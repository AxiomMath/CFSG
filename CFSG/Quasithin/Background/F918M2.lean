module

public import CFSG.Quasithin.Background.SummandSwap
public import CFSG.Quasithin.Background.F918M0
public import CFSG.Quasithin.Background.F918M1

public section

namespace CFSG.Quasithin

open SummandSwap

variable {V : Type} [CommGroup V]

section Shape

variable {A : Subgroup (MulAut V)} {I I' : Subgroup V} {a : MulAut V}

private theorem swap_mem (hS : TwoSummands A I I') (haA : a ∈ A) (haI : a ∉ stabSub I) :
    (∀ x ∈ I, a x ∈ I') ∧ ∀ y ∈ I', a y ∈ I := by
  obtain ⟨h1, h2⟩ := hS.map_eq_of_swap haA haI
  exact ⟨fun x hx => h1 ▸ Subgroup.mem_map_of_mem a.toMonoidHom hx,
    fun y hy => h2 ▸ Subgroup.mem_map_of_mem a.toMonoidHom hy⟩

private theorem stab_mem (hS : TwoSummands A I I') {g : MulAut V} (hg : g ∈ A ⊓ stabSub I) :
    (∀ x ∈ I, g x ∈ I) ∧ ∀ y ∈ I', g y ∈ I' := by
  refine ⟨fun x hx => (mem_stabSub.mp hg.2 x).mpr hx, fun y hy => ?_⟩
  have h2 := hS.map_eq_of_mem_stab hg.1 hg.2
  exact h2 ▸ Subgroup.mem_map_of_mem g.toMonoidHom hy

private theorem decomp_unique (hS : TwoSummands A I I') {x y z w : V} (hx : x ∈ I) (hy : y ∈ I)
    (hz : z ∈ I') (hw : w ∈ I') (h : x * z = y * w) : x = y ∧ z = w := by
  have h1 : y⁻¹ * x = w * z⁻¹ := by
    calc y⁻¹ * x = y⁻¹ * (x * z) * z⁻¹ := by group
      _ = y⁻¹ * (y * w) * z⁻¹ := by rw [h]
      _ = w * z⁻¹ := by group
  have h2 : y⁻¹ * x ∈ I := I.mul_mem (I.inv_mem hy) hx
  have h3 : w * z⁻¹ ∈ I' := I'.mul_mem hw (I'.inv_mem hz)
  have h4 : y⁻¹ * x = 1 := Subgroup.disjoint_def.mp hS.disj h2 (h1 ▸ h3)
  have h5 : w * z⁻¹ = 1 := h1 ▸ h4
  exact ⟨(inv_mul_eq_one.mp h4).symm, (mul_inv_eq_one.mp h5).symm⟩

private theorem exists_decomp (hS : TwoSummands A I I') (v : V) :
    ∃ y ∈ I, ∃ z ∈ I', y * z = v :=
  Subgroup.mem_sup.mp (hS.sup ▸ Subgroup.mem_top v)

private theorem shape_cos (hS : TwoSummands A I I') (hAe : IsElemAbelian2 A) (haA : a ∈ A)
    (haI : a ∉ stabSub I) : ∀ g ∈ A, g ∈ stabSub I ∨ a⁻¹ * g ∈ stabSub I := by
  intro g hg
  by_cases hgI : g ∈ stabSub I
  · exact Or.inl hgI
  · right
    obtain ⟨h1, -⟩ := hS.map_eq_of_swap hg hgI
    obtain ⟨-, h2⟩ := hS.map_eq_of_swap haA haI
    rw [mem_stabSub_iff_map_eq, map_mul_aut', h1, aut_inv_eq hAe haA, h2]

omit [CommGroup V] in
private theorem relIndex_le_two_of_cos {G : Type*} [Group G] {A S : Subgroup G} {a : G}
    (haA : a ∈ A) (hcos : ∀ g ∈ A, g ∈ S ∨ a⁻¹ * g ∈ S) : (A ⊓ S).relIndex A ≤ 2 := by
  refine relIndex_le_of_cover ![1, a] (fun m => ?_) (fun g hg => ?_)
  · fin_cases m
    · exact A.one_mem
    · exact haA
  · rcases hcos g hg with h | h
    · exact ⟨0, by simpa using ⟨hg, h⟩⟩
    · exact ⟨1, by simpa using ⟨A.mul_mem (A.inv_mem haA) hg, h⟩⟩

private theorem shape_faithful (hS : TwoSummands A I I') (hAe : IsElemAbelian2 A) (haA : a ∈ A)
    (haI : a ∉ stabSub I) : (A ⊓ stabSub I) ⊓ centSub I = ⊥ := by
  obtain ⟨-, hI'a⟩ := swap_mem hS haA haI
  rw [eq_bot_iff]
  rintro g ⟨hg, hgc⟩
  rw [Subgroup.mem_bot]
  ext v
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_decomp hS v
  have hz' : g z = z := by
    have h1 : a z ∈ I := hI'a z hz
    have := aut_comm_apply hAe hg.1 haA (a z)
    rw [aut_sq_apply hAe haA, hgc _ h1, aut_sq_apply hAe haA] at this
    exact this
  rw [map_mul, hgc y hy, hz']
  rfl


private theorem fixV_eq_sup (hS : TwoSummands A I I') :
    fixV (A ⊓ stabSub I) = (I ⊓ fixV (A ⊓ stabSub I)) ⊔ (I' ⊓ fixV (A ⊓ stabSub I)) := by
  refine le_antisymm (fun v hv => ?_) (sup_le inf_le_right inf_le_right)
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_decomp hS v
  have hfix : ∀ b ∈ A ⊓ stabSub I, b y = y ∧ b z = z := by
    intro b hb
    obtain ⟨hI, hI'⟩ := stab_mem hS hb
    have := mem_fixV.mp hv b hb
    rw [map_mul] at this
    exact decomp_unique hS (hI y hy) hy (hI' z hz) hz this
  exact Subgroup.mul_mem_sup ⟨hy, fun b hb => (hfix b hb).1⟩ ⟨hz, fun b hb => (hfix b hb).2⟩

private theorem map_fix_eq (hS : TwoSummands A I I') (hAe : IsElemAbelian2 A) (haA : a ∈ A)
    (haI : a ∉ stabSub I) :
    (I ⊓ fixV (A ⊓ stabSub I)).map a.toMonoidHom = I' ⊓ fixV (A ⊓ stabSub I) := by
  obtain ⟨hIa, hI'a⟩ := swap_mem hS haA haI
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxf⟩, rfl⟩
    refine ⟨hIa x hx, fun b hb => ?_⟩
    show b (a x) = a x
    rw [aut_comm_apply hAe hb.1 haA, mem_fixV.mp hxf b hb]
  · rintro ⟨hy, hyf⟩
    refine ⟨a y, ⟨hI'a y hy, fun b hb => ?_⟩, aut_sq_apply hAe haA y⟩
    show b (a y) = a y
    rw [aut_comm_apply hAe hb.1 haA, mem_fixV.mp hyf b hb]

section Ranks

variable [Finite V]

private theorem shape_rk_V (hS : TwoSummands A I I') (haA : a ∈ A) (haI : a ∉ stabSub I) :
    rk V = 2 * rk I := by
  have h1 := hS.rk_add
  have h2 := hS.rk_eq_of_swap haA haI
  omega

omit [Finite V] in
private theorem rk_fixV_A (hS : TwoSummands A I I') (hAe : IsElemAbelian2 A) (haA : a ∈ A)
    (haI : a ∉ stabSub I) : rk (fixV A) = rk ↥(I ⊓ fixV (A ⊓ stabSub I)) := by
  have hmap : I.map a.toMonoidHom = I' := (hS.map_eq_of_swap haA haI).1
  have hdisj : Disjoint I (I.map a.toMonoidHom) := hmap ▸ hS.disj
  have h := rk_fix_sup hAe haA hdisj (shape_cos hS hAe haA haI)
  rwa [hmap, hS.sup, top_inf_eq] at h

private theorem rk_fixV_B (hS : TwoSummands A I I') (hAe : IsElemAbelian2 A) (haA : a ∈ A)
    (haI : a ∉ stabSub I) :
    rk (fixV (A ⊓ stabSub I)) = 2 * rk ↥(I ⊓ fixV (A ⊓ stabSub I)) := by
  have h := rk_sup_add_rk_inf (I ⊓ fixV (A ⊓ stabSub I)) (I' ⊓ fixV (A ⊓ stabSub I))
  rw [← fixV_eq_sup hS] at h
  have hbot : (I ⊓ fixV (A ⊓ stabSub I)) ⊓ (I' ⊓ fixV (A ⊓ stabSub I)) = ⊥ :=
    disjoint_iff.mp (hS.disj.mono inf_le_left inf_le_left)
  rw [hbot, rk_bot, ← map_fix_eq hS hAe haA haI, rk_map_aut] at h
  omega

private theorem rk_eq_add_one {A B : Subgroup (MulAut V)} (hBA : B < A)
    (hle : B.relIndex A ≤ 2) : rk A = rk B + 1 := by
  have hmul := Subgroup.relIndex_mul_card B A
  rw [inf_eq_left.mpr hBA.le] at hmul
  have h1 : B.relIndex A ≠ 1 := fun h => absurd (Subgroup.relIndex_eq_one.mp h) (not_le_of_gt hBA)
  have h0 : B.relIndex A ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact (Nat.card_pos (α := A)).ne' hmul.symm
  have h2 : B.relIndex A = 2 := by omega
  rw [h2] at hmul
  unfold rk
  rw [← hmul, padicValNat.mul two_ne_zero Nat.card_pos.ne', padicValNat_self]
  omega

end Ranks

private theorem shape_quad (hS : TwoSummands A I I') (haA : a ∈ A) (haI : a ∉ stabSub I)
    (hAk : commSeries A 3 = ⊥) {b₁ b₂ : MulAut V} (hb₁ : b₁ ∈ A ⊓ stabSub I)
    (hb₂ : b₂ ∈ A ⊓ stabSub I) {x : V} (hx : x ∈ I) :
    b₂ (b₁ x * x⁻¹) = b₁ x * x⁻¹ := by
  obtain ⟨hIa, -⟩ := swap_mem hS haA haI
  have hfixA : commSub (commSub ⊤ A) A ≤ fixV A :=
    commSub_eq_bot_iff.mp (by simpa [commSeries, commIter] using hAk)
  have hu : b₁ x * x⁻¹ ∈ commSub ⊤ A :=
    Subgroup.subset_closure ⟨b₁, hb₁.1, x, Subgroup.mem_top x, rfl⟩
  have hu' : b₂ (b₁ x * x⁻¹) * (b₁ x * x⁻¹)⁻¹ ∈ commSub (commSub ⊤ A) A :=
    Subgroup.subset_closure ⟨b₂, hb₂.1, _, hu, rfl⟩
  have hfix : a (b₂ (b₁ x * x⁻¹) * (b₁ x * x⁻¹)⁻¹) = b₂ (b₁ x * x⁻¹) * (b₁ x * x⁻¹)⁻¹ :=
    hfixA hu' a haA
  have hxI : b₁ x * x⁻¹ ∈ I := I.mul_mem ((stab_mem hS hb₁).1 x hx) (I.inv_mem hx)
  have hwI : b₂ (b₁ x * x⁻¹) * (b₁ x * x⁻¹)⁻¹ ∈ I :=
    I.mul_mem ((stab_mem hS hb₂).1 _ hxI) (I.inv_mem hxI)
  have hwI' : a (b₂ (b₁ x * x⁻¹) * (b₁ x * x⁻¹)⁻¹) ∈ I' := hIa _ hwI
  rw [hfix] at hwI'
  have h1 := Subgroup.disjoint_def.mp hS.disj hwI hwI'
  exact mul_inv_eq_one.mp h1

private theorem shape_arith {i k b s t : ℕ} (hi : 2 ≤ i) (hk : 1 ≤ k) (hki : k ≤ i)
    (hs : s + k = 2 * i) (ht : t + 2 * k = 2 * i)
    (hA : s ≤ 2 * (b + 1)) (hB : 0 < b → s * b ≤ t * (b + 1)) :
    (b = 0 ∧ i = 2 ∧ k = 2) ∨ (0 < b ∧ k = 2 ∧ i = b + 2) ∨ (0 < b ∧ k = 1 ∧ i ≤ b + 1) := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    left
    omega
  · right
    have h1 := hB hb
    have hs' : (s : ℤ) = 2 * i - k := by omega
    have ht' : (t : ℤ) = 2 * i - 2 * k := by omega
    have h1' : (s : ℤ) * b ≤ t * (b + 1) := by exact_mod_cast h1
    rw [hs', ht'] at h1'
    have hB' : k * b + 2 * k ≤ 2 * i := by
      have : (k : ℤ) * b + 2 * k ≤ 2 * i := by nlinarith
      exact_mod_cast this
    have hk2 : k ≤ 2 := by
      by_contra hcon
      push Not at hcon
      have hA' : (2 * i - k : ℤ) ≤ 2 * b + 2 := by omega
      have hB'' : (k : ℤ) * b + 2 * k ≤ 2 * i := by exact_mod_cast hB'
      have hk3 : (3 : ℤ) ≤ k := by exact_mod_cast hcon
      have hki' : (k : ℤ) ≤ i := by exact_mod_cast hki
      have hi' : (2 : ℤ) ≤ i := by exact_mod_cast hi
      nlinarith [mul_le_mul_of_nonneg_left hA' (show (0 : ℤ) ≤ k by omega),
        mul_nonneg (show (0 : ℤ) ≤ k - 2 by omega) (show (0 : ℤ) ≤ 2 * i - k - 2 by omega)]
    interval_cases k
    · right
      refine ⟨hb, rfl, ?_⟩
      omega
    · left
      refine ⟨hb, rfl, ?_⟩
      omega

section Transvections

variable [Finite V]

private theorem shape_transvections (hV : ∀ v : V, v ^ 2 = 1) (hS : TwoSummands A I I')
    (hAe : IsElemAbelian2 A) (haA : a ∈ A) (haI : a ∉ stabSub I)
    (hquad : ∀ b ∈ A ⊓ stabSub I, ∀ x ∈ I, b x * x⁻¹ ∈ I ⊓ fixV (A ⊓ stabSub I))
    (hk1 : rk ↥(I ⊓ fixV (A ⊓ stabSub I)) = 1) (hbi : rk I ≤ rk ↥(A ⊓ stabSub I) + 1) :
    ∃ (c : V) (hc : c ∈ I), c ≠ 1 ∧
      (∀ b ∈ A ⊓ stabSub I, ∀ x ∈ I, b x = x ∨ b x = x * c) ∧
      rk ↥(A ⊓ stabSub I) + 1 = rk I ∧
      ∀ t : MulAut ↥I, IsTransvectionWith t (⟨c, hc⟩ : ↥I) → t ∈ autSub (A ⊓ stabSub I) I := by
  have hcard2 : Nat.card ↥(I ⊓ fixV (A ⊓ stabSub I)) = 2 := by
    rw [card_eq_two_pow hV, hk1]
    norm_num
  obtain ⟨y, hy1, huniq⟩ :=
    (Nat.card_eq_two_iff' (1 : ↥(I ⊓ fixV (A ⊓ stabSub I)))).mp hcard2
  have hcI : (y : V) ∈ I := y.2.1
  have hc1 : (y : V) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hBc : ∀ b ∈ A ⊓ stabSub I, ∀ x ∈ I, b x = x ∨ b x = x * (y : V) := by
    intro b hb x hx
    by_cases hz : b x * x⁻¹ = 1
    · exact Or.inl (mul_inv_eq_one.mp hz)
    · right
      have h1 := huniq ⟨b x * x⁻¹, hquad b hb x hx⟩ (fun h => hz (congrArg Subtype.val h))
      have h2 : b x * x⁻¹ = y := congrArg Subtype.val h1
      calc b x = (b x * x⁻¹) * x := by group
        _ = x * y := by rw [h2, mul_comm]
  have hcI' : (⟨y, hcI⟩ : ↥I) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hHtv : ∀ t ∈ autSub (A ⊓ stabSub I) I, IsTransvectionWith t (⟨(y : V), hcI⟩ : ↥I) := by
    intro t ht
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp ht
    refine ⟨hcI', fun v => ?_⟩
    rcases hBc g.1 hg v v.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hBe : IsElemAbelian2 (A ⊓ stabSub I) :=
    ⟨fun x hx z hz => hAe.1 x hx.1 z hz.1, fun x hx => hAe.2 x hx.1⟩
  have hfaith := shape_faithful hS hAe haA haI
  have hcardH : Nat.card (autSub (A ⊓ stabSub I) I) = 2 ^ rk ↥(A ⊓ stabSub I) := by
    have h1 := card_autSub_mul (inf_le_right : A ⊓ stabSub I ≤ stabSub I)
    rw [hfaith, Subgroup.card_bot, mul_one] at h1
    rw [h1]
    exact card_eq_two_pow_of_isPGroup hBe.isPGroup
  have hcount : Nat.card (autSub (A ⊓ stabSub I) I) ≤ 2 ^ (rk I - 1) := by
    rw [← card_transvections hV I ⟨y, hcI⟩ hcI']
    have : Finite {t : MulAut ↥I // IsTransvectionWith t (⟨(y : V), hcI⟩ : ↥I)} := by
      apply Nat.finite_of_card_ne_zero
      rw [card_transvections hV I ⟨y, hcI⟩ hcI']
      positivity
    exact Nat.card_le_card_of_injective
      (fun t : autSub (A ⊓ stabSub I) I => (⟨t.1, hHtv t.1 t.2⟩ :
        {t : MulAut ↥I // IsTransvectionWith t (⟨(y : V), hcI⟩ : ↥I)}))
      (fun t t' h => Subtype.ext (Subtype.mk.inj h))
  have hb : rk ↥(A ⊓ stabSub I) ≤ rk I - 1 := by
    rw [hcardH] at hcount
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcount
  have hki : rk ↥(I ⊓ fixV (A ⊓ stabSub I)) ≤ rk I := rk_mono inf_le_left
  have hbeq : rk ↥(A ⊓ stabSub I) + 1 = rk I := by omega
  refine ⟨y, hcI, hc1, hBc, hbeq, ?_⟩
  refine mem_of_card_transvections hV I ⟨y, hcI⟩ hcI' (autSub (A ⊓ stabSub I) I) hHtv ?_
  rw [hcardH]
  congr 1
  omega

end Transvections

end Shape

theorem d29_shape [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G A : Subgroup (MulAut V)}
    (hA : A ∈ kRPlusLe G 3 2) {I I' : Subgroup V} (hS : TwoSummands A I I') (hi : 2 ≤ rk I)
    (hB : A ⊓ stabSub I < A) :
    (∃ (c : V) (hc : c ∈ I), c ≠ 1 ∧
        (∀ b ∈ A ⊓ stabSub I, ∀ x ∈ I, b x = x ∨ b x = x * c) ∧
        rk ↥(I ⊓ fixV (A ⊓ stabSub I)) = 1 ∧
        rk ↥(A ⊓ stabSub I) + 1 = rk I ∧
        1 < rAV A ∧
        (∀ t : MulAut ↥I, IsTransvectionWith t (⟨c, hc⟩ : ↥I) → t ∈ autSub (A ⊓ stabSub I) I)) ∨
    (rk I = rk ↥(A ⊓ stabSub I) + 2 ∧
        rk I - rk ↥(I ⊓ fixV (A ⊓ stabSub I)) = rk ↥(A ⊓ stabSub I) ∧
        (2 < rk I → rAV (A ⊓ stabSub I) = rAV A ∧ rAV A = 2)) := by
  obtain ⟨⟨⟨hA2, hAr⟩, hAk⟩, hAplus⟩ := hA
  have hAe : IsElemAbelian2 A := hA2.isElemAbelian2
  obtain ⟨a, haA, haB⟩ := IsConcreteLE.exists_of_lt hB
  have haI : a ∉ stabSub I := fun h => haB ⟨haA, h⟩
  have hcos := shape_cos hS hAe haA haI
  have hrkA : rk A = rk ↥(A ⊓ stabSub I) + 1 :=
    rk_eq_add_one hB (relIndex_le_two_of_cos haA hcos)
  have hrkV := shape_rk_V hS haA haI
  have hfA := rk_fixV_A hS hAe haA haI
  have hfB := rk_fixV_B hS hAe haA haI
  have hnA := rk_add_rkIdx (fixV A)
  have hnB := rk_add_rkIdx (fixV (A ⊓ stabSub I))
  have hki : rk ↥(I ⊓ fixV (A ⊓ stabSub I)) ≤ rk I := rk_mono inf_le_left
  have hquad : ∀ b ∈ A ⊓ stabSub I, ∀ x ∈ I, b x * x⁻¹ ∈ I ⊓ fixV (A ⊓ stabSub I) := by
    intro b hb x hx
    refine ⟨?_, fun b₂ hb₂ => shape_quad hS haA haI hAk hb hb₂ hx⟩
    exact I.mul_mem ((stab_mem hS hb).1 x hx) (I.inv_mem hx)
  have hk1 : 1 ≤ rk ↥(I ⊓ fixV (A ⊓ stabSub I)) := by
    by_contra hcon
    have h0 : rk ↥(I ⊓ fixV (A ⊓ stabSub I)) = 0 := by omega
    have hbot : I ⊓ fixV (A ⊓ stabSub I) = ⊥ := (rk_eq_zero_iff hV).mp h0
    have hIfix : I ≤ fixV (A ⊓ stabSub I) := fun x hx b hb => by
      have := hquad b hb x hx
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this
    rw [inf_eq_left.mpr hIfix] at hbot
    rw [hbot, rk_bot] at hi
    omega
  have hs : rkIdx (fixV A) + rk ↥(I ⊓ fixV (A ⊓ stabSub I)) = 2 * rk I := by omega
  have ht : rkIdx (fixV (A ⊓ stabSub I)) + 2 * rk ↥(I ⊓ fixV (A ⊓ stabSub I)) = 2 * rk I := by
    omega
  have hArat : rkIdx (fixV A) ≤ 2 * (rk ↥(A ⊓ stabSub I) + 1) := by
    have h1 := hAr
    unfold rAV at h1
    rw [hrkA, div_le_iff₀ (by positivity)] at h1
    exact_mod_cast h1
  have hBrat : 0 < rk ↥(A ⊓ stabSub I) → rkIdx (fixV A) * rk ↥(A ⊓ stabSub I) ≤
      rkIdx (fixV (A ⊓ stabSub I)) * (rk ↥(A ⊓ stabSub I) + 1) := by
    intro hb
    have hne : A ⊓ stabSub I ≠ ⊥ := fun h => by rw [h, rk_bot] at hb; exact lt_irrefl _ hb
    have h1 := hAplus.2 (A ⊓ stabSub I) hne inf_le_left
    unfold rAV at h1
    rw [hrkA, div_le_div_iff₀ (by positivity) (by exact_mod_cast hb)] at h1
    exact_mod_cast h1
  rcases shape_arith hi hk1 hki hs ht hArat hBrat with
    ⟨hb0, hi2, hk2⟩ | ⟨hb, hk2, hib⟩ | ⟨hb, hk1', hib⟩
  · right
    exact ⟨by omega, by omega, fun h => by omega⟩
  · right
    refine ⟨by omega, by omega, fun _ => ?_⟩
    have hrA : rAV A = 2 := by
      unfold rAV
      rw [hrkA]
      have : rkIdx (fixV A) = 2 * (rk ↥(A ⊓ stabSub I) + 1) := by omega
      rw [this]
      push_cast
      field_simp
    have hrB : rAV (A ⊓ stabSub I) = 2 := by
      unfold rAV
      have : rkIdx (fixV (A ⊓ stabSub I)) = 2 * rk ↥(A ⊓ stabSub I) := by omega
      rw [this]
      have hbq : (rk ↥(A ⊓ stabSub I) : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
      push_cast
      field_simp
    exact ⟨hrB.trans hrA.symm, hrA⟩
  · left
    obtain ⟨c, hc, hc1, hBc, hbeq, hfull⟩ :=
      shape_transvections hV hS hAe haA haI hquad hk1' hib
    refine ⟨c, hc, hc1, hBc, hk1', hbeq, ?_, hfull⟩
    unfold rAV
    rw [hrkA, lt_div_iff₀ (by positivity)]
    have : rk ↥(A ⊓ stabSub I) + 1 < rkIdx (fixV A) := by omega
    exact_mod_cast (by omega : 1 * (rk ↥(A ⊓ stabSub I) + 1) < rkIdx (fixV A))

end CFSG.Quasithin
