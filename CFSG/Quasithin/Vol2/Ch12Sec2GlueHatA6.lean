module

public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.H13.L1332Inputs

public section

namespace CFSG.Quasithin.H13

open scoped Pointwise

section Orbits

theorem card_mod_three_of_fpf {W : Type*} [Group W] [Finite W] (ζ : MulAut W) (h3 : ζ ^ 3 = 1)
    (hfp : ∀ w, ζ w = w → w = 1) : Nat.card W % 3 = 1 := by
  classical
  have : Fintype W := Fintype.ofFinite W
  have hσ : MulAut.toPerm W ζ ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, h3, map_one]
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) hσ
  have hsupp : (MulAut.toPerm W ζ).supportᶜ = {1} := by
    ext w
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · exact hfp w
    · rintro rfl
      exact map_one ζ
  rw [hsupp, Finset.card_singleton] at hmod
  rw [Nat.card_eq_fintype_card]
  exact hmod.symm

end Orbits

variable {V : Type} [CommGroup V]

@[expose] def normKer (z : MulAut V) : Subgroup V where
  carrier := {v | v * z v * z (z v) = 1}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
    calc a * b * (z a * z b) * (z (z a) * z (z b))
        = (a * z a * z (z a)) * (b * z b * z (z b)) := by
          simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq, map_inv] at ha ⊢
    rw [← mul_inv, ← mul_inv, ha, inv_one]

theorem mem_normKer {z : MulAut V} {v : V} : v ∈ normKer z ↔ v * z v * z (z v) = 1 := Iff.rfl

theorem zzz_eq {z : MulAut V} (h3 : z ^ 3 = 1) (v : V) : z (z (z v)) = v := by
  have h := congrArg (fun f : MulAut V => f v) h3
  simpa [pow_succ, MulAut.mul_apply] using h

theorem inv_mul_mem_normKer {z : MulAut V} (h3 : z ^ 3 = 1) (v : V) : v⁻¹ * z v ∈ normKer z := by
  rw [mem_normKer]
  simp only [map_mul, map_inv, zzz_eq h3]
  group

variable (hsq : ∀ v : V, v ^ 2 = 1)
include hsq

theorem eq_one_of_mem_normKer {z : MulAut V} {v : V} (hv : v ∈ normKer z) (hzv : z v = v) :
    v = 1 := by
  rw [mem_normKer, hzv, hzv] at hv
  have h2 : v * v = 1 := by rw [← pow_two]; exact hsq v
  rw [h2, one_mul] at hv
  exact hv

theorem zz_eq_of_fpf {z : MulAut V} (h3 : z ^ 3 = 1) {W : Subgroup V}
    (hzW : ∀ w ∈ W, z w ∈ W) (hfp : ∀ w ∈ W, z w = w → w = 1) {w : V} (hw : w ∈ W) :
    z (z w) = w * z w := by
  have hN : w * z w * z (z w) ∈ W := W.mul_mem (W.mul_mem hw (hzW w hw)) (hzW _ (hzW w hw))
  have hfix : z (w * z w * z (z w)) = w * z w * z (z w) := by
    simp only [map_mul, zzz_eq h3]
    simp only [mul_comm, mul_left_comm]
  have h1 := hfp _ hN hfix
  have h2 : w * z w * (w * z w) = 1 := by rw [← pow_two]; exact hsq _
  calc z (z w) = (w * z w) * (w * z w * z (z w)) := by
        rw [← mul_assoc (w * z w) (w * z w), h2, one_mul]
    _ = w * z w := by rw [h1, mul_one]

omit hsq in
@[expose] def restrictMulAut (z : MulAut V) (S : Subgroup V) (h1 : ∀ s ∈ S, z s ∈ S)
    (h2 : ∀ s ∈ S, z⁻¹ s ∈ S) : MulAut ↥S where
  toFun s := ⟨z (s : V), h1 s s.2⟩
  invFun s := ⟨z⁻¹ (s : V), h2 s s.2⟩
  left_inv s := Subtype.ext (by simp)
  right_inv s := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (map_mul z (a : V) (b : V))

omit hsq in
theorem coe_restrictMulAut (z : MulAut V) (S : Subgroup V) (h1 : ∀ s ∈ S, z s ∈ S)
    (h2 : ∀ s ∈ S, z⁻¹ s ∈ S) (s : ↥S) :
    ((restrictMulAut z S h1 h2 s : ↥S) : V) = z (s : V) := rfl

omit hsq in
theorem inv_apply_eq_of_pow_three {z : MulAut V} (h3 : z ^ 3 = 1) (v : V) : z⁻¹ v = z (z v) := by
  have h := zzz_eq h3 (z⁻¹ v)
  rw [MulAut.apply_inv_self] at h
  exact h.symm

omit hsq in
theorem card_mod_three_of_sub {z : MulAut V} (h3 : z ^ 3 = 1) [Finite V] {S : Subgroup V}
    (hzS : ∀ s ∈ S, z s ∈ S) (hfp : ∀ s ∈ S, z s = s → s = 1) : Nat.card S % 3 = 1 := by
  have h2 : ∀ s ∈ S, z⁻¹ s ∈ S := fun s hs => by
    rw [inv_apply_eq_of_pow_three h3]
    exact hzS _ (hzS s hs)
  apply card_mod_three_of_fpf (restrictMulAut z S hzS h2)
  · refine MulEquiv.ext fun s => Subtype.ext ?_
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply,
      coe_restrictMulAut]
    exact zzz_eq h3 (s : V)
  · intro s hs
    exact Subtype.ext (hfp s s.2 (congrArg Subtype.val hs))

omit hsq in
theorem card_cases_of_dvd {c : ℕ} (hc : c ∣ 64) (h3 : c % 3 = 1) :
    c = 1 ∨ c = 4 ∨ c = 16 ∨ c = 64 := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show c ∣ 2 ^ 6 from hc)
  interval_cases i <;> simp_all

omit hsq in
theorem mem_closure_of_map_gen {z : MulAut V} {S : Set V}
    (hzS : ∀ s ∈ S, z s ∈ Subgroup.closure S) :
    ∀ x ∈ Subgroup.closure S, z x ∈ Subgroup.closure S := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hzS s hs
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem exists_gen_of_fpf [Finite V] (hV : Nat.card V = 2 ^ 6) {z : MulAut V} (h3 : z ^ 3 = 1)
    {W : Subgroup V} (hzW : ∀ w ∈ W, z w ∈ W) (hfp : ∀ w ∈ W, z w = w → w = 1)
    (hW : Nat.card W = 4 ∨ Nat.card W = 16) :
    ∃ w₁ ∈ W, ∃ w₂ ∈ W, Subgroup.closure ({w₁, z w₁, w₂, z w₂} : Set V) = W := by
  have hW1 : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hW
    omega
  obtain ⟨⟨w₁, hw₁W⟩, hw₁⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW1
  have hw₁1 : w₁ ≠ 1 := fun h => hw₁ (Subtype.ext h)
  have hcl : ∀ S : Set V, S ⊆ W → (∀ s ∈ S, z s ∈ Subgroup.closure S) →
      Subgroup.closure S ≤ W ∧ Nat.card (Subgroup.closure S) ∣ 64 ∧
        Nat.card (Subgroup.closure S) % 3 = 1 := fun S hSW hzS => by
    have hle : Subgroup.closure S ≤ W := (Subgroup.closure_le W).mpr hSW
    refine ⟨hle, ?_, card_mod_three_of_sub h3 (mem_closure_of_map_gen hzS)
      fun s hs => hfp s (hle hs)⟩
    rw [← show (2 : ℕ) ^ 6 = 64 from rfl, ← hV]
    exact Subgroup.card_subgroup_dvd_card _
  have hzz : ∀ w ∈ W, z (z w) = w * z w := fun w hw => zz_eq_of_fpf hsq h3 hzW hfp hw
  set S₁ := Subgroup.closure ({w₁, z w₁} : Set V) with hS₁
  have hS₁W : ({w₁, z w₁} : Set V) ⊆ W := by
    rintro _ (rfl | rfl)
    · exact hw₁W
    · exact hzW _ hw₁W
  have hzS₁ : ∀ s ∈ ({w₁, z w₁} : Set V), z s ∈ S₁ := by
    rintro _ (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [hzz _ hw₁W]
      exact S₁.mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  obtain ⟨hS₁le, hS₁d, hS₁m⟩ := hcl _ hS₁W hzS₁
  have hS₁1 : Nat.card S₁ ≠ 1 := by
    intro h
    rw [Subgroup.card_eq_one] at h
    exact hw₁1 (by
      have : w₁ ∈ S₁ := Subgroup.subset_closure (Set.mem_insert _ _)
      rw [h] at this
      exact this)
  by_cases hS₁eq : S₁ = W
  · refine ⟨w₁, hw₁W, w₁, hw₁W, ?_⟩
    rw [← hS₁eq, hS₁]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hS₁4 : Nat.card S₁ = 4 := by
    have hlt : Nat.card S₁ ≠ Nat.card W := fun h =>
      hS₁eq (Subgroup.eq_of_le_of_card_ge hS₁le h.ge)
    have hdvd : Nat.card S₁ ∣ Nat.card W := Subgroup.card_dvd_of_le hS₁le
    rcases card_cases_of_dvd hS₁d hS₁m with h | h | h | h
    · exact absurd h hS₁1
    · exact h
    · rcases hW with hW | hW <;> rw [h, hW] at hdvd hlt <;> omega
    · rcases hW with hW | hW <;> rw [h, hW] at hdvd <;> omega
  obtain ⟨w₂, hw₂W, hw₂⟩ : ∃ w₂ ∈ W, w₂ ∉ S₁ := by
    by_contra hcon
    apply hS₁eq
    refine le_antisymm hS₁le fun x hx => ?_
    by_contra hxS
    exact hcon ⟨x, hx, hxS⟩
  set S₂ := Subgroup.closure ({w₁, z w₁, w₂, z w₂} : Set V) with hS₂
  have hS₂W : ({w₁, z w₁, w₂, z w₂} : Set V) ⊆ W := by
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hw₁W
    · exact hzW _ hw₁W
    · exact hw₂W
    · exact hzW _ hw₂W
  have hmem : ∀ x ∈ ({w₁, z w₁, w₂, z w₂} : Set V), x ∈ S₂ := fun x hx =>
    Subgroup.subset_closure hx
  have hzS₂ : ∀ s ∈ ({w₁, z w₁, w₂, z w₂} : Set V), z s ∈ S₂ := by
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hmem _ (by simp)
    · rw [hzz _ hw₁W]
      exact S₂.mul_mem (hmem _ (by simp)) (hmem _ (by simp))
    · exact hmem _ (by simp)
    · rw [hzz _ hw₂W]
      exact S₂.mul_mem (hmem _ (by simp)) (hmem _ (by simp))
  obtain ⟨hS₂le, hS₂d, hS₂m⟩ := hcl _ hS₂W hzS₂
  have hS₁S₂ : S₁ ≤ S₂ := Subgroup.closure_mono (by
    rintro _ (rfl | rfl)
    · simp
    · simp)
  have hS₂ne : S₁ ≠ S₂ := fun h => hw₂ (h ▸ hmem _ (by simp))
  have hcard : Nat.card S₁ < Nat.card S₂ := by
    have hdvd : Nat.card S₁ ∣ Nat.card S₂ := Subgroup.card_dvd_of_le hS₁S₂
    have hne : Nat.card S₁ ≠ Nat.card S₂ := fun h =>
      hS₂ne (Subgroup.eq_of_le_of_card_ge hS₁S₂ h.ge)
    exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) hne
  have hS₂16 : Nat.card S₂ = Nat.card W := by
    have hdvd : Nat.card S₂ ∣ Nat.card W := Subgroup.card_dvd_of_le hS₂le
    rcases card_cases_of_dvd hS₂d hS₂m with h | h | h | h <;>
      rcases hW with hW | hW <;> rw [hS₁4] at hcard <;> rw [h] at hcard hdvd ⊢ <;>
        rw [hW] at hdvd ⊢ <;> omega
  exact ⟨w₁, hw₁W, w₂, hw₂W, Subgroup.eq_of_le_of_card_ge hS₂le hS₂16.ge⟩

omit hsq in
theorem card_centralizer_le [Finite V] {W : Subgroup V} (ζ : MulAut ↥W) (z : MulAut V)
    (hζ : ∀ w : ↥W, ((ζ w : ↥W) : V) = z (w : V)) {w₁ w₂ : V} (hw₁ : w₁ ∈ W) (hw₂ : w₂ ∈ W)
    (hgen : Subgroup.closure ({w₁, z w₁, w₂, z w₂} : Set V) = W) :
    Nat.card (Subgroup.centralizer ({ζ} : Set (MulAut ↥W))) ≤ Nat.card W ^ 2 := by
  let f : ↥(Subgroup.centralizer ({ζ} : Set (MulAut ↥W))) → ↥W × ↥W :=
    fun g => ((g : MulAut ↥W) ⟨w₁, hw₁⟩, (g : MulAut ↥W) ⟨w₂, hw₂⟩)
  have hc : ∀ (k : ↥(Subgroup.centralizer ({ζ} : Set (MulAut ↥W)))) (x : ↥W),
      (k : MulAut ↥W) (ζ x) = ζ ((k : MulAut ↥W) x) := fun k x =>
    congrArg (fun F : MulAut ↥W => F x) (Subgroup.mem_centralizer_singleton_iff.mp k.2)
  have hinj : Function.Injective f := by
    intro g g' h
    have h1 : (g : MulAut ↥W) ⟨w₁, hw₁⟩ = (g' : MulAut ↥W) ⟨w₁, hw₁⟩ := congrArg Prod.fst h
    have h2 : (g : MulAut ↥W) ⟨w₂, hw₂⟩ = (g' : MulAut ↥W) ⟨w₂, hw₂⟩ := congrArg Prod.snd h
    let E := (g : MulAut ↥W).toMonoidHom.eqLocus (g' : MulAut ↥W).toMonoidHom
    have hgen' : W ≤ E.map W.subtype := by
      refine hgen.symm.le.trans ((Subgroup.closure_le _).mpr ?_)
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx | hx <;> rw [hx]
      · exact ⟨⟨w₁, hw₁⟩, h1, rfl⟩
      · refine ⟨ζ ⟨w₁, hw₁⟩, ?_, hζ _⟩
        show (g : MulAut ↥W) (ζ ⟨w₁, hw₁⟩) = (g' : MulAut ↥W) (ζ ⟨w₁, hw₁⟩)
        rw [hc g, hc g', h1]
      · exact ⟨⟨w₂, hw₂⟩, h2, rfl⟩
      · refine ⟨ζ ⟨w₂, hw₂⟩, ?_, hζ _⟩
        show (g : MulAut ↥W) (ζ ⟨w₂, hw₂⟩) = (g' : MulAut ↥W) (ζ ⟨w₂, hw₂⟩)
        rw [hc g, hc g', h2]
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    obtain ⟨y, hy, hyx⟩ := hgen' x.2
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  calc Nat.card _ ≤ Nat.card (↥W × ↥W) := Nat.card_le_card_of_injective f hinj
    _ = Nat.card W ^ 2 := by rw [Nat.card_prod, pow_two]

omit hsq in
@[expose] def restrictAut (H : Subgroup (MulAut V)) (W : Subgroup V)
    (hW : ∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) : ↥H →* MulAut ↥W where
  toFun h := restrictMulAut (h : MulAut V) W (hW h h.2)
    (fun w hw => hW (h : MulAut V)⁻¹ (H.inv_mem h.2) w hw)
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext rfl

section Key

variable [Finite V] (hV : Nat.card V = 2 ^ 6) {H : Subgroup (MulAut V)}
  (hq : CFSG.IsQuasisimple ↥H) (hZ : Nat.card (Subgroup.center ↥H) = 3)
  (hH : Nat.card H = 1080) {zH : ↥H} (hzc : zH ∈ Subgroup.center ↥H)
  (h3 : (zH : MulAut V) ^ 3 = 1) {W : Subgroup V}
  (hW : ∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) (hW1 : W ≠ ⊥)
  (hfp : ∀ w ∈ W, (zH : MulAut V) w = w → w = 1)
include hV hq hZ hH hzc h3 hW hW1 hfp

theorem false_of_small_fpf (hcard : Nat.card W = 4 ∨ Nat.card W = 16) : False := by
  have hzW : ∀ w ∈ W, (zH : MulAut V) w ∈ W := hW _ zH.2
  obtain ⟨w₁, hw₁, w₂, hw₂, hgen⟩ := exists_gen_of_fpf hsq hV h3 hzW hfp hcard
  let ρ := restrictAut H W hW
  have hρ : ∀ (h : ↥H) (w : ↥W), ((ρ h w : ↥W) : V) = (h : MulAut V) w := fun _ _ => rfl
  have hker : ρ.ker ≤ Subgroup.center ↥H := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (MonoidHom.normal_ker ρ) with h | h
    · exfalso
      have hz1 : ρ zH = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top zH
      obtain ⟨⟨w, hwW⟩, hw⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW1
      apply hw
      apply Subtype.ext
      apply hfp w hwW
      have := congrArg (fun F : MulAut ↥W => ((F ⟨w, hwW⟩ : ↥W) : V)) hz1
      simpa [hρ] using this
    · exact h
  have hrange : 360 ≤ Nat.card ρ.range := by
    have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hH] at e1
    have hk : Nat.card ρ.ker ≤ 3 := hZ ▸ Subgroup.card_le_of_le hker
    by_contra hlt
    push Not at hlt
    have : Nat.card ρ.range * Nat.card ρ.ker < 360 * 3 :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hlt hk (by norm_num))
        (Nat.mul_le_mul_left _ le_rfl)
    omega
  have hcent : ρ.range ≤ Subgroup.centralizer ({ρ zH} : Set (MulAut ↥W)) := by
    rintro _ ⟨h, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      (Subgroup.mem_center_iff.mp hzc h)]
  have hbound := card_centralizer_le (ρ zH) (zH : MulAut V) (hρ zH) hw₁ hw₂ hgen
  have := (Subgroup.card_le_of_le hcent).trans hbound
  rcases hcard with h | h <;> rw [h] at this <;> omega

theorem eq_top_of_fpf : W = ⊤ := by
  have hzW : ∀ w ∈ W, (zH : MulAut V) w ∈ W := hW _ zH.2
  have hd : Nat.card W ∣ 64 := by
    rw [← show (2 : ℕ) ^ 6 = 64 from rfl, ← hV]
    exact Subgroup.card_subgroup_dvd_card W
  have hm := card_mod_three_of_sub h3 hzW hfp
  have h1 : Nat.card W ≠ 1 := fun h => hW1 (Subgroup.card_eq_one.mp h)
  rcases card_cases_of_dvd hd hm with h | h | h | h
  · exact absurd h h1
  · exact (false_of_small_fpf hsq hV hq hZ hH hzc h3 hW hW1 hfp (Or.inl h)).elim
  · exact (false_of_small_fpf hsq hV hq hZ hH hzc h3 hW hW1 hfp (Or.inr h)).elim
  · exact Subgroup.eq_top_of_card_eq W (h.trans hV.symm)

end Key

omit hsq in
theorem normKer_invariant {H : Subgroup (MulAut V)} {zH : ↥H} (hzc : zH ∈ Subgroup.center ↥H) :
    ∀ h ∈ H, ∀ v ∈ normKer (zH : MulAut V), (h : MulAut V) v ∈ normKer (zH : MulAut V) := by
  intro h hh v hv
  have hcomm : ∀ x : V, (zH : MulAut V) (h x) = h ((zH : MulAut V) x) := fun x => by
    have := Subgroup.mem_center_iff.mp hzc ⟨h, hh⟩
    have h' := congrArg (fun F : ↥H => ((F : MulAut V) x)) this
    exact h'.symm
  rw [mem_normKer] at hv ⊢
  rw [hcomm, hcomm, ← map_mul, ← map_mul, hv, map_one]

omit hsq in
theorem hatA6SixIrreducible : HatA6SixIrreducible := by
  intro V _ _ hsq hV H hperf hZ ⟨e⟩
  have hs6 : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hq : CFSG.IsQuasisimple ↥H := by
    refine ⟨hperf, e.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := alternatingGroup_nonabelian (n := 6) (by norm_num)
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  have hH : Nat.card H = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥H),
      Nat.card_congr e.toEquiv, card_alternatingGroup_fin 6 (by norm_num), hZ]
    decide
  have hZ1 : Subgroup.center ↥H ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ
    omega
  obtain ⟨⟨zH, hzc⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ1
  have hzH1 : zH ≠ 1 := fun h => hz1 (Subtype.ext h)
  have h3H : zH ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥H)) (x := ⟨zH, hzc⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  have h3 : (zH : MulAut V) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, h3H]
    rfl
  have hNfp : ∀ v ∈ normKer (zH : MulAut V), (zH : MulAut V) v = v → v = 1 :=
    fun v hv hzv => eq_one_of_mem_normKer hsq hv hzv
  have hN1 : normKer (zH : MulAut V) ≠ ⊥ := by
    intro hbot
    apply hzH1
    apply Subtype.ext
    refine MulEquiv.ext fun v => ?_
    have hmem := inv_mul_mem_normKer h3 v
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm
  have hNtop := eq_top_of_fpf hsq hV hq hZ hH hzc h3 (normKer_invariant hzc) hN1 hNfp
  have hCz : ∀ v : V, (zH : MulAut V) v = v → v = 1 := fun v hzv =>
    hNfp v (hNtop ▸ Subgroup.mem_top v) hzv
  refine ⟨?_, fun W hW => ?_⟩
  · rw [eq_bot_iff]
    intro v hv
    exact hCz v (hv _ zH.2)
  · by_cases hW1 : W = ⊥
    · exact Or.inl hW1
    · exact Or.inr (eq_top_of_fpf hsq hV hq hZ hH hzc h3 hW hW1 fun w _ hzw => hCz w hzw)

end CFSG.Quasithin.H13
