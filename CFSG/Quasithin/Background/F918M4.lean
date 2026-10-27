module

public import CFSG.Quasithin.Background.SummandSwap
public import CFSG.Quasithin.Background.F918M0
public import CFSG.Quasithin.Background.B1Transvection

public section

namespace CFSG.Quasithin

section Generic

variable {V : Type} [CommGroup V]

private def quadSub (F : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | (∀ f ∈ F, g f = f) ∧ ∀ v, g v * v⁻¹ ∈ F}
  one_mem' := ⟨fun _ _ => rfl, fun v => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun f hf => ?_, fun v => ?_⟩
    · show g (h f) = f
      rw [hh1 f hf, hg1 f hf]
    · show g (h v) * v⁻¹ ∈ F
      have e : g (h v) * v⁻¹ = (g (h v) * (h v)⁻¹) * (h v * v⁻¹) := by group
      rw [e]
      exact F.mul_mem (hg2 _) (hh2 _)
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun f hf => ?_, fun v => ?_⟩
    · calc g⁻¹ f = g⁻¹ (g f) := by rw [hg1 f hf]
        _ = f := MulAut.inv_apply_self V g f
    · have h1 := hg2 (g⁻¹ v)
      rw [MulAut.apply_inv_self] at h1
      have e : g⁻¹ v * v⁻¹ = (v * (g⁻¹ v)⁻¹)⁻¹ := by group
      rw [e]
      exact F.inv_mem h1

private theorem quadSub_comm {F : Subgroup V} {g h : MulAut V} (hg : g ∈ quadSub F)
    (hh : h ∈ quadSub F) : g * h = h * g := by
  refine MulEquiv.ext fun v => ?_
  show g (h v) = h (g v)
  have he : h v = (h v * v⁻¹) * v := (inv_mul_cancel_right (h v) v).symm
  have hd : g v = (g v * v⁻¹) * v := (inv_mul_cancel_right (g v) v).symm
  have h1 : g (h v) = (h v * v⁻¹) * g v := by
    conv_lhs => rw [he]
    rw [map_mul, hg.1 _ (hh.2 v)]
  have h2 : h (g v) = (g v * v⁻¹) * h v := by
    conv_lhs => rw [hd]
    rw [map_mul, hh.1 _ (hg.2 v)]
  rw [h1, h2, mul_right_comm (h v), mul_right_comm (g v), mul_comm (h v) (g v)]

private theorem quadSub_sq (hV : ∀ v : V, v ^ 2 = 1) {F : Subgroup V} {g : MulAut V}
    (hg : g ∈ quadSub F) : g ^ 2 = 1 := by
  refine MulEquiv.ext fun v => ?_
  rw [pow_two]
  show g (g v) = v
  have he : g v = (g v * v⁻¹) * v := (inv_mul_cancel_right (g v) v).symm
  have h1 : g (g v) = (g v * v⁻¹) * g v := by
    conv_lhs => rw [he]
    rw [map_mul, hg.1 _ (hg.2 v)]
  rw [h1, mul_right_comm, ← pow_two, hV, one_mul]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV v)

private theorem isElemAbelian2_of_le_quadSub (hV : ∀ v : V, v ^ 2 = 1) {F : Subgroup V}
    {E : Subgroup (MulAut V)} (hE : E ≤ quadSub F) : IsElemAbelian2 E :=
  ⟨fun _ hg _ hh => quadSub_comm (hE hg) (hE hh), fun _ hg => quadSub_sq hV (hE hg)⟩

private theorem le_fixV_of_le_quadSub {F : Subgroup V} {E : Subgroup (MulAut V)}
    (hE : E ≤ quadSub F) : F ≤ fixV E :=
  fun f hf _ hg => (hE hg).1 f hf

private theorem commSeries_two_of_le_quadSub {F : Subgroup V} {E : Subgroup (MulAut V)}
    (hE : E ≤ quadSub F) : commSeries E 2 = ⊥ := by
  rw [← isQuadratic_iff_commSeries_two]
  refine le_trans ?_ (le_fixV_of_le_quadSub hE)
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  exact (hE hg).2 v

end Generic

section Ranks

variable {V : Type} [CommGroup V] [Finite V]

private theorem relIndex_le_of_cover_fin {G : Type*} [Group G] {H K : Subgroup G} {n : ℕ}
    (r : Fin n → G) (hr : ∀ m, r m ∈ K) (h : ∀ g ∈ K, ∃ m, (r m)⁻¹ * g ∈ H) :
    H.relIndex K ≤ n :=
  CFSG.Quasithin.SummandSwap.relIndex_le_of_cover r hr h

private theorem rk_le_rk_stab_add_one (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    {v w : V} (hw : ∀ h ∈ H, h w = w) (hv : ∀ h ∈ H, h v = v ∨ h v = v * w) :
    rk H ≤ rk ↥(H ⊓ MulAction.stabilizer (MulAut V) v) + 1 := by
  set K := H ⊓ MulAction.stabilizer (MulAut V) v
  have hKH : K ≤ H := inf_le_left
  have hmemK : ∀ h ∈ H, h v = v → h ∈ K := fun h hh hhv =>
    Subgroup.mem_inf.mpr ⟨hh, MulAction.mem_stabilizer_iff.mpr hhv⟩
  have hidx : K.relIndex H ≤ 2 := by
    by_cases hall : ∀ h ∈ H, h v = v
    · have : H ≤ K := fun h hh => hmemK h hh (hall h hh)
      rw [Subgroup.relIndex_eq_one.mpr this]
      norm_num
    · push Not at hall
      obtain ⟨h0, hh0, hh0v⟩ := hall
      have hh0v' : h0 v = v * w := (hv h0 hh0).resolve_left hh0v
      refine relIndex_le_of_cover_fin ![1, h0] (fun m => ?_) (fun g hg => ?_)
      · fin_cases m
        · exact H.one_mem
        · exact hh0
      · rcases hv g hg with h1 | h1
        · exact ⟨0, by simpa using hmemK g hg h1⟩
        · refine ⟨1, ?_⟩
          have hinv : h0⁻¹ v = v * w := by
            have e : h0 (v * w) = v := by
              rw [map_mul, hh0v', hw h0 hh0, mul_assoc, ← pow_two, hV, mul_one]
            calc h0⁻¹ v = h0⁻¹ (h0 (v * w)) := by rw [e]
              _ = v * w := MulAut.inv_apply_self V h0 _
          have : h0⁻¹ * g ∈ K := by
            refine hmemK _ (H.mul_mem (H.inv_mem hh0) hg) ?_
            show h0⁻¹ (g v) = v
            have hw' : h0⁻¹ w = w := by
              conv_lhs => rw [← hw h0 hh0]
              exact MulAut.inv_apply_self V h0 w
            rw [h1, map_mul, hinv, hw', mul_assoc, ← pow_two, hV, mul_one]
          simpa using this
  have hmul := Subgroup.relIndex_mul_card K H
  rw [inf_eq_left.mpr hKH] at hmul
  have h0 : K.relIndex H ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact (Nat.card_pos (α := H)).ne' hmul.symm
  unfold rk
  rw [← hmul, padicValNat.mul h0 Nat.card_pos.ne']
  have hv1 : padicValNat 2 (K.relIndex H) ≤ 1 := by
    interval_cases hk : K.relIndex H <;> simp
  omega

private theorem two_le_rk_of_mem (hV : ∀ v : V, v ^ 2 = 1) {M : Subgroup V} {x y : V}
    (hx : x ∈ M) (hy : y ∈ M) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) : 2 ≤ rk M := by
  classical
  have h3 : ({1, x, y} : Finset V).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, x, y, hx1.symm, hy1.symm, hxy, rfl⟩
  have hle := B1.card_le_of_finset_subset ({1, x, y} : Finset V) (M := M) (by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl
    · exact M.one_mem
    · exact hx
    · exact hy)
  rw [h3, card_eq_two_pow hV M] at hle
  rcases Nat.lt_or_ge (rk M) 2 with h | h
  · have : 2 ^ rk M ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · exact h

end Ranks

section Main

variable {V : Type} [CommGroup V]

private def fixSubOf (g : MulAut V) : Subgroup V where
  carrier := {v | g v = v}
  one_mem' := map_one g
  mul_mem' := fun {x y} hx hy => by
    show g (x * y) = x * y
    rw [map_mul, hx, hy]
  inv_mem' := fun {x} hx => by
    show g x⁻¹ = x⁻¹
    rw [map_inv, hx]

private theorem fix_of_move (hV : ∀ v : V, v ^ 2 = 1) {b : MulAut V} {c : V} (hc1 : c ≠ 1)
    (h : b c = c ∨ b c = c * c) : b c = c := by
  rcases h with h | h
  · exact h
  · exfalso
    have hcc : c * c = 1 := by rw [← pow_two]; exact hV c
    rw [hcc] at h
    exact hc1 (b.injective (h.trans (map_one b).symm))

private theorem conj_mem_B_of_fix {G A : Subgroup (MulAut V)} {I : Subgroup V} (hAG : A ≤ G)
    {c : V} (hcI : c ∈ I) (hc1 : c ≠ 1)
    (hBc : ∀ b ∈ A ⊓ stabSub I, ∀ x ∈ I, b x = x ∨ b x = x * c)
    (hfull : ∀ t : MulAut ↥I, IsTransvectionWith t (⟨c, hcI⟩ : ↥I) →
      t ∈ autSub (A ⊓ stabSub I) I)
    (hker : G ⊓ centSub I = ⊥) {p : MulAut V} (hpG : p ∈ G) (hpI : p ∈ stabSub I)
    (hpc : p c = c) {b : MulAut V} (hb : b ∈ A ⊓ stabSub I) :
    p * b * p⁻¹ ∈ A ⊓ stabSub I := by
  have hq : p * b * p⁻¹ ∈ stabSub I :=
    (stabSub I).mul_mem ((stabSub I).mul_mem hpI hb.2) ((stabSub I).inv_mem hpI)
  have ht : IsTransvectionWith (resHom I ⟨p * b * p⁻¹, hq⟩) (⟨c, hcI⟩ : ↥I) := by
    refine ⟨fun h => hc1 (congrArg Subtype.val h), fun u => ?_⟩
    have hu : p⁻¹ (u : V) ∈ I := ((stabSub I).inv_mem hpI (u : V)).mpr u.2
    rcases hBc b hb _ hu with h | h
    · left
      ext
      show p (b (p⁻¹ (u : V))) = u
      rw [h, MulAut.apply_inv_self]
    · right
      ext
      show p (b (p⁻¹ (u : V))) = (u : V) * c
      rw [h, map_mul, MulAut.apply_inv_self, hpc]
  obtain ⟨g, hgB, hgt⟩ := mem_autSub.mp (hfull _ ht)
  have hcomp : (g : MulAut V)⁻¹ * (p * b * p⁻¹) ∈ G ⊓ centSub I := by
    refine ⟨G.mul_mem (G.inv_mem (hAG hgB.1))
      (G.mul_mem (G.mul_mem hpG (hAG hb.1)) (G.inv_mem hpG)), fun u hu => ?_⟩
    have h1 : (g : MulAut V) u = (p * b * p⁻¹) u :=
      congrArg (fun φ : MulAut ↥I => ((φ ⟨u, hu⟩ : ↥I) : V)) hgt
    show (g : MulAut V)⁻¹ ((p * b * p⁻¹) u) = u
    rw [← h1, MulAut.inv_apply_self]
  rw [hker, Subgroup.mem_bot, inv_mul_eq_one] at hcomp
  rw [← hcomp]
  exact hgB

variable [Finite V]

theorem d29_further_diag (hV : ∀ v : V, v ^ 2 = 1) {G A : Subgroup (MulAut V)} {I I' : Subgroup V}
    (hS : TwoSummands G I I') (hi : 2 < rk I) (hAG : A ≤ G) (hAe : IsElemAbelian2 A)
    {a : MulAut V} (haA : a ∈ A) (haI : a ∉ stabSub I) {c : V} (hcI : c ∈ I) (hc1 : c ≠ 1)
    (hBc : ∀ b ∈ A ⊓ stabSub I, ∀ x ∈ I, b x = x ∨ b x = x * c)
    (hrkB : rk ↥(A ⊓ stabSub I) + 1 = rk I)
    (hfull : ∀ t : MulAut ↥I, IsTransvectionWith t (⟨c, hcI⟩ : ↥I) →
      t ∈ autSub (A ⊓ stabSub I) I)
    (hgen : Subgroup.closure {x | ∃ n ∈ G ⊓ stabSub I, n c = x} = I)
    (hker : G ⊓ centSub I = ⊥) :
    ∃ A₀ : Subgroup (MulAut V), IsA2 G A₀ ∧ commSeries A₀ 2 = ⊥ ∧ rAV A₀ ≤ 1 := by
  classical
  have haG : a ∈ G := hAG haA
  obtain ⟨hIa, -⟩ := hS.map_eq_of_swap haG haI
  have haa : a * a = 1 := by rw [← pow_two]; exact hAe.2 a haA
  have ha2 : ∀ x, a (a x) = x := fun x => congrArg (fun φ : MulAut V => φ x) haa
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have haI' : ∀ x ∈ I, a x ∈ I' := fun x hx => hIa ▸ Subgroup.mem_map_of_mem a.toMonoidHom hx
  have hc'I' : a c ∈ I' := haI' c hcI
  have hc'1 : a c ≠ 1 := fun h => hc1 (a.injective (h.trans (map_one a).symm))
  have hBG : A ⊓ stabSub I ≤ G := inf_le_left.trans hAG
  have hBN : A ⊓ stabSub I ≤ G ⊓ stabSub I := inf_le_inf_right _ hAG
  have hBa : ∀ b ∈ A ⊓ stabSub I, ∀ x, b (a x) = a (b x) := fun b hb x =>
    congrArg (fun φ : MulAut V => φ x) (hAe.1 b hb.1 a haA)
  have hBfix : ∀ b ∈ A ⊓ stabSub I, b c = c := fun b hb =>
    fix_of_move hV hc1 (hBc b hb c hcI)
  have hBfix' : ∀ b ∈ A ⊓ stabSub I, b (a c) = a c := fun b hb => by
    rw [hBa b hb, hBfix b hb]
  have hBc' : ∀ b ∈ A ⊓ stabSub I, ∀ y ∈ I', b y = y ∨ b y = y * a c := by
    intro b hb y hy
    have hy' : y ∈ I.map a.toMonoidHom := hIa.symm ▸ hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy'
    show b (a x) = a x ∨ b (a x) = a x * a c
    rw [hBa b hb]
    rcases hBc b hb x hx with h | h
    · left
      rw [h]
    · right
      rw [h, map_mul]
  have hNI : ∀ n ∈ G ⊓ stabSub I, ∀ u ∈ I, n u ∈ I := fun n hn u hu =>
    (mem_stabSub.mp hn.2 u).mpr hu
  have hNI' : ∀ n ∈ G ⊓ stabSub I, ∀ u ∈ I', n u ∈ I' := fun n hn u hu =>
    (mem_stabSub.mp ((hS.mem_stab_iff hn.1).mpr hn.2) u).mpr hu
  have hfaith : ∀ n ∈ G, (∀ u ∈ I, n u = u) → n = 1 := by
    intro n hn h
    have : n ∈ G ⊓ centSub I := ⟨hn, h⟩
    rwa [hker, Subgroup.mem_bot] at this
  obtain ⟨K0, hK0⟩ : ∃ K0 : Subgroup V, K0 = Subgroup.closure ({c, a c} : Set V) := ⟨_, rfl⟩
  have hcK0 : c ∈ K0 := hK0 ▸ Subgroup.subset_closure (by simp)
  have hc'K0 : a c ∈ K0 := hK0 ▸ Subgroup.subset_closure (by simp)
  have hBmove : ∀ b ∈ A ⊓ stabSub I, ∀ v, b v * v⁻¹ ∈ K0 := by
    intro b hb v
    have hv : v ∈ I ⊔ I' := by rw [hS.sup]; trivial
    obtain ⟨u, hu, u', hu', rfl⟩ := Subgroup.mem_sup.mp hv
    have e : b (u * u') * (u * u')⁻¹ = (b u * u⁻¹) * (b u' * u'⁻¹) := by
      rw [map_mul, mul_inv, mul_mul_mul_comm]
    rw [e]
    refine K0.mul_mem ?_ ?_
    · rcases hBc b hb u hu with h | h
      · rw [h, mul_inv_cancel]
        exact K0.one_mem
      · rw [h, mul_comm u c, mul_inv_cancel_right]
        exact hcK0
    · rcases hBc' b hb u' hu' with h | h
      · rw [h, mul_inv_cancel]
        exact K0.one_mem
      · rw [h, mul_comm u' (a c), mul_inv_cancel_right]
        exact hc'K0
  obtain ⟨b0, hb0, hb01⟩ : ∃ b0 ∈ A ⊓ stabSub I, b0 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : A ⊓ stabSub I = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [hbot, rk_bot] at hrkB
    omega
  obtain ⟨x0, hx0I, hx0⟩ : ∃ x0 ∈ I, b0 x0 ≠ x0 := by
    by_contra hcon
    push Not at hcon
    exact hb01 (hfaith b0 (hBG hb0) hcon)
  have hb0x0 : b0 x0 = x0 * c := (hBc b0 hb0 x0 hx0I).resolve_left hx0
  have hb0y0 : b0 (a x0) = a x0 * a c := by rw [hBa b0 hb0, hb0x0, map_mul]
  have hF5 : ∀ p ∈ G ⊓ stabSub I, p c = c → p (a c) = a c := by
    intro p hp hpc
    have hb1 : p * b0 * p⁻¹ ∈ A ⊓ stabSub I :=
      conj_mem_B_of_fix hAG hcI hc1 hBc hfull hker hp.1 hp.2 hpc hb0
    have hy : p (a x0) ∈ I' := hNI' p hp _ (haI' x0 hx0I)
    have e : (p * b0 * p⁻¹) (p (a x0)) = p (a x0) * p (a c) := by
      show p (b0 (p⁻¹ (p (a x0)))) = _
      rw [MulAut.inv_apply_self, hb0y0, map_mul]
    rcases hBc' _ hb1 _ hy with h | h
    · exfalso
      rw [e] at h
      have h1 : p (a c) = 1 := mul_left_cancel (h.trans (mul_one _).symm)
      exact hc'1 (p.injective (h1.trans (map_one p).symm))
    · rw [e] at h
      exact mul_left_cancel h
  have hF6 : ∀ p ∈ G ⊓ stabSub I, p (a c) = a c → p c = c := by
    intro p hp hpc'
    have hq : a * p * a⁻¹ ∈ G ⊓ stabSub I :=
      ⟨G.mul_mem (G.mul_mem haG hp.1) (G.inv_mem haG), hS.conj_mem_stab haG hp.1 hp.2⟩
    have hqc : (a * p * a⁻¹) c = c := by
      show a (p (a⁻¹ c)) = c
      rw [hainv, hpc', ha2]
    have h1 := hF5 _ hq hqc
    have h2 : (a * p * a⁻¹) (a c) = a (p c) := by
      show a (p (a⁻¹ (a c))) = a (p c)
      rw [MulAut.inv_apply_self]
    rw [h2] at h1
    exact a.injective h1
  obtain ⟨n0, hn0, hn0c⟩ : ∃ n0 ∈ G ⊓ stabSub I, n0 c ≠ c := by
    by_contra hcon
    push Not at hcon
    have hset : {x | ∃ n ∈ G ⊓ stabSub I, n c = x} = ({c} : Set V) := by
      ext x
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact hcon n hn
      · rintro rfl
        exact ⟨1, (G ⊓ stabSub I).one_mem, rfl⟩
    rw [hset, ← Subgroup.zpowers_eq_closure] at hgen
    have hcard : Nat.card I ≤ 2 := by
      rw [← hgen, Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (hV c)
    rw [card_eq_two_pow hV I] at hcard
    have : 2 ^ 3 ≤ 2 ^ rk I := Nat.pow_le_pow_right (by norm_num) hi
    omega
  have hc2I : n0 c ∈ I := hNI n0 hn0 c hcI
  have hc21 : n0 c ≠ 1 := fun h => hc1 (n0.injective (h.trans (map_one n0).symm))
  have hc2'I' : n0 (a c) ∈ I' := hNI' n0 hn0 _ hc'I'
  have hc2'1 : n0 (a c) ≠ 1 := fun h => hc'1 (n0.injective (h.trans (map_one n0).symm))
  have hc2'c' : n0 (a c) ≠ a c := fun h => hn0c (hF6 n0 hn0 h)
  have hn0inv : n0⁻¹ c ∈ I := hNI _ ((G ⊓ stabSub I).inv_mem hn0) c hcI
  obtain ⟨F, hF⟩ : ∃ F : Subgroup V,
      F = Subgroup.closure ({c, n0 c, a c, n0 (a c)} : Set V) := ⟨_, rfl⟩
  have hcF : c ∈ F := hF ▸ Subgroup.subset_closure (by simp)
  have hc2F : n0 c ∈ F := hF ▸ Subgroup.subset_closure (by simp)
  have hc'F : a c ∈ F := hF ▸ Subgroup.subset_closure (by simp)
  have hc2'F : n0 (a c) ∈ F := hF ▸ Subgroup.subset_closure (by simp)
  have hK0F : K0 ≤ F := by
    rw [hK0, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hcF
    · exact hc'F
  have hK0n0 : ∀ k ∈ K0, n0 k ∈ F := by
    have : K0 ≤ F.comap n0.toMonoidHom := by
      rw [hK0, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hc2F
      · exact hc2'F
    exact fun k hk => this hk
  have hfixF : ∀ g : MulAut V, g c = c → g (n0 c) = n0 c → g (a c) = a c →
      g (n0 (a c)) = n0 (a c) → ∀ f ∈ F, g f = f := by
    intro g h1 h2 h3 h4
    have : F ≤ fixSubOf g := by
      rw [hF, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    exact fun f hf => this hf
  obtain ⟨B1, hB1⟩ : ∃ B1 : Subgroup (MulAut V),
      B1 = (A ⊓ stabSub I) ⊓ MulAction.stabilizer (MulAut V) (n0 c) := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B2 : Subgroup (MulAut V),
      B2 = ((A ⊓ stabSub I) ⊓ MulAction.stabilizer (MulAut V) (n0⁻¹ c)).map
        (MulAut.conj n0).toMonoidHom := ⟨_, rfl⟩
  have hmemB2 : ∀ y ∈ B2, ∃ b ∈ A ⊓ stabSub I, b (n0⁻¹ c) = n0⁻¹ c ∧ y = n0 * b * n0⁻¹ := by
    intro y hy
    rw [hB2] at hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨b, hb.1, MulAction.mem_stabilizer_iff.mp hb.2, rfl⟩
  have hB1Q : B1 ≤ quadSub F := by
    intro x hx
    rw [hB1] at hx
    obtain ⟨hxB, hxs⟩ := hx
    have hxc2 : x (n0 c) = n0 c := MulAction.mem_stabilizer_iff.mp hxs
    have hp : n0⁻¹ * x * n0 ∈ G ⊓ stabSub I :=
      (G ⊓ stabSub I).mul_mem ((G ⊓ stabSub I).mul_mem ((G ⊓ stabSub I).inv_mem hn0)
        (hBN hxB)) hn0
    have hpc : (n0⁻¹ * x * n0) c = c := by
      show n0⁻¹ (x (n0 c)) = c
      rw [hxc2, MulAut.inv_apply_self]
    have h4 : x (n0 (a c)) = n0 (a c) := by
      have h1 : n0⁻¹ (x (n0 (a c))) = a c := hF5 _ hp hpc
      have h2 := congrArg n0 h1
      rwa [MulAut.apply_inv_self] at h2
    exact ⟨hfixF x (hBfix x hxB) hxc2 (hBfix' x hxB) h4, fun v => hK0F (hBmove x hxB v)⟩
  have hB2Q : B2 ≤ quadSub F := by
    intro y hy
    obtain ⟨b, hb, hbc, rfl⟩ := hmemB2 y hy
    have hyN : n0 * b * n0⁻¹ ∈ G ⊓ stabSub I :=
      (G ⊓ stabSub I).mul_mem ((G ⊓ stabSub I).mul_mem hn0 (hBN hb))
        ((G ⊓ stabSub I).inv_mem hn0)
    have h1 : (n0 * b * n0⁻¹) c = c := by
      show n0 (b (n0⁻¹ c)) = c
      rw [hbc, MulAut.apply_inv_self]
    have h2 : (n0 * b * n0⁻¹) (n0 c) = n0 c := by
      show n0 (b (n0⁻¹ (n0 c))) = n0 c
      rw [MulAut.inv_apply_self, hBfix b hb]
    have h3 : (n0 * b * n0⁻¹) (a c) = a c := hF5 _ hyN h1
    have h4 : (n0 * b * n0⁻¹) (n0 (a c)) = n0 (a c) := by
      show n0 (b (n0⁻¹ (n0 (a c)))) = n0 (a c)
      rw [MulAut.inv_apply_self, hBfix' b hb]
    refine ⟨hfixF _ h1 h2 h3 h4, fun v => ?_⟩
    have e : (n0 * b * n0⁻¹) v * v⁻¹ = n0 (b (n0⁻¹ v) * (n0⁻¹ v)⁻¹) := by
      show n0 (b (n0⁻¹ v)) * v⁻¹ = _
      rw [map_mul, map_inv, MulAut.apply_inv_self]
    rw [e]
    exact hK0n0 _ (hBmove b hb _)
  obtain ⟨E, hE⟩ : ∃ E : Subgroup (MulAut V), E = B1 ⊔ B2 := ⟨_, rfl⟩
  have hEQ : E ≤ quadSub F := hE ▸ sup_le hB1Q hB2Q
  have hB1G : B1 ≤ G := by
    rw [hB1]
    exact inf_le_left.trans hBG
  have hB2G : B2 ≤ G := by
    intro y hy
    obtain ⟨b, hb, -, rfl⟩ := hmemB2 y hy
    exact G.mul_mem (G.mul_mem hn0.1 (hBG hb)) (G.inv_mem hn0.1)
  have hEG : E ≤ G := hE ▸ sup_le hB1G hB2G
  have hB12 : ∀ z ∈ B1, z ∈ B2 → z = 1 := by
    intro z hz1 hz2
    have hz1' := hz1
    rw [hB1] at hz1'
    obtain ⟨b, hb, -, rfl⟩ := hmemB2 z hz2
    refine hfaith _ (hB2G hz2) fun u hu => ?_
    rcases hBc _ hz1'.1 u hu with h | h
    · exact h
    · exfalso
      have hu' : n0⁻¹ u ∈ I := hNI _ ((G ⊓ stabSub I).inv_mem hn0) u hu
      have e : (n0 * b * n0⁻¹) u = n0 (b (n0⁻¹ u)) := rfl
      rcases hBc b hb _ hu' with h' | h'
      · rw [e, h', MulAut.apply_inv_self] at h
        have : c = 1 := by
          have h2 : u * 1 = u * c := (mul_one u).trans h
          exact (mul_left_cancel h2).symm
        exact hc1 this
      · rw [e, h', map_mul, MulAut.apply_inv_self] at h
        exact hn0c (mul_left_cancel h)
  have hrkB1 : rk ↥(A ⊓ stabSub I) ≤ rk ↥B1 + 1 := by
    rw [hB1]
    exact rk_le_rk_stab_add_one hV hBfix (fun h hh => hBc h hh _ hc2I)
  have hrkB2 : rk ↥(A ⊓ stabSub I) ≤ rk ↥B2 + 1 := by
    have h1 := rk_le_rk_stab_add_one hV (v := n0⁻¹ c) hBfix (fun h hh => hBc h hh _ hn0inv)
    have h2 : rk ↥B2 = rk ↥((A ⊓ stabSub I) ⊓ MulAction.stabilizer (MulAut V) (n0⁻¹ c)) := by
      rw [hB2]
      unfold rk
      rw [Subgroup.card_map_of_injective (MulAut.conj n0).injective]
    omega
  have hcard2 : ∀ H : Subgroup (MulAut V), H ≤ E → Nat.card H = 2 ^ rk H := fun H hH =>
    card_eq_two_pow_of_isPGroup (isElemAbelian2_of_le_quadSub hV (hH.trans hEQ)).isPGroup
  have hcardE : Nat.card ↥B1 * Nat.card ↥B2 ≤ Nat.card ↥E := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun q : ↥B1 × ↥B2 =>
      (⟨q.1 * q.2, hE ▸ (B1 ⊔ B2).mul_mem (Subgroup.mem_sup_left q.1.2)
        (Subgroup.mem_sup_right q.2.2)⟩ : ↥E)) ?_
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h1 : (x : MulAut V) * y = x' * y' := congrArg Subtype.val h
    have h2 : (x' : MulAut V)⁻¹ * x = y' * (y : MulAut V)⁻¹ := by
      calc (x' : MulAut V)⁻¹ * x = (x' : MulAut V)⁻¹ * (x * y) * (y : MulAut V)⁻¹ := by group
        _ = (x' : MulAut V)⁻¹ * (x' * y') * (y : MulAut V)⁻¹ := by rw [h1]
        _ = y' * (y : MulAut V)⁻¹ := by group
    have hz1 : (x' : MulAut V)⁻¹ * x ∈ B1 := B1.mul_mem (B1.inv_mem x'.2) x.2
    have hz2 : (x' : MulAut V)⁻¹ * x ∈ B2 := by
      rw [h2]
      exact B2.mul_mem y'.2 (B2.inv_mem y.2)
    have hx : (x : MulAut V) = x' := by
      have := hB12 _ hz1 hz2
      rw [inv_mul_eq_one] at this
      exact this.symm
    have hy : (y : MulAut V) = y' := by
      rw [hx] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hrkE : rk ↥B1 + rk ↥B2 ≤ rk ↥E := by
    rw [hcard2 B1 (hE ▸ le_sup_left), hcard2 B2 (hE ▸ le_sup_right), hcard2 E le_rfl,
      ← pow_add] at hcardE
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcardE
  have hFfix : F ≤ fixV E := le_fixV_of_le_quadSub hEQ
  have hM1 : 2 ≤ rk ↥(I ⊓ fixV E) :=
    two_le_rk_of_mem hV ⟨hcI, hFfix hcF⟩ ⟨hc2I, hFfix hc2F⟩ hc1 hc21 (Ne.symm hn0c)
  have hM2 : 2 ≤ rk ↥(I' ⊓ fixV E) :=
    two_le_rk_of_mem hV ⟨hc'I', hFfix hc'F⟩ ⟨hc2'I', hFfix hc2'F⟩ hc'1 hc2'1 (Ne.symm hc2'c')
  have hsum := rk_sup_add_rk_inf (I ⊓ fixV E) (I' ⊓ fixV E)
  have hinf : (I ⊓ fixV E) ⊓ (I' ⊓ fixV E) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hS.disj hx.1.1 hx.2.1)
  rw [hinf, rk_bot] at hsum
  have hle : rk ↥((I ⊓ fixV E) ⊔ (I' ⊓ fixV E)) ≤ rk ↥(fixV E) :=
    rk_mono (sup_le inf_le_right inf_le_right)
  have hidx := rk_add_rkIdx (fixV E)
  have hV2 := hS.rk_add
  have hI' := hS.rk_eq_of_swap haG haI
  have hpos : 0 < rk ↥E := by omega
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, rk_bot] at hpos
    omega
  refine ⟨E, ⟨hEG, hEne, isElemAbelian2_of_le_quadSub hV hEQ⟩,
    commSeries_two_of_le_quadSub hEQ, ?_⟩
  have hfin : rkIdx (fixV E) ≤ rk ↥E := by omega
  unfold rAV
  rw [div_le_one (by exact_mod_cast hpos)]
  exact_mod_cast hfin

end Main

end CFSG.Quasithin
