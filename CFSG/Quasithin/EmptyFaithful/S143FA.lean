module

public import CFSG.Quasithin.EmptyFaithful.S143EB
public import CFSG.Quasithin.EmptyFaithful.S143ED

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Model

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem exists_mem_ne_of_card_four {A : Subgroup W} (hA : Nat.card A = 4) (u : W) :
    ∃ a ∈ A, a ≠ 1 ∧ a ≠ u := by
  by_contra hall
  push Not at hall
  have hsub : (A : Set W) ⊆ {1, u} := fun a ha => by
    by_cases h1 : a = 1
    · exact Or.inl h1
    · exact Or.inr (hall a ha h1)
  have h1 : Nat.card A = (A : Set W).ncard := Nat.card_coe_set_eq _
  have h2 : (A : Set W).ncard ≤ ({1, u} : Set W).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({1, u} : Set W).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
  omega

theorem q_eq_zero_of_mul (h : OfourStruct X L₁ L₂ t) {q : W → ZMod 2}
    (hq : ∀ w, q w = 1 ↔ (w ∈ commV L₁ ∨ w ∈ commV L₂) ∧ w ≠ 1) {a b : W} (ha : a ∈ commV L₁)
    (hb : b ∈ commV L₂) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : q (a * b) = 0 := by
  by_contra hne
  have hq1 : q (a * b) = 1 := by
    revert hne
    generalize q (a * b) = y
    revert y
    decide
  obtain ⟨hmem, -⟩ := (hq _).mp hq1
  rcases hmem with hm | hm
  · have : b ∈ commV L₁ := by
      have := (commV L₁).mul_mem ((commV L₁).inv_mem ha) hm
      simpa using this
    have h2 : b ∈ commV L₁ ⊓ commV L₂ := ⟨this, hb⟩
    rw [h.inf, Subgroup.mem_bot] at h2
    exact hb1 h2
  · have : a ∈ commV L₂ := by
      have := (commV L₂).mul_mem hm ((commV L₂).inv_mem hb)
      simpa using this
    have h2 : a ∈ commV L₁ ⊓ commV L₂ := ⟨ha, this⟩
    rw [h.inf, Subgroup.mem_bot] at h2
    exact ha1 h2

theorem exists_singular_perp (h : OfourStruct X L₁ L₂ t) {q : W → ZMod 2}
    (hq : ∀ w, q w = 1 ↔ (w ∈ commV L₁ ∨ w ∈ commV L₂) ∧ w ≠ 1)
    (hexp : ∀ w : W, w * w = 1) {v : W} (hv1 : v ≠ 1) (hvq : q v = 0) :
    ∃ x : W, x ≠ 1 ∧ x ≠ v ∧ q x = 0 ∧ q (v * x) = 0 := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hv⟩ := h.exists_decomp_W v
  have hu₁1 : u₁ ≠ 1 := by
    intro he
    rw [he, one_mul] at hv
    have : q v = 1 := (hq v).mpr ⟨Or.inr (hv ▸ hu₂), hv1⟩
    rw [hvq] at this
    exact zero_ne_one this
  have hu₂1 : u₂ ≠ 1 := by
    intro he
    rw [he, mul_one] at hv
    have : q v = 1 := (hq v).mpr ⟨Or.inl (hv ▸ hu₁), hv1⟩
    rw [hvq] at this
    exact zero_ne_one this
  obtain ⟨u₁', hu₁', hu₁'1, hu₁'u⟩ := exists_mem_ne_of_card_four h.card_U₁ u₁
  obtain ⟨u₂', hu₂', hu₂'1, hu₂'u⟩ := exists_mem_ne_of_card_four
    (S1417.card_of_actsAsNaturalL2 h.nat₂).2 u₂
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hexp w)
  refine ⟨u₁' * u₂', ?_, ?_, q_eq_zero_of_mul h hq hu₁' hu₂' hu₁'1 hu₂'1, ?_⟩
  · intro he
    have := S1417.eq_of_mul_eq_of_inf_eq_bot h.inf hu₁' (commV L₁).one_mem hu₂' (commV L₂).one_mem
      (by rw [he, mul_one])
    exact hu₁'1 this.1
  · intro he
    have := S1417.eq_of_mul_eq_of_inf_eq_bot h.inf hu₁' hu₁ hu₂' hu₂ (by rw [he, hv])
    exact hu₁'u this.1
  · have e : v * (u₁' * u₂') = (u₁ * u₁') * (u₂ * u₂') := by
      rw [hv]
      calc u₁ * u₂ * (u₁' * u₂') = u₁ * (u₂ * u₁') * u₂' := by group
        _ = u₁ * (u₁' * u₂) * u₂' := by rw [mul_comm u₂ u₁']
        _ = (u₁ * u₁') * (u₂ * u₂') := by group
    rw [e]
    refine q_eq_zero_of_mul h hq ((commV L₁).mul_mem hu₁ hu₁') ((commV L₂).mul_mem hu₂ hu₂') ?_ ?_
    · intro he
      apply hu₁'u
      have := mul_eq_one_iff_eq_inv.mp he
      rw [hinv] at this
      exact this.symm
    · intro he
      apply hu₂'u
      have := mul_eq_one_iff_eq_inv.mp he
      rw [hinv] at this
      exact this.symm

end Model

section Counterexample

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.exists_involution_wOfU :
    ∃ r ∈ Hyp1281Two.wOfU T M, r ∉ VZ T M ∧ r * r = 1 := by
  have h := c.h1281
  have hg := c.goodElt
  obtain ⟨z, a, hzZ, hz1, rfl, haV, haZ, hzz, haa, hza, hga, hgza, hcases⟩ :=
    exists_three_cycle h hg
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := c.c15.orth
  have hHN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    h.uOfL22_le_g1.trans hHN
  have haU : g * z * g⁻¹ ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M haV
  set a := g * z * g⁻¹ with ha
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
    { (inferInstance : Group ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) with
      mul_comm := fun x y => (tilde_isMulCommutative h).is_comm.comm x y }
  obtain ⟨L₁, L₂, t, hS, hsing⟩ := exists_ofourStruct_of_plusType
    (W := ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) (q := q)
    (tilde_mul_self h) hq4 hq1 hq2 hq3
  set aN : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) := ⟨a, hUN haU⟩ with haN
  set v' : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
    ⟨secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) aN, secMk_mem_secImg (X := uOfL22 T M) (x := aN) haU⟩ with hv'
  have hv'q : q v' = 0 :=
    (hq5 v'.1 v'.2 aN haU rfl).mpr (by rw [sq]; exact haa)
  have hv'1 : v' ≠ 1 := by
    intro he
    apply haZ
    have : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) aN = 1 := congrArg Subtype.val he
    exact secMk_eq_one_iff.mp this
  obtain ⟨x, hx1, hxv, hxq, hvxq⟩ := exists_singular_perp hS hsing (tilde_mul_self h) hv'1 hv'q
  obtain ⟨w, hwU, hwx⟩ := mem_secImg.1 x.2
  have hw2 : (w : G) ^ 2 = 1 := (hq5 x.1 x.2 w hwU hwx).mp hxq
  have haw2 : ((aN * w : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) : G) ^ 2 = 1 := by
    refine (hq5 (v' * x).1 (v' * x).2 (aN * w) ((uOfL22 T M).mul_mem haU hwU) ?_).mp hvxq
    rw [map_mul]
    exact congrArg₂ (· * ·) rfl hwx
  have hwa : (w : G) * a = a * (w : G) := by
    have h1 : (a * (w : G)) * (a * (w : G)) = 1 := by
      have := haw2
      rw [sq] at this
      exact this
    have h2 : (w : G) * (w : G) = 1 := by rw [← sq]; exact hw2
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    have hwi : (w : G)⁻¹ = (w : G) := inv_eq_of_mul_eq_one_right h2
    have h3 : a * (w : G) = (a * (w : G))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [mul_inv_rev, hai, hwi] at h3
    exact h3.symm
  have hzU : ∀ y ∈ uOfL22 T M, y * z = z * y := fun y hy =>
    Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 hzZ).2 y hy
  have hwV : ∀ y ∈ VZ T M, y * (w : G) = (w : G) * y := by
    intro y hy
    rcases hcases y hy with rfl | rfl | rfl | rfl
    · simp
    · exact (hzU (w : G) hwU).symm
    · exact hwa.symm
    · calc z * a * (w : G) = z * (a * (w : G)) := mul_assoc _ _ _
        _ = z * ((w : G) * a) := by rw [hwa]
        _ = (z * (w : G)) * a := (mul_assoc _ _ _).symm
        _ = ((w : G) * z) * a := by rw [(hzU (w : G) hwU).symm]
        _ = (w : G) * (z * a) := mul_assoc _ _ _
  refine ⟨(w : G), ⟨hwU, Subgroup.mem_centralizer_iff.mpr fun y hy => hwV y hy⟩, ?_, by
    rw [← sq]; exact hw2⟩
  intro hrV
  have hxe : x.1 = secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) w := hwx.symm
  have hxone : ∀ y : G, (w : G) = y → y ∈ quasithinOmegaOneCenter T → False := by
    intro y hy hyZ
    apply hx1
    apply Subtype.ext
    rw [hxe]
    exact secMk_eq_one_iff.mpr (by rw [hy]; exact hyZ)
  have hxa : ∀ y : G, (w : G) = y → y⁻¹ * a ∈ quasithinOmegaOneCenter T → False := by
    intro y hy hyZ
    apply hxv
    apply Subtype.ext
    rw [hxe]
    show _ = secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) aN
    rw [secMk_eq_secMk_iff]
    rw [hy]
    exact hyZ
  rcases hcases _ hrV with he | he | he | he
  · exact hxone 1 he (quasithinOmegaOneCenter T).one_mem
  · exact hxone z he hzZ
  · exact hxa a he (by rw [inv_mul_cancel]; exact (quasithinOmegaOneCenter T).one_mem)
  · refine hxa (z * a) he ?_
    have : (z * a)⁻¹ * a = z⁻¹ := by rw [hza]; group
    rw [this]
    exact (quasithinOmegaOneCenter T).inv_mem hzZ

end Counterexample

end S143

end CFSG.Quasithin
