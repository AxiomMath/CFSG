module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks

public section

namespace CFSG.StandardType

variable {G : Type} [Group G]

theorem ggSecFiveBPermSpK_eta_eq_one_of_mem_centralizer {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {b : ↥Bs} (hb : (b : G) ∈ Subgroup.centralizer (K : Set G)) {j : Fin n} (hj : j ≠ i0) :
    eta b j = 1 := by
  have hmem : SpCoord.sgnAut j ∈ (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hA]
    exact Subgroup.subset_closure (Or.inl ⟨j, hj, rfl⟩)
  obtain ⟨φ, hφ, hφeq⟩ := Subgroup.mem_map.mp hmem
  have hcongr : MulAut.congr eta φ = SpCoord.sgnAut j := hφeq
  obtain ⟨g, hgK, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
  have hcomm : g * b = b * g := Subgroup.mem_centralizer_iff.mp hb g hgK
  have hfix : φ b = b := Subtype.ext (by rw [hg b, hcomm]; group)
  have h1 : MulAut.congr eta φ (eta b) = eta b := by
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hfix]
  have h2 : eta b j = (eta b j)⁻¹ := by
    have h := congrArg (fun f => f j) h1
    rw [hcongr, SpCoord.sgnAut_apply, Function.update_self] at h
    exact h.symm
  have h3 : Multiplicative.toAdd (eta b j) = - Multiplicative.toAdd (eta b j) := by
    simpa using congrArg Multiplicative.toAdd h2
  have h4 := SpCoord.coord_eq_zero_of_eq_neg (Fact.out : p.Prime) hp2 h3
  refine Multiplicative.toAdd.injective ?_
  simpa using h4

theorem ggSecFiveBPermSpK_card_inf_centralizer_le {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p := by
  let C : Subgroup G := Subgroup.centralizer (K : Set G)
  let f : ↥(Bs ⊓ C) → Multiplicative (ZMod p) :=
    fun c => eta ⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩ i0
  have hf : Function.Injective f := by
    intro c₁ c₂ h
    have hc₁ : (c₁ : G) ∈ C := (Subgroup.mem_inf.mp c₁.2).2
    have hc₂ : (c₂ : G) ∈ C := (Subgroup.mem_inf.mp c₂.2).2
    have hcoord : ∀ j, eta ⟨(c₁ : G), (Subgroup.mem_inf.mp c₁.2).1⟩ j =
        eta ⟨(c₂ : G), (Subgroup.mem_inf.mp c₂.2).1⟩ j := by
      intro j
      by_cases hj : j = i0
      · rw [hj]; exact h
      · rw [ggSecFiveBPermSpK_eta_eq_one_of_mem_centralizer hp2 hA hc₁ hj,
            ggSecFiveBPermSpK_eta_eq_one_of_mem_centralizer hp2 hA hc₂ hj]
    have hsub : (⟨(c₁ : G), (Subgroup.mem_inf.mp c₁.2).1⟩ : ↥Bs) =
        ⟨(c₂ : G), (Subgroup.mem_inf.mp c₂.2).1⟩ :=
      eta.injective (funext hcoord)
    exact Subtype.ext (congrArg (fun x : ↥Bs => (x : G)) hsub)
  have hcard := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at hcard

theorem ggSecFiveBPermSpK_pow_mul_card_inf_centralizer_le {p r : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))}
    {i0 : Fin (r + 2)}
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (r + 2) p i0) :
    p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card ↥Bs := by
  have hcent := ggSecFiveBPermSpK_card_inf_centralizer_le hp2 hA
  have hcardZ : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcardBs : Nat.card ↥Bs = p ^ (r + 2) := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_fun, hcardZ, Nat.card_fin]
  rw [hcardBs]
  calc p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤
        p ^ (r + 1) * p := Nat.mul_le_mul_left _ hcent
    _ = p ^ (r + 2) :=
        (pow_succ p (r + 1)).symm.trans (by rw [show r + 1 + 1 = r + 2 by omega])

theorem card_bstar_inf_center_le_of_bCoordinateBlock {G : Type} [Group G] {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hAut : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Finite ↥Bs :=
    Finite.of_equiv (Fin n → Multiplicative (ZMod p)) eta.toEquiv.symm
  let hCB : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ Bs := inf_le_left
  letI : Finite ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
    Finite.of_injective (Subgroup.inclusion hCB) (Subgroup.inclusion_injective hCB)
  have hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p :=
    ggSecFiveBPermSpK_card_inf_centralizer_le hp2 hAut
  have hle : Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) ≤
      Bs ⊓ Subgroup.centralizer (X : Set G) := by
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  exact (Subgroup.card_le_of_le hle).trans hC

theorem ggSecFiveBPermSpK_eta_eq_one_of_mem_centralizer_of_bBlockOn {G : Type} [Group G]
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {I : Finset (Fin n)}
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I)
    {b : ↥Bs} (hb : (b : G) ∈ Subgroup.centralizer (K : Set G)) {j : Fin n} (hj : j ∈ I) :
    eta b j = 1 := by
  have hmem : SpCoord.sgnAut j ∈ (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hA]
    exact Subgroup.subset_closure (Or.inl ⟨j, hj, rfl⟩)
  obtain ⟨φ, hφ, hφeq⟩ := Subgroup.mem_map.mp hmem
  have hcongr : MulAut.congr eta φ = SpCoord.sgnAut j := hφeq
  obtain ⟨g, hgK, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
  have hcomm : g * b = b * g := Subgroup.mem_centralizer_iff.mp hb g hgK
  have hfix : φ b = b := Subtype.ext (by rw [hg b, hcomm]; group)
  have h1 : MulAut.congr eta φ (eta b) = eta b := by
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hfix]
  have h2 : eta b j = (eta b j)⁻¹ := by
    have h := congrArg (fun f => f j) h1
    rw [hcongr, SpCoord.sgnAut_apply, Function.update_self] at h
    exact h.symm
  have h3 : Multiplicative.toAdd (eta b j) = - Multiplicative.toAdd (eta b j) := by
    simpa using congrArg Multiplicative.toAdd h2
  have h4 := SpCoord.coord_eq_zero_of_eq_neg (Fact.out : p.Prime) hp2 h3
  refine Multiplicative.toAdd.injective ?_
  simpa using h4

theorem ggSecFiveBPermSpK_pow_mul_card_inf_centralizer_le_of_bBlockOn {G : Type} [Group G]
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {I : Finset (Fin n)}
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I) :
    p ^ I.card * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card ↥Bs := by
  classical
  let C : Subgroup G := Subgroup.centralizer (K : Set G)
  let f : ↥(Bs ⊓ C) → ({j // j ∉ I} → Multiplicative (ZMod p)) :=
    fun c j => eta ⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩ j
  have hf : Function.Injective f := by
    intro c₁ c₂ h
    have hc₁ : (c₁ : G) ∈ C := (Subgroup.mem_inf.mp c₁.2).2
    have hc₂ : (c₂ : G) ∈ C := (Subgroup.mem_inf.mp c₂.2).2
    have hcoord : ∀ j, eta ⟨(c₁ : G), (Subgroup.mem_inf.mp c₁.2).1⟩ j =
        eta ⟨(c₂ : G), (Subgroup.mem_inf.mp c₂.2).1⟩ j := by
      intro j
      by_cases hj : j ∈ I
      · rw [ggSecFiveBPermSpK_eta_eq_one_of_mem_centralizer_of_bBlockOn hp2 hA hc₁ hj,
          ggSecFiveBPermSpK_eta_eq_one_of_mem_centralizer_of_bBlockOn hp2 hA hc₂ hj]
      · exact congrFun h ⟨j, hj⟩
    have hsub : (⟨(c₁ : G), (Subgroup.mem_inf.mp c₁.2).1⟩ : ↥Bs) =
        ⟨(c₂ : G), (Subgroup.mem_inf.mp c₂.2).1⟩ :=
      eta.injective (funext hcoord)
    exact Subtype.ext (congrArg (fun x : ↥Bs => (x : G)) hsub)
  have hcardZ : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcomp : Nat.card {j // j ∉ I} = n - I.card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun j => Finset.mem_compl.symm),
      Nat.card_eq_finsetCard, Finset.card_compl, Fintype.card_fin]
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fun, hcardZ, hcomp] at hcard
  have hcardBs : Nat.card ↥Bs = p ^ n := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_fun, hcardZ, Nat.card_fin]
  have hIn : I.card ≤ n := by simpa using I.card_le_univ
  rw [hcardBs]
  calc p ^ I.card * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤
        p ^ I.card * p ^ (n - I.card) := Nat.mul_le_mul_left _ hcard
    _ = p ^ n := by rw [← pow_add, Nat.add_sub_cancel' hIn]

end CFSG.StandardType

end
