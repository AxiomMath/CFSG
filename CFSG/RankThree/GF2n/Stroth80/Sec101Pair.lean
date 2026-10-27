module

public import CFSG.RankThree.GF2n.Stroth80.Sec101ThmG

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem IsSaturated101.conj_le_X_of_mem_LB_of_commutator
    (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X : Subgroup G} (hX : IsMaxClique101 M Q Z B X) (hsat : IsSaturated101 M Q Z B X)
    {C : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X) {σ τ : G}
    (hσ : σ ∈ LB M Q C) (hσQ : σ ∉ Q) (hστ : ⁅σ, τ⁆ ∈ Q) (hτM : τ ∈ M)
    (hne : C ⊔ Z ≠ conjSubgroup τ C ⊔ Z) : conjSubgroup τ C ≤ X := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have hC' : IsRootB M B (conjSubgroup τ C) := hC.conj hτM
  have hσC' : σ ∈ LB M Q (conjSubgroup τ C) := by
    rw [hcC.LB_conj hτM, mem_conjSubgroup]
    have h1 : τ⁻¹ * σ * τ = (τ⁻¹ * ⁅σ, τ⁆ * τ) * σ := by
      rw [commutatorElement_def]; group
    rw [h1]
    exact (LB M Q C).mul_mem (sec39_Q_le_LB ((hcC.conj_mem_Q_of_mem_M hτM).2 _ hστ)) hσ
  have hR : Rt M (LB M Q C) σ ≠ LB M Q C := hC.Rt_ne H hC' hσC' hne
  exact (sec39_conjB_le_Vt hτM (by rw [← hcC.LB_conj hτM]; exact hσC')).trans
    (IsSaturated101.Vt_le h34 H hX.1 hsat hC hCX hσ hσQ hR)

private theorem IsSaturated101.conj_eq_self_of_conj_root_le
    {hc : Ctx M Q Z B} {X : Subgroup G} (hX : IsClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) {C : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X)
    {τ : G} (hτM : τ ∈ M) (hC'X : conjSubgroup τ C ≤ X) : conjSubgroup τ X = X := by
  have hC' : IsRootB M B (conjSubgroup τ C) := hC.conj hτM
  rcases IsSaturated101.inf_eq hc hX hsat hτM with h | h
  · exact absurd ((le_inf hC'X (Subgroup.map_mono hCX)).trans h.le) (hC'.not_le_Z hc)
  · exact h

private theorem IsSaturated101.comm_mem_Z_of_mem_centralizer
    {hc : Ctx M Q Z B} {X X' : Subgroup G} (hsat' : IsSaturated101 M Q Z B X')
    (hX : IsClique101 M Q Z B X) (hXX' : X ⊓ X' = Z)
    {D : Subgroup G} (hD : IsRootB M B D) (hDX' : D ≤ X') {τ : G}
    (hτ : τ ∈ LB M Q D) (hcommX : ∀ w ∈ X, ⁅w, τ⁆ ∈ X) :
    ∀ w ∈ X, w ∈ Subgroup.centralizer (D : Set G) → ⁅w, τ⁆ ∈ Z := by
  have hcD : Ctx M Q Z D := hD.ctx hc
  have hZD : X ⊓ QB D ≤ Z :=
    IsSaturated101.inf_QB_le_Z hc hsat' hX (by rw [inf_comm]; exact hXX') hD hDX'
  intro w hw hwD
  have hwN : w ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.mem_normalizer_fintype fun d hd => by
      rw [show w * d * w⁻¹ = d by
        rw [← Subgroup.mem_centralizer_iff.mp hwD d hd]; group]
      exact hd
  exact hZD ⟨hcommX w hw, (hcD.comm_mem_inf_QB_of_mem_normalizer (hX.le_Q hw) hwN hτ).2⟩

private theorem IsSaturated101.exists_commutator_not_mem_Z
    {hc : Ctx M Q Z B} {C D : Subgroup G} (hC : IsRootB M B C) (hD : IsRootB M B D)
    {τ : G} (hτ : τ ∈ LB M Q D) (hne : C ⊔ Z ≠ conjSubgroup τ C ⊔ Z) :
    ∃ x ∈ C, ⁅x, τ⁆ ∉ Z := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have hτM : τ ∈ M := (hD.ctx hc).LB_le_M hτ
  by_contra hall
  push Not at hall
  have hle : conjSubgroup τ C ≤ Z ⊔ C := by
    intro y hy
    have hc' : τ⁻¹ * y * τ ∈ C := mem_conjSubgroup.mp hy
    have e : y = (τ⁻¹ * y * τ) * ⁅(τ⁻¹ * y * τ)⁻¹, τ⁆ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact (Z ⊔ C).mul_mem (Subgroup.mem_sup_right hc')
      (Subgroup.mem_sup_left (hall _ (C.inv_mem hc')))
  obtain ⟨p, hpQ, hpC⟩ := hcC.exists_conj_of_le_ZB ((hC.conj hτM).ctx hc) hle
  have e := hcC.conj_sup_Z_of_mem_Q hpQ
  rw [conjSubgroup_sup', hcC.conj_Z_eq (hc.hyp.Q_normal.1 hpQ)] at e
  exact hne (by rw [← hpC, e])

private theorem IsSaturated101.mem_normalizer_sup_Z_of_commutator
    {hc : Ctx M Q Z B} {E : Subgroup G} (hE : IsRootB M B E) {x τ : G}
    (hxE : ⁅x, τ⁆ ∈ E) (hxZ : ⁅x, τ⁆ ∉ Z) (hxτ : ⁅⁅x, τ⁆, τ⁆ ∈ Z)
    (hτM : τ ∈ M) : τ ∈ Subgroup.normalizer ((E ⊔ Z : Subgroup G) : Set G) := by
  have hcE : Ctx M Q Z E := hE.ctx hc
  have hEτ : IsRootB M B (conjSubgroup τ E) := hE.conj hτM
  set y := ⁅x, τ⁆ with hy
  have hle : conjSubgroup τ E ≤ Z ⊔ E := by
    rw [sup_comm]
    by_contra hnle
    have hI := IsRootB.inf_sup_Z_eq_Z_of_not_le (hc := hc) hE hEτ hnle
    have hmem : τ * y * τ⁻¹ ∈ (E ⊔ Z) ⊓ (conjSubgroup τ E ⊔ Z) := by
      refine ⟨?_, Subgroup.mem_sup_left ?_⟩
      · rw [show τ * y * τ⁻¹ = ⁅y, τ⁆⁻¹ * y by rw [commutatorElement_def]; group]
        exact (E ⊔ Z).mul_mem (Subgroup.mem_sup_right (Z.inv_mem hxτ))
          (Subgroup.mem_sup_left hxE)
      · rw [mem_conjSubgroup]; simpa [mul_assoc] using hxE
    rw [hI] at hmem
    have hzy : y ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hτM)) _).mp hmem
      simpa [mul_assoc] using this
    exact hxZ hzy
  obtain ⟨p, hpQ, hpE⟩ := hcE.exists_conj_of_le_ZB (hEτ.ctx hc) hle
  apply conjSubgroup_eq_self_iff.mp
  have e := hcE.conj_sup_Z_of_mem_Q hpQ
  rw [conjSubgroup_sup', hcE.conj_Z_eq (hc.hyp.Q_normal.1 hpQ), hpE] at e
  rw [conjSubgroup_sup', hcE.conj_Z_eq hτM, e]

private theorem IsSaturated101.false_of_commutator_root
    (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X X' : Subgroup G} (hX : IsMaxClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) (hX' : IsClique101 M Q Z B X')
    (hsat' : IsSaturated101 M Q Z B X') (hXX' : X ⊓ X' = Z)
    {C D : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X)
    (hD : IsRootB M B D) (hDX' : D ≤ X') {τ : G}
    (hτ : τ ∈ LB M Q D) (hτQ : τ ∉ Q)
    (hcommX : ∀ w ∈ X, ⁅w, τ⁆ ∈ X)
    (h3 : ∀ w ∈ X, w ∈ Subgroup.centralizer (D : Set G) → ⁅w, τ⁆ ∈ Z)
    (hne : C ⊔ Z ≠ conjSubgroup τ C ⊔ Z) : False := by
  have hcD : Ctx M Q Z D := hD.ctx hc
  have hτM : τ ∈ M := hcD.LB_le_M hτ
  obtain ⟨x, hxC, hyZ⟩ :=
    IsSaturated101.exists_commutator_not_mem_Z (hc := hc) hC hD hτ hne
  have hyX : ⁅x, τ⁆ ∈ X := hcommX x (hCX hxC)
  have hyτ : ⁅⁅x, τ⁆, τ⁆ ∈ Z :=
    h3 _ hyX (hcD.comm_mem_centralizer_of_mem_LB (hX.1.le_Q (hCX hxC)) hτ).2
  obtain ⟨E, hE, hyE, hEX⟩ := hX.1.cover _ hyX hyZ
  have hcE : Ctx M Q Z E := hE.ctx hc
  have hτE : τ ∈ Subgroup.normalizer ((E ⊔ Z : Subgroup G) : Set G) :=
    IsSaturated101.mem_normalizer_sup_Z_of_commutator (hc := hc) hE hyE hyZ hyτ hτM
  exact hτQ (IsSaturated101.mem_Q_of_mem_normalizer h34 H hX hsat hX' hsat' hXX' hE hEX hD hDX'
    hτ (hcE.mem_normalizer_LB_of_normalizer hτM hτE))

private theorem IsSaturated101.false_of_not_normalizing_LB
    (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X X' : Subgroup G} (hX : IsMaxClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) (hX' : IsClique101 M Q Z B X')
    (hsat' : IsSaturated101 M Q Z B X') (hXX' : X ⊓ X' = Z)
    {C D : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X)
    (hD : IsRootB M B D) (hDX' : D ≤ X') {σ τ : G}
    (hσ : σ ∈ LB M Q C) (hσQ : σ ∉ Q) (hτ : τ ∈ LB M Q D) (hτQ : τ ∉ Q)
    (hστ : ⁅σ, τ⁆ ∈ Q) (hτN : τ ∉ Subgroup.normalizer (LB M Q C : Set G)) : False := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have hτM : τ ∈ M := (hD.ctx hc).LB_le_M hτ
  have hτCZ : τ ∉ Subgroup.normalizer ((C ⊔ Z : Subgroup G) : Set G) := fun h =>
    hτN (hcC.mem_normalizer_LB_of_normalizer hτM h)
  have hne : C ⊔ Z ≠ conjSubgroup τ C ⊔ Z := by
    intro h
    apply hτCZ
    apply conjSubgroup_eq_self_iff.mp
    rw [conjSubgroup_sup', hcC.conj_Z_eq hτM, ← h]
  have hC'X : conjSubgroup τ C ≤ X :=
    IsSaturated101.conj_le_X_of_mem_LB_of_commutator h34 H hX hsat hC hCX hσ hσQ hστ hτM hne
  have hXτ : conjSubgroup τ X = X :=
    IsSaturated101.conj_eq_self_of_conj_root_le (hc := hc) hX.1 hsat hC hCX hτM hC'X
  have hτX : τ ∈ Subgroup.normalizer (X : Set G) := conjSubgroup_eq_self_iff.mp hXτ
  have hcommX : ∀ w ∈ X, ⁅w, τ⁆ ∈ X := fun w hw => by
    rw [commutatorElement_def]
    simpa [mul_assoc] using
      X.mul_mem hw ((Subgroup.mem_normalizer_iff.mp hτX _).mp (X.inv_mem hw))
  have h3 :=
    IsSaturated101.comm_mem_Z_of_mem_centralizer (hc := hc) hsat' hX.1 hXX' hD hDX' hτ hcommX
  exact IsSaturated101.false_of_commutator_root h34 H hX hsat hX' hsat' hXX' hC hCX hD hDX'
    hτ hτQ hcommX h3 hne

theorem IsSaturated101.no_commuting_pair (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {X X' : Subgroup G} (hX : IsMaxClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) (hX' : IsClique101 M Q Z B X')
    (hsat' : IsSaturated101 M Q Z B X') (hXX' : X ⊓ X' = Z) {C D : Subgroup G}
    (hC : IsRootB M B C) (hCX : C ≤ X) (hD : IsRootB M B D) (hDX' : D ≤ X') {σ τ : G}
    (hσ : σ ∈ LB M Q C) (hσQ : σ ∉ Q) (hτ : τ ∈ LB M Q D) (hτQ : τ ∉ Q)
    (hστ : ⁅σ, τ⁆ ∈ Q) : False := by
  by_cases hτN : τ ∈ Subgroup.normalizer (LB M Q C : Set G)
  · exact hτQ (IsSaturated101.mem_Q_of_mem_normalizer h34 H hX hsat hX' hsat' hXX' hC hCX hD
      hDX' hτ hτN)
  · exact IsSaturated101.false_of_not_normalizing_LB h34 H hX hsat hX' hsat' hXX' hC hCX hD
      hDX' hσ hσQ hτ hτQ hστ hτN

end CFSG.RankThree.GF2n.Stroth80
