module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Par
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4GCover
public import CFSG.Quasithin.EmptyFaithful.A38c5Ker
public import CFSG.Quasithin.EmptyFaithful.SBd8Abs
public import CFSG.Quasithin.EmptyFaithful.S153D51
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4GRank

public section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.S15223P4.G (le_normalizer_V pCoreOf_le_centralizer not_le_centralizer_V
  inf_centralizer_eq_pCoreOf)

namespace CFSG.Quasithin.S15223P4.D1

section Preimage

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M]

theorem isParabolic2_map_of_ker_le (ρ : Γ →* M) (hρ : Function.Surjective ρ)
    (hk : IsPGroup 2 ρ.ker) {Q : Subgroup Γ} (h : IsParabolic2 (⊤ : Subgroup Γ) Q) :
    IsParabolic2 (⊤ : Subgroup M) (Q.map ρ) := by
  obtain ⟨-, S', hS', hN⟩ := h
  have hkS := SzN2.ker_le_of_isSylowTwoOf hk hS'
  refine ⟨le_top, S'.map ρ, isSylowTwoOf_top_map_of_surjective hS' ρ hρ, ?_⟩
  intro m hm
  obtain ⟨x, rfl⟩ := hρ m
  have hx : x ∈ Subgroup.normalizer (S' : Set Γ) := SzN2.mem_normalizer_of_ker_le ρ hkS hm.2
  exact Subgroup.mem_map_of_mem ρ (hN ⟨Subgroup.mem_top _, hx⟩)

theorem isMaxParabolic2_of_map_of_ker_le (ρ : Γ →* M) (hρ : Function.Surjective ρ)
    (hk : IsPGroup 2 ρ.ker) {P : Subgroup Γ} (hkP : ρ.ker ≤ P)
    (h : IsMaxParabolic2 (⊤ : Subgroup M) (P.map ρ)) : IsMaxParabolic2 (⊤ : Subgroup Γ) P := by
  have hcm : (P.map ρ).comap ρ = P := Subgroup.comap_map_eq_self hkP
  obtain ⟨hpar, hne, hmax⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨-, U, hU, hNU⟩ := hpar
    have hS : IsSylowTwoOf (U.comap ρ) ⊤ := by
      refine ⟨le_top, hU.2.1.comap_of_ker_isPGroup ρ hk, ?_⟩
      have h1 : ((U.comap ρ).subgroupOf ⊤).index = (U.comap ρ).index :=
        Subgroup.relIndex_top_right _
      rw [h1, Subgroup.index_comap_of_surjective _ hρ]
      have h2 := hU.2.2
      rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h2
    have hkS' : ρ.ker ≤ U.comap ρ := Subgroup.ker_le_comap ρ U
    have hmapU : (U.comap ρ).map ρ = U := Subgroup.map_comap_eq_self_of_surjective hρ U
    refine ⟨le_top, U.comap ρ, hS, fun x hx => ?_⟩
    have h1 := SzN2.map_mem_normalizer_map ρ hρ hkS' hx.2
    rw [hmapU] at h1
    have h2 := hNU ⟨Subgroup.mem_top _, h1⟩
    rw [← hcm]
    exact h2
  · intro htop
    apply hne
    rw [htop, Subgroup.map_top_of_surjective _ hρ]
  · intro Q hQ hQtop hPQ
    have hkQ : ρ.ker ≤ Q := hkP.trans hPQ
    have hQ' := isParabolic2_map_of_ker_le ρ hρ hk hQ
    have hne' : Q.map ρ ≠ ⊤ := fun htop => hQtop (by
      rw [← Subgroup.comap_map_eq_self hkQ, htop, Subgroup.comap_top])
    have heq := hmax _ hQ' hne' (Subgroup.map_mono hPQ)
    rw [← Subgroup.comap_map_eq_self hkQ, heq, hcm]

end Preimage

section Equiv

noncomputable def statedSL_equiv_SL3F2 {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) :
    ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) ≃* SL3F2 := by
  let r : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two hF
  let m : SL3F2 →* Matrix.SpecialLinearGroup (Fin 3) F :=
    Matrix.SpecialLinearGroup.map (r : ZMod 2 →+* F)
  have hbij : Function.Bijective m := by
    constructor
    · intro A B h
      ext i j
      have := congrArg
        (fun M : Matrix.SpecialLinearGroup (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) i j) h
      simpa [m] using r.injective this
    · intro B
      refine ⟨Matrix.SpecialLinearGroup.map (r.symm : F →+* ZMod 2) B, ?_⟩
      ext i j
      simp [m]
  exact (specialLinearGroupEquivStatedSL 3 F).symm.trans (MulEquiv.ofBijective m hbij).symm

end Equiv

section Quot

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem exists_quotEquiv (hcover : AsA36NoOddCover) (c : P4Ctx T Mc M H B₀ I X)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (e : Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) :
    Nonempty (OTwoQuot X ≃* SL3F2) := by
  have hF' : Fintype.card F = 2 ^ 1 := by rw [hF]; norm_num
  have hXN := le_normalizer_V X M I
  have hker := pCoreOf_le_centralizer c
  have hsq : SQTKGroup (↥X ⧸ CFSG.pCore 2 ↥X) :=
    S153D.sqtkGroup_quot_pCore (IsSQTKIn.mono c.hyp.sqtk c.X_le_I)
  have hH : IsL345Type ↥(autOn X (P4V M I X)) :=
    Or.inl ⟨1, F, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hF'], e⟩
  obtain ⟨φ⟩ := S153D.nonempty_quot_mulEquiv_autOn hcover hXN c.quasi hsq hker
    (not_le_centralizer_V e) hH
  obtain ⟨e'⟩ := e
  exact ⟨((QuotientGroup.quotientMulEquivOfEq
    (CFSG.pCore_eq_open ↥X 2).symm).trans φ).trans (e'.trans (statedSL_equiv_SL3F2 hF))⟩

end Quot

section MaxParabolic

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem isMaxParabolic2_inf_M (hcover : AsA36NoOddCover) (c : P4Ctx T Mc M H B₀ I X)
    (ψ : OTwoQuot X ≃* SL3F2) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (e : Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)))
    (hpar : IsMaxParabolic2 (autOn X (P4V M I X)) (autOn (M ⊓ I ⊓ X) (P4V M I X))) :
    IsMaxParabolic2 X (X ⊓ M) := by
  have hF' : Fintype.card F = 2 ^ 1 := by rw [hF]; norm_num
  have hXV := le_normalizer_V X M I
  have hCV := inf_centralizer_eq_pCoreOf hcover c hF' e
  set f₁ := A4.actionOn (P4V M I X) X hXV with hf₁
  have hker : f₁.ker = (rhoOf ψ).ker := by
    ext x
    rw [MonoidHom.mem_ker, rhoOf_ker, hf₁, A4.actionOn_eq_one_iff hXV x,
      SBc16.mem_pCore_iff_coe X x, ← hCV]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hXI : X ≤ I := c.X_le_I
  have hsub : (M ⊓ I ⊓ X).subgroupOf X = (X ⊓ M).subgroupOf X := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h.1.1⟩, fun h => ⟨⟨h.2, hXI x.2⟩, x.2⟩⟩
  have h1 : autOn X (P4V M I X) = (⊤ : Subgroup ↥X).map f₁ := by
    rw [SBd8.autOn_eq_map_actionOn hXV le_rfl, Subgroup.subgroupOf_self]
  have h2 : autOn (M ⊓ I ⊓ X) (P4V M I X) = ((X ⊓ M).subgroupOf X).map f₁ := by
    rw [SBd8.autOn_eq_map_actionOn hXV inf_le_right, hsub]
  rw [h1, h2] at hpar
  have hρ := rhoOf_surjective ψ
  have hk := rhoOf_ker_isPGroup ψ
  have h3 := (A38c5.isMaxParabolic2_map_iff_of_ker_eq f₁ (rhoOf ψ) hker ⊤
    ((X ⊓ M).subgroupOf X)).mp hpar
  rw [Subgroup.map_top_of_surjective _ hρ] at h3
  have hA : IsSylowTwoOf (sOf152 T Mc M B₀ ⊓ X) X :=
    S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp c.comp) c.sylow
  have hO2 : pCoreOf 2 X ≤ X ⊓ M :=
    (pCoreOf_le_of_isSylowTwoOf hA).trans (le_inf (inf_le_right) (inf_le_left.trans
      (S_le_T152.trans (T_le_M152 c.setting))))
  have hkP : (rhoOf ψ).ker ≤ (X ⊓ M).subgroupOf X := by
    rw [rhoOf_ker]
    intro x hx
    exact hO2 ((SBc16.mem_pCore_iff_coe X x).mp hx)
  have h4 := isMaxParabolic2_of_map_of_ker_le (rhoOf ψ) hρ hk hkP h3
  have h5 := A312.isMaxParabolic2_top_map X ((X ⊓ M).subgroupOf X) h4
  rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h5

end MaxParabolic

end CFSG.Quasithin.S15223P4.D1
