module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly E6QTwo

theorem ggQ2s08r6_markingData (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = 5 ∧ GGLabQTwo 3 labL) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (θ : (↥L ⧸ Subgroup.center ↥L) ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
      Nat.card K = 4 ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  obtain ⟨tag, rank, nn⟩ := labL
  obtain ⟨htag, hrank, hq⟩ := hLab
  dsimp only at htag hrank hq
  subst htag hrank
  obtain ⟨lab', hlab', hhas', -, -, -, -, -, hP⟩ := largeEvenMarking_exists_hasLabel hMark
  have hEq : lab' = ⟨.twA, 5, nn⟩ := hP
  subst hEq
  have hn : nn = 1 := by
    have h1 : 1 ≤ nn := hlab'.1
    have h2 : nn < 2 := hq
    omega
  subst hn
  have hmark := ggInnerDiagOn_relabel hRig hS.1.2.2.1.1 hlab' hhas'
  obtain ⟨-, lab'', -, hraw⟩ := hmark
  obtain ⟨R₀, iR₀, I₀, F₀, -, -, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hEq' : lab'' = ⟨.twA, 5, 1⟩ := hP₀.1
  rw [hEq'] at hraw
  obtain ⟨Fld, hFld, hFldfin, hFldcard, hQ⟩ :=
    HdRo7SU.hdRo7SULCoordAux_twA_rawLegacy_one (lab := ⟨.twA, 5, 1⟩) rfl rfl hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  exact ⟨Fld, hFld, hFldfin, θ, hFldcard, hP.2.1, hP.2.2⟩

theorem ggQ2s08r6_exists_data
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA) (hΛ : Fintype.card M.Λ = 5)
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = 5 ∧ GGLabQTwo 3 labL) :
    Nonempty (GGQ2S08RoSix Bs L x) := by
  obtain ⟨K, hKf, hKfin, θ, hK, hNL, hI⟩ := ggQ2s08r6_markingData hRig hS hMark hLab
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hSS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hH : HdRo7SU.GGHdRo7SULCoordHyp 3 B Bs x L D J :=
    ⟨hS.1.1, hS.1.2.1, hS.1.2.2.1, hS.1.2.2.2.1⟩
  have hBL := HdRo7SU.hdRo7SULCoordAux_centralizerCfg hH rfl
  have hperf : commutator ↥L = ⊤ := hMark.1
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hx : x ∈ Bs := hcfg.2.1.1 hSS.2.1
  have hcard : Nat.card Bs = 3 ^ 6 := by
    have h1 : Nat.card Bs = Nat.card M.V :=
      Nat.card_congr ((Additive.ofMul : ↥Bs ≃ Additive ↥Bs).trans M.model.toEquiv)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : Finite M.V := Finite.of_equiv _ M.model.toEquiv
    haveI : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
    rw [h1, Module.natCard_eq_pow_finrank (K := ZMod 3) (V := M.V), Nat.card_zmod,
      hShape.2.2.2.1, hΛ]
  have hK' : Nat.card K = 4 := hK
  obtain ⟨-, hrange5, Q, hQ, hfull⟩ :=
    e6QTwoSixFrameFullDiagonal hK θ hperf hBs hcard hx hBL hNL hI
  exact ⟨{
    K := K
    instField := hKf
    instFinite := hKfin
    hK := hK
    θ := θ
    Q := Q
    hQ := hQ
    hperf := hperf
    hBs := hBs
    hcard := hcard
    hx := hx
    hxL := hShape.1
    hx1 := hSS.2.2.1
    hBL := hBL
    hstar := hcfg.2.1.2.2.2
    hNL := hNL
    hI := hI
    hLx := hSS.2.2.2.1.1
    hLsn := hSS.2.2.2.1.2.1
    hfull := hfull
    hrange5 := hrange5 }⟩

end CFSG.StandardType

end
