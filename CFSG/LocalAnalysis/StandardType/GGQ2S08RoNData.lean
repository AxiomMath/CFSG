module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNFullDiagonal
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModelA
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModelB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly E6QTwo

theorem ggQ2s08rN_markingData (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = n ∧ GGLabQTwo 3 labL) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (θ : (↥L ⧸ Subgroup.center ↥L) ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))),
      Nat.card K = 4 ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))) (LargeEvenGUSet
            (Fin (n + 1)) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  obtain ⟨tag, rank, nn⟩ := labL
  obtain ⟨htag, hrank, hq⟩ := hLab
  dsimp only at htag hrank hq
  subst htag hrank
  obtain ⟨lab', hlab', hhas', -, -, -, -, -, hP⟩ := largeEvenMarking_exists_hasLabel hMark
  have hEq : lab' = ⟨.twA, rank, nn⟩ := hP
  subst hEq
  have hn : nn = 1 := by
    have h1 : 1 ≤ nn := hlab'.1
    have h2 : nn < 2 := hq
    omega
  subst hn
  have hmark := ggInnerDiagOn_relabel hRig hS.1.2.2.1.1 hlab' hhas'
  obtain ⟨-, lab'', -, hraw⟩ := hmark
  obtain ⟨R₀, iR₀, I₀, F₀, -, -, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hEq' : lab'' = ⟨.twA, rank, 1⟩ := hP₀.1
  rw [hEq'] at hraw
  obtain ⟨Fld, hFld, hFldfin, hFldcard, hQ⟩ :=
    HdRo7SU.hdRo7SULCoordAux_twA_rawLegacy_one (lab := ⟨.twA, rank, 1⟩) rfl rfl hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  exact ⟨Fld, hFld, hFldfin, θ, hFldcard, hP.2.1, hP.2.2⟩

theorem ggQ2s08rN_exists_data_of_card
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 6 ≤ n)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)) ∨
      ((Odd n ∨ Odd (Nat.card (Subgroup.center ↥L))) ∧ ¬ 3 ∣ n))
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = n ∧ GGLabQTwo 3 labL)
    (hcard : Nat.card Bs = 3 ^ (n + 1)) :
    Nonempty (GGQ2S08RoN n Bs L x) := by
  obtain ⟨K, hKf, hKfin, θ, hK, hNL, hI⟩ := ggQ2s08rN_markingData hRig hS hMark hLab
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hSS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hH : HdRo7SU.GGHdRo7SULCoordHyp 3 B Bs x L D J :=
    ⟨hS.1.1, hS.1.2.1, hS.1.2.2.1, hS.1.2.2.2.1⟩
  have hBL := HdRo7SU.hdRo7SULCoordAux_centralizerCfg hH rfl
  have hperf : commutator ↥L = ⊤ := hMark.1
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hx : x ∈ Bs := hcfg.2.1.1 hSS.2.1
  obtain ⟨-, hrange, Q, hQ, hfull⟩ :=
    e6QTwoNFrameFullDiagonal hK (by omega) θ hperf hBs hcard hx hBL hNL hI
  exact ⟨{
    K := K
    instField := hKf
    instFinite := hKfin
    hK := hK
    hn := by omega
    θ := θ
    Q := Q
    hQ := hQ
    hperf := hperf
    hBs := hBs
    hcard := hcard
    hx := hx
    hx1 := hSS.2.2.1
    hBL := hBL
    hstar := hcfg.2.1.2.2.2
    hNL := hNL
    hI := hI
    hLx := hSS.2.2.2.1.1
    hLsn := hSS.2.2.2.1.2.1
    hZcop := hZ
    hfull := hfull
    hrange := hrange }⟩

theorem ggQ2s08rN_exists_data_of_center
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 6 ≤ n)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)) ∨
      ((Odd n ∨ Odd (Nat.card (Subgroup.center ↥L))) ∧ ¬ 3 ∣ n))
    (M : GGQ2LDatum 3 Bs L x)
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = n ∧ GGLabQTwo 3 labL)
    (f : Fin (n + 1) → M.V) (hFrame : GGQ2S08ROFrame M f) :
    Nonempty (GGQ2S08RoN n Bs L x) := by
  refine ggQ2s08rN_exists_data_of_card hRig hn hS hZ hMark hLab ?_
  have h1 : Nat.card Bs = Nat.card M.V :=
    Nat.card_congr ((Additive.ofMul : ↥Bs ≃ Additive ↥Bs).trans M.model.toEquiv)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite M.V := Finite.of_equiv _ M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have hb : Module.Basis (Fin (n + 1)) (ZMod 3) M.V :=
    Module.Basis.mk hFrame.1 (le_of_eq hFrame.2.1.symm)
  have hdim : Module.finrank (ZMod 3) M.V = n + 1 := by
    rw [Module.finrank_eq_card_basis hb, Fintype.card_fin]
  rw [h1, Module.natCard_eq_pow_finrank (K := ZMod 3) (V := M.V), Nat.card_zmod, hdim]

theorem ggQ2s08rN_exists_data
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {n : ℕ}
    (hn : 6 ≤ n) (h3 : ¬ 3 ∣ n + 1)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (M : GGQ2LDatum 3 Bs L x)
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = n ∧ GGLabQTwo 3 labL)
    (f : Fin (n + 1) → M.V) (hFrame : GGQ2S08ROFrame M f) :
    Nonempty (GGQ2S08RoN n Bs L x) := by
  have hH : HdRo7SU.GGHdRo7SULCoordHyp 3 B Bs x L D J :=
    ⟨hS.1.1, hS.1.2.1, hS.1.2.2.1, hS.1.2.2.2.1⟩
  have hrow : HdRo7SU.GGHdRo7SULabL 3 L := by
    obtain ⟨lab', hlab', hhas', -, -, -, -, -, hP⟩ := largeEvenMarking_exists_hasLabel hMark
    subst lab'
    have hn1 : labL.n = 1 := by
      have h1 : 1 ≤ labL.n := hlab'.1
      have h2 : labL.n < 2 := hLab.2.2
      omega
    exact ⟨labL, hlab', hhas', rfl, hLab.1, hn1, by rw [hLab.2.1]; exact hn,
      by rw [hLab.2.1]; exact h3⟩
  exact ggQ2s08rN_exists_data_of_center hRig hn hS
    (Or.inl (HdRo7SU.hdRo7SULCoordAux_centerCoprimeCfg hH hRig hrow)) M hMark hLab f hFrame

theorem ggQ2s08rN_exists_data_of_odd
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 6 ≤ n) (hodd : Odd n) (h3n : ¬ 3 ∣ n)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (M : GGQ2LDatum 3 Bs L x)
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = n ∧ GGLabQTwo 3 labL)
    (f : Fin (n + 1) → M.V) (hFrame : GGQ2S08ROFrame M f) :
    Nonempty (GGQ2S08RoN n Bs L x) :=
  ggQ2s08rN_exists_data_of_center hRig hn hS (Or.inr ⟨Or.inl hodd, h3n⟩) M hMark hLab f hFrame

end CFSG.StandardType

end
