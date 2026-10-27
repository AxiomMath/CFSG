module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeBigCell
public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeHeartDatum
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeNineLin
import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXOffI1Holds
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumInner
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
import CFSG.LocalAnalysis.StandardType.GGQ2P3Hyp
import CFSG.LocalAnalysis.StandardType.GGQ2PmWHeartA
import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXDetCell

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_gammaAt_of_gammaX {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hΓ : GGQ2GammaX p B Bs x L D J) {u : ↥Bs}
    (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers x) : GGGammaAt p B Bs x L D J u := by
  intro φ hφ hφu
  rw [mem_ggAutomizer_iff] at hφ ⊢
  obtain ⟨g, -, hgN, hg⟩ := hφ
  refine ⟨g, hΓ g hgN ?_, hgN, hg⟩
  have hx : x ∈ Subgroup.zpowers (u : G) := by
    rw [hu]
    exact Subgroup.mem_zpowers x
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hφu
  have hgu : g * (u : G) * g⁻¹ = (u : G) ^ k := by
    rw [← hg u, ← hk, Subgroup.coe_zpow]
  rw [← hu, ← hm, ← conj_zpow, hgu, ← zpow_mul]
  exact Subgroup.zpow_mem_zpowers _ _

theorem ggQ2_tn9_orbitStable (hK : GGReflClassOmegaInput) {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {u : G} (hNT : GGNoTransvection 3 Bs) (M : GGQ2LDatum 3 Bs X u)
    (e : Fin 8 ≃ M.Λ) (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A 8 i j) (hB : M.ShapeB)
    (hnorm : ∀ φ ∈ ggAutomizer ⊤ Bs, φ ⟨u, M.hx⟩ ∈ Subgroup.zpowers (⟨u, M.hx⟩ : ↥Bs) →
      φ ∈ Subgroup.normalizer (ggAutomizer X Bs : Set (MulAut ↥Bs))) :
    GGOrbitStableAt 3 Bs ⟨u, M.hx⟩ := by
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  let A : Subgroup (M.V ≃ₗ[ZMod 3] M.V) := (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)
  let c : Fin 8 → M.V := fun i => M.coroot (e i)
  let α : Fin 8 → Module.Dual (ZMod 3) M.V := fun i => M.root (e i)
  let s : Fin 8 → (M.V ≃ₗ[ZMod 3] M.V) := fun i => ggLin (p := 3) M.model (M.simple (e i))
  have hHdim : Module.finrank (ZMod 3) M.coSpan + 1 = Fintype.card M.Λ := hB.2.1
  have hxHcoSpan : M.xV ∉ M.coSpan := hB.2.2.1
  have hsup : M.coSpan ⊔ Submodule.span (ZMod 3) {M.xV} = ⊤ := hB.2.2.2
  have hcoSpan : M.coSpan = Submodule.span (ZMod 3) (Set.range c) := by
    rw [GGQ2LDatum.coSpan]
    congr 1
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, by
        change M.coroot (e (e.symm j)) = M.coroot j
        rw [Equiv.apply_symm_apply]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e k, rfl⟩
  have hxH : M.xV ∉ Submodule.span (ZMod 3) (Set.range c) := by
    rw [← hcoSpan]
    exact hxHcoSpan
  have hxV0 : M.xV ≠ 0 := by
    intro h
    exact hxHcoSpan (by rw [h]; exact M.coSpan.zero_mem)
  have hinf : M.coSpan ⊓ Submodule.span (ZMod 3) {M.xV} = ⊥ :=
    disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem hxHcoSpan)
  have hcardΛ : Fintype.card M.Λ = 8 := by
    simpa using Fintype.card_congr e.symm
  have hdim : Module.finrank (ZMod 3) M.V = 8 := by
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 3) M.coSpan
      (Submodule.span (ZMod 3) {M.xV})
    rw [hsup, hinf, finrank_top, finrank_bot, finrank_span_singleton hxV0] at hfr
    omega
  have hpair : ∀ i j : Fin 8, α i (c j) = (CartanMatrix.A 8 i j : ZMod 3) := by
    intro i j
    rw [M.pairing (e i) (e j), hC i j]
  have hs : ∀ i : Fin 8, ∀ v, s i v = v - α i v • c i := fun i => M.simple_apply (e i)
  have hsA : ∀ i : Fin 8, s i ∈ A := fun i =>
    Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) (GGQ2LDatum.simple_mem_top M (e i))
  have hxfix : ∀ i : Fin 8, α i M.xV = 0 := fun i => GGQ2LDatum.root_xV M (e i)
  have hTF : TransvectionFree A := ggQ2P3P_transvectionFree M.model hNT
  have hStab : ∀ g ∈ A, g M.xV = M.xV → ∃ w ∈ Subgroup.closure (Set.range s),
      ∃ ε : ZMod 3, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c), g h = ε • w h :=
    ggQ2_heartA_stab M (by norm_num) e hC hB hnorm
  have hpm := ggQ2TN9_pm (V := M.V) hK A hTF hdim c α hpair s hs hsA M.xV hxH hxfix hStab
  have hrefl : reflGp A = (ggReflGp 3 Bs).map (ggLin (p := 3) M.model) :=
    ggQ2P3P_reflGp_map M.model (by decide)
  have hlin : ∀ ψ : MulAut ↥Bs, ggLin (p := 3) M.model ψ M.xV =
      M.model (Additive.ofMul (ψ ⟨u, M.hx⟩)) := fun ψ =>
    ggLin_apply_ofMul (p := 3) M.model ψ _
  have hε3 : ∀ ε : ZMod 3, ε ≠ 0 → ε = 1 ∨ ε = -1 := by decide
  intro φ hφ
  obtain ⟨rV, hrV, ε, hε, hεr⟩ := hpm _ (Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) hφ)
  rw [hrefl] at hrV
  obtain ⟨ρ', hρ', hρ'eq⟩ := Subgroup.mem_map.mp hrV
  refine ⟨ρ', hρ', ?_⟩
  rcases hε3 ε hε with rfl | rfl
  · have hOf : Additive.ofMul (φ ⟨u, M.hx⟩) = Additive.ofMul (ρ' ⟨u, M.hx⟩) := by
      apply M.model.injective
      rw [← hlin φ, ← hlin ρ', hρ'eq, hεr, one_smul]
    rw [Additive.ofMul.injective hOf]
  · have hOf : Additive.ofMul (φ ⟨u, M.hx⟩) = Additive.ofMul (ρ' ⟨u, M.hx⟩)⁻¹ := by
      apply M.model.injective
      rw [← hlin φ, ofMul_inv, map_neg, ← hlin ρ', hρ'eq, hεr, neg_one_smul]
    rw [Additive.ofMul.injective hOf, Subgroup.zpowers_inv]

theorem ggQ2_centralizer_le_normalizer_ggG0 (hNC : GGLNoncyclicInput) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) :
    Subgroup.centralizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  obtain ⟨hI, hBs, hDJsub⟩ := hS.1.1
  have hSst : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  exact (Subgroup.centralizer_le hBs.1).trans
    (centralizer_le_normalizer_ggG0 hSst (hNC G 3 B x L hI) hDJsub.1)

theorem ggQ2_tn9_holds_of_gammaNbr (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) (M : GGQ2LDatum 3 Bs L x)
    (e : Fin 8 ≃ M.Λ) (hCM : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A 8 i j) (hB : M.ShapeB)
    (hCav : 4 ∣ Nat.card (ggAutomizer J Bs))
    (hΓ : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K → ∀ u : ↥Bs,
      Subgroup.zpowers (u : G) = Subgroup.zpowers y → GGGammaAt 3 B Bs x L D J u) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hS.1 hI1
  have hΓx : GGQ2GammaX 3 B Bs x L D J :=
    ggQ2_gammaX_of_heartA hLB hP hS hCav M e hCM (by norm_num) hB
  refine ggQ2_reduction hS (ggQ2_centralizer_le_normalizer_ggG0 hNC hS) ?_ ?_
  · intro u hu hu1
    by_cases hx : Subgroup.zpowers (u : G) = Subgroup.zpowers x
    · exact ggQ2_gammaAt_of_gammaX hΓx hx
    by_cases hn : GGNbrLine 3 B x D J u
    · obtain ⟨y, K, hnb, hyu⟩ := hn
      exact hΓ y K hnb u hyu.symm
    · exact ggQ2_gammaTrivial hLB hP hS rfl hK1 hI1 hu hu1 ⟨hx, hn⟩ hCav
  · refine ⟨⟨x, M.hx⟩, hS.1.1.2.2.1.2.2.2.1, ?_, ?_⟩
    · intro h
      apply hB.1
      rw [show x = 1 from congrArg Subtype.val h]
      exact L.one_mem
    · exact ggQ2_tn9_orbitStable hK hS.1.2.2.2.1 M e hCM hB
        (fun ψ hψA hψx => ggQ2_lineStab_normalizes_L hLB hP hS.1 (ggQ2_ajOfSetting hP h5 hS)
          M.hx hψA hψx)

theorem ggQ2_tn9_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J)
    (hsel : GGQ2TN9Sel p B Bs x L D J) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  subst hp
  obtain ⟨⟨M, e, hCM, hB⟩, hCav, hnbr⟩ := hsel
  refine ggQ2_tn9_holds_of_gammaNbr hLB hP hNC h5 hK hS hI1 M e hCM hB hCav ?_
  intro y K hnb u hu
  obtain ⟨N, hdet, n, C₀, e', hC', hW⟩ := hnbr y K hnb
  exact ggQ2_gammaNbr_of_innerDatum hLB hP h5 hS rfl hI1 hnb N hdet C₀ e' hC' hW hu

theorem ggQ2_gammaNbr_of_heartDatum (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr 3 B x D J y K) (N : GGQ2NbrDatum 3 Bs K) {r : ℕ} (hr : 4 ≤ r)
    (e : Fin r ≃ N.Λ) (hC : ∀ i j, N.cartan (e i) (e j) = CartanMatrix.A r i j)
    (hdim : Module.finrank (ZMod 3) N.V = r)
    (hdep : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range N.coroot)) + 1 = r)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers y) :
    GGGammaAt 3 B Bs x L D J u :=
  ggQ2_gammaNbr_of_datumPM hLB hP h5 hS rfl hI1 hnb N
    (fun u₀ hu₀ hfix _ _ _ T hT => N.toWDatum.pmW_of_heartA hr e hC hdim hdep u₀ hu₀ hfix T hT) hu

theorem ggQ2_tn9K_holds_of_gamma (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (MK : GGQ2LDatum 3 Bs K y) (eK : Fin 8 ≃ MK.Λ)
    (hCK : ∀ i j, MK.cartan (eK i) (eK j) = CartanMatrix.A 8 i j) (hBK : MK.ShapeB)
    (hCav : 4 ∣ Nat.card (ggAutomizer J Bs)) (hΓx : GGQ2GammaX 3 B Bs x L D J)
    (hΓ : ∀ (y' : G) (K' : Subgroup G), GGNbr 3 B x D J y' K' → ∀ u : ↥Bs,
      Subgroup.zpowers (u : G) = Subgroup.zpowers y' → GGGammaAt 3 B Bs x L D J u) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hS.1 hI1
  refine ggQ2_reduction hS (ggQ2_centralizer_le_normalizer_ggG0 hNC hS) ?_ ?_
  · intro u hu hu1
    by_cases hx : Subgroup.zpowers (u : G) = Subgroup.zpowers x
    · exact ggQ2_gammaAt_of_gammaX hΓx hx
    by_cases hn : GGNbrLine 3 B x D J u
    · obtain ⟨y', K', hnb', hyu⟩ := hn
      exact hΓ y' K' hnb' u hyu.symm
    · exact ggQ2_gammaTrivial hLB hP hS rfl hK1 hI1 hu hu1 ⟨hx, hn⟩ hCav
  · refine ⟨⟨y, MK.hx⟩, ?_, ?_, ?_⟩
    · rw [hnb.2.1]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))
    · intro h
      apply hBK.1
      rw [show y = 1 from congrArg Subtype.val h]
      exact K.one_mem
    · exact ggQ2_tn9_orbitStable hK hS.1.2.2.2.1 MK eK hCK hBK
        (fun ψ hψA hψy => ggQ2_nbrLineStab_normalizes hLB hP hS.1 (ggQ2_ajOfSetting hP h5 hS)
          hK1 hnb MK.hx hψA hψy)

theorem ggQ2_tn9K_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : p = 3) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hsel : GGQ2TN9SelK p B Bs x L D J y K) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  subst hp
  obtain ⟨⟨MK, eK, hCK, hBK⟩, ⟨NK, eN, hCN, hdimN, hdepN⟩,
    ⟨ML, hcardL, hdetL, nL, CL, eL, hCL, hWL⟩, hCav, hnbr⟩ := hsel
  refine ggQ2_tn9K_holds_of_gamma hLB hP hNC h5 hK hS hI1 hnb MK eK hCK hBK hCav
    (ggQ2xd_gammaX_of_datumPM hLB hP hS rfl hCav ML (fun u₀ _ hfix _ _ _ T hT =>
      GGQ2WDatum.pmW_of_det ML.toWDatum u₀ hfix hcardL hdetL CL eL hCL hWL T hT)) ?_
  intro y' K' hnb' u hu
  by_cases hyy : Subgroup.zpowers y' = Subgroup.zpowers y
  · exact ggQ2_gammaNbr_of_heartDatum hLB hP h5 hS hI1 hnb NK (by norm_num) eN hCN hdimN hdepN
      (hu.trans hyy)
  obtain ⟨N, hdet, n, C₀, e', hC', hW⟩ := hnbr y' K' hnb' hyy
  exact ggQ2_gammaNbr_of_innerDatum hLB hP h5 hS rfl hI1 hnb' N hdet C₀ e' hC' hW hu

theorem ggQ2TwoNode_of_rest
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput)
    (hdLab : GGCoxeterLabelInput) (hWA : GGTBFixNbrXInput) (hTBF : GGTBFixInput)
    (hRGq : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
      {L D J : Subgroup G} {y : G} {K : Subgroup G}, GGQTwoSetting p B Bs x L D J →
        GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs))
    (hr : GGQ2TwoNodeRestInput) : GGQ2TwoNodeInput := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 y K hnb hrow
  by_cases hbig : (GGQ2S08PosTwABig p L J ∧ x ∉ L) ∨ (GGQ2S08PosTwABig p K J ∧ y ∉ K) ∨
      (GGQ2S08PosABig p K J ∧ y ∉ K)
  · rcases hbig with h | h | ⟨h, hy⟩
    · exact (ggQ2s08_noNbrBig_holds hRig hLB hP h5 hK hdLab hWA hTBF hRGq hp hS hI1 hnb
        (Or.inl h)).elim
    · exact (ggQ2s08_noNbrBig_holds hRig hLB hP h5 hK hdLab hWA hTBF hRGq hp hS hI1 hnb
        (Or.inr h)).elim
    · exact (ggQ2s08_noNbrABigK_holds hRig hLB hP h5 hK hdLab hTBF hRGq hp hS hI1 hnb h hy).elim
  by_cases h9 : GGQ2TN9Sel p B Bs x L D J
  · exact ggQ2_tn9_holds hLB hP hNC h5 hK hp hS hI1 h9
  by_cases h9K : GGQ2TN9SelK p B Bs x L D J y K
  · exact ggQ2_tn9K_holds hLB hP hNC h5 hK hp hS hI1 hnb h9K
  exact hr hp hS hI1 hnb hrow hbig
    (fun h => ggQ2_tnBig_false hLB hP h5 hK hdLab hWA hp hS hnb (hRGq hS hnb) h)
    (fun h => ggQ2_tnBigK_false hLB hP h5 hK hdLab hTBF hp hS hI1 hnb (hRGq hS hnb) h) h9 h9K

end CFSG.StandardType

end
