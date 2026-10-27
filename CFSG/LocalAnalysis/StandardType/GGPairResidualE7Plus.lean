module

public import CFSG.LocalAnalysis.StandardType.GGExcPlusPairConj
public import CFSG.LocalAnalysis.StandardType.GGResidualExcRows
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1ExcTops
public import CFSG.LocalAnalysis.StandardType.GGResidualGenFrame
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.ExcPay.Defs
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13604
public import Certificates.Certificate13605
public import Certificates.Certificate13691
public import Certificates.Certificate13720
public import Certificates.Certificate13721
public import Certificates.Certificate13722
public import Certificates.Certificate13723
public import Certificates.Certificate13724
import CFSG.LocalAnalysis.StandardType.ExcPay.E7
import CFSG.LocalAnalysis.StandardType.ExcPay.RouteE7Three
import CFSG.LocalAnalysis.StandardType.ExcPay.CoverE7
import CFSG.LocalAnalysis.StandardType.GGPairConjugation
import CFSG.LocalAnalysis.StandardType.GGRankOneShared
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlusAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux2
import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.ClassicalInvolution.Phan.StandardPairNotComm
import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.Phan

theorem ggAutomizer_commute_of_rankOneIn_commute {G : Type} [Group G] [Finite G]
    {X Bs : Subgroup G} {r r' : MulAut ↥Bs} (hr : r ∈ ggAutomizer X Bs) (hr2 : r ^ 2 = 1)
    (hr' : r' ∈ ggAutomizer X Bs) (hr'2 : r' ^ 2 = 1)
    (h : ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs r', a * b = b * a) :
    r * r' = r' * r := by
  obtain ⟨g, hgK, -, hg⟩ := mem_ggAutomizer_iff.mp (mem_ggAutomizer_ggRankOneIn hr hr2)
  obtain ⟨g', hg'K, -, hg'⟩ := mem_ggAutomizer_iff.mp (mem_ggAutomizer_ggRankOneIn hr' hr'2)
  have hgg : g * g' = g' * g := h g hgK g' hg'K
  have key : ∀ x : G, g * (g' * x * g'⁻¹) * g⁻¹ = g' * (g * x * g⁻¹) * g'⁻¹ := by
    intro x
    calc g * (g' * x * g'⁻¹) * g⁻¹
        = (g * g') * x * (g * g')⁻¹ := by group
      _ = (g' * g) * x * (g' * g)⁻¹ := by rw [hgg]
      _ = g' * (g * x * g⁻¹) * g'⁻¹ := by group
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  simp only [MulAut.mul_apply, hg, hg']
  exact key (b : G)

theorem ggAutomizer_eq_of_overGamma {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    {hN : Bs ≤ Subgroup.normalizer (X : Set G)}
    (hZ : ∀ z ∈ Subgroup.center ↥X, (z : G) ∈ Bs → z = 1)
    {c c' : MulAut ↥Bs} (hc : c ∈ ggAutomizer X Bs) (hc' : c' ∈ ggAutomizer X Bs)
    {a : MulAut ↥(ggGamma X hN).range} (h : GGOverGamma hN c a) (h' : GGOverGamma hN c' a) :
    c = c' := by
  let d : MulAut ↥Bs := c⁻¹ * c'
  have hd_mem : d ∈ ggAutomizer X Bs :=
    (ggAutomizer X Bs).mul_mem ((ggAutomizer X Bs).inv_mem hc) hc'
  have hd : GGOverGamma hN d (1 : MulAut ↥(ggGamma X hN).range) := by
    have hh : GGOverGamma hN (c⁻¹ * c') (a⁻¹ * a) := h.inv.mul h'
    simpa [d] using hh
  have hd_one : d = 1 := by
    obtain ⟨g, hgX, hgN, hg⟩ := mem_ggAutomizer_iff.mp hd_mem
    have hdb_eq : ∀ b : ↥Bs, d b = b := by
      intro b
      apply Subtype.ext
      let z : G := (b : G)⁻¹ * ((d b : ↥Bs) : G)
      have hzX : z ∈ X := by
        have hbN : (b : G) ∈ Subgroup.normalizer (X : Set G) := hN b.2
        have hbCin : (b : G)⁻¹ * g * (b : G) ∈ X := by
          have hmap : X.map (MulAut.conj (b : G)⁻¹).toMonoidHom = X :=
            Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hbN)
          have hmem : MulAut.conj (b : G)⁻¹ g ∈
              X.map (MulAut.conj (b : G)⁻¹).toMonoidHom :=
            Subgroup.mem_map_of_mem (MulAut.conj (b : G)⁻¹).toMonoidHom hgX
          rw [hmap] at hmem
          simpa [MulAut.conj_apply] using hmem
        have hdb : ((d b : ↥Bs) : G) = g * (b : G) * g⁻¹ := hg b
        change (b : G)⁻¹ * ((d b : ↥Bs) : G) ∈ X
        rw [hdb]
        have hsplit : (b : G)⁻¹ * (g * (b : G) * g⁻¹) =
            ((b : G)⁻¹ * g * (b : G)) * g⁻¹ := by group
        rw [hsplit]
        exact X.mul_mem hbCin (X.inv_mem hgX)
      have hgamma : ggGamma X hN (d b) = ggGamma X hN b := by
        have hv := hd b
        simp only [MulAut.one_apply] at hv
        simpa only [MonoidHom.coe_rangeRestrict] using Subtype.ext_iff.mp hv
      have hz_center : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
        rw [Subgroup.mem_center_iff]
        intro l
        apply Subtype.ext
        show (l : G) * z = z * (l : G)
        have h2 : ((d b : ↥Bs) : G) * (l : G) * (((d b : ↥Bs) : G))⁻¹ =
            (b : G) * (l : G) * (b : G)⁻¹ := by
          have hl := congrArg (fun φ : MulAut ↥X => (φ l : G)) hgamma
          simpa [ggGamma_coe] using hl
        have hzconj : z * (l : G) * z⁻¹ = (l : G) := by
          dsimp only [z]
          calc ((b : G)⁻¹ * ((d b : ↥Bs) : G)) * (l : G) *
                ((b : G)⁻¹ * ((d b : ↥Bs) : G))⁻¹
              = (b : G)⁻¹ * (((d b : ↥Bs) : G) * (l : G) *
                  (((d b : ↥Bs) : G))⁻¹) * (b : G) := by group
            _ = (b : G)⁻¹ * ((b : G) * (l : G) * (b : G)⁻¹) * (b : G) := by rw [h2]
            _ = (l : G) := by group
        have hcomm_z : z * (l : G) = (l : G) * z := by
          calc z * (l : G) = z * (l : G) * z⁻¹ * z := by group
            _ = (l : G) * z := by rw [hzconj]
        exact hcomm_z.symm
      have hz_eq_one : (⟨z, hzX⟩ : ↥X) = 1 :=
        hZ _ hz_center (Bs.mul_mem (Bs.inv_mem b.2) (d b).2)
      have hzG : z = 1 := by
        have := congrArg Subtype.val hz_eq_one
        simpa using this
      have hzG' : (b : G)⁻¹ * ((d b : ↥Bs) : G) = 1 := by simpa [z] using hzG
      exact (inv_mul_eq_one.mp hzG').symm
    exact MulEquiv.ext fun b => by rw [hdb_eq b, MulAut.one_apply]
  exact inv_mul_eq_one.mp (by simpa [d] using hd_one)

theorem GGPairConcl.of_excPlusModel
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {G : Type}
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hM : GGExcPlusWeylModel τ p (ggGamma X hN).range)
    (hZ : ∀ z ∈ Subgroup.center ↥X, (z : G) ∈ Bs → z = 1)
    {s s' r r' : MulAut ↥Bs} (hs : s ∈ ggAutomizer X Bs) (hsR : GGIsReflection p s)
    (hs' : s' ∈ ggAutomizer X Bs) (hs'R : GGIsReflection p s')
    (hr : r ∈ ggAutomizer X Bs) (hrR : GGIsReflection p r)
    (hr' : r' ∈ ggAutomizer X Bs) (hr'R : GGIsReflection p r')
    (hne : s ≠ s') (hne' : r ≠ r') (hcomm : s * s' = s' * s ↔ r * r' = r' * r)
    (h : GGPairConcl Bs X s s') : GGPairConcl Bs X r r' := by
  let A : Subgroup (MulAut ↥X) := (ggGamma X hN).range
  let 𝒜 : Subgroup (MulAut ↥A) :=
    ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range A
  have hsc : GGTorusSelfCent p A := ggTorusSelfCent_ggGamma hN hSC
  obtain ⟨vs, hvsN, hovs, hrefls, hmems⟩ :=
    ggReflection_overGamma_of_induced hp hp2 hBs hN
      (show s ∈ ggInduced X Bs from mem_ggAutomizer_iff.mp hs) hsR
  obtain ⟨vs', hvs'N, hovs', hrefls', hmems'⟩ :=
    ggReflection_overGamma_of_induced hp hp2 hBs hN
      (show s' ∈ ggInduced X Bs from mem_ggAutomizer_iff.mp hs') hs'R
  obtain ⟨vr, hvrN, hovr, hreflr, hmemr⟩ :=
    ggReflection_overGamma_of_induced hp hp2 hBs hN
      (show r ∈ ggInduced X Bs from mem_ggAutomizer_iff.mp hr) hrR
  obtain ⟨vr', hvr'N, hovr', hreflr', hmemr'⟩ :=
    ggReflection_overGamma_of_induced hp hp2 hBs hN
      (show r' ∈ ggInduced X Bs from mem_ggAutomizer_iff.mp hr') hr'R
  let is : MulAut ↥A := ggConjAut A hvsN
  let is' : MulAut ↥A := ggConjAut A hvs'N
  let ir : MulAut ↥A := ggConjAut A hvrN
  let ir' : MulAut ↥A := ggConjAut A hvr'N
  have hovs_is : GGOverGamma hN s is := hovs
  have hovs'_is : GGOverGamma hN s' is' := hovs'
  have hovr_ir : GGOverGamma hN r ir := hovr
  have hovr'_ir : GGOverGamma hN r' ir' := hovr'
  have hmems_is : is ∈ 𝒜 := hmems
  have hmems'_is : is' ∈ 𝒜 := hmems'
  have hmemr_ir : ir ∈ 𝒜 := hmemr
  have hmemr'_ir : ir' ∈ 𝒜 := hmemr'
  have hrefls_is : GGIsReflection p is := hrefls
  have hrefls'_is : GGIsReflection p is' := hrefls'
  have hreflr_ir : GGIsReflection p ir := hreflr
  have hreflr'_ir : GGIsReflection p ir' := hreflr'
  have comm_iff : ∀ (c c' : MulAut ↥Bs), c ∈ ggAutomizer X Bs → c' ∈ ggAutomizer X Bs →
      ∀ (a a' : MulAut ↥A), GGOverGamma hN c a → GGOverGamma hN c' a' →
      (a * a' = a' * a ↔ c * c' = c' * c) := by
    intro c c' hc hc' a a' ha ha'
    constructor
    · intro h
      exact ggAutomizer_eq_of_overGamma hZ ((ggAutomizer X Bs).mul_mem hc hc')
        ((ggAutomizer X Bs).mul_mem hc' hc) (ha.mul ha') (by rw [h]; exact ha'.mul ha)
    · intro h
      exact GGOverGamma.unique (ha.mul ha') (by rw [h]; exact ha'.mul ha)
  have hcommImg : is * is' = is' * is ↔ ir * ir' = ir' * ir :=
    (comm_iff s s' hs hs' is is' hovs_is hovs'_is).trans
      (hcomm.trans (comm_iff r r' hr hr' ir ir' hovr_ir hovr'_ir).symm)
  have hne_s : is ≠ is' := by
    intro heq
    exact hne (ggAutomizer_eq_of_overGamma hZ hs hs' hovs_is (heq.symm ▸ hovs'_is))
  have hne_r : ir ≠ ir' := by
    intro heq
    exact hne' (ggAutomizer_eq_of_overGamma hZ hr hr' hovr_ir (heq.symm ▸ hovr'_ir))
  obtain ⟨v, hv, hv1, hv2⟩ :=
    ggExcPlusModel_exists_conj_pair hτ hp hp2 hsc hM
      hmems_is hrefls_is hmems'_is hrefls'_is
      hmemr_ir hreflr_ir hmemr'_ir hreflr'_ir hne_s hne_r hcommImg
  have hW : ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range A ≤
      Subgroup.closure (ggTorusReflSet p A) :=
    (ggWTEx1_weylFrame_of_excPlusModel hp hp2 hsc hM).automizer_le_closure
  obtain ⟨c, hcClosure, hcOver⟩ :=
    exists_overGamma_of_weylReflSet hp hp2 hBs hSC hN hW v hv
  have hcAuto : c ∈ ggAutomizer X Bs :=
    (Subgroup.closure_le _).mpr (fun φ hφ => hφ.1) hcClosure
  have hcov_cs : GGOverGamma hN (c * s * c⁻¹) (v * is * v⁻¹) :=
    (hcOver.mul hovs_is).mul hcOver.inv
  have hcov_cs' : GGOverGamma hN (c * s' * c⁻¹) (v * is' * v⁻¹) :=
    (hcOver.mul hovs'_is).mul hcOver.inv
  have hcov_cs_r : GGOverGamma hN (c * s * c⁻¹) ir := by
    rw [hv1]
    exact hcov_cs
  have hcov_cs'_r : GGOverGamma hN (c * s' * c⁻¹) ir' := by
    rw [hv2]
    exact hcov_cs'
  have hcsc_mem : c * s * c⁻¹ ∈ ggAutomizer X Bs :=
    (ggAutomizer X Bs).mul_mem ((ggAutomizer X Bs).mul_mem hcAuto hs)
      ((ggAutomizer X Bs).inv_mem hcAuto)
  have hcs'c_mem : c * s' * c⁻¹ ∈ ggAutomizer X Bs :=
    (ggAutomizer X Bs).mul_mem ((ggAutomizer X Bs).mul_mem hcAuto hs')
      ((ggAutomizer X Bs).inv_mem hcAuto)
  have hcsc_eq : c * s * c⁻¹ = r :=
    ggAutomizer_eq_of_overGamma hZ hcsc_mem hr hcov_cs_r hovr_ir
  have hcs'c_eq : c * s' * c⁻¹ = r' :=
    ggAutomizer_eq_of_overGamma hZ hcs'c_mem hr' hcov_cs'_r hovr'_ir
  have hconj := ggPairConcl_of_automizer_conj hcAuto h
  rwa [hcsc_eq, hcs'c_eq] at hconj

theorem ggPairConcl_of_excPlusModel_base
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {G : Type}
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hM : GGExcPlusWeylModel τ p (ggGamma X hN).range)
    (hZ : ∀ z ∈ Subgroup.center ↥X, (z : G) ∈ Bs → z = 1)
    {n : ℕ} {N : CoxeterMatrix (Fin n)} {i₀ i₁ i₂ i₃ : Fin n} (hM01 : N.M i₀ i₁ = 2)
    (hM02 : N.M i₀ i₂ = 3) (hM12 : N.M i₁ i₂ = 2) (hM03 : N.M i₀ i₃ = 2) (hM23 : N.M i₂ i₃ = 3)
    {s : Fin n → MulAut ↥Bs} (hs : ∀ i, s i ∈ ggAutomizer X Bs ∧ GGIsReflection p (s i))
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (hcomm2 : ∀ i j, i ≠ j → N.M i j = 2 →
      ∀ a ∈ ggRankOneIn X Bs (s i), ∀ b ∈ ggRankOneIn X Bs (s j), a * b = b * a)
    (hpair3 : ∀ i j, N.M i j = 3 → ∃ W : Subgroup G,
      UnitaryBlockStandardPair F 2 f W (ggRankOneIn X Bs (s i)) (ggRankOneIn X Bs (s j)))
    {r r' : MulAut ↥Bs} (hr : r ∈ ggAutomizer X Bs) (hrR : GGIsReflection p r)
    (hr' : r' ∈ ggAutomizer X Bs) (hr'R : GGIsReflection p r') (hne : r ≠ r') :
    GGPairConcl Bs X r r' := by
  have hne_of : ∀ {i j : Fin n}, N.M i j = 2 → i ≠ j := fun h hij => by
    rw [hij, N.diagonal] at h
    exact absurd h (by decide)
  have hs01ne : s i₀ ≠ s i₁ := by
    intro h
    have hR : ggRankOneIn X Bs (s i₀) = ggRankOneIn X Bs (s i₁) := by rw [h]
    obtain ⟨W, hW⟩ := hpair3 i₀ i₂ hM02
    obtain ⟨x, hx, y, hy, hxy⟩ := UnitaryBlockStandardPair.exists_not_commute hW
    have hx' : x ∈ ggRankOneIn X Bs (s i₁) := by rwa [← hR]
    exact hxy (hcomm2 i₁ i₂ (hne_of hM12) hM12 x hx' y hy)
  have hs02ne : s i₀ ≠ s i₂ := by
    intro h
    have hR : ggRankOneIn X Bs (s i₂) = ggRankOneIn X Bs (s i₀) := by rw [h]
    obtain ⟨W, hW⟩ := hpair3 i₂ i₃ hM23
    obtain ⟨x, hx, y, hy, hxy⟩ := UnitaryBlockStandardPair.exists_not_commute hW
    have hx' : x ∈ ggRankOneIn X Bs (s i₀) := by rwa [← hR]
    exact hxy (hcomm2 i₀ i₃ (hne_of hM03) hM03 x hx' y hy)
  have hs01comm : s i₀ * s i₁ = s i₁ * s i₀ := by
    refine ggAutomizer_commute_of_rankOneIn_commute (hs i₀).1 (hs i₀).2.1 (hs i₁).1 (hs i₁).2.1 ?_
    intro a ha b hb
    exact hcomm2 i₀ i₁ (hne_of hM01) hM01 a ha b hb
  have B1 : GGPairConcl Bs X (s i₀) (s i₁) := by
    refine ⟨?_, ?_⟩
    · intro _ a ha b hb
      exact hcomm2 i₀ i₁ (hne_of hM01) hM01 a ha b hb
    · intro hnc
      exact absurd hs01comm hnc
  have hs02nc : s i₀ * s i₂ ≠ s i₂ * s i₀ := by
    intro heq
    have hP : GGPairConcl Bs X (s i₀) (s i₂) :=
      GGPairConcl.of_excPlusModel hτ hp hp2 hBs hSC hN hM hZ
        (hs i₀).1 (hs i₀).2 (hs i₁).1 (hs i₁).2
        (hs i₀).1 (hs i₀).2 (hs i₂).1 (hs i₂).2
        hs01ne hs02ne ⟨fun _ => heq, fun _ => hs01comm⟩ B1
    obtain ⟨W, hW⟩ := hpair3 i₀ i₂ hM02
    obtain ⟨x, hx, y, hy, hxy⟩ := UnitaryBlockStandardPair.exists_not_commute hW
    exact hxy (hP.1 heq x hx y hy)
  have B2 : GGPairConcl Bs X (s i₀) (s i₂) := by
    refine ⟨?_, ?_⟩
    · intro hc
      exact absurd hc hs02nc
    · intro hnc K' _ _ _ f' hK' hU
      obtain ⟨W, hW⟩ := hpair3 i₀ i₂ hM02
      exact ⟨W, ggPhanNSAPairAux_stdPair_of_card (K := F) (K' := K') (f := f) (f' := f')
        hF hK' hW hU⟩
  by_cases hrr : r * r' = r' * r
  · exact GGPairConcl.of_excPlusModel hτ hp hp2 hBs hSC hN hM hZ
      (hs i₀).1 (hs i₀).2 (hs i₁).1 (hs i₁).2 hr hrR hr' hr'R hs01ne hne
      ⟨fun _ => hrr, fun _ => hs01comm⟩ B1
  · exact GGPairConcl.of_excPlusModel hτ hp hp2 hBs hSC hN hM hZ
      (hs i₀).1 (hs i₀).2 (hs i₂).1 (hs i₂).2 hr hrR hr' hr'R hs02ne hne
      ⟨fun h => absurd h hs02nc, fun h => absurd h hrr⟩ B2

theorem ggPairConcl_of_excPhanPayload_E7
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hM : GGExcPlusWeylModel .E7 p (ggGamma X hN).range)
    (hZ : ∀ z ∈ Subgroup.center ↥X, (z : G) ∈ Bs → z = 1)
    (hP : GGExcPhanPayloadOf 7 CoxeterMatrix.E₇ .E7 p Bs X)
    {r r' : MulAut ↥Bs} (hr : r ∈ ggAutomizer X Bs) (hrR : GGIsReflection p r)
    (hr' : r' ∈ ggAutomizer X Bs) (hr'R : GGIsReflection p r') (hne : r ≠ r') :
    GGPairConcl Bs X r r' := by
  obtain ⟨f, -, -, s, hs, F, _, _, _, hF, -, hcomm2, hpair3⟩ := hP
  exact ggPairConcl_of_excPlusModel_base (Or.inr (Or.inl rfl)) hp hp2 hBs hSC hN hM hZ
    (N := CoxeterMatrix.E₇) (i₀ := 0) (i₁ := 1) (i₂ := 2) (i₃ := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) hs hF hcomm2 hpair3 hr hrR hr' hr'R hne

theorem ggPairConcl_of_excPaySquare_E7
    {G : Type} [Group G] [Finite G] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hplus : p ∣ 2 ^ f + 1) {Bs X : Subgroup G} {ht : GGExcFive .E7}
    (hBs : IsElemAbelian p Bs) (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hM : GGExcPlusWeylModel .E7 p (ggGamma X hN).range)
    (hZ : ∀ z ∈ Subgroup.center ↥X, (z : G) ∈ Bs → z = 1)
    (S : ExcPay.ExcPaySquare .E7 ht f p Bs X)
    {r r' : MulAut ↥Bs} (hr : r ∈ ggAutomizer X Bs) (hrR : GGIsReflection p r)
    (hr' : r' ∈ ggAutomizer X Bs) (hr'R : GGIsReflection p r') (hne : r ≠ r') :
    GGPairConcl Bs X r r' := by
  have : NeZero f := ⟨by omega⟩
  refine ggPairConcl_of_excPlusModel_base (Or.inr (Or.inl rfl)) hp hp2 hBs hSC hN hM hZ
    (N := CoxeterMatrix.E₇) (i₀ := 0) (i₁ := 1) (i₂ := 2) (i₃ := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fun i => ⟨S.s_mem i, S.s_refl i⟩)
    (GGFinModel.card_actualQuadraticSubfield hf)
    (fun i j hij h2 => ExcPay.excPaySquare_comm (Or.inr (Or.inl rfl)) hp hp2 S
      (ExcPay.orth_simple_E7 hij h2)) (fun i j h3 => ?_) hr hrR hr' hr'R hne
  obtain ⟨θG, -, -, -, -, hpair⟩ :=
    ExcPay.excPaySquare_pair (Or.inr (Or.inl rfl)) hp hp2 hplus S (ExcPay.isA2Pair_simple_E7 h3)
  exact ⟨θG.range, hpair⟩

theorem two_le_of_prime_dvd_two_pow_add_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (h : p ∣ 2 ^ n + 1) : 2 ≤ n := by
  rcases n with _ | _ | n
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by simpa using h)) hp2
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using h)) hp3
  · omega

private theorem ggE7Plus_exists_model
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    (hE7 : GGInnerDiagOnLabel (fun p lab => lab.tag = .E7 ∧ p ∣ 2 ^ lab.n + 1) p Bs X) :
    ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      GGExcPlusWeylModel .E7 p (ggGamma X hN).range := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | ⟨y, hnb⟩
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 y X hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hE7
  obtain ⟨hN, hM, -⟩ := ggX_exists_overGamma_lift ggLabelRigidInput_holds hcfg hX hInn hΛ hhas
    (fun _ _ A => GGExcPlusWeylModel .E7 p A) (largeEvenLabelAll_excPlusModel_EE7 hp hp2 hS)
  exact ⟨hN, hM⟩

theorem ggPairConcl_of_selected_E7_plus
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (_hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (_hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) (_hXns : ¬ GGSplitLie p X)
    (_hXnu : ¬ GGMemberUnitary p Bs X)
    (hE7 : GGInnerDiagOnLabel (fun p lab => lab.tag = .E7 ∧ p ∣ 2 ^ lab.n + 1) p Bs X)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e)
    {r' : MulAut ↥Bs} (hr' : r' ∈ ggAutomizer X Bs) (hr'C : r' ∈ ggCoxRefl M e)
    (hne : r ≠ r') :
    GGPairConcl Bs X r r' := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hXn : X = L ∨ ∃ y, GGNbr p B x D J y X :=
    (hX.imp_right (GGSecFiveWeakNbr.of_mem hcfg)).imp_right fun hw => hw.1
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.1.1.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hcfg.1.1.2.1.2.2.2
  obtain ⟨hN, hM⟩ := ggE7Plus_exists_model hcfg hXn hE7
  have hrR : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
  have hr'R : GGIsReflection p r' := ggCoxRefl_isReflection hpres.2 hr'C
  by_cases hp3 : p = 3
  · subst hp3
    have hE7' : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ 1 ≤ lab.n) 3 Bs X :=
      largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨⟨hP.1, Nat.pos_of_ne_zero fun h0 => by
        have h := hP.1.2
        rw [h0] at h
        norm_num at h⟩, hP.2⟩) hE7
    obtain ⟨f, hf, hplus, -, hZ, ⟨S⟩⟩ := ExcPay.exists_excPaySquare_of_route_E7_three le_rfl hcfg
      hXn hE7' (Or.inr (Or.inr (Or.inl rfl)))
    exact ggPairConcl_of_excPaySquare_E7 hp hp2 hf hplus hBs hSC hN hM
      (fun z hz _ => Subgroup.mem_bot.mp (hZ ▸ hz)) S hr hrR hr' hr'R hne
  · have hE7' : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ 2 ≤ lab.n) p Bs X :=
      largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨⟨hP.1,
        two_le_of_prime_dvd_two_pow_add_one hp hp2 hp3 hP.1.2⟩, hP.2⟩) hE7
    obtain ⟨f, -, -, κ, -⟩ := ExcPay.exists_e7Equiv_of_marking hE7'
    have hZ : Subgroup.center ↥X = ⊥ := by
      have h1 := Subgroup.map_center_eq κ.symm
      rw [center_adjointGroup_eq_bot] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ κ.symm.injective).1 h1
    exact ggPairConcl_of_excPhanPayload_E7 hp hp2 hBs hSC hN hM
      (fun z hz _ => Subgroup.mem_bot.mp (hZ ▸ hz))
      (ExcPay.exists_excPhanPayload_of_marking_E7 hp hp3 hBs hSC hE7') hr hrR hr' hr'R hne

end CFSG.StandardType

end
