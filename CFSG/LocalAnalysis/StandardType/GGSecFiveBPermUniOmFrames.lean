module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGQTwoSUThreeDiagonalComm
import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenTriples
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CastBlockSU
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmKFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniModelTwoCenter
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Simple
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorus
import CFSG.Assembly.Subnormal
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredGeneration
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models.OrthogonalPairs

private theorem isQuasisimple_normOmega {f : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K]
    [Finite F] [Finite K] [CharP K 2] (E : QuadExt F K (unitaryInvolution K 2 f)) {m : ℕ}
    (hm : 2 ≤ m) : CFSG.Open.IsQuasisimple ↥(normOmega E m) := by
  have := isSimpleGroup_normOmega E (k := m) (by omega)
  have := isPerfect_normOmega E (k := m) (by omega)
  exact ⟨Group.IsPerfect.commutator_eq_top,
    ((QuotientGroup.quotientMulEquivOfEq (center_normOmega_eq_bot (E := E) hm)).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩

theorem GGSecFiveBPermOmKFrame.comp_normPerm {G : Type} [Group G] {p n m f : ℕ} {F K : Type}
    [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 f)} {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (m + 1) ≃ Fin n}
    {κ : normOmega E m →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (hm : 3 ≤ m) {τ : Equiv.Perm (Fin m)}
    {τ' : Equiv.Perm (Fin (m + 1))} (hτ : ∀ i, τ' (Fin.castSucc i) = Fin.castSucc (τ i)) :
    GGSecFiveBPermOmKFrame E Bs X eta (τ'.trans π)
      (κ.comp (MulAut.conj (normPerm E hm τ)).toMonoidHom) χ := by
  obtain ⟨hinj, hrange, hχ, hact⟩ := hκ
  refine ⟨hinj.comp (MulAut.conj (normPerm E hm τ)).injective, ?_, hχ, fun b => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, hrange]
  obtain ⟨T, hT, hbT⟩ := hact b
  refine ⟨(normPerm E hm τ)⁻¹ * T * normPerm E hm τ, fun v => ?_, fun s => ?_⟩
  · rw [← map_inv]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, normPerm_apply, hT]
    refine Prod.ext rfl (funext fun i => ?_)
    simp [hτ]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hbT]
    congr 1
    group

theorem mem_map_conj_iff_coord_eq_one {G : Type} [Group G] {p n : ℕ} {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {w : G}
    (hw : w ∈ Subgroup.normalizer (Bs : Set G)) {σ : Equiv.Perm (Fin n)}
    (hact : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut σ) {i0 : Fin n}
    (hX : ∀ b : ↥Bs, (b : G) ∈ X ↔ eta b i0 = 1) :
    ∀ b : ↥Bs, (b : G) ∈ X.map (MulAut.conj w).toMonoidHom ↔ eta b (σ i0) = 1 := by
  intro b
  have hcoord : eta b (σ i0) = eta ((ggConjAut Bs hw)⁻¹ b) i0 := by
    simpa using eta_ggConjAut_apply_of_permAut hw hact ((ggConjAut Bs hw)⁻¹ b) i0
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    ← inv_apply_of_forall (ggConjAut_apply Bs hw) b, hX ((ggConjAut Bs hw)⁻¹ b), ← hcoord]

theorem GGSecFiveBPermOmKFrame.blockComm_eq_map_normBlock {G : Type} [Group G] [Finite G]
    {p n m f : ℕ} [Fact p.Prime] {F K : Type} [Field F] [Field K] [Algebra F K]
    [Finite K] [CharP K 2] {E : QuadExt F K (unitaryInvolution K 2 f)}
    {Bs X : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (m + 1) ≃ Fin n}
    {κ : normOmega E m →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    {S : Finset (Fin m)} (hS : 2 ≤ S.card) (hSm : S.card < m) :
    ggBlockComm Bs eta ((fun i : Fin m => π i.castSucc) '' (S : Set (Fin m))) =
      (normBlock E m S).map κ := by
  classical
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have hm3 : 3 ≤ m := by omega
  have hsimp : IsSimpleGroup ↥(normOmega E S.card) :=
    isSimpleGroup_normOmega E (k := S.card) (by omega)
  let A : Finset (Fin m) := Finset.univ.map (Fin.castLEEmb hSm.le)
  have hAcard : A.card = S.card := by simp [A]
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq A S hAcard
  have hAimage : A.image τ = S := by
    simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using hτ
  let τ' : Equiv.Perm (Fin (m + 1)) := τ.viaFintypeEmbedding Fin.castSuccEmb
  have hτ' : ∀ i, τ' (Fin.castSucc i) = Fin.castSucc (τ i) := fun i =>
    Equiv.Perm.viaFintypeEmbedding_apply_image τ Fin.castSuccEmb i
  have hκ' := hκ.comp_normPerm hm3 hτ'
  have hblk := ggSecFiveBPermOmK_ggBlockComm_eq (k := S.card) hBs hyB hX hκ' hS hSm hsimp
  have hset : (Set.range fun i : Fin S.card =>
      (τ'.trans π) (Fin.castLE (by omega : S.card ≤ m + 1) i)) =
      (fun i : Fin m => π i.castSucc) '' (S : Set (Fin m)) := by
    ext x
    simp only [Set.mem_range, Equiv.trans_apply, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨τ (Fin.castLE hSm.le i), ?_, ?_⟩
      · have hmem : τ (Fin.castLE hSm.le i) ∈ A.image τ :=
          Finset.mem_image_of_mem τ
            (Finset.mem_map_of_mem (Fin.castLEEmb hSm.le) (Finset.mem_univ i))
        simpa only [hAimage] using hmem
      · have hc : (Fin.castLE (by omega : S.card ≤ m + 1) i) =
            Fin.castSucc (Fin.castLE hSm.le i) := Fin.ext rfl
        rw [hc, hτ']
    · rintro ⟨s, hs, rfl⟩
      rw [← hAimage] at hs
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp ha
      refine ⟨i, ?_⟩
      have hcast : (Fin.castLEEmb hSm.le) i = Fin.castLE hSm.le i := rfl
      rw [hcast]
      have hc : (Fin.castLE (by omega : S.card ≤ m + 1) i) =
          Fin.castSucc (Fin.castLE hSm.le i) := Fin.ext rfl
      rw [hc, hτ']
  rw [← hset, hblk]
  rw [show Subgroup.map (κ.comp (MulAut.conj (normPerm E hm3 τ)).toMonoidHom)
      (normOmegaCast E hSm.le).range =
      Subgroup.map κ ((normOmegaCast E hSm.le).range.map
        (MulAut.conj (normPerm E hm3 τ)).toMonoidHom) from
    (Subgroup.map_map (K := (normOmegaCast E hSm.le).range) (g := κ)
      (f := (MulAut.conj (normPerm E hm3 τ)).toMonoidHom)).symm]
  rw [range_normOmegaCast E hSm.le, map_normBlock_normPerm E hm3 τ A, hAimage]

theorem ggSecFiveBPermOmK_ggBlockComm_le_of_card {G : Type} [Group G] [Finite G] {p n m f : ℕ}
    [Fact p.Prime] {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {k : ℕ}
    {E : QuadExt F K (unitaryInvolution K 2 f)} {Bs X : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (m + 1) ≃ Fin n}
    {κ : normOmega E m →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (hk : 2 ≤ k) (hkm : k < m)
    (hsimp : IsSimpleGroup ↥(normOmega E k)) {T : Finset (Fin (m + 1))} (hT : T.card = k)
    (hlast : Fin.last m ∉ T) :
    ggBlockComm Bs eta (π '' (T : Set (Fin (m + 1)))) ≤ X := by
  classical
  set T' : Finset (Fin m) := Finset.univ.filter fun j => Fin.castSucc j ∈ T with hT'
  have hTmap : T'.map Fin.castSuccEmb = T := by
    ext x
    simp only [Finset.mem_map, hT', Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.coe_castSuccEmb]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hx
      rcases Fin.eq_castSucc_or_eq_last x with ⟨j, rfl⟩ | rfl
      · exact ⟨j, hx, rfl⟩
      · exact absurd hx hlast
  have hT'card : T'.card = k := by
    rw [← Finset.card_map Fin.castSuccEmb, hTmap, hT]
  have hTset : (π '' (T : Set (Fin (m + 1)))) =
      (fun i : Fin m => π i.castSucc) '' (T' : Set (Fin m)) := by
    rw [← hTmap, Finset.coe_map, Set.image_image]
    simp only [Fin.castSuccEmb_apply]
  rw [hTset, GGSecFiveBPermOmKFrame.blockComm_eq_map_normBlock (S := T') hBs hyB hX hκ
    (by rwa [hT'card]) (by rwa [hT'card]), ← hκ.2.1]
  exact Subgroup.map_le_range _ _

theorem GGSecFiveBPermUniLFrame.range_comp_uniCast_le_of_card_three {G : Type} [Group G]
    {p m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin (m + 1))} {σ : ↥(unitarySU 2 1 K (m + 1)) →* G}
    {χ : Multiplicative (ZMod p) →* Kˣ}
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 1 K)
    (hp : p.Prime) (hm : 4 ≤ m) {M : Subgroup G}
    (hM : ∀ S : Finset (Fin (m + 1)), S.card = 3 → Fin.last m ∉ S →
      ggBlockComm Bs eta (π '' (S : Set (Fin (m + 1)))) ≤ M) :
    (σ.comp (uniCast hK m)).range ≤ M :=
  range_comp_uniCast_le_of_iSup_blockSU hK σ (SuNsRootGen.iSup_blockSU_triples hK hm)
    fun S hS => (hF.map_blockSU_triple_le_ggBlockComm hK hp _
      (by rw [Finset.card_map, hS])).trans
      (hM _ (by rw [Finset.card_map, hS]) fun h => by
        obtain ⟨a, -, ha⟩ := Finset.mem_map.mp h
        exact (Fin.castSucc_lt_last a).ne ha)

theorem GGSecFiveBPermUniLFrame.range_comp_uniCast_le_of_omKFrame {G : Type} [Group G]
    [Finite G] {p m f : ℕ} [Fact p.Prime] {F K : Type} [Field F] [Field K] [Algebra F K]
    [Finite F] [Finite K] [CharP K 2] {E : QuadExt F K (unitaryInvolution K 2 f)}
    {Bs X L : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin (m + 1))}
    {κ : normOmega E m →* G} {χK : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χK) {σ : ↥(unitarySU 2 1 K (m + 1)) →* G}
    {χ : Multiplicative (ZMod p) →* Kˣ} (hF : GGSecFiveBPermUniLFrame Bs L eta π σ χ)
    (hK : UnitaryFieldData 2 1 K) (hm : 4 ≤ m) :
    (σ.comp (uniCast hK m)).range ≤ X :=
  hF.range_comp_uniCast_le_of_card_three hK Fact.out hm fun _ hS hl =>
    ggSecFiveBPermOmK_ggBlockComm_le_of_card hBs hyB hX hκ (by norm_num) (by omega)
      (isSimpleGroup_normOmega E (by norm_num)) hS hl


theorem GGSecFiveBPermUniOmCell.exists_frames (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {m : ℕ} (hm : 3 ≤ m)
    {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull (m + 1) p)
    {f : ℕ} {K : Subgroup G} {i0 : Fin (m + 1)} (hz : f = 1 → Line63.H5.twoCenter L = ⊥)
    (hcell : GGSecFiveBPermUniOmCell p Bs L 𝒦 (m + 1) eta f K i0) :
    p ∣ 2 ^ f + 1 ∧ ∃ y ∈ Bs, CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
        (_ : Algebra (GaloisField 2 f) F)
        (E : QuadExt (GaloisField 2 f) F (unitaryInvolution F 2 f)),
        UnitaryFieldData 2 f F ∧ ∃ π : Equiv.Perm (Fin (m + 1)), π (Fin.last m) = i0 ∧
          (∃ (κ : normOmega E m →* G) (χ : Multiplicative (ZMod p) →* Fˣ),
            GGSecFiveBPermOmKFrame E Bs K eta π κ χ) ∧
          ∃ (σ : ↥(unitarySU 2 f F (m + 1)) →* G) (χ : Multiplicative (ZMod p) →* Fˣ),
            GGSecFiveBPermUniLFrame Bs L eta π σ χ := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hlab, hK𝒦, hiso, hAK⟩ := hcell
  obtain ⟨hpq, F, _, _, _, hN, φ, -, hM, hdiag⟩ :=
    exists_unitary_model_of_uniLabel_of_twoCenter hR (by omega) hz hlab
  have hUF : UnitaryFieldData 2 f F := hM.field
  let _ : Algebra (GaloisField 2 f) F := galoisAlgebra hUF
  have E : QuadExt (GaloisField 2 f) F (unitaryInvolution F 2 f) := galoisQuadExt hUF
  obtain ⟨eK⟩ : Nonempty (↥K ≃* normOmega E m) := by
    rcases hiso with ⟨hev, b, c, hirr, ⟨e⟩⟩ | ⟨hodd, ⟨e⟩⟩
    · have hmo : Odd m := by
        obtain ⟨j, hj⟩ := hev
        exact ⟨j - 1, by omega⟩
      obtain ⟨e'⟩ := nonempty_normOmega_mulEquiv_minus E hmo hirr
      exact ⟨e.trans e'.symm⟩
    · have hme : Even m := by
        obtain ⟨j, hj⟩ := hodd
        exact ⟨j, by omega⟩
      obtain ⟨e'⟩ := nonempty_normOmega_mulEquiv_plus E hme
      exact ⟨e.trans e'.symm⟩
  obtain ⟨y, hNy⟩ := hR.2.2.2.1.2 K hK𝒦
  have hyBs : y ∈ Bs := hR.1.1.2.1.1 hNy.1.2.1
  have hKp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K := hNy.1.2.2.2.2.1
  have hKc : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    ⟨hKp.1, isSubnormal_iff_open.mp hKp.2.1,
      CFSG.Open.IsQuasisimple.of_mulEquiv eK (isQuasisimple_normOmega E (by omega))⟩
  obtain ⟨π, hπ, κ, χK, hκ⟩ := ggSecFiveBPermOmK_exists_frame hMp hp2 E hUF hpq hm rfl
    hR.1.1.2.1 (hR.1.2.2.1.2 y K hNy) eK eta hAK
  obtain ⟨-, hBsE, -, -, -⟩ := hR.1.1.tableB_facts
  obtain ⟨σ, χ, hLF⟩ := exists_uniLFrame_of_model hp hp2 hBsE hR.1.1.2.1.2.2.2
    hR.1.1.card_bstar_inf_centralizer_L.le (by omega) eta hA hN φ hM hdiag π
  exact ⟨hpq, y, hyBs, hKc, F, inferInstance, inferInstance, inferInstance, inferInstance, E, hUF,
    π, hπ, ⟨κ, χK, hκ⟩, σ, χ, hLF⟩

end CFSG.StandardType

end
