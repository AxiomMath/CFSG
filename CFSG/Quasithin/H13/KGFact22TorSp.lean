module

public import CFSG.Quasithin.H13.KGFact22Tor
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagTriangular
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E6TorusFacts
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13.KG22

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique

variable {K : Type} [Field K]

local notation "Sp₄" => StatedSp 2 K
local notation "M₄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K

@[expose] noncomputable def spY : Kˣ →* Sp₄ :=
  torusHom.comp (MonoidHom.mulSingle (fun _ : Fin 2 => Kˣ) 0)

@[expose] noncomputable def spY' : Kˣ →* Sp₄ :=
  torusHom.comp (MonoidHom.mulSingle (fun _ : Fin 2 => Kˣ) 1)

@[expose] noncomputable def spW : Sp₄ :=
  lam 0 sl2W

theorem spY_apply (a : Kˣ) : spY a = torusHom (Pi.mulSingle 0 a) :=
  rfl

theorem spY'_apply (b : Kˣ) : spY' b = torusHom (Pi.mulSingle 1 b) :=
  rfl

theorem spY_injective : Function.Injective (spY : Kˣ →* Sp₄) := by
  intro a b h
  rw [spY_apply, spY_apply] at h
  exact Pi.mulSingle_injective (M := fun _ : Fin 2 => Kˣ) 0 (torusHom_injective h)

theorem spY_mem_borel (a : Kˣ) : spY a ∈ borelSubgroup 2 K :=
  torus_le_borelSubgroup ⟨_, rfl⟩

theorem spY'_mem_borel (b : Kˣ) : spY' b ∈ borelSubgroup 2 K :=
  torus_le_borelSubgroup ⟨_, rfl⟩

theorem spY_comm (a b : Kˣ) : spY a * spY' b = spY' b * spY a := by
  rw [spY_apply, spY'_apply, ← map_mul, ← map_mul, mul_comm]

theorem sl2W_conj_sl2Diag (a : Kˣ) :
    (sl2W : SpecialLinearGroup (Fin 2) K) * sl2Diag a * sl2W⁻¹ = sl2Diag a⁻¹ := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2W,
    coe_sl2W_inv, coe_sl2Diag, coe_sl2Diag]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp

theorem spW_conj_spY (a : Kˣ) : spW * spY a * (spW : Sp₄)⁻¹ = (spY a)⁻¹ := by
  have h1 : spY a = lam 0 (sl2Diag a) := by rw [spY_apply, lam_sl2Diag]
  have h2 : spY a⁻¹ = lam 0 (sl2Diag a⁻¹) := by rw [spY_apply, lam_sl2Diag]
  rw [← map_inv, h1, h2, spW, ← map_inv, ← map_mul, ← map_mul, sl2W_conj_sl2Diag]

theorem spW_comm_spY' (b : Kˣ) : spW * spY' b = spY' b * (spW : Sp₄) := by
  refine (statedSp_commute ?_).eq
  rw [spW, spY'_apply, coe_lam, coe_torusHom]
  show _ * _ = _ * _
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [pairMat, Pi.mulSingle_apply]

theorem spW_conj_spY' (b : Kˣ) : spW * spY' b * (spW : Sp₄)⁻¹ = spY' b := by
  rw [spW_comm_spY', mul_inv_cancel_right]

theorem spW_not_mem_borel : (spW : Sp₄) ∉ borelSubgroup 2 K := by
  intro h
  obtain ⟨A, C, -, -, -, hg⟩ := mem_borelSubgroup_iff.mp h
  have h1 := congrFun (congrFun hg (Sum.inr 0)) (Sum.inl 0)
  rw [spW, coe_lam, blockMat, fromBlocks_apply₂₁] at h1
  simp [pairMat] at h1

theorem borel_le : borelSubgroup 2 K ≤ spY.range ⊔ spY'.range ⊔ unipotent 2 K := by
  intro b hb
  set t := diagHom 2 K ⟨b, hb⟩ with ht
  have htB : torusHom t ∈ borelSubgroup 2 K := torus_le_borelSubgroup ⟨t, rfl⟩
  have hdt : diagHom 2 K ⟨torusHom t, htB⟩ = t := by
    funext i
    apply Units.ext
    simp [diagHom, diagEntry, SymplecticTorusWeyl.coe_torusHom]
  have hu : (torusHom t)⁻¹ * b ∈ unipotent 2 K := by
    have hmem : (⟨torusHom t, htB⟩ : ↥(borelSubgroup 2 K))⁻¹ * ⟨b, hb⟩ ∈ (diagHom 2 K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdt, ← ht, inv_mul_cancel]
    rw [ker_diagHom, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  have hsplit : torusHom t = spY (t 0) * spY' (t 1) := by
    rw [spY_apply, spY'_apply, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp
  have hb' : b = spY (t 0) * spY' (t 1) * ((torusHom t)⁻¹ * b) := by
    rw [← hsplit, mul_inv_cancel_left]
  rw [hb']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _
    (Subgroup.mem_sup_left ⟨t 0, rfl⟩) (Subgroup.mem_sup_right ⟨t 1, rfl⟩)))
    (Subgroup.mem_sup_right hu)

theorem spY_proj_eq_one {y : Sp₄} (hy : y ∈ spY.range) (h : proj 2 K y = 1) : y = 1 := by
  obtain ⟨a, rfl⟩ := hy
  have hz : spY a ∈ spScalars 2 K := by
    rw [← ker_proj]
    exact h
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hc' := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K => (g : M₄)) hc
  have h11 := congrFun (congrFun hc' (Sum.inl 1)) (Sum.inl 1)
  have h00 := congrFun (congrFun hc' (Sum.inl 0)) (Sum.inl 0)
  simp only [spY_apply, coe_torusHom, Matrix.GeneralLinearGroup.coe_scalar] at h11 h00
  simp [Pi.mulSingle_apply] at h11 h00
  have ha : a = 1 := Units.ext (by rw [← h00, h11, Units.val_one])
  rw [ha, map_one]

variable [CharP K 2]

theorem torusOut_projSp4 [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    TorusOut (projUnipotent 2 K) n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBN : borelSubgroup 2 K ≤ Subgroup.normalizer (unipotent 2 K : Set Sp₄) := by
    rw [normalizer_unipotent]
  refine torusOut_of_hom (proj 2 K) (U := unipotent 2 K) (B := borelSubgroup 2 K)
    (Y₀ := spY.range) (Y₀' := spY'.range) (w₀ := spW) ?_ ?_ ?_ borel_le
    (isCyclic_of_surjective spY.rangeRestrict spY.rangeRestrict_surjective)
    (isCyclic_of_surjective spY'.rangeRestrict spY'.rangeRestrict_surjective)
    (fun y hy h => spY_proj_eq_one hy h) ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact hBN (spY_mem_borel a)
  · rintro _ ⟨b, rfl⟩
    exact hBN (spY'_mem_borel b)
  · show Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj Sp₄)) ≤ _
    rw [normalizer_projUnipotent 2 (by norm_num)]
    rfl
  · rw [← Nat.card_congr (MonoidHom.ofInjective spY_injective).toEquiv, Nat.card_units, hK]
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact spY_comm a b
  · intro h
    have h1 : spW ∈ ((borelSubgroup 2 K).map (proj 2 K)).comap (proj 2 K) := h
    rw [Subgroup.comap_map_eq, ker_proj, sup_eq_left.2 ?_] at h1
    · exact spW_not_mem_borel h1
    · rw [← isoFlagStabilizer_flag]
      exact spScalars_le_isoFlagStabilizer _
  · rintro _ ⟨a, rfl⟩
    exact spW_conj_spY a
  · rintro _ ⟨b, rfl⟩
    exact spW_conj_spY' b

theorem torusOut_of_isPSp4 {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (hX : IsPSp4 2 n X) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) : TorusOut S n := by
  obtain ⟨-, K', _, _, hK, ⟨e⟩⟩ := hX
  have : CharP K' 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  refine torusOut_of_equiv e (fun S' hS' => ?_) hS
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K') 2 (r := 2) (by norm_num)
  exact torusOut_of_sylow P (hP ▸ torusOut_projSp4 hK) hS'

end CFSG.Quasithin.H13.KG22
