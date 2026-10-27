module

public import CFSG.Quasithin.H13.L32ACSkPfB
public import CFSG.Quasithin.H13.L32ACSk10
public import CFSG.RankThree.PartTwo.KFacts.KS116ProofTorus
public import CFSG.Quasithin.H13.KGFact22TorSp
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherInvariant
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.H13.L32A5Props
public import CFSG.Quasithin.H13.L32ACSk6
public import CFSG.Quasithin.H13.L32AHStr
public import CFSG.Quasithin.H13.L32ASk1
public import CFSG.Quasithin.H13.L32NSet14Gen
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.J1
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom coe_torusHom statedSp_ext)
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauAut tauAut_proj tauMat tauMat_apply)
open Matrix
open scoped Pointwise

section Sp4

variable {F : Type} [Field F]

local notation "Sp₄" => StatedSp 2 F
local notation "M₄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F

theorem tauMat_isFlagUpper {g : M₄} (hg : IsFlagUpper g) (hd : ∀ x, g x x = 1) :
    IsFlagUpper (tauMat g) ∧ ∀ x, tauMat g x x = 1 := by
  have z : ∀ x y, (flagOrder 2 x : ℕ) < flagOrder 2 y → g y x = 0 := hg
  have hba := z (.inl 0) (.inl 1) (by rw [flagOrder_inl, flagOrder_inl]; decide)
  have hca := z (.inl 0) (.inr 1) (by rw [flagOrder_inl, flagOrder_inr]; decide)
  have hda := z (.inl 0) (.inr 0) (by rw [flagOrder_inl, flagOrder_inr]; decide)
  have hcb := z (.inl 1) (.inr 1) (by rw [flagOrder_inl, flagOrder_inr]; decide)
  have hdb := z (.inl 1) (.inr 0) (by rw [flagOrder_inl, flagOrder_inr]; decide)
  have hdc := z (.inr 1) (.inr 0) (by rw [flagOrder_inr, flagOrder_inr]; decide)
  have h0 := hd (.inl 0)
  have h1 := hd (.inl 1)
  have h2 := hd (.inr 0)
  have h3 := hd (.inr 1)
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
      simp only [flagOrder_inl, flagOrder_inr] at hxy <;> norm_num at hxy <;>
      simp [tauMat_apply, CFSG.QuasithinUnique.Lin2.Five.tauPair, hba, hca, hda, hcb, hdb, hdc]
  · rcases x with x | x <;> fin_cases x <;>
      simp [tauMat_apply, CFSG.QuasithinUnique.Lin2.Five.tauPair, hba, hca, hdb, hdc,
        h0, h1, h2, h3]

theorem tauSp_mem_unipotent [CharP F 2] {u : Sp₄} (hu : u ∈ unipotent 2 F) :
    tauSp u ∈ unipotent 2 F := by
  rw [mem_unipotent_iff_isFlagUpper] at hu ⊢
  rw [coe_tauSp]
  exact tauMat_isFlagUpper hu.1 hu.2

theorem fieldSp_mem_unipotent (σ : F ≃+* F) {u : Sp₄} (hu : u ∈ unipotent 2 F) :
    fieldSp 2 F σ u ∈ unipotent 2 F := by
  rw [mem_unipotent_iff_isFlagUpper] at hu ⊢
  rw [coe_fieldSp]
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · rw [Matrix.map_apply, hu.1 x y hxy, map_zero]
  · rw [Matrix.map_apply, hu.2 x, map_one]

@[expose] noncomputable def sp4T (F : Type) [Field F] : (Fin 2 → Fˣ) →* StatedProj (StatedSp 2 F) :=
  (proj 2 F).comp torusHom

theorem sp4T_range_le [Finite F] [CharP F 2] :
    (sp4T F).range ≤ Subgroup.normalizer ((projUnipotent 2 F : Subgroup _) :
      Set (StatedProj (StatedSp 2 F))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro _ ⟨t, rfl⟩
  rw [normalizer_projUnipotent 2 (by norm_num)]
  exact ⟨_, torus_le_borelSubgroup ⟨t, rfl⟩, rfl⟩

theorem fieldAut_sp4T (σ : F ≃+* F) (t : Fin 2 → Fˣ) :
    fieldAut 2 F σ (sp4T F t) = sp4T F (fun i => Units.map σ.toRingHom.toMonoidHom (t i)) := by
  change fieldAut 2 F σ (proj 2 F (torusHom t)) = proj 2 F (torusHom _)
  rw [fieldAut_proj]
  congr 1
  apply statedSp_ext
  rw [coe_fieldSp, coe_torusHom, coe_torusHom]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [diagonal_apply, Units.val_inv_eq_inv_val, map_inv₀, apply_ite] <;>
    (intro h h'; exact absurd h h')

@[expose] def spTau (t : Fin 2 → Fˣ) : Fin 2 → Fˣ := ![t 0 * t 1, t 0 * (t 1)⁻¹]

theorem tauSp_torusHom [CharP F 2] (t : Fin 2 → Fˣ) : tauSp (torusHom t) = torusHom (spTau t) := by
  apply statedSp_ext
  rw [coe_tauSp, coe_torusHom, coe_torusHom]
  ext r c
  rcases r with r | r <;> rcases c with c | c <;> fin_cases r <;> fin_cases c <;>
    simp [tauMat_apply, CFSG.QuasithinUnique.Lin2.Five.tauPair, spTau, Units.val_inv_eq_inv_val]
  ring

theorem tauAut_sp4T [Finite F] [CharP F 2] (t : Fin 2 → Fˣ) :
    tauAut (sp4T F t) = sp4T F (spTau t) := by
  change tauAut (proj 2 F (torusHom t)) = proj 2 F (torusHom _)
  rw [tauAut_proj, tauSp_torusHom]

theorem sp4T_mem_iff [CharP F 2] (t : Fin 2 → Fˣ) :
    sp4T F t ∈ projUnipotent 2 F ↔ t = 1 := by
  constructor
  · rintro ⟨u, hu, he⟩
    have hz : u⁻¹ * torusHom t ∈ spScalars 2 F := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, he]
      exact inv_mul_cancel _
    rw [Subgroup.mem_subgroupOf, CFSG.Assembly.LowTwoRank.StatedScalars,
      MonoidHom.mem_range] at hz
    obtain ⟨c, hc⟩ := hz
    have hht : ((torusHom t : Sp₄) : GL (Fin 2 ⊕ Fin 2) F) =
        (u : GL (Fin 2 ⊕ Fin 2) F) * Matrix.GeneralLinearGroup.scalar _ c := by
      rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    have hd : ∀ x, ((torusHom t : Sp₄) : GL (Fin 2 ⊕ Fin 2) F) x x = c := by
      intro x
      rw [hht]
      change ((u : GL (Fin 2 ⊕ Fin 2) F) * scalar (Fin 2 ⊕ Fin 2) (c : F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) x x = c
      rw [scalar_apply, mul_diagonal, ((mem_unipotent_iff_isFlagUpper).mp hu).2 x, one_mul]
    have hsq : ∀ i, t i = (t i)⁻¹ := by
      intro i
      refine Units.ext ?_
      have h1 := hd (.inl i)
      have h2 := hd (.inr i)
      simp only [coe_torusHom, diagonal_apply_eq, Sum.elim_inl, Sum.elim_inr] at h1 h2
      rw [h1, h2]
    funext i
    have h1 : (t i) ^ 2 = 1 := by
      calc (t i) ^ 2 = t i * t i := pow_two _
        _ = t i * (t i)⁻¹ := by rw [← hsq i]
        _ = 1 := mul_inv_cancel _
    have h2 : ((t i : F)) ^ 2 = 1 := by
      have := congrArg Units.val h1
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    have h3 : ((t i : F) + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, h2, one_pow, CharTwo.add_self_eq_zero]
    have h4 : (t i : F) = -1 := eq_neg_of_add_eq_zero_left ((pow_eq_zero_iff two_ne_zero).mp h3)
    rw [CharTwo.neg_eq] at h4
    exact Units.ext h4
  · rintro rfl
    rw [map_one]
    exact one_mem _

section Main

variable [Finite F] [CharP F 2]

theorem sp4_comm_mem :
    ∀ a ∈ Subgroup.normalizer ((projUnipotent 2 F : Subgroup _) : Set (StatedProj Sp₄)),
      ∀ b ∈ Subgroup.normalizer ((projUnipotent 2 F : Subgroup _) : Set (StatedProj Sp₄)),
        a * b * a⁻¹ * b⁻¹ ∈ projUnipotent 2 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha b hb
  rw [normalizer_projUnipotent 2 (by norm_num)] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have hHN : (torusHom (r := 2) (k := F)).range ≤
      Subgroup.normalizer ((unipotent 2 F : Subgroup Sp₄) : Set Sp₄) := by
    rw [normalizer_unipotent]
    exact torus_le_borelSubgroup
  have hHab : ∀ h ∈ (torusHom (r := 2) (k := F)).range,
      ∀ h' ∈ (torusHom (r := 2) (k := F)).range, h * h' = h' * h := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hBHU : ∀ x ∈ borelSubgroup 2 F,
      x ∈ ((torusHom (r := 2) (k := F)).range : Set Sp₄) * (unipotent 2 F : Set Sp₄) := by
    intro x hx
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHN]
    have hY : KG22.spY.range ⊔ KG22.spY'.range ≤ (torusHom (r := 2) (k := F)).range := by
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact ⟨_, (KG22.spY_apply a).symm⟩
      · rintro _ ⟨b, rfl⟩
        exact ⟨_, (KG22.spY'_apply b).symm⟩
    exact sup_le_sup_right hY _ (KG22.borel_le hx)
  exact ⟨_, mul_mul_inv_mul_inv_mem_of_mem_mul hHN hHab (hBHU a' ha') (hBHU b' hb'),
    by simp only [map_mul, map_inv]⟩

theorem map_std_sp4 (σ : F ≃+* F) (ε : ℕ) :
    (projUnipotent 2 F).map (fieldAut 2 F σ * tauAut ^ ε).toMonoidHom = projUnipotent 2 F := by
  refine map_mul_eq (map_eq_of_forall_mem ?_) (map_pow_eq (map_eq_of_forall_mem ?_) ε)
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨_, fieldSp_mem_unipotent σ hu, (fieldAut_proj σ u).symm⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨_, tauSp_mem_unipotent hu, (tauAut_proj u).symm⟩

theorem comap_centMod_sp4_field (σ : F ≃+* F) :
    (centMod (projUnipotent 2 F) (fieldAut 2 F σ)).comap (sp4T F) =
      Subgroup.pi Set.univ fun _ => unitsFix σ := by
  ext t
  rw [Subgroup.mem_comap, mem_centMod, fieldAut_sp4T, ← map_inv, ← map_mul, sp4T_mem_iff]
  simp only [Subgroup.mem_pi, Set.mem_univ, true_implies, mem_unitsFix]
  refine ⟨fun h i => ?_, fun h => ⟨sp4T_range_le ⟨t, rfl⟩, ?_⟩⟩
  · have h1 := congrFun h.2 i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply, mul_inv_eq_one] at h1
    exact congrArg Units.val h1
  · funext i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply, mul_inv_eq_one]
    exact Units.ext (h i)

theorem mem_comap_centMod_sp4_graph (σ : F ≃+* F) (t : Fin 2 → Fˣ) :
    t ∈ (centMod (projUnipotent 2 F) (fieldAut 2 F σ * tauAut)).comap (sp4T F) ↔
      (fun i => Units.map σ.toRingHom.toMonoidHom (spTau t i)) = t := by
  rw [Subgroup.mem_comap, mem_centMod, MulAut.mul_apply, tauAut_sp4T, fieldAut_sp4T, ← map_inv,
    ← map_mul, sp4T_mem_iff, mul_inv_eq_one]
  exact ⟨fun h => h.2, fun h => ⟨sp4T_range_le ⟨t, rfl⟩, h⟩⟩

theorem card_comap_centMod_sp4_graph_le (σ : F ≃+* F) :
    Nat.card ((centMod (projUnipotent 2 F) (fieldAut 2 F σ * tauAut)).comap (sp4T F)) ≤
      Nat.card Fˣ := by
  refine Nat.card_le_card_of_injective (fun t => (t : Fin 2 → Fˣ) 0) ?_
  intro s t hst
  have hs := (mem_comap_centMod_sp4_graph σ s).mp s.2
  have ht := (mem_comap_centMod_sp4_graph σ t).mp t.2
  have h0 : (s : Fin 2 → Fˣ) 0 = (t : Fin 2 → Fˣ) 0 := hst
  have hs0 := congrFun hs 0
  have ht0 := congrFun ht 0
  simp only [spTau, Matrix.cons_val_zero] at hs0 ht0
  have h1 : (s : Fin 2 → Fˣ) 0 * (s : Fin 2 → Fˣ) 1 = (t : Fin 2 → Fˣ) 0 * (t : Fin 2 → Fˣ) 1 := by
    apply (Units.map_injective (f := σ.toRingHom.toMonoidHom) σ.injective)
    rw [hs0, ht0, h0]
  apply Subtype.ext
  funext i
  fin_cases i
  · exact h0
  · simpa [h0] using h1

theorem comap_centMod_sp4_graph_eq_bot (σ : F ≃+* F) (hσ : ∀ x, σ (σ x) = x) :
    (centMod (projUnipotent 2 F) (fieldAut 2 F σ * tauAut)).comap (sp4T F) = ⊥ := by
  refine eq_bot_iff.mpr fun t ht => ?_
  have h := (mem_comap_centMod_sp4_graph σ t).mp ht
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [spTau, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hσu : ∀ x : Fˣ,
      Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom x) = x :=
    fun x => Units.ext (hσ x)
  have e0 := congrArg (Units.map σ.toRingHom.toMonoidHom) h0
  have e1 := congrArg (Units.map σ.toRingHom.toMonoidHom) h1
  rw [hσu] at e0 e1
  rw [map_mul, ← e0] at h0
  rw [map_mul, map_inv, ← e0, ← e1] at h1
  have ht0 : t 0 = 1 := by
    have h2 : t 0 * t 0 = t 0 := by
      have := h0
      rwa [← e1, mul_mul_mul_comm, mul_inv_cancel, mul_one] at this
    simpa using h2
  have ht1 : t 1 = 1 := by
    have h2 : t 1 * t 1 = t 1 := by
      have := h1
      rwa [mul_inv, inv_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul] at this
    simpa using h2
  rw [Subgroup.mem_bot]
  funext i
  fin_cases i
  · exact ht0
  · exact ht1

theorem exists_conj_mul_std_sp4 (α : MulAut (StatedProj Sp₄)) :
    ∃ (y : StatedProj Sp₄) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      α = MulAut.conj y * (fieldAut 2 F σ * tauAut ^ ε) := by
  obtain ⟨A, σ, ε, hε, rfl⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow α
  obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.KFacts.conjAut_mem_inner_of_charTwo A
  exact ⟨y, σ, ε, hε, by rw [mul_assoc]; exact congrArg (· * _) hy.symm⟩

theorem n4At_sp4 (hF4 : 4 ≤ Nat.card F) : N4At (StatedProj Sp₄) (projUnipotent 2 F) := by
  intro α _ hαU hcent
  obtain ⟨y, σ, ε, hε, rfl⟩ := exists_conj_mul_std_sp4 α
  rw [centMod_conj_mul_eq sp4_comm_mem (map_std_sp4 σ ε) hαU] at hcent
  interval_cases ε
  · rw [pow_zero, mul_one] at hcent ⊢
    have hσ : σ = 1 := by
      rw [← unitsFix_eq_top_iff, eq_top_iff]
      intro a _
      have h1 : (fun _ => a : Fin 2 → Fˣ) ∈
          (centMod (projUnipotent 2 F) (fieldAut 2 F σ)).comap (sp4T F) :=
        hcent (sp4T_range_le ⟨_, rfl⟩)
      rw [comap_centMod_sp4_field] at h1
      exact h1 0 (Set.mem_univ _)
    left
    rw [hσ, map_one, mul_one]
    exact ⟨y, rfl⟩
  · exfalso
    rw [pow_one] at hcent
    have hall : ∀ a : Fˣ, a = 1 := by
      intro a
      have h1 : (![a, 1] : Fin 2 → Fˣ) ∈
          (centMod (projUnipotent 2 F) (fieldAut 2 F σ * tauAut)).comap (sp4T F) :=
        hcent (sp4T_range_le ⟨_, rfl⟩)
      have h2 := (mem_comap_centMod_sp4_graph σ _).mp h1
      have h3 := congrFun h2 0
      have h4 := congrFun h2 1
      simp only [spTau, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, inv_one] at h3 h4
      rw [h3] at h4
      exact h4
    have h1 : Nat.card Fˣ = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by
      rw [hall a, hall b]⟩, ⟨1⟩⟩
    have h2 := Nat.card_eq_card_units_add_one F
    omega

theorem n2At_sp4 (hF4 : 4 ≤ Nat.card F) : N2At (StatedProj Sp₄) (projUnipotent 2 F) := by
  intro α _ hαU hidx
  exfalso
  obtain ⟨y, σ, ε, hε, rfl⟩ := exists_conj_mul_std_sp4 α
  rw [centMod_conj_mul_eq sp4_comm_mem (map_std_sp4 σ ε) hαU] at hidx
  interval_cases ε
  · rw [pow_zero, mul_one] at hidx
    have h1 := index_comap_le (projUnipotent 2 F) (fieldAut 2 F σ) (sp4T F) sp4T_range_le
    rw [comap_centMod_sp4_field, hidx] at h1
    have hσ := eq_one_of_index_pi_unitsFix_le_three (by rw [Fintype.card_fin]) h1
    rw [hσ, map_one, centMod_one, Subgroup.relIndex_self] at hidx
    omega
  · rw [pow_one] at hidx
    set C := (centMod (projUnipotent 2 F) (fieldAut 2 F σ * tauAut)).comap (sp4T F)
    have h1 : C.index ≤ 3 := by
      have := index_comap_le (projUnipotent 2 F) (fieldAut 2 F σ * tauAut) (sp4T F) sp4T_range_le
      rwa [hidx] at this
    have h2 := C.card_mul_index
    have h3 : Nat.card C ≤ Nat.card Fˣ := card_comap_centMod_sp4_graph_le σ
    have h4 : Nat.card (Fin 2 → Fˣ) = Nat.card Fˣ * Nat.card Fˣ := by
      rw [Nat.card_pi, Fin.prod_univ_two]
    have h5 := Nat.card_eq_card_units_add_one F
    have hpos : 0 < Nat.card C := Nat.card_pos
    have hq : Nat.card Fˣ ≤ 3 := by
      by_contra hq
      have : Nat.card Fˣ * Nat.card Fˣ ≤ Nat.card Fˣ * 3 := by
        rw [← h4, ← h2]
        exact Nat.mul_le_mul h3 h1
      nlinarith
    have hq4 : Nat.card F = 2 ^ 2 := by omega
    have hσ2 := ringAut_pow_eq_one hq4 σ
    have hC : C = ⊥ := comap_centMod_sp4_graph_eq_bot σ fun x => by
      have := congrArg (fun φ : F ≃+* F => φ x) hσ2
      simpa [pow_two] using this
    rw [hC] at h1 h2
    rw [h4, Subgroup.card_bot] at h2
    have h6 : Nat.card Fˣ = 3 := by omega
    rw [h6] at h2
    omega

theorem isSylowTwoOf_projUnipotent_two : IsSylowTwoOf (projUnipotent 2 F) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨S, hS⟩, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.unique_symplectic_four_Sylow_center
      (K := F) (Nat.card F) rfl
  let T : Sylow 2 (StatedProj Sp₄) :=
    S.mapSurjective (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective
      (r := 2) (K := F))
  have hT : (T : Subgroup (StatedProj Sp₄)) = projUnipotent 2 F := by
    rw [Sylow.coe_mapSurjective, hS]
    rfl
  rw [← hT]
  exact isSylowTwoOf_sylow T

end Main

end Sp4

theorem n2Model_n4Model_of_isPSp4 {M : Type} [Group M] {n : ℕ} (hn : 1 < n)
    (h : IsPSp4 2 n M) : N2Model M ∧ N4Model M := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact ⟨(N2Model.of_at isSylowTwoOf_projUnipotent_two (n2At_sp4 hF4)).of_mulEquiv e.symm,
    (N4Model.of_at isSylowTwoOf_projUnipotent_two (n4At_sp4 hF4)).of_mulEquiv e.symm⟩

end CFSG.Quasithin.H13.L32A.C.SkPf
