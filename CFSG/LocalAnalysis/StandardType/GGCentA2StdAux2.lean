module

public import CFSG.LocalAnalysis.StandardType.GGCentA2StdAux
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7CF24Grp
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
public import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3

public section

namespace CFSG.StandardType.NTPlane

open scoped commutatorElement

theorem ntpA2S_le_fixed {S G : Type*} [Group S] [Group G] (Φ : S →* S) (ι : S →* G)
    (hι : ι.ker ≤ Subgroup.center S) (stp : G →* G) (hstp : ∀ X, stp (ι X) = ι (Φ X))
    (K : Subgroup G) (hKperf : _root_.commutator ↥K = ⊤) (hKle : K ≤ ι.range)
    (hKfix : ∀ k ∈ K, stp k = k) :
    K ≤ (Φ.eqLocus (MonoidHom.id _)).map ι := by
  classical
  let Z : Subgroup S := Subgroup.center S
  let H : Subgroup S :=
    { carrier := {x | Φ x * x⁻¹ ∈ Z}
      one_mem' := by simp [Z]
      mul_mem' := by
        intro x y hx hy
        change Φ (x * y) * (x * y)⁻¹ ∈ Z
        rw [map_mul, _root_.mul_inv_rev]
        have hcomm : (Φ y * y⁻¹) * x⁻¹ = x⁻¹ * (Φ y * y⁻¹) :=
          (Subgroup.mem_center_iff.mp hy x⁻¹).symm
        have heq : Φ x * Φ y * (y⁻¹ * x⁻¹) = (Φ x * x⁻¹) * (Φ y * y⁻¹) := by
          calc Φ x * Φ y * (y⁻¹ * x⁻¹) = Φ x * (Φ y * y⁻¹) * x⁻¹ := by group
            _ = Φ x * (x⁻¹ * (Φ y * y⁻¹)) := by rw [mul_assoc (Φ x), hcomm]
            _ = (Φ x * x⁻¹) * (Φ y * y⁻¹) := by group
        rw [heq]
        exact Z.mul_mem hx hy
      inv_mem' := by
        intro x hx
        change Φ x⁻¹ * (x⁻¹)⁻¹ ∈ Z
        rw [map_inv, inv_inv]
        have hxinv : (Φ x * x⁻¹)⁻¹ ∈ Z := Z.inv_mem hx
        have hΦx : Φ x = (Φ x * x⁻¹) * x := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
        have hΦx' : (Φ x)⁻¹ = x⁻¹ * (Φ x * x⁻¹)⁻¹ := by
          have := congrArg (fun y : S => y⁻¹) hΦx
          simpa only [_root_.mul_inv_rev] using this
        rw [hΦx']
        have hcomm : (Φ x * x⁻¹)⁻¹ * x = x * (Φ x * x⁻¹)⁻¹ :=
          (Subgroup.mem_center_iff.mp hxinv x).symm
        have heq : x⁻¹ * (Φ x * x⁻¹)⁻¹ * x = (Φ x * x⁻¹)⁻¹ := by
          rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [heq]
        exact hxinv }
  let P : Subgroup S := Φ.eqLocus (MonoidHom.id _)
  let theta : H →* Subgroup.center S :=
    { toFun := fun x => ⟨Φ (x : S) * (x : S)⁻¹, x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro x y
        apply Subtype.ext
        change Φ ((x : S) * (y : S)) * ((x : S) * (y : S))⁻¹ =
          (Φ (x : S) * (x : S)⁻¹) * (Φ (y : S) * (y : S)⁻¹)
        rw [map_mul, _root_.mul_inv_rev]
        have hcomm : (Φ (y : S) * (y : S)⁻¹) * (x : S)⁻¹ =
            (x : S)⁻¹ * (Φ (y : S) * (y : S)⁻¹) :=
          (Subgroup.mem_center_iff.mp y.2 (x : S)⁻¹).symm
        have heq : Φ (x : S) * Φ (y : S) * ((y : S)⁻¹ * (x : S)⁻¹) =
            (Φ (x : S) * (x : S)⁻¹) * (Φ (y : S) * (y : S)⁻¹) := by
          calc Φ (x : S) * Φ (y : S) * ((y : S)⁻¹ * (x : S)⁻¹) =
              Φ (x : S) * (Φ (y : S) * (y : S)⁻¹) * (x : S)⁻¹ := by group
            _ = Φ (x : S) * ((x : S)⁻¹ * (Φ (y : S) * (y : S)⁻¹)) := by
                rw [mul_assoc (Φ (x : S)), hcomm]
            _ = (Φ (x : S) * (x : S)⁻¹) *
                (Φ (y : S) * (y : S)⁻¹) := by group
        rw [heq] }
  have hker_le : ∀ x : H, theta x = 1 → (x : S) ∈ P := by
    intro x hx
    have hx1 : Φ (x : S) * (x : S)⁻¹ = 1 := by
      have hx' := congrArg (fun z : Subgroup.center S => (z : S)) hx
      change Φ (x : S) * (x : S)⁻¹ = (1 : S) at hx'
      exact hx'
    change Φ (x : S) = (x : S)
    calc Φ (x : S) = Φ (x : S) * (x : S)⁻¹ * (x : S) := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = 1 * (x : S) := by rw [hx1]
      _ = (x : S) := one_mul _
  have hHH : ⁅H, H⁆ ≤ P := by
    have hle : _root_.commutator ↥H ≤ theta.ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      change theta ⁅x, y⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' (theta x) (theta y))
    have hmap : (_root_.commutator ↥H).map H.subtype ≤ P := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := hz
      exact hker_le u (hle hu)
    rwa [Subgroup.map_subtype_commutator] at hmap
  have hcomap : K.comap ι ≤ H := by
    intro x hx
    change Φ x * x⁻¹ ∈ Z
    have hxfix : stp (ι x) = ι x := hKfix (ι x) hx
    have hxstp : ι (Φ x) = ι x := (hstp x).symm.trans hxfix
    have hmemker : Φ x * x⁻¹ ∈ ι.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxstp, mul_inv_cancel]
    exact hι hmemker
  have hKK : ⁅K, K⁆ ≤ P.map ι := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨x, rfl⟩ := hKle ha
    obtain ⟨y, rfl⟩ := hKle hb
    have hxK : x ∈ K.comap ι := by simpa using ha
    have hyK : y ∈ K.comap ι := by simpa using hb
    have hxyH : ⁅x, y⁆ ∈ P :=
      hHH (Subgroup.commutator_mono hcomap hcomap
        (Subgroup.commutator_mem_commutator hxK hyK))
    rw [← map_commutatorElement]
    exact Subgroup.mem_map_of_mem ι hxyH
  have hKcomm : K ≤ ⁅K, K⁆ := by
    intro k hk
    have hk' : (⟨k, hk⟩ : K) ∈ _root_.commutator ↥K := by
      rw [hKperf]
      trivial
    have hmem : k ∈ (_root_.commutator ↥K).map K.subtype :=
      Subgroup.mem_map_of_mem K.subtype hk'
    rwa [Subgroup.map_subtype_commutator] at hmem
  exact hKcomm.trans hKK

theorem ntpA2S_quasisimple_map {S G : Type*} [Group S] [Group G] (ι : S →* G)
    (hι : ι.ker ≤ Subgroup.center S) (P : Subgroup S) (hP : CFSG.IsQuasisimple ↥P) :
    CFSG.IsQuasisimple ↥(P.map ι) ∧
      Nonempty (↥P ⧸ Subgroup.center ↥P ≃* ↥(P.map ι) ⧸ Subgroup.center ↥(P.map ι)) := by
  refine ⟨CFSG.ComponentClassification.GSThmB.CF24.isQuasisimple_map ι hι hP,
    CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hP
      (ι.subgroupMap P) (ι.subgroupMap_surjective P) fun x hx => ?_⟩
  have h1 : ι (x : S) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  refine Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_
  exact Subgroup.mem_center_iff.mp (hι h1) (y : S)

theorem ntpA2S_statedClassicalModel_psl {X K : Type} [Group X] [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) :
    CFSG.Open.StatedClassicalModel X .PSL 3 2 f :=
  ⟨⟨Nat.prime_two, hf, by norm_num, by simp, by simp⟩,
    K, inferInstance, inferInstance, hK, ⟨e⟩⟩

theorem ntpA2S_statedClassicalModel_psu {X K : Type} [Group X] [Field K] [Finite K]
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (e : X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ f) K)) :
    CFSG.Open.StatedClassicalModel X .PSU 3 2 f := by
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  intro h
  have hpow : 2 ^ f = 2 := congrArg Prod.snd h
  have hle : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  rw [hpow] at hle
  norm_num at hle

end CFSG.StandardType.NTPlane
