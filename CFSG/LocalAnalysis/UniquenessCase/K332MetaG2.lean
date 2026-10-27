module

public import CFSG.LocalAnalysis.UniquenessCase.K332MetaDefs
public import CFSG.LocalAnalysis.UniquenessCase.K332MetaExc
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332G2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Wreath
public import CFSG.HardMathSupport.Lang.Proving.FieldCubeRoots
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QSU33
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Adapters.RankThreeOutcomesReverse
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
public import CFSG.Blueprint.ChevalleyRootGroupsTriangular
public import CFSG.LieType.Chevalley.ExactG2FiniteOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47f
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QThree
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Unipotent
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Sylow
public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.Permutation.UnitaryThreeRecognition.Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open scoped commutatorElement MatrixGroups
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree (isPGroup_closure_cycle)
open CFSG.Assembly.RankThreeEven (projSU statedClassicalModel_of_projSU)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47 (Xa Xb Xr Xu Xv Xc Xa_mem Xb_mem Xr_mem Xu_mem Xv_mem Xc_mem
  Xa_add Xb_add Xr_add Xu_add Xa_zero Xb_zero Xr_zero Xu_zero
  rel_ab rel_ru mem_center_iff exists_mulEquiv_sylow_G2 charP_of_natCard_eq_pow)
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (exists_a2Hom_injective factorization_three_g2_eq_sl3)
open CFSG.AGLEmbedding.KFactProofs.G2Q (baseChangeAdjoint baseChangeAdjoint_injective)

def SylowCenterLeOmegaCommAt {X : Type} [Group X] (T : Sylow 3 X) : Prop :=
  ∀ x ∈ Subgroup.center ↥(T : Subgroup X), x ^ 3 = 1 →
    x ∈ ⁅CFSG.omega₁ (G := ↥(T : Subgroup X)) (p := 3),
      CFSG.omega₁ (G := ↥(T : Subgroup X)) (p := 3)⁆

theorem sylowCenterLeOmegaCommAt_of_mulEquiv {X Y : Type} [Group X] [Group Y]
    (T : Sylow 3 X) (S : Sylow 3 Y)
    (e : ↥(T : Subgroup X) ≃* ↥(S : Subgroup Y))
    (h : SylowCenterLeOmegaCommAt T) : SylowCenterLeOmegaCommAt S := by
  intro x hxc hx3
  let x' : ↥(T : Subgroup X) := e.symm x
  have hex' : e x' = x := e.apply_symm_apply x
  have hx'c : x' ∈ Subgroup.center ↥(T : Subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : e g * x = x * e g := Subgroup.mem_center_iff.mp hxc (e g)
    apply e.injective
    rw [map_mul, map_mul, hex']
    exact h1
  have hx'3 : x' ^ 3 = 1 := by
    dsimp [x']
    rw [← map_pow, show x ^ 3 = 1 from hx3, map_one]
  have hmem := h x' hx'c hx'3
  have hΩ : (CFSG.omega₁ (G := ↥(T : Subgroup X)) (p := 3)).map e.toMonoidHom ≤
      CFSG.omega₁ (G := ↥(S : Subgroup Y)) (p := 3) :=
    CFSG.RankThree.Coprime.map_omega₁_le e.toMonoidHom
  have hle : (⁅CFSG.omega₁ (G := ↥(T : Subgroup X)) (p := 3),
      CFSG.omega₁ (G := ↥(T : Subgroup X)) (p := 3)⁆).map e.toMonoidHom ≤
      ⁅CFSG.omega₁ (G := ↥(S : Subgroup Y)) (p := 3),
        CFSG.omega₁ (G := ↥(S : Subgroup Y)) (p := 3)⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hΩ hΩ
  exact hle ⟨x', hmem, hex'⟩

theorem sylowCenterLeOmegaComm_of_sylow {X : Type} [Group X] [Finite X] (T₀ : Sylow 3 X)
    (h : SylowCenterLeOmegaCommAt T₀) : SylowCenterLeOmegaComm X :=
  fun T => sylowCenterLeOmegaCommAt_of_mulEquiv T₀ T (Sylow.equiv T₀ T) h

theorem K332_sylowOmegaCLC_of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : SylowCenterLeOmegaComm A) : SylowCenterLeOmegaComm B :=
  sylowCenterLeOmegaComm_of_mulEquiv e h

theorem K332_sylowOmegaCLC_up {A G : Type} [Group A] [Group G] [Finite A] [Finite G]
    (ι : A →* G) (hι : Function.Injective ι)
    (hcard : (Nat.card G).factorization 3 = (Nat.card A).factorization 3)
    (hA : SylowCenterLeOmegaComm A) : SylowCenterLeOmegaComm G := by
  intro Q
  obtain ⟨P⟩ : Nonempty (Sylow 3 A) := inferInstance
  obtain ⟨Q', ⟨e⟩⟩ := K332_exists_sylow_mulEquiv ι hι hcard P
  exact sylowCenterLeOmegaCommAt_of_mulEquiv Q' Q (Sylow.equiv Q' Q)
    (sylowCenterLeOmegaCommAt_of_mulEquiv P Q' e (hA P))

theorem K332_sylowOmegaCLC_down {A G : Type} [Group A] [Group G] [Finite A] [Finite G]
    (ι : A →* G) (hι : Function.Injective ι)
    (hcard : (Nat.card G).factorization 3 = (Nat.card A).factorization 3)
    (hG : SylowCenterLeOmegaComm G) : SylowCenterLeOmegaComm A := by
  intro P
  obtain ⟨Q, ⟨e⟩⟩ := K332_exists_sylow_mulEquiv ι hι hcard P
  exact sylowCenterLeOmegaCommAt_of_mulEquiv Q P e.symm (hG Q)

theorem sylowCenterLeOmegaCommAt_of_mulEquiv_of_group {X G : Type} [Group X] [Group G]
    (T : Sylow 3 X) (e : ↥(T : Subgroup X) ≃* G)
    (h : ∀ x ∈ Subgroup.center G, x ^ 3 = 1 →
      x ∈ ⁅CFSG.omega₁ (G := G) (p := 3), CFSG.omega₁ (G := G) (p := 3)⁆) :
    SylowCenterLeOmegaCommAt T := by
  intro x hxc hx3
  have hxG : e x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := e.surjective y
    simpa using congrArg e (Subgroup.mem_center_iff.mp hxc g)
  have hxG3 : (e x) ^ 3 = 1 := by
    rw [← map_pow, show x ^ 3 = 1 from hx3, map_one]
  have hmem := h (e x) hxG hxG3
  have hΩ : (CFSG.omega₁ (G := G) (p := 3)).map e.symm.toMonoidHom ≤
      CFSG.omega₁ (G := ↥(T : Subgroup X)) (p := 3) :=
    CFSG.RankThree.Coprime.map_omega₁_le e.symm.toMonoidHom
  have hle : (⁅CFSG.omega₁ (G := G) (p := 3),
      CFSG.omega₁ (G := G) (p := 3)⁆).map e.symm.toMonoidHom ≤
      ⁅CFSG.omega₁ (G := ↥(T : Subgroup X)) (p := 3),
        CFSG.omega₁ (G := ↥(T : Subgroup X)) (p := 3)⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hΩ hΩ
  exact hle ⟨e x, hmem, by simp⟩

theorem K332_sylowOmegaCLC_of_cycle {S : Type} [Group S] [Finite S] (D π c : S)
    (hc : c ∈ Subgroup.center S) (hD : D ^ 3 = 1) (hπ : π ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (hrel : π * D * π⁻¹ = c * D)
    (hscal : ∀ x : S, x * D = D * x → x * π = π * x → ∃ i : ℕ, x = c ^ i) :
    SylowCenterLeOmegaComm S := by
  have hcg : ∀ g : S, g * c = c * g := Subgroup.mem_center_iff.mp hc
  have hcg2 : ∀ g : S, g * c ^ 2 = c ^ 2 * g := fun g =>
    Subgroup.mem_center_iff.mp ((Subgroup.center S).pow_mem hc 2) g
  have hcC : ∀ g : S, Commute c g := fun g => (hcg g).symm
  have hcC2 : ∀ g : S, Commute (c ^ 2) g := fun g => (hcg2 g).symm
  have hconj_c : π * c * π⁻¹ = c := by rw [hcg π, mul_assoc, mul_inv_cancel, mul_one]
  have hconj_c2 : π * c ^ 2 * π⁻¹ = c ^ 2 := by
    rw [hcg2 π, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : π * (c * D) * π⁻¹ = c ^ 2 * D := by
    calc π * (c * D) * π⁻¹ = (π * c * π⁻¹) * (π * D * π⁻¹) := by group
      _ = c * (c * D) := by rw [hconj_c, hrel]
      _ = c ^ 2 * D := by rw [pow_two, mul_assoc]
  have h3 : π * (c ^ 2 * D) * π⁻¹ = D := by
    calc π * (c ^ 2 * D) * π⁻¹ = (π * c ^ 2 * π⁻¹) * (π * D * π⁻¹) := by group
      _ = c ^ 2 * (c * D) := by rw [hconj_c2, hrel]
      _ = c ^ 3 * D := by group
      _ = D := by rw [hc3, one_mul]
  have huv : D * (c * D) = (c * D) * D := by rw [← mul_assoc, hcg D]
  have huw : D * (c ^ 2 * D) = (c ^ 2 * D) * D := by rw [← mul_assoc, hcg2 D]
  have hvw : (c * D) * (c ^ 2 * D) = (c ^ 2 * D) * (c * D) := by
    have h1 : Commute (c * D) (c ^ 2 * D) :=
      (hcC (c ^ 2 * D)).mul_left (((hcC2 D).symm).mul_right (Commute.refl D))
    exact h1.eq
  have hv3 : (c * D) ^ 3 = 1 := by rw [(hcC D).mul_pow, hc3, hD, one_mul]
  have hc23 : (c ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hc3, one_pow]
  have hw3 : (c ^ 2 * D) ^ 3 = 1 := by rw [(hcC2 D).mul_pow, hc23, hD, one_mul]
  have hQ := isPGroup_closure_cycle huv huw hvw hD hv3 hw3 hπ hrel h2 h3
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  have hDP : D ∈ (P : Subgroup S) := hP (Subgroup.subset_closure (by simp))
  have hvP : c * D ∈ (P : Subgroup S) := hP (Subgroup.subset_closure (by simp))
  have hπP : π ∈ (P : Subgroup S) := hP (Subgroup.subset_closure (by simp))
  have hcP : c ∈ (P : Subgroup S) := by
    have := mul_mem hvP (inv_mem hDP)
    simpa using this
  refine sylowCenterLeOmegaComm_of_sylow P ?_
  intro x hxc _
  have hxD : (x : S) * D = D * x :=
    (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hxc (⟨D, hDP⟩ : ↥(P : Subgroup S)))).symm
  have hxπ : (x : S) * π = π * x :=
    (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hxc (⟨π, hπP⟩ : ↥(P : Subgroup S)))).symm
  obtain ⟨i, hi⟩ := hscal x hxD hxπ
  have hπΩ : (⟨π, hπP⟩ : ↥(P : Subgroup S)) ∈
      CFSG.omega₁ (G := ↥(P : Subgroup S)) (p := 3) :=
    Subgroup.subset_closure (by simpa using hπ)
  have hDΩ : (⟨D, hDP⟩ : ↥(P : Subgroup S)) ∈
      CFSG.omega₁ (G := ↥(P : Subgroup S)) (p := 3) :=
    Subgroup.subset_closure (by simpa using hD)
  have hcc : (⟨c, hcP⟩ : ↥(P : Subgroup S)) ∈
      ⁅CFSG.omega₁ (G := ↥(P : Subgroup S)) (p := 3),
        CFSG.omega₁ (G := ↥(P : Subgroup S)) (p := 3)⁆ := by
    have h := Subgroup.commutator_mem_commutator hπΩ hDΩ
    have e : (⁅(⟨π, hπP⟩ : ↥(P : Subgroup S)),
        (⟨D, hDP⟩ : ↥(P : Subgroup S))⁆ : ↥(P : Subgroup S)) =
        (⟨c, hcP⟩ : ↥(P : Subgroup S)) := by
      apply Subtype.ext
      show π * D * π⁻¹ * D⁻¹ = c
      rw [hrel, mul_inv_cancel_right]
    rwa [e] at h
  have hx : x = (⟨c, hcP⟩ : ↥(P : Subgroup S)) ^ i := Subtype.ext (by rw [hi]; rfl)
  rw [hx]
  exact Subgroup.pow_mem _ hcc i

section SL3

variable {K : Type} [Field K]

theorem K332_sylowOmegaCLC_SL3 [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    SylowCenterLeOmegaComm (Matrix.SpecialLinearGroup (Fin 3) K) := by
  obtain ⟨ζ, hζ1, hζ3⟩ :=
    CFSG.HardMathSupport.Lang.Proving.exists_ne_one_pow_three_of_three_dvd K h3
  have hω3 : (ζ : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  have hω1 : (ζ : K) ≠ 1 := fun h => hζ1 (Units.ext h)
  obtain ⟨D, π, c, hc, hD, hπ, hc3, hrel, hscal⟩ := sl3_exists_cycle_data hω3 hω1
  exact K332_sylowOmegaCLC_of_cycle D π c hc hD hπ hc3 hrel hscal

end SL3

theorem sylowCenterLeOmegaComm_projSU_three_three (X : Type) [Group X] [Finite X]
    (e : X ≃* projSU 3 3 1) : SylowCenterLeOmegaComm X := by
  have hadm : StatedLieAdmissible .PSU 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hcard : Nat.card X = 6048 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three
      (statedClassicalModel_of_projSU hadm e)
  obtain ⟨x, y, hx3, hy3, hxy, hP⟩ :=
    CFSG.AGLEmbedding.KFactProofs.G2Q.exists_pair_projSU33 e
  obtain ⟨T, hT⟩ := hP.exists_le_sylow
  have hxT : x ∈ (T : Subgroup X) := hT (Subgroup.subset_closure (by simp))
  have hyT : y ∈ (T : Subgroup X) := hT (Subgroup.subset_closure (by simp))
  have hTcard : Nat.card ↥(T : Subgroup X) = 3 ^ 3 := by
    rw [Sylow.card_eq_multiplicity, hcard, K332_factorization_three_card_psu_three_three]
  let P : Subgroup X := Subgroup.closure ({x, y} : Set X)
  have hPp : IsPGroup 3 P := hP
  have hxP : x ∈ P := Subgroup.subset_closure (by simp)
  have hyP : y ∈ P := Subgroup.subset_closure (by simp)
  have hncP : ¬ IsMulCommutative ↥P := by
    intro hc
    exact hxy (congrArg Subtype.val (hc.is_comm.comm ⟨x, hxP⟩ ⟨y, hyP⟩))
  have hPcard : Nat.card P = 3 ^ 3 := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    have hn_le : n ≤ 3 := by
      have hle : 3 ^ n ≤ 3 ^ 3 := by
        rw [← hn]
        calc Nat.card P ≤ Nat.card (T : Subgroup X) := Subgroup.card_le_of_le hT
          _ = 3 ^ 3 := hTcard
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
    have hn_ge : 3 ≤ n := by
      by_contra h
      have hn_le2 : n ≤ 2 := by omega
      interval_cases n
      · have hcard1 : Nat.card P = 1 := by simpa using hn
        have hbot : P = ⊥ := (Subgroup.eq_bot_iff_card P).mpr hcard1
        have hx1 : x = 1 := by
          have : x ∈ (⊥ : Subgroup X) := by rw [← hbot]; exact hxP
          simpa using this
        exact hxy (by rw [hx1]; simp)
      · have hcard3 : Nat.card P = 3 := by simpa using hn
        haveI : IsCyclic ↥P := isCyclic_of_prime_card hcard3
        exact hncP (inferInstance : IsMulCommutative ↥P)
      · have hcard9 : Nat.card P = 3 ^ 2 := by simpa using hn
        exact hncP (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard9)
    have hn3 : n = 3 := le_antisymm hn_le hn_ge
    rw [hn, hn3]
  have hPT : P = (T : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge hT (by rw [hTcard, hPcard])
  have hxT3 : (⟨x, hxT⟩ : ↥(T : Subgroup X)) ^ 3 = 1 := Subtype.ext hx3
  have hyT3 : (⟨y, hyT⟩ : ↥(T : Subgroup X)) ^ 3 = 1 := Subtype.ext hy3
  have hTcl : Subgroup.closure ({⟨x, hxT⟩, ⟨y, hyT⟩} : Set ↥(T : Subgroup X)) = ⊤ := by
    apply Subgroup.map_injective (f := (T : Subgroup X).subtype)
      (T : Subgroup X).subtype_injective
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    have himage : (T : Subgroup X).subtype ''
        ({⟨x, hxT⟩, ⟨y, hyT⟩} : Set ↥(T : Subgroup X)) = ({x, y} : Set X) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        rcases hw with rfl | rfl
        · exact Set.mem_insert_iff.mpr (Or.inl rfl)
        · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
      · intro hz
        rcases hz with hzx | hzy
        · subst z
          exact ⟨⟨x, hxT⟩, Set.mem_insert_iff.mpr (Or.inl rfl), rfl⟩
        · subst z
          exact ⟨⟨y, hyT⟩, Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)),
            rfl⟩
    rw [himage, ← hPT]
  have hΩT : CFSG.omega₁ (G := ↥(T : Subgroup X)) (p := 3) = ⊤ := by
    rw [eq_top_iff, ← hTcl]
    refine (Subgroup.closure_le (K := CFSG.omega₁ (G := ↥(T : Subgroup X)) (p := 3))).2 ?_
    intro w hw
    rcases hw with hwx | hwy
    · subst w
      exact Subgroup.subset_closure (by simpa using hxT3)
    · subst w
      exact Subgroup.subset_closure (by simpa using hyT3)
  refine sylowCenterLeOmegaComm_of_sylow T ?_
  intro z hz hz3
  have hnc : ¬ IsMulCommutative ↥(T : Subgroup X) := fun hc =>
    hxy (congrArg Subtype.val (hc.is_comm.comm (⟨x, hxT⟩ : ↥(T : Subgroup X))
      ⟨y, hyT⟩))
  have hZ : Nat.card (Subgroup.center ↥(T : Subgroup X)) = 3 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.card_center_of_nonabelian_card_p_cube
      hTcard hnc
  have hcomm := center_le_commutator_of_card_center_eq_prime T.isPGroup' hnc hZ hz
  simpa [hΩT, commutator_def] using hcomm

section Certified

theorem K332_centreLeOmega_posUnipotent {F : Type} [Field F] [Finite F] (h3 : (3 : F) = 0) :
    ∀ z ∈ Subgroup.center ↥(posUnipotent .G2 F), z ^ 3 = 1 →
      z ∈ ⁅CFSG.omega₁ (G := ↥(posUnipotent .G2 F)) (p := 3),
        CFSG.omega₁ (G := ↥(posUnipotent .G2 F)) (p := 3)⁆ := by
  have hsum : ∀ c : F, c + c + c = 0 := by
    intro c
    rw [show c + c + c = (3 : F) * c by ring, h3, zero_mul]
  have pow_three_of_add : ∀ (X : F → ↥(posUnipotent .G2 F)),
      (∀ x y, X (x + y) = X x * X y) → X 0 = 1 → ∀ c, X c ^ 3 = 1 := by
    intro X hadd hzero c
    calc X c ^ 3 = X c * X c * X c := by rw [pow_succ, pow_two]
      _ = X (c + c) * X c := by rw [← hadd]
      _ = X ((c + c) + c) := by rw [← hadd]
      _ = X 0 := by rw [hsum]
      _ = 1 := hzero
  have hXr3 : ∀ c, (⟨Xr c, Xr_mem c⟩ : ↥(posUnipotent .G2 F)) ^ 3 = 1 :=
    pow_three_of_add (fun c => ⟨Xr c, Xr_mem c⟩) (fun x y => Subtype.ext (Xr_add x y))
      (Subtype.ext Xr_zero)
  have hXu3 : ∀ c, (⟨Xu c, Xu_mem c⟩ : ↥(posUnipotent .G2 F)) ^ 3 = 1 :=
    pow_three_of_add (fun c => ⟨Xu c, Xu_mem c⟩) (fun x y => Subtype.ext (Xu_add x y))
      (Subtype.ext Xu_zero)
  have hXa3 : ∀ c, (⟨Xa c, Xa_mem c⟩ : ↥(posUnipotent .G2 F)) ^ 3 = 1 :=
    pow_three_of_add (fun c => ⟨Xa c, Xa_mem c⟩) (fun x y => Subtype.ext (Xa_add x y))
      (Subtype.ext Xa_zero)
  have hXb3 : ∀ c, (⟨Xb c, Xb_mem c⟩ : ↥(posUnipotent .G2 F)) ^ 3 = 1 :=
    pow_three_of_add (fun c => ⟨Xb c, Xb_mem c⟩) (fun x y => Subtype.ext (Xb_add x y))
      (Subtype.ext Xb_zero)
  have mem_omega_of_pow_three : ∀ (X : F → ↥(posUnipotent .G2 F)),
      (∀ c, X c ^ 3 = 1) → ∀ c, X c ∈ CFSG.omega₁ (G := ↥(posUnipotent .G2 F)) (p := 3) := by
    intro X h c
    rw [CFSG.omega₁, CFSG.omega]
    exact Subgroup.subset_closure (by simpa using h c)
  intro z hz _
  obtain ⟨s, t, hst⟩ := (mem_center_iff h3 z).1 hz
  obtain ⟨e, he, hru⟩ := rel_ru (K := F) h3
  obtain ⟨e', he', hab⟩ := rel_ab (K := F)
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have hee' : e' * e' = 1 := by rcases he' with rfl | rfl <;> norm_num
  have hv : (⟨Xv s, Xv_mem s⟩ : ↥(posUnipotent .G2 F)) ∈
      ⁅CFSG.omega₁ (G := ↥(posUnipotent .G2 F)) (p := 3),
        CFSG.omega₁ (G := ↥(posUnipotent .G2 F)) (p := 3)⁆ := by
    have h := Subgroup.commutator_mem_commutator
      (mem_omega_of_pow_three _ hXr3 1)
      (mem_omega_of_pow_three _ hXu3 (e * s))
    have heq : (⁅(⟨Xr 1, Xr_mem 1⟩ : ↥(posUnipotent .G2 F)),
        (⟨Xu (e * s), Xu_mem _⟩ : ↥(posUnipotent .G2 F))⁆ :
          ↥(posUnipotent .G2 F)) = ⟨Xv s, Xv_mem s⟩ := by
      apply Subtype.ext
      show ⁅Xr (1 : F), Xu (e * s)⁆ = Xv s
      rw [hru, show e * (1 * (e * s)) = s by linear_combination s * hee]
    rwa [heq] at h
  have hc : (⟨Xc t, Xc_mem t⟩ : ↥(posUnipotent .G2 F)) ∈
      ⁅CFSG.omega₁ (G := ↥(posUnipotent .G2 F)) (p := 3),
        CFSG.omega₁ (G := ↥(posUnipotent .G2 F)) (p := 3)⁆ := by
    have h := Subgroup.commutator_mem_commutator
      (mem_omega_of_pow_three _ hXa3 (e' * t))
      (mem_omega_of_pow_three _ hXb3 1)
    have heq : (⁅(⟨Xa (e' * t), Xa_mem _⟩ : ↥(posUnipotent .G2 F)),
        (⟨Xb 1, Xb_mem 1⟩ : ↥(posUnipotent .G2 F))⁆ :
          ↥(posUnipotent .G2 F)) = ⟨Xc t, Xc_mem t⟩ := by
      apply Subtype.ext
      show ⁅Xa (e' * t), Xb (1 : F)⁆ = Xc t
      rw [hab, show e' * (e' * t * 1) = t by linear_combination t * hee']
    rwa [heq] at h
  have hz' : z = ⟨Xv s, Xv_mem s⟩ * ⟨Xc t, Xc_mem t⟩ := Subtype.ext hst
  rw [hz']
  exact mul_mem hv hc

theorem K332_sylowOmegaCLC_adjointG2_of_three_dvd_sub_one (K : Type) [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) (hq : 2 ≤ Nat.card K) :
    SylowCenterLeOmegaComm ↥(adjointGroup .G2 K) := by
  obtain ⟨ι, hι⟩ : ∃ ι : Matrix.SpecialLinearGroup (Fin 3) K →* ↥(adjointGroup .G2 K),
      Function.Injective ι := by
    obtain ⟨ι, hι, -⟩ := exists_a2Hom_injective (K := K)
    exact ⟨ι, hι⟩
  obtain ⟨-, hC, -⟩ := exact_G2_finite_order K (q := Nat.card K) rfl
  have hS : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
      show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  refine K332_sylowOmegaCLC_up ι hι ?_ (K332_sylowOmegaCLC_SL3 h3)
  rw [hC, hS]
  exact factorization_three_g2_eq_sl3 h3 hq

theorem K332_sylowOmegaCLC_adjointG2_of_three_dvd_add_one (K : Type) [Field K] [Finite K]
    (h1 : 3 ∣ Nat.card K + 1) : SylowCenterLeOmegaComm ↥(adjointGroup .G2 K) := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨K₂, _, _, _, hK₂⟩ : ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (_ : Algebra K K₂),
      Nat.card K₂ = Nat.card K ^ 2 := by
    have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
    haveI : Fact (ringChar K).Prime := ⟨hp⟩
    exact ⟨FiniteField.Extension K (ringChar K) 2, inferInstance, inferInstance, inferInstance,
      FiniteField.natCard_extension K (ringChar K) 2⟩
  have h₂ : 3 ∣ Nat.card K₂ - 1 := by
    rw [hK₂, show Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) by
      rw [← Nat.sq_sub_sq, one_pow]]
    exact h1.mul_right _
  have hq₂ : 2 ≤ Nat.card K₂ := Finite.one_lt_card
  obtain ⟨-, hN, -⟩ := exact_G2_finite_order K (q := Nat.card K) rfl
  obtain ⟨-, hN₂, -⟩ := exact_G2_finite_order K₂ hK₂
  refine K332_sylowOmegaCLC_down (baseChangeAdjoint (algebraMap K K₂))
    (baseChangeAdjoint_injective _) ?_ (K332_sylowOmegaCLC_adjointG2_of_three_dvd_sub_one K₂ h₂ hq₂)
  rw [hN, hN₂]
  exact K332_factorization_three_g2_sq hq h1

theorem sylowCenterLeOmegaComm_g2_char3 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : UntwistedChevalleyModel X .G2 (3 ^ n)) : SylowCenterLeOmegaComm X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro T
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_sylow_G2 Nat.prime_three h T
  have hchar : CharP F 3 := charP_of_natCard_eq_pow Nat.prime_three hF
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  exact sylowCenterLeOmegaCommAt_of_mulEquiv_of_group T e (K332_centreLeOmega_posUnipotent h3)

theorem sylowCenterLeOmegaComm_g2_of_three_dvd_sub_one {X : Type} [Group X] [Finite X] {q : ℕ}
    (h : UntwistedChevalleyModel X .G2 q) (h3 : 3 ∣ q - 1) (hq : 3 ≤ q) :
    SylowCenterLeOmegaComm X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := K332_exists_equiv_adjointG2 h
  subst hK
  exact K332_sylowOmegaCLC_of_mulEquiv e.symm
    (K332_sylowOmegaCLC_adjointG2_of_three_dvd_sub_one K h3 (by omega))

theorem g2SylowMinusOmega :
    ∀ (X : Type) [Group X] [Finite X] (q : ℕ), UntwistedChevalleyModel X .G2 q → 3 ∣ q + 1 →
      SylowCenterLeOmegaComm X := by
  intro X _ _ q h h3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := K332_exists_equiv_adjointG2 h
  subst hK
  exact K332_sylowOmegaCLC_of_mulEquiv e.symm
    (K332_sylowOmegaCLC_adjointG2_of_three_dvd_add_one K h3)

theorem sylowCenterLeOmegaComm_of_isoGTwoPrime :
    ∀ (X : Type) [Group X] [Finite X], CFSG.RankThree.PartTwo.Sec4.IsoGTwoPrime X →
      SylowCenterLeOmegaComm X := by
  intro X _ _ h
  rcases h with ⟨p, f, ⟨hp, -, -, h3q⟩, hmodel⟩ | ⟨⟨e⟩⟩
  · by_cases hp3 : p = 3
    · subst hp3
      exact sylowCenterLeOmegaComm_g2_char3 hmodel
    · have hnd : ¬ 3 ∣ p ^ f := fun h =>
        hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
          (Nat.prime_three.dvd_of_dvd_pow h)).symm
      generalize p ^ f = q at hnd h3q hmodel
      by_cases hmod : q % 3 = 1
      · exact sylowCenterLeOmegaComm_g2_of_three_dvd_sub_one hmodel (by omega) h3q
      · exact g2SylowMinusOmega X q hmodel (by omega)
  · exact sylowCenterLeOmegaComm_projSU_three_three X e

theorem k332ExclusionMeta_holds : K332ExclusionMeta :=
  k332ExclusionMeta_of_sylowG2 sylowCenterLeOmegaComm_of_isoGTwoPrime

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
