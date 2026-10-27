module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNm
public import CFSG.Quasithin.EmptyFaithful.S1565L6
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch7Setup
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
  CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

theorem asf_V_basic {G : Type} [Group G] [Finite G] {T L I : Subgroup G} (hmod : StmtFSUModule)
    (hyp : Hyp7_0_2 G T L I) :
    fsuV T I ≤ T ∧ T ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
    (∀ x ∈ fsuV T I, ∀ y ∈ fsuV T I, x * y = y * x) ∧ (∀ v ∈ fsuV T I, v * v = 1) := by
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  refine ⟨fsuV_le_T hyp.fsu hV hN, le_sup_right.trans hN, ?_, ?_⟩
  · intro x hx y hy
    have := hV.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  · intro v hv
    have := hV.2 v hv
    simpa [pow_two] using this

theorem asf_card_eq_relIndex_mul {G : Type} [Group G] {A B : Subgroup G} (h : A ≤ B) :
    Nat.card ↥B = A.relIndex B * Nat.card ↥A := by
  have h1 := Subgroup.card_mul_index (A.subgroupOf B)
  have h2 : Nat.card ↥(A.subgroupOf B) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rw [h2] at h1
  rw [← h1, mul_comm]
  rfl

theorem asf_card_of_mQuot_eq_four {G : Type} [Group G] [Finite G] {B₁ U V : Subgroup G}
    (hUB : U ≤ B₁) (hBV : B₁ ≤ V) (hV : IsPGroup 2 ↥V) (h : mQuot B₁ U = 4) :
    Nat.card ↥B₁ = 16 * Nat.card ↥U := by
  have hP : IsPGroup 2 ↥B₁ := hV.to_le hBV
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hcard := asf_card_eq_relIndex_mul hUB
  have hdvd : U.relIndex B₁ ∣ 2 ^ n := by
    rw [← hn, hcard]
    exact dvd_mul_right _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have : mQuot B₁ U = j := by
    unfold mQuot
    rw [hj, padicValNat.prime_pow]
  have hj4 : j = 4 := by omega
  rw [hcard, hj, hj4]
  norm_num

theorem nonab_of_simple_perfect {K Ks : Type} [Group K] [Group Ks] (hperf : commutator K = ⊤)
    (hs : IsSimpleGroup Ks) (ψ : K →* Ks) (hψ : Function.Surjective ψ) :
    ∃ a b : Ks, a * b ≠ b * a := by
  by_contra hcon
  have hall : ∀ a b : Ks, a * b = b * a := fun a b => by
    by_contra hab
    exact hcon ⟨a, b, hab⟩
  have key : (commutator K).map ψ = commutator Ks := by
    rw [commutator_def K, commutator_def Ks, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective ψ hψ]
  have h1 : commutator Ks = ⊤ := by
    rw [← key, hperf]
    exact Subgroup.map_top_of_surjective ψ hψ
  have h2 : commutator Ks = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr ?_
    intro a _ b _
    simp [commutatorElement_def, hall a b]
  rw [h1] at h2
  haveI := hs
  exact (top_ne_bot (α := Subgroup Ks)) h2

theorem star_facts_of_cases {G : Type} [Group G] [Finite G] {H T M K : Subgroup G}
    (hcases : E2.E22CasesNoN H T M K) (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)) :
    IsSimpleGroup ↥(E2.star M H K) ∧ (∃ a b : ↥(E2.star M H K), a * b ≠ b * a) ∧
      Group.IsSolvable ↥(K ⊓ kerIn M H) := by
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hperf : commutator ↥K = ⊤ := commutator_top_of_perfect (perfect_of_mem_cComp hKc)
  unfold E2.E22CasesNoN at hcases
  simp only at hcases
  rcases hcases with ⟨hJ, t, htT, hne, hMeq, hcase⟩ | ⟨hTK, hJ, hcase⟩
  ·
    have hsolv : Group.IsSolvable ↥(K ⊓ kerIn M H) := solvable_kerIn_case1 hJ
    have hs : IsSimpleGroup ↥(E2.star M H K) := by
      rcases hcase with ⟨n, hn2, hPSLSz, hBor⟩ | ⟨p, hp, hp8, hL, hMK, h8⟩
      · exact CFSG.Quasithin.isSimpleGroup_of_psl2_or_sz hPSLSz
      · exact CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hL
    exact ⟨hs, nonab_of_simple_perfect hperf hs (starHom M H K hKH)
      (starHom_surjective M H K hKH), hsolv⟩
  ·
    exact star_facts_case2 hKc hHK hTK hq hJ

end CFSG.Quasithin.H13.L829N
