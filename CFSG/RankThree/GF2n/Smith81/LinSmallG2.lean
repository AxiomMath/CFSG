module

public import CFSG.RankThree.GF2n.Smith81.LinStmt
public import CFSG.RankThree.GF2n.Smith81.InspLocal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables
import CFSG.RankThree.GF2n.Smith81.InspLinLocal
import CFSG.RankThree.GF2n.Smith81.Smith219Step1
import CFSG.RankThree.GF2n.Smith81.Lin26TwoModel
import CFSG.RankThree.GF2n.Smith81.Lin28CondTheta
import CFSG.RankThree.GF2n.Stroth80.Sec312Quot
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.ClassicalGroups.Linear.CentreGroupsDual
import CFSG.CGT.PushingUpLit.CGT6.SixFourE9
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld
open CFSG.SeitzReduction.F4Pilot (ordSL)

open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def KG2Concl {Y : Type} [Group Y] (D : Set Y) (f : ℕ) (d : Y) : Prop :=
  Nat.card (Subgroup.centralizer ({d} : Set Y)) ∣ (2 ^ f) ^ 5 * ordSL 2 (2 ^ f) ∧
    ∃ t ∈ Subgroup.centralizer ({d} : Set Y), orderOf t = 3 ∧
      ∃ x ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set Y)), x ∉ rootGroup D d ∧
        t * x * t⁻¹ * x⁻¹ ∈ rootGroup D d

@[expose] def KG2Statement : Prop :=
  ∀ (Y : Type) [Group Y] (D : Set Y) (f : ℕ), Hyp Y D → 2 ≤ f → LieModel Y .G2 0 2 f →
    (∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) → ∀ d ∈ D, KG2Concl D f d

private theorem eq_one_of_mem_statedSL_of_mulVec_eq_self {K : Type} [Field K] [CharP K 2]
    {A : GL (Fin 2) K} (hA : A ∈ StatedSL 2 K) (h3 : A ^ 3 = 1) {u : Fin 2 → K}
    (hu : u ≠ 0) (hAu : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u) : A = 1 := by
  let x : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨A, CFSG.Open.StatedAPI.det_of_mem_statedSL hA⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
  have hx1 : x = 1 := by
    by_contra hxne
    exact hu (CFSG.CGT.PushingUpLit.CGT6.fixed_vec_eq_zero_of_order_three hx3 hxne u hAu)
  exact Units.ext (congrArg Subtype.val hx1)

theorem exists_fixed_vec_of_comm_mem {K : Type} [Field K]
    {S V Z : Subgroup G} {φ : S →* GL (Fin 2) K}
    {act : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K}
    (hs : SectionAct K S V Z φ act) {s : S} {v : G} (hZV : Z ≤ V) (hv : v ∈ V)
    (hvZ : v ∉ Z) (hcomm : ⁅v, (s : G)⁆ ∈ Z) :
    ∃ u : Fin 2 → K, u ≠ 0 ∧ act (φ s) *ᵥ u = u := by
  classical
  obtain ⟨hSV, hN, ψ, hψ⟩ := hs
  letI := hN
  have hcomm' : ⁅(s : G), v⁆ ∈ Z := by
    rw [← commutatorElement_inv]
    exact Z.inv_mem hcomm
  have hW : (s : G) * v * (s : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hSV s.2) v).mp hv
  let vv : V := ⟨v, hv⟩
  let ww : V := ⟨(s : G) * v * (s : G)⁻¹, hW⟩
  have hw_eq : ww = (⟨⁅(s : G), v⁆, hZV hcomm'⟩ : V) * vv := by
    apply Subtype.ext
    show (s : G) * v * (s : G)⁻¹ = ⁅(s : G), v⁆ * v
    simp only [commutatorElement_def]
    group
  have hq : QuotientGroup.mk (s := Z.subgroupOf V) ww =
      QuotientGroup.mk (s := Z.subgroupOf V) vv := by
    rw [hw_eq, QuotientGroup.mk_mul]
    have hz : QuotientGroup.mk (s := Z.subgroupOf V)
        (⟨⁅(s : G), v⁆, hZV hcomm'⟩ : V) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hcomm')
    rw [hz, one_mul]
  let u : Fin 2 → K := Multiplicative.toAdd (ψ (QuotientGroup.mk (s := Z.subgroupOf V) vv))
  have hfix := hψ s vv ww rfl
  rw [hq] at hfix
  refine ⟨u, ?_, hfix.symm⟩
  intro h0
  have h1 : ψ (QuotientGroup.mk (s := Z.subgroupOf V) vv) = 1 := by
    apply Multiplicative.toAdd.injective
    simpa [u] using h0
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact hvZ h1

theorem phi_eq_one_of_comm_mem_nat {K : Type} [Field K] [CharP K 2]
    {S V Z : Subgroup G} {φ : S →* GL (Fin 2) K}
    (hs : SectionAct K S V Z φ (fun g => (g : Matrix (Fin 2) (Fin 2) K)))
    (hrange : φ.range = StatedSL 2 K) {s : S} {v : G} (hZV : Z ≤ V) (hv : v ∈ V)
    (hvZ : v ∉ Z) (hcomm : ⁅v, (s : G)⁆ ∈ Z) (h3 : s ^ 3 = 1) : φ s = 1 := by
  obtain ⟨u, hu, hAu⟩ := exists_fixed_vec_of_comm_mem hs hZV hv hvZ hcomm
  have hmem : φ s ∈ StatedSL 2 K := hrange ▸ MonoidHom.mem_range.mpr ⟨s, rfl⟩
  exact eq_one_of_mem_statedSL_of_mulVec_eq_self hmem (by rw [← map_pow, h3, map_one]) hu hAu

theorem phi_eq_one_of_comm_mem_dual {K : Type} [Field K] [CharP K 2]
    {S V Z : Subgroup G} {φ : S →* GL (Fin 2) K}
    (hs : SectionAct K S V Z φ
      (fun g => ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ))
    (hrange : φ.range = StatedSL 2 K) {s : S} {v : G} (hZV : Z ≤ V) (hv : v ∈ V)
    (hvZ : v ∉ Z) (hcomm : ⁅v, (s : G)⁆ ∈ Z) (h3 : s ^ 3 = 1) : φ s = 1 := by
  obtain ⟨u, hu, hAu⟩ := exists_fixed_vec_of_comm_mem hs hZV hv hvZ hcomm
  let A : GL (Fin 2) K := φ s
  let B : GL (Fin 2) K := Matrix.GeneralLinearGroup.inverseTranspose A
  have hBmat : (B : Matrix (Fin 2) (Fin 2) K) =
      ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ :=
    Matrix.GeneralLinearGroup.coe_inverseTranspose A
  have hBu : (B : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u := by
    simpa [A, hBmat] using hAu
  have hmem : A ∈ StatedSL 2 K := hrange ▸ MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hBmem : B ∈ StatedSL 2 K :=
    CFSG.ClassicalGroups.Linear.Model.inverseTranspose_mem_statedSL hmem
  have hA3 : A ^ 3 = 1 := by
    show φ s ^ 3 = 1
    rw [← map_pow, h3, map_one]
  have hB3 : B ^ 3 = 1 := by
    show Matrix.GeneralLinearGroup.inverseTranspose A ^ 3 = 1
    rw [← map_pow, hA3, map_one]
  have hB : B = 1 := eq_one_of_mem_statedSL_of_mulVec_eq_self hBmem hB3 hu hBu
  have hA1 : A = 1 := by
    calc A = Matrix.GeneralLinearGroup.inverseTranspose
          (Matrix.GeneralLinearGroup.inverseTranspose A) :=
        (Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose A).symm
      _ = Matrix.GeneralLinearGroup.inverseTranspose B := rfl
      _ = 1 := by rw [hB, map_one]
  simpa [A] using hA1

theorem pCoreOf_Lgen_le_Q [Finite G]
    {M Q Z B V₁ V₂ : Subgroup G} (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂)
    {f : ℕ} (hf : Nat.card Z = 2 ^ f) :
    pCoreOf 2 (Lgen M (LB M Q B)) ≤ Q := by
  classical
  set L := Lgen M (LB M Q B) with hLdef
  obtain ⟨K, hKfield, hKfin, hKcard, φ, hrange, hker, -⟩ := hS
  letI := hKfield
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rw [← Nat.card_eq_fintype_card, hKcard, hf])
  have hK4 : 4 ≤ Nat.card K := by rw [hKcard]; exact hc.hyp.q4
  let P : Subgroup L := pCore 2 L
  let φ' : L →* StatedSL 2 K :=
    φ.codRestrict (StatedSL 2 K) (fun s => hrange ▸ ⟨s, rfl⟩)
  have hφ'surj : Function.Surjective φ' := by
    intro y
    have hy : (y : GL (Fin 2) K) ∈ φ.range := by
      rw [hrange]
      exact y.2
    obtain ⟨s, hs⟩ := hy
    exact ⟨s, Subtype.ext (by simpa [φ'] using hs)⟩
  have hPnorm : (P.map φ').Normal := Subgroup.Normal.map pCore_normal φ' hφ'surj
  haveI := hPnorm
  have hP2 : IsPGroup 2 (P.map φ') :=
    IsPGroup.map (pCore_isPGroup (p := 2) (G := L)) φ'
  have hbot := normal_pGroup_statedSL_eq_bot (k := 2) (by norm_num) hK4
    (P.map φ') hP2
  have hPker : P ≤ φ.ker := by
    intro y hy
    have hmem : φ' y ∈ P.map φ' := Subgroup.mem_map_of_mem φ' hy
    rw [hbot, Subgroup.mem_bot] at hmem
    exact MonoidHom.mem_ker.mpr (by
      have := congrArg (fun z : StatedSL 2 K => (z : GL (Fin 2) K)) hmem
      simpa [φ'] using this)
  have hPsub : P ≤ Q.subgroupOf L := by
    rw [← hker]
    exact hPker
  have hQL : Q ≤ L :=
    (le_sup_left : Q ≤ Q ⊔ (QB B ⊓ M)).trans (le_Lgen_self M (LB M Q B))
  calc pCoreOf 2 L = P.map L.subtype := rfl
    _ ≤ Q := by
      simpa only [Subgroup.map_subgroupOf_eq_of_le hQL] using
        (Subgroup.map_mono (f := L.subtype) hPsub)

theorem centralizer_eq_and_pCore_le_Q [Finite G]
    {M Q Z B V₁ V₂ : Subgroup G} (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) {f : ℕ} (hf : Nat.card Z = 2 ^ f)
    (hdvd : Nat.card (Subgroup.centralizer ({selfIn z} : Set
      ↥(Subgroup.normalClosure ({z} : Set G)))) ∣ (2 ^ f) ^ 5 * ordSL 2 (2 ^ f)) :
    Subgroup.centralizer ({selfIn z} : Set ↥(Subgroup.normalClosure ({z} : Set G))) =
        (Lgen M (LB M Q B)).subgroupOf (Subgroup.normalClosure ({z} : Set G)) ∧
      (pCoreOf 2 (Subgroup.centralizer ({selfIn z} : Set
        ↥(Subgroup.normalClosure ({z} : Set G))))).map
          (Subgroup.normalClosure ({z} : Set G)).subtype ≤ Q := by
  classical
  set X := Subgroup.normalClosure ({z} : Set G) with hXdef
  set L := Lgen M (LB M Q B) with hLdef
  set C := Subgroup.centralizer ({selfIn z} : Set X) with hCdef
  have hLX : L ≤ X := Lgen_le_normalClosure hc hz hz1
  have hLC : L.subgroupOf X ≤ C := by
    intro y hy
    have hyH : (y : G) ∈ H0 M Z := Lgen_le_H0 hc hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hyH.2 z hz).symm
  have hQcard : Nat.card Q = (2 ^ f) ^ 5 := by
    have hw := hS.width hc.hyp
    rw [hw, hf]
  have hLcard : Nat.card L = (2 ^ f) ^ 5 * ordSL 2 (2 ^ f) := by
    rw [hLdef, card_Lgen_eq hS (by norm_num), hQcard, hf]
  have hcardLC : Nat.card (L.subgroupOf X) = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv
  have hdvdC : Nat.card C ∣ Nat.card (L.subgroupOf X) := by
    rw [hcardLC, hLcard]
    exact hdvd
  have hCle : Nat.card C ≤ Nat.card (L.subgroupOf X) := Nat.le_of_dvd Nat.card_pos hdvdC
  have hCeq : C = L.subgroupOf X := (Subgroup.eq_of_le_of_card_ge hLC hCle).symm
  refine ⟨hCeq, ?_⟩
  have hLpCore : pCoreOf 2 L ≤ Q := pCoreOf_Lgen_le_Q hc hS hf
  have hPmap : (pCoreOf 2 C).map X.subtype ≤ Q := by
    rw [hCeq]
    rw [show (pCoreOf 2 (L.subgroupOf X)).map X.subtype = pCoreOf 2 L from
      CFSG.ABGLocalTools.map_pCore_subgroupOf (p := 2) (M := L) (H := X) hLX]
    exact hLpCore
  exact hPmap

theorem _root_.CFSG.RankThree.GF2n.Smith81.LinSetup.mem_Z_of_orderOf_three [Finite G]
    {M Q Z B V₁ V₂ : Subgroup G} (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂) {t x : G}
    (ht : t ∈ Lgen M (LB M Q B)) (ht3 : orderOf t = 3) (hx : x ∈ Q)
    (htx : t * x * t⁻¹ * x⁻¹ ∈ Z) : x ∈ Z := by
  classical
  by_cases hxZ : x ∈ Z
  · exact hxZ
  · obtain ⟨R, -⟩ := exists_restModel_sl_two hc hS
    obtain ⟨-, -, -, -, -, -, hN₁, hN₂, -, -⟩ := hS.basic
    obtain ⟨K, hKfield, hKfin, hKcard, φ, hrange, hker, hZV₁, hV₁Q, hZV₂, hV₂Q, hint,
      hsup, hs₁, hs₂, hswap, hcent⟩ := hS
    letI := hKfield
    letI := hKfin
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := by
      obtain ⟨f, -, hf, -⟩ := hc.hyp.cp
      exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by
        rw [← Nat.card_eq_fintype_card, hKcard, hf])
    have htH : t ∈ H0 M Z := Lgen_le_H0 hc ht
    have hcomm : ⁅x, t⁆ ∈ Z := by
      have h := Z.inv_mem htx
      have h2 : ⁅x, t⁆ = (t * x * t⁻¹ * x⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rwa [h2]
    obtain ⟨a, ha, b, hb, rfl, hcommA, hcommB⟩ :=
      RestModel.exists_split R htH (hN₁ ht) (hN₂ ht) hx hcomm
    let s : Lgen M (LB M Q B) := ⟨t, ht⟩
    have hs3 : s ^ 3 = 1 := by
      apply Subtype.ext
      show t ^ 3 = 1
      simpa [ht3] using pow_orderOf_eq_one t
    have hcontra : φ s = 1 → False := by
      intro hφ1
      have htQ : t ∈ Q := by
        have hk : s ∈ φ.ker := MonoidHom.mem_ker.mpr hφ1
        rw [hker, Subgroup.mem_subgroupOf] at hk
        exact hk
      have ht1 : t = 1 := CFSG.RankThree.GF2n.Smith81.eq_one_of_mem_of_orderOf_dvd_odd
        (isPGroup_Q hc.hyp) htQ (m := 3) (by decide) (by rw [ht3])
      rw [ht1, orderOf_one] at ht3
      omega
    by_cases haZ : a ∈ Z
    · by_cases hbZ : b ∈ Z
      · exact (hxZ (Z.mul_mem haZ hbZ)).elim
      · exact (hcontra (phi_eq_one_of_comm_mem_dual hs₂ hrange hZV₂ hb hbZ hcommB hs3)).elim
    · exact (hcontra (phi_eq_one_of_comm_mem_nat hs₁ hrange hZV₁ ha haZ hcommA hs3)).elim

theorem not_lieModel_G2_lin [Finite G] (hKG2 : KG2Statement)
    {M Q Z B V₁ V₂ : Subgroup G} (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂)
    (h3 : Lin3Facts M Q Z B 2 V₁ V₂) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hHyp : Hyp ↥(Subgroup.normalClosure ({z} : Set G)) (classIn z)) {f : ℕ}
    (hf : Nat.card Z = 2 ^ f) (hf2 : 2 ≤ f)
    (hroot : ∀ d ∈ classIn z, Nat.card (rootGroup (classIn z) d) = 2 ^ f)
    (hL : LieModel ↥(Subgroup.normalClosure ({z} : Set G)) .G2 0 2 f) : False := by
  classical
  set X := Subgroup.normalClosure ({z} : Set G) with hXdef
  change Hyp ↥X (classIn z) at hHyp
  change LieModel ↥X .G2 0 2 f at hL
  obtain ⟨hdvd, t, htC, ht3, x, hxP, hxroot, hcomm⟩ :=
    hKG2 X (classIn z) f hHyp hf2 hL hroot (selfIn z) (IsConj.refl z)
  obtain ⟨hCeq, hPmap⟩ := centralizer_eq_and_pCore_le_Q hc hS hz hz1 hf hdvd
  have htL : (t : G) ∈ Lgen M (LB M Q B) := by
    have h1 : t ∈ (Lgen M (LB M Q B)).subgroupOf X := by
      rw [← hCeq]
      exact htC
    exact Subgroup.mem_subgroupOf.mp h1
  have ht3G : orderOf (t : G) = 3 := by
    rw [Subgroup.orderOf_coe, ht3]
  have hxQ : (x : G) ∈ Q := hPmap (Subgroup.mem_map_of_mem X.subtype hxP)
  have hrootZ : (rootGroup (classIn z) (selfIn z)).map X.subtype = Z := by
    rw [← CFSG.RankThree.GF2n.Smith81.rootGroup_image X.subtype X.subtype_injective
      (classIn z) (selfIn z), image_classIn z]
    simpa [CFSG.Timmesfeld.CorB.cls] using
      Smith219Step1.rootGroup_eq_Z_lin hc.hyp h3.h212 hz hz1
  have hcommZ : (t : G) * (x : G) * (t : G)⁻¹ * (x : G)⁻¹ ∈ Z := by
    have hmem : ((t * x * t⁻¹ * x⁻¹ : X) : G) ∈
        (rootGroup (classIn z) (selfIn z)).map X.subtype :=
      Subgroup.mem_map_of_mem X.subtype hcomm
    rw [hrootZ] at hmem
    simpa using hmem
  have hxZ : (x : G) ∈ Z := hS.mem_Z_of_orderOf_three hc htL ht3G hxQ hcommZ
  exact hxroot ((Subgroup.mem_map_iff_mem X.subtype_injective).mp (by rwa [hrootZ]))
