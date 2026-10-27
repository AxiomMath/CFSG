module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwentyNine
import CFSG.GroupTheory.ChiefSectionPGroup
import CFSG.GroupTheory.CommutatorModSection
import CFSG.LinearAlgebra.SL2CharTwoInvolution
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineDecomp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyNineAbFinal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.GroupTheory CFSG.LinearAlgebra
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

private structure ChiefSect {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) where
  X : Subgroup G
  Y : Subgroup G
  hVY : c.V ≤ Y
  hYX : Y ≤ X
  hXT : X ≤ D.T
  hXP : X ≤ CFSG.Open.pCoreOf 2 c.L
  hNX : c.L ⊔ D.T ≤ Subgroup.normalizer (X : Set G)
  hNY : c.L ⊔ D.T ≤ Subgroup.normalizer (Y : Set G)
  hsq : ∀ x ∈ X, x ^ 2 ∈ Y
  hXX : ⁅X, X⁆ ≤ Y
  hQact : ∀ s ∈ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T), ∀ x ∈ X,
    s * x * s⁻¹ * x⁻¹ ∈ Y
  hK0act : ∀ s ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G), ∀ x ∈ X,
    s * x * s⁻¹ * x⁻¹ ∈ Y
  hnot : ¬ ⁅X, c.L⁆ ≤ Y

private theorem not_commutator_pCoreOf_le_V (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h205 : S20_5 D) (h640 : UC6.R6_40_1 D)
    (h1930 : H1930 D) (c : Ctx23L D Ch) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) :
    ¬ ⁅CFSG.Open.pCoreOf 2 c.L, c.L⁆ ≤ c.V := by
  intro h
  have hK0 := Ctx23L.inf_centralizer_V_le_pCoreOf_L D Ch h4 h23 h1930 c
  have hU : ∀ x ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G), ∀ l ∈ c.L, ⁅x, l⁆ ∈ c.V :=
    fun x hx l hl => Subgroup.commutator_le.mp h x (hK0 hx) l hl
  have hX := Ctx23L.inClassX_L D Ch h4 h23 h1930 (by omega) c hU
  exact Ctx23L.false_of_inClassX_L D Ch h205 h640 h1930 c hX

private theorem normalizer_pCoreOf {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) :
    c.L ⊔ D.T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) ∧
      c.L ⊔ D.T ≤
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) : Set G) := by
  have hnorm : ∀ n ∈ c.L ⊔ D.T, ∀ k ∈ c.L, n * k * n⁻¹ ∈ c.L := by
    intro n hn k hk
    have hLTnorm : c.L ⊔ D.T ≤ Subgroup.normalizer (c.L : Set G) :=
      sup_le (Subgroup.le_normalizer (H := c.L)) c.hL.1.1
    exact (Subgroup.mem_normalizer_iff.mp (hLTnorm hn) k).mp hk
  constructor
  · rw [Subgroup.le_normalizer_iff]
    intro n hn x hx
    exact uc22main1_conj_mem_pCoreOf (K := c.L) hnorm hn hx
  · rw [Subgroup.le_normalizer_iff]
    intro n hn x hx
    exact uc22main1_conj_mem_pCoreOf_self hn hx

private theorem V_le_pCoreOf_L (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {hV : IsElemAbelian 2 c.V}
    {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n) :
    c.V ≤ CFSG.Open.pCoreOf 2 c.L := by
  refine uc22main1_le_pCoreOf (κ.le_of_le_normalizer ((c.V_le_T h4 h1930).trans c.hL.1.1))
    hV.isPGroup ?_
  intro k hk x hx
  exact (Subgroup.mem_normalizer_iff.mp
    ((Ctx23L.sup_le_normalizer_V D Ch c) (Subgroup.mem_sup_left hk)) x).mp hx

private theorem pCoreOf_L_le_pCoreOf_sup {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hHP : c.L ⊔ D.T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G)) :
    CFSG.Open.pCoreOf 2 c.L ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
  uc22main1_le_pCoreOf ((uc22main1_pCoreOf_le c.L).trans le_sup_left)
    (uc22main1_isPGroup_pCoreOf c.L)
    (fun n hn x hx => (Subgroup.mem_normalizer_iff.mp (hHP hn) x).mp hx)

private def chiefSect_of_section {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {X Y : Subgroup G} (hVY : c.V ≤ Y) (hYX : Y ≤ X)
    (hXP : X ≤ CFSG.Open.pCoreOf 2 c.L)
    (hPQ : CFSG.Open.pCoreOf 2 c.L ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))
    (hQT : CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ≤ D.T)
    (hNX : c.L ⊔ D.T ≤ Subgroup.normalizer (X : Set G))
    (hNY : c.L ⊔ D.T ≤ Subgroup.normalizer (Y : Set G)) (hsq : ∀ x ∈ X, x ^ 2 ∈ Y)
    (hXQ : ⁅X, CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)⁆ ≤ Y)
    (hK0Q : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤
      CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))
    (hnot : ¬ ⁅X, c.L⁆ ≤ Y) : ChiefSect c := by
  have hQact : ∀ s ∈ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T), ∀ x ∈ X,
      s * x * s⁻¹ * x⁻¹ ∈ Y := by
    intro s hs x hx
    have hc : ⁅x, s⁆ ∈ Y := Subgroup.commutator_le.mp hXQ x hx s hs
    have hcinv : ⁅x, s⁆⁻¹ = s * x * s⁻¹ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [← hcinv]
    exact Y.inv_mem hc
  exact
    { X := X
      Y := Y
      hVY := hVY
      hYX := hYX
      hXT := (hXP.trans hPQ).trans hQT
      hXP := hXP
      hNX := hNX
      hNY := hNY
      hsq := hsq
      hXX := (Subgroup.commutator_mono le_rfl (hXP.trans hPQ)).trans hXQ
      hQact := hQact
      hK0act := fun s hs => hQact s (hK0Q hs)
      hnot := hnot }

private theorem exists_chiefSect (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h205 : S20_5 D) (h640 : UC6.R6_40_1 D) (h1930 : H1930 D)
    (c : Ctx23L D Ch) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) : Nonempty (ChiefSect c) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hLV, κ, -, -⟩ := c.exists_coordinates_V D Ch h4 h23 h1930
  obtain ⟨hHP, hHQ⟩ := normalizer_pCoreOf c
  have hVP := V_le_pCoreOf_L D Ch h4 h1930 c κ
  have hO2LleQ := pCoreOf_L_le_pCoreOf_sup c hHP
  have hQleT : CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp
        (D.sylowG.of_le (le_sup_right : D.T ≤ c.L ⊔ D.T) le_top))
  have hK0Q : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤
      CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
    (Ctx23L.inf_centralizer_V_le_pCoreOf_L D Ch h4 h23 h1930 c).trans hO2LleQ
  obtain ⟨X, Y, hVY, hYX, hXP, hNX, hNY, hsq, hXQ, hnot⟩ :=
    exists_section_of_not_commutator_le (p := 2) (H := c.L ⊔ D.T) (L := c.L)
      (Q := CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) (P := CFSG.Open.pCoreOf 2 c.L) (V := c.V)
      le_sup_left (uc22main1_pCoreOf_le _) hVP hO2LleQ (uc22main1_isPGroup_pCoreOf _)
      hHP hHQ (Ctx23L.sup_le_normalizer_V D Ch c) c.hL.1.2.1
      (not_commutator_pCoreOf_le_V D Ch h4 h23 h205 h640 h1930 c h3)
  exact ⟨chiefSect_of_section c hVY hYX hXP hO2LleQ hQleT hNX hNY hsq hXQ hK0Q hnot⟩

private theorem relIndex_centMod_eq_of_conj_alpha (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) {hV : IsElemAbelian 2 c.V}
    {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    (S : ChiefSect c) {l l' m : ↥c.L} (hα : κ.α l' = κ.α (m * l * m⁻¹)) :
    (CFSG.GroupTheory.centMod S.X S.Y (l' : G)).relIndex S.X =
      (CFSG.GroupTheory.centMod S.X S.Y (l : G)).relIndex S.X := by
  classical
  let cc : ↥c.L := (m * l * m⁻¹)⁻¹ * l'
  have hcc : (cc : G) ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G) := by
    have h1 : cc ∈ κ.α.ker := by
      show κ.α cc = 1
      rw [map_mul, map_inv, hα, inv_mul_cancel]
    rwa [κ.α_ker, Subgroup.mem_subgroupOf] at h1
  have htriv : ∀ x ∈ S.X, (cc : G) * x * (cc : G)⁻¹ * x⁻¹ ∈ S.Y :=
    fun x hx => S.hK0act cc hcc x hx
  have hgY : ((m * l * m⁻¹ : ↥c.L) : G) ∈ Subgroup.normalizer (S.Y : Set G) :=
    S.hNY (Subgroup.mem_sup_left (m * l * m⁻¹).2)
  have hcY : (cc : G) ∈ Subgroup.normalizer (S.Y : Set G) :=
    S.hNY (Subgroup.mem_sup_left cc.2)
  have hmul := CFSG.GroupTheory.centMod_mul_of_forall_of_normalizer S.hYX S.hXX hgY hcY htriv
  have heq : ((m * l * m⁻¹ : ↥c.L) : G) * (cc : G) = (l' : G) := by
    show ((m * l * m⁻¹ : ↥c.L) : G) * (((m * l * m⁻¹)⁻¹ * l' : ↥c.L) : G) = (l' : G)
    push_cast
    group
  rw [heq] at hmul
  have hconj : ((m * l * m⁻¹ : ↥c.L) : G) = (m : G) * (l : G) * (m : G)⁻¹ := by
    push_cast
    group
  rw [hmul, hconj]
  exact CFSG.GroupTheory.relIndex_centMod_conj S.hYX S.hXX (S.hNY (Subgroup.mem_sup_left l.2))
    (S.hNX (Subgroup.mem_sup_left m.2)) (S.hNY (Subgroup.mem_sup_left m.2))

private theorem exists_mul_mem_inf_centralizer (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {u : G} (huT : u ∈ D.T) (hunc : u ∉ Subgroup.centralizer (c.V : Set G)) :
    ∃ a b : G, a ∈ D.T ⊓ c.L ∧ b ∈ D.T ⊓ Subgroup.centralizer (c.V : Set G) ∧
      u = a * b ∧ a ∉ Subgroup.centralizer (c.V : Set G) := by
  classical
  have hsupT : D.T = (D.T ⊓ c.L) ⊔ (D.T ⊓ Subgroup.centralizer (c.V : Set G)) :=
    Ctx23L.T_eq_sup_inf_centralizer D Ch h4 h23 h1930 c
  have htop : (D.T ⊓ c.L).subgroupOf D.T ⊔
      (D.T ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf D.T = ⊤ := by
    rw [← Subgroup.subgroupOf_sup inf_le_left inf_le_left, ← hsupT,
      Subgroup.subgroupOf_self]
  haveI hBnorm : ((D.T ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf D.T).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    refine (le_inf Subgroup.le_normalizer ?_).trans
      (show Subgroup.normalizer (D.T : Set G) ⊓
          Subgroup.normalizer (Subgroup.centralizer (c.V : Set G) : Set G) ≤
          Subgroup.normalizer ((D.T ⊓ Subgroup.centralizer (c.V : Set G) : Subgroup G) : Set G)
        from Subgroup.inf_normalizer_le_normalizer_inf)
    exact (le_sup_right : D.T ≤ c.L ⊔ D.T).trans
      ((Ctx23L.sup_le_normalizer_V D Ch c).trans
        (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer c.V))
  have huT' : (⟨u, huT⟩ : ↥D.T) ∈ (D.T ⊓ c.L).subgroupOf D.T ⊔
      (D.T ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf D.T := by
    rw [htop]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp huT'
  have habG : u = (a : G) * (b : G) := (congrArg (fun x : ↥D.T => (x : G)) hab).symm
  have hbC : (b : G) ∈ Subgroup.centralizer (c.V : Set G) := (Subgroup.mem_subgroupOf.mp hb).2
  refine ⟨(a : G), (b : G), Subgroup.mem_subgroupOf.mp ha, Subgroup.mem_subgroupOf.mp hb,
    habG, ?_⟩
  intro hac
  exact hunc (habG.symm ▸ (Subgroup.centralizer (c.V : Set G)).mul_mem hac hbC)

private theorem alpha_involution_of_mem_T_inf_L (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) {hV : IsElemAbelian 2 c.V}
    {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    {a : G} (haT : a ∈ D.T) (haL : a ∈ c.L)
    (hac : a ∉ Subgroup.centralizer (c.V : Set G)) :
    κ.α ⟨a, haL⟩ * κ.α ⟨a, haL⟩ = 1 ∧ κ.α ⟨a, haL⟩ ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · have hTp : IsPGroup 2 D.T := CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowG
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hTp) ⟨a, haT⟩
    have hLorder : orderOf (⟨a, haL⟩ : ↥c.L) = 2 ^ k :=
      (Subgroup.orderOf_coe (⟨a, haL⟩ : ↥c.L)).symm.trans
        ((Subgroup.orderOf_coe (⟨a, haT⟩ : ↥D.T)).trans hk)
    have hdvd : orderOf (κ.α ⟨a, haL⟩) ∣ 2 ^ k := by
      rw [← hLorder]
      exact orderOf_map_dvd κ.α _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact specialLinear_mul_self_eq_one_of_orderOf_eq_two_pow _ hj
  · intro h
    apply hac
    have h1 : (⟨a, haL⟩ : ↥c.L) ∈ κ.α.ker := h
    rw [κ.α_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h1
    exact h1.2

private theorem relIndex_centMod_le_two_of_mem_U {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (S : ChiefSect c) {T₀ : Subgroup G} (hT₀T : T₀ ≤ D.T)
    (hTN : D.T ≤ Subgroup.normalizer (T₀ : Set G)) {g₀ : G} (hg₀ : g₀ ∈ D.T)
    (hcyc : D.T ≤ T₀ ⊔ Subgroup.zpowers g₀) {U : Subgroup G} (hUT₀ : U ≤ T₀)
    (hT₀U : ⁅T₀, U⁆ ≤ D.Z) {u : G} (hu : u ∈ U) :
    (CFSG.GroupTheory.centMod S.X S.Y u).relIndex S.X ≤ 2 := by
  have huT : u ∈ D.T := hT₀T (hUT₀ hu)
  refine CFSG.GroupTheory.relIndex_centMod_le_two S.hYX S.hXX S.hXT hT₀T hTN hg₀ hcyc
    (fun x hx => by simpa [pow_two] using S.hsq x hx)
    (S.hNY (Subgroup.mem_sup_right huT)) ?_
  intro x hx
  have hcomm : ⁅x, u⁆ ∈ D.Z := Subgroup.commutator_le.mp hT₀U x hx.2 u hu
  have hZV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have h1 : ⁅u, x⁆ ∈ c.V := by
    have h2 : ⁅u, x⁆ = ⁅x, u⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact c.V.inv_mem (hZV hcomm)
  simpa [commutatorElement_def] using S.hVY h1

private theorem relIndex_centMod_le_two_of_mul_mem {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (S : ChiefSect c) {u a b : G} (hab : u = a * b) (haL : a ∈ c.L)
    (hbT : b ∈ D.T) (hbQ : b ∈ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))
    (hle : (CFSG.GroupTheory.centMod S.X S.Y u).relIndex S.X ≤ 2) :
    (CFSG.GroupTheory.centMod S.X S.Y a).relIndex S.X ≤ 2 := by
  have hbtriv : ∀ x ∈ S.X, b * x * b⁻¹ * x⁻¹ ∈ S.Y := S.hQact b hbQ
  have hbY : b ∈ Subgroup.normalizer (S.Y : Set G) := S.hNY (Subgroup.mem_sup_right hbT)
  have haY : a ∈ Subgroup.normalizer (S.Y : Set G) := S.hNY (Subgroup.mem_sup_left haL)
  have heq : CFSG.GroupTheory.centMod S.X S.Y u =
      CFSG.GroupTheory.centMod S.X S.Y a := by
    rw [hab]
    exact CFSG.GroupTheory.centMod_mul_of_forall_of_normalizer S.hYX S.hXX haY hbY hbtriv
  rwa [← heq]

private theorem exists_involution_relIndex_le_two (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    (S : ChiefSect c) {T₀ : Subgroup G} (hT₀T : T₀ ≤ D.T)
    (hTN : D.T ≤ Subgroup.normalizer (T₀ : Set G)) {g₀ : G} (hg₀ : g₀ ∈ D.T)
    (hcyc : D.T ≤ T₀ ⊔ Subgroup.zpowers g₀) {U : Subgroup G} (hUT₀ : U ≤ T₀)
    (hT₀U : ⁅T₀, U⁆ ≤ D.Z) {u : G} (hu : u ∈ U)
    (hunc : u ∉ Subgroup.centralizer (c.V : Set G)) :
    ∃ l : ↥c.L, κ.α l * κ.α l = 1 ∧ κ.α l ≠ 1 ∧
      (CFSG.GroupTheory.centMod S.X S.Y (l : G)).relIndex S.X ≤ 2 := by
  classical
  obtain ⟨a, b, ha, hb, hab, hac⟩ :=
    exists_mul_mem_inf_centralizer D Ch h4 h23 h1930 c (hT₀T (hUT₀ hu)) hunc
  have hbQ : b ∈ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
    ((inf_le_inf (le_sup_right : D.T ≤ c.L ⊔ D.T) le_rfl).trans
      (Ctx23L.sup_inf_centralizer_V_le_pCoreOf c h4 h23 h1930))
      (Subgroup.mem_inf.mpr ⟨hb.1, hb.2⟩)
  obtain ⟨h2, hαne⟩ := alpha_involution_of_mem_T_inf_L D Ch c κ ha.1 ha.2 hac
  have hle_u := relIndex_centMod_le_two_of_mem_U c S hT₀T hTN hg₀ hcyc hUT₀ hT₀U hu
  have hle_a := relIndex_centMod_le_two_of_mul_mem c S hab ha.2 hb.1 hbQ hle_u
  exact ⟨⟨a, ha.2⟩, h2, hαne, by simpa using hle_a⟩

private theorem relIndex_centMod_le_two_of_involution (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    (S : ChiefSect c) {l₀ : ↥c.L} (h2₀ : κ.α l₀ * κ.α l₀ = 1) (h1₀ : κ.α l₀ ≠ 1)
    (hle₀ : (CFSG.GroupTheory.centMod S.X S.Y (l₀ : G)).relIndex S.X ≤ 2) {g : ↥c.L}
    (h2 : κ.α g * κ.α g = 1) (h1 : κ.α g ≠ 1) :
    (CFSG.GroupTheory.centMod S.X S.Y (g : G)).relIndex S.X ≤ 2 := by
  classical
  obtain ⟨k, hk⟩ := exists_conj_sl2W (K := κ.K) h2₀ h1₀
  obtain ⟨k', hk'⟩ := exists_conj_sl2W (K := κ.K) h2 h1
  obtain ⟨m, hm⟩ := κ.α_surj (k' * k⁻¹)
  have hα : κ.α g = κ.α (m * l₀ * m⁻¹) := by
    rw [map_mul, map_mul, map_inv, hm, ← hk, ← hk']
    group
  rw [relIndex_centMod_eq_of_conj_alpha D Ch c κ S (l := l₀) (l' := g) (m := m) hα]
  exact hle₀

private theorem exists_torus_preimage (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hcardK : Nat.card κ.K = 2 ^ CFSG.Open.pRank 2 D.Z) :
    ∃ (a : κ.Kˣ) (h₀ : ↥c.L), orderOf a = Nat.card κ.K - 1 ∧
      Odd (Nat.card κ.K - 1) ∧ κ.α h₀ = sl2Diag a := by
  classical
  haveI : IsCyclic κ.Kˣ := by
    let : IsCyclic (⊤ : Subgroup κ.Kˣ) := isCyclic_subgroup_units ⊤
    exact isCyclic_of_surjective (⊤ : Subgroup κ.Kˣ).subtype
      (fun a => ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩)
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := κ.Kˣ)
  have hq : orderOf a = Nat.card κ.K - 1 := ha.trans (Nat.card_units (α := κ.K))
  have hqodd : Odd (Nat.card κ.K - 1) := by
    rw [hcardK]
    obtain ⟨m, hm⟩ : ∃ m, CFSG.Open.pRank 2 D.Z = m + 1 :=
      ⟨CFSG.Open.pRank 2 D.Z - 1, by omega⟩
    rw [hm, pow_succ]
    refine ⟨2 ^ m - 1, ?_⟩
    have hpos : 0 < 2 ^ m := by positivity
    omega
  obtain ⟨h₀, hh₀⟩ := κ.α_surj (sl2Diag a)
  exact ⟨a, h₀, hq, hqodd, hh₀⟩

private theorem pow_ker_card_eq_one {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    {a : κ.Kˣ} {h₀ : ↥c.L} {j : ℕ} (hj : Nat.card ↥κ.α.ker = 2 ^ j)
    (hkerpow : h₀ ^ orderOf a ∈ κ.α.ker) :
    (h₀ ^ orderOf a) ^ (2 ^ j) = 1 := by
  have hmem : (⟨h₀ ^ orderOf a, hkerpow⟩ : ↥κ.α.ker) ^ (2 ^ j) = 1 := by
    rw [← hj]
    exact pow_card_eq_one'
  simpa [Subgroup.coe_pow] using congrArg (fun x : ↥κ.α.ker => (x : ↥c.L)) hmem

private theorem exists_odd_lift (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    {a : κ.Kˣ} {h₀ : ↥c.L} (hq : orderOf a = Nat.card κ.K - 1)
    (hqodd : Odd (Nat.card κ.K - 1)) (hh₀ : κ.α h₀ = sl2Diag a) :
    ∃ (h : ↥c.L) (a' : κ.Kˣ), Odd (orderOf h) ∧ orderOf a' = orderOf a ∧
      κ.α h = sl2Diag a' := by
  classical
  have hK0p : IsPGroup 2 ↥κ.α.ker := by
    rw [κ.α_ker]
    exact ((uc22main1_isPGroup_pCoreOf c.L).to_le
      (Ctx23L.inf_centralizer_V_le_pCoreOf_L D Ch h4 h23 h1930 c)).comap_subtype
  obtain ⟨j, hj⟩ := hK0p.exists_card_eq
  let h : ↥c.L := h₀ ^ (2 ^ j)
  let a' : κ.Kˣ := a ^ (2 ^ j)
  have hαh : κ.α h = sl2Diag a' := by
    show κ.α (h₀ ^ (2 ^ j)) = sl2Diag (a ^ (2 ^ j))
    rw [map_pow, hh₀, map_pow]
  have hgcd : Nat.gcd (orderOf a) (2 ^ j) = 1 := by
    have h1 : Nat.Coprime (orderOf a) 2 := hq.symm ▸ hqodd.coprime_two_right
    simpa using h1.pow_right j
  have ha' : orderOf a' = orderOf a := by
    show orderOf (a ^ (2 ^ j)) = orderOf a
    rw [orderOf_pow, hgcd, Nat.div_one]
  have hkerpow : h₀ ^ orderOf a ∈ κ.α.ker := by
    show κ.α (h₀ ^ orderOf a) = 1
    rw [map_pow, hh₀, ← map_pow, pow_orderOf_eq_one, map_one]
  have hpowq : h ^ orderOf a = 1 := by
    have h1 := pow_ker_card_eq_one c κ hj hkerpow
    show (h₀ ^ (2 ^ j)) ^ orderOf a = 1
    rw [← pow_mul, mul_comm, pow_mul]
    exact h1
  refine ⟨h, a', ?_, ha', hαh⟩
  have hdvd1 : orderOf h ∣ orderOf a := orderOf_dvd_of_pow_eq_one hpowq
  have hdvd2 : orderOf a ∣ orderOf h := by
    have h1 : orderOf (κ.α h) ∣ orderOf h := orderOf_map_dvd κ.α h
    rwa [show orderOf (κ.α h) = orderOf a from by rw [hαh, orderOf_sl2Diag, ha']] at h1
  rw [Nat.dvd_antisymm hdvd1 hdvd2]
  rwa [hq]

private theorem exists_odd_order_torus_lift (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hcardK : Nat.card κ.K = 2 ^ CFSG.Open.pRank 2 D.Z) :
    ∃ (h : ↥c.L) (a' : κ.Kˣ), Odd (orderOf h) ∧ orderOf a' = Nat.card κ.K - 1 ∧
      κ.α h = sl2Diag a' := by
  obtain ⟨a, h₀, hq, hqodd, hh₀⟩ := exists_torus_preimage D Ch c κ h3 hcardK
  obtain ⟨h, a', hodd, ha', hα⟩ := exists_odd_lift D Ch h4 h23 h1930 c κ hq hqodd hh₀
  exact ⟨h, a', hodd, ha'.trans hq, hα⟩

private theorem relIndex_inf_le_four {X A B : Subgroup G} (hA : A.relIndex X ≤ 2)
    (hB : B.relIndex X ≤ 2) : (A ⊓ B).relIndex X ≤ 4 := by
  refine (Subgroup.relIndex_inf_le (H := A) (K := B) (L := X)).trans ?_
  have h3 := Nat.mul_le_mul hA hB
  omega

private theorem le_centMod_inf {X Y : Subgroup G} {w h : G} (hYX : Y ≤ X) (hXX : ⁅X, X⁆ ≤ Y)
    (hwY : w ∈ Subgroup.normalizer (Y : Set G))
    (hwhY : w * h ∈ Subgroup.normalizer (Y : Set G)) :
    CFSG.GroupTheory.centMod X Y w ⊓ CFSG.GroupTheory.centMod X Y (w * h) ≤
      CFSG.GroupTheory.centMod X Y h := by
  have hinf := CFSG.GroupTheory.inf_centMod_le_mul hYX hXX
    (g₁ := w⁻¹) (g₂ := w * h) ((Subgroup.normalizer (Y : Set G)).inv_mem hwY) hwhY
  rw [CFSG.GroupTheory.centMod_inv hYX hXX (g := w) hwY] at hinf
  have harg : w⁻¹ * (w * h) = h := by group
  rwa [harg] at hinf

private theorem normalizer_of_le_centMod {X Y P : Subgroup G} {h : G} (hYP : Y ≤ P)
    (hPX : P ≤ X) (hPh : P ≤ CFSG.GroupTheory.centMod X Y h) (hXX : ⁅X, X⁆ ≤ Y)
    (hY : h ∈ Subgroup.normalizer (Y : Set G)) :
    h ∈ Subgroup.normalizer (P : Set G) := by
  have hYX : Y ≤ X := hYP.trans hPX
  have hstep : ∀ g : G, P ≤ CFSG.GroupTheory.centMod X Y g → ∀ p ∈ P, g * p * g⁻¹ ∈ P := by
    intro g hg p hp
    have hcomm : g * p * g⁻¹ * p⁻¹ ∈ Y :=
      ((CFSG.GroupTheory.mem_centMod_iff hYX hXX).mp (hg hp)).2
    rw [show g * p * g⁻¹ = (g * p * g⁻¹ * p⁻¹) * p by group]
    exact P.mul_mem (hYP hcomm) hp
  have hPhinv : P ≤ CFSG.GroupTheory.centMod X Y h⁻¹ := by
    rw [CFSG.GroupTheory.centMod_inv hYX hXX (g := h) hY]
    exact hPh
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · exact hstep h hPh p
  · intro hp
    have h1 := hstep h⁻¹ hPhinv (h * p * h⁻¹) hp
    rwa [show h⁻¹ * (h * p * h⁻¹) * (h⁻¹)⁻¹ = p by group] at h1

private theorem pow24_centralizes_of_P {X Y P : Subgroup G} {h : G} (hPX : P ≤ X)
    (hYX : Y ≤ X) (hXX : ⁅X, X⁆ ≤ Y) (hYP : Y ≤ P) (hsq : ∀ x ∈ X, x * x ∈ Y)
    (hNX : h ∈ Subgroup.normalizer (X : Set G)) (hNY : h ∈ Subgroup.normalizer (Y : Set G))
    (hNP : h ∈ Subgroup.normalizer (P : Set G)) (hrelP : P.relIndex X ≤ 4)
    (hcommP : ∀ p ∈ P, h * p * h⁻¹ * p⁻¹ ∈ Y) (hhodd : Odd (orderOf h)) :
    ∀ x ∈ X, h ^ 24 * x * (h ^ 24)⁻¹ * x⁻¹ ∈ Y := by
  have hX24 : ∀ x ∈ X, h ^ 24 * x * (h ^ 24)⁻¹ * x⁻¹ ∈ P :=
    CFSG.GroupTheory.pow_twentyFour_mem_of_relIndex_le_four hPX (hXX.trans hYP) hNX hNP hrelP
  have hPY24 : ∀ p ∈ P, h ^ 24 * p * (h ^ 24)⁻¹ * p⁻¹ ∈ Y :=
    CFSG.GroupTheory.pow_commutator_mem_of_commutator_mem hNY hcommP 24
  have hgm : ∀ x ∈ X, (h ^ 24) ^ orderOf h * x * ((h ^ 24) ^ orderOf h)⁻¹ * x⁻¹ ∈ Y := by
    intro x hx
    have h1 : (h ^ 24) ^ orderOf h = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    rw [h1]
    simp
  exact CFSG.GroupTheory.commutator_mem_of_odd_pow (W := P) hPX hYX hXX hsq
    ((Subgroup.normalizer (Y : Set G)).pow_mem hNY 24) hPY24 hX24 hhodd hgm

private theorem exists_swap_data (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    (S : ChiefSect c) {l₀ : ↥c.L} (h2₀ : κ.α l₀ * κ.α l₀ = 1) (h1₀ : κ.α l₀ ≠ 1)
    (hle₀ : (CFSG.GroupTheory.centMod S.X S.Y (l₀ : G)).relIndex S.X ≤ 2)
    {h : ↥c.L} {a' : κ.Kˣ} (hαh : κ.α h = sl2Diag a') :
    ∃ w : ↥c.L, (CFSG.GroupTheory.centMod S.X S.Y (w : G)).relIndex S.X ≤ 2 ∧
      (CFSG.GroupTheory.centMod S.X S.Y ((w * h : ↥c.L) : G)).relIndex S.X ≤ 2 := by
  classical
  obtain ⟨w, hw⟩ := κ.α_surj (sl2W : Matrix.SpecialLinearGroup (Fin 2) κ.K)
  have h2w : κ.α w * κ.α w = 1 := by
    rw [hw]
    exact sl2W_mul_self
  have h1w : κ.α w ≠ 1 := by
    rw [hw]
    exact sl2W_ne_one
  have h2wh : κ.α (w * h) * κ.α (w * h) = 1 := by
    rw [map_mul, hw, hαh]
    exact sl2W_mul_sl2Diag_mul_self a'
  have h1wh : κ.α (w * h) ≠ 1 := by
    rw [map_mul, hw, hαh]
    exact sl2W_mul_sl2Diag_ne_one a'
  exact ⟨w,
    relIndex_centMod_le_two_of_involution D Ch c κ S h2₀ h1₀ hle₀ h2w h1w,
    relIndex_centMod_le_two_of_involution D Ch c κ S h2₀ h1₀ hle₀ h2wh h1wh⟩

private theorem pow24_centralizes_X_mod_Y (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    (S : ChiefSect c) {l₀ : ↥c.L}
    (h2₀ : κ.α l₀ * κ.α l₀ = 1) (h1₀ : κ.α l₀ ≠ 1)
    (hle₀ : (CFSG.GroupTheory.centMod S.X S.Y (l₀ : G)).relIndex S.X ≤ 2)
    {h : ↥c.L} {a' : κ.Kˣ} (hhodd : Odd (orderOf h)) (hαh : κ.α h = sl2Diag a') :
    ∀ x ∈ S.X, (h : G) ^ 24 * x * ((h : G) ^ 24)⁻¹ * x⁻¹ ∈ S.Y := by
  obtain ⟨w, hle_w, hle_wh⟩ := exists_swap_data D Ch c κ S h2₀ h1₀ hle₀ hαh
  let P : Subgroup G :=
    CFSG.GroupTheory.centMod S.X S.Y (w : G) ⊓
      CFSG.GroupTheory.centMod S.X S.Y ((w * h : ↥c.L) : G)
  have hPX : P ≤ S.X :=
    inf_le_left.trans (CFSG.GroupTheory.centMod_le S.X S.Y (w : G))
  have hYP : S.Y ≤ P := by
    refine le_inf ?_ ?_
    · exact CFSG.GroupTheory.le_centMod S.hYX S.hXX (S.hNY (Subgroup.mem_sup_left w.2))
    · exact CFSG.GroupTheory.le_centMod S.hYX S.hXX (S.hNY (Subgroup.mem_sup_left (w * h).2))
  have hrelP : P.relIndex S.X ≤ 4 := relIndex_inf_le_four hle_w hle_wh
  have hPh : P ≤ CFSG.GroupTheory.centMod S.X S.Y (h : G) :=
    le_centMod_inf S.hYX S.hXX (S.hNY (Subgroup.mem_sup_left w.2))
      (S.hNY (Subgroup.mem_sup_left (w * h).2))
  have hPN := normalizer_of_le_centMod hYP hPX hPh S.hXX (S.hNY (Subgroup.mem_sup_left h.2))
  have hcommP : ∀ p ∈ P, (h : G) * p * (h : G)⁻¹ * p⁻¹ ∈ S.Y :=
    fun p hp => ((CFSG.GroupTheory.mem_centMod_iff S.hYX S.hXX).mp (hPh hp)).2
  have hhoddG : Odd (orderOf (h : G)) := by simpa [Subgroup.orderOf_coe] using hhodd
  exact pow24_centralizes_of_P hPX S.hYX S.hXX hYP
    (fun x hx => by simpa [pow_two] using S.hsq x hx)
    (S.hNX (Subgroup.mem_sup_left h.2)) (S.hNY (Subgroup.mem_sup_left h.2)) hPN hrelP
    hcommP hhoddG

private def centralizingSubgroup {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (S : ChiefSect c) : Subgroup ↥c.L :=
  { carrier := {n | ∀ x ∈ S.X, (n : G) * x * (n : G)⁻¹ * x⁻¹ ∈ S.Y}
    one_mem' := by
      intro x _
      simpa using S.Y.one_mem
    mul_mem' := by
      intro a b ha hb x hx
      have hb' : (a : G) * ((b : G) * x * (b : G)⁻¹ * x⁻¹) * (a : G)⁻¹ ∈ S.Y :=
        (Subgroup.mem_normalizer_iff.mp (S.hNY (Subgroup.mem_sup_left a.2)) _).mp (hb x hx)
      have heq : (((a * b : ↥c.L)) : G) * x * (((a * b : ↥c.L)) : G)⁻¹ * x⁻¹ =
          (a : G) * ((b : G) * x * (b : G)⁻¹ * x⁻¹) * (a : G)⁻¹ *
            ((a : G) * x * (a : G)⁻¹ * x⁻¹) := by
        push_cast
        group
      rw [heq]
      exact S.Y.mul_mem hb' (ha x hx)
    inv_mem' := by
      intro a ha x hx
      have haY : (a : G) ∈ Subgroup.normalizer (S.Y : Set G) :=
        S.hNY (Subgroup.mem_sup_left a.2)
      have h1 : ((a : G) * x * (a : G)⁻¹ * x⁻¹)⁻¹ ∈ S.Y := S.Y.inv_mem (ha x hx)
      have h2 : (a : G) * ((a : G)⁻¹ * x * (a : G) * x⁻¹) * (a : G)⁻¹ ∈ S.Y := by
        rw [show (a : G) * ((a : G)⁻¹ * x * (a : G) * x⁻¹) * (a : G)⁻¹ =
          ((a : G) * x * (a : G)⁻¹ * x⁻¹)⁻¹ by group]
        exact h1
      simpa [Subgroup.coe_inv] using
        (Subgroup.mem_normalizer_iff.mp haY ((a : G)⁻¹ * x * (a : G) * x⁻¹)).mpr h2 }

private theorem centralizingSubgroup_normal {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (S : ChiefSect c) : (centralizingSubgroup c S).Normal := by
  refine Subgroup.Normal.mk ?_
  intro b hb m x hx
  have hmX : (m : G)⁻¹ * x * (m : G) ∈ S.X := by
    have hmX' : (m : G) ∈ Subgroup.normalizer (S.X : Set G) :=
      S.hNX (Subgroup.mem_sup_left m.2)
    simpa using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (S.X : Set G)).inv_mem hmX') x).mp hx
  have hinner := hb ((m : G)⁻¹ * x * (m : G)) hmX
  have hmY : (m : G) ∈ Subgroup.normalizer (S.Y : Set G) :=
    S.hNY (Subgroup.mem_sup_left m.2)
  have hconj : (m : G) * ((b : G) * ((m : G)⁻¹ * x * (m : G)) * (b : G)⁻¹ *
      ((m : G)⁻¹ * x * (m : G))⁻¹) * (m : G)⁻¹ ∈ S.Y :=
    (Subgroup.mem_normalizer_iff.mp hmY _).mp hinner
  have heq : (((m * b * m⁻¹ : ↥c.L)) : G) * x * (((m * b * m⁻¹ : ↥c.L)) : G)⁻¹ * x⁻¹ =
      (m : G) * ((b : G) * ((m : G)⁻¹ * x * (m : G)) * (b : G)⁻¹ *
        ((m : G)⁻¹ * x * (m : G))⁻¹) * (m : G)⁻¹ := by
    push_cast
    group
  rw [heq]
  exact hconj

private theorem ker_le_centralizingSubgroup {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (S : ChiefSect c) {hV : IsElemAbelian 2 c.V}
    {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n) :
    κ.α.ker ≤ centralizingSubgroup c S := by
  intro b hb
  have hbK0 : (b : G) ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G) := by
    have h1 : b ∈ (c.L ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf c.L := by
      rwa [← κ.α_ker]
    exact Subgroup.mem_subgroupOf.mp h1
  exact S.hK0act (b : G) hbK0

private theorem pow24_mem_centralizingSubgroup {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (S : ChiefSect c) {h : ↥c.L}
    (hXY : ∀ x ∈ S.X, (h : G) ^ 24 * x * ((h : G) ^ 24)⁻¹ * x⁻¹ ∈ S.Y) :
    h ^ 24 ∈ centralizingSubgroup c S := by
  show ∀ x ∈ S.X, ((h ^ 24 : ↥c.L) : G) * x * (((h ^ 24 : ↥c.L)) : G)⁻¹ * x⁻¹ ∈ S.Y
  intro x hx
  rw [Subgroup.coe_pow]
  exact hXY x hx

private theorem map_centralizingSubgroup_eq_top {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (S : ChiefSect c) {hV : IsElemAbelian 2 c.V}
    {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    {h : ↥c.L} {a' : κ.Kˣ} (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hcardK : Nat.card κ.K = 2 ^ CFSG.Open.pRank 2 D.Z)
    (ha' : orderOf a' = Nat.card κ.K - 1) (hα : κ.α h = sl2Diag a')
    (hhN : h ^ 24 ∈ centralizingSubgroup c S) :
    (centralizingSubgroup c S).map κ.α = ⊤ := by
  haveI : (centralizingSubgroup c S).Normal := centralizingSubgroup_normal c S
  haveI : ((centralizingSubgroup c S).map κ.α).Normal :=
    (centralizingSubgroup_normal c S).map κ.α κ.α_surj
  have hmem : (sl2Diag a') ^ 24 ∈ (centralizingSubgroup c S).map κ.α := by
    rw [← hα, ← map_pow]
    exact Subgroup.mem_map_of_mem κ.α hhN
  exact eq_top_of_normal_of_mem_sl2Diag_pow_24 h3 hcardK a' ha' hmem

private theorem centralizingSubgroup_eq_top {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (S : ChiefSect c) {hV : IsElemAbelian 2 c.V}
    {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    (hker : κ.α.ker ≤ centralizingSubgroup c S)
    (himage : (centralizingSubgroup c S).map κ.α = ⊤) :
    centralizingSubgroup c S = ⊤ := by
  refine eq_top_iff.mpr ?_
  intro x _
  have hx : κ.α x ∈ (centralizingSubgroup c S).map κ.α := by
    rw [himage]
    trivial
  obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.mp hx
  have hmem : b⁻¹ * x ∈ κ.α.ker := by
    show κ.α (b⁻¹ * x) = 1
    rw [map_mul, map_inv, hbx, inv_mul_cancel]
  have heq : x = b * (b⁻¹ * x) := by group
  rw [heq]
  exact (centralizingSubgroup c S).mul_mem hb (hker hmem)

private theorem forall_centralizes_of_pow24 (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    (S : ChiefSect c) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hcardK : Nat.card κ.K = 2 ^ CFSG.Open.pRank 2 D.Z) {h : ↥c.L} {a' : κ.Kˣ}
    (ha' : orderOf a' = Nat.card κ.K - 1) (hα : κ.α h = sl2Diag a')
    (hXY : ∀ x ∈ S.X, (h : G) ^ 24 * x * ((h : G) ^ 24)⁻¹ * x⁻¹ ∈ S.Y) :
    ∀ l ∈ c.L, ∀ x ∈ S.X, l * x * l⁻¹ * x⁻¹ ∈ S.Y := by
  have hhN := pow24_mem_centralizingSubgroup c S hXY
  have himage := map_centralizingSubgroup_eq_top c S κ h3 hcardK ha' hα hhN
  have htop := centralizingSubgroup_eq_top c S κ (ker_le_centralizingSubgroup c S κ) himage
  intro l hl x hx
  have hlN : (⟨l, hl⟩ : ↥c.L) ∈ centralizingSubgroup c S := by
    rw [htop]
    trivial
  exact hlN x hx

end Ctx23L

theorem commV2329_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h205 : S20_5 D) (h640 : UC6.R6_40_1 D) : CommV2329 D Ch := by
  intro h1930 c h3 T₀ hT₀T hTN hcyc U hUT₀ hT₀U
  obtain ⟨g₀, hg₀T, hcyc⟩ := hcyc
  classical
  by_contra hne
  have hex : ∃ v ∈ c.V, ∃ u ∈ U, ⁅v, u⁆ ≠ 1 := by
    by_contra hcon
    apply hne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    by_contra hxy
    exact hcon ⟨x, hx, y, hy, hxy⟩
  obtain ⟨v, hv, u, hu, hvu⟩ := hex
  have hunc : u ∉ Subgroup.centralizer (c.V : Set G) := by
    intro hc
    apply hvu
    have hcomm : v * u = u * v := (Subgroup.mem_centralizer_iff.mp hc) v hv
    rw [commutatorElement_def, hcomm]
    group
  obtain ⟨hV, hLV, κ, -, hcardK⟩ := c.exists_coordinates_V D Ch h4 h23 h1930
  obtain ⟨S⟩ := Ctx23L.exists_chiefSect D Ch h4 h23 h205 h640 h1930 c h3
  obtain ⟨l₀, h2₀, h1₀, hle₀⟩ :=
    Ctx23L.exists_involution_relIndex_le_two D Ch h4 h23 h1930 c κ S hT₀T hTN hg₀T hcyc
      hUT₀ hT₀U hu hunc
  obtain ⟨h, a', hhodd, ha', hα⟩ :=
    Ctx23L.exists_odd_order_torus_lift D Ch h4 h23 h1930 c κ h3 hcardK
  have hcent := Ctx23L.pow24_centralizes_X_mod_Y D Ch c κ S h2₀ h1₀ hle₀ hhodd hα
  exact S.hnot (CFSG.GroupTheory.commutator_le_of_forall_centralizes
    (Ctx23L.forall_centralizes_of_pow24 D Ch c κ S h3 hcardK ha' hα hcent))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
