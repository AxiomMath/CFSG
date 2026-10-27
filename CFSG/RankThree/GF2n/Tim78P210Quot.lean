module

public import CFSG.RankThree.GF2n.Tim78P210Basic
public import CFSG.RankThree.GF2n.QuotPair
public import CFSG.RankThree.GF2n.Tim78RootType
import CFSG.CGT.Timmesfeld75.Core214Proof
public import CFSG.CGT.Timmesfeld75.Config214
public import CFSG.CGT.Timmesfeld75.Sec25
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CGT.Timmesfeld75.Targets
public import CFSG.CGT.Timmesfeld75.ZStarSmall
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_b
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate117
public import Certificates.Certificate43
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def nrm (B C : Subgroup G) : Subgroup G := B ⊓ Subgroup.normalizer (C : Set G)

omit [Finite G] in
theorem mem_nrm {B C : Subgroup G} {x : G} :
    x ∈ nrm B C ↔ x ∈ B ∧ x ∈ Subgroup.normalizer (C : Set G) := Subgroup.mem_inf

structure QData (B₀ B₁ A₀ A₁ : Subgroup G) : Prop where
  setup : Setup210 B₀ B₁
  ne : B₀ ≠ B₁
  invol₀ : ∀ x ∈ nrm B₀ B₁, x * x = 1
  invol₁ : ∀ x ∈ nrm B₁ B₀, x * x = 1
  memA₀ : ∀ z, z ∈ A₀ ↔ z ∈ B₀ ∧ z * z ∈ nrm B₀ B₁
  memA₁ : ∀ z, z ∈ A₁ ↔ z ∈ B₁ ∧ z * z ∈ nrm B₁ B₀
  neA₀ : ∃ z ∈ A₀, z ∉ nrm B₀ B₁
  neA₁ : ∃ z ∈ A₁, z ∉ nrm B₁ B₀

namespace QData

variable {B₀ B₁ A₀ A₁ : Subgroup G} (D : QData B₀ B₁ A₀ A₁)
include D

theorem symm : QData B₁ B₀ A₁ A₀ where
  setup := D.setup.symm
  ne := Ne.symm D.ne
  invol₀ := D.invol₁
  invol₁ := D.invol₀
  memA₀ := D.memA₁
  memA₁ := D.memA₀
  neA₀ := D.neA₁
  neA₁ := D.neA₀

omit [Finite G] in
theorem A₀_le : A₀ ≤ B₀ := fun z hz => ((D.memA₀ z).mp hz).1

omit [Finite G] in
theorem F₀_le_A₀ : nrm B₀ B₁ ≤ A₀ := fun z hz => (D.memA₀ z).mpr
  ⟨(mem_nrm.mp hz).1, by rw [D.invol₀ z hz]; exact (nrm B₀ B₁).one_mem⟩

omit [Finite G] in
theorem F₀_ne_bot : nrm B₀ B₁ ≠ ⊥ := D.setup.ne_bot

theorem comm_F {a b : G} (ha : a ∈ nrm B₀ B₁) (hb : b ∈ nrm B₁ B₀) : a * b = b * a := by
  obtain ⟨haB, haN⟩ := mem_nrm.mp ha
  obtain ⟨hbB, hbN⟩ := mem_nrm.mp hb
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ B₁ :=
    B₁.mul_mem ((Subgroup.mem_normalizer_iff.mp haN b).mp hbB) (B₁.inv_mem hbB)
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ B₀ := by
    rw [mul_assoc, mul_assoc]
    refine B₀.mul_mem haB ?_
    have := (Subgroup.mem_normalizer_iff.mp hbN a⁻¹).mp (B₀.inv_mem haB)
    rwa [← mul_assoc]
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ B₀ ⊓ B₁ := Subgroup.mem_inf.mpr ⟨h2, h1⟩
  rw [D.setup.inf_eq_bot D.ne, Subgroup.mem_bot] at h3
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

theorem exists_mul_of_mem_Q {x : G} (hx : x ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀) :
    ∃ a ∈ nrm B₀ B₁, ∃ b ∈ nrm B₁ B₀, x = a * b :=
  exists_mul_of_mem_sup (le_normalizer_of_comm fun _ hb _ ha => (D.comm_F ha hb).symm) hx

theorem comm_Q {x y : G} (hx : x ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀) (hy : y ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀) :
    x * y = y * x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := D.exists_mul_of_mem_Q hx
  obtain ⟨a', ha', b', hb', rfl⟩ := D.exists_mul_of_mem_Q hy
  have h1 := D.setup.comm a (mem_nrm.mp ha).1 a' (mem_nrm.mp ha').1
  have h2 := D.setup.comm₁ b (mem_nrm.mp hb).1 b' (mem_nrm.mp hb').1
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [D.comm_F ha' hb]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [h1, h2]
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [D.comm_F ha hb']
    _ = a' * b' * (a * b) := by group

theorem sq_Q {x : G} (hx : x ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀) : x * x = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := D.exists_mul_of_mem_Q hx
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [D.comm_F ha hb]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [D.invol₀ a ha, D.invol₁ b hb, one_mul]

theorem mem_F₀_of_mem_Q {x : G} (hxB : x ∈ B₀) (hx : x ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀) :
    x ∈ nrm B₀ B₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := D.exists_mul_of_mem_Q hx
  have hbB : b ∈ B₀ := by
    have := B₀.mul_mem (B₀.inv_mem (mem_nrm.mp ha).1) hxB
    rwa [inv_mul_cancel_left] at this
  have h1 : b ∈ B₀ ⊓ B₁ := Subgroup.mem_inf.mpr ⟨hbB, (mem_nrm.mp hb).1⟩
  rw [D.setup.inf_eq_bot D.ne, Subgroup.mem_bot] at h1
  rw [h1, mul_one]
  exact ha

theorem conj_mem_mul_F₀ {y a : G} (hy : y ∈ A₀) (ha : a ∈ nrm B₁ B₀) :
    y⁻¹ * (a * y * a⁻¹) ∈ nrm B₀ B₁ := by
  obtain ⟨hyB, hy2⟩ := (D.memA₀ y).mp hy
  obtain ⟨haB, haN⟩ := mem_nrm.mp ha
  have haa : a * a = 1 := D.invol₁ a ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hyaB : a * y * a⁻¹ ∈ B₀ := (Subgroup.mem_normalizer_iff.mp haN y).mp hyB
  have hcB : y⁻¹ * (a * y * a⁻¹) ∈ B₀ := B₀.mul_mem (B₀.inv_mem hyB) hyaB
  have hsq : (a * y * a⁻¹) * (a * y * a⁻¹) = y * y := by
    have h := D.comm_F hy2 ha
    calc (a * y * a⁻¹) * (a * y * a⁻¹) = a * (y * y) * a⁻¹ := by group
      _ = (y * y) * a * a⁻¹ := by rw [← h]
      _ = y * y := by group
  have hcc : (y⁻¹ * (a * y * a⁻¹)) * (y⁻¹ * (a * y * a⁻¹)) = 1 := by
    have h1 := D.setup.comm _ (B₀.inv_mem hyB) _ hyaB
    calc (y⁻¹ * (a * y * a⁻¹)) * (y⁻¹ * (a * y * a⁻¹)) =
        y⁻¹ * ((a * y * a⁻¹) * y⁻¹) * (a * y * a⁻¹) := by group
      _ = y⁻¹ * (y⁻¹ * (a * y * a⁻¹)) * (a * y * a⁻¹) := by rw [h1]
      _ = (y * y)⁻¹ * ((a * y * a⁻¹) * (a * y * a⁻¹)) := by group
      _ = 1 := by rw [hsq, inv_mul_cancel]
  have hac : a * (y⁻¹ * (a * y * a⁻¹)) = (y⁻¹ * (a * y * a⁻¹)) * a := by
    have hcinv : (y⁻¹ * (a * y * a⁻¹))⁻¹ = y⁻¹ * (a * y * a⁻¹) := inv_eq_of_mul_eq_one_right hcc
    calc a * (y⁻¹ * (a * y * a⁻¹)) = (a * (y⁻¹ * (a * y * a⁻¹)) * a⁻¹) * a := by group
      _ = (y⁻¹ * (a * y * a⁻¹))⁻¹ * a := by
        congr 1
        have e1 : a * (y⁻¹ * (a * y * a⁻¹)) * a⁻¹ = a * y⁻¹ * a * y * (a * a)⁻¹ := by group
        have e2 : (y⁻¹ * (a * y * a⁻¹))⁻¹ = a * y⁻¹ * a⁻¹ * y := by group
        rw [e1, e2, haa, inv_one, mul_one, hainv]
      _ = (y⁻¹ * (a * y * a⁻¹)) * a := by rw [hcinv]
  by_cases ha1 : a = 1
  · rw [ha1]
    simp
  · exact mem_nrm.mpr ⟨hcB, D.setup.mem_normalizer_of_commute₁ haB ha1 hac.symm⟩

theorem conj_F₁_mem {y b : G} (hy : y ∈ A₀) (hb : b ∈ nrm B₁ B₀) :
    y * b * y⁻¹ * b⁻¹ ∈ nrm B₀ B₁ := by
  have h := D.conj_mem_mul_F₀ hy hb
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (D.invol₁ b hb)
  have hyB := D.A₀_le hy
  have hbN := (mem_nrm.mp hb).2
  have hy' : b * y * b⁻¹ ∈ B₀ := (Subgroup.mem_normalizer_iff.mp hbN y).mp hyB
  have e : y * b * y⁻¹ * b⁻¹ = (y⁻¹ * (b * y * b⁻¹))⁻¹ := by
    have h1 := D.setup.comm _ (B₀.inv_mem hyB) _ hy'
    calc y * b * y⁻¹ * b⁻¹ = y * (b * y⁻¹ * b⁻¹) := by group
      _ = y * (b * y * b⁻¹)⁻¹ := by group
      _ = ((b * y * b⁻¹) * y⁻¹)⁻¹ := by group
      _ = (y⁻¹ * (b * y * b⁻¹))⁻¹ := by rw [h1]
  rw [e]
  exact (nrm B₀ B₁).inv_mem h

theorem A₀_le_normalizer_Q :
    A₀ ≤ Subgroup.normalizer ((nrm B₀ B₁ ⊔ nrm B₁ B₀ : Subgroup G) : Set G) := by
  have key : ∀ y ∈ A₀, ∀ x ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀, y * x * y⁻¹ ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
    intro y hy x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := D.exists_mul_of_mem_Q hx
    have hya : y * a * y⁻¹ = a := by
      rw [D.setup.comm _ (D.A₀_le hy) _ (mem_nrm.mp ha).1, mul_inv_cancel_right]
    rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * ((y * b * y⁻¹ * b⁻¹) * b) by group, hya]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left (D.conj_F₁_mem hy hb)) (Subgroup.mem_sup_right hb))
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key y hy x
  · intro hx
    have := key y⁻¹ (A₀.inv_mem hy) _ hx
    rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this

theorem mem_F_of_commute {v x : G} (hv : v ∈ A₀) (hvF : v ∉ nrm B₀ B₁)
    (hx : x ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀) (hvx : v * x = x * v) : x ∈ nrm B₀ B₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := D.exists_mul_of_mem_Q hx
  by_cases hb1 : b = 1
  · rw [hb1, mul_one]
    exact ha
  exfalso
  apply hvF
  refine mem_nrm.mpr ⟨D.A₀_le hv, D.setup.mem_normalizer_of_commute₁ (mem_nrm.mp hb).1 hb1 ?_⟩
  have hva : v * a = a * v := D.setup.comm _ (D.A₀_le hv) _ (mem_nrm.mp ha).1
  calc v * b = a⁻¹ * (v * (a * b)) := by rw [← mul_assoc v a b, hva]; group
    _ = a⁻¹ * ((a * b) * v) := by rw [hvx]
    _ = b * v := by group

theorem F₁_le_A₁ : nrm B₁ B₀ ≤ A₁ := D.symm.F₀_le_A₀

theorem Q_le_R : nrm B₀ B₁ ⊔ nrm B₁ B₀ ≤ A₀ ⊔ A₁ := sup_le_sup D.F₀_le_A₀ D.F₁_le_A₁

theorem R_le_normalizer_Q :
    A₀ ⊔ A₁ ≤ Subgroup.normalizer ((nrm B₀ B₁ ⊔ nrm B₁ B₀ : Subgroup G) : Set G) := by
  refine sup_le D.A₀_le_normalizer_Q ?_
  have := D.symm.A₀_le_normalizer_Q
  rwa [sup_comm] at this

theorem normal_Q : ((nrm B₀ B₁ ⊔ nrm B₁ B₀).subgroupOf (A₀ ⊔ A₁)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer D.Q_le_R).mpr D.R_le_normalizer_Q

theorem mem_conj_F₀_iff {u z : G} (hu : u ∈ A₀ ⊔ A₁) :
    z ∈ conjSubgroup u (nrm B₀ B₁) ↔
      z ∈ conjSubgroup u B₀ ∧ z ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
  have huN := D.R_le_normalizer_Q hu
  have hQ : ∀ y : G, u⁻¹ * y * u ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ ↔ y ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
    intro y
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huN) y)
    rw [inv_inv] at this
    exact this.symm
  rw [mem_conjSubgroup, mem_conjSubgroup, ← hQ]
  constructor
  · intro h
    exact ⟨(mem_nrm.mp h).1, Subgroup.mem_sup_left h⟩
  · rintro ⟨h1, h2⟩
    exact D.mem_F₀_of_mem_Q h1 h2

theorem mem_conj_A₀_iff {u z : G} (hu : u ∈ A₀ ⊔ A₁) :
    z ∈ conjSubgroup u A₀ ↔
      z ∈ conjSubgroup u B₀ ∧ z * z ∈ conjSubgroup u B₀ ∧ z * z ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
  rw [← D.mem_conj_F₀_iff hu]
  simp only [mem_conjSubgroup, D.memA₀]
  rw [show u⁻¹ * z * u * (u⁻¹ * z * u) = u⁻¹ * (z * z) * u by group]

theorem mem_conj_F₀_of_commute {u v x : G} (hu : u ∈ A₀ ⊔ A₁) (hv : v ∈ conjSubgroup u A₀)
    (hvQ : v ∉ nrm B₀ B₁ ⊔ nrm B₁ B₀) (hx : x ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀) (hvx : v * x = x * v) :
    x ∈ conjSubgroup u (nrm B₀ B₁) := by
  have huN := D.R_le_normalizer_Q hu
  have hQ : ∀ y : G, u⁻¹ * y * u ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ ↔ y ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
    intro y
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huN) y)
    rw [inv_inv] at this
    exact this.symm
  rw [mem_conjSubgroup]
  refine D.mem_F_of_commute (mem_conjSubgroup.mp hv) (fun h => hvQ ?_) ((hQ x).mpr hx) ?_
  · exact (hQ v).mp (Subgroup.mem_sup_left h)
  · calc u⁻¹ * v * u * (u⁻¹ * x * u) = u⁻¹ * (v * x) * u := by group
      _ = u⁻¹ * (x * v) * u := by rw [hvx]
      _ = u⁻¹ * x * u * (u⁻¹ * v * u) := by group

omit [Finite G] in
theorem commute_conj {u v x : G} (hv : v ∈ conjSubgroup u A₀)
    (hx : x ∈ conjSubgroup u (nrm B₀ B₁)) : v * x = x * v := by
  have h := D.setup.comm _ (D.A₀_le (mem_conjSubgroup.mp hv)) _
    (mem_nrm.mp (mem_conjSubgroup.mp hx)).1
  calc v * x = u * ((u⁻¹ * v * u) * (u⁻¹ * x * u)) * u⁻¹ := by group
    _ = u * ((u⁻¹ * x * u) * (u⁻¹ * v * u)) * u⁻¹ := by rw [h]
    _ = x * v := by group

end QData

theorem eq_of_commute_mod {Q F F' B B' : Subgroup G} (hQc : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    {v w : G} (hvF : ∀ x ∈ F, v * x = x * v) (hcF : ∀ x ∈ Q, v * x = x * v → x ∈ F)
    (hcF' : ∀ x ∈ Q, w * x = x * w → x ∈ F') (hFQ : F ≤ Q) (hF1 : F ≠ ⊥) (hF2 : IsPGroup 2 F)
    (hFB : F ≤ B) (hF'B' : F' ≤ B') (hwN : w ∈ Subgroup.normalizer (Q : Set G))
    (hw2 : ∃ k : ℕ, w ^ 2 ^ k = 1) (hvw : v * w * (w * v)⁻¹ ∈ Q)
    (hBB' : B ⊓ B' ≠ ⊥ → B = B') : B = B' := by
  have hwF : ∀ x ∈ F, w * x * w⁻¹ ∈ F := by
    intro x hx
    have hxQ := hFQ hx
    have hyQ : w * x * w⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hwN x).mp hxQ
    refine hcF _ hyQ ?_
    set c := v * w * (w * v)⁻¹ with hc
    have hvw' : v * w = c * (w * v) := by rw [hc]; group
    have hcy := hQc c hvw _ hyQ
    have e : v * (w * x * w⁻¹) * v⁻¹ = c * (w * x * w⁻¹) * c⁻¹ := by
      calc v * (w * x * w⁻¹) * v⁻¹ = (v * w) * x * (v * w)⁻¹ := by group
        _ = (c * (w * v)) * x * (c * (w * v))⁻¹ := by rw [hvw']
        _ = c * w * (v * x) * v⁻¹ * w⁻¹ * c⁻¹ := by group
        _ = c * w * (x * v) * v⁻¹ * w⁻¹ * c⁻¹ := by rw [hvF x hx]
        _ = c * (w * x * w⁻¹) * c⁻¹ := by group
    calc v * (w * x * w⁻¹) = v * (w * x * w⁻¹) * v⁻¹ * v := by group
      _ = c * (w * x * w⁻¹) * c⁻¹ * v := by rw [e]
      _ = (w * x * w⁻¹) * v := by rw [hcy, mul_inv_cancel_right]
  have hwNF : w ∈ Subgroup.normalizer (F : Set G) := by
    rw [← conjSubgroup_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (card_conjSubgroup w F).ge
    intro y hy
    rw [mem_conjSubgroup] at hy
    have := hwF _ hy
    rwa [show w * (w⁻¹ * y * w) * w⁻¹ = y by group] at this
  obtain ⟨f, hf, hf1, hwf⟩ := exists_ne_one_commute' hF2 hF1 hw2 hwNF
  apply hBB'
  intro h
  have hfF' := hcF' f (hFQ hf) hwf
  have : f ∈ B ⊓ B' := Subgroup.mem_inf.mpr ⟨hFB hf, hF'B' hfF'⟩
  rw [h, Subgroup.mem_bot] at this
  exact hf1 this

@[expose] def IsSide (B₀ B₁ A₀ A₁ B A : Subgroup G) : Prop :=
  (B₀ = B ∧ A₀ = A) ∨ (B₁ = B ∧ A₁ = A)

namespace QData

variable {B₀ B₁ A₀ A₁ : Subgroup G} (D : QData B₀ B₁ A₀ A₁)
include D

omit D [Finite G] in
theorem isSide_left : IsSide B₀ B₁ A₀ A₁ B₀ A₀ := Or.inl ⟨rfl, rfl⟩

omit D [Finite G] in
theorem isSide_right : IsSide B₀ B₁ A₀ A₁ B₁ A₁ := Or.inr ⟨rfl, rfl⟩

omit [Finite G] in
theorem side_conj {B A : Subgroup G} (h : IsSide B₀ B₁ A₀ A₁ B A) (u : G) :
    ∃ k : G, conjSubgroup u B = conjSubgroup k B₀ := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact ⟨u, rfl⟩
  · obtain ⟨g, hg⟩ := D.setup.conj
    exact ⟨u * g, by rw [hg, conjSubgroup_mul]⟩

theorem side_memA {B A : Subgroup G} (h : IsSide B₀ B₁ A₀ A₁ B A) {u z : G} (hu : u ∈ A₀ ⊔ A₁) :
    z ∈ conjSubgroup u A ↔
      z ∈ conjSubgroup u B ∧ z * z ∈ conjSubgroup u B ∧ z * z ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact D.mem_conj_A₀_iff hu
  · have := D.symm.mem_conj_A₀_iff (u := u) (z := z) (by rwa [sup_comm])
    rwa [sup_comm (nrm B₁ B₀)] at this

theorem side_F {B A : Subgroup G} (h : IsSide B₀ B₁ A₀ A₁ B A) {u v : G} (hu : u ∈ A₀ ⊔ A₁)
    (hv : v ∈ conjSubgroup u A) (hvQ : v ∉ nrm B₀ B₁ ⊔ nrm B₁ B₀) :
    (∀ x ∈ conjSubgroup u B ⊓ (nrm B₀ B₁ ⊔ nrm B₁ B₀), v * x = x * v) ∧
      (∀ x ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀, v * x = x * v →
        x ∈ conjSubgroup u B ⊓ (nrm B₀ B₁ ⊔ nrm B₁ B₀)) ∧
      conjSubgroup u B ⊓ (nrm B₀ B₁ ⊔ nrm B₁ B₀) ≠ ⊥ ∧
      IsPGroup 2 (conjSubgroup u B ⊓ (nrm B₀ B₁ ⊔ nrm B₁ B₀) : Subgroup G) := by
  have h2 : ∀ x ∈ conjSubgroup u B ⊓ (nrm B₀ B₁ ⊔ nrm B₁ B₀), x * x = 1 := fun x hx =>
    D.sq_Q (Subgroup.mem_inf.mp hx).2
  refine ⟨?_, ?_, ?_, fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, sq]; exact h2 x x.2)⟩⟩
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro x hx
      exact D.commute_conj hv ((D.mem_conj_F₀_iff hu).mpr (Subgroup.mem_inf.mp hx))
    · intro x hx
      have hu' : u ∈ A₁ ⊔ A₀ := by rwa [sup_comm]
      refine D.symm.commute_conj hv ((D.symm.mem_conj_F₀_iff hu').mpr ?_)
      rw [sup_comm]
      exact Subgroup.mem_inf.mp hx
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro x hx hvx
      exact Subgroup.mem_inf.mpr ((D.mem_conj_F₀_iff hu).mp
        (D.mem_conj_F₀_of_commute hu hv hvQ hx hvx))
    · intro x hx hvx
      have hu' : u ∈ A₁ ⊔ A₀ := by rwa [sup_comm]
      have := (D.symm.mem_conj_F₀_iff hu').mp (D.symm.mem_conj_F₀_of_commute hu' hv
        (by rwa [sup_comm]) (by rwa [sup_comm]) hvx)
      rw [sup_comm] at this
      exact Subgroup.mem_inf.mpr this
  · intro hbot
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨⟨f, hf⟩, hf1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp D.F₀_ne_bot
      have hf1 : f ≠ 1 := fun h' => hf1' (Subtype.ext h')
      have hmem : u * f * u⁻¹ ∈ conjSubgroup u (nrm B₀ B₁) := by
        rw [mem_conjSubgroup, show u⁻¹ * (u * f * u⁻¹) * u = f by group]
        exact hf
      have := Subgroup.mem_inf.mpr ((D.mem_conj_F₀_iff hu).mp hmem)
      rw [hbot, Subgroup.mem_bot] at this
      exact hf1 (by rw [show f = u⁻¹ * (u * f * u⁻¹) * u by group, this]; group)
    · obtain ⟨⟨f, hf⟩, hf1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp D.symm.F₀_ne_bot
      have hf1 : f ≠ 1 := fun h' => hf1' (Subtype.ext h')
      have hu' : u ∈ A₁ ⊔ A₀ := by rwa [sup_comm]
      have hmem : u * f * u⁻¹ ∈ conjSubgroup u (nrm B₁ B₀) := by
        rw [mem_conjSubgroup, show u⁻¹ * (u * f * u⁻¹) * u = f by group]
        exact hf
      have h' := (D.symm.mem_conj_F₀_iff hu').mp hmem
      rw [sup_comm] at h'
      have := Subgroup.mem_inf.mpr h'
      rw [hbot, Subgroup.mem_bot] at this
      exact hf1 (by rw [show f = u⁻¹ * (u * f * u⁻¹) * u by group, this]; group)

theorem eq_of_commute_mod_side {B A B' A' : Subgroup G} (hs : IsSide B₀ B₁ A₀ A₁ B A)
    (hs' : IsSide B₀ B₁ A₀ A₁ B' A') {u h v w : G} (hu : u ∈ A₀ ⊔ A₁) (hh : h ∈ A₀ ⊔ A₁)
    (hv : v ∈ conjSubgroup u A) (hvQ : v ∉ nrm B₀ B₁ ⊔ nrm B₁ B₀) (hw : w ∈ conjSubgroup h A')
    (hwQ : w ∉ nrm B₀ B₁ ⊔ nrm B₁ B₀) (hvw : v * w * (w * v)⁻¹ ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀) :
    conjSubgroup u B = conjSubgroup h B' := by
  obtain ⟨hvF, hcF, hF1, hF2⟩ := D.side_F hs hu hv hvQ
  obtain ⟨-, hcF', -, -⟩ := D.side_F hs' hh hw hwQ
  have hwR : w ∈ A₀ ⊔ A₁ := by
    have := (D.side_memA hs' hh).mp hw
    rcases hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hw' : h⁻¹ * w * h ∈ A₀ := mem_conjSubgroup.mp hw
      rw [show w = h * (h⁻¹ * w * h) * h⁻¹ by group]
      exact (A₀ ⊔ A₁).mul_mem ((A₀ ⊔ A₁).mul_mem hh (Subgroup.mem_sup_left hw'))
        ((A₀ ⊔ A₁).inv_mem hh)
    · have hw' : h⁻¹ * w * h ∈ A₁ := mem_conjSubgroup.mp hw
      rw [show w = h * (h⁻¹ * w * h) * h⁻¹ by group]
      exact (A₀ ⊔ A₁).mul_mem ((A₀ ⊔ A₁).mul_mem hh (Subgroup.mem_sup_right hw'))
        ((A₀ ⊔ A₁).inv_mem hh)
  have hw2 : ∃ k : ℕ, w ^ 2 ^ k = 1 := by
    have hwB : w ∈ conjSubgroup h B' := ((D.side_memA hs' hh).mp hw).1
    obtain ⟨k, hk⟩ := D.side_conj hs' h
    rw [hk] at hwB
    obtain ⟨n, hn⟩ := D.setup.pow_two_pow_eq_one (mem_conjSubgroup.mp hwB)
    refine ⟨n, ?_⟩
    rw [show (k⁻¹ * w * k) ^ 2 ^ n = k⁻¹ * w ^ 2 ^ n * k by
      simpa using conj_pow (a := k⁻¹) (b := w) (i := 2 ^ n)] at hn
    calc w ^ 2 ^ n = k * (k⁻¹ * w ^ 2 ^ n * k) * k⁻¹ := by group
      _ = 1 := by rw [hn]; group
  refine eq_of_commute_mod (fun x hx y hy => D.comm_Q hx hy) hvF hcF hcF' inf_le_right hF1 hF2
    inf_le_left inf_le_left (D.R_le_normalizer_Q hwR) hw2 hvw ?_
  intro hne
  obtain ⟨k, hk⟩ := D.side_conj hs u
  obtain ⟨k', hk'⟩ := D.side_conj hs' h
  rw [hk, hk'] at hne ⊢
  exact conjSubgroup_eq_of_inf_ne_bot D.setup.ti hne

theorem side_A_eq {B A B' A' : Subgroup G} (hs : IsSide B₀ B₁ A₀ A₁ B A)
    (hs' : IsSide B₀ B₁ A₀ A₁ B' A') {u h : G}
    (hu : u ∈ A₀ ⊔ A₁) (hh : h ∈ A₀ ⊔ A₁) (he : conjSubgroup u B = conjSubgroup h B') :
    conjSubgroup u A = conjSubgroup h A' := by
  ext z
  rw [D.side_memA hs hu, D.side_memA hs' hh, he]

section Quot

variable [((nrm B₀ B₁ ⊔ nrm B₁ B₀).subgroupOf (A₀ ⊔ A₁)).Normal]

local notation "πq" =>
  QuotientGroup.mk' (Subgroup.subgroupOf (nrm B₀ B₁ ⊔ nrm B₁ B₀) (A₀ ⊔ A₁))

omit D [Finite G] in
theorem mk_eq_one_iff (y : ↥(A₀ ⊔ A₁)) : πq y = 1 ↔ (y : G) ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem commute_mod {v w : ↥(A₀ ⊔ A₁)} (h : πq v * πq w = πq w * πq v) :
    (v : G) * w * ((w : G) * v)⁻¹ ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
  rw [← map_mul, ← map_mul] at h
  have h1 := QuotientGroup.eq.mp h
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : ((w : G) * v)⁻¹ * ((v : G) * w) ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
    have := Subgroup.inv_mem _ h1
    simpa [mul_assoc] using this
  have hN := D.R_le_normalizer_Q ((A₀ ⊔ A₁).mul_mem w.2 v.2)
  have := (Subgroup.mem_normalizer_iff.mp hN _).mp h2
  rwa [show (w : G) * v * (((w : G) * v)⁻¹ * ((v : G) * w)) * ((w : G) * v)⁻¹ =
    (v : G) * w * ((w : G) * v)⁻¹ by group] at this

omit D [Finite G] in
theorem conj_image (u : ↥(A₀ ⊔ A₁)) (A : Subgroup G) :
    conjSubgroup (πq u) ((A.subgroupOf (A₀ ⊔ A₁)).map πq) =
      ((conjSubgroup (u : G) A).subgroupOf (A₀ ⊔ A₁)).map πq := by
  rw [← map_conjSubgroup]
  congr 1
  ext x
  rw [mem_conjSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conjSubgroup]
  rfl

theorem elem_image {B A : Subgroup G} (hs : IsSide B₀ B₁ A₀ A₁ B A) :
    IsElemAbelian 2 ((A.subgroupOf (A₀ ⊔ A₁)).map πq) := by
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fun x hx y hy => D.setup.comm x (D.A₀_le hx) y (D.A₀_le hy)
    · exact fun x hx y hy => D.setup.comm₁ x (D.symm.A₀_le hx) y (D.symm.A₀_le hy)
  have hsq : ∀ x ∈ A, x * x ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fun x hx => Subgroup.mem_sup_left ((D.memA₀ x).mp hx).2
    · exact fun x hx => Subgroup.mem_sup_right ((D.memA₁ x).mp hx).2
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp ha') _ (Subgroup.mem_subgroupOf.mp hb'))
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, sq, (mk_eq_one_iff _)]
    exact hsq _ (Subgroup.mem_subgroupOf.mp hx')

theorem image_ne_bot {B A : Subgroup G} (hs : IsSide B₀ B₁ A₀ A₁ B A) :
    (A.subgroupOf (A₀ ⊔ A₁)).map πq ≠ ⊥ := by
  obtain ⟨z, hzA, hzQ⟩ : ∃ z ∈ A, z ∉ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨z, hz, hzF⟩ := D.neA₀
      exact ⟨z, hz, fun h => hzF (D.mem_F₀_of_mem_Q (D.A₀_le hz) h)⟩
    · obtain ⟨z, hz, hzF⟩ := D.neA₁
      exact ⟨z, hz, fun h => hzF (D.symm.mem_F₀_of_mem_Q (D.symm.A₀_le hz) (by rwa [sup_comm]))⟩
  have hzR : z ∈ A₀ ⊔ A₁ := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Subgroup.mem_sup_left hzA
    · exact Subgroup.mem_sup_right hzA
  intro h
  have : πq ⟨z, hzR⟩ ∈ (A.subgroupOf (A₀ ⊔ A₁)).map πq := ⟨⟨z, hzR⟩, hzA, rfl⟩
  rw [h, Subgroup.mem_bot, mk_eq_one_iff] at this
  exact hzQ this

theorem quotPair :
    QuotPair ((A₀.subgroupOf (A₀ ⊔ A₁)).map πq) ((A₁.subgroupOf (A₀ ⊔ A₁)).map πq) := by
  have hπs : Function.Surjective πq := QuotientGroup.mk'_surjective _
  have hmem : ∀ {B A : Subgroup G}, IsSide B₀ B₁ A₀ A₁ B A → ∀ (u : ↥(A₀ ⊔ A₁)) (x),
      x ∈ conjSubgroup (πq u) ((A.subgroupOf (A₀ ⊔ A₁)).map πq) → x ≠ 1 →
      ∃ y : ↥(A₀ ⊔ A₁), (y : G) ∈ conjSubgroup (u : G) A ∧
        (y : G) ∉ nrm B₀ B₁ ⊔ nrm B₁ B₀ ∧ πq y = x := by
    intro B A hs u x hx hx1
    rw [conj_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, fun h => hx1 ((mk_eq_one_iff y).mpr h), rfl⟩
  have hkey : ∀ {B A B' A' : Subgroup G}, IsSide B₀ B₁ A₀ A₁ B A → IsSide B₀ B₁ A₀ A₁ B' A' →
      ∀ u h : ↥(A₀ ⊔ A₁), ∀ x ∈ conjSubgroup (πq u) ((A.subgroupOf (A₀ ⊔ A₁)).map πq), x ≠ 1 →
      ∀ y ∈ conjSubgroup (πq h) ((A'.subgroupOf (A₀ ⊔ A₁)).map πq), y ≠ 1 → x * y = y * x →
      conjSubgroup (πq u) ((A.subgroupOf (A₀ ⊔ A₁)).map πq) =
        conjSubgroup (πq h) ((A'.subgroupOf (A₀ ⊔ A₁)).map πq) := by
    intro B A B' A' hs hs' u h x hx hx1 y hy hy1 hxy
    obtain ⟨v, hv, hvQ, rfl⟩ := hmem hs u x hx hx1
    obtain ⟨w, hw, hwQ, rfl⟩ := hmem hs' h y hy hy1
    have he := D.eq_of_commute_mod_side hs hs' u.2 h.2 hv hvQ hw hwQ (D.commute_mod hxy)
    rw [conj_image, conj_image, D.side_A_eq hs hs' u.2 h.2 he]
  refine ⟨D.elem_image isSide_left, D.elem_image isSide_right, D.image_ne_bot isSide_left,
    D.image_ne_bot isSide_right, ?_, ?_, ?_⟩
  · intro hTT
    obtain ⟨⟨t, ht⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (D.image_ne_bot isSide_left)
    have ht1 : t ≠ 1 := fun h' => ht1' (Subtype.ext h')
    have h1 := hkey isSide_left isSide_right 1 1 t (by rw [map_one, conjSubgroup_one]; exact ht)
      ht1 t (by rw [map_one, conjSubgroup_one, ← hTT]; exact ht) ht1 rfl
    rw [map_one, conjSubgroup_one, conjSubgroup_one] at h1
    obtain ⟨v, hv, hvQ, hvt⟩ := hmem isSide_left 1 t (by rw [map_one, conjSubgroup_one]; exact ht)
      ht1
    obtain ⟨w, hw, hwQ, hwt⟩ := hmem isSide_right 1 t (by
      rw [map_one, conjSubgroup_one, ← hTT]; exact ht) ht1
    have hvw : πq v * πq w = πq w * πq v := by rw [hvt, hwt]
    have he := D.eq_of_commute_mod_side isSide_left isSide_right (A₀ ⊔ A₁).one_mem
      (A₀ ⊔ A₁).one_mem hv hvQ hw hwQ (D.commute_mod hvw)
    rw [conjSubgroup_one, conjSubgroup_one] at he
    exact D.ne he
  · rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ hπs]
  · rintro U ⟨ub, rfl | rfl⟩ V ⟨vb, rfl | rfl⟩ x hx hx1 y hy hy1 hxy <;>
    obtain ⟨u, rfl⟩ := hπs ub <;> obtain ⟨h, rfl⟩ := hπs vb
    · exact hkey isSide_left isSide_left u h x hx hx1 y hy hy1 hxy
    · exact hkey isSide_left isSide_right u h x hx hx1 y hy hy1 hxy
    · exact hkey isSide_right isSide_left u h x hx hx1 y hy hy1 hxy
    · exact hkey isSide_right isSide_right u h x hx hx1 y hy hy1 hxy

theorem card_image_mul :
    Nat.card ((A₀.subgroupOf (A₀ ⊔ A₁)).map πq) * Nat.card (nrm B₀ B₁) = Nat.card A₀ := by
  set φ := MonoidHom.comp πq (A₀.subgroupOf (A₀ ⊔ A₁)).subtype with hφ
  have hrange : φ.range = (A₀.subgroupOf (A₀ ⊔ A₁)).map πq := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card φ.ker = Nat.card (nrm B₀ B₁) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨((y : ↥(A₀ ⊔ A₁)) : G), ?_⟩
        invFun := fun l => ⟨⟨⟨l, Subgroup.mem_sup_left (D.F₀_le_A₀ l.2)⟩, D.F₀_le_A₀ l.2⟩, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun l => rfl }
    · have hy : πq ((y : ↥(A₀.subgroupOf (A₀ ⊔ A₁))) : ↥(A₀ ⊔ A₁)) = 1 := y.2
      rw [mk_eq_one_iff] at hy
      exact D.mem_F₀_of_mem_Q (D.A₀_le (Subgroup.mem_subgroupOf.mp y.1.2)) hy
    · show πq _ = 1
      rw [mk_eq_one_iff]
      exact Subgroup.mem_sup_left l.2
  have hdom : Nat.card ↥(A₀.subgroupOf (A₀ ⊔ A₁)) = Nat.card A₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, hker, hdom] at h1
  rw [mul_comm]
  exact h1

theorem relIndex_eq_card_image :
    (nrm B₀ B₁).relIndex A₀ = Nat.card ((A₀.subgroupOf (A₀ ⊔ A₁)).map πq) := by
  have h1 := Subgroup.relIndex_mul_card (H := nrm B₀ B₁) (K := A₀)
  rw [inf_of_le_left D.F₀_le_A₀, ← D.card_image_mul] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

end Quot

end QData

end CFSG.RankThree.GF2n.Tim78
