module

public import CFSG.RankThree.PartOne.KC.SymplecticTorus
public import CFSG.RankThree.PartOne.KC.SymplecticInnerActorCenter

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

variable {r : ℕ} {K : Type} [Field K]

theorem conj_mem_inSubgroup_core {G : Type*} [Group G] (q : ℕ) (C : Subgroup G) {g s : G}
    (hg : g ∈ C) (hs : s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore q) C) :
    g * s * g⁻¹ ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore q) C := by
  obtain ⟨s', hs', rfl⟩ := hs
  refine ⟨⟨g, hg⟩ * s' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  exact (inferInstance : (CFSG.RankThree.LocalRank.aschbacherSolvableCore q C).Normal).conj_mem
    s' hs' ⟨g, hg⟩

theorem inSubgroup_core_le {G : Type*} [Group G] (q : ℕ) (C : Subgroup G) :
    CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore q) C ≤ C :=
  Subgroup.map_subtype_le _

theorem mem_of_odd_orderOf_of_index_dvd_two {G : Type*} [Group G] (E : Subgroup G)
    (hE : E.index ∣ 2) {a : G} (ha : Odd (orderOf a)) : a ∈ E := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hE with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    rw [h1]
    exact Subgroup.mem_top a
  · have : E.Normal := Subgroup.normal_of_index_eq_two h2
    have hq2 : (QuotientGroup.mk a : G ⧸ E) ^ 2 = 1 := by
      have h3 := pow_card_eq_one' (x := (QuotientGroup.mk a : G ⧸ E))
      have h4 : Nat.card (G ⧸ E) = 2 := h2
      rwa [h4] at h3
    have hqn : (QuotientGroup.mk a : G ⧸ E) ^ orderOf a = 1 := by
      rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]
      rfl
    have hcop : Nat.Coprime 2 (orderOf a) := Nat.coprime_two_left.mpr ha
    have hdvd : orderOf (QuotientGroup.mk a : G ⧸ E) ∣ Nat.gcd 2 (orderOf a) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq2) (orderOf_dvd_of_pow_eq_one hqn)
    rw [hcop] at hdvd
    exact (QuotientGroup.eq_one_iff a).mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))

section Center

variable {ℓ f p : ℕ} {x : StatedSp r K}

theorem spCentralizerD_eq (D : SpData ℓ f r p K x) :
    spCentralizerD r K (conjAut r K (spXg x)) =
      (Subgroup.centralizer ({spXg x} : Set (gsp r K))).map (conjAut r K) := by
  have : Finite K := D.finite
  exact conjAut_range_inf_centralizer_eq_map D.one_le_r D.odd D.pow_eq_one

theorem spCenterN_eq_center (D : SpData ℓ f r p K x) :
    spCenterN r K (conjAut r K (spXg x)) =
      (Subgroup.center ↥((Subgroup.centralizer ({spXg x} : Set (gsp r K))).map
        (conjAut r K))).map ((Subgroup.centralizer ({spXg x} : Set (gsp r K))).map
          (conjAut r K)).subtype := by
  have key : ∀ N' : Subgroup (MulAut (StatedProj (StatedSp r K))),
      spCentralizerD r K (conjAut r K (spXg x)) = N' →
      spCenterN r K (conjAut r K (spXg x)) = (Subgroup.center ↥N').map N'.subtype := by
    intro N' hN'
    subst hN'
    rfl
  exact key _ (spCentralizerD_eq D)

theorem spCenterN_eq (D : SpData ℓ f r p K x) (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (B : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range ≤ B) :
    spCenterN r K (conjAut r K (spXg x)) = (spCenterUnits x).map (conjAut r K) := by
  have : Finite K := D.finite
  have : NeZero r := D.neZero
  rw [spCenterN_eq_center D]
  exact (spProjSetting D blocks B hB).center_image_eq

theorem spQ0_comm (D : SpData ℓ f r p K x) {a b : MulAut (StatedProj (StatedSp r K))}
    (ha : a ∈ spCenterN r K (conjAut r K (spXg x)))
    (hb : b ∈ spCenterN r K (conjAut r K (spXg x))) : a * b = b * a := by
  rw [spCenterN_eq_center D] at ha hb
  exact ProjSetting.center_inf_comm ha hb

theorem spQ0_normal (D : SpData ℓ f r p K x) (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (B : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range ≤ B) :
    ((spCenterN r K (conjAut r K (spXg x)) ⊓ (B ⊓ Subgroup.centralizer
        ({conjAut r K (spXg x)} : Set (MulAut (StatedProj (StatedSp r K)))))).subgroupOf
      (B ⊓ Subgroup.centralizer
        ({conjAut r K (spXg x)} : Set (MulAut (StatedProj (StatedSp r K)))))).Normal := by
  have : Finite K := D.finite
  have : NeZero r := D.neZero
  rw [spCenterN_eq_center D]
  exact (spProjSetting D blocks B hB).center_inf_normal

end Center

section Odd

variable {ℓ f p : ℕ} {x : StatedSp r K}

theorem spCommutator_mem_odd (D : SpData ℓ f r p K x)
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (B : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range ≤ B)
    {A : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hAB : A ≤ B ⊓ Subgroup.centralizer
      ({conjAut r K (spXg x)} : Set (MulAut (StatedProj (StatedSp r K)))))
    (hA : IsPGroup p ↥A) {s a : MulAut (StatedProj (StatedSp r K))}
    (hs : s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer
        ({conjAut r K (spXg x)} : Set (MulAut (StatedProj (StatedSp r K))))))
    (ha : a ∈ A) :
    ⁅s, a⁆ ∈ spCenterN r K (conjAut r K (spXg x)) ⊓ (B ⊓ Subgroup.centralizer
      ({conjAut r K (spXg x)} : Set (MulAut (StatedProj (StatedSp r K))))) ∧
      Odd (orderOf ⁅s, a⁆) := by
  have : Finite K := D.finite
  have : NeZero r := D.neZero
  have S := spProjSetting D blocks B hB
  set t := conjAut r K (spXg x) with ht
  set CB := B ⊓ Subgroup.centralizer ({t} : Set (MulAut (StatedProj (StatedSp r K)))) with hCB
  have haCB : a ∈ CB := hAB ha
  have hsCB : s ∈ CB := inSubgroup_core_le p _ hs
  have hsa : ⁅s, a⁆ ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p) CB := by
    have h1 := conj_mem_inSubgroup_core p _ haCB (inv_mem hs)
    have h2 : ⁅s, a⁆ = s * (a * s⁻¹ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact mul_mem hs h1
  have hsaCB : ⁅s, a⁆ ∈ CB := inSubgroup_core_le p _ hsa
  have hsaD : ⁅s, a⁆ ∈ (conjAut r K).range := (spDescent D).2.1 s a
  have hsaN : ⁅s, a⁆ ∈ (Subgroup.centralizer ({spXg x} : Set (gsp r K))).map (conjAut r K) := by
    rw [← S.N_eq]
    exact Subgroup.mem_inf.mpr ⟨hsaD, (Subgroup.mem_inf.mp hsaCB).2⟩
  have hcent := S.core_le_centralizer_derived D.prime hsa
  have hcQ : ⁅s, a⁆ ∈ spCenterN r K t := by
    rw [spCenterN_eq D blocks B hB, ← S.inf_centralizer_derived_eq]
    exact Subgroup.mem_inf.mpr ⟨hsaN, hcent⟩
  refine ⟨Subgroup.mem_inf.mpr ⟨hcQ, hsaCB⟩, ?_⟩
  let Q₀ : Subgroup (MulAut (StatedProj (StatedSp r K))) := spCenterN r K t ⊓ CB
  have hfinQ : Finite ↥Q₀ := inferInstance
  have hcomm : ∀ z₁ ∈ Q₀, ∀ z₂ ∈ Q₀, Commute z₁ z₂ := fun z₁ h₁ z₂ h₂ =>
    spQ0_comm D (Subgroup.mem_inf.mp h₁).1 (Subgroup.mem_inf.mp h₂).1
  have hσQ : ∀ z ∈ Q₀, (MulAut.conj a) z ∈ Q₀ := by
    intro z hz
    have hz' := Subgroup.mem_inf.mp hz
    have hnorm := spQ0_normal D blocks B hB
    have h2 := hnorm.conj_mem (⟨z, hz'.2⟩ : CB) (Subgroup.mem_subgroupOf.mpr hz) ⟨a, haCB⟩
    exact Subgroup.mem_subgroupOf.mp h2
  have hm : Odd (orderOf a) := by
    have hord : orderOf (⟨a, ha⟩ : ↥A) = orderOf a := Subgroup.orderOf_mk a ha
    obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow D.prime).mp (orderOf_dvd_of_pow_eq_one hk)
    rw [← hord, hj]
    exact D.odd.pow
  have haE : a ∈ spSemilinearAutGroup r K :=
    mem_of_odd_orderOf_of_index_dvd_two _ (spDescent D).2.2 hm
  have hat : a * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp haCB.2
  obtain ⟨j, hj⟩ := hA ⟨a, ha⟩
  have haj : a ^ p ^ j = 1 := congrArg Subtype.val hj
  have hfixσ : ∀ z ∈ Q₀, ∀ k : ℕ, z ^ 2 ^ k = 1 → (MulAut.conj a) z = z := by
    intro z hz k hk
    have hzN := (Subgroup.mem_inf.mp hz).1
    rw [spCenterN_eq D blocks B hB] at hzN
    obtain ⟨u, hu, rfl⟩ := hzN
    have h1 := spA_conj_eq_of_two_pow D.one_le_r D.prime D.odd D.pow_eq_one D.squarefree haE hat
      haj hu hk
    rw [MulAut.conj_apply]
    exact h1
  have hσm : (MulAut.conj a) ^ orderOf a = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hc : s * ((MulAut.conj a) s)⁻¹ ∈ Q₀ := by
    have : s * ((MulAut.conj a) s)⁻¹ = ⁅s, a⁆ := by
      simp only [MulAut.conj_apply, commutatorElement_def]
      group
    rw [this]
    exact Subgroup.mem_inf.mpr ⟨hcQ, hsaCB⟩
  have hodd := odd_orderOf_of_fixed_two_part (MulAut.conj a) Q₀
    (fun z₁ h₁ z₂ h₂ => (hcomm z₁ h₁ z₂ h₂ : Commute z₁ z₂)) hσQ hfixσ hm hσm s hc
  have : s * ((MulAut.conj a) s)⁻¹ = ⁅s, a⁆ := by
    simp only [MulAut.conj_apply, commutatorElement_def]
    group
  rwa [this] at hodd

end Odd

end CFSG.RankThree.PartOne.KCSpComm
