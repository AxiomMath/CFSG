module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69Setup
import TauCeti.Algebra.Group.Subgroup.ModularLaw
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data calC)

variable {G : Type} [Group G] [Finite G]

open scoped commutatorElement

omit [Finite G] in
private lemma eight70_card_eq_sixty_of_alt5 {H : Subgroup G}
    (h : Nonempty (↥H ≃* alternatingGroup (Fin 5))) : Nat.card ↥H = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num

omit [Finite G] in
private lemma eight70_center_eq_bot_of_alt5 {H : Subgroup G}
    (h : Nonempty (↥H ≃* alternatingGroup (Fin 5))) :
    Subgroup.center ↥H = ⊥ := by
  obtain ⟨e⟩ := h
  have hmap : (Subgroup.center ↥H).map e.toMonoidHom = ⊥ := by
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.map_center_eq,
      alternatingGroup.center_eq_bot (by norm_num)]
  have hmap' : (Subgroup.center ↥H).map e.toMonoidHom =
      (⊥ : Subgroup ↥H).map e.toMonoidHom := by
    rw [hmap, Subgroup.map_bot]
  exact Subgroup.map_injective e.injective hmap'

private lemma eight70_not_isPGroup_two_of_alt5 {H : Subgroup G}
    (h : Nonempty (↥H ≃* alternatingGroup (Fin 5))) :
    ¬ IsPGroup 2 ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hp
  have h3 : 3 ∣ Nat.card ↥H := by
    rw [eight70_card_eq_sixty_of_alt5 h]
    norm_num
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at h3
  have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
  norm_num at h32

omit [Finite G] in
private lemma eight70_not_isMulCommutative_of_alt5 {H : Subgroup G}
    (h : Nonempty (↥H ≃* alternatingGroup (Fin 5))) :
    ¬ IsMulCommutative ↥H := by
  intro hcomm
  have : IsMulCommutative ↥H := hcomm
  have hsimple : IsSimpleGroup ↥H := by
    obtain ⟨e⟩ := h
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
    exact e.isSimpleGroup
  have hp : (Nat.card ↥H).Prime := (Group.is_simple_iff_prime_card).mp hsimple
  rw [eight70_card_eq_sixty_of_alt5 h] at hp
  norm_num at hp

private lemma eight70_pRank_alt5_le_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (alternatingGroup (Fin 5))) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt (k := 1) ?_
  intro E _hE hEab
  have hEp : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hEab
  obtain ⟨m, hm⟩ := hEp.exists_card_eq
  have hcard60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hdvd : p ^ m ∣ 60 := by
    have h := Subgroup.card_subgroup_dvd_card E
    rwa [hm, hcard60] at h
  have hm1 : m ≤ 1 := by
    by_contra hmle
    have hm2 : 2 ≤ m := by omega
    have hp2dvd : p ^ 2 ∣ p ^ m := Nat.pow_dvd_pow p hm2
    have hp2dvd60 : p ^ 2 ∣ 60 := hp2dvd.trans hdvd
    have hp2le : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) hp2dvd60
    have hple : p ≤ 7 := by
      by_contra h
      have h8 : 8 ≤ p := by omega
      have h64 : 8 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h8 2
      norm_num at h64
      omega
    have hp3le : 3 ≤ p := (Nat.Prime.odd_iff hp).mp (hp.odd_of_ne_two hp2)
    interval_cases p <;> norm_num at hp2dvd60
  rw [hm]
  exact Nat.pow_le_pow_right hp.pos hm1

omit [Finite G] in
private lemma eight70_le_normalizer_left {X X₁ X₂ : Subgroup G}
    (hsup : X₁ ⊔ X₂ = X)
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x) :
    X ≤ Subgroup.normalizer (X₁ : Set G) := by
  have hconj : ∀ w ∈ X₂, ∀ z ∈ X₁, w * z * w⁻¹ ∈ X₁ := by
    intro w hw z hz
    have h : w * z * w⁻¹ = z := by
      rw [← hcomm z hz w hw]
      group
    rw [h]
    exact hz
  rw [← hsup]
  refine sup_le Subgroup.le_normalizer ?_
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hconj y hy z
  · intro hz
    have h := hconj y⁻¹ (X₂.inv_mem hy) (y * z * y⁻¹) hz
    have h' : y⁻¹ * (y * z * y⁻¹) * (y⁻¹)⁻¹ = z := by group
    rw [h'] at h
    exact h

omit [Finite G] in
private lemma eight70_le_normalizer_right {X X₁ X₂ : Subgroup G}
    (hsup : X₁ ⊔ X₂ = X)
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x) :
    X ≤ Subgroup.normalizer (X₂ : Set G) := by
  refine eight70_le_normalizer_left (X₁ := X₂) (X₂ := X₁) ?_ ?_
  · rw [sup_comm, hsup]
  · intro x hx y hy
    exact (hcomm y hy x hx).symm

omit [Finite G] in
private lemma eight70_normal_dichotomy {X X₁ X₂ N : Subgroup G}
    (hsup : X₁ ⊔ X₂ = X)
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (h₁ : Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)))
    (h₂ : Nonempty (↥X₂ ≃* alternatingGroup (Fin 5)))
    (hN : N ≤ X) (hNnorm : X ≤ Subgroup.normalizer (N : Set G)) :
    N = ⊥ ∨ X₁ ≤ N ∨ X₂ ≤ N := by
  have hX₁le : X₁ ≤ X := hsup ▸ le_sup_left
  have hX₂le : X₂ ≤ X := hsup ▸ le_sup_right
  have hX₁norm : X ≤ Subgroup.normalizer (X₁ : Set G) :=
    eight70_le_normalizer_left hsup hcomm
  have hX₂norm : X ≤ Subgroup.normalizer (X₂ : Set G) :=
    eight70_le_normalizer_right hsup hcomm
  have hN₁norm : ((N ⊓ X₁).subgroupOf X₁).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
    refine (le_inf (hX₁le.trans hNnorm) (hX₁le.trans hX₁norm)).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
  have hN₂norm : ((N ⊓ X₂).subgroupOf X₂).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
    refine (le_inf (hX₂le.trans hNnorm) (hX₂le.trans hX₂norm)).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hsimple₁ : IsSimpleGroup ↥X₁ := h₁.some.isSimpleGroup
  have hsimple₂ : IsSimpleGroup ↥X₂ := h₂.some.isSimpleGroup
  have hcases₁ : N ⊓ X₁ = ⊥ ∨ X₁ ≤ N := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ((N ⊓ X₁).subgroupOf X₁) with h | h
    · left
      have h' : (N ⊓ X₁).subgroupOf X₁ = (⊥ : Subgroup G).subgroupOf X₁ := by simpa using h
      simpa using (Subgroup.subgroupOf_inj.mp h')
    · right
      exact (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left
  have hcases₂ : N ⊓ X₂ = ⊥ ∨ X₂ ≤ N := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ((N ⊓ X₂).subgroupOf X₂) with h | h
    · left
      have h' : (N ⊓ X₂).subgroupOf X₂ = (⊥ : Subgroup G).subgroupOf X₂ := by simpa using h
      simpa using (Subgroup.subgroupOf_inj.mp h')
    · right
      exact (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left
  rcases hcases₁ with h₁bot | h₁le
  · rcases hcases₂ with h₂bot | h₂le
    · left
      have hcommN₁ : ⁅N, X₁⁆ ≤ N ⊓ X₁ := by
        rw [Subgroup.commutator_le]
        intro n hn x hx
        refine ⟨?_, ?_⟩
        · have hconj : x * n⁻¹ * x⁻¹ ∈ N :=
            (Subgroup.mem_normalizer_iff.mp (hNnorm (hX₁le hx)) n⁻¹).mp (N.inv_mem hn)
          have hmem : n * (x * n⁻¹ * x⁻¹) ∈ N := N.mul_mem hn hconj
          simpa [commutatorElement_def, mul_assoc] using hmem
        · have hconj : n * x * n⁻¹ ∈ X₁ :=
            (Subgroup.mem_normalizer_iff.mp (hX₁norm (hN hn)) x).mp hx
          have hmem : n * x * n⁻¹ * x⁻¹ ∈ X₁ := X₁.mul_mem hconj (X₁.inv_mem hx)
          simpa [commutatorElement_def, mul_assoc] using hmem
      have hcommN₁_bot : ⁅N, X₁⁆ = ⊥ := le_bot_iff.mp (h₁bot ▸ hcommN₁)
      have hcent₁ : N ≤ Subgroup.centralizer (X₁ : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommN₁_bot
      have hcommN₂ : ⁅N, X₂⁆ ≤ N ⊓ X₂ := by
        rw [Subgroup.commutator_le]
        intro n hn x hx
        refine ⟨?_, ?_⟩
        · have hconj : x * n⁻¹ * x⁻¹ ∈ N :=
            (Subgroup.mem_normalizer_iff.mp (hNnorm (hX₂le hx)) n⁻¹).mp (N.inv_mem hn)
          have hmem : n * (x * n⁻¹ * x⁻¹) ∈ N := N.mul_mem hn hconj
          simpa [commutatorElement_def, mul_assoc] using hmem
        · have hconj : n * x * n⁻¹ ∈ X₂ :=
            (Subgroup.mem_normalizer_iff.mp (hX₂norm (hN hn)) x).mp hx
          have hmem : n * x * n⁻¹ * x⁻¹ ∈ X₂ := X₂.mul_mem hconj (X₂.inv_mem hx)
          simpa [commutatorElement_def, mul_assoc] using hmem
      have hcommN₂_bot : ⁅N, X₂⁆ = ⊥ := le_bot_iff.mp (h₂bot ▸ hcommN₂)
      have hcent₂ : N ≤ Subgroup.centralizer (X₂ : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommN₂_bot
      have hmem_center : ∀ n ∈ N, n = 1 := by
        intro n hn
        have hnX : n ∈ X := hN hn
        have hX₂normal : (X₂.subgroupOf X).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hX₂le).mpr hX₂norm
        have hsupX : (X₁.subgroupOf X) ⊔ (X₂.subgroupOf X) = ⊤ := by
          apply Subgroup.map_injective X.subtype_injective
          rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hX₁le,
            inf_eq_left.mpr hX₂le, hsup, Subgroup.map_top, Subgroup.range_subtype]
        have hmem : (⟨n, hnX⟩ : ↥X) ∈ (X₁.subgroupOf X) ⊔ (X₂.subgroupOf X) := by
          rw [hsupX]
          exact Subgroup.mem_top _
        obtain ⟨y, hy, z, hz, hyz⟩ :=
          (Subgroup.mem_sup_of_normal_right (s := X₁.subgroupOf X)
            (t := X₂.subgroupOf X)).mp hmem
        let x₁ : G := y
        let x₂ : G := z
        have hx₁ : x₁ ∈ X₁ := hy
        have hx₂ : x₂ ∈ X₂ := hz
        have hprod : x₁ * x₂ = n := by
          have h := congrArg Subtype.val hyz
          simpa [x₁, x₂] using h
        have hx₁_center : (⟨x₁, hx₁⟩ : ↥X₁) ∈ Subgroup.center ↥X₁ := by
          rw [Subgroup.mem_center_iff]
          intro g
          apply Subtype.ext
          show (g : G) * x₁ = x₁ * (g : G)
          have hncomm : (g : G) * n = n * (g : G) :=
            (Subgroup.mem_centralizer_iff.mp (hcent₁ hn)) (g : G) g.2
          have hmain : (g : G) * (x₁ * x₂) = (x₁ * x₂) * (g : G) := by
            rw [hprod]
            exact hncomm
          have h2 : (g : G) * x₁ * x₂ = x₁ * (g : G) * x₂ := by
            calc (g : G) * x₁ * x₂ = (g : G) * (x₁ * x₂) := by group
              _ = (x₁ * x₂) * (g : G) := hmain
              _ = x₁ * (x₂ * (g : G)) := by group
              _ = x₁ * ((g : G) * x₂) := by rw [(hcomm (g : G) g.2 x₂ hx₂).symm]
              _ = x₁ * (g : G) * x₂ := by group
          exact mul_right_cancel h2
        have hx₁one : x₁ = 1 := by
          have hbot := eight70_center_eq_bot_of_alt5 h₁
          have hmem := hx₁_center
          rw [hbot, Subgroup.mem_bot] at hmem
          simpa using congrArg Subtype.val hmem
        have hx₂_center : (⟨x₂, hx₂⟩ : ↥X₂) ∈ Subgroup.center ↥X₂ := by
          rw [Subgroup.mem_center_iff]
          intro g
          apply Subtype.ext
          show (g : G) * x₂ = x₂ * (g : G)
          have hncomm : (g : G) * n = n * (g : G) :=
            (Subgroup.mem_centralizer_iff.mp (hcent₂ hn)) (g : G) g.2
          have hmain : (g : G) * (x₁ * x₂) = (x₁ * x₂) * (g : G) := by
            rw [hprod]
            exact hncomm
          have h2 : x₁ * ((g : G) * x₂) = x₁ * (x₂ * (g : G)) := by
            calc x₁ * ((g : G) * x₂) = (x₁ * (g : G)) * x₂ := by group
              _ = ((g : G) * x₁) * x₂ := by rw [hcomm x₁ hx₁ (g : G) g.2]
              _ = (g : G) * (x₁ * x₂) := by group
              _ = (x₁ * x₂) * (g : G) := hmain
              _ = x₁ * (x₂ * (g : G)) := by group
          exact mul_left_cancel h2
        have hx₂one : x₂ = 1 := by
          have hbot := eight70_center_eq_bot_of_alt5 h₂
          have hmem := hx₂_center
          rw [hbot, Subgroup.mem_bot] at hmem
          simpa using congrArg Subtype.val hmem
        calc n = x₁ * x₂ := hprod.symm
          _ = 1 := by rw [hx₁one, hx₂one, one_mul]
      apply le_bot_iff.mp
      intro n hn
      rw [Subgroup.mem_bot]
      exact hmem_center n hn
    · exact Or.inr (Or.inr h₂le)
  · exact Or.inr (Or.inl h₁le)

omit [Finite G] in
private lemma eight70_center_map_eq_bot {X X₁ X₂ : Subgroup G}
    (hsup : X₁ ⊔ X₂ = X)
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (h₁ : Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)))
    (h₂ : Nonempty (↥X₂ ≃* alternatingGroup (Fin 5))) :
    (Subgroup.center ↥X).map X.subtype = ⊥ := by
  let N : Subgroup G := (Subgroup.center ↥X).map X.subtype
  have hNle : N ≤ X := Subgroup.map_subtype_le _
  have hNcent : X ≤ Subgroup.centralizer (N : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro n ⟨z, hz, rfl⟩
    have hzx : ⟨x, hx⟩ * z = z * ⟨x, hx⟩ := Subgroup.mem_center_iff.mp hz ⟨x, hx⟩
    exact (congrArg Subtype.val hzx).symm
  have hNnorm : X ≤ Subgroup.normalizer (N : Set G) :=
    hNcent.trans (Subgroup.centralizer_le_normalizer _)
  rcases eight70_normal_dichotomy hsup hcomm h₁ h₂ hNle hNnorm with
    hbot | hle | hle
  · exact hbot
  · exfalso
    have hNcomm : IsMulCommutative ↥N :=
      Subgroup.map_isMulCommutative (H := Subgroup.center ↥X) X.subtype
    have : IsMulCommutative ↥(X₁.subgroupOf N) := inferInstance
    have hX₁comm : IsMulCommutative ↥X₁ := by
      have h := Subgroup.map_isMulCommutative (H := X₁.subgroupOf N) N.subtype
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle] at h
    exact eight70_not_isMulCommutative_of_alt5 h₁ hX₁comm
  · exfalso
    have hNcomm : IsMulCommutative ↥N :=
      Subgroup.map_isMulCommutative (H := Subgroup.center ↥X) X.subtype
    have : IsMulCommutative ↥(X₂.subgroupOf N) := inferInstance
    have hX₂comm : IsMulCommutative ↥X₂ := by
      have h := Subgroup.map_isMulCommutative (H := X₂.subgroupOf N) N.subtype
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle] at h
    exact eight70_not_isMulCommutative_of_alt5 h₂ hX₂comm

private lemma eight70_inf_pCore_eq_bot {X X₁ X₂ L : Subgroup G}
    (hXL : X ≤ L) (hsup : X₁ ⊔ X₂ = X)
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (h₁ : Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)))
    (h₂ : Nonempty (↥X₂ ≃* alternatingGroup (Fin 5))) :
    X ⊓ CFSG.Open.pCoreOf 2 L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 L
  let N : Subgroup G := X ⊓ Q
  have hQle : Q ≤ L := Subgroup.map_subtype_le _
  have hQp : IsPGroup 2 Q :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
  have hQnormal : (Q.subgroupOf L).Normal := by
    have hEq : Q.subgroupOf L = CFSG.pCore 2 ↥L := by
      rw [← Subgroup.map_subtype_inj (H := L)]
      rw [Subgroup.map_subgroupOf_eq_of_le hQle]
      rfl
    rw [hEq]
    infer_instance
  have hQnormL : L ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mp hQnormal
  have hNle : N ≤ X := inf_le_left
  have hNnorm : X ≤ Subgroup.normalizer (N : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      refine ⟨X.mul_mem (X.mul_mem hx hn.1) (X.inv_mem hx), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hQnormL (hXL hx)) n).mp hn.2
    · intro hn
      have hnX : n ∈ X := by
        have h := X.mul_mem (X.mul_mem (X.inv_mem hx) hn.1) hx
        simpa [mul_assoc] using h
      refine ⟨hnX, ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hQnormL (hXL hx)) n).mpr hn.2
  have hNp : IsPGroup 2 N := hQp.to_le inf_le_right
  rcases eight70_normal_dichotomy hsup hcomm h₁ h₂ hNle hNnorm with
    hbot | hle | hle
  · exact hbot
  · exact absurd (hNp.to_le hle) (eight70_not_isPGroup_two_of_alt5 h₁)
  · exact absurd (hNp.to_le hle) (eight70_not_isPGroup_two_of_alt5 h₂)

private lemma eight70_pCore_eq_bot {X X₁ X₂ L : Subgroup G}
    (hXQ : X ⊔ CFSG.Open.pCoreOf 2 L = L)
    (hsup : X₁ ⊔ X₂ = X)
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (h₁ : Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)))
    (h₂ : Nonempty (↥X₂ ≃* alternatingGroup (Fin 5))) :
    CFSG.pCore 2 ↥X = ⊥ := by
  have hXL : X ≤ L := by
    rw [← hXQ]
    exact le_sup_left
  have hmap : (CFSG.pCore 2 ↥X).map X.subtype = X ⊓ CFSG.Open.pCoreOf 2 L :=
    map_pCore_eq_inf L X hXQ
  have hbot : X ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    eight70_inf_pCore_eq_bot hXL hsup hcomm h₁ h₂
  have hmapbot : (CFSG.pCore 2 ↥X).map X.subtype = ⊥ := by
    rw [hmap, hbot]
  have hmapbot' : (CFSG.pCore 2 ↥X).map X.subtype =
      (⊥ : Subgroup ↥X).map X.subtype := by
    rw [hmapbot, Subgroup.map_bot]
  exact Subgroup.map_injective X.subtype_injective hmapbot'

omit [Finite G] in
private lemma eight70_not_quasisimple {X X₁ X₂ : Subgroup G}
    (hX₁ : X₁ ≤ X) (hX₂ : X₂ ≤ X)
    (hsup : X₁ ⊔ X₂ = X) (hinf : X₁ ⊓ X₂ = ⊥)
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (h₁ : Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)))
    (h₂ : Nonempty (↥X₂ ≃* alternatingGroup (Fin 5))) :
    ¬ CFSG.Open.IsQuasisimple ↥X := by
  intro hq
  have hcenter_map : (Subgroup.center ↥X).map X.subtype = ⊥ :=
    eight70_center_map_eq_bot hsup hcomm h₁ h₂
  have hcenter : Subgroup.center ↥X = ⊥ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [hcenter_map, Subgroup.map_bot]
  have hsimpleQ : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) := hq.2
  have : IsSimpleGroup (↥X ⧸ (⊥ : Subgroup ↥X)) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).symm.isSimpleGroup
  have hsimpleX : IsSimpleGroup ↥X :=
    (QuotientGroup.quotientBot (G := ↥X)).symm.isSimpleGroup
  have hnormal₁ : (X₁.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX₁).mpr
      (eight70_le_normalizer_left hsup hcomm)
  have : (X₁.subgroupOf X).Normal := hnormal₁
  rcases Subgroup.Normal.eq_bot_or_eq_top (X₁.subgroupOf X) with hbot | htop
  · have hX₁bot : X₁ = ⊥ := by
      have hdisj : Disjoint X₁ X := (Subgroup.subgroupOf_eq_bot).mp hbot
      refine le_bot_iff.mp ?_
      intro x hx
      rw [Subgroup.mem_bot]
      exact Subgroup.disjoint_def.mp hdisj hx (hX₁ hx)
    have hcard : Nat.card ↥X₁ = 60 := eight70_card_eq_sixty_of_alt5 h₁
    rw [hX₁bot] at hcard
    simp at hcard
  · have hXleX₁ : X ≤ X₁ := (Subgroup.subgroupOf_eq_top).mp htop
    have hX₂bot : X₂ = ⊥ := by
      have hle : X₂ ≤ X₁ := hX₂.trans hXleX₁
      have h : X₁ ⊓ X₂ = X₂ := inf_eq_right.mpr hle
      rw [hinf] at h
      exact h.symm
    have hcard : Nat.card ↥X₂ = 60 := eight70_card_eq_sixty_of_alt5 h₂
    rw [hX₂bot] at hcard
    simp at hcard

private lemma eight70_le_of_odd_card_of_sup {Y Q A : Subgroup G}
    (hYnorm : Y ⊔ Q ≤ Subgroup.normalizer (Y : Set G))
    (hQp : IsPGroup 2 Q) (hA : A ≤ Y ⊔ Q) (hoddA : Odd (Nat.card A)) :
    A ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup G := Y ⊔ Q
  have hYR : Y ≤ R := le_sup_left
  have hQR : Q ≤ R := le_sup_right
  have hYRnorm : R ≤ Subgroup.normalizer (Y : Set G) := hYnorm
  have hYnormalR : (Y.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYR).mpr hYRnorm
  let π : ↥R →* ↥R ⧸ (Y.subgroupOf R) := QuotientGroup.mk' _
  let B : Subgroup (↥R ⧸ Y.subgroupOf R) := (A.subgroupOf R).map π
  have hQpR : IsPGroup 2 (Q.subgroupOf R) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQR).symm
  have hsupR : (Y.subgroupOf R) ⊔ (Q.subgroupOf R) = ⊤ := by
    apply Subgroup.map_injective R.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYR,
      inf_eq_left.mpr hQR, Subgroup.map_top, Subgroup.range_subtype]
  have hQmap : (Q.subgroupOf R).map π = ⊤ := by
    apply top_le_iff.mp
    intro z _
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (Y.subgroupOf R) z
    obtain ⟨y, hy, q, hq, hyq⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := Y.subgroupOf R)
        (t := Q.subgroupOf R)).mp (hsupR ▸ Subgroup.mem_top r)
    have hπy : π y = 1 :=
      (QuotientGroup.eq_one_iff (N := Y.subgroupOf R) y).mpr hy
    rw [← hyq, map_mul, hπy, one_mul]
    exact Subgroup.mem_map_of_mem π hq
  have hBle : B ≤ (Q.subgroupOf R).map π := by
    rw [hQmap]
    exact le_top
  have hBp : IsPGroup 2 B := (hQpR.map π).to_le hBle
  have hBcard_dvd : Nat.card B ∣ Nat.card (A.subgroupOf R) :=
    Subgroup.card_map_dvd (H := A.subgroupOf R) π
  have hAcard : Nat.card (A.subgroupOf R) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have hBodd : Odd (Nat.card B) := by
    refine Odd.of_dvd_nat ?_ hBcard_dvd
    rwa [hAcard]
  have hcardB : Nat.card B = 1 := by
    obtain ⟨n, hn⟩ := hBp.exists_card_eq
    have h2nodd : Odd (2 ^ n) := hn ▸ hBodd
    have hn0 : n = 0 := by
      by_contra hne
      have hpos : 0 < n := Nat.pos_of_ne_zero hne
      have hmod1 : 2 ^ n % 2 = 1 := Nat.odd_iff.mp h2nodd
      have hmod0 : 2 ^ n % 2 = 0 := Nat.two_pow_mod_two_eq_zero.mpr hpos
      omega
    rw [hn, hn0, pow_zero]
  have : Subsingleton ↥B := (Nat.card_eq_one_iff_unique.mp hcardB).1
  have hBbot : B = ⊥ := Subgroup.eq_bot_of_subsingleton B
  have hle : A.subgroupOf R ≤ Y.subgroupOf R := by
    have hmapbot : (A.subgroupOf R).map π = ⊥ := hBbot
    rw [Subgroup.map_eq_bot_iff] at hmapbot
    simpa [π, QuotientGroup.ker_mk'] using hmapbot
  intro a ha
  have hmem : (⟨a, hA ha⟩ : ↥R) ∈ A.subgroupOf R := Subgroup.mem_subgroupOf.mpr ha
  exact Subgroup.mem_subgroupOf.mp (hle hmem)

theorem eight70_member {D : Data G} {L X X₁ X₂ : Subgroup G} (hyp : Hyp869 D L X)
    (hX₁ : X₁ ≤ X) (hX₂ : X₂ ≤ X) (hsup : X₁ ⊔ X₂ = X) (hinf : X₁ ⊓ X₂ = ⊥)
    (h₁ : Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)))
    (h₂ : Nonempty (↥X₂ ≃* alternatingGroup (Fin 5)))
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x) :
    ∃ Y ∈ calC D.M, UC22.F08.Thin8 Y ∧
      ((∀ A : Subgroup G, A ≤ X₁ → Odd (Nat.card A) → A ≤ Y) ∨
        ∀ A : Subgroup G, A ≤ X₂ → Odd (Nat.card A) → A ≤ Y) := by
  classical
  rcases hyp with ⟨hcase, hXL, hXQ, hnotthin⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hX₁le : X₁ ≤ X := hX₁
  have hX₂le : X₂ ≤ X := hX₂
  have hX₁norm : X ≤ Subgroup.normalizer (X₁ : Set G) :=
    eight70_le_normalizer_left hsup hcomm
  have hX₂norm : X ≤ Subgroup.normalizer (X₂ : Set G) :=
    eight70_le_normalizer_right hsup hcomm
  have hpcore : CFSG.pCore 2 ↥X = ⊥ :=
    eight70_pCore_eq_bot hXQ hsup hcomm h₁ h₂
  have hbarX : Nonempty (UC22.Bar2 X ≃* ↥X) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hpcore).trans QuotientGroup.quotientBot⟩
  have hbar : Nonempty (UC22.Bar2 L ≃* ↥X) := by
    obtain ⟨e⟩ := nonempty_bar2_equiv_of_sup_pCore L X hXQ
    obtain ⟨f⟩ := hbarX
    exact ⟨e.symm.trans f⟩
  have hnotqX : ¬ CFSG.Open.IsQuasisimple ↥X :=
    eight70_not_quasisimple hX₁le hX₂le hsup hinf hcomm h₁ h₂
  rcases hcase with hLmem | ⟨hLM, hML, hprod⟩
  ·
    obtain ⟨e⟩ := hbar
    exact absurd (CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hLmem.2.2) hnotqX
  ·
    obtain ⟨k, S, hS, hLset⟩ := hprod
    have hpairs : ∀ A ∈ List.ofFn S, ∀ B ∈ List.ofFn S,
        A ≤ Subgroup.normalizer (B : Set G) := by
      intro A hA B hB
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hB
      by_cases hij : S j = S i
      · rw [hij]
        exact Subgroup.le_normalizer
      · exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_calC_normalizes (hS j) (hS i) hij
    have hLeq : L = ⨆ A ∈ List.ofFn S, A := by
      apply SetLike.coe_injective
      rw [hLset, ← CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_prod_list_eq_iSup _
        hpairs, List.map_ofFn]
      rfl
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · exfalso
        have hLbot : L = ⊥ := by
          cases hk
          rw [hLeq, List.ofFn_zero]
          simp
        have hX₁bot : X₁ = ⊥ := by
          refine le_bot_iff.mp ?_
          calc X₁ ≤ X := hX₁le
            _ ≤ L := hXL
            _ = ⊥ := hLbot
        have hcard : Nat.card ↥X₁ = 60 := eight70_card_eq_sixty_of_alt5 h₁
        rw [hX₁bot] at hcard
        simp at hcard
      · exact hk
    let Y : Subgroup G := S ⟨0, hkpos⟩
    have hY : Y ∈ calC D.M := hS ⟨0, hkpos⟩
    have hSle : ∀ i, S i ≤ L := by
      intro i
      rw [hLeq]
      exact le_iSup₂ (f := fun A (_ : A ∈ List.ofFn S) => A) (S i)
        (List.mem_ofFn.2 ⟨i, rfl⟩)
    have hLnormS : ∀ i, L ≤ Subgroup.normalizer (S i : Set G) := by
      intro i
      rw [hLeq]
      refine iSup₂_le fun A hA => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hA
      by_cases hji : S j = S i
      · rw [hji]
        exact Subgroup.le_normalizer
      · exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_calC_normalizes
          (hS i) (hS j) (fun h => hji h.symm)
    have hLnormY : L ≤ Subgroup.normalizer (Y : Set G) := hLnormS ⟨0, hkpos⟩
    let Q : Subgroup G := CFSG.Open.pCoreOf 2 L
    have hQle : Q ≤ L := Subgroup.map_subtype_le _
    have hQp : IsPGroup 2 Q :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
    have hQnormal_sub : (Q.subgroupOf L).Normal := by
      have hEq : Q.subgroupOf L = CFSG.pCore 2 ↥L := by
        rw [← Subgroup.map_subtype_inj (H := L)]
        rw [Subgroup.map_subgroupOf_eq_of_le hQle]
        rfl
      rw [hEq]
      infer_instance
    have hQnormL : L ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mp hQnormal_sub
    have hYQleL : Y ⊔ Q ≤ L := sup_le (hSle ⟨0, hkpos⟩) hQle
    let N : Subgroup G := (Y ⊔ Q) ⊓ X
    have hLnormYQ : L ≤ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) :=
      (le_inf hLnormY hQnormL).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup Y Q)
    have hNle : N ≤ X := inf_le_right
    have hXnormN : X ≤ Subgroup.normalizer (N : Set G) :=
      (le_inf (hXL.trans hLnormYQ) (Subgroup.le_normalizer)).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := Y ⊔ Q) (K := X))
    have hXnormQ : X ≤ Subgroup.normalizer (Q : Set G) := hXL.trans hQnormL
    have hded : N ⊔ Q = Y ⊔ Q := by
      have h := Subgroup.inf_sup_assoc_of_le (H := X) (K := Y ⊔ Q) (N := Q)
        hXnormQ (le_sup_right : Q ≤ Y ⊔ Q)
      rw [hXQ, inf_eq_left.mpr hYQleL] at h
      exact h
    have hNne : N ≠ ⊥ := by
      intro hNbot
      have hYQ : Y ≤ Q := by
        have h : Y ⊔ Q = Q := by
          rw [← hded, hNbot, bot_sup_eq]
        exact sup_eq_right.mp h
      have hYp : IsPGroup 2 Y := hQp.to_le hYQ
      have hYnil : Group.IsNilpotent ↥Y := hYp.isNilpotent
      have hYperf : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY.2.1
      have hYbot : Y = ⊥ := by
        by_contra hYne
        have : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
        have : Group.IsPerfect ↥Y := hYperf
        exact (Group.IsPerfect.not_isNilpotent (G := ↥Y)) hYnil
      have hnt : Nontrivial (UC22.Bar2 Y) := by
        have : Nontrivial (UC22.Bar2 Y ⧸ Subgroup.center (UC22.Bar2 Y)) :=
          hY.2.2.2.toNontrivial
        exact Function.Surjective.nontrivial
          (QuotientGroup.mk'_surjective (Subgroup.center (UC22.Bar2 Y)))
      rw [hYbot] at hnt
      have : Subsingleton (UC22.Bar2 (⊥ : Subgroup G)) := by
        infer_instance
      exact false_of_nontrivial_of_subsingleton (UC22.Bar2 (⊥ : Subgroup G))
    have hNnot : ¬ X ≤ N := by
      intro hXN
      have hXleYQ : X ≤ Y ⊔ Q := hXN.trans inf_le_left
      have hYQL : Y ⊔ Q = L := by
        apply le_antisymm hYQleL
        calc L = X ⊔ Q := hXQ.symm
          _ ≤ Y ⊔ Q := sup_le hXleYQ le_sup_right
      obtain ⟨eY⟩ := nonempty_bar2_equiv_of_sup_pCore L Y hYQL
      obtain ⟨eL⟩ := hbar
      have hqX : CFSG.Open.IsQuasisimple ↥X :=
        CFSG.Open.IsQuasisimple.of_mulEquiv (eY.trans eL).symm hY.2.2
      exact hnotqX hqX
    have hodd_of : ∀ (Xi : Subgroup G), Xi ≤ Y ⊔ Q →
        ∀ A : Subgroup G, A ≤ Xi → Odd (Nat.card A) → A ≤ Y := by
      intro Xi hXi A hA hoddA
      exact eight70_le_of_odd_card_of_sup (hYQleL.trans hLnormY) hQp
        (hA.trans hXi) hoddA
    have hthin_of : ∀ (Xi : Subgroup G),
        Nonempty (↥Xi ≃* alternatingGroup (Fin 5)) →
        Y ⊔ Q = Xi ⊔ Q → UC22.F08.Thin8 Y := by
      intro Xi hXi hYQXi r hr hr2
      have hmono : CFSG.Open.pRank r Y ≤ CFSG.Open.pRank r (Y ⊔ Q) :=
        CFSG.SectionRank.pRank_mono hr.one_lt le_sup_left
      have hXiL : Xi ≤ L := by
        calc Xi ≤ Xi ⊔ Q := le_sup_left
          _ = Y ⊔ Q := hYQXi.symm
          _ ≤ L := hYQleL
      have hQcore : Q ≤ CFSG.Open.pCoreOf 2 (Xi ⊔ Q) := by
        refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer
          (r := 2) (N := Q) (H := Xi ⊔ Q) le_sup_right ?_ hQp
        exact (sup_le hXiL hQle).trans hQnormL
      have hsupcore : Xi ⊔ CFSG.Open.pCoreOf 2 (Xi ⊔ Q) = Xi ⊔ Q := by
        apply le_antisymm
        · exact sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 (Xi ⊔ Q))
        · exact sup_le le_sup_left (le_sup_of_le_right hQcore)
      have hle : CFSG.Open.pRank r (Y ⊔ Q) ≤ CFSG.Open.pRank r Xi := by
        rw [hYQXi]
        exact CFSG.LocalAnalysis.UniquenessCase.UC6.R869S.pRank_le_of_sup_pCore
          le_sup_left hsupcore hr hr2
      have hXiRank : CFSG.Open.pRank r Xi ≤ 1 := by
        obtain ⟨e⟩ := hXi
        rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup Xi]
        rw [← CFSG.SectionRank.pRank_eq_open_pRank_top r ↥Xi]
        rw [CFSG.pRank_congr_of_mulEquiv e r]
        rw [CFSG.SectionRank.pRank_eq_open_pRank_top r (alternatingGroup (Fin 5))]
        exact eight70_pRank_alt5_le_one hr hr2
      omega
    rcases eight70_normal_dichotomy hsup hcomm h₁ h₂ hNle hXnormN with
      hNbot | hN₁ | hN₂
    · exact absurd hNbot hNne
    · have hNX₂bot : N ⊓ X₂ = ⊥ := by
        have hnormal : ((N ⊓ X₂).subgroupOf X₂).Normal := by
          refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
          refine (le_inf (hX₂le.trans hXnormN) (hX₂le.trans hX₂norm)).trans ?_
          exact Subgroup.inf_normalizer_le_normalizer_inf
        have : IsSimpleGroup ↥X₂ := h₂.some.isSimpleGroup
        rcases Subgroup.Normal.eq_bot_or_eq_top ((N ⊓ X₂).subgroupOf X₂) with h | h
        · have h' : (N ⊓ X₂).subgroupOf X₂ = (⊥ : Subgroup G).subgroupOf X₂ := by
            simpa using h
          simpa using (Subgroup.subgroupOf_inj.mp h')
        · exfalso
          apply hNnot
          rw [← hsup]
          exact sup_le hN₁ ((Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left)
      have hmod : X₁ ⊔ (N ⊓ X₂) = N ⊓ (X₁ ⊔ X₂) := by
        have h := Subgroup.inf_sup_assoc_of_le (H := X₂) (K := N) (N := X₁)
          (hX₂le.trans hX₁norm) hN₁
        rwa [sup_comm (N ⊓ X₂) X₁, sup_comm X₂ X₁] at h
      have hNX₁ : N = X₁ := by
        calc N = N ⊓ X := by rw [inf_eq_left.mpr hNle]
          _ = (X₁ ⊔ X₂) ⊓ N := by rw [hsup, inf_comm]
          _ = N ⊓ (X₁ ⊔ X₂) := by rw [inf_comm]
          _ = X₁ ⊔ (N ⊓ X₂) := hmod.symm
          _ = X₁ ⊔ (X₂ ⊓ N) := by rw [inf_comm]
          _ = X₁ := by rw [inf_comm X₂ N, hNX₂bot, sup_bot_eq]
      have hYQ₁ : Y ⊔ Q = X₁ ⊔ Q := by rw [← hded, hNX₁]
      have hX₁leYQ : X₁ ≤ Y ⊔ Q := by
        rw [hYQ₁]
        exact le_sup_left
      refine ⟨Y, hY, hthin_of X₁ h₁ hYQ₁, Or.inl ?_⟩
      intro A hA hoddA
      exact hodd_of X₁ hX₁leYQ A hA hoddA
    · have hNX₁bot : N ⊓ X₁ = ⊥ := by
        have hnormal : ((N ⊓ X₁).subgroupOf X₁).Normal := by
          refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
          refine (le_inf (hX₁le.trans hXnormN) (hX₁le.trans hX₁norm)).trans ?_
          exact Subgroup.inf_normalizer_le_normalizer_inf
        have : IsSimpleGroup ↥X₁ := h₁.some.isSimpleGroup
        rcases Subgroup.Normal.eq_bot_or_eq_top ((N ⊓ X₁).subgroupOf X₁) with h | h
        · have h' : (N ⊓ X₁).subgroupOf X₁ = (⊥ : Subgroup G).subgroupOf X₁ := by
            simpa using h
          simpa using (Subgroup.subgroupOf_inj.mp h')
        · exfalso
          apply hNnot
          rw [← hsup]
          exact sup_le ((Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left) hN₂
      have hmod : X₂ ⊔ (N ⊓ X₁) = N ⊓ (X₁ ⊔ X₂) := by
        have h := Subgroup.inf_sup_assoc_of_le (H := X₁) (K := N) (N := X₂)
          (hX₁le.trans hX₂norm) hN₂
        rwa [sup_comm (N ⊓ X₁) X₂] at h
      have hNX₂ : N = X₂ := by
        calc N = N ⊓ X := by rw [inf_eq_left.mpr hNle]
          _ = (X₁ ⊔ X₂) ⊓ N := by rw [hsup, inf_comm]
          _ = N ⊓ (X₁ ⊔ X₂) := by rw [inf_comm]
          _ = X₂ ⊔ (N ⊓ X₁) := hmod.symm
          _ = X₂ ⊔ (X₁ ⊓ N) := by rw [inf_comm]
          _ = X₂ := by rw [inf_comm X₁ N, hNX₁bot, sup_bot_eq]
      have hYQ₂ : Y ⊔ Q = X₂ ⊔ Q := by rw [← hded, hNX₂]
      have hX₂leYQ : X₂ ≤ Y ⊔ Q := by
        rw [hYQ₂]
        exact le_sup_left
      refine ⟨Y, hY, hthin_of X₂ h₂ hYQ₂, Or.inr ?_⟩
      intro A hA hoddA
      exact hodd_of X₂ hX₂leYQ A hA hoddA

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
