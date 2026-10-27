module

public import CFSG.Quasithin.EmptyFaithful.S146zWG
public import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.Quasithin.H13.NQRigidWMGroups
import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

section Generic

variable {Ω : Type} [Group Ω]

theorem sw_eq_of_normal_of_isQuasisimple {K E : Subgroup Ω} (hKE : K ≤ E)
    (hn : ∀ x ∈ E, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K)
    (hE : CFSG.IsQuasisimple ↥E) : K = E := by
  have hnorm : (K.subgroupOf E).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hn g g.2 k hk
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
    (B1Red.isQuasisimple_to_open hE) (K.subgroupOf E) with hc | htop
  · exfalso
    refine InternalSec.not_commute_of_isQuasisimple hK fun a ha b hb => ?_
    have h1 : (⟨a, hKE ha⟩ : ↥E) ∈ Subgroup.center ↥E := hc ha
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hKE hb⟩
    exact (congrArg Subtype.val h2).symm
  · refine le_antisymm hKE (fun e he => ?_)
    have : (⟨e, he⟩ : ↥E) ∈ K.subgroupOf E := by rw [htop]; trivial
    exact this

theorem sw_eq_or_eq_of_normal [Finite Ω] {J L₁ L₂ K : Subgroup Ω}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂)
    (hL₁J : L₁ ≤ J) (hL₂J : L₂ ≤ J) (h2 : ∀ x ∈ J, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂)
    (hKJ : K ≤ J) (hKn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K) :
    K = L₁ ∨ K = L₂ := by
  have hKL : K ≤ L₁ ⊔ L₂ :=
    (B1Red.perfect_le_oTwoUpper' hKJ hK.1).trans (oTwoUpper_le_of_pow_mem h2)
  have hLJ : L₁ ⊔ L₂ ≤ J := sup_le hL₁J hL₂J
  rcases InternalSec.le_or_le_of_sup_eq rfl hcomm hKL
    (fun x hx k hk => hKn x (hLJ hx) k hk) hK with h | h
  · exact Or.inl
      (sw_eq_of_normal_of_isQuasisimple h (fun x hx k hk => hKn x (hL₁J hx) k hk) hK hq₁)
  · exact Or.inr
      (sw_eq_of_normal_of_isQuasisimple h (fun x hx k hk => hKn x (hL₂J hx) k hk) hK hq₂)

theorem sw_le_of_perfect_of_isSolvable {A B P : Subgroup Ω}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hPAB : P ≤ A ⊔ B) (hP : Group.IsPerfect ↥P)
    (hB : Group.IsSolvable ↥B) : P ≤ A := by
  set H := A ⊔ B with hH
  have hBH : B ≤ H := le_sup_right
  set N : Subgroup ↥H := A.subgroupOf H with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    exact InternalSec.conj_mem_of_mem_sup_of_commute hc g g.2 n hn
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (Subgroup.inclusion hBH)) := by
    intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (B19Aux.mem_sup_iff_of_le_normalizer (InternalSec.le_normalizer_of_commute hc)).1 hh
    refine ⟨⟨b, hb⟩, ?_⟩
    show QuotientGroup.mk' N ⟨b, hBH hb⟩ = QuotientGroup.mk' N ⟨a * b, hh⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      Subgroup.mem_subgroupOf]
    show (b⁻¹ * (a * b) : Ω) ∈ A
    rw [hc a ha b hb, inv_mul_cancel_left]
    exact ha
  have : Group.IsSolvable (↥H ⧸ N) := Group.isSolvable_of_surjective hsurj
  have hPH : P ≤ H := hPAB
  let φ : ↥P →* ↥H ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hPH)
  have hr : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have : Group.IsPerfect ↥φ.range :=
      Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    exact Group.IsPerfect.not_isSolvable ↥φ.range inferInstance
  intro p hp
  have h1 : φ ⟨p, hp⟩ ∈ φ.range := ⟨_, rfl⟩
  rw [hr, Subgroup.mem_bot] at h1
  have h2 : (⟨p, hPH hp⟩ : ↥H) ∈ N := (QuotientGroup.eq_one_iff _).1 h1
  exact h2

theorem sw_isSolvable_of_card_six {H : Type*} [Group H] (h : Nat.card H = 6) :
    Group.IsSolvable H := by
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [h]; norm_num : 3 ∣ Nat.card H)
  set P := Subgroup.zpowers x with hP
  have hPc : Nat.card ↥P = 3 := by rw [hP, Nat.card_zpowers, hx]
  have hidx : P.index = 2 := by
    have := P.card_mul_index
    rw [hPc, h] at this
    omega
  have hPn : P.Normal := Subgroup.normal_of_index_eq_two hidx
  have hPcyc : IsCyclic ↥P := isCyclic_of_prime_card hPc
  have hQc : Nat.card (H ⧸ P) = 2 := by rw [← Subgroup.index_eq_card]; exact hidx
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQcyc : IsCyclic (H ⧸ P) := isCyclic_of_prime_card hQc
  exact Group.isSolvable_of_subgroup_quotient P

end Generic

section Types

@[expose] def SwType {Ω : Type} [Group Ω] (L : Subgroup Ω) : Prop :=
  IsSimpleGroup ↥L ∧
    ((∃ (F : Type) (_ : Field F) (_ : Finite F) (n : ℕ), 2 ≤ n ∧ Nat.card F = 2 ^ n ∧
        Nonempty (↥L ≃* ↥(StatedSL 2 F))) ∨
      Nonempty (↥L ≃* alternatingGroup (Fin 5)) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (m : ℕ), 1 ≤ m ∧ Odd m ∧ Nat.card F = 2 ^ m ∧
        Nonempty (↥L ≃* ↥(StatedSL 3 F))))

theorem SwType.of_mulEquiv {Ω Ω' : Type} [Group Ω] [Group Ω'] {L : Subgroup Ω} {L' : Subgroup Ω'}
    (e : ↥L ≃* ↥L') (h : SwType L) : SwType L' := by
  obtain ⟨hs, h⟩ := h
  have : IsSimpleGroup ↥L := hs
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  rcases h with ⟨F, _, _, n, hn, hF, ⟨e'⟩⟩ | ⟨⟨e'⟩⟩ | ⟨F, _, _, m, hm, hmo, hF, ⟨e'⟩⟩
  · exact Or.inl ⟨F, inferInstance, inferInstance, n, hn, hF, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨e.symm.trans e'⟩)
  · exact Or.inr (Or.inr ⟨F, inferInstance, inferInstance, m, hm, hmo, hF, ⟨e.symm.trans e'⟩⟩)

end Types

section Factors

variable {Ω : Type} [Group Ω]

theorem sw_charP_two {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])

theorem sw_isQuasisimple_of_simple {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : CFSG.IsQuasisimple Q := by
  have hnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := h }
    exact hp IsSimpleGroup.prime_card
  have hperf : Group.IsPerfect Q := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have h1 : ⁅a, b⁆ ∈ commutator Q :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact hab h1
    · exact h
  exact B1Red.isQuasisimple_of_open (CFSG.ComponentClassification.Quasisimple.simple_of_perfect Q)

theorem sw_fac_of_perm_five {G : Subgroup Ω} (e : ↥G ≃* Equiv.Perm (Fin 5)) :
    ∃ K : Subgroup Ω, K ≤ G ∧ (∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
      Nonempty (↥K ≃* alternatingGroup (Fin 5)) := by
  set f : Equiv.Perm (Fin 5) →* Ω := G.subtype.comp e.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := G.subtype_injective.comp e.symm.injective
  have hcard : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  have hA5 : CFSG.IsQuasisimple ↥(alternatingGroup (Fin 5)) :=
    sw_isQuasisimple_of_simple (by rw [hcard]; norm_num)
  have e' := (alternatingGroup (Fin 5)).equivMapOfInjective f hfinj
  refine ⟨(alternatingGroup (Fin 5)).map f, ?_, ?_, ?_, ⟨e'.symm⟩⟩
  · rintro _ ⟨σ, -, rfl⟩
    exact (e.symm σ).2
  · rintro g hg _ ⟨a, ha, rfl⟩
    have hg' : f (e ⟨g, hg⟩) = g := by simp [hf]
    refine ⟨e ⟨g, hg⟩ * a * (e ⟨g, hg⟩)⁻¹, Subgroup.Normal.conj_mem inferInstance a ha _, ?_⟩
    rw [map_mul, map_mul, map_inv, hg']
  · exact B1Red.isQuasisimple_of_open
      (CFSG.ComponentClassification.Components.quasisimple_of_equiv e'.symm
        (B1Red.isQuasisimple_to_open hA5))

theorem sw_fac_of_factorList [Finite Ω] {G : Subgroup Ω} (h : B56FactorList ↥G) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (n : ℕ), 2 ≤ n ∧ Nat.card F = 2 ^ n ∧
        Nonempty (↥G ≃* ↥(StatedSL 2 F)) ∧ IsSimpleGroup ↥G ∧ CFSG.IsQuasisimple ↥G) ∨
      (∃ K : Subgroup Ω, K ≤ G ∧ (∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
        Nonempty (↥K ≃* alternatingGroup (Fin 5))) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (m : ℕ), 1 ≤ m ∧ Odd m ∧ Nat.card F = 2 ^ m ∧
        Nonempty (↥G ≃* ↥(StatedSL 3 F)) ∧ IsSimpleGroup ↥G ∧ CFSG.IsQuasisimple ↥G) ∨
      (Group.IsSolvable ↥G ∧ 3 ∣ Nat.card ↥G) := by
  rcases h with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | he | ⟨m, F, _, _, hm, hmodd, hF, ⟨e⟩⟩
  · have hcard : Nat.card ↥G = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, S146zU.UC2.card_statedSL_two]
    by_cases hn1 : n = 1
    · subst hn1
      right
      right
      right
      have h6 : Nat.card ↥G = 6 := by rw [hcard, hF]; norm_num
      exact ⟨sw_isSolvable_of_card_six h6, by rw [h6]; norm_num⟩
    · left
      have : CharP F 2 := sw_charP_two hF
      have h4 : 4 ≤ Nat.card F := by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hs : IsSimpleGroup ↥(StatedSL 2 F) :=
        CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
      have : IsSimpleGroup ↥G := e.isSimpleGroup
      refine ⟨F, inferInstance, inferInstance, n, by omega, hF, ⟨e⟩, this,
        sw_isQuasisimple_of_simple ?_⟩
      rw [hcard]
      have h16 : 16 ≤ Nat.card F ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left h4 2
      exact Nat.not_prime_mul (by omega) (by omega)
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inl (sw_fac_of_perm_five e))
  · right
    right
    left
    have hcard : Nat.card ↥G =
        Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three]
    have hs : IsSimpleGroup ↥(StatedSL 3 F) :=
      CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd hF hmodd
    have : IsSimpleGroup ↥G := e.isSimpleGroup
    refine ⟨F, inferInstance, inferInstance, m, hm, hmodd, hF, ⟨e⟩, this,
      sw_isQuasisimple_of_simple ?_⟩
    rw [hcard]
    have hq : 2 ≤ Nat.card F := by
      rw [hF]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h8 : 8 ≤ Nat.card F ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left hq 3
    have h4 : 4 ≤ Nat.card F ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hq 2
    exact Nat.not_prime_mul (by omega) (by
      have : 3 * 7 ≤ (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega)

end Factors

section Cases

variable {V : Type} [CommGroup V] [Finite V]

structure SwData (J L₁ L₂ : Subgroup (MulAut V)) : Prop where
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  q₁ : CFSG.IsQuasisimple ↥L₁
  q₂ : CFSG.IsQuasisimple ↥L₂
  le₁ : L₁ ≤ J
  le₂ : L₂ ≤ J
  norm : ∀ x ∈ J, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂
  two : ∀ x ∈ J, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂

variable {J L₁ L₂ : Subgroup (MulAut V)}

omit [Finite V] in
theorem SwData.false_of_case1 (P : SwData J L₁ L₂)
    (hF : CFSG.IsQuasisimple ↥(quasithinGenFitting J)) : False := by
  set F := quasithinGenFitting J with hFdef
  have hFJ : F ≤ J := quasithinGenFitting_le J
  have hLJ : L₁ ⊔ L₂ ≤ J := sup_le P.le₁ P.le₂
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (P.comm b hb a ha).symm
  have hL₁n : ∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁ :=
    InternalSec.conj_mem_of_mem_sup_of_commute P.comm
  have hL₂n : ∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂ := by
    rw [sup_comm]
    exact InternalSec.conj_mem_of_mem_sup_of_commute hc'
  have hLJn : ((L₁ ⊔ L₂).subgroupOf J).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact P.norm g g.2 n hn⟩
  have hcomp : ∀ {A : Subgroup (MulAut V)}, A ≤ L₁ ⊔ L₂ →
      (∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ A, x * k * x⁻¹ ∈ A) → CFSG.IsQuasisimple ↥A → A ≤ F := by
    intro A hAL hAn hAq
    have hA : (A.subgroupOf (L₁ ⊔ L₂)).Normal :=
      ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact hAn g g.2 n hn⟩
    have hsub : CFSG.Open.IsSubnormal A J :=
      CFSG.Open.IsSubnormal.step hAL hA
        (CFSG.Open.IsSubnormal.step hLJ hLJn (CFSG.Open.IsSubnormal.refl J))
    have hc : CFSG.Open.IsComponentOf A J :=
      ⟨hAL.trans hLJ, hsub, B1Red.isQuasisimple_to_open hAq⟩
    exact (le_sSup (show A ∈ {K | CFSG.Open.IsComponentOf K J} from hc)).trans le_sup_right
  have hL₁F : L₁ ≤ F := hcomp le_sup_left hL₁n P.q₁
  have hL₂F : L₂ ≤ F := hcomp le_sup_right hL₂n P.q₂
  have hLF : L₁ ⊔ L₂ ≤ F := sup_le hL₁F hL₂F
  have hLFn : ((L₁ ⊔ L₂).subgroupOf F).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact P.norm g (hFJ g.2) n hn⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
    (B1Red.isQuasisimple_to_open hF) ((L₁ ⊔ L₂).subgroupOf F) with hcen | htop
  · refine InternalSec.not_commute_of_isQuasisimple P.q₁ fun a ha b hb => ?_
    have h1 : (⟨a, hL₁F ha⟩ : ↥F) ∈ Subgroup.center ↥F :=
      hcen (show (⟨a, hL₁F ha⟩ : ↥F) ∈ (L₁ ⊔ L₂).subgroupOf F from Subgroup.mem_sup_left ha)
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hL₁F hb⟩
    exact (congrArg Subtype.val h2).symm
  · have hFL : F ≤ L₁ ⊔ L₂ := fun x hx => by
      have : (⟨x, hx⟩ : ↥F) ∈ (L₁ ⊔ L₂).subgroupOf F := htop ▸ Subgroup.mem_top _
      exact this
    have h1 : L₁ = F := sw_eq_of_normal_of_isQuasisimple hL₁F
      (fun x hx k hk => hL₁n x (hFL hx) k hk) P.q₁ hF
    have h2 : L₂ = F := sw_eq_of_normal_of_isQuasisimple hL₂F
      (fun x hx k hk => hL₂n x (hFL hx) k hk) P.q₂ hF
    have h12 : L₁ = L₂ := h1.trans h2.symm
    exact InternalSec.not_commute_of_isQuasisimple P.q₁ fun a ha b hb =>
      P.comm a ha b (h12 ▸ hb)

omit [Finite V] in
theorem sw_sixty_le_card_quot {L : Type*} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L) :
    60 ≤ Nat.card (L ⧸ Subgroup.center L) := by
  by_contra h
  push Not at h
  have hsolv : Group.IsSolvable (L ⧸ Subgroup.center L) :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable h
  have hLp : Group.IsPerfect L := hq.1
  have hLn : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hperf : Group.IsPerfect (L ⧸ Subgroup.center L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center L))
      (QuotientGroup.mk'_surjective _)
  have hnt : Nontrivial (L ⧸ Subgroup.center L) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hc : Subgroup.center L = ⊤ := by
      rw [← Subgroup.index_eq_one, Subgroup.index_eq_card]
      exact Nat.card_of_subsingleton (1 : L ⧸ Subgroup.center L)
    have hab : ∀ a b : L, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top a) b).symm
    let _ : CommGroup L := { ‹Group L› with mul_comm := hab }
    have hsol : Group.IsSolvable L := inferInstance
    exact Group.IsPerfect.not_isSolvable L hsol
  exact Group.IsPerfect.not_isSolvable _ hsolv

theorem SwData.false_of_case4 (P : SwData J L₁ L₂) (h4 : B56Case4 J) : False := by
  obtain ⟨G₁, G₂, t, hJt, -, hcomm, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -, -⟩ := h4
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htN := InternalSec.mem_normalizer_sup ht₁ ht₂
  have hsol : Group.IsSolvable ↥G₂ := by
    have := isCyclic_of_prime_card hc₂
    infer_instance
  have hLG : ∀ L : Subgroup (MulAut V), L ≤ J → CFSG.IsQuasisimple ↥L → L ≤ G₁ := by
    intro L hLJ hLq
    have h1 : L ≤ ⁅J, J⁆ := InternalSec.le_commutator_of_perfect hLJ hLq.1
    rw [hJt] at h1
    have hLN : L ≤ G₁ ⊔ G₂ := h1.trans (InternalSec.commutator_le_of_zpowers htN)
    exact sw_le_of_perfect_of_isSolvable hcomm hLN hLq.1 hsol
  have hL₁G := hLG L₁ P.le₁ P.q₁
  have hL₂G := hLG L₂ P.le₂ P.q₂
  have hcard : Nat.card ↥G₁ = 360 := by
    rw [Nat.card_congr e₁.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  have hle : Nat.card ↥(L₁ ⊔ L₂) ≤ 360 :=
    hcard ▸ Subgroup.card_le_of_le (sup_le hL₁G hL₂G)
  have hprod := CFSG.RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf P.comm
  have h60₁ := sw_sixty_le_card_quot P.q₁
  have h60₂ := sw_sixty_le_card_quot P.q₂
  have hZ₁ := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L₁)
  have hZ₂ := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L₂)
  have hinf : Nat.card ↥(L₁ ⊓ L₂) ≤ Nat.card ↥(Subgroup.center ↥L₁) := by
    have hK : (L₁ ⊓ L₂).subgroupOf L₁ ≤ Subgroup.center ↥L₁ := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (P.comm y y.2 x hx.2)
    have := Subgroup.card_le_of_le hK
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : L₁ ⊓ L₂ ≤ L₁)).toEquiv]
      at this
  have hz₁ : 0 < Nat.card ↥(Subgroup.center ↥L₁) := Nat.card_pos
  have hz₂ : 0 < Nat.card ↥(Subgroup.center ↥L₂) := Nat.card_pos
  have hb : 60 ≤ Nat.card ↥L₂ := by nlinarith
  nlinarith

theorem SwData.type_of_case5 (P : SwData J L₁ L₂) (h5 : B56Case5 J) : SwType L₁ ∨ SwType L₂ := by
  obtain ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, -⟩ := h5
  have hs : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
    CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd (m := 1) (by simp) odd_one
  have hs' : IsSimpleGroup ↥G₁ := e₁.isSimpleGroup
  have hcard : Nat.card ↥G₁ = 168 := by
    rw [Nat.card_congr e₁.toEquiv, card_statedSL_three, Nat.card_zmod]
    norm_num
  have hq : CFSG.IsQuasisimple ↥G₁ := sw_isQuasisimple_of_simple (by rw [hcard]; norm_num)
  have hG₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
  have hn₁ : ∀ x ∈ J, ∀ g ∈ G₁, x * g * x⁻¹ ∈ G₁ := fun x hx g hg =>
    InternalSec.conj_mem_of_mem_sup_of_commute hc x (by rw [hsup]; exact hx) g hg
  have hty : SwType G₁ := ⟨hs', Or.inr (Or.inr ⟨ZMod 2, inferInstance, inferInstance, 1, le_rfl,
    odd_one, by simp, ⟨e₁⟩⟩)⟩
  rcases sw_eq_or_eq_of_normal P.comm P.q₁ P.q₂ P.le₁ P.le₂ P.two hG₁J hn₁ hq with h | h
  · exact Or.inl (h ▸ hty)
  · exact Or.inr (h ▸ hty)

theorem SwData.type_of_case3 (P : SwData J L₁ L₂) (h3 : B56Case3 J) : SwType L₁ ∨ SwType L₂ := by
  obtain ⟨G₁, G₂, hsup, hinf, hc, hf₁, -⟩ := h3
  have hcBA : ∀ b ∈ G₂, ∀ a ∈ G₁, b * a = a * b := fun b hb a ha => (hc a ha b hb).symm
  have hAJ : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
  have hJn : ∀ {K : Subgroup (MulAut V)}, K ≤ G₁ → (∀ g ∈ G₁, ∀ k ∈ K, g * k * g⁻¹ ∈ K) →
      ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro K hKA hKn x hx k hk
    have hx' : x ∈ G₁ ⊔ G₂ := by rw [hsup]; exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (B19Aux.mem_sup_iff_of_le_normalizer (InternalSec.le_normalizer_of_commute hc)).1 hx'
    have hbk : b * k = k * b := (hc k (hKA hk) b hb).symm
    have e : a * b * k * (a * b)⁻¹ = a * k * a⁻¹ := by
      calc a * b * k * (a * b)⁻¹ = a * (b * k) * b⁻¹ * a⁻¹ := by group
        _ = a * (k * b) * b⁻¹ * a⁻¹ := by rw [hbk]
        _ = a * k * a⁻¹ := by group
    rw [e]
    exact hKn a ha k hk
  have hself : ∀ g ∈ G₁, ∀ k ∈ G₁, g * k * g⁻¹ ∈ G₁ := fun g hg k hk =>
    G₁.mul_mem (G₁.mul_mem hg hk) (G₁.inv_mem hg)
  rcases sw_fac_of_factorList hf₁ with ⟨F, _, _, n, hn, hF, ⟨e⟩, hsA, hqA⟩ |
      ⟨K, hKA, hKn, hKq, ⟨eK⟩⟩ | ⟨F, _, _, m, hm, hmo, hF, ⟨e⟩, hsA, hqA⟩ | ⟨hsol, h3dvd⟩
  · rcases sw_eq_or_eq_of_normal P.comm P.q₁ P.q₂ P.le₁ P.le₂ P.two hAJ (hJn le_rfl hself) hqA
      with h | h
    · exact Or.inl (h ▸ ⟨hsA, Or.inl ⟨F, inferInstance, inferInstance, n, hn, hF, ⟨e⟩⟩⟩)
    · exact Or.inr (h ▸ ⟨hsA, Or.inl ⟨F, inferInstance, inferInstance, n, hn, hF, ⟨e⟩⟩⟩)
  · have hsK : IsSimpleGroup ↥K := by
      have := alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
      exact eK.isSimpleGroup
    rcases sw_eq_or_eq_of_normal P.comm P.q₁ P.q₂ P.le₁ P.le₂ P.two (hKA.trans hAJ)
      (hJn hKA hKn) hKq with h | h
    · exact Or.inl (h ▸ ⟨hsK, Or.inr (Or.inl ⟨eK⟩)⟩)
    · exact Or.inr (h ▸ ⟨hsK, Or.inr (Or.inl ⟨eK⟩)⟩)
  · rcases sw_eq_or_eq_of_normal P.comm P.q₁ P.q₂ P.le₁ P.le₂ P.two hAJ (hJn le_rfl hself) hqA
      with h | h
    · exact Or.inl (h ▸ ⟨hsA, Or.inr (Or.inr ⟨F, inferInstance, inferInstance, m, hm, hmo, hF,
        ⟨e⟩⟩)⟩)
    · exact Or.inr (h ▸ ⟨hsA, Or.inr (Or.inr ⟨F, inferInstance, inferInstance, m, hm, hmo, hF,
        ⟨e⟩⟩)⟩)
  · exfalso
    have hJBA : J = G₂ ⊔ G₁ := by rw [← hsup, sup_comm]
    have hL₁B : L₁ ≤ G₂ :=
      sw_le_of_perfect_of_isSolvable hcBA (hJBA ▸ P.le₁) P.q₁.1 hsol
    have hL₂B : L₂ ≤ G₂ :=
      sw_le_of_perfect_of_isSolvable hcBA (hJBA ▸ P.le₂) P.q₂.1 hsol
    have hLB : L₁ ⊔ L₂ ≤ G₂ := sup_le hL₁B hL₂B
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
    obtain ⟨e, he⟩ := P.two (x : MulAut V) (hAJ x.2)
    have hxe : (x : MulAut V) ^ 2 ^ e ∈ G₁ ⊓ G₂ := ⟨G₁.pow_mem x.2 _, hLB he⟩
    rw [hinf, Subgroup.mem_bot] at hxe
    have hord : orderOf (x : MulAut V) = 3 := by rw [Subgroup.orderOf_coe, hx]
    have hdvd : 3 ∣ 2 ^ e := hord ▸ orderOf_dvd_of_pow_eq_one hxe
    have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega

theorem swType_of_ffModule (h56 : AsB56) (hV : ∀ v : V, v ^ 2 = 1)
    {X : Subgroup (MulAut V)} {τ : MulAut V} (hτ : L₂ = L₁.map (MulAut.conj τ).toMonoidHom)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hn : ∀ x ∈ X, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂)
    (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂) (hFF : IsFFModule X)
    (hL₁J : L₁ ≤ ffJ X) (hL₂J : L₂ ≤ ffJ X) (hB53 : B53Hyp (ffJ X)) : SwType L₁ := by
  have hJX : ffJ X ≤ X := B6.ffJ_le X
  have P : SwData (ffJ X) L₁ L₂ :=
    ⟨hcomm, hq₁, hq₂, hL₁J, hL₂J, fun x hx l hl => hn x (hJX hx) l hl,
      fun x hx => h2 x (hJX hx)⟩
  have hcases := h56 V hV (ffJ X) (InternalSec.ffJ_ne_bot_of_isFFModule hV hFF) hB53
  have hL₂L₁ : SwType L₂ → SwType L₁ := fun h =>
    h.of_mulEquiv ((MulEquiv.subgroupCongr hτ).trans
      (Subgroup.equivMapOfInjective L₁ (MulAut.conj τ).toMonoidHom
        (MulAut.conj τ).injective).symm)
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | h3 | h4 | h5
  · exact (P.false_of_case1 h1.1).elim
  · exact (InternalSec.not_le_perm_three hq₁ hL₁J e).elim
  · rcases P.type_of_case3 h3 with h | h
    exacts [h, hL₂L₁ h]
  · exact (P.false_of_case4 h4).elim
  · rcases P.type_of_case5 h5 with h | h
    exacts [h, hL₂L₁ h]

end Cases

namespace WreathData

variable {G : Type} [Group G] [Finite G] {H R J J' : Subgroup G} {ρ : G}
  (d : WreathData H R J J' ρ)

include d

theorem swType (h56 : AsB56) (hA21 : AsA21SQTKSection) : SwType (wAut J J' R J) := by
  obtain ⟨hq₁, hq₂, hc, hconj, hn, h2', hO2⟩ := d.moduleFacts
  have hXr : wAut J J' R (wY J J' R) = (actY J J' R).range := (range_actY J J' R).symm
  have hτX := d.tau_mem
  have hL₁X := wAut_le_wAut J (J_le_wY J J' R)
  have hL₂X := wAut_le_wAut J' (J'_le_wY J J' R)
  have hFF := d.isFFModule_Y
  have hV := fun v : VMod J J' R => VMod_sq_eq_one v
  obtain ⟨hL₁J, hL₂J⟩ := S153M.twoA_le_ffJ hV hτX hL₁X hL₂X hc hn hconj h2' hq₁ hq₂ hO2 hFF
  have hB53 : B53Hyp (ffJ (wAut J J' R (wY J J' R))) := by
    rw [hXr] at hL₁J hL₂J hn h2' hO2 ⊢
    exact S153M.b53Hyp_of_two hA21 d.sqtk_Y (actY J J' R) hq₁ hq₂ hc hL₁J hL₂J hn h2' hO2
  exact swType_of_ffModule h56 hV hconj hq₁ hq₂ hc hn h2' hFF hL₁J hL₂J hB53

end WreathData

end CFSG.Quasithin.S146zW
