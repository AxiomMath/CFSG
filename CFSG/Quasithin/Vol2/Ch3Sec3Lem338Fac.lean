module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAdapter
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt

public section

namespace CFSG.Quasithin.H13.Ch3Sec3

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped commutatorElement

section Rigid

variable {Ω : Type} [Group Ω]

@[expose] def IsNormalRigid (Q : Subgroup Ω) : Prop :=
  ∀ N : Subgroup Ω, N ≤ Q → Q ≤ Subgroup.normalizer (N : Set Ω) →
    (∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a) → N = Q

theorem eq_of_subgroupOf_eq_top {N Q : Subgroup Ω} (hNQ : N ≤ Q) (h : N.subgroupOf Q = ⊤) :
    N = Q := by
  refine le_antisymm hNQ fun x hx => ?_
  have : (⟨x, hx⟩ : ↥Q) ∈ N.subgroupOf Q := h ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem isNormalRigid_of_isSimpleGroup {Q : Subgroup Ω} (hQ : IsSimpleGroup ↥Q) :
    IsNormalRigid Q := by
  intro N hNQ hQN hnc
  have : (N.subgroupOf Q).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNQ).mpr hQN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf Q) with h | h
  · exfalso
    obtain ⟨a, ha, b, -, hab⟩ := hnc
    have ha' : (⟨a, hNQ ha⟩ : ↥Q) ∈ N.subgroupOf Q := Subgroup.mem_subgroupOf.mpr ha
    rw [h, Subgroup.mem_bot] at ha'
    have ha1 : a = 1 := congrArg Subtype.val ha'
    exact hab (by rw [ha1, one_mul, mul_one])
  · exact eq_of_subgroupOf_eq_top hNQ h

theorem isNormalRigid_of_isQuasisimple {Q : Subgroup Ω} (hQ : CFSG.IsQuasisimple ↥Q) :
    IsNormalRigid Q := by
  intro N hNQ hQN hnc
  have : (N.subgroupOf Q).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNQ).mpr hQN
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
      (B1Red.isQuasisimple_to_open hQ) (N.subgroupOf Q) with h | h
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    have ha' : (⟨a, hNQ ha⟩ : ↥Q) ∈ N.subgroupOf Q := Subgroup.mem_subgroupOf.mpr ha
    have hz := Subgroup.mem_center_iff.mp (h ha') ⟨b, hNQ hb⟩
    exact hab (congrArg Subtype.val hz).symm
  · exact eq_of_subgroupOf_eq_top hNQ h

theorem false_of_isNormalRigid {Q K₁ K₂ : Subgroup Ω} (hQ : IsNormalRigid Q) (h₁ : K₁ ≤ Q)
    (h₂ : K₂ ≤ Q) (hQK : Q ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup Ω) : Set Ω))
    (hKK : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set Ω))
    (hnc : ∃ a ∈ K₁, ∃ b ∈ K₁, a * b ≠ b * a) (hne : K₂ ≠ ⊥) (hinf : K₁ ⊓ K₂ = ⊥) : False := by
  have hKQ : K₁ ⊔ K₂ = Q := hQ _ (sup_le h₁ h₂) hQK (by
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    exact ⟨a, Subgroup.mem_sup_left ha, b, Subgroup.mem_sup_left hb, hab⟩)
  have hK₁ : K₁ = Q := hQ _ h₁ ((le_of_eq hKQ.symm).trans hKK) hnc
  apply hne
  rw [eq_bot_iff, ← hinf]
  exact le_inf (le_of_le_of_eq h₂ hK₁.symm) le_rfl

theorem le_or_commute_of_isSimpleGroup {K N : Subgroup Ω} (hK : IsSimpleGroup ↥K)
    (hperf : ⁅K, K⁆ = K) (hKN : K ≤ Subgroup.normalizer (N : Set Ω))
    (hCK : ⁅K, N⁆ ≤ Subgroup.normalizer (K : Set Ω)) :
    K ≤ N ∨ ∀ a ∈ K, ∀ b ∈ N, a * b = b * a := by
  have hCN : ⁅K, N⁆ ≤ N := commutator_le_right_of_le_normalizer hKN
  have hKC : K ≤ Subgroup.normalizer ((⁅K, N⁆ : Subgroup Ω) : Set Ω) := fun x hx =>
    mem_normalizer_commutator (Subgroup.le_normalizer hx) (hKN hx)
  have : ((⁅K, N⁆ ⊓ K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun x hx =>
      mem_normalizer_inf (hKC hx) (Subgroup.le_normalizer hx)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((⁅K, N⁆ ⊓ K).subgroupOf K) with h | h
  · right
    have hbot : ⁅K, N⁆ ⊓ K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.2⟩ : ↥K) ∈ (⁅K, N⁆ ⊓ K).subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
    have h1 : ⁅⁅K, N⁆, K⁆ = ⊥ := by
      rw [eq_bot_iff, ← hbot]
      exact le_inf (commutator_le_left_of_le_normalizer hKC)
        (commutator_le_right_of_le_normalizer hCK)
    have h2 : ⁅⁅N, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm N K]; exact h1
    have h3 : ⁅⁅K, K⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hperf] at h3
    intro a ha b hb
    have := Subgroup.commutator_mem_commutator ha hb
    rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · left
    exact (le_of_eq (eq_of_subgroupOf_eq_top inf_le_right h).symm).trans (inf_le_left.trans hCN)

end Rigid

section Factor

variable {Ω : Type} [Group Ω]

theorem isSolvable_sl_two_zmodTwo :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  have hcard : Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 2 ^ 1 * 3 ^ 1 := by
    decide
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) hcard

theorem factorList_core {G₁ : Subgroup Ω} (hf : B56FactorList ↥G₁) :
    (∀ N : Subgroup Ω, N ≤ G₁ → Group.IsPerfect ↥N → N = ⊥) ∨
      ∃ Q : Subgroup Ω, Q ≤ G₁ ∧ IsNormalRigid Q ∧
        (∀ N : Subgroup Ω, N ≤ G₁ → Group.IsPerfect ↥N → N ≤ Q) ∧
        ((∃ n : ℕ, LieModel ↥Q .PSL 2 2 n) ∨
          ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
            Nonempty (↥Q ≃* ↥(StatedSL 3 F))) := by
  rcases hf with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | he | ⟨m, F, _, _, -, -, hF, ⟨e⟩⟩
  ·
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · left
      have hn1 : n = 1 := by omega
      subst hn1
      rw [pow_one] at hF
      intro N hN hperf
      by_contra hne
      have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hne
      have := isSolvable_sl_two_zmodTwo
      let f : ↥N →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
        (statedSLEquivZModTwo (n := 2) hF).toMonoidHom.comp
          (e.toMonoidHom.comp (Subgroup.inclusion hN))
      have hfi : Function.Injective f := fun x y hxy => Subgroup.inclusion_injective hN
        (e.injective ((statedSLEquivZModTwo (n := 2) hF).injective hxy))
      have : Group.IsSolvable ↥N := Group.isSolvable_of_isSolvable_injective hfi
      have : Group.IsPerfect ↥N := hperf
      exact Group.IsPerfect.not_isSolvable ↥N inferInstance
    · right
      have : Fintype F := Fintype.ofFinite F
      have h4 : ∃ s : Finset F, s.card = 4 := by
        have h4' : 4 ≤ (Finset.univ : Finset F).card := by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
        obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4'
        exact ⟨s, hs⟩
      have hq : CFSG.IsQuasisimple ↥G₁ :=
        CFSG.QuasithinUnique.Setup.Campbell.isQuasisimple_of_mulEquiv
          (e.trans (specialLinearGroupEquivStatedSL 2 F).symm).symm
          (CFSG.QuasithinUnique.Setup.Campbell.isQuasisimple_sl2 h4)
      have : Nontrivial ↥G₁ := CFSG.LocalCores.isQuasisimple_nontrivial hq
      exact ⟨G₁, le_rfl, isNormalRigid_of_isQuasisimple hq, fun N hN _ => hN,
        Or.inl ⟨n, lieModel_psl_two_of_mulEquiv hq.1 hF e⟩⟩
  ·
    right
    obtain ⟨e⟩ := he
    set A : Subgroup ↥G₁ := (alternatingGroup (Fin 5)).map (e.symm : Equiv.Perm (Fin 5) →* ↥G₁)
      with hA
    set Q : Subgroup Ω := A.map G₁.subtype with hQ
    have eQ : ↥Q ≃* ↥(alternatingGroup (Fin 5)) :=
      (A.equivMapOfInjective G₁.subtype G₁.subtype_injective).symm.trans
        (e.symm.subgroupMap (alternatingGroup (Fin 5))).symm
    have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have hsQ : IsSimpleGroup ↥Q := eQ.isSimpleGroup
    refine ⟨Q, Subgroup.map_subtype_le A, isNormalRigid_of_isSimpleGroup hsQ,
      fun N hN hperf => ?_, Or.inl ⟨2, Or.inl ⟨by decide,
        CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five _ ⟨eQ⟩⟩⟩⟩
    intro x hx
    have : Group.IsPerfect ↥N := hperf
    set f : ↥N →* ℤˣ := Equiv.Perm.sign.comp (e.toMonoidHom.comp (Subgroup.inclusion hN)) with hfd
    have hf : f ⟨x, hx⟩ = 1 := by
      have h1 := Abelianization.commutator_subset_ker f
      rw [Group.IsPerfect.commutator_eq_top] at h1
      exact h1 (Subgroup.mem_top _)
    have hmem : e ⟨x, hN hx⟩ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr hf
    exact ⟨⟨x, hN hx⟩, ⟨e ⟨x, hN hx⟩, hmem, e.symm_apply_apply _⟩, rfl⟩
  ·
    right
    have hq : CFSG.IsQuasisimple ↥G₁ :=
      CFSG.QuasithinUnique.Setup.Campbell.isQuasisimple_of_mulEquiv
        (e.trans (specialLinearGroupEquivStatedSL 3 F).symm).symm
        (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl)
    exact ⟨G₁, le_rfl, isNormalRigid_of_isQuasisimple hq, fun N hN _ => hN,
      Or.inr ⟨m, F, inferInstance, inferInstance, hF, ⟨e⟩⟩⟩

end Factor

section Cases

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem false_of_commute_sup {K G₁ G₂ : Subgroup (MulAut V)} (hK : K ≤ G₁ ⊔ G₂)
    (hnc : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a) (h₁ : ∀ a ∈ K, ∀ b ∈ G₁, a * b = b * a)
    (h₂ : ∀ a ∈ K, ∀ b ∈ G₂, a * b = b * a) : False := by
  have hle : G₁ ⊔ G₂ ≤ Subgroup.centralizer (K : Set (MulAut V)) :=
    sup_le (fun g hg => Subgroup.mem_centralizer_iff.mpr fun k hk => h₁ k hk g hg)
      (fun g hg => Subgroup.mem_centralizer_iff.mpr fun k hk => h₂ k hk g hg)
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  exact hab (Subgroup.mem_centralizer_iff.mp (hle (hK hb)) a ha)

omit [Finite V] in
theorem le_normalizer_of_conj {J K : Subgroup (MulAut V)}
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) : J ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
  fun x hx => Subgroup.mem_normalizer_iff.mpr fun k =>
    ⟨fun hk => hn x hx k hk, fun hk => by
      have := hn x⁻¹ (J.inv_mem hx) _ hk
      simpa [mul_assoc] using this⟩

theorem type_of_b56Cases
    {J K₁ K₂ : Subgroup (MulAut V)} (hq₁ : CFSG.IsQuasisimple ↥K₁)
    (hs₁ : IsSimpleGroup ↥K₁) (hq₂ : CFSG.IsQuasisimple ↥K₂) (hs₂ : IsSimpleGroup ↥K₂)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hinf : K₁ ⊓ K₂ = ⊥) (hK₁J : K₁ ≤ J)
    (hK₂J : K₂ ≤ J)
    (hJK : J ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup (MulAut V)) : Set (MulAut V)))
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    (∃ n : ℕ, LieModel ↥K₁ .PSL 2 2 n) ∨
      ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
        Nonempty (↥K₁ ≃* ↥(StatedSL 3 F)) := by
  have hperf₁ : ⁅K₁, K₁⁆ = K₁ := commutator_eq_self_of_isPerfect hq₁.1
  have hperf₂ : ⁅K₂, K₂⁆ = K₂ := commutator_eq_self_of_isPerfect hq₂.1
  have hK₂N : K₂ ≤ Subgroup.normalizer (K₁ : Set (MulAut V)) := le_normalizer_of_commute hc
  have hK₁N : K₁ ≤ Subgroup.normalizer (K₂ : Set (MulAut V)) :=
    le_normalizer_of_commute fun a ha b hb => (hc b hb a ha).symm
  have hKN₁ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set (MulAut V)) :=
    sup_le Subgroup.le_normalizer hK₂N
  have hKN₂ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set (MulAut V)) :=
    sup_le hK₁N Subgroup.le_normalizer
  have hKJ : K₁ ⊔ K₂ ≤ J := sup_le hK₁J hK₂J
  have hnc : ∀ {K : Subgroup (MulAut V)}, CFSG.IsQuasisimple ↥K →
      ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := fun hq => by
    obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple hq
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  have hne : ∀ {K : Subgroup (MulAut V)}, CFSG.IsQuasisimple ↥K → K ≠ ⊥ := fun hq hb => by
    obtain ⟨a, ha, b, -, hab⟩ := hnc hq
    rw [hb, Subgroup.mem_bot] at ha
    exact hab (by rw [ha, one_mul, mul_one])
  have habs : ∀ Q : Subgroup (MulAut V), IsNormalRigid Q → K₁ ≤ Q → K₂ ≤ Q →
      Q ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup (MulAut V)) : Set (MulAut V)) → False :=
    fun Q hQ h₁ h₂ hQK => false_of_isNormalRigid hQ h₁ h₂ hQK hKN₁ (hnc hq₁) (hne hq₂) hinf
  have hdich : ∀ N : Subgroup (MulAut V), N ≤ J → J ≤ Subgroup.normalizer (N : Set (MulAut V)) →
      (K₁ ≤ N ∨ ∀ a ∈ K₁, ∀ b ∈ N, a * b = b * a) ∧
        (K₂ ≤ N ∨ ∀ a ∈ K₂, ∀ b ∈ N, a * b = b * a) := by
    intro N hNJ hJN
    have hCK : ∀ {K : Subgroup (MulAut V)}, K ≤ K₁ ⊔ K₂ → ⁅K, N⁆ ≤ K₁ ⊔ K₂ := fun hK =>
      (Subgroup.commutator_mono hK hNJ).trans (commutator_le_left_of_le_normalizer hJK)
    exact ⟨le_or_commute_of_isSimpleGroup hs₁ hperf₁ (hK₁J.trans hJN)
        ((hCK le_sup_left).trans hKN₁),
      le_or_commute_of_isSimpleGroup hs₂ hperf₂ (hK₂J.trans hJN) ((hCK le_sup_right).trans hKN₂)⟩
  have hcore : ∀ A B : Subgroup (MulAut V), A ⊓ B = ⊥ → B56FactorList ↥A → A ≤ J →
      J ≤ Subgroup.normalizer (A : Set (MulAut V)) → K₁ ≤ A → (K₂ ≤ A ∨ K₂ ≤ B) →
      (∃ n : ℕ, LieModel ↥K₁ .PSL 2 2 n) ∨
        ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
          Nonempty (↥K₁ ≃* ↥(StatedSL 3 F)) := by
    intro A B hAB hfA hAJ hJA h₁ h₂
    rcases factorList_core hfA with h0 | ⟨Q, hQA, hQ, hQp, htype⟩
    · exact absurd (h0 K₁ h₁ hq₁.1) (hne hq₁)
    have h₁Q : K₁ ≤ Q := hQp K₁ h₁ hq₁.1
    rcases h₂ with h₂ | h₂
    · exact (habs Q hQ h₁Q (hQp K₂ h₂ hq₂.1) (hQA.trans (hAJ.trans hJK))).elim
    ·
      have hKA : ∀ x ∈ K₁ ⊔ K₂, x ∈ A → x ∈ K₁ := by
        intro x hx hxA
        obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hK₂N).mp hx
        have hk₂A : k₂ ∈ A := by
          have : k₂ = k₁⁻¹ * (k₁ * k₂) := by group
          rw [this]
          exact A.mul_mem (A.inv_mem (h₁ hk₁)) hxA
        have hk₂1 : k₂ = 1 := by
          have : k₂ ∈ A ⊓ B := ⟨hk₂A, h₂ hk₂⟩
          rwa [hAB, Subgroup.mem_bot] at this
        rw [hk₂1, mul_one]
        exact hk₁
      have hAN : A ≤ Subgroup.normalizer (K₁ : Set (MulAut V)) := by
        refine le_normalizer_of_conj fun x hx k hk => hKA _ ?_ ?_
        · exact (Subgroup.mem_normalizer_iff.mp (hJK (hAJ hx)) k).mp (Subgroup.mem_sup_left hk)
        · exact A.mul_mem (A.mul_mem hx (h₁ hk)) (A.inv_mem hx)
      have hK₁Q : K₁ = Q := hQ K₁ h₁Q (hQA.trans hAN) (hnc hq₁)
      subst hK₁Q
      exact htype
  have hprod : ∀ G₁ G₂ : Subgroup (MulAut V), G₁ ⊔ G₂ = J → G₁ ⊓ G₂ = ⊥ →
      (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) → B56FactorList ↥G₁ → B56FactorList ↥G₂ →
      (∃ n : ℕ, LieModel ↥K₁ .PSL 2 2 n) ∨
        ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
          Nonempty (↥K₁ ≃* ↥(StatedSL 3 F)) := by
    intro G₁ G₂ hsup hinf₁₂ hc₁₂ hf₁ hf₂
    have hc₂₁ : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc₁₂ b hb a ha).symm
    have hG₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
    have hG₂J : G₂ ≤ J := by rw [← hsup]; exact le_sup_right
    have hJG₁ : J ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) := by
      rw [← hsup]
      exact sup_le Subgroup.le_normalizer (le_normalizer_of_commute hc₁₂)
    have hJG₂ : J ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) := by
      rw [← hsup]
      exact sup_le (le_normalizer_of_commute hc₂₁) Subgroup.le_normalizer
    have hinf₂₁ : G₂ ⊓ G₁ = ⊥ := by rw [inf_comm]; exact hinf₁₂
    obtain ⟨d₁₁, d₂₁⟩ := hdich G₁ hG₁J hJG₁
    obtain ⟨d₁₂, d₂₂⟩ := hdich G₂ hG₂J hJG₂
    have hK₁s : K₁ ≤ G₁ ⊔ G₂ := by rw [hsup]; exact hK₁J
    have hK₂s : K₂ ≤ G₁ ⊔ G₂ := by rw [hsup]; exact hK₂J
    have h₂ : K₂ ≤ G₁ ∨ K₂ ≤ G₂ := by
      rcases d₂₁ with h | c₁
      · exact Or.inl h
      rcases d₂₂ with h | c₂
      · exact Or.inr h
      exact (false_of_commute_sup hK₂s (hnc hq₂) c₁ c₂).elim
    rcases d₁₁ with h₁ | c₁ <;> rcases d₁₂ with h₁' | c₂
    · have h12 : K₁ ≤ G₁ ⊓ G₂ := le_inf h₁ h₁'
      rw [hinf₁₂] at h12
      exact absurd (le_bot_iff.mp h12) (hne hq₁)
    · exact hcore G₁ G₂ hinf₁₂ hf₁ hG₁J hJG₁ h₁ h₂
    · exact hcore G₂ G₁ hinf₂₁ hf₂ hG₂J hJG₂ h₁' h₂.symm
    · exact (false_of_commute_sup hK₁s (hnc hq₁) c₁ c₂).elim
  rcases hcases with ⟨hE, -, -⟩ | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, hinf₁₂, hc₁₂, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc₁₂, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, hinf₁₂, hc₁₂, -, ⟨e₁⟩, -, -, h₂⟩
  ·
    exfalso
    have hcomp : ∀ {K : Subgroup (MulAut V)}, CFSG.IsQuasisimple ↥K → K ≤ K₁ ⊔ K₂ →
        K₁ ⊔ K₂ ≤ Subgroup.normalizer (K : Set (MulAut V)) → K ≤ quasithinGenFitting J := by
      intro K hq hK hKn
      refine le_sup_of_le_right (le_sSup ⟨hK.trans hKJ, ?_, B1Red.isQuasisimple_to_open hq⟩)
      exact IsSubnormal.step hK ((Subgroup.normal_subgroupOf_iff_le_normalizer hK).mpr hKn)
        (IsSubnormal.step hKJ ((Subgroup.normal_subgroupOf_iff_le_normalizer hKJ).mpr hJK)
          (IsSubnormal.refl J))
    exact habs _ (isNormalRigid_of_isQuasisimple hE) (hcomp hq₁ le_sup_left hKN₁)
      (hcomp hq₂ le_sup_right hKN₂) ((quasithinGenFitting_le J).trans hJK)
  ·
    exact (InternalSec.not_le_perm_three hq₁ hK₁J e).elim
  ·
    exact hprod G₁ G₂ hsup hinf₁₂ hc₁₂ hf₁ hf₂
  ·
    exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc₂₁ : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc₁₂ b hb a ha).symm
    have htN : t ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
      InternalSec.mem_normalizer_sup ht₁ ht₂
    have hsub : ∀ {K : Subgroup (MulAut V)}, K ≤ J → Group.IsPerfect ↥K → K ≤ G₁ ⊔ G₂ := by
      intro K hK hp
      rw [hJt] at hK
      exact (InternalSec.le_commutator_of_perfect hK hp).trans
        (InternalSec.commutator_le_of_zpowers htN)
    have hG₁J : G₁ ≤ J := by rw [hJt]; exact le_sup_left.trans le_sup_left
    have hG₂J : G₂ ≤ J := by rw [hJt]; exact le_sup_right.trans le_sup_left
    have hJG₁ : J ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) := by
      rw [hJt]
      exact sup_le (sup_le Subgroup.le_normalizer (le_normalizer_of_commute hc₁₂))
        (Subgroup.zpowers_le.mpr ht₁)
    have hJG₂ : J ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) := by
      rw [hJt]
      exact sup_le (sup_le (le_normalizer_of_commute hc₂₁) Subgroup.le_normalizer)
        (Subgroup.zpowers_le.mpr ht₂)
    obtain ⟨d₁₁, d₂₁⟩ := hdich G₁ hG₁J hJG₁
    obtain ⟨d₁₂, d₂₂⟩ := hdich G₂ hG₂J hJG₂
    have hin : ∀ {K : Subgroup (MulAut V)}, CFSG.IsQuasisimple ↥K → K ≤ J →
        (K ≤ G₁ ∨ ∀ a ∈ K, ∀ b ∈ G₁, a * b = b * a) →
        (K ≤ G₂ ∨ ∀ a ∈ K, ∀ b ∈ G₂, a * b = b * a) → K ≤ G₁ := by
      intro K hq hKJ' d₁ d₂
      rcases d₁ with h | c₁
      · exact h
      rcases d₂ with h | c₂
      · exact (InternalSec.not_le_of_card_prime hq h hc₂).elim
      · exact (false_of_commute_sup (hsub hKJ' hq.1) (hnc hq) c₁ c₂).elim
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact habs G₁ (isNormalRigid_of_isSimpleGroup e₁.isSimpleGroup) (hin hq₁ hK₁J d₁₁ d₁₂)
      (hin hq₂ hK₂J d₂₁ d₂₂) (hG₁J.trans hJK)
  ·
    have hF2 : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod, pow_one]
    have hf₁ : B56FactorList ↥G₁ :=
      Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, le_rfl, odd_one, hF2, ⟨e₁⟩⟩)
    have hf₂ : B56FactorList ↥G₂ := by
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hF, hR⟩
      · exact Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, le_rfl, odd_one, hF2, ⟨e₂⟩⟩)
      · obtain ⟨e₂⟩ := nonempty_mulEquiv_of_realizes (FFModel.nat_faithful _) hR
        exact Or.inl ⟨n, F, inferInstance, inferInstance, Hyp331.one_le_of_card hF, hF, ⟨e₂⟩⟩
    exact hprod G₁ G₂ hsup hinf₁₂ hc₁₂ hf₁ hf₂

end Cases

end CFSG.Quasithin.H13.Ch3Sec3
