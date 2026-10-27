module

public import CFSG.Quasithin.Vol2.Ch11SecO6S4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD.O6S

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecG.Bar
open CFSG.Quasithin.Vol2.Ch11.O6
open scoped MatrixGroups

section Bar

variable {G : Type} [Group G] {K L₁ : Subgroup G}

theorem mk_eq_one_iff_mem (k : ↥K) : (k : KBar K) = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
  rw [QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf, Subgroup.mem_subgroupOf]

theorem mk_commute_of_comm_mem {c l : G} (hc : c ∈ K) (hl : l ∈ K)
    (h : c * l * c⁻¹ * l⁻¹ ∈ pCoreOf 2 K) :
    ((⟨c, hc⟩ : ↥K) : KBar K) * ((⟨l, hl⟩ : ↥K) : KBar K) =
      ((⟨l, hl⟩ : ↥K) : KBar K) * ((⟨c, hc⟩ : ↥K) : KBar K) := by
  have h1 := (mk_eq_one_iff_mem ((⟨c, hc⟩ : ↥K) * (⟨l, hl⟩ : ↥K) * (⟨c, hc⟩ : ↥K)⁻¹ *
    (⟨l, hl⟩ : ↥K)⁻¹)).mpr h
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem mem_sectionCentralizer_sup {r : ℕ} (hL : L₁ ≤ K) {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (haL : a ∈ Subgroup.normalizer (L₁ : Set G))
    (hP : ∀ x ∈ CFSG.pCore r (KBar K), aut K ⟨a, ha⟩ x = x)
    (hL₁ : ∀ x ∈ l1Bar K L₁, aut K ⟨a, ha⟩ x = x) :
    a ∈ sectionCentralizer (oTwoPrime K r ⊔ L₁) (pCoreOf 2 K) := by
  refine ⟨Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨normalizer_le_normalizer_oTwoPrime K r ha, haL⟩,
    LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K ha, fun x hx => ?_⟩
  have hx' : x ∈ ((oTwoPrime K r ⊔ L₁ : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (hL.trans (le_normalizer_oTwoPrime K r))] at hx'
  obtain ⟨u, hu, l, hl, rfl⟩ := hx'
  have huK : u ∈ K := oTwoPrime_le K r hu
  have hxK : u * l ∈ K := K.mul_mem huK (hL hl)
  have hu' : ((⟨u, huK⟩ : ↥K) : KBar K) ∈ CFSG.pCore r (KBar K) :=
    (mem_oTwoPrime_iff ⟨u, huK⟩).mp hu
  have hl' : ((⟨l, hL hl⟩ : ↥K) : KBar K) ∈ l1Bar K L₁ := l1Map_mem hL ⟨l, hl⟩
  have hfix : aut K ⟨a, ha⟩ ((⟨u * l, hxK⟩ : ↥K) : KBar K) = ((⟨u * l, hxK⟩ : ↥K) : KBar K) := by
    have e : ((⟨u * l, hxK⟩ : ↥K) : KBar K) =
        ((⟨u, huK⟩ : ↥K) : KBar K) * ((⟨l, hL hl⟩ : ↥K) : KBar K) := by
      rw [← QuotientGroup.mk_mul]
      rfl
    rw [e, map_mul, hP _ hu', hL₁ _ hl']
  have h1 := mk_commK ha hxK
  rw [hfix, mul_inv_cancel] at h1
  exact (mk_eq_one_iff_mem _).mp h1

end Bar

section Fitting

variable {X : Type} [Group X] [Finite X] {r : ℕ} [Fact r.Prime]

theorem eq_one_of_mem_pCore_of_not_dvd (hrF : ¬ r ∣ Nat.card (CFSG.fittingSubgroup X)) {d : X}
    (hd : d ∈ CFSG.pCore r X) : d = 1 := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := r) (G := X))
  have hdvd : Nat.card (CFSG.pCore r X) ∣ Nat.card (CFSG.fittingSubgroup X) :=
    Subgroup.card_dvd_of_le (CFSG.pCore_le_fitting X r)
  have hm0 : m = 0 := by
    by_contra hm0
    exact hrF ((dvd_pow_self r hm0).trans (hm ▸ hdvd))
  rw [hm0, pow_zero] at hm
  rw [Subgroup.eq_bot_of_card_eq _ hm] at hd
  exact Subgroup.mem_bot.mp hd

end Fitting

theorem dvd_card_fitting_of_not_le {G : Type} [Group G] [Finite G] {K : Subgroup G} {r : ℕ}
    [Fact r.Prime] (h : ¬ oTwoPrime K r ≤ pCoreOf 2 K) :
    r ∣ Nat.card (CFSG.fittingSubgroup (KBar K)) := by
  by_contra hrF
  apply h
  rintro _ ⟨y, hy, rfl⟩
  have h1 := eq_one_of_mem_pCore_of_not_dvd hrF (Subgroup.mem_comap.mp hy)
  rw [QuotientGroup.mk'_apply] at h1
  exact (mk_eq_one_iff_mem y).mp h1

section M2P


theorem factM2Case1Prime_holds : FactM2Case1Prime := by
  intro G _ _ K L₁ R n r hlist h1 hKperf hL₁K hperf ⟨F₄, _, _, hF₄, ⟨eL⟩⟩ _ hRK hRL hRL₁ hr
    A hAR hA
  obtain ⟨p, hp, hp5', φK, hφKs, hφKk⟩ := h1
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hp5 : 5 ≤ p := by rcases hp5' with h | h <;> omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨φ, hφs, hφk, -⟩ := exists_kBar_hom hφKs hφKk
  have hn : n = 2 := by
    rcases hlist with h | ⟨h, -⟩
    · exact (false_of_list2 h hp2 hφs).elim
    · exact h
  subst hn
  have hF₄' : Nat.card F₄ = 4 := by rw [hF₄]; norm_num
  have h60 := index_pCore_eq_sixty hF₄' eL
  have hD : Case1Data (KBar K) := case1Data_of_shape (shape_of_lists hlist hp2 hφs)
  have hOF : CFSG.oddCore (KBar K) = CFSG.fittingSubgroup (KBar K) := oddCore_eq hD
  have hKb : ⁅(⊤ : Subgroup (KBar K)), (⊤ : Subgroup (KBar K))⁆ = ⊤ :=
    commutator_top_eq_top hKperf
  have hfixL : ∀ a (ha : a ∈ R), ∀ x ∈ l1Bar K L₁, aut K ⟨a, hRK ha⟩ x = x := fun a ha =>
    aut_eq_self_of_comm hp5 hφk hL₁K hperf h60 (hRK ha)
      (fun l hl => hRL₁ (Subgroup.commutator_mem_commutator ha hl))
  have hinC : ∀ a (ha : a ∈ A), (∀ x ∈ CFSG.pCore r (KBar K), aut K ⟨a, hRK (hAR ha)⟩ x = x) →
      a ∈ sectionCentralizer (oTwoPrime K r ⊔ L₁) (pCoreOf 2 K) := fun a ha h =>
    mem_sectionCentralizer_sup hL₁K (hRK (hAR ha)) (hRL (hAR ha)) h (hfixL a (hAR ha))
  by_cases hrF : r ∣ Nat.card (CFSG.fittingSubgroup (KBar K))
  swap
  · refine mQuot_le_one_of fun a ha _ _ haC _ => absurd (hinC a ha fun x hx => ?_) haC
    rw [eq_one_of_mem_pCore_of_not_dvd hrF hx, map_one]
  have hr2 : r ≠ 2 := by
    have := hD.struct.2.1 r hr hrF
    omega
  have hna := exists_not_triv r hD hrF (Or.inl hKb)
  have hFt : ∀ f ∈ CFSG.fittingSubgroup (KBar K),
      ActsTriviallyOnFrattiniQuotient (CFSG.pCore r (KBar K)) f := fun f hf =>
    fitting_acts_triv r hf
  have hRK₂ := SecE.sl2pSignalizerFact_holds G K L₁ R p hp hp5' ⟨φK, hφKs, hφKk⟩ hL₁K hperf
    ⟨F₄, inferInstance, inferInstance, hF₄', ⟨eL⟩⟩ hRK hRL hRL₁
  have hcomm : ∀ a (ha : a ∈ R) (x : KBar K),
      x⁻¹ * aut K ⟨a, hRK ha⟩ x ∈ CFSG.fittingSubgroup (KBar K) := fun a ha x => by
    rw [← hOF]
    exact inv_mul_aut_mem_oddCore (hRK ha)
      (fun k hk => hRK₂ (Subgroup.commutator_mem_commutator ha hk)) x
  have hαsq : ∀ a (ha : a ∈ A), (aut K ⟨a, hRK (hAR ha)⟩) ^ 2 ^ 1 = 1 := fun a ha => by
    rw [pow_one, ← map_pow]
    have : (⟨a, hRK (hAR ha)⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 = 1 :=
      Subtype.ext (by simp [hA.2 a ha])
    rw [this, map_one]
  have hsign : ∀ a (ha : a ∈ A), ActsScalar r (aut K ⟨a, hRK (hAR ha)⟩) 1 ∨
      ActsScalar r (aut K ⟨a, hRK (hAR ha)⟩) (r - 1) := by
    intro a ha
    obtain ⟨k, hk⟩ := actsScalar_of_comm r (hD.rank r hr hrF) hFt hna (hcomm a (hAR ha))
    have h2 : ActsScalar r ((aut K ⟨a, hRK (hAR ha)⟩) ^ 2) 1 := by
      have h := hαsq a ha
      rw [pow_one] at h
      rw [h]
      intro d _
      simp
    exact actsScalar_sign r hk h2
  have hinC' : ∀ a (ha : a ∈ A), ActsScalar r (aut K ⟨a, hRK (hAR ha)⟩) 1 →
      a ∈ sectionCentralizer (oTwoPrime K r ⊔ L₁) (pCoreOf 2 K) := fun a ha h =>
    hinC a ha (fix_of_actsScalar_one r hr2 (hαsq a ha) h)
  refine mQuot_le_one_of fun a ha b hb haC hbC => ?_
  have hna' := (hsign a ha).resolve_left fun h => haC (hinC' a ha h)
  have hnb' := (hsign b hb).resolve_left fun h => hbC (hinC' b hb h)
  have hmul : aut K ⟨a * b, hRK (hAR (A.mul_mem ha hb))⟩ =
      aut K ⟨a, hRK (hAR ha)⟩ * aut K ⟨b, hRK (hAR hb)⟩ := by
    rw [← map_mul]
    rfl
  refine hinC' (a * b) (A.mul_mem ha hb) ?_
  rw [hmul]
  exact actsScalar_one_of_mod (ActsScalar.mul r hna' hnb')
    (sub_one_mul_sub_one_mod (Fact.out : r.Prime).two_le)

end M2P

end CFSG.Quasithin.Vol2.Ch11.SecD.O6S
