module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45K22pNonA
public import CFSG.HardMathSupport.Solomon.Coordinator.B0TSylow
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open K22p
open CFSG.ABGLocalTools

theorem eq_or_inf_eq_bot_of_normal_isSimple {Γ : Type*} [Group Γ]
    {K₁ K₂ : Subgroup Γ} (h₁n : K₁.Normal) (h₂n : K₂.Normal)
    (h₁ : IsSimpleGroup ↥K₁) (h₂ : IsSimpleGroup ↥K₂) :
    K₁ = K₂ ∨ K₁ ⊓ K₂ = ⊥ := by
  haveI : IsSimpleGroup ↥K₁ := h₁
  haveI : IsSimpleGroup ↥K₂ := h₂
  haveI : K₁.Normal := h₁n
  haveI : K₂.Normal := h₂n
  have hinf : (K₁ ⊓ K₂).Normal := Subgroup.normal_inf_normal K₁ K₂
  haveI hinf₁ : ((K₁ ⊓ K₂).subgroupOf K₁).Normal := hinf.subgroupOf K₁
  haveI hinf₂ : ((K₁ ⊓ K₂).subgroupOf K₂).Normal := hinf.subgroupOf K₂
  have h₁' := Subgroup.Normal.eq_bot_or_eq_top ((K₁ ⊓ K₂).subgroupOf K₁)
  have h₂' := Subgroup.Normal.eq_bot_or_eq_top ((K₁ ⊓ K₂).subgroupOf K₂)
  rcases h₁' with h | h
  · exact Or.inr (Disjoint.eq_bot_of_le (Subgroup.subgroupOf_eq_bot.mp h) inf_le_left)
  have hle₁ : K₁ ≤ K₂ := (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_right
  rcases h₂' with h' | h'
  · exact Or.inr (Disjoint.eq_bot_of_le (Subgroup.subgroupOf_eq_bot.mp h') inf_le_right)
  exact Or.inl (le_antisymm hle₁ ((Subgroup.subgroupOf_eq_top.mp h').trans inf_le_left))

theorem map_eq_or_inf_eq_bot {M : Type*} [Group M] [Finite M] (σ : MulAut M)
    {N S : Subgroup M} (hN : N.Normal) (hσinv : ∀ x ∈ N, σ x ∈ N)
    (hSN : (S.subgroupOf N).Normal) (hSle : S ≤ N) (hS : IsSimpleGroup ↥S) :
    S.map σ.toMonoidHom = S ∨ S.map σ.toMonoidHom ⊓ S = ⊥ := by
  haveI : IsSimpleGroup ↥S := hS
  have hSmaple : (S.map σ.toMonoidHom : Subgroup M) ≤ N :=
    Subgroup.map_le_iff_le_comap.mpr fun x hx => hσinv x (hSle hx)
  have hnorm : ((S.map σ.toMonoidHom).subgroupOf N).Normal := by
    refine ⟨fun x hx n => ?_⟩
    obtain ⟨s, hs, hxs⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
    have htN : σ⁻¹ (n : M) ∈ N :=
      zpow_mem_of_mem_of_invariant hσinv
        (Subgroup.inv_mem (Subgroup.zpowers σ) (Subgroup.mem_zpowers σ)) n.2
    have hconj : (⟨σ⁻¹ (n : M), htN⟩ : ↥N) * ⟨s, hSle hs⟩ * (⟨σ⁻¹ (n : M), htN⟩ : ↥N)⁻¹
        ∈ S.subgroupOf N :=
      hSN.conj_mem ⟨s, hSle hs⟩ hs ⟨σ⁻¹ (n : M), htN⟩
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_map.mpr ⟨σ⁻¹ (n : M) * s * (σ⁻¹ (n : M))⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mp hconj
    · have hv : σ (σ⁻¹ (n : M)) = (n : M) := MulAut.apply_inv_self M σ (n : M)
      have hxs' : σ s = (x : M) := hxs
      have heq : σ (σ⁻¹ (n : M) * s * (σ⁻¹ (n : M))⁻¹) =
          ((n * x * n⁻¹ : ↥N) : M) := by
        rw [map_mul, map_mul, map_inv, hxs', hv]
        rfl
      exact heq
  have hSsub : IsSimpleGroup ↥(S.subgroupOf N) :=
    (Subgroup.subgroupOfEquivOfLe hSle).isSimpleGroup
  have hSmap_simple : IsSimpleGroup ↥((S.map σ.toMonoidHom).subgroupOf N) := by
    haveI : IsSimpleGroup ↥(S.map σ.toMonoidHom) :=
      (Subgroup.equivMapOfInjective S σ.toMonoidHom σ.injective).symm.isSimpleGroup
    exact (Subgroup.subgroupOfEquivOfLe hSmaple).isSimpleGroup
  rcases eq_or_inf_eq_bot_of_normal_isSimple hnorm hSN hSmap_simple hSsub with h | h
  · left
    have h' := congrArg (Subgroup.map N.subtype) h
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hSmaple, inf_eq_left.mpr hSle] at h'
  · right
    have h' := Subgroup.map_inf ((S.map σ.toMonoidHom).subgroupOf N) (S.subgroupOf N) N.subtype
      N.subtype_injective
    rw [h, Subgroup.map_bot] at h'
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hSmaple, inf_eq_left.mpr hSle] at h'
    exact h'.symm

theorem exists_sylow_map_eq_inf {M : Type*} [Group M] [Finite M] {ℓ : ℕ} [Fact ℓ.Prime]
    (Q : Sylow ℓ M) {N S : Subgroup M} [N.Normal] (hSN : (S.subgroupOf N).Normal)
    (hSle : S ≤ N) :
    ∃ P : Sylow ℓ ↥S, (P : Subgroup ↥S).map S.subtype = (Q : Subgroup M) ⊓ S := by
  obtain ⟨QN, hQN⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_sylow_inf_normal Q N
  haveI := hSN
  have hnorm : N ≤ Subgroup.normalizer (S : Set M) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hSle
  have h := IsSylowOf.inf_of_le_normalizer (P := (Q : Subgroup M) ⊓ N) (K := N) (N := S)
    ⟨QN, hQN⟩ hSle hnorm
  have heq : ((Q : Subgroup M) ⊓ N) ⊓ S = (Q : Subgroup M) ⊓ S := by
    rw [inf_assoc, inf_eq_right.mpr hSle]
  rw [heq] at h
  exact h

theorem exists_ne_one_mem_inf_of_dvd_card {M : Type*} [Group M] [Finite M] {ℓ : ℕ}
    [Fact ℓ.Prime] {Q : Sylow ℓ M} {N S : Subgroup M} [N.Normal]
    (hSN : (S.subgroupOf N).Normal) (hSle : S ≤ N) (hdiv : ℓ ∣ Nat.card S) :
    ∃ y ∈ (Q : Subgroup M) ⊓ S, y ≠ 1 := by
  obtain ⟨P, hP⟩ := exists_sylow_map_eq_inf Q hSN hSle
  have hne : (P : Subgroup ↥S) ≠ ⊥ := P.ne_bot_of_dvd_card hdiv
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨((x : ↥S) : M), ?_, ?_⟩
  · rw [← hP]
    exact Subgroup.mem_map_of_mem S.subtype x.2
  · intro h
    exact hx1 (Subtype.ext (Subtype.ext h))

theorem exists_prime_dvd_card_ne_two_ne {S : Type*} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ¬ IsMulCommutative S) (p : ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ p ∧ q ∣ Nat.card S := by
  haveI : IsSimpleGroup S := hS
  have hnsolv : ¬ Group.IsSolvable S := fun hsolv =>
    hna (IsMulCommutative.of_comm (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv))
  have h3 : 3 ≤ (Nat.card S).primeFactors.card := by
    by_contra h
    push Not at h
    exact hnsolv
      (CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two (by omega))
  have hex : ∃ q ∈ (Nat.card S).primeFactors, q ≠ 2 ∧ q ≠ p := by
    by_contra h
    push Not at h
    have hsub : (Nat.card S).primeFactors ⊆ ({2, p} : Finset ℕ) := fun q hq => by
      by_cases h2 : q = 2
      · simp [h2]
      · simp [h q hq h2]
    have hc := Finset.card_le_card hsub
    have h2c : ({2, p} : Finset ℕ).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨q, hqmem, hq2, hqp⟩ := hex
  exact ⟨q, Nat.prime_of_mem_primeFactors hqmem, hq2, hqp, Nat.dvd_of_mem_primeFactors hqmem⟩

theorem false_of_moved_simple_factor {M : Type} [Group M] [Finite M] (σ : MulAut M)
    {N S : Subgroup M} [hN : N.Normal] (hσinv : ∀ x ∈ N, σ x ∈ N)
    (hSN : (S.subgroupOf N).Normal) (hSle : S ≤ N) (hSsimple : IsSimpleGroup ↥S)
    (hSna : ¬ IsMulCommutative ↥S) (p : ℕ) (hmoved : S.map σ.toMonoidHom ≠ S)
    (hfix : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → FixesSylow σ q) : False := by
  have hdisj : S.map σ.toMonoidHom ⊓ S = ⊥ := by
    rcases map_eq_or_inf_eq_bot σ hN hσinv hSN hSle hSsimple with h | h
    · exact absurd h hmoved
    · exact h
  obtain ⟨q, hqp, hq2, hqp', hqdvd⟩ := exists_prime_dvd_card_ne_two_ne hSsimple hSna p
  have hFs : ∃ Q : Sylow q M, ∀ x ∈ (Q : Subgroup M), σ x = x := hfix q hqp hq2 hqp'
  obtain ⟨Q, hQfix⟩ := hFs
  haveI : Fact q.Prime := ⟨hqp⟩
  obtain ⟨y, hy, hy1⟩ := exists_ne_one_mem_inf_of_dvd_card (Q := Q) hSN hSle hqdvd
  have hyfixed : σ y = y := hQfix y hy.1
  have hymap : y ∈ S.map σ.toMonoidHom := ⟨y, hy.2, hyfixed⟩
  have : y ∈ S.map σ.toMonoidHom ⊓ S := ⟨hymap, hy.2⟩
  rw [hdisj] at this
  exact hy1 (Subgroup.mem_bot.mp this)

theorem isMulCommutative_of_le_fixed {M : Type} [Group M] (σ : MulAut M)
    {N : Subgroup M} [hN : N.Normal] (hfixN : N ≤ σ.toMonoidHom.eqLocus (MonoidHom.id M))
    (hcomm : commSub σ = ⊤) : IsMulCommutative ↥N := by
  have hcentral : (⊤ : Subgroup M) ≤ Subgroup.centralizer (N : Set M) := by
    rw [← hcomm]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨m, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro n hn
    have hconj : σ (m * n * m⁻¹) = m * n * m⁻¹ := hfixN (hN.conj_mem n hn m)
    have hσn : σ n = n := hfixN hn
    have hthis : σ m * n * (σ m)⁻¹ = m * n * m⁻¹ := by
      rw [← hconj]
      simp only [map_mul, map_inv, hσn]
    have key : m⁻¹ * σ m * n = n * m⁻¹ * σ m := by
      calc m⁻¹ * σ m * n = m⁻¹ * (σ m * n * (σ m)⁻¹) * σ m := by group
        _ = m⁻¹ * (m * n * m⁻¹) * σ m := by rw [hthis]
        _ = n * m⁻¹ * σ m := by group
    calc n * (m⁻¹ * σ m) = n * m⁻¹ * σ m := by group
      _ = m⁻¹ * σ m * n := key.symm
      _ = (m⁻¹ * σ m) * n := by group
  have hNcenter : N ≤ Subgroup.center M := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro m
    exact (Subgroup.mem_centralizer_iff.mp
      (hcentral (show m ∈ (⊤ : Subgroup M) from trivial)) n hn).symm
  exact IsMulCommutative.of_comm fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hNcenter a.2) b).symm

theorem exists_restriction_orderOf_three {M : Type*} [Group M] (σ : MulAut M) {S : Subgroup M}
    (hSmap : S.map σ.toMonoidHom = S) (hσ3 : σ ^ 3 = 1) (hσx : ∃ x ∈ S, σ x ≠ x) :
    ∃ σi : MulAut ↥S, orderOf σi = 3 ∧ ∀ y : ↥S, ((σi y : ↥S) : M) = σ (y : M) := by
  obtain ⟨x, hx, hσx⟩ := hσx
  let σi : MulAut ↥S := (MulEquiv.subgroupMap σ S).trans (MulEquiv.subgroupCongr hSmap)
  have hσi_coe : ∀ y : ↥S, ((σi y : ↥S) : M) = σ (y : M) := fun _ => rfl
  have hσi3 : σi ^ 3 = 1 := by
    ext y
    simp only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply, one_mul]
    rw [hσi_coe, hσi_coe, hσi_coe]
    simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply, one_mul] using
      (show (σ ^ 3) (y : M) = y by rw [hσ3]; rfl)
  have hσi_ne : σi ≠ 1 := by
    intro h
    refine hσx ?_
    have hx' : σi ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [h]; rfl
    have := congrArg (fun y : ↥S => (y : M)) hx'
    simpa [hσi_coe] using this
  have horder : orderOf σi = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hσi3 hσi_ne
  exact ⟨σi, horder, hσi_coe⟩

theorem false_of_suzuki_order_three_aut {M : Type} [Group M] [Finite M] (σ : MulAut M)
    {N S : Subgroup M} [N.Normal] (hSN : (S.subgroupOf N).Normal) (hSle : S ≤ N)
    (hSsimple : IsSimpleGroup ↥S) (hSna : ¬ IsMulCommutative ↥S)
    (hKi : CFSG.Open.IsKGroup ↥S) (h3i : ¬ 3 ∣ Nat.card ↥S)
    (hS1 : SimpleThreePrimeIsSz) (hS2 : SzOrder3Aut) (p : ℕ)
    (hfix : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → FixesSylow σ q)
    (σi : MulAut ↥S) (horder : orderOf σi = 3)
    (hσi_coe : ∀ y : ↥S, ((σi y : ↥S) : M) = σ (y : M)) : False := by
  have hnabi : ¬ (∀ a b : ↥S, a * b = b * a) := fun h => hSna (IsMulCommutative.of_comm h)
  obtain ⟨f, hSuz⟩ := hS1 ↥S hSsimple hnabi hKi h3i
  obtain ⟨ℓ₁, ℓ₂, hℓ₁p, hℓ₂p, hℓne, hℓ₁2, hℓ₂2, hℓsyl⟩ := hS2 ↥S f hSuz σi horder
  have key : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ p →
      (∀ P : Subgroup ↥S, IsSylowOf ℓ P ⊤ →
        (IsSylowOf ℓ₁ P ⊤ ∨ IsSylowOf ℓ₂ P ⊤)) → False := by
    intro ℓ hℓp hℓ2 hℓp' hclause
    haveI : Fact ℓ.Prime := ⟨hℓp⟩
    have hFs : ∃ Q : Sylow ℓ M, ∀ x ∈ (Q : Subgroup M), σ x = x := hfix ℓ hℓp hℓ2 hℓp'
    obtain ⟨Q, hQfix⟩ := hFs
    obtain ⟨P, hP⟩ := exists_sylow_map_eq_inf Q hSN hSle
    have hP' : IsSylowOf ℓ (P : Subgroup ↥S) ⊤ := by
      rw [isSylowOf_iff]
      refine ⟨le_top, P.isPGroup', ?_⟩
      rw [Subgroup.relIndex_top_right]
      exact P.not_dvd_index
    obtain ⟨z, hz, hz1⟩ := hℓsyl (P : Subgroup ↥S) (hclause _ hP')
    apply hz1
    apply Subtype.ext
    rw [hσi_coe]
    exact hQfix ((z : ↥S) : M) (by
      have hzmap : ((z : ↥S) : M) ∈ (P : Subgroup ↥S).map S.subtype :=
        Subgroup.mem_map_of_mem S.subtype hz
      rw [hP] at hzmap
      exact hzmap.1)
  by_cases hp1 : ℓ₁ = p
  · have hℓ₂p' : ℓ₂ ≠ p := fun h => hℓne (hp1.trans h.symm)
    exact key ℓ₂ hℓ₂p hℓ₂2 hℓ₂p' fun P hP => Or.inr hP
  · exact key ℓ₁ hℓ₁p hℓ₁2 hp1 fun P hP => Or.inl hP

theorem chiefNon_holds : K22p.ChiefNon := by
  intro hS1 hS2 p M _ _ hK h3 σ hσ hcomm hfix N hN hna
  obtain ⟨r, S, _hr, hSleN, hSnorm, hSsimple, hSna, _hScomm, hSsup⟩ :=
    exists_factors_of_minInv σ hσ hN hna
  haveI : N.Normal := hN.normal
  by_cases hmoved : ∃ i, (S i).map σ.toMonoidHom ≠ S i
  · obtain ⟨i, hi⟩ := hmoved
    exact false_of_moved_simple_factor σ hN.invariant (hSnorm i) (hSleN i) (hSsimple i)
      (hSna i) p hi hfix
  · push Not at hmoved
    by_cases hfixall : ∀ i, ∀ x ∈ S i, σ x = x
    · have hFixN : N ≤ σ.toMonoidHom.eqLocus (MonoidHom.id M) := by
        rw [← hSsup]
        exact iSup_le fun i x hx => hfixall i x hx
      exact hna (isMulCommutative_of_le_fixed σ hFixN hcomm)
    · push Not at hfixall
      obtain ⟨i, x, hx, hσx⟩ := hfixall
      have hKi : CFSG.Open.IsKGroup ↥(S i) := CFSG.Open.IsKGroup.subgroup hK (S i)
      have h3i : ¬ 3 ∣ Nat.card ↥(S i) := fun h =>
        h3 (h.trans (Subgroup.card_subgroup_dvd_card (S i)))
      obtain ⟨σi, horder, hσi_coe⟩ :=
        exists_restriction_orderOf_three σ (hmoved i) hσ ⟨x, hx, hσx⟩
      exact false_of_suzuki_order_three_aut σ (hSnorm i) (hSleN i) (hSsimple i) (hSna i)
        hKi h3i hS1 hS2 p hfix σi horder hσi_coe

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
