module

public import CFSG.RankThree.PartTwo.Sec13.Item135CritProofSteps
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofLin
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofTools
import CFSG.LocalAnalysis.SignalizerFunctor.SurjectiveSylowLifting
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.Res7Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CritProof

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hB h]

omit [Finite G] in
theorem eq_one_of_two_of_odd {S V : Subgroup G} (hS : IsPGroup 2 S) (hV : Odd (Nat.card V))
    {x : G} (hxS : x ∈ S) (hxV : x ∈ V) : x = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨x, hxS⟩
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf x ∣ Nat.card V := by
    rw [← Subgroup.orderOf_mk x hxV]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card V) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hV)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

omit [Finite G] in
theorem eq_of_ne_one_of_card_le_two {H : Type*} [Group H] [Finite H] (hH : Nat.card H ≤ 2)
    {u v : H} (hu : u ≠ 1) (hv : v ≠ 1) : u = v := by
  classical
  by_contra huv
  have : Fintype H := Fintype.ofFinite H
  have h3 : ({1, u, v} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair huv]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hu, Ne.symm hv⟩
  have := Finset.card_le_univ ({1, u, v} : Finset H)
  rw [Nat.card_eq_fintype_card] at hH
  omega

omit [Finite G] in
theorem center_eq_bot_of_simple {T : Type*} [Group T] [IsSimpleGroup T]
    (hab : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hab
    have hb : b ∈ Subgroup.center T := h ▸ Subgroup.mem_top b
    exact hab ((Subgroup.mem_center_iff.mp hb a))

end General

section Crit

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {p : ℕ}
  {C : Subgroup (CFSG.pCore p L)}

theorem dData_of_crit135 [Fact p.Prime] (h : Crit135 L p C) :
    DData p ((omegaOneCore p C).map L.subtype) := by
  have hp := h.prime
  have hcr := h.criticalAt
  refine ⟨(CFSG.pCore_isPGroup.to_le hcr.le).map L.subtype, ?_, ?_, ?_, h.odd_card_centralizer,
    ?_⟩
  · have h3 := h.three_lt
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  · rintro ⟨x, hx⟩
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_subtype, OneMemClass.coe_one]
    rw [← Subgroup.coe_pow, hcr.exp l hl, OneMemClass.coe_one]
  · rw [commutator_def, Subgroup.commutator_le]
    rintro ⟨x, hx⟩ - ⟨y, hy⟩ -
    rw [Subgroup.mem_center_iff]
    rintro ⟨d, hd⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hd
    have := (hcr.comm a ha b (hcr.le hb)).2 e he
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv,
      Subgroup.coe_subtype] at this ⊢
    have h' := congrArg (fun z : L => (z : G)) this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
    exact h'.symm
  · intro t ht
    refine h.pRank_inf_centralizer_le t ?_ ⟨1, ?_⟩
    · rintro rfl
      rw [orderOf_one] at ht
      exact absurd ht (by norm_num)
    · rw [pow_one, ← ht, pow_orderOf_eq_one]

end Crit

theorem false_of_crit {G : Type} [Group G] [Finite G]
    {L K : Subgroup G} {c : G} {p : ℕ} {C : Subgroup (CFSG.pCore p L)} (hcrit : Crit135 L p C)
    {Z : Subgroup L} (hodd : OddCoreAlt7 L Z)
    (hKcrit : Crit135K c L K ((omegaOneCore p C).map L.subtype))
    (hK6 : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) :
    False := by
  classical
  have : Fact p.Prime := ⟨hcrit.prime⟩
  set Dg := (omegaOneCore p C).map L.subtype with hDg
  have hDD : DData p Dg := dData_of_crit135 hcrit
  have hMN : K ⊔ L ≤ Subgroup.normalizer (Dg : Set G) := hKcrit.sup_le_normalizer
  have hKN : K ≤ Subgroup.normalizer (Dg : Set G) := le_sup_left.trans hMN
  have hLN : L ≤ Subgroup.normalizer (Dg : Set G) := le_sup_right.trans hMN
  obtain ⟨-, ⟨eK⟩⟩ := hK6
  set ψK : K →* alternatingGroup (Fin 6) := eK.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K))).comp
      (QuotientGroup.mk' (aschbacherSolvableCore 3 K))) with hψK
  have hψKs : Function.Surjective ψK :=
    eK.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  obtain ⟨eL⟩ := hodd.quotient_center
  set O := CFSG.oddCore L with hOdef
  set Q := L ⧸ O
  set ψL : L →* alternatingGroup (Fin 7) := eL.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center Q)).comp (QuotientGroup.mk' O)) with hψL
  have hψLs : Function.Surjective ψL :=
    eL.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hψL_ker : ∀ x : L, ψL x = 1 ↔ (QuotientGroup.mk' O x : Q) ∈ Subgroup.center Q := by
    intro x
    rw [hψL, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hψL_O : ∀ x : L, x ∈ O → ψL x = 1 := by
    intro x hx
    rw [hψL_ker, show (QuotientGroup.mk' O x : Q) = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _
  set OG := O.map L.subtype with hOG
  have hOGodd : Odd (Nat.card OG) := by
    rw [hOG, Subgroup.card_map_of_injective L.subtype_injective]
    exact CFSG.ABGDGroups.odd_card_oddCore L
  have : O.Characteristic := oddCore_characteristic' L
  have hKO : K ≤ Subgroup.normalizer (OG : Set G) := hKcrit.le_normalizer_left.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic O)
  have hLO : L ≤ Subgroup.normalizer (OG : Set G) := Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic O)
  have hOGL : OG ≤ L := Subgroup.map_subtype_le O
  have hcommKL : ∀ k ∈ K, ∀ l ∈ L, k * l * k⁻¹ * l⁻¹ ∈ OG := by
    intro k hk l hl
    have := hKcrit.commutator_le_oddCore (Subgroup.commutator_mem_commutator hk hl)
    rwa [commutatorElement_def] at this
  have hcommLK : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ * k⁻¹ ∈ OG := by
    intro l hl k hk
    have h1 := Subgroup.commutator_mem_commutator hl hk
    rw [Subgroup.commutator_comm] at h1
    have := hKcrit.commutator_le_oddCore h1
    rwa [commutatorElement_def] at this
  have hmemOG : ∀ x : L, (x : G) ∈ OG ↔ x ∈ O := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rwa [Subtype.ext hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hP2 : ∀ (w : G) (hw : w ∈ L), ψL ⟨w, hw⟩ = 1 → ∀ l ∈ L, w * l * w⁻¹ * l⁻¹ ∈ OG := by
    intro w hw hψw l hl
    rw [hψL_ker] at hψw
    have h1 := Subgroup.mem_center_iff.mp hψw (QuotientGroup.mk' O ⟨l, hl⟩)
    have h2 : (⟨w, hw⟩ * ⟨l, hl⟩ * (⟨w, hw⟩ : L)⁻¹ * (⟨l, hl⟩ : L)⁻¹ : L) ∈ O := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      change QuotientGroup.mk' O ⟨w, hw⟩ * QuotientGroup.mk' O ⟨l, hl⟩ *
        (QuotientGroup.mk' O ⟨w, hw⟩)⁻¹ * (QuotientGroup.mk' O ⟨l, hl⟩)⁻¹ = 1
      rw [← h1]
      group
    exact (hmemOG _).mpr h2
  have hP3 : ∀ {S : Subgroup G}, IsPGroup 2 S → ∀ x y : L, (x : G) ∈ S → (y : G) ∈ S →
      ψL x = 1 → ψL y = 1 → x ≠ 1 → y ≠ 1 → x = y := by
    intro S hS x y hxS hyS hψx hψy hx1 hy1
    rw [hψL_ker] at hψx hψy
    have hne : ∀ z : L, (z : G) ∈ S → z ≠ 1 → (QuotientGroup.mk' O z : Q) ≠ 1 := by
      intro z hzS hz1 h1
      have h2 : z ∈ O := (QuotientGroup.eq_one_iff _).mp h1
      exact hz1 (Subtype.ext (eq_one_of_two_of_odd hS hOGodd hzS ((hmemOG z).mpr h2)))
    have heq := eq_of_ne_one_of_card_le_two hodd.card_center_le
      (u := ⟨_, hψx⟩) (v := ⟨_, hψy⟩)
      (fun h => hne x hxS hx1 (congrArg Subtype.val h))
      (fun h => hne y hyS hy1 (congrArg Subtype.val h))
    have h1 := congrArg Subtype.val heq
    simp only at h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have h2 : ((x⁻¹ * y : L) : G) ∈ OG := (hmemOG _).mpr h1
    have h3 := eq_one_of_two_of_odd hS hOGodd
      (show ((x⁻¹ * y : L) : G) ∈ S from by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact mul_mem (inv_mem hxS) hyS) h2
    have h4 : x⁻¹ * y = 1 := Subtype.ext h3
    rw [inv_mul_eq_one] at h4
    exact h4
  have hQ1 : ∀ v : K, (v : G) ∈ OG → ψK v = 1 := by
    have hNn : (OG.subgroupOf K).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hKO g.2) n).mp hn⟩
    have hNodd : Odd (Nat.card (OG.subgroupOf K)) := by
      have h1 : Nat.card ((OG.subgroupOf K).map K.subtype) = Nat.card (OG.subgroupOf K) :=
        Subgroup.card_map_of_injective K.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype] at h1
      rw [← h1]
      exact hOGodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hbot := altTarget_six.map_eq_bot_of_odd ψK hψKs hNn hNodd
    intro v hv
    have : ψK v ∈ (OG.subgroupOf K).map ψK := ⟨v, hv, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have hQ2 : ∀ (w : G) (hwK : w ∈ K), w ∈ L → ψK ⟨w, hwK⟩ = 1 := by
    intro w hwK hwL
    have hc : ψK ⟨w, hwK⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro t
      obtain ⟨k, rfl⟩ := hψKs t
      have h1 : w * k * w⁻¹ * k⁻¹ ∈ OG := hcommLK w hwL k k.2
      have h2 : w * k * w⁻¹ * k⁻¹ ∈ K := mul_mem (mul_mem (mul_mem hwK k.2) (inv_mem hwK))
        (inv_mem k.2)
      have h3 := hQ1 ⟨_, h2⟩ h1
      have h4 : (⟨w * k * w⁻¹ * k⁻¹, h2⟩ : K) = ⟨w, hwK⟩ * k * ⟨w, hwK⟩⁻¹ * k⁻¹ := rfl
      rw [h4, map_mul, map_mul, map_mul, map_inv, map_inv] at h3
      calc ψK k * ψK ⟨w, hwK⟩ = ψK ⟨w, hwK⟩ * ψK k * (ψK ⟨w, hwK⟩)⁻¹ * (ψK k)⁻¹ *
            (ψK k * ψK ⟨w, hwK⟩) := by rw [h3, one_mul]
        _ = ψK ⟨w, hwK⟩ * ψK k := by group
    have := altTarget_six.simple
    rw [center_eq_bot_of_simple altTarget_six.exists_ne_comm] at hc
    exact hc
  have hfixK : ∀ {U : Subgroup G}, IsPGroup 2 U → U ≤ L → ∀ k : K, ∃ k' : K,
      (k' : G) ∈ Subgroup.centralizer (U : Set G) ∧ ψK k' = ψK k := by
    intro U hU hUL k
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hV2 : ¬ 2 ∣ Nat.card (K ⊓ OG : Subgroup G) := by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr (hOGodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
    obtain ⟨v, hv, hfix⟩ := PartOne.Sec159.exists_fixed_in_coset hU hV2
      (fun u hu => mem_normalizer_inf (hKcrit.le_normalizer_right (hUL hu)) (hLO (hUL hu)))
      (mem_normalizer_inf (Subgroup.le_normalizer k.2) (hKO k.2))
      (fun u hu => by
        refine Subgroup.mem_inf.mpr ⟨?_, hcommLK u (hUL hu) k k.2⟩
        have h1 : u * k * u⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hKcrit.le_normalizer_right (hUL hu)) k).mp k.2
        exact mul_mem h1 (inv_mem k.2))
    have hvK : v ∈ K := (Subgroup.mem_inf.mp hv).1
    refine ⟨⟨k * v, mul_mem k.2 hvK⟩, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := hfix u hu
      calc u * ((k : G) * v) = u * ((k : G) * v) * u⁻¹ * u := by group
        _ = (k : G) * v * u := by rw [this]
    · have h1 : (⟨(k : G) * v, mul_mem k.2 hvK⟩ : K) = k * ⟨v, hvK⟩ := rfl
      rw [h1, map_mul, hQ1 ⟨v, hvK⟩ (Subgroup.mem_inf.mp hv).2, mul_one]
  have hYK : ∀ {U : Subgroup G}, IsPGroup 2 U → U ≤ L →
      Function.Surjective (ψK.comp (Subgroup.inclusion
        (inf_le_left : K ⊓ Subgroup.centralizer (U : Set G) ≤ K))) := by
    intro U hU hUL t
    obtain ⟨k, rfl⟩ := hψKs t
    obtain ⟨k', hk'U, hk'⟩ := hfixK hU hUL k
    exact ⟨⟨k', Subgroup.mem_inf.mpr ⟨k'.2, hk'U⟩⟩, hk'⟩
  set P := kleinA7.comap ψL with hP
  set ψP : P →* kleinA7 := (ψL.comp P.subtype).codRestrict kleinA7 (fun x => x.2) with hψP
  have hψPs : Function.Surjective ψP := by
    rintro ⟨e, he⟩
    obtain ⟨l, hl⟩ := hψLs e
    exact ⟨⟨l, by rw [hP, Subgroup.mem_comap, hl]; exact he⟩, Subtype.ext hl⟩
  obtain ⟨SP, hSP⟩ := CFSG.SignalizerFunctor.Helpers.surjective_pgroup_sylow_lift 2
    Nat.prime_two ψP hψPs isPGroup_kleinA7
  set SL := (SP : Subgroup P).map P.subtype with hSL
  set S := SL.map L.subtype with hS
  have hS2 : IsPGroup 2 S := (SP.isPGroup'.map P.subtype).map L.subtype
  have hSL' : S ≤ L := Subgroup.map_subtype_le SL
  have hlift : ∀ e : alternatingGroup (Fin 7), e ∈ kleinA7 → ∃ x : L, (x : G) ∈ S ∧
      ψL x = e := by
    intro e he
    have h1 : (⟨e, he⟩ : kleinA7) ∈ (SP : Subgroup P).map ψP := hSP ▸ Subgroup.mem_top _
    obtain ⟨s, hs, hse⟩ := h1
    exact ⟨(s : L), ⟨(s : L), ⟨s, hs, rfl⟩, rfl⟩, congrArg Subtype.val hse⟩
  obtain ⟨i, hiS, hψi⟩ := hlift a7a (Subgroup.subset_closure (Set.mem_insert _ _))
  obtain ⟨j, hjS, hψj⟩ := hlift a7b
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hSN : ∀ x ∈ S, x ∈ Subgroup.normalizer (Dg : Set G) := fun x hx => hLN (hSL' hx)
  have hSmem : ∀ x : L, (x : G) ∈ S → ∀ y : L, (y : G) ∈ S → ((x * y : L) : G) ∈ S :=
    fun x hx y hy => by rw [Subgroup.coe_mul]; exact mul_mem hx hy
  have hSinv : ∀ x : L, (x : G) ∈ S → ((x⁻¹ : L) : G) ∈ S :=
    fun x hx => by rw [Subgroup.coe_inv]; exact inv_mem hx
  have hcoe1 : ∀ x : L, x ≠ 1 → (x : G) ≠ 1 := fun x hx h => hx (Subtype.ext h)
  have hcoe_ne : ∀ x y : L, x ≠ y → (x : G) ≠ y := fun x y hxy h => hxy (Subtype.ext h)
  by_cases hA : ∃ f₁ ∈ S, ∃ f₂ ∈ S, orderOf f₁ = 2 ∧ orderOf f₂ = 2 ∧ f₁ ≠ f₂ ∧
      f₁ * f₂ = f₂ * f₁
  · obtain ⟨f₁, hf₁, f₂, hf₂, ho₁, ho₂, hne, hc⟩ := hA
    have hYN : K ⊓ Subgroup.centralizer (S : Set G) ≤ Subgroup.normalizer (Dg : Set G) :=
      inf_le_left.trans hKN
    have hYc : ∀ f ∈ S, ∀ y ∈ K ⊓ Subgroup.centralizer (S : Set G), y * f = f * y := by
      intro f hf y hy
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 f hf).symm
    exact false_of_four_group hDD (hSN f₁ hf₁) (hSN f₂ hf₂) ho₁ ho₂ hne hc hYN
      (hYc f₁ hf₁) (hYc f₂ hf₂) altTarget_six _ (hYK hS2 hSL')
  push Not at hA
  have hord2 : ∀ x : L, x * x = 1 → x ≠ 1 → orderOf (x : G) = 2 := fun x hx hx1 => by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq, hx]) hx1
  have hAL : ∀ x : L, (x : G) ∈ S → ∀ y : L, (y : G) ∈ S → x * x = 1 → y * y = 1 → x ≠ 1 →
      y ≠ 1 → x ≠ y → x * y = y * x → False := by
    intro x hxS y hyS hx hy hx1 hy1 hxy hc
    exact hA x hxS y hyS (hord2 x hx hx1) (hord2 y hy hy1) (hcoe_ne x y hxy)
      (by rw [← Subgroup.coe_mul, hc, Subgroup.coe_mul])
  obtain ⟨w, hwS, hψw, hw1⟩ : ∃ w : L, (w : G) ∈ S ∧ ψL w = 1 ∧ w ≠ 1 := by
    by_contra hno
    push Not at hno
    have hi1 : i ≠ 1 := by
      rintro rfl
      exact a7a_ne_one (hψi ▸ map_one ψL)
    have hj1 : j ≠ 1 := by
      rintro rfl
      exact a7b_ne_one (hψj ▸ map_one ψL)
    have hi2 : i * i = 1 := hno _ (hSmem i hiS i hiS) (by rw [map_mul, hψi, a7a_sq])
    have hj2 : j * j = 1 := hno _ (hSmem j hjS j hjS) (by rw [map_mul, hψj, a7b_sq])
    have hij : i * j * i⁻¹ * j⁻¹ = 1 := hno _
      (hSmem _ (hSmem _ (hSmem i hiS j hjS) _ (hSinv i hiS)) _ (hSinv j hjS))
      (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hψi, hψj, a7ab_comm]; group)
    have hne : i ≠ j := by
      rintro rfl
      exact a7a_ne_a7b (hψi.symm.trans hψj)
    have hc : i * j = j * i := by
      calc i * j = i * j * i⁻¹ * j⁻¹ * (j * i) := by group
        _ = j * i := by rw [hij, one_mul]
    exact hAL i hiS j hjS hi2 hj2 hi1 hj1 hne hc
  have huniq : ∀ x : L, (x : G) ∈ S → ψL x = 1 → x ≠ 1 → x = w :=
    fun x hxS hψx hx1 => hP3 hS2 x w hxS hwS hψx hψw hx1 hw1
  have hw2 : w * w = 1 := by
    by_contra hww
    have := huniq _ (hSmem w hwS w hwS) (by rw [map_mul, hψw, mul_one]) hww
    apply hw1
    calc w = w * w * w⁻¹ := by group
      _ = 1 := by rw [this, mul_inv_cancel]
  have hwo : orderOf (w : G) = 2 := hord2 w hw2 hw1
  have hwc : ∀ s : L, (s : G) ∈ S → s * w = w * s := by
    intro s hs
    have h1 : s * w * s⁻¹ = w := by
      refine huniq _ (hSmem _ (hSmem s hs w hwS) _ (hSinv s hs)) ?_ ?_
      · rw [map_mul, map_mul, map_inv, hψw, mul_one, mul_inv_cancel]
      · intro h
        apply hw1
        calc w = s⁻¹ * (s * w * s⁻¹) * s := by group
          _ = 1 := by rw [h]; group
    calc s * w = s * w * s⁻¹ * s := by group
      _ = w * s := by rw [h1]
  have hsq : ∀ x : L, (x : G) ∈ S → ψL x ≠ 1 → ψL x * ψL x = 1 → x * x = w := by
    intro x hxS hψx hψx2
    by_cases hxx : x * x = 1
    · exfalso
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hψx (map_one ψL)
      have hxw : x ≠ w := by
        rintro rfl
        exact hψx hψw
      exact hAL x hxS w hwS hxx hw2 hx1 hw1 hxw (hwc x hxS)
    · exact huniq _ (hSmem x hxS x hxS) (by rw [map_mul, hψx2]) hxx
  have hii : i * i = w := hsq i hiS (by rw [hψi]; exact a7a_ne_one) (by rw [hψi, a7a_sq])
  have hjj : j * j = w := hsq j hjS (by rw [hψj]; exact a7b_ne_one) (by rw [hψj, a7b_sq])
  have hijij : i * j * (i * j) = w := hsq (i * j) (hSmem i hiS j hjS)
    (by rw [map_mul, hψi, hψj]; exact a7ab_ne_one) (by rw [map_mul, hψi, hψj, a7ab_sq])
  have hinv : ∀ x : L, x * x = w → x⁻¹ = x * w := by
    intro x hx
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, hx, hw2]
  have hij : i * j = w * (j * i) := by
    have h1 : i * j = w * (i * j)⁻¹ := by
      rw [← hijij]
      group
    rw [h1, mul_inv_rev, hinv j hjj, hinv i hii]
    have hiw : i * w = w * i := hwc i hiS
    rw [hiw, show j * w * (w * i) = j * (w * w) * i by group, hw2, mul_one]
  set Y := K ⊓ Subgroup.centralizer (S : Set G) with hYdef
  set ψY := ψK.comp (Subgroup.inclusion (inf_le_left : Y ≤ K)) with hψY
  have hψYs : Function.Surjective ψY := hYK hS2 hSL'
  obtain ⟨y', hy'⟩ := hψYs a6a
  obtain ⟨y, -, hy2, hψy⟩ := exists_two_part ψY a6a_sq y' hy'
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact a6a_ne_one (hψy ▸ map_one ψY)
  obtain ⟨s, hs⟩ := exists_orderOf_eq_two_pow_succ hy2 hy1
  have hy₀ := orderOf_two_pow_pred hs
  set y₀ : Y := y ^ 2 ^ s with hy₀def
  have hYcS : ∀ x : Y, ∀ f ∈ S, (x : G) * f = f * x := fun x f hf =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp x.2).2 f hf).symm
  have hYK' : ∀ x : Y, (x : G) ∈ K := fun x => (Subgroup.mem_inf.mp x.2).1
  have hy₀o : orderOf (y₀ : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy₀
  have hy₀2 : (y₀ : G) * y₀ = 1 := mul_self_eq_one_of_orderOf hy₀o
  have hw2G : (w : G) * w = 1 := by rw [← Subgroup.coe_mul, hw2, OneMemClass.coe_one]
  by_cases hB1 : (y₀ : G) ≠ w
  ·
    set Y' := L ⊓ Subgroup.centralizer ({(y₀ : G)} : Set G) ⊓
      Subgroup.centralizer ({(w : G)} : Set G) with hY'
    have hY'L : Y' ≤ L := inf_le_left.trans inf_le_left
    set ψY' := ψL.comp (Subgroup.inclusion hY'L) with hψY'
    have hψY's : Function.Surjective ψY' := by
      intro t
      obtain ⟨l, rfl⟩ := hψLs t
      obtain ⟨v, hv, h₁, h₂⟩ := exists_fixed_two_involutions hOGodd hy₀2 hw2G
        (hYcS y₀ w hwS) (hKO (hYK' y₀)) (hLO w.2) (hLO l.2)
        (hcommKL _ (hYK' y₀) l l.2) (hP2 w w.2 hψw l l.2)
      have hvL : v ∈ L := hOGL hv
      have hmem : (l : G) * v ∈ Y' := Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
        ⟨mul_mem l.2 hvL, Subgroup.mem_centralizer_singleton_iff.mpr h₁⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr h₂⟩
      refine ⟨⟨(l : G) * v, hmem⟩, ?_⟩
      have h3 : Subgroup.inclusion hY'L ⟨(l : G) * v, hmem⟩ = l * ⟨v, hvL⟩ := rfl
      rw [MonoidHom.comp_apply, h3, map_mul, hψL_O ⟨v, hvL⟩ ((hmemOG ⟨v, hvL⟩).mp hv),
        mul_one]
    have hY'N : Y' ≤ Subgroup.normalizer (Dg : Set G) := hY'L.trans hLN
    exact false_of_four_group hDD (hKN (hYK' y₀)) (hLN w.2) hy₀o hwo hB1 (hYcS y₀ w hwS) hY'N
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2)
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2)
      altTarget_seven ψY' hψY's
  push Not at hB1
  have hwK : (w : G) ∈ K := hB1 ▸ hYK' y₀
  have hψKw : ψK ⟨w, hwK⟩ = 1 := hQ2 w hwK w.2
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := by
    rcases s with _ | s'
    · exfalso
      apply a6a_ne_one
      rw [← hψy]
      have h1 : y₀ = y := by rw [hy₀def, pow_zero, pow_one]
      have h2 : (y : G) = w := by rw [← h1]; exact hB1
      have h3 : ψY y = ψK ⟨w, hwK⟩ := by
        rw [hψY, MonoidHom.comp_apply]
        congr 1
        exact Subtype.ext h2
      rw [h3, hψKw]
    · exact ⟨s', rfl⟩
  set i₀ : Y := y ^ 2 ^ s' with hi₀def
  have hi₀2 : (i₀ : G) * i₀ = w := by
    rw [← hB1, hy₀def, hi₀def, ← Subgroup.coe_mul, ← sq, ← pow_mul, ← pow_succ]
  set iG : G := (i : G) with hiG
  set jG : G := (j : G) with hjG
  set wG : G := (w : G) with hwG
  have hiiG : iG * iG = wG := by rw [hiG, hwG, ← Subgroup.coe_mul, hii]
  have hjjG : jG * jG = wG := by rw [hjG, hwG, ← Subgroup.coe_mul, hjj]
  have hijG : iG * jG = wG * (jG * iG) := by
    rw [hiG, hjG, hwG, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hij]
  have hi₀i : (i₀ : G) * iG = iG * i₀ := hYcS i₀ iG hiS
  have hi₀j : (i₀ : G) * jG = jG * i₀ := hYcS i₀ jG hjS
  have hw1G : wG ≠ 1 := hcoe1 w hw1
  have hijne : iG * jG ≠ jG * iG := by
    intro h
    rw [h] at hijG
    apply hw1G
    calc wG = wG * (jG * iG) * (jG * iG)⁻¹ := by group
      _ = 1 := by rw [← hijG, mul_inv_cancel]
  set e := (i₀ : G) * iG with he
  have he2 : e * e = 1 := by
    calc e * e = (i₀ : G) * (iG * i₀) * iG := by rw [he]; group
      _ = (i₀ : G) * (i₀ * iG) * iG := by rw [← hi₀i]
      _ = ((i₀ : G) * i₀) * (iG * iG) := by group
      _ = 1 := by rw [hi₀2, hiiG, hw2G]
  have hene : e ≠ wG := by
    intro h
    apply hijne
    have hi : (i₀ : G) = iG := by
      calc (i₀ : G) = e * iG⁻¹ := by rw [he]; group
        _ = iG * iG * iG⁻¹ := by rw [h, hiiG]
        _ = iG := by group
    rw [← hi]
    exact hi₀j
  have he1 : e ≠ 1 := by
    intro h
    apply hijne
    have hi : (i₀ : G) = iG⁻¹ := by
      calc (i₀ : G) = e * iG⁻¹ := by rw [he]; group
        _ = iG⁻¹ := by rw [h, one_mul]
    have h1 : iG⁻¹ * jG = jG * iG⁻¹ := hi ▸ hi₀j
    calc iG * jG = iG * (iG⁻¹ * jG) * iG := by rw [h1]; group
      _ = jG * iG := by group
  have heo : orderOf e = 2 := orderOf_eq_prime (by rw [sq, he2]) he1
  have hew : e * wG = wG * e := by
    have hiw : iG * wG = wG * iG := by
      rw [hiG, hwG, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hwc i hiS]
    have hi₀w : (i₀ : G) * wG = wG * i₀ := hYcS i₀ wG hwS
    rw [he, mul_assoc, hiw, ← mul_assoc, hi₀w, mul_assoc]
  have hYN : Y ≤ Subgroup.normalizer (Dg : Set G) := inf_le_left.trans hKN
  have heN : e ∈ Subgroup.normalizer (Dg : Set G) :=
    mul_mem (hKN (hYK' i₀)) (hLN i.2)
  exact false_of_quaternion hDD (hLN w.2) (hLN i.2) (hLN j.2) heN hwo hiiG hjjG hijG heo hew
    hene hYN
    (fun x hx => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 iG hiS).symm)
    (fun x hx => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 jG hjS).symm)
    altTarget_six ψY hψYs

end CFSG.RankThree.PartTwo.Sec13.Res7Proof

namespace CFSG.RankThree.PartTwo.Sec13

theorem item135A7Z3HypTKCrit_holds : Item135A7Z3HypTKCrit := by
  intro G _ _ A c L hD hT hcL hnq hO2 hm hO hA7 hHeis K hK hAK hK6 p C hcrit hodd hKcrit
  exact Res7Proof.false_of_crit hcrit hodd hKcrit hK6

theorem item135A7Z3HypTK_holds :
    Item135A7Z3HypTK :=
  item135A7Z3HypTK_of_crit item135A7Z3HypTKCrit_holds

end CFSG.RankThree.PartTwo.Sec13
