module

public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofTTools
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofTLin
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofX
import CFSG.StronglyEmbedded.Catalog
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item152StepsConf

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Step152ConfTPerm (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (p : ℕ) (P : Subgroup G),
    Pt152 A LB Y M X c' L' → PData152 A X p P →
      ∃ T ∈ scriptQPiStar A LB X (piOf 2), ¬ T ≤ inSubgroup (aschbacherSolvableCore 3) X ∧
        ((T ⊔ P : Subgroup G) : Set G) = (T : Set G) * (P : Set G)

@[expose] noncomputable def Step152ConfTPermR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfTPerm A (lB A)

namespace Proof152ConfA

theorem exists_two_subgroup_not_le_theta
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y M X : Subgroup G}
    (hctx : Ctx152 A LB Y M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A) :
    ∃ T₀ ∈ scriptQPi A LB X (piOf 2), ¬ T₀ ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXs, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five hX60
  obtain ⟨x, hxA, hxX, hx3, -, hxθ⟩ := exists_mem_inf_not_mem_theta hctx hAF hA
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  set π := QuotientGroup.mk' θ with hπ
  have hmemθ : ∀ y : ↥X, π y = 1 → (y : G) ∈ θX := fun y hy =>
    ⟨y, (QuotientGroup.eq_one_iff y).mp hy, rfl⟩
  have hXθ : ¬ X ≤ θX := by
    intro h
    have hsub : Subsingleton (↥X ⧸ θ) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective θ a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective θ b
      have ha : π a = 1 := by
        obtain ⟨t, ht, hta⟩ := h a.2
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          show a = t from Subtype.ext hta.symm]
        exact ht
      have hb : π b = 1 := by
        obtain ⟨t, ht, htb⟩ := h b.2
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          show b = t from Subtype.ext htb.symm]
        exact ht
      rw [ha, hb]
    have := Nat.card_unique (α := ↥X ⧸ θ)
    rw [hX60] at this
    norm_num at this
  obtain ⟨Q, hQ, hQθ⟩ : ∃ Q ∈ collectionIn (scriptQ A LB) X, ¬ Q ≤ θX := by
    by_contra h
    push Not at h
    exact hXθ (hctx.delta_x.le.trans (sSup_le h))
  have hQX : Q ≤ X := hQ.2
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ.1.1.2.2
  obtain ⟨S, hS⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime 3 2
    hA.isPGroup hQ3 (Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ))
  set T₀ := (S : Subgroup Q).map Q.subtype with hT₀
  have hT₀Q : T₀ ≤ Q := Subgroup.map_subtype_le _
  have hAT₀ : A ≤ Subgroup.normalizer (T₀ : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    conv_rhs => rw [hT₀, ← hS ⟨a, ha⟩]
    rw [hT₀, Subgroup.map_map, Subgroup.map_map]
    rfl
  refine ⟨T₀, ⟨⟨mem_scriptQ_of_le hQ.1 hT₀Q hAT₀, hT₀Q.trans hQX⟩,
    (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (S.isPGroup'.map _)⟩, fun hT₀θ => ?_⟩
  set f : Q →* ↥X ⧸ θ := π.comp (Subgroup.inclusion hQX) with hf
  have hfS : (S : Subgroup Q).map f.rangeRestrict = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    obtain ⟨t, ht, hts⟩ := hT₀θ ⟨s, hs, rfl⟩
    change π (Subgroup.inclusion hQX s) = 1
    rw [show Subgroup.inclusion hQX s = t from Subtype.ext hts.symm, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ht
  have h2 : ¬ 2 ∣ Nat.card f.range := by
    intro h2
    set S' := S.mapSurjective f.rangeRestrict_surjective with hS'
    have hc := Sylow.card_eq_multiplicity S'
    rw [Sylow.coe_mapSurjective, hfS, Subgroup.card_bot] at hc
    have h0 : (Nat.card f.range).factorization 2 = 0 := by
      have := Nat.pow_right_injective (le_refl 2) (hc.symm.trans (pow_zero 2).symm)
      exact this
    exact (Nat.factorization_eq_zero_iff _ _).mp h0 |>.elim (fun h => h Nat.prime_two)
      (fun h => h.elim (fun h => h h2) (fun h => Nat.card_pos.ne' h))
  have h3 : ¬ 3 ∣ Nat.card f.range := fun h3 => hQ3 (h3.trans (by
    rw [MonoidHom.range_eq_map]
    exact (Subgroup.card_map_dvd _ _).trans (by rw [Subgroup.card_top])))
  have h60 : Nat.card f.range ∣ 60 := by
    rw [← hX60]
    exact Subgroup.card_subgroup_dvd_card _
  have h5 : Nat.card f.range ∣ 5 := by
    have hc2 : Nat.Coprime (Nat.card f.range) 4 :=
      Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
    have hc3 : Nat.Coprime (Nat.card f.range) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
    have h1 : Nat.card f.range ∣ 4 * 15 := by simpa using h60
    have h1' := hc2.dvd_of_dvd_mul_left h1
    have h1'' : Nat.card f.range ∣ 3 * 5 := by simpa using h1'
    exact hc3.dvd_of_dvd_mul_left h1''
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h5 with h1 | h5'
  ·
    apply hQθ
    intro q hq
    have hmem : f ⟨q, hq⟩ ∈ f.range := ⟨⟨q, hq⟩, rfl⟩
    rw [Subgroup.eq_bot_of_card_eq _ h1, Subgroup.mem_bot] at hmem
    exact hmemθ _ hmem
  ·
    have : Nontrivial f.range := by
      rw [← Finite.one_lt_card_iff_nontrivial, h5']
      norm_num
    obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : f.range)
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hyo : orderOf y = 5 := by
      have h := orderOf_dvd_natCard (⟨y, hy⟩ : f.range)
      rw [h5', Subgroup.orderOf_mk] at h
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hy1'
      · exact h
    have hy5 : y ^ 5 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
    have hrange : f.range = Subgroup.zpowers y := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy) ?_).symm
      rw [Nat.card_zpowers, hyo, h5']
    have hx1 : π ⟨x, hxX⟩ ≠ 1 := fun h => hxθ (hmemθ _ h)
    have hx3' : (π ⟨x, hxX⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxX⟩ : ↥X) ^ 3 = 1 := Subtype.ext hx3
      rw [this, map_one]
    apply not_normalizes_five_of_mulEquiv e hx1 hx3' hy1' hy5
    rw [← hrange]
    obtain ⟨q, rfl⟩ := hy
    have hxq : x * (q : G) * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hAQ hxA) q).mp q.2
    refine ⟨⟨_, hxq⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul, ← map_inv, ← map_mul]
    rfl

theorem step152ConfT_of
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} (hAF : A ∈ partTwoF G)
    (hA : Late.IsE27 A) (hperm : Step152ConfTPerm A LB) : Step152ConfT A LB := by
  intro Y M X c' L' p P hpt hPd
  have hctx := hpt.ctx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hPd.prime⟩
  obtain ⟨hXs, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five hX60
  obtain ⟨x, hxA, hxX, hx3, -, hxθ⟩ := exists_mem_inf_not_mem_theta hctx hAF hA
  obtain ⟨T, hT, hTθ, hTP⟩ := hperm Y M X c' L' p P hpt hPd
  refine ⟨T, ⟨hT, hTP, ?_⟩⟩
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  set π := QuotientGroup.mk' θ with hπ
  have hTX : T ≤ X := hT.prop.1.2
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop
  have hPp : IsPGroup p P := by
    rcases hPd.type_p with ⟨-, h⟩ | ⟨-, h⟩
    · exact IsPGroup.of_card h
    · exact IsPGroup.of_card h
  obtain ⟨R, hR, hPR, -⟩ := hPd.char_p
  have hPθ : P ≤ θX := le_theta_of_le_sylow hPd.odd hXs hX60 hR hPR
  obtain ⟨t, htT, htθ⟩ := Set.not_subset.mp hTθ
  obtain ⟨n, ⟨hnT, hnN⟩, hnθ⟩ :=
    exists_mem_normalizer_not_mem_theta hPd.odd hTX hT2 hPp hPθ hTP htT htθ
  have hnX : n ∈ X := hTX hnT
  have huX : ⁅n, x⁆ ∈ X := by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem hnX hxX) (X.inv_mem hnX)) (X.inv_mem hxX)
  have huθ : ⁅n, x⁆ ∉ θX := by
    intro hu
    apply hnθ
    have hu' : π ⁅(⟨n, hnX⟩ : ↥X), ⟨x, hxX⟩⁆ = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨w, hw, hwu⟩ := hu
      have hwu' : (w : G) = ⁅n, x⁆ := hwu
      have : (⁅(⟨n, hnX⟩ : ↥X), ⟨x, hxX⟩⁆ : ↥X) = w := by
        apply Subtype.ext
        rw [hwu']
        simp [commutatorElement_def]
      rw [this]
      exact hw
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hu'
    have hx1 : π ⟨x, hxX⟩ ≠ 1 := fun h => hxθ ⟨_, (QuotientGroup.eq_one_iff _).mp h, rfl⟩
    have hx3' : (π ⟨x, hxX⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxX⟩ : ↥X) ^ 3 = 1 := Subtype.ext hx3
      rw [this, map_one]
    have hn3 : (π ⟨n, hnX⟩) ^ 3 = 1 := pow_three_of_commute_of_mulEquiv e hx1 hx3' hu'
    obtain ⟨k, hk⟩ := hT2 ⟨n, hnT⟩
    have hnk : (π ⟨n, hnX⟩) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨n, hnX⟩ : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hnk) (orderOf_dvd_of_pow_eq_one hn3)
    rw [(Nat.coprime_pow_primes k 1 Nat.prime_two Nat.prime_three (by norm_num) |>.pow_right
      1 |> fun h => by simpa using h : Nat.Coprime (2 ^ k) 3).gcd_eq_one, Nat.dvd_one,
      orderOf_eq_one_iff] at h1
    exact ⟨_, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
  have hAN : A ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) :
      Set G) :=
    Late.le_normalizer_inf hT.prop.1.1.1.2.2
      (hPd.norm_p.trans (Sec6.normalizer_le_normalizer_normalizer P))
  have hUle : ⁅T ⊓ Subgroup.normalizer (P : Set G), A⁆ ≤ T ⊓ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hAN
  have hU2 : IsPGroup 2 ↥(⁅T ⊓ Subgroup.normalizer (P : Set G), A⁆ : Subgroup G) :=
    hT2.to_le (hUle.trans inf_le_left)
  have hUC : ¬ ⁅T ⊓ Subgroup.normalizer (P : Set G), A⁆ ≤ Subgroup.centralizer (P : Set G) := by
    intro h
    exact huθ (oTwoOddIn_le_theta hXs hX60
      (hPd.cent_p ⟨huX, h (Subgroup.commutator_mem_commutator ⟨hnT, hnN⟩ hxA)⟩))
  exact eq_commutator_of_isPGroup_two hPd.odd hPp (card_frattini_quotient_eq hPd.type_p)
    inf_le_right hPd.norm_p hU2 hUC

end Proof152ConfA

theorem step152ConfTR_of
    (hperm : Step152ConfTPermR) : Step152ConfTR :=
  fun G _ _ A c L hR => Proof152ConfA.step152ConfT_of hR.toSec13Data.mem_partTwoF
    (Late.isE27_of_mem_partTwoE hR.toSec13Data.mem_partTwoE) (hperm G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
