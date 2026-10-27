module

public import CFSG.RankThree.PartTwo.Sec11.Statements
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type*} [Group G] [Finite G]

theorem exists_invariantPiSubgroups_of_invTwoBarNontrivial {E L : Subgroup G}
    (hE : IsPGroup 3 E) (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (h : Sec8.InvTwoBarNontrivial E L) :
    ∃ U ∈ invariantPiSubgroups L E (piOf 2), U ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨X, hX1, hX2, hXinv⟩ := h
  set θL := aschbacherSolvableCore 3 L
  let Y' : Subgroup L := X.comap (QuotientGroup.mk' θL)
  let Y : Subgroup G := Y'.map L.subtype
  have hYL : Y ≤ L := Subgroup.map_subtype_le _
  have hconj : ∀ e ∈ E, ∀ y ∈ Y, e * y * e⁻¹ ∈ Y := by
    rintro e he _ ⟨y, hy, rfl⟩
    have heN := hEL he
    have hτ : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, heN⟩) ∈ Sec4.autThetaQuot E L :=
      Sec4.mem_autThetaQuot_iff.mpr ⟨e, heN, he, rfl⟩
    have h1 := hXinv _ hτ _ hy
    rw [QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk] at h1
    exact ⟨_, h1, rfl⟩
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) := fun e he => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconj e he y, fun hy => ?_⟩
    have := hconj e⁻¹ (E.inv_mem he) _ hy
    simpa [mul_assoc] using this
  have h3Y : ¬ 3 ∣ Nat.card Y := by
    intro h3
    obtain ⟨⟨y, hy⟩, hy3⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have e1 : orderOf y = 3 := (Subgroup.orderOf_coe (⟨y, hy⟩ : Y)).trans hy3
    obtain ⟨y', hy', rfl⟩ := hy
    have hord : orderOf y' = 3 := (Subgroup.orderOf_coe y').symm.trans e1
    have hθ : y' ∈ θL := by
      have hbar : orderOf (QuotientGroup.mk' θL y') ∣ orderOf y' := orderOf_map_dvd _ _
      rw [hord] at hbar
      obtain ⟨k, hk⟩ := hX2 ⟨_, hy'⟩
      have h2 : orderOf (QuotientGroup.mk' θL y') ∣ 2 ^ k := by
        rw [← Subgroup.orderOf_mk (QuotientGroup.mk' θL y') hy']
        exact orderOf_dvd_of_pow_eq_one hk
      have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
      have hg := Nat.dvd_gcd hbar h2
      rw [hcop] at hg
      have h1 : orderOf (QuotientGroup.mk' θL y') = 1 := Nat.eq_one_of_dvd_one hg
      rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have h3θ := (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
    have hdvd : orderOf (⟨y', hθ⟩ : θL) ∣ Nat.card θL := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord] at hdvd
    exact h3θ hdvd
  have h2Y : 2 ∣ Nat.card Y := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
    obtain ⟨k, hk⟩ := hX2 ⟨x, hx⟩
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective θL x
    have hx1' : QuotientGroup.mk' θL y' ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    have hdvd : orderOf (QuotientGroup.mk' θL y') ∣ orderOf y' := orderOf_map_dvd _ _
    have h2 : 2 ∣ orderOf (QuotientGroup.mk' θL y') := by
      have h' : orderOf (QuotientGroup.mk' θL y') ∣ 2 ^ k := by
        rw [← Subgroup.orderOf_mk (QuotientGroup.mk' θL y') hx]
        exact orderOf_dvd_of_pow_eq_one hk
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h'
      rcases j with _ | j
      · exact absurd (orderOf_eq_one_iff.mp (by simpa using hj')) hx1'
      · rw [hj']
        exact dvd_pow_self 2 (Nat.succ_ne_zero j)
    have hyY : (y' : G) ∈ Y := ⟨y', hx, rfl⟩
    calc 2 ∣ orderOf y' := h2.trans hdvd
      _ = orderOf (⟨y', hyY⟩ : Y) := by
        rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      _ ∣ Nat.card Y := orderOf_dvd_natCard _
  let φ : E →* MulAut Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hEY)
  let : MulDistribMulAction E Y := MulDistribMulAction.compHom Y φ
  have hcard : ¬ 3 ∣ Nat.card (Sylow 2 Y) := fun h => h3Y (h.trans
    ((Sylow.card_dvd_index (Classical.arbitrary (Sylow 2 Y))).trans (Subgroup.index_dvd_card _)))
  obtain ⟨S, hS⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 Y) hcard
  have hSinv : ∀ e : E, ∀ s ∈ (S : Subgroup Y), e • s ∈ (S : Subgroup Y) := by
    intro e s hs
    have hmem : e • s ∈ ((e • S : Sylow 2 Y) : Subgroup Y) := by
      rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      exact ⟨s, hs, rfl⟩
    rwa [hS e] at hmem
  set U := (S : Subgroup Y).map Y.subtype
  refine ⟨U, ⟨(Subgroup.map_subtype_le _).trans hYL,
    (isPiSubgroup_piOf_iff Nat.prime_two U).mpr (S.isPGroup'.map Y.subtype), ?_⟩, ?_⟩
  · intro e he
    rw [Subgroup.mem_normalizer_iff]
    have hc : ∀ e ∈ E, ∀ t ∈ U, e * t * e⁻¹ ∈ U := by
      rintro e he _ ⟨s, hs, rfl⟩
      exact ⟨_, hSinv ⟨e, he⟩ s hs, rfl⟩
    intro t
    refine ⟨hc e he t, fun ht => ?_⟩
    have := hc e⁻¹ (E.inv_mem he) _ ht
    simpa [mul_assoc] using this
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective]
    exact Sylow.ne_bot_of_dvd_card S h2Y

theorem exists_isSylowOf_inf (p : ℕ) [Fact p.Prime] (H W : Subgroup G) :
    ∃ R : Subgroup G, IsSylowOf p R H ∧ IsSylowOf p (R ⊓ W) (H ⊓ W) := by
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (H ⊓ W)
  have hSH : S ≤ H := hS.le.trans inf_le_left
  obtain ⟨Q, hQ⟩ := (hS.isPGroup.comap_subtype (K := H)).exists_le_sylow
  refine ⟨(Q : Subgroup H).map H.subtype, ⟨Q, rfl⟩, ?_⟩
  have hSR : S ≤ (Q : Subgroup H).map H.subtype ⊓ W := fun x hx =>
    ⟨⟨⟨x, hSH hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩, (hS.le hx).2⟩
  have hRW := hS.eq_of_le hSR (inf_le_inf_right _ (Subgroup.map_subtype_le _))
    ((Q.isPGroup'.map H.subtype).to_le inf_le_left)
  rw [hRW]
  exact hS

@[expose] def OneNotFieldKind : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
    ¬ KFacts.InducesStdKind L 1 .field ∧ ¬ KFacts.InducesStdKind L 1 .graphField

@[expose] def NormalizesLc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    PartTwoStanding G → A ∈ partTwoF G → c ∈ A → c ≠ 1 → L ∈ thetaComponentsAt 3 c →
      A ≤ Subgroup.normalizer (L : Set G)

theorem item1134_of_item812 (h812 : Sec8.Item812) (h91 : Hyp91Never) (hone : OneNotFieldKind)
    (h45 : NormalizesLc) : Item1134 := by
  intro G _ _ A c L hst hAF hAT hcA hc1 hL hC halt hEF x hxA
  suffices hk : ¬ (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) from
    ⟨fun h => hk (Or.inl h), fun h => hk (Or.inr h)⟩
  intro hk
  have hx1 : x ≠ 1 := by
    rintro rfl
    rcases hk with h | h
    · exact (hone G L).1 h
    · exact (hone G L).2 h
  have hAN := h45 G A c L hst hAF hcA hc1 hL.2
  have hApg : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAF.1.2 g g.2)⟩
  have h81 : Sec8.Hyp81 G A c L x := ⟨hst, hAF, hcA, hc1, hL.2, hC, hxA, hx1, hk, fun hbig => by
    rcases halt with ⟨E, hE, hEA, hbar⟩ | ⟨h27, -⟩
    · exact ⟨E, hE, hEA, exists_invariantPiSubgroups_of_invTwoBarNontrivial (hApg.to_le hEA)
        (hEA.trans hAN) hbar⟩
    · omega, hEF⟩
  have h27 := h812 G A c L x h81
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR, hRW⟩ := exists_isSylowOf_inf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (Subgroup.normalizer (A : Set G))
  refine h91 G A c L x R ⟨h81, h27, ?_, hR, hRW, Or.inl hAT⟩
  rcases halt with ⟨E, hE, hEA, hbar⟩ | ⟨-, hA'⟩
  · have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [h27, hE.2.1])
    exact Or.inl (Or.inl (hEeq ▸ hbar))
  · exact Or.inl (Or.inr hA')

theorem oneNotFieldKind : OneNotFieldKind := fun _ _ _ L =>
  ⟨KFacts.not_inducesStdKind_one_field L, KFacts.not_inducesStdKind_one_graphField L⟩

theorem normalizesLc_of (h45 : Sec4.Item4_5) : NormalizesLc := by
  intro G _ _ A c L hG hA hcA hc1 hL
  exact Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hA.1 hcA hc1 L hL

theorem item1134_of_item45 (h812 : Sec8.Item812) (h91 : Hyp91Never) (h45 : Sec4.Item4_5) :
    Item1134 :=
  item1134_of_item812 h812 h91 oneNotFieldKind (normalizesLc_of h45)

theorem item1134E27_of
    (h91 : Hyp91Never) : Item1134E27 := by
  intro G _ _ A c L hst hAF hAT h27 hcA hc1 hL hC halt hEF x hxA
  suffices hk : ¬ (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) from
    ⟨fun h => hk (Or.inl h), fun h => hk (Or.inr h)⟩
  intro hk
  have hx1 : x ≠ 1 := by
    rintro rfl
    rcases hk with h | h
    · exact (oneNotFieldKind G L).1 h
    · exact (oneNotFieldKind G L).2 h
  have h81 : Sec8.Hyp81 G A c L x :=
    ⟨hst, hAF, hcA, hc1, hL.2, hC, hxA, hx1, hk, fun hbig => absurd hbig (by omega), hEF⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR, hRW⟩ := exists_isSylowOf_inf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (Subgroup.normalizer (A : Set G))
  refine h91 G A c L x R ⟨h81, h27, ?_, hR, hRW, Or.inl hAT⟩
  rcases halt with ⟨E, hE, hEA, hbar⟩ | ⟨-, hA'⟩
  · have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [h27, hE.2.1])
    exact Or.inl (Or.inl (hEeq ▸ hbar))
  · exact Or.inl (Or.inr hA')

end CFSG.RankThree.PartTwo.Sec11
