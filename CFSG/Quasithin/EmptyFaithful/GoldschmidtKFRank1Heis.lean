module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Out
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Abs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdAux

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.LocalCores CFSG.Open CFSG.Quasithin

@[expose] def OutThreeOrElemNine (S : Type) [Group S] : Prop :=
  OutThreeBound S ∨ CFSG.QuasithinUnique.Id2519.HasElemAb 3 9 S

section Extraspecial

variable {B : Type*} [Group B] [CFSG.IsExtraspecial 3 B]

theorem commutator_mem_center_of_extraspecial (g h : B) :
    g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center B := by
  have hcomm := (CFSG.IsExtraspecial.quotient_elementary_abelian 3 B).toIsMulCommutative
  rw [← QuotientGroup.eq_one_iff (N := Subgroup.center B)]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have h2 := hcomm.is_comm.comm (g : B ⧸ Subgroup.center B) (h : B ⧸ Subgroup.center B)
  rw [h2]
  group

theorem exists_mem_center_of_normal_ne_bot {N : Subgroup B} [hN : N.Normal] (hne : N ≠ ⊥) :
    ∃ z ∈ N, z ∈ Subgroup.center B ∧ z ≠ 1 := by
  obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  by_cases hgc : (g : B) ∈ Subgroup.center B
  · exact ⟨g, g.2, hgc, fun h => hg1 (Subtype.ext h)⟩
  · rw [Subgroup.mem_center_iff] at hgc
    push Not at hgc
    obtain ⟨h, hh⟩ := hgc
    refine ⟨h * (g : B) * h⁻¹ * (g : B)⁻¹, N.mul_mem (hN.conj_mem g g.2 h) (N.inv_mem g.2),
      commutator_mem_center_of_extraspecial h g, fun h1 => hh ?_⟩
    calc h * (g : B) = h * (g : B) * h⁻¹ * (g : B)⁻¹ * ((g : B) * h) := by group
      _ = (g : B) * h := by rw [h1, one_mul]

variable [Finite B]

theorem center_eq_zpowers_of_extraspecial {z : B} (hz : z ∈ Subgroup.center B) (hz1 : z ≠ 1) :
    Subgroup.center B = Subgroup.zpowers z := by
  have hcard : Nat.card ↥(Subgroup.center B) = 3 := CFSG.IsExtraspecial.center_order_p 3 B
  have hdvd : orderOf z ∣ 3 := by
    have h := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Subgroup.center B))
    rwa [hcard, Subgroup.orderOf_mk] at h
  have hord : orderOf z = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left fun h => hz1 (orderOf_eq_one_iff.mp h)
  symm
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
    (by rw [Nat.card_zpowers, hord, hcard])

end Extraspecial

section Quotient

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}

theorem isCyclic_of_isPGroup_quotient (h1 : CFSG.Open.pRank 3 L = 1)
    {T : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hT : IsPGroup 3 ↥T) : IsCyclic ↥T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hTQ⟩ := hT.exists_le_sylow
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective
    (QuotientGroup.mk'_surjective (Subgroup.center ↥L)) 3 Q
  have hPcyc : IsCyclic ↥(P : Subgroup ↥L) := isCyclic_of_isPGroup_of_pRank_eq_one h1 P.isPGroup'
  have hQ : (Q : Subgroup (↥L ⧸ Subgroup.center ↥L)) =
      (P : Subgroup ↥L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
    rw [← hP, Sylow.coe_mapSurjective]
  have hQcyc : IsCyclic ↥(Q : Subgroup (↥L ⧸ Subgroup.center ↥L)) := by
    rw [hQ]
    exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
  have : IsCyclic ↥(T.subgroupOf (Q : Subgroup (↥L ⧸ Subgroup.center ↥L))) :=
    Subgroup.isCyclic _
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTQ).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTQ).surjective

theorem isCyclic_of_le_of_pRank_eq_one (h1 : CFSG.Open.pRank 3 L = 1) {T : Subgroup Y}
    (hTL : T ≤ L) (hT : IsPGroup 3 ↥T) : IsCyclic ↥T := by
  have hTp : IsPGroup 3 ↥(T.subgroupOf L) :=
    hT.of_surjective (Subgroup.subgroupOfEquivOfLe hTL).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTL).symm.surjective
  have := isCyclic_of_isPGroup_of_pRank_eq_one h1 hTp
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTL).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTL).surjective

theorem center_eq_bot_of_simple_nonabelian {S : Type*} [Group S] [IsSimpleGroup S]
    (h : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h0 | h0
  · exact h0
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ Subgroup.center S := h0 ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

end Quotient

section Count

theorem card_le_three_mul_card_inf_of_pow_mul_mem {G : Type*} [Group G] [Finite G]
    {F C : Subgroup G} {a : G} (ha : a ∈ F) (h : ∀ b ∈ F, ∃ k < 3, a ^ k * b ∈ C) :
    Nat.card ↥F ≤ 3 * Nat.card ↥(F ⊓ C : Subgroup G) := by
  choose k hk hkC using h
  let φ : F → Fin 3 × (F ⊓ C : Subgroup G) := fun b =>
    (⟨k b b.2, hk b b.2⟩, ⟨a ^ k b b.2 * b, mul_mem (pow_mem ha _) b.2, hkC b b.2⟩)
  have hinj : Function.Injective φ := by
    intro b₁ b₂ hb
    simp only [φ, Prod.mk.injEq, Fin.mk.injEq] at hb
    obtain ⟨h1, h2⟩ := hb
    have h3 := congrArg Subtype.val h2
    simp only at h3
    rw [h1] at h3
    exact Subtype.ext (mul_left_cancel h3)
  have h := Nat.card_le_card_of_injective φ hinj
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h

variable {S : Type} [Group S] [Finite S]

theorem card_le_nine_of_outThreeBound (hcyc : ∀ T : Subgroup S, IsPGroup 3 ↥T → IsCyclic ↥T)
    (hZ : Subgroup.center S = ⊥) (hS : OutThreeBound S) (B' : Subgroup (MulAut S))
    (hB' : ∀ x ∈ B', x ^ 3 = 1) : Nat.card ↥B' ≤ 9 := by
  have : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) fun f g h => MulEquiv.ext (congrFun h)
  obtain ⟨α, hαB, hα⟩ := hS B' hB'
  set C : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range with hC
  have h1 : Nat.card ↥B' ≤ 3 * Nat.card ↥(B' ⊓ C : Subgroup (MulAut S)) :=
    card_le_three_mul_card_inf_of_pow_mul_mem hαB hα
  set Q : Subgroup S := (B' ⊓ C).comap (MulAut.conj : S →* MulAut S) with hQ
  have hQexp : ∀ x ∈ Q, x ^ 3 = 1 := by
    intro x hx
    have h3 : (MulAut.conj x) ^ 3 = 1 := hB' _ hx.1
    rw [← map_pow] at h3
    have hc : x ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h4 := congrArg (fun φ : MulAut S => φ g) h3
      simp only [MulAut.conj_apply, MulAut.one_apply] at h4
      exact (mul_inv_eq_iff_eq_mul.mp h4).symm
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hQp : IsPGroup 3 ↥Q := fun g => ⟨1, Subtype.ext (by simpa using hQexp g g.2)⟩
  have hQc : IsCyclic ↥Q := hcyc Q hQp
  have hQcard : Nat.card ↥Q ∣ 3 := by
    have hexp : Monoid.exponent ↥Q ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hQexp g g.2)
    rwa [IsCyclic.exponent_eq_card] at hexp
  have hsurj : Function.Surjective
      (fun q : Q => (⟨MulAut.conj (q : S), q.2⟩ : ↥(B' ⊓ C : Subgroup (MulAut S)))) := by
    rintro ⟨y, hyB, x, rfl⟩
    exact ⟨⟨x, hyB, ⟨x, rfl⟩⟩, rfl⟩
  have h2 : Nat.card ↥(B' ⊓ C : Subgroup (MulAut S)) ≤ Nat.card ↥Q :=
    Nat.card_le_card_of_surjective _ hsurj
  have h3 : Nat.card ↥Q ≤ 3 := Nat.le_of_dvd (by norm_num) hQcard
  omega

end Count

end CFSG.Quasithin.SBd19F
