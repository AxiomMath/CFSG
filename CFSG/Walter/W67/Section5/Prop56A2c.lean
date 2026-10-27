module

public import CFSG.Walter.W67.Section5.Prop56A2b
public import CFSG.Walter.W67.Section5.P56AbEnd
public import CFSG.Walter.W67.Section6.Basic

public section

namespace CFSG.Walter.W67

variable {G : Type} [Group G] [Finite G]

namespace Frame5

variable {s : Std G} {f5 : Frame5 s}

namespace RData

variable {R : Subgroup G} (hR : f5.RData R)
include hR

theorem false_of_abelian
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (h3 : 3 ∣ Nat.card s.fr.E) (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hRq : Nat.card R = s.q ^ 2)
    (hmax : ∀ Q : Subgroup G, IsPGroup 3 Q → R ≤ Q → s.J ∈ Subgroup.normalizer (Q : Set G) →
      f5.B ≤ Subgroup.normalizer (Q : Set G) → s.fr.E ≤ Subgroup.normalizer (Q : Set G) →
      Q = R) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hP₂c, hsup⟩ := hR.card_P₂ hRc h22 h26i hp hRq
  have hpow := hR.pow_three_eq_one hRc h22 h26i hp hRq
  have hfpf := f5.fpf_of_isPGroup h22 h26i hp hR.isPGroup hR.B_le hR.E_le
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 s.fr.E) := inferInstance
  set P₀ := (S₀ : Subgroup s.fr.E).map s.fr.E.subtype with hP₀def
  have hP₀E : P₀ ≤ s.fr.E := Subgroup.map_subtype_le _
  have hP₀3 : IsPGroup 3 P₀ := S₀.isPGroup'.map _
  have hP₀card : Nat.card P₀ = 3 ^ (Nat.card s.fr.E).factorization 3 := by
    rw [hP₀def, Subgroup.card_map_of_injective s.fr.E.subtype_injective,
      Sylow.card_eq_multiplicity]
  have hapos : 0 < (Nat.card s.fr.E).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3
  have h3f := s.three_dvd_f h26i h3
  refine prop_5_6_abelian G
    { n := s.f
      odd_n := s.odd_f_of_p3 hp
      three_le_n := Nat.le_of_dvd s.f_pos h3f
      three_dvd_n := h3f
      perfect := s.perfect
      abelian_sylow := s.abelian_sylow
      elementary_sylow := s.elementary_sylow
      no_real_three := fun u x t hu hx ht hx1 hx3 ht2 hinv =>
        s.no_real_three h22 hp hu hx ht hx1 (k := 1) (by rwa [pow_one]) ht2 hinv
      centralizer_involution := fun u hu => s.centralizer_involution h22 h26i hp hu
      J := s.J
      orderOf_J := s.orderOf_J
      B := f5.B
      B_cyclic := f5.B_cyclic
      card_B := by rw [f5.card_B, Hyp.q, hp]
      B_le := f5.B_le.trans s.K_le_H
      E := s.fr.E
      E_cyclic := Sec6.isCyclic_E s
      odd_card_E := s.fr.odd_card_E
      E_le := s.fr.E_le_H
      E_le_normalizer_B := f5.E_le_normalizer_B
      E_faithful := fun e he h => by
        by_contra he1
        obtain ⟨b, hb, hne⟩ := f5.exists_not_comm_B h26i he he1
        exact hne (h b hb)
      P₀ := P₀
      P₀_le := hP₀E
      P₀_isPGroup := hP₀3
      P₀_sylow := by
        rw [hP₀card, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
      P₀_ne_bot := fun h => by
        rw [h, Subgroup.card_bot] at hP₀card
        have := Nat.one_lt_pow hapos.ne' (by norm_num : 1 < 3)
        omega
      centralizer_B := fun y hy hy1 b hb hyb => by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP₀3
        have hyk : y ^ (3 ^ k) = 1 := by
          rw [← hk]
          have := pow_card_eq_one' (x := (⟨y, hy⟩ : P₀))
          exact congrArg Subtype.val this
        exact s.centralizer_B h26i hp f5 (hP₀E hy) hyk hy1 hb hyb
      P₁ := f5.P₁
      P₂ := Sec56.invSub s.J R hRc
      P₁_elementary := f5.isElementaryAbelian_P₁ hp
      P₂_elementary :=
        { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
            (hRc _ (P₂_le hRc a.2) _ (P₂_le hRc b.2))⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (by
            simpa using hpow _ (P₂_le hRc a.2)) }
      card_P₁ := by rw [f5.card_P₁, Hyp.q, hp]
      card_P₂ := by rw [hP₂c, Hyp.q, hp]
      P₁_inf_P₂ := hR.P₁_inf_P₂ hRc
      P₁_comm_P₂ := fun a ha b hb => hRc a (hR.P₁_le ha) b (P₂_le hRc hb)
      P₁_le := f5.P₁_le.trans s.K_le_H
      J_inv := fun y hy => hy.2
      B_le_normalizer₁ := f5.B_le_normalizer_P₁
      B_le_normalizer₂ := hR.B_le_P₂ hRc
      E_le_normalizer₁ := f5.E_le_normalizer_P₁
      E_le_normalizer₂ := hR.E_le_P₂ hRc
      fixedPointFree₁ := f5.fpf_P₁
      fixedPointFree₂ := fun b hb hb1 y hy hby => hfpf b hb hb1 y (P₂_le hRc hy) hby
      irreducible₁ := fun Q hQ hBQ => f5.irred_P₁ hQ fun b hb v hv =>
        (Subgroup.mem_normalizer_iff.mp (hBQ hb) v).mp hv
      irreducible₂ := fun Q hQ hBQ => by
        obtain ⟨k, hk⟩ := f5.card_eq_q_pow hp (hR.isPGroup.to_le (hQ.trans (P₂_le hRc))) hBQ
          (fun b hb hb1 y hy => hfpf b hb hb1 y (P₂_le hRc (hQ hy)))
        have h1 := Subgroup.card_le_of_le hQ
        rw [hk, hP₂c] at h1
        have hk1 : k ≤ 1 := (Nat.pow_le_pow_iff_right s.one_lt_q).mp (by rwa [pow_one])
        rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · left
          exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
        · right
          exact Subgroup.eq_of_le_of_card_ge hQ (by rw [hk, hP₂c, pow_one])
      free := fun y hy hoy => by
        rw [hsup]
        exact f5.card_inf_centralizer_pow_three h22 h26i hp hR.isPGroup hR.B_le hR.E_le
          (hP₀E hy) hoy
      sylow_centralizer := fun Q hQ hQC => by
        rw [hsup] at hQC
        have h1 := hR.max Q hQ (hQC.trans (Subgroup.centralizer_le hR.P₁_le))
        rw [hRq, Hyp.q, hp, ← pow_mul, mul_comm] at h1
        exact h1
      maximal := fun Q hQ hVQ hJQ hBQ hEQ => by
        rw [hsup] at hVQ ⊢
        exact hmax Q hQ hVQ hJQ hBQ hEQ
      normalizer_inf_centralizer_J := by
        rw [hsup]
        exact hR.normalizer_inf_H_le h22 h26i hp
      centralizer_J_inf := by
        rw [hsup]
        exact hR.H_inf_centralizer_le hRc h22 h26i hp hRq }

end RData

end Frame5

end CFSG.Walter.W67
