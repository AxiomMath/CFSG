module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_14

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert V.8.15

The structure theorem for a finite fixed-point-free automorphism group.
-/

namespace CFSG.BenderSuzuki
namespace External

universe u

set_option maxHeartbeats 800000 in
/--
Huppert V.8.15.  Let `A` be a group of fixed-point-free automorphisms of the
finite group `G`.  The odd Sylow subgroups of `A` are cyclic, a Sylow
`2`-subgroup is cyclic or generalized quaternion, and every subgroup of `A`
whose order is a product of two primes is cyclic.
-/
public theorem huppert_V_8_15_fixedPointFree_automorphism_subgroup_classification
    {G : Type u} [Group G] [Finite G] (A : Subgroup (MulAut G))
    (hfixed : ∀ φ : A, φ ≠ 1 → ∀ g : G, (φ : MulAut G) g = g → g = 1) :
    (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p A, IsCyclic P) ∧
      (∀ P : Sylow 2 A,
        IsCyclic P ∨
          ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
            Nonempty (P ≃* QuaternionGroup k)) ∧
      (∀ p₁ p₂ : ℕ, p₁.Prime → p₂.Prime →
        ∀ H : Subgroup A, Nat.card H = p₁ * p₂ → IsCyclic H) := by
  classical
  by_cases hGnt : Nontrivial G
  · letI : Nontrivial G := hGnt
    letI : MulDistribMulAction A G := MulDistribMulAction.compHom G A.subtype
    have hregular : ActsRegularly A G := by
      intro a ha
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      have hag : ((a : MulAut G) g) = g := by
        simpa [MulAction.compHom_smul_def] using
          hg ⟨a, Subgroup.mem_zpowers a⟩
      exact hfixed a ha g hag
    have hinvolution_unique :
        ∀ a b : A, orderOf a = 2 → orderOf b = 2 → a = b := by
      intro a b ha hb
      have ha_ne : a ≠ 1 := by
        intro ha1
        rw [ha1, orderOf_one] at ha
        omega
      have hb_ne : b ≠ 1 := by
        intro hb1
        rw [hb1, orderOf_one] at hb
        omega
      have ha_fpf : MonoidHom.FixedPointFree (a : MulAut G) :=
        hfixed a ha_ne
      have hb_fpf : MonoidHom.FixedPointFree (b : MulAut G) :=
        hfixed b hb_ne
      have ha_sq : ((a : MulAut G) ^ 2) = 1 := by
        have ha_sq_A : a ^ 2 = 1 := by
          rw [← ha]
          exact pow_orderOf_eq_one a
        exact congrArg Subtype.val ha_sq_A
      have hb_sq : ((b : MulAut G) ^ 2) = 1 := by
        have hb_sq_A : b ^ 2 = 1 := by
          rw [← hb]
          exact pow_orderOf_eq_one b
        exact congrArg Subtype.val hb_sq_A
      have ha_involutive : Function.Involutive (a : MulAut G) := by
        intro g
        have h := congrArg (fun f : MulAut G => f g) ha_sq
        simpa [pow_two] using h
      have hb_involutive : Function.Involutive (b : MulAut G) := by
        intro g
        have h := congrArg (fun f : MulAut G => f g) hb_sq
        simpa [pow_two] using h
      have ha_inv := ha_fpf.coe_eq_inv_of_involutive ha_involutive
      have hb_inv := hb_fpf.coe_eq_inv_of_involutive hb_involutive
      apply Subtype.ext
      apply MulEquiv.ext
      intro g
      rw [congrFun ha_inv g, congrFun hb_inv g]
    have hunique_order_two_subgroup :
        ∀ (R : Subgroup A) (U V : Subgroup R),
          Nat.card U = 2 → Nat.card V = 2 → U = V := by
      intro R U V hU hV
      have hU_nontrivial : Nontrivial U :=
        Finite.one_lt_card_iff_nontrivial.mp (by omega)
      have hV_nontrivial : Nontrivial V :=
        Finite.one_lt_card_iff_nontrivial.mp (by omega)
      letI : Nontrivial U := hU_nontrivial
      letI : Nontrivial V := hV_nontrivial
      obtain ⟨u, hu_ne⟩ := exists_ne (1 : U)
      obtain ⟨v, hv_ne⟩ := exists_ne (1 : V)
      have hu_order : orderOf u = 2 := by
        have hdvd : orderOf u ∣ 2 := by
          simpa [hU] using orderOf_dvd_natCard u
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact False.elim (hu_ne (orderOf_eq_one_iff.mp h))
        · exact h
      have hv_order : orderOf v = 2 := by
        have hdvd : orderOf v ∣ 2 := by
          simpa [hV] using orderOf_dvd_natCard v
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact False.elim (hv_ne (orderOf_eq_one_iff.mp h))
        · exact h
      have hu_order_R : orderOf (u : R) = 2 := by
        simpa only [Subgroup.orderOf_coe] using hu_order
      have hv_order_R : orderOf (v : R) = 2 := by
        simpa only [Subgroup.orderOf_coe] using hv_order
      have hu_order_A : orderOf ((u : R) : A) = 2 := by
        simpa only [Subgroup.orderOf_coe] using hu_order_R
      have hv_order_A : orderOf ((v : R) : A) = 2 := by
        simpa only [Subgroup.orderOf_coe] using hv_order_R
      have huv_A : ((u : R) : A) = ((v : R) : A) :=
        hinvolution_unique _ _ hu_order_A hv_order_A
      have huv_R : (u : R) = (v : R) := Subtype.ext huv_A
      have hzu : Subgroup.zpowers (u : R) = U := by
        apply Subgroup.eq_of_le_of_card_ge
        · exact (Subgroup.zpowers_le).2 u.2
        · rw [Nat.card_zpowers, hu_order_R, hU]
      have hzv : Subgroup.zpowers (v : R) = V := by
        apply Subgroup.eq_of_le_of_card_ge
        · exact (Subgroup.zpowers_le).2 v.2
        · rw [Nat.card_zpowers, hv_order_R, hV]
      calc
        U = Subgroup.zpowers (u : R) := hzu.symm
        _ = Subgroup.zpowers (v : R) := by rw [huv_R]
        _ = V := hzv
    refine ⟨?_, ?_, ?_⟩
    · intro p hpFact hp_ne_two P
      have hp : Nat.Prime p := hpFact.out
      obtain ⟨n, hP_card⟩ := P.isPGroup'.exists_card_eq
      have hP_odd : Odd (Nat.card P) := by
        rw [hP_card]
        exact (hp.odd_of_ne_two hp_ne_two).pow
      letI : MulDistribMulAction P G :=
        MulDistribMulAction.compHom G (P : Subgroup A).subtype
      have hP_regular : ActsRegularly P G :=
        hregular.subgroup (P : Subgroup A)
      have htop_p : IsPGroup p (⊤ : Subgroup P) :=
        P.isPGroup'.to_subgroup ⊤
      have htop_cyclic : IsCyclic (⊤ : Subgroup P) :=
        isCyclic_of_odd_regular_pSubgroup hp hP_odd hP_regular htop_p
      exact (Subgroup.topEquiv : (⊤ : Subgroup P) ≃* P).isCyclic.mp htop_cyclic
    · intro P
      by_cases hP_bot : (P : Subgroup A) = ⊥
      · left
        haveI : Subsingleton P := by
          constructor
          intro x y
          apply Subtype.ext
          have hx : (x : A) = 1 := by
            apply Subgroup.mem_bot.mp
            simpa [hP_bot] using x.2
          have hy : (y : A) = 1 := by
            apply Subgroup.mem_bot.mp
            simpa [hP_bot] using y.2
          rw [hx, hy]
        exact isCyclic_of_subsingleton
      · haveI : Nontrivial P :=
          (Subgroup.nontrivial_iff_ne_bot (P : Subgroup A)).mpr hP_bot
        obtain ⟨U, hU_card'⟩ :=
          Sylow.exists_subgroup_card_pow_prime_of_le_card
            Nat.prime_two P.isPGroup' (n := 1) (by
              have h := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial P)
              omega)
        have hU_card : Nat.card U = 2 := by simpa using hU_card'
        have hunique : ∀ V : Subgroup P, Nat.card V = 2 → V = U := by
          intro V hV
          exact hunique_order_two_subgroup (P : Subgroup A) V U hV hU_card
        have hclass :=
          huppert_III_8_2_pgroup_unique_order_prime_subgroup
            Nat.prime_two P.isPGroup' ⟨U, hU_card, hunique⟩
        rcases hclass.2 rfl with hcyclic | hquaternion
        · exact Or.inl hcyclic
        · rcases hquaternion with ⟨n, hn, e⟩
          have hk : 2 ≤ 2 ^ (n - 2) := by
            calc
              2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (n - 2) :=
                Nat.pow_le_pow_right (by decide) (by omega)
          have hQp : IsPGroup 2 (QuaternionGroup (2 ^ (n - 2))) :=
            P.isPGroup'.of_equiv e.some
          exact Or.inr ⟨2 ^ (n - 2), hk, hQp, e⟩
    · intro p₁ p₂ hp₁ hp₂ H hcard
      letI : MulDistribMulAction H G :=
        MulDistribMulAction.compHom G H.subtype
      have hH_regular : ActsRegularly H G := hregular.subgroup H
      have heven_case (q : ℕ) (hq : q.Prime) (hq_ne_two : q ≠ 2)
          (hcard_even : Nat.card H = 2 * q) : IsCyclic H := by
        letI : Fact q.Prime := ⟨hq⟩
        have htwo_lt_q : 2 < q :=
          lt_of_le_of_ne hq.two_le (Ne.symm hq_ne_two)
        obtain ⟨P, hPcard_pow⟩ :=
          Sylow.exists_subgroup_card_pow_prime
            (G := H) 2 (n := 1) (by rw [hcard_even]; simp)
        obtain ⟨Q, hQcard_pow⟩ :=
          Sylow.exists_subgroup_card_pow_prime
            (G := H) q (n := 1) (by rw [hcard_even]; simp)
        have hPcard : Nat.card P = 2 := by simpa using hPcard_pow
        have hQcard : Nat.card Q = q := by simpa using hQcard_pow
        have hPchar : P.Characteristic := by
          rw [Subgroup.characteristic_iff_map_eq]
          intro φ
          apply hunique_order_two_subgroup H
          · calc
              Nat.card (P.map φ.toMonoidHom) = Nat.card P :=
                Subgroup.card_map_of_injective
                  (K := P) (f := φ.toMonoidHom) φ.injective
              _ = 2 := hPcard
          · exact hPcard
        have hPnormal : P.Normal := by
          letI : P.Characteristic := hPchar
          exact Subgroup.normal_of_characteristic P
        have hQp : IsPGroup q Q := by
          refine IsPGroup.of_card (p := q) (G := Q) (n := 1) ?_
          simpa using hQcard
        have hQindex : Q.index = 2 := by
          have hmul : q * Q.index = q * 2 := by
            calc
              q * Q.index = Nat.card Q * Q.index := by rw [hQcard]
              _ = Nat.card H := Q.card_mul_index
              _ = 2 * q := hcard_even
              _ = q * 2 := by rw [mul_comm]
          exact Nat.eq_of_mul_eq_mul_left hq.pos hmul
        have hq_not_dvd_Qindex : ¬ q ∣ Q.index := by
          rw [hQindex]
          intro hdiv
          exact (Nat.le_of_dvd (by decide : 0 < 2) hdiv).not_gt htwo_lt_q
        let Qsyl : Sylow q H := hQp.toSylow hq_not_dvd_Qindex
        have hcardSyl_dvd_two : Nat.card (Sylow q H) ∣ 2 := by
          have h := Sylow.card_dvd_index Qsyl
          simpa [Qsyl, IsPGroup.toSylow_coe, hQindex] using h
        have hcardSyl_eq_one : Nat.card (Sylow q H) = 1 := by
          have hcardSyl_le_two : Nat.card (Sylow q H) ≤ 2 :=
            Nat.le_of_dvd (by decide : 0 < 2) hcardSyl_dvd_two
          have hcardSyl_lt_q : Nat.card (Sylow q H) < q :=
            lt_of_le_of_lt hcardSyl_le_two htwo_lt_q
          have hcardSyl_mod :
              Nat.card (Sylow q H) % q = Nat.card (Sylow q H) :=
            Nat.mod_eq_of_lt hcardSyl_lt_q
          have hOne_mod : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
          have hmod : Nat.card (Sylow q H) % q = 1 % q :=
            (card_sylow_modEq_one q H :
              Nat.card (Sylow q H) ≡ 1 [MOD q])
          omega
        haveI : Subsingleton (Sylow q H) :=
          (Nat.card_eq_one_iff_unique.mp hcardSyl_eq_one).1
        have hQnormal : Q.Normal := by
          have hQsylnormal : (Qsyl : Subgroup H).Normal :=
            Sylow.normal_of_subsingleton Qsyl
          simpa [Qsyl, IsPGroup.toSylow_coe] using hQsylnormal
        have hcop : Nat.Coprime (Nat.card Q) (Nat.card P) := by
          simpa [hQcard, hPcard] using
            ((Nat.coprime_primes hq Nat.prime_two).2 hq_ne_two)
        have hdis : Disjoint Q P :=
          disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime hcop)
        have hcard_mul : Nat.card Q * Nat.card P = Nat.card H := by
          rw [hQcard, hPcard, hcard_even, mul_comm]
        have hcomp : Q.IsComplement' P :=
          Subgroup.isComplement'_of_card_mul_and_disjoint hcard_mul hdis
        have hPcyc : IsCyclic P := isCyclic_of_prime_card hPcard
        have hQcyc : IsCyclic Q := isCyclic_of_prime_card hQcard
        have hcent : P ≤ Subgroup.centralizer (Q : Set H) := by
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (Subgroup.commute_of_normal_of_disjoint
            Q P hQnormal hPnormal hdis y x hy hx).eq
        exact isCyclic_of_isComplement'_of_cyclic_of_le_centralizer
          hcomp hQcyc hPcyc hcop hcent
      by_cases hpq : p₁ = p₂
      · subst p₂
        have hHp : IsPGroup p₁ H :=
          IsPGroup.of_card (n := 2) (by simpa [pow_two] using hcard)
        by_cases hp_two : p₁ = 2
        · subst p₁
          haveI : Nontrivial H :=
            Finite.one_lt_card_iff_nontrivial.mp (by
              rw [hcard]
              norm_num)
          obtain ⟨U, hU_card'⟩ :=
            Sylow.exists_subgroup_card_pow_prime_of_le_card
              Nat.prime_two hHp (n := 1) (by
                have h := Finite.one_lt_card_iff_nontrivial.mpr
                  (inferInstance : Nontrivial H)
                omega)
          have hU_card : Nat.card U = 2 := by simpa using hU_card'
          have hunique : ∀ V : Subgroup H, Nat.card V = 2 → V = U := by
            intro V hV
            exact hunique_order_two_subgroup H V U hV hU_card
          have hclass :=
            huppert_III_8_2_pgroup_unique_order_prime_subgroup
              Nat.prime_two hHp ⟨U, hU_card, hunique⟩
          rcases hclass.2 rfl with hcyclic | hquaternion
          · exact hcyclic
          · rcases hquaternion with ⟨n, hn, e⟩
            have hk : 2 ≤ 2 ^ (n - 2) := by
              calc
                2 = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (n - 2) :=
                  Nat.pow_le_pow_right (by decide) (by omega)
            letI : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
            have hcard_e := Nat.card_congr e.some.toEquiv
            have hcardQ : Nat.card (QuaternionGroup (2 ^ (n - 2))) =
                4 * (2 ^ (n - 2)) := by
              rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
            rw [hcard, hcardQ] at hcard_e
            exfalso
            omega
        · have hHodd : Odd (Nat.card H) := by
            rw [hcard]
            exact (hp₁.odd_of_ne_two hp_two).mul (hp₁.odd_of_ne_two hp_two)
          have htop_p : IsPGroup p₁ (⊤ : Subgroup H) := hHp.to_subgroup ⊤
          have htop_cyclic : IsCyclic (⊤ : Subgroup H) :=
            isCyclic_of_odd_regular_pSubgroup hp₁ hHodd hH_regular htop_p
          exact (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).isCyclic.mp htop_cyclic
      · by_cases hp_two : p₁ = 2
        · subst p₁
          exact heven_case p₂ hp₂ (Ne.symm hpq) hcard
        · by_cases hq_two : p₂ = 2
          · subst p₂
            exact heven_case p₁ hp₁ hp_two (by simpa [mul_comm] using hcard)
          · have hHodd : Odd (Nat.card H) := by
              rw [hcard]
              exact (hp₁.odd_of_ne_two hp_two).mul (hp₂.odd_of_ne_two hq_two)
            exact regular_pq_group_cyclic_of_odd_regular_action
              hp₁ hp₂ hpq hcard hHodd hH_regular
  · letI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hGnt
    haveI : Subsingleton (MulAut G) :=
      ⟨fun f g => MulEquiv.ext fun x => Subsingleton.elim (f x) (g x)⟩
    haveI : Subsingleton A := inferInstance
    refine ⟨?_, ?_, ?_⟩
    · intro p hpFact hp_ne_two P
      exact isCyclic_of_subsingleton
    · intro P
      exact Or.inl isCyclic_of_subsingleton
    · intro p₁ p₂ hp₁ hp₂ H hH
      exact isCyclic_of_subsingleton

end External
end CFSG.BenderSuzuki



