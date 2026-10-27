module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_3_split
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Coprime odd Sylow subgroups of PSL(2,q)

Odd Sylow subgroups whose defining prime is coprime to the field cardinal lie
in a split or nonsplit cyclic torus.  The proof uses Huppert II.8.5(a)'s
three-family partition and the exact torus-normalizer cardinalities.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.MatrixGroups
open scoped LinearAlgebra.Projectivization Pointwise IsMulCommutative

universe u

set_option maxHeartbeats 4000000 in
public theorem psl2_sylow_isCyclic_of_coprime_field_card
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) (hKseven : 7 ≤ Nat.card K) :
    ∀ r [Fact r.Prime], r ≠ 2 → Nat.Coprime r (Nat.card K) →
      ∀ R : Sylow r (PSL2MatrixGroup K), IsCyclic R := by
  intro r hrFact hrne hrcop R
  obtain ⟨U, S, hUc, hUcard, hSc, hScard, hpart⟩ :=
    BenderSuzuki.External.huppert_II_8_5_a_psl2_partition
      (F := K) (p := p) (f := f) hKcard
      (default : Sylow p (PSL2MatrixGroup K))
  have hP0card :
      Nat.card ((default : Sylow p (PSL2MatrixGroup K)) :
        Subgroup (PSL2MatrixGroup K)) = Nat.card K := by
    obtain ⟨eP0⟩ :=
      BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
        hKcard (default : Sylow p (PSL2MatrixGroup K))
    exact (Nat.card_congr eP0.toEquiv).symm
  by_cases hRbot : (R : Subgroup (PSL2MatrixGroup K)) = ⊥
  · apply IsCyclic.mk
    refine ⟨1, ?_⟩
    intro z
    refine ⟨0, ?_⟩
    apply Subtype.ext
    have hzbot : (z : PSL2MatrixGroup K) ∈
        (⊥ : Subgroup (PSL2MatrixGroup K)) := by
      rw [← hRbot]
      exact z.property
    simpa using (Subgroup.mem_bot.mp hzbot).symm
  have hRcard_gt : 1 < Nat.card (R : Subgroup (PSL2MatrixGroup K)) :=
    (Subgroup.one_lt_card_iff_ne_bot _).2 hRbot
  obtain ⟨k, hk⟩ : ∃ k : ℕ,
      Nat.card (R : Subgroup (PSL2MatrixGroup K)) = r ^ k :=
    (IsPGroup.iff_card.mp R.isPGroup')
  have hkpos : 0 < k := by
    by_contra hk0
    have hkz : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hkz, pow_zero] at hk
    omega
  have hrdivR : r ∣ Nat.card (R : Subgroup (PSL2MatrixGroup K)) := by
    rw [hk]
    exact dvd_pow_self r (Nat.ne_of_gt hkpos)
  have hrdivG : r ∣ Nat.card (PSL2MatrixGroup K) := by
    have hcarddiv : Nat.card (R : Subgroup (PSL2MatrixGroup K)) ∣
        Nat.card (⊤ : Subgroup (PSL2MatrixGroup K)) :=
      Subgroup.card_dvd_of_le le_top
    exact dvd_trans hrdivR (by simpa using hcarddiv)
  letI : Nontrivial (R : Type _) :=
    Finite.one_lt_card_iff_nontrivial.mp hRcard_gt
  have hcenterNontrivial :
      Nontrivial (Subgroup.center (R : Subgroup (PSL2MatrixGroup K))) :=
    IsPGroup.center_nontrivial
      (G := (R : Subgroup (PSL2MatrixGroup K)))
      (Sylow.isPGroup' R)
  have hcenterCard_gt : 1 < Nat.card (Subgroup.center
      (R : Subgroup (PSL2MatrixGroup K))) :=
    Finite.one_lt_card_iff_nontrivial.mpr hcenterNontrivial
  have hrdivCenter : r ∣ Nat.card (Subgroup.center
      (R : Subgroup (PSL2MatrixGroup K))) := by
    obtain ⟨kc, hkc⟩ :=
      (IsPGroup.iff_card.mp ((Sylow.isPGroup' R).to_subgroup
        (Subgroup.center (R : Subgroup (PSL2MatrixGroup K)))))
    have hkcpos : 0 < kc := by
      by_contra hk0
      have hkz : kc = 0 := Nat.eq_zero_of_not_pos hk0
      rw [hkz, pow_zero] at hkc
      have hcardone : Nat.card (Subgroup.center
          (R : Subgroup (PSL2MatrixGroup K))) = 1 := hkc
      have hnot : ¬ Nontrivial (Subgroup.center
          (R : Subgroup (PSL2MatrixGroup K))) := by
        rw [not_nontrivial_iff_subsingleton]
        exact (Nat.card_eq_one_iff_unique.mp hcardone).1
      exact hnot hcenterNontrivial
    rw [hkc]
    exact dvd_pow_self r (Nat.ne_of_gt hkcpos)
  obtain ⟨z, hzorder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := Subgroup.center (R : Subgroup (PSL2MatrixGroup K))) r
      hrdivCenter
  have hzR : (z : PSL2MatrixGroup K) ∈ (R : Subgroup _) :=
    (z : R).property
  have hzne : (z : PSL2MatrixGroup K) ≠ 1 := by
    intro hz
    have hzcenterone : z =
        (1 : Subgroup.center (R : Subgroup (PSL2MatrixGroup K))) := by
      apply Subtype.ext
      apply Subtype.ext
      exact hz
    have : (1 : ℕ) = r := by simpa [hzcenterone] using hzorder
    exact hrFact.out.ne_one this.symm
  have hzcR : ∀ y : R, (z : PSL2MatrixGroup K) * (y : _) =
      (y : _) * (z : _) := by
    intro y
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp z.property (y : R)).symm
  have hzorderG : orderOf (z : PSL2MatrixGroup K) = r := by
    calc
      orderOf (z : PSL2MatrixGroup K) = orderOf (z : R) :=
        Subgroup.orderOf_coe (z : R)
      _ = orderOf z := Subgroup.orderOf_coe z
      _ = r := hzorder
  obtain ⟨T, hzT, hTuniq⟩ := hpart (z : PSL2MatrixGroup K) hzne
  let Family : Subgroup (PSL2MatrixGroup K) → Prop := fun T =>
    (∃ g, T = (default : Sylow p (PSL2MatrixGroup K)).map
      (MulAut.conj g).toMonoidHom) ∨
      (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g, T = S.map (MulAut.conj g).toMonoidHom)
  have hpartitionFamily : ∀ x : PSL2MatrixGroup K, x ≠ 1 →
      ∃! T : Subgroup (PSL2MatrixGroup K), x ∈ T ∧ Family T := by
    simpa [Family] using hpart
  have hfamily_map : ∀ (T : Subgroup (PSL2MatrixGroup K))
      (x : PSL2MatrixGroup K), Family T → Family (T.map (MulAut.conj x).toMonoidHom) := by
    intro T x hT
    rcases hT with ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
    · left
      refine ⟨x * g, ?_⟩
      rw [hg, Subgroup.map_map]
      congr 1
      ext y
      change x * (g * y * g⁻¹) * x⁻¹ =
        (x * g) * y * (x * g)⁻¹
      rw [mul_inv_rev]
      simp only [mul_assoc]
    · right; left
      refine ⟨x * g, ?_⟩
      rw [hg, Subgroup.map_map]
      congr 1
      ext y
      change x * (g * y * g⁻¹) * x⁻¹ =
        (x * g) * y * (x * g)⁻¹
      rw [mul_inv_rev]
      simp only [mul_assoc]
    · right; right
      refine ⟨x * g, ?_⟩
      rw [hg, Subgroup.map_map]
      congr 1
      ext y
      change x * (g * y * g⁻¹) * x⁻¹ =
        (x * g) * y * (x * g)⁻¹
      rw [mul_inv_rev]
      simp only [mul_assoc]
  rcases hzT.2 with hTP | hTU | hTS
  · exfalso
    rcases hTP with ⟨g, hg⟩
    have hTcard : Nat.card T = Nat.card K := by
      rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
        hP0card]
    have hrdivT : r ∣ Nat.card T := by
      have hord : orderOf (z : PSL2MatrixGroup K) ∣ Nat.card T := by
        simpa [Subgroup.orderOf_coe] using
          (orderOf_dvd_natCard (⟨(z : PSL2MatrixGroup K), hzT.1⟩ : T))
      simpa [hzorderG] using hord
    have hrone : r = 1 := by
      apply Nat.eq_one_of_dvd_coprimes hrcop
      · exact dvd_refl r
      · simpa [hTcard] using hrdivT
    exact hrFact.out.ne_one hrone
  · rcases hTU with ⟨g, hg⟩
    have hRnorm : (R : Subgroup (PSL2MatrixGroup K)) ≤
        Subgroup.normalizer (T : Set (PSL2MatrixGroup K)) := by
      apply subgroup_le_normalizer_of_conj_mem T (R : Subgroup _)
      intro x hx hh
      let Tconj : Subgroup (PSL2MatrixGroup K) :=
        T.map ((MulAut.conj (x : PSL2MatrixGroup K)).toMonoidHom)
      have hTconjEq : Tconj = T := by
        apply hTuniq
        refine ⟨?_, ?_⟩
        · change (z : PSL2MatrixGroup K) ∈
            T.map ((MulAut.conj (x : PSL2MatrixGroup K)).toMonoidHom)
          rw [Subgroup.mem_map]
          refine ⟨(z : PSL2MatrixGroup K), hzT.1, ?_⟩
          change (x : PSL2MatrixGroup K) * (z : _) *
              (x : PSL2MatrixGroup K)⁻¹ = (z : _)
          have hcz := hzcR x
          calc
            (x : PSL2MatrixGroup K) * (z : _) *
                (x : PSL2MatrixGroup K)⁻¹ =
                ((z : _) * (x : PSL2MatrixGroup K)) *
                  (x : PSL2MatrixGroup K)⁻¹ := by rw [hcz.symm]
            _ = (z : _) := by simp [mul_assoc]
        · simpa [Tconj, Family] using hfamily_map T (x : PSL2MatrixGroup K) (by
            right; left; exact ⟨g, hg⟩)
      have hmap : (x : PSL2MatrixGroup K) * hx *
          (x : PSL2MatrixGroup K)⁻¹ ∈ Tconj := by
        change (x : PSL2MatrixGroup K) * hx *
            (x : PSL2MatrixGroup K)⁻¹ ∈
          T.map ((MulAut.conj (x : PSL2MatrixGroup K)).toMonoidHom)
        rw [Subgroup.mem_map]
        exact ⟨hx, hh, rfl⟩
      rw [hTconjEq] at hmap
      exact hmap
    obtain ⟨U0, hU0cyclic, hU0card, hU0normalizer⟩ :=
      BenderSuzuki.External.huppert_II_8_3_split_torus_normalizer_card
        (F := K) (p := p) (f := f) hKcard
    have hU0card_gt : 1 < Nat.card U0 := by
      have hgcdpos : 0 < Nat.gcd (Nat.card K - 1) 2 :=
        Nat.gcd_pos_of_pos_right _ (by norm_num)
      have hgcdle : Nat.gcd (Nat.card K - 1) 2 ≤ 2 :=
        Nat.gcd_le_right _ (by norm_num)
      rw [hU0card]
      have hthree : 3 ≤
          (Nat.card K - 1) / Nat.gcd (Nat.card K - 1) 2 := by
        apply (Nat.le_div_iff_mul_le hgcdpos).2
        omega
      omega
    have hU0ne : U0 ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot]
      exact hU0card_gt
    have hU0align : ∃ a : PSL2MatrixGroup K,
        U0 = U.map (MulAut.conj a).toMonoidHom := by
      obtain ⟨u, hu_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU0ne
      have huG : (u : PSL2MatrixGroup K) ≠ 1 := by
        intro hu
        apply hu_ne
        apply Subtype.ext
        exact hu
      obtain ⟨T0, huT0, hT0uniq⟩ := hpart (u : PSL2MatrixGroup K) huG
      have hU0leT0 : U0 ≤ T0 :=
          BenderSuzuki.lemma114_cyclic_le_unique_partition_family Family
          hpartitionFamily huG huT0.1 (by simpa [Family] using huT0.2)
          u.property hU0cyclic
      rcases huT0.2 with hT0P | hT0U | hT0S
      · exfalso
        rcases hT0P with ⟨g, hg⟩
        have hcop : Nat.Coprime (Nat.card U0) (Nat.card T0) := by
          rw [hg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective]
          rw [hU0card, hP0card]
          exact (BenderSuzuki.lemma114_q_coprime_split_order
            (Nat.card K) Nat.card_pos).symm
        exact huG (BenderSuzuki.lemma114_mem_eq_one_of_coprime_card U0 T0 hcop
          u.property (hU0leT0 u.property))
      · rcases hT0U with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        calc
          U0 = T0 := Subgroup.eq_of_le_of_card_ge hU0leT0 (by
            rw [ha, Subgroup.card_map_of_injective
              (MulAut.conj a).injective, hU0card, hUcard])
          _ = U.map (MulAut.conj a).toMonoidHom := ha
      · exfalso
        rcases hT0S with ⟨g, hg⟩
        have hcop : Nat.Coprime (Nat.card U0) (Nat.card T0) := by
          rw [hg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective]
          rw [hU0card, hScard]
          exact BenderSuzuki.lemma114_split_nonsplit_order_coprime
            (Nat.card K) (Finite.one_lt_card (α := K))
        exact huG (BenderSuzuki.lemma114_mem_eq_one_of_coprime_card U0 T0 hcop
          u.property (hU0leT0 u.property))
    obtain ⟨a, ha⟩ := hU0align
    let b : PSL2MatrixGroup K := g * a⁻¹
    have hTmap : T = U0.map (MulAut.conj b).toMonoidHom := by
      have heq :
          (MulEquiv.toMonoidHom (MulAut.conj b)).comp
              (MulEquiv.toMonoidHom (MulAut.conj a)) =
            MulEquiv.toMonoidHom (MulAut.conj g) := by
        apply MonoidHom.ext
        intro x
        change b * (a * x * a⁻¹) * b⁻¹ = g * x * g⁻¹
        have hb_inv : b⁻¹ = a * g⁻¹ := by
          dsimp [b]
          rw [mul_inv_rev, inv_inv]
        rw [hb_inv]
        rw [show b = g * a⁻¹ by rfl]
        simp only [mul_assoc]
        rw [@inv_mul_cancel_left (PSL2MatrixGroup K) _]
        rw [@inv_mul_cancel_left (PSL2MatrixGroup K) _]
      rw [hg, ha, Subgroup.map_map, heq]
    have hTnormcard :
        Nat.card (Subgroup.normalizer (T : Set (PSL2MatrixGroup K))) =
          2 * Nat.card T := by
      calc
        Nat.card (Subgroup.normalizer (T : Set (PSL2MatrixGroup K))) =
            Nat.card ((Subgroup.normalizer (U0 : Set (PSL2MatrixGroup K))).map
              (MulAut.conj b).toMonoidHom) := by
          rw [hTmap, Subgroup.map_equiv_normalizer_eq]
        _ = Nat.card (Subgroup.normalizer (U0 : Set (PSL2MatrixGroup K))) := by
          rw [Subgroup.card_map_of_injective (K :=
            Subgroup.normalizer (U0 : Set (PSL2MatrixGroup K)))
            (f := (MulAut.conj b).toMonoidHom) (MulAut.conj b).injective]
        _ = 2 * Nat.card U0 := hU0normalizer U0 le_rfl hU0ne
        _ = 2 * Nat.card T := by
          rw [hg, Subgroup.card_map_of_injective (K := U)
            (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
          rw [hU0card, hUcard]
    have hRodd : Odd (Nat.card (R : Subgroup (PSL2MatrixGroup K))) := by
      rw [hk]
      exact (hrFact.out.odd_of_ne_two hrne).pow
    have hTcyclic : IsCyclic T := by
      rw [hg]
      exact (MulEquiv.subgroupMap (MulAut.conj g) U).isCyclic.mp hUc
    letI : IsCyclic T := hTcyclic
    exact Subgroup.isCyclic_of_le
      (BenderSuzuki.lemma114_odd_subgroup_le_of_normalizer_card_two hRnorm hRodd hTnormcard)

  · rcases hTS with ⟨g, hg⟩
    have hRnorm : (R : Subgroup (PSL2MatrixGroup K)) ≤
        Subgroup.normalizer (T : Set (PSL2MatrixGroup K)) := by
      apply subgroup_le_normalizer_of_conj_mem T (R : Subgroup _)
      intro x hx hh
      let Tconj : Subgroup (PSL2MatrixGroup K) :=
        T.map ((MulAut.conj (x : PSL2MatrixGroup K)).toMonoidHom)
      have hTconjEq : Tconj = T := by
        apply hTuniq
        refine ⟨?_, ?_⟩
        · change (z : PSL2MatrixGroup K) ∈
            T.map ((MulAut.conj (x : PSL2MatrixGroup K)).toMonoidHom)
          rw [Subgroup.mem_map]
          refine ⟨(z : PSL2MatrixGroup K), hzT.1, ?_⟩
          change (x : PSL2MatrixGroup K) * (z : _) *
              (x : PSL2MatrixGroup K)⁻¹ = (z : _)
          have hcz := hzcR x
          calc
            (x : PSL2MatrixGroup K) * (z : _) *
                (x : PSL2MatrixGroup K)⁻¹ =
                ((z : _) * (x : PSL2MatrixGroup K)) *
                  (x : PSL2MatrixGroup K)⁻¹ := by rw [hcz.symm]
            _ = (z : _) := by simp [mul_assoc]
        · simpa [Tconj, Family] using hfamily_map T (x : PSL2MatrixGroup K) (by
            right; right; exact ⟨g, hg⟩)
      have hmap : (x : PSL2MatrixGroup K) * hx *
          (x : PSL2MatrixGroup K)⁻¹ ∈ Tconj := by
        change (x : PSL2MatrixGroup K) * hx *
            (x : PSL2MatrixGroup K)⁻¹ ∈
          T.map ((MulAut.conj (x : PSL2MatrixGroup K)).toMonoidHom)
        rw [Subgroup.mem_map]
        exact ⟨hx, hh, rfl⟩
      rw [hTconjEq] at hmap
      exact hmap
    obtain ⟨S0, hS0cyclic, hS0card, hS0normalizer⟩ :=
      BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_normalizer_card
        (F := K) (p := p) (f := f) hKcard
    have hS0card_gt : 1 < Nat.card S0 := by
      have hgcdpos : 0 < Nat.gcd (Nat.card K - 1) 2 :=
        Nat.gcd_pos_of_pos_right _ (by norm_num)
      have hgcdle : Nat.gcd (Nat.card K - 1) 2 ≤ 2 :=
        Nat.gcd_le_right _ (by norm_num)
      rw [hS0card]
      have hfour : 4 ≤
          (Nat.card K + 1) / Nat.gcd (Nat.card K - 1) 2 := by
        apply (Nat.le_div_iff_mul_le hgcdpos).2
        omega
      omega
    have hS0ne : S0 ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot]
      exact hS0card_gt
    have hS0align : ∃ a : PSL2MatrixGroup K,
        S0 = S.map (MulAut.conj a).toMonoidHom := by
      obtain ⟨u, hu_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS0ne
      have huG : (u : PSL2MatrixGroup K) ≠ 1 := by
        intro hu
        apply hu_ne
        apply Subtype.ext
        exact hu
      obtain ⟨T0, huT0, hT0uniq⟩ := hpart (u : PSL2MatrixGroup K) huG
      have hS0leT0 : S0 ≤ T0 :=
          BenderSuzuki.lemma114_cyclic_le_unique_partition_family Family
          hpartitionFamily huG huT0.1 (by simpa [Family] using huT0.2)
          u.property hS0cyclic
      rcases huT0.2 with hT0P | hT0U | hT0S
      · exfalso
        rcases hT0P with ⟨g, hg⟩
        have hcop : Nat.Coprime (Nat.card S0) (Nat.card T0) := by
          rw [hg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective]
          rw [hS0card, hP0card]
          exact (BenderSuzuki.lemma114_q_coprime_nonsplit_order
            (Nat.card K) Nat.card_pos).symm
        exact huG (BenderSuzuki.lemma114_mem_eq_one_of_coprime_card S0 T0 hcop
          u.property (hS0leT0 u.property))
      · exfalso
        rcases hT0U with ⟨g, hg⟩
        have hcop : Nat.Coprime (Nat.card S0) (Nat.card T0) := by
          rw [hg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective]
          rw [hS0card, hUcard]
          exact (BenderSuzuki.lemma114_split_nonsplit_order_coprime
            (Nat.card K) (Finite.one_lt_card (α := K))).symm
        exact huG (BenderSuzuki.lemma114_mem_eq_one_of_coprime_card S0 T0 hcop
          u.property (hS0leT0 u.property))
      · rcases hT0S with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        calc
          S0 = T0 := Subgroup.eq_of_le_of_card_ge hS0leT0 (by
            rw [ha, Subgroup.card_map_of_injective
              (MulAut.conj a).injective, hS0card, hScard])
          _ = S.map (MulAut.conj a).toMonoidHom := ha
    obtain ⟨a, ha⟩ := hS0align
    let b : PSL2MatrixGroup K := g * a⁻¹
    have hTmap : T = S0.map (MulAut.conj b).toMonoidHom := by
      have heq :
          (MulEquiv.toMonoidHom (MulAut.conj b)).comp
              (MulEquiv.toMonoidHom (MulAut.conj a)) =
            MulEquiv.toMonoidHom (MulAut.conj g) := by
        apply MonoidHom.ext
        intro x
        change b * (a * x * a⁻¹) * b⁻¹ = g * x * g⁻¹
        have hb_inv : b⁻¹ = a * g⁻¹ := by
          dsimp [b]
          rw [mul_inv_rev, inv_inv]
        rw [hb_inv]
        rw [show b = g * a⁻¹ by rfl]
        simp only [mul_assoc]
        rw [@inv_mul_cancel_left (PSL2MatrixGroup K) _]
        rw [@inv_mul_cancel_left (PSL2MatrixGroup K) _]
      rw [hg, ha, Subgroup.map_map, heq]
    have hTnormcard :
        Nat.card (Subgroup.normalizer (T : Set (PSL2MatrixGroup K))) =
          2 * Nat.card T := by
      calc
        Nat.card (Subgroup.normalizer (T : Set (PSL2MatrixGroup K))) =
            Nat.card ((Subgroup.normalizer (S0 : Set (PSL2MatrixGroup K))).map
              (MulAut.conj b).toMonoidHom) := by
          rw [hTmap, Subgroup.map_equiv_normalizer_eq]
        _ = Nat.card (Subgroup.normalizer (S0 : Set (PSL2MatrixGroup K))) := by
          rw [Subgroup.card_map_of_injective (K :=
            Subgroup.normalizer (S0 : Set (PSL2MatrixGroup K)))
            (f := (MulAut.conj b).toMonoidHom) (MulAut.conj b).injective]
        _ = 2 * Nat.card S0 := hS0normalizer
        _ = 2 * Nat.card T := by
          rw [hg, Subgroup.card_map_of_injective (K := S)
            (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
          rw [hS0card, hScard]
    have hRodd : Odd (Nat.card (R : Subgroup (PSL2MatrixGroup K))) := by
      rw [hk]
      exact (hrFact.out.odd_of_ne_two hrne).pow
    have hTcyclic : IsCyclic T := by
      rw [hg]
      exact (MulEquiv.subgroupMap (MulAut.conj g) S).isCyclic.mp hSc
    letI : IsCyclic T := hTcyclic
    exact Subgroup.isCyclic_of_le
      (BenderSuzuki.lemma114_odd_subgroup_le_of_normalizer_card_two hRnorm hRodd hTnormcard)


end CFSG.GorensteinWalter
