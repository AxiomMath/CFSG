module

public import CFSG.Quasithin.Background.F6CatRecogInputs2
public import CFSG.Milestones.LR_Brauer_Suzuki_central_involution
public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.Walter.Models
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Milestones.LR_dihedral_simple_recognition
public import CFSG.Quasithin.Background.F6CatRecogSetting
public import CFSG.Walter.J1.Local
public import CFSG.Walter.J1Props.Hyp

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace F6

section Models

@[expose] def wreathEquiv : Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2) ≃
    (Multiplicative (ZMod 2) → Multiplicative (ZMod 4)) × Multiplicative (ZMod 2) where
  toFun x := (x.left, x.right)
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : DecidableEq (Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2)) :=
  wreathEquiv.decidableEq

instance : Fintype (Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2)) :=
  Fintype.ofEquiv _ wreathEquiv.symm

theorem card_sq_eq_one_wreath :
    (Finset.univ.filter fun x : Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2) =>
      x * x = 1).card = 8 := by
  decide

theorem exists_noncomm_sq_eq_one_wreath :
    ¬ ∀ x y : Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2),
      x * x = 1 → y * y = 1 → x * y = y * x := by
  decide

theorem z2_dihedral_pow_four :
    ∀ x : Multiplicative (ZMod 2) × DihedralGroup 4, x ^ 4 = 1 := by
  decide

theorem card_sq_ne_one_z2_dihedral :
    (Finset.univ.filter fun x : Multiplicative (ZMod 2) × DihedralGroup 4 => x * x ≠ 1).card =
      4 := by
  decide

theorem card_sq_ne_one_quaternion :
    (Finset.univ.filter fun x : QuaternionGroup 2 => x * x ≠ 1).card = 6 := by
  decide

theorem dihedral_eight_pow_four : (DihedralGroup.r (1 : ZMod 8)) ^ 4 ≠ 1 := by
  decide

theorem card_le_four_of_le_wreath (H : Subgroup (Multiplicative (ZMod 4) ≀ᵣ
      Multiplicative (ZMod 2))) (hsq : ∀ x ∈ H, x * x = 1)
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) : Nat.card H ≤ 4 := by
  classical
  set W := Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2)
  have hsub : (H : Set W).toFinset ⊆ Finset.univ.filter fun x : W => x * x = 1 := by
    intro x hx
    simp only [Set.mem_toFinset, SetLike.mem_coe] at hx
    simp [hsq x hx]
  have hcard : Nat.card H = (H : Set W).toFinset.card := by
    rw [Set.toFinset_card, Nat.card_eq_fintype_card]
    rfl
  have h8 : Nat.card H ≤ 8 := by
    rw [hcard, ← card_sq_eq_one_wreath]
    exact Finset.card_le_card hsub
  have hdvd : Nat.card H ∣ 2 ^ 5 := by
    have h32 : Nat.card W = 2 ^ 5 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [← h32]
    exact Subgroup.card_subgroup_dvd_card H
  obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hie] at h8 ⊢
  have hi3 : i ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases i
  · norm_num
  · norm_num
  · norm_num
  · exfalso
    have heq : (H : Set W).toFinset = Finset.univ.filter fun x : W => x * x = 1 :=
      Finset.eq_of_subset_of_card_le hsub (by rw [card_sq_eq_one_wreath, ← hcard, hie]; norm_num)
    apply exists_noncomm_sq_eq_one_wreath
    intro x y hx hy
    have hx' : x ∈ (H : Set W).toFinset := heq ▸ by simp [hx]
    have hy' : y ∈ (H : Set W).toFinset := heq ▸ by simp [hy]
    simp only [Set.mem_toFinset, SetLike.mem_coe] at hx' hy'
    exact hcomm x hx' y hy'

end Models

section SylowIso

theorem exists_sylow_mulEquiv_of_mulEquiv {A B : Type*} [Group A] [Finite A] [Group B] (ψ : A ≃* B)
    (Q : Sylow 2 A) :
    ∃ Q' : Sylow 2 B, Nonempty (↥(Q : Subgroup A) ≃* ↥(Q' : Subgroup B)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Q.mapSurjective (f := ψ.toMonoidHom) ψ.surjective, ⟨?_⟩⟩
  exact ((Q : Subgroup A).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
    (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _).symm)

theorem nonempty_sylow_mulEquiv {A : Type*} [Group A] [Finite A] (Q Q' : Sylow 2 A) :
    Nonempty (↥(Q : Subgroup A) ≃* ↥(Q' : Subgroup A)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ⟨Sylow.equiv Q Q'⟩

end SylowIso

section Quaternion

theorem false_of_sylow_quaternion {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (Q : Sylow 2 G)
    (e : ↥(Q : Subgroup G) ≃* QuaternionGroup 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t : G := ((e.symm (QuaternionGroup.a 2) : ↥(Q : Subgroup G)) : G) with ht
  have htQ : t ∈ (Q : Subgroup G) := (e.symm (QuaternionGroup.a 2)).2
  have hord : orderOf t = 2 := by
    rw [ht, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by decide) (by decide)
  have hcen := CFSG.Milestones.brauer_suzuki 3 le_rfl Q
    ⟨by rw [show (2 : ℕ) ^ (3 - 2) = 2 by norm_num]; exact e⟩ t htQ hord
  have hodd : CFSG.oddCore G = ⊥ := by
    refine sSup_eq_bot.mpr fun N ⟨hN, hNodd⟩ => ?_
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hNodd
      have h2 : 2 ∣ Nat.card G := by
        have := Subgroup.orderOf_dvd_natCard ⊤ (Subgroup.mem_top t)
        rw [hord, Subgroup.card_top] at this
        exact this
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have ht1 : t ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hodd,
      Subgroup.mem_bot] at h1
    calc g * t = (g * t) * ((g * t)⁻¹ * (t * g)) := by rw [h1, mul_one]
      _ = t * g := by group
  rw [hZ, Subgroup.mem_bot] at ht1
  rw [ht1, orderOf_one] at hord
  norm_num at hord

end Quaternion

section Walter

variable {D : Type} [Group D] [Finite D]

theorem forall_mul_self_of_mulEquiv {A B : Type*} [Group A] [Group B] {P : Subgroup A}
    {P' : Subgroup B} (ι : ↥P ≃* ↥P') (h : ∀ x ∈ P', x * x = 1) : ∀ x ∈ P, x * x = 1 := by
  intro x hx
  have h1 := h _ (ι ⟨x, hx⟩).2
  have h2 : ι (⟨x, hx⟩ * ⟨x, hx⟩) = ι 1 := by
    rw [map_mul, map_one]
    exact Subtype.ext h1
  simpa using congrArg Subtype.val (ι.injective h2)

theorem walter_cases
    (hW : WalterModelsStatement) (hS : F618RecogSettingSQT D)
    (Q : Sylow 2 (TwoResidualQuot D)) (hab : IsMulCommutative (Q : Subgroup (TwoResidualQuot D))) :
    (∀ x ∈ (Q : Subgroup (TwoResidualQuot D)), x * x = 1) ∧
    (Nat.card (Q : Subgroup (TwoResidualQuot D)) = 8 →
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 8 ∧
        Nonempty (TwoResidualQuot D ≃* StatedProj (StatedSL 2 K))) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (TwoResidualQuot D) .J1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (TwoResidualQuot D) := hS.quasisimple.2.1
  have hnonab : ∃ a b : TwoResidualQuot D, a * b ≠ b * a := hS.quasisimple.2.2
  rcases hW (TwoResidualQuot D) hnonab Q hab with ⟨f, hf, hm⟩ | ⟨p, f, hp, hp2, -, -, h8, hm⟩ |
      ⟨f, -, hf3, hm⟩ | hJ
  ·
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
    let ε := eK.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv_of_mulEquiv ε Q
    obtain ⟨e⟩ := CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hK Q'
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    have hsq : ∀ x ∈ (Q' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)),
        x * x = 1 := by
      intro x hx
      obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
      have h1 : a * a = 1 := by
        change Multiplicative.ofAdd (a.toAdd + a.toAdd) = Multiplicative.ofAdd 0
        rw [CharTwo.add_self_eq_zero]
      have h2 := congrArg Subtype.val (congrArg e h1)
      rw [map_mul, map_one, ha] at h2
      exact h2
    refine ⟨forall_mul_self_of_mulEquiv ι hsq, fun h8 => Or.inl ⟨K, inferInstance, inferInstance,
      ?_, ⟨eK⟩⟩⟩
    have h1 : Nat.card (Q : Subgroup (TwoResidualQuot D)) = Nat.card K := by
      rw [Nat.card_congr ι.toEquiv, ← Nat.card_congr e.toEquiv]
      rfl
    rw [← h1, h8]
  ·
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
    have hcard := card_twoResidualQuot hp hp2 hK eK
    have hn8 : ¬ 8 ∣ Nat.card (Q : Subgroup (TwoResidualQuot D)) := fun h => by
      exact not_eight_dvd_card_psl_two h8 (hcard ▸ h.trans (Subgroup.card_subgroup_dvd_card _))
    have h4 := (not_isCyclic_sylow_two hnonab Q).2
    obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
    have hQ4 : Nat.card (Q : Subgroup (TwoResidualQuot D)) = 4 := by
      rw [hk] at h4 hn8 ⊢
      have hk2 : 2 ≤ k := by
        by_contra h
        interval_cases k <;> norm_num at h4
      have hk3 : k < 3 := by
        by_contra h
        exact hn8 (by
          obtain ⟨j, rfl⟩ : ∃ j, k = 3 + j := ⟨k - 3, by omega⟩
          rw [pow_add]
          exact Dvd.intro _ rfl)
      interval_cases k
      rfl
    have : IsKleinFour (Q : Subgroup (TwoResidualQuot D)) :=
      isKleinFour_of_card_four hQ4 (not_isCyclic_sylow_two hnonab Q).1
    refine ⟨fun x hx => congrArg Subtype.val (IsKleinFour.mul_self ⟨x, hx⟩), fun h => ?_⟩
    omega
  ·
    exfalso
    have hree : CFSG.Blueprint.ReeTitsModel (TwoResidualQuot D) .twistedG2 3 f := by
      rcases hm with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h
      · exact absurd h (by decide)
    obtain ⟨-, -, h2f⟩ := CFSG.SectionRank.smallReeModel_rank hree
    have h3 := (CFSG.SectionRank.isStronglyQuasithin_iff.mp hS.sqt) 3 Nat.prime_three
      (by norm_num)
    omega
  ·
    obtain ⟨eJ⟩ := hJ
    let ε : TwoResidualQuot D ≃* CFSG.Open.walterJ1 := eJ.trans CFSG.Walter.walterJ1EquivNative.symm
    obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv_of_mulEquiv ε Q
    obtain ⟨-, hsq, -, -⟩ := CFSG.Walter.J1Props.jankoHyp.sylow_structure Q'
    exact ⟨forall_mul_self_of_mulEquiv ι hsq, fun _ => Or.inr ⟨eJ⟩⟩

end Walter

section Dihedral

variable {D : Type} [Group D] [Finite D]

theorem psl_two_or_alternating_seven_of_dihedral
    (hS : F618RecogSettingSQT D) (S : Sylow 2 D)
    (hP : Nonempty (↥((S : Subgroup D) ⊓ twoResidual ⊤) ≃* DihedralGroup 4)) :
    (∃ (p e : ℕ) (K : Type) (_ : Field K) (_ : Finite K), p.Prime ∧ p ≠ 2 ∧ 1 ≤ e ∧ e ≤ 2 ∧
      (p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) ∧ StatedLieAdmissible .PSL 2 p e ∧
      Nat.card K = p ^ e ∧ Nonempty (TwoResidualQuot D ≃* StatedProj (StatedSL 2 K)) ∧
      (p ^ e ≠ 9 → Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥) ∧
      (Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥ ∨
        Nat.card (Subgroup.center ↥(twoResidual (⊤ : Subgroup D))) = 3)) ∨
    (Nonempty (TwoResidualQuot D ≃* ↥(alternatingGroup (Fin 7))) ∧
      (Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥ ∨
        Nat.card (Subgroup.center ↥(twoResidual (⊤ : Subgroup D))) = 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eP⟩ := hP
  have : IsSimpleGroup (TwoResidualQuot D) := hS.quasisimple.2.1
  have hnonab : ∃ a b : TwoResidualQuot D, a * b ≠ b * a := hS.quasisimple.2.2
  have : Group.IsPerfect ↥(twoResidual (⊤ : Subgroup D)) := hS.quasisimple.1
  obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_quotient_of_setting hS.toF618RecogSetting S
  have hQ8 : Nat.card (Q : Subgroup (TwoResidualQuot D)) = 8 := by
    rw [← Nat.card_congr eQ.toEquiv, Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
  have eQ' : Nonempty ((Q : Subgroup (TwoResidualQuot D)) ≃* DihedralGroup (2 ^ (3 - 1))) := by
    rw [show (2 : ℕ) ^ (3 - 1) = 4 by norm_num]
    exact ⟨eQ.symm.trans eP⟩
  rcases CFSG.Milestones.lr_dihedral_simple_recognition (TwoResidualQuot D) hnonab Q 3
      (by norm_num) eQ' with ⟨p, f, hp, hp2, hf, hadm, K, _, _, hK, ⟨eK⟩⟩ | he7
  · have : Fact p.Prime := ⟨hp⟩
    have hcard := card_twoResidualQuot hp hp2 hK eK
    have hQd : 8 ∣ p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
      rw [← hcard, ← hQ8]
      exact Subgroup.card_subgroup_dvd_card _
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h16 : p ^ f % 16 = 7 ∨ p ^ f % 16 = 9 := by
      by_contra hne
      have hc : (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∨ (p ^ f % 16 = 1 ∨ p ^ f % 16 = 15) := by
        obtain ⟨m, hm⟩ := hodd
        omega
      rcases hc with hc | hc
      · exact not_eight_dvd_card_psl_two hc hQd
      · have h := sixteen_dvd_card_psl_two hc
        rw [← hcard] at h
        have h' := Sylow.pow_dvd_card_of_pow_dvd_card (P := Q) (n := 4) (by simpa using h)
        rw [hQ8] at h'
        norm_num at h'
    have hf2 := le_two_of_isStronglyQuasithin hS.sqt hp hp2 hK eK
    obtain ⟨hZ1, hZ9⟩ := center_of_quotient_psl_two hS.center hp2 hK eK
    refine Or.inl ⟨p, f, K, inferInstance, inferInstance, hp, hp2, hf, hf2, h16, hadm, hK,
      ⟨eK⟩, hZ1, ?_⟩
    by_cases h9 : p ^ f = 9
    · exact card_center_eq_one_or_three hS.toF618RecogSetting (hZ9 h9)
    · exact Or.inl (hZ1 h9)
  · obtain ⟨e7⟩ := he7
    exact Or.inr ⟨⟨e7⟩, card_center_eq_one_or_three hS.toF618RecogSetting
      (card_center_le_three_of_alternating_seven hS.center e7)⟩

end Dihedral

end F6

end CFSG.Quasithin
