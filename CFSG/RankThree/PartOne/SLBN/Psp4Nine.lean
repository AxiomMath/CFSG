module

public import CFSG.RankThree.PartOne.SLBN.Core
public import CFSG.RankThree.PartOne.SLBN.LocalCover
public import CFSG.RankThree.PartOne.SLBN.Psp4Closure
public import CFSG.RankThree.PartOne.SLBN.Quintuple
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.RankThree.PartOne.SLBN.OddSum

public section

namespace CFSG.RankThree.PartOne.SLBN

open Subgroup Matrix CFSG CFSG.RankThree.PartOne.SRC CFSG.SL2MinimalFaithful
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

theorem eq_one_of_sq_eq_one_of_pow_five {G : Type*} [Group G] {y : G} (h2 : y ^ 2 = 1)
    (h5 : y ^ 5 = 1) : y = 1 := by
  calc y = y ^ 5 * (y ^ 2)⁻¹ * (y ^ 2)⁻¹ := by group
    _ = 1 := by rw [h5, h2]; simp

variable {K : Type} [Field K]

@[expose] noncomputable def psp4Iota : SL(2, K) × SL(2, K) →* StatedProj (StatedSp 2 K) :=
  (sp4Emb0 (K := K)).noncommCoprod (sp4Emb (K := K))
    (fun a b => (sp4Emb_comm_sp4Emb0 b a).symm)

theorem psp4Iota_apply (x : SL(2, K) × SL(2, K)) : psp4Iota x = sp4Emb0 x.1 * sp4Emb x.2 := rfl

theorem psp4Iota_ker (A : SL(2, K) × SL(2, K)) (h : psp4Iota A = 1) : A ^ 2 = 1 := by
  obtain ⟨a, b⟩ := A
  have h' : sp4Emb0 a * sp4Emb b = 1 := h
  have hmul : sp4Emb0 a = (sp4Emb b)⁻¹ := eq_inv_of_mul_eq_one_left h'
  have hmul' : sp4Emb b = (sp4Emb0 a)⁻¹ := eq_inv_of_mul_eq_one_right h'
  have ha : a ∈ Subgroup.center SL(2, K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply sp4Emb0_injective (K := K)
    rw [map_mul, map_mul, hmul]
    exact ((show Commute (sp4Emb0 g) (sp4Emb b) from
      (sp4Emb_comm_sp4Emb0 b g).symm).inv_right).eq
  have hb : b ∈ Subgroup.center SL(2, K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply sp4Emb_injective (K := K)
    rw [map_mul, map_mul, hmul']
    exact ((show Commute (sp4Emb g) (sp4Emb0 a) from sp4Emb_comm_sp4Emb0 g a).inv_right).eq
  exact Prod.ext (sq_eq_one_of_mem_center_SL2 ha) (sq_eq_one_of_mem_center_SL2 hb)

theorem psp4Iota_comm (h2 : (2 : K) ≠ 0) (g : SL(2, K) × SL(2, K)) :
    psp4Iota g * sp4Invol0 = sp4Invol0 * psp4Iota g := by
  obtain ⟨a, b⟩ := g
  show sp4Emb0 a * sp4Emb b * sp4Invol0 = sp4Invol0 * (sp4Emb0 a * sp4Emb b)
  calc sp4Emb0 a * sp4Emb b * sp4Invol0 = sp4Emb0 a * (sp4Emb b * sp4Invol0) := by rw [mul_assoc]
    _ = sp4Emb0 a * (sp4Invol0 * sp4Emb b) := by rw [sp4Emb_comm0 b h2]
    _ = (sp4Emb0 a * sp4Invol0) * sp4Emb b := by rw [mul_assoc]
    _ = (sp4Invol0 * sp4Emb0 a) * sp4Emb b := by rw [sp4Emb0_comm a h2]
    _ = sp4Invol0 * (sp4Emb0 a * sp4Emb b) := by rw [mul_assoc]

section Finite

variable [Finite K] (hK : Nat.card K = 9)
include hK

theorem charP_three_of_card_nine' : CharP K 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 3) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)

theorem two_ne_zero_of_card_nine : (2 : K) ≠ 0 := by
  have := charP_three_of_card_nine' hK
  exact Ring.two_ne_zero (by rw [ringChar.eq K 3]; norm_num)

theorem hasPair_psp4_nine : HasPair 3 (StatedProj (StatedSp 2 K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := charP_three_of_card_nine' hK
  have h2 := two_ne_zero_of_card_nine hK
  let u : Multiplicative K × Multiplicative K →* StatedProj (StatedSp 2 K) :=
    psp4Iota.comp (unipotentHom.prodMap unipotentHom)
  have hpow : ∀ a : Multiplicative K × Multiplicative K, a ^ 3 = 1 := by
    intro a
    refine Prod.ext ?_ ?_
    · apply Multiplicative.toAdd.injective
      rw [Prod.pow_fst, Prod.fst_one, toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    · apply Multiplicative.toAdd.injective
      rw [Prod.pow_snd, Prod.snd_one, toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hinj : Function.Injective u := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hsq : (unipotentHom.prodMap unipotentHom a) ^ 2 = 1 := psp4Iota_ker _ ha
    have hcu : (unipotentHom.prodMap unipotentHom a) ^ 3 = 1 := by
      rw [← map_pow, hpow, map_one]
    have h1 : unipotentHom.prodMap unipotentHom a = 1 := by
      have : unipotentHom.prodMap unipotentHom a =
          (unipotentHom.prodMap unipotentHom a) ^ 3 *
            ((unipotentHom.prodMap unipotentHom a) ^ 2)⁻¹ := by group
      rw [this, hcu, hsq]; simp
    have e1 : unipotentHom a.1 = 1 := (Prod.ext_iff.mp h1).1
    have e2 : unipotentHom a.2 = 1 := (Prod.ext_iff.mp h1).2
    exact Prod.ext (unipotentHom_injective (e1.trans (map_one unipotentHom).symm))
      (unipotentHom_injective (e2.trans (map_one unipotentHom).symm))
  have hE : IsElementaryAbelian 3 u.range := CFSG.RankThree.PartOne.SRC.isElementaryAbelian_range u hpow
  have hcard : Nat.card u.range = 3 ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]
    have : Nat.card (Multiplicative K) = 9 := by
      rw [← hK]; exact Nat.card_congr Multiplicative.toAdd
    rw [this]; norm_num
  have hb2 : orderOf (sp4Invol0 : StatedProj (StatedSp 2 K)) = 2 := orderOf_sp4Invol0 h2
  refine hasPair_of_centralizer hb2 hE (k := 4) le_rfl hcard ?_
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact psp4Iota_comm h2 _

theorem exists_subgroup_card_25 : ∃ P : Subgroup (StatedProj (StatedSp 2 K)), Nat.card P = 25 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ := sl2_quasisimple_nine hK
  have := hQ.1
  have hker : IsPGroup 3 (MonoidHom.id SL(2, K)).ker := by
    rw [MonoidHom.ker_id]
    exact IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨h, h5, -⟩ := exists_five_noncentral_nine (MonoidHom.id SL(2, K)) hK
    Function.surjective_id hker
  have hh5 : h ^ 5 = 1 := by rw [← h5]; exact pow_orderOf_eq_one h
  set a : StatedProj (StatedSp 2 K) := sp4Emb0 h with ha
  set c : StatedProj (StatedSp 2 K) := sp4Emb h with hc
  have ha5 : orderOf a = 5 := by
    rw [ha, orderOf_injective sp4Emb0 (sp4Emb0_injective (K := K)) h, h5]
  have hc5 : orderOf c = 5 := by
    rw [hc, orderOf_injective sp4Emb (sp4Emb_injective (K := K)) h, h5]
  have hac : Commute a c := (sp4Emb_comm_sp4Emb0 h h).symm
  have ha5' : a ^ 5 = 1 := by rw [← ha5]; exact pow_orderOf_eq_one a
  have hc5' : c ^ 5 = 1 := by rw [← hc5]; exact pow_orderOf_eq_one c
  obtain ⟨E, hE, hcardE, -⟩ := exists_isElementaryAbelian_sup (p := 5)
    (A := Subgroup.zpowers a) (B := Subgroup.zpowers c)
    (IsElementaryAbelian.zpowers_of_pow_eq_one ha5') (IsElementaryAbelian.zpowers_of_pow_eq_one hc5')
    (fun x hx y hy => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hac.zpow_zpow i j).eq)
    (fun x hx hy => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h1 : psp4Iota (h ^ i, (h ^ j)⁻¹) = 1 := by
        rw [psp4Iota_apply]
        have e1 : sp4Emb0 (h ^ i) = a ^ i := by rw [ha, map_zpow]
        have e2 : sp4Emb (h ^ j) = c ^ j := by rw [hc, map_zpow]
        show sp4Emb0 (h ^ i) * sp4Emb (h ^ j)⁻¹ = 1
        rw [map_inv, e1, e2, hj]
        exact mul_inv_cancel _
      have h2 := psp4Iota_ker _ h1
      have hsq : (h ^ i) ^ 2 = 1 := (Prod.ext_iff.mp h2).1
      have h5i : (h ^ i) ^ 5 = 1 := by
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hh5,
          _root_.one_zpow]
      have : h ^ i = 1 := eq_one_of_sq_eq_one_of_pow_five hsq h5i
      rw [show a ^ i = sp4Emb0 (h ^ i) by rw [ha, map_zpow], this, map_one])
  refine ⟨E, ?_⟩
  rw [hcardE, Nat.card_zpowers, Nat.card_zpowers, ha5, hc5]

theorem isPerfect_psp4_nine : Group.IsPerfect (StatedProj (StatedSp 2 K)) := by
  have hsimple : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr (by omega)))
  obtain ⟨P, hP⟩ := exists_subgroup_card_25 hK
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (commutator (StatedProj (StatedSp 2 K))) with h | h
  · exfalso
    have hcomm : IsMulCommutative (StatedProj (StatedSp 2 K)) := by
      refine ⟨⟨fun x y => ?_⟩⟩
      have : ⁅x, y⁆ ∈ commutator (StatedProj (StatedSp 2 K)) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [h, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    have hprime := IsSimpleGroup.prime_card (α := StatedProj (StatedSp 2 K))
    have hd : 25 ∣ Nat.card (StatedProj (StatedSp 2 K)) := hP ▸ Subgroup.card_subgroup_dvd_card P
    obtain ⟨m, hm⟩ := hd
    rw [hm] at hprime
    have := Nat.prime_mul_iff.mp hprime
    norm_num at this
  · exact h

theorem rankFourCover_psp4_nine : RankFourCover 3 (StatedProj (StatedSp 2 K)) := by
  have hsimple : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr (by omega)))
  have : CharP K 3 := charP_three_of_card_nine' hK
  have h2 := two_ne_zero_of_card_nine hK
  obtain ⟨P, hP⟩ := exists_subgroup_card_25 hK
  obtain ⟨g₂, g₃, g₄, g₅, hprod⟩ := exists_quintuple_psp4 (K := K)
  let g : Fin 5 → StatedProj (StatedSp 2 K) := ![1, g₂, g₃, g₄, g₅]
  let b : Fin 5 → StatedProj (StatedSp 2 K) := fun i => g i * sp4Invol0 * (g i)⁻¹
  let ι : Fin 5 → SL(2, K) × SL(2, K) →* StatedProj (StatedSp 2 K) := fun i =>
    (MulAut.conj (g i)).toMonoidHom.comp psp4Iota
  have hb2 : ∀ i, orderOf (b i) = 2 := fun i => by
    show orderOf (MulAut.conj (g i) sp4Invol0) = 2
    rw [MulEquiv.orderOf_eq]
    exact orderOf_sp4Invol0 h2
  have hιker : ∀ i A, ι i A = 1 → A ^ 2 = 1 := fun i A h => by
    apply psp4Iota_ker
    have : (MulAut.conj (g i)) (psp4Iota A) = 1 := h
    exact (map_eq_one_iff _ (MulAut.conj (g i)).injective).1 this
  have hιc : ∀ i x, ι i x * b i = b i * ι i x := fun i x => by
    show (MulAut.conj (g i)) (psp4Iota x) * (MulAut.conj (g i)) sp4Invol0 =
      (MulAut.conj (g i)) sp4Invol0 * (MulAut.conj (g i)) (psp4Iota x)
    rw [← map_mul, ← map_mul, psp4Iota_comm h2]
  have hb0 : b 0 = sp4Invol0 := by simp [b, g]
  have hbprod : b 0 * b 1 * b 2 * b 3 * b 4 = 1 := by
    rw [hb0]
    exact hprod
  refine rankFourCover_nine_core (isPerfect_psp4_nine hK)
    (fun Y _ _ φ hφ hker hcen hmin => ker_eq_bot_of_central_psp (by omega) φ hφ hmin hker hcen)
    P hP (fun Q _ _ ρ hρ hker hrank => isCyclic_ker_of_cover_sl2_sq hK ρ hρ hker hrank)
    b ι hb2 hιker hιc ?_ (hasPair_psp4_nine hK)
  intro V _ _ hpow ρ hfix
  have hsq : ∀ i, ρ (b i) * ρ (b i) = 1 := fun i => by
    have h1 : b i ^ 2 = 1 := by
      have h := pow_orderOf_eq_one (b i)
      rwa [hb2 i] at h
    rw [← map_mul, ← sq, h1, map_one]
  have hp : ρ (b 0) * ρ (b 1) * ρ (b 2) * ρ (b 3) * ρ (b 4) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hbprod, map_one]
  have := card_le_of_five_fixed hpow (ρ (b 0)) (ρ (b 1)) (ρ (b 2)) (ρ (b 3)) (ρ (b 4)) (hsq 0)
    (hsq 1) (hsq 2) (hsq 3) (hsq 4) hp (hfix 0) (hfix 1) (hfix 2) (hfix 3) (hfix 4)
  exact this.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))

end Finite

end CFSG.RankThree.PartOne.SLBN
