module

public import CFSG.Sporadic.Co2Schreier.Classes
public import CFSG.Sporadic.Co2Schreier.ThirdE
public import CFSG.GroupTheory.PCore.Defs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Sporadic.Co2Cert

theorem eq_bot_of_odd_normal {G : Type*} [Group G] [Finite G] {K M : Subgroup G} (hMK : M ≤ K)
    [hMn : (M.subgroupOf K).Normal] {m : ℕ} (hM : Nat.card M = 2 ^ m)
    (hC : K ⊓ Subgroup.centralizer (M : Set G) ≤ M) (N : Subgroup K) [hN : N.Normal]
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hM' : Nat.card (M.subgroupOf K) = 2 ^ m := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMK).toEquiv, hM]
  have hNM : N ⊓ M.subgroupOf K = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(N ⊓ M.subgroupOf K) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(N ⊓ M.subgroupOf K) ∣ 2 ^ m := hM' ▸ Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    have hodd' : Odd (Nat.card ↥(N ⊓ M.subgroupOf K)) := Odd.of_dvd_nat hodd h1
    rw [hk'] at hodd' ⊢
    rcases k with _ | k
    · rfl
    · exact absurd hodd' (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, k.succ_ne_zero⟩))
  refine eq_bot_iff.2 fun n hn => ?_
  have hcomm : ∀ q ∈ M.subgroupOf K, n * q = q * n := by
    intro q hq
    have hc : n * q * n⁻¹ * q⁻¹ ∈ N ⊓ M.subgroupOf K := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [mul_assoc, mul_assoc]
        refine N.mul_mem hn ?_
        rw [← mul_assoc]
        exact hN.conj_mem _ (N.inv_mem hn) q
      · exact (M.subgroupOf K).mul_mem (hMn.conj_mem q hq n) ((M.subgroupOf K).inv_mem hq)
    rw [hNM, Subgroup.mem_bot] at hc
    have := mul_inv_eq_one.1 hc
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hmem : ((n : K) : G) ∈ K ⊓ Subgroup.centralizer (M : Set G) := by
    refine Subgroup.mem_inf.2 ⟨(n : K).2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have h := hcomm ⟨g, hMK hg⟩ (Subgroup.mem_subgroupOf.2 hg)
    exact (congrArg Subtype.val h).symm
  have hnM : (n : K) ∈ M.subgroupOf K := Subgroup.mem_subgroupOf.2 (hC hmem)
  have h : n ∈ N ⊓ M.subgroupOf K := Subgroup.mem_inf.2 ⟨hn, hnM⟩
  rw [hNM, Subgroup.mem_bot] at h
  rw [h]
  exact Subgroup.one_mem _

theorem oddCore_eq_bot_of_forall {K : Type*} [Group K]
    (h : ∀ N : Subgroup K, N.Normal → Odd (Nat.card N) → N = ⊥) : CFSG.oddCore K = ⊥ :=
  sSup_eq_bot.2 fun N hN => h N hN.1 hN.2

theorem oddCore_bot_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.oddCore B = ⊥) : CFSG.oddCore A = ⊥ := by
  refine oddCore_eq_bot_of_forall fun N hN hodd => ?_
  have hN' : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
  have hcard : Nat.card (N.map e.toMonoidHom) = Nat.card N :=
    Subgroup.card_map_of_injective e.injective
  have hle : N.map e.toMonoidHom ≤ CFSG.oddCore B :=
    le_sSup ⟨hN', hcard ▸ hodd⟩
  rw [h, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hle
  exact hle

theorem oddCore_locC :
    CFSG.oddCore locC = ⊥ :=
  oddCore_eq_bot_of_forall fun N _ hodd =>
    eq_bot_of_odd_normal locQ_le_C (hMn := locQ_normal) (m := 9) (by rw [card_locQ]; norm_num)
      (by rw [locC_inf_centralizer_Q]; exact inf_le_left) N hodd

theorem oddCore_locD :
    CFSG.oddCore locD = ⊥ :=
  oddCore_eq_bot_of_forall fun N _ hodd =>
    eq_bot_of_odd_normal locR_le_D (hMn := locR_normal) (m := 11) (by rw [card_locR]; norm_num)
      (by rw [locD_inf_centralizer_R]; exact inf_le_left) N hodd

theorem oddCore_locH3 :
    CFSG.oddCore locH3 = ⊥ :=
  oddCore_eq_bot_of_forall fun N _ hodd =>
    eq_bot_of_odd_normal locQu_le_H3 (hMn := locQu_normal_H3) (m := 10)
      (by rw [card_locQu]; norm_num) (le_of_eq locH3_inf_centralizer_Qu) N hodd

theorem CTUC_Co2_third_centralizer_odd_normal_exclusion
    (N : Subgroup locH3) (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N = ⊥ :=
  eq_bot_of_odd_normal locQu_le_H3 (hMn := locQu_normal_H3) (m := 10)
    (by rw [card_locQu]; norm_num) (le_of_eq locH3_inf_centralizer_Qu) N (hN := hN) hodd

theorem centralizer_uP :
    Subgroup.centralizer ({uP} : Set co2P) = locH3.subgroupOf co2P := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, mem_locH3]
  constructor
  · intro h
    exact ⟨x.2, (congrArg Subtype.val h).symm⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext h.symm

theorem conj_mem_centralizer {G : Type*} [Group G] {c a x : G} (h : c * a * c⁻¹ = x) {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G)) :
    c * g * c⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← h]
  have hg' := Subgroup.mem_centralizer_singleton_iff.1 hg
  calc c * g * c⁻¹ * (c * a * c⁻¹) = c * (g * a) * c⁻¹ := by group
    _ = c * (a * g) * c⁻¹ := by rw [hg']
    _ = c * a * c⁻¹ * (c * g * c⁻¹) := by group

theorem conj_inv_mem_centralizer {G : Type*} [Group G] {c a x : G} (h : c * a * c⁻¹ = x) {g : G}
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) :
    c⁻¹ * g * c ∈ Subgroup.centralizer ({a} : Set G) := by
  have h' : c⁻¹ * x * c⁻¹⁻¹ = a := by rw [← h]; group
  have := conj_mem_centralizer h' hg
  rwa [inv_inv] at this

@[expose] def centralizerConj {G : Type*} [Group G] (c a x : G) (h : c * a * c⁻¹ = x) :
    Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({x} : Set G) where
  toFun g := ⟨c * g * c⁻¹, conj_mem_centralizer h g.2⟩
  invFun g := ⟨c⁻¹ * g * c, conj_inv_mem_centralizer h g.2⟩
  left_inv g := Subtype.ext (show c⁻¹ * (c * (g : G) * c⁻¹) * c = g by group)
  right_inv g := Subtype.ext (show c * (c⁻¹ * (g : G) * c) * c⁻¹ = g by group)
  map_mul' g g' := Subtype.ext (show c * ((g : G) * g') * c⁻¹ = (c * g * c⁻¹) * (c * g' * c⁻¹) by
    group)

theorem oddCore_centralizer_of_isConj {G : Type*} [Group G] {a x : G} (h : IsConj a x)
    (hx : CFSG.oddCore (Subgroup.centralizer ({x} : Set G)) = ⊥) :
    CFSG.oddCore (Subgroup.centralizer ({a} : Set G)) = ⊥ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact oddCore_bot_of_equiv (centralizerConj c a x hc) hx

theorem oddCore_centralizer_zP :
    CFSG.oddCore (Subgroup.centralizer ({zP} : Set co2P)) = ⊥ :=
  oddCore_bot_of_equiv ((MulEquiv.subgroupCongr locC_subgroupOf_eq.symm).trans
    (Subgroup.subgroupOfEquivOfLe locC_le_P)) oddCore_locC

theorem oddCore_centralizer_tP :
    CFSG.oddCore (Subgroup.centralizer ({tP} : Set co2P)) = ⊥ :=
  oddCore_bot_of_equiv ((MulEquiv.subgroupCongr locD_subgroupOf_eq.symm).trans
    (Subgroup.subgroupOfEquivOfLe locD_le_P)) oddCore_locD

theorem oddCore_centralizer_uP :
    CFSG.oddCore (Subgroup.centralizer ({uP} : Set co2P)) = ⊥ :=
  oddCore_bot_of_equiv ((MulEquiv.subgroupCongr centralizer_uP).trans
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : locH3 ≤ co2P))) oddCore_locH3

theorem CTUC_Co2_all_involution_centralizers_odd_core_free
    (a : CFSG.Sporadic.Co2Cert.co2P)
    (ha : orderOf a = 2) :
    CFSG.oddCore (Subgroup.centralizer ({a} : Set CFSG.Sporadic.Co2Cert.co2P)) = ⊥ := by
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; norm_num at ha
  rcases invol_cases a ha2 ha1 with h | h | h
  · exact oddCore_centralizer_of_isConj h oddCore_centralizer_zP
  · exact oddCore_centralizer_of_isConj h oddCore_centralizer_tP
  · exact oddCore_centralizer_of_isConj h oddCore_centralizer_uP

@[expose] def centralizerMap {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Subgroup.centralizer ({x} : Set G) ≃* Subgroup.centralizer ({e x} : Set H) where
  toFun g := ⟨e g, by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 g.2]⟩
  invFun g := ⟨e.symm g, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_centralizer_singleton_iff.1 g.2⟩
  left_inv g := Subtype.ext (e.symm_apply_apply _)
  right_inv g := Subtype.ext (e.apply_symm_apply _)
  map_mul' g g' := Subtype.ext (map_mul e _ _)

theorem oddCore_free_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ b : B, orderOf b = 2 → CFSG.oddCore (Subgroup.centralizer ({b} : Set B)) = ⊥)
    (a : A) (ha : orderOf a = 2) : CFSG.oddCore (Subgroup.centralizer ({a} : Set A)) = ⊥ := by
  have hb : orderOf (e a) = 2 := (MulEquiv.orderOf_eq e a).trans ha
  exact oddCore_bot_of_equiv (centralizerMap e a) (h _ hb)

theorem CTUC_Co2_all_involution_centralizers_odd_core_free_Co2
    (x : CFSG.Blueprint.NativeSporadic.Co2) (hx : orderOf x = 2) :
    CFSG.oddCore (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co2)) = ⊥ :=
  @oddCore_free_of_mulEquiv CFSG.Blueprint.NativeSporadic.Co2 co2P Units.instGroup _
    co2PermEquiv CTUC_Co2_all_involution_centralizers_odd_core_free x hx

end CFSG.Sporadic.Co2Schreier
