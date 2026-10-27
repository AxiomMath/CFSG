module

public import CFSG.Quasithin.Vol2.Ch3E213MOL5
public import CFSG.Quasithin.Vol2.Ch3E213MOL3
public import CFSG.Quasithin.Vol2.Ch3E213MOL4

public section

namespace CFSG.Quasithin.Ch3E213M.OL

open CFSG.Open CFSG.QuasithinUnique B6 E2P

theorem conj_mem_zOf' {X : Type} [Group X] {S : Subgroup X} {t w : X}
    (ht : t ∈ Subgroup.normalizer (S : Set X)) (hw : w ∈ E2P.zOf S) : t * w * t⁻¹ ∈ E2P.zOf S := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp ht w).mp hw.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro x hx
  have hx' : t⁻¹ * x * t ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) x).mp hx
    simpa using this
  have h := (Subgroup.mem_centralizer_iff.mp hw.2) _ hx'
  calc x * (t * w * t⁻¹) = t * ((t⁻¹ * x * t) * w) * t⁻¹ := by group
    _ = t * (w * (t⁻¹ * x * t)) * t⁻¹ := by rw [h]
    _ = t * w * t⁻¹ * x := by group

theorem not_isPGroup_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : ¬ IsPGroup 2 X := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt := h2.center_nontrivial
  rw [center_eq_bot_of_simple hnab] at hnt
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt rfl

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

theorem false_of_three (hB : KFactL33NoQuadFour) (hS : Setting H T M V K)
    (hC2 : Case2 H T M K) (hL : IsPSL 3 3 1 ↥(E2.star M H K))
    (hMK : E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp : IsSimpleGroup ↥(E2.star M H K) :=
    isSimpleGroup_of_L3U3 Nat.prime_three le_rfl (Or.inr hL)
  have hnab := nonab_star hS
  have hZK := center_eq_bot_of_simple hnab
  have hX := OS.asHyp_star hS hC2 hsimp hZK hnab
  have := hX.normal
  obtain ⟨z, hz, hzS, hquad⟩ := hB _ _ hX.normal hL hX.cent (toSylow2 hX.isSylow_inf)
  rw [toSylow2_coe] at hzS
  have hzX : E2P.zOf (E2.star M H T ⊓ E2.star M H K) =
      Subgroup.zpowers (z : E2.StarQuot M H) := by
    rw [← map_zOf_subgroupOf inf_le_right, hzS, MonoidHom.map_zpowers]
    rfl
  have hzZ : (z : E2.StarQuot M H) ∈ E2P.zOf (E2.star M H T ⊓ E2.star M H K) :=
    hzX ▸ Subgroup.mem_zpowers _
  have hz2 : (z : E2.StarQuot M H) * z = 1 := by
    rw [← pow_two, ← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hz1 : (z : E2.StarQuot M H) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    omega
  have hzpow : ∀ y ∈ Subgroup.zpowers (z : E2.StarQuot M H), y = 1 ∨ y = z := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hord : orderOf (z : E2.StarQuot M H) = 2 := by rw [Subgroup.orderOf_coe, hz]
    rw [← zpow_mod_orderOf, hord, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  have hTz : ∀ t ∈ E2.star M H T, t * (z : E2.StarQuot M H) = z * t := by
    intro t ht
    have h1 := conj_mem_zOf' (hX.le_normalizer_inf ht) hzZ
    rw [hzX] at h1
    rcases hzpow _ h1 with h | h
    · exfalso
      apply hz1
      calc (z : E2.StarQuot M H) = t⁻¹ * (t * z * t⁻¹) * t := by group
        _ = 1 := by rw [h]; group
    · calc t * (z : E2.StarQuot M H) = t * z * t⁻¹ * t := by group
        _ = z * t := by rw [h]
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hTK : E2.star M H (T ⊓ K) = E2.star M H T ⊓ E2.star M H K :=
    star_inf_T hS.hyp.minParabolic.isSylow hS.mem_cComp.2.2.1 hKH
  have hMK' : E2.star M H M ⊓ E2.star M H K = E2.star M H K ⊓
      Subgroup.centralizer (zOf (E2.star M H T ⊓ E2.star M H K) : Set (E2.StarQuot M H)) := by
    rw [← star_inf_M, hMK, ← hTK]
    rfl
  have hMz : E2.star M H M ≤ Subgroup.centralizer ({(z : E2.StarQuot M H)} : Set _) := by
    intro m hm
    have hKn : E2.star M H T ≤ Subgroup.normalizer (E2.star M H K : Set (E2.StarQuot M H)) :=
      fun t _ => hX.mem_normalizer_K t
    have hm' : m ∈ E2.star M H K ⊔ E2.star M H T := by rw [hX.sup]; trivial
    obtain ⟨k, hk, t, ht, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hKn hm'
    have hkM : k ∈ E2.star M H M := by
      have h1 := (E2.star M H M).mul_mem hm ((E2.star M H M).inv_mem (hX.minPar.le ht))
      simpa using h1
    have hkC : k * (z : E2.StarQuot M H) = z * k := by
      have h1 : k ∈ E2.star M H M ⊓ E2.star M H K := ⟨hkM, hk⟩
      rw [hMK'] at h1
      exact ((Subgroup.mem_centralizer_iff.mp h1.2) _ hzZ).symm
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * t * (z : E2.StarQuot M H) = k * (t * z) := mul_assoc _ _ _
      _ = k * (z * t) := by rw [hTz t ht]
      _ = (k * z) * t := (mul_assoc _ _ _).symm
      _ = (z * k) * t := by rw [hkC]
      _ = z * (k * t) := mul_assoc _ _ _
  have hzM : Subgroup.centralizer ({(z : E2.StarQuot M H)} : Set _) ≤ E2.star M H M := by
    refine hX.minPar.le_of_lt (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr
      (hTz t ht)) (lt_top_iff_ne_top.mpr fun htop => ?_)
    apply hz1
    have hzc : z ∈ Subgroup.center ↥(E2.star M H K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : (g : E2.StarQuot M H) ∈ Subgroup.centralizer ({(z : E2.StarQuot M H)} : Set _) := by
        rw [htop]
        trivial
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg)
    rw [hZK, Subgroup.mem_bot] at hzc
    rw [hzc]
    rfl
  have hMeq := le_antisymm hMz hzM
  have hMH : M ≤ H := hS.hyp.minParabolic.maximal.1.le
  have hVz : E2.star M H V ≤
      pCoreOf 2 (Subgroup.centralizer ({(z : E2.StarQuot M H)} : Set (E2.StarQuot M H))) := by
    rw [← hMeq]
    exact OS.star_le_pCoreOf hMH hS.hyp.le_pCoreOf
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hS.hyp.elem.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hsq : ∀ x ∈ E2.star M H V, x * x = 1 :=
    OS.star_sq fun v hv => by rw [← pow_two]; exact hS.hyp.elem.2 v hv
  have hEA : IsElemAbelian 2 (E2.star M H V) :=
    ⟨⟨⟨fun a b => Subtype.ext (OS.star_comm hVcomm _ a.2 _ b.2)⟩⟩,
      fun x hx => by rw [pow_two]; exact hsq x hx⟩
  have hV4 : 4 ≤ Nat.card (E2.star M H V) := hS.four_le.trans (OS.relIndex_le_card_star hS.hyp)
  obtain ⟨W, _, _, hc, he, ρ, hnt, hq⟩ :=
    exists_quadratic_module hS (kerIn_le_pCoreOf hS hC2 hL) (not_isPGroup_of_simple hnab)
  obtain ⟨v, hv, v', hv', w, hw⟩ := hquad _ hEA hV4 hVz W hc he ρ hnt
  exact hw (hq v hv v' hv' w)

end CFSG.Quasithin.Ch3E213M.OL
