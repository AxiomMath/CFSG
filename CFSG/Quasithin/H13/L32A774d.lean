module

public import CFSG.Quasithin.H13.L32A774a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem sl24_transitive : ∀ v w : Fin 2 → F4, v ≠ 0 → w ≠ 0 →
    ∃ A : SL(2, F4), (A : Matrix (Fin 2) (Fin 2) F4).mulVec v = w := by
  decide +kernel

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem hz_le_normalizer_fsuU : hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) := by
  intro h hh
  refine le_normalizer_conjClosure V _ ?_
  rw [normalizer_eq_centralizer_of_card_two (C.hMod G T L V C.hyp.hyp C.hyp.fsu).2.2.2.1]
  exact hh

theorem eq_fsuU_of {X : Subgroup G} (hVX : fsuV1 T V ≤ X) (hXU : X ≤ fsuU T V)
    (hXK : kz T V ≤ Subgroup.normalizer (X : Set G)) (hne : X ≠ fsuV1 T V) : X = fsuU T V := by
  obtain ⟨-, π, β, hπs, -, -, hβk, hβe⟩ := isL24Section_u0 C.hyp C.hMod C.h63
  rw [C.u0_eq] at hβk
  have hβ1 : ∀ u : ↥(fsuU T V), β u = 1 ↔ (u : G) ∈ fsuV1 T V := fun u => by
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  obtain ⟨w, hwX, hwV⟩ : ∃ w ∈ X, w ∉ fsuV1 T V := by
    by_contra h
    push Not at h
    exact hne (le_antisymm h hVX)
  have hwU := hXU hwX
  have hβw : Multiplicative.toAdd (β ⟨w, hwU⟩) ≠ 0 := fun h0 => hwV ((hβ1 _).mp (by
    rw [← ofAdd_toAdd (β ⟨w, hwU⟩), h0]; rfl))
  refine le_antisymm hXU fun u hu => ?_
  by_cases hβu : Multiplicative.toAdd (β ⟨u, hu⟩) = 0
  · exact hVX ((hβ1 _).mp (by rw [← ofAdd_toAdd (β ⟨u, hu⟩), hβu]; rfl))
  obtain ⟨A, hA⟩ := sl24_transitive _ _ hβw hβu
  obtain ⟨k, rfl⟩ := hπs A
  have hkw : (k : G) * w * (k : G)⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp (C.hz_le_normalizer_fsuU ((oTwoUpper_le (hz T V)) k.2)) w).mp
      hwU
  have h1 := hβe k ⟨w, hwU⟩ ⟨_, hkw⟩ rfl
  rw [hA, ofAdd_toAdd] at h1
  have h2 : β (⟨u, hu⟩ * (⟨_, hkw⟩ : ↥(fsuU T V))⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := (hβ1 _).mp h2
  have hkwX : (k : G) * w * (k : G)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hXK k.2) w).mp hwX
  have h3' : u * ((k : G) * w * (k : G)⁻¹)⁻¹ ∈ fsuV1 T V := by simpa using h3
  rw [show u = (u * ((k : G) * w * (k : G)⁻¹)⁻¹) * ((k : G) * w * (k : G)⁻¹) by group]
  exact mul_mem (hVX h3') hkwX

theorem comm_mem_fsuV1 {q u : G} (hq : q ∈ pCoreOf 2 (hz T V)) (hu : u ∈ fsuU T V) :
    q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hQH : pCoreOf 2 (hz T V) ≤ hz T V := pCoreOf_le 2 _
  have hHU := C.hz_le_normalizer_fsuU
  have hHV1 : hz T V ≤ Subgroup.normalizer (fsuV1 T V : Set G) := by
    rw [normalizer_eq_centralizer_of_card_two hV1]
  have hV1U : fsuV1 T V ≤ fsuU T V := fun w hw => v_le_fsuU (Subgroup.mem_inf.mp hw).1
  have hV1ne : fsuV1 T V ≠ fsuU T V := by
    obtain ⟨u, hu, huV⟩ := C.exists_mem_fsuU C.u0_eq
    exact fun h => huV (Subgroup.mem_inf.mp (h ▸ hu : u ∈ fsuV1 T V)).1
  have hUp : IsPGroup 2 ↥(fsuU T V) := fun u => ⟨1, Subtype.ext (by
    simpa using F7.isElemAbelian_pow_eq_one hUe u.2)⟩
  have hUV1 : fsuU T V ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    le_normalizer_of_conj_mem' fun a ha b hb => by
      rw [F7.isElemAbelian_comm hUe ha (hV1U hb), mul_inv_cancel_right]
      exact hb
  obtain ⟨m, hmU, hmV, hmQ⟩ := exists_mem_fix_mod hV1U hV1ne
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hUp (hQH.trans hHU) (hQH.trans hHV1) hUV1
  let X : Subgroup G :=
    { carrier := {u | u ∈ fsuU T V ∧ ∀ q ∈ pCoreOf 2 (hz T V), q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V}
      one_mem' := ⟨one_mem _, fun q _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun q hq => by
        have hqb : q * b * q⁻¹ ∈ fsuU T V :=
          (Subgroup.mem_normalizer_iff.mp (hHU (hQH hq)) b).mp hb.1
        rw [show q * (a * b) * q⁻¹ * (a * b)⁻¹ =
          (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹) * a⁻¹) by group]
        refine mul_mem (ha.2 q hq) ?_
        rw [F7.isElemAbelian_comm hUe ha.1 (hV1U (hb.2 q hq)), mul_inv_cancel_right]
        exact hb.2 q hq⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun q hq => by
        have h1 := ha.2 q hq
        have hqa : q * a * q⁻¹ ∈ fsuU T V :=
          (Subgroup.mem_normalizer_iff.mp (hHU (hQH hq)) a).mp ha.1
        have e : q * a⁻¹ * q⁻¹ * a⁻¹⁻¹ = (q * a * q⁻¹ * a⁻¹)⁻¹ := by
          rw [show q * a⁻¹ * q⁻¹ * a⁻¹⁻¹ = (q * a * q⁻¹)⁻¹ * a by group,
            F7.isElemAbelian_comm hUe (inv_mem hqa) ha.1]
          group
        rw [e]
        exact inv_mem h1⟩ }
  have hXU : X ≤ fsuU T V := fun a ha => ha.1
  have hVX : fsuV1 T V ≤ X := fun a ha => ⟨hV1U ha, fun q hq => by
    rw [(Subgroup.mem_centralizer_iff.mp (hQH hq) a ha).symm, mul_inv_cancel_right,
      mul_inv_cancel]
    exact one_mem _⟩
  have hXK : kz T V ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_conj_mem' fun k hk a ha => ⟨
      (Subgroup.mem_normalizer_iff.mp (C.hz_le_normalizer_fsuU ((oTwoUpper_le (hz T V)) hk)) a).mp
        ha.1,
      fun q hq => by
        have hkq : k⁻¹ * q * k ∈ pCoreOf 2 (hz T V) := by
          have := (Subgroup.mem_normalizer_iff.mp
            (le_normalizer_pCoreOf 2 _ ((oTwoUpper_le (hz T V)) (inv_mem hk))) q).mp hq
          rwa [inv_inv] at this
        have h1 := ha.2 _ hkq
        have h2 := (Subgroup.mem_normalizer_iff.mp (hHV1 ((oTwoUpper_le (hz T V)) hk)) _).mp h1
        rwa [show k * (k⁻¹ * q * k * a * (k⁻¹ * q * k)⁻¹ * a⁻¹) * k⁻¹ =
          q * (k * a * k⁻¹) * q⁻¹ * (k * a * k⁻¹)⁻¹ by group] at h2⟩
  have hXne : X ≠ fsuV1 T V := fun h => hmV (h ▸ (⟨hmU, fun q hq => hmQ q hq⟩ : m ∈ X))
  have hXeq := C.eq_fsuU_of hVX hXU hXK hXne
  have huX : u ∈ X := hXeq.symm ▸ hu
  exact huX.2 q hq

theorem mem_fsuV1_of_comm {x : G} (hxL1 : x ∈ L₁Of L (fsuV1 T V)) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {u : G} (hu : u ∈ fsuU T V) (hxu : x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    u ∈ fsuV1 T V := by
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hV1
  have huV : u ∈ V := by
    by_contra huV
    exact C.comm_not_mem C.u0_eq hxL1 hx3 hx1 hu huV (Subgroup.mem_inf.mp hxu).1
  have hxz : x * z * x⁻¹ = z :=
    (mem_normalizer_iff_of_gen hzV1 hz1 hgen).mp
      (Subgroup.mem_inf.mp (L32NSet14.Setting.L1_le hxL1)).2
  rcases hgen _ hxu with h | h
  ·
    have hxu' : x * u * x⁻¹ = u := by
      calc x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
        _ = u := by rw [h, one_mul]
    have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
    obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
    have h1281 := C.hyp.hyp1281One C.h13322 C.hMod
    obtain ⟨hcard, hsq, -⟩ := h1281.card_sq
    have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
    obtain ⟨e⟩ : Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) :=
      Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one
        (fun y => Subtype.ext (by simpa using hsq y y.2)) hcard
    have hxV : x ∉ Subgroup.centralizer (V : Set G) := by
      intro hxC
      have hxP : x ∈ pCoreOf 2 L := by
        rw [C.pCoreOf_eq]
        exact Subgroup.mem_inf.mpr ⟨hxL, hxC⟩
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨x, hxP⟩
      have h2k : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hord : orderOf x = 1 :=
        Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
          (orderOf_dvd_of_pow_eq_one hx3) (orderOf_dvd_of_pow_eq_one h2k)
      exact hx1 (orderOf_eq_one_iff.mp hord)
    have hc2 := card_inf_centralizer_eq_two (le_sup_left.trans hLTV) e hxL hx3 hxV
    have hle : fsuV1 T V ≤ V ⊓ Subgroup.centralizer ({x} : Set G) := by
      intro w hw
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw).1, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hgen w hw with rfl | rfl
      · group
      · calc w * x = (x * w * x⁻¹) * x := by rw [hxz]
          _ = x * w := by group
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hc2, hV1])
    have huC : u ∈ V ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨huV, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc u * x = (x * u * x⁻¹) * x := by rw [hxu']
        _ = x * u := by group
    rw [← heq] at huC
    exact huC
  ·
    exfalso
    have hxu' : x * u * x⁻¹ = z * u := by
      calc x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
        _ = z * u := by rw [h]
    have h3 : x ^ 3 * u * (x ^ 3)⁻¹ = z * (z * (z * u)) := by
      calc x ^ 3 * u * (x ^ 3)⁻¹ = x * (x * (x * u * x⁻¹) * x⁻¹) * x⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul]; group
        _ = x * (x * (z * u) * x⁻¹) * x⁻¹ := by rw [hxu']
        _ = x * ((x * z * x⁻¹) * (x * u * x⁻¹)) * x⁻¹ := by group
        _ = x * (z * (z * u)) * x⁻¹ := by rw [hxz, hxu']
        _ = (x * z * x⁻¹) * ((x * z * x⁻¹) * (x * u * x⁻¹)) := by group
        _ = z * (z * (z * u)) := by rw [hxz, hxu']
    rw [hx3] at h3
    have hz2 : z * z = 1 := by
      rw [← pow_two]
      exact F7.isElemAbelian_pow_eq_one (isElemAbelian_fsuU_of C.hyp C.hMod)
        (v_le_fsuU (Subgroup.mem_inf.mp hzV1).1)
    apply hz1
    calc z = z * (z * (z * u)) * u⁻¹ := by rw [← mul_assoc z z, hz2, one_mul]; group
      _ = 1 * u * 1⁻¹ * u⁻¹ := by rw [← h3]
      _ = 1 := by group

end Ctx73

end CFSG.Quasithin.H13.L32A
