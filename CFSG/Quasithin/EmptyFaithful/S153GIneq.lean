module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.D2Basic
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin

open CFSG.Open

section IneqHelpers

variable {G : Type*} [Group G]

private theorem ineq_comm_of_mem {E : Subgroup G} (hE : IsElemAbelian 2 E) {x y : G}
    (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hE hx hy

private theorem ineq_isElemAbelian_of_le {E X : Subgroup G} (hE : IsElemAbelian 2 E)
    (hXE : X ≤ E) : IsElemAbelian 2 X := CFSG.Open.IsElemAbelian.mono hE hXE

private theorem ineq_exists_mul_of_mem_sup {H K : Subgroup G}
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  have comm : ∀ (m : H) (n : K), Commute (H.subtype m) (K.subtype n) :=
    fun m n => hHK m m.2 n n.2
  have h := MonoidHom.noncommCoprod_range H.subtype K.subtype comm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at h
  rw [← h] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact ⟨a, a.2, b, b.2, rfl⟩

private theorem ineq_card_sup_mul_card_inf {H K : Subgroup G}
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have comm : ∀ (m : H) (n : K), Commute (H.subtype m) (K.subtype n) :=
    fun m n => hHK m m.2 n n.2
  set φ := MonoidHom.noncommCoprod H.subtype K.subtype comm with hφ
  have hrange : φ.range = H ⊔ K := by
    have h := MonoidHom.noncommCoprod_range H.subtype K.subtype comm
    rwa [Subgroup.range_subtype, Subgroup.range_subtype] at h
  have key : ∀ p : H × K, p ∈ φ.ker ↔ ((p.1 : G) = ((p.2 : G))⁻¹) := by
    intro p
    rw [MonoidHom.mem_ker, hφ, MonoidHom.noncommCoprod_apply]
    exact mul_eq_one_iff_eq_inv
  have hker : Nat.card φ.ker = Nat.card ↥(H ⊓ K) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1.1 : G), p.1.1.2, by
          rw [(key p.1).1 p.2]; exact K.inv_mem p.1.2.2⟩
        invFun := fun x => ⟨(⟨x, x.2.1⟩, ⟨(x : G)⁻¹, K.inv_mem x.2.2⟩), by
          rw [key]; exact (inv_inv _).symm⟩
        left_inv := fun p => by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            show ((p.1.1 : G))⁻¹ = (p.1.2 : G)
            rw [(key p.1).1 p.2, inv_inv]
        right_inv := fun x => rfl }
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, Nat.card_prod] at h
  rw [mul_comm]
  exact h

private theorem ineq_isElemAbelian_sup {H K : Subgroup G} (hH : IsElemAbelian 2 H)
    (hK : IsElemAbelian 2 K) (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    IsElemAbelian 2 (H ⊔ K) := CFSG.Open.IsElemAbelian.sup_of_commute hH hK hHK

private theorem ineq_card_eq_two_pow [Finite G] {E X : Subgroup G} (hE : IsElemAbelian 2 E)
    (hXE : X ≤ E) : Nat.card X = 2 ^ rk X :=
  card_eq_two_pow_of_isPGroup
    (isPGroup_two_of_sq_eq_one fun v => Subtype.ext (hE.2 v (hXE v.2)))

private theorem ineq_commute_sup {U V : Subgroup G} {b : G} (hbU : ∀ u ∈ U, u * b = b * u)
    (hbV : ∀ v ∈ V, v * b = b * v) {w : G} (hw : w ∈ U ⊔ V) : w * b = b * w := by
  have h : U ⊔ V ≤ Subgroup.centralizer ({b} : Set G) :=
    sup_le (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hbU u hu))
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr (hbV v hv))
  exact Subgroup.mem_centralizer_singleton_iff.mp (h hw)

private theorem ineq_commute_of_commute_mul {U V : Subgroup G} (hUVb : U ⊓ V = ⊥) {a u v : G}
    (hu : u ∈ U) (hv : v ∈ V) (haU : a ∈ Subgroup.normalizer (U : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (h : a * (u * v) = (u * v) * a) :
    a * u = u * a ∧ a * v = v * a := by
  have hu' : a * u * a⁻¹ ∈ U := (Subgroup.mem_set_normalizer_iff.mp haU u).mp hu
  have hv' : a * v * a⁻¹ ∈ V := (Subgroup.mem_set_normalizer_iff.mp haV v).mp hv
  have key : (a * u * a⁻¹) * (a * v * a⁻¹) = u * v := by
    calc (a * u * a⁻¹) * (a * v * a⁻¹) = a * (u * v) * a⁻¹ := by group
      _ = u * v := by rw [h]; group
  have hmem : u⁻¹ * (a * u * a⁻¹) ∈ U ⊓ V := by
    refine ⟨U.mul_mem (U.inv_mem hu) hu', ?_⟩
    have : u⁻¹ * (a * u * a⁻¹) = v * (a * v * a⁻¹)⁻¹ := by
      calc u⁻¹ * (a * u * a⁻¹)
          = u⁻¹ * ((a * u * a⁻¹) * (a * v * a⁻¹)) * (a * v * a⁻¹)⁻¹ := by group
        _ = v * (a * v * a⁻¹)⁻¹ := by rw [key]; group
    rw [this]
    exact V.mul_mem hv (V.inv_mem hv')
  rw [hUVb, Subgroup.mem_bot] at hmem
  have e1 : a * u * a⁻¹ = u := (inv_mul_eq_one.mp hmem).symm
  have e2 : a * v * a⁻¹ = v := by
    rw [e1] at key
    exact mul_left_cancel key
  exact ⟨mul_inv_eq_iff_eq_mul.mp e1, mul_inv_eq_iff_eq_mul.mp e2⟩

private theorem ineq_card_sup_le [Finite G] {H K : Subgroup G}
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  rw [← ineq_card_sup_mul_card_inf hHK]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

private theorem ineq_card_sup_of_inf_bot {U V : Subgroup G}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hUVb : U ⊓ V = ⊥) :
    Nat.card ↥(U ⊔ V) = Nat.card U * Nat.card V := by
  have h := ineq_card_sup_mul_card_inf hUV
  rwa [hUVb, Subgroup.card_bot, mul_one] at h

private theorem ineq_card_mul_le [Finite G] {E X Y : Subgroup G} (hE : IsElemAbelian 2 E)
    (hXE : X ≤ E) (hYE : Y ≤ E) :
    Nat.card X * Nat.card Y ≤ Nat.card E * Nat.card ↥(X ⊓ Y) := by
  rw [← ineq_card_sup_mul_card_inf fun x hx y hy => ineq_comm_of_mem hE (hXE hx) (hYE hy)]
  exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le (sup_le hXE hYE))

private theorem ineq_card_bw_le [Finite G] {S A U V B : Subgroup G}
    (hA : IsMaxElemAbelian S A) (hU : IsElemAbelian 2 U) (hV : IsElemAbelian 2 V)
    (hUS : U ≤ S) (hVS : V ≤ S) (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hUVb : U ⊓ V = ⊥)
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hBA : B ≤ A) (hBW : ∀ b ∈ B, ∀ w ∈ U ⊔ V, b * w = w * b) :
    B ⊔ (U ⊔ V) ≤ S ∧ IsElemAbelian 2 (B ⊔ (U ⊔ V)) ∧ Nat.card ↥(B ⊔ (U ⊔ V)) ≤ Nat.card A ∧
      Nat.card B * (Nat.card U * Nat.card V) ≤
        Nat.card ↥(B ⊔ (U ⊔ V)) * (Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) *
          Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) := by
  obtain ⟨hAS, hAel, hmax⟩ := hA
  have hXel : IsElemAbelian 2 (B ⊔ (U ⊔ V)) :=
    ineq_isElemAbelian_sup (ineq_isElemAbelian_of_le hAel hBA)
      (ineq_isElemAbelian_sup hU hV hUV) hBW
  have hXS : B ⊔ (U ⊔ V) ≤ S := sup_le (hBA.trans hAS) (sup_le hUS hVS)
  have h2 := ineq_card_sup_mul_card_inf hBW
  have h3 := ineq_card_sup_of_inf_bot hUV hUVb
  have h4 : B ⊓ (U ⊔ V) ≤
      (U ⊓ Subgroup.centralizer (A : Set G)) ⊔ (V ⊓ Subgroup.centralizer (A : Set G)) := by
    rintro x ⟨hxB, hxW⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := ineq_exists_mul_of_mem_sup hUV hxW
    have hc : ∀ a ∈ A, a * u = u * a ∧ a * v = v * a := fun a ha =>
      ineq_commute_of_commute_mul hUVb hu hv (hSU (hAS ha)) (hSV (hAS ha))
        (ineq_comm_of_mem hAel ha (hBA hxB))
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left ⟨hu, Subgroup.mem_centralizer_iff.mpr fun a ha => (hc a ha).1⟩)
      (Subgroup.mem_sup_right ⟨hv, Subgroup.mem_centralizer_iff.mpr fun a ha => (hc a ha).2⟩)
  have h5 : Nat.card ↥(B ⊓ (U ⊔ V)) ≤
      Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
    (Subgroup.card_le_of_le h4).trans (ineq_card_sup_le fun x hx y hy => hUV x hx.1 y hy.1)
  refine ⟨hXS, hXel, hmax _ hXS hXel, ?_⟩
  calc Nat.card B * (Nat.card U * Nat.card V) = Nat.card B * Nat.card ↥(U ⊔ V) := by rw [h3]
    _ = Nat.card ↥(B ⊔ (U ⊔ V)) * Nat.card ↥(B ⊓ (U ⊔ V)) := h2.symm
    _ ≤ _ := Nat.mul_le_mul_left _ h5

private theorem ineq_bw_facts [Finite G] {S P A U V : Subgroup G}
    (hA : IsMaxElemAbelian S A)
    (hU : IsElemAbelian 2 U) (hV : IsElemAbelian 2 V) (hUS : U ≤ S) (hVS : V ≤ S)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hUVb : U ⊓ V = ⊥)
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hP : S ⊓ Subgroup.centralizer ((U ⊔ V : Subgroup G) : Set G) ≤ P) :
    (A ⊓ Subgroup.centralizer ((U ⊔ V : Subgroup G) : Set G)) ⊔ (U ⊔ V) ≤ S ∧
      IsElemAbelian 2 ((A ⊓ Subgroup.centralizer ((U ⊔ V : Subgroup G) : Set G)) ⊔ (U ⊔ V)) ∧
      rk ↥((A ⊓ Subgroup.centralizer ((U ⊔ V : Subgroup G) : Set G)) ⊔ (U ⊔ V)) ≤ rk ↥A ∧
      rk ↥U + rk ↥V + rk ↥(A ⊓ P ⊓ Subgroup.centralizer (U : Set G)) +
          rk ↥(A ⊓ P ⊓ Subgroup.centralizer (V : Set G)) ≤
        rk ↥((A ⊓ Subgroup.centralizer ((U ⊔ V : Subgroup G) : Set G)) ⊔ (U ⊔ V)) +
          rk ↥(A ⊓ P) + rk ↥(U ⊓ Subgroup.centralizer (A : Set G)) +
          rk ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
  set B : Subgroup G := A ⊓ Subgroup.centralizer ((U ⊔ V : Subgroup G) : Set G)
  have hAel : IsElemAbelian 2 A := hA.2.1
  have hBW : ∀ b ∈ B, ∀ w ∈ U ⊔ V, b * w = w * b := fun b hb w hw =>
    (Subgroup.mem_centralizer_iff.mp hb.2 w hw).symm
  obtain ⟨hXS, hXel, h1, h2⟩ :=
    ineq_card_bw_le hA hU hV hUS hVS hUV hUVb hSU hSV inf_le_left hBW
  have hEel : IsElemAbelian 2 (A ⊓ P) := ineq_isElemAbelian_of_le hAel inf_le_left
  have hXY : (A ⊓ P ⊓ Subgroup.centralizer (U : Set G)) ⊓
      (A ⊓ P ⊓ Subgroup.centralizer (V : Set G)) = B := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1.1.1, Subgroup.mem_centralizer_iff.mpr fun w hw =>
        ineq_commute_sup (Subgroup.mem_centralizer_iff.mp hx.1.2)
          (Subgroup.mem_centralizer_iff.mp hx.2.2) hw⟩
    · intro x hx
      have hxP : x ∈ P := hP ⟨hA.1 hx.1, hx.2⟩
      exact ⟨⟨⟨hx.1, hxP⟩, Subgroup.centralizer_le (le_sup_left : U ≤ U ⊔ V) hx.2⟩,
        ⟨⟨hx.1, hxP⟩, Subgroup.centralizer_le (le_sup_right : V ≤ U ⊔ V) hx.2⟩⟩
  have hb := ineq_card_mul_le hEel
    (inf_le_left : A ⊓ P ⊓ Subgroup.centralizer (U : Set G) ≤ A ⊓ P)
    (inf_le_left : A ⊓ P ⊓ Subgroup.centralizer (V : Set G) ≤ A ⊓ P)
  rw [hXY] at hb
  have hM : Nat.card U * Nat.card V *
      (Nat.card ↥(A ⊓ P ⊓ Subgroup.centralizer (U : Set G)) *
        Nat.card ↥(A ⊓ P ⊓ Subgroup.centralizer (V : Set G))) ≤
      Nat.card ↥(B ⊔ (U ⊔ V)) * Nat.card ↥(A ⊓ P) *
        (Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) *
          Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) := by
    calc _ ≤ Nat.card U * Nat.card V * (Nat.card ↥(A ⊓ P) * Nat.card B) :=
          Nat.mul_le_mul_left _ hb
      _ = Nat.card ↥(A ⊓ P) * (Nat.card B * (Nat.card U * Nat.card V)) := by ring
      _ ≤ Nat.card ↥(A ⊓ P) * (Nat.card ↥(B ⊔ (U ⊔ V)) *
          (Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) *
            Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)))) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  have cU : Nat.card U = 2 ^ rk ↥U := ineq_card_eq_two_pow hU le_rfl
  have cV : Nat.card V = 2 ^ rk ↥V := ineq_card_eq_two_pow hV le_rfl
  have cA : Nat.card A = 2 ^ rk ↥A := ineq_card_eq_two_pow hAel le_rfl
  have cBW : Nat.card ↥(B ⊔ (U ⊔ V)) = 2 ^ rk ↥(B ⊔ (U ⊔ V)) :=
    ineq_card_eq_two_pow hXel le_rfl
  have cE : Nat.card ↥(A ⊓ P) = 2 ^ rk ↥(A ⊓ P) := ineq_card_eq_two_pow hAel inf_le_left
  have cX : Nat.card ↥(A ⊓ P ⊓ Subgroup.centralizer (U : Set G)) =
      2 ^ rk ↥(A ⊓ P ⊓ Subgroup.centralizer (U : Set G)) :=
    ineq_card_eq_two_pow hAel (inf_le_left.trans inf_le_left)
  have cY : Nat.card ↥(A ⊓ P ⊓ Subgroup.centralizer (V : Set G)) =
      2 ^ rk ↥(A ⊓ P ⊓ Subgroup.centralizer (V : Set G)) :=
    ineq_card_eq_two_pow hAel (inf_le_left.trans inf_le_left)
  have cNU : Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) =
      2 ^ rk ↥(U ⊓ Subgroup.centralizer (A : Set G)) := ineq_card_eq_two_pow hU inf_le_left
  have cNV : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) =
      2 ^ rk ↥(V ⊓ Subgroup.centralizer (A : Set G)) := ineq_card_eq_two_pow hV inf_le_left
  refine ⟨hXS, hXel, ?_, ?_⟩
  · rw [cBW, cA] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  · rw [cU, cV, cBW, cE, cX, cY, cNU, cNV] at hM
    have hM' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      (by simpa only [← pow_add] using hM)
    omega

end IneqHelpers

theorem count_ineq_abstract {G : Type} [Group G] [Finite G] {S P A U V : Subgroup G}
    (hA : IsMaxElemAbelian S A)
    (hU : IsElemAbelian 2 U) (hV : IsElemAbelian 2 V) (hUS : U ≤ S) (hVS : V ≤ S)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hUVb : U ⊓ V = ⊥)
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hP : S ⊓ Subgroup.centralizer ((U ⊔ V : Subgroup G) : Set G) ≤ P) :
    rk ↥U + rk ↥V + rk ↥(A ⊓ P ⊓ Subgroup.centralizer (U : Set G)) +
        rk ↥(A ⊓ P ⊓ Subgroup.centralizer (V : Set G)) ≤
      rk ↥A + rk ↥(A ⊓ P) + rk ↥(U ⊓ Subgroup.centralizer (A : Set G)) +
        rk ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
  obtain ⟨-, -, h1, h2⟩ := ineq_bw_facts hA hU hV hUS hVS hUV hUVb hSU hSV hP
  omega

theorem count_eq_abstract {G : Type} [Group G] [Finite G] {S P A U V : Subgroup G}
    (hA : IsMaxElemAbelian S A)
    (hU : IsElemAbelian 2 U) (hV : IsElemAbelian 2 V) (hUS : U ≤ S) (hVS : V ≤ S)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hUVb : U ⊓ V = ⊥)
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hP : S ⊓ Subgroup.centralizer ((U ⊔ V : Subgroup G) : Set G) ≤ P)
    (hEq : rk ↥U + rk ↥V + rk ↥(A ⊓ P ⊓ Subgroup.centralizer (U : Set G)) +
        rk ↥(A ⊓ P ⊓ Subgroup.centralizer (V : Set G)) =
      rk ↥A + rk ↥(A ⊓ P) + rk ↥(U ⊓ Subgroup.centralizer (A : Set G)) +
        rk ↥(V ⊓ Subgroup.centralizer (A : Set G))) :
    IsMaxElemAbelian S
      ((A ⊓ Subgroup.centralizer ((U ⊔ V : Subgroup G) : Set G)) ⊔ (U ⊔ V)) := by
  obtain ⟨hXS, hXel, h1, h2⟩ := ineq_bw_facts hA hU hV hUS hVS hUV hUVb hSU hSV hP
  have hrk : rk ↥A ≤
      rk ↥((A ⊓ Subgroup.centralizer ((U ⊔ V : Subgroup G) : Set G)) ⊔ (U ⊔ V)) := by omega
  refine ⟨hXS, hXel, fun Y hY hYel => ?_⟩
  calc Nat.card Y ≤ Nat.card A := hA.2.2 Y hY hYel
    _ = 2 ^ rk ↥A := ineq_card_eq_two_pow hA.2.1 le_rfl
    _ ≤ 2 ^ rk ↥((A ⊓ Subgroup.centralizer ((U ⊔ V : Subgroup G) : Set G)) ⊔ (U ⊔ V)) :=
      Nat.pow_le_pow_right (by norm_num) hrk
    _ = _ := (ineq_card_eq_two_pow hXel le_rfl).symm

end CFSG.Quasithin
