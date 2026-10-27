module

public import CFSG.Quasithin.H13.L32A72b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ncard_conj_eq_index (L : Subgroup G) (u : G) :
    {x | ∃ l ∈ L, l * u * l⁻¹ = x}.ncard =
      ((Subgroup.centralizer ({u} : Set G)).subgroupOf L).index := by
  let φ : ↥L →* MulAut G := MulAut.conj.comp L.subtype
  let _ : MulAction ↥L G := MulAction.compHom G φ
  have hsmul : ∀ (l : ↥L) (x : G), l • x = (l : G) * x * (l : G)⁻¹ := fun _ _ => rfl
  have hstab : MulAction.stabilizer ↥L u =
      (Subgroup.centralizer ({u} : Set G)).subgroupOf L := by
    ext l
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsmul,
      Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have horb : MulAction.orbit ↥L u = {x | ∃ l ∈ L, l * u * l⁻¹ = x} := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨l, l.2, (hsmul l u).symm⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, hsmul _ u⟩
  rw [← hstab, MulAction.index_stabilizer, horb]

theorem exists_conj_of_lt (L : Subgroup G) {X : Set G} {u w : G}
    (hu : ∀ l ∈ L, l * u * l⁻¹ ∈ X) (hw : ∀ l ∈ L, l * w * l⁻¹ ∈ X)
    (hlt : X.ncard < ((Subgroup.centralizer ({u} : Set G)).subgroupOf L).index +
      ((Subgroup.centralizer ({w} : Set G)).subgroupOf L).index) :
    ∃ l ∈ L, l * u * l⁻¹ = w := by
  rw [← ncard_conj_eq_index, ← ncard_conj_eq_index] at hlt
  by_contra hne
  have hdisj : Disjoint {x | ∃ l ∈ L, l * u * l⁻¹ = x} {x | ∃ l ∈ L, l * w * l⁻¹ = x} := by
    rw [Set.disjoint_left]
    rintro x ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, h⟩
    refine hne ⟨l₂⁻¹ * l₁, mul_mem (inv_mem hl₂) hl₁, ?_⟩
    rw [show l₂⁻¹ * l₁ * u * (l₂⁻¹ * l₁)⁻¹ = l₂⁻¹ * (l₁ * u * l₁⁻¹) * l₂ by group, ← h]
    group
  have hsub : {x | ∃ l ∈ L, l * u * l⁻¹ = x} ∪ {x | ∃ l ∈ L, l * w * l⁻¹ = x} ⊆ X := by
    rintro x (⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact hu l hl
    · exact hw l hl
  have := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq hdisj] at this
  omega

namespace Ctx72

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx72 G T L V l₀)
include C

theorem u0_eq (h68 : Lemma14_7_68) : u0 T V = fsuV1 T V := by
  obtain ⟨-, hV8, hLTV, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hV1u0 := fsuV1_le_u0 C.hyp C.hMod
  have hinf := inf_u0_eq C.hyp C.hMod C.h63 C.hF
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hV1
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hzV1).1
  have hz0 : z ∈ u0 T V := hV1u0 hzV1
  by_contra hne
  obtain ⟨u, hu, huV1⟩ : ∃ u ∈ u0 T V, u ∉ fsuV1 T V := by
    by_contra h
    push Not at h
    exact hne (le_antisymm h hV1u0)
  have hcard : Nat.card ↥(u0 T V) = 2 * Nat.card ↥(fsuV1 T V) := by
    obtain ⟨k, hk⟩ : Nat.card ↥(fsuV1 T V) ∣ Nat.card ↥(u0 T V) := Subgroup.card_dvd_of_le hV1u0
    have hne2 : Nat.card ↥(u0 T V) ≠ 2 := fun h2 =>
      hne (Subgroup.eq_of_le_of_card_ge hV1u0 (by omega)).symm
    have hpos : 0 < Nat.card ↥(u0 T V) := Nat.card_pos
    have h4 := C.card_u0
    rw [hV1] at hk ⊢
    omega
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hTfix : ∀ w ∈ u0 T V, w ∉ fsuV1 T V → ∀ t ∈ T, t * w * t⁻¹ * w⁻¹ ∈ fsuV1 T V := by
    intro w hw hwV1 t ht
    have htw : t * w * t⁻¹ ∈ u0 T V :=
      (Subgroup.mem_normalizer_iff.mp (hz_le_normalizer_u0 C.hyp C.hMod (hTH ht)) w).mp hw
    have htwV1 : t * w * t⁻¹ ∉ fsuV1 T V := fun h =>
      hwV1 ((Subgroup.mem_normalizer_iff.mp (C.hF.H_normalizes_V₁ (hTH ht)) w).mpr h)
    have h2 := L32NSet14.mul_mem_of_card_eq_two_mul hV1u0 hcard (by rw [hV1]; norm_num) htw hw
      htwV1 hwV1
    have hww : w⁻¹ = w := by
      have : w * w = 1 := by
        rw [← pow_two]
        exact F7.isElemAbelian_pow_eq_one hUe (u0_le_fsuU hw)
      exact inv_eq_of_mul_eq_one_right this
    rwa [hww]
  have huz : u * z ∈ u0 T V := mul_mem hu hz0
  have huzV1 : u * z ∉ fsuV1 T V := fun h => huV1 (by
    have := mul_mem h (inv_mem hzV1)
    rwa [mul_inv_cancel_right] at this)
  have hu1 : u ≠ 1 := fun h => huV1 (h ▸ one_mem _)
  have huz1 : u * z ≠ 1 := fun h => huzV1 (h ▸ one_mem _)
  obtain ⟨hCu, -⟩ := (h68 G T L V C.hyp).2 u hu hu1 (hTfix u hu huV1)
  obtain ⟨hCuz, huniq⟩ := (h68 G T L V C.hyp).2 (u * z) huz huz1 (hTfix _ huz huzV1)
  set N := L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) with hN
  have hidx : (N.subgroupOf L).index = 7 :=
    index_inf_normalizer_V1 (C.hyp.hyp1281One C.h13322 C.hMod) (le_sup_left.trans hLTV)
      inf_le_left hzV1 hz1 hgen
  have hle : ∀ w, Subgroup.centralizer ({w} : Set G) ≤ hz T V →
      (Subgroup.centralizer ({w} : Set G)).subgroupOf L ≤ N.subgroupOf L := by
    intro w hw l hl
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    refine Subgroup.mem_inf.mpr ⟨l.2, ?_⟩
    rw [normalizer_eq_centralizer_of_card_two hV1]
    exact hw hl
  have h7 : ∀ w, Subgroup.centralizer ({w} : Set G) ≤ hz T V →
      7 ≤ ((Subgroup.centralizer ({w} : Set G)).subgroupOf L).index := by
    intro w hw
    have e := Subgroup.relIndex_mul_index (hle w hw)
    rw [hidx] at e
    have hne0 : ((Subgroup.centralizer ({w} : Set G)).subgroupOf L).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    omega
  set X : Set G := {x | x * u⁻¹ ∈ V} with hX
  have hXcard : X.ncard ≤ 8 := by
    have hsub : X ⊆ (fun v => v * u) '' (V : Set G) := fun x hx =>
      ⟨x * u⁻¹, hx, by simp⟩
    calc X.ncard ≤ ((fun v => v * u) '' (V : Set G)).ncard := Set.ncard_le_ncard hsub
      _ ≤ (V : Set G).ncard := Set.ncard_image_le
      _ = 8 := by rw [← Nat.card_coe_set_eq]; exact hV8
  have hR := C.eq.2
  have hXu : ∀ l ∈ L, l * u * l⁻¹ ∈ X := fun l hl =>
    hR l hl u (le_conjClosure _ _ (Subgroup.mem_sup_right hu))
  have hXuz : ∀ l ∈ L, l * (u * z) * l⁻¹ ∈ X := fun l hl => by
    show l * (u * z) * l⁻¹ * u⁻¹ ∈ V
    have h1 := hR l hl _ (le_conjClosure _ _ (Subgroup.mem_sup_right huz))
    have hcomm : u * z = z * u := F7.isElemAbelian_comm hUe (u0_le_fsuU hu) (v_le_fsuU hzV)
    rw [show l * (u * z) * l⁻¹ * u⁻¹ = (l * (u * z) * l⁻¹ * (u * z)⁻¹) * (u * z * u⁻¹) by
      group]
    refine mul_mem h1 ?_
    rw [hcomm, mul_inv_cancel_right]
    exact hzV
  have hCuN : N.subgroupOf L ≤ (Subgroup.centralizer ({u} : Set G)).subgroupOf L := by
    have e := Subgroup.relIndex_mul_index (hle u hCu)
    rw [hidx] at e
    have h8 : ((Subgroup.centralizer ({u} : Set G)).subgroupOf L).index ≤ 8 := by
      rw [← ncard_conj_eq_index]
      refine (Set.ncard_le_ncard fun x hx => ?_).trans hXcard
      obtain ⟨l, hl, rfl⟩ := hx
      exact hXu l hl
    have hne0 : ((Subgroup.centralizer ({u} : Set G)).subgroupOf L).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    exact Subgroup.relIndex_eq_one.mp (by omega)
  obtain ⟨l, hl, hlu⟩ := exists_conj_of_lt L hXu hXuz (by
    have := h7 u hCu
    have := h7 (u * z) hCuz
    omega)
  have hlN : l ∈ Subgroup.normalizer (u0 T V : Set G) :=
    conjSub_eq_self_iff.mp (huniq l (by rw [← hlu]; exact mul_mem_conjSub hu))
  have hlV : l ∈ Subgroup.normalizer (V : Set G) := hLTV (Subgroup.mem_sup_left hl)
  have hlz : l * z * l⁻¹ = z := by
    have h1 : l * z * l⁻¹ ∈ fsuV1 T V := by
      rw [← hinf]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hlV z).mp hzV,
        (Subgroup.mem_normalizer_iff.mp hlN z).mp hz0⟩
    rcases hgen _ h1 with h | h
    · exfalso
      apply hz1
      calc z = l⁻¹ * (l * z * l⁻¹) * l := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hlN' : (⟨l, hl⟩ : ↥L) ∈ N.subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨hl, (mem_normalizer_iff_of_gen hzV1 hz1 hgen).mpr hlz⟩
  have hlC := hCuN hlN'
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hlC
  have hlu' : l * u * l⁻¹ = u := by
    rw [show l * u * l⁻¹ = (⟨l, hl⟩ : ↥L) * u * (l : G)⁻¹ from rfl, hlC, mul_inv_cancel_right]
  rw [hlu'] at hlu
  apply hz1
  calc z = u⁻¹ * (u * z) := by group
    _ = 1 := by rw [← hlu, inv_mul_cancel]

end Ctx72

end CFSG.Quasithin.H13.L32A
