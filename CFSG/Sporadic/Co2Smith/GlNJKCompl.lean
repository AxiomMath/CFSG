module

public import CFSG.Sporadic.Co2Smith.GlNJKGroups

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] def set77 : Set (Fin 2300) := {y | (y : ℕ) ∈ Native.glNJO77}

theorem perm_set77_of_maps {σ : Equiv.Perm (Fin 2300)} (h : ∀ y ∈ set77, σ y ∈ set77) :
    σ • set77 = set77 := by
  have hsub : σ • set77 ⊆ set77 := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [Set.ncard_smul_set]

section Compl


@[expose] noncomputable def LK : Subgroup K := closure (Set.range fun k : Fin 3 => qK k)

@[expose] noncomputable def LKt : Subgroup K := closure (Set.range fun k : Fin 3 => qtK k)

@[expose] noncomputable def QKs (s : ℕ) : Subgroup K := closure {qK 0, jcElt s * qK 1}

theorem LK_le_N : LK ≤ normalizer (Jc : Set K) := by
  rw [LK, closure_le]
  rintro _ ⟨k, rfl⟩
  exact qK_mem_N k.2

theorem LKt_le_N : LKt ≤ normalizer (Jc : Set K) := by
  rw [LKt, closure_le]
  rintro _ ⟨k, rfl⟩
  exact qtK_mem_N k.2

theorem QKs_le_N (s : ℕ) : QKs s ≤ normalizer (Jc : Set K) := by
  rw [QKs, closure_le]
  rintro _ (rfl | rfl)
  · exact qK_mem_N (by norm_num)
  · exact mul_mem (le_normalizer (jcElt_mem s)) (qK_mem_N (by norm_num))

theorem QKs_le_Cz (s : ℕ) : QKs s ≤ Cz := by
  rw [QKs, closure_le]
  rintro _ (rfl | rfl)
  · exact qK_mem_Cz (by norm_num)
  · exact mul_mem (Jc_le_Cz (jcElt_mem s)) (qK_mem_Cz (by norm_num))

theorem QKs_zero_le_LK : QKs 0 ≤ LK := by
  rw [QKs, closure_le, jcElt_zero, one_mul]
  rintro _ (rfl | rfl)
  · exact subset_closure ⟨0, rfl⟩
  · exact subset_closure ⟨1, rfl⟩

theorem QKs_76_le_LKt : QKs 76 ≤ LKt := by
  rw [QKs, closure_le]
  rintro _ (rfl | rfl)
  · have e : qtK 0 = qK 0 := by
      rw [qtK, show Native.glNJTw[0]! = 0 from rfl, jcElt_zero, one_mul]
    rw [← e]
    exact subset_closure ⟨0, rfl⟩
  · have e : qtK 1 = jcElt 76 * qK 1 := by rw [qtK, show Native.glNJTw[1]! = 76 from rfl]
    rw [← e]
    exact subset_closure ⟨1, rfl⟩

theorem LK_inf_Jc {x : K} (hx : x ∈ LK) (hJ : x ∈ Jc) : x = 1 := by
  have hfix : LK ≤ (MulAction.stabilizer (Equiv.Perm (Fin 2300)) ptP).comap co2PermHom := by
    rw [LK, closure_le]
    rintro _ ⟨k, rfl⟩
    exact co2PermHom_apply_of_maps (qK_val k.2) (by norm_num) (by norm_num)
      (glNJPt_spec.1 k k.2)
  obtain ⟨m, hm, rfl⟩ := exists_coord hJ
  rw [jcElt_fix_ptP hm (hfix hx), jcElt_zero]

theorem LKt_inf_Jc {x : K} (hx : x ∈ LKt) (hJ : x ∈ Jc) : x = 1 := by
  have hfix : LKt ≤ (MulAction.stabilizer (Equiv.Perm (Fin 2300)) set77).comap co2PermHom := by
    rw [LKt, closure_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨hp, himg⟩ := glNJO77_spec.2.1 k k.2
    obtain ⟨-, hrep⟩ := rep_co2PermHom_of_permOK (qtK_val k.2) hp
    refine perm_set77_of_maps fun y hy => ?_
    show ((co2PermHom (qtK k) y : Fin 2300) : ℕ) ∈ Native.glNJO77
    rw [← hrep y]
    exact himg y hy
  obtain ⟨m, hm, rfl⟩ := exists_coord hJ
  by_contra h1
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact h1 jcElt_zero
  obtain ⟨hxw, hy, hny, hmaps⟩ := glNJO77_spec.2.2 m hm hm0
  have hxw2 : Native.glNJO77Wx[m]! < 2300 := glNJO77_spec.1 _ hxw
  have e := co2PermHom_apply_of_maps (jcElt_val m) hxw2 hy hmaps
  have hst : co2PermHom (jcElt m) • set77 = set77 := hfix hx
  have hmem : co2PermHom (jcElt m) ⟨_, hxw2⟩ ∈ co2PermHom (jcElt m) • set77 :=
    Set.smul_mem_smul_set (show (⟨_, hxw2⟩ : Fin 2300) ∈ set77 from hxw)
  rw [hst, e] at hmem
  exact hny hmem


theorem piK_zero_iff (x : normalizer (Jc : Set K)) : piK x 0 = 0 ↔ (x : K) ∈ Cz := by
  constructor
  · intro h
    have e := piK_spec x 0
    rw [h, omK_zero] at e
    refine mem_Cz_of_comm ?_
    calc (x : K) * z0 = (x : K) * z0 * (x : K)⁻¹ * x := by group
      _ = z0 * x := by rw [← e]
  · intro h
    apply omK_injective
    rw [piK_spec, omK_zero, comm_of_mem_Cz h, mul_inv_cancel_right]

theorem piK_inj_of_inf {L : Subgroup K} (hL : ∀ x ∈ L, x ∈ Jc → x = 1)
    {x y : normalizer (Jc : Set K)} (hx : (x : K) ∈ L) (hy : (y : K) ∈ L) (h : piK x = piK y) :
    x = y := by
  have h1 : piK (x * y⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := hL _ (L.mul_mem hx (L.inv_mem hy)) (mem_Jc_of_piK_eq_one h1)
  have h3 : x * y⁻¹ = 1 := Subtype.ext h2
  exact mul_inv_eq_one.1 h3

theorem exists_LK_piK {σ : Equiv.Perm (Fin 77)} (hσ : σ ∈ njAut) :
    ∃ x : normalizer (Jc : Set K), (x : K) ∈ LK ∧ piK x = σ := by
  have e := eq_njAut_of_gens (X := (LK.subgroupOf (normalizer (Jc : Set K))).map piK)
    (by rintro _ ⟨x, -, rfl⟩; exact piK_mem_njAut x) (fun i hi => ⟨qN i, ?_, rfl⟩)
  · rw [← e] at hσ
    obtain ⟨x, hx, rfl⟩ := hσ
    exact ⟨x, hx, rfl⟩
  · show (qN i : K) ∈ LK
    rw [qN_val hi]
    exact subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem piK_qtN {i : ℕ} (hi : i < 3) :
    piK ⟨qtK i, qtK_mem_N hi⟩ = piK (qN i) := by
  have e : (⟨qtK i, qtK_mem_N hi⟩ : normalizer (Jc : Set K)) =
      ⟨jcElt Native.glNJTw[i]!, le_normalizer (jcElt_mem _)⟩ * qN i := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, qN_val hi]
    rfl
  rw [e, map_mul, piK_Jc (jcElt_mem _), one_mul]

theorem exists_LKt_piK {σ : Equiv.Perm (Fin 77)} (hσ : σ ∈ njAut) :
    ∃ x : normalizer (Jc : Set K), (x : K) ∈ LKt ∧ piK x = σ := by
  have e := eq_njAut_of_gens (X := (LKt.subgroupOf (normalizer (Jc : Set K))).map piK)
    (by rintro _ ⟨x, -, rfl⟩; exact piK_mem_njAut x)
    (fun i hi => ⟨⟨qtK i, qtK_mem_N hi⟩, subset_closure ⟨⟨i, hi⟩, rfl⟩, piK_qtN hi⟩)
  rw [← e] at hσ
  obtain ⟨x, hx, rfl⟩ := hσ
  exact ⟨x, hx, rfl⟩

theorem exists_QKs_piK (s : ℕ) {σ : Equiv.Perm (Fin 77)} (hσ : σ ∈ njAut0) :
    ∃ x : normalizer (Jc : Set K), (x : K) ∈ QKs s ∧ piK x = σ := by
  have hle : PQ ≤ ((QKs s).subgroupOf (normalizer (Jc : Set K))).map piK := by
    rw [PQ, closure_le]
    rintro _ (rfl | rfl)
    · refine ⟨qN 0, ?_, rfl⟩
      show (qN 0 : K) ∈ QKs s
      rw [qN_val (by norm_num)]
      exact subset_closure (Set.mem_insert _ _)
    · refine ⟨⟨jcElt s * qK 1, QKs_le_N s (subset_closure (Set.mem_insert_of_mem _ rfl))⟩,
        subset_closure (Set.mem_insert_of_mem _ rfl), ?_⟩
      have e : (⟨jcElt s * qK 1, QKs_le_N s (subset_closure (Set.mem_insert_of_mem _ rfl))⟩ :
          normalizer (Jc : Set K)) = ⟨jcElt s, le_normalizer (jcElt_mem _)⟩ * qN 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, qN_val (by norm_num)]
      rw [e, map_mul, piK_Jc (jcElt_mem _), one_mul]
  rw [← PQ_eq_njAut0] at hσ
  obtain ⟨x, hx, rfl⟩ := hle hσ
  exact ⟨x, hx, rfl⟩

theorem LK_inf_Cz_le {x : K} (hx : x ∈ LK) (hz : x ∈ Cz) : x ∈ QKs 0 := by
  have hN := LK_le_N hx
  obtain ⟨y, hy, e⟩ := exists_QKs_piK 0
    (σ := piK ⟨x, hN⟩) ⟨piK_mem_njAut _, (piK_zero_iff ⟨x, hN⟩).2 hz⟩
  have := piK_inj_of_inf (fun _ h1 h2 => LK_inf_Jc h1 h2) (QKs_zero_le_LK hy) hx e
  rw [← show (y : K) = x from congrArg Subtype.val this]
  exact hy

theorem LKt_inf_Cz_le {x : K} (hx : x ∈ LKt) (hz : x ∈ Cz) : x ∈ QKs 76 := by
  have hN := LKt_le_N hx
  obtain ⟨y, hy, e⟩ := exists_QKs_piK 76
    (σ := piK ⟨x, hN⟩) ⟨piK_mem_njAut _, (piK_zero_iff ⟨x, hN⟩).2 hz⟩
  have := piK_inj_of_inf (fun _ h1 h2 => LKt_inf_Jc h1 h2) (QKs_76_le_LKt hy) hx e
  rw [← show (y : K) = x from congrArg Subtype.val this]
  exact hy

end Compl

end CFSG.Sporadic.Co2Smith
