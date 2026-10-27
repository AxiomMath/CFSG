module

public import CFSG.LocalAnalysis.StandardType.FF81.FrameSys
import CFSG.LocalAnalysis.StandardType.GGFFModelBasis
import CFSG.LocalAnalysis.StandardType.GGFFModelSL
import CFSG.LocalAnalysis.StandardType.GGFFSLSylow

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT
open CFSG.RankThree.PartTwo.Sec4.RonanK429F (W6.T W7.T)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)
open scoped MatrixGroups

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

private theorem w6_T_zero : W6.T 0 = tOne 5 := by
  apply Subtype.ext
  decide

private theorem w6_T_one :
    W6.T 1 = jBlock 5 (blockSL (ZMod 2) 4 2 0 (by omega) rhoTwo) := by
  apply Subtype.ext
  rw [jBlock, blockSL_comp_apply]
  decide

private theorem w6_T_two :
    W6.T 2 = jBlock 5 (blockSL (ZMod 2) 4 2 2 (by omega) rhoTwo) := by
  apply Subtype.ext
  rw [jBlock, blockSL_comp_apply]
  decide

private theorem w7_T_zero : W7.T 0 = tOne 6 := by
  apply Subtype.ext
  decide

private theorem w7_T_one :
    W7.T 1 = jBlock 6 (blockSL (ZMod 2) 5 2 0 (by omega) rhoTwo) := by
  apply Subtype.ext
  rw [jBlock, blockSL_comp_apply]
  decide

private theorem w7_T_two :
    W7.T 2 = jBlock 6 (blockSL (ZMod 2) 5 2 2 (by omega) rhoTwo) := by
  apply Subtype.ext
  rw [jBlock, blockSL_comp_apply]
  decide

@[expose] def pullSL (φ : ↥L ≃* SL(n + 1, ZMod 2)) (H : Subgroup SL(n + 1, ZMod 2)) :
    Subgroup G :=
  (H.map φ.symm.toMonoidHom).map L.subtype

theorem pullSL_le (φ : ↥L ≃* SL(n + 1, ZMod 2)) (H : Subgroup SL(n + 1, ZMod 2)) :
    pullSL φ H ≤ L := by
  rw [pullSL]
  exact Subgroup.map_subtype_le _

theorem mem_pullSL_iff (φ : ↥L ≃* SL(n + 1, ZMod 2)) (H : Subgroup SL(n + 1, ZMod 2)) (y : ↥L) :
    (y : G) ∈ pullSL φ H ↔ φ y ∈ H := by
  rw [pullSL]
  change L.subtype y ∈ Subgroup.map L.subtype (Subgroup.map φ.symm.toMonoidHom H) ↔ φ y ∈ H
  rw [Subgroup.mem_map_iff_mem (Subgroup.subtype_injective L)]
  simpa using (Subgroup.mem_map_equiv (f := φ.symm) (K := H) (x := y))

theorem pullSL_top (φ : ↥L ≃* SL(n + 1, ZMod 2)) : pullSL φ ⊤ = L := by
  rw [pullSL, Subgroup.map_top_of_surjective φ.symm.toMonoidHom φ.symm.surjective,
    Subgroup.map_top, Subgroup.range_subtype]

theorem a2System_pullSL {m : ℕ} {adj : Fin m → Fin m → Prop}
    {U : Fin m → Subgroup SL(n + 1, ZMod 2)} (h : A2System adj U ⊤)
    (φ : ↥L ≃* SL(n + 1, ZMod 2)) : A2System adj (fun i => pullSL φ (U i)) L := by
  have hinj : Function.Injective (L.subtype.comp φ.symm.toMonoidHom) :=
    (Subgroup.subtype_injective L).comp φ.symm.injective
  have hfun : (fun i => (U i).map (L.subtype.comp φ.symm.toMonoidHom)) =
      fun i => pullSL φ (U i) := by
    funext i
    rw [pullSL, ← Subgroup.map_map]
  have htop : (⊤ : Subgroup SL(n + 1, ZMod 2)).map
      (L.subtype.comp φ.symm.toMonoidHom) = L := by
    rw [← Subgroup.map_map,
      Subgroup.map_top_of_surjective φ.symm.toMonoidHom φ.symm.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  have := A2System.map h (L.subtype.comp φ.symm.toMonoidHom) hinj
  rwa [hfun, htop] at this

@[expose] def frameJ [NeZero n] (φ : ↥L ≃* SL(n + 1, ZMod 2)) : Subgroup G :=
  pullSL φ (jBlock n).range

private theorem exists_mulEquiv_of_tor_eq {m : ℕ} [NeZero m]
    (e : ↥L ≃* SL(m + 1, ZMod 2)) {z : Fin 3 → ↥L} (hz : GGFF.Model ↥L z)
    {w : Fin 3 → SL(m + 1, ZMod 2)} (hw : GGFF.Model SL(m + 1, ZMod 2) w) :
    ∃ φ : ↥L ≃* SL(m + 1, ZMod 2), ∀ i, φ (z i) = w i := by
  have hz' : GGFF.Model SL(m + 1, ZMod 2) (fun i => e (z i)) := hz.ofMulEquiv e
  obtain ⟨g, hg⟩ := hw.torus (GGFF.tor (fun i => e (z i)))
    hz'.isElemAbelian_tor' hz'.card_tor'
  have hwg : GGFF.Model SL(m + 1, ZMod 2) (fun i => g * w i * g⁻¹) := hw.conj g
  have hmap : ∀ v, vecElt (fun i => g * w i * g⁻¹) v = g * vecElt w v * g⁻¹ :=
    fun v => by simpa [MulAut.conj_apply] using GGFF.vecElt_map (MulAut.conj g) w v
  have htor : ∀ x, (∃ v, x = vecElt (fun i => e (z i)) v) ↔
      ∃ v, x = vecElt (fun i => g * w i * g⁻¹) v := by
    intro x
    constructor
    · intro hx
      obtain ⟨v, hv⟩ := (hg x).mp ((hz'.mem_tor').mpr hx)
      exact ⟨v, by rw [hmap, hv]⟩
    · intro hx
      obtain ⟨v, hv⟩ := hx
      have hx' : x = g * vecElt w v * g⁻¹ := by rw [hv, hmap]
      exact (hz'.mem_tor').mp ((hg x).mpr ⟨v, hx'⟩)
  obtain ⟨h, hh⟩ := GGFF.Model.exists_conj_of_tor_eq hz' hwg htor
  refine ⟨e.trans (MulAut.conj (h * g)).symm, fun i => ?_⟩
  apply (MulAut.conj (h * g)).injective
  rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, hh i]
  simp only [MulAut.conj_apply]
  group

theorem exists_frameModel (hn : n = 5 ∨ n = 6) [NeZero n]
    (hL : Nonempty (↥L ≃* SL(n + 1, ZMod 2))) {z : Fin 3 → ↥L} (hz : GGFF.Model ↥L z) :
    ∃ φ : ↥L ≃* SL(n + 1, ZMod 2), φ (z 0) = tOne n ∧ φ (z 1) ∈ (jBlock n).range ∧
      φ (z 2) ∈ (jBlock n).range := by
  obtain ⟨e⟩ := hL
  rcases hn with rfl | rfl
  · obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_tor_eq e hz GGFF.model_SL6
    refine ⟨φ, ?_, ?_, ?_⟩
    · rw [hφ 0, w6_T_zero]
    · rw [hφ 1, w6_T_one]
      exact ⟨_, rfl⟩
    · rw [hφ 2, w6_T_two]
      exact ⟨_, rfl⟩
  · obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_tor_eq e hz GGFF.model_SL7
    refine ⟨φ, ?_, ?_, ?_⟩
    · rw [hφ 0, w7_T_zero]
    · rw [hφ 1, w7_T_one]
      exact ⟨_, rfl⟩
    · rw [hφ 2, w7_T_two]
      exact ⟨_, rfl⟩

theorem commute_of_mem_frameJ [NeZero n] {φ : ↥L ≃* SL(n + 1, ZMod 2)}
    {w : ↥L} (hw : φ w = tOne n) {j : G} (hj : j ∈ frameJ φ) : (w : G) * j = j * w := by
  obtain ⟨j', hj'⟩ : ∃ j' : ↥L, (j' : G) = j :=
    ⟨⟨j, pullSL_le φ _ (by simpa [frameJ] using hj)⟩, rfl⟩
  have hmem : φ j' ∈ (jBlock n).range := by
    rw [← mem_pullSL_iff]
    simpa [frameJ, ← hj'] using hj
  obtain ⟨B, hB⟩ := hmem
  have hcomm : w * j' = j' * w := by
    apply φ.injective
    rw [map_mul, map_mul, hw, ← hB]
    exact blockSL2_zero_mul_jBlock n rhoTwo B
  rw [← hj']
  simpa using congrArg Subtype.val hcomm

theorem mem_centralizer_iff_of_eq_tOne [NeZero n] {φ : ↥L ≃* SL(n + 1, ZMod 2)} {w : ↥L}
    (hw : φ w = tOne n) (y : ↥L) :
    y * w = w * y ↔ ∃ a : ℕ, ∃ j ∈ frameJ φ, (y : G) = (w : G) ^ a * j := by
  constructor
  · intro hc
    have hc' : φ y * tOne n = tOne n * φ y := by
      rw [← hw, ← map_mul, ← map_mul, hc]
    obtain ⟨a, B, hB⟩ := (mem_centralizer_tOne_iff (n := n)).mp hc'
    refine ⟨a, (φ.symm (jBlock n B) : ↥L), ?_, ?_⟩
    · rw [frameJ, mem_pullSL_iff]
      simp
    · have hy : y = w ^ a * φ.symm (jBlock n B) := by
        apply φ.injective
        simp only [map_mul, map_pow, hw, hB, MulEquiv.apply_symm_apply]
      rw [hy]
      simp
  · rintro ⟨a, j, hj, hy⟩
    apply Subtype.ext
    change (y : G) * (w : G) = (w : G) * (y : G)
    rw [hy]
    have hcomm := commute_of_mem_frameJ hw hj
    calc ((w : G) ^ a * j) * (w : G)
        = (w : G) ^ a * ((w : G) * j) := by rw [mul_assoc, ← hcomm]
      _ = (w : G) * ((w : G) ^ a * j) := by group

end CFSG.StandardType.FF81
