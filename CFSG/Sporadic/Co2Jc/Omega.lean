module

public import CFSG.Sporadic.Co2Jc.Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Descend

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith Subgroup
open CFSG.EvenSporadicStandard.Co2Std.Exclusion


@[expose] def O1 : Set ↥Jc := {x | ∃ k : Fin 77, (x : K) = omK k}

theorem tA_mem_O1 : tA ∈ O1 := by
  refine ⟨0, ?_⟩
  rw [coe_tA, omK_zero]

theorem jcA_mem_O1_iff {m : ℕ} (hm : m < 1024) : jcA m ∈ O1 ↔ m ∈ Native.glNJOm := by
  rw [O1]
  simp only [Set.mem_setOf_eq, coe_jcA]
  constructor
  · rintro ⟨k, hk⟩
    exact (jcElt_mem_range_omK hm).1 ⟨k, hk.symm⟩
  · intro h
    obtain ⟨k, hk⟩ := (jcElt_mem_range_omK hm).2 h
    exact ⟨k, hk.symm⟩

theorem ncard_O1 : O1.ncard = 77 := by
  have hO : O1 = Set.range (fun k : Fin 77 => (⟨omK k, omK_mem_Jc k⟩ : ↥Jc)) := by
    ext x
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk.symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, rfl⟩
  rw [hO, Set.ncard_range_of_injective]
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  · intro a b h
    exact omK_injective (congrArg Subtype.val h)

theorem closure_O1 : Subgroup.closure O1 = ⊤ := by
  have hO : O1 = Subgroup.subtype Jc ⁻¹' Set.range omK := by
    ext x
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, hk.symm⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, hk.symm⟩
  rw [hO, closure_preimage_omK]

theorem apply_mem_O1 {g : MulAut ↥Jc} (hg : g ∈ Qj) {x : ↥Jc} (hx : x ∈ O1) : g x ∈ O1 := by
  obtain ⟨k, hk⟩ := hx
  rw [Qj, autImage] at hg
  obtain ⟨y, rfl⟩ := hg
  refine ⟨piK ⟨(y : K), y.2.2⟩ k, ?_⟩
  rw [conjN_apply, hk]
  exact (piK_spec ⟨(y : K), y.2.2⟩ k).symm

theorem exists_apply_tA_eq {x : ↥Jc} (hx : x ∈ O1) : ∃ g ∈ Qj, g tA = x := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨ℓ, hℓ, hconj⟩ := exists_LK_conj_eq_omK k
  refine ⟨conjN (⊤ : Subgroup K) Jc ⟨ℓ, ⟨Subgroup.mem_top ℓ, LK_le_normalizer hℓ⟩⟩, ?_, ?_⟩
  · rw [Qj, autImage]
    exact ⟨_, rfl⟩
  · apply Subtype.ext
    rw [conjN_apply, coe_tA]
    change ℓ * z0 * ℓ⁻¹ = (x : K)
    rw [hconj, hk]

theorem mem_Qj_of_preserves {g : MulAut ↥Jc} (hg : ∀ x ∈ O1, g x ∈ O1) : g ∈ Qj := by
  obtain ⟨ℓ, hℓ, hℓg⟩ := exists_LK_of_preserves g (fun k : Fin 77 => by
    have hkO : (⟨omK k, omK_mem_Jc k⟩ : ↥Jc) ∈ O1 := ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := hg _ hkO
    exact ⟨k', hk'⟩)
  rw [Qj, autImage]
  refine ⟨⟨ℓ, ⟨Subgroup.mem_top ℓ, LK_le_normalizer hℓ⟩⟩, ?_⟩
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  rw [conjN_apply]
  change ℓ * (a : K) * ℓ⁻¹ = ((g a : Jc) : K)
  exact (hℓg a).symm

private theorem normalizerMonoidHom_eq_one_of_mem_Jc {n : normalizer (Jc : Set K)}
    (hn : (n : K) ∈ Jc) : Jc.normalizerMonoidHom n = 1 := by
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
  rw [Subgroup.mem_subgroupOf]
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Jc_comm hn hz).symm

private theorem normalizerMonoidHom_qN {k : ℕ} (hk : k < 3) :
    Jc.normalizerMonoidHom (qN k) = qA k := by
  rw [qA, dif_pos hk]
  have hq : qN k = (⟨qK k, qK_mem_N hk⟩ : normalizer (Jc : Set K)) := Subtype.ext (qN_val hk)
  rw [hq]

private theorem normalizerMonoidHom_mem_closure_of_piK_mem {n : normalizer (Jc : Set K)}
    (hn : piK n ∈ Subgroup.closure ({piK (qN 0), piK (qN 1)} : Set (Equiv.Perm (Fin 77)))) :
    Jc.normalizerMonoidHom n ∈ Subgroup.closure ({qA 0, qA 1} : Set (MulAut ↥Jc)) := by
  let C : Subgroup (MulAut ↥Jc) := Subgroup.closure ({qA 0, qA 1} : Set (MulAut ↥Jc))
  have hq0 : Jc.normalizerMonoidHom (qN 0) ∈ C := by
    rw [normalizerMonoidHom_qN (by norm_num)]
    exact Subgroup.subset_closure (by simp)
  have hq1 : Jc.normalizerMonoidHom (qN 1) ∈ C := by
    rw [normalizerMonoidHom_qN (by norm_num)]
    exact Subgroup.subset_closure (by simp)
  have key : ∀ σ ∈ Subgroup.closure ({piK (qN 0), piK (qN 1)} : Set (Equiv.Perm (Fin 77))),
      ∀ m : normalizer (Jc : Set K), piK m = σ → Jc.normalizerMonoidHom m ∈ C := by
    intro σ hσ
    refine Subgroup.closure_induction_left
      (s := ({piK (qN 0), piK (qN 1)} : Set (Equiv.Perm (Fin 77)))) ?one ?mul ?inv hσ
    · intro m hm
      rw [normalizerMonoidHom_eq_one_of_mem_Jc (mem_Jc_of_piK_eq_one hm)]
      exact C.one_mem
    · intro x hx y hy ih m hm
      rcases (by simpa using hx : x = piK (qN 0) ∨ x = piK (qN 1)) with rfl | rfl
      · have hm' : piK ((qN 0)⁻¹ * m) = y := by
          rw [map_mul, map_inv, hm]
          group
        have hih := ih ((qN 0)⁻¹ * m) hm'
        have hdec : Jc.normalizerMonoidHom m =
            Jc.normalizerMonoidHom (qN 0) * Jc.normalizerMonoidHom ((qN 0)⁻¹ * m) := by
          have hprod : qN 0 * ((qN 0)⁻¹ * m) = m := by group
          calc
            Jc.normalizerMonoidHom m =
                Jc.normalizerMonoidHom (qN 0 * ((qN 0)⁻¹ * m)) := by rw [hprod]
            _ = Jc.normalizerMonoidHom (qN 0) *
                Jc.normalizerMonoidHom ((qN 0)⁻¹ * m) := by rw [map_mul]
        rw [hdec]
        exact C.mul_mem hq0 hih
      · have hm' : piK ((qN 1)⁻¹ * m) = y := by
          rw [map_mul, map_inv, hm]
          group
        have hih := ih ((qN 1)⁻¹ * m) hm'
        have hdec : Jc.normalizerMonoidHom m =
            Jc.normalizerMonoidHom (qN 1) * Jc.normalizerMonoidHom ((qN 1)⁻¹ * m) := by
          have hprod : qN 1 * ((qN 1)⁻¹ * m) = m := by group
          calc
            Jc.normalizerMonoidHom m =
                Jc.normalizerMonoidHom (qN 1 * ((qN 1)⁻¹ * m)) := by rw [hprod]
            _ = Jc.normalizerMonoidHom (qN 1) *
                Jc.normalizerMonoidHom ((qN 1)⁻¹ * m) := by rw [map_mul]
        rw [hdec]
        exact C.mul_mem hq1 hih
    · intro x hx y hy ih m hm
      rcases (by simpa using hx : x = piK (qN 0) ∨ x = piK (qN 1)) with rfl | rfl
      · have hm' : piK (qN 0 * m) = y := by
          rw [map_mul, hm]
          group
        have hih := ih (qN 0 * m) hm'
        have hdec : Jc.normalizerMonoidHom m =
            (Jc.normalizerMonoidHom (qN 0))⁻¹ * Jc.normalizerMonoidHom (qN 0 * m) := by
          have hprod : (qN 0)⁻¹ * (qN 0 * m) = m := by group
          calc
            Jc.normalizerMonoidHom m =
                Jc.normalizerMonoidHom ((qN 0)⁻¹ * (qN 0 * m)) := by rw [hprod]
            _ = Jc.normalizerMonoidHom (qN 0)⁻¹ *
                Jc.normalizerMonoidHom (qN 0 * m) := by rw [map_mul]
        rw [hdec]
        exact C.mul_mem (C.inv_mem hq0) hih
      · have hm' : piK (qN 1 * m) = y := by
          rw [map_mul, hm]
          group
        have hih := ih (qN 1 * m) hm'
        have hdec : Jc.normalizerMonoidHom m =
            (Jc.normalizerMonoidHom (qN 1))⁻¹ * Jc.normalizerMonoidHom (qN 1 * m) := by
          have hprod : (qN 1)⁻¹ * (qN 1 * m) = m := by group
          calc
            Jc.normalizerMonoidHom m =
                Jc.normalizerMonoidHom ((qN 1)⁻¹ * (qN 1 * m)) := by rw [hprod]
            _ = Jc.normalizerMonoidHom (qN 1)⁻¹ *
                Jc.normalizerMonoidHom (qN 1 * m) := by rw [map_mul]
        rw [hdec]
        exact C.mul_mem (C.inv_mem hq1) hih
  exact key (piK n) hn n rfl

theorem mem_closure_of_apply_tA {g : MulAut ↥Jc} (hg : g ∈ Qj) (ht : g tA = tA) :
    g ∈ Subgroup.closure {qA 0, qA 1} := by
  rw [Qj, autImage] at hg
  obtain ⟨y, rfl⟩ := hg
  let n : normalizer (Jc : Set K) := ⟨(y : K), y.2.2⟩
  have hg_eq : conjN (⊤ : Subgroup K) Jc y = Jc.normalizerMonoidHom n := rfl
  have ht' : Jc.normalizerMonoidHom n tA = tA := by
    rw [← hg_eq]
    exact ht
  have hz : (n : K) * z0 * (n : K)⁻¹ = z0 := by
    simpa [coe_tA] using congrArg Subtype.val ht'
  have hp0 : piK n 0 = 0 := by
    apply omK_injective
    rw [piK_spec, omK_zero, hz]
  have hPQ : piK n ∈ PQ := by
    rw [PQ_eq_njAut0]
    exact ⟨piK_mem_njAut n, hp0⟩
  have hmem : piK n ∈ Subgroup.closure ({piK (qN 0), piK (qN 1)} : Set (Equiv.Perm (Fin 77))) := by
    simpa [PQ] using hPQ
  rw [hg_eq]
  exact normalizerMonoidHom_mem_closure_of_piK_mem hmem

theorem card_Qj : Nat.card Qj = 887040 := by
  have hrange : Qj = Jc.normalizerMonoidHom.range := by
    rw [Qj, autImage]
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion inf_le_right y, rfl⟩
    · rintro ⟨n, rfl⟩
      refine ⟨⟨(n : K), ⟨Subgroup.mem_top _, n.2⟩⟩, ?_⟩
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      rw [conjN_apply]
      rfl
  have hker : Jc.normalizerMonoidHom.ker = Jc.subgroupOf (normalizer (Jc : Set K)) := by
    rw [Subgroup.normalizerMonoidHom_ker]
    ext n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hcent
      exact centralizer_Jc_le hcent
    · intro hJ
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Jc_comm hJ hz).symm
  have hcard_ker : Nat.card Jc.normalizerMonoidHom.ker = 1024 := by
    rw [hker]
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (Subgroup.le_normalizer : Jc ≤ normalizer (Jc : Set K))).toEquiv]
    rw [card_Jc]
  have hquot : Nat.card (↥(normalizer (Jc : Set K)) ⧸ Jc.normalizerMonoidHom.ker) =
      Nat.card Qj := by
    calc
      Nat.card (↥(normalizer (Jc : Set K)) ⧸ Jc.normalizerMonoidHom.ker) =
          Nat.card (Jc.normalizerMonoidHom.range : Subgroup (MulAut ↥Jc)) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange Jc.normalizerMonoidHom).toEquiv
      _ = Nat.card Qj := by rw [hrange]
  have hOS := Subgroup.card_eq_card_quotient_mul_card_subgroup Jc.normalizerMonoidHom.ker
  rw [hquot, hcard_ker, card_normalizer_Jc] at hOS
  omega

end CFSG.Sporadic.Co2Jc
