module

public import CFSG.LocalAnalysis.StandardType.PhanELocalModels
import CFSG.LocalAnalysis.StandardType.PhanELocalPlane
import CFSG.LocalAnalysis.StandardType.PhanELocalGate

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

private theorem plc2_hle :
    ∀ i, i < ([0, 1, 2, 3] : List ℕ).length → ([0, 1, 2, 3] : List ℕ).getD i 0 ≤ 3 := by
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> decide

private theorem plc2_hmono :
    ∀ i, i + 1 < ([0, 1, 2, 3] : List ℕ).length →
      ([0, 1, 2, 3] : List ℕ).getD i 0 ≤ ([0, 1, 2, 3] : List ℕ).getD (i + 1) 0 := by
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  have hi' : i < 3 := by omega
  interval_cases i <;> decide

private theorem plc2_Vsub12 {K : Type} [Field K] : Vsub (K := K) 3 1 ≤ Vsub 3 2 :=
  Vsub_mono (K := K) (c := 1) (c' := 2) (by norm_num)

private theorem plc2_sup_eq_top_of_inf_eq_bot {K : Type} [Field K] [Finite K]
    {U W : Submodule K (Fin 3 → K)} (hd : U ⊓ W = ⊥) (hUW : finrank K U + finrank K W = 3) :
    U ⊔ W = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fin_fun]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [hd, finrank_bot, add_zero] at hsum
  exact hsum.trans hUW

private theorem plc2_sup_eq_top_of_not_le {K : Type} [Field K] [Finite K]
    {U W : Submodule K (Fin 3 → K)} (hW : finrank K W = 2) (h : ¬ U ≤ W) : U ⊔ W = ⊤ := by
  have hlt : W < U ⊔ W := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro heq
    exact h (le_sup_left.trans (le_of_eq heq.symm))
  have hdiff : finrank K W < finrank K ↥(U ⊔ W) := Submodule.finrank_lt_finrank_of_lt hlt
  have hle3 : finrank K ↥(U ⊔ W) ≤ 3 := by
    have := Submodule.finrank_le (U ⊔ W : Submodule K (Fin 3 → K))
    rwa [Module.finrank_fin_fun] at this
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fin_fun]
  omega

private theorem plc2_farSet_of_transversal {K : Type} [Field K] [Finite K] {x : FlagK K 3}
    (h1 : x.E 1 ⊓ Vsub 3 2 = ⊥) (h2 : x.E 2 ⊓ Vsub 3 1 = ⊥) :
    x ∈ farSet 3 [0, 1, 2, 3] := by
  have hle : ∀ i, i < ([0, 1, 2, 3] : List ℕ).length →
      ([0, 1, 2, 3] : List ℕ).getD i 0 ≤ 3 := plc2_hle
  have h11 : x.E 1 ⊓ Vsub 3 1 = ⊥ := by
    apply le_bot_iff.mp
    calc x.E 1 ⊓ Vsub 3 1 ≤ x.E 1 ⊓ Vsub 3 2 :=
          inf_le_inf_left _ (plc2_Vsub12 (K := K))
      _ = ⊥ := h1
  have hE1V2 : x.E 1 ⊔ Vsub 3 2 = ⊤ :=
    plc2_sup_eq_top_of_inf_eq_bot h1 (by
      rw [Plane.finrank_E_one x, finrank_Vsub (K := K) (n := 3) (c := 2) (by norm_num)])
  have hE2V1 : x.E 2 ⊔ Vsub 3 1 = ⊤ :=
    plc2_sup_eq_top_of_inf_eq_bot h2 (by
      rw [Plane.finrank_E_two x, finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)])
  have hnot : ¬ x.E 2 ≤ Vsub 3 2 := by
    intro hle2
    have heq : x.E 2 = Vsub 3 2 :=
      Submodule.eq_of_le_of_finrank_eq hle2 (by
        rw [Plane.finrank_E_two x, finrank_Vsub (K := K) (n := 3) (c := 2) (by norm_num)])
    have hV1 : Vsub (K := K) 3 1 ≤ Vsub 3 2 := plc2_Vsub12 (K := K)
    have hinf : x.E 2 ⊓ Vsub 3 1 = Vsub 3 1 := by
      rw [heq]
      exact inf_eq_right.mpr hV1
    have hzero : finrank K (Vsub (K := K) 3 1) = 0 := by
      rw [← hinf, h2, finrank_bot]
    rw [finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at hzero
    norm_num at hzero
  have hE2V2 : x.E 2 ⊔ Vsub 3 2 = ⊤ :=
    plc2_sup_eq_top_of_not_le (by rw [finrank_Vsub (K := K) (n := 3) (c := 2) (by norm_num)])
      hnot
  rw [mem_farSet_iff (K := K) (d := [0, 1, 2, 3]) hle]
  intro i hi j hj
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> interval_cases j <;>
    refine ⟨fun hij => ?_, fun hij => ?_⟩ <;>
    first
      | (exfalso; omega)
      | (simp_all [Vsub_zero, Vsub_self, x.E_zero, x.top, List.getD_cons_zero,
          List.getD_cons_succ])

private theorem plc2_mem_genSet_iff {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]
    {x : FlagK K 3} :
    x ∈ genSet K f 3 [0, 1, 2, 3] [] ↔
      x.E 1 ⊓ Vsub 3 2 = ⊥ ∧ x.E 2 ⊓ Vsub 3 1 = ⊥ := by
  have hle : ∀ i, i < ([0, 1, 2, 3] : List ℕ).length →
      ([0, 1, 2, 3] : List ℕ).getD i 0 ≤ 3 := plc2_hle
  have hmono : ∀ i, i + 1 < ([0, 1, 2, 3] : List ℕ).length →
      ([0, 1, 2, 3] : List ℕ).getD i 0 ≤ ([0, 1, 2, 3] : List ℕ).getD (i + 1) 0 := plc2_hmono
  constructor
  · intro hx
    simp only [genSet, Set.mem_setOf_eq] at hx
    have hfar := (mem_farSet_iff (K := K) (d := [0, 1, 2, 3]) hle).mp hx.1
    exact ⟨(hfar 2 (by decide) 1 (by decide)).1 (by decide),
      (hfar 1 (by decide) 2 (by decide)).1 (by decide)⟩
  · rintro ⟨h1, h2⟩
    simp only [genSet, Set.mem_setOf_eq]
    refine ⟨plc2_farSet_of_transversal h1 h2, ?_⟩
    intro i hi
    exact blockOK_of_size_one f hle hmono (plc2_farSet_of_transversal h1 h2) hi (by
      simp only [List.length_cons, List.length_nil] at hi
      have hi' : i < 3 := by omega
      interval_cases i <;> decide)

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem a2chamber_connected (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((flagSys K 2).restrict (genSet K f 3 [0, 1, 2, 3] [])).Connected := by
  apply Plane.connected_of_common_nbr
  intro x hx y hy
  rw [plc2_mem_genSet_iff] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hK' : 3 < Nat.card K := by
    rw [hK, pow_two]
    have h16 : 16 ≤ 2 ^ f * 2 ^ f := by
      have := Nat.mul_le_mul hq hq
      simpa using this
    omega
  have hproper2 : Vsub (K := K) 3 2 ≠ ⊤ := by
    intro htop
    have hd : finrank K (Vsub (K := K) 3 2) = 3 := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    rw [finrank_Vsub (K := K) (n := 3) (c := 2) (by norm_num)] at hd
    norm_num at hd
  have hproperx : x.E 1 ⊔ Vsub (K := K) 3 1 ≠ ⊤ := by
    intro htop
    have h11x : x.E 1 ⊓ Vsub (K := K) 3 1 = ⊥ := by
      apply le_bot_iff.mp
      calc x.E 1 ⊓ Vsub 3 1 ≤ x.E 1 ⊓ Vsub 3 2 :=
            inf_le_inf_left _ (plc2_Vsub12 (K := K))
        _ = ⊥ := hx1
    have hd : finrank K ↥(x.E 1 ⊔ Vsub (K := K) 3 1) = 3 := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    have hd2 : finrank K ↥(x.E 1 ⊔ Vsub (K := K) 3 1) = 2 := by
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq (x.E 1) (Vsub (K := K) 3 1)
      rw [h11x, finrank_bot, add_zero, Plane.finrank_E_one x,
        finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at hsum
      simpa using hsum
    omega
  have hpropery : y.E 1 ⊔ Vsub (K := K) 3 1 ≠ ⊤ := by
    intro htop
    have h11y : y.E 1 ⊓ Vsub (K := K) 3 1 = ⊥ := by
      apply le_bot_iff.mp
      calc y.E 1 ⊓ Vsub 3 1 ≤ y.E 1 ⊓ Vsub 3 2 :=
            inf_le_inf_left _ (plc2_Vsub12 (K := K))
        _ = ⊥ := hy1
    have hd : finrank K ↥(y.E 1 ⊔ Vsub (K := K) 3 1) = 3 := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    have hd2 : finrank K ↥(y.E 1 ⊔ Vsub (K := K) 3 1) = 2 := by
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq (y.E 1) (Vsub (K := K) 3 1)
      rw [h11y, finrank_bot, add_zero, Plane.finrank_E_one y,
        finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num)] at hsum
      simpa using hsum
    omega
  obtain ⟨v, hv1, hv2, hv3⟩ := exists_not_mem_union hK' (Vsub (K := K) 3 2)
    (x.E 1 ⊔ Vsub (K := K) 3 1) (y.E 1 ⊔ Vsub (K := K) 3 1) hproper2 hproperx hpropery
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv1 (Submodule.zero_mem _)
  let z : Submodule K (Fin 3 → K) := Submodule.span K {v}
  let m : Submodule K (Fin 3 → K) := x.E 1 ⊔ z
  let m' : Submodule K (Fin 3 → K) := y.E 1 ⊔ z
  have hz : finrank K z = 1 := finrank_span_singleton hv0
  have hzV2 : z ⊓ Vsub (K := K) 3 2 = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf] at hw
    obtain ⟨hwz, hwV⟩ := hw
    by_cases hw0 : w = 0
    · exact hw0
    · exfalso
      change w ∈ Submodule.span K {v} at hwz
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hwz
      have ha : a ≠ 0 := by
        rintro rfl
        exact hw0 (zero_smul K v)
      exact hv1 ((Submodule.smul_mem_iff (Vsub (K := K) 3 2) ha).mp hwV)
  have hmV1 : m ⊓ Vsub (K := K) 3 1 = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf] at hw
    obtain ⟨hwm, hwV⟩ := hw
    change w ∈ x.E 1 ⊔ Submodule.span K {v} at hwm
    rw [Submodule.mem_sup] at hwm
    obtain ⟨a, ha, b, hb, hab⟩ := hwm
    have hb_mem : b ∈ x.E 1 ⊔ Vsub (K := K) 3 1 := by
      have hb_eq : b = w - a := by rw [← hab]; abel
      rw [hb_eq]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right hwV) (Submodule.mem_sup_left ha)
    by_cases hb0 : b = 0
    · have hw_eq : w = a := by
        rw [hb0, add_zero] at hab
        exact hab.symm
      rw [hw_eq]
      have : a ∈ x.E 1 ⊓ Vsub (K := K) 3 2 :=
        ⟨ha, (plc2_Vsub12 (K := K)) (hw_eq ▸ hwV)⟩
      rw [hx1] at this
      exact (Submodule.mem_bot K).mp this
    · exfalso
      have hz_eq : z = Submodule.span K {b} :=
        eq_span_singleton_of_mem_of_finrank_eq_one hz hb hb0
      have hv_span : v ∈ Submodule.span K {b} := by
        rw [← hz_eq]
        exact Submodule.mem_span_singleton_self v
      have hb_le : Submodule.span K {b} ≤ x.E 1 ⊔ Vsub (K := K) 3 1 :=
        (Submodule.span_singleton_le_iff_mem b (x.E 1 ⊔ Vsub (K := K) 3 1)).mpr hb_mem
      exact hv2 (hb_le hv_span)
  have hm'V1 : m' ⊓ Vsub (K := K) 3 1 = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf] at hw
    obtain ⟨hwm, hwV⟩ := hw
    change w ∈ y.E 1 ⊔ Submodule.span K {v} at hwm
    rw [Submodule.mem_sup] at hwm
    obtain ⟨a, ha, b, hb, hab⟩ := hwm
    have hb_mem : b ∈ y.E 1 ⊔ Vsub (K := K) 3 1 := by
      have hb_eq : b = w - a := by rw [← hab]; abel
      rw [hb_eq]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right hwV) (Submodule.mem_sup_left ha)
    by_cases hb0 : b = 0
    · have hw_eq : w = a := by
        rw [hb0, add_zero] at hab
        exact hab.symm
      rw [hw_eq]
      have : a ∈ y.E 1 ⊓ Vsub (K := K) 3 2 :=
        ⟨ha, (plc2_Vsub12 (K := K)) (hw_eq ▸ hwV)⟩
      rw [hy1] at this
      exact (Submodule.mem_bot K).mp this
    · exfalso
      have hz_eq : z = Submodule.span K {b} :=
        eq_span_singleton_of_mem_of_finrank_eq_one hz hb hb0
      have hv_span : v ∈ Submodule.span K {b} := by
        rw [← hz_eq]
        exact Submodule.mem_span_singleton_self v
      have hb_le : Submodule.span K {b} ≤ y.E 1 ⊔ Vsub (K := K) 3 1 :=
        (Submodule.span_singleton_le_iff_mem b (y.E 1 ⊔ Vsub (K := K) 3 1)).mpr hb_mem
      exact hv3 (hb_le hv_span)
  have hm_dim : finrank K m = 2 := by
    have hvx : v ∉ x.E 1 := fun h => hv2 (Submodule.mem_sup_left h)
    change finrank K ↥(x.E 1 ⊔ Submodule.span K {v}) = 2
    rw [Submodule.finrank_sup_span_singleton hvx, Plane.finrank_E_one x]
  have hm'_dim : finrank K m' = 2 := by
    have hvy : v ∉ y.E 1 := fun h => hv3 (Submodule.mem_sup_left h)
    change finrank K ↥(y.E 1 ⊔ Submodule.span K {v}) = 2
    rw [Submodule.finrank_sup_span_singleton hvy, Plane.finrank_E_one y]
  have hchain_x : Plane.HasFl (genSet K f 3 [0, 1, 2, 3] []) (x.E 1) m :=
    Plane.hasFl_ofChain (Plane.finrank_E_one x) hm_dim le_sup_left (by
      rw [plc2_mem_genSet_iff]
      exact ⟨by rw [Plane.ofChain_E_one]; exact hx1,
        by rw [Plane.ofChain_E_two]; exact hmV1⟩)
  have hchain_zx : Plane.HasFl (genSet K f 3 [0, 1, 2, 3] []) z m :=
    Plane.hasFl_ofChain hz hm_dim le_sup_right (by
      rw [plc2_mem_genSet_iff]
      exact ⟨by rw [Plane.ofChain_E_one]; exact hzV2,
        by rw [Plane.ofChain_E_two]; exact hmV1⟩)
  have hchain_zy : Plane.HasFl (genSet K f 3 [0, 1, 2, 3] []) z m' :=
    Plane.hasFl_ofChain hz hm'_dim le_sup_right (by
      rw [plc2_mem_genSet_iff]
      exact ⟨by rw [Plane.ofChain_E_one]; exact hzV2,
        by rw [Plane.ofChain_E_two]; exact hm'V1⟩)
  have hchain_y : Plane.HasFl (genSet K f 3 [0, 1, 2, 3] []) (y.E 1) m' :=
    Plane.hasFl_ofChain (Plane.finrank_E_one y) hm'_dim le_sup_left (by
      rw [plc2_mem_genSet_iff]
      exact ⟨by rw [Plane.ofChain_E_one]; exact hy1,
        by rw [Plane.ofChain_E_two]; exact hm'V1⟩)
  exact ⟨z, m, m', hchain_x, hchain_zx, hchain_zy, hchain_y⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
