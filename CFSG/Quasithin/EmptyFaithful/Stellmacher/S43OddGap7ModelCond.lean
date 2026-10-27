module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7ModelData
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7SqB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod Equiv
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Gap7

namespace Model

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Data

variable {ρ : Geo H M} (d : Data ρ)

omit [Finite G] in
theorem a_mem : d.pt 1 ∈ Vn d.δ₀ := d.pt_mem_V0 (one_mem S5Syl)

omit [Finite G] in
theorem b_mem : d.pt S5g ∈ Vn d.δ₀ := d.pt_mem_V0 S5g_mem_S5Syl

theorem a_not_mem (hy : Hyp S ρ) : d.pt 1 ∉ Zv ρ := d.pt_not_mem hy 1

theorem b_not_mem (hy : Hyp S ρ) : d.pt S5g ∉ Zv ρ := d.pt_not_mem hy S5g

theorem ab_not_mem (hy : Hyp S ρ) : d.pt 1 * (d.pt S5g)⁻¹ ∉ Zv ρ := by
  intro h
  obtain ⟨z, hz, e⟩ := d.pt_That hy (one_mem S5That)
  apply d.hgu
  have e' : ⁅d.u, (dictLift d.D S5g : G)⁆ = z⁻¹ * (d.pt 1 * (d.pt S5g)⁻¹) := by
    rw [e, commutatorElement_def]
    unfold pt
    group
  rw [e']
  exact (Zv ρ).mul_mem ((Zv ρ).inv_mem hz) h

theorem Vn_le (hy : Hyp S ρ) : Vn d.δ₀ ≤ Zv ρ ⊔ Subgroup.closure {d.pt 1, d.pt S5g} :=
  hy.Vn_le_sup_closure d.hδ₀ d.a_mem d.b_mem (d.a_not_mem hy) (d.b_not_mem hy)
    (d.ab_not_mem hy)

theorem Yv_eq (hy : Hyp S ρ) : Yv d.δ₀ = Y0.map d.D.φ := by
  rw [hy.hs.Yv_eq_comm_comm hy.hA hy.h26 (hy.vtype_nbr d.hδ₀) (nbrs_symm d.hδ₀),
    d.D.comm_comm_eq]
  rfl

theorem form_mem_iff (hy : Hyp S ρ) (h h' : Perm (Fin 5)) :
    d.form h h' ∈ Y0 ↔ ⁅d.pt h, d.pt h'⁆ ∈ Yv d.δ₀ := by
  rw [d.Yv_eq hy]
  exact dictPre_mem_iff d.D (d.comm_pt_mem hy h h')

theorem form_mul_inv_mem_iff (hy : Hyp S ρ) (h k h' k' : Perm (Fin 5)) :
    d.form h k * (d.form h' k')⁻¹ ∈ Y0 ↔
      ⁅d.pt h, d.pt k⁆ * ⁅d.pt h', d.pt k'⁆⁻¹ ∈ Yv d.δ₀ := by
  have e : d.form h k * (d.form h' k')⁻¹ =
      dictPre d.D (⁅d.pt h, d.pt k⁆ * ⁅d.pt h', d.pt k'⁆⁻¹) := by
    rw [dictPre_mul d.D (d.comm_pt_mem hy h k) ((Zv ρ).inv_mem (d.comm_pt_mem hy h' k')),
      dictPre_inv d.D (d.comm_pt_mem hy h' k')]
    rfl
  rw [e, d.Yv_eq hy]
  exact dictPre_mem_iff d.D ((Zv ρ).mul_mem (d.comm_pt_mem hy h k)
    ((Zv ρ).inv_mem (d.comm_pt_mem hy h' k')))

theorem pcond (hy : Hyp S ρ) : PCond d.form := by
  refine ⟨fun h h' => ?_, fun h hn => ?_⟩
  · simp only [d.form_mem_iff hy, d.form_mul_inv_mem_iff hy]
    exact hy.pcond_one d.hδ₀ d.a_mem d.b_mem (d.pt_mem_Wn hy h) (d.pt_mem_Wn hy h')
  · simp only [d.form_mem_iff hy, d.form_mul_inv_mem_iff hy] at hn ⊢
    exact hy.pcond_two d.hδ₀ d.a_mem d.b_mem (d.a_not_mem hy) (d.b_not_mem hy)
      (d.ab_not_mem hy) (d.pt_mem_Wn hy h) hn

theorem k2cond (hy : Hyp S ρ) : K2Cond d.form := by
  intro x h1 h2
  have hc : ∀ h h', d.D.φ (d.form h h') = ⁅d.pt h, d.pt h'⁆ := d.φ_form hy
  have hcen : ∀ h w, d.pt h * d.D.φ w = d.D.φ w * d.pt h := fun h w =>
    hy.cen (d.pt_mem_Qv hy h) (d.D.φ_mem w)
  have hPW : (x.map d.pt).prod ∈ Wn ρ := (Wn ρ).list_prod_mem (by
    intro y hy'
    obtain ⟨h, -, rfl⟩ := List.mem_map.mp hy'
    exact d.pt_mem_Wn hy h)
  have hPa : ⁅(x.map d.pt).prod, d.pt 1⁆ = 1 := by
    rw [comm_prod_left d.D.φ d.pt d.form hc hcen 1 x, h1, map_one]
  have hPb : ⁅(x.map d.pt).prod, d.pt S5g⁆ = 1 := by
    rw [comm_prod_left d.D.φ d.pt d.form hc hcen S5g x, h2, map_one]
  have hcent : Zv ρ ⊔ Subgroup.closure {d.pt 1, d.pt S5g} ≤
      Subgroup.centralizer {(x.map d.pt).prod} := by
    refine sup_le (fun z hz => ?_) ((Subgroup.closure_le _).mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hy.cen (hy.Wn_le_Qv hPW) hz).symm
    · rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((commutatorElement_eq_one_iff_mul_comm).mp hPa).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((commutatorElement_eq_one_iff_mul_comm).mp hPb).symm
  have hsq := sq_mem_Yv_of_centralizes hy.hA hy.h26 hy.hs hy.h3 hy.hρ hy.hS d.hδ₀ hPW
    (fun v hv => (Subgroup.mem_centralizer_singleton_iff.mp (hcent (d.Vn_le hy hv))).symm)
  have e := sq_prod_eq_qList d.D.φ d.pt d.form hc hcen (d.pt_sq hy) x
  rw [e, d.Yv_eq hy] at hsq
  exact (Subgroup.mem_map_iff_mem d.D.inj).mp hsq

theorem conj_cases (hy : Hyp S ρ) {q : G} (hqρ : q ∈ stab ρ) (hqδ : q ∈ stab d.δ₀) :
    (∃ z ∈ Zv ρ, q * d.pt 1 * q⁻¹ = z * d.pt 1 ∧
        ∃ z' ∈ Zv ρ, q * d.pt S5g * q⁻¹ = z' * d.pt S5g) ∨
      (∃ z ∈ Zv ρ, q * d.pt 1 * q⁻¹ = z * d.pt S5g ∧
        ∃ z' ∈ Zv ρ, q * d.pt S5g * q⁻¹ = z' * d.pt 1) := by
  have hk : d.D.ψ ⟨q, hqρ⟩ ∈ S5Syl := (d.D.mem_S_iff ⟨q, hqρ⟩).mp ⟨hqρ, hqδ⟩
  obtain ⟨z1, hz1, e1⟩ := d.pt_conj hy ⟨q, hqρ⟩ 1
  obtain ⟨z2, hz2, e2⟩ := d.pt_conj hy ⟨q, hqρ⟩ S5g
  rw [mul_one] at e1
  dsimp only at e1 e2
  set k := d.D.ψ ⟨q, hqρ⟩ with hkdef
  have f1 : q * d.pt 1 * q⁻¹ = z1⁻¹ * d.pt k := by rw [e1]; group
  have f2 : q * d.pt S5g * q⁻¹ = z2⁻¹ * d.pt (k * S5g) := by rw [e2]; group
  rcases S5Syl_cases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    obtain ⟨y1, hy1, g1⟩ := d.pt_mul_That hy 1 h1
    obtain ⟨y2, hy2, g2⟩ := d.pt_mul_That hy S5g h2
    rw [one_mul] at g1
    rw [show S5g * (S5g⁻¹ * k * S5g) = k * S5g by group] at g2
    refine ⟨z1⁻¹ * y1, (Zv ρ).mul_mem ((Zv ρ).inv_mem hz1) hy1, ?_,
      z2⁻¹ * y2, (Zv ρ).mul_mem ((Zv ρ).inv_mem hz2) hy2, ?_⟩
    · rw [f1, g1, mul_assoc]
    · rw [f2, g2, mul_assoc]
  · right
    obtain ⟨y1, hy1, g1⟩ := d.pt_mul_That hy S5g h1
    obtain ⟨y2, hy2, g2⟩ := d.pt_mul_That hy 1 h2
    rw [show S5g * (S5g⁻¹ * k) = k by group] at g1
    rw [one_mul] at g2
    refine ⟨z1⁻¹ * y1, (Zv ρ).mul_mem ((Zv ρ).inv_mem hz1) hy1, ?_,
      z2⁻¹ * y2, (Zv ρ).mul_mem ((Zv ρ).inv_mem hz2) hy2, ?_⟩
    · rw [f1, g1, mul_assoc]
    · rw [f2, g2, mul_assoc]

theorem Vst_le (hy : Hyp S ρ) : Vst d.δ₀ ≤ Subgroup.closure {d.pt 1 * d.pt S5g} ⊔ Zv ρ := by
  set P : Subgroup G := Subgroup.closure {d.pt 1 * d.pt S5g} ⊔ Zv ρ with hP
  have ha := d.a_mem
  have hb := d.b_mem
  have hZP : Zv ρ ≤ P := le_sup_right
  have habP : d.pt 1 * d.pt S5g ∈ P :=
    (le_sup_left : Subgroup.closure _ ≤ P) (Subgroup.subset_closure rfl)
  have hbinv : (d.pt S5g)⁻¹ = d.pt S5g := inv_eq_of_mul_eq_one_right (hy.Vn_sq hb)
  have hainv : (d.pt 1)⁻¹ = d.pt 1 := inv_eq_of_mul_eq_one_right (hy.Vn_sq ha)
  rw [Vst, Subgroup.commutator_le]
  intro v hv q hq
  have hρδ : ρ ∈ nbrs d.δ₀ := nbrs_symm d.hδ₀
  have hqρ : q ∈ stab ρ := Qv_le_stab_of_mem_nbrs hy.hA hρδ hq
  have hqδ : q ∈ stab d.δ₀ := pCoreOf_le 2 _ hq
  have hqV : ∀ w ∈ Vn d.δ₀, ⁅w, q⁆ ∈ Vn d.δ₀ := fun w hw => by
    have e : ⁅w, q⁆ = w * (q * w⁻¹ * q⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (Vn _).mul_mem hw (conj_mem_Vn hqδ ((Vn _).inv_mem hw))
  have hcomm : ∀ x y z : G, q * x * q⁻¹ = z * y → ⁅x, q⁆ = x * y⁻¹ * z⁻¹ := by
    intro x y z e
    have e' : q * x⁻¹ * q⁻¹ = (z * y)⁻¹ := by rw [← e]; group
    calc ⁅x, q⁆ = x * (q * x⁻¹ * q⁻¹) := by rw [commutatorElement_def]; group
      _ = x * y⁻¹ * z⁻¹ := by rw [e']; group
  let N : Subgroup G :=
    { carrier := {w | w ∈ Vn d.δ₀ ∧ ⁅w, q⁆ ∈ P}
      one_mem' := ⟨(Vn _).one_mem, by rw [commutatorElement_one_left]; exact P.one_mem⟩
      mul_mem' := by
        rintro w w' ⟨hw, hwP⟩ ⟨hw', hwP'⟩
        refine ⟨(Vn _).mul_mem hw hw', ?_⟩
        rw [comm_mul_left_eq, hy.Vn_comm hw (hqV w' hw'), mul_inv_cancel_right]
        exact P.mul_mem hwP' hwP
      inv_mem' := by
        rintro w ⟨hw, hwP⟩
        refine ⟨(Vn _).inv_mem hw, ?_⟩
        rw [comm_inv_left_eq, hy.Vn_comm ((Vn _).inv_mem hw) ((Vn _).inv_mem (hqV w hw)),
          inv_mul_cancel_right]
        exact P.inv_mem hwP }
  have hZN : Zv ρ ≤ N := fun z hz => ⟨Sit43.Zv_le_Vn d.hδ₀ hz, hZP (by
    have e : ⁅z, q⁆ = z * (q * z⁻¹ * q⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (Zv ρ).mul_mem hz (hy.conj_mem_Zv hqρ ((Zv ρ).inv_mem hz)))⟩
  have hab : d.pt 1 ∈ N ∧ d.pt S5g ∈ N := by
    rcases d.conj_cases hy hqρ hqδ with ⟨z, hz, e, z', hz', e'⟩ | ⟨z, hz, e, z', hz', e'⟩
    · refine ⟨⟨ha, ?_⟩, ⟨hb, ?_⟩⟩
      · rw [hcomm _ _ _ e, mul_inv_cancel, one_mul]
        exact hZP ((Zv ρ).inv_mem hz)
      · rw [hcomm _ _ _ e', mul_inv_cancel, one_mul]
        exact hZP ((Zv ρ).inv_mem hz')
    · refine ⟨⟨ha, ?_⟩, ⟨hb, ?_⟩⟩
      · rw [hcomm _ _ _ e, hbinv]
        exact P.mul_mem habP (hZP ((Zv ρ).inv_mem hz))
      · rw [hcomm _ _ _ e', hainv, hy.Vn_comm hb ha]
        exact P.mul_mem habP (hZP ((Zv ρ).inv_mem hz'))
  have hVN : Vn d.δ₀ ≤ N := (d.Vn_le hy).trans (sup_le hZN ((Subgroup.closure_le _).mpr
    (Set.insert_subset_iff.mpr ⟨hab.1, Set.singleton_subset_iff.mpr hab.2⟩)))
  exact (hVN hv).2

end Data

theorem exists_data {ρ : Geo H M} (hy : Hyp S ρ) : Nonempty (Data ρ) := by
  obtain ⟨δ₀, hδ₀⟩ := hy.hs.exists_adj hy.hA
  obtain ⟨D⟩ := hy.hs.exists_dict hy.hA hδ₀
  have hδv := hy.vtype_nbr hδ₀
  have hρδ : ρ ∈ nbrs δ₀ := nbrs_symm hδ₀
  have hg₀ : (dictLift D S5g : G) ∈ stab ρ ⊓ stab δ₀ :=
    (D.mem_S_iff (dictLift D S5g)).mpr (by rw [ψ_dictLift]; exact S5g_mem_S5Syl)
  have hg₀C : (dictLift D S5g : G) ∉ Subgroup.centralizer (Yv δ₀ : Set G) := by
    intro hC
    have h1 : (dictLift D S5g : G) ∈ (stab ρ ⊓ stab δ₀) ⊓
        Subgroup.centralizer ((⁅⁅Zv ρ, stab ρ ⊓ stab δ₀⁆, stab ρ ⊓ stab δ₀⁆ : Subgroup G) :
          Set G) := by
      rw [← hy.hs.Yv_eq_comm_comm hy.hA hy.h26 hδv hρδ]
      exact ⟨hg₀, hC⟩
    have h2 := (D.mem_centralizer_Y_iff (dictLift D S5g)).mp h1
    rw [ψ_dictLift] at h2
    exact S5g_not_mem_S5That h2
  have hnot := hy.hs.not_comm_le_Zv hy.hA hy.h26 hy.hb hδv hρδ hg₀ hg₀C
  obtain ⟨u, hu, hgu⟩ : ∃ u ∈ Vn δ₀, ⁅u, (dictLift D S5g : G)⁆ ∉ Zv ρ := by
    by_contra hcon
    push Not at hcon
    apply hnot
    obtain ⟨C, hC, -, -⟩ := exists_centralizer_quotient (X := stab ρ ⊓ stab δ₀) (N := Vn δ₀)
      (Z := Zv ρ) (fun x hx => (Sit43.edge_le_normalizer hy.hA hx).2)
      (fun x hx => (Sit43.edge_le_normalizer hy.hA hx).1)
    have hgC : (dictLift D S5g : G) ∈ C := (hC _).mpr ⟨hg₀, hcon⟩
    rw [Subgroup.commutator_le]
    intro v hv x hx
    exact ((hC x).mp ((Subgroup.zpowers_le.mpr hgC) hx)).2 v hv
  exact ⟨⟨δ₀, hδ₀, D, u, hu, hgu⟩⟩

end Model

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
