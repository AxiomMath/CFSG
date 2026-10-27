module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67PairC
public import CFSG.Quasithin.H13.VolIF956Core
public import CFSG.Quasithin.H13.L32A76S2e
public import CFSG.Quasithin.EmptyFaithful.S1422Extra
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg1667

variable {M V W₁ W₂ : Subgroup G} {g : G}

theorem f956Data (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) {z v i : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z)
    (hz2 : orderOf z = 2) (hv : v ∈ V) (hvU : v ∉ V ⊓ conjSubgroup M g)
    (hi : i ∈ conjSubgroup V g) (hiB : i ∉ conjSubgroup V g ⊓ M) :
    H13.VolI.F956Data (V ⊔ conjSubgroup V g) (V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M))
      (V ⊓ conjSubgroup M g) (conjSubgroup V g ⊓ M) z v i := by
  have hzZ : z ∈ V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) := by
    rw [hz]
    exact Subgroup.mem_zpowers z
  have hzU : z ∈ V ⊓ conjSubgroup M g := (Subgroup.mem_inf.mp hzZ).1
  have hzB : z ∈ conjSubgroup V g ⊓ M := (Subgroup.mem_inf.mp hzZ).2
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hzU).1
  have hzVg : z ∈ conjSubgroup V g := (Subgroup.mem_inf.mp hzB).1
  refine
    { mem_V₁ := by
        intro t
        rw [hz]
        exact Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2
      z_ne := by
        intro h1
        rw [h1, orderOf_one] at hz2
        omega
      z_comm := by
        have hVc : V ≤ Subgroup.centralizer ({z} : Set G) := by
          intro x hx
          rw [mem_centralizer_singleton_iff]
          exact (Subtype.ext_iff.mp ((h.elemAbelian.1).is_comm.comm
            ⟨z, hzV⟩ ⟨x, hx⟩)).symm
        have hVgc : conjSubgroup V g ≤ Subgroup.centralizer ({z} : Set G) := by
          intro x hx
          rw [mem_centralizer_singleton_iff]
          exact (Subtype.ext_iff.mp
            (((E3.isElemAbelian_conjSubgroup h.elemAbelian g).1).is_comm.comm
              ⟨z, hzVg⟩ ⟨x, hx⟩)).symm
        have hHc : V ⊔ conjSubgroup V g ≤ Subgroup.centralizer ({z} : Set G) :=
          sup_le hVc hVgc
        intro x hx
        exact (mem_centralizer_singleton_iff.mp (hHc hx)).symm
      X_le := inf_le_left.trans le_sup_left
      Y_le := inf_le_left.trans le_sup_right
      v_mem := Subgroup.mem_sup_left hv
      i_mem := Subgroup.mem_sup_right hi
      V₁_le_X := inf_le_left
      V₁_le_Y := inf_le_right
      inf_le := le_rfl
      card_X := card_U h hg
      card_Y := card_B h hg
      card_V₁ := by
        rw [hz, Nat.card_zpowers, hz2]
      sq_X := by
        intro a ha
        have h2 := h.elemAbelian.2 a (Subgroup.mem_inf.mp ha).1
        rwa [pow_two] at h2
      sq_Y := by
        intro b hb
        have h2 := (E3.isElemAbelian_conjSubgroup h.elemAbelian g).2 b (Subgroup.mem_inf.mp hb).1
        rwa [pow_two] at h2
      comm_X := by
        intro a ha a' ha'
        exact Subtype.ext_iff.mp ((h.elemAbelian.1).is_comm.comm
          ⟨a, (Subgroup.mem_inf.mp ha).1⟩ ⟨a', (Subgroup.mem_inf.mp ha').1⟩)
      comm_Y := by
        intro b hb b' hb'
        exact Subtype.ext_iff.mp
          (((E3.isElemAbelian_conjSubgroup h.elemAbelian g).1).is_comm.comm
            ⟨b, (Subgroup.mem_inf.mp hb).1⟩ ⟨b', (Subgroup.mem_inf.mp hb').1⟩)
      comm_XY := by
        intro a ha b hb
        have hmem := commutator_U_B_le h hg (Subgroup.commutator_mem_commutator ha hb)
        rwa [commutatorElement_def] at hmem
      v_X := by
        intro a ha
        exact Subtype.ext_iff.mp
          ((h.elemAbelian.1).is_comm.comm ⟨v, hv⟩ ⟨a, (Subgroup.mem_inf.mp ha).1⟩)
      i_Y := by
        intro b hb
        exact Subtype.ext_iff.mp
          (((E3.isElemAbelian_conjSubgroup h.elemAbelian g).1).is_comm.comm
            ⟨i, hi⟩ ⟨b, (Subgroup.mem_inf.mp hb).1⟩)
      v_Y := by
        intro b hb
        have hmem := commutator_V_B_le h hg (Subgroup.commutator_mem_commutator hv hb)
        rwa [commutatorElement_def] at hmem
      i_X := by
        intro a ha
        have hmem := commutator_Vg_U_le h hg (Subgroup.commutator_mem_commutator hi ha)
        rwa [commutatorElement_def] at hmem
      v_fix := fun b hb hc => mem_of_commutator_mem h hg hv hvU hb hc
      i_fix := fun a ha hc => mem_of_commutator_mem' h hg hi hiB ha hc
      nonab := exists_not_commute h hg }

private theorem exists_f956Data (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    ∃ z v i : G, H13.VolI.F956Data (V ⊔ conjSubgroup V g)
      (V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M)) (V ⊓ conjSubgroup M g)
      (conjSubgroup V g ⊓ M) z v i := by
  obtain ⟨z, hz2, hz⟩ := exists_eq_zpowers h hg
  have hVU : ¬ V ≤ V ⊓ conjSubgroup M g := by
    intro hle
    have hc := Subgroup.card_le_of_le hle
    rw [card_V h, card_U h hg] at hc
    omega
  obtain ⟨v, hv, hvU⟩ := SetLike.not_le_iff_exists.mp hVU
  have hVgB : ¬ conjSubgroup V g ≤ conjSubgroup V g ⊓ M := by
    intro hle
    have hc := Subgroup.card_le_of_le hle
    rw [E3.card_conjSubgroup, card_V h, card_B h hg] at hc
    omega
  obtain ⟨i, hi, hiB⟩ := SetLike.not_le_iff_exists.mp hVgB
  exact ⟨z, v, i, f956Data h hg hz hz2 hv hvU hi hiB⟩

theorem isExtraspecialPlus2_K (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    IsExtraspecialPlus2 ↥((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) : Subgroup G) 2 := by
  obtain ⟨z, v, i, D⟩ := exists_f956Data h hg
  refine ⟨isExtraspecial_of_isQ8Sq D.isQ8Sq, ?_, ?_⟩
  · rw [D.card_sup]
    norm_num
  · refine ⟨(V ⊓ conjSubgroup M g).subgroupOf
        (V ⊓ conjSubgroup M g ⊔ (conjSubgroup V g ⊓ M)), ?_⟩
    have hA : IsElemAbelian 2 ((V ⊓ conjSubgroup M g).subgroupOf
        (V ⊓ conjSubgroup M g ⊔ (conjSubgroup V g ⊓ M))) :=
      (h.elemAbelian.mono inf_le_left).subgroupOf _
    have h8 : Nat.card ((V ⊓ conjSubgroup M g).subgroupOf
        (V ⊓ conjSubgroup M g ⊔ (conjSubgroup V g ⊓ M))) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, card_U h hg]
    obtain ⟨e⟩ := H13.L32A.S2.E8.exists_coord hA h8
    exact ⟨e⟩

theorem cube_mem_centralizer (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) {v i : G}
    (hv : v ∈ V) (hvU : v ∉ V ⊓ conjSubgroup M g) (hi : i ∈ conjSubgroup V g)
    (hiB : i ∉ conjSubgroup V g ⊓ M) :
    (v * i) ^ 3 ∈
      centralizer (((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) : Subgroup G) : Set G) := by
  obtain ⟨z, hz2, hz⟩ := exists_eq_zpowers h hg
  have D := f956Data h hg hz hz2 hv hvU hi hiB
  rw [mem_centralizer_iff]
  intro u hu
  exact (D.cube_comm hu).symm

theorem K_le_X (h : Cfg1667 M V W₁ W₂) :
    (V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) ≤ V ⊔ conjSubgroup V g := by
  exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

theorem X_le_normalizer_K (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    V ⊔ conjSubgroup V g ≤
      normalizer (((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) : Subgroup G) : Set G) := by
  refine sup_le ?_ ?_
  · rw [Subgroup.le_normalizer_iff]
    intro y hy k hk
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right (V ⊓ conjSubgroup M g)
      (conjSubgroup V g ⊓ M) (le_normalizer_B h)] at hk
    obtain ⟨u, hu, b, hb, rfl⟩ := Set.mem_mul.mp hk
    have hyu : y * u * y⁻¹ = u := by
      have hc : y * u = u * y :=
        Subtype.ext_iff.mp ((h.elemAbelian.1).is_comm.comm ⟨y, hy⟩ ⟨u, (Subgroup.mem_inf.mp hu).1⟩)
      rw [hc]
      group
    have hyb : y * b * y⁻¹ ∈ V ⊓ conjSubgroup M g ⊔ (conjSubgroup V g ⊓ M) := by
      have hcb : ⁅y, b⁆ ∈ V ⊓ conjSubgroup M g :=
        commutator_V_B_le h hg (Subgroup.commutator_mem_commutator hy hb)
      have he : y * b * y⁻¹ = ⁅y, b⁆ * b := by rw [commutatorElement_def]; group
      rw [he]
      exact mul_mem_sup hcb hb
    rw [show y * (u * b) * y⁻¹ = (y * u * y⁻¹) * (y * b * y⁻¹) by group, hyu]
    exact (V ⊓ conjSubgroup M g ⊔ (conjSubgroup V g ⊓ M)).mul_mem
      (Subgroup.mem_sup_left hu) hyb
  · rw [Subgroup.le_normalizer_iff]
    intro y hy k hk
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right (V ⊓ conjSubgroup M g)
      (conjSubgroup V g ⊓ M) (le_normalizer_B h)] at hk
    obtain ⟨u, hu, b, hb, rfl⟩ := Set.mem_mul.mp hk
    have hyb : y * b * y⁻¹ = b := by
      have hc : y * b = b * y := Subtype.ext_iff.mp
        (((E3.isElemAbelian_conjSubgroup h.elemAbelian g).1).is_comm.comm
          ⟨y, hy⟩ ⟨b, (Subgroup.mem_inf.mp hb).1⟩)
      rw [hc]
      group
    have hyu : y * u * y⁻¹ ∈ V ⊓ conjSubgroup M g ⊔ (conjSubgroup V g ⊓ M) := by
      have hcu : ⁅y, u⁆ ∈ conjSubgroup V g ⊓ M :=
        commutator_Vg_U_le h hg (Subgroup.commutator_mem_commutator hy hu)
      have he : y * u * y⁻¹ = ⁅y, u⁆ * u := by rw [commutatorElement_def]; group
      rw [he]
      exact (V ⊓ conjSubgroup M g ⊔ (conjSubgroup V g ⊓ M)).mul_mem
        (Subgroup.mem_sup_right hcu) (Subgroup.mem_sup_left hu)
    rw [show y * (u * b) * y⁻¹ = (y * u * y⁻¹) * (y * b * y⁻¹) by group, hyb]
    exact (V ⊓ conjSubgroup M g ⊔ (conjSubgroup V g ⊓ M)).mul_mem hyu
      (Subgroup.mem_sup_right hb)

end Cfg1667

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
