module

public import CFSG.RankThree.GF2n.Tim77Prop24Inv
public import CFSG.RankThree.GF2n.ConjModule

public section

open scoped IsMulCommutative

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_map_iff {M : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (M : Set G))
    {U : Subgroup ↥M} :
    x ∈ Subgroup.normalizer ((U.map M.subtype : Subgroup G) : Set G) ↔
      ∀ m ∈ U, conjHom M x hx m ∈ U := by
  constructor
  · intro h m hm
    have h1 : x * (m : G) * x⁻¹ ∈ U.map M.subtype :=
      (Subgroup.mem_normalizer_iff.mp h m).mp ⟨m, hm, rfl⟩
    obtain ⟨m', hm', he⟩ := h1
    have : conjHom M x hx m = m' := Subtype.ext (by rw [coe_conjHom_apply]; exact he.symm)
    rw [this]
    exact hm'
  · intro h
    rw [← conjSubgroup_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (card_conjSubgroup x _).ge
    intro y hy
    rw [mem_conjSubgroup] at hy
    obtain ⟨m, hm, hme⟩ := hy
    refine ⟨conjHom M x hx m, h m hm, ?_⟩
    have hme' : (m : G) = x⁻¹ * y * x := hme
    rw [Subgroup.coe_subtype, coe_conjHom_apply, hme']
    group

namespace Prop24Setup

variable {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
include S

theorem isCommutative_M : IsMulCommutative ↥M := S.isElemAbelian_M.1

theorem mem_M_sq {m : G} (hm : m ∈ M) : m * m = 1 := by
  rw [← sq]
  exact S.isElemAbelian_M.2 m hm

theorem eq_one_of_commute {a b m : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab) (hbL : b ∉ Lb)
    (hm : m ∈ M) (hma : a * m = m * a) (hmb : b * m = m * b) : m = 1 := by
  have h1 := S.mem_L_of_commute_M ha haL hm hma
  have h2 := S.symm.mem_L_of_commute_M hb hbL hm hmb
  have h3 : m ∈ A ⊓ Ab := Subgroup.mem_inf.mpr ⟨S.L_le h1, S.Lb_le h2⟩
  rwa [S.inf_eq_bot, Subgroup.mem_bot] at h3

theorem relIndex_Lb : Lb.relIndex Ab = L.relIndex A := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A)
  have h2 := Subgroup.relIndex_mul_card (H := Lb) (K := Ab)
  rw [inf_of_le_left S.L_le] at h1
  rw [inf_of_le_left S.Lb_le, S.card_Lb_eq] at h2
  have hcard : Nat.card Ab = Nat.card A := by
    obtain ⟨g, hg⟩ := S.conj
    rw [hg, card_conjSubgroup]
  rw [hcard, ← h1] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2

theorem conjHom_of_mem_M {y : G} (hyM : y ∈ M) (hyN : y ∈ Subgroup.normalizer (M : Set G))
    (m : ↥M) : conjHom M y hyN m = m :=
  Subtype.ext (by rw [coe_conjHom_apply, S.comm_M hyM m.2, mul_inv_cancel_right])

theorem le_normalizer_map_of_index_two (hAL : L.relIndex A = 2) {a : G} (ha : a ∈ A)
    (haL : a ∉ L) {U : Subgroup ↥M}
    (hU : ∀ m ∈ U, conjHom M a (S.A_le_normalizer_M ha) m ∈ U) :
    A ≤ Subgroup.normalizer ((U.map M.subtype : Subgroup G) : Set G) := by
  intro y hy
  rw [mem_normalizer_map_iff (S.A_le_normalizer_M hy)]
  intro m hm
  by_cases hyL : y ∈ L
  · rw [S.conjHom_of_mem_M (S.L_le_M hyL)]
    exact hm
  have hl : a⁻¹ * y ∈ L := by
    have h := (Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf A) hAL
      (a := (⟨a, ha⟩ : ↥A)⁻¹) (b := ⟨y, hy⟩)).mpr ⟨fun h => absurd (by
        have := (L.subgroupOf A).inv_mem h
        rwa [inv_inv, Subgroup.mem_subgroupOf] at this) haL, fun h => absurd
        (Subgroup.mem_subgroupOf.mp h) hyL⟩
    rwa [Subgroup.mem_subgroupOf] at h
  have e : conjHom M y (S.A_le_normalizer_M hy) m =
      conjHom M a (S.A_le_normalizer_M ha) m := by
    have hlm := S.comm_M (S.L_le_M hl) m.2
    refine Subtype.ext ?_
    rw [coe_conjHom_apply, coe_conjHom_apply]
    calc y * (m : G) * y⁻¹ = a * ((a⁻¹ * y) * m) * (a⁻¹ * y)⁻¹ * a⁻¹ := by group
      _ = a * (m * (a⁻¹ * y)) * (a⁻¹ * y)⁻¹ * a⁻¹ := by rw [hlm]
      _ = a * m * a⁻¹ := by group
  rw [e]
  exact hU m hm

theorem tim77_2_4_two_dihedral (hAL : L.relIndex A = 2) :
    ∃ s : Finset (Subgroup G), s.SupIndep id ∧ s.sup id = M ∧
      ∀ W ∈ s, W ≤ M ∧ A ⊔ Ab ≤ Subgroup.normalizer (W : Set G) ∧ W ≠ ⊥ ∧
        ∀ U : Subgroup G, U ≤ W → A ⊔ Ab ≤ Subgroup.normalizer (U : Set G) → U = ⊥ ∨ U = W := by
  classical
  have := S.isCommutative_M
  obtain ⟨a, ha, haL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨b, hb, hbL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have haN := S.A_le_normalizer_M ha
  have hbN := S.Ab_le_normalizer_M hb
  obtain ⟨s₀, hs₀, hs₀top, hs₀W⟩ := exists_supIndep_irred_of_dihedral (fun m hm => S.mem_M_sq hm)
    haN hbN (S.sq_A ha) (S.sq_Ab hb) (S.odd_orderOf_mul ha haL hb hbL)
    fun m hm hma hmb => S.eq_one_of_commute ha haL hb hbL hm hma hmb
  have hX : ∀ U : Subgroup ↥M, (∀ m ∈ U, conjHom M a haN m ∈ U) →
      (∀ m ∈ U, conjHom M b hbN m ∈ U) →
      A ⊔ Ab ≤ Subgroup.normalizer ((U.map M.subtype : Subgroup G) : Set G) := fun U hUa hUb =>
    sup_le (S.le_normalizer_map_of_index_two hAL ha haL hUa)
      (S.symm.le_normalizer_map_of_index_two (S.relIndex_Lb.trans hAL) hb hbL hUb)
  have hX' : ∀ U : Subgroup ↥M, A ⊔ Ab ≤ Subgroup.normalizer ((U.map M.subtype : Subgroup G) :
      Set G) → (∀ m ∈ U, conjHom M a haN m ∈ U) ∧ (∀ m ∈ U, conjHom M b hbN m ∈ U) :=
    fun U hU => ⟨(mem_normalizer_map_iff haN).mp (hU (Subgroup.mem_sup_left ha)),
      (mem_normalizer_map_iff hbN).mp (hU (Subgroup.mem_sup_right hb))⟩
  refine ⟨s₀.image (Subgroup.map M.subtype), supIndep_image_map hs₀, ?_, ?_⟩
  · rw [sup_image_map, hs₀top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · intro W hW
    obtain ⟨W₀, hW₀, rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨⟨hW₀a, hW₀b⟩, hW₀0, hW₀irr⟩ := hs₀W W₀ hW₀
    refine ⟨Subgroup.map_subtype_le W₀, hX W₀ hW₀a hW₀b, ?_, ?_⟩
    · intro h
      apply hW₀0
      rwa [← Subgroup.map_bot M.subtype, (Subgroup.map_injective M.subtype_injective).eq_iff] at h
    · intro U hUW hUX
      have hUM : U ≤ M := hUW.trans (Subgroup.map_subtype_le W₀)
      have hUe : (U.comap M.subtype).map M.subtype = U := by
        rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hUM]
      have hle : U.comap M.subtype ≤ W₀ := by
        intro m hm
        have : (m : G) ∈ W₀.map M.subtype := hUW hm
        obtain ⟨m', hm', he⟩ := this
        rwa [← Subtype.ext he]
      rcases hW₀irr (U.comap M.subtype) hle (hX' _ (hUe.symm ▸ hUX)) with h | h
      · left
        rw [← hUe, h, Subgroup.map_bot]
      · right
        rw [← hUe, h]

end Prop24Setup

end CFSG.RankThree.GF2n.Tim77
