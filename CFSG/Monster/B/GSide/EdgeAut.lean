module

public import CFSG.Monster.B.GSide.EdgeAutU62
public import CFSG.Monster.B.GSide.EdgeAutV
public import CFSG.Monster.B.GSide.HSylowCenter

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem map_commutator_of_mulEquiv (e : G ≃* H) :
    (commutator G).map e.toMonoidHom = commutator H := by
  rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ e.surjective,
    ← _root_.commutator_def]

theorem mem_commutator_iff_of_mulEquiv (e : G ≃* H) (x : G) :
    e x ∈ commutator H ↔ x ∈ commutator G := by
  rw [← map_commutator_of_mulEquiv e, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem index_commutator_of_mulEquiv (e : G ≃* H) :
    (commutator G).index = (commutator H).index := by
  rw [← map_commutator_of_mulEquiv e,
    Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]

theorem symm_mem_center_of_mulEquiv (e : G ≃* H) {w : H} (hw : w ∈ Subgroup.center H) :
    e.symm w ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hw ⊢
  intro y
  apply e.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hw]

open scoped _root_.Classical in
theorem mulAut_transport_beta (e : G ≃* H) (τ : G ≃* G) {g w : H}
    (h : ∀ y, e (τ (e.symm y)) = g * (y * (if y ∈ commutator H then 1 else w)) * g⁻¹) (x : G) :
    τ x = e.symm g * (x * (if x ∈ commutator G then 1 else e.symm w)) * (e.symm g)⁻¹ := by
  apply e.injective
  have h1 := h (e x)
  rw [MulEquiv.symm_apply_apply] at h1
  rw [h1, map_mul, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  by_cases hx : x ∈ commutator G
  · rw [ite_eq_left hx, ite_eq_left ((mem_commutator_iff_of_mulEquiv e x).2 hx), map_one]
  · rw [ite_eq_right hx, ite_eq_right fun h' => hx ((mem_commutator_iff_of_mulEquiv e x).1 h'),
      MulEquiv.apply_symm_apply]

end Transport

theorem N1P_eq_pCore :
    N1P = CFSG.pCore 2 P1 := by
  show N1.subgroupOf P1 = _
  rw [← pCore_P1]
  exact Subgroup.comap_map_eq_self_of_injective P1.subtype_injective _

theorem mulAut_mem_N1P
    (τ : MulAut P1) {n : P1} (hn : n ∈ N1P) : τ n ∈ N1P := by
  rw [N1P_eq_pCore] at hn ⊢
  exact Subgroup.characteristic_iff_map_le.1 inferInstance τ ⟨n, hn, rfl⟩

theorem closure_xhat_cQ_le_centralizer :
    Subgroup.closure ({xhat, cQ} : Set Dfull) ≤ Subgroup.centralizer P1 := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;> intro g hg
  · exact xhat_comm_of_mem_Jhat (P1_le_Jhat hg)
  · exact Subgroup.mem_centralizer_singleton_iff.1 hg.2

theorem mem_center_N1P_comm
    {z : N1P} (hz : z ∈ Subgroup.center N1P) (a : P1) :
    a * z = z * a := by
  have h := (mem_center_N1P_iff z).1 hz
  rw [EU_sigLine] at h
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (closure_xhat_cQ_le_centralizer h)) a a.2)

theorem closure_xhat_cQ_eq_map :
    Subgroup.closure ({xhat, cQ} : Set Dfull) =
    (Subgroup.closure ({xP1, cP1} : Set P1)).map P1.subtype := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem mulAut_P1_fix_center
    (τ : MulAut P1) (hx : τ xP1 = xP1) (hc : τ cP1 = cP1) (z : N1P)
    (hz : z ∈ Subgroup.center N1P) : τ z = z := by
  have hle : Subgroup.closure ({xP1, cP1} : Set P1) ≤ τ.toMonoidHom.eqLocus (MonoidHom.id P1) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hx
    · exact hc
  have h := (mem_center_N1P_iff z).1 hz
  rw [EU_sigLine, closure_xhat_cQ_eq_map] at h
  obtain ⟨y, hy, hyz⟩ := h
  have e : y = (z : P1) := Subtype.ext hyz
  calc τ (z : P1) = τ y := congrArg τ e.symm
    _ = y := hle hy
    _ = z := e

theorem commutator_N1P :
    ⁅N1P, N1P⁆ = Subgroup.zpowers xP1 := by
  have h1 : (Subgroup.inclusion N1_le_P1).range = N1P := Subgroup.inclusion_range N1_le_P1
  have h2 : (Subgroup.zpowers xhat).subgroupOf N1 =
      Subgroup.zpowers (⟨xhat, xhat_mem_N1⟩ : N1) :=
    (congrArg (fun K => K.subgroupOf N1)
      (MonoidHom.map_zpowers N1.subtype ⟨xhat, xhat_mem_N1⟩)).symm.trans
      (Subgroup.comap_map_eq_self_of_injective N1.subtype_injective _)
  calc ⁅N1P, N1P⁆ = (commutator N1).map (Subgroup.inclusion N1_le_P1) := by
        rw [map_commutator_eq, h1]
    _ = (Subgroup.zpowers (⟨xhat, xhat_mem_N1⟩ : N1)).map (Subgroup.inclusion N1_le_P1) := by
        rw [commutator_N1, h2]
    _ = Subgroup.zpowers xP1 := MonoidHom.map_zpowers _ _

theorem mul_self_mem_center_N1P
    (n : N1P) : n * n ∈ Subgroup.center N1P := by
  rw [mem_center_N1P_iff]
  show ((n : P1) : Dfull) * ((n : P1) : Dfull) ∈ EU sigLine
  rcases Ehat_sq_mem (N1_le_Ehat (mem_N1_of_mem_N1P n)) with h | h <;> rw [h]
  · exact Subgroup.one_mem _
  · exact xhat_mem_EU

theorem commutator_N1P_top :
    ⁅N1P, ⊤⁆ = N1P := by
  have h1 : N1P.map P1.subtype = N1 :=
    (Subgroup.subgroupOf_map_subtype N1 P1).trans (inf_eq_left.2 N1_le_P1)
  have h2 : (⊤ : Subgroup P1).map P1.subtype = P1 :=
    (MonoidHom.range_eq_map _).symm.trans P1.range_subtype
  apply Subgroup.map_injective P1.subtype_injective
  calc (⁅N1P, ⊤⁆ : Subgroup P1).map P1.subtype =
        ⁅N1P.map P1.subtype, (⊤ : Subgroup P1).map P1.subtype⁆ := Subgroup.map_commutator _ _ _
    _ = ⁅N1, P1⁆ := congrArg₂ (fun A B => ⁅A, B⁆) h1 h2
    _ = N1 := Amalgam.commutator_N1_P1
    _ = N1P.map P1.subtype := h1.symm

theorem N1P_le_commutator :
    N1P ≤ commutator P1 :=
  commutator_N1P_top.symm.le.trans (Subgroup.commutator_mono le_top le_rfl)

theorem index_commutator_P1 :
    (commutator P1).index = 2 := by
  have hne := nonempty_p1Quot_PSU62
  obtain ⟨e⟩ := hne
  have hf : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' N1P)) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' N1P)).ker ≤ commutator P1 := fun x hx => by
    have h1 : e (x : P1 ⧸ N1P) = 1 := hx
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact N1P_le_commutator h1
  have hmap : (commutator P1).map (e.toMonoidHom.comp (QuotientGroup.mk' N1P)) =
      commutator Unitary.PSU62 := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ hf, ← _root_.commutator_def]
  rw [← Subgroup.index_map_eq _ hf hker, hmap, index_commutator_PSU62]

open scoped _root_.Classical in
theorem P1_mulAut_eq_inner_beta
    (τ : MulAut P1) (hx : τ xP1 = xP1) (hc : τ cP1 = cP1) :
    ∃ (g w : P1), w ∈ Subgroup.center P1 ∧ w ∈ N1P ∧
      ∀ x, τ x = g * (x * (if x ∈ commutator P1 then 1 else w)) * g⁻¹ := by
  have h := mulAut_eq_inner_mul_beta N1P (fun τ n hn => mulAut_mem_N1P τ hn)
    (fun z hz a => mem_center_N1P_comm hz a) (xh := xP1) (Subtype.ext xhat_mul_self)
    (fun h => xhat_ne_one (congrArg Subtype.val h)) commutator_N1P mul_self_mem_center_N1P
    commutator_N1P_top end_N1P p1Quot_mulAut_eq_conj index_commutator_P1 τ
    (mulAut_P1_fix_center τ hx hc)
  obtain ⟨g, _, ⟨z, hz, rfl⟩, hτ⟩ := h
  exact ⟨g, z, Subgroup.mem_center_iff.2 fun a => mem_center_N1P_comm hz a, z.2, hτ⟩

@[expose] def edgeFixEquivP1 :
    cEdgeFix ≃* P1 where
  toFun x := ⟨((x : Shat) : Dfull), mem_cEdgeFix_iff.1 x.2⟩
  invFun g := ⟨⟨(g : Dfull), Amalgam.Eam_le_Shat (Amalgam.Pc_le_Eam 0 g.2)⟩, mem_cEdgeFix_iff.2 g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem coe_edgeFixEquivP1
    (x : cEdgeFix) :
    ((edgeFixEquivP1 x : P1) : Dfull) = ((x : Shat) : Dfull) := rfl

theorem coe_edgeFixEquivP1_symm
    (g : P1) :
    (((edgeFixEquivP1.symm g : cEdgeFix) : Shat) : Dfull) = g := rfl

theorem edgeFixEquivP1_lamV0 :
    edgeFixEquivP1 lamV0 = cP1 := Subtype.ext coe_lamV0

theorem edgeFixEquivP1_lamV0_mul_lamW0 :
    edgeFixEquivP1 (lamV0 * lamW0) = xP1 := by
  apply Subtype.ext
  show ((lamV0 : Shat) : Dfull) * ((lamW0 : Shat) : Dfull) = xhat
  rw [coe_lamV0, coe_lamW0, ← mul_assoc, cQ_mul_self, one_mul]

theorem mem_commutator_cEdgeFix_iff
    (x : cEdgeFix) :
    x ∈ commutator cEdgeFix ↔ edgeFixEquivP1 x ∈ commutator P1 :=
  (mem_commutator_iff_of_mulEquiv edgeFixEquivP1 x).symm

theorem cEdgeFix_commutator_index :
    (commutator cEdgeFix).index = 2 :=
  (index_commutator_of_mulEquiv edgeFixEquivP1).trans index_commutator_P1

theorem center_cEdgeFix_le_commutator :
    Subgroup.center cEdgeFix ≤ commutator cEdgeFix := by
  rw [center_cEdgeFix, Subgroup.closure_le]
  rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, mem_commutator_cEdgeFix_iff] <;>
    refine N1P_le_commutator (Subgroup.mem_subgroupOf.2 ?_)
  · show ((lamV0 : Shat) : Dfull) ∈ N1
    rw [coe_lamV0]
    exact cQ_mem_N1
  · show ((lamW0 : Shat) : Dfull) ∈ N1
    rw [coe_lamW0]
    exact N1.mul_mem cQ_mem_N1 xhat_mem_N1

theorem mul_self_of_mem_center_cEdgeFix
    {w : cEdgeFix} (hw : w ∈ Subgroup.center cEdgeFix) :
    w * w = 1 := by
  rcases mem_center_cEdgeFix_iff.1 hw with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact lamV0_mul_self
  · exact lamW0_mul_self
  · calc lamV0 * lamW0 * (lamV0 * lamW0) = lamV0 * lamW0 * (lamW0 * lamV0) :=
          congrArg (lamV0 * lamW0 * ·) lamV0_mul_comm
      _ = lamV0 * (lamW0 * lamW0) * lamV0 := by simp only [mul_assoc]
      _ = 1 := by rw [lamW0_mul_self, mul_one, lamV0_mul_self]

open scoped _root_.Classical in
theorem cEdgeFix_mulAut_eq_inner_beta
    (τ : cEdgeFix ≃* cEdgeFix) (h0 : τ lamV0 = lamV0)
    (h1 : τ lamW0 = lamW0) :
    ∃ (b : cEdgeFix) (w : cEdgeFix), w ∈ Subgroup.center cEdgeFix ∧
      ∀ x : cEdgeFix, τ x = b * (x * (if x ∈ commutator cEdgeFix then 1 else w)) * b⁻¹ := by
  let τ' : MulAut P1 := (edgeFixEquivP1.symm.trans τ).trans edgeFixEquivP1
  have hv : edgeFixEquivP1.symm cP1 = lamV0 :=
    edgeFixEquivP1.symm_apply_eq.2 edgeFixEquivP1_lamV0.symm
  have hx' : edgeFixEquivP1.symm xP1 = lamV0 * lamW0 :=
    edgeFixEquivP1.symm_apply_eq.2 edgeFixEquivP1_lamV0_mul_lamW0.symm
  have hc : τ' cP1 = cP1 :=
    calc τ' cP1 = edgeFixEquivP1 (τ (edgeFixEquivP1.symm cP1)) := rfl
      _ = edgeFixEquivP1 (τ lamV0) := congrArg (fun y => edgeFixEquivP1 (τ y)) hv
      _ = edgeFixEquivP1 lamV0 := congrArg edgeFixEquivP1 h0
      _ = cP1 := edgeFixEquivP1_lamV0
  have hx : τ' xP1 = xP1 :=
    calc τ' xP1 = edgeFixEquivP1 (τ (edgeFixEquivP1.symm xP1)) := rfl
      _ = edgeFixEquivP1 (τ (lamV0 * lamW0)) := congrArg (fun y => edgeFixEquivP1 (τ y)) hx'
      _ = edgeFixEquivP1 (lamV0 * lamW0) := by rw [map_mul, h0, h1]
      _ = xP1 := edgeFixEquivP1_lamV0_mul_lamW0
  have h := P1_mulAut_eq_inner_beta τ' hx hc
  obtain ⟨g, w, hwZ, -, hτ⟩ := h
  exact ⟨edgeFixEquivP1.symm g, edgeFixEquivP1.symm w,
    symm_mem_center_of_mulEquiv edgeFixEquivP1 hwZ,
    mulAut_transport_beta edgeFixEquivP1 τ fun y => hτ y⟩

open scoped _root_.Classical in
theorem exists_cEdgeFix_beta
    (w : cEdgeFix) (hw : w ∈ Subgroup.center cEdgeFix) :
    ∃ β : cEdgeFix ≃* cEdgeFix,
      (∀ x, β x = x * (if x ∈ commutator cEdgeFix then 1 else w)) ∧ β lamV0 = lamV0 ∧
        β lamW0 = lamW0 := by
  have h := exists_beta_mulEquiv cEdgeFix_commutator_index (Subgroup.mem_center_iff.1 hw)
    (mul_self_of_mem_center_cEdgeFix hw) (center_cEdgeFix_le_commutator hw)
  obtain ⟨β, hβ⟩ := h
  refine ⟨β, hβ, ?_, ?_⟩
  · rw [hβ, ite_eq_left (center_cEdgeFix_le_commutator lamV0_mem_center), mul_one]
  · rw [hβ, ite_eq_left (center_cEdgeFix_le_commutator lamW0_mem_center), mul_one]

open scoped _root_.Classical in
theorem cEdgeFix_beta_not_inner :
    ¬ ∃ b : cEdgeFix, ∀ x : cEdgeFix,
    x * (if x ∈ commutator cEdgeFix then 1 else lamV0 * lamW0) = b * x * b⁻¹ := by
  rintro ⟨b, hb⟩
  have hbN : ∀ n ∈ N1, ((b : Shat) : Dfull) * n = n * ((b : Shat) : Dfull) := by
    intro n hn
    have hx : edgeFixEquivP1.symm ⟨n, N1_le_P1 hn⟩ ∈ commutator cEdgeFix := by
      rw [mem_commutator_cEdgeFix_iff, MulEquiv.apply_symm_apply]
      exact N1P_le_commutator (Subgroup.mem_subgroupOf.2 hn)
    have h := hb (edgeFixEquivP1.symm ⟨n, N1_le_P1 hn⟩)
    rw [ite_eq_left hx, mul_one, eq_mul_inv_iff_mul_eq] at h
    exact (congrArg (fun y : cEdgeFix => ((y : Shat) : Dfull)) h).symm
  have hbZ : ((b : Shat) : Dfull) ∈ Subgroup.closure {xhat, cQ} :=
    mem_closure_of_centralizer_N1 (mem_cEdgeFix_iff.1 b.2) hbN
  have hbc : ∀ x : cEdgeFix, b * x * b⁻¹ = x := fun x => by
    have h1 := (Subgroup.mem_centralizer_iff.1 (closure_xhat_cQ_le_centralizer hbZ))
      ((x : Shat) : Dfull) (mem_cEdgeFix_iff.1 x.2)
    have h2 : x * b = b * x := ext_cEdgeFix h1
    rw [← h2, mul_inv_cancel_right]
  have hex : ∃ x : cEdgeFix, x ∉ commutator cEdgeFix := by
    by_contra h
    push Not at h
    have htop : commutator cEdgeFix = ⊤ := eq_top_iff.2 fun x _ => h x
    have hidx := cEdgeFix_commutator_index
    rw [htop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨x, hx⟩ := hex
  have h := (hb x).trans (hbc x)
  rw [ite_eq_right hx] at h
  have h3 : lamV0 * lamW0 = 1 := mul_eq_left.1 h
  have h5 : xP1 = 1 := by
    rw [← edgeFixEquivP1_lamV0_mul_lamW0, h3, map_one]
  exact xhat_ne_one (congrArg Subtype.val h5)

end CFSG.Monster.B.GSide
