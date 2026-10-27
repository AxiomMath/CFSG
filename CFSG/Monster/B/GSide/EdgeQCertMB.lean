module

public import CFSG.Monster.B.GSide.EdgeQCertL

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam
open CFSG.Monster.B.Co2 (v0)

theorem edgeXhat_mul_self :
    edgeXhat * edgeXhat = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  show (((edgeXhat : cEdgeStab) : Shat) : Dfull) * (((edgeXhat : cEdgeStab) : Shat) : Dfull) = 1
  rw [coe_edgeXhat, xhat_mul_self]

theorem edgeXhat_ne_one :
    edgeXhat ≠ 1 := fun h => by
  have h1 : xhat = 1 := coe_edgeXhat.symm.trans
    (congrArg (fun b : cEdgeStab => ((b : Shat) : Dfull)) h)
  have h2 := orderOf_xhat
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem val_mul
    (x y : cEdgeStab) : (((x * y : cEdgeStab) : Shat) : Dfull) =
    ((x : Shat) : Dfull) * ((y : Shat) : Dfull) := rfl

theorem cEdgeStab_val_injective :
    Function.Injective
    (fun b : cEdgeStab => ((b : Shat) : Dfull)) := fun _ _ h => Subtype.ext (Subtype.ext h)

section Generic

variable {G : Type*} [Group G]

@[expose] def pairStab (x z : G) (hz : ∀ g : G, g * z = z * g) (hz2 : z * z = 1) : Subgroup G where
  carrier := {b | b * x * b⁻¹ ∈ ({x, x * z} : Set G)}
  mul_mem' {a b} ha hb := by
    have e : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    have ez : ∀ y : G, a * (y * z) * a⁻¹ = a * y * a⁻¹ * z := fun y => by
      calc a * (y * z) * a⁻¹ = a * y * (z * a⁻¹) := by group
        _ = a * y * (a⁻¹ * z) := by rw [hz a⁻¹]
        _ = a * y * a⁻¹ * z := by group
    rcases hb with hb | hb
    · have e1 := e.trans (congrArg (fun w => a * w * a⁻¹) hb)
      rcases ha with ha | ha
      · exact Or.inl (e1.trans ha)
      · exact Or.inr (e1.trans ha)
    · have e2 := (e.trans (congrArg (fun w => a * w * a⁻¹) hb)).trans (ez x)
      rcases ha with ha | ha
      · exact Or.inr (e2.trans (congrArg (· * z) ha))
      · exact Or.inl ((e2.trans (congrArg (· * z) ha)).trans (by rw [mul_assoc, hz2, mul_one]))
  one_mem' := Or.inl (by group)
  inv_mem' {b} hb := by
    rcases hb with hb | hb
    · exact Or.inl ((congrArg (fun w => b⁻¹ * w * b⁻¹⁻¹) hb.symm).trans (by group))
    · refine Or.inr ?_
      have h1 : b⁻¹ * (x * z) * b⁻¹⁻¹ = b⁻¹ * x * b⁻¹⁻¹ * z := by
        calc b⁻¹ * (x * z) * b⁻¹⁻¹ = b⁻¹ * x * (z * b⁻¹⁻¹) := by group
          _ = b⁻¹ * x * (b⁻¹⁻¹ * z) := by rw [hz b⁻¹⁻¹]
          _ = b⁻¹ * x * b⁻¹⁻¹ * z := by group
      have h2 : b⁻¹ * (x * z) * b⁻¹⁻¹ = x :=
        (congrArg (fun w => b⁻¹ * w * b⁻¹⁻¹) hb.symm).trans (by group)
      calc b⁻¹ * x * b⁻¹⁻¹ = b⁻¹ * x * b⁻¹⁻¹ * z * z := by rw [mul_assoc _ z z, hz2, mul_one]
        _ = x * z := congrArg (· * z) (h1.symm.trans h2)

theorem mem_pairStab {x z : G} {hz : ∀ g : G, g * z = z * g} {hz2 : z * z = 1} {b : G} :
    b ∈ pairStab x z hz hz2 ↔ b * x * b⁻¹ = x ∨ b * x * b⁻¹ = x * z := Iff.rfl

theorem centralizer_le_pairStab (x z : G) (hz : ∀ g : G, g * z = z * g) (hz2 : z * z = 1) :
    Subgroup.centralizer {x} ≤ pairStab x z hz hz2 := fun b hb => by
  have h : b * x = x * b := Subgroup.mem_centralizer_singleton_iff.1 hb
  exact Or.inl (by rw [h, mul_inv_cancel_right])

theorem mem_centralizer_iff_conj (x b : G) :
    b ∈ Subgroup.centralizer {x} ↔ b * x * b⁻¹ = x := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [h, mul_inv_cancel_right]
  · intro h
    calc b * x = b * x * b⁻¹ * b := by group
      _ = x * b := by rw [h]

theorem relIndex_centralizer_pairStab (x z : G) (hz : ∀ g : G, g * z = z * g) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) {q : G} (hq : q * x * q⁻¹ = x * z) :
    (Subgroup.centralizer {x}).relIndex (pairStab x z hz hz2) = 2 := by
  have hqM : q ∈ pairStab x z hz hz2 := Or.inr hq
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨q, hqM⟩, fun b => ?_⟩
  have hne : x ≠ x * z := fun e => hz1 (by
    calc z = x⁻¹ * (x * z) := by group
      _ = 1 := by rw [← e, inv_mul_cancel])
  have hbq : (b : G) * q * x * ((b : G) * q)⁻¹ = (b : G) * x * (b : G)⁻¹ * z := by
    calc (b : G) * q * x * ((b : G) * q)⁻¹ = (b : G) * (q * x * q⁻¹) * (b : G)⁻¹ := by group
      _ = (b : G) * (x * z) * (b : G)⁻¹ := by rw [hq]
      _ = (b : G) * x * ((b : G)⁻¹ * z) := by rw [hz (b : G)⁻¹]; group
      _ = (b : G) * x * (b : G)⁻¹ * z := by group
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
    mem_centralizer_iff_conj, mem_centralizer_iff_conj, hbq]
  rcases b.2 with h | h
  · rw [h]
    exact Or.inr ⟨rfl, fun e => hne e.symm⟩
  · rw [h, mul_assoc, hz2, mul_one]
    exact Or.inl ⟨rfl, fun e => hne e.symm⟩

theorem index_centralizer_eq_ncard [Finite G] (x : G) :
    (Subgroup.centralizer {x}).index = (MulAction.orbit (ConjAct G) x).ncard := by
  have h1 := Subgroup.card_mul_index (Subgroup.centralizer {x})
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct G) x)
  have h3 := Subgroup.nat_card_centralizer_nat_card_stabilizer x
  have h4 : Nat.card (ConjAct G) = Nat.card G := Nat.card_congr ConjAct.toConjAct.toEquiv.symm
  rw [MulAction.index_stabilizer] at h2
  have hpos : 0 < Nat.card (Subgroup.centralizer {x}) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos (h1.trans ?_)
  rw [h3, h2, h4]

theorem orbit_conjAct_eq (x : G) (S : Set G) (h1 : ∀ b : G, b * x * b⁻¹ ∈ S)
    (h2 : ∀ y ∈ S, ∃ b : G, y = b * x * b⁻¹) : MulAction.orbit (ConjAct G) x = S := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    change c • x ∈ S
    rw [ConjAct.smul_def]
    exact h1 _
  · intro hy
    obtain ⟨b, rfl⟩ := h2 y hy
    refine ⟨ConjAct.toConjAct b, ?_⟩
    change ConjAct.toConjAct b • x = b * x * b⁻¹
    rw [ConjAct.toConjAct_smul]

end Generic

@[expose] def edgeMB
    (u : cEdgeFix) : Subgroup cEdgeStab :=
  pairStab (cEdgeIncl u) edgeXhat edgeXhat_comm edgeXhat_mul_self

theorem mem_edgeMB_iff
    {u : cEdgeFix} {b : cEdgeStab} :
    b ∈ edgeMB u ↔
      b * cEdgeIncl u * b⁻¹ ∈ ({cEdgeIncl u, cEdgeIncl u * edgeXhat} : Set cEdgeStab) := Iff.rfl

theorem xhat_pow_val_cases (t : ZMod 2) : xhat ^ t.val = 1 ∨ xhat ^ t.val = xhat := by
  rcases Fischer.zmod2_cases t with rfl | rfl
  · left; rw [ZMod.val_zero, pow_zero]
  · right; rw [ZMod.val_one, pow_one]

theorem xhat_pow_val_eq_one {t : ZMod 2} (h : xhat ^ t.val = 1) : t = 0 := by
  rcases Fischer.zmod2_cases t with rfl | rfl
  · rfl
  · rw [ZMod.val_one, pow_one] at h
    have h2 := orderOf_xhat
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)

theorem conj_edgeQ
    (y q : cEdgeStab) (hy : y ∈ edgeQ) (hq : q ∈ edgeQ) :
    q * y * q⁻¹ = y ∨ q * y * q⁻¹ = y * edgeXhat := by
  set ey : Ehat := ⟨((y : Shat) : Dfull), mem_edgeQ.1 hy⟩ with hey
  set eq : Ehat := ⟨((q : Shat) : Dfull)⁻¹, Ehat.inv_mem (mem_edgeQ.1 hq)⟩ with heq
  have hc := conj_Ehat ey eq
  have hval : (((q * y * q⁻¹ : cEdgeStab) : Shat) : Dfull) = (eq : Dfull)⁻¹ * ey * eq := by
    show ((q : Shat) : Dfull) * ((y : Shat) : Dfull) * ((q : Shat) : Dfull)⁻¹ =
      ((((q : Shat) : Dfull))⁻¹)⁻¹ * ((y : Shat) : Dfull) * ((q : Shat) : Dfull)⁻¹
    rw [inv_inv]
  rcases xhat_pow_val_cases (bV (psiW ey) (psiW eq)) with h1 | h1
  · left
    exact Subtype.ext (Subtype.ext (hval.trans (hc.trans ((congrArg ((ey : Dfull) * ·) h1).trans
      (mul_one _)))))
  · right
    refine Subtype.ext (Subtype.ext (hval.trans (hc.trans ((congrArg ((ey : Dfull) * ·) h1).trans
      ?_))))
    show ((y : Shat) : Dfull) * xhat =
      ((y : Shat) : Dfull) * (((edgeXhat : cEdgeStab) : Shat) : Dfull)
    exact congrArg (((y : Shat) : Dfull) * ·) coe_edgeXhat.symm

theorem edgeQ_le_edgeMB
    {u : cEdgeFix} (hu : u ∈ edgeL) : edgeQ ≤ edgeMB u := fun q hq => by
  rcases conj_edgeQ _ q hu.1 hq with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem cEdgeFix_normal_in :
    (cEdgeFix.subgroupOf cEdgeStab).Normal :=
  Subgroup.normal_of_index_eq_two cEdgeFix_index

theorem conj_mem_cEdgeFix
    (b : cEdgeStab) (a : cEdgeFix) :
    ((b * cEdgeIncl a * b⁻¹ : cEdgeStab) : Shat) ∈ cEdgeFix := by
  have h := cEdgeFix_normal_in.conj_mem (cEdgeIncl a) (show ((cEdgeIncl a : cEdgeStab) : Shat) ∈
    cEdgeFix from a.2) b
  exact h

theorem conj_lam_cases
    {b : cEdgeStab} {y : Shat}
    (h : (b : Shat) * y * (b : Shat)⁻¹ = (lamV0 : Shat) ∨
      (b : Shat) * y * (b : Shat)⁻¹ = (lamW0 : Shat)) :
    y = (lamV0 : Shat) ∨ y = (lamW0 : Shat) := by
  have hb := (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).1 b.2
  have e0 := GSide.clabelS_cvMul cv0 (b : Shat)
  have e1 := GSide.clabelS_cvMul cw0 (b : Shat)
  have hl0 : (lamV0 : Shat) = clabelS cv0 := rfl
  have hl1 : (lamW0 : Shat) = clabelS cw0 := rfl
  have key : ∀ z : Shat, (b : Shat) * y * (b : Shat)⁻¹ = z → y = (b : Shat)⁻¹ * z * b :=
    fun z hz => by rw [← hz]; group
  rcases hb with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0] at e0 <;> rw [h1] at e1
  · rcases h with h | h
    · left; rw [key _ h, hl0, ← e0]
    · right; rw [key _ h, hl1, ← e1]
  · rcases h with h | h
    · right; rw [key _ h, hl0, ← e0]; exact hl1.symm
    · left; rw [key _ h, hl1, ← e1]; exact hl0.symm

theorem mem_image_edgeL_of
    {y : cEdgeStab} (hyQ : y ∈ edgeQ) (hyA : (y : Shat) ∈ cEdgeFix)
    (hylab : ∃ v, (y : Shat) = clabelS v) (hy0 : (y : Shat) ≠ (lamV0 : Shat))
    (hy1 : (y : Shat) ≠ (lamW0 : Shat)) : y ∈ cEdgeIncl '' edgeL :=
  ⟨⟨(y : Shat), hyA⟩, ⟨hyQ, hylab, fun e => hy0 (congrArg Subtype.val e),
    fun e => hy1 (congrArg Subtype.val e)⟩, Subtype.ext rfl⟩

theorem conj_mem_image_edgeL
    {u : cEdgeFix} (hu : u ∈ edgeL) (b : cEdgeStab) :
    b * cEdgeIncl u * b⁻¹ ∈ cEdgeIncl '' edgeL := by
  obtain ⟨hQ, ⟨v, hv⟩, h0, h1⟩ := hu
  have hyv : ((b * cEdgeIncl u * b⁻¹ : cEdgeStab) : Shat) =
      (b : Shat) * (u : Shat) * (b : Shat)⁻¹ := rfl
  refine mem_image_edgeL_of (edgeQ_normal.conj_mem _ hQ b) (conj_mem_cEdgeFix b u)
    ⟨cvMul v (b : Shat)⁻¹, ?_⟩ (fun e => ?_) (fun e => ?_)
  · rw [hyv, GSide.clabelS_cvMul, inv_inv, ← hv]
  · rcases conj_lam_cases (Or.inl (hyv.symm.trans e)) with e2 | e2
    · exact h0 (Subtype.ext e2)
    · exact h1 (Subtype.ext e2)
  · rcases conj_lam_cases (Or.inr (hyv.symm.trans e)) with e2 | e2
    · exact h0 (Subtype.ext e2)
    · exact h1 (Subtype.ext e2)

theorem orbit_conjAct_edgeL
    {u : cEdgeFix} (hu : u ∈ edgeL) :
    MulAction.orbit (ConjAct cEdgeStab) (cEdgeIncl u) = cEdgeIncl '' edgeL := by
  refine orbit_conjAct_eq _ _ (conj_mem_image_edgeL hu) ?_
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨g, rfl⟩ := edgeL_conj hu ha
  exact ⟨cEdgeIncl g, Subtype.ext rfl⟩

theorem index_centralizer_edgeL
    {u : cEdgeFix} (hu : u ∈ edgeL) :
    (Subgroup.centralizer {cEdgeIncl u}).index = 1782 := by
  rw [index_centralizer_eq_ncard, orbit_conjAct_edgeL hu,
    Set.ncard_image_of_injective _ cEdgeIncl_injective, ncard_edgeL]

theorem exists_bV_eq_one
    {v : Wv v0} (hv : v ≠ 0) : ∃ y : Ehat, bV v (psiW y) = 1 := by
  have hz : ∃ z, bV v z ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv (bV_nondegenerate.1 _ hall)
  exact hz.elim fun z hz' => (psiW_surjective z).elim fun y hy =>
    ⟨y, hy ▸ zmod2_eq_one_of_ne_zero hz'⟩

theorem conj_edgeQOf_of_bV
    {u : cEdgeFix} (h : ((u : Shat) : Dfull) ∈ Ehat) (y : Ehat)
    (hb : bV (psiW (toEhat h)) (psiW y) = 1) :
    edgeQOf y.2 * cEdgeIncl u * (edgeQOf y.2)⁻¹ = cEdgeIncl u * edgeXhat := by
  apply cEdgeStab_val_injective
  have hc := conj_Ehat (toEhat h) y⁻¹
  have hb' : bV (psiW (toEhat h)) (psiW y⁻¹) = 1 := by
    rw [psiW_inv, ZModModule.neg_eq_self]
    exact hb
  have e : ((y⁻¹ : Ehat) : Dfull) = (y : Dfull)⁻¹ := rfl
  rw [hb', ZMod.val_one, pow_one, e, inv_inv] at hc
  show (y : Dfull) * ((u : Shat) : Dfull) * (y : Dfull)⁻¹ = ((u : Shat) : Dfull) *
    (((edgeXhat : cEdgeStab) : Shat) : Dfull)
  rw [coe_edgeXhat]
  exact hc

theorem exists_edgeQ_conj_mul
    {u : cEdgeFix} (hu : u ∈ edgeL) :
    ∃ q ∈ edgeQ, q * cEdgeIncl u * q⁻¹ = cEdgeIncl u * edgeXhat :=
  ((mem_edgeL_iff u).1 hu).elim fun h hΔ =>
    (exists_bV_eq_one (psiW_ne_zero_of_DeltaW hΔ)).elim fun y hy =>
      ⟨edgeQOf y.2, edgeQOf_mem y.2, conj_edgeQOf_of_bV h y hy⟩

theorem index_edgeMB
    {u : cEdgeFix} (hu : u ∈ edgeL) : (edgeMB u).index = 891 := by
  obtain ⟨q, -, hq⟩ := exists_edgeQ_conj_mul hu
  have h := Subgroup.relIndex_mul_index
    (centralizer_le_pairStab (cEdgeIncl u) edgeXhat edgeXhat_comm edgeXhat_mul_self)
  rw [relIndex_centralizer_pairStab _ _ _ _ edgeXhat_ne_one hq, index_centralizer_edgeL hu] at h
  change 2 * (edgeMB u).index = 1782 at h
  omega

theorem edgeQOf_not_mem_cEdgeFix
    {y : Ehat} (hy : bV Unitary.sigmaW (psiW y) = 1) :
    ((edgeQOf y.2 : cEdgeStab) : Shat) ∉ cEdgeFix := fun hA => by
  have hN : (y : Dfull) ∈ N1 := ⟨y.2, (mem_cEdgeFix_iff.1 hA).2⟩
  rw [(mem_N1_iff_bV y).1 hN] at hy
  exact zero_ne_one hy

theorem edgeQOf_comm_of_bV
    {u : cEdgeFix} (h : ((u : Shat) : Dfull) ∈ Ehat) (y : Ehat)
    (hb : bV (psiW (toEhat h)) (psiW y) = 0) :
    edgeQOf y.2 * cEdgeIncl u = cEdgeIncl u * edgeQOf y.2 := by
  apply cEdgeStab_val_injective
  have hc := conj_Ehat (toEhat h) y
  rw [hb, ZMod.val_zero, pow_zero, mul_one] at hc
  show (y : Dfull) * ((u : Shat) : Dfull) = ((u : Shat) : Dfull) * y
  calc (y : Dfull) * ((u : Shat) : Dfull) = y * ((y : Dfull)⁻¹ * (toEhat h : Dfull) * y) := by
        rw [hc]; rfl
    _ = ((u : Shat) : Dfull) * y := by
        show (y : Dfull) * ((y : Dfull)⁻¹ * ((u : Shat) : Dfull) * y) = _
        group

theorem edge_hBu
    {u : cEdgeFix} (hu : u ∈ edgeL) :
    ∃ b : cEdgeStab, (b : Shat) ∉ cEdgeFix ∧ b * cEdgeIncl u = cEdgeIncl u * b :=
  ((mem_edgeL_iff u).1 hu).elim fun h hΔ =>
    (exists_bV_one_zero Unitary.sigmaW_ne_zero
      (fun e => psiW_ne_sigma_of_DeltaW hΔ e.symm)).elim fun z hz =>
      (psiW_surjective z).elim fun y hy =>
        ⟨edgeQOf y.2, edgeQOf_not_mem_cEdgeFix (hy ▸ hz.1),
          edgeQOf_comm_of_bV h y (by rw [hy]; exact hz.2)⟩

end CFSG.Monster.B.GSide
