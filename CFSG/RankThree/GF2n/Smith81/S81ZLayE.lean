module

public import CFSG.RankThree.GF2n.Smith81.S81ZUnip
public import CFSG.RankThree.GF2n.Smith81.S81ZMod

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X
open scoped commutatorElement


variable {K : Type} [Field K] {R : Finset Rt}

structure IsStab (R : Finset Rt) (E : Subgroup (Gp K)) : Prop where
  le : E ≤ URge K R 1
  tau : ∀ (t : Tt K), ∀ e ∈ E, tau t * e * (tau t)⁻¹ ∈ E
  norm : ∀ u ∈ URge K R 1, ∀ e ∈ E, u * e * (u⁻¹) ∈ E
  comm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e

structure Chars (K : Type) [Field K] (R : Finset Rt) : Prop where
  surj : ∀ α ∈ R, Function.Surjective (chi (K := K) α)
  ne : ∀ α ∈ R, ∀ β ∈ R, α ≠ β → ∀ σ : K ≃+* K,
    ∃ t : Tt K, σ ((chi α t : Kˣ) : K) ≠ ((chi β t : Kˣ) : K)

section Layers

variable [CharP K 2]

@[expose] def Eh (E : Subgroup (Gp K)) (R : Finset Rt) (h : ℕ) : Subgroup (Gp K) :=
  E ⊓ URge K R h

@[expose] def phiE (hR : Closed R) {h : ℕ} (hh : 1 ≤ h) (E : Subgroup (Gp K)) :
    ↥(Eh E R h) →* Multiplicative (↥(Lay R h) → K) :=
  (layHom hR hh).comp (Subgroup.inclusion (inf_le_right : Eh E R h ≤ URge K R h))

@[expose] def Sh (hR : Closed R) {h : ℕ} (hh : 1 ≤ h) (E : Subgroup (Gp K)) :
    AddSubgroup (↥(Lay R h) → K) :=
  Subgroup.toAddSubgroup' (phiE hR hh E).range

theorem mem_Sh {hR : Closed R} {h : ℕ} {hh : 1 ≤ h} {E : Subgroup (Gp K)} {c : ↥(Lay R h) → K} :
    c ∈ Sh hR hh E ↔ ∃ e : ↥(Eh E R h), layCoord hR hh ⟨e.1, e.2.2⟩ = c := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, he⟩
  · rintro ⟨e, he⟩
    exact ⟨e, he⟩

variable {hR : Closed R} {h : ℕ} {hh : 1 ≤ h} {E : Subgroup (Gp K)}

theorem Sh_tau (hE : IsStab R E) (t : Tt K) {c : ↥(Lay R h) → K} (hc : c ∈ Sh hR hh E) :
    (fun α : ↥(Lay R h) => ((chi α.1 t : Kˣ) : K) * c α) ∈ Sh hR hh E := by
  obtain ⟨e, rfl⟩ := mem_Sh.1 hc
  have he : tau t * e.1 * (tau t)⁻¹ ∈ Eh E R h :=
    ⟨hE.tau t e.1 e.2.1, conj_tau_mem_URge hR t e.2.2⟩
  refine mem_Sh.2 ⟨⟨_, he⟩, ?_⟩
  exact (congrArg Multiplicative.toAdd (layHom_conj_tau hR hh t ⟨e.1, e.2.2⟩))

open _root_.Classical in
@[expose] def Ah (hR : Closed R) {h : ℕ} (hh : 1 ≤ h) (E : Subgroup (Gp K)) :
    Finset ↥(Lay R h) := Finset.univ.filter fun i => ∃ c ∈ Sh hR hh E, c i ≠ 0

theorem mem_Ah {hR : Closed R} {h : ℕ} {hh : 1 ≤ h} {E : Subgroup (Gp K)} {i : ↥(Lay R h)} :
    i ∈ Ah hR hh E ↔ ∃ c ∈ Sh hR hh E, c i ≠ 0 := by
  classical
  simp [Ah]

theorem Sh_eq (hE : IsStab R E) (hC : Chars K R) :
    Sh hR hh E = coordSub K (Ah hR hh E) := by
  classical
  refine eq_coordSub (fun i : ↥(Lay R h) => chi (K := K) i.1) (fun i => ?_) (fun i j hij σ => ?_)
    (Sh hR hh E) (fun t c hc => Sh_tau hE t hc)
  · exact hC.surj i.1 (mem_Lay.1 i.2).1
  · exact hC.ne i.1 (mem_Lay.1 i.2).1 j.1 (mem_Lay.1 j.2).1 (fun e => hij (Subtype.ext e)) σ

theorem Eh_succ_le (hh : 1 ≤ h) : Eh E R (h + 1) ≤ Eh E R h :=
  inf_le_inf_left _ (URge_anti (Nat.le_succ h))

theorem mem_ker_phiE {x : ↥(Eh E R h)} :
    x ∈ (phiE hR hh E).ker ↔ x.1 ∈ URge K R (h + 1) := by
  rw [MonoidHom.mem_ker]
  exact layHom_eq_one_iff hR hh ⟨x.1, x.2.2⟩

theorem card_range_phiE (hR : Closed R) {h : ℕ} (hh : 1 ≤ h) (E : Subgroup (Gp K)) :
    Nat.card (phiE hR hh E).range = Nat.card ↥(Sh hR hh E) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, x.2⟩
      invFun := fun c => ⟨Multiplicative.ofAdd c.1, c.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun c => Subtype.ext rfl }

theorem ker_phiE_eq (hR : Closed R) {h : ℕ} (hh : 1 ≤ h) (E : Subgroup (Gp K)) :
    (phiE hR hh E).ker = (Eh E R (h + 1)).subgroupOf (Eh E R h) := by
  ext x
  rw [mem_ker_phiE (hR := hR) (hh := hh), Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    exact ⟨x.2.1, hx⟩
  · intro hx
    exact hx.2

theorem card_ker_phiE (hR : Closed R) {h : ℕ} (hh : 1 ≤ h) (E : Subgroup (Gp K)) :
    Nat.card (phiE hR hh E).ker = Nat.card ↥(Eh E R (h + 1)) := by
  rw [ker_phiE_eq hR hh E]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Eh_succ_le hh)).toEquiv

theorem card_Eh_step (hR : Closed R) {h : ℕ} (hh : 1 ≤ h) (E : Subgroup (Gp K)) :
    Nat.card ↥(Eh E R h) = Nat.card ↥(Eh E R (h + 1)) * Nat.card ↥(Sh hR hh E) := by
  have h1 : Nat.card ↥(Eh E R h) = Nat.card (↥(Eh E R h) ⧸ (phiE hR hh E).ker) *
      Nat.card (phiE hR hh E).ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (phiE hR hh E).ker
  have h2 : Nat.card (↥(Eh E R h) ⧸ (phiE hR hh E).ker) = Nat.card (phiE hR hh E).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (phiE hR hh E)).toEquiv
  rw [h1, h2, card_range_phiE, card_ker_phiE, mul_comm]

theorem URge_eq_bot {H : ℕ} (hH : ∀ α ∈ R, ht α ≤ H) : URge K R (H + 1) = ⊥ := by
  rw [eq_bot_iff]
  refine iSup₂_le fun α hα => ?_
  obtain ⟨hαR, hαh⟩ := Finset.mem_filter.1 hα
  have := hH α hαR
  push_cast at hαh
  omega

theorem Eh_one (hE : IsStab R E) : Eh E R 1 = E := inf_eq_left.2 hE.le

theorem card_E_prod (hR : Closed R) {H : ℕ} (hH : ∀ α ∈ R, ht α ≤ H) (hE : IsStab R E) :
    Nat.card ↥E = ∏ n ∈ Finset.range H, Nat.card ↥(Sh hR (Nat.succ_pos n) E) := by
  have key : ∀ m : ℕ, m ≤ H → Nat.card ↥E = Nat.card ↥(Eh E R (m + 1)) *
      ∏ n ∈ Finset.range m, Nat.card ↥(Sh hR (Nat.succ_pos n) E) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [Eh_one hE]
    | succ m ih =>
      intro hm
      rw [ih (by omega), Finset.prod_range_succ, card_Eh_step hR (Nat.succ_pos m) E]
      ring
  have := key H le_rfl
  have hbot : Eh E R (H + 1) = ⊥ := by
    unfold Eh
    rw [URge_eq_bot hH]
    simp
  rw [hbot] at this
  simpa using this

theorem card_E_pow [Finite K] (hR : Closed R) {H : ℕ} (hH : ∀ α ∈ R, ht α ≤ H) (hE : IsStab R E)
    (hC : Chars K R) :
    Nat.card ↥E = Nat.card K ^ ∑ n ∈ Finset.range H, (Ah hR (Nat.succ_pos n) E).card := by
  rw [card_E_prod hR hH hE, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [Sh_eq (hR := hR) (hh := Nat.succ_pos n) hE hC, card_coordSub]

theorem Pl_ext_single (R : Finset Rt) {h : ℕ} {α : Rt} (hα : α ∈ Lay R h) (c : K) :
    Pl R h (extLay R h (Pi.single (⟨α, hα⟩ : ↥(Lay R h)) c)) = xE α c := by
  rw [Pl_congr R (c' := Pi.single α c) (fun β hβ => ?_), Pl_single R hα]
  by_cases hβα : β = α
  · subst hβα
    simp [extLay, hβ]
  · have : (⟨β, hβ⟩ : ↥(Lay R h)) ≠ ⟨α, hα⟩ := fun e => hβα (congrArg Subtype.val e)
    simp [extLay, hβ, Pi.single_apply, hβα, this]

theorem exists_leading (hR : Closed R) (hE : IsStab R E) (hC : Chars K R) {h : ℕ} (hh : 1 ≤ h)
    {α : Rt} (hα : α ∈ Lay R h) (hA : (⟨α, hα⟩ : ↥(Lay R h)) ∈ Ah hR hh E) (c : K) :
    ∃ e ∈ E, e ∈ URge K R h ∧ (xE α c)⁻¹ * e ∈ URge K R (h + 1) := by
  have hmem : Pi.single (⟨α, hα⟩ : ↥(Lay R h)) c ∈ Sh hR hh E := by
    rw [Sh_eq hE hC]
    intro j hj
    have : j ≠ ⟨α, hα⟩ := fun e => hj (e ▸ hA)
    simp [Pi.single_apply, this]
  obtain ⟨e, he⟩ := mem_Sh.1 hmem
  refine ⟨e.1, e.2.1, e.2.2, ?_⟩
  have := layCoord_spec hR hh ⟨e.1, e.2.2⟩
  rw [he, Pl_ext_single R hα] at this
  exact this

@[expose] def InA (hR : Closed R) (E : Subgroup (Gp K)) (α : Rt) : Prop :=
  ∃ (h : ℕ) (hh : 1 ≤ h) (hα : α ∈ Lay R h), (⟨α, hα⟩ : ↥(Lay R h)) ∈ Ah hR hh E

theorem InA.mem {hR : Closed R} {α : Rt} (h : InA hR E α) : α ∈ R := by
  obtain ⟨_, _, hα, _⟩ := h
  exact (mem_Lay.1 hα).1

theorem InA.upper (hR : Closed R) (hE : IsStab R E) (hC : Chars K R) {α β : Rt}
    (hα : InA hR E α) (hβ : β ∈ R) (hroot : IsRoot .E7 (α + β)) : InA hR E (α + β) := by
  obtain ⟨h, hh, hαL, hA⟩ := hα
  obtain ⟨hαR, hαh⟩ := mem_Lay.1 hαL
  have hk : 1 ≤ (ht β).toNat := by have := hR.pos β hβ; omega
  set k := (ht β).toNat with hkdef
  have hβk : ht β = k := by have := hR.pos β hβ; omega
  have hαβR : α + β ∈ R := hR.add α hαR β hβ hroot
  have hαβL : α + β ∈ Lay R (h + k) := mem_Lay.2 ⟨hαβR, by rw [ht_add, hαh, hβk]; push_cast; rfl⟩
  refine ⟨h + k, by omega, hαβL, ?_⟩
  obtain ⟨e, heE, heU, hecong⟩ := exists_leading hR hE hC hh hαL hA 1
  set u := xE β (1 : K) with hu
  have huU : u ∈ URge K R k := xE_mem_URge hβ hβk.ge 1
  have hcommE : ⁅u, e⁆ ∈ E := by
    have h1 := hE.norm u (URge_anti hk huU) e heE
    have : ⁅u, e⁆ = (u * e * u⁻¹) * e⁻¹ := by simp [commutatorElement_def]
    rw [this]
    exact E.mul_mem h1 (E.inv_mem heE)
  have hcommU : ⁅u, e⁆ ∈ URge K R (h + k) := by
    have := comm_mem_URge hR hk hh huU heU
    rwa [add_comm] at this
  have hcc := comm_cong hR hk hh (x := u) (f := 1) (y := xE α 1) (f' := (xE α 1)⁻¹ * e) huU
    (xE_mem_URge hαR hαh.ge 1) (Subgroup.one_mem _) hecong
  rw [mul_one, mul_inv_cancel_left, add_comm k h] at hcc
  have hne : β + α ≠ 0 := add_ne_zero_of_pos hR hβ hαR
  have hcomm1 : ⁅u, xE α (1 : K)⁆ = xE (α + β) (1 : K) := by
    rw [hu, comm_xE (hR.root β hβ) (hR.root α hαR) hne 1 1, if_pos (by rwa [add_comm] : IsRoot .E7 (β + α))]
    simp [add_comm]
  rw [hcomm1] at hcc
  have hcc' : Cong R (h + k) (Pl R (h + k) (extLay R (h + k) (Pi.single (⟨α + β, hαβL⟩ : ↥(Lay R (h + k))) (1 : K))))
      (⟨⁅u, e⁆, hcommU⟩ : ↥(URge K R (h + k))).1 := by
    rw [Pl_ext_single R hαβL]
    exact hcc
  have hcoord := layCoord_eq_of_cong hR (by omega : 1 ≤ h + k) ⟨⁅u, e⁆, hcommU⟩ hcc'
  rw [mem_Ah]
  refine ⟨layCoord hR (by omega : 1 ≤ h + k) ⟨⁅u, e⁆, hcommU⟩,
    mem_Sh.2 ⟨⟨⁅u, e⁆, hcommE, hcommU⟩, rfl⟩, ?_⟩
  rw [hcoord]
  simp [extLay, hαβL]

theorem InA.abelian (hR : Closed R) (hE : IsStab R E) (hC : Chars K R) {α β : Rt}
    (hα : InA hR E α) (hβ : InA hR E β) : ¬ IsRoot .E7 (α + β) := by
  intro hroot
  obtain ⟨h, hh, hαL, hA⟩ := hα
  obtain ⟨k, hk, hβL, hB⟩ := hβ
  obtain ⟨hαR, hαh⟩ := mem_Lay.1 hαL
  obtain ⟨hβR, hβk⟩ := mem_Lay.1 hβL
  have hαβR : α + β ∈ R := hR.add α hαR β hβR hroot
  have hαβL : α + β ∈ Lay R (h + k) := mem_Lay.2 ⟨hαβR, by rw [ht_add, hαh, hβk]; push_cast; rfl⟩
  obtain ⟨e, heE, heU, hecong⟩ := exists_leading hR hE hC hh hαL hA 1
  obtain ⟨e', heE', heU', hecong'⟩ := exists_leading hR hE hC hk hβL hB 1
  have hcc := comm_cong hR hh hk (x := xE α 1) (f := (xE α 1)⁻¹ * e) (y := xE β 1)
    (f' := (xE β 1)⁻¹ * e') (xE_mem_URge hαR hαh.ge 1) (xE_mem_URge hβR hβk.ge 1) hecong hecong'
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at hcc
  have h1 : ⁅e, e'⁆ = 1 := by
    rw [commutatorElement_def, hE.comm e heE e' heE']
    group
  rw [h1] at hcc
  have hne : α + β ≠ 0 := add_ne_zero_of_pos hR hαR hβR
  rw [comm_xE (hR.root α hαR) (hR.root β hβR) hne 1 1, if_pos hroot] at hcc
  have hmem : xE (α + β) (1 * 1 : K) ∈ URge K R (h + k + 1) := by
    simpa [Cong] using hcc
  have h2 : Pl R (h + k) (extLay R (h + k) (Pi.single (⟨α + β, hαβL⟩ : ↥(Lay R (h + k))) (1 : K))) ∈
      URge K R (h + k + 1) := by
    rw [Pl_ext_single R hαβL]
    simpa using hmem
  have h3 := Pl_mem_succ_imp hR (by omega : 1 ≤ h + k) h2 (α + β) hαβL
  simp [extLay, hαβL] at h3

open _root_.Classical in
@[expose] def Aset (hR : Closed R) (E : Subgroup (Gp K)) : Finset Rt := R.filter fun α => InA hR E α

theorem mem_Aset {hR : Closed R} {E : Subgroup (Gp K)} {α : Rt} :
    α ∈ Aset hR E ↔ InA hR E α := by
  classical
  simp only [Aset, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.mem, h⟩⟩

theorem card_Aset (hR : Closed R) {H : ℕ} (hH : ∀ α ∈ R, ht α ≤ H) (E : Subgroup (Gp K)) :
    (Aset hR E).card = ∑ n ∈ Finset.range H, (Ah hR (Nat.succ_pos n) E).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun α : Rt => (ht α).toNat - 1) (t := Finset.range H)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hfib : (Aset hR E).filter (fun α => (ht α).toNat - 1 = n) =
        (Ah hR (Nat.succ_pos n) E).map ⟨Subtype.val, Subtype.val_injective⟩ := by
      ext α
      simp only [Finset.mem_filter, Finset.mem_map, mem_Aset, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨h, hh, hαL, hA⟩, hn'⟩
        have hαh := (mem_Lay.1 hαL).2
        have : h = n + 1 := by omega
        subst this
        exact ⟨⟨α, hαL⟩, hA, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        refine ⟨⟨n + 1, Nat.succ_pos n, a.2, ha⟩, ?_⟩
        have := (mem_Lay.1 a.2).2
        omega
    rw [hfib, Finset.card_map]
  · intro α hα
    have hαA := mem_Aset.1 hα
    obtain ⟨h, hh, hαL, -⟩ := hαA
    obtain ⟨hαR, hαh⟩ := mem_Lay.1 hαL
    have h1 := hH α hαR
    have h2 : (ht α).toNat = h := by omega
    rw [Finset.mem_coe, Finset.mem_range]
    show (ht α).toNat - 1 < H
    have h3 : (ht α).toNat ≤ H := by omega
    have h4 : 1 ≤ (ht α).toNat := by omega
    omega

theorem card_E_eq_pow_Aset [Finite K] (hR : Closed R) {H : ℕ} (hH : ∀ α ∈ R, ht α ≤ H)
    (hE : IsStab R E) (hC : Chars K R) : Nat.card ↥E = Nat.card K ^ (Aset hR E).card := by
  rw [card_Aset hR hH, card_E_pow hR hH hE hC]

end Layers

end CFSG.RankThree.GF2n.Smith81.S81Z
