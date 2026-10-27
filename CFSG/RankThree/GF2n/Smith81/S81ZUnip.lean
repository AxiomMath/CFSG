module

public import CFSG.RankThree.GF2n.Smith81.S81XE7Grp
public import CFSG.RankThree.GF2n.Smith81.S81XE7Def

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X
open scoped commutatorElement


variable {K : Type} [Field K]

instance instFiniteGp [Finite K] : Finite (Gp K) := by
  have h1 : Finite (V K) :=
    Finite.of_injective (fun v : V K => (v : Fin e7Data.d → K)) DFunLike.coe_injective
  have h2 : Finite (V K → V K) := inferInstance
  have hEnd : Finite (Module.End K (V K)) :=
    Finite.of_injective (fun f : Module.End K (V K) => (f : V K → V K)) DFunLike.coe_injective
  have hU : Finite (Module.End K (V K))ˣ :=
    Finite.of_injective
      (fun u : (Module.End K (V K))ˣ => ((u : Module.End K (V K)), ((u⁻¹ : (Module.End K (V K))ˣ) :
        Module.End K (V K))))
      (by
        intro a b h
        apply Units.ext
        exact congrArg Prod.fst h)
  exact Finite.of_injective (Subtype.val : Gp K → (Module.End K (V K))ˣ) Subtype.val_injective

abbrev Rt : Type := Fin (Tag.rank .E7) → ℤ

@[expose] def XR (K : Type) [Field K] (α : Rt) : Subgroup (Gp K) := e7Data_valid.rootGroup K α

theorem mem_XR {α : Rt} {g : Gp K} : g ∈ XR K α ↔ ∃ c : K, xE α c = g :=
  e7Data_valid.mem_rootGroup K

theorem xE_mem_XR (α : Rt) (c : K) : xE α c ∈ XR K α := e7Data_valid.xm_mem_rootGroup K α c

theorem xE_add (α : Rt) (c d : K) : xE α (c + d) = xE α c * xE α d := e7Data_valid.xm_add K α c d

theorem xE_zero (α : Rt) : xE α (0 : K) = 1 := e7Data_valid.xm_zero K α

theorem xE_inv (α : Rt) (c : K) : (xE α c)⁻¹ = xE α (-c) := e7Data_valid.xm_neg K α c

theorem xE_injective {α : Rt} (hα : IsRoot .E7 α) : Function.Injective (xE (K := K) α) :=
  e7Data_valid.xm_injective K hα

open _root_.Classical in
theorem comm_xE [CharP K 2] {α β : Rt} (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β) (hne : α + β ≠ 0)
    (c d : K) : ⁅xE α c, xE β d⁆ = if IsRoot .E7 (α + β) then xE (α + β) (c * d) else 1 := by
  obtain ⟨h1, h2⟩ := e7Data_valid.commutator_xm K hα hβ hne
  split_ifs with h
  · obtain ⟨σ, hσ, hσ'⟩ := h1 h
    rw [hσ' c d]
    have : σ = 1 := by
      rcases hσ with rfl | rfl
      · rfl
      · exact CharTwo.neg_eq 1
    rw [this, one_mul]
  · exact h2 h c d


structure Closed (R : Finset Rt) : Prop where
  root : ∀ α ∈ R, IsRoot .E7 α
  pos : ∀ α ∈ R, 0 < ht α
  add : ∀ α ∈ R, ∀ β ∈ R, IsRoot .E7 (α + β) → α + β ∈ R

theorem ht_add (α β : Rt) : ht (α + β) = ht α + ht β := by
  simp [ht, Finset.sum_add_distrib]

theorem add_ne_zero_of_pos {R : Finset Rt} (hR : Closed R) {α β : Rt} (hα : α ∈ R) (hβ : β ∈ R) :
    α + β ≠ 0 := by
  intro h0
  have h3 := ht_add α β
  have hz : ht (0 : Rt) = 0 := by simp [ht]
  rw [h0, hz] at h3
  have h1 := hR.pos α hα
  have h2 := hR.pos β hβ
  omega

@[expose] def URge (K : Type) [Field K] (R : Finset Rt) (h : ℕ) : Subgroup (Gp K) :=
  ⨆ α ∈ R.filter (fun α => (h : ℤ) ≤ ht α), XR K α

theorem XR_le_URge {R : Finset Rt} {h : ℕ} {α : Rt} (hα : α ∈ R) (hh : (h : ℤ) ≤ ht α) :
    XR K α ≤ URge K R h :=
  le_iSup₂_of_le (f := fun α (_ : α ∈ R.filter (fun α => (h : ℤ) ≤ ht α)) => XR K α) α
    (Finset.mem_filter.2 ⟨hα, hh⟩) le_rfl

theorem xE_mem_URge {R : Finset Rt} {h : ℕ} {α : Rt} (hα : α ∈ R) (hh : (h : ℤ) ≤ ht α) (c : K) :
    xE α c ∈ URge K R h :=
  XR_le_URge hα hh (xE_mem_XR α c)

theorem URge_anti {R : Finset Rt} {h k : ℕ} (hhk : h ≤ k) : URge K R k ≤ URge K R h := by
  refine iSup₂_le fun α hα => ?_
  obtain ⟨hαR, hαk⟩ := Finset.mem_filter.1 hα
  exact XR_le_URge hαR (le_trans (by exact_mod_cast hhk) hαk)

theorem URge_induction {R : Finset Rt} {h : ℕ} {C : Gp K → Prop} {g : Gp K}
    (hg : g ∈ URge K R h)
    (hgen : ∀ α ∈ R, (h : ℤ) ≤ ht α → ∀ c : K, C (xE α c)) (h1 : C 1)
    (hmul : ∀ x y, C x → C y → C (x * y)) : C g := by
  refine Subgroup.iSup_induction _ (C := C) hg ?_ h1 hmul
  intro α x hx
  by_cases hα : α ∈ R.filter (fun α => (h : ℤ) ≤ ht α)
  · rw [iSup_pos hα] at hx
    obtain ⟨c, rfl⟩ := mem_XR.1 hx
    obtain ⟨hαR, hαh⟩ := Finset.mem_filter.1 hα
    exact hgen α hαR hαh c
  · rw [iSup_neg hα, Subgroup.mem_bot] at hx
    subst hx
    exact h1

variable {R : Finset Rt}

theorem conj_xE_mem_URge (hR : Closed R) {α : Rt} (hα : α ∈ R) (c : K) {m : ℕ} {g : Gp K}
    (hg : g ∈ URge K R m) [CharP K 2] : xE α c * g * (xE α c)⁻¹ ∈ URge K R m := by
  refine URge_induction (C := fun g => xE α c * g * (xE α c)⁻¹ ∈ URge K R m) hg ?_ ?_ ?_
  · intro β hβ hβm d
    have hne : α + β ≠ 0 := by
      intro h0
      have h3 := ht_add α β
      have hz : ht (0 : Rt) = 0 := by simp [ht]
      rw [h0, hz] at h3
      have h1 := hR.pos α hα
      have h2 := hR.pos β hβ
      omega
    have hcomm := comm_xE (K := K) (hR.root α hα) (hR.root β hβ) hne c d
    have hconj : xE α c * xE β d * (xE α c)⁻¹ = ⁅xE α c, xE β d⁆ * xE β d := by
      rw [commutatorElement_def]; group
    rw [hconj, hcomm]
    refine Subgroup.mul_mem _ ?_ (xE_mem_URge hβ hβm d)
    split_ifs with hr
    · refine xE_mem_URge (hR.add α hα β hβ hr) ?_ _
      rw [ht_add]
      have := hR.pos α hα
      omega
    · exact Subgroup.one_mem _
  · simp
  · intro x y hx hy
    have : xE α c * (x * y) * (xE α c)⁻¹ = (xE α c * x * (xE α c)⁻¹) * (xE α c * y * (xE α c)⁻¹) := by
      group
    rw [this]
    exact Subgroup.mul_mem _ hx hy

theorem conj_mem_URge (hR : Closed R) [CharP K 2] {u : Gp K} (hu : u ∈ URge K R 1) {m : ℕ}
    {g : Gp K} (hg : g ∈ URge K R m) : u * g * u⁻¹ ∈ URge K R m := by
  have key : ∀ u : Gp K, u ∈ URge K R 1 →
      ∀ g : Gp K, g ∈ URge K R m → u * g * u⁻¹ ∈ URge K R m := by
    intro u hu
    refine URge_induction (C := fun u => ∀ g : Gp K, g ∈ URge K R m → u * g * u⁻¹ ∈ URge K R m)
      hu ?_ ?_ ?_
    · intro α hα _ c g hg
      exact conj_xE_mem_URge hR hα c hg
    · intro g hg
      simpa using hg
    · intro x y hx hy g hg
      have : x * y * g * (x * y)⁻¹ = x * (y * g * y⁻¹) * x⁻¹ := by group
      rw [this]
      exact hx _ (hy g hg)
  exact key u hu g hg

theorem comm_mul_right' (x y z : Gp K) : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
  simp only [commutatorElement_def]; group

theorem comm_mul_left' (x y z : Gp K) : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]; group

theorem comm_mem_URge (hR : Closed R) [CharP K 2] {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {x y : Gp K}
    (hx : x ∈ URge K R h) (hy : y ∈ URge K R k) : ⁅x, y⁆ ∈ URge K R (h + k) := by
  have key : ∀ x : Gp K, x ∈ URge K R h →
      ∀ y : Gp K, y ∈ URge K R k → ⁅x, y⁆ ∈ URge K R (h + k) := by
    intro x hx
    have := URge_induction (C := fun x => x ∈ URge K R h ∧
        ∀ y : Gp K, y ∈ URge K R k → ⁅x, y⁆ ∈ URge K R (h + k)) hx ?_ ?_ ?_
    · exact this.2
    · intro α hα hαh c
      refine ⟨xE_mem_URge hα hαh c, fun y hy => ?_⟩
      have := URge_induction (C := fun y => y ∈ URge K R k ∧ ⁅xE α c, y⁆ ∈ URge K R (h + k)) hy ?_
        ?_ ?_
      · exact this.2
      · intro β hβ hβk d
        refine ⟨xE_mem_URge hβ hβk d, ?_⟩
        have hne : α + β ≠ 0 := by
          intro h0
          have h3 := ht_add α β
          have hz : ht (0 : Rt) = 0 := by simp [ht]
          rw [h0, hz] at h3
          have h1 := hR.pos α hα
          have h2 := hR.pos β hβ
          omega
        rw [comm_xE (K := K) (hR.root α hα) (hR.root β hβ) hne c d]
        split_ifs with hr
        · refine xE_mem_URge (hR.add α hα β hβ hr) ?_ _
          rw [ht_add]
          push_cast
          omega
        · exact Subgroup.one_mem _
      · exact ⟨Subgroup.one_mem _, by simp⟩
      · intro y y' hy hy'
        refine ⟨Subgroup.mul_mem _ hy.1 hy'.1, ?_⟩
        rw [comm_mul_right']
        refine Subgroup.mul_mem _ hy.2 ?_
        exact conj_mem_URge hR (URge_anti hk hy.1) hy'.2
    · exact ⟨Subgroup.one_mem _, fun y _ => by simp⟩
    · intro x x' hx hx'
      refine ⟨Subgroup.mul_mem _ hx.1 hx'.1, fun y hy => ?_⟩
      rw [comm_mul_left']
      refine Subgroup.mul_mem _ ?_ (hx.2 y hy)
      exact conj_mem_URge hR (URge_anti hh hx.1) (hx'.2 y hy)
  exact key x hx y hy


@[expose] def htHom : (Fin (Tag.rank .E7) → ℤ) →+ ℤ where
  toFun := ht
  map_zero' := by simp [ht]
  map_add' := ht_add

@[expose] def levH : Fin e7Data.d → ℤ := e7Data.fgrade htHom

@[irreducible] def D7 : ℤ := dE7

theorem D7_pos : 0 < D7 := by
  unfold D7
  exact dE7_pos

theorem levH_shift {γ : Rt} (hγ : IsRoot .E7 γ) {b : Fin e7Data.d} (hb : pr b γ = -1) :
    levH (shift γ b) = levH b + D7 * ht γ := by
  unfold D7
  exact e7Data.isGrading_fgrade htHom b (shift γ b) γ (wt_shift hγ hb)

@[expose] def HasRaise (n : ℤ) (φ : Module.End K (V K)) : Prop :=
  ∀ b, φ (Finsupp.single b 1) ∈ Fil levH (levH b + n)

theorem HasRaise.map_Fil {n : ℤ} {φ : Module.End K (V K)} (hφ : HasRaise n φ) {k : ℤ} {v : V K}
    (hv : v ∈ Fil levH k) : φ v ∈ Fil levH (k + n) := by
  rw [mem_Fil]
  intro b' hb'
  have hsum : v = ∑ b ∈ v.support, v b • Finsupp.single b (1 : K) := by
    conv_lhs => rw [← Finsupp.sum_single v]
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finsupp.smul_single_one]
  rw [hsum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hvb : v b ≠ 0 := Finsupp.mem_support_iff.mp hb
  have hkb : k ≤ levH b := by
    by_contra hcon
    exact hvb ((mem_Fil.mp hv) b (not_le.mp hcon))
  have h2 := (mem_Fil.mp (hφ b)) b' (by omega)
  rw [h2, mul_zero]

theorem HasRaise.mono {n m : ℤ} (hnm : m ≤ n) {φ : Module.End K (V K)} (h : HasRaise n φ) :
    HasRaise m φ := fun b => Fil_mono (by omega) (h b)

theorem HasRaise.add {n : ℤ} {φ ψ : Module.End K (V K)} (hφ : HasRaise n φ) (hψ : HasRaise n ψ) :
    HasRaise n (φ + ψ) := fun b => by
  rw [LinearMap.add_apply]
  exact Submodule.add_mem _ (hφ b) (hψ b)

theorem HasRaise.zero (n : ℤ) : HasRaise n (0 : Module.End K (V K)) := fun b => by
  rw [LinearMap.zero_apply]
  exact Submodule.zero_mem _

theorem HasRaise.smul {n : ℤ} {φ : Module.End K (V K)} (hφ : HasRaise n φ) (c : K) :
    HasRaise n (c • φ) := fun b => by
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ c (hφ b)

theorem HasRaise.mul {n m : ℤ} {φ ψ : Module.End K (V K)} (hφ : HasRaise n φ) (hψ : HasRaise m ψ) :
    HasRaise (n + m) (φ * ψ) := fun b => by
  rw [Module.End.mul_apply]
  have := hφ.map_Fil (hψ b)
  convert this using 2
  ring


theorem endoE_mul (g h : Gp K) : endoE (g * h) = endoE g * endoE h := e7Data_valid.endo_mul K g h

theorem endoE_one : endoE (1 : Gp K) = 1 := e7Data_valid.endo_one K

theorem endoE_xE (α : Rt) (c : K) : endoE (xE α c) = 1 + c • e7Data.rootOp K α :=
  e7Data_valid.endo_xm K α c

theorem rootOp_hasRaise [CharP K 2] {γ : Rt} (hγ : IsRoot .E7 γ) :
    HasRaise (D7 * ht γ) (e7Data.rootOp K γ) := by
  intro b
  rw [rootOp_single hγ]
  by_cases hb : pr b γ = -1
  · rw [if_pos hb]
    have h1 := single_mem_Fil (K := K) levH (shift γ b)
    rwa [levH_shift hγ hb] at h1
  · rw [if_neg hb]
    exact Submodule.zero_mem _

set_option maxRecDepth 20000 in
theorem endoE_sub_one_hasRaise [CharP K 2] (hR : Closed R) {h : ℕ} {g : Gp K}
    (hg : g ∈ URge K R h) : HasRaise (D7 * h) (endoE g - 1) := by
  have hpos := D7_pos
  have hnn : (0 : ℤ) ≤ D7 * h := by positivity
  refine URge_induction (C := fun g => HasRaise (D7 * h) (endoE g - 1)) hg ?_ ?_ ?_
  · intro α hα hαh c
    rw [endoE_xE, add_sub_cancel_left]
    have h1 : HasRaise (D7 * ht α) (e7Data.rootOp K α) := rootOp_hasRaise (hR.root α hα)
    have h2 : HasRaise (D7 * (h : ℤ)) (e7Data.rootOp K α) :=
      h1.mono (mul_le_mul_of_nonneg_left hαh hpos.le)
    exact h2.smul c
  · rw [endoE_one, sub_self]
    exact HasRaise.zero _
  · intro x y hx hy
    rw [endoE_mul]
    have e : endoE x * endoE y - 1 = (endoE x - 1) * (endoE y - 1) + (endoE x - 1) + (endoE y - 1) := by
      noncomm_ring
    rw [e]
    refine ((hx.mul hy).mono ?_).add hx |>.add hy
    omega

@[expose] def Cong (R : Finset Rt) (h : ℕ) (x y : Gp K) : Prop := x⁻¹ * y ∈ URge K R (h + 1)

theorem Cong.refl (R : Finset Rt) (h : ℕ) (x : Gp K) : Cong R h x x := by
  simp [Cong, Subgroup.one_mem]

theorem Cong.symm {R : Finset Rt} {h : ℕ} {x y : Gp K} (hxy : Cong R h x y) : Cong R h y x := by
  have := Subgroup.inv_mem _ hxy
  simpa [Cong] using this

theorem Cong.trans {R : Finset Rt} {h : ℕ} {x y z : Gp K} (hxy : Cong R h x y)
    (hyz : Cong R h y z) : Cong R h x z := by
  have := Subgroup.mul_mem _ hxy hyz
  simpa [Cong, mul_assoc] using this

theorem Cong.mul_left {R : Finset Rt} {h : ℕ} {u u' : Gp K} (x : Gp K) (hu : Cong R h u u') :
    Cong R h (x * u) (x * u') := by
  simpa [Cong, mul_assoc] using hu

theorem Cong.mul_right (hR : Closed R) [CharP K 2] {h : ℕ} {u u' : Gp K} (hu : Cong R h u u')
    {b : Gp K} (hb : b ∈ URge K R 1) : Cong R h (u * b) (u' * b) := by
  have := conj_mem_URge hR (u := b⁻¹) (Subgroup.inv_mem _ hb) hu
  simpa [Cong, mul_assoc] using this

theorem Cong.comm (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) {a b : Gp K}
    (ha : a ∈ URge K R h) (hb : b ∈ URge K R h) : Cong R h (a * b) (b * a) := by
  have := comm_mem_URge hR hh hh (Subgroup.inv_mem _ hb) (Subgroup.inv_mem _ ha)
  have e : ⁅b⁻¹, a⁻¹⁆ = (a * b)⁻¹ * (b * a) := by
    simp only [commutatorElement_def]; group
  rw [e] at this
  exact URge_anti (by omega) this

@[expose] def PL (L : List Rt) (c : Rt → K) : Gp K := (L.map fun α => xE α (c α)).prod

@[expose] def Lay (R : Finset Rt) (h : ℕ) : Finset Rt := R.filter fun α => ht α = h

theorem mem_Lay {R : Finset Rt} {h : ℕ} {α : Rt} : α ∈ Lay R h ↔ α ∈ R ∧ ht α = h := by
  simp [Lay]

theorem PL_mem {R : Finset Rt} {h : ℕ} {L : List Rt} (hL : ∀ α ∈ L, α ∈ R ∧ (h : ℤ) ≤ ht α)
    (c : Rt → K) : PL L c ∈ URge K R h := by
  induction L with
  | nil => simp [PL, Subgroup.one_mem]
  | cons α L ih =>
    simp only [PL, List.map_cons, List.prod_cons]
    exact Subgroup.mul_mem _ (xE_mem_URge (hL α List.mem_cons_self).1
      (hL α List.mem_cons_self).2 _) (ih fun β hβ => hL β (List.mem_cons_of_mem _ hβ))

theorem PL_nil (c : Rt → K) : PL ([] : List Rt) c = 1 := rfl

theorem PL_cons (α : Rt) (L : List Rt) (c : Rt → K) :
    PL (α :: L) c = xE α (c α) * PL L c := by
  simp [PL]

theorem PL_zero (L : List Rt) : PL L (0 : Rt → K) = 1 := by
  induction L with
  | nil => rfl
  | cons α L ih => rw [PL_cons, ih]; simp [xE_zero]

theorem PL_add (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) {L : List Rt}
    (hL : ∀ α ∈ L, α ∈ R ∧ (h : ℤ) ≤ ht α) (c c' : Rt → K) :
    Cong R h (PL L c * PL L c') (PL L (c + c')) := by
  induction L with
  | nil => simpa [PL_nil] using Cong.refl R h (1 : Gp K)
  | cons α L ih =>
    have hL' : ∀ β ∈ L, β ∈ R ∧ (h : ℤ) ≤ ht β := fun β hβ => hL β (List.mem_cons_of_mem _ hβ)
    have ih' := ih hL'
    have hα := hL α List.mem_cons_self
    have hx : xE α (c α) ∈ URge K R h := xE_mem_URge hα.1 hα.2 _
    have hx' : xE α (c' α) ∈ URge K R h := xE_mem_URge hα.1 hα.2 _
    have hA : PL L c ∈ URge K R h := PL_mem hL' c
    have hA' : PL L c' ∈ URge K R h := PL_mem hL' c'
    have h1 : ∀ g, g ∈ URge K R h → g ∈ URge K R 1 := fun g hg => URge_anti hh hg
    rw [PL_cons, PL_cons, PL_cons]
    have e1 : xE α (c α) * PL L c * (xE α (c' α) * PL L c') =
        xE α (c α) * (PL L c * xE α (c' α)) * PL L c' := by group
    have e2 : xE α (c α) * (xE α (c' α) * PL L c) * PL L c' =
        xE α ((c + c') α) * (PL L c * PL L c') := by
      rw [Pi.add_apply, xE_add]; group
    have s1 : Cong R h (PL L c * xE α (c' α)) (xE α (c' α) * PL L c) :=
      Cong.comm hR hh hA hx'
    have s2 : Cong R h (xE α (c α) * (PL L c * xE α (c' α)) * PL L c')
        (xE α (c α) * (xE α (c' α) * PL L c) * PL L c') :=
      Cong.mul_right hR (Cong.mul_left _ s1) (h1 _ hA')
    have s3 : Cong R h (xE α ((c + c') α) * (PL L c * PL L c'))
        (xE α ((c + c') α) * PL L (c + c')) := Cong.mul_left _ ih'
    rw [e1]
    refine s2.trans ?_
    rw [e2]
    exact s3

theorem PL_eq_one_of_zero {L : List Rt} {c : Rt → K} (h : ∀ α ∈ L, c α = 0) : PL L c = 1 := by
  induction L with
  | nil => rfl
  | cons α L ih =>
    rw [PL_cons, h α List.mem_cons_self, xE_zero, ih fun β hβ => h β (List.mem_cons_of_mem _ hβ),
      one_mul]

theorem PL_single {L : List Rt} (hnd : L.Nodup) {α : Rt} (hα : α ∈ L) (d : K) :
    PL L (Pi.single α d) = xE α d := by
  induction L with
  | nil => exact absurd hα List.not_mem_nil
  | cons β L ih =>
    rw [List.nodup_cons] at hnd
    rw [PL_cons]
    by_cases hβα : β = α
    · subst hβα
      rw [PL_eq_one_of_zero (fun γ hγ => ?_), mul_one, Pi.single_eq_same]
      exact Pi.single_eq_of_ne (by rintro rfl; exact hnd.1 hγ) _
    · have hαL : α ∈ L := (List.mem_cons.1 hα).resolve_left (Ne.symm hβα)
      rw [Pi.single_eq_of_ne hβα, xE_zero, one_mul]
      exact ih hnd.2 hαL

@[expose] def Pl (R : Finset Rt) (h : ℕ) (c : Rt → K) : Gp K := PL (Lay R h).toList c

theorem Pl_mem (R : Finset Rt) {h : ℕ} (c : Rt → K) : Pl R h c ∈ URge K R h :=
  PL_mem (fun α hα => by
    obtain ⟨h1, h2⟩ := mem_Lay.1 (Finset.mem_toList.1 hα)
    exact ⟨h1, h2.ge⟩) c

theorem Pl_zero (R : Finset Rt) (h : ℕ) : Pl R h (0 : Rt → K) = 1 := PL_zero _

theorem Pl_single (R : Finset Rt) {h : ℕ} {α : Rt} (hα : α ∈ Lay R h) (d : K) :
    Pl R h (Pi.single α d) = xE α d :=
  PL_single (Finset.nodup_toList _) (Finset.mem_toList.2 hα) d

theorem Pl_add (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) (c c' : Rt → K) :
    Cong R h (Pl R h c * Pl R h c') (Pl R h (c + c')) :=
  PL_add hR hh (fun α hα => by
    obtain ⟨h1, h2⟩ := mem_Lay.1 (Finset.mem_toList.1 hα)
    exact ⟨h1, h2.ge⟩) c c'

theorem coord_exists (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) {g : Gp K}
    (hg : g ∈ URge K R h) : ∃ c : Rt → K, Cong R h (Pl R h c) g := by
  have := URge_induction (C := fun g => g ∈ URge K R h ∧ ∃ c : Rt → K, Cong R h (Pl R h c) g) hg
    ?_ ?_ ?_
  · exact this.2
  · intro α hα hαh d
    refine ⟨xE_mem_URge hα hαh d, ?_⟩
    by_cases hαeq : ht α = h
    · refine ⟨Pi.single α d, ?_⟩
      rw [Pl_single R (mem_Lay.2 ⟨hα, hαeq⟩)]
      exact Cong.refl R h _
    · refine ⟨0, ?_⟩
      rw [Pl_zero]
      have hlt : ((h + 1 : ℕ) : ℤ) ≤ ht α := by push_cast; omega
      simpa [Cong] using xE_mem_URge hα hlt d
  · exact ⟨Subgroup.one_mem _, 0, by rw [Pl_zero]; exact Cong.refl R h _⟩
  · intro x y hx hy
    obtain ⟨hxm, c, hc⟩ := hx
    obtain ⟨hym, c', hc'⟩ := hy
    refine ⟨Subgroup.mul_mem _ hxm hym, c + c', ?_⟩
    have h1 : Cong R h (Pl R h c * Pl R h c') (x * Pl R h c') := Cong.mul_right hR hc
      (URge_anti hh (Pl_mem R c'))
    have h2 : Cong R h (x * Pl R h c') (x * y) := Cong.mul_left _ hc'
    exact (Pl_add hR hh c c').symm.trans (h1.trans h2)

theorem endoE_PL (L : List Rt) (c : Rt → K) :
    endoE (PL L c) = (L.map fun γ => (1 : Module.End K (V K)) + c γ • e7Data.rootOp K γ).prod := by
  induction L with
  | nil => exact endoE_one
  | cons α L ih => rw [PL_cons, endoE_mul, ih, endoE_xE]; simp

set_option maxRecDepth 20000 in
theorem rootOp_raises_levH [CharP K 2] {γ : Rt} (hγ : IsRoot .E7 γ) {h : ℕ} (hh : ht γ = h) :
    Raises levH (D7 * h) (e7Data.rootOp K γ) := by
  intro b b' hne
  rw [rootOp_single hγ] at hne
  by_cases hb : pr b γ = -1
  · rw [if_pos hb, Finsupp.single_apply] at hne
    by_cases hs : shift γ b = b'
    · rw [← hs, levH_shift hγ hb, hh]
    · rw [if_neg hs] at hne
      exact absurd rfl hne
  · rw [if_neg hb] at hne
    exact absurd rfl hne

theorem exists_pr_neg_one {δ : Rt} (hδ : IsRoot .E7 δ) : ∃ b : Fin e7Data.d, pr b δ = -1 := by
  have h12 := (card_pr hδ).2.1
  have hpos : 0 < (Finset.univ.filter fun a : Fin e7Data.d => pr a δ = -1).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.1 hpos
  exact ⟨b, (Finset.mem_filter.1 hb).2⟩

theorem sum_ite_eq_of_nodup' {α M : Type*} [DecidableEq α] [AddCommMonoid M] (L : List α)
    (hnd : L.Nodup) (δ : α) (f : α → M) :
    (L.map fun γ => if γ = δ then f γ else 0).sum = if δ ∈ L then f δ else 0 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons, ih hnd.2]
    by_cases hx : x = δ
    · subst hx
      simp [hnd.1]
    · simp [hx, Ne.symm hx]

set_option maxRecDepth 20000 in
theorem PL_entry [CharP K 2] {L : List Rt} (hnd : L.Nodup) {h : ℕ} (hh : 1 ≤ h)
    (hL : ∀ γ ∈ L, IsRoot .E7 γ ∧ ht γ = h) (c : Rt → K) {δ : Rt} (hδL : δ ∈ L) {b : Fin e7Data.d}
    (hb : pr b δ = -1) :
    (endoE (PL L c) (Finsupp.single b 1)) (shift δ b) = c δ := by
  have hD := D7_pos
  have hd : 0 < D7 * (h : ℤ) := by positivity
  have hδ := (hL δ hδL).1
  have hlev : levH (shift δ b) = levH b + D7 * h := by
    rw [levH_shift hδ hb, (hL δ hδL).2]
  rw [endoE_PL]
  rw [prod_coord levH hd L (fun γ => e7Data.rootOp K γ) c
    (fun γ hγ => rootOp_raises_levH (hL γ hγ).1 (hL γ hγ).2) b (shift δ b) hlev]
  have hterm : ∀ γ ∈ L, c γ * (e7Data.rootOp K γ (Finsupp.single b 1)) (shift δ b) =
      if γ = δ then c γ else 0 := by
    intro γ hγ
    rw [rootOp_single (hL γ hγ).1]
    by_cases hbγ : pr b γ = -1
    · rw [if_pos hbγ, Finsupp.single_apply]
      by_cases hγδ : γ = δ
      · subst hγδ
        simp
      · have hne : shift γ b ≠ shift δ b := fun e => hγδ (toWeight_injective posDef_cartan_E7 (by
          have h1 := wt_shift (hL γ hγ).1 hbγ
          have h2 := wt_shift hδ hb
          rw [e] at h1
          exact add_left_cancel (h1.symm.trans h2)))
        rw [if_neg hne, if_neg hγδ, mul_zero]
    · rw [if_neg hbγ]
      by_cases hγδ : γ = δ
      · exfalso
        subst hγδ
        exact hbγ hb
      · simp [hγδ]
  rw [List.map_congr_left hterm, sum_ite_eq_of_nodup' L hnd δ c, if_pos hδL]

set_option maxRecDepth 20000 in
theorem Pl_mem_succ_imp (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) {c : Rt → K}
    (hc : Pl R h c ∈ URge K R (h + 1)) : ∀ δ ∈ Lay R h, c δ = 0 := by
  intro δ hδ
  obtain ⟨hδR, hδh⟩ := mem_Lay.1 hδ
  obtain ⟨b, hb⟩ := exists_pr_neg_one (hR.root δ hδR)
  have hD := D7_pos
  have hlev : levH (shift δ b) = levH b + D7 * h := by
    rw [levH_shift (hR.root δ hδR) hb, hδh]
  have hA := PL_entry (K := K) (Finset.nodup_toList (Lay R h)) hh
    (fun γ hγ => ⟨hR.root γ (mem_Lay.1 (Finset.mem_toList.1 hγ)).1,
      (mem_Lay.1 (Finset.mem_toList.1 hγ)).2⟩) c (Finset.mem_toList.2 hδ) hb
  have hraise := endoE_sub_one_hasRaise hR hc b
  have hcoord := (mem_Fil.1 hraise) (shift δ b) (by
    rw [hlev]
    have : D7 * (h : ℤ) < D7 * ((h + 1 : ℕ) : ℤ) := by
      push_cast
      nlinarith
    omega)
  have hne : shift δ b ≠ b := fun e => by
    rw [e] at hlev
    have : 0 < D7 * (h : ℤ) := by positivity
    omega
  simp only [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply,
    Finsupp.single_apply, if_neg hne.symm] at hcoord
  have e : Pl R h c = PL (Lay R h).toList c := rfl
  rw [e] at hcoord
  rw [hA] at hcoord
  simpa using hcoord

abbrev Tt (K : Type) [Field K] : Type := Fin (Tag.rank .E7) → Kˣ

@[expose] def chi (α : Rt) : Tt K →* Kˣ where
  toFun t := ((List.finRange (Tag.rank .E7)).map fun i => t i ^ MinData.toWeight α i).prod
  map_one' := by simp
  map_mul' s t := by
    rw [← List.prod_map_mul]
    refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
    simp [mul_zpow]

@[expose] def tau (t : Tt K) : Gp K :=
  ((List.finRange (Tag.rank .E7)).map fun i => e7Data_valid.hm K i (t i)).prod

set_option maxRecDepth 20000 in
theorem tau_conj_xE_aux {α : Rt} (hα : IsRoot .E7 α) (t : Tt K) (c : K) (l : List (Fin (Tag.rank .E7))) :
    (l.map fun i => e7Data_valid.hm K i (t i)).prod * xE α c *
        ((l.map fun i => e7Data_valid.hm K i (t i)).prod)⁻¹ =
      xE α ((((l.map fun i => t i ^ MinData.toWeight α i).prod : Kˣ) : K) * c) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    have e : (e7Data_valid.hm K i (t i) * (l.map fun i => e7Data_valid.hm K i (t i)).prod) * xE α c *
        (e7Data_valid.hm K i (t i) * (l.map fun i => e7Data_valid.hm K i (t i)).prod)⁻¹ =
        e7Data_valid.hm K i (t i) * ((l.map fun i => e7Data_valid.hm K i (t i)).prod * xE α c *
          ((l.map fun i => e7Data_valid.hm K i (t i)).prod)⁻¹) * (e7Data_valid.hm K i (t i))⁻¹ := by
      group
    rw [e, ih]
    have := e7Data_valid.hm_conj_xm K hα i (t i) ((((l.map fun i => t i ^ MinData.toWeight α i).prod : Kˣ) : K) * c)
    rw [this]
    congr 1
    simp [mul_assoc]

set_option maxRecDepth 20000 in
theorem tau_conj_xE {α : Rt} (hα : IsRoot .E7 α) (t : Tt K) (c : K) :
    tau t * xE α c * (tau t)⁻¹ = xE α (((chi α t : Kˣ) : K) * c) :=
  tau_conj_xE_aux hα t c _

theorem conj_tau_mem_URge (hR : Closed R) (t : Tt K) {h : ℕ} {g : Gp K} (hg : g ∈ URge K R h) :
    tau t * g * (tau t)⁻¹ ∈ URge K R h := by
  refine URge_induction (C := fun g => tau t * g * (tau t)⁻¹ ∈ URge K R h) hg ?_ ?_ ?_
  · intro α hα hαh c
    rw [tau_conj_xE (hR.root α hα)]
    exact xE_mem_URge hα hαh _
  · simp
  · intro x y hx hy
    have : tau t * (x * y) * (tau t)⁻¹ = (tau t * x * (tau t)⁻¹) * (tau t * y * (tau t)⁻¹) := by
      group
    rw [this]
    exact Subgroup.mul_mem _ hx hy

theorem conj_tau_PL (hR : Closed R) (t : Tt K) {L : List Rt} (hL : ∀ α ∈ L, α ∈ R) (c : Rt → K) :
    tau t * PL L c * (tau t)⁻¹ = PL L (fun α => ((chi α t : Kˣ) : K) * c α) := by
  induction L with
  | nil => simp [PL_nil]
  | cons α L ih =>
    have hα := hL α List.mem_cons_self
    have hL' : ∀ β ∈ L, β ∈ R := fun β hβ => hL β (List.mem_cons_of_mem _ hβ)
    rw [PL_cons, PL_cons]
    have e : tau t * (xE α (c α) * PL L c) * (tau t)⁻¹ =
        (tau t * xE α (c α) * (tau t)⁻¹) * (tau t * PL L c * (tau t)⁻¹) := by group
    rw [e, tau_conj_xE (hR.root α hα), ih hL']

theorem Cong.conj_tau (hR : Closed R) (t : Tt K) {h : ℕ} {x y : Gp K} (hxy : Cong R h x y) :
    Cong R h (tau t * x * (tau t)⁻¹) (tau t * y * (tau t)⁻¹) := by
  have := conj_tau_mem_URge hR t hxy
  have e : tau t * (x⁻¹ * y) * (tau t)⁻¹ =
      (tau t * x * (tau t)⁻¹)⁻¹ * (tau t * y * (tau t)⁻¹) := by group
  rw [e] at this
  exact this

theorem Pl_congr (R : Finset Rt) {h : ℕ} {c c' : Rt → K} (hcc : ∀ α ∈ Lay R h, c α = c' α) :
    Pl R h c = Pl R h c' := by
  unfold Pl PL
  congr 1
  exact List.map_congr_left fun α hα => by rw [hcc α (Finset.mem_toList.1 hα)]

@[expose] def extLay (R : Finset Rt) (h : ℕ) (c : ↥(Lay R h) → K) : Rt → K :=
  fun α => if hα : α ∈ Lay R h then c ⟨α, hα⟩ else 0

theorem extLay_add (R : Finset Rt) (h : ℕ) (c c' : ↥(Lay R h) → K) :
    extLay R h (c + c') = extLay R h c + extLay R h c' := by
  funext α
  by_cases hα : α ∈ Lay R h <;> simp [extLay, hα]

theorem extLay_zero (R : Finset Rt) (h : ℕ) : extLay R h (0 : ↥(Lay R h) → K) = 0 := by
  funext α
  by_cases hα : α ∈ Lay R h <;> simp [extLay, hα]

@[expose] def layCoord (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) (g : ↥(URge K R h)) :
    ↥(Lay R h) → K :=
  fun α => (Classical.choose (coord_exists hR hh g.2)) α.1

theorem layCoord_spec (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) (g : ↥(URge K R h)) :
    Cong R h (Pl R h (extLay R h (layCoord hR hh g))) g.1 := by
  have := Classical.choose_spec (coord_exists hR hh g.2)
  rw [Pl_congr R (c' := Classical.choose (coord_exists hR hh g.2)) (fun α hα => by
    simp [extLay, hα, layCoord])]
  exact this

theorem coord_unique (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) {c c' : Rt → K}
    (hcc : Cong R h (Pl R h c) (Pl R h c')) : ∀ δ ∈ Lay R h, c δ = c' δ := by
  have h1 := Pl_add hR hh c (c' - c)
  rw [add_sub_cancel] at h1
  have h2 : Cong R h (Pl R h c * Pl R h (c' - c)) (Pl R h c * 1) := by
    rw [mul_one]
    exact h1.trans hcc.symm
  have h3 : Pl R h (c' - c) ∈ URge K R (h + 1) := by
    have : Cong R h (Pl R h (c' - c)) 1 := by
      have := h2
      unfold Cong at this ⊢
      simpa [mul_assoc] using this
    have h4 := Subgroup.inv_mem _ this
    simpa [Cong] using h4
  intro δ hδ
  have := Pl_mem_succ_imp hR hh h3 δ hδ
  simpa [sub_eq_zero, eq_comm] using this

theorem layCoord_eq_of_cong (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) (g : ↥(URge K R h))
    {c : Rt → K} (hc : Cong R h (Pl R h c) g.1) :
    layCoord hR hh g = fun α => c α.1 := by
  funext α
  have h1 := coord_unique hR hh (hc.trans (layCoord_spec hR hh g).symm) α.1 α.2
  have h2 : extLay R h (layCoord hR hh g) α.1 = layCoord hR hh g α := by
    simp [extLay, α.2]
  rw [h2] at h1
  exact h1.symm

theorem layCoord_mul (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) (g g' : ↥(URge K R h)) :
    layCoord hR hh (g * g') = layCoord hR hh g + layCoord hR hh g' := by
  have hs := layCoord_spec hR hh g
  have hs' := layCoord_spec hR hh g'
  have h1 : Cong R h (Pl R h (extLay R h (layCoord hR hh g)) * Pl R h (extLay R h (layCoord hR hh g')))
      (g.1 * g'.1) :=
    (Cong.mul_right hR hs (URge_anti hh g'.2 |> fun _ => URge_anti hh (Pl_mem R _))).trans
      (Cong.mul_left _ hs')
  have h2 := (Pl_add hR hh (extLay R h (layCoord hR hh g)) (extLay R h (layCoord hR hh g'))).symm.trans h1
  rw [← extLay_add] at h2
  have := layCoord_eq_of_cong hR hh (g * g') (c := extLay R h (layCoord hR hh g + layCoord hR hh g')) h2
  rw [this]
  funext α
  simp [extLay, α.2]

theorem layCoord_one (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) :
    layCoord hR hh (1 : ↥(URge K R h)) = 0 := by
  have := layCoord_eq_of_cong hR hh (1 : ↥(URge K R h)) (c := 0) (by
    rw [Pl_zero]; exact Cong.refl R h _)
  rw [this]
  rfl

@[expose] def layHom (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) :
    ↥(URge K R h) →* Multiplicative (↥(Lay R h) → K) where
  toFun g := Multiplicative.ofAdd (layCoord hR hh g)
  map_one' := by simp [layCoord_one]
  map_mul' g g' := by simp [layCoord_mul]

theorem layHom_apply (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) (g : ↥(URge K R h)) :
    layHom hR hh g = Multiplicative.ofAdd (layCoord hR hh g) := rfl

theorem layHom_eq_one_iff (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) (g : ↥(URge K R h)) :
    layHom hR hh g = 1 ↔ g.1 ∈ URge K R (h + 1) := by
  rw [layHom_apply]
  constructor
  · intro h0
    have h1 : layCoord hR hh g = 0 := h0
    have := layCoord_spec hR hh g
    rw [h1, extLay_zero, Pl_zero] at this
    simpa [Cong] using this
  · intro hg
    have h1 : layCoord hR hh g = fun α => (0 : Rt → K) α.1 := by
      refine layCoord_eq_of_cong hR hh g (c := 0) ?_
      rw [Pl_zero]
      simpa [Cong] using hg
    exact h1

theorem layHom_xE (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) {α : Rt} (hα : α ∈ Lay R h)
    (d : K) :
    layHom hR hh ⟨xE α d, xE_mem_URge (mem_Lay.1 hα).1 (mem_Lay.1 hα).2.ge d⟩ =
      Multiplicative.ofAdd (Pi.single (⟨α, hα⟩ : ↥(Lay R h)) d) := by
  rw [layHom_apply]
  congr 1
  have hcong : Cong R h (Pl R h (Pi.single α d))
      (xE α d : Gp K) := by
    rw [Pl_single R hα]
    exact Cong.refl R h _
  have := layCoord_eq_of_cong hR hh
    (⟨xE α d, xE_mem_URge (mem_Lay.1 hα).1 (mem_Lay.1 hα).2.ge d⟩ : ↥(URge K R h)) hcong
  rw [this]
  funext β
  by_cases hβ : β = (⟨α, hα⟩ : ↥(Lay R h))
  · subst hβ; simp
  · have : β.1 ≠ α := fun e => hβ (Subtype.ext e)
    simp [Pi.single_apply, hβ, this]

theorem layHom_surjective (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) :
    Function.Surjective (layHom (K := K) hR hh) := by
  intro x
  let c := Multiplicative.toAdd x
  refine ⟨⟨Pl R h (extLay R h c), Pl_mem R _⟩, ?_⟩
  rw [layHom_apply]
  have := layCoord_eq_of_cong hR hh ⟨Pl R h (extLay R h c), Pl_mem R _⟩
    (c := extLay R h c) (Cong.refl R h _)
  rw [this]
  apply Multiplicative.toAdd.injective
  funext α
  simp [c, extLay, α.2]

theorem layHom_conj_tau (hR : Closed R) [CharP K 2] {h : ℕ} (hh : 1 ≤ h) (t : Tt K)
    (g : ↥(URge K R h)) :
    layHom hR hh ⟨tau t * g.1 * (tau t)⁻¹, conj_tau_mem_URge hR t g.2⟩ =
      Multiplicative.ofAdd (fun α : ↥(Lay R h) => ((chi α.1 t : Kˣ) : K) * layCoord hR hh g α) := by
  rw [layHom_apply]
  congr 1
  have hs := (layCoord_spec hR hh g).conj_tau hR t
  have e : tau t * Pl R h (extLay R h (layCoord hR hh g)) * (tau t)⁻¹ =
      Pl R h (fun α => ((chi α t : Kˣ) : K) * extLay R h (layCoord hR hh g) α) :=
    conj_tau_PL hR t (L := (Lay R h).toList)
      (fun α hα => (mem_Lay.1 (Finset.mem_toList.1 hα)).1) _
  rw [e] at hs
  have := layCoord_eq_of_cong hR hh
    (⟨tau t * g.1 * (tau t)⁻¹, conj_tau_mem_URge hR t g.2⟩ : ↥(URge K R h)) hs
  rw [this]
  funext α
  simp [extLay, α.2]

theorem comm_cong (hR : Closed R) [CharP K 2] {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {x f y f' : Gp K}
    (hx : x ∈ URge K R h) (hy : y ∈ URge K R k) (hf : f ∈ URge K R (h + 1))
    (hf' : f' ∈ URge K R (k + 1)) :
    Cong R (h + k) ⁅x, y⁆ ⁅x * f, y * f'⁆ := by
  have hyf' : y * f' ∈ URge K R k := Subgroup.mul_mem _ hy (URge_anti (Nat.le_succ k) hf')
  have hm1 : ⁅f, y * f'⁆ ∈ URge K R (h + 1 + k) :=
    comm_mem_URge hR (by omega) hk hf hyf'
  have hm2 : ⁅x, f'⁆ ∈ URge K R (h + (k + 1)) := comm_mem_URge hR hh (by omega) hx hf'
  have hxU : x ∈ URge K R 1 := URge_anti hh hx
  have hyU : y ∈ URge K R 1 := URge_anti hk hy
  have e : ⁅x * f, y * f'⁆ = (x * ⁅f, y * f'⁆ * x⁻¹) * (⁅x, y⁆ * (y * ⁅x, f'⁆ * y⁻¹)) := by
    rw [comm_mul_left', comm_mul_right']
    group
  have hn1 : x * ⁅f, y * f'⁆ * x⁻¹ ∈ URge K R (h + k + 1) := by
    have := conj_mem_URge hR hxU hm1
    convert this using 2
    omega
  have hn2 : y * ⁅x, f'⁆ * y⁻¹ ∈ URge K R (h + k + 1) := by
    have := conj_mem_URge hR hyU hm2
    convert this using 2
  have hc : ⁅x, y⁆ ∈ URge K R 1 := URge_anti (by omega) (comm_mem_URge hR hh hk hx hy)
  show ⁅x, y⁆⁻¹ * ⁅x * f, y * f'⁆ ∈ URge K R (h + k + 1)
  rw [e]
  have : ⁅x, y⁆⁻¹ * ((x * ⁅f, y * f'⁆ * x⁻¹) * (⁅x, y⁆ * (y * ⁅x, f'⁆ * y⁻¹))) =
      (⁅x, y⁆⁻¹ * (x * ⁅f, y * f'⁆ * x⁻¹) * ⁅x, y⁆⁻¹⁻¹) * (y * ⁅x, f'⁆ * y⁻¹) := by group
  rw [this]
  refine Subgroup.mul_mem _ ?_ hn2
  exact conj_mem_URge hR (Subgroup.inv_mem _ hc) hn1

@[expose] def HasRaiseL (lev : Fin e7Data.d → ℤ) (n : ℤ) (φ : Module.End K (V K)) : Prop :=
  ∀ b, φ (Finsupp.single b 1) ∈ Fil lev (lev b + n)

theorem HasRaiseL.map_Fil {lev : Fin e7Data.d → ℤ} {n : ℤ} {φ : Module.End K (V K)}
    (hφ : HasRaiseL lev n φ) {k : ℤ} {v : V K} (hv : v ∈ Fil lev k) : φ v ∈ Fil lev (k + n) := by
  rw [mem_Fil]
  intro b' hb'
  have hsum : v = ∑ b ∈ v.support, v b • Finsupp.single b (1 : K) := by
    conv_lhs => rw [← Finsupp.sum_single v]
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finsupp.smul_single_one]
  rw [hsum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hvb : v b ≠ 0 := Finsupp.mem_support_iff.mp hb
  have hkb : k ≤ lev b := by
    by_contra hcon
    exact hvb ((mem_Fil.mp hv) b (not_le.mp hcon))
  have h2 := (mem_Fil.mp (hφ b)) b' (by omega)
  rw [h2, mul_zero]

theorem HasRaiseL.mono {lev : Fin e7Data.d → ℤ} {n m : ℤ} (hnm : m ≤ n) {φ : Module.End K (V K)}
    (h : HasRaiseL lev n φ) : HasRaiseL lev m φ := fun b => Fil_mono (by omega) (h b)

theorem HasRaiseL.add {lev : Fin e7Data.d → ℤ} {n : ℤ} {φ ψ : Module.End K (V K)}
    (hφ : HasRaiseL lev n φ) (hψ : HasRaiseL lev n ψ) : HasRaiseL lev n (φ + ψ) := fun b => by
  rw [LinearMap.add_apply]
  exact Submodule.add_mem _ (hφ b) (hψ b)

theorem HasRaiseL.zero (lev : Fin e7Data.d → ℤ) (n : ℤ) : HasRaiseL lev n (0 : Module.End K (V K)) :=
  fun b => by
    rw [LinearMap.zero_apply]
    exact Submodule.zero_mem _

theorem HasRaiseL.smul {lev : Fin e7Data.d → ℤ} {n : ℤ} {φ : Module.End K (V K)}
    (hφ : HasRaiseL lev n φ) (c : K) : HasRaiseL lev n (c • φ) := fun b => by
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ c (hφ b)

theorem HasRaiseL.mul {lev : Fin e7Data.d → ℤ} {n m : ℤ} {φ ψ : Module.End K (V K)}
    (hφ : HasRaiseL lev n φ) (hψ : HasRaiseL lev m ψ) : HasRaiseL lev (n + m) (φ * ψ) :=
  fun b => by
    rw [Module.End.mul_apply]
    have := hφ.map_Fil (hψ b)
    convert this using 2
    ring

theorem HasRaiseL.sub {lev : Fin e7Data.d → ℤ} {n : ℤ} {φ ψ : Module.End K (V K)}
    (hφ : HasRaiseL lev n φ) (hψ : HasRaiseL lev n ψ) : HasRaiseL lev n (φ - ψ) := fun b => by
  rw [LinearMap.sub_apply]
  exact Submodule.sub_mem _ (hφ b) (hψ b)

@[expose] def levF (f : (Fin (Tag.rank .E7) → ℤ) →+ ℤ) : Fin e7Data.d → ℤ := e7Data.fgrade f

theorem levF_shift (f : (Fin (Tag.rank .E7) → ℤ) →+ ℤ) {γ : Rt} (hγ : IsRoot .E7 γ)
    {b : Fin e7Data.d} (hb : pr b γ = -1) : levF f (shift γ b) = levF f b + D7 * f γ := by
  unfold D7
  exact e7Data.isGrading_fgrade f b (shift γ b) γ (wt_shift hγ hb)

set_option maxRecDepth 20000 in
theorem rootOp_hasRaiseL [CharP K 2] (f : (Fin (Tag.rank .E7) → ℤ) →+ ℤ) {γ : Rt}
    (hγ : IsRoot .E7 γ) : HasRaiseL (levF f) (D7 * f γ) (e7Data.rootOp K γ) := by
  intro b
  rw [rootOp_single hγ]
  by_cases hb : pr b γ = -1
  · rw [if_pos hb]
    have h1 := single_mem_Fil (K := K) (levF f) (shift γ b)
    rwa [levF_shift f hγ hb] at h1
  · rw [if_neg hb]
    exact Submodule.zero_mem _

set_option maxRecDepth 20000 in
theorem endoE_sub_one_hasRaiseL [CharP K 2] (f : (Fin (Tag.rank .E7) → ℤ) →+ ℤ) {m : ℤ}
    (hm : 0 ≤ m) {R : Finset Rt} (hR : ∀ α ∈ R, IsRoot .E7 α ∧ m ≤ f α) {g : Gp K}
    (hg : g ∈ URge K R 1) : HasRaiseL (levF f) (D7 * m) (endoE g - 1) := by
  have hpos := D7_pos
  have hnn : (0 : ℤ) ≤ D7 * m := by positivity
  refine URge_induction (C := fun g => HasRaiseL (levF f) (D7 * m) (endoE g - 1)) hg ?_ ?_ ?_
  · intro α hα _ c
    rw [endoE_xE, add_sub_cancel_left]
    have h1 : HasRaiseL (levF f) (D7 * f α) (e7Data.rootOp K α) :=
      rootOp_hasRaiseL f (hR α hα).1
    have h2 : HasRaiseL (levF f) (D7 * m) (e7Data.rootOp K α) :=
      h1.mono (mul_le_mul_of_nonneg_left (hR α hα).2 hpos.le)
    exact h2.smul c
  · rw [endoE_one, sub_self]
    exact HasRaiseL.zero _ _
  · intro x y hx hy
    rw [endoE_mul]
    have e : endoE x * endoE y - 1 =
        (endoE x - 1) * (endoE y - 1) + (endoE x - 1) + (endoE y - 1) := by
      noncomm_ring
    rw [e]
    refine ((hx.mul hy).mono ?_).add hx |>.add hy
    omega

theorem levF_neg (f : (Fin (Tag.rank .E7) → ℤ) →+ ℤ) (b : Fin e7Data.d) :
    levF (-f) b = - levF f b := by
  unfold levF MinData.fgrade
  have h : (fun j => (-f) (Pi.single j 1)) = -(fun j => f (Pi.single j 1)) := by
    funext j; simp
  rw [h, Matrix.neg_vecMul, neg_dotProduct]

theorem endoE_injective' : Function.Injective (endoE (K := K)) := e7Data_valid.endo_injective K

theorem URge_inf_URge_eq_bot [CharP K 2] (f : (Fin (Tag.rank .E7) → ℤ) →+ ℤ) {R' N : Finset Rt}
    (h0 : ∀ α ∈ R', IsRoot .E7 α ∧ f α = 0) (h1 : ∀ α ∈ N, IsRoot .E7 α ∧ f α = 1) :
    URge K R' 1 ⊓ URge K N 1 = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hg0, hg1⟩ := Subgroup.mem_inf.1 hg
  have hN := endoE_sub_one_hasRaiseL f (m := 1) (by norm_num)
    (fun α hα => ⟨(h1 α hα).1, (h1 α hα).2.ge⟩) hg1
  have hR := endoE_sub_one_hasRaiseL (-f) (m := 0) (le_refl _)
    (fun α hα => ⟨(h0 α hα).1, by simp [(h0 α hα).2]⟩) hg0
  have hD := D7_pos
  rw [Subgroup.mem_bot]
  refine endoE_injective' ?_
  rw [endoE_one]
  have key : ∀ a b', ((endoE g - 1) (Finsupp.single a 1)) b' = 0 := by
    intro a b'
    by_cases hlt : levF f b' < levF f a + D7 * 1
    · exact (mem_Fil.1 (hN a)) b' hlt
    · refine (mem_Fil.1 (hR a)) b' ?_
      rw [levF_neg, levF_neg]
      omega
  refine ext_single fun a => ?_
  refine Finsupp.ext fun b' => ?_
  have := key a b'
  simp only [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply] at this
  rw [Module.End.one_apply]
  exact sub_eq_zero.1 this

theorem URge_mono_R {R R' : Finset Rt} (hRR : R ⊆ R') {h : ℕ} : URge K R h ≤ URge K R' h := by
  refine iSup₂_le fun α hα => ?_
  obtain ⟨hαR, hαh⟩ := Finset.mem_filter.1 hα
  exact XR_le_URge (hRR hαR) hαh

section Split

variable (f : (Fin (Tag.rank .E7) → ℤ) →+ ℤ)

@[expose] def Rp (R : Finset Rt) : Finset Rt := R.filter fun α => f α = 0

@[expose] def Rn (R : Finset Rt) : Finset Rt := R.filter fun α => f α = 1

variable {f}

theorem Rp_subset (R : Finset Rt) : Rp f R ⊆ R := Finset.filter_subset _ _

theorem Rn_subset (R : Finset Rt) : Rn f R ⊆ R := Finset.filter_subset _ _

theorem closed_Rp (hR : Closed R) : Closed (Rp f R) where
  root α hα := hR.root α (Finset.mem_filter.1 hα).1
  pos α hα := hR.pos α (Finset.mem_filter.1 hα).1
  add α hα β hβ hroot := by
    obtain ⟨hαR, hα0⟩ := Finset.mem_filter.1 hα
    obtain ⟨hβR, hβ0⟩ := Finset.mem_filter.1 hβ
    exact Finset.mem_filter.2 ⟨hR.add α hαR β hβR hroot, by rw [map_add, hα0, hβ0]; rfl⟩

theorem closed_Rn (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) (hR : Closed R) :
    Closed (Rn f R) where
  root α hα := hR.root α (Finset.mem_filter.1 hα).1
  pos α hα := hR.pos α (Finset.mem_filter.1 hα).1
  add α hα β hβ hroot := by
    obtain ⟨hαR, hα1⟩ := Finset.mem_filter.1 hα
    obtain ⟨hβR, hβ1⟩ := Finset.mem_filter.1 hβ
    exfalso
    rcases hf _ (hR.add α hαR β hβR hroot) with h | h <;> rw [map_add, hα1, hβ1] at h <;> omega

theorem UN_normal (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) (hR : Closed R)
    [CharP K 2] {u : Gp K} (hu : u ∈ URge K R 1) {g : Gp K} (hg : g ∈ URge K (Rn f R) 1) :
    u * g * u⁻¹ ∈ URge K (Rn f R) 1 := by
  have gen : ∀ β ∈ R, ∀ c : K, ∀ g : Gp K, g ∈ URge K (Rn f R) 1 →
      xE β c * g * (xE β c)⁻¹ ∈ URge K (Rn f R) 1 := by
    intro β hβ c g hg
    refine URge_induction (C := fun g => xE β c * g * (xE β c)⁻¹ ∈ URge K (Rn f R) 1) hg ?_ ?_ ?_
    · intro α hα hα1 d
      obtain ⟨hαR, hαf⟩ := Finset.mem_filter.1 hα
      have hne : β + α ≠ 0 := add_ne_zero_of_pos hR hβ hαR
      have hconj : xE β c * xE α d * (xE β c)⁻¹ = ⁅xE β c, xE α d⁆ * xE α d := by
        rw [commutatorElement_def]; group
      rw [hconj, comm_xE (hR.root β hβ) (hR.root α hαR) hne c d]
      refine Subgroup.mul_mem _ ?_ (xE_mem_URge hα hα1 d)
      split_ifs with hr
      · refine xE_mem_URge ?_ ?_ _
        · refine Finset.mem_filter.2 ⟨hR.add β hβ α hαR hr, ?_⟩
          have hfβ := hf β hβ
          rcases hf _ (hR.add β hβ α hαR hr) with h | h
          · rw [map_add, hαf] at h; omega
          · exact h
        · have := hR.pos (β + α) (hR.add β hβ α hαR hr); omega
      · exact Subgroup.one_mem _
    · simp
    · intro x y hx hy
      have : xE β c * (x * y) * (xE β c)⁻¹ = (xE β c * x * (xE β c)⁻¹) * (xE β c * y * (xE β c)⁻¹) := by
        group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
  have key : ∀ u : Gp K, u ∈ URge K R 1 →
      ∀ g : Gp K, g ∈ URge K (Rn f R) 1 → u * g * u⁻¹ ∈ URge K (Rn f R) 1 := by
    intro u hu
    refine URge_induction (C := fun u => ∀ g : Gp K, g ∈ URge K (Rn f R) 1 →
      u * g * u⁻¹ ∈ URge K (Rn f R) 1) hu ?_ ?_ ?_
    · intro β hβ _ c g hg
      exact gen β hβ c g hg
    · intro g hg
      simpa using hg
    · intro x y hx hy g hg
      have : x * y * g * (x * y)⁻¹ = x * (y * g * y⁻¹) * x⁻¹ := by group
      rw [this]
      exact hx _ (hy g hg)
  exact key u hu g hg

theorem exists_decomp (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) (hR : Closed R) [CharP K 2] {g : Gp K} (hg : g ∈ URge K R 1) :
    ∃ u ∈ URge K (Rp f R) 1, ∃ v ∈ URge K (Rn f R) 1, g = u * v := by
  refine URge_induction (C := fun g => ∃ u ∈ URge K (Rp f R) 1, ∃ v ∈ URge K (Rn f R) 1, g = u * v)
    hg ?_ ?_ ?_
  · intro α hα hα1 c
    rcases hf α hα with h | h
    · exact ⟨xE α c, xE_mem_URge (Finset.mem_filter.2 ⟨hα, h⟩) hα1 c, 1, Subgroup.one_mem _, by simp⟩
    · exact ⟨1, Subgroup.one_mem _, xE α c, xE_mem_URge (Finset.mem_filter.2 ⟨hα, h⟩) hα1 c, by simp⟩
  · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
  · rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨u', hu', v', hv', rfl⟩
    refine ⟨u * u', Subgroup.mul_mem _ hu hu', (u'⁻¹ * v * u'⁻¹⁻¹) * v',
      Subgroup.mul_mem _ ?_ hv', by group⟩
    exact UN_normal hf hR (Subgroup.inv_mem _ (URge_mono_R (Rp_subset R) hu')) hv

theorem decomp_unique [CharP K 2] (hR : Closed R) {u u' v v' : Gp K} (hu : u ∈ URge K (Rp f R) 1)
    (hu' : u' ∈ URge K (Rp f R) 1) (hv : v ∈ URge K (Rn f R) 1) (hv' : v' ∈ URge K (Rn f R) 1)
    (h : u * v = u' * v') : u = u' := by
  have hbot := URge_inf_URge_eq_bot (K := K) f (R' := Rp f R) (N := Rn f R)
    (fun α hα => ⟨hR.root α (Finset.mem_filter.1 hα).1, (Finset.mem_filter.1 hα).2⟩)
    (fun α hα => ⟨hR.root α (Finset.mem_filter.1 hα).1, (Finset.mem_filter.1 hα).2⟩)
  have h1 : u'⁻¹ * u = v' * v⁻¹ := by
    have : u' * (v' * v⁻¹) = u := by
      calc u' * (v' * v⁻¹) = (u' * v') * v⁻¹ := by group
        _ = (u * v) * v⁻¹ := by rw [h]
        _ = u := by group
    calc u'⁻¹ * u = u'⁻¹ * (u' * (v' * v⁻¹)) := by rw [this]
      _ = v' * v⁻¹ := by group
  have hmem : u'⁻¹ * u ∈ URge K (Rp f R) 1 ⊓ URge K (Rn f R) 1 :=
    Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hu') hu,
      by rw [h1]; exact Subgroup.mul_mem _ hv' (Subgroup.inv_mem _ hv)⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  calc u = u' * (u'⁻¹ * u) := by group
    _ = u' := by rw [hmem, mul_one]

@[expose] def prC (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) [CharP K 2] (hR : Closed R) (g : ↥(URge K R 1)) : Gp K :=
  Classical.choose (exists_decomp hf hR g.2)

theorem prC_mem (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) [CharP K 2] (hR : Closed R) (g : ↥(URge K R 1)) :
    prC hf hR g ∈ URge K (Rp f R) 1 :=
  (Classical.choose_spec (exists_decomp hf hR g.2)).1

theorem prC_spec (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) [CharP K 2] (hR : Closed R) (g : ↥(URge K R 1)) :
    ∃ v ∈ URge K (Rn f R) 1, g.1 = prC hf hR g * v :=
  (Classical.choose_spec (exists_decomp hf hR g.2)).2

theorem prC_eq (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) [CharP K 2] (hR : Closed R) (g : ↥(URge K R 1)) {u v : Gp K}
    (hu : u ∈ URge K (Rp f R) 1) (hv : v ∈ URge K (Rn f R) 1) (h : g.1 = u * v) :
    prC hf hR g = u := by
  obtain ⟨v₀, hv₀, h₀⟩ := prC_spec hf hR g
  exact decomp_unique hR (prC_mem hf hR g) hu hv₀ hv (h₀.symm.trans h)

theorem prC_mul (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) [CharP K 2] (hR : Closed R) (g g' : ↥(URge K R 1)) :
    prC hf hR (g * g') = prC hf hR g * prC hf hR g' := by
  obtain ⟨v, hv, h⟩ := prC_spec hf hR g
  obtain ⟨v', hv', h'⟩ := prC_spec hf hR g'
  refine prC_eq hf hR (g * g') (Subgroup.mul_mem _ (prC_mem hf hR g) (prC_mem hf hR g'))
    (v := ((prC hf hR g')⁻¹ * v * (prC hf hR g')⁻¹⁻¹) * v') ?_ ?_
  · refine Subgroup.mul_mem _ ?_ hv'
    exact UN_normal hf hR (Subgroup.inv_mem _ (URge_mono_R (Rp_subset R) (prC_mem hf hR g'))) hv
  · show g.1 * g'.1 = _
    rw [h, h']
    group

@[expose] def projHom (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) [CharP K 2] (hR : Closed R) : ↥(URge K R 1) →* Gp K where
  toFun := prC hf hR
  map_one' := by
    have := prC_eq hf hR (1 : ↥(URge K R 1)) (u := 1) (v := 1) (Subgroup.one_mem _)
      (Subgroup.one_mem _) (by simp)
    exact this
  map_mul' := prC_mul hf hR

end Split

end CFSG.RankThree.GF2n.Smith81.S81Z
