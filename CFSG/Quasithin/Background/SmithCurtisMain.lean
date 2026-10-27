module

public import CFSG.Quasithin.Background.SmithCurtisDatum

public section

namespace CFSG.Quasithin.SmithCurtis

open CoxeterSystem

namespace CurtisDatum

variable {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W]
  {cs : CoxeterSystem M W} {p : ℕ} (D : CurtisDatum G cs p)
  {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

theorem reduced_cons {s : B} {ω : List B} (hω : cs.IsReduced (s :: ω)) :
    cs.IsReduced ω ∧
      cs.length (cs.simple s * cs.wordProd ω) = cs.length (cs.wordProd ω) + 1 := by
  have hred : cs.IsReduced ω := by simpa using hω.drop 1
  exact ⟨hred, by rw [← cs.wordProd_cons, hω.eq, hred.eq, List.length_cons]⟩

theorem fix_nW_act {w : W} {s : B} (h : cs.length (cs.simple s * w) = cs.length w + 1) {m : V}
    (hm : m ∈ D.fixU ρ) {x : G} (hx : x ∈ D.X s) : ρ x (ρ (D.nW w) m) = ρ (D.nW w) m := by
  rw [act_mul]
  refine act_eq_of_mem ρ ?_ hm
  have e : (D.nW w)⁻¹ * (x * D.nW w) = (D.nW w)⁻¹ * x * D.nW w := by group
  rw [e]
  exact D.nW_conj w s h x hx

theorem act_H_mem_fixU {h : G} (hh : h ∈ D.H) {m : V} (hm : m ∈ D.fixU ρ) :
    ρ h m ∈ D.fixU ρ :=
  act_mem_fixSub ρ (D.H_normU' h hh) hm

theorem cover' (g : G) : ∃ q : G × W × G × G, q.1 ∈ D.L ∧ q.2.2.1 ∈ D.H ∧ q.2.2.2 ∈ D.U ∧
    g = q.1 * D.nW q.2.1 * (q.2.2.1 * q.2.2.2) := by
  obtain ⟨l, hl, w, h, hh, u, hu, e⟩ := D.cover g
  exact ⟨(l, w, h, u), hl, hh, hu, e⟩

@[expose] def coeffMap (f : Module.Dual k V) : V →ₗ[k] (G → k) where
  toFun v g := f (ρ g v)
  map_add' a b := funext fun g => by simp only [map_add, Pi.add_apply]
  map_smul' c a := funext fun g => by simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem coeffMap_apply (f : Module.Dual k V) (v : V) (g : G) :
    coeffMap ρ f v g = f (ρ g v) := rfl

theorem coeffMap_act (f : Module.Dual k V) (h : G) (v : V) (g : G) :
    coeffMap ρ f (ρ h v) g = coeffMap ρ f v (g * h) := by
  rw [coeffMap_apply, coeffMap_apply, act_mul]

theorem coeffMap_injective {ρ : Representation k G V} (hρ : IsSimpleRep ρ)
    {f : Module.Dual k V} {y : V} (hfy : f y = 1) : Function.Injective (coeffMap ρ f) := by
  rw [← LinearMap.ker_eq_bot]
  have hst : ∀ (h : G), ∀ v ∈ LinearMap.ker (coeffMap ρ f),
      ρ h v ∈ LinearMap.ker (coeffMap ρ f) := by
    intro h v hv
    rw [LinearMap.mem_ker] at hv ⊢
    funext g
    rw [coeffMap_act, hv]
    rfl
  rcases hρ.2 _ hst with hk | hk
  · exact hk
  · exfalso
    have hy : y ∈ LinearMap.ker (coeffMap ρ f) := hk ▸ Submodule.mem_top
    have h1 := congrFun (LinearMap.mem_ker.mp hy) 1
    rw [coeffMap_apply, map_one, Module.End.one_apply, hfy, Pi.zero_apply] at h1
    exact one_ne_zero h1

theorem range_coeffMap_le {V' : Type*} [AddCommGroup V'] [Module k V']
    {ρ : Representation k G V} {ρ' : Representation k G V'} (hρ : IsSimpleRep ρ)
    {f : Module.Dual k V} {f' : Module.Dual k V'} {y : V} {y' : V'} (hy0 : y ≠ 0)
    (hc : ∀ g, f (ρ g y) = f' (ρ' g y')) :
    LinearMap.range (coeffMap ρ f) ≤ LinearMap.range (coeffMap ρ' f') := by
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ orbitSpan ρ y := by
    rw [orbitSpan_eq_top hρ hy0]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, rfl⟩ := hv
    refine ⟨ρ' h y', funext fun g => ?_⟩
    rw [coeffMap_act, coeffMap_act, coeffMap_apply, coeffMap_apply, hc]
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

variable [Finite G]

theorem act_n_mem_augL (s : B) {z : V} (hz : z ∈ augSub ρ D.L)
    (hfix : ∀ x ∈ D.X s, ρ x z = z) : ρ (D.n s) z ∈ augSub ρ D.L := by
  refine act_mem_augSub_of_fixed ρ (D.L_le s) (D.Q_le s) (D.X_normQ s) (D.Y_normQ s)
    (D.H_normQ s) (D.n_normQ s) (D.H_normX s) (D.n_conjY s)
    (fun x hx => D.Y_le s (D.n_conjX s x hx)) (fun y hy hy1 => ?_) hz hfix
  obtain ⟨h, hh, a, ha, c, hc, e⟩ := D.bruhatY s y hy hy1
  exact ⟨a, ha, h, hh, c, hc, e⟩


theorem heckeT_mem_fixU (s : B) {m : V} (hm : m ∈ D.fixU ρ) : D.heckeT ρ s m ∈ D.fixU ρ := by
  unfold heckeT
  refine sumT_mem_fixSub ρ (D.U_eq s) (fun x hx v hv => ?_) (fun v hv => D.Us_le s
    (D.n_normUs' s v hv)) hm
  have e : x⁻¹ * v * x = x⁻¹ * v * x⁻¹⁻¹ := by rw [inv_inv]
  rw [e]
  exact D.X_normUs s _ (inv_mem hx) v hv

theorem heckeD_mem_fixU (s : B) {m : V} (hm : m ∈ D.fixU ρ) : D.heckeD ρ s m ∈ D.fixU ρ := by
  classical
  unfold heckeD
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun x hx => D.act_H_mem_fixU ρ (D.phi_mem s x x.2 fun h =>
    Finset.ne_of_mem_erase hx (OneMemClass.coe_eq_one.mp h)) hm

theorem heckeD'_mem_fixU (s : B) {m : V} (hm : m ∈ D.fixU ρ) : D.heckeD' ρ s m ∈ D.fixU ρ := by
  classical
  unfold heckeD'
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun x hx => D.act_H_mem_fixU ρ (D.psi_mem s x x.2 fun h =>
    Finset.ne_of_mem_erase hx (OneMemClass.coe_eq_one.mp h)) hm

theorem act_n_sub_mem_augL (s : B) {m : V} (hm : m ∈ D.fixU ρ) :
    ρ (D.n s) m - (D.heckeT ρ s m - D.heckeD ρ s m) ∈ augSub ρ D.L := by
  classical
  unfold heckeT heckeD
  rw [LinearMap.sum_apply]
  exact act_sub_sumT_mem_augSub ρ (D.phi s) (D.phi_spec s) hm

theorem heckeT_heckeT [Fact p.Prime] [CharP k p] (s : B) {m : V} (hm : m ∈ D.fixU ρ) :
    D.heckeT ρ s (D.heckeT ρ s m) = D.heckeT ρ s (D.heckeD' ρ s m) := by
  classical
  unfold heckeT heckeD'
  rw [LinearMap.sum_apply]
  exact sumT_sumT ρ (D.dvd_card_X s) (D.psi s) (D.psi_spec s)
    (fun x hx => D.nsq_conjX s hx) hm

open Classical in
@[expose] noncomputable def dScalar (χ : G → k) (s : B) : k :=
  have := Fintype.ofFinite (D.X s)
  ∑ x ∈ (Finset.univ : Finset (D.X s)).erase 1, χ (D.phi s x)

open Classical in
@[expose] noncomputable def d'Scalar (χ : G → k) (s : B) : k :=
  have := Fintype.ofFinite (D.X s)
  ∑ x ∈ (Finset.univ : Finset (D.X s)).erase 1, χ (D.psi s x)

theorem heckeD_weight (s : B) {m : V} {χ : G → k} (hχ : ∀ h ∈ D.H, ρ h m = χ h • m) :
    D.heckeD ρ s m = D.dScalar χ s • m := by
  classical
  unfold heckeD dScalar
  rw [LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun x hx => hχ _ (D.phi_mem s x x.2 fun h =>
    Finset.ne_of_mem_erase hx (OneMemClass.coe_eq_one.mp h))

theorem heckeD'_weight (s : B) {m : V} {χ : G → k} (hχ : ∀ h ∈ D.H, ρ h m = χ h • m) :
    D.heckeD' ρ s m = D.d'Scalar χ s • m := by
  classical
  unfold heckeD' d'Scalar
  rw [LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun x hx => hχ _ (D.psi_mem s x x.2 fun h =>
    Finset.ne_of_mem_erase hx (OneMemClass.coe_eq_one.mp h))

theorem heckeT_eq_hecke (s : B) {m : V} (hm : m ∈ D.fixU ρ) :
    D.heckeT ρ s m = hecke ρ D.U (D.n s) m := by
  classical
  have := Fintype.ofFinite (D.X s)
  rw [D.heckeT_apply ρ s m, hecke_apply]
  have himg : dcos D.U (D.n s) =
      (Finset.univ : Finset (D.X s)).image fun x : D.X s => (((x : G) * D.n s : G) : G ⧸ D.U) := by
    ext c
    rw [mem_dcos, Finset.mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨x, hx, v, hv, rfl⟩ := D.U_eq s u hu
      refine ⟨⟨x, hx⟩, Finset.mem_univ _, ?_⟩
      rw [QuotientGroup.eq]
      have e : ((x : G) * D.n s)⁻¹ * (x * v * D.n s) = (D.n s)⁻¹ * v * D.n s := by group
      rw [e]
      exact D.Us_le s (D.n_normUs' s v hv)
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, D.X_le s x.2, rfl⟩
  rw [himg, Finset.sum_image]
  · exact Finset.sum_congr rfl fun x _ => (out_act ρ hm _).symm
  · intro x _ x' _ hxx'
    rw [QuotientGroup.eq] at hxx'
    have e : ((x : G) * D.n s)⁻¹ * (x' * D.n s) = (D.n s)⁻¹ * ((x : G)⁻¹ * x') * D.n s := by
      group
    rw [e] at hxx'
    have hL : (D.n s)⁻¹ * ((x : G)⁻¹ * x') * D.n s ∈ D.L :=
      D.n_inv_conjX s (mul_mem (inv_mem x.2) x'.2)
    have h1 : (D.n s)⁻¹ * ((x : G)⁻¹ * x') * D.n s ∈ D.U ⊓ D.L := Subgroup.mem_inf.mpr ⟨hxx', hL⟩
    rw [D.U_inf_L, Subgroup.mem_bot] at h1
    have h2 : (x : G)⁻¹ * x' = 1 := by
      have e2 : (x : G)⁻¹ * x' = D.n s * ((D.n s)⁻¹ * ((x : G)⁻¹ * x') * D.n s) * (D.n s)⁻¹ := by
        group
      rw [e2, h1]
      group
    exact Subtype.ext (inv_mul_eq_one.mp h2)

theorem hecke_nW_simple_mul {w : W} {s : B} (h : cs.length (cs.simple s * w) = cs.length w + 1)
    {m : V} (hm : m ∈ D.fixU ρ) :
    hecke ρ D.U (D.n s) (hecke ρ D.U (D.nW w) m) = hecke ρ D.U (D.nW (cs.simple s * w)) m := by
  have hdeg := D.heckeDeg_mul w s h
  rw [D.nW_simple_mul w s h] at hdeg ⊢
  refine hecke_hecke ρ (fun u hu => ?_) hdeg hm
  obtain ⟨x, hx, v, hv, rfl⟩ := D.U_eq s u hu
  refine ⟨D.n s * (x * v * x⁻¹) * (D.n s)⁻¹, D.Us_le s (D.n_normUs s _ (D.X_normUs s x hx v hv)),
    (D.nW w)⁻¹ * x * D.nW w, D.nW_conj w s h x hx, by group⟩

theorem hecke_weight {g : G} (hg : ∀ h ∈ D.H, g⁻¹ * h * g ∈ D.H) {m : V}
    (hm : m ∈ D.fixU ρ) {χ : G → k} (hχ : ∀ h ∈ D.H, ρ h m = χ h • m) :
    ∀ h ∈ D.H, ρ h (hecke ρ D.U g m) = χ (g⁻¹ * h * g) • hecke ρ D.U g m := by
  intro h hh
  rw [← hecke_mul_left ρ (D.H_normU h hh) (D.H_normU' h hh) g hm]
  have e : h * g = g * (g⁻¹ * h * g) := by group
  rw [e, hecke_mul_right ρ (D.H_normU _ (hg h hh)) (D.H_normU' _ (hg h hh)) g hm,
    hχ _ (hg h hh), map_smul]

theorem fixU_ne_bot [Fact p.Prime] [CharP k p] [Nontrivial V] : D.fixU ρ ≠ ⊥ := by
  obtain ⟨v, hv, hfix⟩ := exists_fixed_ne ρ D.isPGroup_U
  exact (Submodule.ne_bot_iff _).mpr ⟨v, hfix, hv⟩

theorem nW_act_mem_augL {z : V} (hz : z ∈ D.fixU ρ) (hza : z ∈ augSub ρ D.L) (w : W) :
    ρ (D.nW w) z ∈ augSub ρ D.L := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  induction ω with
  | nil => rw [cs.wordProd_nil, D.nW_one, map_one, Module.End.one_apply]; exact hza
  | cons s ω ih =>
    obtain ⟨hred, hlen⟩ := reduced_cons hω
    rw [cs.wordProd_cons, D.nW_simple_mul _ _ hlen, ← act_mul]
    exact D.act_n_mem_augL ρ s (ih hred) fun x hx => D.fix_nW_act ρ hlen hz hx

theorem fixU_inf_augL [Fact p.Prime] [CharP k p] {ρ : Representation k G V}
    (hρ : IsSimpleRep ρ) {z : V} (hz : z ∈ D.fixU ρ) (hza : z ∈ augSub ρ D.L) : z = 0 := by
  by_contra hne
  have := hρ.1
  apply augSub_ne_top ρ D.isPGroup_L
  rw [eq_top_iff, ← orbitSpan_eq_top hρ hne, orbitSpan, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  obtain ⟨l, hl, w, h, hh, u, hu, rfl⟩ := D.cover g
  show ρ (l * D.nW w * (h * u)) z ∈ augSub ρ D.L
  rw [← act_mul, ← act_mul, ← act_mul, hz u hu]
  exact act_mem_augSub_self ρ hl (D.nW_act_mem_augL ρ (D.act_H_mem_fixU ρ hh hz)
    (act_mem_augSub ρ (D.H_normL h hh) hza) w)

@[expose] noncomputable def coinvOp (ω : List B) : V →ₗ[k] V :=
  (ω.map fun s => D.heckeT ρ s - D.heckeD ρ s).prod

theorem coinvOp_nil : D.coinvOp ρ [] = 1 := rfl

theorem coinvOp_cons (s : B) (ω : List B) (v : V) :
    D.coinvOp ρ (s :: ω) v = D.heckeT ρ s (D.coinvOp ρ ω v) - D.heckeD ρ s (D.coinvOp ρ ω v) := by
  rw [coinvOp, List.map_cons, List.prod_cons, Module.End.mul_apply]
  rfl

theorem coinvOp_mem_fixU (ω : List B) {m : V} (hm : m ∈ D.fixU ρ) :
    D.coinvOp ρ ω m ∈ D.fixU ρ := by
  induction ω with
  | nil => exact hm
  | cons s ω ih =>
    rw [coinvOp_cons]
    exact sub_mem (D.heckeT_mem_fixU ρ s ih) (D.heckeD_mem_fixU ρ s ih)

theorem coinv_formula {ω : List B} (hω : cs.IsReduced ω) {m : V} (hm : m ∈ D.fixU ρ) :
    ρ (D.nW (cs.wordProd ω)) m - D.coinvOp ρ ω m ∈ augSub ρ D.L := by
  induction ω with
  | nil =>
    rw [cs.wordProd_nil, D.nW_one, map_one, coinvOp_nil, sub_self]
    exact zero_mem _
  | cons s ω ih =>
    obtain ⟨hred, hlen⟩ := reduced_cons hω
    set m' := D.coinvOp ρ ω m
    have hm' : m' ∈ D.fixU ρ := D.coinvOp_mem_fixU ρ ω hm
    have hfix : ∀ x ∈ D.X s, ρ x (ρ (D.nW (cs.wordProd ω)) m - m') =
        ρ (D.nW (cs.wordProd ω)) m - m' := by
      intro x hx
      rw [map_sub, D.fix_nW_act ρ hlen hm hx, hm' x (D.X_le s hx)]
    have h1 := D.act_n_mem_augL ρ s (ih hred) hfix
    have h2 := D.act_n_sub_mem_augL ρ s hm'
    rw [cs.wordProd_cons, D.nW_simple_mul _ _ hlen, coinvOp_cons]
    have e : ρ (D.n s * D.nW (cs.wordProd ω)) m - (D.heckeT ρ s m' - D.heckeD ρ s m') =
        ρ (D.n s) (ρ (D.nW (cs.wordProd ω)) m - m') +
          (ρ (D.n s) m' - (D.heckeT ρ s m' - D.heckeD ρ s m')) := by
      rw [map_sub, ← act_mul]
      abel
    rw [e]
    exact add_mem h1 h2

@[expose] def IsCurtisType (y : V) (χ : G → k) (μ : B → k) : Prop :=
  y ∈ D.fixU ρ ∧ y ≠ 0 ∧ (∀ h ∈ D.H, ρ h y = χ h • y) ∧ ∀ s, D.heckeT ρ s y = μ s • y

@[expose] noncomputable def coinvScalar (χ : G → k) (μ : B → k) (ω : List B) : k :=
  (ω.map fun s => μ s - D.dScalar χ s).prod

theorem coinvOp_eigen {y : V} {χ : G → k} {μ : B → k} (hχ : ∀ h ∈ D.H, ρ h y = χ h • y)
    (hμ : ∀ s, D.heckeT ρ s y = μ s • y) (ω : List B) :
    D.coinvOp ρ ω y = D.coinvScalar χ μ ω • y := by
  induction ω with
  | nil => rw [coinvOp_nil, coinvScalar, List.map_nil, List.prod_nil, one_smul]; rfl
  | cons s ω ih =>
    rw [coinvOp_cons, ih, map_smul, map_smul, hμ s, D.heckeD_weight ρ s hχ, smul_smul, smul_smul,
      ← sub_smul]
    congr 1
    simp only [coinvScalar, List.map_cons, List.prod_cons]
    ring

@[expose] noncomputable def sph (χ : G → k) (μ : B → k) (g : G) : k :=
  χ (D.cover' g).choose.2.2.1 *
    D.coinvScalar χ μ (cs.exists_isReduced (D.cover' g).choose.2.1).choose

theorem act_sub_sph_mem_augL {y : V} {χ : G → k} {μ : B → k} (hy : y ∈ D.fixU ρ)
    (hχ : ∀ h ∈ D.H, ρ h y = χ h • y) (hμ : ∀ s, D.heckeT ρ s y = μ s • y) (g : G) :
    ρ g y - D.sph χ μ g • y ∈ augSub ρ D.L := by
  obtain ⟨hl, hh, hu, e⟩ := (D.cover' g).choose_spec
  set q := (D.cover' g).choose
  obtain ⟨hred, hw⟩ := (cs.exists_isReduced q.2.1).choose_spec
  set ω := (cs.exists_isReduced q.2.1).choose
  have h1 : ρ g y = χ q.2.2.1 • ρ q.1 (ρ (D.nW (cs.wordProd ω)) y) := by
    conv_lhs => rw [e, hw]
    rw [← act_mul, ← act_mul, ← act_mul, hy _ hu, hχ _ hh, map_smul, map_smul]
  have h2 := D.coinv_formula ρ hred hy
  rw [D.coinvOp_eigen ρ hχ hμ] at h2
  have h3 : ρ q.1 (ρ (D.nW (cs.wordProd ω)) y) - D.coinvScalar χ μ ω • y ∈ augSub ρ D.L :=
    act_sub_mem_augSub ρ hl _ h2
  have e2 : ρ g y - D.sph χ μ g • y =
      χ q.2.2.1 • (ρ q.1 (ρ (D.nW (cs.wordProd ω)) y) - D.coinvScalar χ μ ω • y) := by
    rw [h1, sph, smul_sub, smul_smul]
  rw [e2]
  exact Submodule.smul_mem _ _ h3

theorem fixU_eq_smul [Fact p.Prime] [CharP k p] {ρ : Representation k G V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ)
    {x : V} (hx : x ∈ D.fixU ρ) : ∃ c : k, x = c • y := by
  obtain ⟨hy, hy0, hχ, hμ⟩ := ht
  have key : ∀ v ∈ orbitSpan ρ y, ∃ c : k, v - c • y ∈ augSub ρ D.L := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g, rfl⟩ := hv
      exact ⟨D.sph χ μ g, D.act_sub_sph_mem_augL ρ hy hχ hμ g⟩
    | zero => exact ⟨0, by rw [zero_smul, sub_zero]; exact zero_mem _⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨c', hc'⟩ := hb
      refine ⟨c + c', ?_⟩
      have e : a + b - (c + c') • y = (a - c • y) + (b - c' • y) := by rw [add_smul]; abel
      rw [e]
      exact add_mem hc hc'
    | smul a v _ hv =>
      obtain ⟨c, hc⟩ := hv
      refine ⟨a * c, ?_⟩
      rw [mul_smul, ← smul_sub]
      exact Submodule.smul_mem _ a hc
  obtain ⟨c, hc⟩ := key x (by rw [orbitSpan_eq_top hρ hy0]; exact Submodule.mem_top)
  refine ⟨c, ?_⟩
  have h0 := D.fixU_inf_augL hρ (sub_mem hx (Submodule.smul_mem _ c hy)) hc
  rwa [sub_eq_zero] at h0

theorem fixU_eq_span [Fact p.Prime] [CharP k p] {ρ : Representation k G V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) :
    D.fixU ρ = Submodule.span k {y} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨c, rfl⟩ := D.fixU_eq_smul hρ ht hx
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ht.1

variable {D} in
theorem IsCurtisType.unique [Fact p.Prime] [CharP k p] {ρ : Representation k G V}
    (hρ : IsSimpleRep ρ) {y y' : V} {χ χ' : G → k} {μ μ' : B → k}
    (ht : D.IsCurtisType ρ y χ μ) (ht' : D.IsCurtisType ρ y' χ' μ') :
    (∀ h ∈ D.H, χ h = χ' h) ∧ μ = μ' := by
  obtain ⟨c, hc⟩ := D.fixU_eq_smul hρ ht ht'.1
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ht'.2.1 (by rw [hc, zero_smul])
  have hy0 := ht.2.1
  refine ⟨fun h hh => ?_, funext fun s => ?_⟩
  · have e := ht'.2.2.1 h hh
    rw [hc, map_smul, ht.2.2.1 h hh, smul_smul, smul_smul, mul_comm] at e
    exact mul_right_cancel₀ hc0 (smul_left_injective k hy0 e)
  · have e := ht'.2.2.2 s
    rw [hc, map_smul, ht.2.2.2 s, smul_smul, smul_smul, mul_comm] at e
    exact mul_right_cancel₀ hc0 (smul_left_injective k hy0 e)

variable {D ρ} in
theorem IsCurtisType.chi_mul {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ)
    {h h' : G} (hh : h ∈ D.H) (hh' : h' ∈ D.H) : χ (h * h') = χ h * χ h' := by
  have e := ht.2.2.1 _ (mul_mem hh hh')
  rw [map_mul, Module.End.mul_apply, ht.2.2.1 h' hh', map_smul, ht.2.2.1 h hh, smul_smul,
    mul_comm] at e
  exact (smul_left_injective k ht.2.1 e).symm

variable {D ρ} in
theorem IsCurtisType.chi_one {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) :
    χ 1 = 1 := by
  have e := ht.2.2.1 1 (one_mem _)
  rw [map_one, Module.End.one_apply] at e
  exact (smul_left_injective k ht.2.1 (e.symm.trans (one_smul k y).symm) : _)

variable {D ρ} in
@[expose] noncomputable def IsCurtisType.chiHom {y : V} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType ρ y χ μ) : D.H →* k where
  toFun h := χ h
  map_one' := ht.chi_one
  map_mul' h h' := ht.chi_mul h.2 h'.2

theorem IsCurtisType.chiHom_apply {y : V} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType ρ y χ μ) (h : D.H) : ht.chiHom h = χ h := rfl

variable {D ρ} in
theorem IsCurtisType.mu_eq [Fact p.Prime] [CharP k p] {y : V} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType ρ y χ μ) (s : B) : μ s = 0 ∨ μ s = D.d'Scalar χ s := by
  have h := D.heckeT_heckeT ρ s ht.1
  rw [ht.2.2.2 s, map_smul, ht.2.2.2 s, D.heckeD'_weight ρ s ht.2.2.1, map_smul, ht.2.2.2 s,
    smul_smul, smul_smul] at h
  have h2 : μ s * (μ s - D.d'Scalar χ s) = 0 := by
    have h3 : μ s * μ s = D.d'Scalar χ s * μ s := smul_left_injective k ht.2.1 h
    rw [mul_sub, h3, mul_comm, sub_self]
  rcases mul_eq_zero.mp h2 with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem exists_common_eigen [Finite W] [Fact p.Prime] [CharP k p] (hsplit : SplitOver k D.H)
    [Nontrivial V] : ∃ y : V, ∃ χ : G → k, ∃ μ : B → k, D.IsCurtisType ρ y χ μ := by
  classical
  set P : W → Prop := fun w => ∃ x ∈ D.fixU ρ, (∃ χ : G → k, ∀ h ∈ D.H, ρ h x = χ h • x) ∧
    hecke ρ D.U (D.nW w) x ≠ 0
  have hP1 : P 1 := by
    obtain ⟨y, hy, hy0, χ, hχ⟩ := exists_weight_vector ρ D.H_comm hsplit (D.fixU_ne_bot ρ)
      fun h hh v hv => D.act_H_mem_fixU ρ hh hv
    exact ⟨y, hy, ⟨χ, hχ⟩, by rw [D.nW_one, hecke_one ρ hy]; exact hy0⟩
  have := Fintype.ofFinite W
  obtain ⟨w, hw, hmax⟩ := (Finset.univ.filter P).exists_max_image cs.length
    ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP1⟩⟩
  obtain ⟨x, hx, ⟨χ, hχ⟩, hne⟩ := (Finset.mem_filter.mp hw).2
  have hyU : hecke ρ D.U (D.nW w) x ∈ D.fixU ρ := hecke_mem_fixSub ρ _ hx
  have hmu : ∀ s, ∃ μ : k, D.heckeT ρ s (hecke ρ D.U (D.nW w) x) =
      μ • hecke ρ D.U (D.nW w) x := by
    intro s
    rcases cs.length_simple_mul w s with hup | hdown
    · refine ⟨0, ?_⟩
      rw [zero_smul, D.heckeT_eq_hecke ρ s hyU, D.hecke_nW_simple_mul ρ hup hx]
      by_contra h
      have := hmax (cs.simple s * w) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, ⟨χ, hχ⟩, h⟩)
      omega
    · have hup' : cs.length (cs.simple s * (cs.simple s * w)) =
          cs.length (cs.simple s * w) + 1 := by
        rw [cs.simple_mul_simple_cancel_left]
        omega
      have hy'' : hecke ρ D.U (D.nW (cs.simple s * w)) x ∈ D.fixU ρ := hecke_mem_fixSub ρ _ hx
      have hyeq : hecke ρ D.U (D.nW w) x =
          D.heckeT ρ s (hecke ρ D.U (D.nW (cs.simple s * w)) x) := by
        rw [D.heckeT_eq_hecke ρ s hy'', D.hecke_nW_simple_mul ρ hup' hx,
          cs.simple_mul_simple_cancel_left]
      have hχ'' := D.hecke_weight ρ (fun h hh => D.nW_normH (cs.simple s * w) hh) hx hχ
      refine ⟨D.d'Scalar (fun h => χ ((D.nW (cs.simple s * w))⁻¹ * h *
        D.nW (cs.simple s * w))) s, ?_⟩
      rw [hyeq, D.heckeT_heckeT ρ s hy'', D.heckeD'_weight ρ s hχ'', map_smul]
  refine ⟨hecke ρ D.U (D.nW w) x, fun h => χ ((D.nW w)⁻¹ * h * D.nW w),
    fun s => (hmu s).choose, hyU, hne, D.hecke_weight ρ (fun h hh => D.nW_normH w hh) hx hχ,
    fun s => (hmu s).choose_spec⟩

theorem exists_isCurtisType [Finite W] [Fact p.Prime] [CharP k p] (hsplit : SplitOver k D.H)
    {ρ : Representation k G V} (hρ : IsSimpleRep ρ) :
    ∃ y : V, ∃ χ : G → k, ∃ μ : B → k, D.IsCurtisType ρ y χ μ := by
  have := hρ.1
  exact D.exists_common_eigen ρ hsplit

theorem finrank_fixU [Finite W] [Fact p.Prime] [CharP k p] (hsplit : SplitOver k D.H)
    {ρ : Representation k G V} (hρ : IsSimpleRep ρ) : Module.finrank k (D.fixU ρ) = 1 := by
  obtain ⟨y, χ, μ, ht⟩ := D.exists_isCurtisType hsplit hρ
  rw [D.fixU_eq_span hρ ht, finrank_span_singleton ht.2.1]

theorem exists_form [Fact p.Prime] [CharP k p] {ρ : Representation k G V} (hρ : IsSimpleRep ρ)
    {y : V} (hy : y ∈ D.fixU ρ) (hy0 : y ≠ 0) :
    ∃ f : Module.Dual k V, (∀ z ∈ augSub ρ D.L, f z = 0) ∧ f y = 1 := by
  have hyn : y ∉ augSub ρ D.L := fun h => hy0 (D.fixU_inf_augL hρ hy h)
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyn inferInstance
  refine ⟨(f y)⁻¹ • f, fun z hz => ?_, by
    rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]⟩
  have h := Submodule.mem_map_of_mem (f := f) hz
  rw [hmap] at h
  rw [LinearMap.smul_apply, (Submodule.mem_bot _).mp h, smul_zero]

theorem form_act {f : Module.Dual k V} (hf : ∀ z ∈ augSub ρ D.L, f z = 0) {y : V}
    {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) (hfy : f y = 1) (g : G) :
    f (ρ g y) = D.sph χ μ g := by
  have h := hf _ (D.act_sub_sph_mem_augL ρ ht.1 ht.2.2.1 ht.2.2.2 g)
  rwa [map_sub, map_smul, hfy, smul_eq_mul, mul_one, sub_eq_zero] at h

theorem iso_of_isCurtisType [Fact p.Prime] [CharP k p] {V' : Type*} [AddCommGroup V']
    [Module k V'] {ρ : Representation k G V} {ρ' : Representation k G V'} (hρ : IsSimpleRep ρ)
    (hρ' : IsSimpleRep ρ') {y : V} {y' : V'} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType ρ y χ μ) (ht' : D.IsCurtisType ρ' y' χ μ) :
    ∃ β : V ≃ₗ[k] V', ∀ (g : G) (v : V), β (ρ g v) = ρ' g (β v) := by
  obtain ⟨f, hf, hfy⟩ := D.exists_form hρ ht.1 ht.2.1
  obtain ⟨f', hf', hfy'⟩ := D.exists_form hρ' ht'.1 ht'.2.1
  have hc : ∀ g, f (ρ g y) = f' (ρ' g y') := fun g => by
    rw [D.form_act ρ hf ht hfy, D.form_act ρ' hf' ht' hfy']
  have hi := coeffMap_injective hρ hfy
  have hi' := coeffMap_injective hρ' hfy'
  have hR : LinearMap.range (coeffMap ρ f) = LinearMap.range (coeffMap ρ' f') :=
    le_antisymm (range_coeffMap_le hρ ht.2.1 hc)
      (range_coeffMap_le hρ' ht'.2.1 fun g => (hc g).symm)
  let β : V ≃ₗ[k] V' := (LinearEquiv.ofInjective _ hi).trans
    ((LinearEquiv.ofEq _ _ hR).trans (LinearEquiv.ofInjective _ hi').symm)
  have hβ : ∀ v, coeffMap ρ' f' (β v) = coeffMap ρ f v := fun v => by
    have h1 : LinearEquiv.ofInjective _ hi' (β v) =
        LinearEquiv.ofEq _ _ hR (LinearEquiv.ofInjective _ hi v) :=
      LinearEquiv.apply_symm_apply _ _
    have h2 := congrArg Subtype.val h1
    rwa [LinearEquiv.ofInjective_apply, LinearEquiv.coe_ofEq_apply,
      LinearEquiv.ofInjective_apply] at h2
  refine ⟨β, fun g v => hi' ?_⟩
  rw [hβ]
  funext h
  rw [coeffMap_act, coeffMap_act, hβ]

theorem isSimpleRep_of_fixU [Fact p.Prime] [CharP k p] [Nontrivial V] {y : V}
    (hfix : ∀ x ∈ D.fixU ρ, ∃ c : k, x = c • y) (hgen : orbitSpan ρ y = ⊤) : IsSimpleRep ρ := by
  refine ⟨inferInstance, fun S hS => ?_⟩
  by_cases hne : S = ⊥
  · exact Or.inl hne
  · right
    obtain ⟨x, hxS, hx0, hx⟩ := exists_fixed_mem ρ D.isPGroup_U hS hne
    obtain ⟨c, rfl⟩ := hfix x hx
    have hc : c ≠ 0 := by rintro rfl; exact hx0 (zero_smul k y)
    have hyS : y ∈ S := by
      have := Submodule.smul_mem S c⁻¹ hxS
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    rw [eq_top_iff, ← hgen, orbitSpan, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hS g y hyS

end CurtisDatum

end CFSG.Quasithin.SmithCurtis
