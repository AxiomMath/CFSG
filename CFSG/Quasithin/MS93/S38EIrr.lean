module

public import CFSG.Quasithin.MS93.S38EUniq
public import CFSG.Quasithin.MS93.S38EY

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

variable {U₀ : Type*} [Group U₀]

structure EndSetup (V G₀ Lt Tb Qa E : Subgroup U₀) (e : ℕ) : Prop where
  finite : Finite ↥G₀
  v_le : V ≤ G₀
  nV : G₀ ≤ Subgroup.normalizer (V : Set U₀)
  invol : V = Subgroup.closure {v | v ∈ V ∧ v ^ 2 = 1}
  cls2 : ⁅V, V⁆ ≤ Subgroup.centralizer (V : Set U₀)
  lt_le : Lt ≤ G₀
  nLt : G₀ ≤ Subgroup.normalizer (Lt : Set U₀)
  perf : ⁅Lt, Lt⁆ = Lt
  tb_le : Tb ≤ G₀
  sup : G₀ = Lt ⊔ Tb
  ltC : Lt ≤ Subgroup.centralizer ((⁅V, V⁆ : Subgroup U₀) : Set U₀)
  key : ¬ ⁅⁅V, Lt⁆, V⁆ ≤ ⁅⁅V, V⁆, Tb⁆
  e_le : E ≤ G₀
  e_ab : IsElemAbelian 2 E
  ff : ∃ R : Subgroup U₀, R ≤ V ∧ R.relIndex V ≤ e ∧
    ⁅R, E⁆ ≤ Subgroup.centralizer (V : Set U₀)
  e_eq : Qa.relIndex E = e
  qa_le : Qa ≤ G₀
  nQa : G₀ ≤ Subgroup.normalizer (Qa : Set U₀)
  qa2 : IsPGroup 2 ↥Qa
  faith : ∀ x ∈ E, x ∉ Qa → Lt ≤ Subgroup.closure {y | ∃ k ∈ G₀, k * x * k⁻¹ = y}

theorem le_normalizer_comm_of {N A B : Subgroup U₀} (hA : N ≤ Subgroup.normalizer (A : Set U₀))
    (hB : N ≤ Subgroup.normalizer (B : Set U₀)) :
    N ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup U₀) : Set U₀) := by
  have key : ∀ g ∈ N, ∀ x ∈ ⁅A, B⁆, g * x * g⁻¹ ∈ ⁅A, B⁆ := by
    intro g hg
    have hle : ⁅A, B⁆ ≤ ⁅A, B⁆.comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      show (MulAut.conj g) ⁅a, b⁆ ∈ ⁅A, B⁆
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 (hA hg) a).1 ha)
        ((Subgroup.mem_normalizer_iff.1 (hB hg) b).1 hb)
    intro x hx
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem le_relIndex_kerRel_aux {G₀ Lt Qa E : Subgroup U₀} [Finite ↥G₀] {Y : Type*} [CommGroup Y]
    (ρ : ↥G₀ →* MulAut Y) (hE : E ≤ G₀)
    (faith : ∀ x ∈ E, x ∉ Qa → Lt ≤ Subgroup.closure {y | ∃ k ∈ G₀, k * x * k⁻¹ = y})
    (W N : Subgroup Y) (hWs : Stab ρ.range W) (hNs : Stab ρ.range N)
    (hnc : NonCent ((Lt.subgroupOf G₀).map ρ) W N) :
    Qa.relIndex E ≤ (kerRel ((E.subgroupOf G₀).map ρ) W N
      (hNs.mono (Subgroup.map_le_range _ _))).relIndex ((E.subgroupOf G₀).map ρ) := by
  have mem_Kr : ∀ g, g ∈ (kerRel ρ.range W N hNs).comap ρ ↔ ∀ w ∈ W, ρ g w * w⁻¹ ∈ N :=
    fun g => ⟨fun h => h.2, fun h => ⟨⟨g, rfl⟩, h⟩⟩
  have hKr_conj : ∀ g : ↥G₀, ∀ k ∈ (kerRel ρ.range W N hNs).comap ρ,
      g * k * g⁻¹ ∈ (kerRel ρ.range W N hNs).comap ρ := by
    intro g k hk
    rw [mem_Kr] at hk ⊢
    intro w hw
    have hw' : ρ g⁻¹ w ∈ W := hWs _ ⟨g⁻¹, rfl⟩ w hw
    have h2 := hNs _ ⟨g, rfl⟩ _ (hk _ hw')
    have e : ρ (g * k * g⁻¹) w * w⁻¹ = ρ g (ρ k (ρ g⁻¹ w) * (ρ g⁻¹ w)⁻¹) := by
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, map_mul, map_inv, map_inv,
        MulAut.apply_inv_self]
    rw [e]
    exact h2
  have hnot : ∀ x (hx : x ∈ E), x ∉ Qa →
      (⟨x, hE hx⟩ : ↥G₀) ∉ (kerRel ρ.range W N hNs).comap ρ := by
    intro x hx hxQ hxK
    have hcl : Subgroup.closure {y | ∃ k ∈ G₀, k * x * k⁻¹ = y} ≤
        ((kerRel ρ.range W N hNs).comap ρ).map G₀.subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩ * ⟨x, hE hx⟩ * ⟨k, hk⟩⁻¹, hKr_conj _ _ hxK, rfl⟩
    obtain ⟨k, hkK, w, hw, hkw⟩ := hnc
    obtain ⟨l, hl, rfl⟩ := hkK
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl
    obtain ⟨l', hl', hll'⟩ := hcl (faith x hx hxQ hl)
    have : l' = l := Subtype.ext hll'
    rw [this, SetLike.mem_coe, mem_Kr] at hl'
    exact hkw (hl' w hw)
  set H := (kerRel ((E.subgroupOf G₀).map ρ) W N (hNs.mono (Subgroup.map_le_range _ _))).comap ρ
    with hH
  have h1 : H.relIndex (E.subgroupOf G₀) = (kerRel ((E.subgroupOf G₀).map ρ) W N
      (hNs.mono (Subgroup.map_le_range _ _))).relIndex ((E.subgroupOf G₀).map ρ) :=
    Subgroup.relIndex_comap _ _ _
  have h2 : H ⊓ E.subgroupOf G₀ ≤ Qa.subgroupOf G₀ := by
    intro g hg
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf] at hg
    obtain ⟨hgH, hgE⟩ := hg
    rw [Subgroup.mem_subgroupOf]
    by_contra hgQ
    apply hnot g hgE hgQ
    exact (mem_Kr _).mpr hgH.2
  have h4 : (H ⊓ E.subgroupOf G₀).relIndex (E.subgroupOf G₀) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  calc Qa.relIndex E = (Qa.subgroupOf G₀).relIndex (E.subgroupOf G₀) :=
        (Subgroup.relIndex_subgroupOf hE).symm
    _ ≤ (H ⊓ E.subgroupOf G₀).relIndex (E.subgroupOf G₀) := Subgroup.relIndex_le_of_le_left h2 h4
    _ = H.relIndex (E.subgroupOf G₀) := Subgroup.inf_relIndex_right _ _
    _ = _ := h1

namespace EndSetup

variable {V G₀ Lt Tb Qa E : Subgroup U₀} {e : ℕ}

theorem commV_le (hS : EndSetup V G₀ Lt Tb Qa E e) : ⁅V, Lt⁆ ≤ V :=
  Subgroup.le_normalizer_iff_commutator_le_left.1 (hS.lt_le.trans hS.nV)

theorem comm_le_self (V : Subgroup U₀) : ⁅V, V⁆ ≤ V :=
  Subgroup.le_normalizer_iff_commutator_le_left.1 Subgroup.le_normalizer

theorem le_normalizer_comm (hS : EndSetup V G₀ Lt Tb Qa E e) :
    G₀ ≤ Subgroup.normalizer ((⁅V, V⁆ : Subgroup U₀) : Set U₀) :=
  le_normalizer_comm_of hS.nV hS.nV

theorem c1_le (hS : EndSetup V G₀ Lt Tb Qa E e) : ⁅⁅V, V⁆, Tb⁆ ≤ ⁅V, V⁆ :=
  Subgroup.le_normalizer_iff_commutator_le_left.1 (hS.tb_le.trans hS.le_normalizer_comm)

theorem comm_comm_le (hS : EndSetup V G₀ Lt Tb Qa E e) : ⁅⁅V, Lt⁆, V⁆ ≤ ⁅V, V⁆ :=
  Subgroup.commutator_mono hS.commV_le le_rfl

theorem comm_mul_comm (hS : EndSetup V G₀ Lt Tb Qa E e) {a b : U₀} (ha : a ∈ ⁅V, V⁆)
    (hb : b ∈ ⁅V, V⁆) : a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp (hS.cls2 hb) a (comm_le_self V ha)

theorem exists_lam (hS : EndSetup V G₀ Lt Tb Qa E e) :
    ∃ lam : ↥⁅V, V⁆ →* ℂˣ, (∀ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, V⁆, Tb⁆ → lam c = 1) ∧
      ∃ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, Lt⁆, V⁆ ∧ lam c ≠ 1 := by
  have : Finite ↥G₀ := hS.finite
  have : Finite ↥⁅V, V⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective ((comm_le_self V).trans hS.v_le))
  let _ : CommGroup ↥⁅V, V⁆ :=
    { (inferInstance : Group ↥⁅V, V⁆) with
      mul_comm := fun a b => Subtype.ext (hS.comm_mul_comm a.2 b.2) }
  obtain ⟨c₀, hc₀, hc₀C⟩ := Set.not_subset.mp hS.key
  set N := (⁅⁅V, V⁆, Tb⁆ : Subgroup U₀).subgroupOf ⁅V, V⁆ with hN
  have hne : (QuotientGroup.mk (⟨c₀, hS.comm_comm_le hc₀⟩ : ↥⁅V, V⁆) : ↥⁅V, V⁆ ⧸ N) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    exact hc₀C
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity _ ℂ hne
  refine ⟨φ.comp (QuotientGroup.mk' N), fun c hc => ?_, ⟨c₀, hS.comm_comm_le hc₀⟩, hc₀, hφ⟩
  have : (QuotientGroup.mk' N c : ↥⁅V, V⁆ ⧸ N) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    exact hc
  rw [MonoidHom.comp_apply, this, map_one]

open Classical in
@[expose] noncomputable def lamExt (lam : ↥⁅V, V⁆ →* ℂˣ) (x : U₀) : ℂˣ :=
  if h : x ∈ ⁅V, V⁆ then lam ⟨x, h⟩ else 1

theorem lamExt_of_mem (lam : ↥⁅V, V⁆ →* ℂˣ) {x : U₀} (hx : x ∈ ⁅V, V⁆) :
    lamExt lam x = lam ⟨x, hx⟩ := dite_eq_left hx

theorem lamExt_mul (lam : ↥⁅V, V⁆ →* ℂˣ) {x y : U₀} (hx : x ∈ ⁅V, V⁆) (hy : y ∈ ⁅V, V⁆) :
    lamExt lam (x * y) = lamExt lam x * lamExt lam y := by
  rw [lamExt_of_mem lam (mul_mem hx hy), lamExt_of_mem lam hx, lamExt_of_mem lam hy, ← map_mul]
  rfl

theorem vPair_eq_lamExt (lam : ↥⁅V, V⁆ →* ℂˣ) (v w : ↥V) :
    vPair lam v w = lamExt lam ⁅(v : U₀), (w : U₀)⁆ := by
  rw [lamExt_of_mem lam (commutator_mem_vv v w)]
  rfl

variable (hS : EndSetup V G₀ Lt Tb Qa E e) (lam : ↥⁅V, V⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, V⁆, Tb⁆ → lam c = 1)

include hS hlam1 in
theorem lam_conj {g : U₀} (hg : g ∈ G₀) {c : U₀} (hc : c ∈ ⁅V, V⁆) :
    lamExt lam (g * c * g⁻¹) = lamExt lam c := by
  let S : Subgroup U₀ :=
    { carrier := {g | g ∈ Subgroup.normalizer ((⁅V, V⁆ : Subgroup U₀) : Set U₀) ∧
        ∀ c ∈ ⁅V, V⁆, lamExt lam (g * c * g⁻¹) = lamExt lam c}
      one_mem' := ⟨one_mem _, fun c _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, fun c hc => ?_⟩
        have hbc : b * c * b⁻¹ ∈ ⁅V, V⁆ := (Subgroup.mem_normalizer_iff.mp hb c).mp hc
        have e : a * b * c * (a * b)⁻¹ = a * (b * c * b⁻¹) * a⁻¹ := by group
        rw [e, ha' _ hbc, hb' c hc]
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, fun c hc => ?_⟩
        have hac : a⁻¹ * c * a⁻¹⁻¹ ∈ ⁅V, V⁆ :=
          (Subgroup.mem_normalizer_iff.mp (inv_mem ha) c).mp hc
        have h1 := ha' _ hac
        have e : a * (a⁻¹ * c * a⁻¹⁻¹) * a⁻¹ = c := by group
        rw [e] at h1
        exact h1.symm }
  have hLt : Lt ≤ S := fun l hl => ⟨(hS.lt_le.trans hS.le_normalizer_comm) hl, fun c hc => by
    have := Subgroup.mem_centralizer_iff.mp (hS.ltC hl) c hc
    rw [← this, mul_inv_cancel_right]⟩
  have hTb : Tb ≤ S := fun t ht => ⟨(hS.tb_le.trans hS.le_normalizer_comm) ht, fun c hc => by
    have htc : t * c * t⁻¹ * c⁻¹ ∈ ⁅⁅V, V⁆, Tb⁆ := by
      rw [Subgroup.commutator_comm]
      have := Subgroup.commutator_mem_commutator ht hc
      rwa [commutatorElement_def] at this
    have e : t * c * t⁻¹ = (t * c * t⁻¹ * c⁻¹) * c := by group
    rw [e, lamExt_mul lam (hS.c1_le htc) hc, lamExt_of_mem lam (hS.c1_le htc),
      hlam1 _ htc, one_mul]⟩
  have hG : G₀ ≤ S := hS.sup ▸ sup_le hLt hTb
  exact (hG hg).2 c hc

include hS hlam1 in
theorem hlam : ∀ g : ↥G₀, ∀ v w : ↥V,
    vPair lam (conjV hS.nV g v) (conjV hS.nV g w) = vPair lam v w := by
  intro g v w
  rw [vPair_eq_lamExt, vPair_eq_lamExt, conjV_apply_coe, conjV_apply_coe]
  have e : ⁅(g : U₀) * v * (g : U₀)⁻¹, (g : U₀) * w * (g : U₀)⁻¹⁆ =
      (g : U₀) * ⁅(v : U₀), (w : U₀)⁆ * (g : U₀)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hS.lam_conj lam hlam1 g.2 (commutator_mem_vv v w)

abbrev YM : Type _ := ↥V ⧸ zLam hS.cls2 lam

noncomputable abbrev rho : ↥G₀ →* MulAut (hS.YM lam) :=
  yAct hS.nV hS.cls2 lam (hS.hlam lam hlam1)

noncomputable abbrev kY : Subgroup (MulAut (hS.YM lam)) := (Lt.subgroupOf G₀).map (hS.rho lam hlam1)

noncomputable abbrev eY : Subgroup (MulAut (hS.YM lam)) := (E.subgroupOf G₀).map (hS.rho lam hlam1)

theorem rho_mk (g : ↥G₀) (v : ↥V) :
    hS.rho lam hlam1 g (QuotientGroup.mk v) = QuotientGroup.mk (conjV hS.nV g v) := rfl

theorem mem_zLam_of_mem_centralizer {z : ↥V} (hz : (z : U₀) ∈ Subgroup.centralizer (V : Set U₀)) :
    z ∈ zLam hS.cls2 lam := by
  intro w
  rw [vPair_eq_lamExt]
  have : ⁅(z : U₀), (w : U₀)⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hz w w.2).symm
  rw [this, lamExt_of_mem lam (one_mem _)]
  exact map_one lam

include hS in
theorem sq_eq_one (y : hS.YM lam) : y ^ 2 = 1 := by
  induction y using QuotientGroup.induction_on with
  | H v =>
    have key : ∀ x (hx : x ∈ Subgroup.closure {v | v ∈ V ∧ v ^ 2 = 1}),
        ∀ hxV : x ∈ V, (QuotientGroup.mk (⟨x, hxV⟩ : ↥V) : hS.YM lam) ^ 2 = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        intro hyV
        rw [← QuotientGroup.mk_pow]
        have : (⟨y, hyV⟩ : ↥V) ^ 2 = 1 := Subtype.ext (by simpa using hy.2)
        rw [this, QuotientGroup.mk_one]
      | one =>
        intro h1
        have : (⟨1, h1⟩ : ↥V) = 1 := rfl
        rw [this, QuotientGroup.mk_one, one_pow]
      | mul a b ha hb iha ihb =>
        intro hab
        have haV : a ∈ V := hS.invol ▸ ha
        have hbV : b ∈ V := hS.invol ▸ hb
        have e : (⟨a * b, hab⟩ : ↥V) = ⟨a, haV⟩ * ⟨b, hbV⟩ := rfl
        rw [e, QuotientGroup.mk_mul, mul_pow, iha haV, ihb hbV, one_mul]
      | inv a ha iha =>
        intro hai
        have haV : a ∈ V := hS.invol ▸ ha
        have e : (⟨a⁻¹, hai⟩ : ↥V) = (⟨a, haV⟩ : ↥V)⁻¹ := rfl
        rw [e, QuotientGroup.mk_inv, inv_pow, iha haV, inv_one]
    have hv : (v : U₀) ∈ Subgroup.closure {v | v ∈ V ∧ v ^ 2 = 1} := hS.invol ▸ v.2
    exact key v hv v.2

theorem pairing_isInv : (yPairing hS.cls2 lam).IsInv (hS.rho lam hlam1).range :=
  yPairing_isInv hS.nV hS.cls2 lam (hS.hlam lam hlam1)

theorem kY_le : hS.kY lam hlam1 ≤ (hS.rho lam hlam1).range := Subgroup.map_le_range _ _

theorem eY_le : hS.eY lam hlam1 ≤ (hS.rho lam hlam1).range := Subgroup.map_le_range _ _

theorem range_le_normalizer_kY :
    (hS.rho lam hlam1).range ≤
      Subgroup.normalizer (hS.kY lam hlam1 : Set (MulAut (hS.YM lam))) := by
  rintro _ ⟨g, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g : ↥G₀, ∀ k ∈ hS.kY lam hlam1,
      hS.rho lam hlam1 g * k * (hS.rho lam hlam1 g)⁻¹ ∈ hS.kY lam hlam1 := by
    rintro g _ ⟨l, hl, rfl⟩
    refine ⟨g * l * g⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hS.nLt g.2) l).mp hl
  intro k
  refine ⟨key g k, fun hk => ?_⟩
  have := key g⁻¹ _ hk
  simpa [mul_assoc] using this

include hS in
theorem subgroupOf_perfect :
    ⁅Lt.subgroupOf G₀, Lt.subgroupOf G₀⁆ = Lt.subgroupOf G₀ := by
  apply Subgroup.map_injective G₀.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS.lt_le, hS.perf]

theorem kY_perfect : ⁅hS.kY lam hlam1, hS.kY lam hlam1⁆ = hS.kY lam hlam1 := by
  rw [← Subgroup.map_commutator, hS.subgroupOf_perfect]

include hS in
theorem finite_V : Finite ↥V :=
  have : Finite ↥G₀ := hS.finite
  Finite.of_injective _ (Subgroup.inclusion_injective hS.v_le)

include hS in
theorem finite_YM : Finite (hS.YM lam) :=
  have : Finite ↥V := hS.finite_V
  inferInstance

include hS in
theorem index_fixV_eY_le : (fixV (hS.eY lam hlam1)).index ≤ e := by
  have : Finite ↥V := hS.finite_V
  have : Finite (hS.YM lam) := hS.finite_YM lam
  obtain ⟨R, -, hRe, hRE⟩ := hS.ff
  set Rb : Subgroup (hS.YM lam) := (R.subgroupOf V).map (QuotientGroup.mk' (zLam hS.cls2 lam))
  have hRb : Rb ≤ fixV (hS.eY lam hlam1) := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hr hg
    rw [QuotientGroup.mk'_apply, rho_mk, QuotientGroup.eq]
    apply hS.mem_zLam_of_mem_centralizer lam
    have e : (((conjV hS.nV g r)⁻¹ * r : ↥V) : U₀) = ⁅(g : U₀), (r : U₀)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjV_apply_coe, commutatorElement_def]
      group
    rw [e]
    apply hRE
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hg (R.inv_mem hr)
  have h1 : (fixV (hS.eY lam hlam1)).index ∣ Rb.index := Subgroup.index_dvd_of_le hRb
  have h2 : Rb.index ∣ (R.subgroupOf V).index :=
    Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
  have h3 : 0 < (R.subgroupOf V).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact (Nat.le_of_dvd h3 (h1.trans h2)).trans hRe

include hS in
theorem le_relIndex_kerRel (W N : Subgroup (hS.YM lam))
    (hirr : IrrSec (hS.rho lam hlam1).range W N) (hnc : NonCent (hS.kY lam hlam1) W N) :
    e ≤ (kerRel (hS.eY lam hlam1) W N (hirr.2.2.1.mono (hS.eY_le lam hlam1))).relIndex
      (hS.eY lam hlam1) := by
  have : Finite ↥G₀ := hS.finite
  exact (le_of_eq hS.e_eq.symm).trans
    (le_relIndex_kerRel_aux _ hS.e_le hS.faith W N hirr.2.1 hirr.2.2.1 hnc)

include hS in
theorem nonCent_top (hc : ∃ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, Lt⁆, V⁆ ∧ lam c ≠ 1) :
    NonCent (hS.kY lam hlam1) ⊤ ⊥ := by
  obtain ⟨c, hc, hlc⟩ := hc
  have h1 : ∃ a ∈ ⁅V, Lt⁆, ∃ w ∈ V, lamExt lam ⁅a, w⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : ⁅⁅V, Lt⁆, V⁆ ≤ (lam.ker).map (⁅V, V⁆ : Subgroup U₀).subtype := by
      rw [Subgroup.commutator_le]
      intro a ha w hw
      have hm : ⁅a, w⁆ ∈ ⁅V, V⁆ := Subgroup.commutator_mem_commutator (hS.commV_le ha) hw
      refine ⟨⟨⁅a, w⁆, hm⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, ← lamExt_of_mem lam hm]
      exact hcon a ha w hw
    obtain ⟨c', hc', hcc'⟩ := hle hc
    have : c' = c := Subtype.ext hcc'
    rw [this, SetLike.mem_coe, MonoidHom.mem_ker] at hc'
    exact hlc hc'
  obtain ⟨a, ha, w, hw, haw⟩ := h1
  have h2 : ∃ v ∈ V, ∃ l ∈ Lt, ⁅v, l⁆ ∉ (zLam hS.cls2 lam).map V.subtype := by
    by_contra hcon
    push Not at hcon
    have hle : ⁅V, Lt⁆ ≤ (zLam hS.cls2 lam).map V.subtype := Subgroup.commutator_le.mpr hcon
    obtain ⟨a', ha', haa'⟩ := hle ha
    have := ha' ⟨w, hw⟩
    rw [vPair_eq_lamExt] at this
    have haa : (a' : U₀) = a := haa'
    rw [haa] at this
    exact haw this
  obtain ⟨v, hv, l, hl, hvl⟩ := h2
  refine ⟨hS.rho lam hlam1 ⟨l, hS.lt_le hl⟩,
    ⟨⟨l, hS.lt_le hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩,
    QuotientGroup.mk ⟨v, hv⟩, Subgroup.mem_top _, ?_⟩
  rw [Subgroup.mem_bot, rho_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    QuotientGroup.eq_one_iff]
  intro hz
  apply hvl
  refine ⟨(conjV hS.nV ⟨l, hS.lt_le hl⟩ ⟨v, hv⟩ * ⟨v, hv⟩⁻¹)⁻¹, (zLam hS.cls2 lam).inv_mem hz, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, conjV_apply_coe,
    commutatorElement_def]
  group

include hS in
theorem irrSec (he : e = 2 ∨ e = 4) (hc : ∃ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, Lt⁆, V⁆ ∧ lam c ≠ 1) :
    IrrSec (hS.rho lam hlam1).range (commV (hS.kY lam hlam1))
      (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)) := by
  have : Finite (hS.YM lam) := hS.finite_YM lam
  exact irrSec_commV (hS.sq_eq_one lam) (yPairing hS.cls2 lam) (hS.pairing_isInv lam hlam1)
    (hS.kY_le lam hlam1) (hS.eY_le lam hlam1) (hS.range_le_normalizer_kY lam hlam1)
    (hS.kY_perfect lam hlam1) he (hS.index_fixV_eY_le lam hlam1)
    (fun W N hirr hnc => hS.le_relIndex_kerRel lam hlam1 W N hirr hnc)
    (hS.nonCent_top lam hlam1 hc)

end EndSetup

end CFSG.Quasithin.MS93.S38E
