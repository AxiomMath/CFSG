module

public import CFSG.RankThree.GF2n.Smith81.S81KNormCom
public import CFSG.RankThree.GF2n.Smith81.S81XD6Mon
public import CFSG.RankThree.GF2n.Smith81.S81XD6Nrm
public import CFSG.RankThree.GF2n.Smith81.S81KNormHall

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Normalizer

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.E7X
  CFSG.RankThree.GF2n.Smith81.D6X CFSG.RankThree.GF2n.Smith81.D6Spin


variable {K : Type} [Field K]

@[expose] def SubV (K : Type) [Field K] (b : Fin e7Data.d) : Submodule K (V K) :=
  Finsupp.supported K K {c : Fin e7Data.d | ltB b c = true}

theorem SubV_mono {b c : Fin e7Data.d} (h : ltB b c = true) : SubV K c ≤ SubV K b :=
  Finsupp.supported_mono fun d hd => lt_trans' b c d h hd

@[expose] def TriV (g : Module.End K (V K)) : Prop :=
  ∀ b : Fin e7Data.d, pr b theta = 0 →
    g (Finsupp.single b 1) - Finsupp.single b 1 ∈ SubV K b

theorem TriV.map_sub {g : Module.End K (V K)} (hg : TriV g) {b : Fin e7Data.d}
    (hb : pr b theta = 0) {w : V K} (hw : w ∈ SubV K b) : g w - w ∈ SubV K b := by
  have hw' : w ∈ Submodule.span K ((fun i => Finsupp.single i (1 : K)) ''
      {c : Fin e7Data.d | ltB b c = true}) := by
    rw [← Finsupp.supported_eq_span_single]
    exact hw
  clear hw
  induction hw' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact SubV_mono hc (hg c (lt_idx0 b c hc).2)
  | zero => simp
  | add x y _ _ hx hy =>
    have e : g (x + y) - (x + y) = (g x - x) + (g y - y) := by rw [map_add]; abel
    rw [e]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have e : g (a • x) - a • x = a • (g x - x) := by rw [map_smul, smul_sub]
    rw [e]
    exact Submodule.smul_mem _ _ hx

theorem TriV.mul {g h : Module.End K (V K)} (hg : TriV g) (hh : TriV h) : TriV (g * h) := by
  intro b hb
  have e : (g * h) (Finsupp.single b 1) - Finsupp.single b 1 =
      (g (Finsupp.single b 1) - Finsupp.single b 1) +
        (h (Finsupp.single b 1) - Finsupp.single b 1) +
        (g (h (Finsupp.single b 1) - Finsupp.single b 1) -
          (h (Finsupp.single b 1) - Finsupp.single b 1)) := by
    rw [Module.End.mul_apply, _root_.map_sub g]
    abel
  rw [e]
  exact add_mem (add_mem (hg b hb) (hh b hb)) (hg.map_sub hb (hh b hb))

theorem TriV.one : TriV (1 : Module.End K (V K)) := fun b _ => by simp

@[expose] def TriG (K : Type) [Field K] : Subgroup (Module.End K (V K))ˣ where
  carrier := {g | TriV (g : Module.End K (V K)) ∧
    TriV ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact ha.mul hb
    · rw [mul_inv_rev, Units.val_mul]
      exact hb'.mul ha'
  one_mem' := ⟨by simpa using TriV.one, by simpa using TriV.one⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by simpa using ha⟩

theorem exists_rootK {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    ∃ k : Fin 126, rootK k = β := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk, hkβ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hβ
  exact ⟨⟨k, by omega⟩, hkβ⟩

theorem lt_shift {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (hz : MinData.toWeight β ⬝ᵥ theta = 0) (hpos : 0 < height (τ := .E7) β)
    {b : Fin e7Data.d} (hb : pr b theta = 0) (h : pr b β = -1) : ltB b (shift β b) = true := by
  obtain ⟨k, rfl⟩ := exists_rootK hβ
  exact rel_le_lt b _ ((relTab_spec b _ hb).2 ⟨k, ⟨hz, hpos⟩, h, wt_shift hβ h⟩)

variable [CharP K 2]

theorem triV_xu {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (hz : MinData.toWeight β ⬝ᵥ theta = 0) (hpos : 0 < height (τ := .E7) β) (c : K) :
    TriV ((e7Data_valid.xu K β c : (Module.End K (V K))ˣ) : Module.End K (V K)) := by
  intro b hb
  rw [e7Data_valid.xu_apply, rootOp_single hβ, add_sub_cancel_left]
  by_cases h : pr b β = -1
  · rw [if_pos h]
    refine Submodule.smul_mem _ _ ?_
    exact Finsupp.single_mem_supported K (1 : K) (lt_shift hβ hz hpos hb h)
  · rw [if_neg h, smul_zero]
    exact Submodule.zero_mem _

theorem UL_le_TriG : UL K ≤ TriG K := by
  rw [UL, Subgroup.closure_le]
  rintro g ⟨β, hβ, hz, hpos, c, rfl⟩
  exact ⟨triV_xu hβ hz hpos c, by rw [xu_inv_eq]; exact triV_xu hβ hz hpos (-c)⟩

@[expose] def imW (K : Type) [Field K] (A : Subgroup (Gp K)) : Subgroup (W K ≃ₗ[K] W K) where
  carrier := {x | ∃ g ∈ A, IndW g x}
  mul_mem' := by
    rintro x y ⟨g, hg, hx⟩ ⟨g', hg', hy⟩
    exact ⟨g * g', mul_mem hg hg', hx.mul hy⟩
  one_mem' := ⟨1, one_mem _, IndW.one⟩
  inv_mem' := by
    rintro x ⟨g, hg, hx⟩
    exact ⟨g⁻¹, inv_mem hg, hx.inv⟩

abbrev UW (K : Type) [Field K] : Subgroup (W K ≃ₗ[K] W K) := imW K (ULG K)

theorem UW_le_EAut0 : UW K ≤ EAut0 K := by
  rintro x ⟨g, hg, hx⟩
  exact mem_EAut0_iff.2 ⟨g, ULG_le_LamG hg, hx⟩

theorem tri_of_mem_UW {x : W K ≃ₗ[K] W K} (hx : x ∈ UW K) (b d : Idx0)
    (h : (x (Finsupp.single b (1 : K) : W K) - (Finsupp.single b (1 : K) : W K)) d ≠ 0) :
    ltB b d = true := by
  obtain ⟨u, hu, hxu⟩ := hx
  have hT : TriV (endoE u) := (UL_le_TriG (mem_ULG.1 hu)).1
  have h1 := hT b (mem_idx0.1 b.2)
  have h2 : (endoE u (Finsupp.single (b : Fin e7Data.d) (1 : K) : V K) -
      (Finsupp.single (b : Fin e7Data.d) (1 : K) : V K)) = emb K (x (Finsupp.single b (1 : K)) -
        (Finsupp.single b (1 : K) : W K)) := by
    rw [map_sub, hxu, emb_single]
  rw [h2] at h1
  by_contra hne
  apply h
  have h3 := (Finsupp.mem_supported' K _).1 h1 (d : Fin e7Data.d) (fun hd => hne hd)
  rw [← emb_apply_coe]
  exact h3

@[expose] def IsMonW (m : W K ≃ₗ[K] W K) (σ : Idx0 → Idx0) : Prop :=
  ∀ b : Idx0, ∃ d : K, d ≠ 0 ∧
    m (Finsupp.single b (1 : K) : W K) = d • (Finsupp.single (σ b) (1 : K) : W K)

theorem IsMonW.injective {m : W K ≃ₗ[K] W K} {σ : Idx0 → Idx0} (hm : IsMonW m σ) :
    Function.Injective σ := by
  choose d hd0 hmd using hm
  intro b c hbc
  by_contra hne
  have h1 : m (d c • (Finsupp.single b (1 : K) : W K) - d b • (Finsupp.single c (1 : K) : W K)) =
      0 := by
    rw [map_sub, map_smul, map_smul, hmd, hmd, hbc, smul_smul, smul_smul, mul_comm (d c) (d b),
      sub_self]
  have h2 := m.injective (h1.trans (map_zero m).symm)
  have h3 := congrArg (fun w : W K => w b) h2
  simp [Finsupp.single_apply, hne, Ne.symm hne] at h3
  exact hd0 c h3

theorem eq_self_of_normalizes {m : W K ≃ₗ[K] W K} {σ : Idx0 → Idx0} (hm : IsMonW m σ)
    (hn : ∀ x ∈ UW K, m * x * m⁻¹ ∈ UW K) (b : Idx0) : σ b = b := by
  classical
  have hinj := hm.injective
  choose d hd0 hmd using hm
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  have hedge : ∀ b c : Idx0, RelK (b : Fin e7Data.d) (c : Fin e7Data.d) →
      ltB (σ b) (σ c) = true := by
    rintro b c ⟨k, ⟨hz, hpos⟩, hpr, hwt⟩
    have hβ : IsRoot .E7 (rootK k) :=
      RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)
    have hg : e7Data_valid.xm K (rootK k) 1 ∈ ULG K :=
      mem_ULG.2 (Subgroup.subset_closure ⟨_, hβ, hz, hpos, 1, rfl⟩)
    obtain ⟨x, hx⟩ := exists_indW (ULG_le_LamG hg)
    have hxU : x ∈ UW K := ⟨_, hg, hx⟩
    have hxb : x (Finsupp.single b (1 : K) : W K) =
        (Finsupp.single b (1 : K) : W K) + (Finsupp.single c (1 : K) : W K) := by
      apply emb_injective
      rw [hx, map_add, emb_single, emb_single]
      show ((e7Data_valid.xu K (rootK k) 1 : (Module.End K (V K))ˣ) : Module.End K (V K))
        (Finsupp.single (b : Fin e7Data.d) 1) = _
      rw [e7Data_valid.xu_apply, rootOp_single hβ, if_pos hpr, one_smul, shift_eq hwt]
    have hy := hn x hxU
    have hmi : m.symm (Finsupp.single (σ b) (1 : K) : W K) =
        (d b)⁻¹ • (Finsupp.single b (1 : K) : W K) := by
      apply m.injective
      rw [LinearEquiv.apply_symm_apply, map_smul, hmd b, smul_smul, inv_mul_cancel₀ (hd0 b),
        one_smul]
    have hyv : (m * x * m⁻¹) (Finsupp.single (σ b) (1 : K) : W K) -
        (Finsupp.single (σ b) (1 : K) : W K) =
        ((d b)⁻¹ * d c) • (Finsupp.single (σ c) (1 : K) : W K) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv, hmi, map_smul, hxb,
        map_smul, map_add, hmd b, hmd c, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ (hd0 b),
        one_smul, add_sub_cancel_left]
    have hcoef := tri_of_mem_UW hy (σ b) (σ c) (by
      rw [hyv, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
      exact mul_ne_zero (inv_ne_zero (hd0 b)) (hd0 c))
    exact hcoef
  let σ' : Fin e7Data.d → Fin e7Data.d :=
    fun x => if h : x ∈ idx0 then ((σ ⟨x, h⟩ : Idx0) : Fin e7Data.d) else x
  have hσ'val : ∀ x : Idx0, σ' (x : Fin e7Data.d) = (σ x : Fin e7Data.d) := by
    intro x
    simp only [σ', dif_pos x.2]
  have key := eq_self_of_mono σ'
    (fun x hx => by
      have hx' : x ∈ idx0 := mem_idx0.2 hx
      have := hσ'val ⟨x, hx'⟩
      simp only at this
      rw [this]
      exact mem_idx0.1 (σ ⟨x, hx'⟩).2)
    (fun x y hx hy h => by
      have hx' : x ∈ idx0 := mem_idx0.2 hx
      have hy' : y ∈ idx0 := mem_idx0.2 hy
      have h1 := hσ'val ⟨x, hx'⟩
      have h2 := hσ'val ⟨y, hy'⟩
      simp only at h1 h2
      rw [h1, h2] at h
      exact congrArg Subtype.val (hinj (Subtype.ext h)))
    (fun x y hxy => by
      have hlt := rel_le_lt x y hxy
      obtain ⟨hx, hy⟩ := lt_idx0 x y hlt
      have hx' : x ∈ idx0 := mem_idx0.2 hx
      have hy' : y ∈ idx0 := mem_idx0.2 hy
      have h1 := hσ'val ⟨x, hx'⟩
      have h2 := hσ'val ⟨y, hy'⟩
      simp only at h1 h2
      rw [h1, h2]
      exact hedge ⟨x, hx'⟩ ⟨y, hy'⟩ ((relTab_spec x y hx).1 hxy))
  exact Subtype.ext ((hσ'val b).symm.trans (key b (mem_idx0.1 b.2)))

theorem weight_torMon {t₁ t₂ n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (ht₁ : t₁ ∈ Tor K)
    (ht₂ : t₂ ∈ Tor K) (hn : IsMon n σ ρ) (a : Fin e7Data.d) :
    ∃ s : K, s ≠ 0 ∧ endoE (t₁ * n * t₂) (Finsupp.single a 1) = s • Finsupp.single (σ a) 1 := by
  obtain ⟨s₁, hs₁, h₁⟩ := tor_diag ht₁ (σ a)
  obtain ⟨s₂, hs₂, h₂⟩ := tor_diag ht₂ a
  refine ⟨s₂ * s₁, mul_ne_zero hs₂ hs₁, ?_⟩
  show endoE t₁ (endoE n (endoE t₂ (Finsupp.single a 1))) = _
  rw [h₂, map_smul, hn.weight a, map_smul, h₁, smul_smul]

theorem exists_mon_bruhat {g : W K ≃ₗ[K] W K} (hg : g ∈ EAut0 K) :
    ∃ x₁ ∈ UW K, ∃ x₂ ∈ UW K, ∃ m ∈ EAut0 K, ∃ σ : Idx0 → Idx0, IsMonW m σ ∧
      g = x₁ * m * x₂ := by
  obtain ⟨gt, hgL, hgI⟩ := mem_EAut0_iff.1 hg
  obtain ⟨u₁, hu₁, t₁, ht₁, t₂, ht₂, u₂, hu₂, n, σn, ρ, hn, hgeq⟩ := bruhat_L hgL
  have hmtL : t₁ * n * t₂ ∈ LamG K := by
    have : t₁ * n * t₂ = u₁⁻¹ * gt * u₂⁻¹ := by
      rw [hgeq]
      group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (ULG_le_LamG hu₁)) hgL) (inv_mem (ULG_le_LamG hu₂))
  obtain ⟨x₁, hx₁⟩ := exists_indW (ULG_le_LamG hu₁)
  obtain ⟨x₂, hx₂⟩ := exists_indW (ULG_le_LamG hu₂)
  obtain ⟨m, hm⟩ := exists_indW hmtL
  have hgm : g = x₁ * m * x₂ := by
    rw [hgeq] at hgI
    exact IndW.unique hgI ((hx₁.mul hm).mul hx₂)
  have hmon : ∀ b : Idx0, ∃ c : Idx0, ∃ s : K, s ≠ 0 ∧
      m (Finsupp.single b (1 : K) : W K) = s • (Finsupp.single c (1 : K) : W K) := by
    intro b
    obtain ⟨s, hs, hsv⟩ := weight_torMon ht₁ ht₂ hn (b : Fin e7Data.d)
    have h1 : emb K (m (Finsupp.single b (1 : K) : W K)) =
        s • (Finsupp.single (σn b) (1 : K) : V K) := by
      rw [hm, emb_single]
      exact hsv
    have hc : σn (b : Fin e7Data.d) ∈ idx0 := by
      by_contra hc
      have h2 := (mem_V0.1 (emb_mem_V0 (m (Finsupp.single b (1 : K) : W K)))) _ hc
      rw [h1, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h2
      exact hs h2
    refine ⟨⟨_, hc⟩, s, hs, emb_injective ?_⟩
    rw [h1, map_smul, emb_single]
  choose c s hs0 hms using hmon
  refine ⟨x₁, ⟨u₁, hu₁, hx₁⟩, x₂, ⟨u₂, hu₂, hx₂⟩, m, mem_EAut0_iff.2 ⟨t₁ * n * t₂, hmtL, hm⟩, c,
    fun b => ⟨s b, hs0 b, hms b⟩, hgm⟩

@[expose] def DiagW (K : Type) [Field K] : Subgroup (W K ≃ₗ[K] W K) where
  carrier := {d | ∀ b : Idx0, ∃ c : K,
    d (Finsupp.single b (1 : K) : W K) = c • (Finsupp.single b (1 : K) : W K)}
  mul_mem' := by
    rintro x y hx hy b
    obtain ⟨c, hc⟩ := hy b
    obtain ⟨c', hc'⟩ := hx b
    exact ⟨c' * c, by rw [LinearEquiv.mul_apply, hc, map_smul, hc', smul_smul, mul_comm]⟩
  one_mem' := fun b => ⟨1, by simp⟩
  inv_mem' := by
    rintro x hx b
    obtain ⟨c, hc⟩ := hx b
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact Finsupp.single_ne_zero.2 one_ne_zero (x.injective (hc.trans (map_zero x).symm))
    refine ⟨c⁻¹, ?_⟩
    rw [LinearEquiv.coe_inv]
    apply x.injective
    rw [LinearEquiv.apply_symm_apply, map_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

@[expose] def HdW (K : Type) [Field K] : Subgroup (W K ≃ₗ[K] W K) :=
  EAut0 K ⊓ Subgroup.normalizer (UW K : Set (W K ≃ₗ[K] W K)) ⊓ DiagW K

theorem normalizer_mul {g : W K ≃ₗ[K] W K} (hg : g ∈ EAut0 K)
    (hn : g ∈ Subgroup.normalizer (UW K : Set (W K ≃ₗ[K] W K))) :
    ∃ x ∈ UW K, ∃ h ∈ HdW K, g = x * h := by
  obtain ⟨x₁, hx₁, x₂, hx₂, m, hmE, σ, hσ, hgm⟩ := exists_mon_bruhat hg
  have hmeq : m = x₁⁻¹ * g * x₂⁻¹ := by rw [hgm]; group
  have hnm : ∀ x, x ∈ UW K ↔ m * x * m⁻¹ ∈ UW K := by
    intro x
    have e : m * x * m⁻¹ = x₁⁻¹ * (g * (x₂⁻¹ * x * x₂) * g⁻¹) * x₁ := by rw [hmeq]; group
    rw [e]
    have h1 := Subgroup.mem_normalizer_iff.1 hn (x₂⁻¹ * x * x₂)
    constructor
    · intro hx
      exact mul_mem (mul_mem (inv_mem hx₁) (h1.1 (mul_mem (mul_mem (inv_mem hx₂) hx) hx₂))) hx₁
    · intro hx
      have h2 : g * (x₂⁻¹ * x * x₂) * g⁻¹ ∈ UW K := by
        have := mul_mem (mul_mem hx₁ hx) (inv_mem hx₁)
        have e2 : x₁ * (x₁⁻¹ * (g * (x₂⁻¹ * x * x₂) * g⁻¹) * x₁) * x₁⁻¹ =
            g * (x₂⁻¹ * x * x₂) * g⁻¹ := by group
        rwa [e2] at this
      have h3 := h1.2 h2
      have e3 : x = x₂ * (x₂⁻¹ * x * x₂) * x₂⁻¹ := by group
      rw [e3]
      exact mul_mem (mul_mem hx₂ h3) (inv_mem hx₂)
  have hdiag : m ∈ DiagW K := fun b => by
    obtain ⟨d, hd0, hd⟩ := hσ b
    have := eq_self_of_normalizes hσ (fun x hx => (hnm x).1 hx) b
    exact ⟨d, by rw [hd, this]⟩
  refine ⟨x₁ * (m * x₂ * m⁻¹), mul_mem hx₁ ((hnm x₂).1 hx₂), m,
    ⟨⟨hmE, Subgroup.mem_normalizer_iff.2 hnm⟩, hdiag⟩, ?_⟩
  rw [hgm]
  group

theorem nt_mem_LamG (i : Fin (Tag.rank .E7)) (hi : 1 ≤ i.val) (t : Kˣ) :
    e7Data_valid.nt K i t ∈ LamG K := by
  have hsP : (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ Perp := single_mem_Perp i hi
  have hsN : -(Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ Perp := neg_mem_Perp hsP
  rw [mem_LamG]
  show ((e7Data_valid.xm K (Pi.single i 1) t * e7Data_valid.xm K (-Pi.single i 1)
      (-((t⁻¹ : Kˣ) : K)) * e7Data_valid.xm K (Pi.single i 1) t :
      ↥(e7Data_valid.minGroup K)) : (Module.End K (V K))ˣ) ∈ Lam K
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact mul_mem (mul_mem (xu_mem_Lam hsP _) (xu_mem_Lam hsN _)) (xu_mem_Lam hsP _)

theorem hm_mem_LamG (i : Fin (Tag.rank .E7)) (hi : 1 ≤ i.val) (t : Kˣ) :
    e7Data_valid.hm K i t ∈ LamG K :=
  mul_mem (nt_mem_LamG i hi t) (inv_mem (nt_mem_LamG i hi 1))

theorem conj_mem_UW {t : Gp K} (ht : t ∈ Tor K) {h x : W K ≃ₗ[K] W K} (hh : IndW t h)
    (hx : x ∈ UW K) : h * x * h⁻¹ ∈ UW K := by
  obtain ⟨u, hu, hxu⟩ := hx
  exact ⟨t * u * t⁻¹, tor_conj_ULG ht hu, (hh.mul hxu).mul hh.inv⟩

theorem exists_hmW (i : Fin (Tag.rank .E7)) (hi : 1 ≤ i.val) (t : Kˣ) :
    ∃ h ∈ HdW K, ∀ b : Idx0, h (Finsupp.single b (1 : K) : W K) =
      ((t ^ (e7Data.wt b i) : Kˣ) : K) • (Finsupp.single b (1 : K) : W K) := by
  obtain ⟨h, hh⟩ := exists_indW (hm_mem_LamG (K := K) i hi t)
  have hact : ∀ b : Idx0, h (Finsupp.single b (1 : K) : W K) =
      ((t ^ (e7Data.wt b i) : Kˣ) : K) • (Finsupp.single b (1 : K) : W K) := by
    intro b
    apply emb_injective
    rw [hh, emb_single, map_smul, emb_single]
    show e7Data_valid.endo K (e7Data_valid.hm K i t) (Finsupp.single (b : Fin e7Data.d) 1) = _
    rw [e7Data_valid.endo_hm, MinData.hDiag_single]
  have htor : e7Data_valid.hm K i t ∈ Tor K :=
    Subgroup.mem_iSup_of_mem i (e7Data_valid.hm_mem_torus K i t)
  have htor' : (e7Data_valid.hm K i t)⁻¹ ∈ Tor K := inv_mem htor
  have hnorm : h ∈ Subgroup.normalizer (UW K : Set (W K ≃ₗ[K] W K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => conj_mem_UW htor hh hx
    · intro hx
      have := conj_mem_UW htor' hh.inv hx
      have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
      rwa [e] at this
  exact ⟨h, ⟨⟨mem_EAut0_iff.2 ⟨_, hm_mem_LamG i hi t, hh⟩, hnorm⟩, fun b => ⟨_, hact b⟩⟩, hact⟩

omit [CharP K 2] in
theorem exists_unit_ne_one [Finite K] (hK : 3 ≤ Nat.card K) : ∃ t : Kˣ, t ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun x : K => decide (x = 0)) := by
    intro x y hxy
    simp only [decide_eq_decide] at hxy
    by_cases hx : x = 0
    · exact hx.trans (hxy.1 hx).symm
    · have hy : y ≠ 0 := fun hy => hx (hxy.2 hy)
      have h1 : x = 1 := congrArg Units.val (hcon (Units.mk0 x hx))
      have h2 : y = 1 := congrArg Units.val (hcon (Units.mk0 y hy))
      rw [h1, h2]
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem sep_check : ∀ b b' : Fin e7Data.d, pr b theta = 0 → pr b' theta = 0 → b ≠ b' →
    ∃ i : Fin (Tag.rank .E7), 1 ≤ i.val ∧
      (e7Data.wt b i - e7Data.wt b' i = 1 ∨ e7Data.wt b i - e7Data.wt b' i = -1 ∨
        e7Data.wt b i - e7Data.wt b' i = 2 ∨ e7Data.wt b i - e7Data.wt b' i = -2) := by
  unfold pr
  decide +kernel

theorem exists_sep [Finite K] (hK : 3 ≤ Nat.card K) (b b' : Idx0) (hbb : b ≠ b') :
    ∃ h ∈ HdW K, ∃ c c' : K, c ≠ c' ∧ h (Finsupp.single b (1 : K) : W K) = c • (Finsupp.single b
      (1 : K) : W K) ∧ h (Finsupp.single b' (1 : K) : W K) = c' • (Finsupp.single b'
      (1 : K) : W K) := by
  obtain ⟨i, hi, he⟩ := sep_check b b' (mem_idx0.1 b.2) (mem_idx0.1 b'.2)
    (fun h => hbb (Subtype.ext h))
  obtain ⟨t, ht⟩ := exists_unit_ne_one hK
  obtain ⟨h, hh, hact⟩ := exists_hmW i hi t
  refine ⟨h, hh, _, _, ?_, hact b, hact b'⟩
  intro hc
  have hc' : t ^ (e7Data.wt b i) = t ^ (e7Data.wt b' i) := Units.ext hc
  have h1 : t ^ (e7Data.wt b i - e7Data.wt b' i) = 1 := by
    rw [zpow_sub, hc', mul_inv_cancel]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rcases he with he | he | he | he <;> rw [he] at h1
  · exact ht (by simpa using h1)
  · exact ht (by simpa using h1)
  · have hsq : ((t : K)) ^ 2 = 1 := by
      have := congrArg Units.val h1
      simpa [zpow_ofNat] using this
    have h3 : ((t : K) - 1) ^ 2 = 0 := by linear_combination hsq - ((t : K) - 1) * h2
    exact ht (Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h3)))
  · have hsq : ((t : K)⁻¹) ^ 2 = 1 := by
      have := congrArg Units.val h1
      simpa [zpow_neg, zpow_ofNat] using this
    have hsq' : ((t : K)) ^ 2 = 1 := by
      have h4 : ((t : K)) ^ 2 * ((t : K)⁻¹) ^ 2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (Units.ne_zero t), one_pow]
      rw [hsq, mul_one] at h4
      exact h4
    have h3 : ((t : K) - 1) ^ 2 = 0 := by linear_combination hsq' - ((t : K) - 1) * h2
    exact ht (Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h3)))

omit [CharP K 2] in
theorem finite_W (K : Type) [Field K] [Finite K] : Finite (W K) :=
  Finite.of_equiv (Idx0 → K) Finsupp.equivFunOnFinite.symm

omit [CharP K 2] in
theorem finite_WAut (K : Type) [Field K] [Finite K] : Finite (W K ≃ₗ[K] W K) := by
  haveI := finite_W K
  exact Finite.of_injective (fun f : W K ≃ₗ[K] W K => (f : W K → W K)) DFunLike.coe_injective

attribute [local instance] finite_W finite_WAut

theorem one_add_pow_two_pow {M : Type} [AddCommGroup M] [Module K M] (N : Module.End K M)
    (j : ℕ) : (1 + N) ^ (2 ^ j) = 1 + N ^ (2 ^ j) := by
  have h2 : ∀ Y : Module.End K M, Y + Y = 0 := by
    intro Y
    ext w
    simp only [LinearMap.add_apply, LinearMap.zero_apply]
    rw [← two_smul K (Y w), CharTwo.two_eq_zero, zero_smul]
  have hsq : ∀ Y : Module.End K M, (1 + Y) ^ 2 = 1 + Y ^ 2 := by
    intro Y
    calc (1 + Y) ^ 2 = 1 + (Y + Y) + Y ^ 2 := by noncomm_ring
      _ = 1 + Y ^ 2 := by rw [h2, add_zero]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, ih, hsq, ← pow_mul, ← pow_succ]

theorem pow32_eq_zero_of_tri (N : Module.End K (W K))
    (hN : ∀ b : Idx0, N (Finsupp.single b (1 : K) : W K) ∈
      Finsupp.supported K K {d : Idx0 | ltB b d = true}) : N ^ 32 = 0 := by
  classical
  let h : Idx0 → ℕ := fun c => cntDown c.1
  let Vm : ℕ → Submodule K (W K) := fun m => Finsupp.supported K K {c : Idx0 | m ≤ h c}
  have step : ∀ m, ∀ w ∈ Vm m, N w ∈ Vm (m + 1) := by
    intro m w hw
    have hw' : w ∈ Submodule.span K ((fun i => Finsupp.single i (1 : K)) ''
        {c : Idx0 | m ≤ h c}) := by
      rw [← Finsupp.supported_eq_span_single]
      exact hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine Finsupp.supported_mono (fun d hd => ?_) (hN c)
      have h1 := cntDown_lt_of_lt c.1 d.1 hd
      have h2 : m ≤ cntDown c.1 := hc
      show m + 1 ≤ cntDown d.1
      omega
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ _ hx
  have iter : ∀ j m, ∀ w ∈ Vm m, (N ^ j) w ∈ Vm (m + j) := by
    intro j
    induction j with
    | zero =>
      intro m w hw
      simpa using hw
    | succ j ih =>
      intro m w hw
      have h1 := step _ _ (ih m w hw)
      rw [pow_succ', Module.End.mul_apply]
      have e : m + (j + 1) = m + j + 1 := by omega
      rw [e]
      exact h1
  apply LinearMap.ext
  intro w
  have hw : w ∈ Vm 0 := (Finsupp.mem_supported' K _).2 fun c hc => absurd (Nat.zero_le _) hc
  have h1 := iter 32 0 w hw
  refine Finsupp.ext fun c => ?_
  have h2 := (Finsupp.mem_supported' K _).1 h1 c (fun hc => by
    have := cntDown_lt_32 c.1
    have h3 : 0 + 32 ≤ cntDown c.1 := hc
    omega)
  simpa using h2

omit
  [CharP K 2] in
theorem toLinearMap_pow {M : Type} [AddCommGroup M] [Module K M] (y : M ≃ₗ[K] M) (n : ℕ) :
    ((y ^ n : M ≃ₗ[K] M) : Module.End K M) = (y : Module.End K M) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

theorem isPGroup_UW : IsPGroup 2 (UW K) := by
  intro x
  refine ⟨5, ?_⟩
  set y : W K ≃ₗ[K] W K := (x : W K ≃ₗ[K] W K) with hy
  have hyU : y ∈ UW K := x.2
  set N : Module.End K (W K) := (y : Module.End K (W K)) - 1 with hNdef
  have hN : ∀ b : Idx0, N (Finsupp.single b (1 : K) : W K) ∈
      Finsupp.supported K K {d : Idx0 | ltB b d = true} := by
    intro b
    refine (Finsupp.mem_supported' K _).2 fun d hd => ?_
    by_contra hne
    exact hd (tri_of_mem_UW hyU b d hne)
  have h32 := pow32_eq_zero_of_tri N hN
  have hyN : (y : Module.End K (W K)) = 1 + N := by rw [hNdef]; abel
  have hpow : ((y ^ 2 ^ 5 : W K ≃ₗ[K] W K) : Module.End K (W K)) = 1 := by
    rw [toLinearMap_pow, hyN, one_add_pow_two_pow]
    have : N ^ 2 ^ 5 = 0 := h32
    rw [this, add_zero]
  apply Subtype.ext
  show y ^ 2 ^ 5 = 1
  exact LinearEquiv.toLinearMap_injective (by rw [hpow]; rfl)

omit [CharP K 2] in
theorem diag_coord {h : W K ≃ₗ[K] W K} {s : Idx0 → K}
    (hs : ∀ e : Idx0, h (Finsupp.single e (1 : K) : W K) = s e • (Finsupp.single e (1 : K) : W K))
    (w : W K) (c : Idx0) : (h w) c = s c * w c := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add w₁ w₂ h₁ h₂ => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, h₁, h₂, mul_add]
  | single e a =>
    have h1 : (Finsupp.single e a : W K) = a • (Finsupp.single e (1 : K) : W K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have h2 : h (Finsupp.single e a : W K) = (a * s e) • (Finsupp.single e (1 : K) : W K) := by
      rw [h1, map_smul, hs e, smul_smul]
    rw [h2, Finsupp.smul_apply, Finsupp.single_apply, Finsupp.single_apply]
    by_cases hec : e = c
    · subst hec
      simp [mul_comm]
    · simp [hec]

theorem monomial_of_normalizes [Finite K] (hK : 3 ≤ Nat.card K) {T : W K ≃ₗ[K] W K}
    (hT : ∀ h ∈ HdW K, T * h * T⁻¹ ∈ HdW K) : ∃ σ : Idx0 → Idx0, IsMonW T σ := by
  haveI := finite_WAut K
  have hT' := conj_inv_mem_of_finite hT
  have key : ∀ b : Idx0, ∃ c : Idx0, ∃ d : K, d ≠ 0 ∧
      T (Finsupp.single b (1 : K) : W K) = d • (Finsupp.single c (1 : K) : W K) := by
    intro b
    set w : W K := T (Finsupp.single b (1 : K) : W K) with hw
    have hw0 : w ≠ 0 := fun h =>
      Finsupp.single_ne_zero.2 one_ne_zero (T.injective (h.trans (map_zero T).symm))
    have heig : ∀ h ∈ HdW K, ∃ l : K, h w = l • w := by
      intro h hh
      obtain ⟨l, hl⟩ := (hT' h hh).2 b
      refine ⟨l, ?_⟩
      have e1 : h w = T ((T⁻¹ * h * T) (Finsupp.single b (1 : K) : W K)) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
          LinearEquiv.apply_symm_apply]
      rw [e1, hl, map_smul]
    obtain ⟨c, hc⟩ : ∃ c, w c ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw0 (Finsupp.ext hcon)
    have hclaim : ∀ c', w c' ≠ 0 → c' = c := by
      intro c' hc'
      by_contra hne
      obtain ⟨h, hhH, c₁, c₂, hc12, hc1, hc2⟩ := exists_sep hK c c' (fun h => hne h.symm)
      obtain ⟨l, hl⟩ := heig h hhH
      choose s hs using hhH.2
      have hsc : s c = c₁ := by
        have := (hs c).symm.trans hc1
        have h3 := congrArg (fun v : W K => v c) this
        simpa using h3
      have hsc' : s c' = c₂ := by
        have := (hs c').symm.trans hc2
        have h3 := congrArg (fun v : W K => v c') this
        simpa using h3
      have h4 : ∀ e : Idx0, w e ≠ 0 → s e = l := by
        intro e he
        have := diag_coord hs w e
        rw [hl, Finsupp.smul_apply, smul_eq_mul] at this
        exact (mul_right_cancel₀ he this).symm
      exact hc12 (by rw [← hsc, ← hsc', h4 c hc, h4 c' hc'])
    refine ⟨c, w c, hc, Finsupp.ext fun e => ?_⟩
    rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hec : c = e
    · subst hec
      simp
    · have : w e = 0 := by
        by_contra hne
        exact hec (hclaim e hne).symm
      simp [hec, this]
  choose c d hd0 hcd using key
  exact ⟨c, fun b => ⟨d b, hd0 b, hcd b⟩⟩

theorem pow_card_sub_one_of_diag [Finite K] {h : W K ≃ₗ[K] W K} (hh : h ∈ DiagW K) :
    h ^ (Nat.card K - 1) = 1 := by
  classical
  haveI := Fintype.ofFinite K
  choose s hs using hh
  have hs0 : ∀ e, s e ≠ 0 := by
    intro e he
    have h1 := hs e
    rw [he, zero_smul] at h1
    exact Finsupp.single_ne_zero.2 one_ne_zero (h.injective (h1.trans (map_zero h).symm))
  have hpow : ∀ n : ℕ, ∀ e : Idx0, (h ^ n) (Finsupp.single e (1 : K) : W K) =
      (s e) ^ n • (Finsupp.single e (1 : K) : W K) := by
    intro n
    induction n with
    | zero => intro e; simp
    | succ n ih =>
      intro e
      rw [pow_succ, LinearEquiv.mul_apply, hs e, map_smul, ih e, smul_smul, pow_succ']
  have h1 : ∀ e : Idx0, (h ^ (Nat.card K - 1)) (Finsupp.single e (1 : K) : W K) =
      (Finsupp.single e (1 : K) : W K) := by
    intro e
    rw [hpow, Nat.card_eq_fintype_card, FiniteField.pow_card_sub_one_eq_one _ (hs0 e), one_smul]
  apply LinearEquiv.ext
  intro w
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add w₁ w₂ h₁ h₂ => rw [map_add, h₁, h₂]; rfl
  | single e a =>
    have h2 : (Finsupp.single e a : W K) = a • (Finsupp.single e (1 : K) : W K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h2, map_smul, h1]
    rfl

theorem odd_card_sub_one [Finite K] : Odd (Nat.card K - 1) := by
  haveI := Fintype.ofFinite K
  have h2 : 2 ∣ Fintype.card K :=
    (CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)
  have hpos : 0 < Fintype.card K := Fintype.card_pos
  rw [Nat.card_eq_fintype_card]
  obtain ⟨m, hm⟩ := h2
  exact ⟨m - 1, by omega⟩

theorem odd_orderOf_of_mem_HdW [Finite K] {h : W K ≃ₗ[K] W K} (hh : h ∈ HdW K) :
    Odd (orderOf h) :=
  Odd.of_dvd_nat odd_card_sub_one (orderOf_dvd_of_pow_eq_one (pow_card_sub_one_of_diag hh.2))

end CFSG.RankThree.GF2n.Smith81.D6Normalizer
