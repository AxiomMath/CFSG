module

public import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassDim3Aux
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import CFSG.ClassicalGroups.Orthogonal.Derived

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem owCr_orthRefl_eq_reflect {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) {a : V} (ha : Q a ≠ 0) :
    owCr_orthRefl Q a ha = CFSG.ClassicalGroups.Orthogonal.reflect Q a := by
  ext w
  rw [owCr_orthRefl_apply, CFSG.ClassicalGroups.Orthogonal.reflect_apply ha w]
  rw [show QuadraticMap.polarBilin Q w a = QuadraticMap.polar Q a w by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]]

theorem neg_mem_of_forall_isIsom {Q : QuadraticForm (ZMod p) U} {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : ∀ g, g ∈ J ↔ IsIsom p Q g) :
    (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J := by
  rw [hA]
  intro v
  exact QuadraticMap.map_neg Q v

theorem exists_reflect_of_isRefl_isIsom (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) (hti : IsIsom p Q t) :
    ∃ a : U, Q a ≠ 0 ∧ t = CFSG.ClassicalGroups.Orthogonal.reflect Q a := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨a, ha, hr⟩ := owCr_refl_form Q hQ h2 ht.1 ht.2 hti
  exact ⟨a, ha, hr.trans (owCr_orthRefl_eq_reflect Q ha)⟩

private theorem tableOrth_orthogonal_setup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {a : U} (ha : Q a ≠ 0) :
    ∃ V : Submodule (ZMod p) U,
      (∀ v, v ∈ V ↔ QuadraticMap.polarBilin Q v a = 0) ∧
      Module.finrank (ZMod p) V = Module.finrank (ZMod p) U - 1 ∧
      (QuadraticMap.polarBilin (Q.comp V.subtype)).Nondegenerate ∧
      (Q.comp V.subtype).Nondegenerate ∧ a ∉ V := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  let _ : Invertible (2 : ZMod p) := invertibleOfNonzero h2
  have ha_ne : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  let V : Submodule (ZMod p) U :=
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (Submodule.span (ZMod p) {a})
  have hsym : ∀ x y : U, QuadraticMap.polarBilin Q x y = QuadraticMap.polarBilin Q y x := by
    intro x y
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply]
  have hVmem : ∀ v, v ∈ V ↔ QuadraticMap.polarBilin Q v a = 0 := by
    intro v
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      have h' := h a (Submodule.mem_span_singleton_self a)
      rwa [hsym a v] at h'
    · intro h y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_smul, LinearMap.smul_apply, hsym a v, h, smul_zero]
  have hVfin : Module.finrank (ZMod p) V = Module.finrank (ZMod p) U - 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ (Submodule.span (ZMod p) {a}),
      finrank_span_singleton ha_ne]
  have hVpolar : (QuadraticMap.polarBilin (Q.comp V.subtype)).Nondegenerate :=
    owCr_restrict_nondegenerate Q hQ h2 a ha
  have hVquad : (Q.comp V.subtype).Nondegenerate :=
    (QuadraticMap.nondegenerate_polar_iff).mp hVpolar
  have haV : a ∉ V := by
    intro hmem
    have hp0 := (hVmem a).mp hmem
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self] at hp0
    have h2a : (2 : ZMod p) * Q a = 0 := by simpa [smul_eq_mul] using hp0
    rcases mul_eq_zero.mp h2a with h2' | hQa
    · exact h2 h2'
    · exact ha hQa
  exact ⟨V, hVmem, hVfin, hVpolar, hVquad, haV⟩

private theorem tableOrth_pair_independent {V : Submodule (ZMod p) U} {a w : U}
    (ha_ne : a ≠ 0) (haV : a ∉ V)
    (hw_ne : w ≠ 0) (hwV : w ∈ V) :
    LinearIndependent (ZMod p) ![a, w] := by
  rw [LinearIndependent.pair_iff' ha_ne]
  intro c hc
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hc; exact hw_ne hc.symm
  have hamem : a ∈ V := by
    have heq : a = c⁻¹ • w := by
      rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [heq]; exact V.smul_mem _ hwV
  exact haV hamem

private theorem tableOrth_dim_three_data (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U}
    (hdim : Module.finrank (ZMod p) U = 3) {a : U} (ha : Q a ≠ 0)
    {V : Submodule (ZMod p) U}
    (hVmem : ∀ v, v ∈ V ↔ QuadraticMap.polarBilin Q v a = 0)
    (hVfin : Module.finrank (ZMod p) V = Module.finrank (ZMod p) U - 1)
    (hVpolar : (QuadraticMap.polarBilin (Q.comp V.subtype)).Nondegenerate)
    (hVquad : (Q.comp V.subtype).Nondegenerate) (haV : a ∉ V) :
    ∃ (z w : U) (ν : ZMod p), ¬ IsSquare ν ∧ Q z ≠ 0 ∧
      QuadraticMap.polarBilin Q z a = 0 ∧ Q w = -ν / Q a ∧
      QuadraticMap.polarBilin Q z w = 0 ∧ QuadraticMap.polar Q a w = 0 ∧
      LinearIndependent (ZMod p) ![a, w] := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have ha_ne : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  have hVdim2 : Module.finrank (ZMod p) V = 2 := by omega
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp
  have : Fintype (ZMod p) := ZMod.fintype p
  let _ : NeZero (2 : ZMod p) := ⟨h2⟩
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare
    (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp)
  have hν0 : ν ≠ 0 := fun h => hν ⟨0, by rw [h]; ring⟩
  have ht : (-ν / Q a) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hν0) ha
  obtain ⟨w, hwQ⟩ := owD3_binary_represents (K := ZMod p) hodd (Q.comp V.subtype) hVpolar
    hVdim2 (-ν / Q a) ht
  have hwQ' : Q (w : U) = -ν / Q a := hwQ
  have hwQne : Q (w : U) ≠ 0 := by rw [hwQ']; exact ht
  have hw_ne : (w : U) ≠ 0 := fun h => hwQne (by rw [h, QuadraticMap.map_zero])
  have hVrank2 : 2 ≤ Module.finrank (ZMod p) V := by omega
  obtain ⟨z, hzorth, hzQ⟩ := QuadraticMap.exists_orthogonal_anisotropic
    (Q.comp V.subtype) hVquad hVrank2 hwQne
  have hza : QuadraticMap.polarBilin Q (z : U) a = 0 := (hVmem z).mp z.2
  have hzw : QuadraticMap.polarBilin Q (z : U) (w : U) = 0 := by
    have h := (QuadraticMap.isOrtho_polarBilin (Q := Q.comp V.subtype)).mpr hzorth
    rwa [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply] at h
  have hBaw : QuadraticMap.polar Q a (w : U) = 0 := by
    rw [QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]
    exact (hVmem w).mp w.2
  have haw_ind := tableOrth_pair_independent ha_ne haV hw_ne w.2
  exact ⟨z, w, ν, hν, hzQ, hza, hwQ', hzw, hBaw, haw_ind⟩

private theorem tableOrth_ker_polar_eq_span [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {z a w : U} (hz : Q z ≠ 0) (hza : QuadraticMap.polarBilin Q z a = 0)
    (hzw : QuadraticMap.polarBilin Q z w = 0) (hdim : Module.finrank (ZMod p) U = 3)
    (hind : LinearIndependent (ZMod p) ![a, w]) :
    LinearMap.ker (QuadraticMap.polarBilin Q z) =
      Submodule.span (ZMod p) ({a, w} : Set U) := by
  have hz_ne : z ≠ 0 := fun h => hz (by rw [h, QuadraticMap.map_zero])
  have hker : LinearMap.ker (QuadraticMap.polarBilin Q z) =
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
        (Submodule.span (ZMod p) {z}) := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_smul, LinearMap.smul_apply, h, smul_zero]
    · intro h
      have hz0 := h z (Submodule.mem_span_singleton_self z)
      simpa using hz0
  have hfin : Module.finrank (ZMod p)
      (LinearMap.ker (QuadraticMap.polarBilin Q z)) = 2 := by
    rw [hker, LinearMap.BilinForm.finrank_orthogonal hQ (Submodule.span (ZMod p) {z}),
      finrank_span_singleton hz_ne, hdim]
  have hle : Submodule.span (ZMod p) ({a, w} : Set U) ≤
      LinearMap.ker (QuadraticMap.polarBilin Q z) := by
    rw [Submodule.span_le]
    rintro x (hx | hx)
    · exact hx ▸ hza
    · exact hx ▸ hzw
  have hspanfin : Module.finrank (ZMod p)
      (Submodule.span (ZMod p) ({a, w} : Set U)) = 2 := by
    have hrange : Set.range ![a, w] = ({a, w} : Set U) := by
      ext x; constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [← hrange, finrank_span_eq_card hind]
    simp
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hspanfin, hfin])).symm

private theorem tableOrth_aniso_span_pair {Q : QuadraticForm (ZMod p) U} {a w z : U}
    {ν : ZMod p} (ha : Q a ≠ 0) (hν : ¬ IsSquare ν) (hwQ : Q w = -ν / Q a)
    (hBaw : QuadraticMap.polar Q a w = 0)
    (hker : LinearMap.ker (QuadraticMap.polarBilin Q z) =
      Submodule.span (ZMod p) ({a, w} : Set U)) :
    ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0 := by
  intro v hv hQv
  have hvspan : v ∈ Submodule.span (ZMod p) ({a, w} : Set U) := by
    rw [← hker]; exact hv
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hvspan
  have hQvαβ : Q (α • a + β • w) = α ^ 2 * Q a + β ^ 2 * Q w := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hBaw, smul_zero, smul_zero,
      add_zero, smul_eq_mul, smul_eq_mul]
    ring
  have hmain : α ^ 2 * Q a + β ^ 2 * (-ν / Q a) = 0 := by
    rw [← hwQ, ← hQvαβ, hαβ]; exact hQv
  have hkey : (α * Q a) ^ 2 = β ^ 2 * ν := by
    have hmul := congrArg (fun t : ZMod p => t * Q a) hmain
    field_simp [ha] at hmul
    linear_combination hmul
  by_cases hβ : β = 0
  · have hα : α = 0 := by
      have h0 : (α * Q a) ^ 2 = 0 := by simpa [hβ] using hkey
      rcases mul_eq_zero.mp (sq_eq_zero_iff.mp h0) with h | h
      · exact h
      · exact absurd h ha
    rw [hα, hβ, zero_smul, zero_smul, add_zero] at hαβ
    exact hαβ.symm
  · refine absurd (⟨α * Q a / β, ?_⟩ : IsSquare ν) hν
    rw [← pow_two, div_pow, hkey]
    field_simp [pow_ne_zero 2 hβ]

theorem exists_hyperplane_of_root (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {a : U} (ha : Q a ≠ 0) :
    ∃ z : U, Q z ≠ 0 ∧ QuadraticMap.polarBilin Q z a = 0 ∧
      (Module.finrank (ZMod p) U = 3 →
        ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0) := by
  rcases lt_or_eq_of_le h3 with h4 | hdim
  · obtain ⟨V, hVmem, hVfin, -, hVquad, -⟩ := tableOrth_orthogonal_setup hp hQ ha
    have hVpos : 0 < Module.finrank (ZMod p) V := by omega
    let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hVpos
    obtain ⟨z, hz⟩ := hVquad.exists_isUnit
    exact ⟨z, isUnit_iff_ne_zero.mp hz, (hVmem z).mp z.2, fun h => by omega⟩
  · have hdim' : Module.finrank (ZMod p) U = 3 := hdim.symm
    obtain ⟨V, hVmem, hVfin, hVpolar, hVquad, haV⟩ :=
      tableOrth_orthogonal_setup hp hQ ha
    obtain ⟨z, w, ν, hν, hz, hza, hwQ, hzw, hBaw, haw_ind⟩ :=
      tableOrth_dim_three_data hp hdim' ha hVmem hVfin hVpolar hVquad haV
    have hker_eq := tableOrth_ker_polar_eq_span hQ hz hza hzw hdim' haw_ind
    exact ⟨z, hz, hza, fun _ => tableOrth_aniso_span_pair ha hν hwQ hBaw hker_eq⟩

private theorem tableOrth_exists_aniso_ne_norm {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    [Module.Finite (ZMod p) W] (h2 : (2 : ZMod p) ≠ 0) {Q : QuadraticForm (ZMod p) W}
    (hQ : Q.Nondegenerate) (hfin : 2 ≤ Module.finrank (ZMod p) W) (c : ZMod p) :
    ∃ w : W, Q w ≠ 0 ∧ Q w ≠ c := by
  let _ : Invertible (2 : ZMod p) := invertibleOfNonzero h2
  obtain ⟨b, hortho, hb⟩ := hQ.exists_orthogonal_basis
  let i0 : Fin (Module.finrank (ZMod p) W) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank (ZMod p) W) := ⟨1, by omega⟩
  by_cases h : Q (b i0) ≠ c
  · exact ⟨b i0, hb i0, h⟩
  · push Not at h
    by_cases h' : Q (b i1) ≠ c
    · exact ⟨b i1, hb i1, h'⟩
    · push Not at h'
      have hc : c ≠ 0 := fun hc0 => hb i0 (by rw [h, hc0])
      have horth : Q.IsOrtho (b i0) (b i1) := hortho i0 i1 (by simp [i0, i1])
      have hsum : Q (b i0 + b i1) = Q (b i0) + Q (b i1) := horth
      refine ⟨b i0 + b i1, ?_, ?_⟩
      · rw [hsum, h, h', ← two_mul]
        exact mul_ne_zero h2 hc
      · rw [hsum, h, h']
        intro hcc
        exact hc (add_left_cancel (a := c) (by rw [hcc, add_zero]))

private theorem tableOrth_step1 {Q : QuadraticForm (ZMod p) U} {z : U}
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b ≠ 0 →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    {X : Submodule (ZMod p) U} (hXinv : ∀ h ∈ B, ∀ x ∈ X, h x ∈ X) :
    ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b ≠ 0 →
      b ∈ X ∨ b ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
  intro b hzb hbQ
  by_cases hbX : b ∈ X
  · exact Or.inl hbX
  · right
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    have hB' : CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B := hB b hzb hbQ
    have hx' : CFSG.ClassicalGroups.Orthogonal.reflect Q b x ∈ X := hXinv _ hB' x hx
    have h1 : x - CFSG.ClassicalGroups.Orthogonal.reflect Q b x ∈ X := X.sub_mem hx hx'
    have hmem : (QuadraticMap.polar Q b x / Q b) • b ∈ X := by
      have h2' := h1
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hbQ x, sub_sub_cancel] at h2'
      exact h2'
    have hzero : QuadraticMap.polar Q b x = 0 := by
      by_contra hne
      have hs : QuadraticMap.polar Q b x / Q b ≠ 0 := div_ne_zero hne hbQ
      have hbX' : b ∈ X := by
        have heq : b = (QuadraticMap.polar Q b x / Q b)⁻¹ •
            ((QuadraticMap.polar Q b x / Q b) • b) := by
          rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
        rw [heq]; exact X.smul_mem _ hmem
      exact hbX hbX'
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact hzero

private theorem tableOrth_span_decomp (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {V X : Submodule (ZMod p) U}
    (hVquad : (Q.comp V.subtype).Nondegenerate) (hXV : X ≤ V)
    (hstep : ∀ b, b ∈ V → Q b ≠ 0 →
      b ∈ X ∨ b ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X) :
    V = X ⊔ (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V) := by
  let _ : Invertible (2 : ZMod p) := invertibleOfNonzero (ZMod.prime_ne_zero p 2 hp)
  obtain ⟨b, -, hb⟩ := hVquad.exists_orthogonal_basis
  have hgen : ∀ i, (b i : U) ∈
      X ⊔ (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V) := by
    intro i
    rcases hstep (b i) (b i).2 (hb i) with h | h
    · exact Submodule.mem_sup_left h
    · exact Submodule.mem_sup_right ⟨h, (b i).2⟩
  have hVeq : V = Submodule.span (ZMod p) (Set.range (fun i => (b i : U))) := by
    conv_lhs => rw [← Submodule.map_subtype_top V]
    rw [← b.span_eq, Submodule.map_span, ← Set.range_comp]
    rfl
  apply le_antisymm
  · conv_lhs => rw [hVeq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hgen i)
  · exact sup_le hXV inf_le_right

private theorem tableOrth_inf_decomp [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {V X : Submodule (ZMod p) U}
    (hVpolar : (QuadraticMap.polarBilin (Q.comp V.subtype)).Nondegenerate)
    (hVspan : V = X ⊔ (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V)) :
    X ⊓ (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V) = ⊥ := by
  have hsym : ∀ x y : U, QuadraticMap.polarBilin Q x y = QuadraticMap.polarBilin Q y x := by
    intro x y
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply]
  rw [Submodule.eq_bot_iff]
  intro u hu
  have huX : u ∈ X := hu.1
  have huXperp : u ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := hu.2.1
  have huV : u ∈ V := hu.2.2
  have hzeroV : (⟨u, huV⟩ : V) = 0 := by
    apply hVpolar.1
    intro w
    have hw : (w : U) ∈
        X ⊔ (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V) := by
      rw [← hVspan]; exact w.2
    rcases Submodule.mem_sup.mp hw with ⟨x, hxX, y, hy, hxy⟩
    have h1 : QuadraticMap.polarBilin Q u x = 0 := by
      have := (LinearMap.BilinForm.mem_orthogonal_iff.mp huXperp) x hxX
      rwa [hsym x u] at this
    have h2 : QuadraticMap.polarBilin Q u y = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hy.1) u huX
    have hcomp : QuadraticMap.polarBilin (Q.comp V.subtype) (⟨u, huV⟩ : V) w
        = QuadraticMap.polarBilin Q u (w : U) := by
      rw [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply]
      rfl
    rw [hcomp, ← hxy, map_add, h1, h2, add_zero]
  have : u = 0 := by
    have := congrArg Subtype.val hzeroV
    simpa using this
  exact this

private theorem tableOrth_inf_perp_decomp [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {V X : Submodule (ZMod p) U}
    (hVpolar : (QuadraticMap.polarBilin (Q.comp V.subtype)).Nondegenerate)
    (hVspan : V = X ⊔ (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V)) :
    (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V) ⊓
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
        (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V) = ⊥ := by
  have hsym : ∀ x y : U, QuadraticMap.polarBilin Q x y = QuadraticMap.polarBilin Q y x := by
    intro x y
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply]
  rw [Submodule.eq_bot_iff]
  intro u hu
  have huY : u ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V := hu.1
  have huYperp : u ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V) := hu.2
  have hzeroV : (⟨u, huY.2⟩ : V) = 0 := by
    apply hVpolar.1
    intro w
    have hw : (w : U) ∈
        X ⊔ (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V) := by
      rw [← hVspan]; exact w.2
    rcases Submodule.mem_sup.mp hw with ⟨x, hxX, y, hy, hxy⟩
    have h1 : QuadraticMap.polarBilin Q u x = 0 := by
      have := (LinearMap.BilinForm.mem_orthogonal_iff.mp huY.1) x hxX
      rwa [hsym x u] at this
    have h2 : QuadraticMap.polarBilin Q u y = 0 := by
      have := (LinearMap.BilinForm.mem_orthogonal_iff.mp huYperp) y hy
      rwa [hsym y u] at this
    have hcomp : QuadraticMap.polarBilin (Q.comp V.subtype) (⟨u, huY.2⟩ : V) w
        = QuadraticMap.polarBilin Q u (w : U) := by
      rw [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply]
      rfl
    rw [hcomp, ← hxy, map_add, h1, h2, add_zero]
  have : u = 0 := by
    have := congrArg Subtype.val hzeroV
    simpa using this
  exact this

private theorem tableOrth_quad_nondegenerate_of_inf_perp (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} {X : Submodule (ZMod p) U}
    (hXXperp : X ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X = ⊥) :
    (Q.comp X.subtype).Nondegenerate := by
  let _ : Invertible (2 : ZMod p) := invertibleOfNonzero (ZMod.prime_ne_zero p 2 hp)
  have hsym : ∀ x y : U, QuadraticMap.polarBilin Q x y = QuadraticMap.polarBilin Q y x := by
    intro x y
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply]
  refine (QuadraticMap.nondegenerate_polar_iff).mp ⟨?_, ?_⟩
  · intro x hx
    have hxperp : (x : U) ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      have h := hx ⟨y, hy⟩
      rw [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply] at h
      rw [← hsym (x : U) y]
      simpa only [Submodule.coe_subtype] using h
    have : (x : U) ∈ X ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X :=
      ⟨x.2, hxperp⟩
    have : (x : U) = 0 := by rwa [hXXperp] at this
    exact Subtype.ext this
  · intro y hy
    have hyperp : (y : U) ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro x hx
      have h := hy ⟨x, hx⟩
      rw [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply] at h
      simpa only [Submodule.coe_subtype] using h
    have : (y : U) ∈ X ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X :=
      ⟨y.2, hyperp⟩
    have : (y : U) = 0 := by rwa [hXXperp] at this
    exact Subtype.ext this

private theorem tableOrth_aniso_pair (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {V X : Submodule (ZMod p) U}
    (hXquad : (Q.comp X.subtype).Nondegenerate)
    (hYquad :
      (Q.comp (LinearMap.BilinForm.orthogonal
        (QuadraticMap.polarBilin Q) X ⊓ V).subtype).Nondegenerate)
    (hXXperp : X ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X = ⊥)
    (hXne : X ≠ ⊥) (hYne : LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V ≠ ⊥) :
    ∃ (x : X) (y : ↥(LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V)),
      Q (x : U) ≠ 0 ∧ Q (y : U) ≠ 0 ∧ (y : U) ∈ V ∧ (y : U) ≠ 0 ∧
      (x : U) ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ∧
      (y : U) ∉ X := by
  let _ : Invertible (2 : ZMod p) := invertibleOfNonzero (ZMod.prime_ne_zero p 2 hp)
  have hXpos : 0 < Module.finrank (ZMod p) X := by
    have := (Submodule.one_le_finrank_iff).mpr hXne
    omega
  have hYpos :
      0 < Module.finrank (ZMod p)
        ↥(LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V) := by
    have := (Submodule.one_le_finrank_iff).mpr hYne
    omega
  obtain ⟨bX, -, hbX⟩ := hXquad.exists_orthogonal_basis
  obtain ⟨bY, -, hbY⟩ := hYquad.exists_orthogonal_basis
  let x : X := bX ⟨0, hXpos⟩
  let y : ↥(LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V) := bY ⟨0, hYpos⟩
  have hxQ : Q (x : U) ≠ 0 := hbX ⟨0, hXpos⟩
  have hyQ : Q (y : U) ≠ 0 := hbY ⟨0, hYpos⟩
  have hyV : (y : U) ∈ V := y.2.2
  have hy0 : (y : U) ≠ 0 := fun h => hyQ (by rw [h, QuadraticMap.map_zero])
  have hx0 : (x : U) ≠ 0 := fun h => hxQ (by rw [h, QuadraticMap.map_zero])
  have hxnotY : (x : U) ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
    intro hxY
    have h1 : (x : U) ∈ X ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X :=
      ⟨x.2, hxY⟩
    have h2 : (x : U) ∈ (⊥ : Submodule (ZMod p) U) := by rwa [hXXperp] at h1
    exact hx0 (by simpa using h2)
  have hynotX : (y : U) ∉ X := by
    intro hyX
    have h1 : (y : U) ∈ X ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X :=
      ⟨hyX, y.2.1⟩
    have h2 : (y : U) ∈ (⊥ : Submodule (ZMod p) U) := by rwa [hXXperp] at h1
    exact hy0 (by simpa using h2)
  exact ⟨x, y, hxQ, hyQ, hyV, hy0, hxnotY, hynotX⟩

private theorem tableOrth_notmem_pair {Q : QuadraticForm (ZMod p) U} {X : Submodule (ZMod p) U}
    (hXXperp : X ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X = ⊥) :
    ∀ (x₀ y₀ : U), x₀ ∈ X →
      y₀ ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X → y₀ ≠ 0 →
      x₀ ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X →
      ∀ t : ZMod p, t ≠ 0 → Q (x₀ + t • y₀) ≠ 0 →
      (x₀ + t • y₀ ∉ X) ∧
        (x₀ + t • y₀ ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X) := by
  intro x₀ y₀ hx₀X hy₀ hy₀ne hx₀ne t ht _
  constructor
  · intro hbX
    have hmem : t • y₀ ∈ X := by
      have h := X.sub_mem hbX hx₀X
      rwa [add_sub_cancel_left] at h
    have hy₀X : y₀ ∈ X := by
      have := X.smul_mem t⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
    have h1 : y₀ ∈ X ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X :=
      ⟨hy₀X, hy₀⟩
    have h2 : y₀ ∈ (⊥ : Submodule (ZMod p) U) := by rwa [hXXperp] at h1
    exact hy₀ne (by simpa using h2)
  · intro hbY
    have hty : t • y₀ ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X :=
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X).smul_mem t hy₀
    have hx₀Y : x₀ ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
      have heq : x₀ = (x₀ + t • y₀) - t • y₀ := by abel
      rw [heq]
      exact (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X).sub_mem hbY hty
    exact hx₀ne hx₀Y

private theorem tableOrth_contra_large_left (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {V X : Submodule (ZMod p) U}
    (hstep : ∀ b, b ∈ V → Q b ≠ 0 →
      b ∈ X ∨ b ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X)
    (hnotmem : ∀ (x₀ y₀ : U), x₀ ∈ X →
      y₀ ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X → y₀ ≠ 0 →
      x₀ ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X →
      ∀ t : ZMod p, t ≠ 0 → Q (x₀ + t • y₀) ≠ 0 →
      (x₀ + t • y₀ ∉ X) ∧
        (x₀ + t • y₀ ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X))
    (hXquad : (Q.comp X.subtype).Nondegenerate) (hXdim : 2 ≤ Module.finrank (ZMod p) X)
    (hXXperp : X ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X = ⊥)
    (hXV : X ≤ V)
    {y : ↥(LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V)}
    (hyQ : Q (y : U) ≠ 0) (hyV : (y : U) ∈ V) : False := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨x', hx'Q, hx'ne⟩ := tableOrth_exists_aniso_ne_norm h2 hXquad hXdim (-Q (y : U))
  have hx'0 : (x' : U) ≠ 0 := fun h => hx'Q (by rw [show x' = 0 from Subtype.ext h, map_zero])
  have hx'notY : (x' : U) ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
    intro hxY
    have h1 : (x' : U) ∈ X ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X :=
      ⟨x'.2, hxY⟩
    have h2' : (x' : U) ∈ (⊥ : Submodule (ZMod p) U) := by rwa [hXXperp] at h1
    exact hx'0 (by simpa using h2')
  have hy0 : (y : U) ≠ 0 := fun h => hyQ (by rw [h, QuadraticMap.map_zero])
  have hx'y : QuadraticMap.polar Q (x' : U) (y : U) = 0 := by
    rw [← QuadraticMap.polarBilin_apply_apply]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp y.2.1) (x' : U) x'.2
  have hsumQ : Q ((x' : U) + (y : U)) = Q (x' : U) + Q (y : U) := by
    rw [QuadraticMap.map_add Q, hx'y, add_zero]
  have hbQ : Q ((x' : U) + (y : U)) ≠ 0 := by
    rw [hsumQ]
    intro h0
    exact hx'ne (eq_neg_of_add_eq_zero_left h0)
  have hbV : (x' : U) + (y : U) ∈ V := V.add_mem (hXV x'.2) hyV
  have hbQ1 : Q ((x' : U) + (1 : ZMod p) • (y : U)) ≠ 0 := by simpa using hbQ
  have hbv1 : (x' : U) + (1 : ZMod p) • (y : U) ∈ V := by simpa using hbV
  have hnot := hnotmem (x' : U) (y : U) x'.2 y.2.1 hy0 hx'notY 1 (by norm_num) hbQ1
  rcases hstep ((x' : U) + (1 : ZMod p) • (y : U)) hbv1 hbQ1 with h | h
  · exact hnot.1 h
  · exact hnot.2 h

private theorem tableOrth_contra_large_right (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {V X : Submodule (ZMod p) U}
    (hstep : ∀ b, b ∈ V → Q b ≠ 0 →
      b ∈ X ∨ b ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X)
    (hnotmem : ∀ (x₀ y₀ : U), x₀ ∈ X →
      y₀ ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X → y₀ ≠ 0 →
      x₀ ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X →
      ∀ t : ZMod p, t ≠ 0 → Q (x₀ + t • y₀) ≠ 0 →
      (x₀ + t • y₀ ∉ X) ∧
        (x₀ + t • y₀ ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X))
    (hYquad :
      (Q.comp (LinearMap.BilinForm.orthogonal
        (QuadraticMap.polarBilin Q) X ⊓ V).subtype).Nondegenerate)
    (hYdim :
      2 ≤ Module.finrank (ZMod p)
        ↥(LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V))
    (hXV : X ≤ V) {x : X}
    (hxnotY : (x : U) ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X) :
    False := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨y', hy'Q, hy'ne⟩ := tableOrth_exists_aniso_ne_norm h2 hYquad hYdim (-Q (x : U))
  have hy'0 : (y' : U) ≠ 0 := fun h => hy'Q (by rw [show y' = 0 from Subtype.ext h, map_zero])
  have hxy' : QuadraticMap.polar Q (x : U) (y' : U) = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp y'.2.1) (x : U) x.2
    rwa [QuadraticMap.polarBilin_apply_apply] at h
  have hsumQ : Q ((x : U) + (y' : U)) = Q (x : U) + Q (y' : U) := by
    rw [QuadraticMap.map_add Q, hxy', add_zero]
  have hbQ : Q ((x : U) + (y' : U)) ≠ 0 := by
    rw [hsumQ]
    intro h0
    exact hy'ne (eq_neg_of_add_eq_zero_right h0)
  have hbV : (x : U) + (y' : U) ∈ V := V.add_mem (hXV x.2) y'.2.2
  have hbQ1 : Q ((x : U) + (1 : ZMod p) • (y' : U)) ≠ 0 := by simpa using hbQ
  have hbv1 : (x : U) + (1 : ZMod p) • (y' : U) ∈ V := by simpa using hbV
  have hnot := hnotmem (x : U) (y' : U) x.2 y'.2.1 hy'0 hxnotY 1 (by norm_num) hbQ1
  rcases hstep ((x : U) + (1 : ZMod p) • (y' : U)) hbv1 hbQ1 with h | h
  · exact hnot.1 h
  · exact hnot.2 h

private theorem tableOrth_contra_large (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {V X : Submodule (ZMod p) U}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (hstep : ∀ b, b ∈ V → Q b ≠ 0 →
      b ∈ X ∨ b ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X)
    (hnotmem : ∀ (x₀ y₀ : U), x₀ ∈ X →
      y₀ ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X → y₀ ≠ 0 →
      x₀ ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X →
      ∀ t : ZMod p, t ≠ 0 → Q (x₀ + t • y₀) ≠ 0 →
      (x₀ + t • y₀ ∉ X) ∧
        (x₀ + t • y₀ ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X))
    (hXquad : (Q.comp X.subtype).Nondegenerate)
    (hYquad :
      (Q.comp (LinearMap.BilinForm.orthogonal
        (QuadraticMap.polarBilin Q) X ⊓ V).subtype).Nondegenerate)
    (hVfin : Module.finrank (ZMod p) V = Module.finrank (ZMod p) U - 1)
    (hXV : X ≤ V) (hXXperp : X ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X = ⊥)
    (hVspan : V = X ⊔ (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V))
    (hXY : X ⊓ (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V) = ⊥)
    {x : X} {y : ↥(LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V)}
    (hyQ : Q (y : U) ≠ 0) (hyV : (y : U) ∈ V)
    (hxnotY : (x : U) ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X) : False := by
  have hfinXY : Module.finrank (ZMod p) X +
      Module.finrank (ZMod p) ↥(LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V)
      = Module.finrank (ZMod p) V := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq X
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V)
    rw [← hVspan, hXY, finrank_bot, add_zero] at h
    exact h.symm
  have hVfin3 : 3 ≤ Module.finrank (ZMod p) V := by omega
  have hcases : 2 ≤ Module.finrank (ZMod p) X ∨
      2 ≤ Module.finrank (ZMod p)
        ↥(LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V) := by
    by_contra h
    push Not at h
    omega
  rcases hcases with hXdim | hYdim
  · exact tableOrth_contra_large_left hp hstep hnotmem hXquad hXdim hXXperp hXV hyQ hyV
  · exact tableOrth_contra_large_right hp hstep hnotmem hYquad hYdim hXV hxnotY

private theorem tableOrth_contra_aniso {Q : QuadraticForm (ZMod p) U} {z : U}
    {V X : Submodule (ZMod p) U}
    (hstep : ∀ b, b ∈ V → Q b ≠ 0 →
      b ∈ X ∨ b ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X)
    (hnotmem : ∀ (x₀ y₀ : U), x₀ ∈ X →
      y₀ ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X → y₀ ≠ 0 →
      x₀ ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X →
      ∀ t : ZMod p, t ≠ 0 → Q (x₀ + t • y₀) ≠ 0 →
      (x₀ + t • y₀ ∉ X) ∧
        (x₀ + t • y₀ ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X))
    (haniso : ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0)
    (hVz : ∀ b, b ∈ V → QuadraticMap.polarBilin Q z b = 0) (hXV : X ≤ V)
    {x : X} {y : ↥(LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V)}
    (hyQ : Q (y : U) ≠ 0) (hyV : (y : U) ∈ V)
    (hxnotY : (x : U) ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X)
    (hynotX : (y : U) ∉ X) : False := by
  have hy0 : (y : U) ≠ 0 := fun h => hyQ (by rw [h, QuadraticMap.map_zero])
  have hb0 : (x : U) + (y : U) ≠ 0 := by
    intro h0
    apply hynotX
    have : (y : U) = - (x : U) := eq_neg_of_add_eq_zero_right h0
    rw [this]; exact X.neg_mem x.2
  have hbV : (x : U) + (y : U) ∈ V := V.add_mem (hXV x.2) hyV
  have hbVker : QuadraticMap.polarBilin Q z ((x : U) + (y : U)) = 0 := hVz _ hbV
  have hbQ : Q ((x : U) + (y : U)) ≠ 0 := fun hQb => hb0 (haniso _ hbVker hQb)
  have hbQ1 : Q ((x : U) + (1 : ZMod p) • (y : U)) ≠ 0 := by simpa using hbQ
  have hbv1 : (x : U) + (1 : ZMod p) • (y : U) ∈ V := by simpa using hbV
  have hnot := hnotmem (x : U) (y : U) x.2 y.2.1 hy0 hxnotY 1 (by norm_num) hbQ1
  rcases hstep ((x : U) + (1 : ZMod p) • (y : U)) hbv1 hbQ1 with h | h
  · exact hnot.1 h
  · exact hnot.2 h

private theorem tableOrth_irred_of_decomp (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {z : U} {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b ≠ 0 →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    (hdim : 4 ≤ Module.finrank (ZMod p) U ∨
      ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0)
    {V : Submodule (ZMod p) U} (hVz : ∀ b, b ∈ V → QuadraticMap.polarBilin Q z b = 0)
    (hVpolar : (QuadraticMap.polarBilin (Q.comp V.subtype)).Nondegenerate)
    (hVquad : (Q.comp V.subtype).Nondegenerate)
    (hVfin : Module.finrank (ZMod p) V = Module.finrank (ZMod p) U - 1) :
    IrredOnSection B ⊥ V := by
  intro X _ hXV hXinv
  by_cases hXbot : X = ⊥
  · exact Or.inl hXbot
  right
  by_contra hXV'
  let Xperp : Submodule (ZMod p) U := LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X
  have hstep1 := tableOrth_step1 hB hXinv
  have hstepV : ∀ b, b ∈ V → Q b ≠ 0 →
      b ∈ X ∨ b ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X :=
    fun b hb hbQ => hstep1 b (hVz b hb) hbQ
  have hVspan := tableOrth_span_decomp hp hVquad hXV hstepV
  have hXY := tableOrth_inf_decomp hVpolar hVspan
  have hYYperp := tableOrth_inf_perp_decomp hVpolar hVspan
  have hXXperp : X ⊓ Xperp = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : u ∈ X ⊓ (Xperp ⊓ V) := ⟨hu.1, hu.2, hXV hu.1⟩
    rwa [hXY] at this
  have hXquad := tableOrth_quad_nondegenerate_of_inf_perp hp hXXperp
  have hYquad := tableOrth_quad_nondegenerate_of_inf_perp hp hYYperp
  have hYne : Xperp ⊓ V ≠ ⊥ := by
    intro hbot
    apply hXV'
    rw [hVspan, hbot, sup_bot_eq]
  have hnotmem := tableOrth_notmem_pair hXXperp
  obtain ⟨x, y, hxQ, hyQ, hyV, hy0, hxnotY, hynotX⟩ :=
    tableOrth_aniso_pair hp hXquad hYquad hXXperp hXbot hYne
  rcases hdim with h4 | haniso
  · exact tableOrth_contra_large hp h4 hstepV hnotmem hXquad hYquad hVfin hXV hXXperp hVspan hXY
      hyQ hyV hxnotY
  · exact tableOrth_contra_aniso hstepV hnotmem haniso hVz hXV hyQ hyV hxnotY hynotX

theorem irredOnSection_of_reflect_mem (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {z : U}
    (hz : Q z ≠ 0) {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b ≠ 0 →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    (hdim : 4 ≤ Module.finrank (ZMod p) U ∨
      ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0) :
    IrredOnSection B ⊥ (LinearMap.ker (QuadraticMap.polarBilin Q z)) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  let _ : Invertible (2 : ZMod p) := invertibleOfNonzero h2
  have hz_ne : z ≠ 0 := fun h => hz (by rw [h, QuadraticMap.map_zero])
  let V : Submodule (ZMod p) U :=
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (Submodule.span (ZMod p) {z})
  have hVz : ∀ b, b ∈ V → QuadraticMap.polarBilin Q z b = 0 := by
    intro b hb
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hb) z
      (Submodule.mem_span_singleton_self z)
  have hVpolar : (QuadraticMap.polarBilin (Q.comp V.subtype)).Nondegenerate :=
    owCr_restrict_nondegenerate Q hQ h2 z hz
  have hVquad : (Q.comp V.subtype).Nondegenerate :=
    (QuadraticMap.nondegenerate_polar_iff).mp hVpolar
  have hVfin : Module.finrank (ZMod p) V = Module.finrank (ZMod p) U - 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ (Submodule.span (ZMod p) {z}),
      finrank_span_singleton hz_ne]
  have hHV : LinearMap.ker (QuadraticMap.polarBilin Q z) = V := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_smul, LinearMap.smul_apply, h, smul_zero]
    · intro h
      have hz0 := h z (Submodule.mem_span_singleton_self z)
      simpa using hz0
  rw [hHV]
  exact tableOrth_irred_of_decomp hp hB hdim hVz hVpolar hVquad hVfin
private theorem tableOrth_ker_isCompl_span (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {z : U}
    (hz : Q z ≠ 0) :
    IsCompl (LinearMap.ker (QuadraticMap.polarBilin Q z)) (Submodule.span (ZMod p) {z}) ∧
      Module.finrank (ZMod p) (LinearMap.ker (QuadraticMap.polarBilin Q z)) =
        Module.finrank (ZMod p) U - 1 := by
  have hz_ne : z ≠ 0 := fun h => hz (by rw [h, QuadraticMap.map_zero])
  let W : Submodule (ZMod p) U := LinearMap.ker (QuadraticMap.polarBilin Q z)
  have hWorth : W = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
      (Submodule.span (ZMod p) {z}) := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_smul, LinearMap.smul_apply, h, smul_zero]
    · intro h
      have hz0 := h z (Submodule.mem_span_singleton_self z)
      simpa using hz0
  have hWfin : Module.finrank (ZMod p) W = Module.finrank (ZMod p) U - 1 := by
    rw [hWorth, LinearMap.BilinForm.finrank_orthogonal hQ (Submodule.span (ZMod p) {z}),
      finrank_span_singleton hz_ne]
  have hinf : W ⊓ Submodule.span (ZMod p) {z} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro w ⟨hwW, hwZ⟩
    rw [hWorth] at hwW
    have hwW' : ∀ y ∈ Submodule.span (ZMod p) {z}, QuadraticMap.polarBilin Q y w = 0 :=
      LinearMap.BilinForm.mem_orthogonal_iff.mp hwW
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hwZ
    have hQzz : QuadraticMap.polarBilin Q z z = 2 * Q z := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
      ring
    have h0 := hwW' z (Submodule.mem_span_singleton_self z)
    rw [map_smul, hQzz, smul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with hc | h2Q
    · rw [hc, zero_smul]
    · exact absurd h2Q (mul_ne_zero (ZMod.prime_ne_zero p 2 hp) hz)
  have htop : Module.finrank (ZMod p) ↥(W ⊔ Submodule.span (ZMod p) {z}) =
      Module.finrank (ZMod p) U := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span (ZMod p) {z})
    rw [hinf, finrank_bot, add_zero, hWfin, finrank_span_singleton hz_ne] at h
    omega
  exact ⟨IsCompl.of_le (le_of_eq hinf)
    (le_of_eq (Submodule.eq_top_of_finrank_eq htop).symm), hWfin⟩

private theorem tableOrth_refl_mem_fixReflSubgroup (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : ∀ g, g ∈ J ↔ IsIsom p Q g) {z : U} :
    ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b ≠ 0 →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ fixReflSubgroup p J z := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hsym : ∀ x y : U, QuadraticMap.polarBilin Q x y = QuadraticMap.polarBilin Q y x := by
    intro x y
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply]
  intro b hzb hbQ
  refine mem_fixReflSubgroup ((hA _).mpr (fun v => CFSG.ClassicalGroups.Orthogonal.map_of_mem
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q b) v)) ?_ ?_
  · rw [← owCr_orthRefl_eq_reflect Q hbQ]
    refine ⟨owCc_orthRefl_mul_self Q b hbQ, ?_⟩
    rw [owCc_orthRefl_range Q b hbQ h2]
    exact finrank_span_singleton (fun h => hbQ (by rw [h, QuadraticMap.map_zero]))
  · exact CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (by
      rw [← QuadraticMap.polarBilin_apply_apply, hsym b z]; exact hzb)

private theorem tableOrth_fixRefl_fix_inv {Q : QuadraticForm (ZMod p) U}
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hA : ∀ g, g ∈ J ↔ IsIsom p Q g) (z : U) :
    (∀ h ∈ fixReflSubgroup p J z, ∀ w ∈ Submodule.span (ZMod p) {z}, h w = w) ∧
      (∀ h ∈ fixReflSubgroup p J z,
        ∀ w ∈ LinearMap.ker (QuadraticMap.polarBilin Q z),
          h w ∈ LinearMap.ker (QuadraticMap.polarBilin Q z)) := by
  constructor
  · intro h hh w hw
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    rw [map_smul, fixReflSubgroup_apply_eq hh]
  · intro h hh w hw
    have hhJ : h ∈ J := fixReflSubgroup_le J z hh
    have hisom : IsIsom p Q h := (hA h).mp hhJ
    have hhz : h z = z := fixReflSubgroup_apply_eq hh
    have hw' : QuadraticMap.polarBilin Q z w = 0 := hw
    have hpol := owCr_polarBilin_isom Q h hisom z w
    rw [hhz] at hpol
    change QuadraticMap.polarBilin Q z (h w) = 0
    rw [hpol, hw']

private theorem tableOrth_fixRefl_hirr (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} {z : U} (hz : Q z ≠ 0)
    (hzaniso : Module.finrank (ZMod p) U = 3 →
      ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0)
    (hBmem : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b ≠ 0 →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ fixReflSubgroup p J z) :
    IrredOnSection (fixReflSubgroup p J z) ⊥ (LinearMap.ker (QuadraticMap.polarBilin Q z)) := by
  have hhdim : 4 ≤ Module.finrank (ZMod p) U ∨
      ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0 := by
    by_cases hm : Module.finrank (ZMod p) U = 3
    · exact Or.inr (hzaniso hm)
    · exact Or.inl (by omega)
  exact irredOnSection_of_reflect_mem hp hQ hz hBmem hhdim

private theorem tableOrth_fixRefl_hne (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    {J : Subgroup (U ≃ₗ[ZMod p] U)} {z a : U} (ha : Q a ≠ 0)
    (hza : QuadraticMap.polarBilin Q z a = 0)
    (hBmem : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b ≠ 0 →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ fixReflSubgroup p J z) :
    ∃ h ∈ fixReflSubgroup p J z,
      ∃ w ∈ LinearMap.ker (QuadraticMap.polarBilin Q z), h w ≠ w := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have ha_ne : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  have hraa : CFSG.ClassicalGroups.Orthogonal.reflect Q a a = -a := by
    rw [← owCr_orthRefl_eq_reflect Q ha]
    exact owCr_orthRefl_self Q a ha
  refine ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q a, hBmem a hza ha, a, hza, ?_⟩
  intro heq
  have haeq : a = -a := by
    rw [← hraa]
    exact heq.symm
  have h2a : (2 : ZMod p) • a = 0 := by
    rw [two_smul]
    nth_rewrite 1 [haeq]
    exact neg_add_cancel a
  exact ha_ne ((smul_eq_zero.mp h2a).resolve_left h2)

theorem throughRefl_orth (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : ∀ g, g ∈ J ↔ IsIsom p Q g) : ThroughRefl p (Module.finrank (ZMod p) U - 1) J := by
  intro r hrJ hrrefl
  obtain ⟨a, ha, hr_eq⟩ := exists_reflect_of_isRefl_isIsom hp hQ hrrefl ((hA r).mp hrJ)
  rw [hr_eq]
  obtain ⟨z, hz, hza, hzaniso⟩ := exists_hyperplane_of_root hp hQ h3 ha
  obtain ⟨hcompl, hWfin⟩ := tableOrth_ker_isCompl_span hp h3 hQ hz
  have hBmem := tableOrth_refl_mem_fixReflSubgroup hp hA (z := z)
  obtain ⟨hfix, hinv⟩ := tableOrth_fixRefl_fix_inv hA z
  have hirr := tableOrth_fixRefl_hirr hp h3 hQ hz hzaniso hBmem
  have hne := tableOrth_fixRefl_hne hp ha hza hBmem
  have hsp := splitSupport_of_isCompl hcompl hfix hinv hirr hne
  rw [hWfin] at hsp
  exact ⟨fixReflSubgroup p J z, fixReflSubgroup_le J z, hBmem a hza ha,
    reflGen_fixReflSubgroup J z, hsp⟩

theorem tableConclusions_orth (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : ∀ g, g ∈ J ↔ IsIsom p Q g) :
    TableConclusions p (Module.finrank (ZMod p) U) J := by
  exact ⟨Or.inl (neg_mem_of_forall_isIsom hA),
    coprimeWitness_of_neg_mem hp (neg_mem_of_forall_isIsom hA),
    throughRefl_orth hp h3 hQ hA⟩

end CFSG.StandardType.ZS
