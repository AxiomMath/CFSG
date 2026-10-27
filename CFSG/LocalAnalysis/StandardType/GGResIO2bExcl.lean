module

public import CFSG.LocalAnalysis.StandardType.GGResIO2b
public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.LocalAnalysis.StandardType.GGResIDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrCan
public import CFSG.LocalAnalysis.StandardType.GGCellWitness
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggO2bσ {Λ : Type} {b : Λ} (j₀ j₁ j₂ : {i : Λ // i ≠ b}) : Fin 5 → Option Λ :=
  ![some j₀.1, some j₁.1, some j₂.1, some b, none]

theorem ggIsReflection_ne_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {φ : MulAut ↥Bs} (hr : GGIsReflection p φ) : φ ≠ 1 := by
  rintro rfl
  obtain ⟨-, hc⟩ := hr
  simp only [MulAut.one_apply] at hc
  have hc' : Nat.card {b : ↥Bs // True} * p = Nat.card ↥Bs := by simpa using hc
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)] at hc'
  have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  nlinarith

theorem ggO2bσ_injective {Λ : Type} {b : Λ} {j₀ j₁ j₂ : {i : Λ // i ≠ b}} (h01 : j₀ ≠ j₁)
    (h12 : j₁ ≠ j₂) (h02 : j₀ ≠ j₂) : Function.Injective (ggO2bσ j₀ j₁ j₂) := by
  have e01 : j₀.1 ≠ j₁.1 := fun he => h01 (Subtype.ext he)
  have e12 : j₁.1 ≠ j₂.1 := fun he => h12 (Subtype.ext he)
  have e02 : j₀.1 ≠ j₂.1 := fun he => h02 (Subtype.ext he)
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp [ggO2bσ] at hkl ⊢
  all_goals first
    | exact h01 hkl | exact h01 hkl.symm | exact h12 hkl | exact h12 hkl.symm
    | exact h02 hkl | exact h02 hkl.symm | exact e01 hkl | exact e01 hkl.symm
    | exact e12 hkl | exact e12 hkl.symm | exact e02 hkl | exact e02 hkl.symm
    | exact j₀.2 hkl | exact j₁.2 hkl | exact j₂.2 hkl
    | exact j₀.2 hkl.symm | exact j₁.2 hkl.symm | exact j₂.2 hkl.symm

theorem ggO2bT_get (ver : Bool) (k l : Fin 5) :
    (ggO2bT ver k).get l.castSucc = (ggO2bInt ver k l : ZMod 3) := by
  simp [ggO2bT]

theorem ggO2b_table {Λ : Type} {b : Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod 3) V}
    (ver : Bool) {j₀ j₁ j₂ : {i : Λ // i ≠ b}}
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod 3))
    (hKa : ∀ j : {i : Λ // i ≠ b}, α (some j.1) (h none) = (CK (some j) none : ZMod 3))
    (haK : ∀ j : {i : Λ // i ≠ b}, α none (h (some j.1)) = (CK none (some j) : ZMod 3))
    (haa : α none (h none) = 2) (hCLd : ∀ i, CL i i = 2)
    (c01 : CL j₀ j₁ = -1) (c10 : CL j₁ j₀ = -1) (c12 : CL j₁ j₂ = -1) (c21 : CL j₂ j₁ = -1)
    (c02 : CL j₀ j₂ = 0) (c20 : CL j₂ j₀ = 0) (c1b : CL j₁ b = -1) (cb1 : CL b j₁ = -1)
    (c0b : CL j₀ b = 0) (cb0 : CL b j₀ = 0) (c2b : CL j₂ b = 0) (cb2 : CL b j₂ = 0)
    (k1a : CK (some j₁) none = 0) (ka1 : CK none (some j₁) = 0) (k2a : CK (some j₂) none = 0)
    (ka2 : CK none (some j₂) = 0) (ka0 : CK (some j₀) none = (if ver then -1 else -2))
    (k0a : CK none (some j₀) = (if ver then -2 else -1))
    (hu : α none (h (some b)) = (if ver then 1 else 2))
    (hv : α (some b) (h none) = (if ver then 2 else 1)) :
    GGFTable (RingHom.id (ZMod 3)) (ggO2bT ver) (h ∘ ggO2bσ j₀ j₁ j₂) 0
      (α ∘ ggO2bσ j₀ j₁ j₂) := by
  refine ⟨fun k l => ?_, fun k => by simp [ggO2bT]⟩
  rw [ggO2bT_get, RingHom.id_apply, Function.comp_apply, Function.comp_apply]
  cases ver <;> fin_cases k <;> fin_cases l <;>
    simp [ggO2bσ, ggO2bInt, hL, hKa, haK, haa, hCLd, c01, c10, c12, c21, c02, c20, c1b, cb1, c0b,
      cb0, c2b, cb2, k1a, ka1, k2a, ka2, ka0, k0a, hu, hv]

theorem ggResI_o2b_excl (hFix : GGTBFixInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
      ¬ GGResLeviDatumCell p Bs L J K ggSelI (ggTypRankLt 8)
        (fun b CL CK u v => GGResO2bCell p b CL CK u v) := by
  intro G _ _ p B Bs x L D J y K hH _ hD
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, hWL, hCL, hWK, hCK, htyp, hφ,
    hrefl, hL, hK, hsel, -, -, hAL, hAK, -, hJ, hcell⟩ := hD
  obtain ⟨hp3, j₀, j₁, j₂, h01, h12, h02, hcov, c01, c10, c12, c21, c02, c20, c1b, cb1, c0b, cb0,
    c2b, cb2, k1a, ka1, k2a, ka2, hver⟩ := hcell
  subst hp3
  have hind : LinearIndependent (ZMod 3) h := hsel
  have hspan := ggResI_span_top hFix hH ι hφ hAL hind
  obtain ⟨ver, ka0, k0a, hu, hv⟩ : ∃ ver : Bool,
      CK (some j₀) none = (if ver then -1 else -2) ∧ CK none (some j₀) = (if ver then -2 else -1) ∧
      α none (h (some b)) = (if ver then 1 else 2) ∧ α (some b) (h none) = (if ver then 2 else 1) := by
    rcases hver with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
    · exact ⟨true, by simpa using a1, by simpa using a2, by simpa using a3, by simpa using a4⟩
    · exact ⟨false, by simpa using a1, by simpa using a2, by simpa using a3, by simpa using a4⟩
  set σ := ggO2bσ j₀ j₁ j₂ with hσ
  have hσinj : Function.Injective σ := ggO2bσ_injective h01 h12 h02
  have hσsurj : Function.Surjective σ := by
    rintro (_ | i)
    · exact ⟨4, rfl⟩
    · rcases hcov i with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  have hind' : LinearIndependent (ZMod 3) (h ∘ σ) := hind.comp σ hσinj
  have hspan' : Submodule.span (ZMod 3) (Set.range (h ∘ σ)) = ⊤ := by
    rw [Set.range_comp, hσsurj.range_eq, Set.image_univ, hspan]
  have hKa : ∀ j : {i : Λ // i ≠ b}, α (some j.1) (h none) = (CK (some j) none : ZMod 3) :=
    fun j => hK (some j) none
  have haK : ∀ j : {i : Λ // i ≠ b}, α none (h (some j.1)) = (CK none (some j) : ZMod 3) :=
    fun j => hK none (some j)
  have haa : α none (h none) = 2 := by
    have h1 := hK none none
    rw [hCK.1 none] at h1
    simpa using h1
  have hT' : GGFTable (RingHom.id (ZMod 3)) (ggO2bT ver) (h ∘ σ) 0 (α ∘ σ) :=
    ggO2b_table ver hL hKa haK haa hCL.1 c01 c10 c12 c21 c02 c20 c1b cb1 c0b cb0 c2b cb2 k1a ka1
      k2a ka2 ka0 k0a hu hv
  have hg' : ∀ k w, (fun k => ggLin (p := 3) ι (φ (σ k))) k w = w - (α ∘ σ) k w • (h ∘ σ) k :=
    fun k w => hφ (σ k) w
  have h2' : ∀ k, (α ∘ σ) k ((h ∘ σ) k) = 2 := fun k => by
    rw [hT'.1 k k]
    exact ggO2b_diag ver k
  obtain ⟨hfixL, hpres, hwfix, hnot⟩ := ggResIO2b_linear ver hT' hg' h2' hspan' hind'
  have hnb := hH.2.2.2.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hnb.1.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hKmem : ∀ a : Fin 4, φ (σ (ggO2bβ a)) ∈ ggAutomizer K Bs := by
    intro a
    rw [hAK]
    fin_cases a
    · exact Subgroup.subset_closure (Or.inl ⟨j₀, rfl⟩)
    · exact Subgroup.subset_closure (Or.inl ⟨j₁, rfl⟩)
    · exact Subgroup.subset_closure (Or.inl ⟨j₂, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr rfl)
  have hkill : ∀ c : ↥Bs, K ≤ Subgroup.centralizer ({(c : G)} : Set G) →
      ∀ a : Fin 4, (α ∘ σ) (ggO2bβ a) (ι (Additive.ofMul c)) = 0 := fun c hc a =>
    ggResI_alpha_eq_zero (by decide) (hφ _) (h2' (ggO2bβ a))
      ((ggLin_fix_iff ι _ _).mp (ggResI_automizer_fix c.2 hc _ (hKmem a)))
  set yv : V := ι (Additive.ofMul ⟨y, hyBs⟩) with hyv
  obtain ⟨c₀, hc₀⟩ := hfixL yv (hkill ⟨y, hyBs⟩ hKy)
  have hyv0 : yv ≠ 0 := by
    intro h0
    apply hy1
    have h1 : (⟨y, hyBs⟩ : ↥Bs) = 1 :=
      Additive.ofMul.injective (ι.injective (h0.trans (map_zero ι).symm))
    exact congrArg Subtype.val h1
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₀
    exact hyv0 hc₀
  have hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y := by
    rintro c ⟨hcBs, hcK⟩
    have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcK k hk)
    obtain ⟨c₁, hc₁⟩ := hfixL _ (hkill ⟨c, hcBs⟩ hKc)
    have hcv : ι (Additive.ofMul ⟨c, hcBs⟩) = (c₁ * c₀⁻¹) • yv := by
      rw [hc₁, hc₀, smul_smul, mul_assoc, inv_mul_cancel₀ hc₀0, mul_one]
    have hc' : (⟨c, hcBs⟩ : ↥Bs) = (⟨y, hyBs⟩ : ↥Bs) ^ (c₁ * c₀⁻¹).val := by
      apply Additive.ofMul.injective
      apply ι.injective
      rw [ofMul_pow, map_nsmul, hcv, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
    have hcy : c = y ^ (c₁ * c₀⁻¹).val := by
      have h1 := congrArg Subtype.val hc'
      simpa using h1
    rw [hcy]
    exact Subgroup.npow_mem_zpowers y _
  have hKa' : φ none ∈ ggAutomizer K Bs := hKmem 3
  have hnt : ggAutomizer K Bs ≠ ⊥ := by
    intro hbot
    have h1 := hKa'
    rw [hbot, Subgroup.mem_bot] at h1
    exact ggIsReflection_ne_one (hrefl none) h1
  set ψ : MulAut ↥Bs := (ggO2bW.map fun k => φ (σ k)).prod with hψ
  have hψlin : ggLin (p := 3) ι ψ = (ggO2bW.map fun k => ggLin (p := 3) ι (φ (σ k))).prod := by
    rw [hψ, map_list_prod, List.map_map]
    rfl
  have hψmem : ψ ∈ ggAutomizer ⊤ Bs := by
    have h1 : ψ ∈ Subgroup.closure (Set.range φ) :=
      Subgroup.list_prod_mem _ fun t ht => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp ht
        exact Subgroup.subset_closure ⟨σ k, rfl⟩
    rw [← ggResI_sup_eq_closure hAL hAK] at h1
    exact Subgroup.subset_closure (ggResI_mem_ggInduced_top h1)
  obtain ⟨gw, -, hgN, hgψ⟩ := eq_ggConjAut_of_mem_ggAutomizer hψmem
  have hψy : ggLin (p := 3) ι ψ yv = yv := by
    rw [hψlin, hc₀, map_smul, hwfix]
  have hgy : gw * y * gw⁻¹ = y := by
    have h1 := (ggLin_fix_iff (p := 3) ι ψ ⟨y, hyBs⟩).mpr hψy
    rw [hgψ] at h1
    exact congrArg Subtype.val h1
  have hgK : gw ∈ Subgroup.normalizer (K : Set G) := ggNbr_mem_normalizer hH hCent hnt hgN hgy
  have hcK : ψ * φ none * ψ⁻¹ ∈ ggAutomizer K Bs := by
    obtain ⟨n, hnK, hnN, hn⟩ := mem_ggAutomizer_iff.mp hKa'
    refine Subgroup.subset_closure ⟨gw * n * gw⁻¹, (Subgroup.mem_normalizer_iff.mp hgK n).mp hnK,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hnN) (Subgroup.inv_mem _ hgN), fun c => ?_⟩
    rw [hgψ]
    change gw * ((φ none ((ggConjAut Bs hgN)⁻¹ c) : ↥Bs) : G) * gw⁻¹ = _
    rw [hn]
    change gw * (n * (gw⁻¹ * (c : G) * gw) * n⁻¹) * gw⁻¹ = _
    group
  have hgen : ∀ s ∈ Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none},
      s * s = 1 ∧ ∀ i : Fin 4, ∃ j : Fin 4, ∃ c : ZMod 3,
        ggLin (p := 3) ι s (ggO2bL (h ∘ σ) ver i) = c • ggO2bL (h ∘ σ) ver j := by
    rintro s (⟨j, rfl⟩ | hs)
    · refine ⟨by rw [← pow_two]; exact (hrefl _).1, ?_⟩
      rcases hcov j.1 with he | he | he | he
      · rw [show j = j₀ from Subtype.ext he]; exact hpres 0
      · rw [show j = j₁ from Subtype.ext he]; exact hpres 1
      · rw [show j = j₂ from Subtype.ext he]; exact hpres 2
      · exact absurd he j.2
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact ⟨by rw [← pow_two]; exact (hrefl _).1, hpres 3⟩
  have hpresK : ∀ a ∈ ggAutomizer K Bs, ∀ i : Fin 4, ∃ j : Fin 4, ∃ c : ZMod 3,
      ggLin (p := 3) ι a (ggO2bL (h ∘ σ) ver i) = c • ggO2bL (h ∘ σ) ver j := by
    intro a ha
    rw [hAK] at ha
    induction ha using Subgroup.closure_induction_left with
    | one => exact fun i => ⟨i, 1, by simp⟩
    | mul_left s hs w _ ih =>
      intro i
      obtain ⟨j, c, hj⟩ := ih i
      obtain ⟨k, c', hk⟩ := (hgen s hs).2 j
      exact ⟨k, c * c', by rw [map_mul, LinearEquiv.mul_apply, hj, map_smul, hk, smul_smul]⟩
    | inv_mul_cancel s hs w _ ih =>
      intro i
      have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hgen s hs).1
      obtain ⟨j, c, hj⟩ := ih i
      obtain ⟨k, c', hk⟩ := (hgen s hs).2 j
      exact ⟨k, c * c', by
        rw [hsinv, map_mul, LinearEquiv.mul_apply, hj, map_smul, hk, smul_smul]⟩
  obtain ⟨j, c, hj⟩ := hpresK _ hcK 0
  have hσ4 : σ 4 = none := rfl
  have h1 := hnot j c
  rw [hσ4] at h1
  apply h1
  rw [← hj, map_mul, map_mul, map_inv, hψlin]

end CFSG.StandardType
