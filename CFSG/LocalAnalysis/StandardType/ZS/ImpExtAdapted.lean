module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtNonMonomial
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtDeg
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialDMax
import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

@[expose] def AdaptedBasis (H : Subgroup (U ≃ₗ[ZMod p] U))
    (e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    (f : Module.Basis (Fin 4) (ZMod p) U) : Prop :=
  (∃ σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1), ∀ i : Fin 3,
      ∃ x : (ZMod p)ˣ, f i.castSucc = x • (e (σ i) : U)) ∧ f 3 ∈ centralizerSpace H

theorem AdaptedBasis.unitsSMul {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H)}
    {f : Module.Basis (Fin 4) (ZMod p) U} (hf : AdaptedBasis H e f) (w : Fin 4 → (ZMod p)ˣ) :
    AdaptedBasis H e (f.unitsSMul w) := by
  obtain ⟨⟨σ, hσ⟩, h3⟩ := hf
  constructor
  · refine ⟨σ, fun i => ?_⟩
    obtain ⟨x, hx⟩ := hσ i
    refine ⟨w i.castSucc * x, ?_⟩
    rw [Module.Basis.unitsSMul_apply, hx, ← smul_smul]
  · rw [Module.Basis.unitsSMul_apply]
    exact Submodule.smul_mem _ _ h3

namespace ImpExtStd

variable [Module.Finite (ZMod p) U] {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}
  {e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
    (HardMathSupport.Kantor79.commutatorSpace H)}
  {j₀ j₁ : Fin (Module.finrank (ZMod p) U - 1)} {ζ : (ZMod p)ˣ}

private lemma zsna_exists_perm_fin3 :
    ∀ a b : Fin 3, a ≠ b → ∃ π : Equiv.Perm (Fin 3), π 0 = a ∧ π 1 = b := by
  decide +kernel

private lemma zsna_conj_swap_eq_01 {L : ℕ} (σ : Fin 3 ≃ Fin L) {a b : Fin L}
    (h0 : σ 0 = a) (h1 : σ 1 = b) (_hab : a ≠ b) :
    (σ.trans (Equiv.swap a b)).trans σ.symm = Equiv.swap (0 : Fin 3) 1 := by
  ext i
  have h2a : σ 2 ≠ a := by rw [← h0]; exact σ.injective.ne (by decide)
  have h2b : σ 2 ≠ b := by rw [← h1]; exact σ.injective.ne (by decide)
  have hs0 : σ.symm a = 0 := by rw [Equiv.symm_apply_eq, h0]
  have hs1 : σ.symm b = 1 := by rw [Equiv.symm_apply_eq, h1]
  fin_cases i <;>
    simp [hs0, hs1, Equiv.swap_apply_of_ne_of_ne]

private lemma zsna_conj_swap_eq_12 {L : ℕ} (σ : Fin 3 ≃ Fin L) {a b : Fin L}
    (h1 : σ 1 = a) (h2 : σ 2 = b) (_hab : a ≠ b) :
    (σ.trans (Equiv.swap a b)).trans σ.symm = Equiv.swap (1 : Fin 3) 2 := by
  ext i
  have h0a : σ 0 ≠ a := by rw [← h1]; exact σ.injective.ne (by decide)
  have h0b : σ 0 ≠ b := by rw [← h2]; exact σ.injective.ne (by decide)
  have hs1 : σ.symm a = 1 := by rw [Equiv.symm_apply_eq, h1]
  have hs2 : σ.symm b = 2 := by rw [Equiv.symm_apply_eq, h2]
  fin_cases i <;>
    simp [hs1, hs2, Equiv.swap_apply_of_ne_of_ne]

private lemma zsna_castSucc_two : ((2 : Fin 3).castSucc : Fin 4) = 2 := by decide +kernel

private lemma zsna_three_eq_last : (3 : Fin 4) = Fin.last 3 := by decide +kernel

private lemma zsna_three_ne_zero : (3 : Fin 4) ≠ 0 := by decide +kernel

private lemma zsna_three_ne_one : (3 : Fin 4) ≠ 1 := by decide +kernel

private lemma zsna_three_ne_two : (3 : Fin 4) ≠ 2 := by decide +kernel

private lemma zsna_zero_ne_two : (0 : Fin 4) ≠ 2 := by decide +kernel

private lemma zsna_zero_ne_three : (0 : Fin 4) ≠ 3 := by decide +kernel

private lemma zsna_one_ne_two : (1 : Fin 4) ≠ 2 := by decide +kernel

private lemma zsna_one_ne_three : (1 : Fin 4) ≠ 3 := by decide +kernel

private lemma zsna_two_ne_three : (2 : Fin 4) ≠ 3 := by decide +kernel

private lemma zsna_two_ne_zero : (2 : Fin 4) ≠ 0 := by decide +kernel

private lemma zsna_two_ne_one : (2 : Fin 4) ≠ 1 := by decide +kernel

omit [Module.Finite (ZMod p) U] in
private lemma zsna_exists_lift_action (_S : ImpExtStd G H d e j₀ j₁ ζ)
    {f : Module.Basis (Fin 4) (ZMod p) U} (hf₃ : f 3 ∈ centralizerSpace H)
    {x : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H} (hx : x ∈ movedGroup H) :
    ∃ h ∈ H, h (f 3) = f 3 ∧
      ∀ v : HardMathSupport.Kantor79.commutatorSpace H, h (v : U) = (x v : U) := by
  obtain ⟨⟨h, hh⟩, heq⟩ := MonoidHom.mem_range.mp hx
  refine ⟨h, hh, (mem_centralizerSpace.mp hf₃) h hh, ?_⟩
  intro v
  rw [← heq]
  exact (restrictHom_apply H _ _ ⟨h, hh⟩ v).symm

omit [Module.Finite (ZMod p) U] in
theorem dmax_eq_four (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ) (hζ : orderOf ζ = 4) :
    d = 4 := by
  have hD : DMax p (movedGroup H) d :=
    (dmax_movedGroup_iff S.splitSupport d).2 S.dmax_H
  obtain ⟨-, x, hx, y, hy, hxr, hyr, hord⟩ := hD
  have hle : d ≤ 4 := by
    rw [← hord]
    rcases S.mono with hm | hm
    · rw [hm] at hx hy
      exact orderOf_mul_le_four_of_isRefl_gmmn hp e S.ne hζ hx hy hxr hyr
    · rw [hm] at hx hy
      exact orderOf_mul_le_four_of_isRefl_g2mmn hp e S.ne hζ hx hy hxr hyr
  exact le_antisymm hle (Nat.succ_le_of_lt S.three_lt)

omit [Module.Finite (ZMod p) U] in
private lemma zsna_exists_sigma_castSucc (hne : j₀ ≠ j₁)
    (hL : Module.finrank (ZMod p) U - 1 = 3) :
    ∃ σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1), σ 0 = j₀ ∧ σ 1 = j₁ := by
  let φ : Fin (Module.finrank (ZMod p) U - 1) ≃ Fin 3 := finCongr hL
  let a : Fin 3 := φ j₀
  let b : Fin 3 := φ j₁
  have hab : a ≠ b := by
    intro h
    exact hne (φ.injective (by simpa [a, b] using h))
  obtain ⟨π, hπ0, hπ1⟩ := zsna_exists_perm_fin3 a b hab
  refine ⟨π.trans φ.symm, ?_, ?_⟩
  · simp [a, hπ0]
  · simp [b, hπ1]

private lemma zsna_exists_basis_of_sigma (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hn : Module.finrank (ZMod p) U = 4)
    (σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)) :
    ∃ f : Module.Basis (Fin 4) (ZMod p) U,
      (∀ i : Fin 3, f i.castSucc = e (σ i)) ∧ f 3 ∈ centralizerSpace H := by
  have hfin : Module.finrank (ZMod p) (centralizerSpace H) = 1 :=
    ImpExtSetting.finrank_centralizerSpace S.toImpExtSetting
  have hbot : centralizerSpace H ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hfin
    exact zero_ne_one hfin
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let V := HardMathSupport.Kantor79.commutatorSpace H
  have hvnot : v ∉ V := by
    intro hvV
    have hmem : v ∈ V ⊓ centralizerSpace H := ⟨hvV, hv⟩
    rw [S.splitSupport.1.inf_eq_bot] at hmem
    exact hv0 (by simpa using hmem)
  have h1 : LinearIndependent (ZMod p) (fun i : Fin 3 => e (σ i)) :=
    e.linearIndependent.comp σ σ.injective
  have h2 : LinearIndependent (ZMod p) (fun i : Fin 3 => (e (σ i) : U)) := by
    have hmap := h1.map' (Submodule.subtype V) (Submodule.ker_subtype V)
    simpa [Function.comp_def] using hmap
  have hspan : Submodule.span (ZMod p) (Set.range fun i : Fin 3 => (e (σ i) : U)) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (e (σ i)).2
  have hvnotspan : v ∉ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => (e (σ i) : U)) :=
    fun hvs => hvnot (hspan hvs)
  have hlin : LinearIndependent (ZMod p)
      (Fin.snoc (fun i : Fin 3 => (e (σ i) : U)) v) :=
    LinearIndependent.finSnoc h2 hvnotspan
  let f : Module.Basis (Fin 4) (ZMod p) U :=
    basisOfLinearIndependentOfCardEqFinrank hlin (by rw [Fintype.card_fin, hn])
  have hfval : ⇑f = Fin.snoc (fun i : Fin 3 => (e (σ i) : U)) v :=
    coe_basisOfLinearIndependentOfCardEqFinrank hlin _
  refine ⟨f, fun i => ?_, ?_⟩
  · rw [hfval, Fin.snoc_castSucc]
  · rw [hfval, show (3 : Fin 4) = Fin.last 3 from zsna_three_eq_last, Fin.snoc_last]
    exact hv

theorem exists_basis_castSucc (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hn : Module.finrank (ZMod p) U = 4) :
    ∃ (f : Module.Basis (Fin 4) (ZMod p) U) (σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)),
      σ 0 = j₀ ∧ σ 1 = j₁ ∧ (∀ i : Fin 3, f i.castSucc = e (σ i)) ∧
        f 3 ∈ centralizerSpace H := by
  have hL : Module.finrank (ZMod p) U - 1 = 3 := by omega
  obtain ⟨σ, hσ0, hσ1⟩ := zsna_exists_sigma_castSucc S.ne hL
  obtain ⟨f, hf, hf3⟩ := zsna_exists_basis_of_sigma S hn σ
  exact ⟨f, σ, hσ0, hσ1, hf, hf3⟩

omit [Module.Finite (ZMod p) U] in
theorem isMonomialIn_of_mem (S : ImpExtStd G H d e j₀ j₁ ζ) {f : Module.Basis (Fin 4) (ZMod p) U}
    (hf : AdaptedBasis H e f) {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H) : IsMonomialIn f h := by
  obtain ⟨⟨σ, hσ⟩, hfix⟩ := hf
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let φ := restrictHom H V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hmem : φ ⟨h, hh⟩ ∈ movedGroup H := ⟨⟨h, hh⟩, rfl⟩
  have hnormal : ∃ (d : Fin (Module.finrank (ZMod p) U - 1) → (ZMod p)ˣ)
      (τ : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1))),
      φ ⟨h, hh⟩ = diagMap p e d * permMap p e τ := by
    rcases S.mono with hm | hm
    · rw [hm] at hmem
      obtain ⟨d, τ, -, -, heq⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn e S.ne hmem
      exact ⟨d, τ, heq⟩
    · rw [hm] at hmem
      obtain ⟨d, τ, -, -, heq⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn e S.ne hmem
      exact ⟨d, τ, heq⟩
  obtain ⟨d, τ, hdτ⟩ := hnormal
  have hact : ∀ k : Fin (Module.finrank (ZMod p) U - 1),
      h (e k : U) = (d (τ k) : ZMod p) • (e (τ k) : U) := by
    intro k
    have h1 : φ ⟨h, hh⟩ (e k) = (diagMap p e d * permMap p e τ) (e k) := by rw [hdτ]
    have h2 := congrArg (fun w : V => (w : U)) h1
    simpa [φ, restrictHom_apply, LinearEquiv.mul_apply,
      diagMap_apply_basis,
      permMap_apply_basis] using h2
  intro i
  induction i using Fin.lastCases with
  | last =>
      exact ⟨3, 1, by rw [one_smul]; exact (mem_centralizerSpace.mp hfix) h hh⟩
  | cast i =>
      obtain ⟨x, hx⟩ := hσ i
      rw [Units.smul_def] at hx
      let j : Fin 3 := σ.symm (τ (σ i))
      obtain ⟨x', hx'⟩ := hσ j
      rw [Units.smul_def] at hx'
      refine ⟨j.castSucc, (((x * d (τ (σ i)) * x'⁻¹ : (ZMod p)ˣ) : ZMod p)), ?_⟩
      rw [hx, map_smul, hact, hx']
      rw [show (e (τ (σ i)) : U) = (e (σ j) : U) by simp [j]]
      simp only [← Units.smul_def]
      rw [smul_smul, smul_smul]
      congr 1
      group

private lemma zsna_sq_eq_neg_one (hζ : orderOf ζ = 4) :
    ∃ t : ZMod p, t = (ζ : ZMod p) ∧ t ^ 2 = -1 := by
  let t : ZMod p := (ζ : ZMod p)
  have hζ4 : ζ ^ 4 = 1 := by simpa only [hζ] using pow_orderOf_eq_one ζ
  have ht4 : t ^ 4 = 1 := by
    simpa [t] using congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hζ4
  have ht2sq : (t ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
    exact ht4
  have ht2ne : t ^ 2 ≠ 1 := by
    intro h
    have huy : ζ ^ 2 = 1 := by
      apply Units.ext
      simpa [t, Units.val_pow_eq_pow_val] using h
    have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr huy
    rw [hζ] at hdvd
    norm_num at hdvd
  have ht2 : t ^ 2 = -1 := by
    rcases (sq_eq_one_iff (a := t ^ 2)).mp ht2sq with h | h
    · exact absurd h ht2ne
    · exact h
  exact ⟨t, rfl, ht2⟩

omit [Module.Finite (ZMod p) U] in
private lemma zsna_perm_mem_movedGroup (S : ImpExtStd G H d e j₀ j₁ ζ) :
    ∀ τ : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1)), permMap p e τ ∈ movedGroup H := by
  intro τ
  rcases S.mono with hm | hm <;> rw [hm]
  · exact Subgroup.subset_closure (Or.inl (Set.mem_range_self τ))
  · exact Subgroup.subset_closure (Or.inl (Set.mem_range_self τ))

omit [Module.Finite (ZMod p) U] in
private lemma zsna_lift_action (S : ImpExtStd G H d e j₀ j₁ ζ)
    {f : Module.Basis (Fin 4) (ZMod p) U} {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    (hf : ∀ i : Fin 3, f i.castSucc = e (σ i)) (hf₃ : f 3 ∈ centralizerSpace H)
    (x : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H) (hx : x ∈ movedGroup H)
    (π : Equiv.Perm (Fin 3)) (u : Fin 3 → ZMod p)
    (hact : ∀ i : Fin 3,
      x (e (σ i)) = u i • (e (σ (π i)) : HardMathSupport.Kantor79.commutatorSpace H)) :
    ∃ h ∈ H, h (f 3) = f 3 ∧
      ∀ i : Fin 3, h (f i.castSucc) = u i • f (π i).castSucc := by
  obtain ⟨h, hh, hfix, hlift⟩ := zsna_exists_lift_action S hf₃ hx
  refine ⟨h, hh, hfix, fun i => ?_⟩
  rw [hf i, hlift, hact i, hf (π i)]
  simp

omit [Module.Finite (ZMod p) U] in
private lemma zsna_exists_pij_a (S : ImpExtStd G H d e j₀ j₁ ζ)
    {f : Module.Basis (Fin 4) (ZMod p) U} {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁) (hf : ∀ i : Fin 3, f i.castSucc = e (σ i))
    (hf₃ : f 3 ∈ centralizerSpace H) :
    ∃ a ∈ H, LinearMap.toMatrix f f a.toLinearMap = pijMat 0 1 1 := by
  have hσ2ne1 : σ 2 ≠ j₁ := by
    rw [← hσ₁]
    exact σ.injective.ne (by decide)
  have hσ2ne0 : σ 2 ≠ j₀ := by
    rw [← hσ₀]
    exact σ.injective.ne (by decide)
  let τa : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1)) := Equiv.swap j₀ j₁
  let πa : Equiv.Perm (Fin 3) := (σ.trans τa).trans σ.symm
  have hπa : πa = Equiv.swap (0 : Fin 3) 1 :=
    zsna_conj_swap_eq_01 σ hσ₀ hσ₁ S.ne
  have hπa0 : πa 0 = 1 := by rw [hπa]; decide +kernel
  have hπa1 : πa 1 = 0 := by rw [hπa]; decide +kernel
  have hπa2 : πa 2 = 2 := by rw [hπa]; decide +kernel
  have hs0 : σ.symm j₀ = 0 := by rw [Equiv.symm_apply_eq, hσ₀]
  have hs1 : σ.symm j₁ = 1 := by rw [Equiv.symm_apply_eq, hσ₁]
  have hacta : ∀ i : Fin 3, permMap p e τa (e (σ i)) = (1 : ZMod p) • (e (σ (πa i)) : _) := by
    intro i
    rw [permMap_apply_basis, one_smul]
    congr 1
    fin_cases i <;>
      simp [πa, τa, hs0, hs1, hσ₀, hσ₁, hσ2ne0, hσ2ne1,
        Equiv.swap_apply_of_ne_of_ne]
  obtain ⟨a, haH, hfixa, hacta'⟩ :=
    zsna_lift_action S hf hf₃ (permMap p e τa) (zsna_perm_mem_movedGroup S τa) πa
      (fun _ => 1) hacta
  have ha0 : a (f 0) = f 1 := by
    simpa [hπa0, Fin.castSucc_zero, Fin.castSucc_one] using hacta' 0
  have ha1 : a (f 1) = f 0 := by
    simpa [hπa1, Fin.castSucc_zero, Fin.castSucc_one] using hacta' 1
  have ha2 : a (f 2) = f 2 := by simpa [hπa2] using hacta' 2
  refine ⟨a, haH, ?_⟩
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [LinearMap.toMatrix_apply, ha0, ha1, ha2, hfixa, pijMat]

omit [Module.Finite (ZMod p) U] in
private lemma zsna_exists_pij_b (S : ImpExtStd G H d e j₀ j₁ ζ)
    {f : Module.Basis (Fin 4) (ZMod p) U} {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁) (hf : ∀ i : Fin 3, f i.castSucc = e (σ i))
    (hf₃ : f 3 ∈ centralizerSpace H) :
    ∃ b ∈ H, LinearMap.toMatrix f f b.toLinearMap = pijMat 1 2 1 := by
  have hσ2ne1 : σ 2 ≠ j₁ := by
    rw [← hσ₁]
    exact σ.injective.ne (by decide)
  have hσ2ne0 : σ 2 ≠ j₀ := by
    rw [← hσ₀]
    exact σ.injective.ne (by decide)
  have hs0 : σ.symm j₀ = 0 := by rw [Equiv.symm_apply_eq, hσ₀]
  have hs1 : σ.symm j₁ = 1 := by rw [Equiv.symm_apply_eq, hσ₁]
  let τb : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1)) := Equiv.swap j₁ (σ 2)
  let πb : Equiv.Perm (Fin 3) := (σ.trans τb).trans σ.symm
  have hπb : πb = Equiv.swap (1 : Fin 3) 2 :=
    zsna_conj_swap_eq_12 σ hσ₁ rfl (Ne.symm hσ2ne1)
  have hπb0 : πb 0 = 0 := by rw [hπb]; decide +kernel
  have hπb1 : πb 1 = 2 := by rw [hπb]; decide +kernel
  have hπb2 : πb 2 = 1 := by rw [hπb]; decide +kernel
  have hactb : ∀ i : Fin 3, permMap p e τb (e (σ i)) = (1 : ZMod p) • (e (σ (πb i)) : _) := by
    intro i
    rw [permMap_apply_basis, one_smul]
    congr 1
    fin_cases i <;>
      simp [πb, τb, hs1, hσ₀, hσ₁, Ne.symm hσ2ne0, S.ne,
        Equiv.swap_apply_of_ne_of_ne]
  obtain ⟨b, hbH, hfixb, hactb'⟩ :=
    zsna_lift_action S hf hf₃ (permMap p e τb) (zsna_perm_mem_movedGroup S τb) πb
      (fun _ => 1) hactb
  have hb0 : b (f 0) = f 0 := by
    simpa [hπb0, Fin.castSucc_zero] using hactb' 0
  have hb1 : b (f 1) = f 2 := by
    simpa [hπb1, Fin.castSucc_one] using hactb' 1
  have hb2 : b (f 2) = f 1 := by simpa [hπb2] using hactb' 2
  refine ⟨b, hbH, ?_⟩
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [LinearMap.toMatrix_apply, hb0, hb1, hb2, hfixb, pijMat]

private def zsna_piC : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 1

private def zsna_uC (z : (ZMod p)ˣ) (t : ZMod p) : Fin 3 → ZMod p :=
  Fin.cases ((z⁻¹ : (ZMod p)ˣ) : ZMod p) (Fin.cases t (fun _ => 1))

omit [Module.Finite (ZMod p) U] in
private lemma zsna_c_hact (S : ImpExtStd G H d e j₀ j₁ ζ)
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)} (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁) :
    ∀ i : Fin 3,
      (diagMap p e (pairUnit p j₀ j₁ ζ) * permMap p e (Equiv.swap j₀ j₁)) (e (σ i)) =
        (zsna_uC ζ ((ζ : ZMod p)) i) • e (σ (zsna_piC i)) := by
  let τc : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1)) := Equiv.swap j₀ j₁
  let πc : Equiv.Perm (Fin 3) := zsna_piC
  let t : ZMod p := (ζ : ZMod p)
  let uc : Fin 3 → ZMod p := zsna_uC ζ t
  have hσ2ne1 : σ 2 ≠ j₁ := by
    rw [← hσ₁]
    exact σ.injective.ne (by decide)
  have hσ2ne0 : σ 2 ≠ j₀ := by
    rw [← hσ₀]
    exact σ.injective.ne (by decide)
  have hπc0 : πc 0 = 1 := by decide +kernel
  have hπc1 : πc 1 = 0 := by decide +kernel
  have hπc2 : πc 2 = 2 := by decide +kernel
  have huc0 : uc 0 = ((ζ⁻¹ : (ZMod p)ˣ) : ZMod p) := rfl
  have huc1 : uc 1 = t := rfl
  have huc2 : uc 2 = 1 := rfl
  intro i
  change (diagMap p e (pairUnit p j₀ j₁ ζ) * permMap p e τc) (e (σ i)) =
    uc i • e (σ (πc i))
  fin_cases i <;>
    simp only [πc, τc, uc, t, pairUnit, hσ₀, hσ₁, hσ2ne0, hσ2ne1,
      hπc0, hπc1, hπc2, huc0, huc1, huc2,
      LinearEquiv.mul_apply, diagMap_apply_basis, permMap_apply_basis,
      Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hσ2ne0 hσ2ne1, Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, ↓reduceIte, Ne.symm S.ne, Units.val_one, one_smul]

omit [Module.Finite (ZMod p) U] in
private lemma zsna_c_matrix {f : Module.Basis (Fin 4) (ZMod p) U} {c : U ≃ₗ[ZMod p] U}
    (hc0 : c (f 0) = ((ζ⁻¹ : (ZMod p)ˣ) : ZMod p) • f 1)
    (hc1 : c (f 1) = ((ζ : ZMod p)) • f 0) (hc2 : c (f 2) = f 2)
    (hfixc : c (f 3) = f 3) :
    LinearMap.toMatrix f f c.toLinearMap = pijMat 0 1 ((ζ : ZMod p)) := by
  ext r c'
  fin_cases r <;> fin_cases c' <;>
    simp only [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hc0, hc1, hc2, hfixc,
      pijMat, Module.Basis.repr_self, map_smul, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul, Units.val_inv_eq_inv_val, mul_one, Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, ↓reduceIte, zero_ne_one, one_ne_zero, and_true, and_false, ne_eq,
      not_false_eq_true, not_true_eq_false, mul_zero, zsna_two_ne_zero, zsna_two_ne_one,
      zsna_three_ne_zero, zsna_three_ne_one, zsna_zero_ne_two, zsna_zero_ne_three,
      zsna_one_ne_two, zsna_one_ne_three, zsna_two_ne_three, zsna_three_ne_two]

omit [Module.Finite (ZMod p) U] in
private lemma zsna_exists_pij_c (S : ImpExtStd G H d e j₀ j₁ ζ)
    {f : Module.Basis (Fin 4) (ZMod p) U} {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁) (hf : ∀ i : Fin 3, f i.castSucc = e (σ i))
    (hf₃ : f 3 ∈ centralizerSpace H) :
    ∃ c ∈ H,
      LinearMap.toMatrix f f c.toLinearMap = pijMat 0 1 ((ζ : ZMod p)) := by
  let τc : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1)) := Equiv.swap j₀ j₁
  let πc : Equiv.Perm (Fin 3) := zsna_piC
  let t : ZMod p := (ζ : ZMod p)
  let uc : Fin 3 → ZMod p := zsna_uC ζ t
  have hπc0 : πc 0 = 1 := by decide +kernel
  have hπc1 : πc 1 = 0 := by decide +kernel
  have hπc2 : πc 2 = 2 := by decide +kernel
  have huc0 : uc 0 = ((ζ⁻¹ : (ZMod p)ˣ) : ZMod p) := rfl
  have huc1 : uc 1 = t := rfl
  have huc2 : uc 2 = 1 := rfl
  have hcMem : diagMap p e (pairUnit p j₀ j₁ ζ) * permMap p e τc ∈ movedGroup H := by
    have hd : diagMap p e (pairUnit p j₀ j₁ ζ) ∈ movedGroup H := by
      rcases S.mono with hm | hm
      · rw [hm]
        exact Subgroup.subset_closure (Or.inr rfl)
      · rw [hm]
        exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
    exact Subgroup.mul_mem _ hd (zsna_perm_mem_movedGroup S τc)
  have hactc : ∀ i : Fin 3,
      (diagMap p e (pairUnit p j₀ j₁ ζ) * permMap p e τc) (e (σ i)) =
        uc i • (e (σ (πc i)) : _) := by
    intro i
    simpa only [πc, τc, uc, zsna_piC] using zsna_c_hact S hσ₀ hσ₁ i
  obtain ⟨c, hcH, hfixc, hactc'⟩ :=
    zsna_lift_action S hf hf₃ _ hcMem πc uc hactc
  have hc0 : c (f 0) = ((ζ⁻¹ : (ZMod p)ˣ) : ZMod p) • f 1 := by
    simpa only [hπc0, huc0, Fin.castSucc_zero, Fin.castSucc_one, one_smul] using hactc' 0
  have hc1 : c (f 1) = ((ζ : ZMod p)) • f 0 := by
    simpa only [hπc1, huc1, t, Fin.castSucc_zero, Fin.castSucc_one, one_smul] using hactc' 1
  have hc2 : c (f 2) = f 2 := by
    simpa only [hπc2, huc2, zsna_castSucc_two, one_smul] using hactc' 2
  exact ⟨c, hcH, zsna_c_matrix hc0 hc1 hc2 hfixc⟩

omit [Module.Finite (ZMod p) U] in
private lemma zsna_diag_matrix {f : Module.Basis (Fin 4) (ZMod p) U} {r : U ≃ₗ[ZMod p] U}
    (hr0 : r (f 0) = f 0) (hr1 : r (f 1) = f 1) (hr2 : r (f 2) = -f 2)
    (hfixr : r (f 3) = f 3) :
    LinearMap.toMatrix f f r.toLinearMap = diagSignMat 2 := by
  ext r' c'
  fin_cases r' <;> fin_cases c' <;>
    simp [LinearMap.toMatrix_apply, hr0, hr1, hr2, hfixr, diagSignMat]

omit [Module.Finite (ZMod p) U] in
private lemma zsna_exists_diagSign (S : ImpExtStd G H d e j₀ j₁ ζ)
    {f : Module.Basis (Fin 4) (ZMod p) U} {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁) (hf : ∀ i : Fin 3, f i.castSucc = e (σ i))
    (hf₃ : f 3 ∈ centralizerSpace H) (hg2 : movedGroup H = g2mmn p e j₀ j₁ ζ) :
    ∃ r ∈ H, LinearMap.toMatrix f f r.toLinearMap = diagSignMat 2 := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  have hσ2ne1 : σ 2 ≠ j₁ := by
    rw [← hσ₁]
    exact σ.injective.ne (by decide)
  have hσ2ne0 : σ 2 ≠ j₀ := by
    rw [← hσ₀]
    exact σ.injective.ne (by decide)
  let s : V ≃ₗ[ZMod p] V := diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1)
  have hsMem : s ∈ g2mmn p e j₀ j₁ ζ := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  let τs : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1)) := Equiv.swap j₀ (σ 2)
  let xr : V ≃ₗ[ZMod p] V := permMap p e τs * s * (permMap p e τs)⁻¹
  have hpsMem : permMap p e τs ∈ g2mmn p e j₀ j₁ ζ :=
    Subgroup.subset_closure (Or.inl (Set.mem_range_self τs))
  have hxrMem : xr ∈ movedGroup H := by
    rw [hg2]
    exact (g2mmn p e j₀ j₁ ζ).mul_mem
      ((g2mmn p e j₀ j₁ ζ).mul_mem hpsMem hsMem)
      ((g2mmn p e j₀ j₁ ζ).inv_mem hpsMem)
  let us : Fin 3 → ZMod p := fun i => if i = 2 then -1 else 1
  let dsign : Fin (Module.finrank (ZMod p) U - 1) → (ZMod p)ˣ :=
    fun i => if i = j₀ then -1 else 1
  have hxr_eq : xr = diagMap p e (dsign ∘ τs.symm) := by
    change permMap p e τs * diagMap p e dsign * (permMap p e τs)⁻¹ =
      diagMap p e (dsign ∘ τs.symm)
    rw [permMap_mul_diagMap_mul_inv]
  have hacts : ∀ i : Fin 3, xr (e (σ i)) = us i • (e (σ i) : V) := by
    intro i
    rw [hxr_eq, diagMap_apply_basis]
    fin_cases i <;>
      simp [us, τs, dsign, Function.comp_apply, hσ₀, hσ₁, hσ2ne0,
        Ne.symm S.ne, Ne.symm hσ2ne1, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
  obtain ⟨r, hrH, hfixr, hactr'⟩ :=
    zsna_lift_action S hf hf₃ xr hxrMem (Equiv.refl (Fin 3)) us hacts
  have hr0 : r (f 0) = f 0 := by
    simpa [us, Fin.castSucc_zero] using hactr' 0
  have hr1 : r (f 1) = f 1 := by
    simpa [us, Fin.castSucc_one] using hactr' 1
  have hr2 : r (f 2) = -f 2 := by
    simpa [us, neg_one_smul] using hactr' 2
  exact ⟨r, hrH, zsna_diag_matrix hr0 hr1 hr2 hfixr⟩

omit [Module.Finite (ZMod p) U] in
theorem exists_mem_toMatrix_pijMat (_hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hζ : orderOf ζ = 4) {f : Module.Basis (Fin 4) (ZMod p) U}
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)} (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁)
    (hf : ∀ i : Fin 3, f i.castSucc = e (σ i)) (hf₃ : f 3 ∈ centralizerSpace H) :
    ∃ (t : ZMod p) (a b c : U ≃ₗ[ZMod p] U), t ^ 2 = -1 ∧ a ∈ H ∧ b ∈ H ∧ c ∈ H ∧
      LinearMap.toMatrix f f a.toLinearMap = pijMat 0 1 1 ∧
      LinearMap.toMatrix f f b.toLinearMap = pijMat 1 2 1 ∧
      LinearMap.toMatrix f f c.toLinearMap = pijMat 0 1 t ∧
      (movedGroup H = g2mmn p e j₀ j₁ ζ →
        ∃ r ∈ H, LinearMap.toMatrix f f r.toLinearMap = diagSignMat 2) := by
  obtain ⟨t, ht, ht2⟩ := zsna_sq_eq_neg_one hζ
  obtain ⟨a, haH, haMat⟩ := zsna_exists_pij_a S hσ₀ hσ₁ hf hf₃
  obtain ⟨b, hbH, hbMat⟩ := zsna_exists_pij_b S hσ₀ hσ₁ hf hf₃
  obtain ⟨c, hcH, hcMat0⟩ := zsna_exists_pij_c S hσ₀ hσ₁ hf hf₃
  have hcMat : LinearMap.toMatrix f f c.toLinearMap = pijMat 0 1 t := by
    rw [hcMat0, ← ht]
  exact ⟨t, a, b, c, ht2, haH, hbH, hcH, haMat, hbMat, hcMat, fun hg2 =>
    zsna_exists_diagSign S hσ₀ hσ₁ hf hf₃ hg2⟩

end ImpExtStd

end CFSG.StandardType.ZS

end
