module

public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBRealize
import all CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.StandardType

open CFSG.Open
open Module
open scoped IsMulCommutative

section Rank

variable {G : Type} [Group G]

section KeyLemma

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private lemma eq_one_or_eq_neg_one_of_mul_self_eq_one' {x : K} (hx : x * x = 1) :
    x = 1 ∨ x = -1 := by
  have h : (x - 1) * (x + 1) = 0 := by
    have : (x - 1) * (x + 1) = x * x - 1 := by ring
    rw [this, hx, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)

private lemma one_ne_neg_one_of_two_ne_zero (h2 : (2 : K) ≠ 0) : (1 : K) ≠ -1 := by
  intro h
  apply h2
  calc (2 : K) = 1 + 1 := one_add_one_eq_two.symm
    _ = -1 + 1 := by nth_rewrite 1 [h]; rfl
    _ = 0 := neg_add_cancel 1

private lemma eigenspace_one_sup_eigenspace_neg_one_eq_top (h2 : (2 : K) ≠ 0)
    (g : Module.End K V) (hg : g * g = 1) :
    g.eigenspace 1 ⊔ g.eigenspace (-1) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hgv : g (g v) = v := by
    rw [← Module.End.mul_apply, hg, Module.End.one_apply]
  refine Submodule.mem_sup.2 ⟨(2 : K)⁻¹ • (v + g v), ?_,
    (2 : K)⁻¹ • (v - g v), ?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, map_smul, map_add, hgv, one_smul, add_comm (g v) v]
  · rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, hgv, neg_one_smul,
      ← neg_sub v (g v), smul_neg]
  · rw [← smul_add]
    have hsum : (v + g v) + (v - g v) = (2 : K) • v := by
      rw [two_smul]; abel
    rw [hsum, smul_smul, inv_mul_cancel₀ h2, one_smul]

private lemma isCompl_eigenspace_one_eigenspace_neg_one (h2 : (2 : K) ≠ 0)
    (g : Module.End K V) (hg : g * g = 1) :
    IsCompl (g.eigenspace 1) (g.eigenspace (-1)) := by
  rw [isCompl_iff]
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff_inf_le]
    intro v hv
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff] at hv
    rw [Submodule.mem_bot]
    have h1 : v = g v := by rw [hv.1, one_smul]
    have h2' : g v = -v := by rw [hv.2, neg_one_smul]
    have h : v = -v := h1.trans h2'
    have h2v : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h]
      exact neg_add_cancel v
    exact (smul_eq_zero.mp h2v).resolve_left h2
  · rw [codisjoint_iff]
    exact eigenspace_one_sup_eigenspace_neg_one_eq_top h2 g hg

private lemma apply_sub_smul_one_of_mem_eigenspace_one (g : Module.End K V) (μ : K)
    {a : V} (ha : a ∈ g.eigenspace 1) :
    (g - μ • 1) a = (1 - μ) • a := by
  have hga : g a = a := by
    have := Module.End.mem_eigenspace_iff.mp ha
    simpa using this
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hga]
  rw [sub_smul, one_smul]

private lemma apply_sub_smul_one_of_mem_eigenspace_neg_one (g : Module.End K V) (μ : K)
    {a : V} (ha : a ∈ g.eigenspace (-1)) :
    (g - μ • 1) a = (-1 - μ) • a := by
  have hga : g a = -a := by
    have := Module.End.mem_eigenspace_iff.mp ha
    rw [neg_one_smul] at this
    exact this
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hga,
    ← neg_one_smul K a, ← sub_smul]

private lemma pow_apply_eq_pow_smul_of_apply_eq_smul (h : Module.End K V) (c : K) (a : V)
    (ha : h a = c • a) (k : ℕ) : (h ^ k) a = c ^ k • a := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ha, map_smul, ih, smul_smul, pow_succ']

private lemma ker_pow_sub_smul_one_le_ker_sub_smul_one (h2 : (2 : K) ≠ 0)
    (g : Module.End K V) (hg : g * g = 1) (μ : K) (k : ℕ) (hk : 1 ≤ k) :
    LinearMap.ker ((g - μ • 1) ^ k) ≤ LinearMap.ker (g - μ • 1) := by
  have hcompl := isCompl_eigenspace_one_eigenspace_neg_one h2 g hg
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  have hvsup : v ∈ g.eigenspace 1 ⊔ g.eigenspace (-1) := by
    rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvsup
  have hp : ((g - μ • 1) ^ k) a = (1 - μ) ^ k • a :=
    pow_apply_eq_pow_smul_of_apply_eq_smul _
      (1 - μ) a (apply_sub_smul_one_of_mem_eigenspace_one g μ ha) k
  have hq : ((g - μ • 1) ^ k) b = (-1 - μ) ^ k • b :=
    pow_apply_eq_pow_smul_of_apply_eq_smul _
      (-1 - μ) b (apply_sub_smul_one_of_mem_eigenspace_neg_one g μ hb) k
  rw [map_add, hp, hq] at hv
  rw [map_add, apply_sub_smul_one_of_mem_eigenspace_one g μ ha,
    apply_sub_smul_one_of_mem_eigenspace_neg_one g μ hb]
  by_cases hμ1 : 1 - μ = 0
  · have hd : (-1 - μ) ≠ 0 := by
      intro h
      apply h2
      have hh : (1 - μ) - (-1 - μ) = (2 : K) := by ring
      rw [hμ1, h, sub_zero] at hh
      exact hh.symm
    have hc : (1 - μ) ^ k = 0 := by rw [hμ1, zero_pow (by omega)]
    rw [hc, zero_smul, zero_add] at hv
    have hb0 : b = 0 := (smul_eq_zero.mp hv).resolve_left (pow_ne_zero k hd)
    rw [hb0, hμ1]
    simp
  · by_cases hμ2 : -1 - μ = 0
    · have hd : (1 - μ) ^ k ≠ 0 := pow_ne_zero k hμ1
      have hc : (-1 - μ) ^ k = 0 := by rw [hμ2, zero_pow (by omega)]
      rw [hc, zero_smul, add_zero] at hv
      have ha0 : a = 0 := (smul_eq_zero.mp hv).resolve_left hd
      rw [ha0, hμ2]
      simp
    · have hc : (1 - μ) ^ k ≠ 0 := pow_ne_zero k hμ1
      have hd : (-1 - μ) ^ k ≠ 0 := pow_ne_zero k hμ2
      have haeq : a = (-(((1 - μ) ^ k)⁻¹ * (-1 - μ) ^ k)) • b := by
        have h1 : (1 - μ) ^ k • a = -((-1 - μ) ^ k • b) := by
          rw [add_eq_zero_iff_eq_neg] at hv
          exact hv
        calc a = ((1 - μ) ^ k)⁻¹ • ((1 - μ) ^ k • a) := by
              rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
          _ = ((1 - μ) ^ k)⁻¹ • (-((-1 - μ) ^ k • b)) := by rw [h1]
          _ = -(((1 - μ) ^ k)⁻¹ • ((-1 - μ) ^ k • b)) := by rw [smul_neg]
          _ = -((((1 - μ) ^ k)⁻¹ * (-1 - μ) ^ k) • b) := by rw [smul_smul]
          _ = (-(((1 - μ) ^ k)⁻¹ * (-1 - μ) ^ k)) • b := by rw [neg_smul]
      have haq : a ∈ g.eigenspace (-1) := by
        rw [haeq]; exact Submodule.smul_mem _ _ hb
      have ha0 : a = 0 := by
        have : a ∈ (g.eigenspace 1) ⊓ (g.eigenspace (-1)) := Submodule.mem_inf.mpr ⟨ha, haq⟩
        rw [hcompl.inf_eq_bot] at this
        simpa using this
      have hb0 : b = 0 := by
        rw [ha0, smul_zero, zero_add] at hv
        exact (smul_eq_zero.mp hv).resolve_left hd
      rw [ha0, hb0]
      simp

private lemma maxGenEigenspace_eq_eigenspace_of_involution (h2 : (2 : K) ≠ 0)
    (g : Module.End K V) (hg : g * g = 1) (μ : K) :
    g.maxGenEigenspace μ = g.eigenspace μ := by
  ext v
  constructor
  · intro hv
    rw [Module.End.mem_maxGenEigenspace] at hv
    obtain ⟨k, hk⟩ := hv
    rw [Module.End.mem_eigenspace_iff]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [pow_zero, Module.End.one_apply] at hk
      rw [hk]; simp
    · have hmem : v ∈ LinearMap.ker ((g - μ • 1) ^ k) := by
        rw [LinearMap.mem_ker]; exact hk
      have hthis : v ∈ LinearMap.ker (g - μ • 1) :=
        ker_pow_sub_smul_one_le_ker_sub_smul_one h2 g hg μ k hkpos hmem
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, sub_eq_zero] at hthis
      exact hthis
  · intro hv
    exact Module.End.eigenspace_le_maxGenEigenspace hv

private lemma iSup_subtype_ne_bot_eq_iSup {ι : Type*} (W : ι → Submodule K V) :
    (⨆ χ : {χ : ι // W χ ≠ ⊥}, W χ.1) = ⨆ χ : ι, W χ := by
  apply le_antisymm
  · exact iSup_le fun χ => le_iSup W χ.1
  · refine iSup_le fun χ => ?_
    by_cases h : W χ = ⊥
    · rw [h]; exact bot_le
    · exact le_iSup (fun χ : {χ : ι // W χ ≠ ⊥} => W χ.1) ⟨χ, h⟩

private lemma natCard_le_two_pow_finrank_of_commuting_involutions
    {ι : Type*} [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (f : ι → Module.End K V)
    (hf : Function.Injective f) (hcomm : ∀ i j, Commute (f i) (f j))
    (hsq : ∀ i, f i * f i = 1) :
    Nat.card ι ≤ 2 ^ finrank K V := by
  classical
  have hconv : ∀ i (μ : K), (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    fun i μ => maxGenEigenspace_eq_eigenspace_of_involution h2 (f i) (hsq i) μ
  have hmaps : ∀ i j φ, Set.MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ) :=
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have hindmax : iSupIndep fun χ : ι → K => ⨅ i, (f i).maxGenEigenspace (χ i) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hmaps
  have htri : ∀ i, ⨆ μ : K, (f i).maxGenEigenspace μ = ⊤ := by
    intro i
    rw [iSup_congr fun μ => hconv i μ]
    rw [eq_top_iff]
    calc (⊤ : Submodule K V) = (f i).eigenspace 1 ⊔ (f i).eigenspace (-1) :=
          (eigenspace_one_sup_eigenspace_neg_one_eq_top h2 (f i) (hsq i)).symm
      _ ≤ ⨆ μ : K, (f i).eigenspace μ :=
          sup_le (le_iSup (fun μ : K => (f i).eigenspace μ) 1)
                 (le_iSup (fun μ : K => (f i).eigenspace μ) (-1))
  have hspanmax : (⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i)) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun i j _ => hcomm i j) htri
  let W : (ι → K) → Submodule K V := fun χ => ⨅ i, (f i).eigenspace (χ i)
  have hspan : (⨆ χ : ι → K, W χ) = ⊤ := by
    have h := iSup_congr (fun χ : ι → K => iInf_congr (fun i => (hconv i (χ i)).symm))
    rw [← h] at hspanmax
    exact hspanmax
  have hind : iSupIndep W :=
    iSupIndep.mono hindmax fun χ => iInf_mono fun i => Module.End.eigenspace_le_maxGenEigenspace
  let X := {χ : ι → K // W χ ≠ ⊥}
  haveI : Fintype X := hind.fintypeNeBotOfFiniteDimensional
  have hcardX : Fintype.card X ≤ finrank K V := hind.subtype_ne_bot_le_finrank
  have hspanX : (⨆ χ : X, W χ.1) = ⊤ := by
    rw [iSup_subtype_ne_bot_eq_iSup W, hspan]
  have hχsq : ∀ χ : X, ∀ i, χ.1 i * χ.1 i = 1 := by
    intro χ i
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot χ.2
    have hvi : (f i) v = χ.1 i • v :=
      Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv i)
    have hfix : (f i) ((f i) v) = v := by
      rw [← Module.End.mul_apply, hsq i, Module.End.one_apply]
    have hvfix : (χ.1 i * χ.1 i) • v = v := by
      calc (χ.1 i * χ.1 i) • v = χ.1 i • (χ.1 i • v) := (smul_smul _ _ _).symm
        _ = χ.1 i • ((f i) v) := by rw [← hvi]
        _ = (f i) (χ.1 i • v) := (map_smul _ _ _).symm
        _ = (f i) ((f i) v) := by rw [← hvi]
        _ = v := hfix
    have hzero : (χ.1 i * χ.1 i - 1) • v = 0 := by
      rw [sub_smul, one_smul, hvfix, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  have hχval : ∀ χ : X, ∀ i, χ.1 i = 1 ∨ χ.1 i = -1 :=
    fun χ i => eq_one_or_eq_neg_one_of_mul_self_eq_one' (hχsq χ i)
  let Φ : ι → (X → Fin 2) := fun i χ => if χ.1 i = -1 then 1 else 0
  have hΦ : Function.Injective Φ := by
    intro i j hij
    apply hf
    have hpoint : ∀ χ : X, χ.1 i = χ.1 j := by
      intro χ
      have hb : (if χ.1 i = -1 then (1 : Fin 2) else 0) =
          (if χ.1 j = -1 then (1 : Fin 2) else 0) := congrFun hij χ
      rcases hχval χ i with hi | hi <;> rcases hχval χ j with hj | hj
      · rw [hi, hj]
      · exfalso
        rw [hi, hj] at hb
        rw [if_neg (one_ne_neg_one_of_two_ne_zero h2), if_pos rfl] at hb
        exact (by decide : ¬((0 : Fin 2) = 1)) hb
      · exfalso
        rw [hi, hj] at hb
        rw [if_pos rfl, if_neg (one_ne_neg_one_of_two_ne_zero h2)] at hb
        exact (by decide : ¬((1 : Fin 2) = 0)) hb
      · rw [hi, hj]
    have hker : (⊤ : Submodule K V) ≤ LinearMap.ker (f i - f j) := by
      rw [← hspanX]
      refine iSup_le fun χ => ?_
      intro v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply]
      have hvi : (f i) v = χ.1 i • v :=
        Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv i)
      have hvj : (f j) v = χ.1 j • v :=
        Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv j)
      rw [hvi, hvj, hpoint χ, sub_self]
    have hzero : f i - f j = 0 := by
      ext v
      have hv : v ∈ LinearMap.ker (f i - f j) :=
        hker (show v ∈ (⊤ : Submodule K V) from Submodule.mem_top)
      rw [LinearMap.mem_ker] at hv
      exact hv
    exact sub_eq_zero.mp hzero
  calc Nat.card ι ≤ Nat.card (X → Fin 2) := Nat.card_le_card_of_injective Φ hΦ
    _ = 2 ^ Fintype.card X := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun]; simp
    _ ≤ 2 ^ finrank K V := Nat.pow_le_pow_right (by norm_num) hcardX

end KeyLemma

theorem pow_le_card_of_elemAbelian_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) {S : Subgroup (MulAut ↥Bs)} (hS : IsElemAbelian 2 S) {k : ℕ}
    (hk : 2 ^ k ≤ Nat.card S) [Finite Bs] : p ^ k ≤ Nat.card Bs := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative ↥Bs := hBs.1
  have hp2' : (2 : ZMod p) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hV : ∀ x : Additive ↥Bs, p • x = 0 := fun x => by
    apply Additive.toMul.injective
    show x.toMul ^ p = 1
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBs.2 x.toMul x.toMul.2
  letI : Module (ZMod p) (Additive ↥Bs) := AddCommGroup.zmodModule (n := p) hV
  haveI hfin : Module.Finite (ZMod p) (Additive ↥Bs) := Module.Finite.of_finite
  let f : S → Module.End (ZMod p) (Additive ↥Bs) := fun s =>
    (MonoidHom.toAdditive ((s : MulAut ↥Bs).toMonoidHom)).toZModLinearMap p
  have hf_apply : ∀ (s : S) (b : ↥Bs),
      f s (Additive.ofMul b) = Additive.ofMul ((s : MulAut ↥Bs) b) := fun s b => rfl
  have hf : Function.Injective f := by
    intro s t hst
    have hpoint : ∀ b : ↥Bs, (s : MulAut ↥Bs) b = (t : MulAut ↥Bs) b := by
      intro b
      have h := congrArg (fun g : Module.End (ZMod p) (Additive ↥Bs) => g (Additive.ofMul b)) hst
      rw [hf_apply s b, hf_apply t b] at h
      exact Additive.toMul.injective h
    exact Subtype.ext (MulEquiv.ext hpoint)
  have hcomm : ∀ s t : S, Commute (f s) (f t) := by
    intro s t
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := Additive.ofMul.surjective x
    simp only [Module.End.mul_apply, hf_apply]
    have h := congrArg (fun u : MulAut ↥Bs => u b) (hS.comm s.2 t.2)
    have hb : (s : MulAut ↥Bs) ((t : MulAut ↥Bs) b) = (t : MulAut ↥Bs) ((s : MulAut ↥Bs) b) := by
      simpa [Function.comp_apply] using h
    rw [hb]
  have hsq : ∀ s : S, f s * f s = 1 := by
    intro s
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := Additive.ofMul.surjective x
    simp only [Module.End.mul_apply, Module.End.one_apply, hf_apply]
    have h := congrArg (fun u : MulAut ↥Bs => u b) (hS.mul_self_eq_one s.2)
    have hb : (s : MulAut ↥Bs) ((s : MulAut ↥Bs) b) = b := by
      simpa [Function.comp_apply] using h
    rw [hb]
  have hcard : Nat.card S ≤ 2 ^ finrank (ZMod p) (Additive ↥Bs) :=
    natCard_le_two_pow_finrank_of_commuting_involutions hp2' f hf hcomm hsq
  have hk' : 2 ^ k ≤ 2 ^ finrank (ZMod p) (Additive ↥Bs) := hk.trans hcard
  have hk_le : k ≤ finrank (ZMod p) (Additive ↥Bs) :=
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hk'
  have hVcard : Nat.card (Additive ↥Bs) = p ^ finrank (ZMod p) (Additive ↥Bs) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive ↥Bs)
    rw [Nat.card_zmod] at h
    exact h
  calc p ^ k ≤ p ^ finrank (ZMod p) (Additive ↥Bs) := Nat.pow_le_pow_right hp.pos hk_le
    _ = Nat.card (Additive ↥Bs) := hVcard.symm
    _ = Nat.card ↥Bs := Nat.card_congr (Additive.toMul : Additive ↥Bs ≃ ↥Bs)

end Rank

section CoxeterB

open CFSG.LieType.Universal CFSG.LieType.RootSystem CoxeterSystem CFSG.LieType.Universal.Symplectic

theorem coxeterMatrix_cartanC_eq_B (n : ℕ) :
    coxeterMatrix (isFiniteType_cartanC n) = CoxeterMatrix.B n := by
  have key : ∀ i j : Fin n, i.val < j.val →
      coxeterMatrix (isFiniteType_cartanC n) i j = CoxeterMatrix.B n i j := by
    intro i j hij
    have hijne : i ≠ j := Fin.ne_of_val_ne (by omega)
    by_cases h1 : i.val + 1 = j.val
    · by_cases h2 : j.val + 1 < n
      · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_succ_short n h1 h2]
        simp only [CoxeterMatrix.B, Matrix.of_apply, if_neg hijne]
        split_ifs <;> omega
      · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_succ_long n h1 h2]
        simp only [CoxeterMatrix.B, Matrix.of_apply, if_neg hijne]
        split_ifs <;> omega
    · have h2 : j.val + 1 ≠ i.val := by omega
      rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_far n hijne h1 h2]
      simp only [CoxeterMatrix.B, Matrix.of_apply, if_neg hijne]
      split_ifs <;> omega
  ext i j
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact key i j h
  · have hij : i = j := Fin.ext h
    subst hij
    simp
  · rw [(coxeterMatrix (isFiniteType_cartanC n)).symmetric i j,
      (CoxeterMatrix.B n).symmetric i j]
    exact key j i h

private lemma toStd_single_self_ne_zero (n : ℕ) (b : Fin n) :
    toStd n (Pi.single b (1 : ℤ)) b ≠ 0 := by
  by_cases hb : b.val + 1 < n
  · rw [SpExtras.toStd_single_of_lt' hb, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (Fin.ne_of_val_ne (by simp : b.val ≠ b.val + 1))]
    norm_num
  · rw [SpExtras.toStd_single_of_not_lt' hb, Pi.smul_apply, Pi.single_eq_same]
    norm_num

private theorem exists_elemAbelian_two_coxeterB_succ (k : ℕ) (hk : 1 ≤ k) :
    ∃ S : Subgroup (CoxeterMatrix.B (k + 1)).Group,
      IsElemAbelian 2 S ∧ 2 ^ (k + 1) ≤ Nat.card S := by
  rw [← coxeterMatrix_cartanC_eq_B (k + 1)]
  let S : Subgroup (coxeterMatrix (isFiniteType_cartanC (k + 1))).Group :=
    { carrier := {w | ∃ s : Fin (k + 1) → ℤ, SpIsSign s ∧ SpRealizes (k + 1) w 1 s}
      mul_mem' := by
        rintro w₁ w₂ ⟨s₁, hs₁, h₁⟩ ⟨s₂, hs₂, h₂⟩
        exact ⟨fun c => s₂ c * s₁ c, hs₂.mul hs₁ 1,
          (h₁.mul h₂).congr (by rw [mul_one]) (by funext c; simp [Equiv.Perm.one_def])⟩
      one_mem' := ⟨1, spIsSign_one, spRealizes_one⟩
      inv_mem' := by
        rintro w ⟨s, hs, h⟩
        exact ⟨s, hs, (h.inv hs).congr (by rw [inv_one])
          (by funext c; simp [Equiv.Perm.one_def])⟩ }
  refine ⟨S, ?_, ?_⟩
  · refine ⟨⟨⟨fun w₁ w₂ => Subtype.ext ?_⟩⟩, fun w hw => ?_⟩
    · obtain ⟨s₁, hs₁, h₁⟩ := w₁.2
      obtain ⟨s₂, hs₂, h₂⟩ := w₂.2
      exact SpRealizes.inj (h₁.mul h₂) ((h₂.mul h₁).congr rfl (by
        funext c; simp only [Equiv.Perm.one_apply]; ring))
    · obtain ⟨s, hs, h⟩ := hw
      rw [pow_two]
      exact SpRealizes.inj (h.mul h) (spRealizes_one.congr (by rw [mul_one]) (by
        funext c; simp only [Equiv.Perm.one_apply]; exact (hs.mul_self c).symm))
  · have hex : ∀ T : Finset (Fin (k + 1)),
        ∃ w : (coxeterMatrix (isFiniteType_cartanC (k + 1))).Group,
          w ∈ S ∧ SpRealizes (k + 1) w 1 (spSgnOn T) := by
      intro T
      have hproj : ∀ a ∈ T.erase 0, 1 ≤ a.val := by
        intro a ha
        rw [Finset.mem_erase] at ha
        have : a.val ≠ 0 := fun h => ha.1 (Fin.ext (by simpa using h))
        omega
      obtain ⟨v, hv, hvr⟩ := exists_spLeviW_sgnOn (n := k) hk (T.erase 0) hproj
      by_cases h0 : 0 ∈ T
      · obtain ⟨z, hzr⟩ := exists_spZeroSign (n := k) hk
        have hreal : SpRealizes (k + 1) (v * z) 1
            (fun c => spSgn 0 c * spSgnOn (T.erase 0) c) :=
          (hvr.mul hzr).congr (by rw [mul_one]) (by funext c; simp [Equiv.Perm.one_def])
        refine ⟨v * z, ⟨fun c => spSgn 0 c * spSgnOn (T.erase 0) c,
            (spIsSign_spSgn 0).mul (spIsSign_spSgnOn _) 1, hreal⟩, ?_⟩
        refine hreal.congr rfl ?_
        funext c
        unfold spSgnOn spSgn
        by_cases hc : c = 0
        · subst hc
          simp [h0]
        · have hmem : c ∈ T.erase 0 ↔ c ∈ T := by
            rw [Finset.mem_erase]
            exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
          simp [hc, hmem]
      · have herase : T.erase 0 = T := Finset.erase_eq_self.mpr h0
        exact ⟨v, ⟨spSgnOn (T.erase 0), spIsSign_spSgnOn _, hvr⟩, herase ▸ hvr⟩
    choose w hwmem hwreal using hex
    have hinj : Function.Injective (fun T : Finset (Fin (k + 1)) => (⟨w T, hwmem T⟩ : S)) := by
      intro T T' hTT'
      have hw : w T = w T' := congrArg Subtype.val hTT'
      have hreal : SpRealizes (k + 1) (w T') 1 (spSgnOn T) := hw ▸ hwreal T
      have hreal' : SpRealizes (k + 1) (w T') 1 (spSgnOn T') := hwreal T'
      ext b
      have h1 := congrFun (hreal (Pi.single b (1 : ℤ))) b
      have h2 := congrFun (hreal' (Pi.single b (1 : ℤ))) b
      simp only [Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply] at h1 h2
      have hb : toStd (k + 1) (Pi.single b (1 : ℤ)) b ≠ 0 :=
        toStd_single_self_ne_zero (k + 1) b
      have hmul : spSgnOn T b * toStd (k + 1) (Pi.single b (1 : ℤ)) b =
          spSgnOn T' b * toStd (k + 1) (Pi.single b (1 : ℤ)) b := by rw [← h1, ← h2]
      have hval : spSgnOn T b = spSgnOn T' b := mul_right_cancel₀ hb hmul
      have hmem : b ∈ T ↔ b ∈ T' := by
        have h1' : (b ∈ T) ↔ spSgnOn T b = -1 := by simp [spSgnOn]
        have h2' : (b ∈ T') ↔ spSgnOn T' b = -1 := by simp [spSgnOn]
        rw [h1', h2', hval]
      exact hmem
    have hsurj : Function.Surjective (fun T : Finset (Fin (k + 1)) => (⟨w T, hwmem T⟩ : S)) := by
      rintro ⟨u, hu⟩
      obtain ⟨s, hs, hreal⟩ := hu
      let T : Finset (Fin (k + 1)) := Finset.univ.filter fun a => s a = -1
      have hT : spSgnOn T = s := by
        funext a
        unfold spSgnOn
        by_cases ha : s a = -1
        · have hmem : a ∈ T := by simp [T, ha]
          simp [hmem, ha]
        · have hsa : s a = 1 := by
            rcases hs a with h | h
            · exact h
            · exact absurd h ha
          have hmem : a ∉ T := by simp [T, ha]
          simp [hmem, hsa]
      exact ⟨T, Subtype.ext (SpRealizes.inj
        (show SpRealizes (k + 1) (w T) 1 s from hT ▸ hwreal T) hreal)⟩
    have hcard : Nat.card (Finset (Fin (k + 1))) = Nat.card S :=
      Nat.card_congr (Equiv.ofBijective
        (fun T : Finset (Fin (k + 1)) => (⟨w T, hwmem T⟩ : S)) ⟨hinj, hsurj⟩)
    have hcard2 : Nat.card (Finset (Fin (k + 1))) = 2 ^ (k + 1) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]
    exact le_of_eq (hcard2.symm.trans hcard)

end CoxeterB

theorem exists_elemAbelian_two_coxeterB (n : ℕ) (hn : 2 ≤ n) :
    ∃ S : Subgroup (CoxeterMatrix.B n).Group, IsElemAbelian 2 S ∧ 2 ^ n ≤ Nat.card S := by
  have hEq : n = (n - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
  rw [hEq]
  exact exists_elemAbelian_two_coxeterB_succ (n - 1) (by omega)

end CFSG.StandardType

