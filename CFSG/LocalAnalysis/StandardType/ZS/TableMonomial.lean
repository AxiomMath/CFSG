module

public import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialRows
import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsMonomial
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)

private theorem tmo_refl_ne_one {r : U ≃ₗ[ZMod p] U} (hr : IsRefl p r) : r ≠ 1 := by
  intro h
  rw [h] at hr
  have h0 : ((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - LinearMap.id = 0 := by
    ext x; simp
  have hfin := hr.2
  rw [h0, LinearMap.range_zero, finrank_bot] at hfin
  omega

private theorem tmo_refl_scalar_of_moved (f : Module.Basis (Fin n) (ZMod p) U)
    {r : U ≃ₗ[ZMod p] U} (hr : IsRefl p r) {i₁ : Fin n} (hi₁ : r (f i₁) - f i₁ ≠ 0) :
    ∀ i, ∃ d : ZMod p, d • (r (f i₁) - f i₁) = r (f i) - f i := by
  have hmem : ∀ i, r (f i) - f i ∈ LinearMap.range ((r : U →ₗ[ZMod p] U) - LinearMap.id) :=
    fun i => ⟨f i, by simp [LinearMap.sub_apply, LinearEquiv.coe_coe]⟩
  intro i
  have h := (exists_smul_eq_of_finrank_eq_one (K := ZMod p)
    (V := ↥(LinearMap.range ((r : U →ₗ[ZMod p] U) - LinearMap.id)))
    hr.2 (x := ⟨r (f i₁) - f i₁, hmem i₁⟩) (by simpa using hi₁) ⟨r (f i) - f i, hmem i⟩)
  obtain ⟨d, hd⟩ := h
  exact ⟨d, congrArg Subtype.val hd⟩

private theorem tmo_refl_support_card_le_two (f : Module.Basis (Fin n) (ZMod p) U)
    {r : U ≃ₗ[ZMod p] U} {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hrb : ∀ i, r (f i) = c i • f (σ i)) {i₁ : Fin n} :
    (f.repr (r (f i₁) - f i₁)).support.card ≤ 2 := by
  let a : U := r (f i₁) - f i₁
  have hsub : (f.repr a).support ⊆ {i₁, σ i₁} := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk
    have haeq : f.repr a = Finsupp.single (σ i₁) (c i₁) - Finsupp.single i₁ 1 := by
      dsimp only [a]
      rw [map_sub, hrb i₁, map_smul, Module.Basis.repr_self, Finsupp.smul_single]
      simp
    rw [haeq, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply] at hk
    by_cases hk1 : k = i₁
    · simp [hk1]
    · by_cases hk2 : k = σ i₁
      · simp [hk2]
      · exfalso
        rw [if_neg (Ne.symm hk1), if_neg (Ne.symm hk2), sub_zero] at hk
        exact hk rfl
  calc (f.repr a).support.card ≤ ({i₁, σ i₁} : Finset (Fin n)).card := Finset.card_le_card hsub
    _ ≤ 2 := by
      rw [show ({i₁, σ i₁} : Finset (Fin n)) = insert i₁ {σ i₁} by rfl]
      exact le_trans (Finset.card_insert_le i₁ {σ i₁}) (by simp)

private theorem tmo_exists_notMem_support (hn : 3 ≤ n) {s : Finset (Fin n)} (hs : s.card ≤ 2) :
    ∃ l : Fin n, l ∉ s := by
  have hslt : s.card < n := by omega
  by_contra h
  push Not at h
  have : s.card = n := by
    apply le_antisymm
    · simpa using Finset.card_le_univ s
    · have : (Finset.univ : Finset (Fin n)) ⊆ s := fun x _ => h x
      calc n = (Finset.univ : Finset (Fin n)).card := by simp
        _ ≤ s.card := Finset.card_le_card this
  omega

private theorem tmo_refl_fix_of_notMem_support (f : Module.Basis (Fin n) (ZMod p) U)
    {r : U ≃ₗ[ZMod p] U} {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hrb : ∀ i, r (f i) = c i • f (σ i)) {i₁ l : Fin n}
    (hgen : ∀ i, ∃ d : ZMod p, d • (r (f i₁) - f i₁) = r (f i) - f i)
    (hl : f.repr (r (f i₁) - f i₁) l = 0) : r (f l) = f l := by
  by_contra hne
  obtain ⟨d, hd⟩ := hgen l
  have hcoeff : f.repr (r (f l) - f l) l ≠ 0 := by
    rw [hrb l]
    simp only [map_sub, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      Finsupp.sub_apply, Finsupp.single_apply]
    by_cases hll : σ l = l
    · rw [if_pos hll, if_pos trivial]
      intro hc
      have hc1 : c l = 1 := by
        simpa [smul_eq_mul, mul_one] using (sub_eq_zero.mp hc)
      exact hne (by rw [hrb l, hll, hc1, one_smul])
    · rw [if_neg hll, if_pos trivial]
      simp only [zero_sub]
      exact neg_ne_zero.mpr one_ne_zero
  by_cases hd0 : d = 0
  · rw [hd0, zero_smul] at hd
    exact hne (sub_eq_zero.mp hd.symm)
  · exact hcoeff (by rw [← hd, map_smul, Finsupp.smul_apply, smul_eq_mul, hl, mul_zero])

theorem exists_apply_eq_of_isRefl_of_monomial (hn : 3 ≤ n) {r : U ≃ₗ[ZMod p] U}
    (hr : IsRefl p r) (hmon : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      ∀ i, r (f i) = c i • f (σ i)) : ∃ l, r (f l) = f l := by
  obtain ⟨σ, c, hrb⟩ := hmon
  have hrne : r ≠ 1 := tmo_refl_ne_one hr
  obtain ⟨i₁, hi₁⟩ : ∃ i, r (f i) - f i ≠ 0 := by
    by_contra h
    push Not at h
    exact hrne (f.ext' fun i => sub_eq_zero.mp (h i))
  have hgen := tmo_refl_scalar_of_moved f hr hi₁
  have hs : (f.repr (r (f i₁) - f i₁)).support.card ≤ 2 :=
    tmo_refl_support_card_le_two f hrb
  obtain ⟨l, hl⟩ := tmo_exists_notMem_support hn hs
  have hl0 : f.repr (r (f i₁) - f i₁) l = 0 := Finsupp.notMem_support_iff.mp hl
  exact ⟨l, tmo_refl_fix_of_notMem_support f hrb hgen hl0⟩

private theorem tfne_permMap_mem_closure (f : Module.Basis (Fin n) (ZMod p) U) {i₀ : Fin n}
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hstar : ∀ k : Fin n, k ≠ i₀ → permMap p f (Equiv.swap i₀ k) ∈ H)
    (σ : Equiv.Perm (Fin n)) : permMap p f σ ∈ H := by
  let φ : Equiv.Perm (Fin n) →* (U ≃ₗ[ZMod p] U) :=
    MonoidHom.mk' (permMap p f) (fun σ τ => (permMap_mul f σ τ).symm)
  have htop : (⊤ : Subgroup (Equiv.Perm (Fin n))) ≤ H.comap φ := by
    rw [← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    rintro τ hτ
    obtain ⟨j, k, hjk, rfl⟩ := hτ
    show permMap p f (Equiv.swap j k) ∈ H
    by_cases hj : j = i₀
    · subst j
      exact hstar k (Ne.symm hjk)
    · by_cases hk : k = i₀
      · subst k
        rw [Equiv.swap_comm]
        exact hstar j hj
      · have h1 : permMap p f (Equiv.swap i₀ j) ∈ H := hstar j hj
        have h2 : permMap p f (Equiv.swap i₀ k) ∈ H := hstar k hk
        have heq : Equiv.swap j k = Equiv.swap i₀ j * Equiv.swap i₀ k * Equiv.swap i₀ j := by
          have h := Equiv.swap_mul_swap_mul_swap (x := k) (y := i₀) (z := j) hk (Ne.symm hjk)
          rw [Equiv.swap_comm k i₀] at h
          exact h.symm
        rw [heq]
        simp only [← permMap_mul]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h1
  exact htop (Subgroup.mem_top σ)

private noncomputable def tfneGens (f : Module.Basis (Fin n) (ZMod p) U) (i₀ i₁ : Fin n)
    (ζ : (ZMod p)ˣ) : Finset (U ≃ₗ[ZMod p] U) := by
  classical
  exact insert (diagMap p f (pairUnit p i₀ i₁ ζ) * permMap p f (Equiv.swap i₀ i₁))
    ((Finset.univ.erase i₀).image fun k => permMap p f (Equiv.swap i₀ k))

private theorem tfne_star_mem_gens (f : Module.Basis (Fin n) (ZMod p) U) {i₀ : Fin n}
    (i₁ : Fin n) (ζ : (ZMod p)ˣ) {k : Fin n} (hk : k ≠ i₀) :
    permMap p f (Equiv.swap i₀ k) ∈ tfneGens f i₀ i₁ ζ := by
  classical
  unfold tfneGens
  exact Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩, rfl⟩)

private theorem tfne_twist_mem_gens (f : Module.Basis (Fin n) (ZMod p) U) (i₀ i₁ : Fin n)
    (ζ : (ZMod p)ˣ) :
    diagMap p f (pairUnit p i₀ i₁ ζ) * permMap p f (Equiv.swap i₀ i₁) ∈ tfneGens f i₀ i₁ ζ := by
  classical
  unfold tfneGens
  exact Finset.mem_insert_self _ _

private theorem tfne_swap_mem_gens (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) :
    permMap p f (Equiv.swap i₀ i₁) ∈ tfneGens f i₀ i₁ ζ := by
  classical
  unfold tfneGens
  exact Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i₁, Finset.mem_erase.mpr ⟨hi.symm, Finset.mem_univ i₁⟩, rfl⟩)

private theorem tfne_gens_card_le (f : Module.Basis (Fin n) (ZMod p) U) (i₀ i₁ : Fin n)
    (ζ : (ZMod p)ˣ) : (tfneGens f i₀ i₁ ζ).card ≤ n := by
  classical
  have h1 : (tfneGens f i₀ i₁ ζ).card ≤
      ((Finset.univ.erase i₀).image fun k => permMap p f (Equiv.swap i₀ k)).card + 1 := by
    unfold tfneGens
    exact Finset.card_insert_le _ _
  have h2 : ((Finset.univ.erase i₀).image fun k => permMap p f (Equiv.swap i₀ k)).card ≤
      (Finset.univ.erase i₀).card := Finset.card_image_le
  have h3 : (Finset.univ.erase i₀).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
  have hn : 1 ≤ n := by have := i₀.isLt; omega
  omega

private theorem tfne_gens_mem_gmmn (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (ζ : (ZMod p)ˣ) {x : U ≃ₗ[ZMod p] U} (hx : x ∈ tfneGens f i₀ i₁ ζ) :
    x ∈ gmmn p f i₀ i₁ ζ := by
  classical
  unfold tfneGens at hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr rfl))
      (Subgroup.subset_closure (Or.inl (Set.mem_range_self _)))
  · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    exact Subgroup.subset_closure (Or.inl (Set.mem_range_self _))

private theorem tfne_gens_isRefl (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {x : U ≃ₗ[ZMod p] U} (hx : x ∈ tfneGens f i₀ i₁ ζ) :
    IsRefl p x := by
  classical
  unfold tfneGens at hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact isRefl_diagMap_mul_permMap_swap f hi ζ
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact isRefl_permMap_swap f (Ne.symm (Finset.mem_erase.mp hk).1)

theorem negOrGen_gmmn {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) :
    NegOrGen p n (gmmn p f i₀ i₁ ζ) := by
  classical
  let s : Finset (U ≃ₗ[ZMod p] U) := tfneGens f i₀ i₁ ζ
  have hcard : s.card ≤ n := by
    dsimp only [s]; exact tfne_gens_card_le f i₀ i₁ ζ
  have hmem : ∀ x ∈ s, x ∈ gmmn p f i₀ i₁ ζ := by
    intro x hx; dsimp only [s] at hx; exact tfne_gens_mem_gmmn f ζ hx
  have hrefl : ∀ x ∈ s, IsRefl p x := by
    intro x hx; dsimp only [s] at hx; exact tfne_gens_isRefl f hi ζ hx
  refine Or.inr ⟨s, hcard, fun x hx => ⟨hmem x hx, hrefl x hx⟩, ?_⟩
  apply le_antisymm
  · rw [gmmn, Subgroup.closure_le]
    intro x hx
    rcases hx with ⟨σ, rfl⟩ | hx
    · exact tfne_permMap_mem_closure f (H := Subgroup.closure (↑s))
        (fun k hk => Subgroup.subset_closure (Finset.mem_coe.mpr (by
          dsimp only [s]; exact tfne_star_mem_gens f i₁ ζ hk))) σ
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have htw : diagMap p f (pairUnit p i₀ i₁ ζ) * permMap p f (Equiv.swap i₀ i₁) ∈
          Subgroup.closure (↑s) :=
        Subgroup.subset_closure (Finset.mem_coe.mpr (by
          dsimp only [s]; exact tfne_twist_mem_gens f i₀ i₁ ζ))
      have hp11 : permMap p f (Equiv.swap i₀ i₁) ∈ Subgroup.closure (↑s) :=
        Subgroup.subset_closure (Finset.mem_coe.mpr (by
          dsimp only [s]; exact tfne_swap_mem_gens f hi ζ))
      have hdiag : diagMap p f (pairUnit p i₀ i₁ ζ) =
          (diagMap p f (pairUnit p i₀ i₁ ζ) * permMap p f (Equiv.swap i₀ i₁)) *
            (permMap p f (Equiv.swap i₀ i₁))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [hdiag]
      exact Subgroup.mul_mem _ htw (Subgroup.inv_mem _ hp11)
  · rw [Subgroup.closure_le]
    intro x hx
    rw [Finset.mem_coe] at hx
    exact hmem x hx

private theorem tmo_pairUnit_self {i j : Fin n} (_hij : i ≠ j) (c : (ZMod p)ˣ) :
    pairUnit p i j c i = c := by
  rw [pairUnit, if_pos rfl]

private theorem tmo_pairUnit_other {i j : Fin n} (hij : i ≠ j) (c : (ZMod p)ˣ) :
    pairUnit p i j c j = c⁻¹ := by
  rw [pairUnit, if_neg (Ne.symm hij), if_pos rfl]

private theorem tmo_pairUnit_ne {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) (c : (ZMod p)ˣ) :
    pairUnit p i j c k = 1 := by
  rw [pairUnit, if_neg hki, if_neg hkj]

private noncomputable def tmoDiagHom (f : Module.Basis (Fin n) (ZMod p) U) :
    (Fin n → (ZMod p)ˣ) →* (U ≃ₗ[ZMod p] U) where
  toFun d := diagMap p f d
  map_one' := diagMap_one f
  map_mul' d d' := (diagMap_mul f d d').symm

private noncomputable def tmoDiagWitness (f : Module.Basis (Fin n) (ZMod p) U)
    (ζ : (ZMod p)ˣ) : Subgroup (U ≃ₗ[ZMod p] U) :=
  Subgroup.closure {g | ∃ k j : Fin n, k ≠ j ∧ g = diagMap p f (pairUnit p k j ζ)}

private theorem tmo_basis_mem_commutatorSpace (f : Module.Basis (Fin n) (ZMod p) U)
    {ζ : (ZMod p)ˣ} (hζ : ζ ≠ 1) (hn : 1 < n) (k : Fin n) :
    f k ∈ HardMathSupport.Kantor79.commutatorSpace (tmoDiagWitness f ζ) := by
  obtain ⟨j, hjk⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n) (by rwa [Fintype.card_fin]) k
  have hkj : k ≠ j := Ne.symm hjk
  have hgD : diagMap p f (pairUnit p k j ζ) ∈ tmoDiagWitness f ζ :=
    Subgroup.subset_closure ⟨k, j, hkj, rfl⟩
  have hmem : diagMap p f (pairUnit p k j ζ) (f k) - f k ∈
      HardMathSupport.Kantor79.commutatorSpace (tmoDiagWitness f ζ) :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hgD ⟨f k, rfl⟩
  have hζne : (ζ : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr fun h => hζ (Units.ext h)
  have hval : diagMap p f (pairUnit p k j ζ) (f k) = (ζ : ZMod p) • f k := by
    rw [diagMap_apply_basis, tmo_pairUnit_self hkj ζ]
  have hsub : (ζ : ZMod p) • f k - f k = ((ζ : ZMod p) - 1) • f k := by
    rw [sub_smul, one_smul]
  have heq : ((ζ : ZMod p) - 1)⁻¹ • (diagMap p f (pairUnit p k j ζ) (f k) - f k) = f k := by
    rw [hval, hsub, smul_smul, inv_mul_cancel₀ hζne, one_smul]
  rw [← heq]
  exact Submodule.smul_mem _ _ hmem

private theorem tmo_commutatorSpace_eq_top (f : Module.Basis (Fin n) (ZMod p) U)
    {ζ : (ZMod p)ˣ} (hζ : ζ ≠ 1) (hn : 1 < n) :
    HardMathSupport.Kantor79.commutatorSpace (tmoDiagWitness f ζ) = ⊤ := by
  rw [eq_top_iff, ← f.span_eq, Submodule.span_le]
  rintro x ⟨k, rfl⟩
  exact tmo_basis_mem_commutatorSpace f hζ hn k

theorem coprimeWitness_gmmn {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : ζ ≠ 1) :
    CoprimeWitness p (gmmn p f i₀ i₁ ζ) := by
  have hn : 1 < n := by
    have h := Fintype.one_lt_card_iff.mpr ⟨i₀, i₁, hi⟩
    rwa [Fintype.card_fin] at h
  refine ⟨tmoDiagWitness f ζ, ?_, ?_, tmo_commutatorSpace_eq_top f hζ hn⟩
  · rw [tmoDiagWitness, Subgroup.closure_le]
    rintro x ⟨k, j, hkj, rfl⟩
    exact diagMap_pairUnit_mem_gmmn f hi hkj (Subgroup.mem_zpowers ζ)
  · have hle : tmoDiagWitness f ζ ≤ (tmoDiagHom f).range := by
      rw [tmoDiagWitness, Subgroup.closure_le]
      rintro x ⟨k, j, hkj, rfl⟩
      exact ⟨pairUnit p k j ζ, rfl⟩
    have hcard : Nat.card (tmoDiagWitness f ζ) ∣ (p - 1) ^ n := by
      have h1 : Nat.card (tmoDiagWitness f ζ) ∣ Nat.card (Fin n → (ZMod p)ˣ) :=
        (Subgroup.card_dvd_of_le hle).trans (Subgroup.card_range_dvd (tmoDiagHom f))
      have h2 : Nat.card (Fin n → (ZMod p)ˣ) = (p - 1) ^ n := by
        rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, ZMod.card_units]
      rwa [h2] at h1
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
    have hcop1 : Nat.Coprime (p - 1) p :=
      (Nat.coprime_self_sub_left hp1).mpr (Nat.coprime_one_left p)
    have hcop : Nat.Coprime ((p - 1) ^ n) p :=
      (Nat.coprime_pow_left_iff (by omega) (p - 1) p).mpr hcop1
    exact hcop.coprime_dvd_left hcard

private theorem tmo_sep_gmmn (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : 3 ≤ orderOf ζ) {l i j : Fin n} (hil : i ≠ l)
    (hjl : j ≠ l) (hij : i ≠ j) :
    ∃ h ∈ fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l),
      (∀ k ∈ {i : Fin n | i ≠ l}, ∃ e : ZMod p, h (f k) = e • f k) ∧
      ∃ c d : ZMod p, c ≠ d ∧ h (f i) = c • f i ∧ h (f j) = d • f j := by
  have hζne : ζ ≠ ζ⁻¹ := by
    intro h
    have h2 : ζ ^ 2 = 1 := by
      rw [sq]
      have h3 : ζ * ζ⁻¹ = 1 := mul_inv_cancel ζ
      rwa [← h] at h3
    have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hperm : permMap p f (Equiv.swap i j) ∈
      fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l) := by
    refine mem_fixReflSubgroup (Subgroup.subset_closure (Or.inl (Set.mem_range_self _)))
      (isRefl_permMap_swap f hij) ?_
    rw [permMap_apply_basis, Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl)]
  have htw : diagMap p f (pairUnit p i j ζ) * permMap p f (Equiv.swap i j) ∈
      fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l) := by
    refine mem_fixReflSubgroup ?_ (isRefl_diagMap_mul_permMap_swap f hij ζ) ?_
    · exact Subgroup.mul_mem _ (diagMap_pairUnit_mem_gmmn f hi hij (Subgroup.mem_zpowers ζ))
        (Subgroup.subset_closure (Or.inl (Set.mem_range_self _)))
    · rw [LinearEquiv.mul_apply, permMap_apply_basis,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl), diagMap_apply_basis,
        tmo_pairUnit_ne (Ne.symm hil) (Ne.symm hjl) ζ, Units.val_one, one_smul]
  have hmem : diagMap p f (pairUnit p i j ζ) ∈
      fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l) := by
    have h := Subgroup.mul_mem _ htw hperm
    rwa [mul_assoc, permMap_mul, Equiv.swap_mul_self, permMap_one, mul_one] at h
  refine ⟨diagMap p f (pairUnit p i j ζ), hmem, ?_, (ζ : ZMod p),
    ((ζ⁻¹ : (ZMod p)ˣ) : ZMod p), ?_, ?_, ?_⟩
  · intro k _
    exact ⟨(pairUnit p i j ζ k : ZMod p), by rw [diagMap_apply_basis]⟩
  · intro h
    exact hζne (Units.ext h)
  · rw [diagMap_apply_basis, tmo_pairUnit_self hij ζ]
  · rw [diagMap_apply_basis, tmo_pairUnit_other hij ζ]

theorem irredOnSection_fixReflSubgroup_gmmn {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (hζ : 3 ≤ orderOf ζ) (l : Fin n) :
    IrredOnSection (fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l)) ⊥
      (Submodule.span (ZMod p) (f '' {i | i ≠ l})) := by
  refine irredOnSection_span_of_separating (K := ZMod p) (b := f)
    (B := fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l))
    (S := {i : Fin n | i ≠ l}) f.linearIndependent ?_ ?_
  · intro i hi' j hj' hij
    exact tmo_sep_gmmn f hi hζ hi' hj' hij
  · intro i hi' j hj'
    by_cases hij : i = j
    · subst hij
      refine ⟨1, Subgroup.one_mem _, 1, one_ne_zero, ?_⟩
      simp
    · refine ⟨permMap p f (Equiv.swap i j), ?_, 1, one_ne_zero, ?_⟩
      · refine mem_fixReflSubgroup (Subgroup.subset_closure (Or.inl (Set.mem_range_self _)))
          (isRefl_permMap_swap f hij) ?_
        rw [permMap_apply_basis, Equiv.swap_apply_of_ne_of_ne (Ne.symm hi') (Ne.symm hj')]
      · rw [permMap_apply_basis, Equiv.swap_apply_left, one_smul]

private theorem tmo_exists_ne_pair (hn : 3 ≤ n) (l : Fin n) :
    ∃ i j : Fin n, i ≠ l ∧ j ≠ l ∧ i ≠ j := by
  have hcard : 1 < Fintype.card {i : Fin n // i ≠ l} := by
    rw [Fintype.card_subtype_compl (fun i : Fin n => i = l), Fintype.card_fin,
      Fintype.card_subtype_eq]
    omega
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hcard
  exact ⟨i.1, j.1, i.2, j.2, fun h => hij (Subtype.ext h)⟩

private theorem tmo_isCompl_coordSpan (f : Module.Basis (Fin n) (ZMod p) U) (l : Fin n) :
    IsCompl (Submodule.span (ZMod p) (f '' {i | i ≠ l}))
      (Submodule.span (ZMod p) {f l}) := by
  refine ⟨disjoint_iff.mpr ?_, ?_⟩
  · rw [Submodule.eq_bot_iff]
    rintro x ⟨hxW, hxW'⟩
    change x ∈ Submodule.span (ZMod p) {f l} at hxW'
    rw [Submodule.mem_span_singleton] at hxW'
    obtain ⟨c, rfl⟩ := hxW'
    have hsupp := (Module.Basis.mem_span_image (b := f) (s := {i | i ≠ l})).mp hxW
    have hlsupp : l ∉ (f.repr (c • f l)).support := fun hmem => hsupp hmem rfl
    have hzero : f.repr (c • f l) l = 0 := Finsupp.notMem_support_iff.mp hlsupp
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] at hzero
    rw [hzero, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = (x - (f.repr x l) • f l) + (f.repr x l) • f l := by abel
    have hmem : (x - (f.repr x l) • f l) + (f.repr x l) • f l ∈
        Submodule.span (ZMod p) (f '' {i | i ≠ l}) ⊔ Submodule.span (ZMod p) {f l} := by
      refine Submodule.mem_sup.mpr ⟨x - (f.repr x l) • f l, ?_, (f.repr x l) • f l, ?_, ?_⟩
      · apply (Module.Basis.mem_span_image (b := f) (s := {i | i ≠ l})).mpr
        intro i hi hil
        rw [hil] at hi
        rw [Finset.mem_coe, Finsupp.mem_support_iff, map_sub, map_smul, Module.Basis.repr_self,
          Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
          sub_self] at hi
        exact hi rfl
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (f l)))
      · abel
    rwa [← hx] at hmem

private theorem tmo_finrank_coordSpan (f : Module.Basis (Fin n) (ZMod p) U) (l : Fin n) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) (f '' {i | i ≠ l})) = n - 1 := by
  have hli : LinearIndependent (ZMod p) (fun i : {i : Fin n // i ≠ l} => f i.1) :=
    f.linearIndependent.comp Subtype.val Subtype.val_injective
  have hrange : Set.range (fun i : {i : Fin n // i ≠ l} => f i.1) = f '' {i | i ≠ l} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
  have hcard : Fintype.card {i : Fin n // i ≠ l} = n - 1 := by
    rw [Fintype.card_subtype_compl (fun i : Fin n => i = l), Fintype.card_fin,
      Fintype.card_subtype_eq]
  rw [← hrange, finrank_span_eq_card hli, hcard]

private theorem tmo_diagMap_mul_permMap_mem_coordSpan (f : Module.Basis (Fin n) (ZMod p) U)
    {l : Fin n} {d : Fin n → (ZMod p)ˣ} {σ : Equiv.Perm (Fin n)} (hσ : σ l = l) :
    ∀ w ∈ Submodule.span (ZMod p) (f '' {i | i ≠ l}),
      (diagMap p f d * permMap p f σ) w ∈ Submodule.span (ZMod p) (f '' {i | i ≠ l}) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      rw [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ i, ?_, rfl⟩)
      intro h
      exact hi (σ.injective (h.trans hσ.symm))
  | zero => simp
  | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
  | smul a y _ ihy => rw [map_smul]; exact Submodule.smul_mem _ _ ihy

private theorem tmo_fixRefl_preserves_coordSpan {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ g ∈ J, ∃ (d : Fin n → (ZMod p)ˣ) (σ : Equiv.Perm (Fin n)),
      g = diagMap p f d * permMap p f σ) (l : Fin n) :
    ∀ h ∈ fixReflSubgroup p J (f l),
      ∀ w ∈ Submodule.span (ZMod p) (f '' {i | i ≠ l}),
        h w ∈ Submodule.span (ZMod p) (f '' {i | i ≠ l}) := by
  intro h hh
  rw [fixReflSubgroup] at hh
  have hboth : (∀ w ∈ Submodule.span (ZMod p) (f '' {i | i ≠ l}),
      h w ∈ Submodule.span (ZMod p) (f '' {i | i ≠ l})) ∧
      (∀ w ∈ Submodule.span (ZMod p) (f '' {i | i ≠ l}),
        h⁻¹ w ∈ Submodule.span (ZMod p) (f '' {i | i ≠ l})) := by
    induction hh using Subgroup.closure_induction with
    | mem t ht =>
        obtain ⟨htJ, htref, htl⟩ := ht
        obtain ⟨d, σ, htform⟩ := hmon t htJ
        have hrepr : (Finsupp.single (σ l) (↑(d (σ l))) : Fin n →₀ ZMod p) =
            Finsupp.single l 1 := by
          have h := congrArg f.repr htl
          rw [htform] at h
          simpa [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis, map_smul,
            Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one] using h
        have hsl : σ l = l := by
          by_contra hne
          have h := DFunLike.congr_fun hrepr l
          rw [Finsupp.single_eq_of_ne (Ne.symm hne), Finsupp.single_eq_same] at h
          exact one_ne_zero h.symm
        have hpres := tmo_diagMap_mul_permMap_mem_coordSpan (f := f) (d := d) hsl
        refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · rw [htform]; exact hpres w hw
        · rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right htref.1, htform]
          exact hpres w hw
    | one => exact ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw⟩
    | mul a b _ _ iha ihb =>
        refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · rw [LinearEquiv.mul_apply]; exact iha.1 _ (ihb.1 w hw)
        · rw [mul_inv_rev, LinearEquiv.mul_apply]; exact ihb.2 _ (iha.2 w hw)
    | inv a _ iha => exact ⟨iha.2, fun w hw => by simpa [inv_inv] using iha.1 w hw⟩
  exact hboth.1

private theorem tmo_splitSupport_fixRefl (hn : 3 ≤ n) {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ g ∈ J, ∃ (d : Fin n → (ZMod p)ˣ) (σ : Equiv.Perm (Fin n)),
      g = diagMap p f d * permMap p f σ)
    (hperm : ∀ σ : Equiv.Perm (Fin n), permMap p f σ ∈ J) (l : Fin n)
    (hirr : IrredOnSection (fixReflSubgroup p J (f l)) ⊥
      (Submodule.span (ZMod p) (f '' {i | i ≠ l}))) :
    SplitSupport (fixReflSubgroup p J (f l)) (n - 1) := by
  have hcompl : IsCompl (Submodule.span (ZMod p) (f '' {i | i ≠ l}))
      (Submodule.span (ZMod p) {f l}) := tmo_isCompl_coordSpan f l
  have hfix : ∀ h ∈ fixReflSubgroup p J (f l),
      ∀ w ∈ Submodule.span (ZMod p) {f l}, h w = w := by
    intro h hh w hw
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    rw [map_smul, fixReflSubgroup_apply_eq hh]
  have hinv : ∀ h ∈ fixReflSubgroup p J (f l),
      ∀ w ∈ Submodule.span (ZMod p) (f '' {i | i ≠ l}),
        h w ∈ Submodule.span (ZMod p) (f '' {i | i ≠ l}) :=
    tmo_fixRefl_preserves_coordSpan (f := f) hmon l
  have hne : ∃ h ∈ fixReflSubgroup p J (f l),
      ∃ w ∈ Submodule.span (ZMod p) (f '' {i | i ≠ l}), h w ≠ w := by
    obtain ⟨i, j, hil, hjl, hij⟩ := tmo_exists_ne_pair (n := n) hn l
    have hmem : permMap p f (Equiv.swap i j) ∈ fixReflSubgroup p J (f l) :=
      mem_fixReflSubgroup (hperm _) (isRefl_permMap_swap f hij)
        (by rw [permMap_apply_basis, Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl)])
    refine ⟨permMap p f (Equiv.swap i j), hmem, f i, Submodule.subset_span ⟨i, hil, rfl⟩, ?_⟩
    intro hcon
    rw [permMap_apply_basis, Equiv.swap_apply_left] at hcon
    exact hij (f.injective hcon).symm
  have hsp := splitSupport_of_isCompl (K := ZMod p) (B := fixReflSubgroup p J (f l))
    hcompl hfix hinv hirr hne
  rwa [tmo_finrank_coordSpan f l] at hsp

theorem throughRefl_gmmn (_hp : p ≠ 2) (hn : 3 ≤ n) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁)
    {ζ : (ZMod p)ˣ} (hζ : 3 ≤ orderOf ζ) : ThroughRefl p (n - 1) (gmmn p f i₀ i₁ ζ) := by
  intro r hrJ hrrefl
  obtain ⟨d, σ, -, -, hgeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi hrJ
  have hmon : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), ∀ i, r (f i) = c i • f (σ i) :=
    ⟨σ, fun i => (d (σ i) : ZMod p), fun i => by
      rw [hgeq, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]⟩
  obtain ⟨l, hrl⟩ := exists_apply_eq_of_isRefl_of_monomial (f := f) hn hrrefl hmon
  refine ⟨fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l), fixReflSubgroup_le _ _,
    mem_fixReflSubgroup hrJ hrrefl hrl, reflGen_fixReflSubgroup _ _,
    tmo_splitSupport_fixRefl (f := f) hn ?_ (fun σ => Subgroup.subset_closure
      (Or.inl (Set.mem_range_self σ))) l (irredOnSection_fixReflSubgroup_gmmn (f := f) hi hζ l)⟩
  intro g hg
  obtain ⟨d', σ', -, -, hgeq'⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi hg
  exact ⟨d', σ', hgeq'⟩

private theorem signMap_mem_g2mmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (ζ : (ZMod p)ˣ) (k : Fin n) :
    diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) ∈ g2mmn p f i₀ i₁ ζ := by
  classical
  by_cases hk : k = i₀
  · subst hk
    exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · have hgen : diagMap p f (fun j => if j = i₀ then (-1 : (ZMod p)ˣ) else 1) ∈
        g2mmn p f i₀ i₁ ζ := Subgroup.subset_closure (Or.inr (Or.inl rfl))
    have hperm : permMap p f (Equiv.swap i₀ k) ∈ g2mmn p f i₀ i₁ ζ :=
      Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
    have hconj : permMap p f (Equiv.swap i₀ k) *
        diagMap p f (fun j => if j = i₀ then (-1 : (ZMod p)ˣ) else 1) *
        (permMap p f (Equiv.swap i₀ k))⁻¹ =
        diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) := by
      rw [permMap_mul_diagMap_mul_inv]
      congr 1
      funext x
      simp only [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    rw [← hconj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hperm hgen) (Subgroup.inv_mem _ hperm)

private theorem tmo_noncommProd_diagMap (f : Module.Basis (Fin n) (ZMod p) U)
    (d : Fin n → Fin n → (ZMod p)ˣ) :
    ∀ (s : Finset (Fin n))
      (comm : (s : Set (Fin n)).Pairwise (Function.onFun Commute (fun k => diagMap p f (d k)))),
      s.noncommProd (fun k => diagMap p f (d k)) comm = diagMap p f (∏ k ∈ s, d k) := by
  intro s
  induction s using Finset.cons_induction with
  | empty => intro comm; rw [Finset.noncommProd_empty, Finset.prod_empty, diagMap_one]
  | cons a s ha ih =>
    intro comm
    rw [Finset.noncommProd_cons, ih _, Finset.prod_cons ha, ← diagMap_mul]

private theorem tmo_prod_sign :
    (∏ k : Fin n, (fun k j => if j = k then (-1 : (ZMod p)ˣ) else 1) k) =
      (fun _ : Fin n => (-1 : (ZMod p)ˣ)) := by
  funext j
  rw [Finset.prod_apply]
  change (∏ k : Fin n, (if j = k then (-1 : (ZMod p)ˣ) else 1)) = -1
  rw [Fintype.prod_eq_mul_prod_compl j]
  have h : ∏ k ∈ ({j}ᶜ : Finset (Fin n)),
      (if j = k then (-1 : (ZMod p)ˣ) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    simp only [Finset.mem_compl, Finset.mem_singleton] at hk
    simp [Ne.symm hk]
  rw [h, mul_one]; simp

private theorem tmo_diagMap_neg (f : Module.Basis (Fin n) (ZMod p) U) :
    diagMap p f (fun _ : Fin n => (-1 : (ZMod p)ˣ)) =
      (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) := by
  refine f.ext' fun k => ?_
  rw [diagMap_apply_basis, LinearEquiv.neg_apply]; simp

theorem neg_mem_g2mmn (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) :
    (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ g2mmn p f i₀ i₁ ζ := by
  classical
  let sign : Fin n → (Fin n → (ZMod p)ˣ) := fun k j => if j = k then (-1 : (ZMod p)ˣ) else 1
  have hcomm : ∀ k l, Commute (diagMap p f (sign k)) (diagMap p f (sign l)) := by
    intro k l
    show diagMap p f (sign k) * diagMap p f (sign l) =
      diagMap p f (sign l) * diagMap p f (sign k)
    rw [diagMap_mul, diagMap_mul, mul_comm (sign k) (sign l)]
  have comm_univ : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun Commute (fun k => diagMap p f (sign k))) :=
    fun a _ b _ _ => hcomm a b
  have hmem : (Finset.univ.noncommProd (fun k => diagMap p f (sign k)) comm_univ) ∈
      g2mmn p f i₀ i₁ ζ :=
    Finset.noncommProd_induction _ _ _ (fun g => g ∈ g2mmn p f i₀ i₁ ζ)
      (fun a b ha hb => Subgroup.mul_mem _ ha hb) (Subgroup.one_mem _)
      (fun k _ => signMap_mem_g2mmn f ζ k)
  have hfun : (∏ k : Fin n, sign k) = (fun _ : Fin n => (-1 : (ZMod p)ˣ)) := tmo_prod_sign
  rw [← tmo_diagMap_neg (p := p) f, ← hfun,
    ← tmo_noncommProd_diagMap (p := p) f sign Finset.univ comm_univ]
  exact hmem

theorem irredOnSection_fixReflSubgroup_g2mmn (hp : p ≠ 2) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ)
    (l : Fin n) :
    IrredOnSection (fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l)) ⊥
      (Submodule.span (ZMod p) (f '' {i | i ≠ l})) := by
  have hneg : (-1 : ZMod p) ≠ 1 := by
    intro h
    have h2 : (2 : ZMod p) = 0 := by
      calc (2 : ZMod p) = 1 + 1 := (one_add_one_eq_two).symm
        _ = -1 + 1 := by nth_rewrite 1 [← h]; rfl
        _ = 0 := by simp
    exact ZMod.prime_ne_zero p 2 hp h2
  refine irredOnSection_span_of_separating (K := ZMod p) (b := f)
    (B := fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l))
    (S := {i : Fin n | i ≠ l}) f.linearIndependent ?_ ?_
  · intro i hi j hj hij
    refine ⟨diagMap p f (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1), ?_,
      ?_, (-1 : ZMod p), 1, hneg, ?_, ?_⟩
    · refine mem_fixReflSubgroup ?_ (isRefl_diagMap_sign hp f i) ?_
      · exact signMap_mem_g2mmn f ζ i
      · rw [diagMap_apply_basis, apply_ite Units.val, if_neg (Ne.symm (show i ≠ l from hi)),
          Units.val_one, one_smul]
    · intro k hk
      refine ⟨((if k = i then (-1 : (ZMod p)ˣ) else 1) : ZMod p), ?_⟩
      rw [diagMap_apply_basis, apply_ite Units.val, Units.val_one]
    · rw [diagMap_apply_basis, apply_ite Units.val, if_pos rfl, Units.val_neg, Units.val_one]
    · rw [diagMap_apply_basis, apply_ite Units.val, if_neg (Ne.symm hij), Units.val_one, one_smul]
  · intro i hi j hj
    by_cases hij : i = j
    · subst hij
      refine ⟨diagMap p f (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1), ?_,
        (-1 : ZMod p), ?_, ?_⟩
      · refine mem_fixReflSubgroup ?_ (isRefl_diagMap_sign hp f i) ?_
        · exact signMap_mem_g2mmn f ζ i
        · rw [diagMap_apply_basis, apply_ite Units.val, if_neg (Ne.symm (show i ≠ l from hi)),
            Units.val_one, one_smul]
      · exact neg_ne_zero.mpr one_ne_zero
      · rw [diagMap_apply_basis, apply_ite Units.val, if_pos rfl, Units.val_neg, Units.val_one]
    · refine ⟨permMap p f (Equiv.swap i j), ?_, 1, one_ne_zero, ?_⟩
      · refine mem_fixReflSubgroup ?_ (isRefl_permMap_swap f hij) ?_
        · exact Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
        · rw [permMap_apply_basis]
          exact congrArg f (Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj))
      · rw [permMap_apply_basis, Equiv.swap_apply_left]
        exact (one_smul _ _).symm

private theorem tmo_monomial_of_mem_g2mmn (f : Module.Basis (Fin n) (ZMod p) U)
    (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) {g : U ≃ₗ[ZMod p] U} (hg : g ∈ g2mmn p f i₀ i₁ ζ) :
    ∃ (d : Fin n → (ZMod p)ˣ) (σ : Equiv.Perm (Fin n)), g = diagMap p f d * permMap p f σ := by
  rw [g2mmn] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨σ, rfl⟩ | hx
      · exact ⟨1, σ, by rw [diagMap_one, one_mul]⟩
      · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨fun i => if i = i₀ then (-1 : (ZMod p)ˣ) else 1, 1,
            by rw [permMap_one, mul_one]⟩
        · exact ⟨pairUnit p i₀ i₁ ζ, 1, by rw [permMap_one, mul_one]⟩
  | one => exact ⟨1, 1, by rw [diagMap_one, permMap_one, one_mul]⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨dx, σx, hx⟩ := ihx
      obtain ⟨dy, σy, hy⟩ := ihy
      exact ⟨dx * (dy ∘ σx.symm), σx * σy, by rw [hx, hy, mul_diagMap_permMap]⟩
  | inv x _ ihx =>
      obtain ⟨dx, σx, hx⟩ := ihx
      exact ⟨dx⁻¹ ∘ σx, σx⁻¹, by rw [hx, inv_diagMap_permMap]⟩

theorem throughRefl_g2mmn (hp : p ≠ 2) (hn : 3 ≤ n) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) :
    ThroughRefl p (n - 1) (g2mmn p f i₀ i₁ ζ) := by
  intro r hrJ hrrefl
  obtain ⟨d, σ, hgeq⟩ := tmo_monomial_of_mem_g2mmn f i₀ i₁ ζ hrJ
  have hmon : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), ∀ i, r (f i) = c i • f (σ i) :=
    ⟨σ, fun i => (d (σ i) : ZMod p), fun i => by
      rw [hgeq, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]⟩
  obtain ⟨l, hrl⟩ := exists_apply_eq_of_isRefl_of_monomial (f := f) hn hrrefl hmon
  refine ⟨fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l), fixReflSubgroup_le _ _,
    mem_fixReflSubgroup hrJ hrrefl hrl, reflGen_fixReflSubgroup _ _,
    tmo_splitSupport_fixRefl (f := f) hn ?_ (fun σ => Subgroup.subset_closure
      (Or.inl (Set.mem_range_self σ))) l
      (irredOnSection_fixReflSubgroup_g2mmn (f := f) hp i₀ i₁ ζ l)⟩
  intro g hg
  exact tmo_monomial_of_mem_g2mmn f i₀ i₁ ζ hg

theorem tableConclusions_of_monomial (hp : p ≠ 2) (hn : 3 ≤ n) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁)
    {ζ : (ZMod p)ˣ} {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hJ : J = gmmn p f i₀ i₁ ζ ∨ J = g2mmn p f i₀ i₁ ζ) (hT : TableHyp p J) :
    TableConclusions p n J := by
  rcases hJ with rfl | rfl
  · rcases lt_or_ge (orderOf ζ) 3 with hlt | hge
    · exfalso
      obtain ⟨x, hxJ, y, hyJ, hrx, hry, hd⟩ := hT.dLarge
      rcases TableFacts.orderOf_mul_le_three_or_dvd_of_mem_gmmn hp f hi ζ hxJ hyJ hrx hry with
        hle | hdvd
      · omega
      · have := Nat.le_of_dvd (orderOf_pos ζ) hdvd
        omega
    · refine ⟨negOrGen_gmmn (f := f) hi ζ, coprimeWitness_gmmn (f := f) hi ?_,
        throughRefl_gmmn (f := f) hp hn hi hge⟩
      intro hζ1
      rw [hζ1, orderOf_one] at hge
      omega
  · exact ⟨Or.inl (neg_mem_g2mmn (f := f) i₀ i₁ ζ),
      coprimeWitness_of_neg_mem hp (neg_mem_g2mmn (f := f) i₀ i₁ ζ),
      throughRefl_g2mmn (f := f) hp hn i₀ i₁ ζ⟩

end CFSG.StandardType.ZS
