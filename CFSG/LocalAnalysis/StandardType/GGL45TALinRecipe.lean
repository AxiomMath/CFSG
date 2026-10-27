module

public import CFSG.LocalAnalysis.StandardType.GGL45TALinLift
public import CFSG.LocalAnalysis.StandardType.GGL45TAHFour
public import CFSG.LocalAnalysis.StandardType.GGL45TorusPackageConj
public import CFSG.LocalAnalysis.StandardType.GGL45TorusPackagePow
public import CFSG.LocalAnalysis.StandardType.GGL45NtHFourAut
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.StandardType.GGL45TA

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

variable {d : ℕ} {k : Type} [Field k]

theorem SemilinImpl.pow {K : Type} [Group K] {π : LargeEvenSLGroup (Fin d) k →* K}
    {γ : MulAut K} {σ : k ≃+* k} (h : SemilinImpl π γ 1 σ) (m : ℕ) :
    SemilinImpl π (γ ^ m) 1 (σ ^ m) := by
  induction m with
  | zero =>
    intro a b hab
    rw [pow_zero, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [hab, pow_zero, YS09Field.glMap_one, one_mul, inv_one, mul_one]
  | succ m ih =>
    have h1 := ih.mul h
    rwa [map_one, mul_one, ← pow_succ, ← pow_succ] at h1

theorem semilinImpl_of_mem_field {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) k))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k))) :
    ∃ σ : k ≃+* k, SemilinImpl (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) f 1 σ := by
  obtain ⟨σ, hσ⟩ := hf
  refine ⟨σ, fun h h' hh' => hσ h h' ?_⟩
  change ((h' : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) = ((h : GL (Fin d) k) : Matrix _ _ k).map σ
  rw [hh', one_mul, inv_one, mul_one]
  exact YS09Field.coe_glMap _ _

theorem eq_one_of_semilinImpl_one {K : Type} [Group K] (hd : 2 ≤ d)
    {π : LargeEvenSLGroup (Fin d) k →* K}
    (hker : ∀ h ∈ π.ker, (h : GL (Fin d) k) ∈ LargeEvenScalars (Fin d) k) {σ : k ≃+* k}
    (h : SemilinImpl π 1 1 σ) : σ = 1 := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  ext a
  have h1 : π (rootSL hij (Multiplicative.ofAdd a)) =
      π (rootSL hij (Multiplicative.ofAdd (σ a))) :=
    h _ _ (by rw [one_mul, inv_one, mul_one, map_rootSL, toAdd_ofAdd])
  have h2 : (rootSL hij (Multiplicative.ofAdd (σ a)))⁻¹ * rootSL hij (Multiplicative.ofAdd a) ∈
      π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  rw [← map_inv, ← map_mul] at h2
  obtain ⟨c, hc⟩ := hker _ h2
  have h3 := congrArg (fun g : GL (Fin d) k => (g : Matrix (Fin d) (Fin d) k) i j) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hij, coe_rootSL, Matrix.add_apply, Matrix.one_apply_ne hij,
    Matrix.single_apply_same, toAdd_mul, toAdd_inv, toAdd_ofAdd, zero_add] at h3
  change σ a = a
  exact neg_add_eq_zero.mp h3.symm

theorem exists_field_of_orderOf (hd : 2 ≤ d) {p : ℕ} (hp : p.Prime)
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) k))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)))
    (hord : orderOf f = p) :
    ∃ σ : k ≃+* k, SemilinImpl (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) f 1 σ ∧
      σ ^ p = 1 ∧ σ ≠ 1 := by
  obtain ⟨σ, hσ⟩ := semilinImpl_of_mem_field hf
  refine ⟨σ, hσ, ?_, ?_⟩
  · have hfp : f ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one f
    have h1 := hσ.pow p
    rw [hfp] at h1
    exact eq_one_of_semilinImpl_one hd projMk_ker_le h1
  · rintro rfl
    have h1 : f = 1 := implements_injective_of_surj (QuotientGroup.mk'_surjective _)
      hσ.implements (implements_one_of_scalar ⟨1, map_one _⟩)
    rw [h1, orderOf_one] at hord
    exact hp.one_lt.ne hord

variable {K : Type} [Group K]

theorem implements_inducedAut {π : LargeEvenSLGroup (Fin d) k →* K}
    {θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) k)}
    (hθ : ∀ h, θ (π h : K ⧸ Subgroup.center K) = LargeEvenProjMk _ h) {e : MulAut K}
    {x : GL (Fin d) k} (hx : Implements π e x) :
    Implements (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) (ggInducedAut θ e) x := by
  intro h h' hh'
  rw [← hθ, ggInducedAut_apply, hx h h' hh', hθ]

theorem implements_of_inducedAut (hd : 3 ≤ d) {π : LargeEvenSLGroup (Fin d) k →* K}
    {θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) k)}
    (hθ : ∀ h, θ (π h : K ⧸ Subgroup.center K) = LargeEvenProjMk _ h) {α : MulAut K}
    {A : GL (Fin d) k}
    (hA : Implements (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) (ggInducedAut θ α) A) :
    Implements π α A := by
  refine implements_of_mod_center hd fun y => ?_
  have h1 : θ ((α (π y) : K) : K ⧸ Subgroup.center K) =
      θ ((π (conjSL A y) : K) : K ⧸ Subgroup.center K) := by
    rw [← ggInducedAut_apply, hθ, hθ]
    exact hA y (conjSL A y) rfl
  have h2 := θ.injective h1
  rw [QuotientGroup.eq] at h2
  exact h2

theorem semilinImpl_of_inducedAut (hd : 3 ≤ d) {π : LargeEvenSLGroup (Fin d) k →* K}
    {θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) k)}
    (hθ : ∀ h, θ (π h : K ⧸ Subgroup.center K) = LargeEvenProjMk _ h) {α : MulAut K}
    {g : GL (Fin d) k} {σ : k ≃+* k}
    (h : SemilinImpl (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) (ggInducedAut θ α) g σ) :
    SemilinImpl π α g σ := by
  refine semilinImpl_of_mod_center hd fun y => ?_
  have h1 : θ ((α (π y) : K) : K ⧸ Subgroup.center K) =
      θ ((π (semiSL g σ y) : K) : K ⧸ Subgroup.center K) := by
    rw [← ggInducedAut_apply, hθ, hθ]
    exact h y (semiSL g σ y) rfl
  have h2 := θ.injective h1
  rw [QuotientGroup.eq] at h2
  exact h2

private theorem inducedAut_eq_of_induces {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R)
    {ψ : MulAut K} {φ : MulAut R} (h : LargeEvenInduces θ (fun k k' => k' = ψ k) φ) :
    φ = ggInducedAut θ ψ := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [ggInducedAut_apply]
    exact h l (ψ l) rfl

theorem pow_apply_of_forall_apply {τ : k ≃+* k} {q : ℕ} (hτ : ∀ a, τ a = a ^ q) (j : ℕ)
    (a : k) : (τ ^ j) a = a ^ q ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', RingAut.mul_apply, ih, map_pow, hτ, ← pow_mul, ← pow_succ']

theorem exists_frobPow_of_dvd [Finite k] {p n : ℕ} (hp : p.Prime) (hk : Nat.card k = 2 ^ n)
    (hpn : p ∣ n) (hn : 1 ≤ n) :
    ∃ τ : k ≃+* k, (∀ a, τ a = a ^ 2 ^ (n / p)) ∧ τ ^ p = 1 ∧ τ ≠ 1 := by
  classical
  haveI := Fintype.ofFinite k
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP k 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hk])
  have hτ : ∀ a : k, iterateFrobeniusEquiv k 2 (n / p) a = a ^ 2 ^ (n / p) := fun a => rfl
  refine ⟨iterateFrobeniusEquiv k 2 (n / p), hτ, ?_, fun h1 => ?_⟩
  · ext a
    rw [pow_apply_of_forall_apply hτ, ← pow_mul, Nat.div_mul_cancel hpn, ← hk,
      Nat.card_eq_fintype_card, FiniteField.pow_card]
    rfl
  ·
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
    have hm1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
    have hmn : n / p < n := Nat.div_lt_self (by omega) hp.one_lt
    have hq₀ : 2 ≤ 2 ^ (n / p) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n / p) := Nat.pow_le_pow_right (by norm_num) hm1
    have hgq : g ^ 2 ^ (n / p) = g := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      exact DFunLike.congr_fun h1 (g : k)
    have hg1 : g ^ (2 ^ (n / p) - 1) = 1 := by
      have h2 : g ^ (2 ^ (n / p) - 1) * g = 1 * g := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, hgq]
      exact mul_right_cancel h2
    have h3 := orderOf_dvd_of_pow_eq_one hg1
    rw [hg, Nat.card_units, hk] at h3
    have h4 := Nat.le_of_dvd (by omega) h3
    have h5 : 2 ^ (n / p) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hmn
    omega

private theorem dvd_q₀_sub_one {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hq : (p : ℤ) ∣ 2 ^ n - 1) : (p : ℤ) ∣ ((2 ^ (n / p) : ℕ) : ℤ) - 1 := by
  haveI := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hq ⊢
  push_cast at hq ⊢
  have h1 : ((2 : ZMod p) ^ (n / p)) ^ p = (2 : ZMod p) ^ (n / p) := ZMod.pow_card _
  rw [← pow_mul, Nat.div_mul_cancel hpn] at h1
  rw [← h1]
  exact hq

theorem ggL45H4Raw_linear [Finite k] (hd : 3 ≤ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (lab : LargeEvenLabel) :
    GGL45H4Raw p lab (LargeEvenProj (LargeEvenSLGroup (Fin d) k))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k))) :=
  ggL45H4Raw_of_aut hp
    (fun _ => CFSG.LocalAnalysis.GLTheoremA.T156.Lin.isSimpleGroup_proj' (by omega) k (Or.inl hd))
    (ggL45NtAut_of_inputs hp
      (RecipeFieldLinear.ggRawInnField_linear (by omega) (Or.inl hd) hp.ne_one)
      (fun _ _ => ggInndiagNormal_linear hd)
      (RecipeFieldLinear.ggRawPCyclic_linear (by omega) (hp.odd_of_ne_two hp2)))

theorem ggL45TorusHRaw_linear_case2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (htag : lab.tag = .A) (hrank : lab.rank + 1 = d) (hpd : p ∣ d)
    (hq : (p : ℤ) ∣ 2 ^ lab.n - 1) [Finite k] (hk : Nat.card k = 2 ^ lab.n) :
    GGL45TorusHRaw p lab (LargeEvenProj (LargeEvenSLGroup (Fin d) k))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k))) := by
  intro K _ _ θ hK hA2 ψ E hyp
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hd3 : 3 ≤ d := hp3.trans (Nat.le_of_dvd (by omega) hpd)
  have hπR : Function.Surjective (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) :=
    QuotientGroup.mk'_surjective _
  have hH4 := ggL45H4Raw_linear (k := k) hd3 hp hp2 lab
  rw [← RecipeFieldLinear.coe_recI] at hyp hH4 ⊢
  obtain ⟨f, hf, u, hu, hford, hind⟩ := hyp.2.1
  have hψbar : ggInducedAut θ ψ = u * f * u⁻¹ := (inducedAut_eq_of_induces θ hind).symm
  obtain ⟨σ, hσ, hσp, hσ1⟩ := exists_field_of_orderOf (by omega) hp hf hford
  have hpn : p ∣ lab.n := by
    obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic Nat.prime_two k hk
    haveI : Fact p.Prime := ⟨hp⟩
    rw [← hcard, ← orderOf_eq_prime hσp hσ1]
    exact orderOf_dvd_natCard σ
  have hn1 : 1 ≤ lab.n := by
    by_contra h0
    have h1 := Finite.one_lt_card (α := k)
    rw [hk, show lab.n = 0 by omega, pow_zero] at h1
    exact lt_irrefl _ h1
  have hn3 : 3 ≤ lab.n := hp3.trans (Nat.le_of_dvd (by omega) hpn)
  obtain ⟨τ, hτ, hτp, hτ1⟩ := exists_frobPow_of_dvd (k := k) hp hk hpn hn1
  haveI : IsCyclic (k ≃+* k) := (card_ringAut_and_isCyclic Nat.prime_two k hk).2
  obtain ⟨j, hj, hσj⟩ := ggL45NtAutAsm_exists_pow_of_cyclic hp hσp hτp hσ1 hτ1
  obtain ⟨j', -, hjj'⟩ := Nat.exists_mul_mod_eq_one_of_coprime (k := p) (n := j)
    (hp.coprime_iff_not_dvd.mpr hj).symm hp.one_lt
  have hj' : ¬ p ∣ j' := by
    intro hdiv
    have h0 : j * j' % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdiv j)
    omega
  have hσj' : σ ^ j' = τ := by
    rw [hσj, ← pow_mul, pow_eq_pow_mod _ hτp, hjj', pow_one]
  have hchar : CharP k 2 := by
    haveI := Fintype.ofFinite k
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := lab.n) (by rw [← Nat.card_eq_fintype_card, hk])
  have hk8 : 8 ≤ Nat.card k := by
    rw [hk]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn3
  obtain ⟨π, hπs, hπker, hθ⟩ := exists_cover_linear hd3 hk8 hK θ
  have hu' : u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) Set.univ := by
    rw [← RecipeFieldLinear.coe_recI]; exact hu
  obtain ⟨A, -, hA0⟩ := hu'
  have hA : Implements (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) u A := hA0
  obtain ⟨ũ, hũ⟩ := exists_implements_lift hπs hπker A
  have hũbar : ggInducedAut θ ũ = u :=
    implements_injective_of_surj hπR (implements_inducedAut hθ hũ) hA
  have hũI : GGL45InducesIn θ (RecipeFieldLinear.recI d k : Set (MulAut _)) ũ :=
    (ggL45_inducesIn_iff θ _ ũ).mpr (by rw [hũbar]; exact hu)
  have hyp₁ := ggL45TorusKGHyp_conj p lab (RecipeFieldLinear.recI d k) _ θ ũ hũI ψ E hyp
  have hψ₁bar : ggInducedAut θ (ũ⁻¹ * ψ * ũ) = f := by
    rw [map_mul, map_mul, map_inv, hũbar, hψbar]; group
  have hF : ∀ g ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)),
      ∀ m : ℕ, g ^ m ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) :=
    fun g hg m => YS09Field.matField_pow_closed _ (fun σ h hh => YS09Field.sl_map_mem σ h hh) _ g
      hg m
  have hyp₂ := ggL45TorusKGHyp_pow hp hF hj' hyp₁
  have hψ₂R : SemilinImpl (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k))
      (ggInducedAut θ ((ũ⁻¹ * ψ * ũ) ^ j')) 1 τ := by
    rw [map_pow, hψ₁bar, ← hσj']
    exact hσ.pow j'
  obtain ⟨h1, -, h3, h4, -, h6, h7, h8, h9, h10⟩ := id hyp₂
  have hEimpl : ∀ e ∈ E.map (MulAut.conj ũ⁻¹).toMonoidHom, ∃ x : GL (Fin d) k, Implements π e x := by
    intro e he
    have he' := (ggL45_inducesIn_iff θ _ e).mp (h6 e he)
    rw [RecipeFieldLinear.coe_recI] at he'
    obtain ⟨A', -, hA'⟩ := he'
    exact ⟨A', implements_of_inducedAut hd3 hθ hA'⟩
  have hsemi : ∀ γ : MulAut K, GGL45IsPElt p γ →
      ∃ (g : GL (Fin d) k) (σ' : k ≃+* k) (m : ℕ), σ' ^ p ^ m = 1 ∧ SemilinImpl π γ g σ' := by
    rintro γ ⟨a, ha⟩
    have hγR : GGL45IsPElt p (ggInducedAut θ γ) := ⟨a, by rw [← map_pow, ha, map_one]⟩
    obtain ⟨g, σ', m, hσ', hg⟩ := exists_semilin_of_pElt hd3 hp hp2 hγR
    exact ⟨g, σ', m, hσ', semilinImpl_of_inducedAut hd3 hθ hg⟩
  have hpik : ∃ P : Subgroup (MulAut K), P ≤ E.map (MulAut.conj ũ⁻¹).toMonoidHom ∧
      Nat.card (E.map (MulAut.conj ũ⁻¹).toMonoidHom) ≤ p * Nat.card P ∧ ∀ e ∈ P,
      ∃ γ : MulAut K, GGL45IsPElt p γ ∧
        (∀ e' ∈ E.map (MulAut.conj ũ⁻¹).toMonoidHom, γ * e' = e' * γ) ∧
        e = γ * ((ũ⁻¹ * ψ * ũ) ^ j')⁻¹ * γ⁻¹ * (ũ⁻¹ * ψ * ũ) ^ j' := by
    obtain ⟨P, hPE, hPc, hP⟩ := h10
    refine ⟨P, hPE, hPc, fun e he => ?_⟩
    obtain ⟨γ, hγ1, hγ2, -, hγ4⟩ := hP e he
    exact ⟨γ, hγ1, hγ2, hγ4⟩
  have ha2 : d = 3 → p ∣ Nat.card (Subgroup.center K) := by
    intro hd
    have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hd ▸ hpd)
    have hlab2 : GGLabelA2 lab := by
      unfold GGLabelA2
      refine ⟨by omega, by omega, Or.inl ⟨htag, ?_⟩⟩
      have h2 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
      have h3' : ((3 : ℕ) : ℤ) ∣ ((2 ^ lab.n - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub h2]
        rw [hp3'] at hq
        simpa using hq
      exact Int.natCast_dvd_natCast.mp h3'
    exact hA2 hlab2 hp3'
  let S : LinSetting p (2 ^ (lab.n / p)) d k K ((ũ⁻¹ * ψ * ũ) ^ j')
      (E.map (MulAut.conj ũ⁻¹).toMonoidHom) :=
    { π := π
      surj := hπs
      ker_le := hπker
      τ := τ
      τ_apply := hτ
      hp := hp
      hp2 := hp2
      char_two := hchar
      card_k := by rw [← pow_mul, Nat.div_mul_cancel hpn]; exact hk
      dvd_q₀ := dvd_q₀_sub_one hp hpn hq
      dvd_d := hpd
      three_le := hd3
      ψ_impl := semilinImpl_of_inducedAut hd3 hθ hψ₂R
      E_impl := hEimpl
      semilin := hsemi
      ψ_pow := h1
      elem := h3
      card_E := h4
      comm := h7
      sat := h8
      rk := fun R₀ Q a b c e g h => (h9 R₀ Q a b c e g h).1
      pik := hpik
      a2 := ha2 }
  have h123 := S.torusH123 hθ
  rw [← RecipeFieldLinear.coe_recI] at h123
  have hH₂ := ggL45TorusH_of_parts h123 (hH4 K θ hK _ _ hyp₂)
  have hH₁ := ggL45TorusH_pow hp hyp₁.1 hj' hH₂
  have hũinvI : GGL45InducesIn θ (RecipeFieldLinear.recI d k : Set (MulAut _)) ũ⁻¹ :=
    (ggL45_inducesIn_iff θ _ ũ⁻¹).mpr (by
      rw [map_inv, hũbar]; exact (RecipeFieldLinear.recI d k).inv_mem hu)
  have hH := ggL45TorusH_conj p (RecipeFieldLinear.recI d k) θ ũ⁻¹ hũinvI _ _ hH₁
  have hψeq : ũ⁻¹⁻¹ * (ũ⁻¹ * ψ * ũ) * ũ⁻¹ = ψ := by group
  have hEeq : (E.map (MulAut.conj ũ⁻¹).toMonoidHom).map (MulAut.conj ũ⁻¹⁻¹).toMonoidHom = E := by
    rw [Subgroup.map_map]
    have hid : (MulAut.conj ũ⁻¹⁻¹).toMonoidHom.comp (MulAut.conj ũ⁻¹).toMonoidHom =
        MonoidHom.id _ := by
      ext e : 1
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply, inv_inv]
      group
    rw [hid, Subgroup.map_id]
  rw [hψeq, hEeq] at hH
  exact hH

theorem largeEvenLabelAll_torusHRaw_linear_case2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (htag : lab.tag = .A) (hpd : p ∣ lab.rank + 1)
    (hq : (p : ℤ) ∣ 2 ^ lab.n - 1) : LargeEvenLabelAll lab (GGL45TorusHRaw p lab) := by
  obtain ⟨t, rank, n⟩ := lab
  dsimp only at htag hpd hq
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact NbrGraphLinear.recipeLinear_all (fun k _ _ hk =>
    ggL45TorusHRaw_linear_case2 hp hp2 (lab := ⟨.A, rank, n⟩) rfl rfl hpd hq hk) hQ

theorem ggL45TorusHKnownFormsOn_famTypeACase2_linear :
    GGL45TorusHKnownFormsOn fun p lab => GGL45FamTypeACase2 p lab ∧ lab.tag = .A := by
  rintro p hp hp2 lab - - ⟨⟨⟨-, hpd⟩, hq⟩, htag⟩
  refine largeEvenLabelAll_torusHRaw_linear_case2 hp hp2 htag hpd ?_
  have he : GGL45Eps lab = 1 := by simp [GGL45Eps, htag]
  rwa [he] at hq

end CFSG.StandardType.GGL45TA
