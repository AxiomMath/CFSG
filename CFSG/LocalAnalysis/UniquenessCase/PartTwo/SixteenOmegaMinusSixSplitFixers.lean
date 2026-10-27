module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Out
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8SimQuad
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoPair
public import CFSG.ClassicalGroups.Orthogonal.MinusLeviBlocks
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open CFSG.RankThree.GF2n.Stroth80
open CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven
open CFSG.LieType.Universal.Spin
open Matrix

theorem s16g_actual_fixers_of_elem_cube_split_omegaMinus_six
    {X : Type} [Group X] [Finite X]
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {b d : K} (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1)
    (hpAut : ¬ p ∣ Nat.card (RingAut K))
    (ρ : X →* MulAut (Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K)))
    (hΓρ : (StatedOmega (StatedQuadMinus 3 K b d)).map
      (s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) ≤ ρ.range)
    (hρN : ρ.range ≤ s16gNorm (StatedOmega (StatedQuadMinus 3 K b d)))
    (E : Subgroup X) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3) :
    ∀ x : Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K), x ≠ 1 →
      ∃ B : Subgroup X, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧
        ∀ b ∈ B, ρ b x = x := by
  classical
  let ι : Type := Fin 2 ⊕ Fin 2 ⊕ Fin 2
  let Γ : Subgroup (GL ι K) := StatedOmega (StatedQuadMinus 3 K b d)
  have : Fact p.Prime := ⟨hp⟩
  have : IsMulCommutative ↥E := hE.1
  let : CommGroup ↥E := CommGroup.mk (fun a b => hE.1.is_comm.comm a b)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have htp : ∀ t : Kˣ, orderOf t = p → t ^ p = 1 := fun t ht => by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hpK' : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units K]
    exact hpK
  have hp_ne_zero : (p : K) ≠ 0 := by
    intro h0
    have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
    obtain ⟨m, hm⟩ := hpodd
    obtain ⟨n, hn⟩ := h2dvd
    omega
  have hΓac : AddCommutantScalar Γ :=
    addCommutantScalar_statedOmegaMinus (m := 3) (K := K) (b := b) (c := d) (by norm_num) hirr
  have hΓQ : ∀ A ∈ Γ, ∀ v : ι → K,
      quadMinus 3 K b d (((A : GL ι K) : Matrix ι ι K) *ᵥ v) = quadMinus 3 K b d v := by
    intro A hA v
    rw [show Γ = StatedOmega (StatedQuadMinus 3 K b d) from rfl,
      statedOmega_eq_comap (coe_quadMinus 3 K b d)] at hA
    rw [Subgroup.mem_comap] at hA
    have hO : (toLinEquiv ι K).toMonoidHom A ∈
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b d) :=
      Subgroup.commutator_le_self _ hA
    have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hO v
    rwa [MulEquiv.coe_toMonoidHom, toLinEquiv_apply] at h
  have hEN : E.map ρ ≤ s16gNorm Γ := (Subgroup.map_le_range ρ E).trans hρN
  have hEp : IsPGroup p ↥(E.map ρ) := (IsElemAbelian.isPGroup hE).map ρ
  have hElin : E.map ρ ≤ s16gLin ι K :=
    s16g_le_lin_of_coprime hΓac hp hpAut hEN hEp
  have hpre : ∀ e : E, ∃ g : GL ι K, s16gNatHom ι K g = ρ (e : X) := by
    intro e
    have hmem : ρ (e : X) ∈ s16gLin ι K :=
      hElin (Subgroup.mem_map_of_mem ρ e.2)
    exact MonoidHom.mem_range.1 (by simpa [s16gLin] using hmem)
  let gE : E → GL ι K := fun e => Classical.choose (hpre e)
  have hgE : ∀ e : E, s16gNatHom ι K (gE e) = ρ (e : X) := fun e =>
    Classical.choose_spec (hpre e)
  have hgE_mul : ∀ a b : E, gE (a * b) = gE a * gE b := by
    intro a b
    apply s16gNatHom_injective
    rw [hgE (a * b), map_mul, hgE a, hgE b]
    change ρ ((a : X) * (b : X)) = ρ (a : X) * ρ (b : X)
    rw [map_mul]
  have hgE_one : gE 1 = 1 := by
    apply s16gNatHom_injective
    rw [hgE 1, map_one]
    change ρ (1 : X) = 1
    rw [map_one]
  let rep : E →* Module.End K (ι → K) :=
    { toFun := fun e => Matrix.toLin' (((gE e : GL ι K) : Matrix ι ι K))
      map_one' := by
        rw [hgE_one, Units.val_one, Matrix.toLin'_one]
        rfl
      map_mul' := fun a b => by
        change Matrix.toLin' (((gE (a * b) : GL ι K) : Matrix ι ι K)) =
          Matrix.toLin' (((gE a : GL ι K) : Matrix ι ι K)) *
            Matrix.toLin' (((gE b : GL ι K) : Matrix ι ι K))
        rw [hgE_mul, Units.val_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp] }
  have hrep_apply : ∀ (e : E) (v : ι → K),
      rep e v = ((gE e : GL ι K) : Matrix ι ι K) *ᵥ v := fun e v =>
    Matrix.toLin'_apply _ _
  let N : (E →* Kˣ) → Submodule K (ι → K) :=
    fun χ => ⨅ e : E, (rep e).eigenspace (χ e : K)
  have hint : DirectSum.IsInternal N := by
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpK'
    have hprim : IsPrimitiveRoot (ζ : K) p :=
      IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
    have : HasEnoughRootsOfUnity K p := ⟨⟨ζ, hprim⟩, inferInstance⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    have hexp : Monoid.exponent ↥E ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (hE.2 (a : X) a.2)
    have : HasEnoughRootsOfUnity K (Monoid.exponent ↥E) :=
      HasEnoughRootsOfUnity.of_dvd K (m := Monoid.exponent ↥E) (n := p) hexp
    have hunit : IsUnit (Nat.card ↥E : K) := by
      rw [hEcard, Nat.cast_pow]
      exact (IsUnit.mk0 (p : K) hp_ne_zero).pow 3
    have hIndep : iSupIndep (fun χ : E →* Kˣ => N χ) :=
      TauCeti.iSupIndep_iInf_eigenspace_unitHom
        (G := ↥E) (K := K) (V := ι → K) (ρ := rep)
    have hTop : (⨆ χ : E →* Kˣ, N χ) = ⊤ :=
      TauCeti.iSup_iInf_eigenspace_unitHom_eq_top_of_commGroup
        (G := ↥E) (K := K) (V := ι → K) (ρ := rep) hunit
    exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hIndep hTop
  have hQnd : (QuadraticMap.polarBilin (quadMinus 3 K b d)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr
  obtain ⟨μ, hμquad, -⟩ :=
    s16g_exists_mult_quadratic (Q := quadMinus 3 K b d) hQnd hΓac hΓQ
  have hgnorm : ∀ e : E, gE e ∈ Subgroup.normalizer (Γ : Set (GL ι K)) := by
    intro e
    exact (s16g_mem_norm_natHom_iff Γ (gE e)).1 (by
      rw [hgE e]
      exact hρN (MonoidHom.mem_range.2 ⟨e, rfl⟩))
  let μe : E → Kˣ := fun e => μ ⟨gE e, hgnorm e⟩
  have hker_card : ∀ χ : E →* Kˣ, p ^ 2 ≤ Nat.card ↥χ.ker := by
    intro χ
    have hχrange : Nat.card ↥χ.range ≤ p := by
      refine CFSG.AGLEmbedding.card_le_of_isCyclic_of_pow_eq_one χ.range ?_
      rintro y ⟨e, rfl⟩
      rw [← map_pow, show e ^ p = 1 from Subtype.ext (hE.2 (e : X) e.2), map_one]
    have hprod : Nat.card ↥E = Nat.card ↥χ.ker * Nat.card ↥χ.range :=
      (Subgroup.card_ker_mul_card_range χ).symm
    have hle : Nat.card ↥E ≤ Nat.card ↥χ.ker * p := by
      rw [hprod]
      exact Nat.mul_le_mul_left _ hχrange
    have hp3 : p ^ 3 = p ^ 2 * p := by ring
    have hle' : p ^ 2 * p ≤ Nat.card ↥χ.ker * p := by
      rw [← hp3, ← hEcard]
      exact hle
    exact Nat.le_of_mul_le_mul_right hle' hp.pos
  have hker_nc : ∀ χ : E →* Kˣ, ¬ IsCyclic ↥χ.ker := by
    intro χ hcyc
    have : IsCyclic ↥χ.ker := hcyc
    have hle : Nat.card ↥χ.ker ≤ p := by
      simpa using CFSG.AGLEmbedding.card_le_of_isCyclic_of_pow_eq_one
        (⊤ : Subgroup ↥χ.ker)
        (fun x _ => Subtype.ext (Subtype.ext (hE.2 (x.1 : E) (x.1 : E).2)))
    have hge := hker_card χ
    nlinarith [hp.one_lt]
  have kernel_fixer : ∀ (χ : E →* Kˣ) (v : ι → K), v ∈ N χ →
      ∃ B : Subgroup X, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧
        ∀ b ∈ B, ρ b (Multiplicative.ofAdd v) = Multiplicative.ofAdd v := by
    intro χ v hvN
    let B : Subgroup X := χ.ker.map E.subtype
    have hχkerp : IsPGroup p ↥χ.ker :=
      (((IsElemAbelian.isPGroup hE).of_equiv (Subgroup.topEquiv (G := ↥E)).symm).to_le
        (le_top : χ.ker ≤ ⊤))
    have hBp : IsPGroup p B := IsPGroup.map hχkerp E.subtype
    have hBnc : ¬ IsCyclic ↥B := by
      intro hB
      exact hker_nc χ
        ((Subgroup.equivMapOfInjective χ.ker E.subtype E.subtype_injective).isCyclic.mpr hB)
    refine ⟨B, hBp, hBnc, ?_⟩
    intro b hb
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hb
    have hχe : χ e = 1 := MonoidHom.mem_ker.1 he
    have hrep : rep e v = (χ e : K) • v :=
      Module.End.mem_eigenspace_iff.mp
        (iInf_le (fun e : E => (rep e).eigenspace (χ e : K)) e hvN)
    have hmat : ((gE e : GL ι K) : Matrix ι ι K) *ᵥ v = v := by
      rw [← hrep_apply e v, hrep, hχe, Units.val_one, one_smul]
    change ρ (↑e : X) (Multiplicative.ofAdd v) = Multiplicative.ofAdd v
    rw [← hgE e, s16gNatHom_apply, toAdd_ofAdd, hmat]
  have conjugate_fixer : ∀ (m : X) (B : Subgroup X) (y x : Multiplicative (ι → K)),
      IsPGroup p B → ¬ IsCyclic ↥B → (∀ b ∈ B, ρ b y = y) → ρ m y = x →
      ∃ B' : Subgroup X, IsPGroup p B' ∧ ¬ IsCyclic ↥B' ∧ ∀ b ∈ B', ρ b x = x := by
    intro m B y x hBp hBnc hBfix hm
    refine ⟨B.map (MulAut.conj m).toMonoidHom, hBp.map _, ?_, ?_⟩
    · intro hcyc
      exact hBnc ((Subgroup.equivMapOfInjective B (MulAut.conj m).toMonoidHom
        (MulAut.conj m).injective).isCyclic.mpr hcyc)
    · intro b hb
      obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
      have hconj : (MulAut.conj m).toMonoidHom b₀ = m * b₀ * m⁻¹ := by
        change (MulAut.conj m) b₀ = m * b₀ * m⁻¹
        rw [MulAut.conj_apply]
      rw [hconj]
      calc ρ (m * b₀ * m⁻¹) x
          = ρ m (ρ b₀ ((ρ m)⁻¹ x)) := by
              simp [map_mul, map_inv, MulAut.mul_apply]
        _ = ρ m (ρ b₀ y) := by rw [← hm, MulAut.inv_apply_self]
        _ = ρ m y := by rw [hBfix b₀ hb₀]
        _ = x := hm
  intro x hx1
  let vx : ι → K := Multiplicative.toAdd x
  have hx0 : vx ≠ 0 := by
    intro h0
    apply hx1
    have : Multiplicative.ofAdd vx = x := ofAdd_toAdd x
    rw [← this, h0, ofAdd_zero]
  by_cases hQx : quadMinus 3 K b d vx = 0
  ·
    by_cases hbad : ∃ χ : E →* Kˣ, N χ ≠ ⊥ ∧ ∃ e : E, (χ e : K) ^ 2 ≠ (μe e : K)
    ·
      obtain ⟨χ, hNχ, e, he⟩ := hbad
      obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hNχ
      have hrep_e : rep e v = (χ e : K) • v :=
        Module.End.mem_eigenspace_iff.mp
          (iInf_le (fun e : E => (rep e).eigenspace (χ e : K)) e hvN)
      have hQ1 : quadMinus 3 K b d (rep e v) = (χ e : K) ^ 2 * quadMinus 3 K b d v := by
        rw [hrep_e, QuadraticMap.map_smul, smul_eq_mul]
        ring
      have hQ2 : quadMinus 3 K b d (rep e v) = (μe e : K) * quadMinus 3 K b d v := by
        rw [hrep_apply e v]
        exact hμquad ⟨gE e, hgnorm e⟩ v
      have hzero : ((χ e : K) ^ 2 - (μe e : K)) * quadMinus 3 K b d v = 0 := by
        have hsame : (χ e : K) ^ 2 * quadMinus 3 K b d v =
            (μe e : K) * quadMinus 3 K b d v := by
          rw [← hQ1, hQ2]
        rw [sub_mul, hsame, sub_self]
      have hQv : quadMinus 3 K b d v = 0 :=
        (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr he)
      obtain ⟨γ, hγΓ, hγv⟩ :=
        statedOmegaMinus_exists_mulVec_eq (m := 3) (by norm_num) hirr hv0 hx0 (by
          rw [hQv, hQx])
      have hγmem : s16gNatHom ι K γ ∈ ρ.range :=
        hΓρ (Subgroup.mem_map_of_mem (s16gNatHom ι K) hγΓ)
      obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 hγmem
      obtain ⟨B, hBp, hBnc, hBfix⟩ := kernel_fixer χ v hvN
      have hmy : ρ m (Multiplicative.ofAdd v) = x := by
        rw [hm, s16gNatHom_apply, toAdd_ofAdd, hγv, ofAdd_toAdd]
      exact conjugate_fixer m B (Multiplicative.ofAdd v) x hBp hBnc hBfix hmy
    ·
      have hsquare : ∀ χ : E →* Kˣ, N χ ≠ ⊥ → ∀ e : E,
          (χ e : K) ^ 2 = (μe e : K) := by
        intro χ hNχ e
        by_contra hne
        exact hbad ⟨χ, hNχ, e, hne⟩
      have hex : ∃ χ : E →* Kˣ, N χ ≠ ⊥ := by
        by_contra h
        have hallbot : ∀ χ : E →* Kˣ, N χ = ⊥ := by
          intro χ
          by_contra hne
          exact h ⟨χ, hne⟩
        have hbot : (⨆ χ : E →* Kˣ, N χ) = ⊥ := iSup_eq_bot.mpr hallbot
        rw [hint.submodule_iSup_eq_top] at hbot
        exact top_ne_bot hbot
      obtain ⟨χ0, hN0⟩ := hex
      have hall_eq : ∀ χ : E →* Kˣ, N χ ≠ ⊥ → χ = χ0 := by
        intro χ hNχ
        ext e
        exact CharTwo.sq_inj.mp (by rw [hsquare χ hNχ e, hsquare χ0 hN0 e])
      have hscalar : ∀ e : E, rep e = (χ0 e : K) • (1 : Module.End K (ι → K)) := by
        intro e
        have heig : (rep e).eigenspace (χ0 e : K) = ⊤ := by
          refine le_antisymm le_top ?_
          rw [← hint.submodule_iSup_eq_top]
          refine iSup_le fun χ => ?_
          by_cases hNχ : N χ = ⊥
          · simp [hNχ]
          · rw [hall_eq χ hNχ]
            change (⨅ a : E, (rep a).eigenspace (χ0 a : K)) ≤
              (rep e).eigenspace (χ0 e : K)
            exact iInf_le _ e
        refine LinearMap.ext fun v => ?_
        have hv : v ∈ (rep e).eigenspace (χ0 e : K) := by rw [heig]; trivial
        have := Module.End.mem_eigenspace_iff.mp hv
        simpa using this
      have hxmem : vx ∈ N χ0 := by
        change vx ∈ ⨅ e : E, (rep e).eigenspace (χ0 e : K)
        rw [Submodule.mem_iInf]
        intro e
        rw [Module.End.mem_eigenspace_iff, hscalar e]
        simp
      obtain ⟨B, hBp, hBnc, hBfix⟩ := kernel_fixer χ0 vx hxmem
      exact ⟨B, hBp, hBnc, fun b hb => by
        have hxeq : Multiplicative.ofAdd vx = x := ofAdd_toAdd x
        rw [← hxeq]
        exact hBfix b hb⟩
  ·
    have hQx' : quadMinus 3 K b d vx ≠ 0 := hQx
    obtain ⟨r, hr⟩ :=
      (Finite.injective_iff_surjective.mp (CharTwo.sq_injective (R := K)))
        (quadMinus 3 K b d vx)
    have hr' : r ^ 2 = quadMinus 3 K b d vx := by simpa using hr
    have hr0 : r ≠ 0 := by
      intro h0
      apply hQx'
      rw [← hr', h0]
      simp
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' p hpK'
    let d0 : Fin 2 → Kˣ := Pi.mulSingle 0 t
    let d1 : Fin 2 → Kˣ := Pi.mulSingle 1 t
    have ht1 : t ^ p = 1 := htp t ht
    have hd0 : ∀ j, d0 j ^ p = 1 := by
      intro j
      by_cases hj : j = 0
      · subst hj
        simpa [d0] using ht1
      · simp [d0, Pi.mulSingle, hj]
    have hd1 : ∀ j, d1 j ^ p = 1 := by
      intro j
      by_cases hj : j = 1
      · subst hj
        simpa [d1] using ht1
      · simp [d1, Pi.mulSingle, hj]
    let γ0Γ : Γ := minusDiagGL (b := b) (c := d) (n := 3) (r := p) hpodd d0 hd0
    let γ1Γ : Γ := minusDiagGL (b := b) (c := d) (n := 3) (r := p) hpodd d1 hd1
    let g0 : GL ι K := (γ0Γ : GL ι K)
    let g1 : GL ι K := (γ1Γ : GL ι K)
    have hγ0ord : orderOf g0 = p := by
      have h1 : orderOf γ0Γ = p := by
        rw [show γ0Γ = minusDiagGL (b := b) (c := d) (n := 3) (r := p) hpodd
            (Pi.mulSingle (0 : Fin 2) t) hd0 from rfl,
          orderOf_minusDiagGL_mulSingle (b := b) (c := d) (n := 3) hpodd t 0 hd0, ht]
      rw [show g0 = ((γ0Γ : Γ) : GL ι K) from rfl, Subgroup.orderOf_coe, h1]
    have hγ1ord : orderOf g1 = p := by
      have h1 : orderOf γ1Γ = p := by
        rw [show γ1Γ = minusDiagGL (b := b) (c := d) (n := 3) (r := p) hpodd
            (Pi.mulSingle (1 : Fin 2) t) hd1 from rfl,
          orderOf_minusDiagGL_mulSingle (b := b) (c := d) (n := 3) hpodd t 1 hd1, ht]
      rw [show g1 = ((γ1Γ : Γ) : GL ι K) from rfl, Subgroup.orderOf_coe, h1]
    have hcomm : Commute g0 g1 := by
      change ((γ0Γ * γ1Γ : Γ) : GL ι K) = ((γ1Γ * γ0Γ : Γ) : GL ι K)
      exact congrArg (fun z : Γ => (z : GL ι K))
        (commute_minusDiagGL (b := b) (c := d) (n := 3) (r := p) hpodd d0 d1 hd0 hd1)
    have hγ1notin : g1 ∉ Subgroup.zpowers g0 := by
      intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      have h1 : (((g0 ^ k : GL ι K)) : Matrix ι ι K) (Sum.inl (1 : Fin 2)) (Sum.inl 1) =
          ((g1 : GL ι K) : Matrix ι ι K) (Sum.inl (1 : Fin 2)) (Sum.inl 1) := by
        rw [← hk]
      rw [show g0 = ((γ0Γ : Γ) : GL ι K) from rfl,
        show g1 = ((γ1Γ : Γ) : GL ι K) from rfl,
        ← Subgroup.coe_zpow] at h1
      rw [show γ0Γ = minusDiagGL (b := b) (c := d) (n := 3) (r := p) hpodd d0 hd0 from rfl,
        show γ1Γ = minusDiagGL (b := b) (c := d) (n := 3) (r := p) hpodd d1 hd1 from rfl] at h1
      rw [coe_minusDiagGL_zpow_apply_inl (b := b) (c := d) (n := 3) hpodd hd0 k 1,
        coe_minusDiagGL_apply_inl (b := b) (c := d) (n := 3) hpodd hd1 1] at h1
      have ht_eq : t = 1 := by
        simpa [d0, d1, Pi.mulSingle] using h1.symm
      have hp1 : p = 1 := by
        rw [← ht, ht_eq, orderOf_one]
      exact hp.one_lt.ne hp1.symm
    obtain ⟨hTcard, hTexp⟩ := s16g_card_pair_subgroup hp hcomm hγ0ord hγ1ord hγ1notin
    let T : Subgroup (GL ι K) := Subgroup.zpowers g0 ⊔ Subgroup.zpowers g1
    have hTp : IsPGroup p ↥T := IsPGroup.of_card hTcard
    have hTnc : ¬ IsCyclic ↥T := by
      intro hcyc
      have : IsCyclic ↥T := hcyc
      have hle : Nat.card ↥T ≤ p := by
        simpa using CFSG.AGLEmbedding.card_le_of_isCyclic_of_pow_eq_one
          (⊤ : Subgroup ↥T) (fun z _ => Subtype.ext (hTexp (z : GL ι K) z.2))
      rw [hTcard] at hle
      nlinarith [hp.one_lt]
    have hTle : T ≤ Γ :=
      sup_le (Subgroup.zpowers_le.mpr γ0Γ.2) (Subgroup.zpowers_le.mpr γ1Γ.2)
    let y : ι → K := r • Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) 1
    have hy0 : y ≠ 0 := by
      intro h0
      have h1 := congrFun h0 (Sum.inr (Sum.inr (0 : Fin 2)))
      simp [y, Pi.smul_apply, hr0] at h1
    have hQy : quadMinus 3 K b d y = quadMinus 3 K b d vx := by
      have h1 : quadMinus 3 K b d y = r ^ 2 := by
        rw [show y = r • Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) 1 from rfl,
          QuadraticMap.map_smul, quadMinus_single_u, smul_eq_mul]
        ring
      rw [h1, hr']
    have hfixy0 : ((g0 : GL ι K) : Matrix ι ι K) *ᵥ y = y := by
      rw [show g0 = ((γ0Γ : Γ) : GL ι K) from rfl,
        show γ0Γ = minusDiagGL (b := b) (c := d) (n := 3) (r := p) hpodd d0 hd0 from rfl,
        coe_minusDiagGL, mulVec_diagGL]
      funext j
      rcases j with j | j | j
      · fin_cases j <;> simp [y, d0, Pi.mulSingle, Pi.smul_apply, torusEntMinus]
      · fin_cases j <;> simp [y, d0, Pi.mulSingle, Pi.smul_apply, torusEntMinus]
      · fin_cases j <;> simp [y, d0, Pi.mulSingle, Pi.smul_apply, torusEntMinus]
    have hfixy1 : ((g1 : GL ι K) : Matrix ι ι K) *ᵥ y = y := by
      rw [show g1 = ((γ1Γ : Γ) : GL ι K) from rfl,
        show γ1Γ = minusDiagGL (b := b) (c := d) (n := 3) (r := p) hpodd d1 hd1 from rfl,
        coe_minusDiagGL, mulVec_diagGL]
      funext j
      rcases j with j | j | j
      · fin_cases j <;> simp [y, d1, Pi.mulSingle, Pi.smul_apply, torusEntMinus]
      · fin_cases j <;> simp [y, d1, Pi.mulSingle, Pi.smul_apply, torusEntMinus]
      · fin_cases j <;> simp [y, d1, Pi.mulSingle, Pi.smul_apply, torusEntMinus]
    have hTfix : ∀ z ∈ T, ((z : GL ι K) : Matrix ι ι K) *ᵥ y = y :=
      s16g_fixed_of_pair hfixy0 hfixy1
    let Eb : Subgroup (MulAut (Multiplicative (ι → K))) := T.map (s16gNatHom ι K)
    have hEb_le : Eb ≤ ρ.range := (Subgroup.map_mono hTle).trans hΓρ
    have hEb_p : IsPGroup p ↥Eb := hTp.map (s16gNatHom ι K)
    have hEb_nc : ¬ IsCyclic ↥Eb := by
      intro hcyc
      exact hTnc ((Subgroup.equivMapOfInjective T (s16gNatHom ι K)
        s16gNatHom_injective).isCyclic.mpr hcyc)
    obtain ⟨B, hBp, hBnc, hBle⟩ :=
      exists_noncyclic_pGroup_map_le ρ hp hEb_le hEb_p hEb_nc
    have hBfix : ∀ b ∈ B, ρ b (Multiplicative.ofAdd y) = Multiplicative.ofAdd y := by
      intro b hb
      obtain ⟨z, hzT, hz⟩ := Subgroup.mem_map.1 (hBle b hb)
      rw [← hz, s16gNatHom_apply, toAdd_ofAdd, hTfix z hzT]
    obtain ⟨γ, hγΓ, hγv⟩ :=
      statedOmegaMinus_exists_mulVec_eq (m := 3) (by norm_num) hirr hy0 hx0 hQy
    have hγmem : s16gNatHom ι K γ ∈ ρ.range :=
      hΓρ (Subgroup.mem_map_of_mem (s16gNatHom ι K) hγΓ)
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 hγmem
    have hmy : ρ m (Multiplicative.ofAdd y) = x := by
      rw [hm, s16gNatHom_apply, toAdd_ofAdd, hγv, ofAdd_toAdd]
    exact conjugate_fixer m B (Multiplicative.ofAdd y) x hBp hBnc hBfix hmy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
