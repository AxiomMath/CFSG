module

public import CFSG.Quasithin.H13.KGLieNat

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup

section Five

variable {V : Type} [CommGroup V]

theorem coe_pow_mulAut (P : MulAut V) (n : ℕ) : ⇑(P ^ n) = (⇑P)^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]

theorem false_of_five {G L : Subgroup (MulAut V)} {v : MulAut V} (hc : A5.Cond1321 G L v)
    {g : MulAut V} (hg : g ∈ G) {u : V} (h5 : ((v * (g * v * g⁻¹)) ^ 5) u = u)
    (h1 : (v * (g * v * g⁻¹)) u ≠ u) : False := by
  set P := v * (g * v * g⁻¹) with hP
  have hper : ∀ n, (P ^ n) u = u → Function.IsPeriodicPt P n u := by
    intro n hn
    show (⇑P)^[n] u = u
    rw [← coe_pow_mulAut]
    exact hn
  have key : ∀ n, Nat.Coprime 5 n → P ^ n = 1 → False := by
    intro n hn hPn
    have h := (hper 5 h5).gcd (hper n (by rw [hPn]; rfl))
    rw [Nat.Coprime.gcd_eq_one hn] at h
    exact h1 h
  rcases hc.pair g hg with ⟨k, hk⟩ | h3
  · exact key (2 ^ k) (Nat.Coprime.pow_right _ (by norm_num)) hk
  · exact key 3 (by norm_num) h3

end Five

section Transvec

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

theorem five_of_transvec [CharP K 2] (A A' : M →ₗ[K] M) (hA'A : ∀ x, A' (A x) = x)
    (hAA' : ∀ x, A (A' x) = x) (φ : M →ₗ[K] K) {u₀ : M} (hφu : φ u₀ = 0) {T : M → M}
    (hT : ∀ x, T x = x + φ x • u₀)
    (hs : (φ (A u₀) * φ (A' u₀)) ^ 2 + φ (A u₀) * φ (A' u₀) + 1 = 0) :
    (fun x => T (A (T (A' x))))^[5] u₀ = u₀ ∧ T (A (T (A' u₀))) ≠ u₀ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hstep : ∀ x y x' y' : K, y' = y + x * φ (A' u₀) → x' = x + y' * φ (A u₀) →
      T (A (T (A' (x • u₀ + y • A u₀)))) = x' • u₀ + y' • A u₀ := by
    intro x y x' y' hy hx
    subst hy hx
    simp only [map_add, map_smul, hA'A, hAA', hT, hφu, smul_eq_mul]
    module
  have e0 : u₀ = (1 : K) • u₀ + (0 : K) • A u₀ := by simp
  have e1 := hstep 1 0 (1 + φ (A u₀) * φ (A' u₀)) (φ (A' u₀)) (by ring) (by ring)
  have e2 := hstep (1 + φ (A u₀) * φ (A' u₀)) (φ (A' u₀)) 0
    (φ (A u₀) * φ (A' u₀) * φ (A' u₀)) (by linear_combination -(φ (A' u₀)) * h2)
    (by linear_combination -hs)
  have e3 := hstep 0 (φ (A u₀) * φ (A' u₀) * φ (A' u₀)) ((φ (A u₀) * φ (A' u₀)) ^ 2)
    (φ (A u₀) * φ (A' u₀) * φ (A' u₀)) (by ring) (by ring)
  have e4 := hstep ((φ (A u₀) * φ (A' u₀)) ^ 2) (φ (A u₀) * φ (A' u₀) * φ (A' u₀)) 1
    (φ (A' u₀)) (by linear_combination -(φ (A' u₀)) * hs + (φ (A' u₀)) * h2)
    (by linear_combination -hs + h2)
  have e5 := hstep 1 (φ (A' u₀)) 1 0 (by linear_combination -(φ (A' u₀)) * h2) (by ring)
  refine ⟨?_, ?_⟩
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    conv_lhs => rw [e0]
    rw [e1, e2, e3, e4, e5, ← e0]
  · intro heq
    conv_lhs at heq => rw [e0]
    rw [e1] at heq
    have h := congrArg φ heq
    simp only [map_add, map_smul, hφu, smul_eq_mul, mul_zero, zero_add] at h
    have h0 : φ (A u₀) * φ (A' u₀) = 0 := by linear_combination h
    rw [h0] at hs
    norm_num at hs

theorem exists_transvec [CharP K 2] [Finite K] [Finite M] (T : M →ₗ[K] M)
    (hT2 : ∀ x, T (T x) = x) {w : M} (hw : T w ≠ w)
    (hcard : Nat.card (LinearMap.range (T - LinearMap.id : M →ₗ[K] M)) ≤ Nat.card K) :
    ∃ φ : M →ₗ[K] K, φ (T w - w) = 0 ∧ φ w = 1 ∧ ∀ x, T x = x + φ x • (T w - w) := by
  classical
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set u₀ := T w - w with hu₀
  have hu0 : u₀ ≠ 0 := sub_ne_zero.mpr hw
  have hle : (K ∙ u₀) ≤ LinearMap.range (T - LinearMap.id : M →ₗ[K] M) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨w, by simp [hu₀]⟩
  have hcK : Nat.card (K ∙ u₀) = Nat.card K :=
    (Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton K M u₀ hu0).toEquiv).symm
  have heq : (K ∙ u₀) = LinearMap.range (T - LinearMap.id : M →ₗ[K] M) := by
    apply SetLike.coe_injective
    refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
    show Nat.card (LinearMap.range (T - LinearMap.id : M →ₗ[K] M)) ≤ Nat.card (K ∙ u₀)
    rw [hcK]
    exact hcard
  have hmem : ∀ x, (T - LinearMap.id : M →ₗ[K] M) x ∈ (K ∙ u₀) := fun x => by
    rw [heq]
    exact LinearMap.mem_range_self _ x
  set φ : M →ₗ[K] K := (LinearEquiv.toSpanNonzeroSingleton K M u₀ hu0).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (K ∙ u₀) (T - LinearMap.id : M →ₗ[K] M) hmem with hφdef
  have hφ : ∀ x, φ x • u₀ = T x - x := by
    intro x
    have := LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul K M u₀ hu0
      (LinearMap.codRestrict (K ∙ u₀) (T - LinearMap.id : M →ₗ[K] M) hmem x)
    rw [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply] at this
    exact this
  have hTx : ∀ x, T x = x + φ x • u₀ := fun x => by rw [hφ]; abel
  refine ⟨φ, ?_, ?_, hTx⟩
  · have h1 : φ u₀ • u₀ = 0 := by
      rw [hφ, hu₀, map_sub, hT2]
      have : (w - T w) - (T w - w) = (2 : K) • (w - T w) := by rw [two_smul]; abel
      rw [this, h2, zero_smul]
    exact (smul_eq_zero.mp h1).resolve_right hu0
  · have h1 : φ w • u₀ = (1 : K) • u₀ := by rw [hφ, one_smul]
    exact smul_left_injective K hu0 h1

end Transvec

section Coord

variable {V : Type} [CommGroup V]

theorem exists_coordEquiv {D : FFModel} (hker : D.ker = ⊥) {L : Subgroup (MulAut V)}
    {π : D.Gam →* ↥L} (h : D.RealizesVia L ⊤ ⊥ π) :
    ∃ e : V ≃* ↥D.sec, ∀ (γ : D.Gam) (w : V),
      ((e (((π γ : ↥L) : MulAut V) w) : ↥D.sec) : D.Amb) =
        D.act γ ((e w : ↥D.sec) : D.Amb) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := G64.RealizesVia.exists_secMap hker h
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk u).1 hu))
  exact ⟨(Subgroup.topEquiv (G := V)).symm.trans (MulEquiv.ofBijective f ⟨hfi, hfs⟩),
    fun γ w => hfe γ ⟨w, mem_top w⟩ (mem_top _)⟩

end Coord

section NatFour

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def pairTrace {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} (φ : (ι → K) →ₗ[K] K)
    (u₀ : ι → K) (γ : ↥Γ) : K :=
  φ (Matrix.mulVec ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) u₀) *
    φ (Matrix.mulVec (((γ⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) u₀)

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_nat_four (hV2 : ∀ w : V, w ^ 2 = 1) {G L : Subgroup (MulAut V)}
    {v : MulAut V} (hB4 : B4Hyp G L) (hc : A5.Cond1321 G L v) (hι : 3 ≤ Fintype.card ι)
    [Finite K] (hK : Nat.card K = 4) {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (h : (FFModel.nat Γ).Realizes L ⊤ ⊥)
    (hfind : ∀ (u₀ : ι → K) (φ : (ι → K) →ₗ[K] K), u₀ ≠ 0 → φ ≠ 0 → φ u₀ = 0 →
      ∃ γ : ↥Γ, pairTrace φ u₀ γ ^ 2 + pairTrace φ u₀ γ + 1 = 0) : False := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  obtain ⟨π, hπ⟩ := h
  obtain ⟨e₀, he₀⟩ := exists_coordEquiv rfl hπ
  set e : V ≃* Multiplicative (ι → K) := e₀.trans Subgroup.topEquiv with he
  have hint : ∀ (γ : (FFModel.nat Γ).Gam) (w : V), e (((π γ : ↥L) : MulAut V) w) =
      natAct Γ γ (e w) :=
    fun γ w => he₀ γ w
  set m : Kˣ → MulAut V := fun c => e.trans ((scal c).trans e.symm) with hm
  have hmL : ∀ c, ∀ l ∈ L, m c * l = l * m c := by
    intro c l hl
    obtain ⟨γ, hγ⟩ := hπ.1 ⟨l, hl⟩
    have hl' : l = ((π γ : ↥L) : MulAut V) := (congrArg Subtype.val hγ).symm
    rw [hl']
    ext w
    apply e.injective
    simp only [hm, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [hint, hint, MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_scal, natAct, toAdd_ofAdd]
    rw [Matrix.mulVec_smul]
  have hLG : L ≤ G := hB4.2.1 ▸ quasithinGenFitting_le G
  have hvL : ∀ l ∈ L, v⁻¹ * l * v ∈ L := by
    intro l hl
    have hvN : v⁻¹ ∈ normalizer (L : Set (MulAut V)) := by
      rw [hB4.2.1]
      exact le_normalizer_quasithinGenFitting G (G.inv_mem hc.mem)
    have := (mem_normalizer_iff.1 hvN l).1 hl
    simpa using this
  have hrk : (commHom v).ker.index ≤ 4 := by
    rw [← fixV_zpowers_eq_ker]
    exact index_le_four_of_rkIdx hV2 hc.rank
  have hcardV : Nat.card V = 4 ^ Fintype.card ι := by
    rw [Nat.card_congr e.toEquiv]
    show Nat.card (ι → K) = _
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ι), hK]
  have hV : 16 < Nat.card V := by
    rw [hcardV]
    calc 16 < 4 ^ 3 := by norm_num
      _ ≤ 4 ^ Fintype.card ι := Nat.pow_le_pow_right (by norm_num) hι
  have hcomm : ∀ c, v * m c = m c * v := fun c =>
    comm_of_scalar hB4.2.2.2 hvL hrk hV (hmL c)
  have hTadd : ∀ x y : ι → K, Multiplicative.toAdd (e (v (e.symm (Multiplicative.ofAdd
      (x + y))))) = Multiplicative.toAdd (e (v (e.symm (Multiplicative.ofAdd x)))) +
      Multiplicative.toAdd (e (v (e.symm (Multiplicative.ofAdd y)))) := by
    intro x y
    rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul]
  have hTsmul : ∀ (c : K) (x : ι → K), Multiplicative.toAdd (e (v (e.symm
      (Multiplicative.ofAdd (c • x))))) =
      c • Multiplicative.toAdd (e (v (e.symm (Multiplicative.ofAdd x)))) := by
    intro c x
    by_cases hc0 : c = 0
    · subst hc0
      rw [zero_smul, zero_smul, ofAdd_zero, map_one, map_one, map_one, toAdd_one]
    · set c' : Kˣ := Units.mk0 c hc0
      have h1 : e.symm (Multiplicative.ofAdd (c • x)) = m c' (e.symm (Multiplicative.ofAdd x)) := by
        simp only [hm, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
        congr 1
      have h2 := congrArg (fun f : MulAut V => f (e.symm (Multiplicative.ofAdd x))) (hcomm c')
      simp only [MulAut.mul_apply] at h2
      rw [h1, h2]
      simp only [hm, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
  set T : (ι → K) →ₗ[K] (ι → K) :=
    { toFun := fun x => Multiplicative.toAdd (e (v (e.symm (Multiplicative.ofAdd x))))
      map_add' := hTadd
      map_smul' := hTsmul } with hTdef
  have hTv : ∀ y : V, T (Multiplicative.toAdd (e y)) = Multiplicative.toAdd (e (v y)) := by
    intro y
    show Multiplicative.toAdd (e (v (e.symm (Multiplicative.ofAdd
      (Multiplicative.toAdd (e y)))))) = _
    rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
  have hvv : ∀ y : V, v (v y) = y := by
    intro y
    have := congrArg (fun f : MulAut V => f y) hc.sq
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have hT2 : ∀ x, T (T x) = x := by
    intro x
    obtain ⟨y, rfl⟩ : ∃ y : V, Multiplicative.toAdd (e y) = x :=
      ⟨e.symm (Multiplicative.ofAdd x), by rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]⟩
    rw [hTv, hTv, hvv]
  obtain ⟨y₀, hy₀⟩ : ∃ y : V, v y ≠ y := by
    by_contra hne
    push Not at hne
    exact hc.ne_one (MulEquiv.ext hne)
  set w := Multiplicative.toAdd (e y₀) with hw
  have hTw : T w ≠ w := by
    rw [hw, hTv]
    intro h0
    exact hy₀ (e.injective (Multiplicative.toAdd.injective h0))
  have hcardT : Nat.card (LinearMap.range (T - LinearMap.id : (ι → K) →ₗ[K] (ι → K))) ≤
      Nat.card K := by
    have hsurj : Function.Surjective (fun z : ↥(commHom v).range =>
        (⟨Multiplicative.toAdd (e (z : V)), by
          obtain ⟨y, hy⟩ := z.2
          refine ⟨Multiplicative.toAdd (e y), ?_⟩
          rw [LinearMap.sub_apply, LinearMap.id_apply, hTv, ← hy]
          show _ = Multiplicative.toAdd (e (v y * y⁻¹))
          rw [map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]⟩ :
          ↥(LinearMap.range (T - LinearMap.id : (ι → K) →ₗ[K] (ι → K))))) := by
      rintro ⟨x, z, rfl⟩
      obtain ⟨y, rfl⟩ : ∃ y : V, Multiplicative.toAdd (e y) = z :=
        ⟨e.symm (Multiplicative.ofAdd z), by rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]⟩
      refine ⟨⟨v y * y⁻¹, y, rfl⟩, ?_⟩
      apply Subtype.ext
      show Multiplicative.toAdd (e (v y * y⁻¹)) =
        (T - LinearMap.id : (ι → K) →ₗ[K] (ι → K)) (Multiplicative.toAdd (e y))
      rw [LinearMap.sub_apply, LinearMap.id_apply, hTv, map_mul, map_inv, toAdd_mul, toAdd_inv,
        sub_eq_add_neg]
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [← Subgroup.index_ker] at h1
    rw [hK]
    exact h1.trans hrk
  obtain ⟨φ, hφu, hφw, hTφ⟩ := exists_transvec T hT2 hTw hcardT
  set u₀ := T w - w with hu₀
  have hu0 : u₀ ≠ 0 := sub_ne_zero.mpr hTw
  have hφ0 : φ ≠ 0 := fun h0 => by
    rw [h0, LinearMap.zero_apply] at hφw
    exact zero_ne_one hφw
  obtain ⟨γ, hγ⟩ := hfind u₀ φ hu0 hφ0 hφu
  set A : (ι → K) →ₗ[K] (ι → K) :=
    Matrix.toLin' ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) with hA
  set A' : (ι → K) →ₗ[K] (ι → K) :=
    Matrix.toLin' (((γ⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) with hA'
  have hinvm : (((γ⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) =
      (((γ : Matrix.GeneralLinearGroup ι K)⁻¹ : Matrix.GeneralLinearGroup ι K) :
        Matrix ι ι K) := rfl
  have hA'A : ∀ x, A' (A x) = x := by
    intro x
    rw [hA, hA', Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hinvm,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hAA' : ∀ x, A (A' x) = x := by
    intro x
    rw [hA, hA', Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hinvm,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hs : (φ (A u₀) * φ (A' u₀)) ^ 2 + φ (A u₀) * φ (A' u₀) + 1 = 0 := by
    rw [hA, hA', Matrix.toLin'_apply, Matrix.toLin'_apply]
    simpa only [pairTrace] using hγ
  obtain ⟨h5, h1⟩ := five_of_transvec A A' hA'A hAA' φ hφu hTφ hs
  set g : MulAut V := ((π γ : ↥L) : MulAut V) with hg
  have hgG : g ∈ G := hLG (π γ).2
  have hginv : g⁻¹ = ((π γ⁻¹ : ↥L) : MulAut V) := by
    have h2 : π γ⁻¹ = (π γ)⁻¹ := map_inv π _
    rw [hg, h2]
    rfl
  have hgA : ∀ y : V, Multiplicative.toAdd (e (g y)) = A (Multiplicative.toAdd (e y)) := by
    intro y
    rw [hA, Matrix.toLin'_apply]
    exact congrArg Multiplicative.toAdd (hint (γ : (FFModel.nat Γ).Gam) y)
  have hgA' : ∀ y : V, Multiplicative.toAdd (e (g⁻¹ y)) = A' (Multiplicative.toAdd (e y)) := by
    intro y
    rw [hginv, hA', Matrix.toLin'_apply]
    exact congrArg Multiplicative.toAdd (hint (γ⁻¹ : (FFModel.nat Γ).Gam) y)
  set P := v * (g * v * g⁻¹) with hP
  have hPe : ∀ y : V, Multiplicative.toAdd (e (P y)) =
      T (A (T (A' (Multiplicative.toAdd (e y))))) := by
    intro y
    simp only [hP, MulAut.mul_apply]
    rw [← hgA', hTv, ← hgA, hTv]
  have hPn : ∀ (n : ℕ) (y : V), Multiplicative.toAdd (e ((P ^ n) y)) =
      (fun x => T (A (T (A' x))))^[n] (Multiplicative.toAdd (e y)) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, MulAut.mul_apply, ih, hPe, Function.iterate_succ_apply]
  set u : V := e.symm (Multiplicative.ofAdd u₀) with hu
  have heu : Multiplicative.toAdd (e u) = u₀ := by rw [hu, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  refine false_of_five hc hgG (u := u) ?_ ?_
  · apply e.injective
    apply Multiplicative.toAdd.injective
    rw [hPn, heu, h5]
  · intro h0
    apply h1
    have := congrArg (fun y => Multiplicative.toAdd (e y)) h0
    rw [hPe, heu] at this
    exact this

end NatFour

end CFSG.Quasithin.H13.KGLie
