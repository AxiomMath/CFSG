module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1CardO
public import CFSG.RankThree.GF2n.Stroth80.Sec7NormalizerOmega
public import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

section Realizes

open CFSG.Quasithin CFSG.Open Subgroup
open Matrix

private lemma s16c11_case2orth_eq_zero_or_one {K : Type} [Field K]
    (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
    exact (huniq c hc).trans (huniq 1 one_ne_zero).symm

private noncomputable def s16c11_case2orth_mulAutLinearEquiv {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] (hK : Nat.card K = 2) :
    MulAut (Multiplicative (ι → K)) ≃* ((ι → K) ≃ₗ[K] (ι → K)) where
  toFun φ :=
    { toFun := (AddEquiv.toMultiplicative.symm φ : (ι → K) ≃+ (ι → K))
      map_add' := fun x y => (AddEquiv.toMultiplicative.symm φ).map_add x y
      map_smul' := fun c x => by
        rcases s16c11_case2orth_eq_zero_or_one hK c with rfl | rfl
        · simp
        · simp
      invFun := (AddEquiv.toMultiplicative.symm φ).symm
      left_inv := fun x => (AddEquiv.toMultiplicative.symm φ).left_inv x
      right_inv := fun x => (AddEquiv.toMultiplicative.symm φ).right_inv x }
  invFun ψ := AddEquiv.toMultiplicative ψ.toAddEquiv
  left_inv φ := by ext x; rfl
  right_inv ψ := by ext x; rfl
  map_mul' φ ψ := by ext x; rfl

private noncomputable def s16c11_case2orth_mulAutGL {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (hK : Nat.card K = 2) :
    MulAut (Multiplicative (ι → K)) ≃* GL ι K :=
  (s16c11_case2orth_mulAutLinearEquiv hK).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).symm.trans
      (Matrix.GeneralLinearGroup.toLin (n := ι) (R := K)).symm)

private theorem s16c11_case2orth_mulAutGL_symm_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (hK : Nat.card K = 2) (γ : GL ι K)
    (x : Multiplicative (ι → K)) :
    (s16c11_case2orth_mulAutGL hK).symm γ x =
      Multiplicative.ofAdd ((γ : Matrix ι ι K).mulVec (Multiplicative.toAdd x)) := by
  simp [s16c11_case2orth_mulAutGL, s16c11_case2orth_mulAutLinearEquiv,
    LinearMap.GeneralLinearGroup.generalLinearEquiv]

private noncomputable def s16c11_case2orth_restrictAction {W : Type} [CommGroup W]
    {L₀ : Subgroup (MulAut W)} {J : Subgroup W} (hJ : ∀ x ∈ L₀, ∀ y ∈ J, x y ∈ J) :
    ↥L₀ →* MulAut ↥J where
  toFun x :=
    { toFun := fun u => ⟨(x : MulAut W) (u : W), hJ (x : MulAut W) x.2 (u : W) u.2⟩
      invFun := fun u => ⟨((x⁻¹ : ↥L₀) : MulAut W) (u : W),
        hJ ((x⁻¹ : ↥L₀) : MulAut W) (x⁻¹).2 (u : W) u.2⟩
      left_inv := by
        intro u
        apply Subtype.ext
        change ((x⁻¹ : ↥L₀) : MulAut W) ((x : MulAut W) (u : W)) = (u : W)
        rw [← MulAut.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          MulAut.one_apply]
      right_inv := by
        intro u
        apply Subtype.ext
        change (x : MulAut W) (((x⁻¹ : ↥L₀) : MulAut W) (u : W)) = (u : W)
        rw [← MulAut.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          MulAut.one_apply]
      map_mul' := by
        intro u v
        apply Subtype.ext
        change (x : MulAut W) ((u : W) * (v : W)) =
          (x : MulAut W) (u : W) * (x : MulAut W) (v : W)
        exact map_mul (x : MulAut W) (u : W) (v : W) }
  map_one' := by
    ext u
    change ((1 : ↥L₀) : MulAut W) (u : W) = (u : W)
    rw [Subgroup.coe_one, MulAut.one_apply]
  map_mul' := by
    intro x y
    ext u
    change ((x * y : ↥L₀) : MulAut W) (u : W) = (x : MulAut W) ((y : MulAut W) (u : W))
    rw [Subgroup.coe_mul, MulAut.mul_apply]

private theorem s16c11_case2orth_restrictAction_apply {W : Type} [CommGroup W]
    {L₀ : Subgroup (MulAut W)} {J : Subgroup W} (hJ : ∀ x ∈ L₀, ∀ y ∈ J, x y ∈ J)
    (x : ↥L₀) (u : ↥J) :
    s16c11_case2orth_restrictAction hJ x u =
      ⟨(x : MulAut W) (u : W), hJ (x : MulAut W) x.2 (u : W) u.2⟩ := rfl

private theorem s16c11_case2orth_realizesVia_of_equiv {V : Type*} [CommGroup V] {Γ : Type}
    [Group Γ] {A : Type} [CommGroup A] (act : Γ → A → A) (hact1 : ∀ γ, act γ 1 = 1)
    {H : Subgroup (MulAut V)} {U : Subgroup V} (π : Γ →* ↥H) (hπ : Function.Surjective π)
    (hHU : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut V) u ∈ U) (e : ↥U ≃* A)
    (he : ∀ (γ : Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
      e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = act γ (e u)) :
    (FFModel.mk Γ A act ⊤ ⊥).RealizesVia H U ⊥ π := by
  refine ⟨hπ, bot_le, bot_le, hHU, ?_, fun _ _ _ => trivial, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ m hm
    change m ∈ (⊥ : Subgroup A) at hm
    change act γ m ∈ (⊥ : Subgroup A)
    rw [Subgroup.mem_bot] at hm ⊢
    rw [hm, hact1]
  · let β : ↥U →* ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤ :=
      (QuotientGroup.mk' _).comp (Subgroup.topEquiv.symm.toMonoidHom.comp e.toMonoidHom)
    have hβ : ∀ u : ↥U,
        β u = ((Subgroup.topEquiv.symm (e u) : ↥(⊤ : Subgroup A)) :
          ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤) := fun _ => rfl
    have hinj : ∀ a b : ↥(⊤ : Subgroup A), ((a : ↥(⊤ : Subgroup A) ⧸
        (⊥ : Subgroup A).subgroupOf ⊤) = b) → a = b := by
      intro a b h
      rw [QuotientGroup.eq, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at h
      exact (inv_mul_eq_one.mp h)
    refine ⟨β, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨⟨m, -⟩, rfl⟩ := QuotientGroup.mk_surjective y
      refine ⟨e.symm m, ?_⟩
      rw [hβ]
      congr 1
      exact Subtype.ext (by simp)
    · intro u
      rw [hβ, QuotientGroup.eq_one_iff, Subgroup.bot_subgroupOf, Subgroup.mem_bot,
        Subgroup.mem_bot]
      constructor
      · intro h
        have h' := congrArg Subtype.val h
        simpa using h'
      · intro h
        have hu1 : u = 1 := Subtype.ext h
        apply Subtype.ext
        simp [hu1]
    · intro γ u m hu hm hum
      rw [hβ] at hum ⊢
      have hm' := hinj _ _ hum
      congr 1
      apply Subtype.ext
      change e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = act γ (m : A)
      rw [he, ← hm']
      rfl

theorem s16c11_orth_center_bot {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 2 ≤ m) {b c : K} (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.center ↥(CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c)) = ⊥ := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  let zM : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K :=
    (z : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)
  have hcomm : ∀ g ∈ StatedOmega (StatedQuadMinus m K b c),
      zM * (g : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
          (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) =
        (g : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
          (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) * zM := by
    intro g hg
    have hle : StatedOmega (StatedQuadMinus m K b c) ≤
        CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c) := by
      change ⁅CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c),
        CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c)⁆ ≤ _
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    have hcent := (Subgroup.mem_center_iff.mp hz)
      (⟨g, hle hg⟩ : ↥(CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c)))
    have hcent' := congrArg
      (fun u : ↥(CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c)) =>
        ((u : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
          Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)) hcent
    simpa [zM] using hcent'.symm
  obtain ⟨c, hc⟩ := CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.commutant_scalar_of_linear
    (f₀ := StatedQuadMinus m K b c)
    (fun f hf => CFSG.RankThree.GF2n.Stroth80.stroth_2_4_omegaMinus K hm hpoly f hf)
    zM hcomm
  rcases s16c11_case2orth_eq_zero_or_one hK c with hc0 | hc1
  · exfalso
    have hz0 : zM = 0 := by rw [hc, hc0, zero_smul]
    exact Units.ne_zero (z : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) hz0
  · have hz1 : zM = 1 := by rw [hc, hc1, one_smul]
    exact Subtype.ext (Units.ext hz1)

theorem s16c11_orth_mem_isometryCore_of_normalizes {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 2 ≤ m) {b c : K}
    (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {A : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K}
    (hA : ∀ g ∈ StatedOmega (StatedQuadMinus m K b c),
      A * g * A⁻¹ ∈ StatedOmega (StatedQuadMinus m K b c)) :
    A ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  haveI : CharP K 2 := charP_of_card_eq_prime hK'
  obtain ⟨c, hcne, hcQ⟩ :=
    CFSG.RankThree.GF2n.Stroth80.normalizerOmegaFor_minus K hm hpoly A hA
  have hc1 : c = 1 := by
    rcases s16c11_case2orth_eq_zero_or_one hK c with h | h
    · exact absurd h hcne
    · exact h
  refine Subgroup.subset_closure fun v => ?_
  have h := hcQ v
  rw [hc1, one_smul] at h
  exact h

theorem s16c11_realizes_of_normal_overgroup {W : Type} [CommGroup W] [Finite W] {ι : Type}
    [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {Γ Γ₀ : Subgroup (GL ι K)} {L L₀ : Subgroup (MulAut W)} {J : Subgroup W} (hLL₀ : L ≤ L₀)
    (hnorm : ∀ x ∈ L₀, L.map (MulAut.conj x).toMonoidHom = L)
    (hJ : ∀ x ∈ L₀, ∀ y ∈ J, x y ∈ J) (hfaith : ∀ x ∈ L₀, (∀ y ∈ J, x y = y) → x = 1)
    (hN : ∀ A : GL ι K, (∀ g ∈ Γ, A * g * A⁻¹ ∈ Γ) → A ∈ Γ₀)
    (hcard : Nat.card ↥L₀ = Nat.card ↥Γ₀) (hR : (FFModel.nat Γ).Realizes L J ⊥) :
    (FFModel.nat Γ₀).Realizes L₀ J ⊥ := by
  classical
  obtain ⟨π, hπ⟩ := hR
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  let e : ↥J ≃* Multiplicative (ι → K) := MulEquiv.ofBijective β ⟨hβi, hβs⟩
  let Θ : MulAut ↥J ≃* GL ι K := (MulAut.congr e).trans (s16c11_case2orth_mulAutGL hK)
  let ρ₀ : ↥L₀ →* MulAut ↥J := s16c11_case2orth_restrictAction hJ
  let ρ : ↥L₀ →* GL ι K := Θ.toMonoidHom.comp ρ₀
  let π₀ : ↥Γ →* ↥L₀ := (Subgroup.inclusion hLL₀).comp π
  have hρπ : ∀ γ : ↥Γ, ρ (π₀ γ) = (γ : GL ι K) := by
    intro γ
    have hcongr : MulAut.congr e (ρ₀ (π₀ γ)) =
        (s16c11_case2orth_mulAutGL hK).symm (γ : GL ι K) := by
      apply MulEquiv.ext
      intro x
      rw [s16c11_case2orth_mulAutGL_symm_apply]
      obtain ⟨u, rfl⟩ := e.surjective x
      change e (ρ₀ (π₀ γ) (e.symm (e u))) = Multiplicative.ofAdd
        (((γ : GL ι K) : Matrix ι ι K).mulVec (Multiplicative.toAdd (e u)))
      rw [MulEquiv.symm_apply_apply]
      change e (ρ₀ (π₀ γ) u) = Multiplicative.ofAdd
        (((γ : GL ι K) : Matrix ι ι K).mulVec (Multiplicative.toAdd (e u)))
      have hu' : ((π γ : ↥L) : MulAut W) (u : W) ∈ J :=
        hJ ((π γ : ↥L) : MulAut W) (hLL₀ (π γ).2) (u : W) u.2
      have hval : ρ₀ (π₀ γ) u = (⟨((π γ : ↥L) : MulAut W) (u : W), hu'⟩ : ↥J) := by
        apply Subtype.ext
        rfl
      rw [hval]
      have h1 := hβe γ u hu'
      change β (⟨((π γ : ↥L) : MulAut W) (u : W), hu'⟩ : ↥J) =
        Multiplicative.ofAdd (((γ : GL ι K) : Matrix ι ι K).mulVec (Multiplicative.toAdd (e u)))
      rw [h1]
      rfl
    have hΘ : Θ (ρ₀ (π₀ γ)) = (γ : GL ι K) := by
      change (s16c11_case2orth_mulAutGL hK) (MulAut.congr e (ρ₀ (π₀ γ))) = (γ : GL ι K)
      rw [hcongr, MulEquiv.apply_symm_apply]
    simpa [ρ, Θ] using hΘ
  have hρker : ∀ x : ↥L₀, ρ x = 1 → x = 1 := by
    intro x hx
    have hx1 : ρ₀ x = 1 := by
      apply Θ.injective
      simpa [ρ] using hx
    apply Subtype.ext
    apply hfaith (x : MulAut W) x.2
    intro y hy
    have h2 := congrArg (fun f : MulAut ↥J => (f ⟨y, hy⟩ : W)) hx1
    simpa [ρ₀, s16c11_case2orth_restrictAction_apply, MulAut.one_apply] using h2
  have hρinj : Function.Injective ρ := by
    intro x y hxy
    have h1 : x * y⁻¹ = 1 := hρker (x * y⁻¹) (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  have hρmem' : ∀ x : ↥L₀, ρ x ∈ Γ₀ := by
    intro x
    apply hN
    intro g hg
    let γ : ↥Γ := ⟨g, hg⟩
    have hg_eq : g = ρ (π₀ γ) := (hρπ γ).symm
    have hA : ρ x * g * (ρ x)⁻¹ = ρ (x * π₀ γ * x⁻¹) := by
      rw [hg_eq, ← map_mul, ← map_inv, ← map_mul]
    have hmem : ((x * π₀ γ * x⁻¹ : ↥L₀) : MulAut W) ∈ L := by
      have hconj : ((x * π₀ γ * x⁻¹ : ↥L₀) : MulAut W) =
          (MulAut.conj (x : MulAut W)) ((π γ : ↥L) : MulAut W) := by
        rw [MulAut.conj_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rfl
      rw [hconj]
      have hmem' : (MulAut.conj (x : MulAut W)) ((π γ : ↥L) : MulAut W) ∈
          L.map (MulAut.conj (x : MulAut W)).toMonoidHom :=
        Subgroup.mem_map_of_mem _ (π γ).2
      rwa [hnorm (x : MulAut W) x.2] at hmem'
    let z : ↥L := ⟨((x * π₀ γ * x⁻¹ : ↥L₀) : MulAut W), hmem⟩
    obtain ⟨γ', hγ'⟩ := hπ.1 z
    have hπ₀γ' : π₀ γ' = x * π₀ γ * x⁻¹ := by
      apply Subtype.ext
      show ((π γ' : ↥L) : MulAut W) = ((x * π₀ γ * x⁻¹ : ↥L₀) : MulAut W)
      rw [hγ']
    rw [hA, ← hπ₀γ', hρπ γ']
    exact γ'.2
  let ρ' : ↥L₀ →* ↥Γ₀ := ρ.codRestrict Γ₀ hρmem'
  have hρ'inj : Function.Injective ρ' := by
    intro x y hxy
    exact hρinj (Subtype.ext_iff.mp hxy)
  have hρ'bij : Function.Bijective ρ' :=
    hρ'inj.bijective_of_nat_card_le (le_of_eq hcard.symm)
  let ρe : ↥L₀ ≃* ↥Γ₀ := MulEquiv.ofBijective ρ' hρ'bij
  let π₀' : ↥Γ₀ →* ↥L₀ := ρe.symm.toMonoidHom
  have hπ₀'surj : Function.Surjective π₀' := ρe.symm.surjective
  have hπ₀'ρ : ∀ γ : ↥Γ₀, ρ (π₀' γ) = (γ : GL ι K) := by
    intro γ
    have h1 : ρ' (π₀' γ) = γ := MulEquiv.apply_symm_apply ρe γ
    exact Subtype.ext_iff.mp h1
  refine ⟨π₀', ?_⟩
  refine s16c11_case2orth_realizesVia_of_equiv (natAct Γ₀) (by intro γ; simp [natAct])
    π₀' hπ₀'surj (fun h u hu => hJ _ h.2 u hu) e ?_
  intro γ u hu
  have hΘ : Θ (ρ₀ (π₀' γ)) = (γ : GL ι K) := by
    simpa [ρ] using hπ₀'ρ γ
  have hcongr : MulAut.congr e (ρ₀ (π₀' γ)) =
      (s16c11_case2orth_mulAutGL hK).symm (γ : GL ι K) := by
    apply (s16c11_case2orth_mulAutGL hK).injective
    rw [MulEquiv.apply_symm_apply]
    simpa [Θ] using hΘ
  have hval : (⟨((π₀' γ : ↥L₀) : MulAut W) (u : W), hu⟩ : ↥J) = ρ₀ (π₀' γ) u := by
    apply Subtype.ext
    rfl
  rw [hval]
  calc e (ρ₀ (π₀' γ) u)
      = (MulAut.congr e (ρ₀ (π₀' γ))) (e u) := by
        show e (ρ₀ (π₀' γ) u) = e (ρ₀ (π₀' γ) (e.symm (e u)))
        rw [MulEquiv.symm_apply_apply]
    _ = (s16c11_case2orth_mulAutGL hK).symm (γ : GL ι K) (e u) := by rw [hcongr]
    _ = natAct Γ₀ γ (e u) := by
        rw [s16c11_case2orth_mulAutGL_symm_apply]
        rfl


theorem s16c11_orth_faithful_on {W : Type} [CommGroup W] [Finite W]
    {L L₀ : Subgroup (MulAut W)} {J : Subgroup W} {n : ℕ} (hn : n = 6 ∨ n = 8)
    (hLL₀ : L ≤ L₀) (hL₀ : IsOMinus ↥L₀ n 1) (hL : IsOmegaMinus ↥L n 1)
    (hJ : ∀ x ∈ L₀, ∀ y ∈ J, x y ∈ J) (hN : NatOmegaMinus L J ⊥ n 1) :
    ∀ x ∈ L₀, (∀ y ∈ J, x y = y) → x = 1 := by
  have hcard : Nat.card ↥L₀ = 2 * Nat.card ↥L := s16e_card_eq_two_mul_of_isOMinus hn hL₀ hL
  have hrel : L.relIndex L₀ = 2 := by
    have h := Subgroup.relIndex_mul_card L L₀
    rw [inf_eq_left.mpr hLL₀, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  let C : Subgroup ↥L₀ :=
    { carrier := {c | ∀ y ∈ J, (c : MulAut W) y = y}
      one_mem' := by intro y _; rw [Subgroup.coe_one, MulAut.one_apply]
      mul_mem' := by
        intro a b ha hb y hy
        show ((a * b : ↥L₀) : MulAut W) y = y
        rw [Subgroup.coe_mul, MulAut.mul_apply, hb y hy, ha y hy]
      inv_mem' := by
        intro a ha y hy
        show ((a⁻¹ : ↥L₀) : MulAut W) y = y
        have h2 : (a : MulAut W) (((a⁻¹ : ↥L₀) : MulAut W) y) = y := by
          rw [← MulAut.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
            MulAut.one_apply]
        exact (ha (((a⁻¹ : ↥L₀) : MulAut W) y)
          (hJ ((a⁻¹ : ↥L₀) : MulAut W) (a⁻¹).2 y hy)) ▸ h2 }
  have hCL : C ⊓ (L.subgroupOf L₀) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    obtain ⟨hcC, hcL⟩ := Subgroup.mem_inf.1 hc
    have hcL' : (c : MulAut W) ∈ L := hcL
    obtain ⟨-, K', hK'f, hK'fin, b', c', hK'card, hpoly', hreal⟩ := hN
    letI : Field K' := hK'f
    letI : Finite K' := hK'fin
    rw [pow_one] at hK'card
    obtain ⟨π, hπ⟩ := hreal
    obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ
    obtain ⟨γ, hγ⟩ := hπ.1 ⟨(c : MulAut W), hcL'⟩
    have hγ1 : γ = 1 := by
      apply CFSG.Quasithin.natAct_faithful
        (StatedOmega (StatedQuadMinus (n / 2) K' b' c')) γ
      intro m
      obtain ⟨u, hu⟩ := hβs m
      have hfixc : (c : MulAut W) (u : W) = (u : W) := hcC (u : W) u.2
      have hu' : ((π γ : ↥L) : MulAut W) (u : W) ∈ J := by
        rw [hγ]
        exact hJ (c : MulAut W) c.2 (u : W) u.2
      have h1 := hβe γ u hu'
      have h2 : (⟨((π γ : ↥L) : MulAut W) (u : W), hu'⟩ : ↥J) = u := by
        apply Subtype.ext
        change ((π γ : ↥L) : MulAut W) (u : W) = (u : W)
        have hfun : ((π γ : ↥L) : MulAut W) = (c : MulAut W) := by rw [hγ]
        rw [hfun]
        exact hfixc
      rw [h2] at h1
      have hm : natAct (StatedOmega (StatedQuadMinus (n / 2) K' b' c')) γ m = m := by
        rw [← hu]
        exact h1.symm
      rw [hm, mul_inv_cancel]
    have hc1 : (c : MulAut W) = 1 := by
      have h1 : (⟨(c : MulAut W), hcL'⟩ : ↥L) = π 1 := by rw [← hγ, hγ1]
      have h2 := congrArg (fun l : ↥L => (l : MulAut W)) h1
      rw [map_one] at h2
      simpa using h2
    exact Subtype.ext hc1
  have hCcard : Nat.card ↥C ≤ 2 := by
    haveI : (L.subgroupOf L₀).Normal := Subgroup.normal_of_index_eq_two hrel
    let q : ↥L₀ →* ↥L₀ ⧸ (L.subgroupOf L₀) := QuotientGroup.mk' _
    have hinj : Function.Injective (q.comp C.subtype) := by
      intro a b hab
      simp only [MonoidHom.comp_apply] at hab
      have hab' : q (a : ↥L₀) = q (b : ↥L₀) := hab
      have hq : q ((a : ↥L₀) * (b : ↥L₀)⁻¹) = 1 := by
        rw [map_mul, map_inv, hab', mul_inv_cancel]
      have hmem : (a : ↥L₀) * (b : ↥L₀)⁻¹ ∈ L.subgroupOf L₀ := by
        rw [← QuotientGroup.eq_one_iff]
        exact hq
      have hmemC : (a : ↥L₀) * (b : ↥L₀)⁻¹ ∈ C := C.mul_mem a.2 (C.inv_mem b.2)
      have hinf : (a : ↥L₀) * (b : ↥L₀)⁻¹ ∈ C ⊓ (L.subgroupOf L₀) :=
        Subgroup.mem_inf.2 ⟨hmemC, hmem⟩
      have hone : (a : ↥L₀) * (b : ↥L₀)⁻¹ = 1 := by
        rwa [hCL, Subgroup.mem_bot] at hinf
      exact Subtype.ext (mul_inv_eq_one.mp hone)
    have hle := Nat.card_le_card_of_injective (q.comp C.subtype) hinj
    rwa [show Nat.card (↥L₀ ⧸ (L.subgroupOf L₀)) = 2 by
      rw [← Subgroup.index_eq_card]
      exact hrel] at hle
  have hCcenter : C ≤ Subgroup.center ↥L₀ := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro g
    by_cases h1 : c = 1
    · rw [h1, mul_one, one_mul]
    have hconj : g * c * g⁻¹ ∈ C := by
      intro y hy
      have hy' : ((g⁻¹ : ↥L₀) : MulAut W) y ∈ J :=
        hJ ((g⁻¹ : ↥L₀) : MulAut W) (g⁻¹).2 y hy
      calc ((g * c * g⁻¹ : ↥L₀) : MulAut W) y
          = (g : MulAut W) ((c : MulAut W) (((g⁻¹ : ↥L₀) : MulAut W) y)) := by
            simp [Subgroup.coe_mul, MulAut.mul_apply]
        _ = (g : MulAut W) (((g⁻¹ : ↥L₀) : MulAut W) y) := by rw [hc _ hy']
        _ = y := by
            rw [← MulAut.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
              MulAut.one_apply]
    have hconj_ne : g * c * g⁻¹ ≠ 1 := by
      intro h
      apply h1
      have hh : c = g⁻¹ * (g * c * g⁻¹) * g := by group
      rw [hh, h]
      group
    have hcardC : Nat.card ↥C = 2 := by
      have hlt : 1 < Nat.card ↥C :=
        (Subgroup.one_lt_card_iff_ne_bot C).mpr (fun hbot => h1 (by
          rw [hbot, Subgroup.mem_bot] at hc
          exact hc))
      omega
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥C)).mp hcardC
    have e1 : (⟨c, hc⟩ : ↥C) = y := hy _ fun h => h1 (congrArg Subtype.val h)
    have e2 : (⟨g * c * g⁻¹, hconj⟩ : ↥C) = y :=
      hy _ fun h => hconj_ne (congrArg Subtype.val h)
    have e3 : g * c * g⁻¹ = c := congrArg Subtype.val (e2.trans e1.symm)
    calc g * c = g * c * g⁻¹ * g := by group
      _ = c * g := by rw [e3]
  have hcenter_bot : Subgroup.center ↥L₀ = ⊥ := by
    obtain ⟨-, K', hK'f, hK'fin, b', c', hK'card, hpoly', ⟨e⟩⟩ := hL₀
    letI : Field K' := hK'f
    letI : Finite K' := hK'fin
    rw [pow_one] at hK'card
    have hm : 2 ≤ n / 2 := by rcases hn with rfl | rfl <;> norm_num
    have hmap := Subgroup.map_center_eq e
    rw [s16c11_orth_center_bot hK'card hm hpoly'] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥L₀)
      (f := e.toMonoidHom) e.injective).1 hmap
  intro x hx hfix
  have hxC : (⟨x, hx⟩ : ↥L₀) ∈ C := hfix
  have hxcenter : (⟨x, hx⟩ : ↥L₀) ∈ Subgroup.center ↥L₀ := hCcenter hxC
  rw [hcenter_bot, Subgroup.mem_bot] at hxcenter
  simpa using Subtype.ext_iff.mp hxcenter

theorem s16c11_orth_card_eq {X : Type} [Group X] {n : ℕ} (hX : IsOMinus X n 1) {K : Type}
    [Field K] [Finite K] {b c : K} (hK : Nat.card K = 2)
    (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card X =
      Nat.card ↥(CFSG.MatrixModel.isometryCore (StatedQuadMinus (n / 2) K b c)) := by
  obtain ⟨-, K', hK'f, hK'fin, b', c', hK'card, hpoly', ⟨eX⟩⟩ := hX
  letI : Field K' := hK'f
  letI : Finite K' := hK'fin
  rw [pow_one] at hK'card
  obtain ⟨t'⟩ := s16c167_isometryCore_quadMinus_equiv (n / 2) hK'card hpoly'
  obtain ⟨t⟩ := s16c167_isometryCore_quadMinus_equiv (n / 2) hK hpoly
  exact Nat.card_congr (eX.trans (t'.trans t.symm)).toEquiv

theorem s16c11_orth_realizes {W : Type} [CommGroup W] [Finite W]
    {L L₀ : Subgroup (MulAut W)} {J : Subgroup W} {n : ℕ} (hn : n = 6 ∨ n = 8)
    (hLL₀ : L ≤ L₀) (hL₀ : IsOMinus ↥L₀ n 1) (hL : IsOmegaMinus ↥L n 1)
    (hJ : ∀ x ∈ L₀, ∀ y ∈ J, x y ∈ J) (hN : NatOmegaMinus L J ⊥ n 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K), Nat.card K = 2 ∧
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      (FFModel.nat (CFSG.MatrixModel.isometryCore
        (StatedQuadMinus (n / 2) K b c))).Realizes L₀ J ⊥ := by
  have hcard : Nat.card ↥L₀ = 2 * Nat.card ↥L := s16e_card_eq_two_mul_of_isOMinus hn hL₀ hL
  have hnorm := s16c11_map_conj_eq_of_card_two_mul hLL₀ hcard
  have hfaith := s16c11_orth_faithful_on hn hLL₀ hL₀ hL hJ hN
  obtain ⟨hev, K, hKf, hKfin, b, c, hKcard, hpoly, hreal⟩ := hN
  letI : Field K := hKf
  letI : Finite K := hKfin
  rw [pow_one] at hKcard
  have hm : 2 ≤ n / 2 := by rcases hn with rfl | rfl <;> norm_num
  refine ⟨K, hKf, hKfin, b, c, hKcard, hpoly, ?_⟩
  exact s16c11_realizes_of_normal_overgroup hKcard hLL₀ hnorm hJ hfaith
    (fun A hA => s16c11_orth_mem_isometryCore_of_normalizes hKcard hm hpoly hA)
    (s16c11_orth_card_eq hL₀ hKcard hpoly) hreal

end Realizes

section Transport

open CFSG.Quasithin CFSG.Open

open scoped Matrix

private lemma s16c11_orthfin_mulVec_glCongr_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    {K L : Type} [Field K] [Field L] (e : K ≃+* L) {A : Matrix.GeneralLinearGroup ι K}
    {A' : Matrix.GeneralLinearGroup ι L}
    (hA' : A' = CFSG.Adapters.RankTwoModelTransports.glCongr (ι := ι) e A) (v : ι → K) :
    ((A' : Matrix ι ι L) *ᵥ (e ∘ v) = e ∘ v) ↔ ((A : Matrix ι ι K) *ᵥ v = v) := by
  subst hA'
  rw [CFSG.ClassicalInvolution.Upgrade.glCongr_mulVec e A v]
  constructor
  · intro h
    funext i
    exact e.injective (congrFun h i)
  · intro h
    rw [h]

private lemma s16c11_orthfin_act_glCongr_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {Γ' : Subgroup (Matrix.GeneralLinearGroup ι L)} {A : ↥Γ} {A' : ↥Γ'}
    (hA' : (A' : Matrix.GeneralLinearGroup ι L) =
      CFSG.Adapters.RankTwoModelTransports.glCongr (ι := ι) e
        (A : Matrix.GeneralLinearGroup ι K)) (v : ι → K) :
    (natAct Γ A (Multiplicative.ofAdd v) = Multiplicative.ofAdd v) ↔
      (natAct Γ' A' (Multiplicative.ofAdd (e ∘ v)) = Multiplicative.ofAdd (e ∘ v)) := by
  have key : ∀ w : ι → K,
      (Multiplicative.ofAdd w = (Multiplicative.ofAdd v : Multiplicative (ι → K))) ↔ w = v := by
    intro w
    constructor
    · intro h
      simpa using congrArg Multiplicative.toAdd h
    · intro h
      rw [h]
  have keyL : ∀ w : ι → L,
      (Multiplicative.ofAdd w = (Multiplicative.ofAdd (e ∘ v) :
        Multiplicative (ι → L))) ↔ w = e ∘ v := by
    intro w
    constructor
    · intro h
      simpa using congrArg Multiplicative.toAdd h
    · intro h
      rw [h]
  simp only [natAct, toAdd_ofAdd]
  simp only [keyL, key]
  exact (s16c11_orthfin_mulVec_glCongr_iff e hA' v).symm

theorem s16c11_modelRF3_of_ringEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {K L : Type}
    [Field K] [Field L] (e : K ≃+* L) {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {Γ' : Subgroup (Matrix.GeneralLinearGroup ι L)}
    (hΓ : Γ.map (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := ι) e).toMonoidHom = Γ')
    (h : S16C11ModelRF3 (FFModel.nat Γ')) : S16C11ModelRF3 (FFModel.nat Γ) := by
  classical
  let φ : Matrix.GeneralLinearGroup ι K ≃* Matrix.GeneralLinearGroup ι L :=
    CFSG.Adapters.RankTwoModelTransports.glCongr (ι := ι) e
  have hΓ' : Γ' = Γ.map φ.toMonoidHom := hΓ.symm
  rw [hΓ'] at h
  let ψ : ↥Γ ≃* ↥(Γ.map φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective Γ φ.toMonoidHom φ.injective
  have hψ_coe : ∀ g : ↥Γ,
      ((ψ g : ↥(Γ.map φ.toMonoidHom)) : Matrix.GeneralLinearGroup ι L) =
        φ (g : Matrix.GeneralLinearGroup ι K) := by
    intro g
    exact Subgroup.coe_equivMapOfInjective_apply Γ φ.toMonoidHom φ.injective g
  have hψ_symm_coe : ∀ g' : ↥(Γ.map φ.toMonoidHom),
      (g' : Matrix.GeneralLinearGroup ι L) =
        CFSG.Adapters.RankTwoModelTransports.glCongr (ι := ι) e
          ((ψ.symm g' : ↥Γ) : Matrix.GeneralLinearGroup ι K) := by
    intro g'
    conv_lhs => rw [← ψ.apply_symm_apply g']
    exact hψ_coe (ψ.symm g')
  obtain ⟨T', X', hT'X', hT'p, hT'i, hT'X'3, y', hy', hfix', g', hg'X', hg'mov'⟩ := h
  let v' : ι → L := Multiplicative.toAdd y'
  let y : Multiplicative (ι → K) := Multiplicative.ofAdd (e.symm ∘ v')
  let T : Subgroup ↥Γ := T'.map ψ.symm.toMonoidHom
  let X : Subgroup ↥Γ := X'.map ψ.symm.toMonoidHom
  have hTX : T ≤ X := Subgroup.map_mono hT'X'
  have hTp : IsPGroup 2 ↥T := hT'p.map ψ.symm.toMonoidHom
  have hTi : ¬ 2 ∣ T.index := by
    change ¬ 2 ∣ (T'.map ψ.symm.toMonoidHom).index
    rw [Subgroup.index_map_of_bijective (f := ψ.symm.toMonoidHom) ψ.symm.bijective T']
    exact hT'i
  have hTX3 : T.relIndex X = 3 := by
    change (T'.map ψ.symm.toMonoidHom).relIndex (X'.map ψ.symm.toMonoidHom) = 3
    rw [Subgroup.relIndex_map_map_of_injective (f := ψ.symm.toMonoidHom) T' X'
      ψ.symm.injective]
    exact hT'X'3
  have hev : e ∘ (e.symm ∘ v') = v' := by
    funext i
    simp
  have hfix'w : ∀ t' ∈ T', natAct (Γ.map φ.toMonoidHom) t' y' = y' := by
    intro t' ht'
    have h1 := hfix' t' ht'
    simp only [FFModel.nat] at h1
    exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 h1)
  have hg'mov'w : natAct (Γ.map φ.toMonoidHom) g' y' ≠ y' := by
    intro hEq
    exact hg'mov' (Subgroup.mem_bot.2 (mul_inv_eq_one.2 hEq))
  refine ⟨T, X, hTX, hTp, hTi, hTX3, y, Subgroup.mem_top _, ?_, ?_⟩
  · rintro t ht
    obtain ⟨t', ht', htteq⟩ := Subgroup.mem_map.1 ht
    subst htteq
    have hact := s16c11_orthfin_act_glCongr_iff (e := e) (hA' := hψ_symm_coe t')
      (v := e.symm ∘ v')
    rw [hev] at hact
    exact Subgroup.mem_bot.2 (mul_inv_eq_one.2 (hact.2 (hfix'w t' ht')))
  · refine ⟨ψ.symm g', Subgroup.mem_map_of_mem _ hg'X', ?_⟩
    intro hcon
    have hact := s16c11_orthfin_act_glCongr_iff (e := e) (hA' := hψ_symm_coe g')
      (v := e.symm ∘ v')
    rw [hev] at hact
    have hfixg : natAct Γ (ψ.symm g') y = y :=
      mul_inv_eq_one.1 (Subgroup.mem_bot.1 hcon)
    exact hg'mov'w (hact.1 hfixg)

end Transport

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
