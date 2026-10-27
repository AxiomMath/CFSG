module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmMoves
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoTorus
import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaMono

public section

namespace CFSG.StandardType

open CFSG.RankThree.Classical

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def p9Norm_offSupp {K : Type} [Field K] {M : Type} [AddCommGroup M] [Module K M]
    {s : ℕ} (f : Fin s → ZMod 3) : Submodule K (Fin s → M) where
  carrier := {d | ∀ i, f i ≠ 0 → d i = 0}
  add_mem' := by
    intro d d' hd hd' i hi
    rw [Pi.add_apply, hd i hi, hd' i hi, add_zero]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c d hd i hi
    rw [Pi.smul_apply, hd i hi, smul_zero]

private theorem p9Norm_offSupp_le_iff {K : Type} [Field K] {M : Type} [AddCommGroup M]
    [Module K M] [Nontrivial M] {s : ℕ} (f f' : Fin s → ZMod 3) :
    p9Norm_offSupp (K := K) (M := M) f ≤ p9Norm_offSupp (K := K) (M := M) f' ↔
      NoOffOm.SuppLE f' f := by
  constructor
  · intro h i hi
    by_contra hfi
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    have hmem : (Pi.single i m) ∈ p9Norm_offSupp (K := K) (M := M) f := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        exact absurd hfi hj
      · rw [Pi.single_eq_of_ne hji]
    have h0 := h hmem i hi
    rw [Pi.single_eq_same] at h0
    exact hm h0
  · intro h d hd i hi
    exact hd i (h i hi)

private theorem p9Norm_prod_le_prod_iff {K : Type} [Field K] {M M' : Type} [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module K M'] {P P' : Submodule K M} {W : Submodule K M'} :
    P.prod W ≤ P'.prod W ↔ P ≤ P' := by
  constructor
  · intro h x hx
    have h1 : (x, 0) ∈ P.prod W := by
      rw [Submodule.mem_prod]
      exact ⟨hx, W.zero_mem⟩
    have h2 := h h1
    rw [Submodule.mem_prod] at h2
    exact h2.1
  · intro h
    exact Submodule.prod_mono h le_rfl

private theorem p9Norm_fix_iso {K : Type} [Field K] {X V : Type} [AddCommGroup X]
    [Module K X] [AddCommGroup V] [Module K V] (e : X ≃ₗ[K] V) (t : X ≃ₗ[K] X) :
    LinearMap.ker (((e.symm.trans (t.trans e)).toLinearMap - 1)) =
      (LinearMap.ker (t.toLinearMap - 1)).map e.toLinearMap := by
  ext v
  constructor
  · intro hv
    have h : (e.symm.trans (t.trans e)) v = v := by
      simpa [LinearMap.sub_apply] using sub_eq_zero.mp hv
    refine Submodule.mem_map.mpr ⟨e.symm v, ?_, by simp⟩
    have ht : t (e.symm v) = e.symm v := by
      have h' : e (t (e.symm v)) = v := h
      apply e.injective
      rw [h', LinearEquiv.apply_symm_apply]
    simpa [LinearMap.sub_apply] using sub_eq_zero.mpr ht
  · intro hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    have ht : t x = x := by
      simpa [LinearMap.sub_apply] using sub_eq_zero.mp hx
    have h : (e.symm.trans (t.trans e)) (e x) = e x := by
      simp [LinearEquiv.trans_apply, ht]
    simpa [LinearMap.sub_apply] using sub_eq_zero.mpr h

private theorem p9Norm_fix_conj {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (g t : V ≃ₗ[K] V) :
    LinearMap.ker (((g * t * g⁻¹ : V ≃ₗ[K] V)).toLinearMap - 1) =
      (LinearMap.ker (t.toLinearMap - 1)).map g.toLinearMap :=
  p9Norm_fix_iso g t

private theorem p9Norm_sgnZ_unit (u : (ZMod 3)ˣ) (a : ZMod 3) :
    ChoiceTwo.sgnZ (decide ((u : ZMod 3) = -1)) a = (u : ZMod 3) * a := by
  rcases (by decide : ∀ r : (ZMod 3)ˣ, (r : ZMod 3) = 1 ∨ (r : ZMod 3) = -1) u with h | h
  · have hd : decide ((1 : ZMod 3) = -1) = false := by decide
    rw [h, hd]
    simp [ChoiceTwo.sgnZ]
  · have hd : decide ((-1 : ZMod 3) = -1) = true := by decide
    rw [h, hd]
    simp [ChoiceTwo.sgnZ]

private theorem p9Norm_exists_moveExp_of_conj {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {s : ℕ} (tor : (Fin s → ZMod 3) → V ≃ₗ[K] V)
    (hadd : ∀ f f', tor (f + f') = tor f * tor f') (hzero : tor 0 = 1)
    (hinj : Function.Injective tor) (Q : (Fin s → ZMod 3) → Submodule K V)
    (hQ : ∀ f, LinearMap.ker ((tor f).toLinearMap - 1) = Q f)
    (hQle : ∀ f f', Q f ≤ Q f' ↔ NoOffOm.SuppLE f' f) (g : V ≃ₗ[K] V)
    (hg : ∀ f, ∃ f', g * tor f * g⁻¹ = tor f') :
    ∃ (π : Equiv.Perm (Fin s)) (η : Fin s → Bool),
      ∀ f, g * tor f * g⁻¹ = tor (ChoiceTwo.moveExp π η f) := by
  classical
  choose α hα using hg
  have h0 : α 0 = 0 := by
    apply hinj
    calc tor (α 0) = g * tor 0 * g⁻¹ := (hα 0).symm
      _ = g * 1 * g⁻¹ := by rw [hzero]
      _ = 1 := by group
      _ = tor 0 := hzero.symm
  have haddα : ∀ f f', α (f + f') = α f + α f' := by
    intro f f'
    apply hinj
    calc tor (α (f + f')) = g * tor (f + f') * g⁻¹ := (hα (f + f')).symm
      _ = g * (tor f * tor f') * g⁻¹ := by rw [hadd]
      _ = (g * tor f * g⁻¹) * (g * tor f' * g⁻¹) := by group
      _ = tor (α f) * tor (α f') := by rw [hα f, hα f']
      _ = tor (α f + α f') := (hadd (α f) (α f')).symm
  let αhom : (Fin s → ZMod 3) →+ (Fin s → ZMod 3) :=
    { toFun := α, map_zero' := h0, map_add' := haddα }
  have hmap : ∀ f, Q (α f) = (Q f).map g.toLinearMap := by
    intro f
    rw [← hQ (α f), ← hα f, p9Norm_fix_conj, hQ f]
  have hαhom : ∀ f, αhom f = α f := fun _ => rfl
  have hSupp : ∀ f f', NoOffOm.SuppLE (αhom f) (αhom f') ↔ NoOffOm.SuppLE f f' := by
    intro f f'
    calc NoOffOm.SuppLE (αhom f) (αhom f')
        ↔ NoOffOm.SuppLE (α f) (α f') := by rw [hαhom f, hαhom f']
      _ ↔ Q (α f') ≤ Q (α f) := (hQle (α f') (α f)).symm
      _ ↔ Q f' ≤ Q f := by
            rw [hmap f', hmap f,
              Submodule.map_le_map_iff_of_injective (f := g.toLinearMap) g.injective _ _]
      _ ↔ NoOffOm.SuppLE f f' := hQle f' f
  obtain ⟨π, ηu, hη⟩ :=
    NoOffOm.exists_monomial_of_suppLE αhom hSupp
  refine ⟨π, fun i => decide ((ηu i : ZMod 3) = -1), fun f => ?_⟩
  rw [hα f]
  have hαeq : α f = αhom f := rfl
  rw [hαeq, hη f]
  apply congrArg tor
  funext i
  rw [ChoiceTwo.moveExp_apply]
  exact (p9Norm_sgnZ_unit (ηu i) (f (π i))).symm

namespace FrameRoute

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]

theorem injective_of_torC {s : ℕ} {W : Type} [AddCommGroup W] [Module K W]
    (Φ : ((Fin s → K × K) × W) ≃ₗ[K] V) (tor : (Fin s → ZMod 3) → (V ≃ₗ[K] V))
    (htor : ∀ f d x, tor f (Φ (d, x)) = Φ (ChoiceTwoOm.torC f d, x)) : Function.Injective tor := by
  intro f f' h
  funext i
  have h1 := congrArg (fun e : V ≃ₗ[K] V =>
    e (Φ (Pi.single i ((1 : K), (0 : K)), 0))) h
  simp only [htor] at h1
  have h2 := congrFun (congrArg Prod.fst (Φ.injective h1)) i
  exact ChoiceTwoOm.OmCoord.zpow_inj (by
    simpa [ChoiceTwoOm.torC_apply] using h2)

private theorem p9Norm_fix_torC {s : ℕ} {W : Type} [AddCommGroup W] [Module K W]
    (Φ : ((Fin s → K × K) × W) ≃ₗ[K] V) (tor : (Fin s → ZMod 3) → V ≃ₗ[K] V)
    (htor : ∀ f d x, tor f (Φ (d, x)) = Φ (ChoiceTwoOm.torC f d, x))
    (f : Fin s → ZMod 3) :
    LinearMap.ker ((tor f).toLinearMap - 1) =
      ((p9Norm_offSupp (K := K) (M := K × K) f).prod (⊤ : Submodule K W)).map Φ.toLinearMap := by
  ext v
  constructor
  · intro hv
    obtain ⟨⟨d, x⟩, rfl⟩ := Φ.surjective v
    have ht : tor f (Φ (d, x)) = Φ (d, x) := by
      simpa [LinearMap.sub_apply] using sub_eq_zero.mp hv
    have hcoords : (ChoiceTwoOm.torC f d, x) = (d, x) := by
      apply Φ.injective
      rw [← htor, ht]
    have hd : d ∈ p9Norm_offSupp (K := K) (M := K × K) f := by
      intro i hi
      have hz : ChoiceTwoOm.zpow (f i) (d i) = d i :=
        congrFun (congrArg Prod.fst hcoords) i
      exact ChoiceTwoOm.eq_zero_of_zpow_eq (f i) hi (d i) hz
    exact Submodule.mem_map.mpr ⟨(d, x), by
      rw [Submodule.mem_prod]
      exact ⟨hd, Submodule.mem_top⟩, rfl⟩
  · intro hv
    obtain ⟨⟨d, x⟩, hmem, rfl⟩ := Submodule.mem_map.mp hv
    rw [Submodule.mem_prod] at hmem
    have htd : ChoiceTwoOm.torC f d = d := by
      funext i
      by_cases hi : f i = 0
      · rw [ChoiceTwoOm.torC_apply, hi, ChoiceTwoOm.zpow_zero]
        rfl
      · have hdi : d i = 0 := hmem.1 i hi
        rw [ChoiceTwoOm.torC_apply, hdi, map_zero]
    have ht : tor f (Φ (d, x)) = Φ (d, x) := by rw [htor, htd]
    simpa [LinearMap.sub_apply] using sub_eq_zero.mpr ht

theorem exists_moveExp_of_conj_torC {s : ℕ} {W : Type} [AddCommGroup W] [Module K W]
    (Φ : ((Fin s → K × K) × W) ≃ₗ[K] V)
    (tor : (Fin s → ZMod 3) → (V ≃ₗ[K] V))
    (htor : ∀ f d x, tor f (Φ (d, x)) = Φ (ChoiceTwoOm.torC f d, x)) (g : V ≃ₗ[K] V)
    (hg : ∀ f, ∃ f', g * tor f * g⁻¹ = tor f') :
    ∃ (π : Equiv.Perm (Fin s)) (η : Fin s → Bool),
      ∀ f, g * tor f * g⁻¹ = tor (ChoiceTwo.moveExp π η f) := by
  classical
  have hinj : Function.Injective tor := injective_of_torC Φ tor htor
  have hadd : ∀ f f', tor (f + f') = tor f * tor f' := by
    intro f f'
    apply LinearEquiv.ext
    intro v
    obtain ⟨⟨d, x⟩, rfl⟩ := Φ.surjective v
    rw [LinearEquiv.mul_apply, htor, htor, htor, ChoiceTwoOm.torC_add]
  have hzero : tor 0 = 1 := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨⟨d, x⟩, rfl⟩ := Φ.surjective v
    rw [htor, ChoiceTwoOm.torC_zero]
    rfl
  let Q : (Fin s → ZMod 3) → Submodule K V := fun f =>
    ((p9Norm_offSupp (K := K) (M := K × K) f).prod (⊤ : Submodule K W)).map Φ.toLinearMap
  have hQ : ∀ f, LinearMap.ker ((tor f).toLinearMap - 1) = Q f := fun f =>
    p9Norm_fix_torC Φ tor htor f
  have hQle : ∀ f f', Q f ≤ Q f' ↔ NoOffOm.SuppLE f' f := by
    intro f f'
    have hmap := Submodule.map_le_map_iff_of_injective (f := Φ.toLinearMap) Φ.injective
      ((p9Norm_offSupp (K := K) (M := K × K) f).prod (⊤ : Submodule K W))
      ((p9Norm_offSupp (K := K) (M := K × K) f').prod (⊤ : Submodule K W))
    exact hmap.trans ((p9Norm_prod_le_prod_iff).trans (p9Norm_offSupp_le_iff f f'))
  exact p9Norm_exists_moveExp_of_conj tor hadd hzero hinj Q hQ hQle g hg

end FrameRoute

namespace ChoiceTwoOm.OmCoord

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)}

theorem exists_moveExp_of_conj (C : OmCoord K Q A)
    {g : V ≃ₗ[K] V} (hg : ∀ c ∈ A, g * c * g⁻¹ ∈ A) :
    ∃ (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool),
      ∀ f, g * C.tor f * g⁻¹ = C.tor (ChoiceTwo.moveExp π η f) := by
  have hg' : ∀ f, ∃ f', g * C.tor f * g⁻¹ = C.tor f' := by
    intro f
    obtain ⟨f', hf'⟩ := C.mem_tor (g * C.tor f * g⁻¹) (hg (C.tor f) (C.tor_mem f))
    exact ⟨f', hf'.symm⟩
  exact CFSG.StandardType.FrameRoute.exists_moveExp_of_conj_torC C.Φ C.tor C.tor_acts g hg'

end ChoiceTwoOm.OmCoord

namespace ChoiceTwo.SpFrame

variable {K : Type} [Field K] {n : ℕ} {L : Type} [Field L] [Algebra K L] {ζ : L}
  {E : Subgroup (CFSG.Open.StatedSp n K)}

private theorem p9Norm_torLE_fix {s : ℕ} (hζ : IsPrimitiveRoot ζ 3)
    (f : Fin s → ZMod 3) :
    LinearMap.ker (((ChoiceTwo.torLE K hζ.pow_eq_one f).toLinearMap) - 1) =
      p9Norm_offSupp (K := K) (M := L) f := by
  ext d
  constructor
  · intro hd
    have h : ChoiceTwo.torE ζ f d = d := by
      simpa [ChoiceTwo.torLE_apply, LinearMap.sub_apply] using sub_eq_zero.mp hd
    intro i hi
    have h1 : ζ ^ (f i).val * d i = d i := by
      simpa [ChoiceTwo.torE_apply] using congrFun h i
    have hne : ζ ^ (f i).val ≠ 1 :=
      hζ.pow_ne_one_of_pos_of_lt (by
        intro hv
        exact hi ((ZMod.val_eq_zero (f i)).mp hv)) (ZMod.val_lt (f i))
    have hmul : (ζ ^ (f i).val - 1) * d i = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
  · intro hd
    funext i
    change ChoiceTwo.torE ζ f d i - d i = 0
    rw [ChoiceTwo.torE_apply]
    by_cases hi : f i = 0
    · rw [hi, ZMod.val_zero, pow_zero, one_mul, sub_self]
    · rw [hd i hi]
      simp

private theorem p9Norm_torLE_add {s : ℕ} (hζ : ζ ^ 3 = 1) (f f' : Fin s → ZMod 3) :
    ChoiceTwo.torLE K hζ (f + f') =
      ChoiceTwo.torLE K hζ f * ChoiceTwo.torLE K hζ f' := by
  apply LinearEquiv.ext
  intro d
  rw [LinearEquiv.mul_apply, ChoiceTwo.torLE_apply, ChoiceTwo.torLE_apply,
    ChoiceTwo.torLE_apply, ChoiceTwo.torE_add hζ]

private theorem p9Norm_torLE_zero {s : ℕ} (hζ : ζ ^ 3 = 1) :
    ChoiceTwo.torLE K hζ (0 : Fin s → ZMod 3) = 1 := by
  apply LinearEquiv.ext
  intro d
  rw [ChoiceTwo.torLE_apply, ChoiceTwo.torE_zero]
  rfl

private theorem p9Norm_toLin_tor (hζ : IsPrimitiveRoot ζ 3) (F : SpFrame K n ζ E)
    (f : Fin F.s → ZMod 3) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n ⊕ Fin n → K)
      (Matrix.GeneralLinearGroup.toLin (F.tor f)) =
      F.Φ.symm.trans ((ChoiceTwo.torLE K hζ.pow_eq_one f).trans F.Φ) := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨d, rfl⟩ := F.Φ.surjective v
  have h1 : LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n ⊕ Fin n → K)
      (Matrix.GeneralLinearGroup.toLin (F.tor f)) (F.Φ d) =
      spEnd (F.tor f) (F.Φ d) := rfl
  rw [h1, F.tor_acts]
  simp [ChoiceTwo.torLE_apply, LinearEquiv.trans_apply]

theorem exists_moveExp_of_conj (hζ : IsPrimitiveRoot ζ 3) (F : SpFrame K n ζ E)
    {g : GL (Fin n ⊕ Fin n) K}
    (hg : ∀ f, ∃ f', g * (F.tor f : GL (Fin n ⊕ Fin n) K) * g⁻¹ = F.tor f') :
    ∃ (π : Equiv.Perm (Fin F.s)) (η : Fin F.s → Bool),
      ∀ f, g * (F.tor f : GL (Fin n ⊕ Fin n) K) * g⁻¹ = F.tor (moveExp π η f) := by
  classical
  let G : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv K _
      (Matrix.GeneralLinearGroup.toLin g)
  let T : (Fin F.s → ZMod 3) → (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) :=
    fun f => F.Φ.symm.trans ((ChoiceTwo.torLE K hζ.pow_eq_one f).trans F.Φ)
  have hT : ∀ f, LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n ⊕ Fin n → K)
      (Matrix.GeneralLinearGroup.toLin (F.tor f)) = T f := fun f =>
    p9Norm_toLin_tor hζ F f
  have hTadd : ∀ f f', T (f + f') = T f * T f' := fun f f' =>
    LinearEquiv.ext fun v => by simp [T, LinearEquiv.mul_apply, p9Norm_torLE_add hζ.pow_eq_one]
  have hTzero : T 0 = 1 :=
    LinearEquiv.ext fun v => by simp [T, p9Norm_torLE_zero hζ.pow_eq_one]
  have hTinj : Function.Injective T := by
    intro f f' h
    apply F.tor_injective hζ
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.toLin.injective
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n ⊕ Fin n → K)).injective
    rw [hT f, hT f']
    exact h
  let Q : (Fin F.s → ZMod 3) → Submodule K (Fin n ⊕ Fin n → K) := fun f =>
    (p9Norm_offSupp (K := K) (M := L) f).map F.Φ.toLinearMap
  have hQ : ∀ f, LinearMap.ker ((T f).toLinearMap - 1) = Q f := by
    intro f
    simp only [T, Q]
    rw [p9Norm_fix_iso (e := F.Φ) (t := ChoiceTwo.torLE K hζ.pow_eq_one f),
      p9Norm_torLE_fix hζ f]
  have hQle : ∀ f f', Q f ≤ Q f' ↔ NoOffOm.SuppLE f' f := by
    intro f f'
    simp only [Q]
    rw [Submodule.map_le_map_iff_of_injective (f := F.Φ.toLinearMap) F.Φ.injective _ _]
    exact p9Norm_offSupp_le_iff f f'
  have hgT : ∀ f, ∃ f', G * T f * G⁻¹ = T f' := by
    intro f
    obtain ⟨f', hf'⟩ := hg f
    refine ⟨f', ?_⟩
    have h := congrArg (fun Y : GL (Fin n ⊕ Fin n) K =>
      LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n ⊕ Fin n → K)
        (Matrix.GeneralLinearGroup.toLin Y)) hf'
    simp only [map_mul, MulEquiv.map_inv] at h
    rw [hT f, hT f'] at h
    exact h
  obtain ⟨π, η, hπη⟩ :=
    p9Norm_exists_moveExp_of_conj T hTadd hTzero hTinj Q hQ hQle G hgT
  refine ⟨π, η, fun f => ?_⟩
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n ⊕ Fin n → K)).injective
  simp only [map_mul, MulEquiv.map_inv]
  rw [hT f, hT (ChoiceTwo.moveExp π η f)]
  exact hπη f

end ChoiceTwo.SpFrame

end CFSG.StandardType
