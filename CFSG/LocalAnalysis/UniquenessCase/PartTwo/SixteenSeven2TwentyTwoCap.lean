module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoX
public import CFSG.Quasithin.Background.F918V2F
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_realizesVia_of_iso {W : Type} [CommGroup W] {D : FFModel}
    {H : Subgroup (MulAut W)} {U U' : Subgroup W} {π : D.Gam →* ↥H}
    (hU : StableUnder H U) (hU' : StableUnder H U')
    (j : ↥U ≃* ↥U') (hj : Z391.V2fEqv ↥H j)
    (h : D.RealizesVia H U ⊥ π) : D.RealizesVia H U' ⊥ π := by
  obtain ⟨hπs, -, hks, -, hZinv, hsec, hker, β, hβs, hβk, hβe⟩ := h
  refine ⟨hπs, bot_le, hks, fun h u hu => hU' h h.2 u hu, fun h z hz => ?_,
    hsec, hker, β.comp j.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro y
    obtain ⟨u, hu⟩ := hβs y
    exact ⟨j u, by simpa using hu⟩
  · intro u
    show β (j.symm u) = 1 ↔ _
    rw [hβk (j.symm u), Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : j.symm u = 1 := Subtype.ext h
      have h2 : u = 1 := by rw [← j.apply_symm_apply u, h1, map_one]
      exact congrArg Subtype.val h2
    · intro h
      have h1 : u = 1 := Subtype.ext h
      have h2 : j.symm u = 1 := by rw [h1, map_one]
      exact congrArg Subtype.val h2
  · intro γ u m hu hm hβu
    simp only [MonoidHom.comp_apply]
    change β (j.symm ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩) = _
    have hjinv : j.symm ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ =
        ⟨((π γ : ↥H) : MulAut W) (j.symm u : W),
          hU (π γ) (π γ).2 (j.symm u : W) (j.symm u).2⟩ := by
      apply Subtype.ext
      have h1 := hj (π γ) (j.symm u)
        ⟨((π γ : ↥H) : MulAut W) (j.symm u : W),
          hU (π γ) (π γ).2 (j.symm u : W) (j.symm u).2⟩ rfl
      have h2 : ((π γ : ↥H) : MulAut W) (u : W) =
          (j ⟨((π γ : ↥H) : MulAut W) (j.symm u : W),
            hU (π γ) (π γ).2 (j.symm u : W) (j.symm u).2⟩ : W) := by
        simpa only [Subgroup.smul_def, MulAut.smul_def, MulEquiv.apply_symm_apply] using h1
      have h3 : (⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ : ↥U') =
          j ⟨((π γ : ↥H) : MulAut W) (j.symm u : W),
            hU (π γ) (π γ).2 (j.symm u : W) (j.symm u).2⟩ := Subtype.ext h2
      rw [h3, MulEquiv.symm_apply_apply]
    rw [hjinv]
    exact hβe γ (j.symm u) m _ hm hβu

private theorem s16c167_realizes_of_iso {W : Type} [CommGroup W] {D : FFModel}
    {H : Subgroup (MulAut W)} {U U' : Subgroup W}
    (hU : StableUnder H U) (hU' : StableUnder H U')
    (j : ↥U ≃* ↥U') (hj : Z391.V2fEqv ↥H j)
    (h : D.Realizes H U ⊥) : D.Realizes H U' ⊥ := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π, s16c167_realizesVia_of_iso hU hU' j hj hπ⟩

private theorem s16c167_alternatingNatural_of_iso {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {U U' : Subgroup W}
    (hU : StableUnder H U) (hU' : StableUnder H U')
    (j : ↥U ≃* ↥U') (hj : Z391.V2fEqv ↥H j) {n : ℕ}
    (h : AlternatingNatural H U ⊥ n) : AlternatingNatural H U' ⊥ n :=
  s16c167_realizes_of_iso (D := FFModel.altDn n) hU hU' j hj h

private theorem s16c167_natOmegaMinus_of_iso {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {U U' : Subgroup W}
    (hU : StableUnder H U) (hU' : StableUnder H U')
    (j : ↥U ≃* ↥U') (hj : Z391.V2fEqv ↥H j) {n a : ℕ}
    (h : NatOmegaMinus H U ⊥ n a) : NatOmegaMinus H U' ⊥ n a := by
  obtain ⟨he, K, hK, hKf, b, c, hK2, hpoly, hr⟩ := h
  exact ⟨he, K, hK, hKf, b, c, hK2, hpoly,
    s16c167_realizes_of_iso (D := FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K b c)))
      hU hU' j hj hr⟩

private theorem s16c167_xmod_isIrr_iff {W : Type} [CommGroup W] (L : Subgroup (MulAut W))
    (J : Subgroup W) : IsIrrOn L J ⊥ ↔ XMod.IsIrr ↥L J := by
  unfold IsIrrOn XMod.IsIrr XMod.IsIrrSec XMod.IsInv StableUnder
  constructor
  · rintro ⟨hlt, hstab, -, hmin⟩
    exact ⟨fun a j hj => hstab a a.2 j hj, hlt,
      fun J' hJ' _ hJ'J => hmin J' (fun a ha u hu => hJ' ⟨a, ha⟩ u hu) bot_le hJ'J⟩
  · rintro ⟨hinv, hlt, hmin⟩
    exact ⟨hlt, (fun a ha u hu => hinv ⟨a, ha⟩ u hu),
      (fun a _ u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]),
      fun J' hJ' _ hJ'J => hmin J' (fun a u hu => hJ' (a : MulAut W) a.2 u hu) bot_le hJ'J⟩

private theorem s16c167_isIrrOn_bot_of_mem_irrSet {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥) {J : Subgroup W} (hJ : J ∈ irrSet L) :
    IsIrrOn L J ⊥ := by
  have h := hJ.2
  rwa [hfix, inf_bot_eq] at h

private theorem s16c167_alt_of_mem_irrSet {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥) {J₀ J₁ : Subgroup W} {n : ℕ}
    (hJ₀ : J₀ ∈ irrSet L) (hJ₁ : J₁ ∈ irrSet L) (hinf : J₀ ⊓ J₁ = ⊥) (hsup : J₀ ⊔ J₁ = ⊤)
    (hN₀ : AlternatingNatural L J₀ ⊥ n) (hN₁ : AlternatingNatural L J₁ ⊥ n)
    {K : Subgroup W} (hK : K ∈ irrSet L) : AlternatingNatural L K ⊥ n := by
  by_cases hK0 : K = J₀
  · rwa [hK0]
  by_cases hK1 : K = J₁
  · rwa [hK1]
  have hIrr₀ : XMod.IsIrr ↥L J₀ :=
    (s16c167_xmod_isIrr_iff L J₀).1 (s16c167_isIrrOn_bot_of_mem_irrSet hfix hJ₀)
  have hIrr₁ : XMod.IsIrr ↥L J₁ :=
    (s16c167_xmod_isIrr_iff L J₁).1 (s16c167_isIrrOn_bot_of_mem_irrSet hfix hJ₁)
  have hIrrK : XMod.IsIrr ↥L K :=
    (s16c167_xmod_isIrr_iff L K).1 (s16c167_isIrrOn_bot_of_mem_irrSet hfix hK)
  have hKle : K ≤ J₀ ⊔ J₁ := by rw [hsup]; exact le_top
  have hK₀ : K ⊓ J₀ = ⊥ := Z391.v2f_inf_eq_bot hIrrK hIrr₀ hK0
  have hK₁ : K ⊓ J₁ = ⊥ := Z391.v2f_inf_eq_bot hIrrK hIrr₁ hK1
  obtain ⟨θ, hθe, hθ⟩ :=
    Z391.v2f_exists_graph hIrr₀ hIrr₁ hIrrK.1 hIrrK.2.1.ne' hKle hK₀ hK₁
  have hψmem : ∀ x : ↥J₀, (x : W) * (θ x : W) ∈ K := fun x => (hθ x (θ x)).2 rfl
  let ψ : ↥J₀ →* ↥K :=
    { toFun := fun x => ⟨(x : W) * (θ x : W), hψmem x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show (x : W) * (y : W) * (θ (x * y) : W) =
          ((x : W) * (θ x : W)) * ((y : W) * (θ y : W))
        rw [map_mul]
        ac_rfl }
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : (x : W) * (θ x : W) = (y : W) * (θ y : W) := congrArg Subtype.val hxy
    have h2 : (y : W)⁻¹ * (x : W) = (θ y : W) * (θ x : W)⁻¹ := by
      calc (y : W)⁻¹ * (x : W) =
            (y : W)⁻¹ * ((x : W) * (θ x : W)) * (θ x : W)⁻¹ := by group
        _ = (y : W)⁻¹ * ((y : W) * (θ y : W)) * (θ x : W)⁻¹ := by rw [h1]
        _ = (θ y : W) * (θ x : W)⁻¹ := by group
    have h3 : (x : W) * (y : W)⁻¹ = (θ y : W) * (θ x : W)⁻¹ := by
      rw [mul_comm]; exact h2
    have hxyJ₀ : (x : W) * (y : W)⁻¹ ∈ J₀ := J₀.mul_mem x.2 (J₀.inv_mem y.2)
    have hxyJ₁ : (x : W) * (y : W)⁻¹ ∈ J₁ := by
      have hinv : ((x : W) * (y : W)⁻¹)⁻¹ ∈ J₁ := by
        have h4 : ((x : W) * (y : W)⁻¹)⁻¹ = (θ x : W) * (θ y : W)⁻¹ := by
          rw [h3]; group
        rw [h4]
        exact J₁.mul_mem (θ x).2 (J₁.inv_mem (θ y).2)
      simpa using J₁.inv_mem hinv
    have hbot : (x : W) * (y : W)⁻¹ ∈ (⊥ : Subgroup W) := by
      rw [← hinf]
      exact Subgroup.mem_inf.2 ⟨hxyJ₀, hxyJ₁⟩
    exact Subtype.ext (mul_inv_eq_one.1 (Subgroup.mem_bot.1 hbot))
  have hψsurj : Function.Surjective ψ := by
    intro k
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.1 (hKle k.2)
    have hk : (x : W) * (y : W) ∈ K := hxy ▸ k.2
    have hθx : θ ⟨x, hx⟩ = ⟨y, hy⟩ := (hθ ⟨x, hx⟩ ⟨y, hy⟩).1 hk
    exact ⟨⟨x, hx⟩, Subtype.ext (by
      show (x : W) * (θ ⟨x, hx⟩ : W) = (k : W)
      rw [hθx]
      exact hxy)⟩
  let ψe : ↥J₀ ≃* ↥K := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hψeqv : Z391.V2fEqv ↥L ψe := by
    intro a x x' hxx
    have hθx : θ ⟨a • (x : W), hIrr₀.1 a (x : W) x.2⟩ = ⟨a • (θ x : W),
        hIrr₁.1 a (θ x : W) (θ x).2⟩ := by
      apply Subtype.ext
      exact (hθe a x ⟨a • (x : W), hIrr₀.1 a (x : W) x.2⟩ rfl).symm
    have hx' : x' = ⟨a • (x : W), hIrr₀.1 a (x : W) x.2⟩ := Subtype.ext hxx.symm
    rw [hx']
    change a • ((x : W) * (θ x : W)) =
      (a • (x : W)) * (θ ⟨a • (x : W), hIrr₀.1 a (x : W) x.2⟩ : W)
    rw [smul_mul', hθx]
  have hstab₀ : StableUnder L J₀ := fun x hx u hu => hIrr₀.1 ⟨x, hx⟩ u hu
  have hstabK : StableUnder L K := fun x hx u hu => hIrrK.1 ⟨x, hx⟩ u hu
  exact s16c167_alternatingNatural_of_iso hstab₀ hstabK ψe hψeqv hN₀

private theorem s16c167_omega_of_mem_irrSet {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥) {J₀ J₁ : Subgroup W} {n a : ℕ}
    (hJ₀ : J₀ ∈ irrSet L) (hJ₁ : J₁ ∈ irrSet L) (hinf : J₀ ⊓ J₁ = ⊥) (hsup : J₀ ⊔ J₁ = ⊤)
    (hN₀ : NatOmegaMinus L J₀ ⊥ n a) (hN₁ : NatOmegaMinus L J₁ ⊥ n a)
    {K : Subgroup W} (hK : K ∈ irrSet L) : NatOmegaMinus L K ⊥ n a := by
  by_cases hK0 : K = J₀
  · rwa [hK0]
  by_cases hK1 : K = J₁
  · rwa [hK1]
  have hIrr₀ : XMod.IsIrr ↥L J₀ :=
    (s16c167_xmod_isIrr_iff L J₀).1 (s16c167_isIrrOn_bot_of_mem_irrSet hfix hJ₀)
  have hIrr₁ : XMod.IsIrr ↥L J₁ :=
    (s16c167_xmod_isIrr_iff L J₁).1 (s16c167_isIrrOn_bot_of_mem_irrSet hfix hJ₁)
  have hIrrK : XMod.IsIrr ↥L K :=
    (s16c167_xmod_isIrr_iff L K).1 (s16c167_isIrrOn_bot_of_mem_irrSet hfix hK)
  have hKle : K ≤ J₀ ⊔ J₁ := by rw [hsup]; exact le_top
  have hK₀ : K ⊓ J₀ = ⊥ := Z391.v2f_inf_eq_bot hIrrK hIrr₀ hK0
  have hK₁ : K ⊓ J₁ = ⊥ := Z391.v2f_inf_eq_bot hIrrK hIrr₁ hK1
  obtain ⟨θ, hθe, hθ⟩ :=
    Z391.v2f_exists_graph hIrr₀ hIrr₁ hIrrK.1 hIrrK.2.1.ne' hKle hK₀ hK₁
  have hψmem : ∀ x : ↥J₀, (x : W) * (θ x : W) ∈ K := fun x => (hθ x (θ x)).2 rfl
  let ψ : ↥J₀ →* ↥K :=
    { toFun := fun x => ⟨(x : W) * (θ x : W), hψmem x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show (x : W) * (y : W) * (θ (x * y) : W) =
          ((x : W) * (θ x : W)) * ((y : W) * (θ y : W))
        rw [map_mul]
        ac_rfl }
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : (x : W) * (θ x : W) = (y : W) * (θ y : W) := congrArg Subtype.val hxy
    have h2 : (y : W)⁻¹ * (x : W) = (θ y : W) * (θ x : W)⁻¹ := by
      calc (y : W)⁻¹ * (x : W) =
            (y : W)⁻¹ * ((x : W) * (θ x : W)) * (θ x : W)⁻¹ := by group
        _ = (y : W)⁻¹ * ((y : W) * (θ y : W)) * (θ x : W)⁻¹ := by rw [h1]
        _ = (θ y : W) * (θ x : W)⁻¹ := by group
    have h3 : (x : W) * (y : W)⁻¹ = (θ y : W) * (θ x : W)⁻¹ := by
      rw [mul_comm]; exact h2
    have hxyJ₀ : (x : W) * (y : W)⁻¹ ∈ J₀ := J₀.mul_mem x.2 (J₀.inv_mem y.2)
    have hxyJ₁ : (x : W) * (y : W)⁻¹ ∈ J₁ := by
      have hinv : ((x : W) * (y : W)⁻¹)⁻¹ ∈ J₁ := by
        have h4 : ((x : W) * (y : W)⁻¹)⁻¹ = (θ x : W) * (θ y : W)⁻¹ := by
          rw [h3]; group
        rw [h4]
        exact J₁.mul_mem (θ x).2 (J₁.inv_mem (θ y).2)
      simpa using J₁.inv_mem hinv
    have hbot : (x : W) * (y : W)⁻¹ ∈ (⊥ : Subgroup W) := by
      rw [← hinf]
      exact Subgroup.mem_inf.2 ⟨hxyJ₀, hxyJ₁⟩
    exact Subtype.ext (mul_inv_eq_one.1 (Subgroup.mem_bot.1 hbot))
  have hψsurj : Function.Surjective ψ := by
    intro k
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.1 (hKle k.2)
    have hk : (x : W) * (y : W) ∈ K := hxy ▸ k.2
    have hθx : θ ⟨x, hx⟩ = ⟨y, hy⟩ := (hθ ⟨x, hx⟩ ⟨y, hy⟩).1 hk
    exact ⟨⟨x, hx⟩, Subtype.ext (by
      show (x : W) * (θ ⟨x, hx⟩ : W) = (k : W)
      rw [hθx]
      exact hxy)⟩
  let ψe : ↥J₀ ≃* ↥K := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hψeqv : Z391.V2fEqv ↥L ψe := by
    intro a x x' hxx
    have hθx : θ ⟨a • (x : W), hIrr₀.1 a (x : W) x.2⟩ = ⟨a • (θ x : W),
        hIrr₁.1 a (θ x : W) (θ x).2⟩ := by
      apply Subtype.ext
      exact (hθe a x ⟨a • (x : W), hIrr₀.1 a (x : W) x.2⟩ rfl).symm
    have hx' : x' = ⟨a • (x : W), hIrr₀.1 a (x : W) x.2⟩ := Subtype.ext hxx.symm
    rw [hx']
    change a • ((x : W) * (θ x : W)) =
      (a • (x : W)) * (θ ⟨a • (x : W), hIrr₀.1 a (x : W) x.2⟩ : W)
    rw [smul_mul', hθx]
  have hstab₀ : StableUnder L J₀ := fun x hx u hu => hIrr₀.1 ⟨x, hx⟩ u hu
  have hstabK : StableUnder L K := fun x hx u hu => hIrrK.1 ⟨x, hx⟩ u hu
  exact s16c167_natOmegaMinus_of_iso hstab₀ hstabK ψe hψeqv hN₀

private theorem s16c167_conj_conj {g u m : G} (hm : m = g * u * g⁻¹)
    (I : Subgroup G) :
    conjSubgroup (conjSubgroup I g) u = conjSubgroup (conjSubgroup I m) g := by
  rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, hm]
  congr 1
  group

private theorem s16c167_conjSubgroup_inj {A B : Subgroup G} {g : G}
    (h : conjSubgroup A g = conjSubgroup B g) : A = B := by
  have hc := congrArg (fun C : Subgroup G => conjSubgroup C g⁻¹) h
  rwa [E3.conjSubgroup_conj_inv, E3.conjSubgroup_conj_inv] at hc

private theorem s16c167_conj_centralizer_singleton {g u m : G}
    (hm : m = g * u * g⁻¹) :
    conjSubgroup (Subgroup.centralizer ({m} : Set G)) g =
      Subgroup.centralizer ({u} : Set G) := by
  subst hm
  ext x
  rw [mem_conjSubgroup_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg (fun y => g⁻¹ * y * g) h
    group at h'
    exact h'
  · intro h
    have h' := congrArg (fun y => g * y * g⁻¹) h
    group at h' ⊢
    exact h'

private theorem s16c167_imgTil_inj {V U U' : Subgroup G}
    (hV : IsElemAbelian 2 V) (hU : U ≤ V) (hU' : U' ≤ V)
    (h : imgTil ⊥ V hV U = imgTil ⊥ V hV U') : U = U' := by
  have hmk : Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
    intro x y hxy
    rw [mkTil_eq_iff, Subgroup.mem_bot] at hxy
    exact IntMod.val_injective (mul_inv_eq_one.1 hxy)
  have hmain : (intSub V hV U).map (mkTil (⊥ : Subgroup G) V hV) =
      (intSub V hV U').map (mkTil (⊥ : Subgroup G) V hV) := h
  have h1 : intSub V hV U = intSub V hV U' := Subgroup.map_injective hmk hmain
  have h2 : (U.subgroupOf V).map V.subtype = (U'.subgroupOf V).map V.subtype := by
    simpa only [intSub] using congrArg (Subgroup.map V.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hU, Subgroup.map_subgroupOf_eq_of_le hU'] at h2

private theorem s16c167_imgTil_le_iff {V U U' : Subgroup G}
    (hV : IsElemAbelian 2 V) (hU : U ≤ V) (hU' : U' ≤ V) :
    imgTil ⊥ V hV U ≤ imgTil ⊥ V hV U' ↔ U ≤ U' := by
  constructor
  · intro h
    have h1 : imgTil ⊥ V hV (U ⊓ U') = imgTil ⊥ V hV U := by
      rw [s16c167_imgTil_inf_bot hV, inf_eq_left.2 h]
    exact inf_eq_left.1 (s16c167_imgTil_inj hV (le_trans inf_le_left hU) hU h1)
  · intro h
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono V h)

theorem s16c167_twenty_two_cap (D : Data G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hC : Counterex16 D ⊥ V L hV)
    (h14 : ((D.k + 2 : ℕ) : ℕ∞) < rMV D.M V) {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)}
    (hA : Choice1613 D ⊥ V hV L A) (hAg : A ≤ conjSubgroup V g)
    (hΔ : Concl1617 D ⊥ V hV L A g Δ) (hI : Insp18 D ⊥ V hV L g Δ)
    (h2 : Case168_2 D ⊥ V hV L) (hS : Case168_2Small D ⊥ V hV L)
    (hn4 : ¬ IsLn ↥(lBar ⊥ V hV L) 4 1) {B U : Subgroup G} (hBU : Hyperplane1618 V A B U) :
    E3.mQuot U (V ⊓ centralizer (A : Set G)) ≤ 1 := by
  have hW2 : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hW2inv : ∀ w : Vtil ⊥ V hV, w⁻¹ = w := by
    intro w
    have h : w * w = 1 := by rw [← pow_two]; exact hW2 w
    exact inv_eq_of_mul_eq_one_right h
  have hnat : ∀ K ∈ irrSet (lBar ⊥ V hV L),
      AlternatingNatural (lBar ⊥ V hV L) K ⊥ 6 ∨
        AlternatingNatural (lBar ⊥ V hV L) K ⊥ 7 ∨
        NatOmegaMinus (lBar ⊥ V hV L) K ⊥ 6 1 := by
    intro K hK
    have hfix : fixV (lBar ⊥ V hV L) = ⊥ := s16c167_cfg2_fix D h2
    obtain ⟨L₀, -, hfam⟩ := hS.2.1
    rcases hfam with h6 | h7 | h4 | hom
    · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two h6.2.2
      exact Or.inl (s16c167_alt_of_mem_irrSet hfix
        (s16c167_mem_irrSet_alt (n := 6) (by norm_num) hN₀)
        (s16c167_mem_irrSet_alt (n := 6) (by norm_num) hN₁) hinf hsup hN₀ hN₁ hK)
    · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two h7.2.2
      exact Or.inr (Or.inl (s16c167_alt_of_mem_irrSet hfix
        (s16c167_mem_irrSet_alt (n := 7) (by norm_num) hN₀)
        (s16c167_mem_irrSet_alt (n := 7) (by norm_num) hN₁) hinf hsup hN₀ hN₁ hK))
    · exact absurd h4.2.1 hn4
    · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hom.2.2
      exact Or.inr (Or.inr (s16c167_omega_of_mem_irrSet hfix
        (s16c167_mem_irrSet_omegaMinus (Or.inl rfl) hN₀)
        (s16c167_mem_irrSet_omegaMinus (Or.inl rfl) hN₁) hinf hsup hN₀ hN₁ hK))
  have hleaf : ∀ (I : Subgroup G), I ∈ Δ → ∀ (t t' : MulAut (Vtil ⊥ V hV)),
      (lBar ⊥ V hV L).map (MulAut.conj t).toMonoidHom = lBar ⊥ V hV L →
      (lBar ⊥ V hV L).map (MulAut.conj t').toMonoidHom = lBar ⊥ V hV L →
      (imgTil ⊥ V hV I).map t.toMonoidHom = imgTil ⊥ V hV I →
      (imgTil ⊥ V hV I).map t'.toMonoidHom = imgTil ⊥ V hV I →
      (∀ e ∈ imgTil ⊥ V hV I ⊓ fixV (Subgroup.zpowers t), t e = e) →
      (∀ e ∈ imgTil ⊥ V hV I ⊓ fixV (Subgroup.zpowers t), t' e = e) →
      (∀ e ∈ imgTil ⊥ V hV I, t e * e⁻¹ ∈ imgTil ⊥ V hV I ⊓ fixV (Subgroup.zpowers t)) →
      (∀ e ∈ imgTil ⊥ V hV I, t' e * e⁻¹ ∈ imgTil ⊥ V hV I ⊓ fixV (Subgroup.zpowers t)) →
      E3.mQuot (imgTil ⊥ V hV I) (imgTil ⊥ V hV I ⊓ fixV (Subgroup.zpowers t)) = 1 →
      (∀ e ∈ imgTil ⊥ V hV I, t e = e) ∨ (∀ e ∈ imgTil ⊥ V hV I, t' e = e) ∨
        (∀ e ∈ imgTil ⊥ V hV I, t e = t' e) := by
    intro I hI t t' hxL hyL hxE hyE hxH hyH hxT hyT hH
    rcases hnat (imgTil ⊥ V hV I) (hΔ.2.2.2.2.1 h2 I hI) with h6 | h7 | hom
    · exact s16c167_transv_unique_alt hW2 (n := 6) (by norm_num) h6 hxL hyL hxE hyE
        inf_le_left hH hxH hyH hxT hyT
    · exact s16c167_transv_unique_alt hW2 (n := 7) (by norm_num) h7 hxL hyL hxE hyE
        inf_le_left hH hxH hyH hxT hyT
    · exact s16c167_transv_unique_omega hW2 hom hxL hyL hxE hyE
        inf_le_left hH hxH hyH hxT hyT
  have hBA : B ≤ A := hBU.1
  have hUeq : U = V ⊓ centralizer (B : Set G) := hBU.2.2.1
  have hUne : U ≠ V ⊓ centralizer (A : Set G) := hBU.2.2.2
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hM : D.M ≤ normalizer (V : Set G) :=
    le_of_eq hC.setting.hyp16.hyp125.normalizer_eq.symm
  have h18 := s16c167_eighteen_core D hV hC.setting.hyp16 h14 hA.1 hAg hΔ hI hBU
  have hmB : E3.mQuot (conjSubgroup V g) B = D.k + 1 := h18.1.1.trans h18.1.2
  have hBg : B ∈ E3.gammaSet V (D.k + 1) D.M :=
    ⟨hBA.trans (hA.1.1.trans D.sylowM.le), g, hBA.trans hAg, hmB⟩
  have h0 : mSub (⊥ : Subgroup G) = 0 := by
    rw [mSub]
    exact rk_bot
  have hi : ((D.k + 1 + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V := by
    rw [h0, Nat.add_zero]
    exact lt_trans (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self (D.k + 1))) h14
  have hUM : U ≤ conjSubgroup D.M g := by
    rw [hUeq]
    exact (sixteen_twentyThree_one_bot D hC.setting.hyp16 hBg (hBA.trans hAg) hi).2.2
  have hUV : U ≤ V := by rw [hUeq]; exact inf_le_left
  have hUCB : U ≤ centralizer (B : Set G) := by rw [hUeq]; exact inf_le_right
  have hsimple : IsSimpleGroup ↥(lBar ⊥ V hV L) := s16c167_cfg2_simple D h2
  have hLbot : lBar ⊥ V hV L ≠ ⊥ := by
    haveI := hsimple.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  obtain ⟨a₀, b₀, hab₀, hΔab₀⟩ := Set.ncard_eq_two.1 hΔ.1
  have hmem_a₀ : imgTil ⊥ V hV a₀ ∈ irrBar L ⊥ V hV := by
    refine hΔ.2.2.2.2.1 h2 a₀ ?_
    rw [hΔab₀]
    exact Set.mem_insert_iff.2 (Or.inl rfl)
  have hmem_b₀ : imgTil ⊥ V hV b₀ ∈ irrBar L ⊥ V hV := by
    refine hΔ.2.2.2.2.1 h2 b₀ ?_
    rw [hΔab₀]
    exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 rfl))
  have hsup₀ : imgTil ⊥ V hV a₀ ⊔ imgTil ⊥ V hV b₀ = ⊤ := by
    have ha₀Δ : a₀ ∈ Δ := by
      rw [hΔab₀]; exact Set.mem_insert_iff.2 (Or.inl rfl)
    have hb₀Δ : b₀ ∈ Δ := by
      rw [hΔab₀]; exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 rfl))
    have hab : a₀ ⊔ b₀ = V := by
      have h := hΔ.2.2.2.1
      rw [hΔab₀, sSup_pair] at h
      exact h
    have hmap : imgTil ⊥ V hV (a₀ ⊔ b₀) = imgTil ⊥ V hV a₀ ⊔ imgTil ⊥ V hV b₀ := by
      have hsub : intSub V hV (a₀ ⊔ b₀) = intSub V hV a₀ ⊔ intSub V hV b₀ :=
        Subgroup.subgroupOf_sup (A := a₀) (A' := b₀) (B := V)
          (hΔ.2.1 a₀ ha₀Δ) (hΔ.2.1 b₀ hb₀Δ)
      have h2 := congrArg (Subgroup.map (mkTil ⊥ V hV)) hsub
      rw [Subgroup.map_sup] at h2
      exact h2
    rw [← hmap, hab, ← imgTil_preTil ⊥ V hV ⊤, preTil_top]
  have hall : commSub ⊤ (lBar ⊥ V hV L) = ⊤ := by
    refine top_le_iff.1 (hsup₀.symm.le.trans (sup_le ?_ ?_))
    · calc imgTil ⊥ V hV a₀ = commSub (imgTil ⊥ V hV a₀) (lBar ⊥ V hV L) := hmem_a₀.1.symm
        _ ≤ commSub ⊤ (lBar ⊥ V hV L) := commSub_mono le_top le_rfl
    · calc imgTil ⊥ V hV b₀ = commSub (imgTil ⊥ V hV b₀) (lBar ⊥ V hV L) := hmem_b₀.1.symm
        _ ≤ commSub ⊤ (lBar ⊥ V hV L) := commSub_mono le_top le_rfl
  obtain ⟨t136, -, -, -, -, hW136⟩ := hC.conc
  have hnorm : ∀ x ∈ Mbar D.M ⊥ V hV,
      (lBar ⊥ V hV L).map (MulAut.conj x).toMonoidHom = lBar ⊥ V hV L :=
    s16c167_cfg2_normal hLbot hall hW136
  have hBle : ∀ u ∈ U, B ≤ conjSubgroup V g ⊓ centralizer ({u} : Set G) := by
    intro u hu
    refine le_inf ?_ ?_
    · rw [h18.2.1.1]; exact inf_le_left
    · intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 (hUCB hu) b hb
  have hfixΓ : ∀ u ∈ U, ∀ J ∈ deltaConj Δ g, conjSubgroup J u = J := by
    intro u hu J hJ
    have huVM : u ∈ V ⊓ conjSubgroup D.M g := ⟨hUV hu, hUM hu⟩
    have hmq : E3.mQuot (conjSubgroup V g)
        (conjSubgroup V g ⊓ centralizer ({u} : Set G)) ≤ D.k + 1 := by
      calc E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({u} : Set G))
          ≤ E3.mQuot (conjSubgroup V g) B := E3.mQuot_mono (hBle u hu)
        _ = D.k + 1 := hmB
    rcases hI.disj u huVM hmq J hJ with hfix | hbot
    · exact hfix
    · exfalso
      obtain ⟨I, hI', rfl⟩ := hJ
      have hJle : conjSubgroup I g ≤ conjSubgroup V g :=
        E3.conjSubgroup_mono_left g (hΔ.2.1 I hI')
      have hle := s16c167_swap_rk_le hVg hJle hbot rfl
      exact absurd (hI.big (conjSubgroup I g) ⟨I, hI', rfl⟩) (not_lt.2 (hle.trans hmq))
  have htriv_or_axis : ∀ u ∈ U, conjSubgroup V g ≤ centralizer ({u} : Set G) ∨
      conjSubgroup V g ⊓ centralizer ({u} : Set G) = B := by
    intro u hu
    by_cases htriv : conjSubgroup V g ≤ centralizer ({u} : Set G)
    · exact Or.inl htriv
    · refine Or.inr (s16c167_eq_of_mQuot_le hVg (hBle u hu) inf_le_left ?_)
      set m : G := g * u * g⁻¹ with hm
      have hmM : m ∈ D.M := by rw [hm]; exact mem_conjSubgroup_iff.1 (hUM hu)
      have hm_stab : m ∈ stabTil (⊥ : Subgroup G) V := s16c167_mem_stabTil_bot (hM hmM)
      have hm2 : m ^ 2 = 1 := by
        rw [hm, pow_two]
        calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
          _ = 1 := by
            rw [← pow_two, hV.2 u (hUV hu)]
            group
      have hne : ¬ V ≤ centralizer ({m} : Set G) := by
        intro hle
        apply htriv
        rw [← s16c167_conj_centralizer_singleton hm]
        exact E3.conjSubgroup_mono_left g hle
      have hbar := s16c167_mBar_le_mQuot hV hM hmM hm2 hne
      have hconj : E3.mQuot V (V ⊓ centralizer ({m} : Set G)) =
          E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({u} : Set G)) := by
        rw [← E3.mQuot_conjSubgroup V (V ⊓ centralizer ({m} : Set G)) g]
        congr 1
        rw [E3.conjSubgroup_inf, s16c167_conj_centralizer_singleton hm]
      calc E3.mQuot (conjSubgroup V g) B = mBar D.M ⊥ V hV := h18.1.1
        _ ≤ E3.mQuot V (V ⊓ centralizer ({m} : Set G)) := hbar
        _ = E3.mQuot (conjSubgroup V g)
              (conjSubgroup V g ⊓ centralizer ({u} : Set G)) := hconj
  have hact : ∀ u ∈ U, ∀ u' ∈ U,
      ¬ conjSubgroup V g ≤ centralizer ({u} : Set G) →
      ¬ conjSubgroup V g ≤ centralizer ({u'} : Set G) →
      ∀ J ∈ deltaConj Δ g, ∀ j ∈ J, u * j * u⁻¹ = u' * j * u'⁻¹ := by
    intro u hu u' hu' hnu hnu' J hJ j hj
    obtain ⟨I, hI, rfl⟩ := hJ
    have hiI : g * j * g⁻¹ ∈ I := mem_conjSubgroup_iff.1 hj
    have hiV : g * j * g⁻¹ ∈ V := hΔ.2.1 I hI hiI
    set m : G := g * u * g⁻¹ with hm
    set m' : G := g * u' * g⁻¹ with hm'
    have hmM : m ∈ D.M := by rw [hm]; exact mem_conjSubgroup_iff.1 (hUM hu)
    have hmM' : m' ∈ D.M := by rw [hm']; exact mem_conjSubgroup_iff.1 (hUM hu')
    have hm_stab : m ∈ stabTil (⊥ : Subgroup G) V := s16c167_mem_stabTil_bot (hM hmM)
    have hm_stab' : m' ∈ stabTil (⊥ : Subgroup G) V := s16c167_mem_stabTil_bot (hM hmM')
    have hm2 : m ^ 2 = 1 := by
      rw [hm, pow_two]
      calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
        _ = 1 := by
          rw [← pow_two, hV.2 u (hUV hu)]
          group
    have hm2' : m' ^ 2 = 1 := by
      rw [hm', pow_two]
      calc (g * u' * g⁻¹) * (g * u' * g⁻¹) = g * (u' * u') * g⁻¹ := by group
        _ = 1 := by
          rw [← pow_two, hV.2 u' (hUV hu')]
          group
    let t : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨m, hm_stab⟩
    let t' : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨m', hm_stab'⟩
    have ht2 : t * t = 1 := by
      change actTil ⊥ V hV ⟨m, hm_stab⟩ * actTil ⊥ V hV ⟨m, hm_stab⟩ = 1
      have hmul : (⟨m, hm_stab⟩ : stabTil (⊥ : Subgroup G) V) * ⟨m, hm_stab⟩ = 1 := by
        apply Subtype.ext
        show m * m = 1
        rw [← pow_two]; exact hm2
      rw [← map_mul, hmul, map_one]
    have ht2' : t' * t' = 1 := by
      change actTil ⊥ V hV ⟨m', hm_stab'⟩ * actTil ⊥ V hV ⟨m', hm_stab'⟩ = 1
      have hmul : (⟨m', hm_stab'⟩ : stabTil (⊥ : Subgroup G) V) * ⟨m', hm_stab'⟩ = 1 := by
        apply Subtype.ext
        show m' * m' = 1
        rw [← pow_two]; exact hm2'
      rw [← map_mul, hmul, map_one]
    have hfixI : conjSubgroup I m = I := s16c167_conjSubgroup_inj (by
      rw [← s16c167_conj_conj hm I]
      exact hfixΓ u hu (conjSubgroup I g) ⟨I, hI, rfl⟩)
    have hfixI' : conjSubgroup I m' = I := s16c167_conjSubgroup_inj (by
      rw [← s16c167_conj_conj hm' I]
      exact hfixΓ u' hu' (conjSubgroup I g) ⟨I, hI, rfl⟩)
    have htM : t ∈ Mbar D.M ⊥ V hV := by
      change actTil ⊥ V hV ⟨m, hm_stab⟩ ∈ Mbar D.M ⊥ V hV
      exact actTil_mem_barSub ⊥ V hV hmM hm_stab
    have htM' : t' ∈ Mbar D.M ⊥ V hV := by
      change actTil ⊥ V hV ⟨m', hm_stab'⟩ ∈ Mbar D.M ⊥ V hV
      exact actTil_mem_barSub ⊥ V hV hmM' hm_stab'
    have hxL : (lBar ⊥ V hV L).map (MulAut.conj t).toMonoidHom = lBar ⊥ V hV L := hnorm t htM
    have hyL : (lBar ⊥ V hV L).map (MulAut.conj t').toMonoidHom = lBar ⊥ V hV L :=
      hnorm t' htM'
    have hxE : (imgTil ⊥ V hV I).map t.toMonoidHom = imgTil ⊥ V hV I := by
      change (imgTil ⊥ V hV I).map (actTil ⊥ V hV ⟨m, hm_stab⟩).toMonoidHom = imgTil ⊥ V hV I
      rw [← s16c167_imgTil_conjSubgroup hV hm_stab hm2 I, hfixI]
    have hyE : (imgTil ⊥ V hV I).map t'.toMonoidHom = imgTil ⊥ V hV I := by
      change (imgTil ⊥ V hV I).map (actTil ⊥ V hV ⟨m', hm_stab'⟩).toMonoidHom = imgTil ⊥ V hV I
      rw [← s16c167_imgTil_conjSubgroup hV hm_stab' hm2' I, hfixI']
    have hfixVt : fixV (Subgroup.zpowers t) =
        imgTil ⊥ V hV (V ⊓ centralizer ({m} : Set G)) := by
      change fixV (Subgroup.zpowers (actTil ⊥ V hV ⟨m, hm_stab⟩)) = _
      exact s16c167_fixV_actTil hV hm_stab
    have hfixVt' : fixV (Subgroup.zpowers t') =
        imgTil ⊥ V hV (V ⊓ centralizer ({m'} : Set G)) := by
      change fixV (Subgroup.zpowers (actTil ⊥ V hV ⟨m', hm_stab'⟩)) = _
      exact s16c167_fixV_actTil hV hm_stab'
    have hB_eq : B = conjSubgroup (V ⊓ centralizer ({m} : Set G)) g := by
      rw [E3.conjSubgroup_inf, s16c167_conj_centralizer_singleton hm,
        (htriv_or_axis u hu).resolve_left hnu]
    have hB_eq' : B = conjSubgroup (V ⊓ centralizer ({m'} : Set G)) g := by
      rw [E3.conjSubgroup_inf, s16c167_conj_centralizer_singleton hm',
        (htriv_or_axis u' hu').resolve_left hnu']
    have hBm : V ⊓ centralizer ({m} : Set G) = conjSubgroup B g⁻¹ := by
      rw [← E3.conjSubgroup_conj_inv (V ⊓ centralizer ({m} : Set G)) g, ← hB_eq]
    have hBm' : V ⊓ centralizer ({m'} : Set G) = conjSubgroup B g⁻¹ := by
      rw [← E3.conjSubgroup_conj_inv (V ⊓ centralizer ({m'} : Set G)) g, ← hB_eq']
    have hfixVV : fixV (Subgroup.zpowers t) = fixV (Subgroup.zpowers t') := by
      rw [hfixVt, hfixVt', hBm, hBm']
    have hH : E3.mQuot (imgTil ⊥ V hV I)
        (imgTil ⊥ V hV I ⊓ fixV (Subgroup.zpowers t)) = 1 := by
      have hmqJ : E3.mQuot (conjSubgroup I g) (B ⊓ conjSubgroup I g) =
          E3.mQuot I (I ⊓ centralizer ({m} : Set G)) := by
        rw [hB_eq, ← E3.conjSubgroup_inf, E3.mQuot_conjSubgroup]
        congr 1
        rw [inf_comm (V ⊓ centralizer ({m} : Set G)) I, ← inf_assoc,
          inf_eq_left.2 (hΔ.2.1 I hI)]
      rw [hfixVt, ← s16c167_imgTil_inf_bot hV (U := I)
        (U' := V ⊓ centralizer ({m} : Set G))]
      rw [show I ⊓ (V ⊓ centralizer ({m} : Set G)) = I ⊓ centralizer ({m} : Set G) from by
        rw [← inf_assoc, inf_eq_left.2 (hΔ.2.1 I hI)]]
      rw [s16c167_mQuot_imgTil hV (hΔ.2.1 I hI) inf_le_left]
      rw [← hmqJ]
      exact h18.2.2.2 h2 (conjSubgroup I g) ⟨I, hI, rfl⟩
    have hxH : ∀ e ∈ imgTil ⊥ V hV I ⊓ fixV (Subgroup.zpowers t), t e = e :=
      fun e he => (mem_fixV_zpowers t e).1 he.2
    have hyH : ∀ e ∈ imgTil ⊥ V hV I ⊓ fixV (Subgroup.zpowers t), t' e = e :=
      fun e he => (mem_fixV_zpowers t' e).1 (hfixVV ▸ he.2)
    have hxT : ∀ e ∈ imgTil ⊥ V hV I,
        t e * e⁻¹ ∈ imgTil ⊥ V hV I ⊓ fixV (Subgroup.zpowers t) := by
      intro e he
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact (imgTil ⊥ V hV I).mul_mem (hxE ▸ Subgroup.mem_map_of_mem t.toMonoidHom he)
          ((imgTil ⊥ V hV I).inv_mem he)
      · rw [mem_fixV_zpowers]
        have h1 : t (t e * e⁻¹) = e * (t e)⁻¹ := by
          rw [map_mul, map_inv]
          have h2 : t (t e) = e := by
            rw [← MulAut.mul_apply, ht2, MulAut.one_apply]
          rw [h2]
        rw [h1, hW2inv e, hW2inv (t e), mul_comm]
    have hyT : ∀ e ∈ imgTil ⊥ V hV I,
        t' e * e⁻¹ ∈ imgTil ⊥ V hV I ⊓ fixV (Subgroup.zpowers t) := by
      intro e he
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact (imgTil ⊥ V hV I).mul_mem (hyE ▸ Subgroup.mem_map_of_mem t'.toMonoidHom he)
          ((imgTil ⊥ V hV I).inv_mem he)
      · rw [hfixVV, mem_fixV_zpowers]
        have h1 : t' (t' e * e⁻¹) = e * (t' e)⁻¹ := by
          rw [map_mul, map_inv]
          have h2 : t' (t' e) = e := by
            rw [← MulAut.mul_apply, ht2', MulAut.one_apply]
          rw [h2]
        rw [h1, hW2inv e, hW2inv (t' e), mul_comm]
    rcases hleaf I hI t t' hxL hyL hxE hyE hxH hyH hxT hyT hH with htriv | htriv' | heq
    · exfalso
      have hIle : imgTil ⊥ V hV I ≤ fixV (Subgroup.zpowers t) :=
        fun e he => (mem_fixV_zpowers t e).2 (htriv e he)
      have hIle' : I ≤ V ⊓ centralizer ({m} : Set G) :=
        (s16c167_imgTil_le_iff hV (hΔ.2.1 I hI) inf_le_left).1 (by rwa [hfixVt] at hIle)
      have hJle : conjSubgroup I g ≤ centralizer ({u} : Set G) := by
        rw [← s16c167_conj_centralizer_singleton hm]
        exact E3.conjSubgroup_mono_left g (hIle'.trans inf_le_right)
      have hJleB : conjSubgroup I g ≤ B := by
        rw [← (htriv_or_axis u hu).resolve_left hnu]
        exact le_inf (E3.conjSubgroup_mono_left g (hΔ.2.1 I hI)) hJle
      have hzero : E3.mQuot (conjSubgroup I g) (B ⊓ conjSubgroup I g) = 0 := by
        rw [inf_eq_right.2 hJleB, E3.mQuot_self]
      have hone := h18.2.2.2 h2 (conjSubgroup I g) ⟨I, hI, rfl⟩
      rw [hzero] at hone
      exact absurd hone (by norm_num)
    · exfalso
      have hIle : imgTil ⊥ V hV I ≤ fixV (Subgroup.zpowers t') :=
        fun e he => (mem_fixV_zpowers t' e).2 (htriv' e he)
      have hIle' : I ≤ V ⊓ centralizer ({m'} : Set G) :=
        (s16c167_imgTil_le_iff hV (hΔ.2.1 I hI) inf_le_left).1 (by rwa [hfixVt'] at hIle)
      have hJle : conjSubgroup I g ≤ centralizer ({u'} : Set G) := by
        rw [← s16c167_conj_centralizer_singleton hm']
        exact E3.conjSubgroup_mono_left g (hIle'.trans inf_le_right)
      have hJleB : conjSubgroup I g ≤ B := by
        rw [← (htriv_or_axis u' hu').resolve_left hnu']
        exact le_inf (E3.conjSubgroup_mono_left g (hΔ.2.1 I hI)) hJle
      have hzero : E3.mQuot (conjSubgroup I g) (B ⊓ conjSubgroup I g) = 0 := by
        rw [inf_eq_right.2 hJleB, E3.mQuot_self]
      have hone := h18.2.2.2 h2 (conjSubgroup I g) ⟨I, hI, rfl⟩
      rw [hzero] at hone
      exact absurd hone (by norm_num)
    · have hkey : actTil ⊥ V hV ⟨m, hm_stab⟩ (mkTil ⊥ V hV (IntMod.mk hV ⟨g * j * g⁻¹, hiV⟩)) =
          actTil ⊥ V hV ⟨m', hm_stab'⟩ (mkTil ⊥ V hV (IntMod.mk hV ⟨g * j * g⁻¹, hiV⟩)) := by
        have hmem : mkTil ⊥ V hV (IntMod.mk hV ⟨g * j * g⁻¹, hiV⟩) ∈ imgTil ⊥ V hV I := by
          rw [mem_imgTil]
          exact ⟨IntMod.mk hV ⟨g * j * g⁻¹, hiV⟩, hiI, rfl⟩
        exact heq _ hmem
      rw [actTil_mk, actTil_mk, mkTil_eq_iff, Subgroup.mem_bot] at hkey
      have hval : m * (g * j * g⁻¹) * m⁻¹ = m' * (g * j * g⁻¹) * m'⁻¹ := by
        have h1 : (actStab ⊥ V hV ⟨m, hm_stab⟩ (IntMod.mk hV ⟨g * j * g⁻¹, hiV⟩)).val =
            (actStab ⊥ V hV ⟨m', hm_stab'⟩ (IntMod.mk hV ⟨g * j * g⁻¹, hiV⟩)).val :=
          mul_inv_eq_one.1 hkey
        rwa [actStab_apply_val, actStab_apply_val] at h1
      calc u * j * u⁻¹ = g⁻¹ * (m * (g * j * g⁻¹) * m⁻¹) * g := by rw [hm]; group
        _ = g⁻¹ * (m' * (g * j * g⁻¹) * m'⁻¹) * g := by rw [hval]
        _ = u' * j * u'⁻¹ := by rw [hm']; group
  set C : Subgroup G := U ⊓ centralizer (conjSubgroup V g : Set G) with hCdef
  have hU2 : IsPGroup 2 U := B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hUV hV)
  have hJ₀mem : conjSubgroup a₀ g ∈ deltaConj Δ g := ⟨a₀, by
    rw [hΔab₀]; exact Set.mem_insert_iff.2 (Or.inl rfl), rfl⟩
  have hΓ : deltaConj Δ g = {conjSubgroup a₀ g, conjSubgroup b₀ g} := by
    rw [hΔab₀]
    unfold deltaConj
    rw [Set.image_pair]
  have hsupJ₀ : conjSubgroup a₀ g ⊔ conjSubgroup b₀ g = conjSubgroup V g := by
    have hab : a₀ ⊔ b₀ = V := by
      have h := hΔ.2.2.2.1
      rw [hΔab₀, sSup_pair] at h
      exact h
    unfold conjSubgroup
    rw [← Subgroup.map_sup, hab]
  have hrel : C.relIndex U ≤ 2 := by
    by_cases hCU : C = U
    · rw [hCU, Subgroup.relIndex_self]
      norm_num
    · have hex : ∃ a ∈ U, a ∉ C := by
        by_contra h
        apply hCU
        refine le_antisymm inf_le_left fun x hx => ?_
        by_contra hxC
        exact h ⟨x, hx, hxC⟩
      obtain ⟨a, haU, haC⟩ := hex
      have htwo : C.relIndex U = 2 := by
        rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
        refine ⟨a, haU, haC, fun b hb => ?_⟩
        by_cases hbC : b ∈ C
        · exact Or.inr hbC
        · refine Or.inl ?_
          have hbne : ¬ conjSubgroup V g ≤ centralizer ({b} : Set G) := by
            intro hle
            exact hbC (Subgroup.mem_inf.2 ⟨hb, Subgroup.mem_centralizer_iff.2 fun v hv =>
              Subgroup.mem_centralizer_singleton_iff.1 (hle hv)⟩)
          have hane : ¬ conjSubgroup V g ≤ centralizer ({a} : Set G) := by
            intro hle
            exact haC (Subgroup.mem_inf.2 ⟨haU, Subgroup.mem_centralizer_iff.2 fun v hv =>
              Subgroup.mem_centralizer_singleton_iff.1 (hle hv)⟩)
          have hact' : ∀ j ∈ conjSubgroup a₀ g,
              b * j * b⁻¹ = a * j * a⁻¹ := hact b hb a haU hbne hane (conjSubgroup a₀ g) hJ₀mem
          have hwfixJ₀ : conjSubgroup a₀ g ≤ centralizer ({b * a} : Set G) := by
            intro j hj
            rw [Subgroup.mem_centralizer_singleton_iff]
            have h1 := hact' j hj
            have h2 : (b * a) * j * (b * a)⁻¹ = j := by
              calc (b * a) * j * (b * a)⁻¹ = b * (a * j * a⁻¹) * b⁻¹ := by group
                _ = b * (b * j * b⁻¹) * b⁻¹ := by rw [h1]
                _ = j := by
                  have hb2 : b * b = 1 := by
                    rw [← pow_two]
                    exact hV.2 b (hUV hb)
                  have hbinv : b⁻¹ * b⁻¹ = 1 := by
                    rw [← mul_inv_rev b b, hb2, inv_one]
                  calc b * (b * j * b⁻¹) * b⁻¹ = (b * b) * j * (b⁻¹ * b⁻¹) := by group
                    _ = j := by rw [hb2, hbinv]; group
            have h3 : (b * a) * j = j * (b * a) := by
              calc (b * a) * j = ((b * a) * j * (b * a)⁻¹) * (b * a) := by group
                _ = j * (b * a) := by rw [h2]
            exact h3.symm
          have hwfixΓ : ∀ J' ∈ deltaConj Δ g, conjSubgroup J' (b * a) = J' := by
            intro J' hJ'
            rw [← conjSubgroup_conjSubgroup J' b a, hfixΓ b hb J' hJ', hfixΓ a haU J' hJ']
          have hwVM : b * a ∈ V ⊓ conjSubgroup D.M g :=
            ⟨V.mul_mem (hUV hb) (hUV haU), (conjSubgroup D.M g).mul_mem (hUM hb) (hUM haU)⟩
          obtain ⟨x, hxΓ, hxne, hxeq⟩ := s16c167_twenty_two_x D hC hΔ hS (conjSubgroup a₀ g) hJ₀mem
          have hxle : conjSubgroup (conjSubgroup a₀ g) x ≤ centralizer ({b * a} : Set G) := by
            have h1 := hxeq (b * a) hwVM hwfixΓ
            rw [inf_eq_left.2 hwfixJ₀] at h1
            exact inf_eq_left.1 h1.symm
          have hxJ₁ : conjSubgroup (conjSubgroup a₀ g) x = conjSubgroup b₀ g := by
            have hmem := hxΓ
            rw [hΓ] at hmem
            rcases Set.mem_insert_iff.1 hmem with h | h
            · exact absurd h hxne
            · exact Set.mem_singleton_iff.1 h
          have hVgC : conjSubgroup V g ≤ centralizer ({b * a} : Set G) := by
            rw [← hsupJ₀, ← hxJ₁]
            exact sup_le hwfixJ₀ hxle
          refine Subgroup.mem_inf.2 ⟨U.mul_mem hb haU, ?_⟩
          exact Subgroup.mem_centralizer_iff.2 fun v hv =>
            Subgroup.mem_centralizer_singleton_iff.1 (hVgC hv)
      omega
  have hmqC : E3.mQuot U C ≤ 1 := by
    have h := E3.relIndex_eq_two_pow hU2 C
    have hle : 2 ^ E3.mQuot U C ≤ 2 ^ 1 := by rw [← h]; simpa using hrel
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  refine (E3.mQuot_mono ?_).trans hmqC
  rw [hCdef]
  exact le_inf (inf_le_left.trans hUV) (inf_le_right.trans (Subgroup.centralizer_le hAg))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
