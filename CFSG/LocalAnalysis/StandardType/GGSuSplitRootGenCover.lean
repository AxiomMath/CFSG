module

public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenKGDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase

public section

namespace CFSG.StandardType.SuSplitRootGen

open CFSG.Assembly TableB Multiplicative

variable {p s : ℕ} {H L' : Type} [Group H] [Group L']

private theorem mem_center_of_conj_eq_one {G : Type} [Group G] {x : G}
    (h : MulAut.conj x = 1) : x ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : MulAut.conj x y = y := by rw [h]; rfl
  rw [MulAut.conj_apply] at h1
  calc y * x = x * y * x⁻¹ * x := by rw [h1]
    _ = x * y := by group

private theorem torus_pow_p (τ : Multiplicative (Fin s → ZMod p) →* H)
    (t : Fin s → ZMod p) : τ (ofAdd t) ^ p = 1 := by
  rw [← map_pow, ← ofAdd_nsmul]
  have hp : p • t = 0 := by
    funext i
    show p • t i = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [hp, ofAdd_zero, map_one]

private theorem torus_pow_p' (τ : Multiplicative (Fin s → ZMod p) →* H)
    (u : Multiplicative (Fin s → ZMod p)) : τ u ^ p = 1 := by
  rw [← ofAdd_toAdd u]
  exact torus_pow_p τ (toAdd u)

private theorem injective_conj_torus {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H}
    (hτc : ∀ t, φ (τ t) ∈ Subgroup.center L' → t = 1) :
    Function.Injective fun t : Multiplicative (Fin s → ZMod p) =>
      MulAut.conj (φ (τ t)) := by
  intro t u h
  have h' : MulAut.conj (φ (τ t)) = MulAut.conj (φ (τ u)) := h
  have h1 : MulAut.conj (φ (τ (t * u⁻¹))) = 1 := by
    rw [map_mul τ t u⁻¹, map_inv τ u, map_mul φ, map_inv φ, map_mul (MulAut.conj),
      map_inv (MulAut.conj), h', mul_inv_cancel]
  exact mul_inv_eq_one.mp (hτc _ (mem_center_of_conj_eq_one h1))

private noncomputable def coverTorusEquiv {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H} {A : Subgroup (MulAut L')}
    (hM : IsCoverTorusModel φ τ A)
    (hτc : ∀ t, φ (τ t) ∈ Subgroup.center L' → t = 1) :
    Multiplicative (Fin s → ZMod p) ≃* A where
  toFun t := ⟨MulAut.conj (φ (τ t)), (hM _).mpr ⟨t, rfl⟩⟩
  invFun a := Classical.choose ((hM (a : MulAut L')).mp a.2)
  left_inv t := by
    have h := Classical.choose_spec ((hM (MulAut.conj (φ (τ t)))).mp
      ((hM _).mpr ⟨t, rfl⟩))
    exact (injective_conj_torus hτc h).symm
  right_inv a := by
    apply Subtype.ext
    exact (Classical.choose_spec ((hM (a : MulAut L')).mp a.2)).symm
  map_mul' t u := by
    apply Subtype.ext
    change MulAut.conj (φ (τ (t * u))) =
      MulAut.conj (φ (τ t)) * MulAut.conj (φ (τ u))
    rw [map_mul τ t u, map_mul φ, map_mul (MulAut.conj)]

private theorem coe_coverTorusEquiv {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H} {A : Subgroup (MulAut L')}
    (hM : IsCoverTorusModel φ τ A)
    (hτc : ∀ t, φ (τ t) ∈ Subgroup.center L' → t = 1)
    (t : Multiplicative (Fin s → ZMod p)) :
    ((coverTorusEquiv hM hτc t : A) : MulAut L') = MulAut.conj (φ (τ t)) :=
  rfl

theorem card_eq_of_isCoverTorusModel {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H} {A : Subgroup (MulAut L')}
    (hM : IsCoverTorusModel φ τ A) (hτc : ∀ t, φ (τ t) ∈ Subgroup.center L' → t = 1) :
    Nat.card A = p ^ s := by
  rw [← Nat.card_congr (coverTorusEquiv hM hτc).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem conj_torus_eq {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H} {w : H}
    {f : (Fin s → ZMod p) → Fin s → ZMod p}
    (hw : ∀ t, w * τ (ofAdd t) * w⁻¹ = τ (ofAdd (f t))) (t : Fin s → ZMod p) :
    MulAut.conj (φ w) * MulAut.conj (φ (τ (ofAdd t))) * (MulAut.conj (φ w))⁻¹ =
      MulAut.conj (φ (τ (ofAdd (f t)))) := by
  rw [← map_inv (MulAut.conj), ← map_mul (MulAut.conj), ← map_mul (MulAut.conj)]
  congr 1
  rw [← map_mul φ, ← map_inv φ, ← map_mul φ, hw t]

private theorem conj_inv_torus_eq {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H} {w : H}
    {f : (Fin s → ZMod p) → Fin s → ZMod p}
    (hw : ∀ t, w * τ (ofAdd t) * w⁻¹ = τ (ofAdd (f t))) (t : Fin s → ZMod p) :
    (MulAut.conj (φ w))⁻¹ * MulAut.conj (φ (τ (ofAdd (f t)))) * MulAut.conj (φ w) =
      MulAut.conj (φ (τ (ofAdd t))) := by
  rw [← map_inv (MulAut.conj), ← map_mul (MulAut.conj), ← map_mul (MulAut.conj)]
  congr 1
  rw [← map_inv φ, ← map_mul φ, ← map_mul φ]
  congr 1
  rw [← hw t]
  group

private theorem conj_mem_normalizer_of_torus_conj {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H} {A : Subgroup (MulAut L')}
    (hM : IsCoverTorusModel φ τ A) {w : H}
    {f : (Fin s → ZMod p) → Fin s → ZMod p}
    (hw : ∀ t, w * τ (ofAdd t) * w⁻¹ = τ (ofAdd (f t)))
    (hf2 : ∀ t, f (f t) = t) :
    MulAut.conj (φ w) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro b
  constructor
  · intro hb
    obtain ⟨t, rfl⟩ := (hM b).mp hb
    exact (hM _).mpr ⟨f t, conj_torus_eq hw t⟩
  · intro hb
    obtain ⟨t, ht⟩ := (hM (MulAut.conj (φ w) * b *
      (MulAut.conj (φ w))⁻¹)).mp hb
    refine (hM _).mpr ⟨f t, ?_⟩
    calc b = (MulAut.conj (φ w))⁻¹ * (MulAut.conj (φ w) * b *
          (MulAut.conj (φ w))⁻¹) * MulAut.conj (φ w) := by group
      _ = (MulAut.conj (φ w))⁻¹ * MulAut.conj (φ (τ (ofAdd t))) *
            MulAut.conj (φ w) := by rw [ht]; rfl
      _ = MulAut.conj (φ (τ (ofAdd (f t)))) := by
            simpa [hf2 t] using conj_inv_torus_eq hw (f t)

private theorem ggTorusWeylElt_of_torus_conj {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H} {A : Subgroup (MulAut L')}
    (hM : IsCoverTorusModel φ τ A) {w : H}
    {f : (Fin s → ZMod p) → Fin s → ZMod p}
    (hw : ∀ t, w * τ (ofAdd t) * w⁻¹ = τ (ofAdd (f t))) :
    GGTorusWeylElt p A (φ w) := by
  intro a ha
  obtain ⟨t, rfl⟩ := (hM a).mp ha
  set u := toAdd t with hu
  have ht : t = ofAdd u := by rw [hu, ofAdd_toAdd]
  rw [ht]
  set c : L' := φ (τ (ofAdd (f u))) * (φ (τ (ofAdd u)))⁻¹ with hc
  have hkey : φ w * (MulAut.conj (φ (τ (ofAdd u))) (φ w))⁻¹ = c := by
    rw [hc, MulAut.conj_apply]
    calc φ w * (φ (τ (ofAdd u)) * φ w * (φ (τ (ofAdd u)))⁻¹)⁻¹
        = φ w * φ (τ (ofAdd u)) * (φ w)⁻¹ * (φ (τ (ofAdd u)))⁻¹ := by group
      _ = φ (w * τ (ofAdd u) * w⁻¹) * (φ (τ (ofAdd u)))⁻¹ := by
            simp only [← map_mul, ← map_inv]
      _ = φ (τ (ofAdd (f u))) * (φ (τ (ofAdd u)))⁻¹ := by rw [hw u]
  refine ⟨?_, ?_⟩
  · rw [hkey, hc]
    have harg : (τ (ofAdd (f u)) * (τ (ofAdd u))⁻¹) ^ p = 1 := by
      rw [← map_inv τ (ofAdd u), ← map_mul τ (ofAdd (f u)) (ofAdd u)⁻¹]
      exact torus_pow_p' τ _
    rw [← map_inv φ, ← map_mul φ, ← map_pow, harg, map_one]
  · intro a' ha'
    obtain ⟨v, rfl⟩ := (hM a').mp ha'
    set z := toAdd v with hz
    have hv : v = ofAdd z := by rw [hz, ofAdd_toAdd]
    rw [hv, hkey, hc]
    have hcomm : ∀ x : Fin s → ZMod p,
        MulAut.conj (φ (τ (ofAdd z))) (φ (τ (ofAdd x))) = φ (τ (ofAdd x)) := by
      intro x
      rw [MulAut.conj_apply]
      have hc' : φ (τ (ofAdd z)) * φ (τ (ofAdd x)) =
          φ (τ (ofAdd x)) * φ (τ (ofAdd z)) := by
        simp only [← map_mul]
        change φ (τ (ofAdd (z + x))) = φ (τ (ofAdd (x + z)))
        rw [add_comm]
      rw [hc', mul_assoc, mul_inv_cancel, mul_one]
    rw [map_mul, map_inv, hcomm (f u), hcomm u]

private theorem ggConjAut_coverTorusEquiv {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H} {A : Subgroup (MulAut L')}
    (hM : IsCoverTorusModel φ τ A)
    (hτc : ∀ t, φ (τ t) ∈ Subgroup.center L' → t = 1)
    {w : H} {f : (Fin s → ZMod p) → Fin s → ZMod p}
    (hw : ∀ t, w * τ (ofAdd t) * w⁻¹ = τ (ofAdd (f t)))
    (hn : MulAut.conj (φ w) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (t : Fin s → ZMod p) :
    ggConjAut A hn (coverTorusEquiv hM hτc (ofAdd t)) =
      coverTorusEquiv hM hτc (ofAdd (f t)) := by
  refine Subtype.ext ?_
  rw [ggConjAut_apply, coe_coverTorusEquiv, coe_coverTorusEquiv]
  exact conj_torus_eq hw t

private theorem commute_conj_iff_of_torus_conj {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H} {w : H}
    {f : (Fin s → ZMod p) → Fin s → ZMod p}
    (hτc : ∀ t, φ (τ t) ∈ Subgroup.center L' → t = 1)
    (hw : ∀ t, w * τ (ofAdd t) * w⁻¹ = τ (ofAdd (f t)))
    (t : Fin s → ZMod p) :
    MulAut.conj (φ w) * MulAut.conj (φ (τ (ofAdd t))) =
        MulAut.conj (φ (τ (ofAdd t))) * MulAut.conj (φ w) ↔ f t = t := by
  have hAB : MulAut.conj (φ w) * MulAut.conj (φ (τ (ofAdd t))) =
      MulAut.conj (φ (τ (ofAdd (f t)))) * MulAut.conj (φ w) := by
    rw [← map_mul, ← map_mul]
    congr 1
    rw [← map_mul, ← map_mul, ← hw t]
    group
  constructor
  · intro h
    have h' : MulAut.conj (φ (τ (ofAdd (f t)))) * MulAut.conj (φ w) =
        MulAut.conj (φ (τ (ofAdd t))) * MulAut.conj (φ w) := by
      rw [← hAB]
      exact h
    exact ofAdd.injective (injective_conj_torus hτc (mul_right_cancel h'))
  · intro h
    rw [hAB, h]

private theorem isReflection_of_torus_conj {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H} {A : Subgroup (MulAut L')}
    (hM : IsCoverTorusModel φ τ A)
    (hτc : ∀ t, φ (τ t) ∈ Subgroup.center L' → t = 1)
    {w : H} {f : (Fin s → ZMod p) → Fin s → ZMod p}
    (hw : ∀ t, w * τ (ofAdd t) * w⁻¹ = τ (ofAdd (f t)))
    (hn : MulAut.conj (φ w) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hf2 : ∀ t, f (f t) = t) (hfix : Nat.card {t // f t = t} * p = p ^ s) :
    GGIsReflection p (ggConjAut A hn) := by
  let e := coverTorusEquiv hM hτc
  have he : ∀ t : Fin s → ZMod p, ggConjAut A hn (e (ofAdd t)) = e (ofAdd (f t)) :=
    fun t => ggConjAut_coverTorusEquiv hM hτc hw hn t
  constructor
  · refine MulEquiv.ext fun b => ?_
    obtain ⟨t, rfl⟩ := e.surjective b
    obtain ⟨u, hu⟩ : ∃ u, t = ofAdd u := ⟨toAdd t, (ofAdd_toAdd t).symm⟩
    rw [hu, pow_two, MulAut.mul_apply, he u, he (f u), hf2 u]
    rfl
  · have hiff : ∀ u : Multiplicative (Fin s → ZMod p),
        ggConjAut A hn (e u) = e u ↔ f (toAdd u) = toAdd u := by
      intro u
      have hu : u = ofAdd (toAdd u) := (ofAdd_toAdd u).symm
      conv_lhs => rw [hu]
      rw [he (toAdd u)]
      constructor
      · intro h
        exact ofAdd.injective (e.injective h)
      · intro h
        rw [h]
    have hcard : Nat.card {b : ↥A // ggConjAut A hn b = b} =
        Nat.card {t : Fin s → ZMod p // f t = t} := by
      have hsub : {u : Multiplicative (Fin s → ZMod p) //
          ggConjAut A hn (e u) = e u} ≃ {b : ↥A // ggConjAut A hn b = b} :=
        Equiv.subtypeEquiv e.toEquiv (fun _ => Iff.rfl)
      have hofAdd : {t : Fin s → ZMod p // f t = t} ≃
          {u : Multiplicative (Fin s → ZMod p) // f (toAdd u) = toAdd u} :=
        Equiv.subtypeEquiv Multiplicative.ofAdd (fun t => by rw [toAdd_ofAdd])
      rw [← Nat.card_congr hsub, Nat.card_congr (Equiv.subtypeEquivRight hiff),
        ← Nat.card_congr hofAdd]
    rw [hcard]
    exact hfix.trans (card_eq_of_isCoverTorusModel hM hτc).symm

private theorem eq_of_ggConjAut_cover_eq {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H} {A : Subgroup (MulAut L')}
    (hM : IsCoverTorusModel φ τ A)
    (hτc : ∀ t, φ (τ t) ∈ Subgroup.center L' → t = 1)
    {w₁ w₂ : H} {f₁ f₂ : (Fin s → ZMod p) → Fin s → ZMod p}
    (hw₁ : ∀ t, w₁ * τ (ofAdd t) * w₁⁻¹ = τ (ofAdd (f₁ t)))
    (hw₂ : ∀ t, w₂ * τ (ofAdd t) * w₂⁻¹ = τ (ofAdd (f₂ t)))
    (hn₁ : MulAut.conj (φ w₁) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hn₂ : MulAut.conj (φ w₂) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (h : ggConjAut A hn₁ = ggConjAut A hn₂) : f₁ = f₂ := by
  funext t
  let e := coverTorusEquiv hM hτc
  have h1 := ggConjAut_coverTorusEquiv hM hτc hw₁ hn₁ t
  have h2 := ggConjAut_coverTorusEquiv hM hτc hw₂ hn₂ t
  have h3 : e (ofAdd (f₁ t)) = e (ofAdd (f₂ t)) := by
    rw [← h1, ← h2, h]
  exact ofAdd.injective (e.injective h3)

private theorem ggHypCent_cover_eq {φ : H →* L'}
    {τ : Multiplicative (Fin s → ZMod p) →* H} {A : Subgroup (MulAut L')}
    (hφs : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center H)
    (hkerp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1)
    (hM : IsCoverTorusModel φ τ A)
    (hτc : ∀ t, φ (τ t) ∈ Subgroup.center L' → t = 1)
    {w : H} {f : (Fin s → ZMod p) → Fin s → ZMod p}
    (hw : ∀ t, w * τ (ofAdd t) * w⁻¹ = τ (ofAdd (f t))) :
    ggHypCent A (φ w) = (Subgroup.centralizer (torusFix τ f)).map φ := by
  apply le_antisymm
  · intro l hl
    obtain ⟨g, rfl⟩ := hφs l
    rw [Subgroup.mem_map]
    refine ⟨g, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hu' : u = ofAdd (toAdd u) := (ofAdd_toAdd u).symm
    rw [hu']
    set t := toAdd u with ht
    have hfix : f t = t := hu
    have hmemA : MulAut.conj (φ (τ (ofAdd t))) ∈ A := (hM _).mpr ⟨ofAdd t, rfl⟩
    have hcomm' : MulAut.conj (φ w) * MulAut.conj (φ (τ (ofAdd t))) =
        MulAut.conj (φ (τ (ofAdd t))) * MulAut.conj (φ w) :=
      (commute_conj_iff_of_torus_conj hτc hw t).mpr hfix
    have hlfix : MulAut.conj (φ (τ (ofAdd t))) (φ g) = φ g := by
      have h1 : (φ g : L') ∈ ggFix (MulAut.conj (φ (τ (ofAdd t)))) :=
        (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hl
          (MulAut.conj (φ (τ (ofAdd t)))))) ⟨hmemA, hcomm'⟩
      exact mem_ggFix.mp h1
    set z : H := g * τ (ofAdd t) * g⁻¹ * (τ (ofAdd t))⁻¹ with hz
    have hzker : z ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hz]
      have h2 : φ (τ (ofAdd t)) * φ g = φ g * φ (τ (ofAdd t)) := by
        have h3 := congrArg (fun y => y * φ (τ (ofAdd t))) hlfix
        rw [MulAut.conj_apply] at h3
        calc φ (τ (ofAdd t)) * φ g = (φ (τ (ofAdd t)) * φ g *
              (φ (τ (ofAdd t)))⁻¹) * φ (τ (ofAdd t)) := by group
          _ = φ g * φ (τ (ofAdd t)) := by rw [h3]
      simp only [map_mul, map_inv]
      rw [← h2]
      group
    have hzcent : z ∈ Subgroup.center H := hker hzker
    have hzcomm : Commute z (τ (ofAdd t)) :=
      (Subgroup.mem_center_iff.mp hzcent (τ (ofAdd t))).symm
    have hconj : g * τ (ofAdd t) * g⁻¹ = z * τ (ofAdd t) := by
      rw [hz]; group
    have hxp : τ (ofAdd t) ^ p = 1 := torus_pow_p τ t
    have h1 : (z * τ (ofAdd t)) ^ p = 1 := by
      rw [← hconj,
        show g * τ (ofAdd t) * g⁻¹ = MulAut.conj g (τ (ofAdd t)) from rfl,
        ← map_pow, hxp, map_one]
    have hzp : z ^ p = 1 := by
      have h3 : z ^ p * (τ (ofAdd t)) ^ p = 1 := by
        rw [← hzcomm.mul_pow, h1]
      rwa [hxp, mul_one] at h3
    have hz1 : z = 1 := hkerp z hzker hzp
    rw [hz1, one_mul] at hconj
    calc τ (ofAdd t) * g = (g * τ (ofAdd t) * g⁻¹) * g := by rw [hconj]
      _ = g * τ (ofAdd t) := by group
  · intro l hl
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hl
    change (φ g) ∈ ⨅ (a : MulAut L') (_ : a ∈ A ∧
      MulAut.conj (φ w) * a = a * MulAut.conj (φ w)), ggFix a
    rw [Subgroup.mem_iInf]
    intro a
    rw [Subgroup.mem_iInf]
    intro ha
    rw [mem_ggFix]
    obtain ⟨t, rfl⟩ := (hM a).mp ha.1
    have ht : t = ofAdd (toAdd t) := (ofAdd_toAdd t).symm
    rw [ht] at ha ⊢
    have hft : f (toAdd t) = toAdd t :=
      (commute_conj_iff_of_torus_conj hτc hw (toAdd t)).mp ha.2
    have hmem : τ (ofAdd (toAdd t)) ∈ torusFix τ f := by
      refine ⟨ofAdd (toAdd t), ?_, rfl⟩
      simpa using hft
    have hg' : τ (ofAdd (toAdd t)) * g = g * τ (ofAdd (toAdd t)) :=
      (Subgroup.mem_centralizer_iff.mp hg) _ hmem
    rw [MulAut.conj_apply]
    have hφcomm : φ (τ (ofAdd (toAdd t))) * φ g =
        φ g * φ (τ (ofAdd (toAdd t))) := by
      rw [← map_mul, ← map_mul, hg']
    rw [hφcomm, mul_assoc, mul_inv_cancel, mul_one]

private theorem orderOf_map_eq_of_ker {G K : Type} [Group G] [Group K] (hp : p.Prime)
    (ψ : G →* K) (hψp : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1) {x : G}
    (hx : orderOf x = p) : orderOf (ψ x) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hdvd : orderOf (ψ x) ∣ p := by
    rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, hxp, map_one]
  have hne : orderOf (ψ x) ≠ 1 := by
    intro h
    have h1 : ψ x = 1 := orderOf_eq_one_iff.mp h
    have h2 : x ∈ ψ.ker := MonoidHom.mem_ker.mpr h1
    have h3 : x = 1 := hψp x h2 hxp
    rw [h3, orderOf_one] at hx
    exact hp.ne_one hx.symm
  rcases hp.eq_one_or_self_of_dvd (orderOf (ψ x)) hdvd with h | h
  · exact absurd h hne
  · exact h

private theorem dvd_card_map_of_dvd [Finite H] {φ : H →* L'} (hp : p.Prime)
    (hkerp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1) {S : Subgroup H}
    (hdvd : p ∣ Nat.card S) : p ∣ Nat.card (S.map φ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite S := Finite.of_injective (fun x : S => (x : H)) Subtype.val_injective
  haveI : Fintype S := Fintype.ofFinite S
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p (by simpa using hdvd)
  have hxH : orderOf (x : H) = p := by
    rw [Subgroup.orderOf_coe]
    exact hx
  have hφx : orderOf (φ (x : H)) = p := orderOf_map_eq_of_ker hp φ hkerp hxH
  have hmem : φ (x : H) ∈ S.map φ := Subgroup.mem_map_of_mem φ x.2
  rw [← hφx]
  exact Subgroup.orderOf_dvd_natCard (S.map φ) hmem

theorem ggTorusRootGenAvoid_of_cover (hp : p.Prime) [Finite H] {φ : H →* L'}
    (hφs : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center H)
    (hkerp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1)
    {τ : Multiplicative (Fin s → ZMod p) →* H} {A : Subgroup (MulAut L')}
    (hM : IsCoverTorusModel φ τ A) (hτc : ∀ t, φ (τ t) ∈ Subgroup.center L' → t = 1)
    {ι : Type} [Nonempty ι] (w : ι → H) (f : ι → (Fin s → ZMod p) → Fin s → ZMod p)
    (S : ι → Subgroup H)
    (hw : ∀ i t, w i * τ (ofAdd t) * (w i)⁻¹ = τ (ofAdd (f i t)))
    (hinv : ∀ i t, f i (f i t) = t)
    (hfix : ∀ i, Nat.card {t // f i t = t} * p = p ^ s)
    (hwS : ∀ i, w i ∈ S i)
    (hcomp : ∀ i, IsComponentOf (S i) (Subgroup.centralizer (torusFix τ (f i))))
    (hdvd : ∀ i, p ∣ Nat.card (S i))
    (hgen : ∀ j, (⨆ (i : ι) (_ : f i ≠ f j), S i) = ⊤) :
    GGTorusRootGenAvoid p A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro ρ
  let n : ι → L' := fun i => φ (w i)
  have hn : ∀ i, MulAut.conj (n i) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun i => conj_mem_normalizer_of_torus_conj hM (hw i) (hinv i)
  have hW : ∀ i, GGTorusWeylElt p A (n i) :=
    fun i => ggTorusWeylElt_of_torus_conj hM (hw i)
  have hR : ∀ i, GGIsReflection p (ggConjAut A (hn i)) :=
    fun i => isReflection_of_torus_conj hM hτc (hw i) (hn i) (hinv i) (hfix i)
  have hEq : ∀ i j, ggConjAut A (hn i) = ggConjAut A (hn j) → f i = f j :=
    fun i j h => eq_of_ggConjAut_cover_eq hM hτc (hw i) (hw j) (hn i) (hn j) h
  have hcomp' : ∀ i, IsComponentOf ((S i).map φ) (ggHypCent A (n i)) := by
    intro i
    rw [ggHypCent_cover_eq hφs hker hkerp hM hτc (hw i)]
    exact isComponentOf_iff_open.mpr
      (CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map φ
        (fun g hg => hker (MonoidHom.mem_ker.mpr hg))
        (isComponentOf_iff_open.mp (hcomp i)))
  have hdvd' : ∀ i, p ∣ Nat.card ((S i).map φ) :=
    fun i => dvd_card_map_of_dvd hp hkerp (hdvd i)
  have hmem : ∀ i, n i ∈ (S i).map φ :=
    fun i => Subgroup.mem_map_of_mem φ (hwS i)
  have hle : ∀ i, ggConjAut A (hn i) ≠ ρ → (S i).map φ ≤
      (⨆ (m : L') (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')))
        (J : Subgroup L') (_ : GGTorusWeylElt p A m ∧
          GGIsReflection p (ggConjAut A hm) ∧ ggConjAut A hm ≠ ρ ∧ m ∈ J ∧
          IsComponentOf J (ggHypCent A m) ∧ p ∣ Nat.card J), J) := by
    intro i hne
    exact le_iSup_of_le (n i) (le_iSup_of_le (hn i) (le_iSup_of_le ((S i).map φ)
      (le_iSup_of_le ⟨hW i, hR i, hne, hmem i, hcomp' i, hdvd' i⟩ le_rfl)))
  by_cases hρ : ∃ i₀, ggConjAut A (hn i₀) = ρ
  · obtain ⟨i₀, hi₀⟩ := hρ
    apply le_antisymm le_top
    rw [← Subgroup.map_top_of_surjective φ hφs, ← hgen i₀]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun i => iSup_le fun hfi => ?_
    exact hle i fun h => hfi (hEq i i₀ (h.trans hi₀.symm))
  · push Not at hρ
    let j : ι := Classical.arbitrary ι
    apply le_antisymm le_top
    rw [← Subgroup.map_top_of_surjective φ hφs, ← hgen j]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun i => iSup_le fun _ => hle i (hρ i)

end CFSG.StandardType.SuSplitRootGen

end
