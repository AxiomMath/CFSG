module

public import CFSG.Quasithin.Background.HA7Pair
public import CFSG.Quasithin.Background.HSp4Alpha
public import Certificates.Certificate7022

public section

namespace CFSG.Quasithin

namespace H

namespace PairG

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem fst_injective_of_swap {ι K : Type} [Field K] {A : Subgroup (MulAut (PairMod ι K))}
    {y : MulAut (PairMod ι K)} (hyA : y ∈ A) (hyy : y * y = 1)
    (hy2 : (V₁ ι K).map y.toMonoidHom = V₂ ι K) {v w : ↥(fixV A)}
    (h1 : (v : PairMod ι K).1 = (w : PairMod ι K).1) : v = w := by
  set z := (v : PairMod ι K) * (w : PairMod ι K)⁻¹ with hz
  have hzV : z ∈ V₂ ι K := by
    rw [mem_V₂]
    change (v : PairMod ι K).1 * ((w : PairMod ι K).1)⁻¹ = 1
    rw [h1, mul_inv_cancel]
  have hzy : y z = z := by
    rw [hz, map_mul, map_inv, v.2 y hyA, w.2 y hyA]
  have hz1 : z = 1 := by
    obtain ⟨u, hu, hyu⟩ : z ∈ (V₁ ι K).map y.toMonoidHom := by
      rw [hy2]
      exact hzV
    have hyy' : y (y u) = u := by
      change (y * y) u = u
      rw [hyy]
      rfl
    have hzu : z = u := by
      have h2 : y z = u := by rw [← hyu]; exact hyy'
      rw [← h2, hzy]
    exact eq_one_of_fix_of_map_V₂ hy2 (hzu ▸ hu) hzy
  exact Subtype.ext (by rw [← mul_inv_eq_one, ← hz, hz1])

end PairG

namespace A7

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix Equiv PairG
open scoped Matrix

variable (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))

theorem card_stdMod_four : Nat.card (StdMod (Fin 4) (ZMod 2)) = 16 := by
  rw [card_stdMod, Nat.card_zmod, Fintype.card_fin]
  rfl

theorem card_pairMod_four : Nat.card (PairMod (Fin 4) (ZMod 2)) = 2 ^ 8 := by
  rw [Nat.card_prod, card_stdMod_four]
  rfl

theorem isPGroup_of_equiv {V : Type*} [CommGroup V] (e : V ≃* PairMod (Fin 4) (ZMod 2)) :
    IsPGroup 2 V :=
  IsPGroup.of_card ((Nat.card_congr e.toEquiv).trans card_pairMod_four)

theorem card_fix_natAut_le {γ : Γ α} (h2 : γ * γ = 1) (h1 : γ ≠ 1) :
    Nat.card {v : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) γ v = v} ≤ 4 := by
  have e : Nat.card {v : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) γ v = v} =
      Nat.card {v : Fin 4 → ZMod 2 //
        ((γ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v} :=
    Nat.card_congr
      { toFun := fun v => ⟨Multiplicative.toAdd v.1, congrArg Multiplicative.toAdd v.2⟩
        invFun := fun v => ⟨Multiplicative.ofAdd v.1, congrArg Multiplicative.ofAdd v.2⟩
        left_inv := fun v => rfl
        right_inv := fun v => rfl }
  rw [e, Nat.card_eq_fintype_card]
  exact card_fix_le_four α h2 h1

theorem pairHom_injective : Function.Injective (pairHom (Γ α) (θ α).toMonoidHom) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  rw [pairHom_apply] at hγ
  have h := (pairAut_injective (hγ.trans pairAut_one.symm)).1
  exact natAut_injective (Γ α) (by rw [h, map_one])

theorem card_le_four_of_le {A : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))}
    (hA : A ≤ pairA7 α) (hsq : ∀ x ∈ A, x * x = 1) : Nat.card A ≤ 4 := by
  set E := A.comap (pairHom (Γ α) (θ α).toMonoidHom) with hE
  have hcard : Nat.card E = Nat.card A := by
    have hmap : E.map (pairHom (Γ α) (θ α).toMonoidHom) = A := Subgroup.map_comap_eq_self hA
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective (pairHom_injective α)).symm
  have hcard' : Nat.card (E.map (Γ α).subtype) = Nat.card E :=
    Subgroup.card_map_of_injective (Γ α).subtype_injective
  rw [← hcard, ← hcard']
  refine card_le_four α (Subgroup.map_subtype_le E) ?_
  rintro _ ⟨γ, hγ, rfl⟩
  have h1 : pairHom (Γ α) (θ α).toMonoidHom (γ * γ) = 1 := by
    rw [map_mul]
    exact hsq _ hγ
  have h2 : γ * γ = 1 := pairHom_injective α (h1.trans (map_one _).symm)
  rw [← map_mul, h2, map_one]

theorem card_mul_le_of_le
    {A : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))}
    (hA : A ≤ pairA7 α) (hsq : ∀ x ∈ A, x * x = 1) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card ↥(fixV A) ≤ 2 ^ 6 := by
  obtain ⟨t, htA, ht1⟩ : ∃ t ∈ A, t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hA1 ((Subgroup.eq_bot_iff_forall _).mpr hcon)
  obtain ⟨γ, rfl⟩ := hA htA
  have hγ1 : γ ≠ 1 := fun h => ht1 (by rw [h, map_one])
  have hγ2 : γ * γ = 1 := pairHom_injective α (by rw [map_mul, hsq _ htA, map_one])
  have hθ2 : θ α γ * θ α γ = 1 := by rw [← map_mul, hγ2, map_one]
  have hθ1 : θ α γ ≠ 1 := fun h => hγ1 ((θ α).injective (by rw [h, map_one]))
  have hfix : Nat.card ↥(fixV A) ≤ 4 * 4 := by
    calc Nat.card ↥(fixV A) ≤ Nat.card {x : PairMod (Fin 4) (ZMod 2) //
          pairAut (natAut (Γ α) γ) (natAut (Γ α) (θ α γ)) x = x} :=
          Nat.card_le_card_of_injective (fun v => ⟨v, v.2 _ htA⟩)
            fun v w h => Subtype.ext (congrArg Subtype.val h :)
      _ = Nat.card {v : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) γ v = v} *
          Nat.card {w : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) (θ α γ) w = w} :=
          card_fix_pairAut _ _
      _ ≤ 4 * 4 := Nat.mul_le_mul (card_fix_natAut_le α hγ2 hγ1) (card_fix_natAut_le α hθ2 hθ1)
  calc Nat.card A * Nat.card ↥(fixV A) ≤ 4 * (4 * 4) :=
        Nat.mul_le_mul (card_le_four_of_le α hA hsq) hfix
    _ = 2 ^ 6 := by norm_num

theorem card_mul_le_of_swap
    {A : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))}
    (hAN : A ≤ pairNormA7 α) (hsq : ∀ x ∈ A, x * x = 1) {y : MulAut (PairMod (Fin 4) (ZMod 2))}
    (hyA : y ∈ A) (hy : (V₁ (Fin 4) (ZMod 2)).map y.toMonoidHom ≠ V₁ (Fin 4) (ZMod 2)) :
    Nat.card A * Nat.card ↥(fixV A) ≤ 2 ^ 5 := by
  have : Finite (MulAut (PairMod (Fin 4) (ZMod 2))) := MulEquiv.finite_left
  have hor : ∀ x ∈ pairNormA7 α, (V₁ (Fin 4) (ZMod 2)).map x.toMonoidHom = V₁ (Fin 4) (ZMod 2) ∨
      (V₁ (Fin 4) (ZMod 2)).map x.toMonoidHom = V₂ (Fin 4) (ZMod 2) :=
    fun x hx => map_V₁_eq_or (isNatIrr α) (θ_surjective α) (not_isoMod α) hx
  have hy2 := (hor y (hAN hyA)).resolve_left hy
  set A₀ := A ⊓ pairA7 α with hA₀
  have hmem : ∀ x ∈ A, x ∈ pairA7 α ↔
      (V₁ (Fin 4) (ZMod 2)).map x.toMonoidHom = V₁ (Fin 4) (ZMod 2) := by
    intro x hx
    constructor
    · rintro ⟨γ, rfl⟩
      exact map_V₁_pairAut _ _
    · exact mem_pairA7_of_map α (hAN hx)
  have hidx : Nat.card A ≤ 2 * Nat.card A₀ := by
    refine Sp4.card_le_two_mul_of_mul_mem inf_le_left fun x hx z hz hx' hz' =>
      ⟨A.mul_mem hx hz, ?_⟩
    have hx1 : x ∉ pairA7 α := fun h => hx' ⟨hx, h⟩
    have hz1 : z ∉ pairA7 α := fun h => hz' ⟨hz, h⟩
    have hxV := (hor x (hAN hx)).resolve_left fun h => hx1 ((hmem x hx).mpr h)
    have hzV := (hor z (hAN hz)).resolve_left fun h => hz1 ((hmem z hz).mpr h)
    have hxV2 : (V₂ (Fin 4) (ZMod 2)).map x.toMonoidHom = V₁ (Fin 4) (ZMod 2) := by
      rw [← hxV, Subgroup.map_map]
      have : x.toMonoidHom.comp x.toMonoidHom = MonoidHom.id _ := by
        refine MonoidHom.ext fun v => ?_
        change (x * x) v = v
        rw [hsq x hx]
        rfl
      rw [this, Subgroup.map_id]
    refine (hmem _ (A.mul_mem hx hz)).mpr ?_
    have : (x * z).toMonoidHom = x.toMonoidHom.comp z.toMonoidHom := rfl
    rw [this, ← Subgroup.map_map, hzV, hxV2]
  have hA₀4 : Nat.card A₀ ≤ 4 := card_le_four_of_le α inf_le_right fun x hx => hsq x hx.1
  have hinj : ∀ v w : ↥(fixV A), (v : PairMod (Fin 4) (ZMod 2)).1 =
      (w : PairMod (Fin 4) (ZMod 2)).1 → v = w :=
    fun v w h1 => fst_injective_of_swap hyA (hsq y hyA) hy2 h1
  by_cases hE : A₀ = ⊥
  · have hA : Nat.card A ≤ 2 := by
      rw [hE, Subgroup.card_bot] at hidx
      omega
    have hfix : Nat.card ↥(fixV A) ≤ 16 := by
      rw [← card_stdMod_four]
      exact Nat.card_le_card_of_injective (fun v => (v : PairMod (Fin 4) (ZMod 2)).1)
        fun v w h => hinj v w h
    calc Nat.card A * Nat.card ↥(fixV A) ≤ 2 * 16 := Nat.mul_le_mul hA hfix
      _ = 2 ^ 5 := by norm_num
  · obtain ⟨t, htA₀, ht1⟩ : ∃ t ∈ A₀, t ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hE ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    obtain ⟨γ, hγ⟩ := htA₀.2
    have htA : pairHom (Γ α) (θ α).toMonoidHom γ ∈ A := hγ ▸ htA₀.1
    have hγ1 : γ ≠ 1 := fun h => ht1 (by rw [← hγ, h, map_one])
    have hγ2 : γ * γ = 1 := pairHom_injective α (by rw [map_mul, hsq _ htA, map_one])
    have hfix : Nat.card ↥(fixV A) ≤ 4 := by
      refine le_trans (Nat.card_le_card_of_injective (fun v =>
        (⟨(v : PairMod (Fin 4) (ZMod 2)).1, congrArg Prod.fst (v.2 _ htA)⟩ :
          {u : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) γ u = u}))
        fun v w h => hinj v w (congrArg Subtype.val h)) ?_
      exact card_fix_natAut_le α hγ2 hγ1
    calc Nat.card A * Nat.card ↥(fixV A) ≤ (2 * 4) * 4 :=
          Nat.mul_le_mul (hidx.trans (Nat.mul_le_mul_left 2 hA₀4)) hfix
      _ = 2 ^ 5 := by norm_num

theorem card_mul_card_fixV_le
    {A : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))}
    (hAN : A ≤ pairNormA7 α) (hA2 : IsElemAbelian2 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card ↥(fixV A) ≤ 2 ^ 6 := by
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hA2.2 x hx
  by_cases hsw : ∃ y ∈ A, (V₁ (Fin 4) (ZMod 2)).map y.toMonoidHom ≠ V₁ (Fin 4) (ZMod 2)
  · obtain ⟨y, hyA, hy⟩ := hsw
    exact (card_mul_le_of_swap α hAN hsq hyA hy).trans (by norm_num)
  · push Not at hsw
    exact card_mul_le_of_le α (fun x hx => mem_pairA7_of_map α (hAN hx) (hsw x hx)) hsq hA1

theorem rk_add_two_le_rkIdx_fixV
    {A : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))}
    (hAN : A ≤ pairNormA7 α) (hA2 : IsElemAbelian2 A) (hA1 : A ≠ ⊥) :
    rk ↥A + 2 ≤ rkIdx (fixV A) := by
  have : Finite (MulAut (PairMod (Fin 4) (ZMod 2))) := MulEquiv.finite_left
  have hmain := card_mul_card_fixV_le α hAN hA2 hA1
  have hAcard : Nat.card A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hA2)
  refine SL3Pair.le_rkIdx_of_card_mul_le card_pairMod_four _ ?_
  rw [pow_add, ← hAcard]
  calc Nat.card ↥(fixV A) * (Nat.card A * 2 ^ 2) = 4 * (Nat.card A * Nat.card ↥(fixV A)) := by
        ring
    _ ≤ 4 * 2 ^ 6 := Nat.mul_le_mul_left 4 hmain
    _ = 2 ^ 8 := by norm_num

theorem not_isFOneModule
    {X : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))}
    (hXN : X ≤ pairNormA7 α) : ¬ IsFOneModule X := by
  rintro ⟨A, ⟨hAX, hA1, hAel⟩, hoff⟩
  have h : rk ↥A + 2 ≤ rkIdx (fixV A) := rk_add_two_le_rkIdx_fixV α (hAX.trans hXN) hAel hA1
  have h' : rkIdx (fixV A) ≤ rk ↥A + 1 := hoff
  omega

theorem alphaH_eq_one
    {X : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))}
    (hXN : X ≤ pairNormA7 α) : alphaH X = 1 :=
  alphaH_eq_one_of_not_isFOneModule (not_isFOneModule α hXN)

theorem not_isFFModule
    {X : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))}
    (hXN : X ≤ pairNormA7 α) : ¬ IsFFModule X :=
  not_isFFModule_of_not_isFOneModule (IsPGroup.of_card card_pairMod_four)
    (not_isFOneModule α hXN)

theorem H8_A7Pair_alpha
    {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : A7Four H V₁ ⊥) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom))
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    ¬ IsFOneModule M ∧ alphaH M = 1 ∧ ¬ IsFFModule M := by
  obtain ⟨α', e, h2⟩ := exists_model hreal hφ hinf hsup hniso hMN
  have hF : ¬ IsFOneModule M := by
    rw [← isFOneModule_map_congrHom e]
    exact not_isFOneModule α' h2
  exact ⟨hF, alphaH_eq_one_of_not_isFOneModule hF,
    not_isFFModule_of_not_isFOneModule (isPGroup_of_equiv e) hF⟩

end A7

end H

end CFSG.Quasithin
