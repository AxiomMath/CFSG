module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineModelAux
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineModelJ
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineModelTorus
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineModelSp

public section

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.RankThree.OrthogonalInvolutions
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.OrthBlk
  CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open scoped Matrix commutatorElement

private theorem normalizerMonoidHom_frameB {G : Type} [Group G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (5 + 1)} {t : G} (htN : t ∈ Subgroup.normalizer (K : Set G))
    (ht1 : t * B.b 1 * t⁻¹ = (B.b 1)⁻¹)
    (htj : ∀ j : Fin (5 + 1), 2 ≤ j.val → t * B.b j = B.b j * t)
    {B' : Basis3 G (5 + 1)} (hB' : Adapted B' b₀ K E)
    {j : Fin 5 → Fin 5}
    (hj : ∀ i, B.b i.succ = B'.b (j i).succ ∨
      B.b i.succ = (B'.b (j i).succ)⁻¹) (i : Fin 5) :
    (Subgroup.normalizerMonoidHom K ⟨t, htN⟩)
        ⟨B'.b (j i).succ, hB'.2.2 _ (Fin.succ_ne_zero (j i))⟩ =
      if i = 0 then
        (⟨B'.b (j i).succ, hB'.2.2 _ (Fin.succ_ne_zero (j i))⟩ : ↥K)⁻¹
      else ⟨B'.b (j i).succ, hB'.2.2 _ (Fin.succ_ne_zero (j i))⟩ := by
  have htB' : ∀ i : Fin 5, t * B'.b (j i).succ * t⁻¹ =
      if i = 0 then (B'.b (j i).succ)⁻¹ else B'.b (j i).succ := by
    intro i
    rcases hj i with h | h
    · by_cases hi : i = 0
      · subst hi
        have h' : B.b 1 = B'.b (j 0).succ := by simpa using h
        rw [h'] at ht1
        simpa using ht1
      · have h2 : 2 ≤ (i.succ).val := by
          simp only [Fin.val_succ]
          omega
        have htij := htj i.succ h2
        rw [h] at htij
        simp only [hi]
        calc t * B'.b (j i).succ * t⁻¹ = (t * B'.b (j i).succ) * t⁻¹ := rfl
          _ = (B'.b (j i).succ * t) * t⁻¹ := by rw [htij]
          _ = B'.b (j i).succ := by group
    · by_cases hi : i = 0
      · subst hi
        have h' : B.b 1 = (B'.b (j 0).succ)⁻¹ := by simpa using h
        have h1 : t * (B'.b (j 0).succ)⁻¹ * t⁻¹ = B'.b (j 0).succ := by
          simpa [h'] using ht1
        have := congrArg Inv.inv h1
        simpa [mul_assoc] using this
      · have h2 : 2 ≤ (i.succ).val := by
          simp only [Fin.val_succ]
          omega
        have htij := htj i.succ h2
        rw [h] at htij
        simp only [hi]
        have hcomm : t * B'.b (j i).succ = B'.b (j i).succ * t := by
          have h1 : B'.b (j i).succ * t * (B'.b (j i).succ)⁻¹ = t := by
            calc B'.b (j i).succ * t * (B'.b (j i).succ)⁻¹
                = B'.b (j i).succ * (t * (B'.b (j i).succ)⁻¹) := by group
              _ = B'.b (j i).succ * ((B'.b (j i).succ)⁻¹ * t) := by rw [htij]
              _ = t := by group
          have := congrArg (fun z => z * B'.b (j i).succ) h1
          simpa [mul_assoc] using this.symm
        calc t * B'.b (j i).succ * t⁻¹ = (t * B'.b (j i).succ) * t⁻¹ := rfl
          _ = (B'.b (j i).succ * t) * t⁻¹ := by rw [hcomm]
          _ = B'.b (j i).succ := by group
  let y : ↥K := ⟨B'.b (j i).succ, hB'.2.2 _ (Fin.succ_ne_zero (j i))⟩
  have hny : (Subgroup.normalizerMonoidHom K ⟨t, htN⟩) y =
      if i = 0 then y⁻¹ else y := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    by_cases hi : i = 0
    · simpa [y, hi] using htB' i
    · simpa [y, hi] using htB' i
  simpa [y] using hny

theorem isometry_mul_self_eq_one {A : Subgroup (V5 ≃ₗ[ZMod 2] V5)}
    (hAΩ : A ≤ orthDerived Q5) (F : SevOm.Frame Q5 3 A 5)
    {β : MulAut ↥(orthDerived Q5)} (hβ2 : β * β = 1)
    {h : V5 ≃ₗ[ZMod 2] V5} (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q5)
    (hhconj : ∀ x : ↥(orthDerived Q5),
      ((β x : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
        h * (x : V5 ≃ₗ[ZMod 2] V5) * h⁻¹) :
    h * h = 1 := by
  have hββ : ∀ y : ↥(orthDerived Q5), β (β y) = y := by
    intro y
    have h := congrArg (fun e : MulAut ↥(orthDerived Q5) => e y) hβ2
    simpa using h
  have hcent : ∀ y : ↥(orthDerived Q5),
      (h * h) * (y : V5 ≃ₗ[ZMod 2] V5) = (y : V5 ≃ₗ[ZMod 2] V5) * (h * h) := by
    intro y
    have h1 := hhconj (β y)
    rw [hββ y] at h1
    have h2 := hhconj y
    have h3 : (h * h) * (y : V5 ≃ₗ[ZMod 2] V5) * (h * h)⁻¹ =
        (y : V5 ≃ₗ[ZMod 2] V5) := by
      calc (h * h) * (y : V5 ≃ₗ[ZMod 2] V5) * (h * h)⁻¹
          = h * (h * (y : V5 ≃ₗ[ZMod 2] V5) * h⁻¹) * h⁻¹ := by group
        _ = h * ((β y : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) * h⁻¹ := by rw [h2]
        _ = (y : V5 ≃ₗ[ZMod 2] V5) := h1.symm
    have := congrArg (fun z => z * (h * h)) h3
    simpa [mul_assoc] using this
  have hrotΩ : ∀ k : Fin 5, frameRot F k ∈ orthDerived Q5 :=
    fun k => hAΩ (frameRot_mem F k)
  have hmem : h * h ∈ A := by
    refine mem_of_commute_frameRot hAΩ F (mul_mem hhO hhO) ?_
    intro k
    have hc := hcent ⟨frameRot F k, hrotΩ k⟩
    rw [hc]
    group
  have hhΩ : h * h ∈ orthDerived Q5 := hAΩ hmem
  have hT : ∃ U : Submodule (ZMod 2) V5, finrank (ZMod 2) U = 3 ∧ ∀ u ∈ U, Q5 u = 0 :=
    exists_totallySingular_three_quadMinus (n := 4) (by norm_num)
  have hcenter : (⟨h * h, hhΩ⟩ : ↥(orthDerived Q5)) ∈
      Subgroup.center ↥(orthDerived Q5) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hcent g).symm
  have hz : (⟨h * h, hhΩ⟩ : ↥(orthDerived Q5)) = 1 := by
    have h := hcenter
    rw [CFSG.RankThree.PartOne.center_orthDerived_eq_bot nondegenerate_Q5 hT] at h
    simpa using h
  have := congrArg (fun z : ↥(orthDerived Q5) => (z : V5 ≃ₗ[ZMod 2] V5)) hz
  simpa using this

private theorem mulAut_congr_frameB {G : Type} [Group G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (5 + 1)} {t : G} (htN : t ∈ Subgroup.normalizer (K : Set G))
    (ht1 : t * B.b 1 * t⁻¹ = (B.b 1)⁻¹)
    (htj : ∀ j : Fin (5 + 1), 2 ≤ j.val → t * B.b j = B.b j * t)
    {B' : Basis3 G (5 + 1)} (hB' : Adapted B' b₀ K E)
    {φ : ↥K ≃* ↥(orthDerived Q5)}
    {A : Subgroup (V5 ≃ₗ[ZMod 2] V5)} {F : SevOm.Frame Q5 3 A 5}
    {j : Fin 5 → Fin 5}
    (hj : ∀ i, B.b i.succ = B'.b (j i).succ ∨
      B.b i.succ = (B'.b (j i).succ)⁻¹)
    (hφB' : ∀ (k : Fin 5) (hk : B'.b k.succ ∈ K),
      ((φ ⟨B'.b k.succ, hk⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
        frameRot F k)
    (i : Fin 5) :
    ((MulAut.congr φ (Subgroup.normalizerMonoidHom K ⟨t, htN⟩)
      (φ ⟨B'.b (j i).succ, hB'.2.2 _ (Fin.succ_ne_zero (j i))⟩) :
        ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
      if i = 0 then (frameRot F (j i))⁻¹ else frameRot F (j i) := by
  have hkB' : B'.b (j i).succ ∈ K := hB'.2.2 _ (Fin.succ_ne_zero (j i))
  let y : ↥K := ⟨B'.b (j i).succ, hkB'⟩
  have hny : (Subgroup.normalizerMonoidHom K ⟨t, htN⟩) y =
      if i = 0 then y⁻¹ else y := normalizerMonoidHom_frameB htN ht1 htj hB' hj i
  have hβy : MulAut.congr φ (Subgroup.normalizerMonoidHom K ⟨t, htN⟩) (φ y) =
      φ ((Subgroup.normalizerMonoidHom K ⟨t, htN⟩) y) := by
    simp [MulAut.congr_apply]
  have hframe : ((φ y : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
      frameRot F (j i) := hφB' (j i) hkB'
  rw [hβy, hny]
  by_cases hi : i = 0
  · subst hi
    simp only [↓reduceIte, map_inv]
    simp [y, hframe]
  · simp only [hi, ↓reduceIte]
    simp [y, hframe]

theorem conj_frameRot_of_mulAut_congr {G : Type} [Group G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (5 + 1)} {t : G} (htN : t ∈ Subgroup.normalizer (K : Set G))
    (ht1 : t * B.b 1 * t⁻¹ = (B.b 1)⁻¹)
    (htj : ∀ j : Fin (5 + 1), 2 ≤ j.val → t * B.b j = B.b j * t)
    {B' : Basis3 G (5 + 1)} (hB' : Adapted B' b₀ K E)
    {φ : ↥K ≃* ↥(orthDerived Q5)}
    {A : Subgroup (V5 ≃ₗ[ZMod 2] V5)} {F : SevOm.Frame Q5 3 A 5}
    {j : Fin 5 → Fin 5} (hjinj : Function.Injective j)
    (hj : ∀ i, B.b i.succ = B'.b (j i).succ ∨
      B.b i.succ = (B'.b (j i).succ)⁻¹)
    (hφB' : ∀ (k : Fin 5) (hk : B'.b k.succ ∈ K),
      ((φ ⟨B'.b k.succ, hk⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
        frameRot F k)
    {β : MulAut ↥(orthDerived Q5)}
    (hβeq : β = MulAut.congr φ (Subgroup.normalizerMonoidHom K ⟨t, htN⟩))
    {h : V5 ≃ₗ[ZMod 2] V5}
    (hhconj : ∀ x : ↥(orthDerived Q5),
      ((β x : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
        h * (x : V5 ≃ₗ[ZMod 2] V5) * h⁻¹) :
    ∀ k : Fin 5, h * frameRot F k * h⁻¹ =
      if k = j 0 then (frameRot F k)⁻¹ else frameRot F k := by
  have hsurj : Function.Surjective j := Finite.surjective_of_injective hjinj
  intro k
  obtain ⟨i, rfl⟩ := hsurj k
  have hkB' : B'.b (j i).succ ∈ K := hB'.2.2 _ (Fin.succ_ne_zero (j i))
  let y : ↥K := ⟨B'.b (j i).succ, hkB'⟩
  have hβframe := mulAut_congr_frameB htN ht1 htj hB' hj hφB' i
  have hval : ((β (φ y) : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
      h * ((φ y : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) * h⁻¹ := hhconj (φ y)
  have hframe : ((φ y : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
      frameRot F (j i) := hφB' (j i) hkB'
  have h1 : h * frameRot F (j i) * h⁻¹ =
      if i = 0 then (frameRot F (j i))⁻¹ else frameRot F (j i) := by
    rw [hβeq] at hval
    rw [hframe] at hval
    rw [← hval]
    exact hβframe
  have hcond : (j i = j 0) ↔ i = 0 := by
    constructor
    · intro hji; exact hjinj hji
    · intro hi; rw [hi]
  simpa [hcond] using h1

private theorem mulAut_congr_commute_iff {G : Type} [Group G] {K : Subgroup G} (t : G)
    (htN : t ∈ Subgroup.normalizer (K : Set G)) (φ : ↥K ≃* ↥(orthDerived Q5))
    {g : G} (hgK : g ∈ K) :
    g * t = t * g ↔
      ((MulAut.congr φ (Subgroup.normalizerMonoidHom K ⟨t, htN⟩)
        (φ ⟨g, hgK⟩) : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
        ((φ ⟨g, hgK⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) := by
  let n : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨t, htN⟩
  let y : ↥K := ⟨g, hgK⟩
  have h1 : g * t = t * g ↔ t * g * t⁻¹ = g := by
    constructor
    · intro hc
      calc t * g * t⁻¹ = (g * t) * t⁻¹ := by rw [hc.symm]
        _ = g := by group
    · intro hc
      have hc' : t * g = g * t := by
        calc t * g = (t * g * t⁻¹) * t := by group
          _ = g * t := by rw [hc]
      exact hc'.symm
  have h2 : t * g * t⁻¹ = g ↔ n y = y := by
    constructor
    · intro hc
      apply Subtype.ext
      simpa [n, y, Subgroup.normalizerMonoidHom_apply_apply_coe] using hc
    · intro hc
      have := congrArg Subtype.val hc
      simpa [n, y, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
  have h3 : n y = y ↔
      ((MulAut.congr φ n (φ y) : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
        ((φ y : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) := by
    have hβy : MulAut.congr φ n (φ y) = φ (n y) := by simp [MulAut.congr_apply]
    constructor
    · intro hc
      rw [hβy, hc]
    · intro hc
      apply φ.injective
      rw [← hβy]
      exact Subtype.ext hc
  exact h1.trans (h2.trans h3)

theorem nineJ_equiv_restrict {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (φ : ↥K ≃* ↥(orthDerived Q5)) {a : G} (ha : a ∈ K)
    (hJleK : nineJ K a ≤ K) {U : Submodule (ZMod 2) V5}
    (hU : PolarNondegOn Q5 U) (hU2 : finrank (ZMod 2) U = 2)
    (hT : ∃ T : Submodule (ZMod 2) (perpOf Q5 U), finrank (ZMod 2) T = 3 ∧
      ∀ v ∈ T, (Q5.restrict (perpOf Q5 U)) v = 0)
    (h6 : 6 ≤ finrank (ZMod 2) (perpOf Q5 U))
    (hx3 : (((φ ⟨a, ha⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5)) ^ 3 = 1)
    (hxU : ∀ v ∈ U, ((φ ⟨a, ha⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) v ∈ U)
    (hxfix : ∀ v, ((φ ⟨a, ha⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) v = v ↔
      v ∈ perpOf Q5 U) :
    ∃ Ψ : ↥(nineJ K a) ≃* ↥(orthDerived (Q5.restrict (perpOf Q5 U))),
      (∀ (g : ↥(nineJ K a)) (w : perpOf Q5 U),
        ((((Ψ g : ↥(orthDerived (Q5.restrict (perpOf Q5 U)))) :
          perpOf Q5 U ≃ₗ[ZMod 2] perpOf Q5 U) w : perpOf Q5 U) : V5) =
          ((φ ⟨(g : G), hJleK g.2⟩ : ↥(orthDerived Q5)) :
            V5 ≃ₗ[ZMod 2] V5) (w : V5)) ∧
      ∀ (g : ↥(nineJ K a)) (v : V5), v ∈ U →
        ((φ ⟨(g : G), hJleK g.2⟩ : ↥(orthDerived Q5)) :
          V5 ≃ₗ[ZMod 2] V5) v = v := by
  obtain ⟨eW, heWrestrict, heWfixU⟩ := exists_commutator_centralizer_equiv_restrict
    (Q := Q5) (U := U) nondegenerate_Q5 hU hU2 hT h6
    (x := ((φ ⟨a, ha⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5))
    (φ ⟨a, ha⟩).2 hx3 hxU hxfix
  obtain ⟨eJ, heJ⟩ := exists_nineJ_equiv_commutator (L := orthDerived Q5) φ ha
  refine ⟨eJ.trans eW, ?_, ?_⟩
  · intro g w
    have h1 := heWrestrict (eJ g) w
    have h2 := heJ g (hJleK g.2)
    have hΨ : (eJ.trans eW) g = eW (eJ g) := rfl
    rw [hΨ, h1, h2]
  · intro g v hv
    have h := heWfixU (eJ g) v hv
    have h2 := heJ g (hJleK g.2)
    rwa [h2] at h

theorem commute_transport {G : Type} [Group G] {K : Subgroup G} {a t : G}
    (htN : t ∈ Subgroup.normalizer (K : Set G)) (φ : ↥K ≃* ↥(orthDerived Q5))
    {β : MulAut ↥(orthDerived Q5)}
    (hβeq : β = MulAut.congr φ (Subgroup.normalizerMonoidHom K ⟨t, htN⟩))
    {h : V5 ≃ₗ[ZMod 2] V5}
    (hhconj : ∀ x : ↥(orthDerived Q5),
      ((β x : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
        h * (x : V5 ≃ₗ[ZMod 2] V5) * h⁻¹)
    {u : V5} (hrefl : h = reflect Q5 u)
    {U : Submodule (ZMod 2) V5} (hUc : IsCompl U (perpOf Q5 U))
    (huW : u ∈ perpOf Q5 U)
    {Ψ : ↥(nineJ K a) ≃* ↥(orthDerived (Q5.restrict (perpOf Q5 U)))}
    (hJleK : nineJ K a ≤ K)
    (hΨrestrict : ∀ (g : ↥(nineJ K a)) (w : perpOf Q5 U),
      ((((Ψ g : ↥(orthDerived (Q5.restrict (perpOf Q5 U)))) :
        perpOf Q5 U ≃ₗ[ZMod 2] perpOf Q5 U) w : perpOf Q5 U) : V5) =
        ((φ ⟨(g : G), hJleK g.2⟩ : ↥(orthDerived Q5)) :
          V5 ≃ₗ[ZMod 2] V5) (w : V5))
    (hΨfixU : ∀ (g : ↥(nineJ K a)) (v : V5), v ∈ U →
      ((φ ⟨(g : G), hJleK g.2⟩ : ↥(orthDerived Q5)) :
        V5 ≃ₗ[ZMod 2] V5) v = v) :
    ∀ g : ↥(nineJ K a), (g : G) * t = t * (g : G) ↔
      ((Ψ g : ↥(orthDerived (Q5.restrict (perpOf Q5 U)))) :
        perpOf Q5 U ≃ₗ[ZMod 2] perpOf Q5 U) *
        reflect (Q5.restrict (perpOf Q5 U)) ⟨u, huW⟩ =
      reflect (Q5.restrict (perpOf Q5 U)) ⟨u, huW⟩ *
        ((Ψ g : ↥(orthDerived (Q5.restrict (perpOf Q5 U)))) :
          perpOf Q5 U ≃ₗ[ZMod 2] perpOf Q5 U) := by
  intro g
  let y : ↥K := ⟨(g : G), hJleK g.2⟩
  have h1 := mulAut_congr_commute_iff (K := K) t htN φ (hJleK g.2)
  rw [← hβeq] at h1
  have hβval : ((β (φ y) : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
      h * ((φ y : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) * h⁻¹ := hhconj (φ y)
  have hcommh : (g : G) * t = t * (g : G) ↔
      h * ((φ y : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) * h⁻¹ =
        ((φ y : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) := by
    refine h1.trans ?_
    rw [hβval]
  have hcommr : (g : G) * t = t * (g : G) ↔
      ((φ y : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) * reflect Q5 u =
        reflect Q5 u * ((φ y : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) := by
    rw [hcommh, hrefl]
    constructor
    · intro hc
      have h := congrArg (fun z => z * reflect Q5 u) hc
      simpa [mul_assoc] using h.symm
    · intro hc
      have h := congrArg (fun z => z * (reflect Q5 u)⁻¹) hc
      simpa [mul_assoc] using h.symm
  exact hcommr.trans (commute_reflect_iff_of_restrict hUc (hΨrestrict g) (hΨfixU g) huW)

end CFSG.StandardType.FrameRoute.FS81

end
