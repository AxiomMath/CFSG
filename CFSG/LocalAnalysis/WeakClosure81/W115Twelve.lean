module

public import CFSG.LocalAnalysis.WeakClosure81.W115TwelveDefs
public import CFSG.LocalAnalysis.WeakClosure81.W115Inv34
public import CFSG.LocalAnalysis.WeakClosure81.W115Trans
public import CFSG.LocalAnalysis.WeakClosure81.W115Gen
public import CFSG.Quasithin.Background.SmithB45MatM22Small44
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Counts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W115

open CFSG.Blueprint CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.CharacterTheory.SteinbergBY CFSG.Sporadic.Mathieu CFSG.Quasithin.B45Mat
  CFSG.Quasithin.B45Mat.M22 Module Subgroup
open scoped Matrix

theorem le_mParam_of_forall_inverts {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Subgroup (MulAut W)}
    (hY : ∃ t ∈ Y, orderOf t = 2) {c : ℕ}
    (h : ∀ t ∈ Y, orderOf t = 2 → ∃ x : MulAut W, orderOf x = p ∧ t * x * t⁻¹ = x⁻¹ ∧
      2 * c ≤ rk ↥(commSub ⊤ (zpowers x))) :
    c ≤ E3.mParam Y := by
  classical
  refine SevenFour.le_mParam_of_forall hY ?_
  intro t htY ht
  obtain ⟨x, hx, htinv, hc⟩ := h t htY ht
  have hE : IsElemAbelian p (zpowers x) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
      one_zpow]
  have hinv : ∀ y ∈ zpowers x, t * y * t⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hk := map_zpow (MulAut.conj t) x k
    simp only [MulAut.conj_apply] at hk
    rw [hk, htinv, inv_zpow]
  have hle := SevenFour.rk_commSub_le_two_mul_rkIdx hW hp hp2 hE ht hinv
  omega

theorem rk_eq_finrank_f2Vec {W : Type} [CommGroup W] [Finite W] (hV : ∀ w : W, w ^ 2 = 1) :
    rk W = finrank (ZMod 2) (F2Vec W hV) := by
  have h1 : Nat.card (F2Vec W hV) = 2 ^ finrank (ZMod 2) (F2Vec W hV) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (F2Vec W hV) = Nat.card W := rfl
  unfold rk
  rw [← h2, h1, padicValNat.prime_pow]

theorem rk_commSub_zpowers_eq_rank {W : Type} [CommGroup W] [Finite W] (hV : ∀ w : W, w ^ 2 = 1)
    {n : ℕ} (x : MulAut W) (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (e : F2Vec W hV ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (he : ∀ w : W, e (F2Vec.ofV hV (x w)) = A *ᵥ e (F2Vec.ofV hV w)) :
    rk ↥(commSub ⊤ (zpowers x)) = (A - 1).rank := by
  classical
  let f : W → (Fin n → ZMod 2) := fun w => e (F2Vec.ofV hV w)
  have hfinj : Function.Injective f := fun a b h => by
    have h' := e.injective h
    exact h'
  have hfsurj : Function.Surjective f := fun v =>
    ⟨F2Vec.toV hV (e.symm v), by simp only [f, F2Vec.ofV_toV, LinearEquiv.apply_symm_apply]⟩
  have hcomm : ∀ w, f (CFSG.Quasithin.commHom x w) = (A - 1) *ᵥ f w := by
    intro w
    simp only [f, CFSG.Quasithin.commHom_apply]
    rw [F2Vec.ofV_mul, map_add, he, show F2Vec.ofV hV w⁻¹ = -F2Vec.ofV hV w from rfl, map_neg,
      Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_add_neg]
  have himg : f '' Set.range (CFSG.Quasithin.commHom x) = Set.range ((A - 1).mulVec) := by
    rw [← Set.range_comp]
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨f w, (hcomm w).symm⟩
    · rintro ⟨u, rfl⟩
      obtain ⟨w, rfl⟩ := hfsurj u
      exact ⟨w, hcomm w⟩
  have hcard : Nat.card ↥(commSub ⊤ (zpowers x)) = 2 ^ (A - 1).rank := by
    rw [CFSG.Quasithin.commSub_zpowers_eq_map (fun _ _ _ _ => Subgroup.mem_top _)]
    calc Nat.card ↥((⊤ : Subgroup W).map (CFSG.Quasithin.commHom x))
        = Nat.card (Set.range (CFSG.Quasithin.commHom x)) := by
          rw [← SetLike.coe_sort_coe, Subgroup.coe_map, Subgroup.coe_top, Set.image_univ]
      _ = Nat.card (f '' Set.range (CFSG.Quasithin.commHom x)) := (Nat.card_image_of_injective hfinj _).symm
      _ = Nat.card ↥(LinearMap.range (A - 1).mulVecLin) := by
          rw [himg, ← Matrix.coe_mulVecLin, ← LinearMap.coe_range]
          rfl
      _ = 2 ^ (A - 1).rank := by
          rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
          rfl
  unfold rk
  rw [hcard, padicValNat.prime_pow]

theorem w115_rk_le_four_mul_mParam
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hnorm : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hq : IsQuasisimple ↥L)
    (hM : IsSpor ↥L .M22) (hirr : IsIrrOn L ⊤ ⊥) : rk W ≤ 4 * E3.mParam Y := by
  classical
  have hL1 : L ≠ ⊥ := by
    intro h
    obtain ⟨a, b, hab⟩ := hq.2.2
    have hsub : Subsingleton ↥L := by rw [h]; infer_instance
    have : Subsingleton (↥L ⧸ Subgroup.center ↥L) := inferInstance
    exact hab (Subsingleton.elim (a * b) (b * a))
  have hfix : fixV L = ⊥ := w115_fixV_eq_bot_of_isIrrOn hirr hL1
  unfold E3.mParam
  by_cases hEven : Even (Nat.card Y)
  · rw [if_pos hEven]
    obtain ⟨t₀, hto⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2 (even_iff_two_dvd.1 hEven)
    have hne : ({n : ℕ | ∃ t ∈ Y, orderOf t = 2 ∧ n = rkIdx (fixV (zpowers t))} :
        Set ℕ).Nonempty := ⟨_, (t₀ : MulAut W), t₀.2, by rwa [Subgroup.orderOf_coe], rfl⟩
    obtain ⟨t, htY, hto2, hteq⟩ := Nat.sInf_mem hne
    rw [hteq]
    obtain ⟨b, hb⟩ := w115_fourConj_of_isSpor hLY hnorm hF hM htY hto2
    exact w115_rk_le_four_mul hW hfix
      (fun i => ((b i : ↥L) : MulAut W) * t * ((b i : ↥L) : MulAut W)⁻¹) (fun i => ⟨_, rfl⟩) hb
  · rw [if_neg hEven]
    omega

theorem w115_exists_invol_aut
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hnorm : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (ψ : ↥L ≃* G22)
    {s : MulAut W} (hs : s ∈ Y) (hs2 : orderOf s = 2) :
    ∃ α : MulAut G22, α * α = 1 ∧ α ≠ 1 ∧
      ∀ l : ↥L, ((ψ.symm (α (ψ l)) : ↥L) : MulAut W) = s * l * s⁻¹ := by
  classical
  have hN : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L := by
    intro y hy l hl
    have hmem : ((⟨y, hy⟩ : ↥Y) * (⟨l, hLY hl⟩ : ↥Y) * (⟨y, hy⟩ : ↥Y)⁻¹) ∈ L.subgroupOf Y :=
      hnorm.conj_mem (⟨l, hLY hl⟩ : ↥Y) (Subgroup.mem_subgroupOf.mpr hl) (⟨y, hy⟩ : ↥Y)
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hYnorm : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy l hl
    exact hN y hy l hl
  let κ : ↥Y →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hYnorm)
  have hκ : ∀ (y : ↥Y) (γ : ↥L),
      ((κ y γ : ↥L) : MulAut W) = (y : MulAut W) * (γ : MulAut W) * (y : MulAut W)⁻¹ := by
    intro y γ
    have h := Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hYnorm y) γ
    rw [Subgroup.coe_inclusion] at h
    exact h
  let Φ : ↥Y →* MulAut G22 := ((MulAut.congr ψ).toMonoidHom).comp κ
  have hZ : Subgroup.center ↥L = ⊥ := by
    have hcard : Nat.card (Subgroup.center ↥L) =
        Nat.card (Subgroup.center ↥NativeSporadic.M22) :=
      Nat.card_congr (Subgroup.centerCongr ψ).toEquiv
    rw [CFSG.Sporadic.Schreier.m22_center_eq_bot', Subgroup.card_bot] at hcard
    exact Subgroup.eq_bot_of_card_eq _ hcard
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hκy : κ y = 1 := by
      apply (MulAut.congr ψ).injective
      rw [map_one]
      exact hy
    have hcent : (y : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hyz : (y : MulAut W) * l * (y : MulAut W)⁻¹ = l := by
        rw [← hκ y ⟨l, hl⟩, hκy]
        rfl
      exact (mul_inv_eq_iff_eq_mul.mp hyz).symm
    have hyL : (y : MulAut W) ∈ L := W4Row.mem_of_mem_centralizer_of_fstar_eq hLY hF y.2 hcent
    have hyLcenter : (⟨(y : MulAut W), hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro γ
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hcent (γ : MulAut W) γ.2
    rw [hZ, Subgroup.mem_bot] at hyLcenter
    exact Subtype.ext (by simpa using Subtype.ext_iff.mp hyLcenter)
  have hs_mul : s * s = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    norm_num at hs2
  have hsY2 : (⟨s, hs⟩ : ↥Y) * ⟨s, hs⟩ = 1 := Subtype.ext (by simpa using hs_mul)
  refine ⟨Φ ⟨s, hs⟩, by rw [← map_mul, hsY2, map_one], fun h => hs1 ?_, fun l => ?_⟩
  · have h1 : (⟨s, hs⟩ : ↥Y) = 1 := hΦinj (by rw [map_one]; exact h)
    simpa using Subtype.ext_iff.mp h1
  · have hΦ : Φ ⟨s, hs⟩ (ψ l) = ψ (κ ⟨s, hs⟩ l) := by
      show ψ (κ ⟨s, hs⟩ (ψ.symm (ψ l))) = ψ (κ ⟨s, hs⟩ l)
      rw [MulEquiv.symm_apply_apply]
    rw [hΦ, MulEquiv.symm_apply_apply, hκ]

section Rep


theorem w115_twelve_le_mParam_of_rep34
    {W : Type} [CommGroup W] [Finite W] (hV : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hnorm : (L.subgroupOf Y).Normal)
    (hF : Fstar Y = L) (ψ : ↥L ≃* G22)
    (e : (autRepOf hV ψ).Equiv (matrixBaseChange (RingHom.id (ZMod 2)) rep34)) :
    12 ≤ E3.mParam Y := by
  classical
  have hEven : Even (Nat.card Y) := by
    have hL : Nat.card ↥L = 443520 := by
      rw [Nat.card_congr ψ.toEquiv]
      exact card_M22
    have hdvd : Nat.card ↥L ∣ Nat.card ↥Y := by
      have h := Subgroup.card_dvd_of_le hLY
      exact h
    rw [hL] at hdvd
    exact even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 443520).trans hdvd)
  obtain ⟨t₀, hto⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2 (even_iff_two_dvd.1 hEven)
  refine le_mParam_of_forall_inverts hV Nat.prime_three (by norm_num)
    ⟨(t₀ : MulAut W), t₀.2, by rwa [Subgroup.orderOf_coe]⟩ fun t htY ht => ?_
  obtain ⟨α, hα2, hα1, hαl⟩ := w115_exists_invol_aut hLY hnorm hF ψ htY ht
  obtain ⟨g, hg3, hαg, hrk⟩ := w115_exists_inv_rank34 α hα2 hα1
  refine ⟨((ψ.symm g : ↥L) : MulAut W), ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hg3]
  · rw [← hαl (ψ.symm g), MulEquiv.apply_symm_apply, hαg, map_inv, Subgroup.coe_inv]
  · have he : ∀ w : W, e.toLinearEquiv (F2Vec.ofV hV ((ψ.symm g : MulAut W) w)) =
        rep34 g *ᵥ e.toLinearEquiv (F2Vec.ofV hV w) := by
      intro w
      have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g
        (F2Vec.ofV hV w)
      rw [matrixBaseChange_apply, RingHom.coe_id, Matrix.map_id,
        Representation.Equiv.coe_toIntertwiningMap] at h1
      rw [Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply]
      exact h1
    rw [rk_commSub_zpowers_eq_rank hV _ (rep34 g) e.toLinearEquiv he]
    omega

end Rep

theorem w4Lem11_5Twelve_holds :
    W4Lem11_5Twelve := by
  classical
  intro W _ _ hW Y L hLY hnorm hF hq hO2 hM hirr
  by_cases h45 : 45 ≤ rk W
  · left
    have h4 := w115_rk_le_four_mul_mParam hW hLY hnorm hF hq hM hirr
    omega
  obtain ⟨ψ⟩ := hM
  let θ : ↥L ≃* G22 := ψ
  have hirrFun : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hirr.2.2.2 U hU bot_le le_top
  have hntW : Nontrivial W := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have hbot : (⊥ : Subgroup W) = ⊤ := by
      ext x
      rw [Subgroup.mem_bot]
      exact ⟨fun _ => Subgroup.mem_top x, fun _ => Subsingleton.elim x 1⟩
    exact (ne_of_lt hirr.1) hbot
  have hfin : FiniteDimensional (ZMod 2) (F2Vec W hW) := Module.Finite.of_finite
  have hrkf := rk_eq_finrank_f2Vec hW
  have hτ := isIrreducible_autRepOf hW θ hirrFun
  by_cases h34 : 34 ≤ rk W
  · left
    obtain ⟨e⟩ := m22_binary_rep34_of_le (F2Vec W hW) (autRepOf hW θ) hτ (by omega) (by omega)
    exact w115_twelve_le_mParam_of_rep34 hW hLY hnorm hF θ e
  right
  rcases m22_binary_cases (F2Vec W hW) (autRepOf hW θ) hτ (by omega) with he | he | he
  · obtain ⟨e⟩ := he
    exfalso
    have htriv : ∀ g : G22, g = 1 := by
      intro g
      have h1 : ∀ w : W, (θ.symm g : MulAut W) w = w := by
        intro w
        have h2 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g
          (F2Vec.ofV hW w)
        have h3 : rep1 g = 1 := rfl
        rw [matrixBaseChange_apply, h3, RingHom.coe_id, Matrix.map_id, Matrix.one_mulVec,
          Representation.Equiv.coe_toIntertwiningMap] at h2
        exact Additive.ofMul.injective (e.injective h2)
      have h5 : θ.symm g = 1 := Subtype.ext (MulEquiv.ext h1)
      exact θ.symm.injective (h5.trans (map_one θ.symm).symm)
    have : Subsingleton G22 := ⟨fun x y => (htriv x).trans (htriv y).symm⟩
    have hcardG : Nat.card G22 = 443520 := card_M22
    rw [Nat.card_of_subsingleton (1 : G22)] at hcardG
    norm_num at hcardG
  · obtain ⟨e⟩ := he
    have hd := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_fin_fun] at hd
    omega
  · obtain ⟨e⟩ := he
    have hd := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_fin_fun] at hd
    omega

end CFSG.LocalAnalysis.WeakClosure81.W115
