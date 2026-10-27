module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.Isometry
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaMinusFour
import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars
public import CFSG.GroupTheory.GL52.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.Open Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

theorem exists_minusCoords {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {n : ℕ}
    {S : Sylow 2 ↥H} {Tstar : Subgroup (MulAut W)} (hF : OmegaMinusFrame H n S Tstar) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K),
      Nat.card K = 2 ^ n ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ e : W ≃* Multiplicative (ιM → K),
        H.map (MulAut.congr e).toMonoidHom =
            (StatedOmega (StatedQuadMinus 2 K b c)).map (s16gNatHom ιM K) ∧
        Tstar.map (MulAut.congr e).toMonoidHom ≤
            (isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) ⊓
              Subgroup.normalizer
                ((StatedOmega (StatedQuadMinus 2 K b c) : Subgroup (GL ιM K)) :
                  Set (GL ιM K))).map (s16gNatHom ιM K) ∧
        ∀ w : W, w ∈ CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) ↔
          ∃ c' : K, Multiplicative.toAdd (e w) = c' • KTabC.e1M K := by
  classical
  obtain ⟨-, hN, hTN, hT2, -, hTfix⟩ := hF
  obtain ⟨-, K, hK, hKfin, b, c, hKcard, hirr, hR⟩ := hN
  letI : Field K := hK
  letI : Finite K := hKfin
  haveI hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  refine ⟨K, inferInstance, inferInstance, inferInstance, b, c, hKcard, hirr, ?_⟩
  let Γ : Subgroup (GL ιM K) := StatedOmega (StatedQuadMinus 2 K b c)
  have hRΓ : (CFSG.Quasithin.FFModel.nat Γ).Realizes H ⊤ ⊥ := hR
  obtain ⟨π, e₀, he₀⟩ := KTabC.exists_natEquiv (K := K) (ι := ιM) hRΓ
  have hSFL : KTabC.SylowFixedLine Γ (KTabC.e1M K) := KTabC.sylowFixedLine_minus K b c hirr
  let S' : Sylow 2 ↥Γ := S.mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective
  obtain ⟨x, hx⟩ := hSFL S'
  let e : W ≃* Multiplicative (ιM → K) :=
    e₀.trans (s16gNatHom ιM K ((x⁻¹ : ↥Γ) : GL ιM K))
  have he_apply : ∀ w : W, Multiplicative.toAdd (e w) =
      (((x⁻¹ : ↥Γ) : GL ιM K) : Matrix ιM ιM K) *ᵥ Multiplicative.toAdd (e₀ w) := by
    intro w
    rfl
  let xm : Matrix ιM ιM K := ((x : ↥Γ) : GL ιM K)
  let xim : Matrix ιM ιM K := ((x⁻¹ : ↥Γ) : GL ιM K)
  let w₀ : ιM → K := xm *ᵥ KTabC.e1M K
  have hw₀def : w₀ = xm *ᵥ KTabC.e1M K := rfl
  have hxmx : xm * xim = 1 := by
    simp [xm, xim]
  have hximxm : xim * xm = 1 := by
    simp [xm, xim]
  have hxmul : ∀ v : ιM → K, xm *ᵥ (xim *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, hxmx, Matrix.one_mulVec]
  have hx2 : xim *ᵥ w₀ = KTabC.e1M K := by
    rw [hw₀def, Matrix.mulVec_mulVec, hximxm, Matrix.one_mulVec]
  have hline : ∀ v : ιM → K, (∃ c : K, v = c • w₀) ↔
      ∃ c' : K, xim *ᵥ v = c' • KTabC.e1M K := by
    intro v
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, by rw [Matrix.mulVec_smul, hx2]⟩
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have h := congrArg (fun u => xm *ᵥ u) hc
      rw [Matrix.mulVec_smul, hxmul] at h
      exact h
  have hkey : ∀ h : ↥H, MulAut.congr e (h : MulAut W) =
      s16gNatHom ιM K (((x⁻¹ : ↥Γ) : GL ιM K) * π.symm h * ((x : ↥Γ) : GL ιM K)) := by
    intro h
    ext y
    apply Multiplicative.toAdd.injective
    rw [MulAut.congr_apply]
    set u : W := e.symm y with hu
    have hy : e u = y := e.apply_symm_apply y
    rw [← hy]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
    have hρ : ∀ v : W, Multiplicative.toAdd (e₀ ((h : MulAut W) v)) =
        (((π.symm h : ↥Γ) : GL ιM K) : Matrix ιM ιM K) *ᵥ
          Multiplicative.toAdd (e₀ v) := by
      intro v
      have h1 := he₀ (π.symm h) v
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1
    rw [he_apply ((h : MulAut W) u), hρ u, s16gNatHom_apply,
      toAdd_ofAdd, he_apply u]
    simp only [Units.val_mul, Matrix.mulVec_mulVec]
    congr 1
    rw [mul_assoc (xim * ((((π.symm h : ↥Γ) : GL ιM K) : Matrix ιM ιM K))) xm xim,
      hxmx, mul_one]
  have hH : H.map (MulAut.congr e).toMonoidHom = Γ.map (s16gNatHom ιM K) := by
    apply le_antisymm
    · rintro _ ⟨h, hh, rfl⟩
      change (MulAut.congr e) h ∈ Γ.map (s16gNatHom ιM K)
      rw [hkey ⟨h, hh⟩]
      exact Subgroup.mem_map_of_mem (s16gNatHom ιM K)
        (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem x.2) (π.symm ⟨h, hh⟩).2) x.2)
    · intro y hy
      obtain ⟨γ, hγΓ, rfl⟩ := Subgroup.mem_map.mp hy
      let γ' : ↥Γ := ⟨x * γ * x⁻¹,
        Γ.mul_mem (Γ.mul_mem x.2 hγΓ) (Γ.inv_mem x.2)⟩
      have hγ' : (γ' : GL ιM K) = x * γ * x⁻¹ := rfl
      have harg : x⁻¹ * π.symm (π γ') * x = (⟨γ, hγΓ⟩ : ↥Γ) := by
        rw [MulEquiv.symm_apply_apply]
        apply Subtype.ext
        change ((x⁻¹ : ↥Γ) : GL ιM K) * (γ' : GL ιM K) * ((x : ↥Γ) : GL ιM K) = γ
        rw [hγ']
        simp only [Subgroup.coe_inv, Subgroup.coe_mul]
        group
      have hb : MulAut.congr e (π γ') = s16gNatHom ιM K γ := by
        rw [hkey]
        rw [show (((x⁻¹ : ↥Γ) : GL ιM K) * π.symm (π γ') *
            ((x : ↥Γ) : GL ιM K)) = γ from by
          simpa using congrArg (fun z : ↥Γ => (z : GL ιM K)) harg]
      rw [← hb]
      exact Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom (π γ').2
  have hfixS : ∀ w : W, w ∈ CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) ↔
      ∀ s ∈ (S : Subgroup ↥H), (((π.symm s : ↥Γ) : GL ιM K) : Matrix ιM ιM K) *ᵥ
        Multiplicative.toAdd (e₀ w) = Multiplicative.toAdd (e₀ w) := by
    intro w
    rw [CFSG.Quasithin.mem_fixV]
    constructor
    · intro h s hs
      have h1 : ((s : ↥H) : MulAut W) w = w :=
        h ((s : ↥H) : MulAut W) (Subgroup.mem_map_of_mem H.subtype hs)
      have h2 := he₀ (π.symm s) w
      rw [MulEquiv.apply_symm_apply, h1] at h2
      exact h2.symm
    · intro h y hy
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
      apply e₀.injective
      apply Multiplicative.toAdd.injective
      have h2 := he₀ (π.symm s) w
      rw [MulEquiv.apply_symm_apply] at h2
      change Multiplicative.toAdd (e₀ (((s : ↥H) : MulAut W) w)) =
        Multiplicative.toAdd (e₀ w)
      rw [h2, h s hs]
  have hfixed_line : ∀ v : ιM → K,
      (∀ s ∈ (S : Subgroup ↥H), (((π.symm s : ↥Γ) : GL ιM K) : Matrix ιM ιM K) *ᵥ v = v) ↔
        ∃ c : K, v = c • w₀ := by
    intro v
    exact (KTabC.fixed_iff_fixed_sylowMap π S v).trans (hx v)
  have hfixEq : ∀ w : W, w ∈ CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) ↔
      ∃ c' : K, Multiplicative.toAdd (e w) = c' • KTabC.e1M K := by
    intro w
    exact (hfixS w).trans (by
      rw [hfixed_line (Multiplicative.toAdd (e₀ w)), he_apply w]
      exact hline _)
  have hforward : ∀ t ∈ Tstar, ∀ a ∈ H.map (MulAut.congr e).toMonoidHom,
      MulAut.congr e t * a * (MulAut.congr e t)⁻¹ ∈
        H.map (MulAut.congr e).toMonoidHom := by
    intro t ht a ha
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp ha
    change MulAut.congr e t * MulAut.congr e (h : MulAut W) * (MulAut.congr e t)⁻¹ ∈
      H.map (MulAut.congr e).toMonoidHom
    have hconj : t * (h : MulAut W) * t⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (hTN ht) h).1 hh
    have heq : MulAut.congr e t * MulAut.congr e (h : MulAut W) *
        (MulAut.congr e t)⁻¹ = MulAut.congr e (t * (h : MulAut W) * t⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [heq]
    exact Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hconj
  have ht_norm : ∀ t ∈ Tstar, MulAut.congr e t ∈ s16gNorm Γ := by
    intro t ht
    rw [s16gNorm, ← hH]
    refine (Subgroup.mem_normalizer_iff).mpr fun a =>
      ⟨fun ha => hforward t ht a ha, fun ha => ?_⟩
    have h2 := hforward t⁻¹ (Tstar.inv_mem ht)
      (MulAut.congr e t * a * (MulAut.congr e t)⁻¹) ha
    simpa [map_inv, mul_assoc] using h2
  have hw₀ : KTabC.e1M K ≠ 0 := by
    intro h0
    have h1 := congrFun h0 (Sum.inl 0)
    simp [KTabC.e1M] at h1
  have hfixT : ∀ t ∈ Tstar, ∀ c : K,
      MulAut.congr e t (Multiplicative.ofAdd (c • KTabC.e1M K)) =
        Multiplicative.ofAdd (c • KTabC.e1M K) := by
    intro t ht c
    set y : Multiplicative (ιM → K) := Multiplicative.ofAdd (c • KTabC.e1M K) with hy
    have hw : e.symm y ∈ CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) := by
      rw [hfixEq]
      exact ⟨c, by rw [MulEquiv.apply_symm_apply, hy, toAdd_ofAdd]⟩
    have h1 : t (e.symm y) = e.symm y := hTfix t ht (e.symm y) hw
    calc MulAut.congr e t y = e (t (e.symm y)) := by
          rw [MulAut.congr_apply]
          rfl
      _ = e (e.symm y) := by rw [h1]
      _ = y := e.apply_symm_apply y
  have hΓQ : ∀ A ∈ Γ, ∀ v : ιM → K,
      CFSG.LieType.Universal.Spin.quadMinus 2 K b c
        (((A : GL ιM K) : Matrix ιM ιM K) *ᵥ v) =
      CFSG.LieType.Universal.Spin.quadMinus 2 K b c v := by
    intro A hA v
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c]
    exact CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore
      (CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore
        (StatedQuadMinus 2 K b c) hA) v
  refine ⟨e, hH, ?_, hfixEq⟩
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_eq_pow (p := 2) hT2 (⟨t, ht⟩ : ↥Tstar)
  have ht2 : t ^ 2 ^ k = 1 := by
    have hord : orderOf t = 2 ^ k := by
      rw [Subgroup.orderOf_coe (⟨t, ht⟩ : ↥Tstar), hk]
    rw [← hord]
    exact pow_orderOf_eq_one t
  have htk : (MulAut.congr e t) ^ 2 ^ k = 1 := by
    rw [← map_pow, ht2, map_one]
  obtain ⟨A, hAiso, hAnorm, hAnat⟩ :=
    exists_isoFix_of_mem_s16gNorm
      (Q := CFSG.LieType.Universal.Spin.quadMinus 2 K b c)
      (hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr)
      (hΓ := CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedOmegaMinus
        (m := 2) le_rfl hirr)
      (hΓQ := hΓQ) (w₀ := KTabC.e1M K) (hw₀ := hw₀)
      (t := MulAut.congr e t) (ht := ht_norm t ht) (k := k) (htk := htk)
      (hfix := hfixT t ht)
  have hAiso' : A ∈ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c] at hAiso
    exact hAiso
  exact Subgroup.mem_map.mpr ⟨A, ⟨hAiso', hAnorm⟩, hAnat⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
