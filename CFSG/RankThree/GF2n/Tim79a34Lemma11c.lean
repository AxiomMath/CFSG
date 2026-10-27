module

public import CFSG.RankThree.GF2n.Tim79a34Local
public import CFSG.RankThree.GF2n.Tim79a34SpRad
public import CFSG.RankThree.GF2n.Tim79a34TwStruct

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open scoped commutatorElement Matrix

theorem lemma11c_holds (hB4 : SpRadFactsStatement) (h11a : Lemma11aStatement) :
    Lemma11cStatement := by
  intro G _ _ M V Q P H hH hZ hcP n Φ ψ hNat a T ha hT hTV b hb
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  obtain ⟨hiff, hRbar, hxOf, -⟩ := h11a G M V Q P H hH hZ hcP Φ ψ hNat a T ha hT hTV
  have hadd : ∀ x y : Fin n ⊕ Fin n → GaloisField 2 1,
      ((Additive.toMul (ψ (x + y)) : ↥(wOf V H)) : G) =
        ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) * ((Additive.toMul (ψ y) : ↥(wOf V H)) : G) := by
    intro x y
    rw [map_add]
    rfl
  have hcomm : ∀ x y : Fin n ⊕ Fin n → GaloisField 2 1,
      ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) * ((Additive.toMul (ψ y) : ↥(wOf V H)) : G) =
        ((Additive.toMul (ψ y) : ↥(wOf V H)) : G) * ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) := by
    intro x y
    rw [← hadd x y, ← hadd y x, add_comm x y]
  have hpart1 : ∀ v ∈ V, v ∉ wOf V H →
      ⁅v, ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁆ =
        ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) := by
    intro v hvV hvW
    have hvX : v ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hvV
    have hxmem : xToXbar hVH ⟨v, hvX⟩ ∈ Vy V H :=
      Subgroup.mem_subgroupOf.mpr
        (mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) ⟨v, hvX⟩, hvV, rfl⟩)
    have hmemT : xToXbar hVH ⟨v, hvX⟩ ∈ T.map Φ.toMonoidHom := by
      rw [hTV]
      exact hxmem
    have ht_mem : Φ.symm (xToXbar hVH ⟨v, hvX⟩) ∈ T := Subgroup.mem_map_equiv.mp hmemT
    have ht1 : Φ.symm (xToXbar hVH ⟨v, hvX⟩) ≠ 1 := by
      intro h1
      apply hvW
      have h2 : xToXbar hVH ⟨v, hvX⟩ = 1 := by
        have h3 := Φ.apply_symm_apply (xToXbar hVH ⟨v, hvX⟩)
        rw [h1, map_one] at h3
        exact h3.symm
      have h4 : piBar V H (Subgroup.inclusion (xOf_le_H hVH) ⟨v, hvX⟩) = 1 := by
        rw [← coe_xToXbar hVH ⟨v, hvX⟩, h2, Subgroup.coe_one]
      exact (piBar_eq_one_iff _).mp h4
    have hmat := tw_mat_eq_spTrans_one hF2 hT ht_mem ht1
    have key := hNat.equiv ⟨v, hvX⟩ b
    have hval : ((⟨v, hvX⟩ : ↥(xOf V H)) : G) = v := rfl
    rw [hmat, CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec, hb, one_mul, one_smul,
      hval] at key
    have hconj : v * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) * v⁻¹ =
        ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) := by
      rw [← key, hadd b a]
    rw [commutatorElement_def, hconj, mul_inv_eq_iff_eq_mul, hcomm b a]
  have hpart2 : ∀ w ∈ P ⊓ wOf V H, ∃ p ∈ P,
      ⁅p, ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁆ = w := by
    intro w hw
    have hwP : w ∈ P := (Subgroup.mem_inf.mp hw).1
    have hwW : w ∈ wOf V H := (Subgroup.mem_inf.mp hw).2
    obtain ⟨u, hψu⟩ : ∃ u : Fin n ⊕ Fin n → GaloisField 2 1,
        ((Additive.toMul (ψ u) : ↥(wOf V H)) : G) = w :=
      ⟨ψ.symm (Additive.ofMul ⟨w, hwW⟩), by rw [AddEquiv.apply_symm_apply]; rfl⟩
    have hu : CaseM.spForm a u = 0 := (hiff u).mp (by rw [hψu]; exact hwP)
    have hτ := spTau_mem a u (CaseM.spForm u b) hu
    have hΦτ : Φ (spTau a u (CaseM.spForm u b) hu) ∈ Rbar V H P := by
      rw [hRbar]
      exact Subgroup.mem_map_of_mem Φ.toMonoidHom hτ
    obtain ⟨x, hxP, hxτ⟩ := mem_barOf_iff.mp (mem_Rbar.mp hΦτ)
    have hpX : (x : G) ∈ xOf V H := by
      rw [hxOf]
      exact x.2
    have hxX : xToXbar hVH ⟨(x : G), hpX⟩ = Φ (spTau a u (CaseM.spForm u b) hu) :=
      Subtype.ext (by rw [coe_xToXbar]; exact hxτ)
    have hkey := hNat.equiv ⟨(x : G), hpX⟩ b
    have hmatτ : SpExtras.mat n (GaloisField 2 1) (Φ.symm (xToXbar hVH ⟨(x : G), hpX⟩)) *ᵥ b =
        b + u := by
      rw [hxX, MulEquiv.symm_apply_apply, spTau_mulVec, hb, one_smul, mul_one]
      linear_combination (norm := module)
        CFSG.Timmesfeld.Transvection.ModelRank.vec_add_self (CaseM.spForm u b • a)
    have hval2 : ((⟨(x : G), hpX⟩ : ↥(xOf V H)) : G) = (x : G) := rfl
    rw [hmatτ, hadd b u, hval2] at hkey
    refine ⟨(x : G), hxP, ?_⟩
    rw [commutatorElement_def, ← hkey, mul_inv_eq_iff_eq_mul, hcomm b u, hψu]
  exact ⟨hpart1, hpart2⟩

end CFSG.RankThree.GF2n.Tim79a

end
