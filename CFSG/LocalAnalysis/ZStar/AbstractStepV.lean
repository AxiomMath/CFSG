module

public import CFSG.LocalAnalysis.ZStar.DihedralOddCore
public import CFSG.LocalAnalysis.ZStar.ProductConjugacy

public section

namespace CFSG

namespace ZStar.AbstractStepV

open ZStar.TransferReduction ZStar.CentralizerInduction
  ZStar.DihedralCentralizer ZStar.DihedralOddCore
  ZStar.ProductConjugacy

universe u v

noncomputable local instance subgroupFintype
    {X : Type u} [Group X] [Fintype X] (H : Subgroup X) : Fintype H :=
  Fintype.ofFinite H

@[expose] def CentralizerOddCoreStable
    {X : Type u} [Group X] {A : Type v} (χ : X → A) : Prop :=
  ∀ (w : X), w ≠ 1 → w * w = 1 →
    ∀ (H : Subgroup X), H = Subgroup.centralizer ({w} : Set X) →
      ∀ (N : Subgroup H), N.Normal → Odd (Nat.card N) →
        ∀ v : H, v ∈ N → χ (w * (v : X)) = χ w

theorem abstract_stepV
    {X : Type u} [Group X] [Fintype X] {t σ : X}
    (ht : Isolated t) (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup X, H.Normal → t ∈ H → H = ⊤)
    (ih :
      ∀ {Y : Type u} [Group Y] [Fintype Y] {y : Y},
        Nat.card Y < Nat.card X → Isolated y → y * y = 1 →
          ZStarConclusion Y y)
    (hσ2 : σ * σ = 1) (htσ : Commute t σ)
    (htσ_not_conj : ¬ IsConj t σ)
    {A : Type v} (χ : X → A)
    (hχconj : ∀ {a b : X}, IsConj a b → χ a = χ b)
    (hstable : CentralizerOddCoreStable χ) :
    ZStarConclusion X t ∨
      ∀ t' σ' : X, IsConj t t' → IsConj σ σ' →
        χ (t' * σ') = χ (t * σ) := by
  by_cases hZ : ZStarConclusion X t
  · exact Or.inl hZ
  · right
    intro t' σ' htt' hσσ'
    obtain ⟨g, hg⟩ := isConj_iff.mp htt'
    let h : X := g⁻¹ * σ' * g
    have hσ'h : IsConj σ' h := by
      rw [isConj_iff]
      refine ⟨g⁻¹, ?_⟩
      dsimp only [h]
      group
    have hσh : IsConj σ h := hσσ'.trans hσ'h
    obtain ⟨q, hq⟩ := isConj_iff.mp hσh
    have hh2 : h * h = 1 := by
      calc
        h * h = (q * σ * q⁻¹) * (q * σ * q⁻¹) := by rw [hq]
        _ = q * (σ * σ) * q⁻¹ := by group
        _ = 1 := by rw [hσ2]; simp
    have hth_not_conj : ¬ IsConj t h := by
      intro hth
      exact htσ_not_conj (hth.trans hσh.symm)
    have hnotodd : ¬ Odd (orderOf (t * h)) := by
      intro hodd
      exact hth_not_conj
        (isConj_of_involutions_odd_product ht2 hh2 hodd)
    have heven : Even (orderOf (t * h)) :=
      Nat.not_odd_iff_even.mp hnotodd
    let w : X := (t * h) ^ (orderOf (t * h) / 2)
    have hwdata :
        w ≠ 1 ∧ w * w = 1 ∧ Commute t w ∧ Commute h w := by
      simpa only [w] using halfOrder_involution ht2 hh2 heven
    obtain ⟨hw1, hw2, htw, _hhw⟩ := hwdata
    have hcentral :=
      dihedral_centralizer_induction_or_zStar
        ht ht2 hh2 hmin ih heven
    change ZStarConclusion X t ∨
      ∃ (H : Subgroup X) (htH : t ∈ H) (_hhH : h ∈ H) (_hwH : w ∈ H),
        H = Subgroup.centralizer ({w} : Set X) ∧ H ≠ ⊤ ∧
        Nat.card H < Nat.card X ∧
        Isolated (⟨t, htH⟩ : H) ∧
        (⟨t, htH⟩ : H) * ⟨t, htH⟩ = 1 ∧
        ZStarConclusion H (⟨t, htH⟩ : H) at hcentral
    obtain hZ' | ⟨H, htH, hhH, _hwH, hH, _hHne, _hcard,
        _hisolatedH, htH2, hih⟩ := hcentral
    · exact (hZ hZ').elim
    · let tH : H := ⟨t, htH⟩
      let hH' : H := ⟨h, hhH⟩
      have hhH2 : hH' * hH' = 1 := by
        apply Subtype.ext
        exact hh2
      have hevenH : Even (orderOf (tH * hH')) := by
        rw [← Subgroup.orderOf_coe (tH * hH')]
        simpa only [tH, hH', Subgroup.coe_mul, Subgroup.coe_mk] using heven
      change ZStarConclusion H tH at hih
      obtain ⟨N, hNnormal, hNodd, hNcomm⟩ := hih
      let xH : H := tH * hH'
      let nH : ℕ := orderOf xH / 2
      let wH : H := xH ^ nH
      let vH : H := wH * xH
      let μH : H := tH * wH
      have hpkg :=
        dihedral_oddCore_package htH2 hhH2 hevenH N hNodd hNcomm
      change xH ^ 2 ∈ N ∧ Odd (orderOf (xH ^ 2)) ∧ Odd nH ∧
        vH = xH ^ (nH + 1) ∧ vH ∈ N ∧
        μH * μH = 1 ∧ μH * hH' = vH ∧ μH * hH' ∈ N ∧
        Odd (orderOf (μH * hH')) ∧ IsConj μH hH' at hpkg
      obtain ⟨_hx2N, _hx2odd, _hnodd, _hvpow, hvN, _hμ2, _hμhv,
        _hμhN, _hμhodd, hμhconj⟩ := hpkg
      have horder_xH : orderOf xH = orderOf (t * h) := by
        rw [← Subgroup.orderOf_coe xH]
        rfl
      have hnH : nH = orderOf (t * h) / 2 := by
        dsimp only [nH]
        rw [horder_xH]
      have hwHcoe : (wH : X) = w := by
        dsimp only [wH, w]
        simp only [Subgroup.coe_pow]
        rw [hnH]
        rfl
      have hwvH : w * (vH : X) = t * h := by
        calc
          w * (vH : X) = w * ((wH : X) * (xH : X)) := rfl
          _ = w * (w * (t * h)) := by
            rw [hwHcoe]
            rfl
          _ = t * h := by rw [← mul_assoc, hw2, one_mul]
      have hχthw : χ (t * h) = χ w := by
        simpa only [hwvH] using
          hstable w hw1 hw2 H hH N hNnormal hNodd vH hvN
      have hμHcoe : (μH : X) = t * w := by
        calc
          (μH : X) = t * (wH : X) := rfl
          _ = t * w := by rw [hwHcoe]
      have htμH_eq_w : t * (μH : X) = w := by
        rw [hμHcoe, ← mul_assoc, ht2, one_mul]
      have htμH : Commute t (μH : X) := by
        rw [hμHcoe]
        exact (Commute.refl t).mul_right htw
      have hμhconjX : IsConj (μH : X) h :=
        H.subtype.map_isConj hμhconj
      have hσμH : IsConj σ (μH : X) :=
        hσh.trans hμhconjX.symm
      have hprod : IsConj (t * σ) (t * (μH : X)) :=
        product_isConj_of_isolated ht ht2 htσ htμH hσμH
      have hχth : χ (t * h) = χ (t * σ) := by
        calc
          χ (t * h) = χ w := hχthw
          _ = χ (t * (μH : X)) := congrArg χ htμH_eq_w.symm
          _ = χ (t * σ) := (hχconj hprod).symm
      have hprod_initial : IsConj (t' * σ') (t * h) := by
        rw [isConj_iff]
        refine ⟨g⁻¹, ?_⟩
        calc
          g⁻¹ * (t' * σ') * (g⁻¹)⁻¹ =
              g⁻¹ * ((g * t * g⁻¹) * σ') * g := by
                rw [hg, inv_inv]
          _ = t * (g⁻¹ * σ' * g) := by group
          _ = t * h := rfl
      exact (hχconj hprod_initial).trans hχth

end ZStar.AbstractStepV

end CFSG
