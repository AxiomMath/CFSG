module

public import CFSG.Quasithin.Background.G11Six
public import CFSG.Quasithin.Background.G10FifteenTwist
public import CFSG.Quasithin.Background.G93Apply
public import CFSG.Quasithin.Background.G116IIInputs
public import CFSG.Quasithin.Background.G116IIRank
public import CFSG.Quasithin.Background.G116IIPrep
public import CFSG.Quasithin.Background.G116IIFinish
public import CFSG.Quasithin.Background.G116IISL42
public import CFSG.Quasithin.Background.G10FifteenSwap

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace G11

theorem g116_II_of_inputs (hG93 : G93StmtDimensionOnly)
    (hSL34 : OuterSL34Input) :
    G116IIStmt := by
  have hSL42 := G11.sl42IsoA8
  intro V _ _ _ B Γ v₁ W X X₀ L hyp hnum hq I hI hone htwo hthree
  obtain ⟨x, hxX, hxne, hcompl, hn, i, hi, hi0, -, -, -, hYC, hYfaith, hFT⟩ := hone
  obtain ⟨-, hns, hfH, hiso, hdual⟩ := htwo
  set H := normalClosure Γ L with hH
  have hirr : IsIrr H I := hI.isIrr hyp.fixedSpace_H
  have hxΓ : x ∈ Γ := hyp.X_le hxX
  have hHΓ : H ≤ Γ := hyp.H_le
  have hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H := normalClosure_normal Γ L
  have hdualx : IsDualOf H I (conjSub x I) := hdual x hxX hxne
  set Y := stabilizerOf X I with hY
  have hYX : Y ≤ X := fun y hy => hy.1
  have hYΓ : Y ≤ Γ := hYX.trans hyp.X_le
  have hYI : Invariant Y I := fun k hk u hu => by
    have h1 : k u ∈ conjSub k I := apply_mem_conjSub hu
    rwa [hk.2] at h1
  obtain ⟨m, hm⟩ := exists_card_eq_two_pow_of_sq_eq_one Y fun y hy => hyp.X_sq y hy.1
  have hU : Module.finrank (ZMod 2) ↥(I ⊓ perp B v₁) ≤ m + 1 :=
    finrank_le_of_fullTransvections hi hi0 hFT hm
  have hperp := finrank_le_finrank_inf_perp_add_one hyp.toG101Hyp.nondegenerate' hyp.point I
  have h3 : 2 < Module.finrank (ZMod 2) ↥I := hyp.two_lt_finrank hirr
  have hmI : Module.finrank (ZMod 2) ↥I ≤ m + 2 := by omega
  have hYne : ∃ y ∈ Y, y ≠ 1 := by
    have h1 : Nat.card ↥Y ≠ 1 := by
      rw [hm]
      have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : Y ≠ ⊥ := fun h => h1 (Subgroup.card_eq_one.2 h)
    obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h2
    exact ⟨y, y.2, fun h => hy (Subtype.ext h)⟩
  obtain ⟨L₁, hL₁, hL₁H, hcomm, hHeq⟩ := exists_component_data hyp.component hnum hirr hfH hxΓ
    hcompl hn hdualx hYne hYC
  have hK : Invariant (H ⊔ Y) I := hirr.1.sup_subgroup hYI
  have hKΓ : H ⊔ Y ≤ Γ := sup_le hHΓ hYΓ
  have hAelem : IsElemAbelian 2 Y :=
    ⟨⟨⟨fun a b => Subtype.ext (hyp.X_comm a (hYX a.2) b (hYX b.2))⟩⟩, fun y hy => by
      rw [pow_two]
      exact hyp.X_sq y (hYX hy)⟩
  have hconcl := g93_apply hG93 V Γ (H ⊔ Y) H L₁ Y I m hK hirr.1 hq hKΓ le_sup_left
    (fun k hk h hh => hN k (hKΓ hk) h hh) hirr hfH le_sup_right hAelem hm hYfaith (by omega) hL₁
    hL₁H hcomm hHeq
  have hsd : ¬ SelfDual (restrictRange H I hirr.1) ⊤ := fun h =>
    hns (selfDual_of_restrictRange_top hirr.1 h)
  have finish : ∀ n : ℕ, 5 ≤ n → n ≠ 6 → Nonempty (↥H ≃* ↥(alternatingGroup (Fin n))) →
      Module.finrank (ZMod 2) ↥I = 4 → EndIsField (restrictRange H I hirr.1) 1 →
      Module.finrank (ZMod 2) V = 8 ∧ Nonempty (↥Γ ≃* Equiv.Perm (Fin n)) ∧
        ∃ I' : Submodule (ZMod 2) V, Module.finrank (ZMod 2) ↥I' = 4 ∧
          (∀ w ∈ I', ∀ w' ∈ I', B w w' = 0) ∧
          (∀ γ ∈ (genFittingLayer ↥Γ).map Γ.subtype, ∀ v ∈ I', γ v ∈ I') ∧
          ∃ x ∈ X, (∃ v ∈ I', x v ∉ I') ∧ IsCompl I' (I'.map (x : V →ₗ[ZMod 2] V)) := by
    intro n hn5 hn6 ⟨e⟩ hd4 hE
    exact concl8_of_alt hn5 hn6 hHΓ hyp.X_le hN hirr hxX hcompl hxne hn hiso hd4 hE e
  rcases hconcl.of_not_selfDual hsd with h1 | h3' | h5 | h8 | h11 | h13 | h14 | h17
  ·
    exfalso
    obtain ⟨⟨-, hd, h4, h5⟩ | ⟨-, hd, h4, h5⟩, -⟩ := h1 <;> omega
  ·
    obtain ⟨⟨-, -, hd, ⟨e⟩, hHΓ'⟩, hE, -⟩ := h3'
    have e' : Nonempty (↥H ≃* ↥(alternatingGroup (Fin 7))) :=
      ⟨(restrictRangeEquiv hirr.1 hfH).trans ((MulEquiv.subgroupCongr hHΓ').trans e)⟩
    exact Or.inl (finish 7 (by norm_num) (by norm_num) e' hd hE)
  ·
    exfalso
    obtain ⟨⟨h2, hd, h4, -⟩, -⟩ := h5
    omega
  ·
    exfalso
    obtain ⟨n, ⟨hn1, hd, hm1, hm2, hnat, hn1'⟩, -, -⟩ := h8
    have hn2 : n = 1 ∨ n = 2 := by omega
    rcases hn2 with rfl | rfl
    ·
      have hall := autAll_of_restrictRange_top hirr.1 (hn1' rfl)
      rcases hthree with h | h
      · exact h hall
      · omega
    ·
      obtain ⟨α, P, hαP, hα2, hcommP, hind⟩ := hyp.twist_package hxX hirr.1 hfH
      have hout : ¬ ∃ c : GLV ↥I, ∀ k : ↥(restrictRange H I hirr.1),
          ((α k : ↥(restrictRange H I hirr.1)) : GLV ↥I) = c * (k : GLV ↥I) * c⁻¹ :=
        fun hc => hn (hind hc)
      obtain ⟨s, hs, t, ht, hnot⟩ := hSL34 ↥I (restrictRange H I hirr.1) hnat α P hαP hα2 hout
      exact hnot (hcommP s hs t ht)
  ·
    obtain ⟨⟨-, hd, -, ⟨φ, -⟩, hHΓ', -⟩, hE, -⟩ := h11
    obtain ⟨e8⟩ := hSL42
    have e' : Nonempty (↥H ≃* ↥(alternatingGroup (Fin 8))) :=
      ⟨(restrictRangeEquiv hirr.1 hfH).trans (((MulEquiv.subgroupCongr hHΓ').trans φ).trans e8)⟩
    exact Or.inr (finish 8 (by norm_num) (by norm_num) e' hd hE)
  ·
    exfalso
    obtain ⟨⟨-, ⟨hd, -, hall⟩ | ⟨hd, h4⟩, h6, hHΓ'⟩, -⟩ := h13
    ·
      have hall' : AutAll (restrictRange H I hirr.1) ⊤ := by rw [hHΓ']; exact hall
      have := autAll_of_restrictRange_top hirr.1 hall'
      rcases hthree with h | h
      · exact h this
      · omega
    · omega
  ·
    exfalso
    obtain ⟨⟨hm4, hd, -⟩, -⟩ := h14
    omega
  ·
    exfalso
    obtain ⟨n, ⟨hn, hd, hm4, -⟩, -⟩ := h17
    omega

theorem g116_II (hG93 : G93StmtDimensionOnly) (hSL34 : OuterSL34Input) : G116IIStmt :=
  g116_II_of_inputs hG93 hSL34

end G11

end CFSG.Quasithin
