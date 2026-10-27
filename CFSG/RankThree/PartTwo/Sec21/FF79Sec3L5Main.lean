module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Sigma
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5ExistsA
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Split2
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Iii2
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Swap
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Conj
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Main
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAFinal

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog)
open CFSG.RankThree.PartTwo.Sec21.FF79.L41

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G}

theorem conjBy_eq_of_mem_nor {k : G} (hk : k ∈ Nor A) : conjBy k A = A := by
  have hle : conjBy k A ≤ A := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_set_normalizer_iff.mp hk y).1 hy
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjBy])

theorem ff79_3_5_of_in
    (hKL : FF79KL35a) (hKLb : FF79KL35b) (hO : FF79KLemmaOP)
    (hG : IsSimpleGroup G) (hna : ∃ x y : G, x * y ≠ y * x) (hKp : KProper InCatalog G)
    (hs : FF79Sec3 b J) (h : FF79Sec34In b J B A P D) : FF79Concl35 b A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, hoa, hK⟩ := sec35_exists_a hs h
  have hU := sec34_UFacts hs h ha hoa hK
  have haC : a ∈ CenS (U34 b a J A) := by
    intro x hx
    haveI := hU.elemU.1
    have := (IsMulCommutative.is_comm (M := ↥(U34 b a J A))).comm ⟨x, hx⟩ ⟨a, hU.a_mem⟩
    exact congrArg Subtype.val this
  obtain ⟨hel, hbN, hL⟩ := ff79_3_4_of_in hO hG hna hKp hs h a ha hoa hK
  obtain ⟨hU2, hinf, hsup, hbU2⟩ := sec35_split hG hna hKp hs h hU hoa hK haC hL
  obtain ⟨σ, hσ2, hσb, hσC, hσinv⟩ :=
    sec35_sigma hKL hG hna hKp hs h hU hoa hK haC hL hU2 hbU2
  have hP₁ : FF79Sec35P b (U34 b a J A) :=
    ⟨hel, hbN, hL, sec35_iii hKLb hG hna hKp hs h hU hoa hK haC hL⟩
  set U₁ := U34 b a J A with hU₁
  set U₂ := A ⊓ OppE 3 (CenS U₁) with hU₂
  have hU₂A : U₂ ≤ A := inf_le_left
  have hU₁A : U₁ ≤ A := hU.U_le_A
  have hσA : σ ∈ Nor A := by
    apply mem_nor_of_forall
    intro y hy
    have hy' : y ∈ U₁ ⊔ U₂ := hsup ▸ hy
    have hle : U₁ ⊔ U₂ ≤ A.comap (MulAut.conj σ).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · have : σ * x * σ⁻¹ = x := by
          have h1 := Subgroup.mem_centralizer_iff.mp hσC x hx
          rw [← h1]; simp
        show σ * x * σ⁻¹ ∈ A
        rw [this]; exact hU₁A hx
      · show σ * x * σ⁻¹ ∈ A
        rw [hσinv x hx]; exact A.inv_mem (hU₂A hx)
    exact hle hy'
  have hσ' : IsPGroup 2 (Subgroup.zpowers σ) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hσ2]; norm_num
  obtain ⟨k, hkH, hkD⟩ := exists_conj_le_sylowOf_p h.sylD
    (Q := Subgroup.zpowers σ) ((Subgroup.zpowers_le).2 ⟨hσb, hσA⟩) hσ'
  have hkb : k ∈ Cen b := hkH.1
  have hkA : k ∈ Nor A := hkH.2
  have hσD : k * σ * k⁻¹ ∈ D := hkD σ (Subgroup.mem_zpowers σ)
  have hσ'2 : orderOf (k * σ * k⁻¹) = 2 := by
    have := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective σ
    simpa [MulAut.conj_apply, hσ2] using this
  obtain ⟨As, hAAs, -, -, -, -, hzAs, -, -⟩ := h.star
  have hz : ∀ z ∈ Subgroup.center D, z ≠ 1 → ∀ x ∈ A, z * x * z⁻¹ = x⁻¹ :=
    fun z hz hne x hx => hzAs z hz hne x (hAAs hx)
  have hkAA : conjBy k A = A := conjBy_eq_of_mem_nor hkA
  have hU₁A' : conjBy k U₁ ≤ A := hkAA ▸ Subgroup.map_mono hU₁A
  have hU₂A' : conjBy k U₂ ≤ A := hkAA ▸ Subgroup.map_mono hU₂A
  have hsup' : conjBy k U₁ ⊔ conjBy k U₂ = A := by
    rw [← Subgroup.map_sup, hsup]; exact hkAA
  have hinf' : conjBy k U₁ ⊓ conjBy k U₂ = ⊥ := by
    rw [← Subgroup.map_inf _ _ _ (MulAut.conj k).injective, hinf, Subgroup.map_bot]
  have hP₁' : FF79Sec35P b (conjBy k U₁) := sec35_conj_P hkb hP₁
  have hc₁ : Nat.card (conjBy k U₁) = 9 := by
    rw [card_conjBy, hel.2]; norm_num
  have hc₂ : Nat.card (conjBy k U₂) = 9 := by
    rw [card_conjBy, hU2.2]; norm_num
  have hσ₁ : ∀ x ∈ conjBy k U₁, (k * σ * k⁻¹) * x * (k * σ * k⁻¹)⁻¹ = x := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hσC y hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k * σ * k⁻¹ * (k * y * k⁻¹) * (k * σ * k⁻¹)⁻¹
        = k * (σ * y * σ⁻¹) * k⁻¹ := by group
      _ = k * y * k⁻¹ := by rw [← h1]; simp
  have hσ₂ : ∀ x ∈ conjBy k U₂, (k * σ * k⁻¹) * x * (k * σ * k⁻¹)⁻¹ = x⁻¹ := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k * σ * k⁻¹ * (k * y * k⁻¹) * (k * σ * k⁻¹)⁻¹
        = k * (σ * y * σ⁻¹) * k⁻¹ := by group
      _ = (k * y * k⁻¹)⁻¹ := by rw [hσinv y hy]; group
  obtain ⟨d, hdD, hd₁, hd₂⟩ := sec35_swap (A := A)
    (U₁ := conjBy k U₁) (U₂ := conjBy k U₂) (D' := D) (σ := k * σ * k⁻¹) h.elemA hU₁A' hU₂A'
    hsup' hinf' hc₁ hc₂ h.D8 h.DA hz hσD hσ'2 hσ₁ hσ₂
  have hdb : d ∈ Cen b := (h.sylD.1 hdD).1
  have hP₂' : FF79Sec35P b (conjBy k U₂) := by
    have := sec35_conj_P hdb hP₁'
    rwa [hd₁] at this
  have hle₂ : conjBy k U₂ ≤ OppE 3 (CenS (conjBy k U₁)) := by
    rw [← sec35_conj_oppE k U₁]
    exact Subgroup.map_mono inf_le_right
  have hle₁ : conjBy k U₁ ≤ OppE 3 (CenS (conjBy k U₂)) := by
    have e := sec35_conj_oppE d (conjBy k U₁)
    rw [hd₁] at e
    have := Subgroup.map_mono (f := (MulAut.conj d).toMonoidHom) hle₂
    change conjBy d (conjBy k U₂) ≤ conjBy d (OppE 3 (CenS (conjBy k U₁))) at this
    rw [hd₂, e] at this
    exact this
  exact ⟨conjBy k U₁, conjBy k U₂, hP₁'.1, hP₂'.1, hsup', hinf', hP₁'.2.1, hP₂'.2.1, hle₁,
    hle₂, hP₁'.2.2.1, hP₂'.2.2.1, hP₁'.2.2.2, hP₂'.2.2.2⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
