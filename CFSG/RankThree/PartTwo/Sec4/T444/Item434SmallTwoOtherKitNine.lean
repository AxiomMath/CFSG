module

import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open Item434Kit Item434Alt

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem layer_le_of_closure_coprime_nine (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hcen : Subgroup.center X = ⊥)
    {P : Subgroup X} (hP : A.map (quotConj e) = P.map MulAut.conj)
    (h9 : Nat.card h.layerStar = 9)
    (hgen : Subgroup.closure {x : X | Nat.Coprime (orderOf x) 3 ∧
      ∃ p ∈ P, p ≠ 1 ∧ p * x = x * p} = ⊤) :
    layer G ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hinj := conj_injective_of_center_eq_bot hcen
  set φ := layerQuot e with hφ
  have hZ : IsPGroup 3 ((⊤ : Subgroup (layer G)) ⊓ φ.ker : Subgroup (layer G)) := by
    rw [top_inf_eq, hφ, ker_layerQuot]
    exact h.isPGroup_center_layer
  have hcenL : ∀ z ∈ (⊤ : Subgroup (layer G)) ⊓ φ.ker, ∀ l ∈ (⊤ : Subgroup (layer G)),
      z * l = l * z := by
    intro z hz l _
    rw [top_inf_eq, hφ, ker_layerQuot] at hz
    exact (Subgroup.mem_center_iff.mp hz l).symm
  set C := A ⊓ Subgroup.centralizer (layer G : Set G) with hC
  have hC3 : Nat.card C = 3 := by
    have h27 : Nat.card C * Nat.card h.layerStar = 27 := h.card_inf_mul_card_layerStar
    rw [h9] at h27
    omega
  have hCe : CFSG.Assembly.IsElemAbelian 3 C := Source.isElemAbelian_of_le h.isE27.1 inf_le_left
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set R : Subgroup (layer G) := M.comap (layer G).subtype with hR
  have hlift : ∀ σ ∈ {x : X | Nat.Coprime (orderOf x) 3 ∧ ∃ p ∈ P, p ≠ 1 ∧ p * x = x * p},
      σ ∈ R.map φ := by
    rintro σ ⟨hσ3, p, hpP, hp1, hpσ⟩
    obtain ⟨x, rfl⟩ := layerQuot_surjective e σ
    obtain ⟨y, -, hyx, hy3⟩ := exists_coprime_lift φ hZ (Subgroup.mem_top x) hσ3
    have hpA : MulAut.conj p ∈ A.map (quotConj e) := hP ▸ ⟨p, hpP, rfl⟩
    obtain ⟨a, haA, hap⟩ := hpA
    have haC : a ∉ C := by
      intro haC
      apply hp1
      apply hinj
      rw [map_one, ← hap, (MonoidHom.mem_ker).mp ((ker_quotConj h.isQuasisimple e).symm ▸ haC.2)]
    obtain ⟨hBe, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hCe haC (h.isE27.1.2 a haA)
      fun b hb => hAc b hb.1 a haA
    have hBA : C ⊔ Subgroup.zpowers a ≤ A := sup_le inf_le_left (Subgroup.zpowers_le.mpr haA)
    have hB9 : 9 ≤ Nat.card (C ⊔ Subgroup.zpowers a : Subgroup G) := by rw [hBcard, hC3]
    have hconj : layerConj G a y = y := by
      refine eq_of_coprime_lift φ hZ hcenL (Subgroup.mem_top _) (Subgroup.mem_top _) ?_ ?_ hy3
      · rw [hφ, ← quotConj_layerQuot, ← hφ, hyx, hap, MulAut.conj_apply, hpσ,
          mul_inv_cancel_right]
      · rw [MulEquiv.orderOf_eq]
        exact hy3
    have hya : a * (y : G) * a⁻¹ = y := by rw [← layerConj_apply_coe, hconj]
    have hyB : (y : G) ∈ Subgroup.centralizer ((C ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
      have hCy : C ≤ Subgroup.centralizer ({(y : G)} : Set G) := fun c hc =>
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hc.2 y y.2).symm
      have hay : a ∈ Subgroup.centralizer ({(y : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc a * (y : G) = a * (y : G) * a⁻¹ * a := by group
          _ = y * a := by rw [hya]
      have hle : C ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({(y : G)} : Set G) :=
        sup_le hCy (Subgroup.zpowers_le.mpr hay)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
    exact ⟨y, (Subgroup.centralizer_le_normalizer _).trans (normalizer_le h hBA hB9) hyB, hyx⟩
  have hker : φ.ker ≤ Subgroup.center (layer G) := by rw [hφ, ker_layerQuot]
  have hrange : φ.range ≤ R.map φ := by
    rw [MonoidHom.range_eq_top.mpr (layerQuot_surjective e), ← hgen]
    exact (Subgroup.closure_le _).mpr hlift
  have htop := eq_top_of_range_le_map φ hker hrange
  intro x hx
  have hmem : (⟨x, hx⟩ : layer G) ∈ R := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

theorem false_of_closure_coprime_nine (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hcen : Subgroup.center X = ⊥)
    {P : Subgroup X} (hP : A.map (quotConj e) = P.map MulAut.conj)
    (h9 : Nat.card h.layerStar = 9)
    (hgen : Subgroup.closure {x : X | Nat.Coprime (orderOf x) 3 ∧
      ∃ p ∈ P, p ≠ 1 ∧ p * x = x * p} = ⊤) : False :=
  h.not_le (layer_le_of_closure_coprime_nine h e hcen hP h9 hgen)

theorem closure_coprime_nine_map_conj {P : Subgroup X}
    (hP : Subgroup.closure {x : X | Nat.Coprime (orderOf x) 3 ∧
      ∃ p ∈ P, p ≠ 1 ∧ p * x = x * p} = ⊤) (g : X) :
    Subgroup.closure {x : X | Nat.Coprime (orderOf x) 3 ∧
      ∃ p ∈ P.map (MulAut.conj g).toMonoidHom, p ≠ 1 ∧ p * x = x * p} = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : (MulAut.conj g).symm y ∈ Subgroup.closure {x : X | Nat.Coprime (orderOf x) 3 ∧
      ∃ p ∈ P, p ≠ 1 ∧ p * x = x * p} := by
    rw [hP]
    exact Subgroup.mem_top _
  have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hy
  rw [MonoidHom.map_closure] at h1
  have h2 : (MulAut.conj g).toMonoidHom ((MulAut.conj g).symm y) = y :=
    (MulAut.conj g).apply_symm_apply y
  rw [h2] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨x, ⟨hx3, p, hp, hp1, hpx⟩, rfl⟩
  refine ⟨?_, MulAut.conj g p, ⟨p, hp, rfl⟩, fun h0 => hp1 ?_, ?_⟩
  · rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
    exact hx3
  · exact (MulAut.conj g).injective (h0.trans (map_one _).symm)
  · change MulAut.conj g p * MulAut.conj g x = MulAut.conj g x * MulAut.conj g p
    rw [← map_mul, ← map_mul, hpx]

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
