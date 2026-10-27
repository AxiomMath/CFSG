module

public import CFSG.RankThree.Co2.Three
public import CFSG.RankThree.Co2.WData
public import Certificates.Certificate3054
public import Certificates.Certificate8101
public import Certificates.Certificate8102
public import Certificates.Certificate8103
public import Certificates.Certificate8104
public import Certificates.Certificate8105
public import Certificates.Certificate8106
public import Certificates.Certificate8108
public import Certificates.Certificate8110
public import Certificates.Certificate8111
public import Certificates.Certificate8112
public import Certificates.Certificate8113
public import Certificates.Certificate16022
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate16000
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3138
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphPi
public import CFSG.Monster.B.TwoA.Base.GeomNative
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionBase
public import CFSG.Monster.B.TwoA.Sp8.NormalizerBase
public import CFSG.Monster.B.TwoA.Sp8.Orth8Base
public import CFSG.Monster.B.TwoA.Sp8.SubgeomBuildingBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFive
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFiveBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomIsoBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomStdBase
public import CFSG.Monster.B.TwoA.Unitary.Twenty
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public noncomputable section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster.B.Short CFSG.Monster.B.TwoA.Co2Inv

theorem exists_normalizer_conj_of_weakly_closed {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (S : Sylow p X) {W : Subgroup X} (hWS : W ≤ S)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hweak : ∀ y : X, (∀ a ∈ W, y * a * y⁻¹ ∈ (S : Subgroup X)) → ∀ a ∈ W, y * a * y⁻¹ ∈ W)
    {w g : X} (hw : w ∈ W) (hgw : g * w * g⁻¹ ∈ W) :
    ∃ n ∈ Subgroup.normalizer (W : Set X), n * w * n⁻¹ = g * w * g⁻¹ := by
  set t := g * w * g⁻¹ with ht
  set C : Subgroup X := Subgroup.centralizer {t} with hC
  have hWC : W ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hWab a ha t hgw)
  have hgWC : ∀ a ∈ W, g * a * g⁻¹ ∈ C := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hWab a ha w hw
    calc g * a * g⁻¹ * (g * w * g⁻¹) = g * (a * w) * g⁻¹ := by group
      _ = g * (w * a) * g⁻¹ := by rw [this]
      _ = g * w * g⁻¹ * (g * a * g⁻¹) := by group
  have hWp : IsPGroup p W := S.isPGroup'.to_le hWS
  have hWp' : IsPGroup p (W.subgroupOf C) := hWp.comap_of_injective C.subtype C.subtype_injective
  set Wg : Subgroup X := W.map (MulAut.conj g).toMonoidHom
  have hWgp' : IsPGroup p (Wg.subgroupOf C) :=
    (hWp.map (MulAut.conj g).toMonoidHom).comap_of_injective C.subtype C.subtype_injective
  obtain ⟨Q₁, hQ₁⟩ := hWp'.exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := hWgp'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q₂ Q₁
  have hQp : IsPGroup p ((Q₁ : Subgroup C).map C.subtype) := Q₁.isPGroup'.map C.subtype
  obtain ⟨R, hR⟩ := hQp.exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq X R S
  have hWR : ∀ a ∈ W, a ∈ (R : Subgroup X) := fun a ha =>
    hR ⟨⟨a, hWC ha⟩, hQ₁ (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  have hcgR : ∀ a ∈ W, (c : X) * g * a * ((c : X) * g)⁻¹ ∈ (R : Subgroup X) := by
    intro a ha
    have h1 : (⟨g * a * g⁻¹, hgWC a ha⟩ : C) ∈ (Q₂ : Subgroup C) :=
      hQ₂ (Subgroup.mem_subgroupOf.2 ⟨a, ha, rfl⟩)
    have h2 : c * ⟨g * a * g⁻¹, hgWC a ha⟩ * c⁻¹ ∈ (Q₁ : Subgroup C) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ h1
    have h3 := hR ⟨_, h2, rfl⟩
    have e : ((c * ⟨g * a * g⁻¹, hgWC a ha⟩ * c⁻¹ : C) : X) =
        (c : X) * g * a * ((c : X) * g)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [← e]
    exact h3
  have hS : ∀ x ∈ (R : Subgroup X), r * x * r⁻¹ ∈ (S : Subgroup X) := by
    intro x hx
    rw [← hr, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj r) _ hx
  have hrN : r ∈ Subgroup.normalizer (W : Set X) :=
    mem_normalizer_of_conj_mem (hweak r fun a ha => hS a (hWR a ha))
  have hrcgN : r * ((c : X) * g) ∈ Subgroup.normalizer (W : Set X) := by
    apply mem_normalizer_of_conj_mem
    apply hweak
    intro a ha
    have := hS _ (hcgR a ha)
    have e : r * ((c : X) * g * a * ((c : X) * g)⁻¹) * r⁻¹ =
        r * ((c : X) * g) * a * (r * ((c : X) * g))⁻¹ := by group
    rw [← e]
    exact this
  refine ⟨(c : X) * g, ?_, ?_⟩
  · have := (Subgroup.normalizer (W : Set X)).mul_mem
      ((Subgroup.normalizer (W : Set X)).inv_mem hrN) hrcgN
    simpa [mul_assoc] using this
  · have hct : (c : X) * t * (c : X)⁻¹ = t := by
      have := Subgroup.mem_centralizer_singleton_iff.1 c.2
      rw [this, mul_inv_cancel_right]
    calc (c : X) * g * w * ((c : X) * g)⁻¹ = (c : X) * t * (c : X)⁻¹ := by rw [ht]; group
      _ = t := hct

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

abbrev aG : G := h.rG 1

abbrev IG : Subgroup G := Subgroup.centralizer ({h.aG} : Set G)

abbrev X0G : Subgroup G := Subgroup.centralizer ({h.z} : Set G) ⊓ h.IG

abbrev WG : Subgroup G := h.liftG (subW wWords)

theorem X0G_eq : h.X0G = h.liftG (Subgroup.centralizer {rep 1}) := h.inf_centralizer (rep 1)

theorem card_X0G : Nat.card h.X0G = 2752512 := by
  rw [h.X0G_eq, card_liftG]
  exact card_C 1 (by norm_num) (m := 2752512) (by decide) (classSizes_pos (by norm_num))

theorem aG_mul_self : h.aG * h.aG = 1 := by
  show ((h.φ.symm (rep 1) * h.φ.symm (rep 1) : h.H) : G) = 1
  rw [← map_mul, rep_mul_self (by norm_num), map_one]
  rfl

theorem aG_mem_H : h.aG ∈ h.H := (h.φ.symm (rep 1)).2

theorem z_mem_IG : h.z ∈ h.IG :=
  Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_singleton_iff.1 h.aG_mem_H).symm

theorem WG_le_X0G : h.WG ≤ h.X0G := fun x hx =>
  Subgroup.mem_inf.2 ⟨h.liftG_le_H _ hx, h.liftG_le_centralizer W_le_C1 hx⟩

theorem z_mem_WG : h.z ∈ h.WG := by
  rw [← h.rG_zero, rG, rep_zero]
  exact h.φ_symm_mem_liftG rCr_mem_W

theorem aG_mem_WG : h.aG ∈ h.WG := h.φ_symm_mem_liftG rep_one_mem_W

theorem WG_comm {x y : G} (hx : x ∈ h.WG) (hy : y ∈ h.WG) : x * y = y * x := by
  obtain ⟨hxH, hxW⟩ := h.mem_liftG.1 hx
  obtain ⟨hyH, hyW⟩ := h.mem_liftG.1 hy
  have e : (⟨x, hxH⟩ : h.H) * ⟨y, hyH⟩ = ⟨y, hyH⟩ * ⟨x, hxH⟩ := by
    apply h.φ.injective
    rw [map_mul, map_mul]
    exact elemTwo_W.2 _ hxW _ hyW
  exact congrArg Subtype.val e

theorem WG_sq {x : G} (hx : x ∈ h.WG) : x * x = 1 := by
  obtain ⟨hxH, hxW⟩ := h.mem_liftG.1 hx
  have e : (⟨x, hxH⟩ : h.H) * ⟨x, hxH⟩ = 1 := by
    apply h.φ.injective
    rw [map_mul, map_one]
    exact elemTwo_W.1 _ hxW
  exact congrArg Subtype.val e

@[expose] def MixedG (x : G) : Prop :=
  (IsConj h.z x ∧ IsConj h.aG (x * h.aG)) ∨ (IsConj h.aG x ∧ IsConj h.z (x * h.aG))

theorem exists_class {t : h.H} (ht2 : (t : G) * t = 1) (ht1 : (t : G) ≠ 1) :
    ∃ c < 10, IsConj (rep c) (h.φ t) := by
  have h2 : h.φ t * h.φ t = 1 := by
    rw [← map_mul]
    have : t * t = 1 := Subtype.ext ht2
    rw [this, map_one]
  have h1 : h.φ t ≠ 1 := by
    intro e
    apply ht1
    have : t = 1 := (MulEquiv.map_eq_one_iff h.φ).1 e
    rw [this]
    rfl
  obtain ⟨c, hc, hct⟩ := exists_isConj_rep (h.φ t) h2 h1
  exact ⟨c, hc, hct.symm⟩

theorem sq_of_isConj {x y : G} (hx : x * x = 1) (hxy : IsConj x y) : y * y = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hxy
  calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    _ = 1 := by rw [hx]; group

theorem ne_one_of_isConj {x y : G} (hx : x ≠ 1) (hxy : IsConj x y) : y ≠ 1 := by
  rintro rfl
  exact hx (isConj_one_left.1 hxy)

theorem mul_aG_mem_H {x : G} (hx : x ∈ h.X0G) : x * h.aG ∈ h.H :=
  h.H.mul_mem (Subgroup.mem_inf.1 hx).1 h.aG_mem_H

theorem φ_mul_aG {x : G} (hx : x ∈ h.X0G) :
    h.φ ⟨x * h.aG, h.mul_aG_mem_H hx⟩ = h.φ ⟨x, (Subgroup.mem_inf.1 hx).1⟩ * rep 1 := by
  have e : (⟨x * h.aG, h.mul_aG_mem_H hx⟩ : h.H) =
      ⟨x, (Subgroup.mem_inf.1 hx).1⟩ * h.φ.symm (rep 1) := rfl
  rw [e, map_mul, MulEquiv.apply_symm_apply]

theorem φ_comm_rep1 {x : G} (hx : x ∈ h.X0G) :
    h.φ ⟨x, (Subgroup.mem_inf.1 hx).1⟩ * rep 1 = rep 1 * h.φ ⟨x, (Subgroup.mem_inf.1 hx).1⟩ := by
  rw [h.X0G_eq] at hx
  obtain ⟨_, hS⟩ := h.mem_liftG.1 hx
  exact (Subgroup.mem_centralizer_singleton_iff.1 hS)

theorem isConj_aG_iff {t : h.H} {c : ℕ} (hc : c < 10) (htc : IsConj (rep c) (h.φ t)) :
    IsConj h.aG (t : G) ↔ inB c = true :=
  (h.isConj_iff_of_class hc htc).2.1

theorem typeABG_iff {x : G} (hx : x ∈ h.X0G) :
    (IsConj h.z x ∧ IsConj h.aG (x * h.aG)) ↔
      TypeAB (h.φ ⟨x, (Subgroup.mem_inf.1 hx).1⟩) := by
  have hv := h.φ_mul_aG hx
  have haG2 : h.aG * h.aG = 1 := h.aG_mul_self
  have haG1 : h.aG ≠ 1 := h.rG_ne_one (by norm_num)
  have hz2 : h.z * h.z = 1 := h.sq_eq_one_of_isConj_z (IsConj.refl _)
  have hz1 : h.z ≠ 1 := h.ne_one_of_isConj_z (IsConj.refl _)
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨c, hc, hcu⟩ := h.exists_class (t := ⟨x, (Subgroup.mem_inf.1 hx).1⟩)
      (sq_of_isConj hz2 h1) (ne_one_of_isConj hz1 h1)
    obtain ⟨c', hc', hcv⟩ := h.exists_class (t := ⟨x * h.aG, h.mul_aG_mem_H hx⟩)
      (sq_of_isConj haG2 h2) (ne_one_of_isConj haG1 h2)
    refine ⟨c, hc, c', hc', (h.isConj_iff_of_class hc hcu).1.1 h1,
      (h.isConj_aG_iff hc' hcv).1 h2, hcu, ?_⟩
    rw [← hv]
    exact hcv
  · rintro ⟨c, hc, c', hc', hA, hB, hcu, hcv⟩
    rw [← hv] at hcv
    exact ⟨(h.isConj_iff_of_class hc hcu).1.2 hA, (h.isConj_aG_iff hc' hcv).2 hB⟩

theorem typeBAG_iff {x : G} (hx : x ∈ h.X0G) :
    (IsConj h.aG x ∧ IsConj h.z (x * h.aG)) ↔
      TypeBA (h.φ ⟨x, (Subgroup.mem_inf.1 hx).1⟩) := by
  have hv := h.φ_mul_aG hx
  have haG2 : h.aG * h.aG = 1 := h.aG_mul_self
  have haG1 : h.aG ≠ 1 := h.rG_ne_one (by norm_num)
  have hz2 : h.z * h.z = 1 := h.sq_eq_one_of_isConj_z (IsConj.refl _)
  have hz1 : h.z ≠ 1 := h.ne_one_of_isConj_z (IsConj.refl _)
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨c, hc, hcu⟩ := h.exists_class (t := ⟨x, (Subgroup.mem_inf.1 hx).1⟩)
      (sq_of_isConj haG2 h1) (ne_one_of_isConj haG1 h1)
    obtain ⟨c', hc', hcv⟩ := h.exists_class (t := ⟨x * h.aG, h.mul_aG_mem_H hx⟩)
      (sq_of_isConj hz2 h2) (ne_one_of_isConj hz1 h2)
    refine ⟨c, hc, c', hc', (h.isConj_aG_iff hc hcu).1 h1,
      (h.isConj_iff_of_class hc' hcv).1.1 h2, hcu, ?_⟩
    rw [← hv]
    exact hcv
  · rintro ⟨c, hc, c', hc', hB, hA, hcu, hcv⟩
    rw [← hv] at hcv
    exact ⟨(h.isConj_aG_iff hc hcu).2 hB, (h.isConj_iff_of_class hc' hcv).1.2 hA⟩

theorem mixedG_iff {x : G} (hx : x ∈ h.X0G) :
    h.MixedG x ↔ TypeAB (h.φ ⟨x, (Subgroup.mem_inf.1 hx).1⟩) ∨
      TypeBA (h.φ ⟨x, (Subgroup.mem_inf.1 hx).1⟩) :=
  or_congr (h.typeABG_iff hx) (h.typeBAG_iff hx)

theorem mem_WG_iff {x : G} (hx : x ∈ h.X0G) : x ∈ h.WG ↔ x = 1 ∨ x = h.aG ∨ h.MixedG x := by
  constructor
  · intro hxW
    obtain ⟨hxH, hxS⟩ := h.mem_liftG.1 hxW
    rcases mem_W_cases hxS with e | e | e | e
    · left
      have : (⟨x, hxH⟩ : h.H) = 1 := (MulEquiv.map_eq_one_iff h.φ).1 e
      exact congrArg Subtype.val this
    · right; left
      have : (⟨x, hxH⟩ : h.H) = h.φ.symm (rep 1) := by rw [← e, MulEquiv.symm_apply_apply]
      exact congrArg Subtype.val this
    · exact Or.inr (Or.inr ((h.mixedG_iff hx).2 (Or.inl e)))
    · exact Or.inr (Or.inr ((h.mixedG_iff hx).2 (Or.inr e)))
  · rintro (rfl | rfl | hm)
    · exact h.WG.one_mem
    · exact h.aG_mem_WG
    · have hW := mem_W_of_type (h.φ_comm_rep1 hx) ((h.mixedG_iff hx).1 hm)
      have e : ((h.φ.symm (h.φ ⟨x, (Subgroup.mem_inf.1 hx).1⟩) : h.H) : G) = x := by
        rw [MulEquiv.symm_apply_apply]
      rw [← e]
      exact h.φ_symm_mem_liftG hW

theorem mixedG_conj {i : G} (hi : i ∈ h.IG) {x : G} (hx : h.MixedG x) :
    h.MixedG (i * x * i⁻¹) := by
  have hia : i * h.aG * i⁻¹ = h.aG := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hi, mul_inv_cancel_right]
  have e : i * x * i⁻¹ * h.aG = i * (x * h.aG) * i⁻¹ := by
    calc i * x * i⁻¹ * h.aG = i * x * i⁻¹ * (i * h.aG * i⁻¹) := by rw [hia]
      _ = i * (x * h.aG) * i⁻¹ := by group
  unfold MixedG at hx ⊢
  rw [e, isConj_conj_right, isConj_conj_right, isConj_conj_right, isConj_conj_right]
  exact hx

theorem conj_mem_WG {i : G} (hi : i ∈ h.IG) {w : G} (hw : w ∈ h.WG)
    (hiw : i * w * i⁻¹ ∈ h.X0G) : i * w * i⁻¹ ∈ h.WG := by
  rcases (h.mem_WG_iff (h.WG_le_X0G hw)).1 hw with rfl | rfl | hm
  · simp only [mul_one, mul_inv_cancel]
    exact h.WG.one_mem
  · rw [Subgroup.mem_centralizer_singleton_iff.1 hi, mul_inv_cancel_right]
    exact h.aG_mem_WG
  · exact (h.mem_WG_iff hiw).2 (Or.inr (Or.inr (h.mixedG_conj hi hm)))

abbrev S0G : Subgroup G := h.liftG (subW pWords1)

theorem S0G_le_X0G : h.S0G ≤ h.X0G := by
  rw [h.X0G_eq]
  intro x hx
  obtain ⟨hxH, hxS⟩ := h.mem_liftG.1 hx
  exact h.mem_liftG.2 ⟨hxH, P1_le_C1 hxS⟩

theorem WG_le_S0G : h.WG ≤ h.S0G := by
  intro x hx
  obtain ⟨hxH, hxS⟩ := h.mem_liftG.1 hx
  exact h.mem_liftG.2 ⟨hxH, W_le_P1 hxS⟩

theorem card_S0G : Nat.card h.S0G = 131072 := by rw [card_liftG, card_P1]

theorem isConj_aG_z_mul : IsConj h.aG (h.z * h.aG) := by
  have hzW : h.z * h.aG ∈ h.WG := h.WG.mul_mem h.z_mem_WG h.aG_mem_WG
  have hzX := h.WG_le_X0G hzW
  have hz1 : h.z * h.aG ≠ 1 := by
    intro e
    have : h.z = h.aG := by
      calc h.z = h.z * h.aG * h.aG := by rw [mul_assoc, h.aG_mul_self, mul_one]
        _ = h.aG := by rw [e, one_mul]
    exact h.not_isConj_z_one (isConj_iff.2 ⟨1, by rw [one_mul, inv_one, mul_one, this]⟩)
  have hza : h.z * h.aG ≠ h.aG := by
    intro e
    exact h.ne_one_of_isConj_z (IsConj.refl _) (mul_eq_right.1 e)
  rcases (h.mem_WG_iff hzX).1 hzW with e | e | hm
  · exact absurd e hz1
  · exact absurd e hza
  · rcases hm with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exfalso
      rw [mul_assoc, h.aG_mul_self, mul_one] at h2
      exact h.not_isConj_z_one h2.symm
    · exact h1

theorem card_sylow_I : Nat.card (h.S0G.subgroupOf h.IG) = 2 ^ (Nat.card h.IG).factorization 2 := by
  haveI := h.finite
  have hS0I : h.S0G ≤ h.IG := fun x hx => (Subgroup.mem_inf.1 (h.S0G_le_X0G hx)).2
  set zI : h.IG := ⟨h.z, h.z_mem_IG⟩
  have hcent : (Subgroup.centralizer ({zI} : Set h.IG)).map h.IG.subtype = h.X0G := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy)), y.2⟩
    · intro hx
      exact ⟨⟨x, (Subgroup.mem_inf.1 hx).2⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).1)), rfl⟩
  have hcardC : Nat.card (Subgroup.centralizer ({zI} : Set h.IG)) = 2752512 := by
    rw [← h.card_X0G, ← hcent, Subgroup.card_map_of_injective h.IG.subtype_injective]
  refine card_eq_of_center_isolated (z := zI) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (h.S0G_le_X0G (Subgroup.mem_subgroupOf.1 hx))).1
  · exact Subgroup.mem_subgroupOf.2 (h.WG_le_S0G h.z_mem_WG)
  · rw [card_subgroupOf_eq hS0I, h.card_S0G, hcardC,
      factorization_two_eq (by norm_num : 2752512 = 2 ^ 17 * 21) (by decide)]
    norm_num
  · intro y hy hyc hzy
    have hyS := Subgroup.mem_subgroupOf.1 hy
    obtain ⟨hyH, hyP⟩ := h.mem_liftG.1 hyS
    have hcP : ∀ s ∈ subW pWords1, h.φ ⟨y, hyH⟩ * s = s * h.φ ⟨y, hyH⟩ := by
      intro s hs
      have hsS : ((h.φ.symm s : h.H) : G) ∈ h.S0G := h.φ_symm_mem_liftG hs
      have hsI := hS0I hsS
      have := hyc ⟨_, hsI⟩ (Subgroup.mem_subgroupOf.2 hsS)
      have e : (y : G) * (h.φ.symm s : G) = (h.φ.symm s : G) * y := congrArg Subtype.val this
      exact (h.commute_iff ⟨y, hyH⟩ s).1 e
    obtain ⟨i, hi⟩ := isConj_iff.1 hzy
    have hi' : (i : G) * h.z * (i : G)⁻¹ = y := congrArg Subtype.val hi
    have hiz : IsConj h.z (y : G) := isConj_iff.2 ⟨i, hi'⟩
    rcases mem_center_P1 hyP hcP with e | e | e | e
    · exfalso
      have : (⟨y, hyH⟩ : h.H) = 1 := (MulEquiv.map_eq_one_iff h.φ).1 e
      exact h.ne_one_of_isConj_z hiz (congrArg Subtype.val this)
    · exfalso
      have : (⟨y, hyH⟩ : h.H) = h.φ.symm (rep 1) := by rw [← e, MulEquiv.symm_apply_apply]
      have hya : (y : G) = h.aG := congrArg Subtype.val this
      have hia : (i : G) * h.aG = h.aG * (i : G) := Subgroup.mem_centralizer_singleton_iff.1 i.2
      have hzz : h.z = h.aG := by
        calc h.z = (i : G)⁻¹ * ((i : G) * h.z * (i : G)⁻¹) * (i : G) := by group
          _ = (i : G)⁻¹ * (h.aG * (i : G)) := by rw [hi', hya, mul_assoc]
          _ = h.aG := by rw [← hia, ← mul_assoc, inv_mul_cancel, one_mul]
      exact h.not_isConj_z_one (isConj_iff.2 ⟨1, by rw [one_mul, inv_one, mul_one, hzz]⟩)
    · apply Subtype.ext
      have : (⟨y, hyH⟩ : h.H) = h.zG := by
        apply h.φ.injective
        rw [e, h.φ_zG]
      exact congrArg (Subtype.val : h.H → G) this
    · exfalso
      have : (⟨y, hyH⟩ : h.H) = h.zG * h.φ.symm (rep 1) := by
        apply h.φ.injective
        rw [e, map_mul, h.φ_zG, MulEquiv.apply_symm_apply]
      have hy' : (y : G) = h.z * h.aG := congrArg Subtype.val this
      rw [hy'] at hiz
      exact h.not_isConj_z_one (hiz.trans h.isConj_aG_z_mul.symm)

theorem exists_conj_of_typeAB {w : G} (hw : w ∈ h.X0G) (hz : IsConj h.z w)
    (ha : IsConj h.aG (w * h.aG)) : ∃ i ∈ h.IG, i * h.z * i⁻¹ = w := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hz
  have hwa : w * h.aG = h.aG * w :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hw).2
  set b := g⁻¹ * h.aG * g with hb
  have hbH : b ∈ h.H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * h.aG * g * h.z = g⁻¹ * (h.aG * (g * h.z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * h.z * g⁻¹) * h.aG) * g := by rw [hg, hwa]
      _ = h.z * (g⁻¹ * h.aG * g) := by group
  have hab : IsConj h.aG b := isConj_iff.2 ⟨g⁻¹, by rw [hb, inv_inv]⟩
  have habz : IsConj h.aG (b * h.z) := by
    have e : b * h.z = g⁻¹ * (w * h.aG) * g := by
      rw [hwa, hb, ← hg]
      group
    rw [e]
    exact ha.trans (isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩)
  set u : h.H := ⟨b, hbH⟩
  have haG2 : h.aG * h.aG = 1 := h.aG_mul_self
  have haG1 : h.aG ≠ 1 := h.rG_ne_one (by norm_num)
  obtain ⟨c, hc, hcu⟩ := h.exists_class (t := u) (sq_of_isConj haG2 hab)
    (ne_one_of_isConj haG1 hab)
  have hB := (h.isConj_aG_iff hc hcu).1 hab
  set v : h.H := u * h.zG
  have hv : h.φ v = h.φ u * rCr := (map_mul h.φ u h.zG).trans (congrArg (h.φ u * ·) h.φ_zG)
  have hcv : IsConj (rep c * rCr) (h.φ v) := by
    obtain ⟨k, hk⟩ := isConj_iff.1 hcu
    refine isConj_iff.2 ⟨k, ?_⟩
    rw [hv, ← hk]
    have hkr : k * rCr * k⁻¹ = rCr := conj_rCr k
    calc k * (rep c * rCr) * k⁻¹ = k * rep c * k⁻¹ * (k * rCr * k⁻¹) := by group
      _ = k * rep c * k⁻¹ * rCr := by rw [hkr]
  have hvG : (v : G) = b * h.z := rfl
  have hc1 : c = 1 := by
    have hc' : c = 1 ∨ c = 3 ∨ c = 5 := by
      simp only [inB, Bool.or_eq_true, beq_iff_eq] at hB
      omega
    rcases hc' with rfl | rfl | rfl
    · rfl
    · exfalso
      have e : rep 3 * rCr = rep 2 := by
        rw [← rep_two_mul_rCr, mul_assoc, rCr_mul_self, mul_one]
      rw [e] at hcv
      have hzv := (h.isConj_iff_of_class (by norm_num) hcv).1.2 rfl
      rw [hvG] at hzv
      exact h.not_isConj_z_one (hzv.trans habz.symm)
    · exfalso
      rw [rep_five_mul_rCr] at hcv
      have h8v := (h.isConj_iff_of_class (by norm_num) hcv).2.2.2 (Or.inl rfl)
      rw [hvG] at h8v
      exact h.not_isConj_one_eight (habz.trans h8v.symm)
  subst hc1
  obtain ⟨k, hk⟩ := isConj_iff.1 hcu
  set kG : G := ((h.φ.symm k : h.H) : G)
  have hkb : kG * h.aG * kG⁻¹ = b := by
    have e : h.φ.symm k * h.φ.symm (rep 1) * (h.φ.symm k)⁻¹ = u := by
      apply h.φ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hk]
    exact congrArg Subtype.val e
  have hkz : kG * h.z * kG⁻¹ = h.z := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 (h.φ.symm k).2, mul_inv_cancel_right]
  refine ⟨g * kG, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * kG * h.aG = g * (kG * h.aG * kG⁻¹) * kG := by group
      _ = g * b * kG := by rw [hkb]
      _ = h.aG * (g * kG) := by rw [hb]; group
  · calc g * kG * h.z * (g * kG)⁻¹ = g * (kG * h.z * kG⁻¹) * g⁻¹ := by group
      _ = w := by rw [hkz, hg]

abbrev NWG : Subgroup G := h.IG ⊓ Subgroup.normalizer (h.WG : Set G)

theorem exists_normalizer_conj_z {w : G} (hwW : w ∈ h.WG) (hwX : w ∈ h.X0G)
    (hz : IsConj h.z w) (ha : IsConj h.aG (w * h.aG)) : ∃ n ∈ h.NWG, n * h.z * n⁻¹ = w := by
  haveI := h.finite
  obtain ⟨i, hi, hiz⟩ := h.exists_conj_of_typeAB hwX hz ha
  have hS0I : h.S0G ≤ h.IG := fun x hx => (Subgroup.mem_inf.1 (h.S0G_le_X0G hx)).2
  have hWI : h.WG ≤ h.IG := fun x hx => (Subgroup.mem_inf.1 (h.WG_le_X0G hx)).2
  let S : Sylow 2 h.IG := Sylow.ofCard _ h.card_sylow_I
  have hS : ((S : Subgroup h.IG)) = h.S0G.subgroupOf h.IG := Sylow.coe_ofCard _ _
  have hWS : h.WG.subgroupOf h.IG ≤ (S : Subgroup h.IG) := by
    rw [hS]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (h.WG_le_S0G (Subgroup.mem_subgroupOf.1 hx))
  have hweak : ∀ y : h.IG, (∀ a ∈ h.WG.subgroupOf h.IG, y * a * y⁻¹ ∈ (S : Subgroup h.IG)) →
      ∀ a ∈ h.WG.subgroupOf h.IG, y * a * y⁻¹ ∈ h.WG.subgroupOf h.IG := by
    intro y hy a ha
    have h1 := hy a ha
    rw [hS] at h1
    have h2 : ((y * a * y⁻¹ : h.IG) : G) ∈ h.X0G := h.S0G_le_X0G (Subgroup.mem_subgroupOf.1 h1)
    refine Subgroup.mem_subgroupOf.2 ?_
    have e : ((y * a * y⁻¹ : h.IG) : G) = (y : G) * a * (y : G)⁻¹ := rfl
    rw [e] at h2 ⊢
    exact h.conj_mem_WG y.2 (Subgroup.mem_subgroupOf.1 ha) h2
  have hab : ∀ a ∈ h.WG.subgroupOf h.IG, ∀ b ∈ h.WG.subgroupOf h.IG, a * b = b * a :=
    fun a ha b hb => Subtype.ext (h.WG_comm (Subgroup.mem_subgroupOf.1 ha)
      (Subgroup.mem_subgroupOf.1 hb))
  have hzW : (⟨h.z, h.z_mem_IG⟩ : h.IG) ∈ h.WG.subgroupOf h.IG :=
    Subgroup.mem_subgroupOf.2 h.z_mem_WG
  have hiW : (⟨i, hi⟩ : h.IG) * ⟨h.z, h.z_mem_IG⟩ * (⟨i, hi⟩ : h.IG)⁻¹ ∈
      h.WG.subgroupOf h.IG := by
    refine Subgroup.mem_subgroupOf.2 ?_
    show i * h.z * i⁻¹ ∈ h.WG
    rw [hiz]
    exact hwW
  obtain ⟨n, hn, hnz⟩ := exists_normalizer_conj_of_weakly_closed S hWS hab hweak hzW hiW
  refine ⟨n, Subgroup.mem_inf.2 ⟨n.2, ?_⟩, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxI := hWI hx
      have := (Subgroup.mem_normalizer_iff.1 hn ⟨x, hxI⟩).1 (Subgroup.mem_subgroupOf.2 hx)
      exact Subgroup.mem_subgroupOf.1 this
    · intro hx
      have hxI : x ∈ h.IG := by
        have h1 := hWI hx
        have e : x = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * n := by group
        rw [e]
        exact h.IG.mul_mem (h.IG.mul_mem (h.IG.inv_mem n.2) h1) n.2
      have := (Subgroup.mem_normalizer_iff.1 hn ⟨x, hxI⟩).2 (Subgroup.mem_subgroupOf.2 hx)
      exact Subgroup.mem_subgroupOf.1 this
  · exact (congrArg Subtype.val hnz).trans hiz

theorem X0G_le_normalizer : h.X0G ≤ Subgroup.normalizer (h.WG : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  have hxI : x ∈ h.IG := (Subgroup.mem_inf.1 hx).2
  intro w
  constructor
  · intro hw
    exact h.conj_mem_WG hxI hw (h.X0G.mul_mem (h.X0G.mul_mem hx (h.WG_le_X0G hw))
      (h.X0G.inv_mem hx))
  · intro hw
    have hwX : w ∈ h.X0G := by
      have h1 := h.WG_le_X0G hw
      have e : w = x⁻¹ * (x * w * x⁻¹) * x := by group
      rw [e]
      exact h.X0G.mul_mem (h.X0G.mul_mem (h.X0G.inv_mem hx) h1) hx
    have := h.conj_mem_WG (h.IG.inv_mem hxI) hw (by
      have e : x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = w := by group
      rw [e]
      exact hwX)
    have e : x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = w := by group
    rwa [e] at this

theorem card_typeAB_WG :
    Nat.card {w : h.WG // IsConj h.z (w : G) ∧ IsConj h.aG ((w : G) * h.aG)} = 15 := by
  rw [← card_typeAB_W]
  refine (Nat.card_congr ((h.liftEquiv (subW wWords)).subtypeEquiv fun y => ?_)).symm
  have hx : ((h.φ.symm y : h.H) : G) ∈ h.X0G := h.WG_le_X0G (h.φ_symm_mem_liftG y.2)
  have e : h.φ ⟨((h.φ.symm y : h.H) : G), (Subgroup.mem_inf.1 hx).1⟩ = (y : Cr) := by
    have : (⟨((h.φ.symm y : h.H) : G), (Subgroup.mem_inf.1 hx).1⟩ : h.H) = h.φ.symm y := rfl
    rw [this, MulEquiv.apply_symm_apply]
  show TypeAB (y : Cr) ↔ IsConj h.z ((h.φ.symm y : h.H) : G) ∧
    IsConj h.aG (((h.φ.symm y : h.H) : G) * h.aG)
  rw [h.typeABG_iff hx, e]

theorem card_normalizer_WG : Nat.card h.NWG = 41287680 := by
  haveI := h.finite
  letI := conjActG h.NWG
  have hX0N : h.X0G ≤ h.NWG := fun x hx =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, h.X0G_le_normalizer hx⟩
  have horb : MulAction.orbit h.NWG h.z =
      {w | w ∈ h.WG ∧ IsConj h.z w ∧ IsConj h.aG (w * h.aG)} := by
    ext w
    constructor
    · rintro ⟨n, rfl⟩
      have hnN := (Subgroup.mem_inf.1 n.2).2
      have hnI : (n : G) ∈ h.IG := (Subgroup.mem_inf.1 n.2).1
      have hmem : (n : G) * h.z * (n : G)⁻¹ ∈ h.WG :=
        (Subgroup.mem_normalizer_iff.1 hnN h.z).1 h.z_mem_WG
      have hzAB : IsConj h.z h.z ∧ IsConj h.aG (h.z * h.aG) :=
        ⟨IsConj.refl _, h.isConj_aG_z_mul⟩
      have hia : (n : G) * h.aG * (n : G)⁻¹ = h.aG := by
        rw [Subgroup.mem_centralizer_singleton_iff.1 hnI, mul_inv_cancel_right]
      refine ⟨hmem, ?_, ?_⟩
      · exact isConj_iff.2 ⟨n, rfl⟩
      · have e : (n : G) * h.z * (n : G)⁻¹ * h.aG = (n : G) * (h.z * h.aG) * (n : G)⁻¹ := by
          calc (n : G) * h.z * (n : G)⁻¹ * h.aG =
              (n : G) * h.z * (n : G)⁻¹ * ((n : G) * h.aG * (n : G)⁻¹) := by rw [hia]
            _ = (n : G) * (h.z * h.aG) * (n : G)⁻¹ := by group
        show IsConj h.aG ((n : G) * h.z * (n : G)⁻¹ * h.aG)
        rw [e, isConj_conj_right]
        exact hzAB.2
    · rintro ⟨hwW, hz, ha⟩
      obtain ⟨n, hn, hnz⟩ := h.exists_normalizer_conj_z hwW (h.WG_le_X0G hwW) hz ha
      exact ⟨⟨n, hn⟩, hnz⟩
  have hstab : MulAction.stabilizer h.NWG h.z = h.X0G.subgroupOf h.NWG := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change (n : G) * h.z * (n : G)⁻¹ = h.z ↔ (n : G) ∈ h.X0G
    constructor
    · intro e
      refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_inf.1 n.2).1⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (n : G) * h.z = (n : G) * h.z * (n : G)⁻¹ * (n : G) := by group
        _ = h.z * (n : G) := by rw [e]
    · intro hn
      rw [Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hn).1,
        mul_inv_cancel_right]
  have hcardorb : Nat.card (MulAction.orbit h.NWG h.z) = 15 := by
    rw [horb, ← h.card_typeAB_WG]
    exact Nat.card_congr
      { toFun := fun w => ⟨⟨w.1, w.2.1⟩, w.2.2⟩
        invFun := fun w => ⟨w.1.1, w.1.2, w.2⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
  have hcardstab : Nat.card (MulAction.stabilizer h.NWG h.z) = 2752512 := by
    rw [hstab, card_subgroupOf_eq hX0N, h.card_X0G]
  have hidx : (MulAction.stabilizer h.NWG h.z).index = 15 := by
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hcardorb]
  have := (MulAction.stabilizer h.NWG h.z).index_mul_card
  rw [hidx, hcardstab] at this
  omega

end Co2CentHyp

end CFSG.RankThree.Co2
