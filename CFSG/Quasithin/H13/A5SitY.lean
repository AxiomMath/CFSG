module

public import CFSG.Quasithin.H13.A5Sit
public import CFSG.Quasithin.H13.A5S1519

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5 (Hstar piQ piQ_eq_one_iff)

section General

variable {G : Type} [Group G]

theorem oTwoRes_oTwoRes (X : Subgroup G) : oTwoRes (oTwoRes X) = oTwoRes X := by
  refine le_antisymm (oTwoRes_le _) ?_
  rw [oTwoRes, Subgroup.closure_le]
  rintro y ⟨hy, m, hm, hym⟩
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hy, m, hm, hym⟩, m, hm, hym⟩

end General

structure A5SitY {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
    (S : A5Sit G T V V₁ V₃ L₁ H) (Y : Subgroup G) where
  Y_le_L1 : Y ≤ L₁
  normalizer_le : H ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (Y : Set G)
  oTwoRes_eq : oTwoRes Y = Y
  c : G
  c_mem : c ∈ Y
  c_cube : c ^ 3 = 1
  c_not_mem : c ∉ pCoreOf 2 Y
  decomp : ∀ x ∈ Y, x ∈ pCoreOf 2 Y ∨ c * c * x ∈ pCoreOf 2 Y ∨ c * x ∈ pCoreOf 2 Y

namespace A5SitY

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  {S : A5Sit G T V V₁ V₃ L₁ H} {Y : Subgroup G} (SY : A5SitY S Y)
include SY

theorem Y_le_H : Y ≤ H := SY.Y_le_L1.trans S.L1_le_H

theorem T_le_normalizer : T ≤ Subgroup.normalizer (Y : Set G) := fun _ ht =>
  SY.normalizer_le ⟨S.T_le_H ht, S.hF.T_normalizes_V ht⟩

theorem comm_V {v y : G} (hv : v ∈ V) (hy : y ∈ Y) : v * y * v⁻¹ * y⁻¹ ∈ pCoreOf 2 H :=
  S.comm_V_L1_mem_Q hv (SY.Y_le_L1 hy)

theorem piQ_c_cube : piQ H ⟨SY.c, SY.Y_le_H SY.c_mem⟩ ^ 3 = 1 := by
  rw [← map_pow, piQ_eq_one_iff]
  have : ((⟨SY.c, SY.Y_le_H SY.c_mem⟩ : ↥H) ^ 3 : ↥H) = 1 :=
    Subtype.ext (by simpa using SY.c_cube)
  rw [this]
  exact Subgroup.one_mem _

theorem oTwoRes_Y_sup {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQT : Q ≤ T) :
    oTwoRes (Y ⊔ Q) = Y := by
  apply le_antisymm
  · exact A5.Setting.oTwoRes_sup_le hQ (hQT.trans SY.T_le_normalizer)
  · conv_lhs => rw [← SY.oTwoRes_eq]
    rw [oTwoRes, Subgroup.closure_le]
    rintro y ⟨hy, m, hm, hym⟩
    exact Subgroup.subset_closure ⟨le_sup_left (a := Y) hy, m, hm, hym⟩

end A5SitY

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  (S : A5Sit G T V V₁ V₃ L₁ H)
include S

theorem oTwoRes_L1 : oTwoRes L₁ = L₁ := by
  rw [S.L1_eq]
  exact oTwoRes_oTwoRes _

theorem normalizer_le_L1 :
    H ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L₁ : Set G) := by
  intro x hx
  have h1 : Subgroup.zpowers x ≤
      Subgroup.normalizer ((S.L ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) :=
    F7.le_normalizer_inf (Subgroup.zpowers_le.mpr (S.NV_le hx.2))
      (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer (S.hF.H_normalizes_V₁ hx.1)))
  rw [S.L1_eq]
  exact A5.le_normalizer_oTwoRes_of_le_normalizer h1 (Subgroup.mem_zpowers x)

@[expose] def toA5SitY (c : G) (c_mem : c ∈ L₁) (c_cube : c ^ 3 = 1)
    (c_not_mem : c ∉ pCoreOf 2 L₁)
    (decomp : ∀ x ∈ L₁, x ∈ pCoreOf 2 L₁ ∨ c * c * x ∈ pCoreOf 2 L₁ ∨ c * x ∈ pCoreOf 2 L₁) :
    A5SitY S L₁ where
  Y_le_L1 := le_rfl
  normalizer_le := S.normalizer_le_L1
  oTwoRes_eq := S.oTwoRes_L1
  c := c
  c_mem := c_mem
  c_cube := c_cube
  c_not_mem := c_not_mem
  decomp := decomp

variable {Y : Subgroup G} (SY : A5SitY S Y)
include SY

theorem piQ_V_comm_Y {v y : G} (hv : v ∈ V) (hy : y ∈ Y) :
    piQ H ⟨v, S.V_le_H hv⟩ * piQ H ⟨y, SY.Y_le_H hy⟩ =
      piQ H ⟨y, SY.Y_le_H hy⟩ * piQ H ⟨v, S.V_le_H hv⟩ := by
  rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
    ← map_mul, piQ_eq_one_iff]
  exact SY.comm_V hv hy

theorem mem_normalizer_Y_of_mem_normalizer_sup {x : G}
    (hx : x ∈ Subgroup.normalizer ((Y ⊔ pCoreOf 2 H : Subgroup G) : Set G)) :
    x ∈ Subgroup.normalizer (Y : Set G) := by
  have := A5.le_normalizer_oTwoRes_of_le_normalizer (Subgroup.zpowers_le.mpr hx)
    (Subgroup.mem_zpowers x)
  rwa [SY.oTwoRes_Y_sup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) S.Q_le_T] at this

theorem mem_normalizer_Y_of_comm {g : G} (hg : g ∈ H)
    (hcomm : ∀ l (hl : l ∈ Y), piQ H ⟨g, hg⟩ * piQ H ⟨l, SY.Y_le_H hl⟩ =
      piQ H ⟨l, SY.Y_le_H hl⟩ * piQ H ⟨g, hg⟩) :
    g ∈ Subgroup.normalizer (Y : Set G) := by
  have hYH := SY.Y_le_H
  set K := Y ⊔ pCoreOf 2 H
  have key : ∀ h (hh : h ∈ H), (∀ l (hl : l ∈ Y), piQ H ⟨h, hh⟩ * piQ H ⟨l, hYH hl⟩ =
      piQ H ⟨l, hYH hl⟩ * piQ H ⟨h, hh⟩) → ∀ y ∈ K, h * y * h⁻¹ ∈ K := by
    intro h hh hc y hy
    have hmap : K.map (MulAut.conj h).toMonoidHom ≤ K := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨l, hl, rfl⟩
        have h1 := hc l hl
        rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← map_inv, ← map_inv, ← map_mul,
          ← map_mul, ← map_mul, piQ_eq_one_iff] at h1
        have h2 : (MulAut.conj h).toMonoidHom l = (h * l * h⁻¹ * l⁻¹) * l := by
          show h * l * h⁻¹ = _
          group
        rw [h2]
        exact Subgroup.mul_mem _ (le_sup_right (a := Y) h1) (le_sup_left (a := Y) hl)
      · rintro _ ⟨q, hq, rfl⟩
        exact le_sup_right (a := Y)
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) q).mp hq)
    exact hmap ⟨y, hy, rfl⟩
  have hginv : ∀ l (hl : l ∈ Y), piQ H ⟨g⁻¹, H.inv_mem hg⟩ * piQ H ⟨l, hYH hl⟩ =
      piQ H ⟨l, hYH hl⟩ * piQ H ⟨g⁻¹, H.inv_mem hg⟩ := by
    intro l hl
    have := hcomm l hl
    have e : piQ H ⟨g⁻¹, H.inv_mem hg⟩ = (piQ H ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e]
    calc (piQ H ⟨g, hg⟩)⁻¹ * piQ H ⟨l, hYH hl⟩ =
        (piQ H ⟨g, hg⟩)⁻¹ * (piQ H ⟨l, hYH hl⟩ * piQ H ⟨g, hg⟩) * (piQ H ⟨g, hg⟩)⁻¹ := by
          group
      _ = (piQ H ⟨g, hg⟩)⁻¹ * (piQ H ⟨g, hg⟩ * piQ H ⟨l, hYH hl⟩) * (piQ H ⟨g, hg⟩)⁻¹ := by
          rw [this]
      _ = piQ H ⟨l, hYH hl⟩ * (piQ H ⟨g, hg⟩)⁻¹ := by group
  have hgK : g ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key g hg hcomm y, fun hy => ?_⟩
    have := key g⁻¹ (H.inv_mem hg) hginv _ hy
    simpa [mul_assoc] using this
  exact S.mem_normalizer_Y_of_mem_normalizer_sup SY hgK

end A5Sit

end CFSG.Quasithin.H13
