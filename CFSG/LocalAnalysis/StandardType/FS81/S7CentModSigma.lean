module

public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
import CFSG.LocalAnalysis.StandardType.FS81.S7ModTransfer
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped commutatorElement Pointwise

theorem mem_sup_of_centralizes_mod {G : Type} [Group G] [Finite G] {H U L P J D : Subgroup G}
    [(U.subgroupOf H).Normal] {σ b : G} (hUH : U ≤ H) (hU : IsPGroup 2 U) (hLH : L ≤ H)
    (hLU : ∀ x ∈ L, x ∈ U → x = 1) (hlev : E7LeviData L σ b P J D)
    (hmem : ∀ g ∈ H, g * b * g⁻¹ ∈ L ⊔ U → g ∈ L ⊔ U)
    {x : G} (hxH : x ∈ H) (hxP : ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ U) :
    x ∈ Subgroup.zpowers σ ⊔ U := by
  have hHnorm : H ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mp inferInstance
  have hUn : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U := fun h hh u hu =>
    (Subgroup.mem_normalizer_iff.mp (hHnorm hh) u).mp hu
  have hσH : σ ∈ H := hLH (hlev.P_le hlev.σ_mem)
  have hDL : D ≤ L := hlev.D_le.trans hlev.J_le
  have hDH : D ≤ H := hDL.trans hLH
  have hbL : b ∈ L := hDL hlev.b_mem
  let T : Subgroup G :=
    { carrier := {y | y ∈ H ∧ ∀ z ∈ P, ⁅y, z⁆ ∈ U}
      mul_mem' := by
        rintro a b ⟨haH, haP⟩ ⟨hbH, hbP⟩
        refine ⟨H.mul_mem haH hbH, fun z hz => ?_⟩
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact U.mul_mem (hUn a haH ⁅b, z⁆ (hbP z hz)) (haP z hz)
      one_mem' := ⟨H.one_mem, fun z _ => by simp⟩
      inv_mem' := by
        rintro a ⟨haH, haP⟩
        refine ⟨H.inv_mem haH, fun z hz => ?_⟩
        rw [commutatorElement_inv_left]
        have hza : ⁅z, a⁆ ∈ U := by
          have h := U.inv_mem (haP z hz)
          rwa [commutatorElement_inv] at h
        simpa using hUn a⁻¹ (H.inv_mem haH) ⁅z, a⁆ hza }
  let T₀ : Subgroup G := Subgroup.zpowers σ ⊔ U
  have hzT : Subgroup.zpowers σ ≤ T :=
    Subgroup.zpowers_le.mpr ⟨hσH, fun z hz => by
      have hcomm : Commute σ z := (hlev.P_cent z hz).symm
      rw [hcomm.commutator_eq]
      exact U.one_mem⟩
  have hUT : U ≤ T := by
    intro u hu
    refine ⟨hUH hu, fun z hz => ?_⟩
    have hzH : z ∈ H := hLH (hlev.P_le hz)
    have h := U.mul_mem hu (hUn z hzH u⁻¹ (U.inv_mem hu))
    simpa only [commutatorElement_def, mul_assoc] using h
  have hT0T : T₀ ≤ T := by
    show Subgroup.zpowers σ ⊔ U ≤ T
    exact sup_le hzT hUT
  have hTH : T ≤ H := fun _ hy => hy.1
  have hUT0 : U ≤ T₀ := le_sup_right
  have hT0p : IsPGroup 2 T₀ := by
    have hzN : Subgroup.zpowers σ ≤ Subgroup.normalizer (U : Set G) :=
      (Subgroup.zpowers_le.mpr hσH).trans hHnorm
    have hzp2 : IsPGroup 2 (Subgroup.zpowers σ) :=
      hlev.P_two.to_le (Subgroup.zpowers_le.mpr hlev.σ_mem)
    show IsPGroup 2 ↥(Subgroup.zpowers σ ⊔ U)
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_left' hU hzp2 hzN
  have hconj_map : ∀ g ∈ T, T₀.map (MulAut.conj g : G →* G) ≤ T₀ := by
    intro g hg
    have hgH : g ∈ H := hg.1
    have hgP : ∀ z ∈ P, ⁅g, z⁆ ∈ U := hg.2
    have hmapU : U.map (MulAut.conj g : G →* G) ≤ U := by
      rw [Subgroup.map_le_iff_le_comap]
      intro u hu
      show MulAut.conj g u ∈ U
      rw [MulAut.conj_apply]
      exact hUn g hgH u hu
    have hmapZ : (Subgroup.zpowers σ).map (MulAut.conj g : G →* G) ≤ T₀ := by
      rw [MonoidHom.map_zpowers]
      apply Subgroup.zpowers_le.mpr
      show MulAut.conj g σ ∈ T₀
      rw [conj_eq_commutatorElement_mul]
      exact T₀.mul_mem (Subgroup.mem_sup_right (hgP σ hlev.σ_mem))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers σ))
    show (Subgroup.zpowers σ ⊔ U).map (MulAut.conj g : G →* G) ≤ T₀
    rw [Subgroup.map_sup]
    exact sup_le hmapZ (hmapU.trans le_sup_right)
  have hconj_mem : ∀ g ∈ T, ∀ t ∈ T₀, g * t * g⁻¹ ∈ T₀ := by
    intro g hg t ht
    have h := hconj_map g hg (Subgroup.mem_map_of_mem (MulAut.conj g : G →* G) ht)
    change g * t * g⁻¹ ∈ T₀ at h
    exact h
  have hTN : T ≤ Subgroup.normalizer (T₀ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      exact hconj_mem g hg t ht
    · intro ht
      have h := hconj_mem g⁻¹ (T.inv_mem hg) (g * t * g⁻¹) ht
      simpa [mul_assoc] using h
  have hDP : D ≤ Subgroup.normalizer (P : Set G) := hlev.D_norm
  have hconjT : ∀ e ∈ D, ∀ y ∈ T, e * y * e⁻¹ ∈ T := by
    intro e he y hy
    refine ⟨H.mul_mem (H.mul_mem (hDH he) hy.1) (H.inv_mem (hDH he)), fun z hz => ?_⟩
    have hz' : e⁻¹ * z * e ∈ P := by
      have h := (Subgroup.mem_normalizer_iff.mp (hDP (D.inv_mem he)) z).mp hz
      simpa using h
    have hcomm : ⁅e * y * e⁻¹, z⁆ = e * ⁅y, e⁻¹ * z * e⁆ * e⁻¹ := by
      have h := conjugate_commutatorElement (g₁ := y) (g₂ := e⁻¹ * z * e) (g₃ := e)
      simpa [mul_assoc] using h.symm
    rw [hcomm]
    exact hUn e (hDH he) _ (hy.2 _ hz')
  have hDT : D ≤ Subgroup.normalizer (T : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hconjT e he y hy
    · intro hy
      have h := hconjT e⁻¹ (D.inv_mem he) (e * y * e⁻¹) hy
      simpa [mul_assoc] using h
  have hDT0 : D ≤ Subgroup.normalizer (T₀ : Set G) := by
    have hconjT0 : ∀ e ∈ D, T₀.map (MulAut.conj e : G →* G) ≤ T₀ := by
      intro e he
      have heH : e ∈ H := hDH he
      have heσ : e * σ = σ * e := hlev.J_cent e (hlev.D_le he)
      have hmapU : U.map (MulAut.conj e : G →* G) ≤ U := by
        rw [Subgroup.map_le_iff_le_comap]
        intro u hu
        show MulAut.conj e u ∈ U
        rw [MulAut.conj_apply]
        exact hUn e heH u hu
      have hmapZ : (Subgroup.zpowers σ).map (MulAut.conj e : G →* G) ≤
          Subgroup.zpowers σ := by
        rw [MonoidHom.map_zpowers]
        apply Subgroup.zpowers_le.mpr
        show MulAut.conj e σ ∈ Subgroup.zpowers σ
        rw [MulAut.conj_apply, heσ]
        simp
      show (Subgroup.zpowers σ ⊔ U).map (MulAut.conj e : G →* G) ≤ T₀
      rw [Subgroup.map_sup]
      exact sup_le (hmapZ.trans le_sup_left) (hmapU.trans le_sup_right)
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have h := hconjT0 d hd (Subgroup.mem_map_of_mem (MulAut.conj d : G →* G) ht)
      change d * t * d⁻¹ ∈ T₀ at h
      exact h
    · intro ht
      have h := hconjT0 d⁻¹ (D.inv_mem hd)
        (Subgroup.mem_map_of_mem (MulAut.conj d⁻¹ : G →* G) ht)
      change d⁻¹ * (d * t * d⁻¹) * (d⁻¹)⁻¹ ∈ T₀ at h
      simpa [mul_assoc] using h
  have hDU : ∀ d ∈ D, d ∈ U → d = 1 := fun d hd hdU => hLU d (hDL hd) hdU
  have hC : ∀ y ∈ T, y * b * y⁻¹ * b⁻¹ ∈ U → y ∈ T₀ := by
    intro y hy hyb
    have hybLU : y * b * y⁻¹ ∈ L ⊔ U := by
      have hconjb : y * b * y⁻¹ = ⁅y, b⁆ * b := conj_eq_commutatorElement_mul
      rw [hconjb]
      exact (L ⊔ U).mul_mem (Subgroup.mem_sup_right hyb) (Subgroup.mem_sup_left hbL)
    have hyLU : y ∈ L ⊔ U := hmem y hy.1 hybLU
    have hLnorm : L ≤ Subgroup.normalizer (U : Set G) := hLH.trans hHnorm
    have hcoe : (↑(L ⊔ U) : Set G) = (L : Set G) * (U : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right L U hLnorm
    change y ∈ (↑(L ⊔ U) : Set G) at hyLU
    rw [hcoe] at hyLU
    obtain ⟨l, hlL, u, huU, hlu⟩ := hyLU
    have hlz : l ∈ Subgroup.zpowers σ := by
      apply hlev.centP l hlL
      intro z hz
      have hzH : z ∈ H := hLH (hlev.P_le hz)
      have hzL : z ∈ L := hlev.P_le hz
      have hu'U : u * z * u⁻¹ * z⁻¹ ∈ U := by
        have h := hUn z hzH u⁻¹ (U.inv_mem huU)
        simpa only [mul_assoc] using U.mul_mem huU h
      have hlulU : l * (u * z * u⁻¹ * z⁻¹) * l⁻¹ ∈ U :=
        hUn l (hLH hlL) _ hu'U
      have hyzU : ⁅y, z⁆ ∈ U := hy.2 z hz
      have hident : ⁅l, z⁆ =
          (l * (u * z * u⁻¹ * z⁻¹) * l⁻¹)⁻¹ * ⁅y, z⁆ := by
        rw [← hlu]
        simp only [commutatorElement_def]
        group
      have hLmem : ⁅l, z⁆ ∈ L := by
        have h := L.mul_mem (L.mul_mem hlL hzL)
          (L.mul_mem (L.inv_mem hlL) (L.inv_mem hzL))
        simpa only [commutatorElement_def, mul_assoc] using h
      have hUmem : ⁅l, z⁆ ∈ U := by
        rw [hident]
        exact U.mul_mem (U.inv_mem hlulU) hyzU
      exact commutatorElement_eq_one_iff_mul_comm.mp (hLU ⁅l, z⁆ hLmem hUmem)
    rw [← hlu]
    exact T₀.mul_mem (Subgroup.mem_sup_left hlz) (Subgroup.mem_sup_right huU)
  have hTle : T ≤ T₀ :=
    le_of_centralizer_le_l3Two_mod hUT0 hT0p hT0T hTH hTN hDH hDU hDT hDT0
      hlev.D_SL hlev.b_mem hlev.b_ord hC
  exact hTle ⟨hxH, fun y hy => by
    simpa only [commutatorElement_def] using hxP y hy⟩

end CFSG.StandardType.FrameRoute.FS81

end
