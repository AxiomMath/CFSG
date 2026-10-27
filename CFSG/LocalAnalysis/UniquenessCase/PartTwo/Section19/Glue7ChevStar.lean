module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Chev2StarDef
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rh
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FermatNotDvd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet mem_uniqueSet_of_le normalizer_le_of_mem_uniqueSet)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_M_of_forall_conj_mem (D : Data G) {E : Subgroup G} (hEU : E ∈ uniqueSet D.M)
    {g : G} (hg : ∀ e ∈ E, g⁻¹ * e * g ∈ D.M) : g ∈ D.M := by
  have hle : E ≤ D.M.map (MulAut.conj g).toMonoidHom := fun e he =>
    ⟨g⁻¹ * e * g, hg e he, by simp [MulAut.conj_apply, mul_assoc]⟩
  rw [← CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal]
  exact mem_normalizer_iff_map_conj_eq.mpr (hEU.2 g hle)

theorem mem_M_of_mem_sup_of_mem_centralizer (D : Data G) {K E : Subgroup G}
    (hE_NK : E ≤ normalizer (K : Set G)) (hEcomm : IsMulCommutative ↥E)
    (hEU : E ∈ uniqueSet D.M) (hZM : Zsub K ≤ D.M) {x : G} (hx : x ∈ K ⊔ E)
    (hxC : x ∈ centralizer (K : Set G)) : x ∈ D.M := by
  let X : Subgroup G := (K ⊔ E) ⊓ centralizer (K : Set G)
  have hKEcoe : ((K ⊔ E : Subgroup G) : Set G) = (K : Set G) * (E : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K E hE_NK
  have hcommZ : ∀ y ∈ X, ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Zsub K := by
    rintro y ⟨hyKE, hyC⟩ e he
    have hyKE' : y ∈ ((K ⊔ E : Subgroup G) : Set G) := hyKE
    rw [hKEcoe] at hyKE'
    obtain ⟨k, hk, e₁, he₁, hke⟩ := hyKE'
    have he₁e : e₁ * e = e * e₁ :=
      congrArg Subtype.val ((isMulCommutative_iff.mp hEcomm) ⟨e₁, he₁⟩ ⟨e, he⟩)
    have hcK : y * e * y⁻¹ * e⁻¹ ∈ K := by
      have hconj : e * k⁻¹ * e⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hE_NK he) k⁻¹).mp (K.inv_mem hk)
      have heq : y * e * y⁻¹ * e⁻¹ = k * (e * k⁻¹ * e⁻¹) := by
        rw [← hke]
        calc k * e₁ * e * (k * e₁)⁻¹ * e⁻¹ = k * (e₁ * e) * e₁⁻¹ * k⁻¹ * e⁻¹ := by group
          _ = k * (e * e₁) * e₁⁻¹ * k⁻¹ * e⁻¹ := by rw [he₁e]
          _ = k * (e * k⁻¹ * e⁻¹) := by group
      rw [heq]
      exact K.mul_mem hk hconj
    have hcC : y * e * y⁻¹ * e⁻¹ ∈ centralizer (K : Set G) := by
      have hey : e * y⁻¹ * e⁻¹ ∈ centralizer (K : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hk' : e⁻¹ * k * e⁻¹⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hE_NK (E.inv_mem he)) k).mp hk
        have hyk := Subgroup.mem_centralizer_iff.mp ((centralizer _).inv_mem hyC) _ hk'
        calc k * (e * y⁻¹ * e⁻¹) = e * ((e⁻¹ * k * e⁻¹⁻¹) * y⁻¹) * e⁻¹ := by group
          _ = e * (y⁻¹ * (e⁻¹ * k * e⁻¹⁻¹)) * e⁻¹ := by rw [hyk]
          _ = e * y⁻¹ * e⁻¹ * k := by group
      have hmul := (centralizer (K : Set G)).mul_mem hyC hey
      rwa [← mul_assoc, ← mul_assoc] at hmul
    rw [Zsub, CFSG.center_map_subtype_eq_inf_centralizer]
    exact ⟨hcK, hcC⟩
  let W : Subgroup G := E ⊔ Zsub K
  have hXNW : X ≤ normalizer (W : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun y hy w hw => ?_
    have hle : W ≤ W.comap (MulAut.conj y).toMonoidHom := by
      refine sup_le (fun e he => ?_) (fun z hz => ?_)
      · have hmem : (y * e * y⁻¹ * e⁻¹) * e ∈ W :=
          W.mul_mem (Subgroup.mem_sup_right (hcommZ y hy e he)) (Subgroup.mem_sup_left he)
        simpa [MulAut.conj_apply] using hmem
      · have hzy : z * y = y * z := Subgroup.mem_centralizer_iff.mp hy.2 z (Zsub_le K hz)
        have hmem : z ∈ W := Subgroup.mem_sup_right hz
        simpa [MulAut.conj_apply, ← hzy] using hmem
    exact hle hw
  have hWU : W ∈ uniqueSet D.M := mem_uniqueSet_of_le hEU le_sup_left (sup_le hEU.1 hZM)
  exact (hXNW.trans (normalizer_le_of_mem_uniqueSet D.maxLocal hWU)) ⟨hx, hxC⟩

theorem mem_M_of_mk_mem_map (D : Data G) {K E N : Subgroup G}
    (hE_NK : E ≤ normalizer (K : Set G)) (hEcomm : IsMulCommutative ↥E)
    (hEU : E ∈ uniqueSet D.M) (hZM : Zsub K ≤ D.M)
    (CK : Subgroup ↥N) [CK.Normal] (hCK : CK = (centralizer (K : Set G)).subgroupOf N)
    {b : ↥N} (hb : (b : G) ∈ K ⊔ E)
    (hπb : QuotientGroup.mk' CK b ∈ ((D.M ⊓ (K ⊔ E)).subgroupOf N).map (QuotientGroup.mk' CK)) :
    (b : G) ∈ D.M := by
  obtain ⟨m, hm, hmb⟩ := Subgroup.mem_map.mp hπb
  have hc : m⁻¹ * b ∈ CK := QuotientGroup.eq.mp hmb
  rw [hCK] at hc
  have hm' : (m : G) ∈ D.M ⊓ (K ⊔ E) := hm
  have hcM : (m : G)⁻¹ * b ∈ D.M :=
    mem_M_of_mem_sup_of_mem_centralizer D hE_NK hEcomm hEU hZM
      ((K ⊔ E).mul_mem ((K ⊔ E).inv_mem hm'.2) hb) hc
  rw [show (b : G) = m * ((m : G)⁻¹ * b) by group]
  exact D.M.mul_mem hm'.1 hcM

theorem le_M_of_isChev_quotient (hst : Inputs1719.Chev2StarGen) (D : Data G)
    {K E S N : Subgroup G} {r n : ℕ}
    (hKN : K ≤ N) (hEN : E ≤ N) (hNK : N ≤ normalizer (K : Set G))
    (hEcomm : IsMulCommutative ↥E) (hEU : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M)
    (hZM : Zsub K ≤ D.M) (hSK : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ K) K) (hSM : S ≤ D.M)
    (CK : Subgroup ↥N) [CK.Normal] (hCK : CK = (centralizer (K : Set G)).subgroupOf N)
    (hKs : IsSimpleGroup ↥((K.subgroupOf N).map (QuotientGroup.mk' CK)))
    (hKc : centralizer (((K.subgroupOf N).map (QuotientGroup.mk' CK) : Subgroup (↥N ⧸ CK)) :
      Set (↥N ⧸ CK)) = ⊥)
    (hchev : IsChev ↥((K.subgroupOf N).map (QuotientGroup.mk' CK)) 2)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 ((S.subgroupOf N).map (QuotientGroup.mk' CK)) ⊤)
    (hr : r.Prime) (hr7 : 7 ≤ r) (hr13 : r ≠ 13) (hrn : r ∣ 2 ^ n - 1) (hn : Odd n)
    (hEc : Nat.card ↥((E.subgroupOf N).map (QuotientGroup.mk' CK)) = r)
    (hEp : Permutes ((E.subgroupOf N).map (QuotientGroup.mk' CK))
      ((S.subgroupOf N).map (QuotientGroup.mk' CK))) :
    K ≤ D.M := by
  let π : ↥N →* ↥N ⧸ CK := QuotientGroup.mk' CK
  let Kbar : Subgroup (↥N ⧸ CK) := (K.subgroupOf N).map π
  let Ebar : Subgroup (↥N ⧸ CK) := (E.subgroupOf N).map π
  let Tbar : Subgroup (↥N ⧸ CK) := (S.subgroupOf N).map π
  let Mbar : Subgroup (↥N ⧸ CK) := ((D.M ⊓ (K ⊔ E)).subgroupOf N).map π
  have hE_NK : E ≤ normalizer (K : Set G) := hEN.trans hNK
  have hlift : ∀ b : ↥N, (b : G) ∈ K ⊔ E → π b ∈ Mbar → (b : G) ∈ D.M := fun b hb hπb =>
    mem_M_of_mk_mem_map D hE_NK hEcomm hEU hZM CK hCK hb hπb
  have hKbn : Kbar.Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr hNK).map π
      (QuotientGroup.mk'_surjective CK)
  have hFermat : ∀ k : ℕ, r ≠ 2 ^ k + 1 := fun k hk =>
    Inputs1719.not_dvd_two_pow_sub_one_of_eq_two_pow_add_one hr hk hn hrn
  have hEM : Ebar ≤ Mbar := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hEU.1 hx, Subgroup.mem_sup_right hx⟩)
  have hTKM : Tbar ⊓ Kbar ≤ Mbar := by
    let φ : ↥K →* ↥Kbar :=
      MonoidHom.codRestrict (π.comp (Subgroup.inclusion hKN)) Kbar
        (fun k => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr k.2))
    have hφ_surj : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    have hSKsub : CFSG.ABGLocalTools.IsSylowOf 2 ((S ⊓ K).subgroupOf K) ⊤ := by
      rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff K, Subgroup.map_top,
        Subgroup.range_subtype, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
      exact hSK
    let Ubar : Subgroup (↥N ⧸ CK) := (((S ⊓ K).subgroupOf K).map φ).map Kbar.subtype
    have hUsyl : CFSG.ABGLocalTools.IsSylowOf 2 Ubar Kbar := by
      have h1 := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff Kbar).mpr
        (uc22p22r_isSylowOf_map_top hφ_surj hSKsub)
      rwa [Subgroup.map_top, Subgroup.range_subtype] at h1
    have hUle : Ubar ≤ Tbar ⊓ Kbar := by
      rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hb).1), (φ b).2⟩
    have hUM : Ubar ≤ Mbar := by
      rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      have hbSK : (b : G) ∈ S ⊓ K := Subgroup.mem_subgroupOf.mp hb
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mpr ⟨hSM hbSK.1, Subgroup.mem_sup_left hbSK.2⟩))
    rw [hUsyl.eq_of_le hUle inf_le_right (hT.isPGroup.to_le inf_le_left)]
    exact hUM
  have hstar : ∀ y ∈ Kbar ⊔ Ebar, (∀ x ∈ Ebar, y⁻¹ * x * y ∈ Mbar) → y ∈ Mbar := by
    intro y hy hyE
    have hKE : Kbar ⊔ Ebar = ((K ⊔ E).subgroupOf N).map π := by
      rw [Subgroup.subgroupOf_sup hKN hEN, Subgroup.map_sup]
    rw [hKE] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    have hy₀KE : (y₀ : G) ∈ K ⊔ E := Subgroup.mem_subgroupOf.mp hy₀
    have hy₀M : (y₀ : G) ∈ D.M := by
      refine mem_M_of_forall_conj_mem D hEU fun e he => ?_
      let e' : ↥N := ⟨e, hEN he⟩
      have h1 : π (y₀⁻¹ * e' * y₀) ∈ Mbar := by
        simpa only [map_mul, map_inv] using
          hyE (π e') (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr he))
      exact hlift (y₀⁻¹ * e' * y₀) ((K ⊔ E).mul_mem
        ((K ⊔ E).mul_mem ((K ⊔ E).inv_mem hy₀KE) (Subgroup.mem_sup_right he)) hy₀KE) h1
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨hy₀M, hy₀KE⟩))
  have hKM : Kbar ≤ Mbar := hst (↥N ⧸ CK) Kbar Ebar Tbar Mbar r hKbn hKs hchev hKc hT hr hr7
    hr13 hFermat hEc hEp hTKM hEM hstar
  intro k hk
  exact hlift ⟨k, hKN hk⟩ (Subgroup.mem_sup_left hk)
    (hKM (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
