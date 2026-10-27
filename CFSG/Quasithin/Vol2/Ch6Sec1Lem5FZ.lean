module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FM

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem borelL_le_normalizer_thompsonJ_ch615 (c : Cx615C G T M L V H n) :
    borelL T L ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
  have h := c.hyp
  set R := (T ⊓ L) ⊔ pCoreOf 2 (L ⊔ T) with hR
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T :=
    F7.isSylowTwoOf_pCoreOf_le (h.toHyp5_0_1.isSylowTwoOf le_sup_right)
  have hRT : R ≤ T := sup_le inf_le_left hQT
  have hJ := B6.thompsonJ_eq_of_le c.thompsonJ_le_ch615 hRT
  intro b hb
  have hbR : b ∈ Subgroup.normalizer (R : Set G) := by
    have h1 : b ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := hb.2
    have h2 : b ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
      le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hb.1)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_sup, h1, h2]
  have hc : B6.conjSub b (thompsonJ R) = thompsonJ R := by
    rw [← B6.thompsonJ_conjSub, B6.conjSub_eq_self hbR]
  rw [← hJ]
  refine mem_normalizer_of_conj_mem_l32_ch615 fun y hy => ?_
  rw [← hc, B6.mem_conjSub]
  simpa [mul_assoc] using hy

theorem conj_mem_autI_thompsonJ_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) :
    ∀ y ∈ autI hU (borelL T L), ∀ j ∈ autI hU (thompsonJ T),
      y * j * y⁻¹ ∈ autI hU (thompsonJ T) :=
  C124.autI_conj_mem hU c.borelL_le_normalizer_thompsonJ_ch615

theorem autI_thompsonJ_le_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) :
    autI hU (thompsonJ T) ≤ Subgroup.closure {y | ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      IsFFStarOffender (autI hU T) (autI hU A) ∧ y ∈ autI hU A} := by
  have hTX : T ≤ borelL T L ⊔ H := c.hH.1.1.trans le_sup_right
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUT : UX615 T L H ≤ T :=
    c.U_red_ch615.1.trans (F7.isSylowTwoOf_pCoreOf_le (c.hyp.toHyp5_0_1.isSylowTwoOf hTX))
  refine autI_le_of_le_preI615 (iSup₂_le fun A hA => fun a ha => ?_)
  have haN : a ∈ Subgroup.normalizer (UX615 T L H : Set G) := hXN (hTX (hA.1 ha))
  refine mem_preI615 haN ?_
  by_cases hAC : A ≤ Subgroup.centralizer (UX615 T L H : Set G)
  · rw [(convI_eq_one_iff hU _).mpr (hAC ha)]
    exact Subgroup.one_mem _
  · have hoff := offenderImages_isFFStarOffender hU hUT (hTX.trans hXN) ⟨A, ⟨hA, hAC⟩, rfl⟩
    exact Subgroup.subset_closure ⟨A, hA, hoff, convI_mem_autI hU ha haN⟩

theorem exists_of_fix_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    {w : IntMod (UX615 T L H) hU} (hw1 : w ≠ 1) (hwT : ∀ s ∈ autI hU T, s w = w)
    (hwX : w ∈ commV (autI hU (borelL T L ⊔ H)))
    {d : MulAut (IntMod (UX615 T L H) hU)} (hdD : d ∈ autI hU D) (hd1 : d ≠ 1)
    {G₁ : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hG₁X : G₁ ≤ autI hU (borelL T L ⊔ H))
    (hs₁ : IsSimpleGroup ↥G₁) (hns₁ : ¬ Group.IsSolvable ↥G₁) (hdF : d ∈ G₁)
    (hG₁w : ∀ g ∈ G₁, g w = w) :
    ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅UX615 T L H, borelL T L ⊔ H⁆,
      z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
      ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.normalizer ((borelL T L : Subgroup G) : Set G) := by
  classical
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hTX : T ≤ borelL T L ⊔ H := c.hH.1.1.trans le_sup_right
  have hUT : UX615 T L H ≤ T :=
    c.U_red_ch615.1.trans (F7.isSylowTwoOf_pCoreOf_le (c.hyp.toHyp5_0_1.isSylowTwoOf hTX))
  set z := w.val with hz
  have hzU : z ∈ UX615 T L H := w.val_mem
  have hfix : ∀ g (hg : g ∈ Subgroup.normalizer (UX615 T L H : Set G)),
      convI hU ⟨g, hg⟩ w = w → g * z * g⁻¹ = z := fun g hg h => by
    have := congrArg IntMod.val h
    rwa [convI_apply_val] at this
  have hzC : z ∈ Subgroup.centralizer (T : Set G) := Subgroup.mem_centralizer_iff.mpr fun s hs => by
    have hsN := hXN (hTX hs)
    have h1 := hfix s hsN (hwT _ (convI_mem_autI hU hs hsN))
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [h1]
  have hz2 : z ^ 2 = 1 := by simpa [pow_two] using hU.2 z hzU
  have hzZ : z ∈ quasithinOmegaOneCenter T :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hUT hzU, hzC, hz2⟩
  have hz1 : z ≠ 1 := fun h => hw1 (IntMod.val_injective (by rw [← hz, h, IntMod.val_one]))
  have hzc : z ∈ ⁅UX615 T L H, borelL T L ⊔ H⁆ := val_mem_commutator_ch615 hU hwX
  obtain ⟨⟨dG, hdN⟩, hdGD, rfl⟩ := (mem_autI hU).mp hdD
  have hdG1 : dG ≠ 1 := fun h => hd1 (by
    have : (⟨dG, hdN⟩ : ↥(Subgroup.normalizer (UX615 T L H : Set G))) = 1 := Subtype.ext h
    rw [this, map_one])
  have hdGodd : Odd (orderOf dG) := Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard D hdGD)
  refine ⟨z, ⟨hzZ, hzc⟩, hz1, ⟨dG, hD.1 hdGD, hdGodd, hdG1, hfix dG hdN (hG₁w _ hdF)⟩, ?_⟩
  intro hle
  have hsub : G₁ ≤ autI hU ((borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G)) := by
    intro g hg
    obtain ⟨⟨x, hxN⟩, hxX, rfl⟩ := (mem_autI hU).mp (hG₁X hg)
    have hxz := hfix x hxN (hG₁w _ hg)
    have hxc : x ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc x * z = x * z * x⁻¹ * x := by group
          _ = z * x := by rw [hxz])
    exact (mem_autI hU).mpr ⟨⟨x, hxN⟩, ⟨hxX, hxc⟩, rfl⟩
  have hBn := C124.autI_conj_mem hU hle
  have hn : ((autI hU (borelL T L) ⊓ G₁).subgroupOf G₁).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hBn _ (hsub g.2) _ hx.1, G₁.mul_mem (G₁.mul_mem g.2 hx.2) (G₁.inv_mem g.2)⟩⟩
  rcases hn.eq_bot_or_eq_top with hb | ht
  · have hdB : convI hU ⟨dG, hdN⟩ ∈ autI hU (borelL T L) := convI_mem_autI hU (hD.1 hdGD) hdN
    have h1 : (⟨_, hdF⟩ : ↥G₁) ∈ (autI hU (borelL T L) ⊓ G₁).subgroupOf G₁ := ⟨hdB, hdF⟩
    rw [hb, Subgroup.mem_bot] at h1
    exact hd1 (congrArg Subtype.val h1)
  · have hG₁B : G₁ ≤ autI hU (borelL T L ⊔ T) := fun g hg => by
      have h1 : (⟨g, hg⟩ : ↥G₁) ∈ (autI hU (borelL T L) ⊓ G₁).subgroupOf G₁ := by
        rw [ht]
        exact Subgroup.mem_top _
      exact autI_mono hU le_sup_left h1.1
    have := c.isSolvable_autI_ch615 hU
    exact hns₁ (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hG₁B)
      (Subgroup.inclusion_injective _))

end Cx615C

omit [Finite G] in
theorem autI_oTwoUpper_eq_bot_ch615 (hU : IsElemAbelian 2 (UX615 T L H))
    {Q : Subgroup (MulAut (IntMod (UX615 T L H) hU))}
    (hQ : IsPGroup 2 ↥Q) (hle : autI hU (oTwoUpper H) ≤ Q) : autI hU (oTwoUpper H) = ⊥ := by
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  rw [eq_bot_iff]
  refine autI_le_of_le_preI615 ((Subgroup.closure_le _).mpr fun x hx => ?_)
  have hxN : x ∈ Subgroup.normalizer (UX615 T L H : Set G) := hXN (Subgroup.mem_sup_right hx.1)
  refine mem_preI615 hxN ?_
  have hxK : convI hU ⟨x, hxN⟩ ∈ autI hU (oTwoUpper H) :=
    convI_mem_autI hU (Subgroup.subset_closure hx) hxN
  have hodd : Odd (orderOf (convI hU ⟨x, hxN⟩)) := by
    refine Odd.of_dvd_nat hx.2 ?_
    exact (orderOf_map_dvd _ _).trans (by rw [Subgroup.orderOf_mk])
  rw [eq_one_of_odd_of_mem_l32_ch615 hQ (hle hxK) hodd]
  exact Subgroup.one_mem _


end CFSG.Quasithin.H13
