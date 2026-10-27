module

public import CFSG.Quasithin.Vol2.Ch3T326P
public import CFSG.Quasithin.Vol2.Ch3T326U
public import CFSG.Quasithin.Vol2.Ch3T326W
public import CFSG.Quasithin.Vol2.Ch3T326X
public import CFSG.Quasithin.Vol2.Ch3T326H

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

section Abstract

variable {W : Type} [CommGroup W]

theorem commSub_top_map_of_normalizer {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ∀ u ∈ commSub ⊤ L, g u ∈ commSub ⊤ L := by
  intro u hu
  refine Subgroup.closure_induction (p := fun u _ => g u ∈ commSub ⊤ L) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨b, hb, w, -, rfl⟩
    have e : g (b w * w⁻¹) = (g * b * g⁻¹) (g w) * (g w)⁻¹ := by
      simp [MulAut.mul_apply]
    rw [e]
    exact Subgroup.subset_closure ⟨_, (Subgroup.mem_normalizer_iff.mp hg b).mp hb, _, trivial, rfl⟩
  · simp
  · intro a b _ _ ha hb
    rw [map_mul]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [map_inv]
    exact Subgroup.inv_mem _ ha

theorem stab_of_inner [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} (hD : D3Std M Mp T L V) (horb : orbSup T V = ⊤)
    (hMp : Mp = L ⊔ conjAutSub t L) (hVU : V ≤ commSub ⊤ L)
    (hUfix : ∀ u ∈ commSub ⊤ L, ∀ g ∈ conjAutSub t L, g u = u) {n : MulAut W} (hn : n ∈ T)
    (hnL : n ∈ Subgroup.normalizer (L : Set (MulAut W))) (hin : IsInnerOn L n) :
    V.map n.toMonoidHom = V := by
  obtain ⟨a, ha, hac⟩ := hin
  have haMp : a ∈ Mp := by
    rw [hMp]
    exact Subgroup.mem_sup_left ha
  have hnMp : n ∈ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    hD.hyp.Mp_normal (hD.hyp.sylow.1 hn)
  have hz : a⁻¹ * n ∈ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer haMp)) hnMp
  have hzU : ∀ u ∈ commSub ⊤ L, (a⁻¹ * n) u ∈ commSub ⊤ L := fun u hu => by
    rw [MulAut.mul_apply]
    exact commSub_top_map_of_normalizer
      (Subgroup.inv_mem _ (Subgroup.le_normalizer ha)) _ (commSub_top_map_of_normalizer hnL u hu)
  exact map_eq_self_of_inner hD horb hMp hVU hUfix hn hz hzU hac ha (by group)

theorem mem_stabSub_of_map_eq' {V : Subgroup W} {g : MulAut W} (h : V.map g.toMonoidHom = V) :
    g ∈ stabSub V :=
  CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq h

end Abstract

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem fix_of_le_centralizer [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))] {s : G} (hs : s ∈ T)
    (hU : ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ≤
      Subgroup.centralizer (CFSG.conjugate L s : Set G)) :
    ∀ u ∈ commSub ⊤ (autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)))),
      ∀ g ∈ conjAutSub (conjAct (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))) ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩)
        (autOn L (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))), g u = u := by
  have hLVM := c.L_le_NVM
  have hcomm := commSub_top_autOn (VM := conjClosure (conjClosure V₀ T)
    (Subgroup.normalizer (conjClosure L T : Set G))) hLVM
  have hsVM := c.T_le_NVM (T.inv_mem hs)
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVMdef
  have hconj : conjAutSub (conjAct VM ⟨s⁻¹, hsVM⟩) (autOn L VM) =
      autOn (CFSG.conjugate L s) VM := (autOn_conjugate hLVM hsVM).symm
  intro u hu g hg
  rw [hcomm, Subgroup.mem_subgroupOf] at hu
  rw [hconj] at hg
  obtain ⟨y, hy, rfl⟩ := Setup.mem_autOn_iff.mp hg
  apply Subtype.ext
  rw [Setup.coe_conjAct_apply, Subgroup.mem_centralizer_iff.mp (hU hu) _ hy]
  group

theorem mem_normalizer_of_conjAct (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))] {g : G} (hg : g ∈ T)
    (hgN : conjAct _ ⟨g, c.T_le_NVM hg⟩ ∈ Subgroup.normalizer (autOn L (conjClosure
      (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) : Set _)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hgn
  obtain ⟨s, hs, hsn⟩ := c.exists_t
  have hLVM := c.L_le_NVM
  have e1 := c.conjugate_eq_of hA37 hA38 hs hsn hg hgn
  have hgVM := c.T_le_NVM (T.inv_mem hg)
  have hsVM := c.T_le_NVM (T.inv_mem hs)
  have htn := c.not_mem_normalizer hA37 hs hsn
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVMdef
  have e2 := autOn_conjugate hLVM hgVM
  rw [e1] at e2
  have hinv : conjAct VM ⟨g⁻¹, hgVM⟩ ∈
      Subgroup.normalizer (autOn L VM : Set (MulAut ↥VM)) := by
    have h := Subgroup.inv_mem _ hgN
    rwa [← map_inv] at h
  have hinv' : (autOn L VM).map (MulAut.conj (conjAct VM ⟨g⁻¹, hgVM⟩)).toMonoidHom =
      autOn L VM := Subgroup.mem_normalizer_iff_map_conj_eq.mp hinv
  rw [hinv'] at e2
  exact htn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    ((autOn_conjugate hLVM hsVM).symm.trans e2))

theorem isInnerOn_of_mem_sup [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hL32 : IsPSL 3 2 1 ↥(autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))))
    {g : G} (hgH : g ∈ L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)))
    (hg : g ∈ L ⊔ pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)))) :
    IsInnerOn (autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))) (conjAct _ ⟨g, c.H_le_NVM hgH⟩) := by
  have hHVM := c.H_le_NVM
  have hLVM := c.L_le_NVM
  have hPH : pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G))) ≤
      L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) := Subgroup.map_subtype_le _
  have hLP : L ≤ Subgroup.normalizer
      (pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G))) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hg' := hg
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right L _ hLP] at hg'
  obtain ⟨l, hl, p, hp, rfl⟩ := hg'
  have hpVM := hHVM (hPH hp)
  refine ⟨conjAct _ ⟨l, hLVM hl⟩, Setup.mem_autOn_iff.mpr ⟨⟨l, hLVM hl⟩, hl, rfl⟩,
    fun b hb => ?_⟩
  have e : (conjAct _ ⟨l, hLVM hl⟩)⁻¹ * conjAct _ ⟨l * p, hHVM hgH⟩ =
      conjAct (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))
        ⟨p, hpVM⟩ := by
    rw [← map_inv, ← map_mul]
    exact congrArg _ (Subtype.ext (by simp))
  rw [e]
  exact c.commute_of_mem_pCoreOf hL32 hp hpVM b hb

theorem mem_sup_of_isInnerOn (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hL32 : IsPSL 3 2 1 ↥(autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))))
    {g : G} (hgH : g ∈ L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)))
    (hin : IsInnerOn (autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))) (conjAct _ ⟨g, c.H_le_NVM hgH⟩)) :
    g ∈ L ⊔ pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G))) := by
  obtain ⟨a, ha, hac⟩ := hin
  obtain ⟨l', hl', rfl⟩ := Setup.mem_autOn_iff.mp ha
  have hk : (l' : G)⁻¹ * g ∈ L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hl')) hgH
  have e : conjAct _ ⟨(l' : G)⁻¹ * g, c.H_le_NVM hk⟩ =
      (conjAct _ l')⁻¹ * conjAct (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) ⟨g, c.H_le_NVM hgH⟩ := by
    rw [← map_inv, ← map_mul]
    rfl
  have hkP := c.mem_pCoreOf_of_commute hA37 hA38 hL32 hk (fun b hb => by
    rw [e]
    exact hac b hb)
  have e2 : g = l' * ((l' : G)⁻¹ * g) := by group
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl') (Subgroup.mem_sup_right hkP)

end Ctx

end CFSG.Quasithin.H13.T326
