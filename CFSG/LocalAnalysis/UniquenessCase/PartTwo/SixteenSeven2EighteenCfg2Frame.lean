module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Aut
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W]

structure Cfg2Setting (X L : Subgroup (MulAut W)) (J₀ J₁ : Subgroup W) : Prop where
  sq : ∀ w : W, w ^ 2 = 1
  norm : ∀ x ∈ X, L.map (MulAut.conj x).toMonoidHom = L
  simple : IsSimpleGroup ↥L
  perfect : ⁅L, L⁆ = L
  fix : fixV L = ⊥
  irr₀ : J₀ ∈ irrSet L
  irr₁ : J₁ ∈ irrSet L
  inf_eq : J₀ ⊓ J₁ = ⊥
  sup_eq : J₀ ⊔ J₁ = ⊤

theorem s16c167_cfg2_normal {A : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)}
    (hLbot : L ≠ ⊥) (hall : commSub ⊤ L = ⊤) (h : Conc4_136W A t L) :
    ∀ x ∈ A, L.map (MulAut.conj x).toMonoidHom = L := by
  obtain ⟨-, hcomm, -⟩ := h
  intro x hx
  by_contra hne
  have hnot : x ∉ Subgroup.normalizer (L : Set (MulAut W)) := by
    intro hxN
    exact hne ((Subgroup.mem_normalizer_iff_map_conj_eq).mp hxN)
  have h1 : commSub (commSub ⊤ L) (L.map (MulAut.conj x).toMonoidHom) = ⊥ :=
    (hcomm x hx hnot).2
  rw [hall] at h1
  have h2 : (⊤ : Subgroup W) ≤ fixV (L.map (MulAut.conj x).toMonoidHom) :=
    commSub_eq_bot_iff.mp h1
  have h3 : L.map (MulAut.conj x).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    ext w
    have hfix : y w = w :=
      (mem_fixV.mp (h2 (show w ∈ (⊤ : Subgroup W) from trivial))) y hy
    simpa using hfix
  have h4 : L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective L (f := (MulAut.conj x).toMonoidHom)
      (MulAut.conj x).injective).mp h3
  exact hLbot h4

theorem s16c167_cfg2_perfect {X L K : Subgroup (MulAut W)} (hLX : L ≤ X)
    (hsimple : IsSimpleGroup ↥L)
    (hK : K = X ⊓ Subgroup.centralizer (L : Set (MulAut W)))
    (hcenter : ∀ κ ∈ K, (∀ y ∈ K, y * κ = κ * y) → κ = 1) : ⁅L, L⁆ = L := by
  have hle : ⁅L, L⁆ ≤ L := Subgroup.commutator_le_of_le le_rfl le_rfl
  haveI : ((⁅L, L⁆).subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (Subgroup.normalizer_commutator_ge_left (H₁ := L) (H₂ := L))
  rcases hsimple.eq_bot_or_eq_top_of_normal ((⁅L, L⁆).subgroupOf L) with hH | hH
  · exfalso
    have hHbot : ⁅L, L⁆ = ⊥ := by
      have hd := Subgroup.subgroupOf_eq_bot.mp hH
      rw [disjoint_iff] at hd
      rwa [inf_eq_left.mpr hle] at hd
    have hcent : L ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hHbot
    have hLbot : L = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro a ha
      have haK : a ∈ K := by
        rw [hK]
        exact ⟨hLX ha, hcent ha⟩
      exact hcenter a haK fun y hyK => by
        rw [hK] at hyK
        exact ((Subgroup.mem_centralizer_iff.mp hyK.2) a ha).symm
    exact absurd hLbot ((Subgroup.nontrivial_iff_ne_bot L).mp hsimple.toNontrivial)
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp hH)

theorem s16c167_cfg2_rk_ge_three [Finite W] {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X L J₀ J₁) {J : Subgroup W} (hJ : J ∈ irrSet L) : 3 ≤ rk ↥J := by
  obtain ⟨-, hirr⟩ := hJ
  obtain ⟨hlt, hstab, -, -⟩ := hirr
  rw [F.fix, inf_bot_eq] at hlt
  by_contra h
  have hr : rk ↥J ≤ 2 := by omega
  have hJle : J ≤ fixV L := s16c167_cfg2_perf_fixed F.sq F.perfect hstab hr
  rw [F.fix] at hJle
  exact absurd (le_antisymm hJle bot_le) (ne_of_gt hlt)

theorem s16c167_cfg2_disj [Finite W] {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X L J₀ J₁) {J : Subgroup W} (hJ : J ∈ irrSet L) {x : MulAut W}
    (hx : x ∈ X) : J.map x.toMonoidHom = J ∨ J ⊓ J.map x.toMonoidHom = ⊥ := by
  obtain ⟨-, hirr⟩ := hJ
  obtain ⟨-, hstabJ, -, hmin⟩ := hirr
  have hstabJ' : StableUnder L (J.map x.toMonoidHom) := by
    intro l hl u hu
    rw [Subgroup.mem_map] at hu ⊢
    obtain ⟨v, hv, rfl⟩ := hu
    have hmem : (MulAut.conj x⁻¹) l ∈ L := by
      rw [← F.norm x⁻¹ (X.inv_mem hx)]
      exact Subgroup.mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hl
    refine ⟨(MulAut.conj x⁻¹) l v, hstabJ ((MulAut.conj x⁻¹) l) hmem v hv, ?_⟩
    have hxconj : x * (MulAut.conj x⁻¹) l = l * x := by
      rw [MulAut.conj_apply]; group
    have h1 := congrArg (fun f : MulAut W => f v) hxconj
    simpa only [MulAut.mul_apply, MulEquiv.coe_toMonoidHom] using h1
  have hstabInf : StableUnder L (J ⊓ J.map x.toMonoidHom) := by
    intro l hl u hu
    exact ⟨hstabJ l hl u hu.1, hstabJ' l hl u hu.2⟩
  have hNle : J ⊓ fixV L ≤ J ⊓ J.map x.toMonoidHom := by
    rw [F.fix, inf_bot_eq]
    exact bot_le
  have hres := hmin (J ⊓ J.map x.toMonoidHom) hstabInf hNle inf_le_left
  rw [F.fix, inf_bot_eq] at hres
  rcases hres with hbot | hjeq
  · exact Or.inr hbot
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp hjeq)
      (le_of_eq (Subgroup.card_map_of_injective (f := x.toMonoidHom)
        (MulEquiv.injective x)))).symm

theorem s16c167_commV_stable {Y : Subgroup (MulAut W)} {t : MulAut W}
    (hc : ∀ y ∈ Y, y * t = t * y) : StableUnder Y (commSub ⊤ (Subgroup.zpowers t)) := by
  intro y hy u hu
  refine Subgroup.closure_induction
    (p := fun c _ => y c ∈ commSub ⊤ (Subgroup.zpowers t)) ?_ ?_ ?_ ?_ hu
  · rintro c ⟨x, hx, w, -, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : y * (t ^ k) = (t ^ k) * y := (Commute.zpow_right (hc y hy) k).eq
    have h1 : y ((t ^ k) w * w⁻¹) = (t ^ k) (y w) * (y w)⁻¹ := by
      rw [map_mul, map_inv]
      have h2 := congrArg (fun f : MulAut W => f w) hcomm
      rw [MulAut.mul_apply, MulAut.mul_apply] at h2
      rw [h2]
    rw [h1]
    exact Subgroup.subset_closure
      ⟨t ^ k, (Subgroup.zpowers t).zpow_mem (Subgroup.mem_zpowers t) k, y w, trivial, rfl⟩
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [map_inv]
    exact Subgroup.inv_mem _ ha

theorem s16c167_cfg2_cent_of_fix [Finite W] {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X L J₀ J₁) {U : Subgroup W} (hU : StableUnder L U) (hU0 : U ≠ ⊥)
    {t : MulAut W} (ht : t ∈ X) (hUt : U ≤ fixV (Subgroup.zpowers t)) :
    t ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
  have hA : L ≤ stabSub U := by
    intro x hx
    rw [mem_stabSub]
    intro u
    constructor
    · intro hxu
      have h := hU x⁻¹ (L.inv_mem hx) (x u) hxu
      rwa [MulAut.inv_apply_self] at h
    · intro hu
      exact hU x hx u hu
  let ρ : ↥L →* MulAut ↥U := (resHom U).comp (Subgroup.inclusion hA)
  have hker : ρ.ker = ⊥ := by
    rcases F.simple.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      apply hU0
      refine le_antisymm ?_ bot_le
      rw [← F.fix]
      intro u hu
      rw [mem_fixV]
      intro l hl
      have h1 : resHom U (Subgroup.inclusion hA ⟨l, hl⟩) = 1 := by
        have hmem : (⟨l, hl⟩ : ↥L) ∈ ρ.ker := by
          rw [h]
          exact Subgroup.mem_top _
        exact MonoidHom.mem_ker.mp hmem
      have h3 := congrArg (fun f : MulAut ↥U => f ⟨u, hu⟩) h1
      rw [MulAut.one_apply] at h3
      have h3' := congrArg Subtype.val h3
      rw [resHom_apply, Subgroup.coe_inclusion] at h3'
      simpa using h3'
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hcL : t * l * t⁻¹ * l⁻¹ ∈ L := by
    have hmem : (MulAut.conj t) l ∈ L := by
      rw [← F.norm t ht]
      exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hl
    have h := L.mul_mem hmem (L.inv_mem hl)
    simpa [MulAut.conj_apply] using h
  have hfix : ∀ u ∈ U, (t * l * t⁻¹ * l⁻¹) u = u := by
    intro u hu
    have hlu : l⁻¹ u ∈ U := hU l⁻¹ (L.inv_mem hl) u hu
    have htu : t⁻¹ (l⁻¹ u) = l⁻¹ u :=
      mem_fixV.mp (hUt hlu) t⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers t))
    have htu' : t u = u := mem_fixV.mp (hUt hu) t (Subgroup.mem_zpowers t)
    have hlu' : l (l⁻¹ u) = u := by
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    calc (t * l * t⁻¹ * l⁻¹) u = t (l (t⁻¹ (l⁻¹ u))) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply]
      _ = t (l (l⁻¹ u)) := by rw [htu]
      _ = t u := by rw [hlu']
      _ = u := htu'
  have hrho1 : resHom U (Subgroup.inclusion hA ⟨t * l * t⁻¹ * l⁻¹, hcL⟩) = 1 := by
    refine MulEquiv.ext fun u => ?_
    apply Subtype.ext
    rw [MulAut.one_apply, resHom_apply, Subgroup.coe_inclusion]
    exact hfix (u : W) u.2
  have hrho : ρ ⟨t * l * t⁻¹ * l⁻¹, hcL⟩ = 1 := hrho1
  have hc1 : t * l * t⁻¹ * l⁻¹ = 1 := by
    have hmem : (⟨t * l * t⁻¹ * l⁻¹, hcL⟩ : ↥L) ∈ ρ.ker := MonoidHom.mem_ker.mpr hrho
    rw [hker, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  have htl : t * l * t⁻¹ = l := mul_inv_eq_one.mp hc1
  calc l * t = (t * l * t⁻¹) * t := by rw [htl]
    _ = t * l := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
