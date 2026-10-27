module

public import CFSG.Quasithin.Vol2.Ch11SecFStep2a
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecFStep1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.QuasithinUnique.C5 (conjSubgroup_mono conjSubgroup_normalizer conjSubgroup_le_iff
  conjSubgroup_inf conjSubgroup_commutator conjSubgroup_centralizer)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ V₃ : Subgroup G}

omit [Finite G] in
theorem isCComponent_conj {K X : Subgroup G} (hK : quasithinIsCComponent K X) (g : G) :
    quasithinIsCComponent (conjSubgroup K g) (conjSubgroup X g) :=
  SecA.isCComponent_map_equiv (MulAut.conj g⁻¹) hK

theorem commutator_V₃_conj_eq_bot (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4)
    (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n) :
    ∀ g ∈ Subgroup.normalizer (V₁ : Set G), ⁅V₃, conjSubgroup (fsuV T I) g⁆ = ⊥ := by
  have hQ := fsuV_le_pCoreOf_normalizer hF h1102 h1103 h1141 h1143 h1154 h1156 h hV₁ hk
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := SecA.L_le_normalizer_fsuV h
  have hL₁ : LOf L V₁ ≤ Subgroup.normalizer (V₁ : Set G) := SecD.lOf_le_normalizer L V₁
  have hL₁L : LOf L V₁ ≤ L := (perfectCore_le _).trans inf_le_left
  have hn : 1 ≤ n := by have := h.one_lt; omega
  have hV₂1 : V₂ ≠ ⊥ := SecA.IsVi.ne_bot h hV₂ (by norm_num)
  intro g hg
  by_contra hne
  obtain ⟨l, hl, hinf, hcomm⟩ := exists_line_of_ne_bot hF h1102 h1141 h hV₁ hV₂ hV₃ hk hQ hg hne
  have hlV : conjSubgroup (fsuV T I) l⁻¹ = fsuV T I :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hLV (L.inv_mem (hL₁L hl)))
  have hV₂l : conjSubgroup (conjSubgroup V₂ l) l⁻¹ = V₂ := by
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hg₁ : g * l⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (hL₁ hl))
  have hinf₁ : fsuV T I ⊓ conjSubgroup (fsuV T I) (g * l⁻¹) = V₂ := by
    have h1 := congrArg (fun A => conjSubgroup A l⁻¹) hinf
    rwa [conjSubgroup_inf, hlV, hV₂l, conjSubgroup_conjSubgroup] at h1
  have hcomm₁ : ⁅fsuV T I, conjSubgroup (fsuV T I) (g * l⁻¹)⁆ = V₂ := by
    have h1 := congrArg (fun A => conjSubgroup A l⁻¹) hcomm
    rwa [conjSubgroup_commutator, hlV, hV₂l, conjSubgroup_conjSubgroup] at h1
  set g₁ := g * l⁻¹ with hg₁def
  have hg₁i : g₁⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) := Subgroup.inv_mem _ hg₁
  have hne₁ : ⁅V₃, conjSubgroup (fsuV T I) g₁⁻¹⁆ ≠ ⊥ := by
    intro hbot
    have hle := hF.z G T L I n V₁ V₃ hset hk hV₁ hV₃ _ (conj_fsuV_le_ROf h hV₁ hQ hg₁i) hbot
    have h2 := conjSubgroup_mono hle g₁
    rw [conjSubgroup_commutator, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
      conjSubgroup_eq_iff_mem_normalizer.mpr hg₁, Subgroup.commutator_comm, hcomm₁] at h2
    exact not_V₂_le_V₁ hset.cV hn hV₁ hV₂ h2
  obtain ⟨l', hl', hinf', -⟩ :=
    exists_line_of_ne_bot hF h1102 h1141 h hV₁ hV₂ hV₃ hk hQ hg₁i hne₁
  have hinf'' : fsuV T I ⊓ conjSubgroup (fsuV T I) g₁⁻¹ = conjSubgroup V₂ g₁⁻¹ := by
    have h1 := congrArg (fun A => conjSubgroup A g₁⁻¹) hinf₁
    rwa [conjSubgroup_inf, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one,
      inf_comm] at h1
  have hV₂g₂ : conjSubgroup V₂ (l' * g₁) = V₂ := by
    rw [← conjSubgroup_conjSubgroup, ← hinf', hinf'', conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one]
  have hVg₂ : conjSubgroup (fsuV T I) (l' * g₁) = conjSubgroup (fsuV T I) g₁ := by
    rw [← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr (hLV (hL₁L hl'))]
  obtain ⟨hcc, hnc, huniq⟩ := h1113 G T L I n V₂ h hV₂
  have hL₂g : conjSubgroup (LOf L V₂) (l' * g₁) = LOf L V₂ := by
    refine huniq _ ?_ ?_
    · have h1 := isCComponent_conj hcc (l' * g₁)
      rwa [conjSubgroup_normalizer, hV₂g₂] at h1
    · intro hle
      apply hnc
      rw [← conjSubgroup_le_iff (g := l' * g₁), conjSubgroup_centralizer, hV₂g₂]
      exact hle
  have hVL₂ : ⁅fsuV T I, LOf L V₂⁆ = fsuV T I := hF.vL2 G T L I n V₂ hset hk hV₂
  have hP : ⁅conjSubgroup (fsuV T I) g₁, LOf L V₂⁆ = conjSubgroup (fsuV T I) g₁ := by
    have h1 := congrArg (fun A => conjSubgroup A (l' * g₁)) hVL₂
    rwa [conjSubgroup_commutator, hL₂g, hVg₂] at h1
  have hL₂N : LOf L V₂ ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) g₁ : Set G) := by
    have h1 : LOf L V₂ ≤ Subgroup.normalizer (fsuV T I : Set G) :=
      ((perfectCore_le _).trans inf_le_left).trans hLV
    have h2 := conjSubgroup_mono h1 (l' * g₁)
    rwa [hL₂g, conjSubgroup_normalizer, hVg₂] at h2
  have hbot := hF.l2Rad G T L I n V₁ V₂ hset hk hV₁ hV₂ _ (conj_fsuV_le_ROf h hV₁ hQ hg₁) hL₂N hP
  rw [hcomm₁] at hbot
  exact hV₂1 hbot

end CFSG.Quasithin.Vol2.Ch11.SecF
