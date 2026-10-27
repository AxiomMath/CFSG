module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TRho
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TMB4
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TLift
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TMBApp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open CFSG.Quasithin.H13.L828T
open scoped IsMulCommutative commutatorElement

section SixB2

variable {G : Type} [Group G] [Finite G]

theorem s828_T_sylow {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hyp : Hyp7_0_2 G T L I) (c : S828Ctx T L I H h k)
    (hNbar : ∀ g : MulAut ↥(fsuV T I),
      g ∈ Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))) →
        g ∈ autOn L (fsuV T I)) :
    autOn T (fsuV T I) ≤ autOn L (fsuV T I) ⊓
        stabSub ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)) ∧
      IsPGroup 2 ↥(autOn T (fsuV T I)) ∧
      ¬ 2 ∣ ((autOn T (fsuV T I)).subgroupOf (autOn L (fsuV T I) ⊓
        stabSub ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))).index := by
  classical
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) := sup_le c.hLN c.hTV
  have hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    ⟨le_sup_right, hyp.fsu.sylow.1, hyp.fsu.maximal.1.2.2.1⟩
  have hSyl := AutOn.isSylowTwoOf_autOn hTS hLTV
  have hSH : autOn T (fsuV T I) ≤ autOn L (fsuV T I) := fun g hg =>
    hNbar g (autOn_le_normalizer_82 c.hTL hg)
  have hsup : autOn (L ⊔ T) (fsuV T I) = autOn L (fsuV T I) := by
    rw [AutOn.autOn_sup_eq c.hLN c.hTV]
    exact sup_eq_left.mpr hSH
  have hTU : T ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) := by
    obtain ⟨-, -, -, -, -, -, -, hTU, -⟩ := c.hC5
    exact hTU
  have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hSstab : autOn T (fsuV T I) ≤ stabSub ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)) := by
    have h1 := autOn_inf_normalizer_82 (V := fsuV T I) (L := T) (U := ch82U (fsuV T I) h) hUV
    rw [inf_of_le_left hTU] at h1
    exact (inf_eq_left.mp h1.symm)
  have hSK : autOn T (fsuV T I) ≤ autOn L (fsuV T I) ⊓
      stabSub ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)) := le_inf hSH hSstab
  refine ⟨hSK, AutOn.isPGroup_autOn hyp.fsu.sylow.1, ?_⟩
  have hodd := hSyl.2.2
  rw [hsup] at hodd
  have hdvd : (autOn T (fsuV T I)).relIndex (autOn L (fsuV T I) ⊓
      stabSub ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))) ∣
        (autOn T (fsuV T I)).relIndex (autOn L (fsuV T I)) :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ hSK inf_le_left)
  exact fun h2 => hodd (h2.trans hdvd)

theorem s828_LU_conj_B {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) {l : G} (hl : l ∈ ch82LU L (ch82U (fsuV T I) h))
    {b : G} (hb : b ∈ ch82B (fsuV T I) h) : l * b * l⁻¹ ∈ ch82B (fsuV T I) h := by
  have hLUV : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans c.hLN)
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hLUV hl) b).mp hb.1, ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (s828_LU_norm_P c hl) b).mp hb.2

theorem s828_exists_induces_LU {T L I H : Subgroup G} {h : G} {k : ℕ}
    [IsMulCommutative ↥(fsuV T I)] (c : S828Ctx T L I H h k)
    (y₀ : ↥(Subgroup.normalizer (fsuV T I : Set G)))
    (hy : (y₀ : G) ∈ ch82LU L (ch82U (fsuV T I) h)) :
    ∃ γ : AddMonoid.End (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))),
      Induces γ (⇑(conjAct (fsuV T I) y₀)) := by
  refine exists_induces _ (fun a _ b _ => map_mul _ a b) ?_ ?_
  · intro b hb
    have hb' : ((b : ↥(fsuV T I)) : G) ∈ ch82B (fsuV T I) h := Subgroup.mem_subgroupOf.mp hb
    rw [Subgroup.mem_subgroupOf, CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
    exact s828_LU_conj_B c hy hb'
  · intro u hu
    have hu' : ((u : ↥(fsuV T I)) : G) ∈ ch82U (fsuV T I) h := Subgroup.mem_subgroupOf.mp hu
    rw [Subgroup.mem_subgroupOf, CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp (s828_LU_norm_U T L I h hy) u).mp hu'

theorem s828_mb4_G (hMB3 : MB3_828) (hMB4 : MB4_828) (hcard : Mathieu.StmtH13Card)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hrow : Case8_2 T L I) (hr : Row711M24Code T L I) (c : S828Ctx T L I H h k) :
    (∀ g : MulAut ↥(fsuV T I),
      g ∈ Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))) →
        g ∈ autOn L (fsuV T I)) ∧
    (∃ z ∈ autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I), z ^ 3 = 1 ∧
        (∀ g ∈ autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I),
          ⁅z, g⁆ ∈ pCoreOf 2 (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))) ∧
        ∃ b ∈ (ch82B (fsuV T I) h).subgroupOf (fsuV T I),
          z b * b⁻¹ ∉ (ch82U (fsuV T I) h).subgroupOf (fsuV T I)) ∧
    (∀ S : Subgroup (MulAut ↥(fsuV T I)),
      S ≤ autOn L (fsuV T I) ⊓ stabSub ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)) →
      IsPGroup 2 ↥S →
      ¬ 2 ∣ (S.subgroupOf (autOn L (fsuV T I) ⊓
        stabSub ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))).index →
        ∃ t ∈ S, t ^ 2 = 1 ∧ (∃ g ∈ autOn L (fsuV T I),
            g * t * g⁻¹ ∈ autOn (ch82A (fsuV T I) h) (fsuV T I)) ∧
          ∀ z ∈ autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I),
            (∀ g ∈ autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I),
              ⁅z, g⁆ ∈ pCoreOf 2 (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))) →
            t * z * t⁻¹ * z ∈ pCoreOf 2 (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))) ∧
    (∀ x ∈ pCoreOf 2 (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I)),
      ∀ b ∈ (ch82B (fsuV T I) h).subgroupOf (fsuV T I),
        x b * b⁻¹ ∈ (ch82U (fsuV T I) h).subgroupOf (fsuV T I)) := by
  classical
  obtain ⟨hX, hXe, -⟩ := s828_mb_data hcard hrow c
  obtain ⟨e1, e2, e3⟩ := s828_mb_eqs c
  have hAp : IsPGroup 2 ↥(ch82A (fsuV T I) h) := B6.isPGroup_of_isElemAbelian c.hAe
  have hrows := rows_hlu82_828 hcard c.hL0 c.hV c.hC5 c.hAN hAp
  have hr3 := hrows.2.2.1 hr
  have hM3 := hMB3 _ (autOn L (fsuV T I)) (autOn (ch82A (fsuV T I) h) (fsuV T I)) hX hXe
    (Or.inr (Or.inr (Or.inl hr3)))
  obtain ⟨hNbar, ⟨zb, hzbP, hzb3, hzbc, bb, hbbB, hzbb⟩, hSyl⟩ :=
    hMB4 _ (autOn L (fsuV T I)) (autOn (ch82A (fsuV T I) h) (fsuV T I)) hX hXe hr3
  rw [e3] at hzbP hzbc hM3 hSyl
  rw [e1, e2] at hM3
  rw [e2] at hSyl hzbb
  rw [e1] at hbbB
  exact ⟨hNbar, ⟨zb, hzbP, hzb3, hzbc, bb, hbbB, hzbb⟩, hSyl, hM3⟩

theorem s828_exists_t {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hyp : Hyp7_0_2 G T L I) (c : S828Ctx T L I H h k)
    (hNbar : ∀ g : MulAut ↥(fsuV T I),
      g ∈ Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))) →
        g ∈ autOn L (fsuV T I))
    (hSyl : ∀ S : Subgroup (MulAut ↥(fsuV T I)),
      S ≤ autOn L (fsuV T I) ⊓ stabSub ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)) →
      IsPGroup 2 ↥S →
      ¬ 2 ∣ (S.subgroupOf (autOn L (fsuV T I) ⊓
        stabSub ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))).index →
        ∃ t ∈ S, t ^ 2 = 1 ∧ (∃ g ∈ autOn L (fsuV T I),
            g * t * g⁻¹ ∈ autOn (ch82A (fsuV T I) h) (fsuV T I)) ∧
          ∀ z ∈ autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I),
            (∀ g ∈ autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I),
              ⁅z, g⁆ ∈ pCoreOf 2 (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))) →
            t * z * t⁻¹ * z ∈ pCoreOf 2 (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))) :
    ∃ t : ↥(Subgroup.normalizer (fsuV T I : Set G)), (t : G) ∈ T ∧ (t : G) ^ 2 = 1 ∧
      ∀ z ∈ autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I),
        (∀ g ∈ autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I),
          ⁅z, g⁆ ∈ pCoreOf 2 (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))) →
        conjAct (fsuV T I) t * z * (conjAct (fsuV T I) t)⁻¹ * z ∈
          pCoreOf 2 (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I)) := by
  classical
  obtain ⟨hSK, hSp, hSidx⟩ := s828_T_sylow hyp c hNbar
  obtain ⟨tb, htbS, htb2, ⟨g, hgH, hgt⟩, htinv⟩ := hSyl _ hSK hSp hSidx
  obtain ⟨t₀, ht₀T, ht₀e⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.mp htbS
  obtain ⟨g₀, hg₀L, hg₀e⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.mp hgH
  obtain ⟨a₀, ha₀A, ha₀e⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.mp hgt
  set a' : ↥(Subgroup.normalizer (fsuV T I : Set G)) := g₀⁻¹ * a₀ * g₀ with ha'
  have hconj_a' : conjAct (fsuV T I) a' = tb := by
    rw [ha', map_mul, map_mul, map_inv, hg₀e, ha₀e]
    group
  have ha'2 : a' ^ 2 = 1 := by
    have h1 : (a₀ : G) ^ 2 = 1 := c.hAe.2 _ ha₀A
    have h2 : a₀ ^ 2 = 1 := Subtype.ext (by simpa using h1)
    have h3 : a' ^ 2 = g₀⁻¹ * a₀ ^ 2 * g₀ := by rw [ha', pow_two, pow_two]; group
    rw [h3, h2]
    group
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := c.hTV
  have hTp' : IsPGroup 2 ↥(T.subgroupOf (Subgroup.normalizer (fsuV T I : Set G))) :=
    hyp.fsu.sylow.1.comap_of_injective _ (Subgroup.subtype_injective _)
  have hTi' : ¬ 2 ∣ (T.subgroupOf (Subgroup.normalizer (fsuV T I : Set G))).index :=
    fun h2 => hyp.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTV))
  obtain ⟨t, htT', ht2, htC⟩ := L828Lift.exists_involution_lift
    (T.subgroupOf (Subgroup.normalizer (fsuV T I : Set G))) (conjAct (fsuV T I)).ker hTp' hTi'
    ha'2 ⟨⟨t₀, hTV ht₀T⟩, Subgroup.mem_subgroupOf.mpr ht₀T, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ht₀e, hconj_a', mul_inv_cancel]⟩
  have htconj : conjAct (fsuV T I) t = tb := by
    have h1 : conjAct (fsuV T I) (t * a'⁻¹) = 1 := htC
    rw [map_mul, map_inv, hconj_a', mul_inv_eq_one] at h1
    exact h1
  refine ⟨t, Subgroup.mem_subgroupOf.mp htT', ?_, ?_⟩
  · have := congrArg Subtype.val ht2
    simpa using this
  · intro z hz hzc
    rw [htconj]
    exact htinv z hz hzc

theorem s828_zeta {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k)
    (hM3 : ∀ x ∈ pCoreOf 2 (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I)),
      ∀ b ∈ (ch82B (fsuV T I) h).subgroupOf (fsuV T I),
        x b * b⁻¹ ∈ (ch82U (fsuV T I) h).subgroupOf (fsuV T I))
    {zb : MulAut ↥(fsuV T I)}
    (hzbP : zb ∈ autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I)) (hzb3 : zb ^ 3 = 1)
    (hzbc : ∀ g ∈ autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I),
      ⁅zb, g⁆ ∈ pCoreOf 2 (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I)))
    (hzb : ∃ b ∈ (ch82B (fsuV T I) h).subgroupOf (fsuV T I),
      zb b * b⁻¹ ∉ (ch82U (fsuV T I) h).subgroupOf (fsuV T I)) :
    ∃ (z₀ : ↥(Subgroup.normalizer (fsuV T I : Set G)))
      (γz : AddMonoid.End (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))),
      (z₀ : G) ∈ ch82LU L (ch82U (fsuV T I) h) ∧ conjAct (fsuV T I) z₀ = zb ∧
        Induces γz (⇑(conjAct (fsuV T I) z₀)) ∧
        γz ∈ commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
          ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
          ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
            Set (MulAut ↥(fsuV T I))) ∧ γz ^ 3 = 1 ∧ γz ≠ 1 := by
  classical
  obtain ⟨bb, hbbB, hzbb⟩ := hzb
  obtain ⟨z₀, hz₀LU, hz₀e⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.mp hzbP
  obtain ⟨γz, hγz⟩ := s828_exists_induces_LU c z₀ hz₀LU
  have hγzc : γz ∈ commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I))) := by
    rw [mem_commutant_iff]
    intro γ hγ0
    obtain ⟨g', hg', hγ⟩ := hγ0
    have hcomm : ⁅g', zb⁆ ∈ pCoreOf 2 (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I)) := by
      rw [← commutatorElement_inv]
      exact (pCoreOf 2 _).inv_mem (hzbc g' hg')
    refine Induces.ext_of (Induces.mul hγz hγ) (Induces.mul hγ hγz) ?_
    intro b hb
    obtain ⟨b₁, hb₁, -⟩ := hγ ⟨b, hb⟩
    obtain ⟨b₂, hb₂, -⟩ := hγz b₁
    have hx : g' * zb = ⁅g', zb⁆ * (zb * g') := by
      simp only [commutatorElement_def]
      group
    have key : (⇑g' ∘ ⇑(conjAct (fsuV T I) z₀)) b =
        ⁅g', zb⁆ ((conjAct (fsuV T I) z₀) (g' b)) := by
      rw [Function.comp_apply, hz₀e]
      have := congrArg (fun φ : MulAut ↥(fsuV T I) => φ b) hx
      simpa [MulAut.mul_apply] using this
    have hw : (conjAct (fsuV T I) z₀) (g' b) ∈
        (ch82B (fsuV T I) h).subgroupOf (fsuV T I) := by
      rw [← hb₁, ← hb₂]
      exact b₂.2
    rw [key]
    show ⁅g', zb⁆ ((conjAct (fsuV T I) z₀) (g' b)) *
      ((conjAct (fsuV T I) z₀) (g' b))⁻¹ ∈ (ch82U (fsuV T I) h).subgroupOf (fsuV T I)
    exact hM3 _ hcomm _ hw
  have hz3 : (conjAct (fsuV T I) z₀) ^ 3 = 1 := by rw [hz₀e]; exact hzb3
  have hγz3 : γz ^ 3 = 1 := by
    refine Induces.ext_of (Induces.pow hγz 3) (induces_one _ _) ?_
    intro b hb
    have h1 : ((conjAct (fsuV T I) z₀) ^ 3) b = b := by rw [hz3]; rfl
    have hiter : (⇑(conjAct (fsuV T I) z₀))^[3] b = b := h1
    show (⇑(conjAct (fsuV T I) z₀))^[3] b * (id b)⁻¹ ∈ (ch82U (fsuV T I) h).subgroupOf (fsuV T I)
    rw [hiter]
    simp
  have hγz1 : γz ≠ 1 := by
    intro h1
    have := Induces.mul_inv_mem_of_eq_one hγz h1 bb hbbB
    rw [hz₀e] at this
    exact hzbb this
  exact ⟨z₀, γz, hz₀LU, hz₀e, hγz, hγzc, hγz3, hγz1⟩

theorem s828_exists_t_zeta (hMB3 : MB3_828) (hMB4 : MB4_828) (hcard : Mathieu.StmtH13Card)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hyp : Hyp7_0_2 G T L I) (hrow : Case8_2 T L I) (hr : Row711M24Code T L I)
    (c : S828Ctx T L I H h k)
    (hTP : T ≤ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G))
    (ρ : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
          Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) →*
        AddMonoid.End (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) ×
          QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)))
    (hdiag : ∀ (y₀ : ↥(Subgroup.normalizer (fsuV T I : Set G)))
          (hy : (y₀ : G) ∈ ch82LU L (ch82U (fsuV T I) h))
          (γ : AddMonoid.End (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
            ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))),
        Induces γ (⇑(conjAct (fsuV T I) y₀)) →
        diagEnd γ = ρ ⟨(y₀ : G), s828_LU_norm_P c hy, s828_LU_norm_U T L I h hy⟩) :
    ∃ (t : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
          Subgroup.normalizer (ch82U (fsuV T I) h : Set G)))
      (ζ : ↥(commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
        ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
          Set (MulAut ↥(fsuV T I))))),
      (t : G) ∈ T ∧ (t : G) ^ 2 = 1 ∧ ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧
        ρ t * diagEnd (ζ : AddMonoid.End (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
            ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))) =
          diagEnd ((ζ ^ 2 : ↥(commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
            ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
            ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
              Set (MulAut ↥(fsuV T I))))) : AddMonoid.End (QMod
            ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
            ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))) * ρ t := by
  classical
  obtain ⟨hNbar, ⟨zb, hzbP, hzb3, hzbc, hzb⟩, hSyl, hM3⟩ :=
    s828_mb4_G hMB3 hMB4 hcard hrow hr c
  obtain ⟨t, htT, ht2G, htinv⟩ := s828_exists_t hyp c hNbar hSyl
  obtain ⟨z₀, γz, hz₀LU, hz₀e, hγz, hγzc, hγz3, hγz1⟩ := s828_zeta c hM3 hzbP hzb3 hzbc hzb
  have hTU : T ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) := by
    obtain ⟨-, -, -, -, -, -, -, hTU, -⟩ := c.hC5
    exact hTU
  have hLUN : ∀ {x : G}, x ∈ ch82LU L (ch82U (fsuV T I) h) →
      x ∈ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
        Subgroup.normalizer (ch82U (fsuV T I) h : Set G) := fun hx =>
    ⟨s828_LU_norm_P c hx, s828_LU_norm_U T L I h hx⟩
  set tN : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
      Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) := ⟨(t : G), hTP htT, hTU htT⟩ with htN
  set zN : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
      Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) := ⟨(z₀ : G), hLUN hz₀LU⟩ with hzN
  have hdz : diagEnd γz = ρ zN := hdiag z₀ hz₀LU γz hγz
  set w' : ↥(Subgroup.normalizer (fsuV T I : Set G)) := t * z₀ * t⁻¹ * z₀ with hw'
  have hw'LU : (w' : G) ∈ ch82LU L (ch82U (fsuV T I) h) := by
    have h1 : (t : G) * z₀ * (t : G)⁻¹ ∈ ch82LU L (ch82U (fsuV T I) h) :=
      (Subgroup.mem_normalizer_iff.mp (c.hLUT htT) _).mp hz₀LU
    exact (ch82LU L (ch82U (fsuV T I) h)).mul_mem h1 hz₀LU
  have hconjw' : conjAct (fsuV T I) w' =
      conjAct (fsuV T I) t * zb * (conjAct (fsuV T I) t)⁻¹ * zb := by
    rw [hw', map_mul, map_mul, map_mul, map_inv, hz₀e]
  have hw'O2 : conjAct (fsuV T I) w' ∈
      pCoreOf 2 (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I)) := by
    rw [hconjw']
    exact htinv zb hzbP hzbc
  obtain ⟨γw, hγw⟩ := s828_exists_induces_LU c w' hw'LU
  have hγw1 : γw = 1 := by
    refine Induces.ext_of hγw (induces_one _ _) ?_
    intro b hb
    exact hM3 _ hw'O2 b hb
  have hd1 : diagEnd (1 : AddMonoid.End (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))) = 1 :=
    (diagRing_apply 1).symm.trans (map_one diagRing)
  have hρw : ρ (tN * zN * tN⁻¹ * zN) = 1 := by
    have h1 := hdiag w' hw'LU γw hγw
    rw [hγw1, hd1] at h1
    have e : (⟨(w' : G), hLUN hw'LU⟩ : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) :
        Set G) ⊓ Subgroup.normalizer (ch82U (fsuV T I) h : Set G))) = tN * zN * tN⁻¹ * zN :=
      Subtype.ext rfl
    rw [← e]
    exact h1.symm
  have hpow : ∀ (a : AddMonoid.End (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))) (n : ℕ),
      diagEnd (a ^ n) = diagEnd a ^ n := fun a n => map_pow diagRing a n
  have hz3' : (ρ zN) ^ 3 = 1 := by
    rw [← hdz, ← hpow, hγz3, hd1]
  have hrel : ρ tN * ρ zN = (ρ zN) ^ 2 * ρ tN := by
    have h1 : ρ tN * ρ zN * ρ tN⁻¹ * ρ zN = 1 := by
      have := hρw
      simpa only [map_mul] using this
    have h2 : ρ tN * ρ zN * ρ tN⁻¹ = (ρ zN) ^ 2 := by
      calc ρ tN * ρ zN * ρ tN⁻¹ = (ρ tN * ρ zN * ρ tN⁻¹) * (ρ zN * (ρ zN) ^ 2) := by
            rw [← pow_succ', hz3', mul_one]
        _ = (ρ tN * ρ zN * ρ tN⁻¹ * ρ zN) * (ρ zN) ^ 2 := by simp only [mul_assoc]
        _ = (ρ zN) ^ 2 := by rw [h1, one_mul]
    have h3 : ρ tN⁻¹ * ρ tN = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    calc ρ tN * ρ zN = ρ tN * ρ zN * (ρ tN⁻¹ * ρ tN) := by rw [h3, mul_one]
      _ = (ρ tN * ρ zN * ρ tN⁻¹) * ρ tN := by simp only [mul_assoc]
      _ = (ρ zN) ^ 2 * ρ tN := by rw [h2]
  refine ⟨tN, ⟨γz, hγzc⟩, htT, ht2G, ?_, ?_, ?_⟩
  · exact Subtype.ext hγz3
  · intro h1
    exact hγz1 (congrArg Subtype.val h1)
  · show ρ tN * diagEnd γz = diagEnd (γz ^ 2) * ρ tN
    rw [hpow γz 2, hdz]
    exact hrel

end SixB2

end CFSG.Quasithin.H13
