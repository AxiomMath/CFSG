module

public import CFSG.Quasithin.Vol2.Ch10SecC8Q
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem mem_pCoreOf_of_commutator_mem {x : G} (hxL : x ∈ L)
    (hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hnab : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a)
    (h : ∀ y ∈ L, ⁅x, y⁆ ∈ pCoreOf 2 L) : x ∈ pCoreOf 2 L := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimp
        (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) inferInstance with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center _ := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hc : π ⟨x, hxL⟩ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hy := h y y.2
    obtain ⟨w, hw, hwe⟩ := hy
    have hw' : w ∈ CFSG.pCore 2 ↥L := by exact hw
    have hwe' : w = ⁅(⟨x, hxL⟩ : ↥L), y⁆ := Subtype.ext hwe
    have h1 : π ⁅(⟨x, hxL⟩ : ↥L), y⁆ = 1 := by
      rw [← hwe']
      exact (QuotientGroup.eq_one_iff w).mpr hw'
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
  exact ⟨_, hc, rfl⟩

theorem not_thompsonJ_le_centralizer (hyp : Hyp10 G T L I) (h3210 : TmpL6_3_2_10_nine)
    (hcv : fsuCVM T L I ≠ ⊥) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  intro hJ
  obtain ⟨z, hzC, hz1, -, -, hzZ⟩ := exists_mem_center_fsuCVM hyp hcv
  have hzbot : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ := by
    by_cases hs : Sub326iii T L I
    · exact (h3210 G T L I (fsuVM T L I) hyp.fsu (Or.inl ⟨hs, rfl⟩) hJ).1
    · exact (h3210 G T L I (fsuV T I) hyp.fsu (Or.inr ⟨hs, rfl⟩)
        (hJ.trans (Subgroup.centralizer_le (SecA.fsuV_le_fsuVM T L I)))).1
  have hz : z ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) :=
    ⟨hzZ, hzC.2⟩
  rw [hzbot, Subgroup.mem_bot] at hz
  exact hz1 hz

omit [Finite G] in
theorem conj_commutatorElement_eq {s v l c o : G} (hv : s * v * s⁻¹ = c * v)
    (hl : s * l * s⁻¹ = o * l) (hcl : Commute c l) (hco : Commute c o) (hcv : Commute c v)
    (hov : Commute o v) (hoW : Commute o ⁅v, l⁆) : s * ⁅v, l⁆ * s⁻¹ = ⁅v, l⁆ := by
  have h1 : s * ⁅v, l⁆ * s⁻¹ =
      (s * v * s⁻¹) * (s * l * s⁻¹) * (s * v * s⁻¹)⁻¹ * (s * l * s⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h1, hv, hl]
  have hcX : Commute c (o * l) := hco.mul_right hcl
  have h2 : c * v * (o * l) * (c * v)⁻¹ * (o * l)⁻¹ = v * (o * l) * v⁻¹ * (o * l)⁻¹ := by
    have e1 : c * v * (o * l) * (c * v)⁻¹ = c * (v * (o * l) * v⁻¹) * c⁻¹ := by group
    have e2 : c * (v * (o * l) * v⁻¹) = (v * (o * l) * v⁻¹) * c :=
      ((hcv.mul_right hcX).mul_right hcv.inv_right).eq
    rw [e1, e2]
    group
  rw [h2]
  have h3 : v * (o * l) * v⁻¹ * (o * l)⁻¹ = o * ⁅v, l⁆ * o⁻¹ := by
    rw [commutatorElement_def]
    have e : v * o = o * v := hov.eq.symm
    calc v * (o * l) * v⁻¹ * (o * l)⁻¹ = (v * o) * l * v⁻¹ * l⁻¹ * o⁻¹ := by group
      _ = (o * v) * l * v⁻¹ * l⁻¹ * o⁻¹ := by rw [e]
      _ = o * (v * l * v⁻¹ * l⁻¹) * o⁻¹ := by group
  rw [h3, hoW.eq]
  group

theorem pCoreOf_L_le_centralizer (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1) :
    pCoreOf 2 L ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  obtain ⟨hVM, hR, -, -⟩ := h1011 G T L I hyp
  refine pCoreOf_le_centralizer_of_subnormal hR hVM ?_
  exact IsSubnormal.step (SecA.le_fsuL0 T L) (SecA.normal_fsuL0 hyp.fsu.maximal.1)
    (IsSubnormal.step Subgroup.le_normalizer Subgroup.normal_in_normalizer (IsSubnormal.refl _))

theorem mem_centralizer_fsuUL_of (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h3 : Case10_1_1Three T L I) {s : G} (hs : s ∈ T1 T L)
    (hsL : ∀ y ∈ L, ⁅y, s⁆ ∈ pCoreOf 2 L) :
    s ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
  obtain ⟨x₀, hx₀L, hA, hB⟩ := SecB.inner_of_case3 hyp h3 hs
  have hsimp := SecB.isSimpleGroup_of_LBarL32 h3.1
  have hO := pCoreOf_L_le_centralizer hyp h1011
  have hV1V : fsuUL T L I ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hsy : ∀ y ∈ L, s * y * s⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
    intro y hy
    have h := (pCoreOf 2 L).inv_mem (hsL y hy)
    rw [commutatorElement_def] at h
    convert h using 1
    group
  have hx₀ : x₀ ∈ pCoreOf 2 L := by
    refine mem_pCoreOf_of_commutator_mem hx₀L hsimp
      (nonabelian_of_isQuasisimple hyp.fsu.quasisimple) fun y hy => ?_
    have ha := hA y hy
    have hb := hsy y hy
    have : ⁅x₀, y⁆ = (s * y * s⁻¹ * (x₀ * y * x₀⁻¹)⁻¹)⁻¹ * (s * y * s⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact (pCoreOf 2 L).mul_mem ((pCoreOf 2 L).inv_mem ha) hb
  have hx₀V := hO hx₀
  have hsv : ∀ v ∈ fsuUL T L I, s * v * s⁻¹ * v⁻¹ ∈ fsuCVM T L I := by
    intro v hv
    have h := hB v hv
    have hc : x₀ * v * x₀⁻¹ = v := by
      rw [← Subgroup.mem_centralizer_iff.mp hx₀V v (hV1V hv)]
      group
    rwa [hc] at h
  have hgen : ⁅fsuUL T L I, L⁆ ≤ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    set c := s * v * s⁻¹ * v⁻¹
    set o := s * l * s⁻¹ * l⁻¹
    have hc : c ∈ fsuCVM T L I := hsv v hv
    have ho : o ∈ pCoreOf 2 L := hsy l hl
    have hW : ⁅v, l⁆ ∈ fsuVM T L I :=
      hV1V ((commutator_fsuUL_eq hyp) ▸ Subgroup.commutator_mem_commutator hv hl)
    have hcomm := conj_commutatorElement_eq (s := s) (v := v) (l := l) (c := c) (o := o)
      (by simp only [c]; group) (by simp only [o]; group)
      (Subgroup.mem_centralizer_iff.mp hc.2 l (SecA.le_fsuL0 T L hl)).symm
      (Subgroup.mem_centralizer_iff.mp (hO ho) c hc.1)
      (congrArg Subtype.val ((SecA.isElemAbelian_fsuVM hyp).1.is_comm.comm ⟨c, hc.1⟩
        ⟨v, hV1V hv⟩))
      (Subgroup.mem_centralizer_iff.mp (hO ho) v (hV1V hv)).symm
      (Subgroup.mem_centralizer_iff.mp (hO ho) _ hW).symm
    calc s * ⁅v, l⁆ = s * ⁅v, l⁆ * s⁻¹ * s := by group
      _ = ⁅v, l⁆ * s := by rw [hcomm]
  have hcomm := commutator_fsuUL_eq hyp
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : v ∈ ⁅fsuUL T L I, L⁆ := by rw [hcomm]; exact hv
  exact (Subgroup.mem_centralizer_iff.mp (hgen hv') s rfl).symm

theorem eq_commutator_thompsonJ (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h3 : Case10_1_1Three T L I) (h3210 : TmpL6_3_2_10_nine)
    (hcv : fsuCVM T L I ≠ ⊥) : L = ⁅L, thompsonJ T⁆ := by
  have hJT1 : thompsonJ T ≤ T1 T L := (h1012 G T L I hyp).2.1
  have hNL : ⁅L, thompsonJ T⁆ ≤ L := commutator_le_left_of_le_normalizer (hJT1.trans inf_le_right)
  have hLN : L ≤ Subgroup.normalizer ((⁅L, thompsonJ T⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left L (thompsonJ T)
  rcases le_pCoreOf_or_eq_of_normal hyp.fsu.faithful.1.2.1.2.1
      (SecB.isSimpleGroup_of_LBarL32 h3.1) hNL hLN with h | h
  · exfalso
    apply not_thompsonJ_le_centralizer hyp h3210 hcv
    obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
    obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
    obtain ⟨hVeq, -, -, -⟩ := hdec t ht htn
    have hV1 : ∀ s ∈ thompsonJ T, s ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
      intro s hs
      refine mem_centralizer_fsuUL_of hyp h1011 h3 (hJT1 hs) fun y hy => ?_
      exact h (Subgroup.commutator_mem_commutator hy hs)
    have hTJ : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
    intro s hs
    rw [hVeq]
    refine mem_centralizer_sup (hV1 s hs) ?_
    rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx : t * x * t⁻¹ ∈ fsuUL T L I := SecA.mem_conjugate_iff.mp hx
    have hts : t * s * t⁻¹ ∈ thompsonJ T := (Subgroup.mem_normalizer_iff.mp (hTJ ht) s).mp hs
    have hc := Subgroup.mem_centralizer_iff.mp (hV1 _ hts) _ hx
    have e1 : x * s = t⁻¹ * ((t * x * t⁻¹) * (t * s * t⁻¹)) * t := by group
    have e2 : s * x = t⁻¹ * ((t * s * t⁻¹) * (t * x * t⁻¹)) * t := by group
    rw [e1, e2, hc]
  · exact h.symm

end CFSG.Quasithin.Vol2.Ch10.SecC
