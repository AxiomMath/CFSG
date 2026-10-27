module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
import CFSG.GroupTheory.GL52.GL4OrderThree
import CFSG.GF2Type.Smith1979.CaseIIExclL52
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Open.StatedZModTwo
import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
import CFSG.GroupTheory.GL52.OrderThreeTwo

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.GroupTheory.GL52

variable {G : Type} [Group G]

private theorem layer_eq_of_normal_quasisimple {Y : Type*} [Group Y] (E : Subgroup Y) [E.Normal]
    (hE : CFSG.IsQuasisimple ↥E) (hsolv : Group.IsSolvable (Y ⧸ E)) : CFSG.layer Y = E := by
  refine le_antisymm (sSup_le fun K hK => ?_)
    (le_sSup ⟨hE, Subgroup.Normal.isSubnormal inferInstance⟩)
  have : Group.IsPerfect ↥K := hK.1.1
  let f : ↥K →* Y ⧸ E := (QuotientGroup.mk' E).comp K.subtype
  have : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have := hsolv
  intro x hx
  by_contra hxE
  have hnt : Nontrivial ↥f.range := by
    refine ⟨⟨⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, 1, fun h => hxE ?_⟩⟩
    have h1 : f ⟨x, hx⟩ = 1 := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff x).mp h1
  exact Group.IsPerfect.not_isSolvable ↥f.range inferInstance

private theorem lay_eq_of_sup {A K C : Subgroup G} (hsup : A ⊔ K = C)
    (hcomm : ∀ a ∈ A, ∀ k ∈ K, a * k = k * a) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    [IsSimpleGroup K] (hK : ∃ a b : K, a * b ≠ b * a) : Lay C = K := by
  have hKC : K ≤ C := le_sup_right.trans hsup.le
  have hAC : A ≤ C := le_sup_left.trans hsup.le
  have hAN : A ≤ Nor K := fun a ha => Subgroup.mem_normalizer_iff.mpr fun k => by
    constructor
    · intro hk
      rw [hcomm a ha k hk, mul_inv_cancel_right]
      exact hk
    · intro hk
      have h1 : a⁻¹ * (a * k * a⁻¹) = a * k * a⁻¹ * a⁻¹ := hcomm a⁻¹ (inv_mem ha) _ hk
      have h2 : a⁻¹ * (a * k * a⁻¹) = k * a⁻¹ := by group
      rw [h2] at h1
      rw [mul_right_cancel h1]
      exact hk
  have hCN : C ≤ Nor K := hsup.ge.trans (sup_le hAN Subgroup.le_normalizer)
  haveI : (K.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr hCN
  let eK : ↥(K.subgroupOf C) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC
  haveI : IsSimpleGroup ↥(K.subgroupOf C) := eK.isSimpleGroup
  have hnab : ∃ a b : ↥(K.subgroupOf C), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hK
    refine ⟨eK.symm a, eK.symm b, fun h => hab ?_⟩
    have := congrArg eK h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  have hE := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  let ψ : ↥(A.subgroupOf C) →* ↥C ⧸ K.subgroupOf C :=
    (QuotientGroup.mk' (K.subgroupOf C)).comp (A.subgroupOf C).subtype
  have hψ : Function.Surjective ψ := by
    have hle : A.subgroupOf C ⊔ K.subgroupOf C ≤
        ψ.range.comap (QuotientGroup.mk' (K.subgroupOf C)) := by
      refine sup_le (fun a ha => Subgroup.mem_comap.mpr ⟨⟨a, ha⟩, rfl⟩) fun k hk =>
        Subgroup.mem_comap.mpr ?_
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]
      exact one_mem _
    rw [← Subgroup.subgroupOf_sup hAC hKC, hsup, Subgroup.subgroupOf_self] at hle
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf C) q
    exact MonoidHom.mem_range.mp (Subgroup.mem_comap.mp (hle (Subgroup.mem_top c)))
  haveI : Group.IsSolvable ↥(A.subgroupOf C) := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subtype.ext (hA _ (Subgroup.mem_subgroupOf.mp a.2) _
      (Subgroup.mem_subgroupOf.mp b.2)))
  have hlay := layer_eq_of_normal_quasisimple (K.subgroupOf C) hE
    (Group.isSolvable_of_surjective hψ)
  show (CFSG.layer ↥C).map C.subtype = K
  rw [hlay, Subgroup.subgroupOf_map_subtype, inf_of_le_left hKC]

private theorem exists_mul_ne_of_not_prime {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ¬ (Nat.card Q).Prime) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := h }
  exact hQ IsSimpleGroup.prime_card

private theorem isLnq_of_equiv_SL2F4 {K : Subgroup G}
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F4) : IsLnq 2 2 2 K :=
  ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, F4, inferInstance, inferInstance,
    card_F4.trans (by norm_num),
    ⟨e.trans (((QuotientGroup.quotientMulEquivOfEq ord3_center_SL2_F4).trans
      QuotientGroup.quotientBot).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F4))⟩⟩

private theorem isLnq_of_equiv_GL3 {K : Subgroup G} (e : K ≃* GL (Fin 3) (ZMod 2)) :
    IsLnq 3 2 1 K :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two le_rfl
    (e.trans (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr
      (CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two (K := ZMod 2) (by simp) 3).symm)))

private theorem cen_symm {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (y : Y) :
    Cen (e.symm y) = (Subgroup.centralizer ({y} : Set Y)).map e.symm.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg e h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  · intro h
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h

private theorem exists_conj_eq_symm {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {τ : Y}
    {x : X} (h : IsConj τ (e x)) : ∃ g : X, g * x * g⁻¹ = e.symm τ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine ⟨e.symm c⁻¹, e.injective ?_⟩
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv]
  rw [← hc]
  group

private theorem conj_ne_symm {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {a b : Y}
    (h : ¬ IsConj a b) (g : X) : g * e.symm a * g⁻¹ ≠ e.symm b := fun hg => by
  refine h (isConj_iff.mpr ⟨e g, ?_⟩)
  have := congrArg e hg
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using this

private theorem exists_conj_subgroup {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {H : Subgroup Y} {y : Y} (hy : y ∈ H) {x : X} (hc : IsConj y (e x)) :
    ∃ K : Subgroup X, x ∈ K ∧ Nonempty (K ≃* H) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  refine ⟨(H.map (MulAut.conj c).toMonoidHom).map e.symm.toMonoidHom, ?_,
    ⟨(e.symm.subgroupMap (H.map (MulAut.conj c).toMonoidHom)).symm.trans
      ((MulAut.conj c).subgroupMap H).symm⟩⟩
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, ← hc]
  exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩

private theorem lay_cen {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {τ : Y} {K : Subgroup Y}
    (hdp : IsInnerDirectProduct (Subgroup.zpowers τ) K (Subgroup.centralizer {τ}))
    [IsSimpleGroup K] (hK : ∃ a b : K, a * b ≠ b * a) :
    Lay (Cen (e.symm τ)) = K.map e.symm.toMonoidHom := by
  obtain ⟨hsup, -, hcomm⟩ := hdp
  let eK : ↥(K.map e.symm.toMonoidHom) ≃* ↥K := (e.symm.subgroupMap K).symm
  haveI : IsSimpleGroup ↥(K.map e.symm.toMonoidHom) := eK.isSimpleGroup
  refine lay_eq_of_sup (A := (Subgroup.zpowers τ).map e.symm.toMonoidHom) ?_ ?_ ?_ ?_
  · rw [cen_symm, ← hsup, Subgroup.map_sup]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha k hk]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← map_mul, ← map_mul, (Commute.zpow_zpow_self τ i j).eq]
  · obtain ⟨a, b, hab⟩ := hK
    refine ⟨eK.symm a, eK.symm b, fun h => hab ?_⟩
    have := congrArg eK h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this

private theorem sylow_facts {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
    {m : ℕ} (hcard : Nat.card Y = 3 ^ 2 * m) (hm : ¬ 3 ∣ m)
    (hY : ∀ R : Sylow 3 Y, Nat.card R = 9 ∧ IsElementaryAbelian 3 (R : Subgroup Y) ∧
      Nat.card (Subgroup.normalizer ((R : Subgroup Y) : Set Y)) = 72)
    (P : Sylow 3 X) :
    IsElemAb 3 2 (P : Subgroup X) ∧ Nat.card (Nor (P : Subgroup X)) = 9 * 8 := by
  classical
  have hP : Nat.card P = 3 ^ 2 := card_sylow_of_card_eq_pow_mul (p := 3) (k := 2) (m := m)
    (by rw [Nat.card_congr e.toEquiv, hcard]) hm P
  obtain ⟨R, hR⟩ := exists_sylow_eq_of_card_pow (p := 3) (k := 2)
    (H := (P : Subgroup X).map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]; exact hP)
    (fun R => by rw [(hY R).1]; norm_num)
  obtain ⟨-, hRe, hRN⟩ := hY R
  have hQP : ((P : Subgroup X).map e.toMonoidHom).map e.symm.toMonoidHom = P := by
    ext x
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
  refine ⟨⟨?_, hP⟩, ?_⟩
  · have hQe : IsElementaryAbelian 3 ↥((P : Subgroup X).map e.toMonoidHom) := by
      rw [← hR]
      exact hRe
    have h := IsElementaryAbelian.subgroup_map hQe e.symm.toMonoidHom
    rwa [hQP] at h
  · have hmap := Subgroup.map_equiv_normalizer_eq (P : Subgroup X) e
    rw [← hR] at hmap
    have h1 := Subgroup.card_map_of_injective (K := Nor (P : Subgroup X)) (f := e.toMonoidHom)
      e.injective
    rw [hmap, hRN] at h1
    omega

private theorem g52_sylow (R : Sylow 3 G52) :
    Nat.card R = 9 ∧ IsElementaryAbelian 3 (R : Subgroup G52) ∧
      Nat.card (Subgroup.normalizer ((R : Subgroup G52) : Set G52)) = 72 := by
  obtain ⟨hR, hRe, -, ⟨hD⟩⟩ := syl3_structure R
  refine ⟨hR, hRe, ?_⟩
  have hN := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((R : Subgroup G52).subgroupOf (Subgroup.normalizer ((R : Subgroup G52) : Set G52)))
  rw [Nat.card_congr hD.toEquiv, DihedralGroup.nat_card,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hR] at hN
  rw [hN]

theorem ff79_1_2_five (X : Type) [Group X] [Finite X] (hX : IsLnq 5 2 1 (⊤ : Subgroup X)) :
    (∀ P : Sylow 3 X, IsElemAb 3 2 (P : Subgroup X)) ∧
    (∀ P : Sylow 3 X, Nat.card (Nor (P : Subgroup X)) = 9 * 8) ∧
    (∃ α β : X, orderOf α = 3 ∧ orderOf β = 3 ∧ (∀ g : X, g * α * g⁻¹ ≠ β) ∧
      (∀ x : X, orderOf x = 3 → (∃ g : X, g * x * g⁻¹ = α) ∨ ∃ g : X, g * x * g⁻¹ = β) ∧
      IsLnq 2 2 2 (Lay (Cen α)) ∧ IsLnq 3 2 1 (Lay (Cen β))) ∧
    ∀ x : X, orderOf x = 3 → ∃ K : Subgroup X, x ∈ K ∧ IsLnq 2 2 2 K := by
  obtain ⟨e₀⟩ :=
    GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two (X := ↥(⊤ : Subgroup X)) (n := 5) hX
  let e : X ≃* G52 := Subgroup.topEquiv.symm.trans e₀
  have hS := sylow_facts e (m := 2 ^ 10 * 5 * 7 * 31) (by rw [card_G52]; ring) (by norm_num)
    g52_sylow
  obtain ⟨e4⟩ := ord3_K4_equiv
  obtain ⟨e2⟩ := ord3_K2_equiv_GL
  haveI := ord3_isSimple_SL2_F4
  haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  haveI : IsSimpleGroup ↥ord3K4 := e4.isSimpleGroup
  haveI : IsSimpleGroup ↥ord3K2 := e2.isSimpleGroup
  have hK4 : ∃ a b : ↥ord3K4, a * b ≠ b * a := exists_mul_ne_of_not_prime (by
    rw [Nat.card_congr e4.toEquiv, ord3_card_SL2_F4]
    norm_num)
  have hK2 : ∃ a b : ↥ord3K2, a * b ≠ b * a := exists_mul_ne_of_not_prime (by
    rw [Nat.card_congr e2.toEquiv, CFSG.ComponentClassification.GHarris.card_GL32_gh]
    norm_num)
  have hord : ∀ x : X, orderOf x = 3 → orderOf (e x) = 3 := fun x hx => by
    rw [MulEquiv.orderOf_eq, hx]
  refine ⟨fun P => (hS P).1, fun P => (hS P).2,
    ⟨e.symm ord3T4, e.symm ord3T2, by rw [MulEquiv.orderOf_eq, orderOf_ord3T4],
      by rw [MulEquiv.orderOf_eq, orderOf_ord3T2], conj_ne_symm e ord3_not_isConj_T4_T2,
      fun x hx => ?_, ?_, ?_⟩, fun x hx => ?_⟩
  ·
    rcases ord3_classify (hord x hx) with ⟨-, hc⟩ | ⟨-, hc⟩
    · exact Or.inr (exists_conj_eq_symm e hc)
    · exact Or.inl (exists_conj_eq_symm e hc)
  · rw [lay_cen e ord3_centralizer_T4 hK4]
    exact isLnq_of_equiv_SL2F4 (K := ord3K4.map e.symm.toMonoidHom)
      ((e.symm.subgroupMap ord3K4).symm.trans e4)
  · rw [lay_cen e ord3_centralizer_T2 hK2]
    exact isLnq_of_equiv_GL3 (K := ord3K2.map e.symm.toMonoidHom)
      ((e.symm.subgroupMap ord3K2).symm.trans e2)
  ·
    rcases ord3_classify (hord x hx) with ⟨-, hc⟩ | ⟨-, hc⟩
    · obtain ⟨y, hyK, -, hy⟩ := ord3_exists_T2_mem_K5
      obtain ⟨K, hxK, ⟨eK⟩⟩ := exists_conj_subgroup e hyK (hy.symm.trans hc)
      obtain ⟨e5⟩ := ord3_K5_equiv
      exact ⟨K, hxK, isLnq_of_equiv_SL2F4 (eK.trans e5)⟩
    · obtain ⟨y, hyK, -, hy⟩ := ord3_exists_T4_mem_K4
      obtain ⟨K, hxK, ⟨eK⟩⟩ := exists_conj_subgroup e hyK (hy.symm.trans hc)
      exact ⟨K, hxK, isLnq_of_equiv_SL2F4 (eK.trans e4)⟩

theorem ff79_1_2_four (X : Type) [Group X] [Finite X] (hX : IsLnq 4 2 1 (⊤ : Subgroup X)) :
    (∀ P : Sylow 3 X, IsElemAb 3 2 (P : Subgroup X)) ∧
    (∀ P : Sylow 3 X, Nat.card (Nor (P : Subgroup X)) = 9 * 8) ∧
    (∃ α β : X, orderOf α = 3 ∧ orderOf β = 3 ∧ (∀ g : X, g * α * g⁻¹ ≠ β) ∧
      (∀ x : X, orderOf x = 3 → (∃ g : X, g * x * g⁻¹ = α) ∨ ∃ g : X, g * x * g⁻¹ = β) ∧
      IsLnq 2 2 2 (Lay (Cen α))) ∧
    ∀ x : X, orderOf x = 3 → ∃ K : Subgroup X, x ∈ K ∧ IsLnq 2 2 2 K := by
  obtain ⟨e₀⟩ :=
    GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two (X := ↥(⊤ : Subgroup X)) (n := 4) hX
  let e : X ≃* G42 := Subgroup.topEquiv.symm.trans e₀
  have hS := sylow_facts e (m := 2 ^ 6 * 5 * 7) (by rw [card_G42]; ring) (by norm_num)
    gl4_syl3_structure
  obtain ⟨e4⟩ := gl4_K4_equiv
  obtain ⟨e5⟩ := gl4_K5_equiv
  haveI := ord3_isSimple_SL2_F4
  haveI : IsSimpleGroup ↥gl4K4 := e4.isSimpleGroup
  have hK4 : ∃ a b : ↥gl4K4, a * b ≠ b * a := exists_mul_ne_of_not_prime (by
    rw [Nat.card_congr e4.toEquiv, ord3_card_SL2_F4]
    norm_num)
  have hord : ∀ x : X, orderOf x = 3 → orderOf (e x) = 3 := fun x hx => by
    rw [MulEquiv.orderOf_eq, hx]
  refine ⟨fun P => (hS P).1, fun P => (hS P).2,
    ⟨e.symm gl4Al, e.symm gl4A, by rw [MulEquiv.orderOf_eq, orderOf_gl4Al],
      by rw [MulEquiv.orderOf_eq, orderOf_gl4A], conj_ne_symm e gl4_not_isConj_Al_A,
      fun x hx => ?_, ?_⟩, fun x hx => ?_⟩
  ·
    rcases gl4_ord3_classify (hord x hx) with hc | hc
    · exact Or.inr (exists_conj_eq_symm e hc)
    · exact Or.inl (exists_conj_eq_symm e hc)
  · rw [lay_cen e gl4_centralizer_Al hK4]
    exact isLnq_of_equiv_SL2F4 (K := gl4K4.map e.symm.toMonoidHom)
      ((e.symm.subgroupMap gl4K4).symm.trans e4)
  ·
    rcases gl4_ord3_classify (hord x hx) with hc | hc
    · obtain ⟨y, hyK, hy⟩ := gl4_exists_A_mem_K5
      obtain ⟨K, hxK, ⟨eK⟩⟩ := exists_conj_subgroup e hyK (hy.symm.trans hc)
      exact ⟨K, hxK, isLnq_of_equiv_SL2F4 (eK.trans e5)⟩
    · obtain ⟨y, hyK, hy⟩ := gl4_exists_Al_mem_K4
      obtain ⟨K, hxK, ⟨eK⟩⟩ := exists_conj_subgroup e hyK (hy.symm.trans hc)
      exact ⟨K, hxK, isLnq_of_equiv_SL2F4 (eK.trans e4)⟩

theorem ff79_1_2_holds :
    ∀ (X : Type) [Group X] [Finite X] (n : ℕ), (n = 4 ∨ n = 5) → IsLnq n 2 1 (⊤ : Subgroup X) →
      (∀ P : Sylow 3 X, IsElemAb 3 2 (P : Subgroup X)) ∧
      (∀ P : Sylow 3 X, Nat.card (Nor (P : Subgroup X)) = 9 * 8) ∧
      (∃ α β : X, orderOf α = 3 ∧ orderOf β = 3 ∧ (∀ g : X, g * α * g⁻¹ ≠ β) ∧
        (∀ x : X, orderOf x = 3 → (∃ g : X, g * x * g⁻¹ = α) ∨ ∃ g : X, g * x * g⁻¹ = β) ∧
        IsLnq 2 2 2 (Lay (Cen α)) ∧ (n = 5 → IsLnq 3 2 1 (Lay (Cen β)))) ∧
      ∀ x : X, orderOf x = 3 → ∃ K : Subgroup X, x ∈ K ∧ IsLnq 2 2 2 K := by
  intro X _ _ n hn hX
  rcases hn with rfl | rfl
  · obtain ⟨h1, h2, ⟨α, β, h3, h4, h5, h6, h7⟩, h8⟩ := ff79_1_2_four X hX
    exact ⟨h1, h2, ⟨α, β, h3, h4, h5, h6, h7, fun h => absurd h (by norm_num)⟩, h8⟩
  · obtain ⟨h1, h2, ⟨α, β, h3, h4, h5, h6, h7, h7'⟩, h8⟩ := ff79_1_2_five X hX
    exact ⟨h1, h2, ⟨α, β, h3, h4, h5, h6, h7, fun _ => h7'⟩, h8⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
