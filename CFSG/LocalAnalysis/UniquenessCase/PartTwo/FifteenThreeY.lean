module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def RSimple153 : Prop :=
  ∀ (V : Type) [CommGroup V] (X : Type) [Group X] [Finite X]
    (K : Subgroup (MulAut V)) (Z : Subgroup V), s15KNatPerf X K Z →
      CFSG.Open.IsQuasisimple X ∧ Subgroup.center X = ⊥

@[expose] noncomputable def s15XBar (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (K₀ : Subgroup G) : Subgroup (MulAut (Vtil V₀ V hV)) :=
  ⨆ m ∈ D.M, barSub V₀ V hV (conjSubgroup K₀ m)

section Apply

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

private theorem s15_Three_le_stabTil (h : Hyp151 D V₀ V L) : D.M ≤ stabTil V₀ V :=
  le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀

private theorem s15_Three_conjSubgroup_le {D : Data G} {K : Subgroup G} (hK : K ≤ D.M)
    {m : G} (hm : m ∈ D.M) : conjSubgroup K m ≤ D.M := by
  intro x hx
  rw [conjSubgroup, Subgroup.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  show (MulAut.conj m⁻¹) k ∈ D.M
  rw [MulAut.conj_apply, inv_inv]
  exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hm) (hK hk)) hm

private theorem s15_Three_map_conj_mul {A : Type} [Group A] (H : Subgroup A) (φ ψ : A) :
    (H.map (MulAut.conj φ).toMonoidHom).map (MulAut.conj ψ).toMonoidHom =
      H.map (MulAut.conj (ψ * φ)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem s15_Three_le_normalizer_of_comm {A : Type} [Group A] {S T : Subgroup A}
    (h : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x) : S ≤ normalizer (T : Set A) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer (T : Set A))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (h x hx y hy).symm

theorem s15_Three_barSub_conj_eq (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil V₀ V)
    (hK : K₀ ≤ D.M) {m : G} (hm : m ∈ D.M) :
    barSub V₀ V hV (conjSubgroup K₀ m) =
      (barSub V₀ V hV K₀).map
        (MulAut.conj (actTil V₀ V hV ⟨m⁻¹, hMs (D.M.inv_mem hm)⟩)).toMonoidHom := by
  exact TwelveTwentyThree.barSub_map_conj hV (hK.trans hMs) (hMs (D.M.inv_mem hm))

theorem s15_Three_mem_nBar (hV : IsElemAbelian 2 V) {m : G} :
    m ∈ nBar D.M V₀ V hV L ↔ m ∈ D.M ∧ ∃ h : m ∈ stabTil V₀ V,
      actTil V₀ V hV ⟨m, h⟩ ∈ normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
  unfold nBar
  exact mem_preBarSub D.M V₀ V hV _

theorem s15_Three_mul_comm_of_commutator_eq_bot {A : Type} [Group A] {S T : Subgroup A}
    (h : ⁅S, T⁆ = ⊥) : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x := by
  intro x hx y hy
  have h1 : ⁅x, y⁆ ∈ ⁅S, T⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

private theorem s15_Three_barSub_conj_map_eq' (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) {X : Subgroup G} (hX : X ≤ D.M)
    {m : G} (hm : m ∈ D.M) (m₀ : ↥(stabTil V₀ V)) (hm₀ : (m₀ : G) ∈ D.M) :
    (barSub V₀ V hV (conjSubgroup X m)).map
        (MulAut.conj (actTil V₀ V hV m₀)).toMonoidHom =
      barSub V₀ V hV (conjSubgroup X (m * (m₀ : G)⁻¹)) := by
  ext φ
  rw [Subgroup.mem_map, mem_barSub]
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨a, haY, rfl⟩ := (mem_barSub V₀ V hV _ ψ).1 hψ
    refine ⟨m₀ * a * m₀⁻¹, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff] at haY ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      convert haY using 1
      group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  · rintro ⟨a, ha, haeq⟩
    refine ⟨actTil V₀ V hV (m₀⁻¹ * a * m₀), ?_, ?_⟩
    · refine (mem_barSub V₀ V hV _ _).2 ⟨m₀⁻¹ * a * m₀, ?_, rfl⟩
      rw [mem_conjSubgroup_iff] at ha ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      convert ha using 1
      group
    · rw [← haeq]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      group

private theorem s15_Three_iSup_barSub_conj_eq (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) {X : Subgroup G} (hX : X ≤ D.M)
    (m₀ : ↥(stabTil V₀ V)) (hm₀ : (m₀ : G) ∈ D.M) :
    (⨆ m ∈ D.M, barSub V₀ V hV (conjSubgroup X m)).map
        (MulAut.conj (actTil V₀ V hV m₀)).toMonoidHom =
      ⨆ m ∈ D.M, barSub V₀ V hV (conjSubgroup X m) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_iSup]
    refine iSup_le fun m => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hm => ?_
    rw [s15_Three_barSub_conj_map_eq' hV hMs hX hm m₀ hm₀]
    exact le_iSup₂_of_le (m * (m₀ : G)⁻¹) (D.M.mul_mem hm (D.M.inv_mem hm₀)) le_rfl
  · refine iSup_le fun m => iSup_le fun hm => ?_
    have heq := s15_Three_barSub_conj_map_eq' hV hMs hX (D.M.mul_mem hm hm₀) m₀ hm₀
    rw [show (m * (m₀ : G)) * (m₀ : G)⁻¹ = m by group] at heq
    rw [← heq]
    exact Subgroup.map_mono (le_iSup₂_of_le (m * (m₀ : G)) (D.M.mul_mem hm hm₀) le_rfl)

private theorem s15_Three_comm_map_conj {A : Type} [Group A] {S T : Subgroup A} (φ : A ≃* A)
    (h : S = T ∨ ∀ x ∈ S, ∀ y ∈ T, x * y = y * x) :
    S.map φ.toMonoidHom = T.map φ.toMonoidHom ∨
      ∀ x ∈ S.map φ.toMonoidHom, ∀ y ∈ T.map φ.toMonoidHom, x * y = y * x := by
  rcases h with h | h
  · left; rw [h]
  · right
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, h s hs t ht]

theorem s15_Three_xbar_le (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) :
    s15XBar D V₀ V hV K₀ ≤ Mbar D.M V₀ V hV := by
  refine iSup₂_le fun m hm => ?_
  exact barSub_mono V₀ V hV (s15_Three_conjSubgroup_le (hshape.1.trans h.le) hm)

theorem s15_Three_xbar_comm (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) {m₁ m₂ : G} (h₁ : m₁ ∈ D.M) (h₂ : m₂ ∈ D.M) :
    barSub V₀ V hV (conjSubgroup K₀ m₁) = barSub V₀ V hV (conjSubgroup K₀ m₂) ∨
      ∀ x ∈ barSub V₀ V hV (conjSubgroup K₀ m₁), ∀ y ∈ barSub V₀ V hV (conjSubgroup K₀ m₂),
        x * y = y * x := by
  have hMs : D.M ≤ stabTil V₀ V := s15_Three_le_stabTil h
  set g : G := m₂ * m₁⁻¹ with hgdef
  have hg : g ∈ D.M := D.M.mul_mem h₂ (D.M.inv_mem h₁)
  set μ₁ : MulAut (Vtil V₀ V hV) :=
    actTil V₀ V hV ⟨m₁⁻¹, hMs (D.M.inv_mem h₁)⟩ with hμ₁def
  set μ₂ : MulAut (Vtil V₀ V hV) :=
    actTil V₀ V hV ⟨m₂⁻¹, hMs (D.M.inv_mem h₂)⟩ with hμ₂def
  set n : MulAut (Vtil V₀ V hV) :=
    actTil V₀ V hV ⟨g⁻¹, hMs (D.M.inv_mem hg)⟩ with hndef
  set B : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV (conjSubgroup K₀ g) with hBdef
  have hB : B = (barSub V₀ V hV K₀).map (MulAut.conj n).toMonoidHom := by
    rw [hBdef, hndef]
    exact s15_Three_barSub_conj_eq hV hMs (hshape.1.trans h.le) hg
  have hpair : barSub V₀ V hV K₀ = B ∨
      ∀ x ∈ barSub V₀ V hV K₀, ∀ y ∈ B, x * y = y * x := by
    by_cases hgn : g ∈ nBar D.M V₀ V hV L
    · have hBmem : B ∈ conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L) := by
        refine ⟨n, ⟨?_, ?_⟩, hB⟩
        · rw [hndef]
          exact actTil_mem_barSub V₀ V hV (D.M.inv_mem hg) (hMs (D.M.inv_mem hg))
        · obtain ⟨-, hgs, hnorm⟩ :=
            (s15_Three_mem_nBar (D := D) (V := V) (V₀ := V₀) (L := L) (m := g) hV).1 hgn
          rw [hndef]
          have h1 : actTil V₀ V hV ⟨g⁻¹, hMs (D.M.inv_mem hg)⟩ =
              (actTil V₀ V hV ⟨g, hgs⟩)⁻¹ := by
            rw [show (⟨g⁻¹, hMs (D.M.inv_mem hg)⟩ : ↥(stabTil V₀ V)) = ⟨g, hgs⟩⁻¹ from
              Subtype.ext rfl, map_inv]
          rw [h1]
          exact (normalizer _).inv_mem hnorm
      have hKmem : barSub V₀ V hV K₀ ∈
          conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L) :=
        ⟨1, (s15NBar D V₀ V hV L).one_mem, by ext x; simp⟩
      by_cases hBeq : B = barSub V₀ V hV K₀
      · left; exact hBeq.symm
      · right
        have hcomm : ⁅B, barSub V₀ V hV K₀⁆ = ⊥ :=
          hshape.2.2.1.2.2.1 B hBmem (barSub V₀ V hV K₀) hKmem hBeq
        intro x hx y hy
        exact (s15_Three_mul_comm_of_commutator_eq_bot hcomm y hy x hx).symm
    · right
      have hKB : barSub V₀ V hV K₀ ≤ barSub V₀ V hV L := barSub_mono V₀ V hV hshape.1
      have hBsub : B ≤ barSub V₀ V hV (conjSubgroup L g) := by
        rw [hBdef]
        exact barSub_mono V₀ V hV (Subgroup.map_mono hshape.1)
      have hcommL : ⁅barSub V₀ V hV L, barSub V₀ V hV (conjSubgroup L g)⁆ = ⊥ :=
        (h.commute g hg hgn).1
      have hcomm : ⁅barSub V₀ V hV K₀, B⁆ = ⊥ := by
        have hmono := Subgroup.commutator_mono hKB hBsub
        rw [hcommL] at hmono
        exact le_bot_iff.1 hmono
      intro x hx y hy
      exact s15_Three_mul_comm_of_commutator_eq_bot hcomm x hx y hy
  have hA₁ : (barSub V₀ V hV K₀).map (MulAut.conj μ₁).toMonoidHom =
      barSub V₀ V hV (conjSubgroup K₀ m₁) := by
    rw [hμ₁def]
    exact (s15_Three_barSub_conj_eq hV hMs (hshape.1.trans h.le) h₁).symm
  have hmun : μ₁ * n = μ₂ := by
    rw [hμ₁def, hndef, hμ₂def]
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show m₁⁻¹ * g⁻¹ = m₂⁻¹
    rw [hgdef]
    group
  have hA₂ : B.map (MulAut.conj μ₁).toMonoidHom =
      barSub V₀ V hV (conjSubgroup K₀ m₂) := by
    rw [hB, s15_Three_map_conj_mul, hmun]
    exact (s15_Three_barSub_conj_eq hV hMs (hshape.1.trans h.le) h₂).symm
  rcases s15_Three_comm_map_conj (MulAut.conj μ₁) hpair with hcase | hcase
  · left
    simpa only [← hA₁, ← hA₂] using hcase
  · right
    simpa only [← hA₁, ← hA₂] using hcase

private theorem s15_Three_comp_normal_xbar (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) {m : G} (hm : m ∈ D.M) :
    ((barSub V₀ V hV (conjSubgroup K₀ m)).subgroupOf (s15XBar D V₀ V hV K₀)).Normal := by
  have hle : barSub V₀ V hV (conjSubgroup K₀ m) ≤ s15XBar D V₀ V hV K₀ :=
    le_iSup₂_of_le m hm le_rfl
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  refine iSup₂_le fun m' hm' => ?_
  rcases s15_Three_xbar_comm h hV hshape hm' hm with heq | hcomm
  · rw [heq]; exact Subgroup.le_normalizer
  · exact s15_Three_le_normalizer_of_comm hcomm

private theorem s15_Three_isQuasisimple_conj (hV : IsElemAbelian 2 V) (h : Hyp151 D V₀ V L)
    (hq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV K₀)) {m : G} (hm : m ∈ D.M)
    (hK : K₀ ≤ D.M) :
    CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV (conjSubgroup K₀ m)) := by
  have hMs : D.M ≤ stabTil V₀ V := s15_Three_le_stabTil h
  rw [s15_Three_barSub_conj_eq hV hMs hK hm]
  exact CFSG.Open.IsQuasisimple.of_mulEquiv
    ((barSub V₀ V hV K₀).equivMapOfInjective _ (MulAut.conj _).injective).symm hq

private theorem s15_Three_xbar_map_conj (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) {μ : MulAut (Vtil V₀ V hV)}
    (hμ : μ ∈ Mbar D.M V₀ V hV) :
    (s15XBar D V₀ V hV K₀).map (MulAut.conj μ).toMonoidHom = s15XBar D V₀ V hV K₀ := by
  have hMs : D.M ≤ stabTil V₀ V := s15_Three_le_stabTil h
  obtain ⟨m₀, hm₀, rfl⟩ := (mem_barSub V₀ V hV D.M μ).1 hμ
  exact s15_Three_iSup_barSub_conj_eq hV hMs (hshape.1.trans h.le) m₀ hm₀

private theorem s15_Three_kbar_normal_lbar (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) :
    ((barSub V₀ V hV K₀).subgroupOf (lBar V₀ V hV L)).Normal := by
  have hKmem : barSub V₀ V hV K₀ ∈ conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L) :=
    ⟨1, (s15NBar D V₀ V hV L).one_mem, by ext x; simp⟩
  have hle : barSub V₀ V hV K₀ ≤ lBar V₀ V hV L := by
    rw [← hshape.2.2.1.2.1]
    exact le_iSup₂_of_le (barSub V₀ V hV K₀) hKmem le_rfl
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  rw [← hshape.2.2.1.2.1]
  refine iSup₂_le fun Y hY => ?_
  by_cases hYeq : Y = barSub V₀ V hV K₀
  · rw [hYeq]; exact Subgroup.le_normalizer
  · exact s15_Three_le_normalizer_of_comm
      (s15_Three_mul_comm_of_commutator_eq_bot
        (hshape.2.2.1.2.2.1 Y hY (barSub V₀ V hV K₀) hKmem hYeq))

private theorem s15_Three_lbar_normal_conj (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    ((lBar V₀ V hV L).subgroupOf (⨆ m ∈ D.M, barSub V₀ V hV (conjSubgroup L m))).Normal := by
  have hMs : D.M ≤ stabTil V₀ V := s15_Three_le_stabTil h
  have hL1 : barSub V₀ V hV (conjSubgroup L (1 : G)) = lBar V₀ V hV L := by
    have hconj : conjSubgroup L (1 : G) = L := by
      rw [conjSubgroup, inv_one, map_one]
      exact Subgroup.map_id L
    rw [hconj, lBar]
  have hle : lBar V₀ V hV L ≤ ⨆ m ∈ D.M, barSub V₀ V hV (conjSubgroup L m) := by
    rw [← hL1]
    exact le_iSup₂_of_le (1 : G) D.M.one_mem le_rfl
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  refine iSup₂_le fun m hm => ?_
  by_cases hmn : m ∈ nBar D.M V₀ V hV L
  · obtain ⟨-, hgs, hnorm⟩ :=
      (s15_Three_mem_nBar (D := D) (V := V) (V₀ := V₀) (L := L) (m := m) hV).1 hmn
    have hnorm_inv : actTil V₀ V hV ⟨m⁻¹, hMs (D.M.inv_mem hm)⟩ ∈
        normalizer ((barSub V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) : Set _) := by
      have h1 : actTil V₀ V hV ⟨m⁻¹, hMs (D.M.inv_mem hm)⟩ =
          (actTil V₀ V hV ⟨m, hgs⟩)⁻¹ := by
        rw [show (⟨m⁻¹, hMs (D.M.inv_mem hm)⟩ : ↥(stabTil V₀ V)) = ⟨m, hgs⟩⁻¹ from
          Subtype.ext rfl, map_inv]
      rw [h1]
      exact (normalizer _).inv_mem hnorm
    rw [s15_Three_barSub_conj_eq hV hMs h.le hm]
    refine Subgroup.map_le_iff_le_comap.2 fun y hy => ?_
    exact (normalizer _).mul_mem
      ((normalizer _).mul_mem hnorm_inv (Subgroup.le_normalizer hy))
      ((normalizer _).inv_mem hnorm_inv)
  · have hcommL : ⁅barSub V₀ V hV L, barSub V₀ V hV (conjSubgroup L m)⁆ = ⊥ :=
      (h.commute m hm hmn).1
    exact s15_Three_le_normalizer_of_comm fun x hx y hy =>
      (s15_Three_mul_comm_of_commutator_eq_bot hcommL y hy x hx).symm

private theorem s15_Three_conj_normal_Mbar (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    ((⨆ m ∈ D.M, barSub V₀ V hV (conjSubgroup L m)).subgroupOf
      (Mbar D.M V₀ V hV)).Normal := by
  have hMs : D.M ≤ stabTil V₀ V := s15_Three_le_stabTil h
  have hle : (⨆ m ∈ D.M, barSub V₀ V hV (conjSubgroup L m)) ≤ Mbar D.M V₀ V hV :=
    iSup₂_le fun m hm => barSub_mono V₀ V hV (s15_Three_conjSubgroup_le h.le hm)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro μ hμ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  obtain ⟨m₀, hm₀, rfl⟩ := (mem_barSub V₀ V hV D.M μ).1 hμ
  exact s15_Three_iSup_barSub_conj_eq hV hMs h.le m₀ hm₀

theorem s15_Three_kbar_component (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) (hq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV K₀)) :
    CFSG.Open.IsComponentOf (barSub V₀ V hV K₀) (Mbar D.M V₀ V hV) := by
  have hKM : barSub V₀ V hV K₀ ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV (hshape.1.trans h.le)
  have hL1 : barSub V₀ V hV (conjSubgroup L (1 : G)) = lBar V₀ V hV L := by
    have hconj : conjSubgroup L (1 : G) = L := by
      rw [conjSubgroup, inv_one, map_one]
      exact Subgroup.map_id L
    rw [hconj, lBar]
  have hLGL : lBar V₀ V hV L ≤ ⨆ m ∈ D.M, barSub V₀ V hV (conjSubgroup L m) := by
    rw [← hL1]
    exact le_iSup₂_of_le (1 : G) D.M.one_mem le_rfl
  have hGLM : (⨆ m ∈ D.M, barSub V₀ V hV (conjSubgroup L m)) ≤ Mbar D.M V₀ V hV :=
    iSup₂_le fun m hm => barSub_mono V₀ V hV (s15_Three_conjSubgroup_le h.le hm)
  refine ⟨hKM, ?_, hq⟩
  exact (CFSG.Open.IsSubnormal.step (barSub_mono V₀ V hV hshape.1)
      (s15_Three_kbar_normal_lbar hV hshape) (CFSG.Open.IsSubnormal.refl _)).trans
    ((CFSG.Open.IsSubnormal.step hLGL (s15_Three_lbar_normal_conj h hV)
      (CFSG.Open.IsSubnormal.refl _)).trans
    (CFSG.Open.IsSubnormal.step hGLM (s15_Three_conj_normal_Mbar h hV)
      (CFSG.Open.IsSubnormal.refl _)))

theorem s15_Three_xbar_layer (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) (hq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV K₀)) :
    rankThreeLayer (s15XBar D V₀ V hV K₀) = s15XBar D V₀ V hV K₀ := by
  refine le_antisymm ?_ ?_
  · rw [rankThreeLayer]
    exact sSup_le fun _ hL => hL.1
  · rw [rankThreeLayer]
    refine iSup₂_le fun m hm => ?_
    refine le_sSup ?_
    refine ⟨le_iSup₂_of_le m hm le_rfl, ?_, ?_⟩
    · exact CFSG.Open.IsSubnormal.step (le_iSup₂_of_le m hm le_rfl)
        (s15_Three_comp_normal_xbar h hV hshape hm) (CFSG.Open.IsSubnormal.refl _)
    · exact s15_Three_isQuasisimple_conj hV h hq hm (hshape.1.trans h.le)

theorem s15_Three_xbar_normal (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) :
    ((s15XBar D V₀ V hV K₀).subgroupOf (Mbar D.M V₀ V hV)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (s15_Three_xbar_le h hV hshape)]
  intro μ hμ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact s15_Three_xbar_map_conj h hV hshape hμ

end Apply

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
