module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Good
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineEngine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_perfect_le_centralizer_of_comm_mem {K V₀ : Subgroup G} {w : G} (hperf : ⁅K, K⁆ = K)
    (hV₀ : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a) (hKV₀ : K ≤ centralizer (V₀ : Set G))
    (hw2 : w ^ 2 = 1) (hKw : ∀ k ∈ K, k * w * k⁻¹ * w⁻¹ ∈ V₀) :
    K ≤ centralizer ({w} : Set G) := by
  have hz : ∀ v ∈ Subgroup.zpowers w, v = 1 ∨ v = w := by
    intro v hv
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    have h2 : w ^ (2 : ℤ) = 1 := by exact_mod_cast hw2
    rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, h2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  have h := ElevenNine.le_centralizer_of_perfect_of_sub (V := Subgroup.zpowers w) hperf hV₀ hKV₀
    (fun l hl v hv => by
      rcases hz v hv with rfl | rfl
      · simp
      · exact hKw l hl)
  exact h.trans (Subgroup.centralizer_le (by simp))

theorem s16h_le_celt_of_mem_preTil_fixV {D : Data G} {V₀ V K : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil V₀ V) (hKM : K ≤ D.M) {w : G}
    (hw : w ∈ preTil V₀ V hV (fixV (barSub V₀ V hV K))) : K ≤ F11.CElt D.M V₀ w := by
  intro k hk
  obtain ⟨x, rfl, hx⟩ := (mem_preTil V₀ V hV _).1 hw
  have hks : k ∈ stabTil V₀ V := hMs (hKM hk)
  have hfix := mem_fixV.1 hx _ (actTil_mem_barSub V₀ V hV hk hks)
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix
  exact ⟨hKM hk, stabTil_le_normalizer₀ V₀ V hks, hfix⟩

theorem s16h_uniqueMax_of_calC (D : Data G) (h869 : F08.R869 D) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hnt : ¬ F08.Thin8 K) : UniqueMax D.M K := by
  have hKM : K ≤ D.M := hK.1.le
  refine uc22p22u_uniqueMax_of_calN D hKM ?_
  exact h869 K (Or.inl hK) K le_rfl (sup_eq_left.2 (Subgroup.map_subtype_le _)) hnt

theorem s16h_uniqueMax_cent_of_calC (D : Data G) (h869 : F08.R869 D) {V₀ V K : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V) (hMs : D.M ≤ stabTil V₀ V) (h4 : Nat.card V₀ ≤ 4)
    (hK : K ∈ calC D.M) (hnt : ¬ F08.Thin8 K) {w : G}
    (hw : w ∈ preTil V₀ V hV (fixV (barSub V₀ V hV K))) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hKM : K ≤ D.M := hK.1.le
  have hcelt := s16h_le_celt_of_mem_preTil_fixV hV hMs hKM hw
  have hKV₀ : K ≤ centralizer (V₀ : Set G) :=
    ElevenNine.le_centralizer_of_perfect_of_card_le_four hK.2.1 (fun k hk => (hcelt hk).2.1) h4
  have hcomm : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨a, hV₀ ha⟩ ⟨b, hV₀ hb⟩)
  obtain ⟨x, hxw, -⟩ := (mem_preTil V₀ V hV _).1 hw
  have hw2 : w ^ 2 = 1 := hV.2 w (hxw ▸ x.val_mem)
  have hKw : K ≤ centralizer ({w} : Set G) :=
    s16h_perfect_le_centralizer_of_comm_mem hK.2.1 hcomm hKV₀ hw2 fun k hk => (hcelt hk).2.2
  exact uc22p22u_uniqueMax_mono D (le_inf hKM hKw) inf_le_left
    (s16h_uniqueMax_of_calC D h869 hK hnt)

theorem s16h_pRank_map_aut {A : Type*} [Group A] [Finite A] (q : ℕ) (H : Subgroup A)
    (e : A ≃* A) : CFSG.Open.pRank q (H.map e.toMonoidHom) = CFSG.Open.pRank q H := by
  have step : ∀ (K : Subgroup A) (f : A ≃* A) (k : ℕ),
      (∃ E : Subgroup A, E ≤ K ∧ IsElemAbelian q E ∧ Nat.card E = q ^ k) →
        ∃ E : Subgroup A, E ≤ K.map f.toMonoidHom ∧ IsElemAbelian q E ∧ Nat.card E = q ^ k := by
    rintro K f k ⟨E, hEK, hE, hc⟩
    exact ⟨E.map f.toMonoidHom, Subgroup.map_mono hEK,
      CFSG.SectionRank.isElemAbelian_map hE f.toMonoidHom,
      by rw [Subgroup.card_map_of_injective (f := f.toMonoidHom) f.injective, hc]⟩
  have hback : (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
    ext x
    simp
  unfold CFSG.Open.pRank
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hk
    obtain ⟨E, hEK, hE, hc⟩ := step _ e.symm k hk
    rw [hback] at hEK
    exact ⟨E, hEK, hE, hc⟩
  · intro hk
    exact step H e k hk

theorem s16h_barSub_conjSubgroup_le {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {K L : Subgroup G}
    (h : barSub V₀ V hV K ≤ barSub V₀ V hV L) {x : G} (hx : x ∈ stabTil V₀ V) :
    barSub V₀ V hV (conjSubgroup K x) ≤ barSub V₀ V hV (conjSubgroup L x) := by
  rw [s15_Infra_barSub_conjSubgroup V₀ V hV hx, s15_Infra_barSub_conjSubgroup V₀ V hV hx]
  exact Subgroup.map_mono h

theorem s16h_mem_preTil_fixV_of_le {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {B B' : Subgroup (MulAut (Vtil V₀ V hV))} (h : B ≤ B') {w : G}
    (hw : w ∈ preTil V₀ V hV (fixV B')) : w ∈ preTil V₀ V hV (fixV B) :=
  Subgroup.map_mono (Subgroup.comap_mono fun y hy => mem_fixV.2 fun g hg =>
    mem_fixV.1 hy g (h hg)) hw

theorem s16h_conjSubgroup_le_celt_of_barSub_le {D : Data G} {V₀ V L K : Subgroup G}
    (h : Hyp125 D V₀ V) (hKM : K ≤ D.M)
    (hbar : barSub V₀ V h.isElemAbelian K ≤ barSub V₀ V h.isElemAbelian L) {x : G}
    (hx : x ∈ D.M) {w : G}
    (hw : w ∈ preTil V₀ V h.isElemAbelian
      (fixV (barSub V₀ V h.isElemAbelian (conjSubgroup L x)))) :
    conjSubgroup K x ≤ F11.CElt D.M V₀ w := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hKx : conjSubgroup K x ≤ D.M := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hx) (hKM hy)) hx
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rwa [e] at h1
  exact s16h_le_celt_of_mem_preTil_fixV h.isElemAbelian hMs hKx
    (s16h_mem_preTil_fixV_of_le h.isElemAbelian
      (s16h_barSub_conjSubgroup_le h.isElemAbelian hbar (hMs hx)) hw)

theorem s16h_condU_of_cover_not_thin (D : Data G) (h869 : F08.R869 D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) {K₀ : Subgroup G} (hK₀ : K₀ ∈ calC D.M)
    (hbar : barSub V₀ V h.hyp151.isElemAbelian K₀ ≤ barSub V₀ V h.hyp151.isElemAbelian L)
    (hnt : ¬ F08.Thin8 K₀) : s16h_CondU D V₀ V L h.hyp151.isElemAbelian := by
  have h125 : Hyp125 D V₀ V := h.hyp151.hyp125
  have hV : IsElemAbelian 2 V := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  intro x hx w hw _
  have hKx : conjSubgroup K₀ x ∈ calC D.M :=
    uc22p22u_calC_conj Subgroup.le_normalizer hK₀ hx
  have hntx : ¬ F08.Thin8 (conjSubgroup K₀ x) := fun hthin =>
    hnt fun q hq hq2 => by
      have h1 := hthin q hq hq2
      rwa [conjSubgroup, s16h_pRank_map_aut q K₀ (MulAut.conj x⁻¹)] at h1
  exact s16h_uniqueMax_cent_of_calC D h869 hV h125.pairFacts.le hMs
    (s16c34_card_v0_le_four D h.hyp16) hKx hntx
    (s16h_mem_preTil_fixV_of_le hV (s16h_barSub_conjSubgroup_le hV hbar (hMs hx)) hw)

theorem s16h_condU_of_not_thin (D : Data G) (h127 : R127 D) (h119 : F11.R119 D)
    (h869 : F08.R869 D) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hcomp : IsComponentOf (barSub V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hrank : 2 ≤ CFSG.Open.pRank q (barSub V₀ V h.hyp151.isElemAbelian L)) :
    s16h_CondU D V₀ V L h.hyp151.isElemAbelian := by
  obtain ⟨K, hK, hKbar⟩ := s16h_exists_cover D h127 h119 h.hyp151.hyp125 hcomp
  exact s16h_condU_of_cover_not_thin D h869 h hK hKbar.le
    (s16h_not_thin_of_barSub_pRank h.hyp151.isElemAbelian hq hq2 (by rw [hKbar]; exact hrank))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
