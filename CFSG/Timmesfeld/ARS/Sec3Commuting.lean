module

public import CFSG.Timmesfeld.ARS.Sec3Natural

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Matrix
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec3

section Commuting32

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {A B C : Subgroup G}
  (hA : A ∈ R) (hB : B ∈ R) (hAB : Opposite A B) (hBC : C ∈ psiSet R B)
  (hAC : Commuting A C)

include hR hiso hB hBC in
theorem commutator_mem_lambdaSet_left : ⁅B, C⁆ ∈ lambdaSet R B :=
  mem_lambdaSet_comm hBC.2.1 (mem_lambdaSet_commutator hR hiso hB hBC.1 hBC.2).1

include hR hiso hA hB hAB hBC hAC in
theorem commutator_mem_psiSet_of_commuting : ⁅B, C⁆ ∈ psiSet R A := by
  have hDR : ⁅B, C⁆ ∈ R := hBC.2.1
  have hDl := commutator_mem_lambdaSet_left hR hiso hB hBC
  have hCl : C ∈ lambdaSet R ⁅B, C⁆ := (mem_lambdaSet_commutator hR hiso hB hBC.1 hBC.2).2
  have hnc : ¬ Commuting A ⁅B, C⁆ := not_commuting_of_opposite_of_mem_lambdaSet hR hA hAB hDl
  have hno : ¬ Opposite A ⁅B, C⁆ := fun h =>
    not_commuting_of_opposite_of_mem_lambdaSet hR hA h hCl hAC
  have hne : A ≠ ⁅B, C⁆ := fun e => hnc (e ▸ hR.commuting_self hA)
  refine ⟨hDR, ?_⟩
  rcases hR.rel A hA _ hDR hne with h | h | h
  · exact absurd h hnc
  · exact absurd h hno
  · exact h

omit [Finite G] in
include hBC hAC in
theorem commuting_sup_of_commuting : Commuting C (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) := by
  have hCD : Commuting C ⁅B, C⁆ := hBC.2.2.2.symm
  refine Commuting.sup_right hCD ?_
  rw [commuting_iff_le_centralizer, Subgroup.commutator_le]
  intro a ha d hd
  have h1 : a ∈ Subgroup.centralizer (C : Set G) := commuting_iff_le_centralizer.1 hAC.symm ha
  have h2 : d ∈ Subgroup.centralizer (C : Set G) := commuting_iff_le_centralizer.1 hCD hd
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2)
    (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)

include hR hiso hA hB hAB hBC hAC

theorem conjSub_sup_eq_of_commuting {x : G} (hx : x ∈ A ⊔ B ⊔ C) :
    conjSub (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) x = ⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆ := by
  have hDl := commutator_mem_lambdaSet_left hR hiso hB hBC
  have hDp := commutator_mem_psiSet_of_commuting hR hiso hA hB hAB hBC hAC
  have hX : A ⊔ B ≤ Subgroup.normalizer ((⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆ : Subgroup G) : Set G) :=
    fun y hy => conjSub_eq_self_iff.1
      (conjSub_sup_commutator_eq hR hiso hB hA hAB.symm hDl hDp (sup_comm A B ▸ hy))
  have hC : C ≤ Subgroup.normalizer ((⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆ : Subgroup G) : Set G) :=
    fun c hc => conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun n hn =>
      commuting_sup_of_commuting hBC hAC c hc n hn)
  exact conjSub_eq_self_iff.2 (sup_le hX hC hx)

theorem commuting_sup_sup_of_commuting :
    Commuting (C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆)) (C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆)) := by
  have hDl := commutator_mem_lambdaSet_left hR hiso hB hBC
  have hDp := commutator_mem_psiSet_of_commuting hR hiso hA hB hAB hBC hAC
  have hN := commuting_sup_commutator hR hDl hDp
  have hCN := commuting_sup_of_commuting hBC hAC
  exact Commuting.sup_left (Commuting.sup_right (hR.commuting_self hBC.1) hCN)
    (Commuting.sup_right hCN.symm hN)

theorem conjSub_sup_sup_eq_of_commuting {x : G} (hx : x ∈ A ⊔ B ⊔ C) :
    conjSub (C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆)) x = C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) := by
  set N := ⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆ with hNdef
  have hN : ∀ y ∈ A ⊔ B ⊔ C, conjSub N y = N := fun y hy =>
    conjSub_sup_eq_of_commuting hR hiso hA hB hAB hBC hAC hy
  have hAn : A ≤ Subgroup.normalizer ((C ⊔ N : Subgroup G) : Set G) :=
    le_normalizer_of_conjSub_le fun a ha => by
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
        conjSub_of_forall_commute fun c hc => hAC a ha c hc,
        hN a (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))]
  have hBn : B ≤ Subgroup.normalizer ((C ⊔ N : Subgroup G) : Set G) :=
    le_normalizer_of_conjSub_le fun b hb => by
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
        hN b (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))]
      refine sup_le ((conjSub_le_commutator_sup hb).trans (sup_le ?_ le_sup_left)) le_sup_right
      rw [Subgroup.commutator_comm]
      exact le_sup_left.trans le_sup_right
  have hCn : C ≤ Subgroup.normalizer ((C ⊔ N : Subgroup G) : Set G) := fun c hc =>
    conjSub_eq_self_iff.1 (conjSub_of_mem (Subgroup.mem_sup_left hc))
  exact conjSub_eq_self_iff.2 (sup_le (sup_le hAn hBn) hCn hx)

theorem sup_sup_inf_eq_bot_of_commuting :
    (C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆)) ⊓ (A ⊔ B) = ⊥ := by
  have hDl := commutator_mem_lambdaSet_left hR hiso hB hBC
  have hDp := commutator_mem_psiSet_of_commuting hR hiso hA hB hAB hBC hAC
  have hM := commuting_sup_sup_of_commuting hR hiso hA hB hAB hBC hAC
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  exact eq_one_of_forall_commute_of_mem_sup_left hR hiso hB hA hAB.symm hDl hDp
    (sup_comm A B ▸ hx.2) fun n hn => hM x hx.1 n (Subgroup.mem_sup_right hn)

theorem mul_inv_mem_centralizer_of_commuting {a b c : G} (ha : a ∈ A) (hb : b ∈ B)
    (hb1 : b ≠ 1) (hab : conjSub B a = conjSub A b) (hc : c ∈ C) :
    c * ⁅a, ⁅b, c⁆⁆⁻¹ ∈ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G) := by
  have hDl := commutator_mem_lambdaSet_left hR hiso hB hBC
  have hDp := commutator_mem_psiSet_of_commuting hR hiso hA hB hAB hBC hAC
  have hM := commuting_sup_sup_of_commuting hR hiso hA hB hAB hBC hAC
  have hd : ⁅b, c⁆ ∈ ⁅B, C⁆ := Subgroup.commutator_mem_commutator hb hc
  have he : ⁅a, ⁅b, c⁆⁆ ∈ ⁅A, ⁅B, C⁆⁆ := Subgroup.commutator_mem_commutator ha hd
  have hbe : ⁅b, ⁅a, ⁅b, c⁆⁆⁆ = ⁅b, c⁆ :=
    commutatorElement_commutatorElement_eq hR hiso hB hA hAB.symm hDl hDp hb hb1 ha hab hd
  set d := ⁅b, c⁆ with hddef
  set e := ⁅a, d⁆ with hedef
  have hcM : c ∈ C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) := Subgroup.mem_sup_left hc
  have hdM : d ∈ C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_left hd)
  have heM : e ∈ C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_right he)
  have hzA : ∀ a' ∈ A, Commute a' (c * e⁻¹) := fun a' ha' =>
    (hAC a' ha' c hc).mul_right (hDp.2.2.1 e he a' ha').symm.inv_right
  have hzb : Commute b (c * e⁻¹) := by
    have h1 : b * c * b⁻¹ = d * c := conj_eq_commutator_mul b c
    have h2 : b * e * b⁻¹ = d * e := by rw [conj_eq_commutator_mul, hbe]
    have hdc : Commute d c := hM d hdM c hcM
    have hde : Commute d e := hM d hdM e heM
    rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
    calc b * (c * e⁻¹) * b⁻¹ = (b * c * b⁻¹) * (b * e * b⁻¹)⁻¹ := by group
      _ = d * c * (d * e)⁻¹ := by rw [h1, h2]
      _ = c * e⁻¹ := by rw [hdc.eq, hde.eq, mul_inv_rev]; group
  have hA' : A ≤ Subgroup.centralizer ({c * e⁻¹} : Set G) := fun a' ha' =>
    Subgroup.mem_centralizer_singleton_iff.2 (hzA a' ha').eq
  have hb' : b ∈ Subgroup.centralizer ({c * e⁻¹} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hzb.eq
  have hne : conjSub A 1 ≠ conjSub A b := by
    rw [conjSub_one, ← hab]
    intro e'
    apply hAB.1
    have : conjSub (conjSub B a) a⁻¹ = B := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    rw [← this, ← e', conjSub_of_mem (A.inv_mem ha)]
  have hX : A ⊔ B ≤ Subgroup.centralizer ({c * e⁻¹} : Set G) := by
    rw [← hAB.sup_conjSub_eq (hR.mul_self A hA) (one_mem _) (Subgroup.mem_sup_right hb) hne,
      conjSub_one]
    exact sup_le hA' (conjSub_le hA' hb')
  have hC' : C ≤ Subgroup.centralizer ({c * e⁻¹} : Set G) := fun c' hc' =>
    Subgroup.mem_centralizer_singleton_iff.2
      (hM c' (Subgroup.mem_sup_left hc') _ (Subgroup.mul_mem _ hcM (Subgroup.inv_mem _ heM))).eq
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.1 (sup_le hX hC' hx)

theorem sup_sup_eq_iSup_of_commuting :
    C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) = ⨆ x ∈ A ⊔ B, conjSub C x := by
  have hDl := commutator_mem_lambdaSet_left hR hiso hB hBC
  have hDp := commutator_mem_psiSet_of_commuting hR hiso hA hB hAB hBC hAC
  set S := ⨆ x ∈ A ⊔ B, conjSub C x with hS
  have hCS : C ≤ S := by
    have := le_iSup₂ (f := fun x (_ : x ∈ A ⊔ B) => conjSub C x) 1 (one_mem _)
    rwa [conjSub_one] at this
  have hSx : ∀ x ∈ A ⊔ B, conjSub S x ≤ S := by
    intro x hx
    rw [conjSub, Subgroup.map_le_iff_le_comap, hS]
    refine iSup₂_le fun y hy => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← conjSub, ← conjSub_mul]
    exact le_iSup₂ (f := fun x (_ : x ∈ A ⊔ B) => conjSub C x) (x * y) (Subgroup.mul_mem _ hx hy)
  have hDS : ⁅B, C⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro b hb c hc
    rw [commutatorElement_def]
    have h1 : b * c * b⁻¹ ∈ S :=
      le_iSup₂ (f := fun x (_ : x ∈ A ⊔ B) => conjSub C x) b (Subgroup.mem_sup_right hb)
        (conj_mem_conjSub b hc)
    exact Subgroup.mul_mem _ h1 (hCS (C.inv_mem hc))
  apply le_antisymm
  · refine sup_le hCS ?_
    rw [sup_commutator_eq_iSup hR hiso hB hA hAB.symm hDl hDp]
    refine iSup₂_le fun x hx => (Subgroup.map_mono hDS).trans (hSx x (sup_comm B A ▸ hx))
  · refine iSup₂_le fun x hx => ?_
    rw [← conjSub_sup_sup_eq_of_commuting hR hiso hA hB hAB hBC hAC
      (Subgroup.mem_sup_left hx)]
    exact Subgroup.map_mono le_sup_left

theorem sup_sup_sup_eq_of_commuting :
    C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) ⊔ (A ⊔ B) = A ⊔ B ⊔ C := by
  apply le_antisymm
  · rw [sup_sup_eq_iSup_of_commuting hR hiso hA hB hAB hBC hAC]
    exact sup_le (iSup₂_le fun x hx => conjSub_le le_sup_right (le_sup_left (a := A ⊔ B) hx))
      le_sup_left
  · exact sup_le le_sup_right (le_sup_left.trans le_sup_left)

variable {Z : Subgroup G} (hZ : Z = (C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆)) ⊓
  Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G))
include hZ

theorem sup_inf_centralizer_eq_bot_of_commuting : (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) ⊓ Z = ⊥ := by
  subst hZ
  have hDl := commutator_mem_lambdaSet_left hR hiso hB hBC
  have hDp := commutator_mem_psiSet_of_commuting hR hiso hA hB hAB hBC hAC
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  refine eq_one_of_forall_commute_of_mem_sup hR hiso hB hA hAB.symm hDl hDp hx.1 fun g hg => ?_
  have hg' : g ∈ A ⊔ B ⊔ C := Subgroup.mem_sup_left (sup_comm B A ▸ hg)
  exact Subgroup.mem_centralizer_iff.1 hx.2.2 g hg'

theorem exists_eq_mul_inv_of_mem_centralizer {a b : G} (ha : a ∈ A) (hb : b ∈ B)
    (hb1 : b ≠ 1) (hab : conjSub B a = conjSub A b) {z : G} (hz : z ∈ Z) :
    ∃ c ∈ C, z = c * ⁅a, ⁅b, c⁆⁆⁻¹ := by
  have hbot := sup_inf_centralizer_eq_bot_of_commuting hR hiso hA hB hAB hBC hAC hZ
  have hM := commuting_sup_sup_of_commuting hR hiso hA hB hAB hBC hAC
  subst hZ
  have hle : (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) ≤ Subgroup.normalizer (C : Set G) :=
    (commuting_iff_le_centralizer.1 (commuting_sup_of_commuting hBC hAC)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hzM : z ∈ ((C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) : Subgroup G) : Set G) := hz.1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left C _ hle] at hzM
  obtain ⟨c, hc, n, hn, rfl⟩ := hzM
  refine ⟨c, hc, ?_⟩
  set e := ⁅a, ⁅b, c⁆⁆ with hedef
  have he : e ∈ ⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆ := Subgroup.mem_sup_right
    (Subgroup.commutator_mem_commutator ha (Subgroup.commutator_mem_commutator hb hc))
  have hz' := mul_inv_mem_centralizer_of_commuting hR hiso hA hB hAB hBC hAC ha hb hb1 hab hc
  have hz'M : c * e⁻¹ ∈ C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right (Subgroup.inv_mem _ he))
  have hmem : (c * e⁻¹)⁻¹ * (c * n) ∈
      (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) ⊓ ((C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆)) ⊓
        Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G)) := by
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ ⟨hz'M, hz'⟩) hz⟩
    have : (c * e⁻¹)⁻¹ * (c * n) = e * n := by group
    rw [this]
    exact Subgroup.mul_mem _ he hn
  rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem.symm

theorem sup_centralizer_eq_of_commuting :
    (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) ⊔ Z = C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) := by
  have hZM : Z ≤ C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) := hZ ▸ inf_le_left
  refine le_antisymm (sup_le le_sup_right hZM) (sup_le ?_ le_sup_left)
  intro c hc
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
  obtain ⟨a, ha, -, hab⟩ := hAB.2.2 b hb hb1
  have hz := mul_inv_mem_centralizer_of_commuting hR hiso hA hB hAB hBC hAC ha hb hb1 hab hc
  have he : ⁅a, ⁅b, c⁆⁆ ∈ ⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆ := Subgroup.mem_sup_right
    (Subgroup.commutator_mem_commutator ha (Subgroup.commutator_mem_commutator hb hc))
  have hzM : c * ⁅a, ⁅b, c⁆⁆⁻¹ ∈ C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right (Subgroup.inv_mem _ he))
  have hzZ : c * ⁅a, ⁅b, c⁆⁆⁻¹ ∈ Z := hZ ▸ ⟨hzM, hz⟩
  have : c = (c * ⁅a, ⁅b, c⁆⁆⁻¹) * ⁅a, ⁅b, c⁆⁆ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hzZ) (Subgroup.mem_sup_left he)

theorem centralizer_eq_bot_iff_of_commuting : Z = ⊥ ↔ C ∈ lambdaSet R A := by
  have hDl := commutator_mem_lambdaSet_left hR hiso hB hBC
  have hDp := commutator_mem_psiSet_of_commuting hR hiso hA hB hAB hBC hAC
  have hCR : C ∈ R := hBC.1
  constructor
  · intro hZbot
    obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
    obtain ⟨a, ha, -, hab⟩ := hAB.2.2 b hb hb1
    have hCE : C ≤ ⁅A, ⁅B, C⁆⁆ := by
      intro c hc
      have hz := mul_inv_mem_centralizer_of_commuting hR hiso hA hB hAB hBC hAC ha hb hb1 hab hc
      have he : ⁅a, ⁅b, c⁆⁆ ∈ ⁅A, ⁅B, C⁆⁆ :=
        Subgroup.commutator_mem_commutator ha (Subgroup.commutator_mem_commutator hb hc)
      have hzM : c * ⁅a, ⁅b, c⁆⁆⁻¹ ∈ C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hc)
          (Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.inv_mem _ he)))
      have hzZ : c * ⁅a, ⁅b, c⁆⁆⁻¹ ∈ Z := hZ ▸ ⟨hzM, hz⟩
      rw [hZbot, Subgroup.mem_bot, mul_inv_eq_one] at hzZ
      rw [hzZ]
      exact he
    have hER : ⁅A, ⁅B, C⁆⁆ ∈ R := hDp.2.1
    have hEq : C = ⁅A, ⁅B, C⁆⁆ := by
      by_contra hne
      have := inf_eq_bot hR hiso hCR hER hne
      rw [inf_of_le_left hCE] at this
      exact hR.ne_bot C hCR this
    rw [hEq]
    exact mem_lambdaSet_comm hER (mem_lambdaSet_commutator hR hiso hA hDp.1 hDp.2).1
  · intro hCl
    have hEC : ⁅A, ⁅B, C⁆⁆ ≤ C := by
      rw [Subgroup.commutator_le]
      intro a ha d hd
      exact commutatorElement_mem_of_mem_commutator hR hiso hA hB hAB hCl hBC ha hd
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    rw [hZ] at hx
    have hxN : x ∈ C ⊔ ⁅B, C⁆ := by
      have hle : C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) ≤ C ⊔ ⁅B, C⁆ :=
        sup_le le_sup_left (sup_le le_sup_right (hEC.trans le_sup_left))
      exact hle hx.1
    exact eq_one_of_forall_commute_of_mem_sup hR hiso hA hB hAB hCl hBC hxN fun g hg =>
      Subgroup.mem_centralizer_iff.1 hx.2 g (Subgroup.mem_sup_left hg)

theorem exists_mem_of_not_mem_centralizer {m : G} (hm : m ∈ C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆))
    (hmZ : m ∉ Z) : ∃ F ∈ R, F ≤ C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) ∧ m ∈ F := by
  have hDl := commutator_mem_lambdaSet_left hR hiso hB hBC
  have hDp := commutator_mem_psiSet_of_commuting hR hiso hA hB hAB hBC hAC
  have hM := commuting_sup_sup_of_commuting hR hiso hA hB hAB hBC hAC
  have hsup := sup_centralizer_eq_of_commuting hR hiso hA hB hAB hBC hAC hZ
  have hbot := sup_inf_centralizer_eq_bot_of_commuting hR hiso hA hB hAB hBC hAC hZ
  have hCR : C ∈ R := hBC.1
  set N := ⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆ with hNdef
  have hNM : N ≤ C ⊔ N := le_sup_right
  have hZM : Z ≤ C ⊔ N := hZ ▸ inf_le_left
  have hle : Z ≤ Subgroup.normalizer (N : Set G) :=
    (commuting_iff_le_centralizer.1 (hM.mono hNM hZM)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hm' : m ∈ ((N ⊔ Z : Subgroup G) : Set G) := hsup ▸ hm
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N Z hle] at hm'
  obtain ⟨n, hn, z, hz, rfl⟩ := hm'
  dsimp only at hm hmZ ⊢
  have hn1 : n ≠ 1 := by
    rintro rfl
    rw [one_mul] at hmZ
    exact hmZ hz
  by_cases hz1 : z = 1
  · obtain ⟨F, hF, hFN, hnF⟩ := coveredBy_sup_commutator hR hiso hB hA hAB.symm hDl hDp n hn hn1
    exact ⟨F, hF, hFN.trans hNM, by rw [hz1, mul_one]; exact hnF⟩
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
  obtain ⟨a, ha, -, hab⟩ := hAB.2.2 b hb hb1
  obtain ⟨c, hc, rfl⟩ :=
    exists_eq_mul_inv_of_mem_centralizer hR hiso hA hB hAB hBC hAC hZ ha hb hb1 hab hz
  set e := ⁅a, ⁅b, c⁆⁆ with hedef
  have he : e ∈ N := Subgroup.mem_sup_right
    (Subgroup.commutator_mem_commutator ha (Subgroup.commutator_mem_commutator hb hc))
  have hzc : c * e⁻¹ ∈ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G) := by
    have hz' : c * e⁻¹ ∈ (C ⊔ N) ⊓ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G) :=
      hZ ▸ hz
    exact hz'.2
  have he1 : e ≠ 1 := by
    intro h1
    rw [h1, inv_one, mul_one] at hzc hz1
    have hbc : Commute b c :=
      Subgroup.mem_centralizer_iff.1 hzc b (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))
    exact hz1 (eq_one_of_commute_of_special hR hiso hB hCR hBC.2 hb hb1 hc hbc)
  obtain ⟨x, hx, hxe⟩ := exists_conj_eq_of_mem_sup hR hiso hB hA hAB.symm hDl hDp he he1 hn hn1
  have hxR : x ∈ A ⊔ B ⊔ C := Subgroup.mem_sup_left (sup_comm B A ▸ hx)
  have hxz : Commute x (c * e⁻¹) := Subgroup.mem_centralizer_iff.1 hzc x hxR
  refine ⟨conjSub C x, hR.conjSub_mem hCR x, ?_, ?_⟩
  · rw [← conjSub_sup_sup_eq_of_commuting hR hiso hA hB hAB hBC hAC hxR]
    exact Subgroup.map_mono le_sup_left
  · have hcz : c = (c * e⁻¹) * e := by group
    have key : x * c * x⁻¹ = n * (c * e⁻¹) := by
      calc x * c * x⁻¹ = x * (c * e⁻¹) * x⁻¹ * (x * e * x⁻¹) := by
            nth_rewrite 1 [hcz]
            group
        _ = (c * e⁻¹) * n := by rw [hxe, hxz.eq, mul_inv_cancel_right]
        _ = n * (c * e⁻¹) := (hM _ (hZM hz) n (hNM hn)).eq
    rw [← key]
    exact conj_mem_conjSub x hc

theorem inf_eq_bot_or_eq_of_le {F : Subgroup G} (hF : F ∈ R)
    (hFM : F ≤ C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆)) : F ⊓ Z = ⊥ ∨ F = Z := by
  have hDl := commutator_mem_lambdaSet_left hR hiso hB hBC
  have hDp := commutator_mem_psiSet_of_commuting hR hiso hA hB hAB hBC hAC
  have hM := commuting_sup_sup_of_commuting hR hiso hA hB hAB hBC hAC
  have hsup := sup_centralizer_eq_of_commuting hR hiso hA hB hAB hBC hAC hZ
  have hCR : C ∈ R := hBC.1
  set N := ⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆ with hNdef
  by_cases h : F ⊓ Z = ⊥
  · exact Or.inl h
  right
  obtain ⟨⟨f, hfF, hfZ⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  have hf1' : f ≠ 1 := fun h1 => hf1 (Subtype.ext h1)
  have hcent : ∀ {y : G}, y ∈ Z → y ∈ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G) :=
    fun {y} hy => by
      have hy' : y ∈ (C ⊔ N) ⊓ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G) := hZ ▸ hy
      exact hy'.2
  have hZM : Z ≤ C ⊔ N := hZ ▸ inf_le_left
  have hFx : ∀ x ∈ A ⊔ B ⊔ C, conjSub F x = F := by
    intro x hx
    by_contra hne
    have hfx : x * f * x⁻¹ = f := by
      rw [Subgroup.mem_centralizer_iff.1 (hcent hfZ) x hx, mul_inv_cancel_right]
    have hmem : f ∈ conjSub F x ⊓ F := ⟨hfx ▸ conj_mem_conjSub x hfF, hfF⟩
    rw [inf_eq_bot hR hiso (hR.conjSub_mem hF x) hF hne, Subgroup.mem_bot] at hmem
    exact hf1' hmem
  have hFN : F ⊓ N = ⊥ := by
    by_contra hne
    obtain ⟨⟨y, hyF, hyN⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hy1' : y ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
    have hNF : N ≤ F := by
      intro n hn
      by_cases hn1 : n = 1
      · rw [hn1]
        exact F.one_mem
      obtain ⟨x, hx, rfl⟩ :=
        exists_conj_eq_of_mem_sup hR hiso hB hA hAB.symm hDl hDp hyN hy1' hn hn1
      rw [← hFx x (Subgroup.mem_sup_left (sup_comm B A ▸ hx))]
      exact conj_mem_conjSub x hyF
    have hcard := Subgroup.card_le_of_le hNF
    rw [card_sup_commutator hR hiso hDl hDp, hR.card_eq hF hBC.2.1] at hcard
    have h1 : 1 < Nat.card ↥(⁅B, C⁆ : Subgroup G) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 (hR.ne_bot _ hBC.2.1)
    nlinarith
  have hFZ : F ≤ Z := by
    intro g hg
    have hgM := hFM hg
    rw [hZ]
    refine ⟨hgM, ?_⟩
    have hle : Z ≤ Subgroup.normalizer (N : Set G) :=
      (commuting_iff_le_centralizer.1 (hM.mono le_sup_right hZM)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hg' : g ∈ ((N ⊔ Z : Subgroup G) : Set G) := hsup ▸ hgM
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N Z hle] at hg'
    obtain ⟨n, hn, z, hz, hnz⟩ := hg'
    show g ∈ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxz : x * z * x⁻¹ = z := by
      rw [Subgroup.mem_centralizer_iff.1 (hcent hz) x hx, mul_inv_cancel_right]
    have hcomm : ⁅x, g⁆ ∈ F ⊓ N := by
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        refine F.mul_mem ?_ (F.inv_mem hg)
        rw [← hFx x hx]
        exact conj_mem_conjSub x hg
      · rw [← hnz]
        dsimp only
        have e : ⁅x, n * z⁆ = x * n * x⁻¹ * n⁻¹ := by
          rw [commutatorElement_def]
          calc x * (n * z) * x⁻¹ * (n * z)⁻¹ = x * n * x⁻¹ * (x * z * x⁻¹) * z⁻¹ * n⁻¹ := by
                group
            _ = x * n * x⁻¹ * n⁻¹ := by rw [hxz]; group
        rw [e]
        refine N.mul_mem ?_ (N.inv_mem hn)
        have hNx := conjSub_sup_eq_of_commuting hR hiso hA hB hAB hBC hAC hx
        rw [← hNdef] at hNx
        rw [← hNx]
        exact conj_mem_conjSub x hn
    rw [hFN, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcomm
    exact hcomm
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
  obtain ⟨a, ha, -, hab⟩ := hAB.2.2 b hb hb1
  have hsurj : Function.Surjective fun c : C => (⟨(c : G) * ⁅a, ⁅b, (c : G)⁆⁆⁻¹, by
      rw [hZ]
      refine ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left c.2) (Subgroup.mem_sup_right
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator ha
          (Subgroup.commutator_mem_commutator hb c.2))))), ?_⟩
      exact mul_inv_mem_centralizer_of_commuting hR hiso hA hB hAB hBC hAC ha hb hb1 hab c.2⟩ :
        Z) := by
    rintro ⟨z, hz⟩
    obtain ⟨c, hc, rfl⟩ :=
      exists_eq_mul_inv_of_mem_centralizer hR hiso hA hB hAB hBC hAC hZ ha hb hb1 hab hz
    exact ⟨⟨c, hc⟩, rfl⟩
  have hcard := Nat.card_le_card_of_surjective _ hsurj
  rw [hR.card_eq hCR hF] at hcard
  exact Subgroup.eq_of_le_of_card_ge hFZ hcard

end Commuting32

end Sec3

open Sec3

theorem natural_module_of_commuting [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B C : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hAB : Opposite A B)
    (hBC : C ∈ psiSet R B) (hAC : Commuting A C) {N M Z : Subgroup G}
    (hN : N = ⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆) (hM : M = C ⊔ N)
    (hZ : Z = M ⊓ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G)) :
    (⁅B, C⁆ ∈ lambdaSet R B ∧ ⁅B, C⁆ ∈ psiSet R A ∧
      N = (⨆ x ∈ A ⊔ B, conjSub ⁅B, C⁆ x) ∧ (∀ x ∈ A ⊔ B ⊔ C, conjSub N x = N) ∧
      CoveredBy R N) ∧
    (M = (⨆ x ∈ A ⊔ B, conjSub C x) ∧ Commuting M M ∧ (∀ x ∈ A ⊔ B ⊔ C, conjSub M x = M) ∧
      M ⊔ (A ⊔ B) = A ⊔ B ⊔ C ∧ M ⊓ (A ⊔ B) = ⊥ ∧ N ⊔ Z = M ∧ N ⊓ Z = ⊥) ∧
    ((∀ m ∈ M, m ∉ Z → ∃ F ∈ R, F ≤ M ∧ m ∈ F) ∧ (∀ F ∈ R, F ≤ M → F ⊓ Z = ⊥ ∨ F = Z) ∧
      (Z = ⊥ ↔ C ∈ lambdaSet R A)) := by
  subst hN hM
  have hDl := commutator_mem_lambdaSet_left hR hiso hB hBC
  have hDp := commutator_mem_psiSet_of_commuting hR hiso hA hB hAB hBC hAC
  refine ⟨⟨hDl, hDp, ?_, fun x hx => conjSub_sup_eq_of_commuting hR hiso hA hB hAB hBC hAC hx,
    coveredBy_sup_commutator hR hiso hB hA hAB.symm hDl hDp⟩,
    ⟨sup_sup_eq_iSup_of_commuting hR hiso hA hB hAB hBC hAC,
      commuting_sup_sup_of_commuting hR hiso hA hB hAB hBC hAC,
      fun x hx => conjSub_sup_sup_eq_of_commuting hR hiso hA hB hAB hBC hAC hx,
      sup_sup_sup_eq_of_commuting hR hiso hA hB hAB hBC hAC,
      sup_sup_inf_eq_bot_of_commuting hR hiso hA hB hAB hBC hAC,
      sup_centralizer_eq_of_commuting hR hiso hA hB hAB hBC hAC hZ,
      sup_inf_centralizer_eq_bot_of_commuting hR hiso hA hB hAB hBC hAC hZ⟩,
    ⟨fun m hm hmZ => exists_mem_of_not_mem_centralizer hR hiso hA hB hAB hBC hAC hZ hm hmZ,
      fun F hF hFM => inf_eq_bot_or_eq_of_le hR hiso hA hB hAB hBC hAC hZ hF hFM,
      centralizer_eq_bot_iff_of_commuting hR hiso hA hB hAB hBC hAC hZ⟩⟩
  rw [sup_commutator_eq_iSup hR hiso hB hA hAB.symm hDl hDp, sup_comm B A]

end CFSG.Timmesfeld.ARS
