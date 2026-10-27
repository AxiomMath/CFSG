module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2214_normalizer_le_of_sp {M : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) {A : Subgroup G} (hAM : A ≤ M) (hA : IsPGroup q A)
    (hA1 : A ≠ ⊥) : normalizer (A : Set G) ≤ M := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro g hg
  by_contra hgM
  apply hsp.2.2 g hgM
  have hle : A ≤ M ⊓ M.map (MulAut.conj g).toMonoidHom := by
    refine le_inf hAM fun x hx => ?_
    have hy : g⁻¹ * x * g ∈ A := by
      rw [mem_normalizer_iff.1 hg]
      simpa [mul_assoc] using hx
    exact ⟨g⁻¹ * x * g, hAM hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hA1 (Subgroup.eq_bot_of_card_eq A (by simpa using hk))
  exact (hk ▸ dvd_pow_self q hk0).trans (Subgroup.card_dvd_of_le hle)

theorem uc22p2214_false_of_sp (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D) (c : Ctx22b D Ch) {q : ℕ}
    (hq : q.Prime) (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M) {a : G} (ha : a ∈ c.B0)
    (hao : orderOf a = q) : False := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hA : IsPGroup q (zpowers a) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
  have hA1 : zpowers a ≠ ⊥ := by
    intro h
    have h1 : a = 1 := zpowers_eq_bot.1 h
    rw [h1, orderOf_one] at hao
    exact hq.ne_one hao.symm
  have hAB : zpowers a ≤ c.B0 := zpowers_le.2 ha
  exact s21_2 D Ch h1930 { c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } (zpowers a) hAB
    (uc22p2214_normalizer_le_of_sp hq hsp (hAB.trans c.hBM) hA hA1)

theorem uc22p2214_map_center {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at ha
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, ha x]
  · intro hb
    refine ⟨e.symm b, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hb
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro x
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hb (e x)]

theorem uc22p2214_quotCenter_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nonempty ((A ⧸ center A) ≃* (B ⧸ center B)) :=
  ⟨QuotientGroup.congr (center A) (center B) e (uc22p2214_map_center e)⟩

theorem uc22p2214_shape_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {n : ℕ}
    (h : Shape2214 A n) : Shape2214 B n := by
  rcases h with h | h | h | h
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)
  · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e h)))

theorem uc22p2214_mbarImage_mono {M V X Y : Subgroup G} (h : X ≤ Y) : mbarImage M V X ≤ mbarImage M V Y := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

theorem uc22p2214_mem_mbarImage {M V X : Subgroup G} {x : G} (hxM : x ∈ M) (hx : x ∈ X) :
    (QuotientGroup.mk ⟨x, hxM⟩ : MBar M V) ∈ mbarImage M V X :=
  ⟨⟨x, hxM⟩, hx, rfl⟩

theorem uc22p2214_mk_mem_normalizer {M V X : Subgroup G} {x : G} (hxM : x ∈ M) (hxX : x ∈ normalizer (X : Set G)) :
    (QuotientGroup.mk ⟨x, hxM⟩ : MBar M V) ∈ normalizer (mbarImage M V X : Set (MBar M V)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 := uc22br4_mbarImage_map_conj M V X ⟨x, hxM⟩
  have hX : X.map (MulAut.conj ((⟨x, hxM⟩ : ↥M) : G)).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hxX
  rw [hX] at h1
  exact h1.symm

theorem uc22p2214_isSolvable_mbarImage {M V X : Subgroup G} (hX : Group.IsSolvable ↥X) (hXM : X ≤ M) :
    Group.IsSolvable ↥(mbarImage M V X) := by
  haveI : Group.IsSolvable ↥(X.subgroupOf M) := by
    haveI := hX
    exact Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hXM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXM).injective
  exact Group.isSolvable_of_surjective ((QuotientGroup.mk' _).subgroupMap_surjective (X.subgroupOf M))

theorem uc22p2214_odd_card_B0 (D : Data G) {Ch : Choice2011 G} (c : Ctx22b D Ch) : Odd (Nat.card c.B0) := by
  by_contra h
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) 2 h
  have h1 := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 x.2
  rw [Subgroup.orderOf_coe, hx] at h1
  exact (by decide : ¬ Odd 2) h1

theorem uc22p2214_conjClosure_eq_of_normal {M K : Subgroup G} (hKM : K ≤ M) (hn : (K.subgroupOf M).Normal) :
    conjClosure M K = K := by
  have hMK : M ≤ normalizer (K : Set G) := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hn
  apply le_antisymm
  · refine iSup₂_le fun K' hK' => ?_
    obtain ⟨g, hg, rfl⟩ := hK'
    have hgK : K.map (MulAut.conj g).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hMK hg)
    rw [hgK]
  · exact le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M K) => A) K ⟨1, M.one_mem, by ext x; simp⟩ le_rfl

theorem uc22p2214_quotCenter_of_simple {X : Type} [Group X] [IsSimpleGroup X] (hq : CFSG.Open.IsQuasisimple X) :
    Nonempty (X ≃* (X ⧸ center X)) := by
  obtain ⟨e⟩ := uc22p21k_quotCenter_equiv (uc22p21k_center_eq_bot hq)
  exact ⟨e.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
