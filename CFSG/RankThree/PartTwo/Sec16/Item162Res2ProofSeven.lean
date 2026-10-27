module

public import CFSG.RankThree.PartTwo.Sec16.Item162ResProofA7
public import CFSG.RankThree.PartTwo.Sec17.RouteWire16
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofConf
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.PartTwo.Sec16.Item163Proof
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_with_same_image_of_trivial_quotient_action)

namespace Res162b

theorem eq_bot_of_normal_of_isSolvable_a7 {X : Type*} [Group X]
    (φ : X ≃* alternatingGroup (Fin 7)) (N : Subgroup X) [N.Normal]
    (hN : Group.IsSolvable N) : N = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup X := φ.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have hX : Group.IsSolvable X := by
      subst h
      exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := X)).toMonoidHom)
        (Subgroup.topEquiv (G := X)).surjective
    have hA : Group.IsSolvable (alternatingGroup (Fin 7)) :=
      Group.isSolvable_of_surjective (f := φ.toMonoidHom) φ.surjective
    have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin 7))).mpr hA
    have h1 : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    have h2 : Equiv.swap (1 : Fin 7) 2 * Equiv.swap 2 3 ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    have h3 := congrArg Subtype.val (hcomm ⟨_, h1⟩ ⟨_, h2⟩)
    have key : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) * (Equiv.swap 1 2 * Equiv.swap 2 3) ≠
        (Equiv.swap 1 2 * Equiv.swap 2 3) * (Equiv.swap 0 1 * Equiv.swap 1 2) := by
      decide
    exact key h3

theorem surjective_of_ker_le {D Q₁ Q₂ : Type*} [Group D] [Finite D] [Group Q₁] [Group Q₂]
    [Finite Q₂] (f₁ : D →* Q₁) (hf₁ : Function.Surjective f₁) (f₂ : D →* Q₂)
    (hker : f₂.ker ≤ f₁.ker) (hcard : Nat.card Q₂ ≤ Nat.card Q₁) : Function.Surjective f₂ := by
  have h1 := Subgroup.card_ker_mul_card_range f₁
  have h2 := Subgroup.card_ker_mul_card_range f₂
  rw [MonoidHom.range_eq_top.mpr hf₁, Subgroup.card_top] at h1
  have h3 : Nat.card f₂.ker ≤ Nat.card f₁.ker := Subgroup.card_le_of_le hker
  have h4 : 0 < Nat.card f₁.ker := Nat.card_pos
  have h5 : Nat.card Q₁ ≤ Nat.card f₂.range := by
    by_contra hlt
    have := Nat.mul_lt_mul_of_lt_of_le (not_le.mp hlt) h3 h4
    rw [mul_comm (Nat.card f₂.range), mul_comm (Nat.card Q₁), h2, h1] at this
    exact lt_irrefl _ this
  have h6 : f₂.range = ⊤ := Subgroup.eq_top_of_card_eq _
    (le_antisymm (Subgroup.card_le_card_group _) (hcard.trans h5))
  exact MonoidHom.range_eq_top.mp h6

variable {G : Type} [Group G] [Finite G]

theorem eq_top_of_seven {A : Subgroup G} {c : G} {L Y₂ : Subgroup G}
    (h : Sec15R G A c L) (hY₂ : Y₂ ∈ scriptY0Star A (lB A)) (hm : MeetsY4 A (lB A) L Y₂)
    (φ₂ : ↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7)) :
    ∀ y ∈ Y₂, ∃ d ∈ L ⊓ Y₂, d⁻¹ * y ∈ CFSG.Open.pCoreOf 2 Y₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hAY₂ : A ≤ Subgroup.normalizer (Y₂ : Set G) := hY₂.prop.1.1.2
  have hcA : c ∈ A := hD.mem_A
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  set O := CFSG.Open.pCoreOf 2 Y₂ with hO
  set P := CFSG.pCore 2 ↥Y₂ with hP
  set π := QuotientGroup.mk' P with hπ
  have hsc := Res162.sectionCentralizer_eq_zpowers_of_meetsY4 h hY₂ hm φ₂
  have htriv : ∀ n : ℤ, ∀ y ∈ Y₂, c ^ n * y * (c ^ n)⁻¹ * y⁻¹ ∈ O := by
    intro n y hy
    have hmem : c ^ n ∈ Late.sectionCentralizer A Y₂ O := by
      rw [hO, hsc]
      exact Subgroup.zpow_mem_zpowers c n
    exact hmem.2 y hy
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (Y₂ : Set G) :=
    (Subgroup.zpowers_le.mpr hcA).trans hAY₂
  have hc3g : IsPGroup 3 (Subgroup.zpowers c) := by
    intro z
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp z.2
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hker3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y₂))
    rw [hm]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hlift : ∀ y : ↥Y₂, ∃ k : ↥Y₂, (k : G) ∈ Subgroup.centralizer
      ((Subgroup.zpowers c : Subgroup G) : Set G) ∧ π k = π y := by
    intro y
    refine exists_centralizer_with_same_image_of_trivial_quotient_action 3 Nat.prime_three
      (Subgroup.zpowers c) Y₂ hc3g hcN π hker3 (fun member element => ?_) y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp member.2
    rw [hπ, eq_comm, Step163Alt.mk_eq_mk_iff]
    have h1 := htriv n element element.2
    rw [hn] at h1
    have h2 : (element : G)⁻¹ * ((member : G) * element * (member : G)⁻¹ * (element : G)⁻¹) *
        element ∈ O :=
      (Subgroup.mem_normalizer_iff.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₂) (Y₂.inv_mem element.2)) _).mp h1 |>
        fun h' => by simpa [mul_assoc] using h'
    have he : (element : G)⁻¹ * ((member : G) * element * (member : G)⁻¹ * (element : G)⁻¹) *
        element = (element : G)⁻¹ * ((member : G) * element * (member : G)⁻¹) := by group
    rw [he] at h2
    exact h2
  have hNL : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    normalizer_zpowers_le_normalizer_L h (three_dvd_card_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA)
  set D := L ⊓ Y₂ with hDdef
  set N := (D.subgroupOf Y₂).map π with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn q => ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P q
    obtain ⟨k, hkc, hk⟩ := hlift y
    obtain ⟨d, hd, rfl⟩ := hn
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have hkC : (k : G) ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      have : (k : G) ∈ Subgroup.centralizer ({c} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hkc c (Subgroup.mem_zpowers c)).symm
      exact centralizer_singleton_le_normalizer_zpowers c this
    have hkdk : (k : G) * d * (k : G)⁻¹ ∈ D := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hNL hkC) _).mp (Subgroup.mem_inf.mp hdD).1
      · exact Y₂.mul_mem (Y₂.mul_mem k.2 (Subgroup.mem_inf.mp hdD).2) (Y₂.inv_mem k.2)
    refine ⟨k * d * k⁻¹, Subgroup.mem_subgroupOf.mpr hkdk, ?_⟩
    rw [map_mul, map_mul, map_inv, hk]
  obtain ⟨X, hX, hXLY⟩ := hm
  have hNtop : N = ⊤ := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup (↥Y₂ ⧸ P) := φ₂.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
    · exfalso
      apply Proof162.not_isSolvable_of_mem_scriptY4 hX
      have hXO : X ≤ O := by
        intro x hx
        have hxY : x ∈ Y₂ := (hXLY hx).2
        have hxN : π ⟨x, hxY⟩ ∈ N := ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr (hXLY hx), rfl⟩
        rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          Step163Alt.mem_pCore_two_iff] at hxN
        exact hxN
      have hO2 : IsPGroup 2 X :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₂).to_le hXO
      have := hO2.isNilpotent
      infer_instance
    · exact htop
  intro y hy
  have hmem : π ⟨y, hy⟩ ∈ N := hNtop ▸ Subgroup.mem_top _
  obtain ⟨d, hd, hdy⟩ := hmem
  refine ⟨d, Subgroup.mem_subgroupOf.mp hd, ?_⟩
  exact (Step163Alt.mk_eq_mk_iff d ⟨y, hy⟩).mp hdy

theorem theta_le_pCoreOf_of_seven {L Y : Subgroup G} (hLY : L ≤ Y)
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) :
    ∀ t : ↥L, t ∈ aschbacherSolvableCore 3 ↥L → (t : G) ∈ CFSG.Open.pCoreOf 2 Y := by
  classical
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have hθsol : Group.IsSolvable θ :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
  have hcovL : L = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L := by
    rw [inf_of_le_right hLY]
    exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).symm
  have hcov := Res162.exists_mem_inf_of_cover hcovL
    (by rw [Nat.card_congr φ.toEquiv, Nat.card_congr φL.toEquiv])
  set g₁ : ↥L →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hLY) with hg₁
  have hg₁s : Function.Surjective g₁ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨k, hk, hky⟩ := hcov y y.2
    refine ⟨⟨k, (Subgroup.mem_inf.mp hk).2⟩, ?_⟩
    change QuotientGroup.mk' _ (Subgroup.inclusion hLY ⟨k, _⟩) = QuotientGroup.mk' _ y
    exact (Step163Alt.mk_eq_mk_iff _ _).mpr hky
  have hn : (θ.map g₁).Normal := (inferInstance : θ.Normal).map g₁ hg₁s
  have hsol : Group.IsSolvable (θ.map g₁) :=
    Group.isSolvable_of_surjective (f := g₁.subgroupMap θ) (g₁.subgroupMap_surjective θ)
  have hbot' := eq_bot_of_normal_of_isSolvable_a7 φ (θ.map g₁) hsol
  intro t ht
  have h1 : g₁ t ∈ θ.map g₁ := Subgroup.mem_map_of_mem g₁ ht
  rw [hbot', Subgroup.mem_bot, hg₁, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Step163Alt.mem_pCore_two_iff] at h1
  exact h1

theorem exists_mem_inf_of_seven {A : Subgroup G} {c : G} {L Y₂ : Subgroup G}
    (h : Sec15R G A c L) (hY₂ : Y₂ ∈ scriptY0Star A (lB A)) (hm : MeetsY4 A (lB A) L Y₂)
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    (φ₂ : ↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7)) :
    ∀ l (hl : l ∈ L), ∃ d ∈ L ⊓ Y₂, ∃ hd : d ∈ L,
      (⟨d, hd⟩ : ↥L)⁻¹ * ⟨l, hl⟩ ∈ aschbacherSolvableCore 3 ↥L := by
  classical
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  have hcov₂ := eq_top_of_seven h hY₂ hm φ₂
  set D := L ⊓ Y₂ with hDdef
  have hDL : D ≤ L := inf_le_left
  have hDY : D ≤ Y₂ := inf_le_right
  set f₁ : ↥D →* ↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hDY) with hf₁
  set f₂ : ↥D →* ↥L ⧸ θ := (QuotientGroup.mk' θ).comp (Subgroup.inclusion hDL) with hf₂
  have hf₁s : Function.Surjective f₁ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨d, hd, hdy⟩ := hcov₂ y y.2
    refine ⟨⟨d, hd⟩, ?_⟩
    change QuotientGroup.mk' _ (Subgroup.inclusion hDY ⟨d, hd⟩) = QuotientGroup.mk' _ y
    exact (Step163Alt.mk_eq_mk_iff _ _).mpr hdy
  have hker : f₂.ker ≤ f₁.ker := by
    have hk : f₂.ker = θ.comap (Subgroup.inclusion hDL) := by
      rw [hf₂, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    have hθsol : Group.IsSolvable θ :=
      (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
    have hsolK : Group.IsSolvable f₂.ker := by
      rw [hk]
      exact Group.isSolvable_of_isSolvable_injective
        ((Subgroup.inclusion hDL).subgroupComap_injective θ (Subgroup.inclusion_injective hDL))
    have hn : (f₂.ker.map f₁).Normal := (inferInstance : f₂.ker.Normal).map f₁ hf₁s
    have hsol : Group.IsSolvable (f₂.ker.map f₁) :=
      Group.isSolvable_of_surjective (f := f₁.subgroupMap f₂.ker)
        (f₁.subgroupMap_surjective f₂.ker)
    have hbot' := eq_bot_of_normal_of_isSolvable_a7 φ₂ (f₂.ker.map f₁) hsol
    intro x hx
    have h1 : f₁ x ∈ f₂.ker.map f₁ := Subgroup.mem_map_of_mem f₁ hx
    rw [hbot', Subgroup.mem_bot] at h1
    exact h1
  have hf₂s : Function.Surjective f₂ := surjective_of_ker_le f₁ hf₁s f₂ hker
    (by rw [Nat.card_congr φ₂.toEquiv, Nat.card_congr φL.toEquiv])
  intro l hl
  obtain ⟨d, hd⟩ := hf₂s (QuotientGroup.mk' θ ⟨l, hl⟩)
  refine ⟨d, d.2, hDL d.2, ?_⟩
  have : (Subgroup.inclusion hDL d)⁻¹ * ⟨l, hl⟩ ∈ θ := by
    rw [← QuotientGroup.eq, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply]
    exact hd
  exact this

theorem le_normalizer_of_seven {A : Subgroup G} {c : G} {L Y₂ : Subgroup G}
    (h : Sec15R G A c L) (hY₂ : Y₂ ∈ scriptY0Star A (lB A)) (hm : MeetsY4 A (lB A) L Y₂)
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    (φ₂ : ↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7))
    (hθ : ∀ t : ↥L, t ∈ aschbacherSolvableCore 3 ↥L →
      (t : G) ∈ Subgroup.normalizer (Y₂ : Set G)) :
    L ≤ Subgroup.normalizer (Y₂ : Set G) := by
  intro l hl
  obtain ⟨d, hdD, hdL, hdl⟩ := exists_mem_inf_of_seven h hY₂ hm φL φ₂ l hl
  have h1 := hθ _ hdl
  have h2 : d⁻¹ * l ∈ Subgroup.normalizer (Y₂ : Set G) := by simpa using h1
  have he : l = d * (d⁻¹ * l) := by group
  rw [he]
  exact mul_mem (Subgroup.le_normalizer (Subgroup.mem_inf.mp hdD).2) h2

theorem pCoreOf_le_of_conf162 {A : Subgroup G} {c : G} {L Y₁ Y₂ S : Subgroup G}
    (h : Sec15R G A c L) (hconf : Conf162 A (lB A) c L Y₁ Y₂ S)
    (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h142 : Concl142 A (lB A))
    (hcov : Y₁ = (Y₁ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₁ ∨ c ∈ Y₁) :
    CFSG.Open.pCoreOf 2 Y₁ ≤ S := by
  have h14 := h.toSec14Std
  have hV := Sec17.Proof17Q0.pCoreOf_mem_scriptQ_of_cover h14 h1444 h146 hbot h142
    hconf.maxCE.1.mem₁.prop.1 hcov
  exact Proof162.pCoreOf_le_of_mem_scriptQ h14.isE27 h146 hconf.maxCE.1.s₁ hV

theorem false_of_conf162_a7 {A : Subgroup G} {c : G} {L Y₁ Y₂ S : Subgroup G}
    (h : Sec15R G A c L) (hconf : Conf162 A (lB A) c L Y₁ Y₂ S)
    (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h142 : Concl142 A (lB A))
    (h7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (φ₁ : ↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁ ≃* alternatingGroup (Fin 7))
    (φ₂ : ↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨φL⟩ := h7
  have hLY₁ : L ≤ Y₁ := hconf.le_y
  have hcovL : L = (Y₁ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L := by
    rw [inf_of_le_right hLY₁]
    exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).symm
  have hcov₁ := Res162.eq_sup_of_forall_mem (Res162.exists_mem_inf_of_cover hcovL
    (by rw [Nat.card_congr φ₁.toEquiv, Nat.card_congr φL.toEquiv]))
  have hOS := pCoreOf_le_of_conf162 h hconf h1444 h146 hbot h142 (Or.inl hcov₁)
  have hSN : S ≤ Subgroup.normalizer (Y₂ : Set G) := hconf.maxCE.1.s₂.prop.1.2
  have hLN := le_normalizer_of_seven h hconf.maxCE.1.mem₂ hconf.meets₂ φL φ₂
    (fun t ht => hSN (hOS (theta_le_pCoreOf_of_seven hLY₁ φL φ₁ t ht)))
  exact Res162.false_of_le_normalizer_of_conf162 h hconf h1444 h146 hbot h142 ⟨φL⟩ φ₁ hLN

end Res162b

theorem step162A7R_of_items (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14)
    (h142 : Concl142S14) : Step162A7R := by
  intro G _ _ A c₀ L₀ _ c L Y₁ Y₂ S h hconf _ h7 hY₁ hY₂
  obtain ⟨φ₁⟩ := hY₁
  obtain ⟨φ₂⟩ := hY₂
  have h14 := h.toSec14Std
  exact Res162b.false_of_conf162_a7 h hconf (h1444 G A c L h14) (h146 G A c L h14)
    (hbot G A c L h14) (h142 G A c L h14) h7 φ₁ φ₂

end CFSG.RankThree.PartTwo.Sec16
