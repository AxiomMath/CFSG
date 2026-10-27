module

public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofDefs
public import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.Sporadic.Mathieu.M22
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

namespace Proof1721

section Quot

variable {G : Type} [Group G] [Finite G] {A Y₀ : Subgroup G} [(kerAO2 A Y₀).Normal]

noncomputable abbrev barY0 (A Y₀ : Subgroup G) [(kerAO2 A Y₀).Normal] {x : G} (hx : x ∈ Y₀) :
    ↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀ :=
  QuotientGroup.mk' (kerAO2 A Y₀) ⟨x, Subgroup.mem_sup_right hx⟩

theorem mem_normalizer_oTwoCY0 {t a : G} (htY : t ∈ Y₀) (ha : a ∈ A)
    (hta : t * a * t⁻¹ = a⁻¹) :
    barY0 A Y₀ htY ∈ Subgroup.normalizer
      ((oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) : Subgroup (↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀)) :
        Set (↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀)) := by
  set π := QuotientGroup.mk' (kerAO2 A Y₀) with hπ
  set tb := barY0 A Y₀ htY with htb
  set x := alphaY0 A Y₀ a ha with hx
  have h1 : tb ∈ Subgroup.normalizer ((imgY0 A Y₀ Y₀ : Subgroup _) : Set _) :=
    Subgroup.le_normalizer ⟨⟨t, Subgroup.mem_sup_right htY⟩, htY, rfl⟩
  have hconj : tb * x * tb⁻¹ = x⁻¹ := by
    rw [htb, hx, barY0, alphaY0, ← map_mul, ← map_inv, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext hta
  have h2 : tb ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({x} : Set (↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀)) : Subgroup _) : Set _) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    have hxinv : x⁻¹ * y = y * x⁻¹ := (Commute.inv_left (show Commute x y from hy.symm)).eq
    have hx' : tb * x⁻¹ * tb⁻¹ = x := by
      rw [show tb * x⁻¹ * tb⁻¹ = (tb * x * tb⁻¹)⁻¹ by group, hconj, inv_inv]
    calc tb * y * tb⁻¹ * x = tb * y * tb⁻¹ * (tb * x⁻¹ * tb⁻¹) := by rw [hx']
      _ = tb * (y * x⁻¹) * tb⁻¹ := by group
      _ = tb * (x⁻¹ * y) * tb⁻¹ := by rw [hxinv]
      _ = (tb * x⁻¹ * tb⁻¹) * (tb * y * tb⁻¹) := by group
      _ = x * (tb * y * tb⁻¹) := by rw [hx']
  have h3 : tb ∈ Subgroup.normalizer
      ((imgY0 A Y₀ Y₀ ⊓ Subgroup.centralizer ({x} : Set (↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀)) :
        Subgroup _) : Set _) :=
    Late.le_normalizer_inf (Subgroup.zpowers_le.mpr h1) (Subgroup.zpowers_le.mpr h2)
      (Subgroup.mem_zpowers tb)
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ h3

theorem mem_normalizer_inf_of_mk {X : Subgroup G} (hO2 : CFSG.Open.pCoreOf 2 Y₀ ≤ X) {t : G}
    (htY : t ∈ Y₀)
    (ht : barY0 A Y₀ htY ∈ Subgroup.normalizer ((imgY0 A Y₀ (X ⊓ Y₀) : Subgroup _) : Set _)) :
    t ∈ Subgroup.normalizer ((X ⊓ Y₀ : Subgroup G) : Set G) := by
  set π := QuotientGroup.mk' (kerAO2 A Y₀) with hπ
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxX, hxY⟩ := Subgroup.mem_inf.mp hx
  have htxY : t * x * t⁻¹ ∈ Y₀ := mul_mem (mul_mem htY hxY) (inv_mem htY)
  have himg : π ⟨t * x * t⁻¹, Subgroup.mem_sup_right htxY⟩ ∈ imgY0 A Y₀ (X ⊓ Y₀) := by
    have hxb : π ⟨x, Subgroup.mem_sup_right hxY⟩ ∈ imgY0 A Y₀ (X ⊓ Y₀) :=
      ⟨⟨x, Subgroup.mem_sup_right hxY⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp ht _).mp hxb
    have e : π ⟨t * x * t⁻¹, Subgroup.mem_sup_right htxY⟩ =
        barY0 A Y₀ htY * π ⟨x, Subgroup.mem_sup_right hxY⟩ * (barY0 A Y₀ htY)⁻¹ := by
      rw [barY0, ← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [e]
    exact h1
  obtain ⟨y, hy, hyeq⟩ := himg
  have hyX : (y : G) ∈ X ⊓ Y₀ := Subgroup.mem_subgroupOf.mp hy
  have hker : (y : G)⁻¹ * (t * x * t⁻¹) ∈ CFSG.Open.pCoreOf 2 Y₀ := by
    have h1 := QuotientGroup.eq.mp hyeq
    exact h1
  have hmem : t * x * t⁻¹ = (y : G) * ((y : G)⁻¹ * (t * x * t⁻¹)) := by group
  have hX : t * x * t⁻¹ ∈ X := by
    rw [hmem]
    exact mul_mem (Subgroup.mem_inf.mp hyX).1 (hO2 hker)
  exact Subgroup.mem_inf.mpr ⟨hX, htxY⟩

end Quot

section Lift

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_dvd_card_quot {L : Subgroup G} (h27 : ¬ 27 ∣ Nat.card L) :
    ¬ 27 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := fun h => h27 (h.trans
    (Dvd.intro _ (Subgroup.card_eq_card_quotient_mul_card_subgroup
      (aschbacherSolvableCore 3 ↥L)).symm))

theorem not_dvd_card_L_of_quot {L : Subgroup G}
    (h27 : ¬ 27 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L)) : ¬ 27 ∣ Nat.card L := by
  intro h
  apply h27
  have hcop : Nat.Coprime 27 (Nat.card (aschbacherSolvableCore 3 ↥L)) := by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L)] at h
  exact hcop.dvd_of_dvd_mul_right h

theorem exists_inverting_of_quot (hK : KS1721Invert) {L : Subgroup G}
    (htype : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22))
    {E : Subgroup G} (hEL : E ≤ L) (hE9 : Nat.card E = 9) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (h27 : ¬ 27 ∣ Nat.card L) :
    ∃ t ∈ L, t ∈ Subgroup.normalizer (E : Set G) ∧ ∀ x ∈ E, t * x * t⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E' : Subgroup ↥L := E.subgroupOf L with hE'
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE9]
  have hE'3 : IsPGroup 3 E' := IsPGroup.of_card (n := 2) (by rw [hE'9]; norm_num)
  have hinj : Set.InjOn π (E' : Set ↥L) := injOn_mk_of_isPGroup Nat.prime_three hE'3
  have hEb9 : Nat.card (E'.map π) = 9 := by rw [card_map_eq_of_injOn π hinj, hE'9]
  have hEb3 : ∀ y ∈ E'.map π, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE3 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [this, map_one]
  obtain ⟨gb, hgbN, hgb⟩ := hK _ htype (E'.map π) hEb9 hEb3 (not_dvd_card_quot h27)
  rw [normalizer_map_mk_eq hE'3] at hgbN
  obtain ⟨g, hgN, rfl⟩ := hgbN
  refine ⟨(g : G), g.2, Subgroup.mem_normalizer_fintype fun x hx => ?_, fun x hx => ?_⟩
  · have hxL : x ∈ L := hEL hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hgN ⟨x, hxL⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_subgroupOf.mp h1
  · have hxL : x ∈ L := hEL hx
    have hx' : (⟨x, hxL⟩ : ↥L) ∈ E' := Subgroup.mem_subgroupOf.mpr hx
    have h1 : g * ⟨x, hxL⟩ * g⁻¹ ∈ E' := (Subgroup.mem_normalizer_iff.mp hgN _).mp hx'
    have h2 : (⟨x, hxL⟩ : ↥L)⁻¹ ∈ E' := inv_mem hx'
    have h3 : π (g * ⟨x, hxL⟩ * g⁻¹) = π ((⟨x, hxL⟩ : ↥L)⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_inv]
      exact hgb _ ⟨⟨x, hxL⟩, hx', rfl⟩
    have h4 := hinj h1 h2 h3
    exact congrArg Subtype.val h4

end Lift

section Decomp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem eq_zpowers_sup_inf (h : Sec17Std G A c L Y₀) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr h.c_mem) inf_le_left
  have hcard := (isElemAbelian_zpowers_sup_of_card_nine h.c_pow_three
    (fun hcB => hcL (Subgroup.mem_inf.mp hcB).2) le_rfl h9
    (fun b hb => h.isE27.1.2 b hb.1) (fun b hb => h.commute_of_mem h.c_mem hb.1)).2
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.isE27.2, hcard])).symm

theorem mem_normalizer_A_of_mem_L (h : Sec17Std G A c L Y₀)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {t : G} (htL : t ∈ L)
    (htE : t ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G)) :
    t ∈ Subgroup.normalizer (A : Set G) := by
  rw [eq_zpowers_sup_inf h h9]
  exact mem_normalizer_sup
    (Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer (h.le_centralizer_c htL)) htE

end Decomp

section LType

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G}

theorem not_dvd_card_L (h : Sec17Y1 G A c L Y₀ Y₁ S p P)
    (hSyl : Claim1721SylL3)
    (htype : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    ¬ 27 ∣ Nat.card L := by
  rcases htype with hL3 | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact hSyl G A c L Y₀ Y₁ S p P h hL3
  · refine not_dvd_card_L_of_quot ?_
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · refine not_dvd_card_L_of_quot ?_
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Mathieu.card_M22]
    decide

end LType

end Proof1721

end CFSG.RankThree.PartTwo.Sec17
