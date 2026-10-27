module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3Gen
public import CFSG.RankThree.PartTwo.Sec4.Census.Lift46

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13

theorem isPerfect_center_of_isLThreePi {X : Type} [Group X] (hL : IsLThreePi X)
    (hns : ¬ Group.IsSolvable X) : Group.IsPerfect X ∧ Subgroup.center X = ⊥ := by
  have hperf : Group.IsPerfect X := by
    obtain ⟨p, e, hp, he, hcase⟩ := hL
    rcases hcase with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · haveI := (isPerfect_center_projSL p e he hq).1
      exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    · by_cases hq2 : 2 < p ^ e
      · haveI := (isPerfect_center_projSU p e he hq hq2).1
        exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      · exfalso
        have hp2 : 2 ≤ p := hp.out.two_le
        have he1 : e = 1 := by
          by_contra hne
          have h2e : 2 ≤ e := by omega
          have : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right (by omega) h2e
          have : 4 ≤ p ^ 2 := by nlinarith
          omega
        subst he1
        have hp2' : p = 2 := by rw [pow_one] at hq2; omega
        subst hp2'
        apply hns
        haveI := isSolvable_projSU_two
        exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
  haveI : Nontrivial X := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hns (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _)
  exact ⟨hperf, center_eq_bot_of_isLThreePi hL hperf⟩

section Inner

variable {Γ : Type} [Group Γ] [Finite Γ] {A L : Subgroup Γ} {b : Γ}

theorem eq_zpowers_sup_inf' (hA : Late.IsE27 A) (hbA : b ∈ A) (hb1 : b ≠ 1) (hbL : b ∉ L)
    (h9 : Nat.card (A ⊓ L : Subgroup Γ) = 9) : A = Subgroup.zpowers b ⊔ (A ⊓ L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb3 : orderOf b = 3 := orderOf_eq_prime (hA.1.2 b hbA) hb1
  have hcAL : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr hbA
  have hle : Subgroup.zpowers b ⊔ (A ⊓ L) ≤ A := sup_le hcAL inf_le_left
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hcAL hx⟩ ⟨y, hy.1⟩)
  have hdisj : Subgroup.zpowers b ⊓ (A ⊓ L) = ⊥ := by
    rw [eq_bot_iff, ← Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hb3 hbL]
    exact fun x hx => ⟨hx.2.2, hx.1⟩
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hb3, h9] at hcard
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hA.2])).symm

theorem autThetaQuot_eq_map_conj' (hA : Late.IsE27 A) (hbA : b ∈ A)
    (hLb : L ≤ Subgroup.centralizer ({b} : Set Γ)) (hAc : A = Subgroup.zpowers b ⊔ (A ⊓ L)) :
    Sec4.autThetaQuot A L = (((A ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map
        (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut _) := by
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have hconj : ∀ (g : Γ) (hgN : g ∈ Subgroup.normalizer (L : Set Γ)) (hg : g ∈ L),
      Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨g, hgN⟩) =
        MulAut.conj (QuotientGroup.mk' θ ⟨g, hg⟩) := by
    intro g hgN hg
    ext q
    induction q using QuotientGroup.induction_on with
    | H l =>
      change (((L.normalizerMonoidHom ⟨g, hgN⟩ l : L)) : ↥L ⧸ θ) =
        (QuotientGroup.mk' θ ⟨g, hg⟩) * (l : ↥L ⧸ θ) * (QuotientGroup.mk' θ ⟨g, hg⟩)⁻¹
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      rfl
  apply le_antisymm
  · intro σ hσ
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
    rw [hAc, sup_comm] at haA
    obtain ⟨β, hβ, j, rfl⟩ :=
      Res4L34.exists_eq_mul_zpow_of_mem_sup (B := A ⊓ L) (fun β hβ => hAab β hβ.1 b hbA) haA
    refine ⟨QuotientGroup.mk' θ ⟨β, hβ.2⟩,
      ⟨⟨β, hβ.2⟩, Subgroup.mem_subgroupOf.mpr hβ, rfl⟩, ?_⟩
    rw [← hconj β (L.le_normalizer hβ.2) hβ.2]
    ext q
    induction q using QuotientGroup.induction_on with
    | H l =>
      change (((L.normalizerMonoidHom ⟨β, L.le_normalizer hβ.2⟩ l : L)) : ↥L ⧸ θ) =
        (((L.normalizerMonoidHom ⟨β * b ^ j, haN⟩ l : L)) : ↥L ⧸ θ)
      congr 1
      refine Subtype.ext ?_
      have hlc : Commute (l : Γ) b := Subgroup.mem_centralizer_singleton_iff.mp (hLb l.2)
      change β * (l : Γ) * β⁻¹ = (β * b ^ j) * (l : Γ) * (β * b ^ j)⁻¹
      have hcj : b ^ j * (l : Γ) * (b ^ j)⁻¹ = l := by
        rw [((hlc.symm).zpow_left j).eq]
        group
      calc β * (l : Γ) * β⁻¹ = β * (b ^ j * (l : Γ) * (b ^ j)⁻¹) * β⁻¹ := by rw [hcj]
        _ = (β * b ^ j) * (l : Γ) * (β * b ^ j)⁻¹ := by group
  · rintro _ ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
    have hβ' := Subgroup.mem_subgroupOf.mp hβ
    exact Sec4.mem_autThetaQuot_iff.mpr ⟨β, L.le_normalizer β.2, hβ'.1,
      hconj β (L.le_normalizer β.2) β.2⟩

theorem gen_or_bot_inner
    (hA : Late.IsE27 A) (hbA : b ∈ A) (hb1 : b ≠ 1)
    (hLb : L ≤ Subgroup.centralizer ({b} : Set Γ)) (hbL : b ∉ L)
    (h9 : Nat.card (A ⊓ L : Subgroup Γ) = 9)
    (hQ8 : Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
      Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    (hL : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hns : ¬ Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    sSup {Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card Y ∧
        ∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y} = ⊤ ∨
      ∀ Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), ¬ 3 ∣ Nat.card Y →
        (∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y) → Y = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAc := eq_zpowers_sup_inf' hA hbA hb1 hbL h9
  have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
  have hLc : ∀ l ∈ L, l * b = b * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLb hl)
  have hB : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (by
      have := congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, x.2.1⟩ ⟨y, y.2.1⟩)
      simpa using this)⟩⟩, fun x hx => hA.1.2 x hx.1⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hEq : (A ⊓ L).subgroupOf L = A.subgroupOf L := Subgroup.inf_subgroupOf_right A L
  set Ebar := ((A ⊓ L).subgroupOf L).map π with hEbar
  have hE9 : Nat.card Ebar = 9 := by
    rw [hEbar, hEq, card_map_mk_subgroupOf hA.1, h9]
  have hEe : CFSG.Assembly.IsElemAbelian 3 Ebar := by
    rw [hEbar, hEq]
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π (A.subgroupOf L)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 A L hA.1)
  have hpt : ∀ z ∈ Ebar, z ≠ 1 → ∃ y ∈ A ⊓ L, y ≠ 1 ∧ ∃ hyL : y ∈ L, π ⟨y, hyL⟩ = z := by
    rintro z ⟨y', hy', rfl⟩ hz1
    refine ⟨y', Subgroup.mem_subgroupOf.mp hy', fun hy1 => hz1 ?_, y'.2, rfl⟩
    have : y' = 1 := Subtype.ext hy1
    rw [this, map_one]
  have htrans : ∀ y₀ ∈ Ebar, y₀ ≠ 1 → ∀ y₁ ∈ Ebar, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (Ebar : Set (↥L ⧸ θ)), w * y₀ * w⁻¹ = y₁ := by
    intro z₀ hz₀ hz₀1 z₁ hz₁ hz₁1
    obtain ⟨y₀, hy₀, hy₀1, hy₀L, rfl⟩ := hpt z₀ hz₀ hz₀1
    obtain ⟨y₁, hy₁, hy₁1, hy₁L, rfl⟩ := hpt z₁ hz₁ hz₁1
    obtain ⟨w, hwL, hwN, hw⟩ :=
      exists_conj_eq_of_autIn hb3 hbL hLc hAc hB h9 hQ8 hy₀ hy₁ hy₀1 hy₁1
    refine ⟨π ⟨w, hwL⟩, ?_, ?_⟩
    · have hwN' : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.normalizer
          (((A ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.mp hwN (x : Γ)
      exact Subgroup.le_normalizer_map π ⟨_, hwN', rfl⟩
    · rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext hw
  have hP := autThetaQuot_eq_map_conj' hA hbA hLb hAc
  have hinv : ∀ Y : Subgroup (↥L ⧸ θ), (∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y) ↔
      Ebar ≤ Subgroup.normalizer (Y : Set (↥L ⧸ θ)) := by
    intro Y
    constructor
    · intro h z hz
      have hσ : MulAut.conj z ∈ Sec4.autThetaQuot A L := by
        rw [hP]
        exact ⟨z, hz, rfl⟩
      exact mem_normalizer_of_conj_mem' fun v hv => h _ hσ ⟨v, hv, rfl⟩
    · intro h σ hσ
      rw [hP] at hσ
      obtain ⟨z, hz, rfl⟩ := hσ
      rintro _ ⟨v, hv, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (h hz) v).mp hv
  obtain ⟨p, e, hp, he, hiso⟩ := hL
  have hperf := (isPerfect_center_of_isLThreePi ⟨p, e, hp, he, hiso⟩ hns).1
  rcases hessGen_or_bot he hiso hperf hEe hE9 htrans with h | h
  · left
    rw [eq_top_iff, ← h]
    exact sSup_le_sSup fun Y hY => ⟨hY.1, (hinv Y).mpr hY.2⟩
  · right
    exact fun Y hY3 hYP => h Y hY3 ((hinv Y).mp hYP)

end Inner

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
