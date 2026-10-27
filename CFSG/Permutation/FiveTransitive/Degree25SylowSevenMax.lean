module

public import CFSG.Permutation.FiveTransitive.Degree25SmallSupport

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

theorem sylow_seven_card_ne_three_hundred_forty_three
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (S : Sylow 7 P) :
    Nat.card S ≠ 343 := by
  classical
  intro hScard
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let F : Set X := MulAction.fixedPoints S X
  have hFmod :=
    S.isPGroup'.card_modEq_card_fixedPoints X
  have hFmod' :
      4 = Fintype.card F % 7 := by
    change Nat.card X % 7 = Nat.card F % 7 at hFmod
    rw [Nat.card_eq_fintype_card, hcard,
      Nat.card_eq_fintype_card] at hFmod
    norm_num at hFmod
    simpa only [Fintype.card_subtype] using hFmod
  have hFcardGe : 4 ≤ Fintype.card F := by
    have hmodLe :
        Fintype.card F % 7 ≤ Fintype.card F :=
      Nat.mod_le _ _
    omega
  have hSnontrivial : Nontrivial S :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hScard]
      norm_num)
  letI : Nontrivial S := hSnontrivial
  have hFne : F ≠ Set.univ := by
    obtain ⟨u, hu⟩ := exists_ne (1 : S)
    intro hFuniv
    have hfixedU : MulAction.fixedBy X u = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      have hz : z ∈ F := by
        rw [hFuniv]
        trivial
      exact hz u
    exact hu
      ((MulAction.fixedBy_eq_univ_iff_eq_one
        (M := S) (α := X)).mp hfixedU)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ F := by
    by_contra h
    push Not at h
    exact hFne (Set.eq_univ_of_forall h)
  let O₁ : Set X := MulAction.orbit S x
  let R₁ : Subgroup S := MulAction.stabilizer S x
  have hO₁cardNe : Fintype.card O₁ ≠ 1 := by
    intro hone
    apply hx
    apply MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr
    simpa only [F, O₁] using hone
  have hO₁cardPos : 0 < Fintype.card O₁ :=
    Fintype.card_pos_iff.mpr
      ⟨⟨x, MulAction.mem_orbit_self x⟩⟩
  have hO₁cardGt : 1 < Fintype.card O₁ := by omega
  have hO₁cardLe : Fintype.card O₁ ≤ 25 := by
    calc
      Fintype.card O₁ ≤ Fintype.card X :=
        Fintype.card_le_of_injective
          (fun z : O₁ => (z : X)) Subtype.val_injective
      _ = 25 := hcard
  have horbit₁ :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      S x
  have hScardF : Fintype.card S = 343 := by
    rw [← Nat.card_eq_fintype_card, hScard]
  have horbit₁' :
      Fintype.card O₁ * Fintype.card R₁ = 343 := by
    rw [hScardF] at horbit₁
    simpa only [O₁, R₁] using horbit₁
  have hO₁dvd : Fintype.card O₁ ∣ 343 :=
    ⟨Fintype.card R₁, horbit₁'.symm⟩
  have hO₁card : Fintype.card O₁ = 7 := by
    interval_cases Fintype.card O₁
    all_goals try norm_num at hO₁dvd
    all_goals omega
  have hR₁card : Nat.card R₁ = 49 := by
    rw [Nat.card_eq_fintype_card]
    rw [hO₁card] at horbit₁'
    omega
  have hR₁index : R₁.index = 7 := by
    change (MulAction.stabilizer S x).index = 7
    rw [MulAction.index_stabilizer]
    rw [← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card]
    exact hO₁card
  have hR₁normal : R₁.Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hR₁index, hScard]
    norm_num
  have hR₁fixesOrbit (v : R₁) {z : X}
      (hz : z ∈ O₁) : ((v : R₁) : S) • z = z := by
    obtain ⟨t, rfl⟩ :=
      MulAction.mem_orbit_iff.mp hz
    have hconj :
        t⁻¹ * (v : S) * t ∈ R₁ :=
      hR₁normal.conj_mem (v : S) v.prop t⁻¹
    have hconjFix :
        (t⁻¹ * (v : S) * t) • x = x :=
      MulAction.mem_stabilizer_iff.mp hconj
    calc
      (v : S) • (t • x) = ((v : S) * t) • x :=
        (mul_smul _ _ _).symm
      _ = (t * (t⁻¹ * (v : S) * t)) • x := by
        congr 1
        group
      _ = t • ((t⁻¹ * (v : S) * t) • x) :=
        mul_smul _ _ _
      _ = t • x := by rw [hconjFix]
  have hexSecond :
      ∃ y : X, y ∉ F ∪ O₁ := by
    by_contra h
    push Not at h
    have hR₁nontrivial : Nontrivial R₁ :=
      Finite.one_lt_card_iff_nontrivial.mp (by
        rw [hR₁card]
        norm_num)
    letI : Nontrivial R₁ := hR₁nontrivial
    obtain ⟨v, hv⟩ := exists_ne (1 : R₁)
    have hvPerm :
        ((((v : R₁) : S) : P) : Equiv.Perm X) = 1 := by
      ext z
      rcases h z with hzF | hzO
      · change ((v : R₁) : S) • z = z
        exact hzF ((v : R₁) : S)
      · change ((v : R₁) : S) • z = z
        exact hR₁fixesOrbit v hzO
    apply hv
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hvPerm
  obtain ⟨y, hy⟩ := hexSecond
  have hyF : y ∉ F := fun h => hy (Or.inl h)
  have hyO₁ : y ∉ O₁ := fun h => hy (Or.inr h)
  let O₂ : Set X := MulAction.orbit S y
  let R₂ : Subgroup S := MulAction.stabilizer S y
  have hO₂cardNe : Fintype.card O₂ ≠ 1 := by
    intro hone
    apply hyF
    apply MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr
    simpa only [F, O₂] using hone
  have hO₂cardPos : 0 < Fintype.card O₂ :=
    Fintype.card_pos_iff.mpr
      ⟨⟨y, MulAction.mem_orbit_self y⟩⟩
  have hO₂cardGt : 1 < Fintype.card O₂ := by omega
  have hO₂cardLe : Fintype.card O₂ ≤ 25 := by
    calc
      Fintype.card O₂ ≤ Fintype.card X :=
        Fintype.card_le_of_injective
          (fun z : O₂ => (z : X)) Subtype.val_injective
      _ = 25 := hcard
  have horbit₂ :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      S y
  have horbit₂' :
      Fintype.card O₂ * Fintype.card R₂ = 343 := by
    rw [hScardF] at horbit₂
    simpa only [O₂, R₂] using horbit₂
  have hO₂dvd : Fintype.card O₂ ∣ 343 :=
    ⟨Fintype.card R₂, horbit₂'.symm⟩
  have hO₂card : Fintype.card O₂ = 7 := by
    interval_cases Fintype.card O₂
    all_goals try norm_num at hO₂dvd
    all_goals omega
  have hR₂index : R₂.index = 7 := by
    change (MulAction.stabilizer S y).index = 7
    rw [MulAction.index_stabilizer]
    rw [← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card]
    exact hO₂card
  have hR₂normal : R₂.Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hR₂index, hScard]
    norm_num
  have hR₂fixesOrbit (v : R₂) {z : X}
      (hz : z ∈ O₂) : ((v : R₂) : S) • z = z := by
    obtain ⟨t, rfl⟩ :=
      MulAction.mem_orbit_iff.mp hz
    have hconj :
        t⁻¹ * (v : S) * t ∈ R₂ :=
      hR₂normal.conj_mem (v : S) v.prop t⁻¹
    have hconjFix :
        (t⁻¹ * (v : S) * t) • y = y :=
      MulAction.mem_stabilizer_iff.mp hconj
    calc
      (v : S) • (t • y) = ((v : S) * t) • y :=
        (mul_smul _ _ _).symm
      _ = (t * (t⁻¹ * (v : S) * t)) • y := by
        congr 1
        group
      _ = t • ((t⁻¹ * (v : S) * t) • y) :=
        mul_smul _ _ _
      _ = t • y := by rw [hconjFix]
  have hO₁O₂ : Disjoint O₁ O₂ := by
    rcases MulAction.orbit.eq_or_disjoint (G := S) x y with heq | hdisj
    · exfalso
      apply hyO₁
      change y ∈ MulAction.orbit S x
      rw [heq]
      exact MulAction.mem_orbit_self y
    · exact hdisj
  have hFO₁ : Disjoint F O₁ := by
    rw [Set.disjoint_left]
    intro z hzF hzO
    obtain ⟨t, ht⟩ :=
      MulAction.mem_orbit_iff.mp hzO
    have htInv : t⁻¹ • z = z := hzF t⁻¹
    apply hx
    have hxz : x = z := by
      calc
        x = t⁻¹ • (t • x) := by simp
        _ = t⁻¹ • z := by rw [ht]
        _ = z := htInv
    rwa [hxz]
  have hFO₂ : Disjoint F O₂ := by
    rw [Set.disjoint_left]
    intro z hzF hzO
    obtain ⟨t, ht⟩ :=
      MulAction.mem_orbit_iff.mp hzO
    have htInv : t⁻¹ • z = z := hzF t⁻¹
    apply hyF
    have hyz : y = z := by
      calc
        y = t⁻¹ • (t • y) := by simp
        _ = t⁻¹ • z := by rw [ht]
        _ = z := htInv
    rwa [hyz]
  let K : Subgroup S := R₁ ⊓ R₂
  have hKindexLe : K.index ≤ 49 := by
    calc
      K.index = (R₁ ⊓ R₂).index := rfl
      _ ≤ R₁.index * R₂.index :=
        Subgroup.index_inf_le
      _ = 49 := by rw [hR₁index, hR₂index]
  have hKindexCard := K.index_mul_card
  have hKcardGe : 7 ≤ Nat.card K := by
    rw [hScard] at hKindexCard
    nlinarith [Nat.card_pos (α := K)]
  have hKnontrivial : Nontrivial K :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nontrivial K := hKnontrivial
  obtain ⟨v, hv⟩ := exists_ne (1 : K)
  let vS : S := v
  let vP : P := vS
  let w : Equiv.Perm X := vP
  have hfixO₁ {z : X} (hz : z ∈ O₁) : w z = z := by
    let v₁ : R₁ := ⟨vS, v.prop.1⟩
    exact hR₁fixesOrbit v₁ hz
  have hfixO₂ {z : X} (hz : z ∈ O₂) : w z = z := by
    let v₂ : R₂ := ⟨vS, v.prop.2⟩
    exact hR₂fixesOrbit v₂ hz
  let U : Set X := F ∪ (O₁ ∪ O₂)
  have hfixU {z : X} (hz : z ∈ U) : w z = z := by
    rcases hz with hzF | hzO
    · exact hzF vS
    · rcases hzO with hzO₁ | hzO₂
      · exact hfixO₁ hzO₁
      · exact hfixO₂ hzO₂
  have hFncard : F.ncard = Fintype.card F := by
    rw [← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card]
  have hO₁ncard : O₁.ncard = 7 := by
    rw [← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card]
    exact hO₁card
  have hO₂ncard : O₂.ncard = 7 := by
    rw [← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card]
    exact hO₂card
  have hFUdisjoint : Disjoint F (O₁ ∪ O₂) :=
    hFO₁.union_right hFO₂
  have hUncard : U.ncard = F.ncard + 14 := by
    change (F ∪ (O₁ ∪ O₂)).ncard = F.ncard + 14
    rw [Set.ncard_union_eq hFUdisjoint,
      Set.ncard_union_eq hO₁O₂, hO₁ncard, hO₂ncard]
  have hUncardGe : 18 ≤ U.ncard := by
    rw [hUncard, hFncard]
    omega
  have hUcomplCard : Uᶜ.ncard ≤ 7 := by
    have htotal := Set.ncard_add_ncard_compl U
    rw [Nat.card_eq_fintype_card, hcard] at htotal
    omega
  have hsuppSubset : (w.support : Set X) ⊆ Uᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzU
    exact Equiv.Perm.mem_support.mp hz (hfixU hzU)
  have hsuppCard : w.support.card ≤ 7 := by
    rw [← Set.ncard_coe_finset]
    exact
      (Set.ncard_le_ncard hsuppSubset).trans hUcomplCard
  have hwNe : w ≠ 1 := by
    intro hw
    apply hv
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hw
  exact hnotAlt
    (alternatingGroup_le_of_nontrivial_support_le_seven
      X P hcard h5 vP.prop hwNe hsuppCard)

end FiveTransitive.Degree25

end CFSG
