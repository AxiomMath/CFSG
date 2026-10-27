module

public import CFSG.Monster.Existence.Census.TwoClasses
public import CFSG.Monster.SteinbergMBXFullShortAlmostSimple
import CFSG.LocalAnalysis.ComponentInitial.SimpleSocleComponent

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.B.TwoA

namespace SteinbergBQ

theorem two_part_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : ∀ B : Subgroup Y, CFSG.IsComponent B →
      ∃ m : ℕ, Odd m ∧ Nat.card (B ⧸ Subgroup.center B) = 2 ^ n * m)
    (B : Subgroup X) (hB : CFSG.IsComponent B) :
    ∃ m : ℕ, Odd m ∧ Nat.card (B ⧸ Subgroup.center B) = 2 ^ n * m := by
  obtain ⟨m, hm, hcard⟩ := h _ (CFSG.LocalCores.isComponent_map_mulEquiv e hB)
  refine ⟨m, hm, ?_⟩
  rw [← hcard]
  exact Nat.card_congr (QuotientGroup.congr _ _ (B.equivMapOfInjective _ e.injective)
    (Subgroup.map_center_eq _)).toEquiv

@[expose] def conjCentEquiv {G : Type*} [Group G] (c s : G) :
    Subgroup.centralizer {s} ≃* Subgroup.centralizer {c * s * c⁻¹} where
  toFun g := ⟨c * g * c⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 g.2
    calc c * g * c⁻¹ * (c * s * c⁻¹) = c * ((g : G) * s) * c⁻¹ := by group
      _ = c * (s * g) * c⁻¹ := by rw [h]
      _ = c * s * c⁻¹ * (c * g * c⁻¹) := by group⟩
  invFun g := ⟨c⁻¹ * g * c, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 g.2
    calc c⁻¹ * g * c * s = c⁻¹ * ((g : G) * (c * s * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * s * c⁻¹) * g) * c := by rw [h]
      _ = s * (c⁻¹ * g * c) := by group⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by
    change c * ((a : G) * b) * c⁻¹ = c * a * c⁻¹ * (c * b * c⁻¹)
    group)

theorem map_subtype_centralizer_eq {G : Type*} [Group G] {K : Subgroup G} (s : K) :
    (Subgroup.centralizer {s}).map K.subtype = K ⊓ Subgroup.centralizer {(s : G)} := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hh)
  · rintro ⟨hg, hc⟩
    refine ⟨⟨g, hg⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hc)

theorem not_isComponent_of_selfCentralizing {X : Type} [Group X] [Finite X] {t : X}
    (hcent : Subgroup.centralizer (inSubgroup (pCore 2) (cent t) : Set X) ≤
      inSubgroup (pCore 2) (cent t))
    (B : Subgroup (cent t)) (hB : CFSG.IsComponent B) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (pCore 2 (cent t)) := pCore_isPGroup
  have hRs : Group.IsSolvable (pCore 2 (cent t)) := by
    have := hR2.isNilpotent
    infer_instance
  have hBR := (CFSG.LocalCores.component_solvable_centralizer hRs
    (pCore_normal (p := 2) (G := cent t)).isSubnormal).1 B hB
  have hBle : B ≤ pCore 2 (cent t) := by
    intro b hb
    have hbR := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hBR hb
    have hbc : (b : X) ∈ Subgroup.centralizer (inSubgroup (pCore 2) (cent t) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨r, hr, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hbR r hr)
    obtain ⟨r, hr, hrb⟩ := hcent hbc
    rwa [show b = r from Subtype.ext hrb.symm]
  have hB2 : IsPGroup 2 B := hR2.to_le hBle
  have : Nontrivial B := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
  have : Group.IsPerfect B := hB.1.1
  have : Group.IsSolvable B := by
    have := hB2.isNilpotent
    infer_instance
  exact Group.IsPerfect.not_isSolvable B inferInstance

theorem two_part_Cfull (B : Subgroup Cfull) (hB : CFSG.IsComponent B) :
    ∃ m : ℕ, Odd m ∧ Nat.card (B ⧸ Subgroup.center B) = 2 ^ 41 * m := by
  obtain ⟨-, -, ⟨A, hAn, -, -, -, hAs, hAab, -, hAcen, hAodd, -, -⟩, -⟩ :=
    full_short_centralizer_almost_simple.{0}
  obtain ⟨-, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.central_extension_simple_socle_component_quotients
      ZstarF_le_center hAn hAs hAab hAcen hB
  obtain ⟨m, hm, hD⟩ := full_short_centralizer_odd_index.2.2.2.2.2.2.2.1
  have hAD : Nat.card A * A.index = 2 ^ 41 * m := by
    rw [Subgroup.card_mul_index, hD]
  have hcop : Nat.Coprime (2 ^ 41) A.index :=
    Nat.Coprime.pow_left 41 (Nat.coprime_two_left.2 hAodd)
  obtain ⟨m', hm'⟩ : 2 ^ 41 ∣ Nat.card A :=
    hcop.dvd_of_dvd_mul_right ⟨m, hAD⟩
  have hmm : m' * A.index = m := by
    rw [hm', mul_assoc] at hAD
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hAD
  refine ⟨m', (Nat.odd_mul.1 (hmm ▸ hm)).1, ?_⟩
  rw [Nat.card_congr e.toEquiv, hm']

theorem two_part_cent_tGmat (B : Subgroup (cent tGmat)) (hB : CFSG.IsComponent B) :
    ∃ m : ℕ, Odd m ∧ Nat.card (B ⧸ Subgroup.center B) = 2 ^ 41 * m :=
  two_part_of_mulEquiv (((cent tGmat).equivMapOfInjective Gmat.subtype
    Gmat.subtype_injective).trans (MulEquiv.subgroupCongr (map_subtype_centralizer_eq tGmat)))
    two_part_Cfull B hB

end SteinbergBQ

open SteinbergBQ

theorem native_M_involution_local_components_two_part :
    ∀ t : Gmat, orderOf t = 2 → ∀ B : Subgroup (Subgroup.centralizer ({t} : Set Gmat)),
      CFSG.IsComponent B → ∃ m : ℕ, Odd m ∧ Nat.card (B ⧸ Subgroup.center B) = 2 ^ 41 * m := by
  intro t ht B hB
  rcases Census.generated_group_two_involution_classes t ht with hx | hs
  · obtain ⟨-, -, hcent, -, -, -⟩ := isTwoBCentralizer_Gmat t hx
    exact (not_isComponent_of_selfCentralizing hcent B hB).elim
  · obtain ⟨c, rfl⟩ := isConj_iff.1 hs
    exact two_part_of_mulEquiv (conjCentEquiv c tGmat).symm two_part_cent_tGmat B hB

end CFSG.Monster.Existence
