module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.T1531Close
public import CFSG.Quasithin.EmptyFaithful.T1531In66a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace S1567

section General

variable {G : Type*} [Group G] [Finite G]

theorem pCoreOf_eq_inf_pCoreOf_of_normal {Y H : Subgroup G} (hYH : Y ≤ H)
    (hH : H ≤ Subgroup.normalizer (Y : Set G)) : pCoreOf 2 Y = Y ⊓ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine le_inf (pCoreOf_le 2 Y) ?_
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYH)
      (hH.trans (normalizer_le_normalizer_pCoreOf 2 Y)) (pCoreOf_isPGroup 2 Y)
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun y hy => ?_)
      (pCoreOf_isPGroup 2 H).to_inf_right
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, le_normalizer_pCoreOf 2 H (hYH hy)⟩

theorem nonempty_oTwoQuot_mulEquiv_zmod_three {Y H : Subgroup G} (hYH : Y ≤ H)
    (hH : H ≤ Subgroup.normalizer (Y : Set G))
    (hgen : Y ≤ Subgroup.closure {x | x ∈ Y ∧ Odd (orderOf x)})
    (hS3 : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3))) (hY : ¬ Y ≤ pCoreOf 2 H) :
    Nonempty (OTwoQuot Y ≃* Multiplicative (ZMod 3)) := by
  classical
  obtain ⟨e⟩ := hS3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : ↥Y →* Equiv.Perm (Fin 3) :=
    (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).comp (Subgroup.inclusion hYH)
  have hmemH : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H ↔ x ∈ CFSG.Open.pCore 2 ↥H := fun x =>
    Subgroup.mem_map_iff_mem H.subtype_injective
  have hmemY : ∀ y : ↥Y, (y : G) ∈ pCoreOf 2 Y ↔ y ∈ CFSG.Open.pCore 2 ↥Y := fun y =>
    Subgroup.mem_map_iff_mem Y.subtype_injective
  have hφker : ∀ y : ↥Y, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H := fun y =>
    (e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)).trans
      (hmemH (Subgroup.inclusion hYH y)).symm
  have hker : CFSG.Open.pCore 2 ↥Y = φ.ker := by
    ext y
    rw [← hmemY y, pCoreOf_eq_inf_pCoreOf_of_normal hYH hH, MonoidHom.mem_ker, hφker y]
    exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
  have hsign : ∀ y : ↥Y, Equiv.Perm.sign (φ y) = 1 := by
    let σ : ↥Y →* ℤˣ := Equiv.Perm.sign.comp φ
    have hodd : ∀ x : G, ∀ hx : x ∈ Y, Odd (orderOf x) → σ ⟨x, hx⟩ = 1 := by
      intro x hx ho
      have h2 : orderOf (⟨x, hx⟩ : ↥Y) = orderOf x := (Subgroup.orderOf_coe ⟨x, hx⟩).symm
      have h1 : orderOf (σ ⟨x, hx⟩) ∣ orderOf x := by
        rw [← h2]
        exact orderOf_map_dvd σ _
      have h3 : orderOf (σ ⟨x, hx⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one (Int.units_sq _)
      have hcop : Nat.Coprime 2 (orderOf x) := Nat.coprime_two_left.mpr ho
      exact orderOf_eq_one_iff.mp
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h3 hcop) h1)
    have hle : Y ≤ σ.ker.map Y.subtype := by
      refine hgen.trans ((Subgroup.closure_le _).mpr ?_)
      rintro x ⟨hxY, hxo⟩
      exact ⟨⟨x, hxY⟩, hodd x hxY hxo, rfl⟩
    intro y
    obtain ⟨y', hy', hyy'⟩ := hle y.2
    have hyy : y' = y := Subtype.ext hyy'
    rw [hyy] at hy'
    exact hy'
  have hrange_le : φ.range ≤ alternatingGroup (Fin 3) := by
    rintro _ ⟨y, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mpr (hsign y)
  have hcardA : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 3)
    rw [Nat.card_perm] at h
    have h6 : (Nat.card (Fin 3)).factorial = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    omega
  have hrange_ne : φ.range ≠ ⊥ := by
    obtain ⟨y, hyY, hy⟩ := Set.not_subset.mp hY
    intro hbot
    have hmem : φ ⟨y, hyY⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hy ((hφker ⟨y, hyY⟩).mp hmem)
  have hcardR : Nat.card φ.range = 3 := by
    have hdvd : Nat.card φ.range ∣ Nat.card (alternatingGroup (Fin 3)) :=
      Subgroup.card_dvd_of_le hrange_le
    rw [hcardA] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hrange_ne
    · exact h
  have hcardZ : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    simp
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (mulEquivOfPrimeCardEq hcardR hcardZ))⟩

end General

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem YE_TE_le_normalizer_YE (c : Ctx153 G T Mc M V₁ V₂ t) :
    YE153 Mc M E ⊔ TE153 T E ≤ Subgroup.normalizer (YE153 Mc M E : Set G) :=
  sup_le Subgroup.le_normalizer (TE153_le_normalizer_YE153 c)

theorem pCoreOf_YE (c : Ctx153 G T Mc M V₁ V₂ t) (r66 : Res15366B T Mc M V₁ V₂ E) :
    pCoreOf 2 (YE153 Mc M E) = YE153 Mc M E ⊓ Subgroup.centralizer (E : Set G) := by
  have h1 : YE153 Mc M E ⊓ (YE153 Mc M E ⊔ TE153 T E) = YE153 Mc M E :=
    inf_eq_left.mpr le_sup_left
  rw [pCoreOf_eq_inf_pCoreOf_of_normal le_sup_left (YE_TE_le_normalizer_YE c), r66.pCore_YETE,
    ← inf_assoc, h1]

theorem YE_quot (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) :
    Nonempty (OTwoQuot (YE153 Mc M E) ≃* Multiplicative (ZMod 3)) := by
  have hgen : YE153 Mc M E ≤ Subgroup.closure {x | x ∈ YE153 Mc M E ∧ Odd (orderOf x)} :=
    Subgroup.closure_mono fun x hx => ⟨mem_oTwoUpper_of_odd hx.1 hx.2, hx.2⟩
  have hnc : ¬ YE153 Mc M E ≤ pCoreOf 2 (YE153 Mc M E ⊔ TE153 T E) := by
    intro hle
    obtain ⟨-, y, hy, ⟨e, he, hne⟩, -⟩ := CFSG.Quasithin.Y_facts h113 c L
    have hyC : y ∈ Subgroup.centralizer (E : Set G) := by
      have hy' := hle hy
      rw [r66.pCore_YETE] at hy'
      exact hy'.2
    apply hne
    have hcomm := Subgroup.mem_centralizer_iff.mp hyC e he
    rw [← hcomm]
    group
  exact nonempty_oTwoQuot_mulEquiv_zmod_three le_sup_left (YE_TE_le_normalizer_YE c) hgen
    r66.quot_S3 hnc

end Main

end S1567

end CFSG.Quasithin
