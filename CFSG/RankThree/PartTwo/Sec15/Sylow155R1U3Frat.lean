module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Cover
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Deg16
import CFSG.GroupTheory.CoprimeSectionStability

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec11.LSSolvableProof (card_projSL_two_even isSimpleGroup_projSL)
open scoped commutatorElement

private theorem res1_le_sup_inf_normalizer {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] {H Y S : Subgroup P} (hYH : Y ≤ H) (hn : H ≤ Subgroup.normalizer (Y : Set P))
    (hS : CFSG.ABGLocalTools.IsSylowOf p S Y) :
    H ≤ Y ⊔ (H ⊓ Subgroup.normalizer (S : Set P)) := by
  intro x hx
  have hxY : x ∈ Subgroup.normalizer (Y : Set P) := hn hx
  have hS' : CFSG.ABGLocalTools.IsSylowOf p (S.map (MulAut.conj x).toMonoidHom) Y := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hxY s).1 (hS.le hs)
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hS.card_eq]
  obtain ⟨k, hk, hconj⟩ := hS.exists_mem_conj hS'
  have hkx : k⁻¹ * x ∈ Subgroup.normalizer (S : Set P) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have e1 : x * s * x⁻¹ ∈ S.map (MulAut.conj x).toMonoidHom ↔ s ∈ S := by
      constructor
      · rintro ⟨t, ht, hts⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hts
        exact mul_left_cancel (mul_right_cancel hts) ▸ ht
      · exact fun hs => ⟨s, hs, rfl⟩
    have e2 := hconj (x * s * x⁻¹)
    rw [e1, show k⁻¹ * (x * s * x⁻¹) * k = (k⁻¹ * x) * s * (k⁻¹ * x)⁻¹ by group] at e2
    exact e2
  rw [show x = k * (k⁻¹ * x) by group]
  exact Subgroup.mul_mem_sup hk ⟨H.mul_mem (H.inv_mem (hYH hk)) hx, hkx⟩

theorem exists_perfect_cover_act_sylow_of_centralizer {P Q : Type*} [Group P] [Finite P]
    [Group Q] (ρ : P →* Q) {p : ℕ} [Fact p.Prime] {j : P} (hj : IsPGroup p (Subgroup.zpowers j))
    {S B : Subgroup Q} (hS : ⁅S, S⁆ = S) (hS1 : S ≠ ⊥)
    (hSj : S ≤ Subgroup.centralizer {ρ j}) (hSρ : S ≤ ρ.range) (hB : Group.IsSolvable B)
    (hcent : ∀ x ∈ Subgroup.centralizer {j}, ρ x ∈ B) :
    ∃ Pi SK : Subgroup P, Pi.map ρ = S ∧ ⁅Pi, Pi⁆ = Pi ∧
      Group.IsNilpotent ↥(ρ.comp Pi.subtype).ker ∧ CFSG.ABGLocalTools.IsSylowOf p SK ρ.ker ∧
      Pi ≤ Subgroup.normalizer (SK : Set P) ∧ j ∈ Subgroup.normalizer (SK : Set P) ∧
      ∃ x ∈ Pi, ∃ s ∈ SK, x * s * x⁻¹ ≠ s := by
  classical
  set Nst : Subgroup P := (Subgroup.centralizer {ρ j}).comap ρ with hNst
  set Γ : Subgroup P := (Subgroup.zpowers (ρ j)).comap ρ with hΓ
  have hcomm : ∀ x ∈ Nst, ∀ y ∈ Γ, Commute (ρ x) (ρ y) := by
    intro x hx y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hy)
    rw [← hk]
    exact Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hx) k
  have hjΓ : j ∈ Γ := Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
  have hΓN : Γ ≤ Nst := by
    refine Subgroup.comap_mono (Subgroup.zpowers_le.mpr ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hNΓ : Nst ≤ Subgroup.normalizer (Γ : Set P) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : ρ (x * h * x⁻¹) = ρ h := by
        rw [map_mul, map_mul, (hcomm x hx h hh).eq, mul_assoc (ρ h), ← map_mul, mul_inv_cancel,
          map_one, mul_one]
      exact Subgroup.mem_comap.mpr (by rw [h1]; exact hh)
    · intro hh
      have h2 := (hcomm x⁻¹ (Nst.inv_mem hx) _ hh).eq
      have h1 : ρ h = ρ (x * h * x⁻¹) := by
        calc ρ h = ρ (x⁻¹ * (x * h * x⁻¹) * x) := by congr 1; group
          _ = ρ x⁻¹ * ρ (x * h * x⁻¹) * ρ x := by simp only [map_mul]
          _ = ρ (x * h * x⁻¹) * (ρ x⁻¹ * ρ x) := by rw [h2, mul_assoc (ρ (x * h * x⁻¹))]
          _ = ρ (x * h * x⁻¹) := by rw [← map_mul, inv_mul_cancel, map_one, mul_one]
      exact Subgroup.mem_comap.mpr (by rw [h1]; exact hh)
  obtain ⟨Sj, hSj', hjSj⟩ : ∃ Sj : Subgroup P, CFSG.ABGLocalTools.IsSylowOf p Sj Γ ∧ j ∈ Sj := by
    have hB' : IsPGroup p ((Subgroup.zpowers j).subgroupOf Γ) := hj.comap_subtype
    obtain ⟨T, hT⟩ := hB'.exists_le_sylow
    refine ⟨(T : Subgroup Γ).map Γ.subtype, ⟨T, rfl⟩, ?_⟩
    exact ⟨⟨j, hjΓ⟩, hT (show (⟨j, hjΓ⟩ : Γ) ∈ (Subgroup.zpowers j).subgroupOf Γ from
      Subgroup.mem_zpowers _), rfl⟩
  have hSjΓ : Sj ≤ Γ := hSj'.le
  set Λ : Subgroup P := Nst ⊓ Subgroup.normalizer (Sj : Set P) with hΛ
  have hfrat : Nst ≤ Γ ⊔ Λ := res1_le_sup_inf_normalizer hΓN hNΓ hSj'
  have hjΛ : j ∈ Λ := ⟨hΓN hjΓ, Subgroup.le_normalizer hjSj⟩
  have hSΛ : S ≤ Λ.map ρ := by
    intro s hs
    obtain ⟨x, rfl⟩ := hSρ hs
    have hxN : x ∈ Nst := Subgroup.mem_comap.mpr (hSj hs)
    have hle : (Γ ⊔ Λ).map ρ ≤ Λ.map ρ := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ le_rfl
      refine (Subgroup.map_comap_le _ _).trans (Subgroup.zpowers_le.mpr ?_)
      exact ⟨j, hjΛ, rfl⟩
    exact hle ⟨x, hfrat hxN, rfl⟩
  obtain ⟨Pi, hPiΛ, hPiS, hPi, hnil⟩ := exists_perfect_cover_nilpotent ρ Λ S hS hSΛ
  have hPiN : ∀ x ∈ Pi, x ∈ Nst := fun x hx => (hPiΛ hx).1
  have hPiSj : ∀ x ∈ Pi, x ∈ Subgroup.normalizer (Sj : Set P) := fun x hx => (hPiΛ hx).2
  have hkerN : ∀ x : P, x ∈ Subgroup.normalizer (ρ.ker : Set P) := by
    intro x
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, map_mul, map_mul, map_inv]
    constructor
    · intro h1
      rw [h1, mul_one, mul_inv_cancel]
    · intro h1
      calc ρ h = (ρ x)⁻¹ * (ρ x * ρ h * (ρ x)⁻¹) * ρ x := by group
        _ = 1 := by rw [h1, mul_one, inv_mul_cancel]
  have hkerΓ : ρ.ker ≤ Γ := fun k hk =>
    Subgroup.mem_comap.mpr (by rw [MonoidHom.mem_ker.mp hk]; exact Subgroup.one_mem _)
  have hSK : CFSG.ABGLocalTools.IsSylowOf p (Sj ⊓ ρ.ker) ρ.ker :=
    hSj'.inf_of_le_normalizer hkerΓ fun x _ => hkerN x
  have hnorm : ∀ x ∈ Subgroup.normalizer (Sj : Set P),
      x ∈ Subgroup.normalizer ((Sj ⊓ ρ.ker : Subgroup P) : Set P) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact and_congr ((Subgroup.mem_normalizer_iff.mp hx) h)
      ((Subgroup.mem_normalizer_iff.mp (hkerN x)) h)
  refine ⟨Pi, Sj ⊓ ρ.ker, hPiS, hPi, hnil, hSK,
    fun x hx => hnorm x (hPiSj x hx), hnorm j (Subgroup.le_normalizer hjSj), ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 : ⁅Sj, Pi⁆ ≤ Sj ⊓ ρ.ker := by
    rw [Subgroup.commutator_le]
    intro s hs x hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def,
        show s * x * s⁻¹ * x⁻¹ = s * (x * s⁻¹ * x⁻¹) by group]
      exact Sj.mul_mem hs
        ((Subgroup.mem_normalizer_iff.mp (hPiSj x hx) s⁻¹).mp (Sj.inv_mem hs))
    · rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact (hcomm x (hPiN x hx) s (hSjΓ hs)).symm
  have h2 : ⁅Sj ⊓ ρ.ker, Pi⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro s hs x hx
    have := hcon x hx s hs
    calc x * s = x * s * x⁻¹ * x := by group
      _ = s * x := by rw [this]
  have h3 : ⁅Sj, Pi⁆ = ⊥ :=
    CFSG.GroupTheory.CoprimeSection.commutator_eq_bot_of_two_step hPi h1 h2
  have hPiC : Pi ≤ Subgroup.centralizer {j} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h4 : ⁅j, x⁆ = 1 := by
      have : ⁅j, x⁆ ∈ ⁅Sj, Pi⁆ := Subgroup.commutator_mem_commutator hjSj hx
      rwa [h3, Subgroup.mem_bot] at this
    exact ((commutatorElement_eq_one_iff_commute.mp h4).eq).symm
  have hSB : S ≤ B := by
    rw [← hPiS]
    rintro _ ⟨x, hx, rfl⟩
    exact hcent x (hPiC hx)
  haveI := hB
  haveI : Group.IsSolvable ↥S := solvable_of_solvable_injective (Subgroup.inclusion_injective hSB)
  haveI : Group.IsPerfect ↥S := Subgroup.isPerfect_iff.mpr hS
  haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS1
  exact Group.IsPerfect.not_isSolvable ↥S inferInstance

theorem exists_perfect_cover_act_of_centralizer {P Q : Type*} [Group P] [Finite P] [Group Q]
    (ρ : P →* Q) {p : ℕ} [Fact p.Prime] {j : P} (hj : IsPGroup p (Subgroup.zpowers j))
    {S B : Subgroup Q} (hS : ⁅S, S⁆ = S) (hS1 : S ≠ ⊥)
    (hSj : S ≤ Subgroup.centralizer {ρ j}) (hSρ : S ≤ ρ.range) (hB : Group.IsSolvable B)
    (hcent : ∀ x ∈ Subgroup.centralizer {j}, ρ x ∈ B) :
    ∃ Pi SK : Subgroup P, Pi.map ρ = S ∧ ⁅Pi, Pi⁆ = Pi ∧
      Group.IsNilpotent ↥(ρ.comp Pi.subtype).ker ∧ IsPGroup p SK ∧ SK ≤ ρ.ker ∧
      Pi ≤ Subgroup.normalizer (SK : Set P) ∧ j ∈ Subgroup.normalizer (SK : Set P) ∧
      ∃ x ∈ Pi, ∃ s ∈ SK, x * s * x⁻¹ ≠ s := by
  obtain ⟨Pi, SK, hPiS, hPi, hnil, hSK, hPS, hjS, hact⟩ :=
    exists_perfect_cover_act_sylow_of_centralizer ρ hj hS hS1 hSj hSρ hB hcent
  exact ⟨Pi, SK, hPiS, hPi, hnil, hSK.isPGroup, hSK.le, hPS, hjS, hact⟩

theorem isPerfect_projSL_two_even {f : ℕ} (hf : 2 ≤ f) :
    Group.IsPerfect (projSL 2 (GaloisField 2 f)) := by
  haveI := isSimpleGroup_projSL hf
  refine TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative fun hc => ?_
  have hp := (Group.is_simple_iff_prime_card (α := projSL 2 (GaloisField 2 f))).mp inferInstance
  rw [card_projSL_two_even f (by omega)] at hp
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h16 : 16 ≤ (2 ^ f) ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left h4 2
  rcases Nat.prime_mul_iff.mp hp with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

theorem false_of_frattini_section_of_minDegree {G : Type} [Group G] [Finite G] {Q : Type*}
    [Group Q] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3) {P : Subgroup G} (ρ : P →* Q) {j : P}
    (hj : IsPGroup p (Subgroup.zpowers j)) {S B : Subgroup Q}
    (hSj : S ≤ Subgroup.centralizer {ρ j}) (hSρ : S ≤ ρ.range) (hB : Group.IsSolvable B)
    (hcent : ∀ x ∈ Subgroup.centralizer {j}, ρ x ∈ B) {f : ℕ} (hf : 3 ≤ f)
    (e : S ≃* projSL 2 (GaloisField 2 f))
    (hdeg : ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
      ∀ (N : Subgroup X) [N.Normal], Group.IsSolvable N →
        Nonempty (X ⧸ N ≃* projSL 2 (GaloisField 2 f)) →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
        (σ : X →* (V →ₗ[ZMod p] V)), (∃ x, σ x ≠ 1) → 7 ≤ Module.finrank (ZMod p) V) :
    False := by
  haveI := isPerfect_projSL_two_even (show 2 ≤ f by omega)
  haveI := isSimpleGroup_projSL (show 2 ≤ f by omega)
  have hSperf : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.mp
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
  have hS1 : S ≠ ⊥ := by
    haveI : Nontrivial ↥S := e.toEquiv.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot S).mp inferInstance
  obtain ⟨Pi, SK, hPiS, hPi, hnil, hSK, -, hPS, -, hact⟩ :=
    exists_perfect_cover_act_of_centralizer ρ hj hSperf hS1 hSj hSρ hB hcent
  haveI : Group.IsPerfect ↥Pi := Subgroup.isPerfect_iff.mpr hPi
  set σ : Pi →* Q := ρ.comp Pi.subtype with hσ
  have hrange : σ.range = S := by
    rw [hσ, MonoidHom.range_comp, Subgroup.range_subtype, hPiS]
  haveI : Group.IsNilpotent ↥σ.ker := hnil
  have hN : Group.IsSolvable ↥σ.ker := inferInstance
  let e' : ↥Pi ⧸ σ.ker ≃* projSL 2 (GaloisField 2 f) :=
    (QuotientGroup.quotientKerEquivRange σ).trans ((MulEquiv.subgroupCongr hrange).trans e)
  have hlocP : CFSG.Assembly.RankThreeEven.localRank p ↥P < 3 :=
    (CFSG.RankThree.PartTwo.localRank_subgroup_le (Fact.out : p.Prime) P).trans_lt hloc
  exact false_of_perfect_cover_act_of_minDegree hp2 hlocP hN hf e'
    (fun V _ _ _ τ hτ => hdeg ↥Pi inferInstance σ.ker hN ⟨e'⟩ V τ hτ) hSK hPS hact

theorem false_of_frattini_section
    {G : Type} [Group G] [Finite G] {Q : Type*} [Group Q] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3)
    {P : Subgroup G} (ρ : P →* Q) {j : P} (hj : IsPGroup p (Subgroup.zpowers j))
    {S B : Subgroup Q} (hSj : S ≤ Subgroup.centralizer {ρ j}) (hSρ : S ≤ ρ.range)
    (hB : Group.IsSolvable B) (hcent : ∀ x ∈ Subgroup.centralizer {j}, ρ x ∈ B) {f : ℕ}
    (hf : 6 ≤ f) (e : S ≃* projSL 2 (GaloisField 2 f)) : False :=
  false_of_frattini_section_of_minDegree (by omega) hloc ρ hj hSj hSρ hB hcent (by omega) e
    (l2EvenSolvableMinDegree_no3 f hf p hp5)

theorem false_of_frattini_section_four
    {G : Type} [Group G] [Finite G]
    {Q : Type*} [Group Q] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3) {P : Subgroup G} (ρ : P →* Q) {j : P}
    (hj : IsPGroup p (Subgroup.zpowers j)) {S B : Subgroup Q}
    (hSj : S ≤ Subgroup.centralizer {ρ j}) (hSρ : S ≤ ρ.range) (hB : Group.IsSolvable B)
    (hcent : ∀ x ∈ Subgroup.centralizer {j}, ρ x ∈ B) (e : S ≃* projSL 2 (GaloisField 2 4)) :
    False :=
  false_of_frattini_section_of_minDegree hp2 hloc ρ hj hSj hSρ hB hcent (by norm_num) e
    (l2EvenSolvableMinDegree_four p hp2)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
