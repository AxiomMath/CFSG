module

public import CFSG.RankThree.PartTwo.Sec21.Item222ProofMono
public import CFSG.RankThree.PartTwo.Sec21.Item222ProofStar
import CFSG.RankThree.PartTwo.Sec13.Item13GL
import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec21.Item22Refl

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item222Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14 (monomial)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint
open Matrix

variable {G : Type} [Group G]

theorem card_fixedSubgroupOf_eq_nine [Finite G] {A : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 3 ^ 3) {φ : MulAut A}
    (hφ : IsReflectionOn φ) : Nat.card (fixedSubgroupOf φ) = 9 := by
  have h := card_eq_three_mul_card_fixed hAe.1.is_comm.comm hφ
  rw [h27] at h
  omega

theorem exists_mem_eq_inf_centralizer_zpowers [Finite G] {A L : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 3 ^ 3) {c : G} (hcA : c ∈ A)
    (hc1 : c ≠ 1) (hLC : L ≤ Subgroup.centralizer ({c} : Set G)) {C : Subgroup A}
    (hC9 : Nat.card C = 9) (hcC : (⟨c, hcA⟩ : A) ∉ C) (hCL : C ≤ L.comap A.subtype)
    {φ : MulAut A} (hφL : φ ∈ starOf A L) (hφ : IsReflectionOn φ) :
    ∃ d ∈ L, Nat.card (Subgroup.zpowers d) = 3 ∧
      L ⊓ Subgroup.centralizer (fixedInG A φ : Set G) =
        L ⊓ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  set c' : A := ⟨c, hcA⟩ with hc'
  have hc'1 : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hB9 := card_fixedSubgroupOf_eq_nine hAe h27 hφ
  obtain ⟨d, hd, hd1⟩ := exists_ne_one_mem_inf (by rw [h27]; norm_num) hB9 hC9
  have hdc : d ∉ Subgroup.zpowers c' := by
    intro h
    rcases Sec13.eq_of_mem_zpowers_of_pow_three (hA3 c') h with h | h | h
    · exact hd1 h
    · exact hcC (h ▸ hd.2)
    · apply hcC
      have e : c' = d * d := by
        calc c' = c' ^ 3 * c' := by rw [hA3, one_mul]
          _ = c' ^ 2 * c' ^ 2 := by group
          _ = d * d := by rw [h]
      rw [e]
      exact C.mul_mem hd.2 hd.2
  have hc'B : c' ∈ fixedSubgroupOf φ := Item2131One.apply_eq_of_mem_starOf hcA hLC hφL
  have hBeq := eq_sup_zpowers hA3 hB9 hc'B hd.1 hc'1 hdc
  refine ⟨(d : G), hCL hd.2, ?_, ?_⟩
  · rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hAe.2 d d.2) fun h => hd1 (Subtype.ext h)
  · rw [centralizer_zpowers_eq]
    exact inf_centralizer_eq hBeq hLC

theorem exists_mem_eq_inf_centralizer_singleton [Finite G] {A L : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 3 ^ 3) {c : G} (hcA : c ∈ A)
    (hc1 : c ≠ 1) (hLC : L ≤ Subgroup.centralizer ({c} : Set G)) {u : MulAut A}
    (hu : u ∈ starOf A L) (hufix : ∀ a : A, u a = a → a ∈ Subgroup.zpowers (⟨c, hcA⟩ : A))
    {φ : MulAut A} (hφL : φ ∈ starOf A L) (hφ : IsReflectionOn φ) :
    ∃ b ∈ A, (∃ x ∈ L, x * b ≠ b * x) ∧
      Even (Nat.card (L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G)) ∧
      L ⊓ Subgroup.centralizer (fixedInG A φ : Set G) =
        L ⊓ Subgroup.centralizer ({b} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  set c' : A := ⟨c, hcA⟩ with hc'
  have hc'1 : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  set B := fixedSubgroupOf φ with hBdef
  have hB9 : Nat.card B = 9 := card_fixedSubgroupOf_eq_nine hAe h27 hφ
  obtain ⟨b, hbB, x, hxL, hxb⟩ : ∃ b ∈ B, ∃ x ∈ L, x * (b : G) ≠ (b : G) * x := by
    by_contra h
    push Not at h
    obtain ⟨t₀, ht₀, rfl⟩ := hu
    have ht₀L : (t₀ : G) ∈ L := Subgroup.mem_subgroupOf.mp ht₀
    have hBle : B ≤ Subgroup.zpowers c' := by
      intro a ha
      refine hufix a (Subtype.ext ?_)
      change (t₀ : G) * a * (t₀ : G)⁻¹ = a
      rw [h a ha t₀ ht₀L, mul_inv_cancel_right]
    have h3 : Nat.card B ≤ 3 := by
      calc Nat.card B ≤ Nat.card (Subgroup.zpowers c') := Subgroup.card_le_of_le hBle
        _ = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime (hA3 c') hc'1]
    omega
  have hbc : b ∉ Subgroup.zpowers c' := by
    intro h
    apply hxb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    have hcx : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp (hLC hxL)
    rw [Subgroup.coe_zpow]
    exact (Commute.zpow_right hcx k).eq
  have hc'B : c' ∈ B := Item2131One.apply_eq_of_mem_starOf hcA hLC hφL
  have hBeq := eq_sup_zpowers hA3 hB9 hc'B hbB hc'1 hbc
  refine ⟨(b : G), b.2, ⟨x, hxL, hxb⟩, ?_, inf_centralizer_eq hBeq hLC⟩
  obtain ⟨t, htL, htφ⟩ := hφL
  have htL' : (t : G) ∈ L := Subgroup.mem_subgroupOf.mp htL
  have htb : (t : G) ∈ Subgroup.centralizer ({(b : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : ((φ b : A) : G) = (t : G) * b * (t : G)⁻¹ := by
      rw [← htφ]
      rfl
    have h2 : φ b = b := hbB
    rw [h2] at h1
    calc (t : G) * b = ((t : G) * b * (t : G)⁻¹) * t := by group
      _ = b * t := by rw [← h1]
  have h2 : 2 ∣ orderOf (t : G) := by
    rw [Subgroup.orderOf_coe, ← hφ.1, ← htφ]
    exact orderOf_map_dvd _ t
  have hdvd : orderOf (t : G) ∣ Nat.card (L ⊓ Subgroup.centralizer ({(b : G)} : Set G) :
      Subgroup G) := by
    rw [← Subgroup.orderOf_mk (t : G) (Subgroup.mem_inf.mpr ⟨htL', htb⟩)]
    exact orderOf_dvd_natCard _
  exact even_iff_two_dvd.mpr (h2.trans hdvd)

theorem quaternion_facts :
    QuaternionGroup.a (1 : ZMod (2 * 2)) * QuaternionGroup.a 1 ≠ 1 ∧
      QuaternionGroup.a (1 : ZMod (2 * 2)) * QuaternionGroup.a 1 * QuaternionGroup.a 1 *
        QuaternionGroup.a 1 = 1 ∧
      QuaternionGroup.xa (0 : ZMod (2 * 2)) * QuaternionGroup.xa 0 ≠ 1 ∧
      QuaternionGroup.xa (0 : ZMod (2 * 2)) * QuaternionGroup.xa 0 * QuaternionGroup.xa 0 *
        QuaternionGroup.xa 0 = 1 ∧
      QuaternionGroup.a (1 : ZMod (2 * 2)) * QuaternionGroup.xa 0 ≠
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  decide

@[expose] def StarS3Info (A : Subgroup G) [Finite G] (L : Subgroup G) : Prop :=
  Nonempty (lBar L ≃* NativeSporadic.J2) ∨
    ∃ n : ℕ, 0 < n ∧ Even n ∧
      ((Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n)) ∧ Sec4.IsTypeCOn A L) ∨
        (Nonempty (lBar L ≃* SL3 n) ∧ IsTypeCOnBarSL A L))

@[expose] def StarD8Info (L : Subgroup G) : Prop :=
  ((∃ n : ℕ, 0 < n ∧ Even n ∧
      (Nonempty (lBar L ≃* projSp 2 (GaloisField 2 n)) ∨ Nonempty (lBar L ≃* projSU 4 2 n))) ∨
    Nonempty (lBar L ≃* projSU 5 2 2)) ∨
  StatedClassicalModel (lBar L) .PSL 4 2 1 ∨ StatedClassicalModel (lBar L) .PSL 5 2 1

theorem star_three_cases [Finite G] (h211 : Item211) (h2131 : Item2131One) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) (hcA : c ∈ A) (h27 : Nat.card A = 3 ^ 3) :
    ∃ σ₁ ∈ starOf A L, ∃ σ₂ ∈ starOf A L, σ₁ * σ₁ = 1 ∧ σ₂ * σ₂ = 1 ∧ IsReflectionOn σ₁ ∧
      IsReflectionOn σ₂ ∧ starOf A L = Subgroup.closure {σ₁, σ₂} ∧
      ((Nonempty (starOf A L ≃* Equiv.Perm (Fin 3)) ∧
          (∀ a : A, (σ₁ * σ₂) a = a → a ∈ Subgroup.zpowers (⟨c, hcA⟩ : A)) ∧
          (⟨c, hcA⟩ : A) ∈ commOf σ₁ ⊔ commOf σ₂ ∧ StarS3Info A L) ∨
        (Nonempty (starOf A L ≃* DihedralGroup 4) ∧ Nat.card (commOf (σ₁ * σ₂)) = 9 ∧
          (⟨c, hcA⟩ : A) ∉ commOf (σ₁ * σ₂) ∧ StarD8Info L)) := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : IsMulCommutative A := hAe.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  obtain ⟨f, hWf, -⟩ := h2131 G A E U c L hpair h27
  set c' : A := ⟨c, hcA⟩ with hc'
  set v := Multiplicative.toAdd (f.symm c') with hvdef
  have hfv : f (Multiplicative.ofAdd v) = c' := by
    rw [hvdef, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hv : v ≠ 0 := by
    intro h
    apply hc1
    have h1 : c' = 1 := by rw [← hfv, h, ofAdd_zero, map_one]
    exact congrArg Subtype.val h1
  have hS : ∀ σ ∈ starOf A L, coordGL f σ ∈ monomial ∧ Item2131One.matOf f σ *ᵥ v = v := by
    intro σ hσ
    refine ⟨hWf ⟨σ, starOf_le_wStar A L hσ, rfl⟩, ?_⟩
    apply coord_injective f
    rw [← apply_coord, hfv]
    exact Item2131One.apply_eq_of_mem_starOf hcA hLC hσ
  have hle8 := card_le_eight f hv hS
  have hcard : ∀ {X : Type} [Group X], Nonempty (starOf A L ≃* X) → Nat.card X ≤ 8 := by
    rintro X _ ⟨e⟩
    rw [← Nat.card_congr e.toEquiv]
    exact hle8
  have key : (Nonempty (starOf A L ≃* Equiv.Perm (Fin 3)) ∧ StarS3Info A L) ∨
      (Nonempty (starOf A L ≃* DihedralGroup 4) ∧ StarD8Info L) := by
    rcases h211 G A E U c L hpair with ⟨-, -, -, -, h9⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨-, -, he⟩ |
        ⟨-, -, he | he⟩ | ⟨hJ, -, he⟩ | ⟨-, -, he⟩ | ⟨hn, -, he⟩ | ⟨-, -, he⟩ | ⟨h9, -, he⟩ |
        ⟨-, h81, -⟩ | ⟨-, h81, -⟩ | ⟨h12, -, he⟩ | ⟨-, h81, -⟩
    · omega
    ·
      exfalso
      obtain ⟨q1, q2, q3, q4, q5⟩ := quaternion_facts
      set ι : QuaternionGroup 2 →* MulAut A := (starOf A L).subtype.comp e.symm.toMonoidHom
      have hinj : Function.Injective ι := (starOf A L).subtype_injective.comp e.symm.injective
      have hmem : ∀ x, ι x ∈ starOf A L := fun x => (e.symm x).2
      have hne1 : ∀ {x : QuaternionGroup 2}, x * x ≠ 1 → ι x * ι x ≠ 1 := fun h h' =>
        h (hinj (by rw [map_mul, h', map_one]))
      have h41 : ∀ {x : QuaternionGroup 2}, x * x * x * x = 1 → ι x * ι x * ι x * ι x = 1 :=
        fun h => by rw [← map_mul, ← map_mul, ← map_mul, h, map_one]
      exact q5 (hinj (by
        rw [map_mul, map_mul]
        exact commute_of_orderOf_four f hv (hS _ (hmem _)) (hS _ (hmem _)) (hne1 q1) (h41 q2)
          (hne1 q3) (h41 q4)))
    · exact absurd (hcard he) (by rw [Item2131One.card_semidihedral_four]; norm_num)
    · exact absurd (hcard he) (by rw [DihedralGroup.nat_card]; norm_num)
    · exact absurd (hcard he) (by rw [Item2131One.card_GL_two_three]; norm_num)
    · exact Or.inl ⟨he, Or.inl hJ⟩
    · exact absurd (hcard he) (by rw [Item2131One.card_GL_two_three]; norm_num)
    · exact Or.inl ⟨he, Or.inr hn⟩
    · exact absurd (hcard he) (by rw [DihedralGroup.nat_card]; norm_num)
    · exact Or.inr ⟨he, Or.inl h9⟩
    · rw [h27] at h81
      norm_num at h81
    · rw [h27] at h81
      norm_num at h81
    · exact Or.inr ⟨he, Or.inr h12⟩
    · rw [h27] at h81
      norm_num at h81
  rcases key with ⟨⟨e⟩, hinfo⟩ | ⟨⟨e⟩, hinfo⟩
  ·
    obtain ⟨σ₁, h₁, σ₂, h₂, h11, h22, hne, h3, h31, hcl⟩ := exists_generators_perm_three e
    refine ⟨σ₁, h₁, σ₂, h₂, h11, h22,
      isReflectionOn_of_not_commute f hAc hv (hS σ₁ h₁) (hS σ₂ h₂) h11 h22 hne,
      isReflectionOn_of_not_commute f hAc hv (hS σ₂ h₂) (hS σ₁ h₁) h22 h11 (Ne.symm hne), hcl,
      Or.inl ⟨⟨e⟩, fun a ha => ?_, ?_, hinfo⟩⟩
    · rw [← hfv]
      exact mem_zpowers_of_fixed f hv (hS _ ((starOf A L).mul_mem h₁ h₂)) h3 h31 ha
    · rw [← hfv]
      exact mem_sup_commOf f hv (hS σ₁ h₁) (hS σ₂ h₂) h11 h22 hne h3
  ·
    obtain ⟨σ₁, h₁, σ₂, h₂, h11, h22, hne, h2, h4, hcl⟩ := exists_generators_dihedral e
    obtain ⟨hc9, hcC⟩ := card_commOf_of_orderOf_four f hAc hv
      (hS _ ((starOf A L).mul_mem h₁ h₂)) h2 h4
    refine ⟨σ₁, h₁, σ₂, h₂, h11, h22,
      isReflectionOn_of_not_commute f hAc hv (hS σ₁ h₁) (hS σ₂ h₂) h11 h22 hne,
      isReflectionOn_of_not_commute f hAc hv (hS σ₂ h₂) (hS σ₁ h₁) h22 h11 (Ne.symm hne), hcl,
      Or.inr ⟨⟨e⟩, hc9, ?_, hinfo⟩⟩
    rw [← hfv]
    exact hcC

end CFSG.RankThree.PartTwo.Sec21.Item222Proof
