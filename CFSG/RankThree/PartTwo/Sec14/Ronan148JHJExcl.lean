module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JInner
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JFix
public import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
public import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofTripleA6
public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofCover

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree.PartTwo

variable {Γ : Type} [Group Γ]

theorem le_normalizer_map_center {A Z : Subgroup Γ} [Finite Γ]
    (hAN : A ≤ Subgroup.normalizer (Z : Set Γ)) :
    A ≤ Subgroup.normalizer
      (((Subgroup.center ↥Z).map Z.subtype : Subgroup Γ) : Set Γ) := by
  intro a ha
  refine Item148HJ.mem_normalizer_of_conj_mem fun g hg => ?_
  obtain ⟨g', hg', rfl⟩ := hg
  have hgZ : a * (g' : Γ) * a⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hAN ha) g').mp g'.2
  refine ⟨⟨_, hgZ⟩, ?_, rfl⟩
  change _ ∈ Subgroup.center ↥Z
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  have hh : a⁻¹ * (h : Γ) * a ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp (hAN (A.inv_mem ha)) h).mp h.2
    simpa using this
  have hc := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hg') ⟨_, hh⟩)
  change a⁻¹ * (h : Γ) * a * (g' : Γ) = (g' : Γ) * (a⁻¹ * (h : Γ) * a) at hc
  change (h : Γ) * (a * (g' : Γ) * a⁻¹) = a * (g' : Γ) * a⁻¹ * (h : Γ)
  calc (h : Γ) * (a * (g' : Γ) * a⁻¹)
      = a * (a⁻¹ * (h : Γ) * a * (g' : Γ)) * a⁻¹ := by group
    _ = a * ((g' : Γ) * (a⁻¹ * (h : Γ) * a)) * a⁻¹ := by rw [hc]
    _ = a * (g' : Γ) * a⁻¹ * (h : Γ) := by group

theorem zpowers_eq_of_card_three {C : Subgroup Γ} [Finite C] (hC3 : Nat.card C = 3) {c : Γ}
    (hcC : c ∈ C) (hc1 : c ≠ 1) : Subgroup.zpowers c = C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Subgroup.zpowers c ≤ C := Subgroup.zpowers_le.mpr hcC
  have hc3 : c ^ 3 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard C hcC
    rw [hC3] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hC3, Nat.card_zpowers, hord]

theorem forall_commute_of_three_dvd_card_center [Finite Γ] {Aq C E Z : Subgroup Γ}
    (hAp : IsPGroup 3 Aq)
    (hF3 : ∀ w : Γ, w ∈ Subgroup.centralizer (Aq : Set Γ) → w ^ 3 = 1 → w ∈ Aq)
    (hC3 : Nat.card C = 3) (hAeq : C ⊔ E = Aq)
    (hEZ : E ≤ Subgroup.centralizer (Z : Set Γ)) (hAZ : Aq ⊓ Z ≤ C)
    (hAN : Aq ≤ Subgroup.normalizer (Z : Set Γ)) (h3 : 3 ∣ Nat.card (Subgroup.center ↥Z)) :
    ∀ x ∈ Z, x ^ 3 = 1 → ∀ y ∈ Z, x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ZZ : Subgroup Γ := (Subgroup.center ↥Z).map Z.subtype with hZZ
  have hZZ3 : 3 ∣ Nat.card ZZ := by
    rwa [hZZ, Subgroup.card_map_of_injective Z.subtype_injective]
  have hZZc : ∀ k ∈ ZZ, ∀ y ∈ Z, k * y = y * k := by
    rintro _ ⟨k, hk, rfl⟩ y hy
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hk) ⟨y, hy⟩)).symm
  have hZZZ : ZZ ≤ Z := Subgroup.map_subtype_le _
  obtain ⟨k, hkZZ, hk1, hk3, hkA⟩ :=
    exists_pow_eq_one_mem_centralizer hAp (le_normalizer_map_center hAN) hZZ3
  have hkAq : k ∈ Aq := hF3 k hkA hk3
  have hkC : k ∈ C := hAZ ⟨hkAq, hZZZ hkZZ⟩
  have hCk : Subgroup.zpowers k = C := zpowers_eq_of_card_three hC3 hkC hk1
  have hCZZ : C ≤ ZZ := hCk ▸ Subgroup.zpowers_le.mpr hkZZ
  have hAZc : Aq ≤ Subgroup.centralizer (Z : Set Γ) := by
    rw [← hAeq]
    refine sup_le (fun c hc => ?_) hEZ
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hZZc c (hCZZ hc) y hy).symm
  intro x hx hx3 y hy
  have hxA : x ∈ Subgroup.centralizer (Aq : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hAZc ha) x hx).symm
  have hxC : x ∈ C := hAZ ⟨hF3 x hxA hx3, hx⟩
  exact hZZc x (hCZZ hxC) y hy

theorem false_of_isTripleCover_of_le [Finite Γ] {Aq C E Z : Subgroup Γ}
    (hAp : IsPGroup 3 Aq)
    (hF3 : ∀ w : Γ, w ∈ Subgroup.centralizer (Aq : Set Γ) → w ^ 3 = 1 → w ∈ Aq)
    (hC3 : Nat.card C = 3) (hAeq : C ⊔ E = Aq)
    (hEZ : E ≤ Subgroup.centralizer (Z : Set Γ)) (hAZ : Aq ⊓ Z ≤ C)
    (hAN : Aq ≤ Subgroup.normalizer (Z : Set Γ))
    (hZ6 : Sec4.IsTripleCover ↥Z (alternatingGroup (Fin 6))) : False := by
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥Z) := by rw [hZ6.1]
  have key := forall_commute_of_three_dvd_card_center hAp hF3 hC3 hAeq hEZ hAZ hAN h3
  obtain ⟨x, hx3, hxZ⟩ := Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 hZ6
  apply hxZ
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hx3' : (x : Γ) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
  exact (key x x.2 hx3' y y.2).symm

theorem exists_commute_of_j2
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {c : X} (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) : ∃ y : X, y ^ 3 = 1 ∧ y * c = c * y ∧ y ∉ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcp : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1, pow_one])
  obtain ⟨P, hcP⟩ := hcp.exists_le_sylow
  have hcP' : c ∈ (P : Subgroup X) := hcP (Subgroup.mem_zpowers c)
  obtain ⟨⟨hHeis, -⟩, -⟩ := Sec4.Sporadic.rank3II_4_15 X hX P _ rfl _ rfl
  obtain ⟨⟨-, -, -, hZ3⟩, hP27, hexp⟩ := hHeis
  have hP3 : ∀ g : ↥(P : Subgroup X), g ^ 3 = 1 := fun g => by
    have := Monoid.pow_exponent_eq_one g
    rwa [hexp] at this
  have hpow : ∀ g ∈ (P : Subgroup X), g ^ 3 = 1 := fun g hg => by
    simpa using congrArg Subtype.val (hP3 ⟨g, hg⟩)
  have hcard : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  set c' : ↥(P : Subgroup X) := ⟨c, hcP'⟩ with hc'
  by_cases hcZ : c' ∈ Subgroup.center ↥(P : Subgroup X)
  ·
    have hnot : ¬ (P : Subgroup X) ≤ Subgroup.zpowers c := by
      intro hle
      have := Subgroup.card_le_of_le hle
      rw [hP27, hcard] at this
      omega
    obtain ⟨y, hyP, hyc⟩ := Set.not_subset.mp hnot
    refine ⟨y, hpow y hyP, ?_, hyc⟩
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hcZ) ⟨y, hyP⟩)
  ·
    have hZne : Subgroup.center ↥(P : Subgroup X) ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hZ3
      omega
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
    refine ⟨(y : ↥(P : Subgroup X)), hpow _ y.1.2, ?_, fun hyc => ?_⟩
    · exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp y.2) c')).symm
    ·
      apply hcZ
      have hy1' : ((y : ↥(P : Subgroup X)) : X) ≠ 1 := fun h =>
        hy1 (Subtype.ext (Subtype.ext h))
      have hyy : Subgroup.zpowers ((y : ↥(P : Subgroup X)) : X) = Subgroup.zpowers c :=
        zpowers_eq_of_card_three hcard hyc hy1'
      have hcy : c ∈ Subgroup.zpowers ((y : ↥(P : Subgroup X)) : X) :=
        hyy ▸ Subgroup.mem_zpowers c
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcy
      have hk' : (y : ↥(P : Subgroup X)) ^ k = c' := Subtype.ext (by simpa using hk)
      rw [← hk']
      exact Subgroup.zpow_mem _ y.2 k

theorem false_of_j2_of_le
    [Finite Γ]
    {Aq C Z : Subgroup Γ} (hAab : ∀ x ∈ Aq, ∀ y ∈ Aq, x * y = y * x)
    (hA3 : ∀ a ∈ Aq, a ^ 3 = 1)
    (hF3 : ∀ w : Γ, w ∈ Subgroup.centralizer (Aq : Set Γ) → w ^ 3 = 1 → w ∈ Aq)
    (hC3 : Nat.card C = 3) (hAZ : Aq ⊓ Z ≤ C) (hAN : Aq ≤ Subgroup.normalizer (Z : Set Γ))
    (ψ : ↥Z ≃* CFSG.Blueprint.NativeSporadic.J2) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZc : Subgroup.center ↥Z = ⊥ := KFacts.KS14.Native.center_eq_bot_of_j2 ⟨ψ⟩
  have hZZ : Z ⊓ Subgroup.centralizer (Z : Set Γ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hz : (⟨x, hx.1⟩ : ↥Z) ∈ Subgroup.center ↥Z := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hZc, Subgroup.mem_bot] at hz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz
  have hsup := sup_eq_of_forall_inner hAab hA3 hF3 hZZ hAN
    (fun a ha => exists_inner_of_j2 ψ (hAN ha) (hA3 a ha))
  have hcardZ : Nat.card ↥Z = 604800 := KFacts.KS14.card_eq_of_j2 ⟨ψ⟩
  by_cases h0 : Aq ⊓ Z = ⊥
  ·
    rw [h0, sup_bot_eq] at hsup
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hcardZ]; norm_num)
    have hyA : (y : Γ) ∈ Subgroup.centralizer (Aq : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have ha' : a ∈ Aq ⊓ Subgroup.centralizer (Z : Set Γ) := by rw [hsup]; exact ha
      exact (Subgroup.mem_centralizer_iff.mp ha'.2 y y.2).symm
    have hy3 : (y : Γ) ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy] at this
      simpa using congrArg Subtype.val this
    have hy0 : (y : Γ) ∈ Aq ⊓ Z := ⟨hF3 _ hyA hy3, y.2⟩
    rw [h0, Subgroup.mem_bot] at hy0
    have : y = 1 := Subtype.ext hy0
    rw [this, orderOf_one] at hy
    omega
  · obtain ⟨c0, hc01⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h0
    have hc0C : (c0 : Γ) ∈ C := hAZ c0.2
    have hc01' : (c0 : Γ) ≠ 1 := fun h => hc01 (Subtype.ext h)
    have hCc : Subgroup.zpowers (c0 : Γ) = C := zpowers_eq_of_card_three hC3 hc0C hc01'
    set c' : ↥Z := ⟨c0, c0.2.2⟩ with hc'
    have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa [hc'] using hA3 _ c0.2.1)
    have hc'1 : c' ≠ 1 := fun h => hc01' (by simpa [hc'] using congrArg Subtype.val h)
    obtain ⟨y, hy3, hyc, hyn⟩ := exists_commute_of_j2 ⟨ψ⟩ hc'3 hc'1
    have hyA : (y : Γ) ∈ Subgroup.centralizer (Aq : Set Γ) := by
      have hle : Aq ≤ Subgroup.centralizer ({(y : Γ)} : Set Γ) := by
        rw [← hsup]
        refine sup_le (fun a ha => ?_) (fun a ha => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp ha.2 y y.2).symm
        · have haC : a ∈ Subgroup.zpowers (c0 : Γ) := hCc ▸ hAZ ha
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp haC
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hyc' : (y : Γ) * c0 = c0 * y := by simpa [hc'] using congrArg Subtype.val hyc
          exact (Commute.zpow_right hyc' k).eq.symm
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha))
    have hy3' : (y : Γ) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
    have hyC : (y : Γ) ∈ Subgroup.zpowers (c0 : Γ) := hCc ▸ hAZ ⟨hF3 _ hyA hy3', y.2⟩
    apply hyn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyC
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa [hc'] using hk)⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
