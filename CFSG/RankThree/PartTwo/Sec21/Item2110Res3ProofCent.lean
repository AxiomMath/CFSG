module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofData
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofRank

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def Item2110ALInI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      A ⊓ L ≤ iOf218 L d

namespace Item2110Res3Proof

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem inSubgroup_theta_inf_le {I J : Subgroup G} (hIJ : I ≤ J) :
    inSubgroup (aschbacherSolvableCore 3) J ⊓ I ≤ inSubgroup (aschbacherSolvableCore 3) I := by
  set T := inSubgroup (aschbacherSolvableCore 3) J with hT
  set N := T ⊓ I with hN
  have hJT : J ≤ normalizer (T : Set G) := Sec6.le_normalizer_theta J
  obtain ⟨hTsol, -, hT3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three
  obtain ⟨-, -, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥I) Nat.prime_three
  have hNI : N ≤ I := inf_le_right
  have hNT : N ≤ T := inf_le_left
  have hle : N.subgroupOf I ≤ aschbacherSolvableCore 3 ↥I := by
    refine hmax _ ⟨fun n hn g => ?_⟩ ?_ ?_
    · rw [mem_subgroupOf] at hn ⊢
      simp only [coe_mul, coe_inv]
      exact Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp (hJT (hIJ g.2)) _).mp hn.1,
        I.mul_mem (I.mul_mem g.2 hn.2) (I.inv_mem g.2)⟩
    · have e₁ : ↥(N.subgroupOf I) ≃* ↥N := subgroupOfEquivOfLe hNI
      have e₂ : ↥T ≃* ↥(aschbacherSolvableCore 3 ↥J) :=
        ((aschbacherSolvableCore 3 ↥J).equivMapOfInjective J.subtype J.subtype_injective).symm
      have : Group.IsSolvable ↥T := Group.isSolvable_of_isSolvable_injective
        (f := e₂.toMonoidHom) e₂.injective
      have : Group.IsSolvable ↥N := Group.isSolvable_of_isSolvable_injective
        (f := inclusion hNT) (inclusion_injective hNT)
      exact Group.isSolvable_of_isSolvable_injective (f := e₁.toMonoidHom) e₁.injective
    · intro h3
      apply hT3
      have h1 : Nat.card ↥(N.subgroupOf I) = Nat.card ↥N :=
        Nat.card_congr (subgroupOfEquivOfLe hNI).toEquiv
      have h2 : Nat.card ↥N ∣ Nat.card ↥T := card_dvd_of_le hNT
      have h3' : Nat.card ↥T = Nat.card ↥(aschbacherSolvableCore 3 ↥J) :=
        card_map_of_injective J.subtype_injective
      rw [h1] at h3
      exact h3.trans (h3' ▸ h2)
  intro x hx
  exact ⟨⟨x, hx.2⟩, hle (mem_subgroupOf.mpr hx), rfl⟩

theorem mem_zpowers_of_acts_trivially {A I J : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hIJ : I ≤ J) {a d : G} (haA : a ∈ A)
    (haI : a ∈ I) (hdA : d ∈ A) (hdI : d ∈ I) (hdc : ∀ x ∈ I, x * d = d * x) (hd1 : d ≠ 1)
    (haJ : ∀ l ∈ J, l⁻¹ * (a * l * a⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) J)
    (hZ : ∀ H : Subgroup (lBar I), H ≤ center (lBar I) → Nat.card H ≤ 3) : a ∈ zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥I with hθ
  set π := QuotientGroup.mk' θ with hπ
  set a₀ : I := ⟨a, haI⟩
  set d₀ : I := ⟨d, hdI⟩
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have haZ : π a₀ ∈ center (lBar I) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ g
    have hx : (x : G)⁻¹ * (a * x * a⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) I :=
      inSubgroup_theta_inf_le hIJ (Subgroup.mem_inf.mpr ⟨haJ x (hIJ x.2), I.mul_mem
        (I.inv_mem x.2) (I.mul_mem (I.mul_mem haI x.2) (I.inv_mem haI))⟩)
    obtain ⟨y, hy, hyx⟩ := hx
    have hy' : x⁻¹ * (a₀ * x * a₀⁻¹) ∈ θ := by
      have : y = x⁻¹ * (a₀ * x * a₀⁻¹) := Subtype.ext hyx
      rwa [← this]
    have h1 : π x = π (a₀ * x * a₀⁻¹) := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      exact hy'
    have h2 := congrArg (· * π a₀) h1
    simp only [map_mul, map_inv, inv_mul_cancel_right] at h2
    exact h2
  have hd₀Z : d₀ ∈ center I := mem_center_iff.mpr fun g => Subtype.ext (hdc g g.2)
  have hdZ : π d₀ ∈ center (lBar I) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hd₀Z x]
  set P : Subgroup I := A.subgroupOf I with hP
  have hP3 : IsPGroup 3 P := fun x => ⟨1, by
    have hx : ((x : I) : G) ^ 3 = 1 := hAe.2 _ (mem_subgroupOf.mp x.2)
    apply Subtype.ext
    apply Subtype.ext
    simpa using hx⟩
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hP3
  have hd₀P : d₀ ∈ P := mem_subgroupOf.mpr hdA
  have hd₀1 : π d₀ ≠ 1 := by
    intro h
    have h' : π d₀ = π 1 := by rw [h, map_one]
    have := hinj hd₀P (one_mem P) h'
    exact hd1 (congrArg Subtype.val this)
  have hd₀3 : π d₀ ^ 3 = 1 := by
    rw [← map_pow]
    have : d₀ ^ 3 = 1 := Subtype.ext hd3
    rw [this, map_one]
  set H := closure ({π a₀, π d₀} : Set (lBar I)) with hH
  have hHZ : H ≤ center (lBar I) := by
    rw [hH, closure_le]
    rintro x (rfl | rfl)
    · exact haZ
    · exact hdZ
  have hdH : zpowers (π d₀) ≤ H := zpowers_le.mpr (subset_closure (Set.mem_insert_of_mem _ rfl))
  have hcard : Nat.card (zpowers (π d₀)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd₀3 hd₀1]
  have hHeq : zpowers (π d₀) = H :=
    eq_of_le_of_card_ge hdH (by rw [hcard]; exact hZ H hHZ)
  have haH : π a₀ ∈ zpowers (π d₀) := hHeq ▸ subset_closure (Set.mem_insert _ _)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp haH
  have hk' : π (d₀ ^ k) = π a₀ := by rw [map_zpow, hk]
  have heq : d₀ ^ k = a₀ := hinj (zpow_mem hd₀P k) (mem_subgroupOf.mpr haA) hk'
  have : d ^ k = a := congrArg Subtype.val heq
  exact this ▸ zpow_mem (mem_zpowers d) k

section Cent


theorem item2110CentAJ_of (h211 : Item211) (h45 : Sec4.Item4_5) (h219 : Item219)
    (hAL : Item2110ALInI) : Item2110CentAJ := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen J hJ hJI
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcA, hc1, hLc, -, hcL⟩ := Item2113Res2Proof.pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have h27 : Nat.card A = 27 := by
    rw [Item2113Proof.card_eq_of_isList218 h211 hpair hL]; norm_num
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    Item2113Res3Proof.card_inf_eq_nine h211 h45 hpair hL
  obtain ⟨hdI, hcases⟩ := h219 G A E U c L hpair hL d hdA hd1 hdcen
  have hdL : d ∈ L := Item2113Proof.mem_of_isCentral218 hdcen
  have hALI : A ⊓ L ≤ iOf218 L d := hAL G A E U c L hpair hL d hdA hd1 hdcen
  have hIJ : iOf218 L d ≤ J := by
    rw [hJI]
    exact le_sup_left
  have hIL : iOf218 L d ≤ L := (map_subtype_le _).trans inf_le_left
  have hIC : iOf218 L d ≤ centralizer ({d} : Set G) := (map_subtype_le _).trans inf_le_right
  have hdc : ∀ x ∈ iOf218 L d, x * d = d * x := fun x hx =>
    mem_centralizer_singleton_iff.mp (hIC hx)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hAN : A ≤ normalizer (J : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hdA hd1
      J hJ
  have hcJ : c ∈ Sec4.thetaQuotCentralizer J :=
    Item2110Res2Proof.mem_thetaQuotCentralizer_of_eq_sup (hAN hcA)
      (fun x hx => mem_centralizer_singleton_iff.mp (hLc (hIL hx))) hJI
  have hJd : J ≤ centralizer ({d} : Set G) := Sec6.le_centralizer_of_mem_thetaComponentsAt hJ
  have hdJ : d ∈ Sec4.thetaQuotCentralizer J := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAN hdA, fun l hl => ?_⟩
    have : d * l * d⁻¹ = l := by
      rw [← mem_centralizer_singleton_iff.mp (hJd hl), mul_inv_cancel_right]
    rw [this, inv_mul_cancel]
    exact one_mem _
  have hcd : c ∉ zpowers d := fun h => hcL ((zpowers_le.mpr hdL) h)
  have hcard3 : Nat.card (zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hAcL : zpowers c ⊔ (A ⊓ L) = A := by
    have hle : zpowers c ⊔ (A ⊓ L) ≤ A := sup_le (zpowers_le.mpr hcA) inf_le_left
    have hlt : A ⊓ L < zpowers c ⊔ (A ⊓ L) := by
      refine lt_of_le_of_ne le_sup_right fun h => hcL ?_
      have hc' : c ∈ zpowers c ⊔ (A ⊓ L) := mem_sup_left (mem_zpowers c)
      rw [← h] at hc'
      exact hc'.2
    have hdvd : Nat.card (zpowers c ⊔ (A ⊓ L) : Subgroup G) ∣ 3 ^ 3 := by
      rw [← h27.trans (by norm_num : (27 : ℕ) = 3 ^ 3)]
      exact card_dvd_of_le hle
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hgt : 9 < Nat.card (zpowers c ⊔ (A ⊓ L) : Subgroup G) := by
      rw [← h9]
      exact card_lt_of_lt hlt
    have hj3 : j = 3 := by
      rcases j with _ | _ | _ | _ | j
      · rw [hjc] at hgt; norm_num at hgt
      · rw [hjc] at hgt; norm_num at hgt
      · rw [hjc] at hgt; norm_num at hgt
      · rfl
      · omega
    exact eq_of_le_of_card_ge hle (by rw [hjc, hj3, h27]; norm_num)
  obtain ⟨a, haAL, had⟩ : ∃ a ∈ A ⊓ L, a ∉ zpowers d := by
    by_contra hcon
    have hle : A ⊓ L ≤ zpowers d := fun x hx => by
      by_contra hx'
      exact hcon ⟨x, hx, hx'⟩
    have := card_le_of_le hle
    rw [h9, hcard3] at this
    norm_num at this
  have hcl := lBar_cases hdI hdc hd3 hd1 hcases
  have hZ : ∀ H : Subgroup (lBar (iOf218 L d)), H ≤ center (lBar (iOf218 L d)) →
      Nat.card H ≤ 3 := fun H hH => card_le_three_of_le_center hcl hH
  have haC : a ∉ Sec4.thetaQuotCentralizer J := by
    intro haC
    have haJ := (Sec6.mem_thetaQuotCentralizer_iff.mp haC).2
    exact had (mem_zpowers_of_acts_trivially hAe hIJ haAL.1 (hALI haAL) hdA hdI hdc hd1 haJ hZ)
  set B := A ⊓ Sec4.thetaQuotCentralizer J with hB
  have hdB : zpowers d ≤ B := zpowers_le.mpr ⟨hdA, hdJ⟩
  have hcB : c ∈ B := ⟨hcA, hcJ⟩
  have hBA : B ≤ A := inf_le_left
  have hdvd : Nat.card B ∣ 3 ^ 3 := by
    rw [← h27.trans (by norm_num : (27 : ℕ) = 3 ^ 3)]
    exact card_dvd_of_le hBA
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hB27 : Nat.card B ≠ 27 := by
    intro h
    have hBeq : B = A := eq_of_le_of_card_ge hBA (by rw [h, h27])
    have haB : a ∈ B := by
      rw [hBeq]
      exact haAL.1
    exact haC haB.2
  have hB3 : 3 < Nat.card B := by
    have hlt : zpowers d < B := lt_of_le_of_ne hdB fun h => hcd (h ▸ hcB)
    rw [← hcard3]
    exact card_lt_of_lt hlt
  have hB9 : Nat.card B = 9 := by
    rcases j with _ | _ | _ | _ | j
    · rw [hjc] at hB3; norm_num at hB3
    · rw [hjc] at hB3; norm_num at hB3
    · rw [hjc]; norm_num
    · exact absurd (by rw [hjc]; norm_num) hB27
    · omega
  refine ⟨hB9, le_antisymm (sup_le inf_le_left inf_le_left) ?_⟩
  have hcle : zpowers c ≤ B ⊔ (A ⊓ J) := (zpowers_le.mpr hcB).trans le_sup_left
  have hALle : A ⊓ L ≤ B ⊔ (A ⊓ J) := (le_inf inf_le_left (hALI.trans hIJ)).trans le_sup_right
  calc A = zpowers c ⊔ (A ⊓ L) := hAcL.symm
    _ ≤ B ⊔ (A ⊓ J) := sup_le hcle hALle

end Cent

end Item2110Res3Proof

end CFSG.RankThree.PartTwo.Sec21
