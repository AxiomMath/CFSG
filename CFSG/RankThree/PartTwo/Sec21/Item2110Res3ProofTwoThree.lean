module

import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofTheta

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open scoped commutatorElement

@[expose] def KF2110SylowNoncentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ d : G, d ≠ 1 → d ^ 3 = 1 →
    ∀ J ∈ thetaComponentsAt 3 d, d ∈ J → ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S J →
      ∃ s ∈ S, s ^ 3 = 1 ∧ ∃ t ∈ S, s * t ≠ t * s

namespace Item2110Res3Proof

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_of_mem_zpowers_of_pow_three {c y : G} (hc3 : c ^ 3 = 1) {k : ℕ}
    (hy : y ^ (3 ^ k) = 1) (hyc : y * c * y⁻¹ ∈ zpowers c) : y * c = c * y := by
  by_cases hc1 : c = 1
  · rw [hc1, mul_one, one_mul]
  rcases Item2113Res2Proof.mem_zpowers_cube hc3 hyc with h | h | h
  · exfalso
    apply hc1
    calc c = y⁻¹ * (y * c * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  · calc y * c = y * c * y⁻¹ * y := by group
      _ = c * y := by rw [h]
  · exfalso
    have hinv : y * c * y⁻¹ = c⁻¹ := h.trans (Item2113Res2Proof.sq_eq_inv_of_cube hc3)
    have hy2 : y ^ 2 * c * (y ^ 2)⁻¹ = c := by
      calc y ^ 2 * c * (y ^ 2)⁻¹ = y * (y * c * y⁻¹) * y⁻¹ := by rw [pow_two]; group
        _ = y * c⁻¹ * y⁻¹ := by rw [hinv]
        _ = (y * c * y⁻¹)⁻¹ := by group
        _ = c := by rw [hinv, inv_inv]
    have hP : ∀ n : ℕ, y ^ (2 * n + 1) * c * (y ^ (2 * n + 1))⁻¹ = c⁻¹ := by
      intro n
      induction n with
      | zero => simpa using hinv
      | succ n ih =>
        calc y ^ (2 * (n + 1) + 1) * c * (y ^ (2 * (n + 1) + 1))⁻¹
            = y ^ 2 * (y ^ (2 * n + 1) * c * (y ^ (2 * n + 1))⁻¹) * (y ^ 2)⁻¹ := by
              have e : y ^ (2 * (n + 1) + 1) = y ^ 2 * y ^ (2 * n + 1) := by
                rw [← pow_add]
                congr 1
                ring
              rw [e, mul_inv_rev]
              simp only [mul_assoc]
          _ = (y ^ 2 * c * (y ^ 2)⁻¹)⁻¹ := by rw [ih]; group
          _ = c⁻¹ := by rw [hy2]
    obtain ⟨n, hn⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have h1 := hP n
    rw [← hn, hy, one_mul, inv_one, mul_one] at h1
    apply hc1
    have h2 : c * c = 1 := by
      calc c * c = c * c⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel c
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hc3, h2, inv_one, one_mul]

theorem le_centralizer_of_normalizer {A R : Subgroup G} (hAR : A ≤ R) (hR3 : IsPGroup 3 R)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hmax : ∀ x : G, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A)
    (hN : ∀ y ∈ R, y ∈ normalizer (A : Set G) → ∀ a ∈ A, y * a = a * y) :
    ∀ y ∈ R, ∀ a ∈ A, y * a = a * y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent R := hR3.isNilpotent
  set N : Subgroup G := normalizer (A : Set G) ⊓ R with hNdef
  set N' : Subgroup R := N.subgroupOf R with hN'
  have hconj : ∀ k ∈ normalizer (N' : Set R), ∀ a ∈ A, (k : G) * a * (k : G)⁻¹ ∈ A := by
    intro k hk a ha
    have haN' : (⟨a, hAR ha⟩ : R) ∈ N' := by
      rw [hN', mem_subgroupOf]
      exact ⟨fun x => by
        constructor
        · intro hx
          exact A.mul_mem (A.mul_mem ha hx) (A.inv_mem ha)
        · intro hx
          have := A.mul_mem (A.mul_mem (A.inv_mem ha) hx) ha
          simpa [mul_assoc] using this, hAR ha⟩
    have h1 := (mem_normalizer_iff.mp hk _).mp haN'
    rw [hN', mem_subgroupOf] at h1
    simp only [coe_mul, coe_inv] at h1
    refine hmax _ ?_ (fun b hb => (hN _ h1.2 h1.1 b hb).symm)
    rw [conj_pow, hA3 a ha, mul_one, mul_inv_cancel]
  have hself : normalizer (N' : Set R) = N' := by
    refine le_antisymm (fun k hk => ?_) le_normalizer
    rw [hN', mem_subgroupOf]
    refine ⟨mem_normalizer_iff.mpr fun h => ⟨fun hh => hconj k hk h hh, fun hh => ?_⟩, k.2⟩
    have hk' : k⁻¹ ∈ normalizer (N' : Set R) := inv_mem hk
    have := hconj k⁻¹ hk' _ hh
    simpa [mul_assoc] using this
  have htop : N' = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent) N' hself
  intro y hy a ha
  have hyN : (⟨y, hy⟩ : R) ∈ N' := htop ▸ mem_top _
  rw [hN', mem_subgroupOf] at hyN
  exact hN y hy hyN.1 a ha

theorem commutator_mem_theta_of_ne {M K K' : Subgroup G}
    (hK : K.subgroupOf M ∈ thetaComponents 3 ↥M) (hK' : K'.subgroupOf M ∈ thetaComponents 3 ↥M)
    (hne : K.subgroupOf M ≠ K'.subgroupOf M) (hKM : K ≤ M) (hK'M : K' ≤ M) :
    ∀ k ∈ K, ∀ k' ∈ K', k * k' * k⁻¹ * k'⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) M := by
  intro k hk k' hk'
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := ↥M) Nat.prime_three
  set N := aschbacherSolvableCore 3 ↥M with hN
  set π := QuotientGroup.mk' N with hπ
  have hc₁ := isComponent_map_of_mem_thetaComponents Nat.prime_three hK
  have hc₂ := isComponent_map_of_mem_thetaComponents Nat.prime_three hK'
  have hne'' : (K.subgroupOf M).map π ≠ (K'.subgroupOf M).map π := fun h =>
    hne (hbij.injOn hK hK' h)
  have hcomm := (CFSG.LocalCores.distinct_components_commute hc₁ hc₂).resolve_left hne''
  have hkF : k ∈ M := hKM hk
  have hk'F : k' ∈ M := hK'M hk'
  have h1 : π ⟨k, hkF⟩ ∈ (K.subgroupOf M).map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk)
  have h2 : π ⟨k', hk'F⟩ ∈ (K'.subgroupOf M).map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk')
  have h3 : ⁅π ⟨k, hkF⟩, π ⟨k', hk'F⟩⁆ ∈ ⁅(K.subgroupOf M).map π, (K'.subgroupOf M).map π⁆ :=
    Subgroup.commutator_mem_commutator h1 h2
  rw [hcomm, Subgroup.mem_bot, commutatorElement_def] at h3
  have h4 : (⟨k, hkF⟩ * ⟨k', hk'F⟩ * ⟨k, hkF⟩⁻¹ * ⟨k', hk'F⟩⁻¹ : ↥M) ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    change π (⟨k, hkF⟩ * ⟨k', hk'F⟩ * ⟨k, hkF⟩⁻¹ * ⟨k', hk'F⟩⁻¹ : ↥M) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact h3
  exact ⟨_, h4, rfl⟩

theorem exists_invariant_sylowOf {p : ℕ} [Fact p.Prime] {J E : Subgroup G}
    (hEN : E ≤ normalizer (J : Set G)) (hEp : IsPGroup p E) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P J ∧ E ≤ normalizer (P : Set G) := by
  classical
  set W : Subgroup G := J ⊔ E with hW
  have hJW : J ≤ W := le_sup_left
  have hEW : E ≤ W := le_sup_right
  have hWN : W ≤ normalizer (J : Set G) := sup_le le_normalizer hEN
  have hE' : IsPGroup p (E.subgroupOf W) := hEp.comap_subtype
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  set S : Subgroup G := (Q : Subgroup W).map W.subtype with hS
  have hSW : CFSG.ABGLocalTools.IsSylowOf p S W := ⟨Q, rfl⟩
  have hES : E ≤ S := by
    intro e he
    exact ⟨⟨e, hEW he⟩, hQ (Subgroup.mem_subgroupOf.mpr he), rfl⟩
  refine ⟨S ⊓ J, hSW.inf_of_le_normalizer hJW hWN, ?_⟩
  intro e he
  rw [mem_normalizer_iff]
  intro x
  have h1 := (mem_normalizer_iff.mp (le_normalizer (hES he)) x)
  have h2 := (mem_normalizer_iff.mp (hEN he) x)
  constructor
  · rintro ⟨hxS, hxJ⟩
    exact ⟨h1.mp hxS, h2.mp hxJ⟩
  · rintro ⟨hxS, hxJ⟩
    exact ⟨h1.mpr hxS, h2.mpr hxJ⟩

section TwoThree


theorem centA_eq (h45 : Sec4.Item4_5) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdcen : IsCentral218 L d) {J₀ : Subgroup G} (hJ₀ : J₀ ∈ thetaComponentsAt 3 d)
    (hJ₀I : J₀ = iOf218 L d ⊔ inSubgroup (aschbacherSolvableCore 3) J₀)
    (hB9 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer J₀ : Subgroup G) = 9) :
    zpowers c ⊔ zpowers d = A ⊓ Sec4.thetaQuotCentralizer J₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcA, -, hLc, -, hcL⟩ := Item2113Res2Proof.pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have hdL : d ∈ L := Item2113Proof.mem_of_isCentral218 hdcen
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hIL : iOf218 L d ≤ L := (map_subtype_le _).trans inf_le_left
  have hAN : A ≤ normalizer (J₀ : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hdA hd1
      J₀ hJ₀
  have hcJ : c ∈ Sec4.thetaQuotCentralizer J₀ :=
    Item2110Res2Proof.mem_thetaQuotCentralizer_of_eq_sup (hAN hcA)
      (fun x hx => mem_centralizer_singleton_iff.mp (hLc (hIL hx))) hJ₀I
  have hJd : J₀ ≤ centralizer ({d} : Set G) := Sec6.le_centralizer_of_mem_thetaComponentsAt hJ₀
  have hdJ : d ∈ Sec4.thetaQuotCentralizer J₀ := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAN hdA, fun l hl => ?_⟩
    have : d * l * d⁻¹ = l := by
      rw [← mem_centralizer_singleton_iff.mp (hJd hl), mul_inv_cancel_right]
    rw [this, inv_mul_cancel]
    exact one_mem _
  set B := A ⊓ Sec4.thetaQuotCentralizer J₀
  have hle : zpowers c ⊔ zpowers d ≤ B :=
    sup_le (zpowers_le.mpr ⟨hcA, hcJ⟩) (zpowers_le.mpr ⟨hdA, hdJ⟩)
  have hcd : c ∉ zpowers d := fun h => hcL ((zpowers_le.mpr hdL) h)
  have hcard3 : Nat.card (zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hlt : zpowers d < zpowers c ⊔ zpowers d := lt_of_le_of_ne le_sup_right fun h =>
    hcd (h ▸ mem_sup_left (mem_zpowers c))
  have hgt : 3 < Nat.card (zpowers c ⊔ zpowers d : Subgroup G) := by
    rw [← hcard3]
    exact card_lt_of_lt hlt
  have hdvd : Nat.card (zpowers c ⊔ zpowers d : Subgroup G) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hB9]
    exact card_dvd_of_le hle
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hj2 : j = 2 := by
    rcases j with _ | _ | j
    · rw [hjc] at hgt; norm_num at hgt
    · rw [hjc] at hgt; norm_num at hgt
    · omega
  exact eq_of_le_of_card_ge hle (by rw [hB9, hjc, hj2]; norm_num)

theorem item2110TwoThree_of (h45 : Sec4.Item4_5) (hJ : Item2110JThetaI)
    (hC : Item2110CentAJ) (hKF : KF2110SylowNoncentral) : Item2110TwoThree := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen h2 J₁ hJ₁ J₂ hJ₂ hdJ₁ hdJ₂
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  obtain ⟨-, J₀, hJ₀, hJ₀I⟩ := hJ G A E U c L hpair hL d hdA hd1 hdcen
  obtain ⟨hB9, hsup⟩ := hC G A E U c L hpair hL d hdA hd1 hdcen J₀ hJ₀ hJ₀I
  have hBcd := centA_eq h45 hpair hL hdA hd1 hdcen hJ₀ hJ₀I hB9
  obtain ⟨J', hJ', hdJ', hne'⟩ : ∃ J' ∈ thetaComponentsAt 3 d, d ∈ J' ∧ J' ≠ J₀ := by
    by_cases h : J₁ = J₀
    · exact ⟨J₂, hJ₂, hdJ₂, fun h' => hne (h.trans h'.symm)⟩
    · exact ⟨J₁, hJ₁, hdJ₁, h⟩
  obtain ⟨hcA, -, -, -, -⟩ := Item2113Res2Proof.pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have hAmax := hpair.mem_S.1.2.1
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAe.2
  have hc3 : c ^ 3 = 1 := hA3 c hcA
  have hd3 : d ^ 3 = 1 := hA3 d hdA
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA3 x x.2)⟩
  set M := centralizer ({d} : Set G) with hM
  obtain ⟨hJ'M, hJ'θ⟩ := mem_thetaComponentsIn_iff.mp hJ'
  obtain ⟨hJ₀M, hJ₀θ⟩ := mem_thetaComponentsIn_iff.mp hJ₀
  have hsne : J'.subgroupOf M ≠ J₀.subgroupOf M := fun h => hne' (by
    rw [← map_subgroupOf_eq_of_le hJ'M, ← map_subgroupOf_eq_of_le hJ₀M, h])
  have hmax : ∀ x : G, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A := by
    intro x hx3 hxA
    have hab := Sec15.isElemAbelian_sup_zpowers hAe hx3 hxA
    have heq := hAmax _ hab le_sup_left
    exact heq ▸ mem_sup_right (mem_zpowers x)
  have hAN : A ≤ normalizer (J' : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hdA hd1
      J' hJ'
  obtain ⟨S', hS', hAS'⟩ := exists_invariant_sylowOf hAN hAp
  obtain ⟨Q, hQ⟩ := hS'
  have hS'J : S' ≤ J' := hQ ▸ map_subtype_le _
  have hS'3 : IsPGroup 3 S' := hQ ▸ Q.isPGroup'.map _
  have hcentr : ∀ y ∈ S', y ∈ normalizer (A : Set G) → ∀ a ∈ A, y * a = a * y := by
    intro y hyS hyA
    have hyM : y ∈ M := hJ'M (hS'J hyS)
    obtain ⟨k, hk⟩ := hS'3 ⟨y, hyS⟩
    have hyk : y ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hyc : y * c = c * y := by
      have hyO : y ∈ CFSG.GH74.GLS.oPrimeResidualOf 3
          (normalizer (A : Set G) ⊓ centralizer ({d} : Set G)) :=
        ⟨⟨y, hyA, hyM⟩, subset_closure ⟨k, Subtype.ext (by simpa using hyk)⟩, rfl⟩
      have hyH := h2 hyO
      exact commute_of_mem_zpowers_of_pow_three hc3 hyk
        ((mem_normalizer_iff.mp hyH c).mp (mem_zpowers c))
    have hyd : y * d = d * y := mem_centralizer_singleton_iff.mp hyM
    have hyJ₀ : ∀ a ∈ A ⊓ J₀, y * a = a * y := by
      intro a ⟨haA, haJ₀⟩
      have hθ := commutator_mem_theta_of_ne hJ'θ hJ₀θ hsne hJ'M hJ₀M
        y (hS'J hyS) a haJ₀
      have hmA : y * a * y⁻¹ * a⁻¹ ∈ A :=
        A.mul_mem ((mem_normalizer_iff.mp hyA a).mp haA) (A.inv_mem haA)
      have h1 : y * a * y⁻¹ * a⁻¹ ∈ A ⊓ inSubgroup (aschbacherSolvableCore 3) M := ⟨hmA, hθ⟩
      rw [Sec12.inf_inSubgroup_theta_eq_bot hAp, mem_bot] at h1
      calc y * a = y * a * y⁻¹ * a⁻¹ * (a * y) := by group
        _ = a * y := by rw [h1, one_mul]
    have hCy : A ≤ centralizer ({y} : Set G) := by
      have h1 : zpowers c ⊔ zpowers d ≤ centralizer ({y} : Set G) :=
        sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyc.symm))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyd.symm))
      have h2' : A ⊓ J₀ ≤ centralizer ({y} : Set G) := fun a ha =>
        mem_centralizer_singleton_iff.mpr (hyJ₀ a ha).symm
      rw [← hsup, ← hBcd]
      exact sup_le h1 h2'
    intro a ha
    exact (mem_centralizer_singleton_iff.mp (hCy ha)).symm
  set R := A ⊔ S' with hR
  have hR3 : IsPGroup 3 R := hAp.to_sup_of_normal_right' hS'3 hAS'
  have hRc : ∀ y ∈ R, y ∈ normalizer (A : Set G) → ∀ a ∈ A, y * a = a * y := by
    intro y hy hyA a ha
    rw [hR, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A S' hAS'] at hy
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    have hsA : s ∈ normalizer (A : Set G) := by
      have := mul_mem (inv_mem (le_normalizer hb)) hyA
      simpa using this
    have h1 := hcentr s hs hsA a ha
    have h2' : b * a = a * b :=
      congrArg Subtype.val (hAe.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
    calc b * s * a = b * (s * a) := by group
      _ = b * (a * s) := by rw [h1]
      _ = b * a * s := by group
      _ = a * b * s := by rw [h2']
      _ = a * (b * s) := by group
  have hS'C := le_centralizer_of_normalizer le_sup_left hR3 hA3 hmax hRc
  obtain ⟨s, hsS, hs3, t, htS, hst⟩ := hKF G hpair.standing d hd1 hd3 J' hJ' hdJ' S' ⟨Q, hQ⟩
  have hsA : s ∈ A := hmax s hs3 fun a ha =>
    (hS'C s (mem_sup_right hsS) a ha).symm
  exact hst (hS'C t (mem_sup_right htS) s hsA).symm

end TwoThree

end Item2110Res3Proof

end CFSG.RankThree.PartTwo.Sec21
