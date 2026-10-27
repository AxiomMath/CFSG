module

public import CFSG.RankThree.PartTwo.Sec15.Sylow1523ThetaFrob
public import CFSG.RankThree.PartTwo.Sec15.Sylow1523ONFrob
public import CFSG.RankThree.Native.ONSevenKernel
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow1523Theta

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.Blueprint
open scoped commutatorElement

theorem le_center_of_commutator_le_center {E : Type*} [Group E] [Group.IsPerfect E]
    {N : Subgroup E} (h : ⁅N, ⊤⁆ ≤ Subgroup.center E) : N ≤ Subgroup.center E := by
  have h1 : ⁅⁅N, (⊤ : Subgroup E)⁆, (⊤ : Subgroup E)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h.trans (Subgroup.center_le_centralizer _)
  have h2 : ⁅⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆, N⁆ = ⊥ := by
    apply Subgroup.commutator_commutator_eq_bot_of_rotate
    · rw [Subgroup.commutator_comm (⊤ : Subgroup E) N]
      exact h1
    · exact h1
  rw [← _root_.commutator_def, Group.IsPerfect.commutator_eq_top,
    Subgroup.commutator_eq_bot_iff_le_centralizer] at h2
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (h2 (Subgroup.mem_top g)) n hn).symm

theorem not_sq_dvd_card_ON {r : ℕ} (hr : r.Prime) (h2 : r ≠ 2) (h3 : r ≠ 3) (h7 : r ≠ 7) :
    ¬ r ^ 2 ∣ 460815505920 := by
  intro h
  have hcop : Nat.Coprime (r ^ 2) (2 ^ 9 * 3 ^ 4 * 7 ^ 3) := by
    refine Nat.Coprime.pow_left 2 ?_
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_
    · exact Nat.Coprime.pow_right 9 ((Nat.coprime_primes hr Nat.prime_two).mpr h2)
    · exact Nat.Coprime.pow_right 4 ((Nat.coprime_primes hr Nat.prime_three).mpr h3)
    · exact Nat.Coprime.pow_right 3 ((Nat.coprime_primes hr (by norm_num)).mpr h7)
  have hN : (460815505920 : ℕ) = 5 * 11 * 19 * 31 * (2 ^ 9 * 3 ^ 4 * 7 ^ 3) := by norm_num
  rw [hN] at h
  have hM : r ^ 2 ∣ 5 * 11 * 19 * 31 := hcop.dvd_of_dvd_mul_right h
  have hr1 : r ∣ 5 * 11 * 19 * 31 := (dvd_pow_self r two_ne_zero).trans hM
  have key : r = 5 ∨ r = 11 ∨ r = 19 ∨ r = 31 := by
    rcases (Nat.Prime.dvd_mul hr).mp hr1 with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h)
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h)))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h)))
  rcases key with rfl | rfl | rfl | rfl <;> norm_num at hM

variable {H : Type} [Group H] [Finite H]

theorem pCore_two_eq_of_frob_cover {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    [Group.IsPerfect H]
    (e : (H ⧸ aschbacherSolvableCore 3 H) ⧸ Subgroup.center (H ⧸ aschbacherSolvableCore 3 H) ≃* S)
    (hfrob : ∃ Z : Subgroup S, IsPGroup 2 Z ∧ (∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) ∧ Z ≠ ⊥ ∧
      ∃ t : S, t ^ 7 = 1 ∧ t ∈ Subgroup.normalizer (Z : Set S) ∧
        ∀ z ∈ Z, t * z * t⁻¹ = z → z = 1)
    (hseven : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → ¬ 7 ∣ Nat.card π.ker)
    (hsq : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ≠ 7 → ¬ r ^ 2 ∣ Nat.card S)
    (hloc : ∀ q : ℕ, q.Prime → 3 < q → ∀ Q : Subgroup H, IsPGroup q Q → ∀ u : H, u ≠ 1 →
      IsPGroup 2 (Subgroup.zpowers u) → CFSG.pRank q ↥(Q ⊓ Subgroup.centralizer {u}) ≤ 2) :
    CFSG.pCore 2 H = aschbacherSolvableCore 3 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := aschbacherSolvableCore 3 H with hθdef
  set R := CFSG.pCore 2 H with hRdef
  obtain ⟨hθs, -, hθ3, -, -, -, hθmax⟩ :=
    solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  have hRθ : R ≤ θ := hθmax 2 Nat.prime_two (by norm_num)
  refine le_antisymm hRθ ?_
  set π := QuotientGroup.mk' R with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R
  set Θ := θ.map π with hΘ
  have hΘn : Θ.Normal := Subgroup.Normal.map inferInstance π hπs
  have hΘs : Group.IsSolvable Θ := Group.isSolvable_of_surjective (π.subgroupMap_surjective θ)
  have hO2 : CFSG.pCore 2 (H ⧸ R) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hnormal2 : ∀ N : Subgroup (H ⧸ R), N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hN2 =>
    le_bot_iff.mp (hO2 ▸ le_sSup ⟨hN, hN2⟩)
  have hcent_bot : Subgroup.centralizer ((⊥ : Subgroup (H ⧸ R)) : Set (H ⧸ R)) = ⊤ :=
    eq_top_iff.mpr fun g _ => Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [(Subgroup.mem_bot).mp hh, one_mul, mul_one]
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := fun h3 => hθ3 (h3.trans (Subgroup.card_map_dvd θ π))
  have hcore_bot : ∀ r : ℕ, r.Prime → ¬ r ∣ Nat.card Θ → CFSG.pCore r Θ = ⊥ := by
    intro r hr hrΘ
    have : Fact r.Prime := ⟨hr⟩
    rw [← Subgroup.card_eq_one]
    rcases (CFSG.pCore_isPGroup (p := r) (G := Θ)).card_eq_or_dvd with h1 | h1
    · exact h1
    · exact absurd (h1.trans (Subgroup.card_subgroup_dvd_card _)) hrΘ
  set Zc := Subgroup.center (H ⧸ θ) with hZc
  set ψ : H →* S :=
    e.toMonoidHom.comp ((QuotientGroup.mk' Zc).comp (QuotientGroup.mk' θ)) with hψ
  have hψs : Function.Surjective ψ :=
    e.surjective.comp ((QuotientGroup.mk'_surjective Zc).comp (QuotientGroup.mk'_surjective θ))
  have hψker : ∀ h : H, ψ h = 1 ↔ (h : H ⧸ θ) ∈ Zc := by
    intro h
    change e (QuotientGroup.mk' Zc (QuotientGroup.mk' θ h)) = 1 ↔ _
    simp only [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hψθ : θ ≤ ψ.ker := fun h hh => (hψker h).mpr (by
    rw [(QuotientGroup.eq_one_iff h).mpr hh]
    exact Zc.one_mem)
  by_contra hθR
  by_cases hc : Θ ≤ Subgroup.center (H ⧸ R)
  ·
    set φ : H ⧸ R →* S := QuotientGroup.lift R ψ (hRθ.trans hψθ) with hφ
    have hφπ : ∀ h : H, φ (π h) = ψ h := fun h => rfl
    have hφs : Function.Surjective φ := by
      intro s
      obtain ⟨h, rfl⟩ := hψs s
      exact ⟨π h, hφπ h⟩
    have hΘker : Θ ≤ φ.ker := by
      rintro _ ⟨h, hh, rfl⟩
      rw [MonoidHom.mem_ker, hφπ]
      exact hψθ hh
    have hcomm : ⁅φ.ker, ⊤⁆ ≤ Θ := by
      rw [Subgroup.commutator_le]
      intro x hx y _
      obtain ⟨h, rfl⟩ := hπs x
      obtain ⟨h', rfl⟩ := hπs y
      have hz : (h : H ⧸ θ) ∈ Zc := (hψker h).mp (by rw [← hφπ]; exact hx)
      have h1 : QuotientGroup.mk' θ ⁅h, h'⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hz _).symm
      exact ⟨⁅h, h'⁆, (QuotientGroup.eq_one_iff _).mp h1, map_commutatorElement π h h'⟩
    have hcentral : φ.ker ≤ Subgroup.center (H ⧸ R) :=
      le_center_of_commutator_le_center (hcomm.trans hc)
    have hΘbot : Θ = ⊥ := by
      rw [← Subgroup.card_eq_one]
      by_contra hne
      obtain ⟨r, hr, hrΘ⟩ := Nat.exists_prime_and_dvd hne
      have : Fact r.Prime := ⟨hr⟩
      have hrK : r ∣ Nat.card φ.ker := hrΘ.trans (Subgroup.card_dvd_of_le hΘker)
      have hr2 : r ≠ 2 := by
        rintro rfl
        obtain ⟨⟨x, hx⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2 hrΘ
        have hox : orderOf x = 2 := (Subgroup.orderOf_mk x hx).symm.trans hx2
        have hxc : x ∈ Subgroup.center (H ⧸ R) := hc hx
        have hN : (Subgroup.zpowers x).Normal := ⟨fun w hw g => by
          have hwc : w ∈ Subgroup.center (H ⧸ R) := (Subgroup.zpowers_le.mpr hxc) hw
          rw [Subgroup.mem_center_iff.mp hwc g, mul_inv_cancel_right]
          exact hw⟩
        have h2 : IsPGroup 2 (Subgroup.zpowers x) :=
          IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hox, pow_one])
        have h0 := hnormal2 _ hN h2
        rw [Subgroup.zpowers_eq_bot] at h0
        rw [h0, orderOf_one] at hox
        exact absurd hox (by norm_num)
      have hr3 : r ≠ 3 := by
        rintro rfl
        exact hΘ3 hrΘ
      have hr7 : r ≠ 7 := by
        rintro rfl
        exact hseven (H ⧸ R) φ hφs hcentral hrK
      obtain ⟨C⟩ : Nonempty (Sylow r φ.ker) := inferInstance
      obtain ⟨Q⟩ : Nonempty (Sylow r S) := inferInstance
      exact Sylow.ne_bot_of_dvd_card C hrK
        (CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot φ hφs hcentral C Q
          (CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd (hsq r hr hr2 hr3 hr7) Q))
    apply hθR
    rw [hΘ, Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hΘbot
    exact hΘbot
  ·
    obtain ⟨q, hq, hqc⟩ := Sec16.Steps166.exists_pCore_centralizer_ne_top hΘs hc
    have : Fact q.Prime := ⟨hq⟩
    have hq2 : q ≠ 2 := by
      rintro rfl
      apply hqc
      have hN : ((CFSG.pCore 2 Θ).map Θ.subtype).Normal := inferInstance
      rw [hnormal2 _ hN (CFSG.pCore_isPGroup.map Θ.subtype)]
      exact hcent_bot
    have hq3 : q ≠ 3 := by
      rintro rfl
      apply hqc
      rw [hcore_bot 3 Nat.prime_three hΘ3, Subgroup.map_bot]
      exact hcent_bot
    have hq3' : 3 < q := by
      have := hq.two_le
      omega
    have hψsol : Group.IsSolvable ψ.ker := by
      let f : θ →* ψ.ker := Subgroup.inclusion hψθ
      let g : ψ.ker →* Zc := ((QuotientGroup.mk' θ).comp ψ.ker.subtype).codRestrict Zc
        fun x => (hψker x).mp x.2
      have hfg : g.ker ≤ f.range := by
        intro x hx
        have h1 : QuotientGroup.mk' θ (x : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp h1⟩, rfl⟩
      have : Group.IsSolvable θ := hθs
      have : Group.IsSolvable Zc :=
        Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
      exact Group.isSolvable_of_ker_le_range f g hfg
    obtain ⟨Z, hZ2, hZab, hZ1, t, ht7, htN, htfix⟩ := hfrob
    have : ((CFSG.pCore q Θ).map Θ.subtype).Normal := inferInstance
    exact false_of_noncentral_pCore_frob ψ hψs hψsol (hRθ.trans hψθ) hZ2 hZab hZ1
      (by norm_num : Nat.Prime 7) (by norm_num) (by norm_num) ht7 htN htfix hq2
      (CFSG.pCore_isPGroup.map Θ.subtype) hqc (hloc q hq hq3')

theorem pCore_two_eq_of_ON
    [Group.IsPerfect H]
    (e : (H ⧸ aschbacherSolvableCore 3 H) ⧸ Subgroup.center (H ⧸ aschbacherSolvableCore 3 H) ≃*
      NativeSporadic.ON)
    (hloc : ∀ q : ℕ, q.Prime → 3 < q → ∀ Q : Subgroup H, IsPGroup q Q → ∀ u : H, u ≠ 1 →
      IsPGroup 2 (Subgroup.zpowers u) → CFSG.pRank q ↥(Q ⊓ Subgroup.centralizer {u}) ≤ 2) :
    CFSG.pCore 2 H = aschbacherSolvableCore 3 H := by
  have : IsSimpleGroup NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
  refine pCore_two_eq_of_frob_cover ?_ ON_frobenius_pair ?_ ?_ hloc
  · exact e
  · intro E _ _ _ π hπ hC
    refine CFSG.RankThree.Native.not_seven_dvd_card_ker_ON ?_ π hπ hC
    exact ⟨MulEquiv.refl _⟩
  · intro r hr h2 h3 h7
    rw [CFSG.Sporadic.ON.card_ON_eq]
    exact not_sq_dvd_card_ON hr h2 h3 h7

end CFSG.RankThree.PartTwo.Sec15.Sylow1523Theta
