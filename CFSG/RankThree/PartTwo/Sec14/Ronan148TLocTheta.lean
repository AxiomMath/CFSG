module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TLocDefs
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {X : Type} [Group X]

theorem pPrimeCoreOf_map_mulAut (σ : MulAut X) (H : Subgroup X) :
    pPrimeCoreOf 3 (H.map σ.toMonoidHom) = (pPrimeCoreOf 3 H).map σ.toMonoidHom := by
  let ψ : ↥H ≃* ↥(H.map σ.toMonoidHom) := Subgroup.equivMapOfInjective H σ.toMonoidHom σ.injective
  have h1 : (pPrimeCore 3 ↥H).map ψ.toMonoidHom = pPrimeCore 3 ↥(H.map σ.toMonoidHom) :=
    pPrimeCore_map_iso 3 ψ
  have h2 : (H.map σ.toMonoidHom).subtype.comp ψ.toMonoidHom = σ.toMonoidHom.comp H.subtype := by
    ext g
    rfl
  unfold pPrimeCoreOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

theorem map_autFix_eq_of_commute {ε b : MulAut X} (h : ε * b = b * ε) :
    (Sec4.autFix b).map ε.toMonoidHom = Sec4.autFix b := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change b (ε y) = ε y
    have h1 : b (ε y) = ε (b y) := by
      change (b * ε) y = (ε * b) y
      rw [h]
    rw [h1, Sec4.mem_autFix.mp hy]
  · intro hx
    refine ⟨ε.symm x, ?_, by simp⟩
    rw [SetLike.mem_coe, Sec4.mem_autFix]
    have hx' : b x = x := Sec4.mem_autFix.mp hx
    have h1 : ε (b (ε.symm x)) = b x := by
      change (ε * b) (ε.symm x) = b x
      rw [h]
      change b (ε (ε.symm x)) = b x
      rw [MulEquiv.apply_symm_apply]
    apply ε.injective
    rw [h1, hx', MulEquiv.apply_symm_apply]

theorem map_eq_of_invariant {E : Subgroup (MulAut X)} {K : Subgroup X} [Finite X]
    (hKE : ∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) {ε : MulAut X} (hε : ε ∈ E) :
    K.map ε.toMonoidHom = K := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨k, hk, rfl⟩
    exact hKE ε hε k hk
  · rw [Subgroup.card_map_of_injective ε.injective]

theorem core_invariant {E : Subgroup (MulAut X)} [Finite X] (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    {K : Subgroup X} (hKE : ∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) {b : MulAut X} (hb : b ∈ E) :
    ∀ ε ∈ E, ∀ y ∈ pPrimeCoreOf 3 (K ⊓ Sec4.autFix b),
      ε y ∈ pPrimeCoreOf 3 (K ⊓ Sec4.autFix b) := by
  intro ε hε y hy
  have hmap : (K ⊓ Sec4.autFix b).map ε.toMonoidHom = K ⊓ Sec4.autFix b := by
    rw [Subgroup.map_inf _ _ _ ε.injective, map_eq_of_invariant hKE hε,
      map_autFix_eq_of_commute (hEc ε hε b hb)]
  have h1 : ε y ∈ (pPrimeCoreOf 3 (K ⊓ Sec4.autFix b)).map ε.toMonoidHom := ⟨y, hy, rfl⟩
  rwa [← pPrimeCoreOf_map_mulAut, hmap] at h1

theorem finite_mulAut [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun σ : MulAut X => (σ : X → X)) fun a b h => MulEquiv.ext (congrFun h)

theorem mem_fixE_of_autFix [Finite X] {E : Subgroup (MulAut X)} (hE9 : Nat.card E = 9)
    (hE3 : ∀ ε ∈ E, ε ^ 3 = 1) {ε₀ ε₁ : MulAut X} (h₀ : ε₀ ∈ E) (h₀1 : ε₀ ≠ 1) (h₁ : ε₁ ∈ E)
    (h₁0 : ε₁ ∉ Subgroup.zpowers ε₀) {x : X} (hx₀ : ε₀ x = x) (hx₁ : ε₁ x = x) :
    x ∈ fixE E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut X) := finite_mulAut
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (IsPGroup.commutative_of_card_eq_prime_sq (p := 3)
      (by rw [hE9]; norm_num) ⟨a, ha⟩ ⟨b, hb⟩)
  set F := Subgroup.zpowers ε₀ ⊔ Subgroup.zpowers ε₁ with hF
  have hFE : F ≤ E := sup_le (Subgroup.zpowers_le.mpr h₀) (Subgroup.zpowers_le.mpr h₁)
  have hz₀ : Nat.card (Subgroup.zpowers ε₀) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE3 ε₀ h₀) h₀1
  have hlt : Subgroup.zpowers ε₀ < F := by
    refine lt_of_le_of_ne le_sup_left fun h => h₁0 ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ε₁)
  have hFcard : Nat.card F = 9 := by
    have hdvd : Nat.card F ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le hFE
    have h3 : 3 ∣ Nat.card F := hz₀ ▸ Subgroup.card_dvd_of_le hlt.le
    have hne : Nat.card F ≠ 3 := fun h3' => by
      have := Subgroup.eq_of_le_of_card_ge hlt.le (by rw [h3', hz₀])
      exact hlt.ne this
    have h9 : Nat.card F ≠ 1 := fun h1 => by
      rw [h1] at h3
      norm_num at h3
    obtain ⟨i, hi, hiF⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card F ∣ 3 ^ 2 by norm_num [hdvd])
    interval_cases i
    · exact absurd (by simpa using hiF) h9
    · exact absurd (by simpa using hiF) hne
    · simpa using hiF
  have hFeq : F = E := Subgroup.eq_of_le_of_card_ge hFE (by rw [hFcard, hE9])
  let S : Subgroup (MulAut X) :=
    { carrier := {β | β x = x}
      mul_mem' := fun {β γ} hβ hγ => by
        change (β * γ) x = x
        rw [MulAut.mul_apply, show γ x = x from hγ, show β x = x from hβ]
      one_mem' := rfl
      inv_mem' := fun {β} hβ => by
        change β⁻¹ x = x
        have hβ' : β x = x := hβ
        calc β⁻¹ x = β⁻¹ (β x) := by rw [hβ']
          _ = x := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] }
  have hFS : F ≤ S := sup_le (Subgroup.zpowers_le.mpr hx₀) (Subgroup.zpowers_le.mpr hx₁)
  intro ε hε
  rw [← hFeq] at hε
  exact hFS hε

theorem autFix_eq_of_mem_zpowers {ε₀ ε₁ : MulAut X} (h3 : ε₀ ^ 3 = 1) (h₁ : ε₁ ∈ Subgroup.zpowers ε₀)
    (h₁1 : ε₁ ≠ 1) : Sec4.autFix ε₁ = Sec4.autFix ε₀ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h₁
  have hfix : ∀ (β : MulAut X) (n : ℤ) (x : X), β x = x → (β ^ n) x = x := by
    intro β n x hx
    have hnat : ∀ m : ℕ, (β ^ m) x = x := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ, MulAut.mul_apply, hx, ih]
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · exact_mod_cast hnat m
    · rw [zpow_neg, zpow_natCast]
      calc (β ^ m)⁻¹ x = (β ^ m)⁻¹ ((β ^ m) x) := by rw [hnat m]
        _ = x := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hk3 : ¬ (3 : ℤ) ∣ k := by
    rintro ⟨j, rfl⟩
    apply h₁1
    rw [zpow_mul, show ε₀ ^ (3 : ℤ) = 1 by exact_mod_cast h3, one_zpow]
  have hkk : ε₀ = (ε₀ ^ k) ^ k := by
    rw [← zpow_mul]
    have hmod : k * k % 3 = 1 := by
      have : k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases this with h | h <;>
        · have : k * k % 3 = (k % 3) * (k % 3) % 3 := Int.mul_emod _ _ _
          rw [this, h]
          norm_num
    have hk : k * k = 3 * (k * k / 3) + 1 := by omega
    rw [hk, zpow_add, zpow_mul, show ε₀ ^ (3 : ℤ) = 1 by exact_mod_cast h3, one_zpow, one_mul,
      zpow_one]
  ext x
  constructor
  · intro hx
    rw [Sec4.mem_autFix] at hx ⊢
    rw [hkk]
    exact hfix (ε₀ ^ k) k x hx
  · intro hx
    exact hfix ε₀ k x hx

theorem isSolvable_inSubgroup_theta [Finite X] (H : Subgroup X) :
    Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) H) := by
  have h := (solvable_prime_complement_core_characterization (H := ↥H) Nat.prime_three).1
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective (aschbacherSolvableCore 3 ↥H) H.subtype
      H.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)

theorem eq_bot_of_loc [Finite X] {E : Subgroup (MulAut X)} (hE9 : Nat.card E = 9)
    (hE3 : ∀ ε ∈ E, ε ^ 3 = 1) (hloc : LocE X E) (hfix : IsPGroup 3 (fixE E))
    {K : Subgroup X} (hKE : ∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) (hKp : Group.IsPerfect K) (hK1 : K ≠ ⊥)
    (hgen : K ≤ ⨆ (ε : MulAut X) (_ : ε ∈ E) (_ : ε ≠ 1), pPrimeCoreOf 3 (K ⊓ Sec4.autFix ε))
    {N : Subgroup X} (hN3 : ¬ 3 ∣ Nat.card N) (hNE : ∀ ε ∈ E, ∀ n ∈ N, ε n ∈ N)
    (hNK : K ≤ Subgroup.normalizer (N : Set X)) : N = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut X) := finite_mulAut
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (IsPGroup.commutative_of_card_eq_prime_sq (p := 3)
      (by rw [hE9]; norm_num) ⟨a, ha⟩ ⟨b, hb⟩)
  by_contra hN1
  obtain ⟨ε₀, hε₀, hε₀1, hN0⟩ := hloc N hN3 hNE
  have hNfix : ¬ N ≤ fixE E := by
    intro hle
    apply hN1
    have hP : IsPGroup 3 N := hfix.to_le hle
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact Subgroup.card_eq_one.mp hk
    · exact absurd (hk ▸ dvd_pow_self 3 (Nat.succ_ne_zero k)) hN3
  have hcore : ∀ b ∈ E, b ≠ 1 →
      pPrimeCoreOf 3 (K ⊓ Sec4.autFix b) ≤ inSubgroup (aschbacherSolvableCore 3) (Sec4.autFix ε₀) := by
    intro b hb hb1
    set W := pPrimeCoreOf 3 (K ⊓ Sec4.autFix b) with hW
    have hWK : W ≤ K := (pPrimeCoreOf_le 3 _).trans inf_le_left
    have hW3 : Nat.Coprime 3 (Nat.card W) := coprime_card_pPrimeCoreOf 3 _
    have hWN : W ≤ Subgroup.normalizer (N : Set X) := hWK.trans hNK
    have hV3 : ¬ 3 ∣ Nat.card (W ⊔ N : Subgroup X) := by
      intro h3
      have hd := (card_sup_dvd_card_mul hWN)
      have h3' : 3 ∣ Nat.card W * Nat.card N := h3.trans hd
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3' with h | h
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hW3 h
      · exact hN3 h
    have hVE : ∀ ε ∈ E, ∀ v ∈ W ⊔ N, ε v ∈ W ⊔ N := by
      intro ε hε v hv
      have hmap : (W ⊔ N).map ε.toMonoidHom ≤ W ⊔ N := by
        rw [Subgroup.map_sup]
        refine sup_le_sup ?_ ?_
        · rintro _ ⟨w, hw, rfl⟩
          exact core_invariant hEc hKE hb ε hε w hw
        · rintro _ ⟨n, hn, rfl⟩
          exact hNE ε hε n hn
      exact hmap ⟨v, hv, rfl⟩
    obtain ⟨ε₁, hε₁, hε₁1, hV1⟩ := hloc (W ⊔ N) hV3 hVE
    by_cases hε₁0 : ε₁ ∈ Subgroup.zpowers ε₀
    · rw [← autFix_eq_of_mem_zpowers (hE3 ε₀ hε₀) hε₁0 hε₁1]
      exact le_sup_left.trans hV1
    · exfalso
      apply hNfix
      intro n hn
      have hn0 : n ∈ inSubgroup (aschbacherSolvableCore 3) (Sec4.autFix ε₀) := hN0 hn
      have hn1 : n ∈ inSubgroup (aschbacherSolvableCore 3) (Sec4.autFix ε₁) :=
        hV1 (Subgroup.mem_sup_right hn)
      have hx₀ : ε₀ n = n := by
        obtain ⟨m, -, rfl⟩ := hn0
        exact m.2
      have hx₁ : ε₁ n = n := by
        obtain ⟨m, -, rfl⟩ := hn1
        exact m.2
      exact mem_fixE_of_autFix hE9 hE3 hε₀ hε₀1 hε₁ hε₁0 hx₀ hx₁
  have hKT : K ≤ inSubgroup (aschbacherSolvableCore 3) (Sec4.autFix ε₀) :=
    hgen.trans (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => hcore b hb hb1)
  have := isSolvable_inSubgroup_theta (Sec4.autFix ε₀)
  have hsol : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKT)
      (Subgroup.inclusion_injective hKT)
  haveI := hKp
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK1
  exact Group.IsPerfect.not_isSolvable K hsol

theorem theta_eq_bot_of_loc [Finite X] {E : Subgroup (MulAut X)} (hE9 : Nat.card E = 9)
    (hE3 : ∀ ε ∈ E, ε ^ 3 = 1) (hloc : LocE X E) (hfix : IsPGroup 3 (fixE E))
    {K : Subgroup X} (hKE : ∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) (hKp : Group.IsPerfect K) (hK1 : K ≠ ⊥)
    (hgen : K ≤ ⨆ (ε : MulAut X) (_ : ε ∈ E) (_ : ε ≠ 1), pPrimeCoreOf 3 (K ⊓ Sec4.autFix ε)) :
    aschbacherSolvableCore 3 K = ⊥ := by
  have hchar := (solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three)
  set N : Subgroup X := inSubgroup (aschbacherSolvableCore 3) K with hNdef
  have hN3 : ¬ 3 ∣ Nat.card N := by
    rw [hNdef, inSubgroup, Subgroup.card_map_of_injective K.subtype_injective]
    exact hchar.2.2.1
  have hNE : ∀ ε ∈ E, ∀ n ∈ N, ε n ∈ N := by
    intro ε hε n hn
    obtain ⟨m, hm, rfl⟩ := hn
    set σ : MulAut K :=
      { toFun := fun k => ⟨ε (k : X), hKE ε hε k k.2⟩
        invFun := fun k => ⟨ε.symm (k : X), by
          have h1 := map_eq_of_invariant hKE hε
          have hk : (k : X) ∈ K.map ε.toMonoidHom := by rw [h1]; exact k.2
          obtain ⟨y, hy, hyk⟩ := hk
          have : ε.symm (k : X) = y := by
            rw [← hyk]
            exact ε.symm_apply_apply y
          rw [this]
          exact hy⟩
        left_inv := fun k => Subtype.ext (ε.symm_apply_apply (k : X))
        right_inv := fun k => Subtype.ext (ε.apply_symm_apply (k : X))
        map_mul' := fun a b => Subtype.ext (map_mul ε (a : X) (b : X)) } with hσ
    have hθσ : (aschbacherSolvableCore 3 K).map σ.toMonoidHom = aschbacherSolvableCore 3 K :=
      CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three σ
    have hm' : σ m ∈ aschbacherSolvableCore 3 K := by
      rw [← hθσ]
      exact ⟨m, hm, rfl⟩
    exact ⟨σ m, hm', rfl⟩
  have hNK : K ≤ Subgroup.normalizer (N : Set X) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hn : (⟨k, hk⟩ : K) * m * (⟨k, hk⟩ : K)⁻¹ ∈ aschbacherSolvableCore 3 K :=
        (Subgroup.normal_of_characteristic _).conj_mem m hm ⟨k, hk⟩
      exact ⟨_, hn, rfl⟩
    · intro hn
      obtain ⟨m, hm, hmn⟩ := hn
      have hm' : (⟨k, hk⟩ : K)⁻¹ * m * (⟨k, hk⟩ : K)⁻¹⁻¹ ∈ aschbacherSolvableCore 3 K :=
        (Subgroup.normal_of_characteristic _).conj_mem m hm _
      refine ⟨_, hm', ?_⟩
      have : (m : X) = k * n * k⁻¹ := hmn
      simp [this, mul_assoc]
  have hNbot := eq_bot_of_loc hE9 hE3 hloc hfix hKE hKp hK1 hgen hN3 hNE hNK
  rw [hNdef, inSubgroup] at hNbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hNbot

theorem faithful_of_loc [Finite X] {E : Subgroup (MulAut X)} (hE9 : Nat.card E = 9)
    (hE3 : ∀ ε ∈ E, ε ^ 3 = 1) (hloc : LocE X E) (hfix : IsPGroup 3 (fixE E))
    {K : Subgroup X} (hKE : ∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) (hKp : Group.IsPerfect K) (hK1 : K ≠ ⊥)
    (hgen : K ≤ ⨆ (ε : MulAut X) (_ : ε ∈ E) (_ : ε ≠ 1), pPrimeCoreOf 3 (K ⊓ Sec4.autFix ε))
    {ε₀ : MulAut X} (hε₀ : ε₀ ∈ E) (hε₀1 : ε₀ ≠ 1) : ¬ K ≤ Sec4.autFix ε₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut X) := finite_mulAut
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (IsPGroup.commutative_of_card_eq_prime_sq (p := 3)
      (by rw [hE9]; norm_num) ⟨a, ha⟩ ⟨b, hb⟩)
  intro hK0
  have hO : pPrimeCoreOf 3 K = ⊥ := by
    refine eq_bot_of_loc hE9 hE3 hloc hfix hKE hKp hK1 hgen
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)) ?_ ?_
    · intro ε hε y hy
      have h1 := core_invariant hEc hKE hε₀ ε hε y (by rwa [inf_of_le_left hK0])
      rwa [inf_of_le_left hK0] at h1
    · exact fun k hk => le_normalizer_pPrimeCoreOf 3 K hk
  have hKfix : K ≤ fixE E := by
    refine hgen.trans (iSup_le fun ε => iSup_le fun hε => iSup_le fun hε1 => ?_)
    by_cases hε0 : ε ∈ Subgroup.zpowers ε₀
    · have hKε : K ≤ Sec4.autFix ε := by
        rw [autFix_eq_of_mem_zpowers (hE3 ε₀ hε₀) hε0 hε1]
        exact hK0
      rw [inf_of_le_left hKε, hO]
      exact bot_le
    · intro w hw
      have hw' := (pPrimeCoreOf_le 3 _) hw
      exact mem_fixE_of_autFix hE9 hE3 hε₀ hε₀1 hε hε0 (Sec4.mem_autFix.mp (hK0 hw'.1))
        (Sec4.mem_autFix.mp hw'.2)
  have hP : IsPGroup 3 K := hfix.to_le hKfix
  have hsol : Group.IsSolvable K := by
    have := hP.isNilpotent
    infer_instance
  haveI := hKp
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK1
  exact Group.IsPerfect.not_isSolvable K hsol

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
