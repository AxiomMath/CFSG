module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K7

open CFSG.QuasithinUnique.Vol2Native.A312L.Seven Equiv

theorem eq_bot_of_isSimpleGroup {X : Type} [Group X] [Finite X] {R : Subgroup X}
    (h2 : IsPGroup 2 R) (hs : IsSimpleGroup ↥(Subgroup.normalizer (R : Set X)))
    (hc : ¬ ∃ k : ℕ, Nat.card ↥(Subgroup.normalizer (R : Set X)) = 2 ^ k) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (R.subgroupOf (Subgroup.normalizer (R : Set X))).Normal :=
    Subgroup.normal_in_normalizer
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hn with hb | ht
  · rw [Subgroup.subgroupOf_eq_bot] at hb
    exact disjoint_self.mp (hb.mono_right Subgroup.le_normalizer)
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at ht
    have heq : Subgroup.normalizer (R : Set X) = R := le_antisymm ht Subgroup.le_normalizer
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h2
    exact hc ⟨k, by rw [heq]; exact hk⟩


theorem pow_360_eq_one {R : Subgroup ↥A7s} (hR : R ≠ ⊥) (h2 : IsPGroup 2 R)
    (hT : T7 ≤ Subgroup.normalizer (R : Set ↥A7s)) {g : ↥A7s}
    (hg : g ∈ Subgroup.normalizer (R : Set ↥A7s)) : g ^ 360 = 1 := by
  set N := Subgroup.normalizer (R : Set ↥A7s) with hN
  obtain ⟨i, hi, hZ⟩ := overgroup_Z hT
  have hcard : Nat.card ↥N = [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520].getD i 0 := by
    rw [← card_map_subtype, hZ]
    exact card_Z hi
  have hpow : Nat.card ↥N ∣ 360 → g ^ 360 = 1 := fun h =>
    orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard _ hg).trans h)
  have hnp : ∀ c, Nat.card ↥N = c → 7 ∣ c → ¬ ∃ k : ℕ, Nat.card ↥N = 2 ^ k := by
    rintro c hc h7 ⟨k, hk⟩
    rw [hc] at hk
    subst hk
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow (by norm_num) h7)
    omega
  have hL3 : ∀ e : ↥N ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Nat.card ↥N = 168 → False := fun e h168 => by
    have := slThree_isSimple
    exact hR (eq_bot_of_isSimpleGroup h2 e.isSimpleGroup (hnp 168 h168 (by norm_num)))
  have hmap : ↥N ≃* ↥(N.map A7s.subtype) := N.equivMapOfInjective A7s.subtype A7s.subtype_injective
  interval_cases i
  · exact hpow (by rw [hcard]; decide)
  · exact hpow (by rw [hcard]; decide)
  · exact hpow (by rw [hcard]; decide)
  · exact hpow (by rw [hcard]; decide)
  · exact hpow (by rw [hcard]; decide)
  · exact hpow (by rw [hcard]; decide)
  · exact hpow (by rw [hcard]; decide)
  · exact hpow (by rw [hcard]; decide)
  · exact (hL3 (hmap.trans ((MulEquiv.subgroupCongr hZ).trans z8Equiv.symm))
      (by rw [hcard]; rfl)).elim
  · exact (hL3 (hmap.trans ((MulEquiv.subgroupCongr hZ).trans z9Equiv.symm))
      (by rw [hcard]; rfl)).elim
  · exact hpow (by rw [hcard]; decide)
  · exfalso
    have htop : N = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcard, card_A7s]; rfl)
    have : IsSimpleGroup ↥A7s := alternatingGroup.isSimpleGroup (by simp)
    have hs : IsSimpleGroup ↥N :=
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).isSimpleGroup
    exact hR (eq_bot_of_isSimpleGroup h2 hs (hnp 2520 (by rw [hcard]; rfl) (by norm_num)))

theorem exists_hom_A7s {Y : Type} [Group Y] [Finite Y]
    (hY : IsAlt 7 Y ∨ IsHat Y ↥(alternatingGroup (Fin 7))) :
    ∃ ρ : Y →* ↥A7s, Function.Surjective ρ ∧ ρ.ker = Subgroup.center Y ∧
      Nat.card ↥(Subgroup.center Y) ∣ 3 := by
  rcases hY with hA | ⟨-, hc, ⟨e⟩⟩
  · obtain ⟨e⟩ := hA
    have hZ : Subgroup.center Y = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : e z ∈ Subgroup.center ↥A7s :=
        Subgroup.map_center_le_center e.surjective ⟨z, hz, rfl⟩
      rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot,
        map_eq_one_iff _ e.injective] at h1
      exact (Subgroup.mem_bot).mpr h1
    refine ⟨e.toMonoidHom, e.surjective, ?_, ?_⟩
    · rw [hZ]
      exact (MonoidHom.ker_eq_bot_iff _).mpr e.injective
    · rw [hZ, Subgroup.card_bot]
      exact one_dvd 3
  · refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)),
      e.surjective.comp (QuotientGroup.mk'_surjective _), ?_, by rw [hc]⟩
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

theorem mul_inv_mem_center {Y : Type} [Group Y] [Finite Y]
    (hY : IsAlt 7 Y ∨ IsHat Y ↥(alternatingGroup (Fin 7))) {P R : Subgroup Y}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P ⊤) (hPR : P ≤ Subgroup.normalizer (R : Set Y))
    (hR2 : IsPGroup 2 R) (hR : R ≠ ⊥) (φ : MulAut Y) (hφR : ∀ r ∈ R, φ r ∈ R) {m : ℕ}
    (hm : Nat.Coprime m 360) (hφm : φ ^ m = 1) (y : Y) : φ y * y⁻¹ ∈ Subgroup.center Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ₀, hρ₀s, hρ₀k, hc3⟩ := exists_hom_A7s hY
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.exists_conj_of_isSylowTwoOf
    (A312.isSylowTwoOf_top_map ρ₀ hρ₀s hP) isSylowTwoOf_T7
  set ρ : Y →* ↥A7s := (MulAut.conj g).toMonoidHom.comp ρ₀ with hρ
  have hρs : Function.Surjective ρ := (MulAut.conj g).surjective.comp hρ₀s
  have hρk : ρ.ker = Subgroup.center Y := by
    rw [hρ, MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective, hρ₀k]
  have hρP : P.map ρ = T7 := by
    rw [hρ, ← Subgroup.map_map]
    exact hg
  have hφR' : R.map φ.toMonoidHom = R :=
    Subgroup.eq_of_le_of_card_ge (fun _ ⟨r, hr, hrx⟩ => hrx ▸ hφR r hr)
      (Subgroup.card_map_of_injective φ.injective).ge
  have hφinv : ∀ r ∈ R, φ⁻¹ r ∈ R := by
    intro r hr
    rw [← hφR'] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    simpa using hx
  have hφk : ρ.ker.map φ.toMonoidHom = ρ.ker := by
    rw [hρk]
    exact Subgroup.characteristic_iff_map_eq.mp inferInstance φ
  set eQ := QuotientGroup.quotientKerEquivOfSurjective ρ hρs with heQ
  set σ : MulAut ↥A7s := eQ.symm.trans ((QuotientGroup.congr ρ.ker ρ.ker φ hφk).trans eQ)
    with hσdef
  have hσ : ∀ x, σ (ρ x) = ρ (φ x) := by
    intro x
    have h1 : eQ.symm (ρ x) = (x : Y ⧸ ρ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hσdef, MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
    rfl
  have hσpow : ∀ k : ℕ, ∀ x, (σ ^ k) (ρ x) = ρ ((φ ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih, hσ]
  have hσm : σ ^ m = 1 := by
    ext a
    obtain ⟨x, rfl⟩ := hρs a
    rw [hσpow, hφm]
    rfl
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  obtain ⟨π, hπ⟩ := hbij.2 σ
  have hπm : π ^ m = 1 := hbij.1 (by rw [map_pow, hπ, hσm, map_one])
  have hm2 : ¬ 2 ∣ m := fun h => by
    have := Nat.Coprime.coprime_dvd_left h hm
    norm_num at this
  have hsign : Equiv.Perm.sign π = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
    · exact h
    · exfalso
      have h1 : Equiv.Perm.sign (π ^ m) = 1 := by rw [hπm, map_one]
      rw [map_pow, h, (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm2)).neg_one_pow] at h1
      exact absurd h1 (by decide)
  set π' : ↥A7s := ⟨π, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩ with hπ'
  have hσπ : ∀ a : ↥A7s, σ a = π' * a * π'⁻¹ := by
    intro a
    rw [← hπ]
    exact Subtype.ext (MulAut.conjNormal_apply π a)
  set R₀ := R.map ρ with hR₀
  have hR₀N : π' ∈ Subgroup.normalizer (R₀ : Set ↥A7s) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hσπ, hσ]
      exact ⟨φ x, hφR x hx, rfl⟩
    · intro ha
      rw [← hσπ] at ha
      obtain ⟨x, hx, hxa⟩ := ha
      refine ⟨φ⁻¹ x, hφinv x hx, ?_⟩
      apply σ.injective
      rw [hσ, ← hxa, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hR₀ : R₀ ≠ ⊥ := by
    intro h
    apply hR
    have hle : R ≤ Subgroup.center Y := by
      rw [← hρk]
      exact (Subgroup.map_eq_bot_iff R).mp h
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hR2
    have h3 : 2 ^ k ∣ 3 := hk ▸ (Subgroup.card_dvd_of_le hle).trans hc3
    have hk0 : k = 0 := by
      rcases k with _ | k
      · rfl
      · exact absurd ((pow_dvd_pow 2 (Nat.succ_pos k)).trans h3) (by norm_num)
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  have hT7 : T7 ≤ Subgroup.normalizer (R₀ : Set ↥A7s) := by
    rw [← hρP]
    exact (Subgroup.map_mono hPR).trans (Subgroup.le_normalizer_map ρ)
  have h360 := pow_360_eq_one hR₀ (hR2.map ρ) hT7 hR₀N
  have hπ'm : π' ^ m = 1 := Subtype.ext (by simpa [hπ'] using hπm)
  have hπ1 : π' = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hπ'm, h360⟩
    rwa [Nat.Coprime.gcd_eq_one hm, pow_one] at h
  have hσ1 : ∀ a, σ a = a := fun a => by rw [hσπ, hπ1]; group
  rw [← hρk, MonoidHom.mem_ker, map_mul, map_inv, ← hσ, hσ1, mul_inv_cancel]

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K7
