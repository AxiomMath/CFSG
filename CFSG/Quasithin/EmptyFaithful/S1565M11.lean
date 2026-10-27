module

public import CFSG.Quasithin.EmptyFaithful.S1565M8

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Sigma

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

private noncomputable def starMapM11 (M' H K : Subgroup G) (hKH : K ≤ H) :
    ↥K →* ↥(E2.star M' H K) :=
  (((QuotientGroup.mk' ((kerIn M' H).subgroupOf H)).comp (Subgroup.inclusion hKH)).codRestrict
    (E2.star M' H K) fun k => ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)

omit [Finite G] in
private theorem starMapM11_surjective (M' H K : Subgroup G) (hKH : K ≤ H) :
    Function.Surjective (starMapM11 M' H K hKH) := by
  rintro ⟨y, x, hx, rfl⟩
  refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
  apply Subtype.ext
  rfl

omit [Finite G] in
private theorem starMapM11_eq_one_iff (M' H K : Subgroup G) (hKH : K ≤ H) (k : ↥K) :
    starMapM11 M' H K hKH k = 1 ↔ Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).mp this
  · intro h
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr h

theorem exists_sigma_central (hF : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) (hne : autIH V₁ I H K ≠ ⊥) {M' : Subgroup G}
    (hkerchar : ∀ x : G, x ∈ kerIn M' H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) :
    ∃ σ : ↥(autIH V₁ I H K) →* ↥(E2.star M' H K), Function.Surjective σ ∧
      σ.ker ≤ Subgroup.center ↥(autIH V₁ I H K) := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hFI := factElem hF hIU
  have hρ := toAutI_surjective hF I
  have hker := toAutI_ker_le_kerIn hF hIU hne hkerchar
  have hq := starMapM11_surjective M' H K hKH
  have hkq : (toAutI hF I).ker ≤ (starMapM11 M' H K hKH).ker := by
    intro k hk
    rw [MonoidHom.mem_ker, starMapM11_eq_one_iff]
    exact hker k hk
  let σ : ↥(autIH V₁ I H K) →* ↥(E2.star M' H K) :=
    (toAutI hF I).liftOfRightInverse (Function.surjInv hρ) (Function.rightInverse_surjInv hρ)
      ⟨starMapM11 M' H K hKH, hkq⟩
  have hσρ : ∀ k, σ (toAutI hF I k) = starMapM11 M' H K hKH k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨_, hkq⟩ k
  have hσs : Function.Surjective σ := by
    intro y
    obtain ⟨k, rfl⟩ := hq y
    exact ⟨toAutI hF I k, hσρ k⟩
  refine ⟨σ, hσs, ?_⟩
  intro l hl
  obtain ⟨k, rfl⟩ := hρ l
  have hk1 : starMapM11 M' H K hKH k = 1 := by
    rw [← hσρ]
    exact hl
  have hkK : (k : G) ∈ kerIn M' H :=
    Subgroup.mem_subgroupOf.mp ((starMapM11_eq_one_iff M' H K hKH k).mp hk1)
  have hkc := (hkerchar _).mp hkK
  rw [Subgroup.mem_center_iff]
  intro l'
  obtain ⟨k', rfl⟩ := hρ l'
  have hmem : ((k * k' * k⁻¹ * k'⁻¹ : ↥K) : G) ∈ pCoreOf 2 H := by
    have := hkc.2 (k' : G) (Subgroup.mem_sup_left k'.2)
    simpa using this
  have h1 : toAutI hF I (k * k' * k⁻¹ * k'⁻¹) = 1 := by
    rw [toAutI_eq_one_iff]
    exact hF.actH_eq_one_of_mem_pCoreOf hIU hmem
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have h2 := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  exact h2.symm

end Sigma

section Exceptional

variable {W : Type} [CommGroup W]

theorem center_eq_bot_of_natural_sl_two {L : Subgroup (MulAut W)} {U Z : Subgroup W} {d : ℕ}
    [NeZero d] (h : BinaryNaturalSL L U Z d 1) : Subgroup.center ↥L = ⊥ := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  change ↥(StatedSL d K) →* ↥L at π
  have hinj := natural_realizes_injective _ hπ
  have hsurj : Function.Surjective π := hπ.1
  let e := specialLinearGroupEquivStatedSL d K
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨γ, rfl⟩ := hsurj z
  have hγ : ∀ γ' : ↥(StatedSL d K), γ' * γ = γ * γ' := by
    intro γ'
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hz (π γ')
  have hA : e.symm γ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K) := by
    rw [Subgroup.mem_center_iff]
    intro A
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hγ (e A)
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hd : d ≠ 0 := NeZero.ne d
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Fintype.card_fin, zero_pow hd] at hr
    exact zero_ne_one hr
  have hunits : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, hK]
    norm_num
  have hsub : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hunits).1
  have hr1 : r = 1 := by
    have := Subsingleton.elim (Units.mk0 r hr0) 1
    exact congrArg Units.val this
  subst hr1
  have hA1 : e.symm γ = 1 := by
    apply Subtype.ext
    rw [← hrA]
    simp
  have : γ = 1 := by
    have := congrArg e hA1
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  rw [this, map_one]
  exact Subgroup.one_mem _

theorem card_statedSL_four_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(StatedSL 4 K) = 20160 :=
  CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two hK

theorem card_statedSL_five_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(StatedSL 5 K) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_of_card_eq_two hK

end Exceptional

section KsNe

private theorem ordA_two_ge16 (q : ℕ) (hq : 16 ≤ q) : 10000000 ≤ ordA 2 q := by
  unfold ordA
  have h : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  rw [h, Finset.prod_pair (by norm_num)]
  have hg : Nat.gcd (2 + 1) (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd (2 + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [Nat.le_div_iff_mul_le hg0]
  have h1 : 16 ^ 3 ≤ q ^ (2 * (2 + 1) / 2) := by
    show 16 ^ 3 ≤ q ^ 3
    exact Nat.pow_le_pow_left hq 3
  have h2 : 255 ≤ q ^ 2 - 1 := by
    have : 256 ≤ q ^ 2 := by nlinarith
    omega
  have h3 : 4095 ≤ q ^ 3 - 1 := by
    have : 4096 ≤ q ^ 3 := by nlinarith [pow_pos (by omega : 0 < q) 2]
    omega
  calc 10000000 * Nat.gcd (2 + 1) (q - 1) ≤ 10000000 * 3 := Nat.mul_le_mul_left _ hg
    _ ≤ 16 ^ 3 * (255 * 4095) := by norm_num
    _ ≤ q ^ (2 * (2 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

private theorem ordTwistedA_two_ge16 (q : ℕ) (hq : 16 ≤ q) : 10000000 ≤ ordTwistedA 2 q := by
  unfold ordTwistedA
  have h : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  rw [h, Finset.prod_pair (by norm_num)]
  have hg : Nat.gcd (2 + 1) (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd (2 + 1) (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [Nat.le_div_iff_mul_le hg0]
  have h1 : 16 ^ 3 ≤ q ^ (2 * (2 + 1) / 2) := by
    show 16 ^ 3 ≤ q ^ 3
    exact Nat.pow_le_pow_left hq 3
  have h2 : 255 ≤ ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat := by
    have : (256 : ℤ) ≤ (q : ℤ) ^ 2 := by nlinarith
    have : (255 : ℤ) ≤ (q : ℤ) ^ 2 - (-1 : ℤ) ^ 2 := by norm_num; linarith
    omega
  have h3 : 4097 ≤ ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat := by
    have : (4096 : ℤ) ≤ (q : ℤ) ^ 3 := by nlinarith [sq_nonneg (q : ℤ)]
    have : (4097 : ℤ) ≤ (q : ℤ) ^ 3 - (-1 : ℤ) ^ 3 := by norm_num; linarith
    omega
  calc 10000000 * Nat.gcd (2 + 1) (q + 1) ≤ 10000000 * 3 := Nat.mul_le_mul_left _ hg
    _ ≤ 16 ^ 3 * (255 * 4097) := by norm_num
    _ ≤ q ^ (2 * (2 + 1) / 2) *
        (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat * ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

private theorem ordBC_two_ge8 (q : ℕ) (hq : 8 ≤ q) : 10000000 ≤ ordBC 2 q := by
  unfold ordBC
  have h : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h, Finset.prod_pair (by norm_num)]
  have hg : Nat.gcd 2 (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [Nat.le_div_iff_mul_le hg0]
  have h1 : 8 ^ 4 ≤ q ^ (2 * 2) := by
    show 8 ^ 4 ≤ q ^ 4
    exact Nat.pow_le_pow_left hq 4
  have h2 : 63 ≤ q ^ (2 * 1) - 1 := by
    have : 64 ≤ q ^ (2 * 1) := by
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
        _ = q ^ (2 * 1) := by norm_num
    omega
  have h3 : 4095 ≤ q ^ (2 * 2) - 1 := by
    have : 4096 ≤ q ^ (2 * 2) := by
      calc 4096 = 8 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    omega
  calc 10000000 * Nat.gcd 2 (q - 1) ≤ 10000000 * 2 := Nat.mul_le_mul_left _ hg
    _ ≤ 8 ^ 4 * (63 * 4095) := by norm_num
    _ ≤ q ^ (2 * 2) * ((q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

theorem ks_card_ne {Y : Type} [Group Y] {Ks : Subgroup Y} {n : ℕ}
    (hn : 3 ≤ n) (h : Shape15365 n Ks) :
    Nat.card ↥Ks ≠ 2520 ∧ Nat.card ↥Ks ≠ 20160 ∧ Nat.card ↥Ks ≠ 9999360 := by
  have hq8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases h with h | h | h | h | h
  ·
    obtain ⟨-, hc⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two h
    rw [hc]
    show 2 ^ n * (2 ^ (2 * n) - 1) ≠ 2520 ∧ 2 ^ n * (2 ^ (2 * n) - 1) ≠ 20160 ∧
      2 ^ n * (2 ^ (2 * n) - 1) ≠ 9999360
    rcases Nat.lt_or_ge n 8 with h8 | h8
    · interval_cases n <;> norm_num
    · have h256 : 256 ≤ 2 ^ n := by
        calc 256 = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h8
      have h65 : 65535 ≤ 2 ^ (2 * n) - 1 := by
        have : 2 ^ 16 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have : 256 * 65535 ≤ 2 ^ n * (2 ^ (2 * n) - 1) := Nat.mul_le_mul h256 h65
      omega
  ·
    obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
    subst hf
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · have : a = 1 := by omega
      subst this
      norm_num
    · have h32 : 32 ≤ 2 ^ (2 * a + 1) := by
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h1024 : 1024 ≤ (2 ^ (2 * a + 1)) ^ 2 := by
        calc 1024 = 32 ^ 2 := by norm_num
          _ ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left h32 2
      have h31 : 31 ≤ 2 ^ (2 * a + 1) - 1 := by omega
      have h1025 : 1025 ≤ (2 ^ (2 * a + 1)) ^ 2 + 1 := by omega
      have : 1024 * 31 * 1025 ≤
          (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1024 h31) h1025
      omega
  ·
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.1 rfl
    have h2 : 3 - 1 = 2 := rfl
    rw [h2] at hc
    rcases Nat.eq_or_lt_of_le hn with h3 | h4
    · subst h3
      have : ordTwistedA 2 (2 ^ 3) = 5515776 := by decide
      omega
    · have h16 : 16 ≤ 2 ^ n := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4
      have := ordTwistedA_two_ge16 (2 ^ n) h16
      omega
  ·
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    have h2 : 3 - 1 = 2 := rfl
    rw [h2] at hc
    rcases Nat.eq_or_lt_of_le hn with h3 | h4
    · subst h3
      have : ordA 2 (2 ^ 3) = 16482816 := by decide
      omega
    · have h16 : 16 ≤ 2 ^ n := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4
      have := ordA_two_ge16 (2 ^ n) h16
      omega
  ·
    have h' : IsPSp4 2 n ↥Ks := by
      simpa [E2.IsSp4Prime, show n ≠ 1 by omega] using h
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h').2.2.1 rfl
    have := ordBC_two_ge8 (2 ^ n) hq8
    omega

end KsNe

section Excl

variable {W : Type} [CommGroup W]

theorem not_d310_exceptional {L : Subgroup (MulAut W)} [Finite ↥L]
    {V : Subgroup W} {Y : Type} [Group Y] {Ks : Subgroup Y} {n : ℕ} (hn : 3 ≤ n)
    (hKs : Shape15365 n Ks) (σ : ↥L →* ↥Ks) (hσ : Function.Surjective σ)
    (hz : σ.ker ≤ Subgroup.center ↥L) :
    ¬ (AlternatingNatural L V (V ⊓ fixV L) 6 ∨ BinaryNaturalSL L V (V ⊓ fixV L) 4 1 ∨
      BinaryNaturalSL L V (V ⊓ fixV L) 5 1 ∨ A7Four L V (V ⊓ fixV L)) := by
  obtain ⟨hc504, -⟩ := ks_card_facts hn hKs
  obtain ⟨hne7, hne4, hne5⟩ := ks_card_ne hn hKs
  have hle : Nat.card ↥Ks ≤ Nat.card ↥L := Nat.card_le_card_of_surjective σ hσ
  rintro (hA6 | hL4 | hL5 | hA7)
  ·
    obtain ⟨π, hπ⟩ := hA6
    have h1 : Nat.card ↥L ≤ Nat.card ↥(alternatingGroup (Fin 6)) :=
      Nat.card_le_card_of_surjective π hπ.1
    have h2 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num [Nat.factorial]
    omega
  ·
    have hbot := center_eq_bot_of_natural_sl_two hL4
    obtain ⟨K, _, _, hK, π, hπ⟩ := hL4
    change ↥(StatedSL 4 K) →* ↥L at π
    have hσinj : Function.Injective σ :=
      (MonoidHom.ker_eq_bot_iff σ).mp (le_bot_iff.mp (hz.trans hbot.le))
    have hπb : Function.Bijective π := ⟨natural_realizes_injective _ hπ, hπ.1⟩
    have h1 : Nat.card ↥Ks = Nat.card ↥L := Nat.card_congr (Equiv.ofBijective σ ⟨hσinj, hσ⟩).symm
    have h2 : Nat.card ↥L = Nat.card ↥(StatedSL 4 K) := (Nat.card_congr (Equiv.ofBijective π hπb)).symm
    have h3 := card_statedSL_four_two (K := K) (by simpa using hK)
    exact hne4 (by omega)
  ·
    have hbot := center_eq_bot_of_natural_sl_two hL5
    obtain ⟨K, _, _, hK, π, hπ⟩ := hL5
    change ↥(StatedSL 5 K) →* ↥L at π
    have hσinj : Function.Injective σ :=
      (MonoidHom.ker_eq_bot_iff σ).mp (le_bot_iff.mp (hz.trans hbot.le))
    have hπb : Function.Bijective π := ⟨natural_realizes_injective _ hπ, hπ.1⟩
    have h1 : Nat.card ↥Ks = Nat.card ↥L := Nat.card_congr (Equiv.ofBijective σ ⟨hσinj, hσ⟩).symm
    have h2 : Nat.card ↥L = Nat.card ↥(StatedSL 5 K) := (Nat.card_congr (Equiv.ofBijective π hπb)).symm
    have h3 := card_statedSL_five_two (K := K) (by simpa using hK)
    exact hne5 (by omega)
  ·
    obtain ⟨α, π, hπ⟩ := hA7
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by norm_num)
    let τ : ↥(alternatingGroup (Fin 7)) →* ↥Ks := σ.comp π
    have hτs : Function.Surjective τ := hσ.comp hπ.1
    rcases hsimple.eq_bot_or_eq_top_of_normal τ.ker with hbot | htop
    · have hτinj : Function.Injective τ := (MonoidHom.ker_eq_bot_iff τ).mp hbot
      have h1 : Nat.card ↥Ks = Nat.card ↥(alternatingGroup (Fin 7)) :=
        (Nat.card_congr (Equiv.ofBijective τ ⟨hτinj, hτs⟩)).symm
      have h2 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num [Nat.factorial]
      exact hne7 (by omega)
    · have : Subsingleton ↥Ks := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := hτs a
        obtain ⟨y, rfl⟩ := hτs b
        have hx : x ∈ τ.ker := by rw [htop]; exact Subgroup.mem_top _
        have hy : y ∈ τ.ker := by rw [htop]; exact Subgroup.mem_top _
        rw [MonoidHom.mem_ker] at hx hy
        rw [hx, hy]
      have : Nat.card ↥Ks = 1 := Nat.card_eq_one_iff_unique.mpr ⟨this, ⟨1⟩⟩
      omega

end Excl

end CFSG.Quasithin
