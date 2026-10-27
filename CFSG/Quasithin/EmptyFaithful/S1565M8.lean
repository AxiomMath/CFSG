module

public import CFSG.Quasithin.EmptyFaithful.S1565M9
public import CFSG.Quasithin.EmptyFaithful.S1565L1
public import CFSG.Quasithin.EmptyFaithful.S1565L9
public import CFSG.Quasithin.EmptyFaithful.S1565L11
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Quasithin.Background.ThreePrimeGroup

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Nonzero

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem natural_not_le [Nonempty ι] (Γ : Subgroup (GL ι F)) {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} {π : Γ →* ↥H} (hR : (FFModel.nat Γ).RealizesVia H U Z π) : ¬ U ≤ Z := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβker, -⟩ := hR
  intro hUZ
  obtain ⟨i⟩ := ‹Nonempty ι›
  let m : ↥(FFModel.nat Γ).sec := ⟨Multiplicative.ofAdd (Pi.single i 1), trivial⟩
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
  have h1 : β u = 1 := (hβker u).mpr (hUZ u.2)
  rw [hu] at h1
  have h2 := (QuotientGroup.eq_one_iff m).mp h1
  rw [Subgroup.mem_subgroupOf] at h2
  have h3 : (Multiplicative.ofAdd (Pi.single i (1 : F)) : Multiplicative (ι → F)) = 1 :=
    Subgroup.mem_bot.mp h2
  have h4 := congrArg (fun x : Multiplicative (ι → F) => Multiplicative.toAdd x i) h3
  simp at h4

end Nonzero

section Odd

variable {W : Type} [CommGroup W]

theorem not_even_of_natural {L Q : Subgroup (MulAut W)} {V : Subgroup W} {n' : ℕ} [Finite ↥L]
    (S : Sylow 2 ↥L)
    (hS : ∀ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), (b : MulAut W) ∈ Q)
    (h3 : ¬ 3 ∣ Nat.card Q)
    (h : BinaryNaturalSL L V (V ⊓ fixV L) 3 n' ∨ BinaryNaturalSp4 L V (V ⊓ fixV L) n') :
    ¬ Even n' := by
  intro hev
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ 2 ^ n' - 1 := three_dvd_two_pow_sub_one_of_even hev
  have key : ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), orderOf b = 3 := by
    rcases h with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
    · have hchar : CharP K 2 := by
        have := Fintype.ofFinite K
        exact charP_of_card_eq_prime_pow (f := n') (by rw [← Nat.card_eq_fintype_card, hK])
      obtain ⟨ω, hω⟩ := exists_unit_orderOf_three (K := K) (by rw [hK]; exact hdvd)
      have hω1 : ω ≠ 1 := fun h => by rw [h, orderOf_one] at hω; omega
      have hω2 : ω ^ 2 ≠ 1 := by
        intro h2
        have := orderOf_dvd_of_pow_eq_one h2
        rw [hω] at this
        omega
      have hr : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
      obtain ⟨b, hbN, hb3, hbreg⟩ := natural_sl3_borel_element ω hω1 hω2 3 hr hπ S
      have hb1 : b ≠ 1 := by
        intro hb1
        apply natural_not_le (StatedSL 3 K) hπ
        intro u hu
        exact hbreg u hu (by rw [hb1]; simp)
      exact ⟨b, hbN, orderOf_eq_prime hb3 hb1⟩
    · have hchar : CharP K 2 := by
        have := Fintype.ofFinite K
        exact charP_of_card_eq_prime_pow (f := n') (by rw [← Nat.card_eq_fintype_card, hK])
      obtain ⟨ω, hω⟩ := exists_unit_orderOf_three (K := K) (by rw [hK]; exact hdvd)
      have hω1 : ω ≠ 1 := fun h => by rw [h, orderOf_one] at hω; omega
      have hr : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
      obtain ⟨b, hbN, hb3, hbreg⟩ := natural_sp4_borel_element ω hω1 3 hr hπ S
      have hb1 : b ≠ 1 := by
        intro hb1
        apply natural_not_le (StatedSp 2 K) hπ
        intro u hu
        exact hbreg u hu (by rw [hb1]; simp)
      exact ⟨b, hbN, orderOf_eq_prime hb3 hb1⟩
  obtain ⟨b, hbN, hord⟩ := key
  have hbQ := hS b hbN
  have hord' : orderOf (⟨(b : MulAut W), hbQ⟩ : ↥Q) = 3 := by
    rw [← Subgroup.orderOf_coe (⟨(b : MulAut W), hbQ⟩ : ↥Q)]
    show orderOf (b : MulAut W) = 3
    rw [Subgroup.orderOf_coe b, hord]
  exact h3 (hord' ▸ orderOf_dvd_natCard _)

end Odd

section NeOne

variable {W : Type} [CommGroup W]

theorem ne_one_of_natural {L : Subgroup (MulAut W)} [Finite ↥L] {V : Subgroup W} {n' c : ℕ} (hc1 : 504 ≤ c)
    (hc2 : c ≠ 720) (hcL : c ∣ Nat.card ↥L)
    (h : BinaryNaturalSL L V (V ⊓ fixV L) 3 n' ∨ BinaryNaturalSp4 L V (V ⊓ fixV L) n') :
    n' ≠ 1 := by
  intro h1
  subst h1
  rcases h with hSL | ⟨K, _, _, hK, π, hπ⟩
  · have h168 := card_le_168_of_natural_sl3 hSL
    have := Nat.le_of_dvd Nat.card_pos hcL
    omega
  · have hdvd : Nat.card ↥L ∣ Nat.card ↥(StatedSp 2 K) := Subgroup.card_dvd_of_surjective hπ.1
    have hcard : Nat.card ↥(StatedSp 2 K) = 720 := by
      rw [LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 2, hK]
      decide
    rw [hcard] at hdvd
    obtain ⟨d, hd⟩ := hcL.trans hdvd
    have hd1 : d < 2 := by
      by_contra hd2
      push Not at hd2
      have : c * 2 ≤ c * d := Nat.mul_le_mul_left c hd2
      omega
    interval_cases d <;> omega

end NeOne

section KsCard

private theorem ordA_two_ge (q : ℕ) (hq : 8 ≤ q) : 721 ≤ ordA 2 q := by
  unfold ordA
  have h : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  rw [h, Finset.prod_pair (by norm_num)]
  have hg : Nat.gcd (2 + 1) (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd (2 + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [Nat.le_div_iff_mul_le hg0]
  have h1 : 8 ^ 3 ≤ q ^ (2 * (2 + 1) / 2) := by
    show 8 ^ 3 ≤ q ^ 3
    exact Nat.pow_le_pow_left hq 3
  have h2 : 63 ≤ q ^ 2 - 1 := by
    have : 64 ≤ q ^ 2 := by nlinarith
    omega
  have h3 : 511 ≤ q ^ 3 - 1 := by
    have : 512 ≤ q ^ 3 := by nlinarith [pow_pos (by omega : 0 < q) 2]
    omega
  calc 721 * Nat.gcd (2 + 1) (q - 1) ≤ 721 * 3 := Nat.mul_le_mul_left _ hg
    _ ≤ 8 ^ 3 * (63 * 511) := by norm_num
    _ ≤ q ^ (2 * (2 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

private theorem ordTwistedA_two_ge (q : ℕ) (hq : 8 ≤ q) : 721 ≤ ordTwistedA 2 q := by
  unfold ordTwistedA
  have h : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  rw [h, Finset.prod_pair (by norm_num)]
  have hg : Nat.gcd (2 + 1) (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd (2 + 1) (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [Nat.le_div_iff_mul_le hg0]
  have h1 : 8 ^ 3 ≤ q ^ (2 * (2 + 1) / 2) := by
    show 8 ^ 3 ≤ q ^ 3
    exact Nat.pow_le_pow_left hq 3
  have h2 : 63 ≤ ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat := by
    have : (64 : ℤ) ≤ (q : ℤ) ^ 2 := by nlinarith
    have : (63 : ℤ) ≤ (q : ℤ) ^ 2 - (-1 : ℤ) ^ 2 := by norm_num; linarith
    omega
  have h3 : 513 ≤ ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat := by
    have : (512 : ℤ) ≤ (q : ℤ) ^ 3 := by nlinarith [sq_nonneg (q : ℤ)]
    have : (513 : ℤ) ≤ (q : ℤ) ^ 3 - (-1 : ℤ) ^ 3 := by norm_num; linarith
    omega
  calc 721 * Nat.gcd (2 + 1) (q + 1) ≤ 721 * 3 := Nat.mul_le_mul_left _ hg
    _ ≤ 8 ^ 3 * (63 * 513) := by norm_num
    _ ≤ q ^ (2 * (2 + 1) / 2) *
        (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat * ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

private theorem ordBC_two_ge (q : ℕ) (hq : 8 ≤ q) : 721 ≤ ordBC 2 q := by
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
  calc 721 * Nat.gcd 2 (q - 1) ≤ 721 * 2 := Nat.mul_le_mul_left _ hg
    _ ≤ 8 ^ 4 * (63 * 4095) := by norm_num
    _ ≤ q ^ (2 * 2) * ((q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

theorem ks_card_facts {Y : Type} [Group Y] {Ks : Subgroup Y} {n : ℕ}
    (hn : 3 ≤ n) (h : Shape15365 n Ks) : 504 ≤ Nat.card ↥Ks ∧ Nat.card ↥Ks ≠ 720 := by
  have hq8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases h with h | h | h | h | h
  ·
    obtain ⟨-, hc⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two h
    rw [hc]
    show 504 ≤ 2 ^ n * (2 ^ (2 * n) - 1) ∧ 2 ^ n * (2 ^ (2 * n) - 1) ≠ 720
    rcases Nat.eq_or_lt_of_le hn with h3 | h4
    · subst h3
      norm_num
    · have h16 : 16 ≤ 2 ^ n := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4
      have h256 : 256 ≤ 2 ^ (2 * n) := by
        calc 256 = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 16 * 255 ≤ 2 ^ n * (2 ^ (2 * n) - 1) := Nat.mul_le_mul h16 (by omega)
      omega
  ·
    obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
    subst hf
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
    have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h64 : 64 ≤ (2 ^ (2 * a + 1)) ^ 2 := by
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left h8 2
    have h7 : 7 ≤ 2 ^ (2 * a + 1) - 1 := by omega
    have h65 : 65 ≤ (2 ^ (2 * a + 1)) ^ 2 + 1 := by omega
    have : 64 * 7 * 65 ≤
        (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h64 h7) h65
    omega
  ·
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.1 rfl
    have := ordTwistedA_two_ge (2 ^ n) hq8
    have h2 : 3 - 1 = 2 := rfl
    rw [h2] at hc
    omega
  ·
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    have := ordA_two_ge (2 ^ n) hq8
    have h2 : 3 - 1 = 2 := rfl
    rw [h2] at hc
    omega
  ·
    have h' : IsPSp4 2 n ↥Ks := by
      simpa [E2.IsSp4Prime, show n ≠ 1 by omega] using h
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h').2.2.1 rfl
    have := ordBC_two_ge (2 ^ n) hq8
    omega

end KsCard

section Sigma

variable {Γ : Type} [Group Γ]

private noncomputable def starMapM8 (M' H K : Subgroup Γ) (hKH : K ≤ H) :
    ↥K →* ↥(E2.star M' H K) :=
  (((QuotientGroup.mk' ((kerIn M' H).subgroupOf H)).comp (Subgroup.inclusion hKH)).codRestrict
    (E2.star M' H K) fun k => ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)

private theorem starMapM8_surjective (M' H K : Subgroup Γ) (hKH : K ≤ H) :
    Function.Surjective (starMapM8 M' H K hKH) := by
  rintro ⟨y, x, hx, rfl⟩
  refine ⟨⟨(x : Γ), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
  apply Subtype.ext
  rfl

private theorem starMapM8_eq_one_iff (M' H K : Subgroup Γ) (hKH : K ≤ H) (k : ↥K) :
    starMapM8 M' H K hKH k = 1 ↔ Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).mp this
  · intro h
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr h

theorem card_star_dvd_of_kernel {M' H K : Subgroup Γ} (hKH : K ≤ H) {L : Type} [Group L]
    (ρ : ↥K →* L) (hρ : Function.Surjective ρ)
    (hker : ∀ k : ↥K, ρ k = 1 → Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H) :
    Nat.card ↥(E2.star M' H K) ∣ Nat.card L := by
  have hq := starMapM8_surjective M' H K hKH
  have hkq : ρ.ker ≤ (starMapM8 M' H K hKH).ker := by
    intro k hk
    rw [MonoidHom.mem_ker, starMapM8_eq_one_iff]
    exact hker k hk
  let σ : L →* ↥(E2.star M' H K) :=
    ρ.liftOfRightInverse (Function.surjInv hρ) (Function.rightInverse_surjInv hρ)
      ⟨starMapM8 M' H K hKH, hkq⟩
  have hσρ : ∀ k, σ (ρ k) = starMapM8 M' H K hKH k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨_, hkq⟩ k
  have hσs : Function.Surjective σ := by
    intro y
    obtain ⟨k, rfl⟩ := hq y
    exact ⟨ρ k, hσρ k⟩
  exact Subgroup.card_dvd_of_surjective hσs

end Sigma

section Big

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem twistFieldBig_of (hF : HypF918 T V L V₁ Vp H K)
    (M I : Subgroup G) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (hkerchar : ∀ x : G, x ∈ kerIn (H ⊓ M) H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)))
    (h3 : IsThreePrimeGroup (M ⊓ H)) {n : ℕ} (hn3 : 3 ≤ n)
    (hKs : Shape15365 n (E2.star (H ⊓ M) H K)) : TwistFieldBig hF I hIU := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hFI := factElem hF hIU
  obtain ⟨S, hS⟩ := exists_sylow_borel_acting_two hF M I hIU hnt hkerchar hB
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  have hfin : Finite ↥(autIH V₁ I H K) := Finite.of_surjective _ (toAutI_surjective hF I)
  set φ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  set Q : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure I H))) :=
    ((H ⊓ M).subgroupOf H).map φ with hQ
  have hSQ : ∀ b ∈ Subgroup.normalizer
      ((S : Subgroup ↥(autIH V₁ I H K)) : Set ↥(autIH V₁ I H K)),
      (b : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈ Q := by
    intro b hb
    obtain ⟨k, hkM, hkb⟩ := hS b hb
    rw [← hkb, toAutI_coe]
    exact ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr ⟨hKH k.2, hkM⟩, rfl⟩
  have h3Q : ¬ 3 ∣ Nat.card ↥Q := by
    intro hdvd
    apply h3
    have h1 : Nat.card ↥Q ∣ Nat.card ↥((H ⊓ M).subgroupOf H) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥((H ⊓ M).subgroupOf H) = Nat.card ↥(H ⊓ M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [inf_comm M H]
    rw [← h2]
    exact hdvd.trans h1
  have hcard : Nat.card ↥(E2.star (H ⊓ M) H K) ∣ Nat.card ↥(autIH V₁ I H K) :=
    card_star_dvd_of_kernel hKH (toAutI hF I) (toAutI_surjective hF I)
      (toAutI_ker_le_kerIn hF hIU hne hkerchar)
  obtain ⟨hc1, hc2⟩ := ks_card_facts hn3 hKs
  intro V'
  have key : ∀ n' : ℕ, (BinaryNaturalSL (autIH V₁ I H K) V' (V' ⊓ fixV (autIH V₁ I H K)) 3 n' ∨
      BinaryNaturalSp4 (autIH V₁ I H K) V' (V' ⊓ fixV (autIH V₁ I H K)) n') → 3 ≤ n' := by
    intro n' h
    have h1 := ne_one_of_natural hc1 hc2 hcard h
    have h2 := not_even_of_natural S hSQ h3Q h
    rw [Nat.not_even_iff_odd, Nat.odd_iff] at h2
    omega
  exact ⟨fun n' h => key n' (Or.inl h), fun n' h => key n' (Or.inr h)⟩

end Big

section Final

attribute [local instance] commGroupOfFact

end Final

end CFSG.Quasithin
