module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R1KBase
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open CFSG.Assembly (InCatalog)
open CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]
variable {b t c : G} {J : Subgroup G}

theorem nor_sup_decomp {x : G} (hx : orderOf x = 3) {Z : Subgroup G} [hZ : Z.Normal]
    (hZc : Nat.Coprime 3 (Nat.card Z)) {g : G}
    (hg : g ∈ Nor (Subgroup.zpowers x ⊔ Z)) :
    ∃ z ∈ Z, ∃ n ∈ Nor (Subgroup.zpowers x), g = z * n := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    omega
  set E : Subgroup G := Subgroup.zpowers x ⊔ Z with hE
  have hxE : x ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hxZ : Subgroup.zpowers x ⊓ Z = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have hd1 : Nat.card ↥(Subgroup.zpowers x ⊓ Z) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers x ⊓ Z ≤ Subgroup.zpowers x)
      rwa [hcardx] at this
    have hd2 : Nat.card ↥(Subgroup.zpowers x ⊓ Z) ∣ Nat.card Z :=
      Subgroup.card_dvd_of_le inf_le_right
    exact Nat.eq_one_of_dvd_coprimes hZc hd1 hd2
  have hcardE : Nat.card E = 3 * Nat.card Z := by
    have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (Z : Set G) :=
      Subgroup.le_normalizer_of_normal
    have := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hle
    rw [hxZ, hcardx, Subgroup.card_bot] at this
    simpa using this
  have hsyl : IsSylowOf 3 (Subgroup.zpowers x) E := by
    refine L14.isSylowOf_of_card le_sup_left ?_
    rw [hcardx, hcardE]
    have hz0 : Nat.card Z ≠ 0 := Nat.card_pos.ne'
    have : (3 * Nat.card Z).factorization 3 = 1 := by
      rw [Nat.factorization_mul (by norm_num) hz0, Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_three,
        Nat.factorization_eq_zero_of_not_dvd
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hZc)]
    rw [this]
    norm_num
  have hxg : g * x * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hg x).mp hxE
  have hle : Subgroup.zpowers (g * x * g⁻¹) ≤ E := Subgroup.zpowers_le.mpr hxg
  have hp3 : IsPGroup 3 (Subgroup.zpowers (g * x * g⁻¹)) := by
    refine isPGroup_zpowers_of_pow_three ?_
    calc (g * x * g⁻¹) ^ 3 = g * x ^ 3 * g⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hx3]; group
  obtain ⟨k, hkE, hk⟩ := L14.exists_conj_le_sylowOf hsyl hle hp3
  have hkgx : (k * g) * x * (k * g)⁻¹ ∈ Subgroup.zpowers x := by
    have := hk (g * x * g⁻¹) (Subgroup.mem_zpowers _)
    simpa [mul_assoc] using this
  have hkgN : k * g ∈ Nor (Subgroup.zpowers x) := mem_Nor_zpowers_of_conj hkgx
  have hkinv : k⁻¹ ∈ E := E.inv_mem hkE
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hkinv
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hg' : g = (x ^ i * z) * (k * g) := by rw [hyz]; group
  refine ⟨x ^ i * z * (x ^ i)⁻¹, hZ.conj_mem z hz (x ^ i), x ^ i * (k * g), ?_, ?_⟩
  · exact (Nor (Subgroup.zpowers x)).mul_mem (Subgroup.zpow_mem _ (Subgroup.le_normalizer
      (Subgroup.mem_zpowers x)) i) hkgN
  · exact hg'.trans (by group)

theorem conj_mem_inv {Z : Subgroup G} [hZ : Z.Normal] {z : G} (hz : z ∈ Z) (g : G) :
    g⁻¹ * z * g ∈ Z := by
  simpa using hZ.conj_mem z hz g⁻¹

theorem not_mem_of_coprime {Z : Subgroup G} (hZc : Nat.Coprime 3 (Nat.card Z)) {x : G}
    (hx : orderOf x = 3) : x ∉ Z := by
  intro hxZ
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hx1 : x = 1 := eq_one_of_mem_coprime_of_pow_three hZc hxZ hx3
  rw [hx1, orderOf_one] at hx
  omega

theorem not_dvd_of_two_power {Z R : Subgroup G} (hZc : Nat.Coprime 3 (Nat.card Z))
    (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ (2 ^ k) ∈ Z) : ¬ 3 ∣ Nat.card R := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hd
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 3 hd
  have hrG : orderOf (r : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hr
  obtain ⟨k, hk⟩ := hR2 (r : G) r.2
  have hr3 : (r : G) ^ 3 = 1 := by
    rw [← hrG]
    exact pow_orderOf_eq_one _
  have h4 : ∀ m : ℕ, (r : G) ^ (4 ^ m) = r := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_mul, ih]
      calc (r : G) ^ 4 = (r : G) ^ 3 * (r : G) := by rw [pow_succ]
        _ = (r : G) := by rw [hr3, one_mul]
  have hrZ : (r : G) ∈ Z := by
    have e2 : (2 : ℕ) ^ k * 2 ^ k = 4 ^ k := by
      rw [← mul_pow]
      norm_num
    have e : ((r : G) ^ (2 ^ k)) ^ (2 ^ k) = (r : G) := by
      rw [← pow_mul, e2, h4 k]
    rw [← e]
    exact Z.pow_mem hk _
  exact not_mem_of_coprime hZc hrG hrZ

theorem FS79Hyp1.no2_Z (h : FS79Hyp1 b t c J) {Z : Subgroup G}
    (hZc : Nat.Coprime 3 (Nat.card Z)) {R : Subgroup G}
    (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ (2 ^ k) ∈ Z) (hb : b ∈ Nor R) (hc : c ∈ Nor R) : R ≤ Z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR3 := not_dvd_of_two_power hZc hR2
  have hBR : Subgroup.closure ({b, c} : Set G) ≤ Nor R := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hb
    · exact hc
  obtain ⟨R₂, hR₂syl, -, hAR⟩ := CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime
    (q := 3) (r := 2) (A := Subgroup.closure ({b, c} : Set G)) (K := R) (P := ⊥)
    Nat.prime_three Nat.prime_two h.isPGroup_B hBR hR3 bot_le IsPGroup.of_bot
    Subgroup.le_normalizer_of_normal
  have hR₂2 : IsPGroup 2 R₂ := CFSG.ABGLocalTools.IsSylowOf.isPGroup hR₂syl
  have hR₂bot : R₂ = ⊥ := h.no_two R₂ hR₂2 hAR
  have hndvd : ¬ 2 ∣ R₂.relIndex R := (CFSG.ABGLocalTools.isSylowOf_iff.mp hR₂syl).2.2
  rw [hR₂bot, Subgroup.relIndex_bot_left] at hndvd
  intro r hr
  obtain ⟨k, hk⟩ := hR2 r hr
  have hord : orderOf r ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hr
  have hoddord : Odd (orderOf r) :=
    (Nat.not_even_iff_odd.mp (fun he => hndvd (even_iff_two_dvd.mp he))).of_dvd_nat hord
  have hcop : Nat.Coprime (2 ^ k) (orderOf r) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hoddord)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Z.pow_mem hk m

theorem FS79Hyp1.weak_Z (h : FS79Hyp1 b t c J) {Z : Subgroup G} [hZ : Z.Normal]
    (hZc : Nat.Coprime 3 (Nat.card Z)) {h' : G}
    (hh : ∀ k : ℤ, h' * b ^ k * h'⁻¹ ∈ Nor (Subgroup.zpowers b ⊔ Z)) :
    h' * b * h'⁻¹ ∈ Subgroup.zpowers b ⊔ Z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E : Subgroup G := Subgroup.zpowers b ⊔ Z with hE
  have hbE : b ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hb' : h' * b * h'⁻¹ ∈ Nor E := by simpa using hh 1
  set b' : G := h' * b * h'⁻¹ with hb'def
  have hb'3 : b' ^ 3 = 1 := by
    rw [hb'def, conj_pow, h.b_pow_three]
    group
  set F : Subgroup G := E ⊔ Subgroup.zpowers b' with hF
  have hFN : F ≤ Nor E := sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hb')
  have hbF : b ∈ F := Subgroup.mem_sup_left hbE
  have hb'F : b' ∈ F := Subgroup.mem_sup_right (Subgroup.mem_zpowers b')
  have hbp : IsPGroup 3 ((Subgroup.zpowers b).subgroupOf F) :=
    (isPGroup_zpowers_of_pow_three h.b_pow_three).of_equiv
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hbF)).symm
  obtain ⟨S, hS⟩ := hbp.exists_le_sylow
  set S₀ : Subgroup G := (S : Subgroup ↥F).map F.subtype with hS₀
  have hS₀syl : IsSylowOf 3 S₀ F := by
    have : CFSG.ABGLocalTools.IsSylowOf 3 S₀ F := ⟨S, rfl⟩
    exact abgSylow_to_ff79 this
  have hS₀p : IsPGroup 3 S₀ := hS₀syl.2.1
  have hbS₀ : b ∈ S₀ := ⟨⟨b, hbF⟩, hS (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers b)), rfl⟩
  have hb'p : IsPGroup 3 (Subgroup.zpowers b') := isPGroup_zpowers_of_pow_three hb'3
  obtain ⟨k, hkF, hk⟩ := L14.exists_conj_le_sylowOf hS₀syl (Subgroup.zpowers_le.mpr hb'F) hb'p
  have hkb' : k * b' * k⁻¹ ∈ S₀ := hk b' (Subgroup.mem_zpowers b')
  have hkb'' : (k * h') * b * (k * h')⁻¹ ∈ S₀ := by simpa [hb'def, mul_assoc] using hkb'
  have hmem := conj_mem_zpowers_of_pgroup_gen h.ord_b h.weak hS₀p hbS₀ hkb''
  have hkN : k⁻¹ ∈ Nor E := (Nor E).inv_mem (hFN hkF)
  have hE1 : (k * h') * b * (k * h')⁻¹ ∈ E := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hi]
    exact E.zpow_mem hbE i
  have := (Subgroup.mem_normalizer_iff.mp hkN _).mp hE1
  have e : k⁻¹ * ((k * h') * b * (k * h')⁻¹) * k⁻¹⁻¹ = b' := by
    rw [hb'def]
    group
  rw [e] at this
  exact this

theorem Nor_le_Nor_sup_of_normal {A Z : Subgroup G} [hZ : Z.Normal] :
    Nor A ≤ Nor (A ⊔ Z) := fun g hg =>
  Subgroup.inf_normalizer_le_normalizer_sup A Z
    ⟨hg, Subgroup.le_normalizer_of_normal (H := Z) (K := ⊤) (Subgroup.mem_top g)⟩

theorem FS79Hyp1.qdata_top (h : FS79Hyp1 b t c J) {Z : Subgroup G} [hZ : Z.Normal]
    (hZc : Nat.Coprime 3 (Nat.card Z)) : QData (⊤ : Subgroup G) Z b t c J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbZ : b ∉ Z := not_mem_of_coprime hZc h.ord_b
  refine ⟨le_top, fun g _ z hz => hZ.conj_mem z hz g, Subgroup.mem_top _, Subgroup.mem_top _,
    Subgroup.mem_top _, le_top, h.c_mem, h.b_pow_three, hbZ, h.t_sq, ?_, h.inv_b,
    h.c_pow_three, not_mem_of_coprime hZc h.ord_c, h.J_perm, ?_,
    fun j hj => Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b hj),
    fun j hj => Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t hj), ?_, ?_, ?_,
    fun R _ _ hR2 hb hc => h.no2_Z hZc hR2 hb hc,
    fun h' _ hh => h.weak_Z hZc hh⟩
  ·
    intro htZ
    apply hbZ
    have h1 : t * (b * t⁻¹ * b⁻¹) ∈ Z :=
      Z.mul_mem htZ (hZ.conj_mem t⁻¹ (Z.inv_mem htZ) b)
    have e : t * (b * t⁻¹ * b⁻¹) = b := by
      have h3 : t * b * t⁻¹ = b⁻¹ := h.inv_b
      calc t * (b * t⁻¹ * b⁻¹) = (t * b * t⁻¹) * b⁻¹ := by group
        _ = b⁻¹ * b⁻¹ := by rw [h3]
        _ = b := by
          have hb3 := h.b_pow_three
          calc b⁻¹ * b⁻¹ = b⁻¹ * b⁻¹ * b ^ 3 := by rw [hb3, mul_one]
            _ = b := by group
    rw [← e]
    exact h1
  ·
    refine h.eq_bot_of_normal_in_J (inf_le_left : J ⊓ Z ≤ J) ?_ ?_
    · intro j hj x hx
      exact ⟨J.mul_mem (J.mul_mem hj hx.1) (J.inv_mem hj), hZ.conj_mem x hx.2 j⟩
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hZc
  ·
    intro g hg j hj
    obtain ⟨z₀, hz₀, n, hn, rfl⟩ := nor_sup_decomp h.ord_b hZc hg.2
    have hj' : n * j * n⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (h.N_le_NJ hn) j).mp hj
    refine ⟨n * j * n⁻¹, hj', (n * j * n⁻¹)⁻¹ * z₀ * (n * j * n⁻¹) * z₀⁻¹, ?_, ?_⟩
    · exact Z.mul_mem (conj_mem_inv hz₀ _) (Z.inv_mem hz₀)
    · group
  ·
    refine ⟨Opp 3 (Nor (Subgroup.zpowers b)), ?_, L14.Opp_coprime 3 _, ?_, ?_⟩
    · exact fun k hk => ⟨Subgroup.mem_top k,
        Nor_le_Nor_sup_of_normal (L14.Opp_le 3 _ hk)⟩
    · intro g hg w hw
      obtain ⟨z₀, hz₀, n, hn, rfl⟩ := nor_sup_decomp h.ord_b hZc hg.2
      refine ⟨n * w * n⁻¹, L14.Opp_conj_mem hn hw, (n * w * n⁻¹)⁻¹ * z₀ * (n * w * n⁻¹) * z₀⁻¹,
        Z.mul_mem (conj_mem_inv hz₀ _) (Z.inv_mem hz₀), ?_⟩
      group
    · intro g hg
      obtain ⟨z₀, hz₀, n, hn, rfl⟩ := nor_sup_decomp h.ord_b hZc hg.2
      obtain ⟨k, hk, y, hy, j, hj, rfl⟩ := h.nor_decomp hn
      refine ⟨k, hk, y, hy, j, hj, (k * y * j)⁻¹ * z₀ * (k * y * j), conj_mem_inv hz₀ _, ?_⟩
      group
  ·
    refine ⟨Opp 3 (Nor (Subgroup.zpowers c)), ?_, L14.Opp_coprime 3 _, ?_, ?_⟩
    · exact fun k hk => ⟨Subgroup.mem_top k,
        Nor_le_Nor_sup_of_normal (L14.Opp_le 3 _ hk)⟩
    · intro g hg w hw
      obtain ⟨z₀, hz₀, n, hn, rfl⟩ := nor_sup_decomp h.ord_c hZc hg.2
      refine ⟨n * w * n⁻¹, L14.Opp_conj_mem hn hw, (n * w * n⁻¹)⁻¹ * z₀ * (n * w * n⁻¹) * z₀⁻¹,
        Z.mul_mem (conj_mem_inv hz₀ _) (Z.inv_mem hz₀), ?_⟩
      group
    · intro g hg
      obtain ⟨z₀, hz₀, n₀, hn₀, rfl⟩ := nor_sup_decomp h.ord_c hZc hg.2
      have hmem : n₀ ∈ setMul (Opp 3 (Nor (Subgroup.zpowers c)))
          (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers c)) := by
        rw [h.N_c]
        exact hn₀
      obtain ⟨q, hq, n₁, hn₁, rfl⟩ := hmem
      refine ⟨q, hq, n₁, ⟨⟨Subgroup.mem_top _, Nor_le_Nor_sup_of_normal hn₁.2⟩,
        Nor_le_Nor_sup_of_normal hn₁.1⟩, (q * n₁)⁻¹ * z₀ * (q * n₁), conj_mem_inv hz₀ _, ?_⟩
      group

end CFSG.RankThree.PartTwo.Sec21.FF81
