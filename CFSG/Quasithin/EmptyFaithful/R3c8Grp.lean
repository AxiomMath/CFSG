module

public import CFSG.Quasithin.EmptyFaithful.SBc2N34

public section

namespace CFSG.Quasithin.R3c8

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Perm

theorem perm3_conj : ∀ τ σ : Equiv.Perm (Fin 3), τ ≠ 1 → τ * τ = 1 → σ ≠ 1 → σ * σ * σ = 1 →
    τ * σ * τ⁻¹ = σ⁻¹ := by decide

theorem perm3_sq_one {τ : Equiv.Perm (Fin 3)} {k : ℕ} (hτ : τ ^ 2 ^ k = 1) : τ * τ = 1 := by
  have h1 : orderOf τ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hτ
  have h2 : orderOf τ ∣ 6 := by
    have := orderOf_dvd_natCard τ
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using this
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj1 : j ≤ 1 := by
    by_contra hj2
    have h4 : 4 ∣ 2 ^ j := by
      have : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      simpa using this
    have : 4 ∣ 6 := h4.trans (hj' ▸ h2)
    omega
  have : orderOf τ ∣ 2 := by
    rw [hj']
    interval_cases j <;> simp
  rw [← sq]
  exact orderOf_dvd_iff_pow_eq_one.mp this

end Perm

section Quot

theorem mem_of_commutator_data {H : Type} [Group H] (N : Subgroup H) [N.Normal]
    {s y r : H} (hs : s ∈ N) (hy3 : y ^ 3 = 1) {k : ℕ} (hr : r ^ 2 ^ k = 1)
    (hrel : s * y * s⁻¹ = r * y⁻¹) : y ∈ N := by
  let q := QuotientGroup.mk' N
  have h1 : q s = 1 := (QuotientGroup.eq_one_iff s).mpr hs
  have h2 : q y = q r * (q y)⁻¹ := by
    have := congrArg q hrel
    rw [map_mul, map_mul, map_inv, h1, one_mul, inv_one, mul_one, map_mul, map_inv] at this
    exact this
  have h3 : q y * q y = q r := by
    have : q y * q y = q r * (q y)⁻¹ * q y := by rw [← h2]
    simpa using this
  have h4 : (q y) ^ 2 ^ (k + 1) = 1 := by
    have : (q y) ^ 2 ^ (k + 1) = (q r) ^ 2 ^ k := by
      rw [pow_succ, mul_comm, pow_mul, sq, h3]
    rw [this, ← map_pow, hr, map_one]
  have h5 : (q y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have h6 : (q y) ^ Nat.gcd (2 ^ (k + 1)) 3 = 1 := pow_gcd_eq_one.mpr ⟨h4, h5⟩
  have h7 : Nat.gcd (2 ^ (k + 1)) 3 = 1 := by
    apply Nat.Coprime.pow_left
    norm_num
  rw [h7, pow_one] at h6
  exact (QuotientGroup.eq_one_iff y).mp h6

end Quot

section Out

variable {G : Type} [Group G] [Finite G]

theorem normal_sup_centralizer (L : Subgroup G) :
    ((L ⊔ Subgroup.centralizer (L : Set G)).subgroupOf (Subgroup.normalizer (L : Set G))).Normal := by
  classical
  have hle : L ⊔ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr fun g hg => ?_
  have h1 : g ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    B2F.le_normalizer_centralizer (le_refl _) hg
  exact SBc2.mem_normalizer_sup hg h1

theorem inf_le_pCore_of_s3 {X S L R Yp : Subgroup G}
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hSX : S ≤ X) (hYX : Yp ≤ X)
    (hS2 : IsPGroup 2 S) (hR2 : IsPGroup 2 R)
    (φ : ↥X →* Equiv.Perm (Fin 3)) (hker : φ.ker = R.subgroupOf X)
    {y : G} (hyY : y ∈ Yp) (hy3 : orderOf y = 3)
    (hyL : y ∉ L ⊔ Subgroup.centralizer (L : Set G)) : S ⊓ L ≤ R := by
  intro s hs
  by_contra hsR
  obtain ⟨hsS, hsL⟩ := hs
  let sX : ↥X := ⟨s, hSX hsS⟩
  let yX : ↥X := ⟨y, hYX hyY⟩
  have hφs : φ sX ≠ 1 := by
    intro h
    apply hsR
    have h' : sX ∈ φ.ker := h
    rw [hker, Subgroup.mem_subgroupOf] at h'
    exact h'
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hyR : y ∉ R := by
    intro hyR
    obtain ⟨k, hk⟩ := hR2 ⟨y, hyR⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hy3] at this
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega
  have hφy : φ yX ≠ 1 := by
    intro h
    apply hyR
    have h' : yX ∈ φ.ker := h
    rw [hker, Subgroup.mem_subgroupOf] at h'
    exact h'
  have hφs2 : φ sX * φ sX = 1 := by
    obtain ⟨k, hk⟩ := hS2 ⟨s, hsS⟩
    have hk' : sX ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simpa [sX] using congrArg Subtype.val hk
    exact perm3_sq_one (by rw [← map_pow, hk', map_one])
  have hφy3 : φ yX * φ yX * φ yX = 1 := by
    rw [← map_mul, ← map_mul]
    have : yX * yX * yX = 1 := by
      apply Subtype.ext
      simp only [yX, Subgroup.coe_mul, Subgroup.coe_one]
      rw [← pow_three', hy3']
    rw [this, map_one]
  have hconj := perm3_conj (φ sX) (φ yX) hφs hφs2 hφy hφy3
  set r : G := s * y * s⁻¹ * y with hr
  have hrX : r ∈ X := X.mul_mem (X.mul_mem (X.mul_mem (hSX hsS) (hYX hyY)) (X.inv_mem (hSX hsS))) (hYX hyY)
  have hrR : r ∈ R := by
    have h1 : φ ⟨r, hrX⟩ = 1 := by
      have e : (⟨r, hrX⟩ : ↥X) = sX * yX * sX⁻¹ * yX := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, hconj, inv_mul_cancel]
    have h' : (⟨r, hrX⟩ : ↥X) ∈ φ.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at h'
    exact h'
  obtain ⟨k, hk⟩ := hR2 ⟨r, hrR⟩
  have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have := normal_sup_centralizer L
  let N := (L ⊔ Subgroup.centralizer (L : Set G)).subgroupOf (Subgroup.normalizer (L : Set G))
  let H := Subgroup.normalizer (L : Set G)
  have hsH : s ∈ H := hXL (hSX hsS)
  have hyH : y ∈ H := hXL (hYX hyY)
  have hrH : r ∈ H := hXL hrX
  have hsN : (⟨s, hsH⟩ : ↥H) ∈ N := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hsL)
  have hrel : (⟨s, hsH⟩ : ↥H) * ⟨y, hyH⟩ * (⟨s, hsH⟩ : ↥H)⁻¹ = ⟨r, hrH⟩ * (⟨y, hyH⟩ : ↥H)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hr]
    group
  have hy3H : (⟨y, hyH⟩ : ↥H) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hy3'
  have hrk : (⟨r, hrH⟩ : ↥H) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa using hk'
  have hmem := mem_of_commutator_data N hsN hy3H hrk hrel
  exact hyL (Subgroup.mem_subgroupOf.mp hmem)


end Out

section Syl3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_card_three_mul_two_pow {Y L : Subgroup G} (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    {a : ℕ} (hcard : Nat.card ↥Y = 3 * 2 ^ a) {b y : G} (hbY : b ∈ Y) (hbL : b ∈ L)
    (hb3 : orderOf b = 3) (hyY : y ∈ Y) (hy3 : y ^ 3 = 1) : y ∈ L := by
  have hnorm : Y ≤ Subgroup.normalizer ((Y ⊓ L : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hYL hg⟩
  have hN : ((Y ⊓ L).subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hnorm
  let N := (Y ⊓ L).subgroupOf Y
  have hbN : (⟨b, hbY⟩ : ↥Y) ∈ N := Subgroup.mem_subgroupOf.mpr ⟨hbY, hbL⟩
  have h3N : 3 ∣ Nat.card ↥N := by
    have : orderOf (⟨(⟨b, hbY⟩ : ↥Y), hbN⟩ : ↥N) = 3 := by
      rw [← hb3, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    rw [← this]
    exact orderOf_dvd_natCard _
  obtain ⟨m, hm⟩ := h3N
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hcard, hm] at hmul
  have hq : Nat.card (↥Y ⧸ N) ∣ 2 ^ a := by
    refine ⟨m, ?_⟩
    have : 3 * 2 ^ a = 3 * (Nat.card (↥Y ⧸ N) * m) := by rw [hmul]; ring
    omega
  let q := QuotientGroup.mk' N
  have h1 : (q ⟨y, hyY⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyY⟩ : ↥Y) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have h2 : (q ⟨y, hyY⟩) ^ 2 ^ a = 1 := by
    have h := pow_card_eq_one' (G := ↥Y ⧸ N) (x := q ⟨y, hyY⟩)
    obtain ⟨c, hc⟩ := hq
    rw [hc, pow_mul, h, one_pow]
  have h3 : (q ⟨y, hyY⟩) ^ Nat.gcd (2 ^ a) 3 = 1 := pow_gcd_eq_one.mpr ⟨h2, h1⟩
  have h4 : Nat.gcd (2 ^ a) 3 = 1 := by
    apply Nat.Coprime.pow_left
    norm_num
  rw [h4, pow_one] at h3
  have h5 : (⟨y, hyY⟩ : ↥Y) ∈ N := (QuotientGroup.eq_one_iff _).mp h3
  exact (Subgroup.mem_subgroupOf.mp h5).2

end Syl3

section Act

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_odd {B Q W : Subgroup G} (hBW : B ≤ Subgroup.normalizer (W : Set G))
    (hW : Nat.card ↥W = 4) (hQB : IsSylowTwoOf Q B) (hQW : Q ≤ Subgroup.centralizer (W : Set G))
    (h3 : ¬ 3 ∣ Nat.card ↥B) : B ≤ Subgroup.centralizer (W : Set G) := by
  let ψ : ↥B →* Equiv.Perm ↥W :=
    (MulAut.toPerm ↥W).comp ((Subgroup.normalizerMonoidHom W).comp (Subgroup.inclusion hBW))
  have hψ : ∀ (b : ↥B) (w : ↥W), ((ψ b w : ↥W) : G) = (b : G) * (w : G) * (b : G)⁻¹ := fun b w => rfl
  have hker : Q.subgroupOf B ≤ ψ.ker := by
    intro b hb
    rw [MonoidHom.mem_ker]
    ext w
    rw [hψ]
    have hbQ : (b : G) ∈ Q := Subgroup.mem_subgroupOf.mp hb
    have := Subgroup.mem_centralizer_iff.mp (hQW hbQ) (w : G) w.2
    show (b : G) * (w : G) * (b : G)⁻¹ = (w : G)
    rw [← this]
    group
  have hdvd1 : ψ.ker.index ∣ Q.relIndex B := Subgroup.index_dvd_of_le hker
  have hodd : ¬ 2 ∣ ψ.ker.index := fun h => hQB.2.2 (h.trans hdvd1)
  have hdvd2 : ψ.ker.index ∣ 24 := by
    rw [Subgroup.index_ker]
    have h1 := Subgroup.card_subgroup_dvd_card ψ.range
    have h2 : Nat.card (Equiv.Perm ↥W) = 24 := by
      classical
      have : Fintype ↥W := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hW]
      rfl
    rwa [h2] at h1
  have hdvd3 : ψ.ker.index ∣ 3 := by
    have hcop : Nat.Coprime ψ.ker.index 8 := by
      have : Nat.Coprime ψ.ker.index 2 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd))
      simpa using Nat.Coprime.pow_right 3 this
    exact hcop.dvd_of_dvd_mul_left (by simpa using hdvd2)
  have hdvd4 : ψ.ker.index ∣ Nat.card ↥B := Subgroup.index_dvd_card _
  have h1 : ψ.ker.index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact h
    · exact absurd (h ▸ hdvd4) h3
  have htop : ψ.ker = ⊤ := Subgroup.index_eq_one.mp h1
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hb1 : ψ ⟨b, hb⟩ = 1 := by
    have : (⟨b, hb⟩ : ↥B) ∈ ψ.ker := by rw [htop]; exact Subgroup.mem_top _
    exact this
  have := congrArg (fun p : Equiv.Perm ↥W => ((p ⟨w, hw⟩ : ↥W) : G)) hb1
  simp only [hψ] at this
  have e : b * w * b⁻¹ = w := this
  calc w * b = (b * w * b⁻¹) * b := by rw [e]
    _ = b * w := by group

end Act

end CFSG.Quasithin.R3c8
