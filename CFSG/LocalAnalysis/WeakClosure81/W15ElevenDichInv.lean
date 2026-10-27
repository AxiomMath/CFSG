module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenFree
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma b15_W15ElevenDichInv_zpow_eq_one_or_self {v : G} (hv : v * v = 1) (n : ℤ) :
    v ^ n = 1 ∨ v ^ n = v := by
  have hv2 : v ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hv]
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul, hv2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, hv2, one_zpow, one_mul, zpow_one]

private lemma b15_W15ElevenDichInv_mul_comm_of_mem {I : Subgroup G} (hI : IsElemAbelian 2 I)
    {x y : G} (hx : x ∈ I) (hy : y ∈ I) : x * y = y * x := by
  haveI : IsMulCommutative I := hI.1
  simpa using congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : I) (⟨y, hy⟩ : I))

private lemma b15_W15ElevenDichInv_inv_eq_of_mem {I : Subgroup G} (hI : IsElemAbelian 2 I)
    {x : G} (hx : x ∈ I) : x⁻¹ = x := by
  have h := hI.2 x hx
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_right h

theorem commutator_zpowers_le_inf_centralizer_of_mul_self {I : Subgroup G}
    (hI : IsElemAbelian 2 I) {a : G} (haN : a ∈ normalizer (I : Set G)) (ha : a * a = 1) :
    ⁅I, zpowers a⁆ ≤ I ⊓ centralizer ({a} : Set G) := by
  classical
  rw [Subgroup.commutator_le]
  intro i hi g hg
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rcases b15_W15ElevenDichInv_zpow_eq_one_or_self ha n with hn | hn
  · rw [hn]
    simp
  · rw [hn]
    let j : G := a * i * a⁻¹
    have hj_eq : j = a * i * a⁻¹ := rfl
    have hj : j ∈ I := (Subgroup.mem_normalizer_iff.mp haN i).mp hi
    have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hji : j * i = i * j := b15_W15ElevenDichInv_mul_comm_of_mem hI hj hi
    have hija : a * j * a⁻¹ = i := by
      rw [hj_eq, ha_inv]
      calc a * (a * i * a) * a = (a * a) * i * (a * a) := by group
        _ = i := by rw [ha, one_mul, mul_one]
    have hcomm : (i * j) * a = a * (i * j) := by
      have h1 : a * (i * j) * a⁻¹ = i * j := by
        calc a * (i * j) * a⁻¹
            = (a * i * a⁻¹) * (a * j * a⁻¹) := by group
          _ = j * i := by rw [hija]
          _ = i * j := hji
      rw [ha_inv] at h1
      calc (i * j) * a = (a * a) * (i * j) * a := by rw [ha, one_mul]
        _ = a * (a * (i * j) * a) := by group
        _ = a * (i * j) := by rw [h1]
    have hcommut : ⁅i, a⁆ = i * j := by
      rw [commutatorElement_def]
      simp only [hj_eq]
      rw [b15_W15ElevenDichInv_inv_eq_of_mem hI hi, ha_inv]
      group
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hcommut]
      exact Subgroup.mul_mem _ hi hj
    · rw [hcommut]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm

theorem card_inf_centralizer_mul_card_commutator_zpowers {I : Subgroup G}
    (hI : IsElemAbelian 2 I) {a : G} (haN : a ∈ normalizer (I : Set G)) (ha : a * a = 1) :
    Nat.card ↥(I ⊓ centralizer ({a} : Set G)) * Nat.card ↥⁅I, zpowers a⁆ = Nat.card ↥I := by
  classical
  haveI : IsMulCommutative I := hI.1
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  let c : I →* I :=
    ((MulAut.conj a).toMonoidHom.comp I.subtype).codRestrict I
      (fun x => (Subgroup.mem_normalizer_iff.mp haN x).mp x.2)
  have hc_coe : ∀ x : I, ((c x : I) : G) = a * (x : G) * a⁻¹ := fun _ => rfl
  let φ : I →* I :=
    { toFun := fun i => i * c i
      map_one' := by
        show (1 : I) * c 1 = 1
        rw [map_one, mul_one]
      map_mul' := fun x y => by
        show (x * y) * c (x * y) = (x * c x) * (y * c y)
        rw [map_mul]
        calc (x * y) * (c x * c y) = x * (y * c x) * c y := by group
          _ = x * (c x * y) * c y := by rw [mul_comm' y (c x)]
          _ = (x * c x) * (y * c y) := by group }
  have hφ_coe : ∀ i : I, ((φ i : I) : G) = (i : G) * (a * (i : G) * a⁻¹) := fun _ => rfl
  have hker_map : (φ.ker).map I.subtype = I ⊓ centralizer ({a} : Set G) := by
    apply le_antisymm
    · rintro g ⟨i, hi, hgi⟩
      rw [← hgi]
      have hphi : φ i = 1 := MonoidHom.mem_ker.mp hi
      refine Subgroup.mem_inf.mpr ⟨i.2, ?_⟩
      have h1 : (i : G) * (a * (i : G) * a⁻¹) = 1 := by
        have h := congrArg (fun t : I => (t : G)) hphi
        rw [hφ_coe i, Subgroup.coe_one] at h
        exact h
      have h2 : a * (i : G) * a⁻¹ = (i : G) := by
        rw [← inv_eq_of_mul_eq_one_right h1, b15_W15ElevenDichInv_inv_eq_of_mem hI i.2]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc (i : G) * a = (a * (i : G) * a⁻¹) * a := by rw [h2]
          _ = a * (i : G) := by group)
    · intro g hg
      obtain ⟨hgI, hgc⟩ := Subgroup.mem_inf.mp hg
      refine Subgroup.mem_map.mpr ⟨⟨g, hgI⟩, ?_, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      show ((φ ⟨g, hgI⟩ : I) : G) = 1
      have hca : a * g * a⁻¹ = g := by
        rw [show a * g = g * a from (Subgroup.mem_centralizer_singleton_iff.mp hgc).symm]
        group
      calc ((φ ⟨g, hgI⟩ : I) : G) = g * (a * g * a⁻¹) := hφ_coe ⟨g, hgI⟩
        _ = g * g := by rw [hca]
        _ = 1 := by rw [← pow_two, hI.2 g hgI]
  have hrange_map : (φ.range).map I.subtype = ⁅I, zpowers a⁆ := by
    apply le_antisymm
    · rintro g ⟨y, hy, hgy⟩
      rw [← hgy]
      obtain ⟨i, rfl⟩ := MonoidHom.mem_range.mp hy
      have hcoe : ((φ i : I) : G) = ⁅(i : G), a⁆ := by
        rw [hφ_coe, commutatorElement_def,
          b15_W15ElevenDichInv_inv_eq_of_mem hI i.2, ha_inv]
        group
      change ((φ i : I) : G) ∈ ⁅I, zpowers a⁆
      rw [hcoe]
      exact Subgroup.commutator_mem_commutator i.2 (Subgroup.mem_zpowers a)
    · rw [Subgroup.commutator_le]
      intro x hx g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rcases b15_W15ElevenDichInv_zpow_eq_one_or_self ha n with hn | hn
      · rw [hn]
        have h1 : ⁅x, (1 : G)⁆ = 1 := by rw [commutatorElement_def]; simp
        rw [h1]
        exact Subgroup.mem_map.mpr ⟨(1 : I), (φ.range).one_mem, rfl⟩
      · rw [hn]
        refine Subgroup.mem_map.mpr ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
        show ((φ ⟨x, hx⟩ : I) : G) = ⁅x, a⁆
        rw [hφ_coe, commutatorElement_def,
          b15_W15ElevenDichInv_inv_eq_of_mem hI hx, ha_inv]
        group
  have hcard_ker : Nat.card ↥φ.ker = Nat.card ↥(I ⊓ centralizer ({a} : Set G)) := by
    have h1 := Subgroup.card_map_of_injective (K := φ.ker) (f := I.subtype) I.subtype_injective
    rw [hker_map] at h1
    exact h1.symm
  have hcard_range : Nat.card ↥φ.range = Nat.card ↥⁅I, zpowers a⁆ := by
    have h1 := Subgroup.card_map_of_injective (K := φ.range) (f := I.subtype) I.subtype_injective
    rw [hrange_map] at h1
    exact h1.symm
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hcard_ker, hcard_range] at h
  exact h

theorem inf_centralizer_le_commutator_of_inv_mod {I : Subgroup G} (hI : IsElemAbelian 2 I)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a z : G} (haN : a ∈ normalizer (I : Set G))
    (hzN : z ∈ normalizer (I : Set G)) (ha : a * a = 1) (hz : z ^ p = 1)
    (hcz : I ⊓ centralizer ({z} : Set G) = ⊥) (hinv : z * (a * z * a⁻¹) ∈ I) :
    I ⊓ centralizer ({a} : Set G) ≤ ⁅I, zpowers a⁆ := by
  classical
  haveI : IsMulCommutative I := hI.1
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  let w : G := a * z * a⁻¹
  have hw_eq : w = a * z * a⁻¹ := rfl
  let j : G := z * w
  have hj_eq : j = z * w := rfl
  have hjI : j ∈ I := by rw [hj_eq, hw_eq]; exact hinv
  have haw : a * w * a⁻¹ = z := by
    rw [hw_eq, ha_inv]
    calc a * (a * z * a) * a = (a * a) * z * (a * a) := by group
      _ = z := by rw [ha, one_mul, mul_one]
  let s : G := z * w⁻¹
  have hs_eq_w : s = z * w⁻¹ := rfl
  let i₁ : G := z * j⁻¹ * z⁻¹
  have hi₁_eq : i₁ = z * j⁻¹ * z⁻¹ := rfl
  have hi1I : i₁ ∈ I := by
    rw [hi₁_eq]
    exact (Subgroup.mem_normalizer_iff.mp hzN (j⁻¹)).mp (Subgroup.inv_mem _ hjI)
  have hw_j : w = z⁻¹ * j := by rw [hj_eq]; group
  have hwinv : w⁻¹ = j⁻¹ * z := by rw [hw_j]; group
  have hdecomp : s = i₁ * z ^ 2 := by
    rw [hs_eq_w, hwinv, hi₁_eq]
    group
  have hs_inv : a * s * a⁻¹ = s⁻¹ := by
    rw [hs_eq_w]
    calc a * (z * w⁻¹) * a⁻¹ = (a * z * a⁻¹) * (a * w⁻¹ * a⁻¹) := by group
      _ = w * (a * w⁻¹ * a⁻¹) := by rw [← hw_eq]
      _ = w * (a * w * a⁻¹)⁻¹ := by rw [← conj_inv]
      _ = w * z⁻¹ := by rw [haw]
      _ = (z * w⁻¹)⁻¹ := by group
  have hwN : w ∈ normalizer (I : Set G) := by
    rw [hw_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haN hzN) (Subgroup.inv_mem _ haN)
  have hsN : s ∈ normalizer (I : Set G) := by
    rw [hs_eq_w]
    exact Subgroup.mul_mem _ hzN (Subgroup.inv_mem _ hwN)
  have hz2N : z ^ 2 ∈ normalizer (I : Set G) := Subgroup.pow_mem _ hzN 2
  have hstep : ∀ u ∈ I, s * u * s⁻¹ = z ^ 2 * u * (z ^ 2)⁻¹ := by
    intro u hu
    have hvI : z ^ 2 * u * (z ^ 2)⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp hz2N u).mp hu
    have hcomm : i₁ * (z ^ 2 * u * (z ^ 2)⁻¹) * i₁⁻¹ = z ^ 2 * u * (z ^ 2)⁻¹ := by
      have h := b15_W15ElevenDichInv_mul_comm_of_mem hI hi1I hvI
      calc i₁ * (z ^ 2 * u * (z ^ 2)⁻¹) * i₁⁻¹
          = (i₁ * (z ^ 2 * u * (z ^ 2)⁻¹)) * i₁⁻¹ := rfl
        _ = ((z ^ 2 * u * (z ^ 2)⁻¹) * i₁) * i₁⁻¹ := by rw [h]
        _ = (z ^ 2 * u * (z ^ 2)⁻¹) * (i₁ * i₁⁻¹) := by group
        _ = z ^ 2 * u * (z ^ 2)⁻¹ := by group
    calc s * u * s⁻¹ = (i₁ * z ^ 2) * u * (i₁ * z ^ 2)⁻¹ := by rw [hdecomp]
      _ = i₁ * (z ^ 2 * u * (z ^ 2)⁻¹) * i₁⁻¹ := by group
      _ = z ^ 2 * u * (z ^ 2)⁻¹ := hcomm
  have hconj_pow : ∀ k : ℕ, ∀ u ∈ I,
      s ^ k * u * (s ^ k)⁻¹ = (z ^ 2) ^ k * u * ((z ^ 2) ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u hu; simp
    | succ k ih =>
        intro u hu
        have hu' : (z ^ 2) ^ k * u * ((z ^ 2) ^ k)⁻¹ ∈ I :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hz2N k) u).mp hu
        calc s ^ (k + 1) * u * (s ^ (k + 1))⁻¹
            = s * (s ^ k * u * (s ^ k)⁻¹) * s⁻¹ := by
              rw [pow_succ', mul_inv_rev]; group
          _ = s * ((z ^ 2) ^ k * u * ((z ^ 2) ^ k)⁻¹) * s⁻¹ := by rw [ih u hu]
          _ = z ^ 2 * ((z ^ 2) ^ k * u * ((z ^ 2) ^ k)⁻¹) * (z ^ 2)⁻¹ := hstep _ hu'
          _ = (z ^ 2) ^ (k + 1) * u * ((z ^ 2) ^ (k + 1))⁻¹ := by
              rw [pow_succ', mul_inv_rev]; group
  have hdecomp_k : ∀ k : ℕ, ∃ i ∈ I, s ^ k = i * z ^ (2 * k) := by
    intro k
    induction k with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ k ih =>
        obtain ⟨i, hi, hik⟩ := ih
        let i₂ : G := z ^ (2 * k) * i₁ * (z ^ (2 * k))⁻¹
        have hi₂_eq : i₂ = z ^ (2 * k) * i₁ * (z ^ (2 * k))⁻¹ := rfl
        have hi2 : i₂ ∈ I := by
          rw [hi₂_eq]
          exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hzN (2 * k)) i₁).mp hi1I
        refine ⟨i * i₂, Subgroup.mul_mem _ hi hi2, ?_⟩
        have hzi : z ^ (2 * k) * i₁ = i₂ * z ^ (2 * k) := by rw [hi₂_eq]; group
        rw [pow_succ, hik, hdecomp]
        calc i * z ^ (2 * k) * (i₁ * z ^ 2)
            = i * (z ^ (2 * k) * i₁) * z ^ 2 := by group
          _ = i * (i₂ * z ^ (2 * k)) * z ^ 2 := by rw [hzi]
          _ = (i * i₂) * (z ^ (2 * k) * z ^ 2) := by group
          _ = (i * i₂) * z ^ (2 * k + 2) := by rw [← pow_add]
          _ = (i * i₂) * z ^ (2 * (k + 1)) := by
                rw [show 2 * (k + 1) = 2 * k + 2 by ring]
  have hspI : s ^ p ∈ I := by
    obtain ⟨i, hi, hik⟩ := hdecomp_k p
    rw [hik]
    have hzp : z ^ (2 * p) = 1 := by
      rw [show 2 * p = p * 2 by ring, pow_mul, hz, one_pow]
    rw [hzp, mul_one]
    exact hi
  let x : G := s ^ Nat.card ↥I
  have hx_def : x = s ^ Nat.card ↥I := rfl
  have hx_pow : x ^ p = 1 := by
    rw [hx_def]
    change (s ^ Nat.card ↥I) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul]
    exact congrArg (fun t : I => (t : G))
      (pow_card_eq_one' (G := ↥I) (x := ⟨s ^ p, hspI⟩))
  have hxN : x ∈ normalizer (I : Set G) := by
    rw [hx_def]
    exact Subgroup.pow_mem _ hsN _
  have hinv' : a * x * a⁻¹ = x⁻¹ := by
    rw [hx_def, ← conj_pow (a := a) (b := s) (i := Nat.card ↥I), hs_inv, inv_pow]
  have hcx : I ⊓ centralizer ({x} : Set G) = ⊥ := by
    apply le_antisymm _ bot_le
    intro u hu
    obtain ⟨huI, huxc⟩ := Subgroup.mem_inf.mp hu
    have hux : x * u * x⁻¹ = u := by
      have hcomm : x * u = u * x := (Subgroup.mem_centralizer_singleton_iff.mp huxc).symm
      calc x * u * x⁻¹ = (u * x) * x⁻¹ := by rw [hcomm]
        _ = u := by group
    have hyu : (z ^ 2) ^ (Nat.card ↥I) * u * ((z ^ 2) ^ (Nat.card ↥I))⁻¹ = u := by
      rw [← hconj_pow (Nat.card ↥I) u huI, ← hx_def]
      exact hux
    have hycomm : Commute ((z ^ 2) ^ (Nat.card ↥I)) u := by
      show (z ^ 2) ^ (Nat.card ↥I) * u = u * (z ^ 2) ^ (Nat.card ↥I)
      calc (z ^ 2) ^ (Nat.card ↥I) * u
          = ((z ^ 2) ^ (Nat.card ↥I) * u * ((z ^ 2) ^ (Nat.card ↥I))⁻¹)
            * (z ^ 2) ^ (Nat.card ↥I) := by group
        _ = u * (z ^ 2) ^ (Nat.card ↥I) := by rw [hyu]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hI.isPGroup
    have hcop : Nat.Coprime (2 * Nat.card ↥I) p := by
      have h2m : 2 * Nat.card ↥I = 2 ^ (k + 1) := by rw [hk, pow_succ']
      rw [h2m]
      exact ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_left (k + 1)
    obtain ⟨r, t, hrt⟩ : ∃ r t : ℤ,
        (((2 * Nat.card ↥I : ℕ)) : ℤ) * r + (p : ℤ) * t = 1 := by
      refine ⟨Nat.gcdA (2 * Nat.card ↥I) p, Nat.gcdB (2 * Nat.card ↥I) p, ?_⟩
      have hbez := Nat.gcd_eq_gcd_ab (2 * Nat.card ↥I) p
      rw [hcop.gcd_eq_one] at hbez
      simpa using hbez.symm
    have hYz : (z ^ 2) ^ (Nat.card ↥I) = z ^ (((2 * Nat.card ↥I : ℕ)) : ℤ) := by
      rw [← pow_mul, zpow_natCast]
    have hz_eq : z = ((z ^ 2) ^ (Nat.card ↥I)) ^ r := by
      calc z = z ^ (1 : ℤ) := (zpow_one z).symm
        _ = z ^ ((((2 * Nat.card ↥I : ℕ)) : ℤ) * r + (p : ℤ) * t) := by rw [← hrt]
        _ = z ^ ((((2 * Nat.card ↥I : ℕ)) : ℤ) * r) * z ^ ((p : ℤ) * t) := by
              rw [zpow_add]
        _ = (z ^ (((2 * Nat.card ↥I : ℕ)) : ℤ)) ^ r * (z ^ ((p : ℤ))) ^ t := by
              rw [zpow_mul, zpow_mul]
        _ = ((z ^ 2) ^ (Nat.card ↥I)) ^ r * (z ^ p) ^ t := by rw [← hYz, zpow_natCast]
        _ = ((z ^ 2) ^ (Nat.card ↥I)) ^ r * 1 ^ t := by rw [hz]
        _ = ((z ^ 2) ^ (Nat.card ↥I)) ^ r := by rw [one_zpow, mul_one]
    have huz : Commute u z := by
      have h1 : Commute u (((z ^ 2) ^ (Nat.card ↥I)) ^ r) := (hycomm.symm).zpow_right r
      rwa [← hz_eq] at h1
    have hmemz : u ∈ centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr huz
    have hubot : u ∈ (⊥ : Subgroup G) := by
      have : u ∈ I ⊓ centralizer ({z} : Set G) := ⟨huI, hmemz⟩
      rwa [hcz] at this
    exact hubot
  exact inf_centralizer_le_commutator_of_inv hI hp hp2 hx_pow hxN haN ha hinv' hcx

theorem card_inf_centralizer_sq_of_inv_mod {I : Subgroup G} (hI : IsElemAbelian 2 I)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a z : G} (haN : a ∈ normalizer (I : Set G))
    (hzN : z ∈ normalizer (I : Set G)) (ha : a * a = 1) (hz : z ^ p = 1)
    (hcz : I ⊓ centralizer ({z} : Set G) = ⊥) (hinv : z * (a * z * a⁻¹) ∈ I) :
    Nat.card ↥(I ⊓ centralizer ({a} : Set G)) ^ 2 = Nat.card ↥I := by
  have hle1 := commutator_zpowers_le_inf_centralizer_of_mul_self hI haN ha
  have hle2 := inf_centralizer_le_commutator_of_inv_mod hI hp hp2 haN hzN ha hz hcz hinv
  have heq : ⁅I, zpowers a⁆ = I ⊓ centralizer ({a} : Set G) := le_antisymm hle1 hle2
  have h2 := card_inf_centralizer_mul_card_commutator_zpowers hI haN ha
  rw [heq] at h2
  rw [pow_two]
  exact h2

theorem card_modEq_one_of_isPGroup_inf_centralizer_eq_bot {p : ℕ} [Fact p.Prime] {X I : Subgroup G}
    (hX : IsPGroup p ↥X) (hXN : X ≤ normalizer (I : Set G))
    (hcent : I ⊓ centralizer (X : Set G) = ⊥) : Nat.card ↥I ≡ 1 [MOD p] := by
  classical
  letI : Subgroup.Normalizes X I := ⟨hXN⟩
  have hmod := hX.card_modEq_card_fixedPoints (↥I)
  have hfixed : MulAction.fixedPoints ↥X ↥I = {1} := by
    ext i
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hi
      rw [Set.mem_singleton_iff]
      apply Subtype.ext
      show (i : G) = 1
      have hmem : (i : G) ∈ I ⊓ centralizer (X : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨i.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have h2 := congrArg Subtype.val (hi ⟨h, hh⟩)
        rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h2
        calc h * (i : G) = h * (i : G) * h⁻¹ * h := by group
          _ = (i : G) * h := by rw [h2]
      have := hmem
      rw [hcent] at this
      exact Subgroup.mem_bot.mp this
    · intro hi
      rw [Set.mem_singleton_iff] at hi
      subst hi
      intro x
      apply Subtype.ext
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      simp
  have hcard : Nat.card (MulAction.fixedPoints ↥X ↥I) = 1 := by
    rw [hfixed]
    exact Nat.card_unique
  rwa [hcard] at hmod

theorem inf_centralizer_le_of_mul_mem_centralizer {I A : Subgroup G} {a v : G} (ha : a ∈ A)
    (hav : a * v ∈ centralizer (I : Set G)) :
    I ⊓ centralizer (A : Set G) ≤ I ⊓ centralizer ({v} : Set G) := by
  intro i hi
  obtain ⟨hiI, hicA⟩ := Subgroup.mem_inf.mp hi
  have hai : a * i = i * a := (Subgroup.mem_centralizer_iff.mp hicA) a ha
  have hiav : i * (a * v) = (a * v) * i := (Subgroup.mem_centralizer_iff.mp hav) i hiI
  refine Subgroup.mem_inf.mpr ⟨hiI, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply mul_left_cancel (a := a)
  calc a * (i * v) = (a * i) * v := by group
    _ = (i * a) * v := by rw [hai]
    _ = i * (a * v) := by group
    _ = (a * v) * i := hiav
    _ = a * (v * i) := by group

end CFSG.LocalAnalysis.WeakClosure81
