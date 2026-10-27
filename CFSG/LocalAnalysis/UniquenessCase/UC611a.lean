module

public import CFSG.Open.RankThreeDefs
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

local notation "Q8" => QuaternionGroup 2

theorem uc611_q8_normal : ∀ s x : Q8, s ^ 2 ≠ 1 → ∃ k < 4, x * s * x⁻¹ = s ^ k := by decide

theorem uc611_q8_cent : ∀ s u : Q8, s ^ 2 ≠ 1 → u * s = s * u → ∃ k < 4, u = s ^ k := by decide

theorem uc611_q8_cube : ∀ s : Q8, s ^ 2 ≠ 1 → ∀ k < 4, (s ^ k) ^ 3 = 1 → s ^ k = 1 := by decide

theorem uc611_q8_comm_four : ∀ g h : Q8, g ^ 2 ≠ 1 → h ^ 2 ≠ 1 → h * g = g * h →
    h = g ∨ h = g⁻¹ := by decide

theorem uc611_q8_gen : ∀ g h : Q8, g ^ 2 ≠ 1 → h ^ 2 ≠ 1 → h ≠ g → h ≠ g⁻¹ →
    ∀ x : Q8, ∃ i < 4, ∃ j < 2, x = g ^ i * h ^ j := by decide

theorem uc611_q8_prod : ∀ s t : Q8, s ^ 2 ≠ 1 → t ≠ s → t ≠ s⁻¹ → (s * t⁻¹) ^ 2 ≠ 1 := by decide

theorem uc611_q8_invol : ∀ g : Q8, g ^ 2 = 1 → g = 1 ∨ g = QuaternionGroup.a 2 := by decide

theorem uc611_q8_aut_inj {φ : Q8 →* Q8} (h3 : ∀ x, φ (φ (φ x)) = x) : Function.Injective φ :=
  fun a b h => by rw [← h3 a, ← h3 b, h]

theorem uc611_q8_aut_eq_of_fixed {φ : Q8 →* Q8} (h3 : ∀ x, φ (φ (φ x)) = x) {s : Q8}
    (hs : s ^ 2 ≠ 1) (hφs : φ s = s) (x : Q8) : φ x = x := by
  obtain ⟨k, -, hk⟩ := uc611_q8_normal s x hs
  have h1 : φ (x * s * x⁻¹) = x * s * x⁻¹ := by rw [hk, map_pow, hφs]
  rw [map_mul, map_mul, map_inv, hφs] at h1
  have h2 : x⁻¹ * φ x * s = s * (x⁻¹ * φ x) := by
    calc x⁻¹ * φ x * s = x⁻¹ * (φ x * s * (φ x)⁻¹) * φ x := by group
      _ = x⁻¹ * (x * s * x⁻¹) * φ x := by rw [h1]
      _ = s * (x⁻¹ * φ x) := by group
  obtain ⟨j, hj4, hj⟩ := uc611_q8_cent s _ hs h2
  obtain ⟨u, hu⟩ : ∃ u, u = x⁻¹ * φ x := ⟨_, rfl⟩
  rw [← hu] at hj
  have hφx : φ x = x * u := by rw [hu]; group
  have hφu : φ u = u := by rw [hj, map_pow, hφs]
  have h4 : φ (φ x) = x * u * u := by rw [hφx, map_mul, hφu, hφx]
  have h5 : φ (φ (φ x)) = x * u * u * u := by rw [h4, map_mul, map_mul, hφu, hφx]
  have h6 : u ^ 3 = 1 := by
    have := h3 x
    rw [h5] at this
    have h7 : x * u ^ 3 = x := by
      calc x * u ^ 3 = x * u * u * u := by simp [pow_succ, mul_assoc]
        _ = x := this
    simpa using h7
  have h8 : u = 1 := by
    rw [hj] at h6 ⊢
    exact uc611_q8_cube s hs j hj4 h6
  rw [hφx, h8, mul_one]

theorem uc611_q8_aut_move {φ : Q8 →* Q8} (h3 : ∀ x, φ (φ (φ x)) = x) (hnt : ∃ x, φ x ≠ x) {s : Q8}
    (hs : s ^ 2 ≠ 1) : (φ s) ^ 2 ≠ 1 ∧ φ s ≠ s ∧ φ s ≠ s⁻¹ := by
  refine ⟨fun h => hs ?_, fun h => ?_, fun h => hs ?_⟩
  · apply uc611_q8_aut_inj h3
    rw [map_pow, h, map_one]
  · obtain ⟨x, hx⟩ := hnt
    exact hx (uc611_q8_aut_eq_of_fixed h3 hs h x)
  · have h1 : φ (φ s) = s := by rw [h, map_inv, h, inv_inv]
    have h2 : φ (φ (φ s)) = s⁻¹ := by rw [h1, h]
    rw [h3] at h2
    rw [sq]
    exact mul_eq_one_iff_eq_inv.mpr h2

theorem uc611_q8_aut_not_comm {φ : Q8 →* Q8} (h3 : ∀ x, φ (φ (φ x)) = x) (hnt : ∃ x, φ x ≠ x)
    {s : Q8} (hs : s ^ 2 ≠ 1) : φ s * s ≠ s * φ s := by
  obtain ⟨h1, h2, h3'⟩ := uc611_q8_aut_move h3 hnt hs
  intro h
  rcases uc611_q8_comm_four s (φ s) hs h1 h with h | h
  · exact h2 h
  · exact h3' h

theorem uc611_q8_aut_gen {φ : Q8 →* Q8} (h3 : ∀ x, φ (φ (φ x)) = x) (hnt : ∃ x, φ x ≠ x)
    {s : Q8} (hs : s ^ 2 ≠ 1) (x : Q8) : ∃ i < 4, ∃ j < 2, x = s ^ i * (φ s) ^ j := by
  obtain ⟨h1, h2, h3'⟩ := uc611_q8_aut_move h3 hnt hs
  exact uc611_q8_gen s (φ s) hs h1 h2 h3' x

structure Q8CCPres (R B : Subgroup G) (ι : QuaternionGroup 2 →* G) : Prop where
  inj : Function.Injective ι
  cyc : IsCyclic ↥B
  comm : ∀ (X : QuaternionGroup 2), ∀ b ∈ B, ι X * b = b * ι X
  mem_iff : ∀ X : QuaternionGroup 2, ι X ∈ B ↔ (X = 1 ∨ X = QuaternionGroup.a 2)
  mem_R : ∀ r, r ∈ R ↔ ∃ X : QuaternionGroup 2, ∃ b ∈ B, r = ι X * b

section Pres

variable {R B : Subgroup G} {ι : QuaternionGroup 2 →* G}

theorem uc611_pres_mul_mem (h : Q8CCPres R B ι) (X : QuaternionGroup 2) {b : G} (hb : b ∈ B) :
    ι X * b ∈ R := (h.mem_R _).2 ⟨X, b, hb, rfl⟩

theorem uc611_pres_range_mem (h : Q8CCPres R B ι) (X : QuaternionGroup 2) : ι X ∈ R := by
  simpa using uc611_pres_mul_mem h X B.one_mem

theorem uc611_pres_B_mem (h : Q8CCPres R B ι) {b : G} (hb : b ∈ B) : b ∈ R := by
  simpa using uc611_pres_mul_mem h 1 hb

theorem uc611_pres_comm_R (h : Q8CCPres R B ι) {b r : G} (hb : b ∈ B) (hr : r ∈ R) :
    b * r = r * b := by
  haveI := h.cyc
  obtain ⟨X, b', hb', rfl⟩ := (h.mem_R r).1 hr
  exact (Commute.mul_right (h.comm X b hb).symm (setLike_mul_comm hb hb') :
    Commute b (ι X * b')).eq

theorem uc611_pres_mem_of_central (h : Q8CCPres R B ι) {r : G} (hr : r ∈ R)
    (hc : ∀ r' ∈ R, r * r' = r' * r) : r ∈ B := by
  obtain ⟨X, b, hb, rfl⟩ := (h.mem_R r).1 hr
  have hX : ∀ Y, Y * X = X * Y := by
    intro Y
    have h1 := hc (ι Y) (uc611_pres_range_mem h Y)
    apply h.inj
    rw [map_mul, map_mul]
    have h2 : ι X * ι Y * b = ι Y * ι X * b := by
      calc ι X * ι Y * b = ι X * b * ι Y := by rw [mul_assoc, h.comm Y b hb, ← mul_assoc]
        _ = ι Y * (ι X * b) := h1
        _ = ι Y * ι X * b := by rw [mul_assoc]
    exact (mul_right_cancel h2).symm
  exact B.mul_mem ((h.mem_iff X).2 ((CFSG.Semidihedral.Local.qEight_center X).1 hX)) hb

theorem uc611_pres_conj_mem (h : Q8CCPres R B ι) {w : G} (hw : w ∈ normalizer (R : Set G)) {b : G}
    (hb : b ∈ B) : w * b * w⁻¹ ∈ B := by
  have hwR : w * b * w⁻¹ ∈ R := (mem_normalizer_iff.1 hw b).1 (uc611_pres_B_mem h hb)
  refine uc611_pres_mem_of_central h hwR fun r hr => ?_
  have hr' : w⁻¹ * r * w ∈ R := (mem_normalizer_iff''.1 hw r).1 hr
  have h1 := uc611_pres_comm_R h hb hr'
  calc w * b * w⁻¹ * r = w * (b * (w⁻¹ * r * w)) * w⁻¹ := by group
    _ = w * ((w⁻¹ * r * w) * b) * w⁻¹ := by rw [h1]
    _ = r * (w * b * w⁻¹) := by group

theorem uc611_pres_c (h : Q8CCPres R B ι) :
    ι (QuaternionGroup.a 2) ∈ B ∧ ι (QuaternionGroup.a 2) ≠ 1 ∧ ι (QuaternionGroup.a 2) ^ 2 = 1 := by
  refine ⟨(h.mem_iff _).2 (Or.inr rfl), fun h1 => ?_, ?_⟩
  · exact (by decide : (QuaternionGroup.a 2 : Q8) ≠ 1) (h.inj (by rw [h1, map_one]))
  · rw [← map_pow, (by decide : (QuaternionGroup.a 2 : Q8) ^ 2 = 1), map_one]

theorem uc611_pres_eq_of_sq (h : Q8CCPres R B ι) {b : G} (hb : b ∈ B) (hb2 : b ^ 2 = 1) :
    b = 1 ∨ b = ι (QuaternionGroup.a 2) := by
  haveI := h.cyc
  classical
  by_contra hne
  obtain ⟨hne1, hne2⟩ := not_or.1 hne
  obtain ⟨hc, hc1, hc2⟩ := uc611_pres_c h
  letI : Fintype ↥B := Fintype.ofFinite _
  have key := IsCyclic.card_pow_eq_one_le (α := ↥B) (n := 2) (by norm_num)
  have hsub : ({1, ⟨_, hc⟩, ⟨b, hb⟩} : Finset ↥B) ⊆
      Finset.univ.filter (fun a : ↥B => a ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext hc2
    · exact Subtype.ext hb2
  have h3 : ({1, ⟨_, hc⟩, ⟨b, hb⟩} : Finset ↥B).card = 3 := by
    refine Finset.card_eq_three.2 ⟨1, ⟨_, hc⟩, ⟨b, hb⟩, ?_, ?_, ?_, rfl⟩
    · exact fun h' => hc1 (congrArg Subtype.val h').symm
    · exact fun h' => hne1 (congrArg Subtype.val h').symm
    · exact fun h' => hne2 (congrArg Subtype.val h').symm
  have := Finset.card_le_card hsub
  omega

theorem uc611_pres_comm_z (h : Q8CCPres R B ι) {n : ℕ} (hn : Nat.card B = 2 ^ n) {z : G}
    (hz3 : z ^ 3 = 1) (hzR : z ∈ normalizer (R : Set G)) : ∀ b ∈ B, z * b = b * z := by
  haveI := h.cyc
  have hzB : z ∈ normalizer (B : Set G) := by
    rw [mem_normalizer_iff]
    intro b
    refine ⟨fun hb => uc611_pres_conj_mem h hzR hb, fun hb => ?_⟩
    have := uc611_pres_conj_mem h (inv_mem hzR) hb
    simpa [mul_assoc] using this
  have hψ3 : B.normalizerMonoidHom ⟨z, hzB⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨z, hzB⟩ : normalizer (B : Set G)) ^ 3 = 1 := Subtype.ext hz3
    rw [this, map_one]
  have hord3 : orderOf (B.normalizerMonoidHom ⟨z, hzB⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one hψ3
  have hordc : orderOf (B.normalizerMonoidHom ⟨z, hzB⟩) ∣ Nat.totient (2 ^ n) := by
    rw [← hn, ← IsCyclic.card_mulAut]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime 3 (Nat.totient (2 ^ n)) := by
    cases n with
    | zero => simp
    | succ m =>
      rw [Nat.totient_prime_pow_succ Nat.prime_two]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right m (by norm_num)) (by norm_num)
  have hord1 : orderOf (B.normalizerMonoidHom ⟨z, hzB⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hord3 hordc
  have hψ1 := orderOf_eq_one_iff.1 hord1
  intro b hb
  have h1 := congrArg (fun f : MulAut ↥B => ((f ⟨b, hb⟩ : ↥B) : G)) hψ1
  have h2 : z * b * z⁻¹ = b := h1
  calc z * b = z * b * z⁻¹ * z := by group
    _ = b * z := by rw [h2]

theorem uc611_pres_conj_range (h : Q8CCPres R B ι) {w : G} (hw : w ∈ normalizer (R : Set G))
    (hwB : ∀ b ∈ B, w * b = b * w) (X : QuaternionGroup 2) : ∃ Y, w * ι X * w⁻¹ = ι Y := by
  obtain ⟨hc, hc1, hc2⟩ := uc611_pres_c h
  by_cases hX : X ^ 2 = 1
  · refine ⟨X, ?_⟩
    have hXB : ι X ∈ B := (h.mem_iff X).2 (uc611_q8_invol X hX)
    rw [hwB _ hXB]
    group
  · have hXc : X ^ 2 = QuaternionGroup.a 2 := CFSG.Semidihedral.Local.qEight_sq_ne_one X hX
    have hr : w * ι X * w⁻¹ ∈ R :=
      (mem_normalizer_iff.1 hw _).1 (uc611_pres_range_mem h X)
    obtain ⟨Y, b, hb, hYb⟩ := (h.mem_R _).1 hr
    have hsq : (w * ι X * w⁻¹) ^ 2 = ι (QuaternionGroup.a 2) := by
      rw [conj_pow, ← map_pow, hXc, hwB _ hc]
      group
    by_cases hY : Y ^ 2 = 1
    · exfalso
      have hYB : ι Y ∈ B := (h.mem_iff Y).2 (uc611_q8_invol Y hY)
      have hrB : w * ι X * w⁻¹ ∈ B := hYb ▸ B.mul_mem hYB hb
      have h1 : w * (w * ι X * w⁻¹) = (w * ι X * w⁻¹) * w := hwB _ hrB
      have h2 : w * ι X * w⁻¹ = ι X := by
        have h3 : w * (w * ι X * w⁻¹) = w * ι X := by rw [h1]; group
        exact mul_left_cancel h3
      have hXB : ι X ∈ B := h2 ▸ hrB
      rcases (h.mem_iff X).1 hXB with h' | h'
      · exact hX (by rw [h']; exact one_pow 2)
      · exact hX (by rw [h']; decide)
    · have hYc : Y ^ 2 = QuaternionGroup.a 2 := CFSG.Semidihedral.Local.qEight_sq_ne_one Y hY
      have hb2 : b ^ 2 = 1 := by
        have h1 : (ι Y * b) ^ 2 = ι (QuaternionGroup.a 2) * b ^ 2 := by
          rw [Commute.mul_pow (h.comm Y b hb), ← map_pow, hYc]
        rw [← hYb, hsq] at h1
        exact mul_eq_left.1 h1.symm
      rcases uc611_pres_eq_of_sq h hb hb2 with hb1 | hbc
      · exact ⟨Y, by rw [hYb, hb1, mul_one]⟩
      · exact ⟨Y * QuaternionGroup.a 2, by rw [hYb, hbc, map_mul]⟩

theorem uc611_pres_commutator (h : Q8CCPres R B ι) {w : G} (hw : w ∈ normalizer (R : Set G))
    (hwB : ∀ b ∈ B, w * b = b * w) {r : G} (hr : r ∈ R) : ∃ Y, ⁅r, w⁆ = ι Y := by
  obtain ⟨X, b, hb, rfl⟩ := (h.mem_R r).1 hr
  obtain ⟨Y, hY⟩ := uc611_pres_conj_range h hw hwB X⁻¹
  refine ⟨X * Y, ?_⟩
  rw [map_mul, ← hY, map_inv, commutatorElement_def]
  have hbw : b * w = w * b := (hwB b hb).symm
  calc ι X * b * w * (ι X * b)⁻¹ * w⁻¹ = ι X * (b * w) * b⁻¹ * (ι X)⁻¹ * w⁻¹ := by group
    _ = ι X * (w * b) * b⁻¹ * (ι X)⁻¹ * w⁻¹ := by rw [hbw]
    _ = ι X * (w * (ι X)⁻¹ * w⁻¹) := by group

end Pres

theorem uc611_exists_aut {ι : QuaternionGroup 2 →* G} (hι : Function.Injective ι) {z : G}
    (hz : ∀ X, ∃ Y, z * ι X * z⁻¹ = ι Y) :
    ∃ φ : QuaternionGroup 2 →* QuaternionGroup 2, ∀ X, ι (φ X) = z * ι X * z⁻¹ := by
  choose f hf using hz
  refine ⟨MonoidHom.mk' f fun X Y => hι ?_, fun X => (hf X).symm⟩
  rw [map_mul, ← hf, ← hf, ← hf, map_mul]
  group

theorem uc611_pres_of {R : Subgroup G} {n : ℕ} (hR : rankThreeIsQ8CentralCyclic R n) :
    ∃ (B : Subgroup G) (ι : QuaternionGroup 2 →* G), Q8CCPres R B ι ∧ Nat.card B = 2 ^ n := by
  obtain ⟨A, B, ⟨e⟩, hBc, hBn, hcomm, hsup, hinf⟩ := hR
  let ι : QuaternionGroup 2 →* G := A.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := A.subtype_injective.comp e.symm.injective
  have hιA : ∀ X, ι X ∈ A := fun X => (e.symm X).2
  have hAι : ∀ x ∈ A, ∃ X, ι X = x := fun x hx => ⟨e ⟨x, hx⟩, by simp [ι]⟩
  have hsq : ∀ X, ι X ∈ B → X ^ 2 = 1 := by
    intro X hX
    have h1 : (⟨ι X, Subgroup.mem_inf.2 ⟨hιA X, hX⟩⟩ : ↥(A ⊓ B)) ^ Nat.card ↥(A ⊓ B) = 1 :=
      pow_card_eq_one'
    rw [hinf] at h1
    have h2 : ι X ^ 2 = 1 := congrArg Subtype.val h1
    apply hι
    rw [map_pow, map_one, h2]
  have hc : ι (QuaternionGroup.a 2) ∈ B := by
    haveI : Nontrivial ↥(A ⊓ B) := Finite.one_lt_card_iff_nontrivial.1 (by rw [hinf]; norm_num)
    obtain ⟨⟨y, hyA, hyB⟩, hy1⟩ := exists_ne (1 : ↥(A ⊓ B))
    obtain ⟨Y, rfl⟩ := hAι y hyA
    have hY1 : Y ≠ 1 := fun h' => hy1 (Subtype.ext (by simp [h']))
    rcases uc611_q8_invol Y (hsq Y hyB) with h' | h'
    · exact absurd h' hY1
    · rw [← h']
      exact hyB
  refine ⟨B, ι, ⟨hι, hBc, fun X b hb => hcomm _ (hιA X) b hb, fun X => ⟨fun hX => ?_, ?_⟩, ?_⟩,
    hBn⟩
  · exact uc611_q8_invol X (hsq X hX)
  · rintro (rfl | rfl)
    · rw [map_one]
      exact B.one_mem
    · exact hc
  · intro r
    rw [← hsup]
    constructor
    · intro hr
      obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hr
      obtain ⟨X, rfl⟩ := hAι a ha
      exact ⟨X, b, hb, rfl⟩
    · rintro ⟨X, b, hb, rfl⟩
      exact Subgroup.mul_mem_sup (hιA X) hb

theorem uc611_q8cc_core {R : Subgroup G} {n : ℕ} (hR : rankThreeIsQ8CentralCyclic R n) {z : G}
    (hz3 : z ^ 3 = 1) (hzR : z ∈ normalizer (R : Set G)) (hnt : ∃ r ∈ R, z * r ≠ r * z) :
    ∃ (B : Subgroup G) (ι : QuaternionGroup 2 →* G), Function.Injective ι ∧ IsCyclic ↥B ∧
      Nat.card B = 2 ^ n ∧ ⁅R, zpowers z⁆ = ι.range ∧ R ⊓ centralizer ({z} : Set G) = B ∧
      ∀ T : Subgroup G, T ≤ R → IsMulCommutative T → z ∈ normalizer (T : Set G) → T ≤ B := by
  obtain ⟨B, ι, h, hBn⟩ := uc611_pres_of hR
  have hzB : ∀ b ∈ B, z * b = b * z := uc611_pres_comm_z h hBn hz3 hzR
  obtain ⟨φ, hφ⟩ := uc611_exists_aut h.inj (uc611_pres_conj_range h hzR hzB)
  have hφ3 : ∀ X, φ (φ (φ X)) = X := by
    intro X
    apply h.inj
    rw [hφ, hφ, hφ]
    have hz3' : z * z * z = 1 := by simpa [pow_succ, mul_assoc] using hz3
    calc z * (z * (z * ι X * z⁻¹) * z⁻¹) * z⁻¹ = (z * z * z) * ι X * (z * z * z)⁻¹ := by
          simp only [mul_assoc, mul_inv_rev]
      _ = ι X := by rw [hz3']; simp
  have hφnt : ∃ X, φ X ≠ X := by
    obtain ⟨r, hr, hzr⟩ := hnt
    obtain ⟨X, b, hb, rfl⟩ := (h.mem_R r).1 hr
    refine ⟨X, fun hX => hzr ?_⟩
    have h1 : z * ι X * z⁻¹ = ι X := by rw [← hφ, hX]
    exact (Commute.mul_right (mul_inv_eq_iff_eq_mul.1 h1 : Commute z (ι X))
      (hzB b hb : Commute z b)).eq
  refine ⟨B, ι, h.inj, h.cyc, hBn, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [commutator_le]
      intro r hr w hw
      have hW : zpowers z ≤ normalizer (R : Set G) ⊓ centralizer (B : Set G) :=
        zpowers_le.2 ⟨hzR, mem_centralizer_iff.2 fun b hb => (hzB b hb).symm⟩
      have hw' := hW hw
      obtain ⟨Y, hY⟩ := uc611_pres_commutator h hw'.1
        (fun b hb => (mem_centralizer_iff.1 hw'.2 b hb).symm) hr
      exact ⟨Y, hY.symm⟩
    · have hmem : ∀ r ∈ R, ⁅r, z⁆ ∈ ⁅R, zpowers z⁆ := fun r hr =>
        commutator_mem_commutator hr (mem_zpowers z)
      have hs : (QuaternionGroup.a 1 : Q8) ^ 2 ≠ 1 := by decide
      obtain ⟨-, h2, h3⟩ := uc611_q8_aut_move hφ3 hφnt hs
      have hS2 : (QuaternionGroup.a 1 * (φ (QuaternionGroup.a 1))⁻¹ : Q8) ^ 2 ≠ 1 :=
        uc611_q8_prod _ _ hs h2 h3
      have hS : ι (QuaternionGroup.a 1 * (φ (QuaternionGroup.a 1))⁻¹) ∈ ⁅R, zpowers z⁆ := by
        have := hmem _ (uc611_pres_range_mem h (QuaternionGroup.a 1))
        convert this using 1
        rw [map_mul, map_inv, hφ, commutatorElement_def]
        group
      have hφS : ι (φ (QuaternionGroup.a 1 * (φ (QuaternionGroup.a 1))⁻¹)) ∈ ⁅R, zpowers z⁆ := by
        have := hmem _ (uc611_pres_range_mem h (φ (QuaternionGroup.a 1)))
        convert this using 1
        rw [hφ, map_mul, map_inv, hφ, commutatorElement_def]
        group
      rintro _ ⟨X', rfl⟩
      obtain ⟨i, -, j, -, hX'⟩ := uc611_q8_aut_gen hφ3 hφnt hS2 X'
      rw [hX', map_mul, map_pow, map_pow]
      exact mul_mem (pow_mem hS i) (pow_mem hφS j)
  · apply le_antisymm
    · rintro r ⟨hrR, hrc⟩
      have hrz : z * r = r * z := mem_centralizer_iff.1 hrc z rfl
      obtain ⟨X, b, hb, rfl⟩ := (h.mem_R r).1 hrR
      have h2 : Commute z (ι X) := by
        have := Commute.mul_right (hrz : Commute z (ι X * b))
          (Commute.inv_right (hzB b hb : Commute z b))
        simpa using this
      have h3 : φ X = X := h.inj (by rw [hφ]; exact mul_inv_eq_iff_eq_mul.2 h2.eq)
      by_cases hX : X ^ 2 = 1
      · exact B.mul_mem ((h.mem_iff X).2 (uc611_q8_invol X hX)) hb
      · exact absurd h3 (uc611_q8_aut_move hφ3 hφnt hX).2.1
    · intro r hr
      refine ⟨uc611_pres_B_mem h hr, mem_centralizer_iff.2 fun w hw => ?_⟩
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hzB r hr
  · intro T hTR hT hzT t ht
    obtain ⟨X, b, hb, rfl⟩ := (h.mem_R t).1 (hTR ht)
    have hzt : z * (ι X * b) * z⁻¹ ∈ T := (mem_normalizer_iff.1 hzT _).1 ht
    have hcomm := setLike_mul_comm ht hzt
    have hconj : z * (ι X * b) * z⁻¹ = ι (φ X) * b := by
      calc z * (ι X * b) * z⁻¹ = (z * ι X * z⁻¹) * (z * b * z⁻¹) := by group
        _ = ι (φ X) * b := by rw [← hφ X, hzB b hb]; group
    rw [hconj] at hcomm
    have e1 : ∀ Y Y' : QuaternionGroup 2, ι Y * b * (ι Y' * b) = ι Y * ι Y' * (b * b) := by
      intro Y Y'
      calc ι Y * b * (ι Y' * b) = ι Y * (b * ι Y') * b := by simp only [mul_assoc]
        _ = ι Y * (ι Y' * b) * b := by rw [← h.comm Y' b hb]
        _ = ι Y * ι Y' * (b * b) := by simp only [mul_assoc]
    have hXφ : X * φ X = φ X * X := by
      apply h.inj
      rw [map_mul, map_mul]
      rw [e1, e1] at hcomm
      exact mul_right_cancel hcomm
    by_cases hX2 : X ^ 2 = 1
    · exact B.mul_mem ((h.mem_iff X).2 (uc611_q8_invol X hX2)) hb
    · exact absurd hXφ.symm (uc611_q8_aut_not_comm hφ3 hφnt hX2)

theorem uc611_q8cc_action {R : Subgroup G} {n : ℕ} (hR : rankThreeIsQ8CentralCyclic R n) {z : G}
    (hz3 : z ^ 3 = 1) (hzR : z ∈ normalizer (R : Set G)) (hnt : ∃ r ∈ R, z * r ≠ r * z) :
    Nonempty (↥⁅R, zpowers z⁆ ≃* QuaternionGroup 2) ∧ IsCyclic ↥(R ⊓ centralizer ({z} : Set G)) ∧
      Nat.card ↥(R ⊓ centralizer ({z} : Set G)) = 2 ^ n := by
  obtain ⟨B, ι, hι, hBc, hBn, hK, hC, -⟩ := uc611_q8cc_core hR hz3 hzR hnt
  refine ⟨⟨((MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hK.symm)).symm⟩, ?_, ?_⟩
  · rw [hC]
    exact hBc
  · rw [hC]
    exact hBn

theorem uc611_q8cc_cyclic {R : Subgroup G} {n : ℕ} (hR : rankThreeIsQ8CentralCyclic R n) {z : G}
    (hz3 : z ^ 3 = 1) (hzR : z ∈ normalizer (R : Set G)) (hnt : ∃ r ∈ R, z * r ≠ r * z)
    {T : Subgroup G} (hTR : T ≤ R) (hT : IsMulCommutative T) (hzT : z ∈ normalizer (T : Set G)) :
    IsCyclic ↥T := by
  obtain ⟨B, -, -, hBc, -, -, -, hT'⟩ := uc611_q8cc_core hR hz3 hzR hnt
  haveI := hBc
  exact Subgroup.isCyclic_of_le (hT' T hTR hT hzT)

end CFSG.LocalAnalysis.UniquenessCase.UC6
