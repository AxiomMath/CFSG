module
public import CFSG.Literature.GL52Group
public import Mathlib.Algebra.Field.ZMod
public section
namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open Subgroup
variable {G : Type*} [Group G]

private lemma exists_scalar_orbit :
    ∀ a b a' b' : ZMod 7, a ≠ 0 → b ≠ 0 → a' ≠ 0 → b' ≠ 0 →
      ∃ i : Fin 3, ∃ j : Fin 2, ∃ t : Fin 7,
        ((t : ℕ) : ZMod 7) * (((-1 : ZMod 7) ^ (j : ℕ)) * a') = a ∧
        ((t : ℕ) : ZMod 7) * (((2 : ZMod 7) ^ (i : ℕ)) * b') = b := by
  let : Fintype (ZMod 7) := ZMod.fintype 7
  decide

private lemma conj_zpow_E49 {g x : G} {c : ℤ} (h : g * x * g⁻¹ = x ^ c) (k : ℤ) :
    g * x ^ k * g⁻¹ = x ^ (c * k) := by
  calc g * x ^ k * g⁻¹ = (MulAut.conj g) (x ^ k) := by rw [MulAut.conj_apply]
    _ = ((MulAut.conj g) x) ^ k := map_zpow (MulAut.conj g) x k
    _ = (x ^ c) ^ k := by rw [← h, MulAut.conj_apply]
    _ = x ^ (c * k) := by rw [zpow_mul]

private lemma map_conj_mul_E49 (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]; congr 1; ext x; simp [MulAut.conj_apply, mul_assoc]

@[simp] private lemma map_conj_one_E49 (H : Subgroup G) :
    H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩; simpa [MulAut.conj_apply] using hx
  · intro hy; exact ⟨y, hy, by simp⟩

theorem exists_conj_eq_of_E49 [Finite G] {R X Z D D' : Subgroup G} {ℓ κ : G}
    (hR : Nat.card R = 49) (hXR : X ≤ R) (hZR : Z ≤ R) (hDR : D ≤ R) (hD'R : D' ≤ R)
    (hX : Nat.card X = 7) (hZ : Nat.card Z = 7) (hD : Nat.card D = 7) (hD' : Nat.card D' = 7)
    (hXZ : X ≠ Z) (hDX : D ≠ X) (hDZ : D ≠ Z) (hD'X : D' ≠ X) (hD'Z : D' ≠ Z)
    (hℓx : ∀ x ∈ X, ℓ * x * ℓ⁻¹ = x) (hℓz : ∀ z ∈ Z, ℓ * z * ℓ⁻¹ = z ^ 2)
    (hκx : ∀ x ∈ X, κ * x * κ⁻¹ = x⁻¹) (hκz : ∀ z ∈ Z, κ * z * κ⁻¹ = z) :
    ∃ i j : ℕ, D = D'.map (MulAut.conj (ℓ ^ i * κ ^ j)).toMonoidHom := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hRcomm : ∀ a b : R, a * b = b * a :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := R) (p := 7)
      (by rw [hR]; norm_num)).is_comm.comm
  have hcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb => by
    simpa using hRcomm ⟨a, ha⟩ ⟨b, hb⟩
  have hXne : X ≠ ⊥ := by rw [Ne, Subgroup.eq_bot_iff_card, hX]; norm_num
  have hZne : Z ≠ ⊥ := by rw [Ne, Subgroup.eq_bot_iff_card, hZ]; norm_num
  obtain ⟨x, hxX, hx1⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one X).mp ((Subgroup.nontrivial_iff_ne_bot X).mpr hXne)
  obtain ⟨z, hzZ, hz1⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one Z).mp ((Subgroup.nontrivial_iff_ne_bot Z).mpr hZne)
  have hxgen : Subgroup.zpowers x = X :=
    (CFSG.Literature.GL52.eq_zpowers_of_card_prime Nat.prime_seven hX hxX hx1).symm
  have hzgen : Subgroup.zpowers z = Z :=
    (CFSG.Literature.GL52.eq_zpowers_of_card_prime Nat.prime_seven hZ hzZ hz1).symm
  have hxord : orderOf x = 7 := by rw [← Nat.card_zpowers, hxgen, hX]
  have hzord : orderOf z = 7 := by rw [← Nat.card_zpowers, hzgen, hZ]
  have hXZsup : X ⊔ Z = R := by
    have h7 : 7 ∣ Nat.card ↥(X ⊔ Z) := by
      simpa [hX] using Subgroup.card_dvd_of_le (le_sup_left : X ≤ X ⊔ Z)
    have hd : Nat.card ↥(X ⊔ Z) ∣ 7 ^ 2 := by
      simpa [hR] using Subgroup.card_dvd_of_le (sup_le hXR hZR)
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_seven).mp hd
    interval_cases k
    · rw [hk, pow_zero] at h7; norm_num at h7
    · exfalso
      have hsup : X ⊔ Z = X :=
        (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk, hX]; norm_num)).symm
      exact hXZ (Subgroup.eq_of_le_of_card_ge (hsup ▸ le_sup_right) (by rw [hX, hZ])).symm
    · exact Subgroup.eq_of_le_of_card_ge (sup_le hXR hZR) (by rw [hk, hR]; norm_num)
  have hrepr : ∀ w ∈ R, ∃ a b : ℤ, w = x ^ a * z ^ b := by
    let φ : (X.subgroupOf R) × (Z.subgroupOf R) →* R :=
      { toFun := fun p => (p.1 : R) * (p.2 : R), map_one' := by simp,
        map_mul' := fun p q => by
          show ((p.1 : R) * (q.1 : R)) * ((p.2 : R) * (q.2 : R)) =
            ((p.1 : R) * (p.2 : R)) * ((q.1 : R) * (q.2 : R))
          calc (p.1 : R) * (q.1 : R) * ((p.2 : R) * (q.2 : R))
              = (p.1 : R) * ((q.1 : R) * (p.2 : R)) * (q.2 : R) := by group
            _ = (p.1 : R) * ((p.2 : R) * (q.1 : R)) * (q.2 : R) := by
                  rw [hRcomm (q.1 : R) (p.2 : R)]
            _ = (p.1 : R) * (p.2 : R) * ((q.1 : R) * (q.2 : R)) := by group }
    have htop : φ.range = ⊤ := by
      have hXle : X.subgroupOf R ≤ φ.range := fun y hy => ⟨(⟨y, hy⟩, 1), by simp [φ]⟩
      have hZle : Z.subgroupOf R ≤ φ.range := fun y hy => ⟨(1, ⟨y, hy⟩), by simp [φ]⟩
      have hle : X.subgroupOf R ⊔ Z.subgroupOf R ≤ φ.range := sup_le hXle hZle
      rw [← Subgroup.subgroupOf_sup hXR hZR, hXZsup, Subgroup.subgroupOf_self] at hle
      exact top_le_iff.mp hle
    intro w hw
    obtain ⟨p, hp⟩ := show (⟨w, hw⟩ : R) ∈ φ.range by
      rw [htop]; exact Subgroup.mem_top _
    have hp1zp : ((p.1 : R) : G) ∈ Subgroup.zpowers x := by rw [hxgen]; exact p.1.2
    have hp2zp : ((p.2 : R) : G) ∈ Subgroup.zpowers z := by rw [hzgen]; exact p.2.2
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hp1zp
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp hp2zp
    refine ⟨a, b, ?_⟩
    have hval : ((p.1 : R) : G) * ((p.2 : R) : G) = w := by
      simpa [φ] using congrArg (fun t : R => (t : G)) hp
    rw [← hval, ← ha, ← hb]
  have hcoords : ∀ {E : Subgroup G}, E ≤ R → Nat.card E = 7 → E ≠ X → E ≠ Z →
      ∃ (w : G) (a b : ℤ), Subgroup.zpowers w = E ∧ w = x ^ a * z ^ b ∧
        (a : ZMod 7) ≠ 0 ∧ (b : ZMod 7) ≠ 0 := by
    intro E hER hE7 hEX hEZ
    have hEbot : E ≠ ⊥ := by rw [Ne, Subgroup.eq_bot_iff_card, hE7]; norm_num
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEbot
    have hwE : (u : G) ∈ E := u.2
    have hw1 : (u : G) ≠ 1 := by simpa using hu1
    have hEgen : Subgroup.zpowers (u : G) = E :=
      (CFSG.Literature.GL52.eq_zpowers_of_card_prime Nat.prime_seven hE7 hwE hw1).symm
    obtain ⟨a, b, hw⟩ := hrepr (u : G) (hER hwE)
    have hxX' : x ∈ X := hxgen ▸ Subgroup.mem_zpowers x
    have hzZ' : z ∈ Z := hzgen ▸ Subgroup.mem_zpowers z
    have ha0 : (a : ZMod 7) ≠ 0 := by
      intro ha0
      have hxa : x ^ a = 1 := by
        have hdvd : (orderOf x : ℤ) ∣ a := by
          rw [hxord]
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd a 7).mp ha0
        exact orderOf_dvd_iff_zpow_eq_one.mp hdvd
      have hwZ : (u : G) ∈ Z := by
        rw [hw, hxa, one_mul]
        exact Subgroup.zpow_mem (K := Z) hzZ' b
      exact hEZ (Subgroup.eq_of_le_of_card_ge
        (hEgen ▸ Subgroup.zpowers_le.mpr hwZ) (by rw [hE7, hZ]))
    have hb0 : (b : ZMod 7) ≠ 0 := by
      intro hb0
      have hzb : z ^ b = 1 := by
        have hdvd : (orderOf z : ℤ) ∣ b := by
          rw [hzord]
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd b 7).mp hb0
        exact orderOf_dvd_iff_zpow_eq_one.mp hdvd
      have hwX : (u : G) ∈ X := by
        rw [hw, hzb, mul_one]
        exact Subgroup.zpow_mem (K := X) hxX' a
      exact hEX (Subgroup.eq_of_le_of_card_ge
        (hEgen ▸ Subgroup.zpowers_le.mpr hwX) (by rw [hE7, hX]))
    exact ⟨u, a, b, hEgen, hw, ha0, hb0⟩
  obtain ⟨w, a, b, hDgen, hw, ha0, hb0⟩ := hcoords hDR hD hDX hDZ
  obtain ⟨w', a', b', hD'gen, hw', ha0', hb0'⟩ := hcoords hD'R hD' hD'X hD'Z
  obtain ⟨i, j, t, hta, htb⟩ := exists_scalar_orbit (a : ZMod 7) (b : ZMod 7)
    (a' : ZMod 7) (b' : ZMod 7) ha0 hb0 ha0' hb0'
  let T : ℕ := (t : ℕ)
  have hword : orderOf w = 7 := by rw [← Nat.card_zpowers, hDgen, hD]
  have hw'ord : orderOf w' = 7 := by rw [← Nat.card_zpowers, hD'gen, hD']
  let m : G := ℓ ^ (i : ℕ) * κ ^ (j : ℕ)
  have hℓxi : ℓ ^ (i : ℕ) * x * (ℓ ^ (i : ℕ))⁻¹ = x := by
    induction (i : ℕ) with
    | zero => simp
    | succ k ih =>
        calc ℓ ^ (k + 1) * x * (ℓ ^ (k + 1))⁻¹
            = ℓ * (ℓ ^ k * x * (ℓ ^ k)⁻¹) * ℓ⁻¹ := by group
          _ = ℓ * x * ℓ⁻¹ := by rw [ih]
          _ = x := hℓx x hxX
  have hℓzi : ℓ ^ (i : ℕ) * z * (ℓ ^ (i : ℕ))⁻¹ = z ^ ((2 : ℤ) ^ (i : ℕ)) := by
    induction (i : ℕ) with
    | zero => simp
    | succ k ih =>
        calc ℓ ^ (k + 1) * z * (ℓ ^ (k + 1))⁻¹
            = ℓ * (ℓ ^ k * z * (ℓ ^ k)⁻¹) * ℓ⁻¹ := by group
          _ = ℓ * z ^ ((2 : ℤ) ^ k) * ℓ⁻¹ := by rw [ih]
          _ = z ^ ((2 : ℤ) * (2 : ℤ) ^ k) := by
                rw [conj_zpow_E49 (c := 2) (by simpa using hℓz z hzZ)]
          _ = z ^ ((2 : ℤ) ^ (k + 1)) := by congr 1; rw [pow_succ]; ring
  have hκxj : κ ^ (j : ℕ) * x * (κ ^ (j : ℕ))⁻¹ = x ^ ((-1 : ℤ) ^ (j : ℕ)) := by
    induction (j : ℕ) with
    | zero => simp
    | succ k ih =>
        calc κ ^ (k + 1) * x * (κ ^ (k + 1))⁻¹
            = κ * (κ ^ k * x * (κ ^ k)⁻¹) * κ⁻¹ := by group
          _ = κ * x ^ ((-1 : ℤ) ^ k) * κ⁻¹ := by rw [ih]
          _ = x ^ ((-1 : ℤ) * (-1 : ℤ) ^ k) := by
                rw [conj_zpow_E49 (c := -1) (by simpa using hκx x hxX)]
          _ = x ^ ((-1 : ℤ) ^ (k + 1)) := by congr 1; rw [pow_succ]; ring
  have hκzj : κ ^ (j : ℕ) * z * (κ ^ (j : ℕ))⁻¹ = z := by
    induction (j : ℕ) with
    | zero => simp
    | succ k ih =>
        calc κ ^ (k + 1) * z * (κ ^ (k + 1))⁻¹
            = κ * (κ ^ k * z * (κ ^ k)⁻¹) * κ⁻¹ := by group
          _ = κ * z * κ⁻¹ := by rw [ih]
          _ = z := hκz z hzZ
  have hmx : m * x * m⁻¹ = x ^ ((-1 : ℤ) ^ (j : ℕ)) := by
    have h1 : m * x * m⁻¹
        = ℓ ^ (i : ℕ) * (κ ^ (j : ℕ) * x * (κ ^ (j : ℕ))⁻¹) * (ℓ ^ (i : ℕ))⁻¹ := by
      simp only [m]; group
    rw [h1, hκxj, conj_zpow_E49 (c := 1) (by simpa using hℓxi), one_mul]
  have hmz : m * z * m⁻¹ = z ^ ((2 : ℤ) ^ (i : ℕ)) := by
    have h1 : m * z * m⁻¹
        = ℓ ^ (i : ℕ) * (κ ^ (j : ℕ) * z * (κ ^ (j : ℕ))⁻¹) * (ℓ ^ (i : ℕ))⁻¹ := by
      simp only [m]; group
    rw [h1, hκzj]; simpa using hℓzi
  have hmw' : m * w' * m⁻¹
      = x ^ (((-1 : ℤ) ^ (j : ℕ)) * a') * z ^ (((2 : ℤ) ^ (i : ℕ)) * b') := by
    have h1 : m * w' * m⁻¹ = (m * x ^ a' * m⁻¹) * (m * z ^ b' * m⁻¹) := by
      rw [hw']; group
    rw [h1, conj_zpow_E49 hmx, conj_zpow_E49 hmz]
  have hTA : ((T : ℤ) * (((-1 : ℤ) ^ (j : ℕ)) * a')) ≡ a [ZMOD 7] := by
    refine (ZMod.intCast_eq_intCast_iff _ _ 7).mp ?_
    push_cast [T]; exact hta
  have hTB : ((T : ℤ) * (((2 : ℤ) ^ (i : ℕ)) * b')) ≡ b [ZMOD 7] := by
    refine (ZMod.intCast_eq_intCast_iff _ _ 7).mp ?_
    push_cast [T]; exact htb
  have hxT : x ^ ((((-1 : ℤ) ^ (j : ℕ)) * a') * (T : ℤ)) = x ^ a := by
    rw [zpow_eq_zpow_iff_modEq, hxord]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hTA
  have hzT : z ^ ((((2 : ℤ) ^ (i : ℕ)) * b') * (T : ℤ)) = z ^ b := by
    rw [zpow_eq_zpow_iff_modEq, hzord]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hTB
  have hxz : Commute x z := hcomm x (hXR hxX) z (hZR hzZ)
  have hpow : (m * w' * m⁻¹) ^ T = w := by
    rw [hmw', hw, ← zpow_natCast,
      Commute.mul_zpow (hxz.zpow_zpow _ _) (T : ℤ), ← zpow_mul, ← zpow_mul, hxT, hzT]
  have hmem : w ∈ Subgroup.zpowers (m * w' * m⁻¹) := by
    rw [← hpow]
    exact Subgroup.pow_mem (K := Subgroup.zpowers (m * w' * m⁻¹)) (Subgroup.mem_zpowers _) T
  have hAord : orderOf (m * w' * m⁻¹) = 7 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj m) w'
    rwa [MulAut.conj_apply, hw'ord] at h
  have hfin : Subgroup.zpowers w = Subgroup.zpowers (m * w' * m⁻¹) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hAord, hword]
  refine ⟨(i : ℕ), (j : ℕ), ?_⟩
  calc D = Subgroup.zpowers w := hDgen.symm
    _ = Subgroup.zpowers (m * w' * m⁻¹) := hfin
    _ = (Subgroup.zpowers w').map (MulAut.conj m).toMonoidHom := by
          rw [MonoidHom.map_zpowers]; rfl
    _ = D'.map (MulAut.conj m).toMonoidHom := by rw [hD'gen]

theorem normalizer_le_of_E49_orbit [Finite G] {M R X Z : Subgroup G} {ℓ κ : G}
    (hR : Nat.card R = 49) (hXR : X ≤ R) (hZR : Z ≤ R) (hX : Nat.card X = 7) (hZ : Nat.card Z = 7)
    (hXZ : X ≠ Z) (hℓM : ℓ ∈ M) (hκM : κ ∈ M)
    (hℓR : ℓ ∈ normalizer (R : Set G)) (hκR : κ ∈ normalizer (R : Set G))
    (hℓx : ∀ x ∈ X, ℓ * x * ℓ⁻¹ = x) (hℓz : ∀ z ∈ Z, ℓ * z * ℓ⁻¹ = z ^ 2)
    (hκx : ∀ x ∈ X, κ * x * κ⁻¹ = x⁻¹) (hκz : ∀ z ∈ Z, κ * z * κ⁻¹ = z)
    (hNX : normalizer (X : Set G) ≤ M) (hNZ : normalizer (Z : Set G) ≤ M)
    (hfixZ : ∀ m ∈ M, m ∈ normalizer (R : Set G) → Z.map (MulAut.conj m).toMonoidHom = Z)
    (hswap : ∀ h : G, X.map (MulAut.conj h).toMonoidHom = Z → h ∈ M) :
    normalizer (R : Set G) ≤ M := by
  intro w hwR
  by_contra hwM
  let D : Subgroup G := X.map (MulAut.conj w).toMonoidHom
  let D' : Subgroup G := Z.map (MulAut.conj w).toMonoidHom
  have hRw : R.map (MulAut.conj w).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hwR
  have hDR : D ≤ R := (Subgroup.map_mono hXR).trans_eq hRw
  have hD'R : D' ≤ R := (Subgroup.map_mono hZR).trans_eq hRw
  have hDcard : Nat.card D = 7 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective, hX]
  have hD'card : Nat.card D' = 7 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective, hZ]
  have hDX : D ≠ X := fun h => hwM (hNX (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h))
  have hDZ : D ≠ Z := fun h => hwM (hswap w h)
  have hD'Z : D' ≠ Z := fun h => hwM (hNZ (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h))
  have hD'X : D' ≠ X := by
    intro h
    have hmap : X.map (MulAut.conj w⁻¹).toMonoidHom = Z := by
      have h' := congrArg (fun H : Subgroup G => H.map (MulAut.conj w⁻¹).toMonoidHom) h
      rw [map_conj_mul_E49, inv_mul_cancel, map_conj_one_E49] at h'
      exact h'.symm
    exact hwM (by simpa using M.inv_mem (hswap w⁻¹ hmap))
  obtain ⟨i, j, hij⟩ := exists_conj_eq_of_E49 hR hXR hZR hDR hD'R hX hZ hDcard hD'card
    hXZ hDX hDZ hD'X hD'Z hℓx hℓz hκx hκz
  let m : G := ℓ ^ i * κ ^ j
  have hmM : m ∈ M := M.mul_mem (M.pow_mem hℓM i) (M.pow_mem hκM j)
  have hmR : m ∈ normalizer (R : Set G) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hℓR i) (Subgroup.pow_mem _ hκR j)
  let h : G := w⁻¹ * m * w
  have hhR : h ∈ normalizer (R : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hwR) hmR) hwR
  have hhZ : Z.map (MulAut.conj h).toMonoidHom = X := by
    have h1 : h = w⁻¹ * (m * w) := by simp only [h]; group
    calc Z.map (MulAut.conj h).toMonoidHom
        = Z.map (MulAut.conj (w⁻¹ * (m * w))).toMonoidHom := by rw [h1]
      _ = (Z.map (MulAut.conj (m * w)).toMonoidHom).map (MulAut.conj w⁻¹).toMonoidHom :=
            (map_conj_mul_E49 Z (m * w) w⁻¹).symm
      _ = ((Z.map (MulAut.conj w).toMonoidHom).map (MulAut.conj m).toMonoidHom).map
            (MulAut.conj w⁻¹).toMonoidHom := by rw [map_conj_mul_E49 Z w m]
      _ = D.map (MulAut.conj w⁻¹).toMonoidHom := by rw [← hij]
      _ = X := by
            calc (X.map (MulAut.conj w).toMonoidHom).map (MulAut.conj w⁻¹).toMonoidHom
                = X.map (MulAut.conj (w⁻¹ * w)).toMonoidHom := map_conj_mul_E49 X w w⁻¹
              _ = X := by rw [inv_mul_cancel]; exact map_conj_one_E49 X
  have hhX : X.map (MulAut.conj h⁻¹).toMonoidHom = Z := by
    have h' := congrArg (fun H : Subgroup G => H.map (MulAut.conj h⁻¹).toMonoidHom) hhZ
    rw [map_conj_mul_E49, inv_mul_cancel, map_conj_one_E49] at h'
    exact h'.symm
  have hhM : h ∈ M := by
    have := hswap h⁻¹ hhX
    simpa using M.inv_mem this
  exact hXZ (hhZ.symm.trans (hfixZ h hhM hhR))
