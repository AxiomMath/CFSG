module

public import CFSG.RankThree.PartOne.TAIL.QAbel
public import CFSG.RankThree.PartOne.TAIL.Frattini

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

variable {G : Type} [Group G]

theorem pow_class_two {a y u : G} (hau : a * u = u * a) (hyu : y * u = u * y)
    (hya : y * a = a * y * u) :
    ∀ n : ℕ, y ^ n * a = a * y ^ n * u ^ n ∧ (a * y) ^ n = a ^ n * y ^ n * u ^ (n.choose 2) := by
  have hun_a : ∀ m : ℕ, u ^ m * a = a * u ^ m := fun m =>
    (Commute.pow_left (show Commute u a from hau.symm) m).eq
  have hun_y : ∀ m : ℕ, u ^ m * y = y * u ^ m := fun m =>
    (Commute.pow_left (show Commute u y from hyu.symm) m).eq
  have hyn_u : ∀ m : ℕ, y ^ m * u = u * y ^ m := fun m =>
    (Commute.pow_left (show Commute y u from hyu) m).eq
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e1 : y ^ (n + 1) * a = a * y ^ (n + 1) * u ^ (n + 1) := by
      calc y ^ (n + 1) * a = y * (y ^ n * a) := by rw [pow_succ', mul_assoc]
        _ = y * (a * y ^ n * u ^ n) := by rw [ih1]
        _ = (y * a) * (y ^ n * u ^ n) := by simp only [mul_assoc]
        _ = (a * y * u) * (y ^ n * u ^ n) := by rw [hya]
        _ = a * y * (u * y ^ n) * u ^ n := by simp only [mul_assoc]
        _ = a * y * (y ^ n * u) * u ^ n := by rw [hyn_u n]
        _ = a * (y * y ^ n) * (u * u ^ n) := by simp only [mul_assoc]
        _ = a * y ^ (n + 1) * u ^ (n + 1) := by rw [← pow_succ', ← pow_succ']
    refine ⟨e1, ?_⟩
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    calc (a * y) ^ (n + 1) = (a * y) ^ n * (a * y) := by rw [pow_succ]
      _ = a ^ n * y ^ n * u ^ (n.choose 2) * (a * y) := by rw [ih2]
      _ = a ^ n * y ^ n * (u ^ (n.choose 2) * a) * y := by simp only [mul_assoc]
      _ = a ^ n * y ^ n * (a * u ^ (n.choose 2)) * y := by rw [hun_a]
      _ = a ^ n * (y ^ n * a) * u ^ (n.choose 2) * y := by simp only [mul_assoc]
      _ = a ^ n * (a * y ^ n * u ^ n) * u ^ (n.choose 2) * y := by rw [ih1]
      _ = a ^ n * a * y ^ n * (u ^ n * u ^ (n.choose 2)) * y := by simp only [mul_assoc]
      _ = a ^ n * a * y ^ n * (u ^ (n + n.choose 2) * y) := by
          rw [← pow_add]; simp only [mul_assoc]
      _ = a ^ n * a * y ^ n * (y * u ^ (n + n.choose 2)) := by rw [hun_y]
      _ = a ^ (n + 1) * y ^ (n + 1) * u ^ ((n + 1).choose 2) := by
          rw [hc, pow_succ a n, pow_succ y n]; simp only [mul_assoc]

@[expose] def powSub (Q : Subgroup G) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) : Subgroup G where
  carrier := {x | ∃ v ∈ Q, v ^ 7 = x}
  one_mem' := ⟨1, Q.one_mem, one_pow 7⟩
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v * w, Q.mul_mem hv hw, (show Commute v w from hQ v hv w hw).mul_pow 7⟩
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v⁻¹, Q.inv_mem hv, inv_pow v 7⟩

namespace SchemeHyp

variable [Finite G] {A B : Subgroup G} {c b d y₀ : G} {K M₀ : Subgroup G}
  (h : SchemeHyp G A B c b d y₀ K M₀)

include h in
theorem M₀_le_normalizer_Xs : M₀ ≤ Subgroup.normalizer (Xs A B : Set G) := by
  intro g hg
  have hgc : c * g = g * c := (Subgroup.mem_centralizer_singleton_iff.mp (h.M₀_cent hg)).symm
  have hgA : g ∈ Subgroup.normalizer (A : Set G) := h.mem_normalizer_A_of_comm hgc (h.M₀_nrm hg)
  exact mem_normalizer_of_conj_mem (Xs A B) fun x hx => conj_mem_Xs hgA (h.M₀_nrm hg) hx

variable {P : Subgroup G} (hP : PData A B y₀ P)

include h hP

theorem pow7_eq {j : ℤ} {v : G} (hv : v ∈ Qsub K P) : (c ^ j * v) ^ 7 = v ^ 7 := by
  have hvX : v ∈ Xs A B := hP.le_Xs (Qsub_le K P hv)
  have hcjA : c ^ j ∈ A := A.zpow_mem h.c_mem j
  have hinv : v⁻¹ ∈ Xs A B := (Xs A B).inv_mem hvX
  have hu : (c ^ j * v)⁻¹ * (v * c ^ j) ∈ B := by
    have := hinv.2.2 ((c ^ j)⁻¹) (A.inv_mem hcjA)
    have e : (c ^ j * v)⁻¹ * (v * c ^ j) = v⁻¹ * (c ^ j)⁻¹ * v⁻¹⁻¹ * (c ^ j)⁻¹⁻¹ := by group
    rw [e]
    exact this
  set u := (c ^ j * v)⁻¹ * (v * c ^ j) with hudef
  have hau : c ^ j * u = u * c ^ j := h.A_comm hcjA (h.B_le hu)
  have hyu : v * u = u * v := h.Q_comm hP hv (h.B_le_Q hP hu)
  have hya : v * c ^ j = c ^ j * v * u := by rw [hudef]; group
  have key := (pow_class_two hau hyu hya 7).2
  rw [key]
  have h1 : (c ^ j) ^ 7 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : c ^ ((7 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact h.c_pow
    rw [this, one_zpow]
  have h2 : u ^ (Nat.choose 7 2) = 1 := by
    have : Nat.choose 7 2 = 7 * 3 := by decide
    rw [this, pow_mul, h.B_pow hu, one_pow]
  rw [h1, h2, one_mul, mul_one]

theorem B_le_pow : B ≤ powSub (Qsub K P) (fun _ hx _ hy => h.Q_comm hP hx hy) := by
  set W := powSub (Qsub K P) (fun _ hx _ hy => h.Q_comm hP hx hy) with hW
  have hWB : W ≤ B := by
    rintro _ ⟨v, hv, rfl⟩
    exact h.Q_pow_mem_B hP v hv
  have hd' : y₀ ^ 7 ∈ W := ⟨y₀, h.y₀_mem_Q hP, rfl⟩
  have hd'B : y₀ ^ 7 ∈ B := hWB hd'
  have hd'1 : y₀ ^ 7 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h.y₀_orderOf]; norm_num)
  have hinv : ∀ n ∈ Subgroup.normalizer (P : Set G), ∀ w ∈ W, n * w * n⁻¹ ∈ W := by
    intro n hn w hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hvP : v ∈ P := Qsub_le K P hv
    have hnv : n * v * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hn v).mp hvP
    obtain ⟨j, q, hq, hnvq⟩ := h.P_eq_zpowers_mul_Q hP hnv
    refine ⟨q, hq, ?_⟩
    calc q ^ 7 = (c ^ j * q) ^ 7 := (h.pow7_eq hP hq).symm
      _ = (n * v * n⁻¹) ^ 7 := by rw [← hnvq]
      _ = n * v ^ 7 * n⁻¹ := by rw [conj_pow]
  have hfr := frattini h.M₀_le_normalizer_Xs ⟨hP.le_Xs, hP.pgroup, hP.idx⟩
  by_contra hne
  have hord7 : orderOf (y₀ ^ 7) = 7 := orderOf_eq_prime (h.B_pow hd'B) hd'1
  have hzcard : Nat.card (Subgroup.zpowers (y₀ ^ 7)) = 7 := by rw [Nat.card_zpowers, hord7]
  have hzle : Subgroup.zpowers (y₀ ^ 7) ≤ W := Subgroup.zpowers_le.mpr hd'
  have hWdvd : Nat.card W ∣ 7 ^ 2 := by
    have := Subgroup.card_dvd_of_le hWB
    rwa [h.B_card] at this
  have h7W : 7 ∣ Nat.card W := by
    have := Subgroup.card_dvd_of_le hzle
    rwa [hzcard] at this
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp hWdvd
  have hWeq : Subgroup.zpowers (y₀ ^ 7) = W := by
    rw [hj'] at h7W
    interval_cases j
    · exact absurd h7W (by decide)
    · exact Subgroup.eq_of_le_of_card_ge hzle (by rw [hzcard, hj']; norm_num)
    · exfalso
      apply hne
      have : W = B := Subgroup.eq_of_le_of_card_ge hWB (by rw [hj', h.B_card])
      rw [this]
  obtain ⟨g, hgM, hg⟩ := h.irr (y₀ ^ 7) hd'B hd'1
  obtain ⟨x, hx, n, hn, rfl⟩ := hfr g hgM
  have h1 : n * y₀ ^ 7 * n⁻¹ ∈ Subgroup.zpowers (y₀ ^ 7) := by
    rw [hWeq]
    exact hinv n hn _ hd'
  have h2 : x * (n * y₀ ^ 7 * n⁻¹) * x⁻¹ = n * y₀ ^ 7 * n⁻¹ :=
    hx.2.1 _ (Subgroup.zpowers_le.mpr hd'B h1)
  apply hg
  have e : x * n * y₀ ^ 7 * (x * n)⁻¹ = x * (n * y₀ ^ 7 * n⁻¹) * x⁻¹ := by group
  rw [e, h2]
  exact h1

theorem Q_pow_eq_one {v : G} (hv : v ∈ Qsub K P) (h1 : v ^ 7 = 1) : v ∈ B := by
  let ρ : ↥(Qsub K P) →* ↥B :=
    { toFun := fun x => ⟨x.1 ^ 7, h.Q_pow_mem_B hP x.1 x.2⟩
      map_one' := Subtype.ext (one_pow 7)
      map_mul' := fun x y => Subtype.ext (show (x.1 * y.1) ^ 7 = x.1 ^ 7 * y.1 ^ 7 from
        (show Commute x.1 y.1 from h.Q_comm hP x.2 y.2).mul_pow 7) }
  have hρ : Function.Surjective ρ := by
    intro β
    obtain ⟨w, hw, hwβ⟩ := h.B_le_pow hP β.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwβ⟩
  have hcard := Subgroup.card_ker_mul_card_of_surjective hρ
  rw [h.B_card, h.Q_card hP] at hcard
  have hker : Nat.card ρ.ker = 7 ^ 2 := by
    have e : Nat.card ρ.ker * 7 ^ 2 = 7 ^ 2 * 7 ^ 2 := by rw [hcard]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) e
  have hBle : B.subgroupOf (Qsub K P) ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (h.B_pow hx)
  have hBcard : Nat.card (B.subgroupOf (Qsub K P)) = 7 ^ 2 := by
    rw [← h.B_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.B_le_Q hP)).toEquiv
  have heq : B.subgroupOf (Qsub K P) = ρ.ker :=
    Subgroup.eq_of_le_of_card_ge hBle (by rw [hker, hBcard])
  have hmem : (⟨v, hv⟩ : ↥(Qsub K P)) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext h1
  rw [← heq] at hmem
  exact hmem

theorem P_pow_eq_one_iff {x : G} (hx : x ∈ P) : x ^ 7 = 1 ↔ x ∈ A := by
  constructor
  · intro h1
    obtain ⟨j, q, hq, rfl⟩ := h.P_eq_zpowers_mul_Q hP hx
    rw [h.pow7_eq hP hq] at h1
    exact A.mul_mem (A.zpow_mem h.c_mem j) (h.B_le (h.Q_pow_eq_one hP hq h1))
  · intro hxA
    exact h.A_pow hxA

end SchemeHyp

end CFSG.RankThree.PartOne.TAIL
