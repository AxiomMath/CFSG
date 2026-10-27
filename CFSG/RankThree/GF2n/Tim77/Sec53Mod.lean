module

public import CFSG.RankThree.GF2n.Tim77.InvolAutD
public import CFSG.RankThree.GF2n.Tim77Prop24
public import CFSG.RankThree.GF2n.Tim77Prop24TwoD
public import CFSG.CGT.T75N.BenderCenter
public import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75

theorem sec53_mem_or_of_index_two {G : Type} [Group G] {A L : Subgroup G}
    (hq : L.relIndex A = 2) {a x : G} (ha : a ∈ A) (haL : a ∉ L) (hx : x ∈ A) :
    x ∈ L ∨ a⁻¹ * x ∈ L := by
  by_cases hxL : x ∈ L
  · exact Or.inl hxL
  · refine Or.inr ?_
    have h := (Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf A) hq
      (a := (⟨a, ha⟩ : ↥A)⁻¹) (b := ⟨x, hx⟩)).mpr (by
        simp [Subgroup.mem_subgroupOf, haL, hxL])
    simpa [Subgroup.mem_subgroupOf] using h

theorem sec53_ncard_le_four {α : Type*} (x₁ x₂ x₃ x₄ : α) :
    ({x₁, x₂, x₃, x₄} : Set α).ncard ≤ 4 := by
  have h1 := Set.ncard_insert_le x₁ ({x₂, x₃, x₄} : Set α)
  have h2 := Set.ncard_insert_le x₂ ({x₃, x₄} : Set α)
  have h3 := Set.ncard_insert_le x₃ ({x₄} : Set α)
  rw [Set.ncard_singleton] at h3
  omega

theorem sec53_ncard_le_six {α : Type*} (x₁ x₂ x₃ x₄ x₅ x₆ : α) :
    ({x₁, x₂, x₃, x₄, x₅, x₆} : Set α).ncard ≤ 6 := by
  have h1 := Set.ncard_insert_le x₁ ({x₂, x₃, x₄, x₅, x₆} : Set α)
  have h2 := Set.ncard_insert_le x₂ ({x₃, x₄, x₅, x₆} : Set α)
  have h3 := Set.ncard_insert_le x₃ ({x₄, x₅, x₆} : Set α)
  have h4 := Set.ncard_insert_le x₄ ({x₅, x₆} : Set α)
  have h5 := Set.ncard_insert_le x₅ ({x₆} : Set α)
  rw [Set.ncard_singleton] at h5
  omega

theorem sec53_cancel_conj {G : Type} [Group G] {w g v : G} (hgw : g * w = w * g)
    (h : w * v * w⁻¹ = g * (w * v * w⁻¹) * g⁻¹) : g * v = v * g := by
  have h1 : w * v * w⁻¹ = w * (g * v * g⁻¹) * w⁻¹ := by
    calc w * v * w⁻¹ = g * (w * v * w⁻¹) * g⁻¹ := h
      _ = (g * w) * v * (g * w)⁻¹ := by group
      _ = (w * g) * v * (w * g)⁻¹ := by rw [hgw]
      _ = w * (g * v * g⁻¹) * w⁻¹ := by group
  have h2 : v = g * v * g⁻¹ := mul_left_cancel (mul_right_cancel h1)
  calc g * v = (g * v * g⁻¹) * g := by group
    _ = v * g := by rw [← h2]

theorem sec53_conj_ne {G : Type} [Group G] [Finite G] {A Ab L Lb M : Subgroup G}
    (S : Prop24Setup A Ab L Lb M) {a b : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab)
    (hbL : b ∉ Lb) {v : G} (hv : v ∈ M) (hv1 : v ≠ 1) {i j : ℕ} (hij : i < j)
    (hj : j < orderOf (a * b)) :
    (a * b) ^ i * v * ((a * b) ^ i)⁻¹ ≠ (a * b) ^ j * v * ((a * b) ^ j)⁻¹ := by
  intro hE
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  have hdpos : 0 < d := by omega
  have hdlt : d < orderOf (a * b) := by omega
  have hpow : (a * b) ^ (i + d) = (a * b) ^ d * (a * b) ^ i := by
    rw [add_comm, pow_add]
  have hgw : (a * b) ^ d * (a * b) ^ i = (a * b) ^ i * (a * b) ^ d := by
    rw [← pow_add, ← pow_add, add_comm]
  have hE' : (a * b) ^ i * v * ((a * b) ^ i)⁻¹ =
      (a * b) ^ d * (a * b) ^ i * v * ((a * b) ^ d * (a * b) ^ i)⁻¹ := by
    rw [← hpow]
    exact hE
  have hcomm : (a * b) ^ d * v = v * (a * b) ^ d := by
    refine sec53_cancel_conj hgw ?_
    calc (a * b) ^ i * v * ((a * b) ^ i)⁻¹
        = (a * b) ^ d * (a * b) ^ i * v * ((a * b) ^ d * (a * b) ^ i)⁻¹ := hE'
      _ = (a * b) ^ d * ((a * b) ^ i * v * ((a * b) ^ i)⁻¹) * ((a * b) ^ d)⁻¹ := by
          group
  have hj' : (a * b) ^ (d : ℤ) ≠ 1 := by
    rw [zpow_natCast]
    intro h1
    have h2 := Nat.le_of_dvd hdpos (orderOf_dvd_of_pow_eq_one h1)
    omega
  have hvc : (a * b) ^ (d : ℤ) * v = v * (a * b) ^ (d : ℤ) := by
    rw [zpow_natCast]
    exact hcomm
  exact hv1 (invAutD_rot_fix S ha haL hb (S.odd_orderOf_mul ha haL hb hbL)
    (pow_orderOf_eq_one _) hj' hv hvc)

theorem sec53_orbit_three {G : Type} [Group G] [Finite G] {A Ab L Lb M : Subgroup G}
    (S : Prop24Setup A Ab L Lb M) {a b : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab)
    (hbL : b ∉ Lb) {N : Subgroup G} (hNM : N ≤ M) (hN1 : N ≠ ⊥) (hN4 : Nat.card N ≤ 4)
    (hnorm : a * b ∈ Subgroup.normalizer (N : Set G)) : (a * b) ^ 3 = 1 := by
  obtain ⟨⟨v, hvN⟩, hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
  have hv1 : v ≠ 1 := fun h => hv1' (Subtype.ext h)
  have hvM : v ∈ M := hNM hvN
  have hodd : Odd (orderOf (a * b)) := S.odd_orderOf_mul ha haL hb hbL
  have hnpos : 0 < orderOf (a * b) := orderOf_pos _
  have hn1 : orderOf (a * b) ≠ 1 := by
    intro h1
    have hab : a * b = 1 := orderOf_eq_one_iff.mp h1
    have hba : b = a := by
      rw [eq_inv_of_mul_eq_one_right hab, inv_eq_of_mul_eq_one_right (S.sq_A ha)]
    have hbA : b ∈ A ⊓ Ab := Subgroup.mem_inf.mpr ⟨by rw [hba]; exact ha, hb⟩
    rw [S.inf_eq_bot, Subgroup.mem_bot] at hbA
    exact hbL (by rw [hbA]; exact Lb.one_mem)
  have hconj_mem : ∀ k : ℕ, (a * b) ^ k * v * ((a * b) ^ k)⁻¹ ∈ N := fun k =>
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (N : Set G)).pow_mem hnorm k) v).mp hvN
  have hconj_ne_one : ∀ k : ℕ, (a * b) ^ k * v * ((a * b) ^ k)⁻¹ ≠ 1 := by
    intro k h
    apply hv1
    calc v = ((a * b) ^ k)⁻¹ * ((a * b) ^ k * v * ((a * b) ^ k)⁻¹) * (a * b) ^ k := by
          group
      _ = 1 := by rw [h]; group
  have hF : Function.Injective (fun o : Option (Fin (orderOf (a * b))) =>
      (Option.elim o (⟨1, N.one_mem⟩ : ↥N) fun i =>
        (⟨(a * b) ^ (i : ℕ) * v * ((a * b) ^ (i : ℕ))⁻¹, hconj_mem (i : ℕ)⟩ : ↥N))) := by
    rintro (_ | i) (_ | j) hop
    · rfl
    · have h' : (1 : G) = (a * b) ^ (j : ℕ) * v * ((a * b) ^ (j : ℕ))⁻¹ :=
        congrArg Subtype.val hop
      exact absurd h'.symm (hconj_ne_one j)
    · have h' : (a * b) ^ (i : ℕ) * v * ((a * b) ^ (i : ℕ))⁻¹ = (1 : G) :=
        congrArg Subtype.val hop
      exact absurd h' (hconj_ne_one i)
    · have h' : (a * b) ^ (i : ℕ) * v * ((a * b) ^ (i : ℕ))⁻¹ =
          (a * b) ^ (j : ℕ) * v * ((a * b) ^ (j : ℕ))⁻¹ := congrArg Subtype.val hop
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
      · exact absurd h' (sec53_conj_ne S ha haL hb hbL hvM hv1 h j.isLt)
      · exact congrArg some (Fin.ext h)
      · exact absurd h'.symm (sec53_conj_ne S ha haL hb hbL hvM hv1 h i.isLt)
  have hcard := Nat.card_le_card_of_injective _ hF
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hcard
  have hn3 : orderOf (a * b) ≤ 3 := by omega
  have h3 : orderOf (a * b) = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  calc (a * b) ^ 3 = (a * b) ^ orderOf (a * b) := by rw [h3]
    _ = 1 := pow_orderOf_eq_one _

theorem sec53_cube_of_inner {G : Type} [Group G] [Finite G] {A Ab L Lb M : Subgroup G}
    (S : Prop24Setup A Ab L Lb M) {y : G}
    (hyX : y ∈ Subgroup.normalizer ((A ⊔ Ab : Subgroup G) : Set G))
    (hyM : ∀ x ∈ A ⊔ Ab, y * x * y⁻¹ * x⁻¹ ∈ M)
    (hyL : ∃ l ∈ L, y * l * y⁻¹ ≠ l)
    (hL2 : ∀ l ∈ L, ∀ l' ∈ L, y * l * y⁻¹ * l⁻¹ = 1 ∨ y * l' * y⁻¹ * l'⁻¹ = 1 ∨
      y * l * y⁻¹ * l⁻¹ = y * l' * y⁻¹ * l'⁻¹)
    {a b : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab) (hbL : b ∉ Lb) :
    (a * b) ^ 3 = 1 := by
  have hyM' : ∀ m ∈ M, y * m * y⁻¹ ∈ M := by
    intro m hm
    have h1 := hyM m (S.M_le_X hm)
    have h2 : y * m * y⁻¹ = (y * m * y⁻¹ * m⁻¹) * m := by group
    rw [h2]
    exact M.mul_mem h1 hm
  have hnormM : ∀ x ∈ A ⊔ Ab, ∀ m : G, m ∈ M ↔ x * m * x⁻¹ ∈ M := fun x hx m =>
    Subgroup.mem_normalizer_iff.mp (S.sup_le_normalizer_M hx) m
  have hmul : ∀ m ∈ M, ∀ n ∈ M, y * (m * n) * y⁻¹ * (m * n)⁻¹ =
      (y * m * y⁻¹ * m⁻¹) * (y * n * y⁻¹ * n⁻¹) := by
    intro m hm n hn
    have hφn : y * n * y⁻¹ * n⁻¹ ∈ M := hyM n (S.M_le_X hn)
    calc y * (m * n) * y⁻¹ * (m * n)⁻¹
        = (y * m * y⁻¹) * (y * n * y⁻¹ * n⁻¹) * m⁻¹ := by group
      _ = (y * m * y⁻¹) * ((y * n * y⁻¹ * n⁻¹) * m⁻¹) := by group
      _ = (y * m * y⁻¹) * (m⁻¹ * (y * n * y⁻¹ * n⁻¹)) := by
          rw [S.comm_M hφn (M.inv_mem hm)]
      _ = (y * m * y⁻¹ * m⁻¹) * (y * n * y⁻¹ * n⁻¹) := by group
  have hequiv : ∀ x ∈ A ⊔ Ab, ∀ m ∈ M,
      y * (x * m * x⁻¹) * y⁻¹ * (x * m * x⁻¹)⁻¹ = x * (y * m * y⁻¹ * m⁻¹) * x⁻¹ := by
    intro x hx m hm
    have hc : y * x * y⁻¹ * x⁻¹ ∈ M := hyM x hx
    have hq : x * (y * m * y⁻¹) * x⁻¹ ∈ M := (hnormM x hx _).mp (hyM' m hm)
    have hcq : (y * x * y⁻¹ * x⁻¹) * (x * (y * m * y⁻¹) * x⁻¹) =
        (x * (y * m * y⁻¹) * x⁻¹) * (y * x * y⁻¹ * x⁻¹) := S.comm_M hc hq
    calc y * (x * m * x⁻¹) * y⁻¹ * (x * m * x⁻¹)⁻¹
        = ((y * x * y⁻¹ * x⁻¹) * (x * (y * m * y⁻¹) * x⁻¹)) * (y * x * y⁻¹ * x⁻¹)⁻¹ *
            (x * m * x⁻¹)⁻¹ := by group
      _ = (x * (y * m * y⁻¹) * x⁻¹) * (x * m * x⁻¹)⁻¹ := by
          rw [hcq]
          group
      _ = x * (y * m * y⁻¹ * m⁻¹) * x⁻¹ := by group
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, ∀ z : G, z ∈ N ↔ ∃ m ∈ M, z = y * m * y⁻¹ * m⁻¹ := by
    refine ⟨{ carrier := {z | ∃ m ∈ M, z = y * m * y⁻¹ * m⁻¹}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun z => Iff.rfl⟩
    · rintro _ _ ⟨m, hm, rfl⟩ ⟨n, hn, rfl⟩
      exact ⟨m * n, M.mul_mem hm hn, (hmul m hm n hn).symm⟩
    · exact ⟨1, M.one_mem, by group⟩
    · rintro _ ⟨m, hm, rfl⟩
      refine ⟨m⁻¹, M.inv_mem hm, ?_⟩
      have h := hmul m hm m⁻¹ (M.inv_mem hm)
      rw [mul_inv_cancel, show y * 1 * y⁻¹ * (1 : G)⁻¹ = 1 by group] at h
      exact (eq_inv_of_mul_eq_one_right h.symm).symm
  have hNM : N ≤ M := by
    intro z hz
    obtain ⟨m, hm, rfl⟩ := (hN z).mp hz
    exact hyM m (S.M_le_X hm)
  have hNconj : ∀ x ∈ A ⊔ Ab, ∀ z ∈ N, x * z * x⁻¹ ∈ N := by
    intro x hx z hz
    obtain ⟨m, hm, rfl⟩ := (hN z).mp hz
    rw [hN]
    exact ⟨x * m * x⁻¹, (hnormM x hx m).mp hm, (hequiv x hx m hm).symm⟩
  have hab : a * b ∈ A ⊔ Ab :=
    (A ⊔ Ab).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hnormN : a * b ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hNconj _ hab z hz
    · intro hz
      have h := hNconj _ ((A ⊔ Ab).inv_mem hab) _ hz
      have e : (a * b)⁻¹ * (a * b * z * (a * b)⁻¹) * (a * b)⁻¹⁻¹ = z := by group
      rwa [e] at h
  obtain ⟨l₀, hl₀, hl₀ne⟩ := hyL
  obtain ⟨u, hu⟩ : ∃ u : G, u = y * l₀ * y⁻¹ * l₀⁻¹ := ⟨_, rfl⟩
  have huN : u ∈ N := (hN u).mpr ⟨l₀, S.L_le_M hl₀, hu⟩
  have hu1 : u ≠ 1 := by
    intro h
    apply hl₀ne
    rw [hu] at h
    calc y * l₀ * y⁻¹ = (y * l₀ * y⁻¹ * l₀⁻¹) * l₀ := by group
      _ = l₀ := by rw [h, one_mul]
  have hLcase : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ = 1 ∨ y * l * y⁻¹ * l⁻¹ = u := by
    intro l hl
    rcases hL2 l hl l₀ hl₀ with h | h | h
    · exact Or.inl h
    · exact absurd (hu.trans h) hu1
    · exact Or.inr (h.trans hu.symm)
  obtain ⟨k, hkX, hk⟩ := S.exists_conj_eq
  obtain ⟨w, hw⟩ : ∃ w : G, w = k * u * k⁻¹ := ⟨_, rfl⟩
  have hLbcase : ∀ lb ∈ Lb, y * lb * y⁻¹ * lb⁻¹ = 1 ∨ y * lb * y⁻¹ * lb⁻¹ = w := by
    intro lb hlb
    have hlbc : lb ∈ conjSubgroup k A := by
      rw [← hk]
      exact S.Lb_le hlb
    obtain ⟨l', hl'⟩ : ∃ l' : G, l' = k⁻¹ * lb * k := ⟨_, rfl⟩
    have hl'A : l' ∈ A := by
      rw [hl']
      exact mem_conjSubgroup.mp hlbc
    have hl'M : l' ∈ M := by
      rw [hl']
      have h := (hnormM k⁻¹ ((A ⊔ Ab).inv_mem hkX) lb).mp (S.Lb_le_M hlb)
      rwa [inv_inv] at h
    have hl'L : l' ∈ L := by
      rw [← S.inf_M]
      exact Subgroup.mem_inf.mpr ⟨hl'A, hl'M⟩
    have e : lb = k * l' * k⁻¹ := by
      rw [hl']
      group
    rw [e, hequiv k hkX l' hl'M]
    rcases hLcase l' hl'L with h | h
    · left
      rw [h, mul_one, mul_inv_cancel]
    · right
      rw [h, hw]
  have hsub : (N : Set G) ⊆ ({1, u, w, u * w} : Set G) := by
    intro z hz
    obtain ⟨m, hm, rfl⟩ := (hN z).mp hz
    obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hm
    rw [hmul l (S.L_le_M hl) lb (S.Lb_le_M hlb)]
    rcases hLcase l hl with h1 | h1 <;> rcases hLbcase lb hlb with h2 | h2 <;>
      rw [h1, h2] <;> simp
  have hcardN : Nat.card N ≤ 4 := by
    have h1 : Nat.card N = (N : Set G).ncard := Nat.card_coe_set_eq (N : Set G)
    rw [h1]
    exact (Set.ncard_le_ncard hsub).trans (sec53_ncard_le_four _ _ _ _)
  have hN1 : N ≠ ⊥ := by
    intro h
    apply hu1
    have huA := huN
    rw [h] at huA
    exact Subgroup.mem_bot.mp huA
  exact sec53_orbit_three S ha haL hb hbL hNM hN1 hcardN hnormN

theorem sec53_card_quot_le_six {G : Type} [Group G] [Finite G] {A Ab L Lb M : Subgroup G}
    (S : Prop24Setup A Ab L Lb M) [(M.subgroupOf (A ⊔ Ab)).Normal] (hq : L.relIndex A = 2)
    {a b : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab) (hbL : b ∉ Lb)
    (h3 : (a * b) ^ 3 = 1) :
    Nat.card (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab)) ≤ 6 := by
  have haX : a ∈ A ⊔ Ab := Subgroup.mem_sup_left ha
  have hbX : b ∈ A ⊔ Ab := Subgroup.mem_sup_right hb
  have hqb : Lb.relIndex Ab = 2 := S.relIndex_Lb.trans hq
  set πq := QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) with hπq
  obtain ⟨x1, hx1def⟩ : ∃ x : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab), x = πq ⟨a, haX⟩ :=
    ⟨_, rfl⟩
  obtain ⟨y1, hy1def⟩ : ∃ y : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab), y = πq ⟨b, hbX⟩ :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab), c = x1 * y1 := ⟨_, rfl⟩
  have hta2 : (⟨a, haX⟩ : ↥(A ⊔ Ab)) * ⟨a, haX⟩ = 1 := Subtype.ext (S.sq_A ha)
  have htb2 : (⟨b, hbX⟩ : ↥(A ⊔ Ab)) * ⟨b, hbX⟩ = 1 := Subtype.ext (S.sq_Ab hb)
  have htab3 : ((⟨a, haX⟩ : ↥(A ⊔ Ab)) * ⟨b, hbX⟩) ^ 3 = 1 :=
    Subtype.ext (by simpa using h3)
  have hx1 : x1 * x1 = 1 := by rw [hx1def, ← map_mul, hta2, map_one]
  have hy1 : y1 * y1 = 1 := by rw [hy1def, ← map_mul, htb2, map_one]
  have hc3 : c ^ 3 = 1 := by
    rw [hc, hx1def, hy1def, ← map_mul, ← map_pow, htab3, map_one]
  have hAK : (A.subgroupOf (A ⊔ Ab)).map πq ≤ Subgroup.closure ({x1, y1} : Set _) := by
    rw [Subgroup.map_le_iff_le_comap]
    intro y hy
    rw [Subgroup.mem_comap]
    have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
    rcases sec53_mem_or_of_index_two hq ha haL hyA with hyL | hyL
    · have h1 : πq y = 1 := (Prop24Setup.mk_eq_one_iff y).mpr (S.L_le_M hyL)
      rw [h1]
      exact Subgroup.one_mem _
    · have hzX : a⁻¹ * (y : G) ∈ A ⊔ Ab := (A ⊔ Ab).mul_mem ((A ⊔ Ab).inv_mem haX) y.2
      have e : y = (⟨a, haX⟩ : ↥(A ⊔ Ab)) * ⟨a⁻¹ * (y : G), hzX⟩ := Subtype.ext (by simp)
      have h1 : πq ⟨a⁻¹ * (y : G), hzX⟩ = 1 :=
        (Prop24Setup.mk_eq_one_iff _).mpr (S.L_le_M hyL)
      have h2 : πq y = x1 := by
        rw [e, map_mul, h1, mul_one, hx1def]
      rw [h2]
      exact Subgroup.subset_closure (by simp)
  have hBK : (Ab.subgroupOf (A ⊔ Ab)).map πq ≤ Subgroup.closure ({x1, y1} : Set _) := by
    rw [Subgroup.map_le_iff_le_comap]
    intro y hy
    rw [Subgroup.mem_comap]
    have hyAb : (y : G) ∈ Ab := Subgroup.mem_subgroupOf.mp hy
    rcases sec53_mem_or_of_index_two hqb hb hbL hyAb with hyL | hyL
    · have h1 : πq y = 1 := (Prop24Setup.mk_eq_one_iff y).mpr (S.Lb_le_M hyL)
      rw [h1]
      exact Subgroup.one_mem _
    · have hzX : b⁻¹ * (y : G) ∈ A ⊔ Ab := (A ⊔ Ab).mul_mem ((A ⊔ Ab).inv_mem hbX) y.2
      have e : y = (⟨b, hbX⟩ : ↥(A ⊔ Ab)) * ⟨b⁻¹ * (y : G), hzX⟩ := Subtype.ext (by simp)
      have h1 : πq ⟨b⁻¹ * (y : G), hzX⟩ = 1 :=
        (Prop24Setup.mk_eq_one_iff _).mpr (S.Lb_le_M hyL)
      have h2 : πq y = y1 := by
        rw [e, map_mul, h1, mul_one, hy1def]
      rw [h2]
      exact Subgroup.subset_closure (by simp)
  have hsup : (A.subgroupOf (A ⊔ Ab)).map πq ⊔ (Ab.subgroupOf (A ⊔ Ab)).map πq = ⊤ :=
    Prop24Setup.image_sup
  have hgen : (⊤ : Subgroup (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab))) ≤
      Subgroup.closure ({x1, y1} : Set _) := by
    rw [← hsup]
    exact sup_le hAK hBK
  have hcy : x1 * c = y1 := by rw [hc, ← mul_assoc, hx1, one_mul]
  have hyx : y1 * x1 = c * c := by
    have h3' : c * c * c = 1 := by
      rw [← hc3, pow_three']
    rw [eq_inv_of_mul_eq_one_left h3', hc, mul_inv_rev, inv_eq_of_mul_eq_one_right hx1,
      inv_eq_of_mul_eq_one_right hy1]
  have hstep : ∀ x : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab), (x = x1 ∨ x = y1) →
      ∀ g : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab), (∃ k : ℕ, g = c ^ k ∨ g = x1 * c ^ k) →
        ∃ k : ℕ, x * g = c ^ k ∨ x * g = x1 * c ^ k := by
    intro x hx g hg
    obtain ⟨k, hk⟩ := hg
    rcases hx with hx | hx <;> rcases hk with hk | hk <;> rw [hx, hk]
    · exact ⟨k, Or.inr rfl⟩
    · exact ⟨k, Or.inl (by rw [← mul_assoc, hx1, one_mul])⟩
    · exact ⟨k + 1, Or.inr (by rw [← hcy, mul_assoc, ← pow_succ'])⟩
    · exact ⟨2 + k, Or.inl (by rw [← mul_assoc, hyx, pow_add, sq])⟩
  have hinv : ∀ x : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab), (x = x1 ∨ x = y1) → x⁻¹ = x := by
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact inv_eq_of_mul_eq_one_right hx1
    · rw [hx]
      exact inv_eq_of_mul_eq_one_right hy1
  have hP : ∀ g ∈ Subgroup.closure ({x1, y1} : Set (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab))),
      ∃ k : ℕ, g = c ^ k ∨ g = x1 * c ^ k := by
    intro g hg
    refine Subgroup.closure_induction_left
      (p := fun g _ => ∃ k : ℕ, g = c ^ k ∨ g = x1 * c ^ k) ⟨0, Or.inl (pow_zero c).symm⟩
      (fun x hx y _ ih => hstep x (by simpa using hx) y ih) (fun x hx y _ ih => ?_) hg
    show ∃ k : ℕ, x⁻¹ * y = c ^ k ∨ x⁻¹ * y = x1 * c ^ k
    rw [hinv x (by simpa using hx)]
    exact hstep x (by simpa using hx) y ih
  have hpow : ∀ k : ℕ, c ^ k = 1 ∨ c ^ k = c ∨ c ^ k = c * c := by
    intro k
    have hck : c ^ k = c ^ (k % 3) := by
      conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hc3, one_pow, one_mul]
    rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
    · left
      rw [hck, h, pow_zero]
    · right
      left
      rw [hck, h, pow_one]
    · right
      right
      rw [hck, h, sq]
  have hsub : (Set.univ : Set (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab))) ⊆
      ({1, c, c * c, x1, x1 * c, x1 * (c * c)} : Set _) := by
    intro g _
    obtain ⟨k, hk⟩ := hP g (hgen (Subgroup.mem_top g))
    rcases hpow k with h | h | h <;> rcases hk with hk | hk <;> rw [h] at hk <;>
      rw [hk] <;> simp
  calc Nat.card (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab))
      = (Set.univ : Set (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab))).ncard :=
        (Set.ncard_univ _).symm
    _ ≤ ({1, c, c * c, x1, x1 * c, x1 * (c * c)} : Set _).ncard := Set.ncard_le_ncard hsub
    _ ≤ 6 := sec53_ncard_le_six _ _ _ _ _ _

theorem sec53_dihedral_three {G : Type} [Group G] [Finite G] {A Ab L Lb M : Subgroup G}
    (S : Prop24Setup A Ab L Lb M)
    (hq : L.relIndex A = 2) {a b : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab) (hbL : b ∉ Lb)
    (h3 : (a * b) ^ 3 = 1) [(M.subgroupOf (A ⊔ Ab)).Normal] :
    Nonempty (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* DihedralGroup 3) := by
  obtain ⟨hN, -, hmod⟩ := S.tim77_2_4_one CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  rcases hmod with ⟨f, hf, hrel, -⟩ | ⟨c, hc, hrel, -⟩ | ⟨m, hm, h3m, hrel, ⟨e⟩⟩
  · exfalso
    rw [hq] at hrel
    have h2f : 2 ^ f = 2 ^ 1 := by
      rw [pow_one]
      exact hrel.symm
    have h1 := Nat.pow_right_injective (le_refl 2) h2f
    omega
  · exfalso
    rw [hq] at hrel
    have h2f : 2 ^ (2 * c + 1) = 2 ^ 1 := by
      rw [pow_one]
      exact hrel.symm
    have h1 := Nat.pow_right_injective (le_refl 2) h2f
    omega
  · have hle6 := sec53_card_quot_le_six S hq ha haL hb hbL h3
    have hcard : Nat.card (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab)) = 2 * m := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hm3 : m = 3 := by omega
    subst hm3
    exact ⟨e⟩

end CFSG.RankThree.GF2n.Tim77
