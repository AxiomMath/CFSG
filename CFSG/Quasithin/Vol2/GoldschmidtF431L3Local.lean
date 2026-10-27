module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Solv

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G]

namespace L3Datum

section Good

variable {M₁ M₂ : Subgroup G} (D : L3Datum M₁ M₂)

structure Good : Prop where
  cent : ∀ x ∈ D.Z, x ≠ 1 → ∀ y : G, y * x = x * y → y ∈ M₁ ⊓ M₂
  ex : ∃ z ∈ D.Z, z ≠ 1

variable {D}

theorem Good.of_hyp {z : G} (hz : z ∈ D.Z) (hz1 : z ≠ 1)
    (hC : Subgroup.centralizer ({z} : Set G) ≤ M₁) : D.Good :=
  ⟨D.centZ_of_hyp hz hz1 hC, z, hz, hz1⟩

theorem conjSub_Z_eq {h : G} (hh : h ∈ M₁ ⊓ M₂) [Finite G] : conjSub h D.Z = D.Z := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have := D.Z_norm hh (mem_conjSub.mp hx)
    simpa [mul_assoc] using this
  · rw [mem_conjSub]
    simpa using D.Z_norm ((M₁ ⊓ M₂).inv_mem hh) hx

end Good

end L3Datum

namespace L3Datum

section Good2

variable [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}

theorem pow_mul_B {s b : G} (hs : s ∈ D.S) (hb : b ∈ D.B) (n : ℕ) :
    ∃ s' ∈ D.S, (s * b) ^ n = s' * b ^ n := by
  induction n with
  | zero => exact ⟨1, D.S.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨s', hs', h⟩ := ih
    have hbn : b ^ n ∈ M₁ ⊓ M₂ := Subgroup.pow_mem _ (D.B_le hb) n
    refine ⟨s' * (b ^ n * s * (b ^ n)⁻¹), D.S.mul_mem hs' (D.S_norm _ hbn s hs), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem two_elt_mem_S {y : G} (hy : y ∈ M₁ ⊓ M₂) {k : ℕ} (hk : y ^ (2 ^ k) = 1) : y ∈ D.S := by
  obtain ⟨s, hs, b, hb, rfl⟩ := D.mul_SB y hy
  obtain ⟨s', hs', h⟩ := pow_mul_B (D := D) hs hb (2 ^ k)
  rw [hk] at h
  have hbk : b ^ (2 ^ k) = s'⁻¹ := by
    have : s' * b ^ (2 ^ k) = 1 := h.symm
    exact eq_inv_of_mul_eq_one_right this
  have hbS : b ^ (2 ^ k) ∈ D.S := by rw [hbk]; exact D.S.inv_mem hs'
  have hb1 : b ^ (2 ^ k) = 1 := D.B_inf_S hbS (Subgroup.pow_mem _ hb _)
  have hdvd : orderOf b ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hb1
  have hdvd2 : orderOf b ∣ Nat.card D.B := by
    have := orderOf_dvd_natCard (⟨b, hb⟩ : D.B)
    rwa [Subgroup.orderOf_mk] at this
  have hodd : Odd (orderOf b) := D.B_odd.of_dvd_nat hdvd2
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    by_contra hne
    have : Even (orderOf b) := by rw [hj']; exact Nat.even_pow.mpr ⟨even_two, hne⟩
    exact (Nat.not_even_iff_odd.mpr hodd) this
  have : orderOf b = 1 := by rw [hj', hj0, pow_zero]
  have hb1' : b = 1 := orderOf_eq_one_iff.mp this
  rw [hb1', mul_one]
  exact hs

namespace Good

variable (hG : D.Good)
include hG

omit [Finite G] in
theorem normalizer_Z {n : G} (hn : ∀ x ∈ D.Z, n * x * n⁻¹ ∈ D.Z) : n ∈ M₁ ⊓ M₂ := by
  obtain ⟨z, hz, hz1⟩ := hG.ex
  have hz' := hn z hz
  have hz'1 : n * z * n⁻¹ ≠ 1 := by
    intro h; apply hz1
    have := congrArg (fun y => n⁻¹ * y * n) h
    simpa [mul_assoc] using this
  obtain ⟨b, hb, hbz⟩ := D.trans z hz hz1 _ hz' hz'1
  have hc : (b⁻¹ * n) * z = z * (b⁻¹ * n) := by
    calc b⁻¹ * n * z = b⁻¹ * (n * z * n⁻¹) * n := by group
      _ = b⁻¹ * (b * z * b⁻¹) * n := by rw [hbz]
      _ = z * (b⁻¹ * n) := by group
  have h1 := hG.cent z hz hz1 _ hc
  have : n = b * (b⁻¹ * n) := by group
  rw [this]
  exact (M₁ ⊓ M₂).mul_mem (D.B_le hb) h1

theorem TI {a b x : G} (hxa : x ∈ conjSub a D.Z) (hxb : x ∈ conjSub b D.Z) (hx1 : x ≠ 1) :
    conjSub a D.Z = conjSub b D.Z := by
  rw [mem_conjSub] at hxa hxb
  obtain ⟨x', hx'⟩ : ∃ x', x' = a⁻¹ * x * a := ⟨_, rfl⟩
  obtain ⟨x'', hx''⟩ : ∃ x'', x'' = b⁻¹ * x * b := ⟨_, rfl⟩
  rw [← hx'] at hxa
  rw [← hx''] at hxb
  have h1 : x' ≠ 1 := by rw [hx']; exact conj_ne_one' hx1
  have h2 : x'' ≠ 1 := by rw [hx'']; exact conj_ne_one' hx1
  obtain ⟨u, hu, huv⟩ := D.trans x' hxa h1 x'' hxb h2
  have hcomm : (a⁻¹ * b * u) * x' = x' * (a⁻¹ * b * u) := by
    calc a⁻¹ * b * u * x' = a⁻¹ * b * (u * x' * u⁻¹) * u := by group
      _ = a⁻¹ * b * x'' * u := by rw [huv]
      _ = a⁻¹ * b * (b⁻¹ * x * b) * u := by rw [hx'']
      _ = a⁻¹ * x * b * u := by group
      _ = x' * (a⁻¹ * b * u) := by rw [hx']; group
  have hH := hG.cent x' hxa h1 _ hcomm
  have hab : a⁻¹ * b ∈ M₁ ⊓ M₂ := by
    have : a⁻¹ * b = (a⁻¹ * b * u) * u⁻¹ := by group
    rw [this]
    exact (M₁ ⊓ M₂).mul_mem hH ((M₁ ⊓ M₂).inv_mem (D.B_le hu))
  have : b = a * (a⁻¹ * b) := by group
  rw [this, conjSub_mul, conjSub_Z_eq hab]

omit [Finite G] in
theorem cent_conj_le {a x y : G} (hx : x ∈ conjSub a D.Z) (hx1 : x ≠ 1) (hy : y * x = x * y) :
    y ∈ conjSub a (M₁ ⊓ M₂) := by
  rw [mem_conjSub] at hx ⊢
  exact hG.cent _ hx (conj_ne_one' hx1) _ (conj_commute hy)

theorem two_elt_conj {a x y : G} (hx : x ∈ conjSub a D.Z) (hx1 : x ≠ 1) (hy : y * x = x * y)
    {k : ℕ} (hk : y ^ (2 ^ k) = 1) : y ∈ conjSub a D.S := by
  have h1 := hG.cent_conj_le hx hx1 hy
  rw [mem_conjSub] at h1 ⊢
  refine two_elt_mem_S h1 (k := k) ?_
  have e : (a⁻¹ * y * a) ^ (2 ^ k) = a⁻¹ * y ^ (2 ^ k) * a := by
    have := conj_pow (a := a⁻¹) (b := y) (i := 2 ^ k)
    simpa using this
  rw [e, hk]; group

theorem sylow_top : IsSylowTwoOf D.S ⊤ := by
  refine isSylowTwoOf_top_of_centralizer_le ⟨D.S_le_M₁, D.S_pgroup, D.S_index⟩ ?_ ?_
  · obtain ⟨z, hz, hz1⟩ := hG.ex
    exact ⟨z, hz, hz1⟩
  · intro w hw hw1 y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    exact (hG.cent w hw hw1 y hy).1

end Good

end Good2

end L3Datum

namespace L3Datum

section Inv

variable [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}

theorem Good.inv_conj_Z (hG : D.Good) {j : G} (hj : j ^ 2 = 1) (hj1 : j ≠ 1) :
    ∃ a : G, a⁻¹ * j * a ∈ D.Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf j = 2 := orderOf_eq_prime hj hj1
  obtain ⟨m, -, hm⟩ := exists_conj_mem_of_isSylowTwoOf_involution hG.sylow_top (u := j)
    (Subgroup.mem_top j) hord
  have hx2 : (m⁻¹ * j * m) ^ 2 = 1 := by rw [conj_sq, hj]; group
  have hx1 : m⁻¹ * j * m ≠ 1 := conj_ne_one' hj1
  rcases D.frame.inv _ hm hx2 hx1 with h | h
  · obtain ⟨n, hn, hnZ⟩ := D.cov₁ _ h hx1
    exact ⟨m * n⁻¹, by simpa [mul_assoc] using hnZ⟩
  · obtain ⟨n, hn, hnZ⟩ := D.cov₂ _ h hx1
    exact ⟨m * n⁻¹, by simpa [mul_assoc] using hnZ⟩

theorem Good.inv_conj_in_M0 (hG : D.Good) {z : G} (hz : z ∈ D.Z) (hz1 : z ≠ 1) {x : G}
    (hx : x ∈ M₁ ⊔ M₂) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ m ∈ M₁ ⊔ M₂, m * z * m⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hSM : D.S ≤ M₁ ⊔ M₂ := D.S_le_M₁.trans le_sup_left
  have hK := F7.isSylowTwoOf_mono_right hG.sylow_top hSM le_top
  obtain ⟨m, hmM, hm⟩ := exists_conj_mem_of_isSylowTwoOf_involution hK hx hord
  have hy2 : (m⁻¹ * x * m) ^ 2 = 1 := by rw [conj_sq, hx2]; group
  have hy1 : m⁻¹ * x * m ≠ 1 := conj_ne_one' hx1
  have key : ∀ n ∈ M₁ ⊔ M₂, n * (m⁻¹ * x * m) * n⁻¹ ∈ D.Z →
      ∃ c ∈ M₁ ⊔ M₂, c * z * c⁻¹ = x := by
    intro n hn hnZ
    have hn1 : n * (m⁻¹ * x * m) * n⁻¹ ≠ 1 := by
      intro h; apply hy1
      have := congrArg (fun y => n⁻¹ * y * n) h
      simpa [mul_assoc] using this
    obtain ⟨b, hb, hbz⟩ := D.trans z hz hz1 _ hnZ hn1
    have hbM : b ∈ M₁ ⊔ M₂ := Subgroup.mem_sup_left (D.B_le hb).1
    refine ⟨m * n⁻¹ * b, (M₁ ⊔ M₂).mul_mem ((M₁ ⊔ M₂).mul_mem hmM ((M₁ ⊔ M₂).inv_mem hn)) hbM, ?_⟩
    calc m * n⁻¹ * b * z * (m * n⁻¹ * b)⁻¹ = m * n⁻¹ * (b * z * b⁻¹) * n * m⁻¹ := by group
      _ = m * n⁻¹ * (n * (m⁻¹ * x * m) * n⁻¹) * n * m⁻¹ := by rw [hbz]
      _ = x := by group
  rcases D.frame.inv _ hm hy2 hy1 with h | h
  · obtain ⟨n, hn, hnZ⟩ := D.cov₁ _ h hy1
    exact key n (Subgroup.mem_sup_left hn) hnZ
  · obtain ⟨n, hn, hnZ⟩ := D.cov₂ _ h hy1
    exact key n (Subgroup.mem_sup_right hn) hnZ

theorem Good.eq_top [IsSimpleGroup G] (hG : D.Good) {z : G}
    (hz : z ∈ D.Z) (hz1 : z ≠ 1) (hC : Subgroup.centralizer ({z} : Set G) ≤ M₁) :
    M₁ ⊔ M₂ = ⊤ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf z = 2 := orderOf_eq_prime (D.Z_sq hz) hz1
  have hsolv := solvable_of_conj (M := M₁ ⊔ M₂) hord (hC.trans le_sup_left)
    (fun (x : G) (hx : x ∈ M₁ ⊔ M₂) (hx2 : orderOf x = 2) => by
      have hx2' : x ^ 2 = 1 := by
        have := pow_orderOf_eq_one x
        rwa [hx2] at this
      have hx1 : x ≠ 1 := by
        intro h; rw [h, orderOf_one] at hx2; omega
      exact hG.inv_conj_in_M0 hz hz1 hx hx2' hx1)
    (exists_klein_four D.frame.Q₁_ea D.frame.four_le) hne
  apply D.nonsolv
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (le_sup_left : M₁ ≤ M₁ ⊔ M₂)) (Subgroup.inclusion_injective _)

end Inv

end L3Datum

namespace L3Datum

section F446

variable [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}

omit [Finite G] in
theorem conjSub_Q₁_eq {m : G} (hm : m ∈ M₁) : conjSub m D.Q₁ = D.Q₁ := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have := D.Q₁_norm m hm _ (mem_conjSub.mp hx)
    simpa [mul_assoc] using this
  · rw [mem_conjSub]
    simpa using D.Q₁_norm m⁻¹ (M₁.inv_mem hm) x hx

omit [Finite G] in
theorem conjSub_Q₂_eq {m : G} (hm : m ∈ M₂) : conjSub m D.Q₂ = D.Q₂ := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have := D.Q₂_norm m hm _ (mem_conjSub.mp hx)
    simpa [mul_assoc] using this
  · rw [mem_conjSub]
    simpa using D.Q₂_norm m⁻¹ (M₂.inv_mem hm) x hx

omit [Finite G] in
theorem Z_ne_one_mem (hG : D.Good) (c : G) : ∃ y ∈ conjSub c D.Z, y ≠ 1 := by
  obtain ⟨z, hz, hz1⟩ := hG.ex
  refine ⟨c * z * c⁻¹, mul_mem_conjSub hz, fun h => hz1 ?_⟩
  have := congrArg (fun y => c⁻¹ * y * c) h
  simpa [mul_assoc] using this

omit [Finite G] in
theorem Good.mem_H_of_normalizer_S (hG : D.Good) {n : G}
    (hn : n ∈ Subgroup.normalizer (D.S : Set G)) : n ∈ M₁ ⊓ M₂ := by
  refine hG.normalizer_Z (fun x hx => ?_)
  rw [D.mem_Z] at hx ⊢
  have hn' : n⁻¹ ∈ Subgroup.normalizer (D.S : Set G) :=
    (Subgroup.normalizer (D.S : Set G)).inv_mem hn
  refine ⟨(Subgroup.mem_normalizer_iff.mp hn x).mp hx.1, fun s hs => ?_⟩
  have h1 : n⁻¹ * s * n ∈ D.S := by
    have := (Subgroup.mem_normalizer_iff.mp hn' s).mp hs
    simpa using this
  have h2 := hx.2 (n⁻¹ * s * n) h1
  calc s * (n * x * n⁻¹) = n * ((n⁻¹ * s * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * s * n)) * n⁻¹ := by rw [h2]
    _ = n * x * n⁻¹ * s := by group

theorem Good.members_in_Q (hG : D.Good) {Q M : Subgroup G}
    (hcov : ∀ x ∈ Q, x ≠ 1 → ∃ m ∈ M, m * x * m⁻¹ ∈ D.Z) {a : G} (hY : conjSub a D.Z ≤ Q) :
    ∃ m ∈ M, conjSub m D.Z = conjSub a D.Z := by
  obtain ⟨y, hy, hy1⟩ := Z_ne_one_mem hG a
  obtain ⟨m', hm', hmZ⟩ := hcov y (hY hy) hy1
  refine ⟨m'⁻¹, M.inv_mem hm', ?_⟩
  refine hG.TI (x := y) ?_ hy hy1
  rw [mem_conjSub]; simpa using hmZ

theorem Good.mem_of_normalizes_Q (hG : D.Good) {Q M : Subgroup G}
    (hcov : ∀ x ∈ Q, x ≠ 1 → ∃ m ∈ M, m * x * m⁻¹ ∈ D.Z) (hZQ : D.Z ≤ Q)
    (hHM : M₁ ⊓ M₂ ≤ M) {n : G} (hn : ∀ x ∈ Q, n * x * n⁻¹ ∈ Q) : n ∈ M := by
  have hle : conjSub n D.Z ≤ Q := by
    intro x hx
    have := hn _ (hZQ (mem_conjSub.mp hx))
    simpa [mul_assoc] using this
  obtain ⟨m, hm, hmeq⟩ := hG.members_in_Q hcov hle
  have h1 : conjSub (m⁻¹ * n) D.Z = D.Z := by
    rw [conjSub_mul, ← hmeq, conjSub_conjSub_inv]
  have h2 : m⁻¹ * n ∈ M₁ ⊓ M₂ := by
    apply hG.normalizer_Z
    intro x hx
    have : m⁻¹ * n * x * (m⁻¹ * n)⁻¹ ∈ conjSub (m⁻¹ * n) D.Z := mul_mem_conjSub hx
    rwa [h1] at this
  have : n = m * (m⁻¹ * n) := by group
  rw [this]
  exact M.mul_mem hm (hHM h2)

theorem Good.normalizer_Q₁ (hG : D.Good) {n : G} (hn : ∀ x ∈ D.Q₁, n * x * n⁻¹ ∈ D.Q₁) :
    n ∈ M₁ :=
  hG.mem_of_normalizes_Q D.cov₁ D.Z_le_Q₁ (fun _ hh => hh.1) hn

theorem Good.normalizer_Q₂ (hG : D.Good) {n : G} (hn : ∀ x ∈ D.Q₂, n * x * n⁻¹ ∈ D.Q₂) :
    n ∈ M₂ :=
  hG.mem_of_normalizes_Q D.cov₂ D.Z_le_Q₂ (fun _ hh => hh.2) hn

theorem Good.Q_not_conj (hG : D.Good) (x : G) : conjSub x D.Q₁ ≠ D.Q₂ := by
  intro h
  have hT := hG.sylow_top
  obtain ⟨n, hn, hnQ⟩ := normal_sylow_fusion hT
    (fun t ht a ha => D.Q₁_norm t (D.S_le_M₁ ht) a ha)
    (fun t ht b hb => D.Q₂_norm t (D.S_le_M₂ ht) b hb) h
  have hnH := hG.mem_H_of_normalizer_S hn
  rw [conjSub_Q₁_eq hnH.1] at hnQ
  exact D.frame.Q_ne hnQ

theorem Good.Q_not_conj' (hG : D.Good) (x : G) : conjSub x D.Q₂ ≠ D.Q₁ := by
  intro h
  apply hG.Q_not_conj x⁻¹
  rw [← h, conjSub_conjSub_inv]

end F446

end L3Datum

namespace L3Datum

section F446b

variable [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}

theorem Good.ea_le_conj_S (hG : D.Good) {c y : G} {A : Subgroup G} (hy : y ∈ conjSub c D.Z)
    (hy1 : y ≠ 1) (hyA : y ∈ A) (hA : IsElemAbelian 2 A) : A ≤ conjSub c D.S := by
  intro q hq
  refine hG.two_elt_conj hy hy1 (F7.isElemAbelian_comm hA hq hyA) (k := 1) ?_
  simpa using F7.isElemAbelian_pow_eq_one hA hq

theorem Good.Q_unique (hG : D.Good) {Q Q' : Subgroup G} (hF : Frame D.S Q Q')
    (hnc : ∀ x : G, conjSub x Q ≠ Q') {c a b : G} (ha : conjSub c D.Z ≤ conjSub a Q)
    (hb : conjSub c D.Z ≤ conjSub b Q) : conjSub a Q = conjSub b Q := by
  obtain ⟨y, hy, hy1⟩ := Z_ne_one_mem hG c
  have hFc := hF.conj c
  have key : ∀ e : G, conjSub c D.Z ≤ conjSub e Q →
      conjSub e Q = conjSub c Q ∨ conjSub e Q = conjSub c Q' := by
    intro e he
    have hea : IsElemAbelian 2 (conjSub e Q) := F7.isElemAbelian_conjSub hF.Q₁_ea
    have hle := hG.ea_le_conj_S hy hy1 (he hy) hea
    refine hFc.maxea _ hle hea ?_
    rw [card_conjSub, card_conjSub]
  have hsub : ∀ e : G, conjSub e Q = conjSub c Q' → False := by
    intro e he
    apply hnc (c⁻¹ * e)
    rw [conjSub_mul, he, conjSub_conjSub_inv]
  rcases key a ha with h1 | h1 <;> rcases key b hb with h2 | h2
  · rw [h1, h2]
  · exact absurd h2 (hsub b)
  · exact absurd h1 (hsub a)
  · rw [h1, h2]

end F446b

end L3Datum

namespace L3Datum

section Tri

variable [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}

theorem Good.Z_inf_conj (hG : D.Good) {g : G} (hg : g ∉ M₁ ⊓ M₂) {w : G} (hw : w ∈ D.Z)
    (hw' : w ∈ conjSub g D.Z) : w = 1 := by
  by_contra hw1
  have h := hG.TI (a := 1) (b := g) (x := w) (by rw [conjSub_one]; exact hw) hw' hw1
  rw [conjSub_one] at h
  apply hg
  apply hG.normalizer_Z
  intro x hx
  have : g * x * g⁻¹ ∈ conjSub g D.Z := mul_mem_conjSub hx
  rwa [← h] at this

omit [Finite G] in
theorem commute_of_mem_conj {g x y : G} (hx : x ∈ conjSub g D.Z) (hy : y ∈ conjSub g D.S) :
    y * x = x * y := by
  rw [mem_conjSub] at hx hy
  have := (D.mem_Z.mp hx).2 _ hy
  have e1 : y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
  have e2 : x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
  rw [e1, e2, this]

theorem Good.caseI_aux (hG : D.Good) {g : G} (hg : g ∉ M₁ ⊓ M₂) {Q Q' : Subgroup G}
    (hF : Frame D.S Q Q') {x : G} (hxg : x ∈ conjSub g D.Z) (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    D.S ⊓ conjSub g D.S = Q ∧ (Q = conjSub g Q ∨ Q = conjSub g Q') := by
  have hxS : x ∈ D.S := hF.Q₁_le hxQ
  have hxZ : x ∉ centerOf D.S := fun h => hx1 (hG.Z_inf_conj hg h hxg)
  have hQP : Q ≤ conjSub g D.S := hG.ea_le_conj_S hxg hx1 hxQ hF.Q₁_ea
  have hA : conjSub g⁻¹ Q ≤ D.S := (le_conjSub_iff g).mp hQP
  have hAe := F7.isElemAbelian_conjSub (g := g⁻¹) hF.Q₁_ea
  have hcard : Nat.card Q ≤ Nat.card (conjSub g⁻¹ Q) := by rw [card_conjSub]
  have hQeq : Q = conjSub g Q ∨ Q = conjSub g Q' := by
    rcases hF.maxea _ hA hAe hcard with h | h
    · left
      have := congrArg (conjSub g) h
      rwa [conjSub_inv_conjSub] at this
    · right
      have := congrArg (conjSub g) h
      rwa [conjSub_inv_conjSub] at this
  refine ⟨?_, hQeq⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨hyS, hyP⟩ := Subgroup.mem_inf.mp hy
    exact hF.cent₁ x hxQ hxZ y hyS (commute_of_mem_conj hxg hyP)
  · intro y hy
    exact Subgroup.mem_inf.mpr ⟨hF.Q₁_le hy, hQP hy⟩

theorem Good.caseI (hG : D.Good) {g : G} (hg : g ∉ M₁ ⊓ M₂) {x : G} (hxg : x ∈ conjSub g D.Z)
    (hxS : x ∈ D.S) (hx1 : x ≠ 1) :
    ∃ Q, (Q = D.Q₁ ∨ Q = D.Q₂) ∧ D.S ⊓ conjSub g D.S = Q ∧
      (Q = conjSub g D.Q₁ ∨ Q = conjSub g D.Q₂) := by
  have hx2 : x ^ 2 = 1 := sq_of_conj_sq (D.Z_sq (mem_conjSub.mp hxg))
  rcases D.frame.inv x hxS hx2 hx1 with h | h
  · obtain ⟨h1, h2⟩ := hG.caseI_aux hg D.frame hxg h hx1
    exact ⟨D.Q₁, Or.inl rfl, h1, h2⟩
  · obtain ⟨h1, h2⟩ := hG.caseI_aux hg D.frame.symm hxg h hx1
    exact ⟨D.Q₂, Or.inr rfl, h1, h2.symm⟩

theorem Good.caseI' (hG : D.Good) {g : G} (hg : g ∉ M₁ ⊓ M₂) {x : G} (hxZ : x ∈ D.Z)
    (hxP : x ∈ conjSub g D.S) (hx1 : x ≠ 1) :
    ∃ Q, (Q = D.Q₁ ∨ Q = D.Q₂) ∧ D.S ⊓ conjSub g D.S = Q ∧
      (Q = conjSub g D.Q₁ ∨ Q = conjSub g D.Q₂) := by
  have hg' : g⁻¹ ∉ M₁ ⊓ M₂ := fun h => hg (by simpa using (M₁ ⊓ M₂).inv_mem h)
  have hx' : g⁻¹ * x * g ∈ conjSub g⁻¹ D.Z := by
    rw [mem_conjSub]
    have : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [this]; exact hxZ
  have hxS : g⁻¹ * x * g ∈ D.S := mem_conjSub.mp hxP
  obtain ⟨Q, hQ, hS, hQc⟩ := hG.caseI hg' hx' hxS (conj_ne_one' hx1)
  have hSP : D.S ⊓ conjSub g D.S = conjSub g Q := by
    have : conjSub g Q = conjSub g D.S ⊓ D.S := by
      rw [← hS, conjSub_inf, conjSub_inv_conjSub]
    rw [this, inf_comm]
  rcases hQc with h | h
  · refine ⟨D.Q₁, Or.inl rfl, ?_, ?_⟩
    · rw [hSP, h, conjSub_inv_conjSub]
    · have h1 : D.Q₁ = conjSub g Q := by rw [h, conjSub_inv_conjSub]
      rcases hQ with hq | hq
      · exact Or.inl (h1.trans (congrArg (conjSub g) hq))
      · exact Or.inr (h1.trans (congrArg (conjSub g) hq))
  · refine ⟨D.Q₂, Or.inr rfl, ?_, ?_⟩
    · rw [hSP, h, conjSub_inv_conjSub]
    · have h1 : D.Q₂ = conjSub g Q := by rw [h, conjSub_inv_conjSub]
      rcases hQ with hq | hq
      · exact Or.inl (h1.trans (congrArg (conjSub g) hq))
      · exact Or.inr (h1.trans (congrArg (conjSub g) hq))

theorem Good.caseII_aux (hG : D.Good) {g : G}
    (hI : ∀ x ∈ conjSub g D.Z, x ∈ D.S → x = 1) (hI' : ∀ x ∈ D.Z, x ∈ conjSub g D.S → x = 1)
    {Qa Qa' Qb Qb' : Subgroup G} (hFa : Frame D.S Qa Qa') (hFb : Frame (conjSub g D.S) Qb Qb')
    (hQa : Qa = D.Q₁ ∨ Qa = D.Q₂) (hQb : Qb = conjSub g D.Q₁ ∨ Qb = conjSub g D.Q₂)
    {j : G} (hjS : j ∈ D.S) (hjP : j ∈ conjSub g D.S) (hj1 : j ≠ 1)
    (hjQa : j ∈ Qa) (hjQb : j ∈ Qb) :
    ∃ a : G, D.S ⊓ conjSub g D.S = conjSub a D.Z ∧ conjSub a D.Z ≠ D.Z ∧
      conjSub a D.Z ≠ conjSub g D.Z := by
  have hjZ : j ∉ D.Z := fun h => hj1 (hI' j h hjP)
  have hjZg : j ∉ conjSub g D.Z := fun h => hj1 (hI j h hjS)
  have hj2 : j ^ 2 = 1 := F7.isElemAbelian_pow_eq_one hFa.Q₁_ea hjQa
  obtain ⟨a, ha⟩ := hG.inv_conj_Z hj2 hj1
  have hjY : j ∈ conjSub a D.Z := mem_conjSub.mpr ha
  have hQa_le : Qa ≤ conjSub a D.S := hG.ea_le_conj_S hjY hj1 hjQa hFa.Q₁_ea
  have hQb_le : Qb ≤ conjSub a D.S := hG.ea_le_conj_S hjY hj1 hjQb hFb.Q₁_ea
  have hcard1 : Nat.card D.Q₁ ≤ Nat.card Qa := by
    rcases hQa with h | h
    · rw [h]
    · rw [h, D.frame.card_eq]
  have hcard2 : Nat.card D.Q₁ ≤ Nat.card Qb := by
    rcases hQb with h | h
    · rw [h, card_conjSub]
    · rw [h, card_conjSub, D.frame.card_eq]
  have hFa' := D.frame.conj a
  have hA : Qa = conjSub a D.Q₁ ∨ Qa = conjSub a D.Q₂ :=
    hFa'.maxea Qa hQa_le hFa.Q₁_ea (by rw [card_conjSub]; exact hcard1)
  have hB : Qb = conjSub a D.Q₁ ∨ Qb = conjSub a D.Q₂ :=
    hFa'.maxea Qb hQb_le hFb.Q₁_ea (by rw [card_conjSub]; exact hcard2)
  have hne : Qa ≠ Qb := by
    intro heq
    obtain ⟨w, hw, hw1⟩ := Z_ne_one_mem hG g
    have hwQb : w ∈ Qb := by
      rcases hQb with h | h
      · rw [h]; exact conjSub_mono g D.Z_le_Q₁ hw
      · rw [h]; exact conjSub_mono g D.Z_le_Q₂ hw
    exact hw1 (hI w hw (hFa.Q₁_le (heq ▸ hwQb)))
  have hmeet : Qa ⊓ Qb = conjSub a D.Z := by
    rcases hA with h1 | h1 <;> rcases hB with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2, ← conjSub_inf, D.frame.inter]
    · rw [h1, h2, ← conjSub_inf, inf_comm, D.frame.inter]
    · exact absurd (h1.trans h2.symm) hne
  refine ⟨a, ?_, ?_, ?_⟩
  · apply le_antisymm
    · intro u hu
      obtain ⟨huS, huP⟩ := Subgroup.mem_inf.mp hu
      have hcomm : ∀ v ∈ D.S ⊓ conjSub g D.S, ∀ w ∈ D.S ⊓ conjSub g D.S, v * w = w * v := by
        intro v hv w hw
        obtain ⟨hvS, hvP⟩ := Subgroup.mem_inf.mp hv
        obtain ⟨hwS, hwP⟩ := Subgroup.mem_inf.mp hw
        have hc := D.frame.comm v hvS w hwS
        have hcP : v * w * v⁻¹ * w⁻¹ ∈ conjSub g D.S :=
          (conjSub g D.S).mul_mem ((conjSub g D.S).mul_mem ((conjSub g D.S).mul_mem hvP hwP)
            ((conjSub g D.S).inv_mem hvP)) ((conjSub g D.S).inv_mem hwP)
        have h1 := hI' _ hc hcP
        calc v * w = (v * w * v⁻¹ * w⁻¹) * (w * v) := by group
          _ = w * v := by rw [h1, one_mul]
      have hj_mem : j ∈ D.S ⊓ conjSub g D.S := Subgroup.mem_inf.mpr ⟨hjS, hjP⟩
      have hu_j : u * j = j * u := hcomm u hu j hj_mem
      have huQa : u ∈ Qa := hFa.cent₁ j hjQa hjZ u huS hu_j
      have huQb : u ∈ Qb := hFb.cent₁ j hjQb (by rw [centerOf_conjSub]; exact hjZg) u huP hu_j
      rw [← hmeet]
      exact Subgroup.mem_inf.mpr ⟨huQa, huQb⟩
    · rw [← hmeet]
      exact le_inf (inf_le_left.trans hFa.Q₁_le) (inf_le_right.trans hFb.Q₁_le)
  · intro h; apply hjZ; rw [← h]; exact hjY
  · intro h; apply hjZg; rw [← h]; exact hjY

theorem Good.trichotomy (hG : D.Good) {g : G} (hg : g ∉ M₁ ⊓ M₂) :
    D.S ⊓ conjSub g D.S = ⊥ ∨
    (∃ Q, (Q = D.Q₁ ∨ Q = D.Q₂) ∧ D.S ⊓ conjSub g D.S = Q ∧
        (Q = conjSub g D.Q₁ ∨ Q = conjSub g D.Q₂)) ∨
    (∃ a : G, D.S ⊓ conjSub g D.S = conjSub a D.Z ∧ conjSub a D.Z ≠ D.Z ∧
        conjSub a D.Z ≠ conjSub g D.Z) := by
  by_cases hI : ∃ x ∈ conjSub g D.Z, x ∈ D.S ∧ x ≠ 1
  · obtain ⟨x, hx, hxS, hx1⟩ := hI
    exact Or.inr (Or.inl (hG.caseI hg hx hxS hx1))
  by_cases hI' : ∃ x ∈ D.Z, x ∈ conjSub g D.S ∧ x ≠ 1
  · obtain ⟨x, hx, hxP, hx1⟩ := hI'
    exact Or.inr (Or.inl (hG.caseI' hg hx hxP hx1))
  have hI2 : ∀ x ∈ conjSub g D.Z, x ∈ D.S → x = 1 := fun x hx hxS => by
    by_contra h; exact hI ⟨x, hx, hxS, h⟩
  have hI2' : ∀ x ∈ D.Z, x ∈ conjSub g D.S → x = 1 := fun x hx hxP => by
    by_contra h; exact hI' ⟨x, hx, hxP, h⟩
  by_cases hbot : D.S ⊓ conjSub g D.S = ⊥
  · exact Or.inl hbot
  right; right
  set D₀ : Subgroup G := D.S ⊓ conjSub g D.S with hD₀
  have hp : IsPGroup 2 D₀ := D.S_pgroup.to_le inf_le_left
  obtain ⟨j, hj, hj1, hj2⟩ := exists_involution_of_ne_bot hp hbot
  obtain ⟨hjS, hjP⟩ := Subgroup.mem_inf.mp hj
  have hFg := D.frame.conj g
  rcases D.frame.inv j hjS hj2 hj1 with h1 | h1 <;> rcases hFg.inv j hjP hj2 hj1 with h2 | h2
  · exact hG.caseII_aux hI2 hI2' D.frame hFg (Or.inl rfl) (Or.inl rfl) hjS hjP hj1 h1 h2
  · exact hG.caseII_aux hI2 hI2' D.frame hFg.symm (Or.inl rfl) (Or.inr rfl) hjS hjP hj1 h1 h2
  · exact hG.caseII_aux hI2 hI2' D.frame.symm hFg (Or.inr rfl) (Or.inl rfl) hjS hjP hj1 h1 h2
  · exact hG.caseII_aux hI2 hI2' D.frame.symm hFg.symm (Or.inr rfl) (Or.inr rfl) hjS hjP hj1 h1 h2

end Tri

end L3Datum

end CFSG.Quasithin.H13.F431.L3
