module
public import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup
open scoped commutatorElement

theorem eq_one_of_mul_self {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : Odd (Nat.card Q)) {q : G} (hq : q ∈ Q) (h : q * q = 1) : q = 1 := by
  have h1 : orderOf q ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard Q hq
  have h2 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
  have : orderOf q = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at h1
      exact absurd (even_iff_two_dvd.mpr h1) (Nat.not_even_iff_odd.mpr hQ)
  exact orderOf_eq_one_iff.mp this

theorem eq_zero_of_neg_eq {M : Type*} [AddCommGroup M] [Finite M]
    (hM : Odd (Nat.card M)) {m : M} (h : -m = m) : m = 0 := by
  have h1 : addOrderOf m ∣ Nat.card M := addOrderOf_dvd_natCard m
  have h2 : addOrderOf m ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero (by
    rw [two_nsmul]; nth_rewrite 1 [← h]; exact neg_add_cancel m)
  have : addOrderOf m = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at h1
      exact absurd (even_iff_two_dvd.mpr h1) (Nat.not_even_iff_odd.mpr hM)
  exact AddMonoid.addOrderOf_eq_one_iff.mp this

theorem exists_pow_sq {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : Odd (Nat.card Q)) {x : G} (hx : x ∈ Q) : ∃ k : ℕ, (x ^ 2) ^ k = x := by
  obtain ⟨n, hn⟩ : Odd (orderOf x) := Odd.of_dvd_nat hQ (Subgroup.orderOf_dvd_natCard Q hx)
  refine ⟨n + 1, ?_⟩
  rw [← pow_mul, show 2 * (n + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
    one_mul]

private theorem comm_center {G : Type*} [Group G] {q : G} (hq : q ∈ center G) (g : G) :
    g * q = q * g :=
  (mem_center_iff.mp hq g)

private theorem fix_of_fix {G : Type*} [Group G] [Finite G] {Q Q₀ : Subgroup G} [Q.Normal]
    (hQodd : Odd (Nat.card Q)) (hQ₀Q : Q₀ ≤ Q) (hQ₀Z : Q₀ ≤ center G)
    (hQ' : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Q₀) {a b e : G} (ha : a * a = 1) (hb : b * b = 1)
    (he : e * e = 1) (hab : a * b = b * a) (hae : a * e = e * a) (hbe : b * e = e * b)
    (hc : ∀ x ∈ Q, (a * b * e) * x * (a * b * e)⁻¹ * x ∈ Q₀)
    (hT : ∀ x ∈ Q, (a * b) * x * (a * b)⁻¹ * x⁻¹ ∈ Q₀ →
      (a * e) * x * (a * e)⁻¹ * x⁻¹ ∈ Q₀ → x ∈ Q₀)
    {x : G} (hx : x ∈ Q) (hxz : (a * b) * x * (a * b)⁻¹ = x) :
    a * x * a⁻¹ = x ∧ b * x * b⁻¹ = x ∧ x * (e * x * e⁻¹) ∈ Q₀ := by
  have hQn : Q.Normal := inferInstance
  obtain ⟨u, hu⟩ : ∃ u, u = a * e := ⟨_, rfl⟩
  have huab : (a * b) * u = u * (a * b) := by
    rw [hu]
    calc a * b * (a * e) = a * (b * a) * e := by group
      _ = a * (a * b) * e := by rw [hab]
      _ = a * a * (b * e) := by group
      _ = a * a * (e * b) := by rw [hbe]
      _ = a * (a * e) * b := by group
      _ = a * (e * a) * b := by rw [hae]
      _ = a * e * (a * b) := by group
  have huu : u * u = 1 := by
    rw [hu]
    calc a * e * (a * e) = a * (e * a) * e := by group
      _ = a * (a * e) * e := by rw [hae]
      _ = (a * a) * (e * e) := by group
      _ = 1 := by rw [ha, he, one_mul]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hux : u * x * u⁻¹ ∈ Q := hQn.conj_mem x hx u
  set w := x * (u * x * u⁻¹) with hw
  have hwQ : w ∈ Q := Q.mul_mem hx hux
  have hw0 : w ∈ Q₀ := by
    refine hT w hwQ ?_ ?_
    · have : (a * b) * w * (a * b)⁻¹ = w := by
        calc (a * b) * w * (a * b)⁻¹
            = ((a * b) * x * (a * b)⁻¹) * (((a * b) * u) * x * ((a * b) * u)⁻¹) := by
              rw [hw]; group
          _ = x * ((u * (a * b)) * x * (u * (a * b))⁻¹) := by rw [hxz, huab]
          _ = x * (u * ((a * b) * x * (a * b)⁻¹) * u⁻¹) := by group
          _ = w := by rw [hxz]
      rw [this, mul_inv_cancel]; exact one_mem _
    · have : u * w * u⁻¹ * w⁻¹ = ⁅u * x * u⁻¹, x⁆ := by
        rw [hw, commutatorElement_def]
        calc u * (x * (u * x * u⁻¹)) * u⁻¹ * (x * (u * x * u⁻¹))⁻¹
            = u * x * u⁻¹ * ((u * u) * x * (u * u)⁻¹) * (u * x * u⁻¹)⁻¹ * x⁻¹ := by group
          _ = u * x * u⁻¹ * x * (u * x * u⁻¹)⁻¹ * x⁻¹ := by rw [huu]; group
      rw [← hu, this]
      exact hQ' _ hux x hx
  set c := a * b * e with hcdef
  have hq₂ : c * x * c⁻¹ * x ∈ Q₀ := hc x hx
  set q₂ := c * x * c⁻¹ * x with hq₂def
  have hcx : c * x * c⁻¹ = q₂ * x⁻¹ := by rw [hq₂def]; group
  have hbe' : b * e = (a * b) * u := by
    rw [hu]
    calc b * e = (a * a) * (b * e) := by rw [ha, one_mul]
      _ = a * (a * b) * e := by group
      _ = a * (b * a) * e := by rw [hab]
      _ = a * b * (a * e) := by group
  have hbex : (b * e) * x * (b * e)⁻¹ = u * x * u⁻¹ := by
    rw [hbe']
    calc (a * b) * u * x * ((a * b) * u)⁻¹ = (u * (a * b)) * x * (u * (a * b))⁻¹ := by
          rw [huab]
      _ = u * ((a * b) * x * (a * b)⁻¹) * u⁻¹ := by group
      _ = u * x * u⁻¹ := by rw [hxz]
  have hac : a = c * (b * e) := by
    rw [hcdef]
    calc a = a * (b * b) * (e * e) := by rw [hb, he]; group
      _ = a * b * (b * e) * e := by group
      _ = a * b * (e * b) * e := by rw [hbe]
      _ = a * b * e * (b * e) := by group
  have hw' : u * x * u⁻¹ = x⁻¹ * w := by rw [hw]; group
  have hwc : c * w * c⁻¹ = w := by
    rw [comm_center (hQ₀Z hw0) c]; group
  have hax : a * x * a⁻¹ = x * (q₂⁻¹ * w) := by
    calc a * x * a⁻¹ = c * ((b * e) * x * (b * e)⁻¹) * c⁻¹ := by
          rw [hac]; group
      _ = c * (x⁻¹ * w) * c⁻¹ := by rw [hbex, hw']
      _ = (c * x * c⁻¹)⁻¹ * (c * w * c⁻¹) := by group
      _ = (q₂ * x⁻¹)⁻¹ * w := by rw [hcx, hwc]
      _ = x * q₂⁻¹ * w := by group
      _ = x * (q₂⁻¹ * w) := by group
  have hq0 : q₂⁻¹ * w ∈ Q₀ := Q₀.mul_mem (Q₀.inv_mem hq₂) hw0
  set q := q₂⁻¹ * w with hqdef
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hq1 : q = 1 := by
    refine eq_one_of_mul_self hQodd (hQ₀Q hq0) ?_
    have h1 : x = x * q * q := by
      calc x = (a * a) * x * (a * a)⁻¹ := by rw [ha]; group
        _ = a * (a * x * a⁻¹) * a⁻¹ := by group
        _ = a * (x * q) * a⁻¹ := by rw [hax]
        _ = (a * x * a⁻¹) * (a * q * a⁻¹) := by group
        _ = x * q * q := by rw [hax, comm_center (hQ₀Z hq0) a]; group
    calc q * q = x⁻¹ * (x * q * q) := by group
      _ = 1 := by rw [← h1, inv_mul_cancel]
  have hax' : a * x * a⁻¹ = x := by rw [hax, hq1, mul_one]
  refine ⟨hax', ?_, ?_⟩
  · calc b * x * b⁻¹ = a * ((a * b) * x * (a * b)⁻¹) * a⁻¹ := by
          rw [show a * ((a * b) * x * (a * b)⁻¹) * a⁻¹ = (a * a) * b * x * b⁻¹ * (a * a)⁻¹ by
            group, ha]
          group
      _ = x := by rw [hxz, hax']
  · have hec : e = c * (a * b) := by
      rw [hcdef]
      calc e = (a * a) * (b * b) * e := by rw [ha, hb]; group
        _ = a * (a * b) * b * e := by group
        _ = a * (b * a) * b * e := by rw [hab]
        _ = a * b * (a * (b * e)) := by group
        _ = a * b * (a * (e * b)) := by rw [hbe]
        _ = a * b * ((a * e) * b) := by group
        _ = a * b * ((e * a) * b) := by rw [hae]
        _ = a * b * e * (a * b) := by group
    have hex : e * x * e⁻¹ = q₂ * x⁻¹ := by
      calc e * x * e⁻¹ = c * ((a * b) * x * (a * b)⁻¹) * c⁻¹ := by rw [hec]; group
        _ = q₂ * x⁻¹ := by rw [hxz, hcx]
    rw [hex, show x * (q₂ * x⁻¹) = (x * q₂) * x⁻¹ by group, comm_center (hQ₀Z hq₂) x,
      mul_inv_cancel_right]
    exact hq₂

private theorem comm_of_inv {G : Type*} [Group G] [Finite G] {Q Q₀ : Subgroup G}
    (hQodd : Odd (Nat.card Q)) (hQ₀Q : Q₀ ≤ Q) (hQ₀Z : Q₀ ≤ center G)
    (hQ' : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Q₀) {d x y : G} (hx : x ∈ Q) (hy : y ∈ Q)
    (hxd : x * (d * x * d⁻¹) ∈ Q₀) (hyd : d * y * d⁻¹ = y) : x * y = y * x := by
  have hg := hQ' x hx y hy
  set g := ⁅x, y⁆ with hgdef
  set q := x * (d * x * d⁻¹) with hqdef
  have hdx : d * x * d⁻¹ = x⁻¹ * q := by rw [hqdef]; group
  have hgd : d * g * d⁻¹ = x⁻¹ * y * x * y⁻¹ := by
    calc d * g * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) * (d * x * d⁻¹)⁻¹ * (d * y * d⁻¹)⁻¹ := by
          rw [hgdef, commutatorElement_def]; group
      _ = x⁻¹ * (q * y) * q⁻¹ * x * y⁻¹ := by rw [hdx, hyd]; group
      _ = x⁻¹ * (y * q) * q⁻¹ * x * y⁻¹ := by rw [comm_center (hQ₀Z hxd) y]
      _ = x⁻¹ * y * x * y⁻¹ := by group
  have hgd' : d * g * d⁻¹ = g := by rw [comm_center (hQ₀Z hg) d]; group
  have hgx : y * x⁻¹ * y⁻¹ * x = g := by
    calc y * x⁻¹ * y⁻¹ * x = x⁻¹ * g * x := by rw [hgdef, commutatorElement_def]; group
      _ = g := by rw [comm_center (hQ₀Z hg) x⁻¹]; group
  have hg1 : g = 1 := by
    refine eq_one_of_mul_self hQodd (hQ₀Q hg) ?_
    calc g * g = (x⁻¹ * y * x * y⁻¹) * (y * x⁻¹ * y⁻¹ * x) := by rw [← hgd, hgd', hgx]
      _ = 1 := by group
  calc x * y = g * (y * x) := by rw [hgdef, commutatorElement_def]; group
    _ = y * x := by rw [hg1, one_mul]

private theorem comm_of_eigen {G M : Type*} [Group G] [Finite G] [AddCommGroup M] [Finite M]
    [DistribMulAction G M] (hfaith : ∀ g : G, (∀ m : M, g • m = m) → g = 1)
    (hirr : ∀ N : AddSubgroup M, (∀ g : G, ∀ m ∈ N, g • m ∈ N) → N = ⊥ ∨ N = ⊤)
    (hModd : Odd (Nat.card M)) {Q Q₀ : Subgroup G} (hQodd : Odd (Nat.card Q)) (hQ₀Z : Q₀ ≤ center G)
    (hQ' : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Q₀) {a b e : G} (he : e * e = 1) (hae : a * e = e * a)
    (hLA : ∀ m : M, (a * e) • m = m → a • m = m)
    (hU : ∃ m : M, m ≠ 0 ∧ a • m = -m ∧ b • m = m) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q)
    (hxa : a * x * a⁻¹ = x) (hxb : b * x * b⁻¹ = x) (hya : a * y * a⁻¹ = y)
    (hyb : b * y * b⁻¹ = y) (hxe : x * (e * x * e⁻¹) ∈ Q₀) (hye : y * (e * y * e⁻¹) ∈ Q₀) :
    x * y = y * x := by
  have hcomm : ∀ {g z : G}, g * z * g⁻¹ = z → g * z = z * g := fun {g z} h => by
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [h]
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  let P : M → Prop := fun m => a • m = -m ∧ b • m = m
  have hPe : ∀ m, P m → e • m = m := by
    intro m hm
    set n := m - e • m with hn
    have han : a • n = -n := by
      have : a • e • m = -(e • m) := by
        rw [smul_smul, hae, ← smul_smul, hm.1, smul_neg]
      rw [hn, smul_sub, hm.1, this]; abel
    have hen : e • n = -n := by
      rw [hn, smul_sub, smul_smul, he, one_smul]; abel
    have : (a * e) • n = n := by rw [← smul_smul, hen, smul_neg, han, neg_neg]
    have := eq_zero_of_neg_eq hModd (by rw [← han, hLA n this])
    rw [hn, sub_eq_zero] at this
    exact this.symm
  have hPg : ∀ {g : G}, a * g * a⁻¹ = g → b * g * b⁻¹ = g → ∀ m, P m → P (g • m) := by
    intro g hga hgb m hm
    refine ⟨?_, ?_⟩
    · rw [smul_smul, hcomm hga, ← smul_smul, hm.1, smul_neg]
    · rw [smul_smul, hcomm hgb, ← smul_smul, hm.2]
  have hcen : ∀ {q : G}, q ∈ Q₀ → ∀ g : G, g * q * g⁻¹ = q := fun {q} hq g => by
    rw [comm_center (hQ₀Z hq) g]; group
  have hpow : ∀ {z : G}, z ∈ Q → a * z * a⁻¹ = z → b * z * b⁻¹ = z → z * (e * z * e⁻¹) ∈ Q₀ →
      ∃ k : ℕ, ∀ m, P m → z • m = (z * (e * z * e⁻¹)) ^ k • m := by
    intro z hz hza hzb hze
    set q := z * (e * z * e⁻¹) with hq
    have hPq : ∀ m, P m → P (q • m) := hPg (hcen hze a) (hcen hze b)
    have hsq : ∀ m, P m → (z ^ 2) • m = q • m := by
      intro m hm
      rw [hq, heinv, ← smul_smul, ← smul_smul, ← smul_smul, hPe m hm, hPe _ (hPg hza hzb m hm),
        sq, ← smul_smul]
    have hk : ∀ k : ℕ, ∀ m, P m → (z ^ 2) ^ k • m = q ^ k • m ∧ P (q ^ k • m) := by
      intro k
      induction k with
      | zero => intro m hm; simpa using hm
      | succ k ih =>
        intro m hm
        obtain ⟨h1, h2⟩ := ih (q • m) (hPq m hm)
        refine ⟨?_, ?_⟩
        · rw [pow_succ, ← smul_smul, hsq m hm, h1, smul_smul, ← pow_succ]
        · rw [pow_succ, ← smul_smul]; exact h2
    obtain ⟨k, hk'⟩ := exists_pow_sq hQodd hz
    exact ⟨k, fun m hm => by rw [← (hk k m hm).1, hk']⟩
  obtain ⟨k, hkx⟩ := hpow hx hxa hxb hxe
  obtain ⟨l, hly⟩ := hpow hy hya hyb hye
  set qx := x * (e * x * e⁻¹)
  set qy := y * (e * y * e⁻¹)
  have hPqy : ∀ j : ℕ, ∀ m, P m → P (qy ^ j • m) := by
    intro j
    induction j with
    | zero => intro m hm; simpa using hm
    | succ j ih =>
      intro m hm
      rw [pow_succ, ← smul_smul]
      exact ih _ (hPg (hcen hye a) (hcen hye b) m hm)
  have hPqx : ∀ j : ℕ, ∀ m, P m → P (qx ^ j • m) := by
    intro j
    induction j with
    | zero => intro m hm; simpa using hm
    | succ j ih =>
      intro m hm
      rw [pow_succ, ← smul_smul]
      exact ih _ (hPg (hcen hxe a) (hcen hxe b) m hm)
  have hqq : qx ^ k * qy ^ l = qy ^ l * qx ^ k :=
    (Commute.pow_pow (mem_center_iff.mp (hQ₀Z hxe) qy).symm k l)
  have hxy : ∀ m, P m → (x * y) • m = (y * x) • m := by
    intro m hm
    rw [← smul_smul, ← smul_smul, hly m hm, hkx _ (hPqy l m hm), smul_smul, hqq, ← smul_smul,
      ← hkx m hm, hly _ (hPg hxa hxb m hm)]
  obtain ⟨m₀, hm₀, hm₀P⟩ := hU
  have hg := hQ' x hx y hy
  set g := ⁅x, y⁆ with hgdef
  have hgyx : g * (y * x) = x * y := by rw [hgdef, commutatorElement_def]; group
  let C : AddSubgroup M :=
    { carrier := {m | g • m = m}
      add_mem' := fun {m n} hm hn => by
        simp only [Set.mem_setOf_eq] at hm hn ⊢
        rw [smul_add, hm, hn]
      zero_mem' := by simp
      neg_mem' := fun {m} hm => by
        simp only [Set.mem_setOf_eq] at hm ⊢
        rw [smul_neg, hm] }
  have hCinv : ∀ h : G, ∀ m ∈ C, h • m ∈ C := by
    intro h m hm
    change g • h • m = h • m
    have hm' : g • m = m := hm
    rw [smul_smul, ← comm_center (hQ₀Z hg) h, ← smul_smul, hm']
  have hnC : (y * x) • m₀ ∈ C := by
    change g • (y * x) • m₀ = (y * x) • m₀
    rw [smul_smul, hgyx, hxy m₀ hm₀P]
  have hn0 : (y * x) • m₀ ≠ 0 := fun h => hm₀ ((smul_eq_zero_iff_eq _).mp h)
  rcases hirr C hCinv with hC | hC
  · exact absurd ((AddSubgroup.mem_bot).mp (hC ▸ hnC)) hn0
  · have hg1 : g = 1 := hfaith g fun m => by
      have : m ∈ C := hC ▸ AddSubgroup.mem_top m
      exact this
    rw [← hgyx, hg1, one_mul]

private theorem F_mul {G : Type*} [Group G] {Q₀ : Subgroup G} (hQ₀Z : Q₀ ≤ center G) {u v x : G}
    (hu : u * x * u⁻¹ * x⁻¹ ∈ Q₀) (hv : v * x * v⁻¹ * x⁻¹ ∈ Q₀) :
    (u * v) * x * (u * v)⁻¹ * x⁻¹ ∈ Q₀ := by
  have h : (u * v) * x * (u * v)⁻¹ * x⁻¹ =
      (u * (v * x * v⁻¹ * x⁻¹) * u⁻¹) * (u * x * u⁻¹ * x⁻¹) := by group
  rw [h, comm_center (hQ₀Z hv) u, show v * x * v⁻¹ * x⁻¹ * u * u⁻¹ = v * x * v⁻¹ * x⁻¹ by group]
  exact Q₀.mul_mem hv hu

private theorem prod_pair {G : Type*} [Group G] {a b e : G} (hb : b * b = 1) :
    (a * b) * (b * e) = a * e := by
  calc (a * b) * (b * e) = a * (b * b) * e := by group
    _ = a * e := by rw [hb, mul_one]

private theorem pair_sq {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

private theorem rotate_eigen {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
    {a b a' b' t : G} (ha : t * a * t⁻¹ = a') (hb : t * b * t⁻¹ = b')
    (h : ∃ m : M, m ≠ 0 ∧ a • m = -m ∧ b • m = m) :
    ∃ m : M, m ≠ 0 ∧ a' • m = -m ∧ b' • m = m := by
  obtain ⟨m, hm, ham, hbm⟩ := h
  have ha' : a' * t = t * a := by rw [← ha]; group
  have hb' : b' * t = t * b := by rw [← hb]; group
  refine ⟨t • m, fun h0 => hm ((smul_eq_zero_iff_eq _).mp h0), ?_, ?_⟩
  · rw [smul_smul, ha', ← smul_smul, ham, smul_neg]
  · rw [smul_smul, hb', ← smul_smul, hbm]

theorem comm_of_frame_action {G M : Type*} [Group G] [Finite G] [AddCommGroup M] [Finite M]
    [DistribMulAction G M] (hfaith : ∀ g : G, (∀ m : M, g • m = m) → g = 1)
    (hirr : ∀ N : AddSubgroup M, (∀ g : G, ∀ m ∈ N, g • m ∈ N) → N = ⊥ ∨ N = ⊤)
    (hModd : Odd (Nat.card M)) {Q Q₀ : Subgroup G} [hQn : Q.Normal] (hQodd : Odd (Nat.card Q))
    (hQ₀Q : Q₀ ≤ Q) (hQ₀Z : Q₀ ≤ center G) (hQ' : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Q₀)
    {d₁ d₂ d₃ t : G} (h1 : d₁ * d₁ = 1) (h2 : d₂ * d₂ = 1) (h3 : d₃ * d₃ = 1)
    (h12 : d₁ * d₂ = d₂ * d₁) (h13 : d₁ * d₃ = d₃ * d₁) (h23 : d₂ * d₃ = d₃ * d₂)
    (hn12 : d₁ ≠ d₂) (hn13 : d₁ ≠ d₃) (hn23 : d₂ ≠ d₃)
    (ht1 : t * d₁ * t⁻¹ = d₂) (ht2 : t * d₂ * t⁻¹ = d₃) (ht3 : t * d₃ * t⁻¹ = d₁)
    (hc : ∀ x ∈ Q, (d₁ * d₂ * d₃) * x * (d₁ * d₂ * d₃)⁻¹ * x ∈ Q₀)
    (hT₁ : ∀ x ∈ Q, (d₂ * d₃) * x * (d₂ * d₃)⁻¹ * x⁻¹ ∈ Q₀ →
      (d₃ * d₁) * x * (d₃ * d₁)⁻¹ * x⁻¹ ∈ Q₀ → x ∈ Q₀)
    (hLA : ∀ a ∈ ({d₁, d₂, d₃} : Set G), ∀ b ∈ ({d₁, d₂, d₃} : Set G), a ≠ b →
      ∀ m : M, (a * b) • m = m → a • m = m)
    (hM : ∃ m : M, d₁ • m ≠ m) :
    ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  classical
  have hm1 : d₁ ∈ ({d₁, d₂, d₃} : Set G) := by simp
  have hm2 : d₂ ∈ ({d₁, d₂, d₃} : Set G) := by simp
  have hm3 : d₃ ∈ ({d₁, d₂, d₃} : Set G) := by simp
  have hU₃ : ∃ m : M, m ≠ 0 ∧ d₁ • m = -m ∧ d₂ • m = m := by
    obtain ⟨m₀, hm₀⟩ := hM
    set m₁ := m₀ - d₁ • m₀ with hm₁
    have hm₁0 : m₁ ≠ 0 := fun h => hm₀ (sub_eq_zero.mp h).symm
    have hd₁m₁ : d₁ • m₁ = -m₁ := by
      rw [hm₁, smul_sub, smul_smul, h1, one_smul]; abel
    have hd₂d₁ : d₁ • d₂ • m₁ = -(d₂ • m₁) := by
      rw [smul_smul, h12, ← smul_smul, hd₁m₁, smul_neg]
    refine ⟨m₁ + d₂ • m₁, fun h0 => ?_, ?_, ?_⟩
    · have hneg : d₂ • m₁ = -m₁ := eq_neg_of_add_eq_zero_right h0
      have hfix : (d₁ * d₂) • m₁ = m₁ := by rw [← smul_smul, hneg, smul_neg, hd₁m₁, neg_neg]
      have := hLA d₁ hm1 d₂ hm2 hn12 m₁ hfix
      exact hm₁0 (eq_zero_of_neg_eq hModd (by rw [← hd₁m₁, this]))
    · rw [smul_add, hd₁m₁, hd₂d₁]; abel
    · rw [smul_add, smul_smul, h2, one_smul, add_comm]
  have hU₁ : ∃ m : M, m ≠ 0 ∧ d₂ • m = -m ∧ d₃ • m = m := rotate_eigen ht1 ht2 hU₃
  have hU₂ : ∃ m : M, m ≠ 0 ∧ d₃ • m = -m ∧ d₁ • m = m := rotate_eigen ht2 ht3 hU₁
  have hz11 : (d₂ * d₃) * (d₂ * d₃) = 1 := pair_sq h2 h3 h23
  have hz22 : (d₃ * d₁) * (d₃ * d₁) = 1 := pair_sq h3 h1 h13.symm
  have hz33 : (d₁ * d₂) * (d₁ * d₂) = 1 := pair_sq h1 h2 h12
  have hz12 : (d₂ * d₃) * (d₃ * d₁) = (d₁ * d₂) := by rw [prod_pair h3, h12]
  have hz23 : (d₃ * d₁) * (d₁ * d₂) = (d₂ * d₃) := by rw [prod_pair h1, h23]
  have hz31 : (d₁ * d₂) * (d₂ * d₃) = (d₃ * d₁) := by rw [prod_pair h2, h13]
  have hinv : ∀ {z : G}, z * z = 1 → z⁻¹ = z := fun h => inv_eq_of_mul_eq_one_right h
  have hz21 : (d₃ * d₁) * (d₂ * d₃) = (d₁ * d₂) := by
    rw [← hinv hz22, ← hinv hz11, ← mul_inv_rev, hz12, hinv hz33]
  have hz32 : (d₁ * d₂) * (d₃ * d₁) = (d₂ * d₃) := by
    rw [← hinv hz33, ← hinv hz22, ← mul_inv_rev, hz23, hinv hz11]
  have hz13 : (d₂ * d₃) * (d₁ * d₂) = (d₃ * d₁) := by
    rw [← hinv hz11, ← hinv hz33, ← mul_inv_rev, hz31, hinv hz22]
  let T₁ : Subgroup G :=
    { carrier := {1, (d₂ * d₃), (d₃ * d₁), (d₁ * d₂)}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [hz11, hz22, hz33, hz12, hz21, hz13, hz31, hz23, hz32]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl
        · simp
        · rw [hinv hz11]; simp
        · rw [hinv hz22]; simp
        · rw [hinv hz33]; simp }
  have hT₁mem : ∀ u ∈ T₁, u = 1 ∨ u = (d₂ * d₃) ∨ u = (d₃ * d₁) ∨ u = (d₁ * d₂) := fun u hu => hu
  have hT₁sq : ∀ u ∈ T₁, u * u = 1 := by
    intro u hu
    rcases hT₁mem u hu with rfl | rfl | rfl | rfl
    · simp
    · exact hz11
    · exact hz22
    · exact hz33
  have hT₁comm : ∀ u ∈ T₁, ∀ v ∈ T₁, u * v = v * u := by
    intro u hu v hv
    have h1' := hT₁sq u hu
    have h2' := hT₁sq v hv
    have h3' := hT₁sq (u * v) (T₁.mul_mem hu hv)
    rw [← hinv h3', mul_inv_rev, hinv h1', hinv h2']
  have hzAT : (d₂ * d₃) ∈ T₁ := by simp [T₁]
  have hzBT : (d₃ * d₁) ∈ T₁ := by simp [T₁]
  have hzA1 : (d₂ * d₃) ≠ 1 := fun h => hn23 (by rw [← hinv h3]; exact eq_inv_of_mul_eq_one_left h)
  have hzB1 : (d₃ * d₁) ≠ 1 := fun h => hn13 (by rw [← hinv h1]; exact (eq_inv_of_mul_eq_one_left h).symm)
  have hzAB : (d₂ * d₃) ≠ (d₃ * d₁) := by
    intro h
    apply hn12
    have : d₂ * d₃ * d₃ = d₃ * d₁ * d₃ := by rw [h]
    rw [mul_assoc, h3, mul_one, mul_assoc, h13, ← mul_assoc, h3, one_mul] at this
    exact this.symm
  letI iC : CommGroup T₁ :=
    { (inferInstance : Group T₁) with mul_comm := fun a b => Subtype.ext (hT₁comm a a.2 b b.2) }
  haveI : CFSG.IsElementaryAbelian 2 T₁ :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hT₁comm a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by rw [sq]; simpa using hT₁sq g g.2) }
  haveI : Nontrivial T₁ := ⟨⟨⟨(d₂ * d₃), hzAT⟩, 1, fun h => hzA1 (congrArg Subtype.val h)⟩⟩
  let α : T₁ →* MulAut Q := (MulAut.conjNormal (H := Q)).comp T₁.subtype
  have hα : ∀ (b : T₁) (x : Q), ((α b x : Q) : G) = (b : G) * x * (b : G)⁻¹ := by
    intro b x
    simp [α, MulAut.conjNormal_apply]
  have hgen := CFSG.SolvableSignalizer.iSup_fixedBySubgroup_index_eq_top 2 Nat.prime_two α
    (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hQodd)
  have hFzA : ∀ x ∈ Q, (d₂ * d₃) * x * (d₂ * d₃)⁻¹ * x⁻¹ ∈ Q₀ → (d₃ * d₁) * x * (d₃ * d₁)⁻¹ * x⁻¹ ∈ Q₀ → x ∈ Q₀ := hT₁
  have hc₁ : d₂ * d₃ * d₁ = d₁ * d₂ * d₃ := by
    calc d₂ * d₃ * d₁ = d₂ * (d₃ * d₁) := by group
      _ = d₂ * (d₁ * d₃) := by rw [h13]
      _ = (d₂ * d₁) * d₃ := by group
      _ = d₁ * d₂ * d₃ := by rw [h12]
  have hc₂ : d₃ * d₁ * d₂ = d₁ * d₂ * d₃ := by
    calc d₃ * d₁ * d₂ = (d₁ * d₃) * d₂ := by rw [h13]
      _ = d₁ * (d₃ * d₂) := by group
      _ = d₁ * (d₂ * d₃) := by rw [h23]
      _ = d₁ * d₂ * d₃ := by group
  have K₃ := fun (x : G) (hx : x ∈ Q) (hxz : (d₁ * d₂) * x * (d₁ * d₂)⁻¹ = x) =>
    fix_of_fix hQodd hQ₀Q hQ₀Z hQ' h1 h2 h3 h12 h13 h23 hc
      (fun y hy hy3 hy2 => hFzA y hy (by rw [← hz32]; exact F_mul hQ₀Z hy3 (by rwa [← h13]))
        (by rwa [← h13])) hx hxz
  have K₁ := fun (x : G) (hx : x ∈ Q) (hxz : (d₂ * d₃) * x * (d₂ * d₃)⁻¹ = x) =>
    fix_of_fix hQodd hQ₀Q hQ₀Z hQ' h2 h3 h1 h23 h12.symm h13.symm (fun y hy => hc₁ ▸ hc y hy)
      (fun y hy hy1 hy3 => hFzA y hy hy1 (by
        rw [← hz31]; exact F_mul hQ₀Z (by rwa [h12]) hy1)) hx hxz
  have K₂ := fun (x : G) (hx : x ∈ Q) (hxz : (d₃ * d₁) * x * (d₃ * d₁)⁻¹ = x) =>
    fix_of_fix hQodd hQ₀Q hQ₀Z hQ' h3 h1 h2 h13.symm h23.symm h12 (fun y hy => hc₂ ▸ hc y hy)
      (fun y hy hy2 hy1 => hFzA y hy (by rwa [h23]) hy2) hx hxz
  let X : Set Q := {x | (d₂ * d₃) * (x : G) * (d₂ * d₃)⁻¹ = x ∨ (d₃ * d₁) * (x : G) * (d₃ * d₁)⁻¹ = x ∨
    (d₁ * d₂) * (x : G) * (d₁ * d₂)⁻¹ = x}
  have hLA' : ∀ {a b : G}, a ∈ ({d₁, d₂, d₃} : Set G) → b ∈ ({d₁, d₂, d₃} : Set G) → a ≠ b →
      ∀ m : M, (a * b) • m = m → a • m = m := fun ha hb hab => hLA _ ha _ hb hab
  have hXc : ∀ x ∈ X, ∀ y ∈ X, (x : G) * y = y * x := by
    intro x hx y hy
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
    · obtain ⟨hxa, hxb, hxe⟩ := K₁ x x.2 hx
      obtain ⟨hya, hyb, hye⟩ := K₁ y y.2 hy
      exact comm_of_eigen hfaith hirr hModd hQodd hQ₀Z hQ' h1 h12.symm
        (hLA' hm2 hm1 (Ne.symm hn12)) hU₁ x.2 y.2 hxa hxb hya hyb hxe hye
    · obtain ⟨-, -, hxe⟩ := K₁ x x.2 hx
      obtain ⟨-, hyb, -⟩ := K₂ y y.2 hy
      exact comm_of_inv hQodd hQ₀Q hQ₀Z hQ' x.2 y.2 hxe hyb
    · obtain ⟨-, -, hxe⟩ := K₁ x x.2 hx
      obtain ⟨hya, -, -⟩ := K₃ y y.2 hy
      exact comm_of_inv hQodd hQ₀Q hQ₀Z hQ' x.2 y.2 hxe hya
    · obtain ⟨-, -, hxe⟩ := K₂ x x.2 hx
      obtain ⟨hya, -, -⟩ := K₁ y y.2 hy
      exact comm_of_inv hQodd hQ₀Q hQ₀Z hQ' x.2 y.2 hxe hya
    · obtain ⟨hxa, hxb, hxe⟩ := K₂ x x.2 hx
      obtain ⟨hya, hyb, hye⟩ := K₂ y y.2 hy
      exact comm_of_eigen hfaith hirr hModd hQodd hQ₀Z hQ' h2 h23.symm
        (hLA' hm3 hm2 (Ne.symm hn23)) hU₂ x.2 y.2 hxa hxb hya hyb hxe hye
    · obtain ⟨-, -, hxe⟩ := K₂ x x.2 hx
      obtain ⟨-, hyb, -⟩ := K₃ y y.2 hy
      exact comm_of_inv hQodd hQ₀Q hQ₀Z hQ' x.2 y.2 hxe hyb
    · obtain ⟨-, -, hxe⟩ := K₃ x x.2 hx
      obtain ⟨-, hyb, -⟩ := K₁ y y.2 hy
      exact comm_of_inv hQodd hQ₀Q hQ₀Z hQ' x.2 y.2 hxe hyb
    · obtain ⟨-, -, hxe⟩ := K₃ x x.2 hx
      obtain ⟨hya, -, -⟩ := K₂ y y.2 hy
      exact comm_of_inv hQodd hQ₀Q hQ₀Z hQ' x.2 y.2 hxe hya
    · obtain ⟨hxa, hxb, hxe⟩ := K₃ x x.2 hx
      obtain ⟨hya, hyb, hye⟩ := K₃ y y.2 hy
      exact comm_of_eigen hfaith hirr hModd hQodd hQ₀Z hQ' h3 h13
        (hLA' hm1 hm3 hn13) hU₃ x.2 y.2 hxa hxb hya hyb hxe hye
  have hcard : Nat.card T₁ ≠ 2 := by
    intro h2'
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : T₁)).mp h2'
    have e1 := hy ⟨(d₂ * d₃), hzAT⟩ (fun h => hzA1 (congrArg Subtype.val h))
    have e2 := hy ⟨(d₃ * d₁), hzBT⟩ (fun h => hzB1 (congrArg Subtype.val h))
    exact hzAB (congrArg Subtype.val (e1.trans e2.symm))
  have hle : (⊤ : Subgroup Q) ≤ closure X := by
    rw [← hgen]
    refine iSup₂_le fun B hB x hx => ?_
    rw [CFSG.SolvableSignalizer.mem_fixedBySubgroup] at hx
    obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hBbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
      rw [hBbot, Subgroup.index_bot] at hB
      exact hcard hB
    have hfix : (b : G) * x * (b : G)⁻¹ = x := by rw [← hα]; exact congrArg Subtype.val (hx b hbB)
    apply Subgroup.subset_closure
    rcases hT₁mem b b.2 with h | h | h | h
    · exact absurd (Subtype.ext h) hb1
    · exact Or.inl (h ▸ hfix)
    · exact Or.inr (Or.inl (h ▸ hfix))
    · exact Or.inr (Or.inr (h ▸ hfix))
  have hcl : IsMulCommutative (closure X) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => Subtype.ext (hXc x hx y hy)
  intro x hx y hy
  have hx' : (⟨x, hx⟩ : Q) ∈ closure X := hle (mem_top _)
  have hy' : (⟨y, hy⟩ : Q) ∈ closure X := hle (mem_top _)
  have := hcl.is_comm.comm ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩
  exact congrArg (fun z : closure X => ((z : Q) : G)) this

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

