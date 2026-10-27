module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open

private lemma excPayS_mul_comm_of_conj_eq {G : Type} [Group G] {x x' y : G}
    (h : x * y * x⁻¹ = x' * y * x'⁻¹) : y * (x⁻¹ * x') = (x⁻¹ * x') * y := by
  have hz : y = (x⁻¹ * x') * y * (x⁻¹ * x')⁻¹ := by
    calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
      _ = x⁻¹ * (x' * y * x'⁻¹) * x := by rw [h]
      _ = (x⁻¹ * x') * y * (x⁻¹ * x')⁻¹ := by group
  calc y * (x⁻¹ * x') = ((x⁻¹ * x') * y * (x⁻¹ * x')⁻¹) * (x⁻¹ * x') := by rw [← hz]
    _ = (x⁻¹ * x') * y := by group

private lemma excPayS_eq_of_forall_conj_eq {G : Type} [Group G] {X : Subgroup G}
    (hZ : Subgroup.center ↥X = ⊥) {x x' : G} (hx : x ∈ X) (hx' : x' ∈ X)
    (h : ∀ y ∈ X, x * y * x⁻¹ = x' * y * x'⁻¹) : x = x' := by
  have hmem : (⟨x⁻¹ * x', X.mul_mem (X.inv_mem hx) hx'⟩ : ↥X) ∈ Subgroup.center ↥X :=
    Subgroup.mem_center_iff.mpr fun w => Subtype.ext (excPayS_mul_comm_of_conj_eq (h w w.2))
  have hone : (⟨x⁻¹ * x', X.mul_mem (X.inv_mem hx) hx'⟩ : ↥X) = 1 :=
    Subgroup.mem_bot.mp (hZ ▸ hmem)
  exact inv_mul_eq_one.mp (by simpa using congrArg Subtype.val hone)

private lemma excPayS_conj_mem {G : Type} [Group G] {Bs X : Subgroup G}
    (hinn : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    {b y : G} (hb : b ∈ Bs) (hy : y ∈ X) : b * y * b⁻¹ ∈ X := by
  obtain ⟨x, hxX, hxconj⟩ := hinn b hb
  rw [hxconj y hy]
  exact X.mul_mem (X.mul_mem hxX hy) (X.inv_mem hxX)

private lemma excPayS_conj_conj_eq {G : Type} [Group G] {Bs X : Subgroup G}
    (hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hconj : ∀ a ∈ Bs, ∀ y ∈ X, a * y * a⁻¹ ∈ X)
    {b b' x : G} (hb : b ∈ Bs) (hb' : b' ∈ Bs) (hxX : x ∈ X)
    (hx : ∀ y ∈ X, x * y * x⁻¹ = b * y * b⁻¹) :
    ∀ y ∈ X, (b' * x * b'⁻¹) * y * (b' * x * b'⁻¹)⁻¹ = x * y * x⁻¹ := by
  intro y hy
  have hy' : b'⁻¹ * y * b' ∈ X := by
    simpa using hconj b'⁻¹ (Bs.inv_mem hb') y hy
  have hb'conj : b' * b * b'⁻¹ = b := by
    rw [hcomm b' hb' b hb]
    group
  calc (b' * x * b'⁻¹) * y * (b' * x * b'⁻¹)⁻¹
      = b' * (x * (b'⁻¹ * y * b') * x⁻¹) * b'⁻¹ := by group
    _ = b' * (b * (b'⁻¹ * y * b') * b⁻¹) * b'⁻¹ := by rw [hx _ hy']
    _ = (b' * b * b'⁻¹) * y * (b' * b * b'⁻¹)⁻¹ := by group
    _ = b * y * b⁻¹ := by rw [hb'conj]
    _ = x * y * x⁻¹ := (hx y hy).symm

private lemma excPayS_conj_pow_eq {G : Type} [Group G] {X : Subgroup G} {b x : G}
    (hxX : x ∈ X) (hx : ∀ y ∈ X, x * y * x⁻¹ = b * y * b⁻¹) (n : ℕ) :
    ∀ y ∈ X, x ^ n * y * (x ^ n)⁻¹ = b ^ n * y * (b ^ n)⁻¹ := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    have hby : b ^ n * y * (b ^ n)⁻¹ ∈ X := by
      rw [← ih y hy]
      exact X.mul_mem (X.mul_mem (X.pow_mem hxX n) hy) (X.inv_mem (X.pow_mem hxX n))
    calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹
        = x * (x ^ n * y * (x ^ n)⁻¹) * x⁻¹ := by rw [pow_succ', mul_inv_rev]; group
      _ = x * (b ^ n * y * (b ^ n)⁻¹) * x⁻¹ := by rw [ih y hy]
      _ = b * (b ^ n * y * (b ^ n)⁻¹) * b⁻¹ := hx _ hby
      _ = b ^ (n + 1) * y * (b ^ (n + 1))⁻¹ := by rw [pow_succ', mul_inv_rev]; group

private lemma excPayI_key_of_center_bot {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hZ : Subgroup.center ↥X = ⊥)
    (hinn : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    ∀ b ∈ Bs, ∃ x ∈ X, x ∈ Bs ∧ b * x⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.mp hBs.1 ⟨a, ha⟩ ⟨b, hb⟩)
  have hconj : ∀ a ∈ Bs, ∀ y ∈ X, a * y * a⁻¹ ∈ X :=
    fun a ha y hy => excPayS_conj_mem hinn ha hy
  intro b hb
  obtain ⟨x, hxX, hxconj⟩ := hinn b hb
  have hxconj' : ∀ y ∈ X, x * y * x⁻¹ = b * y * b⁻¹ := fun y hy => (hxconj y hy).symm
  have hxcent : x ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hx'inX : b' * x * b'⁻¹ ∈ X := hconj b' hb' x hxX
    have hsame : ∀ y ∈ X, x * y * x⁻¹ = (b' * x * b'⁻¹) * y * (b' * x * b'⁻¹)⁻¹ :=
      fun y hy => (excPayS_conj_conj_eq hcomm hconj hb hb' hxX hxconj' y hy).symm
    have heq : x = b' * x * b'⁻¹ := excPayS_eq_of_forall_conj_eq hZ hxX hx'inX hsame
    calc b' * x = (b' * x * b'⁻¹) * b' := by group
      _ = x * b' := by rw [← heq]
  have hxpow : x ^ p = 1 := by
    refine excPayS_eq_of_forall_conj_eq hZ (X.pow_mem hxX p) X.one_mem ?_
    intro y hy
    simpa [hBs.2 b hb] using excPayS_conj_pow_eq hxX hxconj' p y hy
  have hxBs : x ∈ Bs := hSC x hxcent hxpow
  have hcent : b * x⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    have hcx : b⁻¹ * x ∈ Subgroup.centralizer (X : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => excPayS_mul_comm_of_conj_eq (hxconj y hy)
    have hbx : b * x⁻¹ = (b⁻¹ * x)⁻¹ := by
      have h1 : b * x = x * b := Subgroup.mem_centralizer_iff.mp hxcent b hb
      have h2 : x⁻¹ * b = b * x⁻¹ := by
        calc x⁻¹ * b = x⁻¹ * (b * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * b) * x⁻¹ := by rw [h1]
          _ = b * x⁻¹ := by group
      rw [mul_inv_rev, inv_inv]
      exact h2.symm
    simpa [hbx] using (Subgroup.centralizer (X : Set G)).inv_mem hcx
  exact ⟨x, hxX, hxBs, hcent⟩

theorem excPay_inner_split {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hZ : Subgroup.center ↥X = ⊥)
    (hinn : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    (∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G)) ∧
      ∀ y ∈ X, (∀ x ∈ X ⊓ Bs, y * x = x * y) → y ^ p = 1 → y ∈ Bs := by
  have key := excPayI_key_of_center_bot hBs hSC hZ hinn
  constructor
  · intro b hb
    obtain ⟨x, hxX, hxBs, hcent⟩ := key b hb
    exact ⟨x, Subgroup.mem_inf.mpr ⟨hxX, hxBs⟩, hcent⟩
  · intro y hyX hycomm hyp
    refine hSC y ?_ hyp
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨x, hxX, hxBs, hcent⟩ := key b hb
    have hyx : x * y = y * x := (hycomm x (Subgroup.mem_inf.mpr ⟨hxX, hxBs⟩)).symm
    have hcy : y * (b * x⁻¹) = (b * x⁻¹) * y :=
      Subgroup.mem_centralizer_iff.mp hcent y hyX
    calc b * y = (b * x⁻¹) * (x * y) := by group
      _ = (b * x⁻¹) * (y * x) := by rw [hyx]
      _ = (b * x⁻¹) * y * x := by group
      _ = y * (b * x⁻¹) * x := by rw [← hcy]
      _ = y * b := by group

private lemma excPayI_pow_mem_center {G : Type} [Group G] {p : ℕ} {X : Subgroup G} {b x : G}
    (hxX : x ∈ X) (hx : ∀ y ∈ X, x * y * x⁻¹ = b * y * b⁻¹) (hb : b ^ p = 1) :
    (⟨x ^ p, X.pow_mem hxX p⟩ : ↥X) ∈ Subgroup.center ↥X := by
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  have h1 : x ^ p * (w : G) * (x ^ p)⁻¹ = (w : G) := by
    rw [excPayS_conj_pow_eq hxX hx p w w.2, hb]
    simp
  calc (w : G) * x ^ p = (x ^ p * (w : G) * (x ^ p)⁻¹) * x ^ p := by rw [h1]
    _ = x ^ p * (w : G) := by group

private lemma excPayI_pow_card_center {G : Type} [Group G] {X : Subgroup G} {z : G}
    (hz : z ∈ X) (hzc : (⟨z, hz⟩ : ↥X) ∈ Subgroup.center ↥X) :
    z ^ Nat.card ↥(Subgroup.center ↥X) = 1 := by
  have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥X))
    (x := (⟨⟨z, hz⟩, hzc⟩ : Subgroup.center ↥X))
  have h' : (⟨z, hz⟩ : ↥X) ^ Nat.card ↥(Subgroup.center ↥X) = 1 :=
    congrArg (fun t : Subgroup.center ↥X => (t : ↥X)) h
  simpa using congrArg (Subgroup.subtype X) h'

private lemma excPayI_eq_of_conj_eq_of_coprime {G : Type} [Group G] {p : ℕ} {X : Subgroup G}
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {x x' : G} (hxX : x ∈ X) (hx'X : x' ∈ X)
    (hsame : ∀ y ∈ X, x * y * x⁻¹ = x' * y * x'⁻¹)
    (hxpow : x ^ p = 1) (hx'pow : x' ^ p = 1) : x' = x := by
  have hzX : x⁻¹ * x' ∈ X := X.mul_mem (X.inv_mem hxX) hx'X
  have hzc : (⟨x⁻¹ * x', hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact excPayS_mul_comm_of_conj_eq (hsame w w.2)
  have hzcard : (x⁻¹ * x') ^ Nat.card ↥(Subgroup.center ↥X) = 1 :=
    excPayI_pow_card_center hzX hzc
  have hxz : Commute x (x⁻¹ * x') := excPayS_mul_comm_of_conj_eq (hsame x hxX)
  have hzp : (x⁻¹ * x') ^ p = 1 := by
    have hx'eq : x' = x * (x⁻¹ * x') := by group
    have h1 : x' ^ p = x ^ p * (x⁻¹ * x') ^ p := by
      conv_lhs => rw [hx'eq]
      exact hxz.mul_pow p
    rw [hxpow, one_mul] at h1
    rw [← h1, hx'pow]
  have hzone : x⁻¹ * x' = 1 := by
    have h := (pow_gcd_eq_one (a := x⁻¹ * x')
      (m := Nat.card ↥(Subgroup.center ↥X)) (n := p)).mpr ⟨hzcard, hzp⟩
    rwa [hZ.gcd_eq_one, pow_one] at h
  calc x' = x * (x⁻¹ * x') := by group
    _ = x * 1 := by rw [hzone]
    _ = x := mul_one x

private lemma excPayI_witness_pow {G : Type} [Group G] {p : ℕ} {X : Subgroup G} {b x₀ : G}
    (hp : p.Prime) (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (hb : b ^ p = 1) (hx₀X : x₀ ∈ X)
    (hx₀conj' : ∀ y ∈ X, x₀ * y * x₀⁻¹ = b * y * b⁻¹) :
    ∃ m : ℕ, x₀ ^ m ∈ X ∧
      (∀ y ∈ X, x₀ ^ m * y * (x₀ ^ m)⁻¹ = b * y * b⁻¹) ∧ (x₀ ^ m) ^ p = 1 := by
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hZ hp.one_lt
  let m : ℕ := Nat.card ↥(Subgroup.center ↥X) * k
  have hm : m = Nat.card ↥(Subgroup.center ↥X) * k := rfl
  have hbm : b ^ m = b := by
    rw [pow_eq_pow_mod m hb, hm, hk, pow_one]
  have hxXs : x₀ ^ m ∈ X := X.pow_mem hx₀X m
  have hxconj : ∀ y ∈ X, x₀ ^ m * y * (x₀ ^ m)⁻¹ = b * y * b⁻¹ := by
    intro y hy
    rw [excPayS_conj_pow_eq hx₀X hx₀conj' m y hy, hbm]
  have hx0pZ : (⟨x₀ ^ p, X.pow_mem hx₀X p⟩ : ↥X) ∈ Subgroup.center ↥X :=
    excPayI_pow_mem_center hx₀X hx₀conj' hb
  have hx0pn : (x₀ ^ p) ^ Nat.card ↥(Subgroup.center ↥X) = 1 :=
    excPayI_pow_card_center (X := X) (X.pow_mem hx₀X p) hx0pZ
  have hxpow : (x₀ ^ m) ^ p = 1 := by
    calc (x₀ ^ m) ^ p = x₀ ^ (m * p) := (pow_mul x₀ m p).symm
      _ = (x₀ ^ p) ^ m := pow_mul' x₀ m p
      _ = ((x₀ ^ p) ^ Nat.card ↥(Subgroup.center ↥X)) ^ k := by rw [hm, pow_mul]
      _ = 1 := by rw [hx0pn, one_pow]
  exact ⟨m, hxXs, hxconj, hxpow⟩

private lemma excPayI_key {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hp : p.Prime) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (hinn : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    ∀ b ∈ Bs, ∃ x ∈ X, x ∈ Bs ∧ b * x⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.mp hBs.1 ⟨a, ha⟩ ⟨b, hb⟩)
  have hconj : ∀ a ∈ Bs, ∀ y ∈ X, a * y * a⁻¹ ∈ X :=
    fun a ha y hy => excPayS_conj_mem hinn ha hy
  intro b hb
  obtain ⟨x₀, hx₀X, hx₀conj⟩ := hinn b hb
  have hx₀conj' : ∀ y ∈ X, x₀ * y * x₀⁻¹ = b * y * b⁻¹ :=
    fun y hy => (hx₀conj y hy).symm
  have hbp : b ^ p = 1 := by simpa using hBs.2 b hb
  obtain ⟨m, hxXs, hxconj, hxpow⟩ :=
    excPayI_witness_pow hp hZ hbp hx₀X hx₀conj'
  have hxcent : x₀ ^ m ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hx'X : b' * (x₀ ^ m) * b'⁻¹ ∈ X := hconj b' hb' _ hxXs
    have hsame : ∀ y ∈ X, (x₀ ^ m) * y * (x₀ ^ m)⁻¹ =
        (b' * (x₀ ^ m) * b'⁻¹) * y * (b' * (x₀ ^ m) * b'⁻¹)⁻¹ :=
      fun y hy => (excPayS_conj_conj_eq hcomm hconj hb hb' hxXs hxconj y hy).symm
    have hx'pow : (b' * (x₀ ^ m) * b'⁻¹) ^ p = 1 := by
      rw [conj_pow, hxpow]
      simp
    have heq : b' * (x₀ ^ m) * b'⁻¹ = x₀ ^ m :=
      excPayI_eq_of_conj_eq_of_coprime hZ hxXs hx'X hsame hxpow hx'pow
    calc b' * (x₀ ^ m) = (b' * (x₀ ^ m) * b'⁻¹) * b' := by group
      _ = (x₀ ^ m) * b' := by rw [heq]
  have hxBs : x₀ ^ m ∈ Bs := hSC _ hxcent hxpow
  have hcent : b * (x₀ ^ m)⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    have hbx : b * (x₀ ^ m)⁻¹ = (x₀ ^ m)⁻¹ * b := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, Subgroup.mem_centralizer_iff.mp hxcent b hb,
        inv_mul_cancel_left]
    rw [hbx]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => excPayS_mul_comm_of_conj_eq (hxconj y hy)
  exact ⟨x₀ ^ m, hxXs, hxBs, hcent⟩

theorem excPay_inner_split_of_coprime {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} (hp : p.Prime) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (hinn : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    (∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G)) ∧
      ∀ y ∈ X, (∀ x ∈ X ⊓ Bs, y * x = x * y) → y ^ p = 1 → y ∈ Bs := by
  have hkey := excPayI_key hp hBs hSC hZ hinn
  constructor
  · intro b hb
    obtain ⟨x, hxX, hxBs, hcent⟩ := hkey b hb
    exact ⟨x, Subgroup.mem_inf.mpr ⟨hxX, hxBs⟩, hcent⟩
  · intro y hyX hycomm hyp
    refine hSC y ?_ hyp
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨x, hxX, hxBs, hcent⟩ := hkey b hb
    have hyx : x * y = y * x := (hycomm x (Subgroup.mem_inf.mpr ⟨hxX, hxBs⟩)).symm
    have hcy : y * (b * x⁻¹) = (b * x⁻¹) * y :=
      Subgroup.mem_centralizer_iff.mp hcent y hyX
    calc b * y = (b * x⁻¹) * (x * y) := by group
      _ = (b * x⁻¹) * (y * x) := by rw [hyx]
      _ = (b * x⁻¹) * y * x := by group
      _ = y * (b * x⁻¹) * x := by rw [← hcy]
      _ = y * b := by group

end CFSG.StandardType.ExcPay
