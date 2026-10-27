module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.Line63

theorem exists_lift_weyl {L' : Type} [Group L'] [Finite L'] {Z T : Subgroup L'}
    {A : Subgroup (MulAut L')} (hZ : Z ≤ Subgroup.center L') (hZ2 : IsPGroup 2 Z)
    (hT3 : IsPGroup 3 T) (hA3 : IsPGroup 3 A) (hZA : ∀ a ∈ A, ∀ z ∈ Z, a z ∈ Z)
    (hTA : ∀ a ∈ A, ∀ t ∈ T, a t = t) (n₀ : L') (hn₀ : ∀ a ∈ A, n₀ * (a n₀)⁻¹ ∈ T ⊔ Z) :
    ∃ z ∈ Z, ∀ a ∈ A, (n₀ * z) * (a (n₀ * z))⁻¹ ∈ T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun φ : MulAut L' => (φ : L' → L')) DFunLike.coe_injective
  haveI : Fintype A := Fintype.ofFinite A
  have hcen : ∀ y ∈ Z, ∀ g : L', g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hZ hy) g
  haveI hZn : Z.Normal := ⟨fun y hy g => by rw [hcen y hy g, mul_inv_cancel_right]; exact hy⟩
  have hdisj : Disjoint T Z := IsPGroup.disjoint_of_ne 3 2 (by norm_num) T Z hT3 hZ2
  have huniq : ∀ s ∈ T, ∀ z ∈ Z, ∀ s' ∈ T, ∀ z' ∈ Z, s * z = s' * z' → z = z' := by
    intro s hs z hz s' hs' z' hz' h
    have h1 : s'⁻¹ * s = z' * z⁻¹ := by
      calc s'⁻¹ * s = s'⁻¹ * (s * z) * z⁻¹ := by group
        _ = s'⁻¹ * (s' * z') * z⁻¹ := by rw [h]
        _ = z' * z⁻¹ := by group
    have hT : z' * z⁻¹ ∈ T := h1 ▸ T.mul_mem (T.inv_mem hs') hs
    have hZ' : z' * z⁻¹ ∈ Z := Z.mul_mem hz' (Z.inv_mem hz)
    have h2 : z' * z⁻¹ = 1 := by
      have := hdisj.le_bot ⟨hT, hZ'⟩
      simpa using this
    exact (mul_inv_eq_one.mp h2).symm
  have hdec : ∀ a : A, ∃ s ∈ T, ∃ z ∈ Z, n₀ * (a.1 n₀)⁻¹ = s * z := by
    intro a
    have h := hn₀ a.1 a.2
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at h
    obtain ⟨s, hs, z, hz, hsz⟩ := h
    exact ⟨s, hs, z, hz, hsz.symm⟩
  choose s hs z hz hsz using hdec
  have hcoc : ∀ a b : A, z (a * b) = z a * a.1 (z b) := by
    intro a b
    have e1 : n₀ * ((a * b).1 n₀)⁻¹ = (n₀ * (a.1 n₀)⁻¹) * a.1 (n₀ * (b.1 n₀)⁻¹) := by
      simp only [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
      group
    rw [hsz, hsz, hsz, map_mul, hTA a.1 a.2 _ (hs b)] at e1
    have hzb : a.1 (z b) ∈ Z := hZA a.1 a.2 _ (hz b)
    have e2 : s a * z a * (s b * a.1 (z b)) = (s a * s b) * (z a * a.1 (z b)) := by
      rw [mul_assoc (s a), ← mul_assoc (z a), ← hcen (z a) (hz a) (s b)]
      group
    rw [e2] at e1
    exact huniq _ (hs _) _ (hz _) _ (T.mul_mem (hs a) (hs b)) _ (Z.mul_mem (hz a) hzb) e1
  letI : CommGroup Z :=
    { (inferInstance : Group Z) with
      mul_comm := fun x y => Subtype.ext (hcen y y.2 x) }
  let zz : A → Z := fun a => ⟨z a, hz a⟩
  let act : A → Z →* Z := fun a =>
    { toFun := fun y => ⟨a.1 (y : L'), hZA a.1 a.2 y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [Subgroup.coe_mul, map_mul]) }
  have hcoc' : ∀ a b : A, zz (a * b) = zz a * act a (zz b) := fun a b =>
    Subtype.ext (hcoc a b)
  set N := Fintype.card A with hN
  set u : Z := ∏ b : A, zz b with hu
  have hsum : ∀ a : A, u = zz a ^ N * act a u := by
    intro a
    calc u = ∏ b : A, zz (a * b) :=
          (Fintype.prod_equiv (Equiv.mulLeft a) (fun b => zz (a * b)) zz fun _ => rfl).symm
      _ = ∏ b : A, (zz a * act a (zz b)) := Finset.prod_congr rfl fun b _ => hcoc' a b
      _ = zz a ^ N * act a u := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, map_prod]
  have hcop : (Nat.card Z).Coprime N := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hA3
    rw [hk, hN, ← Nat.card_eq_fintype_card, hj]
    exact Nat.Coprime.pow k j (by norm_num)
  obtain ⟨r, hr⟩ := (powCoprime hcop).surjective u
  have hr' : r ^ N = u := hr
  have hza : ∀ a : A, zz a = r * (act a r)⁻¹ := by
    intro a
    apply (powCoprime hcop).injective
    change zz a ^ N = (r * (act a r)⁻¹) ^ N
    rw [mul_pow, inv_pow, ← map_pow, hr']
    have := hsum a
    rw [eq_mul_inv_iff_mul_eq]
    exact this.symm
  refine ⟨(r : L')⁻¹, Z.inv_mem r.2, fun a ha => ?_⟩
  have hzaL : z ⟨a, ha⟩ = (r : L') * (a (r : L'))⁻¹ := congrArg Subtype.val (hza ⟨a, ha⟩)
  have harZ : a (r : L') ∈ Z := hZA a ha _ r.2
  have key : (n₀ * (r : L')⁻¹) * (a (n₀ * (r : L')⁻¹))⁻¹ = s ⟨a, ha⟩ := by
    have h0 := hsz ⟨a, ha⟩
    simp only at h0
    rw [map_mul, map_inv, mul_inv_rev, inv_inv]
    have c2 : (r : L')⁻¹ * (a (r : L') * (a n₀)⁻¹) = (a (r : L') * (a n₀)⁻¹) * (r : L')⁻¹ :=
      (hcen _ (Z.inv_mem r.2) _).symm
    have c3 : a (r : L') * (a n₀)⁻¹ = (a n₀)⁻¹ * a (r : L') := (hcen _ harZ _).symm
    have c4 : a (r : L') * (r : L')⁻¹ = (r : L')⁻¹ * a (r : L') := hcen _ (Z.inv_mem r.2) _
    have c5 : (a (r : L'))⁻¹ * (r : L')⁻¹ = (r : L')⁻¹ * (a (r : L'))⁻¹ :=
      hcen _ (Z.inv_mem r.2) _
    calc n₀ * (r : L')⁻¹ * (a (r : L') * (a n₀)⁻¹)
        = n₀ * ((a n₀)⁻¹ * a (r : L') * (r : L')⁻¹) := by rw [mul_assoc, c2, c3]
      _ = n₀ * (a n₀)⁻¹ * ((r : L')⁻¹ * a (r : L')) := by rw [← c4]; group
      _ = s ⟨a, ha⟩ * (z ⟨a, ha⟩ * ((r : L')⁻¹ * a (r : L'))) := by rw [h0, mul_assoc]
      _ = s ⟨a, ha⟩ * ((r : L') * ((a (r : L'))⁻¹ * (r : L')⁻¹) * a (r : L')) := by
          rw [hzaL]; group
      _ = s ⟨a, ha⟩ := by rw [c5]; group
  rw [key]
  exact hs _

variable {G : Type} [Group G]

theorem eq_one_of_cube {Z : Subgroup G} (hZ2 : IsPGroup 2 Z) {c : G} (hc : c ∈ Z)
    (h3 : c ^ 3 = 1) : c = 1 := by
  obtain ⟨k, hk⟩ := hZ2 ⟨c, hc⟩
  have hk' : c ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have := pow_gcd_eq_one.mpr ⟨hk', h3⟩
  rwa [(Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, pow_one] at this

theorem comm_of_cube {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) (hZ2 : IsPGroup 2 Z)
    {x y : G} (hx : x ^ 3 = 1) (hc : (y * x)⁻¹ * (x * y) ∈ Z) : x * y = y * x := by
  set c := (y * x)⁻¹ * (x * y) with hcdef
  have hcen : ∀ g : G, g * c = c * g := fun g => Subgroup.mem_center_iff.mp (hZ hc) g
  have hxy : x * y = y * x * c := by rw [hcdef]; group
  have h1 : y⁻¹ * x * y = x * c := by
    calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
      _ = y⁻¹ * (y * x * c) := by rw [hxy]
      _ = x * c := by group
  have h2 : (y⁻¹ * x * y) ^ 3 = 1 := by
    have : (y⁻¹ * x * y) ^ 3 = y⁻¹ * x ^ 3 * y := by simp only [pow_succ, pow_zero, one_mul]; group
    rw [this, hx]; group
  have h3 : c ^ 3 = 1 := by
    rw [h1, Commute.mul_pow (show Commute x c from hcen x), hx, one_mul] at h2
    exact h2
  have := eq_one_of_cube hZ2 hc h3
  rw [hxy, this, mul_one]
theorem exists_lift_fixed {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'}
    {A : Subgroup (MulAut L')} (hZ : Z ≤ Subgroup.center L') (hZ2 : IsPGroup 2 Z)
    (hA3 : IsPGroup 3 A) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hZA : ∀ a ∈ A, ∀ z ∈ Z, a z ∈ Z) (n₀ : L')
    (h3 : ∀ a ∈ A, (n₀ * (a n₀)⁻¹) ^ 3 ∈ Z)
    (hfix : ∀ a ∈ A, ∀ a' ∈ A, (n₀ * (a n₀)⁻¹)⁻¹ * a' (n₀ * (a n₀)⁻¹) ∈ Z) :
    ∃ z ∈ Z, ∀ a ∈ A, ((n₀ * z) * (a (n₀ * z))⁻¹) ^ 3 = 1 ∧
      ∀ a' ∈ A, a' ((n₀ * z) * (a (n₀ * z))⁻¹) = (n₀ * z) * (a (n₀ * z))⁻¹ := by
  classical
  have hcen : ∀ y ∈ Z, ∀ g : L', g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hZ hy) g
  haveI hZn : Z.Normal := ⟨fun y hy g => by rw [hcen y hy g, mul_inv_cancel_right]; exact hy⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
  set m := (2 ^ k) ^ 2 with hm
  have hmZ : ∀ z ∈ Z, z ^ m = 1 := by
    intro z hz
    have : (⟨z, hz⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    rw [hk] at this
    have h' : z ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val this
    rw [hm, sq, pow_mul, h', one_pow]
  obtain ⟨j, hj⟩ : ∃ j, m = 3 * j + 1 := ⟨(m - 1) / 3, by
    have : m % 3 = 1 := by rw [hm, ← pow_mul, pow_mul', Nat.pow_mod]; norm_num
    omega⟩
  set u : MulAut L' → L' := fun a => n₀ * (a n₀)⁻¹ with hudef
  set s : MulAut L' → L' := fun a => u a ^ m with hsdef
  have hus : ∀ a ∈ A, (s a)⁻¹ * u a ∈ Z := by
    intro a ha
    have : (s a)⁻¹ * u a = ((u a ^ 3) ^ j)⁻¹ := by
      simp only [hsdef]; rw [hj, pow_succ, ← pow_mul]; group
    rw [this]; exact Z.inv_mem (Z.pow_mem (h3 a ha) j)
  have hs3 : ∀ a ∈ A, s a ^ 3 = 1 := by
    intro a ha
    simp only [hsdef]
    rw [← pow_mul, mul_comm, pow_mul]; exact hmZ _ (h3 a ha)
  have hsfix : ∀ a ∈ A, ∀ a' ∈ A, a' (s a) = s a := by
    intro a ha a' ha'
    have hw := hfix a ha a' ha'
    simp only [hsdef]
    have : a' (u a) = u a * ((u a)⁻¹ * a' (u a)) := by group
    rw [map_pow, this, Commute.mul_pow (hcen _ hw _), hmZ _ hw, mul_one]
  have hmk_s : ∀ a ∈ A, ((s a : L') : L' ⧸ Z) = ((u a : L') : L' ⧸ Z) := fun a ha =>
    QuotientGroup.eq.mpr (hus a ha)
  have hmk_fix : ∀ a ∈ A, ∀ a' ∈ A, ((a' (u a) : L') : L' ⧸ Z) = ((u a : L') : L' ⧸ Z) :=
    fun a ha a' ha' => (QuotientGroup.eq.mpr (hfix a ha a' ha')).symm
  have hu_mul : ∀ a b : MulAut L', u (a * b) = u a * a (u b) := by
    intro a b; simp only [hudef, MulAut.mul_apply, map_mul, map_inv]; group
  have hmk_u : ∀ a ∈ A, ∀ b ∈ A,
      ((u (a * b) : L') : L' ⧸ Z) = ((u a : L') : L' ⧸ Z) * ((u b : L') : L' ⧸ Z) := by
    intro a ha b hb
    rw [hu_mul, QuotientGroup.mk_mul, hmk_fix b hb a ha]
  have hscomm : ∀ a ∈ A, ∀ b ∈ A, s a * s b = s b * s a := by
    intro a ha b hb
    apply comm_of_cube hZ hZ2 (hs3 a ha)
    apply QuotientGroup.eq.mp
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hmk_s a ha, hmk_s b hb, ← hmk_u b hb a ha,
      ← hmk_u a ha b hb, hAc a ha b hb]
  have hsmul : ∀ a ∈ A, ∀ b ∈ A, s (a * b) = s a * s b := by
    intro a ha b hb
    have hc : (s (a * b))⁻¹ * (s a * s b) ∈ Z := by
      apply QuotientGroup.eq.mp
      rw [QuotientGroup.mk_mul, hmk_s a ha, hmk_s b hb, hmk_s _ (A.mul_mem ha hb),
        hmk_u a ha b hb]
    set c := (s (a * b))⁻¹ * (s a * s b) with hcdef
    have hsc : s a * s b = s (a * b) * c := by rw [hcdef]; group
    have h1 : (s a * s b) ^ 3 = 1 := by
      rw [Commute.mul_pow (hscomm a ha b hb), hs3 a ha, hs3 b hb, one_mul]
    rw [hsc, Commute.mul_pow (hcen c hc _), hs3 _ (A.mul_mem ha hb), one_mul] at h1
    rw [hsc, eq_one_of_cube hZ2 hc h1, mul_one]
  let σ : A →* L' :=
    { toFun := fun a => s a.1
      map_one' := by simp only [hsdef, hudef]; simp
      map_mul' := fun a b => hsmul a.1 a.2 b.1 b.2 }
  have hT3 : IsPGroup 3 σ.range := by
    rintro ⟨_, a, rfl⟩
    exact ⟨1, Subtype.ext (by simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]; exact hs3 a.1 a.2)⟩
  have hTA : ∀ a ∈ A, ∀ t ∈ σ.range, a t = t := by
    rintro a ha _ ⟨b, rfl⟩
    exact hsfix b.1 b.2 a ha
  have hn₀ : ∀ a ∈ A, n₀ * (a n₀)⁻¹ ∈ σ.range ⊔ Z := by
    intro a ha
    have : n₀ * (a n₀)⁻¹ = s a * ((s a)⁻¹ * u a) := by simp only [hudef]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨⟨a, ha⟩, rfl⟩)
      (Subgroup.mem_sup_right (hus a ha))
  obtain ⟨z, hz, hzT⟩ := exists_lift_weyl hZ hZ2 hT3 hA3 hZA hTA n₀ hn₀
  refine ⟨z, hz, fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := hzT a ha
  rw [← hb]
  exact ⟨hs3 b.1 b.2, fun a' ha' => hsfix b.1 b.2 a' ha'⟩

def twoPart {L' : Type} [Group L'] [Finite L'] (N : Subgroup L')
    (hN : N ≤ Subgroup.center L') : Subgroup L' where
  carrier := {z | z ∈ N ∧ z ^ (2 ^ Nat.card L') = 1}
  one_mem' := ⟨N.one_mem, one_pow _⟩
  mul_mem' := fun {x y} hx hy => ⟨N.mul_mem hx.1 hy.1, by
    rw [Commute.mul_pow (Subgroup.mem_center_iff.mp (hN hy.1) x), hx.2, hy.2, one_mul]⟩
  inv_mem' := fun {x} hx => ⟨N.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem pow_two_pow_card {L' : Type} [Group L'] [Finite L'] (x : L') {j : ℕ}
    (h : x ^ (2 ^ j) = 1) : x ^ (2 ^ Nat.card L') = 1 := by
  obtain ⟨i, -, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  have h1 : 2 ^ i ≤ Nat.card L' := hio ▸ orderOf_le_card
  have h2 : i < Nat.card L' := Nat.lt_two_pow_self.trans_le h1
  exact orderOf_dvd_iff_pow_eq_one.mp (hio ▸ pow_dvd_pow 2 h2.le)

theorem descent_noInvariantLine {L' R : Type} [Group L'] [Finite L'] [Group R]
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    {I : Set (MulAut R)} (hAI : ∀ a ∈ A, ∃ x ∈ I, ∀ l : L', x (ψ l) = ψ (a l))
    (H : ∀ (L₁ : Type) [Group L₁] [Finite L₁] (ψ₁ : L₁ →* R), Function.Surjective ψ₁ →
      ψ₁.ker ≤ Subgroup.center L₁ → commutator L₁ = ⊤ → Odd (Nat.card ψ₁.ker) →
      ∀ A₁ : Subgroup (MulAut L₁), CFSG.Open.IsElemAbelian 3 A₁ →
        (∀ a ∈ A₁, ∃ x ∈ I, ∀ l : L₁, x (ψ₁ l) = ψ₁ (a l)) → Nat.card A₁ = Nat.card A →
        ∃ W : Set L₁,
          (∀ n ∈ W, ∀ a ∈ A₁, (n * (a n)⁻¹) ^ 3 = 1 ∧
            ∀ a' ∈ A₁, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
          ∀ Λ : Subgroup (MulAut L₁), Λ ≤ A₁ → Nat.card Λ = 3 →
            ∃ n ∈ W, ∃ e ∈ Λ, MulAut.conj n * e * (MulAut.conj n)⁻¹ ∉ Λ) :
    ∃ W : Set L',
      (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      ∀ Λ : Subgroup (MulAut L'), Λ ≤ A → Nat.card Λ = 3 →
        ∃ n ∈ W, ∃ e ∈ Λ, MulAut.conj n * e * (MulAut.conj n)⁻¹ ∉ Λ := by
  classical
  set Z := twoPart ψ.ker hker with hZdef
  have hZc : Z ≤ Subgroup.center L' := fun z hz => hker hz.1
  have hcen : ∀ y ∈ Z, ∀ g : L', g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hZc hy) g
  haveI hZn : Z.Normal := ⟨fun y hy g => by rw [hcen y hy g, mul_inv_cancel_right]; exact hy⟩
  have hZ2 : IsPGroup 2 Z := fun g => ⟨Nat.card L', Subtype.ext (by simpa using g.2.2)⟩
  have hAp : ∀ a ∈ A, a ^ 3 = 1 := hA.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAp g.1 g.2)⟩
  have hkerA : ∀ a ∈ A, ∀ z ∈ ψ.ker, a z ∈ ψ.ker := by
    intro a ha z hz
    obtain ⟨x, -, hx⟩ := hAI a ha
    rw [MonoidHom.mem_ker, ← hx, (MonoidHom.mem_ker).mp hz, map_one]
  have hZA : ∀ a ∈ A, ∀ z ∈ Z, a z ∈ Z := fun a ha z hz =>
    ⟨hkerA a ha z hz.1, by rw [← map_pow, hz.2, map_one]⟩
  have hmap : ∀ a ∈ A, Z.map a.toMonoidHom = Z := by
    intro a ha
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩; exact hZA a ha z hz
    · intro z hz
      refine ⟨a⁻¹ z, hZA _ (A.inv_mem ha) z hz, ?_⟩
      simp
  have hπs : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  let ρf : A → MulAut (L' ⧸ Z) := fun a => QuotientGroup.congr Z Z a.1 (hmap a.1 a.2)
  have hρf : ∀ (a : A) (l : L'), ρf a (l : L' ⧸ Z) = ((a.1 l : L') : L' ⧸ Z) := fun a l =>
    QuotientGroup.congr_mk _ _ _ _ l
  let ρ : A →* MulAut (L' ⧸ Z) :=
    { toFun := ρf
      map_one' := by
        ext x
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
        rw [hρf]; rfl
      map_mul' := fun a b => by
        ext x
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
        simp only [MulAut.mul_apply, hρf]
        rfl }
  have hρ : ∀ (a : A) (l : L'), ρ a (l : L' ⧸ Z) = ((a.1 l : L') : L' ⧸ Z) := hρf
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hfixl : ∀ l : L', l⁻¹ * a.1 l ∈ Z := by
      intro l
      have := hρ a l
      rw [ha, MulAut.one_apply] at this
      exact QuotientGroup.eq.mp this
    letI : CommGroup Z :=
      { (inferInstance : Group Z) with mul_comm := fun x y => Subtype.ext (hcen y y.2 x) }
    let f : L' →* Z :=
      { toFun := fun l => ⟨l⁻¹ * a.1 l, hfixl l⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun l m => Subtype.ext (by
          show (l * m)⁻¹ * a.1 (l * m) = l⁻¹ * a.1 l * (m⁻¹ * a.1 m)
          have hc := hcen _ (hfixl l) m⁻¹
          calc (l * m)⁻¹ * a.1 (l * m) = m⁻¹ * (l⁻¹ * a.1 l) * a.1 m := by rw [map_mul]; group
            _ = (l⁻¹ * a.1 l) * m⁻¹ * a.1 m := by rw [hc]
            _ = l⁻¹ * a.1 l * (m⁻¹ * a.1 m) := by group) }
    have hf : ∀ l, f l = 1 := fun l =>
      Abelianization.commutator_subset_ker f (by rw [hperf]; exact Subgroup.mem_top l)
    apply Subtype.ext
    ext l
    have h1 : l⁻¹ * a.1 l = 1 := congrArg Subtype.val (hf l)
    exact (inv_mul_eq_one.mp h1).symm
  set A₁ := ρ.range with hA₁def
  have hA₁ : CFSG.Open.IsElemAbelian 3 A₁ := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      show ρ a * ρ b = ρ b * ρ a
      have : a * b = b * a := Subtype.ext (hAc a.1 a.2 b.1 b.2)
      rw [← map_mul, this, map_mul]
    · rintro _ ⟨a, rfl⟩
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hAp a.1 a.2)
      rw [← map_pow, this, map_one]
  have hcardA : Nat.card A₁ = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
  have hZψ : Z ≤ ψ.ker := fun z hz => hz.1
  let ψ₁ : L' ⧸ Z →* R := QuotientGroup.lift Z ψ hZψ
  have hψ₁ : ∀ l : L', ψ₁ (l : L' ⧸ Z) = ψ l := fun l => QuotientGroup.lift_mk _ _ _
  have hψ₁s : Function.Surjective ψ₁ := fun r => by
    obtain ⟨l, rfl⟩ := hψ r; exact ⟨l, hψ₁ l⟩
  have hψ₁ker : ψ₁.ker ≤ Subgroup.center (L' ⧸ Z) := by
    intro x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    have hl : l ∈ ψ.ker := by rw [MonoidHom.mem_ker, ← hψ₁]; exact hx
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hker hl) g]
  have hperf₁ : commutator (L' ⧸ Z) = ⊤ := by
    have : (commutator L').map (QuotientGroup.mk' Z) = commutator (L' ⧸ Z) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hπs]
    rw [← this, hperf, Subgroup.map_top_of_surjective _ hπs]
  have hodd : Odd (Nat.card ψ₁.ker) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hne)
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective x.1
    have hx2 : x.1 ^ 2 = 1 := by
      have := congrArg Subtype.val (pow_orderOf_eq_one x)
      rw [hx] at this; simpa using this
    have hl2 : l ^ 2 ∈ Z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hl, hx2]
    have hlker : l ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψ₁, hl]; exact x.2
    have hlZ : l ∈ Z := ⟨hlker, pow_two_pow_card l (j := Nat.card L' + 1)
      (by rw [pow_succ, pow_mul', hl2.2])⟩
    have : x = 1 := Subtype.ext (by rw [← hl]; exact (QuotientGroup.eq_one_iff l).mpr hlZ)
    rw [this, orderOf_one] at hx
    norm_num at hx
  have hAI₁ : ∀ a ∈ A₁, ∃ x ∈ I, ∀ l : L' ⧸ Z, x (ψ₁ l) = ψ₁ (a l) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨x, hx, hxa⟩ := hAI a.1 a.2
    refine ⟨x, hx, fun l => ?_⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l
    rw [hψ₁, hρ, hψ₁]; exact hxa l
  obtain ⟨W₁, hW₁, hmv₁⟩ := H (L' ⧸ Z) ψ₁ hψ₁s hψ₁ker hperf₁ hodd A₁ hA₁ hAI₁ hcardA
  refine ⟨{n | (∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      (n : L' ⧸ Z) ∈ W₁}, fun n hn => hn.1, ?_⟩
  intro Λ hΛA hΛ3
  set Λ₁ := (Λ.subgroupOf A).map ρ with hΛ₁def
  have hΛ₁A : Λ₁ ≤ A₁ := Subgroup.map_le_range _ _
  have hΛ₁3 : Nat.card Λ₁ = 3 := by
    rw [hΛ₁def, Subgroup.card_map_of_injective hρinj, ← hΛ3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛA).toEquiv
  obtain ⟨nb, hnb, eb, heb, hne⟩ := hmv₁ Λ₁ hΛ₁A hΛ₁3
  obtain ⟨e, heΛ, rfl⟩ := heb
  have heΛ' : e.1 ∈ Λ := Subgroup.mem_subgroupOf.mp heΛ
  obtain ⟨n₀, rfl⟩ := QuotientGroup.mk_surjective nb
  have hn₀ := hW₁ _ hnb
  have hu : ∀ a : A, ((n₀ * (a.1 n₀)⁻¹ : L') : L' ⧸ Z) = (n₀ : L' ⧸ Z) * (ρ a (n₀ : L' ⧸ Z))⁻¹ :=
    fun a => by rw [hρ, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have h3 : ∀ a ∈ A, (n₀ * (a n₀)⁻¹) ^ 3 ∈ Z := by
    intro a ha
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hu ⟨a, ha⟩]
    exact (hn₀ (ρ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).1
  have hfix : ∀ a ∈ A, ∀ a' ∈ A, (n₀ * (a n₀)⁻¹)⁻¹ * a' (n₀ * (a n₀)⁻¹) ∈ Z := by
    intro a ha a' ha'
    apply QuotientGroup.eq.mp
    rw [show ((a' (n₀ * (a n₀)⁻¹) : L') : L' ⧸ Z) =
        ρ ⟨a', ha'⟩ ((n₀ * (a n₀)⁻¹ : L') : L' ⧸ Z) from (hρ ⟨a', ha'⟩ _).symm, hu ⟨a, ha⟩]
    exact ((hn₀ (ρ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).2 _ ⟨⟨a', ha'⟩, rfl⟩).symm
  obtain ⟨z, hz, hzW⟩ := exists_lift_fixed hZc hZ2 hA3 hAc hZA n₀ h3 hfix
  have hz1 : ((z : L') : L' ⧸ Z) = 1 := (QuotientGroup.eq_one_iff z).mpr hz
  have hmk : ((n₀ * z : L') : L' ⧸ Z) = (n₀ : L' ⧸ Z) := by
    rw [QuotientGroup.mk_mul, hz1, mul_one]
  refine ⟨n₀ * z, ⟨hzW, by show ((n₀ * z : L') : L' ⧸ Z) ∈ W₁; rw [hmk]; exact hnb⟩, e.1, heΛ',
    fun hmem => hne ?_⟩
  set g := MulAut.conj (n₀ * z) * e.1 * (MulAut.conj (n₀ * z))⁻¹ with hgdef
  have hgA : g ∈ A := hΛA hmem
  refine ⟨⟨g, hgA⟩, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
  ext x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  have key := hρ e ((n₀ * z)⁻¹ * l * (n₀ * z))
  rw [hρ]
  simp only [hgdef, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hz1, mul_one] at key ⊢
  rw [key]

end CFSG.StandardType.Line63
