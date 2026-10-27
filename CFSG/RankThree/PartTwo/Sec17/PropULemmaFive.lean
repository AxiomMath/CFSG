module

public import CFSG.RankThree.PartTwo.Sec17.PropUStepTwoA
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Arith
public import CFSG.RankThree.OddKernel.FixedPlaneKernel
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec17
  CFSG.GH74.GLS
open scoped commutatorElement

theorem pu_E1_mem_center_of_pow {K : Type} [Group K] [Finite K] {k : ℕ} (g : K)
    (h3K : ¬ 3 ∣ Nat.card (K ⧸ Subgroup.center K)) (hg : g ^ (3 ^ k) ∈ Subgroup.center K) :
    g ∈ Subgroup.center K := by
  have h4 : ((g : K ⧸ Subgroup.center K)) ^ (3 ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hg
  have h5 : orderOf (g : K ⧸ Subgroup.center K) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h4
  have h6 : orderOf (g : K ⧸ Subgroup.center K) ∣ Nat.card (K ⧸ Subgroup.center K) :=
    orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (K ⧸ Subgroup.center K)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3K)
  have h7 := Nat.dvd_gcd h5 h6
  rw [Nat.Coprime.gcd_eq_one hcop] at h7
  have h8 : (g : K ⧸ Subgroup.center K) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h7)
  exact (QuotientGroup.eq_one_iff g).mp h8

theorem pu_E1_conj_eq_one_iff {K : Type} [Group K] (g : K) :
    (MulAut.conj g : MulAut K) = 1 ↔ g ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h x
    have hx : g * x * g⁻¹ = x := by
      have := congrArg (fun f : MulAut K => f x) h
      simpa using this
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  · intro h
    ext x
    show g * x * g⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact (h x).symm

theorem eq_one_of_out_abelian {X : Type} [Group X] [Finite X]
    (hX3 : oPrimeResidual 3 X = ⊤) (hXJ : Nonempty (X ⧸ CFSG.pCore 2 X ≃* J2)) {K : Type}
    [Group K] [Finite K] (hout : commutator (MulAut K) ≤ (MulAut.conj : K →* MulAut K).range)
    (h3K : ¬ 3 ∣ Nat.card (K ⧸ Subgroup.center K)) (φ : X →* MulAut K) : φ = 1 := by
  obtain ⟨e⟩ := hXJ
  haveI hJ2 : IsSimpleGroup J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hS : IsSimpleGroup (X ⧸ CFSG.pCore 2 X) := MulEquiv.isSimpleGroup e
  haveI : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hIn : ((MulAut.conj : K →* MulAut K).range).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal K
  have hMn : ((MulAut.conj : K →* MulAut K).range.comap φ).Normal :=
    Subgroup.Normal.comap hIn φ
  have hF5 := CFSG.RankThree.PartTwo.Sec17.PropU.normal_le_or_eq_top (CFSG.pCore 2 X)
    CFSG.pCore_isPGroup hS hX3 ((MulAut.conj : K →* MulAut K).range.comap φ)
  have hM : (MulAut.conj : K →* MulAut K).range.comap φ = ⊤ := by
    rcases hF5 with hle | htop
    · exfalso
      have hcomm : commutator X ≤ CFSG.pCore 2 X := by
        refine Subgroup.commutator_le.mpr ?_
        intro a _ b _
        have hab : φ ⁅a, b⁆ ∈ (MulAut.conj : K →* MulAut K).range := by
          rw [map_commutatorElement]
          exact hout (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
        exact hle (Subgroup.mem_comap.mpr hab)
      haveI : IsMulCommutative (X ⧸ CFSG.pCore 2 X) :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
      have hp := (Group.is_simple_iff_prime_card (α := X ⧸ CFSG.pCore 2 X)).mp hS
      rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2] at hp
      norm_num at hp
    · exact htop
  have hinner : ∀ x : X, φ x ∈ (MulAut.conj : K →* MulAut K).range := fun x => by
    have hx : x ∈ (MulAut.conj : K →* MulAut K).range.comap φ := by
      rw [hM]
      exact Subgroup.mem_top x
    exact Subgroup.mem_comap.mp hx
  have hker : oPrimeResidual 3 X ≤ φ.ker := by
    unfold oPrimeResidual
    rw [Subgroup.closure_le]
    rintro x ⟨k, hk⟩
    show x ∈ φ.ker
    rw [MonoidHom.mem_ker]
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hinner x)
    have h1 : (φ x) ^ (3 ^ k) = 1 := by
      rw [← map_pow φ x (3 ^ k), hk, map_one]
    have h2 : (MulAut.conj (g ^ (3 ^ k)) : MulAut K) = 1 := by
      rw [map_pow (MulAut.conj : K →* MulAut K) g (3 ^ k), hg, h1]
    have h3 : g ^ (3 ^ k) ∈ Subgroup.center K := (pu_E1_conj_eq_one_iff _).mp h2
    have h4 : g ∈ Subgroup.center K := pu_E1_mem_center_of_pow g h3K h3
    rw [← hg]
    exact (pu_E1_conj_eq_one_iff g).mpr h4
  rw [hX3] at hker
  have hall : ∀ x : X, φ x = 1 := fun x => MonoidHom.mem_ker.mp (hker (Subgroup.mem_top x))
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.one_apply]
  exact hall x

theorem card_ker_pow_ge {A B : Type} [CommGroup A] [Finite A] [CommGroup B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) {p : ℕ} (hB : ∀ b : B, b ^ p = 1) :
    Nat.card B ≤ Nat.card (powMonoidHom p : A →* A).ker := by
  have h1 : Nat.card (powMonoidHom p : A →* A).ker * Nat.card (powMonoidHom p : A →* A).range
      = Nat.card A := Subgroup.card_ker_mul_card_range (powMonoidHom p : A →* A)
  have h3 : Nat.card f.ker * Nat.card B = Nat.card A :=
    Subgroup.card_ker_mul_card_of_surjective hf
  have h2 : (powMonoidHom p : A →* A).range ≤ f.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    show f (a ^ p) = 1
    rw [map_pow, hB]
  have h4 : Nat.card (powMonoidHom p : A →* A).range ≤ Nat.card f.ker :=
    Subgroup.card_le_of_le h2
  have hpos : 0 < Nat.card (powMonoidHom p : A →* A).range := Nat.card_pos
  have h5 : Nat.card B * Nat.card (powMonoidHom p : A →* A).range
      ≤ Nat.card (powMonoidHom p : A →* A).ker * Nat.card (powMonoidHom p : A →* A).range := by
    calc Nat.card B * Nat.card (powMonoidHom p : A →* A).range
        ≤ Nat.card B * Nat.card f.ker := Nat.mul_le_mul le_rfl h4
      _ = Nat.card f.ker * Nat.card B := Nat.mul_comm _ _
      _ = Nat.card A := h3
      _ = Nat.card (powMonoidHom p : A →* A).ker
            * Nat.card (powMonoidHom p : A →* A).range := h1.symm
  exact Nat.le_of_mul_le_mul_right h5 hpos

theorem exists_pElement_lift (p : ℕ) [Fact p.Prime] {K : Type} [Group K] [Finite K]
    (hp : p ∣ Nat.card (K ⧸ Subgroup.center K)) :
    ∃ x : K, (∃ m : ℕ, x ^ (p ^ m) = 1) ∧ ∀ a : ℕ, x ^ a ∈ Subgroup.center K → p ∣ a := by
  obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card' p hp
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective xb
  have hne : orderOf x₀ ≠ 0 := (orderOf_pos x₀).ne'
  obtain ⟨m, r, hr, hdec⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hne p (Fact.out : p.Prime).one_lt.ne'
  have hcop : Nat.Coprime (orderOf (x₀ : K ⧸ Subgroup.center K)) r := by
    rw [hxb]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hr
  have hord : orderOf ((x₀ : K ⧸ Subgroup.center K) ^ r) = p :=
    (Nat.Coprime.orderOf_pow hcop).trans hxb
  refine ⟨x₀ ^ r, ⟨m, ?_⟩, ?_⟩
  · rw [← pow_mul, show r * p ^ m = orderOf x₀ by rw [hdec, Nat.mul_comm], pow_orderOf_eq_one]
  · intro a ha
    have h2 := (QuotientGroup.eq_one_iff (N := Subgroup.center K) ((x₀ ^ r) ^ a)).mpr ha
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_pow] at h2
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rwa [hord] at h3

theorem pu_dvd_of_zpow_mem_center {H : Type} [Group H] {x : H}
    (hp : ∃ m : ℕ, x ^ (5 ^ m) = 1) (hi : ∀ n : ℕ, x ^ n ∈ Subgroup.center H → 5 ∣ n)
    (a : ℤ) (ha : x ^ a ∈ Subgroup.center H) : (5 : ℤ) ∣ a := by
  obtain ⟨m, hm⟩ := hp
  have hN : x ^ ((5 : ℤ) ^ (m + 1)) = 1 := by
    have e : (5 : ℤ) ^ (m + 1) = ((5 ^ (m + 1) : ℕ) : ℤ) := by norm_cast
    rw [e, zpow_natCast, pow_succ, pow_mul, hm, one_pow]
  have hN0 : (5 : ℤ) ^ (m + 1) ≠ 0 := by positivity
  have hnn : 0 ≤ a % (5 : ℤ) ^ (m + 1) := Int.emod_nonneg a hN0
  have e1 : x ^ a = x ^ (a % (5 : ℤ) ^ (m + 1)) := zpow_eq_zpow_emod a hN
  have e2 : x ^ (a % (5 : ℤ) ^ (m + 1)).toNat = x ^ (a % (5 : ℤ) ^ (m + 1)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
  have hmem : x ^ (a % (5 : ℤ) ^ (m + 1)).toNat ∈ Subgroup.center H := by
    rw [e2, ← e1]
    exact ha
  have h5 : (5 : ℤ) ∣ ((a % (5 : ℤ) ^ (m + 1)).toNat : ℤ) := by
    exact_mod_cast hi _ hmem
  rw [Int.toNat_of_nonneg hnn] at h5
  have h5N : (5 : ℤ) ∣ (5 : ℤ) ^ (m + 1) := dvd_pow_self 5 (Nat.succ_ne_zero m)
  rw [← Int.emod_add_mul_ediv a ((5 : ℤ) ^ (m + 1))]
  exact dvd_add h5 (dvd_mul_of_dvd_left h5N _)

theorem pu_coord {G : Type} [Group G] {K : Subgroup G} {x : K}
    (hp : ∃ m : ℕ, x ^ (5 ^ m) = 1) (hi : ∀ n : ℕ, x ^ n ∈ Subgroup.center ↥K → 5 ∣ n)
    {v w : G} (hv : ∀ g ∈ K, g * v = v * g) (hw : ∀ g ∈ K, g * w = w * g)
    (a : ℤ) (h : (x : G) ^ a * (v * w) = 1) : (5 : ℤ) ∣ a := by
  have hxa : (x : G) ^ a = (v * w)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hc : x ^ a ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgv : Commute (g : G) v := hv (g : G) g.2
    have hgw : Commute (g : G) w := hw (g : G) g.2
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
    rw [hxa]
    exact (hgv.mul_right hgw).inv_right.eq
  exact pu_dvd_of_zpow_mem_center hp hi a hc

theorem pu_exists_of_quot {G : Type} [Group G] [Finite G] {P : Type} [CommGroup P]
    (mu : P →* G)
    (eps : P →* Multiplicative (ZMod 5) × (Multiplicative (ZMod 5) × Multiplicative (ZMod 5)))
    (hker : mu.ker ≤ eps.ker) (hsurj : Function.Surjective eps) :
    ∃ E : Subgroup G, E ≤ mu.range ∧ CFSG.Assembly.IsElemAbelian 5 E ∧ 125 ≤ Nat.card E := by
  have hι : Function.Injective (QuotientGroup.kerLift mu) := QuotientGroup.kerLift_injective mu
  haveI : Finite (P ⧸ mu.ker) := Finite.of_injective _ hι
  have hχ : Function.Surjective (QuotientGroup.lift mu.ker eps hker) := by
    intro b
    obtain ⟨v, rfl⟩ := hsurj b
    exact ⟨(v : P ⧸ mu.ker), rfl⟩
  have hz : ∀ z : Multiplicative (ZMod 5), z ^ 5 = 1 := fun z => by
    rw [← toAdd_eq_zero, toAdd_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hB : ∀ b : Multiplicative (ZMod 5) × (Multiplicative (ZMod 5) × Multiplicative (ZMod 5)),
      b ^ 5 = 1 := by
    rintro ⟨b₁, b₂, b₃⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hz]
  have hcard := card_ker_pow_ge (QuotientGroup.lift mu.ker eps hker) hχ hB
  have hBcard : Nat.card (Multiplicative (ZMod 5) × (Multiplicative (ZMod 5) × Multiplicative (ZMod 5)))
      = 125 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod]
  rw [hBcard] at hcard
  refine ⟨((powMonoidHom 5 : (P ⧸ mu.ker) →* (P ⧸ mu.ker)).ker).map (QuotientGroup.kerLift mu),
    ?_, ?_, ?_⟩
  · rintro _ ⟨q, -, rfl⟩
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    exact MonoidHom.mem_range.mpr ⟨v, (QuotientGroup.kerLift_mk mu v).symm⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · show a * b = b * a
      apply Subtype.ext
      obtain ⟨q₁, -, h₁⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨q₂, -, h₂⟩ := Subgroup.mem_map.mp b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← h₁, ← h₂, ← map_mul, ← map_mul, mul_comm]
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      have hq5 : q ^ 5 = 1 := by simpa using MonoidHom.mem_ker.mp hq
      rw [← map_pow, hq5, map_one]
  · rw [Subgroup.card_map_of_injective hι]
    exact hcard

theorem exists_elemAbelian_of_independent {G : Type} [Group G] [Finite G] {K₂ K₃ K₄ : Subgroup G}
    (h23 : ∀ a ∈ K₂, ∀ b ∈ K₃, a * b = b * a) (h24 : ∀ a ∈ K₂, ∀ b ∈ K₄, a * b = b * a)
    (h34 : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a) {x₂ : ↥K₂} {x₃ : ↥K₃} {x₄ : ↥K₄}
    (hp₂ : ∃ m : ℕ, x₂ ^ (5 ^ m) = 1) (hp₃ : ∃ m : ℕ, x₃ ^ (5 ^ m) = 1)
    (hp₄ : ∃ m : ℕ, x₄ ^ (5 ^ m) = 1)
    (hi₂ : ∀ a : ℕ, x₂ ^ a ∈ Subgroup.center ↥K₂ → 5 ∣ a)
    (hi₃ : ∀ a : ℕ, x₃ ^ a ∈ Subgroup.center ↥K₃ → 5 ∣ a)
    (hi₄ : ∀ a : ℕ, x₄ ^ a ∈ Subgroup.center ↥K₄ → 5 ∣ a) :
    ∃ E : Subgroup G, E ≤ K₂ ⊔ K₃ ⊔ K₄ ∧ CFSG.Assembly.IsElemAbelian 5 E ∧ 125 ≤ Nat.card E := by
  have c23 : ∀ m n : ℤ, Commute ((x₂ : G) ^ m) ((x₃ : G) ^ n) := fun m n =>
    h23 _ (zpow_mem x₂.2 m) _ (zpow_mem x₃.2 n)
  have c24 : ∀ m n : ℤ, Commute ((x₂ : G) ^ m) ((x₄ : G) ^ n) := fun m n =>
    h24 _ (zpow_mem x₂.2 m) _ (zpow_mem x₄.2 n)
  have c34 : ∀ m n : ℤ, Commute ((x₃ : G) ^ m) ((x₄ : G) ^ n) := fun m n =>
    h34 _ (zpow_mem x₃.2 m) _ (zpow_mem x₄.2 n)
  have c34' : ∀ m n : Multiplicative ℤ,
      Commute (zpowersHom G (x₃ : G) m) (zpowersHom G (x₄ : G) n) := by
    intro m n
    simp only [zpowersHom_apply]
    exact c34 _ _
  have c2 : ∀ (m : Multiplicative ℤ) (n : Multiplicative ℤ × Multiplicative ℤ),
      Commute (zpowersHom G (x₂ : G) m)
        (((zpowersHom G (x₃ : G)).noncommCoprod (zpowersHom G (x₄ : G)) c34') n) := by
    intro m n
    simp only [MonoidHom.noncommCoprod_apply, zpowersHom_apply]
    exact (c23 _ _).mul_right (c24 _ _)
  obtain ⟨mu, hmu⟩ : ∃ f : (Multiplicative ℤ × (Multiplicative ℤ × Multiplicative ℤ)) →* G,
      ∀ v, f v = (x₂ : G) ^ Multiplicative.toAdd v.1 *
        ((x₃ : G) ^ Multiplicative.toAdd v.2.1 * (x₄ : G) ^ Multiplicative.toAdd v.2.2) :=
    ⟨(zpowersHom G (x₂ : G)).noncommCoprod
      ((zpowersHom G (x₃ : G)).noncommCoprod (zpowersHom G (x₄ : G)) c34') c2, fun v => rfl⟩
  have hind : ∀ a b c : ℤ, (x₂ : G) ^ a * ((x₃ : G) ^ b * (x₄ : G) ^ c) = 1 →
      (5 : ℤ) ∣ a ∧ (5 : ℤ) ∣ b ∧ (5 : ℤ) ∣ c := by
    intro a b c h
    have ha : (5 : ℤ) ∣ a := pu_coord (K := K₂) (x := x₂) (v := (x₃ : G) ^ b)
      (w := (x₄ : G) ^ c) hp₂ hi₂ (fun g hg => h23 g hg _ (zpow_mem x₃.2 b))
      (fun g hg => h24 g hg _ (zpow_mem x₄.2 c)) a h
    have hb' : (x₃ : G) ^ b * ((x₂ : G) ^ a * (x₄ : G) ^ c) = 1 := by
      rw [← mul_assoc, ← (c23 a b).eq, mul_assoc]
      exact h
    have hb : (5 : ℤ) ∣ b := pu_coord (K := K₃) (x := x₃) (v := (x₂ : G) ^ a)
      (w := (x₄ : G) ^ c) hp₃ hi₃ (fun g hg => (h23 _ (zpow_mem x₂.2 a) g hg).symm)
      (fun g hg => h34 g hg _ (zpow_mem x₄.2 c)) b hb'
    have hc' : (x₄ : G) ^ c * ((x₂ : G) ^ a * (x₃ : G) ^ b) = 1 := by
      rw [← mul_assoc, ← (c24 a c).eq, mul_assoc, ← (c34 b c).eq]
      exact h
    have hc : (5 : ℤ) ∣ c := pu_coord (K := K₄) (x := x₄) (v := (x₂ : G) ^ a)
      (w := (x₃ : G) ^ b) hp₄ hi₄ (fun g hg => (h24 _ (zpow_mem x₂.2 a) g hg).symm)
      (fun g hg => (h34 _ (zpow_mem x₃.2 b) g hg).symm) c hc'
    exact ⟨ha, hb, hc⟩
  obtain ⟨eps₀, heps₀⟩ : ∃ f : Multiplicative ℤ →* Multiplicative (ZMod 5),
      ∀ x : Multiplicative ℤ, f x = Multiplicative.ofAdd ((Multiplicative.toAdd x : ℤ) : ZMod 5) :=
    ⟨(Int.castAddHom (ZMod 5)).toMultiplicative, fun x => rfl⟩
  obtain ⟨eps, heps⟩ : ∃ f : (Multiplicative ℤ × (Multiplicative ℤ × Multiplicative ℤ)) →*
      (Multiplicative (ZMod 5) × (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))),
      ∀ v, f v = (eps₀ v.1, eps₀ v.2.1, eps₀ v.2.2) :=
    ⟨eps₀.prodMap (eps₀.prodMap eps₀), fun v => rfl⟩
  have key5 : ∀ x : Multiplicative ℤ, (5 : ℤ) ∣ Multiplicative.toAdd x → eps₀ x = 1 := by
    intro x hx
    rw [← toAdd_eq_zero, heps₀, toAdd_ofAdd]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr (by exact_mod_cast hx)
  have hker : mu.ker ≤ eps.ker := by
    intro v hv
    rw [MonoidHom.mem_ker, hmu] at hv
    obtain ⟨h1, h2, h3⟩ := hind _ _ _ hv
    rw [MonoidHom.mem_ker, heps]
    exact Prod.ext (key5 _ h1) (Prod.ext (key5 _ h2) (key5 _ h3))
  have hsurj : Function.Surjective eps := by
    rintro ⟨b₁, b₂, b₃⟩
    obtain ⟨n₁, hn₁⟩ := ZMod.intCast_surjective (Multiplicative.toAdd b₁)
    obtain ⟨n₂, hn₂⟩ := ZMod.intCast_surjective (Multiplicative.toAdd b₂)
    obtain ⟨n₃, hn₃⟩ := ZMod.intCast_surjective (Multiplicative.toAdd b₃)
    refine ⟨(Multiplicative.ofAdd n₁, (Multiplicative.ofAdd n₂, Multiplicative.ofAdd n₃)), ?_⟩
    simp [heps, heps₀, hn₁, hn₂, hn₃]
  obtain ⟨E, hE₁, hE₂, hE₃⟩ := pu_exists_of_quot mu eps hker hsurj
  refine ⟨E, ?_, hE₂, hE₃⟩
  have hK₂ : K₂ ≤ K₂ ⊔ K₃ ⊔ K₄ := le_trans le_sup_left le_sup_left
  have hK₃ : K₃ ≤ K₂ ⊔ K₃ ⊔ K₄ := le_trans le_sup_right le_sup_left
  have hK₄ : K₄ ≤ K₂ ⊔ K₃ ⊔ K₄ := le_sup_right
  intro y hy
  obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp (hE₁ hy)
  rw [hmu]
  exact mul_mem (hK₂ (zpow_mem x₂.2 _))
    (mul_mem (hK₃ (zpow_mem x₃.2 _)) (hK₄ (zpow_mem x₄.2 _)))

theorem component_facts
    {N : Type} [Group N] [Finite N] (hK : CFSG.IsKGroup N)
    (h3 : ¬ 3 ∣ Nat.card N) {K : Subgroup N} (hKc : CFSG.IsComponent K) :
    Group.IsPerfect ↥K ∧ ¬ 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) ∧
      5 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) ∧ 2 ∣ Nat.card ↥K ∧
      commutator (MulAut ↥K) ≤ (MulAut.conj : ↥K →* MulAut ↥K).range := by
  have hperf : Group.IsPerfect ↥K := hKc.1.1
  haveI hsimp : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKc.1.2.1
  have hnab : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a := hKc.1.2.2
  obtain ⟨f, hf⟩ := CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_isKGroup_section hK h3 K
    (Subgroup.center ↥K) hnab
  have hdvdN : Nat.card (↥K ⧸ Subgroup.center ↥K) ∣ Nat.card N :=
    dvd_trans (Subgroup.card_quotient_dvd_card _) (Subgroup.card_subgroup_dvd_card K)
  have h3Q : ¬ 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := fun h => h3 (dvd_trans h hdvdN)
  have h2Q : 2 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.RankThree.PartTwo.KFacts.two_dvd_card_of_suzukiModel hf
  have h2K : 2 ∣ Nat.card ↥K := dvd_trans h2Q (Subgroup.card_quotient_dvd_card _)
  have hcyc : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
    ((CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0}
      (↥K ⧸ Subgroup.center ↥K) 2 f hf).2 ↥K ⟨MulEquiv.refl _⟩).1
  have hcomm : IsMulCommutative (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) := by
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
    exact zpow_mul_comm g m n
  have hnorm : (MulAut.conj : ↥K →* MulAut ↥K).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal ↥K
  have hout : commutator (MulAut ↥K) ≤ (MulAut.conj : ↥K →* MulAut ↥K).range :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp hcomm
  obtain ⟨-, a, -, F, hFld, hFin, hfdef, hFcard, ⟨e⟩⟩ := hf
  rw [hfdef] at hFcard
  have hcardQ : Nat.card (↥K ⧸ Subgroup.center ↥K) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) :=
    (Nat.card_congr e.toEquiv).trans (CFSG.LieType.Ree.suzuki_order hFcard)
  have h5Q : 5 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    rw [hcardQ]
    exact dvd_mul_of_dvd_right
      (CFSG.SignalizerFunctorTheorem.McBride.SzModel.five_dvd_sq_add_one a) _
  exact ⟨hperf, h3Q, h5Q, h2K, hout⟩

theorem pu_comm_of_ne {N : Type} [Group N] [Finite N] {K L : Subgroup N}
    (hK : CFSG.IsComponent K) (hL : CFSG.IsComponent L) (hne : K ≠ L) :
    ∀ a ∈ K, ∀ b ∈ L, a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
  · exact absurd h hne
  · intro a ha b hb
    have hle : K ≤ Subgroup.centralizer (L : Set N) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm

theorem false_of_four_components {N : Type} [Group N] [Finite N]
    (hrank : ∀ t : N, orderOf t = 2 → ∀ E : Subgroup N, E ≤ Subgroup.centralizer {t} →
      CFSG.Assembly.IsElemAbelian 5 E → Nat.card E ≤ 25)
    {K₁ K₂ K₃ K₄ : Subgroup N} (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h14 : K₁ ≠ K₄) (h23 : K₂ ≠ K₃)
    (h24 : K₂ ≠ K₄) (h34 : K₃ ≠ K₄) (c₁ : CFSG.IsComponent K₁) (c₂ : CFSG.IsComponent K₂)
    (c₃ : CFSG.IsComponent K₃) (c₄ : CFSG.IsComponent K₄) (e₁ : 2 ∣ Nat.card ↥K₁)
    (f₂ : 5 ∣ Nat.card (↥K₂ ⧸ Subgroup.center ↥K₂)) (f₃ : 5 ∣ Nat.card (↥K₃ ⧸ Subgroup.center ↥K₃))
    (f₄ : 5 ∣ Nat.card (↥K₄ ⧸ Subgroup.center ↥K₄)) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have m₂₃ := pu_comm_of_ne c₂ c₃ h23
  have m₂₄ := pu_comm_of_ne c₂ c₄ h24
  have m₃₄ := pu_comm_of_ne c₃ c₄ h34
  have hc₁₂ := pu_comm_of_ne c₁ c₂ h12
  have hc₁₃ := pu_comm_of_ne c₁ c₃ h13
  have hc₁₄ := pu_comm_of_ne c₁ c₄ h14
  obtain ⟨x₂, hx₂p, hx₂i⟩ := exists_pElement_lift 5 f₂
  obtain ⟨x₃, hx₃p, hx₃i⟩ := exists_pElement_lift 5 f₃
  obtain ⟨x₄, hx₄p, hx₄i⟩ := exists_pElement_lift 5 f₄
  obtain ⟨E, hE, hEel, h125⟩ :=
    exists_elemAbelian_of_independent m₂₃ m₂₄ m₃₄ hx₂p hx₃p hx₄p hx₂i hx₃i hx₄i
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 e₁
  have ht2 : orderOf (t : N) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hcent : K₂ ⊔ K₃ ⊔ K₄ ≤ Subgroup.centralizer {(t : N)} := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc₁₂ (t : N) t.2 a ha).symm
    · intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc₁₃ (t : N) t.2 a ha).symm
    · intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc₁₄ (t : N) t.2 a ha).symm
  have hbound := hrank (t : N) ht2 E (hE.trans hcent) hEel
  omega

abbrev pu_Comp (N : Type) [Group N] : Type := {K : Subgroup N // CFSG.IsComponent K}

def pu_act {N X : Type} [Group N] [Group X] (φ : X →* MulAut N) (x : X) (K : pu_Comp N) :
    pu_Comp N :=
  ⟨K.1.map (φ x).toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv (φ x) K.2⟩

abbrev pu_mulAction {N X : Type} [Group N] [Group X] (φ : X →* MulAut N) :
    MulAction X (pu_Comp N) where
  smul x K := pu_act φ x K
  one_smul K := by
    apply Subtype.ext
    show K.1.map (φ 1).toMonoidHom = K.1
    rw [map_one]
    ext n
    constructor
    · rintro ⟨m, hm, rfl⟩
      simpa using hm
    · intro hn
      exact ⟨n, hn, by simp⟩
  mul_smul x y K := by
    apply Subtype.ext
    show K.1.map (φ (x * y)).toMonoidHom = (K.1.map (φ y).toMonoidHom).map (φ x).toMonoidHom
    rw [Subgroup.map_map, map_mul]
    rfl

theorem pu_finite_comp (N : Type) [Group N] [Finite N] : Finite (pu_Comp N) := by
  haveI : Finite (Subgroup N) :=
    Finite.of_injective (SetLike.coe : Subgroup N → Set N) SetLike.coe_injective
  infer_instance

theorem pu_card_le_three {N : Type} [Group N] [Finite N]
    (hcomp : ∀ K₁ K₂ K₃ K₄ : Subgroup N, K₁ ≠ K₂ → K₁ ≠ K₃ → K₁ ≠ K₄ → K₂ ≠ K₃ → K₂ ≠ K₄ →
      K₃ ≠ K₄ → CFSG.IsComponent K₁ → CFSG.IsComponent K₂ → CFSG.IsComponent K₃ →
      CFSG.IsComponent K₄ → False) :
    Nat.card (pu_Comp N) ≤ 3 := by
  classical
  haveI := pu_finite_comp N
  by_contra hlt
  have hlt' : 3 < Nat.card (pu_Comp N) := not_le.mp hlt
  haveI : Fintype (pu_Comp N) := Fintype.ofFinite _
  have h4 : Fintype.card (Fin 4) ≤ Fintype.card (pu_Comp N) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h4
  have hinj : ∀ i j : Fin 4, i ≠ j → (e i).1 ≠ (e j).1 := fun i j hij h =>
    hij (e.injective (Subtype.ext h))
  exact hcomp (e 0).1 (e 1).1 (e 2).1 (e 3).1 (hinj 0 1 (by decide)) (hinj 0 2 (by decide))
    (hinj 0 3 (by decide)) (hinj 1 2 (by decide)) (hinj 1 3 (by decide)) (hinj 2 3 (by decide))
    (e 0).2 (e 1).2 (e 2).2 (e 3).2

theorem fixes_components {N : Type} [Group N] [Finite N]
    (hcomp : ∀ K₁ K₂ K₃ K₄ : Subgroup N, K₁ ≠ K₂ → K₁ ≠ K₃ → K₁ ≠ K₄ → K₂ ≠ K₃ → K₂ ≠ K₄ →
      K₃ ≠ K₄ → CFSG.IsComponent K₁ → CFSG.IsComponent K₂ → CFSG.IsComponent K₃ →
      CFSG.IsComponent K₄ → False)
    {X : Type} [Group X] [Finite X] (hX3 : oPrimeResidual 3 X = ⊤)
    (hXJ : Nonempty (X ⧸ CFSG.pCore 2 X ≃* J2)) (φ : X →* MulAut N) {K : Subgroup N}
    (hK : CFSG.IsComponent K) (x : X) : K.map (φ x).toMonoidHom = K := by
  classical
  obtain ⟨e⟩ := hXJ
  haveI : IsSimpleGroup J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  haveI hsimple : IsSimpleGroup (X ⧸ CFSG.pCore 2 X) := MulEquiv.isSimpleGroup e
  haveI := pu_finite_comp N
  have hcard := pu_card_le_three hcomp
  letI := pu_mulAction φ
  obtain ⟨σ, hσ⟩ : ∃ σ : X →* Equiv.Perm (pu_Comp N), ∀ (y : X) (L : pu_Comp N),
      σ y L = pu_act φ y L :=
    ⟨MulAction.toPermHom X (pu_Comp N), fun _ _ => rfl⟩
  rcases normal_le_or_eq_top (CFSG.pCore 2 X) CFSG.pCore_isPGroup hsimple hX3 σ.ker with
    hle | htop
  · exfalso
    have hdvd : (CFSG.pCore 2 X).index ∣ σ.ker.index := Subgroup.index_dvd_of_le hle
    have hidx : (CFSG.pCore 2 X).index = 604800 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
    have hle6 : σ.ker.index ≤ 6 := by
      rw [show σ.ker.index = Nat.card (X ⧸ σ.ker) from rfl,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange σ).toEquiv]
      calc Nat.card σ.range ≤ Nat.card (Equiv.Perm (pu_Comp N)) :=
            Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
        _ = Nat.factorial (Nat.card (pu_Comp N)) := Nat.card_perm
        _ ≤ Nat.factorial 3 := Nat.factorial_le hcard
        _ = 6 := rfl
    rw [hidx] at hdvd
    have hpos : 0 < σ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have := Nat.le_of_dvd hpos hdvd
    omega
  · have hx : x ∈ σ.ker := by
      rw [htop]
      exact Subgroup.mem_top x
    have h1 : σ x = 1 := MonoidHom.mem_ker.mp hx
    have h2 : (σ x ⟨K, hK⟩).1 = K := by
      rw [h1]
      rfl
    rw [hσ] at h2
    exact h2

@[expose] def restrictAut {N X : Type} [Group N] [Group X] (φ : X →* MulAut N) (K : Subgroup N)
    (hfix : ∀ x : X, K.map (φ x).toMonoidHom = K) : X →* MulAut ↥K where
  toFun x :=
    { toFun := fun k => ⟨φ x k, (hfix x).le (Subgroup.mem_map_of_mem _ k.2)⟩
      invFun := fun k => ⟨φ x⁻¹ k, (hfix x⁻¹).le (Subgroup.mem_map_of_mem _ k.2)⟩
      left_inv := fun k => Subtype.ext (by
        change φ x⁻¹ (φ x (k : N)) = k
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun k => Subtype.ext (by
        change φ x (φ x⁻¹ (k : N)) = k
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun a b => Subtype.ext (by
        change φ x ((a : N) * (b : N)) = φ x (a : N) * φ x (b : N)
        exact map_mul _ _ _) }
  map_one' := by
    refine MulEquiv.ext fun k => Subtype.ext ?_
    change φ 1 (k : N) = (k : N)
    rw [map_one, MulAut.one_apply]
  map_mul' x y := by
    refine MulEquiv.ext fun k => Subtype.ext ?_
    change φ (x * y) (k : N) = φ x (φ y (k : N))
    rw [map_mul, MulAut.mul_apply]

theorem coe_restrictAut {N X : Type} [Group N] [Group X] (φ : X →* MulAut N) (K : Subgroup N)
    (hfix : ∀ x : X, K.map (φ x).toMonoidHom = K) (x : X) (k : ↥K) :
    ((restrictAut φ K hfix x k : ↥K) : N) = φ x (k : N) := rfl

theorem pe_abstract
    {N : Type} [Group N] [Finite N] (hK : CFSG.IsKGroup N) (h3 : ¬ 3 ∣ Nat.card N)
    (hrank : ∀ t : N, orderOf t = 2 → ∀ E : Subgroup N, E ≤ Subgroup.centralizer {t} →
      CFSG.Assembly.IsElemAbelian 5 E → Nat.card E ≤ 25)
    {X : Type} [Group X] [Finite X] (hX3 : oPrimeResidual 3 X = ⊤)
    (hXJ : Nonempty (X ⧸ CFSG.pCore 2 X ≃* J2)) (φ : X →* MulAut N) :
    ∀ x : X, ∀ e ∈ CFSG.layer N, φ x e = e := by
  classical
  have hcomp : ∀ K₁ K₂ K₃ K₄ : Subgroup N, K₁ ≠ K₂ → K₁ ≠ K₃ → K₁ ≠ K₄ → K₂ ≠ K₃ → K₂ ≠ K₄ →
      K₃ ≠ K₄ → CFSG.IsComponent K₁ → CFSG.IsComponent K₂ → CFSG.IsComponent K₃ →
      CFSG.IsComponent K₄ → False := fun K₁ K₂ K₃ K₄ h12 h13 h14 h23 h24 h34 c₁ c₂ c₃ c₄ =>
    false_of_four_components hrank h12 h13 h14 h23 h24 h34 c₁ c₂ c₃ c₄
      (component_facts hK h3 c₁).2.2.2.1 (component_facts hK h3 c₂).2.2.1
      (component_facts hK h3 c₃).2.2.1 (component_facts hK h3 c₄).2.2.1
  have hcent : ∀ K : Subgroup N, CFSG.IsComponent K → ∀ x : X, ∀ k ∈ K, φ x k = k := by
    intro K hKc x k hk
    have hfix : ∀ y : X, K.map (φ y).toMonoidHom = K := fun y =>
      fixes_components hcomp hX3 hXJ φ hKc y
    obtain ⟨-, h3K, -, -, hout⟩ := component_facts hK h3 hKc
    have h1 := eq_one_of_out_abelian hX3 hXJ hout h3K (restrictAut φ K hfix)
    have h2 := coe_restrictAut φ K hfix x ⟨k, hk⟩
    rw [h1] at h2
    simpa using h2.symm
  intro x e he
  let F : Subgroup N :=
    { carrier := {e | φ x e = e}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢
        rw [ha, hb]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_inv] at ha ⊢
        rw [ha] }
  have hle : CFSG.layer N ≤ F := by
    rw [CFSG.layer.eq_sSup]
    exact sSup_le fun K hK k hk => hcent K hK x k hk
  exact hle he

theorem pe_layer
    {G : Type} [Group G] [Finite G] (hloc : CFSG.Assembly.RankThreeEven.localRank 5 G < 3)
    {N₀ X : Subgroup G} (hK : CFSG.IsKGroup ↥N₀) (h3 : ¬ 3 ∣ Nat.card N₀)
    (hXN : X ≤ Subgroup.normalizer (N₀ : Set G)) (hX3 : oPrimeResidualOf 3 X = X)
    (hXJ : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* J2)) :
    X ≤ Subgroup.centralizer ((inSubgroup CFSG.layer N₀ : Subgroup G) : Set G) := by
  have hX3' : oPrimeResidual 3 ↥X = ⊤ := by
    have hmap : Subgroup.map X.subtype (⊤ : Subgroup ↥X) = X := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    apply Subgroup.map_injective X.subtype_injective
    rw [hmap]
    exact hX3
  have hrank : ∀ t : ↥N₀, orderOf t = 2 → ∀ E : Subgroup ↥N₀, E ≤ Subgroup.centralizer {t} →
      CFSG.Assembly.IsElemAbelian 5 E → Nat.card E ≤ 25 := by
    intro t ht E hEc hE
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hEle : E.map N₀.subtype ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hte := Subgroup.mem_centralizer_iff.1 (hEc he) t (Set.mem_singleton t)
      have := congrArg Subtype.val hte
      simpa using this
    have hEel : CFSG.Open.IsElemAbelian 5 (E.map N₀.subtype) :=
      CFSG.SectionRank.isElemAbelian_map hE N₀.subtype
    have hcard : Nat.card (E.map N₀.subtype) = Nat.card E :=
      Subgroup.card_map_of_injective N₀.subtype_injective
    have hpow : IsPGroup 5 E := by
      intro g
      refine ⟨1, ?_⟩
      rw [pow_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 _ g.2
    obtain ⟨r, hr⟩ := (IsPGroup.iff_card).1 hpow
    have hr2 : r ≤ CFSG.Open.pRank 5 (Subgroup.centralizer ({(t : G)} : Set G)) :=
      CFSG.SectionRank.le_pRank (by norm_num) hEle hEel (hcard.trans hr)
    have hbound : CFSG.pRank 5 ↥(Subgroup.centralizer ({(t : G)} : Set G)) ≤
        CFSG.Assembly.RankThreeEven.localRank 5 G :=
      CFSG.RankThree.OddKernel.pRank_centralizer_le_localRank (by norm_num)
        ((Subgroup.orderOf_coe t).trans ht)
    have hOpen : CFSG.Open.pRank 5 (Subgroup.centralizer ({(t : G)} : Set G)) =
        CFSG.pRank 5 ↥(Subgroup.centralizer ({(t : G)} : Set G)) :=
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).trans
        (CFSG.SectionRank.pRank_eq_open_pRank_top 5 _).symm
    have hr3 : r ≤ 2 := by omega
    calc Nat.card E = 5 ^ r := hr
      _ ≤ 5 ^ 2 := Nat.pow_le_pow_right (by norm_num) hr3
      _ = 25 := by norm_num
  have key := pe_abstract hK h3 hrank hX3' hXJ (N₀.normalizerMonoidHom.comp (Subgroup.inclusion hXN))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh' : h ∈ inSubgroup CFSG.layer N₀ := hh
  obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.1 hh'
  have hc := congrArg Subtype.val (key ⟨x, hx⟩ e₀ he₀)
  have hc' : (x : G) * (e₀ : G) * (x : G)⁻¹ = (e₀ : G) := hc
  exact (mul_inv_eq_iff_eq_mul.1 hc').symm

end CFSG.RankThree.PartTwo.Sec17.PropU
