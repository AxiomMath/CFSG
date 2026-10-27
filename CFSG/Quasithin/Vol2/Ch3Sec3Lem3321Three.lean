module

public import CFSG.Quasithin.SteinbergCDBinaryLinearAutIndexThree
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316J
public import CFSG.Quasithin.EmptyFaithful.S146xB2Cmp

public section

namespace CFSG.Quasithin.H13.L3321

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Open

abbrev SL4 : Type := SpecialLinearGroup (Fin 4) (ZMod 2)

theorem eq_one_of_conj_eq (g : SL4) (hg : ∀ h : SL4, g * h * g⁻¹ = h) : g = 1 := by
  apply SteinbergCD.injective_conj_binarySL 4
  rw [map_one]
  exact MulEquiv.ext fun h => by rw [MulAut.conj_apply, hg h, MulAut.one_apply]

theorem exists_conj_of_pow_three (φ : MulAut SL4) (h3 : φ ^ 3 = 1) :
    ∃ g : SL4, φ = MulAut.conj g := by
  rcases SteinbergCD.aut_eq_conj_or_conj_mul_graphAut (n := 4) (by norm_num) φ with hφ | ⟨g, rfl⟩
  · exact hφ
  · exfalso
    set γ := BinaryParabolic.graphAut 4 with hγ
    have hγγ : γ * γ = 1 := MulEquiv.ext fun x => BinaryParabolic.graphFun_graphFun x
    have hc : ∀ k : SL4, γ * MulAut.conj k = MulAut.conj (γ k) * γ := by
      intro k
      have h1 := SteinbergCD.mulAut_mul_conj_mul_inv γ k
      calc γ * MulAut.conj k = γ * MulAut.conj k * γ⁻¹ * γ := by group
        _ = MulAut.conj (γ k) * γ := by rw [h1]
    have h2 : (MulAut.conj g * γ) ^ 2 = MulAut.conj (g * γ g) := by
      calc (MulAut.conj g * γ) ^ 2 = MulAut.conj g * (γ * MulAut.conj g) * γ := by
            rw [sq]; group
        _ = MulAut.conj g * MulAut.conj (γ g) * (γ * γ) := by rw [hc g]; group
        _ = MulAut.conj (g * γ g) := by rw [hγγ, mul_one, map_mul]
    have h1 : (MulAut.conj g * γ) ^ 3 = MulAut.conj (g * γ g * g) * γ := by
      rw [pow_succ, h2, ← mul_assoc, ← map_mul]
    rw [h1] at h3
    have key : γ = MulAut.conj (g * γ g * g)⁻¹ := by
      calc γ = (MulAut.conj (g * γ g * g))⁻¹ * (MulAut.conj (g * γ g * g) * γ) := by group
        _ = MulAut.conj (g * γ g * g)⁻¹ := by rw [h3, mul_one, map_inv]
    rw [hγ] at key
    exact SteinbergCD.graphAut_ne_conj (n := 4) (by norm_num) _ key

@[expose] def matW0 (x : ZMod 3 × ZMod 3) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] ^ (x.1 : ZMod 3).val *
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1] ^ (x.2 : ZMod 3).val

theorem det_matW0 : ∀ x, (matW0 x).det = 1 := by decide +kernel

theorem matW0_add : ∀ x y, matW0 (x + y) = matW0 x * matW0 y := by decide +kernel

theorem matW0_eq_one : ∀ x, matW0 x = 1 → x = 0 := by decide +kernel

@[expose] def homW0 : Multiplicative (ZMod 3 × ZMod 3) →* SL4 where
  toFun x := ⟨matW0 (Multiplicative.toAdd x), det_matW0 _⟩
  map_one' := by
    apply Subtype.ext
    show matW0 0 = 1
    decide +kernel
  map_mul' x y := by
    apply Subtype.ext
    show matW0 (Multiplicative.toAdd x + Multiplicative.toAdd y) = _
    rw [matW0_add]
    rfl

theorem homW0_injective : Function.Injective homW0 := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have h1 : matW0 (Multiplicative.toAdd x) = 1 := congrArg Subtype.val hx
  have h2 := matW0_eq_one _ h1
  rw [Subgroup.mem_bot]
  exact h2

abbrev W0 : Subgroup SL4 := homW0.range

theorem card_W0 : Nat.card W0 = 9 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective homW0_injective).toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem W0_comm {x y : SL4} (hx : x ∈ W0) (hy : y ∈ W0) : x * y = y * x := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem W0_pow {x : SL4} (hx : x ∈ W0) : x ^ 3 = 1 := by
  obtain ⟨u, rfl⟩ := hx
  rw [← map_pow]
  have : u ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    exact (by decide : ∀ z : ZMod 3 × ZMod 3, 3 • z = 0) _
  rw [this, map_one]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_pow_two_pow_three {X : Type*} [Group X] {g : X} {a b : ℕ}
    (h2 : g ^ 2 ^ a = 1) (h3 : g ^ 3 ^ b = 1) : g = 1 := by
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  have hc : Nat.gcd (2 ^ a) (3 ^ b) = 1 :=
    Nat.Coprime.pow a b (by norm_num : Nat.Coprime 2 3)
  rw [hc, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

omit [Finite G] in
theorem map_conj_pow_eq {L : Subgroup G} {α : ↥L →* SL4} {c : G}
    (hc : c ∈ Subgroup.normalizer (L : Set G))
    (hcα : ∀ l : ↥L, α ⟨c * l * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc l).mp l.2⟩ = α l)
    (m : ℕ) (l : ↥L) :
    α ⟨c ^ m * l * (c ^ m)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hc m) l).mp l.2⟩ = α l := by
  induction m generalizing l with
  | zero =>
    congr 1
    apply Subtype.ext
    simp
  | succ m ih =>
    have hm := (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hc m) l).mp l.2
    have h1 := hcα ⟨c ^ m * l * (c ^ m)⁻¹, hm⟩
    have e : (⟨c ^ (m + 1) * l * (c ^ (m + 1))⁻¹,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hc (m + 1)) l).mp l.2⟩ : ↥L) =
        ⟨c * (c ^ m * l * (c ^ m)⁻¹) * c⁻¹,
          (Subgroup.mem_normalizer_iff.mp hc _).mp hm⟩ := by
      apply Subtype.ext
      show c ^ (m + 1) * l * (c ^ (m + 1))⁻¹ = c * (c ^ m * l * (c ^ m)⁻¹) * c⁻¹
      rw [pow_succ']
      group
    rw [e, h1, ih]

theorem mem_of_orderOf_three {L H : Subgroup G} {α : ↥L →* SL4} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) (hH : IsTwoLocal H) (hLH : L ≤ H) (he : evenRank G ≤ 2)
    {x : G} (hxH : x ∈ H) (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : orderOf x = 3) :
    x ∈ L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hxL
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  obtain ⟨φ, hφ⟩ := L3316.exists_inducedAut hα hker hxN
  have hxxx : x * x * x = 1 := by
    have h := hx3'
    rw [pow_succ, pow_succ, pow_one] at h
    exact h
  have hφ3 : φ ^ 3 = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨l, rfl⟩ := hα y
    have hxl := (Subgroup.mem_normalizer_iff.mp hxN l).mp l.2
    have hxxl := (Subgroup.mem_normalizer_iff.mp hxN _).mp hxl
    have hxxxl := (Subgroup.mem_normalizer_iff.mp hxN _).mp hxxl
    have e3 : (⟨x * (x * (x * l * x⁻¹) * x⁻¹) * x⁻¹, hxxxl⟩ : ↥L) = l := by
      apply Subtype.ext
      show x * (x * (x * l * x⁻¹) * x⁻¹) * x⁻¹ = l
      calc x * (x * (x * l * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * l * (x * x * x)⁻¹ := by group
        _ = l := by rw [hxxx, one_mul, inv_one, mul_one]
    calc (φ ^ 3) (α l) = φ (φ (φ (α l))) := by
          rw [pow_succ, pow_succ, pow_one]
          rfl
      _ = φ (φ (α ⟨_, hxl⟩)) := by rw [hφ l]
      _ = φ (α ⟨_, hxxl⟩) := by rw [hφ ⟨_, hxl⟩]
      _ = α ⟨_, hxxxl⟩ := by rw [hφ ⟨_, hxxl⟩]
      _ = α l := by rw [e3]
      _ = (1 : MulAut SL4) (α l) := rfl
  obtain ⟨g, hg⟩ := exists_conj_of_pow_three φ hφ3
  obtain ⟨l₀, hl₀⟩ := hα g
  have hl₀N : (l₀ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l₀.2
  set c : G := (l₀ : G)⁻¹ * x with hcdef
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hl₀N) hxN
  have hcH : c ∈ H := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLH l₀.2)) hxH
  have hcα : ∀ l : ↥L, α ⟨c * l * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN l).mp l.2⟩ = α l := by
    intro l
    have hxl := (Subgroup.mem_normalizer_iff.mp hxN l).mp l.2
    have e : (⟨c * l * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN l).mp l.2⟩ : ↥L) =
        l₀⁻¹ * ⟨x * l * x⁻¹, hxl⟩ * l₀ := by
      apply Subtype.ext
      show (l₀ : G)⁻¹ * x * l * ((l₀ : G)⁻¹ * x)⁻¹ = (l₀ : G)⁻¹ * (x * l * x⁻¹) * l₀
      group
    rw [e, map_mul, map_mul, map_inv, ← hφ l, hg, MulAut.conj_apply, hl₀]
    group
  have hc3L : c ^ 3 ∈ L := by
    have e : c ^ 3 = (l₀ : G)⁻¹ * (x * (l₀ : G)⁻¹ * x⁻¹) * (x * x * (l₀ : G)⁻¹ * x⁻¹ * x⁻¹) *
        (x * x * x) := by
      rw [hcdef, pow_succ, pow_succ, pow_one]
      group
    rw [e, hxxx, mul_one]
    have h1 : x * (l₀ : G)⁻¹ * x⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hxN _).mp (L.inv_mem l₀.2)
    have h2 : x * x * (l₀ : G)⁻¹ * x⁻¹ * x⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp hxN _).mp h1
      simpa [mul_assoc] using this
    exact L.mul_mem (L.mul_mem (L.inv_mem l₀.2) h1) h2
  have hc3α : α ⟨c ^ 3, hc3L⟩ = 1 := by
    apply eq_one_of_conj_eq
    intro y
    obtain ⟨l, rfl⟩ := hα y
    have h1 := map_conj_pow_eq hcN hcα 3 l
    rw [← map_inv, ← map_mul, ← map_mul, ← h1]
    congr 1
  have hc3O : (⟨c ^ 3, hc3L⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← hker]
    exact hc3α
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hc3O⟩
  have hk' : (c ^ 3) ^ 2 ^ k = 1 := by
    have := congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => ((y : ↥L) : G)) hk
    simpa using this
  set c' : G := c ^ 2 ^ k with hc'def
  have hc'3 : c' ^ 3 = 1 := by
    rw [hc'def, ← pow_mul, mul_comm, pow_mul, hk']
  have hc'L : c' ∉ L := by
    intro hc'
    apply hxL
    have hcL : c ∈ L := by
      obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (2 ^ k : ℤ) * u + 3 * v = 1 := by
        have hcop : IsCoprime ((2 : ℤ) ^ k) 3 :=
          IsCoprime.pow_left (by norm_num : IsCoprime (2 : ℤ) 3)
        obtain ⟨u, v, h⟩ := hcop
        exact ⟨u, v, by linarith⟩
      have e : c = (c' ^ u) * ((c ^ 3) ^ v) := by
        rw [hc'def, ← _root_.zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_natCast,
          ← _root_.zpow_mul, ← _root_.zpow_add]
        nth_rewrite 1 [← _root_.zpow_one c]
        congr 1
        push_cast
        linarith
      rw [e]
      exact L.mul_mem (L.zpow_mem hc' u) (L.zpow_mem hc3L v)
    have e : x = (l₀ : G) * c := by rw [hcdef]; group
    rw [e]
    exact L.mul_mem l₀.2 hcL
  have hc'1 : c' ≠ 1 := fun h1 => hc'L (h1 ▸ L.one_mem)
  have hc'o : orderOf c' = 3 := orderOf_eq_prime hc'3 hc'1
  have hc'N : c' ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hcN _
  have hc'H : c' ∈ H := Subgroup.pow_mem _ hcH _
  have hc'α : ∀ l : ↥L, α ⟨c' * l * c'⁻¹, (Subgroup.mem_normalizer_iff.mp hc'N l).mp l.2⟩ =
      α l := fun l => map_conj_pow_eq hcN hcα (2 ^ k) l
  have hzN : Subgroup.zpowers c' ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.zpowers_le).2 hc'N
  let act : ↥(Subgroup.zpowers c') →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hzN)
  have hact : ∀ (a : ↥(Subgroup.zpowers c')) (l : ↥L), ((act a l : ↥L) : G) =
      (a : G) * l * (a : G)⁻¹ := fun a l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L _ l
  have hNa : ∀ a : ↥(Subgroup.zpowers c'), ∀ n ∈ CFSG.pCore 2 ↥L, act a n ∈ CFSG.pCore 2 ↥L :=
    fun a n hn => by
      have h1 := (CFSG.pCore_characteristic (p := 2) (G := ↥L)).fixed (act a).symm
      have h2 : act a n ∈ (CFSG.pCore 2 ↥L).comap (act a).symm.toMonoidHom := by
        rw [Subgroup.mem_comap]
        simpa using hn
      rwa [h1] at h2
  have hA3 : IsPGroup 3 ↥(Subgroup.zpowers c') := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hc'o]
    exact ⟨1, by norm_num⟩
  have hcop : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hm]
    intro h3
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hA3
    act (CFSG.pCore 2 ↥L) hNa hcop
  have hcent : ∀ l : ↥L, ∃ y : ↥L, (y : G) * c' = c' * y ∧ α y = α l := by
    intro l
    have hmem : (l : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ {q : ↥L ⧸ CFSG.pCore 2 ↥L |
        ∀ a : ↥(Subgroup.zpowers c'),
          CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction act _ hNa a q = q} := by
      intro a
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk, QuotientGroup.eq,
        ← hker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
      have h1 : act a l = ⟨(a : G) * l * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp
          (hzN a.2) l).mp l.2⟩ := Subtype.ext (hact a l)
      rw [h1]
      have key : ∀ m : ℤ, ∀ l : ↥L, α ⟨c' ^ m * l * (c' ^ m)⁻¹, (Subgroup.mem_normalizer_iff.mp
          (Subgroup.zpow_mem _ hc'N m) l).mp l.2⟩ = α l := by
        intro m l
        have hc'ord : c' ^ (3 : ℤ) = 1 := by rw [_root_.zpow_ofNat]; exact hc'3
        have hm' : c' ^ m = c' ^ ((m % 3).toNat) := by
          rw [← _root_.zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))]
          conv_lhs => rw [← Int.emod_add_mul_ediv m 3, _root_.zpow_add, _root_.zpow_mul, hc'ord,
            _root_.one_zpow,
            mul_one]
        have e : (⟨c' ^ m * l * (c' ^ m)⁻¹, (Subgroup.mem_normalizer_iff.mp
            (Subgroup.zpow_mem _ hc'N m) l).mp l.2⟩ : ↥L) =
            ⟨c' ^ ((m % 3).toNat) * l * (c' ^ ((m % 3).toNat))⁻¹,
              (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hc'N _) l).mp l.2⟩ :=
          Subtype.ext (by simp only [hm'])
        rw [e]
        exact map_conj_pow_eq hc'N hc'α _ l
      have e2 : (⟨(a : G) * l * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hzN a.2) l).mp
          l.2⟩ : ↥L) = ⟨c' ^ m * l * (c' ^ m)⁻¹, (Subgroup.mem_normalizer_iff.mp
            (Subgroup.zpow_mem _ hc'N m) l).mp l.2⟩ := by
        apply Subtype.ext
        show (a : G) * l * (a : G)⁻¹ = c' ^ m * l * (c' ^ m)⁻¹
        rw [hm]
      rw [e2, key m l]
    rw [hlift] at hmem
    obtain ⟨y, hy, hyl⟩ := hmem
    refine ⟨y, ?_, ?_⟩
    · have h1 := hy ⟨c', Subgroup.mem_zpowers c'⟩
      have h2 := congrArg Subtype.val h1
      rw [hact] at h2
      calc (y : G) * c' = (c' * y * c'⁻¹) * c' := by rw [h2]
        _ = c' * y := by group
    · have h1 : ((y : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = (l : ↥L ⧸ CFSG.pCore 2 ↥L) := hyl
      rw [QuotientGroup.eq, ← hker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
      exact h1
  let K₁ : Subgroup ↥L := W0.comap α ⊓ (Subgroup.centralizer ({c'} : Set G)).comap L.subtype
  let f : ↥K₁ →* ↥W0 := (α.comp K₁.subtype).codRestrict W0 fun y => y.2.1
  have hfs : Function.Surjective f := by
    intro w
    obtain ⟨l, hl⟩ := hα w
    obtain ⟨y, hyc, hyl⟩ := hcent l
    refine ⟨⟨y, ?_, ?_⟩, Subtype.ext ?_⟩
    · show α y ∈ W0
      rw [hyl, hl]
      exact w.2
    · show (y : G) ∈ Subgroup.centralizer ({c'} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyc
    · show α y = w
      rw [hyl, hl]
  have hfk : ∀ y : ↥K₁, f y = 1 → ∃ n : ℕ, y ^ 2 ^ n = 1 := by
    intro y hy
    have h1 : ((y : ↥L)) ∈ CFSG.pCore 2 ↥L := by
      rw [← hker, MonoidHom.mem_ker]
      exact congrArg Subtype.val hy
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, h1⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hn
    simpa using this
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥K₁) := inferInstance
  have h9 : 3 ^ 2 ∣ Nat.card ↥K₁ := by
    have := Subgroup.card_dvd_of_surjective (f := f) hfs
    rw [card_W0] at this
    exact this
  have h9P := P.pow_dvd_card_of_pow_dvd_card h9
  obtain ⟨v, hv⟩ := (IsPGroup.iff_card).1 P.isPGroup'
  have hv2 : 2 ≤ v := by
    rw [hv] at h9P
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h9P
  have hP1 : ∀ p ∈ (P : Subgroup ↥K₁), f p = 1 → p = 1 := by
    intro p hp hfp
    obtain ⟨n, hn⟩ := hfk p hfp
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨p, hp⟩
    have hm' : p ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    exact eq_one_of_pow_two_pow_three hn hm'
  have hPe : IsElemAbelian 3 (P : Subgroup ↥K₁) := by
    refine ⟨⟨⟨fun p q => Subtype.ext ?_⟩⟩, fun p hp => ?_⟩
    · show (p : ↥K₁) * q = q * p
      have h1 : f ((p : ↥K₁) * q * (p : ↥K₁)⁻¹ * (q : ↥K₁)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
        rw [W0_comm (f p).2 (f q).2]
        group
      have h2 := hP1 _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ p.2 q.2)
        (Subgroup.inv_mem _ p.2)) (Subgroup.inv_mem _ q.2)) h1
      calc (p : ↥K₁) * q = ((p : ↥K₁) * q * (p : ↥K₁)⁻¹ * (q : ↥K₁)⁻¹) * (q * p) := by group
        _ = q * p := by rw [h2, one_mul]
    · refine hP1 _ (Subgroup.pow_mem _ hp 3) ?_
      rw [map_pow]
      exact Subtype.ext (W0_pow (f p).2)
  set E : Subgroup G := ((P : Subgroup ↥K₁).map K₁.subtype).map L.subtype with hEdef
  have hEe : IsElemAbelian 3 E :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hPe _) _
  have hEc : Nat.card E = 3 ^ v := by
    rw [hEdef, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective K₁.subtype_injective, hv]
  have hEL : E ≤ L := Subgroup.map_subtype_le _
  have hEC : ∀ e ∈ E, e * c' = c' * e := by
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    have h1 := y.2.2
    have h2 : ((y : ↥L) : G) ∈ Subgroup.centralizer ({c'} : Set G) := h1
    rw [Subgroup.mem_centralizer_singleton_iff] at h2
    exact h2
  have hQe : IsElemAbelian 3 (Subgroup.zpowers c') := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
      obtain ⟨m', hm'⟩ := Subgroup.mem_zpowers_iff.1 b.2
      show (a : G) * b = b * a
      rw [← hm, ← hm', ← _root_.zpow_add, ← _root_.zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, _root_.zpow_natCast,
        hc'3, _root_.one_zpow]
  have hQc : Nat.card (Subgroup.zpowers c') = 3 ^ 1 := by
    rw [Nat.card_zpowers, hc'o, pow_one]
  have hdisj : Subgroup.zpowers c' ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyQ, hyE⟩
    rw [Subgroup.mem_bot]
    by_contra hy1
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyQ
    apply hc'L
    have hord : orderOf (c' ^ m) = 3 := by
      have hd := orderOf_dvd_of_pow_eq_one (show (c' ^ m) ^ 3 = 1 by
        rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
          _root_.zpow_natCast, hc'3, _root_.one_zpow])
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hy1
      · exact h
    have hmem : c' ∈ Subgroup.zpowers (c' ^ m) := by
      have hle : Subgroup.zpowers (c' ^ m) ≤ Subgroup.zpowers c' :=
        (Subgroup.zpowers_le).2 hyQ
      have hc : Nat.card (Subgroup.zpowers (c' ^ m)) = Nat.card (Subgroup.zpowers c') := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hord, hc'o]
      have := Subgroup.eq_of_le_of_card_ge hle hc.ge
      rw [this]
      exact Subgroup.mem_zpowers c'
    exact (Subgroup.zpowers_le.2 (hEL hyE)) hmem
  have hcomm : ∀ a ∈ Subgroup.zpowers c', ∀ e ∈ E, a * e = e * a := by
    intro a ha e heE
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have h1 : Commute e c' := hEC e heE
    exact (h1.zpow_right m).symm.eq
  have hrk := le_pRank_of_commute_of_inf_eq_bot' Nat.prime_three hQe hEe hcomm hdisj hQc hEc
    ((Subgroup.zpowers_le).2 hc'H) (hEL.trans hLH)
  have hle := A1b.pRank_le_evenRank Nat.prime_three (by norm_num) hH
  omega

end CFSG.Quasithin.H13.L3321
