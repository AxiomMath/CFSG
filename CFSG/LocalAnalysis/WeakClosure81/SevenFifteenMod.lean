module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.WeakClosure81.SevenFifteenLinear
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G]

private noncomputable def conjEnd (N : Subgroup G) [IsElementaryAbelian 2 ↥N] :
    ↥(Subgroup.normalizer (N : Set G)) →* Module.End (ZMod 2) (Additive ↥N) where
  toFun w := AddMonoidHom.toZModLinearMap 2
    (MonoidHom.toAdditive (Subgroup.normalizerMonoidHom N w).toMonoidHom)
  map_one' := LinearMap.ext fun a => Additive.toMul.injective (by
    simp [MonoidHom.toAdditive])
  map_mul' := fun g h => LinearMap.ext fun a => Additive.toMul.injective (by
    simp [MonoidHom.toAdditive, map_mul])

private theorem conjEnd_apply (N : Subgroup G) [IsElementaryAbelian 2 ↥N]
    (w : ↥(Subgroup.normalizer (N : Set G))) (a : Additive ↥N) :
    (((conjEnd N w) a).toMul : G) = (w : G) * (a.toMul : G) * (w : G)⁻¹ :=
  rfl

private lemma mem_inf_centralizer_of_conjEnd_eq (N : Subgroup G) [IsElementaryAbelian 2 ↥N]
    {w : G} (hwN : w ∈ Subgroup.normalizer (N : Set G)) {a : Additive ↥N}
    (ha : conjEnd N ⟨w, hwN⟩ a = a) :
    (a.toMul : G) ∈ N ⊓ Subgroup.centralizer ({w} : Set G) := by
  refine ⟨a.toMul.2, ?_⟩
  show (a.toMul : G) ∈ Subgroup.centralizer ({w} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h : (((conjEnd N ⟨w, hwN⟩ a).toMul : ↥N) : G) = (a.toMul : G) :=
    congrArg (fun x : ↥N => (x : G)) (congrArg Additive.toMul ha)
  rw [conjEnd_apply] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

private lemma conjEnd_sub_one_toMul (I : Subgroup G) [IsElementaryAbelian 2 ↥I]
    {v : G} (hvI : v ∈ Subgroup.normalizer (I : Set G)) (b : Additive ↥I) :
    (((conjEnd I ⟨v, hvI⟩ - 1) b).toMul : G) = ⁅(b.toMul : G), v⁆⁻¹ := by
  rw [commutatorElement_inv, commutatorElement_def]
  rw [LinearMap.sub_apply, Module.End.one_apply, toMul_sub, Subgroup.coe_div, div_eq_mul_inv,
    conjEnd_apply]

private noncomputable def fixedSubgroupEquiv (I : Subgroup G) [IsElementaryAbelian 2 ↥I]
    {v : G} (hvI : v ∈ Subgroup.normalizer (I : Set G)) :
    ↥(I ⊓ Subgroup.centralizer ({v} : Set G)) ≃
      ↥(LinearMap.ker (conjEnd I ⟨v, hvI⟩ - 1)) where
  toFun a := ⟨Additive.ofMul ⟨a.1, a.2.1⟩, by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    apply (Additive.toMul (α := ↥I)).injective
    apply Subtype.ext
    rw [conjEnd_apply]
    have ha : (a.1 : G) * v = v * a.1 := Subgroup.mem_centralizer_singleton_iff.mp a.2.2
    simp only [toMul_ofMul, Subgroup.coe_mk]
    rw [← ha]
    group⟩
  invFun b := ⟨(b.1.toMul : G), mem_inf_centralizer_of_conjEnd_eq I hvI (by
    have hb := LinearMap.mem_ker.mp b.2
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hb)⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv b := by
    apply Subtype.ext
    apply (Additive.toMul (α := ↥I)).injective
    apply Subtype.ext
    rfl

theorem le_iSup_inf_centralizer {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {N : Subgroup G}
    (hN : IsElemAbelian 2 N) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) (hyN : y ∈ Subgroup.normalizer (N : Set G))
    (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hxy : ∀ a ∈ N, x * (y * a * y⁻¹) * x⁻¹ = y * (x * a * x⁻¹) * y⁻¹)
    (hfix : N ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) = ⊥) :
    N ≤ (⨆ b : ZMod p, N ⊓ Subgroup.centralizer ({x * y ^ b.val} : Set G)) ⊔
      (N ⊓ Subgroup.centralizer ({y} : Set G)) := by
  letI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  letI : IsElementaryAbelian 2 ↥N := isElemAbelian_iff_isElementaryAbelian.mp hN
  set σ : Module.End (ZMod 2) (Additive ↥N) := conjEnd N ⟨x, hxN⟩ with hσdef
  set τ : Module.End (ZMod 2) (Additive ↥N) := conjEnd N ⟨y, hyN⟩ with hτdef
  let T : Subgroup G := (⨆ b : ZMod p, N ⊓ Subgroup.centralizer ({x * y ^ b.val} : Set G)) ⊔
    (N ⊓ Subgroup.centralizer ({y} : Set G))
  have hστ : Commute σ τ := by
    rw [Commute, hσdef, hτdef]
    refine LinearMap.ext fun a => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply]
    apply (Additive.toMul (α := ↥N)).injective
    apply Subtype.ext
    rw [conjEnd_apply, conjEnd_apply, conjEnd_apply, conjEnd_apply]
    exact hxy a.toMul a.toMul.2
  have hxp' : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (N : Set G))) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hxp]
    rfl
  have hyp' : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (N : Set G))) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hyp]
    rfl
  have hσ : σ ^ p = 1 := by
    rw [hσdef, ← map_pow, hxp', map_one]
  have hτ : τ ^ p = 1 := by
    rw [hτdef, ← map_pow, hyp', map_one]
  have hfixLin : ∀ a : Additive ↥N, σ a = a → τ a = a → a = 0 := by
    intro a ha hb
    have hxa : (a.toMul : G) ∈ N ⊓ Subgroup.centralizer ({x} : Set G) := by
      rw [hσdef] at ha
      exact mem_inf_centralizer_of_conjEnd_eq N hxN ha
    have hya : (a.toMul : G) ∈ N ⊓ Subgroup.centralizer ({y} : Set G) := by
      rw [hτdef] at hb
      exact mem_inf_centralizer_of_conjEnd_eq N hyN hb
    have hbot : (a.toMul : G) ∈ (⊥ : Subgroup G) := by
      have hmem : (a.toMul : G) ∈ N ⊓ Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G) := ⟨hxa, hya.2⟩
      rwa [hfix] at hmem
    exact toMul_eq_one.mp (Subtype.ext (Subgroup.mem_bot.mp hbot))
  have hmem : ∀ b : ZMod p, x * y ^ b.val ∈ Subgroup.normalizer (N : Set G) := fun b =>
    (Subgroup.normalizer (N : Set G)).mul_mem hxN
      ((Subgroup.normalizer (N : Set G)).pow_mem hyN b.val)
  have hσb : ∀ b : ZMod p, σ * τ ^ b.val = conjEnd N ⟨x * y ^ b.val, hmem b⟩ := by
    intro b
    have h1 : (⟨x, hxN⟩ * ⟨y, hyN⟩ ^ b.val : ↥(Subgroup.normalizer (N : Set G))) =
        ⟨x * y ^ b.val, hmem b⟩ := by
      apply Subtype.ext
      simp [Subgroup.coe_mul, Subgroup.coe_pow]
    calc σ * τ ^ b.val = conjEnd N (⟨x, hxN⟩ * ⟨y, hyN⟩ ^ b.val) := by
          rw [hσdef, hτdef, ← map_pow, ← map_mul]
      _ = conjEnd N ⟨x * y ^ b.val, hmem b⟩ := by rw [h1]
  intro n hn
  change n ∈ T
  let nN : ↥N := ⟨n, hn⟩
  obtain ⟨f, c, hf, hc, hsum⟩ :=
    exists_eq_sum_of_commute (M := Additive ↥N) hp hστ hσ hτ hfixLin (Additive.ofMul nN)
  have hprod : (∏ b : ZMod p, (f b).toMul) ∈ T.comap N.subtype := by
    refine Subgroup.prod_mem _ (fun b _ => ?_)
    rw [Subgroup.mem_comap]
    have hfb : conjEnd N ⟨x * y ^ b.val, hmem b⟩ (f b) = f b := by
      have h := hf b
      rwa [hσb b] at h
    have hmemfb : ((f b).toMul : G) ∈ N ⊓ Subgroup.centralizer ({x * y ^ b.val} : Set G) :=
      mem_inf_centralizer_of_conjEnd_eq N (hmem b) hfb
    exact Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem b hmemfb)
  have hcT : c.toMul ∈ T.comap N.subtype := by
    rw [Subgroup.mem_comap]
    have hc' : τ c = c := hc
    rw [hτdef] at hc'
    exact Subgroup.mem_sup_right (mem_inf_centralizer_of_conjEnd_eq N hyN hc')
  have hprodT : (((∏ b : ZMod p, (f b).toMul) : ↥N) : G) ∈ T := Subgroup.mem_comap.mp hprod
  have hcT' : (c.toMul : G) ∈ T := Subgroup.mem_comap.mp hcT
  have hn_eq : nN = (∏ b : ZMod p, (f b).toMul) * c.toMul := by
    have h := congrArg Additive.toMul hsum
    simpa [nN, toMul_add, toMul_sum] using h
  have : (nN : G) ∈ T := by
    rw [hn_eq, Subgroup.coe_mul]
    exact T.mul_mem hprodT hcT'
  exact this

theorem exists_card_eq_pow_of_inverting_involution {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    [Finite G] {I : Subgroup G} (hI : IsElemAbelian 2 I) {x z g v : G}
    (hxI : x ∈ Subgroup.normalizer (I : Set G)) (hzI : z ∈ Subgroup.normalizer (I : Set G))
    (hgI : g ∈ Subgroup.normalizer (I : Set G)) (hvI : v ∈ Subgroup.normalizer (I : Set G))
    (hx : x ^ p = 1) (hz : z ^ p = 1) (hxz : x * z = z * x)
    (hgx : g * x * g⁻¹ = x * z) (hgz : g * z = z * g)
    (hvx : v * x * v⁻¹ = x⁻¹) (hvz : v * z = z * v) (hv : v * v = 1)
    (hCz : I ⊓ Subgroup.centralizer ({z} : Set G) = ⊥)
    (hCx : I ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({v} : Set G)) :
    ∃ k : ℕ, Nat.card ↥I = 2 ^ (p * k) ∧
      Nat.card ↥(I ⊓ Subgroup.centralizer ({v} : Set G)) = 2 ^ ((p + 1) * k / 2) ∧
      Nat.card ↥⁅I, Subgroup.zpowers v⁆ = 2 ^ ((p - 1) * k / 2) := by
  letI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  letI : IsElementaryAbelian 2 ↥I := isElemAbelian_iff_isElementaryAbelian.mp hI
  set σ : Module.End (ZMod 2) (Additive ↥I) := conjEnd I ⟨x, hxI⟩ with hσdef
  set τ : Module.End (ZMod 2) (Additive ↥I) := conjEnd I ⟨z, hzI⟩ with hτdef
  set γ : Module.End (ZMod 2) (Additive ↥I) := conjEnd I ⟨g, hgI⟩ with hγdef
  set ν : Module.End (ZMod 2) (Additive ↥I) := conjEnd I ⟨v, hvI⟩ with hνdef
  have hxz' : (⟨x, hxI⟩ : ↥(Subgroup.normalizer (I : Set G))) * ⟨z, hzI⟩ =
      ⟨z, hzI⟩ * ⟨x, hxI⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hxz
  have hστ : Commute σ τ := by
    rw [Commute, hσdef, hτdef]
    calc conjEnd I ⟨x, hxI⟩ * conjEnd I ⟨z, hzI⟩
        = conjEnd I (⟨x, hxI⟩ * ⟨z, hzI⟩) := (map_mul _ _ _).symm
      _ = conjEnd I (⟨z, hzI⟩ * ⟨x, hxI⟩) := by rw [hxz']
      _ = conjEnd I ⟨z, hzI⟩ * conjEnd I ⟨x, hxI⟩ := map_mul _ _ _
  have hxp' : (⟨x, hxI⟩ : ↥(Subgroup.normalizer (I : Set G))) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hx]
    rfl
  have hzp' : (⟨z, hzI⟩ : ↥(Subgroup.normalizer (I : Set G))) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hz]
    rfl
  have hσ : σ ^ p = 1 := by rw [hσdef, ← map_pow, hxp', map_one]
  have hτ : τ ^ p = 1 := by rw [hτdef, ← map_pow, hzp', map_one]
  have hτfix : ∀ a : Additive ↥I, τ a = a → a = 0 := by
    intro a ha
    rw [hτdef] at ha
    have hmem : (a.toMul : G) ∈ I ⊓ Subgroup.centralizer ({z} : Set G) :=
      mem_inf_centralizer_of_conjEnd_eq I hzI ha
    have hbot : (a.toMul : G) ∈ (⊥ : Subgroup G) := by rwa [hCz] at hmem
    exact toMul_eq_one.mp (Subtype.ext (Subgroup.mem_bot.mp hbot))
  have hγ : Function.Injective γ := by
    have hgI' : g⁻¹ ∈ Subgroup.normalizer (I : Set G) :=
      (Subgroup.normalizer (I : Set G)).inv_mem hgI
    have hleft : Function.LeftInverse (conjEnd I ⟨g⁻¹, hgI'⟩) γ := by
      intro a
      rw [hγdef, ← Module.End.mul_apply, ← map_mul]
      have h1 : (⟨g⁻¹, hgI'⟩ : ↥(Subgroup.normalizer (I : Set G))) * ⟨g, hgI⟩ = 1 := by
        apply Subtype.ext
        simp
      rw [h1, map_one, Module.End.one_apply]
    exact hleft.injective
  have hgx' : (⟨g, hgI⟩ : ↥(Subgroup.normalizer (I : Set G))) * ⟨x, hxI⟩ =
      ⟨x, hxI⟩ * ⟨z, hzI⟩ * ⟨g, hgI⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hgx]
    group
  have hγσ : γ * σ = σ * τ * γ := by
    rw [hγdef, hσdef, hτdef]
    calc conjEnd I ⟨g, hgI⟩ * conjEnd I ⟨x, hxI⟩
        = conjEnd I (⟨g, hgI⟩ * ⟨x, hxI⟩) := (map_mul _ _ _).symm
      _ = conjEnd I (⟨x, hxI⟩ * ⟨z, hzI⟩ * ⟨g, hgI⟩) := by rw [hgx']
      _ = conjEnd I (⟨x, hxI⟩ * ⟨z, hzI⟩) * conjEnd I ⟨g, hgI⟩ := map_mul _ _ _
      _ = (conjEnd I ⟨x, hxI⟩ * conjEnd I ⟨z, hzI⟩) * conjEnd I ⟨g, hgI⟩ := by rw [map_mul]
  have hgz' : (⟨g, hgI⟩ : ↥(Subgroup.normalizer (I : Set G))) * ⟨z, hzI⟩ =
      ⟨z, hzI⟩ * ⟨g, hgI⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hgz
  have hγτ : γ * τ = τ * γ := by
    rw [hγdef, hτdef]
    calc conjEnd I ⟨g, hgI⟩ * conjEnd I ⟨z, hzI⟩
        = conjEnd I (⟨g, hgI⟩ * ⟨z, hzI⟩) := (map_mul _ _ _).symm
      _ = conjEnd I (⟨z, hzI⟩ * ⟨g, hgI⟩) := by rw [hgz']
      _ = conjEnd I ⟨z, hzI⟩ * conjEnd I ⟨g, hgI⟩ := map_mul _ _ _
  have hv' : (⟨v, hvI⟩ : ↥(Subgroup.normalizer (I : Set G))) * ⟨v, hvI⟩ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    exact hv
  have hν : ν * ν = 1 := by rw [hνdef, ← map_mul, hv', map_one]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hxinv : x ^ (p - 1) = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hp1, hx]
  have hvx' : (⟨v, hvI⟩ : ↥(Subgroup.normalizer (I : Set G))) * ⟨x, hxI⟩ =
      ⟨x, hxI⟩ ^ (p - 1) * ⟨v, hvI⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    rw [hxinv]
    rw [← hvx]
    group
  have hνσ : ν * σ = σ ^ (p - 1) * ν := by
    rw [hνdef, hσdef]
    calc conjEnd I ⟨v, hvI⟩ * conjEnd I ⟨x, hxI⟩
        = conjEnd I (⟨v, hvI⟩ * ⟨x, hxI⟩) := (map_mul _ _ _).symm
      _ = conjEnd I (⟨x, hxI⟩ ^ (p - 1) * ⟨v, hvI⟩) := by rw [hvx']
      _ = conjEnd I (⟨x, hxI⟩ ^ (p - 1)) * conjEnd I ⟨v, hvI⟩ := map_mul _ _ _
      _ = conjEnd I ⟨x, hxI⟩ ^ (p - 1) * conjEnd I ⟨v, hvI⟩ := by rw [map_pow]
  have hfix : ∀ a : Additive ↥I, σ a = a → ν a = a := by
    intro a ha
    rw [hσdef] at ha
    have hxa : (a.toMul : G) ∈ I ⊓ Subgroup.centralizer ({x} : Set G) :=
      mem_inf_centralizer_of_conjEnd_eq I hxI ha
    have hva : (a.toMul : G) ∈ Subgroup.centralizer ({v} : Set G) := hCx hxa
    rw [hνdef]
    apply (Additive.toMul (α := ↥I)).injective
    apply Subtype.ext
    rw [conjEnd_apply]
    rw [Subgroup.mem_centralizer_singleton_iff] at hva
    rw [← hva]
    group
  obtain ⟨k, hk1, hk2, hk3⟩ :=
    exists_finrank_eq_of_inverting_involution (M := Additive ↥I) hp hστ hσ hτ hτfix hγ hγσ hγτ
      hν hνσ hfix
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [Nat.card_congr Additive.ofMul,
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥I), Nat.card_zmod, hk1]
  · rw [Nat.card_congr (fixedSubgroupEquiv I hvI),
      Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := ↥(LinearMap.ker (conjEnd I ⟨v, hvI⟩ - 1))), Nat.card_zmod, ← hνdef, hk2]
  · let S : AddSubgroup (Additive ↥I) := (LinearMap.range (ν - 1)).toAddSubgroup
    let f : Additive ↥I →+ Additive G :=
      { toFun := fun a => Additive.ofMul (a.toMul : G)
        map_zero' := rfl
        map_add' := fun a b => by simp [toMul_add, ofMul_mul] }
    let R : Subgroup G := (S.map f).toSubgroup'
    have hf_inj : Function.Injective f := by
      intro a b hab
      apply (Additive.toMul (α := ↥I)).injective
      apply Subtype.ext
      exact Additive.ofMul.injective hab
    have mem_R : ∀ y : G, y ∈ R ↔ ∃ a ∈ LinearMap.range (ν - 1), (a.toMul : G) = y := by
      intro y
      constructor
      · intro hy
        have hy' : Additive.ofMul y ∈ S.map f :=
          (AddSubgroup.mem_toSubgroup' (S.map f) y).mp hy
        rcases AddSubgroup.mem_map.mp hy' with ⟨a, ha, haf⟩
        exact ⟨a, ha, Additive.ofMul.injective haf⟩
      · rintro ⟨a, ha, hay⟩
        refine (AddSubgroup.mem_toSubgroup' (S.map f) y).mpr ?_
        have hmem : f a ∈ S.map f := AddSubgroup.mem_map.mpr ⟨a, ha, rfl⟩
        have hfa : f a = Additive.ofMul y := by
          show Additive.ofMul (a.toMul : G) = Additive.ofMul y
          rw [hay]
        rwa [hfa] at hmem
    have hR_le : R ≤ ⁅I, Subgroup.zpowers v⁆ := by
      intro y hy
      rw [mem_R] at hy
      obtain ⟨a, ⟨b, hb⟩, hay⟩ := hy
      rw [← hay, ← hb, hνdef, conjEnd_sub_one_toMul I hvI b]
      exact (⁅I, Subgroup.zpowers v⁆).inv_mem
        (Subgroup.commutator_mem_commutator b.toMul.2 (Subgroup.mem_zpowers v))
    have hv2 : v ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hv]
    have hpar : ∀ m : ℤ, v ^ m = 1 ∨ v ^ m = v := by
      intro m
      rw [zpow_eq_zpow_emod m hv2]
      rcases Int.emod_two_eq_zero_or_one m with h | h
      · left; rw [h, zpow_zero]
      · right; rw [h, zpow_one]
    have hR_ge : ⁅I, Subgroup.zpowers v⁆ ≤ R := by
      refine Subgroup.commutator_le.mpr fun a ha k hk => ?_
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      rcases hpar m with hm | hm
      · rw [hm, commutatorElement_def]; simp
      · rw [hm]
        have hva : (((ν - 1) (Additive.ofMul ⟨a, ha⟩)).toMul : G) ∈ R := by
          rw [mem_R]
          exact ⟨_, ⟨_, rfl⟩, rfl⟩
        rw [hνdef, conjEnd_sub_one_toMul I hvI] at hva
        simpa using R.inv_mem hva
    have hR_eq : R = ⁅I, Subgroup.zpowers v⁆ := le_antisymm hR_le hR_ge
    have hcardR : Nat.card ↥R = 2 ^ Module.finrank (ZMod 2) (LinearMap.range (ν - 1)) := by
      have h1 : Nat.card ↥R = Nat.card ↥(S.map f) :=
        Nat.card_congr
          { toFun := fun y =>
              ⟨Additive.ofMul (y : G), (AddSubgroup.mem_toSubgroup' (S.map f) (y : G)).mp y.2⟩
            invFun := fun a =>
              ⟨Additive.toMul a.1,
                (AddSubgroup.mem_toSubgroup' (S.map f) (Additive.toMul a.1)).mpr a.2⟩
            left_inv := fun y => by apply Subtype.ext; rfl
            right_inv := fun a => by apply Subtype.ext; rfl }
      have h2 : Nat.card ↥(S.map f) = Nat.card ↥S :=
        Nat.card_congr (AddSubgroup.equivMapOfInjective S f hf_inj).toEquiv.symm
      have h3 : Nat.card ↥S = Nat.card ↥(LinearMap.range (ν - 1)) := rfl
      rw [h1, h2, h3,
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.range (ν - 1))),
        Nat.card_zmod]
    rw [← hR_eq, hcardR, hk3]

end CFSG.LocalAnalysis.WeakClosure81
