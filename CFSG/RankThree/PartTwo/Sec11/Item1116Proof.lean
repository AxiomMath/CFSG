module

public import CFSG.RankThree.PartTwo.Sec11.Item1116KFact
public import CFSG.RankThree.PartTwo.Sec11.Item1113
public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
public import CFSG.RankThree.PartTwo.Sec11.RFacts
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

namespace Item1116Proof

section Elementary

variable {G : Type*} [Group G]

theorem pow_three_modEq_one {n k m : ℕ} (hn : n ∣ 9) (hk : k ^ 3 ^ m ≡ 1 [MOD n]) :
    k ^ 3 ≡ 1 [MOD n] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (by simpa using hn : n ∣ 3 ^ 2)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp [Nat.ModEq, Nat.mod_one]
  have hk3 : k ^ 3 ^ m ≡ 1 [MOD 3] := hk.of_dvd (dvd_pow_self 3 hi0.ne')
  have hk1 : k % 3 = 1 := by
    have h1 : ((k ^ 3 ^ m : ℕ) : ZMod 3) = ((1 : ℕ) : ZMod 3) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hk3
    rw [Nat.cast_pow, ZMod.pow_card_pow] at h1
    simpa using (ZMod.natCast_eq_natCast_iff' k 1 3).mp h1
  have h9 : k ^ 3 ≡ 1 [MOD 9] := by
    have hk9 : k % 9 = 1 ∨ k % 9 = 4 ∨ k % 9 = 7 := by omega
    unfold Nat.ModEq
    rw [Nat.pow_mod]
    rcases hk9 with h | h | h <;> rw [h]
  exact h9.of_dvd hn

theorem conj_pow_three_eq_of_pow_nine {r x : G} (hr : ∃ m : ℕ, r ^ 3 ^ m = 1)
    (hrx : r * x * r⁻¹ ∈ Subgroup.zpowers x) (hx9 : x ^ 9 = 1) :
    r ^ 3 * x * (r ^ 3)⁻¹ = x := by
  obtain ⟨m, hm⟩ := hr
  obtain ⟨k, hk⟩ : ∃ k : ℕ, r * x * r⁻¹ = x ^ k := by
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hrx
    refine ⟨(z % 9).toNat, ?_⟩
    have e1 : (((z % 9).toNat : ℕ) : ℤ) = z % 9 :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
    rw [← hz, ← zpow_natCast, e1]
    exact zpow_eq_zpow_emod' z hx9
  have hconj : ∀ n : ℕ, r ^ n * x * (r ^ n)⁻¹ = x ^ (k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : r ^ (n + 1) * x * (r ^ (n + 1))⁻¹ = r * (r ^ n * x * (r ^ n)⁻¹) * r⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [e, ih, ← conj_pow, hk, ← pow_mul, pow_succ, mul_comm (k ^ n) k]
  have h1 : x ^ (k ^ 3 ^ m) = x ^ 1 := by
    rw [← hconj (3 ^ m), hm]
    simp
  have h3 := pow_three_modEq_one (orderOf_dvd_of_pow_eq_one hx9) (pow_eq_pow_iff_modEq.mp h1)
  rw [hconj 3, pow_eq_pow_iff_modEq.mpr h3, pow_one]

theorem exists_zpow_mul_zpow_of_mem_closure {r s a : G}
    (hrs : r ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G))
    (ha : a ∈ Subgroup.closure ({r, s} : Set G)) : ∃ i j : ℤ, a = r ^ i * s ^ j := by
  have hle : Subgroup.zpowers r ≤ Subgroup.normalizer (Subgroup.zpowers s : Set G) :=
    Subgroup.zpowers_le.mpr hrs
  have hcl : Subgroup.closure ({r, s} : Set G) = Subgroup.zpowers r ⊔ Subgroup.zpowers s := by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure]
  have ha' : a ∈ ((Subgroup.zpowers r ⊔ Subgroup.zpowers s : Subgroup G) : Set G) := by
    rw [← hcl]
    exact ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at ha'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp ha'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  exact ⟨i, j, rfl⟩

theorem mem_zpowers_zpow_of_not_dvd {r : G} (hr : ∃ k : ℕ, r ^ 3 ^ k = 1) {i : ℤ}
    (hi : ¬ (3 : ℤ) ∣ i) : r ∈ Subgroup.zpowers (r ^ i) := by
  obtain ⟨k, hk⟩ := hr
  have hcop : IsCoprime i ((3 : ℤ) ^ k) :=
    ((Prime.coprime_iff_not_dvd Int.prime_three).mpr hi).symm.pow_right
  obtain ⟨u, v, huv⟩ := hcop
  have hk' : r ^ ((3 : ℤ) ^ k) = 1 := by
    rw [show ((3 : ℤ) ^ k) = ((3 ^ k : ℕ) : ℤ) by push_cast; rfl, zpow_natCast, hk]
  refine Subgroup.mem_zpowers_iff.mpr ⟨u, ?_⟩
  calc (r ^ i) ^ u = (r ^ i) ^ u * (r ^ ((3 : ℤ) ^ k)) ^ v := by rw [hk', one_zpow, mul_one]
    _ = r ^ (u * i + v * 3 ^ k) := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm i u, mul_comm ((3 : ℤ) ^ k) v]
    _ = r := by rw [huv, zpow_one]

theorem commutator_sup_le_of_comm {Y A : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) :
    ⁅Y ⊔ A, Y ⊔ A⁆ ≤ Y := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left Y A hAY
  rw [Subgroup.commutator_le]
  intro u hu v hv
  have hu' : u ∈ ((Y ⊔ A : Subgroup G) : Set G) := hu
  have hv' : v ∈ ((Y ⊔ A : Subgroup G) : Set G) := hv
  rw [hset] at hu' hv'
  obtain ⟨y₁, hy₁, a₁, ha₁, rfl⟩ := Set.mem_mul.mp hu'
  obtain ⟨y₂, hy₂, a₂, ha₂, rfl⟩ := Set.mem_mul.mp hv'
  have hc : a₂ * a₁⁻¹ = a₁⁻¹ * a₂ := by
    have h12 := hA a₁ ha₁ a₂ ha₂
    calc a₂ * a₁⁻¹ = a₁⁻¹ * (a₁ * a₂) * a₁⁻¹ := by group
      _ = a₁⁻¹ * (a₂ * a₁) * a₁⁻¹ := by rw [h12]
      _ = a₁⁻¹ * a₂ := by group
  have e : ⁅y₁ * a₁, y₂ * a₂⁆ = y₁ * (a₁ * y₂ * a₁⁻¹) * (a₂ * y₁⁻¹ * a₂⁻¹) * y₂⁻¹ := by
    calc ⁅y₁ * a₁, y₂ * a₂⁆ = y₁ * a₁ * y₂ * (a₂ * a₁⁻¹) * y₁⁻¹ * a₂⁻¹ * y₂⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = y₁ * a₁ * y₂ * (a₁⁻¹ * a₂) * y₁⁻¹ * a₂⁻¹ * y₂⁻¹ := by rw [hc]
      _ = y₁ * (a₁ * y₂ * a₁⁻¹) * (a₂ * y₁⁻¹ * a₂⁻¹) * y₂⁻¹ := by group
  rw [e]
  refine Y.mul_mem (Y.mul_mem (Y.mul_mem hy₁ ?_) ?_) (Y.inv_mem hy₂)
  · exact (Subgroup.mem_normalizer_iff.mp (hAY ha₁) y₂).mp hy₂
  · exact (Subgroup.mem_normalizer_iff.mp (hAY ha₂) y₁⁻¹).mp (Y.inv_mem hy₁)

theorem nonempty_commutator_prod_equiv (X : Type*) [Group X] :
    Nonempty (_root_.commutator (Multiplicative (ZMod 3) × X) ≃* _root_.commutator X) := by
  set P := Multiplicative (ZMod 3) × X with hP
  have : IsMulCommutative (Multiplicative (ZMod 3)) := ⟨⟨mul_comm⟩⟩
  have hPc : _root_.commutator P =
      (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (_root_.commutator X) := by
    rw [commutator_def, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod, ← commutator_def,
      ← commutator_def, commutator_eq_bot]
  have hmem : ∀ w : P, w ∈ _root_.commutator P ↔ w.1 = 1 ∧ w.2 ∈ _root_.commutator X := by
    intro w
    rw [hPc, Subgroup.mem_prod, Subgroup.mem_bot]
  exact ⟨{ toFun := fun w => ⟨(w : P).2, ((hmem w).mp w.2).2⟩
           invFun := fun z => ⟨((1 : Multiplicative (ZMod 3)), (z : X)),
             (hmem _).mpr ⟨rfl, z.2⟩⟩
           left_inv := fun w => Subtype.ext (Prod.ext ((hmem w).mp w.2).1.symm rfl)
           right_inv := fun z => rfl
           map_mul' := fun w w' => rfl }⟩

theorem mem_normalizer_inf {R S : Subgroup G} {y : G}
    (hyR : y ∈ Subgroup.normalizer (R : Set G)) (hyS : y ∈ Subgroup.normalizer (S : Set G)) :
    y ∈ Subgroup.normalizer ((R ⊓ S : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨hz1, hz2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hyR z).mp hz1,
      (Subgroup.mem_normalizer_iff.mp hyS z).mp hz2⟩
  · rintro ⟨hz1, hz2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hyR z).mpr hz1,
      (Subgroup.mem_normalizer_iff.mp hyS z).mpr hz2⟩

end Elementary

section Quotients

variable {G : Type} [Group G] [Finite G]

theorem nonempty_thetaQuot_equiv_commutator {a : G} {Y A : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) (hAC : A ≤ Subgroup.centralizer ({a} : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    {X : Type} [Group X] (e : sec11YA a Y A ≃* Multiplicative (ZMod 3) × X) :
    Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X) := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set π : C →* C ⧸ aschbacherSolvableCore 3 C := QuotientGroup.mk' _ with hπ
  have hYC : Y ≤ C := Sec6.le_centralizer_of_mem_thetaComponentsAt hY
  set Y' := Y.subgroupOf C with hY'
  set A' := A.subgroupOf C with hA'
  have hM : sec11YA a Y A = (Y' ⊔ A').map π := by
    rw [sec11YA, Subgroup.subgroupOf_sup hYC hAC]
  have hA'Y' : A' ≤ Subgroup.normalizer (Y' : Set C) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact Subgroup.mem_normalizer_iff.mp (hAY (Subgroup.mem_subgroupOf.mp hu)) (z : G)
  have hA'c : ∀ u ∈ A', ∀ v ∈ A', u * v = v * u := fun u hu v hv =>
    Subtype.ext (hA _ (Subgroup.mem_subgroupOf.mp hu) _ (Subgroup.mem_subgroupOf.mp hv))
  have hYp : Group.IsPerfect Y := Sec6.isPerfect_of_mem_thetaComponentsAt hY
  have hY'p : Group.IsPerfect Y' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hYC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYC).symm.surjective
  have hYM : Y'.map π ≤ sec11YA a Y A := by
    rw [hM]
    exact Subgroup.map_mono le_sup_left
  have hcomm : ⁅sec11YA a Y A, sec11YA a Y A⁆ = Y'.map π := by
    apply le_antisymm
    · rw [hM, ← Subgroup.map_commutator]
      exact Subgroup.map_mono (commutator_sup_le_of_comm hA'Y' hA'c)
    · have : Group.IsPerfect (Y'.map π) := Group.IsPerfect.map π
      calc Y'.map π = ⁅Y'.map π, Y'.map π⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ ⁅sec11YA a Y A, sec11YA a Y A⁆ := Subgroup.commutator_mono hYM hYM
  set f : Y →* C ⧸ aschbacherSolvableCore 3 C := π.comp (Subgroup.inclusion hYC) with hf
  have hfrange : f.range = Y'.map π := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hθ := Sec6.theta_eq_inf_of_mem_thetaComponentsAt hY
  have hfker : f.ker = aschbacherSolvableCore 3 Y := by
    ext y
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hy
      have h1 : (y : G) ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
        rw [hθ]
        exact ⟨y.2, ⟨_, hy, rfl⟩⟩
      obtain ⟨y', hy', hyy'⟩ := h1
      rwa [Subtype.ext hyy'] at hy'
    · intro hy
      have h1 : (y : G) ∈ inSubgroup (aschbacherSolvableCore 3) Y := ⟨y, hy, rfl⟩
      rw [hθ] at h1
      obtain ⟨-, ⟨w, hw, hwy⟩⟩ := h1
      rwa [show w = Subgroup.inclusion hYC y from Subtype.ext hwy] at hw
  have e1 : Y ⧸ aschbacherSolvableCore 3 Y ≃* Y'.map π :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hfrange))
  have e2 : _root_.commutator (sec11YA a Y A) ≃* Y'.map π :=
    ((_root_.commutator (sec11YA a Y A)).equivMapOfInjective (sec11YA a Y A).subtype
      (sec11YA a Y A).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [Subgroup.map_subtype_commutator, hcomm]))
  have hec : (_root_.commutator (sec11YA a Y A)).map e.toMonoidHom =
      _root_.commutator (Multiplicative (ZMod 3) × X) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ e.surjective, commutator_def]
  have e3 : _root_.commutator (sec11YA a Y A) ≃*
      _root_.commutator (Multiplicative (ZMod 3) × X) :=
    ((_root_.commutator (sec11YA a Y A)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hec)
  obtain ⟨e4⟩ := nonempty_commutator_prod_equiv X
  exact ⟨e1.trans (e2.symm.trans (e3.trans e4))⟩

theorem commutator_mem_theta_sec11K {L : Subgroup G} {a t : G}
    (htN : t ∈ Subgroup.normalizer (L : Set G)) (hta : t * a = a * t)
    (htC : t ∈ Sec4.thetaQuotCentralizer L) :
    ∀ k ∈ sec11K L a, t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) (sec11K L a) := by
  intro k hk
  have hkL := sec11K_le L a hk
  have htKN : t ∈ Subgroup.normalizer (sec11K L a : Set G) :=
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (mem_normalizer_inf htN
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hta)))
  have h1 : t * k * t⁻¹ * k⁻¹ ∈ sec11K L a :=
    (sec11K L a).mul_mem ((Subgroup.mem_normalizer_iff.mp htKN k).mp hk)
      ((sec11K L a).inv_mem hk)
  have h2 : t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have h3 := (Sec6.mem_thetaQuotCentralizer_iff.mp htC).2 k hkL
    have e : t * k * t⁻¹ * k⁻¹ = k * (k⁻¹ * (t * k * t⁻¹)) * k⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L hkL) _).mp h3
  exact Sec13.inf_inSubgroup_theta_le (sec11K_le L a) ⟨h1, h2⟩

end Quotients

end Item1116Proof

section Main

namespace Item1116Proof

variable {G : Type} [Group G] [Finite G]

theorem not_le_centralizer_of_isSylowOf {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {T : Subgroup G} (hT : IsSylowOf 3 T L) :
    ¬ T ≤ Subgroup.centralizer ({a} : Set G) := by
  intro hTa
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haN := h.toHyp81.a_mem_normalizer
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  set τ := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩) with hτ
  have hτ3 : τ ^ 3 = 1 := by
    have h1 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [hτ, ← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨Q, hQ⟩ := hT
  obtain ⟨y, hy, hne⟩ := exists_ne_of_sylow_of_isList1016 h.isList1016 hτ3
    h.toHyp81.not_isInnerAut_induced (Q.mapSurjective (QuotientGroup.mk'_surjective _))
  apply hne
  rw [Sylow.coe_mapSurjective] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  have hqT : (q : G) ∈ T := by
    rw [← hQ]
    exact ⟨q, hq, rfl⟩
  have hqa : a * (q : G) * a⁻¹ = q := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hTa hqT), mul_inv_cancel_right]
  rw [QuotientGroup.mk'_apply, hτ, Sec4.thetaQuotMulAut_mk]
  congr 1
  exact Subtype.ext hqa

theorem le_centralizer_and_normalizer (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) :
    R ≤ Subgroup.centralizer ({c} : Set G) ∧ R ≤ Subgroup.normalizer (L : Set G) := by
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hRc := le_centralizer_of_le_normalizer_zpowers (orderOf_eq_prime hc3 h.ne_one)
    h.isSylowOf.isPGroup h.isSylowOf.le
  exact ⟨hRc, le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hc3 h.ne_one
    h.isSylowOf.isPGroup hRc L h.mem_thetaComponentsAt⟩

theorem mem_R {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}
    {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g) : r ∈ R ∧ x ∈ R ∧ s ∈ R := by
  have hmem : ∀ y ∈ ({r, x, s} : Set G), y ∈ R := fun y hy => by
    rw [h.R_eq]
    exact Subgroup.subset_closure hy
  exact ⟨hmem r (by simp), hmem x (by simp), hmem s (by simp)⟩

theorem exists_pow_eq_one_of_mem {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g) {y : G}
    (hy : y ∈ R) : ∃ k : ℕ, y ^ 3 ^ k = 1 := by
  obtain ⟨k, hk⟩ := h.isSylowOf.isPGroup ⟨y, hy⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem ordProj_card_sec11K_lt {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g) :
    3 ^ (Nat.card (sec11K L a)).factorization 3 < orderOf x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKL : sec11K L a ≤ L := sec11K_le L a
  have hKa : sec11K L a ≤ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (sec11K L a)
  have hx : orderOf x = 3 ^ (Nat.card L).factorization 3 := by
    rw [← Nat.card_zpowers, ← h.inf_L_eq]
    exact h.toSec11Std.isSylowOf_inf_L.card_eq
  have hdvd : 3 ^ (Nat.card (sec11K L a)).factorization 3 ∣ 3 ^ (Nat.card L).factorization 3 :=
    Nat.ordProj_dvd_ordProj_of_dvd Nat.card_pos.ne' (Subgroup.card_dvd_of_le hKL) 3
  have hne : 3 ^ (Nat.card (sec11K L a)).factorization 3 ≠ 3 ^ (Nat.card L).factorization 3 := by
    intro heq
    have hTL : IsSylowOf 3 T L :=
      CFSG.ABGLocalTools.isSylowOf_of_card (hT.le.trans hKL) (hT.card_eq.trans heq)
    exact not_le_centralizer_of_isSylowOf h.toSec11Std hTL (hT.le.trans hKa)
  rw [hx]
  exact lt_of_le_of_ne (Nat.le_of_dvd (by positivity) hdvd) hne

theorem nine_le_orderOf_s {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}
    {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s ≠ Subgroup.zpowers c) : 9 ≤ orderOf s := by
  have hcs := h.c_mem_zpowers_s
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.mem_partTwoF.1.2 c h.mem_A) h.ne_one
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem h (mem_R h).2.2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have h3 : 3 ∣ orderOf s := hc3 ▸ orderOf_dvd_of_mem_zpowers hcs
  have hj2 : 2 ≤ j := by
    by_contra hj2
    interval_cases j
    · rw [hj, pow_zero] at h3
      norm_num at h3
    · apply hsc
      exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcs)
        (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hj, hc3, pow_one]))).symm
  rw [hj]
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2

theorem eq_one_of_mem_zpowers_s_of_not_mem {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hcY : c ∉ Sec4.thetaQuotCentralizer Y) {u : G} (hus : u ∈ Subgroup.zpowers s)
    (huY : u ∈ Sec4.thetaQuotCentralizer Y) : u = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcs := h.c_mem_zpowers_s
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.mem_partTwoF.1.2 c h.mem_A) h.ne_one
  have hsR : s ∈ R := (mem_R h).2.2
  set S := Subgroup.zpowers s with hS
  set Z := (S ⊓ Sec4.thetaQuotCentralizer Y).subgroupOf S with hZ
  set C' := (Subgroup.zpowers c).subgroupOf S with hC'
  have hS3 : IsPGroup 3 S := h.isSylowOf.isPGroup.to_le (Subgroup.zpowers_le.mpr hsR)
  by_contra hu1
  have hZ3 : IsPGroup 3 Z := hS3.to_subgroup _
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have : (⟨u, hus⟩ : S) ∈ Z := Subgroup.mem_subgroupOf.mpr ⟨hus, huY⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hu1 (congrArg Subtype.val this)
  have h3 : 3 ∣ Nat.card Z := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ3
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hZne
      rw [pow_zero] at hn
      exact Subgroup.eq_bot_of_card_eq Z hn
    rw [hn]
    exact dvd_pow_self 3 hn0
  have hC'3 : Nat.card C' = 3 := by
    rw [hC', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hcs)).toEquiv,
      Nat.card_zpowers, hc3]
  have hle : C' ≤ Z := (IsCyclic.subgroup_le_iff_card_dvd).mpr (hC'3 ▸ h3)
  have hcZ : (⟨c, hcs⟩ : S) ∈ Z := hle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers c))
  exact hcY (Subgroup.mem_subgroupOf.mp hcZ).2

theorem c_not_mem_thetaQuotCentralizer (h118 : Item118) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) : c ∉ Sec4.thetaQuotCentralizer Y := by
  intro hc
  obtain ⟨-, -, hCA⟩ := h118 G A c L a R Y h.toSec11Std d g h.inf_eq h.closure_eq h.g_mem.2
    h.g_not_mem h.conj_mem
  have h1 := mem_sectionCentralizer_of_mem_thetaQuotCentralizer h.mem_A hc
  rw [hCA] at h1
  exact (h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq).1 h1

theorem exists_isList119_of_not_field (h45 : Sec4.Item4_5) (h119 : Item119) {A : Subgroup G}
    {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) (hnf : ¬ KFacts.InducesStdKind Y c .field) :
    ∃ (X : Type) (_ : Group X), IsList119 X ∧
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X) := by
  have hAe := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy a h.a_mem)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.a_mem h.a_ne_one Y
      h.mem_thetaComponentsAt_Y
  have key : ∀ (X : Type) [Group X], IsList119 X →
      Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) × X) →
      ∃ (X : Type) (_ : Group X), IsList119 X ∧
        Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X) :=
    fun X _ hX ⟨e⟩ => ⟨X, inferInstance, hX,
      nonempty_thetaQuot_equiv_commutator h.mem_thetaComponentsAt_Y hAC hAY hAc e⟩
  rcases h119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq with
    ⟨hf, -⟩ | ⟨⟨q, hq, he⟩ | ⟨q, hq, he⟩, -⟩ | ⟨hL | hP, -⟩ | ⟨hM | hH, -, -⟩
  · exact absurd hf hnf
  · exact key _ (Or.inl ⟨q, hq, ⟨MulEquiv.refl _⟩⟩) he
  · exact key _ (Or.inr (Or.inl ⟨q, hq, ⟨MulEquiv.refl _⟩⟩)) he
  · obtain ⟨p, e, hp, he1, ⟨hpe, he⟩ | ⟨hpe, he⟩⟩ := hL
    · exact key _ (Or.inr (Or.inr (Or.inl ⟨p, e, hp, he1, Or.inl ⟨hpe, ⟨MulEquiv.refl _⟩⟩⟩))) he
    · exact key _ (Or.inr (Or.inr (Or.inl ⟨p, e, hp, he1, Or.inr ⟨hpe, ⟨MulEquiv.refl _⟩⟩⟩))) he
  · obtain ⟨π, p, f, K, hK, hPF, hmod, he⟩ := hP
    exact key _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨π, p, f, K, hK, hPF, hmod,
      ⟨MulEquiv.refl _⟩⟩)))) he
  · have hX : IsList119 CFSG.Blueprint.NativeSporadic.M24 :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨MulEquiv.refl _⟩))))
    exact key _ hX hM
  · have hX : IsList119 CFSG.Blueprint.NativeSporadic.He :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨MulEquiv.refl _⟩))))
    exact key _ hX hH

end Item1116Proof

theorem item1116_of_ne_closure (h45 : Sec4.Item4_5) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
      (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
        Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s} → 9 < orderOf x := by
  intro G _ _ A c L a R Y d x s r g h hrs
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hRL⟩ := Item1116Proof.le_centralizer_and_normalizer h45 h
  obtain ⟨hrR, hxR, -⟩ := Item1116Proof.mem_R h
  have hRs : ∀ y ∈ R, y ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) := by
    intro y hy
    rw [← h.inf_centralizer_eq]
    exact Item1116Proof.mem_normalizer_inf (Subgroup.le_normalizer hy)
      (Sec6.normalizer_le_normalizer_thetaQuotCentralizer L (hRL hy))
  have hRx : ∀ y ∈ R, y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro y hy
    rw [← h.inf_L_eq]
    exact Item1116Proof.mem_normalizer_inf (Subgroup.le_normalizer hy) (hRL hy)
  obtain ⟨i, j, hij⟩ := Item1116Proof.exists_zpow_mul_zpow_of_mem_closure (hRs r hrR)
    h.a_mem_closure
  have h3i : (3 : ℤ) ∣ i := by
    by_contra h3
    apply hrs
    have hri : r ^ i ∈ Subgroup.closure ({a, s} : Set G) := by
      have e : r ^ i = a * (s ^ j)⁻¹ := by
        rw [hij]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) j))
    have hr : r ∈ Subgroup.closure ({a, s} : Set G) :=
      Subgroup.zpowers_le.mpr hri (Item1116Proof.mem_zpowers_zpow_of_not_dvd
        (Item1116Proof.exists_pow_eq_one_of_mem h hrR) h3)
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact hr
      · exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact h.a_mem_closure
      · exact Subgroup.subset_closure (by simp)
  obtain ⟨i', rfl⟩ := h3i
  by_contra hx'
  have hx : orderOf x ≤ 9 := not_lt.mp hx'
  have hx9 : x ^ 9 = 1 := by
    obtain ⟨k, hk⟩ := Item1116Proof.exists_pow_eq_one_of_mem h hxR
    obtain ⟨j', -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
    have hj2 : j' ≤ 2 := by
      by_contra hj
      have h27 : 3 ^ 3 ≤ orderOf x := by
        rw [hj']
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h27
      omega
    have hdvd : orderOf x ∣ 9 := by
      rw [hj', show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact Nat.pow_dvd_pow 3 hj2
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hr3 := Item1116Proof.conj_pow_three_eq_of_pow_nine
    (Item1116Proof.exists_pow_eq_one_of_mem h hrR)
    ((Subgroup.mem_normalizer_iff.mp (hRx r hrR) x).mp (Subgroup.mem_zpowers x)) hx9
  have hr3C : r ^ (3 : ℤ) ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [zpow_ofNat, Subgroup.mem_centralizer_singleton_iff]
    calc r ^ 3 * x = (r ^ 3 * x * (r ^ 3)⁻¹) * r ^ 3 := by group
      _ = x * r ^ 3 := by rw [hr3]
  have hsC : s ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h.commute_s_x
  have haC : a ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [hij, zpow_mul]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hr3C i') (Subgroup.zpow_mem _ hsC j)
  apply Item1116Proof.not_le_centralizer_of_isSylowOf h.toSec11Std h.toSec11Std.isSylowOf_inf_L
  rw [h.inf_L_eq, Subgroup.zpowers_le]
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp haC).symm

end Main

end CFSG.RankThree.PartTwo.Sec11
