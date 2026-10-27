module

public import CFSG.Quasithin.H13.KGFact68Base
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L2pB
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L33

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.GorensteinWalter
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Small

variable {Y : Type} [Group Y] [Finite Y]

theorem not_e68Hyp_of_smallList {L A R : Subgroup Y} {z : Y} (h : E6.E68Hyp L A R z)
    (hS : SmallListFacts ↥L) (hF : FixPointwiseInner ↥L) : False := by
  set P := ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L) with hPdef
  have hPsyl : IsSylowTwoOf P ⊤ := isSylowTwoOf_top_of_sylow (sylowIn h)
  have hshape := hS.sylow_shape P hPsyl
  have hP2 : IsPGroup 2 P := (sylowIn h).isPGroup'
  have hcZ : Nat.card (Subgroup.center ↥P) = 2 := card_center_of_shape P hP2 hshape
  have hP8 : 8 ≤ Nat.card ↥P := by
    rcases hshape with ⟨n, hn, ⟨e⟩⟩ | he
    · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      omega
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, CFSG.Semidihedral.card 4 (by norm_num)]
      norm_num
  have hZ : Subgroup.center ↥L = ⊥ := by
    have := hS.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h1 | h1
    · exact h1
    · exfalso
      have h2 : Subgroup.center ↥P = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_center_iff]
        intro y
        have h3 : (x : ↥L) ∈ Subgroup.center ↥L := by rw [h1]; trivial
        exact Subtype.ext (Subgroup.mem_center_iff.mp h3 (y : ↥L))
      rw [h2, Subgroup.card_top] at hcZ
      omega
  refine not_e68Hyp_of_inner h hZ (fun a ha => ?_) ?_
  · obtain ⟨g, hg⟩ := hF P hPsyl (conjOn L a (leN h ha)) fun y hy => conjOn_fix_of_hyp h ha hy
    exact ⟨g, hg.symm⟩
  · exact (card_omegaZ_le_card_center P).trans hcZ.le

end Small

section PSL2

variable {K : Type} [Field K] [Finite K]

omit [Field K] [Finite K] in
theorem isOddPrimePower_of_prime_card {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = p) :
    IsOddPrimePower (Nat.card K) :=
  ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩

theorem psl2_aut_fix_four_prime {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = p) {V : Subgroup PSL(2, K)}
    (hV : IsKleinFour V) {α : MulAut PSL(2, K)} (hα : ∀ v ∈ V, α v = v) :
    ∃ g0 ∈ V, α = MulAut.conj g0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hK' := isOddPrimePower_of_prime_card hp hp5 hK
  have hKpow : Nat.card K = p ^ 1 := by rw [hK, pow_one]
  have hcard : 3 < Nat.card K := by rw [hK]; omega
  have hex : ∃ (g : PGL2 K) (σ : K ≃+* K),
      α = pgl2InnerAutPSL2 K hK' hcard g * psl2FieldAut K σ := by
    obtain ⟨xx, hxx⟩ := pGammaL2ToMulAutPSL2_surjective K hKpow hK' hcard α
    have h := congrArg (pGammaL2ToMulAutPSL2 K hK' hcard)
      (SemidirectProduct.inl_left_mul_inr_right xx)
    rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr, hxx] at h
    exact ⟨xx.left, xx.right, h.symm⟩
  obtain ⟨g, σ, hαgσ⟩ := hex
  have hσ : σ = 1 := (CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime K hK).elim _ _
  rw [hσ, map_one, mul_one] at hαgσ
  let toPGL : PSL(2, K) →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP : IsKleinFour (V.map toPGL) := isKleinFour_map_of_injective _ hV toPGL htoPGL
  have hgC : g ∈ Subgroup.centralizer ((V.map toPGL : Subgroup (PGL2 K)) : Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 : pgl2InnerAutPSL2 K hK' hcard g v = v := by
      rw [← hαgσ]
      exact hα v hv
    have h2 := toPGL_pgl2InnerAutPSL2_apply K hK' hcard g v
    rw [h1] at h2
    calc toPGL v * g = (g * toPGL v * g⁻¹) * g := by rw [← h2]
      _ = g * toPGL v := by group
  rw [pgl2_kleinFour_centralizer_eq_self K hK' _ hVP] at hgC
  obtain ⟨g0, hg0V, hg0⟩ := hgC
  refine ⟨g0, hg0V, ?_⟩
  rw [hαgσ, ← hg0]
  exact pgl2InnerAutPSL2_toPGL K hK' hcard g0

theorem card_psl2_five (hK : Nat.card K = 5) : Nat.card PSL(2, K) = 60 := by
  rw [psl2_card_formula K (isOddPrimePower_of_prime_card Nat.prime_five le_rfl hK), hK]
  norm_num

theorem isKleinFour_sylow_psl2_five (hK : Nat.card K = 5) (S : Sylow 2 PSL(2, K)) :
    IsKleinFour ↥(S : Subgroup PSL(2, K)) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K
    (isOddPrimePower_of_prime_card Nat.prime_five le_rfl hK) S
  have hcard : Nat.card ↥(S : Subgroup PSL(2, K)) = 2 * 2 ^ m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hdvd : Nat.card ↥(S : Subgroup PSL(2, K)) ∣ 60 := by
    rw [← card_psl2_five hK]
    exact Subgroup.card_subgroup_dvd_card _
  have hm1 : m = 1 := by
    by_contra hne
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    rw [hcard] at hdvd
    have h8 : 8 ∣ 2 * 2 ^ (k + 2) := ⟨2 ^ k, by ring⟩
    have := h8.trans hdvd
    omega
  subst hm1
  refine ⟨by rw [hcard]; norm_num, ?_⟩
  rw [Monoid.exponent_eq_of_mulEquiv e, DihedralGroup.exponent]
  norm_num

end PSL2

section Burnside

variable {X : Type} [Group X] [Finite X]

theorem not_normalizer_le_centralizer (hperf : commutator X = ⊤) {p : ℕ} [Fact p.Prime]
    (P : Sylow p X) (hP1 : (P : Subgroup X) ≠ ⊥) :
    ¬ Subgroup.normalizer ((P : Subgroup X) : Set X) ≤
      Subgroup.centralizer ((P : Subgroup X) : Set X) := by
  intro hP
  have hcomm : ∀ a b : ↥(P : Subgroup X), a * b = b * a := fun a b =>
    Subtype.ext (hP (Subgroup.le_normalizer b.2) a a.2)
  set f := MonoidHom.transferSylow P hP with hf
  have hf1 : ∀ x : X, f x = 1 := by
    have hker : commutator X ≤ f.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    intro x
    rw [← MonoidHom.mem_ker]
    exact hker (hperf ▸ Subgroup.mem_top x)
  apply hP1
  rw [eq_bot_iff]
  intro g hg
  have h1 := MonoidHom.transferSylow_eq_pow P hP g hg
  rw [hf1] at h1
  have h2 : g ^ (P : Subgroup X).index = 1 := (congrArg Subtype.val h1).symm
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
  have hk' : g ^ p ^ k = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime (p ^ k) (P : Subgroup X).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr P.not_dvd_index)
  have h3 : orderOf g ∣ Nat.gcd (p ^ k) (P : Subgroup X).index :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact Subgroup.mem_bot.mpr h3

theorem pow_mem_centralizer_iff_of_four {V : Subgroup X} (hV : IsKleinFour ↥V) {x : X}
    (hxN : x ∈ Subgroup.normalizer (V : Set X)) (hxC : x ∉ Subgroup.centralizer (V : Set X))
    (hodd : Odd (orderOf x)) (j : ℕ) :
    x ^ j ∈ Subgroup.centralizer (V : Set X) ↔ 3 ∣ j := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have hNV : ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun v hv => (Subgroup.mem_normalizer_iff.mp hxN v).mp hv
  have hNV' : ∀ v ∈ V, x⁻¹ * v * x ∈ V := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) v).mp hv
    simpa using this
  let T := {v : X // v ∈ V ∧ v ≠ 1}
  let σ : Equiv.Perm T :=
    { toFun := fun t => ⟨x * t.1 * x⁻¹, hNV _ t.2.1, fun h => t.2.2 (by
        have : t.1 = x⁻¹ * (x * t.1 * x⁻¹) * x := by group
        rw [this, h]
        group)⟩
      invFun := fun t => ⟨x⁻¹ * t.1 * x, hNV' _ t.2.1, fun h => t.2.2 (by
        have : t.1 = x * (x⁻¹ * t.1 * x) * x⁻¹ := by group
        rw [this, h]
        group)⟩
      left_inv := fun t => Subtype.ext (by group)
      right_inv := fun t => Subtype.ext (by group) }
  have hσpow : ∀ n : ℕ, ∀ t : T, ((σ ^ n) t : X) = x ^ n * t.1 * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      rw [pow_succ', Equiv.Perm.mul_apply]
      show x * (((σ ^ n) t : T) : X) * x⁻¹ = _
      rw [ih t]
      group
  have hT : Fintype.card T = 3 := by
    have h1 : Nat.card T = Nat.card ↥V - 1 := by
      have e : T ≃ {v : ↥V // v ≠ 1} :=
        { toFun := fun t => ⟨⟨t.1, t.2.1⟩, fun h => t.2.2 (congrArg Subtype.val h)⟩
          invFun := fun v => ⟨v.1, v.1.2, fun h => v.2 (Subtype.ext h)⟩
          left_inv := fun t => rfl
          right_inv := fun v => rfl }
      rw [Nat.card_congr e, Nat.card_eq_fintype_card (α := {v : ↥V // v ≠ 1}),
        Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card]
    rw [← Nat.card_eq_fintype_card, h1, hV.card_four]
  have hσo : orderOf σ ∣ orderOf x := by
    apply orderOf_dvd_of_pow_eq_one
    ext t
    rw [hσpow, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
    rfl
  have hσ6 : orderOf σ ∣ 6 := by
    have := orderOf_dvd_card (G := Equiv.Perm T) (x := σ)
    rwa [Fintype.card_perm, hT] at this
  have hσ3 : σ ^ 3 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    have hod : Odd (orderOf σ) := hodd.of_dvd_nat hσo
    have h6 : orderOf σ ∣ 3 * 2 := hσ6
    exact (Nat.coprime_two_right.mpr hod).dvd_of_dvd_mul_right h6
  have hfixT : ∀ n : ℕ, σ ^ n = 1 → x ^ n ∈ Subgroup.centralizer (V : Set X) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1, one_mul, mul_one]
    · have h1 := hσpow n ⟨v, hv, hv1⟩
      rw [hn] at h1
      have h2 : v = x ^ n * v * (x ^ n)⁻¹ := h1
      calc v * x ^ n = (x ^ n * v * (x ^ n)⁻¹) * x ^ n := by rw [← h2]
        _ = x ^ n * v := by group
  have hx3 := hfixT 3 hσ3
  constructor
  · intro hj
    by_contra h3
    have hcop : Nat.Coprime j 3 := (Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
    have hbez : (1 : ℤ) = (j : ℤ) * Nat.gcdA j 3 + ((3 : ℕ) : ℤ) * Nat.gcdB j 3 := by
      have := Nat.gcd_eq_gcd_ab j 3
      rw [hcop] at this
      exact_mod_cast this
    apply hxC
    have : x = (x ^ j) ^ Nat.gcdA j 3 * (x ^ 3) ^ Nat.gcdB j 3 := by
      rw [← zpow_natCast x j, ← zpow_natCast x 3, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez,
        zpow_one]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hj _) (Subgroup.zpow_mem _ hx3 _)
  · rintro ⟨k, rfl⟩
    rw [pow_mul]
    exact Subgroup.pow_mem _ hx3 k

end Burnside

section Five

variable {Y : Type} [Group Y] [Finite Y]

theorem e68Concl_of_psl2_five
    {L A R : Subgroup Y} {z : Y} (hmodel : Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 2 5 1)
    (h : E6.E68Hyp L A R z) : E6.E68Concl L A R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, e, hcard, -, -⟩ :=
    CFSG.QuasithinUnique.K1.psl2_model_data (by norm_num) hmodel
  have hK : Nat.card K = 5 := by rw [Nat.card_eq_fintype_card, hcard, pow_one]
  set P := ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L) with hPdef
  set S : Sylow 2 PSL(2, K) := (sylowIn h).mapSurjective (f := e.toMonoidHom) e.surjective with hS
  have hScoe : (S : Subgroup PSL(2, K)) = P.map e.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hSk := isKleinFour_sylow_psl2_five hK S
  have hPk : IsKleinFour ↥P := by
    have e' : ↥P ≃* ↥(S : Subgroup PSL(2, K)) :=
      (P.equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hScoe.symm)
    exact ⟨by rw [Nat.card_congr e'.toEquiv, hSk.card_four],
      by rw [Monoid.exponent_eq_of_mulEquiv e', hSk.exponent_two]⟩
  have hZL : Subgroup.center ↥L = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [psl2_center_eq_bot K] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hinj := conj_injective_of_center hZL
  have hfix : ∀ φ : MulAut ↥L, (∀ x ∈ P, φ x = x) → ∃ g ∈ P, φ = MulAut.conj g := by
    intro φ hφ
    set φ' : MulAut PSL(2, K) := (e.symm.trans φ).trans e with hφ'def
    have hφ' : ∀ v ∈ (S : Subgroup PSL(2, K)), φ' v = v := by
      intro v hv
      rw [hScoe] at hv
      obtain ⟨x, hx, rfl⟩ := hv
      simp [φ', hφ x hx]
    obtain ⟨g0, hg0, hφg⟩ := psl2_aut_fix_four_prime Nat.prime_five le_rfl hK hSk hφ'
    rw [hScoe] at hg0
    obtain ⟨g, hg, rfl⟩ := hg0
    refine ⟨g, hg, ?_⟩
    ext x
    have h1 := congrArg (fun ψ : MulAut PSL(2, K) => e.symm (ψ (e x))) hφg
    simp only [hφ'def, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply,
      MulEquiv.coe_toMonoidHom] at h1
    rw [h1]
    simp
  have hAin : ∀ a (ha : a ∈ A), ∃ g ∈ P, conjOn L a (leN h ha) = MulAut.conj g :=
    fun a ha => hfix _ fun x hx => conjOn_fix_of_hyp h ha hx
  have hrel := relIndex_eq_card_range L A (leN h)
  have h4 := h.four_le
  set S₁ : Set (MulAut ↥L) := ((actHom L A (leN h)).range : Set (MulAut ↥L)) with hS₁
  set S₂ : Set (MulAut ↥L) := (MulAut.conj : ↥L →* MulAut ↥L) '' (P : Set ↥L) with hS₂
  have hsub : S₁ ⊆ S₂ := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨g, hg, hgeq⟩ := hAin a ha
    exact ⟨g, hg, hgeq.symm⟩
  have hS₂card : S₂.ncard ≤ 4 := by
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hPk.card_four]
  have hS₁card : (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A = S₁.ncard := by
    rw [hrel, hS₁]
    exact Nat.card_coe_set_eq _
  have heq : S₁ = S₂ := Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  have hidx : (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A = 4 := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hsurj : ∀ g ∈ P, ∃ a, ∃ ha : a ∈ A, conjOn L a (leN h ha) = MulAut.conj g := by
    intro g hg
    have h1 : MulAut.conj g ∈ S₁ := by rw [heq]; exact ⟨g, hg, rfl⟩
    obtain ⟨⟨a, ha⟩, ha'⟩ := h1
    exact ⟨a, ha, ha'⟩
  have hRin : ∀ r (hr : r ∈ R), ∃ p ∈ P, conjOn L r (h.normalizer hr) = MulAut.conj p := by
    intro r hr
    apply hfix
    intro x hx
    obtain ⟨a, ha, hax⟩ := hsurj x hx
    have hra : r * a = a * r :=
      (Subgroup.mem_centralizer_iff.mp (h.centralizer hr) a ha).symm
    have hcomm : conjOn L r (h.normalizer hr) * conjOn L a (leN h ha) =
        conjOn L a (leN h ha) * conjOn L r (h.normalizer hr) := by
      rw [← conjOn_mul, ← conjOn_mul]
      congr 1
    rw [hax] at hcomm
    have h1 : MulAut.conj ((conjOn L r (h.normalizer hr)) x) = MulAut.conj x := by
      rw [← mulAut_conj_conj, hcomm, mul_inv_cancel_right]
    exact hinj h1
  have hperf : commutator ↥L = ⊤ := Group.isPerfect_def.mp h.quasisimple.1
  have hP1 : P ≠ ⊥ := by
    intro hb
    have := hPk.card_four
    rw [hb, Subgroup.card_bot] at this
    norm_num at this
  obtain ⟨y, hyN, hyC⟩ := Set.not_subset.mp (not_normalizer_le_centralizer hperf (sylowIn h) hP1)
  obtain ⟨s, t, ht, hst⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  set x := y ^ 2 ^ s with hxdef
  have hxodd : Odd (orderOf x) := by
    rw [hxdef, orderOf_pow_of_dvd (by positivity) (by rw [hst]; exact Dvd.intro t rfl), hst,
      Nat.mul_div_cancel_left t (by positivity)]
    exact ht
  have hxN : x ∈ Subgroup.normalizer (P : Set ↥L) := Subgroup.pow_mem _ hyN _
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    have := hPk.isMulCommutative
    intro a ha b hb
    exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hPC : P ≤ Subgroup.centralizer (P : Set ↥L) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (hPab a ha b hb).symm
  have hxC : x ∉ Subgroup.centralizer (P : Set ↥L) := by
    intro hxc
    set N := Subgroup.normalizer (P : Set ↥L) with hN
    have hPN : (P.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
    have hm := Subgroup.pow_index_mem (P.subgroupOf N) (⟨y, hyN⟩ : ↥N)
    have hym : y ^ (P.subgroupOf N).index ∈ Subgroup.centralizer (P : Set ↥L) := by
      have h1 := Subgroup.mem_subgroupOf.mp hm
      rw [SubmonoidClass.coe_pow] at h1
      exact hPC h1
    have hmodd : ¬ 2 ∣ (P.subgroupOf N).index := by
      intro h2
      apply (sylowIn h).not_dvd_index
      have h3 := Subgroup.relIndex_mul_index (Subgroup.le_normalizer : P ≤ N)
      rw [← h3]
      exact Dvd.dvd.mul_right h2 _
    have hcop : Nat.Coprime (2 ^ s) (P.subgroupOf N).index :=
      Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hmodd)
    have hbez : (1 : ℤ) = ((2 ^ s : ℕ) : ℤ) * Nat.gcdA (2 ^ s) (P.subgroupOf N).index +
        ((P.subgroupOf N).index : ℤ) * Nat.gcdB (2 ^ s) (P.subgroupOf N).index := by
      have := Nat.gcd_eq_gcd_ab (2 ^ s) (P.subgroupOf N).index
      rw [hcop] at this
      exact_mod_cast this
    apply hyC
    have : y = (y ^ 2 ^ s) ^ Nat.gcdA (2 ^ s) (P.subgroupOf N).index *
        (y ^ (P.subgroupOf N).index) ^ Nat.gcdB (2 ^ s) (P.subgroupOf N).index := by
      rw [← zpow_natCast y (2 ^ s), ← zpow_natCast y (P.subgroupOf N).index, ← zpow_mul,
        ← zpow_mul, ← zpow_add, ← hbez, zpow_one]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hxc _) (Subgroup.zpow_mem _ hym _)
  have hxpow := pow_mem_centralizer_iff_of_four hPk hxN hxC hxodd
  refine ⟨(x : Y), x.2, by rwa [Subgroup.orderOf_coe], fun r hr => ?_, fun _ j => ?_⟩
  ·
    obtain ⟨p, hp, hpr⟩ := hRin r hr
    have hconj : ∀ w : ↥L, r * (w : Y) * r⁻¹ = (p : Y) * w * (p : Y)⁻¹ := fun w => by
      have := congrArg (fun φ : MulAut ↥L => ((φ w : ↥L) : Y)) hpr
      simpa [conjOn_coe, MulAut.conj_apply] using this
    have h1 : (x : Y) * r * (x : Y)⁻¹ * r⁻¹ = (x : Y) * (r * ((x⁻¹ : ↥L) : Y) * r⁻¹) := by
      rw [Subgroup.coe_inv]
      group
    rw [h1, hconj]
    have h3 : x * p * x⁻¹ * p⁻¹ ∈ P :=
      P.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN p).mp hp) (P.inv_mem hp)
    have h4 : ((x * p * x⁻¹ * p⁻¹ : ↥L) : Y) ∈ R :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h3)).1
    convert h4 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  ·
    rw [hidx, show (4 : ℕ) - 1 = 3 from rfl, ← hxpow j]
    constructor
    · intro hj
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨a, ha, hag⟩ := hsurj g hg
      have h1 := hj a ha
      rw [← Subgroup.coe_pow, commutator_mem_centralizer_iff hZL (leN h ha) hag] at h1
      exact h1.symm
    · intro hxj a ha
      obtain ⟨g, hg, hag⟩ := hAin a ha
      rw [← Subgroup.coe_pow, commutator_mem_centralizer_iff hZL (leN h ha) hag]
      exact (Subgroup.mem_centralizer_iff.mp hxj g hg).symm

end Five

theorem e68ComponentFactsL2p_holds :
    E6.E68ComponentFactsL2p := by
  intro Y _ _ L A R z hc h
  obtain ⟨hmodel, -⟩ := hc
  rcases hmodel with hL3 | ⟨p, hFM, hL2⟩
  · exact (not_e68Hyp_of_smallList h (Unc25L33.l33_facts ↥L hL3).1
      (Unc25L33.l33_facts ↥L hL3).2).elim
  · have hp : p.Prime := hFM.1
    have hadm := hL2.1
    obtain ⟨-, -, -, h22, h23⟩ := hadm
    have hp2 : p ≠ 2 := fun hp2 => h22 (by subst hp2; rfl)
    have hp3 : p ≠ 3 := fun hp3 => h23 (by subst hp3; rfl)
    by_cases hp5 : p = 5
    · subst hp5
      exact e68Concl_of_psl2_five hL2 h
    · have h7 : 7 ≤ p := by
        have h2 := hp.two_le
        by_contra hlt
        interval_cases p
        · exact hp2 rfl
        · exact hp3 rfl
        · exact absurd hp (by decide)
        · exact hp5 rfl
        · exact absurd hp (by decide)
      rcases h7.lt_or_eq with h7' | h7'
      · obtain ⟨hS, hF⟩ := Unc25Small.l2p_facts hFM h7' ↥L hL2
        exact (not_e68Hyp_of_smallList h hS hF).elim
      · subst h7'
        obtain ⟨K, _, _, _, e, hcard, -, -⟩ :=
          CFSG.QuasithinUnique.K1.psl2_model_data (by norm_num) hL2
        have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
        have hK : Nat.card K = 7 := by rw [Nat.card_eq_fintype_card, hcard, pow_one]
        have H : Unc25Small.L2pHyp K 7 := ⟨le_rfl, hK, Or.inr ⟨by norm_num, 3, by norm_num⟩⟩
        exact (not_e68Hyp_of_smallList h
          (Unc25Small.SmallListFacts.of_mulEquiv e (Unc25Small.psl2_smallListFacts H))
          (Unc25Small.FixPointwiseInner.of_mulEquiv e (Unc25Small.psl2_fixPointwiseInner H))).elim

end CFSG.Quasithin.H13.KG68
