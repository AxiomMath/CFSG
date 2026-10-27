module

public import CFSG.RankThree.PartOne.S9.QD32.PrimeSupport
public import CFSG.RankThree.PartTwo.Sec11.Item116R1StarGrp
public import CFSG.RankThree.PartTwo.Sec11.Item116R1StarCore
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Five

public section

section

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FixedRank36
  CFSG.RankThree.PartTwo.Sec3 Subgroup
open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartTwo.Sec11

theorem h11_two_zpowers {H : Type*} [Group H] {x : H} (hx : x * x = 1) :
    IsPGroup 2 (Subgroup.zpowers x) :=
  CFSG.RankThree.PartOne.Torsion37.isPGroup_zpowers_two (n := 1) (by simpa [pow_two] using hx)

theorem h11_eq_neg_one_of_bot {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (T : Module.End R M) (hT : T * T = 1) (hE : Module.End.eigenspace T 1 = ⊥) : T = -1 := by
  ext v
  have hTT : T (T v) = v := by
    have h := congrArg (fun f : Module.End R M => f v) hT
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  have hw : T v + v ∈ Module.End.eigenspace T 1 := by
    rw [Module.End.mem_eigenspace_iff, one_smul, map_add, hTT, add_comm]
  rw [hE, Submodule.mem_bot] at hw
  rw [LinearMap.neg_apply, Module.End.one_apply]
  exact eq_neg_of_add_eq_zero_left hw

theorem h11_eq_one_of_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (T : Module.End R M) (hE : Module.End.eigenspace T 1 = ⊤) : T = 1 := by
  ext v
  have hv : v ∈ Module.End.eigenspace T 1 := by
    rw [hE]
    exact Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff, one_smul] at hv
  rw [Module.End.one_apply]
  exact hv

theorem h11_rep_comm {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {D U U' : Subgroup G}
    [IsElementaryAbelian p (↥D ⧸ frattini ↥D)] (hU : U ≤ Subgroup.normalizer (D : Set G))
    (hU' : U' ≤ Subgroup.normalizer (D : Set G)) {u : ↥U} {u' : ↥U'}
    (hc : (u : G) * (u' : G) = (u' : G) * (u : G)) :
    frattiniRep p (conjAction D U hU) u * frattiniRep p (conjAction D U' hU') u' =
      frattiniRep p (conjAction D U' hU') u' * frattiniRep p (conjAction D U hU) u := by
  have key : ∀ x : ↥D, conjAction D U hU u (conjAction D U' hU' u' x) =
      conjAction D U' hU' u' (conjAction D U hU u x) := by
    intro x
    apply Subtype.ext
    simp only [conjAction_apply_coe]
    calc (u : G) * ((u' : G) * (x : G) * (u' : G)⁻¹) * (u : G)⁻¹
        = ((u : G) * (u' : G)) * (x : G) * ((u : G) * (u' : G))⁻¹ := by group
      _ = ((u' : G) * (u : G)) * (x : G) * ((u' : G) * (u : G))⁻¹ := by rw [hc]
      _ = (u' : G) * ((u : G) * (x : G) * (u : G)⁻¹) * (u' : G)⁻¹ := by group
  ext v
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hv : v = Additive.ofMul (a : ↥D ⧸ frattini ↥D) := by rw [ha]; rfl
  rw [hv]
  simp only [Module.End.mul_apply, frattiniRep_apply, key]

theorem h11_frattini_ne_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hloc : FiveLocalRankHyp G) (hp3 : 3 < p) {D R : Subgroup G} (hD : IsPGroup p D)
    (hRD : R ≤ Subgroup.normalizer (D : Set G)) [IsElementaryAbelian p (↥D ⧸ frattini ↥D)]
    (hpr : 3 ≤ CFSG.pRank p ↥D) {g : ↥R} (hg1 : g ≠ 1) (hgg : g * g = 1)
    (hT : frattiniRep p (conjAction D R hRD) g = 1) : False := by
  have hgG : (g : G) * (g : G) = 1 := by
    have h := congrArg Subtype.val hgg
    simpa using h
  have hgG1 : (g : G) ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hρ2 : conjAction D R hRD g * conjAction D R hRD g = 1 := by
    rw [← map_mul, hgg, map_one]
  have hρ1 : conjAction D R hRD g = 1 :=
    frattiniRep_eq_one hD (by omega) (conjAction D R hRD) g (h11_two_zpowers hρ2) hT
  have hcen : D ≤ Subgroup.centralizer ({(g : G)} : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun f : MulAut ↥D => ((f ⟨d, hd⟩ : ↥D) : G)) hρ1
    simp only [conjAction_apply_coe, MulAut.one_apply] at h
    calc d * (g : G) = ((g : G) * d * (g : G)⁻¹) * (g : G) := by rw [h]
      _ = (g : G) * d := by group
  have hDC : D ⊓ Subgroup.centralizer ({(g : G)} : Set G) = D := inf_eq_left.mpr hcen
  have hb := hloc p Fact.out hp3 D hD (g : G) hgG1 (h11_two_zpowers hgG)
  rw [hDC] at hb
  omega

theorem h11_frattini_eq_neg_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hloc : FiveLocalRankHyp G) (hp3 : 3 < p) {D R R' : Subgroup G} (hD : IsPGroup p D)
    (hRD : R ≤ Subgroup.normalizer (D : Set G)) (hR'D : R' ≤ Subgroup.normalizer (D : Set G))
    [IsElementaryAbelian p (↥D ⧸ frattini ↥D)] (hirr : IsFrattiniIrreducibleFor R' D)
    (hpr : 3 ≤ CFSG.pRank p ↥D) (hcomm : ∀ a ∈ R, ∀ b ∈ R', a * b = b * a)
    {g : ↥R} (hg1 : g ≠ 1) (hgg : g * g = 1) :
    frattiniRep p (conjAction D R hRD) g = -1 := by
  have hTT : frattiniRep p (conjAction D R hRD) g * frattiniRep p (conjAction D R hRD) g = 1 := by
    rw [← map_mul, hgg, map_one]
  have hinv : ∀ (l : ↥R') (w : Additive (↥D ⧸ frattini ↥D)),
      w ∈ Module.End.eigenspace (frattiniRep p (conjAction D R hRD) g) 1 →
      frattiniRep p (conjAction D R' hR'D) l w ∈
        Module.End.eigenspace (frattiniRep p (conjAction D R hRD) g) 1 := by
    intro l w hw
    have hc := h11_rep_comm (p := p) (u := g) (u' := l) hRD hR'D (hcomm _ g.2 _ l.2)
    have h2 := congrArg (fun f : Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)) => f w) hc
    simp only [Module.End.mul_apply] at h2
    rw [Module.End.mem_eigenspace_iff, one_smul] at hw
    rw [Module.End.mem_eigenspace_iff, one_smul, h2, hw]
  rcases irr_to_module hD hR'D hirr _ hinv with hE | hE
  · exact h11_eq_neg_one_of_bot _ hTT hE
  · exact False.elim (h11_frattini_ne_one hloc hp3 hD hRD hpr hg1 hgg (h11_eq_one_of_top _ hE))

theorem five_e3iii {G : Type} [Group G] [Finite G] (hloc : FiveLocalRankHyp G) {S : Subgroup G} {w w' : G}
    (hwS : w ∈ normalizer (S : Set G)) (hw'S : w' ∈ normalizer (S : Set G))
    (hw : FiveStarData S w) (hw' : FiveStarData S w') (hcomm : ⁅fiveStarR S w, fiveStarR S w'⁆ = ⊥) : False := by
  obtain ⟨⟨eR⟩, -, -⟩ := hw
  obtain ⟨-, -, p, D, hp, hp3, hDp, -, hSD, -, hpr, hirr⟩ := hw'
  haveI : Fact p.Prime := ⟨hp⟩
  have hRD : fiveStarR S w ≤ Subgroup.normalizer (D : Set G) := (fiveStarR_le hwS).trans hSD
  have hR'D : fiveStarR S w' ≤ Subgroup.normalizer (D : Set G) := (fiveStarR_le hw'S).trans hSD
  have hcomm' : ∀ a ∈ fiveStarR S w, ∀ b ∈ fiveStarR S w', a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha) b hb).symm
  have hel : IsElementaryAbelian p (↥D ⧸ frattini ↥D) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hDp).2.2.2.1
  have hQD : IsExtraspecialPGroup 2 QD32 :=
    (CFSG.RankThree.GroupTheory.SteinbergBY.quaternion_dihedral_extraspecial_involution_generation).2.1
  have hext : IsExtraspecialPGroup 2 ↥(fiveStarR S w) :=
    CFSG.RankThree.PartOne.Lifting36.isExtraspecialPGroup_of_mulEquiv eR.symm hQD
  have hcard : Nat.card ↥(fiveStarR S w) = 32 := by
    rw [Nat.card_congr eR.toEquiv, CFSG.RankThree.GroupTheory.card_QD32]
  obtain ⟨z, hzZ, hz1, hzz⟩ := CFSG.RankThree.PartOne.FixedRank36.exists_center_generator hext
  obtain ⟨r, hrc, hro⟩ :=
    CFSG.RankThree.PartOne.FixedRank36.exists_noncentral_involution hext hcard
  have hzc : z ∈ Subgroup.center ↥(fiveStarR S w) := by
    rw [hzZ]
    exact Subgroup.mem_zpowers z
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hrc (Subgroup.one_mem _)
  have hrr : r * r = 1 := by
    rw [← pow_two, ← hro, pow_orderOf_eq_one]
  have hzr : z * r ≠ 1 := by
    intro h
    apply hrc
    have hrz : r = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hrz]
    exact inv_mem hzc
  have hzrzr : z * r * (z * r) = 1 := by
    have hcr : r * z = z * r := Subgroup.mem_center_iff.mp hzc r
    calc z * r * (z * r) = z * (r * z) * r := by group
      _ = z * (z * r) * r := by rw [hcr]
      _ = (z * z) * (r * r) := by group
      _ = 1 := by rw [hzz, hrr, mul_one]
  have hz_neg := h11_frattini_eq_neg_one hloc hp3 hDp hRD hR'D hirr hpr hcomm' hz1 hzz
  have hr_neg := h11_frattini_eq_neg_one hloc hp3 hDp hRD hR'D hirr hpr hcomm' hr1 hrr
  have hzr_one : frattiniRep p (conjAction D (fiveStarR S w) hRD) (z * r) = 1 := by
    rw [map_mul]
    ext v
    rw [Module.End.mul_apply, hz_neg, LinearMap.neg_apply, Module.End.one_apply,
      Module.End.one_apply, hr_neg, LinearMap.neg_apply, Module.End.one_apply, neg_neg]
  exact h11_frattini_ne_one hloc hp3 hDp hRD hpr hzr hzrzr hzr_one

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

def h12_conjAut {G : Type} [Group G] (R : Subgroup G) {w : G} (hw : w ∈ normalizer (R : Set G)) :
    MulAut ↥R where
  toFun r := ⟨w * r * w⁻¹, (Subgroup.mem_normalizer_iff.mp hw (r : G)).mp r.2⟩
  invFun r := ⟨w⁻¹ * r * w, by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hw) (r : G)).mp r.2
    rwa [inv_inv] at h⟩
  left_inv r := Subtype.ext (by simp [mul_assoc])
  right_inv r := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem h12_pow_apply {G : Type} [Group G] {R : Subgroup G} {w : G} (γ : MulAut ↥R)
    (hγ : ∀ r : ↥R, ((γ r : ↥R) : G) = w * r * w⁻¹) (n : ℕ) (r : ↥R) :
    (((γ ^ n) r : ↥R) : G) = w ^ n * r * (w ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' γ n, MulAut.mul_apply, hγ, ih, pow_succ' w n]
    group

theorem h12_mem_inSubgroup_center_iff {G : Type} [Group G] (R : Subgroup G) (x : ↥R) :
    (x : G) ∈ inSubgroup Subgroup.center R ↔ x ∈ Subgroup.center ↥R := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
  · intro hx
    exact Subgroup.mem_map_of_mem R.subtype hx

theorem h12_center_fixed {H : Type} [Group H] (hS : IsExtraspecialPGroup 2 H)
    (γ : MulAut H) : ∀ z ∈ Subgroup.center H, γ z = z := by
  have hcard : Nat.card (Subgroup.center H) = 2 := hS.2.2.2
  have key : ∀ a b : Subgroup.center H, a ≠ 1 → b ≠ 1 → a = b := by
    intro a b ha hb
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center H)).mp hcard
    rw [huniq a ha, huniq b hb]
  intro z hz
  by_cases hz1 : z = 1
  · subst hz1
    simp
  · have hγz : γ z ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      have h2 := congrArg γ (hz (γ.symm g))
      simpa using h2
    have hγz1 : γ z ≠ 1 := by
      intro h
      apply hz1
      have h2 := congrArg γ.symm h
      simpa using h2
    have h3 := key ⟨z, hz⟩ ⟨γ z, hγz⟩ (fun h => hz1 (congrArg Subtype.val h))
      (fun h => hγz1 (congrArg Subtype.val h))
    exact (congrArg Subtype.val h3).symm

theorem h12_dich {H : Type} [Group H] [Finite H] (hS : IsExtraspecialPGroup 2 H)
    (hcard : Nat.card H = 32) (γ : MulAut H) (h5 : γ ^ 5 = 1)
    (hfpf : ∀ s : H, γ s * s⁻¹ ∈ Subgroup.center H → s ∈ Subgroup.center H)
    (T : Subgroup H) (hT : ∀ t ∈ T, γ t ∈ T) : T ≤ Subgroup.center H ∨ T = ⊤ := by
  classical
  have hfix : ∀ z ∈ Subgroup.center H, γ z = z := h12_center_fixed hS γ
  have hZ : ∀ z ∈ Subgroup.center H, γ z ∈ Subgroup.center H := by
    intro z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have h2 := congrArg γ (hz (γ.symm g))
    simpa using h2
  have hAinv : ∀ a ∈ T ⊔ Subgroup.center H, γ a ∈ T ⊔ Subgroup.center H := by
    have hle : (T ⊔ Subgroup.center H).map (γ : H →* H) ≤ T ⊔ Subgroup.center H := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨t, ht, rfl⟩
        exact Subgroup.mem_sup_left (hT t ht)
      · rintro _ ⟨z, hz, rfl⟩
        exact Subgroup.mem_sup_right (hZ z hz)
    intro a ha
    exact hle (Subgroup.mem_map_of_mem _ ha)
  set A : Subgroup H := T ⊔ Subgroup.center H with hAdef
  letI : Fintype A := Fintype.ofFinite A
  let f : Function.End A := fun a => ⟨γ (a : H), hAinv (a : H) a.2⟩
  have hfpow : ∀ (n : ℕ) (a : A), (((f ^ n) a : A) : H) = (γ ^ n) (a : H) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ' f n, pow_succ' γ n]
      show γ (((f ^ n) a : A) : H) = (γ * γ ^ n) (a : H)
      rw [ih a, MulAut.mul_apply]
  have hf5 : f ^ 5 = 1 := by
    apply funext
    intro a
    apply Subtype.ext
    rw [hfpow 5 a, h5]
    try rfl
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hf1 : f ^ 5 ^ 1 = 1 := by simpa using hf5
  have hmod : Nat.card A ≡ Nat.card (Function.fixedPoints f) [MOD 5] := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Equiv.Perm.card_fixedPoints_modEq hf1
  have hmemfix : ∀ a : A, f a = a ↔ (a : H) ∈ Subgroup.center H := by
    intro a
    constructor
    · intro h
      have h1 : γ (a : H) = (a : H) := congrArg Subtype.val h
      apply hfpf
      rw [h1, mul_inv_cancel]
      exact Subgroup.one_mem _
    · intro h
      exact Subtype.ext (hfix _ h)
  have hfp : Nat.card (Function.fixedPoints f) = Nat.card (Subgroup.center H) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨((a : A) : H), (hmemfix (a : A)).mp a.2⟩
        invFun := fun z => ⟨⟨(z : H), Subgroup.mem_sup_right z.2⟩,
          (hmemfix ⟨(z : H), Subgroup.mem_sup_right z.2⟩).mpr z.2⟩
        left_inv := fun a => ?_
        right_inv := fun z => rfl }
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hmod2 : Nat.card A ≡ 2 [MOD 5] := by
    rw [hfp, hS.2.2.2] at hmod
    exact hmod
  have hdvd : Nat.card A ∣ 2 ^ 5 := by
    rw [show (2 : ℕ) ^ 5 = Nat.card H by norm_num [hcard]]
    exact Subgroup.card_subgroup_dvd_card A
  have hcardA : Nat.card A = 2 ∨ Nat.card A = 32 := by
    obtain ⟨i, hi, hiA⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hmod3 : 2 ^ i % 5 = 2 % 5 := by
      rw [← hiA]
      exact hmod2
    interval_cases i
    · norm_num at hmod3
    · exact Or.inl (hiA.trans (by norm_num))
    · norm_num at hmod3
    · norm_num at hmod3
    · norm_num at hmod3
    · exact Or.inr (hiA.trans (by norm_num))
  rcases hcardA with h2 | h32
  · left
    have hZA : Subgroup.center H ≤ A := (le_sup_right : Subgroup.center H ≤ T ⊔ Subgroup.center H)
    have heq : Subgroup.center H = A :=
      Subgroup.eq_of_le_of_card_ge hZA (le_of_eq (by rw [h2, hS.2.2.2]))
    intro t ht
    have htA : t ∈ A := Subgroup.mem_sup_left ht
    rw [heq]
    exact htA
  · right
    have hAtop : A = ⊤ := Subgroup.eq_top_of_card_eq A (by rw [h32, hcard])
    have hfr : T ⊔ frattini H = ⊤ := by
      rw [hS.2.2.1]
      exact hAtop
    exact frattini_nongenerating hfr

theorem star_eq_of_normalizes {G : Type} [Group G] [Finite G] (hloc : FiveLocalRankHyp G) {S : Subgroup G}
    {w w' : G} (hw5 : IsPGroup 5 (zpowers w)) (hwS : w ∈ normalizer (S : Set G))
    (hw'S : w' ∈ normalizer (S : Set G)) (hw : FiveStarData S w) (hw' : FiveStarData S w')
    (hn : w ∈ normalizer (fiveStarR S w' : Set G)) : fiveStarR S w = fiveStarR S w' := by
  have hw1 := hw
  have hw1' := hw'
  obtain ⟨⟨eR⟩, hfpfw, -⟩ := hw1
  obtain ⟨⟨eR'⟩, -, -⟩ := hw1'
  have hQD : IsExtraspecialPGroup 2 QD32 :=
    CFSG.RankThree.GroupTheory.SteinbergBY.quaternion_dihedral_extraspecial_involution_generation.2.1
  have hS : IsExtraspecialPGroup 2 ↥(fiveStarR S w) :=
    CFSG.RankThree.PartOne.Lifting36.isExtraspecialPGroup_of_mulEquiv eR.symm hQD
  have hRcard : Nat.card ↥(fiveStarR S w) = 32 := (Nat.card_congr eR.toEquiv).trans card_QD32
  have hR'card : Nat.card ↥(fiveStarR S w') = 32 := (Nat.card_congr eR'.toEquiv).trans card_QD32
  have hwR : w ∈ normalizer ((fiveStarR S w : Subgroup G) : Set G) := mem_normalizer_fiveStarR_self S w
  obtain ⟨γ, hγ⟩ : ∃ γ : MulAut ↥(fiveStarR S w),
      ∀ r : ↥(fiveStarR S w), ((γ r : ↥(fiveStarR S w)) : G) = w * r * w⁻¹ :=
    ⟨h12_conjAut (fiveStarR S w) hwR, fun r => rfl⟩
  obtain ⟨k, hk⟩ := hw5 ⟨w, Subgroup.mem_zpowers w⟩
  have hwk : w ^ 5 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hγk : γ ^ 5 ^ k = 1 := by
    refine MulEquiv.ext fun r => Subtype.ext ?_
    rw [h12_pow_apply γ hγ, hwk]
    simp
  have hfpf : ∀ s : ↥(fiveStarR S w), γ s * s⁻¹ ∈ Subgroup.center ↥(fiveStarR S w) →
      s ∈ Subgroup.center ↥(fiveStarR S w) := by
    intro s hs
    have h1 : ((γ s * s⁻¹ : ↥(fiveStarR S w)) : G) ∈ inSubgroup Subgroup.center (fiveStarR S w) :=
      Subgroup.mem_map_of_mem (Subgroup.subtype (fiveStarR S w)) hs
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hγ] at h1
    exact (h12_mem_inSubgroup_center_iff (fiveStarR S w) s).mp (hfpfw s s.2 h1)
  have h5 : γ ^ 5 = 1 := pow_five_eq_one_of_fpf hS hRcard γ hγk hfpf
  have hT : ∀ t ∈ (fiveStarR S w').subgroupOf (fiveStarR S w),
      γ t ∈ (fiveStarR S w').subgroupOf (fiveStarR S w) := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    rw [hγ]
    exact (Subgroup.mem_normalizer_iff.mp hn (t : G)).mp ht
  rcases h12_dich hS hRcard γ h5 hfpf _ hT with hle | htop
  ·
    exfalso
    have hZ : ∀ x : G, x ∈ fiveStarR S w → x ∈ fiveStarR S w' →
        x ∈ inSubgroup Subgroup.center (fiveStarR S w) := by
      intro x hx hx'
      have hxT : (⟨x, hx⟩ : ↥(fiveStarR S w)) ∈ (fiveStarR S w').subgroupOf (fiveStarR S w) :=
        Subgroup.mem_subgroupOf.mpr hx'
      exact (h12_mem_inSubgroup_center_iff (fiveStarR S w) ⟨x, hx⟩).mpr (hle hxT)
    have hcR : ⁅fiveStarR S w', Subgroup.zpowers w⁆ ≤ fiveStarR S w :=
      Subgroup.commutator_mono (fiveStarR_le hw'S) le_rfl
    have hcR' : ⁅fiveStarR S w', Subgroup.zpowers w⁆ ≤ fiveStarR S w' :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hn)
    have hcRZ : ⁅fiveStarR S w', Subgroup.zpowers w⁆ ≤ inSubgroup Subgroup.center (fiveStarR S w) := by
      intro x hx
      exact hZ x (hcR hx) (hcR' hx)
    have hwc : Subgroup.zpowers w ≤
        Subgroup.centralizer ((inSubgroup Subgroup.center (fiveStarR S w) : Subgroup G) : Set G) := by
      apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
      have hx' : w * (x : G) * w⁻¹ = x := by
        rw [← hγ, h12_center_fixed hS γ x hx]
      show (x : G) * w = w * (x : G)
      calc (x : G) * w = (w * (x : G) * w⁻¹) * w := by rw [hx']
        _ = w * (x : G) := by group
    have hZw : ⁅Subgroup.zpowers w, inSubgroup Subgroup.center (fiveStarR S w)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hwc
    have hZw' : ⁅inSubgroup Subgroup.center (fiveStarR S w), Subgroup.zpowers w⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hZw
    have hpp : ⁅⁅fiveStarR S w', Subgroup.zpowers w⁆, Subgroup.zpowers w⁆ ≤
        ⁅inSubgroup Subgroup.center (fiveStarR S w), Subgroup.zpowers w⁆ :=
      Subgroup.commutator_mono hcRZ le_rfl
    rw [hZw'] at hpp
    have hcop : Nat.Coprime 5 (Nat.card ↥(fiveStarR S w')) := by
      rw [hR'card]
      norm_num
    have hidem := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 5
      Nat.prime_five (Subgroup.zpowers w) (fiveStarR S w') hw5 (Subgroup.zpowers_le.mpr hn) hcop
    have hR'w : ⁅fiveStarR S w', Subgroup.zpowers w⁆ = ⊥ :=
      hidem.symm.trans (le_bot_iff.mp hpp)
    have hRS : ⁅fiveStarR S w', S⁆ ≤ fiveStarR S w' :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_fiveStarR hw'S)
    have h1 : ⁅⁅Subgroup.zpowers w, fiveStarR S w'⁆, S⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (H₁ := Subgroup.zpowers w) (H₂ := fiveStarR S w'), hR'w,
        Subgroup.commutator_bot_left]
    have h2 : ⁅⁅fiveStarR S w', S⁆, Subgroup.zpowers w⁆ = ⊥ := by
      apply le_bot_iff.mp
      calc ⁅⁅fiveStarR S w', S⁆, Subgroup.zpowers w⁆ ≤ ⁅fiveStarR S w', Subgroup.zpowers w⁆ :=
            Subgroup.commutator_mono hRS le_rfl
        _ = ⊥ := hR'w
    have h3 : ⁅⁅S, Subgroup.zpowers w⁆, fiveStarR S w'⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    exact five_e3iii hloc hwS hw'S hw hw' h3
  ·
    have hsub : fiveStarR S w ≤ fiveStarR S w' := by
      intro x hx
      have hxT : (⟨x, hx⟩ : ↥(fiveStarR S w)) ∈ (fiveStarR S w').subgroupOf (fiveStarR S w) := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hxT
    exact Subgroup.eq_of_le_of_card_ge hsub (le_of_eq (by rw [hRcard, hR'card]))

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem h13_act {G : Type} [Group G] (H : Subgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (H : Set G)) (r : G) (hr : r ∈ H) :
    ((Subgroup.normalizerMonoidHom H ⟨x, hx⟩ : MulAut H) ⟨r, hr⟩ : G) = x * r * x⁻¹ := rfl

theorem h13_triv_of_one {G : Type} [Group G] (H : Subgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (H : Set G))
    (h : Subgroup.normalizerMonoidHom H ⟨x, hx⟩ = 1) : ∀ r ∈ H, x * r * x⁻¹ = r := by
  intro r hr
  have h1 : ((Subgroup.normalizerMonoidHom H ⟨x, hx⟩ : MulAut H) ⟨r, hr⟩ : G) = r := by
    rw [h]
    rfl
  exact (h13_act H hx r hr).symm.trans h1

theorem h13_QD32_not_comm : ¬ ∀ u v : QD32, u * v = v * u := by
  intro hcomm
  obtain ⟨h32, -, -, -, -, -, hord, hcen, -⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBY.quaternion_dihedral_extraspecial_involution_generation
  have htop : Subgroup.center QD32 = ⊤ :=
    (Subgroup.eq_top_iff' (Subgroup.center QD32)).mpr fun g =>
      Subgroup.mem_center_iff.mpr fun h => hcomm h g
  have h1 : Nat.card ↥(Subgroup.center QD32) = 32 := by
    rw [htop, Subgroup.card_top, h32]
  rw [hcen, Nat.card_zpowers, hord] at h1
  omega

theorem h13_no_triv {G : Type} [Group G] {S : Subgroup G} {x : G} (hx : FiveStarData S x)
    (htriv : ∀ r ∈ fiveStarR S x, x * r * x⁻¹ = r) : False := by
  obtain ⟨⟨e⟩, hfix, -⟩ := hx
  have hcen : ∀ r : fiveStarR S x, r ∈ Subgroup.center (fiveStarR S x) := by
    intro r
    have h1 : x * (r : G) * x⁻¹ * (r : G)⁻¹ ∈ CFSG.inSubgroup Subgroup.center (fiveStarR S x) := by
      rw [htriv (r : G) r.2, mul_inv_cancel]
      exact one_mem _
    have h2 : (r : G) ∈ (Subgroup.center (fiveStarR S x)).map (fiveStarR S x).subtype :=
      hfix (r : G) r.2 h1
    obtain ⟨z, hz, hzr⟩ := Subgroup.mem_map.mp h2
    have hzr' : z = r := Subtype.ext hzr
    rw [← hzr']
    exact hz
  have hcomm : ∀ u v : QD32, u * v = v * u := by
    intro u v
    have key := Subgroup.mem_center_iff.mp (hcen (e.symm v)) (e.symm u)
    have h3 := congrArg e key
    simpa using h3
  exact h13_QD32_not_comm hcomm

theorem five_cyclic_action {G : Type} [Group G] [Finite G] (hloc : FiveLocalRankHyp G) {θ S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hstar : FiveStarAt θ S) {P : Subgroup G} (hP5 : IsPGroup 5 P)
    (hPS : P ≤ normalizer (S : Set G)) (hPθ : P ≤ normalizer (θ : Set G)) {a b : G} (ha : a ∈ P)
    (hb : b ∈ P) (hcomm : ∀ s ∈ S, a * (b * s * b⁻¹) * a⁻¹ = b * (a * s * a⁻¹) * b⁻¹)
    (hnt : ∃ s ∈ S, a * s * a⁻¹ ≠ s) :
    ∃ j : ℤ, ∀ s ∈ S, b * s * b⁻¹ = a ^ j * s * (a ^ j)⁻¹ := by
  classical
  have ha5 : IsPGroup 5 (Subgroup.zpowers a) := hP5.to_le (Subgroup.zpowers_le.mpr ha)
  have hSa : FiveStarData S a := hstar a ha5 (hPθ ha) (hPS ha) hnt
  have hne : Nonempty (↥(fiveStarR S a) ≃* QD32) := by
    obtain ⟨h, -, -⟩ := hSa
    exact h
  have haN : a ∈ Subgroup.normalizer (fiveStarR S a : Set G) := mem_normalizer_fiveStarR_self S a
  have hbN : b ∈ Subgroup.normalizer (fiveStarR S a : Set G) :=
    mem_normalizer_fiveStarR_of_commute (hPS ha) (hPS hb) hcomm
  have hPm5 : IsPGroup 5 ↥(P ⊓ Subgroup.normalizer (fiveStarR S a : Set G)) :=
    hP5.to_le inf_le_left
  have hPmN : P ⊓ Subgroup.normalizer (fiveStarR S a : Set G) ≤
      Subgroup.normalizer (fiveStarR S a : Set G) := inf_le_right
  set ψ : ↥(P ⊓ Subgroup.normalizer (fiveStarR S a : Set G)) →* MulAut ↥(fiveStarR S a) :=
    (Subgroup.normalizerMonoidHom (fiveStarR S a)).comp (Subgroup.inclusion hPmN) with hψ
  set A : Subgroup (MulAut ↥(fiveStarR S a)) := ψ.range with hA
  have hA5 : IsPGroup 5 ↥A :=
    hPm5.of_surjective ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ)
  have hMA : Nat.card (MulAut ↥(fiveStarR S a)) ∣ 2 ^ 7 * 3 * 5 :=
    (quaternionDihedralAutomorphismPrimeSupport ↥(fiveStarR S a) hne).1
  have hAdvd : Nat.card ↥A ∣ 2 ^ 7 * 3 * 5 := (Subgroup.card_subgroup_dvd_card A).trans hMA
  haveI : Finite (MulAut ↥(fiveStarR S a)) := Nat.finite_of_card_ne_zero (fun h => by
    rw [h, zero_dvd_iff] at hMA
    norm_num at hMA)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 5)).mp hA5
  set a' : ↥(P ⊓ Subgroup.normalizer (fiveStarR S a : Set G)) :=
    ⟨a, Subgroup.mem_inf.mpr ⟨ha, haN⟩⟩ with ha'
  set b' : ↥(P ⊓ Subgroup.normalizer (fiveStarR S a : Set G)) :=
    ⟨b, Subgroup.mem_inf.mpr ⟨hb, hbN⟩⟩ with hb'
  set t : MulAut ↥(fiveStarR S a) := ψ a' with ht
  have ht1 : t ≠ 1 := by
    intro h
    have h' : Subgroup.normalizerMonoidHom (fiveStarR S a) ⟨a, haN⟩ = 1 := h
    exact h13_no_triv hSa (h13_triv_of_one (fiveStarR S a) haN h')
  have hbA : ψ b' ∈ A := MonoidHom.mem_range.mpr ⟨b', rfl⟩
  have htA : t ∈ A := MonoidHom.mem_range.mpr ⟨a', rfl⟩
  have hdvdt : orderOf t ∣ Nat.card ↥A := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr htA)
  have hn1 : n = 1 := by
    have hle : n ≤ 1 := by
      by_contra hcon
      have h25 : 5 ^ 2 ∣ 5 ^ n := pow_dvd_pow 5 (by omega)
      have h1920 : 5 ^ 2 ∣ 2 ^ 7 * 3 * 5 := by
        have h5n : 5 ^ n ∣ 2 ^ 7 * 3 * 5 := by
          rw [← hn]
          exact hAdvd
        exact dvd_trans h25 h5n
      norm_num at h1920
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hn
      rw [hn] at hdvdt
      exact ht1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvdt))
    · omega
  have hcardA : Nat.card ↥A = 5 := by
    rw [hn, hn1, pow_one]
  have hord : orderOf t = 5 := by
    rw [hcardA] at hdvdt
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvdt with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  have hzp : Subgroup.zpowers t = A := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htA)
    exact le_of_eq (by rw [Nat.card_zpowers, hord, hcardA])
  obtain ⟨k, hk⟩ : ∃ k : ℤ, t ^ k = ψ b' := by
    have hmem : ψ b' ∈ Subgroup.zpowers t := by
      rw [hzp]
      exact hbA
    exact Subgroup.mem_zpowers_iff.mp hmem
  set y : ↥(P ⊓ Subgroup.normalizer (fiveStarR S a : Set G)) := (a' ^ k)⁻¹ * b' with hy
  have hψy : ψ y = 1 := by
    rw [hy, map_mul, map_inv, map_zpow, ← ht, hk, inv_mul_cancel]
  have hyP : (y : G) ∈ P := (Subgroup.mem_inf.mp y.2).1
  have hyN : (y : G) ∈ Subgroup.normalizer (fiveStarR S a : Set G) := (Subgroup.mem_inf.mp y.2).2
  have hyR : ∀ r ∈ fiveStarR S a, (y : G) * r * (y : G)⁻¹ = r :=
    h13_triv_of_one (fiveStarR S a) hyN hψy
  have hyS : ∀ s ∈ S, (y : G) * s * (y : G)⁻¹ = s := by
    intro s hs
    by_contra hns
    have hy5 : IsPGroup 5 (Subgroup.zpowers (y : G)) := hP5.to_le (Subgroup.zpowers_le.mpr hyP)
    have hSy : FiveStarData S (y : G) := hstar (y : G) hy5 (hPθ hyP) (hPS hyP) ⟨s, hs, hns⟩
    have hT : fiveStarR S (y : G) = fiveStarR S a :=
      star_eq_of_normalizes hloc hy5 (hPS hyP) (hPS ha) hSy hSa hyN
    refine h13_no_triv hSy (fun r hr => ?_)
    rw [hT] at hr
    exact hyR r hr
  refine ⟨k, fun s hs => ?_⟩
  have h1 := hyS s hs
  have hy_eq : (y : G) = (a ^ k)⁻¹ * b := by
    rw [hy]
    rfl
  rw [hy_eq] at h1
  calc b * s * b⁻¹ = a ^ k * ((a ^ k)⁻¹ * b * s * ((a ^ k)⁻¹ * b)⁻¹) * (a ^ k)⁻¹ := by group
    _ = a ^ k * s * (a ^ k)⁻¹ := by rw [h1]

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem zpow_inv_mul_zpow_mem {G : Type*} [Group G] {θ H : Subgroup G}
    (hθH : θ ≤ H) (hHθ : H ≤ normalizer (θ : Set G)) {x n : G} (hx : x ∈ H) (hn : n ∈ θ)
    (c : ℤ) : (x ^ c)⁻¹ * (x * n) ^ c ∈ θ := by
  haveI : (θ.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHθ
  have hxn : x * n ∈ H := mul_mem hx (hθH hn)
  have h1 : QuotientGroup.mk' (θ.subgroupOf H) (⟨x * n, hxn⟩ : H) =
      QuotientGroup.mk' (θ.subgroupOf H) (⟨x, hx⟩ : H) := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hn
  have h2 : QuotientGroup.mk' (θ.subgroupOf H) ((⟨x * n, hxn⟩ : H) ^ c) =
      QuotientGroup.mk' (θ.subgroupOf H) ((⟨x, hx⟩ : H) ^ c) := by
    rw [map_zpow, map_zpow, h1]
  have h3 : ((⟨x, hx⟩ : H) ^ c)⁻¹ * (⟨x * n, hxn⟩ : H) ^ c ∈ θ.subgroupOf H := by
    have h2' := h2.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2'
    exact h2'
  have h4 := Subgroup.mem_subgroupOf.mp h3
  simpa using h4

theorem five_decomp_mem {G : Type*} [Group G] {θ H : Subgroup G} (hθH : θ ≤ H)
    (hHθ : H ≤ normalizer (θ : Set G)) {x n₁ n₂ : G} (hx : x ∈ H) (hn₁ : n₁ ∈ θ) (hn₂ : n₂ ∈ θ)
    (c : ℤ) : ((x ^ (-c))⁻¹ * n₂ * (x * n₁) ^ (-c)) ∈ θ := by
  have hxc : x ^ (-c) ∈ H := zpow_mem hx _
  have hconj : ∀ t ∈ θ, ∀ g ∈ H, g⁻¹ * t * g ∈ θ := by
    intro t ht g hg
    have := (Subgroup.mem_normalizer_iff.mp (hHθ (inv_mem hg)) t).mp ht
    simpa using this
  have h1 : (x ^ (-c))⁻¹ * n₂ * x ^ (-c) ∈ θ := hconj n₂ hn₂ _ hxc
  have h2 : (x ^ (-c))⁻¹ * (x * n₁) ^ (-c) ∈ θ := by
    have := zpow_inv_mul_zpow_mem hθH hHθ hx hn₁ (-c)
    exact this
  have : (x ^ (-c))⁻¹ * n₂ * (x * n₁) ^ (-c) =
      ((x ^ (-c))⁻¹ * n₂ * x ^ (-c)) * ((x ^ (-c))⁻¹ * (x * n₁) ^ (-c)) := by group
  rw [this]
  exact mul_mem h1 h2

theorem fiveCaseCore_of_star : FiveCaseCore := by
  have hstar := CFSG.RankThree.PartTwo.Sec11.five_star_prop
  intro G _ _ hloc θ H S K₁ K₂ _ _ hθH hHθ hθs hθ3 hO2 hSθ hS2 _hSyl hK₁H hK₁S hK₁perf hK₂H hK₂S
    hK₂perf hcomm _hind hs₁ h5₁ hs₂ h5₂ hnt₁ hnt₂
  classical
  have hloc' : FiveLocalRankHyp G := hloc
  have hSA : FiveStarAt θ S := hstar G hloc' θ S hθs hθ3 hO2 hSθ hS2
  obtain ⟨x₁, hx₁K, hx₁θ, hx₁5⟩ := exists_five_element_not_mem h5₁
  obtain ⟨x₂, hx₂K, hx₂θ, hx₂5⟩ := exists_five_element_not_mem h5₂
  obtain ⟨P, y₁, y₂, n₁, n₂, hP5, hPS, hPH, hy₁P, hy₂P, hn₁θ, hn₁S, hn₂θ, hn₂S, hy₁eq, hy₂eq⟩ :=
    exists_five_lifts hθH hHθ hK₁H hK₁S hK₂H hK₂S hcomm hx₁K hx₂K hx₁5 hx₂5
  have hPθ : P ≤ normalizer (θ : Set G) := fun g hg => hHθ (hPH hg)
  have hy₁nt : ∃ s ∈ S, y₁ * s * y₁⁻¹ ≠ s := by
    by_contra hcon
    push Not at hcon
    apply hx₁θ
    refine five_nc_lemma (K := K₁) hθH hHθ hθs hK₁H hK₁S hK₁perf hs₁ hnt₁ hx₁K (m := 1) (one_mem H)
      (fun g _ => by simpa using (one_mem θ)) ?_ hcon
    rw [hy₁eq]
    simpa using hn₁θ
  have hy₂nt : ∃ s ∈ S, y₂ * s * y₂⁻¹ ≠ s := by
    by_contra hcon
    push Not at hcon
    apply hx₂θ
    refine five_nc_lemma (K := K₂) hθH hHθ hθs hK₂H hK₂S hK₂perf hs₂ hnt₂ hx₂K (m := 1) (one_mem H)
      (fun g _ => by simpa using (one_mem θ)) ?_ hcon
    rw [hy₂eq]
    simpa using hn₂θ
  have hV : ∀ a ∈ P, (∀ g ∈ P, ∀ s ∈ S, a * (g * s * g⁻¹) * a⁻¹ = g * (a * s * a⁻¹) * g⁻¹) →
      (∃ s ∈ S, a * s * a⁻¹ ≠ s) → ∀ b ∈ P, ∃ j : ℤ, ∀ s ∈ S,
        b * s * b⁻¹ = a ^ j * s * (a ^ j)⁻¹ :=
    fun a haP hcen hnt b hb => five_cyclic_action hloc' hS2 hSA hP5 hPS hPθ haP hb
      (fun s hs => hcen b hb s hs) hnt
  obtain ⟨c, hc⟩ := exists_zpow_action hP5 hPS hV hy₁P hy₂P hy₁nt
  have hy₁S : y₁ ∈ normalizer (S : Set G) := hPS hy₁P
  have hy₂S : y₂ ∈ normalizer (S : Set G) := hPS hy₂P
  have hzS : ∀ s ∈ S, (y₂ * y₁ ^ (-c)) * s * (y₂ * y₁ ^ (-c))⁻¹ = s := by
    intro s hs
    have hy₁c : ∀ t ∈ S, y₁ ^ (-c) * t * (y₁ ^ (-c))⁻¹ ∈ S := by
      intro t ht
      have hmem : y₁ ^ (-c) ∈ normalizer (S : Set G) := zpow_mem hy₁S _
      exact (Subgroup.mem_normalizer_iff.mp hmem t).mp ht
    have h1 := hc (y₁ ^ (-c) * s * (y₁ ^ (-c))⁻¹) (hy₁c s hs)
    have e : y₂ * y₁ ^ (-c) * s * (y₂ * y₁ ^ (-c))⁻¹ =
        y₂ * (y₁ ^ (-c) * s * (y₁ ^ (-c))⁻¹) * y₂⁻¹ := by group
    rw [e, h1]
    group
  have hx₁m : x₁ ^ (-c) ∈ K₁ := zpow_mem hx₁K _
  have hmH : x₁ ^ (-c) ∈ H := hK₁H hx₁m
  have hmK : ∀ g ∈ K₂, ⁅x₁ ^ (-c), g⁆ ∈ θ := fun g hg =>
    hcomm (Subgroup.commutator_mem_commutator hx₁m hg)
  have hy : (x₂ * x₁ ^ (-c))⁻¹ * (y₂ * y₁ ^ (-c)) ∈ θ := by
    have h := five_decomp_mem hθH hHθ (hK₁H hx₁K) hn₁θ hn₂θ c
    have e : (x₂ * x₁ ^ (-c))⁻¹ * (y₂ * y₁ ^ (-c)) =
        (x₁ ^ (-c))⁻¹ * n₂ * (x₁ * n₁) ^ (-c) := by
      rw [hy₂eq, hy₁eq]
      group
    rw [e]
    exact h
  exact hx₂θ (five_nc_lemma (K := K₂) hθH hHθ hθs hK₂H hK₂S hK₂perf hs₂ hnt₂ hx₂K hmH hmK hy hzS)

theorem fiveCaseCore : FiveCaseCore := fiveCaseCore_of_star

end CFSG.RankThree.PartTwo.Sec11

end
