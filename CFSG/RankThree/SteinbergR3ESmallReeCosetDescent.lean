module

public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.LieType.Ree.G2ExceptionalCosetInvolutions
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals

public noncomputable section

namespace CFSG.RankThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.AlgebraicGroups CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.GroupTheory

theorem fixed_torusGroup_eq_map_of_det_one {τ : Tag} (hdet : τ.cartan.transpose.det = 1)
    {K : Type} [Field K] (σ : K ≃+* K) :
    torusGroup τ K ⊓ (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) =
      (torusGroup τ (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype) := by
  set k := fixSubfield σ
  set ι := k.subtype
  refine le_antisymm ?_ ?_
  · rintro h ⟨hh, hfix⟩
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    have hσa : ∀ i, σ (a i : K) = a i := by
      have hF : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ a) = rootDiagUnit τ a := hfix
      have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ a) =
          rootDiagUnit τ (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) :=
        Units.ext (entrywise_rootDiag σ.toRingHom a)
      have h1 := rootDiagUnit_injective (h0.symm.trans hF)
      intro i
      exact congrArg Units.val (congrFun h1 i)
    set a' : Fin τ.rank → kˣ := fun i =>
      Units.mk0 ⟨a i, hσa i⟩ fun h => (a i).ne_zero (congrArg Subtype.val h)
    have ha' : ∀ i, Units.map ι.toMonoidHom (a' i) = a i := fun i => Units.ext rfl
    refine ⟨((List.finRange τ.rank).map fun j =>
      torusElt τ k j (∏ i, a' i ^ τ.cartan.transpose.adjugate j i)).prod,
      list_prod_torusElt_mem_torusGroup _, ?_⟩
    rw [map_list_prod, List.map_map]
    rw [rootDiagUnit_eq_list_prod_torusElt_adjugate
      (u := fun i => Units.map ι.toMonoidHom (a' i)) fun i => by rw [hdet, zpow_one, ha']]
    refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
    rw [Function.comp_apply, baseChangeGL_torusElt, map_prod]
    simp only [map_zpow]
  · have hle : torusGroup τ k ≤ (torusGroup τ K).comap (baseChangeGL ι) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨⟨i, s⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
      exact torusElt_mem_torusGroup i _
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨hle hg, ?_⟩
    change baseChangeGL σ.toRingHom (baseChangeGL ι g) = baseChangeGL ι g
    rw [baseChangeGL_baseChangeGL,
      show σ.toRingHom.comp ι = ι from RingHom.ext fun c => (mem_fixSubfield σ).1 c.2]

theorem entrywiseFixedGroup_eq_fixedFieldImage_of_det_one {τ : Tag}
    (hdet : τ.cartan.transpose.det = 1) {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    entrywiseFixedGroup τ σ = fixedFieldImage τ σ := by
  obtain ⟨-, -, -, hJΓ, hΓ, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  refine le_antisymm (fun g hg => ?_) hJΓ
  have hg' : g ∈ (entrywiseFixedGroup τ σ : Set (ModGL τ K)) := hg
  rw [hΓ] at hg'
  obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.1 hg'
  refine mul_mem ?_ hj
  have hh' : h ∈ torusGroup τ K ⊓
      (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) := ⟨hh.1, hh.2.2⟩
  rw [fixed_torusGroup_eq_map_of_det_one hdet σ] at hh'
  obtain ⟨t, ht, rfl⟩ := hh'
  have hle : torusGroup τ (fixSubfield σ) ≤ adjointGroup τ (fixSubfield σ) :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  exact ⟨t, hle ht, rfl⟩

theorem det_transpose_cartan_G2 : Tag.G2.cartan.transpose.det = 1 := by
  rw [Matrix.det_transpose, det_cartan_G2]

section BaseChange

variable {k K : Type} [Field k] [Finite k] [CharP k ReeTag.G2.prime] [Field K] [Finite K]
  [CharP K ReeTag.G2.prime]

theorem adjointBaseChangeHom_finiteExceptionalAut (ι₀ : k →+* K)
    (u : adjointGroup ReeTag.G2.tag k) :
    adjointBaseChangeHom ReeTag.G2.tag ι₀ (ReeTag.G2.finiteExceptionalAut k u) =
      ReeTag.G2.finiteExceptionalAut K (adjointBaseChangeHom ReeTag.G2.tag ι₀ u) := by
  have hx : ∀ (i : Fin ReeTag.G2.tag.rank) (c : k),
      adjointBaseChangeHom ReeTag.G2.tag ι₀ (xElement i c) = xElement i (ι₀ c) :=
    fun i c => Subtype.ext (baseChangeGL_xUnit _ i c)
  have hy : ∀ (i : Fin ReeTag.G2.tag.rank) (c : k),
      adjointBaseChangeHom ReeTag.G2.tag ι₀ (yElement i c) = yElement i (ι₀ c) :=
    fun i c => Subtype.ext (baseChangeGL_yUnit _ i c)
  have h := adjointGroup_hom_ext
    (f := (adjointBaseChangeHom ReeTag.G2.tag ι₀).comp
      (ReeTag.G2.finiteExceptionalAut k).toMonoidHom)
    (g := (ReeTag.G2.finiteExceptionalAut K).toMonoidHom.comp
      (adjointBaseChangeHom ReeTag.G2.tag ι₀))
    (fun i c => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [ReeTag.finiteExceptionalAut_xElement, hx, hx, ReeTag.finiteExceptionalAut_xElement,
        map_pow])
    (fun i c => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [ReeTag.finiteExceptionalAut_yElement, hy, hy, ReeTag.finiteExceptionalAut_yElement,
        map_pow])
  exact DFunLike.congr_fun h u

theorem adjointBaseChangeHom_finiteFrobeniusAut (ι₀ : k →+* K)
    (u : adjointGroup ReeTag.G2.tag k) :
    adjointBaseChangeHom ReeTag.G2.tag ι₀ (ReeTag.G2.finiteFrobeniusAut k u) =
      ReeTag.G2.finiteFrobeniusAut K (adjointBaseChangeHom ReeTag.G2.tag ι₀ u) := by
  refine Subtype.ext ?_
  rw [coe_adjointBaseChangeHom, ReeTag.coe_finiteFrobeniusAut, ReeTag.coe_finiteFrobeniusAut,
    coe_adjointBaseChangeHom]
  change baseChangeGL ι₀ (Units.map (entrywiseHom (frobenius k ReeTag.G2.prime))
      (u : ModGL ReeTag.G2.tag k)) =
    Units.map (entrywiseHom (frobenius K ReeTag.G2.prime)) (baseChangeGL ι₀ (u : ModGL _ k))
  have hc : (frobenius K ReeTag.G2.prime).comp ι₀ = ι₀.comp (frobenius k ReeTag.G2.prime) :=
    RingHom.ext fun c => by simp only [RingHom.comp_apply, frobenius_def, map_pow]
  rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
    baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hc]

theorem adjointBaseChangeHom_finiteFrobeniusAut_pow (ι₀ : k →+* K) (n : ℕ)
    (u : adjointGroup ReeTag.G2.tag k) :
    adjointBaseChangeHom ReeTag.G2.tag ι₀ ((ReeTag.G2.finiteFrobeniusAut k ^ n) u) =
      (ReeTag.G2.finiteFrobeniusAut K ^ n) (adjointBaseChangeHom ReeTag.G2.tag ι₀ u) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply, ih,
      adjointBaseChangeHom_finiteFrobeniusAut]

theorem adjointBaseChangeHom_finiteReeAut (ι₀ : k →+* K) (a : ℕ)
    (u : adjointGroup ReeTag.G2.tag k) :
    adjointBaseChangeHom ReeTag.G2.tag ι₀ (ReeTag.G2.finiteReeAut k a u) =
      ReeTag.G2.finiteReeAut K a (adjointBaseChangeHom ReeTag.G2.tag ι₀ u) := by
  change adjointBaseChangeHom ReeTag.G2.tag ι₀
      ((ReeTag.G2.finiteExceptionalAut k * ReeTag.G2.finiteFrobeniusAut k ^ a) u) =
    (ReeTag.G2.finiteExceptionalAut K * ReeTag.G2.finiteFrobeniusAut K ^ a)
      (adjointBaseChangeHom ReeTag.G2.tag ι₀ u)
  rw [MulAut.mul_apply, MulAut.mul_apply, adjointBaseChangeHom_finiteExceptionalAut,
    adjointBaseChangeHom_finiteFrobeniusAut_pow]

theorem finiteFrobeniusAut_pow_eq_one {d : ℕ} (hk : Nat.card k = 3 ^ d) :
    ReeTag.G2.finiteFrobeniusAut k ^ d = 1 := by
  have hexp : ExpChar k 3 := by
    have : CharP k 3 := ‹CharP k ReeTag.G2.prime›
    exact ExpChar.prime Nat.prime_three
  have : Fintype k := Fintype.ofFinite k
  refine MulEquiv.ext fun u => Subtype.ext ?_
  rw [coe_pow_apply_of_entrywise_frobenius 3 (ReeTag.G2.finiteFrobeniusAut k)
    (fun g => by rw [ReeTag.coe_finiteFrobeniusAut, iterateFrobenius_one]; rfl) d u]
  have hid : iterateFrobenius k 3 d = RingHom.id k := RingHom.ext fun c => by
    rw [iterateFrobenius_def, RingHom.id_apply, ← hk, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  rw [hid, MulAut.one_apply]
  exact Units.ext (entrywise_id _)

theorem finiteReeAut_eq_of_modEq {a b d m : ℕ} (hk : Nat.card k = 3 ^ d) (hab : a = b + d * m) :
    ReeTag.G2.finiteReeAut k a = ReeTag.G2.finiteReeAut k b := by
  change ReeTag.G2.finiteExceptionalAut k * ReeTag.G2.finiteFrobeniusAut k ^ a =
    ReeTag.G2.finiteExceptionalAut k * ReeTag.G2.finiteFrobeniusAut k ^ b
  rw [hab, pow_add, pow_mul, finiteFrobeniusAut_pow_eq_one hk, one_pow, mul_one]

end BaseChange

theorem fixed_reeGamma_eq_map {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    {a b d m : ℕ} (σ : K ≃+* K) (hk : Nat.card (fixSubfield σ) = 3 ^ d) (hab : a = b + d * m) :
    ((ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (ReeTag.G2.reeGamma K a).subtype =
      (ReeTag.G2.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype) := by
  set k := fixSubfield σ
  set ι := adjointBaseChangeHom ReeTag.G2.tag k.subtype with hι
  have hFab := finiteReeAut_eq_of_modEq (k := k) hk hab
  have hJ := entrywiseFixedGroup_eq_fixedFieldImage_of_det_one (τ := ReeTag.G2.tag)
    det_transpose_cartan_G2 σ
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ReeTag.G2.reeGammaFieldAut K a σ x = x := hx
    obtain ⟨hgC, hgF⟩ := ReeTag.mem_reeGamma.1 x.2
    have hfix : (x : ModGL ReeTag.G2.tag K) ∈ entrywiseFixedGroup ReeTag.G2.tag σ := by
      refine ⟨hgC, ?_⟩
      have h := congrArg (fun y : ReeTag.G2.reeGamma K a => (y : ModGL ReeTag.G2.tag K)) hx'
      simp only [ReeTag.coe_reeGammaFieldAut] at h
      exact h
    rw [hJ] at hfix
    obtain ⟨v, hv, hvx⟩ := hfix
    refine ⟨v, ReeTag.mem_reeGamma.2 ⟨hv, ?_⟩, hvx⟩
    apply adjointBaseChangeHom_injective ReeTag.G2.tag k.subtype
    rw [← hFab, adjointBaseChangeHom_finiteReeAut]
    have hιv : ι ⟨v, hv⟩ = ⟨(x : ModGL ReeTag.G2.tag K), hgC⟩ := Subtype.ext hvx
    rw [hιv]
    exact hgF
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hvC, hvF⟩ := ReeTag.mem_reeGamma.1 hv
    have hgC : baseChangeGL k.subtype v ∈ adjointGroup ReeTag.G2.tag K :=
      baseChangeGL_mem_adjointGroup _ hvC
    have hgΓ : baseChangeGL k.subtype v ∈ ReeTag.G2.reeGamma K a := by
      refine ReeTag.mem_reeGamma.2 ⟨hgC, ?_⟩
      have h := adjointBaseChangeHom_finiteReeAut k.subtype a ⟨v, hvC⟩
      rw [hFab, hvF] at h
      exact h.symm
    refine ⟨⟨_, hgΓ⟩, ?_, rfl⟩
    change ReeTag.G2.reeGammaFieldAut K a σ ⟨_, hgΓ⟩ = ⟨_, hgΓ⟩
    refine Subtype.ext ?_
    rw [ReeTag.coe_reeGammaFieldAut]
    change Units.map (entrywiseHom σ.toRingHom) (baseChangeGL k.subtype v) =
      baseChangeGL k.subtype v
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
      show σ.toRingHom.comp k.subtype = k.subtype from RingHom.ext fun c => c.2]

theorem exists_conj_eq_section_of_ker_isPGroup {O A : Type*} [Group O] [Finite O] [Group A]
    (hA : ∀ u v : A, u * v = v * u)
    (χ : O →* A) {q p : ℕ} [Fact q.Prime] (hp : p.Prime) (hpq : p ≠ q) (hR : IsPGroup q χ.ker)
    (s : A →* O) (hs : ∀ σ, χ (s σ) = σ) (x : O) (hx : orderOf x = p) :
    orderOf (χ x) = p ∧ ∃ o : O, o * x * o⁻¹ = s (χ x) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set σ := χ x with hσdef
  have hσp : orderOf σ = p := by
    have h1 : orderOf σ ∣ p := by
      rw [← hx]
      exact orderOf_map_dvd χ x
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exfalso
      have hxk : x ∈ χ.ker := by
        rw [MonoidHom.mem_ker]
        exact orderOf_eq_one_iff.1 h
      obtain ⟨n, hn⟩ := hR ⟨x, hxk⟩
      have hdvd : p ∣ q ^ n := by
        rw [← hx]
        exact orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn)
      exact hpq ((Nat.prime_dvd_prime_iff_eq hp (Fact.out)).1 (hp.dvd_of_dvd_pow hdvd))
    · exact h
  refine ⟨hσp, ?_⟩
  set H := (Subgroup.zpowers σ).comap χ with hHdef
  have hxH : x ∈ H := Subgroup.mem_zpowers σ
  have hsH : s σ ∈ H := by
    change χ (s σ) ∈ Subgroup.zpowers σ
    rw [hs]
    exact Subgroup.mem_zpowers σ
  have hkerH : χ.ker ≤ H := fun y hy => by
    change χ y ∈ Subgroup.zpowers σ
    rw [MonoidHom.mem_ker.1 hy]
    exact Subgroup.one_mem _
  set χH : H →* A := χ.comp H.subtype
  have hker : χH.ker = χ.ker.subgroupOf H := by
    ext y
    rfl
  have hrange : χH.range = Subgroup.zpowers σ := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      exact y.2
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨x, hxH⟩, rfl⟩
  have hHcard : Nat.card H = Nat.card χ.ker * p := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup χH.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange χH).toEquiv, hrange,
      Nat.card_zpowers, hσp, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerH).toEquiv,
      mul_comm]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hR
  have hfact : (Nat.card H).factorization p = 1 := by
    have hq : q.Prime := Fact.out
    rw [hHcard, hm, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hp.ne_zero,
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)),
      smul_zero, zero_add, hp.factorization_self]
  have hcard1 : Nat.card ((Subgroup.zpowers x).subgroupOf H) =
      p ^ (Nat.card H).factorization p := by
    rw [hfact, pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((Subgroup.zpowers_le).2 hxH)).toEquiv, Nat.card_zpowers, hx]
  have hsp : orderOf (s σ) = p := by
    have h1 : orderOf (s σ) ∣ p := orderOf_dvd_of_pow_eq_one (by
      rw [← map_pow, ← hσp, pow_orderOf_eq_one, map_one])
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exfalso
      have : σ = 1 := by
        rw [← hs σ, orderOf_eq_one_iff.1 h, map_one]
      rw [this, orderOf_one] at hσp
      exact hp.one_lt.ne hσp
    · exact h
  have hcard2 : Nat.card ((Subgroup.zpowers (s σ)).subgroupOf H) =
      p ^ (Nat.card H).factorization p := by
    rw [hfact, pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((Subgroup.zpowers_le).2 hsH)).toEquiv, Nat.card_zpowers, hsp]
  let P₁ := Sylow.ofCard _ hcard1
  let P₂ := Sylow.ofCard _ hcard2
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H P₁ P₂
  have hmem : h * ⟨x, hxH⟩ * h⁻¹ ∈ (P₂ : Subgroup H) := by
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (MulAut.conj h)⁻¹ • (h * ⟨x, hxH⟩ * h⁻¹) = ⟨x, hxH⟩ := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]
      group
    rw [this]
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers x)
  have hmem' : (h : O) * x * (h : O)⁻¹ ∈ Subgroup.zpowers (s σ) := Subgroup.mem_subgroupOf.1 hmem
  obtain ⟨j, hj⟩ := hmem'
  have hj' : s σ ^ j = (h : O) * x * (h : O)⁻¹ := hj
  refine ⟨h, ?_⟩
  have hχ : σ ^ j = σ := by
    have := congrArg χ hj'
    rw [map_zpow, hs, map_mul, map_mul, map_inv, hA (χ h) (χ x), mul_inv_cancel_right] at this
    exact this
  rw [← hj', ← map_zpow, hχ]

theorem finiteReeAut_eq_pow {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime] (n : ℕ) :
    ReeTag.G2.finiteReeAut K n = ReeTag.G2.finiteExceptionalAut K ^ (2 * n + 1) := by
  change ReeTag.G2.finiteExceptionalAut K * ReeTag.G2.finiteFrobeniusAut K ^ n = _
  rw [← finiteExceptionalAut_mul_self ReeTag.G2, ← sq, ← pow_mul, ← pow_succ']

theorem exists_conj_eq_of_lang {Γ M : Type*} [Group Γ] [Group M] (hZ : Subgroup.center Γ = ⊥)
    (F₀ : MulAut Γ) {p : ℕ} (hp : 1 ≤ p) (hF₀p : F₀ ^ p = 1) (S₀ : MulAut M)
    (hLang : ∀ m : M, ∃ h, m = h⁻¹ * S₀ h) (e : Γ →* M) (he : Function.Injective e)
    (heF₀ : ∀ g, e (F₀ g) = S₀ (e g))
    (hnorm : ∀ h : M, (S₀ ^ p) h = h → h ∈ Subgroup.normalizer (e.range : Set M))
    (x : Γ) (hβ : (MulAut.conj x * F₀) ^ p = 1) :
    ∃ δ : MulAut Γ, δ * (MulAut.conj x * F₀) * δ⁻¹ = F₀ := by
  classical
  have hβ' := hβ
  rw [conj_mul_pow, hF₀p, mul_one] at hβ'
  generalize hNdef : ((List.range p).map fun i => (F₀ ^ i) x).prod = N at hβ'
  have hN1 : N = 1 := by
    have hc : N ∈ Subgroup.center Γ := by
      refine Subgroup.mem_center_iff.2 fun g => ?_
      have h1 : N * g * N⁻¹ = g := by
        have := congrArg (fun φ : MulAut Γ => φ g) hβ'
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc g * N = N * g * N⁻¹ * N := by rw [h1]
        _ = N * g := by group
    rw [hZ] at hc
    exact Subgroup.mem_bot.1 hc
  have hS₀iter : ∀ (i : ℕ) (g : Γ), (⇑S₀.toMonoidHom)^[i] (e g) = e ((F₀ ^ i) g) := by
    intro i
    induction i with
    | zero => intro g; rfl
    | succ i ih =>
      intro g
      rw [Function.iterate_succ_apply', ih, MulEquiv.coe_toMonoidHom, ← heF₀,
        ← MulAut.mul_apply, ← pow_succ']
  have hnormx : ((List.range p).map fun i => (⇑S₀.toMonoidHom)^[i] (e x)).prod = 1 := by
    have h1 : ((List.range p).map fun i => (⇑S₀.toMonoidHom)^[i] (e x)) =
        ((List.range p).map fun i => (F₀ ^ i) x).map e := by
      rw [List.map_map]
      exact List.map_congr_left fun i _ => hS₀iter i x
    rw [h1, ← map_list_prod, hNdef, hN1, map_one]
  obtain ⟨h, hR, hxh, -⟩ :=
    exceptional_Lang_norm_one_descent S₀.toMonoidHom hp hLang (e x) hnormx
  have hS₀iterate : ∀ (n : ℕ) (y : M), (⇑S₀.toMonoidHom)^[n] y = (S₀ ^ n) y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply', ih, pow_succ', MulAut.mul_apply]
      rfl
  have hhS : (S₀ ^ p) h = h := by
    rw [← hS₀iterate]
    exact mem_iterateFixedSubgroup.1 hR
  have hmap : e.range.map (MulAut.conj h).toMonoidHom = e.range :=
    map_conj_eq_of_mem_normalizer (hnorm h hhS)
  let eΓ : Γ ≃* e.range := MonoidHom.ofInjective he
  have heΓ : ∀ g, (eΓ g : M) = e g := fun _ => rfl
  let δ : MulAut Γ := eΓ.trans ((mulAutRestrict _ (MulAut.conj h) hmap).trans eΓ.symm)
  have hδ : ∀ g, e (δ g) = h * e g * h⁻¹ := by
    intro g
    rw [← heΓ, ← heΓ]
    change ((eΓ (eΓ.symm (mulAutRestrict _ (MulAut.conj h) hmap (eΓ g))) : e.range) : M) = _
    rw [MulEquiv.apply_symm_apply, coe_mulAutRestrict, MulAut.conj_apply]
  have hδinv : ∀ g, e (δ⁻¹ g) = h⁻¹ * e g * h := by
    intro g
    have h1 := hδ (δ⁻¹ g)
    rw [MulAut.apply_inv_self] at h1
    rw [h1]
    group
  refine ⟨δ, MulEquiv.ext fun u => he ?_⟩
  have hxh' : e x = h⁻¹ * S₀ h := hxh
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hδ, MulAut.conj_apply, map_mul,
    map_mul, map_inv, hxh', heF₀, hδinv, heF₀, map_mul, map_mul, map_inv]
  group

theorem exceptional_G2_lang_data {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] {a b p : ℕ}
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (hbp : (2 * b + 1) * p = 2 * a + 1)
    (φK : MulAut (adjointGroup Tag.G2 K))
    (hφx0 : ∀ c : K, φK (xElement ⟨0, by decide⟩ c) = xElement ⟨1, by decide⟩ c)
    (hφx1 : ∀ c : K, φK (xElement ⟨1, by decide⟩ c) = xElement ⟨0, by decide⟩ (c ^ 3))
    (hφy0 : ∀ c : K, φK (yElement ⟨0, by decide⟩ c) = yElement ⟨1, by decide⟩ c)
    (hφy1 : ∀ c : K, φK (yElement ⟨1, by decide⟩ c) = yElement ⟨0, by decide⟩ (c ^ 3)) :
    ∃ S₀ : MulAut (adjointGroup Tag.G2 L),
      (∀ m, ∃ h, m = h⁻¹ * S₀ h) ∧
      (∀ u, S₀ (adjointBaseChangeHom Tag.G2 (algebraMap K L) u) =
        adjointBaseChangeHom Tag.G2 (algebraMap K L) ((φK ^ (2 * b + 1)) u)) ∧
      (∀ u, (S₀ ^ p) (adjointBaseChangeHom Tag.G2 (algebraMap K L) u) =
        adjointBaseChangeHom Tag.G2 (algebraMap K L) ((φK ^ (2 * a + 1)) u)) ∧
      ∃ Frq : L →+* L, (∀ c, Frq c = c ^ Nat.card K) ∧
        ∀ y, (((S₀ ^ p) ((S₀ ^ p) y) : adjointGroup Tag.G2 L) : ModGL Tag.G2 L) =
          Units.map (entrywiseHom Frq) (y : ModGL Tag.G2 L) := by
  classical
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L 3 := charP_of_injective_algebraMap (algebraMap K L).injective 3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Algebra (ZMod 3) L := ZMod.algebra L 3
  have : Algebra.IsAlgebraic (ZMod 3) L := by
    have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
    let : Algebra (ZMod 3) K := ZMod.algebra K 3
    have : IsScalarTower (ZMod 3) K L := IsScalarTower.of_algebraMap_eq fun c =>
      (RingHom.ext_zmod (algebraMap (ZMod 3) L) ((algebraMap K L).comp
        (algebraMap (ZMod 3) K))) ▸ rfl
    have : Algebra.IsAlgebraic (ZMod 3) K := Algebra.IsAlgebraic.of_finite (ZMod 3) K
    exact Algebra.IsAlgebraic.trans (ZMod 3) K L
  have : IsAlgClosure (ZMod 3) L := ⟨inferInstance, inferInstance⟩
  obtain ⟨Φ, hΦ, -, hΦFr, -⟩ := exceptional_Lang_G2_closure_exceptional_map (L := L)
  obtain ⟨⟨Fr, hFr⟩, -⟩ := (exceptional_Lang_root_coordinate_surjectivity 3 L).1 Tag.G2 1 le_rfl
  have hLang := (exceptional_Lang_root_coordinate_surjectivity 3 L).2.2 rfl Φ hΦ Fr hFr b
  obtain ⟨hsq, -⟩ := hΦFr (iterateFrobenius L 3 1) fun c => by
    rw [iterateFrobenius_def, pow_one]
  have hFrtw : ∀ y, Fr y = frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) y := fun y =>
    Subtype.ext (hFr y)
  have hΦΦ : Φ * Φ = Fr := MulEquiv.ext fun y => by
    rw [MulAut.mul_apply, hFrtw]
    exact DFunLike.congr_fun hsq y
  have hS₀pow : Φ * Fr ^ b = Φ ^ (2 * b + 1) := by
    rw [← hΦΦ, ← sq, ← pow_mul, ← pow_succ']
  have hS₀p : (Φ * Fr ^ b) ^ p = Φ ^ (2 * a + 1) := by rw [hS₀pow, ← pow_mul, hbp]
  set ι := adjointBaseChangeHom Tag.G2 (algebraMap K L) with hιdef
  have hιx : ∀ (i : Fin Tag.G2.rank) (c : K), ι (xElement i c) = xElement i (algebraMap K L c) :=
    fun i c => Subtype.ext (baseChangeGL_xUnit _ i c)
  have hιy : ∀ (i : Fin Tag.G2.rank) (c : K), ι (yElement i c) = yElement i (algebraMap K L c) :=
    fun i c => Subtype.ext (baseChangeGL_yUnit _ i c)
  have hΦι : ∀ u : adjointGroup Tag.G2 K, Φ (ι u) = ι (φK u) := by
    have h := adjointGroup_hom_ext (f := Φ.toMonoidHom.comp ι) (g := ι.comp φK.toMonoidHom)
      (fun i c => by
        fin_cases i
        · exact ((congrArg Φ (hιx _ c)).trans (hΦ _).1).trans
            ((hιx _ c).symm.trans (congrArg ι (hφx0 c).symm))
        · exact ((congrArg Φ (hιx _ c)).trans (hΦ _).2.2.1).trans
            (((hιx _ (c ^ 3)).trans (by rw [map_pow])).symm.trans (congrArg ι (hφx1 c).symm)))
      (fun i c => by
        fin_cases i
        · exact ((congrArg Φ (hιy _ c)).trans (hΦ _).2.1).trans
            ((hιy _ c).symm.trans (congrArg ι (hφy0 c).symm))
        · exact ((congrArg Φ (hιy _ c)).trans (hΦ _).2.2.2).trans
            (((hιy _ (c ^ 3)).trans (by rw [map_pow])).symm.trans (congrArg ι (hφy1 c).symm)))
    exact fun u => DFunLike.congr_fun h u
  have hΦnι : ∀ (n : ℕ) (u : adjointGroup Tag.G2 K), (Φ ^ n) (ι u) = ι ((φK ^ n) u) := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, ih, hΦι, pow_succ', MulAut.mul_apply]
  refine ⟨Φ * Fr ^ b, hLang, fun u => by rw [hS₀pow, hΦnι], fun u => by rw [hS₀p, hΦnι],
    iterateFrobenius L 3 (2 * a + 1), fun c => by rw [iterateFrobenius_def, hK], fun y => ?_⟩
  rw [← MulAut.mul_apply, hS₀p, ← pow_add, show 2 * a + 1 + (2 * a + 1) = 2 * (2 * a + 1) by
    ring, pow_mul, sq, hΦΦ]
  exact coe_pow_apply_of_entrywise_frobenius 3 Fr hFr _ y

section Descent

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem finiteExceptionalAut_G2_formulas :
    (∀ c : K, ReeTag.G2.finiteExceptionalAut K (xElement ⟨0, by decide⟩ c) =
      xElement ⟨1, by decide⟩ c) ∧
    (∀ c : K, ReeTag.G2.finiteExceptionalAut K (xElement ⟨1, by decide⟩ c) =
      xElement ⟨0, by decide⟩ (c ^ 3)) ∧
    (∀ c : K, ReeTag.G2.finiteExceptionalAut K (yElement ⟨0, by decide⟩ c) =
      yElement ⟨1, by decide⟩ c) ∧
    ∀ c : K, ReeTag.G2.finiteExceptionalAut K (yElement ⟨1, by decide⟩ c) =
      yElement ⟨0, by decide⟩ (c ^ 3) := by
  have hp0 : ReeTag.G2.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have hp1 : ReeTag.G2.perm ⟨1, by decide⟩ = ⟨0, by decide⟩ := by decide
  have he0 : ReeTag.G2.exponent ⟨0, by decide⟩ = 1 := by decide
  have he1 : ReeTag.G2.exponent ⟨1, by decide⟩ = 3 := by decide
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_⟩
  · have h := ReeTag.finiteExceptionalAut_xElement (t := ReeTag.G2) (K := K) ⟨0, by decide⟩ c
    rw [hp0, he0, pow_one] at h
    exact h
  · have h := ReeTag.finiteExceptionalAut_xElement (t := ReeTag.G2) (K := K) ⟨1, by decide⟩ c
    rw [hp1, he1] at h
    exact h
  · have h := ReeTag.finiteExceptionalAut_yElement (t := ReeTag.G2) (K := K) ⟨0, by decide⟩ c
    rw [hp0, he0, pow_one] at h
    exact h
  · have h := ReeTag.finiteExceptionalAut_yElement (t := ReeTag.G2) (K := K) ⟨1, by decide⟩ c
    rw [hp1, he1] at h
    exact h

@[expose] def reeGammaToAdjoint (a : ℕ) :
    ReeTag.G2.reeGamma K a →* adjointGroup ReeTag.G2.tag K where
  toFun g := ⟨g, (ReeTag.mem_reeGamma.1 g.2).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem reeGammaToAdjoint_injective (a : ℕ) :
    Function.Injective (reeGammaToAdjoint (K := K) a) := fun g₁ g₂ h => by
  have h' := congrArg (fun y : adjointGroup ReeTag.G2.tag K => (y : ModGL ReeTag.G2.tag K)) h
  exact Subtype.ext h'

theorem finiteReeAut_reeGammaToAdjoint (a : ℕ) (g : ReeTag.G2.reeGamma K a) :
    ReeTag.G2.finiteReeAut K a (reeGammaToAdjoint a g) = reeGammaToAdjoint a g :=
  (ReeTag.mem_reeGamma.1 g.2).2

theorem exists_conj_eq_of_finiteReeAut {a b p : ℕ} (hK : Nat.card K = 3 ^ (2 * a + 1))
    (hp : 1 ≤ p) (hbp : (2 * b + 1) * p = 2 * a + 1) (F₀ : MulAut (ReeTag.G2.reeGamma K a))
    (hF₀ : ∀ g, reeGammaToAdjoint a (F₀ g) = ReeTag.G2.finiteReeAut K b (reeGammaToAdjoint a g))
    (x : ReeTag.G2.reeGamma K a) (hβ : (MulAut.conj x * F₀) ^ p = 1) :
    ∃ δ : MulAut (ReeTag.G2.reeGamma K a), δ * (MulAut.conj x * F₀) * δ⁻¹ = F₀ := by
  classical
  set j := reeGammaToAdjoint (K := K) a with hj
  let L := AlgebraicClosure K
  obtain ⟨hφx0, hφx1, hφy0, hφy1⟩ := finiteExceptionalAut_G2_formulas (K := K)
  obtain ⟨S₀, hLang, hS₀ι, hSι, Frq, hFrqc, hS₀pp⟩ :=
    exceptional_G2_lang_data L hK hbp (ReeTag.G2.finiteExceptionalAut K) hφx0 hφx1 hφy0 hφy1
  set ι := adjointBaseChangeHom Tag.G2 (algebraMap K L) with hιdef
  set e := ι.comp j with hedef
  have he : Function.Injective e :=
    (adjointBaseChangeHom_injective Tag.G2 (algebraMap K L)).comp (reeGammaToAdjoint_injective a)
  have hF₀n : ∀ (n : ℕ) (g : ReeTag.G2.reeGamma K a),
      j ((F₀ ^ n) g) = (ReeTag.G2.finiteReeAut K b ^ n) (j g) := by
    intro n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [pow_succ', MulAut.mul_apply, hF₀, ih, pow_succ' (ReeTag.G2.finiteReeAut K b),
        MulAut.mul_apply]
  have hF₀p : F₀ ^ p = 1 := by
    refine MulEquiv.ext fun g => reeGammaToAdjoint_injective a ?_
    rw [hF₀n, finiteReeAut_eq_pow, ← pow_mul, hbp, ← finiteReeAut_eq_pow,
      finiteReeAut_reeGammaToAdjoint, MulAut.one_apply]
  have heF₀ : ∀ g, e (F₀ g) = S₀ (e g) := by
    intro g
    change ι (j (F₀ g)) = S₀ (ι (j g))
    rw [hF₀, finiteReeAut_eq_pow]
    exact (hS₀ι (j g)).symm
  have hmemĜ : ∀ y : adjointGroup Tag.G2 L, y ∈ e.range ↔
      (y : ModGL Tag.G2 L) ∈ (adjointGroup Tag.G2 K).map (baseChangeGL (algebraMap K L)) ∧
        (S₀ ^ p) y = y := by
    intro y
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨⟨(j g).1, (j g).2, rfl⟩, ?_⟩
      change (S₀ ^ p) (ι (j g)) = ι (j g)
      refine (hSι (j g)).trans ?_
      have h1 := finiteReeAut_reeGammaToAdjoint a g
      rw [finiteReeAut_eq_pow] at h1
      exact congrArg ι h1
    · rintro ⟨⟨u, hu, huy⟩, hy⟩
      have hyι : y = ι ⟨u, hu⟩ := Subtype.ext huy.symm
      rw [hyι] at hy
      have hy' := (hSι ⟨u, hu⟩).symm.trans hy
      have hF : ReeTag.G2.finiteReeAut K a ⟨u, hu⟩ = ⟨u, hu⟩ := by
        have h1 := adjointBaseChangeHom_injective Tag.G2 (algebraMap K L) hy'
        rw [finiteReeAut_eq_pow]
        exact h1
      exact ⟨⟨u, ReeTag.mem_reeGamma.2 ⟨hu, hF⟩⟩, hyι.symm⟩
  obtain ⟨-, -, hnorml⟩ := Chevalley_Frobenius_fixed_ambient_normalizer Tag.G2 K L Frq hFrqc
  have hconjmem : ∀ (h' : adjointGroup Tag.G2 L), (S₀ ^ p) h' = h' →
      ∀ y ∈ e.range, h' * y * h'⁻¹ ∈ e.range := by
    intro h' hS' y hy
    have hN' : (h' : ModGL Tag.G2 L) ∈ Subgroup.normalizer
        ((adjointGroup Tag.G2 K).map (baseChangeGL (algebraMap K L)) : Set (ModGL Tag.G2 L)) := by
      refine hnorml ⟨h'.2, ?_⟩
      change Units.map (entrywiseHom Frq) (h' : ModGL Tag.G2 L) = h'
      rw [← hS₀pp h', hS', hS']
    rw [hmemĜ] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hN' _).1 hy1
    · rw [map_mul, map_mul, map_inv, hS', hy2]
  have hnorm : ∀ h : adjointGroup Tag.G2 L, (S₀ ^ p) h = h →
      h ∈ Subgroup.normalizer (e.range : Set (adjointGroup Tag.G2 L)) := by
    intro h hhS
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconjmem h hhS y, fun hy => ?_⟩
    have h2 := hconjmem h⁻¹ (by rw [map_inv, hhS]) _ hy
    have e2 : h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y := by group
    rwa [e2] at h2
  exact exists_conj_eq_of_lang (small_Ree_fixed_group_center_trivial a K hK).1 F₀ hp hF₀p S₀
    hLang e he heF₀ hnorm x hβ

end Descent

private theorem small_Ree_coset_descent_data {a : ℕ}
    (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (σ : K ≃+* K) (hσp : orderOf σ = p) (x : ReeTag.G2.reeGamma K a)
    (hβ₁p : (MulAut.conj x * ReeTag.G2.reeGammaFieldAut K a σ) ^ p = 1) :
    ∃ δ : MulAut (ReeTag.G2.reeGamma K a),
      δ * (MulAut.conj x * ReeTag.G2.reeGammaFieldAut K a σ) * δ⁻¹ =
        ReeTag.G2.reeGammaFieldAut K a σ ∧
      Nat.card (fixSubfield σ) = 3 ^ ((2 * a + 1) / p) ∧
      ((ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.G2.reeGamma K a).subtype =
        (ReeTag.G2.reeGamma (fixSubfield σ) (((2 * a + 1) / p - 1) / 2)).map
          (baseChangeGL (fixSubfield σ).subtype) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨σ₁, hσ₁, hσ₁ord, hσ₁top, hcardAut, hfix⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := K) Nat.prime_three (by omega) hK
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ₁, hσ₁top⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hpf : p ∣ 2 * a + 1 := by
    rw [← hσp, ← hcardAut]
    exact orderOf_dvd_natCard σ
  obtain ⟨d, hd⟩ := hpf
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨m, hm⟩ := hpodd
  have hdodd : Odd d := by
    have h1 : Odd (p * d) := hd ▸ odd_two_mul_add_one a
    exact (Nat.odd_mul.1 h1).2
  obtain ⟨b, hb⟩ := hdodd
  have hbp : (2 * b + 1) * p = 2 * a + 1 := by rw [← hb, hd, mul_comm]
  set σh := ReeTag.G2.reeGammaFieldAut K a σ with hσh
  have hσ₁pow : ∀ (n : ℕ) (c : K), (σ₁ ^ n) c = c ^ (3 ^ n) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ, RingAut.mul_apply, hσ₁, ih, ← pow_mul, ← pow_succ']
  set e₀ := d * (m + 1) with he₀
  set τ₀ := σ₁ ^ e₀ with hτ₀def
  have hτ₀ord : orderOf τ₀ = p := by
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · rw [h, mul_zero] at hd
        omega
      · exact h
    have hp2le := hp.two_le
    have hcop : Nat.Coprime p (m + 1) := Nat.coprime_of_lt_prime (by omega) (by omega) hp
    have hg : Nat.gcd (p * d) (d * (m + 1)) = d := by
      rw [mul_comm p d, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
    rw [hτ₀def, orderOf_pow' _ (by positivity), hσ₁ord, hd, hg, Nat.mul_div_cancel _ hd0]
  have hzz : Subgroup.zpowers τ₀ = Subgroup.zpowers σ :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hτ₀ord, hσp])
  obtain ⟨r, hr⟩ : ∃ r : ℕ, σ ^ r = τ₀ := by
    have h : τ₀ ∈ Subgroup.zpowers σ := hzz ▸ Subgroup.mem_zpowers τ₀
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  obtain ⟨r', hr'⟩ : ∃ r' : ℕ, τ₀ ^ r' = σ := by
    have h : σ ∈ Subgroup.zpowers τ₀ := hzz ▸ Subgroup.mem_zpowers σ
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  set τh := ReeTag.G2.reeGammaFieldAut K a τ₀ with hτh
  set x' := ((List.range r).map fun i => (σh ^ i) x).prod with hx'
  have hβ₂ : (MulAut.conj x * σh) ^ r = MulAut.conj x' * τh := by
    rw [conj_mul_pow, hτh, ← hr]
    congr 1
    exact (map_pow (ReeTag.G2.reeGammaFieldAutHom K a) σ r).symm
  have hβ₂p : (MulAut.conj x' * τh) ^ p = 1 := by
    rw [← hβ₂, ← pow_mul, mul_comm, pow_mul, hβ₁p, one_pow]
  have hexp : ExpChar K 3 := by
    have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
    exact ExpChar.prime Nat.prime_three
  have hFr : ∀ g : adjointGroup ReeTag.G2.tag K,
      ((ReeTag.G2.finiteFrobeniusAut K g : adjointGroup ReeTag.G2.tag K) :
        ModGL ReeTag.G2.tag K) =
        Units.map (entrywiseHom (iterateFrobenius K 3 1)) (g : ModGL ReeTag.G2.tag K) := by
    intro g
    rw [ReeTag.coe_finiteFrobeniusAut]
    congr 2
  have hτ₀ring : τ₀.toRingHom = iterateFrobenius K 3 e₀ := RingHom.ext fun c => by
    rw [iterateFrobenius_def]
    exact hσ₁pow e₀ c
  have hF₀ : ∀ g, reeGammaToAdjoint a (τh g) =
      ReeTag.G2.finiteReeAut K b (reeGammaToAdjoint a g) := by
    intro g
    have hfixg := finiteReeAut_reeGammaToAdjoint a g
    rw [finiteReeAut_eq_pow] at hfixg
    refine Subtype.ext ?_
    change Units.map (entrywiseHom τ₀.toRingHom) (g : ModGL ReeTag.G2.tag K) = _
    have e1 : p * d = 2 * (d * m) + d := by rw [hm]; ring
    have e2 : d * (m + 1) = d * m + d := by ring
    rw [finiteReeAut_eq_pow, ← hfixg, ← MulAut.mul_apply, ← pow_add,
      show 2 * b + 1 + (2 * a + 1) = 2 * e₀ by rw [he₀, e2]; omega, pow_mul, sq,
      finiteExceptionalAut_mul_self ReeTag.G2, hτ₀ring]
    exact (coe_pow_apply_of_entrywise_frobenius 3 (ReeTag.G2.finiteFrobeniusAut K) hFr e₀
      (reeGammaToAdjoint a g)).symm
  obtain ⟨δ₂, hδ₂⟩ := exists_conj_eq_of_finiteReeAut hK hp.one_lt.le hbp τh hF₀ x' hβ₂p
  have hrr : (MulAut.conj x * σh) ^ (r * r') = MulAut.conj x * σh := by
    have hσrr : σ ^ (r * r') = σ ^ 1 := by rw [pow_mul, hr, hr', pow_one]
    rw [pow_eq_pow_iff_modEq, hσp] at hσrr
    have hdvd : orderOf (MulAut.conj x * σh) ∣ p := orderOf_dvd_of_pow_eq_one hβ₁p
    have h2 := Nat.ModEq.of_dvd hdvd hσrr
    rw [← pow_eq_pow_iff_modEq, pow_one] at h2
    exact h2
  have hfin : δ₂ * (MulAut.conj x * σh) * δ₂⁻¹ = σh := by
    rw [← hrr, pow_mul, hβ₂, ← conj_pow, hδ₂, hτh]
    have h1 : ReeTag.G2.reeGammaFieldAut K a τ₀ ^ r' =
        ReeTag.G2.reeGammaFieldAut K a (τ₀ ^ r') :=
      (map_pow (ReeTag.G2.reeGammaFieldAutHom K a) τ₀ r').symm
    rw [h1, hr']
  have hd' : (2 * a + 1) / p = d := by rw [hd, Nat.mul_div_cancel_left _ hp.pos]
  have hbd : ((2 * a + 1) / p - 1) / 2 = b := by rw [hd', hb]; omega
  have hab : a = b + d * m := by
    have e1 : p * d = 2 * (d * m) + d := by rw [hm]; ring
    omega
  obtain ⟨-, S, hS, hScard⟩ := hfix (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσp] at hScard
  have hSk : S = fixSubfield σ := by
    refine SetLike.coe_injective (Set.ext fun c => ?_)
    rw [hS]
    constructor
    · intro hc
      exact hc σ (Subgroup.mem_zpowers σ)
    · intro hc τ hτ
      have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) c :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hc)
      exact MulAction.mem_stabilizer_iff.1 (hle hτ)
  have hk : Nat.card (fixSubfield σ) = 3 ^ d := by rw [← hSk, hScard, hd']
  exact ⟨δ₂, hfin, by rw [hd']; exact hk, by rw [hbd]; exact fixed_reeGamma_eq_map σ hk hab⟩


theorem small_Ree_large_prime_field_coset_descent (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (α : MulAut (ReeTag.G2.reeGamma K a)) (hα : orderOf α = p)
    (hαout : α ∉ OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a)) :
    p ∣ 2 * a + 1 ∧
    ∃ (δ : MulAut (ReeTag.G2.reeGamma K a)) (σ : K ≃+* K), orderOf σ = p ∧
      δ * α * δ⁻¹ = ReeTag.G2.reeGammaFieldAut K a σ ∧
      Nat.card (fixSubfield σ) = 3 ^ ((2 * a + 1) / p) ∧
      ((ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.G2.reeGamma K a).subtype =
        (ReeTag.G2.reeGamma (fixSubfield σ) (((2 * a + 1) / p - 1) / 2)).map
          (baseChangeGL (fixSubfield σ).subtype) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨σ₁, hσ₁, hσ₁ord, hσ₁top, hcardAut, hfix⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := K) Nat.prime_three (by omega) hK
  have hcomm : ∀ u v : K ≃+* K, u * v = v * u := by
    intro u v
    have hu : u ∈ Subgroup.zpowers σ₁ := hσ₁top ▸ Subgroup.mem_top u
    have hv : v ∈ Subgroup.zpowers σ₁ := hσ₁top ▸ Subgroup.mem_top v
    obtain ⟨k, rfl⟩ := hu
    obtain ⟨l, rfl⟩ := hv
    exact zpow_mul_comm σ₁ k l
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ₁, hσ₁top⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  obtain ⟨-, -, -, ⟨R, χ, hker, hsec, -, hR3, -⟩, -, -⟩ :=
    small_Ree_outer_three_kernel_field_complement a ha K hK
  set s : (K ≃+* K) →* Outer (ReeTag.G2.reeGamma K a) :=
    (QuotientGroup.mk' (OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a))).comp
      (ReeTag.G2.reeGammaFieldAutHom K a) with hsdef
  have hs : ∀ σ, χ (s σ) = σ := fun σ => hsec σ
  have hmkα : orderOf (QuotientGroup.mk (s := OuterAutomorphisms.inner
      (ReeTag.G2.reeGamma K a)) α) = p := by
    have h1 : orderOf (QuotientGroup.mk (s := OuterAutomorphisms.inner
        (ReeTag.G2.reeGamma K a)) α) ∣ p := by
      rw [← hα]
      exact orderOf_map_dvd (QuotientGroup.mk' (OuterAutomorphisms.inner _)) α
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exfalso
      rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h
      exact hαout h
    · exact h
  have hR : IsPGroup 3 χ.ker := hker ▸ hR3
  obtain ⟨hσp, o, ho⟩ := exists_conj_eq_section_of_ker_isPGroup hcomm χ hp (by omega) hR s hs
    (QuotientGroup.mk α) hmkα
  set σ := χ (QuotientGroup.mk (s := OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a)) α)
    with hσdef
  have hpf : p ∣ 2 * a + 1 := by
    rw [← hσp, ← hcardAut]
    exact orderOf_dvd_natCard σ
  refine ⟨hpf, ?_⟩
  obtain ⟨δ₁, rfl⟩ := QuotientGroup.mk_surjective o
  set σh := ReeTag.G2.reeGammaFieldAut K a σ with hσh
  have hmk : (QuotientGroup.mk (s := OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a))
      (δ₁ * α * δ₁⁻¹)) = QuotientGroup.mk σh := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact ho
  have hin : δ₁ * α * δ₁⁻¹ * σh⁻¹ ∈ OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a) := by
    have h1 := QuotientGroup.eq.1 hmk.symm
    have h2 := (innerNormal (ReeTag.G2.reeGamma K a)).conj_mem _ h1 σh
    have e : σh * (σh⁻¹ * (δ₁ * α * δ₁⁻¹)) * σh⁻¹ = δ₁ * α * δ₁⁻¹ * σh⁻¹ := by group
    rwa [e] at h2
  obtain ⟨x, hx⟩ := hin
  have hβ₁ : δ₁ * α * δ₁⁻¹ = MulAut.conj x * σh := by
    rw [hx]
    group
  have hβ₁p : (MulAut.conj x * σh) ^ p = 1 := by
    rw [← hβ₁, conj_pow, ← hα, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  obtain ⟨δ₂, hfin, hk, hfixed⟩ :=
    small_Ree_coset_descent_data ha hK hp (by omega) σ hσp x hβ₁p
  refine ⟨δ₂ * δ₁, σ, hσp, ?_, hk, hfixed⟩
  rw [show δ₂ * δ₁ * α * (δ₂ * δ₁)⁻¹ = δ₂ * (δ₁ * α * δ₁⁻¹) * δ₂⁻¹ by group, hβ₁, hfin]

end CFSG.RankThree
