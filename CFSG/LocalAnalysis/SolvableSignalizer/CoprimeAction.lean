module

public import CFSG.LocalAnalysis.SolvableSignalizer.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeFixedFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.ProductFixedPoints

public section

namespace CFSG.SolvableSignalizer

open scoped Pointwise

section Distrib

variable {A G : Type*} [Group A] [Group G]

abbrev actionAsDistrib (α : A →* MulAut G) : MulDistribMulAction A G :=
  MulDistribMulAction.compHom G α

abbrev actionFixedAll (α : A →* MulAut G) : Subgroup G :=
  fixedBySubgroup α ⊤

@[expose]
def actionFixedAllIn (α : A →* MulAut G) (H : Subgroup G) : Subgroup G :=
  H ⊓ actionFixedAll α

private theorem isInvariant_iff_forall {α : A →* MulAut G} {H : Subgroup G} :
    IsInvariant α H ↔ ∀ a g, α a g ∈ H ↔ g ∈ H := by
  refine ⟨fun h a g => ?_, fun h a => ?_⟩
  · have key : α a g ∈ H.map (α a).toMonoidHom ↔ g ∈ H :=
      Subgroup.mem_map_iff_mem (α a).injective
    rwa [h a] at key
  · ext g
    refine ⟨?_, fun hg => ⟨α a⁻¹ g, (h a⁻¹ g).mpr hg, by simp⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact (h a x).mpr hx

private theorem apply_mem_of_isInvariant {α : A →* MulAut G} {H : Subgroup G}
    (hH : IsInvariant α H) (a : A) {g : G} (hg : g ∈ H) : α a g ∈ H :=
  (isInvariant_iff_forall.mp hH a g).mpr hg

theorem IsInvariant.toFeitThompson (α : A →* MulAut G) (H : Subgroup G)
    (h : IsInvariant α H) :
    letI := actionAsDistrib α
    CFSG.IsInvariant A G H :=
  letI := actionAsDistrib α
  ⟨fun a g => (isInvariant_iff_forall.mp h a g).symm⟩

theorem IsInvariant.of_feitThompson (α : A →* MulAut G) (H : Subgroup G)
    (h : letI := actionAsDistrib α; CFSG.IsInvariant A G H) :
    IsInvariant α H :=
  let := actionAsDistrib α
  isInvariant_iff_forall.mpr fun a g => (h.invariant a g).symm

private theorem fixedPoints_eq_fixedBySubgroup (α : A →* MulAut G) (B : Subgroup A) :
    letI := actionAsDistrib α
    CFSG.fixedPointSubgroup B G = fixedBySubgroup α B := by
  let := actionAsDistrib α
  ext g
  rw [FixedPoints.mem_subgroup, mem_fixedBySubgroup]
  exact ⟨fun h b hb => h ⟨b, hb⟩, fun h b => h b b.2⟩

private theorem actionFixedAll_eq_fixedPointSubgroup (α : A →* MulAut G) :
    actionFixedAll α = (letI := actionAsDistrib α; CFSG.fixedPointSubgroup A G) := by
  ext g
  simp only [actionFixedAll, mem_fixedBySubgroup, Subgroup.mem_top, forall_true_left]
  rfl

private theorem fixedBySubgroup_zpowers (α : A →* MulAut G) (a : A) :
    fixedBySubgroup α (Subgroup.zpowers a) = fixedSubgroup α a := by
  ext g
  simp only [mem_fixedBySubgroup, mem_fixedSubgroup, Subgroup.forall_mem_zpowers, map_zpow]
  exact ⟨fun h => by simpa using h 1, fun h k => MulAction.mem_fixedBy_zpow (G := MulAut G) h k⟩

end Distrib

section SylowHall

variable {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]

private theorem coprime_card_of_isPGroup {p : ℕ} (hp : p.Prime) (hA : IsPGroup p A) {n : ℕ}
    (hn : ¬ p ∣ n) : Nat.Coprime (Nat.card A) n := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  rw [hk]
  exact (hp.coprime_iff_not_dvd.mpr hn).pow_left k

theorem exists_sylow_isInvariant
    (p : ℕ) (hp : p.Prime) (hA : IsPGroup p A) (α : A →* MulAut G)
    (q : ℕ) (hq : q.Prime)
    (hcop : ¬ p ∣ Nat.card G) :
    ∃ P : Sylow q G, IsInvariant α (P : Subgroup G) := by
  let := actionAsDistrib α
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (IsPGroup p A) := ⟨hA⟩
  obtain ⟨P, hP⟩ := CFSG.exists_invariant_sylow (A := A) (G := G) (p := p) (q := q)
    (hp.coprime_iff_not_dvd.mpr hcop)
  exact ⟨P, IsInvariant.of_feitThompson α _ hP⟩

theorem exists_sylow_isInvariant_le {A G : Type*} [Group A] [Group G] [Finite A]
    [Finite G] (p : ℕ) (hp : p.Prime) (hA : IsPGroup p A) (α : A →* MulAut G)
    (q : ℕ) (hq : q.Prime)
    (hcop : ¬ p ∣ Nat.card G)
    (U : Subgroup G) (hU : IsInvariant α U) (hUq : IsPGroup q U) :
    ∃ P : Sylow q G, IsInvariant α (P : Subgroup G) ∧ U ≤ P := by
  let := actionAsDistrib α
  obtain ⟨P, hUP, hP⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing
    p q hp hq hA (hp.coprime_iff_not_dvd.mpr hcop) U hUq
    fun a _ hg => apply_mem_of_isInvariant hU a hg
  refine ⟨P, fun a => ?_, hUP⟩
  have h := congrArg (fun P : Sylow q G => (P : Subgroup G)) (hP a)
  rw [Sylow.pointwise_smul_def] at h
  exact h

private theorem exists_mem_actionFixedAll_conjugate_eq
    (p : ℕ) (hp : p.Prime) (hA : IsPGroup p A) (α : A →* MulAut G)
    (hcop : ¬ p ∣ Nat.card G) (hsol : Group.IsSolvable G)
    (π : Set Nat.Primes) (P Q : Subgroup G)
    (hP : CFSG.IsHallSubgroup π P) (hQ : CFSG.IsHallSubgroup π Q)
    (hPi : IsInvariant α P) (hQi : IsInvariant α Q) :
    ∃ c : G, c ∈ actionFixedAll α ∧ conjugate P c = Q := by
  let := actionAsDistrib α
  obtain ⟨g, hgfix, hgeq⟩ :=
    CFSG.exists_mem_fixedPointSubgroup_eq_map_conj_of_isHallSubgroup_of_isInvariant
      (G := G) (A := A) hsol (coprime_card_of_isPGroup hp hA hcop) π P Q hP hQ
      (IsInvariant.toFeitThompson α P hPi) (IsInvariant.toFeitThompson α Q hQi)
  refine ⟨g⁻¹, ?_, ?_⟩
  · rw [actionFixedAll_eq_fixedPointSubgroup]
    exact Subgroup.inv_mem _ hgfix
  · simp only [conjugate, inv_inv]
    exact hgeq.symm

theorem exists_isHallSubgroup_isInvariant_le
    (p : ℕ) (hp : p.Prime) (hA : IsPGroup p A) (α : A →* MulAut G)
    (hcop : ¬ p ∣ Nat.card G)
    (hsol : Group.IsSolvable G)
    (π : Set Nat.Primes) (_hpπ : (⟨p, hp⟩ : Nat.Primes) ∉ π)
    (U : Subgroup G) (hU : IsInvariant α U) (hUπ : CFSG.IsPiSubgroup π U) :
    ∃ P : Subgroup G, CFSG.IsHallSubgroup π P ∧ IsInvariant α P ∧ U ≤ P := by
  let := actionAsDistrib α
  obtain ⟨P, hP, hPi, hUP⟩ := CFSG.exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := A) hsol (coprime_card_of_isPGroup hp hA hcop) π U hUπ
    (IsInvariant.toFeitThompson α U hU)
  exact ⟨P, hP, IsInvariant.of_feitThompson α P hPi, hUP⟩

theorem iInf_invariant_isHallSubgroup_largest
    (p : ℕ) (hp : p.Prime) (hA : IsPGroup p A) (α : A →* MulAut G)
    (hcop : ¬ p ∣ Nat.card G)
    (hsol : Group.IsSolvable G)
    (π : Set Nat.Primes) (hpπ : (⟨p, hp⟩ : Nat.Primes) ∉ π) :
    let R : Subgroup G := ⨅ (P : Subgroup G) (_ : CFSG.IsHallSubgroup π P)
      (_ : IsInvariant α P), P
    IsInvariant α R ∧ CFSG.IsPiSubgroup π R ∧
      actionFixedAll α ≤ Subgroup.normalizer (R : Set G) ∧
      ∀ U : Subgroup G, IsInvariant α U → CFSG.IsPiSubgroup π U →
        actionFixedAll α ≤ Subgroup.normalizer (U : Set G) → U ≤ R := by
  intro R
  have memR : ∀ x, x ∈ R ↔ ∀ (P : Subgroup G) (_ : CFSG.IsHallSubgroup π P)
      (_ : IsInvariant α P), x ∈ P := by
    intro x
    simp only [R, Subgroup.mem_iInf]
  obtain ⟨P₀, hP₀hall, hP₀inv⟩ :
      ∃ P : Subgroup G, CFSG.IsHallSubgroup π P ∧ IsInvariant α P := by
    let := actionAsDistrib α
    obtain ⟨P, hP, hPi⟩ := CFSG.exists_isHallSubgroup_isInvariant
      (A := A) (G := G) hsol (coprime_card_of_isPGroup hp hA hcop) π
    exact ⟨P, hP, IsInvariant.of_feitThompson α P hPi⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [isInvariant_iff_forall]
    intro a x
    rw [memR, memR]
    exact forall₃_congr fun P _ hPi => isInvariant_iff_forall.mp hPi a x
  · exact CFSG.IsPiSubgroup.of_le
      (le_trans (iInf_le _ P₀) (le_trans (iInf_le _ hP₀hall) (iInf_le _ hP₀inv)))
      hP₀hall.p_in_pi_of_p_dvd_card
  · apply Subgroup.le_normalizer_iff.mpr
    intro c hc k hk
    have hcC : ∀ a : A, α a c = c := fun a =>
      (mem_fixedBySubgroup α ⊤ c).mp hc a (Subgroup.mem_top a)
    rw [memR]
    intro P hP hPi
    have hP'hall : CFSG.IsHallSubgroup π (conjugate P c) := by
      simpa [conjugate] using hP.map_mulAut (MulAut.conj c⁻¹)
    have hk' : k ∈ conjugate P c :=
      (memR k).mp hk _ hP'hall (hPi.map_conj fun a => by rw [map_inv, hcC a])
    rwa [mem_conjugate_iff] at hk'
  · intro U hUi hUπ hUnorm x hx
    obtain ⟨P, hPhall, hPi, hUP⟩ :=
      exists_isHallSubgroup_isInvariant_le p hp hA α hcop hsol π hpπ U hUi hUπ
    rw [memR]
    intro Q hQhall hQinv
    obtain ⟨c, hcC, hcQ⟩ :=
      exists_mem_actionFixedAll_conjugate_eq p hp hA α hcop hsol π P Q hPhall hQhall
        hPi hQinv
    have hUc_eq : conjugate U c = U := by
      refine le_antisymm (fun y hy => ?_) fun y hy => ?_
      · rw [mem_conjugate_iff] at hy
        have h := Subgroup.le_normalizer_iff.mp hUnorm c⁻¹ (inv_mem hcC) (c * y * c⁻¹) hy
        simpa [mul_assoc] using h
      · rw [mem_conjugate_iff]
        exact Subgroup.le_normalizer_iff.mp hUnorm c hcC y hy
    have hle : U ≤ Q := by
      rw [← hUc_eq, ← hcQ]
      exact Subgroup.map_mono hUP
    exact hle hx

theorem mul_inter_actionFixedAll_eq {A G : Type*} [Group A] [Group G] [Finite A]
    [Finite G] (p : ℕ) (hp : p.Prime) (hA : IsPGroup p A) (α : A →* MulAut G)
    (X Y : Subgroup G) (hX : IsInvariant α X) (hY : IsInvariant α Y)
    (hcop : ¬ p ∣ Nat.card (X ⊓ Y : Subgroup G)) :
    ((X : Set G) * (Y : Set G)) ∩ (actionFixedAll α : Set G) =
      (actionFixedAllIn α X : Set G) * (actionFixedAllIn α Y : Set G) := by
  let := actionAsDistrib α
  apply Set.Subset.antisymm
  · rintro g ⟨⟨x, hx, y, hy, rfl⟩, hfix⟩
    have hfix' : ∀ a : A, α a (x * y) = x * y :=
      fun a => (mem_fixedBySubgroup α ⊤ (x * y)).mp hfix a (Subgroup.mem_top a)
    obtain ⟨x', hx'X, y', hy'Y, hprod', hx'fix, hy'fix⟩ :=
      CFSG.SignalizerFunctor.Helpers.fixed_product_decomposition p hp A hA G X Y
        (fun a _ hg => apply_mem_of_isInvariant hX a hg)
        (fun a _ hg => apply_mem_of_isInvariant hY a hg)
        (hp.coprime_iff_not_dvd.mpr hcop) (x * y) hfix' ⟨x, hx, y, hy, rfl⟩
    exact ⟨x', ⟨hx'X, (mem_fixedBySubgroup α ⊤ x').mpr fun b _ => hx'fix b⟩,
      y', ⟨hy'Y, (mem_fixedBySubgroup α ⊤ y').mpr fun b _ => hy'fix b⟩, hprod'⟩
  · rintro _ ⟨x, ⟨hxX, hxf⟩, y, ⟨hyY, hyf⟩, rfl⟩
    refine ⟨⟨x, hxX, y, hyY, rfl⟩, (mem_fixedBySubgroup α ⊤ (x * y)).mpr fun b hb => ?_⟩
    rw [map_mul, (mem_fixedBySubgroup α ⊤ x).mp hxf b hb, (mem_fixedBySubgroup α ⊤ y).mp hyf b hb]

end SylowHall

section Generation

variable {A G : Type*} [CommGroup A] [Group G] [Finite A] [Finite G]

theorem iSup_fixedSubgroup_eq_top
    (p : ℕ) (hp : p.Prime) [CFSG.IsElementaryAbelian p A]
    (α : A →* MulAut G)
    (hcard : p ^ 2 ≤ Nat.card A)
    (hcop : ¬ p ∣ Nat.card G) :
    (⨆ (a : A) (_ : a ≠ 1), fixedSubgroup α a) = ⊤ := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (IsPGroup p A) := ⟨CFSG.IsElementaryAbelian.isPGroup p A⟩
  let := actionAsDistrib α
  have hnotcyc : ¬ IsCyclic A := by
    intro _
    have hdvd : Nat.card A ∣ p := by
      rw [← IsCyclic.exponent_eq_card]
      exact CFSG.IsElementaryAbelian.exponent_dvd_p p A
    have := hcard.trans (Nat.le_of_dvd hp.pos hdvd)
    nlinarith [hp.two_le]
  have h := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := G) (A := A) (p := p) (hp.coprime_iff_not_dvd.mpr hcop) (hncyc := hnotcyc)
  simpa only [fixedPoints_eq_fixedBySubgroup, fixedBySubgroup_zpowers] using h

theorem iSup_fixedBySubgroup_index_eq_top
    (p : ℕ) (hp : p.Prime) [CFSG.IsElementaryAbelian p A]
    (α : A →* MulAut G)
    [Nontrivial A]
    (hcop : ¬ p ∣ Nat.card G) :
    (⨆ (B : Subgroup A) (_ : B.index = p), fixedBySubgroup α B) = ⊤ := by
  let := actionAsDistrib α
  let : Fact p.Prime := ⟨hp⟩
  have hAp : IsPGroup p A := CFSG.IsElementaryAbelian.isPGroup p A
  rw [eq_top_iff]
  by_cases hcyc : IsCyclic A
  ·
    have hbot : (⊥ : Subgroup A).index = p := by
      rw [Subgroup.index_bot, ← IsCyclic.exponent_eq_card,
        CFSG.IsElementaryAbelian.exponent_eq_prime (p := p) (G := A)]
    have hfix : fixedBySubgroup α (⊥ : Subgroup A) = ⊤ := by
      ext g
      simp
    rw [← hfix]
    exact le_iSup₂_of_le ⊥ hbot le_rfl
  ·
    let : Fact (IsPGroup p A) := ⟨hAp⟩
    rw [← CFSG.iSup_fixedPointSubgroup_cyclicQuot_eq_top_of_noncyclic_abelian_pGroup_action
      (G := G) (A := A) p (hp.coprime_iff_not_dvd.mpr hcop) hcyc]
    refine iSup₂_le fun Y hYcyc => ?_
    rw [fixedPoints_eq_fixedBySubgroup]
    by_cases hYtop : Y = ⊤
    · subst hYtop
      obtain ⟨B, hB, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup A)).resolve_left bot_ne_top
      refine le_iSup₂_of_le B (hAp.isCoatom_iff_index_eq_prime.mp hB) fun g hg => ?_
      rw [mem_fixedBySubgroup] at hg ⊢
      exact fun b _ => hg b (Subgroup.mem_top b)
    · have hYindex : Y.index = p := by
        rw [Subgroup.index_eq_card]
        have : IsCyclic (A ⧸ Y) := hYcyc
        have hexp : Monoid.exponent (A ⧸ Y) ∣ p := by
          rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
          intro x
          obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Y x
          rw [← map_pow,
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (CFSG.IsElementaryAbelian.exponent_dvd_p p A) a, map_one]
        have hdvd : Nat.card (A ⧸ Y) ∣ p := by
          rwa [← IsCyclic.exponent_eq_card]
        refine (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left fun h1 => ?_
        have : Nontrivial (A ⧸ Y) := QuotientGroup.nontrivial_iff.mpr hYtop
        exact not_subsingleton (A ⧸ Y) (Nat.card_eq_one_iff_unique.mp h1).1
      exact le_iSup₂_of_le Y hYindex le_rfl

theorem mul_eq_univ_of_fixedSubgroup_eq_mul
    (p : ℕ) (hp : p.Prime) [CFSG.IsElementaryAbelian p A]
    (α : A →* MulAut G)
    (hcard : p ^ 2 ≤ Nat.card A)
    (hcop : ¬ p ∣ Nat.card G)
    (X Y : Subgroup G) (hX : IsInvariant α X) (hY : IsInvariant α Y)
    (hnorm : actionFixedAll α ≤ Subgroup.normalizer (X : Set G))
    (hlocal : ∀ a : A, a ≠ 1 →
      (fixedSubgroup α a : Set G) =
        (X ⊓ fixedSubgroup α a : Subgroup G) * (Y ⊓ fixedSubgroup α a : Subgroup G)) :
    (X : Set G) * (Y : Set G) = Set.univ := by
  let := actionAsDistrib α
  let : Fact p.Prime := ⟨hp⟩
  have hexp : ∀ x : A, x ^ p = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p p A) x
  have hlocal' : ∀ B : Subgroup A, Nat.card B = p →
      ∀ g ∈ FixedPoints.subgroup B G,
        ∃ x ∈ X ⊓ FixedPoints.subgroup B G, ∃ y ∈ Y ⊓ FixedPoints.subgroup B G, x * y = g := by
    intro B hB g hg
    have hne : B ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hB
      exact hp.ne_one hB.symm
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have ha_ne : (a : A) ≠ 1 := fun h => ha (Subtype.ext h)
    have hgen : Subgroup.zpowers (a : A) = B := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a.2) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime (hexp a) ha_ne, hB]
    have hCG : FixedPoints.subgroup B G = fixedSubgroup α a := by
      have h := fixedBySubgroup_zpowers α (a : A)
      rw [hgen] at h
      exact (fixedPoints_eq_fixedBySubgroup α B).trans h
    rw [hCG] at hg ⊢
    have hmem : g ∈ (fixedSubgroup α a : Set G) := hg
    rw [hlocal a ha_ne] at hmem
    exact hmem
  have hmain := CFSG.SignalizerFunctor.Helpers.coprime_fixed_factorization
    (ActorType := A) (GroupType := G) p hp hexp hcard (hp.coprime_iff_not_dvd.mpr hcop) X Y
    (fun a _ hg => apply_mem_of_isInvariant hX a hg)
    (fun a _ hg => apply_mem_of_isInvariant hY a hg)
    (by rwa [actionFixedAll_eq_fixedPointSubgroup α] at hnorm) hlocal'
  simpa only [CFSG.SignalizerFunctor.Helpers.subgroupProduct] using hmain

end Generation

end CFSG.SolvableSignalizer
