module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.RingTheory.PrimitiveIdempotent

public section

namespace CFSG.RankThree.GF2n.Stroth80

section CommCore

variable {K : Type} [Field K] {X : Type} [AddCommGroup X] [Module K X]
  {R : Type} [CommRing R] [Algebra K R] [Module R X] [IsScalarTower K R X]
  {Γ : Type} [Group Γ]

theorem commCore_isReduced [Finite R] [Nontrivial X] (ρ : Γ →* (X ≃ₗ[K] X))
    (σ : Γ →* (R ≃ₐ[K] R)) (hcomp : ∀ (g : Γ) (c : R) (x : X), ρ g (c • x) = σ g c • ρ g x)
    (hirr : ∀ S : Submodule K X, (∀ g : Γ, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hfaith : ∀ c : R, (∀ x : X, c • x = 0) → c = 0) : IsReduced R := by
  classical
  haveI : IsArtinianRing R := inferInstance
  haveI : Nontrivial R := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    refine ⟨⟨0, 1, fun h => hab ?_⟩⟩
    have h1 : ∀ x : X, x = 0 := fun x => by
      have : (1 : R) • x = (0 : R) • x := by rw [h]
      simpa using this
    rw [h1 a, h1 b]
  set I : Ideal R := nilradical R with hI
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_nilradical (R := R)
  have hex : ∃ m : ℕ, I ^ m = ⊥ := ⟨m, hm⟩
  let T : Submodule K X :=
    { carrier := {y | ∀ c ∈ I, c • y = 0}
      add_mem' := fun {a b} ha hb c hc => by rw [smul_add, ha c hc, hb c hc, add_zero]
      zero_mem' := fun c _ => smul_zero c
      smul_mem' := fun a y hy c hc => by rw [smul_comm, hy c hc, smul_zero] }
  have hnil : ∀ (g : Γ) (c : R), c ∈ I → σ g c ∈ I := by
    intro g c hc
    exact (IsNilpotent.map (mem_nilradical.mp hc) (σ g)) |> fun h => mem_nilradical.mpr h
  have hTinv : ∀ g : Γ, ∀ y ∈ T, ρ g y ∈ T := by
    intro g y hy c hc
    have h1 : (σ g (σ g⁻¹ c)) = c := by
      rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    have h2 := hcomp g (σ g⁻¹ c) y
    rw [h1, hy _ (hnil g⁻¹ c hc), map_zero] at h2
    exact h2.symm
  have hIbot : I = ⊥ := by
    by_contra hne
    classical
    let k := Nat.find hex
    have hk : I ^ k = ⊥ := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, Ideal.one_eq_top] at hk
      exact absurd hk top_ne_bot
    have hk1 : I ^ (k - 1) ≠ ⊥ := Nat.find_min hex (by omega)
    obtain ⟨d, hd, hd0⟩ : ∃ d ∈ I ^ (k - 1), d ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hk1 (eq_bot_iff.mpr fun d hd => by simpa using hcon d hd)
    obtain ⟨x, hx⟩ : ∃ x : X, d • x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hd0 (hfaith d hcon)
    have hdx : d • x ∈ T := by
      intro c hc
      have : c * d ∈ I ^ k := by
        rw [show k = (k - 1) + 1 by omega, pow_succ']
        exact Ideal.mul_mem_mul hc hd
      rw [hk] at this
      rw [← mul_smul, show c * d = 0 by simpa using this, zero_smul]
    rcases hirr T hTinv with hT | hT
    · exact hx (by simpa [hT] using hdx)
    · apply hne
      rw [eq_bot_iff]
      intro c hc
      have : c = 0 := hfaith c fun y => by
        have hy : y ∈ T := by rw [hT]; trivial
        exact hy c hc
      simp [this]
  exact ⟨fun c hc => by
    have : c ∈ I := mem_nilradical.mpr hc
    rw [hIbot] at this
    simpa using this⟩

theorem commCore_prim_mul_eq_zero {R : Type} [CommRing R] {p p' : R}
    (hp : TauCeti.IsPrimitiveIdempotent p) (hp' : TauCeti.IsPrimitiveIdempotent p')
    (h : p ≠ p') : p * p' = 0 := by
  have hq : IsIdempotentElem (p * p') := hp.isIdempotentElem.mul hp'.isIdempotentElem
  have h1 : (p * p') * p = p * p' := by
    rw [mul_comm p p', mul_assoc, hp.isIdempotentElem.eq]
  have h2 : p * (p * p') = p * p' := by
    rw [← mul_assoc, hp.isIdempotentElem.eq]
  have h3 : (p * p') * p' = p * p' := by rw [mul_assoc, hp'.isIdempotentElem.eq]
  have h4 : p' * (p * p') = p * p' := by
    rw [mul_comm p p', ← mul_assoc, hp'.isIdempotentElem.eq]
  rcases hp.eq_zero_or_eq hq h2 h1 with h0 | h0
  · exact h0
  · rcases hp'.eq_zero_or_eq hq h4 h3 with h0' | h0'
    · exact h0'
    · exact absurd (h0.symm.trans h0') h

theorem exists_primIdem_below {R : Type} [CommRing R] [Finite R] {e : R}
    (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    ∃ p : R, TauCeti.IsPrimitiveIdempotent p ∧ p * e = p := by
  classical
  let r : R → R → Prop := fun q q' => q * q' = q ∧ q ≠ q'
  have hwf : WellFounded r := by
    haveI : IsTrans R r := ⟨fun a b c hab hbc => by
      refine ⟨?_, ?_⟩
      · rw [← hab.1, mul_assoc, hbc.1]
      · intro hac
        subst hac
        apply hab.2
        rw [← hab.1, mul_comm, hbc.1]⟩
    haveI : Std.Irrefl r := ⟨fun a h => h.2 rfl⟩
    exact Finite.wellFounded_of_trans_of_irrefl r
  let S : Set R := {q | IsIdempotentElem q ∧ q ≠ 0 ∧ q * e = q}
  have hS : S.Nonempty := ⟨e, he, h0, he.eq⟩
  obtain ⟨p, hpS, hpmin⟩ := hwf.has_min S hS
  refine ⟨p, TauCeti.isPrimitiveIdempotent_of_eq_zero_or_eq hpS.1 hpS.2.1
    fun q hq _ hqp => ?_, hpS.2.2⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hq0, hqp'⟩ := hcon
  apply hpmin q ⟨hq, hq0, ?_⟩ ⟨hqp, hqp'⟩
  rw [← hqp, mul_assoc, hpS.2.2]

def primEquiv {R : Type} [CommRing R] (φ : R ≃+* R) :
    Equiv.Perm {p : R // TauCeti.IsPrimitiveIdempotent p} where
  toFun p := ⟨φ p.1, p.2.map φ⟩
  invFun p := ⟨φ.symm p.1, p.2.map φ.symm⟩
  left_inv p := Subtype.ext (by simp)
  right_inv p := Subtype.ext (by simp)

theorem commCore_card_prim_le [Finite R] [Module.Finite K X]
    (hfaith : ∀ c : R, (∀ x : X, c • x = 0) → c = 0) :
    Nat.card {p : R // TauCeti.IsPrimitiveIdempotent p} ≤ Module.finrank K X := by
  classical
  haveI : Finite {p : R // TauCeti.IsPrimitiveIdempotent p} := inferInstance
  letI : Fintype {p : R // TauCeti.IsPrimitiveIdempotent p} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have hex : ∀ p : {p : R // TauCeti.IsPrimitiveIdempotent p}, ∃ y : X, p.1 • y ≠ 0 := fun p => by
    by_contra hcon
    push Not at hcon
    exact p.2.ne_zero (hfaith p.1 hcon)
  choose y hy using hex
  let v : {p : R // TauCeti.IsPrimitiveIdempotent p} → X := fun p => p.1 • y p
  have hv : ∀ p p' : {p : R // TauCeti.IsPrimitiveIdempotent p},
      p'.1 • v p = if p = p' then v p else 0 := by
    intro p p'
    by_cases h : p = p'
    · subst h
      simp only [if_true, v]
      rw [← mul_smul, p.2.isIdempotentElem.eq]
    · rw [if_neg h]
      simp only [v]
      rw [← mul_smul, mul_comm,
        commCore_prim_mul_eq_zero p.2 p'.2 (fun h' => h (Subtype.ext h')), zero_smul]
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 := congrArg (fun z => i.1 • z) hc
    simp only [Finset.smul_sum, smul_zero] at h1
    have h2 : ∀ j : {p : R // TauCeti.IsPrimitiveIdempotent p},
        i.1 • (c j • v j) = if j = i then c j • v j else 0 := by
      intro j
      rw [smul_comm, hv j i]
      split_ifs <;> simp
    simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    rcases smul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h (by simp only [v]; exact hy i)
  exact hli.fintype_card_le_finrank

theorem commCore_sigma_one (ρ : Γ →* (X ≃ₗ[K] X)) (σ : Γ →* (R ≃ₐ[K] R))
    (hcomp : ∀ (g : Γ) (c : R) (x : X), ρ g (c • x) = σ g c • ρ g x)
    (hfaith : ∀ c : R, (∀ x : X, c • x = 0) → c = 0) (g : Γ) (hg : ρ g = 1) : σ g = 1 := by
  refine AlgEquiv.ext fun c => ?_
  show σ g c = c
  refine (sub_eq_zero.mp (hfaith (σ g c - c) fun x => ?_))
  have h1 := hcomp g c x
  rw [hg] at h1
  have h2 : c • x = σ g c • x := by simpa using h1
  rw [sub_smul, ← h2, sub_self]

theorem commCore_prim_subsingleton [Finite R] [Module.Finite K X]
    (ρ : Γ →* (X ≃ₗ[K] X)) (σ : Γ →* (R ≃ₐ[K] R))
    (hcomp : ∀ (g : Γ) (c : R) (x : X), ρ g (c • x) = σ g c • ρ g x)
    (hirr : ∀ S : Submodule K X, (∀ g : Γ, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hfaith : ∀ c : R, (∀ x : X, c • x = 0) → c = 0)
    (hperm : ∀ (ι : Type) [Fintype ι], Fintype.card ι ≤ Module.finrank K X →
      ∀ h : Γ →* Equiv.Perm ι, (∀ g : Γ, ρ g = 1 → h g = 1) → h = 1) :
    Subsingleton {p : R // TauCeti.IsPrimitiveIdempotent p} := by
  classical
  letI : Fintype {p : R // TauCeti.IsPrimitiveIdempotent p} := Fintype.ofFinite _
  let h : Γ →* Equiv.Perm {p : R // TauCeti.IsPrimitiveIdempotent p} :=
    MonoidHom.mk' (fun g => primEquiv (σ g).toRingEquiv) (fun a b => by
      ext p
      simp [primEquiv])
  have hcard : Fintype.card {p : R // TauCeti.IsPrimitiveIdempotent p} ≤ Module.finrank K X := by
    have := commCore_card_prim_le (K := K) (X := X) hfaith
    rwa [Nat.card_eq_fintype_card] at this
  have h1 : h = 1 := hperm _ hcard h (fun g hg => by
    have := commCore_sigma_one ρ σ hcomp hfaith g hg
    show primEquiv (σ g).toRingEquiv = 1
    rw [this]
    exact Equiv.ext fun p => Subtype.ext rfl)
  have hfix : ∀ (g : Γ) (p : {p : R // TauCeti.IsPrimitiveIdempotent p}), σ g p.1 = p.1 := by
    intro g p
    have := congrArg (fun f => (f g p).1) h1
    simpa [h, primEquiv] using this
  let S : {p : R // TauCeti.IsPrimitiveIdempotent p} → Submodule K X := fun p =>
    { carrier := {y | ∃ x : X, y = p.1 • x}
      add_mem' := fun {a b} ha hb => by
        obtain ⟨x, rfl⟩ := ha
        obtain ⟨x', rfl⟩ := hb
        exact ⟨x + x', by rw [smul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := fun a y hy => by
        obtain ⟨x, rfl⟩ := hy
        exact ⟨a • x, by rw [smul_comm]⟩ }
  have hS : ∀ p : {p : R // TauCeti.IsPrimitiveIdempotent p}, S p = ⊤ := by
    intro p
    rcases hirr (S p) (fun g y hy => by
      obtain ⟨x, rfl⟩ := hy
      exact ⟨ρ g x, by rw [hcomp, hfix]⟩) with hb | ht
    · exfalso
      obtain ⟨x, hx⟩ : ∃ x : X, p.1 • x ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact p.2.ne_zero (hfaith p.1 hcon)
      have : p.1 • x ∈ S p := ⟨x, rfl⟩
      rw [hb] at this
      exact hx this
    · exact ht
  refine ⟨fun p p' => ?_⟩
  by_contra hne
  have h0 : p.1 * p'.1 = 0 := commCore_prim_mul_eq_zero p.2 p'.2 (fun h' => hne (Subtype.ext h'))
  apply p.2.ne_zero
  refine hfaith p.1 fun y => ?_
  have : y ∈ S p' := by rw [hS p']; trivial
  obtain ⟨x, rfl⟩ := this
  rw [← mul_smul, h0, zero_smul]

theorem commCore_idem [Finite R] [Module.Finite K X]
    (ρ : Γ →* (X ≃ₗ[K] X)) (σ : Γ →* (R ≃ₐ[K] R))
    (hcomp : ∀ (g : Γ) (c : R) (x : X), ρ g (c • x) = σ g c • ρ g x)
    (hirr : ∀ S : Submodule K X, (∀ g : Γ, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hfaith : ∀ c : R, (∀ x : X, c • x = 0) → c = 0)
    (hperm : ∀ (ι : Type) [Fintype ι], Fintype.card ι ≤ Module.finrank K X →
      ∀ h : Γ →* Equiv.Perm ι, (∀ g : Γ, ρ g = 1 → h g = 1) → h = 1) :
    ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  classical
  intro e he
  by_contra hcon
  push Not at hcon
  obtain ⟨he0, he1⟩ := hcon
  have hsub := commCore_prim_subsingleton ρ σ hcomp hirr hfaith hperm
  have he' : IsIdempotentElem (1 - e) := he.one_sub
  have he'0 : (1 - e) ≠ 0 := fun h => he1 (sub_eq_zero.mp h).symm
  obtain ⟨p, hp, hpe⟩ := exists_primIdem_below he he0
  obtain ⟨p', hp', hpe'⟩ := exists_primIdem_below he' he'0
  have h0 : p * p' = 0 := by
    calc p * p' = (p * e) * (p' * (1 - e)) := by rw [hpe, hpe']
      _ = (p * p') * (e * (1 - e)) := by ring
      _ = 0 := by rw [mul_sub, mul_one, he.eq, sub_self, mul_zero]
  have hne : p ≠ p' := by
    intro h
    subst h
    exact hp.ne_zero (hp.isIdempotentElem.eq.symm.trans h0)
  exact hne (congrArg Subtype.val (hsub.elim ⟨p, hp⟩ ⟨p', hp'⟩))

theorem isField_of_finite_reduced_idem {R : Type} [CommRing R] [Finite R] [Nontrivial R]
    [IsReduced R] (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : IsField R := by
  classical
  haveI : IsArtinianRing R := inferInstance
  have hsub : ∀ I J : MaximalSpectrum R, I = J := by
    intro I J
    by_contra hne
    haveI := I.isMaximal
    haveI := J.isMaximal
    let e := IsArtinianRing.equivPi R
    let ind : (K : MaximalSpectrum R) → R ⧸ K.asIdeal :=
      Pi.single (M := fun K : MaximalSpectrum R => R ⧸ K.asIdeal) I 1
    let E : R := e.symm ind
    have heE : e E = ind := e.apply_symm_apply ind
    have hind : IsIdempotentElem ind := by
      show ind * ind = ind
      simp only [ind]
      rw [← Pi.single_mul, mul_one]
    have hE : IsIdempotentElem E := by
      apply e.injective
      show e (E * E) = e E
      rw [map_mul, heE]
      exact hind
    rcases h E hE with h0 | h1
    · have h2 : ind = 0 := by rw [← heE, h0, map_zero]
      have h3 := congrFun h2 I
      simp only [ind, Pi.single_eq_same, Pi.zero_apply] at h3
      exact one_ne_zero h3
    · have h2 : ind = 1 := by rw [← heE, h1, map_one]
      have h3 := congrFun h2 J
      simp only [ind, Pi.one_apply] at h3
      rw [Pi.single_eq_of_ne (fun h' => hne h'.symm)] at h3
      exact zero_ne_one h3
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  haveI : IsLocalRing R := IsLocalRing.of_unique_max_ideal ⟨M, hM, fun N hN =>
    congrArg MaximalSpectrum.asIdeal (hsub ⟨N, hN⟩ ⟨M, hM⟩)⟩
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing R

theorem commCore_trivial [Finite R] [Module.Finite K X] [Nontrivial X]
    (ρ : Γ →* (X ≃ₗ[K] X)) (σ : Γ →* (R ≃ₐ[K] R))
    (hcomp : ∀ (g : Γ) (c : R) (x : X), ρ g (c • x) = σ g c • ρ g x)
    (hirr : ∀ S : Submodule K X, (∀ g : Γ, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hfaith : ∀ c : R, (∀ x : X, c • x = 0) → c = 0)
    (hperm : ∀ (ι : Type) [Fintype ι], Fintype.card ι ≤ Module.finrank K X →
      ∀ h : Γ →* Equiv.Perm ι, (∀ g : Γ, ρ g = 1 → h g = 1) → h = 1)
    (hab : ∀ (C : Type) [Group C] [IsCyclic C] (h : Γ →* C), (∀ g : Γ, ρ g = 1 → h g = 1) →
      h = 1) :
    ∀ g : Γ, σ g = 1 := by
  classical
  haveI : IsReduced R := commCore_isReduced ρ σ hcomp hirr hfaith
  haveI : Nontrivial R := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    refine ⟨⟨0, 1, fun h => hab ?_⟩⟩
    have h1 : ∀ x : X, x = 0 := fun x => by
      have : (1 : R) • x = (0 : R) • x := by rw [h]
      simpa using this
    rw [h1 a, h1 b]
  have hfield : IsField R :=
    isField_of_finite_reduced_idem (commCore_idem ρ σ hcomp hirr hfaith hperm)
  letI : Field R := hfield.toField
  intro g
  have := hab (R ≃ₐ[K] R) σ (fun g hg => commCore_sigma_one ρ σ hcomp hfaith g hg)
  exact DFunLike.congr_fun this g

end CommCore

end CFSG.RankThree.GF2n.Stroth80
