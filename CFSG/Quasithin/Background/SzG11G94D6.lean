module

public import CFSG.Quasithin.Background.SzG11G94D6Ctx
public import CFSG.Quasithin.Background.SzG11G94Solv
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6D

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzG11G94

open CFSG.Quasithin.G11 CFSG.Open CFSG.Quasithin.SzN31 CFSG.Quasithin.SzN31.SmD6
open scoped Pointwise

section Orbits

theorem fix_of_small_orbit {G X : Type*} [Group G] [MulAction G X] {γ : G} {q : ℕ}
    (hq : q.Prime) (h5 : 5 ≤ q) (hγ : orderOf γ = q) {x : X} (S : Set X) (hS : S.ncard ≤ 3)
    (hSf : S.Finite) (hmem : ∀ k : ℕ, γ ^ k • x ∈ S) : γ • x = x := by
  classical
  have hcard : Nat.card S ≤ 3 := by rw [Nat.card_coe_set_eq]; exact hS
  have : Finite S := hSf.to_subtype
  let f : Fin 4 → S := fun k => ⟨γ ^ (k : ℕ) • x, hmem k⟩
  have : Fintype S := Fintype.ofFinite S
  obtain ⟨s, t, hst, hfst⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
  have hfst' : γ ^ (s : ℕ) • x = γ ^ (t : ℕ) • x := congrArg Subtype.val hfst
  have key : ∀ s t : Fin 4, (s : ℕ) < t → γ ^ (s : ℕ) • x = γ ^ (t : ℕ) • x → γ • x = x := by
    intro s t hlt h
    set n := (t : ℕ) - s with hn
    have hn1 : 1 ≤ n := by omega
    have hn3 : n ≤ 3 := by omega
    have hts : (t : ℕ) = s + n := by omega
    have hfix : γ ^ n • x = x := by
      have : γ ^ (s : ℕ) • (γ ^ n • x) = γ ^ (s : ℕ) • x := by
        rw [← mul_smul, ← pow_add, ← hts]
        exact h.symm
      exact MulAction.injective (γ ^ (s : ℕ)) this
    have hcop : Nat.Coprime n q := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => ?_)
      have := Nat.le_of_dvd (by omega) hd
      omega
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
    have hpow : ∀ j : ℕ, γ ^ (n * j) • x = x := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [mul_add, mul_one, pow_add, mul_smul, hfix, ih]
    have hγu : γ ^ (n * u) = γ := by
      rw [← pow_mod_orderOf, hγ, hu, pow_one]
    have := hpow u
    rwa [hγu] at this
  rcases lt_trichotomy (s : ℕ) t with h | h | h
  · exact key s t h hfst'
  · exact absurd (Fin.ext h) hst
  · exact key t s h hfst'.symm

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem false_of_prime_order_of_planes {Γ P : Subgroup (GLV V)}
    {W : Fin 3 → Submodule (ZMod 2) V} (hW : ThreePlanes Γ P W)
    (hperm : ∀ g ∈ Γ, ∀ i, ∃ j, G11.conjSub g (W i) = W j) {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    {γ : ↥Γ} (hγ : orderOf γ = q) : False := by
  classical
  have hmemW : ∀ (k : ℕ) (i : Fin 3),
      γ ^ k • W i ∈ ({W 0, W 1, W 2} : Set (Submodule (ZMod 2) V)) := by
    intro k i
    obtain ⟨j, hj⟩ := hperm _ (γ ^ k).2 i
    have : γ ^ k • W i = W j := hj
    rw [this]
    fin_cases j <;> simp
  have hplane : ∀ i, γ • W i = W i := by
    intro i
    refine fix_of_small_orbit hq h5 hγ ({W 0, W 1, W 2} : Set (Submodule (ZMod 2) V)) ?_
      (Set.toFinite _) (hmemW · i)
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    simp
  have hpowW : ∀ (k : ℕ) (i : Fin 3), γ ^ k • W i = W i := by
    intro k i
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, hplane, ih]
  have hvec : ∀ i, ∀ v ∈ W i, γ • v = v := by
    intro i v hv
    by_cases hv0 : v = 0
    · subst hv0
      simp
    · have hcardW : (W i : Set V).ncard = 4 := by
        have : Module.Finite (ZMod 2) (W i) := Module.Finite.of_finite
        have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W i)
        rw [Nat.card_zmod, hW.rank i] at h1
        rw [← Nat.card_coe_set_eq]
        exact h1
      have hWi : ((W i : Set V) \ {0}).ncard = 3 := by
        rw [Set.ncard_sdiff_singleton_of_mem (by simp), hcardW]
      refine fix_of_small_orbit hq h5 hγ ((W i : Set V) \ {0}) hWi.le (Set.toFinite _) fun k => ?_
      have hk : γ ^ k • v ∈ W i := by
        have h1 : G11.conjSub ((γ ^ k : ↥Γ) : GLV V) (W i) = W i := hpowW k i
        have h2 := G11.apply_mem_conjSub (g := ((γ ^ k : ↥Γ) : GLV V)) hv
        rw [h1] at h2
        exact h2
      refine ⟨hk, ?_⟩
      intro h0
      apply hv0
      have : γ ^ k • v = γ ^ k • (0 : V) := by simpa using h0
      exact MulAction.injective (γ ^ k) this
  have hone : γ = 1 := by
    apply Subtype.ext
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨w, hw, rfl⟩ := hW.exists_decomp v
    have e0 : (γ : GLV V) (w 0) = w 0 := hvec 0 _ (hw 0)
    have e1 : (γ : GLV V) (w 1) = w 1 := hvec 1 _ (hw 1)
    have e2 : (γ : GLV V) (w 2) = w 2 := hvec 2 _ (hw 2)
    change (γ : GLV V) (w 0 + w 1 + w 2) = _
    rw [map_add, map_add, e0, e1, e2]
    rfl
  rw [hone, orderOf_one] at hγ
  exact hq.one_lt.ne hγ

end Orbits

section Planes

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {Γ A : Subgroup (GLV V)}

theorem Ctx0.isSolvable_of_planes (hC : Ctx0 Γ A) {W : Fin 3 → Submodule (ZMod 2) V}
    (hW : ThreePlanes Γ (pCoreOf 3 Γ) W) : Group.IsSolvable ↥Γ := by
  classical
  set P := pCoreOf 3 Γ with hPdef
  have hP3 : IsPGroup 3 P := isPGroup_pCoreOf 3 Γ
  have hfix : fixedSpace P = ⊥ := hC.fixedSpace_eq_bot
  have hPn : ∀ γ ∈ Γ, ∀ n ∈ P, γ * n * γ⁻¹ ∈ P := pCoreOf_normal_conj 3 Γ
  have h9le : 9 ≤ Nat.card P := hC.nine_le_card
  rcases hW.kernels_eq_or_ne hP3 hfix hPn with ⟨h01, h12⟩ | ⟨h01, h02, h12⟩
  · exfalso
    have := hW.card_le_three_of_eq hP3 hfix h01 h12
    omega
  · have hdist : ∀ i j : Fin 3, i ≠ j → centralizerOn P (W i) ≠ centralizerOn P (W j) := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact h01
      · exact h02
      · exact Ne.symm h01
      · exact absurd rfl hij
      · exact h12
      · exact Ne.symm h02
      · exact Ne.symm h12
      · exact absurd rfl hij
    refine isSolvable_of_prime_divisors (p := 2) (q := 3) fun r hr hrd => ?_
    by_contra hr23
    rw [not_or] at hr23
    have h5 : 5 ≤ r := by
      have := hr.two_le
      by_contra h
      interval_cases r
      · exact hr23.1 rfl
      · exact hr23.2 rfl
      · exact absurd hr (by decide)
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨γ, hγ⟩ := exists_prime_orderOf_dvd_card' r hrd
    exact false_of_prime_order_of_planes hW
      (fun g hg i => hW.conj_mem_of_distinct hP3 hfix hPn hdist hg i) hr h5 hγ

end Planes

section Simple

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem commute_of_centralizes_of_simple [Nontrivial V] {P : Subgroup (GLV V)}
    (hs : ∀ U : Submodule (ZMod 2) V, Invariant P U → U = ⊥ ∨ U = ⊤)
    {g h : GLV V} (hg : ∀ p ∈ P, g * p = p * g) (hh : ∀ p ∈ P, h * p = p * h) :
    g * h = h * g := by
  classical
  let S : Subalgebra (ZMod 2) (Module.End (ZMod 2) V) :=
    Subalgebra.centralizer (ZMod 2) {f | ∃ p ∈ P, f = ((p : GLV V) : Module.End (ZMod 2) V)}
  have hmemS : ∀ f : Module.End (ZMod 2) V, f ∈ S ↔ ∀ p ∈ P,
      f * ((p : GLV V) : Module.End (ZMod 2) V) = ((p : GLV V) : Module.End (ZMod 2) V) * f := by
    intro f
    simp only [S, Subalgebra.mem_centralizer_iff, Set.mem_ofPred_eq]
    constructor
    · intro hf p hp
      exact (hf _ ⟨p, hp, rfl⟩).symm
    · rintro hf _ ⟨p, hp, rfl⟩
      exact (hf p hp).symm
  have : Finite S := by
    have : Finite (Module.End (ZMod 2) V) :=
      Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
    infer_instance
  have hunit : ∀ a : S, IsUnit a ∨ a = 0 := by
    intro a
    by_cases ha : a = 0
    · exact Or.inr ha
    · left
      have hker : LinearMap.ker (a : Module.End (ZMod 2) V) = ⊥ := by
        have hinv : Invariant P (LinearMap.ker (a : Module.End (ZMod 2) V)) := by
          intro p hp v hv
          have hc := (hmemS _).1 a.2 p hp
          have hcv : (a : Module.End (ZMod 2) V) (p v) = p ((a : Module.End (ZMod 2) V) v) := by
            have := congrArg (fun f : Module.End (ZMod 2) V => f v) hc
            simpa [Module.End.mul_apply] using this
          rw [LinearMap.mem_ker] at hv ⊢
          rw [hcv, hv]
          simp
        rcases hs _ hinv with h0 | h1
        · exact h0
        · exfalso
          apply ha
          apply Subtype.ext
          ext v
          have : v ∈ LinearMap.ker (a : Module.End (ZMod 2) V) := by rw [h1]; trivial
          simpa using this
      have hinj : Function.Injective (a : Module.End (ZMod 2) V) := LinearMap.ker_eq_bot.1 hker
      have hbij : Function.Bijective (a : Module.End (ZMod 2) V) :=
        Finite.injective_iff_bijective.1 hinj
      let e := LinearEquiv.ofBijective (a : Module.End (ZMod 2) V) hbij
      have hinvS : (e.symm : Module.End (ZMod 2) V) ∈ S := by
        rw [hmemS]
        intro p hp
        have hc := (hmemS _).1 a.2 p hp
        ext v
        simp only [Module.End.mul_apply]
        have hcv : (a : Module.End (ZMod 2) V) (p (e.symm v)) = p v := by
          have := congrArg (fun f : Module.End (ZMod 2) V => f (e.symm v)) hc
          have h2 : (a : Module.End (ZMod 2) V) (p (e.symm v)) =
              p ((a : Module.End (ZMod 2) V) (e.symm v)) := by
            simpa [Module.End.mul_apply] using this
          rw [h2]
          congr 1
          exact e.apply_symm_apply v
        have h3 := congrArg e.symm hcv
        have h4 : e.symm ((a : Module.End (ZMod 2) V) (p (e.symm v))) = p (e.symm v) :=
          e.symm_apply_apply _
        rw [h4] at h3
        exact h3.symm
      refine ⟨⟨a, ⟨(e.symm : Module.End (ZMod 2) V), hinvS⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        ext v
        simp [e]
      · apply Subtype.ext
        ext v
        simp [e]
  let _ : DivisionRing S := DivisionRing.ofIsUnitOrEqZero hunit
  let _ : Field S := littleWedderburn S
  let gS : S := ⟨((g : GLV V) : Module.End (ZMod 2) V), (hmemS _).2 fun p hp => by
    ext v
    have := congrArg (fun f : GLV V => f v) (hg p hp)
    simpa using this⟩
  let hS : S := ⟨((h : GLV V) : Module.End (ZMod 2) V), (hmemS _).2 fun p hp => by
    ext v
    have := congrArg (fun f : GLV V => f v) (hh p hp)
    simpa using this⟩
  have hcomm := mul_comm gS hS
  have := congrArg (fun x : S => (x : Module.End (ZMod 2) V)) hcomm
  refine LinearEquiv.ext fun v => ?_
  have h2 := congrArg (fun f : Module.End (ZMod 2) V => f v) this
  exact h2

theorem index_centralizer_dvd_432 {Γ : Type*} [Group Γ] [Finite Γ] (P : Subgroup Γ) [P.Normal]
    (hP : Nat.card P = 27) (hnc : ∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) :
    (Subgroup.centralizer (P : Set Γ)).index ∣ 432 := by
  have hnc' : ∃ u v : P, u * v ≠ v * u := by
    obtain ⟨u, hu, v, hv, h⟩ := hnc
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, fun h' => h (congrArg Subtype.val h')⟩
  have hst : ∀ p : SmD6GrpB.NCPairs P,
      MulAction.stabilizer Γ p = Subgroup.centralizer (P : Set Γ) := by
    intro p
    ext γ
    rw [SmD6GrpB.mem_stabilizer_iff]
    constructor
    · rintro ⟨ha, hb⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hgen := SmD6GrpB.closure_pair_eq_top hP p.2
      have hx' : (⟨x, hx⟩ : P) ∈ Subgroup.closure ({p.1.1, p.1.2} : Set P) := by
        rw [hgen]
        exact Subgroup.mem_top _
      have hle : Subgroup.closure ({p.1.1, p.1.2} : Set P) ≤
          (Subgroup.centralizer ({γ} : Set Γ)).comap P.subtype := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.2 ha.symm
        · exact Subgroup.mem_centralizer_singleton_iff.2 hb.symm
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx'))
    · intro hγ
      rw [Subgroup.mem_centralizer_iff] at hγ
      exact ⟨(hγ _ p.1.1.2).symm, (hγ _ p.1.2.2).symm⟩
  have h := SmD6GrpB.index_dvd_card_of_stabilizer_eq _ hst
  rwa [SmD6GrpB.card_noncommuting_pairs hP hnc'] at h

variable {Γ A : Subgroup (GLV V)}

theorem Ctx0.isSolvable_of_simple (hC : Ctx0 Γ A)
    (hs : ∀ U : Submodule (ZMod 2) V, Invariant (pCoreOf 3 Γ) U → U = ⊥ ∨ U = ⊤) :
    Group.IsSolvable ↥Γ := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [hC.hd]; norm_num)
  have hnc := hC.nonabelian_of_simple hs
  have hP27 := hC.card_eq_27 hnc
  set P' : Subgroup ↥Γ := (pCoreOf 3 Γ).subgroupOf Γ with hP'
  have hcard : Nat.card P' = 27 := by
    rw [hP', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 3 Γ)).toEquiv, hP27]
  have hnc' : ∃ u ∈ P', ∃ v ∈ P', u * v ≠ v * u := by
    obtain ⟨u, hu, v, hv, huv⟩ := hnc
    exact ⟨⟨u, pCoreOf_le 3 Γ hu⟩, hu, ⟨v, pCoreOf_le 3 Γ hv⟩, hv,
      fun h => huv (congrArg Subtype.val h)⟩
  set C : Subgroup ↥Γ := Subgroup.centralizer (P' : Set ↥Γ) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hCab : ∀ x y : C, x * y = y * x := by
    intro x y
    have hx : ∀ p ∈ pCoreOf 3 Γ, ((x : ↥Γ) : GLV V) * p = p * ((x : ↥Γ) : GLV V) := by
      intro p hp
      have := Subgroup.mem_centralizer_iff.1 x.2 ⟨p, pCoreOf_le 3 Γ hp⟩ hp
      exact (congrArg Subtype.val this).symm
    have hy : ∀ p ∈ pCoreOf 3 Γ, ((y : ↥Γ) : GLV V) * p = p * ((y : ↥Γ) : GLV V) := by
      intro p hp
      have := Subgroup.mem_centralizer_iff.1 y.2 ⟨p, pCoreOf_le 3 Γ hp⟩ hp
      exact (congrArg Subtype.val this).symm
    have := commute_of_centralizes_of_simple hs hx hy
    exact Subtype.ext (Subtype.ext this)
  have hCsolv : Group.IsSolvable C := Group.isSolvable_of_comm hCab
  have hidx : C.index ∣ 432 := index_centralizer_dvd_432 P' hcard hnc'
  have hqsolv : Group.IsSolvable (↥Γ ⧸ C) := by
    refine isSolvable_of_card_dvd_two_pow_mul_three_pow (a := 4) (b := 3) ?_
    rw [← Subgroup.index_eq_card]
    exact hidx
  exact Group.isSolvable_of_ker_le_range C.subtype (QuotientGroup.mk' C)
    (by rw [QuotientGroup.ker_mk']; simp)

theorem Ctx0.isSolvable (hC : Ctx0 Γ A) : Group.IsSolvable ↥Γ := by
  rcases hC.simple_or_planes with hs | ⟨W, hW⟩
  · exact hC.isSolvable_of_simple hs
  · exact hC.isSolvable_of_planes hW

end Simple

end CFSG.Quasithin.SzG11G94
