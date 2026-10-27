module

public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicFourActors
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
  CFSG.LieType.AlgebraicGroups SteinbergBN EvenF4QPlus RootSpace CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical CFSG.LieType.Steinberg.Adjoint
open Subgroup
open scoped Pointwise commutatorElement

theorem F4_four_thetaT_eq_bot {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + 1)
    (B : Subgroup (MulAut (adjointGroup .F4 K)))
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    thetaT p E = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  have := hE
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨a, ha⟩
    simpa using congrArg Subtype.val h
  set ι' : adjointGroup Tag.F4 K →* ModGL Tag.F4 (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup Tag.F4 K).subtype
    with hι'
  have hι'inj : Function.Injective ι' :=
    (baseChangeGL_injective (τ := Tag.F4) (algebraMap K (AlgebraicClosure K))).comp
      Subtype.val_injective
  by_cases hEinn : ∃ b ∈ E, (b : MulAut (adjointGroup .F4 K)) ∉
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range
  · obtain ⟨b, hbE, hbR⟩ := hEinn
    have hb1 : b ≠ 1 := fun h => hbR (by rw [h]; exact one_mem _)
    have hbp : orderOf b = p := orderOf_eq_prime (hEpow b hbE) hb1
    refine eq_bot_iff.2 fun y hy => ?_
    have h := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy b) hbE) hb1)
    rw [inSubgroup, F4_localCore_eq_bot_of_noninner K hp hp3 B hB b hbR hbp,
      Subgroup.map_bot] at h
    exact h
  push Not at hEinn
  set P : Subgroup (adjointGroup .F4 K) := (E.map B.subtype).comap
    (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) with hP
  have hle : E.map B.subtype ≤
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
    rintro _ ⟨b, hb, rfl⟩
    exact hEinn b hb
  have hPmap : P.map (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) =
      E.map B.subtype :=
    Subgroup.map_comap_eq_self hle
  have hPcard : Nat.card P = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap,
      Subgroup.card_map_of_injective B.subtype_injective, hEcard]
  have hPE : ∀ y ∈ P, ∃ e ∈ E, (e : MulAut (adjointGroup .F4 K)) = MulAut.conj y :=
    fun y hy => by
      obtain ⟨e, he, hye⟩ := hy
      exact ⟨e, he, hye⟩
  have hPpow : ∀ y ∈ P, y ^ p = 1 := fun y hy => by
    obtain ⟨e, he, hye⟩ := hPE y hy
    apply hinj
    rw [map_pow, ← hye, map_one, ← Subgroup.coe_pow, hEpow e he, Subgroup.coe_one]
  obtain ⟨g, hg, hgn, hc⟩ := exists_lang_torus_coordinates K (AlgebraicClosure K) F hF hp hp3
    hpd P (IsPGroup.of_card hPcard)
  have hPT : ∀ y ∈ P, g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (y : ModGL Tag.F4 K) * g ∈
        torusGroup Tag.F4 (AlgebraicClosure K) ⊓ conjEntrywiseImage K g⁻¹ := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := hc y hy
    rw [hxy, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hx
  have hbi : ∀ i : Fin Tag.F4.rank, ∃ b ∈ P, b ≠ 1 ∧
      torusRootChar (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (b : ModGL Tag.F4 K) * g) (Pi.single i 1) = 1 := fun i => by
    let χ : P →* (AlgebraicClosure K)ˣ :=
      { toFun := fun y => Units.mk0 (torusRootChar (g⁻¹ * baseChangeGL
            (algebraMap K (AlgebraicClosure K)) (((y : adjointGroup .F4 K)) : ModGL Tag.F4 K) *
              g) (Pi.single i 1))
          (torusRootChar_ne_zero (torusGroup_le_diagonalGroup (hPT y y.2).1) _)
        map_one' := by
          apply Units.ext
          simp only [Subgroup.coe_one, map_one, mul_one, inv_mul_cancel, Units.val_mk0,
            Units.val_one]
          exact torusRootChar_one _
        map_mul' := fun a b => by
          apply Units.ext
          simp only [Subgroup.coe_mul, map_mul, Units.val_mk0, Units.val_mul]
          rw [show g⁻¹ * (baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((a : adjointGroup .F4 K) : ModGL Tag.F4 K) *
                baseChangeGL (algebraMap K (AlgebraicClosure K))
                  ((b : adjointGroup .F4 K) : ModGL Tag.F4 K)) * g =
              (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                ((a : adjointGroup .F4 K) : ModGL Tag.F4 K) * g) *
              (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                ((b : adjointGroup .F4 K) : ModGL Tag.F4 K) * g) by group]
          exact torusRootChar_mul (torusGroup_le_diagonalGroup (hPT a a.2).1)
            (torusGroup_le_diagonalGroup (hPT b b.2).1) _ }
    obtain ⟨a, ha1, hχa⟩ := exists_ne_one_map_eq_one_of_card_sq hp
      (fun a => Subtype.ext (by simpa using hPpow a a.2)) hPcard χ
    refine ⟨a, a.2, fun h => ha1 (Subtype.ext h), ?_⟩
    have h1 := congrArg Units.val hχa
    simpa [χ] using h1
  choose b hbP hb1 hbχ using hbi
  have hβE : ∀ i, (⟨MulAut.conj (b i), hB ⟨b i, rfl⟩⟩ : B) ∈ E := fun i => by
    obtain ⟨e, he, hye⟩ := hPE (b i) (hbP i)
    have : e = ⟨MulAut.conj (b i), hB ⟨b i, rfl⟩⟩ := Subtype.ext hye
    rw [← this]
    exact he
  have hβ1 : ∀ i, (⟨MulAut.conj (b i), hB ⟨b i, rfl⟩⟩ : B) ≠ 1 := fun i h =>
    hb1 i (hinj (by rw [map_one]; exact congrArg Subtype.val h))
  have hact : ∀ i, inSubgroup (aschbacherSolvableCore p)
        (centralizer ({(⟨MulAut.conj (b i), hB ⟨b i, rfl⟩⟩ : B)} : Set B)) ≤
      (centralizer ({b i} : Set (adjointGroup Tag.F4 K)) ⊓
        centralizer ((⁅centralizer ({b i} : Set (adjointGroup Tag.F4 K)),
          centralizer ({b i} : Set (adjointGroup Tag.F4 K))⁆ :
            Subgroup (adjointGroup Tag.F4 K)) : Set (adjointGroup Tag.F4 K))).map
        ((MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).codRestrict B
          fun c => hB ⟨c, rfl⟩) ∧
      ∀ y ∈ centralizer ({b i} : Set (adjointGroup Tag.F4 K)) ⊓
        centralizer ((⁅centralizer ({b i} : Set (adjointGroup Tag.F4 K)),
          centralizer ({b i} : Set (adjointGroup Tag.F4 K))⁆ :
            Subgroup (adjointGroup Tag.F4 K)) : Set (adjointGroup Tag.F4 K)),
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.F4 K) * g ∈
            torusGroup Tag.F4 (AlgebraicClosure K) ∧
          torusRootChar (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (y : ModGL Tag.F4 K) * g) (Pi.single i 1) = 1 := fun i => by
    have hxi := hPT (b i) (hbP i)
    have hbip : orderOf (b i) = p := orderOf_eq_prime (hPpow _ (hbP i)) (hb1 i)
    have hxip : orderOf (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((b i : adjointGroup .F4 K) : ModGL Tag.F4 K) * g) = p := by
      rw [show g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((b i : adjointGroup .F4 K) : ModGL Tag.F4 K) * g =
        (MulAut.conj g⁻¹).toMonoidHom (ι' (b i)) by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          rfl,
        orderOf_injective _ (MulAut.conj g⁻¹).injective, orderOf_injective ι' hι'inj, hbip]
    obtain ⟨-, hS, htor⟩ := F4_four_nonregular_actor K (AlgebraicClosure K) F hℓ hℓ2 hf hK hF
      hp hp3 hpd B hB hg hgn hxi hxip ⟨Pi.single i 1, isRoot_single Tag.F4 i, hbχ i⟩
      (x₁ := b i) (by group)
    exact ⟨hS, fun y hy => ⟨(htor y hy).1.1,
      (htor y hy).2 _ ⟨isRoot_single Tag.F4 i, hbχ i⟩⟩⟩
  refine eq_bot_iff.2 fun z hz => ?_
  have hzi : ∀ i, z ∈ inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨MulAut.conj (b i), hB ⟨b i, rfl⟩⟩ : B)} : Set B)) := fun i =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hz _) (hβE i)) (hβ1 i)
  obtain ⟨y, hy0, hyz⟩ := (hact 0).1 (hzi 0)
  have hyi : ∀ i, y ∈ centralizer ({b i} : Set (adjointGroup Tag.F4 K)) ⊓
      centralizer ((⁅centralizer ({b i} : Set (adjointGroup Tag.F4 K)),
        centralizer ({b i} : Set (adjointGroup Tag.F4 K))⁆ :
          Subgroup (adjointGroup Tag.F4 K)) : Set (adjointGroup Tag.F4 K)) := fun i => by
    obtain ⟨y', hy', hy'z⟩ := (hact i).1 (hzi i)
    have : y' = y := hinj (congrArg Subtype.val (hy'z.trans hyz.symm))
    rw [← this]
    exact hy'
  have hy1 : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.F4 K) * g =
      1 :=
    eq_one_of_torusRootChar_single (AlgebraicClosure K) ((hact 0).2 y hy0).1
      fun i => ((hact i).2 y (hyi i)).2
  have hy1' : y = 1 := by
    apply hι'inj
    rw [map_one]
    change baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.F4 K) = 1
    calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.F4 K) =
          g * (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (y : ModGL Tag.F4 K) * g) * g⁻¹ := by group
      _ = 1 := by rw [hy1]; group
  rw [← hyz, hy1', map_one]
  exact one_mem _

theorem F4_four_odd_card_commutator {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + 1)
    (B : Subgroup (MulAut (adjointGroup .F4 K)))
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (t : B) (htE : t ∈ E) (ht1 : t ≠ 1) :
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (centralizer {t}), E⁆ :
      Subgroup B)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  have := hE
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨a, ha⟩
    simpa using congrArg Subtype.val h
  have htp : orderOf t = p := orderOf_eq_prime (hEpow t htE) ht1
  have hnon : (t : MulAut (adjointGroup .F4 K)) ∉
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range →
      inSubgroup (aschbacherSolvableCore p) (centralizer {t}) = ⊥ := fun htR => by
    rw [inSubgroup, F4_localCore_eq_bot_of_noninner K hp hp3 B hB t htR htp, Subgroup.map_bot]
  by_cases htR : (t : MulAut (adjointGroup .F4 K)) ∈
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range
  · obtain ⟨x₁, hx₁⟩ := htR
    have htb : t = ⟨MulAut.conj x₁, hB ⟨x₁, rfl⟩⟩ := Subtype.ext hx₁.symm
    subst htb
    have hx₁p : orderOf x₁ = p := by
      rw [← orderOf_injective _ hinj x₁, ← htp, Subgroup.orderOf_mk]
    obtain ⟨g, hg, hgn, x, hx, hxp, hxx₁⟩ :=
      exists_lang_coordinate K (AlgebraicClosure K) F hF hp hp3 hpd hx₁p
    obtain ⟨⟨eT⟩, hreg⟩ := F4_four_torus_data K (AlgebraicClosure K) F hF hp hp3 hpd hg hgn
    set bx : B := ⟨MulAut.conj x₁, hB ⟨x₁, rfl⟩⟩ with hbx
    have hSM : inSubgroup (aschbacherSolvableCore p) (centralizer ({bx} : Set B)) ≤
        centralizer ({bx} : Set B) := Subgroup.map_subtype_le _
    have hEM : E ≤ centralizer ({bx} : Set B) := fun e he =>
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val
        (hE.is_comm.comm (⟨bx, htE⟩ : E) ⟨e, he⟩)).symm
    by_cases hR : {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1} = ∅
    ·
      have hX : ∀ y ∈ centralizer ({x₁} : Set (adjointGroup Tag.F4 K)),
          g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.F4 K) * g ∈
            torusGroup Tag.F4 (AlgebraicClosure K) ⊓ conjEntrywiseImage K g⁻¹ := fun y hy => by
        rw [← hreg x hx hxp hR]
        exact conj_inv_baseChange_mem K (AlgebraicClosure K) hxx₁ hy
      obtain ⟨φ, hφ⟩ := exists_injective_pi_of_conj_mem K (AlgebraicClosure K) eT g _ hX
      refine odd_card_commutator_of_invariant hinj hB x₁ le_rfl (fun η hη z hz => ?_) φ hφ hp
        hp3 (IsElementaryAbelian.isPGroup p E) hEM hSM ?_
      · rw [mem_centralizer_singleton_iff] at hz ⊢
        rw [← hη, ← map_mul, hz, map_mul]
      · rw [Subgroup.commutator_le]
        intro s hs e he
        have hct : ⁅s, e⁆ ∈ centralizer ({bx} : Set B) := by
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem (hSM hs) (hEM he)) (inv_mem (hSM hs)))
            (inv_mem (hEM he))
        obtain ⟨c, hc⟩ : ((⁅s, e⁆ : B) : MulAut (adjointGroup .F4 K)) ∈
            (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
          rw [show ((⁅s, e⁆ : B) : MulAut (adjointGroup .F4 K)) =
              ⁅(s : MulAut (adjointGroup .F4 K)), (e : MulAut (adjointGroup .F4 K))⁆ from
            map_commutatorElement B.subtype s e]
          exact F4_commutator_mem_range_conj K _ _
        refine ⟨c, mem_centralizer_singleton_iff.2 (hinj ?_), hc⟩
        have h1 := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hct)
        simp only [Subgroup.coe_mul] at h1
        rw [map_mul, map_mul, hc]
        exact h1
    ·
      obtain ⟨-, hS, htor⟩ := F4_four_nonregular_actor K (AlgebraicClosure K) F hℓ hℓ2 hf hK
        hF hp hp3 hpd B hB hg hgn hx hxp (Set.nonempty_iff_ne_empty.2 hR) hxx₁
      obtain ⟨φ, hφ⟩ := exists_injective_pi_of_conj_mem K (AlgebraicClosure K) eT g _
        fun y hy => (htor y hy).1
      refine odd_card_commutator_of_invariant hinj hB x₁ inf_le_left (fun η hη z hz => ?_) φ hφ
        hp hp3 (IsElementaryAbelian.isPGroup p E) hEM hSM ?_
      · obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
        have hη' : η⁻¹ x₁ = x₁ := by
          calc η⁻¹ x₁ = η⁻¹ (η x₁) := by rw [hη]
            _ = x₁ := by simp
        refine Subgroup.mem_inf.2 ⟨?_, mem_centralizer_iff.2 fun r hr => ?_⟩
        · rw [mem_centralizer_singleton_iff] at hz1 ⊢
          rw [← hη, ← map_mul, hz1, map_mul]
        · have hr' := apply_mem_derived_centralizer hη' hr
          have h1 := mem_centralizer_iff.1 hz2 _ hr'
          have h2 := congrArg η h1
          rwa [map_mul, map_mul, MulAut.apply_inv_self] at h2
      · have hSnorm : ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({bx} : Set B)), E⁆ ≤
            inSubgroup (aschbacherSolvableCore p) (centralizer ({bx} : Set B)) := by
          rw [Subgroup.commutator_le]
          intro s hs e he
          obtain ⟨s', hs', rfl⟩ := hs
          have hconj : (⟨e, hEM he⟩ : centralizer ({bx} : Set B)) * s'⁻¹ *
              (⟨e, hEM he⟩ : centralizer ({bx} : Set B))⁻¹ ∈
                aschbacherSolvableCore p (centralizer ({bx} : Set B)) :=
            (aschbacherSolvableCore_normal p _).conj_mem _ (inv_mem hs') _
          rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc e]
          refine mul_mem ⟨s', hs', rfl⟩ ⟨_, hconj, ?_⟩
          simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
        refine hSnorm.trans fun s hs => ?_
        obtain ⟨y, hy, rfl⟩ := hS hs
        exact ⟨y, hy, rfl⟩
  · rw [hnon htR, Subgroup.commutator_bot_left, Subgroup.card_bot]
    exact odd_one

theorem F4_four_nonregular_core {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + 1)
    (B : Subgroup (MulAut (adjointGroup .F4 K)))
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    (x : adjointGroup .F4 K) (hxp : orderOf x = p)
    (hRne : (⁅centralizer ({x} : Set (adjointGroup .F4 K)),
      centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) ≠ ⊥) :
      Nonempty ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
        centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) ≃*
          matrixIsometryGroup (f4J0 K)) ∧
      inSubgroup (aschbacherSolvableCore p)
          (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)) ≤
        (centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
          centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
            centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
              Set (adjointGroup .F4 K))).map
          ((MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).codRestrict B
            fun c => hB ⟨c, rfl⟩) ∧
      (∀ a ∈ centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
          centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
            centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
              Set (adjointGroup .F4 K)),
        ∀ b ∈ centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
          centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
            centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
              Set (adjointGroup .F4 K)), a * b = b * a) ∧
      ∃ φ : ↥(centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
          centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
            centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
              Set (adjointGroup .F4 K))) →*
          (Fin Tag.G2.rank → Multiplicative (ZMod (Nat.card K ^ 2 + 1))),
        Function.Injective φ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  obtain ⟨g, hg, hgn, x', hx', hx'p, hxx'⟩ :=
    exists_lang_coordinate K (AlgebraicClosure K) F hF hp hp3 hpd hxp
  obtain ⟨⟨eT⟩, hreg⟩ := F4_four_torus_data K (AlgebraicClosure K) F hF hp hp3 hpd hg hgn
  have hR : {α | IsRoot Tag.F4 α ∧ torusRootChar x' α = 1}.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hR
    apply hRne
    have hX : ∀ y ∈ centralizer ({x} : Set (adjointGroup Tag.F4 K)),
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.F4 K) * g ∈
          torusGroup Tag.F4 (AlgebraicClosure K) := fun y hy => by
      have h1 := conj_inv_baseChange_mem K (AlgebraicClosure K) hxx' hy
      rw [hreg x' hx' hx'p hR] at h1
      exact h1.1
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun a ha =>
      mem_centralizer_iff.2 fun b hb => ?_
    exact mul_comm_of_conj_mem_torusGroup K (AlgebraicClosure K) g _ hX b hb a ha
  obtain ⟨hSp, hS, htor⟩ := F4_four_nonregular_actor K (AlgebraicClosure K) F hℓ hℓ2 hf hK hF
    hp hp3 hpd B hB hg hgn hx' hx'p hR hxx'
  obtain ⟨φ, hφ⟩ := exists_injective_pi_of_conj_mem K (AlgebraicClosure K) eT g _
    fun y hy => (htor y hy).1
  exact ⟨hSp, hS, mul_comm_of_conj_mem_torusGroup K (AlgebraicClosure K) g _
    fun y hy => (htor y hy).1.1, φ, hφ⟩

theorem odd_F4_cyclotomic_four_all_actors_local_core_product_odd {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + 1)
    (B : Subgroup (MulAut (adjointGroup .F4 K)))
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) (t : B)
    (htE : t ∈ E) (ht1 : t ≠ 1) :
    thetaT p E = ⊥ ∧
    ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer {t}), E⁆ : Subgroup B) : Set B) *
        (thetaT p E : Set B) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer {t}), E⁆ ⊔ thetaT p E :
        Subgroup B) : Set B) ∧
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (centralizer {t}), E⁆ ⊔
      thetaT p E)) ∧
    ((t : MulAut (adjointGroup .F4 K)) ∉
        (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range →
      inSubgroup (aschbacherSolvableCore p) (centralizer {t}) = ⊥ ∧
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer {t}), E⁆ : Subgroup B) : Set B) *
          (thetaT p E : Set B) = {1}) ∧
    ∀ x : adjointGroup .F4 K, (t : MulAut (adjointGroup .F4 K)) = MulAut.conj x →
      (⁅centralizer ({x} : Set (adjointGroup .F4 K)),
        centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) ≠ ⊥ →
      Nonempty ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
        centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) ≃*
          matrixIsometryGroup (f4J0 K)) ∧
      inSubgroup (aschbacherSolvableCore p) (centralizer {t}) ≤
        (centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
          centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
            centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
              Set (adjointGroup .F4 K))).map
          ((MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).codRestrict B
            fun c => hB ⟨c, rfl⟩) ∧
      (∀ a ∈ centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
          centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
            centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
              Set (adjointGroup .F4 K)),
        ∀ b ∈ centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
          centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
            centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
              Set (adjointGroup .F4 K)), a * b = b * a) ∧
      ∃ φ : ↥(centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
          centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
            centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
              Set (adjointGroup .F4 K))) →*
          (Fin Tag.G2.rank → Multiplicative (ZMod (Nat.card K ^ 2 + 1))),
        Function.Injective φ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨a, ha⟩
    simpa using congrArg Subtype.val h
  have htp : orderOf t = p := orderOf_eq_prime (hEpow t htE) ht1
  have hnon : (t : MulAut (adjointGroup .F4 K)) ∉
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range →
      inSubgroup (aschbacherSolvableCore p) (centralizer {t}) = ⊥ := fun htR => by
    rw [inSubgroup, F4_localCore_eq_bot_of_noninner K hp hp3 B hB t htR htp, Subgroup.map_bot]
  have hIB := F4_four_thetaT_eq_bot hℓ hℓ2 hf K hK hp hp3 hpd B hB E hE hEcard
  have hodd := F4_four_odd_card_commutator hℓ hℓ2 hf K hK hp hp3 hpd B hB E hE t htE ht1
  have hjoin : ⁅inSubgroup (aschbacherSolvableCore p) (centralizer {t}), E⁆ ⊔ thetaT p E =
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer {t}), E⁆ := by
    rw [hIB, sup_bot_eq]
  refine ⟨hIB, ?_, by rw [hjoin]; exact hodd, fun htR => ⟨hnon htR, ?_⟩,
    fun x htx hRne => ?_⟩
  · rw [hjoin, hIB, Subgroup.coe_bot, Set.mul_singleton]
    simp
  · rw [hnon htR, Subgroup.commutator_bot_left, hIB, Subgroup.coe_bot,
      Set.singleton_mul_singleton, one_mul]
  · have htb : t = ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ := Subtype.ext htx
    have hxp : orderOf x = p := by
      rw [← orderOf_injective _ hinj x, ← htp, htb, Subgroup.orderOf_mk]
    rw [htb]
    exact F4_four_nonregular_core hℓ hℓ2 hf K hK hp hp3 hpd B hB x hxp hRne

end CFSG.RankThree.Chevalley
