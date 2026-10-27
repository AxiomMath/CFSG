module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmCompAlign

public section

namespace CFSG.StandardType

namespace CoordOm

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

local notation "bComp" => CFSG.RankThree.PartOne.KCOrthogonal.blockComponent
local notation "bCompApply" => CFSG.RankThree.PartOne.KCOrthogonal.blockComponent_apply_of_mem

theorem eq_sum_smul_single_sub {R : Type*} [CommRing R] {r : ℕ} (s δ : Fin r → R) (i₀ : Fin r)
    (hδ : δ i₀ = 1) (hsum : ∑ i, δ i * s i = 0) :
    s = ∑ i ∈ Finset.univ.erase i₀,
      s i • ((Pi.single i 1 : Fin r → R) - δ i • Pi.single i₀ 1) := by
  classical
  funext m
  rw [Finset.sum_apply]
  by_cases hm : m = i₀
  · subst hm
    have h1 : ∀ i ∈ Finset.univ.erase m,
        ((s i • ((Pi.single i 1 : Fin r → R) - δ i • Pi.single m 1) : Fin r → R)) m =
          -(δ i * s i) := by
      intro i hi
      have hne := Finset.ne_of_mem_erase hi
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hne,
        smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_neg_distrib]
    have h2 := Finset.add_sum_erase Finset.univ (fun i => δ i * s i) (Finset.mem_univ m)
    rw [hsum, hδ, one_mul] at h2
    linear_combination h2
  · rw [Finset.sum_eq_single m]
    · simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hm,
        smul_eq_mul, mul_zero, sub_zero, mul_one]
    · intro i _ him
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_of_ne' him, Pi.single_eq_of_ne hm,
        smul_eq_mul, mul_zero, sub_zero]
    · intro hm'
      exact absurd (Finset.mem_erase.mpr ⟨hm, Finset.mem_univ m⟩) hm'

theorem ofAdd_sum_mem {G : Type*} [Group G] {p r : ℕ} {I : Type*}
    {ι : Multiplicative (Fin r → ZMod p) →* G} {L : Subgroup G} (T : Finset I)
    (f : I → Fin r → ZMod p) (hf : ∀ m ∈ T, ι (ofAdd (f m)) ∈ L) :
    ι (ofAdd (∑ m ∈ T, f m)) ∈ L := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty, ofAdd_zero, map_one]; exact L.one_mem
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, ofAdd_add, map_mul]
    exact L.mul_mem (hf a (Finset.mem_insert_self a T))
      (ih fun m hm => hf m (Finset.mem_insert_of_mem hm))

section Count

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

theorem card_ge_of_three [Fact p.Prime] (F : SevOm.Frame Q p A r) {H : Subgroup (V ≃ₗ[K] V)}
    [Finite H]
    {v₁ v₂ v₃ : Fin r → ZMod p} (h₁ : F.ι (ofAdd v₁) ∈ H) (h₂ : F.ι (ofAdd v₂) ∈ H)
    (h₃ : F.ι (ofAdd v₃) ∈ H) {k₁ k₂ k₃ : Fin r} (hv₁ : v₁ k₁ ≠ 0) (hv₂ : v₂ k₂ ≠ 0)
    (hv₃ : v₃ k₃ ≠ 0) (h12 : v₁ k₂ = 0) (h13 : v₁ k₃ = 0) (h23 : v₂ k₃ = 0) :
    p ^ 3 ≤ Nat.card H := by
  have hmem : ∀ a : ZMod p × ZMod p × ZMod p,
      F.ι (ofAdd (a.1 • v₁ + a.2.1 • v₂ + a.2.2 • v₃)) ∈ H := by
    intro a
    rw [ofAdd_add, ofAdd_add, map_mul, map_mul]
    exact H.mul_mem (H.mul_mem (StepTwoToral.ofAdd_smul_mem h₁ _)
      (StepTwoToral.ofAdd_smul_mem h₂ _)) (StepTwoToral.ofAdd_smul_mem h₃ _)
  have hinj : Function.Injective fun a : ZMod p × ZMod p × ZMod p => (⟨_, hmem a⟩ : H) := by
    intro a b hab
    have h0 : a.1 • v₁ + a.2.1 • v₂ + a.2.2 • v₃ = b.1 • v₁ + b.2.1 • v₂ + b.2.2 • v₃ :=
      ofAdd.injective (F.inj (congrArg Subtype.val hab))
    have e3 := congrFun h0 k₃
    have e2 := congrFun h0 k₂
    have e1 := congrFun h0 k₁
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h13, h23, mul_zero, zero_add] at e3
    have hc : a.2.2 = b.2.2 := mul_right_cancel₀ hv₃ e3
    rw [hc] at e2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h12, mul_zero, zero_add,
      add_left_inj] at e2
    have hb : a.2.1 = b.2.1 := mul_right_cancel₀ hv₂ e2
    rw [hb, hc] at e1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_left_inj] at e1
    have ha : a.1 = b.1 := mul_right_cancel₀ hv₁ e1
    exact Prod.ext ha (Prod.ext hb hc)
  have hcard : Nat.card (ZMod p × ZMod p × ZMod p) = p ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod]
    ring
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [hcard] at h

variable [FiniteDimensional K V]

theorem frame_triv_orbit (F : SevOm.Frame Q p A r) {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    {t : Multiplicative (Fin r → ZMod p)}
    (ht : ∀ j, toAdd t j ≠ 0 → F.U j ≤ othersSpace x.toLinearMap h) :
    ∀ u ∈ orbitSpace x.toLinearMap h, F.ι t u = u := by
  intro u hu
  refine (F.fix t u).mpr fun j hj w hw => ?_
  rw [QuadraticMap.polar_comm]
  exact hx.polar_orbit_others hh hu (ht j hj hw)

theorem frame_triv_others (F : SevOm.Frame Q p A r) {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    {t : Multiplicative (Fin r → ZMod p)}
    (ht : ∀ j, toAdd t j ≠ 0 → F.U j ≤ orbitSpace x.toLinearMap h) :
    ∀ v ∈ othersSpace x.toLinearMap h, F.ι t v = v :=
  fun v hv => (F.fix t v).mpr fun j hj _ hw => hx.polar_orbit_others hh (ht j hj hw) hv

end Count

theorem centralizerDet_commutator {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {x : V ≃ₗ[K] V} {h : K[X]} (a b : ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))) :
    centralizerDet x h ⁅a, b⁆ = 1 := by
  rw [commutatorElement_def, map_mul, map_mul, map_mul]
  have e1 : centralizerDet x h a * centralizerDet x h a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have e2 : centralizerDet x h b * centralizerDet x h b⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  calc centralizerDet x h a * centralizerDet x h b * centralizerDet x h a⁻¹ *
        centralizerDet x h b⁻¹ =
      (centralizerDet x h a * centralizerDet x h a⁻¹) *
        (centralizerDet x h b * centralizerDet x h b⁻¹) := by ring
    _ = 1 := by rw [e1, e2, one_mul]

section Class

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

theorem blockComponent_apply_orbit {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (g : ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {u : V} (hu : u ∈ orbitSpace x.toLinearMap h) :
    (bComp hx g h).1 u = g.1 u := by
  classical
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
  have hh' := hx.reciprocalPolynomial_mem hh
  rw [map_add, map_add, bCompApply hx g h hh hu₁, bCompApply hx g h hh' hu₂]
  simp only [true_or, or_true, ite_true]

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem eq_zero_of_fix_orbit {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hX : h ≠ X - 1) {u : V}
    (hu : u ∈ orbitSpace x.toLinearMap h) (hfix : x u = u) : u = 0 := by
  have h1 := hx.sum_pow_eq_zero_orbit hh hX hu
  have hpow : ∀ i : ℕ, (x.toLinearMap ^ i) u = u := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      exact hfix
  rw [Finset.sum_congr rfl fun i _ => hpow i, Finset.sum_const, Finset.card_range,
    ← Nat.cast_smul_eq_nsmul K,
    CFSG.RankThree.PartOne.OddIso.natCast_odd_eq_one (hp.odd_of_ne_two hp2), one_smul] at h1
  exact h1

theorem prod_pairTwist {G : Type*} [CommGroup G] {r : ℕ} (c : G) (i j : Fin r) :
    ∏ m, (if m = i then c else 1) * (if m = j then c⁻¹ else 1) = 1 := by
  classical
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp only [Finset.mem_univ, ite_true, mul_inv_cancel]

theorem comp_class (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (F : SevOm.Frame Q p A r) (hr4 : 4 ≤ r)
    (hF : FrameMoves F (CoordSpNs.galSigns p (Nat.card K))) (β : Fin r → ZMod p) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι (ofAdd β)).toLinearMap) (hX : h ≠ X - 1)
    {L : Subgroup (V ≃ₗ[K] V)} (hLeq : L = specialBlock Q (F.ι (ofAdd β)) h)
    (hcardL : Nat.card (A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ p ^ 2) :
    ∃ (k : Fin r) (c : ZMod p) (ε : Fin r → (ZMod p)ˣ), c ≠ 0 ∧
      (∀ i, ε i ∈ CoordSpNs.galSigns p (Nat.card K)) ∧ (∀ i, i ≠ k → β i = (ε i : ZMod p) * c) ∧
      ∀ s : Fin r → ZMod p, s k = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0 →
        F.ι (ofAdd s) ∈ L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ he => LinearEquiv.ext (congrFun he)
  set x := F.ι (ofAdd β) with hxdef
  have hx : OddOrderIsometry Q p x := F.oddOrderIsometry hQ hp2 hp hAΩ (ofAdd β)
  have hxA : x ∈ A := F.mem _
  have hxc : x ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hLB : L ≤ supportedBlock Q x h := hLeq ▸ specialBlock_le_supportedBlock h
  have hdich : ∀ j, F.U j ≤ orbitSpace x.toLinearMap h ∨ F.U j ≤ othersSpace x.toLinearMap h :=
    fun j => frame_piece_dichotomy hQ hT hp hp2 F hAΩ hmax (ofAdd β) hh j
  have hAc : ∀ y ∈ A, y ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (frame_comm F hy hxA)
  have hoff : ∀ t : Multiplicative (Fin r → ZMod p),
      (∀ j, toAdd t j ≠ 0 → F.U j ≤ othersSpace x.toLinearMap h) →
        F.ι t ∈ A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := fun t ht =>
    Subgroup.mem_inf.mpr ⟨F.mem t, Subgroup.mem_centralizer_iff.mpr fun g hg =>
      commute_of_triv hx hh (hLB hg) (hAc _ (F.mem t)) (frame_triv_orbit F hx hh ht)⟩
  set z := (bComp hx ⟨x, hxc⟩ h).1 with hzdef
  have hzA : z ∈ A := blockComponent_mem_A hQ hT hp hp2 F hAΩ hmax hx hxA hxA hxc h hh
  have hzB : z ∈ supportedBlock Q x h := hx.blockComponent_mem
    (Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup (hAΩ hxA), hxc⟩) hh
  have hzx : ∀ u ∈ orbitSpace x.toLinearMap h, z u = x u := fun u hu =>
    blockComponent_apply_orbit hx ⟨x, hxc⟩ hh hu
  have hzL : z ∈ A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := by
    refine Subgroup.mem_inf.mpr ⟨hzA, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    have hgB := hLB hg
    have hgc : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
      (Subgroup.mem_inf.mp (mem_supportedBlock.mp hgB).1).2
    have hgx : ∀ v, g (x v) = x (g v) := fun v => by
      show (g * x) v = (x * g) v
      rw [Subgroup.mem_centralizer_singleton_iff.mp hgc]
    ext v
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_of_isCompl (hx.isCompl_orbit_others hh) v
    simp only [LinearEquiv.mul_apply, map_add]
    rw [hzx u hu, (mem_supportedBlock.mp hzB).2 w hw, (mem_supportedBlock.mp hgB).2 w hw,
      hzx (g u) (mem_orbitSpace_of_apply hgc hu), (mem_supportedBlock.mp hzB).2 w hw, hgx]
  obtain ⟨sz, hsz⟩ := F.exists_eq hzA
  have hszS : ∀ j, F.U j ≤ orbitSpace x.toLinearMap h → toAdd sz j ≠ 0 := by
    intro j hj h0
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot j)
    have h1 : z u = u := by
      rw [← hsz]
      exact F.triv sz j h0 u hu
    rw [hzx u (hj hu)] at h1
    exact hu0 (eq_zero_of_fix_orbit hx hp hp2 hh hX (hj hu) h1)
  have hszO : ∀ j, ¬ F.U j ≤ orbitSpace x.toLinearMap h → toAdd sz j = 0 := by
    intro j hj
    by_contra h0
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot j)
    have h1 : F.ι sz u = u := by
      rw [hsz]
      exact (mem_supportedBlock.mp hzB).2 u (((hdich j).resolve_left hj) hu)
    exact hu0 (F.fpf sz j h0 u hu h1)
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, F.U j₀ ≤ orbitSpace x.toLinearMap h := by
    by_contra hno
    push Not at hno
    have hsz1 : sz = 1 := toAdd.injective (funext fun j => hszO j (hno j))
    obtain ⟨u, hu, hu0⟩ :=
      (Submodule.ne_bot_iff _).mp (primaryComponent_ne_bot hx.squarefree_minpoly hh)
    have huo : u ∈ orbitSpace x.toLinearMap h := Submodule.mem_sup_left hu
    have h1 : x u = u := by
      rw [← hzx u huo, ← hsz, hsz1, map_one]
      rfl
    exact hu0 (eq_zero_of_fix_orbit hx hp hp2 hh hX huo h1)
  have hsingle : ∀ k₁, ¬ F.U k₁ ≤ orbitSpace x.toLinearMap h →
      F.ι (ofAdd (Pi.single k₁ 1)) ∈ A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := by
    intro k₁ hk₁
    refine hoff _ fun j hj => ?_
    have hjk : j = k₁ := by
      by_contra hne
      exact hj (by rw [toAdd_ofAdd, Pi.single_eq_of_ne hne])
    rw [hjk]
    exact (hdich k₁).resolve_left hk₁
  obtain ⟨k, hk⟩ : ∃ k, ∀ i, i ≠ k → F.U i ≤ orbitSpace x.toLinearMap h := by
    by_contra hno
    push Not at hno
    obtain ⟨k₁, hk₁j, hk₁⟩ := hno j₀
    obtain ⟨k₂, hk₂k, hk₂⟩ := hno k₁
    have hk₂j : k₂ ≠ j₀ := fun e => hk₂ (e ▸ hj₀)
    have h3 := card_ge_of_three F (hsingle k₁ hk₁) (hsingle k₂ hk₂)
      (show F.ι (ofAdd (toAdd sz)) ∈ A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) by
        rw [ofAdd_toAdd, hsz]
        exact hzL)
      (k₁ := k₁) (k₂ := k₂) (k₃ := j₀) (by simp) (by simp) (hszS j₀ hj₀)
      (by simp [hk₂k]) (by simp [Ne.symm hk₁j])
      (by simp [Ne.symm hk₂j])
    exact absurd (h3.trans hcardL) (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  obtain ⟨i₀, -, -, -, -, -, hi₀k, -, -⟩ := SevOm.exists_three_ne hr4 k
  have hβS : ∀ i, i ≠ k → β i ≠ 0 := by
    intro i hik h0
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot i)
    exact hu0 (eq_zero_of_fix_orbit hx hp hp2 hh hX (hk i hik hu) (F.triv (ofAdd β) i h0 u hu))
  set c := β i₀ with hcdef
  have hc0 : c ≠ 0 := hβS i₀ hi₀k
  have hO1 : (1 : (ZMod p)ˣ) ∈ CoordSpNs.galSigns p (Nat.card K) := Subgroup.one_mem _
  have halign : ∀ i, i ≠ k →
      ∃ u ∈ CoordSpNs.galSigns p (Nat.card K), β i = (u : ZMod p) * c := by
    intro i hik
    obtain ⟨w, -, hw⟩ := hF (Equiv.swap i₀ i) 1 (fun _ => hO1) (by simp)
    refine frame_align hQ hp hp2 hAΩ F β hh hX (hk i₀ hi₀k) (hk i hik) (w := w) fun s => ?_
    rw [hw s]
    simp only [Pi.one_apply, Units.val_one, one_mul]
  choose! u hu hβu using halign
  set ε : Fin r → (ZMod p)ˣ := fun i => if i = k then 1 else u i with hεdef
  have hεO : ∀ i, ε i ∈ CoordSpNs.galSigns p (Nat.card K) := by
    intro i
    by_cases hik : i = k
    · simp only [hεdef, hik, ite_true]
      exact hO1
    · simp only [hεdef, hik, ite_false]
      exact hu i hik
  have hβε : ∀ i, i ≠ k → β i = (ε i : ZMod p) * c := by
    intro i hik
    simp only [hεdef, hik, ite_false]
    exact hβu i hik
  have hεi₀ : ε i₀ = 1 := by
    have h1 := hβε i₀ hi₀k
    apply Units.ext
    rw [Units.val_one]
    have h2 : ((ε i₀ : ZMod p) - 1) * c = 0 := by
      rw [sub_mul, ← h1, one_mul, hcdef, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hc0)
  refine ⟨k, c, ε, hc0, hεO, hβε, fun s hsk hsum => ?_⟩
  have hgen : ∀ i, i ≠ k → F.ι (ofAdd ((Pi.single i 1 : Fin r → ZMod p) -
      (↑(ε i)⁻¹ : ZMod p) • Pi.single i₀ 1)) ∈ L := by
    intro i hik
    by_cases hii : i = i₀
    · rw [hii, hεi₀, inv_one, Units.val_one, one_smul, sub_self, ofAdd_zero, map_one]
      exact L.one_mem
    set η : Fin r → (ZMod p)ˣ := fun m =>
      (if m = i₀ then (ε i)⁻¹ else 1) * (if m = i then ((ε i)⁻¹)⁻¹ else 1) with hηdef
    have hηO : ∀ m, η m ∈ CoordSpNs.galSigns p (Nat.card K) := by
      intro m
      refine Subgroup.mul_mem _ ?_ ?_
      · split_ifs
        · exact Subgroup.inv_mem _ (hεO i)
        · exact hO1
      · split_ifs
        · exact Subgroup.inv_mem _ (Subgroup.inv_mem _ (hεO i))
        · exact hO1
    obtain ⟨w, hw, hws⟩ := hF (Equiv.swap i₀ i) η hηO (prod_pairTwist _ i₀ i)
    have hηi₀ : (η i₀ : ZMod p) = (↑(ε i)⁻¹ : ZMod p) := by
      simp only [hηdef, Ne.symm hii, ite_true, ite_false, mul_one]
    have hηi : (η i : ZMod p) = (ε i : ZMod p) := by
      simp only [hηdef, hii, ite_true, ite_false, one_mul, inv_inv]
    have hηm : ∀ m, m ≠ i₀ → m ≠ i → (η m : ZMod p) = 1 := by
      intro m h1 h2
      simp only [hηdef, h1, h2, ite_false, mul_one, Units.val_one]
    have hwx : w⁻¹ * x * w = x := by
      rw [hxdef, hws β]
      congr 2
      funext m
      by_cases hm₀ : m = i₀
      · subst hm₀
        rw [Equiv.swap_apply_left, hηi₀, hβε i hik, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, one_mul]
      · by_cases hmi : m = i
        · rw [hmi, Equiv.swap_apply_right, hηi, hβε i hik]
        · rw [Equiv.swap_apply_of_ne_of_ne hm₀ hmi, hηm m hm₀ hmi, one_mul]
    have hwC : w ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w * x = w * (w⁻¹ * x * w) := by rw [hwx]
        _ = x * w := by group
    have hwI : w ∈ isometryCentralizer Q x := Subgroup.mem_inf.mpr
      ⟨orthDerived_le_orthogonalGroup (Subgroup.mem_inf.mp hw).1, hwC⟩
    set g := F.ι (ofAdd (Pi.single i (1 : ZMod p))) with hgdef
    have hgB : g ∈ supportedBlock Q x h := by
      refine mem_supportedBlock.mpr ⟨Subgroup.mem_inf.mpr
        ⟨orthDerived_le_orthogonalGroup (hAΩ (F.mem _)), hAc _ (F.mem _)⟩,
        frame_triv_others F hx hh fun j hj => ?_⟩
      have hji : j = i := by
        by_contra hne
        exact hj (by rw [toAdd_ofAdd, Pi.single_eq_of_ne hne])
      rw [hji]
      exact hk i hik
    have hgC : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := hAc _ (F.mem _)
    have hcomm : g⁻¹ * (w⁻¹ * g * w) = F.ι (ofAdd (-((Pi.single i 1 : Fin r → ZMod p) -
        (↑(ε i)⁻¹ : ZMod p) • Pi.single i₀ 1))) := by
      rw [hgdef, hws, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
      congr 2
      funext m
      simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hm₀ : m = i₀
      · rw [hm₀, Equiv.swap_apply_left, hηi₀, Pi.single_eq_same, Pi.single_eq_same,
          Pi.single_eq_of_ne (Ne.symm hii)]
        ring
      · by_cases hmi : m = i
        · rw [hmi, Equiv.swap_apply_right, Pi.single_eq_same, Pi.single_eq_of_ne hii,
            Pi.single_eq_of_ne (Ne.symm hii)]
          ring
        · rw [Equiv.swap_apply_of_ne_of_ne hm₀ hmi, Pi.single_eq_of_ne hmi,
            Pi.single_eq_of_ne hm₀]
          ring
    have hSB : g⁻¹ * (w⁻¹ * g * w) ∈ supportedBlock Q x h := by
      refine Subgroup.mul_mem _ (Subgroup.inv_mem _ hgB) ?_
      have h1 := conj_mem_supportedBlock (Subgroup.inv_mem _ hwI) hgB
      rwa [inv_inv] at h1
    have hspec : g⁻¹ * (w⁻¹ * g * w) ∈ specialBlock Q x h := by
      refine mem_specialBlock.mpr ⟨hSB, ?_⟩
      have h1 : (⟨g⁻¹ * (w⁻¹ * g * w), supportedBlock_le_centralizer h hSB⟩ :
          ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))) =
          ⁅(⟨g⁻¹, Subgroup.inv_mem _ hgC⟩ : ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))),
            ⟨w⁻¹, Subgroup.inv_mem _ hwC⟩⁆ := by
        apply Subtype.ext
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      show centralizerDet x h ⟨g⁻¹ * (w⁻¹ * g * w), supportedBlock_le_centralizer h hSB⟩ = 1
      rw [h1]
      exact centralizerDet_commutator _ _
    rw [hcomm, hLeq.symm] at hspec
    have h2 := L.inv_mem hspec
    rwa [← map_inv, ← ofAdd_neg, neg_neg] at h2
  have hdecomp := eq_sum_smul_single_sub s (fun m => (↑(ε m)⁻¹ : ZMod p)) i₀
    (by simp [hεi₀]) hsum
  rw [hdecomp]
  refine ofAdd_sum_mem _ _ fun m _ => ?_
  by_cases hmk : m = k
  · rw [hmk, hsk, zero_smul, ofAdd_zero, map_one]
    exact L.one_mem
  · exact StepTwoToral.ofAdd_smul_mem (hgen m hmk) (s m)

end Class

end CoordOm

end CFSG.StandardType
