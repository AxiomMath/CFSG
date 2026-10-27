module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

private theorem r4k_coprime_card_pPrimeCore (p : ℕ) (Y : Type*) [Group Y] [Finite Y] :
    Nat.Coprime p (Nat.card (CFSG.pPrimeCore p Y)) := by
  refine Nat.coprime_of_dvd fun q hq hqp hqn => ?_
  have : Fact q.Prime := ⟨hq⟩
  have hle : CFSG.pPrimeCore p Y ≤ CFSG.pPrimeCore q Y :=
    sSup_le_sSup fun K hK => ⟨hK.1, Nat.Coprime.coprime_dvd_left hqp hK.2⟩
  exact (Nat.Prime.coprime_iff_not_dvd hq).1 CFSG.pPrimeCore_coprime_card
    (hqn.trans (Subgroup.card_dvd_of_le hle))

private theorem r4k_eq_one_of_mem_largeEvenPPrimeCoreOf {G : Type} [Group G] [Finite G]
    {p : ℕ} {X : Subgroup G} {u : G}
    (hu : u ∈ LargeEvenPPrimeCoreOf p X) (hup : u ^ p = 1) : u = 1 := by
  rw [LargeEvenPPrimeCoreOf, LargeEvenPPrimeCore] at hu
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hu
  have hcop : Nat.Coprime p (Nat.card (CFSG.pPrimeCore p ↥X)) :=
    r4k_coprime_card_pPrimeCore p ↥X
  have hvpow : v ^ p = 1 := by
    apply Subtype.ext
    show ((v ^ p : ↥X) : G) = ((1 : ↥X) : G)
    have hvGu : (v : G) = u := hvu
    rw [Subgroup.coe_pow, Subgroup.coe_one, hvGu, hup]
  have h1 : orderOf v ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hvpow
  have h2 : orderOf v ∣ Nat.card (CFSG.pPrimeCore p ↥X) :=
    (CFSG.pPrimeCore p ↥X).orderOf_dvd_natCard hv
  have hv1 : v = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  rw [← hvu, hv1]
  rfl

theorem ggAutomizer_fixes_of_commutator {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {x z : G} (hBs : IsElemAbelian p Bs) (hxBs : x ∈ Bs) (hzBs : z ∈ Bs)
    (hXz : X ≤ Subgroup.centralizer ({z} : Set G))
    (hcomm : (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X) :
    ∀ φ ∈ ggAutomizer X Bs, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ ∧ φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩ := by
  intro φ hφ
  obtain ⟨g, hgX, hgN, hgval⟩ := mem_ggAutomizer_iff.mp hφ
  have hgx : g * x * g⁻¹ = x := by
    have hc : ⁅g, x⁆ ∈ LargeEvenPPrimeCoreOf p X :=
      hcomm (Subgroup.commutator_mem_commutator hgX (Subgroup.mem_zpowers x))
    have hcBs : ⁅g, x⁆ ∈ Bs := by
      rw [commutatorElement_def]
      exact Bs.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN x).mp hxBs) (Bs.inv_mem hxBs)
    have hc1 : ⁅g, x⁆ = 1 :=
      r4k_eq_one_of_mem_largeEvenPPrimeCoreOf hc (hBs.2 _ hcBs)
    rw [commutatorElement_def] at hc1
    exact mul_inv_eq_one.mp hc1
  have hgz : g * z * g⁻¹ = z := by
    have hcommz : g * z = z * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (hXz hgX)
    rw [hcommz]
    group
  refine ⟨?_, ?_⟩
  · apply Subtype.ext
    rw [hgval ⟨x, hxBs⟩, hgx]
  · apply Subtype.ext
    rw [hgval ⟨z, hzBs⟩, hgz]

private theorem r4k_not_five_dvd_card_linearEquiv {W : Type*} [AddCommGroup W]
    [Module (ZMod 3) W] [Finite W] (hW : Module.finrank (ZMod 3) W = 3) :
    ¬ 5 ∣ Nat.card (W ≃ₗ[ZMod 3] W) := by
  classical
  let b : Module.Basis (Fin 3) (ZMod 3) W :=
    (Module.finBasis (ZMod 3) W).reindex (finCongr hW)
  have h1 : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)) =
      Nat.card (W ≃ₗ[ZMod 3] W) := by
    rw [Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv]
    exact Nat.card_congr
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W).toEquiv
  rw [← h1, Matrix.card_GL_field]
  decide

theorem ggFive_not_dvd_of_fixes {G : Type} [Group G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hcard : Nat.card Bs = 3 ^ 5) {x z : G}
    (hxBs : x ∈ Bs) (hzBs : z ∈ Bs) (hD : Nat.card (Subgroup.closure {x, z}) = 3 ^ 2)
    {H : Subgroup (MulAut ↥Bs)}
    (hH : ∀ φ ∈ H, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ ∧ φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩) :
    ¬ 5 ∣ Nat.card H := by
  subst hp3
  intro h5
  have : Finite ↥Bs := (Nat.card_ne_zero.mp (by rw [hcard]; norm_num)).2
  have : Finite ↥H := inferInstance
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨φ, hφord⟩ := exists_prime_orderOf_dvd_card' 5 h5
  obtain ⟨V, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := 3) hBs
  have : Finite V := Finite.of_equiv _ (Additive.ofMul.trans ι.toEquiv)
  have : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  let x' : ↥Bs := ⟨x, hxBs⟩
  let z' : ↥Bs := ⟨z, hzBs⟩
  let vx : V := ι (Additive.ofMul x')
  let vz : V := ι (Additive.ofMul z')
  let D' : Submodule (ZMod 3) V := Submodule.span (ZMod 3) ({vx, vz} : Set V)
  have hcardV : Nat.card V = 3 ^ 5 := by
    rw [← card_eq_of_ggLin ι]
    exact hcard
  have hfrV : Module.finrank (ZMod 3) V = 5 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [hcardV, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  let E : Subgroup G := Subgroup.closure ({x, z} : Set G)
  have hE9 : Nat.card E = 3 ^ 2 := by
    change Nat.card (Subgroup.closure ({x, z} : Set G)) = 3 ^ 2
    exact hD
  have hEBs : E ≤ Bs := by
    rw [show E = Subgroup.closure ({x, z} : Set G) from rfl, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hxBs
    · exact hzBs
  let K : Subgroup ↥Bs :=
    { carrier := {b | ι (Additive.ofMul b) ∈ D'}
      one_mem' := by
        change ι (Additive.ofMul (1 : ↥Bs)) ∈ D'
        simp
      mul_mem' := by
        intro a b ha hb
        change ι (Additive.ofMul (a * b)) ∈ D'
        rw [ofMul_mul, map_add]
        exact D'.add_mem ha hb
      inv_mem' := by
        intro a ha
        change ι (Additive.ofMul a⁻¹) ∈ D'
        rw [ofMul_inv, map_neg]
        exact D'.neg_mem ha }
  have hx'K : x' ∈ K := by
    change ι (Additive.ofMul x') ∈ D'
    exact Submodule.subset_span (by simp [vx])
  have hz'K : z' ∈ K := by
    change ι (Additive.ofMul z') ∈ D'
    exact Submodule.subset_span (by simp [vz])
  have hclosure : Subgroup.closure ({x', z'} : Set ↥Bs) ≤ K := by
    rw [Subgroup.closure_le]
    intro b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact hx'K
    · exact hz'K
  have hEsub : E.subgroupOf Bs = Subgroup.closure ({x', z'} : Set ↥Bs) := by
    apply Subgroup.map_injective Bs.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hEBs]
    rw [show E = Subgroup.closure ({x, z} : Set G) from rfl]
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    simp [x', z']
  have hmem : ∀ (y : G) (hy : y ∈ E),
      ι (Additive.ofMul (⟨y, hEBs hy⟩ : ↥Bs)) ∈ D' := by
    intro y hy
    have hb : (⟨y, hEBs hy⟩ : ↥Bs) ∈ E.subgroupOf Bs := by
      rw [Subgroup.mem_subgroupOf]
      exact hy
    rw [hEsub] at hb
    exact hclosure hb
  have hE9le : 3 ^ 2 ≤ Nat.card D' := by
    let g : E → D' := fun b =>
      ⟨ι (Additive.ofMul (⟨(b : G), hEBs b.2⟩ : ↥Bs)), hmem (b : G) b.2⟩
    have hg_inj : Function.Injective g := by
      intro b1 b2 h
      apply Subtype.ext
      have h' : ι (Additive.ofMul (⟨(b1 : G), hEBs b1.2⟩ : ↥Bs)) =
          ι (Additive.ofMul (⟨(b2 : G), hEBs b2.2⟩ : ↥Bs)) := by
        simpa [g] using congrArg (fun w : D' => (w : V)) h
      have h'' := ι.injective h'
      have h3 := Additive.ofMul.injective h''
      exact congrArg (fun w : ↥Bs => (w : G)) h3
    rw [← hE9]
    exact Nat.card_le_card_of_injective g hg_inj
  have hcardD'_le : Nat.card D' ≤ 3 ^ 2 := by
    have hsurj : Function.Surjective (fun p : ZMod 3 × ZMod 3 =>
        (⟨p.1 • vx + p.2 • vz, by
          change p.1 • vx + p.2 • vz ∈ Submodule.span (ZMod 3) ({vx, vz} : Set V)
          exact (Submodule.mem_span_pair (R := ZMod 3) (x := vx) (y := vz)).mpr
            ⟨p.1, p.2, rfl⟩⟩ : D')) := by
      intro w
      have hw : (w : V) ∈ Submodule.span (ZMod 3) ({vx, vz} : Set V) := w.2
      obtain ⟨a, b, hab⟩ :=
        (Submodule.mem_span_pair (R := ZMod 3) (x := vx) (y := vz)).mp hw
      exact ⟨(a, b), Subtype.ext hab⟩
    calc Nat.card D' ≤ Nat.card (ZMod 3 × ZMod 3) :=
          Nat.card_le_card_of_surjective _ hsurj
      _ = 3 ^ 2 := by
          rw [Nat.card_prod, Nat.card_zmod]
          norm_num
  have hcardD' : Nat.card D' = 3 ^ 2 := le_antisymm hcardD'_le hE9le
  have hfrD' : Module.finrank (ZMod 3) D' = 2 := by
    have : Module.Finite (ZMod 3) D' := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := D')
    rw [hcardD', Nat.card_zmod] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  let T : V ≃ₗ[ZMod 3] V := ggLin (p := 3) ι (φ : MulAut ↥Bs)
  have hfixx : T vx = vx := by
    have h := (hH (φ : MulAut ↥Bs) φ.2).1
    exact (ggLin_fix_iff (p := 3) ι (φ : MulAut ↥Bs) x').mp h
  have hfixz : T vz = vz := by
    have h := (hH (φ : MulAut ↥Bs) φ.2).2
    exact (ggLin_fix_iff (p := 3) ι (φ : MulAut ↥Bs) z').mp h
  have hfixD' : ∀ v ∈ D', T v = v := by
    intro v hv
    refine Submodule.span_induction (p := fun w _ => T w = w) ?_ ?_ ?_ ?_ hv
    · intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact hfixx
      · exact hfixz
    · simp
    · intro a b ha hb iha ihb
      rw [map_add, iha, ihb]
    · intro c w hw ihw
      rw [map_smul, ihw]
  have hψord : orderOf (φ : MulAut ↥Bs) = 5 :=
    (orderOf_injective H.subtype H.subtype_injective φ).trans hφord
  have hψ5 : (φ : MulAut ↥Bs) ^ 5 = 1 := by
    rw [← hψord]
    exact pow_orderOf_eq_one _
  have hT5 : T ^ 5 = 1 := by
    have := map_pow (ggLin (p := 3) ι) (φ : MulAut ↥Bs) 5
    rw [hψ5, map_one] at this
    exact this.symm
  have hψ_ne : (φ : MulAut ↥Bs) ≠ 1 := by
    intro h1
    have hord1 : orderOf (φ : MulAut ↥Bs) = 1 := by rw [h1]; exact orderOf_one
    rw [hψord] at hord1
    exact absurd hord1 (by norm_num)
  have hT_ne : T ≠ 1 := by
    intro hT
    apply hψ_ne
    have h : (ggLin (p := 3) ι) (φ : MulAut ↥Bs) = (ggLin (p := 3) ι) 1 := by
      rw [map_one]
      exact hT
    exact ggLin_injective (p := 3) ι h
  have hmap : Submodule.map (T : V →ₗ[ZMod 3] V) D' = D' := by
    apply le_antisymm
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
      simpa [hfixD' v hv] using hv
    · intro v hv
      exact Submodule.mem_map.mpr ⟨v, hv, hfixD' v hv⟩
  let W : Type := V ⧸ D'
  let Tq : W ≃ₗ[ZMod 3] W := Submodule.Quotient.equiv D' D' T hmap
  have hTq_apply : ∀ v : V, Tq (Submodule.Quotient.mk v) = Submodule.Quotient.mk (T v) := by
    intro v
    rw [show Tq = Submodule.Quotient.equiv D' D' T hmap from rfl]
    rw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
    rfl
  have hTq_pow : ∀ (n : ℕ) (v : V),
      (Tq ^ n) (Submodule.Quotient.mk v) = Submodule.Quotient.mk ((T ^ n) v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, hTq_apply, ih]
      congr 1
  have hTq5 : Tq ^ 5 = 1 := by
    apply LinearEquiv.ext
    intro w
    refine Submodule.Quotient.induction_on D' w ?_
    intro v
    rw [hTq_pow 5 v, hT5]
    rfl
  have hWfr : Module.finrank (ZMod 3) W = 3 := by
    have h := Submodule.finrank_quotient_add_finrank D'
    rw [hfrD', hfrV] at h
    change Module.finrank (ZMod 3) (V ⧸ D') = 3
    omega
  have : Finite W := by
    change Finite (V ⧸ D')
    exact Finite.of_surjective (Submodule.Quotient.mk (p := D'))
      (Submodule.Quotient.mk_surjective D')
  have hnot5 : ¬ 5 ∣ Nat.card (W ≃ₗ[ZMod 3] W) :=
    r4k_not_five_dvd_card_linearEquiv hWfr
  have hcopW : Nat.Coprime 5 (Nat.card (W ≃ₗ[ZMod 3] W)) :=
    (Nat.prime_five.coprime_iff_not_dvd).mpr hnot5
  have hTq1 : Tq = 1 := by
    have hord1 : orderOf Tq = 1 :=
      Nat.eq_one_of_dvd_coprimes hcopW (orderOf_dvd_iff_pow_eq_one.mpr hTq5)
        (orderOf_dvd_natCard Tq)
    exact orderOf_eq_one_iff.mp hord1
  have hNmem : ∀ v : V, T v - v ∈ D' := by
    intro v
    have h := congrArg (fun e : W ≃ₗ[ZMod 3] W => e (Submodule.Quotient.mk v)) hTq1
    rw [hTq_apply] at h
    have h' : Submodule.Quotient.mk (p := D') (T v) =
        Submodule.Quotient.mk (p := D') v := by simpa using h
    have hzero : Submodule.Quotient.mk (p := D') (T v - v) = 0 := by
      rw [show Submodule.Quotient.mk (p := D') (T v - v) =
          Submodule.Quotient.mk (p := D') (T v) - Submodule.Quotient.mk (p := D') v from
        map_sub (Submodule.mkQ D') (T v) v, h', sub_self]
    exact (Submodule.Quotient.mk_eq_zero D').mp hzero
  have hND : ∀ v ∈ D', T v - v = 0 := by
    intro v hv
    rw [hfixD' v hv, sub_self]
  have hTN : ∀ v : V, T (T v - v) = T v - v := by
    intro v
    exact sub_eq_zero.mp (hND (T v - v) (hNmem v))
  have hT_pow : ∀ (n : ℕ) (v : V), (T ^ n) v = v + n • (T v - v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih]
      calc T v + n • (T (T v) - T v)
          = T v + n • (T v - v) := by rw [← map_sub, hTN]
        _ = v + (n + 1) • (T v - v) := by
            have hTv : T v = v + (T v - v) := (add_sub_cancel v (T v)).symm
            nth_rewrite 1 [hTv]
            rw [add_assoc]
            congr 1
            rw [add_comm, ← succ_nsmul]
  have h5N : ∀ v : V, 5 • (T v - v) = 0 := by
    intro v
    have h := hT_pow 5 v
    rw [hT5] at h
    have h' : v + 5 • (T v - v) = v + 0 := by simpa using h.symm
    exact add_left_cancel h'
  have hN0 : ∀ v : V, T v - v = 0 := by
    intro v
    have h5 := h5N v
    have h3 : (3 : ℕ) • (T v - v) = 0 := ZModModule.char_nsmul_eq_zero 3 (T v - v)
    have h2 : (2 : ℕ) • (T v - v) = 0 := by
      have hmod := nsmul_eq_mod_nsmul (a := T v - v) (n := 3) 5 h3
      rw [hmod] at h5
      simpa using h5
    have hdvd2 : addOrderOf (T v - v) ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero h2
    have hdvd3 : addOrderOf (T v - v) ∣ 3 := addOrderOf_dvd_of_nsmul_eq_zero h3
    have h1 : addOrderOf (T v - v) ∣ 1 := by
      have h := Nat.dvd_gcd hdvd2 hdvd3
      rwa [show Nat.gcd 2 3 = 1 by decide] at h
    have hw1 : (1 : ℕ) • (T v - v) = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp h1
    simpa using hw1
  have hT1 : T = 1 := by
    apply LinearEquiv.ext
    intro v
    exact sub_eq_zero.mp (hN0 v)
  exact hT_ne hT1


end CFSG.StandardType
