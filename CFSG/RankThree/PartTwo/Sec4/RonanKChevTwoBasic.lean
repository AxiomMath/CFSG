module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKFacts
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeCore

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open CFSG CFSG.RankThree.PartTwo.Sec4.Item462AltProof

section Conj

variable {X : Type*} [Group X]

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hyc : y ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut X => φ g) hy
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  rw [hZ, Subgroup.mem_bot] at hyc
  exact hyc

theorem mul_conj_mul_inv (β : MulAut X) (y : X) :
    β * MulAut.conj y * β⁻¹ = MulAut.conj (β y) := by
  ext m
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem conj_apply_eq_iff (x y : X) : MulAut.conj x y = y ↔ x * y = y * x := by
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]

theorem exists_conj_of_isInnerAut (hinj : Function.Injective (MulAut.conj : X →* MulAut X))
    {β : MulAut X} (hβ : orderOf β = 3) (hin : β ∈ (MulAut.conj : X →* MulAut X).range) :
    ∃ x : X, β = MulAut.conj x ∧ x ^ 3 = 1 ∧ x ≠ 1 := by
  obtain ⟨x, rfl⟩ := hin
  refine ⟨x, rfl, ?_, ?_⟩
  · apply hinj
    rw [map_pow, ← hβ, pow_orderOf_eq_one, map_one]
  · rintro rfl
    rw [map_one, orderOf_one] at hβ
    norm_num at hβ

end Conj

section Datum

variable {X : Type*} [Group X]

@[expose] def PullDatum (β : MulAut X) : Prop :=
  ∃ R U : Subgroup X, (∀ r ∈ R, β r = r) ∧ (∀ c : X, β c = c → ∀ r ∈ R, c * r * c⁻¹ ∈ R) ∧
    Group.IsSolvable R ∧ ¬ 3 ∣ Nat.card R ∧ U ≤ R ∧ IsPGroup 2 U ∧ ¬ IsCyclic U

theorem pullDatum_of_innThetaNoncyclic
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X)) {β : MulAut X}
    (h : InnThetaNoncyclic β) : PullDatum β := by
  obtain ⟨W, V, hWs, hW3, hWinn, hβW, hnorm, hVW, hV2, hVnc⟩ := h
  set R : Subgroup X := W.comap (MulAut.conj : X →* MulAut X) with hRdef
  set U : Subgroup X := V.comap (MulAut.conj : X →* MulAut X) with hUdef
  have hVrange : V ≤ (MulAut.conj : X →* MulAut X).range := fun v hv => hWinn (hVW hv)
  have hRmap : R.map (MulAut.conj : X →* MulAut X) = W := by
    rw [hRdef, Subgroup.map_comap_eq, inf_eq_right.mpr hWinn]
  have hUmap : U.map (MulAut.conj : X →* MulAut X) = V := by
    rw [hUdef, Subgroup.map_comap_eq, inf_eq_right.mpr hVrange]
  let eR : R ≃* W := (R.equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr hRmap)
  let eU : U ≃* V := (U.equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr hUmap)
  refine ⟨R, U, ?_, ?_, ?_, ?_, fun u hu => hVW hu, ?_, ?_⟩
  · intro r hr
    have hr' : MulAut.conj r ∈ W := hr
    have h2 : β * MulAut.conj r * β⁻¹ = MulAut.conj r := by
      rw [hβW _ hr', mul_inv_cancel_right]
    rw [mul_conj_mul_inv] at h2
    exact hinj h2
  · intro c hc r hr
    have h := hnorm c hc _ (show MulAut.conj r ∈ W from hr)
    show MulAut.conj (c * r * c⁻¹) ∈ W
    rwa [map_mul, map_mul, map_inv]
  · haveI := hWs
    exact Group.isSolvable_of_isSolvable_injective (f := eR.toMonoidHom) eR.injective
  · rw [Nat.card_congr eR.toEquiv]
    exact hW3
  · exact hV2.of_equiv eU.symm
  · intro hU
    exact hVnc (isCyclic_of_surjective eU.toMonoidHom eU.surjective)

theorem PullDatum.congr {Y : Type*} [Group Y] (e : X ≃* Y) {β : MulAut X} (h : PullDatum β) :
    PullDatum (MulAut.congr e β) := by
  obtain ⟨R, U, hfix, hnorm, hsol, h3, hUR, hU2, hUnc⟩ := h
  have hfix' : ∀ c : Y, MulAut.congr e β c = c ↔ β (e.symm c) = e.symm c := by
    intro c
    change e (β (e.symm c)) = c ↔ _
    constructor
    · intro hc
      apply e.injective
      rw [hc, MulEquiv.apply_symm_apply]
    · intro hc
      rw [hc, MulEquiv.apply_symm_apply]
  let eR : R ≃* R.map e.toMonoidHom := R.equivMapOfInjective e.toMonoidHom e.injective
  let eU : U ≃* U.map e.toMonoidHom := U.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨R.map e.toMonoidHom, U.map e.toMonoidHom, ?_, ?_, ?_, ?_, Subgroup.map_mono hUR, ?_,
    ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    rw [hfix']
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hfix r hr
  · rintro c hc _ ⟨r, hr, rfl⟩
    rw [hfix'] at hc
    refine ⟨e.symm c * r * (e.symm c)⁻¹, hnorm _ hc r hr, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · haveI := hsol
    exact Group.isSolvable_of_isSolvable_injective (f := eR.symm.toMonoidHom) eR.symm.injective
  · rw [← Nat.card_congr eR.toEquiv]
    exact h3
  · exact hU2.of_equiv eU
  · intro hc
    exact hUnc (isCyclic_of_surjective eU.symm.toMonoidHom eU.symm.surjective)

theorem not_innThetaNoncyclic_of_mulEquiv {Y : Type*} [Group Y] (e : X ≃* Y)
    (hZ : Subgroup.center X = ⊥)
    (hY : ∀ β : MulAut Y, orderOf β = 3 → ¬ PullDatum β) (β : MulAut X) (hβ : orderOf β = 3) :
    ¬ InnThetaNoncyclic β := by
  intro h
  refine hY (MulAut.congr e β) ?_
    ((pullDatum_of_innThetaNoncyclic (conj_injective_of_center_eq_bot hZ) h).congr e)
  rw [MulEquiv.orderOf_eq, hβ]

theorem PullDatum.conj {β : MulAut X} (h : PullDatum β) (α : MulAut X) :
    PullDatum (α * β * α⁻¹) := by
  have h' := h.congr α
  have heq : MulAut.congr α β = α * β * α⁻¹ := by
    ext x
    rfl
  rwa [heq] at h'

theorem PullDatum.conj_inner {x : X} (h : PullDatum (MulAut.conj x)) (g : X) :
    PullDatum (MulAut.conj (g * x * g⁻¹)) := by
  have h' := h.conj (MulAut.conj g)
  rwa [mul_conj_mul_inv, MulAut.conj_apply] at h'

end Datum

section Quasisimple

variable {X : Type*} [Group X]

theorem not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  intro hs
  obtain ⟨-, hsimple, a, b, hab⟩ := hQ
  haveI := hsimple
  have : Group.IsSolvable (Q ⧸ Subgroup.center Q) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (Subgroup.center Q))
      (QuotientGroup.mk'_surjective _)
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := Q ⧸ Subgroup.center Q)).2 this a b)

theorem commute_of_quasisimple {R T : Subgroup X} (hRs : Group.IsSolvable R)
    (hTq : IsQuasisimple T) (hRT : ∀ t ∈ T, ∀ r ∈ R, t * r * t⁻¹ ∈ R)
    (hTR : ∀ r ∈ R, ∀ t ∈ T, r * t * r⁻¹ ∈ T) : ∀ r ∈ R, ∀ t ∈ T, r * t = t * r := by
  set N : Subgroup T := (R ⊓ T).subgroupOf T with hNdef
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hNdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨hRT g g.2 n hn.1, mul_mem (mul_mem g.2 hn.2) (inv_mem g.2)⟩
  have hNs : Group.IsSolvable N := by
    haveI := hRs
    let f : N →* R :=
      { toFun := fun n => ⟨(n : T), (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp n.2)).1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z : R => (z : X)) hab))
  have hNZ : N ≤ Subgroup.center T := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hTq hNn with htop | hle
    · exfalso
      apply not_isSolvable_of_isQuasisimple hTq
      haveI := hNs
      have e : N ≃* T := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    · exact hle
  intro r hr
  have hc : ∀ t : T, (⟨r * t * r⁻¹ * (t : X)⁻¹, mul_mem (hTR r hr t t.2) (inv_mem t.2)⟩ : T) ∈
      Subgroup.center T := by
    intro t
    apply hNZ
    rw [hNdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨?_, mul_mem (hTR r hr t t.2) (inv_mem t.2)⟩
    have h1 : (t : X) * r⁻¹ * (t : X)⁻¹ ∈ R := hRT t t.2 _ (inv_mem hr)
    have h2 := mul_mem hr h1
    simpa only [mul_assoc] using h2
  let χ : T →* Subgroup.center T :=
    { toFun := fun t => ⟨_, hc t⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        simp
      map_mul' := fun t s => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_mk]
        have hz := Subgroup.mem_center_iff.mp (hc s) ⟨r * t * r⁻¹, hTR r hr t t.2⟩
        have hz' := congrArg (fun z : T => (z : X)) hz
        simp only [Subgroup.coe_mul, Subgroup.coe_mk] at hz'
        calc r * (↑t * ↑s) * r⁻¹ * (↑t * ↑s)⁻¹
            = (r * ↑t * r⁻¹) * (r * ↑s * r⁻¹ * (↑s)⁻¹) * (↑t)⁻¹ := by group
          _ = (r * ↑s * r⁻¹ * (↑s)⁻¹) * (r * ↑t * r⁻¹) * (↑t)⁻¹ := by rw [hz']
          _ = r * ↑t * r⁻¹ * (↑t)⁻¹ * (r * ↑s * r⁻¹ * (↑s)⁻¹) := by
              have hz2 := Subgroup.mem_center_iff.mp (hc s)
                ⟨r * t * r⁻¹ * (t : X)⁻¹, mul_mem (hTR r hr t t.2) (inv_mem t.2)⟩
              have hz2' := congrArg (fun z : T => (z : X)) hz2
              simp only [Subgroup.coe_mul, Subgroup.coe_mk] at hz2'
              calc (r * ↑s * r⁻¹ * (↑s)⁻¹) * (r * ↑t * r⁻¹) * (↑t)⁻¹
                  = (r * ↑s * r⁻¹ * (↑s)⁻¹) * (r * ↑t * r⁻¹ * (↑t)⁻¹) := by group
                _ = r * ↑t * r⁻¹ * (↑t)⁻¹ * (r * ↑s * r⁻¹ * (↑s)⁻¹) := hz2'.symm }
  have hker : commutator T ≤ χ.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro u _ v _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp (χ v).2 _
  intro t ht
  have hT : commutator T = ⊤ := hTq.1.commutator_eq_top
  have h1 : χ ⟨t, ht⟩ = 1 := hker (hT ▸ Subgroup.mem_top _)
  have h2 : r * t * r⁻¹ * t⁻¹ = 1 :=
    congrArg (fun z : Subgroup.center T => ((z : T) : X)) h1
  calc r * t = (r * t * r⁻¹ * t⁻¹) * (t * r) := by group
    _ = t * r := by rw [h2, one_mul]

end Quasisimple

section Kill

variable {X : Type*} [Group X]

theorem eq_one_of_isPGroup_two_of_odd {U : Subgroup X} (hU : IsPGroup 2 U) {u : X} (hu : u ∈ U)
    (hodd : Odd (orderOf u)) : u = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU) ⟨u, hu⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exfalso
    rw [hk] at hodd
    exact Nat.not_even_iff_odd.mpr hodd (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero k⟩)

theorem PullDatum.false_of_forall_odd {β : MulAut X} (h : PullDatum β)
    (hodd : ∀ R U : Subgroup X, (∀ r ∈ R, β r = r) →
      (∀ c : X, β c = c → ∀ r ∈ R, c * r * c⁻¹ ∈ R) → Group.IsSolvable R → ¬ 3 ∣ Nat.card R →
      U ≤ R → ∀ u ∈ U, Odd (orderOf u)) : False := by
  obtain ⟨R, U, hfix, hnorm, hsol, h3, hUR, hU2, hUnc⟩ := h
  apply hUnc
  have hbot : U = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    exact (Subgroup.mem_bot).mpr
      (eq_one_of_isPGroup_two_of_odd hU2 hu (hodd R U hfix hnorm hsol h3 hUR u hu))
  rw [hbot]
  infer_instance

theorem PullDatum.false_of_no_involution {β : MulAut X} (h : PullDatum β)
    (hinv : ∀ c : X, β c = c → c ^ 2 = 1 → c = 1) : False := by
  obtain ⟨R, U, hfix, -, -, -, hUR, hU2, hUnc⟩ := h
  apply hUnc
  have hbot : U = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU2) ⟨u, hu⟩
    rw [Subgroup.orderOf_mk] at hk
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact orderOf_eq_one_iff.mp hk
    · exfalso
      set c := u ^ (2 ^ k) with hc
      have hc2 : c ^ 2 = 1 := by
        rw [hc, ← pow_mul, ← pow_succ, ← hk, pow_orderOf_eq_one]
      have hcfix : β c = c := by rw [hc, map_pow, hfix u (hUR hu)]
      have hdvd : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (hinv c hcfix hc2)
      rw [hk] at hdvd
      have h1 := Nat.le_of_dvd (by positivity) hdvd
      have h2 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
  rw [hbot]
  infer_instance

theorem PullDatum.false_of_isCyclic_fixed {β : MulAut X} (h : PullDatum β)
    (hcyc : ∀ P : Subgroup X, IsPGroup 2 P → (∀ x ∈ P, β x = x) → IsCyclic P) : False := by
  obtain ⟨R, U, hfix, -, -, -, hUR, hU2, hUnc⟩ := h
  exact hUnc (hcyc U hU2 fun x hx => hfix x (hUR hx))

theorem PullDatum.false_of_quasisimple {β : MulAut X} (h : PullDatum β) (S : Subgroup X)
    (hSfix : ∀ s ∈ S, β s = s) (hSn : ∀ c : X, β c = c → ∀ s ∈ S, c * s * c⁻¹ ∈ S)
    (hSq : IsQuasisimple S)
    (hodd : ∀ c : X, β c = c → (∀ s ∈ S, c * s = s * c) → Odd (orderOf c)) : False := by
  refine h.false_of_forall_odd fun R U hfix hnorm hsol _ hUR u hu => ?_
  have hcomm := commute_of_quasisimple hsol hSq (fun t ht r hr => hnorm t (hSfix t ht) r hr)
    (fun r hr s hs => hSn r (hfix r hr) s hs)
  exact hodd u (hfix u (hUR hu)) fun s hs => hcomm u (hUR hu) s hs

theorem odd_orderOf_of_centralizes {C S : Subgroup X} [Finite X] (hSC : S ≤ C)
    (hSn : ∀ c ∈ C, ∀ s ∈ S, c * s * c⁻¹ ∈ S) (hZ : Odd (Nat.card (Subgroup.center S)))
    (hidx : Odd (S.relIndex C)) {c : X} (hc : c ∈ C) (hcS : ∀ s ∈ S, c * s = s * c) :
    Odd (orderOf c) := by
  have hN : (S.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hSn g g.2 n hn
  have hpow : (⟨c, hc⟩ : C) ^ (S.subgroupOf C).index ∈ S.subgroupOf C :=
    (S.subgroupOf C).pow_index_mem _
  rw [Subgroup.mem_subgroupOf] at hpow
  have hpow' : c ^ S.relIndex C ∈ S := by
    simpa [Subgroup.relIndex] using hpow
  have hcen : (⟨c ^ S.relIndex C, hpow'⟩ : S) ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_mk]
    exact ((Commute.pow_left (hcS s s.2) _).eq).symm
  have h1 : (⟨⟨c ^ S.relIndex C, hpow'⟩, hcen⟩ : Subgroup.center S) ^
      Nat.card (Subgroup.center S) = 1 := pow_card_eq_one'
  have h2 : c ^ (S.relIndex C * Nat.card (Subgroup.center S)) = 1 := by
    rw [pow_mul]
    exact congrArg (fun z : Subgroup.center S => ((z : S) : X)) h1
  exact (hidx.mul hZ).of_dvd_nat (orderOf_dvd_of_pow_eq_one h2)

theorem PullDatum.false_of_quasisimple_relIndex [Finite X] {β : MulAut X} (h : PullDatum β)
    (C : Subgroup X) (hC : ∀ x, x ∈ C ↔ β x = x) (S : Subgroup X) (hSC : S ≤ C)
    (hSn : ∀ c ∈ C, ∀ s ∈ S, c * s * c⁻¹ ∈ S) (hSq : IsQuasisimple S)
    (hZ : Odd (Nat.card (Subgroup.center S))) (hidx : Odd (S.relIndex C)) : False :=
  h.false_of_quasisimple S (fun s hs => (hC s).mp (hSC hs))
    (fun c hc s hs => hSn c ((hC c).mpr hc) s hs) hSq
    (fun c hc hcS => odd_orderOf_of_centralizes hSC hSn hZ hidx ((hC c).mpr hc) hcS)

theorem PullDatum.false_of_quasisimple_fixed [Finite X] {β : MulAut X} (h : PullDatum β)
    (C : Subgroup X) (hC : ∀ x, x ∈ C ↔ β x = x) (hCq : IsQuasisimple C)
    (hZ : Odd (Nat.card (Subgroup.center C))) : False :=
  h.false_of_quasisimple_relIndex C hC C le_rfl
    (fun c hc s hs => mul_mem (mul_mem hc hs) (inv_mem hc)) hCq hZ
    (by rw [Subgroup.relIndex_self]; exact odd_one)

theorem PullDatum.false_of_coreFreeAt {β : MulAut X} (h : PullDatum β)
    (hcf : CFSG.HardMathSupport.Timmesfeld.CrossChar.CoreFreeAt 3 β) : False := by
  obtain ⟨R, U, hfix, hnorm, -, h3, hUR, -, hUnc⟩ := h
  have hR : R = ⊥ := hcf.1 R (fun r hr => hfix r hr) (fun c hc r hr => hnorm c hc r hr)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  apply hUnc
  have hU : U = ⊥ := le_bot_iff.mp (hR ▸ hUR)
  rw [hU]
  infer_instance

theorem PullDatum.false_of_fieldCoreAt [Finite X]
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X)) {β : MulAut X} (h : PullDatum β)
    (hfc : CFSG.HardMathSupport.Timmesfeld.CrossChar.FieldCoreAt 3 β) : False := by
  obtain ⟨T, hTfix, hTn, hTq, -, hout⟩ := hfc
  obtain ⟨R, U, hfix, hnorm, hsol, h3, hUR, -, hUnc⟩ := h
  have hcomm := commute_of_quasisimple hsol hTq (fun t ht r hr => hnorm t (hTfix ht) r hr)
    (fun r hr t ht => hTn r (hfix r hr) t ht)
  have hR : R = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    apply hinj
    rw [map_one]
    apply hout
    ·
      have hd : orderOf (MulAut.conj r) ∣ Nat.card R := by
        have h1 : orderOf (MulAut.conj r) ∣ orderOf r := orderOf_map_dvd _ r
        have h2 : orderOf r ∣ Nat.card R := by
          rw [← Subgroup.orderOf_mk r hr]
          exact orderOf_dvd_natCard _
        exact h1.trans h2
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h => h3 (h.trans hd)
    · have h2 := mul_conj_mul_inv β r
      rw [hfix r hr] at h2
      calc MulAut.conj r * β = β * MulAut.conj r * β⁻¹ * β := by rw [h2]
        _ = β * MulAut.conj r := by group
    · intro t ht
      rw [MulAut.conj_apply, hcomm r hr t ht, mul_inv_cancel_right]
  apply hUnc
  have hU : U = ⊥ := le_bot_iff.mp (hR ▸ hUR)
  rw [hU]
  infer_instance

theorem PullDatum.false_of_localCore [Finite X]
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X)) {β : MulAut X} (h : PullDatum β)
    (B : Subgroup (MulAut X)) (hInnB : (MulAut.conj : X →* MulAut X).range ≤ B)
    (hBle : B ≤ (MulAut.conj : X →* MulAut X).range ⊔ Subgroup.zpowers β) (hβB : β ∈ B)
    (hcore : inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3)
      (Subgroup.centralizer ({⟨β, hβB⟩} : Set B)) = ⊥) : False := by
  obtain ⟨R, U, hfix, hnorm, hsol, h3, hUR, -, hUnc⟩ := h
  set Cb : Subgroup B := Subgroup.centralizer ({⟨β, hβB⟩} : Set B) with hCbdef
  have hRB : ∀ r ∈ R, MulAut.conj r ∈ B := fun r _ => hInnB ⟨r, rfl⟩
  have hRC : ∀ r (hr : r ∈ R), (⟨MulAut.conj r, hRB r hr⟩ : B) ∈ Cb := by
    intro r hr
    rw [hCbdef, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have h2 := mul_conj_mul_inv β r
    rw [hfix r hr] at h2
    have key : β * MulAut.conj r = MulAut.conj r * β := by
      calc β * MulAut.conj r = β * MulAut.conj r * β⁻¹ * β := by group
        _ = MulAut.conj r * β := by rw [h2]
    first | exact key | exact key.symm
  let φ : R →* Cb :=
    { toFun := fun r => ⟨⟨MulAut.conj (r : X), hRB r r.2⟩, hRC r r.2⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; apply Subtype.ext; simp }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have := congrArg (fun z : Cb => ((z : B) : MulAut X)) hab
    exact Subtype.ext (hinj this)
  set N : Subgroup Cb := φ.range with hNdef
  have hdecomp : ∀ g : Cb, ∃ y : X, β y = y ∧ ∃ i : ℤ,
      ((g : B) : MulAut X) = MulAut.conj y * β ^ i := by
    intro g
    have hgB : ((g : B) : MulAut X) ∈ (MulAut.conj : X →* MulAut X).range ⊔ Subgroup.zpowers β :=
      hBle (g : B).2
    haveI : ((MulAut.conj : X →* MulAut X).range).Normal := by
      refine ⟨fun n hn a => ?_⟩
      obtain ⟨y, rfl⟩ := hn
      exact ⟨a y, (mul_conj_mul_inv a y).symm⟩
    rw [Subgroup.mem_sup_of_normal_left] at hgB
    obtain ⟨_, ⟨y, rfl⟩, _, ⟨i, rfl⟩, hy⟩ := hgB
    refine ⟨y, ?_, i, hy.symm⟩
    have hgc : ((g : B) : MulAut X) * β = β * ((g : B) : MulAut X) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp g.2
      have h' := congrArg (fun z : B => (z : MulAut X)) this
      simp only [Subgroup.coe_mul] at h'
      first | exact h'.symm | exact h'
    rw [← hy] at hgc
    have hcomm : MulAut.conj y * β = β * MulAut.conj y := by
      have h1 : MulAut.conj y * β ^ i * β = β * (MulAut.conj y * β ^ i) := hgc
      have h2 : MulAut.conj y * β * β ^ i = β * MulAut.conj y * β ^ i := by
        calc MulAut.conj y * β * β ^ i = MulAut.conj y * β ^ i * β := by
              rw [mul_assoc, mul_assoc, ← zpow_one_add, ← zpow_add_one, add_comm]
          _ = β * (MulAut.conj y * β ^ i) := h1
          _ = β * MulAut.conj y * β ^ i := by rw [mul_assoc]
      exact mul_right_cancel h2
    have h3' : β * MulAut.conj y * β⁻¹ = MulAut.conj y := by
      rw [← hcomm]; group
    rw [mul_conj_mul_inv] at h3'
    exact hinj h3'
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨r, rfl⟩ := hn
    obtain ⟨y, hy, i, hg⟩ := hdecomp g
    have hyr : y * (r : X) * y⁻¹ ∈ R := hnorm y hy r r.2
    refine ⟨⟨y * r * y⁻¹, hyr⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv, hg]
    have hβr : ∀ j : ℤ, β ^ j * MulAut.conj (r : X) * (β ^ j)⁻¹ = MulAut.conj (r : X) := by
      intro j
      rw [mul_conj_mul_inv]
      congr 1
      have hfixr : β (r : X) = r := hfix r r.2
      induction j using Int.induction_on with
      | zero => simp
      | succ k ih =>
        rw [zpow_add_one, MulAut.mul_apply, hfixr, ih]
      | pred k ih =>
        rw [zpow_sub_one, MulAut.mul_apply]
        have : β⁻¹ (r : X) = r := by
          conv_lhs => rw [← hfixr]
          exact MulAut.inv_apply_self X β r
        rw [this, ih]
    calc MulAut.conj (y * r * y⁻¹)
        = MulAut.conj y * MulAut.conj (r : X) * (MulAut.conj y)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = MulAut.conj y * (β ^ i * MulAut.conj (r : X) * (β ^ i)⁻¹) * (MulAut.conj y)⁻¹ := by
          rw [hβr i]
      _ = MulAut.conj y * β ^ i * MulAut.conj (r : X) * (MulAut.conj y * β ^ i)⁻¹ := by group
  have hNs : Group.IsSolvable N := by
    haveI := hsol
    exact Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hN3 : ¬ 3 ∣ Nat.card N := by
    rw [hNdef, Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm]
    exact h3
  have hNle := (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
    (H := Cb) Nat.prime_three).2.2.2.1 N hNn hNs hN3
  have hR : R = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    have hmem : φ ⟨r, hr⟩ ∈ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 Cb :=
      hNle ⟨⟨r, hr⟩, rfl⟩
    have hmem' : ((φ ⟨r, hr⟩ : Cb) : B) ∈ inSubgroup
        (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3) Cb :=
      ⟨_, hmem, rfl⟩
    rw [hcore, Subgroup.mem_bot] at hmem'
    have h1 : MulAut.conj r = 1 := congrArg Subtype.val hmem'
    rw [Subgroup.mem_bot]
    exact hinj (h1.trans (map_one _).symm)
  apply hUnc
  have hU : U = ⊥ := le_bot_iff.mp (hR ▸ hUR)
  rw [hU]
  infer_instance

end Kill

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

end
