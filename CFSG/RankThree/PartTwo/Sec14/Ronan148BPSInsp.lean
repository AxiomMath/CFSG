module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSCompC
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13
open scoped commutatorElement

@[expose] def ThreeSolv148 (X : Type) [Group X] [Finite X] : Prop :=
  ∀ V : Subgroup X, Nat.Coprime 3 (Nat.card V) → Group.IsSolvable V

@[expose] def ThreeSolvInv148 (X : Type) [Group X] [Finite X] (P : Subgroup (MulAut X)) : Prop :=
  ∀ V : Subgroup X, Nat.Coprime 3 (Nat.card V) → (∀ p ∈ P, ∀ v ∈ V, (p : MulAut X) v ∈ V) →
    Group.IsSolvable V

@[expose] def RankTwo148 (X : Type) [Group X] : Prop :=
  ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≠ 27

@[expose] def SigGen148 (X : Type) [Group X] [Finite X] (P : Subgroup (MulAut X)) : Prop :=
  ∀ K Q D : Subgroup (MulAut X), K ≤ (MulAut.conj : X →* MulAut X).range →
    Q ≤ (MulAut.conj : X →* MulAut X).range → Group.IsPerfect K →
    IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) → 3 ∣ Nat.card K →
    P ≤ Subgroup.normalizer (K : Set (MulAut X)) →
    (∀ p ∈ P, (∀ k ∈ K, p * k * p⁻¹ * k⁻¹ ∈ (aschbacherSolvableCore 3 ↥K).map K.subtype) →
      p = 1) →
    IsHyperplane P D → Q ≤ Subgroup.centralizer (D : Set (MulAut X)) →
    Q ∈ invariantPiSubgroups ⊤ P (piCompl 3) → Q = ⁅Q, P⁆ →
    Q ≤ Subgroup.normalizer (K : Set (MulAut X)) →
    ¬ ⁅K, Q⁆ ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype →
    K ≤ sSup {V : Subgroup (MulAut X) | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ P (piCompl 3) ∧
      V = ⁅V, P⁆}

namespace PS

variable {X : Type} [Group X] [Finite X]

theorem conj_injective (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [← hZ, Subgroup.mem_center_iff]
  intro y
  have := congrArg (fun φ : MulAut X => φ y) hx
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc y * x = x * y * x⁻¹ * x := by rw [this]
    _ = x * y := by group

noncomputable def innEquiv (hZ : Subgroup.center X = ⊥) {V : Subgroup (MulAut X)}
    (hV : V ≤ (MulAut.conj : X →* MulAut X).range) :
    ↥(V.comap (MulAut.conj : X →* MulAut X)) ≃* ↥V :=
  (V.comap (MulAut.conj : X →* MulAut X)).equivMapOfInjective _ (conj_injective hZ) |>.trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hV))

theorem rankTwo_inn (hZ : Subgroup.center X = ⊥) (hb : RankTwo148 X)
    {E : Subgroup (MulAut X)} (hE : E ≤ (MulAut.conj : X →* MulAut X).range)
    (hEa : CFSG.Assembly.IsElemAbelian 3 E) : Nat.card E ≠ 27 := by
  have e := innEquiv hZ hE
  have h1 : CFSG.Assembly.IsElemAbelian 3 (E.comap (MulAut.conj : X →* MulAut X)) := by
    refine ⟨⟨⟨fun u v => e.injective ?_⟩⟩, fun x hx => ?_⟩
    · rw [map_mul, map_mul]
      exact hEa.1.is_comm.comm _ _
    · apply conj_injective hZ
      rw [map_pow, map_one]
      exact hEa.2 _ hx
  rw [← Nat.card_congr e.toEquiv]
  exact hb _ h1

theorem inSubgroup_theta_map_injective {G G' : Type*} [Group G] [Group G'] [Finite G]
    (f : G →* G') (hf : Function.Injective f) (K : Subgroup G) :
    inSubgroup (aschbacherSolvableCore 3) (K.map f) =
      (inSubgroup (aschbacherSolvableCore 3) K).map f := by
  set e : ↥K ≃* ↥(K.map f) := K.equivMapOfInjective f hf with he
  have hθ : (aschbacherSolvableCore 3 ↥K).map e.toMonoidHom = aschbacherSolvableCore 3 ↥(K.map f) :=
    CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  have hcomp : (K.map f).subtype.comp e.toMonoidHom = f.comp K.subtype := by
    ext x
    rfl
  rw [inSubgroup, inSubgroup, ← hθ, Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem conj_apply_eq (α : MulAut X) (x : X) :
    MulAut.conj (α x) = α * MulAut.conj x * α⁻¹ := by
  ext y
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]

theorem pPrimeCore_thetaQuot_eq_bot_of_inv (hZ : Subgroup.center X = ⊥)
    {P W : Subgroup (MulAut X)} (hWinn : W ≤ (MulAut.conj : X →* MulAut X).range)
    (hPW : P ≤ Subgroup.normalizer (W : Set (MulAut X))) (ha : ThreeSolvInv148 X P) :
    CFSG.pPrimeCore 3 (↥W ⧸ aschbacherSolvableCore 3 ↥W) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hchar, h3θ, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥W) Nat.prime_three
  haveI : (aschbacherSolvableCore 3 ↥W).Normal := by haveI := hchar; infer_instance
  haveI := theta_characteristic ↥W
  set θ := aschbacherSolvableCore 3 ↥W with hθ
  set mk := QuotientGroup.mk' θ with hmk
  set O := CFSG.pPrimeCore 3 (↥W ⧸ θ) with hO
  set N : Subgroup ↥W := O.comap mk with hN
  have hNn : N.Normal := Subgroup.Normal.comap inferInstance mk
  have hker : mk.ker ≤ N := MonoidHom.ker_le_comap mk O
  have hmap : N.map mk = O :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective θ) O
  have hcard : Nat.card N = Nat.card O * Nat.card θ := by
    have h := card_map_mul_card_ker_of_le' mk hker
    rw [hmap, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hN3 : Nat.Coprime 3 (Nat.card N) := by
    rw [hcard]
    exact Nat.Coprime.mul_right CFSG.pPrimeCore_coprime_card
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3θ)
  have hNinv : ∀ (p : ↥P) (w : ↥W), w ∈ N → conjAct hPW p w ∈ N := by
    intro p w hw
    change mk (conjAct hPW p w) ∈ O
    have h1 : mk (conjAct hPW p w) = thetaAct hPW p (mk w) := (thetaAct_mk hPW p w).symm
    rw [h1]
    have hfix := (CFSG.pPrimeCore_characteristic (p := 3)
      (G := ↥W ⧸ θ)).fixed (thetaAct hPW p)
    rw [← hO] at hfix
    have : mk w ∈ O.comap (thetaAct hPW p).toMonoidHom := by rw [hfix]; exact hw
    exact this
  set NX : Subgroup (MulAut X) := N.map W.subtype with hNX
  have hNXinn : NX ≤ (MulAut.conj : X →* MulAut X).range :=
    (Subgroup.map_subtype_le N).trans hWinn
  set V : Subgroup X := NX.comap (MulAut.conj : X →* MulAut X) with hV
  have eV := innEquiv hZ hNXinn
  have eN : ↥N ≃* ↥NX := N.equivMapOfInjective W.subtype W.subtype_injective
  have hV3 : Nat.Coprime 3 (Nat.card V) := by
    rw [Nat.card_congr eV.toEquiv, ← Nat.card_congr eN.toEquiv]
    exact hN3
  have hVinv : ∀ p ∈ P, ∀ v ∈ V, (p : MulAut X) v ∈ V := by
    intro p hp v hv
    change MulAut.conj (p v) ∈ NX
    rw [conj_apply_eq]
    obtain ⟨w, hw, hwv⟩ := (hv : MulAut.conj v ∈ NX)
    refine ⟨conjAct hPW ⟨p, hp⟩ w, hNinv ⟨p, hp⟩ w hw, ?_⟩
    rw [Subgroup.coe_subtype, conjAct_apply]
    change (p : MulAut X) * (w : MulAut X) * (p : MulAut X)⁻¹ = _
    rw [← hwv]
    rfl
  have hVsol := ha V hV3 hVinv
  have hNsol : Group.IsSolvable N := by
    have : Group.IsSolvable NX :=
      Group.isSolvable_of_surjective (f := eV.toMonoidHom) eV.surjective
    exact Group.isSolvable_of_surjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  have hNθ : N ≤ θ := hmax N hNn hNsol
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3)
  rw [← hmap, eq_bot_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hNθ hy

end PS

section Reduction

variable {X : Type} [Group X] [Finite X]

open PS in
theorem sigImg148_of_insp (hZ : Subgroup.center X = ⊥) {P : Subgroup (MulAut X)}
    (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) (ha : ThreeSolvInv148 X P)
    (hb : RankTwo148 X) (hc : SigGen148 X P) : SigImg148 X P := by
  classical
  intro W Q D hWinn hPW hD hQWD hQinv hQP hsig hQO
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := theta_characteristic ↥W
  set Ws := ↥W ⧸ aschbacherSolvableCore 3 ↥W
  set mk := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥W) with hmk
  have hPp : IsPGroup 3 P := fun g => ⟨1, Subtype.ext (by simpa using hP.2 g g.2)⟩
  have hDp : IsPGroup 3 D := hPp.to_le hD.1
  have hDW : D ≤ Subgroup.normalizer (W : Set (MulAut X)) := hD.1.trans hPW
  have hQW : Q ≤ W := hQWD.trans inf_le_left
  have hQD : Q ≤ Subgroup.centralizer (D : Set (MulAut X)) := hQWD.trans inf_le_right
  have hQ3 : Nat.Coprime 3 (Nat.card Q) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_
    exact (hQinv.2.1 ⟨3, Nat.prime_three⟩ h3) rfl
  have ha' := pPrimeCore_thetaQuot_eq_bot_of_inv hZ hWinn hPW ha
  have hb' : ∀ E : Subgroup (MulAut X), E ≤ W → CFSG.Assembly.IsElemAbelian 3 E →
      Nat.card E ≠ 27 := fun E hEW hE => rankTwo_inn hZ hb (hEW.trans hWinn) hE
  have hQOD := hsig D hD Q hQWD hQinv hQP
  set Qs : Subgroup Ws := (Q.subgroupOf W).map mk with hQs
  have hQs1 : Qs ≠ ⊥ := map_ne_bot hQW hQO
  have hQs3 : Nat.Coprime 3 (Nat.card Qs) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQW).toEquiv]
  have hQsF := map_le_centralizer_pCore' hDp hDW hQW hQOD
  obtain ⟨J, hJ, hQJ'⟩ := exists_component_not_le_centralizer ha' hQs1 hQs3 hQsF
  have hinv : ∀ J' : Subgroup Ws, IsComponent J' → ∀ p : ↥P,
      J'.map (thetaAct hPW p).toMonoidHom = J' := fun J' hJ' p =>
    map_eq_of_noE27 hP hPW ha' hb' hJ' p
  have hQJ := le_normalizer_of_commutator hPW hQW hQP hinv hJ
  have hfaith : ∀ c (hc : c ∈ P), (∀ j ∈ J, thetaAct hPW ⟨c, hc⟩ j = j) → c = 1 :=
    fun c hc hcJ => eq_one_of_centralizes_component hP hP9 hPW hD hQW hQD hQP hQOD ha' hJ
      (hinv J hJ) hQJ hQJ' hc hcJ
  obtain ⟨hK'mem, hK'J⟩ := perfectResidual_comap_mem_thetaComponents Nat.prime_three hJ
  set K' : Subgroup ↥W := inSubgroup perfectResidual (J.comap mk) with hK'
  set K : Subgroup (MulAut X) := K'.map W.subtype with hK
  have hKmem : K ∈ thetaComponentsIn W := ⟨K', hK'mem, rfl⟩
  have hKW : K ≤ W := Subgroup.map_subtype_le K'
  have hfixK' : ∀ (σ : MulAut ↥W) (τ : MulAut Ws), (∀ w, τ (mk w) = mk (σ w)) →
      J.map τ.toMonoidHom = J → K'.map σ.toMonoidHom = K' := by
    intro σ τ hστ hτJ
    have hcomap : (J.comap mk).map σ.toMonoidHom = J.comap mk := by
      ext w
      constructor
      · rintro ⟨v, hv, rfl⟩
        change mk (σ v) ∈ J
        rw [← hστ, ← hτJ]
        exact ⟨mk v, hv, rfl⟩
      · intro hw
        refine ⟨σ.symm w, ?_, σ.apply_symm_apply w⟩
        change mk (σ.symm w) ∈ J
        have h1 : τ (mk (σ.symm w)) = mk w := by rw [hστ, σ.apply_symm_apply]
        have h2 : mk w ∈ J.map τ.toMonoidHom := by rw [hτJ]; exact hw
        obtain ⟨j, hj, hjw⟩ := h2
        have : j = mk (σ.symm w) := τ.injective (hjw.trans h1.symm)
        rw [← this]
        exact hj
    rw [hK', CFSG.RankThree.PartTwo.map_inSubgroup_perfectResidual, hcomap]
  have hPK : P ≤ Subgroup.normalizer (K : Set (MulAut X)) := by
    intro p hp
    have hmap := hfixK' (conjAct hPW ⟨p, hp⟩) (thetaAct hPW ⟨p, hp⟩)
      (fun w => thetaAct_mk hPW ⟨p, hp⟩ w) (hinv J hJ ⟨p, hp⟩)
    refine mem_normalizer_of_conj_le fun k hk => ?_
    obtain ⟨k', hk', rfl⟩ := hk
    refine ⟨conjAct hPW ⟨p, hp⟩ k', ?_, rfl⟩
    rw [← hmap]
    exact ⟨k', hk', rfl⟩
  have hQK : Q ≤ Subgroup.normalizer (K : Set (MulAut X)) := by
    intro q hq
    have hqW := hQW hq
    have hqN : mk ⟨q, hqW⟩ ∈ Subgroup.normalizer (J : Set Ws) :=
      hQJ ⟨⟨q, hqW⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    have hτJ : J.map (MulAut.conj (mk ⟨q, hqW⟩)).toMonoidHom = J := by
      ext j
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hqN i).mp hi
      · intro hj
        refine ⟨(mk ⟨q, hqW⟩)⁻¹ * j * mk ⟨q, hqW⟩, ?_, by
          simp [MulAut.conj_apply, mul_assoc]⟩
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hqN) j).mp hj
        rwa [inv_inv] at this
    have hmap := hfixK' (MulAut.conj ⟨q, hqW⟩) (MulAut.conj (mk ⟨q, hqW⟩))
      (fun w => by simp [MulAut.conj_apply]) hτJ
    refine mem_normalizer_of_conj_le fun k hk => ?_
    obtain ⟨k', hk', rfl⟩ := hk
    refine ⟨MulAut.conj ⟨q, hqW⟩ k', ?_, rfl⟩
    rw [← hmap]
    exact ⟨k', hk', rfl⟩
  set eK : ↥K' ≃* ↥K := K'.equivMapOfInjective W.subtype W.subtype_injective with heK
  have hKperf : Group.IsPerfect K := by
    have := hK'mem.1
    exact Group.IsPerfect.ofSurjective (f := eK.toMonoidHom) eK.surjective
  have hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ eK (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three eK)) hK'mem.2.2
  have h3J := three_dvd_card_of_isComponent ha' hJ
  have h3K : 3 ∣ Nat.card K := by
    rw [hK, Subgroup.card_map_of_injective W.subtype_injective]
    exact h3J.trans (hK'J ▸ Subgroup.card_map_dvd _ _)
  have hθK : ∀ y ∈ (aschbacherSolvableCore 3 ↥K).map K.subtype,
      ∃ hyW : y ∈ W, mk ⟨y, hyW⟩ = 1 := by
    intro y hy
    have hsub : inSubgroup (aschbacherSolvableCore 3) K' =
        K' ⊓ aschbacherSolvableCore 3 ↥W :=
      solvable_prime_complement_core_subnormal_intersection Nat.prime_three hK'mem.2.1
    have hmapθ : (aschbacherSolvableCore 3 ↥K).map K.subtype =
        (inSubgroup (aschbacherSolvableCore 3) K').map W.subtype :=
      inSubgroup_theta_map_injective W.subtype W.subtype_injective K'
    rw [hmapθ, hsub] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨w.2, ?_⟩
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hw.2
  have hJK' : ∀ j ∈ J, ∃ k' ∈ K', mk k' = j := by
    intro j hj
    rw [← hK'J] at hj
    obtain ⟨k', hk', rfl⟩ := hj
    exact ⟨k', hk', rfl⟩
  have hfaithK : ∀ p ∈ P, (∀ k ∈ K, p * k * p⁻¹ * k⁻¹ ∈
      (aschbacherSolvableCore 3 ↥K).map K.subtype) → p = 1 := by
    intro p hp hpK
    refine hfaith p hp fun j hj => ?_
    obtain ⟨k', hk', rfl⟩ := hJK' j hj
    obtain ⟨hyW, hy1⟩ := hθK _ (hpK _ ⟨k', hk', rfl⟩)
    change thetaAct hPW ⟨p, hp⟩ ((k' : ↥W) : Ws) = ((k' : ↥W) : Ws)
    rw [thetaAct_mk]
    have e : (⟨p * W.subtype k' * p⁻¹ * (W.subtype k')⁻¹, hyW⟩ : ↥W) =
        conjAct hPW ⟨p, hp⟩ k' * k'⁻¹ := rfl
    rw [e, map_mul, map_inv, mul_inv_eq_one] at hy1
    exact hy1
  have hQKnt : ¬ ⁅K, Q⁆ ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype := by
    intro hle
    apply hQJ'
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    obtain ⟨k', hk', rfl⟩ := hJK' j hj
    have hqQ : (q : MulAut X) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    obtain ⟨hyW, hy1⟩ := hθK _ (hle (Subgroup.commutator_mem_commutator ⟨k', hk', rfl⟩ hqQ))
    have e : (⟨⁅W.subtype k', (q : MulAut X)⁆, hyW⟩ : ↥W) = ⁅k', q⁆ := rfl
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hy1
    exact hy1
  obtain hgen := hc K Q D (hKW.trans hWinn) (hQW.trans hWinn) hKperf hKq h3K hPK hfaithK hD hQD
    hQinv hQP hQK hQKnt
  exact ⟨K, hKmem, hPK, h3K, hgen⟩

end Reduction

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
