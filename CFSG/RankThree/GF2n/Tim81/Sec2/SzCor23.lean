module

public import CFSG.RankThree.GF2n.Tim81.Sec2.SzSmall
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedComm
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedUpper

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped Matrix

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.B45Sz CFSG.QuasithinUnique.Setup.X7
open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private theorem four_mul_two_pow_le_four_pow {b : ℕ} (hb : 2 ≤ b) :
    4 * 2 ^ b ≤ 4 ^ b := by
  have h : 2 + b ≤ 2 * b := by
    rw [two_mul]
    exact Nat.add_le_add_right hb b
  calc 4 * 2 ^ b = 2 ^ 2 * 2 ^ b := by norm_num
    _ = 2 ^ (2 + b) := (pow_add 2 2 b).symm
    _ ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right (by norm_num) h
    _ = 4 ^ b := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]

theorem isSzNatural_of_card_lt_fixedSub_conj
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (x : ↥(suzukiGroup a K))
    (h : Nat.card W <
      Nat.card (fixedSub ρ
        (CFSG.CGT.Timmesfeld75.conjSubgroup x (szZ a K))) ^ 4) :
    IsSzNatural ρ := by
  classical
  rw [show CFSG.CGT.Timmesfeld75.conjSubgroup x (szZ a K) =
      (szZ a K).map (MulAut.conj x).toMonoidHom from rfl] at h
  rw [natCard_fixedSub_map_conj ρ x (szZ a K)] at h
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sz_descent (a := a) (K := K) hK hnt
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨E, hEfield, hEfin, hEchar, ιK, ιD, A, hAne, hA, hrest⟩ := hdesc b
  let _ : Field E := hEfield
  let _ : Finite E := hEfin
  let _ : CharP E 2 := hEchar
  let _ : Algebra K E := ιK.toAlgebra
  obtain ⟨⟨Φ⟩, hshift, hdimW⟩ := hrest
  have hD : Finite (EndRing ρ) := finite_endRing ρ
  have hcardfix := natCard_fixedSub_sz_eq_pow_finrank (a := a) (K := K) (W := W) hK E b ιD Φ
    (szZ a K)
  have hdimfix := finrank_fixedSub_szZ E hK hA
  have hWcard : Nat.card W = 2 ^ (d * 4 ^ A.card) := by
    rw [natCard_eq_pow_finrank (ρ := ρ), hDcard, hdimW, ← pow_mul]
  have hfixcard : Nat.card (fixedSub ρ (szZ a K)) = 2 ^ (d * 2 ^ A.card) := by
    rw [hcardfix, hdimfix, hDcard, ← pow_mul]
  have hA1 : A.card = 1 := by
    rcases Nat.lt_or_ge A.card 2 with hlt | hge
    · have hpos : 0 < A.card := Finset.card_pos.mpr hAne
      omega
    · exfalso
      have h4 := four_mul_two_pow_le_four_pow hge
      have hle : Nat.card (fixedSub ρ (szZ a K)) ^ 4 ≤ Nat.card W := by
        rw [hfixcard, hWcard, ← pow_mul]
        apply Nat.pow_le_pow_right (by norm_num)
        calc d * 2 ^ A.card * 4 = d * (4 * 2 ^ A.card) := by ring
          _ ≤ d * 4 ^ A.card := Nat.mul_le_mul_left d h4
      omega
  apply isSzNatural_of_finrank_eq_four hK ρ hnt
  rw [hdimW, hA1]
  norm_num

section GenericComm

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) G W} [Fact ρ.IsIrreducible]

private theorem natCard_fixedSub_dualMat_eq_commonKernel
    {k : Type} [Field k] {G : Type} [Group G] {κ : Type} [Fintype κ] [DecidableEq κ]
    (S : G →* Matrix κ κ k) (Z : Subgroup G) :
    Nat.card (fixedSub (matRep (dualMat S)) Z) =
      Nat.card {y : κ → k // ∀ z : Z, ((S (z : G) - 1)ᵀ).mulVec y = 0} := by
  classical
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun y => ?_))
  constructor
  · intro hy z
    have h1 := (mem_fixedSub.mp hy) ((z⁻¹ : Z) : G) (z⁻¹).2
    simp only [Subgroup.coe_inv, inv_inv, matRep_apply, dualMat_apply] at h1
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mulVec, Matrix.one_mulVec,
      h1, sub_self]
  · intro hy g hg
    have h1 := hy ⟨g⁻¹, Z.inv_mem hg⟩
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mulVec, Matrix.one_mulVec,
      sub_eq_zero] at h1
    simpa [matRep_apply, dualMat_apply] using h1

private theorem natCard_fixedSub_eq_of_equiv
    {k : Type} [Field k] {G : Type} [Group G] {V V' : Type}
    [AddCommMonoid V] [Module k V] [AddCommMonoid V'] [Module k V']
    {ρ : Representation k G V} {σ : Representation k G V'} (e : ρ.Equiv σ) (Z : Subgroup G) :
    Nat.card (fixedSub ρ Z) = Nat.card (fixedSub σ Z) := by
  classical
  refine Nat.card_congr (Equiv.subtypeEquiv e.toLinearEquiv.toEquiv (fun v => ?_))
  constructor
  · intro hv
    change ∀ z ∈ Z, σ z (e v) = e v
    intro z hz
    have h2 : e ((ρ z) v) = e v :=
      congrArg (fun w => e w) (mem_fixedSub.mp hv z hz)
    simpa only [equiv_apply] using h2
  · intro hv
    change ∀ z ∈ Z, ρ z v = v
    intro z hz
    have h1 : σ z (e v) = e v := mem_fixedSub.mp hv z hz
    have h2 : e ((ρ z) v) = e v := by
      rw [equiv_apply e z v]
      exact h1
    exact e.toLinearEquiv.injective h2

private theorem smul_mem_commSub_X7 (Z : Subgroup G) (d : EndRing ρ) {w : W}
    (hw : w ∈ commSub ρ Z) :
    d • w ∈ commSub ρ Z := by
  classical
  change w ∈ (⨆ a : G, ⨆ (_ : a ∈ Z), LinearMap.range (ρ a - 1)) at hw
  change d • w ∈ commSub ρ Z
  refine Submodule.iSup_induction (fun a : G => ⨆ (_ : a ∈ Z), LinearMap.range (ρ a - 1))
    (motive := fun w => d • w ∈ commSub ρ Z) hw ?_ ?_ ?_
  · intro a x hx
    refine Submodule.iSup_induction (fun (_ : a ∈ Z) => LinearMap.range (ρ a - 1))
      (motive := fun x => d • x ∈ commSub ρ Z) hx ?_ ?_ ?_
    · intro ha y hy
      obtain ⟨u, rfl⟩ := hy
      refine Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha ?_)
      refine LinearMap.mem_range.mpr ⟨d • u, ?_⟩
      have hd : ρ a (d • u) = d • ρ a u := by
        have h := (repD ρ a).map_smul d u
        simpa [repD_apply] using h
      simp only [LinearMap.sub_apply, Module.End.one_apply, hd, smul_sub]
    · simpa using Submodule.zero_mem (commSub ρ Z)
    · intro x y hx hy
      simpa [smul_add] using Submodule.add_mem (commSub ρ Z) hx hy
  · simpa using Submodule.zero_mem (commSub ρ Z)
  · intro x y hx hy
    simpa [smul_add] using Submodule.add_mem (commSub ρ Z) hx hy

private noncomputable def commSubD (Z : Subgroup G) : Submodule (EndRing ρ) W where
  carrier := (commSub ρ Z : Set W)
  zero_mem' := (commSub ρ Z).zero_mem
  add_mem' := fun hx hy => (commSub ρ Z).add_mem hx hy
  smul_mem' := fun d _ hx => smul_mem_commSub_X7 Z d hx

private theorem commSubD_eq (Z : Subgroup G) :
    commSubD (ρ := ρ) Z = commSubK (repD ρ) Z := by
  classical
  apply le_antisymm
  · intro w hw
    change w ∈ (⨆ a : G, ⨆ (_ : a ∈ Z), LinearMap.range (ρ a - 1)) at hw
    change w ∈ (⨆ a : G, ⨆ (_ : a ∈ Z), LinearMap.range (repD ρ a - 1))
    refine Submodule.iSup_induction (fun a : G => ⨆ (_ : a ∈ Z), LinearMap.range (ρ a - 1))
      (motive := fun w => w ∈ (⨆ a : G, ⨆ (_ : a ∈ Z), LinearMap.range (repD ρ a - 1))) hw ?_ ?_ ?_
    · intro a x hx
      refine Submodule.iSup_induction (fun (_ : a ∈ Z) => LinearMap.range (ρ a - 1))
        (motive := fun x =>
          x ∈ (⨆ a : G, ⨆ (_ : a ∈ Z), LinearMap.range (repD ρ a - 1))) hx ?_ ?_ ?_
      · intro ha y hy
        obtain ⟨u, rfl⟩ := hy
        exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha
          (LinearMap.mem_range.mpr ⟨u, by simp only [LinearMap.sub_apply, Module.End.one_apply,
            repD_apply]⟩))
      · exact Submodule.zero_mem _
      · intro x y hx hy
        exact Submodule.add_mem _ hx hy
    · exact Submodule.zero_mem _
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  · intro w hw
    change w ∈ (⨆ a : G, ⨆ (_ : a ∈ Z), LinearMap.range (repD ρ a - 1)) at hw
    change w ∈ commSub ρ Z
    refine Submodule.iSup_induction (fun a : G => ⨆ (_ : a ∈ Z), LinearMap.range (repD ρ a - 1))
      (motive := fun w => w ∈ commSub ρ Z) hw ?_ ?_ ?_
    · intro a x hx
      refine Submodule.iSup_induction (fun (_ : a ∈ Z) => LinearMap.range (repD ρ a - 1))
        (motive := fun x => x ∈ commSub ρ Z) hx ?_ ?_ ?_
      · intro ha y hy
        obtain ⟨u, rfl⟩ := hy
        refine Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha ?_)
        exact LinearMap.mem_range.mpr ⟨u, by simp only [LinearMap.sub_apply, Module.End.one_apply,
          repD_apply]⟩
      · exact Submodule.zero_mem _
      · intro x y hx hy
        exact Submodule.add_mem _ hx hy
    · exact Submodule.zero_mem _
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy

private theorem map_commSubK_of_equiv
    {k : Type} [Field k] {G : Type} [Group G] {V V' : Type}
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    {ρ : Representation k G V} {σ : Representation k G V'} (e : ρ.Equiv σ) (Z : Subgroup G) :
    Submodule.map e.toLinearEquiv.toLinearMap
        (commSubK ρ Z) =
      commSubK σ Z := by
  classical
  apply le_antisymm
  · intro y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    change w ∈ (⨆ a : G, ⨆ (_ : a ∈ Z), LinearMap.range (ρ a - 1)) at hw
    change e w ∈ (⨆ a : G, ⨆ (_ : a ∈ Z), LinearMap.range (σ a - 1))
    refine Submodule.iSup_induction (fun a : G => ⨆ (_ : a ∈ Z), LinearMap.range (ρ a - 1))
      (motive := fun w => e w ∈ (⨆ a : G, ⨆ (_ : a ∈ Z), LinearMap.range (σ a - 1))) hw ?_ ?_ ?_
    · intro a x hx
      refine Submodule.iSup_induction (fun (_ : a ∈ Z) => LinearMap.range (ρ a - 1))
        (motive := fun x => e x ∈ (⨆ a : G, ⨆ (_ : a ∈ Z), LinearMap.range (σ a - 1))) hx ?_ ?_ ?_
      · intro ha u hu
        obtain ⟨v, rfl⟩ := hu
        refine Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha ?_)
        refine LinearMap.mem_range.mpr ⟨e v, ?_⟩
        simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, equiv_apply]
      · simpa using Submodule.zero_mem _
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    · simpa using Submodule.zero_mem _
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · refine iSup₂_le fun a ha => ?_
    rintro y ⟨v, rfl⟩
    rw [Submodule.mem_map]
    refine ⟨(ρ a - 1) (e.toLinearEquiv.symm v), ?_, ?_⟩
    · exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha
        (LinearMap.mem_range.mpr ⟨e.toLinearEquiv.symm v, rfl⟩))
    · rw [LinearMap.sub_apply, Module.End.one_apply]
      change e ((ρ a) (e.toLinearEquiv.symm v) - e.toLinearEquiv.symm v) =
        (σ a) v - v
      rw [map_sub, equiv_apply e a (e.toLinearEquiv.symm v)]
      rw [show e (e.toLinearEquiv.symm v) = v from
        LinearEquiv.apply_symm_apply e.toLinearEquiv v]

private theorem map_commSubK_repD {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) (Z : Subgroup G) :
    Submodule.map b.equivFun.toLinearMap
        (commSubK (repD ρ) Z) =
      commSubK
        (CFSG.QuasithinUnique.Setup.X7.matRep
          (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b :
            G →* Matrix (Fin m) (Fin m) (EndRing ρ))) Z := by
  classical
  have hcoord : ∀ (g : G) (w : W),
      (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b :
          G →* Matrix (Fin m) (Fin m) (EndRing ρ)) g) (b.equivFun w) =
        b.equivFun (repD ρ g w) := by
    intro g w
    rw [CFSG.QuasithinUnique.Setup.X7.matRep_apply]
    change (LinearMap.toMatrix b b (repD ρ g)).mulVec (b.equivFun w) =
      b.equivFun (repD ρ g w)
    exact LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
  let e : Representation.Equiv (repD ρ)
      (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b :
          G →* Matrix (Fin m) (Fin m) (EndRing ρ))) :=
    Representation.Equiv.mk b.equivFun (fun g => by
      refine LinearMap.ext fun w => ?_
      exact (hcoord g w).symm)
  exact map_commSubK_of_equiv e Z

private theorem finrank_eq_of_natCard_eq {d e kD kE kR kRE a bb f : ℕ}
    (hd : 2 ≤ d) (hf : 0 < f)
    (hKDpow : kD = d ^ a) (hEpow : kR = e ^ bb) (hDE : e = d ^ f)
    (hbase : kE = kD ^ f) (hkE : kRE = kE) (hdual : kRE = kR) : a = bb := by
  have hleft : kD ^ f = d ^ (a * f) := by rw [hKDpow, ← pow_mul]
  have hright : kR = d ^ (f * bb) := by rw [hEpow, hDE, ← pow_mul]
  have hKDKE : kD ^ f = kR := by rw [← hbase, ← hkE, hdual]
  have hpow : d ^ (a * f) = d ^ (f * bb) := by rw [← hleft, hKDKE, hright]
  have h := Nat.pow_right_injective hd hpow
  rw [mul_comm f bb] at h
  exact Nat.eq_of_mul_eq_mul_right hf h

private theorem natCard_fixedSub_dualMat_eq_of_map {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W)
    {E : Type} [Field E] [Finite E] (ιD : EndRing ρ →+* E) {κ : Type} [Fintype κ]
    [DecidableEq κ] (R : G →* Matrix κ κ E)
    (Φ : (CFSG.QuasithinUnique.Setup.X7.matRep R).Equiv (matRepE b ιD))
    (RE : G →* Matrix (Fin m) (Fin m) E)
    (hRE : ∀ g, RE g = (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ιD)
    (Z : Subgroup G) :
    Nat.card (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.dualMat RE)) Z) =
      Nat.card (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.dualMat R)) Z) := by
  classical
  have hmatRepE : matRepE b ιD = CFSG.QuasithinUnique.Setup.X7.matRep RE := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    rw [matRepE_apply, CFSG.QuasithinUnique.Setup.X7.matRep_apply, hRE g]
  have hΦRE : (CFSG.QuasithinUnique.Setup.X7.matRep R).Equiv
      (CFSG.QuasithinUnique.Setup.X7.matRep RE) := hmatRepE ▸ Φ
  obtain ⟨P, Q, hPQ⟩ := CFSG.QuasithinUnique.Setup.X7.MatIso.exists_of_equiv hΦRE
  obtain ⟨e⟩ := hPQ.dual.equiv
  exact natCard_fixedSub_eq_of_equiv e Z

private theorem finrank_fixedSub_dualMat_eq_baseChange {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W)
    (RD : G →* Matrix (Fin m) (Fin m) (EndRing ρ))
    (hRD : ∀ g, RD g = CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g)
    {E : Type} [Field E] [Finite E] (ιD : EndRing ρ →+* E) {κ : Type} [Fintype κ]
    [DecidableEq κ] (R : G →* Matrix κ κ E)
    (Φ : (CFSG.QuasithinUnique.Setup.X7.matRep R).Equiv (matRepE b ιD)) (Z : Subgroup G) :
    Module.finrank E (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.dualMat R)) Z) =
      Module.finrank (EndRing ρ) (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.dualMat RD)) Z) := by
  classical
  let D := EndRing ρ
  let RE : G →* Matrix (Fin m) (Fin m) E := (ιD.mapMatrix).toMonoidHom.comp RD
  let Y : Z → Matrix (Fin m) (Fin m) D := fun z => (RD (z : G) - 1)ᵀ
  let KD := {x : Fin m → D // ∀ z : Z, (Y z).mulVec x = 0}
  let KE := {x : Fin m → E // ∀ z : Z, ((RE (z : G) - 1)ᵀ).mulVec x = 0}
  letI : Algebra D E := ιD.toAlgebra
  let f : ℕ := Module.finrank D E
  haveI : Finite D := finite_endRing ρ
  have hfpos : 0 < f := by
    have : Module.Finite D E := Module.Finite.of_finite; exact Module.finrank_pos
  have hbase_ge : 2 ≤ Nat.card D := by
    have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial D); omega
  have hKD : Nat.card (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
      (CFSG.QuasithinUnique.Setup.X7.dualMat RD)) Z) = Nat.card KD :=
    natCard_fixedSub_dualMat_eq_commonKernel RD Z
  have hKE : Nat.card (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
      (CFSG.QuasithinUnique.Setup.X7.dualMat RE)) Z) = Nat.card KE :=
    natCard_fixedSub_dualMat_eq_commonKernel RE Z
  have hYmap : ∀ z : Z, (Y z).map ιD = ((RE (z : G) - 1)ᵀ) := by
    intro z
    simp only [Y, RE, MonoidHom.comp_apply]
    rw [Matrix.transpose_map, Matrix.map_sub _ (fun a b => map_sub ιD a b),
      Matrix.map_one _ (map_zero ιD) (map_one ιD)]
    rfl
  have hbase : Nat.card KE = Nat.card KD ^ f := by
    simpa only [KE, KD, hYmap] using natCard_common_ker_map ιD Y
  have hRE : ∀ g, RE g = (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ιD :=
    fun g => by simp only [RE, MonoidHom.comp_apply, hRD g]; rfl
  have hdual := natCard_fixedSub_dualMat_eq_of_map (b := b) (ιD := ιD) (R := R) Φ RE hRE Z
  haveI : Finite ↥(fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
      (CFSG.QuasithinUnique.Setup.X7.dualMat RD)) Z) := Subtype.finite
  haveI : Module.Finite D ↥(fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
      (CFSG.QuasithinUnique.Setup.X7.dualMat RD)) Z) := Module.Finite.of_finite
  have hKDpow : Nat.card KD = Nat.card D ^
      Module.finrank D (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.dualMat RD)) Z) := by
    rw [← hKD]; exact Module.natCard_eq_pow_finrank
  haveI : Finite ↥(fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
      (CFSG.QuasithinUnique.Setup.X7.dualMat R)) Z) := Subtype.finite
  haveI : Module.Finite E ↥(fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
      (CFSG.QuasithinUnique.Setup.X7.dualMat R)) Z) := Module.Finite.of_finite
  have hEpow : Nat.card (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.dualMat R)) Z) = Nat.card E ^
      Module.finrank E (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.dualMat R)) Z) :=
    Module.natCard_eq_pow_finrank
  have hDE : Nat.card E = Nat.card D ^ f := by simpa only [f] using natCard_E_eq ιD
  exact (finrank_eq_of_natCard_eq hbase_ge hfpos hKDpow hEpow hDE hbase hKE hdual).symm

theorem natCard_commSub_mul_natCard_fixedSub_dualMat {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W)
    {E : Type} [Field E] [Finite E] (ιD : EndRing ρ →+* E) {κ : Type} [Fintype κ]
    [DecidableEq κ] (R : G →* Matrix κ κ E)
    (Φ : (CFSG.QuasithinUnique.Setup.X7.matRep R).Equiv (matRepE b ιD)) (Z : Subgroup G) :
    Nat.card (commSub ρ Z) *
      Nat.card (EndRing ρ) ^ Module.finrank E
        (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
          (CFSG.QuasithinUnique.Setup.X7.dualMat R)) Z) = Nat.card W := by
  classical
  let D := EndRing ρ
  let RD : G →* Matrix (Fin m) (Fin m) D :=
    CFSG.QuasithinUnique.Setup.SL2Modules.matRep b
  haveI : Finite D := finite_endRing ρ
  have hcardSD : Nat.card (commSub ρ Z) =
      Nat.card D ^ Module.finrank D (commSubK
        (CFSG.QuasithinUnique.Setup.X7.matRep RD) Z) := by
    have h1 : Nat.card (commSub ρ Z) =
        Nat.card (commSubD (ρ := ρ) Z) :=
      Nat.card_congr (Set.equivOfEq rfl)
    have h2 : Nat.card (commSubD (ρ := ρ) Z) =
        Nat.card D ^ Module.finrank D (commSubD (ρ := ρ) Z) :=
      Module.natCard_eq_pow_finrank
    have h3 : commSubD (ρ := ρ) Z =
        commSubK (repD ρ) Z := commSubD_eq Z
    have h4 : Module.finrank D (commSubK (repD ρ) Z) =
        Module.finrank D (commSubK
          (CFSG.QuasithinUnique.Setup.X7.matRep RD) Z) := by
      rw [← map_commSubK_repD (ρ := ρ) (b := b) Z]
      exact (LinearEquiv.finrank_map_eq b.equivFun _).symm
    rw [h1, h2, h3, h4]
  have hinter : Module.finrank D (commSubK
        (CFSG.QuasithinUnique.Setup.X7.matRep RD) Z) +
      Module.finrank D (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.dualMat RD)) Z) = m := by
    have h := finrank_commSubK_add_finrank_fixedSub_dualMat (R := RD) Z
    simpa using h
  have hWcard : Nat.card W = Nat.card D ^ m := by
    rw [natCard_eq_pow_finrank (ρ := ρ), Module.finrank_eq_card_basis b,
      Fintype.card_fin]

  have hfin : Module.finrank E (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.dualMat R)) Z) =
      Module.finrank D (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.dualMat RD)) Z) :=
    finrank_fixedSub_dualMat_eq_baseChange (ρ := ρ) b RD (fun g => rfl) ιD R Φ Z
  rw [hcardSD]
  rw [hfin]
  rw [← pow_add, hinter, hWcard]

end GenericComm


section SzComm

variable {ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W} [Fact ρ.IsIrreducible]

theorem natCard_commSub_mul_natCard_fixedSub_dualMat_sz
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (k : Type) [Field k] [Algebra K k] [Finite k]
    {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) (ιD : EndRing ρ →+* k)
    {A : Finset ℕ}
    (Φ : (CFSG.QuasithinUnique.Setup.X7.matRep (szT k hK A)).Equiv (matRepE b ιD))
    (Z : Subgroup ↥(suzukiGroup a K)) :
    Nat.card (commSub ρ Z) * Nat.card (EndRing ρ) ^
      Module.finrank k (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.dualMat (szT k hK A))) Z) = Nat.card W :=
  natCard_commSub_mul_natCard_fixedSub_dualMat b ιD (szT k hK A) Φ Z

end SzComm

section SzCor23Comm

variable {ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W} [Fact ρ.IsIrreducible]

private theorem card_eq_one_of_pow_lt {b q N : ℕ} (hb : 1 ≤ b) (hq : 1 < q)
    (hW : N = q ^ (4 ^ b)) (hwlt : N < q ^ (4 * 2 ^ b)) : b = 1 := by
  have hexp : 4 ^ b < 4 * 2 ^ b := by
    have h1 : q ^ (4 ^ b) < q ^ (4 * 2 ^ b) := by rwa [hW] at hwlt
    exact (Nat.pow_lt_pow_iff_right hq).mp h1
  rcases Nat.lt_or_ge b 2 with hlt | hge
  · exact le_antisymm (Nat.le_of_lt_succ hlt) hb
  · exfalso
    exact (not_lt_of_ge (four_mul_two_pow_le_four_pow hge)) hexp

theorem isSzNatural_of_commSub_card_lt
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hnt : ∃ g, ρ g ≠ 1) (x : ↥(suzukiGroup a K))
    (h : Nat.card W * Nat.card (commSub ρ
        (CFSG.CGT.Timmesfeld75.conjSubgroup x (szZ a K))) ^ 4 < Nat.card W ^ 4) :
    IsSzNatural ρ := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sz_descent (a := a) (K := K) hK hnt
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨E, hEfield, hEfin, hEchar, ιK, ιD, A, hAne, hA, hrest⟩ := hdesc b
  letI : Field E := hEfield
  letI : Finite E := hEfin
  letI : CharP E 2 := hEchar
  letI : Algebra K E := ιK.toAlgebra
  obtain ⟨⟨Φ⟩, hshift, hdimW⟩ := hrest
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  have hWcard : Nat.card W = Nat.card (EndRing ρ) ^ (4 ^ A.card) := by
    rw [natCard_eq_pow_finrank (ρ := ρ), hdimW]
  have hdual : ∀ g : ↥(suzukiGroup a K),
      Matrix.transpose ((szT E hK A) g⁻¹) = JtS K E A * szT E hK A g * JtS K E A := by
    intro g
    rw [szT_apply, szT_apply, map_inv]
    exact tensorRepS_inv_transpose E A (szIncl hK g)
  have hself : Module.finrank E (fixedSub (CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.dualMat (szT E hK A))) (szZ a K)) =
      2 ^ A.card := by
    rw [finrank_fixedSub_dualMat_eq (R := szT E hK A) (A := szZ a K) (J := JtS K E A)
      (JtS_mul_self E A) hdual, finrank_fixedSub_szZ E hK hA]
  have hcomm := natCard_commSub_mul_natCard_fixedSub_dualMat_sz (a := a) (K := K)
    (W := W) (ρ := ρ) hK E b ιD Φ (szZ a K)
  rw [hself] at hcomm
  have hconj := natCard_commSub_map_conj ρ x (szZ a K)
  have hcard : Nat.card (commSub ρ
        ((szZ a K).map (MulAut.conj x).toMonoidHom)) *
      Nat.card (EndRing ρ) ^ (2 ^ A.card) = Nat.card W := by
    rw [hconj]
    exact hcomm
  have hpow4 : Nat.card W ^ 4 =
      Nat.card (commSub ρ
        ((szZ a K).map (MulAut.conj x).toMonoidHom)) ^ 4 *
        Nat.card (EndRing ρ) ^ (4 * 2 ^ A.card) := by
    rw [← hcard, mul_pow, ← pow_mul]
    rw [mul_comm (2 ^ A.card) 4]
  have hlt : Nat.card (commSub ρ
        ((szZ a K).map (MulAut.conj x).toMonoidHom)) ^ 4 * Nat.card W <
      Nat.card (commSub ρ
        ((szZ a K).map (MulAut.conj x).toMonoidHom)) ^ 4 *
        Nat.card (EndRing ρ) ^ (4 * 2 ^ A.card) := by
    rw [← hpow4, mul_comm _ (Nat.card W)]
    exact h
  have hwlt : Nat.card W < Nat.card (EndRing ρ) ^ (4 * 2 ^ A.card) :=
    Nat.lt_of_mul_lt_mul_left hlt
  have hq : 1 < Nat.card (EndRing ρ) :=
    Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (EndRing ρ))
  have hbpos : 1 ≤ A.card := Finset.card_pos.mpr hAne
  have hb1 : A.card = 1 := card_eq_one_of_pow_lt hbpos hq hWcard hwlt
  apply isSzNatural_of_finrank_eq_four hK ρ hnt
  rw [hdimW, hb1]
  norm_num

theorem isSzNatural_or_fixed_comm_bounds
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hnt : ∃ g, ρ g ≠ 1) (x : ↥(suzukiGroup a K)) :
    IsSzNatural ρ ∨
      (Nat.card (fixedSub ρ
          (CFSG.CGT.Timmesfeld75.conjSubgroup x (szZ a K))) ^ 4 ≤ Nat.card W ∧
        Nat.card W ^ 4 ≤ Nat.card W *
          Nat.card (commSub ρ
            (CFSG.CGT.Timmesfeld75.conjSubgroup x (szZ a K))) ^ 4) := by
  classical
  by_cases hnat : IsSzNatural ρ
  · exact Or.inl hnat
  · right
    constructor
    · exact not_lt.mp fun hlt =>
        hnat (isSzNatural_of_card_lt_fixedSub_conj hK ρ hnt x hlt)
    · exact not_lt.mp fun hlt =>
        hnat (isSzNatural_of_commSub_card_lt (ρ := ρ) hK hnt x hlt)

end SzCor23Comm

end CFSG.RankThree.GF2n.Tim81.Sec2
