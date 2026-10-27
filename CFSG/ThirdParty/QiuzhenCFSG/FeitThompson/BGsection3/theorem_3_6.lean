module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_5

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

universe uG uF uV

public abbrev CFSG.Theorem36IndHyp {G : Type uG} [Group G] [Finite G] (_H : Subgroup G) : Prop :=
  ∀ {G' : Type uG} [Group G'] [Finite G'] (H' R' R₀' : Subgroup G') (p : ℕ),
    Nat.card G' < Nat.card G →
    Group.IsSolvable G' →
    Odd (Nat.card G') →
    H'.Normal →
    H'.IsComplement' R' →
    Nat.Coprime (Nat.card H') (Nat.card R') →
    R₀' ≤ R' →
    Nat.Prime (Nat.card R₀') →
    Nat.Prime p →
    IsZGroup ↥(subgroupCentralizerIn H' R₀') →
    HasPLengthOne p ↥⁅H', R'⁆

public theorem CFSG.theorem_3_6_subgroup_step {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (N : Subgroup G) (hN_lt : N < H) (hN_normal : N.Normal)
    (hRinv : ∀ r : R, ∀ x ∈ N, (r : G) * x * (r : G)⁻¹ ∈ N)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀)) :
    HasPLengthOne p ↥⁅N, R⁆ := by
  let : Fact p.Prime := ⟨hp⟩
  let S : Subgroup G := N ⊔ R
  have hcardS_dvd : Nat.card S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S
  have hdisj : Disjoint N R := hHR.disjoint.mono_left hN_lt.1
  have hcardS_lt : Nat.card S < Nat.card G := by
    have hcardN_lt : Nat.card N < Nat.card H := natCard_lt_of_subgroup_lt hN_lt
    have hcompS : (N.subgroupOf S).IsComplement' (R.subgroupOf S) :=
      isComplement'_subgroupOf_sup_of_disjoint N R hdisj
    have hcardS_eq : Nat.card N * Nat.card R = Nat.card S := by
      simpa [natCard_subgroupOf_eq N S le_sup_left, natCard_subgroupOf_eq R S le_sup_right] using
        hcompS.card_mul_card
    have hcardG_eq : Nat.card H * Nat.card R = Nat.card G := by
      simpa using hHR.card_mul_card
    have hlt_mul : Nat.card N * Nat.card R < Nat.card H * Nat.card R := by
      exact Nat.mul_lt_mul_of_pos_right hcardN_lt (Nat.card_pos (α := R))
    calc
      Nat.card S = Nat.card N * Nat.card R := hcardS_eq.symm
      _ < Nat.card H * Nat.card R := hlt_mul
      _ = Nat.card G := hcardG_eq
  have hcop_sub :
      Nat.Coprime (Nat.card (N.subgroupOf S)) (Nat.card (R.subgroupOf S)) :=
    coprime_card_subgroupOf_sup_of_le N H R hN_lt.1 hcopHR
  have hR₀sub_le : R₀.subgroupOf S ≤ R.subgroupOf S := by
    intro x hx
    exact hR₀_le (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hR₀sub_prime : Nat.Prime (Nat.card (R₀.subgroupOf S)) := by
    rw [natCard_subgroupOf_eq R₀ S (hR₀_le.trans le_sup_right)]
    exact hR₀_prime
  have hCZ_N :
      IsZGroup ↥(subgroupCentralizerIn N R₀) :=
    isZGroup_subgroupCentralizerIn_of_le H N R₀ hN_lt.1
  have hCZ_sub :
      IsZGroup ↥(subgroupCentralizerIn (N.subgroupOf S) (R₀.subgroupOf S)) := by
    let : IsZGroup ↥(subgroupCentralizerIn N R₀) := hCZ_N
    exact isZGroup_subgroupCentralizerIn_subgroupOf S N R₀ (hR₀_le.trans le_sup_right)
  have hsub :
      HasPLengthOne p ↥⁅N.subgroupOf S, R.subgroupOf S⁆ := by
    exact
      hind (N.subgroupOf S) (R.subgroupOf S) (R₀.subgroupOf S) p hcardS_lt
        (by infer_instance)
        (odd_of_card_dvd hodd hcardS_dvd)
        (normal_subgroupOf_sup_of_conj_mem N R hRinv)
        (isComplement'_subgroupOf_sup_of_disjoint N R hdisj)
        hcop_sub
        hR₀sub_le
        hR₀sub_prime
        hp
        hCZ_sub
  exact hasPLengthOne_commutator_subgroupOf_map (p := p) S N R le_sup_left le_sup_right hsub


public theorem CFSG.theorem_3_6_reduce_eq_commutator {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_lt : ⁅H, R⁆ < H) :
    HasPLengthOne p ↥⁅H, R⁆ := by
  let : Fact p.Prime := ⟨hp⟩
  let N : Subgroup G := ⁅H, R⁆
  have hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  let C : Subgroup H := commutatorAction (A := ↥R) (G := ↥H)
  have hCmap : C.map H.subtype = N := by
    simpa [C, N] using commutatorAction_subgroup_conj_map_eq_commutator H R hRnormH
  have hC_normal : C.Normal :=
    commutatorAction_normal (G := ↥H) (A := ↥R)
  have hN_le_H : N ≤ H := by
    simpa [N] using (Subgroup.commutator_le_left (H₁ := H) (H₂ := R))
  have hcommsub_eq : N.subgroupOf H = C := by
    ext x
    constructor
    · intro hx
      have hxmap : (x : G) ∈ C.map H.subtype := by rw [hCmap]; exact hx
      rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
      have hxy : y = x := by
        apply Subtype.ext
        simpa using hyx
      simpa [hxy] using hy
    · intro hx
      have hxmap : (x : G) ∈ C.map H.subtype := ⟨x, hx, rfl⟩
      rw [hCmap] at hxmap
      exact hxmap
  have hH_norm_comm : H ≤ Subgroup.normalizer (N : Set G) := by
    let : (N.subgroupOf H).Normal := by
      rwa [hcommsub_eq]
    exact Subgroup.le_normalizer_of_normal_subgroupOf hN_le_H
  let : IsInvariant (↥R) (↥H) C := commutatorAction_isInvariant (G := ↥H) (A := ↥R)
  have hRinv : ∀ r : R, ∀ x ∈ N, (r : G) * x * (r : G)⁻¹ ∈ N := by
    intro r x hx
    have hxCmap : x ∈ C.map H.subtype := by simpa [hCmap] using hx
    rcases Subgroup.mem_map.mp hxCmap with ⟨xH, hxH, rfl⟩
    have hsmul : r • xH ∈ C := (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := C) r xH).1 hxH
    have hmem : (((r • xH : H) : G)) ∈ N := by
      rw [← hCmap]
      exact Subgroup.mem_map_of_mem H.subtype hsmul
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH] using hmem
  have hR_norm_comm : R ≤ Subgroup.normalizer (N : Set G) := by
    intro r hrR
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hRinv ⟨r, hrR⟩ x hx
    · intro hx
      have hx' :
          ((r : G)⁻¹ * ((r : G) * x * (r : G)⁻¹) * (((r : G)⁻¹)⁻¹)) ∈ N :=
        hRinv ⟨r⁻¹, R.inv_mem hrR⟩ ((r : G) * x * (r : G)⁻¹) hx
      simpa [mul_assoc] using hx'
  have hcomm₂_le :
      (commutatorAction₂ (A := ↥R) (G := ↥H)).map H.subtype ≤ ⁅N, R⁆ := by
    let S : Set H := {x : H | ∃ a : R, ∃ h : H, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc
      (commutatorAction₂ (A := ↥R) (G := ↥H)).map H.subtype = (Subgroup.closure S).map H.subtype := by
        rfl
      _ = Subgroup.closure (H.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := H.subtype) S)
      _ ≤ ⁅N, R⁆ := by
        refine (Subgroup.closure_le (K := ⁅N, R⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : G) ∈ N := by
          rw [← hCmap]
          exact Subgroup.mem_map_of_mem H.subtype hhC
        have : ⁅(h : G)⁻¹, (a : G)⁆ ∈ ⁅N, R⁆ :=
          Subgroup.commutator_mem_commutator (H₁ := N) (H₂ := R) (N.inv_mem hhcomm) a.2
        simpa [commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH, mul_assoc] using this
  have hcomm₂_eq :
      commutatorAction₂ (A := ↥R) (G := ↥H) = C := by
    simpa [C] using proposition_1_6_b (G := ↥H) (A := ↥R)
      (by have : Group.IsSolvable G := hsolvG; infer_instance) hcopHR.symm
  have hdouble_le : ⁅N, R⁆ ≤ N := by
    rw [Subgroup.commutator_def]
    refine (Subgroup.closure_le (K := N)).2 ?_
    rintro _ ⟨n, hn, r, hr, rfl⟩
    have hconj : (r : G) * n⁻¹ * (r : G)⁻¹ ∈ N :=
      hRinv ⟨r, hr⟩ n⁻¹ (N.inv_mem hn)
    have hmem : n * ((r : G) * n⁻¹ * (r : G)⁻¹) ∈ N :=
      N.mul_mem hn hconj
    simpa [commutatorElement_def, mul_assoc] using hmem
  have hdouble_eq : ⁅N, R⁆ = N := by
    apply le_antisymm hdouble_le
    intro x hx
    have hx₂ : x ∈ (commutatorAction₂ (A := ↥R) (G := ↥H)).map H.subtype := by
      rw [hcomm₂_eq, hCmap]
      exact hx
    exact hcomm₂_le hx₂
  have hcomm_normal : N.Normal := by
    have hnorm_top : Subgroup.normalizer (N : Set G) = ⊤ := by
      apply top_unique
      rw [← hHR.sup_eq_top]
      exact sup_le hH_norm_comm hR_norm_comm
    exact Subgroup.normalizer_eq_top_iff.mp hnorm_top
  change HasPLengthOne p ↥N
  rw [← hdouble_eq]
  exact
    theorem_3_6_subgroup_step H R R₀ p hind N (by simpa [N] using hcomm_lt) hcomm_normal hRinv
      hsolvG hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ

public theorem CFSG.theorem_3_6_quotient_step {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (X : Subgroup G) [X.Normal] (hX_le_H : X ≤ H) (hX_ne_bot : X ≠ ⊥)
    (hXinv : ∀ r : R, ∀ x ∈ X, (r : G) * x * (r : G)⁻¹ ∈ X)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) :
    HasPLengthOne p (↥H ⧸ X.subgroupOf H) := by
  let : Fact p.Prime := ⟨hp⟩
  let q : G →* G ⧸ X := QuotientGroup.mk' X
  have hcard_lt : Nat.card (G ⧸ X) < Nat.card G :=
    natCard_quotient_lt_natCard_of_ne_bot X hX_ne_bot
  have hcard_quot_dvd : Nat.card (G ⧸ X) ∣ Nat.card G := by
    exact ⟨Nat.card X, by
      simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G) (s := X))⟩
  have hR₀q_prime : Nat.Prime (Nat.card (R₀.map q)) := by
    have hdisj : Disjoint H R₀ := hHR.disjoint.mono_right hR₀_le
    have hq_inj : Function.Injective (q ∘ R₀.subtype) := by
      intro a b hab
      apply Subtype.ext
      change q (a : G) = q (b : G) at hab
      have habX : (a : G)⁻¹ * (b : G) ∈ X := QuotientGroup.eq.mp hab
      have habH : (a : G)⁻¹ * (b : G) ∈ H := hX_le_H habX
      have habR₀ : (a : G)⁻¹ * (b : G) ∈ R₀ := R₀.mul_mem (R₀.inv_mem a.2) b.2
      have hab_one : (a : G)⁻¹ * (b : G) = 1 := (Subgroup.disjoint_def.mp hdisj) habH habR₀
      have : (b : G) = a := by
        simpa [mul_assoc] using congrArg (fun t : G => (a : G) * t) hab_one
      exact this.symm
    let f : R₀ → R₀.map q := fun r => ⟨q r, ⟨r, r.2, rfl⟩⟩
    have hf_inj : Function.Injective f := by
      intro a b hab
      exact hq_inj (by simpa [f] using congrArg Subtype.val hab)
    have hf_surj : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rcases hx with ⟨r, hrR₀, rfl⟩
      exact ⟨⟨r, hrR₀⟩, rfl⟩
    have hcard_eq : Nat.card R₀ = Nat.card (R₀.map q) :=
      Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
    rw [← hcard_eq]
    exact hR₀_prime
  have hR₀q_le : R₀.map q ≤ R.map q := by
    intro x hx
    rcases hx with ⟨r, hr, rfl⟩
    exact ⟨r, hR₀_le hr, rfl⟩
  have hcopHRq :
      Nat.Coprime (Nat.card (H.map q)) (Nat.card (R.map q)) :=
    coprime_card_map_mk'_of_le_isComplement' H R X hX_le_H hHR hcopHR
  have hcopHR₀ :
      Nat.Coprime (Nat.card H) (Nat.card R₀) :=
    by
      have hR₀dvdR : Nat.card R₀ ∣ Nat.card R := by
        rw [← natCard_subgroupOf_eq R₀ R hR₀_le]
        exact Subgroup.card_subgroup_dvd_card (R₀.subgroupOf R)
      exact Nat.Coprime.of_dvd_right hR₀dvdR hcopHR
  have hXinv₀ : ∀ r : R₀, ∀ x ∈ X, (r : G) * x * (r : G)⁻¹ ∈ X := by
    intro r x hx
    exact hXinv ⟨r, hR₀_le r.2⟩ x hx
  have hR₀normH : R₀ ≤ Subgroup.normalizer H := hR₀_le.trans (Subgroup.le_normalizer_of_normal (H := H))
  have hCZ_quot :
      IsZGroup ↥(subgroupCentralizerIn (H.map q) (R₀.map q)) := by
    have hEq :
        subgroupCentralizerIn (H.map q) (R₀.map q) =
          (subgroupCentralizerIn H R₀).map q :=
      subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime H R₀ X hR₀normH
        (by infer_instance) hcopHR₀ hXinv₀
    let f : subgroupCentralizerIn H R₀ →* (subgroupCentralizerIn H R₀).map q :=
      { toFun := fun x => ⟨q x, ⟨x, x.2, rfl⟩⟩
        map_one' := rfl
        map_mul' := by intro a b; rfl }
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    let : IsZGroup ↥(subgroupCentralizerIn H R₀) := hCZ
    have hZmap : IsZGroup ↥((subgroupCentralizerIn H R₀).map q) :=
      IsZGroup.of_surjective (f := f) hf
    rw [hEq]
    exact hZmap
  have hquot :
      HasPLengthOne p ↥⁅H.map q, R.map q⁆ := by
    exact
      hind (H.map q) (R.map q) (R₀.map q) p hcard_lt
        (by infer_instance)
        (odd_of_card_dvd hodd hcard_quot_dvd)
        (by infer_instance)
        (isComplement'_map_mk'_of_le_isComplement' H R X hX_le_H hHR)
        hcopHRq
        hR₀q_le
        hR₀q_prime
        hp
        hCZ_quot
  have hmap_comm : ⁅H.map q, R.map q⁆ = H.map q := by
    simpa [hcomm_eq] using (Subgroup.map_commutator (H₁ := H) (H₂ := R) q).symm
  have hplen_map : HasPLengthOne p ↥(H.map q) := by
    rwa [hmap_comm] at hquot
  let e : (↥H ⧸ X.subgroupOf H) ≃* H.map q := quotientSubgroupRangeEquiv H X
  exact hasPLengthOne_of_equiv (p := p) e.symm hplen_map

public theorem CFSG.theorem_3_6_characteristic_quotient_step {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (XH : Subgroup H) (hXH_char : XH.Characteristic) (hXH_ne_bot : XH ≠ ⊥)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) :
    HasPLengthOne p (↥H ⧸ XH) := by
  let : Fact p.Prime := ⟨hp⟩
  let X : Subgroup G := XH.map H.subtype
  have hX_card :
      Nat.card X = Nat.card XH := by
    simpa [X] using
      (Subgroup.card_map_of_injective (K := XH) (f := H.subtype) H.subtype_injective)
  have hX_le_H : X ≤ H := by
    simpa [X] using (Subgroup.map_subtype_le XH)
  have hRnormH : R ≤ Subgroup.normalizer H :=
    Subgroup.le_normalizer_of_normal (H := H)
  have hXinv : ∀ r : R, ∀ x ∈ X, (r : G) * x * (r : G)⁻¹ ∈ X := by
    let : XH.Characteristic := hXH_char
    have : IsInvariant (↥R) (↥H) XH := isInvariant_of_characteristic (A := ↥R) (G := ↥H) XH
    intro r x hx
    rcases hx with ⟨xH, hxH, rfl⟩
    refine ⟨r • xH, (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := XH) r xH).1 hxH, ?_⟩
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  have hX_normal : X.Normal := by
    let : XH.Characteristic := hXH_char
    let : H.Normal := hH_normal
    simpa [X] using (inferInstance : X.Normal)
  have hX_ne_bot : X ≠ ⊥ := by
    intro hX_bot
    apply hXH_ne_bot
    apply (Subgroup.card_eq_one (H := XH)).1
    rw [← hX_card]
    simp [hX_bot]
  let : X.Normal := hX_normal
  have hquot :
      HasPLengthOne p (↥H ⧸ X.subgroupOf H) :=
    theorem_3_6_quotient_step H R R₀ p hind X hX_le_H hX_ne_bot hXinv
      hsolvG hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq
  have hXsub_eq : X.subgroupOf H = XH := by
    ext x
    constructor
    · intro hx
      have hx' : (x : G) ∈ X := by
        simpa [Subgroup.mem_subgroupOf] using hx
      rcases hx' with ⟨y, hy, hyx⟩
      have hy_eq : y = x := by
        apply Subtype.ext
        simpa using hyx
      simpa [hy_eq] using hy
    · intro hx
      change (x : G) ∈ X
      exact ⟨x, hx, rfl⟩
  let e : (↥H ⧸ X.subgroupOf H) ≃* (↥H ⧸ XH) := QuotientGroup.quotientMulEquivOfEq hXsub_eq
  exact hasPLengthOne_of_equiv (p := p) e hquot

public theorem CFSG.theorem_3_6_pPrimeCore_eq_bot {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    pPrimeCore p ↥H = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let XH : Subgroup H := pPrimeCore p ↥H
  by_contra hXH_ne_bot
  have hXquot :
      HasPLengthOne p (↥H ⧸ XH) :=
    theorem_3_6_characteristic_quotient_step H R R₀ p hind XH
      (by
        dsimp [XH]
        infer_instance)
      hXH_ne_bot hsolvG hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq
  have hplenH : HasPLengthOne p ↥H :=
    lemma_1_21_b (G := ↥H) (p := p) (H := XH)
      (pPrimeCore_coprime_card (p := p) (G := ↥H)) hXquot
  exact hbad hplenH

public theorem CFSG.theorem_3_6_fitting_eq_pcore {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    fittingSubgroup H = pCore p H := by
  let : Fact p.Prime := ⟨hp⟩
  exact
    Fitting_eq_pcore H p
      (theorem_3_6_pPrimeCore_eq_bot H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad)

noncomputable instance {H : Type*} [Group H] [Finite H] {x : H} {V : Subgroup H} [V.Normal] : MulDistribMulAction (↥(Subgroup.zpowers x)) (↥V ⧸ frattini V) := by
  have hfrattini_inv : IsInvariant (↥(Subgroup.zpowers x)) (↥V) (frattini V) :=
    isInvariant_of_characteristic (A := ↥(Subgroup.zpowers x)) (G := ↥V) (frattini V)
  exact quotientMulDistribMulAction (A := ↥(Subgroup.zpowers x)) (G := ↥V) (frattini V) hfrattini_inv

public theorem CFSG.theorem_3_6_mem_centralizer_of_quotient_frattini
    {H : Type*} [Group H] [Finite H] (p : ℕ) [Fact p.Prime]
    (V Φ : Subgroup H) [V.Normal] [Φ.Normal] (hVp : IsPGroup p ↥V)
    (hΦ_eq : Φ = (frattini V).map V.subtype) (x : H)
    (hcop_zpowers : Nat.Coprime (Nat.card (Subgroup.zpowers x)) (Nat.card V))
    (hx_cent :
      QuotientGroup.mk' Φ x ∈
        Subgroup.centralizer
          (((V.map (QuotientGroup.mk' Φ)) : Subgroup (H ⧸ Φ)) : Set (H ⧸ Φ))) :
    x ∈ Subgroup.centralizer (V : Set H) := by
  let : Fact (IsPGroup p ↥V) := ⟨hVp⟩
  let q : H →* (H ⧸ Φ) := QuotientGroup.mk' Φ
  let Vbar : Subgroup (H ⧸ Φ) := V.map q
  have hq_cent : q x ∈ Subgroup.centralizer (Vbar : Set (H ⧸ Φ)) := by
    simpa [q, Vbar] using hx_cent
  have hznorm : Subgroup.zpowers x ≤ Subgroup.normalizer V := by
    exact Subgroup.le_normalizer_of_normal (K := Subgroup.zpowers x) (H := V)
  have hfrattini_inv : IsInvariant (↥(Subgroup.zpowers x)) (↥V) (frattini V) :=
    isInvariant_of_characteristic (A := ↥(Subgroup.zpowers x)) (G := ↥V) (frattini V)
  have hquot :
      ActsTrivially (A := ↥(Subgroup.zpowers x)) (G := ↥V ⧸ frattini V) := by
    let xgen : Subgroup.zpowers x := ⟨x, Subgroup.mem_zpowers x⟩
    have hx_fix :
        ∀ qv : ↥V ⧸ frattini V, xgen • qv = qv := by
      intro qv
      refine QuotientGroup.induction_on qv ?_
      intro v
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hvbar : q ((v : V) : H) ∈ Vbar := by
        exact ⟨v, v.2, rfl⟩
      have hcomm :
          q x * q ((v : V) : H) =
            q ((v : V) : H) * q x :=
        (Subgroup.mem_centralizer_iff.mp hq_cent _ hvbar).symm
      have hq_eq :
          q ((((xgen : Subgroup.zpowers x) • v : V) : V) : H) = q ((v : V) : H) := by
        calc
          q ((((xgen : Subgroup.zpowers x) • v : V) : V) : H)
              = q x * q ((v : V) : H) * q x⁻¹ := by
                  simp [xgen, q,
                    mul_assoc]
          _ = q ((v : V) : H) * q x * q x⁻¹ := by rw [hcomm]
          _ = q ((v : V) : H) := by simp [mul_assoc]
      have hdiv_mem_Φ :
          ((((xgen : Subgroup.zpowers x) • v : V) : V) : H) / ((v : V) : H) ∈ Φ :=
        (QuotientGroup.eq_iff_div_mem).1 hq_eq
      have hdiv_mem_map :
          ((((xgen : Subgroup.zpowers x) • v : V) : V) : H) / ((v : V) : H) ∈
            (frattini V).map V.subtype := by
        simpa [hΦ_eq] using hdiv_mem_Φ
      rcases hdiv_mem_map with ⟨y, hy, hy_eq⟩
      have hy' : y = ((xgen • v) / v : V) := by
        apply Subtype.ext
        simpa [xgen] using hy_eq
      simpa [hy'] using hy
    intro a qv
    have ha_mem : a ∈ Subgroup.zpowers xgen := by
      rcases Subgroup.mem_zpowers_iff.mp a.2 with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
        apply Subtype.ext
        simpa [xgen] using hn⟩
    exact smul_eq_self_of_mem_zpowers ha_mem (hx_fix qv)
  have htriv : ActsTrivially (A := ↥(Subgroup.zpowers x)) (G := ↥V) :=
    theorem_1_8 (R := ↥V) (A := ↥(Subgroup.zpowers x)) (p := p) hcop_zpowers hquot
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  let a1 : Subgroup.zpowers x := ⟨x, (Subgroup.mem_zpowers_iff).2 ⟨1, by simp⟩⟩
  let vV : V := ⟨v, hv⟩
  have hfix : a1 • vV = vV := htriv a1 vV
  have hfix_val : (((a1 : Subgroup.zpowers x) • vV : V) : H) = v := by
    exact congrArg Subtype.val hfix
  have hconj : x * v * x⁻¹ = v := by
    simpa [a1, vV, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hznorm] using hfix_val
  have := congrArg (fun t : H => t * x) hconj
  simpa [mul_assoc] using this.symm

set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.theorem_3_6_pPrimeCore_quotient_frattini_fitting_eq_bot
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    let V : Subgroup H := fittingSubgroup H
    let Φ : Subgroup H := (frattini V).map V.subtype
    pPrimeCore p (↥H ⧸ Φ) = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let V : Subgroup H := fittingSubgroup H
  have hV_eq : V = pCore p H := by
    simpa [V] using
      theorem_3_6_fitting_eq_pcore H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hVp : IsPGroup p ↥V := by
    rw [hV_eq]
    exact pCore_isPGroup (G := ↥H) (p := p)
  let : Fact (IsPGroup p ↥V) := ⟨hVp⟩
  have : V.Characteristic := by
    dsimp [V]
    infer_instance
  have : V.Normal := by
    dsimp [V]
    infer_instance
  let Φ : Subgroup H := (frattini V).map V.subtype
  have hΦ_char : Φ.Characteristic := by
    simpa [Φ] using characteristic_map_subtype_of_characteristic V (frattini V)
  have : Φ.Characteristic := hΦ_char
  have : Φ.Normal := by infer_instance
  have hΦ_le_V : Φ ≤ V := by
    simpa [Φ] using (Subgroup.map_subtype_le (frattini V))
  have hΦ_p : IsPGroup p ↥Φ := by
    have hfrattini_p : IsPGroup p ↥(frattini V) := hVp.to_subgroup (frattini V)
    simpa [Φ] using IsPGroup.map (p := p) (H := frattini V) hfrattini_p V.subtype
  let q : ↥H →* (↥H ⧸ Φ) := QuotientGroup.mk' Φ
  have hV_map : V.map q = pCore p (↥H ⧸ Φ) := by
    have hmap := pCore_map_mk'_eq_of_normal_isPGroup (G := ↥H) (p := p) Φ hΦ_p
    simpa [q, hV_eq] using hmap
  let A : Subgroup (↥H ⧸ Φ) := pPrimeCore p (↥H ⧸ Φ)
  have hA_cop : Nat.Coprime p (Nat.card A) := by
    simpa [A] using pPrimeCore_coprime_card (G := (↥H ⧸ Φ)) (p := p)
  have hsolvH : Group.IsSolvable ↥H := by infer_instance
  have hcentV : Subgroup.centralizer (V : Set H) ≤ V := by
    simpa [V] using
      centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := ↥H) hsolvH
  by_contra hA_ne_bot
  let Vbar : Subgroup (↥H ⧸ Φ) := V.map q
  have hVbar_eq : Vbar = pCore p (↥H ⧸ Φ) := by
    simpa [Vbar] using hV_map
  have hA_cent : A ≤ Subgroup.centralizer (Vbar : Set (↥H ⧸ Φ)) := by
    have hVbar_p : IsPGroup p ↥Vbar := by
      exact hVbar_eq ▸ pCore_isPGroup (G := ↥H ⧸ Φ) (p := p)
    have hA_cent' :
        A ≤ Subgroup.centralizer (pCore p (↥H ⧸ Φ) : Set (↥H ⧸ Φ)) :=
      pPrimeCore_le_centralizer_of_normal_pgroup (G := ↥H ⧸ Φ) (p := p)
        (R := pCore p (↥H ⧸ Φ)) (pCore_isPGroup (G := ↥H ⧸ Φ) (p := p))
    simpa [hVbar_eq] using hA_cent'
  let W : Subgroup H := A.comap q
  have hΦ_le_W : Φ ≤ W := by
    intro x hx
    change q x ∈ A
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff (N := Φ) x).2 hx
    simp [hxq]
  let qW : W →* A := (q.comp W.subtype).codRestrict A (by intro w; exact w.2)
  have hqW_surj : Function.Surjective qW := by
    intro a
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective (N := Φ) (a : ↥H ⧸ Φ)
    refine ⟨⟨h, ?_⟩, ?_⟩
    · simp [W, q, hh]
    · apply Subtype.ext
      simpa [qW, q, hh]
  have hqW_ker : qW.ker = Φ.subgroupOf W := by
    ext w
    simp [qW, q, Subgroup.mem_subgroupOf]
  have hquot_card : Nat.card (W ⧸ Φ.subgroupOf W) = Nat.card A := by
    let e : W ⧸ qW.ker ≃* A := QuotientGroup.quotientKerEquivOfSurjective qW hqW_surj
    have hcard : Nat.card (W ⧸ qW.ker) = Nat.card A := Nat.card_congr e.toEquiv
    simpa [hqW_ker] using hcard
  have hΦsub_p : IsPGroup p ↥(Φ.subgroupOf W) := by
    let e : ↥(Φ.subgroupOf W) ≃* ↥Φ := Subgroup.subgroupOfEquivOfLe (H := Φ) (K := W) hΦ_le_W
    exact hΦ_p.of_equiv e.symm
  obtain ⟨n, hΦcard⟩ := hΦsub_p.exists_card_eq
  have hp_not_dvd_A : ¬ p ∣ Nat.card A := (Nat.Prime.coprime_iff_not_dvd hp).1 hA_cop
  have hΦ_index_cop : Nat.Coprime (Nat.card (Φ.subgroupOf W)) (Φ.subgroupOf W).index := by
    rw [Subgroup.index_eq_card, hquot_card, hΦcard]
    exact (hp.coprime_pow_of_not_dvd (m := n) hp_not_dvd_A).symm
  obtain ⟨L, hL_comp⟩ :=
    Subgroup.exists_right_complement'_of_coprime (N := Φ.subgroupOf W) hΦ_index_cop
  let eL : W ⧸ Φ.subgroupOf W ≃* L := (hL_comp.symm).QuotientMulEquiv
  have hL_card : Nat.card L = Nat.card A := by
    calc
      Nat.card L = Nat.card (W ⧸ Φ.subgroupOf W) := Nat.card_congr eL.symm.toEquiv
      _ = Nat.card A := hquot_card
  let LH : Subgroup H := L.map W.subtype
  have hLH_card_map : Nat.card LH = Nat.card L := by
    simpa [LH] using
      (Subgroup.card_map_of_injective (K := L) (f := W.subtype) W.subtype_injective)
  have hLH_card : Nat.card LH = Nat.card A := hLH_card_map.trans hL_card
  have hLH_cop : Nat.Coprime p (Nat.card LH) := by
    rw [hLH_card]
    exact hA_cop
  have hLH_cent : LH ≤ Subgroup.centralizer (V : Set H) := by
    intro x hx
    rcases hx with ⟨xL, hxL, rfl⟩
    let xH : H := W.subtype xL
    have hxLH : xH ∈ LH := Subgroup.mem_map.mpr ⟨xL, hxL, rfl⟩
    have horder_dvd : orderOf xH ∣ Nat.card LH := by
      simpa using orderOf_dvd_natCard (⟨xH, hxLH⟩ : LH)
    have horder_cop : Nat.Coprime p (orderOf xH) := Nat.Coprime.of_dvd_right horder_dvd hLH_cop
    obtain ⟨m, hVcard⟩ := hVp.exists_card_eq
    have hp_not_dvd_order : ¬ p ∣ orderOf xH := (Nat.Prime.coprime_iff_not_dvd hp).1 horder_cop
    have hcop_zpowers :
        Nat.Coprime (Nat.card (Subgroup.zpowers xH)) (Nat.card V) := by
      rw [Nat.card_zpowers, hVcard]
      exact hp.coprime_pow_of_not_dvd (m := m) hp_not_dvd_order
    have hx_cent : q xH ∈ Subgroup.centralizer (Vbar : Set (↥H ⧸ Φ)) :=
      hA_cent (show q xH ∈ A from (xL : W).2)
    simpa [xH, q, Vbar] using
      theorem_3_6_mem_centralizer_of_quotient_frattini (p := p) (V := V) (Φ := Φ) hVp rfl xH
        hcop_zpowers (by simpa [q, Vbar] using hx_cent)
  have hLH_le_V : LH ≤ V := hLH_cent.trans hcentV
  have hLH_card_one : Nat.card LH = 1 := by
    obtain ⟨m, hVcard⟩ := hVp.exists_card_eq
    have hLH_dvd : Nat.card LH ∣ p ^ m := by
      rw [← hVcard]
      exact Subgroup.card_dvd_of_le hLH_le_V
    rcases (Nat.dvd_prime_pow hp).1 hLH_dvd with ⟨k, _, hk_card⟩
    have hk_zero : k = 0 := by
      by_contra hk_ne
      have hpdvd : p ∣ Nat.card LH := by
        rw [hk_card]
        exact dvd_pow_self p (Nat.pos_iff_ne_zero.mpr hk_ne).ne'
      exact ((Nat.Prime.coprime_iff_not_dvd hp).1 hLH_cop) hpdvd
    simpa [hk_zero] using hk_card
  have hLH_bot : LH = ⊥ := (Subgroup.card_eq_one (H := LH)).1 hLH_card_one
  have hL_card_one : Nat.card L = 1 := by
    rw [← hLH_card_map]
    simp [hLH_bot]
  have hL_bot : L = ⊥ := (Subgroup.card_eq_one (H := L)).1 hL_card_one
  have hΦ_top : Φ.subgroupOf W = ⊤ := by
    simpa [hL_bot] using hL_comp.sup_eq_top
  have hA_card_one : Nat.card A = 1 := by
    rw [← hquot_card]
    simp [hΦ_top]
  exact hA_ne_bot ((Subgroup.card_eq_one (H := A)).1 hA_card_one)

public theorem CFSG.theorem_3_6_frattini_fitting_eq_bot
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    frattini (fittingSubgroup H) = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let V : Subgroup H := fittingSubgroup H
  have hV_eq : V = pCore p H := by
    simpa [V] using
      theorem_3_6_fitting_eq_pcore H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hVp : IsPGroup p ↥V := by
    rw [hV_eq]
    exact pCore_isPGroup (G := ↥H) (p := p)
  have : V.Characteristic := by
    dsimp [V]
    infer_instance
  have : V.Normal := by
    dsimp [V]
    infer_instance
  let Φ : Subgroup H := (frattini V).map V.subtype
  have hΦ_char : Φ.Characteristic := by
    simpa [Φ] using characteristic_map_subtype_of_characteristic V (frattini V)
  have : Φ.Characteristic := hΦ_char
  have : Φ.Normal := by infer_instance
  have hΦ_p : IsPGroup p ↥Φ := by
    have hfrattini_p : IsPGroup p ↥(frattini V) := hVp.to_subgroup (frattini V)
    simpa [Φ] using IsPGroup.map (p := p) (H := frattini V) hfrattini_p V.subtype
  have hΦ_bot : Φ = ⊥ := by
    by_contra hΦ_ne_bot
    have hquot :
        HasPLengthOne p (↥H ⧸ Φ) :=
      theorem_3_6_characteristic_quotient_step H R R₀ p hind Φ hΦ_char hΦ_ne_bot
        hsolvG hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq
    have hcore_quot_bot :
        pPrimeCore p (↥H ⧸ Φ) = ⊥ := by
      simpa [V, Φ] using
        theorem_3_6_pPrimeCore_quotient_frattini_fitting_eq_bot H R R₀ p hind hsolvG hodd
          hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
    have hplenH : HasPLengthOne p ↥H :=
      lemma_1_21_c (G := ↥H) (p := p) Φ hΦ_p hcore_quot_bot hquot
    exact hbad hplenH
  exact
    (Subgroup.map_eq_bot_iff_of_injective (H := frattini V) (f := V.subtype) V.subtype_injective).1
      (by simpa [Φ] using hΦ_bot)

public theorem CFSG.theorem_3_6_fitting_elementaryAbelian
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    IsElementaryAbelian p ↥(fittingSubgroup H) := by
  let : Fact p.Prime := ⟨hp⟩
  let V : Subgroup H := fittingSubgroup H
  have hV_eq : V = pCore p H := by
    simpa [V] using
      theorem_3_6_fitting_eq_pcore H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hVp : IsPGroup p ↥V := by
    rw [hV_eq]
    exact pCore_isPGroup (G := ↥H) (p := p)
  let : Fact (IsPGroup p ↥V) := ⟨hVp⟩
  have hfrattini_bot : frattini V = ⊥ := by
    simpa [V] using
      theorem_3_6_frattini_fitting_eq_bot H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  exact (lemma_1_7_c (R := ↥V) (p := p)).1 hfrattini_bot

public theorem CFSG.theorem_3_6_centralizer_fitting_eq_fitting
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    Subgroup.centralizer (fittingSubgroup H : Set H) = fittingSubgroup H := by
  let V : Subgroup H := fittingSubgroup H
  have hV_elem : IsElementaryAbelian p ↥V := by
    simpa [V] using
      theorem_3_6_fitting_elementaryAbelian H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  let : IsElementaryAbelian p ↥V := hV_elem
  have hV_le_cent : V ≤ Subgroup.centralizer (V : Set H) := by
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := V)).2 inferInstance
  have hsolvH : Group.IsSolvable ↥H := by infer_instance
  have hcent_le_V : Subgroup.centralizer (V : Set H) ≤ V := by
    simpa [V] using
      centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := ↥H) hsolvH
  simpa [V] using le_antisymm hcent_le_V hV_le_cent

public theorem CFSG.theorem_3_6_two_minimal_normals_force_pLengthOne
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ M N : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    [M.Normal] [N.Normal] [IsMinimalNormal M] [IsMinimalNormal N]
    (hM_le_H : M ≤ H) (hN_le_H : N ≤ H) (hM_ne_bot : M ≠ ⊥) (hN_ne_bot : N ≠ ⊥)
    (hMN_ne : M ≠ N)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) :
    HasPLengthOne p ↥H := by
  let : Fact p.Prime := ⟨hp⟩
  have hMN_bot : M ⊓ N = ⊥ := by
    by_contra hMN_ne_bot
    have hinf_eq_M : M ⊓ N = M :=
      IsMinimalNormal.eq_of_ne_bot M (M ⊓ N) inf_le_left hMN_ne_bot
    have hinf_eq_N : M ⊓ N = N :=
      IsMinimalNormal.eq_of_ne_bot N (M ⊓ N) inf_le_right hMN_ne_bot
    exact hMN_ne (hinf_eq_M.symm.trans hinf_eq_N)
  have hM_quot : HasPLengthOne p (↥H ⧸ M.subgroupOf H) :=
    theorem_3_6_quotient_step H R R₀ p hind M hM_le_H hM_ne_bot
      (by
        intro r x hx
        exact (inferInstance : M.Normal).conj_mem x hx (r : G))
      hsolvG hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq
  have hN_quot : HasPLengthOne p (↥H ⧸ N.subgroupOf H) :=
    theorem_3_6_quotient_step H R R₀ p hind N hN_le_H hN_ne_bot
      (by
        intro r x hx
        exact (inferInstance : N.Normal).conj_mem x hx (r : G))
      hsolvG hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq
  have hsub_bot : M.subgroupOf H ⊓ N.subgroupOf H = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxMN : ((x : H) : G) ∈ M ⊓ N := ⟨hx.1, hx.2⟩
      have hx1 : ((x : H) : G) = 1 := by
        simpa [hMN_bot] using hxMN
      exact Subtype.ext hx1
    · intro hx
      change ((x : H) : G) ∈ M ∧ ((x : H) : G) ∈ N
      have hx1 : ((x : H) : G) = 1 := by
        simpa using hx
      constructor
      · simp [hx1]
      · simp [hx1]
  exact lemma_1_21_e (G := ↥H) (p := p) (M.subgroupOf H) (N.subgroupOf H) hsub_bot hM_quot
    hN_quot

public theorem CFSG.theorem_3_6_unique_minimal_normal_in_H
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ M N : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    [M.Normal] [N.Normal] [IsMinimalNormal M] [IsMinimalNormal N]
    (hM_le_H : M ≤ H) (hN_le_H : N ≤ H) (hM_ne_bot : M ≠ ⊥) (hN_ne_bot : N ≠ ⊥)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    M = N := by
  by_contra hMN_ne
  exact hbad <|
    theorem_3_6_two_minimal_normals_force_pLengthOne H R R₀ M N p hind hM_le_H hN_le_H
      hM_ne_bot hN_ne_bot hMN_ne hsolvG hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ
      hcomm_eq

public theorem CFSG.theorem_3_6_fitting_quotient_coprime_card
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    let V : Subgroup H := fittingSubgroup H
    Nat.Coprime p (Nat.card (fittingSubgroup (↥H ⧸ V))) := by
  let : Fact p.Prime := ⟨hp⟩
  let V : Subgroup H := fittingSubgroup H
  have hV_eq : V = pCore p H := by
    simpa [V] using
      theorem_3_6_fitting_eq_pcore H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hVp : IsPGroup p ↥V := by
    rw [hV_eq]
    exact pCore_isPGroup (G := ↥H) (p := p)
  have : V.Normal := by
    dsimp [V]
    infer_instance
  let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
  have hpCore_quot_bot : pCore p (↥H ⧸ V) = ⊥ := by
    have hmap :
        V.map q = pCore p (↥H ⧸ V) := by
      simpa [q, hV_eq] using
        pCore_map_mk'_eq_of_normal_isPGroup (G := ↥H) (p := p) V hVp
    calc
      pCore p (↥H ⧸ V) = V.map q := hmap.symm
      _ = ⊥ := by simp [q]
  let Q : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
  have hQ_norm : Q.Normal := by
    dsimp [Q]
    infer_instance
  have hQ_nil : Group.IsNilpotent ↥Q := by
    dsimp [Q]
    infer_instance
  have hp_not_dvd_Q : ¬ p ∣ Nat.card Q := by
    intro hp_dvd_Q
    let P : Sylow p ↥Q := default
    have hP_ne_bot : (P : Subgroup ↥Q) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (G := ↥Q) (p := p) P hp_dvd_Q
    have hP_map_normal : ((P : Subgroup ↥Q).map Q.subtype).Normal := by
      have hP_normal : (P : Subgroup ↥Q).Normal :=
        Group.IsNilpotent.sylow_normal hQ_nil p P
      have : (P : Subgroup ↥Q).Characteristic :=
        Sylow.characteristic_of_normal P hP_normal
      infer_instance
    have hP_map_p : IsPGroup p ((P : Subgroup ↥Q).map Q.subtype) := P.isPGroup'.map Q.subtype
    have hP_le_core : (P : Subgroup ↥Q).map Q.subtype ≤ pCore p (↥H ⧸ V) :=
      le_sSup ⟨hP_map_normal, hP_map_p⟩
    have hP_map_bot : (P : Subgroup ↥Q).map Q.subtype = ⊥ := by
      exact le_antisymm (hP_le_core.trans (by simp [hpCore_quot_bot])) bot_le
    have hP_bot : (P : Subgroup ↥Q) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := (P : Subgroup ↥Q)) (f := Q.subtype)
        Q.subtype_injective).1 hP_map_bot
    exact hP_ne_bot hP_bot
  simpa [V, Q] using (Nat.Prime.coprime_iff_not_dvd hp).2 hp_not_dvd_Q

public theorem CFSG.theorem_3_6_invariant_complement_in_fitting_preimage
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    let V : Subgroup H := fittingSubgroup H
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    let U : Subgroup H := Fbar.comap (QuotientGroup.mk' V)
    ∃ K : Subgroup H,
      K ≤ U ∧
      V ⊔ K = U ∧
      Disjoint V K ∧
      IsInvariant (↥R) (↥H) K ∧
      IsInvariant (↥R) (↥H) (Subgroup.normalizer K) := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  let V : Subgroup H := fittingSubgroup H
  let : V.Normal := by
    dsimp [V]
    infer_instance
  let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
  let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
  let U : Subgroup H := Fbar.comap q
  have hV_le_U : V ≤ U := by
    intro x hx
    change q x ∈ Fbar
    have hx1 : q x = 1 := by
      exact (QuotientGroup.eq_one_iff (N := V) (x := x)).2 hx
    simp [hx1]
  have hV_char : V.Characteristic := by
    dsimp [V]
    infer_instance
  let : V.Characteristic := hV_char
  have hV_inv : IsInvariant (↥R) (↥H) V :=
    isInvariant_of_characteristic (A := ↥R) (G := ↥H) V
  let : IsInvariant (↥R) (↥H) V := hV_inv
  have hFbar_char : Fbar.Characteristic := by
    dsimp [Fbar]
    infer_instance
  have hU_char : U.Characteristic := by
    dsimp [U, q]
    exact Subgroup.Characteristic.comap_quotient_mk (H := V) (K := Fbar) hFbar_char
  let : U.Characteristic := hU_char
  have hU_inv : IsInvariant (↥R) (↥H) U :=
    isInvariant_of_characteristic (A := ↥R) (G := ↥H) U
  let : IsInvariant (↥R) (↥H) U := hU_inv

  have hV_elem : IsElementaryAbelian p ↥V := by
    simpa [V] using
      theorem_3_6_fitting_elementaryAbelian H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  let : IsElementaryAbelian p ↥V := hV_elem
  have hVp : IsPGroup p ↥V := IsElementaryAbelian.isPGroup p ↥V
  have hVsub_inv : IsInvariant (↥R) (↥U) (V.subgroupOf U) := by
    refine ⟨?_⟩
    intro a x
    change ((x : H) ∈ V) ↔ ((((a • x : U) : U) : H) ∈ V)
    have hx := IsInvariant.invariant (A := ↥R) (G := ↥H) (H := V) a (x : H)
    change ((x : H) ∈ V) ↔ ((((a • x : U) : U) : H) ∈ V) at hx
    exact hx
  let : IsInvariant (↥R) (↥U) (V.subgroupOf U) := hVsub_inv
  have hVsub_norm : (V.subgroupOf U).Normal :=
    Subgroup.Normal.subgroupOf (G := ↥H) (hH := inferInstance) U
  let : (V.subgroupOf U).Normal := hVsub_norm
  have hcopRVsub : Nat.Coprime (Nat.card R) (Nat.card (V.subgroupOf U)) := by
    have hV_dvd_H : Nat.card V ∣ Nat.card H :=
      Subgroup.card_subgroup_dvd_card (s := V) (α := H)
    have hcopRV : Nat.Coprime (Nat.card R) (Nat.card V) :=
      Nat.Coprime.of_dvd_right hV_dvd_H hcopHR.symm
    rw [natCard_subgroupOf_eq V U hV_le_U]
    exact hcopRV
  have hU_map : U.map q = Fbar := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      rcases QuotientGroup.mk'_surjective V x with ⟨y, rfl⟩
      exact ⟨y, by simpa [U, q] using hx, rfl⟩
  have hquot_card : Nat.card (↥U ⧸ V.subgroupOf U) = Nat.card Fbar := by
    calc
      Nat.card (↥U ⧸ V.subgroupOf U) = Nat.card (U.map q) := by
        symm
        simpa [q] using natCard_map_mk'_eq U V
      _ = Nat.card Fbar := by rw [hU_map]
  have hcop_p_Fbar : Nat.Coprime p (Nat.card Fbar) := by
    simpa [V, Fbar] using
      theorem_3_6_fitting_quotient_coprime_card H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hVsub_p : IsPGroup p ↥(V.subgroupOf U) := by
    let e := (Subgroup.subgroupOfEquivOfLe (G := ↥H) (H := V) (K := U) hV_le_U).symm
    exact hVp.of_equiv e
  obtain ⟨n, hVsub_card⟩ := hVsub_p.exists_card_eq
  have hVsub_coprime_index : Nat.Coprime (Nat.card (V.subgroupOf U)) (V.subgroupOf U).index := by
    rw [Subgroup.index_eq_card, hquot_card, hVsub_card]
    exact hcop_p_Fbar.pow_left n
  obtain ⟨K0, hK0_comp, hK0_inv⟩ :=
    Subgroup.quotientDiff.exists_invariant_complement' (G := U) (A := ↥R) (H := V.subgroupOf U)
      (hH := inferInstance) hVsub_coprime_index hcopRVsub
  let : IsInvariant (↥R) (↥U) K0 := hK0_inv
  let K : Subgroup H := K0.map U.subtype
  have hK_le_U : K ≤ U := by
    simpa [K] using (Subgroup.map_subtype_le K0)
  have hVsub_map : (V.subgroupOf U).map U.subtype = V := by
    simp [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hV_le_U]
  have hVK_sup : V ⊔ K = U := by
    calc
      V ⊔ K = (V.subgroupOf U).map U.subtype ⊔ K0.map U.subtype := by simp [K, hVsub_map]
      _ = ((V.subgroupOf U) ⊔ K0).map U.subtype := by
        symm
        simpa using (Subgroup.map_sup (V.subgroupOf U) K0 U.subtype)
      _ = (⊤ : Subgroup U).map U.subtype := by rw [hK0_comp.sup_eq_top]
      _ = U := by
        ext x
        constructor
        · rintro ⟨y, -, rfl⟩
          exact y.2
        · intro hx
          exact ⟨⟨x, hx⟩, by simp, rfl⟩
  have hVK_disj : Disjoint V K := by
    have hmap_disj :
        Disjoint ((V.subgroupOf U).map U.subtype) (K0.map U.subtype) :=
      Subgroup.disjoint_map U.subtype_injective hK0_comp.disjoint
    simpa [K, hVsub_map] using hmap_disj
  have hK_inv : IsInvariant (↥R) (↥H) K := by
    simpa [K] using isInvariant_map_subtype (A := ↥R) (G := ↥H) U K0
  let : IsInvariant (↥R) (↥H) K := hK_inv
  have hNK_inv : IsInvariant (↥R) (↥H) (Subgroup.normalizer K) := by
    simpa using isInvariant_normalizer_of_isInvariant (A := ↥R) (G := ↥H) K
  exact ⟨K, hK_le_U, hVK_sup, hVK_disj, hK_inv, hNK_inv⟩

private theorem CFSG.map_subgroupOf_map_conjNormal_eq
    {G : Type*} [Group G] {U K : Subgroup G} [U.Normal] (hK : K ≤ U) (x : G) :
    ((K.subgroupOf U).map (MulAut.conjNormal (H := U) x).toMonoidHom).map U.subtype =
      K.map (MulAut.conj x).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
    exact Subgroup.mem_map.mpr ⟨(w : G), hw, by
      simp [MulAut.conjNormal_apply, MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨MulAut.conjNormal (H := U) x ⟨w, hK hw⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨w, hK hw⟩, hw, rfl⟩
    · simp [MulAut.conjNormal_apply, MulAut.conj_apply, mul_assoc]

private theorem CFSG.map_subgroupOf_map_conj_eq_local
    {G : Type*} [Group G]
    {K0 K : Subgroup G} (hK : K ≤ K0) (n : K0) :
    ((K.subgroupOf K0).map (MulAut.conj (n : K0)).toMonoidHom).map K0.subtype =
      K.map (MulAut.conj ((n : K0) : G)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨(z : G), hz, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨(n : G) * y * (n : G)⁻¹, ?_⟩, ?_, rfl⟩
    · exact K0.mul_mem (K0.mul_mem n.property (hK hy)) (K0.inv_mem n.property)
    · refine Subgroup.mem_map.mpr ?_
      refine ⟨⟨y, hK hy⟩, hy, ?_⟩
      ext
      simp [MulAut.conj_apply, mul_assoc]

private theorem CFSG.mem_normalizer_of_map_conj_eq
    {G : Type*} [Group G] {K : Subgroup G} {g h : G}
    (hmap : K.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj h).toMonoidHom) :
    h⁻¹ * g ∈ Subgroup.normalizer K := by
  let φ : G →* G := ((MulAut.conj h)⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom
  let ψ : G →* G := ((MulAut.conj h)⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom
  have hmap_comp : K.map φ = K.map ψ := by
    simpa [φ, ψ, Subgroup.map_map] using
      congrArg (fun S : Subgroup G => S.map ((MulAut.conj h)⁻¹).toMonoidHom) hmap
  have hφ : φ = (MulAut.conj (h⁻¹ * g)).toMonoidHom := by
    ext x
    simp [φ, MulAut.conj_apply, mul_assoc]
  have hψ : ψ = MonoidHom.id G := by
    ext x
    simp [ψ, MulAut.conj_apply, mul_assoc]
  have hmap_conj : K.map (MulAut.conj (h⁻¹ * g)).toMonoidHom = K := by
    calc
      K.map (MulAut.conj (h⁻¹ * g)).toMonoidHom = K.map φ := by simp [hφ]
      _ = K.map ψ := hmap_comp
      _ = K := by rw [hψ]; simp
  rw [← Subgroup.conjAct_pointwise_smul_iff]
  change K.map (MulAut.conj (h⁻¹ * g)).toMonoidHom = K
  exact hmap_conj

theorem CFSG.normalizer_sup_eq_top_of_isComplement'_of_coprime
    {G : Type*} [Group G] [Finite G]
    (V U K : Subgroup G) [V.Normal] [U.Normal] [IsMulCommutative ↥V]
    (hVK_sup : V ⊔ K = U) (hVK_disj : Disjoint V K)
    (hcop : Nat.Coprime (Nat.card V) (Nat.card K)) :
    V ⊔ Subgroup.normalizer K = ⊤ := by
  have hV_le_U : V ≤ U := by
    rw [← hVK_sup]
    exact le_sup_left
  have hK_le_U : K ≤ U := by
    rw [← hVK_sup]
    exact le_sup_right
  have hVsub_comp_base : (V.subgroupOf U).IsComplement' (K.subgroupOf U) := by
    subst U
    simpa using (isComplement'_subgroupOf_sup_of_disjoint V K hVK_disj)
  let Vsub : Subgroup U := V.subgroupOf U
  let Ksub : Subgroup U := K.subgroupOf U
  have hVsub_comp : Vsub.IsComplement' Ksub := by
    simpa [Vsub, Ksub] using hVsub_comp_base
  have hcop_cards_sub : Nat.Coprime (Nat.card Vsub) (Nat.card Ksub) := by
    simpa [Vsub, Ksub, natCard_subgroupOf_eq V U hV_le_U, natCard_subgroupOf_eq K U hK_le_U] using
      hcop
  have hcop_index_sub : Nat.Coprime (Nat.card Vsub) Vsub.index := by
    simpa [hVsub_comp.symm.index_eq_card] using hcop_cards_sub
  apply top_le_iff.mp
  intro x hx
  let KxU : Subgroup U := Ksub.map (MulAut.conjNormal (H := U) (x : G)).toMonoidHom
  have hcard_KxU : Nat.card KxU = Nat.card Ksub := by
    simpa [KxU] using
      (Subgroup.card_map_of_injective (K := Ksub)
        (f := (MulAut.conjNormal (H := U) (x : G)).toMonoidHom)
        (hf := EquivLike.injective (MulAut.conjNormal (H := U) (x : G))))
  have hcop_KxU : Nat.Coprime (Nat.card Vsub) (Nat.card KxU) := by
    rw [hcard_KxU]
    exact hcop_cards_sub
  have hcardmul_KxU : Nat.card Vsub * Nat.card KxU = Nat.card U := by
    calc
      Nat.card Vsub * Nat.card KxU = Nat.card Vsub * Nat.card Ksub := by rw [hcard_KxU]
      _ = Nat.card U := hVsub_comp.card_mul_card
  have hKxU_comp : Vsub.IsComplement' KxU :=
    Subgroup.isComplement'_of_coprime hcardmul_KxU hcop_KxU
  obtain ⟨n, hn⟩ :=
    Subgroup.exists_conj_eq_of_isComplement' (G := U) (H := Vsub) (K₁ := Ksub) (K₂ := KxU)
      hcop_index_sub hVsub_comp hKxU_comp
  have hmapH :
      K.map (MulAut.conj (x : G)).toMonoidHom =
        K.map (MulAut.conj ((n : U) : G)).toMonoidHom := by
    calc
      K.map (MulAut.conj (x : G)).toMonoidHom = KxU.map U.subtype := by
        symm
        exact map_subgroupOf_map_conjNormal_eq (U := U) (K := K) hK_le_U x
      _ = (Ksub.map (MulAut.conj (n : U)).toMonoidHom).map U.subtype := by
        simpa [KxU] using congrArg (fun S : Subgroup U => S.map U.subtype) hn
      _ = K.map (MulAut.conj ((n : U) : G)).toMonoidHom := by
        simpa [Ksub] using
          (map_subgroupOf_map_conj_eq_local (G := G) (K0 := U) (K := K) hK_le_U (n : U))
  have hnorm : ((n : U) : G)⁻¹ * x ∈ Subgroup.normalizer K :=
    mem_normalizer_of_map_conj_eq (K := K) (g := x) (h := ((n : U) : G)) hmapH
  have hnV : ((n : U) : G) ∈ V := by
    exact n.2
  have hmem :
      ((n : U) : G) * (((n : U) : G)⁻¹ * x) ∈ V ⊔ Subgroup.normalizer K := by
    exact (V ⊔ Subgroup.normalizer K).mul_mem
      (Subgroup.mem_sup_left hnV) (Subgroup.mem_sup_right hnorm)
  simpa [mul_assoc] using hmem

public theorem CFSG.theorem_3_6_normalizer_sup_top
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    let V : Subgroup H := fittingSubgroup H
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    let U : Subgroup H := Fbar.comap (QuotientGroup.mk' V)
    ∃ K : Subgroup H,
      K ≤ U ∧
      V ⊔ K = U ∧
      Disjoint V K ∧
      IsInvariant (↥R) (↥H) K ∧
      IsInvariant (↥R) (↥H) (Subgroup.normalizer K) ∧
      V ⊔ Subgroup.normalizer K = ⊤ := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  let V : Subgroup H := fittingSubgroup H
  let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
  let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
  let U : Subgroup H := Fbar.comap q
  obtain ⟨K, hK_le_U, hVK_sup, hVK_disj, hK_inv, hNK_inv⟩ :=
    theorem_3_6_invariant_complement_in_fitting_preimage H R R₀ p hind hsolvG hodd hHR
      hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hV_norm : V.Normal := by
    dsimp [V]
    infer_instance
  let : V.Normal := hV_norm
  have hU_norm : U.Normal := by
    dsimp [U, q, Fbar]
    infer_instance
  let : U.Normal := hU_norm
  have hV_elem : IsElementaryAbelian p ↥V := by
    simpa [V] using
      theorem_3_6_fitting_elementaryAbelian H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  let : IsMulCommutative ↥V := hV_elem.toIsMulCommutative
  have hVp : IsPGroup p ↥V := IsElementaryAbelian.isPGroup p ↥V
  obtain ⟨n, hV_card⟩ := hVp.exists_card_eq
  have hU_map : U.map q = Fbar := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      rcases QuotientGroup.mk'_surjective V x with ⟨y, rfl⟩
      exact ⟨y, by simpa [U, q] using hx, rfl⟩
  have hquot_card : Nat.card (↥U ⧸ V.subgroupOf U) = Nat.card Fbar := by
    calc
      Nat.card (↥U ⧸ V.subgroupOf U) = Nat.card (U.map q) := by
        symm
        simpa [q] using natCard_map_mk'_eq U V
      _ = Nat.card Fbar := by rw [hU_map]
  have hVsub_comp : (V.subgroupOf U).IsComplement' (K.subgroupOf U) := by
    rw [show U = V ⊔ K from hVK_sup.symm]
    exact isComplement'_subgroupOf_sup_of_disjoint V K hVK_disj
  have hKsub_card : Nat.card (K.subgroupOf U) = Nat.card Fbar := by
    calc
      Nat.card (K.subgroupOf U) = (V.subgroupOf U).index := by
        symm
        exact hVsub_comp.symm.index_eq_card
      _ = Nat.card (↥U ⧸ V.subgroupOf U) := by simp [Subgroup.index_eq_card]
      _ = Nat.card Fbar := hquot_card
  have hK_card : Nat.card K = Nat.card Fbar := by
    rw [← natCard_subgroupOf_eq K U hK_le_U, hKsub_card]
  have hcop_p_Fbar : Nat.Coprime p (Nat.card Fbar) := by
    simpa [V, Fbar] using
      theorem_3_6_fitting_quotient_coprime_card H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hcop_VK : Nat.Coprime (Nat.card V) (Nat.card K) := by
    have : Nat.Coprime (p ^ n) (Nat.card K) := by
      rw [hK_card]
      exact hcop_p_Fbar.pow_left n
    simpa [hV_card] using this
  have hVNK_sup : V ⊔ Subgroup.normalizer K = ⊤ :=
    normalizer_sup_eq_top_of_isComplement'_of_coprime V U K hVK_sup hVK_disj hcop_VK
  exact ⟨K, hK_le_U, hVK_sup, hVK_disj, hK_inv, hNK_inv, hVNK_sup⟩

private theorem CFSG.isPGroup_of_isHallSubgroup_singleton
    {G : Type*} [Group G] [Finite G] {P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hP : IsHallSubgroup ({⟨p, Fact.out⟩} : Set Nat.Primes) P) :
    IsPGroup p P := by
  rw [IsPGroup.iff_card]
  have hcard_ne_zero : Nat.card P ≠ 0 := Nat.card_pos.ne'
  refine ⟨(Nat.card P).primeFactorsList.length, ?_⟩
  rw [← List.prod_replicate, ← List.eq_replicate_of_mem ?_, Nat.prod_primeFactorsList hcard_ne_zero]
  intro q hq
  obtain ⟨hq_prime, hq_dvd⟩ := (Nat.mem_primeFactorsList hcard_ne_zero).mp hq
  let q' : Nat.Primes := ⟨q, hq_prime⟩
  have hq_mem : q' ∈ ({⟨p, Fact.out⟩} : Set Nat.Primes) := hP.p_in_pi_of_p_dvd_card q' hq_dvd
  simpa [q'] using congrArg Subtype.val hq_mem

set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.exists_invariant_pSubgroup_of_isInvariant
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    {H : Subgroup G} [IsInvariant A G H] {p : ℕ} [Fact p.Prime]
    (hsolvH : Group.IsSolvable ↥H) (hcopAH : Nat.Coprime (Nat.card A) (Nat.card H)) :
    ∃ P : Subgroup H, IsPGroup p P ∧ ¬ p ∣ P.index ∧ IsInvariant A H P := by
  let π : Set Nat.Primes := {⟨p, Fact.out⟩}

  obtain ⟨Psub, hPsub_hall, hPsub_inv⟩ :=
    exists_isHallSubgroup_isInvariant (G := H) (A := A) hsolvH hcopAH π
  have hPsub_p : IsPGroup p Psub := by
    simpa [π] using isPGroup_of_isHallSubgroup_singleton (G := H) (P := Psub) (p := p) hPsub_hall
  have hp_not_dvd_index : ¬ p ∣ Psub.index := by
    intro hp_dvd
    exact (hPsub_hall.p_in_pi_of_p_dvd_index ⟨p, Fact.out⟩ hp_dvd) (by
      dsimp [π]
      exact Set.mem_singleton_iff.mpr (Subtype.ext rfl))
  exact ⟨Psub, hPsub_p, hp_not_dvd_index, hPsub_inv⟩

@[expose]
public def CFSG.normalizerOf
    {G : Type*} [Group G] {H : Subgroup G} (K : Subgroup H) : Subgroup H :=
  Subgroup.normalizer (K : Set H)

@[expose]
public def CFSG.normalizerSubtypeMap
    {G : Type*} [Group G] {H : Subgroup G} (K : Subgroup H)
    (P : Subgroup (normalizerOf K)) : Subgroup H :=
  P.map (normalizerOf K).subtype

private theorem CFSG.isPGroup_normalizerSubtypeMap
    {G : Type*} [Group G] {H : Subgroup G} {p : ℕ} (K : Subgroup H)
    (P : Subgroup (normalizerOf K)) (hP : IsPGroup p P) :
    IsPGroup p (normalizerSubtypeMap K P) := by
  unfold normalizerSubtypeMap
  exact hP.map (normalizerOf K).subtype


public theorem CFSG.theorem_3_6_complement_card_coprime
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_disj : Disjoint (fittingSubgroup H) K)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H))) :
    Nat.Coprime p (Nat.card K) := by
  let : Fact p.Prime := ⟨hp⟩
  let V : Subgroup H := fittingSubgroup H
  let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
  let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
  let U : Subgroup H := Fbar.comap q
  have hK_le_U : K ≤ U := by
    intro x hx
    have hxsup : x ∈ fittingSubgroup H ⊔ K := by
      exact Subgroup.mem_sup_right hx
    rw [hVK_sup] at hxsup
    simpa [V, q, Fbar, U] using hxsup
  have hV_norm : V.Normal := by
    dsimp [V]
    infer_instance
  let : V.Normal := hV_norm
  have hU_map : U.map q = Fbar := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      rcases QuotientGroup.mk'_surjective V x with ⟨y, rfl⟩
      exact ⟨y, by simpa [U, q] using hx, rfl⟩
  have hquot_card : Nat.card (↥U ⧸ V.subgroupOf U) = Nat.card Fbar := by
    calc
      Nat.card (↥U ⧸ V.subgroupOf U) = Nat.card (U.map q) := by
        symm
        simpa [q] using natCard_map_mk'_eq U V
      _ = Nat.card Fbar := by rw [hU_map]
  have hVsub_comp : (V.subgroupOf U).IsComplement' (K.subgroupOf U) := by
    rw [show U = V ⊔ K from hVK_sup.symm]
    exact isComplement'_subgroupOf_sup_of_disjoint V K hVK_disj
  have hKsub_card : Nat.card (K.subgroupOf U) = Nat.card Fbar := by
    calc
      Nat.card (K.subgroupOf U) = (V.subgroupOf U).index := by
        symm
        exact hVsub_comp.symm.index_eq_card
      _ = Nat.card (↥U ⧸ V.subgroupOf U) := by simp [Subgroup.index_eq_card]
      _ = Nat.card Fbar := hquot_card
  have hK_card : Nat.card K = Nat.card Fbar := by
    rw [← natCard_subgroupOf_eq K U hK_le_U, hKsub_card]
  have hcop_p_Fbar : Nat.Coprime p (Nat.card Fbar) := by
    simpa [V, Fbar] using
      theorem_3_6_fitting_quotient_coprime_card H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  rw [hK_card]
  exact hcop_p_Fbar

public theorem CFSG.theorem_3_6_complement_map_fitting
    {G : Type*} [Group G] {H : Subgroup G} (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H))) :
    K.map (QuotientGroup.mk' (fittingSubgroup H)) =
      fittingSubgroup (↥H ⧸ fittingSubgroup H) := by
  have hV_norm : (fittingSubgroup H).Normal := by infer_instance
  let : (fittingSubgroup H).Normal := hV_norm
  let q : ↥H →* (↥H ⧸ fittingSubgroup H) := QuotientGroup.mk' (fittingSubgroup H)
  let Fbar : Subgroup (↥H ⧸ fittingSubgroup H) := fittingSubgroup (↥H ⧸ fittingSubgroup H)
  let U : Subgroup H := Fbar.comap q
  have hV_map_bot : (fittingSubgroup H).map q = ⊥ := by
    simp [q]
  have hU_map : U.map q = Fbar := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      rcases QuotientGroup.mk'_surjective (fittingSubgroup H) x with ⟨y, rfl⟩
      exact ⟨y, by simpa [U, q] using hx, rfl⟩
  calc
    K.map q = ⊥ ⊔ K.map q := by simp
    _ = (fittingSubgroup H).map q ⊔ K.map q := by rw [hV_map_bot]
    _ = (fittingSubgroup H ⊔ K).map q := by
      symm
      simpa using (Subgroup.map_sup (fittingSubgroup H) K q)
    _ = U.map q := by
      simpa [Fbar, U, q] using congrArg (fun S : Subgroup H => S.map q) hVK_sup
    _ = Fbar := hU_map

public theorem CFSG.theorem_3_6_hasPLengthOne_of_normalizer_pSubgroup_commutator_eq_bot
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hK_map_fitting :
      K.map (QuotientGroup.mk' (fittingSubgroup H)) = fittingSubgroup (↥H ⧸ fittingSubgroup H))
    (hVNK_sup : fittingSubgroup H ⊔ normalizerOf K = ⊤)
    (P : Subgroup (normalizerOf K))
    (hP_p : IsPGroup p P) (hP_not_dvd : ¬ p ∣ P.index)
    (hPK_bot : ⁅normalizerSubtypeMap K P, K⁆ = ⊥) :
    HasPLengthOne p ↥H := by
  let : Fact p.Prime := ⟨hp⟩
  let V : Subgroup H := fittingSubgroup H
  have hV_eq : V = pCore p H := by
    simpa [V] using
      theorem_3_6_fitting_eq_pcore H R R₀ p hind hsolvG hodd hHR hcopHR hR₀_le
        hR₀_prime hp hCZ hcomm_eq hbad
  have hVp : IsPGroup p ↥V := by
    rw [hV_eq]
    exact pCore_isPGroup (G := ↥H) (p := p)
  have hV_norm : V.Normal := by
    dsimp [V]
    infer_instance
  let : V.Normal := hV_norm
  let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
  let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
  let NK : Subgroup H := normalizerOf K
  let Psub : Subgroup H := normalizerSubtypeMap K P
  let φ : NK →* (↥H ⧸ V) := q.comp NK.subtype
  let Pbar : Subgroup (↥H ⧸ V) := P.map φ
  have hV_map_bot : V.map q = ⊥ := by
    simp [q]
  have hK_map : K.map q = Fbar := by
    simpa [V, Fbar, q] using hK_map_fitting
  have hVNK_map : (V ⊔ NK).map q = NK.map q := by
    calc
      (V ⊔ NK).map q = V.map q ⊔ NK.map q := by simpa using (Subgroup.map_sup V NK q)
      _ = ⊥ ⊔ NK.map q := by rw [hV_map_bot]
      _ = NK.map q := by simp
  have htop_map : (⊤ : Subgroup H).map q = ⊤ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases QuotientGroup.mk'_surjective V x with ⟨y, rfl⟩
      exact ⟨y, by simp, rfl⟩
  have hNK_map_top : NK.map q = ⊤ := by
    calc
      NK.map q = (V ⊔ NK).map q := hVNK_map.symm
      _ = (⊤ : Subgroup H).map q := by simpa [V, NK, normalizerOf] using congrArg (fun S : Subgroup H => S.map q) hVNK_sup
      _ = ⊤ := htop_map
  have hφ_surj : Function.Surjective φ := by
    intro x
    have hx : x ∈ NK.map q := by simp [hNK_map_top]
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hPbar_eq : Pbar = Psub.map q := by
    calc
      Pbar = P.map φ := by rfl
      _ = (P.map NK.subtype).map q := by
        rw [show φ = q.comp NK.subtype by rfl, Subgroup.map_map]
      _ = Psub.map q := by rfl
  have hPbar_p : IsPGroup p Pbar := by
    simpa [Pbar] using IsPGroup.map (p := p) (H := P) hP_p φ
  have hidx_dvd : Pbar.index ∣ P.index := by
    simpa [Pbar] using Subgroup.index_map_dvd (H := P) hφ_surj
  have hPbar_not_dvd : ¬ p ∣ Pbar.index := by
    intro hp_dvd
    exact hP_not_dvd (hp_dvd.trans hidx_dvd)
  have hPsub_centK : Psub ≤ Subgroup.centralizer (K : Set H) := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Psub) (H₂ := K)).1 hPK_bot
  have hPbar_cent : Pbar ≤ Subgroup.centralizer (K.map q : Set (↥H ⧸ V)) := by
    intro x hx
    rw [hPbar_eq] at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨k, hk, rfl⟩
    have hy_cent : (y : H) ∈ Subgroup.centralizer (K : Set H) := hPsub_centK hy
    have hcomm_yk : k * (y : H) = y * k := (Subgroup.mem_centralizer_iff.mp hy_cent) k hk
    simpa [q, map_mul] using congrArg q hcomm_yk
  have hsolvQ : Group.IsSolvable (↥H ⧸ V) := by infer_instance
  have hcentFbar_le : Subgroup.centralizer (Fbar : Set (↥H ⧸ V)) ≤ Fbar := by
    simpa [Fbar] using
      centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := ↥H ⧸ V) hsolvQ
  have hPbar_le_Fbar : Pbar ≤ Fbar := by
    have hPbar_le_centFbar : Pbar ≤ Subgroup.centralizer (Fbar : Set (↥H ⧸ V)) := by
      simpa [hK_map] using hPbar_cent
    exact hPbar_le_centFbar.trans hcentFbar_le
  have hcop_p_Fbar : Nat.Coprime p (Nat.card Fbar) := by
    simpa [V, Fbar] using
      theorem_3_6_fitting_quotient_coprime_card H R R₀ p hind hsolvG hodd hHR
        hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hPbar_card_one : Nat.card Pbar = 1 := by
    have hcard_dvd : Nat.card Pbar ∣ Nat.card Fbar := Subgroup.card_dvd_of_le hPbar_le_Fbar
    have hp_not_dvd_Pbarcard : ¬ p ∣ Nat.card Pbar := by
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.of_dvd_right hcard_dvd hcop_p_Fbar)
    exact (hPbar_p.card_eq_or_dvd).resolve_right hp_not_dvd_Pbarcard
  have hPbar_bot : Pbar = ⊥ := (Subgroup.card_eq_one (H := Pbar)).1 hPbar_card_one
  have hp_not_dvd_bot_index : ¬ p ∣ (⊥ : Subgroup (↥H ⧸ V)).index := by
    simpa [hPbar_bot] using hPbar_not_dvd
  have hp_not_dvd_qcard : ¬ p ∣ Nat.card (↥H ⧸ V) := by
    have hnot_dvd_bot_card : ¬ p ∣ Nat.card ((↥H ⧸ V) ⧸ (⊥ : Subgroup (↥H ⧸ V))) := by
      simpa [Subgroup.index_eq_card] using hp_not_dvd_bot_index
    have hcard_bot :
        Nat.card ((↥H ⧸ V) ⧸ (⊥ : Subgroup (↥H ⧸ V))) = Nat.card (↥H ⧸ V) :=
      Nat.card_congr (QuotientGroup.quotientBot (G := ↥H ⧸ V)).toEquiv
    rw [hcard_bot] at hnot_dvd_bot_card
    exact hnot_dvd_bot_card
  have hcop_qcard : Nat.Coprime p (Nat.card (↥H ⧸ V)) := by
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hp_not_dvd_qcard
  have htop_le_core : (⊤ : Subgroup (↥H ⧸ V)) ≤ pPrimeCore p (↥H ⧸ V) := by
    exact le_sSup ⟨(inferInstance : (⊤ : Subgroup (↥H ⧸ V)).Normal), by simpa using hcop_qcard⟩
  have hcore_top : pPrimeCore p (↥H ⧸ V) = ⊤ := top_unique htop_le_core
  have hcore_bot_H : pPrimeCore p ↥H = ⊥ := by
    exact
      theorem_3_6_pPrimeCore_eq_bot H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hOp_eq_V : Op_p'p p ↥H = V := by
    calc
      Op_p'p p ↥H = pCore p H := Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := ↥H) (p := p) hcore_bot_H
      _ = V := hV_eq.symm
  let eOp : (↥H ⧸ Op_p'p p ↥H) ≃* (↥H ⧸ V) := QuotientGroup.quotientMulEquivOfEq hOp_eq_V
  have hcore_top_op : pPrimeCore p (↥H ⧸ Op_p'p p ↥H) = ⊤ := by
    have hmap :
        (pPrimeCore p (↥H ⧸ V)).map eOp.symm.toMonoidHom =
          pPrimeCore p (↥H ⧸ Op_p'p p ↥H) := by
      simpa [eOp] using
        (pPrimeCore_map_iso (G := (↥H ⧸ V))
          (G' := (↥H ⧸ Op_p'p p ↥H)) (p := p) eOp.symm)
    simpa [hcore_top] using hmap.symm
  simp [HasPLengthOne, Op_p'pp', hcore_top_op]

public theorem CFSG.theorem_3_6_exists_normalizer_invariant_pSubgroup_with_nontrivial_commutator
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H)))
    (hNK_inv : IsInvariant (↥R) (↥H) (normalizerOf K))
    (hVNK_sup : fittingSubgroup H ⊔ normalizerOf K = ⊤) :
    ∃ P : Subgroup (normalizerOf K),
      IsPGroup p P ∧
      ¬ p ∣ P.index ∧
      IsInvariant (↥R) (↥(normalizerOf K)) P ∧
      ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let NK : Subgroup H := normalizerOf K
  have hK_map_fitting :
      K.map (QuotientGroup.mk' (fittingSubgroup H)) = fittingSubgroup (↥H ⧸ fittingSubgroup H) :=
    theorem_3_6_complement_map_fitting (H := H) K hVK_sup
  have hNK_card_dvd_H : Nat.card NK ∣ Nat.card H := by
    simpa [NK] using (Subgroup.card_dvd_of_le (show NK ≤ (⊤ : Subgroup H) by simp))
  have hcopR_NK : Nat.Coprime (Nat.card R) (Nat.card NK) := by
    exact Nat.Coprime.of_dvd_right hNK_card_dvd_H hcopHR.symm
  have hsolvNK : Group.IsSolvable ↥NK := by infer_instance
  let : IsInvariant (↥R) (↥H) NK := by
    simpa [NK] using hNK_inv
  obtain ⟨P, hP_p, hP_not_dvd, hP_inv⟩ :=
    exists_invariant_pSubgroup_of_isInvariant
      (G := ↥H) (A := ↥R) (H := NK) (p := p) hsolvNK hcopR_NK
  have hPK_ne_bot : ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ := by
    intro hPK_bot
    exact hbad <|
      theorem_3_6_hasPLengthOne_of_normalizer_pSubgroup_commutator_eq_bot H R R₀ p hind hsolvG
        hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hK_map_fitting
        hVNK_sup P hP_p hP_not_dvd hPK_bot
  exact ⟨P, hP_p, hP_not_dvd, hP_inv, hPK_ne_bot⟩

public theorem CFSG.theorem_3_6_exists_normalizer_pSubgroup_with_nontrivial_commutator
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H)))
    (hNK_inv : IsInvariant (↥R) (↥H) (normalizerOf K))
    (hVNK_sup : fittingSubgroup H ⊔ normalizerOf K = ⊤) :
    ∃ P : Subgroup (normalizerOf K),
      IsPGroup p P ∧
      ¬ p ∣ P.index ∧
      ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ := by
  obtain ⟨P, hP_p, hP_not_dvd, _hP_inv, hPK_ne_bot⟩ :=
    theorem_3_6_exists_normalizer_invariant_pSubgroup_with_nontrivial_commutator H R R₀ p hind
      hsolvG hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hNK_inv
      hVNK_sup
  exact ⟨P, hP_p, hP_not_dvd, hPK_ne_bot⟩

private theorem CFSG.normal_map_subtype_of_normal_and_isInvariant
    {G : Type*} [Group G] {H R : Subgroup G}
    [H.Normal] (hHR : H.IsComplement' R) (S : Subgroup H)
    [S.Normal]
    (hSinv : IsInvariant (↥R) (↥H) S) :
    (S.map H.subtype).Normal := by
  let N : Subgroup G := S.map H.subtype
  have hN_le_H : N ≤ H := by
    simpa [N] using (Subgroup.map_subtype_le S)
  have hNsub_eq : N.subgroupOf H = S := by
    ext x
    constructor
    · intro hx
      change ((x : H) : G) ∈ N at hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
      have hy_eq : y = x := by
        apply Subtype.ext
        simpa using hyx
      simpa [hy_eq] using hy
    · intro hx
      change ((x : H) : G) ∈ N
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hH_norm_N : H ≤ Subgroup.normalizer (N : Set G) := by
    let : (N.subgroupOf H).Normal := by
      rwa [hNsub_eq]
    exact Subgroup.le_normalizer_of_normal_subgroupOf hN_le_H
  have hRinv :
      ∀ r : R, ∀ x ∈ N, (r : G) * x * (r : G)⁻¹ ∈ N := by
    intro r x hx
    have hxN : x ∈ S.map H.subtype := by
      simpa [N] using hx
    rcases Subgroup.mem_map.mp hxN with ⟨xH, hxH, rfl⟩
    have hsmul : r • xH ∈ S := (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := S) r xH).1 hxH
    have hmem : (((r • xH : H) : G)) ∈ N := by
      change (((r • xH : H) : G)) ∈ S.map H.subtype
      exact Subgroup.mem_map_of_mem H.subtype hsmul
    simpa [Subgroup.conjMulDistribMulActionOfNormal_smul_coe] using hmem
  have hR_norm_N : R ≤ Subgroup.normalizer (N : Set G) := by
    intro r hrR
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hRinv ⟨r, hrR⟩ x hx
    · intro hx
      have hx' :
          ((r : G)⁻¹ * ((r : G) * x * (r : G)⁻¹) * (((r : G)⁻¹)⁻¹)) ∈ N :=
        hRinv ⟨r⁻¹, R.inv_mem hrR⟩ ((r : G) * x * (r : G)⁻¹) hx
      simpa [mul_assoc] using hx'
  have hnorm_top : Subgroup.normalizer (N : Set G) = ⊤ := by
    apply top_unique
    rw [← hHR.sup_eq_top]
    exact sup_le hH_norm_N hR_norm_N
  have hN_normal : N.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
  simpa [N] using hN_normal

noncomputable instance {G : Type uG} [Group G] {H : Subgroup G} {K : Subgroup H} : MulDistribMulAction (↥K) (↥(fittingSubgroup H)) := by
  have hKnormV : K ≤ Subgroup.normalizer (fittingSubgroup H) := Subgroup.le_normalizer_of_normal (H := (fittingSubgroup H))
  exact Subgroup.conjMulDistribMulActionOfLeNormalizer (G := ↥H) K (fittingSubgroup H) hKnormV

public theorem CFSG.theorem_3_6_fitting_centralizer_commutator_decomposition
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H)))
    (hVK_disj : Disjoint (fittingSubgroup H) K) :
    let V : Subgroup H := fittingSubgroup H
    Disjoint (subgroupCentralizerIn V K) ⁅V, K⁆ ∧
      subgroupCentralizerIn V K ⊔ ⁅V, K⁆ = V := by
  let : Fact p.Prime := ⟨hp⟩
  let V : Subgroup H := fittingSubgroup H
  let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
  let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
  let U : Subgroup H := Fbar.comap q
  have hVK_eq : V ⊔ K = U := by
    simpa [V, U, Fbar, q] using hVK_sup
  have hV_le_U : V ≤ U := by
    rw [← hVK_eq]
    exact le_sup_left
  have hK_le_U : K ≤ U := by
    rw [← hVK_eq]
    exact le_sup_right
  have hV_norm : V.Normal := by
    dsimp [V]
    infer_instance
  let : V.Normal := hV_norm
  have hVp : IsPGroup p ↥V := by
    have hV_eq_pcore : V = pCore p H := by
      simpa [V] using
        theorem_3_6_fitting_eq_pcore H R R₀ p hind hsolvG hodd hHR hcopHR
          hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
    rw [hV_eq_pcore]
    exact pCore_isPGroup (G := ↥H) (p := p)
  obtain ⟨n, hV_card⟩ := hVp.exists_card_eq
  have hU_map : U.map q = Fbar := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      rcases QuotientGroup.mk'_surjective V x with ⟨y, rfl⟩
      exact ⟨y, by simpa [U, q] using hx, rfl⟩
  have hquot_card : Nat.card (↥U ⧸ V.subgroupOf U) = Nat.card Fbar := by
    calc
      Nat.card (↥U ⧸ V.subgroupOf U) = Nat.card (U.map q) := by
        symm
        simpa [q] using natCard_map_mk'_eq U V
      _ = Nat.card Fbar := by rw [hU_map]
  have hVsub_comp : (V.subgroupOf U).IsComplement' (K.subgroupOf U) := by
    rw [show U = V ⊔ K from hVK_eq.symm]
    exact isComplement'_subgroupOf_sup_of_disjoint V K hVK_disj
  have hKsub_card : Nat.card (K.subgroupOf U) = Nat.card Fbar := by
    calc
      Nat.card (K.subgroupOf U) = (V.subgroupOf U).index := by
        symm
        exact hVsub_comp.symm.index_eq_card
      _ = Nat.card (↥U ⧸ V.subgroupOf U) := by simp [Subgroup.index_eq_card]
      _ = Nat.card Fbar := hquot_card
  have hK_card : Nat.card K = Nat.card Fbar := by
    rw [← natCard_subgroupOf_eq K U hK_le_U, hKsub_card]
  have hcop_p_Fbar : Nat.Coprime p (Nat.card Fbar) := by
    simpa [V, Fbar] using
      theorem_3_6_fitting_quotient_coprime_card H R R₀ p hind hsolvG hodd hHR
        hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hcop_VK : Nat.Coprime (Nat.card V) (Nat.card K) := by
    have : Nat.Coprime (p ^ n) (Nat.card K) := by
      rw [hK_card]
      exact hcop_p_Fbar.pow_left n
    simpa [hV_card] using this
  have hV_elem : IsElementaryAbelian p ↥V := by
    simpa [V] using
      theorem_3_6_fitting_elementaryAbelian H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  let : IsMulCommutative ↥V := hV_elem.toIsMulCommutative
  have hKnormV : K ≤ Subgroup.normalizer V := Subgroup.le_normalizer_of_normal (H := V)

  have hfix_eq :
      fixedPointSubgroup (↥K) (↥V) = (subgroupCentralizerIn V K).subgroupOf V := by
    simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn V K hKnormV
  have hcomm_eq_map :
      (commutatorAction (A := ↥K) (G := ↥V)).map V.subtype = ⁅V, K⁆ := by
    simpa using commutatorAction_subgroup_conj_map_eq_commutator V K hKnormV
  have hsubtype_inj : Function.Injective V.subtype := by
    intro x y hxy
    exact Subtype.ext hxy
  have hW_le_V : ⁅V, K⁆ ≤ V := Subgroup.commutator_le_left (H₁ := V) (H₂ := K)
  have hcomm_eq :
      commutatorAction (A := ↥K) (G := ↥V) = (⁅V, K⁆).subgroupOf V := by
    apply (Subgroup.map_injective (f := V.subtype) hsubtype_inj)
    simpa [Subgroup.map_subgroupOf_eq_of_le hW_le_V] using hcomm_eq_map
  have hcompl :
      IsCompl (fixedPointSubgroup (↥K) (↥V)) (commutatorAction (A := ↥K) (G := ↥V)) := by
    exact proposition_1_6_d (G := ↥V) (A := ↥K)
      (by have : Group.IsSolvable G := hsolvG; infer_instance) hcop_VK.symm inferInstance
  have hcompl_sub :
      IsCompl ((subgroupCentralizerIn V K).subgroupOf V) ((⁅V, K⁆).subgroupOf V) := by
    simpa [hfix_eq, hcomm_eq] using hcompl
  have hC_le_V : subgroupCentralizerIn V K ≤ V := inf_le_left
  have hdisj :
      Disjoint (subgroupCentralizerIn V K) ⁅V, K⁆ := by
    have hmap_disj :
        Disjoint (((subgroupCentralizerIn V K).subgroupOf V).map V.subtype)
          (((⁅V, K⁆).subgroupOf V).map V.subtype) :=
      Subgroup.disjoint_map hsubtype_inj hcompl_sub.disjoint
    simpa [Subgroup.map_subgroupOf_eq_of_le hC_le_V, Subgroup.map_subgroupOf_eq_of_le hW_le_V] using
      hmap_disj
  have hsup :
      subgroupCentralizerIn V K ⊔ ⁅V, K⁆ = V := by
    calc
      subgroupCentralizerIn V K ⊔ ⁅V, K⁆ =
          ((subgroupCentralizerIn V K).subgroupOf V).map V.subtype ⊔
            ((⁅V, K⁆).subgroupOf V).map V.subtype := by
            simp [Subgroup.map_subgroupOf_eq_of_le hC_le_V, Subgroup.map_subgroupOf_eq_of_le hW_le_V]
      _ =
          (((subgroupCentralizerIn V K).subgroupOf V) ⊔
            ((⁅V, K⁆).subgroupOf V)).map V.subtype := by
            symm
            simpa using
              (Subgroup.map_sup ((subgroupCentralizerIn V K).subgroupOf V) ((⁅V, K⁆).subgroupOf V)
                V.subtype)
      _ = (⊤ : Subgroup V).map V.subtype := by rw [hcompl_sub.sup_eq_top]
      _ = V := by
        ext x
        constructor
        · rintro ⟨y, -, rfl⟩
          exact y.2
        · intro hx
          exact ⟨⟨x, hx⟩, by simp, rfl⟩
  exact ⟨hdisj, hsup⟩

public theorem CFSG.theorem_3_6_fitting_centralizer_proper
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (hVK_disj : Disjoint (fittingSubgroup H) K) (hK_ne_bot : K ≠ ⊥) :
    let V : Subgroup H := fittingSubgroup H
    subgroupCentralizerIn V K ≠ V := by
  let V : Subgroup H := fittingSubgroup H
  show subgroupCentralizerIn V K ≠ V
  intro hCV_eq
  have hV_le_centK : V ≤ Subgroup.centralizer (K : Set H) := by
    intro x hx
    have hxC : x ∈ subgroupCentralizerIn V K := by
      rw [hCV_eq]
      exact hx
    exact hxC.2
  have hK_le_centV : K ≤ Subgroup.centralizer (V : Set H) :=
    (Subgroup.le_centralizer_iff (H := V) (K := K)).mp hV_le_centK
  have hcentV_eq :
      Subgroup.centralizer (V : Set H) = V := by
    simpa [V] using
      theorem_3_6_centralizer_fitting_eq_fitting H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hK_le_V : K ≤ V := by
    simpa [hcentV_eq] using hK_le_centV
  have hK_bot : K = ⊥ := by
    apply bot_unique
    intro x hx
    have hxV : x ∈ V := hK_le_V hx
    have hxbot : x ∈ (⊥ : Subgroup H) := by
      have hxVK : x ∈ V ⊓ K := ⟨hxV, hx⟩
      rw [hVK_disj.eq_bot] at hxVK
      exact hxVK
    simpa using hxbot
  exact hK_ne_bot hK_bot

private theorem CFSG.isInvariant_subgroupCentralizerIn_of_isInvariant
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (V K : Subgroup G) [IsInvariant A G V] [IsInvariant A G K] :
    IsInvariant A G (subgroupCentralizerIn V K) := by
  have hcent_inv : IsInvariant A G (Subgroup.centralizer (K : Set G)) :=
    isInvariant_centralizer (A := A) K
  simpa [subgroupCentralizerIn] using isInvariant_inf (A := A) (G := G) V (Subgroup.centralizer (K : Set G))

private theorem CFSG.subgroupCentralizerIn_normalizer_le
    {G : Type*} [Group G] {V K N : Subgroup G} [V.Normal]
    (hN_le : N ≤ Subgroup.normalizer K) :
    N ≤ Subgroup.normalizer (subgroupCentralizerIn V K : Set G) := by
  have hforward :
      ∀ n : N, ∀ x : G,
        x ∈ subgroupCentralizerIn V K → (n : G) * x * (n : G)⁻¹ ∈ subgroupCentralizerIn V K := by
    intro n x hx
    rcases hx with ⟨hxV, hxC⟩
    refine ⟨Subgroup.Normal.conj_mem inferInstance x hxV (n : G), ?_⟩
    change (n : G) * x * (n : G)⁻¹ ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : (n : G)⁻¹ * k * (((n : G)⁻¹)⁻¹) ∈ K := by
      exact ((Subgroup.mem_normalizer_iff.mp (hN_le (N.inv_mem n.2))) k).1 hk
    have hcomm : ((n : G)⁻¹ * k * (((n : G)⁻¹)⁻¹)) * x =
        x * ((n : G)⁻¹ * k * (((n : G)⁻¹)⁻¹)) :=
      (Subgroup.mem_centralizer_iff.mp hxC) _ hk'
    have := congrArg (fun t : G => (n : G) * t * (n : G)⁻¹) hcomm
    simpa [mul_assoc] using this
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hforward ⟨n, hn⟩ x hx
  · intro hx
    have hinv : n⁻¹ ∈ N := N.inv_mem hn
    have hx' :
        n⁻¹ * ((n : G) * x * (n : G)⁻¹) * (n⁻¹)⁻¹ ∈ subgroupCentralizerIn V K :=
      hforward ⟨n⁻¹, hinv⟩ _ hx
    simpa [mul_assoc] using hx'

private theorem CFSG.commutator_normalizer_le
    {G : Type*} [Group G] {V K N : Subgroup G} [V.Normal]
    (hN_le : N ≤ Subgroup.normalizer K) :
    N ≤ Subgroup.normalizer (((⁅V, K⁆ : Subgroup G) : Set G)) := by
  let S : Set G := {x : G | ∃ v ∈ V, ∃ k ∈ K, ⁅v, k⁆ = x}
  have hforward : ∀ n : N, ∀ x ∈ ⁅V, K⁆, (n : G) * x * (n : G)⁻¹ ∈ ⁅V, K⁆ := by
    intro n x hx
    rw [Subgroup.commutator_def] at hx ⊢
    refine Subgroup.closure_induction (k := S)
      (p := fun y _hy => (n : G) * y * (n : G)⁻¹ ∈ Subgroup.closure S) (x := x)
      ?mem ?one ?mul ?inv hx
    · intro y hy
      rcases hy with ⟨v, hv, k, hk, rfl⟩
      have hk' : (n : G) * k * (n : G)⁻¹ ∈ K := by
        exact ((Subgroup.mem_normalizer_iff.mp (hN_le n.2)) k).1 hk
      refine Subgroup.subset_closure ?_
      refine ⟨(n : G) * v * (n : G)⁻¹, Subgroup.Normal.conj_mem inferInstance v hv (n : G),
        (n : G) * k * (n : G)⁻¹, hk', ?_⟩
      simp [commutatorElement_def, mul_assoc]
    · simp
    · intro y z _hy _hz hy hz
      simpa [mul_assoc] using (Subgroup.closure S).mul_mem hy hz
    · intro y _hy hy
      simpa [mul_assoc] using (Subgroup.closure S).inv_mem hy
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hforward ⟨n, hn⟩ x hx
  · intro hx
    have hx' :
        (n⁻¹ : G) * ((n : G) * x * (n : G)⁻¹) * ((n⁻¹ : G)⁻¹) ∈ ⁅V, K⁆ :=
      hforward ⟨n⁻¹, N.inv_mem hn⟩ _ hx
    simpa [mul_assoc] using hx'

public theorem CFSG.theorem_3_6_fitting_commutator_eq_fitting_and_centralizer_eq_bot
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H)))
    (hVK_disj : Disjoint (fittingSubgroup H) K) (hK_ne_bot : K ≠ ⊥) :
    IsInvariant (↥R) (↥H) K →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    fittingSubgroup H ⊔ normalizerOf K = ⊤ →
    ⁅fittingSubgroup H, K⁆ = fittingSubgroup H ∧
      subgroupCentralizerIn (fittingSubgroup H) K = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  intro hK_inv hNK_inv hVNK_sup
  let V : Subgroup H := fittingSubgroup H
  obtain ⟨hCW_disj, hCW_sup⟩ :=
    theorem_3_6_fitting_centralizer_commutator_decomposition H R R₀ p hind hsolvG hodd
      hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K
      (by simpa [V] using hVK_sup) hVK_disj
  have hC_proper : subgroupCentralizerIn V K ≠ V :=
    theorem_3_6_fitting_centralizer_proper H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_disj hK_ne_bot
  have hV_char : V.Characteristic := by
    dsimp [V]
    infer_instance
  let : V.Characteristic := hV_char
  have hV_inv : IsInvariant (↥R) (↥H) V :=
    isInvariant_of_characteristic (A := ↥R) (G := ↥H) V
  let : IsInvariant (↥R) (↥H) V := hV_inv
  have hV_elem : IsElementaryAbelian p ↥V := by
    simpa [V] using
      theorem_3_6_fitting_elementaryAbelian H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  let : IsElementaryAbelian p ↥V := hV_elem
  let : IsMulCommutative ↥V := hV_elem.toIsMulCommutative
  let C : Subgroup H := subgroupCentralizerIn V K
  let W : Subgroup H := ⁅V, K⁆
  have hC_le_V : C ≤ V := inf_le_left
  have hW_le_V : W ≤ V := Subgroup.commutator_le_left (H₁ := V) (H₂ := K)
  have hV_le_norm_C : V ≤ Subgroup.normalizer (C : Set H) := by
    let : (C.subgroupOf V).Normal := by infer_instance
    exact Subgroup.le_normalizer_of_normal_subgroupOf hC_le_V
  have hV_le_norm_W : V ≤ Subgroup.normalizer (W : Set H) := by
    let : (W.subgroupOf V).Normal := by infer_instance
    exact Subgroup.le_normalizer_of_normal_subgroupOf hW_le_V
  have hNK_le_norm_C : normalizerOf K ≤ Subgroup.normalizer (C : Set H) := by
    simpa [C, normalizerOf] using
      subgroupCentralizerIn_normalizer_le (V := V) (K := K) (N := normalizerOf K)
        (show normalizerOf K ≤ Subgroup.normalizer (K : Set H) by simp [normalizerOf])
  have hNK_le_norm_W : normalizerOf K ≤ Subgroup.normalizer (W : Set H) := by
    simpa [W, normalizerOf] using
      commutator_normalizer_le (V := V) (K := K) (N := normalizerOf K)
        (show normalizerOf K ≤ Subgroup.normalizer (K : Set H) by simp [normalizerOf])
  have hC_normal_H : C.Normal := by
    have hnorm_top : Subgroup.normalizer (C : Set H) = ⊤ := by
      apply top_unique
      rw [← hVNK_sup]
      exact sup_le hV_le_norm_C hNK_le_norm_C
    exact Subgroup.normalizer_eq_top_iff.mp hnorm_top
  have hW_normal_H : W.Normal := by
    have hnorm_top : Subgroup.normalizer (W : Set H) = ⊤ := by
      apply top_unique
      rw [← hVNK_sup]
      exact sup_le hV_le_norm_W hNK_le_norm_W
    exact Subgroup.normalizer_eq_top_iff.mp hnorm_top
  have hC_inv : IsInvariant (↥R) (↥H) C := by
    let : IsInvariant (↥R) (↥H) K := hK_inv
    simpa [C] using isInvariant_subgroupCentralizerIn_of_isInvariant (A := ↥R) V K
  have hW_inv : IsInvariant (↥R) (↥H) W := by
    let : IsInvariant (↥R) (↥H) K := hK_inv
    simpa [W] using isInvariant_commutator (A := ↥R) V K
  let Cmap : Subgroup G := C.map H.subtype
  let Wmap : Subgroup G := W.map H.subtype
  have hCmap_normal : Cmap.Normal := by
    let : C.Normal := hC_normal_H
    simpa [Cmap, C] using
      normal_map_subtype_of_normal_and_isInvariant (G := G) (H := H) (R := R) hHR C hC_inv
  have hWmap_normal : Wmap.Normal := by
    let : W.Normal := hW_normal_H
    simpa [Wmap, W] using
      normal_map_subtype_of_normal_and_isInvariant (G := G) (H := H) (R := R) hHR W hW_inv
  have hCmap_disj_Wmap : Disjoint Cmap Wmap := by
    simpa [Cmap, Wmap] using Subgroup.disjoint_map H.subtype_injective hCW_disj
  have hC_or_W_bot : C = ⊥ ∨ W = ⊥ := by
    by_cases hC_bot : C = ⊥
    · exact Or.inl hC_bot
    by_cases hW_bot : W = ⊥
    · exact Or.inr hW_bot
    exfalso
    have hCmap_ne_bot : Cmap ≠ ⊥ := by
      intro hbot
      exact hC_bot ((Subgroup.map_eq_bot_iff_of_injective (H := C) (f := H.subtype)
        H.subtype_injective).1 (by simpa [Cmap] using hbot))
    have hWmap_ne_bot : Wmap ≠ ⊥ := by
      intro hbot
      exact hW_bot ((Subgroup.map_eq_bot_iff_of_injective (H := W) (f := H.subtype)
        H.subtype_injective).1 (by simpa [Wmap] using hbot))
    obtain ⟨M, _, hM_le_Cmap, hM_ne_bot, hMmin⟩ :=
      exists_minimal_normal_le (G := G) Cmap hCmap_normal hCmap_ne_bot
    obtain ⟨N, _, hN_le_Wmap, hN_ne_bot, hNmin⟩ :=
      exists_minimal_normal_le (G := G) Wmap hWmap_normal hWmap_ne_bot
    let : IsMinimalNormal M := {
      minimal := by
        intro L hLnorm hLM
        by_cases hL_bot : L = ⊥
        · exact Or.inl hL_bot
        · exact Or.inr (hMmin L hLnorm hLM hL_bot)
    }
    let : IsMinimalNormal N := {
      minimal := by
        intro L hLnorm hLN
        by_cases hL_bot : L = ⊥
        · exact Or.inl hL_bot
        · exact Or.inr (hNmin L hLnorm hLN hL_bot)
    }
    have hM_le_H : M ≤ H := by
      exact hM_le_Cmap.trans (by simpa [Cmap] using (Subgroup.map_subtype_le C))
    have hN_le_H : N ≤ H := by
      exact hN_le_Wmap.trans (by simpa [Wmap] using (Subgroup.map_subtype_le W))
    have hMN_ne : M ≠ N := by
      intro hMN
      have hM_le_bot : M ≤ ⊥ := by
        intro x hx
        have hxC : x ∈ Cmap := hM_le_Cmap hx
        have hxW : x ∈ Wmap := by simpa [hMN] using hN_le_Wmap (hMN ▸ hx)
        have hxbot : x ∈ (⊥ : Subgroup G) := by
          have hxinf : x ∈ Cmap ⊓ Wmap := ⟨hxC, hxW⟩
          simpa [hCmap_disj_Wmap.eq_bot] using hxinf
        simpa using hxbot
      exact hM_ne_bot (bot_unique hM_le_bot)
    have := theorem_3_6_unique_minimal_normal_in_H H R R₀ M N p hind hM_le_H hN_le_H hM_ne_bot
      hN_ne_bot hsolvG hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
    exact hMN_ne this
  have hC_bot : C = ⊥ := by
    cases hC_or_W_bot with
    | inl h => exact h
    | inr hW_bot =>
        have : C = V := by simpa [C, W, V, hW_bot] using hCW_sup
        exact (hC_proper this).elim
  have hW_eq_V : W = V := by
    simpa [C, W, V, hC_bot] using hCW_sup
  exact ⟨hW_eq_V, hC_bot⟩

public theorem CFSG.theorem_3_6_K_fixedPointSubgroup_on_fitting_eq_bot
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H)))
    (hVK_disj : Disjoint (fittingSubgroup H) K) (hK_ne_bot : K ≠ ⊥) :
    let V : Subgroup H := fittingSubgroup H

    IsInvariant (↥R) (↥H) K →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    V ⊔ normalizerOf K = ⊤ →
    fixedPointSubgroup (↥K) (↥V) = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hK_inv hNK_inv hVNK_sup
  let V : Subgroup H := fittingSubgroup H
  let hKnormV : K ≤ Subgroup.normalizer V := Subgroup.le_normalizer_of_normal (H := V)

  have hCVK_bot :
      subgroupCentralizerIn V K = ⊥ :=
    (theorem_3_6_fitting_commutator_eq_fitting_and_centralizer_eq_bot H R R₀ p hind hsolvG hodd
      hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hVK_disj hK_ne_bot
      hK_inv hNK_inv hVNK_sup).2
  rw [fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn V K hKnormV]
  simpa using congrArg (fun S : Subgroup H => S.subgroupOf V) hCVK_bot

public theorem CFSG.theorem_3_6_normalizer_complement_structure
    {G : Type uG} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    let U : Subgroup H := Fbar.comap q
    ∃ K : Subgroup H,
      K ≤ U ∧
      V ⊔ K = U ∧
      Disjoint V K ∧
      IsInvariant (↥R) (↥H) K ∧
      IsInvariant (↥R) (↥H) (normalizerOf K) ∧
      V ⊔ normalizerOf K = ⊤ ∧
      ⁅V, K⁆ = V ∧
      subgroupCentralizerIn V K = ⊥ ∧
      V ⊓ normalizerOf K = ⊥ ∧
      (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) ∧
      subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  let V : Subgroup H := fittingSubgroup H
  let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
  let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
  let U : Subgroup H := Fbar.comap q
  obtain ⟨K, hK_le_U, hVK_sup, hVK_disj, hK_inv, hNK_inv, hVNK_sup⟩ :=
    theorem_3_6_normalizer_sup_top H R R₀ p hind hsolvG hodd hHR hcopHR hR₀_le
      hR₀_prime hp hCZ hcomm_eq hbad
  let NK : Subgroup H := normalizerOf K
  have hK_map_fitting :
      K.map q = Fbar := theorem_3_6_complement_map_fitting (H := H) K (by simpa [V, Fbar, U, q] using hVK_sup)
  obtain ⟨P, hP_p, hP_not_dvd, hPK_ne_bot⟩ :=
    theorem_3_6_exists_normalizer_pSubgroup_with_nontrivial_commutator H R R₀ p hind hsolvG
      hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K
      (by simpa [V, Fbar, U, q] using hVK_sup) hNK_inv hVNK_sup
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    apply hPK_ne_bot
    apply bot_unique
    intro x hx
    have hxK : x ∈ K := by
      refine (Subgroup.commutator_le (H₁ := normalizerSubtypeMap K P) (H₂ := K) (H₃ := K)).2 ?_ hx
      intro a ha b hb
      have haNK : a ∈ NK := by
        simpa [NK, normalizerSubtypeMap] using (Subgroup.map_subtype_le P ha)
      have haNorm : (a : H) ∈ Subgroup.normalizer (K : Set H) := by
        simpa [NK, normalizerOf] using haNK
      have hconj : (a : H) * b * (a : H)⁻¹ ∈ K := ((Subgroup.mem_normalizer_iff.mp haNorm) b).1 hb
      simpa [commutatorElement_def, mul_assoc] using K.mul_mem hconj (K.inv_mem hb)
    simpa [hK_bot] using hxK
  obtain ⟨hCW_disj, hCW_sup⟩ :=
    theorem_3_6_fitting_centralizer_commutator_decomposition H R R₀ p hind hsolvG hodd
      hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K
      (by simpa [V, Fbar, U, q] using hVK_sup) hVK_disj
  have hC_proper : subgroupCentralizerIn V K ≠ V :=
    theorem_3_6_fitting_centralizer_proper H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_disj hK_ne_bot
  have hV_char : V.Characteristic := by
    dsimp [V]
    infer_instance
  let : V.Characteristic := hV_char
  have hV_inv : IsInvariant (↥R) (↥H) V := isInvariant_of_characteristic (A := ↥R) (G := ↥H) V
  let : IsInvariant (↥R) (↥H) V := hV_inv
  have hV_elem : IsElementaryAbelian p ↥V := by
    simpa [V] using
      theorem_3_6_fitting_elementaryAbelian H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  let : IsElementaryAbelian p ↥V := hV_elem
  let : IsMulCommutative ↥V := hV_elem.toIsMulCommutative
  let C : Subgroup H := subgroupCentralizerIn V K
  let W : Subgroup H := ⁅V, K⁆
  have hC_le_V : C ≤ V := inf_le_left
  have hW_le_V : W ≤ V := Subgroup.commutator_le_left (H₁ := V) (H₂ := K)
  have hV_le_norm_C : V ≤ Subgroup.normalizer (C : Set H) := by
    let : (C.subgroupOf V).Normal := by infer_instance
    exact Subgroup.le_normalizer_of_normal_subgroupOf hC_le_V
  have hV_le_norm_W : V ≤ Subgroup.normalizer (W : Set H) := by
    let : (W.subgroupOf V).Normal := by infer_instance
    exact Subgroup.le_normalizer_of_normal_subgroupOf hW_le_V
  have hNK_le_norm_C : NK ≤ Subgroup.normalizer (C : Set H) := by
    simpa [C, NK, normalizerOf] using
      subgroupCentralizerIn_normalizer_le (V := V) (K := K) (N := NK)
        (show NK ≤ Subgroup.normalizer (K : Set H) by simp [NK, normalizerOf])
  have hNK_le_norm_W : NK ≤ Subgroup.normalizer (W : Set H) := by
    simpa [W, NK, normalizerOf] using
      commutator_normalizer_le (V := V) (K := K) (N := NK)
        (show NK ≤ Subgroup.normalizer (K : Set H) by simp [NK, normalizerOf])
  have hC_normal_H : C.Normal := by
    have hnorm_top : Subgroup.normalizer (C : Set H) = ⊤ := by
      apply top_unique
      rw [← hVNK_sup]
      exact sup_le hV_le_norm_C hNK_le_norm_C
    exact Subgroup.normalizer_eq_top_iff.mp hnorm_top
  have hW_normal_H : W.Normal := by
    have hnorm_top : Subgroup.normalizer (W : Set H) = ⊤ := by
      apply top_unique
      rw [← hVNK_sup]
      exact sup_le hV_le_norm_W hNK_le_norm_W
    exact Subgroup.normalizer_eq_top_iff.mp hnorm_top
  have hC_inv : IsInvariant (↥R) (↥H) C := by
    let : IsInvariant (↥R) (↥H) K := hK_inv
    simpa [C] using isInvariant_subgroupCentralizerIn_of_isInvariant (A := ↥R) V K
  have hW_inv : IsInvariant (↥R) (↥H) W := by
    let : IsInvariant (↥R) (↥H) K := hK_inv
    simpa [W] using isInvariant_commutator (A := ↥R) V K
  let Cmap : Subgroup G := C.map H.subtype
  let Wmap : Subgroup G := W.map H.subtype
  have hCmap_normal : Cmap.Normal := by
    let : C.Normal := hC_normal_H
    simpa [Cmap, C] using
      normal_map_subtype_of_normal_and_isInvariant (G := G) (H := H) (R := R) hHR C hC_inv
  have hWmap_normal : Wmap.Normal := by
    let : W.Normal := hW_normal_H
    simpa [Wmap, W] using
      normal_map_subtype_of_normal_and_isInvariant (G := G) (H := H) (R := R) hHR W hW_inv
  have hCmap_disj_Wmap : Disjoint Cmap Wmap := by
    simpa [Cmap, Wmap] using Subgroup.disjoint_map H.subtype_injective hCW_disj
  have hC_or_W_bot : C = ⊥ ∨ W = ⊥ := by
    by_cases hC_bot : C = ⊥
    · exact Or.inl hC_bot
    by_cases hW_bot : W = ⊥
    · exact Or.inr hW_bot
    exfalso
    have hCmap_ne_bot : Cmap ≠ ⊥ := by
      intro hbot
      exact hC_bot ((Subgroup.map_eq_bot_iff_of_injective (H := C) (f := H.subtype)
        H.subtype_injective).1 (by simpa [Cmap] using hbot))
    have hWmap_ne_bot : Wmap ≠ ⊥ := by
      intro hbot
      exact hW_bot ((Subgroup.map_eq_bot_iff_of_injective (H := W) (f := H.subtype)
        H.subtype_injective).1 (by simpa [Wmap] using hbot))
    obtain ⟨M, hMnorm, hM_le_Cmap, hM_ne_bot, hMmin⟩ :=
      exists_minimal_normal_le (G := G) Cmap hCmap_normal hCmap_ne_bot
    obtain ⟨N, hNnorm, hN_le_Wmap, hN_ne_bot, hNmin⟩ :=
      exists_minimal_normal_le (G := G) Wmap hWmap_normal hWmap_ne_bot
    let : IsMinimalNormal M := {
      minimal := by
        intro L hLnorm hLM
        by_cases hL_bot : L = ⊥
        · exact Or.inl hL_bot
        · exact Or.inr (hMmin L hLnorm hLM hL_bot)
    }
    let : IsMinimalNormal N := {
      minimal := by
        intro L hLnorm hLN
        by_cases hL_bot : L = ⊥
        · exact Or.inl hL_bot
        · exact Or.inr (hNmin L hLnorm hLN hL_bot)
    }
    have hM_le_H : M ≤ H := by
      exact hM_le_Cmap.trans (by simpa [Cmap] using (Subgroup.map_subtype_le C))
    have hN_le_H : N ≤ H := by
      exact hN_le_Wmap.trans (by simpa [Wmap] using (Subgroup.map_subtype_le W))
    have hMN_ne : M ≠ N := by
      intro hMN
      have hM_le_bot : M ≤ ⊥ := by
        intro x hx
        have hxC : x ∈ Cmap := hM_le_Cmap hx
        have hxW : x ∈ Wmap := by simpa [hMN] using hN_le_Wmap (hMN ▸ hx)
        have hxbot : x ∈ (⊥ : Subgroup G) := by
          have hxinf : x ∈ Cmap ⊓ Wmap := ⟨hxC, hxW⟩
          simpa [hCmap_disj_Wmap.eq_bot] using hxinf
        simpa using hxbot
      exact hM_ne_bot (bot_unique hM_le_bot)
    have := theorem_3_6_unique_minimal_normal_in_H H R R₀ M N p hind hM_le_H hN_le_H hM_ne_bot
      hN_ne_bot hsolvG hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
    exact hMN_ne this
  have hC_bot : C = ⊥ := by
    cases hC_or_W_bot with
    | inl h => exact h
    | inr hW_bot =>
        have : C = V := by simpa [C, W, V, hW_bot] using hCW_sup
        exact (hC_proper this).elim
  have hW_eq_V : W = V := by
    simpa [C, W, V, hC_bot] using hCW_sup
  have hVinfNK_le_C : V ⊓ NK ≤ C := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    change (x : H) ∈ Subgroup.centralizer (K : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hxNK : (x : H) ∈ Subgroup.normalizer (K : Set H) := hx.2
    have hconjK : (x : H) * k⁻¹ * (x : H)⁻¹ ∈ K :=
      ((Subgroup.mem_normalizer_iff.mp hxNK) _).1 (K.inv_mem hk)
    have hcommK : ⁅k, (x : H)⁆ ∈ K := by
      simpa [commutatorElement_def, mul_assoc] using K.mul_mem hk hconjK
    have hconjV : (k : H) * (x : H) * (k : H)⁻¹ ∈ V :=
      Subgroup.Normal.conj_mem (inferInstance : V.Normal) x hx.1 (k : H)
    have hcommV : ⁅k, (x : H)⁆ ∈ V := by
      simpa [commutatorElement_def, mul_assoc] using V.mul_mem hconjV (V.inv_mem hx.1)
    have hcomm1 : ⁅k, (x : H)⁆ = 1 := (Subgroup.disjoint_def.mp hVK_disj) hcommV hcommK
    have hkx : (k : H) * (x : H) = x * k := by
      have hkx' : (k : H) * (x : H) * (k : H)⁻¹ = x := by
        simpa [commutatorElement_def, mul_assoc] using congrArg (fun t : H => t * x) hcomm1
      simpa [mul_assoc] using congrArg (fun t : H => t * k) hkx'
    simpa using hkx
  have hVinfNK_bot : V ⊓ NK = ⊥ := by
    apply bot_unique
    intro x hx
    have hxC : x ∈ C := hVinfNK_le_C hx
    simpa [hC_bot] using hxC
  have hNK_map_top : NK.map q = ⊤ := by
    apply top_unique
    intro x _
    rcases QuotientGroup.mk'_surjective V x with ⟨y, rfl⟩
    have hy_sup : y ∈ V ⊔ NK := by
      simpa [V, NK, normalizerOf] using
        (show y ∈ fittingSubgroup H ⊔ Subgroup.normalizer (K : Set H) by
          rw [hVNK_sup]
          simp)
    rcases (Subgroup.mem_sup_of_normal_left (s := V) (t := NK) (x := y)).1 hy_sup with
      ⟨v, hv, n, hn, hmul⟩
    have hvq : q v = 1 := by
      simpa [q] using (QuotientGroup.eq_one_iff (N := V) (x := v)).2 hv
    refine ⟨n, hn, ?_⟩
    calc
      q n = 1 * q n := by simp
      _ = q v * q n := by rw [hvq]
      _ = q (v * n) := by symm; exact map_mul q v n
      _ = q y := by rw [hmul]
  let φ := q.comp NK.subtype
  have hφ_surj : Function.Surjective φ := by
    intro x
    have hx : x ∈ NK.map q := by simp [hNK_map_top]
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hφker : φ.ker = (V ⊓ NK).subgroupOf NK := by
    ext x
    constructor
    · intro hx
      have hxq : q (x : H) = 1 := by simpa [φ] using hx
      have hxV : (x : H) ∈ V := (QuotientGroup.eq_one_iff (N := V) (x := (x : H))).1 hxq
      show (x : H) ∈ V ⊓ NK
      exact ⟨hxV, x.property⟩
    · intro hx
      have hxV : (x : H) ∈ V := by
        have hx' : (x : H) ∈ V ⊓ NK := hx
        exact hx'.1
      have hxq : q (x : H) = 1 := (QuotientGroup.eq_one_iff (N := V) (x := (x : H))).2 hxV
      simpa [φ] using hxq
  have hφker_bot : φ.ker = ⊥ := by
    simpa [hVinfNK_bot] using hφker
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hφker_bot
  have hK_le_NK : K ≤ NK := by
    exact Subgroup.le_normalizer
  have hKsub_map_eq : (K.subgroupOf NK).map φ = Fbar := by
    calc
      (K.subgroupOf NK).map φ = ((K.subgroupOf NK).map NK.subtype).map q := by
        rw [show φ = q.comp NK.subtype by rfl, Subgroup.map_map]
      _ = K.map q := by rw [Subgroup.map_subgroupOf_eq_of_le hK_le_NK]
      _ = Fbar := hK_map_fitting
  have hKsub_nil : Group.IsNilpotent ↥(K.subgroupOf NK) := by
    let eK :
        ↥(K.subgroupOf NK) ≃* ↥Fbar :=
      (Subgroup.equivMapOfInjective (f := φ) (K.subgroupOf NK) hφinj).trans
        (MulEquiv.subgroupCongr hKsub_map_eq)
    exact Group.nilpotent_of_mulEquiv (G := ↥Fbar) (G' := ↥(K.subgroupOf NK)) eK.symm
  have hKsub_normal : (K.subgroupOf NK).Normal := by
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := NK) (N := K)
      (by simp [NK, normalizerOf])
  have hKsub_le_fit : K.subgroupOf NK ≤ fittingSubgroup NK := by
    exact le_sSup ⟨hKsub_normal, hKsub_nil⟩
  have hFnk_map_le_Fbar : (fittingSubgroup NK).map φ ≤ Fbar := by
    have hFnk_map_normal : ((fittingSubgroup NK).map φ).Normal := by
      exact Subgroup.Normal.map (H := fittingSubgroup NK)
        (inferInstance : (fittingSubgroup NK).Normal) φ hφ_surj
    have hFnk_map_nil : Group.IsNilpotent ↥((fittingSubgroup NK).map φ) := by
      let ψ : fittingSubgroup NK →* (fittingSubgroup NK).map φ :=
        { toFun := fun x => ⟨φ x, ⟨x, x.2, rfl⟩⟩
          map_one' := rfl
          map_mul' := by intro a b; rfl }
      have hψ_surj : Function.Surjective ψ := by
        rintro ⟨x, hx⟩
        rcases hx with ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      exact Group.nilpotent_of_surjective (G := ↥(fittingSubgroup NK))
        (G' := ↥((fittingSubgroup NK).map φ)) ψ hψ_surj
    exact le_sSup ⟨hFnk_map_normal, hFnk_map_nil⟩
  have hFit_le_Ksub : fittingSubgroup NK ≤ K.subgroupOf NK := by
    rw [← hKsub_map_eq] at hFnk_map_le_Fbar
    exact (Subgroup.map_le_map_iff_of_injective hφinj).1 hFnk_map_le_Fbar
  have hKsub_fit : (K.subgroupOf NK) = fittingSubgroup NK :=
    le_antisymm hKsub_le_fit hFit_le_Ksub
  let CH : Subgroup H := subgroupCentralizerIn (⊤ : Subgroup H) K
  have hCH_le_NK : CH ≤ NK := by
    have hcent_le : Subgroup.centralizer (K : Set H) ≤ NK := by
      simpa [NK, normalizerOf] using (centralizer_le_normalizer (R := K))
    intro x hx
    exact hcent_le (by simpa using hx.2)
  have hCH_eq : (CH.subgroupOf NK) = subgroupCentralizerIn (⊤ : Subgroup NK) (K.subgroupOf NK) := by
    symm
    simpa [CH] using subgroupCentralizerIn_subgroupOf_eq NK (⊤ : Subgroup H) K hK_le_NK
  have hsolvNK : Group.IsSolvable ↥NK := by infer_instance
  have hcent_fit_le :
      subgroupCentralizerIn (⊤ : Subgroup NK) (fittingSubgroup NK) ≤ fittingSubgroup NK := by
    simpa [subgroupCentralizerIn] using
      centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := ↥NK) hsolvNK
  have hCHsub_le : CH.subgroupOf NK ≤ K.subgroupOf NK := by
    simpa [hCH_eq, hKsub_fit] using hcent_fit_le
  have hCH_le_K : CH ≤ K := by
    intro x hx
    have hxsub : (⟨x, hCH_le_NK hx⟩ : NK) ∈ CH.subgroupOf NK := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxK : (⟨x, hCH_le_NK hx⟩ : NK) ∈ K.subgroupOf NK := hCHsub_le hxsub
    simpa [Subgroup.mem_subgroupOf] using hxK
  exact ⟨K, hK_le_U, hVK_sup, hVK_disj, hK_inv, hNK_inv, hVNK_sup, hW_eq_V, hC_bot,
    hVinfNK_bot, hKsub_fit, hCH_le_K⟩

public theorem CFSG.theorem_3_6_r0_centralizing_complement_forces_cyclic
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (hsolvG : Group.IsSolvable G)
    [hH_normal : H.Normal] (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (K : Subgroup H)
    (hKsub_fit : (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K))
    (hCH_le_K : subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K)
    (hKR₀_bot : ⁅K.map H.subtype, R₀⁆ = ⊥) :
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    let NK : Subgroup H := normalizerOf K
    NK ≤ (subgroupCentralizerIn H R₀).subgroupOf H ∧
      IsCyclic K ∧
      subgroupCentralizerIn (⊤ : Subgroup H) K = K := by
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hNK_inv
  let NK : Subgroup H := normalizerOf K
  have hR₀normH : R₀ ≤ Subgroup.normalizer H := hR₀_le.trans hRnormH

  have hNK_invR : IsInvariant (↥R) (↥H) NK := by
    simpa [NK] using hNK_inv
  have hNK_inv₀ : IsInvariant (↥R₀) (↥H) NK := by
    refine ⟨?_⟩
    intro a x
    have hx := IsInvariant.invariant (A := ↥R) (G := ↥H) (H := NK)
      ⟨(a : G), hR₀_le a.2⟩ x
    change (x ∈ NK) ↔ (a • x ∈ NK) at hx
    exact hx
  let : IsInvariant (↥R₀) (↥H) NK := hNK_inv₀
  have hK_le_NK : K ≤ NK := Subgroup.le_normalizer
  have hR₀_ne_bot : R₀ ≠ ⊥ := by
    intro hR₀_bot
    exact hR₀_prime.ne_one <| by simp [hR₀_bot]
  have : Nontrivial R₀ := (Subgroup.nontrivial_iff_ne_bot R₀).2 hR₀_ne_bot
  have hR₀_coprime_H : Nat.Coprime (Nat.card R₀) (Nat.card H) := by
    have hR₀_dvd_R : Nat.card R₀ ∣ Nat.card R := by
      rw [← natCard_subgroupOf_eq R₀ R hR₀_le]
      exact Subgroup.card_subgroup_dvd_card (R₀.subgroupOf R)
    exact Nat.Coprime.of_dvd_left hR₀_dvd_R hcopHR.symm
  have hNK_coprime_R₀ : Nat.Coprime (Nat.card R₀) (Nat.card NK) := by
    have hNK_dvd_H : Nat.card NK ∣ Nat.card H := by
      simpa [NK] using (Subgroup.card_dvd_of_le (show NK ≤ (⊤ : Subgroup H) by simp))
    exact Nat.Coprime.of_dvd_right hNK_dvd_H hR₀_coprime_H
  have hK_le_centR₀ : K ≤ (subgroupCentralizerIn H R₀).subgroupOf H := by
    have hKmap_centR₀ :
        K.map H.subtype ≤ Subgroup.centralizer (R₀ : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K.map H.subtype) (H₂ := R₀)).1 hKR₀_bot
    intro x hx
    refine ⟨x.2, ?_⟩
    exact hKmap_centR₀ (Subgroup.mem_map_of_mem H.subtype hx)
  have hK_fix_H : K ≤ fixedPointSubgroup (↥R₀) (↥H) := by
    rw [fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn H R₀ hR₀normH]
    exact hK_le_centR₀
  have hK_fix_NK : K.subgroupOf NK ≤ fixedPointSubgroup (↥R₀) (↥NK) := by
    rw [fixedPointSubgroup_subtype_eq_local (A := ↥R₀) (G := ↥H) NK]
    intro x hx
    exact hK_fix_H (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hK_triv_NK :
      ActsTriviallyOnSubgroup (A := ↥R₀) (G := ↥NK) (K.subgroupOf NK) :=
    actsTriviallyOnSubgroup_of_le_fixedPointSubgroup (A := ↥R₀) (G := ↥NK) hK_fix_NK
  have hKsub_inv₀ : IsInvariant (↥R₀) (↥NK) (K.subgroupOf NK) := by
    refine ⟨?_⟩
    intro a x
    constructor
    · intro hx
      have hxfix : a • x = x := hK_triv_NK a x hx
      simpa [hxfix] using hx
    · intro hx
      have hxfix : a⁻¹ • (a • x) = a • x := hK_triv_NK a⁻¹ (a • x) hx
      have hxa : x = a • x := by simpa [smul_smul] using hxfix
      exact hxa ▸ hx
  let : IsInvariant (↥R₀) (↥NK) (K.subgroupOf NK) := hKsub_inv₀
  have hK_triv_pointwise : ∀ a : R₀, ∀ x : K.subgroupOf NK, a • x = x := by
    intro a x
    apply Subtype.ext
    exact hK_fix_NK x.2 a
  have hfix_exists :
      ∃ a : R₀, a ≠ 1 ∧ ∀ x : NK, a • x = x := by
    by_contra hcontra
    push Not at hcontra
    have hfaith_crit : ∀ a : R₀, (∀ x : NK, a • x = x) → a = 1 := by
      intro a ha
      by_contra ha_ne
      rcases hcontra a ha_ne with ⟨x, hx⟩
      exact hx (ha x)
    have hfaith_NK : FaithfulSMul R₀ NK :=
      (faithfulSMul_iff (G := ↥R₀) (α := ↥NK)).2 hfaith_crit
    let : FaithfulSMul R₀ NK := hfaith_NK
    have hsolvNK : Group.IsSolvable ↥NK := by infer_instance
    have hfaith_fit : FaithfulSMul R₀ (fittingSubgroup NK) :=
      faithful_on_fitting_of_coprime (G := ↥NK) (A := ↥R₀) hsolvNK hNK_coprime_R₀
    obtain ⟨a, ha_ne⟩ := exists_ne (1 : R₀)
    have hfit_le_fix : fittingSubgroup NK ≤ fixedPointSubgroup (↥R₀) (↥NK) := by
      rw [← hKsub_fit]
      exact hK_fix_NK
    have hfit_fix : ∀ x : fittingSubgroup NK, a • x = x := by
      intro x
      apply Subtype.ext
      exact hfit_le_fix x.2 a
    exact ha_ne <|
      (faithfulSMul_iff (G := ↥R₀) (α := ↥(fittingSubgroup NK))).1 hfaith_fit a hfit_fix
  obtain ⟨a, ha_ne, ha_fix⟩ := hfix_exists
  let Cfix : Subgroup R₀ := actionCentralizerIn (A := ↥R₀) (G := ↥NK) (⊤ : Subgroup R₀)
  have ha_Cfix : a ∈ Cfix := by
    refine ⟨by simp, ?_⟩
    exact (mem_fixingSubgroup_iff (M := ↥R₀) (s := (Set.univ : Set NK))).2 <| by
      intro x _
      exact ha_fix x
  have hCfix_ne_bot : Cfix ≠ ⊥ := by
    intro hCfix_bot
    exact ha_ne <| by simpa [Cfix, hCfix_bot] using ha_Cfix
  have hCfix_card_ne_one : Nat.card Cfix ≠ 1 := by
    intro hcard
    exact hCfix_ne_bot ((Subgroup.card_eq_one (H := Cfix)).1 hcard)
  have hCfix_card_eq : Nat.card Cfix = Nat.card R₀ := by
    exact (hR₀_prime.eq_one_or_self_of_dvd (Nat.card Cfix)
      (Subgroup.card_subgroup_dvd_card Cfix)).resolve_left hCfix_card_ne_one
  have hCfix_top : Cfix = ⊤ := (Subgroup.card_eq_iff_eq_top (H := Cfix)).1 hCfix_card_eq
  have hNK_fix_NK : (⊤ : Subgroup NK) ≤ fixedPointSubgroup (↥R₀) (↥NK) := by
    intro x hx
    rw [FixedPoints.mem_subgroup]
    intro r
    have hr_Cfix : r ∈ Cfix := by simp [hCfix_top]
    have hr_fix :=
      (mem_fixingSubgroup_iff (M := ↥R₀) (s := (Set.univ : Set NK))).1 hr_Cfix.2
    exact hr_fix x (by trivial)
  have hNK_fix_H : NK ≤ fixedPointSubgroup (↥R₀) (↥H) := by
    intro x hx
    have hxfix : (⟨x, hx⟩ : NK) ∈ fixedPointSubgroup (↥R₀) (↥NK) := hNK_fix_NK (by simp)
    rw [fixedPointSubgroup_subtype_eq_local (A := ↥R₀) (G := ↥H) NK] at hxfix
    exact hxfix
  have hNK_le_centR₀ : NK ≤ (subgroupCentralizerIn H R₀).subgroupOf H := by
    rw [fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn H R₀ hR₀normH] at hNK_fix_H
    exact hNK_fix_H
  let f : NK →* subgroupCentralizerIn H R₀ :=
    { toFun := fun x => ⟨x, by simpa [Subgroup.mem_subgroupOf] using hNK_le_centR₀ x.2⟩
      map_one' := rfl
      map_mul' := by intro x y; rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val hxy
  let : IsZGroup ↥NK := IsZGroup.of_injective (f := f) hf
  have hKsub_nil : Group.IsNilpotent ↥(K.subgroupOf NK) := by
    rw [hKsub_fit]
    infer_instance
  let : Group.IsNilpotent ↥(K.subgroupOf NK) := hKsub_nil
  have hKsub_cyclic : IsCyclic ↥(K.subgroupOf NK) := by infer_instance
  have hK_cyclic : IsCyclic K := by
    let e : K.subgroupOf NK ≃* K :=
      Subgroup.subgroupOfEquivOfLe (G := ↥H) (H := K) (K := NK) hK_le_NK
    exact isCyclic_of_surjective (f := e.toMonoidHom) e.surjective
  let : IsCyclic K := hK_cyclic
  have hK_le_CH : K ≤ subgroupCentralizerIn (⊤ : Subgroup H) K := by
    have hK_le_cent : K ≤ Subgroup.centralizer (K : Set H) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := K)).2 inferInstance
    intro x hx
    exact ⟨by simp, hK_le_cent hx⟩
  exact ⟨hNK_le_centR₀, hK_cyclic, le_antisymm hCH_le_K hK_le_CH⟩

set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.theorem_3_6_r0_commutator_nontrivial
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H))) :
    (hK_inv : IsInvariant (↥R) (↥H) K) →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    fittingSubgroup H ⊔ normalizerOf K = ⊤ →
    fittingSubgroup H ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    ⁅K.map H.subtype, R₀⁆ ≠ ⊥ := by
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hK_inv hNK_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
  let V : Subgroup H := fittingSubgroup H
  let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
  let NK : Subgroup H := normalizerOf K
  let φ : NK →* (↥H ⧸ V) := q.comp NK.subtype
  obtain ⟨P, hP_p, hP_not_dvd, hPK_ne_bot⟩ :=
    theorem_3_6_exists_normalizer_pSubgroup_with_nontrivial_commutator H R R₀ p hind hsolvG
      hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hNK_inv
      hVNK_sup
  intro hKR₀_bot
  obtain ⟨_hNK_le_centR₀, hK_cyclic, hCH_eq⟩ :=
    theorem_3_6_r0_centralizing_complement_forces_cyclic H R R₀ hsolvG hcopHR hR₀_le
      hR₀_prime hCZ K hKsub_fit hCH_le_K hKR₀_bot hNK_inv
  have hV_char : V.Characteristic := by
    dsimp [V]
    infer_instance
  let : V.Characteristic := hV_char
  let : IsInvariant (↥R) (↥H) V := isInvariant_of_characteristic (A := ↥R) (G := ↥H) V
  let : V.Normal := by
    dsimp [V]
    infer_instance
  let : MulDistribMulAction (↥R) (↥H ⧸ V) :=
    quotientMulDistribMulAction (A := ↥R) (G := ↥H) V inferInstance
  have hcommH_map :
      (commutatorAction (A := ↥R) (G := ↥H)).map H.subtype = H := by
    simpa [hcomm_eq] using commutatorAction_subgroup_conj_map_eq_commutator H R hRnormH
  have hcommH_top : commutatorAction (A := ↥R) (G := ↥H) = ⊤ := by
    apply (Subgroup.map_injective (f := H.subtype) H.subtype_injective)
    calc
      (commutatorAction (A := ↥R) (G := ↥H)).map H.subtype = H := hcommH_map
      _ = (⊤ : Subgroup H).map H.subtype := by
        ext x
        constructor
        · intro hx
          exact ⟨⟨x, hx⟩, by simp, rfl⟩
        · rintro ⟨y, -, rfl⟩
          exact y.2
  have hcommQ_top : commutatorAction (A := ↥R) (G := ↥H ⧸ V) = ⊤ := by
    have hcommHq_le :
        (commutatorAction (A := ↥R) (G := ↥H)).map q ≤
          commutatorAction (A := ↥R) (G := ↥H ⧸ V) := by
      let S : Set H := {x : H | ∃ a : R, ∃ g : H, x = g⁻¹ * (a • g)}
      let T : Set (↥H ⧸ V) := {x : ↥H ⧸ V | ∃ a : R, ∃ g : ↥H ⧸ V, x = g⁻¹ * (a • g)}
      rw [commutatorAction_eq_closure (G := ↥H) (A := ↥R)]
      have hmap :
          (Subgroup.closure S).map q = Subgroup.closure (q '' S) := by
        simpa using (MonoidHom.map_closure (f := q) S)
      rw [hmap, commutatorAction_eq_closure (G := ↥H ⧸ V) (A := ↥R)]
      refine (Subgroup.closure_le (K := Subgroup.closure T)).2 ?_
      intro x hx
      rcases hx with ⟨y, hyS, rfl⟩
      rcases hyS with ⟨a, g, rfl⟩
      refine Subgroup.subset_closure ?_
      refine ⟨a, q g, ?_⟩
      calc
        q (g⁻¹ * (a • g)) = (q g)⁻¹ * q (a • g) := by simp
        _ = (q g)⁻¹ * (a • q g) := by simp [q]
    apply top_unique
    have hmap_top :
        (commutatorAction (A := ↥R) (G := ↥H)).map q = ⊤ := by
      rw [hcommH_top]
      exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective V)
    rw [← hmap_top]
    exact hcommHq_le
  let : IsInvariant (↥R) (↥H) NK := hNK_inv
  -- letI : MulDistribMulAction (↥R) (↥NK) := instMulDistribMulAction_subtype (A := ↥R) (G := ↥H) NK
  have hNK_map_top : NK.map q = ⊤ := by
    apply top_unique
    intro x _
    rcases QuotientGroup.mk'_surjective V x with ⟨y, rfl⟩
    have hy_sup : y ∈ V ⊔ NK := by
      simpa [V, NK, normalizerOf] using
        (show y ∈ fittingSubgroup H ⊔ normalizerOf K by
          rw [hVNK_sup]
          simp)
    rcases (Subgroup.mem_sup_of_normal_left (s := V) (t := NK) (x := y)).1 hy_sup with
      ⟨v, hv, n, hn, hmul⟩
    have hvq : q v = 1 := by
      simpa [q] using (QuotientGroup.eq_one_iff (N := V) (x := v)).2 hv
    refine ⟨n, hn, ?_⟩
    calc
      q n = 1 * q n := by simp
      _ = q v * q n := by rw [hvq]
      _ = q (v * n) := by symm; exact map_mul q v n
      _ = q y := by rw [hmul]
  have hφ_surj : Function.Surjective φ := by
    intro x
    have hx : x ∈ NK.map q := by simp [hNK_map_top]
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hφker : φ.ker = V.subgroupOf NK := by
    ext x
    constructor
    · intro hx
      have hxq : q (x : H) = 1 := by simpa [φ] using hx
      have hxV : (x : H) ∈ V := (QuotientGroup.eq_one_iff (N := V) (x := (x : H))).1 hxq
      exact hxV
    · intro hx
      have hxV : (x : H) ∈ V := hx
      have hxq : q (x : H) = 1 := (QuotientGroup.eq_one_iff (N := V) (x := (x : H))).2 hxV
      simpa [φ] using hxq
  have hφker_bot : φ.ker = ⊥ := by
    have hVsub_bot : V.subgroupOf NK = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot, disjoint_iff]
      exact hVinfNK_bot
    rw [hφker, hVsub_bot]
  have hφ_smul (a : R) (n : NK) : φ (a • n) = a • φ n := by
    change q (((a • n : NK) : H)) = a • q (n : H)
    change q (a • (n : H)) = a • q (n : H)
    simp [q]
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hφker_bot
  have hcommNK_map :
      (commutatorAction (A := ↥R) (G := ↥NK)).map φ = commutatorAction (A := ↥R) (G := ↥H ⧸ V) := by
    let S : Set NK := {x : NK | ∃ a : R, ∃ n : NK, x = n⁻¹ * (a • n)}
    let T : Set (↥H ⧸ V) := {x : ↥H ⧸ V | ∃ a : R, ∃ y : ↥H ⧸ V, x = y⁻¹ * (a • y)}
    have himage : φ '' S = T := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases hy with ⟨a, n, rfl⟩
        refine ⟨a, φ n, ?_⟩
        rw [map_mul, map_inv, hφ_smul]
      · rintro ⟨a, y, rfl⟩
        rcases hφ_surj y with ⟨n, rfl⟩
        refine ⟨n⁻¹ * (a • n), ⟨a, n, rfl⟩, ?_⟩
        rw [map_mul, map_inv, hφ_smul]
    calc
      (commutatorAction (A := ↥R) (G := ↥NK)).map φ = (Subgroup.closure S).map φ := by
        simpa [S] using
          congrArg (fun L : Subgroup NK => L.map φ) (commutatorAction_eq_closure (G := ↥NK) (A := ↥R))
      _ = Subgroup.closure (φ '' S) := by
        simpa using (MonoidHom.map_closure (f := φ) S)
      _ = Subgroup.closure T := by rw [himage]
      _ = commutatorAction (A := ↥R) (G := ↥H ⧸ V) := by
        symm
        simpa [T] using (commutatorAction_eq_closure (G := ↥H ⧸ V) (A := ↥R))
  have hcommNK_top : commutatorAction (A := ↥R) (G := ↥NK) = ⊤ := by
    apply (Subgroup.map_injective (f := φ) hφinj)
    calc
      (commutatorAction (A := ↥R) (G := ↥NK)).map φ =
          commutatorAction (A := ↥R) (G := ↥H ⧸ V) := hcommNK_map
      _ = ⊤ := hcommQ_top
      _ = (⊤ : Subgroup NK).map φ := by
        symm
        exact Subgroup.map_top_of_surjective φ hφ_surj
  let : IsInvariant (↥R) (↥H) K := hK_inv
  -- letI : MulDistribMulAction (↥R) (↥K) := instMulDistribMulAction_subtype (A := ↥R) (G := ↥H) K
  let ρ : R →* MulAut K := MulDistribMulAction.toMulAut (G := ↥R) (M := ↥K)
  let ψ : NK →* MulAut K := by
    change Subgroup.normalizer (K : Set H) →* MulAut K
    exact Subgroup.normalizerMonoidHom (H := K)
  let eAut : MulAut K ≃* (ZMod (Nat.card K))ˣ := IsCyclic.mulAutMulEquiv (G := K)
  let : CommGroup (MulAut K) := MonoidHom.commGroupOfInjective eAut.toMonoidHom eAut.injective
  have hψker :
      ψ.ker = (subgroupCentralizerIn (⊤ : Subgroup H) K).subgroupOf NK := by
    ext x
    change x ∈ K.normalizerMonoidHom.ker ↔
      (x : H) ∈ (⊤ : Subgroup H) ⊓ Subgroup.centralizer (K : Set H)
    rw [Subgroup.normalizerMonoidHom_ker (H := K)]
    constructor
    · intro hx
      exact ⟨by simp, hx⟩
    · intro hx
      exact hx.2
  have hψker_K : ψ.ker = K.subgroupOf NK := by
    simpa [hCH_eq] using hψker
  have hψ_smul (a : R) (n : NK) : ψ (a • n) = ψ n := by
    apply DFunLike.ext
    intro k
    apply Subtype.ext
    have hfirst :
        (K.normalizerMonoidHom (a • n)) k = a • (K.normalizerMonoidHom n) (a⁻¹ • k) := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change ((a • (n : H)) * (k : H) * (a • (n : H))⁻¹ : H) =
          (a • (((K.normalizerMonoidHom n) (a⁻¹ • k) : K) : H) : H)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change ((a • (n : H)) * (k : H) * (a • (n : H))⁻¹ : H) =
          (a • (((n : H) * ((a⁻¹ • k : K) : H) * (n : H)⁻¹ : H) : H) : H)
      apply Subtype.ext
      have hk :
          (((a⁻¹ • k : K) : H) : G) = (a : G)⁻¹ * (((k : K) : H) : G) * (a : G) := by
        change (((a⁻¹ : R) • ((k : K) : H) : H) : G) =
            (a : G)⁻¹ * (((k : K) : H) : G) * (a : G)
        simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      simp [hk, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
    have hcomm :
        (ρ a * ψ n) ((ρ a)⁻¹ k) = (ψ n * ρ a) ((ρ a)⁻¹ k) := by
      exact congrArg (fun f : MulAut K => f ((ρ a)⁻¹ k)) (mul_comm (ρ a) (ψ n))
    have hcomm' : (ρ a) (ψ n ((ρ a)⁻¹ k)) = ψ n k := by
      simpa using hcomm
    calc
      (((ψ (a • n)) k : K) : H) = ((ρ a) (ψ n ((ρ a)⁻¹ k)) : H) := by
        have hfirst' := congrArg (fun x : K => ((x : K) : H)) hfirst
        change (((ψ (a • n)) k : K) : H) =
          ((ρ a) (ψ n ((ρ a)⁻¹ k)) : H) at hfirst'
        exact hfirst'
      _ = ((ψ n k : K) : H) := by
        exact congrArg (fun x : K => ((x : K) : H)) hcomm'
  have hcommNK_le_ker : commutatorAction (A := ↥R) (G := ↥NK) ≤ ψ.ker := by
    rw [commutatorAction_eq_closure (G := ↥NK) (A := ↥R)]
    refine (Subgroup.closure_le (K := ψ.ker)).2 ?_
    intro x hx
    rcases hx with ⟨a, n, rfl⟩
    change ψ (n⁻¹ * (a • n)) = 1
    rw [map_mul, map_inv, hψ_smul]
    simp
  have hNK_le_K : NK ≤ K := by
    have htop_le : (⊤ : Subgroup NK) ≤ K.subgroupOf NK := by
      simpa [hcommNK_top, hψker_K] using hcommNK_le_ker
    intro x hx
    have hxsub : (⟨x, hx⟩ : NK) ∈ K.subgroupOf NK := htop_le (by simp)
    simpa [Subgroup.mem_subgroupOf] using hxsub
  let Psub : Subgroup H := normalizerSubtypeMap K P
  have hPsub_le_K : Psub ≤ K := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact hNK_le_K y.2
  have hPsub_comm : ⁅Psub, K⁆ = ⊥ := by
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Psub) (H₂ := K)).2
    have hK_le_cent : K ≤ Subgroup.centralizer (K : Set H) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := K)).2 inferInstance
    exact hPsub_le_K.trans hK_le_cent
  exact hPK_ne_bot (by simpa [Psub] using hPsub_comm)

public theorem CFSG.theorem_3_6_centralizer_KR₀_on_fitting_eq_bot
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H))) :
    (hK_inv : IsInvariant (↥R) (↥H) K) →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    fittingSubgroup H ⊔ normalizerOf K = ⊤ →
    fittingSubgroup H ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    let Vg : Subgroup G := (fittingSubgroup H).map H.subtype
    let KR₀ : Subgroup G := K.map H.subtype ⊔ R₀
    let _ : (fittingSubgroup H).Characteristic := by infer_instance
    let _ : Vg.Normal := by
      dsimp [Vg]
      exact ConjAct.normal_of_characteristic_of_normal
    haveI : Subgroup.Normalizes KR₀ Vg := ⟨Subgroup.le_normalizer_of_normal (H := Vg)⟩
    actionCentralizerIn (A := ↥KR₀) (G := ↥Vg) (⊤ : Subgroup KR₀) = ⊥ := by
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hK_inv hNK_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
  let V : Subgroup H := fittingSubgroup H
  let Kg : Subgroup G := K.map H.subtype
  let Vg : Subgroup G := V.map H.subtype
  let KR₀ : Subgroup G := Kg ⊔ R₀
  let Kgsub : Subgroup KR₀ := Kg.subgroupOf KR₀
  let R₀sub : Subgroup KR₀ := R₀.subgroupOf KR₀
  have hV_char : V.Characteristic := by
    dsimp [V]
    infer_instance
  let : V.Characteristic := hV_char
  have hVg_normal : Vg.Normal := by
    dsimp [Vg, V]
    exact ConjAct.normal_of_characteristic_of_normal
  have hKR₀normVg : KR₀ ≤ Subgroup.normalizer Vg := Subgroup.le_normalizer_of_normal (H := Vg)
  have : Subgroup.Normalizes KR₀ Vg := ⟨hKR₀normVg⟩
  let ρ : KR₀ →* MulAut Vg := MulDistribMulAction.toMulAut (G := ↥KR₀) (M := ↥Vg)
  let C : Subgroup KR₀ := actionCentralizerIn (A := ↥KR₀) (G := ↥Vg) (⊤ : Subgroup KR₀)
  have hCker : C = ρ.ker := by
    ext x
    constructor
    · intro hx
      change ρ x = 1
      ext v
      have hxfix :
          x ∈ fixingSubgroupOf (↥KR₀) (↥Vg) (Set.univ : Set Vg) := by
        simpa [C, actionCentralizerIn] using hx
      have hvfix := (mem_fixingSubgroup_iff (M := ↥KR₀) (s := (Set.univ : Set Vg))).1 hxfix v
        (by trivial)
      exact congrArg Subtype.val hvfix
    · intro hx
      have hxfix :
          x ∈ fixingSubgroupOf (↥KR₀) (↥Vg) (Set.univ : Set Vg) := by
        refine (mem_fixingSubgroup_iff (M := ↥KR₀) (s := (Set.univ : Set Vg))).2 ?_
        intro v _
        have hv : ρ x v = v := by
          simpa [ρ, MulDistribMulAction.toMulAut_apply] using DFunLike.congr_fun hx v
        exact hv
      simpa [C, actionCentralizerIn] using hxfix
  have hC_normal : C.Normal := by
    rw [hCker]
    exact MonoidHom.normal_ker ρ
  have hK_le_NK : K ≤ normalizerOf K := by
    exact Subgroup.le_normalizer
  have hVinfK_bot : V ⊓ K = ⊥ := by
    apply bot_unique
    intro x hx
    have hxNK : x ∈ normalizerOf K := hK_le_NK hx.2
    have hxbot : x ∈ V ⊓ normalizerOf K := ⟨hx.1, hxNK⟩
    have : x ∈ (⊥ : Subgroup H) := by
      rwa [hVinfNK_bot] at hxbot
    simpa using this
  have hVK_disj : Disjoint V K := by
    rw [disjoint_iff]
    exact hVinfK_bot
  have hVgKg_disj : Disjoint Vg Kg := by
    simpa [Vg, Kg] using Subgroup.disjoint_map H.subtype_injective hVK_disj
  have hCKg_disj : Disjoint C Kgsub := by
    rw [Subgroup.disjoint_def]
    intro x hxC hxKg
    have hxfix :
        x ∈ fixingSubgroupOf (↥KR₀) (↥Vg) (Set.univ : Set Vg) := by
      simpa [C, actionCentralizerIn] using hxC
    have hxKg' : (x : KR₀) ∈ Kgsub := hxKg
    have hxKgG : ((x : KR₀) : G) ∈ Kg := by
      simpa [Kgsub, Subgroup.mem_subgroupOf] using hxKg'
    rcases Subgroup.mem_map.mp hxKgG with ⟨y, hyK, hyx⟩
    have hy_cent : (y : H) ∈ Subgroup.centralizer (V : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hvVg : ((v : H) : G) ∈ Vg := by
        exact Subgroup.mem_map_of_mem H.subtype hv
      let v' : Vg := ⟨((v : H) : G), hvVg⟩
      have hvfix :
          x • v' = v' :=
        (mem_fixingSubgroup_iff (M := ↥KR₀) (s := (Set.univ : Set Vg))).1 hxfix
          v' (by trivial)
      have hvfix' :
          (((x : KR₀) : G) * (((v : H) : G)) * (((x : KR₀) : G))⁻¹ : G) = ((v : H) : G) := by
        exact congrArg Subtype.val hvfix
      have hcommG : (((x : KR₀) : G) * (((v : H) : G)) : G) = (((v : H) : G) * (((x : KR₀) : G))) := by
        have := congrArg (fun z : G => z * (((x : KR₀) : G))) hvfix'
        simpa [mul_assoc] using this
      have hcommY : ((((v : H) : G) * ((y : H) : G)) : G) = (((y : H) : G) * ((v : H) : G)) := by
        calc
          (((v : H) : G) * ((y : H) : G) : G) = (((v : H) : G) * (((x : KR₀) : G)) : G) := by
            simpa using congrArg (fun z : G => ((v : H) : G) * z) hyx
          _ = (((x : KR₀) : G) * ((v : H) : G) : G) := hcommG.symm
          _ = (((y : H) : G) * ((v : H) : G) : G) := by
            simpa using congrArg (fun z : G => z * ((v : H) : G)) hyx.symm
      apply Subtype.ext
      simpa using hcommY
    have hyV : y ∈ V := by
      have hcent_eq :
          Subgroup.centralizer (fittingSubgroup H : Set H) = fittingSubgroup H := by
        simpa [V] using
          theorem_3_6_centralizer_fitting_eq_fitting H R R₀ p hind hsolvG hodd hHR
            hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
      have hy_cent' : (y : H) ∈ Subgroup.centralizer (fittingSubgroup H : Set H) := by
        simpa [V] using hy_cent
      rw [hcent_eq] at hy_cent'
      simpa [V] using hy_cent'
    have hxVg : ((x : KR₀) : G) ∈ Vg := by
      rw [← hyx]
      exact Subgroup.mem_map_of_mem H.subtype hyV
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hVgKg_disj) hxVg hxKgG
  let hR₀normH : R₀ ≤ Subgroup.normalizer H := hR₀_le.trans hRnormH
  have : Subgroup.Normalizes R₀ H := ⟨hR₀normH⟩
  have hK_inv₀ : IsInvariant (↥R₀) (↥H) K := by
    refine ⟨?_⟩
    intro a x
    have hx := hK_inv.invariant (A := ↥R) (G := ↥H) (H := K)
      ⟨a, hR₀_le a.2⟩ x
    change (x ∈ K) ↔ (a • x ∈ K) at hx
    exact hx
  let : IsInvariant (↥R₀) (↥H) K := hK_inv₀
  have hR₀_le_normKg : R₀ ≤ Subgroup.normalizer (Kg : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyK, rfl⟩
      have hy' : (⟨a, ha⟩ : R₀) • y ∈ K := (IsInvariant.invariant (A := ↥R₀) (G := ↥H)
          (H := K) ⟨a, ha⟩ y).1 hyK
      refine Subgroup.mem_map.mpr ?_
      exact ⟨(⟨a, ha⟩ : R₀) • y, hy', by
        simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]⟩
    · intro hx
      have ha_inv : a⁻¹ ∈ R₀ := R₀.inv_mem ha
      rcases Subgroup.mem_map.mp hx with ⟨y, hyK, hyx⟩
      have hy' : (⟨a⁻¹, ha_inv⟩ : R₀) • y ∈ K := (IsInvariant.invariant (A := ↥R₀) (G := ↥H)
          (H := K) ⟨a⁻¹, ha_inv⟩ y).1 hyK
      refine Subgroup.mem_map.mpr ?_
      exact ⟨(⟨a⁻¹, ha_inv⟩ : R₀) • y, hy', by
        have hyx' : (↑y * a : G) = (a * x * a⁻¹) * a := by
          simpa [mul_assoc] using congrArg (fun z : G => z * a) hyx
        calc
          H.subtype ((⟨a⁻¹, ha_inv⟩ : R₀) • y) = a⁻¹ * (↑y * a) := by
            simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
          _ = a⁻¹ * ((a * x * a⁻¹) * a) := by
            exact congrArg (fun z : G => a⁻¹ * z) hyx'
          _ = x := by simp [mul_assoc]⟩
  have hKgsub_normal : Kgsub.Normal := by
    have hKR₀_le_normKg : KR₀ ≤ Subgroup.normalizer (Kg : Set G) := by
      exact sup_le Kg.le_normalizer hR₀_le_normKg
    simpa [Kgsub, KR₀] using
      (Subgroup.normal_subgroupOf_of_le_normalizer (H := KR₀) (N := Kg) hKR₀_le_normKg)
  have hKgR₀_disj : Disjoint Kg R₀ := by
    rw [Subgroup.disjoint_def]
    intro x hxKg hxR₀
    rcases Subgroup.mem_map.mp hxKg with ⟨y, hyK, rfl⟩
    have hyH : ((y : H) : G) ∈ H := y.2
    exact (Subgroup.disjoint_def.mp hHR.disjoint) hyH (hR₀_le hxR₀)
  have hKgsubR₀sub_disj : Disjoint Kgsub R₀sub := by
    rw [Subgroup.disjoint_def]
    intro x hxKg hxR₀
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hKgR₀_disj)
      (by simpa [Kgsub, Subgroup.mem_subgroupOf] using hxKg)
      (by simpa [R₀sub, Subgroup.mem_subgroupOf] using hxR₀)
  have hKgsub_sup_R₀sub : Kgsub ⊔ R₀sub = ⊤ := by
    calc
      Kgsub ⊔ R₀sub = (Kg ⊔ R₀).subgroupOf KR₀ := by
        symm
        exact Subgroup.subgroupOf_sup (A := Kg) (A' := R₀) (B := KR₀) le_sup_left le_sup_right
      _ = ⊤ := by
        simp [KR₀]
  have hR₀sub_compl : R₀sub.IsComplement' Kgsub := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKgsubR₀sub_disj.symm ?_
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hxsup' : x ∈ Kgsub ⊔ R₀sub := by
        simp [hKgsub_sup_R₀sub]
      have hxsup : x ∈ R₀sub ⊔ Kgsub := by
        simpa [sup_comm] using hxsup'
      rcases (Subgroup.mem_sup_of_normal_right (s := R₀sub) (t := Kgsub) (x := x)).1 hxsup with
        ⟨r, hr, k, hk, rfl⟩
      exact Set.mem_mul.mpr ⟨r, hr, k, hk, rfl⟩
  have hR₀sub_card_eq : Nat.card R₀sub = Nat.card R₀ := by
    simpa using Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := R₀) (K := KR₀) le_sup_right).toEquiv
  have hKgsub_card_eq : Nat.card Kgsub = Nat.card Kg := by
    simpa using Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := Kg) (K := KR₀) le_sup_left).toEquiv
  have hKg_card_eq : Nat.card Kg = Nat.card K := by
    simpa [Kg] using
      (Subgroup.card_map_of_injective (K := K) (f := H.subtype) H.subtype_injective)
  have hKg_coprime_R₀ : Nat.Coprime (Nat.card Kg) (Nat.card R₀) := by
    rw [hKg_card_eq]
    exact Nat.Coprime.of_dvd (Subgroup.card_subgroup_dvd_card K) (Subgroup.card_dvd_of_le hR₀_le)
      hcopHR
  have hR₀sub_index_eq : R₀sub.index = Nat.card Kgsub := by
    have hmul :
        Nat.card R₀sub * R₀sub.index = Nat.card R₀sub * Nat.card Kgsub := by
      calc
        Nat.card R₀sub * R₀sub.index = Nat.card KR₀ := by
          rw [Nat.mul_comm]
          exact Subgroup.index_mul_card (H := R₀sub)
        _ = Nat.card R₀sub * Nat.card Kgsub := hR₀sub_compl.card_mul_card.symm
    exact Nat.mul_left_cancel (Nat.card_pos (α := R₀sub)) hmul
  let q' : Nat.Primes := ⟨Nat.card R₀, hR₀_prime⟩
  let π : Set Nat.Primes := {q'}
  have hR₀sub_hall : IsHallSubgroup π R₀sub := by
    refine isHallSubgroup_of (G := KR₀) (π := π) (H := R₀sub) (hcard := ?_) (hindex := ?_)
    · intro q hq_dvd
      have hq_dvd' : q.val ∣ Nat.card R₀ := by
        simpa [hR₀sub_card_eq] using hq_dvd
      have hq_eq : q = q' := by
        apply Subtype.ext
        simpa [q'] using ((hR₀_prime.dvd_iff_eq q.2.ne_one).1 hq_dvd').symm
      simp [π, hq_eq]
    · intro q hq_mem hq_dvd
      have hq_eq : q = q' := by simpa [π] using hq_mem
      subst hq_eq
      rw [hR₀sub_index_eq, hKgsub_card_eq] at hq_dvd
      exact ((hR₀_prime.coprime_iff_not_dvd).1 hKg_coprime_R₀.symm) hq_dvd
  let πq : KR₀ →* (↥KR₀ ⧸ Kgsub) := QuotientGroup.mk' Kgsub
  let πqC : C →* (↥KR₀ ⧸ Kgsub) := πq.comp C.subtype
  have hπqC_ker_bot : πqC.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxKg : ((x : C) : KR₀) ∈ Kgsub := by
      change πq (((x : C) : KR₀)) = 1 at hx
      exact (QuotientGroup.eq_one_iff (N := Kgsub) (x := ((x : C) : KR₀))).1 hx
    exact Subtype.ext ((Subgroup.disjoint_def.mp hCKg_disj) x.2 hxKg)
  have hπqC_inj : Function.Injective πqC :=
    (MonoidHom.ker_eq_bot_iff πqC).1 hπqC_ker_bot
  have hπqC_map_eq : (⊤ : Subgroup C).map πqC = C.map πq := by
    ext z
    constructor
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  have hCmap_card : Nat.card (C.map πq) = Nat.card C := by
    calc
      Nat.card (C.map πq) = Nat.card ((⊤ : Subgroup C).map πqC) := by rw [hπqC_map_eq]
      _ = Nat.card (⊤ : Subgroup C) := Subgroup.card_map_of_injective (K := (⊤ : Subgroup C))
        (f := πqC) hπqC_inj
      _ = Nat.card C := by simp
  have hquot_card_eq : Nat.card (↥KR₀ ⧸ Kgsub) = Nat.card R₀ := by
    exact Nat.card_congr
      (hR₀sub_compl.QuotientMulEquiv.trans
        (Subgroup.subgroupOfEquivOfLe (H := R₀) (K := KR₀) le_sup_right)).toEquiv
  have hquot_prime : Nat.Prime (Nat.card (↥KR₀ ⧸ Kgsub)) := by
    simpa [hquot_card_eq] using hR₀_prime
  let : Fact (Nat.Prime (Nat.card (↥KR₀ ⧸ Kgsub))) := ⟨hquot_prime⟩
  have hCmap_bot_or_top : C.map πq = ⊥ ∨ C.map πq = ⊤ :=
    Subgroup.eq_bot_or_eq_top_of_prime_card (C.map πq)
  cases hCmap_bot_or_top with
  | inl hCmap_bot =>
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxmap : πq x = 1 := by
        have : πq x ∈ (⊥ : Subgroup (↥KR₀ ⧸ Kgsub)) := by
          exact hCmap_bot ▸ ⟨x, hx, rfl⟩
        simpa using this
      have hxone : (⟨x, hx⟩ : C) = 1 := by
        apply hπqC_inj
        show πqC ⟨x, hx⟩ = πqC 1
        simpa [πqC] using hxmap
      exact congrArg Subtype.val hxone
  | inr hCmap_top =>
      have hC_card_eq : Nat.card C = Nat.card R₀ := by
        calc
          Nat.card C = Nat.card (C.map πq) := hCmap_card.symm
          _ = Nat.card (↥KR₀ ⧸ Kgsub) := (Subgroup.card_eq_iff_eq_top (H := C.map πq)).2 hCmap_top
          _ = Nat.card R₀ := hquot_card_eq
      have hC_index_eq : C.index = R₀sub.index := by
        have hmul :
            Nat.card R₀ * C.index = Nat.card R₀ * R₀sub.index := by
          calc
            Nat.card R₀ * C.index = Nat.card C * C.index := by rw [hC_card_eq.symm]
            _ = Nat.card KR₀ := by
              rw [Nat.mul_comm]
              exact Subgroup.index_mul_card (H := C)
            _ = Nat.card R₀sub * R₀sub.index := by
              rw [Nat.mul_comm]
              exact (Subgroup.index_mul_card (H := R₀sub)).symm
            _ = Nat.card R₀ * R₀sub.index := by rw [hR₀sub_card_eq]
        exact Nat.mul_left_cancel (Nat.card_pos (α := R₀)) hmul
      have hC_hall : IsHallSubgroup π C := by
        refine isHallSubgroup_of (G := KR₀) (π := π) (H := C) (hcard := ?_) (hindex := ?_)
        · intro q hq_dvd
          have hq_eq : q = q' := by
            apply Subtype.ext
            have hq_dvd' : q.val ∣ Nat.card R₀ := by simpa [hC_card_eq] using hq_dvd
            simpa [q'] using ((hR₀_prime.dvd_iff_eq q.2.ne_one).1 hq_dvd').symm
          simp [π, hq_eq]
        · intro q hq_mem hq_dvd
          have hq_eq : q = q' := by simpa [π] using hq_mem
          subst hq_eq
          exact (hR₀sub_hall.p_in_pi_of_p_dvd_index q' (hC_index_eq ▸ hq_dvd)) (by simp [π])
      have hCR₀_eq : R₀sub = C := by
        let : C.Normal := hC_normal
        exact IsHallSubgroup.eq_of_normal (hH := hC_hall) (hK := hR₀sub_hall)
      have hR₀sub_normal : R₀sub.Normal := by
        rw [hCR₀_eq]
        exact hC_normal
      have hKg_le_cent : Kg ≤ Subgroup.centralizer (R₀ : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hxsub : (⟨x, Subgroup.mem_sup_left hx⟩ : KR₀) ∈ Kgsub := by
          simpa [Kgsub, Subgroup.mem_subgroupOf] using hx
        have hysub : (⟨y, Subgroup.mem_sup_right hy⟩ : KR₀) ∈ R₀sub := by
          simpa [R₀sub, Subgroup.mem_subgroupOf] using hy
        have hcommG : (x * y : G) = y * x := by
          exact congrArg Subtype.val <|
            (Subgroup.commute_of_normal_of_disjoint Kgsub R₀sub hKgsub_normal hR₀sub_normal
              hKgsubR₀sub_disj _ _ hxsub hysub).eq
        simpa using hcommG.symm
      have hKR₀_bot : ⁅Kg, R₀⁆ = ⊥ := by
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Kg) (H₂ := R₀)).2 hKg_le_cent
      exact False.elim <|
        (theorem_3_6_r0_commutator_nontrivial H R R₀ p hind hsolvG hodd hHR hcopHR
          hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup hVinfNK_bot
          hKsub_fit hCH_le_K) hKR₀_bot

set_option maxHeartbeats 1000000

public theorem CFSG.theorem_3_6_commutator_bot_of_local_sub_comm
    {G : Type*} [Group G] (H : Subgroup G) (K : Subgroup H) (R₀ : Subgroup G) :
    let Kg : Subgroup G := K.map H.subtype
    let KR₀ : Subgroup G := Kg ⊔ R₀
    let Kgsub : Subgroup KR₀ := Kg.subgroupOf KR₀
    let R₀sub : Subgroup KR₀ := R₀.subgroupOf KR₀
    ⁅R₀sub, Kgsub⁆ ≤ ⊥ →
    ⁅K.map H.subtype, R₀⁆ = ⊥ := by
  dsimp
  intro hcomm_sub
  exact commutator_eq_bot_of_sup_subgroupOf_commutator_le_bot (G := G) (K.map H.subtype) R₀ hcomm_sub

public theorem CFSG.theorem_3_6_false_of_local_sub_comm
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H))) :
    IsInvariant (↥R) (↥H) K →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    fittingSubgroup H ⊔ normalizerOf K = ⊤ →
    fittingSubgroup H ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    let Kg : Subgroup G := K.map H.subtype
    let KR₀ : Subgroup G := Kg ⊔ R₀
    let Kgsub : Subgroup KR₀ := Kg.subgroupOf KR₀
    let R₀sub : Subgroup KR₀ := R₀.subgroupOf KR₀
    ⁅R₀sub, Kgsub⁆ ≤ ⊥ →
    False := by
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hK_inv hNK_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K hcomm_sub
  have hcomm_KgR₀_bot : ⁅K.map H.subtype, R₀⁆ = ⊥ := by
    exact theorem_3_6_commutator_bot_of_local_sub_comm H K R₀ hcomm_sub
  exact
    (theorem_3_6_r0_commutator_nontrivial H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup hVinfNK_bot
      hKsub_fit hCH_le_K) hcomm_KgR₀_bot

public theorem CFSG.theorem_3_6_false_of_comm_sub
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H))) :
    IsInvariant (↥R) (↥H) K →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    fittingSubgroup H ⊔ normalizerOf K = ⊤ →
    fittingSubgroup H ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    (Kg KR₀ : Subgroup G) →
    (Kgsub : Subgroup KR₀) →
    (R₀sub : Subgroup KR₀) →
    Kg = K.map H.subtype →
    KR₀ = Kg ⊔ R₀ →
    Kgsub = Kg.subgroupOf KR₀ →
    R₀sub = R₀.subgroupOf KR₀ →
    ⁅R₀sub, Kgsub⁆ ≤ ⊥ →
    False := by
  intro hK_inv hNK_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K Kg KR₀ Kgsub R₀sub
    hKg hKR₀ hKgsub hR₀sub hcomm_sub
  subst hR₀sub hKgsub hKR₀ hKg
  exact
    theorem_3_6_false_of_local_sub_comm H R R₀ p hind hsolvG hodd hHR hcopHR hR₀_le
      hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup hVinfNK_bot hKsub_fit
      hCH_le_K hcomm_sub

public theorem CFSG.theorem_3_6_fixed_points_of_R₀_on_fitting
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H))) :
    IsInvariant (↥R) (↥H) K →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    fittingSubgroup H ⊔ normalizerOf K = ⊤ →
    fittingSubgroup H ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    let Vg : Subgroup G := (fittingSubgroup H).map H.subtype
    Nat.card (subgroupCentralizerIn Vg R₀) = p := by
  set_option maxHeartbeats 800000 in
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  intro hK_inv hNK_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
  let V : Subgroup H := fittingSubgroup H
  let Kg : Subgroup G := K.map H.subtype
  let Vg : Subgroup G := V.map H.subtype
  let KR₀ : Subgroup G := Kg ⊔ R₀
  let Kgsub : Subgroup KR₀ := Kg.subgroupOf KR₀
  let R₀sub : Subgroup KR₀ := R₀.subgroupOf KR₀
  let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
  let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
  let U : Subgroup H := Fbar.comap q
  have hV_char : V.Characteristic := by
    dsimp [V]
    infer_instance
  let : V.Characteristic := hV_char
  have hVg_normal : Vg.Normal := by
    dsimp [Vg, V]
    exact ConjAct.normal_of_characteristic_of_normal
  have hKR₀normVg : KR₀ ≤ Subgroup.normalizer Vg := Subgroup.le_normalizer_of_normal (H := Vg)
  have : Subgroup.Normalizes KR₀ Vg := ⟨hKR₀normVg⟩
  have hR₀normVg : R₀ ≤ Subgroup.normalizer Vg := Subgroup.le_normalizer_of_normal (H := Vg)
  have : Subgroup.Normalizes R₀ Vg := ⟨hR₀normVg⟩
  have hV_elem : IsElementaryAbelian p ↥V := by
    simpa [V] using
      theorem_3_6_fitting_elementaryAbelian H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  let : IsElementaryAbelian p ↥V := hV_elem
  have hVg_elem : IsElementaryAbelian p ↥Vg := by
    refine
      { toIsMulCommutative := by infer_instance
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    rcases Subgroup.mem_map.mp x.2 with ⟨y, hyV, hyx⟩
    let yV : V := ⟨y, hyV⟩
    have hy_pow : yV ^ p = 1 := by
      exact
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p ↥V) yV
    have hy_pow_G : ((((yV : V) : H) : G) ^ p) = 1 := by
      simpa using congrArg H.subtype (congrArg Subtype.val hy_pow)
    have hx_eq : ((x : Vg) : G) = (((yV : V) : H) : G) := by
      simpa [yV] using hyx.symm
    calc
      ((x : Vg) : G) ^ p = (((yV : V) : H) : G) ^ p := by simp [hx_eq]
      _ = 1 := hy_pow_G
  let : IsElementaryAbelian p ↥Vg := hVg_elem
  let : CommGroup Vg := IsMulCommutative.instCommGroup
  let ψ : KR₀ →* MulAut Vg := MulDistribMulAction.toMulAut (G := ↥KR₀) (M := ↥Vg)
  let ρ : Representation (ZMod p) KR₀ (Additive Vg) := {
    toFun := fun a =>
      let eAdd : Additive Vg ≃+ Additive Vg :=
        MulEquiv.toAdditive (ψ a)
      let eLin : Additive Vg ≃ₗ[ZMod p] Additive Vg :=
        eAdd.toLinearEquiv (fun c x => by
          simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
      eLin.toLinearMap
    map_one' := by
      ext x
      apply Additive.toMul.injective
      simp [ψ, MulDistribMulAction.toMulAut]
    map_mul' := by
      intro a b
      ext x
      apply Additive.toMul.injective
      simp [ψ, MulDistribMulAction.toMulAut, smul_smul] }
  have hV_le_U : V ≤ U := by
    intro x hx
    change q x ∈ Fbar
    have hx1 : q x = 1 := by
      exact (QuotientGroup.eq_one_iff (N := V) (x := x)).2 hx
    simp [hx1]
  have hK_le_U : K ≤ U := by
    intro x hx
    have hx' : x ∈ V ⊔ K := Subgroup.mem_sup_right hx
    rw [hVK_sup] at hx'
    exact hx'
  have hU_map : U.map q = Fbar := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      rcases QuotientGroup.mk'_surjective V x with ⟨y, rfl⟩
      exact ⟨y, by simpa [U, q] using hx, rfl⟩
  have hquot_card : Nat.card (↥U ⧸ V.subgroupOf U) = Nat.card Fbar := by
    calc
      Nat.card (↥U ⧸ V.subgroupOf U) = Nat.card (U.map q) := by
        symm
        simpa [q] using natCard_map_mk'_eq U V
      _ = Nat.card Fbar := by rw [hU_map]
  have hK_le_NK : K ≤ normalizerOf K := Subgroup.le_normalizer
  have hVinfK_bot : V ⊓ K = ⊥ := by
    apply bot_unique
    intro x hx
    have hxNK : x ∈ normalizerOf K := hK_le_NK hx.2
    have hxbot : x ∈ V ⊓ normalizerOf K := ⟨hx.1, hxNK⟩
    have : x ∈ (⊥ : Subgroup H) := by
      rwa [hVinfNK_bot] at hxbot
    simpa using this
  have hVK_disj : Disjoint V K := by
    rw [disjoint_iff]
    exact hVinfK_bot
  have hVsub_comp : (V.subgroupOf U).IsComplement' (K.subgroupOf U) := by
    rw [show U = V ⊔ K from hVK_sup.symm]
    exact isComplement'_subgroupOf_sup_of_disjoint V K hVK_disj
  have hKsub_card : Nat.card (K.subgroupOf U) = Nat.card Fbar := by
    calc
      Nat.card (K.subgroupOf U) = (V.subgroupOf U).index := by
        symm
        exact hVsub_comp.symm.index_eq_card
      _ = Nat.card (↥U ⧸ V.subgroupOf U) := by simp [Subgroup.index_eq_card]
      _ = Nat.card Fbar := hquot_card
  have hK_card : Nat.card K = Nat.card Fbar := by
    rw [← natCard_subgroupOf_eq K U hK_le_U, hKsub_card]
  have hKg_card_eq : Nat.card Kg = Nat.card K := by
    simpa [Kg] using
      (Subgroup.card_map_of_injective (K := K) (f := H.subtype) H.subtype_injective)
  have hR₀sub_card_eq : Nat.card R₀sub = Nat.card R₀ := by
    simpa using Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := R₀) (K := KR₀) le_sup_right).toEquiv
  have hKgsub_card_eq : Nat.card Kgsub = Nat.card Kg := by
    simpa using Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := Kg) (K := KR₀) le_sup_left).toEquiv
  have hp_dvd_H : p ∣ Nat.card H := by
    by_contra hp_ndvd_H
    exact hbad <|
      hasPLengthOne_of_coprime_card (p := p) ((hp.coprime_iff_not_dvd).2 hp_ndvd_H)
  have hcop_p_R : Nat.Coprime p (Nat.card R) := Nat.Coprime.of_dvd_left hp_dvd_H hcopHR
  have hcop_p_R₀ : Nat.Coprime p (Nat.card R₀) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hR₀_le) hcop_p_R
  have hcop_p_Fbar : Nat.Coprime p (Nat.card Fbar) := by
    simpa [V, Fbar] using
      theorem_3_6_fitting_quotient_coprime_card H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hcop_p_K : Nat.Coprime p (Nat.card K) := by
    rw [hK_card]
    exact hcop_p_Fbar
  have hcop_p_Kgsub : Nat.Coprime p (Nat.card Kgsub) := by
    rw [hKgsub_card_eq, hKg_card_eq]
    exact hcop_p_K
  have hcop_p_R₀sub : Nat.Coprime p (Nat.card R₀sub) := by
    rw [hR₀sub_card_eq]
    exact hcop_p_R₀
  let hR₀normH : R₀ ≤ Subgroup.normalizer H := hR₀_le.trans hRnormH
  have : Subgroup.Normalizes R₀ H := ⟨hR₀normH⟩
  have hK_inv₀ : IsInvariant (↥R₀) (↥H) K := by
    refine ⟨?_⟩
    intro a x
    have hx := hK_inv.invariant (A := ↥R) (G := ↥H) (H := K)
      ⟨a, hR₀_le a.2⟩ x
    change (x ∈ K) ↔ (a • x ∈ K) at hx
    exact hx
  let : IsInvariant (↥R₀) (↥H) K := hK_inv₀
  have hR₀_le_normKg : R₀ ≤ Subgroup.normalizer (Kg : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyK, rfl⟩
      have hy' : (⟨a, ha⟩ : R₀) • y ∈ K := (IsInvariant.invariant (A := ↥R₀) (G := ↥H)
          (H := K) ⟨a, ha⟩ y).1 hyK
      refine Subgroup.mem_map.mpr ?_
      exact ⟨(⟨a, ha⟩ : R₀) • y, hy', by
        simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]⟩
    · intro hx
      have ha_inv : a⁻¹ ∈ R₀ := R₀.inv_mem ha
      rcases Subgroup.mem_map.mp hx with ⟨y, hyK, hyx⟩
      have hy' : (⟨a⁻¹, ha_inv⟩ : R₀) • y ∈ K := (IsInvariant.invariant (A := ↥R₀) (G := ↥H)
          (H := K) ⟨a⁻¹, ha_inv⟩ y).1 hyK
      refine Subgroup.mem_map.mpr ?_
      exact ⟨(⟨a⁻¹, ha_inv⟩ : R₀) • y, hy', by
        have hyx' : (↑y * a : G) = (a * x * a⁻¹) * a := by
          simpa [mul_assoc] using congrArg (fun z : G => z * a) hyx
        calc
          H.subtype ((⟨a⁻¹, ha_inv⟩ : R₀) • y) = a⁻¹ * (↑y * a) := by
            simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
          _ = a⁻¹ * ((a * x * a⁻¹) * a) := by
            exact congrArg (fun z : G => a⁻¹ * z) hyx'
          _ = x := by simp [mul_assoc]⟩
  have hKgsub_normal : Kgsub.Normal := by
    have hKR₀_le_normKg : KR₀ ≤ Subgroup.normalizer (Kg : Set G) := sup_le Kg.le_normalizer hR₀_le_normKg
    simpa [Kgsub, KR₀] using
      (Subgroup.normal_subgroupOf_of_le_normalizer (H := KR₀) (N := Kg) hKR₀_le_normKg)
  have hKgR₀_disj : Disjoint Kg R₀ := by
    rw [Subgroup.disjoint_def]
    intro x hxKg hxR₀
    rcases Subgroup.mem_map.mp hxKg with ⟨y, hyK, rfl⟩
    have hyH : ((y : H) : G) ∈ H := y.2
    exact (Subgroup.disjoint_def.mp hHR.disjoint) hyH (hR₀_le hxR₀)
  have hKgsubR₀sub_disj : Disjoint Kgsub R₀sub := by
    rw [Subgroup.disjoint_def]
    intro x hxKg hxR₀
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hKgR₀_disj)
      (by simpa [Kgsub, Subgroup.mem_subgroupOf] using hxKg)
      (by simpa [R₀sub, Subgroup.mem_subgroupOf] using hxR₀)
  have hKgsub_sup_R₀sub : Kgsub ⊔ R₀sub = ⊤ := by
    calc
      Kgsub ⊔ R₀sub = (Kg ⊔ R₀).subgroupOf KR₀ := by
        symm
        exact Subgroup.subgroupOf_sup (A := Kg) (A' := R₀) (B := KR₀) le_sup_left le_sup_right
      _ = ⊤ := by
        simp [KR₀]
  have hR₀sub_compl : R₀sub.IsComplement' Kgsub := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKgsubR₀sub_disj.symm ?_
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hxsup' : x ∈ Kgsub ⊔ R₀sub := by
        simp [hKgsub_sup_R₀sub]
      have hxsup : x ∈ R₀sub ⊔ Kgsub := by
        simpa [sup_comm] using hxsup'
      rcases (Subgroup.mem_sup_of_normal_right (s := R₀sub) (t := Kgsub) (x := x)).1 hxsup with
        ⟨r, hr, k, hk, rfl⟩
      exact Set.mem_mul.mpr ⟨r, hr, k, hk, rfl⟩
  have hcopKgsubR₀sub : Nat.Coprime (Nat.card Kgsub) (Nat.card R₀sub) := by
    rw [hKgsub_card_eq, hKg_card_eq, hR₀sub_card_eq]
    exact Nat.Coprime.of_dvd (Subgroup.card_subgroup_dvd_card K) (Subgroup.card_dvd_of_le hR₀_le)
      hcopHR
  have hR₀sub_compl_symm : Kgsub.IsComplement' R₀sub := hR₀sub_compl.symm
  have hoddKR₀ : Odd (Nat.card KR₀) := odd_of_card_dvd hodd (Subgroup.card_subgroup_dvd_card KR₀)
  have hsolvKR₀ : Group.IsSolvable ↥KR₀ := by infer_instance
  have hoddKR₀' : Odd (Nat.card ↥KR₀) := by simpa using hoddKR₀
  have hR₀sub_prime : Nat.Prime (Nat.card R₀sub) := by
    rw [hR₀sub_card_eq]
    exact hR₀_prime
  have hKR₀_coprime_p : Nat.Coprime p (Nat.card KR₀) := by
    rw [← hR₀sub_compl.card_mul_card]
    exact Nat.Coprime.mul_right hcop_p_R₀sub hcop_p_Kgsub
  have hcharKR₀ : ringChar (ZMod p) = 0 ∨
      (Nat.Prime (ringChar (ZMod p)) ∧ Nat.Coprime (ringChar (ZMod p)) (Nat.card KR₀)) := by
    right
    rw [ZMod.ringChar_zmod_n]
    exact ⟨hp, hKR₀_coprime_p⟩
  have hcharKR₀' : ringChar (ZMod p) = 0 ∨
      (Nat.Prime (ringChar (ZMod p)) ∧ Nat.Coprime (ringChar (ZMod p)) (Nat.card ↥KR₀)) := by
    simpa using hcharKR₀
  have hψker : ψ.ker = actionCentralizerIn (A := ↥KR₀) (G := ↥Vg) (⊤ : Subgroup KR₀) := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      refine ⟨by simp, ?_⟩
      refine (mem_fixingSubgroup_iff (M := ↥KR₀) (s := (Set.univ : Set Vg))).2 ?_
      intro v _
      have hv : ψ x v = v := by
        simpa [ψ, MulDistribMulAction.toMulAut_apply] using DFunLike.congr_fun hx v
      exact hv
    · intro hx
      change ψ x = 1
      ext v
      have hxfix : x ∈ fixingSubgroupOf (↥KR₀) (↥Vg) (Set.univ : Set Vg) := by
        simpa [actionCentralizerIn] using hx
      exact congrArg Subtype.val <|
        (mem_fixingSubgroup_iff (M := ↥KR₀) (s := (Set.univ : Set Vg))).1 hxfix v (by trivial)
  have hρker_eq_ψker : ρ.ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      ext v
      have hv : ρ x (Additive.ofMul v) = Additive.ofMul v := by
        simpa using congrArg (fun f => f (Additive.ofMul v)) hx
      have hv' := congrArg Additive.toMul hv
      change x • v = v at hv'
      exact congrArg Subtype.val hv'
    · intro hx
      apply DFunLike.ext
      intro v
      apply Additive.toMul.injective
      have hv : ψ x (Additive.toMul v) = Additive.toMul v := by
        simpa [ψ, MulDistribMulAction.toMulAut_apply] using
          DFunLike.congr_fun hx (Additive.toMul v)
      change ψ x (Additive.toMul v) = Additive.toMul v
      exact hv
  have hρker : ρ.ker = actionCentralizerIn (A := ↥KR₀) (G := ↥Vg) (⊤ : Subgroup KR₀) := by
    rw [hρker_eq_ψker, hψker]
  have hρker_bot : ρ.ker = ⊥ := by
    rw [hρker]
    exact theorem_3_6_centralizer_KR₀_on_fitting_eq_bot H R R₀ p hind hsolvG hodd hHR
      hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup
      hVinfNK_bot hKsub_fit hCH_le_K
  let Cfix : Subgroup G := subgroupCentralizerIn Vg R₀
  set_option maxHeartbeats 800000 in
  have hfixR₀sub_of_hCfix_bot : Cfix = ⊥ → ρ.fixedSubspace R₀sub = ⊥ := by
    intro hCfix_bot
    rw [Representation.fixedSubspace, Submodule.eq_bot_iff]
    intro v hv
    rw [Representation.mem_invariants] at hv
    have hvC : (((Additive.toMul v : Vg) : G)) ∈ Cfix := by
      refine ⟨(Additive.toMul v).2, ?_⟩
      change (((Additive.toMul v : Vg) : G)) ∈ Subgroup.centralizer (R₀ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      let rsub : R₀sub :=
        ⟨⟨r, Subgroup.mem_sup_right hr⟩, by simpa [R₀sub, Subgroup.mem_subgroupOf] using hr⟩
      have hvr : (ρ.comp R₀sub.subtype) rsub v = v := hv rsub
      have hvr_mul : (Additive.toMul ((ρ.comp R₀sub.subtype) rsub v) : Vg) = Additive.toMul v := by
        exact congrArg Additive.toMul hvr
      have hconjV : (((rsub : R₀sub) : KR₀) • (Additive.toMul v) : Vg) = Additive.toMul v := by
        change (Additive.toMul ((ρ.comp R₀sub.subtype) rsub v) : Vg) = Additive.toMul v
        exact hvr_mul
      have hconj :
          (((r : G) * (((Additive.toMul v : Vg) : G)) * (r : G)⁻¹ : G) =
            (((Additive.toMul v : Vg) : G))) := by
        exact congrArg Subtype.val hconjV
      have hcomm :
          (((r : G) * (((Additive.toMul v : Vg) : G)) : G) =
            (((Additive.toMul v : Vg) : G) * (r : G))) := by
        calc
          (((r : G) * (((Additive.toMul v : Vg) : G)) : G)) =
              ((((r : G) * (((Additive.toMul v : Vg) : G)) * (r : G)⁻¹ : G) * (r : G))) := by
                simp [mul_assoc]
          _ = (((Additive.toMul v : Vg) : G) * (r : G)) := by
              exact congrArg (fun z : G => z * (r : G)) hconj
      exact hcomm
    have hvCbot : (((Additive.toMul v : Vg) : G)) ∈ (⊥ : Subgroup G) := by
      have hvC' : (((Additive.toMul v : Vg) : G)) ∈ Cfix := hvC
      rw [hCfix_bot] at hvC'
      exact hvC'
    have hv1 : (((Additive.toMul v : Vg) : G)) = 1 := by
      exact hvCbot
    have hv1' : (Additive.toMul v : Vg) = 1 := by
      apply Subtype.ext
      exact hv1
    exact toMul_eq_one.mp hv1'
  set_option maxHeartbeats 800000 in
  have hcomm_sub_of_hCfix_bot : Cfix = ⊥ → ⁅R₀sub, Kgsub⁆ ≤ ⊥ := by
    intro hCfix_bot
    have hfixR₀sub : ρ.fixedSubspace R₀sub = ⊥ := hfixR₀sub_of_hCfix_bot hCfix_bot
    have hcomm_sub' :=
      theorem_3_4 (G := ↥KR₀) (F := ZMod p) (V := Additive ↥Vg) (K := Kgsub) (R := R₀sub)
        (ρ := ρ) (hsolvG := hsolvKR₀) (hodd := hoddKR₀') (hK_normal := hKgsub_normal)
        (hKR := hR₀sub_compl_symm) (hcopKR := hcopKgsubR₀sub) (hR_prime := hR₀sub_prime)
        (hchar := hcharKR₀') (hfixR := hfixR₀sub)
    have hρcentKg_bot : ρ.centralizerIn Kgsub = ⊥ := by
      exact centralizerIn_eq_bot_of_ker_eq_bot ρ Kgsub hρker_bot
    intro x hx
    have hx' := hcomm_sub' hx
    rw [hρcentKg_bot] at hx'
    exact hx'
  set_option maxHeartbeats 800000 in
  have hCfix_ne_bot : Cfix ≠ ⊥ := by
    intro hCfix_bot
    have hcomm_sub : ⁅R₀sub, Kgsub⁆ ≤ ⊥ := hcomm_sub_of_hCfix_bot hCfix_bot
    exact
      theorem_3_6_false_of_comm_sub H R R₀ p hind hsolvG hodd hHR hcopHR hR₀_le
        hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup hVinfNK_bot hKsub_fit
        hCH_le_K Kg KR₀ Kgsub R₀sub rfl rfl rfl rfl hcomm_sub
  have hVg_le_H : Vg ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyV, rfl⟩
    exact y.2
  have hCfix_le_centH : Cfix ≤ subgroupCentralizerIn H R₀ := by
    intro x hx
    exact ⟨hVg_le_H hx.1, hx.2⟩
  let f : Cfix →* subgroupCentralizerIn H R₀ :=
    { toFun := fun x => ⟨x, hCfix_le_centH x.2⟩
      map_one' := rfl
      map_mul' := by intro x y; rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val hxy
  let : IsZGroup ↥Cfix := IsZGroup.of_injective (f := f) hf
  have hVg_le_cent : Vg ≤ Subgroup.centralizer (Vg : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := Vg)).2 inferInstance
  have hCfix_comm : IsMulCommutative ↥Cfix := by
    refine (Subgroup.le_centralizer_iff_isMulCommutative (K := Cfix)).1 ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hVg_le_cent hx.1 y hy.1
  let : IsMulCommutative ↥Cfix := hCfix_comm
  let : CommGroup Cfix := IsMulCommutative.instCommGroup
  let : Group.IsNilpotent ↥Cfix := by infer_instance
  have hCfix_cyclic : IsCyclic ↥Cfix := by infer_instance
  have hCfix_card_ne_one : Nat.card Cfix ≠ 1 := by
    intro hcard
    exact hCfix_ne_bot ((Subgroup.card_eq_one (H := Cfix)).1 hcard)
  obtain ⟨x, hxorder⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Cfix)
  let xVg : Vg := ⟨(x : G), x.2.1⟩
  have hxpowVg : xVg ^ p = 1 := by
    exact
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p ↥Vg) xVg
  have hxpow : x ^ p = 1 := by
    apply Subtype.ext
    simpa [xVg] using congrArg Subtype.val hxpowVg
  have horder_dvd_p : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxpow
  have hxorder_ne_one : orderOf x ≠ 1 := by
    simpa [hxorder] using hCfix_card_ne_one
  have horder_eq_p : orderOf x = p := by
    exact (hp.eq_one_or_self_of_dvd (orderOf x) horder_dvd_p).resolve_left hxorder_ne_one
  calc
    Nat.card Cfix = orderOf x := hxorder.symm
    _ = p := horder_eq_p

public theorem CFSG.theorem_3_6_centralizer_of_R₀_on_P_eq_bot
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H)))
    (P : Subgroup (normalizerOf K)) (hP_p : IsPGroup p P) :
    IsInvariant (↥R) (↥H) K →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    fittingSubgroup H ⊔ normalizerOf K = ⊤ →
    fittingSubgroup H ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    subgroupCentralizerIn ((normalizerSubtypeMap K P).map H.subtype) R₀ = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  intro hK_inv hNK_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
  let V : Subgroup H := fittingSubgroup H
  let NK : Subgroup H := normalizerOf K
  let Psub : Subgroup H := normalizerSubtypeMap K P
  let NKg : Subgroup G := NK.map H.subtype
  let Psubg : Subgroup G := Psub.map H.subtype
  let Vg : Subgroup G := V.map H.subtype
  let Cfix : Subgroup G := subgroupCentralizerIn Vg R₀
  let CP : Subgroup G := subgroupCentralizerIn Psubg R₀
  have hV_char : V.Characteristic := by
    dsimp [V]
    infer_instance
  let : V.Characteristic := hV_char
  have hVg_normal : Vg.Normal := by
    dsimp [Vg, V]
    exact ConjAct.normal_of_characteristic_of_normal
  have hPsub_le_NK : Psub ≤ NK := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  have hPsub_p : IsPGroup p Psub := by
    change IsPGroup p (normalizerSubtypeMap K P)
    exact isPGroup_normalizerSubtypeMap K P hP_p
  have hPsubg_p : IsPGroup p Psubg := by
    simpa [Psubg] using IsPGroup.map (p := p) (H := Psub) hPsub_p H.subtype
  have hCP_le_Psubg : CP ≤ Psubg := by
    intro x hx
    exact hx.1
  have hCP_p : IsPGroup p CP := hPsubg_p.to_le hCP_le_Psubg
  have hCfix_card : Nat.card Cfix = p := by
    exact
      theorem_3_6_fixed_points_of_R₀_on_fitting H R R₀ p hind hsolvG hodd hHR
        hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup
        hVinfNK_bot hKsub_fit hCH_le_K
  have hCfix_cyclic : IsCyclic ↥Cfix := isCyclic_of_prime_card hCfix_card
  have hCfix_p : IsPGroup p Cfix := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by simp [hCfix_card]⟩
  have hCP_le_normR₀ : CP ≤ Subgroup.normalizer (R₀ : Set G) := by
    have hCP_le_centR₀ : CP ≤ Subgroup.centralizer (R₀ : Set G) := by
      intro x hx
      exact hx.2
    exact hCP_le_centR₀.trans (centralizer_le_normalizer (R := R₀))
  have hCP_le_normCfix : CP ≤ Subgroup.normalizer (Cfix : Set G) := by
    exact subgroupCentralizerIn_normalizer_le (V := Vg) (K := R₀) (N := CP) hCP_le_normR₀
  have : Subgroup.Normalizes CP Cfix := ⟨hCP_le_normCfix⟩
  have hCP_triv : ActsTrivially (A := ↥CP) (G := ↥Cfix) := by
    exact
      actsTrivially_of_isPGroup_on_cyclic_prime_order hp hCP_p hCfix_cyclic hCfix_card
  have hCPCfix_comm : ⁅CP, Cfix⁆ = ⊥ := by
    exact
      commutator_eq_bot_of_actsTrivially_subgroup_conj (K := Cfix) (R := CP) hCP_le_normCfix hCP_triv
  have hVNK_disj : Disjoint V NK := by
    rw [disjoint_iff]
    exact hVinfNK_bot
  have hNKg_disj_Vg : Disjoint NKg Vg := by
    simpa [NKg, NK, Vg, V] using (Subgroup.disjoint_map H.subtype_injective hVNK_disj).symm
  have hPsubg_le_NKg : Psubg ≤ NKg := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact Subgroup.mem_map_of_mem H.subtype (hPsub_le_NK hy)
  have hCP_le_NKg : CP ≤ NKg := hCP_le_Psubg.trans hPsubg_le_NKg
  have hCP_disj_Cfix : Disjoint CP Cfix := by
    rw [Subgroup.disjoint_def]
    intro x hxCP hxCfix
    exact (Subgroup.disjoint_def.mp hNKg_disj_Vg) (hCP_le_NKg hxCP) hxCfix.1
  let M : Subgroup G := CP ⊔ Cfix
  have hM_p : IsPGroup p M := by
    dsimp [M]
    exact IsPGroup.to_sup_of_normal_right' hCP_p hCfix_p hCP_le_normCfix
  have hVg_le_H : Vg ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyV, rfl⟩
    exact y.2
  have hCfix_le_CH : Cfix ≤ subgroupCentralizerIn H R₀ := by
    intro x hx
    exact ⟨hVg_le_H hx.1, hx.2⟩
  have hPsubg_le_H : Psubg ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  have hCP_le_CH : CP ≤ subgroupCentralizerIn H R₀ := by
    intro x hx
    exact ⟨hPsubg_le_H hx.1, hx.2⟩
  have hM_le_CH : M ≤ subgroupCentralizerIn H R₀ := sup_le hCP_le_CH hCfix_le_CH
  let f : M →* subgroupCentralizerIn H R₀ :=
    { toFun := fun x => ⟨x, hM_le_CH x.2⟩
      map_one' := rfl
      map_mul' := by intro x y; rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val hxy
  let : IsZGroup ↥M := IsZGroup.of_injective (f := f) hf
  let : Group.IsNilpotent ↥M := hM_p.isNilpotent
  have hM_cyclic : IsCyclic ↥M := by infer_instance
  have hCfixsub_normal : (Cfix.subgroupOf M).Normal := by
    have hM_le_normCfix : M ≤ Subgroup.normalizer (Cfix : Set G) := sup_le hCP_le_normCfix
      Cfix.le_normalizer
    simpa [M] using
      (Subgroup.normal_subgroupOf_of_le_normalizer (H := M) (N := Cfix) hM_le_normCfix)
  have hCPsub_disj_Cfixsub : Disjoint (CP.subgroupOf M) (Cfix.subgroupOf M) := by
    rw [Subgroup.disjoint_def]
    intro x hxCP hxCfix
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hCP_disj_Cfix)
      (by simpa [Subgroup.mem_subgroupOf] using hxCP)
      (by simpa [Subgroup.mem_subgroupOf] using hxCfix)
  have hCPsub_sup_Cfixsub : CP.subgroupOf M ⊔ Cfix.subgroupOf M = ⊤ := by
    calc
      CP.subgroupOf M ⊔ Cfix.subgroupOf M = (CP ⊔ Cfix).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := CP) (A' := Cfix) (B := M) le_sup_left le_sup_right
      _ = ⊤ := by simp [M]
  have hCPsub_compl : (CP.subgroupOf M).IsComplement' (Cfix.subgroupOf M) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hCPsub_disj_Cfixsub ?_
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hxsup : x ∈ CP.subgroupOf M ⊔ Cfix.subgroupOf M := by
        simp [hCPsub_sup_Cfixsub]
      rcases (Subgroup.mem_sup_of_normal_right (s := CP.subgroupOf M) (t := Cfix.subgroupOf M)
        (x := x)).1 hxsup with ⟨y, hy, z, hz, rfl⟩
      exact Set.mem_mul.mpr ⟨y, hy, z, hz, rfl⟩
  have hCP_le_centCfix : CP ≤ Subgroup.centralizer Cfix := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hCPCfix_comm
  let μ : (CP.subgroupOf M × Cfix.subgroupOf M) →* M :=
    { toFun := fun x => x.1 * x.2
      map_one' := by simp
      map_mul' := by
        intro x y
        have hcomm : Commute (y.1 : M) (x.2 : M) := by
          apply Subtype.ext
          exact (hCP_le_centCfix y.1.2 (x.2 : M) x.2.2).symm
        calc
          ((x.1 * y.1) * (x.2 * y.2) : M) = x.1 * (y.1 * x.2) * y.2 := by
            simp [mul_assoc]
          _ = x.1 * (x.2 * y.1) * y.2 := by rw [hcomm.eq]
          _ = (x.1 * x.2) * (y.1 * y.2) := by simp [mul_assoc] }
  have hμ_bij : Function.Bijective μ := by
    simpa [μ] using
      (Subgroup.isComplement_iff_bijective (s := CP.subgroupOf M) (t := Cfix.subgroupOf M)).1
        ((Subgroup.isComplement'_def).1 hCPsub_compl)
  let eM : (CP.subgroupOf M × Cfix.subgroupOf M) ≃* M := MulEquiv.ofBijective μ hμ_bij
  have hprod_cyclic : IsCyclic (CP.subgroupOf M × Cfix.subgroupOf M) := by
    rw [eM.isCyclic]
    exact hM_cyclic
  have hcop_prod :
      Nat.Coprime (Nat.card (CP.subgroupOf M)) (Nat.card (Cfix.subgroupOf M)) := by
    exact (Group.isCyclic_prod_iff (M := ↥(CP.subgroupOf M)) (N := ↥(Cfix.subgroupOf M))).1
      hprod_cyclic |>.2.2
  have hCPsub_card : Nat.card (CP.subgroupOf M) = Nat.card CP := by
    exact natCard_subgroupOf_eq CP M le_sup_left
  have hCfixsub_card : Nat.card (Cfix.subgroupOf M) = Nat.card Cfix := by
    exact natCard_subgroupOf_eq Cfix M le_sup_right
  have hp_not_dvd_CP : ¬ p ∣ Nat.card CP := by
    have hcop_CP_p : Nat.Coprime (Nat.card CP) p := by
      simpa [hCPsub_card, hCfixsub_card, hCfix_card] using hcop_prod
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop_CP_p.symm
  have hCP_card_one : Nat.card CP = 1 := (hCP_p.card_eq_or_dvd).resolve_right hp_not_dvd_CP
  exact (Subgroup.card_eq_one (H := CP)).1 hCP_card_one

public theorem CFSG.theorem_3_6_pSubgroup_eq_commutator_with_R₀
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H)))
    (P : Subgroup (normalizerOf K)) (hP_p : IsPGroup p P) :
    (hK_inv : IsInvariant (↥R) (↥H) K) →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    fittingSubgroup H ⊔ normalizerOf K = ⊤ →
    fittingSubgroup H ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    let Psubg : Subgroup G := (normalizerSubtypeMap K P).map H.subtype
    Psubg = ⁅Psubg, R₀⁆ ∧ Psubg ≤ ⁅Psubg, R⁆ := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hK_inv hNK_inv hP_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
  let NK : Subgroup H := normalizerOf K
  let Psub : Subgroup H := normalizerSubtypeMap K P
  let Psubg : Subgroup G := Psub.map H.subtype
  let hR₀normH : R₀ ≤ Subgroup.normalizer H := hR₀_le.trans hRnormH
  have : Subgroup.Normalizes R₀ H := ⟨hR₀normH⟩
  have hPsub_inv₀ : IsInvariant (↥R₀) (↥H) Psub := by
    refine ⟨?_⟩
    intro a x
    have hx := IsInvariant.invariant (A := ↥R) (G := ↥H) (H := Psub)
      ⟨(a : G), hR₀_le a.2⟩ x
    change (x ∈ Psub) ↔ (a • x ∈ Psub) at hx
    exact hx
  have hPsubg_le_H : Psubg ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  have hCP_bot : subgroupCentralizerIn Psubg R₀ = ⊥ := by
    exact
      theorem_3_6_centralizer_of_R₀_on_P_eq_bot H R R₀ p hind hsolvG hodd hHR
        hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup P hP_p hK_inv hNK_inv
        hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
  have hR₀normPsubg : R₀ ≤ Subgroup.normalizer Psubg := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨(⟨a, ha⟩ : R₀) • y, ?_, ?_⟩
      · exact (IsInvariant.invariant (A := ↥R₀) (G := ↥H) (H := Psub) ⟨a, ha⟩ y).1 hy
      · simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    · intro hx
      have hxH_conj : (a : G) * x * (a : G)⁻¹ ∈ H := hPsubg_le_H hx
      have hxH : x ∈ H := (Subgroup.mem_normalizer_iff.mp (hR₀normH ha) x).2 hxH_conj
      let xH : H := ⟨x, hxH⟩
      have hxPsub_smul : (⟨a, ha⟩ : R₀) • xH ∈ Psub := by
        have hsmul_mem :
            ((((⟨a, ha⟩ : R₀) • xH : H) : G)) ∈ Psubg := by
          simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hR₀normH] using hx
        rcases Subgroup.mem_map.mp hsmul_mem with ⟨y, hy, hy_eq⟩
        have hyx : y = (⟨a, ha⟩ : R₀) • xH := by
          apply H.subtype_injective
          simpa using hy_eq
        simpa [hyx] using hy
      have hxPsub : xH ∈ Psub :=
        (IsInvariant.invariant (A := ↥R₀) (G := ↥H) (H := Psub) ⟨a, ha⟩ xH).2 hxPsub_smul
      exact Subgroup.mem_map_of_mem H.subtype hxPsub
  have : Subgroup.Normalizes R₀ Psubg := ⟨hR₀normPsubg⟩
  have hR₀_dvd_R : Nat.card R₀ ∣ Nat.card R := by
    rw [← natCard_subgroupOf_eq R₀ R hR₀_le]
    exact Subgroup.card_subgroup_dvd_card (R₀.subgroupOf R)
  have hR₀_coprime_H : Nat.Coprime (Nat.card R₀) (Nat.card H) := by
    exact Nat.Coprime.of_dvd_left hR₀_dvd_R hcopHR.symm
  have hPsubg_dvd_H : Nat.card Psubg ∣ Nat.card H := by
    exact Subgroup.card_dvd_of_le hPsubg_le_H
  have hR₀_coprime_Psubg : Nat.Coprime (Nat.card R₀) (Nat.card Psubg) := by
    exact Nat.Coprime.of_dvd_right hPsubg_dvd_H hR₀_coprime_H
  have hfixed_eq :
      fixedPointSubgroup (↥R₀) (↥Psubg) = (subgroupCentralizerIn Psubg R₀).subgroupOf Psubg := by
    simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Psubg R₀ hR₀normPsubg
  have hfix_bot : fixedPointSubgroup (↥R₀) (↥Psubg) = ⊥ := by
    rw [hfixed_eq]
    simpa using congrArg (fun S : Subgroup G => S.subgroupOf Psubg) hCP_bot
  have hsolvPsubg : Group.IsSolvable ↥Psubg := by infer_instance
  have hsup :
      fixedPointSubgroup (↥R₀) (↥Psubg) ⊔ commutatorAction (A := ↥R₀) (G := ↥Psubg) = ⊤ := by
    exact proposition_1_6_a (G := ↥Psubg) (A := ↥R₀) hsolvPsubg hR₀_coprime_Psubg
  have hcomm_top : commutatorAction (A := ↥R₀) (G := ↥Psubg) = ⊤ := by
    rw [hfix_bot, bot_sup_eq] at hsup
    exact hsup
  have hcomm_map :
      (commutatorAction (A := ↥R₀) (G := ↥Psubg)).map Psubg.subtype = ⁅Psubg, R₀⁆ := by
    simpa using commutatorAction_subgroup_conj_map_eq_commutator Psubg R₀ hR₀normPsubg
  have htop_map : (⊤ : Subgroup Psubg).map Psubg.subtype = Psubg := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  have hPsubg_eq_commR₀ : Psubg = ⁅Psubg, R₀⁆ := by
    calc
      Psubg = (⊤ : Subgroup Psubg).map Psubg.subtype := htop_map.symm
      _ = (commutatorAction (A := ↥R₀) (G := ↥Psubg)).map Psubg.subtype := by rw [hcomm_top]
      _ = ⁅Psubg, R₀⁆ := hcomm_map
  have hPsubg_le_commR : Psubg ≤ ⁅Psubg, R⁆ := by
    calc
      Psubg = ⁅Psubg, R₀⁆ := hPsubg_eq_commR₀
      _ ≤ ⁅Psubg, R⁆ := Subgroup.commutator_mono le_rfl hR₀_le
  exact ⟨hPsubg_eq_commR₀, hPsubg_le_commR⟩

public theorem CFSG.pSubgroup_le_pCore_of_hasPLengthOne_of_pPrimeCore_eq_bot
    {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (A : Subgroup Q) (hA_p : IsPGroup p A)
    (hplenQ : HasPLengthOne p Q) (hcore_bot : pPrimeCore p Q = ⊥) :
    A ≤ pCore p Q := by
  let q : Q →* (Q ⧸ pCore p Q) := QuotientGroup.mk' (pCore p Q)
  let Abar : Subgroup (Q ⧸ pCore p Q) := A.map q
  have hAbar_p : IsPGroup p Abar := by
    simpa [Abar] using hA_p.map q
  have hOp_eq : Op_p'p p Q = pCore p Q :=
    Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := Q) (p := p) hcore_bot
  have hplenQ' : Op_p'pp' p Q = ⊤ := by
    simpa [HasPLengthOne] using hplenQ
  have hcore_top_op : pPrimeCore p (Q ⧸ Op_p'p p Q) = ⊤ := by
    have htmp :
        (pPrimeCore p (Q ⧸ Op_p'p p Q)).comap
          (QuotientGroup.mk' (Op_p'p p Q)) = ⊤ := by
      simpa [Op_p'pp'] using hplenQ'
    apply (Subgroup.comap_injective
      (QuotientGroup.mk'_surjective (Op_p'p p Q)))
    simpa using htmp
  let eQ : (Q ⧸ Op_p'p p Q) ≃* (Q ⧸ pCore p Q) := QuotientGroup.quotientMulEquivOfEq hOp_eq
  have hcore_top_quot : pPrimeCore p (Q ⧸ pCore p Q) = ⊤ := by
    have hmap_q :
        (pPrimeCore p (Q ⧸ Op_p'p p Q)).map eQ.toMonoidHom =
          pPrimeCore p (Q ⧸ pCore p Q) := by
      simpa [eQ] using
        (pPrimeCore_map_iso (G := (Q ⧸ Op_p'p p Q))
          (G' := (Q ⧸ pCore p Q)) (p := p) eQ)
    simpa [hcore_top_op] using hmap_q.symm
  have hcop_quot : Nat.Coprime p (Nat.card (Q ⧸ pCore p Q)) := by
    simpa [hcore_top_quot] using
      (pPrimeCore_coprime_card (G := (Q ⧸ pCore p Q)) (p := p))
  have hp_not_dvd_Abar : ¬ p ∣ Nat.card Abar := by
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1
      (Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card Abar) hcop_quot)
  have hAbar_card_one : Nat.card Abar = 1 :=
    (hAbar_p.card_eq_or_dvd).resolve_right hp_not_dvd_Abar
  have hAbar_bot : Abar = ⊥ := (Subgroup.card_eq_one (H := Abar)).1 hAbar_card_one
  have hA_le_ker : A ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (f := q) (H := A)).1 (by simpa [Abar] using hAbar_bot)
  simpa [q] using hA_le_ker

public theorem CFSG.theorem_3_6_pPrimeCore_eq_bot_of_fitting_le
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (S : Subgroup H) (hV_le_S : fittingSubgroup H ≤ S) :
    pPrimeCore p ↥S = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let V : Subgroup H := fittingSubgroup H
  have hV_elem : IsElementaryAbelian p ↥V := by
    simpa [V] using
      theorem_3_6_fitting_elementaryAbelian H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  have hVp : IsPGroup p ↥V := IsElementaryAbelian.isPGroup p ↥V
  have hcentV_eq : Subgroup.centralizer (V : Set H) = V := by
    simpa [V] using
      theorem_3_6_centralizer_fitting_eq_fitting H R R₀ p hind hsolvG hodd hHR
        hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  let N : Subgroup H := (pPrimeCore p ↥S).map S.subtype
  have hVsub_p : IsPGroup p ↥(V.subgroupOf S) := by
    exact hVp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (G := ↥H) (H := V) (K := S) hV_le_S).symm
  have hN_le_centV : N ≤ Subgroup.centralizer (V : Set H) := by
    let Nsub : Subgroup S := pPrimeCore p ↥S
    let Vsub : Subgroup S := V.subgroupOf S
    have hNsub_normal : Nsub.Normal := by
      dsimp [Nsub]
      infer_instance
    have hVsub_normal : Vsub.Normal := by
      dsimp [Vsub]
      exact Subgroup.Normal.subgroupOf (G := ↥H) (hH := inferInstance) S
    have hNsub_coprime : Nat.Coprime p (Nat.card Nsub) := by
      dsimp [Nsub]
      exact pPrimeCore_coprime_card (p := p) (G := ↥S)
    obtain ⟨m, hVsub_card⟩ := hVsub_p.exists_card_eq
    have hcop_Nsub_Vsub : Nat.Coprime (Nat.card Nsub) (Nat.card Vsub) := by
      rw [hVsub_card]
      exact hNsub_coprime.symm.pow_right m
    have hNsubVsub_disj : Disjoint Nsub Vsub := by
      exact Subgroup.disjoint_of_coprime_natCard hcop_Nsub_Vsub
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_map.mp hx with ⟨x', hx', rfl⟩
    have hysub : (⟨y, hV_le_S hy⟩ : S) ∈ Vsub := by
      simpa [Vsub, Subgroup.mem_subgroupOf] using hy
    have hcommS : (x' : S) * ⟨y, hV_le_S hy⟩ = ⟨y, hV_le_S hy⟩ * x' := by
      exact (Subgroup.commute_of_normal_of_disjoint Nsub Vsub hNsub_normal hVsub_normal
        hNsubVsub_disj _ _ hx' hysub).eq
    simpa using congrArg Subtype.val hcommS.symm
  have hN_le_V : N ≤ V := by
    simpa [hcentV_eq] using hN_le_centV
  have hN_card :
      Nat.card N = Nat.card (pPrimeCore p ↥S) := by
    simpa [N] using
      (Subgroup.card_map_of_injective (K := pPrimeCore p ↥S) (f := S.subtype)
        (hf := S.subtype_injective))
  have hcop_p_N : Nat.Coprime p (Nat.card N) := by
    rw [hN_card]
    exact pPrimeCore_coprime_card (p := p) (G := ↥S)
  obtain ⟨n, hV_card⟩ := hVp.exists_card_eq
  have hcop_V_N : Nat.Coprime (Nat.card V) (Nat.card N) := by
    rw [hV_card]
    exact hcop_p_N.pow_left n
  have hVN_bot : V ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop_V_N).eq_bot
  have hN_bot : N = ⊥ := by
    apply bot_unique
    intro x hx
    have hxV : x ∈ V := hN_le_V hx
    have hxVN : x ∈ V ⊓ N := ⟨hxV, hx⟩
    simpa [hVN_bot] using hxVN
  exact
    (Subgroup.map_eq_bot_iff_of_injective (H := pPrimeCore p ↥S) (f := S.subtype)
      S.subtype_injective).1 (by simpa [N] using hN_bot)

public theorem CFSG.theorem_3_6_local_subambient_step
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) (X : Subgroup H) :
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    IsInvariant (↥R) (↥H) X →
    normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
    let N : Subgroup H := fittingSubgroup H ⊔ X ⊔ normalizerSubtypeMap K P
    let Ng : Subgroup G := N.map H.subtype
    Ng ⊔ R₀ < ⊤ →
    HasPLengthOne p ↥⁅Ng, R₀⁆ := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hP_inv hX_inv hPsub_normX hS_lt
  let V : Subgroup H := fittingSubgroup H
  let Psub : Subgroup H := normalizerSubtypeMap K P
  let Y : Subgroup H := X ⊔ Psub
  let N : Subgroup H := V ⊔ X ⊔ Psub
  let Ng : Subgroup G := N.map H.subtype
  let S : Subgroup G := Ng ⊔ R₀
  let hR₀normH : R₀ ≤ Subgroup.normalizer H := hR₀_le.trans hRnormH
  have : Subgroup.Normalizes R₀ H := ⟨hR₀normH⟩
  have hP_inv₀ : IsInvariant (↥R₀) (↥H) Psub := by
    refine ⟨?_⟩
    intro a x
    have hx := IsInvariant.invariant (A := ↥R) (G := ↥H) (H := Psub)
      ⟨(a : G), hR₀_le a.2⟩ x
    change (x ∈ Psub) ↔ (a • x ∈ Psub) at hx
    exact hx
  have hX_inv₀ : IsInvariant (↥R₀) (↥H) X := by
    refine ⟨?_⟩
    intro a x
    have hx := IsInvariant.invariant (A := ↥R) (G := ↥H) (H := X)
      ⟨(a : G), hR₀_le a.2⟩ x
    change (x ∈ X) ↔ (a • x ∈ X) at hx
    exact hx
  have hV_char : V.Characteristic := by
    dsimp [V]
    infer_instance
  let : V.Characteristic := hV_char
  have hV_inv₀ : IsInvariant (↥R₀) (↥H) V :=
    isInvariant_of_characteristic (A := ↥R₀) (G := ↥H) V
  have hY_inv₀ : IsInvariant (↥R₀) (↥H) Y := by
    let : IsInvariant (↥R₀) (↥H) X := hX_inv₀
    let : IsInvariant (↥R₀) (↥H) Psub := hP_inv₀
    simpa [Y] using isInvariant_sup_of_le_normalizer X Psub hPsub_normX
  have hY_le_normV : Y ≤ Subgroup.normalizer (V : Set H) :=
    Subgroup.le_normalizer_of_normal (H := V)
  have hN_inv₀ : IsInvariant (↥R₀) (↥H) N := by
    let : IsInvariant (↥R₀) (↥H) V := hV_inv₀
    let : IsInvariant (↥R₀) (↥H) Y := hY_inv₀
    simpa [N, Y, sup_assoc] using isInvariant_sup_of_le_normalizer V Y hY_le_normV
  have hNg_le_H : Ng ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  have hR₀invNg : ∀ r : R₀, ∀ x ∈ Ng, (r : G) * x * (r : G)⁻¹ ∈ Ng := by
    intro r x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨r • y, (IsInvariant.invariant (A := ↥R₀) (G := ↥H) (H := N) r y).1 hy, ?_⟩
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  have hR₀_le_normNg : R₀ ≤ Subgroup.normalizer (Ng : Set G) :=
    subgroup_le_normalizer_of_conj_mem Ng R₀ hR₀invNg
  have hS_le_normNg : S ≤ Subgroup.normalizer (Ng : Set G) := sup_le Ng.le_normalizer hR₀_le_normNg
  have hNgsub_normal : (Ng.subgroupOf S).Normal := by
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := S) (N := Ng) hS_le_normNg
  have hcardS_dvd : Nat.card S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S
  have hcardS_lt : Nat.card S < Nat.card G := by
    simpa [S, Ng, N, V, Psub, sup_assoc] using natCard_lt_of_subgroup_lt hS_lt
  have hdisj : Disjoint Ng R₀ := (hHR.disjoint.mono_left hNg_le_H).mono_right hR₀_le
  have hNg_dvd_H : Nat.card Ng ∣ Nat.card H := Subgroup.card_dvd_of_le hNg_le_H
  have hR₀_dvd_R : Nat.card R₀ ∣ Nat.card R := by
    rw [← natCard_subgroupOf_eq R₀ R hR₀_le]
    exact Subgroup.card_subgroup_dvd_card (R₀.subgroupOf R)
  have hcopNgR₀ : Nat.Coprime (Nat.card Ng) (Nat.card R₀) := by
    exact Nat.Coprime.of_dvd hNg_dvd_H hR₀_dvd_R hcopHR
  have hcop_sub :
      Nat.Coprime (Nat.card (Ng.subgroupOf S)) (Nat.card (R₀.subgroupOf S)) := by
    simpa [natCard_subgroupOf_eq Ng S le_sup_left, natCard_subgroupOf_eq R₀ S le_sup_right] using
      hcopNgR₀
  have hR₀sub_prime : Nat.Prime (Nat.card (R₀.subgroupOf S)) := by
    rw [natCard_subgroupOf_eq R₀ S le_sup_right]
    exact hR₀_prime
  have hCZ_Ng : IsZGroup ↥(subgroupCentralizerIn Ng R₀) :=
    isZGroup_subgroupCentralizerIn_of_le H Ng R₀ hNg_le_H
  have hCZ_sub : IsZGroup ↥(subgroupCentralizerIn (Ng.subgroupOf S) (R₀.subgroupOf S)) := by
    let : IsZGroup ↥(subgroupCentralizerIn Ng R₀) := hCZ_Ng
    exact isZGroup_subgroupCentralizerIn_subgroupOf S Ng R₀ le_sup_right
  have hsub : HasPLengthOne p ↥⁅Ng.subgroupOf S, R₀.subgroupOf S⁆ := by
    let : (Ng.subgroupOf S).Normal := hNgsub_normal
    have hcomp_sub :
        (Ng.subgroupOf S).IsComplement' (R₀.subgroupOf S) := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
        ?_ ?_
      · rw [Subgroup.disjoint_def]
        intro x hxNg hxR₀
        apply Subtype.ext
        exact (Subgroup.disjoint_def.mp hdisj)
          (by simpa [Subgroup.mem_subgroupOf] using hxNg)
          (by simpa [Subgroup.mem_subgroupOf] using hxR₀)
      ext x
      constructor
      · intro _; trivial
      · intro _
        have hxsup : x ∈ Ng.subgroupOf S ⊔ R₀.subgroupOf S := by
          have hsub_sup : Ng.subgroupOf S ⊔ R₀.subgroupOf S = ⊤ := by
            calc
              Ng.subgroupOf S ⊔ R₀.subgroupOf S = (Ng ⊔ R₀).subgroupOf S := by
                symm
                exact Subgroup.subgroupOf_sup (A := Ng) (A' := R₀) (B := S) le_sup_left le_sup_right
              _ = ⊤ := by simp [S]
          simp [hsub_sup]
        rcases (Subgroup.mem_sup_of_normal_left
          (s := Ng.subgroupOf S) (t := R₀.subgroupOf S) (x := x)).1 hxsup with
          ⟨n, hn, r, hr, rfl⟩
        exact Set.mem_mul.mpr ⟨n, hn, r, hr, rfl⟩
    exact
      hind (Ng.subgroupOf S) (R₀.subgroupOf S) (R₀.subgroupOf S) p hcardS_lt
        (by infer_instance)
        (odd_of_card_dvd hodd hcardS_dvd)
        hNgsub_normal
        hcomp_sub
        hcop_sub
        le_rfl
        hR₀sub_prime
        hp
        hCZ_sub
  simpa [Ng, N, V, Psub, sup_assoc] using
    hasPLengthOne_commutator_subgroupOf_map (p := p) S Ng R₀ le_sup_left le_sup_right hsub

public theorem CFSG.theorem_3_6_commutator_bot_of_proper_subambient
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H)
    (hVK_sup :
      fittingSubgroup H ⊔ K =
        (fittingSubgroup (↥H ⧸ fittingSubgroup H)).comap
          (QuotientGroup.mk' (fittingSubgroup H)))
    (hVK_disj : Disjoint (fittingSubgroup H) K)
    (P : Subgroup (normalizerOf K)) (hP_p : IsPGroup p P) :
    IsInvariant (↥R) (↥H) K →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    fittingSubgroup H ⊔ normalizerOf K = ⊤ →
    fittingSubgroup H ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    ∀ (X : Subgroup H), X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      let N : Subgroup H := fittingSubgroup H ⊔ X ⊔ normalizerSubtypeMap K P
      let Ng : Subgroup G := N.map H.subtype
      Ng ⊔ R₀ < ⊤ →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hK_inv hNK_inv hP_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K X hX_le_K hX_inv
    hPsub_normX hS_lt
  let V : Subgroup H := fittingSubgroup H
  let Psub : Subgroup H := normalizerSubtypeMap K P
  let Xg : Subgroup G := X.map H.subtype
  let Psubg : Subgroup G := Psub.map H.subtype
  let N : Subgroup H := V ⊔ X ⊔ Psub
  let Ng : Subgroup G := N.map H.subtype
  have hV_le_N : V ≤ N := by
    dsimp [N]
    exact le_trans le_sup_left le_sup_left
  have hX_le_N : X ≤ N := by
    dsimp [N]
    exact le_trans le_sup_right le_sup_left
  have hPsub_le_N : Psub ≤ N := by
    dsimp [N]
    exact le_sup_right
  have hXg_le_Ng : Xg ≤ Ng := by
    dsimp [Xg, Ng]
    exact Subgroup.map_mono hX_le_N
  have hPsubg_le_Ng : Psubg ≤ Ng := by
    dsimp [Psubg, Ng]
    exact Subgroup.map_mono hPsub_le_N
  have hplenQ : HasPLengthOne p ↥⁅Ng, R₀⁆ := by
    simpa [N, Ng, V, Psub, sup_assoc] using
      theorem_3_6_local_subambient_step H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ K P X hP_inv hX_inv hPsub_normX hS_lt
  have hN_core_bot : pPrimeCore p ↥N = ⊥ :=
    theorem_3_6_pPrimeCore_eq_bot_of_fitting_le H R R₀ p hind hsolvG hodd hHR
      hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad N hV_le_N
  let eNg : ↥N ≃* ↥Ng := Subgroup.equivMapOfInjective (f := H.subtype) N H.subtype_injective
  have hNg_core_bot : pPrimeCore p ↥Ng = ⊥ := by
    have hmap :
        (pPrimeCore p ↥N).map eNg.toMonoidHom = pPrimeCore p ↥Ng :=
      pPrimeCore_map_iso (G := ↥N) (G' := ↥Ng) (p := p) eNg
    simpa [hN_core_bot] using hmap.symm
  let hR₀normH : R₀ ≤ Subgroup.normalizer H := hR₀_le.trans hRnormH
  have : Subgroup.Normalizes R₀ H := ⟨hR₀normH⟩
  have hP_inv₀ : IsInvariant (↥R₀) (↥H) Psub := by
    refine ⟨?_⟩
    intro a x
    have hx := IsInvariant.invariant (A := ↥R) (G := ↥H) (H := Psub)
      ⟨(a : G), hR₀_le a.2⟩ x
    change (x ∈ Psub) ↔ (a • x ∈ Psub) at hx
    exact hx
  have hX_inv₀ : IsInvariant (↥R₀) (↥H) X := by
    refine ⟨?_⟩
    intro a x
    have hx := IsInvariant.invariant (A := ↥R) (G := ↥H) (H := X)
      ⟨(a : G), hR₀_le a.2⟩ x
    change (x ∈ X) ↔ (a • x ∈ X) at hx
    exact hx
  have hV_char : V.Characteristic := by
    dsimp [V]
    infer_instance
  let : V.Characteristic := hV_char
  have hV_inv₀ : IsInvariant (↥R₀) (↥H) V :=
    isInvariant_of_characteristic (A := ↥R₀) (G := ↥H) V
  let Y : Subgroup H := X ⊔ Psub
  have hY_inv₀ : IsInvariant (↥R₀) (↥H) Y := by
    let : IsInvariant (↥R₀) (↥H) X := hX_inv₀
    let : IsInvariant (↥R₀) (↥H) Psub := hP_inv₀
    simpa [Y] using isInvariant_sup_of_le_normalizer X Psub hPsub_normX
  have hY_le_normV : Y ≤ Subgroup.normalizer (V : Set H) :=
    Subgroup.le_normalizer_of_normal (H := V)
  have hN_inv₀ : IsInvariant (↥R₀) (↥H) N := by
    let : IsInvariant (↥R₀) (↥H) V := hV_inv₀
    let : IsInvariant (↥R₀) (↥H) Y := hY_inv₀
    simpa [N, Y, sup_assoc] using isInvariant_sup_of_le_normalizer V Y hY_le_normV
  have hR₀invNg : ∀ r : R₀, ∀ x ∈ Ng, (r : G) * x * (r : G)⁻¹ ∈ Ng := by
    intro r x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨r • y, (IsInvariant.invariant (A := ↥R₀) (G := ↥H) (H := N) r y).1 hy, ?_⟩
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  have hR₀_le_normNg : R₀ ≤ Subgroup.normalizer (Ng : Set G) :=
    subgroup_le_normalizer_of_conj_mem Ng R₀ hR₀invNg
  have hcommNg_le : ⁅Ng, R₀⁆ ≤ Ng := by
    refine (Subgroup.commutator_le (H₁ := Ng) (H₂ := R₀) (H₃ := Ng)).2 ?_
    intro a ha b hb
    have hbNorm : (b : G) ∈ Subgroup.normalizer (Ng : Set G) := hR₀_le_normNg hb
    have hconj : (b : G) * a⁻¹ * (b : G)⁻¹ ∈ Ng :=
      ((Subgroup.mem_normalizer_iff.mp hbNorm) a⁻¹).1 (Ng.inv_mem ha)
    simpa [commutatorElement_def, mul_assoc] using Ng.mul_mem ha hconj
  have : Subgroup.Normalizes R₀ Ng := ⟨hR₀_le_normNg⟩
  have hQ_eq :
      (commutatorAction (A := ↥R₀) (G := ↥Ng)).map Ng.subtype = ⁅Ng, R₀⁆ := by
    simpa using commutatorAction_subgroup_conj_map_eq_commutator Ng R₀ hR₀_le_normNg
  let Qsub : Subgroup Ng := (⁅Ng, R₀⁆).subgroupOf Ng
  have hQsub_map :
      Qsub.map Ng.subtype = ⁅Ng, R₀⁆ := by
    simpa [Qsub] using
      (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := ⁅Ng, R₀⁆) (K := Ng)
        hcommNg_le)
  let eQ :
      ↥Qsub ≃* ↥⁅Ng, R₀⁆ :=
    (Subgroup.equivMapOfInjective (f := Ng.subtype) Qsub Ng.subtype_injective).trans
      (MulEquiv.subgroupCongr hQsub_map)
  have hplenQsub : HasPLengthOne p ↥Qsub :=
    hasPLengthOne_of_equiv (p := p) eQ.symm hplenQ
  have hQsub_eq_comm :
      Qsub = commutatorAction (A := ↥R₀) (G := ↥Ng) := by
    apply (Subgroup.map_injective (f := Ng.subtype) Ng.subtype_injective)
    rw [hQsub_map, hQ_eq]
  have hQsub_normal : Qsub.Normal := by
    rw [hQsub_eq_comm]
    exact commutatorAction_normal (G := ↥Ng) (A := ↥R₀)
  have hQsub_core_bot : pPrimeCore p ↥Qsub = ⊥ := by
    have hmap_le :
        (pPrimeCore p ↥Qsub).map Qsub.subtype ≤ pPrimeCore p ↥Ng :=
      pPrimeCore_map_subtype_le_pPrimeCore_of_normal (p := p) Qsub
    have hmap_bot : (pPrimeCore p ↥Qsub).map Qsub.subtype = ⊥ := by
      exact le_antisymm (hmap_le.trans (by simp [hNg_core_bot])) bot_le
    exact
      (Subgroup.map_eq_bot_iff_of_injective (H := pPrimeCore p ↥Qsub) (f := Qsub.subtype)
        Qsub.subtype_injective).1 hmap_bot
  have hcop_p_K : Nat.Coprime p (Nat.card K) :=
    theorem_3_6_complement_card_coprime H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_disj hVK_sup
  obtain ⟨hPsubg_eq_commR₀, _hPsubg_le_commR⟩ :=
    theorem_3_6_pSubgroup_eq_commutator_with_R₀ H R R₀ p hind hsolvG hodd hHR
      hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup P hP_p hK_inv hNK_inv hP_inv
      hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
  let Psubgsub : Subgroup Ng := Psubg.subgroupOf Ng
  have hPsub_p : IsPGroup p Psub := by
    change IsPGroup p (normalizerSubtypeMap K P)
    exact isPGroup_normalizerSubtypeMap K P hP_p
  have hPsubg_p : IsPGroup p Psubg := by
    simpa [Psubg] using hPsub_p.map H.subtype
  have hPsubgsub_p : IsPGroup p Psubgsub := by
    exact hPsubg_p.of_equiv
      (Subgroup.subgroupOfEquivOfLe (G := G) (H := Psubg) (K := Ng) hPsubg_le_Ng).symm
  have hPsubg_le_commQ : Psubg ≤ ⁅Ng, R₀⁆ := by
    calc
      Psubg = ⁅Psubg, R₀⁆ := by simpa [Psubg] using hPsubg_eq_commR₀
      _ ≤ ⁅Ng, R₀⁆ := Subgroup.commutator_mono hPsubg_le_Ng le_rfl
  have hPsubgsub_le_Qsub : Psubgsub ≤ Qsub := by
    intro x hx
    exact hPsubg_le_commQ (by simpa [Psubgsub, Subgroup.mem_subgroupOf] using hx)
  have hPsubgsubQsub_p : IsPGroup p (Psubgsub.subgroupOf Qsub) := by
    exact hPsubgsub_p.of_equiv
      (Subgroup.subgroupOfEquivOfLe (G := ↥Ng) (H := Psubgsub) (K := Qsub) hPsubgsub_le_Qsub).symm
  have hPsubgsubQsub_le_pCore : Psubgsub.subgroupOf Qsub ≤ pCore p ↥Qsub :=
    pSubgroup_le_pCore_of_hasPLengthOne_of_pPrimeCore_eq_bot
      (A := Psubgsub.subgroupOf Qsub) hPsubgsubQsub_p hplenQsub hQsub_core_bot
  let OQ : Subgroup Qsub := pCore p ↥Qsub
  let OQg : Subgroup Ng := OQ.map Qsub.subtype
  have hOQg_p : IsPGroup p OQg := by
    dsimp [OQg, OQ]
    exact (pCore_isPGroup (G := ↥Qsub) (p := p)).map Qsub.subtype
  have hOQg_normal : OQg.Normal := by
    let : (pCore p ↥Qsub).Characteristic := pCore_characteristic (p := p)
    dsimp [OQg, OQ]
    infer_instance
  let Xgsub : Subgroup Ng := Xg.subgroupOf Ng
  have hXgsub_le_normOQg : Xgsub ≤ Subgroup.normalizer (OQg : Set Ng) := by
    let : OQg.Normal := hOQg_normal
    simpa using (Subgroup.le_normalizer_of_normal (K := Xgsub) (H := OQg))
  have hPsubgsub_le_OQg : Psubgsub ≤ OQg := by
    intro x hx
    let xQ : Qsub := ⟨x, hPsubgsub_le_Qsub hx⟩
    have hxQ : xQ ∈ Psubgsub.subgroupOf Qsub := by
      simpa [Psubgsub, xQ, Subgroup.mem_subgroupOf] using hx
    have hxCore : xQ ∈ pCore p ↥Qsub := hPsubgsubQsub_le_pCore hxQ
    exact Subgroup.mem_map_of_mem Qsub.subtype hxCore
  have hcommsub_le_OQg : ⁅Xgsub, Psubgsub⁆ ≤ OQg := by
    refine (Subgroup.commutator_le (H₁ := Xgsub) (H₂ := Psubgsub) (H₃ := OQg)).2 ?_
    intro a ha b hb
    have haNorm : (a : Ng) ∈ Subgroup.normalizer (OQg : Set Ng) := hXgsub_le_normOQg ha
    have hconj :
        (a : Ng) * b * (a : Ng)⁻¹ ∈ OQg :=
      ((Subgroup.mem_normalizer_iff.mp haNorm) b).1 (hPsubgsub_le_OQg hb)
    simpa [commutatorElement_def, mul_assoc] using OQg.mul_mem hconj (OQg.inv_mem (hPsubgsub_le_OQg hb))
  have hcommg_le :
      ⁅Xg, Psubg⁆ ≤ OQg.map Ng.subtype := by
    have hmap_eq :
        (⁅Xgsub, Psubgsub⁆).map Ng.subtype = ⁅Xg, Psubg⁆ := by
      simpa [Xgsub, Psubgsub] using
        commutator_subgroupOf_map_eq (S := Ng) (H := Psubg) (R := Xg) hPsubg_le_Ng hXg_le_Ng
    rw [← hmap_eq]
    exact Subgroup.map_mono hcommsub_le_OQg
  have hcommXP_map_le :
      (⁅X, Psub⁆).map H.subtype ≤ OQg.map Ng.subtype := by
    calc
      (⁅X, Psub⁆).map H.subtype = ⁅Xg, Psubg⁆ := by
        simpa [Xg, Psubg] using (Subgroup.map_commutator (H₁ := X) (H₂ := Psub) H.subtype)
      _ ≤ OQg.map Ng.subtype := hcommg_le
  have hOQg_map_p : IsPGroup p (OQg.map Ng.subtype) := hOQg_p.map Ng.subtype
  let C : Subgroup H := ⁅X, Psub⁆
  have hcommXP_map_p : IsPGroup p (C.map H.subtype) := by
    exact IsPGroup.to_le (hK := hOQg_map_p) hcommXP_map_le
  let eC : ↥C ≃* ↥(C.map H.subtype) :=
    Subgroup.equivMapOfInjective (f := H.subtype) C H.subtype_injective
  have hcommXP_p : IsPGroup p C := by
    exact hcommXP_map_p.of_equiv
      eC.symm
  have hcommXP_dvd_K : Nat.card C ∣ Nat.card K := by
    have hC_le_X : C ≤ X := by
      refine (Subgroup.commutator_le (H₁ := X) (H₂ := Psub) (H₃ := X)).2 ?_
      intro a ha b hb
      have hbNorm : (b : H) ∈ Subgroup.normalizer (X : Set H) := hPsub_normX hb
      have hconj : (b : H) * a⁻¹ * (b : H)⁻¹ ∈ X :=
        ((Subgroup.mem_normalizer_iff.mp hbNorm) a⁻¹).1 (X.inv_mem ha)
      simpa [commutatorElement_def, mul_assoc] using X.mul_mem ha hconj
    exact (Subgroup.card_dvd_of_le hC_le_X).trans
      (Subgroup.card_dvd_of_le hX_le_K)
  have hcop_p_commXP : Nat.Coprime p (Nat.card C) :=
    Nat.Coprime.of_dvd_right hcommXP_dvd_K hcop_p_K
  have hp_not_dvd_commXP : ¬ p ∣ Nat.card C :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 hcop_p_commXP
  have hcard_commXP : Nat.card C = 1 :=
    (hcommXP_p.card_eq_or_dvd).resolve_right hp_not_dvd_commXP
  have hcommXP_bot : C = ⊥ := (Subgroup.card_eq_one (H := C)).1 hcard_commXP
  simpa [Psub, C] using hcommXP_bot

public theorem CFSG.theorem_3_6_H_eq_VKP_R_eq_R₀
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    ∃ K : Subgroup H, ∃ P : Subgroup (normalizerOf K),
      V ⊔ K = Fbar.comap q ∧
      Disjoint V K ∧
      IsInvariant (↥R) (↥H) K ∧
      IsInvariant (↥R) (↥H) (normalizerOf K) ∧
      IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) ∧
      V ⊔ normalizerOf K = ⊤ ∧
      V ⊓ normalizerOf K = ⊥ ∧
      (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) ∧
      subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K ∧
      IsPGroup p P ∧
      ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ ∧
      V ⊔ K ⊔ normalizerSubtypeMap K P = ⊤ ∧
      R = R₀ ∧
      ∀ X : Subgroup H, X ≤ K →
        IsInvariant (↥R) (↥H) X →
        normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
        X < K →
        ⁅X, normalizerSubtypeMap K P⁆ = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  let V : Subgroup H := fittingSubgroup H
  let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
  let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
  obtain ⟨K, _hK_le_U, hVK_sup, hVK_disj, hK_inv, hNK_inv, hVNK_sup, _hVK_comm, _hCVK_bot,
    hVinfNK_bot, hKsub_fit, hCH_le_K⟩ :=
    theorem_3_6_normalizer_complement_structure H R R₀ p hind hsolvG hodd hHR
      hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  obtain ⟨P, hP_p, _hP_not_dvd, hP_inv, hPK_ne_bot⟩ :=
    theorem_3_6_exists_normalizer_invariant_pSubgroup_with_nontrivial_commutator H R R₀ p hind
      hsolvG hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup
      hNK_inv hVNK_sup
  let Psub : Subgroup H := normalizerSubtypeMap K P
  have hPsub_inv : IsInvariant (↥R) (↥H) Psub := by
    let : IsInvariant (↥R) (↥H) (normalizerOf K) := hNK_inv
    let : IsInvariant (↥R) (↥(normalizerOf K)) P := hP_inv
    simpa [Psub, normalizerSubtypeMap] using
      isInvariant_map_subtype (A := ↥R) (G := ↥H) (normalizerOf K) P
  have hV_char : V.Characteristic := by
    dsimp [V]
    infer_instance
  let : V.Characteristic := hV_char
  have htop_map_H : (⊤ : Subgroup H).map H.subtype = H := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  have hPsub_le_NK : Psub ≤ normalizerOf K := by
    simpa [Psub, normalizerSubtypeMap] using (Subgroup.map_subtype_le P)
  have hPsub_normK : Psub ≤ Subgroup.normalizer (K : Set H) := by
    simpa [normalizerOf] using hPsub_le_NK
  have hN_top_of_ambient_top :
      ∀ (X : Subgroup H),
        IsInvariant (↥R) (↥H) X →
        Psub ≤ Subgroup.normalizer (X : Set H) →
        let N : Subgroup H := V ⊔ X ⊔ Psub
        let Ng : Subgroup G := N.map H.subtype
        Ng ⊔ R₀ = ⊤ →
        N = ⊤ := by
    intro X hX_inv hPsub_normX
    dsimp
    intro hNgR₀_top
    let N : Subgroup H := V ⊔ X ⊔ Psub
    let Ng : Subgroup G := N.map H.subtype
    let S : Subgroup G := Ng ⊔ R₀
    have hNg_le_H : Ng ≤ H := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.2
    let hR₀normH : R₀ ≤ Subgroup.normalizer H := hR₀_le.trans hRnormH
    have : Subgroup.Normalizes R₀ H := ⟨hR₀normH⟩
    have hPsub_inv₀ : IsInvariant (↥R₀) (↥H) Psub := by
      refine ⟨?_⟩
      intro a x
      have hx := IsInvariant.invariant (A := ↥R) (G := ↥H) (H := Psub)
        ⟨(a : G), hR₀_le a.2⟩ x
      change (x ∈ Psub) ↔ (a • x ∈ Psub) at hx
      exact hx
    have hX_inv₀ : IsInvariant (↥R₀) (↥H) X := by
      refine ⟨?_⟩
      intro a x
      have hx := IsInvariant.invariant (A := ↥R) (G := ↥H) (H := X)
        ⟨(a : G), hR₀_le a.2⟩ x
      change (x ∈ X) ↔ (a • x ∈ X) at hx
      exact hx
    have hV_inv₀ : IsInvariant (↥R₀) (↥H) V :=
      isInvariant_of_characteristic (A := ↥R₀) (G := ↥H) V
    let Y : Subgroup H := X ⊔ Psub
    have hY_inv₀ : IsInvariant (↥R₀) (↥H) Y := by
      let : IsInvariant (↥R₀) (↥H) X := hX_inv₀
      let : IsInvariant (↥R₀) (↥H) Psub := hPsub_inv₀
      simpa [Y] using isInvariant_sup_of_le_normalizer X Psub hPsub_normX
    have hY_le_normV : Y ≤ Subgroup.normalizer (V : Set H) :=
      Subgroup.le_normalizer_of_normal (H := V)
    have hN_inv₀ : IsInvariant (↥R₀) (↥H) N := by
      let : IsInvariant (↥R₀) (↥H) V := hV_inv₀
      let : IsInvariant (↥R₀) (↥H) Y := hY_inv₀
      simpa [N, Y, sup_assoc] using isInvariant_sup_of_le_normalizer V Y hY_le_normV
    have hR₀invNg : ∀ r : R₀, ∀ x ∈ Ng, (r : G) * x * (r : G)⁻¹ ∈ Ng := by
      intro r x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨r • y, (IsInvariant.invariant (A := ↥R₀) (G := ↥H) (H := N) r y).1 hy, ?_⟩
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    have hR₀_le_normNg : R₀ ≤ Subgroup.normalizer (Ng : Set G) :=
      subgroup_le_normalizer_of_conj_mem Ng R₀ hR₀invNg
    have hS_le_normNg : S ≤ Subgroup.normalizer (Ng : Set G) :=
      sup_le Ng.le_normalizer hR₀_le_normNg
    have hNgsub_normal : (Ng.subgroupOf S).Normal := by
      exact Subgroup.normal_subgroupOf_of_le_normalizer (H := S) (N := Ng) hS_le_normNg
    have hH_le_Ng : H ≤ Ng := by
      let : (Ng.subgroupOf S).Normal := hNgsub_normal
      intro h hh
      have hs : h ∈ S := by
        change h ∈ Ng ⊔ R₀
        rw [hNgR₀_top]
        simp
      have hsup :
          (⟨h, hs⟩ : S) ∈ Ng.subgroupOf S ⊔ R₀.subgroupOf S := by
        have hsub_sup : Ng.subgroupOf S ⊔ R₀.subgroupOf S = ⊤ := by
          calc
            Ng.subgroupOf S ⊔ R₀.subgroupOf S = (Ng ⊔ R₀).subgroupOf S := by
              symm
              exact Subgroup.subgroupOf_sup (A := Ng) (A' := R₀) (B := S) le_sup_left le_sup_right
            _ = ⊤ := by simp [S]
        simp [hsub_sup]
      rcases (Subgroup.mem_sup_of_normal_left
        (s := Ng.subgroupOf S) (t := R₀.subgroupOf S) (x := ⟨h, hs⟩)).1 hsup with
        ⟨n, hn, r, hr, hmul⟩
      have hnNg : (n : G) ∈ Ng := by
        simpa [Subgroup.mem_subgroupOf] using hn
      have hnH : (n : G) ∈ H := hNg_le_H hnNg
      have hrR₀ : (r : G) ∈ R₀ := by
        simpa [Subgroup.mem_subgroupOf] using hr
      have hmul_val : (n : G) * (r : G) = h := by
        exact congrArg Subtype.val hmul
      have hrH : (r : G) ∈ H := by
        have hr_eq : (r : G) = (n : G)⁻¹ * h := by
          calc
            (r : G) = 1 * (r : G) := by simp
            _ = (n : G)⁻¹ * ((n : G) * (r : G)) := by simp
            _ = (n : G)⁻¹ * h := by rw [hmul_val]
        rw [hr_eq]
        exact H.mul_mem (H.inv_mem hnH) hh
      have hrbot : (r : G) ∈ (⊥ : Subgroup G) := by
        have hrinf : (r : G) ∈ H ⊓ R := ⟨hrH, hR₀_le hrR₀⟩
        simpa [hHR.disjoint.eq_bot] using hrinf
      have hr_one : (r : G) = 1 := by simpa using hrbot
      have hh_eq : h = (n : G) := by
        calc
          h = (n : G) * (r : G) := by simpa using hmul_val.symm
          _ = (n : G) := by simp [hr_one]
      exact hh_eq ▸ hnNg
    have hNg_eq_H : Ng = H := le_antisymm hNg_le_H hH_le_Ng
    apply (Subgroup.map_injective (f := H.subtype) H.subtype_injective)
    calc
      N.map H.subtype = Ng := rfl
      _ = H := hNg_eq_H
      _ = (⊤ : Subgroup H).map H.subtype := htop_map_H.symm
  have hNgK_sup_top :
      (V ⊔ K ⊔ Psub).map H.subtype ⊔ R₀ = ⊤ := by
    by_contra hnot_top
    have hlt :
        (V ⊔ K ⊔ Psub).map H.subtype ⊔ R₀ < ⊤ := by
      exact lt_of_le_of_ne le_top hnot_top
    have hcommKP_bot : ⁅K, Psub⁆ = ⊥ := by
      simpa [V, Psub, sup_assoc] using
        theorem_3_6_commutator_bot_of_proper_subambient H R R₀ p hind hsolvG hodd
          hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hVK_disj P hP_p
          hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K K le_rfl hK_inv
          hPsub_normK hlt
    exact hPK_ne_bot (by simpa [Subgroup.commutator_comm, Psub] using hcommKP_bot)
  have hVKP_top : V ⊔ K ⊔ Psub = ⊤ := by
    exact hN_top_of_ambient_top K hK_inv hPsub_normK hNgK_sup_top
  have hHsupR₀_top : H ⊔ R₀ = ⊤ := by
    calc
      H ⊔ R₀ = ((V ⊔ K ⊔ Psub).map H.subtype) ⊔ R₀ := by
        rw [hVKP_top]
        simp [htop_map_H]
      _ = ⊤ := hNgK_sup_top
  have hR_le_R₀ : R ≤ R₀ := by
    intro r hr
    have hrsup : r ∈ H ⊔ R₀ := by
      rw [hHsupR₀_top]
      simp
    rcases (Subgroup.mem_sup_of_normal_left (s := H) (t := R₀) (x := r)).1 hrsup with
      ⟨h, hhH, r₀, hr₀, hmul⟩
    have hhR : h ∈ R := by
      have hh_eq : h = r * r₀⁻¹ := by
        calc
          h = h * 1 := by simp
          _ = h * (r₀ * r₀⁻¹) := by simp
          _ = (h * r₀) * r₀⁻¹ := by simp [mul_assoc]
          _ = r * r₀⁻¹ := by rw [hmul]
      rw [hh_eq]
      exact R.mul_mem hr (R.inv_mem (hR₀_le hr₀))
    have hhbot : h ∈ (⊥ : Subgroup G) := by
      have hhinf : h ∈ H ⊓ R := ⟨hhH, hhR⟩
      simpa [hHR.disjoint.eq_bot] using hhinf
    have hh_one : h = 1 := by simpa using hhbot
    have hr_eq : r = r₀ := by
      calc
        r = h * r₀ := by simpa using hmul.symm
        _ = r₀ := by simp [hh_one]
    exact hr_eq ▸ hr₀
  have hR_eq_R₀ : R = R₀ := le_antisymm hR_le_R₀ hR₀_le
  have hPsub_p : IsPGroup p Psub := by
    change IsPGroup p (normalizerSubtypeMap K P)
    exact isPGroup_normalizerSubtypeMap K P hP_p
  have hcop_p_K : Nat.Coprime p (Nat.card K) :=
    theorem_3_6_complement_card_coprime H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_disj hVK_sup
  have hcop_K_Psub : Nat.Coprime (Nat.card K) (Nat.card Psub) := by
    obtain ⟨n, hcardPsub⟩ := hPsub_p.exists_card_eq
    rw [hcardPsub]
    exact hcop_p_K.symm.pow_right n
  have hKinfPsub_bot : K ⊓ Psub = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop_K_Psub).eq_bot
  have hK_le_X_of_top :
      ∀ (X : Subgroup H), X ≤ K →
        Psub ≤ Subgroup.normalizer (X : Set H) →
        V ⊔ X ⊔ Psub = ⊤ →
        K ≤ X := by
    intro X hX_le hPsub_normX htop
    let NK : Subgroup H := normalizerOf K
    have hV_disj_NK : Disjoint V NK := by
      rw [disjoint_iff]
      exact hVinfNK_bot
    have hK_le_NK : K ≤ NK := Subgroup.le_normalizer
    have hM_le_NK : X ⊔ Psub ≤ NK := sup_le (hX_le.trans hK_le_NK) hPsub_le_NK
    intro k hk
    let M : Subgroup H := X ⊔ Psub
    have hksup : k ∈ V ⊔ M := by
      have : k ∈ V ⊔ X ⊔ Psub := by simp [htop]
      simpa [M, sup_assoc] using this
    rcases (Subgroup.mem_sup_of_normal_left (s := V) (t := M) (x := k)).1 hksup with
      ⟨v, hv, m, hm, hmul⟩
    have hmNK : (m : H) ∈ NK := hM_le_NK (by simpa [M] using hm)
    have hvNK : v ∈ NK := by
      have hkNK : k ∈ NK := hK_le_NK hk
      have hv_eq : v = k * (m : H)⁻¹ := by
        calc
          v = v * 1 := by simp
          _ = v * ((m : H) * (m : H)⁻¹) := by simp
          _ = (v * (m : H)) * (m : H)⁻¹ := by simp [mul_assoc]
          _ = k * (m : H)⁻¹ := by rw [hmul]
      rw [hv_eq]
      exact NK.mul_mem hkNK (NK.inv_mem hmNK)
    have hv_one : v = 1 := (Subgroup.disjoint_def.mp hV_disj_NK) hv hvNK
    have hkM : k ∈ M := by
      have hk_eq : k = (m : H) := by
        calc
          k = v * (m : H) := by simpa using hmul.symm
          _ = (m : H) := by simp [hv_one]
      exact hk_eq ▸ hm
    have hM_le_normX : M ≤ Subgroup.normalizer (X : Set H) := by
      exact sup_le Subgroup.le_normalizer hPsub_normX
    let kM : M := ⟨k, hkM⟩
    have hXsub_normal : (X.subgroupOf M).Normal := by
      exact Subgroup.normal_subgroupOf_of_le_normalizer (H := M) (N := X) hM_le_normX
    let : (X.subgroupOf M).Normal := hXsub_normal
    have hkM_sup : kM ∈ X.subgroupOf M ⊔ Psub.subgroupOf M := by
      have hsub_sup : X.subgroupOf M ⊔ Psub.subgroupOf M = ⊤ := by
        calc
          X.subgroupOf M ⊔ Psub.subgroupOf M = (X ⊔ Psub).subgroupOf M := by
            symm
            exact Subgroup.subgroupOf_sup (A := X) (A' := Psub) (B := M) le_sup_left le_sup_right
          _ = ⊤ := by simp [M]
      simp [hsub_sup]
    rcases (Subgroup.mem_sup_of_normal_left
      (s := X.subgroupOf M) (t := Psub.subgroupOf M) (x := kM)).1 hkM_sup with
      ⟨x, hx, y, hy, hxy⟩
    have hxX : (x : H) ∈ X := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxK : (x : H) ∈ K := hX_le hxX
    have hyPsub : (y : H) ∈ Psub := by
      simpa [Subgroup.mem_subgroupOf] using hy
    have hxy_val : (x : H) * (y : H) = k := by
      exact congrArg Subtype.val hxy
    have hyK : (y : H) ∈ K := by
      have hy_eq : (y : H) = (x : H)⁻¹ * k := by
        calc
          (y : H) = 1 * (y : H) := by simp
          _ = (x : H)⁻¹ * ((x : H) * (y : H)) := by simp
          _ = (x : H)⁻¹ * k := by rw [hxy_val]
      rw [hy_eq]
      exact K.mul_mem (K.inv_mem hxK) hk
    have hybot : (y : H) ∈ (⊥ : Subgroup H) := by
      have hyinf : (y : H) ∈ K ⊓ Psub := ⟨hyK, hyPsub⟩
      simpa [hKinfPsub_bot] using hyinf
    have hy_one : (y : H) = 1 := by simpa using hybot
    have hk_eq : k = (x : H) := by
      calc
        k = (x : H) * (y : H) := by simpa using hxy_val.symm
        _ = (x : H) := by simp [hy_one]
    exact hk_eq ▸ hxX
  refine ⟨K, P, hVK_sup, hVK_disj, hK_inv, hNK_inv, hPsub_inv, hVNK_sup, hVinfNK_bot,
    hKsub_fit, hCH_le_K, hP_p, hPK_ne_bot, hVKP_top, hR_eq_R₀, ?_⟩
  intro X hX_le hX_inv hPsub_normX hX_lt
  let NgX : Subgroup G := (V ⊔ X ⊔ Psub).map H.subtype
  have hNgX_lt : NgX ⊔ R₀ < ⊤ := by
    by_cases htop : NgX ⊔ R₀ = ⊤
    · have htopX : V ⊔ X ⊔ Psub = ⊤ := by
        simpa [NgX] using hN_top_of_ambient_top X hX_inv hPsub_normX htop
      have hK_le_X : K ≤ X := hK_le_X_of_top X hX_le hPsub_normX htopX
      exact False.elim (hX_lt.not_ge hK_le_X)
    · exact lt_of_le_of_ne le_top htop
  simpa [V, Psub, NgX, sup_assoc] using
    theorem_3_6_commutator_bot_of_proper_subambient H R R₀ p hind hsolvG hodd hHR
      hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hVK_disj P hP_p hK_inv hNK_inv
      hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K X hX_le hX_inv hPsub_normX hNgX_lt

public theorem CFSG.theorem_3_6_K_eq_commutator_with_P
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    (hK_inv : IsInvariant (↥R) (↥H) K) →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    K = ⁅K, normalizerSubtypeMap K P⁆ := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit hP_p hPK_ne_bot hproper
  let Psub : Subgroup H := normalizerSubtypeMap K P
  have hPsub_le_NK : Psub ≤ normalizerOf K := by
    simpa [Psub, normalizerSubtypeMap] using (Subgroup.map_subtype_le P)
  have hPsub_normK : Psub ≤ Subgroup.normalizer (K : Set H) := by
    simpa [normalizerOf] using hPsub_le_NK
  have hcop_p_K : Nat.Coprime p (Nat.card K) :=
    theorem_3_6_complement_card_coprime H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_disj hVK_sup
  have hPsub_p : IsPGroup p Psub := by
    change IsPGroup p (normalizerSubtypeMap K P)
    exact isPGroup_normalizerSubtypeMap K P hP_p
  have hX_eq : K = ⁅K, Psub⁆ := by
    let X : Subgroup H := ⁅K, Psub⁆
    by_contra hX_ne
    let NK : Subgroup H := normalizerOf K
    let Ksub : Subgroup NK := K.subgroupOf NK
    let Psubsub : Subgroup NK := Psub.subgroupOf NK
    let Xsub : Subgroup NK := ⁅Ksub, Psubsub⁆
    have hK_le_NK : K ≤ NK := Subgroup.le_normalizer
    have hKsub_normal : Ksub.Normal := by
      exact Subgroup.normal_subgroupOf_of_le_normalizer (H := NK) (N := K)
        (by simp [NK, normalizerOf])
    let : Ksub.Normal := hKsub_normal
    have hPsubsub_normXsub : Psubsub ≤ Subgroup.normalizer (Xsub : Set NK) := by
      exact commutator_normalizer_le (V := Ksub) (K := Psubsub) (N := Psubsub)
        (show Psubsub ≤ Subgroup.normalizer (Psubsub : Set NK) from Subgroup.le_normalizer)
    have hXsub_map : Xsub.map NK.subtype = X := by
      calc
        Xsub.map NK.subtype = ⁅Ksub.map NK.subtype, Psubsub.map NK.subtype⁆ := by
          simpa [Xsub] using (Subgroup.map_commutator (H₁ := Ksub) (H₂ := Psubsub) NK.subtype)
        _ = ⁅K, Psub⁆ := by
          rw [Subgroup.map_subgroupOf_eq_of_le (G := H) (H := K) (K := NK) hK_le_NK]
          rw [Subgroup.map_subgroupOf_eq_of_le (G := H) (H := Psub) (K := NK) hPsub_le_NK]
        _ = X := rfl
    have hXsub_le_Ksub : Xsub ≤ Ksub := by
      simpa [Xsub] using (Subgroup.commutator_le_left (H₁ := Ksub) (H₂ := Psubsub))
    have hX_le_K : X ≤ K := by
      rw [← hXsub_map]
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [Ksub, Subgroup.mem_subgroupOf] using (hXsub_le_Ksub hy)
    have hX_lt : X < K := by
      refine lt_of_le_of_ne hX_le_K ?_
      simpa [X, eq_comm] using hX_ne
    have hX_inv : IsInvariant (↥R) (↥H) X := by
      let : IsInvariant (↥R) (↥H) K := hK_inv
      let : IsInvariant (↥R) (↥H) Psub := hPsub_inv
      simpa [X] using isInvariant_commutator (A := ↥R) K Psub
    have hPsub_conjX :
        ∀ a : Psub, ∀ x ∈ X, (a : H) * x * (a : H)⁻¹ ∈ X := by
      intro a x hx
      rw [← hXsub_map] at hx ⊢
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      let aNK : NK := ⟨a, hPsub_le_NK a.2⟩
      have haPsubsub : aNK ∈ Psubsub := by
        change (a : H) ∈ Psub
        exact a.2
      refine ⟨aNK * y * aNK⁻¹, ?_, ?_⟩
      · exact ((Subgroup.mem_normalizer_iff.mp (hPsubsub_normXsub haPsubsub)) y).1 hy
      · rfl
    have hPsub_normX : Psub ≤ Subgroup.normalizer (X : Set H) :=
      subgroup_le_normalizer_of_conj_mem X Psub hPsub_conjX
    have hcommXX_bot : ⁅X, Psub⁆ = ⊥ :=
      hproper X hX_le_K hX_inv hPsub_normX hX_lt
    have : Subgroup.Normalizes Psub K := ⟨hPsub_normK⟩
    let C : Subgroup K := commutatorAction (A := ↥Psub) (G := ↥K)
    have hCmap : C.map K.subtype = X := by
      simpa [C, X] using commutatorAction_subgroup_conj_map_eq_commutator K Psub hPsub_normK
    have hcomm₂_map_le :
        (commutatorAction₂ (A := ↥Psub) (G := ↥K)).map K.subtype ≤ ⁅X, Psub⁆ := by
      let S : Set K := {x : K | ∃ a : Psub, ∃ g : K, g ∈ C ∧ x = g⁻¹ * (a • g)}
      calc
        (commutatorAction₂ (A := ↥Psub) (G := ↥K)).map K.subtype = (Subgroup.closure S).map K.subtype := by
          rfl
        _ = Subgroup.closure (K.subtype '' S) := by
          simpa using (MonoidHom.map_closure (f := K.subtype) S)
        _ ≤ ⁅X, Psub⁆ := by
          refine (Subgroup.closure_le (K := ⁅X, Psub⁆)).2 ?_
          rintro _ ⟨y, hy, rfl⟩
          rcases hy with ⟨a, g, hgC, rfl⟩
          have hgX : (g : H) ∈ X := by
            rw [← hCmap]
            exact Subgroup.mem_map_of_mem K.subtype hgC
          have :
              ⁅((g : K) : H)⁻¹, (a : H)⁆ ∈ ⁅X, Psub⁆ :=
            Subgroup.commutator_mem_commutator (H₁ := X) (H₂ := Psub) (X.inv_mem hgX) a.2
          simpa [C, X, commutatorElement_def,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hPsub_normK, mul_assoc] using this
    have hcomm₂_bot : commutatorAction₂ (A := ↥Psub) (G := ↥K) = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective
        (H := commutatorAction₂ (A := ↥Psub) (G := ↥K)) (f := K.subtype) K.subtype_injective).1
      exact le_antisymm (hcomm₂_map_le.trans (by simp [hcommXX_bot])) bot_le
    have hcopPsubK : Nat.Coprime (Nat.card Psub) (Nat.card K) := by
      obtain ⟨n, hcardPsub⟩ := hPsub_p.exists_card_eq
      rw [hcardPsub]
      exact hcop_p_K.pow_left n
    have hsolvK : Group.IsSolvable ↥K := by infer_instance
    have hcomm_eq' :
        commutatorAction₂ (A := ↥Psub) (G := ↥K) = commutatorAction (A := ↥Psub) (G := ↥K) :=
      proposition_1_6_b (G := ↥K) (A := ↥Psub) hsolvK hcopPsubK
    have hcomm_bot : C = ⊥ := by
      calc
        C = commutatorAction (A := ↥Psub) (G := ↥K) := rfl
        _ = commutatorAction₂ (A := ↥Psub) (G := ↥K) := hcomm_eq'.symm
        _ = ⊥ := hcomm₂_bot
    have hX_bot : X = ⊥ := by
      simpa [C, hcomm_bot] using hCmap.symm
    exact hPK_ne_bot (by simpa [Psub, X, Subgroup.commutator_comm] using hX_bot)
  simpa [Psub] using hX_eq

public theorem CFSG.theorem_3_6_K_is_q_group
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    IsInvariant (↥R) (↥H) K →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    ∃ qK : ℕ, Nat.Prime qK ∧ qK ≠ p ∧ qK ≠ Nat.card R₀ ∧ IsPGroup qK K := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper
  let Psub : Subgroup H := normalizerSubtypeMap K P
  let NK : Subgroup H := normalizerOf K
  have hPsub_le_NK : Psub ≤ NK := by
    simpa [Psub, NK, normalizerSubtypeMap] using (Subgroup.map_subtype_le P)
  have hPsub_normK : Psub ≤ Subgroup.normalizer (K : Set H) := by
    simpa [NK, normalizerOf] using hPsub_le_NK
  let : IsInvariant (↥R) (↥H) K := hK_inv
  have : Subgroup.Normalizes Psub K := ⟨hPsub_normK⟩
  have hcop_p_K : Nat.Coprime p (Nat.card K) :=
    theorem_3_6_complement_card_coprime H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_disj hVK_sup
  have hPsub_p : IsPGroup p Psub := by
    change IsPGroup p (normalizerSubtypeMap K P)
    exact isPGroup_normalizerSubtypeMap K P hP_p
  have hcop_K_Psub : Nat.Coprime (Nat.card K) (Nat.card Psub) := by
    obtain ⟨n, hcardPsub⟩ := hPsub_p.exists_card_eq
    rw [hcardPsub]
    exact hcop_p_K.symm.pow_right n
  have hKinfPsub_bot : K ⊓ Psub = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop_K_Psub).eq_bot
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    exact hPK_ne_bot (by simp [hK_bot])
  have hPsub_ne_bot : Psub ≠ ⊥ := by
    intro hPsub_bot
    exact hPK_ne_bot (by
      simp [Psub, hPsub_bot])
  let : Nontrivial ↥K := K.nontrivial_iff_ne_bot.mpr hK_ne_bot
  let : Nontrivial ↥Psub := Psub.nontrivial_iff_ne_bot.mpr hPsub_ne_bot
  have hfaith : FaithfulSMul (↥Psub) (↥K) := by
    refine (faithfulSMul_iff (G := ↥Psub) (α := ↥K)).2 ?_
    intro a ha
    have ha_cent : (a : H) ∈ subgroupCentralizerIn (⊤ : Subgroup H) K := by
      refine ⟨by simp, ?_⟩
      change (a : H) ∈ Subgroup.centralizer (K : Set H)
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hfix : a • (⟨k, hk⟩ : K) = ⟨k, hk⟩ := ha ⟨k, hk⟩
      have hfix' : (a : H) * k * (a : H)⁻¹ = k := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hPsub_normK] using
          congrArg Subtype.val hfix
      have := congrArg (fun t : H => t * (a : H)) hfix'
      simpa [mul_assoc] using this.symm
    have haK : (a : H) ∈ K := hCH_le_K ha_cent
    have ha_bot : (a : H) ∈ (⊥ : Subgroup H) := by
      have : (a : H) ∈ K ⊓ Psub := ⟨haK, a.2⟩
      simpa [hKinfPsub_bot] using this
    apply Subtype.ext
    simpa using ha_bot
  have hKsub_nil : Group.IsNilpotent ↥(K.subgroupOf NK) := by
    rw [hKsub_fit]
    infer_instance
  have hK_le_NK : K ≤ NK := Subgroup.le_normalizer
  let eK : K.subgroupOf NK ≃* K :=
    Subgroup.subgroupOfEquivOfLe (G := ↥H) (H := K) (K := NK) hK_le_NK
  have hnilK : Group.IsNilpotent ↥K :=
    Group.nilpotent_of_mulEquiv (G := ↥(K.subgroupOf NK)) (G' := ↥K) eK
  have htop_map : (⊤ : Subgroup K).map K.subtype = K := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  have hproper_fix :
      ∀ L : Subgroup K, L.Characteristic → L ≠ ⊤ → L ≤ fixedPointSubgroup (↥Psub) (↥K) := by
    intro L hL_char hL_top
    let Lmap : Subgroup H := L.map K.subtype
    have hLmap_le_K : Lmap ≤ K := by
      simpa [Lmap] using (Subgroup.map_subtype_le L)
    have hLmap_ne_K : Lmap ≠ K := by
      intro hEq
      apply hL_top
      apply (Subgroup.map_injective (f := K.subtype) K.subtype_injective)
      simpa [Lmap, htop_map] using hEq
    have hLmap_lt : Lmap < K := lt_of_le_of_ne hLmap_le_K hLmap_ne_K
    let : L.Characteristic := hL_char
    let : IsInvariant (↥R) (↥K) L := isInvariant_of_characteristic (A := ↥R) (G := ↥K) L
    have hLmap_invR : IsInvariant (↥R) (↥H) Lmap := by
      simpa [Lmap] using isInvariant_map_subtype (A := ↥R) (G := ↥H) K L
    let : IsInvariant (↥Psub) (↥K) L := isInvariant_of_characteristic (A := ↥Psub) (G := ↥K) L
    have hPsub_normLmap : Psub ≤ Subgroup.normalizer (Lmap : Set H) := by
      refine subgroup_le_normalizer_of_conj_mem Lmap Psub ?_
      intro a x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy' : a • y ∈ L := (IsInvariant.invariant (A := ↥Psub) (G := ↥K) (H := L) a y).1 hy
      simpa [Lmap, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hPsub_normK] using
        (Subgroup.mem_map_of_mem K.subtype hy')
    have : Subgroup.Normalizes Psub Lmap := ⟨hPsub_normLmap⟩
    have hcommLmap_bot : ⁅Lmap, Psub⁆ = ⊥ :=
      hproper Lmap hLmap_le_K hLmap_invR hPsub_normLmap hLmap_lt
    have htrivLmap : ActsTrivially (A := ↥Psub) (G := ↥Lmap) := by
      exact actsTrivially_subgroup_conj_of_commutator_eq_bot Lmap Psub hPsub_normLmap
        (by simpa [Subgroup.commutator_comm] using hcommLmap_bot)
    intro x hx
    rw [FixedPoints.mem_subgroup]
    intro a
    have hxmap : (x : H) ∈ Lmap := Subgroup.mem_map_of_mem K.subtype hx
    have hfix : a • (⟨(x : H), hxmap⟩ : Lmap) = ⟨(x : H), hxmap⟩ := htrivLmap a ⟨(x : H), hxmap⟩
    apply Subtype.ext
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hPsub_normK, hPsub_normLmap] using
      congrArg Subtype.val hfix
  let : FaithfulSMul (↥Psub) (↥K) := hfaith
  obtain ⟨qK, hqK_prime, hqK_pgroup⟩ :=
    exists_prime_isPGroup_of_nilpotent_of_proper_characteristic_fixed
      (K := ↥K) (A := ↥Psub) hnilK hproper_fix
  have : Fact qK.Prime := ⟨hqK_prime⟩
  obtain ⟨nK, hnK_pos, hcardKq⟩ :=
    (IsPGroup.nontrivial_iff_card (p := qK) (G := ↥K) (hG := hqK_pgroup)).mp inferInstance
  have hqK_dvd_K : qK ∣ Nat.card K := by
    rw [hcardKq]
    exact dvd_pow_self qK (Nat.ne_of_gt hnK_pos)
  have hqK_ne_p : qK ≠ p := by
    intro hEq
    have hqK_cop_K : Nat.Coprime qK (Nat.card K) := by
      simpa [hEq] using hcop_p_K
    exact (hqK_prime.coprime_iff_not_dvd.mp hqK_cop_K) hqK_dvd_K
  have hcop_H_R₀ : Nat.Coprime (Nat.card H) (Nat.card R₀) := by
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le hR₀_le) hcopHR
  have hqK_ne_R₀ : qK ≠ Nat.card R₀ := by
    intro hEq
    have hqK_cop_R₀ : Nat.Coprime qK (Nat.card R₀) :=
      Nat.Coprime.of_dvd_left (dvd_trans hqK_dvd_K (Subgroup.card_subgroup_dvd_card K)) hcop_H_R₀
    exact (hqK_prime.coprime_iff_not_dvd.mp hqK_cop_R₀) (hEq ▸ dvd_rfl)
  exact ⟨qK, hqK_prime, hqK_ne_p, hqK_ne_R₀, hqK_pgroup⟩

public theorem CFSG.theorem_3_6_K_class_two_exponent_q
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    IsInvariant (↥R) (↥H) K →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    ∃ qK : ℕ, Nat.Prime qK ∧ qK ≠ p ∧ qK ≠ Nat.card R₀ ∧ IsPGroup qK K ∧
      commutator (↥K) ≤ Subgroup.center (↥K) ∧ Monoid.exponent (↥K) = qK := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper
  let Psub : Subgroup H := normalizerSubtypeMap K P
  let NK : Subgroup H := normalizerOf K
  have hPsub_le_NK : Psub ≤ NK := by
    simpa [Psub, NK, normalizerSubtypeMap] using (Subgroup.map_subtype_le P)
  have hPsub_normK : Psub ≤ Subgroup.normalizer (K : Set H) := by
    simpa [NK, normalizerOf] using hPsub_le_NK
  let : IsInvariant (↥R) (↥H) K := hK_inv
  have : Subgroup.Normalizes Psub K := ⟨hPsub_normK⟩
  have hcop_p_K : Nat.Coprime p (Nat.card K) :=
    theorem_3_6_complement_card_coprime H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_disj hVK_sup
  have hPsub_p : IsPGroup p Psub := by
    change IsPGroup p (normalizerSubtypeMap K P)
    exact isPGroup_normalizerSubtypeMap K P hP_p
  have hcop_K_Psub : Nat.Coprime (Nat.card K) (Nat.card Psub) := by
    obtain ⟨n, hcardPsub⟩ := hPsub_p.exists_card_eq
    rw [hcardPsub]
    exact hcop_p_K.symm.pow_right n
  have hKinfPsub_bot : K ⊓ Psub = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop_K_Psub).eq_bot
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    exact hPK_ne_bot (by simp [hK_bot])
  let : Nontrivial ↥K := K.nontrivial_iff_ne_bot.mpr hK_ne_bot
  have hPsub_ne_bot : Psub ≠ ⊥ := by
    intro hPsub_bot
    exact hPK_ne_bot (by
      simp [Psub, hPsub_bot])
  let : Nontrivial ↥Psub := Psub.nontrivial_iff_ne_bot.mpr hPsub_ne_bot
  have hfaith : FaithfulSMul (↥Psub) (↥K) := by
    refine (faithfulSMul_iff (G := ↥Psub) (α := ↥K)).2 ?_
    intro a ha
    have ha_cent : (a : H) ∈ subgroupCentralizerIn (⊤ : Subgroup H) K := by
      refine ⟨by simp, ?_⟩
      change (a : H) ∈ Subgroup.centralizer (K : Set H)
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hfix : a • (⟨k, hk⟩ : K) = ⟨k, hk⟩ := ha ⟨k, hk⟩
      have hfix' : (a : H) * k * (a : H)⁻¹ = k := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hPsub_normK] using
          congrArg Subtype.val hfix
      have := congrArg (fun t : H => t * (a : H)) hfix'
      simpa [mul_assoc] using this.symm
    have haK : (a : H) ∈ K := hCH_le_K ha_cent
    have ha_bot : (a : H) ∈ (⊥ : Subgroup H) := by
      have : (a : H) ∈ K ⊓ Psub := ⟨haK, a.2⟩
      simpa [hKinfPsub_bot] using this
    apply Subtype.ext
    simpa using ha_bot
  let : FaithfulSMul (↥Psub) (↥K) := hfaith
  have htop_map : (⊤ : Subgroup K).map K.subtype = K := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  have hproper_fix :
      ∀ L : Subgroup K, L.Characteristic → L ≠ ⊤ → L ≤ fixedPointSubgroup (↥Psub) (↥K) := by
    intro L hL_char hL_top
    let Lmap : Subgroup H := L.map K.subtype
    have hLmap_le_K : Lmap ≤ K := by
      simpa [Lmap] using (Subgroup.map_subtype_le L)
    have hLmap_ne_K : Lmap ≠ K := by
      intro hEq
      apply hL_top
      apply (Subgroup.map_injective (f := K.subtype) K.subtype_injective)
      simpa [Lmap, htop_map] using hEq
    have hLmap_lt : Lmap < K := lt_of_le_of_ne hLmap_le_K hLmap_ne_K
    let : L.Characteristic := hL_char
    let : IsInvariant (↥R) (↥K) L := isInvariant_of_characteristic (A := ↥R) (G := ↥K) L
    have hLmap_invR : IsInvariant (↥R) (↥H) Lmap := by
      simpa [Lmap] using isInvariant_map_subtype (A := ↥R) (G := ↥H) K L
    let : IsInvariant (↥Psub) (↥K) L := isInvariant_of_characteristic (A := ↥Psub) (G := ↥K) L
    have hPsub_normLmap : Psub ≤ Subgroup.normalizer (Lmap : Set H) := by
      refine subgroup_le_normalizer_of_conj_mem Lmap Psub ?_
      intro a x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy' : a • y ∈ L := (IsInvariant.invariant (A := ↥Psub) (G := ↥K) (H := L) a y).1 hy
      simpa [Lmap, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hPsub_normK] using
        (Subgroup.mem_map_of_mem K.subtype hy')
    have : Subgroup.Normalizes Psub Lmap := ⟨hPsub_normLmap⟩
    have hcommLmap_bot : ⁅Lmap, Psub⁆ = ⊥ :=
      hproper Lmap hLmap_le_K hLmap_invR hPsub_normLmap hLmap_lt
    have htrivLmap : ActsTrivially (A := ↥Psub) (G := ↥Lmap) := by
      exact actsTrivially_subgroup_conj_of_commutator_eq_bot Lmap Psub hPsub_normLmap
        (by simpa [Subgroup.commutator_comm] using hcommLmap_bot)
    intro x hx
    rw [FixedPoints.mem_subgroup]
    intro a
    have hxmap : (x : H) ∈ Lmap := Subgroup.mem_map_of_mem K.subtype hx
    have hfix : a • (⟨(x : H), hxmap⟩ : Lmap) = ⟨(x : H), hxmap⟩ := htrivLmap a ⟨(x : H), hxmap⟩
    apply Subtype.ext
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hPsub_normK, hPsub_normLmap] using
      congrArg Subtype.val hfix
  obtain ⟨qK, hqK_prime, hqK_ne_p, hqK_ne_R₀, hqK_pgroup⟩ :=
    theorem_3_6_K_is_q_group H R R₀ p hind hsolvG hodd hHR hcopHR hR₀_le
      hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit
      hCH_le_K hP_p hPK_ne_bot hproper
  have : Fact qK.Prime := ⟨hqK_prime⟩
  have : Fact (IsPGroup qK ↥K) := ⟨hqK_pgroup⟩
  have hcopPsubK : Nat.Coprime (Nat.card Psub) (Nat.card K) := by
    obtain ⟨n, hcardPsub⟩ := hPsub_p.exists_card_eq
    rw [hcardPsub]
    exact hcop_p_K.pow_left n
  have hoddK : Odd (Nat.card K) := by
    exact odd_of_card_dvd hodd
      ((Subgroup.card_subgroup_dvd_card K).trans (Subgroup.card_subgroup_dvd_card H))
  have hqK_dvd_K : qK ∣ Nat.card K := by
    obtain ⟨nK, hnK_pos, hcardKq⟩ :=
      (IsPGroup.nontrivial_iff_card (p := qK) (G := ↥K) (hG := hqK_pgroup)).mp inferInstance
    rw [hcardKq]
    exact dvd_pow_self qK (Nat.ne_of_gt hnK_pos)
  have hqodd : qK ≠ 2 := Odd.ne_two_of_dvd_nat hoddK hqK_dvd_K
  obtain ⟨hcomm_center, hexpK⟩ :=
    classTwo_exponent_prime_of_proper_characteristic_fixed
      (K := ↥K) (A := ↥Psub) hqodd hcopPsubK hproper_fix
  exact ⟨qK, hqK_prime, hqK_ne_p, hqK_ne_R₀, hqK_pgroup, hcomm_center, hexpK⟩

public theorem CFSG.theorem_3_6_K_quotient_commutator_fixed_eq_bot
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    IsInvariant (↥R) (↥H) K →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    let Psub : Subgroup H := normalizerSubtypeMap K P
    haveI : Subgroup.Normalizes Psub K :=
      ⟨by
        simpa [Psub, normalizerOf, normalizerSubtypeMap] using (Subgroup.map_subtype_le P)⟩
    let hKcomm_inv : IsInvariant (↥Psub) (↥K) (commutator (↥K)) :=
      isInvariant_of_characteristic (A := ↥Psub) (G := ↥K) (commutator (↥K))
    let _ : MulDistribMulAction (↥Psub) (↥K ⧸ commutator (↥K)) :=
      quotientMulDistribMulAction (A := ↥Psub) (G := ↥K) (commutator (↥K)) hKcomm_inv
    fixedPointSubgroup (↥Psub) (↥K ⧸ commutator (↥K)) = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit hP_p hPK_ne_bot hproper
  let Psub : Subgroup H := normalizerSubtypeMap K P
  have hPsub_le_NK : Psub ≤ normalizerOf K := by
    simpa [Psub, normalizerSubtypeMap] using (Subgroup.map_subtype_le P)
  have hPsub_normK : Psub ≤ Subgroup.normalizer (K : Set H) := by
    simpa [normalizerOf] using hPsub_le_NK
  have : Subgroup.Normalizes Psub K := ⟨hPsub_normK⟩
  have hcop_p_K : Nat.Coprime p (Nat.card K) :=
    theorem_3_6_complement_card_coprime H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_disj hVK_sup
  have hPsub_p : IsPGroup p Psub := by
    change IsPGroup p (normalizerSubtypeMap K P)
    exact isPGroup_normalizerSubtypeMap K P hP_p
  have hcopPsubK : Nat.Coprime (Nat.card Psub) (Nat.card K) := by
    obtain ⟨n, hcardPsub⟩ := hPsub_p.exists_card_eq
    rw [hcardPsub]
    exact hcop_p_K.pow_left n
  have hK_eq : K = ⁅K, Psub⁆ :=
    theorem_3_6_K_eq_commutator_with_P H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit
      hP_p hPK_ne_bot hproper
  let hKcomm_inv : IsInvariant (↥Psub) (↥K) (commutator (↥K)) :=
    isInvariant_of_characteristic (A := ↥Psub) (G := ↥K) (commutator (↥K))
  let : MulAction.QuotientAction (↥Psub) (commutator (↥K)) :=
    quotientAction_of_isInvariant (A := ↥Psub) (commutator (↥K)) hKcomm_inv
  let : MulDistribMulAction (↥Psub) (↥K ⧸ commutator (↥K)) :=
    quotientMulDistribMulAction (A := ↥Psub) (G := ↥K) (commutator (↥K)) hKcomm_inv
  have htop_map : (⊤ : Subgroup K).map K.subtype = K := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  have hcommK_top : commutatorAction (A := ↥Psub) (G := ↥K) = ⊤ := by
    apply (Subgroup.map_injective (f := K.subtype) K.subtype_injective)
    calc
      (commutatorAction (A := ↥Psub) (G := ↥K)).map K.subtype = ⁅K, Psub⁆ := by
        simpa using commutatorAction_subgroup_conj_map_eq_commutator K Psub hPsub_normK
      _ = K := hK_eq.symm
      _ = (⊤ : Subgroup K).map K.subtype := htop_map.symm
  let qcomm : ↥K →* (↥K ⧸ commutator (↥K)) := QuotientGroup.mk' (commutator (↥K))
  have hmap_top :
      (commutatorAction (A := ↥Psub) (G := ↥K)).map qcomm = ⊤ := by
    rw [hcommK_top]
    simpa [qcomm] using
      (Subgroup.map_top_of_surjective (f := QuotientGroup.mk' (commutator (↥K)))
        (QuotientGroup.mk'_surjective (N := commutator (↥K))))
  have hmap_le :
      (commutatorAction (A := ↥Psub) (G := ↥K)).map qcomm ≤
        commutatorAction (A := ↥Psub) (G := ↥K ⧸ commutator (↥K)) := by
    let S : Set K := {x : K | ∃ a : Psub, ∃ g : K, x = g⁻¹ * (a • g)}
    let T : Set (↥K ⧸ commutator (↥K)) :=
      {x : ↥K ⧸ commutator (↥K) | ∃ a : Psub, ∃ g : ↥K ⧸ commutator (↥K), x = g⁻¹ * (a • g)}
    have hS : commutatorAction (A := ↥Psub) (G := ↥K) = Subgroup.closure S := by
      simpa [S] using (commutatorAction_eq_closure (G := ↥K) (A := ↥Psub))
    have hT :
        commutatorAction (A := ↥Psub) (G := ↥K ⧸ commutator (↥K)) = Subgroup.closure T := by
      simpa [T] using
        (commutatorAction_eq_closure (G := ↥K ⧸ commutator (↥K)) (A := ↥Psub))
    rw [hS, hT]
    have hmap :
        (Subgroup.closure S).map qcomm = Subgroup.closure (qcomm '' S) := by
      simpa [qcomm] using (MonoidHom.map_closure (f := qcomm) S)
    rw [hmap]
    refine (Subgroup.closure_le (K := Subgroup.closure T)).2 ?_
    intro x hx
    rcases hx with ⟨y, hyS, rfl⟩
    rcases hyS with ⟨a, g, rfl⟩
    refine Subgroup.subset_closure ?_
    refine ⟨a, qcomm g, ?_⟩
    simp [qcomm]
  have hcommQ_top : commutatorAction (A := ↥Psub) (G := ↥K ⧸ commutator (↥K)) = ⊤ := by
    apply top_unique
    simpa [hmap_top] using hmap_le
  have hQcomm : IsMulCommutative (↥K ⧸ commutator (↥K)) := by
    exact
      (Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := commutator (↥K))).mpr le_rfl
  have hcopPsubQ : Nat.Coprime (Nat.card Psub) (Nat.card (↥K ⧸ commutator (↥K))) := by
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_quotient_dvd_card (s := commutator (↥K))) hcopPsubK
  have hsolvQ : Group.IsSolvable (↥K ⧸ commutator (↥K)) := by infer_instance
  have hcompl :
      IsCompl (fixedPointSubgroup (↥Psub) (↥K ⧸ commutator (↥K)))
        (commutatorAction (A := ↥Psub) (G := ↥K ⧸ commutator (↥K))) :=
    proposition_1_6_d (G := ↥K ⧸ commutator (↥K)) (A := ↥Psub) hsolvQ hcopPsubQ hQcomm
  simpa [hcommQ_top] using hcompl.inf_eq_bot

public theorem CFSG.theorem_3_6_K_frattini_eq_commutator
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    IsInvariant (↥R) (↥H) K →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    frattini (↥K) = commutator (↥K) := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper
  obtain ⟨qK, hqK_prime, -, -, hqK_pgroup, -, hexpK⟩ :=
    theorem_3_6_K_class_two_exponent_q H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv
      hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper
  have : Fact qK.Prime := ⟨hqK_prime⟩
  have : Fact (IsPGroup qK ↥K) := ⟨hqK_pgroup⟩
  have hfrattini :
      frattini (↥K) =
        Subgroup.closure ((derivedSubgroup (↥K) : Set ↥K) ∪ Set.range (fun x : ↥K => x ^ qK)) :=
    lemma_1_7_d (R := ↥K) (p := qK)
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [hfrattini] at hx
    exact
      (Subgroup.closure_le (K := commutator (↥K))).2 (by
        rintro x (hx | hx)
        · rw [derivedSubgroup, derivedSeries_one] at hx
          change x ∈ ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆
          exact hx
        · rcases hx with ⟨y, rfl⟩
          have hyq : y ^ qK = 1 := by
            exact
              (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                (show Monoid.exponent (↥K) ∣ qK by simp [hexpK])) y
          simp [hyq]) hx
  · intro x hx
    rw [hfrattini]
    apply Subgroup.subset_closure
    apply Or.inl
    rw [derivedSubgroup, derivedSeries_one]
    change x ∈ commutator (↥K) at hx
    exact hx

set_option maxHeartbeats 1000000 in
public theorem CFSG.theorem_3_6_K_quotient_commutator_p_faithful
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    IsInvariant (↥R) (↥H) K →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    let Psub : Subgroup H := normalizerSubtypeMap K P
    haveI : Subgroup.Normalizes Psub K :=
      ⟨by
        simpa [Psub, normalizerOf, normalizerSubtypeMap] using (Subgroup.map_subtype_le P)⟩
    let hKcomm_inv : IsInvariant (↥Psub) (↥K) (commutator (↥K)) :=
      isInvariant_of_characteristic (A := ↥Psub) (G := ↥K) (commutator (↥K))
    let _ : MulDistribMulAction (↥Psub) (↥K ⧸ commutator (↥K)) :=
      quotientMulDistribMulAction (A := ↥Psub) (G := ↥K) (commutator (↥K)) hKcomm_inv
    FaithfulSMul (↥Psub) (↥K ⧸ commutator (↥K)) := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper
  let Psub : Subgroup H := normalizerSubtypeMap K P
  have hPsub_le_NK : Psub ≤ normalizerOf K := by
    simpa [Psub, normalizerSubtypeMap] using (Subgroup.map_subtype_le P)
  have hPsub_normK : Psub ≤ Subgroup.normalizer (K : Set H) := by
    simpa [normalizerOf] using hPsub_le_NK
  have : Subgroup.Normalizes Psub K := ⟨hPsub_normK⟩
  have hcop_p_K : Nat.Coprime p (Nat.card K) :=
    theorem_3_6_complement_card_coprime H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_disj hVK_sup
  have hPsub_p : IsPGroup p Psub := by
    change IsPGroup p (normalizerSubtypeMap K P)
    exact isPGroup_normalizerSubtypeMap K P hP_p
  have hcopPsubK : Nat.Coprime (Nat.card Psub) (Nat.card K) := by
    obtain ⟨n, hcardPsub⟩ := hPsub_p.exists_card_eq
    rw [hcardPsub]
    exact hcop_p_K.pow_left n
  have hKinfPsub_bot : K ⊓ Psub = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcopPsubK.symm).eq_bot
  obtain ⟨qK, hqK_prime, -, -, hqK_pgroup, -, -⟩ :=
    theorem_3_6_K_class_two_exponent_q H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv
      hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper
  have : Fact qK.Prime := ⟨hqK_prime⟩
  have : Fact (IsPGroup qK ↥K) := ⟨hqK_pgroup⟩
  have hPhi_eq : frattini (↥K) = commutator (↥K) :=
    theorem_3_6_K_frattini_eq_commutator H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv
      hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper
  let hKcomm_inv : IsInvariant (↥Psub) (↥K) (commutator (↥K)) :=
    isInvariant_of_characteristic (A := ↥Psub) (G := ↥K) (commutator (↥K))
  let : MulAction.QuotientAction (↥Psub) (commutator (↥K)) :=
    quotientAction_of_isInvariant (A := ↥Psub) (commutator (↥K)) hKcomm_inv
  let : MulDistribMulAction (↥Psub) (↥K ⧸ commutator (↥K)) :=
    quotientMulDistribMulAction (A := ↥Psub) (G := ↥K) (commutator (↥K)) hKcomm_inv
  refine (faithfulSMul_iff (G := ↥Psub) (α := ↥K ⧸ commutator (↥K))).2 ?_
  intro a ha
  have hcop_zpow_K : Nat.Coprime (Nat.card (Subgroup.zpowers a)) (Nat.card K) := by
    exact Nat.Coprime.of_dvd_left (Subgroup.card_subgroup_dvd_card (Subgroup.zpowers a)) hcopPsubK
  let hcomm_inv_zpow : IsInvariant (↥(Subgroup.zpowers a)) (↥K) (commutator (↥K)) :=
    isInvariant_of_characteristic (A := ↥(Subgroup.zpowers a)) (G := ↥K) (commutator (↥K))
  let : MulAction.QuotientAction (↥(Subgroup.zpowers a)) (commutator (↥K)) :=
    quotientAction_of_isInvariant (A := ↥(Subgroup.zpowers a)) (commutator (↥K))
      hcomm_inv_zpow
  let : MulDistribMulAction (↥(Subgroup.zpowers a)) (↥K ⧸ commutator (↥K)) :=
    quotientMulDistribMulAction (A := ↥(Subgroup.zpowers a)) (G := ↥K)
      (commutator (↥K)) hcomm_inv_zpow
  have hquot_comm :
      ActsTrivially (A := ↥(Subgroup.zpowers a)) (G := ↥K ⧸ commutator (↥K)) := by
    intro b x
    exact smul_eq_self_of_mem_zpowers (y := a) b.2 (ha x)
  let hPhi_inv_zpow : IsInvariant (↥(Subgroup.zpowers a)) (↥K) (frattini (↥K)) :=
    isInvariant_of_characteristic (A := ↥(Subgroup.zpowers a)) (G := ↥K) (frattini (↥K))
  let : MulAction.QuotientAction (↥(Subgroup.zpowers a)) (frattini (↥K)) :=
    quotientAction_of_isInvariant (A := ↥(Subgroup.zpowers a)) (frattini (↥K))
      hPhi_inv_zpow
  let : MulDistribMulAction (↥(Subgroup.zpowers a)) (↥K ⧸ frattini (↥K)) :=
    quotientMulDistribMulAction (A := ↥(Subgroup.zpowers a)) (G := ↥K) (frattini (↥K))
      hPhi_inv_zpow
  have hquot :
      ActsTrivially (A := ↥(Subgroup.zpowers a)) (G := ↥K ⧸ frattini (↥K)) := by
    intro b x
    refine QuotientGroup.induction_on x ?_
    intro k
    change QuotientGroup.mk' (frattini (↥K)) (b • k) = QuotientGroup.mk' (frattini (↥K)) k
    apply (QuotientGroup.eq_iff_div_mem (N := frattini (↥K)) (x := b • k) (y := k)).2
    have hb_fix_comm := hquot_comm b ((k : ↥K) : ↥K ⧸ commutator (↥K))
    have hb_div_comm : (b • k) / k ∈ commutator (↥K) :=
      (QuotientGroup.eq_iff_div_mem (N := commutator (↥K)) (x := b • k) (y := k)).1
        (by simpa using hb_fix_comm)
    rw [hPhi_eq]
    exact hb_div_comm
  have htrivK : ActsTrivially (A := ↥(Subgroup.zpowers a)) (G := ↥K) :=
    theorem_1_8 (R := ↥K) (A := ↥(Subgroup.zpowers a)) (p := qK) hcop_zpow_K (by simpa using hquot)
  have ha_cent : (a : H) ∈ subgroupCentralizerIn (⊤ : Subgroup H) K := by
    refine ⟨by simp, ?_⟩
    change (a : H) ∈ Subgroup.centralizer (K : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    let a1 : Subgroup.zpowers a := ⟨a, Subgroup.mem_zpowers a⟩
    have hfix : a1 • (⟨k, hk⟩ : K) = ⟨k, hk⟩ := htrivK a1 ⟨k, hk⟩
    have hfix' : (a : H) * k * (a : H)⁻¹ = k := by
      simpa [a1, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hPsub_normK] using
        congrArg Subtype.val hfix
    have := congrArg (fun t : H => t * (a : H)) hfix'
    simpa [mul_assoc] using this.symm
  have haK : (a : H) ∈ K := hCH_le_K ha_cent
  have ha_bot : (a : H) ∈ (⊥ : Subgroup H) := by
    have : (a : H) ∈ K ⊓ Psub := ⟨haK, a.2⟩
    simpa [hKinfPsub_bot] using this
  apply Subtype.ext
  simpa using ha_bot

public theorem CFSG.theorem_3_6_K_quotient_commutator_r_fixed_ne_bot
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    (hK_inv : IsInvariant (↥R) (↥H) K) →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    V ⊔ normalizerOf K = ⊤ →
    V ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    R = R₀ →
    let _ : IsInvariant (↥R) (↥H) K := hK_inv
    let hKcomm_invR : IsInvariant (↥R) (↥K) (commutator (↥K)) :=
      isInvariant_of_characteristic (A := ↥R) (G := ↥K) (commutator (↥K))
    let _ : MulDistribMulAction (↥R) (↥K ⧸ commutator (↥K)) :=
      quotientMulDistribMulAction (A := ↥R) (G := ↥K) (commutator (↥K)) hKcomm_invR
    fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)) ≠ ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
    hP_p hPK_ne_bot hproper hR_eq
  let Psub : Subgroup H := normalizerSubtypeMap K P
  let NK : Subgroup H := normalizerOf K
  have hPsub_le_NK : Psub ≤ NK := by
    simpa [Psub, NK, normalizerSubtypeMap] using (Subgroup.map_subtype_le P)
  have hPsub_normK : Psub ≤ Subgroup.normalizer (K : Set H) := by
    simpa [NK, normalizerOf] using hPsub_le_NK
  let Psubg : Subgroup G := Psub.map H.subtype
  let Sg : Subgroup G := Psubg ⊔ R
  let Ksub : Subgroup Sg := Psubg.subgroupOf Sg
  let Rsub : Subgroup Sg := R.subgroupOf Sg
  let : IsInvariant (↥R) (↥H) K := hK_inv
  let : IsInvariant (↥R) (↥H) Psub := by
    simpa [Psub] using hPsub_inv
  let hKcomm_invR : IsInvariant (↥R) (↥K) (commutator (↥K)) :=
    isInvariant_of_characteristic (A := ↥R) (G := ↥K) (commutator (↥K))
  let : MulAction.QuotientAction (↥R) (commutator (↥K)) :=
    quotientAction_of_isInvariant (A := ↥R) (commutator (↥K)) hKcomm_invR
  let : MulDistribMulAction (↥R) (↥K ⧸ commutator (↥K)) :=
    quotientMulDistribMulAction (A := ↥R) (G := ↥K) (commutator (↥K)) hKcomm_invR
  obtain ⟨qK, hqK_prime, hqK_ne_p, hqK_ne_R₀, hqK_pgroup, hcomm_center, hexpK⟩ :=
    theorem_3_6_K_class_two_exponent_q H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit
      hCH_le_K hP_p hPK_ne_bot hproper
  have : Fact qK.Prime := ⟨hqK_prime⟩
  have : Fact (IsPGroup qK ↥K) := ⟨hqK_pgroup⟩
  have : Subgroup.Normalizes Psub K := ⟨hPsub_normK⟩
  let hKcomm_invP : IsInvariant (↥Psub) (↥K) (commutator (↥K)) :=
    isInvariant_of_characteristic (A := ↥Psub) (G := ↥K) (commutator (↥K))
  let : MulAction.QuotientAction (↥Psub) (commutator (↥K)) :=
    quotientAction_of_isInvariant (A := ↥Psub) (commutator (↥K)) hKcomm_invP
  let : MulDistribMulAction (↥Psub) (↥K ⧸ commutator (↥K)) :=
    quotientMulDistribMulAction (A := ↥Psub) (G := ↥K) (commutator (↥K)) hKcomm_invP
  let : FaithfulSMul (↥Psub) (↥K ⧸ commutator (↥K)) :=
    theorem_3_6_K_quotient_commutator_p_faithful H R R₀ p hind hsolvG hodd hHR
      hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv
      hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper
  let : IsElementaryAbelian qK (↥K ⧸ commutator (↥K)) := by
    refine
      { toIsMulCommutative := by
          exact
            (Subgroup.Normal.quotient_commutative_iff_commutator_le
              (N := commutator (↥K))).mpr le_rfl
        exponent_dvd_p := by
          exact (Group.exponent_quotient_dvd (H := commutator (↥K))).trans (by simp [hexpK]) }
  let : CommGroup (↥K ⧸ commutator (↥K)) := IsMulCommutative.instCommGroup
  have hPsubg_le_H : Psubg ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  have hPsubg_le_normKg : Psubg ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
      rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
      let kK : K := ⟨k, hk⟩
      have hkmap :
          H.subtype ((((⟨b, hb⟩ : Psub) • kK : K) : H)) ∈ K.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype (((⟨b, hb⟩ : Psub) • kK).2)
      change H.subtype b * H.subtype k * (H.subtype b)⁻¹ ∈ K.map H.subtype at hkmap
      exact hkmap
    · intro hx
      rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
      have hb_inv : b⁻¹ ∈ Psub := Psub.inv_mem hb
      rcases Subgroup.mem_map.mp hx with ⟨k, hk, hkx⟩
      let kK : K := ⟨k, hk⟩
      have hkmap :
          H.subtype ((((⟨b⁻¹, hb_inv⟩ : Psub) • kK : K) : H)) ∈ K.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype (((⟨b⁻¹, hb_inv⟩ : Psub) • kK).2)
      have hkx' :
          H.subtype ((((⟨b⁻¹, hb_inv⟩ : Psub) • kK : K) : H)) = x := by
        calc
          H.subtype ((((⟨b⁻¹, hb_inv⟩ : Psub) • kK : K) : H)) = (b : G)⁻¹ * (k : H) * (b : G) := by
            simp [kK, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
              mul_assoc]
          _ = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * (b : G) := by
            simpa using congrArg (fun z : G => (b : G)⁻¹ * z * (b : G)) hkx
          _ = x := by simp [mul_assoc]
      exact hkx' ▸ hkmap
  have hR_le_normKg : R ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
      let kK : K := ⟨k, hk⟩
      have hkmap :
          H.subtype ((((⟨a, ha⟩ : R) • kK : K) : H)) ∈ K.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype (((⟨a, ha⟩ : R) • kK).2)
      change a * H.subtype k * a⁻¹ ∈ K.map H.subtype at hkmap
      exact hkmap
    · intro hx
      have ha_inv : a⁻¹ ∈ R := R.inv_mem ha
      rcases Subgroup.mem_map.mp hx with ⟨k, hk, hkx⟩
      let kK : K := ⟨k, hk⟩
      have hkmap :
          H.subtype ((((⟨a⁻¹, ha_inv⟩ : R) • kK : K) : H)) ∈ K.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype (((⟨a⁻¹, ha_inv⟩ : R) • kK).2)
      have hkx' :
          H.subtype ((((⟨a⁻¹, ha_inv⟩ : R) • kK : K) : H)) = x := by
        calc
          H.subtype ((((⟨a⁻¹, ha_inv⟩ : R) • kK : K) : H)) =
              H.subtype ((⟨a⁻¹, ha_inv⟩ : R) • (k : H)) := by
            rfl
          _ = (a : G)⁻¹ * (k : H) * (a : G) := by
            simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
          _ = (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * (a : G) := by
            simpa using congrArg (fun z : G => (a : G)⁻¹ * z * (a : G)) hkx
          _ = x := by simp [mul_assoc]
      exact hkx' ▸ hkmap
  have hSg_le_normKg :
      Sg ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) :=
    sup_le hPsubg_le_normKg hR_le_normKg
  have hSg_le_normH : Sg ≤ Subgroup.normalizer H := by
    exact sup_le (hPsubg_le_H.trans (Subgroup.le_normalizer_of_normal (H := H))) hRnormH
  have : Subgroup.Normalizes Sg H := ⟨hSg_le_normH⟩
  have hPsubgsub_normal : (Psubg.subgroupOf Sg).Normal := by
    have hSg_le_normPsubg : Sg ≤ Subgroup.normalizer (Psubg : Set G) := by
      have hR_le_normPsubg : R ≤ Subgroup.normalizer (Psubg : Set G) := by
        intro a ha
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          let yP : Psub := ⟨y, hy⟩
          have hymap :
              H.subtype ((((⟨a, ha⟩ : R) • yP : Psub) : H)) ∈ Psubg :=
            Subgroup.mem_map_of_mem H.subtype (((⟨a, ha⟩ : R) • yP).2)
          change a * H.subtype y * a⁻¹ ∈ Psubg at hymap
          exact hymap
        · intro hx
          have ha_inv : a⁻¹ ∈ R := R.inv_mem ha
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
          let yP : Psub := ⟨y, hy⟩
          have hymap :
              H.subtype ((((⟨a⁻¹, ha_inv⟩ : R) • yP : Psub) : H)) ∈ Psubg :=
            Subgroup.mem_map_of_mem H.subtype (((⟨a⁻¹, ha_inv⟩ : R) • yP).2)
          have hyx' :
              H.subtype ((((⟨a⁻¹, ha_inv⟩ : R) • yP : Psub) : H)) = x := by
            calc
              H.subtype ((((⟨a⁻¹, ha_inv⟩ : R) • yP : Psub) : H)) =
                  H.subtype ((⟨a⁻¹, ha_inv⟩ : R) • (y : H)) := by
                rfl
              _ = (a : G)⁻¹ * (y : H) * (a : G) := by
                simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
              _ = (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * (a : G) := by
                simpa using congrArg (fun z : G => (a : G)⁻¹ * z * (a : G)) hyx
              _ = x := by simp [mul_assoc]
          exact hyx' ▸ hymap
      exact sup_le Psubg.le_normalizer hR_le_normPsubg
    simpa [Sg] using
      (Subgroup.normal_subgroupOf_of_le_normalizer (H := Sg) (N := Psubg) hSg_le_normPsubg)
  have hsub_sup : (Psubg.subgroupOf Sg) ⊔ R.subgroupOf Sg = ⊤ := by
    calc
      (Psubg.subgroupOf Sg) ⊔ R.subgroupOf Sg = (Psubg ⊔ R).subgroupOf Sg := by
        symm
        exact Subgroup.subgroupOf_sup (A := Psubg) (A' := R) (B := Sg) le_sup_left le_sup_right
      _ = ⊤ := by simp [Sg]
  have hK_invS : IsInvariant (↥Sg) (↥H) K := by
    refine ⟨?_⟩
    have hforward : ∀ a : Sg, ∀ x : H, x ∈ K → a • x ∈ K := by
      intro a x hx
      have hnorm : (a : G) ∈ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) :=
        hSg_le_normKg a.2
      have hxmap : (x : G) ∈ K.map H.subtype := Subgroup.mem_map_of_mem H.subtype hx
      have hxmap' : (a : G) * (x : G) * (a : G)⁻¹ ∈ K.map H.subtype :=
        (Subgroup.mem_normalizer_iff.mp hnorm) (x : G) |>.1 hxmap
      have hxsmul : ((a • x : H) : G) ∈ K.map H.subtype := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hSg_le_normH] using hxmap'
      rcases Subgroup.mem_map.mp hxsmul with ⟨y, hy, hy_eq⟩
      have hxy : (a • x : H) = y := H.subtype_injective hy_eq.symm
      simpa [hxy] using hy
    intro a x
    constructor
    · exact hforward a x
    · intro hx
      have h :=
        hforward a⁻¹ (a • x) hx
      simpa [smul_smul] using h
  let : IsInvariant (↥Sg) (↥H) K := hK_invS
  let hKcomm_invS : IsInvariant (↥Sg) (↥K) (commutator (↥K)) :=
    isInvariant_of_characteristic (A := ↥Sg) (G := ↥K) (commutator (↥K))
  let : MulAction.QuotientAction (↥Sg) (commutator (↥K)) :=
    quotientAction_of_isInvariant (A := ↥Sg) (commutator (↥K)) hKcomm_invS
  let : MulDistribMulAction (↥Sg) (↥K ⧸ commutator (↥K)) :=
    quotientMulDistribMulAction (A := ↥Sg) (G := ↥K) (commutator (↥K)) hKcomm_invS
  let i : Sg →* MulAut (↥K ⧸ commutator (↥K)) :=
    MulDistribMulAction.toMulAut (G := ↥Sg) (M := ↥K ⧸ commutator (↥K))
  let ρ : Representation (ZMod qK) Sg (Additive (↥K ⧸ commutator (↥K))) :=
    { toFun := fun a =>
        let eAdd :
            Additive (↥K ⧸ commutator (↥K)) ≃+ Additive (↥K ⧸ commutator (↥K)) :=
          MulEquiv.toAdditive (i a)
        let eLin :
            Additive (↥K ⧸ commutator (↥K)) ≃ₗ[ZMod qK]
              Additive (↥K ⧸ commutator (↥K)) :=
          eAdd.toLinearEquiv (fun c x => by
            simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
        eLin.toLinearMap
      map_one' := by
        ext x
        apply Additive.toMul.injective
        exact one_smul (↥Sg) (Additive.toMul x)
      map_mul' := by
        intro a b
        ext x
        apply Additive.toMul.injective
        exact mul_smul a b (Additive.toMul x) }
  by_contra hfixR_bot
  have hfixRsub : ρ.fixedSubspace Rsub = ⊥ := by
    rw [Representation.fixedSubspace, Submodule.eq_bot_iff]
    intro v hv
    rw [Representation.mem_invariants] at hv
    have hvfix : Additive.toMul v ∈ fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)) := by
      rw [FixedPoints.mem_subgroup]
      intro r
      let rsub : Rsub := ⟨⟨r, Subgroup.mem_sup_right r.2⟩, by
        simp [Rsub, Subgroup.mem_subgroupOf]⟩
      have hvr : (ρ.comp Rsub.subtype) rsub v = v := hv rsub
      have : (r • (Additive.toMul v) : ↥K ⧸ commutator (↥K)) = Additive.toMul v := by
        have hvr' := congrArg Additive.toMul hvr
        change r • Additive.toMul v = Additive.toMul v at hvr'
        exact hvr'
      exact this
    have hvfix' : Additive.toMul v ∈ fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)) := hvfix
    rw [hfixR_bot] at hvfix'
    have hvone : Additive.toMul v = 1 := by simpa using hvfix'
    exact toMul_eq_one.mp hvone
  have hPsub_p : IsPGroup p Psub := by
    change IsPGroup p (normalizerSubtypeMap K P)
    exact isPGroup_normalizerSubtypeMap K P hP_p
  have hPsubg_p : IsPGroup p Psubg := by
    simpa [Psubg] using hPsub_p.map H.subtype
  have hKsub_normal : Ksub.Normal := hPsubgsub_normal
  have hPsubgR_disj : Disjoint Psubg R := by
    exact hHR.disjoint.mono_left hPsubg_le_H
  have hKsubRsub_disj : Disjoint Ksub Rsub := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hPsubgR_disj)
      (by simpa [Ksub, Subgroup.mem_subgroupOf] using hxK)
      (by simpa [Rsub, Subgroup.mem_subgroupOf] using hxR)
  have hKsub_sup_Rsub : Ksub ⊔ Rsub = ⊤ := by
    simpa [Ksub, Rsub] using hsub_sup
  have hKsub_compl : Ksub.IsComplement' Rsub := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKsubRsub_disj ?_
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hxsup : x ∈ Ksub ⊔ Rsub := by
        simp [hKsub_sup_Rsub]
      rcases (Subgroup.mem_sup_of_normal_left (s := Ksub) (t := Rsub) (x := x)).1 hxsup with
        ⟨y, hy, z, hz, rfl⟩
      exact Set.mem_mul.mpr ⟨y, hy, z, hz, rfl⟩
  have hKsub_card_eq : Nat.card Ksub = Nat.card Psubg := by
    simpa using Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := Psubg) (K := Sg) le_sup_left).toEquiv
  have hRsub_card_eq : Nat.card Rsub = Nat.card R := by
    simpa using Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := R) (K := Sg) le_sup_right).toEquiv
  have hcopPsubgR : Nat.Coprime (Nat.card Psubg) (Nat.card R) := by
    exact Nat.Coprime.of_dvd (Subgroup.card_dvd_of_le hPsubg_le_H) dvd_rfl hcopHR
  have hoddSg : Odd (Nat.card Sg) := odd_of_card_dvd hodd (Subgroup.card_subgroup_dvd_card Sg)
  have hsolvSg : Group.IsSolvable ↥Sg := by infer_instance
  have hR_prime : Nat.Prime (Nat.card R) := by simpa [hR_eq] using hR₀_prime
  have hcop_q_Psubg : Nat.Coprime qK (Nat.card Psubg) := by
    obtain ⟨n, hcardPsubg⟩ := hPsubg_p.exists_card_eq
    rw [hcardPsubg]
    exact (Nat.Prime.coprime_iff_not_dvd hqK_prime).2 (by
      intro hdiv
      exact hqK_ne_p ((Nat.prime_dvd_prime_iff_eq hqK_prime hp).1 (hqK_prime.dvd_of_dvd_pow hdiv)))
  have hcop_q_R : Nat.Coprime qK (Nat.card R) := by
    exact (Nat.Prime.coprime_iff_not_dvd hqK_prime).2 (by
      intro hdiv
      exact hqK_ne_R₀ (hR_eq ▸ (Nat.prime_dvd_prime_iff_eq hqK_prime hR_prime).1 hdiv))
  have hcharSg :
      ringChar (ZMod qK) = 0 ∨
        (Nat.Prime (ringChar (ZMod qK)) ∧ Nat.Coprime (ringChar (ZMod qK)) (Nat.card Sg)) := by
    right
    rw [ZMod.ringChar_zmod_n]
    refine ⟨hqK_prime, ?_⟩
    rw [← hKsub_compl.card_mul_card, hKsub_card_eq, hRsub_card_eq]
    exact Nat.Coprime.mul_right hcop_q_Psubg hcop_q_R
  have hcomm_sub' :
      ⁅Rsub, Ksub⁆ ≤ ρ.centralizerIn Ksub :=
    theorem_3_4 (G := ↥Sg) (F := ZMod qK) (V := Additive (↥K ⧸ commutator (↥K)))
      (K := Ksub) (R := Rsub) (ρ := ρ) hsolvSg (by simpa using hoddSg) hKsub_normal hKsub_compl
      (by simpa [hKsub_card_eq, hRsub_card_eq] using hcopPsubgR) (by simpa [hRsub_card_eq] using hR_prime)
      hcharSg hfixRsub
  have hρcent_bot : ρ.centralizerIn Ksub = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    rw [Representation.centralizerIn, Subgroup.mem_inf] at ha
    rcases ha with ⟨haKsub, haKer⟩
    let aK : Ksub := ⟨a, haKsub⟩
    have haPsubg : (((aK : Ksub) : Sg) : G) ∈ Psubg := by
      simpa [Ksub, Subgroup.mem_subgroupOf] using haKsub
    rcases Subgroup.mem_map.mp haPsubg with ⟨b, hb, hba⟩
    let bP : Psub := ⟨b, hb⟩
    have ha_eq_one : ρ (aK : Ksub) = 1 := by
      simpa [MonoidHom.mem_ker] using haKer
    have hb_fix : ∀ x : ↥K ⧸ commutator (↥K), bP • x = x := by
      intro x
      refine QuotientGroup.induction_on x ?_
      intro k
      have hkfix :
          ρ (aK : Ksub) (Additive.ofMul (((k : K) : ↥K ⧸ commutator (↥K)))) =
            Additive.ofMul (((k : K) : ↥K ⧸ commutator (↥K))) := by
        simp [ha_eq_one]
      have hkfix' :
          (((aK : Ksub) : Sg) • (((k : K) : ↥K ⧸ commutator (↥K)))) =
            (((k : K) : ↥K ⧸ commutator (↥K))) := by
        simpa [ρ, i, MulDistribMulAction.toMulAut_apply,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH, hSg_le_normH] using
          congrArg Additive.toMul hkfix
      have hbk :
          bP • k = (((aK : Ksub) : Sg) • k : K) := by
        apply Subtype.ext
        apply H.subtype_injective
        have hba' := congrArg (fun z : G => z * ((k : K) : H) * z⁻¹) hba
        have haK_smul :
            H.subtype (((((aK : Ksub) : Sg) • k : K)) : H) =
              (((aK : Ksub) : Sg) : G) * ((k : K) : H) *
                (((aK : Ksub) : Sg) : G)⁻¹ := by
          change H.subtype (((aK : Ksub) : Sg) • (k : H)) = _
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        rw [haK_smul]
        simpa [bP, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hPsub_normK] using hba'
      have hsmul_eq :
          bP • (((k : K) : ↥K ⧸ commutator (↥K))) =
            (((aK : Ksub) : Sg) • (((k : K) : ↥K ⧸ commutator (↥K)))) := by
        calc
          bP • (((k : K) : ↥K ⧸ commutator (↥K))) =
              QuotientGroup.mk' (commutator (↥K)) (bP • k) := by
                simp
          _ = QuotientGroup.mk' (commutator (↥K)) ((((aK : Ksub) : Sg) • k : K)) := by
                simp [hbk]
          _ = (((aK : Ksub) : Sg) • (((k : K) : ↥K ⧸ commutator (↥K)))) := by
                simp
      exact hsmul_eq.trans hkfix'
    have hb_one : bP = 1 := by
      exact (faithfulSMul_iff (G := ↥Psub) (α := ↥K ⧸ commutator (↥K))).1 inferInstance bP hb_fix
    apply Subtype.ext
    have hb_one' : (b : H) = 1 := congrArg Subtype.val hb_one
    have hb_one_G : (b : G) = 1 := by
      simpa using congrArg H.subtype hb_one'
    simpa [aK] using hba.symm.trans hb_one_G
  have hcomm_sub : ⁅Rsub, Ksub⁆ ≤ ⊥ := by
    intro x hx
    have hx' := hcomm_sub' hx
    rw [hρcent_bot] at hx'
    exact hx'
  have hcomm_map :
      (⁅Rsub, Ksub⁆).map Sg.subtype = ⁅R, Psubg⁆ := by
    simpa [Ksub, Rsub] using
      commutator_subgroupOf_map_eq (S := Sg) (H := Psubg) (R := R) le_sup_left le_sup_right
  have hcommRPsubg_bot : ⁅R, Psubg⁆ = ⊥ := by
    have hmap_bot : (⁅Rsub, Ksub⁆).map Sg.subtype = ⊥ := by
      simpa using (Subgroup.map_mono hcomm_sub : (⁅Rsub, Ksub⁆).map Sg.subtype ≤ (⊥ : Subgroup Sg).map Sg.subtype)
    simpa [hcomm_map] using hmap_bot
  have hcommPsubgR_bot : ⁅Psubg, R⁆ = ⊥ := by
    simpa [Subgroup.commutator_comm] using hcommRPsubg_bot
  obtain ⟨_hPsubg_eq_commR₀, hPsubg_le_commR⟩ :=
    theorem_3_6_pSubgroup_eq_commutator_with_R₀ H R R₀ p hind hsolvG hodd hHR
      hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup P hP_p hK_inv hNK_inv hPsub_inv
      hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
  have hPsubg_bot : Psubg = ⊥ := by
    apply bot_unique
    intro x hx
    have hx' : x ∈ ⁅Psubg, R⁆ := hPsubg_le_commR hx
    simpa [hcommPsubgR_bot] using hx'
  have hPsub_bot : Psub = ⊥ := by
    exact
      (Subgroup.map_eq_bot_iff_of_injective (H := Psub) (f := H.subtype) H.subtype_injective).1
        (by simpa [Psubg] using hPsubg_bot)
  exact hPK_ne_bot (by simp [Psub, hPsub_bot])

public theorem CFSG.theorem_3_6_K_fixed_not_le_commutator
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    (hK_inv : IsInvariant (↥R) (↥H) K) →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    V ⊔ normalizerOf K = ⊤ →
    V ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    R = R₀ →
    let _ : IsInvariant (↥R) (↥H) K := hK_inv
    ¬ fixedPointSubgroup (↥R) (↥K) ≤ commutator (↥K) := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
    hP_p hPK_ne_bot hproper hR_eq
  let : IsInvariant (↥R) (↥H) K := hK_inv
  let hKcomm_invR : IsInvariant (↥R) (↥K) (commutator (↥K)) :=
    isInvariant_of_characteristic (A := ↥R) (G := ↥K) (commutator (↥K))
  let : MulAction.QuotientAction (↥R) (commutator (↥K)) :=
    quotientAction_of_isInvariant (A := ↥R) (commutator (↥K)) hKcomm_invR
  let : MulDistribMulAction (↥R) (↥K ⧸ commutator (↥K)) :=
    quotientMulDistribMulAction (A := ↥R) (G := ↥K) (commutator (↥K)) hKcomm_invR
  have hfix_ne_bot :
      fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)) ≠ ⊥ :=
    theorem_3_6_K_quotient_commutator_r_fixed_ne_bot H R R₀ p hind hsolvG hodd hHR
      hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hNK_inv
      hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper hR_eq
  have hcopRK : Nat.Coprime (Nat.card R) (Nat.card K) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card K) hcopHR.symm
  have hsolvK : Group.IsSolvable ↥K := by infer_instance
  have hfixed_quot :
      fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)) =
        (fixedPointSubgroup (↥R) (↥K)).map (QuotientGroup.mk' (commutator (↥K))) := by
    simpa using
      proposition_1_5_d (G := ↥K) (A := ↥R) hsolvK hcopRK (π := ∅) (commutator (↥K))
        hKcomm_invR
  intro hle
  have hmap_bot :
      (fixedPointSubgroup (↥R) (↥K)).map (QuotientGroup.mk' (commutator (↥K))) = ⊥ := by
    exact
      (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' (commutator (↥K)))
        (H := fixedPointSubgroup (↥R) (↥K))).2 (by simpa using hle)
  have hfix_bot : fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)) = ⊥ := by
    simpa [hfixed_quot] using hmap_bot
  exact hfix_ne_bot hfix_bot

public theorem CFSG.theorem_3_6_K_fixed_card_eq_q_and_inf_commutator_eq_bot
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    (hK_inv : IsInvariant (↥R) (↥H) K) →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    V ⊔ normalizerOf K = ⊤ →
    V ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    R = R₀ →
    let _ : IsInvariant (↥R) (↥H) K := hK_inv
    ∃ qK : ℕ,
      Nat.Prime qK ∧
        Nat.card (fixedPointSubgroup (↥R) (↥K)) = qK ∧
        fixedPointSubgroup (↥R) (↥K) ⊓ commutator (↥K) = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
    hP_p hPK_ne_bot hproper hR_eq
  let : IsInvariant (↥R) (↥H) K := hK_inv
  let Cfix : Subgroup K := fixedPointSubgroup (↥R) (↥K)
  obtain ⟨qK, hqK_prime, _, _, hqK_pgroup, _, hexpK⟩ :=
    theorem_3_6_K_class_two_exponent_q H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit
      hCH_le_K hP_p hPK_ne_bot hproper
  have hfix_not_le : ¬ Cfix ≤ commutator (↥K) :=
    theorem_3_6_K_fixed_not_le_commutator H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv
      hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper hR_eq
  have hCfix_ne_bot : Cfix ≠ ⊥ := by
    intro hbot
    apply hfix_not_le
    simp [Cfix, hbot]
  let f : Cfix →* subgroupCentralizerIn H R₀ :=
    { toFun := fun x =>
        let xK : K := x.1
        have hx_centR : ((xK : H) : G) ∈ subgroupCentralizerIn H R := by
          refine ⟨(xK : H).2, ?_⟩
          change ((xK : H) : G) ∈ Subgroup.centralizer (R : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro r hrR
          have hxfix : (⟨r, hrR⟩ : R) • xK = xK := x.2 ⟨r, hrR⟩
          have hxfixH : ((⟨r, hrR⟩ : R) • (xK : H) : H) = (xK : H) := by
            exact congrArg Subtype.val hxfix
          have hxconj : (r : G) * ((xK : H) : G) * (r : G)⁻¹ = ((xK : H) : G) := by
            simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH] using
              congrArg H.subtype hxfixH
          have := congrArg (fun t : G => t * (r : G)) hxconj
          simpa [mul_assoc] using this
        have hx_centR₀ : ((xK : H) : G) ∈ subgroupCentralizerIn H R₀ := by
          simpa [hR_eq] using hx_centR
        ⟨((xK : H) : G), hx_centR₀⟩
      map_one' := rfl
      map_mul' := by intro x y; rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val hxy
  let : IsZGroup ↥Cfix := IsZGroup.of_injective (f := f) hf
  have : Fact qK.Prime := ⟨hqK_prime⟩
  have hCfix_q : IsPGroup qK Cfix := by
    exact hqK_pgroup.of_injective (Cfix.subtype) Cfix.subtype_injective
  let : Group.IsNilpotent ↥Cfix := hCfix_q.isNilpotent
  have hCfix_cyclic : IsCyclic ↥Cfix := by infer_instance
  have hCfix_card_ne_one : Nat.card Cfix ≠ 1 := by
    intro hcard
    exact hCfix_ne_bot ((Subgroup.card_eq_one (H := Cfix)).1 hcard)
  obtain ⟨x, hxorder⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Cfix)
  have hxpowK : ((x : Cfix) : K) ^ qK = 1 := by
    exact
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent (↥K) ∣ qK by simp [hexpK]) ((x : Cfix) : K)
  have hxpow : x ^ qK = 1 := by
    exact Cfix.subtype_injective (by simpa using hxpowK)
  have horder_dvd_q : orderOf x ∣ qK := orderOf_dvd_of_pow_eq_one hxpow
  have hxorder_ne_one : orderOf x ≠ 1 := by
    simpa [hxorder] using hCfix_card_ne_one
  have horder_eq_q : orderOf x = qK := by
    exact (hqK_prime.eq_one_or_self_of_dvd (orderOf x) horder_dvd_q).resolve_left hxorder_ne_one
  have hCfix_card : Nat.card Cfix = qK := by
    calc
      Nat.card Cfix = orderOf x := hxorder.symm
      _ = qK := horder_eq_q
  have hCfix_prime : Nat.Prime (Nat.card Cfix) := by
    simpa [hCfix_card] using hqK_prime
  have hCfix_inf_bot : Cfix ⊓ commutator (↥K) = ⊥ := by
    apply bot_unique
    intro y hy
    rcases hy with ⟨hyC, hycomm⟩
    by_contra hy_ne_one
    let yC : Cfix := ⟨y, hyC⟩
    have hyC_ne_one : yC ≠ 1 := by
      intro hyC_one
      exact hy_ne_one (by simpa [yC] using congrArg Subtype.val hyC_one)
    have hyz_top : Subgroup.zpowers yC = ⊤ :=
      zpowers_eq_top_of_prime_card_of_ne_one hCfix_prime hyC_ne_one
    have htop_map : (⊤ : Subgroup Cfix).map Cfix.subtype = Cfix := by
      ext z
      constructor
      · rintro ⟨w, -, rfl⟩
        exact w.2
      · intro hz
        exact ⟨⟨z, hz⟩, by simp, rfl⟩
    have hCfix_eq_zpowers : Cfix = Subgroup.zpowers y := by
      calc
        Cfix = (⊤ : Subgroup Cfix).map Cfix.subtype := htop_map.symm
        _ = (Subgroup.zpowers yC).map Cfix.subtype := by rw [hyz_top]
        _ = Subgroup.zpowers y := by
              simp [yC]
    have hCfix_le_comm : Cfix ≤ commutator (↥K) := by
      calc
        Cfix = Subgroup.zpowers y := hCfix_eq_zpowers
        _ ≤ commutator (↥K) := (Subgroup.zpowers_le).2 hycomm
    exact hfix_not_le hCfix_le_comm
  exact ⟨qK, hqK_prime, hCfix_card, hCfix_inf_bot⟩

public theorem CFSG.theorem_3_6_K_commutatorAction_proper
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    (hK_inv : IsInvariant (↥R) (↥H) K) →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    V ⊔ normalizerOf K = ⊤ →
    V ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    R = R₀ →
    let _ : IsInvariant (↥R) (↥H) K := hK_inv
    fixedPointSubgroup (↥R) (↥K) ⊓ commutatorAction (A := ↥R) (G := ↥K) = ⊥ ∧
      commutatorAction (A := ↥R) (G := ↥K) ≠ ⊤ := by
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
    hP_p hPK_ne_bot hproper hR_eq
  let : IsInvariant (↥R) (↥H) K := hK_inv
  let Cfix : Subgroup K := fixedPointSubgroup (↥R) (↥K)
  let Kcomm : Subgroup K := commutatorAction (A := ↥R) (G := ↥K)
  let hKcomm_invR : IsInvariant (↥R) (↥K) (commutator (↥K)) :=
    isInvariant_of_characteristic (A := ↥R) (G := ↥K) (commutator (↥K))
  let : MulAction.QuotientAction (↥R) (commutator (↥K)) :=
    quotientAction_of_isInvariant (A := ↥R) (commutator (↥K)) hKcomm_invR
  let : MulDistribMulAction (↥R) (↥K ⧸ commutator (↥K)) :=
    quotientMulDistribMulAction (A := ↥R) (G := ↥K) (commutator (↥K)) hKcomm_invR
  obtain ⟨qK, hqK_prime, hCfix_card, hCfix_inf_bot⟩ :=
    theorem_3_6_K_fixed_card_eq_q_and_inf_commutator_eq_bot H R R₀ p hind hsolvG hodd
      hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj
      hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K hP_p hPK_ne_bot
      hproper hR_eq
  have hCfix_ne_bot : Cfix ≠ ⊥ := by
    intro hCfix_bot
    have hcard_one : Nat.card Cfix = 1 := by
      simp [hCfix_bot]
    exact hqK_prime.ne_one (hCfix_card.symm.trans hcard_one)
  have hfixQ_ne_bot :
      fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)) ≠ ⊥ :=
    theorem_3_6_K_quotient_commutator_r_fixed_ne_bot H R R₀ p hind hsolvG hodd
      hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hNK_inv
      hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper hR_eq
  have hcopRK : Nat.Coprime (Nat.card R) (Nat.card K) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card K) hcopHR.symm
  have hcopRQ :
      Nat.Coprime (Nat.card R) (Nat.card (↥K ⧸ commutator (↥K))) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_quotient_dvd_card (s := commutator (↥K))) hcopRK
  have hsolvQ : Group.IsSolvable (↥K ⧸ commutator (↥K)) := by infer_instance
  let qcomm : ↥K →* (↥K ⧸ commutator (↥K)) := QuotientGroup.mk' (commutator (↥K))
  have hfixQ_eq' :
      fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)) = Cfix.map qcomm := by
    have hsolvK : Group.IsSolvable ↥K := by infer_instance
    simpa [Cfix, qcomm] using
      proposition_1_5_d (G := ↥K) (A := ↥R) hsolvK hcopRK (π := ∅)
        (commutator (↥K)) hKcomm_invR
  have hQcomm : IsMulCommutative (↥K ⧸ commutator (↥K)) := by
    exact
      (Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := commutator (↥K))).mpr le_rfl
  have hcomplQ :
      IsCompl (fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)))
        (commutatorAction (A := ↥R) (G := ↥K ⧸ commutator (↥K))) :=
    proposition_1_6_d (G := ↥K ⧸ commutator (↥K)) (A := ↥R)
      (by have : Group.IsSolvable G := hsolvG; infer_instance) hcopRQ hQcomm
  have hfixQ_inf_bot :
      fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)) ⊓
        commutatorAction (A := ↥R) (G := ↥K ⧸ commutator (↥K)) = ⊥ :=
    hcomplQ.inf_eq_bot
  have hmap_le :
      Kcomm.map qcomm ≤ commutatorAction (A := ↥R) (G := ↥K ⧸ commutator (↥K)) := by
    let S : Set K := {x : K | ∃ a : R, ∃ g : K, x = g⁻¹ * (a • g)}
    let T : Set (↥K ⧸ commutator (↥K)) :=
      {x : ↥K ⧸ commutator (↥K) | ∃ a : R, ∃ g : ↥K ⧸ commutator (↥K), x = g⁻¹ * (a • g)}
    have hS : Kcomm = Subgroup.closure S := by
      simpa [Kcomm, S] using (commutatorAction_eq_closure (G := ↥K) (A := ↥R))
    have hT :
        commutatorAction (A := ↥R) (G := ↥K ⧸ commutator (↥K)) = Subgroup.closure T := by
      simpa [T] using
        (commutatorAction_eq_closure (G := ↥K ⧸ commutator (↥K)) (A := ↥R))
    rw [hS, hT]
    have hmap :
        (Subgroup.closure S).map qcomm = Subgroup.closure (qcomm '' S) := by
      simpa [qcomm] using (MonoidHom.map_closure (f := qcomm) S)
    rw [hmap]
    refine (Subgroup.closure_le (K := Subgroup.closure T)).2 ?_
    intro x hx
    rcases hx with ⟨y, hyS, rfl⟩
    rcases hyS with ⟨a, g, rfl⟩
    refine Subgroup.subset_closure ?_
    refine ⟨a, qcomm g, ?_⟩
    simp [qcomm]
  have hfix_inf_Kcomm_bot : Cfix ⊓ Kcomm = ⊥ := by
    apply bot_unique
    intro y hy
    rcases hy with ⟨hyC, hyKcomm⟩
    have hyfixQ : qcomm y ∈ fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)) := by
      rw [hfixQ_eq']
      exact Subgroup.mem_map_of_mem qcomm hyC
    have hycommQ : qcomm y ∈ commutatorAction (A := ↥R) (G := ↥K ⧸ commutator (↥K)) := by
      exact hmap_le (Subgroup.mem_map_of_mem qcomm hyKcomm)
    have hybotQ : qcomm y ∈ (⊥ : Subgroup (↥K ⧸ commutator (↥K))) := by
      have hyinfQ :
          qcomm y ∈ fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)) ⊓
            commutatorAction (A := ↥R) (G := ↥K ⧸ commutator (↥K)) :=
        ⟨hyfixQ, hycommQ⟩
      simpa [hfixQ_inf_bot] using hyinfQ
    have hycomm : y ∈ commutator (↥K) := by
      have hy_eq_one : qcomm y = 1 := by simpa using hybotQ
      exact (QuotientGroup.eq_one_iff (N := commutator (↥K)) (x := y)).1 hy_eq_one
    have hybot : y ∈ (⊥ : Subgroup K) := by
      have hyinf : y ∈ Cfix ⊓ commutator (↥K) := ⟨hyC, hycomm⟩
      rw [hCfix_inf_bot] at hyinf
      exact hyinf
    simpa using hybot
  have hKcomm_ne_top : Kcomm ≠ ⊤ := by
    intro hKcomm_top
    have hmap_top : Kcomm.map qcomm = ⊤ := by
      rw [hKcomm_top]
      simpa [qcomm] using
        (Subgroup.map_top_of_surjective (f := qcomm)
          (QuotientGroup.mk'_surjective (N := commutator (↥K))))
    have hcommQ_top : commutatorAction (A := ↥R) (G := ↥K ⧸ commutator (↥K)) = ⊤ := by
      apply top_unique
      simpa [hmap_top] using hmap_le
    have hfixQ_bot : fixedPointSubgroup (↥R) (↥K ⧸ commutator (↥K)) = ⊥ := by
      simpa [hcommQ_top] using hfixQ_inf_bot
    exact hfixQ_ne_bot hfixQ_bot
  exact ⟨hfix_inf_Kcomm_bot, hKcomm_ne_top⟩

public theorem CFSG.theorem_3_6_K_commutatorAction_abelian
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    (hK_inv : IsInvariant (↥R) (↥H) K) →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    V ⊔ normalizerOf K = ⊤ →
    V ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    R = R₀ →
    let _ : IsInvariant (↥R) (↥H) K := hK_inv
    IsMulCommutative ↥(commutatorAction (A := ↥R) (G := ↥K)) := by
  set_option maxHeartbeats 800000 in
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
    hP_p hPK_ne_bot hproper hR_eq
  let V : Subgroup H := fittingSubgroup H
  let Kg : Subgroup G := K.map H.subtype
  let KR : Subgroup G := Kg ⊔ R
  let Vg : Subgroup G := V.map H.subtype
  let Kcomm : Subgroup K := commutatorAction (A := ↥R) (G := ↥K)
  let f : K →* G := H.subtype.comp K.subtype
  let Kcommg : Subgroup G := Kcomm.map f
  let Kcommsub : Subgroup KR := Kcommg.subgroupOf KR
  let RsubKR : Subgroup KR := R.subgroupOf KR
  let S : Subgroup KR := Kcommsub ⊔ RsubKR
  let Ksub : Subgroup S := Kcommsub.subgroupOf S
  let Rsub : Subgroup S := RsubKR.subgroupOf S
  let : IsInvariant (↥R) (↥H) K := hK_inv
  have hf : Function.Injective f := by
    intro x y hxy
    apply K.subtype_injective
    apply H.subtype_injective
    simpa [f] using hxy
  have hKcommg_le_Kg : Kcommg ≤ Kg := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact Subgroup.mem_map_of_mem H.subtype (show ((y : K) : H) ∈ K from (y : K).2)
  have hKcommg_le_H : Kcommg ≤ H := hKcommg_le_Kg.trans (by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2)
  have hKcommg_le_KR : Kcommg ≤ KR := hKcommg_le_Kg.trans le_sup_left
  have hV_char : V.Characteristic := by
    dsimp [V]
    infer_instance
  let : V.Characteristic := hV_char
  have hVg_normal : Vg.Normal := by
    dsimp [Vg, V]
    exact ConjAct.normal_of_characteristic_of_normal
  have hRnormKg : R ≤ Subgroup.normalizer (Kg : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyK, rfl⟩
      have hy' : (⟨a, ha⟩ : R) • y ∈ K :=
        (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := K) ⟨a, ha⟩ y).1 hyK
      exact Subgroup.mem_map_of_mem H.subtype hy'
    · intro hx
      have ha_inv : a⁻¹ ∈ R := R.inv_mem ha
      rcases Subgroup.mem_map.mp hx with ⟨y, hyK, hyx⟩
      have hy' : (⟨a⁻¹, ha_inv⟩ : R) • y ∈ K :=
        (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := K) ⟨a⁻¹, ha_inv⟩ y).1 hyK
      refine Subgroup.mem_map.mpr ?_
      refine ⟨(⟨a⁻¹, ha_inv⟩ : R) • y, hy', ?_⟩
      have hyx' : (↑y * a : G) = (a * x * a⁻¹) * a := by
        simpa [mul_assoc] using congrArg (fun z : G => z * a) hyx
      calc
        H.subtype ((⟨a⁻¹, ha_inv⟩ : R) • y) = a⁻¹ * (↑y * a) := by
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
        _ = a⁻¹ * ((a * x * a⁻¹) * a) := by
          exact congrArg (fun z : G => a⁻¹ * z) hyx'
        _ = x := by simp [mul_assoc]
  have : Subgroup.Normalizes R Kg := ⟨hRnormKg⟩
  have hKcomm_invR : IsInvariant (↥R) (↥K) Kcomm :=
    commutatorAction_isInvariant (G := ↥K) (A := ↥R)
  have hRnormKcommg : R ≤ Subgroup.normalizer (Kcommg : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem Kcommg R ?_
    intro a x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hy' : a • y ∈ Kcomm :=
      (IsInvariant.invariant (A := ↥R) (G := ↥K) (H := Kcomm) a y).1 hy
    exact Subgroup.mem_map_of_mem f hy'
  have hKcommsub_normal : Ksub.Normal := by
    have hS_le_normKcommsub : S ≤ Subgroup.normalizer (Kcommsub : Set KR) := by
      rw [show S = Kcommsub ⊔ RsubKR by rfl]
      refine sup_le Kcommsub.le_normalizer ?_
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have haR : ((a : KR) : G) ∈ R := by
        simpa [RsubKR, KR, Subgroup.mem_subgroupOf] using ha
      constructor
      · intro hx
        have hx' : ((x : KR) : G) ∈ Kcommg := by
          simpa [Kcommsub, Subgroup.mem_subgroupOf] using hx
        have hconj : ((a : KR) : G) * ((x : KR) : G) * (((a : KR) : G))⁻¹ ∈ Kcommg :=
          ((Subgroup.mem_normalizer_iff.mp (hRnormKcommg haR)) (((x : KR) : G))).1 hx'
        simpa [Kcommsub, Subgroup.mem_subgroupOf] using hconj
      · intro hx
        have hx' : ((a : KR) : G) * ((x : KR) : G) * (((a : KR) : G))⁻¹ ∈ Kcommg := by
          simpa [Kcommsub, Subgroup.mem_subgroupOf] using hx
        have hx'' : ((x : KR) : G) ∈ Kcommg :=
          ((Subgroup.mem_normalizer_iff.mp (hRnormKcommg haR)) (((x : KR) : G))).2 hx'
        simpa [Kcommsub, Subgroup.mem_subgroupOf] using hx''
    simpa [Ksub, S] using
      (Subgroup.normal_subgroupOf_of_le_normalizer (H := S) (N := Kcommsub) hS_le_normKcommsub)
  have hKcommgR_disj : Disjoint Kcommg R := (hHR.disjoint.mono_left hKcommg_le_H)
  have hKcommsubRsubKR_disj : Disjoint Kcommsub RsubKR := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hKcommgR_disj)
      (by simpa [Kcommsub, Subgroup.mem_subgroupOf] using hxK)
      (by simpa [RsubKR, KR, Subgroup.mem_subgroupOf] using hxR)
  have hKsubRsub_disj : Disjoint Ksub Rsub := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hKcommsubRsubKR_disj)
      (by simpa [Ksub, Subgroup.mem_subgroupOf] using hxK)
      (by simpa [Rsub, Subgroup.mem_subgroupOf] using hxR)
  have hsub_sup : Ksub ⊔ Rsub = ⊤ := by
    calc
      Ksub ⊔ Rsub = (Kcommsub ⊔ RsubKR).subgroupOf S := by
        symm
        exact Subgroup.subgroupOf_sup (A := Kcommsub) (A' := RsubKR) (B := S) le_sup_left le_sup_right
      _ = ⊤ := by simp [S]
  have hKsub_compl : Ksub.IsComplement' Rsub := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKsubRsub_disj ?_
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hxsup : x ∈ Ksub ⊔ Rsub := by simp [hsub_sup]
      rcases (Subgroup.mem_sup_of_normal_left (s := Ksub) (t := Rsub) (x := x)).1 hxsup with
        ⟨y, hy, z, hz, rfl⟩
      exact Set.mem_mul.mpr ⟨y, hy, z, hz, rfl⟩
  have hcomm_KgR_le_Kcommg : ⁅Kg, R⁆ ≤ Kcommg := by
    let Sgen : Set K := {x : K | ∃ a : R, ∃ g : K, x = g⁻¹ * (a • g)}
    have hKcomm_def : Kcomm = Subgroup.closure Sgen := by
      simpa [Kcomm, Sgen] using (commutatorAction_eq_closure (G := ↥K) (A := ↥R))
    refine (Subgroup.commutator_le).2 ?_
    intro x hx y hy
    rcases Subgroup.mem_map.mp hx with ⟨g, hg, rfl⟩
    let gK : K := ⟨g, hg⟩
    have hgen : gK * ((⟨y, hy⟩ : R) • gK)⁻¹ ∈ Kcomm := by
      rw [hKcomm_def]
      refine Subgroup.subset_closure ?_
      refine ⟨⟨y, hy⟩, gK⁻¹, ?_⟩
      apply Subtype.ext
      simp [gK]
    have hcomm :
        ⁅H.subtype gK, y⁆ = f (gK * ((⟨y, hy⟩ : R) • gK)⁻¹) := by
      have hsmul : (((⟨y, hy⟩ : R) • gK : K) : G) = y * (g : G) * y⁻¹ := by
        change H.subtype (((⟨y, hy⟩ : R) • (g : H) : H)) = y * (g : G) * y⁻¹
        simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      simp [f, gK, commutatorElement_def, hsmul, mul_assoc]
    exact hcomm ▸ Subgroup.mem_map_of_mem f hgen
  have hKcommg_ne_bot : Kcommg ≠ ⊥ := by
    intro hbot
    have hcommKgR_bot : ⁅Kg, R⁆ = ⊥ := by
      apply bot_unique
      intro x hx
      have hx' : x ∈ Kcommg := hcomm_KgR_le_Kcommg hx
      simpa [hbot] using hx'
    exact
      (theorem_3_6_r0_commutator_nontrivial H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup hVinfNK_bot
        hKsub_fit hCH_le_K) (by simpa [Kg, hR_eq] using hcommKgR_bot)
  have hKcommsub_ne : Kcommsub ≠ ⊥ := by
    intro hbot
    apply hKcommg_ne_bot
    have hcard : Nat.card Kcommsub = 1 := (Subgroup.eq_bot_iff_card (H := Kcommsub)).1 hbot
    have hcard' : Nat.card Kcommg = 1 := by
      simpa [Kcommsub, natCard_subgroupOf_eq Kcommg KR hKcommg_le_KR] using hcard
    exact (Subgroup.eq_bot_iff_card (H := Kcommg)).2 hcard'
  have hKsub_ne : Ksub ≠ ⊥ := by
    intro hbot
    apply hKcommsub_ne
    have hcard : Nat.card Ksub = 1 := (Subgroup.eq_bot_iff_card (H := Ksub)).1 hbot
    have hcard' : Nat.card Kcommsub = 1 := by
      simpa [Ksub, natCard_subgroupOf_eq Kcommsub S le_sup_left] using hcard
    exact (Subgroup.eq_bot_iff_card (H := Kcommsub)).2 hcard'
  have hRsubKR_ne : RsubKR ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card RsubKR = 1 := (Subgroup.eq_bot_iff_card (H := RsubKR)).1 hbot
    have hcard' : Nat.card R = 1 := by
      simpa [RsubKR, natCard_subgroupOf_eq R KR le_sup_right] using hcard
    have hcardR₀ : Nat.card R₀ = 1 := by
      simpa [hR_eq] using hcard'
    exact hR₀_prime.ne_one hcardR₀
  have hRsub_ne : Rsub ≠ ⊥ := by
    intro hbot
    apply hRsubKR_ne
    have hcard : Nat.card Rsub = 1 := (Subgroup.eq_bot_iff_card (H := Rsub)).1 hbot
    have hcard' : Nat.card RsubKR = 1 := by
      simpa [Rsub, natCard_subgroupOf_eq RsubKR S le_sup_right] using hcard
    exact (Subgroup.eq_bot_iff_card (H := RsubKR)).2 hcard'
  have hKcomm_centR_bot : subgroupCentralizerIn Kcommg R = ⊥ := by
    have hfix_inf_bot :
        fixedPointSubgroup (↥R) (↥K) ⊓ Kcomm = ⊥ := by
      exact
        (theorem_3_6_K_commutatorAction_proper H R R₀ p hind hsolvG hodd hHR hcopHR
          hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv
          hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper hR_eq).1
    apply bot_unique
    intro x hx
    rcases Subgroup.mem_map.mp hx.1 with ⟨y, hyKcomm, hyx⟩
    have hyfix : y ∈ fixedPointSubgroup (↥R) (↥K) := by
      rw [FixedPoints.mem_subgroup]
      intro a
      have hcomm : (a : G) * H.subtype (y : H) = H.subtype (y : H) * (a : G) := by
        change (a : G) * f y = f y * (a : G)
        simpa [hyx] using (Subgroup.mem_centralizer_iff.mp hx.2) a a.2
      have hyconj : (a : G) * H.subtype (y : H) * (a : G)⁻¹ = H.subtype (y : H) := by
        calc
          (a : G) * H.subtype (y : H) * (a : G)⁻¹ =
              (H.subtype (y : H) * (a : G)) * (a : G)⁻¹ := by rw [hcomm]
          _ = H.subtype (y : H) := by simp [mul_assoc]
      apply hf
      change (a : G) * H.subtype (y : H) * (a : G)⁻¹ = H.subtype (y : H)
      simpa [f, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH] using hyconj
    have hybot : y ∈ (⊥ : Subgroup K) := by
      have hyinf : y ∈ fixedPointSubgroup (↥R) (↥K) ⊓ Kcomm := ⟨hyfix, hyKcomm⟩
      simpa [hfix_inf_bot] using hyinf
    have hyone : y = 1 := by simpa using hybot
    have hxone : x = 1 := by simpa [hyx, f] using congrArg f hyone
    simp [hxone]
  have hR_prime : Nat.Prime (Nat.card R) := by simpa [hR_eq] using hR₀_prime
  have hcent :
      ∀ x : Rsub, x ≠ 1 → elementCentralizerIn Ksub (x : S) = ⊥ := by
    rintro ⟨x, hxRsub⟩ hx
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rcases hy with ⟨hyKsub, hyC⟩
    have hyKcommg' : (((y : S) : KR) : G) ∈ Kcommg := by
      simpa [Ksub, Kcommsub, Subgroup.mem_subgroupOf] using hyKsub
    have hxRsubKR : ((x : S) : KR) ∈ RsubKR := by
      change x ∈ RsubKR.subgroupOf S at hxRsub ⊢
      exact hxRsub
    let xR : R := ⟨(((x : S) : KR) : G), by
      simpa [RsubKR, KR, Subgroup.mem_subgroupOf] using hxRsubKR⟩
    have hxR_ne : xR ≠ 1 := by
      intro hxR_one
      apply hx
      apply Subtype.ext
      apply Subtype.ext
      simpa [xR] using congrArg Subtype.val hxR_one
    have hz_top : Subgroup.zpowers xR = ⊤ :=
      zpowers_eq_top_of_prime_card_of_ne_one hR_prime hxR_ne
    have hycentR : (((y : S) : KR) : G) ∈ subgroupCentralizerIn Kcommg R := by
      refine ⟨hyKcommg', ?_⟩
      change (((y : S) : KR) : G) ∈ Subgroup.centralizer (R : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro r hrR
      have hcommx :
          Commute (((y : S) : KR) : G) (xR : G) := by
        have hcommS : (y : S) * x = x * (y : S) :=
          Subgroup.mem_centralizer_singleton_iff.mp hyC
        have hcommKR : ((y : S) : KR) * (x : S) = (x : S) * ((y : S) : KR) := by
          exact congrArg Subtype.val hcommS
        change (((y : S) : KR) : G) * (xR : G) = (xR : G) * (((y : S) : KR) : G)
        simpa [xR] using congrArg Subtype.val hcommKR
      have hrz : (⟨r, hrR⟩ : R) ∈ Subgroup.zpowers xR := by
        have : (⟨r, hrR⟩ : R) ∈ (⊤ : Subgroup R) := by simp
        rw [← hz_top] at this
        exact this
      rcases hrz with ⟨n, hn⟩
      have hnG : (r : G) = (xR : G) ^ n := by
        simpa [xR] using congrArg Subtype.val hn.symm
      simpa [hnG, Commute] using (hcommx.zpow_right n).eq.symm
    have hybot : (((y : S) : KR) : G) ∈ (⊥ : Subgroup G) := by
      rw [hKcomm_centR_bot] at hycentR
      exact hycentR
    have hyone : y = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hybot
    simp [hyone]
  have hfrob : IsFrobeniusGroupWithKernelComplement Ksub Rsub :=
    (lemma_3_1 (G := S) (K := Ksub) (R := Rsub) hKsub_ne hRsub_ne hKcommsub_normal hKsub_compl).2
      hcent
  have hKg_card_eq : Nat.card Kg = Nat.card K := by
    simpa [Kg] using
      (Subgroup.card_map_of_injective (K := K) (f := H.subtype) H.subtype_injective)
  have hp_dvd_H : p ∣ Nat.card H := by
    by_contra hp_ndvd_H
    exact hbad <|
      hasPLengthOne_of_coprime_card (p := p) ((hp.coprime_iff_not_dvd).2 hp_ndvd_H)
  have hcop_p_R : Nat.Coprime p (Nat.card R) := Nat.Coprime.of_dvd_left hp_dvd_H hcopHR
  have hcop_p_K : Nat.Coprime p (Nat.card K) :=
    theorem_3_6_complement_card_coprime H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_disj hVK_sup
  have hcop_p_Kg : Nat.Coprime p (Nat.card Kg) := by
    rw [hKg_card_eq]
    exact hcop_p_K
  have hcop_p_Kcommg : Nat.Coprime p (Nat.card Kcommg) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hKcommg_le_Kg) hcop_p_Kg
  have hKRg_disj : Disjoint Kg R := by
    rw [Subgroup.disjoint_def]
    intro x hxKg hxR
    rcases Subgroup.mem_map.mp hxKg with ⟨y, hyK, rfl⟩
    exact (Subgroup.disjoint_def.mp hHR.disjoint) y.2 hxR
  let Kgsub : Subgroup KR := Kg.subgroupOf KR
  have hKgsub_normal : Kgsub.Normal := by
    have hKR_le_normKg : KR ≤ Subgroup.normalizer (Kg : Set G) := by
      exact sup_le Kg.le_normalizer hRnormKg
    simpa [Kgsub, KR] using
      (Subgroup.normal_subgroupOf_of_le_normalizer (H := KR) (N := Kg) hKR_le_normKg)
  have hKgsubRsubKR_disj : Disjoint Kgsub RsubKR := by
    rw [Subgroup.disjoint_def]
    intro x hxKg hxR
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hKRg_disj)
      (by simpa [Kgsub, Subgroup.mem_subgroupOf] using hxKg)
      (by simpa [RsubKR, KR, Subgroup.mem_subgroupOf] using hxR)
  have hKgsub_sup_RsubKR : Kgsub ⊔ RsubKR = ⊤ := by
    calc
      Kgsub ⊔ RsubKR = (Kg ⊔ R).subgroupOf KR := by
        symm
        exact Subgroup.subgroupOf_sup (A := Kg) (A' := R) (B := KR) le_sup_left le_sup_right
      _ = ⊤ := by simp [KR]
  have hRsubKR_compl : RsubKR.IsComplement' Kgsub := by
    let : Kgsub.Normal := hKgsub_normal
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKgsubRsubKR_disj.symm ?_
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hxsup' : x ∈ Kgsub ⊔ RsubKR := by simp [hKgsub_sup_RsubKR]
      have hxsup : x ∈ RsubKR ⊔ Kgsub := by simpa [sup_comm] using hxsup'
      rcases (Subgroup.mem_sup_of_normal_right (s := RsubKR) (t := Kgsub) (x := x)).1 hxsup with
        ⟨r, hr, k, hk, rfl⟩
      exact Set.mem_mul.mpr ⟨r, hr, k, hk, rfl⟩
  have hRsubKR_card_eq : Nat.card RsubKR = Nat.card R := by
    simpa using Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := R) (K := KR) le_sup_right).toEquiv
  have hKgsub_card_eq : Nat.card Kgsub = Nat.card Kg := by
    simpa using Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := Kg) (K := KR) le_sup_left).toEquiv
  have hcop_p_KR : Nat.Coprime p (Nat.card KR) := by
    rw [← hRsubKR_compl.card_mul_card, hRsubKR_card_eq, hKgsub_card_eq]
    exact Nat.Coprime.mul_right hcop_p_R hcop_p_Kg
  have hcharKR :
      ringChar (ZMod p) = 0 ∨
        (Nat.Prime (ringChar (ZMod p)) ∧ Nat.Coprime (ringChar (ZMod p)) (Nat.card KR)) := by
    right
    rw [ZMod.ringChar_zmod_n]
    exact ⟨hp, hcop_p_KR⟩
  have hcharS :
      ringChar (ZMod p) = 0 ∨
        (Nat.Prime (ringChar (ZMod p)) ∧ Nat.Coprime (ringChar (ZMod p)) (Nat.card S)) :=
    hchar_of_card_dvd (G := KR) (F := ZMod p) hcharKR (Subgroup.card_subgroup_dvd_card S)
  have hKRnormVg : KR ≤ Subgroup.normalizer Vg := Subgroup.le_normalizer_of_normal (H := Vg)
  have : Subgroup.Normalizes KR Vg := ⟨hKRnormVg⟩
  have hV_elem : IsElementaryAbelian p ↥V := by
    simpa [V] using
      theorem_3_6_fitting_elementaryAbelian H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  let : IsElementaryAbelian p ↥V := hV_elem
  have hVg_elem : IsElementaryAbelian p ↥Vg := by
    refine
      { toIsMulCommutative := by infer_instance
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    rcases Subgroup.mem_map.mp x.2 with ⟨y, hyV, hyx⟩
    let yV : V := ⟨y, hyV⟩
    have hy_pow : yV ^ p = 1 := by
      exact
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p ↥V) yV
    have hy_pow_G : ((((yV : V) : H) : G) ^ p) = 1 := by
      simpa using congrArg H.subtype (congrArg Subtype.val hy_pow)
    have hx_eq : ((x : Vg) : G) = (((yV : V) : H) : G) := by
      simpa [yV] using hyx.symm
    calc
      ((x : Vg) : G) ^ p = (((yV : V) : H) : G) ^ p := by simp [hx_eq]
      _ = 1 := hy_pow_G
  let : IsElementaryAbelian p ↥Vg := hVg_elem
  let : CommGroup Vg := IsMulCommutative.instCommGroup
  let ψ : KR →* MulAut Vg := MulDistribMulAction.toMulAut (G := ↥KR) (M := ↥Vg)
  let ρKR : Representation (ZMod p) KR (Additive Vg) := {
    toFun := fun a =>
      let eAdd : Additive Vg ≃+ Additive Vg := MulEquiv.toAdditive (ψ a)
      let eLin : Additive Vg ≃ₗ[ZMod p] Additive Vg :=
        eAdd.toLinearEquiv (fun c x => by
          simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
      eLin.toLinearMap
    map_one' := by
      ext x
      apply Additive.toMul.injective
      simp [ψ, MulDistribMulAction.toMulAut]
    map_mul' := by
      intro a b
      ext x
      apply Additive.toMul.injective
      simp [ψ, MulDistribMulAction.toMulAut, smul_smul] }
  have hψker :
      ψ.ker = actionCentralizerIn (A := ↥KR) (G := ↥Vg) (⊤ : Subgroup KR) := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      refine ⟨by simp, ?_⟩
      refine (mem_fixingSubgroup_iff (M := ↥KR) (s := (Set.univ : Set Vg))).2 ?_
      intro v _
      have hv : ψ x v = v := by
        simpa [ψ, MulDistribMulAction.toMulAut_apply] using DFunLike.congr_fun hx v
      exact hv
    · intro hx
      change ψ x = 1
      ext v
      have hxfix : x ∈ fixingSubgroupOf (↥KR) (↥Vg) (Set.univ : Set Vg) := by
        simpa [actionCentralizerIn] using hx
      exact
        congrArg Subtype.val <|
          (mem_fixingSubgroup_iff (M := ↥KR) (s := (Set.univ : Set Vg))).1 hxfix v (by trivial)
  have hρKRker_eq_ψker : ρKR.ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      ext v
      have hv : ρKR x (Additive.ofMul v) = Additive.ofMul v := by
        simpa using congrArg (fun g => g (Additive.ofMul v)) hx
      have hv' := congrArg Additive.toMul hv
      change x • v = v at hv'
      exact congrArg Subtype.val hv'
    · intro hx
      apply DFunLike.ext
      intro v
      apply Additive.toMul.injective
      have hv : ψ x (Additive.toMul v) = Additive.toMul v := by
        simpa [ψ, MulDistribMulAction.toMulAut_apply] using DFunLike.congr_fun hx (Additive.toMul v)
      change ψ x (Additive.toMul v) = Additive.toMul v
      exact hv
  have hρKRker_bot : ρKR.ker = ⊥ := by
    rw [hρKRker_eq_ψker, hψker]
    have hcentKR :
        actionCentralizerIn (A := ↥KR) (G := ↥Vg) (⊤ : Subgroup KR) = ⊥ := by
      subst hR_eq
      simpa [KR, Kg] using
        theorem_3_6_centralizer_KR₀_on_fitting_eq_bot H R R p hind hsolvG hodd hHR
          hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup
          hVinfNK_bot hKsub_fit hCH_le_K
    exact hcentKR
  let ρ : Representation (ZMod p) S (Additive Vg) := ρKR.comp S.subtype
  have hρker_bot : ρ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxKR : (S.subtype x : KR) ∈ ρKR.ker := by
      change ρKR (S.subtype x) = 1
      simpa [ρ, MonoidHom.mem_ker] using hx
    rw [hρKRker_bot] at hxKR
    apply Subtype.ext
    simpa using hxKR
  let Cfix : Subgroup G := subgroupCentralizerIn Vg R
  have hCfix_le_Vg : Cfix ≤ Vg := by
    intro x hx
    exact hx.1
  have hRnormVg : R ≤ Subgroup.normalizer Vg := Subgroup.le_normalizer_of_normal (H := Vg)
  have : Subgroup.Normalizes R Vg := ⟨hRnormVg⟩
  let Ffix : Subgroup Vg := fixedPointSubgroup (↥R) (↥Vg)
  let eFix : ρKR.fixedSubspace RsubKR ≃ Additive Ffix := by
    refine
      { toFun := fun v => Additive.ofMul ⟨Additive.toMul v.1, ?_⟩
        invFun := fun c => ⟨Additive.ofMul ((Additive.toMul c : Ffix) : Vg), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [FixedPoints.mem_subgroup]
      intro r
      let rsub : RsubKR := ⟨⟨r, Subgroup.mem_sup_right r.2⟩, by
        simp [RsubKR, KR, Subgroup.mem_subgroupOf]⟩
      have hvr : (ρKR.comp RsubKR.subtype) rsub v.1 = v.1 := v.2 rsub
      have :
          (r • (Additive.toMul v.1) : Vg) = Additive.toMul v.1 := by
        have hvr' := congrArg Additive.toMul hvr
        change r • Additive.toMul v.1 = Additive.toMul v.1 at hvr'
        exact hvr'
      exact this
    · rw [Representation.fixedSubspace, Representation.mem_invariants]
      rintro ⟨r, hrRsub⟩
      apply Additive.toMul.injective
      have hrR : (r : G) ∈ R := by
        simpa [RsubKR, KR, Subgroup.mem_subgroupOf] using hrRsub
      let rR : R := ⟨(r : G), hrR⟩
      have hrfixR : ((rR : R) • ((Additive.toMul c : Ffix) : Vg) : Vg) =
          ((Additive.toMul c : Ffix) : Vg) :=
        (Additive.toMul c : Ffix).2 rR
      have hrfix : ((r • ((Additive.toMul c : Ffix) : Vg)) : Vg) =
          ((Additive.toMul c : Ffix) : Vg) := by
        have hrfixR' := hrfixR
        change r • ((Additive.toMul c : Ffix) : Vg) =
          ((Additive.toMul c : Ffix) : Vg) at hrfixR'
        exact hrfixR'
      simpa [ρKR, ψ, MulDistribMulAction.toMulAut_apply,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hrfix
    · intro v
      apply Subtype.ext
      rfl
    · intro c
      apply Additive.toMul.injective
      apply Subtype.ext
      rfl
  have hCfix_card : Nat.card Cfix = p := by
    simpa [Cfix, hR_eq] using
      theorem_3_6_fixed_points_of_R₀_on_fitting H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup hVinfNK_bot
        hKsub_fit hCH_le_K
  have hfixKR_card : Nat.card ↥(ρKR.fixedSubspace RsubKR) = p := by
    have hFfix_eq : Ffix = Cfix.subgroupOf Vg := by
      simpa [Cfix, Ffix] using
        fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Vg R hRnormVg
    have hFfix_card : Nat.card Ffix = p := by
      calc
        Nat.card Ffix = Nat.card (Cfix.subgroupOf Vg) := by rw [hFfix_eq]
        _ = Nat.card Cfix := by rw [natCard_subgroupOf_eq Cfix Vg hCfix_le_Vg]
        _ = p := hCfix_card
    calc
      Nat.card ↥(ρKR.fixedSubspace RsubKR) = Nat.card (Additive Ffix) := Nat.card_congr eFix
      _ = Nat.card Ffix := by rfl
      _ = p := hFfix_card
  have hfixKR :
      Module.rank (ZMod p) ↥(ρKR.fixedSubspace RsubKR) = 1 := by
    let : FiniteDimensional (ZMod p) ↥(ρKR.fixedSubspace RsubKR) := Module.Finite.of_finite
    have hcard_pow :
        Nat.card ↥(ρKR.fixedSubspace RsubKR) =
          p ^ Module.finrank (ZMod p) ↥(ρKR.fixedSubspace RsubKR) := by
      simpa [Nat.card_eq_fintype_card, ZMod.card] using
        (Module.natCard_eq_pow_finrank (K := ZMod p) (V := ↥(ρKR.fixedSubspace RsubKR)))
    have hfin : Module.finrank (ZMod p) ↥(ρKR.fixedSubspace RsubKR) = 1 := by
      have hinj := Nat.pow_right_injective (a := p) hp.two_le
      apply hinj
      calc
        p ^ Module.finrank (ZMod p) ↥(ρKR.fixedSubspace RsubKR) =
            Nat.card ↥(ρKR.fixedSubspace RsubKR) := hcard_pow.symm
        _ = p := hfixKR_card
        _ = p ^ 1 := by simp
    rw [← Module.finrank_eq_rank, hfin]
    rfl
  have hfixR : Module.rank (ZMod p) ↥(ρ.fixedSubspace Rsub) = 1 := by
    rw [fixedSubspace_subgroupOf_eq (ρ := ρKR) (S := S) (R := RsubKR) le_sup_right]
    exact hfixKR
  have hRsub_prime : Nat.Prime (Nat.card Rsub) := by
    rw [natCard_subgroupOf_eq RsubKR S le_sup_right, natCard_subgroupOf_eq R KR le_sup_right]
    exact hR_prime
  have hRsub_cyclic : IsCyclic Rsub := by
    let : Fact (Nat.Prime (Nat.card R)) := ⟨hR_prime⟩
    have hcardRsub : Nat.card Rsub = Nat.card R := by
      rw [natCard_subgroupOf_eq RsubKR S le_sup_right, natCard_subgroupOf_eq R KR le_sup_right]
    exact isCyclic_of_prime_card (α := Rsub) hcardRsub
  have hsolvKsub : Group.IsSolvable Ksub := by infer_instance
  have hcomm_le :
      ⁅Ksub, Ksub⁆ ≤ ρ.centralizerIn Ksub :=
    theorem_3_5 Ksub Rsub ρ hfrob hsolvKsub hRsub_cyclic hRsub_prime hcharS hfixR
  have hcent_bot : ρ.centralizerIn Ksub = ⊥ :=
    centralizerIn_eq_bot_of_ker_eq_bot ρ Ksub hρker_bot
  have hcomm_eq_bot : ⁅Ksub, Ksub⁆ = ⊥ := by
    rw [hcent_bot] at hcomm_le
    exact le_antisymm hcomm_le bot_le
  have hKsub_comm : IsMulCommutative ↥Ksub := by
    exact
      (Subgroup.le_centralizer_iff_isMulCommutative (K := Ksub)).mp <|
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Ksub) (H₂ := Ksub)).mp hcomm_eq_bot
  let : IsMulCommutative ↥Ksub := hKsub_comm
  let eKsub : Ksub ≃* Kcommsub :=
    Subgroup.subgroupOfEquivOfLe (H := Kcommsub) (K := S) le_sup_left
  have hKcommsub_comm : IsMulCommutative ↥Kcommsub := by
    refine ⟨⟨?_⟩⟩
    intro a b
    apply eKsub.symm.injective
    exact ((IsMulCommutative.is_comm (M := Ksub)).comm (eKsub.symm a) (eKsub.symm b))
  let : IsMulCommutative ↥Kcommsub := hKcommsub_comm
  let eKcommg : Kcommsub ≃* Kcommg :=
    Subgroup.subgroupOfEquivOfLe (H := Kcommg) (K := KR) hKcommg_le_KR
  have hKcommg_comm : IsMulCommutative ↥Kcommg := by
    refine ⟨⟨?_⟩⟩
    intro a b
    apply eKcommg.symm.injective
    exact ((IsMulCommutative.is_comm (M := Kcommsub)).comm (eKcommg.symm a) (eKcommg.symm b))
  let : IsMulCommutative ↥Kcommg := hKcommg_comm
  let eKcomm : Kcomm ≃* Kcommg := Subgroup.equivMapOfInjective (f := f) Kcomm hf
  refine ⟨⟨?_⟩⟩
  intro a b
  apply eKcomm.injective
  exact ((IsMulCommutative.is_comm (M := Kcommg)).comm (eKcomm a) (eKcomm b))

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.theorem_3_6_K_elementaryAbelian
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    (hK_inv : IsInvariant (↥R) (↥H) K) →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    V ⊔ normalizerOf K = ⊤ →
    V ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    R = R₀ →
    let _ : IsInvariant (↥R) (↥H) K := hK_inv
    ∃ qK : ℕ,
      Nat.Prime qK ∧ qK ≠ p ∧ qK ≠ Nat.card R₀ ∧ IsElementaryAbelian qK ↥K := by
  set_option maxHeartbeats 800000 in
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
    hP_p hPK_ne_bot hproper hR_eq
  let Psub : Subgroup H := normalizerSubtypeMap K P
  have hPsub_le_NK : Psub ≤ normalizerOf K := by
    simpa [Psub, normalizerSubtypeMap] using (Subgroup.map_subtype_le P)
  have hPsub_normK : Psub ≤ Subgroup.normalizer (K : Set H) := by
    simpa [normalizerOf] using hPsub_le_NK
  let : IsInvariant (↥R) (↥H) K := hK_inv
  let Cfix : Subgroup K := fixedPointSubgroup (↥R) (↥K)
  let Kcomm : Subgroup K := commutatorAction (A := ↥R) (G := ↥K)
  obtain ⟨qK, hqK_prime, hqK_ne_p, hqK_ne_R₀, hqK_pgroup, hcomm_center, hexpK⟩ :=
    theorem_3_6_K_class_two_exponent_q H R R₀ p hind hsolvG hodd hHR hcopHR hR₀_le
      hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit
      hCH_le_K hP_p hPK_ne_bot hproper
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    exact hPK_ne_bot (by simp [hK_bot])
  have : Fact qK.Prime := ⟨hqK_prime⟩
  have : Fact (IsPGroup qK ↥K) := ⟨hqK_pgroup⟩
  obtain ⟨qK', hqK'_prime, hqK_fix_card', hfix_inf_comm_bot⟩ :=
    theorem_3_6_K_fixed_card_eq_q_and_inf_commutator_eq_bot H R R₀ p hind hsolvG hodd
      hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj
      hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K hP_p hPK_ne_bot
      hproper hR_eq
  have hq_eq : qK' = qK := by
    have hCfix_q : IsPGroup qK Cfix :=
      hqK_pgroup.of_injective Cfix.subtype Cfix.subtype_injective
    have hCfix_card_ne_one : Nat.card Cfix ≠ 1 := by
      intro hcard_one
      exact hqK'_prime.ne_one (hqK_fix_card'.symm.trans hcard_one)
    have hqK_dvd_card : qK ∣ Nat.card Cfix :=
      (hCfix_q.card_eq_or_dvd).resolve_left hCfix_card_ne_one
    have hcardCfix : Nat.card Cfix = qK' := by
      simpa [Cfix] using hqK_fix_card'
    have hqK_dvd_qK' : qK ∣ qK' := by
      rw [← hcardCfix]
      exact hqK_dvd_card
    exact ((Nat.prime_dvd_prime_iff_eq hqK_prime hqK'_prime).1 hqK_dvd_qK').symm
  have hqK_fix_card : Nat.card Cfix = qK := by
    exact hqK_fix_card'.trans hq_eq
  have hcomm_pkg :=
    theorem_3_6_K_commutatorAction_proper H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv
      hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper hR_eq
  have hfix_inf_Kcomm_bot : Cfix ⊓ Kcomm = ⊥ := hcomm_pkg.1
  have hKcomm_ne_top : Kcomm ≠ ⊤ := hcomm_pkg.2
  have hKcomm_normal : Kcomm.Normal := commutatorAction_normal (G := ↥K) (A := ↥R)
  have hKcomm_comm :
      IsMulCommutative ↥Kcomm :=
    theorem_3_6_K_commutatorAction_abelian H R R₀ p hind hsolvG hodd hHR hcopHR
      hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv
      hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper hR_eq
  have hcopRK : Nat.Coprime (Nat.card R) (Nat.card K) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card K) hcopHR.symm
  have hsolvK : Group.IsSolvable ↥K := by infer_instance
  have hsupCK : Cfix ⊔ Kcomm = ⊤ :=
    proposition_1_6_a (G := ↥K) (A := ↥R) hsolvK hcopRK
  have hcomplCK : Cfix.IsComplement' Kcomm := by
    have hdisj : Disjoint Cfix Kcomm := by
      rw [Subgroup.disjoint_def]
      intro x hxC hxK
      have hx : x ∈ Cfix ⊓ Kcomm := ⟨hxC, hxK⟩
      simpa [hfix_inf_Kcomm_bot] using hx
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hxsup : x ∈ Cfix ⊔ Kcomm := by simp [hsupCK]
      rcases (Subgroup.mem_sup_of_normal_right (s := Cfix) (t := Kcomm) (x := x)).1 hxsup with
        ⟨y, hy, z, hz, rfl⟩
      exact Set.mem_mul.mpr ⟨y, hy, z, hz, rfl⟩
  have hKcomm_index : Kcomm.index = qK := by
    rw [hcomplCK.index_eq_card, hqK_fix_card]
  have hKcomm_not_Pinvariant :
      ¬ Psub ≤ Subgroup.normalizer ((Kcomm.map K.subtype : Subgroup H) : Set H) := by
    intro hnorm
    let X : Subgroup H := Kcomm.map K.subtype
    have hX_le_K : X ≤ K := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.2
    have hX_lt_K : X < K := by
      refine lt_of_le_of_ne hX_le_K ?_
      intro hX_eq_K
      have htop_map : (⊤ : Subgroup K).map K.subtype = K := by
        ext x
        constructor
        · rintro ⟨y, -, rfl⟩
          exact y.2
        · intro hx
          exact ⟨⟨x, hx⟩, by simp, rfl⟩
      have hmap_eq : Kcomm.map K.subtype = (⊤ : Subgroup K).map K.subtype := by
        simpa [X, htop_map] using hX_eq_K
      apply hKcomm_ne_top
      exact (Subgroup.map_injective (f := K.subtype) K.subtype_injective) hmap_eq
    have hX_inv : IsInvariant (↥R) (↥H) X := by
      have hKcomm_inv : IsInvariant (↥R) (↥K) Kcomm :=
        commutatorAction_isInvariant (G := ↥K) (A := ↥R)
      simpa [X] using isInvariant_map_subtype (A := ↥R) (G := ↥H) K Kcomm
    have hcommXP_bot : ⁅X, Psub⁆ = ⊥ := hproper X hX_le_K hX_inv hnorm hX_lt_K
    have : Subgroup.Normalizes Psub X := ⟨hnorm⟩
    have htrivX : ActsTrivially (A := ↥Psub) (G := ↥X) := by
      exact actsTrivially_subgroup_conj_of_commutator_eq_bot X Psub hnorm
        (by simpa [Subgroup.commutator_comm] using hcommXP_bot)
    let qcomm : ↥K →* (↥K ⧸ commutator (↥K)) := QuotientGroup.mk' (commutator (↥K))
    have : Subgroup.Normalizes Psub K := ⟨hPsub_normK⟩
    let hKcomm_invP : IsInvariant (↥Psub) (↥K) (commutator (↥K)) :=
      isInvariant_of_characteristic (A := ↥Psub) (G := ↥K) (commutator (↥K))
    let : MulAction.QuotientAction (↥Psub) (commutator (↥K)) :=
      quotientAction_of_isInvariant (A := ↥Psub) (commutator (↥K)) hKcomm_invP
    let : MulDistribMulAction (↥Psub) (↥K ⧸ commutator (↥K)) :=
      quotientMulDistribMulAction (A := ↥Psub) (G := ↥K) (commutator (↥K)) hKcomm_invP
    have hfixQ_bot :
        fixedPointSubgroup (↥Psub) (↥K ⧸ commutator (↥K)) = ⊥ :=
      theorem_3_6_K_quotient_commutator_fixed_eq_bot H R R₀ p hind hsolvG hodd hHR
        hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv
        hKsub_fit hP_p hPK_ne_bot hproper
    have hKcomm_le_comm : Kcomm ≤ commutator (↥K) := by
      intro x hx
      have hxmap : ((x : K) : H) ∈ X := Subgroup.mem_map_of_mem K.subtype hx
      have hxfixQ : qcomm x ∈ fixedPointSubgroup (↥Psub) (↥K ⧸ commutator (↥K)) := by
        rw [FixedPoints.mem_subgroup]
        intro a
        have hxfix : a • (⟨((x : K) : H), hxmap⟩ : X) = ⟨((x : K) : H), hxmap⟩ := htrivX a _
        have hxfixK : a • x = x := by
          have hxfixH : (((a • (⟨((x : K) : H), hxmap⟩ : X) : X) : H)) = ((x : K) : H) := by
            simpa using congrArg Subtype.val hxfix
          apply Subtype.ext
          simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hnorm, hPsub_normK] using
            hxfixH
        apply QuotientGroup.eq.mpr
        change ((a • x : K)⁻¹ * x) ∈ commutator (↥K)
        simp [hxfixK]
      have hxbot : qcomm x ∈ (⊥ : Subgroup (↥K ⧸ commutator (↥K))) := by
        simpa [hfixQ_bot] using hxfixQ
      have hqone : qcomm x = 1 := by simpa using hxbot
      exact (QuotientGroup.eq_one_iff (N := commutator (↥K)) x).1 hqone
    have hPhi_eq : frattini (↥K) = commutator (↥K) :=
      theorem_3_6_K_frattini_eq_commutator H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv
        hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper
    let hKcomm_inv : IsInvariant (↥R) (↥K) (commutator (↥K)) :=
      isInvariant_of_characteristic (A := ↥R) (G := ↥K) (commutator (↥K))
    let : MulAction.QuotientAction (↥R) (commutator (↥K)) :=
      quotientAction_of_isInvariant (A := ↥R) (commutator (↥K)) hKcomm_inv
    let : MulDistribMulAction (↥R) (↥K ⧸ commutator (↥K)) :=
      quotientMulDistribMulAction (A := ↥R) (G := ↥K) (commutator (↥K)) hKcomm_inv
    have hquot_triv_comm : ActsTrivially (A := ↥R) (G := ↥K ⧸ commutator (↥K)) := by
      intro a x
      refine QuotientGroup.induction_on x ?_
      intro k
      have hkcomm : k⁻¹ * (a • k) ∈ Kcomm := by
        let S : Set K := {x : K | ∃ b : R, ∃ g : K, x = g⁻¹ * (b • g)}
        have hKcomm_def : Kcomm = Subgroup.closure S := by
          simpa [Kcomm, S] using (commutatorAction_eq_closure (G := ↥K) (A := ↥R))
        rw [hKcomm_def]
        exact Subgroup.subset_closure ⟨a, k, rfl⟩
      have hkcomm' : k⁻¹ * (a • k) ∈ commutator (↥K) := hKcomm_le_comm hkcomm
      have hconj : (a • k) * k⁻¹ ∈ commutator (↥K) := by
        have : k * (k⁻¹ * (a • k)) * k⁻¹ ∈ commutator (↥K) :=
          (inferInstance : (commutator (↥K)).Normal).conj_mem _ hkcomm' k
        simpa [mul_assoc] using this
      have hfix : ((a • k : K) : ↥K ⧸ commutator (↥K)) = ((k : K) : ↥K ⧸ commutator (↥K)) :=
        (QuotientGroup.eq_iff_div_mem (N := commutator (↥K)) (x := a • k) (y := k)).2
          (by simpa [div_eq_mul_inv] using hconj)
      simpa using hfix
    let hPhi_inv : IsInvariant (↥R) (↥K) (frattini (↥K)) :=
      isInvariant_of_characteristic (A := ↥R) (G := ↥K) (frattini (↥K))
    let : MulAction.QuotientAction (↥R) (frattini (↥K)) :=
      quotientAction_of_isInvariant (A := ↥R) (frattini (↥K)) hPhi_inv
    let : MulDistribMulAction (↥R) (↥K ⧸ frattini (↥K)) :=
      quotientMulDistribMulAction (A := ↥R) (G := ↥K) (frattini (↥K)) hPhi_inv
    have hquot_triv : ActsTrivially (A := ↥R) (G := ↥K ⧸ frattini (↥K)) := by
      intro a x
      refine QuotientGroup.induction_on x ?_
      intro k
      have hk_fix_comm :
          a • ((k : ↥K) : ↥K ⧸ commutator (↥K)) = ((k : ↥K) : ↥K ⧸ commutator (↥K)) :=
        hquot_triv_comm a ((k : ↥K) : ↥K ⧸ commutator (↥K))
      have hk_div_comm : (a • k) / k ∈ commutator (↥K) :=
        (QuotientGroup.eq_iff_div_mem (N := commutator (↥K)) (x := a • k) (y := k)).1
          (by simpa using hk_fix_comm)
      have hfix : ((a • k : K) : ↥K ⧸ frattini (↥K)) = ((k : K) : ↥K ⧸ frattini (↥K)) := by
        apply (QuotientGroup.eq_iff_div_mem (N := frattini (↥K)) (x := a • k) (y := k)).2
        rw [hPhi_eq]
        exact hk_div_comm
      simpa using hfix
    have htrivR : ActsTrivially (A := ↥R) (G := ↥K) :=
      theorem_1_8 (R := ↥K) (A := ↥R) (p := qK) hcopRK (by simpa using hquot_triv)
    let Kg : Subgroup G := K.map H.subtype
    have hRnormKg : R ≤ Subgroup.normalizer (Kg : Set G) := by
      refine subgroup_le_normalizer_of_conj_mem Kg R ?_
      intro a x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact Subgroup.mem_map_of_mem H.subtype <|
        (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := K) a y).1 hy
    have : Subgroup.Normalizes R Kg := ⟨hRnormKg⟩
    have htrivKg : ActsTrivially (A := ↥R) (G := ↥Kg) := by
      intro a x
      rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hyx⟩
      have hyfix : a • (⟨y, hy⟩ : K) = ⟨y, hy⟩ := htrivR a ⟨y, hy⟩
      have hyfixH : (((a • (⟨y, hy⟩ : K) : K) : H)) = y := congrArg Subtype.val hyfix
      have hyfixH' : a • (y : H) = y := by
        change a • (y : H) = y at hyfixH
        exact hyfixH
      have hyfixG : (a : G) * (y : H) * (a : G)⁻¹ = y := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH] using
          congrArg H.subtype hyfixH'
      apply Subtype.ext
      calc
        ((a • x : Kg) : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        _ = (a : G) * (y : H) * (a : G)⁻¹ := by
          simpa using congrArg (fun z : G => (a : G) * z * (a : G)⁻¹) hyx.symm
        _ = y := hyfixG
        _ = x := by simpa using hyx
    have hKR_bot : ⁅R, Kg⁆ = ⊥ :=
      commutator_eq_bot_of_actsTrivially_subgroup_conj Kg R hRnormKg htrivKg
    exact
      (theorem_3_6_r0_commutator_nontrivial H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup hVinfNK_bot
        hKsub_fit hCH_le_K) (by simpa [Kg, Subgroup.commutator_comm, hR_eq] using hKR_bot)
  have : Subgroup.Normalizes Psub K := ⟨hPsub_normK⟩
  let σP : Psub →* MulAut (↥K) := MulDistribMulAction.toMulAut (G := ↥Psub) (M := ↥K)
  have hKcomm_exists_conj_ne :
      ∃ a : Psub, Kcomm.map (σP a).toMonoidHom ≠ Kcomm := by
    by_contra hforall
    push Not at hforall
    have hnorm :
        Psub ≤ Subgroup.normalizer ((Kcomm.map K.subtype : Subgroup H) : Set H) := by
      refine subgroup_le_normalizer_of_conj_mem (Kcomm.map K.subtype) Psub ?_
      intro a x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy' : a • y ∈ Kcomm := by
        have hmap : Kcomm.map (σP a).toMonoidHom = Kcomm := hforall a
        have hmem : a • y ∈ Kcomm.map (σP a).toMonoidHom := by
          change (σP a y) ∈ Kcomm.map (σP a).toMonoidHom
          exact Subgroup.mem_map_of_mem (σP a).toMonoidHom hy
        rw [hmap] at hmem
        exact hmem
      exact Subgroup.mem_map_of_mem K.subtype hy'
    exact hKcomm_not_Pinvariant hnorm
  rcases hKcomm_exists_conj_ne with ⟨a, ha_ne⟩
  let Kcommx : Subgroup K := Kcomm.map (σP a).toMonoidHom
  let e : Kcomm ≃* Kcommx := Subgroup.equivMapOfInjective (f := (σP a).toMonoidHom) Kcomm
    (σP a).injective
  have hKcommx_comm : IsMulCommutative ↥Kcommx := by
    refine ⟨⟨?_⟩⟩
    intro x y
    apply e.symm.injective
    simpa using ((IsMulCommutative.is_comm (M := Kcomm)).comm (e.symm x) (e.symm y))
  have hcardKcommx : Nat.card Kcommx = Nat.card Kcomm := by
    exact (Nat.card_congr e.toEquiv).symm
  have hKcommx_index : Kcommx.index = qK := by
    rw [Subgroup.index_eq_card]
    have hcardK : Nat.card K = qK * Nat.card Kcomm := by
      rw [← hcomplCK.card_mul_card, hqK_fix_card, mul_comm]
    have hcardK' : Nat.card K = Nat.card (K ⧸ Kcommx) * Nat.card Kcommx := by
      simpa [Subgroup.index_eq_card] using (Subgroup.card_eq_card_quotient_mul_card_subgroup Kcommx)
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Kcommx))
    calc
      Nat.card (K ⧸ Kcommx) * Nat.card Kcommx = Nat.card K := hcardK'.symm
      _ = qK * Nat.card Kcomm := hcardK
      _ = qK * Nat.card Kcommx := by rw [hcardKcommx]
  have hsup_top : Kcomm ⊔ Kcommx = ⊤ := by
    by_contra hsup_ne
    have hU_lt : Kcomm ⊔ Kcommx < ⊤ := lt_of_le_of_ne le_top hsup_ne
    let U : Subgroup K := Kcomm ⊔ Kcommx
    have hU_index_dvd : U.index ∣ Kcomm.index := by
      exact Subgroup.index_dvd_of_le (show Kcomm ≤ U by exact le_sup_left)
    have hU_index_ne_one : U.index ≠ 1 := by
      intro hU_one
      exact hsup_ne (Subgroup.index_eq_one.mp hU_one)
    have hU_index_eq : U.index = qK := by
      exact (hqK_prime.eq_one_or_self_of_dvd U.index (hKcomm_index ▸ hU_index_dvd)).resolve_left
        hU_index_ne_one
    have hU_card_eq : Nat.card U = Nat.card Kcomm := by
      apply Nat.eq_of_mul_eq_mul_left hqK_prime.pos
      calc
        qK * Nat.card U = U.index * Nat.card U := by rw [hU_index_eq]
        _ = Nat.card K := Subgroup.index_mul_card (H := U)
        _ = Kcomm.index * Nat.card Kcomm := (Subgroup.index_mul_card (H := Kcomm)).symm
        _ = qK * Nat.card Kcomm := by rw [hKcomm_index]
    have hKcomm_sub_top : Kcomm.subgroupOf U = ⊤ := by
      apply (Subgroup.card_eq_iff_eq_top (H := Kcomm.subgroupOf U)).1
      simpa [natCard_subgroupOf_eq Kcomm U le_sup_left] using hU_card_eq.symm
    have hU_eq_Kcomm : U = Kcomm := by
      apply le_antisymm (by
        intro x hx
        have hxsub : (⟨x, hx⟩ : U) ∈ Kcomm.subgroupOf U := by
          simp [hKcomm_sub_top]
        simpa [Subgroup.mem_subgroupOf] using hxsub) le_sup_left
    have hKcommx_le_Kcomm : Kcommx ≤ Kcomm := by
      rw [← hU_eq_Kcomm]
      exact le_sup_right
    have hKcommx_eq : Kcommx = Kcomm := by
      apply le_antisymm hKcommx_le_Kcomm ?_
      have hKcommx_sub_top : Kcommx.subgroupOf Kcomm = ⊤ := by
        apply (Subgroup.card_eq_iff_eq_top (H := Kcommx.subgroupOf Kcomm)).1
        simpa [natCard_subgroupOf_eq Kcommx Kcomm hKcommx_le_Kcomm] using hcardKcommx
      intro x hx
      have hxsub : (⟨x, hx⟩ : Kcomm) ∈ Kcommx.subgroupOf Kcomm := by
        simp [hKcommx_sub_top]
      simpa [Subgroup.mem_subgroupOf] using hxsub
    exact ha_ne hKcommx_eq
  let Z : Subgroup ↥K := Subgroup.center (↥K)
  have hKcommx_normal : Kcommx.Normal := by
    exact Subgroup.Normal.map hKcomm_normal (σP a).toMonoidHom (σP a).surjective
  have hinf_le_center : Kcomm ⊓ Kcommx ≤ Z := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    have hysup : y ∈ Kcomm ⊔ Kcommx := by simp [hsup_top]
    rcases (Subgroup.mem_sup_of_normal_left (s := Kcomm) (t := Kcommx) (x := y)).1 hysup with
      ⟨u, hu, v, hv, huv⟩
    have hzKcomm : z * u = u * z := by
      simpa using congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := Kcomm)).comm ⟨z, hz.1⟩ ⟨u, hu⟩)
    have hzKcommx : z * v = v * z := by
      simpa using congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := Kcommx)).comm ⟨z, hz.2⟩ ⟨v, hv⟩)
    calc
      y * z = (u * v) * z := by rw [huv]
      _ = u * (v * z) := by simp [mul_assoc]
      _ = u * (z * v) := by rw [hzKcommx]
      _ = (u * z) * v := by simp [mul_assoc]
      _ = (z * u) * v := by rw [hzKcomm]
      _ = z * (u * v) := by simp [mul_assoc]
      _ = z * y := by rw [huv]
  have hKcomm_rel : (Kcomm ⊓ Kcommx).relIndex Kcommx = qK := by
    have hrel :
        Kcomm.relIndex Kcommx = Kcomm.index := by
      calc
        Kcomm.relIndex Kcommx = Kcomm.relIndex (Kcommx ⊔ Kcomm) := by
          exact (Subgroup.relIndex_sup_right (H := Kcommx) (K := Kcomm)).symm
        _ = Kcomm.relIndex ⊤ := by
          simpa [sup_comm] using
            congrArg (fun S : Subgroup K => Kcomm.relIndex S) hsup_top
        _ = Kcomm.index := Kcomm.relIndex_top_right
    calc
      (Kcomm ⊓ Kcommx).relIndex Kcommx = Kcomm.relIndex Kcommx := by
        simpa [inf_comm] using (Subgroup.inf_relIndex_left (H := Kcommx) (K := Kcomm))
      _ = qK := by rw [hrel, hKcomm_index]
  have hinf_index : (Kcomm ⊓ Kcommx).index = qK ^ 2 := by
    calc
      (Kcomm ⊓ Kcommx).index = (Kcomm ⊓ Kcommx).relIndex Kcommx * Kcommx.index := by
        exact (Subgroup.relIndex_mul_index (show Kcomm ⊓ Kcommx ≤ Kcommx by exact inf_le_right)).symm
      _ = qK * qK := by rw [hKcomm_rel, hKcommx_index]
      _ = qK ^ 2 := by ring
  have hZ_index_dvd : Z.index ∣ qK ^ 2 := by
    exact dvd_trans (Subgroup.index_dvd_of_le hinf_le_center) (dvd_of_eq hinf_index)
  by_cases hK_comm : IsMulCommutative ↥K
  · refine ⟨qK, hqK_prime, hqK_ne_p, hqK_ne_R₀, ?_⟩
    refine
      { toIsMulCommutative := hK_comm
        exponent_dvd_p := ?_ }
    simp [hexpK]
  · have hZ_index_ne_one : Z.index ≠ 1 := by
      intro hZ_one
      apply hK_comm
      refine ⟨⟨?_⟩⟩
      intro x y
      have hZ_top : Z = ⊤ := Subgroup.index_eq_one.mp hZ_one
      have hxZ : x ∈ Z := by simp [hZ_top]
      exact (Subgroup.mem_center_iff.mp hxZ y).symm
    obtain ⟨m, hm_le, hm_index⟩ := (Nat.dvd_prime_pow hqK_prime).1 hZ_index_dvd
    have hm_ne_zero : m ≠ 0 := by
      intro hm_zero
      exact hZ_index_ne_one (by simpa [hm_zero] using hm_index)
    have hm_eq_one_or_two : m = 1 ∨ m = 2 := by
      rcases Nat.lt_or_eq_of_le hm_le with (hm_lt_two | hm_eq_two)
      · have hm_le_one : m ≤ 1 := Nat.le_of_lt_succ hm_lt_two
        rcases Nat.lt_or_eq_of_le hm_le_one with (hm_lt_one | hm_eq_one)
        · have hm_zero : m = 0 := Nat.lt_one_iff.mp hm_lt_one
          exact (hm_ne_zero hm_zero).elim
        · exact Or.inl hm_eq_one
      · exact Or.inr hm_eq_two
    have hQ_cyclic_contra : m ≠ 1 := by
      intro hm_one
      have hQ_card : Nat.card (↥K ⧸ Z) = qK := by
        simpa [hm_index, hm_one] using (Subgroup.index_eq_card (H := Z)).symm
      have hQ_cyclic : IsCyclic (↥K ⧸ Z) := isCyclic_of_prime_card (α := ↥K ⧸ Z) hQ_card
      let : IsCyclic (↥K ⧸ Z) := hQ_cyclic
      have hkerZ : (QuotientGroup.mk' Z).ker ≤ Subgroup.center ↥K := by
        simp [Z, QuotientGroup.ker_mk']
      have hcommQ : IsMulCommutative ↥K := by
        exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
          (QuotientGroup.mk' Z) hkerZ
      exact hK_comm hcommQ
    have hm_two : m = 2 := hm_eq_one_or_two.resolve_left hQ_cyclic_contra
    have hQ_card : Nat.card (↥K ⧸ Z) = qK ^ 2 := by
      simpa [hm_index, hm_two] using (Subgroup.index_eq_card (H := Z)).symm
    let Psubg : Subgroup G := Psub.map H.subtype
    let Sg : Subgroup G := Psubg ⊔ R
    have hPsubg_le_H : Psubg ≤ H := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.2
    have hPsubg_le_normKg : Psubg ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
        rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
        let kK : K := ⟨k, hk⟩
        have hkmap :
            H.subtype ((((⟨b, hb⟩ : Psub) • kK : K) : H)) ∈ K.map H.subtype :=
          Subgroup.mem_map_of_mem H.subtype (((⟨b, hb⟩ : Psub) • kK).2)
        change H.subtype b * H.subtype k * (H.subtype b)⁻¹ ∈ K.map H.subtype at hkmap
        exact hkmap
      · intro hx
        rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
        have hb_inv : b⁻¹ ∈ Psub := Psub.inv_mem hb
        rcases Subgroup.mem_map.mp hx with ⟨k, hk, hkx⟩
        let kK : K := ⟨k, hk⟩
        have hkmap :
            H.subtype ((((⟨b⁻¹, hb_inv⟩ : Psub) • kK : K) : H)) ∈ K.map H.subtype :=
          Subgroup.mem_map_of_mem H.subtype (((⟨b⁻¹, hb_inv⟩ : Psub) • kK).2)
        have hkx' :
            H.subtype ((((⟨b⁻¹, hb_inv⟩ : Psub) • kK : K) : H)) = x := by
          calc
            H.subtype ((((⟨b⁻¹, hb_inv⟩ : Psub) • kK : K) : H)) = (b : G)⁻¹ * (k : H) * (b : G) := by
              simp [kK, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
                mul_assoc]
            _ = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * (b : G) := by
              simpa using congrArg (fun z : G => (b : G)⁻¹ * z * (b : G)) hkx
            _ = x := by simp [mul_assoc]
        exact hkx' ▸ hkmap
    have hRnormKg : R ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hyK, rfl⟩
        exact Subgroup.mem_map_of_mem H.subtype <|
          (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := K) ⟨a, ha⟩ y).1 hyK
      · intro hx
        have ha_inv : a⁻¹ ∈ R := R.inv_mem ha
        rcases Subgroup.mem_map.mp hx with ⟨y, hyK, hyx⟩
        refine Subgroup.mem_map.mpr ?_
        let yK : K := ⟨y, hyK⟩
        refine ⟨(⟨a⁻¹, ha_inv⟩ : R) • yK,
          (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := K) ⟨a⁻¹, ha_inv⟩ yK).1 hyK, ?_⟩
        have hyx' : H.subtype ((((⟨a⁻¹, ha_inv⟩ : R) • yK : K) : H)) = x := by
          calc
            H.subtype ((((⟨a⁻¹, ha_inv⟩ : R) • yK : K) : H)) =
                H.subtype ((⟨a⁻¹, ha_inv⟩ : R) • (y : H)) := by
              rfl
            _ = (a : G)⁻¹ * (y : H) * (a : G) := by
              simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
            _ = (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * (a : G) := by
              simpa using congrArg (fun z : G => (a : G)⁻¹ * z * (a : G)) hyx
            _ = x := by simp [mul_assoc]
        exact hyx'
    have hSg_le_normKg :
        Sg ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) :=
      sup_le hPsubg_le_normKg hRnormKg
    have hR_le_normPsubg : R ≤ Subgroup.normalizer (Psubg : Set G) := by
      refine subgroup_le_normalizer_of_conj_mem Psubg R ?_
      intro a x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy' : (⟨a, a.2⟩ : R) • y ∈ Psub :=
        (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := Psub) ⟨a, a.2⟩ y).1 hy
      exact Subgroup.mem_map_of_mem H.subtype hy'
    have hSg_le_normPsubg : Sg ≤ Subgroup.normalizer (Psubg : Set G) := by
      exact sup_le Psubg.le_normalizer hR_le_normPsubg
    have hSg_le_normH : Sg ≤ Subgroup.normalizer H := by
      exact sup_le (hPsubg_le_H.trans (Subgroup.le_normalizer_of_normal (H := H))) hRnormH
    have : Subgroup.Normalizes Sg H := ⟨hSg_le_normH⟩
    have hPsubgsub_normal : (Psubg.subgroupOf Sg).Normal := by
      simpa [Sg] using
        (Subgroup.normal_subgroupOf_of_le_normalizer (H := Sg) (N := Psubg) hSg_le_normPsubg)
    have hPsubgR_disj : Disjoint Psubg R := hHR.disjoint.mono_left hPsubg_le_H
    let Psubgsub : Subgroup Sg := Psubg.subgroupOf Sg
    let Rsub : Subgroup Sg := R.subgroupOf Sg
    have hPsubgsubRsub_disj : Disjoint Psubgsub Rsub := by
      rw [Subgroup.disjoint_def]
      intro x hxP hxR
      apply Subtype.ext
      exact (Subgroup.disjoint_def.mp hPsubgR_disj)
        (by simpa [Psubgsub, Subgroup.mem_subgroupOf] using hxP)
        (by simpa [Rsub, Subgroup.mem_subgroupOf] using hxR)
    have hsub_sup : Psubgsub ⊔ Rsub = ⊤ := by
      calc
        Psubgsub ⊔ Rsub = (Psubg ⊔ R).subgroupOf Sg := by
          symm
          exact Subgroup.subgroupOf_sup (A := Psubg) (A' := R) (B := Sg) le_sup_left le_sup_right
        _ = ⊤ := by simp [Sg]
    have hPsubgsub_compl : Psubgsub.IsComplement' Rsub := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hPsubgsubRsub_disj ?_
      ext x
      constructor
      · intro _; trivial
      · intro _
        have hxsup : x ∈ Psubgsub ⊔ Rsub := by simp [hsub_sup]
        rcases (Subgroup.mem_sup_of_normal_left (s := Psubgsub) (t := Rsub) (x := x)).1 hxsup with
          ⟨y, hy, z, hz, rfl⟩
        exact Set.mem_mul.mpr ⟨y, hy, z, hz, rfl⟩
    have hPsub_p : IsPGroup p Psub := by
      change IsPGroup p (normalizerSubtypeMap K P)
      exact isPGroup_normalizerSubtypeMap K P hP_p
    have hPsubg_p : IsPGroup p Psubg := by
      simpa [Psubg] using hPsub_p.map H.subtype
    have hPsubg_card_eq : Nat.card Psubg = Nat.card Psub := by
      simpa [Psubg] using
        (Subgroup.card_map_of_injective (K := Psub) (f := H.subtype) H.subtype_injective)
    have hcop_q_Psubg : Nat.Coprime qK (Nat.card Psubg) := by
      obtain ⟨n, hcardPsub⟩ := hPsub_p.exists_card_eq
      rw [hPsubg_card_eq, hcardPsub]
      exact (Nat.Prime.coprime_iff_not_dvd hqK_prime).2 (by
        intro hdiv
        exact hqK_ne_p ((Nat.prime_dvd_prime_iff_eq hqK_prime hp).1 (hqK_prime.dvd_of_dvd_pow hdiv)))
    have hR_prime : Nat.Prime (Nat.card R) := by simpa [hR_eq] using hR₀_prime
    have hcop_q_R : Nat.Coprime qK (Nat.card R) := by
      exact (Nat.Prime.coprime_iff_not_dvd hqK_prime).2 (by
        intro hdiv
        exact hqK_ne_R₀ (hR_eq ▸ (Nat.prime_dvd_prime_iff_eq hqK_prime hR_prime).1 hdiv))
    have hPsubgsub_card_eq : Nat.card Psubgsub = Nat.card Psubg := by
      simpa [Psubgsub] using Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := Psubg) (K := Sg) le_sup_left).toEquiv
    have hRsub_card_eq : Nat.card Rsub = Nat.card R := by
      simpa [Rsub] using Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := R) (K := Sg) le_sup_right).toEquiv
    have hSg_card : Nat.card Sg = Nat.card Psubg * Nat.card R := by
      rw [← hPsubgsub_compl.card_mul_card, hPsubgsub_card_eq, hRsub_card_eq]
    have hcop_q_Sg : Nat.Coprime qK (Nat.card Sg) := by
      rw [hSg_card]
      exact Nat.Coprime.mul_right hcop_q_Psubg hcop_q_R
    have hoddSg : Odd (Nat.card Sg) := odd_of_card_dvd hodd (Subgroup.card_subgroup_dvd_card Sg)
    have hK_invS : IsInvariant (↥Sg) (↥H) K := by
      refine ⟨?_⟩
      have hforward : ∀ a : Sg, ∀ x : H, x ∈ K → a • x ∈ K := by
        intro a x hx
        have hnorm : (a : G) ∈ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) :=
          hSg_le_normKg a.2
        have hxmap : (x : G) ∈ K.map H.subtype := Subgroup.mem_map_of_mem H.subtype hx
        have hxmap' : (a : G) * (x : G) * (a : G)⁻¹ ∈ K.map H.subtype :=
          (Subgroup.mem_normalizer_iff.mp hnorm) (x : G) |>.1 hxmap
        have hxsmul : ((a • x : H) : G) ∈ K.map H.subtype := by
          simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hSg_le_normH] using hxmap'
        rcases Subgroup.mem_map.mp hxsmul with ⟨y, hy, hy_eq⟩
        have hxy : (a • x : H) = y := H.subtype_injective hy_eq.symm
        simpa [hxy] using hy
      intro a x
      constructor
      · exact hforward a x
      · intro hx
        have h := hforward a⁻¹ (a • x) hx
        simpa [smul_smul] using h
    let : IsInvariant (↥Sg) (↥H) K := hK_invS
    let hZ_invS : IsInvariant (↥Sg) (↥K) Z :=
      isInvariant_of_characteristic (A := ↥Sg) (G := ↥K) Z
    let : MulAction.QuotientAction (↥Sg) Z :=
      quotientAction_of_isInvariant (A := ↥Sg) Z hZ_invS
    let : MulDistribMulAction (↥Sg) (↥K ⧸ Z) :=
      quotientMulDistribMulAction (A := ↥Sg) (G := ↥K) Z hZ_invS
    have hQ_nontriv : Nontrivial (↥K ⧸ Z) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hQ_card]
      exact Nat.one_lt_pow (by decide) hqK_prime.one_lt
    let : Nontrivial (↥K ⧸ Z) := hQ_nontriv
    have hQ_elem : IsElementaryAbelian qK (↥K ⧸ Z) :=
      isElementaryAbelian_quotient_center_of_commutator_le_center_of_exponent_eq hcomm_center hexpK
    let : IsElementaryAbelian qK (↥K ⧸ Z) := hQ_elem
    let : CommGroup (↥K ⧸ Z) := IsMulCommutative.instCommGroup
    let ι : Sg →* MulAut (↥K ⧸ Z) := MulDistribMulAction.toMulAut (G := ↥Sg) (M := ↥K ⧸ Z)
    let I : Subgroup (MulAut (↥K ⧸ Z)) := ι.range
    let ρI : Representation (ZMod qK) I (Additive (↥K ⧸ Z)) := {
      toFun := fun a =>
        let eAdd : Additive (↥K ⧸ Z) ≃+ Additive (↥K ⧸ Z) := MulEquiv.toAdditive (a : MulAut _)
        let eLin : Additive (↥K ⧸ Z) ≃ₗ[ZMod qK] Additive (↥K ⧸ Z) :=
          eAdd.toLinearEquiv (fun c x => by
            simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
        eLin.toLinearMap
      map_one' := by
        ext x
        apply Additive.toMul.injective
        simp
      map_mul' := by
        intro a' b'
        ext x
        apply Additive.toMul.injective
        simp }
    have hρI_inj : Function.Injective ρI := by
      intro a' b' hab
      apply Subtype.ext
      ext x
      have hx := congrArg (fun f => f (Additive.ofMul x)) hab
      have hx' := congrArg Additive.toMul hx
      simpa [ρI] using hx'
    have hI_card_dvd_Sg : Nat.card I ∣ Nat.card Sg := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ι).toEquiv]
      exact Subgroup.card_quotient_dvd_card (s := ι.ker)
    have hoddI : Odd (Nat.card I) := odd_of_card_dvd hoddSg hI_card_dvd_Sg
    have hcop_q_I : Nat.Coprime qK (Nat.card I) := Nat.Coprime.of_dvd_right hI_card_dvd_Sg hcop_q_Sg
    have hchar_not_dvd_I : ¬ ringChar (ZMod qK) ∣ Nat.card I := by
      simpa [ZMod.ringChar_zmod_n] using (Nat.Prime.coprime_iff_not_dvd hqK_prime).1 hcop_q_I
    let : FiniteDimensional (ZMod qK) (Additive (↥K ⧸ Z)) := Module.Finite.of_finite
    have hfinQ : Module.finrank (ZMod qK) (Additive (↥K ⧸ Z)) = 2 := by
      have hcard_pow :
          Nat.card (Additive (↥K ⧸ Z)) =
            qK ^ Module.finrank (ZMod qK) (Additive (↥K ⧸ Z)) := by
        simpa [Nat.card_eq_fintype_card, ZMod.card] using
          (Module.natCard_eq_pow_finrank (K := ZMod qK) (V := Additive (↥K ⧸ Z)))
      have hinj := Nat.pow_right_injective (a := qK) hqK_prime.two_le
      apply hinj
      calc
        qK ^ Module.finrank (ZMod qK) (Additive (↥K ⧸ Z)) = Nat.card (Additive (↥K ⧸ Z)) := hcard_pow.symm
        _ = Nat.card (↥K ⧸ Z) := by rfl
        _ = qK ^ 2 := hQ_card
    have hI_comm : IsMulCommutative ↥I := by
      exact
        theorem_2_6_a (F := ZMod qK) hoddI hfinQ hρI_inj
          hchar_not_dvd_I
    let j : Sg →* I := ι.rangeRestrict
    have hPsubgsub_eq_comm :
        Psubgsub = ⁅Psubgsub, Rsub⁆ := by
      apply (Subgroup.map_injective (f := Sg.subtype) Sg.subtype_injective)
      calc
        Psubgsub.map Sg.subtype = Psubg := by
          simpa [Psubgsub] using Subgroup.map_subgroupOf_eq_of_le (G := G) (H := Psubg) (K := Sg) le_sup_left
        _ = ⁅Psubg, R₀⁆ := (theorem_3_6_pSubgroup_eq_commutator_with_R₀ H R R₀ p hind hsolvG hodd
          hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup P hP_p hK_inv
          hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K).1
        _ = ⁅Psubg, R⁆ := by simp [hR_eq]
        _ = (⁅Psubgsub, Rsub⁆).map Sg.subtype := by
          symm
          simpa [Psubgsub, Rsub] using
            commutator_subgroupOf_map_eq (S := Sg) (H := R) (R := Psubg) le_sup_right le_sup_left
    have hPsubgsub_map_bot : Psubgsub.map j = ⊥ := by
      calc
        Psubgsub.map j = (⁅Psubgsub, Rsub⁆).map j := by
          simpa using congrArg (fun S : Subgroup Sg => S.map j) hPsubgsub_eq_comm
        _ = ⁅Psubgsub.map j, Rsub.map j⁆ := by
          simpa using (Subgroup.map_commutator (H₁ := Psubgsub) (H₂ := Rsub) j)
        _ = ⊥ := by
          apply (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Psubgsub.map j) (H₂ := Rsub.map j)).2
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (IsMulCommutative.is_comm (M := I)).comm y x
    have hPsubgsub_trivQ : ActsTrivially (A := ↥Psubgsub) (G := ↥K ⧸ Z) := by
      intro b x
      have hbmap : j b ∈ Psubgsub.map j := Subgroup.mem_map_of_mem j b.2
      have hbbot : j b ∈ (⊥ : Subgroup I) := by simpa [hPsubgsub_map_bot] using hbmap
      have hbone : j b = 1 := by simpa using hbbot
      have hbval : (ι (b : Sg) : MulAut (↥K ⧸ Z)) = 1 := by
        change ((j b : I) : MulAut (↥K ⧸ Z)) = 1
        exact congrArg Subtype.val hbone
      have hb := congrArg (fun f : MulAut (↥K ⧸ Z) => f x) hbval
      change b • x = x at hb
      exact hb
    let C : Subgroup K := commutatorAction (A := ↥Psub) (G := ↥K)
    have hC_le_Z : C ≤ Z := by
      have hC_eq :
          C = Subgroup.closure {x : K | ∃ b : Psub, ∃ g : K, x = g⁻¹ * (b • g)} := by
        change commutatorAction (A := ↥Psub) (G := ↥K) =
            Subgroup.closure {x : K | ∃ b : Psub, ∃ g : K, x = g⁻¹ * (b • g)}
        exact commutatorAction_eq_closure (G := ↥K) (A := ↥Psub)
      rw [hC_eq]
      refine (Subgroup.closure_le (K := Z)).2 ?_
      intro x hx
      rcases hx with ⟨b, g, rfl⟩
      let bPsubg : Psubg := ⟨((b : H) : G), Subgroup.mem_map_of_mem H.subtype b.2⟩
      let bSg : Psubgsub := ⟨⟨((b : H) : G), Subgroup.mem_sup_left bPsubg.2⟩, by
        show (((⟨((b : H) : G), Subgroup.mem_sup_left bPsubg.2⟩ : Sg) : G) ∈ Psubg)
        exact bPsubg.2⟩
      have hbfix : bSg • ((g : K) : ↥K ⧸ Z) = (g : ↥K ⧸ Z) := hPsubgsub_trivQ bSg ((g : K) : ↥K ⧸ Z)
      have hbsmul : (bSg • g : K) = b • g := by
        apply Subtype.ext
        apply H.subtype_injective
        calc
          H.subtype (((bSg : Psubgsub) • g : K) : H) =
              H.subtype ((((bSg : Psubgsub) : Sg) • (g : H) : H)) := by
            rfl
          _ =
              (((bSg : Psubgsub) : Sg) : G) * (g : H) * ((((bSg : Psubgsub) : Sg) : G)⁻¹) := by
            simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
          _ = ((b : H) : G) * (g : H) * (((b : H) : G)⁻¹) := by
            simp [bSg]
          _ = H.subtype ((b • g : K) : H) := by
            symm
            simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      have hbfix' : ((b • g : K) : ↥K ⧸ Z) = (g : ↥K ⧸ Z) := by
        rw [← hbsmul]
        change bSg • ((g : K) : ↥K ⧸ Z) = (g : ↥K ⧸ Z)
        exact hbfix
      have hqone : (((g⁻¹ * (b • g) : K) : ↥K ⧸ Z)) = 1 := by
        calc
          (((g⁻¹ * (b • g) : K) : ↥K ⧸ Z)) = (g : ↥K ⧸ Z)⁻¹ * ((b • g : K) : ↥K ⧸ Z) := by
            simp
          _ = (g : ↥K ⧸ Z)⁻¹ * (g : ↥K ⧸ Z) := by rw [hbfix']
          _ = 1 := by simp
      exact (QuotientGroup.eq_one_iff (N := Z) (g⁻¹ * (b • g))).mp hqone
    have hK_eq_commP : K = ⁅K, Psub⁆ :=
      theorem_3_6_K_eq_commutator_with_P H R R₀ p hind hsolvG hodd hHR hcopHR hR₀_le
        hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit
        hP_p hPK_ne_bot hproper
    have hcomm_map :
        (commutatorAction (A := ↥Psub) (G := ↥K)).map K.subtype = ⁅K, Psub⁆ := by
      exact commutatorAction_subgroup_conj_map_eq_commutator K Psub hPsub_normK
    have hK_le_Zmap : K ≤ Z.map K.subtype := by
      intro x hx
      have hxcomm : x ∈ ⁅K, Psub⁆ := by
        rw [← hK_eq_commP]
        exact hx
      have hxC' : x ∈ (commutatorAction (A := ↥Psub) (G := ↥K)).map K.subtype := by
        rw [hcomm_map]
        exact hxcomm
      have hxC : x ∈ C.map K.subtype := by
        change x ∈ (commutatorAction (A := ↥Psub) (G := ↥K)).map K.subtype
        exact hxC'
      exact (Subgroup.map_mono hC_le_Z) hxC
    have hZmap_le_K : Z.map K.subtype ≤ K := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
      exact z.2
    have hZmap_eq_K : Z.map K.subtype = K := le_antisymm hZmap_le_K hK_le_Zmap
    have htop_map : (⊤ : Subgroup K).map K.subtype = K := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, by simp, rfl⟩
    have hZ_top : Z = ⊤ := by
      apply (Subgroup.map_injective (f := K.subtype) K.subtype_injective)
      calc
        Z.map K.subtype = K := hZmap_eq_K
        _ = (⊤ : Subgroup K).map K.subtype := htop_map.symm
    exact (hK_comm <| by
      refine ⟨⟨?_⟩⟩
      intro x y
      have hxZ : x ∈ Z := by simp [hZ_top]
      exact (Subgroup.mem_center_iff.mp hxZ y).symm).elim

set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.theorem_3_6_K_card_gt_q_sq
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H)
    (K : Subgroup H) (P : Subgroup (normalizerOf K)) :
    let V : Subgroup H := fittingSubgroup H
    let q : ↥H →* (↥H ⧸ V) := QuotientGroup.mk' V
    let Fbar : Subgroup (↥H ⧸ V) := fittingSubgroup (↥H ⧸ V)
    V ⊔ K = Fbar.comap q →
    Disjoint V K →
    (hK_inv : IsInvariant (↥R) (↥H) K) →
    IsInvariant (↥R) (↥H) (normalizerOf K) →
    IsInvariant (↥R) (↥H) (normalizerSubtypeMap K P) →
    V ⊔ normalizerOf K = ⊤ →
    V ⊓ normalizerOf K = ⊥ →
    (K.subgroupOf (normalizerOf K)) = fittingSubgroup (normalizerOf K) →
    subgroupCentralizerIn (⊤ : Subgroup H) K ≤ K →
    IsPGroup p P →
    ⁅normalizerSubtypeMap K P, K⁆ ≠ ⊥ →
    (∀ X : Subgroup H, X ≤ K →
      IsInvariant (↥R) (↥H) X →
      normalizerSubtypeMap K P ≤ Subgroup.normalizer (X : Set H) →
      X < K →
      ⁅X, normalizerSubtypeMap K P⁆ = ⊥) →
    R = R₀ →
    let _ : IsInvariant (↥R) (↥H) K := hK_inv
    ∃ qK : ℕ,
      Nat.Prime qK ∧ qK ≠ p ∧ qK ≠ Nat.card R₀ ∧
        IsElementaryAbelian qK ↥K ∧ qK ^ 2 < Nat.card K := by
  set_option maxHeartbeats 800000 in
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  dsimp
  intro hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K
    hP_p hPK_ne_bot hproper hR_eq
  let Psub : Subgroup H := normalizerSubtypeMap K P
  have hPsub_le_NK : Psub ≤ normalizerOf K := by
    simpa [Psub, normalizerSubtypeMap] using (Subgroup.map_subtype_le P)
  have hPsub_normK : Psub ≤ Subgroup.normalizer (K : Set H) := by
    simpa [normalizerOf] using hPsub_le_NK
  let : IsInvariant (↥R) (↥H) K := hK_inv
  have : Subgroup.Normalizes Psub K := ⟨hPsub_normK⟩
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    exact hPK_ne_bot (by simp [hK_bot])
  let : Nontrivial ↥K := K.nontrivial_iff_ne_bot.mpr hK_ne_bot
  obtain ⟨qK, hqK_prime, hqK_ne_p, hqK_ne_R₀, hK_elem⟩ :=
    theorem_3_6_K_elementaryAbelian H R R₀ p hind hsolvG hodd hHR hcopHR hR₀_le
      hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv hVNK_sup
      hVinfNK_bot hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper hR_eq
  have : Fact qK.Prime := ⟨hqK_prime⟩
  have hqK_pgroup : IsPGroup qK ↥K := IsElementaryAbelian.isPGroup qK ↥K
  have : Fact (IsPGroup qK ↥K) := ⟨hqK_pgroup⟩
  let Cfix : Subgroup K := fixedPointSubgroup (↥R) (↥K)
  obtain ⟨qK', hqK'_prime, hqK_fix_card', _hfix_inf_comm_bot⟩ :=
    theorem_3_6_K_fixed_card_eq_q_and_inf_commutator_eq_bot H R R₀ p hind hsolvG hodd
      hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj
      hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K hP_p hPK_ne_bot
      hproper hR_eq
  have hq_eq : qK' = qK := by
    have hCfix_q : IsPGroup qK Cfix :=
      hqK_pgroup.of_injective Cfix.subtype Cfix.subtype_injective
    have hCfix_card_ne_one : Nat.card Cfix ≠ 1 := by
      intro hcard_one
      exact hqK'_prime.ne_one (hqK_fix_card'.symm.trans hcard_one)
    have hqK_dvd_card : qK ∣ Nat.card Cfix :=
      (hCfix_q.card_eq_or_dvd).resolve_left hCfix_card_ne_one
    have hcardCfix : Nat.card Cfix = qK' := by
      simpa [Cfix] using hqK_fix_card'
    have hqK_dvd_qK' : qK ∣ qK' := by
      rw [← hcardCfix]
      exact hqK_dvd_card
    exact ((Nat.prime_dvd_prime_iff_eq hqK_prime hqK'_prime).1 hqK_dvd_qK').symm
  have hqK_fix_card : Nat.card Cfix = qK := by
    exact hqK_fix_card'.trans hq_eq
  let Kg : Subgroup G := K.map H.subtype
  have hRnormKg : R ≤ Subgroup.normalizer (Kg : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyK, rfl⟩
      exact Subgroup.mem_map_of_mem H.subtype <|
        (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := K) ⟨a, ha⟩ y).1 hyK
    · intro hx
      have ha_inv : a⁻¹ ∈ R := R.inv_mem ha
      rcases Subgroup.mem_map.mp hx with ⟨y, hyK, hyx⟩
      refine Subgroup.mem_map.mpr ?_
      let yK : K := ⟨y, hyK⟩
      refine ⟨(⟨a⁻¹, ha_inv⟩ : R) • yK,
        (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := K) ⟨a⁻¹, ha_inv⟩ yK).1 hyK, ?_⟩
      have hyx' : H.subtype ((((⟨a⁻¹, ha_inv⟩ : R) • yK : K) : H)) = x := by
        calc
          H.subtype ((((⟨a⁻¹, ha_inv⟩ : R) • yK : K) : H)) =
              H.subtype ((⟨a⁻¹, ha_inv⟩ : R) • (y : H)) := by
            rfl
          _ = (a : G)⁻¹ * (y : H) * (a : G) := by
            simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
          _ = (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * (a : G) := by
            simpa using congrArg (fun z : G => (a : G)⁻¹ * z * (a : G)) hyx
          _ = x := by simp [mul_assoc]
      exact hyx'
  have hKR_nonbot : ⁅Kg, R⁆ ≠ ⊥ := by
    simpa [Kg, hR_eq] using
      theorem_3_6_r0_commutator_nontrivial H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup
        hVinfNK_bot hKsub_fit hCH_le_K
  have hcard_ne_q : Nat.card K ≠ qK := by
    intro hcardKq
    have hCfix_top : Cfix = ⊤ := by
      apply (Subgroup.card_eq_iff_eq_top (H := Cfix)).1
      simpa [hcardKq] using hqK_fix_card
    have htrivR : ActsTrivially (A := ↥R) (G := ↥K) := by
      intro a x
      have hxfix : x ∈ Cfix := by simp [Cfix, hCfix_top]
      exact hxfix a
    have : Subgroup.Normalizes R Kg := ⟨hRnormKg⟩
    have htrivKg : ActsTrivially (A := ↥R) (G := ↥Kg) := by
      intro a x
      rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hyx⟩
      have hyfix : a • (⟨y, hy⟩ : K) = ⟨y, hy⟩ := htrivR a ⟨y, hy⟩
      have hyfixH : ((a • (⟨y, hy⟩ : K) : K) : H) = y := congrArg Subtype.val hyfix
      have hyfixH' : a • (y : H) = y := by
        change a • (y : H) = y at hyfixH
        exact hyfixH
      have hyfixG : (a : G) * (y : H) * (a : G)⁻¹ = y := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormH] using
          congrArg H.subtype hyfixH'
      apply Subtype.ext
      calc
        ((a • x : Kg) : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        _ = (a : G) * (y : H) * (a : G)⁻¹ := by
          simpa using congrArg (fun z : G => (a : G) * z * (a : G)⁻¹) hyx.symm
        _ = y := hyfixG
        _ = x := by simpa using hyx
    have hKR_bot : ⁅R, Kg⁆ = ⊥ :=
      commutator_eq_bot_of_actsTrivially_subgroup_conj Kg R hRnormKg htrivKg
    exact hKR_nonbot (by simpa [Subgroup.commutator_comm] using hKR_bot)
  have hcard_ne_qsq : Nat.card K ≠ qK ^ 2 := by
    intro hcardKq2
    let Psubg : Subgroup G := Psub.map H.subtype
    let Sg : Subgroup G := Psubg ⊔ R
    have hPsubg_le_H : Psubg ≤ H := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.2
    have hPsubg_le_normKg : Psubg ≤ Subgroup.normalizer (Kg : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
        rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
        let kK : K := ⟨k, hk⟩
        have hkmap :
            H.subtype ((((⟨b, hb⟩ : Psub) • kK : K) : H)) ∈ Kg :=
          Subgroup.mem_map_of_mem H.subtype (((⟨b, hb⟩ : Psub) • kK).2)
        change H.subtype b * H.subtype k * (H.subtype b)⁻¹ ∈ Kg at hkmap
        exact hkmap
      · intro hx
        rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
        have hb_inv : b⁻¹ ∈ Psub := Psub.inv_mem hb
        rcases Subgroup.mem_map.mp hx with ⟨k, hk, hkx⟩
        let kK : K := ⟨k, hk⟩
        have hkmap :
            H.subtype ((((⟨b⁻¹, hb_inv⟩ : Psub) • kK : K) : H)) ∈ Kg :=
          Subgroup.mem_map_of_mem H.subtype (((⟨b⁻¹, hb_inv⟩ : Psub) • kK).2)
        have hkx' :
            H.subtype ((((⟨b⁻¹, hb_inv⟩ : Psub) • kK : K) : H)) = x := by
          calc
            H.subtype ((((⟨b⁻¹, hb_inv⟩ : Psub) • kK : K) : H)) =
                (b : G)⁻¹ * (k : H) * (b : G) := by
              simp [kK, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
                mul_assoc]
            _ = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * (b : G) := by
              simpa using congrArg (fun z : G => (b : G)⁻¹ * z * (b : G)) hkx
            _ = x := by simp [mul_assoc]
        exact hkx' ▸ hkmap
    have hSg_le_normKg : Sg ≤ Subgroup.normalizer (Kg : Set G) :=
      sup_le hPsubg_le_normKg hRnormKg
    have hR_le_normPsubg : R ≤ Subgroup.normalizer (Psubg : Set G) := by
      refine subgroup_le_normalizer_of_conj_mem Psubg R ?_
      intro a x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy' : (⟨a, a.2⟩ : R) • y ∈ Psub :=
        (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := Psub) ⟨a, a.2⟩ y).1 hy
      exact Subgroup.mem_map_of_mem H.subtype hy'
    have hSg_le_normPsubg : Sg ≤ Subgroup.normalizer (Psubg : Set G) := by
      exact sup_le Psubg.le_normalizer hR_le_normPsubg
    have hSg_le_normH : Sg ≤ Subgroup.normalizer H := by
      exact sup_le (hPsubg_le_H.trans (Subgroup.le_normalizer_of_normal (H := H))) hRnormH
    have : Subgroup.Normalizes Sg H := ⟨hSg_le_normH⟩
    have hPsubgsub_normal : (Psubg.subgroupOf Sg).Normal := by
      simpa [Sg] using
        (Subgroup.normal_subgroupOf_of_le_normalizer (H := Sg) (N := Psubg) hSg_le_normPsubg)
    have hPsubgR_disj : Disjoint Psubg R := hHR.disjoint.mono_left hPsubg_le_H
    let Psubgsub : Subgroup Sg := Psubg.subgroupOf Sg
    let Rsub : Subgroup Sg := R.subgroupOf Sg
    have hPsubgsubRsub_disj : Disjoint Psubgsub Rsub := by
      rw [Subgroup.disjoint_def]
      intro x hxP hxR
      apply Subtype.ext
      exact (Subgroup.disjoint_def.mp hPsubgR_disj)
        (by simpa [Psubgsub, Subgroup.mem_subgroupOf] using hxP)
        (by simpa [Rsub, Subgroup.mem_subgroupOf] using hxR)
    have hsub_sup : Psubgsub ⊔ Rsub = ⊤ := by
      calc
        Psubgsub ⊔ Rsub = (Psubg ⊔ R).subgroupOf Sg := by
          symm
          exact Subgroup.subgroupOf_sup (A := Psubg) (A' := R) (B := Sg) le_sup_left le_sup_right
        _ = ⊤ := by simp [Sg]
    have hPsubgsub_compl : Psubgsub.IsComplement' Rsub := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hPsubgsubRsub_disj ?_
      ext x
      constructor
      · intro _; trivial
      · intro _
        have hxsup : x ∈ Psubgsub ⊔ Rsub := by simp [hsub_sup]
        rcases (Subgroup.mem_sup_of_normal_left (s := Psubgsub) (t := Rsub) (x := x)).1 hxsup with
          ⟨y, hy, z, hz, rfl⟩
        exact Set.mem_mul.mpr ⟨y, hy, z, hz, rfl⟩
    have hPsub_p : IsPGroup p Psub := by
      change IsPGroup p (normalizerSubtypeMap K P)
      exact isPGroup_normalizerSubtypeMap K P hP_p
    have hPsubg_p : IsPGroup p Psubg := by
      simpa [Psubg] using hPsub_p.map H.subtype
    have hPsubg_card_eq : Nat.card Psubg = Nat.card Psub := by
      simpa [Psubg] using
        (Subgroup.card_map_of_injective (K := Psub) (f := H.subtype) H.subtype_injective)
    have hcop_q_Psubg : Nat.Coprime qK (Nat.card Psubg) := by
      obtain ⟨n, hcardPsub⟩ := hPsub_p.exists_card_eq
      rw [hPsubg_card_eq, hcardPsub]
      exact (Nat.Prime.coprime_iff_not_dvd hqK_prime).2 (by
        intro hdiv
        exact hqK_ne_p ((Nat.prime_dvd_prime_iff_eq hqK_prime hp).1 (hqK_prime.dvd_of_dvd_pow hdiv)))
    have hR_prime : Nat.Prime (Nat.card R) := by simpa [hR_eq] using hR₀_prime
    have hcop_q_R : Nat.Coprime qK (Nat.card R) := by
      exact (Nat.Prime.coprime_iff_not_dvd hqK_prime).2 (by
        intro hdiv
        exact hqK_ne_R₀ (hR_eq ▸ (Nat.prime_dvd_prime_iff_eq hqK_prime hR_prime).1 hdiv))
    have hPsubgsub_card_eq : Nat.card Psubgsub = Nat.card Psubg := by
      simpa [Psubgsub] using Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := Psubg) (K := Sg) le_sup_left).toEquiv
    have hRsub_card_eq : Nat.card Rsub = Nat.card R := by
      simpa [Rsub] using Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := R) (K := Sg) le_sup_right).toEquiv
    have hSg_card : Nat.card Sg = Nat.card Psubg * Nat.card R := by
      rw [← hPsubgsub_compl.card_mul_card, hPsubgsub_card_eq, hRsub_card_eq]
    have hcop_q_Sg : Nat.Coprime qK (Nat.card Sg) := by
      rw [hSg_card]
      exact Nat.Coprime.mul_right hcop_q_Psubg hcop_q_R
    have hoddSg : Odd (Nat.card Sg) := odd_of_card_dvd hodd (Subgroup.card_subgroup_dvd_card Sg)
    have hK_invS : IsInvariant (↥Sg) (↥H) K := by
      refine ⟨?_⟩
      have hforward : ∀ a : Sg, ∀ x : H, x ∈ K → a • x ∈ K := by
        intro a x hx
        have hnorm : (a : G) ∈ Subgroup.normalizer (Kg : Set G) := hSg_le_normKg a.2
        have hxmap : (x : G) ∈ Kg := Subgroup.mem_map_of_mem H.subtype hx
        have hxmap' : (a : G) * (x : G) * (a : G)⁻¹ ∈ Kg :=
          (Subgroup.mem_normalizer_iff.mp hnorm) (x : G) |>.1 hxmap
        have hxsmul : ((a • x : H) : G) ∈ Kg := by
          simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hSg_le_normH] using
            hxmap'
        rcases Subgroup.mem_map.mp hxsmul with ⟨y, hy, hy_eq⟩
        have hxy : (a • x : H) = y := H.subtype_injective hy_eq.symm
        simpa [hxy] using hy
      intro a x
      constructor
      · exact hforward a x
      · intro hx
        have h := hforward a⁻¹ (a • x) hx
        simpa [smul_smul] using h
    let : IsInvariant (↥Sg) (↥H) K := hK_invS
    let : CommGroup K := IsMulCommutative.instCommGroup
    let ι : Sg →* MulAut (↥K) := MulDistribMulAction.toMulAut (G := ↥Sg) (M := ↥K)
    let I : Subgroup (MulAut (↥K)) := ι.range
    let ρI : Representation (ZMod qK) I (Additive (↥K)) := {
      toFun := fun a =>
        let eAdd : Additive (↥K) ≃+ Additive (↥K) := MulEquiv.toAdditive (a : MulAut _)
        let eLin : Additive (↥K) ≃ₗ[ZMod qK] Additive (↥K) :=
          eAdd.toLinearEquiv (fun c x => by
            simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
        eLin.toLinearMap
      map_one' := by
        ext x
        apply Additive.toMul.injective
        simp
      map_mul' := by
        intro a' b'
        ext x
        apply Additive.toMul.injective
        simp }
    have hρI_inj : Function.Injective ρI := by
      intro a' b' hab
      apply Subtype.ext
      ext x
      have hx := congrArg (fun f => f (Additive.ofMul x)) hab
      have hx' := congrArg Additive.toMul hx
      simpa [ρI] using hx'
    have hI_card_dvd_Sg : Nat.card I ∣ Nat.card Sg := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ι).toEquiv]
      exact Subgroup.card_quotient_dvd_card (s := ι.ker)
    have hoddI : Odd (Nat.card I) := odd_of_card_dvd hoddSg hI_card_dvd_Sg
    have hcop_q_I : Nat.Coprime qK (Nat.card I) := Nat.Coprime.of_dvd_right hI_card_dvd_Sg hcop_q_Sg
    have hchar_not_dvd_I : ¬ ringChar (ZMod qK) ∣ Nat.card I := by
      simpa [ZMod.ringChar_zmod_n] using (Nat.Prime.coprime_iff_not_dvd hqK_prime).1 hcop_q_I
    let : FiniteDimensional (ZMod qK) (Additive (↥K)) := Module.Finite.of_finite
    have hfinK : Module.finrank (ZMod qK) (Additive (↥K)) = 2 := by
      have hcard_pow :
          Nat.card (Additive (↥K)) =
            qK ^ Module.finrank (ZMod qK) (Additive (↥K)) := by
        simpa [Nat.card_eq_fintype_card, ZMod.card] using
          (Module.natCard_eq_pow_finrank (K := ZMod qK) (V := Additive (↥K)))
      have hinj := Nat.pow_right_injective (a := qK) hqK_prime.two_le
      apply hinj
      calc
        qK ^ Module.finrank (ZMod qK) (Additive (↥K)) = Nat.card (Additive (↥K)) := hcard_pow.symm
        _ = Nat.card (↥K) := by rfl
        _ = qK ^ 2 := hcardKq2
    have hI_comm : IsMulCommutative ↥I := by
      exact theorem_2_6_a (F := ZMod qK) hoddI hfinK hρI_inj hchar_not_dvd_I
    let j : Sg →* I := ι.rangeRestrict
    have hPsubgsub_eq_comm : Psubgsub = ⁅Psubgsub, Rsub⁆ := by
      apply (Subgroup.map_injective (f := Sg.subtype) Sg.subtype_injective)
      calc
        Psubgsub.map Sg.subtype = Psubg := by
          simpa [Psubgsub] using
            Subgroup.map_subgroupOf_eq_of_le (G := G) (H := Psubg) (K := Sg) le_sup_left
        _ = ⁅Psubg, R₀⁆ := (theorem_3_6_pSubgroup_eq_commutator_with_R₀ H R R₀ p hind hsolvG
          hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup P hP_p
          hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K).1
        _ = ⁅Psubg, R⁆ := by simp [hR_eq]
        _ = (⁅Psubgsub, Rsub⁆).map Sg.subtype := by
          symm
          simpa [Psubgsub, Rsub] using
            commutator_subgroupOf_map_eq (S := Sg) (H := R) (R := Psubg) le_sup_right le_sup_left
    have hPsubgsub_map_bot : Psubgsub.map j = ⊥ := by
      calc
        Psubgsub.map j = (⁅Psubgsub, Rsub⁆).map j := by
          simpa using congrArg (fun S : Subgroup Sg => S.map j) hPsubgsub_eq_comm
        _ = ⁅Psubgsub.map j, Rsub.map j⁆ := by
          simpa using (Subgroup.map_commutator (H₁ := Psubgsub) (H₂ := Rsub) j)
        _ = ⊥ := by
          apply (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Psubgsub.map j)
            (H₂ := Rsub.map j)).2
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (IsMulCommutative.is_comm (M := I)).comm y x
    have hPsubgsub_trivK : ActsTrivially (A := ↥Psubgsub) (G := ↥K) := by
      intro b x
      have hbmap : j b ∈ Psubgsub.map j := Subgroup.mem_map_of_mem j b.2
      have hbbot : j b ∈ (⊥ : Subgroup I) := by simpa [hPsubgsub_map_bot] using hbmap
      have hbone : j b = 1 := by simpa using hbbot
      have hbval : (ι (b : Sg) : MulAut (↥K)) = 1 := by
        change ((j b : I) : MulAut (↥K)) = 1
        exact congrArg Subtype.val hbone
      have hb := congrArg (fun f : MulAut (↥K) => f x) hbval
      change b • x = x at hb
      exact hb
    have htrivPsub : ActsTrivially (A := ↥Psub) (G := ↥K) := by
      intro b g
      let bPsubg : Psubg := ⟨((b : H) : G), Subgroup.mem_map_of_mem H.subtype b.2⟩
      let bSg : Psubgsub := ⟨⟨((b : H) : G), Subgroup.mem_sup_left bPsubg.2⟩, by
        show (((⟨((b : H) : G), Subgroup.mem_sup_left bPsubg.2⟩ : Sg) : G) ∈ Psubg)
        exact bPsubg.2⟩
      have hbfix : bSg • g = g := hPsubgsub_trivK bSg g
      have hbsmul : (bSg • g : K) = b • g := by
        apply Subtype.ext
        apply H.subtype_injective
        calc
          H.subtype (((bSg : Psubgsub) • g : K) : H) =
              H.subtype ((((bSg : Psubgsub) : Sg) • (g : H) : H)) := by
            rfl
          _ =
              (((bSg : Psubgsub) : Sg) : G) * (g : H) * ((((bSg : Psubgsub) : Sg) : G)⁻¹) := by
            simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
          _ = ((b : H) : G) * (g : H) * (((b : H) : G)⁻¹) := by
            simp [bSg]
          _ = H.subtype ((b • g : K) : H) := by
            symm
            simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      simpa [hbsmul] using hbfix
    have hPK_bot : ⁅Psub, K⁆ = ⊥ :=
      commutator_eq_bot_of_actsTrivially_subgroup_conj K Psub hPsub_normK htrivPsub
    exact hPK_ne_bot hPK_bot
  obtain ⟨nK, hnK_pos, hcardKq⟩ :=
    (IsPGroup.nontrivial_iff_card (p := qK) (G := ↥K) (hG := hqK_pgroup)).mp inferInstance
  have hnK_ne_one : nK ≠ 1 := by
    intro hnK_one
    exact hcard_ne_q (by simp [hcardKq, hnK_one])
  have hnK_ne_two : nK ≠ 2 := by
    intro hnK_two
    exact hcard_ne_qsq (by simp [hcardKq, hnK_two])
  have htwo_lt_nK : 2 < nK := by
    by_contra! hle
    have hnK_le_two : nK ≤ 2 := hle
    rcases Nat.lt_or_eq_of_le hnK_le_two with (hlt | heq)
    · have hnK_le_one : nK ≤ 1 := Nat.le_of_lt_succ hlt
      rcases Nat.lt_or_eq_of_le hnK_le_one with (hlt1 | heq1)
      · have hnK_zero : nK = 0 := Nat.lt_one_iff.mp hlt1
        exact hnK_pos.ne' hnK_zero
      · exact hnK_ne_one heq1
    · exact hnK_ne_two heq
  have hpow_lt : qK ^ 2 < qK ^ nK := by
    exact Nat.pow_lt_pow_right hqK_prime.one_lt htwo_lt_nK
  refine ⟨qK, hqK_prime, hqK_ne_p, hqK_ne_R₀, hK_elem, ?_⟩
  simpa [hcardKq] using hpow_lt

public theorem CFSG.theorem_3_6_cyclic_quotient_card_eq_prime
    {K : Type*} [Group K] [Finite K] {q : ℕ} [Fact q.Prime]
    [IsElementaryAbelian q K] (Y : Subgroup K) (hcyc : IsCyclic (K ⧸ Y))
    (hY_ne_top : Y ≠ ⊤) :
    Nat.card (K ⧸ Y) = q := by
  let hQ_elem : IsElementaryAbelian q (K ⧸ Y) := {
    is_comm := inferInstance
    exponent_dvd_p := (Group.exponent_quotient_dvd (H := Y)).trans
      (IsElementaryAbelian.exponent_dvd_p q K)
  }
  let : IsElementaryAbelian q (K ⧸ Y) := hQ_elem
  let : Nontrivial (K ⧸ Y) := (QuotientGroup.nontrivial_iff (G := K) (N := Y)).2 hY_ne_top
  obtain ⟨x, hxorder⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K ⧸ Y)
  have hxpow : x ^ q = 1 := by
    exact
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent (K ⧸ Y) ∣ q by simpa using hQ_elem.exponent_dvd_p) x
  have horder_dvd_q : orderOf x ∣ q := orderOf_dvd_of_pow_eq_one hxpow
  have hcard_gt_one : 1 < Nat.card (K ⧸ Y) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have horder_ne_one : orderOf x ≠ 1 := by
    intro horder_one
    have : Nat.card (K ⧸ Y) = 1 := by rw [← hxorder, horder_one]
    rw [this] at hcard_gt_one
    exact lt_irrefl 1 hcard_gt_one
  have horder_eq_q : orderOf x = q :=
    (Fact.out : Nat.Prime q).eq_one_or_self_of_dvd (orderOf x) horder_dvd_q |>.resolve_left horder_ne_one
  calc
    Nat.card (K ⧸ Y) = orderOf x := hxorder.symm
    _ = q := horder_eq_q

public theorem CFSG.theorem_3_6_distinct_cyclic_quotients_sup_top
    {K : Type*} [Group K] [Finite K] {q : ℕ} [Fact q.Prime]
    [IsElementaryAbelian q K] (Y Z : Subgroup K)
    (hY_cyc : IsCyclic (K ⧸ Y)) (hZ_cyc : IsCyclic (K ⧸ Z))
    (hY_ne_top : Y ≠ ⊤) (hZ_ne_top : Z ≠ ⊤) (hYZ_ne : Y ≠ Z) :
    Y ⊔ Z = ⊤ := by
  have hY_index : Y.index = q := by
    simpa [Subgroup.index_eq_card] using theorem_3_6_cyclic_quotient_card_eq_prime Y hY_cyc hY_ne_top
  have hZ_index : Z.index = q := by
    simpa [Subgroup.index_eq_card] using theorem_3_6_cyclic_quotient_card_eq_prime Z hZ_cyc hZ_ne_top
  let U : Subgroup K := Y ⊔ Z
  have hU_index_dvd : U.index ∣ Y.index := Subgroup.index_dvd_of_le (show Y ≤ U by exact le_sup_left)
  by_contra hU_ne_top
  have hU_index_ne_one : U.index ≠ 1 := by
    intro hU_index_one
    exact hU_ne_top (Subgroup.index_eq_one.mp hU_index_one)
  have hU_index_eq_q : U.index = q :=
    (Fact.out : Nat.Prime q).eq_one_or_self_of_dvd U.index (hY_index ▸ hU_index_dvd) |>.resolve_left hU_index_ne_one
  have hcardU_eq : Nat.card U = Nat.card Y := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < q from (Fact.out : Nat.Prime q).pos)
    calc
      q * Nat.card U = U.index * Nat.card U := by rw [hU_index_eq_q]
      _ = Nat.card K := Subgroup.index_mul_card (H := U)
      _ = Y.index * Nat.card Y := (Subgroup.index_mul_card (H := Y)).symm
      _ = q * Nat.card Y := by rw [hY_index]
  have hY_eq_U : Y = U := Subgroup.eq_of_le_of_card_ge le_sup_left (by simp [hcardU_eq])
  have hZ_le_Y : Z ≤ Y := by
    intro z hz
    have hzU : z ∈ U := (show Z ≤ U from le_sup_right) hz
    rw [← hY_eq_U] at hzU
    exact hzU
  have hcardY_eq_cardZ : Nat.card Y = Nat.card Z := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < q from (Fact.out : Nat.Prime q).pos)
    calc
      q * Nat.card Y = Y.index * Nat.card Y := by rw [hY_index]
      _ = Nat.card K := Subgroup.index_mul_card (H := Y)
      _ = Z.index * Nat.card Z := (Subgroup.index_mul_card (H := Z)).symm
      _ = q * Nat.card Z := by rw [hZ_index]
  have hZ_eq_Y : Z = Y := Subgroup.eq_of_le_of_card_ge hZ_le_Y (by simp [hcardY_eq_cardZ])
  exact hYZ_ne hZ_eq_Y.symm

public theorem CFSG.theorem_3_6_hyperplane_fixed_iSup_top
    {K V : Type*} [Group K] [Finite K] [Group V] [Finite V]
    {q p : ℕ} [Fact q.Prime] [Fact p.Prime]
    [IsElementaryAbelian q K] [IsElementaryAbelian p V] [MulDistribMulAction K V]
    (hq_ne_p : q ≠ p) (hncyc : ¬ IsCyclic K) :
    (⨆ (Y : Subgroup K) (_ : IsCyclic (K ⧸ Y)), fixedPointSubgroup (↥Y) V) = ⊤ := by
  let : CommGroup K := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup q K) := ⟨IsElementaryAbelian.isPGroup q K⟩
  let hVp : IsPGroup p V := IsElementaryAbelian.isPGroup p V
  obtain ⟨n, hcardV⟩ := hVp.exists_card_eq
  have hcop_q_p : Nat.Coprime q p := by
    exact (Fact.out : Nat.Prime q).coprime_iff_not_dvd.2 (by
      intro hdiv
      exact hq_ne_p ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime q) (Fact.out : Nat.Prime p)).1 hdiv))
  have hcop_q_V : Nat.Coprime q (Nat.card V) := by
    rw [hcardV]
    exact hcop_q_p.pow_right n
  exact proposition_1_16_b (G := V) (A := K) q hcop_q_V hncyc

public theorem CFSG.theorem_3_6_hyperplane_fixed_disjoint
    {K V : Type*} [Group K] [Finite K] [Group V] [MulDistribMulAction K V]
    {q : ℕ} [Fact q.Prime] [IsElementaryAbelian q K]
    (hfix_top : fixedPointSubgroup (↥(⊤ : Subgroup K)) V = ⊥)
    (Y Z : Subgroup K)
    (hY_cyc : IsCyclic (K ⧸ Y)) (hZ_cyc : IsCyclic (K ⧸ Z))
    (hY_fix_ne_bot : fixedPointSubgroup (↥Y) V ≠ ⊥)
    (hZ_fix_ne_bot : fixedPointSubgroup (↥Z) V ≠ ⊥)
    (hYZ_ne : Y ≠ Z) :
    Disjoint (fixedPointSubgroup (↥Y) V) (fixedPointSubgroup (↥Z) V) := by
  let : CommGroup K := IsMulCommutative.instCommGroup
  have hY_ne_top : Y ≠ ⊤ := by
    intro hY_top
    apply hY_fix_ne_bot
    subst hY_top
    simpa using hfix_top
  have hZ_ne_top : Z ≠ ⊤ := by
    intro hZ_top
    apply hZ_fix_ne_bot
    subst hZ_top
    simpa using hfix_top
  have hsup : Y ⊔ Z = ⊤ :=
    theorem_3_6_distinct_cyclic_quotients_sup_top (q := q) Y Z hY_cyc hZ_cyc hY_ne_top hZ_ne_top
      hYZ_ne
  rw [Subgroup.disjoint_def]
  intro x hxY hxZ
  have hxY' : ∀ y : Y, y • x = x := by
    simpa [FixedPoints.mem_subgroup] using hxY
  have hxZ' : ∀ z : Z, z • x = x := by
    simpa [FixedPoints.mem_subgroup] using hxZ
  have hxsup : x ∈ fixedPointSubgroup (↥(Y ⊔ Z)) V := by
    rw [FixedPoints.mem_subgroup]
    intro a
    rcases (Subgroup.mem_sup_of_normal_left (s := Y) (t := Z) (x := (a : K))).1 a.2 with
      ⟨y, hy, z, hz, hyz⟩
    let yY : Y := ⟨y, hy⟩
    let zZ : Z := ⟨z, hz⟩
    calc
      a • x = (y * z) • x := by
        change ((a : K) • x) = ((y * z : K) • x)
        rw [← hyz]
      _ = y • (z • x) := by simp [mul_smul]
      _ = y • x := by
        have hz := hxZ' zZ
        change z • x = x at hz
        rw [hz]
      _ = x := by
        have hy := hxY' yY
        change y • x = x at hy
        exact hy
  have hxTop : x ∈ fixedPointSubgroup (↥(⊤ : Subgroup K)) V := by
    simpa [hsup] using hxsup
  have hxbot : x ∈ (⊥ : Subgroup V) := by
    simpa [hfix_top] using hxTop
  simpa using hxbot

public theorem CFSG.theorem_3_6_hyperplane_fixed_singleton_false
    {K V : Type*} [CommGroup K] [Group V] [MulDistribMulAction K V]
    (hfaith : actionCentralizerIn (A := K) (G := V) (⊤ : Subgroup K) = ⊥)
    {Y : Subgroup K} (hY_cyc : IsCyclic (K ⧸ Y)) (hncyc : ¬ IsCyclic K)
    (hfix_top : fixedPointSubgroup (↥Y) V = ⊤) :
    False := by
  have hY_ne_bot : Y ≠ ⊥ := by
    intro hY_bot
    apply hncyc
    subst hY_bot
    have hcyc_bot : IsCyclic (K ⧸ (⊥ : Subgroup K)) := hY_cyc
    exact ((QuotientGroup.quotientBot (G := K)).isCyclic).1 hcyc_bot
  have hY_le_cent : Y ≤ actionCentralizerIn (A := K) (G := V) (⊤ : Subgroup K) := by
    intro y hy
    refine ⟨by simp, ?_⟩
    change y ∈ fixingSubgroup K (Set.univ : Set V)
    rw [mem_fixingSubgroup_iff]
    intro v _hv
    have hvfix : v ∈ fixedPointSubgroup (↥Y) V := by
      simp [hfix_top]
    exact hvfix ⟨y, hy⟩
  have hY_eq_bot : Y = ⊥ := by
    apply bot_unique
    intro y hy
    have hy' : y ∈ actionCentralizerIn (A := K) (G := V) (⊤ : Subgroup K) := hY_le_cent hy
    simpa [hfaith] using hy'
  exact hY_ne_bot hY_eq_bot

open scoped Pointwise

private theorem CFSG.theorem_3_6_fixedPointSubgroup_subgroup_eq_bot_of_disjoint
    {A : Type*} [Group A] {M : Type*} [Group M] [MulDistribMulAction A M]
    (U : Subgroup M) [IsInvariant A M U]
    (hdisj : Disjoint U (fixedPointSubgroup A M)) :
    fixedPointSubgroup A (↥U) = ⊥ := by
  apply bot_unique
  intro x hx
  have hxU : (x : M) ∈ U := x.2
  have hxFix : (x : M) ∈ fixedPointSubgroup A M := by
    rw [FixedPoints.mem_subgroup] at hx ⊢
    intro a
    exact congrArg Subtype.val (hx a)
  have hxbot : (x : M) ∈ (⊥ : Subgroup M) := by
    exact (Subgroup.disjoint_def.mp hdisj) hxU hxFix
  simpa using hxbot

private theorem CFSG.theorem_3_6_fixedPointSubgroup_sup_eq_bot_of_disjoint
    {A : Type*} [Group A] [Finite A]
    {M : Type*} [Group M] [Finite M] [IsMulCommutative M] [MulDistribMulAction A M]
    (U W : Subgroup M) [IsInvariant A M U] [IsInvariant A M W] [IsInvariant A M (U ⊔ W)]
    (hdisj : Disjoint U W)
    (hfixU : fixedPointSubgroup A (↥U) = ⊥)
    (hfixW : fixedPointSubgroup A (↥W) = ⊥) :
    fixedPointSubgroup A (↥(U ⊔ W)) = ⊥ := by
  let S : Subgroup M := U ⊔ W
  -- letI : MulDistribMulAction A (↥U) := instMulDistribMulAction_subtype (A := A) (G := M) U
  -- letI : MulDistribMulAction A (↥W) := instMulDistribMulAction_subtype (A := A) (G := M) W
  -- letI : MulDistribMulAction A (↥S) := instMulDistribMulAction_subtype (A := A) (G := M) S
  apply bot_unique
  intro x hx
  rw [FixedPoints.mem_subgroup] at hx
  rcases (Subgroup.mem_sup_of_normal_left (s := U) (t := W) (x := (x : M))).1 x.2 with
    ⟨u, huU, w, hwW, huw_eq⟩
  have hunique :
      ∀ {u₁ u₂ w₁ w₂ : M}, u₁ ∈ U → u₂ ∈ U → w₁ ∈ W → w₂ ∈ W →
        u₁ * w₁ = u₂ * w₂ → u₁ = u₂ ∧ w₁ = w₂ := by
    intro u₁ u₂ w₁ w₂ hu₁ hu₂ hw₁ hw₂ hEq
    have huw :
        u₁ * u₂⁻¹ ∈ U ∧ u₁ * u₂⁻¹ ∈ W := by
      constructor
      · exact U.mul_mem hu₁ (U.inv_mem hu₂)
      · have hEq' : u₁ * u₂⁻¹ = w₂ * w₁⁻¹ := by
          calc
            u₁ * u₂⁻¹ = (u₂ * w₂) * (w₁⁻¹ * u₂⁻¹) := by
              rw [← hEq]
              simp [mul_assoc]
            _ = (u₂ * u₂⁻¹) * (w₂ * w₁⁻¹) := by
              ac_rfl
            _ = w₂ * w₁⁻¹ := by
              simp
        rw [hEq']
        exact W.mul_mem hw₂ (W.inv_mem hw₁)
    have hu_eq : u₁ = u₂ := by
      have hbot : u₁ * u₂⁻¹ = 1 := by
        exact (Subgroup.disjoint_def.mp hdisj) huw.1 huw.2
      calc
        u₁ = (u₁ * u₂⁻¹) * u₂ := by simp [mul_assoc]
        _ = u₂ := by simp [hbot]
    have hw_eq : w₁ = w₂ := by
      calc
        w₁ = u₁⁻¹ * (u₂ * w₂) := by rw [← hEq]; simp
        _ = w₂ := by simp [hu_eq]
    exact ⟨hu_eq, hw_eq⟩
  have hu_fix : ∀ a : A, a • u = u := by
    intro a
    have hau : a • u ∈ U := (IsInvariant.invariant (A := A) (G := M) (H := U) a u).1 huU
    have haw : a • w ∈ W := (IsInvariant.invariant (A := A) (G := M) (H := W) a w).1 hwW
    have huwx : a • u * (a • w) = u * w := by
      calc
        a • u * (a • w) = a • (u * w) := by simp [smul_mul']
        _ = a • (x : M) := by simp [huw_eq]
        _ = x := congrArg Subtype.val (hx a)
        _ = u * w := huw_eq.symm
    exact (hunique hau huU haw hwW huwx).1
  have hw_fix : ∀ a : A, a • w = w := by
    intro a
    have hau : a • u ∈ U := (IsInvariant.invariant (A := A) (G := M) (H := U) a u).1 huU
    have haw : a • w ∈ W := (IsInvariant.invariant (A := A) (G := M) (H := W) a w).1 hwW
    have huwx : a • u * (a • w) = u * w := by
      calc
        a • u * (a • w) = a • (u * w) := by simp [smul_mul']
        _ = a • (x : M) := by simp [huw_eq]
        _ = x := congrArg Subtype.val (hx a)
        _ = u * w := huw_eq.symm
    exact (hunique hau huU haw hwW huwx).2
  let uU : U := ⟨u, huU⟩
  let wW : W := ⟨w, hwW⟩
  have hu_mem : uU ∈ fixedPointSubgroup A (↥U) := by
    rw [FixedPoints.mem_subgroup]
    intro a
    exact Subtype.ext (hu_fix a)
  have hw_mem : wW ∈ fixedPointSubgroup A (↥W) := by
    rw [FixedPoints.mem_subgroup]
    intro a
    exact Subtype.ext (hw_fix a)
  have hu_one : uU = 1 := by
    have hu_bot : uU ∈ (⊥ : Subgroup U) := by simpa [hfixU] using hu_mem
    simpa using hu_bot
  have hw_one : wW = 1 := by
    have hw_bot : wW ∈ (⊥ : Subgroup W) := by simpa [hfixW] using hw_mem
    simpa using hw_bot
  have hx_one : x = 1 := by
    have hu_val : u = 1 := congrArg Subtype.val hu_one
    have hw_val : w = 1 := congrArg Subtype.val hw_one
    calc
      x = ⟨u * w, by
          have : u * w ∈ S := by
            simpa [S] using Subgroup.mul_mem_sup huU hwW
          exact this⟩ := by
            apply Subtype.ext
            simp [huw_eq]
      _ = 1 := by
            apply Subtype.ext
            simp [hu_val, hw_val]
  simp [hx_one]

private theorem CFSG.theorem_3_6_normal_map_subtype_of_normal_and_isInvariant
    {G : Type*} [Group G] {H R : Subgroup G}
    [H.Normal] (hHR : H.IsComplement' R) (S : Subgroup H)
    [S.Normal]
    (hSinv : IsInvariant (↥R) (↥H) S) :
    (S.map H.subtype).Normal := by
  let N : Subgroup G := S.map H.subtype
  have hN_le_H : N ≤ H := by
    simpa [N] using (Subgroup.map_subtype_le S)
  have hNsub_eq : N.subgroupOf H = S := by
    ext x
    constructor
    · intro hx
      change ((x : H) : G) ∈ N at hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
      have hy_eq : y = x := by
        apply Subtype.ext
        simpa using hyx
      simpa [hy_eq] using hy
    · intro hx
      change ((x : H) : G) ∈ N
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hH_norm_N : H ≤ Subgroup.normalizer (N : Set G) := by
    let : (N.subgroupOf H).Normal := by
      rwa [hNsub_eq]
    exact Subgroup.le_normalizer_of_normal_subgroupOf hN_le_H
  have hRinv :
      ∀ r : R, ∀ x ∈ N, (r : G) * x * (r : G)⁻¹ ∈ N := by
    intro r x hx
    have hxN : x ∈ S.map H.subtype := by
      simpa [N] using hx
    rcases Subgroup.mem_map.mp hxN with ⟨xH, hxH, rfl⟩
    have hsmul : r • xH ∈ S := (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := S) r xH).1 hxH
    have hmem : (((r • xH : H) : G)) ∈ N := by
      change (((r • xH : H) : G)) ∈ S.map H.subtype
      exact Subgroup.mem_map_of_mem H.subtype hsmul
    simpa [Subgroup.conjMulDistribMulActionOfNormal_smul_coe] using hmem
  have hR_norm_N : R ≤ Subgroup.normalizer (N : Set G) := by
    intro r hrR
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hRinv ⟨r, hrR⟩ x hx
    · intro hx
      have hx' :
          ((r : G)⁻¹ * ((r : G) * x * (r : G)⁻¹) * (((r : G)⁻¹)⁻¹)) ∈ N :=
        hRinv ⟨r⁻¹, R.inv_mem hrR⟩ ((r : G) * x * (r : G)⁻¹) hx
      simpa [mul_assoc] using hx'
  have hnorm_top : Subgroup.normalizer (N : Set G) = ⊤ := by
    apply top_unique
    rw [← hHR.sup_eq_top]
    exact sup_le hH_norm_N hR_norm_N
  have hN_normal : N.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
  simpa [N] using hN_normal

set_option maxHeartbeats 2000000

private theorem CFSG.theorem_3_6_final_contradiction
    {G : Type*} [Group G] [Finite G]
    (H R R₀ : Subgroup G) (p : ℕ) (hind : Theorem36IndHyp H)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀))
    (hcomm_eq : ⁅H, R⁆ = H) (hbad : ¬ HasPLengthOne p ↥H) :
    False := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let hRnormH : R ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  obtain ⟨K, P, hVK_sup, hVK_disj, hK_inv, hNK_inv, hPsub_inv, hVNK_sup, hVinfNK_bot,
    hKsub_fit, hCH_le_K, hP_p, hPK_ne_bot, hVKP_top, hR_eq, hproper⟩ :=
    theorem_3_6_H_eq_VKP_R_eq_R₀ H R R₀ p hind hsolvG hodd hHR hcopHR hR₀_le
      hR₀_prime hp hCZ hcomm_eq hbad
  let V : Subgroup H := fittingSubgroup H
  let Psub : Subgroup H := normalizerSubtypeMap K P
  have hPsub_le_NK : Psub ≤ normalizerOf K := by
    simpa [Psub, normalizerSubtypeMap] using (Subgroup.map_subtype_le P)
  have hPsub_normK : Psub ≤ Subgroup.normalizer (K : Set H) := by
    simpa [normalizerOf] using hPsub_le_NK
  let : IsInvariant (↥R) (↥H) K := hK_inv
  have : Subgroup.Normalizes Psub K := ⟨hPsub_normK⟩
  let actP_K : MulDistribMulAction (↥Psub) (↥K) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := H) Psub K hPsub_normK
  have hP_smul_K_coe (a : Psub) (k : K) :
      ((a • k : K) : H) = (a : H) * (k : H) * (a : H)⁻¹ := by
    change ((actP_K.smul a k : K) : H) = (a : H) * (k : H) * (a : H)⁻¹
    exact
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
        (G := H) Psub K hPsub_normK a k
  obtain ⟨qK, hqK_prime, hqK_ne_p, hqK_ne_R, hK_elem, hqK_sq_lt⟩ :=
    theorem_3_6_K_card_gt_q_sq H R R₀ p hind hsolvG hodd hHR hcopHR hR₀_le
      hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hNK_inv hPsub_inv hVNK_sup
      hVinfNK_bot hKsub_fit hCH_le_K hP_p hPK_ne_bot hproper hR_eq
  have : Fact qK.Prime := ⟨hqK_prime⟩
  let : IsElementaryAbelian qK ↥K := hK_elem
  let : CommGroup K := IsMulCommutative.instCommGroup
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    exact hPK_ne_bot (by simp [hK_bot])
  let : Nontrivial ↥K := K.nontrivial_iff_ne_bot.mpr hK_ne_bot
  have hV_elem : IsElementaryAbelian p ↥V := by
    simpa [V] using
      theorem_3_6_fitting_elementaryAbelian H R R₀ p hind hsolvG hodd hHR hcopHR
        hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
  let : IsElementaryAbelian p ↥V := hV_elem
  let hKnormV : K ≤ Subgroup.normalizer V := Subgroup.le_normalizer_of_normal (H := V)
  have : Subgroup.Normalizes K V := ⟨hKnormV⟩
  let actK_V : MulDistribMulAction (↥K) (↥V) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := H) K V hKnormV
  have hK_smul_V_coe (a : K) (x : V) :
      ((a • x : V) : H) = (a : H) * (x : H) * (a : H)⁻¹ := by
    change ((actK_V.smul a x : V) : H) = (a : H) * (x : H) * (a : H)⁻¹
    exact
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
        (G := H) K V hKnormV a x
  let hV_invR : IsInvariant (↥R) (↥H) V :=
    isInvariant_of_characteristic (A := ↥R) (G := ↥H) V
  let : IsInvariant (↥R) (↥H) V := hV_invR
  have hfixK_V_bot :
      fixedPointSubgroup (↥K) (↥V) = ⊥ := by
    simpa [V] using
      theorem_3_6_K_fixedPointSubgroup_on_fitting_eq_bot H R R₀ p hind hsolvG hodd
        hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hVK_disj hK_ne_bot
        hK_inv hNK_inv hVNK_sup
  let Vg : Subgroup G := V.map H.subtype
  have hCVR_card : Nat.card (subgroupCentralizerIn Vg R) = p := by
    simpa [Vg, V, hR_eq] using
      theorem_3_6_fixed_points_of_R₀_on_fitting H R R₀ p hind hsolvG hodd hHR
        hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup
        hVinfNK_bot hKsub_fit hCH_le_K
  have hVg_ne_bot : Vg ≠ ⊥ := by
    intro hVg_bot
    have hCVR_card' : 1 = p := by
      simpa [hVg_bot, subgroupCentralizerIn] using hCVR_card
    exact hp.ne_one hCVR_card'.symm
  have hV_ne_bot : V ≠ ⊥ := by
    intro hV_bot
    apply hVg_ne_bot
    exact (Subgroup.map_eq_bot_iff_of_injective (H := V) (f := H.subtype) H.subtype_injective).2
      hV_bot
  have hK_not_cyclic : ¬ IsCyclic ↥K := by
    intro hcyc
    obtain ⟨x, hxorder⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥K)
    have hxpow : x ^ qK = 1 := by
      exact
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent ↥K ∣ qK by simpa using hK_elem.exponent_dvd_p) x
    have horder_dvd_qK : orderOf x ∣ qK := orderOf_dvd_of_pow_eq_one hxpow
    have horder_ne_one : orderOf x ≠ 1 := by
      intro horder_one
      have hcard_one : Nat.card K = 1 := hxorder.symm.trans horder_one
      exact hK_ne_bot ((Subgroup.card_eq_one (H := K)).1 hcard_one)
    have hcardK_eq_qK : Nat.card K = qK := by
      calc
        Nat.card K = orderOf x := hxorder.symm
        _ = qK := (hqK_prime.eq_one_or_self_of_dvd (orderOf x) horder_dvd_qK).resolve_left
          horder_ne_one
    have hqK_le_qKsq : qK ≤ qK ^ 2 := by
      calc
        qK = 1 * qK := by simp
        _ ≤ qK * qK := Nat.mul_le_mul_right qK hqK_prime.one_lt.le
        _ = qK ^ 2 := by simp [pow_two]
    exact
      (not_lt_of_ge (by simpa [hcardK_eq_qK] using hqK_le_qKsq)) hqK_sq_lt
  have hfix_cover :
      (⨆ (Y : Subgroup K) (_ : IsCyclic (↥K ⧸ Y)), fixedPointSubgroup (↥Y) (↥V)) = ⊤ := by
    exact theorem_3_6_hyperplane_fixed_iSup_top (K := ↥K) (V := ↥V) (q := qK) (p := p)
      hqK_ne_p hK_not_cyclic
  let Ω : Set (Subgroup K) :=
    {Y | Y.index = qK ∧ fixedPointSubgroup (↥Y) (↥V) ≠ ⊥}
  have hΩ_nonempty : Ω.Nonempty := by
    by_contra hΩ_empty
    have hall_bot :
        (⨆ (Y : Subgroup K) (_ : IsCyclic (↥K ⧸ Y)), fixedPointSubgroup (↥Y) (↥V)) = ⊥ := by
      apply le_antisymm
      · refine iSup_le ?_
        intro Y
        refine iSup_le ?_
        intro hY_cyc
        by_cases hY_top : Y = ⊤
        · subst hY_top
          intro x hx
          have hxK : x ∈ fixedPointSubgroup (↥K) (↥V) := by
            rw [FixedPoints.mem_subgroup] at hx ⊢
            intro a
            exact hx ⟨a, by simp⟩
          simpa [hfixK_V_bot] using hxK
        · have hY_index : Y.index = qK := by
            simpa [Subgroup.index_eq_card] using
              theorem_3_6_cyclic_quotient_card_eq_prime (q := qK) Y hY_cyc hY_top
          have hY_notin : Y ∉ Ω := by
            intro hY_in
            exact hΩ_empty ⟨Y, hY_in⟩
          have hY_fix_bot : fixedPointSubgroup (↥Y) (↥V) = ⊥ := by
            by_cases hfix : fixedPointSubgroup (↥Y) (↥V) = ⊥
            · exact hfix
            · exfalso
              exact hY_notin ⟨hY_index, hfix⟩
          simp [hY_fix_bot]
      · exact bot_le
    let : Nontrivial ↥V := V.nontrivial_iff_ne_bot.mpr hV_ne_bot
    have htop_ne_bot : (⊤ : Subgroup V) ≠ (⊥ : Subgroup V) := top_ne_bot
    have hall_bot' := hall_bot
    simp [hfix_cover] at hall_bot'
  let Ωsub := {Y : Subgroup K // Y ∈ Ω}
  let F : Ωsub → Subgroup V := fun Y => fixedPointSubgroup (↥Y.1) (↥V)
  have hF_ne_bot : ∀ Y : Ωsub, F Y ≠ ⊥ := by
    intro Y
    exact Y.2.2
  have hF_cyclicQuot : ∀ Y : Ωsub, IsCyclic (↥K ⧸ Y.1) := by
    intro Y
    have hcardQ : Nat.card (↥K ⧸ Y.1) = qK := by
      simpa [Subgroup.index_eq_card] using Y.2.1
    exact isCyclic_of_prime_card (α := ↥K ⧸ Y.1) hcardQ
  have hF_Kinv : ∀ Y : Ωsub, IsInvariant (↥K) (↥V) (F Y) := by
    intro Y
    have hforward : ∀ a : K, ∀ {x : V}, x ∈ F Y → a • x ∈ F Y := by
      intro a x hx
      change x ∈ fixedPointSubgroup (↥Y.1) (↥V) at hx
      change a • x ∈ fixedPointSubgroup (↥Y.1) (↥V)
      rw [FixedPoints.mem_subgroup] at hx ⊢
      intro y
      have hyx : (y : K) • x = x := by
        have hyx' := hx y
        change (y : K) • x = x at hyx'
        exact hyx'
      calc
        (y : K) • (a • x) = (((y : K) * a) • x) := by simp [mul_smul]
        _ = ((a * (y : K)) • x) := by
          exact congrArg (fun k : K => k • x) (IsMulCommutative.is_comm.comm (y : K) a)
        _ = a • ((y : K) • x) := by simp [mul_smul]
        _ = a • x := by rw [hyx]
    let : Y.1.Normal := by
      infer_instance
    refine ⟨?_⟩
    intro a x
    constructor
    · intro hx
      exact hforward a hx
    · intro hx
      have hx' : a⁻¹ • (a • x) ∈ F Y := hforward a⁻¹ hx
      simpa [inv_smul_smul] using hx'
  have hfix_top_subK :
      fixedPointSubgroup (↥(⊤ : Subgroup ↥K)) (↥V) = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxK : x ∈ fixedPointSubgroup (↥K) (↥V) := by
        rw [FixedPoints.mem_subgroup] at hx ⊢
        intro a
        exact hx ⟨a, by simp⟩
      simpa [hfixK_V_bot] using hxK
    · exact bot_le
  have hF_pairwise : Pairwise (fun Y Z : Ωsub => Disjoint (F Y) (F Z)) := by
    intro Y Z hYZ
    exact
      theorem_3_6_hyperplane_fixed_disjoint (K := ↥K) (V := ↥V) (q := qK)
        hfix_top_subK Y.1 Z.1 (hF_cyclicQuot Y) (hF_cyclicQuot Z)
        (hF_ne_bot Y) (hF_ne_bot Z) (by
          intro hEq
          exact hYZ (Subtype.ext hEq))
  let : Fintype Ωsub := Fintype.ofFinite Ωsub
  have hF_iSup_eq :
      iSup F =
        (⨆ (Y : Subgroup K) (_ : IsCyclic (↥K ⧸ Y)), fixedPointSubgroup (↥Y) (↥V)) := by
    apply le_antisymm
    · refine iSup_le ?_
      intro Y
      exact le_iSup_of_le Y.1 <| le_iSup_of_le (hF_cyclicQuot Y) le_rfl
    · refine iSup_le ?_
      intro Y
      refine iSup_le ?_
      intro hY_cyc
      by_cases hfixY : fixedPointSubgroup (↥Y) (↥V) = ⊥
      · simp [hfixY]
      · have hY_ne_top : Y ≠ ⊤ := by
          intro hY_top
          apply hfixY
          subst hY_top
          simpa using hfix_top_subK
        have hY_index : Y.index = qK := by
          simpa [Subgroup.index_eq_card] using
            theorem_3_6_cyclic_quotient_card_eq_prime (q := qK) Y hY_cyc hY_ne_top
        let YΩ : Ωsub := ⟨Y, ⟨hY_index, hfixY⟩⟩
        simpa [F, YΩ] using (le_iSup F YΩ : F YΩ ≤ iSup F)
  have hF_iSup_top : iSup F = ⊤ := by
    calc
      iSup F =
          (⨆ (Y : Subgroup K) (_ : IsCyclic (↥K ⧸ Y)), fixedPointSubgroup (↥Y) (↥V)) :=
        hF_iSup_eq
      _ = ⊤ := hfix_cover
  have hF_univ_sup_top : (Finset.univ : Finset Ωsub).sup F = ⊤ := by
    rw [Finset.sup_univ_eq_iSup]
    exact hF_iSup_top
  let Kg : Subgroup G := K.map H.subtype
  let Psubg : Subgroup G := Psub.map H.subtype
  let Sg : Subgroup G := Psubg ⊔ R
  have hRnormKg : R ≤ Subgroup.normalizer (Kg : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyK, rfl⟩
      exact Subgroup.mem_map_of_mem H.subtype <|
        (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := K) ⟨a, ha⟩ y).1 hyK
    · intro hx
      have ha_inv : a⁻¹ ∈ R := R.inv_mem ha
      rcases Subgroup.mem_map.mp hx with ⟨y, hyK, hyx⟩
      refine Subgroup.mem_map.mpr ?_
      let yK : K := ⟨y, hyK⟩
      refine ⟨(⟨a⁻¹, ha_inv⟩ : R) • yK,
        (IsInvariant.invariant (A := ↥R) (G := ↥H) (H := K) ⟨a⁻¹, ha_inv⟩ yK).1 hyK, ?_⟩
      have hyx' : H.subtype ((((⟨a⁻¹, ha_inv⟩ : R) • yK : K) : H)) = x := by
        calc
          H.subtype ((((⟨a⁻¹, ha_inv⟩ : R) • yK : K) : H)) =
              H.subtype ((⟨a⁻¹, ha_inv⟩ : R) • (y : H)) := by
            rfl
          _ =
              (a : G)⁻¹ * (y : H) * (a : G) := by
            simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
          _ = (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * (a : G) := by
            simpa using congrArg (fun z : G => (a : G)⁻¹ * z * (a : G)) hyx
          _ = x := by simp [mul_assoc]
      exact hyx'
  have hPsubg_le_H : Psubg ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  have hPsubg_le_normKg : Psubg ≤ Subgroup.normalizer (Kg : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
      rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
      let kK : K := ⟨k, hk⟩
      have hkmap :
          H.subtype ((((⟨b, hb⟩ : Psub) • kK : K) : H)) ∈ Kg :=
        Subgroup.mem_map_of_mem H.subtype (((⟨b, hb⟩ : Psub) • kK).2)
      change H.subtype b * H.subtype k * (H.subtype b)⁻¹ ∈ Kg at hkmap
      exact hkmap
    · intro hx
      rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
      have hb_inv : b⁻¹ ∈ Psub := Psub.inv_mem hb
      rcases Subgroup.mem_map.mp hx with ⟨k, hk, hkx⟩
      let kK : K := ⟨k, hk⟩
      have hkmap :
          H.subtype ((((⟨b⁻¹, hb_inv⟩ : Psub) • kK : K) : H)) ∈ Kg :=
        Subgroup.mem_map_of_mem H.subtype (((⟨b⁻¹, hb_inv⟩ : Psub) • kK).2)
      have hkx' :
          H.subtype ((((⟨b⁻¹, hb_inv⟩ : Psub) • kK : K) : H)) = x := by
        calc
          H.subtype ((((⟨b⁻¹, hb_inv⟩ : Psub) • kK : K) : H)) =
              (b : G)⁻¹ * (k : H) * (b : G) := by
            simp [kK, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
              mul_assoc]
          _ = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * (b : G) := by
            simpa using congrArg (fun z : G => (b : G)⁻¹ * z * (b : G)) hkx
          _ = x := by simp [mul_assoc]
      exact hkx' ▸ hkmap
  have hSg_le_normKg : Sg ≤ Subgroup.normalizer (Kg : Set G) := sup_le hPsubg_le_normKg hRnormKg
  have hSg_le_normH : Sg ≤ Subgroup.normalizer H := by
    exact sup_le (hPsubg_le_H.trans (Subgroup.le_normalizer_of_normal (H := H))) hRnormH
  have : Subgroup.Normalizes Sg H := ⟨hSg_le_normH⟩
  let actS_H : MulDistribMulAction (↥Sg) (↥H) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) Sg H hSg_le_normH
  have hS_smul_H_coe (a : Sg) (x : H) :
      (((a : Sg) • x : H) : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
    change ((actS_H.smul a x : H) : G) = (a : G) * (x : G) * (a : G)⁻¹
    exact
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
        (G := G) Sg H hSg_le_normH a x
  have hK_invS : IsInvariant (↥Sg) (↥H) K := by
    refine ⟨?_⟩
    have hforward : ∀ a : Sg, ∀ x : H, x ∈ K → a • x ∈ K := by
      intro a x hx
      have hnorm : (a : G) ∈ Subgroup.normalizer ((Kg : Subgroup G) : Set G) := hSg_le_normKg a.2
      have hxmap : (x : G) ∈ Kg := Subgroup.mem_map_of_mem H.subtype hx
      have hxmap' : (a : G) * (x : G) * (a : G)⁻¹ ∈ Kg :=
        (Subgroup.mem_normalizer_iff.mp hnorm) (x : G) |>.1 hxmap
      have hxsmul : ((a • x : H) : G) ∈ Kg := by
        simpa [Kg, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hSg_le_normH] using
          hxmap'
      rcases Subgroup.mem_map.mp hxsmul with ⟨y, hy, hy_eq⟩
      have hxy : (a • x : H) = y := H.subtype_injective hy_eq.symm
      simpa [hxy] using hy
    intro a x
    constructor
    · exact hforward a x
    · intro hx
      have h := hforward a⁻¹ (a • x) hx
      simpa [smul_smul] using h
  let : IsInvariant (↥Sg) (↥H) K := hK_invS
  let hV_invS : IsInvariant (↥Sg) (↥H) V :=
    isInvariant_of_characteristic (A := ↥Sg) (G := ↥H) V
  let : IsInvariant (↥Sg) (↥H) V := hV_invS
  let : CommGroup ↥V := IsMulCommutative.instCommGroup
  have hsub_le_normalizer (X Y : Subgroup V) : Y ≤ Subgroup.normalizer (X : Set V) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor <;> intro hx <;> simpa [mul_assoc, mul_comm] using hx
  have hF_restrict_inv (Y Z : Ωsub) : IsInvariant Y.1 (↥V) (F Z) := by
    refine ⟨?_⟩
    intro a x
    exact (hF_Kinv Z).invariant (a : K) x
  have hF_sup_inv : ∀ s : Finset Ωsub, ∀ Y : Ωsub, IsInvariant Y.1 (↥V) (s.sup F) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro Y
        refine ⟨?_⟩
        intro a x
        constructor
        · intro hx
          have hxone : x = 1 := by simpa using hx
          simp [hxone]
        · intro hx
          have hxone : a • x = 1 := by simpa [hx]
          rw [smul_eq_iff_eq_inv_smul] at hxone
          simpa using hxone
    | insert i s hi ih =>
        intro Y
        let : IsInvariant Y.1 (↥V) (F i) := hF_restrict_inv Y i
        let : IsInvariant Y.1 (↥V) (s.sup F) := ih Y
        have hs_le_norm : s.sup F ≤ Subgroup.normalizer (F i : Set V) :=
          hsub_le_normalizer (X := F i) (Y := s.sup F)
        have hsup_inv :
            IsInvariant Y.1 (↥V) (F i ⊔ s.sup F) :=
          isInvariant_sup_of_le_normalizer (A := Y.1) (G := ↥V) (X := F i) (Y := s.sup F)
            hs_le_norm
        simpa [Finset.sup_insert, hi] using hsup_inv
  have hF_supIndep_and_fix :
      ∀ s : Finset Ωsub,
        s.SupIndep F ∧ ∀ Y : Ωsub, Y ∉ s → fixedPointSubgroup Y.1 (↥(s.sup F)) = ⊥ := by
    intro s
    induction s using Finset.induction with
    | empty =>
        constructor
        · simp
        · intro Y hY
          apply bot_unique
          intro x hx
          have hsub :
              Subsingleton ↥((∅ : Finset Ωsub).sup F) := by
            simpa using (inferInstance : Subsingleton ↥(⊥ : Subgroup V))
          have hxone : x = 1 := hsub.elim x 1
          change x = 1
          exact hxone
    | insert i s hi ih =>
        rcases ih with ⟨hs_ind, hs_fix⟩
        have hdisj_i_s : Disjoint (F i) (s.sup F) := by
          rw [Subgroup.disjoint_def]
          intro x hxFi hxSup
          have hxs_fix : (⟨x, hxSup⟩ : ↥(s.sup F)) ∈ fixedPointSubgroup i.1 (↥(s.sup F)) := by
            rw [FixedPoints.mem_subgroup]
            intro a
            exact Subtype.ext <| by
              have ha := hxFi a
              change ((a • (⟨x, hxSup⟩ : ↥(s.sup F)) : ↥(s.sup F)) : V) = x at ha
              exact ha
          have hxbot : (⟨x, hxSup⟩ : ↥(s.sup F)) ∈ (⊥ : Subgroup ↥(s.sup F)) := by
            simpa [hs_fix i hi] using hxs_fix
          have hxone : x = 1 := by
            have hxone_sub : (⟨x, hxSup⟩ : ↥(s.sup F)) = 1 := by
              simpa using hxbot
            exact congrArg Subtype.val hxone_sub
          simp [hxone]
        constructor
        · exact hs_ind.insert hdisj_i_s
        · intro Y hYins
          have hYi : Y ≠ i := by
            intro hEq
            exact hYins (hEq ▸ Finset.mem_insert_self i s)
          have hYs : Y ∉ s := by
            intro hYs
            exact hYins (Finset.mem_insert_of_mem hYs)
          let : IsInvariant Y.1 (↥V) (F i) := hF_restrict_inv Y i
          let : IsInvariant Y.1 (↥V) (s.sup F) := hF_sup_inv s Y
          have hFi_fix_bot : fixedPointSubgroup Y.1 (↥(F i)) = ⊥ := by
            have hdisj_iY : Disjoint (F i) (F Y) := hF_pairwise hYi.symm
            simpa [F] using
              theorem_3_6_fixedPointSubgroup_subgroup_eq_bot_of_disjoint
                (A := Y.1) (M := ↥V) (U := F i) hdisj_iY
          let : IsInvariant Y.1 (↥V) (F i ⊔ s.sup F) := by
            exact
              isInvariant_sup_of_le_normalizer (A := Y.1) (G := ↥V) (X := F i)
                (Y := s.sup F) (hsub_le_normalizer (X := F i) (Y := s.sup F))
          have hfix_sup :
              fixedPointSubgroup Y.1 (↥(F i ⊔ s.sup F)) = ⊥ :=
            theorem_3_6_fixedPointSubgroup_sup_eq_bot_of_disjoint
              (A := Y.1) (M := ↥V) (U := F i) (W := s.sup F) hdisj_i_s hFi_fix_bot
                (hs_fix Y hYs)
          apply bot_unique
          intro x hx
          let x' : ↥(F i ⊔ s.sup F) := ⟨x, by simpa [Finset.sup_insert, hi] using x.2⟩
          have hx' : x' ∈ fixedPointSubgroup Y.1 (↥(F i ⊔ s.sup F)) := by
            rw [FixedPoints.mem_subgroup] at hx ⊢
            intro a
            apply Subtype.ext
            change ((a : Y.1) • ((x : ↥((insert i s).sup F)) : V) : V) =
                ((x : ↥((insert i s).sup F)) : V)
            exact congrArg Subtype.val (hx a)
          have hxbot : x' ∈ (⊥ : Subgroup ↥(F i ⊔ s.sup F)) := by
            simpa [hfix_sup] using hx'
          have hxone' : x' = 1 := by simpa using hxbot
          change x = 1
          apply Subtype.ext
          simpa [x'] using congrArg Subtype.val hxone'
  have hF_supIndep : (Finset.univ : Finset Ωsub).SupIndep F := (hF_supIndep_and_fix _).1
  have hF_iSupIndep : iSupIndep F := hF_supIndep.iSupIndep_of_univ
  let ρK : Sg →* MulAut (↥K) := MulDistribMulAction.toMulAut (G := ↥Sg) (M := ↥K)
  let ρV : Sg →* MulAut (↥V) := MulDistribMulAction.toMulAut (G := ↥Sg) (M := ↥V)
  have hρ_transport (a : Sg) (y : K) (x : V) :
      ((ρK a) y) • ((ρV a) x) = (ρV a) (y • x) := by
    apply Subtype.ext
    apply H.subtype_injective
    have hy :
        ((((ρK a) y : K) : H) : G) = (a : G) * (y : H) * (a : G)⁻¹ := by
      change (((a : Sg) • (y : H) : H) : G) = (a : G) * (y : H) * (a : G)⁻¹
      exact hS_smul_H_coe a y
    have hx :
        ((((ρV a) x : V) : H) : G) = (a : G) * (x : H) * (a : G)⁻¹ := by
      change (((a : Sg) • (x : H) : H) : G) = (a : G) * (x : H) * (a : G)⁻¹
      exact hS_smul_H_coe a x
    have hright :
        ((((ρV a) (y • x) : V) : H) : G) =
          (a : G) * ((y : H) * (x : H) * (y : H)⁻¹) * (a : G)⁻¹ := by
      change (((a : Sg) • (((y : K) • x : V) : H) : H) : G) =
        (a : G) * ((y : H) * (x : H) * (y : H)⁻¹) * (a : G)⁻¹
      rw [hS_smul_H_coe, hK_smul_V_coe]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_assoc]
    calc
      (((((ρK a) y) • ((ρV a) x) : V) : H) : G) =
          ((((ρK a) y : K) : H) : G) * ((((ρV a) x : V) : H) : G) *
            ((((ρK a) y : K) : H) : G)⁻¹ := by
              rfl
      _ = (a : G) * (y : H) * (x : H) * (y : H)⁻¹ * (a : G)⁻¹ := by
            rw [hy, hx]
            simp only [InvMemClass.coe_inv, mul_assoc, mul_inv_rev, inv_inv, inv_mul_cancel_left]
      _ = (a : G) * ((y : H) * (x : H) * (y : H)⁻¹) * (a : G)⁻¹ := by
            simp only [InvMemClass.coe_inv, mul_assoc]
      _ = ((((ρV a) (y • x) : V) : H) : G) := hright.symm
  have hF_map_le (a : Sg) (Y : Ωsub) :
      (F Y).map (ρV a : ↥V →* ↥V) ≤
        fixedPointSubgroup (↥(Y.1.map (ρK a : ↥K →* ↥K))) (↥V) := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hx, rfl⟩
    change ∀ b : Y.1.map (ρK a : ↥K →* ↥K), (b : K) • ((ρV a) x) = (ρV a) x
    have hxfix : ∀ y : Y.1, (y : K) • x = x := by
      have hx' : x ∈ fixedPointSubgroup (↥Y.1) (↥V) := by
        simpa [F] using hx
      simpa [FixedPoints.mem_subgroup] using hx'
    intro b
    have hbmem :
        (b : K) ∈ Y.1.map (ρK a : ↥K →* ↥K) := by
      exact b.2
    rcases Subgroup.mem_map.mp hbmem with ⟨y, hyY, hyb⟩
    have hyfix : y • x = x := hxfix ⟨y, hyY⟩
    calc
      (b : K) • ((ρV a) x) = ((ρK a) y) • ((ρV a) x) := by
        simpa using congrArg (fun t : K => t • ((ρV a) x)) hyb.symm
      _ = (ρV a) (y • x) := hρ_transport a y x
      _ = (ρV a) x := by rw [hyfix]
  let : MulAction (↥Sg) Ωsub := {
    smul := fun a Y => by
      refine ⟨Y.1.map (ρK a : ↥K →* ↥K), ?_⟩
      have hindex : (Y.1.map (ρK a : ↥K →* ↥K)).index = qK := by
        calc
          (Y.1.map (ρK a : ↥K →* ↥K)).index = Y.1.index := by
            simp
          _ = qK := Y.2.1
      have hmap_ne_bot : (F Y).map (ρV a : ↥V →* ↥V) ≠ ⊥ := by
        intro hbot
        exact hF_ne_bot Y <|
          (Subgroup.map_eq_bot_iff_of_injective (H := F Y) (f := (ρV a : ↥V →* ↥V))
            (ρV a).injective).1 hbot
      have hfix_ne_bot :
          fixedPointSubgroup (↥(Y.1.map (ρK a : ↥K →* ↥K))) (↥V) ≠ ⊥ := by
        intro hbot
        exact hmap_ne_bot (le_bot_iff.mp ((hF_map_le a Y).trans (le_of_eq hbot)))
      exact ⟨hindex, hfix_ne_bot⟩
    one_smul := by
      intro Y
      apply Subtype.ext
      change Y.1.map (ρK 1 : ↥K →* ↥K) = Y.1
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        simpa [ρK] using hy
      · intro hx
        exact Subgroup.mem_map.mpr ⟨x, hx, by simp [ρK]⟩
    mul_smul := by
      intro a b Y
      apply Subtype.ext
      change Y.1.map (ρK (a * b) : ↥K →* ↥K) =
          (Y.1.map (ρK b : ↥K →* ↥K)).map (ρK a : ↥K →* ↥K)
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        refine Subgroup.mem_map.mpr ?_
        refine ⟨(ρK b) y, Subgroup.mem_map_of_mem (ρK b : ↥K →* ↥K) hy, ?_⟩
        simp [ρK, mul_smul]
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨z, hz, hzx⟩
        rcases Subgroup.mem_map.mp hz with ⟨y, hy, hyz⟩
        refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
        calc
          (ρK (a * b)) y = (ρK a) ((ρK b) y) := by simp [ρK, mul_smul]
          _ = (ρK a) z := by simpa using congrArg (ρK a) hyz
          _ = x := hzx
  }
  have hF_comm :
      Pairwise (fun Y Z : Ωsub => ∀ x y : V, x ∈ F Y → y ∈ F Z → Commute x y) := by
    intro Y Z hYZ x y hx hy
    simp [Commute]
  let φ := Subgroup.noncommPiCoprod (H := F) (hcomm := hF_comm)
  have hφ_range : φ.range = ⨆ Y : Ωsub, F Y := Subgroup.noncommPiCoprod_range (H := F)
  have hφ_inj : Function.Injective φ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (H := F) (hcomm := hF_comm) hF_iSupIndep
  let hφ_cod : ∀ u, φ u ∈ (⊤ : Subgroup V) := by
    intro u
    simp
  let φ' : (∀ Y : Ωsub, F Y) →* ↥(⊤ : Subgroup V) := φ.codRestrict ⊤ hφ_cod
  have hφ'_inj : Function.Injective φ' := (φ.injective_codRestrict ⊤ hφ_cod).mpr hφ_inj
  have hφ'_surj : Function.Surjective φ' := by
    intro x
    have hx : x.1 ∈ φ.range := by
      rw [hφ_range, hF_iSup_top]
      exact x.2
    rcases hx with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    exact hu
  let eF : (∀ Y : Ωsub, F Y) ≃* ↥(⊤ : Subgroup V) := MulEquiv.ofBijective φ' ⟨hφ'_inj, hφ'_surj⟩
  let eV : (∀ Y : Ωsub, F Y) ≃* V := eF.trans Subgroup.topEquiv
  let WV : Ωsub → Subgroup V :=
    fun Y => ⨆ Z : Ωsub, ⨆ (_ : Z ∈ MulAction.orbit (↥Sg) Y), F Z
  have hWV_nontrivial (Y : Ωsub) : WV Y ≠ ⊥ := by
    intro hbot
    have hFY_le : F Y ≤ WV Y := by
      exact
        le_iSup_of_le Y <|
          le_iSup_of_le (MulAction.mem_orbit_self Y) le_rfl
    exact hF_ne_bot Y <| le_bot_iff.mp (hFY_le.trans <| le_of_eq hbot)
  have hWV_disj_of_orbit_disj {Y Z : Ωsub}
      (hYZ : Disjoint (MulAction.orbit (↥Sg) Y) (MulAction.orbit (↥Sg) Z)) :
      Disjoint (WV Y) (WV Z) := by
    classical
    change Disjoint
        (⨆ U : Ωsub, ⨆ (_ : U ∈ MulAction.orbit (↥Sg) Y), F U)
        (⨆ W : Ωsub, ⨆ (_ : W ∈ MulAction.orbit (↥Sg) Z), F W)
    let u : Finset Ωsub := (MulAction.orbit (↥Sg) Y).toFinite.toFinset
    let v : Finset Ωsub := (MulAction.orbit (↥Sg) Z).toFinite.toFinset
    have hu_sup :
        u.sup F = ⨆ U : Ωsub, ⨆ (_ : U ∈ MulAction.orbit (↥Sg) Y), F U := by
      simpa [u] using (Finset.sup_eq_iSup u F)
    have hv_sup :
        v.sup F = ⨆ W : Ωsub, ⨆ (_ : W ∈ MulAction.orbit (↥Sg) Z), F W := by
      simpa [v] using (Finset.sup_eq_iSup v F)
    have huv : Disjoint u v := by
      rw [Finset.disjoint_left]
      intro a haU haV
      exact (Set.disjoint_left.mp hYZ) (by simpa [u] using haU) (by simpa [v] using haV)
    have hsupIndep : (Finset.univ : Finset Ωsub).SupIndep F := iSupIndep.supIndep' Finset.univ hF_iSupIndep
    rw [← hu_sup, ← hv_sup]
    exact hsupIndep.disjoint_sup_sup (by simp) (by simp) huv
  let WH : Ωsub → Subgroup H := fun Y => (WV Y).map V.subtype
  let Wg : Ωsub → Subgroup G := fun Y => (WH Y).map H.subtype
  have hWH_nontrivial (Y : Ωsub) : WH Y ≠ ⊥ := by
    intro hbot
    exact hWV_nontrivial Y <|
      (Subgroup.map_eq_bot_iff_of_injective (H := WV Y) (f := V.subtype) V.subtype_injective).1
        (by simpa [WH] using hbot)
  have hWg_nontrivial (Y : Ωsub) : Wg Y ≠ ⊥ := by
    intro hbot
    exact hWH_nontrivial Y <|
      (Subgroup.map_eq_bot_iff_of_injective (H := WH Y) (f := H.subtype) H.subtype_injective).1
        (by simpa [Wg] using hbot)
  have hWg_le_H (Y : Ωsub) : Wg Y ≤ H := by
    simpa [Wg] using (Subgroup.map_subtype_le (WH Y))
  have hWH_disj_of_orbit_disj {Y Z : Ωsub}
      (hYZ : Disjoint (MulAction.orbit (↥Sg) Y) (MulAction.orbit (↥Sg) Z)) :
      Disjoint (WH Y) (WH Z) := by
    simpa [WH] using Subgroup.disjoint_map V.subtype_injective (hWV_disj_of_orbit_disj hYZ)
  have hWg_disj_of_orbit_disj {Y Z : Ωsub}
      (hYZ : Disjoint (MulAction.orbit (↥Sg) Y) (MulAction.orbit (↥Sg) Z)) :
      Disjoint (Wg Y) (Wg Z) := by
    simpa [Wg] using Subgroup.disjoint_map H.subtype_injective (hWH_disj_of_orbit_disj hYZ)
  have hWV_invK (Y : Ωsub) : IsInvariant (↥K) (↥V) (WV Y) := by
    refine ⟨?_⟩
    intro a x
    constructor
    · intro hx
      have hmap_le :
          (WV Y).map (MulDistribMulAction.toMulAut (↥K) (↥V) a : ↥V →* ↥V) ≤ WV Y := by
        dsimp [WV]
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro U
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro hUY z hz
        rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
        have hw' :
            (MulDistribMulAction.toMulAut (↥K) (↥V) a) w ∈ F U :=
          (hF_Kinv U).invariant (A := ↥K) (G := ↥V) (H := F U) a w |>.1 hw
        have hFU_le : F U ≤ WV Y := by
          exact le_iSup_of_le U <| le_iSup_of_le hUY le_rfl
        exact hFU_le hw'
      exact hmap_le (Subgroup.mem_map_of_mem _ hx)
    · intro hx
      have hmap_le :
          (WV Y).map (MulDistribMulAction.toMulAut (↥K) (↥V) a⁻¹ : ↥V →* ↥V) ≤ WV Y := by
        dsimp [WV]
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro U
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro hUY z hz
        rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
        have hw' :
            (MulDistribMulAction.toMulAut (↥K) (↥V) a⁻¹) w ∈ F U :=
          (hF_Kinv U).invariant (A := ↥K) (G := ↥V) (H := F U) a⁻¹ w |>.1 hw
        have hFU_le : F U ≤ WV Y := by
          exact le_iSup_of_le U <| le_iSup_of_le hUY le_rfl
        exact hFU_le hw'
      have hx' :
          (MulDistribMulAction.toMulAut (↥K) (↥V) a⁻¹)
              ((MulDistribMulAction.toMulAut (↥K) (↥V) a) x) ∈ WV Y :=
        hmap_le (Subgroup.mem_map_of_mem _ hx)
      simpa [MulDistribMulAction.toMulAut_apply] using hx'
  have hWV_invS (Y : Ωsub) : IsInvariant (↥Sg) (↥V) (WV Y) := by
    refine ⟨?_⟩
    intro a x
    constructor
    · intro hx
      have hmap_le : (WV Y).map (ρV a : ↥V →* ↥V) ≤ WV Y := by
        dsimp [WV]
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro U
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro hUY
        have hFa_le : (F U).map (ρV a : ↥V →* ↥V) ≤ F (a • U) := by
          have hle := hF_map_le a U
          change (F U).map (ρV a : ↥V →* ↥V) ≤ F (a • U) at hle
          exact hle
        exact
          hFa_le.trans <|
            le_iSup_of_le (a • U) <|
              le_iSup_of_le (MulAction.mem_orbit_of_mem_orbit a hUY) le_rfl
      exact hmap_le (Subgroup.mem_map_of_mem _ hx)
    · intro hx
      have hmap_le : (WV Y).map (ρV a⁻¹ : ↥V →* ↥V) ≤ WV Y := by
        dsimp [WV]
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro U
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro hUY
        have hFa_le : (F U).map (ρV a⁻¹ : ↥V →* ↥V) ≤ F (a⁻¹ • U) := by
          have hle := hF_map_le a⁻¹ U
          change (F U).map (ρV a⁻¹ : ↥V →* ↥V) ≤ F (a⁻¹ • U) at hle
          exact hle
        exact
          hFa_le.trans <|
            le_iSup_of_le (a⁻¹ • U) <|
              le_iSup_of_le (MulAction.mem_orbit_of_mem_orbit a⁻¹ hUY) le_rfl
      have hx' : (ρV a⁻¹) ((ρV a) x) ∈ WV Y := hmap_le (Subgroup.mem_map_of_mem _ hx)
      simpa [ρV, MulDistribMulAction.toMulAut_apply] using hx'
  have hWV_invR (Y : Ωsub) : IsInvariant (↥R) (↥V) (WV Y) := by
    refine ⟨?_⟩
    intro a x
    let aS : Sg := ⟨(a : G), Subgroup.mem_sup_right a.2⟩
    have hx := (hWV_invS Y).invariant (A := ↥Sg) (G := ↥V) (H := WV Y) aS x
    change (x ∈ WV Y) ↔ (a • x ∈ WV Y) at hx
    exact hx
  have hWH_le_V (Y : Ωsub) : WH Y ≤ V := by
    simpa [WH] using (Subgroup.map_subtype_le (WV Y))
  have hWH_invR (Y : Ωsub) : IsInvariant (↥R) (↥H) (WH Y) := by
    let : IsInvariant (↥R) (↥V) (WV Y) := hWV_invR Y
    simpa [WH] using isInvariant_map_subtype (A := ↥R) (G := ↥H) V (WV Y)
  have hWH_normal (Y : Ωsub) : (WH Y).Normal := by
    have hV_norm_WH : V ≤ Subgroup.normalizer (WH Y : Set H) := by
      let : ((WH Y).subgroupOf V).Normal := by
        infer_instance
      exact Subgroup.le_normalizer_of_normal_subgroupOf (hWH_le_V Y)
    have hK_norm_WH : K ≤ Subgroup.normalizer (WH Y : Set H) := by
      refine subgroup_le_normalizer_of_conj_mem (WH Y) K ?_
      intro a x hx
      rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
      have hz' : a • z ∈ WV Y := (hWV_invK Y).invariant (A := ↥K) (G := ↥V) (H := WV Y) a z |>.1 hz
      simpa [WH, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hKnormV] using
        (Subgroup.mem_map_of_mem V.subtype hz')
    have hP_norm_WH : Psub ≤ Subgroup.normalizer (WH Y : Set H) := by
      refine subgroup_le_normalizer_of_conj_mem (WH Y) Psub ?_
      intro a x hx
      rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
      let aS : Sg := ⟨((a : H) : G),
        Subgroup.mem_sup_left (Subgroup.mem_map_of_mem H.subtype a.2)⟩
      have hz' : aS • z ∈ WV Y :=
        (hWV_invS Y).invariant (A := ↥Sg) (G := ↥V) (H := WV Y) aS z |>.1 hz
      refine Subgroup.mem_map.mpr ⟨aS • z, hz', ?_⟩
      apply Subtype.ext
      calc
        ((((aS • z : V) : H) : G)) = (aS : G) * (z : H) * (aS : G)⁻¹ := by
          change (((aS : Sg) • (z : H) : H) : G) = (aS : G) * (z : H) * (aS : G)⁻¹
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        _ = ((a : H) : G) * (z : H) * (((a : H) : G)⁻¹) := by
          simp [aS]
    have hH_norm_WH : (⊤ : Subgroup H) ≤ Subgroup.normalizer (WH Y : Set H) := by
      rw [← hVKP_top]
      exact sup_le (sup_le hV_norm_WH hK_norm_WH) hP_norm_WH
    exact Subgroup.normalizer_eq_top_iff.mp (top_unique hH_norm_WH)
  have hWg_normal (Y : Ωsub) : (Wg Y).Normal := by
    let : (WH Y).Normal := hWH_normal Y
    exact theorem_3_6_normal_map_subtype_of_normal_and_isInvariant hHR (WH Y) (hWH_invR Y)
  have hS_transitive : ∀ Y Z : Ωsub, Z ∈ MulAction.orbit (↥Sg) Y := by
    intro Y Z
    by_contra hZ
    have hYZ_disj : Disjoint (MulAction.orbit (↥Sg) Y) (MulAction.orbit (↥Sg) Z) := by
      rw [Set.disjoint_left]
      intro U hUY hUZ
      have hU_eq_Y : MulAction.orbit (↥Sg) U = MulAction.orbit (↥Sg) Y :=
        (MulAction.orbit_eq_iff (G := ↥Sg) (a := U) (b := Y)).2 hUY
      have hU_eq_Z : MulAction.orbit (↥Sg) U = MulAction.orbit (↥Sg) Z :=
        (MulAction.orbit_eq_iff (G := ↥Sg) (a := U) (b := Z)).2 hUZ
      have hYZ_eq : MulAction.orbit (↥Sg) Y = MulAction.orbit (↥Sg) Z :=
        hU_eq_Y.symm.trans hU_eq_Z
      have hZ_mem : Z ∈ MulAction.orbit (↥Sg) Y := by
        rw [hYZ_eq]
        exact MulAction.mem_orbit_self Z
      exact hZ hZ_mem
    have hWgY_ne_bot : Wg Y ≠ ⊥ := hWg_nontrivial Y
    have hWgZ_ne_bot : Wg Z ≠ ⊥ := hWg_nontrivial Z
    obtain ⟨M, _, hM_le_WgY, hM_ne_bot, hMmin⟩ :=
      exists_minimal_normal_le (G := G) (Wg Y) (hWg_normal Y) hWgY_ne_bot
    obtain ⟨N, _, hN_le_WgZ, hN_ne_bot, hNmin⟩ :=
      exists_minimal_normal_le (G := G) (Wg Z) (hWg_normal Z) hWgZ_ne_bot
    let : IsMinimalNormal M := {
      minimal := by
        intro L hLnorm hLM
        by_cases hL_bot : L = ⊥
        · exact Or.inl hL_bot
        · exact Or.inr (hMmin L hLnorm hLM hL_bot)
    }
    let : IsMinimalNormal N := {
      minimal := by
        intro L hLnorm hLN
        by_cases hL_bot : L = ⊥
        · exact Or.inl hL_bot
        · exact Or.inr (hNmin L hLnorm hLN hL_bot)
    }
    have hM_le_H : M ≤ H := hM_le_WgY.trans (hWg_le_H Y)
    have hN_le_H : N ≤ H := hN_le_WgZ.trans (hWg_le_H Z)
    have hMN_ne : M ≠ N := by
      intro hMN
      have hM_le_bot : M ≤ ⊥ := by
        intro x hx
        have hxY : x ∈ Wg Y := hM_le_WgY hx
        have hxZ : x ∈ Wg Z := by simpa [hMN] using hN_le_WgZ (hMN ▸ hx)
        have hxbot : x ∈ (⊥ : Subgroup G) := by
          have hxinf : x ∈ Wg Y ⊓ Wg Z := ⟨hxY, hxZ⟩
          simpa [hWg_disj_of_orbit_disj hYZ_disj |>.eq_bot] using hxinf
        simpa using hxbot
      exact hM_ne_bot (bot_unique hM_le_bot)
    have :=
      theorem_3_6_unique_minimal_normal_in_H H R R₀ M N p hind hM_le_H hN_le_H hM_ne_bot
        hN_ne_bot hsolvG hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad
    exact hMN_ne this
  let toVg : ↥V →* ↥Vg :=
    { toFun := fun x => ⟨H.subtype x.1, Subgroup.mem_map_of_mem H.subtype x.2⟩
      map_one' := by
        apply Subtype.ext
        rfl
      map_mul' := by
        intro x y
        apply Subtype.ext
        rfl }
  have htoVg_inj : Function.Injective toVg := by
    intro x y hxy
    apply Subtype.ext
    apply H.subtype_injective
    simpa [toVg] using congrArg Subtype.val hxy
  have hRnormVg : R ≤ Subgroup.normalizer (Vg : Set G) := Subgroup.le_normalizer_of_normal (H := Vg)
  have : Subgroup.Normalizes R Vg := ⟨hRnormVg⟩
  have htoVg_smul (a : R) (x : V) : toVg (a • x) = a • toVg x := by
    apply Subtype.ext
    change (((a : R) • (x : H) : H) : G) = (a : G) * ((x : H) : G) * (a : G)⁻¹
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
  have hCfixVg_card : Nat.card (fixedPointSubgroup (↥R) (↥Vg)) = p := by
    let Cfix : Subgroup G := subgroupCentralizerIn Vg R
    have hCfix_le_Vg : Cfix ≤ Vg := inf_le_left
    have hfix_eq :
        fixedPointSubgroup (↥R) (↥Vg) = Cfix.subgroupOf Vg := by
      ext x
      constructor
      · intro hx
        refine ⟨x.2, ?_⟩
        change (x : G) ∈ Subgroup.centralizer (R : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro r hrR
        have hxfix : (⟨r, hrR⟩ : R) • x = x := hx ⟨r, hrR⟩
        have hxconj : (r : G) * (x : G) * (r : G)⁻¹ = x := by
          simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormVg] using
            congrArg Subtype.val hxfix
        have := congrArg (fun t : G => t * r) hxconj
        simpa [mul_assoc] using this
      · intro hx
        rcases hx with ⟨-, hxC⟩
        rw [FixedPoints.mem_subgroup]
        intro a
        apply Subtype.ext
        have hcomm : (a : G) * (x : G) = (x : G) * (a : G) :=
          Subgroup.mem_centralizer_iff.mp hxC (a : G) a.2
        have hxconj : (a : G) * (x : G) * (a : G)⁻¹ = x := by
          calc
            (a : G) * (x : G) * (a : G)⁻¹ = ((x : G) * (a : G)) * (a : G)⁻¹ := by
              rw [hcomm]
            _ = x := by simp [mul_assoc]
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormVg] using hxconj
    calc
      Nat.card (fixedPointSubgroup (↥R) (↥Vg)) = Nat.card (Cfix.subgroupOf Vg) := by
            rw [hfix_eq]
      _ = Nat.card Cfix := by
            exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := Cfix) (K := Vg) hCfix_le_Vg).toEquiv
      _ = p := hCVR_card
  let ιR : R →* Sg := Subgroup.inclusion (show R ≤ Sg by exact le_sup_right)
  let ιPsubg : Psubg →* Sg := Subgroup.inclusion (show Psubg ≤ Sg by exact le_sup_left)
  let : MulAction (↥R) Ωsub := MulAction.compHom Ωsub ιR
  let : MulAction (↥Psubg) Ωsub := MulAction.compHom Ωsub ιPsubg
  let WR : Ωsub → Subgroup V :=
    fun Y => ⨆ Z : Ωsub, ⨆ (_ : Z ∈ MulAction.orbit (↥R) Y), F Z
  let WRg : Ωsub → Subgroup Vg := fun Y => (WR Y).map toVg
  have hWR_nontrivial (Y : Ωsub) : WR Y ≠ ⊥ := by
    intro hbot
    have hFY_le : F Y ≤ WR Y := by
      exact
        le_iSup_of_le Y <|
          le_iSup_of_le (MulAction.mem_orbit_self Y) le_rfl
    exact hF_ne_bot Y <| le_bot_iff.mp (hFY_le.trans <| le_of_eq hbot)
  have hWR_disj_of_orbit_disj {Y Z : Ωsub}
      (hYZ : Disjoint (MulAction.orbit (↥R) Y) (MulAction.orbit (↥R) Z)) :
      Disjoint (WR Y) (WR Z) := by
    classical
    change Disjoint
        (⨆ U : Ωsub, ⨆ (_ : U ∈ MulAction.orbit (↥R) Y), F U)
        (⨆ W : Ωsub, ⨆ (_ : W ∈ MulAction.orbit (↥R) Z), F W)
    let u : Finset Ωsub := (MulAction.orbit (↥R) Y).toFinite.toFinset
    let v : Finset Ωsub := (MulAction.orbit (↥R) Z).toFinite.toFinset
    have hu_sup :
        u.sup F = ⨆ U : Ωsub, ⨆ (_ : U ∈ MulAction.orbit (↥R) Y), F U := by
      simpa [u] using (Finset.sup_eq_iSup u F)
    have hv_sup :
        v.sup F = ⨆ W : Ωsub, ⨆ (_ : W ∈ MulAction.orbit (↥R) Z), F W := by
      simpa [v] using (Finset.sup_eq_iSup v F)
    have huv : Disjoint u v := by
      rw [Finset.disjoint_left]
      intro a haU haV
      exact (Set.disjoint_left.mp hYZ) (by simpa [u] using haU) (by simpa [v] using haV)
    have hsupIndep : (Finset.univ : Finset Ωsub).SupIndep F := iSupIndep.supIndep' Finset.univ hF_iSupIndep
    rw [← hu_sup, ← hv_sup]
    exact hsupIndep.disjoint_sup_sup (by simp) (by simp) huv
  have hWRg_disj_of_orbit_disj {Y Z : Ωsub}
      (hYZ : Disjoint (MulAction.orbit (↥R) Y) (MulAction.orbit (↥R) Z)) :
      Disjoint (WRg Y) (WRg Z) := by
    simpa [WRg] using Subgroup.disjoint_map htoVg_inj (hWR_disj_of_orbit_disj hYZ)
  have hfaithK :
      actionCentralizerIn (A := ↥K) (G := ↥V) (⊤ : Subgroup K) = ⊥ := by
    let Kg : Subgroup G := K.map H.subtype
    let KR : Subgroup G := Kg ⊔ R
    have hKRnormVg : KR ≤ Subgroup.normalizer (Vg : Set G) :=
      Subgroup.le_normalizer_of_normal (H := Vg)
    have : Subgroup.Normalizes KR Vg := ⟨hKRnormVg⟩
    have hcentKR :
        actionCentralizerIn (A := ↥KR) (G := ↥Vg) (⊤ : Subgroup KR) = ⊥ := by
      subst hR_eq
      simpa [KR, Kg, Vg, V] using
        theorem_3_6_centralizer_KR₀_on_fitting_eq_bot H R R p hind hsolvG hodd hHR
          hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup hK_inv hNK_inv hVNK_sup
          hVinfNK_bot hKsub_fit hCH_le_K
    apply bot_unique
    intro k hk
    let kg : KR := ⟨((k : H) : G), by
      exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem H.subtype k.2)⟩
    have hkfix : k ∈ fixingSubgroupOf (↥K) (↥V) (Set.univ : Set V) := by
      rw [actionCentralizerIn] at hk
      exact hk.2
    have hkgfix : kg ∈ fixingSubgroupOf (↥KR) (↥Vg) (Set.univ : Set Vg) := by
      rw [mem_fixingSubgroup_iff]
      intro v _
      rcases Subgroup.mem_map.mp v.2 with ⟨x, hx, hxv⟩
      let xV : V := ⟨x, hx⟩
      have hv : v = toVg xV := by
        apply Subtype.ext
        exact hxv.symm
      subst v
      apply Subtype.ext
      have hxfix : k • xV = xV :=
        (mem_fixingSubgroup_iff (M := ↥K) (s := (Set.univ : Set V))).1 hkfix xV (by trivial)
      have hxfixH : (((k : K) • xV : V) : H) = (xV : H) := congrArg Subtype.val hxfix
      have hxfixG := congrArg H.subtype hxfixH
      change ((k : H) : G) * (toVg xV : G) * ((k : H) : G)⁻¹ = (toVg xV : G) at hxfixG
      exact hxfixG
    have hkgcent : kg ∈ actionCentralizerIn (A := ↥KR) (G := ↥Vg) (⊤ : Subgroup KR) := by
      rw [actionCentralizerIn]
      exact ⟨by simp, hkgfix⟩
    have hkgbot : kg ∈ (⊥ : Subgroup KR) := by
      simpa [hcentKR] using hkgcent
    have hkg_one : kg = 1 := by simpa using hkgbot
    apply Subtype.ext
    apply H.subtype_injective
    change ((k : H) : G) = 1
    simpa [kg] using congrArg Subtype.val hkg_one
  have hΩ_not_subsingleton : ¬ Subsingleton Ωsub := by
    intro hsub
    rcases hΩ_nonempty with ⟨Y0, hY0Ω⟩
    let Y0sub : Ωsub := ⟨Y0, hY0Ω⟩
    have hF_eq : iSup F = F Y0sub := by
      apply le_antisymm
      · refine iSup_le ?_
        intro Y
        simp [Subsingleton.elim Y Y0sub]
      · exact le_iSup F Y0sub
    have hFY0_top : F Y0sub = ⊤ := by
      calc
        F Y0sub = iSup F := hF_eq.symm
        _ = ⊤ := hF_iSup_top
    exact
      theorem_3_6_hyperplane_fixed_singleton_false (K := ↥K) (V := ↥V)
        (Y := Y0sub.1) hfaithK
        (hF_cyclicQuot Y0sub) hK_not_cyclic hFY0_top
  have hR_nontriv : ∃ Y : Ωsub, ∃ a : R, a • Y ≠ Y := by
    by_contra hall
    push Not at hall
    let τ : Sg →* Equiv.Perm Ωsub := MulAction.toPermHom (G := ↥Sg) (α := Ωsub)
    let Psubgsub : Subgroup Sg := Psubg.subgroupOf Sg
    let Rsub : Subgroup Sg := R.subgroupOf Sg
    have hsub_sup : Psubgsub ⊔ Rsub = ⊤ := by
      calc
        Psubgsub ⊔ Rsub = (Psubg ⊔ R).subgroupOf Sg := by
          symm
          exact Subgroup.subgroupOf_sup (A := Psubg) (A' := R) (B := Sg) le_sup_left le_sup_right
        _ = ⊤ := by simp [Sg]
    have hRsub_map_bot : Rsub.map τ = ⊥ := by
      apply bot_unique
      intro x hx
      rw [Subgroup.mem_bot]
      rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
      let aR : R := ⟨((a : Sg) : G), ha⟩
      apply Equiv.ext
      intro Y
      apply Subtype.ext
      have haY := hall Y aR
      change (a : Sg) • Y = Y at haY
      simpa [τ, Rsub] using congrArg Subtype.val haY
    have hPsubgsub_eq_comm : Psubgsub = ⁅Psubgsub, Rsub⁆ := by
      apply (Subgroup.map_injective (f := Sg.subtype) Sg.subtype_injective)
      calc
        Psubgsub.map Sg.subtype = Psubg := by
          simpa [Psubgsub] using
            Subgroup.map_subgroupOf_eq_of_le (G := G) (H := Psubg) (K := Sg) le_sup_left
        _ = ⁅Psubg, R₀⁆ := (theorem_3_6_pSubgroup_eq_commutator_with_R₀ H R R₀ p hind hsolvG
          hodd hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K hVK_sup P hP_p
          hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K).1
        _ = ⁅Psubg, R⁆ := by simp [hR_eq]
        _ = (⁅Psubgsub, Rsub⁆).map Sg.subtype := by
          symm
          rw [Subgroup.map_commutator]
          rw [Subgroup.map_subgroupOf_eq_of_le (G := G) (H := Psubg) (K := Sg) le_sup_left]
          rw [Subgroup.map_subgroupOf_eq_of_le (G := G) (H := R) (K := Sg) le_sup_right]
    have hPsubgsub_map_bot : Psubgsub.map τ = ⊥ := by
      calc
        Psubgsub.map τ = (⁅Psubgsub, Rsub⁆).map τ := by
          simpa using congrArg (fun S : Subgroup Sg => S.map τ) hPsubgsub_eq_comm
        _ = ⁅Psubgsub.map τ, Rsub.map τ⁆ := by
          simpa using (Subgroup.map_commutator (H₁ := Psubgsub) (H₂ := Rsub) τ)
        _ = ⊥ := by
          simp [hRsub_map_bot]
    have hτrange_bot : τ.range = ⊥ := by
      rw [MonoidHom.range_eq_map]
      rw [← hsub_sup, Subgroup.map_sup]
      simp [hPsubgsub_map_bot, hRsub_map_bot]
    have hS_triv (a : Sg) (Y : Ωsub) : a • Y = Y := by
      have ha_range : τ a ∈ τ.range := MonoidHom.mem_range.mpr ⟨a, rfl⟩
      have ha_bot : τ a ∈ (⊥ : Subgroup (Equiv.Perm Ωsub)) := by
        simpa [hτrange_bot] using ha_range
      have ha_one : τ a = 1 := by simpa using ha_bot
      simpa [τ] using congrArg (fun f : Equiv.Perm Ωsub => f Y) ha_one
    have hsub : Subsingleton Ωsub := ⟨fun Y Z => by
      rcases (MulAction.mem_orbit_iff.mp (hS_transitive Y Z)) with ⟨a, rfl⟩
      exact (hS_triv a Y).symm⟩
    exact hΩ_not_subsingleton hsub
  have hR_prime : Nat.Prime (Nat.card R) := by
    simpa [hR_eq] using hR₀_prime
  let : Fact (Nat.card R).Prime := ⟨hR_prime⟩
  let : Fintype ↥R := Fintype.ofFinite ↥R
  have hR_pgroup : IsPGroup (Nat.card R) ↥R := by
    simpa using (IsPGroup.of_card (p := Nat.card R) (G := ↥R) (n := 1) (by simp))
  have hstab_bot_of_nonfix {Y : Ωsub} (hY_nonfix : ∃ a : R, a • Y ≠ Y) :
      MulAction.stabilizer (↥R) Y = ⊥ := by
    rcases hY_nonfix with ⟨a, ha_move⟩
    have hstabY_ne_top : MulAction.stabilizer (↥R) Y ≠ ⊤ := by
      intro htop
      have ha_stab : a ∈ MulAction.stabilizer (↥R) Y := by
        simp [htop]
      exact ha_move (MulAction.mem_stabilizer_iff.mp ha_stab)
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (MulAction.stabilizer (↥R) Y) with
      hbot | htop
    · exact hbot
    · exact False.elim (hstabY_ne_top htop)
  have hsmul_mem_F {Y : Ωsub} (a : R) (x : F Y) : a • (x : V) ∈ F (a • Y) := by
    have hxmap :
        (ρV (ιR a)) (x : V) ∈ (F Y).map (ρV (ιR a) : ↥V →* ↥V) :=
      Subgroup.mem_map_of_mem _ x.2
    have hxF : (ρV (ιR a)) (x : V) ∈ F (a • Y) := (hF_map_le (ιR a) Y hxmap)
    have hιR_smul : (ιR a : Sg) • (x : V) = a • (x : V) := by
      apply Subtype.ext
      change (ιR a : Sg) • ((x : V) : H) = a • ((x : V) : H)
      apply H.subtype_injective
      calc
        H.subtype ((ιR a : Sg) • ((x : V) : H)) =
            (ιR a : G) * (((x : V) : H) : G) * (ιR a : G)⁻¹ :=
          hS_smul_H_coe (ιR a) ((x : V) : H)
        _ = (a : G) * (((x : V) : H) : G) * (a : G)⁻¹ := by rfl
        _ = H.subtype (a • ((x : V) : H)) := by
          symm
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    simpa [ρV, MulDistribMulAction.toMulAut_apply, hιR_smul] using hxF
  have horbit_injective {Y : Ωsub} (hstabY_bot : MulAction.stabilizer (↥R) Y = ⊥) :
      Function.Injective (fun a : R => a • Y) := by
    intro a b hab
    have hstab : b⁻¹ * a ∈ MulAction.stabilizer (↥R) Y := by
      rw [MulAction.mem_stabilizer_iff]
      calc
        (b⁻¹ * a) • Y = b⁻¹ • (a • Y) := by simp [mul_smul]
        _ = b⁻¹ • (b • Y) := by simp [hab]
        _ = Y := by simp
    have hbot : b⁻¹ * a ∈ (⊥ : Subgroup R) := by simpa [hstabY_bot] using hstab
    have hone : b⁻¹ * a = 1 := by simpa using hbot
    simpa using (inv_mul_eq_iff_eq_mul.mp hone)
  let : CommGroup V := inferInstance
  have hcard_F_eq_p_and_fix_le_WRg_of_stab_bot {Y : Ωsub}
      (hstabY_bot : MulAction.stabilizer (↥R) Y = ⊥) :
      Nat.card (F Y) = p ∧ fixedPointSubgroup (↥R) (↥Vg) ≤ WRg Y := by
    have hFY_iSupIndep : iSupIndep (fun a : R => F (a • Y)) :=
      hF_iSupIndep.comp (horbit_injective hstabY_bot)
    have hleftmul_bij (b : R) : Function.Bijective (fun a : R => b * a) := by
      constructor
      · intro a₁ a₂ h
        exact mul_left_cancel h
      · intro a
        refine ⟨b⁻¹ * a, ?_⟩
        simp
    let traceV : F Y →* V :=
      { toFun := fun x => ∏ a : R, a • (x : V)
        map_one' := by simp
        map_mul' := by
          intro x y
          simp [smul_mul', Finset.prod_mul_distrib] }
    have htraceV_mem_WR (x : F Y) : traceV x ∈ WR Y := by
      dsimp [traceV, WR]
      exact
        Subgroup.prod_mem (WR Y) (t := Finset.univ) (fun a _ =>
          have hAY_orbit : a • Y ∈ MulAction.orbit (↥R) Y := by
            exact MulAction.mem_orbit_iff.mpr ⟨a, rfl⟩
          have hF_le_WR : F (a • Y) ≤ WR Y := by
            exact le_iSup_of_le (a • Y) <| le_iSup_of_le hAY_orbit le_rfl
          show a • (x : V) ∈ WR Y from
            hF_le_WR (hsmul_mem_F a x))
    have htraceV_fixed (x : F Y) (b : R) : b • traceV x = traceV x := by
      calc
        b • traceV x = ∏ a : R, b • (a • (x : V)) := by
          simpa [traceV] using
            (Finset.smul_prod' (s := Finset.univ) (r := b) (f := fun a : R => a • (x : V)))
        _ = ∏ a : R, (b * a) • (x : V) := by simp [mul_smul]
        _ = ∏ a : R, a • (x : V) := by
          exact (hleftmul_bij b).prod_comp (fun a : R => a • (x : V))
        _ = traceV x := by rfl
    have htraceVg_fixed (x : F Y) : toVg (traceV x) ∈ fixedPointSubgroup (↥R) (↥Vg) := by
      rw [FixedPoints.mem_subgroup]
      intro b
      simpa [htoVg_smul] using congrArg toVg (htraceV_fixed x b)
    let traceFix : F Y →* fixedPointSubgroup (↥R) (↥Vg) :=
      { toFun := fun x => ⟨toVg (traceV x), htraceVg_fixed x⟩
        map_one' := by
          apply Subtype.ext
          simp [traceV]
        map_mul' := by
          intro x y
          ext
          simp [traceV, Finset.prod_mul_distrib] }
    have htraceFix_mem_WRg (x : F Y) :
        ((traceFix x : fixedPointSubgroup (↥R) (↥Vg)) : Vg) ∈ WRg Y := by
      change toVg (traceV x) ∈ WRg Y
      exact Subgroup.mem_map_of_mem _ (htraceV_mem_WR x)
    have htraceFix_injective : Function.Injective traceFix := by
      intro x y hxy
      have hxy_one : traceFix (x * y⁻¹) = 1 := by
        rw [map_mul, map_inv, hxy]
        simp
      have htrace_one : traceV (x * y⁻¹) = 1 := by
        apply htoVg_inj
        simpa [traceFix] using congrArg Subtype.val hxy_one
      have hone_all :
          ∀ a ∈ (Finset.univ : Finset R), a • (((x * y⁻¹ : F Y) : F Y) : V) = 1 := by
        have hnoncomm :=
          Subgroup.eq_one_of_noncommProd_eq_one_of_iSupIndep
            (s := Finset.univ) (f := fun a : R => a • (((x * y⁻¹ : F Y) : F Y) : V))
            (comm := fun _ _ _ _ _ => Commute.all _ _)
            (K := fun a : R => F (a • Y)) hFY_iSupIndep
            (hmem := fun a _ => hsmul_mem_F a (x * y⁻¹ : F Y))
            (heq1 := by simpa [traceV, Finset.noncommProd_eq_prod] using htrace_one)
        exact hnoncomm
      have hone : (1 : R) • (((x * y⁻¹ : F Y) : F Y) : V) = 1 := hone_all 1 (by simp)
      have hmul_eq_one : x * y⁻¹ = 1 := by
        apply Subtype.ext
        simpa using hone
      exact mul_inv_eq_one.mp hmul_eq_one
    have hcardFY_le :
        Nat.card (F Y) ≤ Nat.card (fixedPointSubgroup (↥R) (↥Vg)) :=
      Nat.card_le_card_of_injective (f := traceFix) htraceFix_injective
    have hcardFY_le_p : Nat.card (F Y) ≤ p := by
      exact hCfixVg_card ▸ hcardFY_le
    have hcardFY_ne_one : Nat.card (F Y) ≠ 1 := by
      intro hcard_one
      exact hF_ne_bot Y ((Subgroup.card_eq_one (H := F Y)).1 hcard_one)
    have : Nontrivial ↥(F Y) := (F Y).nontrivial_iff_ne_bot.mpr (hF_ne_bot Y)
    obtain ⟨x, hx_ne_one⟩ := exists_ne (1 : F Y)
    have hxpowV : ((x : F Y) : V) ^ p = 1 := by
      exact
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent ↥V ∣ p by simpa using hV_elem.exponent_dvd_p) (((x : F Y) : V))
    have hxpow : x ^ p = 1 := by
      apply Subtype.ext
      simpa using hxpowV
    have horder_eq_p : orderOf x = p := orderOf_eq_prime hxpow hx_ne_one
    have hp_dvd_cardFY : p ∣ Nat.card (F Y) := by
      rw [← horder_eq_p]
      exact orderOf_dvd_natCard x
    have hcardFY_ge_p : p ≤ Nat.card (F Y) := Nat.le_of_dvd Nat.card_pos hp_dvd_cardFY
    have hcardFY : Nat.card (F Y) = p := by
      exact le_antisymm hcardFY_le_p hcardFY_ge_p
    have htraceFix_range_top : traceFix.range = ⊤ := by
      apply (Subgroup.card_eq_iff_eq_top (H := traceFix.range)).1
      calc
        Nat.card traceFix.range = Nat.card (F Y) := by
          rw [MonoidHom.range_eq_map]
          simpa using
            (Subgroup.card_map_of_injective (K := (⊤ : Subgroup (F Y))) (f := traceFix)
              htraceFix_injective)
        _ = p := hcardFY
        _ = Nat.card (fixedPointSubgroup (↥R) (↥Vg)) := hCfixVg_card.symm
    have hfix_le_WRg : fixedPointSubgroup (↥R) (↥Vg) ≤ WRg Y := by
      intro z hz
      have hz_range :
          (⟨z, hz⟩ : fixedPointSubgroup (↥R) (↥Vg)) ∈ traceFix.range := by
        simp [htraceFix_range_top]
      rcases hz_range with ⟨x, hx⟩
      have hxWRg :
          ((traceFix x : fixedPointSubgroup (↥R) (↥Vg)) : Vg) ∈ WRg Y :=
        htraceFix_mem_WRg x
      simpa [hx] using hxWRg
    exact ⟨hcardFY, hfix_le_WRg⟩
  rcases hR_nontriv with ⟨Y0, a0, ha0_move⟩
  have hstabY0_ne_top : MulAction.stabilizer (↥R) Y0 ≠ ⊤ := by
    intro htop
    have ha0_stab : a0 ∈ MulAction.stabilizer (↥R) Y0 := by
      simp [htop]
    exact ha0_move (MulAction.mem_stabilizer_iff.mp ha0_stab)
  have hstabY0_bot : MulAction.stabilizer (↥R) Y0 = ⊥ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (MulAction.stabilizer (↥R) Y0) with
      hbot | htop
    · exact hbot
    · exact False.elim (hstabY0_ne_top htop)
  have hcardFY0 : Nat.card (F Y0) = p :=
    (hcard_F_eq_p_and_fix_le_WRg_of_stab_bot hstabY0_bot).1
  have hfix_le_WRgY0 : fixedPointSubgroup (↥R) (↥Vg) ≤ WRg Y0 :=
    (hcard_F_eq_p_and_fix_le_WRg_of_stab_bot hstabY0_bot).2
  have hCfixVg_ne_bot : fixedPointSubgroup (↥R) (↥Vg) ≠ ⊥ := by
    intro hbot
    have hcard_one : Nat.card (fixedPointSubgroup (↥R) (↥Vg)) = 1 := by
      simp [hbot]
    exact hp.ne_one (hCfixVg_card.symm.trans hcard_one)
  have hfix_le_WRg_of_nonfix {Y : Ωsub} (hY_nonfix : ∃ a : R, a • Y ≠ Y) :
      fixedPointSubgroup (↥R) (↥Vg) ≤ WRg Y :=
    (hcard_F_eq_p_and_fix_le_WRg_of_stab_bot (hstab_bot_of_nonfix hY_nonfix)).2
  have hnontriv_orbit_unique {Y Z : Ωsub}
      (hY_nonfix : ∃ a : R, a • Y ≠ Y) (hZ_nonfix : ∃ a : R, a • Z ≠ Z)
      (hYZ : Disjoint (MulAction.orbit (↥R) Y) (MulAction.orbit (↥R) Z)) : False := by
    have hfix_le_Y : fixedPointSubgroup (↥R) (↥Vg) ≤ WRg Y := hfix_le_WRg_of_nonfix hY_nonfix
    have hfix_le_Z : fixedPointSubgroup (↥R) (↥Vg) ≤ WRg Z := hfix_le_WRg_of_nonfix hZ_nonfix
    have hfix_le_bot : fixedPointSubgroup (↥R) (↥Vg) ≤ ⊥ := by
      intro x hx
      have hxY : x ∈ WRg Y := hfix_le_Y hx
      have hxZ : x ∈ WRg Z := hfix_le_Z hx
      have hxinf : x ∈ WRg Y ⊓ WRg Z := ⟨hxY, hxZ⟩
      simpa [hWRg_disj_of_orbit_disj hYZ |>.eq_bot] using hxinf
    exact hCfixVg_ne_bot (bot_unique hfix_le_bot)
  have hcardF_all (Y : Ωsub) : Nat.card (F Y) = p := by
    rcases MulAction.mem_orbit_iff.mp (hS_transitive Y0 Y) with ⟨a, rfl⟩
    have hle₁ : Nat.card (F Y0) ≤ Nat.card (F (a • Y0)) := by
      let f : F Y0 → F (a • Y0) := fun x =>
        ⟨(ρV a) x, hF_map_le a Y0 (Subgroup.mem_map_of_mem (ρV a : ↥V →* ↥V) x.2)⟩
      exact Nat.card_le_card_of_injective (f := f) (by
        intro x y hxy
        apply Subtype.ext
        exact (ρV a).injective (congrArg Subtype.val hxy))
    have hle₂ : Nat.card (F (a • Y0)) ≤ Nat.card (F Y0) := by
      let f : F (a • Y0) → F ((a⁻¹ : Sg) • (a • Y0)) := fun x =>
        ⟨(ρV a⁻¹) x, hF_map_le a⁻¹ (a • Y0)
          (Subgroup.mem_map_of_mem (ρV a⁻¹ : ↥V →* ↥V) x.2)⟩
      have hcard_le :
          Nat.card (F (a • Y0)) ≤ Nat.card (F ((a⁻¹ : Sg) • (a • Y0))) :=
        Nat.card_le_card_of_injective (f := f) (by
          intro x y hxy
          apply Subtype.ext
          exact (ρV a⁻¹).injective (congrArg Subtype.val hxy))
      simpa using hcard_le
    exact (le_antisymm hle₂ hle₁).trans hcardFY0
  have hF_cyclic_prime (Y : Ωsub) : IsCyclic ↥(F Y) := by
    exact isCyclic_of_prime_card (α := ↥(F Y)) (hcardF_all Y)
  let : CommGroup K := IsMulCommutative.instCommGroup
  let CfixK : Subgroup K := fixedPointSubgroup (↥R) (↥K)
  let Kcomm : Subgroup K := commutatorAction (A := ↥R) (G := ↥K)
  have hcopRK : Nat.Coprime (Nat.card R) (Nat.card K) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card K) hcopHR.symm
  obtain ⟨qFix, hqFix_prime, hCfixK_card', _hCfixK_inf_comm_bot⟩ :=
    theorem_3_6_K_fixed_card_eq_q_and_inf_commutator_eq_bot H R R₀ p hind hsolvG hodd
      hHR hcopHR hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj
      hK_inv hNK_inv hPsub_inv hVNK_sup hVinfNK_bot hKsub_fit hCH_le_K hP_p hPK_ne_bot
      hproper hR_eq
  have hCfixK_q : IsPGroup qK CfixK := by
    exact (IsElementaryAbelian.isPGroup qK ↥K).of_injective CfixK.subtype CfixK.subtype_injective
  have hCfixK_card_ne_one : Nat.card CfixK ≠ 1 := by
    intro hcard_one
    exact hqFix_prime.ne_one (hCfixK_card'.symm.trans hcard_one)
  have hqK_dvd_cardCfixK : qK ∣ Nat.card CfixK :=
    (hCfixK_q.card_eq_or_dvd).resolve_left hCfixK_card_ne_one
  have hqFix_eq_qK : qFix = qK := by
    rw [hCfixK_card'] at hqK_dvd_cardCfixK
    exact (Nat.prime_dvd_prime_iff_eq hqK_prime hqFix_prime).1 hqK_dvd_cardCfixK |>.symm
  have hCfixK_card : Nat.card CfixK = qK := by
    exact hCfixK_card'.trans hqFix_eq_qK
  have hcomplK : IsCompl CfixK Kcomm :=
    proposition_1_6_d (G := ↥K) (A := ↥R)
      (by have : Group.IsSolvable G := hsolvG; infer_instance) hcopRK (by infer_instance)
  have hsup_CfixK_Kcomm : CfixK ⊔ Kcomm = ⊤ := hcomplK.sup_eq_top
  have hdisj_CfixK_Kcomm : Disjoint CfixK Kcomm := hcomplK.disjoint
  have hmul_univ_CfixK_Kcomm : (↑CfixK : Set K) * (↑Kcomm : Set K) = Set.univ := by
    ext x
    constructor
    · intro _; simp
    · intro _hx
      have hxsup : x ∈ CfixK ⊔ Kcomm := by simp [hsup_CfixK_Kcomm]
      rcases (Subgroup.mem_sup.mp hxsup) with ⟨y, hy, z, hz, rfl⟩
      exact Set.mem_mul.mpr ⟨y, hy, z, hz, rfl⟩
  have hcomplK' : CfixK.IsComplement' Kcomm :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj_CfixK_Kcomm hmul_univ_CfixK_Kcomm
  have hKcomm_index : Kcomm.index = qK := by
    calc
      Kcomm.index = Nat.card CfixK := hcomplK'.index_eq_card
      _ = qK := hCfixK_card
  have hR_fixed_eq_Kcomm {Y : Ωsub} (hY_fix : ∀ a : R, a • Y = Y) : Y.1 = Kcomm := by
    have hFY_invR : IsInvariant (↥R) (↥V) (F Y) := by
      have hforward : ∀ a : R, ∀ {x : V}, x ∈ F Y → a • x ∈ F Y := by
        intro a x hx
        let xFY : F Y := ⟨x, hx⟩
        simpa [hY_fix a] using hsmul_mem_F a xFY
      refine ⟨?_⟩
      intro a x
      constructor
      · exact hforward a
      · intro hx
        have hx' : a⁻¹ • (a • x) ∈ F Y := hforward a⁻¹ hx
        simpa [inv_smul_smul] using hx'
    let : IsInvariant (↥R) (↥V) (F Y) := hFY_invR
    let : IsInvariant (↥K) (↥V) (F Y) := hF_Kinv Y
    let CY : Subgroup K := actionCentralizerIn (A := ↥K) (G := ↥(F Y)) (⊤ : Subgroup K)
    have hY_le_CY : Y.1 ≤ CY := by
      intro y hy
      change y ∈ (⊤ : Subgroup K) ⊓ fixingSubgroupOf (↥K) (↥(F Y)) Set.univ
      constructor
      · simp
      · change y ∈ fixingSubgroupOf (↥K) (↥(F Y)) Set.univ
        rw [mem_fixingSubgroup_iff]
        intro v _hv
        apply Subtype.ext
        have hvfix : (v : V) ∈ fixedPointSubgroup (↥Y.1) (↥V) := by
          simp [F]
        exact hvfix ⟨y, hy⟩
    have hCY_ne_top : CY ≠ ⊤ := by
      intro hCY_top
      have hFY_le_fixK : F Y ≤ fixedPointSubgroup (↥K) (↥V) := by
        intro x hx
        rw [FixedPoints.mem_subgroup]
        intro k
        have hkCY : k ∈ CY := by simp [CY, hCY_top]
        have hkpair : k ∈ (⊤ : Subgroup K) ⊓ fixingSubgroupOf (↥K) (↥(F Y)) Set.univ := by
          simpa [CY, actionCentralizerIn] using hkCY
        have hkfix : k ∈ fixingSubgroupOf (↥K) (↥(F Y)) Set.univ := hkpair.2
        have hkx : k • (⟨x, hx⟩ : F Y) = ⟨x, hx⟩ :=
          (mem_fixingSubgroup_iff (M := ↥K) (s := (Set.univ : Set (F Y)))).1 hkfix _ (by trivial)
        exact congrArg Subtype.val hkx
      have hFY_le_bot : F Y ≤ ⊥ := by
        intro x hx
        have hxfixK : x ∈ fixedPointSubgroup (↥K) (↥V) := hFY_le_fixK hx
        simpa [hfixK_V_bot] using hxfixK
      exact hF_ne_bot Y (bot_unique hFY_le_bot)
    have hCY_eq_Y_or_top : CY = Y.1 ∨ CY = ⊤ := by
      have hCY_index_dvd : CY.index ∣ Y.1.index := Subgroup.index_dvd_of_le hY_le_CY
      rcases hqK_prime.eq_one_or_self_of_dvd CY.index (Y.2.1 ▸ hCY_index_dvd) with
        hidx_one | hidx_q
      · exact Or.inr (Subgroup.index_eq_one.mp hidx_one)
      · left
        have hcardCY_eq : Nat.card CY = Nat.card Y.1 := by
          apply Nat.eq_of_mul_eq_mul_left hqK_prime.pos
          calc
            qK * Nat.card CY = CY.index * Nat.card CY := by rw [hidx_q]
            _ = Nat.card K := Subgroup.index_mul_card (H := CY)
            _ = Y.1.index * Nat.card Y.1 := (Subgroup.index_mul_card (H := Y.1)).symm
            _ = qK * Nat.card Y.1 := by rw [Y.2.1]
        exact (Subgroup.eq_of_le_of_card_ge hY_le_CY (le_of_eq hcardCY_eq)).symm
    have hCY_eq_Y : CY = Y.1 := by
      rcases hCY_eq_Y_or_top with hCY_eq | hCY_top
      · exact hCY_eq
      · exact False.elim (hCY_ne_top hCY_top)
    let ρ : R →* MulAut ↥(F Y) := MulDistribMulAction.toMulAut (G := ↥R) (M := ↥(F Y))
    let ψ : K →* MulAut ↥(F Y) := MulDistribMulAction.toMulAut (G := ↥K) (M := ↥(F Y))
    let eAut : MulAut ↥(F Y) ≃* (ZMod (Nat.card (F Y)))ˣ := IsCyclic.mulAutMulEquiv (G := ↥(F Y))
    let : CommGroup (MulAut ↥(F Y)) :=
      MonoidHom.commGroupOfInjective eAut.toMonoidHom eAut.injective
    have hψker : ψ.ker = CY := by
      simp [ψ, CY, actionCentralizerIn, fixingSubgroupOf_univ_eq_ker_toMulAut]
    have hιR_smul_K (a : R) (g : K) : (ιR a : Sg) • g = (a : R) • g := by
      apply Subtype.ext
      apply H.subtype_injective
      change (((ιR a : Sg) • (g : H) : H) : G) = (((a : R) • (g : H) : H) : G)
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, ιR, mul_assoc]
    have hιR_smul_V (a : R) (x : V) : (ιR a : Sg) • x = (a : R) • x := by
      apply Subtype.ext
      apply H.subtype_injective
      change (((ιR a : Sg) • (x : H) : H) : G) = (((a : R) • (x : H) : H) : G)
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, ιR, mul_assoc]
    have hψ_smul (a : R) (g : K) : ψ (a • g) = ψ g := by
      apply DFunLike.ext
      intro v
      have hfirst : ψ (a • g) v = (ρ a) (ψ g ((ρ a)⁻¹ v)) := by
        apply Subtype.ext
        have h := hρ_transport (ιR a) g ((((a⁻¹ : R) • v : F Y) : F Y) : V)
        have h' :
            ((a • g : K) • ((a : R) • (((a⁻¹ : R) • v : F Y) : V) : V) : V) =
              ((a : R) • ((g : K) • (((a⁻¹ : R) • v : F Y) : V) : V) : V) := by
          simpa [ρ, ψ, ρK, ρV, ιR, MulDistribMulAction.toMulAut_apply,
            hιR_smul_K, hιR_smul_V] using h
        have hv : (a : R) • ((a⁻¹ : R) • v : F Y) = v := by
          simp [smul_smul]
        have hvV : (((a : R) • ((a⁻¹ : R) • v : F Y) : F Y) : V) = v := by
          exact congrArg Subtype.val hv
        calc
          ((((a • g : K) • v : F Y) : F Y) : V) =
              ((a • g : K) • (((a : R) • ((a⁻¹ : R) • v : F Y) : F Y) : V) : V) := by
                exact congrArg (fun x : V => ((a • g : K) • x : V)) hvV.symm
          _ = ((a : R) • ((g : K) • (((a⁻¹ : R) • v : F Y) : V) : V) : V) := h'
      have hcomm :
          (ρ a * ψ g) ((ρ a)⁻¹ v) = (ψ g * ρ a) ((ρ a)⁻¹ v) := by
        exact congrArg (fun f : MulAut ↥(F Y) => f ((ρ a)⁻¹ v)) (mul_comm (ρ a) (ψ g))
      have hcomm' : (ρ a) (ψ g ((ρ a)⁻¹ v)) = ψ g v := by
        simpa [MulAut.mul_apply] using hcomm
      exact hfirst.trans hcomm'
    have hKcomm_le_ker : Kcomm ≤ ψ.ker := by
      change commutatorAction (A := ↥R) (G := ↥K) ≤ ψ.ker
      rw [commutatorAction_eq_closure (G := ↥K) (A := ↥R)]
      refine (Subgroup.closure_le (K := ψ.ker)).2 ?_
      intro x hx
      rcases hx with ⟨a, g, rfl⟩
      change ψ (g⁻¹ * (a • g)) = 1
      rw [map_mul, map_inv, hψ_smul]
      simp
    have hKcomm_le_CY : Kcomm ≤ CY := by
      rw [← hψker]
      exact hKcomm_le_ker
    have hKcomm_le_Y : Kcomm ≤ Y.1 := by
      simpa [CY, hCY_eq_Y] using hKcomm_le_CY
    have hcardKcomm_eq : Nat.card Kcomm = Nat.card Y.1 := by
      apply Nat.eq_of_mul_eq_mul_left hqK_prime.pos
      calc
        qK * Nat.card Kcomm = Kcomm.index * Nat.card Kcomm := by rw [hKcomm_index]
        _ = Nat.card K := Subgroup.index_mul_card (H := Kcomm)
        _ = Y.1.index * Nat.card Y.1 := (Subgroup.index_mul_card (H := Y.1)).symm
        _ = qK * Nat.card Y.1 := by rw [Y.2.1]
    exact (Subgroup.eq_of_le_of_card_ge hKcomm_le_Y (le_of_eq hcardKcomm_eq.symm)).symm
  have hfixed_unique {Y Z : Ωsub}
      (hY_fix : ∀ a : R, a • Y = Y) (hZ_fix : ∀ a : R, a • Z = Z) : Y = Z := by
    apply Subtype.ext
    calc
      Y.1 = Kcomm := hR_fixed_eq_Kcomm hY_fix
      _ = Z.1 := (hR_fixed_eq_Kcomm hZ_fix).symm
  let orbitR0 : Set Ωsub := MulAction.orbit (↥R) Y0
  let FixR : Set Ωsub := MulAction.fixedPoints (↥R) Ωsub
  have hcard_orbitR0 : orbitR0.ncard = Nat.card R := by
    calc
      orbitR0.ncard = (MulAction.stabilizer (↥R) Y0).index := by
        simpa [orbitR0] using (MulAction.index_stabilizer (G := ↥R) (x := Y0)).symm
      _ = Nat.card R := by
        simp [hstabY0_bot]
  have hfixed_outside_orbit {Y : Ωsub} (hY_out : Y ∉ orbitR0) : Y ∈ FixR := by
    by_contra hY_notfix
    have hY_nonfix : ∃ a : R, a • Y ≠ Y := by
      by_contra hY_fix
      push Not at hY_fix
      exact hY_notfix (by simpa [FixR, MulAction.mem_fixedPoints] using hY_fix)
    have hdisj : Disjoint orbitR0 (MulAction.orbit (↥R) Y) := by
      rw [Set.disjoint_left]
      intro U hU0 hUY
      have hUeq0 : MulAction.orbit (↥R) U = orbitR0 :=
        (MulAction.orbit_eq_iff (G := ↥R) (a := U) (b := Y0)).2 hU0
      have hUeqY : MulAction.orbit (↥R) U = MulAction.orbit (↥R) Y :=
        (MulAction.orbit_eq_iff (G := ↥R) (a := U) (b := Y)).2 hUY
      have hYeq0 : MulAction.orbit (↥R) Y = orbitR0 := by
        calc
          MulAction.orbit (↥R) Y = MulAction.orbit (↥R) U := hUeqY.symm
          _ = orbitR0 := hUeq0
      have hY_mem : Y ∈ orbitR0 := by
        rw [← hYeq0]
        exact MulAction.mem_orbit_self Y
      exact hY_out hY_mem
    exact hnontriv_orbit_unique ⟨a0, ha0_move⟩ hY_nonfix hdisj
  have hFixR_card_le_one : FixR.ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff]
    intro Y Z hY hZ
    exact hfixed_unique
      ((MulAction.mem_fixedPoints (M := ↥R) (α := Ωsub)).1 hY)
      ((MulAction.mem_fixedPoints (M := ↥R) (α := Ωsub)).1 hZ)
  have hdisj_orbitR0_FixR : Disjoint orbitR0 FixR := by
    rw [Set.disjoint_left]
    intro Y hY_orbit hY_fix
    have hY_fixed_orbit :
        ∀ Z : Ωsub, Z ∈ MulAction.orbit (↥R) Y → Z = Y :=
      (MulAction.mem_fixedPoints' (M := ↥R) (α := Ωsub)).1 hY_fix
    have hY0_mem : Y0 ∈ MulAction.orbit (↥R) Y := by
      have hYeq0 : MulAction.orbit (↥R) Y = orbitR0 :=
        (MulAction.orbit_eq_iff (G := ↥R) (a := Y) (b := Y0)).2 hY_orbit
      rw [hYeq0]
      exact MulAction.mem_orbit_self Y0
    have hY_eq : Y = Y0 := (hY_fixed_orbit Y0 hY0_mem).symm
    have hY0_fix : ∀ a : R, a • Y0 = Y0 := by
      intro a
      simpa [hY_eq] using ((MulAction.mem_fixedPoints (M := ↥R) (α := Ωsub)).1 hY_fix) a
    exact ha0_move (hY0_fix a0)
  have hcardOmega_split : Nat.card Ωsub = Nat.card R ∨ Nat.card Ωsub = Nat.card R + 1 := by
    have hcover : orbitR0 ∪ FixR = Set.univ := by
      ext Y
      constructor
      · intro _; simp
      · intro _
        by_cases hY_orbit : Y ∈ orbitR0
        · exact Or.inl hY_orbit
        · exact Or.inr (hfixed_outside_orbit hY_orbit)
    have hcard_union : Nat.card Ωsub = Nat.card R + FixR.ncard := by
      calc
        Nat.card Ωsub = (Set.univ : Set Ωsub).ncard := by symm; exact Set.ncard_univ Ωsub
        _ = (orbitR0 ∪ FixR).ncard := by rw [hcover]
        _ = orbitR0.ncard + FixR.ncard := Set.ncard_union_eq hdisj_orbitR0_FixR
        _ = Nat.card R + FixR.ncard := by rw [hcard_orbitR0]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hFixR_card_le_one with hFix0 | hFix1
    · left
      simpa [hFix0] using hcard_union
    · right
      simpa [hFix1] using hcard_union
  rcases hcardOmega_split with hcardOmega_eq | hcardOmega_eq
  · have hp_dvd_H : p ∣ Nat.card H := by
      by_contra hp_ndvd_H
      exact hbad <| hasPLengthOne_of_coprime_card (p := p) ((hp.coprime_iff_not_dvd).2 hp_ndvd_H)
    have hcop_p_R : Nat.Coprime p (Nat.card R) := Nat.Coprime.of_dvd_left hp_dvd_H hcopHR
    have hPsub_p : IsPGroup p Psub := by
      change IsPGroup p (normalizerSubtypeMap K P)
      exact isPGroup_normalizerSubtypeMap K P hP_p
    have hPsubg_p : IsPGroup p Psubg := by
      simpa [Psubg] using hPsub_p.map H.subtype
    have hp_not_dvd_Omega : ¬ p ∣ Nat.card Ωsub := by
      intro hp_dvd_Omega
      exact (hp.coprime_iff_not_dvd).1 hcop_p_R (hcardOmega_eq ▸ hp_dvd_Omega)
    obtain ⟨Y, hY_fixPsubg_mem⟩ :=
      hPsubg_p.nonempty_fixed_point_of_prime_not_dvd_card Ωsub hp_not_dvd_Omega
    have hY_fixPsubg : ∀ a : Psubg, a • Y = Y :=
      (MulAction.mem_fixedPoints (M := ↥Psubg) (α := Ωsub)).1 hY_fixPsubg_mem
    have hPsubnormV : Psub ≤ Subgroup.normalizer V := Subgroup.le_normalizer_of_normal (H := V)
    have : Subgroup.Normalizes Psub V := ⟨hPsubnormV⟩
    let actP_V : MulDistribMulAction (↥Psub) (↥V) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (G := H) Psub V hPsubnormV
    have hP_smul_V_coe (a : Psub) (x : V) :
        ((a • x : V) : H) = (a : H) * (x : H) * (a : H)⁻¹ := by
      change ((actP_V.smul a x : V) : H) = (a : H) * (x : H) * (a : H)⁻¹
      exact
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
          (G := H) Psub V hPsubnormV a x
    have hιPsubg_smul_V (a : Psub) (x : V) :
        (ιPsubg ⟨((a : H) : G), Subgroup.mem_map_of_mem H.subtype a.2⟩ : Sg) • x = a • x := by
      apply Subtype.ext
      apply H.subtype_injective
      calc
        (((((ιPsubg ⟨((a : H) : G), Subgroup.mem_map_of_mem H.subtype a.2⟩ : Sg) • x : V) : H) : G)) =
            (((ιPsubg ⟨((a : H) : G), Subgroup.mem_map_of_mem H.subtype a.2⟩ : Sg) : G) *
              (x : H) * (((ιPsubg ⟨((a : H) : G), Subgroup.mem_map_of_mem H.subtype a.2⟩ : Sg) : G)⁻¹)) := by
              rfl
        _ = ((a : H) : G) * (x : H) * (((a : H) : G)⁻¹) := by
              rfl
        _ = ((((a • x : V) : H) : G)) := by
              simpa only [Subgroup.coe_mul, InvMemClass.coe_inv] using
                congrArg Subtype.val (hP_smul_V_coe a x).symm
    have hFY_invP : IsInvariant (↥Psub) (↥V) (F Y) := by
      have hforward : ∀ a : Psub, ∀ {x : V}, x ∈ F Y → a • x ∈ F Y := by
        intro a x hx
        let ag : Psubg := ⟨((a : H) : G), Subgroup.mem_map_of_mem H.subtype a.2⟩
        have hag_fix : (ιPsubg ag : Sg) • Y = Y := by
          have hag_fix' := hY_fixPsubg ag
          change (ιPsubg ag : Sg) • Y = Y at hag_fix'
          exact hag_fix'
        have hxmap :
            (ρV (ιPsubg ag)) x ∈ (F Y).map (ρV (ιPsubg ag) : ↥V →* ↥V) :=
          Subgroup.mem_map_of_mem (ρV (ιPsubg ag) : ↥V →* ↥V) hx
        have hxFY : (ρV (ιPsubg ag)) x ∈ F ((ιPsubg ag : Sg) • Y) := hF_map_le (ιPsubg ag) Y hxmap
        simpa [hag_fix, F, ρV, ag, hιPsubg_smul_V a, MulDistribMulAction.toMulAut_apply] using hxFY
      refine ⟨?_⟩
      intro a x
      constructor
      · exact hforward a
      · intro hx
        have hx' : a⁻¹ • (a • x) ∈ F Y := hforward a⁻¹ hx
        simpa [inv_smul_smul] using hx'
    let : IsInvariant (↥Psub) (↥V) (F Y) := hFY_invP
    let : IsInvariant (↥K) (↥V) (F Y) := hF_Kinv Y
    let CY : Subgroup K := actionCentralizerIn (A := ↥K) (G := ↥(F Y)) (⊤ : Subgroup K)
    have hY_le_CY : Y.1 ≤ CY := by
      intro y hy
      change y ∈ (⊤ : Subgroup K) ⊓ fixingSubgroupOf (↥K) (↥(F Y)) Set.univ
      constructor
      · simp
      · change y ∈ fixingSubgroupOf (↥K) (↥(F Y)) Set.univ
        rw [mem_fixingSubgroup_iff]
        intro v _hv
        apply Subtype.ext
        have hvfix : (v : V) ∈ fixedPointSubgroup (↥Y.1) (↥V) := by
          simp [F]
        exact hvfix ⟨y, hy⟩
    have hCY_ne_top : CY ≠ ⊤ := by
      intro hCY_top
      have hFY_le_fixK : F Y ≤ fixedPointSubgroup (↥K) (↥V) := by
        intro x hx
        rw [FixedPoints.mem_subgroup]
        intro k
        have hkCY : k ∈ CY := by simp [CY, hCY_top]
        have hkpair : k ∈ (⊤ : Subgroup K) ⊓ fixingSubgroupOf (↥K) (↥(F Y)) Set.univ := by
          simpa [CY, actionCentralizerIn] using hkCY
        have hkfix : k ∈ fixingSubgroupOf (↥K) (↥(F Y)) Set.univ := hkpair.2
        have hkx : k • (⟨x, hx⟩ : F Y) = ⟨x, hx⟩ :=
          (mem_fixingSubgroup_iff (M := ↥K) (s := (Set.univ : Set (F Y)))).1 hkfix _ (by trivial)
        exact congrArg Subtype.val hkx
      have hFY_le_bot : F Y ≤ ⊥ := by
        intro x hx
        have hxfixK : x ∈ fixedPointSubgroup (↥K) (↥V) := hFY_le_fixK hx
        simpa [hfixK_V_bot] using hxfixK
      exact hF_ne_bot Y (bot_unique hFY_le_bot)
    have hCY_eq_Y_or_top : CY = Y.1 ∨ CY = ⊤ := by
      have hCY_index_dvd : CY.index ∣ Y.1.index := Subgroup.index_dvd_of_le hY_le_CY
      rcases hqK_prime.eq_one_or_self_of_dvd CY.index (Y.2.1 ▸ hCY_index_dvd) with hidx_one | hidx_q
      · exact Or.inr (Subgroup.index_eq_one.mp hidx_one)
      · left
        have hcardCY_eq : Nat.card CY = Nat.card Y.1 := by
          apply Nat.eq_of_mul_eq_mul_left hqK_prime.pos
          calc
            qK * Nat.card CY = CY.index * Nat.card CY := by rw [hidx_q]
            _ = Nat.card K := Subgroup.index_mul_card (H := CY)
            _ = Y.1.index * Nat.card Y.1 := (Subgroup.index_mul_card (H := Y.1)).symm
            _ = qK * Nat.card Y.1 := by rw [Y.2.1]
        exact (Subgroup.eq_of_le_of_card_ge hY_le_CY (le_of_eq hcardCY_eq)).symm
    have hCY_eq_Y : CY = Y.1 := by
      rcases hCY_eq_Y_or_top with hCY_eq | hCY_top
      · exact hCY_eq
      · exact False.elim (hCY_ne_top hCY_top)
    let ρ : Psub →* MulAut ↥(F Y) := MulDistribMulAction.toMulAut (G := ↥Psub) (M := ↥(F Y))
    let ψ : K →* MulAut ↥(F Y) := MulDistribMulAction.toMulAut (G := ↥K) (M := ↥(F Y))
    let eAut : MulAut ↥(F Y) ≃* (ZMod (Nat.card (F Y)))ˣ := IsCyclic.mulAutMulEquiv (G := ↥(F Y))
    let : CommGroup (MulAut ↥(F Y)) :=
      MonoidHom.commGroupOfInjective eAut.toMonoidHom eAut.injective
    have hψker : ψ.ker = CY := by
      simp [ψ, CY, actionCentralizerIn, fixingSubgroupOf_univ_eq_ker_toMulAut]
    have hP_transport (a : Psub) (g : K) (x : V) :
        ((a • g : K) • (a • x : V) : V) = (a : Psub) • ((g : K) • x : V) := by
      apply Subtype.ext
      rw [hK_smul_V_coe (a • g) (a • x)]
      rw [hP_smul_K_coe a g, hP_smul_V_coe a x]
      rw [hP_smul_V_coe a ((g : K) • x), hK_smul_V_coe g x]
      simp only [mul_assoc, mul_inv_rev, inv_inv, inv_mul_cancel_left]
    have hψ_smul (a : Psub) (g : K) : ψ (a • g) = ψ g := by
      apply DFunLike.ext
      intro v
      have hfirst : ψ (a • g) v = (ρ a) (ψ g ((ρ a)⁻¹ v)) := by
        apply Subtype.ext
        let v' : F Y := (ρ a)⁻¹ v
        have hv : (ρ a) v' = v := by
          simp [v']
        have hvV : (((ρ a) v' : F Y) : V) = v := congrArg Subtype.val hv
        have hρ_coe : (((ρ a) v' : F Y) : V) = a • (v' : V) := by
          change ((a • v' : F Y) : V) = a • (v' : V)
          rfl
        calc
          ((((a • g : K) • v : F Y) : F Y) : V) =
              ((a • g : K) • (((ρ a) v' : F Y) : V) : V) := by
                exact congrArg (fun z : V => ((a • g : K) • z : V)) hvV.symm
          _ = ((a : Psub) • ((g : K) • (v' : V) : V) : V) := by
            rw [hρ_coe]
            exact hP_transport a g (v' : V)
      have hcomm :
          (ρ a * ψ g) ((ρ a)⁻¹ v) = (ψ g * ρ a) ((ρ a)⁻¹ v) := by
        exact congrArg (fun f : MulAut ↥(F Y) => f ((ρ a)⁻¹ v)) (mul_comm (ρ a) (ψ g))
      have hcomm' : (ρ a) (ψ g ((ρ a)⁻¹ v)) = ψ g v := by
        simpa [MulAut.mul_apply] using hcomm
      exact hfirst.trans hcomm'
    have hKcomm_le_ker : commutatorAction (A := ↥Psub) (G := ↥K) ≤ ψ.ker := by
      rw [commutatorAction_eq_closure (G := ↥K) (A := ↥Psub)]
      refine (Subgroup.closure_le (K := ψ.ker)).2 ?_
      intro x hx
      rcases hx with ⟨a, g, rfl⟩
      change ψ (g⁻¹ * (a • g)) = 1
      rw [map_mul, map_inv, hψ_smul]
      simp
    have hKcomm_le_CY : commutatorAction (A := ↥Psub) (G := ↥K) ≤ CY := by
      rw [← hψker]
      exact hKcomm_le_ker
    have hKcomm_le_Y : commutatorAction (A := ↥Psub) (G := ↥K) ≤ Y.1 := by
      simpa [CY, hCY_eq_Y] using hKcomm_le_CY
    have hKP_eq : K = ⁅K, Psub⁆ := by
      simpa [Psub] using
        theorem_3_6_K_eq_commutator_with_P H R R₀ p hind hsolvG hodd hHR hcopHR
          hR₀_le hR₀_prime hp hCZ hcomm_eq hbad K P hVK_sup hVK_disj hK_inv hPsub_inv hKsub_fit
          hP_p hPK_ne_bot hproper
    have hKcomm_map_eq : (commutatorAction (A := ↥Psub) (G := ↥K)).map K.subtype = ⁅K, Psub⁆ := by
      simpa using commutatorAction_subgroup_conj_map_eq_commutator K Psub hPsub_normK
    have hK_le_Ymap : K ≤ Y.1.map K.subtype := by
      calc
        K = ⁅K, Psub⁆ := hKP_eq
        _ = (commutatorAction (A := ↥Psub) (G := ↥K)).map K.subtype := hKcomm_map_eq.symm
        _ ≤ Y.1.map K.subtype := Subgroup.map_mono hKcomm_le_Y
    have hYmap_le_K : Y.1.map K.subtype ≤ K := Subgroup.map_subtype_le Y.1
    have hY_top : Y.1 = ⊤ := by
      apply top_unique
      intro k hk
      have hkmap : ((k : K) : H) ∈ Y.1.map K.subtype := hK_le_Ymap k.2
      rcases Subgroup.mem_map.mp hkmap with ⟨y, hy, hyk⟩
      exact K.subtype_injective hyk ▸ hy
    have hqK_eq_one : qK = 1 := by
      simpa [hY_top] using Y.2.1.symm
    exact hqK_prime.ne_one hqK_eq_one
  · have hR_odd : Odd (Nat.card R) := odd_of_card_dvd hodd (Subgroup.card_subgroup_dvd_card R)
    have hcardOmega_even : Even (Nat.card Ωsub) := by
      rw [hcardOmega_eq]
      exact hR_odd.add_one
    have hoddSg : Odd (Nat.card Sg) := odd_of_card_dvd hodd (Subgroup.card_subgroup_dvd_card Sg)
    let : MulAction.IsPretransitive (↥Sg) Ωsub := ⟨hS_transitive⟩
    have hcardOmega_dvd : Nat.card Ωsub ∣ Nat.card Sg := by
      rw [← MulAction.index_stabilizer_of_transitive (G := ↥Sg) (x := Y0)]
      exact Subgroup.index_dvd_card (H := MulAction.stabilizer (↥Sg) Y0)
    have hcardOmega_odd : Odd (Nat.card Ωsub) := odd_of_card_dvd hoddSg hcardOmega_dvd
    exact (Nat.not_odd_iff_even.mpr hcardOmega_even) hcardOmega_odd

public theorem CFSG.theorem_3_6 {G : Type uG} [Group G] [Finite G] (H R R₀ : Subgroup G) (p : ℕ)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) [hH_normal : H.Normal]
    (hHR : H.IsComplement' R) (hcopHR : Nat.Coprime (Nat.card H) (Nat.card R))
    (hR₀_le : R₀ ≤ R) (hR₀_prime : Nat.Prime (Nat.card R₀))
    (hp : Nat.Prime p) (hCZ : IsZGroup ↥(subgroupCentralizerIn H R₀)) :
    HasPLengthOne p ↥⁅H, R⁆ := by
  let P : ℕ → Prop := fun n =>
    ∀ (G' : Type uG) [Group G'] [Finite G'] (H' R' R₀' : Subgroup G') (p' : ℕ),
      Nat.card G' = n →
      Group.IsSolvable G' →
      Odd (Nat.card G') →
      H'.Normal →
      H'.IsComplement' R' →
      Nat.Coprime (Nat.card H') (Nat.card R') →
      R₀' ≤ R' →
      Nat.Prime (Nat.card R₀') →
      Nat.Prime p' →
      IsZGroup ↥(subgroupCentralizerIn H' R₀') →
      HasPLengthOne p' ↥⁅H', R'⁆
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih G' _ _ H' R' R₀' p' hcard hsolvG' hodd' hH'_normal hH'R' hcopH'R'
      hR₀'_le hR₀'_prime hp' hCZ'
    let : H'.Normal := hH'_normal
    have hind : Theorem36IndHyp H' := by
      intro G'' _ _ H'' R'' R₀'' p'' hlt hsolvG'' hodd'' hH''_normal hH''R'' hcopH''R''
        hR₀''_le hR₀''_prime hp'' hCZ''
      have hlt' : Nat.card G'' < n := by
        simpa [hcard] using hlt
      exact
        ih (Nat.card G'') hlt' G'' H'' R'' R₀'' p'' rfl hsolvG'' hodd'' hH''_normal hH''R''
          hcopH''R'' hR₀''_le hR₀''_prime hp'' hCZ''
    by_cases hcomm_lt : ⁅H', R'⁆ < H'
    · exact
        theorem_3_6_reduce_eq_commutator H' R' R₀' p' hind hsolvG' hodd' hH'R'
          hcopH'R' hR₀'_le hR₀'_prime hp' hCZ' hcomm_lt
    · have hcomm_eq : ⁅H', R'⁆ = H' := by
        have hcomm_le : ⁅H', R'⁆ ≤ H' := Subgroup.commutator_le_left (H₁ := H') (H₂ := R')
        apply le_antisymm hcomm_le
        by_contra hcontra
        have hneq : ⁅H', R'⁆ ≠ H' := by
          intro hEq
          exact hcontra (hEq.symm.le)
        exact hcomm_lt (lt_of_le_of_ne hcomm_le hneq)
      by_cases hbad : ¬ HasPLengthOne p' ↥H'
      · exact False.elim <|
          theorem_3_6_final_contradiction H' R' R₀' p' hind hsolvG' hodd' hH'R'
            hcopH'R' hR₀'_le hR₀'_prime hp' hCZ' hcomm_eq hbad
      · have hgood : HasPLengthOne p' ↥H' := by
          classical
          exact not_not.mp hbad
        let : Fact p'.Prime := ⟨hp'⟩
        let ecomm : ↥H' ≃* ↥⁅H', R'⁆ := MulEquiv.subgroupCongr hcomm_eq.symm
        exact hasPLengthOne_of_equiv (p := p') ecomm hgood
  exact hP (Nat.card G) G H R R₀ p rfl hsolvG hodd hH_normal hHR hcopHR hR₀_le hR₀_prime hp
    hCZ
