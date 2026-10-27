module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitRoots
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeDiag
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
public import CFSG.LieType.Chevalley.KernelComponentRoots
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UG3
import CFSG.RankThree.Lattice.SteinbergBIE6QplusStab
import CFSG.LieType.Chevalley.E6RootInvolutionNoInverted

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.StandardType CFSG.StandardType.TableCRes CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.RankThree.E6 CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav
  CFSG.StandardType.ExcFrames.E6QPlusThree

noncomputable section


@[expose] def e6SplitRefl (i : ExcRaw.Root 1) : WeylGroup .E6 :=
  if ExcRaw.tabFix1.getD i.val false = true then rootReflection (e6SplitRoot i)
  else rootReflection (e6SplitRoot i) *
    rootReflection (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i))


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .E6 L p}

theorem rootDiagUnit_mem_fullThreeTorus_iff (hS : E6SplitLangTwo S) (a : Fin Tag.E6.rank → Lˣ) :
    rootDiagUnit .E6 a ∈ fullThreeTorus S ↔ a ^ 3 = 1 ∧ ∀ j, a (TwistTag.E6.perm j) = a j := by
  constructor
  · intro ht
    have hT : rootDiagUnit .E6 a ∈ S.D.torus := ht.1
    have h3 : a ^ 3 = 1 := by
      apply rootDiagUnit_injective (K := L)
      rw [← rootDiagUnit_pow, ht.2, rootDiagUnit_one]
    refine ⟨h3, fun j => ?_⟩
    have hρj : S.ρ (Pi.single j 1) =
        -permLattice (τ := .E6) TwistTag.E6.perm (Pi.single j 1) :=
      hS.2.2 (Pi.single j 1) (isRoot_single .E6 j)
    have hj := (rootDiagUnit_mem_langTorus_iff S a).1 hT (Pi.single j 1) (isRoot_single .E6 j)
    rw [hρj, hS.1] at hj
    have hperm : rootChar a (permLattice (τ := .E6) TwistTag.E6.perm (Pi.single j 1)) =
        a (TwistTag.E6.perm j) := by
      calc rootChar a (permLattice (τ := .E6) TwistTag.E6.perm (Pi.single j 1))
          = rootChar (fun i => a (TwistTag.E6.perm i)) (Pi.single j 1) :=
            rootChar_permLattice (τ := .E6) a TwistTag.E6.perm (Pi.single j 1)
        _ = a (TwistTag.E6.perm j) := by
            simpa using rootChar_nsmul_single (fun i => a (TwistTag.E6.perm i)) j 1
    have hneg : rootChar a (-permLattice (τ := .E6) TwistTag.E6.perm (Pi.single j 1)) =
        (a (TwistTag.E6.perm j))⁻¹ := by
      have h : rootChar a (-permLattice (τ := .E6) TwistTag.E6.perm (Pi.single j 1)) =
          (rootChar a (permLattice (τ := .E6) TwistTag.E6.perm (Pi.single j 1)))⁻¹ := by
        simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
      rw [h, hperm]
    have hpos : rootChar a (Pi.single j 1) = a j := by
      simpa using rootChar_nsmul_single a j 1
    rw [hneg, hpos] at hj
    have hja : a j ^ 2 = (a j)⁻¹ := by
      have h : (a j) ^ 3 = 1 := by
        have h' : (a ^ 3) j = (1 : Fin Tag.E6.rank → Lˣ) j := congrFun h3 j
        change (a j) ^ 3 = 1 at h'
        exact h'
      rw [pow_succ] at h
      exact eq_inv_iff_mul_eq_one.2 h
    rw [hja] at hj
    exact inv_injective hj
  · rintro ⟨h3, hσ⟩
    have hchar : ∀ γ, IsRoot .E6 γ → rootChar a (S.ρ γ) = rootChar a γ ^ S.D.q := by
      intro γ hγ
      have hσγ : rootChar a (permLattice (τ := .E6) TwistTag.E6.perm γ) =
          rootChar a γ := by
        calc rootChar a (permLattice (τ := .E6) TwistTag.E6.perm γ)
            = rootChar (fun i => a (TwistTag.E6.perm i)) γ :=
              rootChar_permLattice (τ := .E6) a TwistTag.E6.perm γ
          _ = rootChar a γ := by
              congr 1
              funext j
              exact hσ j
      have hneg : rootChar a (-permLattice (τ := .E6) TwistTag.E6.perm γ) =
          (rootChar a (permLattice (τ := .E6) TwistTag.E6.perm γ))⁻¹ := by
        simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
      have hρ : S.ρ γ = -permLattice (τ := .E6) TwistTag.E6.perm γ :=
        hS.2.2 γ hγ
      rw [hρ, hS.1, hneg, hσγ]
      have hcube : rootChar a γ ^ 3 = 1 := by
        rw [← rootChar_pow, h3]
        simp [rootChar]
      have hsq : rootChar a γ ^ 2 = (rootChar a γ)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        rw [pow_succ] at hcube
        exact hcube
      exact hsq.symm
    refine (mem_fullThreeTorus S).2 ⟨(rootDiagUnit_mem_langTorus_iff S a).2 hchar, ?_⟩
    rw [rootDiagUnit_pow, h3, rootDiagUnit_one]

theorem fullThreeTorus_eq_range_e6ThreeDiag (hS : E6SplitLangTwo S) {ζ : Lˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) : fullThreeTorus S = (e6ThreeDiag ζ hζ).range := by
  refine le_antisymm ?_ ?_
  · intro t ht
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
      ((inf_le_left : S.D.torus ≤ torusGroup .E6 L) ht.1)
    obtain ⟨hb3, hbσ⟩ := (rootDiagUnit_mem_fullThreeTorus_iff hS b).1 ht
    obtain ⟨x, hx⟩ := TableBExc.E6Three.exists_zetaVec_eq (τ := .E6) (p := 3) hζo hζ hb3
    have hcomp : TableBExc.E6Three.zetaVec ζ hζ (fun k => x (TwistTag.E6.perm k)) =
        fun k => b (TwistTag.E6.perm k) := by
      funext k
      rw [TableBExc.E6Three.zetaVec_apply]
      exact congrFun hx (TwistTag.E6.perm k)
    have hxσ : ∀ j, x (TwistTag.E6.perm j) = x j := by
      intro j
      have h1 : TableBExc.E6Three.zetaVec ζ hζ (fun k => x (TwistTag.E6.perm k)) =
          TableBExc.E6Three.zetaVec ζ hζ x := by
        rw [hcomp, funext hbσ, ← hx]
      exact congrFun (TableBExc.E6Three.zetaVec_injective hζo hζ h1) j
    have h0 : x (ExcFrames.e6Idx 0) = x ExcFrames.e6Five := by
      have hp0 : ExcFrames.e6Perm 0 = ExcFrames.e6Five := by decide
      have h := hxσ 0
      rw [show TwistTag.E6.perm 0 = ExcFrames.e6Perm 0 from rfl, hp0,
        show (0 : Fin TwistTag.E6.tag.rank) = ExcFrames.e6Idx 0 from rfl] at h
      exact h.symm
    have h2 : x (ExcFrames.e6Idx 2) = x ExcFrames.e6Four := by
      have hp2 : ExcFrames.e6Perm 2 = ExcFrames.e6Four := by decide
      have h := hxσ 2
      rw [show TwistTag.E6.perm 2 = ExcFrames.e6Perm 2 from rfl, hp2,
        show (2 : Fin TwistTag.E6.tag.rank) = ExcFrames.e6Idx 2 from rfl] at h
      exact h.symm
    obtain ⟨s, hs⟩ := (ExcFrames.exists_twE6ThreeFrame_eq_iff x).2 ⟨h0, h2⟩
    exact ⟨Multiplicative.ofAdd s, by rw [e6ThreeDiag_apply, hs, hx]⟩
  · intro x hx
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hx
    rw [← hs]
    rw [show s = Multiplicative.ofAdd (Multiplicative.toAdd s) from rfl, e6ThreeDiag_apply]
    refine (rootDiagUnit_mem_fullThreeTorus_iff hS _).2 ⟨?_, ?_⟩
    · funext i
      rw [Pi.pow_apply, TableBExc.E6Three.zetaVec_apply, Pi.one_apply, ← pow_mul, mul_comm,
        pow_mul, hζ, one_pow]
    · intro j
      have h := ExcFrames.twE6ThreeFrame_perm (Multiplicative.toAdd s) j
      change ζ ^ ((ExcFrames.twE6ThreeFrame (Multiplicative.toAdd s))
          (TwistTag.E6.perm j : Fin Tag.E6.rank)).val =
        ζ ^ ((ExcFrames.twE6ThreeFrame (Multiplicative.toAdd s)) j).val
      exact congrArg (fun z : ZMod 3 => ζ ^ z.val) h

theorem rootChar_permLattice_of_mem_fullThreeTorus (hS : E6SplitLangTwo S)
    {a : Fin Tag.E6.rank → Lˣ} (ha : rootDiagUnit .E6 a ∈ fullThreeTorus S)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar a (permLattice (τ := .E6) TwistTag.E6.perm v) = rootChar a v := by
  have haσ : ∀ j, a (TwistTag.E6.perm j) = a j :=
    ((rootDiagUnit_mem_fullThreeTorus_iff hS a).1 ha).2
  rw [rootChar_permLattice a TwistTag.E6.perm v]
  congr 1
  funext j
  exact haσ j

private theorem e6SplitRoot_corootPair_orth :
    ∀ i : ExcRaw.Root 1, ExcRaw.tabFix1.getD i.val false = false →
      corootPair (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)) (e6SplitRoot i) = 0 ∧
      corootPair (e6SplitRoot i)
        (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)) = 0 := by
  decide +kernel

private theorem corootPair_permLattice (β v : Fin Tag.E6.rank → ℤ) :
    corootPair (permLattice (τ := .E6) TwistTag.E6.perm β)
        (permLattice (τ := .E6) TwistTag.E6.perm v) = corootPair β v := by
  unfold corootPair
  have h1 : iform (permLattice (τ := .E6) TwistTag.E6.perm β)
      (permLattice (τ := .E6) TwistTag.E6.perm v) = iform β v := by
    convert iform_permLattice_e6Rho' β v using 2 <;> rfl
  have h2 : iform (permLattice (τ := .E6) TwistTag.E6.perm β)
      (permLattice (τ := .E6) TwistTag.E6.perm β) = iform β β := by
    convert iform_permLattice_e6Rho' β β using 2 <;> rfl
  rw [h1, h2]

private theorem corootPair_sub_smul {β v w : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) (c : ℤ) :
    corootPair β (v - c • w) = corootPair β v - c * corootPair β w := by
  have hI : iform β β ≠ 0 := ne_of_gt (iform_self_pos_of_isRoot hβ)
  have h1 := corootPair_mul hβ (v - c • w)
  have h2 := corootPair_mul hβ v
  have h3 := corootPair_mul hβ w
  rw [iform_sub_right, iform_smul_right] at h1
  refine mul_right_cancel₀ hI ?_
  rw [h1, sub_mul, h2, mul_assoc, h3]
  ring

omit
  [IsAlgClosed L] in
private theorem rootChar_sub_smul {b : Fin Tag.E6.rank → Lˣ} {v w : Fin Tag.E6.rank → ℤ}
    (c : ℤ) :
    rootChar b (v - c • w) = rootChar b v * (rootChar b w) ^ (-c) := by
  rw [rootChar_sub, rootChar_zsmul, zpow_neg]

omit
  [IsAlgClosed L] in
private theorem zeta_pow_val_mul_zpow {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (a b : ZMod 3) (n : ℤ) :
    ζ ^ a.val * (ζ ^ b.val) ^ (-n) = ζ ^ (a - (n : ZMod 3) * b).val := by
  have h := TableBExc.E6Three.zmodPowHom_zpow (p := 3) ζ hζ (-n) b
  rw [show ζ ^ a.val = CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
        (Multiplicative.ofAdd a) from rfl,
    show ζ ^ b.val = CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
        (Multiplicative.ofAdd b) from rfl,
    h, ← map_mul, ← ofAdd_add]
  rw [CFSG.RankThree.CentralCover.zmodPowHom_apply]
  congr 1
  push_cast
  ring_nf

omit
  [IsAlgClosed L] in
private theorem zeta_pow_val_injective' {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) :
    Function.Injective fun a : ZMod 3 => ζ ^ a.val := by
  intro a b h
  have h' : CFSG.SectionRank.zmodPowHom ζ hζ (Multiplicative.ofAdd a) =
      CFSG.SectionRank.zmodPowHom ζ hζ (Multiplicative.ofAdd b) := by
    simpa [CFSG.SectionRank.zmodPowHom] using h
  exact Multiplicative.ofAdd.injective
    (CFSG.StandardType.ReflSp.zmodPowHom_injective (p := 3) hζ hζo h')

private theorem e6SplitRoot_separating (v : ExcRaw.V 1)
    (hv : ∀ j : ExcRaw.Root 1, ExcRaw.root 1 j v = 0) : v = 0 := by
  have h : ∀ v : ExcRaw.V 1, (∀ j : ExcRaw.Root 1, ExcRaw.root 1 j v = 0) → v = 0 := by
    decide +kernel
  exact h v hv

namespace E6SplitDatum

variable {T₀ : Subgroup (ModGL .E6 L)} (d : E6SplitDatum S T₀)
include d

theorem orderOf_ζ : orderOf d.ζ = 3 := by
  have hdvd : orderOf d.ζ ∣ 3 := orderOf_dvd_of_pow_eq_one d.ζ_pow_three
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) d.ζ_ne_one
  · exact h

theorem eq_fullThreeTorus (hS : E6SplitLangTwo S) : T₀ = fullThreeTorus S := by
  have hcardT : Nat.card ↥T₀ = 3 ^ 4 := by
    calc Nat.card ↥T₀ = Nat.card (Additive ↥T₀) :=
          (Nat.card_congr Additive.toMul).symm
      _ = Nat.card (ExcRaw.V 1) := Nat.card_congr d.coord.toEquiv
      _ = 3 ^ 4 := by
          simp [CFSG.StandardType.GGQ2Frame.ExcRaw.V,
            CFSG.StandardType.GGQ2Frame.ExcRaw.dim, ZMod.card]
  have hfin : Finite ↥(fullThreeTorus S) := by
    rw [fullThreeTorus_eq_range_e6ThreeDiag hS (orderOf_ζ d) d.ζ_pow_three]
    exact Finite.of_equiv (Multiplicative (Fin Tag.F4.rank → ZMod 3))
      (Equiv.ofInjective (e6ThreeDiag d.ζ d.ζ_pow_three)
        (e6ThreeDiag_injective (orderOf_ζ d) d.ζ_pow_three))
  have hcardF : Nat.card ↥(fullThreeTorus S) = 3 ^ 4 := by
    rw [fullThreeTorus_eq_range_e6ThreeDiag hS (orderOf_ζ d) d.ζ_pow_three]
    calc Nat.card ↥(e6ThreeDiag d.ζ d.ζ_pow_three).range
        = Nat.card (Multiplicative (Fin Tag.F4.rank → ZMod 3)) :=
          (Nat.card_congr (Equiv.ofInjective (e6ThreeDiag d.ζ d.ζ_pow_three)
            (e6ThreeDiag_injective (orderOf_ζ d) d.ζ_pow_three))).symm
      _ = 3 ^ 4 := by
          rw [show Tag.F4.rank = 4 from rfl]
          norm_num
  exact Subgroup.eq_of_le_of_card_ge d.le_fullThreeTorus (by rw [hcardF, hcardT])

theorem exists_rootDiagUnit (t : ↥T₀) : ∃ b, (t : ModGL .E6 L) = rootDiagUnit .E6 b :=
  exists_rootDiagUnit_eq_of_mem_torusGroup
    ((inf_le_left : S.D.torus ≤ torusGroup .E6 L)
      (fullThreeTorus_le_torus S (d.le_fullThreeTorus t.2)))

theorem weylTuple_e6SplitRefl_mem (hS : E6SplitLangTwo S) (i : ExcRaw.Root 1)
    {b : Fin Tag.E6.rank → Lˣ} (hb : rootDiagUnit .E6 b ∈ T₀) :
    ∃ h : rootDiagUnit .E6 (weylTuple (e6SplitRefl i) b) ∈ T₀,
      d.coord (Additive.ofMul ⟨_, h⟩) =
        ExcRaw.reflection 1 i (d.coord (Additive.ofMul ⟨_, hb⟩)) := by
  have hbT : rootDiagUnit .E6 b ∈ fullThreeTorus S := d.le_fullThreeTorus hb
  obtain ⟨hb3, hbσ⟩ := (rootDiagUnit_mem_fullThreeTorus_iff hS b).1 hbT
  have hwG : e6SplitRefl i ∈ e6WGamma := by
    rw [e6SplitRefl]
    split_ifs with hlong
    · exact rootReflection_mem_relWeylTwist (isRoot_e6SplitRoot i)
        ((permLattice_e6SplitRoot_eq_iff i).2 hlong)
    · have hfalse : ExcRaw.tabFix1.getD i.val false = false := by
        simpa using hlong
      have hcp := (e6SplitRoot_corootPair_orth i hfalse).2
      have hmul := corootPair_mul (isRoot_e6SplitRoot i)
        (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i))
      rw [hcp] at hmul
      have hzero : iform (e6SplitRoot i)
          (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)) = 0 := by
        rw [zero_mul] at hmul
        exact (mul_eq_zero.mp hmul.symm).resolve_left (by norm_num)
      exact rootReflection_mul_mem_relWeylTwist (isRoot_e6SplitRoot i) hzero
  have hcomm : ∀ x, e6SplitRefl i • permLattice e6Rho x =
      permLattice e6Rho (e6SplitRefl i • x) :=
    (mem_e6WGamma_iff.1 hwG)
  have hcomm_inv : ∀ v, permLattice e6Rho ((e6SplitRefl i)⁻¹ • v) =
      (e6SplitRefl i)⁻¹ • permLattice e6Rho v := by
    intro v
    have h1 : e6SplitRefl i • permLattice e6Rho ((e6SplitRefl i)⁻¹ • v) =
        permLattice e6Rho v := by
      rw [hcomm, ← mul_smul, mul_inv_cancel, one_smul]
    calc permLattice e6Rho ((e6SplitRefl i)⁻¹ • v)
        = (e6SplitRefl i)⁻¹ • (e6SplitRefl i •
            permLattice e6Rho ((e6SplitRefl i)⁻¹ • v)) :=
          (inv_smul_smul (e6SplitRefl i) _).symm
      _ = (e6SplitRefl i)⁻¹ • permLattice e6Rho v := by rw [h1]
  have hcube : (weylTuple (e6SplitRefl i) b) ^ 3 = 1 := by
    funext k
    change (rootChar b ((e6SplitRefl i)⁻¹ • (Pi.single k 1 : Fin Tag.E6.rank → ℤ))) ^ 3 = 1
    rw [← rootChar_pow, hb3]
    simp [rootChar]
  have hσwb : ∀ k : Fin Tag.E6.rank,
      (weylTuple (e6SplitRefl i) b) (e6Rho k) =
      (weylTuple (e6SplitRefl i) b) k := by
    intro k
    change rootChar b ((e6SplitRefl i)⁻¹ •
        (Pi.single (e6Rho k) 1 : Fin Tag.E6.rank → ℤ)) =
      rootChar b ((e6SplitRefl i)⁻¹ • (Pi.single k 1 : Fin Tag.E6.rank → ℤ))
    have hsingle : permLattice e6Rho (Pi.single k 1) = Pi.single (e6Rho k) 1 :=
      permLattice_single e6Rho k
    rw [show Pi.single (e6Rho k) 1 = permLattice e6Rho (Pi.single k 1) from hsingle.symm,
      ← hcomm_inv]
    simpa [e6Rho] using rootChar_permLattice_of_mem_fullThreeTorus hS hbT
      ((e6SplitRefl i)⁻¹ • (Pi.single k 1 : Fin Tag.E6.rank → ℤ))
  have hmem : rootDiagUnit .E6 (weylTuple (e6SplitRefl i) b) ∈ T₀ := by
    rw [eq_fullThreeTorus d hS]
    exact (rootDiagUnit_mem_fullThreeTorus_iff hS _).2 ⟨hcube, hσwb⟩
  refine ⟨hmem, ?_⟩
  set v : ExcRaw.V 1 := d.coord (Additive.ofMul ⟨rootDiagUnit .E6 b, hb⟩) with hv
  set c : ExcRaw.V 1 :=
    d.coord (Additive.ofMul ⟨rootDiagUnit .E6 (weylTuple (e6SplitRefl i) b), hmem⟩) with hc
  have hroot_b : ∀ j, rootChar b (e6SplitRoot j) = d.ζ ^ (ExcRaw.root 1 j v).val := by
    intro j
    exact d.rootChar_eq ⟨rootDiagUnit .E6 b, hb⟩ b rfl j
  have hroot_w : ∀ j, rootChar (weylTuple (e6SplitRefl i) b) (e6SplitRoot j) =
      d.ζ ^ (ExcRaw.root 1 j c).val := by
    intro j
    exact d.rootChar_eq ⟨rootDiagUnit .E6 (weylTuple (e6SplitRefl i) b), hmem⟩
      (weylTuple (e6SplitRefl i) b) rfl j
  have hσchar : rootChar b (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)) =
      rootChar b (e6SplitRoot i) :=
    rootChar_permLattice_of_mem_fullThreeTorus hS hbT _
  have hrefl : ∀ j, ExcRaw.root 1 j (ExcRaw.reflection 1 i v) =
      ExcRaw.root 1 j v -
        (ExcRaw.pairing 1 j i : ZMod 3) * ExcRaw.root 1 i v := by
    intro j
    rw [ExcRaw.reflection_apply, map_sub, map_smul, ExcRaw.pairing_eq]
    simp only [smul_eq_mul, mul_comm]
  have hexp : ∀ j, ExcRaw.root 1 j c = ExcRaw.root 1 j (ExcRaw.reflection 1 i v) := by
    intro j
    have h1 : d.ζ ^ (ExcRaw.root 1 j c).val =
        rootChar b ((e6SplitRefl i)⁻¹ • e6SplitRoot j) := by
      rw [← hroot_w j, rootChar_weylTuple]
    have hγ : IsRoot .E6 (e6SplitRoot i) := isRoot_e6SplitRoot i
    have hσγ : IsRoot .E6 (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)) :=
      hγ.permLattice TwistTag.E6.cartan_perm
    by_cases hlong : ExcRaw.tabFix1.getD i.val false = true
    · have hσeq : permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i) = e6SplitRoot i :=
        (permLattice_e6SplitRoot_eq_iff i).2 hlong
      rw [e6SplitRefl, if_pos hlong] at h1
      rw [rootReflection_inv hγ, rootReflection_smul hγ] at h1
      rw [rootChar_sub_smul, hroot_b j, hroot_b i] at h1
      have hc1 : corootPair (e6SplitRoot i) (e6SplitRoot j) =
          (ExcRaw.pairing 1 j i : ℤ) := by
        calc corootPair (e6SplitRoot i) (e6SplitRoot j)
            = e6RelCorootPair (e6SplitRoot i) (e6SplitRoot j) := by
              rw [e6RelCorootPair, if_pos hσeq]
          _ = (ExcRaw.pairing 1 j i : ℤ) := (pairing_one_eq_e6RelCorootPair j i).symm
      rw [hc1, zeta_pow_val_mul_zpow (ζ := d.ζ) d.ζ_pow_three
        (ExcRaw.root 1 j v) (ExcRaw.root 1 i v) (ExcRaw.pairing 1 j i)] at h1
      have h := zeta_pow_val_injective' d.ζ_pow_three (orderOf_ζ d) h1
      rw [hrefl j]
      exact h
    · have hfalse : ExcRaw.tabFix1.getD i.val false = false := by simpa using hlong
      have hσne : permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i) ≠ e6SplitRoot i :=
        fun h => hlong ((permLattice_e6SplitRoot_eq_iff i).1 h)
      have horth := (e6SplitRoot_corootPair_orth i hfalse).1
      rw [e6SplitRefl, if_neg hlong] at h1
      rw [mul_inv_rev, rootReflection_inv hγ, rootReflection_inv hσγ] at h1
      rw [mul_smul, rootReflection_smul hγ, rootReflection_smul hσγ] at h1
      have hinv : ∀ x : Fin Tag.E6.rank → ℤ,
          permLattice (τ := .E6) TwistTag.E6.perm
            (permLattice (τ := .E6) TwistTag.E6.perm x) = x := by
        intro x
        simpa [e6Rho] using permLattice_e6Rho_e6Rho x
      have hperm : corootPair (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i))
          (e6SplitRoot j) =
          corootPair (e6SplitRoot i)
            (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot j)) := by
        have h := corootPair_permLattice (e6SplitRoot i)
          (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot j))
        rwa [hinv] at h
      rw [corootPair_sub_smul hσγ, horth, mul_zero, sub_zero, hperm] at h1
      rw [rootChar_sub_smul, rootChar_sub_smul, hσchar, hroot_b j, hroot_b i] at h1
      have hc : corootPair (e6SplitRoot i) (e6SplitRoot j) +
          corootPair (e6SplitRoot i)
            (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot j)) =
          (ExcRaw.pairing 1 j i : ℤ) := by
        have h := pairing_one_eq_e6RelCorootPair j i
        rw [e6RelCorootPair, if_neg hσne] at h
        rw [← hperm]
        exact h.symm
      rw [mul_assoc, ← zpow_add, ← neg_add, hc,
        zeta_pow_val_mul_zpow (ζ := d.ζ) d.ζ_pow_three
          (ExcRaw.root 1 j v) (ExcRaw.root 1 i v) (ExcRaw.pairing 1 j i)] at h1
      have h := zeta_pow_val_injective' d.ζ_pow_three (orderOf_ζ d) h1
      rw [hrefl j]
      convert h using 2
  have hcv : c = ExcRaw.reflection 1 i v := by
    have hzero : c - ExcRaw.reflection 1 i v = 0 := by
      apply e6SplitRoot_separating
      intro j
      rw [map_sub, hexp j, sub_self]
    exact sub_eq_zero.mp hzero
  exact hcv

end E6SplitDatum

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
