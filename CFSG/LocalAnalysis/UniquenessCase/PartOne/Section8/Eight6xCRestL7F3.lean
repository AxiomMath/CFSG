module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwAct
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
open CFSG.RankThree.Chevalley CFSG.RankThree.E6 CFSG.RegularModuleThree

open scoped Matrix

@[expose] noncomputable def f3Diag {L : Type} [Field L] (τ : Tag) (ζ : Lˣ)
    (x : Fin τ.rank → ZMod 3) : ModGL τ L :=
  rootDiagUnit τ (fun i => ζ ^ (x i).val)

theorem f3Diag_zero {L : Type} [Field L] {τ : Tag} (ζ : Lˣ) : f3Diag τ ζ 0 = 1 := by
  have h : (fun i : Fin τ.rank => ζ ^ ((0 : Fin τ.rank → ZMod 3) i).val) = 1 := by
    funext i
    simp
  rw [f3Diag, h, rootDiagUnit_one]

theorem f3Diag_pow_three {L : Type} [Field L] {τ : Tag} {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (x : Fin τ.rank → ZMod 3) :
    f3Diag τ ζ x ^ 3 = 1 := by
  simp only [f3Diag, rootDiagUnit_pow, ← rootDiagUnit_one]
  congr 1
  funext i
  rw [Pi.pow_apply, Pi.one_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem f3Diag_injective {L : Type} [Field L] {τ : Tag} {ζ : Lˣ}
    (hζ : orderOf ζ = 3) : Function.Injective (f3Diag τ ζ) := by
  have : NeZero 3 := ⟨by norm_num⟩
  intro x y hxy
  have h := CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := τ) (K := L) hxy
  funext i
  exact eq_of_pow_val_eq_pow_val hζ (congrFun h i)

theorem exists_f3Diag_eq {L : Type} [Field L] {τ : Tag} {ζ : Lˣ}
    (hζ : orderOf ζ = 3) {t : ModGL τ L} (ht : t ∈ torusGroup τ L) (ht3 : t ^ 3 = 1) :
    ∃ x, f3Diag τ ζ x = t := by
  have : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hb3 : b ^ 3 = 1 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := τ) (K := L)
    rw [← rootDiagUnit_pow, ht3, rootDiagUnit_one]
  have hbi : ∀ i, b i ^ 3 = 1 := fun i => by
    simpa using congrFun hb3 i
  choose m hm using fun i => exists_pow_val_eq_of_pow_eq_one hζ (hbi i)
  refine ⟨m, ?_⟩
  simp only [f3Diag]
  congr 1
  funext i
  exact hm i

private theorem f3Diag_mem_twistedTorus_iff_fixed_l7f {L : Type} [Field L]
    [IsAlgClosed L] (t : TwistTag) {ζ : Lˣ} {Fr : L →+* L} {v : WeylGroup t.tag}
    {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
    (hv : ∀ x, v • permLattice t.perm x = M *ᵥ x) (x : Fin t.tag.rank → ZMod 3) :
    f3Diag t.tag ζ x ∈
        twistedTorusOf (canonicalRep (coxeterSystem t.tag) L v) (twistHom t L Fr) ↔
      (fun i => ζ ^ (x i).val) ∈ fixedCharTuples M Fr := by
  rw [f3Diag, twistedTorusOf_twistHom_eq_map t Fr v M hv]
  constructor
  · rintro ⟨b, hb, hba⟩
    have hba' : b = (fun i => ζ ^ (x i).val) :=
      CFSG.LieType.Chevalley.rootDiagUnit_injective hba
    rwa [← hba']
  · rintro ha'
    exact ⟨_, ha', rfl⟩

theorem f3Diag_mem_twistedTorusOf_iff {L : Type} [Field L]
    [IsAlgClosed L] (t : TwistTag) {ζ : Lˣ} (hζ : orderOf ζ = 3) {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {v : WeylGroup t.tag}
    {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
    (hv : ∀ x, v • permLattice t.perm x = M *ᵥ x) (x : Fin t.tag.rank → ZMod 3) :
    f3Diag t.tag ζ x ∈
        twistedTorusOf (canonicalRep (coxeterSystem t.tag) L v) (twistHom t L Fr) ↔
      (M.map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x = (q : ZMod 3) • x := by
  have : NeZero 3 := ⟨by norm_num⟩
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  rw [f3Diag_mem_twistedTorus_iff_fixed_l7f t hv x, mem_fixedCharTuples_iff]
  constructor
  · intro h
    funext j
    have h1 := h (Pi.single j 1)
    rw [rootChar_pow_val_eq hζ x (M *ᵥ Pi.single j 1),
      CTTorus.map_units_eq_pow hFr, rootChar_pow_val_eq hζ x (Pi.single j 1),
      charVal_single, ← pow_mul] at h1
    have hcoord : ((M.map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x) j =
        charVal x (M *ᵥ Pi.single j 1) := by
      change ((M.map (Int.cast : ℤ → ZMod 3))ᵀ *ᵥ x) j =
        charVal x (M *ᵥ Pi.single j 1)
      rw [← charVal_single ((M.map (Int.cast : ℤ → ZMod 3))ᵀ *ᵥ x) j, charVal_mulVec]
    have hq : ζ ^ ((x j).val * q) = ζ ^ (((q : ZMod 3) * x j)).val := by
      refine pow_eq_pow_of_natCast_eq hζ3 ?_
      push_cast
      simp only [ZMod.natCast_zmod_val]
      ring
    simpa only [Pi.smul_apply, smul_eq_mul] using
      eq_of_pow_val_eq_pow_val hζ (by rw [hcoord]; exact h1.trans hq)
  · intro hx u
    rw [rootChar_pow_val_eq hζ x (M *ᵥ u), CTTorus.map_units_eq_pow hFr,
      rootChar_pow_val_eq hζ x u, ← pow_mul]
    have hx' : ((M.map (Int.cast : ℤ → ZMod 3))ᵀ *ᵥ x) = (q : ZMod 3) • x := hx
    have h1 : charVal x (M *ᵥ u) = (q : ZMod 3) * charVal x u := by
      rw [← charVal_mulVec, hx', charVal_smul_col]
    rw [h1]
    refine pow_eq_pow_of_natCast_eq hζ3 ?_
    push_cast
    simp only [ZMod.natCast_zmod_val]
    ring

theorem f3Diag_conj_of_twActsAs {L : Type} [Field L] {τ : Tag}
    {ζ : Lˣ} (hζ : ζ ^ 3 = 1) {g : ModGL τ L} {u : WeylGroup τ} (hg : TwActsAs g u)
    {W : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hW : ∀ y, u⁻¹ • y = W *ᵥ y)
    (x : Fin τ.rank → ZMod 3) :
    g * f3Diag τ ζ x * g⁻¹ = f3Diag τ ζ ((W.map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x) := by
  rw [f3Diag, hg]
  congr 1
  funext i
  by_cases h1 : ζ = 1
  · subst h1
    simp [weylTuple, rootChar]
  · have hord : orderOf ζ = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hζ) with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) h1
      · exact h
    have : NeZero 3 := ⟨by norm_num⟩
    rw [weylTuple, hW, rootChar_pow_val_eq hord x (W *ᵥ Pi.single i 1)]
    have hcoord : charVal x (W *ᵥ Pi.single i 1) =
        ((W.map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x) i := by
      change charVal x (W *ᵥ Pi.single i 1) =
        ((W.map (Int.cast : ℤ → ZMod 3))ᵀ *ᵥ x) i
      rw [← charVal_single ((W.map (Int.cast : ℤ → ZMod 3))ᵀ *ᵥ x) i, charVal_mulVec]
    rw [hcoord]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7
