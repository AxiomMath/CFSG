module

public import CFSG.LieType.Chevalley.EvenTrialityTorusCoordinates
public import CFSG.RankThree.PartOne.KGD.D4Frame
import CFSG.LieType.Chevalley.EvenCartanRootDiagonals
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD

private lemma iterate_three_eq_pow {n : ℕ} {L : Type} [Monoid L] (f : L → L)
    (hf : ∀ c, f c = c ^ 2 ^ n) (x : L) :
    f (f (f x)) = x ^ (2 ^ n) ^ 3 := by
  rw [hf, hf, hf]
  calc ((x ^ 2 ^ n) ^ 2 ^ n) ^ 2 ^ n
      = (x ^ 2 ^ n) ^ (2 ^ n * 2 ^ n) := (pow_mul _ _ _).symm
    _ = x ^ (2 ^ n * (2 ^ n * 2 ^ n)) := (pow_mul _ _ _).symm
    _ = x ^ (2 ^ n) ^ 3 := by congr 1; ring

theorem triD4Line_exists_trialityTorusHom_baseChange
    {n : ℕ} (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (L : Type) [Field L] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2 ^ n) (h : ModGL Tag.D4 L)
    (hT : h ∈ torusGroup Tag.D4 L) (hF : twistHom TwistTag.D4 L Fr h = h) :
    ∃ p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ,
      baseChangeGL (algebraMap K L) (trialityTorusHom σ p) = h := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  letI : Fintype K := Fintype.ofFinite K
  have hcard : ∀ c : K, c ^ Nat.card K = c := fun c => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    rw [ringEquiv_pow_three_apply]
    change σ (σ (σ c)) = c
    rw [iterate_three_eq_pow (n := n) (⇑σ) hσ c, ← hK]
    exact hcard c
  have hT' : h ∈ torusGroup TwistTag.D4.tag L := hT
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT'
  have hcompat : ∀ i, c (TwistTag.D4.perm i) = Units.map Fr.toMonoidHom (c i) :=
    compat_of_twistHom_rootDiagUnit (t := TwistTag.D4) (b := c) hF
  have hFv : ∀ i, (c (TwistTag.D4.perm i) : L) = Fr (c i : L) := fun i => by
    simpa using congrArg Units.val (hcompat i)
  have hperm3 : ∀ i : Fin 4,
      TwistTag.D4.perm (TwistTag.D4.perm (TwistTag.D4.perm i)) = i := by
    intro i
    fin_cases i <;> rfl
  have hf3 : ∀ i, (c i : L) = Fr (Fr (Fr (c i : L))) := by
    intro i
    calc (c i : L)
        = (c (TwistTag.D4.perm (TwistTag.D4.perm (TwistTag.D4.perm i))) : L) :=
          congrArg (fun j => (c j : L)) (hperm3 i).symm
      _ = Fr (c (TwistTag.D4.perm (TwistTag.D4.perm i)) : L) := hFv _
      _ = Fr (Fr (c (TwistTag.D4.perm i) : L)) := congrArg Fr (hFv _)
      _ = Fr (Fr (Fr (c i : L))) := congrArg (fun y => Fr (Fr y)) (hFv i)
  have hpow : ∀ i, (c i : L) ^ Nat.card K = (c i : L) := by
    intro i
    rw [hK, ← iterate_three_eq_pow (n := n) (⇑Fr) hFr (c i : L)]
    exact (hf3 i).symm
  have hrange : ∀ i, ∃ a : K, algebraMap K L a = (c i : L) := fun i =>
    mem_range_algebraMap_of_pow_card_eq (hpow i)
  let ck : Fin TwistTag.D4.tag.rank → K := fun i => Classical.choose (hrange i)
  have hck : ∀ i, algebraMap K L (ck i) = (c i : L) := fun i =>
    Classical.choose_spec (hrange i)
  let cu : Fin TwistTag.D4.tag.rank → Kˣ := fun i => Units.mk0 (ck i) (by
    intro hz
    have h := hck i
    rw [hz, map_zero] at h
    exact (c i).ne_zero h.symm)
  have hcu : ∀ i, Units.map (algebraMap K L).toMonoidHom (cu i) = c i := fun i =>
    Units.ext (by simpa [cu] using hck i)
  have hισ : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) := by
    ext x
    simp only [RingHom.comp_apply]
    change algebraMap K L (σ x) = Fr (algebraMap K L x)
    rw [hσ, hFr, map_pow]
  have hbc : baseChangeGL (algebraMap K L) (rootDiagUnit TwistTag.D4.tag cu) =
      rootDiagUnit TwistTag.D4.tag c := by
    rw [baseChangeGL_rootDiagUnit]
    congr 1
    funext i
    exact hcu i
  have hbc' : baseChangeGL (algebraMap K L)
      (twistHom TwistTag.D4 K σ.toRingHom (rootDiagUnit TwistTag.D4.tag cu)) =
      baseChangeGL (algebraMap K L) (rootDiagUnit TwistTag.D4.tag cu) := by
    rw [← twistHom_baseChangeGL (algebraMap K L) hισ (rootDiagUnit TwistTag.D4.tag cu), hbc]
    exact hF
  have hd_fix : twistHom TwistTag.D4 K σ.toRingHom (rootDiagUnit TwistTag.D4.tag cu) =
      rootDiagUnit TwistTag.D4.tag cu := baseChangeGL_injective (algebraMap K L) hbc'
  have hle : torusGroup Tag.D4 K ≤ adjointGroup Tag.D4 K :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  have hd_torus : rootDiagUnit TwistTag.D4.tag cu ∈ torusGroup TwistTag.D4.tag K :=
    (even_power_two_Cartan_root_diagonals_inner TwistTag.D4.tag (Or.inr (Or.inr (Or.inl rfl)))
      K (ringChar.eq K 2)).1 cu
  have hd : rootDiagUnit TwistTag.D4.tag cu ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨hd_torus,
      (mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).2
        ⟨hle hd_torus, hd_fix⟩⟩
  obtain ⟨p, hp⟩ := exists_trialityTorusHom_eq (K := K) (σ := σ) hσ3 hd
  exact ⟨p, by rw [hp]; exact hbc⟩

end CFSG.StandardType
