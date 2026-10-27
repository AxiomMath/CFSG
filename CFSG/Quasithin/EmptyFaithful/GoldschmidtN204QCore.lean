module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204QImg
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204Mod
public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin.N204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N X : Subgroup G}

theorem twoImg_pCoreOf_le : twoImg N (pCoreOf 2 X) ≤ pCoreOf 2 (twoImg N X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 (twoImg_mono (pCoreOf_le 2 X))
    (twoImg_le_normalizer (le_normalizer_pCoreOf 2 X)) (isPGroup_twoImg (pCoreOf_isPGroup 2 X))

theorem charTwo_twoImg (hXN : X ≤ N) (hQ : CharTwoMod X (pCoreOf 2 N)) :
    CharTwo (twoImg N X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨hxX, hxC⟩ := hx
  obtain ⟨g, hgX, rfl⟩ := mem_twoImg.mp hxX
  refine twoImg_pCoreOf_le (mem_twoImg.mpr ⟨g, hQ g hgX fun p hp => ?_, rfl⟩)
  have hpN : p ∈ N := hXN (pCoreOf_le 2 X hp)
  have hmem : twoProj N ⟨p, hpN⟩ ∈ pCoreOf 2 (twoImg N X) :=
    twoImg_pCoreOf_le (mem_twoImg.mpr ⟨⟨p, hpN⟩, hp, rfl⟩)
  have hcomm := Subgroup.mem_centralizer_iff.mp hxC _ hmem
  have h1 : twoProj N ⁅g, ⟨p, hpN⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  exact mem_pCoreOf_iff.mpr ((QuotientGroup.eq_one_iff _).mp h1)

theorem pCoreOf_twoQuot_top : pCoreOf 2 (⊤ : Subgroup (TwoQuot N)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pCoreOf 2 (⊤ : Subgroup (TwoQuot N)) with hO
  have hOn : O.Normal := ⟨fun n hn g =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 ⊤ (Subgroup.mem_top g)) n).mp hn⟩
  have h2 : IsPGroup 2 ↥(O.comap (twoProj N)) :=
    IsPGroup.comap_of_ker_isPGroup (pCoreOf_isPGroup 2 _) (twoProj N)
      (by rw [QuotientGroup.ker_mk']; exact CFSG.LieType.BorelTits.pCore_isPGroup 2)
  have hle : O.comap (twoProj N) ≤ CFSG.Open.pCore 2 ↥N := le_pCore 2 (hOn.comap _) h2
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
  exact (QuotientGroup.eq_one_iff a).mpr (hle hx)

theorem nonempty_oTwoQuot_equiv_of_surjective {X Y : Type*} [Group X] [Finite X] [Group Y]
    (ψ : X →* Y) (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ↥ψ.ker) :
    Nonempty (oTwoQuot X ≃* oTwoQuot Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Y := Finite.of_surjective ψ hψ
  let ρ : X →* oTwoQuot Y := (QuotientGroup.mk' (CFSG.Open.pCore 2 Y)).comp ψ
  have hρ : Function.Surjective ρ := (QuotientGroup.mk'_surjective _).comp hψ
  have hρker : ρ.ker = (CFSG.Open.pCore 2 Y).comap ψ := by
    ext x
    simp [ρ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hker2 : ρ.ker = CFSG.Open.pCore 2 X := by
    refine le_antisymm ?_ fun x hx => ?_
    · rw [hρker]
      exact le_pCore 2 ((CFSG.LieType.BorelTits.pCore_normal 2 (G := Y)).comap ψ)
        (IsPGroup.comap_of_ker_isPGroup (CFSG.LieType.BorelTits.pCore_isPGroup 2) ψ hker)
    · rw [hρker]
      exact map_pCore_le 2 ψ hψ ⟨x, hx, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker2.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)⟩

theorem nonempty_oTwoQuot_twoImg {L : Subgroup G} (hL : L ≤ N) :
    Nonempty (OTwoQuot (twoImg N L) ≃* OTwoQuot L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥L →* ↥(twoImg N L) :=
    ((twoProj N).comp (Subgroup.inclusion hL)).codRestrict (twoImg N L)
      (fun x => mem_twoImg.mpr ⟨Subgroup.inclusion hL x, x.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨a, haL, rfl⟩ := mem_twoImg.mp hy
    exact ⟨⟨a, haL⟩, Subtype.ext rfl⟩
  have hker : IsPGroup 2 ↥f.ker := by
    intro x
    have h1 : twoProj N (Subgroup.inclusion hL x.1) = 1 := congrArg Subtype.val x.2
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥N))
      ⟨Subgroup.inclusion hL x.1, (QuotientGroup.eq_one_iff _).mp h1⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : ↥(CFSG.Open.pCore 2 ↥N) => ((y : ↥N) : G)) hk
    simpa using this
  obtain ⟨e⟩ := nonempty_oTwoQuot_equiv_of_surjective f hf hker
  exact ⟨e.symm⟩

end CFSG.Quasithin.N204
