module

public import CFSG.RankThree.PartTwo.Sec19.Step1914TriSeitz
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.KS18L34GenProof
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
public import CFSG.RankThree.PartTwo.Sec19.Step199Proof

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL)

namespace Step1918Proof

variable {G : Type} [Group G] [Finite G]

theorem le_of_gen {K D M' : Subgroup G} (hD : CFSG.Assembly.IsElemAbelian 3 D)
    (hD9 : Nat.card D = 9) (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hCM : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set G) ≤ M')
    (hgen : Function.Injective ((Step199Proof.pCoreAct K).comp (Subgroup.inclusion hDK)) →
      Subgroup.closure {x : K ⧸ CFSG.pCore 2 K | ∃ φ ∈
        ((Step199Proof.pCoreAct K).comp (Subgroup.inclusion hDK)).range, φ ≠ 1 ∧ φ x = x} = ⊤) :
    K ≤ M' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := (Step199Proof.pCoreAct K).comp (Subgroup.inclusion hDK) with hρ
  have hD3 : IsPGroup 3 D := fun d => ⟨1, Subtype.ext (by simpa using hD.2 d d.2)⟩
  have hO3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 K) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hOeq : (CFSG.pCore 2 K).map K.subtype = CFSG.Open.pCoreOf 2 K := by
    rfl
  have hDO : D ≤ Subgroup.normalizer
      (((CFSG.pCore 2 K).map K.subtype : Subgroup G) : Set G) := by
    rw [hOeq]
    exact hDK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hOM : (CFSG.pCore 2 K).map K.subtype ≤ M' :=
    Step199Proof.le_of_centralizer_le hD hD9 hDO
      (by rwa [Subgroup.card_map_of_injective K.subtype_injective]) hCM
  refine Step199Proof.le_of_closure_fixed_eq_top hO3 hD3 hDK hDO ρ
    (fun d k k' h => Step199Proof.pCoreAct_mk _ k k' h) hOM hCM fun hinj => ?_
  rw [eq_top_iff, ← hgen hinj]
  apply Subgroup.closure_mono
  rintro x ⟨φ, ⟨d, rfl⟩, hφ1, hφx⟩
  exact ⟨d, fun h => hφ1 (by rw [h, map_one]), hφx⟩

omit [Finite G] in
theorem isElemAbelian_range {K D : Subgroup G} (hD : CFSG.Assembly.IsElemAbelian 3 D)
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.Assembly.IsElemAbelian 3
      ((Step199Proof.pCoreAct K).comp (Subgroup.inclusion hDK)).range := by
  set ρ := (Step199Proof.pCoreAct K).comp (Subgroup.inclusion hDK) with hρ
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨a, rfl⟩⟩ := x
    obtain ⟨_, ⟨b, rfl⟩⟩ := y
    apply Subtype.ext
    change ρ a * ρ b = ρ b * ρ a
    rw [← map_mul, ← map_mul]
    congr 1
    exact hD.1.is_comm.comm a b
  · rintro _ ⟨a, rfl⟩
    have : a ^ 3 = 1 := Subtype.ext (by simpa using hD.2 a a.2)
    rw [← map_pow, this, map_one]

theorem le_of_seitz (hS199 : Seitz199) (hS : SeitzL3Pi) {K D M' : Subgroup G}
    (hKp : Group.IsPerfect K) (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hCM : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set G) ≤ M')
    (htype : (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi (K ⧸ CFSG.pCore 2 K) p e ∧
        p ^ e ≠ 4) ∨
      (∃ p f : ℕ, p ≠ 3 ∧ CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ CFSG.pCore 2 K)
        .trialityD4 p f)) :
    K ≤ M' := by
  refine le_of_gen hD hD9 hDK hCM fun hinj => ?_
  set ρ := (Step199Proof.pCoreAct K).comp (Subgroup.inclusion hDK) with hρ
  have hρab := isElemAbelian_range hD hDK
  have hρcard : Nat.card ρ.range = 9 := by
    rw [← hD9]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rcases htype with ⟨p, e, hp, he, hiso, h4⟩ | ⟨p, f, hp3, hmodel⟩
  · have : Group.IsPerfect (K ⧸ CFSG.pCore 2 K) := inferInstance
    obtain ⟨-, h2⟩ := Step1914TriProof.isSimpleGroup_of_isoLThreePi he hiso
    exact hS _ p e he hiso h2 h4 ρ.range hρab hρcard
  · exact hS199 _ ρ.range hρab.2 hρcard (Or.inr ⟨p, f, hp3, hmodel⟩)

theorem le_or_inner
    {K D M' : Subgroup G} (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hCM : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set G) ≤ M')
    (htype : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 2)) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    K ≤ M' ∨
      (Function.Injective ((Step199Proof.pCoreAct K).comp (Subgroup.inclusion hDK)) ∧
        ((Step199Proof.pCoreAct K).comp (Subgroup.inclusion hDK)).range ≤
          (MulAut.conj : K ⧸ CFSG.pCore 2 K →* MulAut _).range) := by
  set ρ := (Step199Proof.pCoreAct K).comp (Subgroup.inclusion hDK) with hρ
  by_cases hexc : Function.Injective ρ ∧
      ρ.range ≤ (MulAut.conj : K ⧸ CFSG.pCore 2 K →* MulAut _).range
  · exact Or.inr hexc
  refine Or.inl (le_of_gen hD hD9 hDK hCM fun hinj => ?_)
  have hρab := isElemAbelian_range hD hDK
  have hρcard : Nat.card ρ.range = 9 := by
    rw [← hD9]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rcases htype with hL34 | hM12
  · rcases KFacts.ks18L34Gen _ hL34 ρ.range hρab hρcard with hgen | hinn
    · exact hgen
    · exact absurd ⟨hinj, hinn⟩ hexc
  · exfalso
    obtain ⟨-, -, hinn, -⟩ := KFacts.ks18M12 _ hM12
    refine hexc ⟨hinj, ?_⟩
    rintro _ ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := hinn (ρ a) ⟨1, by rw [pow_one]; exact hρab.2 _ ⟨a, rfl⟩⟩
    exact ⟨x, hx.symm⟩

end Step1918Proof

end CFSG.RankThree.PartTwo.Sec19
