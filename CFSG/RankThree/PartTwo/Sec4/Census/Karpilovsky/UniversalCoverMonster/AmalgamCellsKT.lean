module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.KernelQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Monster.Existence.Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PerfectCoreLemma

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG CFSG.Monster.Existence CFSG.Blueprint CFSG.AGLEmbedding

theorem card_center_cent_of_twoA {G : Type} [Group G] [Finite G] {a : G}
    (ha : orderOf a = 2) (h : IsTwoACentralizer a) :
    Nat.card (Subgroup.center (cent a)) = 2 := by
  obtain ⟨-, hcen, -⟩ := h
  have h1 : Nat.card ((Subgroup.center (cent a)).map (cent a).subtype) =
      Nat.card (Subgroup.center (cent a)) :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ (cent a).subtype_injective).toEquiv.symm
  rw [← h1, hcen, Nat.card_zpowers, ha]

theorem perfectCoreCell_of_perfect_quotient {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hperf : Group.IsPerfect H) (N : Subgroup H) [N.Normal] (hN : Nat.Coprime (Nat.card N) p)
    {B : Type} [Group B] (e : (↥H ⧸ N) ≃* B) (hB : KernelTrivialAt B p) :
    PerfectCoreCell p H := by
  refine ⟨H, le_rfl, fun g hg l hl => H.mul_mem (H.mul_mem hg hl) (H.inv_mem hg), hperf,
    by simp, ?_⟩
  exact kernelTrivialAt_of_quotient N hN ((kernelTrivialAt_iff_of_mulEquiv e p).2 hB)

theorem perfectCoreCell_cent_of_twoA_of_kt {G : Type} [Group G] [Finite G] {a : G}
    (ha : orderOf a = 2) (h : IsTwoACentralizer a) {p : ℕ} [hpp : Fact p.Prime] (hp2 : p ≠ 2)
    (hB : KernelTrivialAt NativeSporadic.B p) : PerfectCoreCell p (cent a) := by
  have hcard := card_center_cent_of_twoA ha h
  obtain ⟨hperf, -, ⟨e⟩⟩ := h
  have hQ : Nat.Coprime (Nat.card (Subgroup.center (cent a))) p := by
    rw [hcard]; exact (Nat.coprime_primes Nat.prime_two hpp.out).2 (Ne.symm hp2)
  have e' : ↥(cent a) ⧸ Subgroup.center ↥(cent a) ≃* NativeSporadic.B := e
  have := perfectCoreCell_of_perfect_quotient (H := cent a) (B := NativeSporadic.B) hperf (Subgroup.center (cent a)) hQ
  have := this e'
  exact this hB

theorem perfectCoreCell_of_two_quotient {G : Type} [Group G] [Finite G] {p : ℕ} [hpp : Fact p.Prime]
    (hp2 : p ≠ 2) {H : Subgroup G} (N : Subgroup H) [N.Normal] (hN : IsPGroup 2 N) {B : Type}
    [Group B] (hBp : Group.IsPerfect B) (e : (↥H ⧸ N) ≃* B) (hKT : KernelTrivialAt B p) :
    PerfectCoreCell p H := by
  have : Group.IsPerfect B := hBp
  have hQ : Group.IsPerfect (↥H ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨S, hSn, hSperf, hSN, hidx⟩ := exists_perfect_normal_sup_eq_top hp2 N hN hQ
  refine perfectCoreCell_of_normal_perfect S hSperf hidx ?_
  let ψ : S →* (↥H ⧸ N) := (QuotientGroup.mk' N).comp S.subtype
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have : x ∈ S ⊔ N := hSN ▸ Subgroup.mem_top x
    obtain ⟨s, hs, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 this
    refine ⟨⟨s, hs⟩, ?_⟩
    show ((s : ↥H) : ↥H ⧸ N) = ((s * n : ↥H) : _)
    rw [QuotientGroup.eq]
    simpa using hn
  have hker : IsPGroup 2 ψ.ker := by
    let f : ψ.ker →* N :=
      { toFun := fun x => ⟨((x : S) : ↥H), (QuotientGroup.eq_one_iff _).1 x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hN.of_injective f fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun x : N => (x : ↥H)) hab))
  have hQc : Nat.Coprime (Nat.card ψ.ker) p := by
    obtain ⟨k, hk⟩ := hker.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hpp.out).2 (Ne.symm hp2))
  let eψ := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  exact kernelTrivialAt_of_quotient ψ.ker hQc ((kernelTrivialAt_iff_of_mulEquiv (eψ.trans e) p).2 hKT)

theorem perfectCoreCell_cent_of_twoB_of_kt {G : Type} [Group G] [Finite G] {z : G}
    (h : IsTwoBCentralizer z) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hCo1 : Group.IsPerfect NativeSporadic.Co1) (hKT : KernelTrivialAt NativeSporadic.Co1 p) :
    PerfectCoreCell p (cent z) := by
  obtain ⟨-, hQcard, -, ⟨e⟩, -, -⟩ := h
  have : (pCore 2 (cent z)).Normal := pCore_normal
  exact perfectCoreCell_of_two_quotient hp2 (pCore 2 (cent z)) (IsPGroup.of_card hQcard) hCo1 e hKT

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
