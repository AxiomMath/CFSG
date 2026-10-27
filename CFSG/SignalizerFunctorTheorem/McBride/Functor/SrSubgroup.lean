module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Bridge
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeTransitivity

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

private theorem normalizer_inf_centralizer_singleton (hA : IsMulCommutative A) {Q : Subgroup G}
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) {b : G} (hb : b ∈ A) :
    A ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  obtain ⟨hyQ, hyb⟩ := Subgroup.mem_inf.mp hy
  refine Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer_iff.mp hAQ x hx y hyQ, ?_⟩
  have hbx : Commute b x := comm_of_mem_of_isMulCommutative hA hb hx
  have hby : Commute b y := Subgroup.mem_centralizer_iff.mp hyb b rfl
  exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]
    exact (hbx.mul_right hby).mul_right hbx.inv_right

@[expose] def signalizersOfPrime (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G)
    (P : Subgroup G → Prop) (r : ℕ) : Set (Subgroup G) :=
  {X | X ∈ signalizers p A θ P ∧ IsPGroup r X}

@[expose] def IsSrSubgroup (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G)
    (P : Subgroup G → Prop) (r : ℕ) (S : Subgroup G) : Prop :=
  Maximal (· ∈ signalizersOfPrime p A θ P r) S

@[expose] def IsSrSubgroupOf (A : Subgroup G) (r : ℕ) (U S : Subgroup G) : Prop :=
  Maximal (fun Q : Subgroup G => A ≤ Subgroup.normalizer (Q : Set G) ∧ IsPGroup r Q ∧ Q ≤ U) S

private theorem mem_signalizersOfPrime_iff [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hθ : IsFunctor p A θ) {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) {P : Subgroup G → Prop}
    (hPr : ∀ X : Subgroup G, IsPGroup r X → P X) {X : Subgroup G} :
    X ∈ signalizersOfPrime p A θ P r ↔
      CFSG.SignalizerFunctor.Helpers.signalizerPrimeCompatible p 1 r A (thetaOf θ) X := by
  constructor
  · rintro ⟨hX, hXr⟩
    exact ⟨((mem_signalizers_iff_signalizerCompatible hp hA hθ).mp hX).1, hXr⟩
  · rintro ⟨hc, hXr⟩
    refine ⟨(mem_signalizers_iff_signalizerCompatible hp hA hθ).mpr ⟨hc, ?_, hPr X hXr⟩, hXr⟩
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨n, hn⟩ := hXr.exists_card_eq
    rw [hn]
    exact ((Nat.coprime_primes hp hr).mpr hrp.symm).pow_right n

theorem isSrSubgroup_of_forall_isSrSubgroupOf [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    {r : ℕ} {P : Subgroup G → Prop} {S : Subgroup G} (hS : S ∈ signalizersOfPrime p A θ P r)
    {B : Subgroup G} (hBA : B ≤ A) (hB : p ^ 2 ≤ Nat.card B)
    (h : ∀ b ∈ B, b ≠ 1 → IsSrSubgroupOf A r (θ b) (S ⊓ Subgroup.centralizer {b})) :
    IsSrSubgroup p A θ P r S := by
  have hBe : IsElemAbelian p B :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hBA
  refine ⟨hS, fun Q hQ hSQ => ?_⟩
  calc Q = ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), Q ⊓ Subgroup.centralizer {b} :=
        (iSup_inf_centralizer hp hBe hB (hBA.trans hQ.1.1) hQ.1.2.1).symm
    _ ≤ S := by
      refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
      have hmax := h b hb hb1
      have := hmax.2 (y := Q ⊓ Subgroup.centralizer {b})
        ⟨normalizer_inf_centralizer_singleton hA.1 hQ.1.1 (hBA hb), hQ.2.to_le inf_le_left,
          hQ.1.2.2.1 b (hBA hb) hb1⟩ (inf_le_inf_right _ hSQ)
      exact this.trans inf_le_left

theorem IsSrSubgroup.isSrSubgroupOf_inf_centralizer [Finite G] (hp : p.Prime)
    (hA : IsElemAbelian p A) (hrank : p ^ 3 ≤ Nat.card A) (hθ : IsFunctor p A θ) {r : ℕ}
    (hr : r.Prime) (hrp : r ≠ p) {P : Subgroup G → Prop}
    (hPr : ∀ X : Subgroup G, IsPGroup r X → P X) {S : Subgroup G}
    (hS : IsSrSubgroup p A θ P r S) {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) :
    IsSrSubgroupOf A r (θ b) (S ⊓ Subgroup.centralizer {b}) := by
  open CFSG.SignalizerFunctor.Helpers in
  have hΘ := hθ.isSignalizerFunctor_thetaOf hp hA
  have hrank' : p ^ (1 + 2) ≤ Nat.card A := hrank
  have hset : (fun X : Subgroup G => X ∈ signalizersOfPrime p A θ P r) =
      signalizerPrimeCompatible p 1 r A (thetaOf θ) :=
    funext fun X => propext (mem_signalizersOfPrime_iff hp hA hθ hr hrp hPr)
  have hSmax : Maximal (signalizerPrimeCompatible p 1 r A (thetaOf θ)) S := by
    rw [← hset]
    exact hS
  have hSmem : S ∈ signalizersOfPrime p A θ P r := hS.1
  have hbS : S ⊓ Subgroup.centralizer {b} ≤ θ b := hSmem.1.2.2.1 b hb hb1
  refine ⟨⟨normalizer_inf_centralizer_singleton hA.1 hSmem.1.1 hb,
    hSmem.2.to_le inf_le_left, hbS⟩, fun Q hQ hSQ => ?_⟩
  have hQb : Q ≤ θ b := hQ.2.2
  have hQc : signalizerPrimeCompatible p 1 r A (thetaOf θ) Q := by
    refine ⟨(signalizerCompatible_thetaOf_iff hp hA hθ).mpr ⟨hQ.1, fun a ha ha1 => ?_⟩, hQ.2.1⟩
    exact (inf_le_inf_right _ hQb).trans (hθ.balance b hb hb1 a ha ha1)
  obtain ⟨P', hQP', hP'max⟩ := Finite.exists_le_maximal (p := signalizerPrimeCompatible p 1 r A
    (thetaOf θ)) hQc
  obtain ⟨g, hg⟩ := signalizer_prime_transitivity p 1 r hp hr hrp.symm A hA hrank' (thetaOf θ)
    hΘ.coprime hΘ.normalized hΘ.balanced P' S hP'max hSmax
  have hgA : g.1 ∈ Subgroup.centralizer (A : Set G) := g.2.1
  have hbg : Commute b g.1 := Subgroup.mem_centralizer_iff.mp hgA b hb
  have hle1 : Q.map (MulAut.conj g.1).toMonoidHom ≤ S ⊓ Subgroup.centralizer {b} := by
    have hP'S : P'.map (MulAut.conj g.1).toMonoidHom = S := hg
    refine le_inf ?_ ?_
    · rw [← hP'S]
      exact Subgroup.map_mono hQP'
    · rintro _ ⟨x, hx, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff.mp hh]
      have hbx : Commute b x :=
        Subgroup.mem_centralizer_iff.mp (hθ.le_centralizer b hb hb1 (hQb hx)) b rfl
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
      exact (hbg.mul_right hbx).mul_right hbg.inv_right
  have hcard : Nat.card (Q.map (MulAut.conj g.1).toMonoidHom) = Nat.card Q :=
    Subgroup.card_map_of_injective (MulAut.conj g.1).injective
  have h1 : Nat.card Q ≤ Nat.card (S ⊓ Subgroup.centralizer {b} : Subgroup G) :=
    hcard ▸ Subgroup.card_le_of_le hle1
  exact (Subgroup.eq_of_le_of_card_ge hSQ h1).ge

theorem isSrSubgroup_iff [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hrank : p ^ 3 ≤ Nat.card A) (hθ : IsFunctor p A θ) {r : ℕ} (hr : r.Prime) (hrp : r ≠ p)
    {P : Subgroup G → Prop} (hPr : ∀ X : Subgroup G, IsPGroup r X → P X) {S : Subgroup G}
    (hS : S ∈ signalizersOfPrime p A θ P r) {B : Subgroup G} (hBA : B ≤ A)
    (hB : p ^ 2 ≤ Nat.card B) :
    IsSrSubgroup p A θ P r S ↔
      ∀ b ∈ B, b ≠ 1 → IsSrSubgroupOf A r (θ b) (S ⊓ Subgroup.centralizer {b}) :=
  ⟨fun h _ hb hb1 =>
    h.isSrSubgroupOf_inf_centralizer hp hA hrank hθ hr hrp hPr (hBA hb) hb1,
    isSrSubgroup_of_forall_isSrSubgroupOf hp hA hS hBA hB⟩

theorem two_le_rank_of_not_isCyclic [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    {B : Subgroup G} (hBA : B ≤ A) (hB : ¬ IsCyclic B) : p ^ 2 ≤ Nat.card B := by
  have : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p B
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hBA)
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · exfalso
    interval_cases n
    · have : Subsingleton B := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
      exact hB isCyclic_of_subsingleton
    · exact hB (isCyclic_of_prime_card (p := p) (by simpa using hn))
  · rw [hn]
    exact Nat.pow_le_pow_right hp.pos hn2

end CFSG.SignalizerFunctorTheorem.McBride
