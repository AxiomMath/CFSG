module

public import CFSG.RankThree.PartOne.SEITZ3.D4Assembly

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Generic

variable {G : Type*} [Group G]

theorem index_modEq_one_of_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {N : Subgroup G} (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ N) :
    N.index ≡ 1 [MOD p] := by
  have hSp : IsPGroup p ↥(S : Subgroup G) := S.isPGroup'
  have hSidx : ¬ p ∣ (S : Subgroup G).index := S.not_dvd_index
  have hSN : (S : Subgroup G) ≤ N := fun s hs => hN (Subgroup.le_normalizer hs)
  have hmod : Nat.card (G ⧸ N) ≡ Nat.card (MulAction.fixedPoints (S : Subgroup G) (G ⧸ N))
      [MOD p] := hSp.card_modEq_card_fixedPoints (G ⧸ N)
  have hfix : MulAction.fixedPoints (S : Subgroup G) (G ⧸ N) = {((1 : G) : G ⧸ N)} := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have key : ∀ s : ↥(S : Subgroup G), s • (g : G ⧸ N) = (g : G ⧸ N) ↔ g⁻¹ * (s : G)⁻¹ * g ∈ N :=
      fun s => by
        rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
        have e : ((s : G) * g)⁻¹ * g = g⁻¹ * (s : G)⁻¹ * g := by group
        rw [e]
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff, QuotientGroup.eq]
    simp only [key]
    constructor
    · intro h
      have hg : ∀ s ∈ (S : Subgroup G), g⁻¹ * s * g ∈ N := fun s hs => by
        simpa using h ⟨s⁻¹, (S : Subgroup G).inv_mem hs⟩
      obtain ⟨m, hmN, hmn⟩ := exists_mem_normalizer_of_conj_le hSN hSp hSidx hg
      have h6 := N.mul_mem (hN hmn) (N.inv_mem hmN)
      have h7 : g⁻¹ * 1 = (g * m * (m : G)⁻¹)⁻¹ := by group
      rw [h7]
      exact N.inv_mem (by simpa using h6)
    · intro hg s
      have hgN : g ∈ N := by simpa using N.inv_mem hg
      exact N.mul_mem (N.mul_mem (N.inv_mem hgN) (hSN ((S : Subgroup G).inv_mem s.2))) hgN
  have hcard : Nat.card (MulAction.fixedPoints (S : Subgroup G) (G ⧸ N)) = 1 := by
    rw [hfix]
    exact Nat.card_unique
  rw [hcard] at hmod
  exact hmod

theorem closure_cenGen_eq_top_of_normalizer [Finite G] [IsSimpleGroup G] {p e : ℕ} [Fact p.Prime]
    (M₀ S E' : Subgroup G) (φ : ↥S ≃* (Fin 2 → Multiplicative (ZMod (p ^ e))))
    (hE'S : E' ≤ S) (hE'p : ∀ x ∈ E', x ^ p = 1) (hE'c : Nat.card E' = p ^ 2)
    (hcoatom : ∀ N : Subgroup G, IsCoatom N → M₀ ≤ N → ¬ Subgroup.normalizer (S : Set G) ≤ N)
    (hgen : M₀ ≤ Subgroup.closure (cenGen E')) :
    Subgroup.closure (cenGen E') = ⊤ := by
  have hp : p.Prime := Fact.out
  have hE'ne : E' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE'c
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hE'le : E' ≤ Subgroup.closure (cenGen E') := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · exact Subgroup.subset_closure ⟨x, hx, hx1, rfl⟩
  have hbot : Subgroup.closure (cenGen E') ≠ ⊥ := fun h => hE'ne (eq_bot_iff.2 (h ▸ hE'le))
  by_contra hne
  have hNtop : Subgroup.normalizer (Subgroup.closure (cenGen E') : Set G) ≠ ⊤ := by
    intro h6
    have hnormal : (Subgroup.closure (cenGen E')).Normal := Subgroup.normalizer_eq_top_iff.1 h6
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure (cenGen E')) with h7 | h7
    · exact hbot h7
    · exact hne h7
  obtain ⟨M, hM, hleM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom _).resolve_left hNtop
  refine hcoatom M hM (hgen.trans (Subgroup.le_normalizer.trans hleM)) fun n hn => ?_
  have hnS : cj S n = S := mem_normalizer_iff_cj.1 hn
  have h1 : cj E' n ≤ S := fun x hx => by
    have : x ∈ cj S n := cj_le_cj hE'S n hx
    rwa [hnS] at this
  have h2 : cj E' n = E' :=
    plane_unique hp φ h1 hE'S (fun x hx => pow_eq_one_of_mem_cj hE'p hx) hE'p
      (by rw [card_cj]; exact hE'c) hE'c
  have h3 : Subgroup.closure (cenGen (cj E' n)) = Subgroup.closure (cenGen E') := by rw [h2]
  rw [closure_cenGen_cj] at h3
  exact hleM (mem_normalizer_iff_cj.2 h3)

end Generic

section Max

@[expose] def Max3D4CentN : Prop :=
  ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K],
    IsoLie K (.trialityD4 q) → ∀ p : ℕ, p.Prime → 5 ≤ p →
      (p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1) →
      ∀ S : Sylow p K, ∀ E : Subgroup K, E ≤ S → CFSG.IsElementaryAbelian p E →
        Nat.card E = p ^ 2 →
        ∃ x ∈ E, x ≠ 1 ∧ ∀ N : Subgroup K, IsCoatom N → Subgroup.centralizer {x} ≤ N →
          ¬ Subgroup.normalizer ((S : Subgroup K) : Set K) ≤ N

end Max

section Reduction

theorem closure_cenGen_trialityD4_phi36_eq_top_N
    (hcent : Max3D4CentN)
    {q : TauCeti.PrimePower}
    (hq : q.p = 2) {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hiso : IsoLie K (.trialityD4 q)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp36 : p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1) (E₁ : Subgroup K)
    (hE₁ : CFSG.IsElementaryAbelian p E₁) (hE₁c : Nat.card E₁ = p ^ 2) :
    Subgroup.closure (cenGen E₁) = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  obtain ⟨X, _, _, σ, hX, hσ, -, ⟨e⟩⟩ := exists_trialityD4_model hq hiso
  have hQ : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hq]
  have hshape : ∃ e', SylowShape p 2 e' K := by
    rcases hp36 with h3 | h6
    · rw [hQ] at h3
      exact ⟨_, (CFSG.RankThree.PartOne.K128.sylowShape_D4 (ℓ := 2) q.exponent_pos X hX σ hσ
        (m := 3) (by decide) hp hp5 h3).of_mulEquiv e⟩
    · rw [hQ] at h6
      exact ⟨_, (CFSG.RankThree.PartOne.K128.sylowShape_D4 (ℓ := 2) q.exponent_pos X hX σ hσ
        (m := 6) (by decide) hp hp5 h6).of_mulEquiv e⟩
  obtain ⟨e', hshape⟩ := hshape
  obtain ⟨S, hS⟩ := (IsPGroup.of_card hE₁c : IsPGroup p ↥E₁).exists_le_sylow
  obtain ⟨φ⟩ := hshape _ S.isPGroup' S.not_dvd_index
  obtain ⟨x, hxE, hx1, hcoat⟩ := hcent q hq K hiso p hp hp5 hp36 S E₁ hS hE₁ hE₁c
  refine closure_cenGen_eq_top_of_normalizer (Subgroup.centralizer {x}) (S : Subgroup K) E₁ φ hS
    hE₁p hE₁c hcoat fun k hk => ?_
  exact Subgroup.subset_closure ⟨x, hxE, hx1, (Subgroup.mem_centralizer_iff.1 hk x rfl).symm⟩

theorem exc3D4NonsplitPhi3Phi6_of_centN
    (h : Max3D4CentN) : Exc3D4NonsplitPhi3Phi6 := by
  intro q hq K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  refine closure_fixUnion_eq_top_of_inner_equiv hnab (MulEquiv.refl K) (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  exact closure_cenGen_trialityD4_phi36_eq_top_N h hq hiso hp hp5 hP E₁ hE₁ hcard₁

end Reduction

end CFSG.RankThree.PartOne.SEITZ7
