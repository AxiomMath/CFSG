module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ShapeFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Sub
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixSeven
import CFSG.LocalAnalysis.UniquenessCase.UC6K36Rank
import CFSG.LocalAnalysis.UniquenessCase.UC6K36Comp
import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise MatrixGroups
open CFSG.ASVolI.ChIJK (F4)

variable {G : Type} [Group G] [Finite G]

theorem eq_one_or_eq_of_mem_zpowers {t x : G} (ht : orderOf t = 2) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨n, hn⟩ := hx
  have hn' : t ^ n = x := hn
  have h1 : t ^ (n % (orderOf t : ℤ)) = t ^ n := zpow_mod_orderOf t n
  rw [ht] at h1
  have h2 : (((2 : ℕ) : ℤ)) = 2 := rfl
  rw [h2] at h1
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [← hn', ← h1, h]
    simp
  · right
    rw [← hn', ← h1, h]
    simp

theorem eq_of_zpowers_eq_of_orderOf_two {t t' : G} (ht : orderOf t = 2) (ht' : orderOf t' = 2)
    (h : zpowers t = zpowers t') : t = t' := by
  have h1 : t ∈ zpowers t' := h ▸ mem_zpowers t
  rcases eq_one_or_eq_of_mem_zpowers ht' h1 with h2 | h2
  · rw [h2, orderOf_one] at ht
    omega
  · exact h2

theorem eq_zpowers_of_le_zpowers {t : G} (ht : orderOf t = 2) {Q : Subgroup G} (hQ : Q ≠ ⊥)
    (hle : Q ≤ zpowers t) : Q = zpowers t := by
  obtain ⟨q, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hQ
  have hqG : (q : G) ≠ 1 := fun h => hq1 (Subtype.ext h)
  rcases eq_one_or_eq_of_mem_zpowers ht (hle q.2) with h | h
  · exact absurd h hqG
  · refine le_antisymm hle ?_
    rw [Subgroup.zpowers_le]
    rw [← h]
    exact q.2

theorem false_of_commutative_perfect {H : Subgroup G} (hP : Group.IsPerfect H) [Nontrivial H]
    (hc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : False := by
  haveI : Group.IsPerfect H := hP
  haveI : IsMulCommutative H := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
  haveI : Subsingleton H := inferInstance
  exact (not_subsingleton H) inferInstance

theorem false_of_isQuasisimple_sup {K L₁ L₂ : Subgroup G} (hq : CFSG.IsQuasisimple K) (hsup : K = L₁ ⊔ L₂)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h₁ : Group.IsPerfect L₁) (h₂ : Group.IsPerfect L₂)
    [Nontrivial L₁] [Nontrivial L₂] : False := by
  have hL₁K : L₁ ≤ K := hsup ▸ le_sup_left
  have hL₂K : L₂ ≤ K := hsup ▸ le_sup_right
  have hL₂N : L₂ ≤ normalizer (L₁ : Set G) := by
    intro x hx
    refine mem_normalizer_of_map_conj_eq ?_
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : (MulAut.conj x).toMonoidHom y = y := by
        show x * y * x⁻¹ = y
        calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [← hcomm y hy x hx]
          _ = y := by group
      rw [this]
      exact hy
    · intro hz
      refine ⟨z, hz, ?_⟩
      show x * z * x⁻¹ = z
      calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [← hcomm z hz x hx]
        _ = z := by group
  have hN : (L₁.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hL₁K, hsup]
    exact sup_le Subgroup.le_normalizer hL₂N
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with htop | hcen
  · have hKL₁ : K ≤ L₁ := Subgroup.subgroupOf_eq_top.1 htop
    exact false_of_commutative_perfect h₂ fun a ha b hb => hcomm a (hKL₁ (hL₂K ha)) b hb
  · refine false_of_commutative_perfect h₁ fun a ha b hb => ?_
    have := Subgroup.mem_center_iff.1 (hcen (show (⟨a, hL₁K ha⟩ : K) ∈ L₁.subgroupOf K from ha))
      ⟨b, hL₁K hb⟩
    exact (congrArg Subtype.val this).symm

theorem false_of_component_le_centralizer {K Λ : Subgroup G} (hK : CFSG.IsComponent K) (hKΛ : K ≤ Λ)
    (hKC : K ≤ centralizer (Λ : Set G)) : False := by
  haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  exact false_of_commutative_perfect hK.1.1 fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (hKC ha) b (hKΛ hb)).symm

theorem Rank2Good.exists_le_sylow {K : Subgroup G} (hK : CFSG.IsComponent K) (hg : Rank2Good K)
    (P : Sylow 3 G) :
    ∃ A : Subgroup G, A ≤ K ∧ A ≤ (P : Subgroup G) ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨A, hAK, hAe, hAc⟩, -⟩ := hg
  obtain ⟨k, hk, hkA⟩ := exists_conj_le_sylow_of_isSubnormal P hK.2 hAK hAe.isPGroup
  refine ⟨A.map (MulAut.conj k).toMonoidHom, ?_, ?_, hAe.map _, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact K.mul_mem (K.mul_mem hk (hAK ha)) (K.inv_mem hk)
  · rintro _ ⟨a, ha, rfl⟩
    exact hkA a ha
  · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hAc]

theorem mem_sup_centralizer_of_forall {Λ : Subgroup G} {S : Set (Subgroup G)} (hΛ : Λ = sSup S) {e g : G}
    (hg : g ∈ Λ) (h : ∀ K ∈ S, ∀ y ∈ K, e * y * e⁻¹ = g * y * g⁻¹) :
    e ∈ Λ ⊔ centralizer (Λ : Set G) := by
  have hle : Λ ≤ centralizer ({g⁻¹ * e} : Set G) := by
    rw [hΛ]
    refine sSup_le fun K hK y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := h K hK y hy
    calc y * (g⁻¹ * e) = g⁻¹ * (g * y * g⁻¹) * e := by group
      _ = g⁻¹ * (e * y * e⁻¹) * e := by rw [h1]
      _ = (g⁻¹ * e) * y := by group
  have hc : g⁻¹ * e ∈ centralizer (Λ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  have : e = g * (g⁻¹ * e) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hg hc

structure Oracle36 (M E : Subgroup G) (p : ℕ) : Prop where
  conclIn : ∀ X : Subgroup G, X ≠ ⊤ → E ≤ X → ¬ X ≤ M → pCoreOf 2 (X ⊓ M) ≠ ⊥ →
    PartTwo.Star36 ↥X → K36ConclIn X M p
  star_comp : ∀ K : Subgroup G, CFSG.IsComponent K → ⁅K, pCoreOf 2 M⁆ ≠ ⊥ →
    PartTwo.Star36 ↥(E ⊔ pCoreOf 2 M ⊔ K)
  star_cent : ∀ Λ : Subgroup G, Λ.Normal →
    PartTwo.Star36 ↥(E ⊔ pCoreOf 2 M ⊔ centralizer (Λ : Set G)) ∨ centralizer (Λ : Set G) ≤ M

namespace Hyp36

variable {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem mul_comm_of_pCoreOf_eq {t : G} (ht : orderOf t = 2) (hQ : pCoreOf 2 M = zpowers t) {m : G}
    (hm : m ∈ M) : m * t * m⁻¹ = t := by
  have hn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm
  have htQ : t ∈ pCoreOf 2 M := hQ ▸ mem_zpowers t
  have h1 : m * t * m⁻¹ ∈ pCoreOf 2 M := (Subgroup.mem_normalizer_iff.1 hn t).1 htQ
  rw [hQ] at h1
  rcases eq_one_or_eq_of_mem_zpowers ht h1 with h2 | h2
  · have h3 : t = 1 := by
      calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
        _ = 1 := by rw [h2]; group
    rw [h3, orderOf_one] at ht
    omega
  · exact h2

theorem pCoreOf_le_pCoreOf_inf {X : Subgroup G} (hQX : pCoreOf 2 M ≤ X) :
    pCoreOf 2 M ≤ pCoreOf 2 (X ⊓ M) := by
  have hQXM : pCoreOf 2 M ≤ X ⊓ M := le_inf hQX (CFSG.openPCoreOf_le 2 M)
  have hQnorm : ((pCoreOf 2 M).subgroupOf (X ⊓ M)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQXM]
    exact inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  exact le_pCoreOf_of_normal hQXM hQnorm (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)

theorem perfect_le_of_le_sup_sup {N P : Subgroup G} (hP : Group.IsPerfect P)
    (hEN : E ≤ normalizer (N : Set G)) (hQN : pCoreOf 2 M ≤ normalizer (N : Set G))
    (hPX : P ≤ E ⊔ pCoreOf 2 M ⊔ N) : P ≤ N := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hsolvE : Group.IsSolvable ↥E := by
    haveI := h.isPGroup.isNilpotent
    infer_instance
  have hsolvQ : Group.IsSolvable ↥(pCoreOf 2 M) := by
    haveI := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).isNilpotent
    infer_instance
  have hEQN : E ≤ normalizer ((pCoreOf 2 M ⊔ N : Subgroup G) : Set G) := by
    intro e he'
    have hsup : pCoreOf 2 M ⊔ N = sSup {pCoreOf 2 M, N} := (sSup_pair).symm
    rw [hsup]
    refine mem_normalizer_sSup (fun A hA => ?_)
    rcases hA with rfl | rfl
    · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (h.E_le he')
    · exact hEN he'
  have h1 : P ≤ pCoreOf 2 M ⊔ N :=
    perfect_le_of_le_sup_of_isSolvable hP hsolvE hEQN (hPX.trans (sup_assoc E (pCoreOf 2 M) N).le)
  exact perfect_le_of_le_sup_of_isSolvable hP hsolvQ hQN h1

theorem shapeComp_of_component (O : Oracle36 M E p) {K : Subgroup G}
    (hKc : CFSG.IsComponent K) (hne : ⁅K, pCoreOf 2 M⁆ ≠ ⊥) (hX : E ⊔ pCoreOf 2 M ⊔ K ≠ ⊤) :
    p = 3 ∧ ∃ t : G, orderOf t = 2 ∧ pCoreOf 2 M = zpowers t ∧ ShapeComp t K := by
  set Q := pCoreOf 2 M with hQdef
  set X := E ⊔ Q ⊔ K with hXdef
  obtain ⟨hEN, hQN⟩ := h.normalizes_component hKc hne
  have hEX : E ≤ X := le_sup_of_le_left le_sup_left
  have hQX : Q ≤ X := le_sup_of_le_left le_sup_right
  have hKX : K ≤ X := le_sup_right
  have hXM : ¬ X ≤ M := fun hle => h.false_of_component_le hKc hne (hKX.trans hle)
  have hQle : Q ≤ pCoreOf 2 (X ⊓ M) := h.pCoreOf_le_pCoreOf_inf hQX
  have hQX' : pCoreOf 2 (X ⊓ M) ≠ ⊥ := fun hb => h.pCore_ne_bot (le_bot_iff.1 (hb ▸ hQle))
  obtain ⟨hp3, t, ht2, hpc, L', hL'X, hL'n, hXeq, hshape⟩ :=
    O.conclIn X hX hEX hXM hQX' (O.star_comp K hKc hne)
  have hQeq : Q = zpowers t := eq_zpowers_of_le_zpowers ht2 h.pCore_ne_bot (hQle.trans hpc.le)
  have htQ : t ∈ Q := hQeq ▸ mem_zpowers t
  have hXN : X ≤ normalizer (L' : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL'X).1 hL'n
  have hKXc : CFSG.IsComponent (K.subgroupOf X) := CFSG.LocalCores.component_overgroup hKc hKX
  have hKL' : K ≤ L' := by
    rcases CFSG.LocalCores.component_normal_subgroup hKXc hL'n with hle | hcomm
    · exact CFSG.LocalCores.le_of_subgroupOf_le hKX hle
    · exfalso
      have hc : ⁅K, L' ⊓ X⁆ = ⊥ := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hKX hcomm
      rw [inf_eq_left.2 hL'X] at hc
      have hKcent : K ≤ centralizer (L' : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
      have hcent := eq_of_forall_mul_mem_center hKc.1.1 (hQN htQ) (fun k hk y hy => by
        have hkX : k ∈ X ⊓ M ⊔ L' := hXeq ▸ hKX hk
        have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (X ⊓ M) L'
          (inf_le_left.trans hXN)
        have hk' : k ∈ ((X ⊓ M : Subgroup G) : Set G) * (L' : Set G) := by
          rw [← hmul]
          exact hkX
        obtain ⟨m, hm, l, hl, rfl⟩ := Set.mem_mul.1 hk'
        have hmM : m ∈ M := (Subgroup.mem_inf.1 hm).2
        have htm : m * t = t * m := by
          calc m * t = (m * t * m⁻¹) * m := by group
            _ = t * m := by rw [h.mul_comm_of_pCoreOf_eq ht2 hQeq hmM]
        have hcL' : (m * l)⁻¹ * (t * (m * l) * t⁻¹) ∈ L' := by
          have e1 : (m * l)⁻¹ * (t * (m * l) * t⁻¹) = l⁻¹ * (t * l * t⁻¹) := by
            calc (m * l)⁻¹ * (t * (m * l) * t⁻¹) = l⁻¹ * (m⁻¹ * (t * m)) * l * t⁻¹ := by group
              _ = l⁻¹ * (m⁻¹ * (m * t)) * l * t⁻¹ := by rw [htm]
              _ = l⁻¹ * (t * l * t⁻¹) := by group
          rw [e1]
          exact L'.mul_mem (L'.inv_mem hl) ((Subgroup.mem_normalizer_iff.1 (hXN (hQX htQ)) l).1 hl)
        exact Subgroup.mem_centralizer_iff.1 (hKcent hy) _ hcL')
      apply hne
      rw [hQeq]
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun k hk => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨n, hn⟩ := hq
      have hn' : t ^ n = q := hn
      have hcomm' : Commute t k := by
        have := hcent k hk
        show t * k = k * t
        calc t * k = (t * k * t⁻¹) * t := by group
          _ = k * t := by rw [this]
      rw [← hn']
      exact (hcomm'.zpow_left n).eq
  have hperf : Group.IsPerfect L' := shape_isPerfect hshape
  have hL'K : L' ≤ K := h.perfect_le_of_le_sup_sup hperf hEN hQN hL'X
  have hKeq : L' = K := le_antisymm hL'K hKL'
  rw [hKeq] at hshape
  refine ⟨hp3, t, ht2, hQeq, ?_⟩
  rcases hshape with hgf | hA
  · rcases hgf with hgf | ⟨L₁, L₂, hsup, hcomm, ⟨e₁⟩, ⟨e₂⟩, -, -, -⟩
    · exact Or.inl hgf
    · exfalso
      haveI : Nontrivial SL(3, F4) := CFSG.LocalCores.isQuasisimple_nontrivial sl3F4_isQuasisimple
      haveI : Nontrivial ↥L₁ := e₁.symm.injective.nontrivial (α := SL(3, F4))
      haveI : Nontrivial ↥L₂ := e₂.symm.injective.nontrivial (α := SL(3, F4))
      haveI := sl3F4_isPerfect
      exact false_of_isQuasisimple_sup hKc.1 hsup hcomm
        (Group.IsPerfect.ofSurjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective)
        (Group.IsPerfect.ofSurjective (f := e₂.symm.toMonoidHom) e₂.symm.surjective)
  · exact Or.inr hA

theorem sup_eq_top_of_normal {D : Subgroup G} [D.Normal] (hED : E ≤ D) : D ⊔ M = ⊤ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨R, hER⟩ := (h.isPGroup.comap_subtype (K := D)).exists_le_sylow
  set R' : Subgroup G := (R : Subgroup D).map D.subtype with hR'
  have hER' : E ≤ R' := by
    intro x hx
    exact ⟨⟨x, hED hx⟩, hER (show (⟨x, hED hx⟩ : D) ∈ E.subgroupOf D from hx), rfl⟩
  have hR'p : IsPGroup p R' := R.isPGroup'.map _
  have hR'M : R' ≤ M := h.le_of_isPGroup hR'p hER'
  have hNM : normalizer (R' : Set G) ≤ M := h.normalizer_le_of_le hER' hR'M
  have hfr := Sylow.normalizer_sup_eq_top R
  refine top_le_iff.1 ?_
  rw [← hfr]
  exact sup_le_sup_right hNM D |>.trans (by rw [sup_comm])

theorem false_of_elemAbelian_four (he3 : twoLocalPrimeRank 3 G ≤ 3) {B : Subgroup G} (hBM : B ≤ M)
    (hB : IsElemAbelian 3 B) (hcard : 3 ^ 4 ≤ Nat.card B) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h4 := four_le_pRank_of_elemAbelian hBM hB hcard
  have := (pRank_le_twoLocalPrimeRank (G := G) Nat.prime_three h.maxTwoLocal.1).trans he3
  omega

theorem exists_sylow_three (hp3 : p = 3) : ∃ P : Sylow 3 G, E ≤ (P : Subgroup G) ∧ (P : Subgroup G) ≤ M := by
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow h.isPGroup
  exact ⟨P, hEP, h.le_of_isPGroup P.isPGroup' hEP⟩

theorem false_of_three (hp3 : p = 3) (he3 : twoLocalPrimeRank 3 G ≤ 3) {K₀ K₁ K₂ : Subgroup G}
    (h₀ : CFSG.IsComponent K₀) (h₁ : CFSG.IsComponent K₁) (h₂ : CFSG.IsComponent K₂)
    (hne01 : K₀ ≠ K₁) (hne02 : K₀ ≠ K₂) (hne12 : K₁ ≠ K₂) (g₀ : Rank2Good K₀) (g₁ : Rank2Good K₁)
    (g₂ : Rank2Good K₂) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, -, hPM⟩ := h.exists_sylow_three hp3
  obtain ⟨A₀, hA₀K, hA₀P, hA₀e, hA₀c⟩ := g₀.exists_le_sylow h₀ P
  obtain ⟨A₁, hA₁K, hA₁P, hA₁e, hA₁c⟩ := g₁.exists_le_sylow h₁ P
  obtain ⟨A₂, hA₂K, hA₂P, hA₂e, hA₂c⟩ := g₂.exists_le_sylow h₂ P
  have hcomm : ∀ {X Y : Subgroup G}, CFSG.IsComponent X → CFSG.IsComponent Y → X ≠ Y →
      ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
    intro X Y hX hY hXY x hx y hy
    have hc : ⁅X, Y⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hX hY).resolve_left hXY
    have hXc : X ≤ centralizer (Y : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
    exact (Subgroup.mem_centralizer_iff.1 (hXc hx) y hy).symm
  obtain ⟨hB, hBcard⟩ := exists_elemAbelian_of_three_commuting (p := 3)
    (hcomm h₀ h₁ hne01) (hcomm h₀ h₂ hne02) (hcomm h₁ h₂ hne12) hA₀K hA₁K hA₂K hA₀e hA₁e hA₂e
    hA₀c hA₁c hA₂c g₀.2 g₂.2
  exact h.false_of_elemAbelian_four he3
    (sup_le (sup_le (hA₀P.trans hPM) (hA₁P.trans hPM)) (hA₂P.trans hPM)) hB hBcard

theorem inf_ne_bot_of_two (hp3 : p = 3) (he3 : twoLocalPrimeRank 3 G ≤ 3) {K₀ K₁ : Subgroup G}
    (h₀ : CFSG.IsComponent K₀) (h₁ : CFSG.IsComponent K₁) (hne : K₀ ≠ K₁) (g₀ : Rank2Good K₀)
    (g₁ : Rank2Good K₁) : K₀ ⊓ K₁ ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hinf
  obtain ⟨P, -, hPM⟩ := h.exists_sylow_three hp3
  obtain ⟨A₀, hA₀K, hA₀P, hA₀e, hA₀c⟩ := g₀.exists_le_sylow h₀ P
  obtain ⟨A₁, hA₁K, hA₁P, hA₁e, hA₁c⟩ := g₁.exists_le_sylow h₁ P
  have hc : ⁅K₀, K₁⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute h₀ h₁).resolve_left hne
  have hK : K₀ ≤ centralizer (K₁ : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
  obtain ⟨hB, hBcard⟩ := exists_elemAbelian_of_two_commuting (p := 3)
    (fun x hx y hy => (Subgroup.mem_centralizer_iff.1 (hK hx) y hy).symm) hinf hA₀K hA₁K hA₀e hA₁e
    hA₀c hA₁c
  exact h.false_of_elemAbelian_four he3 (sup_le (hA₀P.trans hPM) (hA₁P.trans hPM)) hB hBcard.ge

theorem normalizer_lam36_eq_top_of_rank (hp3 : p = 3) (he3 : twoLocalPrimeRank 3 G ≤ 3)
    (hg : ∀ K ∈ comps36 M, Rank2Good K) : normalizer (lam36 M : Set G) = ⊤ := by
  refine h.normalizer_lam36_eq_top (fun g K hK => ?_)
  have hpK : p ∣ Nat.card K := h.dvd_card_component hK.1 hK.2
  have hK' : CFSG.IsComponent (K.map (MulAut.conj g).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv _ hK.1
  have hpK' : p ∣ Nat.card (K.map (MulAut.conj g).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact h.normalizes_of_rank hp3 he3 hK' hpK' ((hg K hK).conj g)

theorem centralizer_lam36_le (O : Oracle36 M E p) (hΛ : (lam36 M).Normal) :
    centralizer (lam36 M : Set G) ≤ M := by
  haveI := hΛ
  set Λ := lam36 M with hΛdef
  set C : Subgroup G := centralizer (Λ : Set G) with hCdef
  haveI hCn : C.Normal := Subgroup.normal_centralizer (H := Λ)
  have hCnorm : normalizer (C : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.2 hCn
  set Q := pCoreOf 2 M with hQdef
  have hEC : E ≤ normalizer (C : Set G) := by rw [hCnorm]; exact le_top
  have hQC : Q ≤ normalizer (C : Set G) := by rw [hCnorm]; exact le_top
  by_contra hCM
  obtain hstar | hle := O.star_cent Λ hΛ
  swap
  · exact hCM hle
  obtain ⟨K0, hK0c, hK0ne⟩ := h.exists_component
  have hK0mem : K0 ∈ comps36 M := ⟨hK0c, hK0ne⟩
  have hK0Λ : K0 ≤ Λ := le_sSup hK0mem
  set X : Subgroup G := E ⊔ Q ⊔ C with hXdef
  have hXtop : X ≠ ⊤ := by
    intro hXt
    have hXt' : E ⊔ Q ⊔ C = ⊤ := hXt
    have hK0C : K0 ≤ C := h.perfect_le_of_le_sup_sup hK0c.1.1 hEC hQC (by rw [hXt']; exact le_top)
    exact false_of_component_le_centralizer hK0c hK0Λ hK0C
  have hEX : E ≤ X := le_sup_of_le_left le_sup_left
  have hCX : C ≤ X := le_sup_right
  have hQX : Q ≤ X := le_sup_of_le_left le_sup_right
  have hXM : ¬ X ≤ M := fun hle => hCM (hCX.trans hle)
  have hQle : Q ≤ pCoreOf 2 (X ⊓ M) := h.pCoreOf_le_pCoreOf_inf hQX
  have hQX' : pCoreOf 2 (X ⊓ M) ≠ ⊥ := fun hb => h.pCore_ne_bot (le_bot_iff.1 (hb ▸ hQle))
  obtain ⟨-, t, ht2, hpc, -⟩ := O.conclIn X hXtop hEX hXM hQX' hstar
  have hQeq : Q = pCoreOf 2 (X ⊓ M) := by
    rw [hpc]
    exact eq_zpowers_of_le_zpowers ht2 h.pCore_ne_bot (hQle.trans hpc.le)
  obtain ⟨Lt, hLtc, hLtne⟩ := (h.subgroupOf hEX hXM hQX').exists_component
  set L : Subgroup G := Lt.map X.subtype with hLdef
  have hLX : L ≤ X := Subgroup.map_subtype_le Lt
  have hLq : CFSG.IsQuasisimple L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Lt.equivMapOfInjective X.subtype X.subtype_injective) hLtc.1
  have hLC : L ≤ C := h.perfect_le_of_le_sup_sup hLq.1 hEC hQC hLX
  have hLsub : L.IsSubnormal := by
    have hcomap : L.subgroupOf C = Lt.comap (Subgroup.inclusion hCX) := by
      ext c
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hLdef, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyc⟩
        have : y = Subgroup.inclusion hCX c := Subtype.ext (by simpa using hyc)
        rw [← this]
        exact hy
      · intro hc
        exact ⟨_, hc, rfl⟩
    have h1 : (L.subgroupOf C).IsSubnormal := hcomap ▸ hLtc.2.comap _
    exact Subgroup.IsSubnormal.trans hLC h1 hCn.isSubnormal
  have hLne : ⁅L, Q⁆ ≠ ⊥ := by
    intro hb
    apply hLtne
    have hmap_eq : (M.subgroupOf X).map X.subtype = X ⊓ M := by
      rw [Subgroup.subgroupOf_map_subtype, inf_comm]
    have hQmap : (pCoreOf 2 (M.subgroupOf X)).map X.subtype = Q := by
      rw [pCoreOf_map_subtype', hmap_eq, hQeq]
    rw [← hQmap, ← Subgroup.map_commutator] at hb
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hb
  have hLmem : L ∈ comps36 M := ⟨⟨hLq, hLsub⟩, hLne⟩
  exact false_of_component_le_centralizer ⟨hLq, hLsub⟩ (le_sSup hLmem) hLC

theorem comps36_eq_singleton_or_pair (hp3 : p = 3) (he3 : twoLocalPrimeRank 3 G ≤ 3) {t : G}
    (hshape : ∀ K ∈ comps36 M, ShapeComp t K) {K₀ : Subgroup G} (hK₀ : K₀ ∈ comps36 M) :
    comps36 M = {K₀} ∨ ∃ K₁ : Subgroup G, K₁ ∈ comps36 M ∧ K₁ ≠ K₀ ∧ comps36 M = {K₀, K₁} ∧
      Nonempty (↥K₀ ≃* SL(3, F4)) ∧ Nonempty (↥K₁ ≃* SL(3, F4)) ∧
      K₀ ⊓ K₁ = (center ↥K₀).map K₀.subtype ∧ UC6.InducesGraphField t K₀ ∧ UC6.InducesGraphField t K₁ := by
  by_cases hone : ∀ K ∈ comps36 M, K = K₀
  · exact Or.inl (Set.eq_singleton_iff_unique_mem.2 ⟨hK₀, hone⟩)
  right
  push Not at hone
  obtain ⟨K₁, hK₁, hne⟩ := hone
  have hg : ∀ K ∈ comps36 M, Rank2Good K := fun K hK => (hshape K hK).rank2Good
  have hpair : comps36 M = {K₀, K₁} := by
    ext K
    constructor
    · intro hK
      by_contra hK'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hK'
      exact h.false_of_three hp3 he3 hK₀.1 hK₁.1 hK.1 hne.symm (Ne.symm hK'.1) (Ne.symm hK'.2)
        (hg _ hK₀) (hg _ hK₁) (hg _ hK)
    · rintro (rfl | rfl)
      · exact hK₀
      · exact hK₁
  have hinf := h.inf_ne_bot_of_two hp3 he3 hK₀.1 hK₁.1 hne.symm (hg _ hK₀) (hg _ hK₁)
  have hcomm : ⁅K₀, K₁⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hK₀.1 hK₁.1).resolve_left hne.symm
  have hK : K₀ ≤ centralizer (K₁ : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hK' : K₁ ≤ centralizer (K₀ : Set G) := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.1 ?_
    rw [Subgroup.commutator_comm]
    exact hcomm
  have hle0 : K₀ ⊓ K₁ ≤ (center ↥K₀).map K₀.subtype := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := Subgroup.mem_inf.1 hx
    exact ⟨⟨x, hx0⟩, Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hK g.2) x hx1).symm), rfl⟩
  have hle1 : K₀ ⊓ K₁ ≤ (center ↥K₁).map K₁.subtype := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := Subgroup.mem_inf.1 hx
    exact ⟨⟨x, hx1⟩, Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hK' g.2) x hx0).symm), rfl⟩
  have hZ₀ : center ↥K₀ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.map_bot] at hle0
    exact hinf (le_bot_iff.1 hle0)
  have hZ₁ : center ↥K₁ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.map_bot] at hle1
    exact hinf (le_bot_iff.1 hle1)
  obtain ⟨hSL₀, hc₀, hgf₀⟩ := (hshape K₀ hK₀).of_center_ne_bot hZ₀
  obtain ⟨hSL₁, -, hgf₁⟩ := (hshape K₁ hK₁).of_center_ne_bot hZ₁
  have hcard : Nat.card ↥(K₀ ⊓ K₁) = 3 := by
    have hd : Nat.card ↥(K₀ ⊓ K₁) ∣ 3 := by
      have := Subgroup.card_dvd_of_le hle0
      rwa [Subgroup.card_map_of_injective K₀.subtype_injective, hc₀] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.1 h1) hinf
    · exact h3
  have heq : K₀ ⊓ K₁ = (center ↥K₀).map K₀.subtype :=
    Subgroup.eq_of_le_of_card_ge hle0 (by
      rw [hcard, Subgroup.card_map_of_injective K₀.subtype_injective, hc₀])
  exact ⟨K₁, hK₁, hne, hpair, hSL₀, hSL₁, heq, hgf₀, hgf₁⟩

theorem exists_inner_of_shape (hp3 : p = 3) (hOF : L34OuterFree) {t : G} (ht : orderOf t = 2)
    (hQt : pCoreOf 2 M = zpowers t) (hshape : ∀ K ∈ comps36 M, ShapeComp t K) {e : G} (he : e ∈ E)
    (he1 : e ≠ 1) : ∀ K ∈ comps36 M, ∃ g ∈ K, ∀ y ∈ K, e * y * e⁻¹ = g * y * g⁻¹ := by
  have hteM : ∀ m ∈ M, t * m = m * t := fun m hm => by
    have := h.mul_comm_of_pCoreOf_eq ht hQt hm
    calc t * m = (m * t * m⁻¹) * m := by rw [this]
      _ = m * t := by group
  have ht2' : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have he3' : e * e * e = 1 := by
    have := h.elem.2 e he
    rw [hp3, pow_three'] at this
    exact this
  intro K hK
  refine (hshape K hK).exists_inner hOF ht2' ((h.normalizes_component hK.1 hK.2).1 he) he3'
    (hteM e (h.E_le he)) ?_
  intro k _ hek
  have hkc : k ∈ centralizer ({e} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hek.symm
  exact hteM k (h.centralizer_le_of_ne_one he he1 hkc)

theorem mem_lam36_sup_centralizer_of_singleton (hp3 : p = 3) (hOF : L34OuterFree) {t : G}
    (ht : orderOf t = 2) (hQt : pCoreOf 2 M = zpowers t) (hshape : ∀ K ∈ comps36 M, ShapeComp t K)
    {K₀ : Subgroup G} (hs : comps36 M = {K₀}) {e : G} (he : e ∈ E) :
    e ∈ lam36 M ⊔ centralizer (lam36 M : Set G) := by
  by_cases he1 : e = 1
  · rw [he1]
    exact one_mem _
  have hK₀ : K₀ ∈ comps36 M := by rw [hs]; exact Set.mem_singleton K₀
  obtain ⟨g, hg, hgy⟩ := h.exists_inner_of_shape hp3 hOF ht hQt hshape he he1 K₀ hK₀
  have hΛ : lam36 M = K₀ := by rw [lam36, hs, sSup_singleton]
  refine mem_sup_centralizer_of_forall (S := comps36 M) rfl (hΛ ▸ hg) ?_
  intro K hK y hy
  rw [hs, Set.mem_singleton_iff] at hK
  subst hK
  exact hgy y hy

theorem mem_lam36_sup_centralizer (hp3 : p = 3) (he3 : twoLocalPrimeRank 3 G ≤ 3) (hOF : L34OuterFree)
    {t : G} (ht : orderOf t = 2) (hQt : pCoreOf 2 M = zpowers t) (hshape : ∀ K ∈ comps36 M, ShapeComp t K)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ comps36 M) {e : G} (he : e ∈ E) :
    e ∈ lam36 M ⊔ centralizer (lam36 M : Set G) := by
  rcases h.comps36_eq_singleton_or_pair hp3 he3 hshape hK₀ with hs | ⟨K₁, hK₁, hne, hpair, -⟩
  · exact h.mem_lam36_sup_centralizer_of_singleton hp3 hOF ht hQt hshape hs he
  by_cases he1 : e = 1
  · rw [he1]
    exact one_mem _
  have hex := h.exists_inner_of_shape hp3 hOF ht hQt hshape he he1
  obtain ⟨g₀, hg₀, hg₀y⟩ := hex K₀ hK₀
  obtain ⟨g₁, hg₁, hg₁y⟩ := hex K₁ hK₁
  have hcomm : ∀ a ∈ K₀, ∀ b ∈ K₁, a * b = b * a := by
    have hc : ⁅K₀, K₁⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hK₀.1 hK₁.1).resolve_left hne.symm
    have hK : K₀ ≤ centralizer (K₁ : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.1 (hK ha) b hb).symm
  have hΛ0 : K₀ ≤ lam36 M := le_sSup hK₀
  have hΛ1 : K₁ ≤ lam36 M := le_sSup hK₁
  refine mem_sup_centralizer_of_forall (S := comps36 M) rfl ((lam36 M).mul_mem (hΛ0 hg₀) (hΛ1 hg₁)) ?_
  intro K hK y hy
  rw [hpair] at hK
  rcases hK with rfl | hK
  · rw [hg₀y y hy]
    have h1 : g₁ * y = y * g₁ := (hcomm y hy g₁ hg₁).symm
    calc g₀ * y * g₀⁻¹ = g₀ * (y * g₁) * g₁⁻¹ * g₀⁻¹ := by group
      _ = g₀ * (g₁ * y) * g₁⁻¹ * g₀⁻¹ := by rw [h1]
      _ = (g₀ * g₁) * y * (g₀ * g₁)⁻¹ := by group
  · rw [Set.mem_singleton_iff] at hK
    subst hK
    rw [hg₁y y hy]
    have hy' : g₁ * y * g₁⁻¹ ∈ K := K.mul_mem (K.mul_mem hg₁ hy) (K.inv_mem hg₁)
    calc g₁ * y * g₁⁻¹ = (g₁ * y * g₁⁻¹) * g₀ * g₀⁻¹ := by group
      _ = g₀ * (g₁ * y * g₁⁻¹) * g₀⁻¹ := by rw [← hcomm g₀ hg₀ _ hy']
      _ = (g₀ * g₁) * y * (g₀ * g₁)⁻¹ := by group

theorem concl_of_normal_lam36 (hp3 : p = 3) {t : G} (ht : orderOf t = 2) (hQt : pCoreOf 2 M = zpowers t)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ comps36 M) (hK₀shape : ShapeComp t K₀) (hΛ : (lam36 M).Normal)
    (hCM : centralizer (lam36 M : Set G) ≤ M) (hED : E ≤ lam36 M ⊔ centralizer (lam36 M : Set G))
    (hstruct : comps36 M = {K₀} ∨ ∃ K₁ : Subgroup G, K₁ ∈ comps36 M ∧ K₁ ≠ K₀ ∧ comps36 M = {K₀, K₁} ∧
      Nonempty (↥K₀ ≃* SL(3, F4)) ∧ Nonempty (↥K₁ ≃* SL(3, F4)) ∧
      K₀ ⊓ K₁ = (center ↥K₀).map K₀.subtype ∧ UC6.InducesGraphField t K₀ ∧ UC6.InducesGraphField t K₁) :
    K36Concl M p := by
  haveI := hΛ
  haveI : (lam36 M ⊔ centralizer (lam36 M : Set G)).Normal := inferInstance
  have hD := h.sup_eq_top_of_normal hED
  have hΛM : lam36 M ⊔ M = ⊤ := by
    rw [← hD, sup_assoc, sup_eq_right.2 hCM]
  refine ⟨hp3, t, ht, hQt, lam36 M, hΛ, hΛM, ?_⟩
  rcases hstruct with hs | ⟨K₁, hK₁, hne, hpair, hSL₀, hSL₁, hinf, hgf₀, hgf₁⟩
  · have hΛ0 : lam36 M = K₀ := by rw [lam36, hs, sSup_singleton]
    rw [hΛ0]
    rcases hK₀shape with hgf | hA
    · exact Or.inl (Or.inl hgf)
    · exact Or.inr hA
  · have hΛ01 : lam36 M = K₀ ⊔ K₁ := by rw [lam36, hpair, sSup_pair]
    have hcomm : ∀ a ∈ K₀, ∀ b ∈ K₁, a * b = b * a := by
      have hc : ⁅K₀, K₁⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hK₀.1 hK₁.1).resolve_left hne.symm
      have hK : K₀ ≤ centralizer (K₁ : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.1 (hK ha) b hb).symm
    rw [hΛ01]
    exact Or.inl (Or.inr ⟨K₀, K₁, rfl, hcomm, hSL₀, hSL₁, hinf, hgf₀, hgf₁⟩)

theorem concl_of_forall_ne_top (O : Oracle36 M E p) (he3 : twoLocalPrimeRank 3 G ≤ 3) (hOF : L34OuterFree)
    (hall : ∀ K ∈ comps36 M, E ⊔ pCoreOf 2 M ⊔ K ≠ ⊤) : K36Concl M p := by
  obtain ⟨K₀, hK₀c, hK₀ne⟩ := h.exists_component
  have hK₀ : K₀ ∈ comps36 M := ⟨hK₀c, hK₀ne⟩
  obtain ⟨hp3, t, ht, hQt, hK₀shape⟩ := h.shapeComp_of_component O hK₀c hK₀ne (hall K₀ hK₀)
  have hshape : ∀ K ∈ comps36 M, ShapeComp t K := by
    intro K hK'
    obtain ⟨-, t', ht', hQt', hs⟩ := h.shapeComp_of_component O hK'.1 hK'.2 (hall K hK')
    have : t' = t := eq_of_zpowers_eq_of_orderOf_two ht' ht (hQt'.symm.trans hQt)
    exact this ▸ hs
  have hΛn : normalizer (lam36 M : Set G) = ⊤ :=
    h.normalizer_lam36_eq_top_of_rank hp3 he3 (fun K hK' => (hshape K hK').rank2Good)
  haveI hΛ : (lam36 M).Normal := Subgroup.normalizer_eq_top_iff.1 hΛn
  have hCM : centralizer (lam36 M : Set G) ≤ M := h.centralizer_lam36_le O hΛ
  have hED : E ≤ lam36 M ⊔ centralizer (lam36 M : Set G) := fun e he' =>
    h.mem_lam36_sup_centralizer hp3 he3 hOF ht hQt hshape hK₀ he'
  exact h.concl_of_normal_lam36 hp3 ht hQt hK₀ hK₀shape hΛ hCM hED
    (h.comps36_eq_singleton_or_pair hp3 he3 hshape hK₀)

theorem frame_of_forall_ne_top (hconcl : (∀ K ∈ comps36 M, E ⊔ pCoreOf 2 M ⊔ K ≠ ⊤) → K36Concl M p) :
    K36Concl M p ∨ ∃ L : Subgroup G, L.Normal ∧ CFSG.IsComponent L ∧ ⁅L, pCoreOf 2 M⁆ ≠ ⊥ ∧
      E ⊔ pCoreOf 2 M ⊔ L = ⊤ := by
  by_cases hcase : ∃ K ∈ comps36 M, E ⊔ pCoreOf 2 M ⊔ K = ⊤
  · right
    obtain ⟨K, hKc, hKt⟩ := hcase
    refine ⟨K, ?_, hKc.1, hKc.2, hKt⟩
    have hN : normalizer (K : Set G) = ⊤ := by
      refine top_le_iff.1 (hKt.symm.le.trans ?_)
      obtain ⟨hEN, hQN⟩ := h.normalizes_component hKc.1 hKc.2
      exact sup_le (sup_le hEN hQN) Subgroup.le_normalizer
    exact Subgroup.normalizer_eq_top_iff.1 hN
  · left
    push Not at hcase
    exact hconcl hcase

theorem frame_312_of_oracle (O : Oracle36 M E p) (he3 : twoLocalPrimeRank 3 G ≤ 3) (hOF : L34OuterFree) :
    K36Concl M p ∨ ∃ L : Subgroup G, L.Normal ∧ CFSG.IsComponent L ∧ ⁅L, pCoreOf 2 M⁆ ≠ ⊥ ∧
      E ⊔ pCoreOf 2 M ⊔ L = ⊤ :=
  h.frame_of_forall_ne_top (fun hall => h.concl_of_forall_ne_top O he3 hOF hall)

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
