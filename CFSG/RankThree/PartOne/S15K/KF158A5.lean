module

public import CFSG.RankThree.PartOne.S15K.KF158A
public import CFSG.RankThree.PartOne.S15K.PairComp
public import CFSG.RankThree.PartOne.S15K.U5Pair
public import CFSG.RankThree.PartOne.S15K.FiveCoord

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.RankThree.PartOne.U5K.Pkg
open scoped commutatorElement

@[expose] def KF158FiveRefl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∃ t ∈ reflectionSet p E, autFixedInG E t = A

@[expose] def KF158FiveS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ t ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E, orderOf (t * s) = 3 →
      ∃ S : Subgroup G, S ≤ kZero p E t ⊔ kZero p E s ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
        autFixedInG E t ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, autFixedInG E t⁆

variable {G : Type} [Group G] [Finite G]

theorem card_autFixedInG_five {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hcardE : Nat.card E = p ^ 4) {t : MulAut E}
    (ht : t ∈ reflectionSet p E) : Nat.card ↥(autFixedInG E t) = p ^ 3 := by
  obtain ⟨-, -, -, hcard⟩ := Sec13Base.reflection_facts h ht
  have hp := h.prime
  unfold autFixedInG
  rw [Subgroup.card_map_of_injective E.subtype_injective]
  rw [hcardE] at hcard
  have hpos : 0 < p := hp.pos
  have h4 : Nat.card ↥(autFixed E t) * p = p ^ 3 * p := by rw [← hcard]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos h4

theorem exists_pair_J (hS : SchreierFor InCatalog) (h82 : LocalThetaComponentEmbeddingFrontier)
    (hPair : KFU5PairEx) (hSU3 : KF158FiveS) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {c' : E} (M : Model p E c') {x y z : Fin 5}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∃ J : Subgroup G, kZero p E (fiveT M x y) ⊔ kZero p E (fiveT M y z) ≤ J ∧
      autFixedInG E (fiveT M x y) ⊓ Subgroup.centralizer (J : Set G) =
        autFixedInG E (fiveT M x y) ⊓ autFixedInG E (fiveT M y z) ∧
      J ∈ thetaCompCentralizer p (autFixedInG E (fiveT M x y) ⊓ autFixedInG E (fiveT M y z)) ∧
      ∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
        autFixedInG E (fiveT M x y) ≤ Subgroup.normalizer (S : Set G) ∧
        S = ⁅S, autFixedInG E (fiveT M x y)⁆ := by
  classical
  have h := h15.h12
  have hp := h.prime
  obtain ⟨-, -, -, -, -, hcardE, -, -⟩ := id hout
  have ht : fiveT M x y ∈ reflectionSet p E := fiveT_mem M hxy
  have hs : fiveT M y z ∈ reflectionSet p E := fiveT_mem M hyz
  have hord : orderOf (fiveT M x y * fiveT M y z) = 3 := fiveT_mul_orderOf M hxy hyz hxz
  set t := fiveT M x y with htdef
  set s := fiveT M y z with hsdef
  have htt : t * t = 1 := RefFacts.mul_self_eq_one ht.1
  have hss : s * s = 1 := RefFacts.mul_self_eq_one hs.1
  have hts : t * s ≠ s * t := by
    intro hcomm
    have h2 : (t * s) ^ 2 = 1 := by
      calc (t * s) ^ 2 = t * s * (t * s) := by rw [pow_two]
        _ = t * (s * t) * s := by group
        _ = t * (t * s) * s := by rw [← hcomm]
        _ = (t * t) * (s * s) := by group
        _ = 1 := by rw [htt, hss, one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at this
    omega
  have hne : t ≠ s := by
    intro hts'
    rw [← hts'] at hord
    rw [htt, orderOf_one] at hord
    omega
  obtain ⟨f', hf', hAtf, hPairs⟩ := hPair G p A c L E h15 hF hout
  have hAtt : KFAt p E f' t := hAtf t ht
  have hAts : KFAt p E f' s := hAtf s hs
  have hU : CentrallyUThree f' ↥(kZero p E t ⊔ kZero p E s) := (hPairs t ht s hs hne).2 hord
  have hDcard' : Nat.card ↥(autFixedInG E t ⊓ autFixedInG E s) = p ^ 2 :=
    card_fiveFixedInG_inf M hxy hyz hxz
  have hCt := card_autFixedInG_five h hcardE ht
  have hCs := card_autFixedInG_five h hcardE hs
  set D : Subgroup G := autFixedInG E t ⊓ autFixedInG E s with hD
  have hDcard : Nat.card ↥D = p ^ 2 := hDcard'
  set C : Subgroup G := Subgroup.centralizer (D : Set G) with hC
  obtain ⟨Mc, hMc, hKt, hKs⟩ := exists_thetaComp_pair hS h82 h hAtt hAts hf' hU hts hD hDcard hCt hCs
  set J : Subgroup G := Mc.map C.subtype with hJ
  have hK1J : kZero p E t ≤ J := fun x hx => ⟨⟨x, kZero_le_centralizer_of_le (inf_le_left) hx⟩,
    hKt (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hK2J : kZero p E s ≤ J := fun x hx => ⟨⟨x, kZero_le_centralizer_of_le (inf_le_right) hx⟩,
    hKs (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hJC : J ≤ C := Subgroup.map_subtype_le _
  have hBJ : autFixedInG E t ⊓ Subgroup.centralizer (J : Set G) = D := by
    apply le_antisymm
    · rintro x ⟨hxt, hxJ⟩
      have hxE : x ∈ E := (Subgroup.map_subtype_le _) hxt
      have hxK2 : x ∈ E ⊓ Subgroup.centralizer (kZero p E s : Set G) :=
        ⟨hxE, Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hK2J) hxJ⟩
      have hxs : x ∈ autFixedInG E s := by
        have := hAts.2.2.1
        rw [← this]
        exact hxK2
      exact ⟨hxt, hxs⟩
    · intro x hx
      exact ⟨hx.1, Subgroup.le_centralizer_iff.1 hJC hx⟩
  obtain ⟨S, hSJ, hS1, hS2, hSN, hSc⟩ := hSU3 G p A c L E h15 hF hout t ht s hs hord
  exact ⟨J, sup_le hK1J hK2J, hBJ, ⟨Mc, hMc, rfl⟩, S, hSJ.trans (sup_le hK1J hK2J), hS1, hS2, hSN,
    hSc⟩

theorem kf158AFive_of_model (hS : SchreierFor InCatalog) (h82 : LocalThetaComponentEmbeddingFrontier)
    (hPair : KFU5PairEx) (hRefl : KF158FiveRefl) (hSU3 : KF158FiveS) :
    KF158AFive := by
  intro G _ _ p A c L E h15 hF hout
  classical
  have h := h15.h12
  have hp := h.prime
  obtain ⟨-, -, -, -, -, hcardE, -, -⟩ := id hout
  obtain ⟨ψ, k, hk, hstab⟩ := exists_psi_k h15 hF hout
  let M := mkModel h15 hF hout ψ k hk hstab
  obtain ⟨t₀, ht₀, htA⟩ := hRefl G p A c L E h15 hF hout
  obtain ⟨a, b, hab, hTab⟩ := exists_fiveT_of_mem M ht₀
  subst hTab
  obtain ⟨l, hla, hlb⟩ : ∃ l : Fin 5, l ≠ a ∧ l ≠ b := by
    have : ∀ a b : Fin 5, ∃ l : Fin 5, l ≠ a ∧ l ≠ b := by decide
    exact this a b
  have hbl : b ≠ l := hlb.symm
  have hal : a ≠ l := hla.symm
  obtain ⟨J, hKJ, hAJ', hJθ, S, hSJ, hS1, hS2, hSN, hSc⟩ :=
    exists_pair_J hS h82 hPair hSU3 h15 hF hout M hab hbl hal
  have ht : fiveT M a b ∈ reflectionSet p E := fiveT_mem M hab
  obtain ⟨f', hf', hAtf, -⟩ := hPair G p A c L E h15 hF hout
  have hAtt : KFAt p E f' (fiveT M a b) := hAtf _ ht
  have hDcard : Nat.card ↥(autFixedInG E (fiveT M a b) ⊓ autFixedInG E (fiveT M b l)) = p ^ 2 :=
    card_fiveFixedInG_inf M hab hbl hal
  have hCt := card_autFixedInG_five h hcardE ht
  have hne' := hAtt.1
  refine ⟨fiveT M a b, ht, kZero p E (fiveT M a b), J, ⟨fun f' hf' => absurd ⟨f', hf'⟩ hne', fun _ => rfl⟩,
    le_sup_left.trans hKJ, hAtt.2.2.2.1, ?_, ?_, S, hSJ, hS1, hS2, ?_, ?_⟩
  · rw [← htA, hAJ', hDcard, hCt]
    ring
  · rw [← htA, hAJ']
    exact hJθ
  · rw [← htA]
    exact hSN
  · rw [← htA]
    exact hSc

end CFSG.RankThree.PartOne.S15K
