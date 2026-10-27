module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Lam
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSevenPrime
public import CFSG.Alternating.Multipliers.OddKernel
import CFSG.LocalAnalysis.UniquenessCase.UC6K316L34
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup Equiv Equiv.Perm

namespace Alt36

section TwoLocal

theorem pCoreOf_ne_bot_of_isNilpotent {X : Type*} [Group X] [Finite X] {r : ℕ} [Fact r.Prime] {H : Subgroup X}
    [Group.IsNilpotent H] (hr : r ∣ Nat.card H) : pCoreOf r H ≠ ⊥ := by
  obtain ⟨P⟩ : Nonempty (Sylow r H) := inferInstance
  have hPn : (P : Subgroup H).Normal :=
    Sylow.normal_of_normalizerCondition normalizerCondition_of_isNilpotent P
  have hle : (P : Subgroup H).map H.subtype ≤ pCoreOf r H :=
    CFSG.LieType.BorelTits.le_pCoreOf r (Subgroup.map_subtype_le _)
      (by
        change ((((P : Subgroup H)).map H.subtype).comap H.subtype).Normal
        rwa [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]) (P.isPGroup'.map _)
  intro hbot
  rw [hbot, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at hle
  exact P.ne_bot_of_dvd_card hr hle

variable {J A : Type*} [Group J] [Finite J] [Group A] [Finite A]

theorem pCoreOf_comap_ne_bot (ψ : J →* A) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center J)
    {V : Subgroup A} (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥) : pCoreOf 2 (V.comap ψ) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : V.comap ψ →* V := ψ.subgroupComap V
  have hf : Function.Surjective f := ψ.subgroupComap_surjective V hψ
  have hfker : f.ker ≤ center (V.comap ψ) := by
    intro w hw
    have h1 : (w : J) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.1 hw)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.1 (hker h1)) g)
  haveI : Group.IsNilpotent V := hV.isNilpotent
  haveI : Group.IsNilpotent (V.comap ψ) := Subgroup.isNilpotent_of_ker_le_center f hfker
  have h2V : 2 ∣ Nat.card V := by
    obtain ⟨k, hk⟩ := hV.exists_card_eq
    rcases k with _ | k
    · exact absurd (Subgroup.card_eq_one.1 (by rw [hk, pow_zero])) hV1
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _
  exact pCoreOf_ne_bot_of_isNilpotent (h2V.trans (Subgroup.card_dvd_of_surjective hf))

theorem comap_normalizer_le (ψ : J →* A) (V : Subgroup A) :
    (normalizer (V : Set A)).comap ψ ≤ normalizer (pCoreOf 2 (V.comap ψ) : Set J) :=
  (Subgroup.le_normalizer_comap ψ).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem pRank_comap_le_twoLocalPrimeRank {G : Type} [Group G] [Finite G] {L : Subgroup G} (ψ : ↥L →* A)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center ↥L) {V : Subgroup A} (hV : IsPGroup 2 V)
    (hV1 : V ≠ ⊥) {B : Subgroup A} (hB : B ≤ normalizer (V : Set A)) {q : ℕ} (hq : q.Prime) :
    CFSG.Open.pRank q (B.comap ψ) ≤ twoLocalPrimeRank q G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Subgroup ↥L := pCoreOf 2 (V.comap ψ)
  have hT1 : T ≠ ⊥ := pCoreOf_comap_ne_bot ψ hψ hker hV hV1
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTG1 : T.map L.subtype ≠ ⊥ := fun h =>
    hT1 ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h)
  have hloc : IsTwoLocal (normalizer ((T.map L.subtype : Subgroup G) : Set G)) :=
    ⟨T.map L.subtype, hTG1, hT2.map _, rfl⟩
  have hBN : (B.comap ψ).map L.subtype ≤ normalizer ((T.map L.subtype : Subgroup G) : Set G) :=
    (Subgroup.map_mono ((Subgroup.comap_mono hB).trans (comap_normalizer_le ψ V))).trans
      (Subgroup.le_normalizer_map _)
  calc CFSG.Open.pRank q (B.comap ψ) ≤ CFSG.Open.pRank q ((B.comap ψ).map L.subtype) :=
        CFSG.SectionRank.pRank_le_map hq.one_lt _ L.subtype_injective _
    _ ≤ CFSG.Open.pRank q (normalizer ((T.map L.subtype : Subgroup G) : Set G)) :=
        CFSG.SectionRank.pRank_mono hq.one_lt hBN
    _ ≤ twoLocalPrimeRank q G := pRank_le_twoLocalPrimeRank hq hloc

end TwoLocal

section Klein

variable {n : ℕ}

@[expose] def four (n : ℕ) : Finset (Fin n) := Finset.univ.filter fun x => x.val < 4

theorem mem_four {x : Fin n} : x ∈ four n ↔ x.val < 4 := by
  simp [four]

theorem card_four (hn : 4 ≤ n) : Nat.card (four n) = 4 := by
  rw [Nat.card_eq_finsetCard, four, Fin.card_filter_val_lt]
  omega

@[expose] noncomputable def klein (n : ℕ) : Subgroup (alternatingGroup (Fin n)) :=
  (alternatingGroup.kleinFour (four n)).map (alternatingGroup.ofSubtype (four n))

theorem card_klein (hn : 4 ≤ n) : Nat.card (klein n) = 4 := by
  rw [klein, Subgroup.card_map_of_injective alternatingGroup.ofSubtype_injective]
  exact alternatingGroup.kleinFour_card_of_card_eq_four (card_four hn)

theorem isPGroup_klein (hn : 4 ≤ n) : IsPGroup 2 (klein n) :=
  IsPGroup.of_card (n := 2) (by rw [card_klein hn]; norm_num)

theorem klein_ne_bot (hn : 4 ≤ n) : klein n ≠ ⊥ := fun h => by
  have h4 := card_klein hn
  rw [h, Subgroup.card_bot] at h4
  norm_num at h4

theorem mem_normalizer_klein_of_subset (hn : 4 ≤ n) {g : alternatingGroup (Fin n)}
    (hg : (g : Perm (Fin n)).support ⊆ four n) : g ∈ normalizer (klein n : Set (alternatingGroup (Fin n))) := by
  obtain ⟨k, rfl⟩ := (alternatingGroup.mem_range_ofSubtype_iff (four n) g).2 hg
  haveI := alternatingGroup.normal_kleinFour (card_four hn)
  refine Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ ?_)
  rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
  exact Subgroup.mem_top k

theorem mem_normalizer_klein_of_disjoint {g : alternatingGroup (Fin n)}
    (hg : Disjoint (g : Perm (Fin n)).support (four n)) :
    g ∈ normalizer (klein n : Set (alternatingGroup (Fin n))) := by
  have hcomm : ∀ v ∈ klein n, g * v = v * g := by
    intro v hv
    obtain ⟨v₀, -, rfl⟩ := Subgroup.mem_map.1 hv
    have hv' : ((alternatingGroup.ofSubtype (four n) v₀ : alternatingGroup (Fin n)) : Perm (Fin n)).support ⊆
        four n := (alternatingGroup.mem_range_ofSubtype_iff (four n) _).1 ⟨v₀, rfl⟩
    have hd : Perm.Disjoint (g : Perm (Fin n))
        ((alternatingGroup.ofSubtype (four n) v₀ : alternatingGroup (Fin n)) : Perm (Fin n)) :=
      disjoint_iff_disjoint_support.2 (Finset.disjoint_of_subset_right hv' hg)
    exact Subtype.ext hd.commute.eq
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    rw [hcomm v hv, mul_inv_cancel_right]
    exact hv
  · intro hv
    have h1 := hcomm _ hv
    have h2 : v = g * v * g⁻¹ := by
      calc v = g⁻¹ * ((g * v * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * v * g⁻¹)) := by rw [h1]
        _ = g * v * g⁻¹ := by group
    rw [h2]
    exact hv

theorem eq_of_mem_support_swap_mul_swap {α : Type*} [Fintype α] [DecidableEq α] {a b c x : α}
    (h : x ∈ (swap a b * swap a c).support) : x = a ∨ x = b ∨ x = c := by
  by_contra hx
  simp only [not_or] at hx
  apply mem_support.1 h
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 hx.2.2, swap_apply_of_ne_of_ne hx.1 hx.2.1]

@[expose] def pt (n k : ℕ) (hk : k < n) : Fin n := ⟨k, hk⟩

theorem tcyc_aux (hn : 13 ≤ n) (i : Fin 4) :
    (swap (pt n (3 * i.val + 1) (by omega)) (pt n (3 * i.val + 2) (by omega)) *
      swap (pt n (3 * i.val + 1) (by omega)) (pt n (3 * i.val + 3) (by omega))).IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same (Fin.ne_of_val_ne (by simp [pt])) (Fin.ne_of_val_ne (by simp [pt]))
    (Fin.ne_of_val_ne (by simp [pt]))

@[expose] def tcyc (hn : 13 ≤ n) (i : Fin 4) : alternatingGroup (Fin n) :=
  ⟨swap (pt n (3 * i.val + 1) (by omega)) (pt n (3 * i.val + 2) (by omega)) *
      swap (pt n (3 * i.val + 1) (by omega)) (pt n (3 * i.val + 3) (by omega)),
    (tcyc_aux hn i).mem_alternatingGroup⟩

theorem tcyc_isThreeCycle (hn : 13 ≤ n) (i : Fin 4) : ((tcyc hn i : alternatingGroup (Fin n)) :
    Perm (Fin n)).IsThreeCycle :=
  tcyc_aux hn i

theorem val_of_mem_support_tcyc (hn : 13 ≤ n) {i : Fin 4} {x : Fin n}
    (hx : x ∈ ((tcyc hn i : alternatingGroup (Fin n)) : Perm (Fin n)).support) :
    3 * i.val + 1 ≤ x.val ∧ x.val ≤ 3 * i.val + 3 := by
  rcases eq_of_mem_support_swap_mul_swap hx with rfl | rfl | rfl <;> simp [pt]

theorem tcyc_disjoint (hn : 13 ≤ n) (i j : Fin 4) (hij : i ≠ j) :
    Disjoint ((tcyc hn i : alternatingGroup (Fin n)) : Perm (Fin n)).support
      ((tcyc hn j : alternatingGroup (Fin n)) : Perm (Fin n)).support := by
  refine Finset.disjoint_left.2 fun x hxi hxj => hij (Fin.ext ?_)
  have h1 := val_of_mem_support_tcyc hn hxi
  have h2 := val_of_mem_support_tcyc hn hxj
  omega

theorem tcyc_mem_normalizer (hn : 13 ≤ n) (i : Fin 4) :
    tcyc hn i ∈ normalizer (klein n : Set (alternatingGroup (Fin n))) := by
  by_cases hi : i = 0
  · refine mem_normalizer_klein_of_subset (by omega) fun x hx => ?_
    have h1 := val_of_mem_support_tcyc hn hx
    rw [hi] at h1
    rw [mem_four]
    simp only [Fin.val_zero] at h1
    omega
  · refine mem_normalizer_klein_of_disjoint (Finset.disjoint_left.2 fun x hx hx4 => ?_)
    have h1 := val_of_mem_support_tcyc hn hx
    rw [mem_four] at hx4
    have hi1 : 1 ≤ i.val := Nat.one_le_iff_ne_zero.2 fun h => hi (Fin.ext h)
    omega

end Klein

theorem four_le_twoLocalPrimeRank_of_thirteen_le {G : Type} [Group G] [Finite G] (L : Subgroup G) {n : ℕ}
    (φ : ↥L ⧸ center ↥L ≃* alternatingGroup (Fin n)) (hn : 13 ≤ n) : 4 ≤ twoLocalPrimeRank 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ : ↥L →* alternatingGroup (Fin n) := φ.toMonoidHom.comp (QuotientGroup.mk' (center ↥L))
  have hψ : Function.Surjective ψ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = center ↥L := by
    ext x
    simp [ψ, MonoidHom.mem_ker]
  obtain ⟨U⟩ : Nonempty (Sylow 3 ψ.ker) := inferInstance
  have hU : ∀ u : ψ.ker, u ∈ U → (u : ↥L) ∈ center ↥L := fun u _ => hker ▸ u.2
  have h4 := CFSG.AGLEmbeddingD2.four_le_pRank_comap_of_central_sylow_alt ψ hψ U hU (tcyc hn)
    (tcyc_isThreeCycle hn) (tcyc_disjoint hn)
  have hB : closure (Set.range (tcyc hn)) ≤ normalizer (klein n : Set (alternatingGroup (Fin n))) :=
    (Subgroup.closure_le _).2 (Set.range_subset_iff.2 (tcyc_mem_normalizer hn))
  exact h4.trans (pRank_comap_le_twoLocalPrimeRank ψ hψ hker.le (isPGroup_klein (by omega))
    (klein_ne_bot (by omega)) hB Nat.prime_three)

end Alt36

namespace Hyp36

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem centerOf_eq (L : Subgroup G) : Odd.centerOf L = (center ↥L).map L.subtype := by
  ext z
  rw [Odd.mem_centerOf]
  constructor
  · rintro ⟨hzL, hz⟩
    exact ⟨⟨z, hzL⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hz g g.2), rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨y, hy⟩)⟩

theorem center_eq_bot (h : Hyp36 G M p E) (L : Subgroup G) [L.Normal] (hLp : Group.IsPerfect ↥L) {n : ℕ}
    (hn : 8 ≤ n) (φ : ↥L ⧸ center ↥L ≃* alternatingGroup (Fin n)) : center ↥L = ⊥ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set ψ : ↥L →* alternatingGroup (Fin (m + 2)) := φ.toMonoidHom.comp (QuotientGroup.mk' (center ↥L))
  have hψ : Function.Surjective ψ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = center ↥L := by
    ext x
    simp [ψ, MonoidHom.mem_ker]
  haveI := hLp
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega : 6 ≤ m) ψ hψ hker.le
    (hker ▸ h.odd_card_center_of_normal L)
  rw [hker] at h1
  exact Subgroup.card_eq_one.1 h1

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
