module

public import CFSG.Quasithin.EmptyFaithful.S146zMSuz
public import CFSG.Quasithin.Background.F9Comp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporNorm
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.SectionRank
open scoped commutatorElement

section Aux

variable {Q : Type*} [Group Q]

theorem isSolvable_finset_sup_of_commute {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Subgroup Q) (hs : ∀ i ∈ s, Group.IsSolvable ↥(f i))
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ f i, ∀ y ∈ f j, x * y = y * x) :
    Group.IsSolvable ↥(s.sup f) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    infer_instance
  | insert a s ha ih =>
    rw [Finset.sup_insert]
    have hs' : ∀ i ∈ s, Group.IsSolvable ↥(f i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
    have hc' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ f i, ∀ y ∈ f j, x * y = y * x :=
      fun i hi j hj hij => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hB := ih hs' hc'
    have hA := hs a (Finset.mem_insert_self a s)
    have hcomm : ∀ x ∈ f a, ∀ y ∈ s.sup f, x * y = y * x := by
      intro x hx y hy
      have hle : s.sup f ≤ Subgroup.centralizer ({x} : Set Q) := by
        refine Finset.sup_le fun i hi => ?_
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact hc a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi)) w hx z hz
      exact (Subgroup.mem_centralizer_iff.mp (hle hy)) x (Set.mem_singleton x)
    have hcomm' : ∀ (x : ↥(f a)) (y : ↥(s.sup f)),
        Commute ((f a).subtype x) ((s.sup f).subtype y) := fun x y => hcomm x x.2 y y.2
    have hrange : ((f a).subtype.noncommCoprod (s.sup f).subtype hcomm').range =
        f a ⊔ s.sup f := by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    set φ := (f a).subtype.noncommCoprod (s.sup f).subtype hcomm' with hφ
    have := hA
    have := hB
    have hsolvr : Group.IsSolvable ↥φ.range :=
      Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    rwa [hrange] at hsolvr

end Aux

section Main

variable {Q : Type} [Group Q] [Finite Q]

theorem zm_isSylowTwoOf_inf_of_isSubnormal {T H L : Subgroup Q} (h : IsSubnormal L H) :
    IsSylowTwoOf T H → IsSylowTwoOf (T ⊓ L) L := by
  induction h with
  | refl K =>
    intro hT
    rwa [inf_eq_left.mpr hT.1]
  | @step L M K hLM hN _ ih =>
    intro hT
    have h1 := ih hT
    have hnorm : M ≤ Subgroup.normalizer (L : Set Q) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hN
    have h2 := B6.isSylowTwoOf_inf_normal h1 hLM hnorm
    rwa [inf_assoc, inf_eq_right.mpr hLM] at h2

@[expose] def borOf (T L : Subgroup Q) : Subgroup Q :=
  Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) ⊓ L

theorem borOf_suzuki {T L : Subgroup Q} (hT : IsSylowTwoOf T ⊤)
    (hsub : IsSubnormal L ⊤) {f : ℕ} (hf : CFSG.Blueprint.SuzukiModel ↥L 2 f) :
    Group.IsSolvable ↥(borOf T L) ∧
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ ℓ ∣ Nat.card ↥(borOf T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl := zm_isSylowTwoOf_inf_of_isSubnormal hsub hT
  have hpg : IsPGroup 2 ↥((T ⊓ L).subgroupOf L) :=
    hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.1).symm
  let S₁ : Sylow 2 ↥L := hpg.toSylow hSyl.2.2
  obtain ⟨hs, ℓ, hℓ, h2, h3, hdvd⟩ := suzuki_normalizer_sylow hf S₁
  set N := Subgroup.normalizer ((S₁ : Subgroup ↥L) : Set ↥L) with hN
  have hS₁ : (S₁ : Subgroup ↥L) = (T ⊓ L).subgroupOf L := rfl
  have hNeq : N = (Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)).comap L.subtype := by
    rw [hN, hS₁]
    exact (Subgroup.comap_normalizer_eq_of_le_range (f := L.subtype)
      (by rw [Subgroup.range_subtype]; exact inf_le_right)).symm
  have hbor : borOf T L = N.map L.subtype := by
    rw [hNeq, Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_comm _ _
  rw [hbor]
  refine ⟨Group.isSolvable_of_surjective (f := L.subtype.subgroupMap N)
    (L.subtype.subgroupMap_surjective N), ℓ, hℓ, h2, h3, ?_⟩
  rw [Subgroup.card_map_of_injective L.subtype_injective]
  exact hdvd

omit [Finite Q] in
theorem conjSub_borOf {T L : Subgroup Q} {t : Q} (ht : t ∈ T) :
    conjSub t (borOf T L) = borOf T (conjSub t L) := by
  unfold borOf
  rw [conjSub_inf, ← conjSub_normalizer, conjSub_inf, F7.conjSub_eq_of_mem ht]

theorem exists_solvable_normalized_of_suzuki
    (h37 : A37Statement Q) {T : Subgroup Q} (hT : IsSylowTwoOf T ⊤) {K : Subgroup Q}
    (hSz : ∀ L ∈ cComp (⊤ : Subgroup Q),
      ⁅L, K⁆ = ⊥ ∧ ∃ f : ℕ, CFSG.Blueprint.SuzukiModel ↥L 2 f)
    {J : Subgroup Q} (hJ : J ∈ cComp (⊤ : Subgroup Q)) {P : Subgroup Q} (hPK : P ≤ K) :
    ∃ B : Subgroup Q, Group.IsSolvable ↥B ∧ P ≤ Subgroup.normalizer (B : Set Q) ∧
      T ≤ Subgroup.normalizer (B : Set Q) ∧
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ ℓ ∣ Nat.card ↥B := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  set 𝒥 : Finset (Subgroup Q) :=
    ((Finset.univ : Finset Q).filter fun t => t ∈ T).image fun t => conjSub t J with h𝒥def
  have h𝒥 : ∀ L ∈ 𝒥, ∃ t ∈ T, L = conjSub t J := fun L hL => by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hL
    exact ⟨t, (Finset.mem_filter.mp ht).2, rfl⟩
  have h𝒥c : ∀ L ∈ 𝒥, L ∈ cComp (⊤ : Subgroup Q) := fun L hL => by
    obtain ⟨t, -, rfl⟩ := h𝒥 L hL
    exact conjSub_mem_cComp_of_mem hJ (Subgroup.mem_top t)
  have h𝒥T : ∀ L ∈ 𝒥, ∀ s ∈ T, conjSub s L ∈ 𝒥 := fun L hL s hs => by
    obtain ⟨t, ht, rfl⟩ := h𝒥 L hL
    rw [← conjSub_mul]
    exact Finset.mem_image.mpr ⟨s * t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.mul_mem hs ht⟩, rfl⟩
  have hJ𝒥 : J ∈ 𝒥 :=
    Finset.mem_image.mpr ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.one_mem⟩, conjSub_one J⟩
  set B : Subgroup Q := 𝒥.sup (borOf T) with hB
  have hbor_le : ∀ L ∈ 𝒥, borOf T L ≤ B := fun L hL => Finset.le_sup (f := borOf T) hL
  have hborL : ∀ L, borOf T L ≤ L := fun L => inf_le_right
  have hsuz : ∀ L ∈ 𝒥, Group.IsSolvable ↥(borOf T L) ∧
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ ℓ ∣ Nat.card ↥(borOf T L) := fun L hL => by
    obtain ⟨f, hf⟩ := (hSz L (h𝒥c L hL)).2
    exact borOf_suzuki hT (subnormal_of_mem_cComp (h𝒥c L hL)) hf
  have hcomm : ∀ L ∈ 𝒥, ∀ L' ∈ 𝒥, L ≠ L' → ∀ x ∈ borOf T L, ∀ y ∈ borOf T L', x * y = y * x := by
    intro L hL L' hL' hne x hx y hy
    have h1 : ⁅L, L'⁆ = ⊥ := h37 L (h𝒥c L hL) L' (h𝒥c L' hL') hne
    have h2 : ⁅x, y⁆ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator (hborL L hx) (hborL L' hy)
    rw [h1, Subgroup.mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hBs : Group.IsSolvable ↥B :=
    isSolvable_finset_sup_of_commute 𝒥 (borOf T) (fun L hL => (hsuz L hL).1)
      (fun L hL L' hL' hne x hx y hy => hcomm L hL L' hL' hne x hx y hy)
  have hBconj : ∀ t ∈ T, B ≤ conjSub t⁻¹ B := by
    intro t ht
    refine Finset.sup_le fun L hL => ?_
    rw [le_conjSub_iff, inv_inv, conjSub_borOf ht]
    exact hbor_le _ (h𝒥T L hL t ht)
  have hBeq : ∀ t ∈ T, conjSub t B = B := by
    intro t ht
    refine le_antisymm ((conjSub_le_iff t).mpr (hBconj t ht)) ?_
    have := hBconj t⁻¹ (T.inv_mem ht)
    rwa [inv_inv] at this
  have hTn : T ≤ Subgroup.normalizer (B : Set Q) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hBeq t ht]
      exact mul_mem_conjSub hh
    · intro hh
      have := mul_mem_conjSub (g := t⁻¹) hh
      rw [hBeq t⁻¹ (T.inv_mem ht)] at this
      have e : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
      rwa [e] at this
  have hBc : ∀ p ∈ P, B ≤ Subgroup.centralizer ({p} : Set Q) := by
    intro p hp
    refine Finset.sup_le fun L hL => ?_
    have hLc : L ≤ Subgroup.centralizer (K : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hSz L (h𝒥c L hL)).1
    intro x hx
    have := Subgroup.mem_centralizer_iff.mp (hLc (hborL L hx)) p (hPK hp)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact this
  have hPn : P ≤ Subgroup.normalizer (B : Set Q) := by
    intro p hp
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (hBc p hp hb) p (Set.mem_singleton p)).symm
  obtain ⟨ℓ, hℓ, h2, h3, hd⟩ := (hsuz J hJ𝒥).2
  exact ⟨B, hBs, hPn, hTn, ℓ, hℓ, h2, h3, hd.trans (Subgroup.card_dvd_of_le (hbor_le J hJ𝒥))⟩

end Main


end CFSG.Quasithin
