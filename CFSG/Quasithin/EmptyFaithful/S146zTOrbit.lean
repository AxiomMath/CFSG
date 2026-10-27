module

public import CFSG.Quasithin.EmptyFaithful.S146zTSeven
public import CFSG.Quasithin.Background.SzQTwoClosed
public import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.Quasithin.S146zT

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.F7
open scoped commutatorElement

section Basic

variable {Q : Type} [Group Q]

theorem isSylowTwoOf_eq_of_le [Finite Q] {R S L : Subgroup Q} (hR : IsSylowTwoOf R L)
    (hS : IsSylowTwoOf S L) (hRS : R ≤ S) : R = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : R.relIndex S * S.relIndex L = R.relIndex L :=
    Subgroup.relIndex_mul_relIndex R S L hRS hS.1
  have hodd : ¬ 2 ∣ R.relIndex S := fun hd =>
    isSylowTwoOf_odd_relIndex hR (h1 ▸ hd.mul_right _)
  obtain ⟨k, hk⟩ := hS.2.1.index (R.subgroupOf S)
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ (R.subgroupOf S).index := hk ▸ dvd_pow_self 2 hk0
    exact hodd h2
  have h2 : R.relIndex S = 1 := by
    change (R.subgroupOf S).index = 1
    rw [hk, hk0, pow_zero]
  exact le_antisymm hRS (Subgroup.relIndex_eq_one.mp h2)

@[expose] def IsSzSub (L : Subgroup Q) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ Nonempty (↥L ≃* ↥(Sz n))

theorem isSzSub_conjSub {L : Subgroup Q} (h : IsSzSub L) (g : Q) : IsSzSub (conjSub g L) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := h
  exact ⟨n, hn, ⟨(Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e⟩⟩

theorem isComponent_of_cComp_suzuki [Finite Q] {L : Subgroup Q}
    (hL : L ∈ cComp (⊤ : Subgroup Q)) (hSz : IsSzSub L) : CFSG.IsComponent L := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hSz
  obtain ⟨-, a, ha, K, hKf, hKfin, hfa, hKcard, ⟨e'⟩⟩ := suzukiModel_of_equiv_sz hn e
  rw [hfa] at hKcard
  have hsimple : IsSimpleGroup ↥L := by
    have := (CFSG.LieType.Ree.suzuki_simple ha hKcard).2.2
    exact e'.isSimpleGroup
  have hnonab : ∃ x y : ↥L, x * y ≠ y * x := by
    by_contra hcomm
    push Not at hcomm
    exact not_isSolvable_of_mem_cComp hL (Group.isSolvable_of_comm hcomm)
  exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1,
    A3.subnormal_top_iff.mp (subnormal_of_mem_cComp hL)⟩

end Basic

section Compat

variable {Q : Type} [Group Q] [Finite Q]

theorem conjSub_inf_eq_inf_conjSub {T Hh L : Subgroup Q}
    (hT : IsSylowTwoOf T ⊤) (hTH : T ≤ Hh) (hHs : Group.IsSolvable ↥Hh)
    (hL : L ∈ cComp (⊤ : Subgroup Q)) (hSz : IsSzSub L) {h : Q} (hh : h ∈ Hh) :
    conjSub h (T ⊓ L) = T ⊓ conjSub h L := by
  have hL' : conjSub h L ∈ cComp (⊤ : Subgroup Q) :=
    conjSub_mem_cComp_of_mem hL (Subgroup.mem_top h)
  obtain ⟨n, hn, ⟨e⟩⟩ := isSzSub_conjSub hSz h
  have hSyl : IsSylowTwoOf (T ⊓ conjSub h L) (conjSub h L) :=
    zm_isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hL') hT
  have hSyl0 : IsSylowTwoOf (T ⊓ L) L :=
    zm_isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hL) hT
  have hR : IsSylowTwoOf (conjSub h (T ⊓ L)) (conjSub h L) := isSylowTwoOf_conj hSyl0 h
  have hAs : Group.IsSolvable ↥(Hh ⊓ conjSub h L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : Hh ⊓ conjSub h L ≤ Hh))
      (Subgroup.inclusion_injective _)
  have hSA : T ⊓ conjSub h L ≤ Hh ⊓ conjSub h L := inf_le_inf_right _ hTH
  have hnorm : Hh ⊓ conjSub h L ≤ Subgroup.normalizer ((T ⊓ conjSub h L : Subgroup Q) : Set Q) :=
    SzQ.le_normalizer_of_solvable_ambient hn e hSyl hSA inf_le_right hAs
  have hRA : conjSub h (T ⊓ L) ≤ Hh ⊓ conjSub h L := by
    refine le_inf ?_ hR.1
    intro x hx
    have h1 : h⁻¹ * x * h ∈ Hh := hTH (mem_conjSub.mp hx).1
    have h2 := Hh.mul_mem (Hh.mul_mem hh h1) (Hh.inv_mem hh)
    have h3 : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rwa [h3] at h2
  have hSylA : IsSylowTwoOf (T ⊓ conjSub h L) (Hh ⊓ conjSub h L) :=
    F7.isSylowTwoOf_mono_right hSyl hSA inf_le_right
  obtain ⟨x, hxA, hle⟩ := F7.isSylowTwoOf_exists_conj_le hSylA hRA hR.2.1
  rw [F7.conjSub_eq_of_mem_normalizer (hnorm hxA)] at hle
  exact isSylowTwoOf_eq_of_le hR hSyl hle

theorem conjSub_borOf_of_mem {T Hh L : Subgroup Q}
    (hT : IsSylowTwoOf T ⊤) (hTH : T ≤ Hh) (hHs : Group.IsSolvable ↥Hh)
    (hL : L ∈ cComp (⊤ : Subgroup Q)) (hSz : IsSzSub L) {h : Q} (hh : h ∈ Hh) :
    conjSub h (borOf T L) = borOf T (conjSub h L) := by
  unfold borOf
  rw [conjSub_inf, ← conjSub_normalizer, conjSub_inf_eq_inf_conjSub hT hTH hHs hL hSz hh]

end Compat

section Main

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_solvable_normalized_of_suzuki_orbit
    {T Hh J : Subgroup Q} (hT : IsSylowTwoOf T ⊤) (hTH : T ≤ Hh)
    (hHs : Group.IsSolvable ↥Hh) (hJ : J ∈ cComp (⊤ : Subgroup Q)) (hSz : IsSzSub J) :
    ∃ B : Subgroup Q, Group.IsSolvable ↥B ∧ Hh ≤ Subgroup.normalizer (B : Set Q) ∧
      ∃ ℓ : ℕ, ℓ.Prime ∧ 7 ≤ ℓ ∧ ℓ ∣ Nat.card ↥B := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  set 𝒥 : Finset (Subgroup Q) :=
    ((Finset.univ : Finset Q).filter fun t => t ∈ Hh).image fun t => conjSub t J with h𝒥def
  have h𝒥 : ∀ L ∈ 𝒥, ∃ t ∈ Hh, L = conjSub t J := fun L hL => by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hL
    exact ⟨t, (Finset.mem_filter.mp ht).2, rfl⟩
  have h𝒥c : ∀ L ∈ 𝒥, L ∈ cComp (⊤ : Subgroup Q) := fun L hL => by
    obtain ⟨t, -, rfl⟩ := h𝒥 L hL
    exact conjSub_mem_cComp_of_mem hJ (Subgroup.mem_top t)
  have h𝒥S : ∀ L ∈ 𝒥, IsSzSub L := fun L hL => by
    obtain ⟨t, -, rfl⟩ := h𝒥 L hL
    exact isSzSub_conjSub hSz t
  have h𝒥H : ∀ L ∈ 𝒥, ∀ s ∈ Hh, conjSub s L ∈ 𝒥 := fun L hL s hs => by
    obtain ⟨t, ht, rfl⟩ := h𝒥 L hL
    rw [← conjSub_mul]
    exact Finset.mem_image.mpr
      ⟨s * t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Hh.mul_mem hs ht⟩, rfl⟩
  have hJ𝒥 : J ∈ 𝒥 :=
    Finset.mem_image.mpr ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Hh.one_mem⟩, conjSub_one J⟩
  set B : Subgroup Q := 𝒥.sup (borOf T) with hB
  have hbor_le : ∀ L ∈ 𝒥, borOf T L ≤ B := fun L hL => Finset.le_sup (f := borOf T) hL
  have hborL : ∀ L, borOf T L ≤ L := fun L => inf_le_right
  have hsuz : ∀ L ∈ 𝒥, Group.IsSolvable ↥(borOf T L) ∧
      ∃ ℓ : ℕ, ℓ.Prime ∧ 7 ≤ ℓ ∧ ℓ ∣ Nat.card ↥(borOf T L) := fun L hL => by
    obtain ⟨n, hn, ⟨e⟩⟩ := h𝒥S L hL
    exact borOf_suzuki_seven hT (subnormal_of_mem_cComp (h𝒥c L hL))
      (suzukiModel_of_equiv_sz hn e)
  have hcomm : ∀ L ∈ 𝒥, ∀ L' ∈ 𝒥, L ≠ L' →
      ∀ x ∈ borOf T L, ∀ y ∈ borOf T L', x * y = y * x := by
    intro L hL L' hL' hne x hx y hy
    have h1 : ⁅L, L'⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute
        (isComponent_of_cComp_suzuki (h𝒥c L hL) (h𝒥S L hL))
        (isComponent_of_cComp_suzuki (h𝒥c L' hL') (h𝒥S L' hL'))).resolve_left hne
    have h2 : ⁅x, y⁆ ∈ ⁅L, L'⁆ :=
      Subgroup.commutator_mem_commutator (hborL L hx) (hborL L' hy)
    rw [h1, Subgroup.mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hBs : Group.IsSolvable ↥B :=
    isSolvable_finset_sup_of_commute 𝒥 (borOf T) (fun L hL => (hsuz L hL).1)
      (fun L hL L' hL' hne x hx y hy => hcomm L hL L' hL' hne x hx y hy)
  have hBconj : ∀ t ∈ Hh, B ≤ conjSub t⁻¹ B := by
    intro t ht
    refine Finset.sup_le fun L hL => ?_
    rw [le_conjSub_iff, inv_inv,
      conjSub_borOf_of_mem hT hTH hHs (h𝒥c L hL) (h𝒥S L hL) ht]
    exact hbor_le _ (h𝒥H L hL t ht)
  have hBeq : ∀ t ∈ Hh, conjSub t B = B := by
    intro t ht
    refine le_antisymm ((conjSub_le_iff t).mpr (hBconj t ht)) ?_
    have := hBconj t⁻¹ (Hh.inv_mem ht)
    rwa [inv_inv] at this
  have hHn : Hh ≤ Subgroup.normalizer (B : Set Q) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hBeq t ht]
      exact mul_mem_conjSub hh
    · intro hh
      have := mul_mem_conjSub (g := t⁻¹) hh
      rw [hBeq t⁻¹ (Hh.inv_mem ht)] at this
      have e : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
      rwa [e] at this
  obtain ⟨ℓ, hℓ, h7, hd⟩ := (hsuz J hJ𝒥).2
  exact ⟨B, hBs, hHn, ℓ, hℓ, h7, hd.trans (Subgroup.card_dvd_of_le (hbor_le J hJ𝒥))⟩

end Main

end CFSG.Quasithin.S146zT
