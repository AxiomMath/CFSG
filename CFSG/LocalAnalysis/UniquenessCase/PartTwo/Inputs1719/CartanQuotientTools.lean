module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
public import CFSG.LocalAnalysis.SectionRank.PRank
public import TauCeti.Algebra.Group.NormalizerQuotient.Conjugation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient normalizerQuotientMk normalizerQuotientMk_ker
  normalizerQuotientMk_surjective normalizerQuotientCongr normalizerQuotientEquivMap)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F11 (Omega1p)

theorem normalizerQuotient_equiv_of_complement {Y : Type} [Group Y] {U H : Subgroup Y}
    (hH : H ≤ Subgroup.normalizer (U : Set Y))
    (hUH : ∀ x ∈ U, x ∈ H → x = 1)
    (hB : ∀ g ∈ Subgroup.normalizer (U : Set Y), ∃ u ∈ U, ∃ h ∈ H, g = u * h) :
    Nonempty (normalizerQuotient U ≃* H) := by
  classical
  let N := Subgroup.normalizer (U : Set Y)
  haveI : (U.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  let u : N → U := fun g =>
    ⟨Classical.choose (hB g g.2), (Classical.choose_spec (hB g g.2)).1⟩
  let h : N → H := fun g =>
    ⟨(Classical.choose_spec (hB g g.2)).2.choose,
      (Classical.choose_spec (hB g g.2)).2.choose_spec.1⟩
  have hg_eq : ∀ g : N, (g : Y) = (u g : Y) * (h g : Y) := fun g =>
    (Classical.choose_spec (hB g g.2)).2.choose_spec.2
  have unique : ∀ {u₁ u₂ : Y} {h₁ h₂ : Y}, u₁ ∈ U → u₂ ∈ U → h₁ ∈ H → h₂ ∈ H →
      u₁ * h₁ = u₂ * h₂ → h₁ = h₂ := by
    intro u₁ u₂ h₁ h₂ hu₁ hu₂ hh₁ hh₂ heq
    have hmem : h₂ * h₁⁻¹ ∈ U := by
      have hdecomp : u₂⁻¹ * u₁ = h₂ * h₁⁻¹ := by
        calc u₂⁻¹ * u₁ = u₂⁻¹ * (u₁ * h₁) * h₁⁻¹ := by group
          _ = u₂⁻¹ * (u₂ * h₂) * h₁⁻¹ := by rw [heq]
          _ = h₂ * h₁⁻¹ := by group
      rw [← hdecomp]
      exact U.mul_mem (U.inv_mem hu₂) hu₁
    have hh : h₂ * h₁⁻¹ ∈ H := H.mul_mem hh₂ (H.inv_mem hh₁)
    exact (mul_inv_eq_one.mp (hUH _ hmem hh)).symm
  let f : N →* H :=
    { toFun := h
      map_one' := Subtype.ext (unique (u 1).2 U.one_mem (h 1).2 H.one_mem
        (by simpa using (hg_eq 1).symm))
      map_mul' := fun g g' => by
        have hmem : (h g : Y) * (u g' : Y) * (h g : Y)⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp (hH (h g).2) (u g' : Y)).mp (u g').2
        refine Subtype.ext (unique (u (g * g')).2
          (U.mul_mem (u g).2 hmem) (h (g * g')).2
          (H.mul_mem (h g).2 (h g').2) ?_)
        calc ((u (g * g') : Y) * (h (g * g') : Y)) = (g * g') := (hg_eq (g * g')).symm
          _ = ((u g : Y) * (h g : Y)) * ((u g' : Y) * (h g' : Y)) := by
            rw [hg_eq g, hg_eq g']
          _ = ((u g : Y) * ((h g : Y) * (u g' : Y) * (h g : Y)⁻¹)) *
              ((h g : Y) * (h g' : Y)) := by group }
  have hker : f.ker = U.subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx1 : (h x : Y) = 1 := congrArg Subtype.val hx
      rw [hg_eq x, hx1, mul_one]
      exact (u x).2
    · intro hx
      change h x = 1
      refine Subtype.ext (unique (u x).2 hx (h x).2 H.one_mem ?_)
      rw [hg_eq x]
      simp [hx]
  have hsurj : Function.Surjective f := by
    intro h'
    refine ⟨⟨(h' : Y), hH h'.2⟩, Subtype.ext ?_⟩
    refine unique (u ⟨(h' : Y), hH h'.2⟩).2 U.one_mem
      (h ⟨(h' : Y), hH h'.2⟩).2 h'.2 ?_
    change (u ⟨(h' : Y), hH h'.2⟩ : Y) * (h ⟨(h' : Y), hH h'.2⟩ : Y) = 1 * (h' : Y)
    simpa using (hg_eq ⟨(h' : Y), hH h'.2⟩).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

theorem normalizerQuotient_equiv_of_isSylowTwoOf {Y Y' : Type} [Group Y] [Group Y']
    [Finite Y] [Finite Y'] {S : Subgroup Y} {S' : Subgroup Y'} (e : Y ≃* Y')
    (hS : IsSylowTwoOf S ⊤) (hS' : IsSylowTwoOf S' ⊤) :
    Nonempty (normalizerQuotient S ≃* normalizerQuotient S') := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSidx : ¬ 2 ∣ S.index := by
    rw [← Subgroup.relIndex_top_right (H := S)]
    exact hS.2.2
  have hS'idx : ¬ 2 ∣ S'.index := by
    rw [← Subgroup.relIndex_top_right (H := S')]
    exact hS'.2.2
  let P : Sylow 2 Y := hS.2.1.toSylow hSidx
  let Q : Sylow 2 Y' := hS'.2.1.toSylow hS'idx
  have hP : (P : Subgroup Y) = S := IsPGroup.toSylow_coe hS.2.1 hSidx
  have hQ : (Q : Subgroup Y') = S' := IsPGroup.toSylow_coe hS'.2.1 hS'idx
  let P' : Sylow 2 Y' := P.mapSurjective (f := (e : Y →* Y')) e.surjective
  have hP' : (P' : Subgroup Y') = S.map (e : Y →* Y') := by
    rw [Sylow.coe_mapSurjective (f := (e : Y →* Y')), hP]
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y' P' Q
  have hconj : (S.map (e : Y →* Y')).map (MulAut.conj y).toMonoidHom = S' := by
    have h1 : ((y • P' : Sylow 2 Y') : Subgroup Y') = S' := by rw [hy, hQ]
    have hP'set : ((P' : Sylow 2 Y') : Set Y') =
        ((S.map (e : Y →* Y') : Subgroup Y') : Set Y') := by
      simpa using congrArg (fun R : Subgroup Y' => (R : Set Y')) hP'
    have h2set : ((y • P' : Sylow 2 Y') : Set Y') =
        (((S.map (e : Y →* Y')).map (MulAut.conj y).toMonoidHom : Subgroup Y') : Set Y') := by
      rw [Sylow.coe_smul, hP'set, Subgroup.coe_map]
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    have h2 : ((y • P' : Sylow 2 Y') : Subgroup Y') =
        (S.map (e : Y →* Y')).map (MulAut.conj y).toMonoidHom := by
      apply Subgroup.ext
      intro z
      change z ∈ ((y • P' : Sylow 2 Y') : Set Y') ↔
        z ∈ (((S.map (e : Y →* Y')).map (MulAut.conj y).toMonoidHom : Subgroup Y') : Set Y')
      exact Iff.of_eq (congrArg (fun s : Set Y' => z ∈ s) h2set)
    rw [← h2, h1]
  exact ⟨(normalizerQuotientEquivMap S e).trans
    ((normalizerQuotientEquivMap (S.map (e : Y →* Y')) (MulAut.conj y)).trans
      (normalizerQuotientCongr hconj))⟩

theorem pRank_and_card_Omega1p_of_comm {A : Type} [Group A] [Finite A] {r k : ℕ}
    (hA : ∀ a b : A, a * b = b * a) (hr : r.Prime)
    (hk : Nat.card {a : A // a ^ r = 1} = r ^ k) :
    CFSG.Open.pRank r (⊤ : Subgroup A) = k ∧
      Nat.card (Omega1p r (⊤ : Subgroup A)) = r ^ k := by
  classical
  let T : Subgroup A :=
    { carrier := {a | a ^ r = 1}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have hcomm : Commute a b := hA a b
        rw [hcomm.mul_pow, ha, hb, one_mul]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [inv_pow, ha, inv_one] }
  have hT : Omega1p r (⊤ : Subgroup A) = T := by
    apply le_antisymm
    · rw [Omega1p, Subgroup.closure_le]
      intro x hx
      exact hx.2
    · intro x hx
      exact Subgroup.subset_closure ⟨trivial, hx⟩
  have hcardT : Nat.card T = r ^ k := hk
  have hElemT : IsElemAbelian r T := by
    refine ⟨IsMulCommutative.mk (Std.Commutative.mk ?_), ?_⟩
    · intro a b
      apply Subtype.ext
      exact hA a.1 b.1
    · intro x hx
      exact hx
  have hup : CFSG.Open.pRank r (⊤ : Subgroup A) ≤ k := by
    refine CFSG.SectionRank.pRank_le (G := A) hr.one_lt ?_
    intro E _ hE
    have hET : E ≤ T := by
      intro x hx
      exact hE.2 x hx
    calc Nat.card E ≤ Nat.card T := Subgroup.card_le_of_le hET
      _ = r ^ k := hcardT
  have hlow : k ≤ CFSG.Open.pRank r (⊤ : Subgroup A) := by
    refine CFSG.SectionRank.le_pRank (G := A) hr.one_lt (H := ⊤) (E := T) le_top hElemT ?_
    exact hcardT
  refine ⟨le_antisymm hup hlow, ?_⟩
  rw [hT]
  exact hcardT

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
