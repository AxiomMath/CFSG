module

public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin.H13.NQCat.LieCartan

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def TorusConcl (S : Type) [Group S] (alt : Prop) : Prop :=
  ∀ P Y E : Subgroup S, IsSylowTwoOf P ⊤ → Y ≤ Subgroup.normalizer (P : Set S) →
    Odd (Nat.card Y) → Nat.card Y * Nat.card P = Nat.card (Subgroup.normalizer (P : Set S)) →
    E ≤ P → IsElemAbelian 2 E → Nat.card E = 16 → E ≤ Subgroup.centralizer (P : Set S) →
      (∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) ∧
      3 < (Y ⊓ Subgroup.centralizer (E : Set S)).relIndex Y ∧
      (Y ⊓ Subgroup.centralizer (E : Set S) = ⊥ → alt)

section Equiv

variable {S T : Type} [Group S] [Group T]

theorem isElemAbelian_map {E : Subgroup S} (hE : IsElemAbelian 2 E) (f : S →* T) :
    IsElemAbelian 2 (E.map f) := CFSG.SectionRank.isElemAbelian_map hE _

theorem centralizer_map_equiv (e : S ≃* T) (A : Subgroup S) :
    Subgroup.centralizer ((A.map e.toMonoidHom : Subgroup T) : Set T) =
      (Subgroup.centralizer (A : Set S)).map e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    have h1 := h (e a) ⟨a, ha, rfl⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h1
  · rintro h _ ⟨a, ha, rfl⟩
    have h1 := congrArg e (h a ha)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    exact h1

theorem isSylowTwoOf_top_map_equiv (e : S ≃* T) {P : Subgroup S} (hP : IsSylowTwoOf P ⊤) :
    IsSylowTwoOf (P.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hP.2.1.map _, ?_⟩
  have h1 := hP.2.2
  rw [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at h1
  rw [show ((P.map e.toMonoidHom).subgroupOf ⊤).index = (P.map e.toMonoidHom).index from
    Subgroup.relIndex_top_right _, MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
  exact h1

theorem TorusConcl.of_mulEquiv {alt : Prop} (e : S ≃* T) (h : TorusConcl T alt) :
    TorusConcl S alt := by
  intro P Y E hP hYN hYodd hYcard hEP hE hEcard hEZ
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hN : Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup T) : Set T) =
      (Subgroup.normalizer (P : Set S)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq P e).symm
  have hcY : Nat.card (Y.map e.toMonoidHom) = Nat.card Y :=
    Subgroup.card_map_of_injective hinj
  obtain ⟨h1, h2, h3⟩ := h (P.map e.toMonoidHom) (Y.map e.toMonoidHom) (E.map e.toMonoidHom)
    (isSylowTwoOf_top_map_equiv e hP) (hN ▸ Subgroup.map_mono hYN) (hcY ▸ hYodd)
    (by rw [hN, hcY, Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective hinj,
      hYcard])
    (Subgroup.map_mono hEP) (isElemAbelian_map hE _)
    (by rw [Subgroup.card_map_of_injective hinj, hEcard])
    (by rw [centralizer_map_equiv]; exact Subgroup.map_mono hEZ)
  have hC : Y.map e.toMonoidHom ⊓ Subgroup.centralizer
      ((E.map e.toMonoidHom : Subgroup T) : Set T) =
      (Y ⊓ Subgroup.centralizer (E : Set S)).map e.toMonoidHom := by
    rw [centralizer_map_equiv, Subgroup.map_inf_eq _ _ _ hinj]
  refine ⟨fun a ha b hb => e.injective ?_, ?_, fun h0 => h3 ?_⟩
  · rw [map_mul, map_mul]
    exact h1 (e a) ⟨a, ha, rfl⟩ (e b) ⟨b, hb, rfl⟩
  · rw [hC, Subgroup.relIndex_map_map_of_injective _ _ hinj] at h2
    exact h2
  · rw [hC, h0, Subgroup.map_bot]

end Equiv

section Torus

variable {S : Type} [Group S]

abbrev cj (c : S) : S →* S := (MulAut.conj c).toMonoidHom

theorem cj_comp (c d : S) : (cj c).comp (cj d) = cj (c * d) := by
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

theorem map_cj_cj_inv (A : Subgroup S) (c : S) : (A.map (cj c)).map (cj c⁻¹) = A := by
  rw [Subgroup.map_map, cj_comp, inv_mul_cancel]
  ext x
  simp

theorem map_cj_of_mem {A : Subgroup S} {c : S} (hc : c ∈ A) : A.map (cj c) = A :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hc)

theorem inf_eq_bot_of_two_odd [Finite S] {A B : Subgroup S} (hA : IsPGroup 2 A)
    (hB : Odd (Nat.card B)) : A ⊓ B = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hn]
  exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hB)

theorem card_mul_of_le_sup [Finite S] {A B N : Subgroup S} (hAN : A ≤ N) (hBN : B ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (A : Set S)) (hA : IsPGroup 2 A) (hB : Odd (Nat.card B))
    (hsup : N ≤ A ⊔ B) : Nat.card A * Nat.card B = Nat.card N := by
  have hAn : (A.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAN).2 hnorm
  have htop : A.subgroupOf N ⊔ B.subgroupOf N = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have h1 : (⟨x, hx⟩ : N) ∈ (A ⊔ B).subgroupOf N := Subgroup.mem_subgroupOf.2 (hsup hx)
    rwa [Subgroup.subgroupOf_sup hAN hBN] at h1
  have hdisj : Disjoint (A.subgroupOf N) (B.subgroupOf N) := by
    rw [Subgroup.disjoint_def]
    intro x hxA hxB
    have h1 : (x : S) ∈ A ⊓ B := ⟨hxA, hxB⟩
    rw [inf_eq_bot_of_two_odd hA hB, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hmul : (A.subgroupOf N : Set N) * (B.subgroupOf N : Set N) = Set.univ := by
    rw [← Subgroup.normal_mul, htop, Subgroup.coe_top]
  have hc := (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul).card_mul_card
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv] at hc

theorem exists_conj_of_complement [Finite S] {U H Y : Subgroup S} (hU2 : IsPGroup 2 U)
    (hHN : H ≤ Subgroup.normalizer (U : Set S))
    (hNH : Subgroup.normalizer (U : Set S) ≤ U ⊔ H) (hodd : Odd (Nat.card H)) (g : S)
    (hYN : Y ≤ Subgroup.normalizer ((U.map (cj g) : Subgroup S) : Set S))
    (hYodd : Odd (Nat.card Y))
    (hYcard : Nat.card Y * Nat.card (U.map (cj g)) =
      Nat.card (Subgroup.normalizer ((U.map (cj g) : Subgroup S) : Set S))) :
    ∃ c : S, U.map (cj g) = U.map (cj c) ∧ Y = H.map (cj c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := U.map (cj g) with hPdef
  set N := Subgroup.normalizer (P : Set S) with hNdef
  have hNmap : N = (Subgroup.normalizer (U : Set S)).map (cj g) :=
    (Subgroup.map_equiv_normalizer_eq U (MulAut.conj g)).symm
  set H' := H.map (cj g) with hH'def
  have hinj : Function.Injective (cj g) := (MulAut.conj g).injective
  have hH'N : H' ≤ N := by rw [hNmap]; exact Subgroup.map_mono hHN
  have hNH' : N ≤ P ⊔ H' := by
    rw [hNmap, hPdef, hH'def, ← Subgroup.map_sup]
    exact Subgroup.map_mono hNH
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hP2 : IsPGroup 2 P := hU2.map _
  have hH'odd : Odd (Nat.card H') := by rwa [Subgroup.card_map_of_injective hinj]
  have hcH' : Nat.card P * Nat.card H' = Nat.card N :=
    card_mul_of_le_sup hPN hH'N le_rfl hP2 hH'odd hNH'
  set P₀ := P.subgroupOf N with hP₀
  set Y₀ := Y.subgroupOf N with hY₀
  set H₀ := H'.subgroupOf N with hH₀
  have hP₀n : P₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).2 le_rfl
  have cP : Nat.card P₀ = Nat.card P := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
  have cY : Nat.card Y₀ = Nat.card Y := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv
  have cH : Nat.card H₀ = Nat.card H' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH'N).toEquiv
  have hdisj : ∀ {A : Subgroup S}, Odd (Nat.card A) → Disjoint P₀ (A.subgroupOf N) := by
    intro A hA
    rw [Subgroup.disjoint_def]
    intro x hxP hxA
    have h1 : (x : S) ∈ P ⊓ A := ⟨hxP, hxA⟩
    rw [inf_eq_bot_of_two_odd hP2 hA, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hcY : Subgroup.IsComplement' P₀ Y₀ :=
    Subgroup.isComplement'_of_card_mul_and_disjoint (by rw [cP, cY, mul_comm, hYcard])
      (hdisj hYodd)
  have hcH : Subgroup.IsComplement' P₀ H₀ :=
    Subgroup.isComplement'_of_card_mul_and_disjoint (by rw [cP, cH, hcH'])
      (hdisj hH'odd)
  have hsolv : Group.IsSolvable P₀ := by
    have : Group.IsNilpotent P₀ :=
      (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm).isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card P₀) P₀.index := by
    have h1 := Subgroup.card_mul_index P₀
    have h2 : P₀.index = Nat.card Y := by
      have hpos : 0 < Nat.card P := Nat.card_pos
      have h3 : Nat.card P * P₀.index = Nat.card P * Nat.card Y := by
        rw [← cP, h1, cP, mul_comm, hYcard]
      exact Nat.eq_of_mul_eq_mul_left hpos h3
    obtain ⟨n, hn⟩ := (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm).exists_card_eq
    rw [h2, hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hYodd)
  obtain ⟨n, hnP, hn⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy P₀ hsolv
    hcop hcH.mul_eq hcY.mul_eq (disjoint_iff.mp hcH.disjoint) (disjoint_iff.mp hcY.disjoint)
  have hsub : (N.subtype).comp (MulAut.conj n⁻¹).toMonoidHom = (cj (n : S)⁻¹).comp N.subtype := by
    ext x
    simp
  have hY : Y = H'.map (cj (n : S)⁻¹) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hYN, ← hY₀, hn, Subgroup.map_map, hsub,
      ← Subgroup.map_map, hH₀, Subgroup.map_subgroupOf_eq_of_le hH'N]
  refine ⟨(n : S)⁻¹ * g, ?_, ?_⟩
  · rw [← cj_comp, ← Subgroup.map_map, ← hPdef,
      map_cj_of_mem (inv_mem (show (n : S) ∈ P from hnP))]
  · rw [hY, hH'def, Subgroup.map_map, cj_comp]

theorem torusConcl_of_torus [Finite S] {U H : Subgroup S} {alt : Prop}
    (hU : IsSylowTwoOf U ⊤) (hHN : H ≤ Subgroup.normalizer (U : Set S))
    (hNH : Subgroup.normalizer (U : Set S) ≤ U ⊔ H) (hodd : Odd (Nat.card H))
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (h : ∀ E : Subgroup S, E ≤ U → IsElemAbelian 2 E → Nat.card E = 16 →
      E ≤ Subgroup.centralizer (U : Set S) →
      3 < (H ⊓ Subgroup.centralizer (E : Set S)).relIndex H ∧
        (H ⊓ Subgroup.centralizer (E : Set S) = ⊥ → alt)) :
    TorusConcl S alt := by
  intro P Y E hP hYN hYodd hYcard hEP hE hEcard hEZ
  obtain ⟨g, -, rfl⟩ := hU.exists_conj hP
  obtain ⟨c, hPc, rfl⟩ := exists_conj_of_complement hU.2.1 hHN hNH hodd g hYN hYodd hYcard
  rw [hPc] at hEP hEZ
  have hinj : Function.Injective (cj c) := (MulAut.conj c).injective
  have hinj' : Function.Injective (cj c⁻¹) := (MulAut.conj c⁻¹).injective
  set E' := E.map (cj c⁻¹) with hE'
  have hEE' : E = E'.map (cj c) := by
    rw [hE', Subgroup.map_map, cj_comp, mul_inv_cancel]
    ext x
    simp
  have hCE : Subgroup.centralizer ((E : Subgroup S) : Set S) =
      (Subgroup.centralizer (E' : Set S)).map (cj c) := by
    rw [hEE']
    exact centralizer_map_equiv (MulAut.conj c) E'
  obtain ⟨h1, h2⟩ := h E' (by rw [hE', ← map_cj_cj_inv U c]; exact Subgroup.map_mono hEP)
    (isElemAbelian_map hE _) (by rw [Subgroup.card_map_of_injective hinj', hEcard])
    (by
      rw [← map_cj_cj_inv U c, centralizer_map_equiv (MulAut.conj c⁻¹), hE']
      exact Subgroup.map_mono hEZ)
  have hYC : H.map (cj c) ⊓ Subgroup.centralizer ((E : Subgroup S) : Set S) =
      (H ⊓ Subgroup.centralizer (E' : Set S)).map (cj c) := by
    rw [hCE, Subgroup.map_inf_eq _ _ _ hinj]
  refine ⟨?_, ?_, fun h0 => h2 ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rw [hYC, Subgroup.relIndex_map_map_of_injective _ _ hinj]
    exact h1
  · rw [hYC] at h0
    exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h0

end Torus

end CFSG.Quasithin.H13.NQCat.LieCartan
