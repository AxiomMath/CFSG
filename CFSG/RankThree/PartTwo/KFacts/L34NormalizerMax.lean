module

public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.GH74.KGroups.L34
public import Certificates.Certificate8034

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34Max

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.L34

theorem l34Max_chain_check :
    (QN0.check = true ∧ QN0.orderCertificate = 72) ∧
      (QE0.check = true ∧ QE0.orderCertificate = 9) :=
  ⟨Certificates.certificate8034.1, Certificates.certificate8034.2.1⟩

theorem l34Max_conj_check : normCheck = true ∧ outCheck = true :=
  ⟨Certificates.certificate8034.2.2.1, Certificates.certificate8034.2.2.2.1⟩

theorem l34Max_gen_check : genCheck = true :=
  Certificates.certificate8034.2.2.2.2.1

theorem l34Max_stab_check : stabCheck = true :=
  Certificates.certificate8034.2.2.2.2.2

abbrev P21 : Subgroup (Equiv.Perm (Fin 21)) := QP21.originalSubgroup

abbrev N0 : Subgroup (Equiv.Perm (Fin 21)) := QN0.originalSubgroup

abbrev E0 : Subgroup (Equiv.Perm (Fin 21)) := QE0.originalSubgroup

theorem evalCodes_mem_of (H : Subgroup (Equiv.Perm (Fin 21))) {S : List (Equiv.Perm (Fin 21))}
    (hS : ∀ g ∈ S, g ∈ H) : ∀ w : List ℤ, evalCodes S w ∈ H
  | [] => H.one_mem
  | z :: w => by
    have hget : ∀ k, S.getD k 1 ∈ H := fun k => by
      rw [List.getD_eq_getElem?_getD]
      cases h : S[k]? with
      | none => exact H.one_mem
      | some g => exact hS g (List.mem_of_getElem? h)
    rw [evalCodes]
    refine H.mul_mem ?_ (evalCodes_mem_of H hS w)
    split_ifs
    · exact hget _
    · exact H.inv_mem (hget _)

theorem pa_mem : pa ∈ P21 := by
  rw [P21, QP21_closure]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem pb_mem : pb ∈ P21 := by
  rw [P21, QP21_closure]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem ofPAB_mem (w : List ℤ) : ofPAB w ∈ P21 := by
  rw [ofPAB, tab_eq]
  refine evalCodes_mem_of P21 ?_ w
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact pa_mem
  · exact pb_mem

theorem N0_eq : N0 = Subgroup.closure {n0a, n0b} := by
  rw [N0, QN0, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem E0_eq : E0 = Subgroup.closure {e0a, e0b} := by
  rw [E0, QE0, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem n0a_mem : n0a ∈ N0 := by
  rw [N0_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem n0b_mem : n0b ∈ N0 := by
  rw [N0_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem e0a_mem : e0a ∈ E0 := by
  rw [E0_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem N0_le_P21 : N0 ≤ P21 := by
  rw [N0_eq, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ofPAB_mem _
  · exact ofPAB_mem _

theorem E0_le_P21 : E0 ≤ P21 := by
  rw [E0_eq, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ofPAB_mem _
  · exact ofPAB_mem _

theorem reps_mem {g : Equiv.Perm (Fin 21)} (hg : g ∈ reps) : g ∈ P21 := by
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp hg
  exact ofPAB_mem _

theorem QN0_ok : ValidSchreier QN0 := l34Max_chain_check.1.1

theorem QE0_ok : ValidSchreier QE0 := l34Max_chain_check.2.1

theorem card_N0 : Nat.card N0 = 72 := by
  rw [N0, card_group QN0 QN0_ok, l34Max_chain_check.1.2]

theorem card_E0 : Nat.card E0 = 9 := by
  rw [E0, card_group QE0 QE0_ok, l34Max_chain_check.2.2]

theorem card_P21 : Nat.card P21 = 20160 := by
  rw [P21, card_group QP21 QP21_ok, QP21_valid.2]

theorem N0_le_normalizer :
    N0 ≤ Subgroup.normalizer (E0 : Set (Equiv.Perm (Fin 21))) := by
  have hconj : ∀ n ∈ [n0a, n0b], ∀ e ∈ [e0a, e0b], n * e * n⁻¹ ∈ E0 := by
    intro n hn e he
    rw [mem_iff_sift QE0 QE0_ok]
    have h := l34Max_conj_check.1
    rw [normCheck, List.all_eq_true] at h
    exact List.all_eq_true.mp (h n hn) e he
  rw [N0_eq, Subgroup.closure_le]
  intro n hn
  have hn' : n ∈ [n0a, n0b] := by
    rcases hn with rfl | rfl <;> simp
  rw [SetLike.mem_coe, E0_eq]
  apply CFSG.RankThree.Asc83Table.mem_normalizer_closure_of_conj_mem
  intro s hs
  have hs' : s ∈ [e0a, e0b] := by
    rcases hs with rfl | rfl <;> simp
  rw [← E0_eq]
  exact hconj n hn' s hs'

theorem pa_conj_not_mem : pa * e0a * pa⁻¹ ∉ E0 := by
  intro h
  rw [mem_iff_sift QE0 QE0_ok] at h
  have hout := l34Max_conj_check.2
  rw [outCheck, h] at hout
  exact absurd hout (by decide)

theorem keyF_inv_mul {y h : Equiv.Perm (Fin 21)} (hyh : keyF y = keyF h) :
    keyF (h⁻¹ * y) = U0 := by
  have h1 : keyF (h⁻¹ * y) = (keyF y).image ⇑(h⁻¹) := by
    rw [keyF, keyF, Finset.image_image, Equiv.Perm.coe_mul]
  rw [h1, hyh, keyF, Finset.image_image, ← Equiv.Perm.coe_mul, inv_mul_cancel,
    Equiv.Perm.coe_one, Finset.image_id]

theorem stab_spec
    {y : Equiv.Perm (Fin 21)} (hy : y ∈ P21) :
    (keyF y = U0 → y ∈ N0) ∧
      (keyF y ≠ U0 → ∃ n ∈ N0, ∃ g ∈ reps, keyF y = keyF (n * g)) := by
  have hs : (elemsT QP21).all (fun y => if keyF y = U0 then QN0.sift y 0 else
      targets.contains (keyF y)) = true := l34Max_stab_check
  have h := forall_of_all QP21 QP21_ok hs y hy
  by_cases hk : keyF y = U0
  · rw [ite_eq_left hk] at h
    exact ⟨fun _ => (mem_iff_sift QN0 QN0_ok y).mpr h, fun h' => absurd hk h'⟩
  · rw [ite_eq_right hk, List.contains_iff_mem] at h
    refine ⟨fun h' => absurd h' hk, fun _ => ?_⟩
    obtain ⟨n, hn, h2⟩ := List.mem_flatMap.mp h
    obtain ⟨g, hg, h3⟩ := List.mem_map.mp h2
    exact ⟨n, (mem_elemsT QN0 QN0_ok n).mp hn, g, hg, h3.symm⟩

theorem gen_spec {g : Equiv.Perm (Fin 21)} (hg : g ∈ reps) :
    P21 ≤ Subgroup.closure {n0a, n0b, g} := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hg
  have h := List.all_eq_true.mp l34Max_gen_check d hd
  simp only [Bool.and_eq_true, schreierPermEq_eq_true_iff] at h
  have hS : ∀ x ∈ [n0a, n0b, ofPAB d.1], x ∈ Subgroup.closure {n0a, n0b, ofPAB d.1} := by
    intro x hx
    apply Subgroup.subset_closure
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp
  rw [P21, QP21_closure, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [← h.1]
    exact evalCodes_mem_of _ hS _
  · rw [← h.2]
    exact evalCodes_mem_of _ hS _

theorem maximal_N0
    {Y : Subgroup (Equiv.Perm (Fin 21))} (hNY : N0 ≤ Y) (hYP : Y ≤ P21) : Y = N0 ∨ Y = P21 := by
  by_cases hYN : Y ≤ N0
  · exact Or.inl (le_antisymm hYN hNY)
  right
  refine le_antisymm hYP ?_
  obtain ⟨y, hyY, hyN⟩ := Set.not_subset.mp hYN
  have hyP := hYP hyY
  have hk : keyF y ≠ U0 := fun hk => hyN ((stab_spec hyP).1 hk)
  obtain ⟨n, hn, g, hg, hkey⟩ := (stab_spec hyP).2 hk
  have hzP : (n * g)⁻¹ * y ∈ P21 :=
    P21.mul_mem (P21.inv_mem (P21.mul_mem (N0_le_P21 hn) (reps_mem hg))) hyP
  have hzN : (n * g)⁻¹ * y ∈ N0 := (stab_spec hzP).1 (keyF_inv_mul hkey)
  have hgY : g ∈ Y := by
    have heq : g = n⁻¹ * y * ((n * g)⁻¹ * y)⁻¹ := by group
    rw [heq]
    exact Y.mul_mem (Y.mul_mem (Y.inv_mem (hNY hn)) hyY) (Y.inv_mem (hNY hzN))
  refine (gen_spec hg).trans ?_
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact hNY n0a_mem
  · exact hNY n0b_mem
  · exact hgY

theorem normalizer_E0_inf :
    Subgroup.normalizer (E0 : Set (Equiv.Perm (Fin 21))) ⊓ P21 = N0 := by
  rcases maximal_N0 (le_inf N0_le_normalizer N0_le_P21) inf_le_right with h | h
  · exact h
  · exfalso
    have hpa : pa ∈ Subgroup.normalizer (E0 : Set (Equiv.Perm (Fin 21))) ⊓ P21 := by
      rw [h]
      exact pa_mem
    exact pa_conj_not_mem ((Subgroup.mem_normalizer_iff.mp hpa.1 e0a).mp e0a_mem)

abbrev E0' : Subgroup P21 := E0.subgroupOf P21

abbrev N0' : Subgroup P21 := N0.subgroupOf P21

theorem card_E0' : Nat.card E0' = 9 := by
  rw [E0', Nat.card_congr (Subgroup.subgroupOfEquivOfLe E0_le_P21).toEquiv, card_E0]

theorem card_N0' : Nat.card N0' = 72 := by
  rw [N0', Nat.card_congr (Subgroup.subgroupOfEquivOfLe N0_le_P21).toEquiv, card_N0]

theorem maximal_N0'
    {Y : Subgroup P21} (h : N0' ≤ Y) : Y = N0' ∨ Y = ⊤ := by
  have hle : N0 ≤ Y.map P21.subtype := by
    intro x hx
    exact ⟨⟨x, N0_le_P21 hx⟩, h (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  rcases maximal_N0 hle (Subgroup.map_subtype_le Y) with h1 | h1
  · left
    rw [N0', ← h1]
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  · right
    rw [eq_top_iff]
    intro x _
    have hx : (x : Equiv.Perm (Fin 21)) ∈ Y.map P21.subtype := by
      rw [h1]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← Subtype.ext hyx]

theorem normalizer_E0' :
    Subgroup.normalizer (E0' : Set P21) = N0' := by
  have h1 : N0' ≤ Subgroup.normalizer (E0' : Set P21) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hxN := N0_le_normalizer hx
    rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro h
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hxN h
  rcases maximal_N0' h1 with h | h
  · exact h.symm.symm
  · exfalso
    have hpa : (⟨pa, pa_mem⟩ : P21) ∈ Subgroup.normalizer (E0' : Set P21) :=
      h ▸ Subgroup.mem_top _
    have he : (⟨e0a, E0_le_P21 e0a_mem⟩ : P21) ∈ E0' := Subgroup.mem_subgroupOf.mpr e0a_mem
    have h2 := Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hpa _).mp he)
    exact pa_conj_not_mem h2

theorem exists_map_conj_eq_of_card {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    {E E' : Subgroup P} (hE : Nat.card E = p ^ (Nat.card P).factorization p)
    (hE' : Nat.card E' = p ^ (Nat.card P).factorization p) :
    ∃ g : P, E'.map (MulAut.conj g).toMonoidHom = E := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (Sylow.ofCard E' hE') (Sylow.ofCard E hE)
  refine ⟨g, ?_⟩
  have h := congrArg (fun Q : Sylow p P => (Q : Subgroup P)) hg
  simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at h
  rw [← h]
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem exists_mulEquiv_map_eq_E0'
    {X : Type*} [Group X] (ψ : X ≃* P21) {E : Subgroup X} (hE : Nat.card E = 9) :
    ∃ φ : X ≃* P21, E.map φ.toMonoidHom = E0' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ^ (Nat.card P21).factorization 3 = 9 := by
    rw [card_P21, show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rfl
  have hE1 : Nat.card (E.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hE]
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_card (P := P21) (p := 3) (E := E0')
    (E' := E.map ψ.toMonoidHom) (h3.symm ▸ card_E0') (h3.symm ▸ hE1)
  refine ⟨ψ.trans (MulAut.conj g), ?_⟩
  rw [← hg, Subgroup.map_map]
  rfl

theorem card_normalizer_of_mulEquiv
    {X : Type*} [Group X] (ψ : X ≃* P21) {E : Subgroup X} (hE : Nat.card E = 9) :
    Nat.card (Subgroup.normalizer (E : Set X)) = 72 := by
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_eq_E0' ψ hE
  have h := Subgroup.map_equiv_normalizer_eq E φ
  rw [hφ, normalizer_E0'] at h
  rw [← Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, h, card_N0']

theorem eq_normalizer_of_mulEquiv
    {X : Type*} [Group X] (ψ : X ≃* P21) {E Y : Subgroup X} (hE : Nat.card E = 9)
    (hEY : Subgroup.normalizer (E : Set X) ≤ Y) (hY : Y ≠ ⊤) :
    Y = Subgroup.normalizer (E : Set X) := by
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_eq_E0' ψ hE
  have hN : (Subgroup.normalizer (E : Set X)).map φ.toMonoidHom = N0' := by
    rw [Subgroup.map_equiv_normalizer_eq E φ, hφ, normalizer_E0']
  have h1 : N0' ≤ Y.map φ.toMonoidHom := hN ▸ Subgroup.map_mono hEY
  rcases maximal_N0' h1 with h | h
  · exact Subgroup.map_injective (f := φ.toMonoidHom) φ.injective (h.trans hN.symm)
  · exfalso
    apply hY
    rw [← Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective] at h
    exact Subgroup.map_injective (f := φ.toMonoidHom) φ.injective h

theorem nonempty_mulEquiv_P21 :
    Nonempty (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2) ≃* P21) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e4⟩ := equiv_psl_P21
  let e1 := KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)
  let e2 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 2) :=
    QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 _)
  let f : GaloisField 2 2 ≃+* GF4 :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField GF4 2 2 (by norm_num) card_F).symm
  let e3 := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv f (Fin 3)
  exact ⟨e1.trans (e2.trans (e3.trans e4))⟩

theorem card_normalizer_of_card_eq_nine
    {X : Type*} [Group X]
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) {E : Subgroup X}
    (hE : Nat.card E = 9) : Nat.card (Subgroup.normalizer (E : Set X)) = 72 := by
  obtain ⟨e'⟩ := nonempty_mulEquiv_P21
  exact card_normalizer_of_mulEquiv (e.trans e') hE

theorem eq_normalizer_of_normalizer_le
    {X : Type*} [Group X]
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) {E Y : Subgroup X}
    (hE : Nat.card E = 9) (hEY : Subgroup.normalizer (E : Set X) ≤ Y) (hY : Y ≠ ⊤) :
    Y = Subgroup.normalizer (E : Set X) := by
  obtain ⟨e'⟩ := nonempty_mulEquiv_P21
  exact eq_normalizer_of_mulEquiv (e.trans e') hE hEY hY

theorem index_eq_of_normalizer_le
    {X : Type*} [Group X]
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) {E Y : Subgroup X}
    (hE : Nat.card E = 9) (hEY : Subgroup.normalizer (E : Set X) ≤ Y) (hY : Y ≠ ⊤) :
    Y.index = 280 := by
  have hX : Nat.card X = 20160 := by
    rw [Nat.card_congr e.toEquiv, KFacts.L34.card_projSL]
  have hYc : Nat.card Y = 72 := by
    rw [eq_normalizer_of_normalizer_le e hE hEY hY, card_normalizer_of_card_eq_nine e hE]
  have h := Y.card_mul_index
  rw [hX, hYc] at h
  omega

end CFSG.RankThree.PartTwo.KFacts.L34Max
