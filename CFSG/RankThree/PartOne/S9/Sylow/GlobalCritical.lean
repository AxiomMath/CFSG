module

public import CFSG.RankThree.PartOne.S9.Sylow.GlobalBridge
public import CFSG.RankThree.PartOne.S9.StatementsSylow
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores

public section

namespace CFSG.RankThree.PartOne.Sec9B

open CFSG Subgroup CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

structure CritData {G : Type} [Group G] (H A R Q D : Subgroup G) (p q : ℕ) : Prop where
  A_normalizes : A ≤ Subgroup.normalizer (R : Set G)
  comm_eq : ⁅R, A⁆ = R
  not_le_J : ¬ R ≤ inSubgroup (pCore 2) H
  minimal : ∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
    U ≤ inSubgroup (pCore 2) H ∧ U ≤ Subgroup.centralizer (D : Set G)
  sylow : IsSylowOf q Q
    (((pCore q (↥H ⧸ pCore 2 ↥H)).comap (QuotientGroup.mk' (pCore 2 ↥H))).map H.subtype)
  R_normalizes_Q : R ≤ Subgroup.normalizer (Q : Set G)
  A_normalizes_Q : A ≤ Subgroup.normalizer (Q : Set G)
  D_le_Q : D ≤ Q
  D_char : (D.subgroupOf Q).Characteristic
  D_ne_bot : D ≠ ⊥
  comm_D_ne : ⁅R, D⁆ ≠ ⊥
  D_exp : ∀ d ∈ D, d ^ q = 1
  comm_D_Q : ⁅D, Q⁆ ≤ D ⊓ Subgroup.centralizer (D : Set G)
  card_B : Nat.card ↥(A ⊓ Subgroup.centralizer (R : Set G)) = p ^ 2
  normal_le : ∀ C : Subgroup G, C ≤ A → (C.subgroupOf H).Normal →
    C ≤ A ⊓ Subgroup.centralizer (R : Set G)

section Transport

variable {G : Type} [Group G]

theorem critData_of_abstract (H : Subgroup G) {p q : ℕ} {A' R' Q' D' : Subgroup ↥H}
    (hAR : A' ≤ Subgroup.normalizer (R' : Set ↥H)) (hRA : ⁅R', A'⁆ = R')
    (hRJ : ¬ R' ≤ pCore 2 ↥H)
    (hmin : ∀ U : Subgroup ↥H, U < R' → A' ≤ Subgroup.normalizer (U : Set ↥H) → ⁅U, A'⁆ = U →
      U ≤ pCore 2 ↥H ∧ U ≤ Subgroup.centralizer (D' : Set ↥H))
    (hQ : IsSylowOf q Q' ((pCore q (↥H ⧸ pCore 2 ↥H)).comap (QuotientGroup.mk' (pCore 2 ↥H))))
    (hRQ : R' ≤ Subgroup.normalizer (Q' : Set ↥H)) (hAQ : A' ≤ Subgroup.normalizer (Q' : Set ↥H))
    (hDQ : D' ≤ Q') (hDc : (D'.subgroupOf Q').Characteristic) (hD1 : D' ≠ ⊥)
    (hRD : ⁅R', D'⁆ ≠ ⊥) (hDe : ∀ d ∈ D', d ^ q = 1)
    (hDZ : ⁅D', Q'⁆ ≤ D' ⊓ Subgroup.centralizer (D' : Set ↥H))
    (hB : Nat.card ↥(A' ⊓ Subgroup.centralizer (R' : Set ↥H)) = p ^ 2)
    (hC : ∀ C : Subgroup ↥H, C ≤ A' → C.Normal → C ≤ A' ⊓ Subgroup.centralizer (R' : Set ↥H)) :
    CritData H (A'.map H.subtype) (R'.map H.subtype) (Q'.map H.subtype) (D'.map H.subtype) p q := by
  have hι := H.subtype_injective
  have hle : ∀ K : Subgroup ↥H, K.map H.subtype ≤ H := fun K => Subgroup.map_subtype_le K
  refine
    { A_normalizes := (map_le_normalizer_map_iff hι).mpr hAR
      comm_eq := by rw [← Subgroup.map_commutator, hRA]
      not_le_J := fun h => hRJ ((Subgroup.map_le_map_iff_of_injective hι).mp h)
      minimal := ?_
      sylow := isSylowOf_map hι hQ
      R_normalizes_Q := (map_le_normalizer_map_iff hι).mpr hRQ
      A_normalizes_Q := (map_le_normalizer_map_iff hι).mpr hAQ
      D_le_Q := Subgroup.map_mono hDQ
      D_char := ?_
      D_ne_bot := fun h => hD1 ((Subgroup.map_eq_bot_iff_of_injective _ hι).mp h)
      comm_D_ne := fun h => hRD (by
        apply Subgroup.map_injective hι
        rw [Subgroup.map_commutator, h, Subgroup.map_bot])
      D_exp := (forall_pow_eq_one_map_iff hι).mpr hDe
      comm_D_Q := ?_
      card_B := by
        rw [← map_inf_centralizer_map hι, Subgroup.card_map_of_injective hι]
        exact hB
      normal_le := ?_ }
  ·
    intro U hUR hAU hUA
    have hUH : U ≤ H := hUR.le.trans (hle R')
    set U' := U.subgroupOf H with hU'
    have hUmap : U'.map H.subtype = U := by
      rw [hU', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUH]
    have hU'R : U' < R' := by
      rw [← Subgroup.map_lt_map_iff_of_injective hι, hUmap]
      exact hUR
    have hAU' : A' ≤ Subgroup.normalizer (U' : Set ↥H) := by
      rw [← map_le_normalizer_map_iff hι, hUmap]
      exact hAU
    have hUA' : ⁅U', A'⁆ = U' := by
      apply Subgroup.map_injective hι
      rw [Subgroup.map_commutator, hUmap, hUA]
    obtain ⟨h1, h2⟩ := hmin U' hU'R hAU' hUA'
    refine ⟨?_, ?_⟩
    · rw [← hUmap]
      exact Subgroup.map_mono h1
    · rw [← hUmap]
      exact (map_le_centralizer_map_iff hι).mpr h2
  ·
    set e := Q'.equivMapOfInjective H.subtype hι with he
    have h1 : ∀ x : ↥(Q'.map H.subtype), H.subtype ((e.symm x : Q') : ↥H) = (x : G) := by
      intro x
      have := Subgroup.coe_equivMapOfInjective_apply Q' H.subtype hι (e.symm x)
      rw [← he, e.apply_symm_apply] at this
      exact this.symm
    have heq : (D'.map H.subtype).subgroupOf (Q'.map H.subtype) =
        (D'.subgroupOf Q').map e.toMonoidHom := by
      ext x
      rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp hx
        have : ((e.symm x : Q') : ↥H) = d := hι (by rw [h1 x, ← hdx])
        rw [this]
        exact hd
      · intro hx
        rw [← h1 x]
        exact Subgroup.mem_map_of_mem _ hx
    rw [heq]
    exact characteristic_map_mulEquiv e hDc
  ·
    rw [← Subgroup.map_commutator D' Q' H.subtype]
    refine (Subgroup.map_mono hDZ).trans ?_
    rw [map_inf_centralizer_map hι]
  ·
    intro C hCA hCn
    have hCH : C ≤ H := hCA.trans (hle A')
    set C' := C.subgroupOf H with hC'
    have hCmap : C'.map H.subtype = C := by
      rw [hC', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCH]
    have hC'A : C' ≤ A' := by
      rw [← Subgroup.map_le_map_iff_of_injective hι, hCmap]
      exact hCA
    have := Subgroup.map_mono (f := H.subtype) (hC C' hC'A hCn)
    rw [hCmap, map_inf_centralizer_map hι] at this
    exact this

end Transport

section Relative

variable {G : Type} [Group G] [Finite G]

theorem relative_centralizerConstrainedCriticalAction
    (hCCCA : CentralizerConstrainedCriticalAction) (H A : Subgroup G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hAH : A ≤ H) (hA : IsElementaryAbelian p A) (hAcard : Nat.card ↥A = p ^ 3)
    {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1)
    (hS : ⁅inSubgroup (pCore 2) (H ⊓ Subgroup.centralizer ({b} : Set G)), A⁆ ≤
      inSubgroup (aschbacherSolvableCore p) H)
    (hJ : ¬ ⁅inSubgroup (pCore 2) (H ⊓ Subgroup.centralizer ({b} : Set G)), A⁆ ≤
      inSubgroup (pCore 2) H) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ p ∧ ∃ R Q D : Subgroup G,
      R ≤ inSubgroup (pCore 2) (H ⊓ Subgroup.centralizer ({b} : Set G)) ⊓
        inSubgroup (aschbacherSolvableCore p) H ∧
      b ∈ Subgroup.centralizer (R : Set G) ∧ CritData H A R Q D p q := by
  have hι := H.subtype_injective
  have hA' : (A.subgroupOf H).map H.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAH]
  have hbH : b ∈ H := hAH hbA
  set b' : ↥H := ⟨b, hbH⟩ with hb'
  have hV : (inSubgroup (pCore 2) (Subgroup.centralizer ({b'} : Set ↥H))).map H.subtype =
      inSubgroup (pCore 2) (H ⊓ Subgroup.centralizer ({b} : Set G)) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_inSubgroup_pCore_centralizer 2 H b'
  have hS' : ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({b'} : Set ↥H)), A.subgroupOf H⁆ ≤
      aschbacherSolvableCore p ↥H := by
    rw [← Subgroup.map_le_map_iff_of_injective hι, Subgroup.map_commutator, hV, hA']
    exact hS
  have hJ' : ¬ ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({b'} : Set ↥H)), A.subgroupOf H⁆ ≤
      pCore 2 ↥H := by
    rw [← Subgroup.map_le_map_iff_of_injective hι, Subgroup.map_commutator, hV, hA']
    exact hJ
  have hAel : IsElementaryAbelian p ↥(A.subgroupOf H) := by
    rw [← isElementaryAbelian_map_iff hι, hA']
    exact hA
  have hAcard' : Nat.card ↥(A.subgroupOf H) = p ^ 3 := by
    rw [← Subgroup.card_map_of_injective hι, hA']
    exact hAcard
  obtain ⟨q, hq, hq2, hqp, R', Q', D', hR'VS, hAR', hRA', hRJ', hmin', hQ', hRQ', hAQ', hDQ',
    hDc', hD1', hRD', hDe', hDZ', hB', hb'R', hC'⟩ :=
    hCCCA ↥H p hp hp2 (A.subgroupOf H) hAel hAcard' b' (Subgroup.mem_subgroupOf.mpr hbA)
      (fun h => hb1 (congrArg Subtype.val h)) hS' hJ'
  refine ⟨q, hq, hq2, hqp, R'.map H.subtype, Q'.map H.subtype, D'.map H.subtype, ?_, ?_, ?_⟩
  · calc R'.map H.subtype ≤ ((inSubgroup (pCore 2) (Subgroup.centralizer ({b'} : Set ↥H))) ⊓
          aschbacherSolvableCore p ↥H).map H.subtype := Subgroup.map_mono hR'VS
      _ ≤ (inSubgroup (pCore 2) (Subgroup.centralizer ({b'} : Set ↥H))).map H.subtype ⊓
          (aschbacherSolvableCore p ↥H).map H.subtype := Subgroup.map_inf_le _ _ _
      _ = inSubgroup (pCore 2) (H ⊓ Subgroup.centralizer ({b} : Set G)) ⊓
          inSubgroup (aschbacherSolvableCore p) H := by rw [hV]; rfl
  · refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hg
    have := Subgroup.mem_centralizer_iff.mp hb'R' r hr
    exact congrArg Subtype.val this
  · have hcrit := critData_of_abstract H hAR' hRA' hRJ' hmin' hQ' hRQ' hAQ' hDQ' hDc' hD1' hRD'
      hDe' hDZ' hB' hC'
    rwa [hA'] at hcrit

theorem relative_initialCriticalAction (hICA : InitialCriticalAction) (H A T : Subgroup G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hAH : A ≤ H) (hTH : T ≤ H)
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card ↥A = p ^ 3)
    (hT : IsSylowOf 2 T (inSubgroup (aschbacherSolvableCore p) H))
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hJ : ¬ ⁅T, A⁆ ≤ inSubgroup (pCore 2) H) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ p ∧ ∃ R Q D : Subgroup G, R ≤ T ∧ CritData H A R Q D p q := by
  have hι := H.subtype_injective
  have hA' : (A.subgroupOf H).map H.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAH]
  have hT' : (T.subgroupOf H).map H.subtype = T := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTH]
  have hAel : IsElementaryAbelian p ↥(A.subgroupOf H) := by
    rw [← isElementaryAbelian_map_iff hι, hA']
    exact hA
  have hAcard' : Nat.card ↥(A.subgroupOf H) = p ^ 3 := by
    rw [← Subgroup.card_map_of_injective hι, hA']
    exact hAcard
  have hTs : IsSylowOf 2 (T.subgroupOf H) (aschbacherSolvableCore p ↥H) := by
    rw [← isSylowOf_map_iff hι, hT']
    exact hT
  have hAT' : A.subgroupOf H ≤ Subgroup.normalizer (T.subgroupOf H : Set ↥H) := by
    rw [← map_le_normalizer_map_iff hι, hA', hT']
    exact hAT
  have hJ' : ¬ ⁅T.subgroupOf H, A.subgroupOf H⁆ ≤ pCore 2 ↥H := by
    rw [← Subgroup.map_le_map_iff_of_injective hι, Subgroup.map_commutator, hA', hT']
    exact hJ
  obtain ⟨q, hq, hq2, hqp, R', Q', D', hRT', hAR', hRA', hRJ', hmin', hQ', hRQ', hAQ', hDQ',
    hDc', hD1', hRD', hDe', hDZ', hB', hC'⟩ :=
    hICA ↥H p hp hp2 (A.subgroupOf H) (T.subgroupOf H) hAel hAcard' hTs hAT' hJ'
  refine ⟨q, hq, hq2, hqp, R'.map H.subtype, Q'.map H.subtype, D'.map H.subtype, ?_, ?_⟩
  · rw [← hT']
    exact Subgroup.map_mono hRT'
  · have hcrit := critData_of_abstract H hAR' hRA' hRJ' hmin' hQ' hRQ' hAQ' hDQ' hDc' hD1' hRD'
      hDe' hDZ' hB' hC'
    rwa [hA'] at hcrit

end Relative

end CFSG.RankThree.PartOne.Sec9B
