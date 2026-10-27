module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.CoverCentKit
public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofSixRee

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

open CFSG.RankThree.PartTwo Subgroup
open scoped commutatorElement Pointwise

theorem normal_of_commutator_le {C : Type} [Group C] (E : Subgroup C) (h : ⁅(⊤ : Subgroup C), ⊤⁆ ≤ E) :
    E.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have : ⁅g, n⁆ ∈ E := h (Subgroup.commutator_mem_commutator (mem_top g) (mem_top n))
  have h2 : g * n * g⁻¹ = ⁅g, n⁆ * n := by rw [commutatorElement_def]; group
  rw [h2]; exact E.mul_mem this hn

theorem isSolvable_quotient_of_commutator_le {C : Type} [Group C] (E : Subgroup C) [E.Normal]
    (h : ⁅(⊤ : Subgroup C), ⊤⁆ ≤ E) : Group.IsSolvable (C ⧸ E) := by
  have hc : ∀ a b : C ⧸ E, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rename_i x y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have : ⁅y⁻¹, x⁻¹⁆ ∈ E := h (Subgroup.commutator_mem_commutator (mem_top _) (mem_top _))
    have h2 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by rw [commutatorElement_def]; group
    rw [h2]; exact this
  let _ : CommGroup (C ⧸ E) := { (inferInstance : Group (C ⧸ E)) with mul_comm := hc }
  infer_instance


theorem perfect_of_equiv_alt6 {S : Type*} [Group S] (D : Subgroup S)
    (e : ↥D ≃* alternatingGroup (Fin 6)) : ⁅D, D⁆ = D := by
  have h1 : commutator ↥D = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [show commutator ↥D = ⁅(⊤ : Subgroup ↥D), ⊤⁆ from rfl,
      Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.2 e.surjective]
    exact commutator_alternatingGroup_eq_top (by simp)
  rw [← Subgroup.map_subtype_commutator, h1, Subgroup.map_top, Subgroup.range_subtype]

theorem conj_eq_of_comm {G : Type*} [Group G] {a x : G} (h : a * x = x * a) : a * x * a⁻¹ = x := by
  rw [h]; group

theorem commutator_sup_le_of_central {G : Type*} [Group G] (A E : Subgroup G)
    (hA : ∀ a ∈ A, ∀ f ∈ A ⊔ E, a * f = f * a) : ⁅A ⊔ E, A ⊔ E⁆ ≤ E := by
  have hn : A ≤ Subgroup.normalizer (E : Set G) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [conj_eq_of_comm (hA a ha n (Subgroup.mem_sup_right hn))]; exact hn
    · intro h
      have := conj_eq_of_comm (hA a⁻¹ (A.inv_mem ha) _ (Subgroup.mem_sup_right h))
      have e : a⁻¹ * (a * n * a⁻¹) * a⁻¹⁻¹ = n := by group
      rw [e] at this
      rw [this]; exact h
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right A E hn
  rw [Subgroup.commutator_def, Subgroup.closure_le]
  rintro _ ⟨f, hf, g, hg, rfl⟩
  have hf' : f ∈ (A : Set G) * (E : Set G) := by rw [← hmul]; exact hf
  have hg' : g ∈ (A : Set G) * (E : Set G) := by rw [← hmul]; exact hg
  obtain ⟨a, ha, e, he, rfl⟩ := hf'
  obtain ⟨a', ha', e', he', rfl⟩ := hg'
  have hF : ∀ x ∈ A, x ∈ A ⊔ E := fun x hx => Subgroup.mem_sup_left hx
  have hFE : ∀ x ∈ E, x ∈ A ⊔ E := fun x hx => Subgroup.mem_sup_right hx
  have key : ⁅a * e, a' * e'⁆ = e * e' * e⁻¹ * e'⁻¹ := by
    have h1 : ⁅a * e, a' * e'⁆ = a * (e * a' * e' * e⁻¹) * a⁻¹ * (e'⁻¹ * a'⁻¹) := by
      rw [commutatorElement_def]; group
    have hX : e * a' * e' * e⁻¹ ∈ A ⊔ E :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hFE e he) (hF a' ha'))
        (hFE e' he')) (Subgroup.inv_mem _ (hFE e he))
    rw [h1, conj_eq_of_comm (hA a ha _ hX)]
    have hY : e' * e⁻¹ * e'⁻¹ ∈ A ⊔ E :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hFE e' he') (Subgroup.inv_mem _ (hFE e he)))
        (Subgroup.inv_mem _ (hFE e' he'))
    have h2 : e * a' * e' * e⁻¹ * (e'⁻¹ * a'⁻¹) = e * (a' * (e' * e⁻¹ * e'⁻¹) * a'⁻¹) := by group
    rw [h2, conj_eq_of_comm (hA a' ha' _ hY)]; group
  show _ ∈ E
  rw [key]
  exact E.mul_mem (E.mul_mem (E.mul_mem he he') (E.inv_mem he)) (E.inv_mem he')

theorem not_isSolvable_alt_six : ¬ Group.IsSolvable (alternatingGroup (Fin 6)) := by
  intro h
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hc := (IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin 6))).2 h
  let g1 : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let g2 : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  have hne : g1 * g2 ≠ g2 * g1 := by decide +kernel
  exact hne (hc g1 g2)

theorem not_hasType424_of_alt6_normal {K : Type} [Group K] [Finite K] (C E : Subgroup K)
    (hEC : E ≤ C) [(E.subgroupOf C).Normal] (hq : Group.IsSolvable (↥C ⧸ E.subgroupOf C))
    (eE : ↥E ≃* alternatingGroup (Fin 6)) : ¬ Sec11.KS11Lie2Proof.HasType424 ↥C := by
  let e : ↥(E.subgroupOf C) ≃* alternatingGroup (Fin 6) := (Subgroup.subgroupOfEquivOfLe hEC).trans eE
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥(E.subgroupOf C) := e.isSimpleGroup
  refine Proving.not_hasType424_of_normal_simple (E.subgroupOf C) ?_ hq ?_
  · intro h
    exact not_isSolvable_alt_six (Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective)
  · intro h
    exact Proving.not_isType424_alt_six (Sec11.isType424_of_mulEquiv e.symm h)

theorem not_hasType424_of_alt6_core {K : Type} [Group K] [Finite K] (C E : Subgroup K)
    (hEC : E ≤ C) (hcomm : ⁅C, C⁆ ≤ E) (eE : ↥E ≃* alternatingGroup (Fin 6)) :
    ¬ Sec11.KS11Lie2Proof.HasType424 ↥C := by
  have hle : ⁅(⊤ : Subgroup ↥C), ⊤⁆ ≤ E.subgroupOf C := by
    rw [Subgroup.subgroupOf, ← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator,
      Subgroup.map_top, Subgroup.range_subtype]
    exact hcomm
  have : (E.subgroupOf C).Normal := normal_of_commutator_le _ hle
  exact not_hasType424_of_alt6_normal C E hEC (isSolvable_quotient_of_commutator_le _ hle) eE

theorem alt6_normal_index_nine {G : Type} [Group G] (x : G) (E : Subgroup G)
    (eE : ↥E ≃* alternatingGroup (Fin 6))
    (hEC : E ≤ Subgroup.centralizer ({x} : Set G))
    (hcard : Nat.card (Subgroup.centralizer ({x} : Set G)) = 3240)
    (hmove : ∀ c ∈ Subgroup.centralizer ({x} : Set G), ∀ e ∈ E,
      c * e * c⁻¹ ∈ Subgroup.zpowers x ⊔ E) :
    (E.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal ∧
      Nat.card (↥(Subgroup.centralizer ({x} : Set G)) ⧸
        E.subgroupOf (Subgroup.centralizer ({x} : Set G))) = 9 := by
  set C := Subgroup.centralizer ({x} : Set G) with hC
  set F := Subgroup.zpowers x ⊔ E with hF
  have hxC : x ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have hAC : Subgroup.zpowers x ≤ C := (Subgroup.zpowers_le).2 hxC
  have hFC : F ≤ C := sup_le hAC hEC
  have hcent : ∀ a ∈ Subgroup.zpowers x, ∀ f ∈ F, a * f = f * a := by
    intro a ha f hf
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hxf : x * f = f * x := (Subgroup.mem_centralizer_singleton_iff.1 (hFC hf)).symm
    exact ((Commute.zpow_left hxf n) : Commute (x ^ n) f).eq
  have hFE : ⁅F, F⁆ ≤ E := commutator_sup_le_of_central _ _ hcent
  have hperf : ⁅E, E⁆ = E := perfect_of_equiv_alt6 E eE
  have hnorm : ∀ c ∈ C, ∀ e ∈ E, c * e * c⁻¹ ∈ E := by
    intro c hc e he
    set S : Subgroup G := E.map (MulAut.conj c).toMonoidHom with hS
    have hSF : S ≤ F := by
      rintro _ ⟨e', he', rfl⟩
      exact hmove c hc e' he'
    have hSS : ⁅S, S⁆ = S := by
      rw [hS, ← Subgroup.map_commutator, hperf]
    have hSE : S ≤ E := by
      rw [← hSS]
      exact (Subgroup.commutator_mono hSF hSF).trans hFE
    exact hSE ⟨e, he, rfl⟩
  refine ⟨⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := hnorm (g : G) g.2 (n : G) hn
      simpa using this⟩, ?_⟩
  have hEcard : Nat.card E = 360 := by
    rw [Nat.card_congr eE.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf C)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, hEcard, hcard] at h
  omega

theorem not_hasType424_of_alt6_index_nine {G : Type} [Group G] [Finite G] (x : G) (E : Subgroup G)
    (eE : ↥E ≃* alternatingGroup (Fin 6))
    (hEC : E ≤ Subgroup.centralizer ({x} : Set G))
    (hcard : Nat.card (Subgroup.centralizer ({x} : Set G)) = 3240)
    (hmove : ∀ c ∈ Subgroup.centralizer ({x} : Set G), ∀ e ∈ E,
      c * e * c⁻¹ ∈ Subgroup.zpowers x ⊔ E) :
    ¬ Sec11.KS11Lie2Proof.HasType424 ↥(Subgroup.centralizer ({x} : Set G)) := by
  obtain ⟨hnormal, hq⟩ := alt6_normal_index_nine x E eE hEC hcard hmove
  have := hnormal
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (↥(Subgroup.centralizer ({x} : Set G)) ⧸
      E.subgroupOf (Subgroup.centralizer ({x} : Set G))) :=
    IsPGroup.of_card (n := 2) (by rw [hq]; norm_num)
  have hsol : Group.IsSolvable (↥(Subgroup.centralizer ({x} : Set G)) ⧸
      E.subgroupOf (Subgroup.centralizer ({x} : Set G))) :=
    let _ : Group.IsNilpotent _ := hP.isNilpotent
    inferInstance
  exact not_hasType424_of_alt6_normal _ E hEC hsol eE

theorem transfer_subgroupOf {G : Type} [Group G] (H : Subgroup G) (y : H) (D : Subgroup G)
    (hD1 : D ≤ centralizer ({(y : G)} : Set G) ⊓ H)
    (hD2 : ⁅centralizer ({(y : G)} : Set G) ⊓ H, centralizer ({(y : G)} : Set G) ⊓ H⁆ ≤ D) :
    D.subgroupOf H ≤ centralizer ({y} : Set H) ∧
      ⁅centralizer ({y} : Set H), centralizer ({y} : Set H)⁆ ≤ D.subgroupOf H := by
  have hmap : (centralizer ({y} : Set H)).map H.subtype ≤ centralizer ({(y : G)} : Set G) ⊓ H := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨?_, c.2⟩
    have hc' := mem_centralizer_iff.1 hc y rfl
    show H.subtype c ∈ centralizer ({(y : G)} : Set G)
    refine mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact congrArg Subtype.val hc'
  refine ⟨fun g hg => ?_, ?_⟩
  · have := (hD1 hg).1
    have h2 := mem_centralizer_iff.1 this (y : G) rfl
    refine mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact Subtype.ext h2
  · rw [Subgroup.subgroupOf, ← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator]
    exact (Subgroup.commutator_mono hmap hmap).trans hD2


theorem noType424At3_of_mulEquiv {G H : Type} [Group G] [Finite G] [Group H] (ψ : G ≃* H)
    (h : ∀ y : H, orderOf y = 3 →
      ¬ Sec11.KS11Lie2Proof.HasType424 ↥(Subgroup.centralizer ({y} : Set H))) :
    Coordinator.CoverCent.NoType424At3 G := by
  intro s hs3 hs
  rw [Item424Res2.fixSub_conj_eq_centralizer_singleton] at hs
  exact h (ψ s) (by rw [MulEquiv.orderOf_eq]; exact hs3)
    (hs.of_mulEquiv (Sec4.Res4Seven.centralizerMapEquiv ψ s))

theorem noType424At3_of_conj_class {G : Type} [Group G] [Finite G] (x : G)
    (hconj : ∀ s : G, orderOf s = 3 → ∃ g : G, s = g * x * g⁻¹)
    (h : ¬ Sec11.KS11Lie2Proof.HasType424 ↥(Subgroup.centralizer ({x} : Set G))) :
    Coordinator.CoverCent.NoType424At3 G := by
  intro s hs3 hs
  obtain ⟨g, rfl⟩ := hconj s hs3
  rw [Item424Res2.fixSub_conj_eq_centralizer_singleton] at hs
  exact h (hs.of_mulEquiv
    ((Sec4.Res4Seven.centralizerMapEquiv (MulAut.conj g) x).symm))

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
