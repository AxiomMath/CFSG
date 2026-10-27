module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalLevi
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalDiag
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TableBOrth

section General

variable {G H : Type*} [Group G] [Group H]

@[expose] def IsEndNode (A : Subgroup G) (t : G) : Prop :=
  t ∈ A ∧ t ≠ 1 ∧
    IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({t} : Set G)))
      (Subgroup.centralizer ({t} : Set G)) ∧
    ∀ s ∈ A, ((∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set G)), s * j = j * s) ↔
      s ∈ Subgroup.zpowers t)

theorem IsEndNode.map (φ : G ≃* H) {A : Subgroup G} {t : G} (h : IsEndNode A t) :
    IsEndNode (A.map φ.toMonoidHom) (φ t) := by
  obtain ⟨htA, ht1, hcomp, hcent⟩ := h
  have hC : Subgroup.centralizer ({φ t} : Set H) =
      (Subgroup.centralizer ({t} : Set G)).map φ.toMonoidHom :=
    (TableBSymp.map_centralizer_singleton φ t).symm
  have hL : LargeEvenLayer (Subgroup.centralizer ({φ t} : Set H)) =
      (LargeEvenLayer (Subgroup.centralizer ({t} : Set G))).map φ.toMonoidHom := by
    rw [hC, largeEvenLayer_map_of_injective _ φ.injective]
  refine ⟨⟨t, htA, rfl⟩, fun h1 => ht1 (φ.injective (by rw [h1, map_one])), ?_, ?_⟩
  · rw [hL, hC]
    exact isComponentOf_map_of_injective _ φ.injective hcomp
  · rintro _ ⟨s, hs, rfl⟩
    rw [hL]
    constructor
    · intro hj
      have h1 : ∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set G)), s * j = j * s := by
        intro j hj'
        apply φ.injective
        rw [map_mul, map_mul]
        exact hj _ ⟨j, hj', rfl⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ((hcent s hs).mp h1)
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [← map_zpow, hn]; rfl⟩
    · intro hmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hs' : s ∈ Subgroup.zpowers t := by
        refine Subgroup.mem_zpowers_iff.mpr ⟨n, φ.injective ?_⟩
        rw [map_zpow]
        exact hn
      rintro _ ⟨j, hj, rfl⟩
      have := (hcent s hs).mpr hs' j hj
      change φ s * φ j = φ j * φ s
      rw [← map_mul, ← map_mul, this]

theorem ggEndNodeElt_iff {p r : ℕ} {R : Type} [Group R] :
    GGEndNodeElt p r R ↔ ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A →
      p ^ 3 ≤ Nat.card A → ∃ t, IsEndNode A t := by
  constructor
  · intro h A hA hr h3
    obtain ⟨t, htA, ht1, hc, hs⟩ := h A hA hr h3
    exact ⟨t, htA, ht1, hc, hs⟩
  · intro h A hA hr h3
    obtain ⟨t, htA, ht1, hc, hs⟩ := h A hA hr h3
    exact ⟨t, htA, ht1, hc, hs⟩

theorem ggEndNodeElt_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (φ : R ≃* R')
    (h : GGEndNodeElt p r R) : GGEndNodeElt p r R' := by
  rw [ggEndNodeElt_iff] at h ⊢
  intro A hA hr h3
  have hcard : Nat.card (A.map φ.symm.toMonoidHom) = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ φ.symm.injective).toEquiv).symm
  obtain ⟨t, ht⟩ := h _ (TableB.isElemAbelian_map hA _) (hcard ▸ hr) (hcard ▸ h3)
  refine ⟨φ t, ?_⟩
  have := ht.map φ
  rwa [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id R' from
    MonoidHom.ext fun x => φ.apply_symm_apply x, Subgroup.map_id] at this

end General

section Tools

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

open CFSG.ClassicalGroups.Orthogonal (toLinEquiv statedOmega_eq_comap)

@[expose] noncomputable def omegaEquivOrthDerived (QF : QuadraticForm K (ι → K)) :
    LargeEvenOmega ⇑QF ≃* CFSG.RankThree.Classical2.orthDerived QF :=
  (MulEquiv.subgroupCongr (statedOmega_eq_comap (Q := QF) rfl)).trans
    ((Subgroup.equivMapOfInjective _ (toLinEquiv ι K).toMonoidHom (toLinEquiv ι K).injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective
        (toLinEquiv ι K).surjective _)))

theorem permutationGL_conj_diagGL (π : Equiv.Perm ι) (d : ι → Kˣ) :
    TauCeti.permutationGL (k := K) π * TauCeti.diagGL d * (TauCeti.permutationGL (k := K) π)⁻¹ =
      TauCeti.diagGL (d ∘ ⇑π⁻¹) := by
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix _ π⁻¹ (TauCeti.permutationGL_coe _),
    mul_inv_cancel_right]

theorem map_conj_omega {Q : (ι → K) → K} {g : GL ι K} (hg : g ∈ LargeEvenOrthGroup Q) :
    (LargeEvenOmega Q).map (MulAut.conj g).toMonoidHom = LargeEvenOmega Q := by
  rw [largeEvenOmega_def, Subgroup.map_commutator, TableBSymp.map_conj_eq_self hg]

@[expose] noncomputable def conjOmega {Q : (ι → K) → K} {g : GL ι K}
    (hg : g ∈ LargeEvenOrthGroup Q) : LargeEvenOmega Q ≃* LargeEvenOmega Q :=
  ((MulAut.conj g).subgroupMap (LargeEvenOmega Q)).trans
    (MulEquiv.subgroupCongr (map_conj_omega hg))

theorem coe_conjOmega {Q : (ι → K) → K} {g : GL ι K} (hg : g ∈ LargeEvenOrthGroup Q)
    (x : LargeEvenOmega Q) : ((conjOmega hg x : LargeEvenOmega Q) : GL ι K) = g * x * g⁻¹ :=
  rfl

theorem eq_one_of_eq_inv_of_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {u : Kˣ} (hu : u ^ p = 1)
    (h : u = u⁻¹) : u = 1 :=
  eq_one_of_sq_of_pow_prime hp hp2 (by rw [sq]; nth_rewrite 2 [h]; exact mul_inv_cancel u) hu

end Tools

section Plus

open TableBSymp

variable {K : Type} [Field K]

@[expose] def plusSplit (k : ℕ) : Fin (k + 1) ⊕ Fin (k + 1) ≃ (Fin k ⊕ Fin k) ⊕ (Fin 1 ⊕ Fin 1) :=
  (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans
    (Equiv.sumSumSumComm (Fin k) (Fin 1) (Fin k) (Fin 1))

theorem plusSplit_symm_inl_inl (k : ℕ) (x : Fin k) :
    (plusSplit k).symm (Sum.inl (Sum.inl x)) = Sum.inl (Fin.castSucc x) := by
  simp [plusSplit]
  rfl

theorem plusSplit_symm_inl_inr (k : ℕ) (x : Fin k) :
    (plusSplit k).symm (Sum.inl (Sum.inr x)) = Sum.inr (Fin.castSucc x) := by
  simp [plusSplit]
  rfl

theorem plusSplit_symm_inr_inl (k : ℕ) (a : Fin 1) :
    (plusSplit k).symm (Sum.inr (Sum.inl a)) = Sum.inl (Fin.last k) := by
  rw [Fin.fin_one_eq_zero a]
  simp [plusSplit, Fin.last]
  exact Fin.ext (by simp)

theorem plusSplit_symm_inr_inr (k : ℕ) (a : Fin 1) :
    (plusSplit k).symm (Sum.inr (Sum.inr a)) = Sum.inr (Fin.last k) := by
  rw [Fin.fin_one_eq_zero a]
  simp [plusSplit, Fin.last]
  exact Fin.ext (by simp)

theorem largeEvenQPlus_split (k : ℕ) (v : Fin (k + 1) ⊕ Fin (k + 1) → K) :
    LargeEvenQPlus K (k + 1) v =
      LargeEvenQPlus K k (fun x => v ((plusSplit k).symm (Sum.inl x))) +
        v ((plusSplit k).symm (Sum.inr (Sum.inl 0))) *
          v ((plusSplit k).symm (Sum.inr (Sum.inr 0))) := by
  simp only [largeEvenQPlus_def, plusSplit_symm_inl_inl, plusSplit_symm_inl_inr,
    plusSplit_symm_inr_inl, plusSplit_symm_inr_inr]
  rw [Fin.sum_univ_castSucc]

theorem isPairTorus_plus {k : ℕ} {ζ : Kˣ} (hζ2 : ζ * ζ ≠ 1) :
    IsPairTorus (plusSplit k) (pairedUnits (Pi.mulSingle (Fin.last k) ζ)) ζ where
  rest x := by
    rcases x with x | x
    · rw [plusSplit_symm_inl_inl]
      simp [pairedUnits, Pi.mulSingle_apply, Fin.castSucc_ne_last]
    · rw [plusSplit_symm_inl_inr]
      simp [pairedUnits, Pi.mulSingle_apply, Fin.castSucc_ne_last]
  left := by
    rw [plusSplit_symm_inr_inl]
    simp [pairedUnits]
  right := by
    rw [plusSplit_symm_inr_inr]
    simp [pairedUnits]
  sq_ne_one := hζ2

theorem isQuasisimple_omegaPlus [Finite K] {k : ℕ} (hk : 3 ≤ k) :
    CFSG.IsQuasisimple (LargeEvenOmega (LargeEvenQPlus K k)) := by
  rw [← coe_qPlusForm]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (omegaEquivOrthDerived (qPlusForm K k)).symm
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived (nondegenerate_qPlusForm k)
      (CFSG.ClassicalGroups.Orthogonal.regular_quadPlus hk).2)

end Plus

section Swaps

open TableBSymp

variable {K : Type} [Field K] {m : ℕ}

theorem permutationGL_commutator_pairSwap (i k : Fin m) :
    TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k)) *
        TauCeti.permutationGL (k := K) (pairSwap k) *
        (TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k)))⁻¹ *
        (TauCeti.permutationGL (k := K) (pairSwap k))⁻¹ =
      TauCeti.permutationGL (k := K) (pairSwap i * pairSwap k) := by
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  rw [pairSwap_inv]
  congr 1
  unfold pairSwap
  rw [← Equiv.swap_apply_apply]
  simp

theorem permutationGL_mem_centralizer_diagGL {ι : Type} [Fintype ι] [DecidableEq ι]
    {π : Equiv.Perm ι} {d : ι → Kˣ} (h : d ∘ ⇑π⁻¹ = d) :
    TauCeti.permutationGL (k := K) π ∈
      Subgroup.centralizer ({TauCeti.diagGL d} : Set (GL ι K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := permutationGL_conj_diagGL (K := K) π d
  rw [h] at h1
  calc TauCeti.permutationGL (k := K) π * TauCeti.diagGL d =
      TauCeti.permutationGL (k := K) π * TauCeti.diagGL d *
        (TauCeti.permutationGL (k := K) π)⁻¹ * TauCeti.permutationGL (k := K) π := by group
    _ = TauCeti.diagGL d * TauCeti.permutationGL (k := K) π := by rw [h1]

theorem pairedUnits_comp_sumCongr_inv {u : Fin m → Kˣ} {σ : Equiv.Perm (Fin m)}
    (h : u ∘ ⇑σ⁻¹ = u) : pairedUnits u ∘ ⇑(Equiv.Perm.sumCongr σ σ)⁻¹ = pairedUnits u := by
  funext x
  rw [Equiv.Perm.sumCongr_inv]
  rcases x with i | i
  · simp only [Function.comp_apply, Equiv.Perm.sumCongr_apply, Sum.map_inl, pairedUnits,
      Sum.elim_inl]
    exact congrFun h i
  · simp only [Function.comp_apply, Equiv.Perm.sumCongr_apply, Sum.map_inr, pairedUnits,
      Sum.elim_inr]
    rw [show u (σ⁻¹ i) = u i from congrFun h i]

theorem pairedUnits_comp_pairSwap_inv {u : Fin m → Kˣ} {j : Fin m} (h : u j = 1) :
    pairedUnits u ∘ ⇑(pairSwap j)⁻¹ = pairedUnits u := by
  rw [pairSwap_inv, pairedUnits_comp_pairSwap, h, inv_one]
  congr 1
  exact Function.update_eq_self_iff.mpr h.symm

theorem eq_one_of_commute_pairSwap_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {u : Fin m → Kˣ}
    (hu : ∀ j, u j ^ p = 1) {a b : Fin m} (hab : a ≠ b)
    (h : TauCeti.diagGL (pairedUnits u) * TauCeti.permutationGL (k := K) (pairSwap a * pairSwap b) =
      TauCeti.permutationGL (k := K) (pairSwap a * pairSwap b) * TauCeti.diagGL (pairedUnits u)) :
    u a = 1 := by
  have h1 := pairSwap_mul_conj (K := K) a b u
  rw [← h, mul_inv_cancel_right] at h1
  have h2 := congrFun (TauCeti.diagGL_injective h1) (Sum.inl a)
  simp only [pairedUnits, Sum.elim_inl, Function.update_self,
    Function.update_of_ne hab] at h2
  exact eq_one_of_eq_inv_of_pow hp hp2 (hu a) h2

end Swaps

section PlusEndNode

open TableBSymp

variable {K : Type} [Field K]

theorem diagGL_pairedUnits_mulSingle_pow {k : ℕ} (ζ : Kˣ) (n : ℕ) :
    TauCeti.diagGL (pairedUnits (Pi.mulSingle (Fin.last k) ζ)) ^ n =
      TauCeti.diagGL (pairedUnits (Pi.mulSingle (Fin.last k) (ζ ^ n))) := by
  rw [← pairedHom_apply, ← pairedHom_apply, ← map_pow, ← map_pow, Pi.mulSingle_pow]

theorem exists_pow_eq_mulSingle {k p : ℕ} [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p)
    {u : Fin (k + 1) → Kˣ} (hu : ∀ j, u j ^ p = 1) (h : ∀ j : Fin k, u (Fin.castSucc j) = 1) :
    ∃ n : ℕ, Pi.mulSingle (Fin.last k) (ζ ^ n) = u := by
  have hprim : IsPrimitiveRoot ζ p := hζo ▸ IsPrimitiveRoot.orderOf ζ
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p _).mpr
    (hu (Fin.last k)))
  refine ⟨n, funext fun j => ?_⟩
  induction j using Fin.lastCases with
  | last => rw [Pi.mulSingle_eq_same, hn]
  | cast j => rw [Pi.mulSingle_eq_of_ne (Fin.castSucc_ne_last j), h j]

variable [Finite K] [CharP K 2]

theorem ggEndNodeElt_omegaPlusGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) {k : ℕ} (hk : 3 ≤ k) :
    GGEndNodeElt p (k + 1) (LargeEvenOmega (LargeEvenQPlus K (k + 1))) := by
  rw [ggEndNodeElt_iff]
  intro A hA hr _
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo, hζ, hζ1, hζ2⟩ := exists_zeta (K := K) hp hp2 hpq
  have hAGO : A.map (LargeEvenOmega (LargeEvenQPlus K (k + 1))).subtype ≤
      LargeEvenOrthGroup (LargeEvenQPlus K (k + 1)) :=
    (Subgroup.map_subtype_le A).trans (omega_le_orth _)
  have hAGc : Nat.card (A.map (LargeEvenOmega (LargeEvenQPlus K (k + 1))).subtype) = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm
  have hAGe : IsElemAbelian p (A.map (LargeEvenOmega (LargeEvenQPlus K (k + 1))).subtype) :=
    TableB.isElemAbelian_map hA _
  obtain ⟨g, hgO, χ, hχ, hsurj⟩ := exists_orth_conj_plus hp2 hζo hAGO hAGe (hAGc ▸ hr)
  have hu₀p : ∀ j, (Pi.mulSingle (Fin.last k) ζ : Fin (k + 1) → Kˣ) j ^ p = 1 := fun j => by
    rw [Pi.mulSingle_apply]
    split_ifs
    · exact hζ
    · exact one_pow p
  obtain ⟨x₀, hx₀⟩ := hsurj _ hu₀p
  obtain ⟨a₀, ha₀A, ha₀⟩ := Subgroup.mem_map.mp x₀.2
  have hcA : ∀ (a : LargeEvenOmega (LargeEvenQPlus K (k + 1))) (ha : a ∈ A),
      ((conjOmega hgO a : LargeEvenOmega (LargeEvenQPlus K (k + 1))) :
        GL (Fin (k + 1) ⊕ Fin (k + 1)) K) =
      TauCeti.diagGL (pairedUnits fun j => χ j ⟨(a : GL _ K), Subgroup.mem_map_of_mem _ ha⟩) := by
    intro a ha
    have h1 := hχ ⟨(a : GL _ K), Subgroup.mem_map_of_mem _ ha⟩
    rw [coe_conjOmega]
    rw [← h1]
  set u₀ : Fin (k + 1) → Kˣ := Pi.mulSingle (Fin.last k) ζ with hu₀
  have hPT : IsPairTorus (plusSplit k) (pairedUnits u₀) ζ := isPairTorus_plus hζ2
  have hx₀' : x₀ = ⟨(a₀ : GL _ K), Subgroup.mem_map_of_mem _ ha₀A⟩ := Subtype.ext ha₀.symm
  have hct : ((conjOmega hgO a₀ : LargeEvenOmega (LargeEvenQPlus K (k + 1))) :
      GL (Fin (k + 1) ⊕ Fin (k + 1)) K) = TauCeti.diagGL (pairedUnits u₀) := by
    rw [hcA a₀ ha₀A, ← hx₀']
    congr 2
    funext j
    exact hx₀ j
  suffices hend : IsEndNode (A.map (conjOmega hgO).toMonoidHom) (conjOmega hgO a₀) by
    refine ⟨a₀, ?_⟩
    have h1 := hend.map (conjOmega hgO).symm
    rwa [Subgroup.map_map, show (conjOmega hgO).symm.toMonoidHom.comp (conjOmega hgO).toMonoidHom =
      MonoidHom.id _ from MonoidHom.ext fun x => (conjOmega hgO).symm_apply_apply x,
      Subgroup.map_id, MulEquiv.symm_apply_apply] at h1
  have hmemCent : ∀ y : LargeEvenOmega (LargeEvenQPlus K (k + 1)),
      y ∈ Subgroup.centralizer
        ({conjOmega hgO a₀} : Set (LargeEvenOmega (LargeEvenQPlus K (k + 1))))
        ↔ (y : GL (Fin (k + 1) ⊕ Fin (k + 1)) K) ∈
          Subgroup.centralizer ({TauCeti.diagGL (pairedUnits u₀)} : Set (GL _ K)) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← hct]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  set D : Subgroup (LargeEvenOmega (LargeEvenQPlus K (k + 1))) :=
    ((LargeEvenOmega (LargeEvenQPlus K k)).map (embHom (plusSplit k))).subgroupOf
      (LargeEvenOmega (LargeEvenQPlus K (k + 1))) with hD
  have hDle : D ≤ Subgroup.centralizer
      ({conjOmega hgO a₀} : Set (LargeEvenOmega (LargeEvenQPlus K (k + 1)))) := by
    intro y hy
    rw [hmemCent]
    rw [hD, Subgroup.mem_subgroupOf] at hy
    obtain ⟨h, _, hh⟩ := hy
    rw [← hh]
    exact hPT.embHom_mem_centralizer h
  have hcomm : ∀ a ∈ Subgroup.centralizer
      ({conjOmega hgO a₀} : Set (LargeEvenOmega (LargeEvenQPlus K (k + 1)))),
      ∀ b ∈ Subgroup.centralizer
        ({conjOmega hgO a₀} : Set (LargeEvenOmega (LargeEvenQPlus K (k + 1)))),
      a * b * a⁻¹ * b⁻¹ ∈ D := by
    intro a ha b hb
    rw [hD, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hPT.commutator_mem_map_embHom_omega (largeEvenQPlus_split k) ((hmemCent a).mp ha)
      ((hmemCent b).mp hb) (omega_le_orth _ a.2) (omega_le_orth _ b.2)
  have hq : CFSG.IsQuasisimple D := by
    have e1 : D ≃* ((LargeEvenOmega (LargeEvenQPlus K k)).map (embHom (plusSplit k))) :=
      Subgroup.subgroupOfEquivOfLe (map_embHom_omega_le (largeEvenQPlus_split k))
    have e2 := (LargeEvenOmega (LargeEvenQPlus K k)).equivMapOfInjective _
      (embHom_injective (plusSplit k))
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans e2.symm).symm
      (isQuasisimple_omegaPlus hk)
  obtain ⟨hlay, hcompD⟩ := TableBSymp.largeEvenLayer_eq_of_commutator_mem hDle hcomm hq
  refine ⟨⟨a₀, ha₀A, rfl⟩, ?_, ?_, ?_⟩
  · intro h1
    have h2 := congrArg (fun y : LargeEvenOmega (LargeEvenQPlus K (k + 1)) =>
      ((y : GL (Fin (k + 1) ⊕ Fin (k + 1)) K) :
        Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) K)
        (Sum.inl (Fin.last k)) (Sum.inl (Fin.last k))) h1
    simp only [hct, OneMemClass.coe_one, Units.val_one, Matrix.one_apply_eq, TauCeti.diagGL_coe,
      Matrix.diagonal_apply_eq, pairedUnits, Sum.elim_inl, hu₀, Pi.mulSingle_eq_same] at h2
    exact hζ1 (Units.ext h2)
  · rw [hlay]
    exact hcompD
  · rintro _ ⟨s, hs, rfl⟩
    rw [hlay]
    have hcs := hcA s hs
    set us : Fin (k + 1) → Kˣ :=
      fun j => χ j ⟨(s : GL _ K), Subgroup.mem_map_of_mem _ hs⟩ with hus
    have husp : ∀ j, us j ^ p = 1 := fun j => by
      rw [hus, ← map_pow]
      have h1 : (⟨(s : GL _ K), Subgroup.mem_map_of_mem _ hs⟩ :
          A.map (LargeEvenOmega (LargeEvenQPlus K (k + 1))).subtype) ^ p = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val (hA.2 s hs))
      rw [h1, map_one]
    constructor
    · intro hcomm'
      have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have hj : ∀ j : Fin k, us (Fin.castSucc j) = 1 := by
        intro j
        obtain ⟨j', hj'⟩ := exists_ne j
        have hjj : Fin.castSucc j ≠ Fin.castSucc j' :=
          fun h => hj' (Fin.castSucc_injective _ h).symm
        have hwΩ : TauCeti.permutationGL (k := K)
            (pairSwap (Fin.castSucc j) * pairSwap (Fin.castSucc j')) ∈
            LargeEvenOmega (LargeEvenQPlus K (k + 1)) :=
          permutationGL_pairSwap_mul_mem_omegaPlus
        have hwD : (⟨_, hwΩ⟩ : LargeEvenOmega (LargeEvenQPlus K (k + 1))) ∈ D := by
          rw [hD, Subgroup.mem_subgroupOf]
          change TauCeti.permutationGL (k := K)
            (pairSwap (Fin.castSucc j) * pairSwap (Fin.castSucc j')) ∈ _
          rw [← permutationGL_commutator_pairSwap]
          refine hPT.commutator_mem_map_embHom_omega (largeEvenQPlus_split k) ?_ ?_
            (sumCongr_mem_orthPlus _) (pairSwap_mem_orthPlus _)
          · apply permutationGL_mem_centralizer_diagGL
            apply pairedUnits_comp_sumCongr_inv
            funext i
            have hlast : ∀ i, (Equiv.swap (Fin.castSucc j) (Fin.castSucc j')) i = Fin.last k ↔
                i = Fin.last k := fun i => by
              rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne
                (Fin.castSucc_ne_last j).symm (Fin.castSucc_ne_last j').symm]
            simp only [Function.comp_apply, Equiv.swap_inv, hu₀, Pi.mulSingle_apply, hlast]
          · apply permutationGL_mem_centralizer_diagGL
            apply pairedUnits_comp_pairSwap_inv
            rw [hu₀, Pi.mulSingle_eq_of_ne (Fin.castSucc_ne_last j')]
        have h2 := congrArg Subtype.val (hcomm' _ hwD)
        simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom] at h2
        rw [hcs] at h2
        exact eq_one_of_commute_pairSwap_mul hp hp2 husp hjj h2
      obtain ⟨n, hn⟩ := exists_pow_eq_mulSingle hζo husp hj
      refine Subgroup.mem_zpowers_iff.mpr ⟨(n : ℤ), Subtype.ext ?_⟩
      rw [zpow_natCast, SubgroupClass.coe_pow, hct, hu₀, diagGL_pairedUnits_mulSingle_pow, hn,
        MulEquiv.coe_toMonoidHom, hcs]
    · intro hmem j hj
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hjt := Subgroup.mem_centralizer_singleton_iff.mp (hDle hj)
      rw [← hn]
      exact (Commute.zpow_left hjt.symm n).eq



theorem ggEndNode_omegaPlus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    {m : ℕ} (hm : 4 ≤ m) :
    GGEndNode p m (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact ggEndNode_of_elt subset_rfl (center_omegaPlus_eq_bot hp hp2 hpq (by omega))
    (ggEndNodeElt_of_mulEquiv (projMkEquiv (scalars_subgroupOf_omegaPlus_eq_bot (by omega)))
      (ggEndNodeElt_omegaPlusGroup hp hp2 hpq (by omega)))

end PlusEndNode

end TableBOrth

end CFSG.StandardType
