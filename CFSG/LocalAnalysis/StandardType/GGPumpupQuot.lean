module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.GGPumpup

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBPrimeJoin Subgroup
open scoped Pointwise

variable {H : Type*} [Group H]

theorem map_conjugate {H' : Type*} [Group H'] (f : H →* H') (A : Subgroup H) (g : H) :
    (conjugate A g).map f = conjugate (A.map f) (f g) := by
  ext y
  simp only [conjugate, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, by simp only [map_mul, map_inv, inv_inv]⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨g⁻¹ * a * g⁻¹⁻¹, ⟨a, ha, rfl⟩, by simp only [map_mul, map_inv, inv_inv]⟩

theorem conjugate_le_conjugate_iff {A B : Subgroup H} (g : H) :
    conjugate A g ≤ conjugate B g ↔ A ≤ B :=
  map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective

theorem conjugate_eq_of_mem_normalizer {K : Subgroup H} {g : H}
    (hg : g ∈ normalizer (K : Set H)) : conjugate K g = K := by
  ext y
  rw [UnbalancedLayer.mem_conjugate_iff]
  exact ((mem_normalizer_iff.mp hg) y).symm

theorem mem_normalizer_of_conjugate_eq {K : Subgroup H} {g : H} (h : conjugate K g = K) :
    g ∈ normalizer (K : Set H) := by
  rw [mem_normalizer_iff]
  intro y
  rw [← UnbalancedLayer.mem_conjugate_iff, h]

theorem conjugate_eq_of_le_of_le {K : Subgroup H} {g : H} (h1 : conjugate K g ≤ K)
    (h2 : conjugate K g⁻¹ ≤ K) : conjugate K g = K := by
  refine le_antisymm h1 ?_
  have h3 := (conjugate_le_conjugate_iff (A := conjugate K g⁻¹) (B := K) g).mpr h2
  rwa [UnbalancedLayer.conjugate_conjugate, inv_mul_cancel, UnbalancedLayer.conjugate_one] at h3

theorem conjugate_iSup {ι : Sort*} (S : ι → Subgroup H) (g : H) :
    conjugate (⨆ i, S i) g = ⨆ i, conjugate (S i) g :=
  Subgroup.map_iSup _ _

theorem conjugate_pow_eq {K : Subgroup H} {x : H} (h : conjugate K x = K) (n : ℕ) :
    conjugate K (x ^ n) = K := by
  induction n with
  | zero => rw [pow_zero, UnbalancedLayer.conjugate_one]
  | succ n ih =>
    rw [pow_succ, ← UnbalancedLayer.conjugate_conjugate, ih, h]

theorem conjugate_eq_of_le_centralizer {T : Subgroup H} {x : H}
    (hT : T ≤ centralizer ({x} : Set H)) : conjugate T x = T := by
  refine conjugate_eq_of_mem_normalizer (centralizer_le_normalizer _ ?_)
  rw [mem_centralizer_iff]
  intro t ht
  exact mem_centralizer_singleton_iff.mp (hT ht)

@[expose] def orbitJoinLT (A : Subgroup H) (x : H) (n : ℕ) : Subgroup H :=
  ⨆ (i : ℕ) (_ : i < n), conjugate A (x ^ i)

theorem conjugate_le_orbitJoinLT (A : Subgroup H) (x : H) {n i : ℕ} (hi : i < n) :
    conjugate A (x ^ i) ≤ orbitJoinLT A x n :=
  le_iSup₂_of_le i hi le_rfl

theorem le_orbitJoinLT (A : Subgroup H) (x : H) {n : ℕ} (hn : 0 < n) :
    A ≤ orbitJoinLT A x n := by
  have h := conjugate_le_orbitJoinLT A x hn
  rwa [pow_zero, UnbalancedLayer.conjugate_one] at h

theorem orbitJoinLT_le {A K : Subgroup H} {x : H} {n : ℕ}
    (h : ∀ i, i < n → conjugate A (x ^ i) ≤ K) : orbitJoinLT A x n ≤ K :=
  iSup₂_le h

theorem orbitJoinLT_eq_self {A : Subgroup H} {x : H} (hx : x ∈ normalizer (A : Set H))
    {n : ℕ} (hn : 0 < n) : orbitJoinLT A x n = A :=
  le_antisymm (orbitJoinLT_le fun i _ =>
      (conjugate_eq_of_mem_normalizer (pow_mem hx i)).le)
    (le_orbitJoinLT A x hn)

theorem map_orbitJoinLT {H' : Type*} [Group H'] (f : H →* H') (A : Subgroup H) (x : H)
    (n : ℕ) : (orbitJoinLT A x n).map f = orbitJoinLT (A.map f) (f x) n := by
  simp only [orbitJoinLT, Subgroup.map_iSup, map_conjugate, map_pow]

theorem mem_normalizer_orbitJoinLT {A : Subgroup H} {x g : H} {n : ℕ}
    (hg : ∀ i, i < n → g ∈ normalizer (conjugate A (x ^ i) : Set H)) :
    g ∈ normalizer (orbitJoinLT A x n : Set H) := by
  refine mem_normalizer_of_conjugate_eq ?_
  unfold conjugate
  rw [orbitJoinLT, Subgroup.map_iSup]
  refine iSup_congr fun i => ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun hi => ?_
  exact conjugate_eq_of_mem_normalizer (hg i hi)

@[expose] def closureIn (N T : Subgroup H) : Subgroup H :=
  ⨆ (g : H) (_ : g ∈ N), conjugate T g

theorem conjugate_le_closureIn (N T : Subgroup H) {g : H} (hg : g ∈ N) :
    conjugate T g ≤ closureIn N T :=
  le_iSup₂_of_le g hg le_rfl

theorem le_closureIn (N T : Subgroup H) : T ≤ closureIn N T := by
  have h := conjugate_le_closureIn N T (one_mem N)
  rwa [UnbalancedLayer.conjugate_one] at h

theorem closureIn_le {N T K : Subgroup H} (h : ∀ g ∈ N, conjugate T g ≤ K) :
    closureIn N T ≤ K :=
  iSup₂_le h

theorem closureIn_le_self {N T : Subgroup H} (hTN : T ≤ N) : closureIn N T ≤ N :=
  closureIn_le fun g hg =>
    ((conjugate_le_conjugate_iff g).mpr hTN).trans
      (conjugate_eq_of_mem_normalizer (le_normalizer hg)).le

theorem conjugate_closureIn_le {N T : Subgroup H} {g : H}
    (h : ∀ a ∈ N, ∃ b ∈ N, conjugate T (a * g) = conjugate T b) :
    conjugate (closureIn N T) g ≤ closureIn N T := by
  rw [closureIn, conjugate_iSup]
  refine iSup_le fun a => ?_
  rw [conjugate_iSup]
  refine iSup_le fun ha => ?_
  obtain ⟨b, hb, hab⟩ := h a ha
  rw [UnbalancedLayer.conjugate_conjugate, hab]
  exact conjugate_le_closureIn N T hb

theorem conjugate_closureIn_eq_of_mem {N T : Subgroup H} {g : H} (hg : g ∈ N) :
    conjugate (closureIn N T) g = closureIn N T :=
  conjugate_eq_of_le_of_le (conjugate_closureIn_le fun a ha => ⟨a * g, mul_mem ha hg, rfl⟩)
    (conjugate_closureIn_le fun a ha => ⟨a * g⁻¹, mul_mem ha (inv_mem hg), rfl⟩)

theorem conjugate_closureIn_le_of_mem_normalizer {N T : Subgroup H} {g : H}
    (hgN : g ∈ normalizer (N : Set H)) (hgT : conjugate T g = T) :
    conjugate (closureIn N T) g ≤ closureIn N T := by
  refine conjugate_closureIn_le fun a ha => ⟨g⁻¹ * a * g, ?_, ?_⟩
  · have h := (mem_normalizer_iff.mp (inv_mem hgN) a).mp ha
    rwa [inv_inv] at h
  · rw [show a * g = g * (g⁻¹ * a * g) by group, ← UnbalancedLayer.conjugate_conjugate, hgT]

theorem conjugate_closureIn_eq_of_mem_normalizer {N T : Subgroup H} {g : H}
    (hgN : g ∈ normalizer (N : Set H)) (hgT : conjugate T g = T) :
    conjugate (closureIn N T) g = closureIn N T := by
  refine conjugate_eq_of_le_of_le (conjugate_closureIn_le_of_mem_normalizer hgN hgT)
    (conjugate_closureIn_le_of_mem_normalizer (inv_mem hgN) ?_)
  have h := congrArg (fun K => conjugate K g⁻¹) hgT
  simp only [UnbalancedLayer.conjugate_conjugate, mul_inv_cancel,
    UnbalancedLayer.conjugate_one] at h
  exact h.symm

theorem closureIn_subgroupOf_normal {N T : Subgroup H} (hTN : T ≤ N) :
    ((closureIn N T).subgroupOf N).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer (closureIn_le_self hTN)]
  intro g hg
  exact mem_normalizer_of_conjugate_eq (conjugate_closureIn_eq_of_mem hg)

theorem exists_mul_pow_eq {N : Subgroup H} {n m : H} (hn : n ∈ N)
    (hm : m ∈ normalizer (N : Set H)) (j : ℕ) : ∃ n' ∈ N, (n * m) ^ j = n' * m ^ j := by
  induction j with
  | zero => exact ⟨1, one_mem N, by rw [pow_zero, pow_zero, one_mul]⟩
  | succ j ih =>
    obtain ⟨n', hn', h⟩ := ih
    refine ⟨n' * (m ^ j * n * (m ^ j)⁻¹), mul_mem hn' ?_, ?_⟩
    · exact (mem_normalizer_iff.mp (pow_mem hm j) n).mp hn
    · rw [pow_succ, h, pow_succ]
      group

theorem mem_of_mem_sup_of_coprime [Finite H] {p : ℕ} {N M : Subgroup H}
    (hM : p.Coprime (Nat.card M)) (hMN : M ≤ normalizer (N : Set H)) {t : H} (ht : t ∈ N ⊔ M)
    {k : ℕ} (htk : t ^ p ^ k = 1) : t ∈ N := by
  have ht' : t ∈ (N : Set H) * (M : Set H) := by
    rw [← coe_mul_of_right_le_normalizer_left N M hMN]
    exact ht
  obtain ⟨n, hn, m, hm, rfl⟩ := ht'
  obtain ⟨n', hn', h⟩ := exists_mul_pow_eq hn (hMN hm) (p ^ k)
  rw [htk] at h
  have hmk : m ^ p ^ k ∈ N := by
    rw [eq_inv_of_mul_eq_one_right h.symm]
    exact inv_mem hn'
  have hord : orderOf m ∣ Nat.card M := by
    rw [← Subgroup.orderOf_mk m hm]
    exact orderOf_dvd_natCard _
  have hco : (p ^ k).Coprime (orderOf m) := (hM.coprime_dvd_right hord).pow_left k
  obtain ⟨a, ha⟩ := exists_pow_eq_self_of_coprime hco
  refine mul_mem hn ?_
  rw [← ha]
  exact pow_mem hmk a

theorem le_of_le_sup_of_coprime [Finite H] {p : ℕ} [Fact p.Prime] {T N M : Subgroup H}
    (hT : primeResidual p T = ⊤) (hM : p.Coprime (Nat.card M))
    (hMN : M ≤ normalizer (N : Set H)) (hle : T ≤ N ⊔ M) : T ≤ N := by
  have hres : primeResidual p T ≤ N.subgroupOf T := by
    refine sSup_le fun P hP z hz => ?_
    obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow (⟨z, hz⟩ : P)
    have h1 : (⟨z, hz⟩ : P) ^ p ^ k = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one _
    have hzk : (z : H) ^ p ^ k = 1 := by
      have h2 := congrArg (fun w : P => ((w : T) : H)) h1
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h2
    exact mem_of_mem_sup_of_coprime hM hMN (hle z.2) hzk
  rw [hT, top_le_iff, subgroupOf_eq_top] at hres
  exact hres

section PComponents

variable [Finite H] {p : ℕ} [Fact p.Prime]

theorem not_le_pPrimeCore {A : Subgroup H} (hA : IsPComponent p A) :
    ¬ A ≤ pPrimeCore p H := by
  intro hle
  apply core_ne_top p A hA
  rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection p A hA.choose_spec.2.1]
  exact subgroupOf_eq_top.mpr hle

theorem map_pPrimeCore_le {A : Subgroup H} (hA : IsPComponent p A) :
    (pPrimeCore p A).map A.subtype ≤ pPrimeCore p H := by
  rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection p A hA.choose_spec.2.1,
    subgroupOf_map_subtype]
  exact inf_le_left

theorem pPrimeCore_le_normalizer {A : Subgroup H} (hA : IsPComponent p A) :
    pPrimeCore p H ≤ normalizer (A : Set H) :=
  ((contains_or_normalizes_core p A (pPrimeCore p H) hA
    (Normal.isSubnormal inferInstance)).resolve_left (not_le_pPrimeCore hA)).1

theorem pLayer_le_normalizer {A : Subgroup H} (hA : IsPComponent p A) :
    pLayer H p ≤ normalizer (A : Set H) := by
  refine sSup_le fun L hL => ?_
  by_cases h : L = A
  · rw [h]
    exact le_normalizer
  · exact (mutual_normalization_core_commutation p A L hA hL (Ne.symm h)).1

end PComponents

section Main

variable [Finite H] {p : ℕ} [hp : Fact p.Prime]

theorem exists_pComponent_closureIn_eq {x : H} (hx : x ^ p = 1) {T : Subgroup H}
    (hTC : T ≤ centralizer ({x} : Set H))
    (hT : IsPComponent p (T.subgroupOf (centralizer ({x} : Set H))))
    (hTE : T ≤ pLayer H p) :
    ∃ A : Subgroup H, IsPComponent p A ∧ closureIn (pLayer H p) T = orbitJoinLT A x p := by
  set O := pPrimeCore p H with hOdef
  set π := QuotientGroup.mk' O with hπdef
  set E := pLayer H p with hEdef
  have hxp : ∃ n : ℕ, x ^ p ^ n = 1 := ⟨1, by rw [pow_one]; exact hx⟩
  have hCb : (centralizer ({x} : Set H)).map π = centralizer ({π x} : Set (H ⧸ O)) :=
    LBalance.Quot.map_centralizer_eq hxp
  have hTb : IsPComponent p ((T.map π).subgroupOf (centralizer ({π x} : Set (H ⧸ O)))) := by
    have h := LBalance.Quot.isPComponent_map_of_map_eq hCb hT
    rwa [map_subgroupOf_eq_of_le hTC] at h
  have hTbC : T.map π ≤ centralizer ({π x} : Set (H ⧸ O)) := (map_mono hTC).trans hCb.le
  have hTbE : T.map π ≤ layer (H ⧸ O) :=
    (map_mono hTE).trans LBalance.Quot.map_pLayer_eq_layer_quotient.le
  obtain ⟨M, hM, hTM, -, -⟩ :=
    UnbalancedLayer.ordinary_layer_local_prime_component_orbit_location hp.out hTbC hTb hTbE
  obtain ⟨hA, hAM⟩ := canonicalPrimeLift_isPComponent p M hM
  set A := canonicalPrimeLift p M with hAdef
  have hAi : ∀ i : ℕ, IsPComponent p (conjugate A (x ^ i)) := fun i =>
    UnbalancedLayer.isPComponent_conjugate hA _
  have hordp : orderOf (π x) ≤ p :=
    orderOf_le_of_pow_eq_one hp.out.pos (by rw [← map_pow, hx, map_one])
  have hTKAb : T.map π ≤ (orbitJoinLT A x p).map π := by
    rw [map_orbitJoinLT, hAM]
    exact hTM.trans (iSup_le fun i => conjugate_le_orbitJoinLT M (π x) (lt_of_lt_of_le i.2 hordp))
  have hTKAO : T ≤ orbitJoinLT A x p ⊔ O := by
    have h := map_le_iff_le_comap.mp hTKAb
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at h
  have hTres : primeResidual p T = ⊤ :=
    primeResidual_eq_top_of_equiv p (subgroupOfEquivOfLe hTC)
      (primeResidual_eq_top_of_pComponent p _ hT)
  have hONKA : O ≤ normalizer (orbitJoinLT A x p : Set H) := fun o ho =>
    mem_normalizer_orbitJoinLT fun i _ => pPrimeCore_le_normalizer (hAi i) ho
  have hTKA : T ≤ orbitJoinLT A x p :=
    le_of_le_sup_of_coprime hTres pPrimeCore_coprime_card hONKA hTKAO
  have hEKA : E ≤ normalizer (orbitJoinLT A x p : Set H) := fun g hg =>
    mem_normalizer_orbitJoinLT fun i _ => pLayer_le_normalizer (hAi i) hg
  have hKKA : closureIn E T ≤ orbitJoinLT A x p := closureIn_le fun g hg =>
    ((conjugate_le_conjugate_iff g).mpr hTKA).trans (conjugate_eq_of_mem_normalizer (hEKA hg)).le
  have hEn : E.Normal := by
    have : E.Characteristic := pLayer_characteristic
    infer_instance
  have hKsub : (closureIn E T).IsSubnormal :=
    IsSubnormal.step _ E (closureIn_le_self hTE) hEn.isSubnormal (closureIn_subgroupOf_normal hTE)
  have hxE : x ∈ normalizer (E : Set H) := by
    rw [normalizer_eq_top_iff.mpr hEn]
    exact mem_top x
  have hKx : conjugate (closureIn E T) x = closureIn E T :=
    conjugate_closureIn_eq_of_mem_normalizer hxE (conjugate_eq_of_le_centralizer hTC)
  have hTperf : ⁅T, T⁆ = T := by
    have := CatalogueBHeldSmallCore.pComponent_perfect p _ hT
    have : Group.IsPerfect T := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hTC).toMonoidHom) (subgroupOfEquivOfLe hTC).surjective
    exact isPerfect_iff.mp this
  have hAK : A ≤ closureIn E T := by
    by_contra hAK
    have hcomm : ∀ i : ℕ, ⁅conjugate A (x ^ i), closureIn E T⁆ ≤ O := fun i => by
      rcases contains_or_normalizes_core p _ _ (hAi i) hKsub with h | h
      · exact absurd ((conjugate_le_conjugate_iff (x ^ i)).mp
          (h.trans (conjugate_pow_eq hKx i).ge)) hAK
      · exact h.2.trans (map_pPrimeCore_le (hAi i))
    have hcen : (orbitJoinLT A x p).map π ≤
        centralizer ((closureIn E T).map π : Set (H ⧸ O)) := by
      rw [orbitJoinLT, Subgroup.map_iSup]
      refine iSup_le fun i => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun _ => ?_
      rw [← commutator_eq_bot_iff_le_centralizer, ← map_commutator, Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk']
      exact hcomm i
    have hKK : ⁅closureIn E T, closureIn E T⁆ ≤ O := by
      have h1 : (closureIn E T).map π ≤ centralizer ((closureIn E T).map π : Set (H ⧸ O)) :=
        (map_mono hKKA).trans hcen
      rwa [← commutator_eq_bot_iff_le_centralizer, ← map_commutator, Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk'] at h1
    have hTO : T ≤ O := by
      rw [← hTperf]
      exact (commutator_mono (le_closureIn E T) (le_closureIn E T)).trans hKK
    apply pComponent_ne_bot hTb
    rw [(Subgroup.map_eq_bot_iff _).mpr (hTO.trans (QuotientGroup.ker_mk' O).ge), bot_subgroupOf]
  have hKAK : orbitJoinLT A x p ≤ closureIn E T := orbitJoinLT_le fun i _ =>
    ((conjugate_le_conjugate_iff (x ^ i)).mpr hAK).trans (conjugate_pow_eq hKx i).le
  exact ⟨A, hA, le_antisymm hKKA hKAK⟩

end Main

end CFSG.StandardType.GGPumpup

end
