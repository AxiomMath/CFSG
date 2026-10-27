module

public import CFSG.Open.LocalVocabulary
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

private theorem exists_mem_inv_mul_mem_normalizer {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (S : Sylow p X) {W : Subgroup X} (hSW : (S : Subgroup X) ≤ W) {g : X}
    (hg : ((g • S : Sylow p X) : Subgroup X) ≤ W) :
    ∃ w ∈ W, w⁻¹ * g ∈ normalizer ((S : Subgroup X) : Set X) := by
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq W (S.subtype hSW) ((g • S).subtype hg)
  refine ⟨y, y.2, ?_⟩
  have h1 : (y : X) • S = g • S :=
    Sylow.subtype_injective (hP := Sylow.smul_le hSW y) (hQ := hg)
      ((Sylow.smul_subtype hSW y).symm.trans hy)
  have h2 : ((y : X)⁻¹ * g) • S = S := by rw [mul_smul, ← h1, inv_smul_smul]
  exact Sylow.smul_eq_iff_mem_normalizer.1 h2

private theorem card_comap_mk' {X : Type*} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (T : Subgroup (X ⧸ K)) :
    Nat.card (T.comap (QuotientGroup.mk' K)) = Nat.card T * Nat.card K := by
  have h1 := Subgroup.card_mul_index (T.comap (QuotientGroup.mk' K))
  have h2 := Subgroup.card_mul_index T
  have h3 := Subgroup.card_mul_index K
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K)] at h1
  have h4 : K.index = Nat.card (X ⧸ K) := Subgroup.index_eq_card K
  have hpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  calc Nat.card X = Nat.card K * K.index := h3.symm
    _ = Nat.card K * Nat.card (X ⧸ K) := by rw [h4]
    _ = Nat.card K * (Nat.card T * T.index) := by rw [h2]
    _ = Nat.card T * Nat.card K * T.index := by ring

private theorem eq_of_mk'_eq {X : Type*} [Group X] {K : Subgroup X} [K.Normal] {A : Subgroup X}
    (hdisj : Disjoint A K) {a b : X} (ha : a ∈ A) (hb : b ∈ A)
    (h : QuotientGroup.mk' K a = QuotientGroup.mk' K b) : a = b :=
  inv_mul_eq_one.1 (disjoint_def.1 hdisj (A.mul_mem (A.inv_mem ha) hb) (QuotientGroup.eq.1 h))

private theorem isElemAbelian_of_map_le {X : Type*} [Group X] {K : Subgroup X} [K.Normal] {q : ℕ}
    {A : Subgroup X} (hdisj : Disjoint A K) {T : Subgroup (X ⧸ K)}
    (hT : CFSG.Open.IsElemAbelian q T) (hAT : A.map (QuotientGroup.mk' K) ≤ T) :
    CFSG.Open.IsElemAbelian q A := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
  · show (a : X) * b = b * a
    have ha' : QuotientGroup.mk' K (a : X) ∈ T := hAT (Subgroup.mem_map_of_mem _ a.2)
    have hb' : QuotientGroup.mk' K (b : X) ∈ T := hAT (Subgroup.mem_map_of_mem _ b.2)
    have hc := hT.comm ha' hb'
    rw [← map_mul, ← map_mul] at hc
    exact eq_of_mk'_eq hdisj (A.mul_mem a.2 b.2) (A.mul_mem b.2 a.2) hc
  · have haT : QuotientGroup.mk' K a ∈ T := hAT (Subgroup.mem_map_of_mem _ ha)
    have h1 : QuotientGroup.mk' K (a ^ q) = QuotientGroup.mk' K 1 := by
      rw [map_pow, hT.2 _ haT, map_one]
    exact eq_of_mk'_eq hdisj (A.pow_mem ha q) A.one_mem h1

private theorem lift_sylow {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal] {q : ℕ}
    (hq : q.Prime) (hqK : ¬ q ∣ Nat.card K) {T : Subgroup (X ⧸ K)}
    (hT : CFSG.Open.IsElemAbelian q T) {n : ℕ} (hTc : Nat.card T = q ^ n) {A : Subgroup X}
    (hA : IsSylowOf q A (T.comap (QuotientGroup.mk' K))) :
    Nat.card A = q ^ n ∧ Disjoint A K ∧ A.map (QuotientGroup.mk' K) = T ∧
      CFSG.Open.IsElemAbelian q A := by
  have : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card A = q ^ n := by
    rw [hA.card_eq, card_comap_mk', hTc,
      Nat.factorization_mul (pow_ne_zero n hq.ne_zero) Nat.card_pos.ne', Finsupp.add_apply,
      hq.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hqK,
      add_zero]
  have hdisj : Disjoint A K := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hcard]
    exact ((Nat.Prime.coprime_iff_not_dvd hq).2 hqK).pow_left n
  have hle : A.map (QuotientGroup.mk' K) ≤ T := Subgroup.map_le_iff_le_comap.2 hA.le
  have hmapcard : Nat.card (A.map (QuotientGroup.mk' K)) = Nat.card A := by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← Subgroup.inf_relIndex_right K A,
      disjoint_iff.1 hdisj.symm, Subgroup.relIndex_bot_left]
  exact ⟨hcard, hdisj,
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hTc, hmapcard, hcard])),
    isElemAbelian_of_map_le hdisj hT hle⟩

private theorem exists_mem_map_conj_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {W P P' : Subgroup G} (hP : IsSylowOf p P W) (hP' : IsSylowOf p P' W) :
    ∃ w ∈ W, P' = P.map (MulAut.conj w).toMonoidHom := by
  obtain ⟨A, rfl⟩ := hP
  obtain ⟨B, rfl⟩ := hP'
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq W A B
  refine ⟨y, y.2, ?_⟩
  have h1 : (B : Subgroup W) = (A : Subgroup W).map (MulAut.conj y).toMonoidHom := by
    rw [← hy, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [h1, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem comap_normalizer_map_mk'_le {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (K : Subgroup X) [K.Normal] (S : Sylow p X) :
    (normalizer (((S : Subgroup X).map (QuotientGroup.mk' K) : Subgroup (X ⧸ K)) :
      Set (X ⧸ K))).comap (QuotientGroup.mk' K) ≤ K ⊔ normalizer ((S : Subgroup X) : Set X) := by
  intro g hg
  have hW : ((S : Subgroup X).map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) =
      (S : Subgroup X) ⊔ K := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hSW : (S : Subgroup X) ≤ ((S : Subgroup X).map (QuotientGroup.mk' K)).comap
      (QuotientGroup.mk' K) := by
    rw [hW]
    exact le_sup_left
  have hgW : ((g • S : Sylow p X) : Subgroup X) ≤ ((S : Subgroup X).map
      (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ (S : Subgroup X) := by
      rwa [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        MulAut.smul_def, MulAut.conj_inv_apply] at hx
    have h1 := (mem_normalizer_iff.1 (Subgroup.mem_comap.1 hg) _).1
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' K) hx')
    have e : QuotientGroup.mk' K g * QuotientGroup.mk' K (g⁻¹ * x * g) *
        (QuotientGroup.mk' K g)⁻¹ = QuotientGroup.mk' K x := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [e] at h1
    exact h1
  obtain ⟨w, hwW, hwn⟩ := exists_mem_inv_mul_mem_normalizer S hSW hgW
  have hWK : ((S : Subgroup X).map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) ≤
      K ⊔ normalizer ((S : Subgroup X) : Set X) := by
    rw [hW]
    exact sup_le (le_normalizer.trans le_sup_right) le_sup_left
  have hg' : g = w * (w⁻¹ * g) := by group
  rw [hg']
  exact (K ⊔ normalizer ((S : Subgroup X) : Set X)).mul_mem (hWK hwW)
    ((le_sup_right :
      normalizer ((S : Subgroup X) : Set X) ≤ K ⊔ normalizer ((S : Subgroup X) : Set X)) hwn)

theorem not_dvd_card_sylow_of_quotient {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    {r : ℕ} (hr : r.Prime) (hK : ¬ r ∣ Nat.card K)
    (hY : ¬ r ∣ Nat.card (Sylow 2 (X ⧸ K))) : ¬ r ∣ Nat.card (Sylow 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : Function.Surjective (QuotientGroup.mk' K) := QuotientGroup.mk'_surjective K
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  let U : Sylow 2 (X ⧸ K) := S.mapSurjective hπ
  have hU : (U : Subgroup (X ⧸ K)) = (S : Subgroup X).map (QuotientGroup.mk' K) := rfl
  set N : Subgroup X := normalizer ((S : Subgroup X) : Set X)
  set P : Subgroup X :=
    (normalizer ((U : Subgroup (X ⧸ K)) : Set (X ⧸ K))).comap (QuotientGroup.mk' K)
  have hNP : N ≤ P := fun x hx => by
    show QuotientGroup.mk' K x ∈ normalizer ((U : Subgroup (X ⧸ K)) : Set (X ⧸ K))
    rw [hU]
    exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hx)
  have hKP : K ≤ P := fun x hx => by
    have h1 : QuotientGroup.mk' K x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    show QuotientGroup.mk' K x ∈ normalizer ((U : Subgroup (X ⧸ K)) : Set (X ⧸ K))
    rw [h1]
    exact one_mem _
  have hPeq : P = K ⊔ N := le_antisymm (comap_normalizer_map_mk'_le K S) (sup_le hKP hNP)
  have hrel : N.relIndex P = N.relIndex K := by
    rw [hPeq]
    exact CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal K N
  have hidx : P.index = Nat.card (Sylow 2 (X ⧸ K)) :=
    (Subgroup.index_comap_of_surjective _ hπ).trans U.card_eq_index_normalizer.symm
  have hcard : Nat.card (Sylow 2 X) = N.relIndex P * P.index :=
    S.card_eq_index_normalizer.trans (Subgroup.relIndex_mul_index hNP).symm
  intro hdvd
  rw [hcard] at hdvd
  rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
  · rw [hrel] at h
    exact hK (h.trans (Subgroup.relIndex_dvd_card N K))
  · rw [hidx] at h
    exact hY h

theorem exists_pair_lift {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal] {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (hpK : ¬ p ∣ Nat.card K) (hrK : ¬ r ∣ Nat.card K)
    {E₁ Q₁ : Subgroup (X ⧸ K)} (hE : CFSG.Open.IsElemAbelian r E₁)
    (hEc : Nat.card E₁ = r ^ 2) (hQ : CFSG.Open.IsElemAbelian p Q₁)
    (hQc : Nat.card Q₁ = p ^ 2) (hpow : ∀ x ∈ Q₁, ∃ k : ℕ, ∀ e ∈ E₁, x * e * x⁻¹ = e ^ k) :
    ∃ E Q : Subgroup X, CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      CFSG.Open.IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧
      ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨Q, hQS⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (Q₁.comap (QuotientGroup.mk' K))
  obtain ⟨hQc', -, hQmap, hQel⟩ := lift_sylow K hp hpK hQ hQc hQS
  have hxQ : ∀ x ∈ Q, QuotientGroup.mk' K x ∈ Q₁ := fun x hx =>
    hQmap.le (Subgroup.mem_map_of_mem _ hx)
  have hQÊ : Q ≤ normalizer ((E₁.comap (QuotientGroup.mk' K) : Subgroup X) : Set X) := by
    refine Subgroup.le_normalizer_iff.2 fun x hx y hy => ?_
    obtain ⟨k, hk⟩ := hpow _ (hxQ x hx)
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv, hk _ (Subgroup.mem_comap.1 hy)]
    exact E₁.pow_mem (Subgroup.mem_comap.1 hy) k
  have hÊc : Nat.card (E₁.comap (QuotientGroup.mk' K)) = r ^ 2 * Nat.card K := by
    rw [card_comap_mk', hEc]
  have hpÊ : ¬ p ∣ Nat.card (E₁.comap (QuotientGroup.mk' K)) := by
    rw [hÊc]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow h))
    · exact hpK h
  obtain ⟨E', hE'⟩ :=
    CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hp hr hQel.isPGroup hQÊ hpÊ
  obtain ⟨E, hES, hQE⟩ : ∃ E : Subgroup X,
      IsSylowOf r E (E₁.comap (QuotientGroup.mk' K)) ∧ Q ≤ normalizer (E : Set X) :=
    ⟨_, ⟨E', rfl⟩, hE'⟩
  obtain ⟨hEc', hEdisj, hEmap, hEel⟩ := lift_sylow K hr hrK hE hEc hES
  refine ⟨E, Q, hEel, hEc', hQel, hQc', fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hpow _ (hxQ x hx)
  refine ⟨k, fun e he => ?_⟩
  have heE₁ : QuotientGroup.mk' K e ∈ E₁ := hEmap.le (Subgroup.mem_map_of_mem _ he)
  refine eq_of_mk'_eq hEdisj ((mem_normalizer_iff.1 (hQE hx) e).1 he) (E.pow_mem he k) ?_
  rw [map_mul, map_mul, map_inv, map_pow, hk _ heE₁]

theorem exists_pow_conj_of_coprime {G : Type} [Group G] [Finite G] {L S E₀ Q : Subgroup G}
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (hSL : S ≤ L) (hSr : ¬ r ∣ Nat.card S)
    (hSp : ¬ p ∣ Nat.card S) (hE₀L : E₀ ≤ L) (hE₀S : E₀ ≤ normalizer (S : Set G))
    (hE₀el : CFSG.Open.IsElemAbelian r E₀) (hE₀c : Nat.card E₀ = r ^ 2)
    (hQel : CFSG.Open.IsElemAbelian p Q) (hQS : Q ≤ normalizer (S : Set G))
    (hpow : ∀ x ∈ Q, ∃ k : ℕ, ∀ h ∈ L, h ∈ normalizer (S : Set G) → x * h * x⁻¹ * (h ^ k)⁻¹ ∈ S) :
    ∃ E : Subgroup G, E ≤ L ∧ CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hWL : S ⊔ E₀ ≤ L := sup_le hSL hE₀L
  have hWN : S ⊔ E₀ ≤ normalizer (S : Set G) := sup_le le_normalizer hE₀S
  have hQW : Q ≤ normalizer ((S ⊔ E₀ : Subgroup G) : Set G) := by
    have hW : S ⊔ E₀ = closure ((S : Set G) ∪ E₀) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    rw [hW, le_normalizer_closure_iff]
    intro x hx g hg
    rw [← hW]
    rcases hg with hg | hg
    · exact mem_sup_left ((mem_normalizer_iff.1 (hQS hx) g).1 hg)
    · obtain ⟨k, hk⟩ := hpow x hx
      have h1 := hk g (hE₀L hg) (hE₀S hg)
      have h2 : x * g * x⁻¹ = (x * g * x⁻¹ * (g ^ k)⁻¹) * g ^ k := by group
      rw [h2]
      exact mul_mem (mem_sup_left h1) (mem_sup_right (pow_mem hg k))
  have hdisj₀ : Disjoint S E₀ := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hE₀c]
    exact ((Nat.Prime.coprime_iff_not_dvd hr).2 hSr).symm.pow_right 2
  have hWc : Nat.card (S ⊔ E₀ : Subgroup G) = Nat.card S * r ^ 2 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer S E₀ hE₀S hdisj₀, hE₀c]
  have hpW : ¬ p ∣ Nat.card (S ⊔ E₀ : Subgroup G) := by
    rw [hWc]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hSp h
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨P', hP'⟩ :=
    CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hp hr hQel.isPGroup hQW hpW
  have hE₀W : IsSylowOf r E₀ (S ⊔ E₀) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_right, hE₀el.isPGroup, fun h => ?_⟩
    have h1 := relIndex_mul_card E₀ (S ⊔ E₀)
    rw [inf_eq_left.2 (le_sup_right : E₀ ≤ S ⊔ E₀), hWc, hE₀c] at h1
    have h2 : E₀.relIndex (S ⊔ E₀) = Nat.card S :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hr.pos 2) h1
    exact hSr (h2 ▸ h)
  obtain ⟨E, hE, hQE⟩ : ∃ E : Subgroup G, IsSylowOf r E (S ⊔ E₀) ∧ Q ≤ normalizer (E : Set G) :=
    ⟨_, ⟨P', rfl⟩, hP'⟩
  obtain ⟨w, -, hEeq⟩ := exists_mem_map_conj_eq hE₀W hE
  have hEel : CFSG.Open.IsElemAbelian r E := by
    rw [hEeq]
    exact hE₀el.map _
  have hEc : Nat.card E = r ^ 2 := by
    rw [hEeq, card_map_of_injective (f := (MulAut.conj w).toMonoidHom)
      (MulAut.conj w).injective, hE₀c]
  have hEW : E ≤ S ⊔ E₀ := hE.le
  have hdisj : Disjoint E S := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hEc]
    exact ((Nat.Prime.coprime_iff_not_dvd hr).2 hSr).pow_left 2
  refine ⟨E, hEW.trans hWL, hEel, hEc, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hpow x hx
  refine ⟨k, fun e he => ?_⟩
  have h1 := hk e (hWL (hEW he)) (hWN (hEW he))
  have h2 : x * e * x⁻¹ * (e ^ k)⁻¹ ∈ E :=
    mul_mem ((mem_normalizer_iff.1 (hQE hx) e).1 he) (inv_mem (pow_mem he k))
  exact mul_inv_eq_one.1 (disjoint_def.1 hdisj h2 h1)

end CFSG.LocalAnalysis.UniquenessCase.UC22
