module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Permutation.FiveTransitive.SetwiseSylowNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace Om8Lift

open CFSG.Open Subgroup
open scoped Pointwise

theorem le_centralizer_of_conj_mem {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P V₀ : Subgroup G} (hP : IsPGroup p P) (hV₀ : Nat.card V₀ < p) {v : G}
    (hv : ∀ x ∈ P, x * v * x⁻¹ * v⁻¹ ∈ V₀) : P ≤ Subgroup.centralizer ({v} : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulAction P G :=
    MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp P.subtype)
  have hsmul : ∀ y : P, y • v = (y : G) * v * (y : G)⁻¹ := by
    intro y
    change (ConjAct.toConjAct (y : G)) • v = (y : G) * v * (y : G)⁻¹
    rw [ConjAct.toConjAct_smul]
  have hcard_le : Nat.card (MulAction.orbit P v) ≤ Nat.card V₀ := by
    refine Nat.card_le_card_of_injective
      (fun w : MulAction.orbit P v => (⟨w.1 * v⁻¹, ?_⟩ : V₀)) ?_
    · obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp w.2
      rw [← hx, hsmul]
      exact hv (x : G) x.2
    · intro a b hab
      exact Subtype.ext (mul_right_cancel (Subtype.ext_iff.mp hab))
  obtain ⟨n, hn⟩ := hP.card_orbit v
  have hn0 : n = 0 := by
    have hlt : p ^ n < p := by
      rw [← hn]
      exact lt_of_le_of_lt hcard_le hV₀
    by_contra hn_ne
    have hp_le : p ≤ p ^ n := by
      have h1n : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn_ne
      simpa using (Nat.pow_le_pow_iff_right hp.one_lt).2 h1n
    exact absurd hp_le (not_le.mpr hlt)
  have hcard1 : Nat.card (MulAction.orbit P v) = 1 := by rw [hn, hn0, pow_zero]
  have hsub : Subsingleton (MulAction.orbit P v) := by
    have hle : Nat.card (MulAction.orbit P v) ≤ 1 := by rw [hcard1]
    exact Finite.card_le_one_iff_subsingleton.1 hle
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  have hxv : (⟨x, hx⟩ : P) • v = v := by
    have h1 : (⟨v, MulAction.mem_orbit_iff.2 ⟨(1 : P), by simp⟩⟩ : MulAction.orbit P v) =
        (⟨(⟨x, hx⟩ : P) • v, MulAction.mem_orbit v (⟨x, hx⟩ : P)⟩ :
          MulAction.orbit P v) := Subsingleton.elim _ _
    exact (Subtype.ext_iff.mp h1).symm
  have hconj : x * v * x⁻¹ = v := by
    rw [hsmul] at hxv
    exact hxv
  have hcomm : v * x = x * v := by
    have h2 : x * v = v * x := by
      calc x * v = x * v * x⁻¹ * x := by group
        _ = v * x := by rw [hconj]
    exact h2.symm
  exact hcomm

theorem two_le_pRank_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {H E : Subgroup G} (hEH : E ≤ H) (hE : IsElemAbelian p E) (hcard : p ^ 2 ≤ Nat.card E) :
    2 ≤ pRank p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE.isPGroup
  have hk2 : 2 ≤ k := by
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  exact hk2.trans (CFSG.SectionRank.le_pRank hp.one_lt hEH hE hk)

theorem le_ker_of_isPGroup_of_not_dvd {M B : Type*} [Group M] [Finite M] [Group B] (φ : M →* B)
    {p : ℕ} (hp : p.Prime) (hφ : ¬ p ∣ Nat.card φ.range) {X : Subgroup M} (hX : IsPGroup p X) :
    X ≤ φ.ker := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (X.map φ) := by
    have h : (φ '' (X : Set M)).Finite := (Set.toFinite (X : Set M)).image φ
    exact h.to_subtype
  have hmap : IsPGroup p (X.map φ) := hX.map φ
  have hdvd : Nat.card (X.map φ) ∣ Nat.card φ.range :=
    Subgroup.card_dvd_of_le (Subgroup.map_le_range φ X)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hmap
  have hn0 : n = 0 := by
    by_contra hn_ne
    apply hφ
    have hpdvd : p ∣ p ^ n := dvd_pow_self p hn_ne
    rw [← hn] at hpdvd
    exact hpdvd.trans hdvd
  have hcard1 : Nat.card (X.map φ) = 1 := by rw [hn, hn0, pow_zero]
  exact (Subgroup.map_eq_bot_iff X).mp (Subgroup.eq_bot_of_card_eq (X.map φ) hcard1)

theorem card_map_eq_of_inf_ker_eq_bot {M B : Type*} [Group M] [Finite M] [Group B] (φ : M →* B)
    {p : ℕ} {E : Subgroup M} (hE : IsElemAbelian p E) (hker : E ⊓ φ.ker = ⊥) :
    IsElemAbelian p (E.map φ) ∧ Nat.card (E.map φ) = Nat.card E := by
  refine ⟨hE.map φ, ?_⟩
  have hker' : (φ.ker).subgroupOf E = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_comm]
    exact hker
  have hinj : Function.Injective (φ.domRestrict E) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict]
    exact hker'
  have hcard : Nat.card E = Nat.card (φ.domRestrict E).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [← MonoidHom.domRestrict_range]
  exact hcard.symm

private theorem mulAut_smul_eq_map {B : Type*} [Group B] (a : MulAut B) (H : Subgroup B) :
    a • H = H.map a.toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  congr 1

theorem exists_isElemAbelian_map_le_zpowers {M B : Type*} [Group M] [Finite M] [Group B]
    (φ : M →* B) {p : ℕ} (hp : p.Prime) {E : Subgroup M} (hE : IsElemAbelian p E)
    (hEcard : p ^ 3 ≤ Nat.card E)
    (hker : ∀ E' : Subgroup M, IsElemAbelian p E' → E' ≤ φ.ker → Nat.card E' ≤ p)
    (hrange : ¬ p ^ 3 ∣ Nat.card φ.range) {b : B} (hb : b ∈ φ.range) (hbp : orderOf b = p) :
    ∃ E' : Subgroup M, IsElemAbelian p E' ∧ p ^ 2 ≤ Nat.card E' ∧
      E'.map φ ≤ Subgroup.zpowers b := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (E.map φ) := by
    have h : (φ '' (E : Set M)).Finite := (Set.toFinite (E : Set M)).image φ
    exact h.to_subtype
  let K : Subgroup M := E ⊓ φ.ker
  have hK_le : Nat.card K ≤ p :=
    hker K (hE.mono inf_le_left) inf_le_right
  have hKcard_sub : Nat.card K = Nat.card ((φ.ker).subgroupOf E) := by
    rw [← Subgroup.inf_subgroupOf_left φ.ker E]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ φ.ker ≤ E)).toEquiv).symm
  have hprod : Nat.card K * Nat.card (E.map φ) = Nat.card E := by
    have h1 : Nat.card ((φ.domRestrict E).ker) * Nat.card ((φ.domRestrict E).range) =
        Nat.card E := Subgroup.card_ker_mul_card_range (φ.domRestrict E)
    rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at h1
    rwa [← hKcard_sub] at h1
  have hp2_le : p ^ 2 ≤ Nat.card (E.map φ) := by
    have h1 : p * p ^ 2 ≤ p * Nat.card (E.map φ) := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ Nat.card E := hEcard
        _ = Nat.card K * Nat.card (E.map φ) := hprod.symm
        _ ≤ p * Nat.card (E.map φ) := Nat.mul_le_mul_right _ hK_le
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hmap_p : IsPGroup p (E.map φ) := hE.isPGroup.map φ
  have hmap_dvd : Nat.card (E.map φ) ∣ Nat.card φ.range :=
    Subgroup.card_dvd_of_le (Subgroup.map_le_range φ E)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hmap_p
  have hk2 : k = 2 := by
    have hk_ge : 2 ≤ k := by
      rw [hk] at hp2_le
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hp2_le
    have hk_le : k ≤ 2 := by
      by_contra hk_gt
      have hk3 : 3 ≤ k := by omega
      apply hrange
      have hdvd : p ^ 3 ∣ p ^ k := Nat.pow_dvd_pow p hk3
      rw [← hk] at hdvd
      exact hdvd.trans hmap_dvd
    omega
  have hmap_card : Nat.card (E.map φ) = p ^ 2 := by rw [hk, hk2]
  have hEcard3 : Nat.card E = p ^ 3 := by
    have hle : Nat.card E ≤ p ^ 3 := by
      rw [← hprod, hmap_card]
      calc Nat.card K * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ hK_le
        _ = p ^ 3 := by ring
    exact le_antisymm hle hEcard
  let R : Subgroup B := φ.range
  haveI : Finite R := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI : Finite (Sylow p R) :=
    Finite.of_injective (SetLike.coe : Sylow p R → Set R) SetLike.coe_injective
  let Ebar : Subgroup R := (E.map φ).subgroupOf R
  have hEbar_card : Nat.card Ebar = p ^ 2 := by
    change Nat.card ((E.map φ).subgroupOf R) = p ^ 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_le_range φ E)).toEquiv,
      hmap_card]
  have hEbar_p : IsPGroup p Ebar :=
    hmap_p.of_equiv (Subgroup.subgroupOfEquivOfLe (Subgroup.map_le_range φ E)).symm
  have hEbar_idx : ¬ p ∣ Ebar.index := by
    intro hdvd
    apply hrange
    obtain ⟨c, hc⟩ := hdvd
    rw [← Subgroup.card_mul_index (H := Ebar), hEbar_card, hc]
    exact ⟨c, by ring⟩
  let S : Sylow p R := hEbar_p.toSylow hEbar_idx
  let Bbar : Subgroup R := (Subgroup.zpowers b).subgroupOf R
  have hBbar_card : Nat.card Bbar = p := by
    change Nat.card ((Subgroup.zpowers b).subgroupOf R) = p
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hb)).toEquiv,
      Nat.card_zpowers, hbp]
  have hBbar_p : IsPGroup p Bbar := IsPGroup.of_card (n := 1) (by rw [hBbar_card, pow_one])
  obtain ⟨Q, hBQ⟩ := hBbar_p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R S Q
  have hBQS : Bbar ≤ (g • S : Sylow p R) := by rw [hg]; exact hBQ
  have hBbar_map : Bbar.map R.subtype = Subgroup.zpowers b := by
    dsimp only [Bbar]
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.2 hb)]
  have hSm : ((g • S : Sylow p R) : Subgroup R).map R.subtype =
      ((E.map φ).map (MulAut.conj (g : B)).toMonoidHom) ⊓ R := by
    rw [Sylow.coe_subgroup_smul]
    have hSE : (S : Subgroup R) = Ebar := IsPGroup.toSylow_coe hEbar_p hEbar_idx
    rw [hSE, Subgroup.conj_smul_subgroupOf (Subgroup.map_le_range φ E) g,
      mulAut_smul_eq_map, Subgroup.subgroupOf_map_subtype]
  have hmap_le : Bbar.map R.subtype ≤
      ((g • S : Sylow p R) : Subgroup R).map R.subtype := Subgroup.map_mono hBQS
  rw [hBbar_map, hSm] at hmap_le
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 g.2
  let E₁ : Subgroup M := E.map (MulAut.conj m).toMonoidHom
  have hE₁ : IsElemAbelian p E₁ := hE.map (MulAut.conj m).toMonoidHom
  have hE₁_card : Nat.card E₁ = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj m).injective
  have hE₁map : E₁.map φ = (E.map φ).map (MulAut.conj (φ m)).toMonoidHom := by
    have hcomp : φ.comp (MulAut.conj m).toMonoidHom =
        (MulAut.conj (φ m)).toMonoidHom.comp φ := by
      ext y
      simp [MulAut.conj_apply, map_mul, map_inv]
    dsimp only [E₁]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  have hE₁map_card : Nat.card (E₁.map φ) = p ^ 2 := by
    rw [hE₁map, Subgroup.card_map_of_injective (MulAut.conj (φ m)).injective, hmap_card]
  have hzpow_le : Subgroup.zpowers b ≤ E₁.map φ := by
    rw [hE₁map]
    have hle : Subgroup.zpowers b ≤ (E.map φ).map (MulAut.conj (g : B)).toMonoidHom :=
      hmap_le.trans inf_le_left
    rwa [← hm] at hle
  let K₁ : Subgroup M := E₁ ⊓ φ.ker
  have hK₁card_sub : Nat.card K₁ = Nat.card ((φ.ker).subgroupOf E₁) := by
    rw [← Subgroup.inf_subgroupOf_left φ.ker E₁]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : E₁ ⊓ φ.ker ≤ E₁)).toEquiv).symm
  have hE₁inf_card : Nat.card K₁ = p := by
    have hprod₁ : Nat.card K₁ * Nat.card (E₁.map φ) = Nat.card E₁ := by
      have h1 : Nat.card ((φ.domRestrict E₁).ker) * Nat.card ((φ.domRestrict E₁).range) =
          Nat.card E₁ := Subgroup.card_ker_mul_card_range (φ.domRestrict E₁)
      rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at h1
      rwa [← hK₁card_sub] at h1
    rw [hE₁map_card, hE₁_card, hEcard3] at hprod₁
    have h2 : Nat.card K₁ * p ^ 2 = p * p ^ 2 := by rw [hprod₁]; ring
    exact Nat.mul_right_cancel (pow_pos hp.pos 2) h2
  let P' : Subgroup M := (Subgroup.zpowers b).comap φ
  let E' : Subgroup M := E₁ ⊓ P'
  let K' : Subgroup M := E' ⊓ φ.ker
  have hE' : IsElemAbelian p E' := hE₁.mono inf_le_left
  have hE'ker : K' = K₁ := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ E' ⊓ φ.ker := hx
      obtain ⟨hxE', hxker⟩ := Subgroup.mem_inf.1 hx'
      have hx'' : x ∈ E₁ ⊓ P' := hxE'
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx'').1, hxker⟩
    · intro x hx
      have hx' : x ∈ E₁ ⊓ φ.ker := hx
      obtain ⟨hxE₁, hxker⟩ := Subgroup.mem_inf.1 hx'
      have hxP : x ∈ P' := by
        change φ x ∈ Subgroup.zpowers b
        rw [MonoidHom.mem_ker.1 hxker]
        exact Subgroup.one_mem _
      have hxE' : x ∈ E' := Subgroup.mem_inf.2 ⟨hxE₁, hxP⟩
      exact Subgroup.mem_inf.2 ⟨hxE', hxker⟩
  have hE'map : E'.map φ = Subgroup.zpowers b := by
    apply le_antisymm
    · exact Subgroup.map_le_iff_le_comap.2 inf_le_right
    · intro y hy
      have hy₁ : y ∈ E₁.map φ := hzpow_le hy
      obtain ⟨x, hxE₁, hxy⟩ := Subgroup.mem_map.1 hy₁
      rw [← hxy]
      refine Subgroup.mem_map_of_mem φ ⟨hxE₁, ?_⟩
      change φ x ∈ Subgroup.zpowers b
      rw [hxy]
      exact hy
  have hE'ker_sub : Nat.card K' = Nat.card ((φ.ker).subgroupOf E') := by
    rw [← Subgroup.inf_subgroupOf_left φ.ker E']
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : E' ⊓ φ.ker ≤ E')).toEquiv).symm
  have hkerE'_card : Nat.card ((φ.ker).subgroupOf E') = p := by
    rw [← hE'ker_sub, hE'ker, hE₁inf_card]
  have hK'_card : Nat.card K' = p := hE'ker_sub.trans hkerE'_card
  have hE'card : p ^ 2 ≤ Nat.card E' := by
    have hprod' : Nat.card K' * Nat.card (E'.map φ) = Nat.card E' := by
      have h1 : Nat.card ((φ.domRestrict E').ker) * Nat.card ((φ.domRestrict E').range) =
          Nat.card E' := Subgroup.card_ker_mul_card_range (φ.domRestrict E')
      rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at h1
      rwa [← hE'ker_sub] at h1
    rw [hK'_card, hE'map, Nat.card_zpowers, hbp] at hprod'
    rw [← hprod']
    exact le_of_eq (by ring)
  exact ⟨E', hE', hE'card, hE'map.le⟩

theorem map_normalizer_sylow {M B : Type*} [Group M] [Finite M] [Group B] (φ : M →* B)
    {q : ℕ} (hq : q.Prime) {T : Subgroup M} (hT : IsPGroup q T) (hTi : ¬ q ∣ T.index) :
    (Subgroup.normalizer (T : Set M)).map φ =
      Subgroup.normalizer (T.map φ : Set B) ⊓ φ.range := by
  haveI : Fact q.Prime := ⟨hq⟩
  apply le_antisymm
  · intro b hb
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hb
    exact Subgroup.mem_inf.2
      ⟨Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ hn),
       MonoidHom.mem_range.2 ⟨n, rfl⟩⟩
  · intro b hb
    obtain ⟨hbN, hbr⟩ := Subgroup.mem_inf.1 hb
    obtain ⟨m, hmφ⟩ := MonoidHom.mem_range.1 hbr
    let H : Subgroup M := T ⊔ φ.ker
    have hH : m ∈ Subgroup.normalizer (H : Set M) := by
      have h1 : m ∈ (Subgroup.normalizer (T.map φ : Set B)).comap φ := by
        rw [Subgroup.mem_comap, hmφ]
        exact hbN
      rw [Subgroup.comap_normalizer_eq_of_le_range (H := T.map φ) (f := φ)
        (Subgroup.map_le_range φ T)] at h1
      rwa [Subgroup.comap_map_eq] at h1
    let S : Sylow q M := hT.toSylow hTi
    have hSH : (S : Subgroup M) ≤ H := by
      have hST : (S : Subgroup M) = T := IsPGroup.toSylow_coe hT hTi
      rw [hST]
      exact le_sup_left
    obtain ⟨k, hk⟩ :=
      CFSG.FiveTransitive.SetwiseSylowNormalizer.exists_correction H (S.subtype hSH) m hH
    have hN : (k : M) * m ∈ Subgroup.normalizer (T : Set M) := by
      have hX : ((S.subtype hSH : Subgroup H).map H.subtype) = T := by
        rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSH]
        exact IsPGroup.toSylow_coe hT hTi
      rw [hX] at hk
      exact hk
    have hkP : φ (k : M) ∈ (Subgroup.normalizer (T : Set M)).map φ := by
      have hkT : φ (k : M) ∈ T.map φ := by
        have hkH : (k : M) ∈ (T.map φ).comap φ := by
          rw [Subgroup.comap_map_eq]
          exact k.2
        exact Subgroup.mem_comap.1 hkH
      exact Subgroup.map_mono Subgroup.le_normalizer hkT
    have hnP : φ ((k : M) * m) ∈ (Subgroup.normalizer (T : Set M)).map φ :=
      Subgroup.mem_map_of_mem φ hN
    have hb_eq : (φ (k : M))⁻¹ * φ ((k : M) * m) = b := by
      rw [map_mul, hmφ, inv_mul_cancel_left]
    rw [← hb_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hkP) hnP

private theorem not_isCyclic_map {A B : Type*} [Group A] [Group B] {S : Subgroup A} (f : A →* B)
    (hf : Function.Injective f) (h : ¬ IsCyclic S) : ¬ IsCyclic (S.map f) :=
  fun hc => h ((MulEquiv.isCyclic (S.equivMapOfInjective f hf)).2 hc)

private theorem exists_isPGroup_noncyclic_of_surjective {C P : Type*} [Group C] [Finite C]
    [Group P] (g : C →* P) (hg : Function.Surjective g) {p : ℕ} [Fact p.Prime] {E : Subgroup P}
    (hEp : IsPGroup p E) (hEc : ¬ IsCyclic E) :
    ∃ X : Subgroup C, IsPGroup p X ∧ ¬ IsCyclic X := by
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  have hQc : ¬ IsCyclic (Q : Subgroup P) := fun hc => hEc (Subgroup.isCyclic_of_le hEQ)
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hg p Q
  have hSQ : (S : Subgroup C).map g = (Q : Subgroup P) := by rw [← hS]; rfl
  refine ⟨(S : Subgroup C), S.2, ?_⟩
  intro hc
  apply hQc
  rw [← hSQ]
  exact isCyclic_of_surjective (g.subgroupMap (S : Subgroup C))
    (g.subgroupMap_surjective (S : Subgroup C))

theorem exists_isPGroup_noncyclic_le_normalizer {M B : Type*} [Group M] [Finite M] [Group B]
    (φ : M →* B) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {T : Subgroup M} (hT : IsPGroup q T)
    (hTi : ¬ q ∣ T.index) {X : Subgroup B} (hXr : X ≤ φ.range) (hXp : IsPGroup p X)
    (hXc : ¬ IsCyclic X) (hXN : X ≤ Subgroup.normalizer (T.map φ : Set B)) :
    ∃ Y : Subgroup M, Y ≤ Subgroup.normalizer (T : Set M) ∧ IsPGroup p Y ∧ ¬ IsCyclic Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  let C : Subgroup M := Subgroup.normalizer (T : Set M)
  let g : C →* B := φ.comp C.subtype
  have hg_range : g.range = Subgroup.normalizer (T.map φ : Set B) ⊓ φ.range := by
    dsimp only [g, C]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact map_normalizer_sylow φ hq hT hTi
  have hXg : X ≤ g.range := by
    intro x hx
    rw [hg_range]
    exact Subgroup.mem_inf.2 ⟨hXN hx, hXr hx⟩
  let E : Subgroup g.range := X.subgroupOf g.range
  have hEp : IsPGroup p E :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXg).symm
  have hEc : ¬ IsCyclic E :=
    fun hc => hXc ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hXg)).1 hc)
  obtain ⟨Y₀, hY₀p, hY₀c⟩ :=
    exists_isPGroup_noncyclic_of_surjective g.rangeRestrict g.rangeRestrict_surjective hEp hEc
  refine ⟨Y₀.map C.subtype, Subgroup.map_subtype_le Y₀, hY₀p.map C.subtype,
    not_isCyclic_map C.subtype C.subtype_injective hY₀c⟩

end Om8Lift

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
