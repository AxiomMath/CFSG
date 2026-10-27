module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsNineOddInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qe
public import CFSG.LocalAnalysis.UniquenessCase.UC6S29

public section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup

theorem oddOuterInner_lieModel_sq {r : ℕ} (hr : r.Prime) :
    ∀ (S : Type) [Group S] [Finite S], Blueprint.LieModel S .PSL 2 r 2 →
      FooteLit.OddOuterInner S := by
  intro S _ _ hS σ hσ
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hS
  have hxo : Odd (orderOf (autEquiv e σ)) := by rwa [MulEquiv.orderOf_eq]
  have hright : (autEquiv e σ).right = 1 := by
    have h1 : orderOf (autEquiv e σ).right ∣ 2 := by
      have := orderOf_dvd_natCard (autEquiv e σ).right
      rwa [card_ringAut F hr hF] at this
    have h2 : orderOf (autEquiv e σ).right ∣ orderOf (autEquiv e σ) :=
      orderOf_map_dvd (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) _
    have := Nat.dvd_gcd h1 h2
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hxo), Nat.dvd_one,
      orderOf_eq_one_iff] at this
  have hx : autEquiv e σ = SemidirectProduct.inl (autEquiv e σ).left :=
    SemidirectProduct.ext rfl hright
  have hlo : Odd (orderOf (autEquiv e σ).left) := by
    rw [hx, orderOf_injective _ SemidirectProduct.inl_injective] at hxo
    exact hxo
  obtain ⟨z, hz⟩ := mem_psl2Range_of_odd _ hlo
  refine ⟨e.symm z, (autEquiv e).injective ?_⟩
  rw [autEquiv_conj, MulEquiv.apply_symm_apply, incl_apply, hz]
  exact hx

end CFSG.ComponentClassification.AutL2Facts

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

section PSL2Lemmas

open CFSG.PSL2Table CFSG.GH74.GLS.IVK.L2Borel
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem commutator_borel_mem_unipotent {g h : PSL(2, F)} (hg : g ∈ borel F) (hh : h ∈ borel F) :
    g * h * g⁻¹ * h⁻¹ ∈ unipotent F := by
  obtain ⟨A, hA, rfl⟩ := hg
  obtain ⟨B, hB, rfl⟩ := hh
  have hA' : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hA
  have hB' : (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hB
  have hdA := det_entries A
  have hdB := det_entries B
  rw [hA', mul_zero, sub_zero] at hdA
  rw [hB', mul_zero, sub_zero] at hdB
  have hA0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdA
  have hB0 : (B : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdB
  rw [show mk A * mk B * (mk A)⁻¹ * (mk B)⁻¹ = mk (A * B * A⁻¹ * B⁻¹) by
    simp only [map_mul, map_inv]]
  rw [mk_mem_unipotent_iff]
  have e1 : ((A : Matrix (Fin 2) (Fin 2) F) 1 1) = ((A : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdA
  have e2 : ((B : Matrix (Fin 2) (Fin 2) F) 1 1) = ((B : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdB
  constructor
  · simp only [mul_apply_SL, coe_inv_SL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, hA', hB', neg_zero, mul_zero,
      zero_mul, add_zero, zero_add]
  · simp only [mul_apply_SL, coe_inv_SL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, hA', hB', neg_zero, mul_zero,
      zero_mul, add_zero, zero_add, e1, e2]
    field_simp

theorem sylow_sup_zpowers_eq_top {r n : ℕ} [Fact r.Prime] [Finite F] (hF : Nat.card F = r ^ n)
    (h2 : (2 : F) ≠ 0) (W : Sylow r (PSL(2, F))) {x : PSL(2, F)}
    (hx : x ∉ Subgroup.normalizer ((W : Subgroup (PSL(2, F))) : Set (PSL(2, F)))) :
    (W : Subgroup (PSL(2, F))) ⊔ Subgroup.zpowers x = ⊤ := by
  obtain ⟨c, hc⟩ := exists_conj_eq_unipotent hF W
  rw [hc] at hx ⊢
  rw [normalizer_map_equiv, normalizer_unipotent_eq h2] at hx
  have hx' : (MulAut.conj c).symm x ∉ borel F := fun h =>
    hx ⟨_, h, by simp [MulAut.conj_symm_apply, MulAut.conj_apply]; group⟩
  have htop := closure_unipotent_insert_eq_top hx'
  rw [eq_top_iff]
  intro g _
  obtain ⟨g', rfl⟩ := (MulAut.conj c).surjective g
  have hg' : g' ∈ Subgroup.closure ((unipotent F : Set PSL(2, F)) ∪ {(MulAut.conj c).symm x}) := by
    rw [htop]; exact Subgroup.mem_top _
  refine Subgroup.closure_induction (p := fun g _ => (MulAut.conj c) g ∈
      (unipotent F).map (MulAut.conj c).toMonoidHom ⊔ Subgroup.zpowers x) ?_ ?_ ?_ ?_ hg'
  · rintro y (hy | hy)
    · exact Subgroup.mem_sup_left ⟨y, hy, rfl⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      simp only [MulEquiv.apply_symm_apply]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  · simp
  · intro a b _ _ ha hb
    rw [map_mul]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [map_inv]
    exact Subgroup.inv_mem _ ha

theorem exists_inverting {r n p : ℕ} [Fact r.Prime] [Finite F] (hF : Nat.card F = r ^ n)
    (h2 : (2 : F) ≠ 0) (hq : 5 ≤ Nat.card F) (hp : p.Prime) (hpr : p ≠ r) {l : PSL(2, F)}
    (hl : orderOf l = p) : ∃ w : PSL(2, F), w * l * w⁻¹ = l⁻¹ := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    apply h2
    have := CharP.cast_eq_zero F (ringChar F)
    rw [h] at this
    simpa using this
  have hrF : (r : F) = 0 := by
    have h0 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card, hF] at h0
    have hn : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hF
      omega
    push_cast at h0
    exact pow_eq_zero_iff hn |>.1 h0
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hchar
  have hq' : 5 ≤ Fintype.card F := by rwa [Nat.card_eq_fintype_card] at hq
  have hord1 : ∀ c : PSL(2, F), orderOf (c * l * c⁻¹) = p := by
    intro c
    have := MulEquiv.orderOf_eq (MulAut.conj c) l
    rw [MulAut.conj_apply] at this
    rw [this, hl]
  have hnotunip : ∀ {t : F} (c : PSL(2, F)), c * l * c⁻¹ = mk (unip t) → False := by
    intro t c hc
    have h1 := hord1 c
    rw [hc] at h1
    have h3 : orderOf (mk (unip t)) ∣ r :=
      orderOf_dvd_of_pow_eq_one (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22qe_unipotent_pow hrF
        (mk_unip_mem_unipotent t))
    rw [h1] at h3
    exact hpr ((Nat.prime_dvd_prime_iff_eq hp (Fact.out)).1 h3)
  have key : ∀ x : PSL(2, F), IsConj l x → IsConj x x⁻¹ → ∃ w : PSL(2, F), w * l * w⁻¹ = l⁻¹ := by
    intro x hlx hxx
    obtain ⟨c1, hc1⟩ := isConj_iff.1 hlx
    obtain ⟨c2, hc2⟩ := isConj_iff.1 hxx
    refine ⟨c1⁻¹ * c2 * c1, ?_⟩
    calc c1⁻¹ * c2 * c1 * l * (c1⁻¹ * c2 * c1)⁻¹ = c1⁻¹ * (c2 * (c1 * l * c1⁻¹) * c2⁻¹) * c1 := by group
      _ = c1⁻¹ * (c2 * x * c2⁻¹) * c1 := by rw [hc1]
      _ = c1⁻¹ * x⁻¹ * c1 := by rw [hc2]
      _ = l⁻¹ := by rw [← hc1]; group
  rcases conj_cases hchar hq' hν l with h1 | h1 | h1 | ⟨x, hx, hx1, hlx⟩ | ⟨x, hx, hx1, hlx⟩
  · rw [h1, orderOf_one] at hl
    exact absurd hl.symm hp.one_lt.ne'
  · obtain ⟨c, hc⟩ := isConj_iff.1 h1
    exact (hnotunip c hc).elim
  · obtain ⟨c, hc⟩ := isConj_iff.1 h1
    exact (hnotunip c hc).elim
  · exact key x hlx ((isConj_splitTorus_iff hx hx1 (Subgroup.inv_mem _ hx)).2 (Or.inr rfl))
  · exact key x hlx ((isConj_nonsplitTorus_iff hchar hν hx hx1 (Subgroup.inv_mem _ hx)).2 (Or.inr rfl))

theorem exists_mem_normalizer_zpowers_not_mem {r n p : ℕ} [Fact r.Prime] [Finite F]
    (hF : Nat.card F = r ^ n) (h2 : (2 : F) ≠ 0) (hq : 5 ≤ Nat.card F) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpr : p ≠ r) (W : Sylow r (PSL(2, F))) {l : PSL(2, F)} (hl : orderOf l = p) :
    ∃ x ∈ Subgroup.normalizer (Subgroup.zpowers l : Set PSL(2, F)),
      x ∉ Subgroup.normalizer ((W : Subgroup (PSL(2, F))) : Set PSL(2, F)) := by
  obtain ⟨w, hw⟩ := exists_inverting hF h2 hq hp hpr hl
  have hwN : w ∈ Subgroup.normalizer (Subgroup.zpowers l : Set PSL(2, F)) := by
    refine CFSG.LocalAnalysis.UniquenessCase.UC6.mem_normalizer_of_forward_uc6 fun y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have : w * l ^ k * w⁻¹ = (l⁻¹) ^ k := by rw [← hw, conj_zpow]
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers l)) k
  by_contra hcon
  push Not at hcon
  have hlN : l ∈ Subgroup.normalizer (Subgroup.zpowers l : Set PSL(2, F)) :=
    Subgroup.le_normalizer (Subgroup.mem_zpowers l)
  have hwW := hcon w hwN
  have hlW := hcon l hlN
  obtain ⟨c, hc⟩ := exists_conj_eq_unipotent hF W
  rw [hc, normalizer_map_equiv, normalizer_unipotent_eq h2] at hwW hlW
  obtain ⟨b, hb, hbw⟩ := hwW
  obtain ⟨b', hb', hbl⟩ := hlW
  have hcomm : w * l * w⁻¹ * l⁻¹ ∈ (W : Subgroup (PSL(2, F))) := by
    have := commutator_borel_mem_unipotent hb hb'
    rw [hc]
    refine ⟨_, this, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom] at hbw hbl
    rw [← hbw, ← hbl]
    simp only [map_mul, map_inv]
    rfl
  rw [hw] at hcomm
  have hl2 : l ^ 2 ∈ (W : Subgroup (PSL(2, F))) := by
    have := Subgroup.inv_mem _ hcomm
    simpa [sq] using this
  obtain ⟨k, hk⟩ := W.isPGroup' ⟨l ^ 2, hl2⟩
  have hk' : (l ^ 2) ^ r ^ k = 1 := congrArg Subtype.val hk
  have hord2 : orderOf (l ^ 2) = p := by
    rw [Nat.Coprime.orderOf_pow, hl]
    rw [hl]
    exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hdvd : p ∣ r ^ k := by
    rw [← hord2]
    exact orderOf_dvd_of_pow_eq_one hk'
  exact hpr ((Nat.prime_dvd_prime_iff_eq hp (Fact.out)).1 (hp.dvd_of_dvd_pow hdvd))

theorem sylow_sup_normalizer_zpowers_eq_top {r n p : ℕ} [Fact r.Prime] [Finite F]
    (hF : Nat.card F = r ^ n) (h2 : (2 : F) ≠ 0) (hq : 5 ≤ Nat.card F) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpr : p ≠ r) (W : Sylow r (PSL(2, F))) {l : PSL(2, F)} (hl : orderOf l = p) :
    (W : Subgroup (PSL(2, F))) ⊔ Subgroup.normalizer (Subgroup.zpowers l : Set PSL(2, F)) = ⊤ := by
  obtain ⟨x, hxN, hxW⟩ := exists_mem_normalizer_zpowers_not_mem hF h2 hq hp hp2 hpr W hl
  rw [eq_top_iff, ← sylow_sup_zpowers_eq_top hF h2 W hxW]
  exact sup_le_sup_left (Subgroup.zpowers_le.2 hxN) _

open CFSG.ABGLocalTools CFSG.Blueprint in
theorem sup_normalizer_zpowers_eq_top_of_lieModel {S : Type} [Group S] [Finite S] {r p : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hL : LieModel S .PSL 2 r 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpr : p ≠ r) (E : Subgroup S) (hE : IsSylowOf r E ⊤) {l : S} (hl : orderOf l = p) :
    E ⊔ Subgroup.normalizer (Subgroup.zpowers l : Set S) = ⊤ := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨F, _, _, e, hF, hFq⟩ := CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' hr hr2 hL
  let φ : S ≃* PSL(2, F) := CFSG.GH74.GLS.IVK.toPSL e
  obtain ⟨-, hSp, hSnd⟩ := isSylowOf_iff.1 hE
  let W : Sylow r S := hSp.toSylow (by simpa [Subgroup.relIndex_top_right] using hSnd)
  let W' : Sylow r (PSL(2, F)) := Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective W
  have hW' : (W' : Subgroup (PSL(2, F))) = E.map φ.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hodd : Odd (Nat.card F) := by
    rw [hFq]
    exact (hr.odd_of_ne_two hr2).pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.GLS.IVK.L2Borel.two_ne_zero_of_odd_card hodd
  have hq : 5 ≤ Nat.card F := by
    have h3 : 3 ≤ r := by
      have := hr.two_le
      omega
    rw [hFq]
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left h3 2
  have hlord : orderOf (φ l) = p := by rw [MulEquiv.orderOf_eq]; exact hl
  have key := sylow_sup_normalizer_zpowers_eq_top hFq h2 hq hp hp2 hpr W' hlord
  rw [hW'] at key
  have hN : Subgroup.normalizer (Subgroup.zpowers (φ l) : Set PSL(2, F)) =
      (Subgroup.normalizer (Subgroup.zpowers l : Set S)).map φ.toMonoidHom := by
    rw [← normalizer_map_equiv φ (Subgroup.zpowers l), MonoidHom.map_zpowers]
    rfl
  rw [hN, ← Subgroup.map_sup] at key
  have := congrArg (Subgroup.comap φ.toMonoidHom) key
  rwa [Subgroup.comap_map_eq_self_of_injective φ.injective, Subgroup.comap_top] at this
end PSL2Lemmas

open Subgroup CFSG.Open CFSG.ABGLocalTools

end CFSG.LocalAnalysis.UniquenessCase.UC6
