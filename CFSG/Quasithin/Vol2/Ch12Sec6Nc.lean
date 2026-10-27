module

public import CFSG.Quasithin.Vol2.Ch12Sec6FrE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c S126FE Equiv
open scoped IsMulCommutative

namespace S126N

theorem eq_id_of_comm (μ : D8 →* D8) (hinj : Function.Injective μ)
    (hcomm : ∀ σ ∈ alternatingGroup (Fin 8), ∀ y, μ (dAct σ y) = dAct σ (μ y)) :
    ∀ y, μ y = y := by
  let μ' : B5FinS8.Mod8 →* B5FinS8.Mod8 :=
    S126Ex.e8.symm.toMonoidHom.comp (μ.comp S126Ex.e8.toMonoidHom)
  have hμ'i : Function.Injective μ' :=
    S126Ex.e8.symm.injective.comp (hinj.comp S126Ex.e8.injective)
  have he8 : ∀ (σ : Perm (Fin 8)) (y : D8),
      S126Ex.e8.symm (dAct σ y) = B5FinS8.act8 σ (S126Ex.e8.symm y) := by
    intro σ y
    rw [MulEquiv.symm_apply_eq, S126Ex.e8_act, MulEquiv.apply_symm_apply]
  have hμ'c : ∀ σ ∈ alternatingGroup (Fin 8), ∀ q,
      μ' (B5FinS8.act8 σ q) = B5FinS8.act8 σ (μ' q) := by
    intro σ hσ q
    change S126Ex.e8.symm (μ (S126Ex.e8 (B5FinS8.act8 σ q))) =
      B5FinS8.act8 σ (S126Ex.e8.symm (μ (S126Ex.e8 q)))
    rw [S126Ex.e8_act, ← he8]
    congr 1
    exact hcomm σ hσ _
  have hk := B5FinS8.k8 μ' hμ'i hμ'c
  intro y
  have h1 := hk (S126Ex.e8.symm y)
  change S126Ex.e8.symm (μ (S126Ex.e8 (S126Ex.e8.symm y))) = _ at h1
  rw [MulEquiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq] at h1
  exact h1

variable {G : Type} [Group G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem conj_mem_centralizer {x v : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hv : v ∈ Subgroup.centralizer (L : Set G)) :
    x * v * x⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : x⁻¹ * l * x ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxL) l).1 hl
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hv _ hl'
  calc l * (x * v * x⁻¹) = x * ((x⁻¹ * l * x) * v) * x⁻¹ := by group
    _ = x * (v * (x⁻¹ * l * x)) * x⁻¹ := by rw [h1]
    _ = x * v * x⁻¹ * l := by group

omit [IsMulCommutative ↥V] in
theorem conj_inv_mem_centralizer {x v : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hv : x * v * x⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    v ∈ Subgroup.centralizer (L : Set G) := by
  have h := conj_mem_centralizer (Subgroup.inv_mem _ hxL) hv
  rwa [show x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ = v by group] at h

theorem pi_bijective [Finite G] (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    Function.Bijective F.π := by
  have hcardA := card_autOn hH hH.hyp.irrPlus.2.2.1
  obtain ⟨e⟩ := Finite.card_eq.1 hcardA.symm
  exact ⟨(Finite.injective_iff_surjective_of_equiv e).2 F.π_surj, F.π_surj⟩

theorem exists_actsAs [Finite G] (F : Frame126 T L V) (hH : Hyp126 G T L V) {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxV : x ∈ Subgroup.normalizer (V : Set G)) :
    ∃ σ : Perm (Fin 8), ActsAs F x σ := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  let πE : ↥(alternatingGroup (Fin 8)) ≃* ↥(autOn L V) :=
    MulEquiv.ofBijective F.π (pi_bijective F hH)
  set a : MulAut ↥V := conjAct V ⟨x, hxV⟩ with ha
  have haN : a ∈ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
    autOn_le_normalizer_autOn
      (T := Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) hLV inf_le_right
      inf_le_left (mem_autOn_iff_exists.mpr ⟨x, hxV, ⟨hxL, hxV⟩, rfl⟩)
  set ρ := CFSG.QuasithinUnique.Claim2526.thetaHom (autOn L V) πE.symm ⟨a, haN⟩ with hρ
  have hρA : ∀ σ : ↥(alternatingGroup (Fin 8)), ρ * σ * ρ⁻¹ ∈ alternatingGroup (Fin 8) := by
    intro σ
    have hn : (alternatingGroup (Fin 8)).Normal := inferInstance
    exact hn.conj_mem _ σ.2 ρ
  have hconj : ∀ (σ : ↥(alternatingGroup (Fin 8))) (v : ↥V),
      a (((F.π σ : ↥(autOn L V)) : MulAut ↥V) v) =
        ((F.π ⟨ρ * σ * ρ⁻¹, hρA σ⟩ : ↥(autOn L V)) : MulAut ↥V) (a v) := by
    intro σ v
    set k : ↥(autOn L V) := (autOn L V).normalizerMonoidHom ⟨a, haN⟩ (πE σ) with hkdef
    have hk : (k : MulAut ↥V) = a * (πE σ : MulAut ↥V) * a⁻¹ := rfl
    have h1 := CFSG.QuasithinUnique.Claim2526.theta_spec (autOn L V) πE.symm ⟨a, haN⟩ (πE σ)
    rw [MulEquiv.symm_apply_apply, ← hρ] at h1
    have h2 : πE.symm k = ⟨ρ * σ * ρ⁻¹, hρA σ⟩ := Subtype.ext h1
    have h3 : k = F.π ⟨ρ * σ * ρ⁻¹, hρA σ⟩ := by
      rw [← h2]
      exact (πE.apply_symm_apply k).symm
    have h4 : (k : MulAut ↥V) (a v) =
        ((F.π ⟨ρ * σ * ρ⁻¹, hρA σ⟩ : ↥(autOn L V)) : MulAut ↥V) (a v) := by
      rw [h3]
    rw [← h4, hk]
    show a ((πE σ : MulAut ↥V) v) = (a * (πE σ : MulAut ↥V) * a⁻¹) (a v)
    simp [MulAut.mul_apply]
  let f : ↥V →* D8 := F.β.comp a.toMonoidHom
  have hker : F.β.ker ≤ f.ker := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv ⊢
    change F.β (a v) = 1
    rw [F.β_ker] at hv ⊢
    exact conj_mem_centralizer hxL hv
  let eβ := QuotientGroup.quotientKerEquivOfSurjective F.β F.β_surj
  let τ : D8 →* D8 := (QuotientGroup.lift F.β.ker f hker).comp eβ.symm.toMonoidHom
  have hτ : ∀ v, τ (F.β v) = F.β (a v) := by
    intro v
    have h1 : eβ.symm (F.β v) = QuotientGroup.mk v := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift F.β.ker f hker (eβ.symm (F.β v)) = _
    rw [h1, QuotientGroup.lift_mk]
    rfl
  let μ : D8 →* D8 := (dAct ρ⁻¹).comp τ
  have hμi : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨v, rfl⟩ := F.β_surj y
    have h1 : τ (F.β v) = 1 := by
      have := congrArg (dAct ρ) hy
      rwa [map_one, show dAct ρ (μ (F.β v)) = τ (F.β v) from dAct_dAct_inv ρ _] at this
    rw [hτ, F.β_ker] at h1
    rw [F.β_ker]
    exact conj_inv_mem_centralizer hxL h1
  have hμc : ∀ σ ∈ alternatingGroup (Fin 8), ∀ y, μ (dAct σ y) = dAct σ (μ y) := by
    intro σ hσ y
    obtain ⟨v, rfl⟩ := F.β_surj y
    change dAct ρ⁻¹ (τ (dAct σ (F.β v))) = dAct σ (dAct ρ⁻¹ (τ (F.β v)))
    rw [← F.equi ⟨σ, hσ⟩, hτ, hτ, hconj, F.equi, ← dAct_mul, ← dAct_mul]
    have e : ρ⁻¹ * ((⟨ρ * σ * ρ⁻¹, hρA ⟨σ, hσ⟩⟩ : ↥(alternatingGroup (Fin 8))) :
        Perm (Fin 8)) = σ * ρ⁻¹ := by
      show ρ⁻¹ * (ρ * σ * ρ⁻¹) = σ * ρ⁻¹
      group
    rw [e]
  have hid := eq_id_of_comm μ hμi hμc
  refine ⟨ρ, fun v w hw => ?_⟩
  have hwa : w = a v := Subtype.ext hw
  have h1 := hid (F.β v)
  change dAct ρ⁻¹ (τ (F.β v)) = F.β v at h1
  have h2 : τ (F.β v) = dAct ρ (F.β v) := by
    have := congrArg (dAct ρ) h1
    rwa [dAct_dAct_inv] at this
  rw [hwa, ← hτ, h2]

theorem hasWt_iff (F : Frame126 T L V) {x : G} {σ : Perm (Fin 8)} (hx : ActsAs F x σ) {k : ℕ}
    (v w : ↥V) (hw : (w : G) = x * v * x⁻¹) : HasWt k (F.β w) ↔ HasWt k (F.β v) := by
  rw [hx v w hw, hasWt_dAct_iff]

theorem exists_sylow_pi [Finite G] (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    ∃ P : Subgroup (Perm (Fin 8)), P ≤ alternatingGroup (Fin 8) ∧ IsPGroup 2 P ∧
      64 ≤ Nat.card P ∧ ∀ σ ∈ P, ∃ hσ : σ ∈ alternatingGroup (Fin 8), ∃ t ∈ T,
        ∃ ht : t ∈ Subgroup.normalizer (V : Set G),
          conjAct V ⟨t, ht⟩ = ((F.π ⟨σ, hσ⟩ : ↥(autOn L V)) : MulAut ↥V) := by
  have hyp := hH.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hcardA := card_autOn hH hLV
  let f : ↥(alternatingGroup (Fin 8)) →* MulAut ↥V := (autOn L V).subtype.comp F.π
  have hfi : Function.Injective f := Subtype.val_injective.comp (pi_bijective F hH).1
  have hfr : f.range = autOn L V := by
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      exact (F.π σ).2
    · intro hx
      obtain ⟨σ, hσ⟩ := F.π_surj ⟨x, hx⟩
      exact ⟨σ, by simp [f, hσ]⟩
  have hsylTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal
      (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow (le_sup_right : T ≤ L ⊔ T)) le_sup_left
      (sup_le Subgroup.le_normalizer hyp.normalizes)
  have hS := CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn hsylTL hLV
  have hS64 : Nat.card ↥(autOn (T ⊓ L) V) = 2 ^ 6 :=
    card_of_isSylowTwoOf hS (m := 315) (by rw [hcardA, card_A8]; norm_num) (by decide)
  let P₀ : Subgroup ↥(alternatingGroup (Fin 8)) := (autOn (T ⊓ L) V).comap f
  have hP₀ : Nat.card P₀ = 64 := by
    have h1 : P₀.map f = autOn (T ⊓ L) V := by
      rw [Subgroup.map_comap_eq, hfr]
      exact inf_of_le_right hS.1
    have h2 : Nat.card (P₀.map f) = Nat.card P₀ :=
      Nat.card_congr (Subgroup.equivMapOfInjective P₀ f hfi).toEquiv.symm
    rw [← h2, h1, hS64]
    norm_num
  refine ⟨P₀.map (alternatingGroup (Fin 8)).subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · refine IsPGroup.of_card (n := 6) ?_
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective P₀ _ Subtype.val_injective).toEquiv,
      hP₀]
    norm_num
  · rw [← Nat.card_congr (Subgroup.equivMapOfInjective P₀ _ Subtype.val_injective).toEquiv, hP₀]
  · rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨t, ht, htTL, hta⟩ := mem_autOn_iff_exists.mp (show f σ ∈ autOn (T ⊓ L) V from hσ)
    exact ⟨σ.2, t, htTL.1, ht, hta⟩

@[expose] def e4567 : Fin 8 → ZMod 2 := ![0, 0, 0, 0, 1, 1, 1, 1]

theorem fixD8_chk : ∀ x : Fin 8 → ZMod 2, x 0 = 0 →
    (∀ i, x (tf 1 0 i) + x (tf 1 0 0) = x i) → (∀ i, x (tf 2 0 i) + x (tf 2 0 0) = x i) →
    (∀ i, x (tf 0 1 i) + x (tf 0 1 0) = x i) → (∀ i, x (tf 0 2 i) + x (tf 0 2 0) = x i) →
    (∀ i, x (bsw i) + x (bsw 0) = x i) → x = 0 ∨ x = e4567 := by
  decide +kernel

theorem wt_e4567 : (Finset.univ.filter fun i => e4567 i ≠ 0).card = 4 := by
  decide

theorem nrm_eq (m : ↥(coreMod 8)) :
    (nrm (m : PermMod 8) : PermMod 8) = m ∨ (nrm (m : PermMod 8) : PermMod 8) = m * allOnes 8 := by
  rcases zmod2_cases (Multiplicative.toAdd (m : PermMod 8) 0) with h0 | h0
  · left
    apply Multiplicative.toAdd.injective
    funext i
    rw [nrm_apply, h0, add_zero]
  · right
    apply Multiplicative.toAdd.injective
    funext i
    rw [nrm_apply, h0, toAdd_mul]
    rfl

theorem iota_mem (y : D8) : iota y ∈ coreMod 8 := (mem_coreMod).2 (iota_sum y)

theorem mk_iota (y : D8) : (QuotientGroup.mk (⟨iota y, iota_mem y⟩ : ↥(coreMod 8)) : D8) = y := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rw [mk_eq_iff]
  exact nrm_eq m

theorem eq_of_fix_Q8_D8 {y : D8} (h : ∀ σ ∈ Q8, dAct σ y = y) : y = 1 ∨ HasWt 4 y := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_Q8
  have hc : ∀ u v : Fin 4, tau u v ∈ Q8 → ∀ i, Multiplicative.toAdd (iota y) (tf u v i) +
      Multiplicative.toAdd (iota y) (tf u v 0) = Multiplicative.toAdd (iota y) i := by
    intro u v hm i
    have := cond_of_fix (h _ hm) i
    rwa [tau_inv_apply, tau_inv_apply] at this
  have key := fixD8_chk (Multiplicative.toAdd (iota y)) (iota_zero y) (hc 1 0 h1) (hc 2 0 h2)
    (hc 0 1 h3) (hc 0 2 h4) (fun i => by
      have := cond_of_fix (h _ h5) i
      rwa [bsw_inv] at this)
  rcases key with hk | hk
  · left
    apply iota_inj
    rw [map_one]
    exact Multiplicative.toAdd.injective hk
  · right
    refine ⟨⟨iota y, iota_mem y⟩, mk_iota y, ?_⟩
    change (Finset.univ.filter fun i => Multiplicative.toAdd (iota y) i ≠ 0).card = 4
    rw [hk]
    exact wt_e4567

theorem fix_sylow_D8 {P : Subgroup (Perm (Fin 8))} (hPA : P ≤ alternatingGroup (Fin 8))
    (hP2 : IsPGroup 2 P) (hP64 : 64 ≤ Nat.card P) {y : D8} (h : ∀ σ ∈ P, dAct σ y = y) :
    y = 1 ∨ HasWt 4 y := by
  obtain ⟨g, hg⟩ := S126Ex.exists_conj_le_P8 hP2
  let P' := P.map (MulAut.conj g⁻¹).toMonoidHom
  have hP'le : P' ≤ Q8 := by
    rintro _ ⟨q, hq, rfl⟩
    have e : (MulAut.conj g⁻¹).toMonoidHom q = g⁻¹ * q * g := by
      simp
    rw [e]
    refine ⟨hg q hq, ?_⟩
    have hn : (alternatingGroup (Fin 8)).Normal := inferInstance
    have := hn.conj_mem q (hPA hq) g⁻¹
    rwa [inv_inv] at this
  have hcard : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.equivMapOfInjective P _ (MulAut.conj g⁻¹).injective).toEquiv.symm
  have hP'eq : P' = Q8 := Subgroup.eq_of_le_of_card_ge hP'le (by
    have := card_Q8_le
    omega)
  have hfix : ∀ ρ ∈ Q8, dAct ρ (dAct g⁻¹ y) = dAct g⁻¹ y := by
    intro ρ hρ
    rw [← hP'eq] at hρ
    obtain ⟨q, hq, rfl⟩ := hρ
    have e : (MulAut.conj g⁻¹).toMonoidHom q = g⁻¹ * q * g := by
      simp
    rw [e, ← dAct_mul, show g⁻¹ * q * g * g⁻¹ = g⁻¹ * q by group, dAct_mul, h q hq]
  rcases eq_of_fix_Q8_D8 hfix with h1 | h1
  · left
    have := congrArg (dAct g) h1
    rwa [dAct_dAct_inv, map_one] at this
  · right
    have := hasWt_dAct g h1
    rwa [dAct_dAct_inv] at this

theorem T_fixed [Finite G] (F : Frame126 T L V) (hH : Hyp126 G T L V) {w : ↥V}
    (hw : ∀ t ∈ T, t * (w : G) = w * t) : F.β w = 1 ∨ HasWt 4 (F.β w) := by
  obtain ⟨P, hPA, hP2, hP64, hP⟩ := exists_sylow_pi F hH
  refine fix_sylow_D8 hPA hP2 hP64 fun σ hσ => ?_
  obtain ⟨hσA, t, htT, ht, hta⟩ := hP σ hσ
  have h1 := F.equi ⟨σ, hσA⟩ w
  rw [← hta] at h1
  have h2 : (conjAct V ⟨t, ht⟩ : MulAut ↥V) w = w := by
    apply Subtype.ext
    change t * w * t⁻¹ = w
    rw [hw t htT, mul_inv_cancel_right]
  rw [h2] at h1
  exact h1.symm

theorem wt_one : wt (1 : PermMod 8) = 0 := by
  decide

theorem wt_allOnes : wt (allOnes 8) = 8 := by
  decide

theorem ne_one_of_nonsing {y : D8} (hy : IsNonsing y) : y ≠ 1 := by
  obtain ⟨m, rfl, hm⟩ := hy
  intro h
  rcases (mk_eq_one_iff m).1 h with rfl | rfl
  · rw [show ((1 : ↥(coreMod 8)) : PermMod 8) = 1 from rfl, wt_one] at hm
    exact absurd hm (by norm_num)
  · rw [show ((eOm : ↥(coreMod 8)) : PermMod 8) = allOnes 8 from rfl, wt_allOnes] at hm
    exact absurd hm (by norm_num)

theorem not_nonsing_of_T_fixed [Finite G] (F : Frame126 T L V) (hH : Hyp126 G T L V) {w : ↥V}
    (hw : ∀ t ∈ T, t * (w : G) = w * t) : ¬ IsNonsing (F.β w) := by
  intro hn
  rcases T_fixed F hH hw with h | h
  · exact ne_one_of_nonsing hn h
  · exact not_nonsing_and_wt4 hn h

omit [IsMulCommutative ↥V] in
theorem mem_normalizer_of_TI {M : Subgroup G}
    (hTI : ∀ m ∈ M, CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥) {v c : G}
    (hvV : v ∈ V) (hv1 : v ≠ 1) (hcM : c ∈ M) (hcv : c * v = v * c) :
    c ∈ Subgroup.normalizer (V : Set G) := by
  rcases hTI c hcM with h | h
  · have h1 : c⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h
    simpa using Subgroup.inv_mem _ h1
  · exfalso
    apply hv1
    have hmem : v ∈ V ⊓ CFSG.conjugate V c := by
      refine ⟨hvV, v, hvV, ?_⟩
      change c⁻¹ * v * c⁻¹⁻¹ = v
      rw [inv_inv, mul_assoc, ← hcv, inv_mul_cancel_left]
    rw [h] at hmem
    exact hmem

theorem not_two_central [Finite G] (h1262 : Theorem12_6_2) (h1222 : Stmt12_2_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G} (hv : F.Nonsing v) {S : Subgroup G}
    (hS : quasithinIsSylowTwo S) : ¬ S ≤ Subgroup.centralizer ({v} : Set G) := by
  intro hSv
  have hyp := hH.hyp
  obtain ⟨hvV, hvn⟩ := hv
  have hCM := h1262 G T L V F hH v ⟨hvV, hvn⟩
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, hTI, -, -⟩ := hall V hyp.irrPlus
  have hv1 : v ≠ 1 := by
    intro h
    apply ne_one_of_nonsing hvn
    have : (⟨v, hvV⟩ : ↥V) = 1 := Subtype.ext h
    rw [this, map_one]
  have hCN : Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G) := by
    intro c hc
    refine ⟨hCM hc, mem_normalizer_of_TI hTI hvV hv1 (hCM hc) ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 hc
  have hSM : S ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G) :=
    hSv.trans hCN
  have hTM : T ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G) :=
    le_inf hyp.normalizes hTV
  obtain ⟨h, hhM, hh⟩ := A4.exists_conj_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTM)
    (isSylowTwoOf_of_quasithinIsSylowTwo hS hSM)
  have hwV : h⁻¹ * v * h ∈ V := by
    have := conj_mem (Subgroup.inv_mem _ hhM.2) ⟨v, hvV⟩
    simpa using this
  have hwT : ∀ t ∈ T, t * (h⁻¹ * v * h) = (h⁻¹ * v * h) * t := by
    intro t ht
    have hst : h * t * h⁻¹ ∈ S := (hh _).2 (by simpa [mul_assoc] using ht)
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hSv hst)
    calc t * (h⁻¹ * v * h) = h⁻¹ * ((h * t * h⁻¹) * v) * h := by group
      _ = h⁻¹ * (v * (h * t * h⁻¹)) * h := by rw [h1]
      _ = (h⁻¹ * v * h) * t := by group
  obtain ⟨σ, hσ⟩ := exists_actsAs F hH (Subgroup.inv_mem _ hhM.1) (Subgroup.inv_mem _ hhM.2)
  have hwn : IsNonsing (F.β ⟨h⁻¹ * v * h, hwV⟩) :=
    (hasWt_iff F hσ ⟨v, hvV⟩ ⟨h⁻¹ * v * h, hwV⟩ (by simp)).2 hvn
  exact not_nonsing_of_T_fixed F hH (w := ⟨h⁻¹ * v * h, hwV⟩) hwT hwn

end S126N

end CFSG.Quasithin.H13
