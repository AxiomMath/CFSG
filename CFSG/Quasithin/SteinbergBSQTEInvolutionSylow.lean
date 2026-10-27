module

public import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore
public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianRankOne
public import CFSG.LieType.CentralExt.CoprimeLift

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup CFSG.Wreathed.OddLinearThreeCentralizerCore CFSG.LieType.CentralExt

namespace QTEInvolutionSylow

section Abstract

variable {H : Type*} [Group H] [Finite H]

theorem twoLocal_of_small_centralizers {c : H} (hc : c ∈ center H) (hc2 : orderOf c = 2)
    (hsmall : ∀ a : H, a * a = 1 → a ≠ 1 → a ≠ c →
      (Nat.card (centralizer ({a} : Set H))).factorization 2 < (Nat.card H).factorization 2 ∧
      ∀ E : Subgroup H, E ≤ centralizer ({a} : Set H) → (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 4) :
    (∀ S : Subgroup H, IsPGroup 2 S → Nat.card S = 2 ^ (Nat.card H).factorization 2 →
      IsCyclic (center S)) ∧
    ∀ E : Subgroup H, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun S hS hcard => ?_, fun E hcomm hexp => ?_⟩
  ·
    have hcS : c ∈ S := by
      let P : Sylow 2 H := Sylow.ofCard S hcard
      have hN : (zpowers c).Normal := normal_of_le_center (zpowers_le.2 hc)
      have hzp : IsPGroup 2 (zpowers c) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc2, pow_one])
      exact IsPGroup.le_sylow_of_normal hzp P (mem_zpowers c)
    have hkey : ∀ x : center S, orderOf x = 2 → ((x : S) : H) = c := by
      intro x hx
      by_contra hxc
      have hxH : orderOf ((x : S) : H) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
      have ha2 : ((x : S) : H) * ((x : S) : H) = 1 := by
        rw [← sq, ← hxH, pow_orderOf_eq_one]
      have ha1 : ((x : S) : H) ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hxH
        exact absurd hxH (by norm_num)
      obtain ⟨hlt, -⟩ := hsmall _ ha2 ha1 hxc
      have hSC : S ≤ centralizer ({((x : S) : H)} : Set H) := by
        intro s hs
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (mem_center_iff.1 x.2 ⟨s, hs⟩)
      have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (card_dvd_of_le hSC) 2
      rw [hcard, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at hle
      omega
    have huniq : ∀ x y : center S, orderOf x = 2 → orderOf y = 2 → x = y := by
      intro x y hx hy
      apply Subtype.ext
      apply Subtype.ext
      rw [hkey x hx, hkey y hy]
    have hZ2 : IsPGroup 2 (center S) := hS.to_subgroup (center S)
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    let _ : CommGroup (center S) :=
      { (inferInstance : Group (center S)) with
        mul_comm := fun a b => Subtype.ext ((mem_center_iff.1 b.2) a) }
    exact
      CFSG.TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
        k (center S) hZ2 hk huniq
  · by_cases h : ∃ a ∈ E, a ≠ 1 ∧ a ≠ c
    · obtain ⟨a, haE, ha1, hac⟩ := h
      refine (hsmall a (hexp a haE) ha1 hac).2 E (fun x hx => ?_) hexp
      rw [mem_centralizer_singleton_iff]
      exact hcomm x hx a haE
    · push Not at h
      have hle : E ≤ zpowers c := fun x hx => by
        by_cases hx1 : x = 1
        · rw [hx1]
          exact one_mem _
        · rw [h x hx hx1]
          exact mem_zpowers c
      calc Nat.card E ≤ Nat.card (zpowers c) := card_le_of_le hle
        _ = 2 := by rw [Nat.card_zpowers, hc2]
        _ ≤ 4 := by norm_num

theorem sylow_transfer {A : Type*} [Group A] [Finite A] {t : A}
    (φ : H →* centralizer ({t} : Set A)) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ center H) (hodd : Odd (Nat.card φ.ker))
    (hH1 : ∀ S : Subgroup H, IsPGroup 2 S → Nat.card S = 2 ^ (Nat.card H).factorization 2 →
      IsCyclic (center S))
    (hH2 : ∀ E : Subgroup H, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E ≤ 4)
    (T : Sylow 2 A) (hTt : (T : Subgroup A) ≤ centralizer ({t} : Set A)) :
    IsCyclic (center (T : Subgroup A)) ∧
      ∀ E : Subgroup A, E ≤ T → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC2 : ¬ 2 ∣ Nat.card φ.ker := fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  have hlift : ∀ U : Subgroup A, U ≤ centralizer ({t} : Set A) → IsPGroup 2 U →
      ∃ Û : Subgroup H, Nonempty (Û ≃* U) := by
    intro U hUC hU
    have hU' : IsPGroup 2 (U.subgroupOf (centralizer ({t} : Set A))) :=
      hU.of_equiv (subgroupOfEquivOfLe hUC).symm
    exact ⟨liftSubgroup 2 φ (U.subgroupOf (centralizer ({t} : Set A))),
      ⟨(liftSubgroupEquiv hφ hcen hC2 hU').trans (subgroupOfEquivOfLe hUC)⟩⟩
  have hcardH : Nat.card H = Nat.card φ.ker * Nat.card (centralizer ({t} : Set A)) := by
    rw [← card_mul_index φ.ker, index_ker, MonoidHom.range_eq_top.2 hφ, card_top]
  have hTcard := T.card_eq_multiplicity
  have hfacC : (Nat.card (centralizer ({t} : Set A))).factorization 2 =
      (Nat.card A).factorization 2 := by
    apply le_antisymm
    · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (card_subgroup_dvd_card _) 2
    · have hdvd : Nat.card (T : Subgroup A) ∣ Nat.card (centralizer ({t} : Set A)) := by
        rw [← Nat.card_congr (subgroupOfEquivOfLe hTt).toEquiv]
        exact card_subgroup_dvd_card _
      have := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd 2
      rwa [hTcard, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at this
  have hfacH : (Nat.card H).factorization 2 = (Nat.card A).factorization 2 := by
    rw [hcardH, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hC2, zero_add, hfacC]
  obtain ⟨Û, ⟨eT⟩⟩ := hlift T hTt T.isPGroup'
  refine ⟨?_, fun E hET hcomm hexp => ?_⟩
  · have hÛ : IsPGroup 2 Û := T.isPGroup'.of_equiv eT.symm
    have hcardÛ : Nat.card Û = 2 ^ (Nat.card H).factorization 2 := by
      rw [Nat.card_congr eT.toEquiv, hTcard, hfacH]
    have := hH1 Û hÛ hcardÛ
    exact isCyclic_of_surjective (centerCongr eT).toMonoidHom (centerCongr eT).surjective
  · obtain ⟨Ê, ⟨eE⟩⟩ := hlift E (hET.trans hTt) (T.isPGroup'.to_le hET)
    rw [← Nat.card_congr eE.toEquiv]
    refine hH2 Ê (fun x hx y hy => ?_) (fun x hx => ?_)
    · have h := hcomm _ (eE ⟨x, hx⟩).2 _ (eE ⟨y, hy⟩).2
      have h' : eE (⟨x, hx⟩ * ⟨y, hy⟩) = eE (⟨y, hy⟩ * ⟨x, hx⟩) := by
        rw [map_mul, map_mul]
        exact Subtype.ext h
      exact congrArg Subtype.val (eE.injective h')
    · have h := hexp _ (eE ⟨x, hx⟩).2
      have h' : eE (⟨x, hx⟩ * ⟨x, hx⟩) = eE 1 := by
        rw [map_mul, map_one]
        exact Subtype.ext h
      exact congrArg Subtype.val (eE.injective h')

end Abstract

section TwoDim

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W]

theorem comm_of_mem_centralizer {a g : W ≃ₗ[E] W}
    (hg : g ∈ centralizer ({a} : Set (W ≃ₗ[E] W))) :
    ∀ v, (a : Module.End E W) (g v) = g ((a : Module.End E W) v) := by
  intro v
  have h := congrArg (fun e : W ≃ₗ[E] W => e v) (mem_centralizer_singleton_iff.1 hg)
  simp only [LinearEquiv.mul_apply] at h
  exact h.symm

theorem eigenspaceRestriction_one (f : Module.End E W) (μ : E)
    (hc : ∀ v, f ((1 : W ≃ₗ[E] W) v) = (1 : W ≃ₗ[E] W) (f v)) :
    eigenspaceRestriction f μ 1 hc = 1 :=
  LinearEquiv.ext fun x => Subtype.ext (eigenspaceRestriction_apply f μ 1 hc x)

theorem eigenspaceRestriction_mul (f : Module.End E W) (μ : E) (g h : W ≃ₗ[E] W)
    (hg : ∀ v, f (g v) = g (f v)) (hh : ∀ v, f (h v) = h (f v))
    (hgh : ∀ v, f ((g * h) v) = (g * h) (f v)) :
    eigenspaceRestriction f μ (g * h) hgh =
      eigenspaceRestriction f μ g hg * eigenspaceRestriction f μ h hh := by
  refine LinearEquiv.ext fun x => Subtype.ext ?_
  rw [LinearEquiv.mul_apply, eigenspaceRestriction_apply, eigenspaceRestriction_apply,
    eigenspaceRestriction_apply, LinearEquiv.mul_apply]

variable [FiniteDimensional E W]

@[expose] noncomputable def eigenScalarHom (a : W ≃ₗ[E] W) :
    centralizer ({a} : Set (W ≃ₗ[E] W)) →* Eˣ × Eˣ where
  toFun g := ((eigenspaceRestriction (a : Module.End E W) (-1) g.1
      (comm_of_mem_centralizer g.2)).det,
    (eigenspaceRestriction (a : Module.End E W) 1 g.1 (comm_of_mem_centralizer g.2)).det)
  map_one' := by
    refine Prod.ext ?_ ?_
    · change (eigenspaceRestriction (a : Module.End E W) (-1) 1 _).det = 1
      rw [eigenspaceRestriction_one, map_one]
    · change (eigenspaceRestriction (a : Module.End E W) 1 1 _).det = 1
      rw [eigenspaceRestriction_one, map_one]
  map_mul' g h := by
    refine Prod.ext ?_ ?_
    · change (eigenspaceRestriction (a : Module.End E W) (-1) (g.1 * h.1) _).det =
        (eigenspaceRestriction (a : Module.End E W) (-1) g.1 _).det *
          (eigenspaceRestriction (a : Module.End E W) (-1) h.1 _).det
      rw [eigenspaceRestriction_mul _ _ _ _ (comm_of_mem_centralizer g.2)
        (comm_of_mem_centralizer h.2), map_mul]
    · change (eigenspaceRestriction (a : Module.End E W) 1 (g.1 * h.1) _).det =
        (eigenspaceRestriction (a : Module.End E W) 1 g.1 _).det *
          (eigenspaceRestriction (a : Module.End E W) 1 h.1 _).det
      rw [eigenspaceRestriction_mul _ _ _ _ (comm_of_mem_centralizer g.2)
        (comm_of_mem_centralizer h.2), map_mul]

theorem finrank_eigenspaces_eq_one (h2 : (2 : E) ≠ 0) (hW : Module.finrank E W = 2)
    {a : W ≃ₗ[E] W} (ha2 : a * a = 1) (ha1 : a ≠ 1) (han : a ≠ LinearEquiv.neg E) :
    Module.finrank E (minusSpace (a : Module.End E W)) = 1 ∧
      Module.finrank E (plusSpace (a : Module.End E W)) = 1 := by
  have hinv : Function.Involutive (a : Module.End E W) := fun v => by
    have h := congrArg (fun e : W ≃ₗ[E] W => e v) ha2
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq, LinearEquiv.coe_coe] using h
  have hcompl := involution_spaces_isCompl h2 (a : Module.End E W) hinv
  have hsum := involution_finrank_sum h2 (a : Module.End E W) hinv
  have hm : Module.finrank E (minusSpace (a : Module.End E W)) ≠ 0 := by
    intro h0
    apply ha1
    have := involution_eq_id_of_minus_bot h2 (a : Module.End E W) hinv
      (Submodule.finrank_eq_zero.1 h0)
    exact LinearEquiv.toLinearMap_injective this
  have hp : Module.finrank E (plusSpace (a : Module.End E W)) ≠ 0 := by
    intro h0
    apply han
    have hplus : plusSpace (a : Module.End E W) = ⊥ := Submodule.finrank_eq_zero.1 h0
    have hminus : minusSpace (a : Module.End E W) = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [hplus, sup_bot_eq] at this
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ minusSpace (a : Module.End E W) := by
      rw [hminus]
      exact Submodule.mem_top
    have := Module.End.mem_eigenspace_iff.1 hv
    rw [LinearEquiv.neg_apply, ← neg_one_smul E v]
    exact this
  rw [hW] at hsum
  omega

theorem eigenScalarHom_injective (h2 : (2 : E) ≠ 0) (hW : Module.finrank E W = 2)
    {a : W ≃ₗ[E] W} (ha2 : a * a = 1) (ha1 : a ≠ 1) (han : a ≠ LinearEquiv.neg E) :
    Function.Injective (eigenScalarHom a) := by
  obtain ⟨hm, hp⟩ := finrank_eigenspaces_eq_one h2 hW ha2 ha1 han
  have hinv : Function.Involutive (a : Module.End E W) := fun v => by
    have h := congrArg (fun e : W ≃ₗ[E] W => e v) ha2
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq, LinearEquiv.coe_coe] using h
  have hcompl := involution_spaces_isCompl h2 (a : Module.End E W) hinv
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ μ : E, Module.finrank E (Module.End.eigenspace (a : Module.End E W) μ) = 1 →
      (eigenspaceRestriction (a : Module.End E W) μ g.1 (comm_of_mem_centralizer g.2)).det = 1 →
      ∀ x : Module.End.eigenspace (a : Module.End E W) μ, g.1 x = x := by
    intro μ hμ hdet x
    have h := line_equiv_eq_smul_det hμ
      (eigenspaceRestriction (a : Module.End E W) μ g.1 (comm_of_mem_centralizer g.2))
    rw [hdet] at h
    have hx := congrArg (fun e => ((e x : Module.End.eigenspace (a : Module.End E W) μ) : W)) h
    simp only [eigenspaceRestriction_apply] at hx
    rw [hx]
    exact one_smul Eˣ (x : W)
  have h₁ := hfix (-1) hm (congrArg Prod.fst hg)
  have h₂ := hfix 1 hp (congrArg Prod.snd hg)
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨x, hx, y, hy, rfl⟩ :=
    Submodule.mem_sup.1 (hcompl.sup_eq_top ▸ Submodule.mem_top (x := v))
  rw [map_add, h₁ ⟨x, hx⟩, h₂ ⟨y, hy⟩]
  rfl

theorem card_le_four_of_le_centralizer (h2 : (2 : E) ≠ 0) (hW : Module.finrank E W = 2)
    {a : W ≃ₗ[E] W} (ha2 : a * a = 1) (ha1 : a ≠ 1) (han : a ≠ LinearEquiv.neg E)
    {Q : Subgroup (W ≃ₗ[E] W)} (hQ : Q ≤ centralizer ({a} : Set (W ≃ₗ[E] W)))
    (hexp : ∀ x ∈ Q, x * x = 1) : Nat.card Q ≤ 4 := by
  have hsq : ∀ x : Q, eigenScalarHom a ⟨x, hQ x.2⟩ ^ 2 = 1 := by
    intro x
    rw [← map_pow]
    have : (⟨x, hQ x.2⟩ : centralizer ({a} : Set (W ≃ₗ[E] W))) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact hexp x x.2)
    rw [this, map_one]
  let f : Q → rootsOfUnity 2 E × rootsOfUnity 2 E := fun x =>
    (⟨(eigenScalarHom a ⟨x, hQ x.2⟩).1, (mem_rootsOfUnity 2 _).2 (by
      rw [← Prod.pow_fst, hsq x, Prod.fst_one])⟩,
     ⟨(eigenScalarHom a ⟨x, hQ x.2⟩).2, (mem_rootsOfUnity 2 _).2 (by
      rw [← Prod.pow_snd, hsq x, Prod.snd_one])⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    have h : eigenScalarHom a ⟨x, hQ x.2⟩ = eigenScalarHom a ⟨y, hQ y.2⟩ :=
      Prod.ext (congrArg (fun z => ((z.1 : rootsOfUnity 2 E) : Eˣ)) hxy)
        (congrArg (fun z => ((z.2 : rootsOfUnity 2 E) : Eˣ)) hxy)
    have h' : (x : W ≃ₗ[E] W) = y :=
      congrArg (fun z : centralizer ({a} : Set (W ≃ₗ[E] W)) => (z : W ≃ₗ[E] W))
        (eigenScalarHom_injective h2 hW ha2 ha1 han h)
    exact Subtype.ext h'
  calc Nat.card Q ≤ Nat.card (rootsOfUnity 2 E × rootsOfUnity 2 E) :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card (rootsOfUnity 2 E) * Nat.card (rootsOfUnity 2 E) := Nat.card_prod _ _
    _ ≤ 2 * 2 := Nat.mul_le_mul (card_rootsOfUnity E 2) (card_rootsOfUnity E 2)
    _ = 4 := rfl

end TwoDim

section LinearTwo

variable {E : Type*} [Field E] [Finite E] {W : Type*} [AddCommGroup W] [Module E W]
  [FiniteDimensional E W]

theorem finite_linearEquiv : Finite (W ≃ₗ[E] W) := by
  have : Finite W := Module.finite_of_finite E
  exact Finite.of_injective (fun e : W ≃ₗ[E] W => (e : W → W)) DFunLike.coe_injective

theorem card_linearEquiv_of_finrank_two (hW : Module.finrank E W = 2) :
    Nat.card (W ≃ₗ[E] W) = (Nat.card E ^ 2 - 1) * (Nat.card E ^ 2 - Nat.card E) := by
  have := Fintype.ofFinite E
  let bW := Module.finBasisOfFinrankEq E W hW
  have h1 : Nat.card (W ≃ₗ[E] W) = Nat.card (Matrix.GeneralLinearGroup (Fin 2) E) :=
    (Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' bW).toEquiv.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv E W).toEquiv)).symm
  rw [h1, Matrix.card_GL_field, Fin.prod_univ_two, Nat.card_eq_fintype_card]
  simp

omit [Finite E] [FiniteDimensional E W] in
theorem neg_mem_center_orderOf (h2 : (2 : E) ≠ 0) [Nontrivial W] :
    LinearEquiv.neg E ∈ center (W ≃ₗ[E] W) ∧ orderOf (LinearEquiv.neg E : W ≃ₗ[E] W) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨mem_center_iff.2 fun g => LinearEquiv.ext fun v => ?_, orderOf_eq_prime ?_ ?_⟩
  · simp only [LinearEquiv.mul_apply, LinearEquiv.neg_apply, map_neg]
  · exact LinearEquiv.ext fun v => by
      simp only [sq, LinearEquiv.mul_apply, LinearEquiv.neg_apply, neg_neg,
        LinearEquiv.coe_one, id_eq]
  · intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    have h' := congrArg (fun e : W ≃ₗ[E] W => e v) h
    simp only [LinearEquiv.neg_apply, LinearEquiv.coe_one, id_eq] at h'
    apply hv
    have h2v : (2 : E) • v = 0 := by rw [two_smul]; nth_rewrite 1 [← h']; exact neg_add_cancel v
    exact (smul_eq_zero.1 h2v).resolve_left h2
  
theorem linear_two_twoLocal (hE : Odd (Nat.card E)) (hW : Module.finrank E W = 2) :
    (∀ S : Subgroup (W ≃ₗ[E] W), IsPGroup 2 S →
      Nat.card S = 2 ^ (Nat.card (W ≃ₗ[E] W)).factorization 2 → IsCyclic (center S)) ∧
    ∀ Q : Subgroup (W ≃ₗ[E] W), (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) → (∀ x ∈ Q, x * x = 1) →
      Nat.card Q ≤ 4 := by
  have h2 : (2 : E) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero E hE
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (by rw [hW]; norm_num)
  have := Fintype.ofFinite E
  have : Finite (W ≃ₗ[E] W) := finite_linearEquiv
  obtain ⟨hc, hc2⟩ := neg_mem_center_orderOf (W := W) h2
  refine twoLocal_of_small_centralizers hc hc2 fun a ha2 ha1 han => ⟨?_, fun Q hQ hexp =>
    card_le_four_of_le_centralizer h2 hW ha2 ha1 han hQ hexp⟩
  set q := Nat.card E with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr0 : r ≠ 0 := by
    have : 1 < Nat.card E := Finite.one_lt_card
    omega
  have hdvd := card_dvd_of_injective (eigenScalarHom a) (eigenScalarHom_injective h2 hW ha2 ha1 han)
  rw [Nat.card_prod, Nat.card_units, ← hq, hr, Nat.add_sub_cancel] at hdvd
  have hGL : Nat.card (W ≃ₗ[E] W) = (r * r) * ((r + 2) * (r + 1)) := by
    rw [card_linearEquiv_of_finrank_two hW, ← hq, hr,
      Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = r * (r + 2) + 1 by ring),
      Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = r * (r + 1) + (r + 1) by ring)]
    ring
  have hrr : r * r ≠ 0 := Nat.mul_ne_zero hr0 hr0
  have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hrr).2 hdvd 2
  have heven : 2 ∣ r + 2 := by
    rw [hr] at hE
    obtain ⟨k, hk⟩ := hE
    exact ⟨k + 1, by omega⟩
  have hone := (Nat.prime_two.dvd_iff_one_le_factorization (by omega)).1 heven
  have e1 : (r * r * ((r + 2) * (r + 1))).factorization 2 =
      (r * r).factorization 2 + ((r + 2).factorization 2 + (r + 1).factorization 2) := by
    rw [Nat.factorization_mul (a := r * r) hrr (Nat.mul_ne_zero (by omega) (by omega)),
      Finsupp.add_apply, Nat.factorization_mul (a := r + 2) (b := r + 1) (by omega) (by omega),
      Finsupp.add_apply]
  rw [hGL, e1]
  omega

end LinearTwo

end QTEInvolutionSylow

end CFSG.Quasithin.SteinbergBS
