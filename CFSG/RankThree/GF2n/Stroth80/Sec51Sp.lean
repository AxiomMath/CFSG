module

public import CFSG.RankThree.GF2n.Stroth80.Sec5PtsCore
public import CFSG.RankThree.GF2n.Stroth80.Sec51Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec311Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Symplectic
open CFSG.ClassicalGroups.Alternating (Lsp Tsp Tsp_app Tsp_mem_Lsp)
open scoped commutatorElement Matrix

section SpMatrix

variable {m : ℕ} {K : Type} [Field K]

theorem exists_transvection_LspGL (u : Fin m ⊕ Fin m → K) :
    ∃ A ∈ LspGL m K u, ∀ x : Fin m ⊕ Fin m → K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = x + spForm m K x u • u := by
  set g := Tsp (spForm_isAlt (m := m) (K := K)) u 1 with hg
  set A : StatedSp m K := (spEquiv (m := m) (K := K)).symm g with hA
  refine ⟨(A : GL (Fin m ⊕ Fin m) K), mem_LspGL_iff.mpr ⟨A.2, ?_⟩, fun x => ?_⟩
  · have : spEquiv (m := m) (K := K) ⟨(A : GL (Fin m ⊕ Fin m) K), A.2⟩ = g := by
      show spEquiv (m := m) (K := K) A = g
      rw [hA, MulEquiv.apply_symm_apply]
    rw [this]
    exact Tsp_mem_Lsp _ _ _
  · have h1 := spEquiv_app A x
    rw [hA, MulEquiv.apply_symm_apply, hg, Tsp_app] at h1
    rw [← h1, one_mul]

theorem spForm_conj_mulVec {g A : GL (Fin m ⊕ Fin m) K} (hg : g ∈ StatedSp m K)
    (u : Fin m ⊕ Fin m → K) :
    spForm m K u
        (((g⁻¹ * A * g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) =
      spForm m K ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)
        ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)) := by
  have hinv := (mem_statedSp_iff_forall g).mp hg
  have hgg : (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      ((g⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set w := (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
    ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) with hw
  have e : ((g⁻¹ * A * g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u =
      ((g⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w := by
    simp only [Units.val_mul, hw, Matrix.mulVec_mulVec, mul_assoc]
  have h1 : (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
      (((g⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  rw [e]
  calc spForm m K u (((g⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w)
      = spForm m K ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)
        ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          (((g⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w)) :=
        (hinv u _).symm
    _ = spForm m K ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) w := by rw [h1]

theorem LspGL_mulVec_self {u : Fin m ⊕ Fin m → K} {A : GL (Fin m ⊕ Fin m) K}
    (hA : A ∈ LspGL m K u) : (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u := by
  obtain ⟨-, w, c, hw, h⟩ := mem_LspGL_iff_siegel.mp hA
  rw [h u, spForm_self, hw]
  simp

end SpMatrix


variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem not_slNat_of_form (hc : Ctx M Q Z B) {t : G} (hsl : SLNat hc t) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Subgroup (GL ι K)}
    (hnat : NaturalRep (ι := ι) K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t))
    (hι : 3 ≤ Fintype.card ι) (F : (ι → K) →+ (ι → K) →+ K)
    (hinv : ∀ g : GL ι K, g ∈ X → ∀ x y : ι → K,
      F ((g : Matrix ι ι K) *ᵥ x) ((g : Matrix ι ι K) *ᵥ y) = F x y)
    (hne : ∃ x y : ι → K, F x y ≠ 0) : False := by
  obtain ⟨K', fK', finK', hK', m', hm', hnat'⟩ := hsl
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have c1 := card_of_naturalRep hnat sec39_Z_le_Vt hK
  have c2 := card_of_naturalRep hnat' sec39_Z_le_Vt hK'
  rw [c1] at c2
  have c3 := Nat.eq_of_mul_eq_mul_left (by omega) c2
  simp only [Fintype.card_fin] at c3
  have hm'eq : m' = Fintype.card ι := (Nat.pow_right_injective hq2 c3).symm
  obtain ⟨φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hnat
  obtain ⟨φ', hφ', hker', hnorm', hn', ψ', hψ'⟩ := hnat'
  haveI := hn
  let e : Multiplicative (Fin m' → K') ≃* Multiplicative (ι → K) := ψ'.symm.trans ψ
  let Θ : (Fin m' → K') →+ (ι → K) :=
    AddMonoidHom.mk' (fun x => Multiplicative.toAdd (e (Multiplicative.ofAdd x)))
      (fun a b => by rw [ofAdd_add, map_mul, toAdd_mul])
  have hΘ : ∀ (s : ↥(Rt M (LB M Q B) t)) (x : Fin m' → K'),
      Θ ((φ' s : Matrix (Fin m') (Fin m') K') *ᵥ x) = (φ s : Matrix ι ι K) *ᵥ Θ x := by
    intro s x
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (ψ'.symm (Multiplicative.ofAdd x))
    have hx : x = Multiplicative.toAdd (ψ' (QuotientGroup.mk v)) := by
      rw [hv, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    set w : ↥(Vt M (LB M Q B) B Z t) := ⟨(s : G) * v * (s : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hnorm s.2) v).mp v.2⟩ with hw
    have h1 := hψ' s v w rfl
    have h2 := hψ s v w rfl
    have eΘx : Θ x = Multiplicative.toAdd (ψ (QuotientGroup.mk v)) := by
      show Multiplicative.toAdd (e (Multiplicative.ofAdd x)) = _
      simp only [e, MulEquiv.trans_apply]
      rw [hv]
    have eΘy : Θ ((φ' s : Matrix (Fin m') (Fin m') K') *ᵥ x) =
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) := by
      have h1' : (φ' s : Matrix (Fin m') (Fin m') K') *ᵥ x =
          Multiplicative.toAdd (ψ' (QuotientGroup.mk w)) := by rw [hx]; exact h1.symm
      rw [h1']
      show Multiplicative.toAdd (e (Multiplicative.ofAdd
        (Multiplicative.toAdd (ψ' (QuotientGroup.mk w))))) = _
      simp only [e, MulEquiv.trans_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply]
    rw [eΘy, eΘx]
    exact h2
  let β : (Fin m' → K') →+ (Fin m' → K') →+ K :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => F (Θ x) (Θ y))
      (fun a b => by rw [map_add, map_add])) (fun a b => AddMonoidHom.ext fun y => by
        show F (Θ (a + b)) (Θ y) = F (Θ a) (Θ y) + F (Θ b) (Θ y)
        simp only [map_add, AddMonoidHom.add_apply])
  have hinvβ : ∀ g : GL (Fin m') K', g ∈ StatedSL m' K' → ∀ x y : Fin m' → K',
      β ((g : Matrix (Fin m') (Fin m') K') *ᵥ x) ((g : Matrix (Fin m') (Fin m') K') *ᵥ y) =
        β x y := by
    intro g hg x y
    rw [← hφ'] at hg
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hg
    show F (Θ _) (Θ _) = F (Θ x) (Θ y)
    rw [hΘ, hΘ]
    have hs : φ s ∈ X := hφ ▸ MonoidHom.mem_range.mpr ⟨s, rfl⟩
    exact hinv _ hs _ _
  have hm3 : 3 ≤ m' := by omega
  have hΘsurj : ∀ u : ι → K, ∃ x, Θ x = u := fun u =>
    ⟨Multiplicative.toAdd (e.symm (Multiplicative.ofAdd u)), by
      show Multiplicative.toAdd (e (Multiplicative.ofAdd
        (Multiplicative.toAdd (e.symm (Multiplicative.ofAdd u))))) = u
      simp⟩
  obtain ⟨u₁, u₂, hu⟩ := hne
  obtain ⟨x₁, hx₁⟩ := hΘsurj u₁
  obtain ⟨x₂, hx₂⟩ := hΘsurj u₂
  have h0 := biadd_eq_zero_of_SL hm3 β hinvβ x₁ x₂
  change F (Θ x₁) (Θ x₂) = 0 at h0
  rw [hx₁, hx₂] at h0
  exact hu h0

@[expose] def bilinAddHom {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : V →+ V →+ K :=
  AddMonoidHom.mk' (fun x => (B x).toAddMonoidHom) (fun a b => AddMonoidHom.ext fun y => by
    show B (a + b) y = B a y + B b y
    simp only [map_add, LinearMap.add_apply])

theorem bilinAddHom_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (x y : V) : bilinAddHom B x y = B x y := rfl

theorem not_slNat_of_spNat (hc : Ctx M Q Z B) {t : G} (hsp : SpNat hc t) : ¬ SLNat hc t := by
  intro hsl
  obtain ⟨K, fK, finK, hK, m, hm, hnat⟩ := hsp
  refine not_slNat_of_form hc hsl hK hnat
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) (bilinAddHom (spForm m K))
    (fun g hg x y => by
      rw [bilinAddHom_apply, bilinAddHom_apply]
      exact (mem_statedSp_iff_forall g).mp hg x y)
    ⟨Pi.single (Sum.inl ⟨0, by omega⟩) 1, Pi.single (Sum.inr ⟨0, by omega⟩) 1, ?_⟩
  rw [bilinAddHom_apply, spForm_single_inl_inr]
  simp

theorem sec51_sp (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h311a : Stroth311aStatement) (h311bC : Stroth311bCommStatement)
    (h311bK : Stroth311bCardStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ (C L L' N R : Subgroup G), C = conjSubgroup r B → L = LB M Q B → L' = LB M Q C →
        N = hc.CN t → R = Rt M L t →
        (∀ x ∈ N, ∃ a ∈ L ⊓ N, ∃ b ∈ L' ⊓ N, x = a * b) ∧
        Nat.card ↥(L ⊓ L') = Nat.card Q * Nat.card Z ∧
        (∀ s ∈ R, ∀ x ∈ L ⊓ L', ⁅s, x⁆ ∈ Q) ∧
        IsOppDecomp N (L ⊓ L') L L' (L ⊓ N) (L' ⊓ N) := by
  intro G _ _ M Q Z B hc n t hs hnat r hr hplane C L L' N R hC hL hL' hN hR
  subst hC hL hL' hN hR
  have hnat' := hnat
  obtain ⟨T, hT⟩ := exists_centLB hc t
  obtain ⟨K, fK, finK, hK, m, hm, φ, hφ, hker, hact⟩ := hnat
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  obtain ⟨u, hu0, hL, hr'⟩ := hc.sp_points h34 hRoot hs hK hm φ hφ hker hact
  have hnotSL := not_slNat_of_spNat hc hnat'
  have hRM : Rt M (LB M Q B) t ≤ M := fun x hx => hc.Rt_le_M t hx
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (LB M Q B) hs.mem
  have hu'ne : ∀ s : ↥(Rt M (LB M Q B) t), spForm m K u
      ((φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0 →
      (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u ≠ 0 := fun s h h0 => h (by
    rw [h0, map_zero])
  have hRne : Rt M (LB M Q B) t ≠ LB M Q B := by
    intro heq
    have hne := (hr' ⟨r, hr⟩).1.mp hplane
    have hrL : r ∈ LB M Q B := heq ▸ hr
    have hmem : φ ⟨r, hr⟩ ∈ LspGL m K u := by
      rw [← hL]
      exact ⟨⟨r, hr⟩, Subgroup.mem_subgroupOf.mpr hrL, rfl⟩
    exact hne (by rw [LspGL_mulVec_self hmem, spForm_self])
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hL35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.2.1
  have hN311 := h311a G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen t hs.mem hs.notQ hRne
  have hTcard := h311bK G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen t hs.mem hs.notQ hRne
    hnotSL T hT
  have hNNT := h311bC G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen t hs.mem hs.notQ hRne
    hnotSL T hT
  have hNN : ⁅hc.CN t, hc.CN t⁆ ≤ LB M Q B := hNNT.trans (fun x hx => ((hT x).mp hx).1)
  refine hc.sec51_assembly hs h35 hN311 hNN T hT hTcard hL35 ?_ ?_ ?_ ?_ ?_ ?_ r hr hplane
  ·
    intro s hs' hpl
    have hne := (hr' ⟨s, hs'⟩).1.mp hpl
    have hL2 := (hr' ⟨s, hs'⟩).2
    rw [← hc.LB_conj (hRM hs')] at hL2
    exact le_sup_secSp φ hφ hker hne hL hL2
  ·
    intro s hs' hpl x hx
    have hne := (hr' ⟨s, hs'⟩).1.mp hpl
    have hL2 := (hr' ⟨s, hs'⟩).2
    rw [← hc.LB_conj (hRM hs')] at hL2
    have hxR : x ∈ Rt M (LB M Q B) t := hLR hx.1
    have h1 : φ ⟨x, hxR⟩ ∈ LspGL m K u := by
      rw [← hL]
      exact ⟨⟨x, hxR⟩, Subgroup.mem_subgroupOf.mpr hx.1, rfl⟩
    have h2 : φ ⟨x, hxR⟩ ∈ LspGL m K
        ((φ ⟨s, hs'⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) := by
      rw [← hL2]
      exact ⟨⟨x, hxR⟩, Subgroup.mem_subgroupOf.mpr hx.2, rfl⟩
    have h3 : φ ⟨x, hxR⟩ ∈ LspGL m K u ⊓ LspGL m K
        ((φ ⟨s, hs'⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) := ⟨h1, h2⟩
    rw [(LspGL_inf_eq_bot_iff hu0 (hu'ne ⟨s, hs'⟩ hne)).mpr hne, Subgroup.mem_bot] at h3
    have h4 : (⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := h3
    rw [hker] at h4
    exact Subgroup.mem_subgroupOf.mp h4
  ·
    intro s hs' hpl
    have hne := (hr' ⟨s, hs'⟩).1.mp hpl
    obtain ⟨A, hA, hAx⟩ := exists_transvection_LspGL u
    rw [← hL] at hA
    obtain ⟨l, hl, hlA⟩ := hA
    refine ⟨(l : G), Subgroup.mem_subgroupOf.mp hl, ?_⟩
    set s' : ↥(Rt M (LB M Q B) t) := ⟨s, hs'⟩ with hs'def
    have hr1 := (hr' (s'⁻¹ * l * s')).1
    have hcoe : ((s'⁻¹ * l * s' : ↥(Rt M (LB M Q B) t)) : G) = s⁻¹ * (l : G) * s := rfl
    rw [hcoe] at hr1
    refine hr1.mpr ?_
    have hg : (φ s' : GL (Fin m ⊕ Fin m) K) ∈ StatedSp m K :=
      hφ ▸ MonoidHom.mem_range.mpr ⟨s', rfl⟩
    have hφr : φ (s'⁻¹ * l * s') = (φ s')⁻¹ * A * φ s' := by
      rw [map_mul, map_mul, map_inv, hlA]
    rw [hφr, spForm_conj_mulVec hg, hAx, map_add, map_smul, spForm_self, zero_add, smul_eq_mul]
    have : spForm m K ((φ s' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) u ≠ 0 := by
      rw [← spForm_isAlt.neg_eq]
      exact neg_ne_zero.mpr hne
    exact mul_ne_zero this this
  ·
    intro s hs' hpl
    have hne := (hr' ⟨s, hs'⟩).1.mp hpl
    have hL2 := (hr' ⟨s, hs'⟩).2
    obtain ⟨A, hA, hAx⟩ := exists_transvection_LspGL
      ((φ ⟨s, hs'⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)
    rw [← hL2] at hA
    obtain ⟨l, hl, hlA⟩ := hA
    refine ⟨(l : G), ?_, ?_⟩
    · rw [hc.LB_conj (hRM hs')]
      exact Subgroup.mem_subgroupOf.mp hl
    · refine ((hr' l).1).mpr ?_
      rw [hlA, hAx, map_add, map_smul, spForm_self, zero_add, smul_eq_mul]
      exact mul_ne_zero hne hne
  ·
    intro s hs' hpl hI hdec
    have hne := (hr' ⟨s, hs'⟩).1.mp hpl
    have hL2 := (hr' ⟨s, hs'⟩).2
    rw [← hc.LB_conj (hRM hs')] at hL2
    obtain ⟨n', hn'⟩ := stroth_2_1_ii_secSp (m := m) (by omega) φ hφ hker
      (fun ρ hρ x hx => hc.CN_conj_mem hs.mem hρ hx) hI
      (fun x hx y hy => hdec.2.2.2.2.2.2.1 x hx y hy) hdec hLR
      (hc.LB_conj_le_Rt_of_mem hs.mem hs') hne hL hL2
    refine ⟨2 ^ m * n', ?_, by rw [hn', hK]⟩
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right n'
  ·
    refine ⟨2 * m - 1, ?_⟩
    have h := card_inf_mul_card_map hLR φ hker
    rw [hL, card_LspGL hu0, hK] at h
    exact h

end CFSG.RankThree.GF2n.Stroth80
