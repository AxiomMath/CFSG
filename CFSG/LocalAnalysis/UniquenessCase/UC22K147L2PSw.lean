module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2PBN
public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2PTenR
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Omega4Plus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair

open Subgroup CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.QuasithinUnique.Setup.X7b CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Norm
open CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Br CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.Quasithin.G11 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
open scoped MatrixGroups Matrix

section Glue

variable {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]

theorem ten_glue [Nontrivial Y] {H : Type} [Group H] (σ : H →* GLV Y) {L₁ L₂ : Subgroup H}
    (hinj : ∀ x ∈ L₁, σ x = 1 → x = 1) (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    (hirr : ∀ U : Submodule (ZMod 2) Y, (∀ x ∈ L₁ ⊔ L₂, ∀ u ∈ U, σ x u ∈ U) → U = ⊥ ∨ U = ⊤)
    {F₀ : Type} [Field F₀] [Fintype F₀] [CharP F₀ 2] (e₁ : ↥L₁ ≃* SL(2, F₀)) {n : ℕ}
    (hn : 3 ≤ n) (hF₀ : Fintype.card F₀ = 2 ^ n) {t : H} (ht : t * t = 1)
    (ht₁ : ∀ x ∈ L₁, t * x * t ∈ L₂) (ht₂ : ∀ y ∈ L₂, t * y * t ∈ L₁)
    (hδ : Module.finrank (ZMod 2) (LinearMap.range ((σ t : Module.End (ZMod 2) Y) - 1)) ≤
      n + 1) :
    n ≤ Module.finrank (ZMod 2) (LinearMap.range ((σ t : Module.End (ZMod 2) Y) - 1)) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Algebra (ZMod 2) F),
        Nat.card F = 2 ^ n ∧ IsTensorModel 2 F (L₁.map σ ⊔ L₂.map σ) := by
  have hbij : Function.Bijective (σ.subgroupMap L₁) :=
    ⟨(injective_iff_map_eq_one _).mpr fun x hx =>
      Subtype.ext (hinj x x.2 (congrArg Subtype.val hx)), σ.subgroupMap_surjective L₁⟩
  refine ten_core (K₁ := L₁.map σ) (K₂ := L₂.map σ) ?_ ?_
    ((MulEquiv.ofBijective _ hbij).symm.trans e₁) hn hF₀ (τ := σ t) ?_ ?_ ?_ hδ
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, hcomm x hx y hy, map_mul]
  · intro U hU
    refine hirr U fun x hx u hu => hU _ ?_ u hu
    rw [← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem σ hx
  · rw [← map_mul, ht, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨t * x * t, ht₁ x hx, by rw [map_mul, map_mul]⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨t * y * t, ht₂ y hy, by rw [map_mul, map_mul]⟩

end Glue

section Rep

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem finrank_range_sub_one (ρ : Representation (ZMod 2) G V) (t : G) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) =
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t}) := by
  have h := LinearMap.finrank_range_add_finrank_ker (ρ t - 1)
  rw [ker_sub_one_eq_repFixedSpace] at h
  omega

variable {ρ : Representation (ZMod 2) G V} {L L₂ : Subgroup G}

theorem IsPair.le_finrank_inf_range (hP : IsPair L L₂) {F : Type} [Field F] [Fintype F]
    [CharP F 2] (e : ↥L ≃* SL(2, F)) {n : ℕ} (hn : 3 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (hB : fixSub ρ L₂ = ⊥) {t : G} (ht : t * t = 1) (htN : t ∉ normalizer (L : Set G))
    (htd : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t}) ≤ n + 1)
    {M : Submodule (ZMod 2) V} (hM : IsMinInv ρ (L ⊔ L₂) M) :
    n ≤ Module.finrank (ZMod 2) ↥(M ⊓ LinearMap.range (ρ t - 1)) := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have h4 : 4 ≤ Nat.card F := by
    rw [hFn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : IsSimpleGroup SL(2, F) := P22y.isSimpleGroup_sl2 h4
  haveI : IsSimpleGroup ↥L := e.isSimpleGroup
  haveI := hP.sup_normal
  have hBL := hP.fixSub_eq_bot hB
  have hfix : fixSub ρ L ⊓ fixSub ρ L₂ = ⊥ := by rw [hB, inf_bot_eq]
  have hMt : ∀ m ∈ M, ρ t m ∈ M := fun m hm =>
    hP.apply_mem_of_isMinInv e (by omega) hFn hfix hM ht htd hm
  have hMH : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ L₂ ⊔ zpowers t) M := fun h hh m hm =>
    invariant_of_incL_tElt (L ⊔ L₂) t ht (ρ.comp (L ⊔ L₂ ⊔ zpowers t).subtype) M
      (fun l u hu => hM.1 l l.2 u hu) hMt ⟨h, hh⟩ m hm
  haveI : Nontrivial ↥M := Submodule.nontrivial_iff_ne_bot.mpr hM.2.1
  let σ : ↥(L ⊔ L₂ ⊔ zpowers t) →* GLV ↥M :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥M).toMonoidHom.comp
      (restr ρ hMH).asGroupHom
  have hσ : ∀ (h : ↥(L ⊔ L₂ ⊔ zpowers t)) (m : ↥M), ((σ h m : ↥M) : V) = ρ h m := fun h m => by
    simp [σ, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
      Representation.asGroupHom_apply]
  have hLX : L ≤ L ⊔ L₂ ⊔ zpowers t := le_sup_left.trans le_sup_left
  have hL₂X : L₂ ≤ L ⊔ L₂ ⊔ zpowers t := le_sup_right.trans le_sup_left
  let t' : ↥(L ⊔ L₂ ⊔ zpowers t) := ⟨t, mem_sup_right (mem_zpowers t)⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htN₂ : t ∉ normalizer (L₂ : Set G) := fun h => htN (hP.mem_normalizer_iff.mp h)
  have hsub : (LinearMap.range ((σ t' : Module.End (ZMod 2) ↥M) - 1)).map M.subtype ≤
      M ⊓ LinearMap.range (ρ t - 1) := by
    refine le_inf (Submodule.map_subtype_le M _) ?_
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    refine ⟨(m : V), ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, Submodule.subtype_apply,
      LinearEquiv.coe_coe, hσ]
    rfl
  have hfr : Module.finrank (ZMod 2) (LinearMap.range ((σ t' : Module.End (ZMod 2) ↥M) - 1)) ≤
      Module.finrank (ZMod 2) ↥(M ⊓ LinearMap.range (ρ t - 1)) :=
    (Submodule.finrank_map_subtype_eq M _).symm.trans_le (Submodule.finrank_mono hsub)
  have hR : Module.finrank (ZMod 2) ↥(M ⊓ LinearMap.range (ρ t - 1)) ≤ n + 1 :=
    (Submodule.finrank_mono inf_le_right).trans ((finrank_range_sub_one ρ t).trans_le htd)
  have hglue := ten_glue σ (L₁ := L.subgroupOf (L ⊔ L₂ ⊔ zpowers t))
    (L₂ := L₂.subgroupOf (L ⊔ L₂ ⊔ zpowers t)) ?_ ?_ ?_
    ((Subgroup.subgroupOfEquivOfLe hLX).trans e) hn hF (t := t') (Subtype.ext ht) ?_ ?_
    (hfr.trans hR)
  · exact hglue.1.trans hfr
  · intro x hx h1
    by_contra hx1
    obtain ⟨m, hm, hne⟩ := exists_moved_of_ne_one (fun l hl => hM.1 l (mem_sup_left hl))
      (exists_moved_of_fixSub_eq_bot hBL hM.2.1) (mem_subgroupOf.mp hx)
      fun h => hx1 (Subtype.ext h)
    apply hne
    have h2 := congrArg (fun f : GLV ↥M => ((f ⟨m, hm⟩ : ↥M) : V)) h1
    simp only [hσ] at h2
    exact h2
  · intro x hx y hy
    exact Subtype.ext (hP.commute (mem_subgroupOf.mp hx) (mem_subgroupOf.mp hy))
  · intro U hU
    have hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ L₂) (U.map M.subtype) := by
      intro h hh
      refine sup_induction_of_mul
        (C := fun h : G => ∀ v ∈ U.map M.subtype, ρ h v ∈ U.map M.subtype) ?_ ?_
        (fun v hv => by rw [map_one, Module.End.one_apply]; exact hv)
        (fun x y hx hy v hv => by rw [map_mul, Module.End.mul_apply]; exact hx _ (hy v hv)) hh
      · rintro l hl _ ⟨u, hu, rfl⟩
        exact ⟨σ ⟨l, hLX hl⟩ u, hU ⟨l, hLX hl⟩ (mem_sup_left (mem_subgroupOf.mpr hl)) u hu,
          hσ _ u⟩
      · rintro l hl _ ⟨u, hu, rfl⟩
        exact ⟨σ ⟨l, hL₂X hl⟩ u, hU ⟨l, hL₂X hl⟩ (mem_sup_right (mem_subgroupOf.mpr hl)) u hu,
          hσ _ u⟩
    by_cases h0 : U.map M.subtype = ⊥
    · exact Or.inl (Submodule.map_injective_of_injective M.injective_subtype
        (h0.trans (Submodule.map_bot _).symm))
    · exact Or.inr (Submodule.map_injective_of_injective M.injective_subtype
        ((hM.2.2 _ (Submodule.map_subtype_le M U) hinv h0).trans
          (Submodule.map_subtype_top M).symm))
  · intro x hx
    rw [mem_subgroupOf]
    have h1 := hP.conj_mem_of_not_mem htN (mem_subgroupOf.mp hx)
    rw [htinv] at h1
    exact h1
  · intro y hy
    rw [mem_subgroupOf]
    have h1 := hP.symm.conj_mem_of_not_mem htN₂ (mem_subgroupOf.mp hy)
    rw [htinv] at h1
    exact h1

theorem IsPair.isMinInv_top (hP : IsPair L L₂) (hirr : ρ.IsIrreducible) {F : Type} [Field F]
    [Fintype F] [CharP F 2] (e : ↥L ≃* SL(2, F)) {n : ℕ} (hn : 3 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (hB : fixSub ρ L₂ = ⊥) {t : G} (ht : t * t = 1)
    (htN : t ∉ normalizer (L : Set G))
    (htd : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t}) ≤ n + 1) :
    IsMinInv ρ (L ⊔ L₂) ⊤ := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨hVnt, hirr'⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr
  haveI := hVnt
  obtain ⟨M, -, hM⟩ := exists_isMinInv ρ (K := L ⊔ L₂) (U := ⊤)
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have hMG : ∀ g : G, M.map (ρ g) = M := by
    intro g
    by_contra hne
    have hM' := hM.map hP.sup_normal g
    have hinf : M ⊓ M.map (ρ g) = ⊥ := by
      by_contra h0
      have h1 := hM.2.2 _ inf_le_left
        (fun x hx v hv => ⟨hM.1 x hx v hv.1, hM'.1 x hx v hv.2⟩) h0
      have h2 : M ≤ M.map (ρ g) := h1.symm.le.trans inf_le_right
      exact hne (hM'.2.2 M h2 hM.1 hM.2.1).symm
    have hA := hP.le_finrank_inf_range e hn hF hB ht htN htd hM
    have hA' := hP.le_finrank_inf_range e hn hF hB ht htN htd hM'
    have hdisj : (M ⊓ LinearMap.range (ρ t - 1)) ⊓ (M.map (ρ g) ⊓ LinearMap.range (ρ t - 1)) =
        ⊥ := eq_bot_iff.mpr fun v hv => by
      have h1 : v ∈ M ⊓ M.map (ρ g) := ⟨hv.1.1, hv.2.1⟩
      rwa [hinf] at h1
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (M ⊓ LinearMap.range (ρ t - 1))
      (M.map (ρ g) ⊓ LinearMap.range (ρ t - 1))
    rw [hdisj, finrank_bot] at hsum
    have hle : Module.finrank (ZMod 2) ↥((M ⊓ LinearMap.range (ρ t - 1)) ⊔
        (M.map (ρ g) ⊓ LinearMap.range (ρ t - 1))) ≤
          Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) :=
      Submodule.finrank_mono (sup_le inf_le_right inf_le_right)
    have := finrank_range_sub_one ρ t
    omega
  have hMtop : M = ⊤ := by
    rcases hirr' M (fun g v hv => by rw [← hMG g]; exact ⟨v, hv, rfl⟩) with h | h
    · exact absurd h hM.2.1
    · exact h
  rw [← hMtop]
  exact hM

theorem IsPair.natOmegaPlus4_of_not_mem_normalizer (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible) (hP : IsPair L L₂) {F : Type}
    [Field F] [Fintype F] [CharP F 2] (e : ↥L ≃* SL(2, F)) {n : ℕ} (hn : 3 ≤ n)
    (hF : Fintype.card F = 2 ^ n) {t : G} (ht : t * t = 1)
    (htd : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t}) ≤ n + 1)
    (hB : fixSub ρ L₂ = ⊥) (htN : t ∉ normalizer (L : Set G)) :
    NatOmegaPlus4 ρ (lgConj L) ⊤ ⊥ n := by
  classical
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have h4 : 4 ≤ Nat.card F := by
    rw [hFn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : IsSimpleGroup SL(2, F) := P22y.isSimpleGroup_sl2 h4
  haveI : IsSimpleGroup ↥L := e.isSimpleGroup
  have hV := hP.isMinInv_top hirr e hn hF hB ht htN htd
  obtain ⟨hVnt, -⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr
  haveI := hVnt
  let ρGL : G →* GLV V :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom
  have hρGL : ∀ (g : G) (v : V), ρGL g v = ρ g v := fun g v => by
    simp [ρGL, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
      Representation.asGroupHom_apply]
  have hinjGL : Function.Injective ρGL := fun a b h =>
    hρ (LinearMap.ext fun v => by rw [← hρGL, ← hρGL, h])
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htN₂ : t ∉ normalizer (L₂ : Set G) := fun h => htN (hP.mem_normalizer_iff.mp h)
  have hτ : ((ρGL t : GLV V) : Module.End (ZMod 2) V) = ρ t := LinearMap.ext (hρGL t)
  obtain ⟨-, K, _, _, _, hK, φ₀, ψ, hψ₀⟩ := ten_glue ρGL (L₁ := L) (L₂ := L₂)
    (fun x _ h => hinjGL (h.trans (map_one ρGL).symm)) (fun x hx y hy => hP.commute hx hy)
    (fun U hU => by
      by_cases h0 : U = ⊥
      · exact Or.inl h0
      · exact Or.inr (hV.2.2 U le_top (fun x hx u hu => by rw [← hρGL]; exact hU x hx u hu) h0))
    e hn hF ht (fun x hx => by have h1 := hP.conj_mem_of_not_mem htN hx; rwa [htinv] at h1)
    (fun y hy => by have h1 := hP.symm.conj_mem_of_not_mem htN₂ hy; rwa [htinv] at h1)
    (by rw [hτ, finrank_range_sub_one]; exact htd)
  have hK4 : 4 ≤ Nat.card K := by rwa [hK, ← hFn]
  set σ := specialLinearGroupEquivStatedSL 2 K
  have hcoe : ∀ x : ↥(StatedSL 2 K), ((σ.symm x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := fun x => by
    have := specialLinearGroupEquivStatedSL_coe 2 K (σ.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  let φ : ↥(L.map ρGL ⊔ L₂.map ρGL) ≃* SL(2, K) × SL(2, K) :=
    φ₀.trans (MulEquiv.prodCongr σ.symm σ.symm)
  have hψ : ∀ (γ : ↥(L.map ρGL ⊔ L₂.map ρGL)) (v : V), ψ ((γ : GLV V) v) =
      ((φ γ).1 : Matrix (Fin 2) (Fin 2) K) * ψ v * ((φ γ).2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    intro γ v
    rw [hψ₀]
    show _ = ((σ.symm (φ₀ γ).1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * ψ v *
      ((σ.symm (φ₀ γ).2 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ
    rw [hcoe, hcoe]
  obtain ⟨φ', hφ'⟩ := exists_mulEquiv_omega_of_tensor hK4 φ ψ hψ
  have hX : (L ⊔ L₂).map ρGL = L.map ρGL ⊔ L₂.map ρGL := Subgroup.map_sup L L₂ ρGL
  let φX : ↥(lgConj L) ≃* ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    ((MulEquiv.subgroupCongr hP.lgConj_eq).trans
      ((Subgroup.equivMapOfInjective (L ⊔ L₂) ρGL hinjGL).trans
        (MulEquiv.subgroupCongr hX))).trans φ'
  refine ⟨K, inferInstance, inferInstance, hK, fun _ _ _ _ => Submodule.mem_top,
    fun _ _ v hv => by rw [(Submodule.mem_bot _).mp hv, map_zero]; exact zero_mem _, bot_le, φX,
    (coordEquiv ψ).toLinearMap.toAddMonoidHom, fun x hx => by
      rw [(Submodule.mem_bot _).mp hx, map_zero],
    fun x _ hx => (Submodule.mem_bot _).mpr ((coordEquiv ψ).map_eq_zero_iff.mp hx),
    fun y => ⟨(coordEquiv ψ).symm y, Submodule.mem_top, (coordEquiv ψ).apply_symm_apply y⟩,
    fun h x _ => ?_⟩
  have h1 := hφ' ((MulEquiv.subgroupCongr hX)
    ((Subgroup.equivMapOfInjective (L ⊔ L₂) ρGL hinjGL)
      ((MulEquiv.subgroupCongr hP.lgConj_eq) h))) x
  have h2 : (((MulEquiv.subgroupCongr hX) ((Subgroup.equivMapOfInjective (L ⊔ L₂) ρGL hinjGL)
      ((MulEquiv.subgroupCongr hP.lgConj_eq) h)) : ↥(L.map ρGL ⊔ L₂.map ρGL)) : GLV V) x =
        ρ h x := hρGL h x
  rw [h2] at h1
  exact h1

end Rep

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair
