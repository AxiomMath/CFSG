module

public import CFSG.Quasithin.H13.L32A58b
public import CFSG.Quasithin.Background.G64NatTop

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise IsMulCommutative

variable {G : Type} [Group G]

theorem relIndex_sup_of_normalizes {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)) ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)).injective, ?_⟩
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hy' : y ∈ (A : Set G) * (B : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left A B hB) ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using hb

@[expose] def mulAutToEnd (W : Type*) [Group W] : MulAut W →* AddMonoid.End (Additive W) where
  toFun α :=
    { toFun := fun m => Additive.ofMul (α (Additive.toMul m))
      map_zero' := by simp
      map_add' := fun a b => by simp }
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mulAutToEnd_apply {W : Type*} [Group W] (α : MulAut W) (m : Additive W) :
    mulAutToEnd W α m = Additive.ofMul (α (Additive.toMul m)) := rfl

theorem card_toSubgroup' {W : Type*} [Group W] (A : AddSubgroup (Additive W)) :
    Nat.card ↥(AddSubgroup.toSubgroup' A) = Nat.card ↥A :=
  Nat.card_congr
    { toFun := fun x => ⟨Additive.ofMul (x : W), x.2⟩
      invFun := fun x => ⟨Additive.toMul (x : Additive W), x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_eq_eight_of_h55 {W : Type} [Group W] [Finite W] (ρ : H6.Γ →* MulAut W)
    (hW : ∀ w : W, w ^ 2 = 1) {x : W} (hx : x ≠ 1) (hLp : ∀ g ∈ H6.Lp, ρ g x = x)
    (hgen : Subgroup.closure (Set.range fun g => ρ g x) = ⊤)
    (hLl : Nat.card ↥(Subgroup.closure {y | ∃ g ∈ H6.Ll, ρ g x = y}) = 4) :
    Nat.card W = 8 := by
  set ρ' : H6.Γ →* AddMonoid.End (Additive W) := (mulAutToEnd W).comp ρ with hρ'
  have hρ'x : ∀ g, ρ' g (Additive.ofMul x) = Additive.ofMul (ρ g x) := fun g => rfl
  have h2 : ∀ m : Additive W, m + m = 0 := fun m => by
    have := hW (Additive.toMul m)
    rw [pow_two] at this
    exact congrArg Additive.ofMul this
  have hx' : Additive.ofMul x ≠ 0 := fun h => hx (congrArg Additive.toMul h)
  have hLp' : ∀ g ∈ H6.Lp, ρ' g (Additive.ofMul x) = Additive.ofMul x := fun g hg => by
    rw [hρ'x, hLp g hg]
  have hgen' : AddSubgroup.closure (Set.range fun g : H6.Γ => ρ' g (Additive.ofMul x)) = ⊤ := by
    apply AddSubgroup.toSubgroup'.injective
    rw [AddSubgroup.toSubgroup'_closure, map_top]
    convert hgen using 2
    ext w
    simp only [Set.mem_preimage, Set.mem_range, hρ'x]
    exact ⟨fun ⟨g, hg⟩ => ⟨g, congrArg Additive.toMul hg⟩,
      fun ⟨g, hg⟩ => ⟨g, congrArg Additive.ofMul hg⟩⟩
  have hLl' : Nat.card ↥(AddSubgroup.closure
      {y | ∃ g ∈ H6.Ll, ρ' g (Additive.ofMul x) = y}) = 4 := by
    rw [← card_toSubgroup', AddSubgroup.toSubgroup'_closure]
    have hs : (Additive.ofMul ⁻¹' {y | ∃ g ∈ H6.Ll, ρ' g (Additive.ofMul x) = y} : Set W) =
        {y | ∃ g ∈ H6.Ll, ρ g x = y} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hρ'x]
      exact ⟨fun ⟨g, hg, h⟩ => ⟨g, hg, congrArg Additive.toMul h⟩,
        fun ⟨g, hg, h⟩ => ⟨g, hg, congrArg Additive.ofMul h⟩⟩
    rw [hs]
    exact hLl
  obtain ⟨f, hf, -⟩ := H6.volI_H_5_5 (Additive W) ρ' h2 (Additive.ofMul x) hx' hLp' hgen' hLl'
  have h := Nat.card_congr (Equiv.ofBijective f hf)
  show Nat.card (Additive W) = 8
  rw [← h]
  exact H6.card_v3

theorem map_graph_Lp : H6.Lp.map H6.graph.toMonoidHom = H6.Ll := by
  ext g
  rw [Subgroup.mem_map_equiv]
  have hs : H6.graph.symm g = H6.graph g := by
    apply H6.graph.injective
    rw [MulEquiv.apply_symm_apply, H6.graph_apply, H6.graph_apply, H6.graphFun_graphFun]
  rw [hs, ← H6.graph_mem_Ll_iff, H6.graph_apply, H6.graph_apply, H6.graphFun_graphFun]

theorem map_graph_Ll : H6.Ll.map H6.graph.toMonoidHom = H6.Lp := by
  rw [← map_graph_Lp, Subgroup.map_map]
  convert Subgroup.map_id H6.Lp
  ext g
  simp [H6.graph_apply, H6.graphFun_graphFun]

theorem exists_aligned {Q : Type*} [Group Q] (e : Q ≃* GL32) {B P₁ P₂ : Subgroup Q}
    (hB : Nat.card B = 8) (h₁ : B ≤ P₁) (h₂ : B ≤ P₂) (hc₁ : Nat.card P₁ = 24)
    (hc₂ : Nat.card P₂ = 24) (hne : P₁ ≠ P₂) :
    ∃ ψ : H6.Γ ≃* Q, H6.Lp.map ψ.toMonoidHom = P₁ ∧ H6.Ll.map ψ.toMonoidHom = P₂ := by
  set ψ₀ : H6.Γ ≃* Q := (e.trans (slEquivGL 3).symm).symm with hψ₀
  set B' := B.map ψ₀.symm.toMonoidHom with hB'
  have hB'c : Nat.card B' = 2 ^ (Nat.card H6.Γ).factorization 2 := by
    rw [hB', Subgroup.card_map_of_injective ψ₀.symm.injective, hB, H6.card_gamma_factorization]
    norm_num
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq H6.Γ H6.sylowBorel (Sylow.ofCard B' hB'c)
  have e' := congrArg (fun R : Sylow 2 H6.Γ => (R : Subgroup H6.Γ)) hy
  simp only [Sylow.coe_subgroup_smul, H6.sylowBorel, Sylow.coe_ofCard] at e'
  have hyB : ∀ t ∈ H6.borel, y * t * y⁻¹ ∈ B' := fun t ht => by
    rw [← e', Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨t, ht, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  set ψ₁ : H6.Γ ≃* Q := (MulAut.conj y).trans ψ₀ with hψ₁def
  have hψ₁ : ∀ g, ψ₁ g = ψ₀ (y * g * y⁻¹) := fun g => rfl
  have hT : ∀ {P : Subgroup Q}, B ≤ P → H6.borel ≤ P.map ψ₁.symm.toMonoidHom := by
    intro P hP t ht
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, hψ₁]
    apply hP
    have h1 := hyB t ht
    rw [hB', Subgroup.mem_map_equiv, MulEquiv.symm_symm] at h1
    exact h1
  have hc : ∀ {P : Subgroup Q}, Nat.card P = 24 →
      Nat.card ↥(P.map ψ₁.symm.toMonoidHom) = 24 := fun hP => by
    rw [Subgroup.card_map_of_injective ψ₁.symm.injective, hP]
  have hback : ∀ P : Subgroup Q, (P.map ψ₁.symm.toMonoidHom).map ψ₁.toMonoidHom = P := by
    intro P
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_symm,
      MulEquiv.apply_symm_apply]
  have hgr : ∀ (P : Subgroup Q) (R : Subgroup H6.Γ),
      (R.map H6.graph.toMonoidHom).map ψ₁.toMonoidHom = P →
      R.map (H6.graph.trans ψ₁).toMonoidHom = P := by
    intro P R h
    rw [← h]
    ext x
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_trans_apply]
  have hinj : Function.Injective (Subgroup.map ψ₁.symm.toMonoidHom) :=
    Subgroup.map_injective ψ₁.symm.injective
  rcases H6.eq_Lp_or_Ll (hT h₁) (hc hc₁) with e₁ | e₁ <;>
    rcases H6.eq_Lp_or_Ll (hT h₂) (hc hc₂) with e₂ | e₂
  · exact absurd (hinj (e₁.trans e₂.symm)) hne
  · exact ⟨ψ₁, by rw [← e₁, hback], by rw [← e₂, hback]⟩
  · refine ⟨H6.graph.trans ψ₁, hgr _ _ ?_, hgr _ _ ?_⟩
    · rw [map_graph_Lp, ← e₁, hback]
    · rw [map_graph_Ll, ← e₂, hback]
  · exact absurd (hinj (e₁.trans e₂.symm)) hne

@[expose] noncomputable def barK (K A : Subgroup G) : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))

variable [Finite G]

omit [Finite G] in
theorem card_barK_mul {K A : Subgroup G} (hQA : pCoreOf 2 K ≤ A) :
    Nat.card (barK K A) * Nat.card (pCoreOf 2 K) = Nat.card ↥(A ⊓ K) := by
  set N := CFSG.pCore 2 ↥K with hNdef
  have h1 : Nat.card (barK K A) = N.relIndex (A.subgroupOf K) := F6.card_map_mk _ _
  have hNA : N ≤ A.subgroupOf K := fun x hx => by
    rw [Subgroup.mem_subgroupOf]
    exact hQA ((mem_pCore_two_iff' x).mp hx)
  have h2 := Subgroup.relIndex_mul_card (H := N) (K := A.subgroupOf K)
  rw [inf_eq_left.mpr hNA] at h2
  have h3 : Nat.card N = Nat.card (pCoreOf 2 K) := by
    rw [hNdef]
    exact (Subgroup.card_map_of_injective K.subtype_injective).symm
  have h4 : Nat.card ↥(A.subgroupOf K) = Nat.card ↥(A ⊓ K) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [h1, ← h3, h2, h4]

namespace T53

namespace Ctx

variable {T L V V₂ Y : Subgroup G} (C : Ctx G T L V V₂ Y)
include C

theorem exists_z : ∃ z ∈ fsuV1 T V, z ≠ 1 ∧ ∀ v ∈ fsuV1 T V, v = 1 ∨ v = z := by
  have : IsMulCommutative ↥V := C.isMulCommutative_V
  have hc := C.set14.card_V1
  obtain ⟨w, hw⟩ : ∃ w : ↥(fsuV1 T V), w ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Nat.card ↥(fsuV1 T V) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => (hall a).trans (hall b).symm⟩
    omega
  refine ⟨w, w.2, fun h => hw (Subtype.ext h), fun v hv => ?_⟩
  by_cases hv1 : v = 1
  · exact Or.inl hv1
  · right
    have := G58.eq_of_card_two hc (x := ⟨v, hv⟩) (y := w)
      (fun h => hv1 (congrArg Subtype.val h)) hw
    exact congrArg Subtype.val this

omit C [Finite G] in
theorem T_le_centralizer_V1 : T ≤ Subgroup.centralizer (fsuV1 T V : Set G) := by
  have hZ : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun _ hz => hz.1
  exact Subgroup.le_centralizer_iff.mp (V1_le_Z.trans (hZ.trans inf_le_right))

theorem Y_le_centralizer_V1 : Y ≤ Subgroup.centralizer (fsuV1 T V : Set G) := by
  have : IsMulCommutative ↥V := C.isMulCommutative_V
  rw [← L32A.normalizer_eq_centralizer_of_card_two C.set14.card_V1]
  exact C.hYG1

theorem pCoreOf_le_T (h4 : Lemma14_7_4_two_three) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    {K : Subgroup G} (hK : K ∈ cComp (hY T L V₂ Y)) : pCoreOf 2 K ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  calc pCoreOf 2 K ≤ pCoreOf 2 (hY T L V₂ Y) :=
        A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
    _ = T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) := C.pCoreOf_hY_eq h4 hQ
    _ ≤ T := inf_le_left

theorem barK_facts (h4 : Lemma14_7_4_two_three) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    {K : Subgroup G} (hK : K ∈ cComp (hY T L V₂ Y))
    (hKn : hY T L V₂ Y ≤ Subgroup.normalizer (K : Set G))
    (eGL : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* GL32) (hXK : xL L V₂ ≤ K) (hYK : Y ≤ K) :
    Nat.card (barK K T) = 8 ∧ Nat.card (barK K (Y ⊔ T)) = 24 ∧
      Nat.card (barK K (xL L V₂ ⊔ T)) = 24 ∧ barK K T ≤ barK K (Y ⊔ T) ∧
      barK K T ≤ barK K (xL L V₂ ⊔ T) ∧ barK K (Y ⊔ T) ≠ barK K (xL L V₂ ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ hY T L V₂ Y := le_of_mem_cComp hK
  have hQT := C.pCoreOf_le_T h4 hQ hK
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := le_sup_right.trans hKn
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 K).exists_card_eq
  have hKc : Nat.card K = 2 ^ (3 + k) * 21 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
    have h2 : Nat.card (CFSG.pCore 2 ↥K) = Nat.card (pCoreOf 2 K) := by
      exact (Subgroup.card_map_of_injective K.subtype_injective).symm
    rw [h2, hk, G58.card_of_gl32 eGL] at h1
    rw [h1, pow_add]
    ring
  have hsylK : IsSylowIn 2 (T ⊓ K) K :=
    F6.isSylowIn_inf_of_isSubnormal (subnormal_of_mem_cComp hK)
      (C.isSylowTwoOf_T (K := hY T L V₂ Y) le_sup_right)
  have hTKc : Nat.card ↥(T ⊓ K) = 2 ^ (3 + k) :=
    G58.card_eq_of_isSylowIn hsylK hKc (by decide)
  have hbT : Nat.card (barK K T) = 8 := by
    have h1 := card_barK_mul (K := K) (A := T) hQT
    rw [hk, hTKc, pow_add] at h1
    have hpos : 0 < 2 ^ k := by positivity
    have : Nat.card (barK K T) * 2 ^ k = 8 * 2 ^ k := by rw [h1]; norm_num
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have key : ∀ {Z : Subgroup G}, Z ≤ K → T.relIndex (Z ⊔ T) = 3 →
      Nat.card (barK K (Z ⊔ T)) = 24 := by
    intro Z hZK hZ3
    set A := (Z ⊔ T) ⊓ K with hAdef
    have hTA : T ≤ Subgroup.normalizer (A : Set G) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer ((le_sup_right : T ≤ Z ⊔ T) ht), hTK ht⟩
    have hAT : A ⊔ T = Z ⊔ T :=
      le_antisymm (sup_le inf_le_left le_sup_right)
        (sup_le ((le_inf le_sup_left hZK).trans le_sup_left) le_sup_right)
    have h3 : T.relIndex A = 3 := by
      rw [← relIndex_sup_of_normalizes hTA, hAT, hZ3]
    have h4' := Subgroup.relIndex_mul_card (H := T) (K := A)
    have hTA' : T ⊓ A = T ⊓ K := by
      rw [hAdef, ← inf_assoc, inf_eq_left.mpr (le_sup_right : T ≤ Z ⊔ T)]
    rw [h3, hTA', hTKc] at h4'
    have h1 := card_barK_mul (K := K) (A := Z ⊔ T) (hQT.trans le_sup_right)
    rw [← hAdef, ← h4', hk, pow_add] at h1
    have hpos : 0 < 2 ^ k := by positivity
    have : Nat.card (barK K (Z ⊔ T)) * 2 ^ k = 24 * 2 ^ k := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hbY := key hYK C.relIndex_yT
  have hbX := key hXK (C.quot_xT h4).2
  refine ⟨hbT, hbY, hbX, Subgroup.map_mono fun x hx => (le_sup_right : T ≤ Y ⊔ T) hx,
    Subgroup.map_mono fun x hx => (le_sup_right : T ≤ xL L V₂ ⊔ T) hx, fun he => ?_⟩
  have hXY : xL L V₂ ≤ Y ⊔ T := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x, hXK hx⟩ ∈ barK K (xL L V₂ ⊔ T) :=
      ⟨⟨x, hXK hx⟩, Subgroup.mem_subgroupOf.mpr ((le_sup_left : xL L V₂ ≤ xL L V₂ ⊔ T) hx),
        rfl⟩
    rw [← he] at h1
    obtain ⟨k', hk', hkk⟩ := h1
    have h2 : k'⁻¹ * ⟨x, hXK hx⟩ ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.eq]
      exact hkk
    have h3 : ((k'⁻¹ * ⟨x, hXK hx⟩ : ↥K) : G) ∈ T := hQT ((mem_pCore_two_iff' _).mp h2)
    have e : x = (k' : G) * ((k'⁻¹ * ⟨x, hXK hx⟩ : ↥K) : G) := by simp
    rw [e]
    exact mul_mem (Subgroup.mem_subgroupOf.mp hk') ((le_sup_right : T ≤ Y ⊔ T) h3)
  have hXT : xL L V₂ ≤ T := by
    rw [← C.inf_eq h4]
    exact le_inf le_sup_left hXY
  have h1 := (C.quot_xT h4).2
  rw [sup_eq_right.mpr hXT, Subgroup.relIndex_self] at h1
  norm_num at h1

theorem card_vH (h4 : Lemma14_7_4_two_three) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    {K : Subgroup G} (hK : K ∈ cComp (hY T L V₂ Y))
    (hKn : hY T L V₂ Y ≤ Subgroup.normalizer (K : Set G)) (hHK : hY T L V₂ Y = K ⊔ T)
    (eGL : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* GL32) (hXK : xL L V₂ ≤ K) (hYK : Y ≤ K)
    (hO2 : pCoreOf 2 K = K ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G)) :
    Nat.card ↥(vH T L V V₂ Y) = 8 := by
  set W := vH T L V V₂ Y with hWdef
  have hKH : K ≤ hY T L V₂ Y := le_of_mem_cComp hK
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := hKH.trans (le_normalizer_conjClosure _ _)
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := le_sup_right.trans hKn
  set σ : ↥K →* MulAut ↥W := (conjAct W).comp (Subgroup.inclusion hKW) with hσdef
  have hσ : ∀ (k : ↥K) (w : ↥W), ((σ k w : ↥W) : G) = (k : G) * w * (k : G)⁻¹ := fun k w =>
    Subgroup.normalizerMonoidHom_apply_apply_coe W _ w
  have hker : CFSG.pCore 2 ↥K ≤ σ.ker := by
    intro k hk
    have hk' : (k : G) ∈ pCoreOf 2 K := (mem_pCore_two_iff' k).mp hk
    rw [hO2] at hk'
    rw [MonoidHom.mem_ker]
    ext w
    rw [hσ]
    have h1 := Subgroup.mem_centralizer_iff.mp hk'.2 w w.2
    simp only [MulAut.one_apply]
    rw [← h1, mul_inv_cancel_right]
  set σ' := QuotientGroup.lift (CFSG.pCore 2 ↥K) σ hker with hσ'def
  have hσ' : ∀ k : ↥K, σ' (QuotientGroup.mk k) = σ k := fun k => rfl
  obtain ⟨hbT, hbY, hbX, hTY, hTX, hne⟩ := C.barK_facts h4 hQ hK hKn eGL hXK hYK
  obtain ⟨ψ, hψp, hψl⟩ := exists_aligned eGL hbT hTY hTX hbY hbX hne
  set ρ : H6.Γ →* MulAut ↥W := σ'.comp ψ.toMonoidHom with hρdef
  have hρ : ∀ (g : H6.Γ) (k : ↥K), ψ g = QuotientGroup.mk k → ρ g = σ k := by
    intro g k hk
    show σ' (ψ g) = σ k
    rw [hk, hσ']
  obtain ⟨z, hzV1, hz1, hz12⟩ := C.exists_z
  have hzW : z ∈ W := le_conjClosure _ _ hzV1
  have hTz : ∀ t ∈ T, t * z * t⁻¹ = z := fun t ht => by
    rw [← Subgroup.mem_centralizer_iff.mp (T_le_centralizer_V1 (T := T) (V := V) ht) z hzV1,
      mul_inv_cancel_right]
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (C.vH_le_center hQ).2.2 w w.2)
  refine card_eq_eight_of_h55 ρ hW2 (x := ⟨z, hzW⟩) (fun h => hz1 (congrArg Subtype.val h))
    ?_ ?_ ?_
  ·
    intro g hg
    have h1 : ψ g ∈ barK K (Y ⊔ T) := hψp ▸ ⟨g, hg, rfl⟩
    obtain ⟨k, hk, hkg⟩ := h1
    rw [hρ g k hkg.symm]
    apply Subtype.ext
    rw [hσ]
    have hkC : (k : G) ∈ Subgroup.centralizer (fsuV1 T V : Set G) :=
      sup_le C.Y_le_centralizer_V1 (T_le_centralizer_V1 (T := T) (V := V))
        (Subgroup.mem_subgroupOf.mp hk)
    show (k : G) * z * (k : G)⁻¹ = z
    rw [← Subgroup.mem_centralizer_iff.mp hkC z hzV1, mul_inv_cancel_right]
  ·
    rw [eq_top_iff]
    intro w _
    have hWle : W ≤ (Subgroup.closure (Set.range fun g => ρ g ⟨z, hzW⟩)).map W.subtype := by
      rw [MonoidHom.map_closure]
      refine conjClosure_le fun h hh v hv => ?_
      rw [hHK] at hh
      obtain ⟨k, hk, t, ht, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTK).1 hh
      rcases hz12 v hv with hv1 | hvz
      · rw [hv1, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [hvz]
        have e : k * t * z * (k * t)⁻¹ = k * z * k⁻¹ := by
          calc k * t * z * (k * t)⁻¹ = k * (t * z * t⁻¹) * k⁻¹ := by group
            _ = k * z * k⁻¹ := by rw [hTz t ht]
        rw [e]
        apply Subgroup.subset_closure
        refine ⟨ρ (ψ.symm (QuotientGroup.mk ⟨k, hk⟩)) ⟨z, hzW⟩, ⟨_, rfl⟩, ?_⟩
        rw [hρ _ ⟨k, hk⟩ (MulEquiv.apply_symm_apply _ _)]
        exact hσ ⟨k, hk⟩ ⟨z, hzW⟩
    obtain ⟨w', hw', hww'⟩ := hWle w.2
    rwa [show w' = w from Subtype.ext hww'] at hw'
  ·
    have hcl : (Subgroup.closure {y | ∃ g ∈ H6.Ll, ρ g ⟨z, hzW⟩ = y}).map W.subtype = V₂ := by
      rw [MonoidHom.map_closure]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro _ ⟨y, ⟨g, hg, rfl⟩, rfl⟩
        have h1 : ψ g ∈ barK K (xL L V₂ ⊔ T) := hψl ▸ ⟨g, hg, rfl⟩
        obtain ⟨k, hk, hkg⟩ := h1
        rw [hρ g k hkg.symm]
        show ((σ k ⟨z, hzW⟩ : ↥W) : G) ∈ V₂
        rw [hσ]
        obtain ⟨a, ha, t, ht, hat⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
          C.T_le_normalizer_xL).1 (Subgroup.mem_subgroupOf.mp hk)
        have e : (k : G) * z * (k : G)⁻¹ = a * z * a⁻¹ := by
          calc (k : G) * z * (k : G)⁻¹ = a * (t * z * t⁻¹) * a⁻¹ := by rw [hat]; group
            _ = a * z * a⁻¹ := by rw [hTz t ht]
        rw [e, ← C.conjClosure_V1_X]
        exact mem_conjClosure ha hzV1
      · rw [← C.conjClosure_V1_X]
        refine conjClosure_le fun a ha v hv => ?_
        rcases hz12 v hv with hv1 | hvz
        · rw [hv1, mul_one, mul_inv_cancel]
          exact Subgroup.one_mem _
        · rw [hvz]
          apply Subgroup.subset_closure
          have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨a, hXK ha⟩ ∈
              barK K (xL L V₂ ⊔ T) :=
            ⟨⟨a, hXK ha⟩, Subgroup.mem_subgroupOf.mpr
              ((le_sup_left : xL L V₂ ≤ xL L V₂ ⊔ T) ha), rfl⟩
          rw [← hψl] at h1
          obtain ⟨g, hg, hga⟩ := h1
          refine ⟨ρ g ⟨z, hzW⟩, ⟨g, hg, rfl⟩, ?_⟩
          rw [hρ g ⟨a, hXK ha⟩ hga]
          exact hσ ⟨a, hXK ha⟩ ⟨z, hzW⟩
    rw [← Subgroup.card_map_of_injective W.subtype_injective, hcl, C.hV2.2.2.2]

theorem binaryNaturalSL_vH (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    {K : Subgroup G} (hK : K ∈ cComp (hY T L V₂ Y)) (eGL : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* GL32)
    (hO2 : pCoreOf 2 K = K ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G))
    (hcard : Nat.card ↥(vH T L V V₂ Y) = 8) :
    ∃ _ : IsMulCommutative ↥(vH T L V V₂ Y),
      BinaryNaturalSL (V := ↥(vH T L V V₂ Y)) (autOn K (vH T L V V₂ Y)) ⊤ ⊥ 3 1 := by
  set W := vH T L V V₂ Y with hWdef
  have hcomm : IsMulCommutative ↥W := (C.vH_le_center hQ).2.1
  refine ⟨hcomm, ?_⟩
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (C.vH_le_center hQ).2.2 w w.2)
  obtain ⟨π, hπ⟩ := G64.realizesVia_top_of_card (V := ↥W) hW2
    (show Nat.card ↥W = 2 ^ 3 by rw [hcard]; norm_num)
  have : Finite (MulAut ↥W) := Finite.of_injective _ DFunLike.coe_injective
  have hSL : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) = 168 := by
    rw [← Nat.card_congr
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).toEquiv]
    exact H6.card_gamma
  have hcardTop : Nat.card (MulAut ↥W) ≤ 168 := by
    have h1 := Nat.card_le_card_of_surjective π hπ.1
    rw [Subgroup.card_top, hSL] at h1
    exact h1
  have hKW : K ≤ Subgroup.normalizer (W : Set G) :=
    (le_of_mem_cComp hK).trans (le_normalizer_conjClosure _ _)
  set σ : ↥K →* MulAut ↥W := (conjAct W).comp (Subgroup.inclusion hKW) with hσdef
  have hσ : ∀ (k : ↥K) (w : ↥W), ((σ k w : ↥W) : G) = (k : G) * w * (k : G)⁻¹ := fun k w =>
    Subgroup.normalizerMonoidHom_apply_apply_coe W _ w
  have hrange : σ.range = autOn K W := by
    rw [hσdef, MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : σ.ker = CFSG.pCore 2 ↥K := by
    ext k
    rw [MonoidHom.mem_ker, mem_pCore_two_iff', hO2]
    constructor
    · intro hk
      refine ⟨k.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have h1 := congrArg (fun α : MulAut ↥W => ((α ⟨w, hw⟩ : ↥W) : G)) hk
      simp only [MulAut.one_apply] at h1
      rw [hσ] at h1
      calc w * (k : G) = ((k : G) * w * (k : G)⁻¹) * k := by rw [h1]
        _ = (k : G) * w := by group
    · intro hk
      ext w
      rw [hσ]
      simp only [MulAut.one_apply]
      rw [← Subgroup.mem_centralizer_iff.mp hk.2 w w.2, mul_inv_cancel_right]
  have hAut : Nat.card (autOn K W) = 168 := by
    rw [← hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange σ).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv, G58.card_of_gl32 eGL]
  have htop : autOn K W = ⊤ := Subgroup.eq_top_of_le_card _ (by rw [hAut]; exact hcardTop)
  refine ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, ?_⟩
  rw [htop]
  exact ⟨π, hπ⟩

theorem not_le_normalizer_V2 : ¬ Y ≤ Subgroup.normalizer (V₂ : Set G) := by
  intro hYV2
  have : IsMulCommutative ↥V := C.isMulCommutative_V
  have S := C.set14
  have hV2Y := C.centralizes_V2_of_normalizes hYV2
  have hYC : Y ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : v * y * v⁻¹ * y⁻¹ ∈ ⁅V₂, Y⁆ := Subgroup.commutator_mem_commutator hv hy
    rw [hV2Y, Subgroup.mem_bot] at h1
    calc v * y = (v * y * v⁻¹ * y⁻¹) * y * v := by group
      _ = y * v := by rw [h1, one_mul]
  have hL1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  apply C.hcex
  refine ⟨Or.inr hV2Y, fun hLY => ?_, ?_⟩
  · exfalso
    apply C.not_le_M
    have hYV : Y ≤ Subgroup.normalizer (V : Set G) := by
      intro y hy
      rw [← S.gen]
      refine mem_normalizer_conjClosure_of fun l hl w hw => ?_
      have hl' : l ∈ l1 T L V := hL1 ▸ hl
      have hyl : y * l ∈ (Y : Set G) * (l1 T L V : Set G) := Set.mul_mem_mul hy hl'
      rw [hLY] at hyl
      obtain ⟨l₂, hl₂, y₂, hy₂, hlye⟩ := hyl
      have hlye' : l₂ * y₂ = y * l := hlye
      have hyw : y₂ * w * y₂⁻¹ = w := by
        rw [← Subgroup.mem_centralizer_iff.mp (hYC hy₂) w hw, mul_inv_cancel_right]
      have hl₂' : l₂ ∈ L₁Of L (fsuV1 T V) := hL1 ▸ hl₂
      have e : y * (l * w * l⁻¹) * y⁻¹ = l₂ * (y₂ * w * y₂⁻¹) * l₂⁻¹ := by
        calc y * (l * w * l⁻¹) * y⁻¹ = (y * l) * w * (y * l)⁻¹ := by group
          _ = (l₂ * y₂) * w * (l₂ * y₂)⁻¹ := by rw [hlye']
          _ = l₂ * (y₂ * w * y₂⁻¹) * l₂⁻¹ := by group
      rw [e, hyw]
      exact mem_conjClosure hl₂' hw
    have h := C.inf_M_eq
    rw [inf_eq_left.mpr hYV] at h
    exact inf_eq_left.mp h
  · have hW : conjClosure V₂ Y = V₂ := by
      refine le_antisymm (conjClosure_le fun y hy v hv => ?_) (le_conjClosure _ _)
      rw [← Subgroup.mem_centralizer_iff.mp (hYC hy) v hv, mul_inv_cancel_right]
      exact hv
    rw [hW]
    have := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := V₂)
    rw [inf_eq_left.mpr C.hV2.1, S.card_V1, C.hV2.2.2.2] at this
    omega

theorem V2_le_vH : V₂ ≤ vH T L V V₂ Y :=
  calc V₂ = conjClosure (fsuV1 T V) (xL L V₂) := C.conjClosure_V1_X.symm
    _ ≤ vH T L V V₂ Y := conjClosure_mono le_rfl (le_sup_left.trans le_sup_left)

theorem vH_eq_conjClosure_V2 (hcard : Nat.card ↥(vH T L V V₂ Y) = 8) :
    vH T L V V₂ Y = conjClosure V₂ Y := by
  set W := vH T L V V₂ Y with hWdef
  set E := conjClosure V₂ Y with hEdef
  have hYH : Y ≤ hY T L V₂ Y := le_sup_right.trans le_sup_left
  have hEW : E ≤ W := conjClosure_le fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure (fsuV1 T V) (hY T L V₂ Y) (hYH hy)) v).mp (C.V2_le_vH hv)
  have hV2E : V₂ ≤ E := le_conjClosure _ _
  have hEc : Nat.card E ∣ 8 := hcard ▸ Subgroup.card_dvd_of_le hEW
  have h4E : 4 ∣ Nat.card E := C.hV2.2.2.2 ▸ Subgroup.card_dvd_of_le hV2E
  have hle : Nat.card E ≤ 8 := Nat.le_of_dvd (by norm_num) hEc
  have hpos : 0 < Nat.card E := Nat.card_pos
  have hE : Nat.card E = 4 ∨ Nat.card E = 8 := by
    interval_cases h : Nat.card E <;> omega
  rcases hE with h | h
  ·
    exfalso
    have hEV : E = V₂ := (Subgroup.eq_of_le_of_card_ge hV2E (by rw [h, C.hV2.2.2.2])).symm
    apply C.not_le_normalizer_V2
    rw [← hEV]
    exact le_normalizer_conjClosure V₂ Y
  · exact (Subgroup.eq_of_le_of_card_ge hEW (by rw [h, hcard])).symm

end Ctx

end T53

end CFSG.Quasithin.H13.L32A
