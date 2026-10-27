module

public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.Background.G2Omega4PlusModel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise MatrixGroups
open Om4Model

variable {G : Type*} [Group G]

structure Om4Data (A K VL : Subgroup G) where
  hnorm : A ≤ Subgroup.normalizer (VL : Set G)
  α : A →* OmG
  ψ : VL ≃* Multiplicative Mt
  surj : Function.Surjective α
  ker_eq : α.ker = K.subgroupOf A
  equiv : ∀ (a : A) (v : VL), Multiplicative.toAdd (ψ (conjAct VL ⟨a, hnorm a.2⟩ v)) =
    omSmul (α a) (Multiplicative.toAdd (ψ v))

structure AlmostSpecialOm4Hyp (V V₁ L T H : Subgroup G) : Prop where
  base : AlmostSpecialBase V V₁ L T H
  g22 : G22Conclusion V V₁ T H
  card_V₁ : Nat.card V₁ = 2
  L_star : Nonempty (↥(starImg L T L) ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
  V_le_VL : V ≤ conjClosure V₁ L
  module : ∃ D : Om4Data (L ⊔ conjClosure V H) (pCoreOf 2 (L ⊔ T)) (conjClosure V₁ L),
    ∀ v w : ↥(conjClosure V₁ L), (w : G) ∈ V₁ → (w : G) ≠ 1 →
      ((v : G) ∈ V ↔ polarDet (Multiplicative.toAdd (D.ψ v)) (Multiplicative.toAdd (D.ψ w)) = 0)

structure Om4Setting (V V₁ L T H : Subgroup G) where
  hyp : AlmostSpecialOm4Hyp V V₁ L T H
  D : Om4Data (L ⊔ conjClosure V H) (pCoreOf 2 (L ⊔ T)) (conjClosure V₁ L)
  perp : ∀ v w : ↥(conjClosure V₁ L), (w : G) ∈ V₁ → (w : G) ≠ 1 →
    ((v : G) ∈ V ↔ polarDet (Multiplicative.toAdd (D.ψ v)) (Multiplicative.toAdd (D.ψ w)) = 0)

namespace Om4Setting

section NoFinite

variable {V V₁ L T H : Subgroup G} (S : Om4Setting V V₁ L T H)

include S

theorem U_le_T : conjClosure V H ≤ T := S.hyp.g22.three.1

theorem T_le_normU : T ≤ Subgroup.normalizer (conjClosure V H : Set G) := S.hyp.g22.three.2

theorem U_le_normL {u : G} (hu : u ∈ conjClosure V H) : u ∈ Subgroup.normalizer (L : Set G) :=
  S.hyp.base.T_le_normL (S.U_le_T hu)

theorem V₁_le_U : V₁ ≤ conjClosure V H :=
  S.hyp.base.le_V.trans (le_conjClosure V H)

theorem V₁_le_T : V₁ ≤ T := S.hyp.base.le_V.trans S.hyp.base.V_le_T

theorem LT_le_normVL : L ⊔ T ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) :=
  sup_le (le_normalizer_conjClosure V₁ L)
    (le_normalizer_conjClosure_of_normalizes S.hyp.base.T_le_normV₁ S.hyp.base.T_le_normL)

theorem VL_le_LU : conjClosure V₁ L ≤ L ⊔ conjClosure V H :=
  conjClosure_le_sup_of_normalizes S.V₁_le_U fun _ hu => S.U_le_normL hu

theorem VL_le_LT : conjClosure V₁ L ≤ L ⊔ T :=
  conjClosure_le fun _ hl _ hz =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ((le_sup_left : L ≤ L ⊔ T) hl)
      ((le_sup_right : T ≤ L ⊔ T) (S.V₁_le_T hz)))
      (Subgroup.inv_mem _ ((le_sup_left : L ≤ L ⊔ T) hl))

theorem VL_sq_eq_one {x : G} (hx : x ∈ conjClosure V₁ L) : x ^ 2 = 1 := by
  have h : S.D.ψ ⟨x, hx⟩ * S.D.ψ ⟨x, hx⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    exact add_self_mt _
  have h2 : (⟨x, hx⟩ : ↥(conjClosure V₁ L)) * ⟨x, hx⟩ = 1 :=
    S.D.ψ.injective (by rw [map_mul, h, map_one])
  have := congrArg Subtype.val h2
  simpa [sq] using this

theorem VL_isPGroup : IsPGroup 2 (conjClosure V₁ L) :=
  isPGroup_two_of_forall fun c hc => ⟨1, by simpa using S.VL_sq_eq_one hc⟩

theorem alpha_eq_one_iff (x : ↥(L ⊔ conjClosure V H)) :
    S.D.α x = 1 ↔ (x : G) ∈ pCoreOf 2 (L ⊔ T) := by
  rw [← MonoidHom.mem_ker, S.D.ker_eq, Subgroup.mem_subgroupOf]

theorem VL_le_O : conjClosure V₁ L ≤ pCoreOf 2 (L ⊔ T) :=
  le_pCoreOf_of_le_normalizer 2 S.VL_le_LT S.LT_le_normVL S.VL_isPGroup

theorem O_centralizes_VL (x : ↥(L ⊔ conjClosure V H)) (hx : (x : G) ∈ pCoreOf 2 (L ⊔ T)) :
    ∀ v ∈ conjClosure V₁ L, (x : G) * v * (x : G)⁻¹ = v := by
  intro v hv
  have h1 := S.D.equiv x ⟨v, hv⟩
  rw [(S.alpha_eq_one_iff x).2 hx] at h1
  have h2 : conjAct (conjClosure V₁ L) ⟨x, S.D.hnorm x.2⟩ ⟨v, hv⟩ = ⟨v, hv⟩ := by
    apply S.D.ψ.injective
    apply Multiplicative.toAdd.injective
    rw [h1]
    simp [omSmul]
  have h3 := congrArg Subtype.val h2
  rwa [conjAct_coe_apply] at h3

theorem alpha_cube_eq_one {l : G} (hl : l ∈ L) :
    (S.D.α ⟨l, (le_sup_left : L ≤ L ⊔ conjClosure V H) hl⟩) ^ 3 = 1 := by
  obtain ⟨e⟩ := S.hyp.L_star
  set x : ↥(starImg L T L) := ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨l, (le_sup_left : L ≤ L ⊔ T) hl⟩,
    secMk_mem_secImg hl⟩ with hx
  have h3 : x ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    have : ∀ y : Multiplicative (ZMod 3) × Multiplicative (ZMod 3), y ^ 3 = 1 := by decide
    exact this _
  have h4 : (secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨l, (le_sup_left : L ≤ L ⊔ T) hl⟩) ^ 3 = 1 :=
    congrArg Subtype.val h3
  rw [← map_pow] at h4
  have h6 := secMk_eq_one_iff.1 h4
  have h7 : ((⟨l, (le_sup_left : L ≤ L ⊔ conjClosure V H) hl⟩ : ↥(L ⊔ conjClosure V H)) ^ 3 :
      ↥(L ⊔ conjClosure V H)) ∈ S.D.α.ker := by
    rw [S.D.ker_eq, Subgroup.mem_subgroupOf]
    simpa using h6
  rw [MonoidHom.mem_ker, map_pow] at h7
  exact h7

end NoFinite

section WithFinite

variable [Finite G] {V V₁ L T H : Subgroup G} (S : Om4Setting V V₁ L T H)

include S

theorem O_le_T : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf S.hyp.base.sylow_LT

end WithFinite

end Om4Setting

namespace Om4Setting

section PartOne

variable {V V₁ L T H : Subgroup G} (S : Om4Setting V V₁ L T H)

include S

theorem exists_v₁ : ∃ v₁ ∈ V₁, v₁ ≠ 1 ∧ ∀ v ∈ V₁, v = 1 ∨ v = v₁ := by
  have h := S.hyp.card_V₁
  rw [Nat.card_eq_two_iff' (1 : V₁)] at h
  obtain ⟨y, hy, huniq⟩ := h
  refine ⟨y, y.2, fun h1 => hy (Subtype.ext h1), fun v hv => ?_⟩
  by_cases h1 : v = 1
  · exact Or.inl h1
  · right
    have := huniq ⟨v, hv⟩ (fun h => h1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this

theorem LU_decomp (y : OmG) : ∃ l υ : OmG, l ^ 3 = 1 ∧
    (∃ u : ↥(L ⊔ conjClosure V H), (u : G) ∈ conjClosure V H ∧ S.D.α u = υ) ∧ y = l * υ := by
  obtain ⟨x, rfl⟩ := S.D.surj y
  have hmul : ((L ⊔ conjClosure V H : Subgroup G) : Set G) =
      (L : Set G) * (conjClosure V H : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L _ (fun u hu => S.U_le_normL hu)
  have hx : (x : G) ∈ ((L ⊔ conjClosure V H : Subgroup G) : Set G) := x.2
  rw [hmul] at hx
  obtain ⟨l, hl, u, hu, hxe⟩ := hx
  have hlLU : l ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) hl
  have huLU : u ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu
  have e : x = ⟨l, hlLU⟩ * ⟨u, huLU⟩ := Subtype.ext hxe.symm
  refine ⟨S.D.α ⟨l, hlLU⟩, S.D.α ⟨u, huLU⟩, S.alpha_cube_eq_one hl, ⟨⟨u, huLU⟩, hu, rfl⟩, ?_⟩
  rw [e, map_mul]

theorem fix_X₁ {v₁ : G} (hv₁ : v₁ ∈ V₁) (hne : v₁ ≠ 1) (huniq : ∀ v ∈ V₁, v = 1 ∨ v = v₁)
    {u : ↥(L ⊔ conjClosure V H)} (hu : (u : G) ∈ conjClosure V H) :
    omSmul (S.D.α u) (Multiplicative.toAdd (S.D.ψ ⟨v₁, le_conjClosure V₁ L hv₁⟩)) =
      Multiplicative.toAdd (S.D.ψ ⟨v₁, le_conjClosure V₁ L hv₁⟩) := by
  have h1 := S.D.equiv u ⟨v₁, le_conjClosure V₁ L hv₁⟩
  rw [← h1]
  have hconj : (u : G) * v₁ * (u : G)⁻¹ ∈ V₁ :=
    (Subgroup.mem_normalizer_iff.1 (S.hyp.base.T_le_normV₁ (S.U_le_T hu)) v₁).1 hv₁
  have h2 : conjAct (conjClosure V₁ L) ⟨u, S.D.hnorm u.2⟩ ⟨v₁, le_conjClosure V₁ L hv₁⟩ =
      ⟨v₁, le_conjClosure V₁ L hv₁⟩ := by
    apply Subtype.ext
    rw [conjAct_coe_apply]
    rcases huniq _ hconj with h | h
    · exfalso
      apply hne
      have : v₁ = (u : G)⁻¹ * ((u : G) * v₁ * (u : G)⁻¹) * u := by group
      rw [this, h]
      group
    · exact h
  rw [h2]

end PartOne

end Om4Setting

namespace Om4Setting

section PartOneMain

variable [Finite G] {V V₁ L T H : Subgroup G} (S : Om4Setting V V₁ L T H)

include S

omit [Finite G] in
theorem core {g : G} (hg : g ∈ L) (hgV : ¬ rconj V₁ g ≤ V) :
    ∃ X₁ : Mt, X₁ ≠ 0 ∧ X₁.det = 0 ∧
      (∀ s : OmG, omSmul s X₁ = X₁ → ∃ u : ↥(L ⊔ conjClosure V H),
        (u : G) ∈ conjClosure V H ∧ S.D.α u = s) ∧
      (∀ v : ↥(conjClosure V₁ L), (v : G) ∈ V ↔
        polarDet (Multiplicative.toAdd (S.D.ψ v)) X₁ = 0) ∧
      polarDet X₁ (omSmul (S.D.α ⟨g⁻¹, (le_sup_left : L ≤ L ⊔ conjClosure V H) (L.inv_mem hg)⟩) X₁)
        ≠ 0 := by
  obtain ⟨v₁, hv₁, hne, huniq⟩ := S.exists_v₁
  set U := conjClosure V H with hU
  set VL := conjClosure V₁ L with hVL
  have hv₁VL : v₁ ∈ VL := le_conjClosure V₁ L hv₁
  set w : ↥VL := ⟨v₁, hv₁VL⟩ with hw
  set X₁ : Mt := Multiplicative.toAdd (S.D.ψ w) with hX₁def
  have hX₁ : X₁ ≠ 0 := by
    intro h0
    apply hne
    have h1 : S.D.ψ w = 1 := toAdd_eq_zero.1 h0
    have h2 : w = 1 := S.D.ψ.injective (h1.trans (map_one S.D.ψ).symm)
    exact congrArg Subtype.val h2
  have hfix : ∀ u : ↥(L ⊔ U), (u : G) ∈ U → omSmul (S.D.α u) X₁ = X₁ :=
    fun u hu => S.fix_X₁ hv₁ hne huniq hu
  have hdec := S.LU_decomp
  let P : OmG → Prop := fun υ => ∃ u : ↥(L ⊔ U), (u : G) ∈ U ∧ S.D.α u = υ
  have hfixP : ∀ υ, P υ → omSmul υ X₁ = X₁ := by
    rintro υ ⟨u, hu, rfl⟩
    exact hfix u hu
  have hdet₁ : X₁.det = 0 := det_eq_zero_of_decomp hdec hfixP
  have hstab₁ : ∀ s : OmG, omSmul s X₁ = X₁ → P s :=
    fun s hs => pred_of_stab hX₁ hdet₁ hdec hfixP hs
  have hgLU : g ∈ L ⊔ U := (le_sup_left : L ≤ L ⊔ U) hg
  have hginvL : g⁻¹ ∈ L := L.inv_mem hg
  have hginvLU : g⁻¹ ∈ L ⊔ U := (le_sup_left : L ≤ L ⊔ U) hginvL
  have hv₂VL : g⁻¹ * v₁ * g ∈ VL := by
    have := mem_conjClosure (Z := V₁) hginvL hv₁
    simpa using this
  set w₂ : ↥VL := ⟨g⁻¹ * v₁ * g, hv₂VL⟩ with hw₂
  set X₂ : Mt := Multiplicative.toAdd (S.D.ψ w₂) with hX₂def
  have hX₂eq : X₂ = omSmul (S.D.α ⟨g⁻¹, hginvLU⟩) X₁ := by
    have h1 := S.D.equiv ⟨g⁻¹, hginvLU⟩ w
    have h2 : conjAct VL ⟨((⟨g⁻¹, hginvLU⟩ : ↥(L ⊔ U)) : G), S.D.hnorm (⟨g⁻¹, hginvLU⟩ : ↥(L ⊔ U)).2⟩
        w = w₂ := by
      apply Subtype.ext
      rw [conjAct_coe_apply]
      simp [hw, hw₂]
    rw [h2] at h1
    exact h1
  have hw₂V : (w₂ : G) ∉ V := by
    intro hmem
    apply hgV
    intro y hy
    have hy' : g * y * g⁻¹ ∈ V₁ := mem_rconj.1 hy
    rcases huniq _ hy' with h | h
    · have : y = 1 := by
        have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
        rw [this, h]; group
      rw [this]; exact V.one_mem
    · have : y = g⁻¹ * v₁ * g := by
        have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
        rw [this, h]
      rw [this]; exact hmem
  have hpolar : polarDet X₁ X₂ ≠ 0 := by
    rw [polarDet_comm]
    intro h0
    exact hw₂V ((S.perp w₂ w hv₁ hne).2 h0)
  refine ⟨X₁, hX₁, hdet₁, fun s hs => hstab₁ s hs, fun v => S.perp v w hv₁ hne, ?_⟩
  rw [← hX₂eq]
  exact hpolar

theorem I_eq_LU {g : G} (hg : g ∈ L) (hgV : ¬ rconj V₁ g ≤ V) :
    conjClosure V H ⊔ rconj (conjClosure V H) g = L ⊔ conjClosure V H := by
  obtain ⟨X₁, hX₁, hdet₁, hstab₁, -, hpolar⟩ := S.core hg hgV
  set U := conjClosure V H with hU
  have hgLU : g ∈ L ⊔ U := (le_sup_left : L ≤ L ⊔ U) hg
  have hginvLU : g⁻¹ ∈ L ⊔ U := (le_sup_left : L ≤ L ⊔ U) (L.inv_mem hg)
  set X₂ : Mt := omSmul (S.D.α ⟨g⁻¹, hginvLU⟩) X₁ with hX₂def
  have hX₂ : X₂ ≠ 0 := fun h => hX₁ ((omSmul_eq_zero_iff _ _).1 h)
  have hdet₂ : X₂.det = 0 := by rw [hX₂def, det_omSmul]; exact hdet₁
  set I := U ⊔ rconj U g with hI
  have hUI : U ≤ I := le_sup_left
  let J : Subgroup OmG := (I.subgroupOf (L ⊔ U)).map S.D.α
  have hJ1 : ∀ s : OmG, omSmul s X₁ = X₁ → s ∈ J := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ := hstab₁ s hs
    exact ⟨u, Subgroup.mem_subgroupOf.2 (hUI hu), rfl⟩
  have hγinv : S.D.α ⟨g⁻¹, hginvLU⟩ = (S.D.α ⟨g, hgLU⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  have hX₂eq' : X₂ = omSmul (S.D.α ⟨g, hgLU⟩)⁻¹ X₁ := by rw [hX₂def, hγinv]
  have hX₁eq : omSmul (S.D.α ⟨g, hgLU⟩) X₂ = X₁ := by
    rw [hX₂eq', ← omSmul_mul, mul_inv_cancel, omSmul_one]
  have hJ2 : ∀ s : OmG, omSmul s X₂ = X₂ → s ∈ J := by
    intro s hs
    have h1 : omSmul (S.D.α ⟨g, hgLU⟩ * s * (S.D.α ⟨g, hgLU⟩)⁻¹) X₁ = X₁ := by
      rw [omSmul_mul, omSmul_mul, ← hX₂eq', hs, hX₁eq]
    obtain ⟨u, hu, hυ⟩ := hstab₁ _ h1
    refine ⟨⟨g⁻¹, hginvLU⟩ * u * ⟨g, hgLU⟩, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · have : ((⟨g⁻¹, hginvLU⟩ * u * ⟨g, hgLU⟩ : ↥(L ⊔ U)) : G) = g⁻¹ * u * g := rfl
      rw [this]
      exact (le_sup_right : rconj U g ≤ I) (inv_mul_mul_mem_rconj hu)
    · rw [map_mul, map_mul, hγinv, hυ]
      group
  have hJ : J = ⊤ := generation hX₁ hX₂ hdet₁ hdet₂ hpolar hJ1 hJ2
  have hgen : ∀ x : ↥(L ⊔ U), ∃ i : ↥(L ⊔ U), (i : G) ∈ I ∧ S.D.α i = S.D.α x := by
    intro x
    have hx : S.D.α x ∈ J := by rw [hJ]; trivial
    obtain ⟨i, hi, hix⟩ := hx
    exact ⟨i, Subgroup.mem_subgroupOf.1 hi, hix⟩
  exact I_eq_sup_of_hom S.D.α S.hyp.base.oTwo_eq hg hI
    ((S.O_le_T).trans S.T_le_normU) (pCoreOf_isPGroup 2 (L ⊔ T))
    (fun x h => (S.alpha_eq_one_iff x).1 h) hgen

end PartOneMain

end Om4Setting

namespace Om4Setting

section PartTwo

variable [Finite G] {V V₁ L T H : Subgroup G} (S : Om4Setting V V₁ L T H)

include S

@[expose] noncomputable def theta : ↥L →* OmG :=
  S.D.α.comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ conjClosure V H))

omit [Finite G] in
theorem theta_eq_one_iff (x : ↥L) : S.theta x = 1 ↔ (x : G) ∈ pCoreOf 2 (L ⊔ T) :=
  S.alpha_eq_one_iff ⟨x, (le_sup_left : L ≤ L ⊔ conjClosure V H) x.2⟩

omit [Finite G] in
theorem card_range_theta : Nat.card S.theta.range = 9 := by
  obtain ⟨e0⟩ := S.hyp.L_star
  obtain ⟨e, -⟩ := secImg_equiv_of_hom (A := L ⊔ T) (B := pCoreOf 2 (L ⊔ T)) (X := L)
    (le_sup_left : L ≤ L ⊔ T) S.theta.rangeRestrict S.theta.rangeRestrict_surjective
    (fun x => by
      rw [← S.theta_eq_one_iff x]
      constructor
      · intro h
        have := congrArg Subtype.val h
        exact this
      · intro h
        exact Subtype.ext h)
  have h1 : Nat.card ↥(starImg L T L) = Nat.card S.theta.range := Nat.card_congr e.toEquiv
  have h2 : Nat.card ↥(starImg L T L) =
      Nat.card (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) := Nat.card_congr e0.toEquiv
  rw [← h1, h2, Nat.card_prod]
  simp

end PartTwo

end Om4Setting

namespace Om4Setting

section PartTwoMain

variable [Finite G] {V V₁ L T H : Subgroup G} (S : Om4Setting V V₁ L T H)

include S

theorem pCoreOf_I_le_P {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgV : ¬ rconj V₁ g ≤ V) (hI : I = U ⊔ rconj U g) :
    pCoreOf 2 I ≤ (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g := by
  subst hU
  have hI' : I = L ⊔ conjClosure V H := hI.trans (S.I_eq_LU hg hgV)
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := sx_facts_gen hI' S.U_le_T S.T_le_normU
    S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  have hLI : L ≤ I := hI' ▸ le_sup_left
  have hUI : conjClosure V H ≤ I := hI' ▸ le_sup_right
  have hgI : g ∈ I := hLI hg
  have hIP := I_le_normalizer_P hI hgI hINorm hSxU
  have hPSx : (conjClosure V H ⊓ pCoreOf 2 I) ⊔ rconj (conjClosure V H ⊓ pCoreOf 2 I) g ≤
      pCoreOf 2 I := sup_le inf_le_right (rconj_inf_le_Sx hgI hINorm)
  set P := (conjClosure V H ⊓ pCoreOf 2 I) ⊔ rconj (conjClosure V H ⊓ pCoreOf 2 I) g with hP
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := hLI.trans hIP
  have hWP : conjClosure V H ⊓ pCoreOf 2 I ≤ P := le_sup_left
  have hKker : (L ⊓ pCoreOf 2 I).subgroupOf L = S.theta.ker := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
    rw [S.theta_eq_one_iff x]
    constructor
    · rintro ⟨_, hx⟩
      exact hSxO hx
    · intro hx
      exact ⟨x.2, mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hLI x.2) hx⟩
  have hodd : ¬ 2 ∣ ((L ⊓ pCoreOf 2 I).subgroupOf L ⊔ (⊥ : Subgroup G).subgroupOf L).index := by
    rw [Subgroup.bot_subgroupOf, sup_bot_eq, hKker, Subgroup.index_ker, S.card_range_theta]
    norm_num
  have hL : L ⊓ pCoreOf 2 I ≤ P :=
    inf_le_of_central_odd_index (C := ⊥) S.hyp.base.oTwo_eq hPSx hLP
      (fun k hk y hy => by
        have h := comm_Sx_mem_P hI hgI hINorm hSxU (hLI hy) hk.2
        have := P.inv_mem h
        simpa [mul_assoc] using this)
      (S.hyp.base.isPGroup_T.to_le (inf_le_right.trans hSxT)) (by simp) hodd
  have hmul : ((L ⊔ conjClosure V H : Subgroup G) : Set G) =
      (L : Set G) * (conjClosure V H : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L _ (fun u hu => S.U_le_normL hu)
  intro s hs
  have hsLU : s ∈ ((L ⊔ conjClosure V H : Subgroup G) : Set G) := hI' ▸ pCoreOf_le 2 I hs
  rw [hmul] at hsLU
  obtain ⟨l, hl, u, hu, rfl⟩ := hsLU
  have hlLU : l ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) hl
  have huLU : u ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu
  have hsLU' : l * u ∈ L ⊔ conjClosure V H := Subgroup.mul_mem _ hlLU huLU
  have h1 : S.D.α ⟨l * u, hsLU'⟩ = 1 := (S.alpha_eq_one_iff _).2 (hSxO hs)
  have e : (⟨l * u, hsLU'⟩ : ↥(L ⊔ conjClosure V H)) = ⟨l, hlLU⟩ * ⟨u, huLU⟩ := rfl
  rw [e, map_mul] at h1
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem S.hyp.base.isPGroup_T (S.U_le_T hu)
  have hαu2 : (S.D.α ⟨u, huLU⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨u, huLU⟩ : ↥(L ⊔ conjClosure V H)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hαl : S.D.α ⟨l, hlLU⟩ = 1 := by
    have hlu : S.D.α ⟨l, hlLU⟩ = (S.D.α ⟨u, huLU⟩)⁻¹ := eq_inv_of_mul_eq_one_left h1
    refine eq_one_of_pow_three_of_pow_two_pow (k := k) (S.alpha_cube_eq_one hl) ?_
    rw [hlu, inv_pow, hαu2, inv_one]
  have hαu : S.D.α ⟨u, huLU⟩ = 1 := by
    rw [hαl, one_mul] at h1
    exact h1
  have hlO : l ∈ pCoreOf 2 (L ⊔ T) := (S.alpha_eq_one_iff _).1 hαl
  have huO : u ∈ pCoreOf 2 (L ⊔ T) := (S.alpha_eq_one_iff _).1 hαu
  have hlP : l ∈ P := hL ⟨hl, mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hLI hl) hlO⟩
  have huP : u ∈ P := hWP ⟨hu, mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hUI hu) huO⟩
  exact P.mul_mem hlP huP

end PartTwoMain

end Om4Setting

namespace Om4Setting

section PartThree

variable [Finite G] {V V₁ L T H : Subgroup G} (S : Om4Setting V V₁ L T H)

include S

omit [Finite G] in
theorem LU_le_normVL : L ⊔ conjClosure V H ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) :=
  S.D.hnorm

theorem I_eq_LU' {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgV : ¬ rconj V₁ g ≤ V) (hI : I = U ⊔ rconj U g) : I = L ⊔ U := by
  have h : U ⊔ rconj U g = L ⊔ U := by
    rw [hU]
    exact S.I_eq_LU hg hgV
  exact hI.trans h

omit [Finite G] in
theorem U_le_T' {U : Subgroup G} (hU : U = conjClosure V H) : U ≤ T := by
  rw [hU]
  exact S.U_le_T

omit [Finite G] in
theorem LU_le_normVL' {U : Subgroup G} (hU : U = conjClosure V H) :
    L ⊔ U ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) := by
  rw [hU]
  exact S.LU_le_normVL

theorem commutator_inter_le_VL {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgV : ¬ rconj V₁ g ≤ V) (hI : I = U ⊔ rconj U g) :
    ⁅U ⊓ rconj U g, I⁆ ≤ conjClosure V₁ L := by
  have hI' : I = L ⊔ U := S.I_eq_LU' hU hg hgV hI
  have hIVL : I ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) := hI' ▸ S.LU_le_normVL' hU
  refine commutator_inter_le_of hI hIVL
    (fun x hx y hy => G22Conclusion.commutator_mem S.hyp.base S.hyp.g22 (hU ▸ hx) (hU ▸ hy))
    (le_conjClosure V₁ L) ?_
  intro y hy
  have hy' : g * y * g⁻¹ ∈ V₁ := mem_rconj.1 hy
  have hVL : g * y * g⁻¹ ∈ conjClosure V₁ L := le_conjClosure V₁ L hy'
  have h2 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V₁ L (L.inv_mem hg)) _).1 hVL
  simpa [mul_assoc] using h2

theorem commutator_S₂_le {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgV : ¬ rconj V₁ g ≤ V) (hI : I = U ⊔ rconj U g) :
    ⁅conjClosure V₁ L ⊔ (U ⊓ rconj U g), I⁆ ≤ conjClosure V₁ L := by
  have hC := S.commutator_inter_le_VL hU hg hgV hI
  have hI' : I = L ⊔ U := S.I_eq_LU' hU hg hgV hI
  have hIVL : I ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) := hI' ▸ S.LU_le_normVL' hU
  have hUI : U ≤ I := hI ▸ le_sup_left
  have hCN : U ⊓ rconj U g ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) :=
    inf_le_left.trans (hUI.trans hIVL)
  have hmul : ((conjClosure V₁ L ⊔ (U ⊓ rconj U g) : Subgroup G) : Set G) =
      (conjClosure V₁ L : Set G) * ((U ⊓ rconj U g : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCN
  rw [Subgroup.commutator_le]
  intro y hy x hx
  have hy' : y ∈ ((conjClosure V₁ L ⊔ (U ⊓ rconj U g) : Subgroup G) : Set G) := hy
  rw [hmul] at hy'
  obtain ⟨v, hv, c, hc, rfl⟩ := hy'
  have h1 : c * x * c⁻¹ * x⁻¹ ∈ conjClosure V₁ L := hC (Subgroup.commutator_mem_commutator hc hx)
  have h2 : x * v⁻¹ * x⁻¹ ∈ conjClosure V₁ L :=
    (Subgroup.mem_normalizer_iff.1 (hIVL hx) _).1 ((conjClosure V₁ L).inv_mem hv)
  show v * c * x * (v * c)⁻¹ * x⁻¹ ∈ conjClosure V₁ L
  have : v * c * x * (v * c)⁻¹ * x⁻¹ = v * (c * x * c⁻¹ * x⁻¹) * (x * v⁻¹ * x⁻¹) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hv h1) h2

theorem I_series {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgV : ¬ rconj V₁ g ≤ V) (hI : I = U ⊔ rconj U g) :
    conjClosure V₁ L ≤ conjClosure V₁ L ⊔ (U ⊓ rconj U g) ∧
      conjClosure V₁ L ⊔ (U ⊓ rconj U g) ≤ pCoreOf 2 I ∧
      conjClosure V₁ L ≤ centerOf (pCoreOf 2 I) ∧
      I ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) ∧
      I ≤ Subgroup.normalizer ((conjClosure V₁ L ⊔ (U ⊓ rconj U g) : Subgroup G) : Set G) ∧
      I ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) := by
  have hC := S.commutator_inter_le_VL hU hg hgV hI
  have hI' : I = L ⊔ U := S.I_eq_LU' hU hg hgV hI
  have hIVL : I ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) := hI' ▸ S.LU_le_normVL' hU
  have hUI : U ≤ I := hI ▸ le_sup_left
  have hUT : U ≤ T := S.U_le_T' hU
  have hVLI : conjClosure V₁ L ≤ I := by
    rw [hI', hU]
    exact S.VL_le_LU
  have hS₂N : I ≤ Subgroup.normalizer
      ((conjClosure V₁ L ⊔ (U ⊓ rconj U g) : Subgroup G) : Set G) := by
    refine le_normalizer_sup_of_conj_mem (fun x hx a ha => ?_) (fun x hx b hb => ?_)
    · exact (le_sup_left : conjClosure V₁ L ≤ _)
        ((Subgroup.mem_normalizer_iff.1 (hIVL hx) a).1 ha)
    · have h1 : b * x * b⁻¹ * x⁻¹ ∈ conjClosure V₁ L :=
        hC (Subgroup.commutator_mem_commutator hb hx)
      have h2 : x * b * x⁻¹ = (b * x * b⁻¹ * x⁻¹)⁻¹ * b := by group
      rw [h2]
      exact Subgroup.mul_mem _ ((le_sup_left : conjClosure V₁ L ≤ _) (Subgroup.inv_mem _ h1))
        ((le_sup_right : U ⊓ rconj U g ≤ _) hb)
  have hS₂I : conjClosure V₁ L ⊔ (U ⊓ rconj U g) ≤ I := sup_le hVLI (inf_le_left.trans hUI)
  have hS₂T : conjClosure V₁ L ⊔ (U ⊓ rconj U g) ≤ T :=
    sup_le (S.VL_le_O.trans S.O_le_T) (inf_le_left.trans hUT)
  have hS₂O : conjClosure V₁ L ⊔ (U ⊓ rconj U g) ≤ pCoreOf 2 I :=
    le_pCoreOf_of_le_normalizer 2 hS₂I hS₂N (S.hyp.base.isPGroup_T.to_le hS₂T)
  refine ⟨le_sup_left, hS₂O, ?_, hIVL, hS₂N, le_normalizer_pCoreOf 2 I⟩
  intro v hv
  refine ⟨hS₂O ((le_sup_left : conjClosure V₁ L ≤ _) hv),
    Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
  obtain ⟨-, hSxO, -, -, -⟩ := sx_facts_gen hI' hUT (hU ▸ S.T_le_normU)
    S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  have hsLU : s ∈ L ⊔ U := hI' ▸ pCoreOf_le 2 I hs
  have h1 := S.O_centralizes_VL ⟨s, (hU ▸ hsLU : s ∈ L ⊔ conjClosure V H)⟩ (hSxO hs) v hv
  calc s * v = (s * v * s⁻¹) * s := by group
    _ = v * s := by rw [show s * v * s⁻¹ = v from h1]

end PartThree

end Om4Setting

namespace AlmostSpecialOm4Hyp

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialOm4Hyp V V₁ L T H)

include hyp

theorem G26_one {g : G} (hg : g ∈ L) (hgV : ¬ rconj V₁ g ≤ V) :
    conjClosure V H ⊔ rconj (conjClosure V H) g = L ⊔ conjClosure V H := by
  obtain ⟨D, hperp⟩ := hyp.module
  exact (⟨hyp, D, hperp⟩ : Om4Setting V V₁ L T H).I_eq_LU hg hgV

theorem G26_two {U I S W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgV : ¬ rconj V₁ g ≤ V) (hI : I = U ⊔ rconj U g) (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S) :
    S = W ⊔ rconj W g ∧ (S : Set G) = (W : Set G) * (rconj W g : Set G) := by
  obtain ⟨D, hperp⟩ := hyp.module
  let St : Om4Setting V V₁ L T H := ⟨hyp, D, hperp⟩
  subst hS
  subst hW
  have hI' := St.I_eq_LU' hU hg hgV hI
  have hLI : L ≤ I := hI' ▸ le_sup_left
  obtain ⟨-, -, -, hINorm, hSxU⟩ := sx_facts_gen hI' (St.U_le_T' hU)
    (by rw [hU]; exact St.T_le_normU) hyp.base.T_le_normL hyp.base.sylow_LT
  exact pCoreOf_I_eq_of_le hI (hLI hg) hINorm hSxU (St.pCoreOf_I_le_P hU hg hgV hI)

theorem G26_three {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgV : ¬ rconj V₁ g ≤ V) (hI : I = U ⊔ rconj U g) :
    conjClosure V₁ L ≤ conjClosure V₁ L ⊔ (U ⊓ rconj U g) ∧
      conjClosure V₁ L ⊔ (U ⊓ rconj U g) ≤ pCoreOf 2 I ∧
      conjClosure V₁ L ≤ centerOf (pCoreOf 2 I) ∧
      I ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) ∧
      I ≤ Subgroup.normalizer ((conjClosure V₁ L ⊔ (U ⊓ rconj U g) : Subgroup G) : Set G) ∧
      I ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) := by
  obtain ⟨D, hperp⟩ := hyp.module
  exact (⟨hyp, D, hperp⟩ : Om4Setting V V₁ L T H).I_series hU hg hgV hI

theorem G26_four {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgV : ¬ rconj V₁ g ≤ V) (hI : I = U ⊔ rconj U g) :
    ⁅conjClosure V₁ L ⊔ (U ⊓ rconj U g), I⁆ ≤ conjClosure V₁ L := by
  obtain ⟨D, hperp⟩ := hyp.module
  exact (⟨hyp, D, hperp⟩ : Om4Setting V V₁ L T H).commutator_S₂_le hU hg hgV hI

end AlmostSpecialOm4Hyp

end CFSG.Quasithin
