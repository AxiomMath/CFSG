module

public import CFSG.Monster.B.CTIB.DistThreeProduct
public import CFSG.Monster.B.CTIB.Component

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
  CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical

section Swap

variable {G : Type*} [Group G]

theorem conj_mem_centralizer_iff {d g : G} : g ∈ Subgroup.centralizer {d} ↔ g * d * g⁻¹ = d := by
  rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

theorem conj_mem_centralizer_pair_iff {c e g : G} :
    g ∈ Subgroup.centralizer {c, e} ↔ g * c * g⁻¹ = c ∧ g * e * g⁻¹ = e := by
  rw [Subgroup.mem_centralizer_iff, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h
    exact ⟨(h c (Set.mem_insert c {e})).symm, (h e (Set.mem_insert_of_mem c rfl)).symm⟩
  · rintro ⟨h1, h2⟩ y (rfl | rfl)
    · exact h1.symm
    · exact h2.symm

theorem image_conj_pair_eq_iff {c e g : G} (hne : c ≠ e) :
    (fun x => g * x * g⁻¹) '' {c, e} = {c, e} ↔
      (g * c * g⁻¹ = c ∧ g * e * g⁻¹ = e) ∨ (g * c * g⁻¹ = e ∧ g * e * g⁻¹ = c) := by
  rw [Set.image_pair]
  have hinj : g * c * g⁻¹ ≠ g * e * g⁻¹ := fun h => hne (by simpa using h)
  constructor
  · intro h
    have h1 : g * c * g⁻¹ ∈ ({c, e} : Set G) := h ▸ Set.mem_insert _ _
    have h2 : g * e * g⁻¹ ∈ ({c, e} : Set G) := h ▸ Set.mem_insert_of_mem _ rfl
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hinj
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hinj
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [h1, h2]
    · rw [h1, h2, Set.pair_comm]

end Swap

theorem le_of_isPerfect_of_card_quotient {C : Type*} [Group C] [Finite C] {F K : Subgroup C}
    [F.Normal] {n : ℕ} (hq : Nat.card (C ⧸ F) = 2 ^ n) (hK : Group.IsPerfect K) : K ≤ F := by
  have hp : IsPGroup 2 (C ⧸ F) := IsPGroup.of_card hq
  have : Group.IsNilpotent (C ⧸ F) := hp.isNilpotent
  have hmap : Group.IsPerfect (K.map (QuotientGroup.mk' F)) := Group.IsPerfect.map _
  by_contra hnot
  have hne : K.map (QuotientGroup.mk' F) ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hnot
  have : Nontrivial (K.map (QuotientGroup.mk' F)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  exact Group.IsPerfect.not_isSolvable (K.map (QuotientGroup.mk' F)) inferInstance

theorem unique_component_of_normal_quasisimple {C : Type*} [Group C] [Finite C] {F : Subgroup C}
    [hn : F.Normal] {n : ℕ} (hq : Nat.card (C ⧸ F) = 2 ^ n) (hF : CFSG.IsQuasisimple F) :
    CFSG.IsComponent F ∧ ∀ K : Subgroup C, CFSG.IsComponent K → K = F := by
  refine ⟨⟨hF, hn.isSubnormal⟩, fun K hK => ?_⟩
  have hKle : K ≤ F := le_of_isPerfect_of_card_quotient hq hK.1.1
  have hsub : (K.subgroupOf F).IsSubnormal := hK.2.subgroupOf
  rcases subnormal_eq_top_or_le_center hF hsub with h | h
  · exact le_antisymm hKle (Subgroup.subgroupOf_eq_top.1 h)
  · exfalso
    have hK' : CFSG.IsQuasisimple (K.subgroupOf F) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKle).symm hK.1
    exact not_le_center_of_isQuasisimple hK' h

theorem natCard_quotient_center_of_mulEquiv_F4
    {H : Type*} [Group H]
    (e : adjointGroup Tag.F4 (ZMod 2) ≃* H) :
    Nat.card (H ⧸ Subgroup.center H) = Nat.card (adjointGroup Tag.F4 (ZMod 2)) :=
  Nat.card_congr ((QuotientGroup.congr (Subgroup.center H)
    (Subgroup.center (adjointGroup Tag.F4 (ZMod 2))) e.symm
    (Subgroup.map_center_eq e.symm)).trans (adjointQuotientF4Equiv (ZMod 2))).toEquiv

theorem commutator_subgroupOf_normal {G : Type*} [Group G] {R C : Subgroup G} (hRC : R ≤ C)
    (hidx : R.relIndex C = 2) : (⁅R, R⁆.subgroupOf C).Normal := by
  have hRn : (R.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hidx
  have hle : ⁅R, R⁆ ≤ C := (Subgroup.commutator_le_self R).trans hRC
  have heq : ⁅R, R⁆.subgroupOf C = ⁅R.subgroupOf C, R.subgroupOf C⁆ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hle, inf_eq_left.2 hRC]
  rw [heq]
  exact Subgroup.commutator_normal _ _

theorem centralizer_pair_eq_inf
    (hinj : Function.Injective clabel) (v w : CVert) :
    Subgroup.centralizer {clabelS v, clabelS w} = vStab v ⊓ vStab w := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, ← commute_clabelS_iff hinj v,
    ← commute_clabelS_iff hinj w]
  constructor
  · intro h
    exact ⟨(h _ (Set.mem_insert _ _)).symm, (h _ (Set.mem_insert_of_mem _ rfl)).symm⟩
  · rintro ⟨h1, h2⟩ y (rfl | rfl)
    · exact h1.eq.symm
    · exact h2.eq.symm

theorem mem_centralizer_mul_iff
    (hL : DistThreeLabelsInput) (hO : DistThreeOuterInput)
    (hP : DistThreePathInput) (hT : TypeThreeBoundInput) {v w : CVert}
    (hvw : cgraph.dist v w = 3) (g : Shat) :
    g ∈ Subgroup.centralizer {clabelS v * clabelS w} ↔
      (g * clabelS v * g⁻¹ = clabelS v ∧ g * clabelS w * g⁻¹ = clabelS w) ∨
      (g * clabelS v * g⁻¹ = clabelS w ∧ g * clabelS w * g⁻¹ = clabelS v) := by
  have hLvw := hL v w hvw
  obtain ⟨-, -, hne, hce⟩ := hLvw
  have hc2 := clabelS_mul_clabelS v
  have he2 := clabelS_mul_clabelS w
  have hdc : clabelS v * clabelS w * clabelS v = clabelS w := by
    rw [mul_assoc, hce.eq, ← mul_assoc, hc2, one_mul]
  have hde : clabelS v * clabelS w * clabelS w = clabelS v := by rw [mul_assoc, he2, mul_one]
  have hEnd := (distance_three_product_determines_endpoints hL hO hP hT hvw).1
  rw [conj_mem_centralizer_iff]
  constructor
  · intro hg
    have hmem : ∀ x : Shat,
        clabelS v * clabelS w * x = g * (clabelS v * clabelS w * (g⁻¹ * x * g)) * g⁻¹ := by
      intro x
      calc clabelS v * clabelS w * x =
            (g * (clabelS v * clabelS w) * g⁻¹) * x := by rw [hg]
        _ = g * (clabelS v * clabelS w * (g⁻¹ * x * g)) * g⁻¹ := by group
    have ha : g * clabelS v * g⁻¹ ∈ ({clabelS v, clabelS w} : Set Shat) := by
      rw [← hEnd]
      refine ⟨isConj_iff.2 ⟨g, rfl⟩, ?_⟩
      rw [hmem, show g⁻¹ * (g * clabelS v * g⁻¹) * g = clabelS v by group, hdc]
      exact (isConj_clabelS v w).trans (isConj_iff.2 ⟨g, rfl⟩)
    have hb : g * clabelS w * g⁻¹ ∈ ({clabelS v, clabelS w} : Set Shat) := by
      rw [← hEnd]
      have hcw' : IsConj (clabelS v) (g * clabelS w * g⁻¹) :=
        (isConj_clabelS v w).trans (isConj_iff.2 ⟨g, rfl⟩)
      refine ⟨hcw', ?_⟩
      rw [hmem, show g⁻¹ * (g * clabelS w * g⁻¹) * g = clabelS w by group, hde]
      exact isConj_iff.2 ⟨g, rfl⟩
    have hinj' : g * clabelS v * g⁻¹ ≠ g * clabelS w * g⁻¹ := fun h =>
      hne (by simpa using h.symm)
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hinj'
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
    · exact absurd (ha.trans hb.symm) hinj'
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · calc g * (clabelS v * clabelS w) * g⁻¹ =
            (g * clabelS v * g⁻¹) * (g * clabelS w * g⁻¹) := by group
        _ = clabelS v * clabelS w := congrArg₂ (· * ·) h1 h2
    · calc g * (clabelS v * clabelS w) * g⁻¹ =
            (g * clabelS v * g⁻¹) * (g * clabelS w * g⁻¹) := by group
        _ = clabelS w * clabelS v := congrArg₂ (· * ·) h1 h2
        _ = clabelS v * clabelS w := hce.eq

theorem exists_swap_of_dist_three
    (hP : DistThreePathInput) {v w : CVert}
    (hvw : cgraph.dist v w = 3) :
    ∃ σ : Shat, σ * clabelS v * σ⁻¹ = clabelS w ∧ σ * clabelS w * σ⁻¹ = clabelS v := by
  have hwv : cgraph.dist w v = 3 := by rw [SimpleGraph.dist_comm]; exact hvw
  obtain ⟨g₁, hg₁⟩ := cvMul_transitive v w
  have hw' : cvMul w g₁ ∈ sphereDistThree w := by
    have h := sphereDistThree_cvMul (mem_sphereDistThree.2 hvw) g₁
    rwa [hg₁] at h
  obtain ⟨h, hhw, hhv⟩ := hP.1 w (cvMul w g₁) v hw' (mem_sphereDistThree.2 hwv)
  refine ⟨(g₁ * h)⁻¹, ?_, ?_⟩
  · have h1 := clabelS_cvMul v (g₁ * h)
    rw [cvMul_mul, hg₁, hhw] at h1
    rw [inv_inv, ← h1]
  · have h1 := clabelS_cvMul w (g₁ * h)
    rw [cvMul_mul, hhv] at h1
    rw [inv_inv, ← h1]

theorem relIndex_centralizer_pair
    (hL : DistThreeLabelsInput) (hO : DistThreeOuterInput)
    (hP : DistThreePathInput) (hT : TypeThreeBoundInput) {v w : CVert}
    (hvw : cgraph.dist v w = 3) :
    (Subgroup.centralizer {clabelS v, clabelS w}).relIndex
      (Subgroup.centralizer {clabelS v * clabelS w}) = 2 := by
  have hne := (hL v w hvw).2.2.1
  have hfix := mem_centralizer_mul_iff hL hO hP hT hvw
  obtain ⟨σ, hσc, hσe⟩ := exists_swap_of_dist_three hP hvw
  have hσC : σ ∈ Subgroup.centralizer {clabelS v * clabelS w} := (hfix σ).2 (Or.inr ⟨hσc, hσe⟩)
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨σ, hσC⟩, fun b => ?_⟩
  have hb1 : ((b * ⟨σ, hσC⟩ : Subgroup.centralizer {clabelS v * clabelS w}) : Shat) *
      clabelS v * ((b * ⟨σ, hσC⟩ : Subgroup.centralizer {clabelS v * clabelS w}) : Shat)⁻¹ =
      (b : Shat) * clabelS w * (b : Shat)⁻¹ := by
    calc ((b * ⟨σ, hσC⟩ : Subgroup.centralizer {clabelS v * clabelS w}) : Shat) *
          clabelS v * ((b * ⟨σ, hσC⟩ : Subgroup.centralizer {clabelS v * clabelS w}) : Shat)⁻¹ =
          (b : Shat) * (σ * clabelS v * σ⁻¹) * (b : Shat)⁻¹ := by rw [Subgroup.coe_mul]; group
      _ = (b : Shat) * clabelS w * (b : Shat)⁻¹ :=
        congrArg (fun z => (b : Shat) * z * (b : Shat)⁻¹) hσc
  have hb2 : ((b * ⟨σ, hσC⟩ : Subgroup.centralizer {clabelS v * clabelS w}) : Shat) *
      clabelS w * ((b * ⟨σ, hσC⟩ : Subgroup.centralizer {clabelS v * clabelS w}) : Shat)⁻¹ =
      (b : Shat) * clabelS v * (b : Shat)⁻¹ := by
    calc ((b * ⟨σ, hσC⟩ : Subgroup.centralizer {clabelS v * clabelS w}) : Shat) *
          clabelS w * ((b * ⟨σ, hσC⟩ : Subgroup.centralizer {clabelS v * clabelS w}) : Shat)⁻¹ =
          (b : Shat) * (σ * clabelS w * σ⁻¹) * (b : Shat)⁻¹ := by rw [Subgroup.coe_mul]; group
      _ = (b : Shat) * clabelS v * (b : Shat)⁻¹ :=
        congrArg (fun z => (b : Shat) * z * (b : Shat)⁻¹) hσe
  have hinj' : (b : Shat) * clabelS v * (b : Shat)⁻¹ ≠ (b : Shat) * clabelS w * (b : Shat)⁻¹ :=
    fun h => hne (by simpa using h.symm)
  rcases (hfix b).1 b.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inr ⟨Subgroup.mem_subgroupOf.2 (conj_mem_centralizer_pair_iff.2 ⟨h1, h2⟩),
      fun h => ?_⟩
    have h' := conj_mem_centralizer_pair_iff.1 (Subgroup.mem_subgroupOf.1 h)
    exact hne ((hb2.symm.trans h'.2).symm.trans h1)
  · refine Or.inl ⟨Subgroup.mem_subgroupOf.2
      (conj_mem_centralizer_pair_iff.2 ⟨hb1.trans h2, hb2.trans h1⟩), fun h => ?_⟩
    have h' := conj_mem_centralizer_pair_iff.1 (Subgroup.mem_subgroupOf.1 h)
    exact hinj' (h'.1.trans h2.symm)

theorem distance_three_product_full_centralizer
    (hL : DistThreeLabelsInput)
    (hO : DistThreeOuterInput) (hP : DistThreePathInput) (hT : TypeThreeBoundInput)
    {v w : CVert} (hvw : cgraph.dist v w = 3) {R F C : Subgroup Shat}
    (hR : R = Subgroup.centralizer {clabelS v, clabelS w}) (hF : F = ⁅R, R⁆)
    (hC : C = Subgroup.centralizer {clabelS v * clabelS w}) :
    (∀ g : Shat, g ∈ C ↔
      (fun x => g * x * g⁻¹) '' {clabelS v, clabelS w} = {clabelS v, clabelS w}) ∧
    R = vStab v ⊓ vStab w ∧ R ≤ C ∧ R.relIndex C = 2 ∧ (F.subgroupOf C).Normal ∧
    Nat.card C = 26489012826931200 ∧ Nat.card C = 8 * Nat.card (adjointGroup Tag.F4 (ZMod 2)) ∧
    Nat.card (C ⧸ F.subgroupOf C) = 8 ∧ Nat.card F = 3311126603366400 ∧
    CFSG.IsComponent (F.subgroupOf C) ∧
    (∀ K : Subgroup C, CFSG.IsComponent K → K = F.subgroupOf C) ∧
    F = pairF4 v w ∧ IsSimpleGroup F ∧ IsSimpleGroup (adjointGroup Tag.F4 (ZMod 2)) ∧
    (∃ Ψ : groupJ ≃* adjointGroup Tag.F4 (ZMod 2),
      (∀ (g : twistedFixedGroup TwistTag.E6 (ZMod 2) (RingHom.id (ZMod 2))) (x : groupJ),
        ((x : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) =
            baseChangeGL (algebraMap (ZMod 2) K) (g : ModGL TwistTag.E6.tag (ZMod 2)) →
          (Ψ x : ModGL Tag.F4 (ZMod 2)) = e6FixedToF4 (ZMod 2) g) ∧
      ∀ ρ : vStab v →* GStar, Function.Surjective ρ →
        (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) →
        ∀ s : vStab v, (s : Shat) = clabelS w → ρ s = betaStarElt →
          ∃ φ : F ≃* groupJ,
            (∀ (f : F) (y : vStab v), (y : Shat) = f →
              ρ y = SemidirectProduct.inl ⟨(φ f : ModGL Tag.E6 K), groupJ_le_stdGroup (φ f).2⟩) ∧
            ∃ e : F ≃* adjointGroup Tag.F4 (ZMod 2), ∀ f, e f = Ψ (φ f)) ∧
    ∀ K : Subgroup C, CFSG.IsComponent K →
      IsSimpleGroup (K ⧸ Subgroup.center K) ∧ 17 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  subst hR hC
  have hinj := clabel_injective_of_inputs hL hO hP hT
  have hne := (hL v w hvw).2.2.1
  have hfix := mem_centralizer_mul_iff hL hO hP hT hvw
  have hstab : ∀ g : Shat, g ∈ Subgroup.centralizer {clabelS v * clabelS w} ↔
      (fun x => g * x * g⁻¹) '' {clabelS v, clabelS w} = {clabelS v, clabelS w} := fun g =>
    (hfix g).trans (image_conj_pair_eq_iff (Ne.symm hne)).symm
  have hRv := centralizer_pair_eq_inf hinj v w
  have hRC : Subgroup.centralizer {clabelS v, clabelS w} ≤
      Subgroup.centralizer {clabelS v * clabelS w} := fun x hx =>
    (hfix x).2 (Or.inl (conj_mem_centralizer_pair_iff.1 hx))
  have hidx := relIndex_centralizer_pair hL hO hP hT hvw
  have hFn := commutator_subgroupOf_normal hRC hidx
  have hsplit := native_distance_three_pair_split_pinned_F4 hL hO hP hT hvw
  have hFp : F = pairF4 v w := by rw [hF, hRv, hsplit.1]
  rw [← hF] at hFn
  subst hFp
  obtain ⟨-, -, ⟨s₀, hs₀, ρ₀, iv₀, hρ₀, hρ₀s⟩, Ψ, hΨ, hall⟩ := hsplit
  have hφ₀ := hall ρ₀ hρ₀.1 hρ₀.2.1 s₀ hs₀ hρ₀s
  obtain ⟨φ₀, -, -⟩ := hφ₀
  have hFR : pairF4 v w ≤ Subgroup.centralizer {clabelS v, clabelS w} := by
    rw [hRv]
    exact pairF4_le_inf v w
  have hFC : pairF4 v w ≤ Subgroup.centralizer {clabelS v * clabelS w} := hFR.trans hRC
  have hRcard : Nat.card (Subgroup.centralizer ({clabelS v, clabelS w} : Set Shat)) =
      13244506413465600 := by
    have h := native_distance_three_pair_is_full_local_centralizer hL hO hP hT hvw
    obtain ⟨-, -, -, -, -, hcard, -⟩ := h
    rw [hRv]
    exact hcard
  have hCcard : Nat.card (Subgroup.centralizer {clabelS v * clabelS w}) = 26489012826931200 := by
    have h := Subgroup.relIndex_mul_card (Subgroup.centralizer {clabelS v, clabelS w})
      (Subgroup.centralizer {clabelS v * clabelS w})
    rw [hidx, inf_eq_left.2 hRC, hRcard] at h
    omega
  have hFcard : Nat.card (pairF4 v w) = 3311126603366400 :=
    (Nat.card_congr φ₀.toEquiv).trans CFSG.Monster.B.E6.FieldInvF4.card_groupJ
  have hF4card : Nat.card (adjointGroup Tag.F4 (ZMod 2)) = 3311126603366400 :=
    (Nat.card_congr Ψ.toEquiv).symm.trans CFSG.Monster.B.E6.FieldInvF4.card_groupJ
  have hF'card : Nat.card ((pairF4 v w).subgroupOf (Subgroup.centralizer
      {clabelS v * clabelS w})) = 3311126603366400 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv).trans hFcard
  have hquot : Nat.card (Subgroup.centralizer {clabelS v * clabelS w} ⧸
      (pairF4 v w).subgroupOf (Subgroup.centralizer {clabelS v * clabelS w})) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((pairF4 v w).subgroupOf (Subgroup.centralizer {clabelS v * clabelS w}))
    rw [hCcard, hF'card] at h
    omega
  have e' : adjointGroup Tag.F4 (ZMod 2) ≃*
      (pairF4 v w).subgroupOf (Subgroup.centralizer {clabelS v * clabelS w}) :=
    (φ₀.trans Ψ).symm.trans (Subgroup.subgroupOfEquivOfLe hFC).symm
  have hFq : CFSG.IsQuasisimple
      ((pairF4 v w).subgroupOf (Subgroup.centralizer {clabelS v * clabelS w})) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e'
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 (ZMod 2))
  have hU := unique_component_of_normal_quasisimple (n := 3) (by rw [hquot]; norm_num) hFq
  have hquotF := (natCard_quotient_center_of_mulEquiv_F4 e').trans hF4card
  refine ⟨hstab, hRv, hRC, hidx, hFn, hCcard, by rw [hCcard, hF4card], hquot, hFcard, hU.1,
    hU.2, rfl, @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_groupJ φ₀,
    @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_groupJ Ψ.symm,
    ⟨Ψ, hΨ, fun ρ hρ hker s hs hρs => ?_⟩, fun K hK => ?_⟩
  · have h := hall ρ hρ hker s hs hρs
    obtain ⟨φ, hφ, he, -⟩ := h
    exact ⟨φ, hφ, he⟩
  · rw [hU.2 K hK]
    refine ⟨hFq.2.1, ?_⟩
    rw [hquotF]
    norm_num

end CFSG.Monster.B.CTIB
