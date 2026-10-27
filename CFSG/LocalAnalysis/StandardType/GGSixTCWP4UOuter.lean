module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UStd
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrameO
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule

section Inn

theorem exists_hmat_of_mem_inndiagAut
    {τ : Tag} {K : Type} [Field K]
    {α : MulAut ↥(adjointGroup τ K)} (hα : α ∈ LayerSixE.inndiagAut τ K) :
    ∃ h : ModGL τ K, baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
        adjointGroup τ (AlgebraicClosure K) ∧
      ∀ c : ↥(adjointGroup τ K), ((α c : ↥(adjointGroup τ K)) : ModGL τ K) = h * c * h⁻¹ := by
  let Sub : Subgroup (MulAut ↥(adjointGroup τ K)) :=
    { carrier := {α | ∃ h : ModGL τ K, baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
          adjointGroup τ (AlgebraicClosure K) ∧
        ∀ c : ↥(adjointGroup τ K), ((α c : ↥(adjointGroup τ K)) : ModGL τ K) = h * c * h⁻¹}
      one_mem' := ⟨1, by rw [map_one]; exact one_mem _, fun c => by simp⟩
      mul_mem' := by
        rintro α α' ⟨h, hh, hα⟩ ⟨h', hh', hα'⟩
        refine ⟨h * h', ?_, fun c => ?_⟩
        · rw [map_mul]
          exact mul_mem hh hh'
        · rw [MulAut.mul_apply, hα, hα']
          group
      inv_mem' := by
        rintro α ⟨h, hh, hα⟩
        refine ⟨h⁻¹, ?_, fun c => ?_⟩
        · rw [map_inv]
          exact inv_mem hh
        · have h1 := hα (α⁻¹ c)
          rw [MulAut.apply_inv_self] at h1
          rw [inv_inv, h1]
          group }
  have hle : LayerSixE.inndiagAut τ K ≤ Sub := by
    refine sup_le ?_ ?_
    · rintro _ ⟨g, rfl⟩
      refine ⟨(g : ModGL τ K), baseChangeGL_mem_adjointGroup _ g.2, fun c => ?_⟩
      rfl
    · rintro _ ⟨a, rfl⟩
      refine ⟨rootDiagUnit τ a, ?_, fun c => ?_⟩
      · rw [baseChangeGL_rootDiagUnit]
        exact CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _)
      · exact coe_rootDiagAut a c
  exact hle hα

end Inn

section Glue

theorem exists_theta_E6
    {k : Type} [Field k] [Finite k] [CharP k 2] {X : Type*} [Group X]
    (ψ : ↥(e6Data_valid.minGroup k) →* X)
    (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k)) :
    ∃ θ : (↥ψ.range ⧸ Subgroup.center ↥ψ.range) ≃* ↥(adjointGroup .E6 k),
      ∀ u : ↥(e6Data_valid.minGroup k),
        θ (QuotientGroup.mk (ψ.rangeRestrict u)) = e6Isogeny k u := by
  classical
  have hπ : Function.Surjective (e6Isogeny k) := e6Isogeny_surjective k
  have hker' : (e6Isogeny k).ker = Subgroup.center ↥(e6Data_valid.minGroup k) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center
  have hkπ : ψ.ker ≤ (e6Isogeny k).ker := hker.trans hker'.ge
  have hC : Subgroup.center ↥(adjointGroup .E6 k) = ⊥ := center_adjointGroup_eq_bot_field _ k
  have hψ' : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hψ'ker : ψ.rangeRestrict.ker ≤ (e6Isogeny k).ker := by
    rw [ψ.ker_rangeRestrict]
    exact hkπ
  let ε : ↥ψ.range →* ↥(adjointGroup .E6 k) :=
    ψ.rangeRestrict.liftOfSurjective hψ' ⟨e6Isogeny k, hψ'ker⟩
  have hε : ∀ u, ε (ψ.rangeRestrict u) = e6Isogeny k u := fun u =>
    ψ.rangeRestrict.liftOfRightInverse_comp_apply _ _ ⟨e6Isogeny k, hψ'ker⟩ u
  have hεsurj : Function.Surjective ε := by
    intro c
    obtain ⟨u, rfl⟩ := hπ c
    exact ⟨ψ.rangeRestrict u, hε u⟩
  have hεker : ε.ker = Subgroup.center ↥ψ.range := by
    ext y
    obtain ⟨u, rfl⟩ := hψ' y
    rw [MonoidHom.mem_ker, hε, Subgroup.mem_center_iff]
    constructor
    · intro h w
      obtain ⟨v, rfl⟩ := hψ' w
      have hu : u ∈ Subgroup.center ↥(e6Data_valid.minGroup k) := by
        rw [← hker']
        exact h
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hu v)]
    · intro h
      have hcomm : ∀ v, e6Isogeny k v * e6Isogeny k u = e6Isogeny k u * e6Isogeny k v := by
        intro v
        have h1 := h (ψ.rangeRestrict v)
        rw [← map_mul, ← map_mul] at h1
        have h2 : (v * u) * (u * v)⁻¹ ∈ ψ.rangeRestrict.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
        have h3 : e6Isogeny k (v * u) = e6Isogeny k (u * v) := by
          have h4 := hψ'ker h2
          rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h4
          exact h4
        rw [map_mul, map_mul] at h3
        exact h3
      have hu : e6Isogeny k u ∈ Subgroup.center ↥(adjointGroup .E6 k) := by
        rw [Subgroup.mem_center_iff]
        intro c
        obtain ⟨v, rfl⟩ := hπ c
        exact hcomm v
      rw [hC, Subgroup.mem_bot] at hu
      exact hu
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hεker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ε hεsurj), fun u => ?_⟩
  exact hε u


theorem exists_uframeO_E6_core
    {k : Type} [Field k] [Finite k] [CharP k 2] {f : ℕ} (hK : Nat.card k = 2 ^ f)
    (hq : 4 ≤ 2 ^ f) {X : Type} [Group X] {B : Subgroup X}
    (ψ : ↥(e6Data_valid.minGroup k) →* X)
    (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k))
    (hperf : commutator ↥ψ.range = ⊤) (hBfaith : B ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥)
    (hBN : B ≤ Subgroup.normalizer (ψ.range : Set X))
    (hdiag : ∀ b ∈ B, GGPsiInnerDiag (e6Datum k) ψ b) :
    ∃ (S : LangSetup .E6 (AlgebraicClosure k) 5), S.D.q = 2 ^ f ∧
      ∃ fr : GGTCUFrameO ψ.range B (ModGL .E6 (AlgebraicClosure k)),
        fr.Θ.range = S.Γ ∧ ∀ b, fr.ν b ∈ S.D.model := by
  classical
  have hπ : Function.Surjective (e6Isogeny k) := e6Isogeny_surjective _
  have hperfC : commutator ↥(adjointGroup .E6 (k)) = ⊤ :=
    single_edge_perfect .E6 k (by decide)
  obtain ⟨S, hSq, hSΓ, hSmodel⟩ := exists_stdSetup_E6 hK hperfC
  have hSq4 : 4 ≤ S.D.q := hSq ▸ hq
  obtain ⟨θ, hθ⟩ := exists_theta_E6 ψ hker
  let ι₀ : ↥(adjointGroup .E6 (k)) →*
      ModGL .E6 (AlgebraicClosure (k)) :=
    (baseChangeGL (algebraMap (k) (AlgebraicClosure (k)))).comp
      (adjointGroup .E6 (k)).subtype
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hex : ∀ b : ↥B, ∃ α : MulAut ↥(adjointGroup .E6 (k)),
      α ∈ LayerSixE.inndiagAut .E6 (k) ∧
        LayerSixE.GGInduces (e6Isogeny (k)) ψ (b : X) α :=
    fun b => LayerSixE.exists_induces_E6 ψ hker (hBN b.2) (hdiag b b.2)
  choose α hαD hα using hex
  choose hm hhm hhact using fun b : ↥B => exists_hmat_of_mem_inndiagAut (hαD b)
  let m : ↥B → ModGL .E6 (AlgebraicClosure (k)) := fun b =>
    baseChangeGL (algebraMap (k) (AlgebraicClosure (k))) (hm b)
  have hmM : ∀ b, m b ∈ S.D.model := fun b => hSmodel _ (hhm b)
  have hmact : ∀ (b : ↥B) (c : ↥(adjointGroup .E6 (k))),
      ι₀ (α b c) = m b * ι₀ c * (m b)⁻¹ := by
    intro b c
    change baseChangeGL _ ((α b c : ↥(adjointGroup .E6 (k))) :
        ModGL .E6 (k)) = _ * baseChangeGL _ (c : ModGL .E6 (k)) * _
    rw [hhact b c, map_mul, map_mul, map_inv]
  have huniq : ∀ (m₁ m₂ : ModGL .E6 (AlgebraicClosure (k)))
      (σ : MulAut ↥(adjointGroup .E6 (k))), m₁ ∈ S.D.model → m₂ ∈ S.D.model →
      (∀ c, ι₀ (σ c) = m₁ * ι₀ c * m₁⁻¹) → (∀ c, ι₀ (σ c) = m₂ * ι₀ c * m₂⁻¹) → m₁ = m₂ := by
    intro m₁ m₂ σ h₁ h₂ e₁ e₂
    have hz : m₁⁻¹ * m₂ = 1 := by
      refine eq_one_of_commute_Γ S (by decide) hSq4
        (mul_mem (inv_mem (S.D.mem_model.1 h₁).1) (S.D.mem_model.1 h₂).1) ?_
      intro x hx
      rw [hSΓ] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have e : m₁ * ι₀ ⟨y, hy⟩ * m₁⁻¹ = m₂ * ι₀ ⟨y, hy⟩ * m₂⁻¹ :=
        (e₁ ⟨y, hy⟩).symm.trans (e₂ ⟨y, hy⟩)
      show (m₁⁻¹ * m₂) * ι₀ ⟨y, hy⟩ = ι₀ ⟨y, hy⟩ * (m₁⁻¹ * m₂)
      calc (m₁⁻¹ * m₂) * ι₀ ⟨y, hy⟩ = m₁⁻¹ * (m₂ * ι₀ ⟨y, hy⟩ * m₂⁻¹) * m₂ := by group
        _ = ι₀ ⟨y, hy⟩ * (m₁⁻¹ * m₂) := by rw [← e]; group
    exact inv_mul_eq_one.1 hz
  have hBN' : ∀ b : ↥B, (b : X) ∈ Subgroup.normalizer (ψ.range : Set X) := fun b => hBN b.2
  have hmul : ∀ b b' : ↥B, m (b * b') = m b * m b' := by
    intro b b'
    have h1 : α (b * b') = α b * α b' :=
      LayerSixE.GGInduces.unique hπ (hBN' (b * b')) (hα (b * b'))
        ((hα b).mul (hBN' b') (hα b'))
    refine huniq (m (b * b')) (m b * m b') (α (b * b')) (hmM _) (mul_mem (hmM b) (hmM b'))
      (hmact (b * b')) (fun c => ?_)
    rw [h1, MulAut.mul_apply, hmact b, hmact b']
    group
  let ν : ↥B →* ModGL .E6 (AlgebraicClosure (k)) := MonoidHom.mk' m hmul
  have hνinj : Function.Injective ν := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hm1 : m b = 1 := hb
    have hα1 : ∀ c, α b c = c := fun c => hι₀inj (by rw [hmact b c, hm1]; simp)
    have hZ : ∀ j ∈ ψ.range, (b : X) * j * (b : X)⁻¹ * j⁻¹ ∈
        (Subgroup.center ↥ψ.range).map ψ.range.subtype := by
      intro j hj
      obtain ⟨u, rfl⟩ := hj
      obtain ⟨u', hu'⟩ := LayerSixE.exists_conj_eq (hBN' b) u
      have hπ' := hα b u u' hu'
      rw [hα1] at hπ'
      have hc0 : (e6Isogeny (k)) (u' * u⁻¹) = 1 :=
        (map_mul (e6Isogeny (k)) u' u⁻¹).trans
          (by rw [map_inv, hπ', mul_inv_cancel])
      have hc : u' * u⁻¹ ∈ Subgroup.center ↥(e6Data_valid.minGroup (k)) :=
        (CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := k)).le
          hc0
      refine ⟨ψ.rangeRestrict (u' * u⁻¹), ?_, ?_⟩
      · show ψ.rangeRestrict (u' * u⁻¹) ∈ Subgroup.center ↥ψ.range
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨v, rfl⟩ := ψ.rangeRestrict_surjective g
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hc v)]
      · show ψ (u' * u⁻¹) = (b : X) * ψ u * (b : X)⁻¹ * (ψ u)⁻¹
        rw [map_mul, map_inv, hu']
    have hZJ : ∀ z ∈ (Subgroup.center ↥ψ.range).map ψ.range.subtype, ∀ j ∈ ψ.range,
        z * j = j * z := by
      rintro _ ⟨c, hc, rfl⟩ j hj
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨j, hj⟩)).symm
    have hZZ : ∀ z ∈ (Subgroup.center ↥ψ.range).map ψ.range.subtype,
        ∀ z' ∈ (Subgroup.center ↥ψ.range).map ψ.range.subtype, z * z' = z' * z := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc c')).symm
    have hcomm := commute_of_central_commutator' hperf hZJ hZZ hZ
    have hbC : (b : X) ∈ Subgroup.centralizer (ψ.range : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact (hcomm j hj).symm
    have hbbot : (b : X) ∈ B ⊓ Subgroup.centralizer (ψ.range : Set X) :=
      Subgroup.mem_inf.2 ⟨b.2, hbC⟩
    rw [hBfaith, Subgroup.mem_bot] at hbbot
    exact Subtype.ext hbbot
  refine ⟨S, hSq, ?_⟩
  refine ⟨⟨ι₀.comp θ.toMonoidHom, hι₀inj.comp θ.injective, ν, hνinj, ?_⟩, ?_, hmM⟩
  · intro b y y' hy'
    obtain ⟨u, rfl⟩ := ψ.rangeRestrict_surjective y
    obtain ⟨u', rfl⟩ := ψ.rangeRestrict_surjective y'
    have hψu : ψ u' = (b : X) * ψ u * (b : X)⁻¹ := hy'
    have h1 := hα b u u' hψu
    change ι₀ (θ (QuotientGroup.mk (ψ.rangeRestrict u'))) =
      m b * ι₀ (θ (QuotientGroup.mk (ψ.rangeRestrict u))) * (m b)⁻¹
    rw [hθ, hθ, h1, hmact]
  · change (ι₀.comp θ.toMonoidHom).range = S.Γ
    rw [hSΓ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 θ.surjective,
      ← MonoidHom.range_eq_map]
    show ((baseChangeGL (algebraMap (k) (AlgebraicClosure (k)))).comp
      (adjointGroup .E6 (k)).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]


theorem exists_uframeO_E6
    {X : Type} [Group X] [Finite X] {n f p : ℕ}
    {G₀ B D J L : Subgroup X} {x : X} {ψ : (ggU .E6 n f).K →* X}
    (h : GGTCHyp .E6 n f ψ p G₀ B D J L x) (hq : 4 ≤ 2 ^ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (S : LangSetup .E6 (AlgebraicClosure K) 5), S.D.q = 2 ^ f ∧
        ∃ fr : GGTCUFrameO G₀ B (ModGL .E6 (AlgebraicClosure K)),
          fr.Θ.range = S.Γ ∧ ∀ b, fr.ν b ∈ S.D.model := by
  have hf : 1 ≤ f := h.adm.2.1
  have hker := h.ker
  have hperf := h.perfect
  have hrange := h.range
  have hBfaith := h.b_faithful
  have hBN := h.b_norm
  have hdiag := h.b_diag
  subst hrange
  obtain ⟨S, hSq, fr⟩ := exists_uframeO_E6_core (k := GaloisField 2 f)
    (GaloisField.card 2 f (by omega)) hq ψ hker hperf hBfaith hBN hdiag
  exact ⟨GaloisField 2 f, inferInstance, inferInstance, inferInstance, S, hSq, fr⟩

end Glue

section Leaf

theorem upper_E6_of_inputs_outer
    (hR : LangFamilyCompFieldSL)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .E6 n f).K →* X} (h : GGTCHyp .E6 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .E6 f) (htor : p = 3 → p ^ 5 ≤ Nat.card B)
    (hp3 : p = 3 ∧ 3 ∣ 2 ^ f - 1) : Nat.card B ≤ p ^ 4 := by
  have hp := h.prime
  have hp2 := h.ne_two
  have hf : 1 ≤ f := h.adm.2.1
  have hq4 : 4 ≤ 2 ^ f := by
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have h3 := Nat.le_of_dvd (by omega) hp3.2
    omega
  have hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E6 (2 ^ f) :=
    ((LieModel.chevalleyExceptional_iff (by decide)).1 h.model).2.2
  have hTor : UToralAt .E6 p (Nat.card B) := by
    obtain ⟨hp3', -⟩ := hp3
    subst hp3'
    refine utoralAt_of_bigBar (τ := .E6) hp hp2
      ExcFramesHalf.bigElemAbelianToralBar_E6_three ?_
    have h5 := htor rfl
    have h6 : Tag.rank .E6 - 1 = 5 := rfl
    rw [h6]
    exact h5
  obtain ⟨t', m, f', hlt, hm, -⟩ := hF
  obtain ⟨Ψ, ρ, hΨ, -, hρ, horth, hcard, -⟩ := uframeO_main
    (uFieldInput_of_SL hR (Or.inl rfl)) (Or.inr (Or.inl rfl)) hp hp2 (exists_uframeO_E6 h hq4)
    h.b_norm h.b_elem h.d_le h.d_card (h.j_comp.1.trans inf_le_left)
    (Assembly.isComponentOf_iff_open.1 h.j_comp) h.j_cent ⟨t', m, f', hlt, hm⟩ hTor
  have hr := e6_finrank_le_two hΨ hρ horth
  exact hcard.trans (Nat.pow_le_pow_right hp.pos (by omega))

theorem upper_E6_of_inputs
    (hR : LangFamilyCompFieldSL)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .E6 n f).K →* X} (h : GGTCHyp .E6 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .E6 f) (htor : p = 3 → p ^ 5 ≤ Nat.card B) :
    Nat.card B ≤ p ^ 4 := by
  by_cases hp3 : p ≠ 3 ∨ ¬ 3 ∣ 2 ^ f - 1
  · exact upper_E6_of_inputs_inner hR h hF htor hp3
  · push Not at hp3
    exact upper_E6_of_inputs_outer hR h hF htor hp3

end Leaf

end CFSG.StandardType.TableCRes
