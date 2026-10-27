module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTBFrame
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLCover
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Cover
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLMod
public import CFSG.LocalAnalysis.StandardType.GGTableBLinIrredDef
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRestTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.LinTwoTB

open Matrix CFSG CFSG.Assembly TableB CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.StandardType.LinTwoTv

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem exists_data_with_rank_bound (hK : Nat.card K = 2) (hd : 6 ≤ d) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* projectiveSL d K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A : Subgroup (MulAut L')) (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    (hr : 3 ^ (d / 2) ≤ Nat.card A) :
    ∃ (s e : ℕ) (D : TorusData L' s) (wt : L' → ℕ),
      (∀ g h : L', MulAut.conj g = MulAut.conj h → g = h) ∧ D.IsTorusAut A ∧ s ≤ d / 2 ∧ 0 < e ∧
      (∀ v, wt (D.el v) = e * hamWt v) ∧ (∀ (φ : MulAut L') (g : L'), wt (φ g) = wt g) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  have hperfSL : commutator (SpecialLinearGroup (Fin (m + 2)) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := m + 2) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  have hsec : TypeA.SLHasSections (m + 2) K := TypeA.slHasSections_of_five_le (by omega)
  obtain ⟨φ₀, hφ₀s, hφ₀⟩ := TypeA.exists_sl_cover hsec ψ hψ hker hperf
  have hφ₀inj : Function.Injective φ₀ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply TwoThree.eq_one_of_mem_scalars hK
    rw [← proj_eq_one_iff, ← hφ₀, hg, map_one]
  let Ξ₀ : SpecialLinearGroup (Fin (m + 2)) K ≃* L' := MulEquiv.ofBijective φ₀ ⟨hφ₀inj, hφ₀s⟩
  let Ξ : L' ≃* GL (Fin (m + 2)) K := Ξ₀.symm.trans (glEquivSL hK).symm
  have hconj : ∀ g s : SpecialLinearGroup (Fin (m + 2)) K,
      φ₀ (g * s * g⁻¹) = MulAut.conj (φ₀ g) (φ₀ s) := by
    intro g s
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hinner : ∀ a ∈ A, ∃ b : L', a = MulAut.conj b := by
    intro a ha
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    have h1 := TypeA.act_of_lift hperfSL hker hφ₀ (a := a) (g := TwoThree.toSLHom hK B)
      (by rw [TwoThree.toGL_toSLHom]; exact hφa)
    refine ⟨φ₀ (TwoThree.toSLHom hK B), ?_⟩
    ext l
    obtain ⟨s, rfl⟩ := hφ₀s l
    rw [h1 s, hconj]
  have hZ : ∀ g h : L', MulAut.conj g = MulAut.conj h → g = h := by
    intro g h hgh
    obtain ⟨z, hz⟩ : ∃ z : L', z = h⁻¹ * g := ⟨_, rfl⟩
    have hc : ∀ x : L', z * x = x * z := by
      intro x
      have h1 := congrArg (fun f : MulAut L' => f x) hgh
      simp only [MulAut.conj_apply] at h1
      rw [hz]
      calc h⁻¹ * g * x = h⁻¹ * (g * x * g⁻¹) * g := by group
        _ = h⁻¹ * (h * x * h⁻¹) * g := by rw [h1]
        _ = x * (h⁻¹ * g) := by group
    have hs : Ξ₀.symm z ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 2)) K) := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply Ξ₀.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (hc (Ξ₀ s)).symm
    rw [StandardType.LineL2.center_eq_bot_two hK, Subgroup.mem_bot] at hs
    have h2 : h⁻¹ * g = 1 := by
      have := congrArg Ξ₀ hs
      rw [← hz]
      simpa using this
    exact (inv_mul_eq_one.mp h2).symm
  have hinj : Function.Injective (MulAut.conj : L' →* MulAut L') := fun g h hgh => hZ g h hgh
  set E : Subgroup L' := A.comap (MulAut.conj : L' →* MulAut L') with hE
  have hmemE : ∀ b, b ∈ E ↔ MulAut.conj b ∈ A := fun b => Iff.rfl
  have hAE : ∀ a, a ∈ A ↔ ∃ b ∈ E, a = MulAut.conj b := by
    intro a
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := hinner a ha
      exact ⟨b, (hmemE b).mpr (hb ▸ ha), hb⟩
    · rintro ⟨b, hb, rfl⟩
      exact (hmemE b).mp hb
  have hEel : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA a.2 b.2
    · rw [map_pow, map_one]
      exact hA.2 _ hx
  have hcardE : Nat.card E = Nat.card A := by
    refine Nat.card_congr (Equiv.ofBijective (fun b : E => (⟨MulAut.conj b, b.2⟩ : A))
      ⟨?_, ?_⟩)
    · intro b b' h
      exact Subtype.ext (hinj (congrArg Subtype.val h))
    · rintro ⟨a, ha⟩
      obtain ⟨b, hb, rfl⟩ := (hAE a).mp ha
      exact ⟨⟨b, hb⟩, rfl⟩
  set E' : Subgroup (GL (Fin (m + 2)) K) := E.map Ξ.toMonoidHom with hE'
  have hE'el : IsElemAbelian 3 E' := TableB.isElemAbelian_map hEel Ξ.toMonoidHom
  have hcardE' : 3 ^ ((m + 2) / 2) ≤ Nat.card E' := by
    rw [hE', Subgroup.card_map_of_injective Ξ.injective, hcardE]
    exact hr
  obtain ⟨s, e, D', hD'range, hsd, he, hD'wt⟩ := exists_torusData_with_rank_bound hK hE'el hcardE'
  refine ⟨s, e, D'.map Ξ.symm, fun g => wtGL (Ξ g), hZ, ?_, hsd, he, ?_, ?_⟩
  · intro a
    rw [hAE a]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb' : Ξ b ∈ D'.ι.range := hD'range ▸ ⟨b, hb, rfl⟩
      obtain ⟨v, hv⟩ := D'.mem_tor.mp hb'
      refine ⟨v, ?_⟩
      rw [TorusData.el_map, ← hv, MulEquiv.symm_apply_apply]
    · rintro ⟨v, rfl⟩
      have hv : D'.el v ∈ E' := hD'range ▸ D'.mem_tor.mpr ⟨v, rfl⟩
      obtain ⟨b, hb, hbv⟩ := hv
      refine ⟨b, hb, ?_⟩
      have h1 : Ξ.symm (D'.el v) = b := by
        rw [← hbv]
        exact Ξ.symm_apply_apply b
      rw [TorusData.el_map, h1]
  · intro v
    simp only [TorusData.el_map, MulEquiv.apply_symm_apply]
    exact hD'wt v
  · intro φ g
    have h1 := wtGL_mulAut hK (by omega : 3 ≤ m + 2) (MulAut.congr Ξ φ) (Ξ g)
    simpa [MulAut.congr_apply] using h1

theorem exists_data (hK : Nat.card K = 2) (hd : 6 ≤ d) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* projectiveSL d K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A : Subgroup (MulAut L')) (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    (hr : 3 ^ (d / 2) ≤ Nat.card A) :
    ∃ (s e : ℕ) (D : TorusData L' s) (wt : L' → ℕ),
      (∀ g h : L', MulAut.conj g = MulAut.conj h → g = h) ∧ D.IsTorusAut A ∧ 0 < e ∧
      (∀ v, wt (D.el v) = e * hamWt v) ∧ (∀ (φ : MulAut L') (g : L'), wt (φ g) = wt g) := by
  obtain ⟨s, e, D, wt, hZ, hTA, _hsd, he, hwι, hwt⟩ :=
    exists_data_with_rank_bound hK hd ψ hψ hker hperf A hA hAI hr
  exact ⟨s, e, D, wt, hZ, hTA, he, hwι, hwt⟩

theorem exists_data_card_eq (hK : Nat.card K = 2) (hd : 6 ≤ d) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* projectiveSL d K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A : Subgroup (MulAut L')) (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    (hr : 3 ^ (d / 2) ≤ Nat.card A) :
    Nat.card A = 3 ^ (d / 2) := by
  obtain ⟨s, e, D, wt, hZ, hTA, hsd, he, hwι, hwt⟩ :=
    exists_data_with_rank_bound hK hd ψ hψ hker hperf A hA hAI hr
  have hAeq : A = D.tor.map (MulAut.conj : L' →* MulAut L') := by
    ext a
    rw [Subgroup.mem_map]
    constructor
    · intro ha
      obtain ⟨v, hv⟩ := (hTA a).mp ha
      exact ⟨D.el v, D.mem_tor.mpr ⟨v, rfl⟩, hv.symm⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨v, rfl⟩ := D.mem_tor.mp hx
      exact (hTA (MulAut.conj (D.el v))).mpr ⟨v, rfl⟩
  have hcardTor : Nat.card D.tor = 3 ^ s := by
    rw [TorusData.tor, ← Nat.card_congr (MonoidHom.ofInjective D.inj).toEquiv,
      Nat.card_eq_fintype_card]
    simp [Fintype.card_pi, ZMod.card]
  have hcardA : Nat.card A = 3 ^ s := by
    rw [hAeq, Subgroup.card_map_of_injective (fun x y h => hZ x y h), hcardTor]
  have hge : d / 2 ≤ s := by
    have hpow : 3 ^ (d / 2) ≤ 3 ^ s := by rw [← hcardA]; exact hr
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow
  have hseq : s = d / 2 := le_antisymm hsd hge
  rw [hcardA, hseq]

theorem ggTorusNbrSCr_two (hK : Nat.card K = 2) (hd : 6 ≤ d) :
    GGTorusNbrSCr 3 (d / 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 _
  obtain ⟨s, e, D, wt, hZ, hTA, he, hwι, hwt⟩ := exists_data hK hd ψ hψ hker hperf A hA hAI hr
  exact D.nbr_core hZ hTA he hwι hwt

theorem ggTableBModuleSCr_two (hK : Nat.card K = 2) (hd : 6 ≤ d) :
    GGTableBModuleSCr 3 (d / 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 _
  obtain ⟨s, e, D, wt, hZ, hTA, he, hwι, hwt⟩ := exists_data hK hd ψ hψ hker hperf A hA hAI hr
  exact D.module_core hTA h3

theorem ggTableBActionSCr_two (hK : Nat.card K = 2) (hd : 6 ≤ d) :
    GGTableBActionSCr 3 (d / 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  refine ⟨by norm_num, fun L' _ _ ψ hψ hker hperf A hA hAI hr h3 _ => ?_⟩
  obtain ⟨s, e, D, wt, hZ, hTA, he, hwι, hwt⟩ := exists_data hK hd ψ hψ hker hperf A hA hAI hr
  exact D.action_core hZ hTA he hwι hwt h3

end CFSG.StandardType.LinTwoTB

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem GGLinTwoLabel.twoThree {p : ℕ} {lab : LargeEvenLabel} (h : GGLinTwoLabel p lab) :
    GGTwoThreeLabel p lab :=
  ⟨h.2.2.2, h.2.2.1, Or.inl h.1⟩

theorem ggBstarInnerDiagLInputOn_linTwo : GGBstarInnerDiagLInputOn GGLinTwoLabel :=
  ggBstarInnerDiagLInputOn_of_labels (fun _ _ h => Or.inl h.1) fun _ _ _ hlab h =>
    largeEvenLabelAll_innerDiag_twoThree hlab h.twoThree

theorem largeEvenLabelAll_linTwo_nbr {p : ℕ} {lab : LargeEvenLabel} (h : GGLinTwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbrSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn, hp⟩ := h
  dsimp only at ht hl hn hp
  subst ht hn hp
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', (l + 1) / 2,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TwoThree.ggTorusLift_two hK2 (by omega)),
    ggTorusNbrSCr_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
      (LinTwoTB.ggTorusNbrSCr_two hK2 (by omega))⟩

theorem largeEvenLabelAll_linTwo_module {p : ℕ} {lab : LargeEvenLabel} (h : GGLinTwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTableBModuleSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn, hp⟩ := h
  dsimp only at ht hl hn hp
  subst ht hn hp
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', (l + 1) / 2,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TwoThree.ggTorusLift_two hK2 (by omega)),
    ggTableBModuleSCr_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
      (LinTwoTB.ggTableBModuleSCr_two hK2 (by omega))⟩

theorem largeEvenLabelAll_linTwo_action {p : ℕ} {lab : LargeEvenLabel} (h : GGLinTwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTableBActionSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn, hp⟩ := h
  dsimp only at ht hl hn hp
  subst ht hn hp
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', (l + 1) / 2,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TwoThree.ggTorusLift_two hK2 (by omega)),
    ggTableBActionSCr_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
      (LinTwoTB.ggTableBActionSCr_two hK2 (by omega))⟩

theorem ggTableBCxInputOn_linTwo_holds : GGTableBCxInputOn GGLinTwoLabel :=
  ggTableBCxInputOn_of_labelsSCr (fun _ _ h => Or.inl h.1) ggBstarInnerDiagLInputOn_linTwo
    fun _ _ _ _ h => largeEvenLabelAll_linTwo_nbr h

theorem ggTableBModuleInputOn_linTwo_holds : GGTableBModuleInputOn GGLinTwoLabel :=
  ggTableBModuleInputOn_of_labelsSCr ggBstarInnerDiagLInputOn_linTwo
    fun _ _ _ _ h => largeEvenLabelAll_linTwo_module h

theorem ggTableBActionInputOn_linTwo_holds : GGTableBActionInputOn GGLinTwoLabel :=
  ggTableBActionInputOn_of_labelsSCr ggBstarInnerDiagLInputOn_linTwo
    fun _ _ _ _ h => largeEvenLabelAll_linTwo_action h

theorem ggTableBCxInputOn_of_not_linTwo {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGLinTwoLabel p lab) :
    GGTableBCxInputOn S :=
  (ggTableBCxInputOn_linTwo_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGLinTwoLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBModuleInputOn_of_not_linTwo {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGLinTwoLabel p lab) :
    GGTableBModuleInputOn S :=
  (ggTableBModuleInputOn_linTwo_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGLinTwoLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBActionInputOn_of_not_linTwo {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGLinTwoLabel p lab) :
    GGTableBActionInputOn S :=
  (ggTableBActionInputOn_linTwo_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGLinTwoLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

end CFSG.StandardType

end
