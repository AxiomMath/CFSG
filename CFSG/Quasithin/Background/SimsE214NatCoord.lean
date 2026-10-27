module

public import CFSG.Quasithin.Background.SimsE2Defs
public import CFSG.Quasithin.Background.G2SL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs

public section

open scoped commutatorElement MatrixGroups

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank SL2Model

namespace E214N

variable {Γ : Type} [Group Γ]

section Coord

variable {P : Subgroup Γ} {F : Type} [Field F] {s : ℕ}
  (φ : ↥P →* Multiplicative (Fin s → Fin 2 → F))

@[expose] def coordSub (S : Set (Fin s)) : Subgroup Γ where
  carrier := {x | ∃ hx : x ∈ P, ∀ l ∈ S, Multiplicative.toAdd (φ ⟨x, hx⟩) l = 0}
  mul_mem' := by
    rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
    refine ⟨P.mul_mem hx hy, fun l hl => ?_⟩
    have e : φ ⟨x * y, P.mul_mem hx hy⟩ = φ ⟨x, hx⟩ * φ ⟨y, hy⟩ := map_mul φ ⟨x, hx⟩ ⟨y, hy⟩
    rw [e, toAdd_mul, Pi.add_apply, hx0 l hl, hy0 l hl, add_zero]
  one_mem' := ⟨P.one_mem, fun l _ => by
    have e : φ ⟨1, P.one_mem⟩ = 1 := map_one φ
    rw [e, toAdd_one, Pi.zero_apply]⟩
  inv_mem' := by
    rintro x ⟨hx, hx0⟩
    refine ⟨P.inv_mem hx, fun l hl => ?_⟩
    have e : φ ⟨x⁻¹, P.inv_mem hx⟩ = (φ ⟨x, hx⟩)⁻¹ := map_inv φ ⟨x, hx⟩
    rw [e, toAdd_inv, Pi.neg_apply, hx0 l hl, neg_zero]

theorem mem_coordSub {S : Set (Fin s)} {x : Γ} :
    x ∈ coordSub φ S ↔ ∃ hx : x ∈ P, ∀ l ∈ S, Multiplicative.toAdd (φ ⟨x, hx⟩) l = 0 :=
  Iff.rfl

theorem coordSub_le (S : Set (Fin s)) : coordSub φ S ≤ P := fun _ hx =>
  ((mem_coordSub φ).1 hx).1

theorem le_coordSub {Z : Subgroup Γ} (hZP : Z ≤ P) (hφk : ∀ x : ↥P, φ x = 1 ↔ (x : Γ) ∈ Z)
    (S : Set (Fin s)) : Z ≤ coordSub φ S := fun z hz =>
  (mem_coordSub φ).2 ⟨hZP hz, fun l _ => by
    rw [(hφk ⟨z, hZP hz⟩).2 hz, toAdd_one, Pi.zero_apply]⟩

theorem le_normalizer_coordSub {I : Subgroup Γ} (hIP : I ≤ Subgroup.normalizer (P : Set Γ))
    (β : ↥I →* SL(2, F))
    (hφe : ∀ (m : ↥I) (x y : ↥P), (y : Γ) = m * x * m⁻¹ →
      φ y = Multiplicative.ofAdd (fun j => β m • Multiplicative.toAdd (φ x) j))
    (S : Set (Fin s)) : I ≤ Subgroup.normalizer (coordSub φ S : Set Γ) := by
  have key : ∀ m ∈ I, ∀ x ∈ coordSub φ S, m * x * m⁻¹ ∈ coordSub φ S := by
    intro m hm x hxS
    obtain ⟨hx, hx0⟩ := (mem_coordSub φ).1 hxS
    have hmx : m * x * m⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hIP hm) x).mp hx
    refine (mem_coordSub φ).2 ⟨hmx, fun l hl => ?_⟩
    rw [hφe ⟨m, hm⟩ ⟨x, hx⟩ ⟨m * x * m⁻¹, hmx⟩ rfl]
    simp only [toAdd_ofAdd, hx0 l hl, smul_zero]
  exact fun m hm => B6.mem_normalizer_of_forall_mem (key m hm)
    (fun x hx => by simpa using key m⁻¹ (I.inv_mem hm) x hx)

theorem isSumOfNaturalSections_of_coord {I Z J : Subgroup Γ} (hZP : Z ≤ P) (hJI : J ≤ I)
    (hIP : I ≤ Subgroup.normalizer (P : Set Γ)) (hIZ : I ≤ Subgroup.normalizer (Z : Set Γ))
    (β : ↥I →* SL(2, F)) (hβs : Function.Surjective β) (hβk : ∀ x : ↥I, β x = 1 ↔ (x : Γ) ∈ J)
    (hs : 0 < s) (hφs : Function.Surjective φ) (hφk : ∀ x : ↥P, φ x = 1 ↔ (x : Γ) ∈ Z)
    (hφe : ∀ (m : ↥I) (x y : ↥P), (y : Γ) = m * x * m⁻¹ →
      φ y = Multiplicative.ofAdd (fun j => β m • Multiplicative.toAdd (φ x) j)) :
    IsSumOfNaturalSections s I P Z J (StatedSL 2 F) := by
  classical
  have hWP : ∀ j : Fin s, coordSub φ {l | l ≠ j} ≤ P := fun j => coordSub_le φ _
  have hsingle : ∀ j (w : Fin 2 → F), ∃ y : ↥P, (y : Γ) ∈ coordSub φ {l | l ≠ j} ∧
      φ y = Multiplicative.ofAdd (Pi.single j w) := by
    intro j w
    obtain ⟨y, hy⟩ := hφs (Multiplicative.ofAdd (Pi.single j w))
    refine ⟨y, (mem_coordSub φ).2 ⟨y.2, fun l hl => ?_⟩, hy⟩
    have e : φ ⟨(y : Γ), y.2⟩ = Multiplicative.ofAdd (Pi.single j w) := hy
    rw [e, toAdd_ofAdd, Pi.single_eq_of_ne hl]
  have hnat : ∀ j, IsNaturalSection I (coordSub φ {l | l ≠ j}) Z J (StatedSL 2 F) := by
    intro j
    let ρ : ↥I →* ↥(StatedSL 2 F) := (specialLinearGroupEquivStatedSL 2 F).toMonoidHom.comp β
    let ψ : ↥(coordSub φ {l | l ≠ j}) →* Multiplicative (Fin 2 → F) :=
      (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin s => Fin 2 → F) j)).comp
        (φ.comp (Subgroup.inclusion (hWP j)))
    have hψ : ∀ w : ↥(coordSub φ {l | l ≠ j}), Multiplicative.toAdd (ψ w) =
        Multiplicative.toAdd (φ (Subgroup.inclusion (hWP j) w)) j := fun w => rfl
    refine ⟨le_coordSub φ hZP hφk _, hJI, le_normalizer_coordSub φ hIP β hφe _, hIZ, ρ, ψ,
      (specialLinearGroupEquivStatedSL 2 F).surjective.comp hβs, ?_, ?_, ?_, ?_⟩
    · ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hβk x]
      exact MulEquiv.map_eq_one_iff (specialLinearGroupEquivStatedSL 2 F)
    · intro v
      obtain ⟨y, hyW, hy⟩ := hsingle j (Multiplicative.toAdd v)
      refine ⟨⟨y, hyW⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [hψ]
      have e : φ (Subgroup.inclusion (hWP j) ⟨(y : Γ), hyW⟩) =
          Multiplicative.ofAdd (Pi.single j (Multiplicative.toAdd v)) := hy
      rw [e, toAdd_ofAdd, Pi.single_eq_same]
    · ext w
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      obtain ⟨hwP, hw0⟩ := (mem_coordSub φ).1 w.2
      constructor
      · intro h1
        have h2 : Multiplicative.toAdd (φ (Subgroup.inclusion (hWP j) w)) j = 0 := by
          have h3 := congrArg Multiplicative.toAdd h1
          rw [hψ, toAdd_one] at h3
          exact h3
        refine (hφk (Subgroup.inclusion (hWP j) w)).1 ?_
        apply Multiplicative.toAdd.injective
        funext l
        rw [toAdd_one, Pi.zero_apply]
        by_cases hl : l = j
        · rw [hl]
          exact h2
        · exact hw0 l hl
      · intro h1
        apply Multiplicative.toAdd.injective
        rw [hψ, (hφk (Subgroup.inclusion (hWP j) w)).2 h1, toAdd_one, toAdd_one, Pi.zero_apply]
    · intro m u v huv
      apply Multiplicative.toAdd.injective
      rw [hψ, hφe m (Subgroup.inclusion (hWP j) u) (Subgroup.inclusion (hWP j) v) huv, hψ]
      rfl
  refine ⟨fun j => coordSub φ {l | l ≠ j}, fun j => ⟨le_coordSub φ hZP hφk _, hWP j,
    le_normalizer_coordSub φ hIP β hφe _, hnat j⟩, ?_, ?_⟩
  ·
    refine le_antisymm (iSup_le hWP) fun x hx => ?_
    have hZK : Z ≤ ⨆ j : Fin s, coordSub φ {l | l ≠ j} :=
      (le_coordSub φ hZP hφk _).trans (le_iSup (fun j : Fin s => coordSub φ {l | l ≠ j}) ⟨0, hs⟩)
    have himg : ∀ v : Fin s → Fin 2 → F, Multiplicative.ofAdd v ∈
        ((⨆ j : Fin s, coordSub φ {l | l ≠ j}).subgroupOf P).map φ := by
      intro v
      rw [← Finset.univ_sum_single v, ofAdd_sum]
      refine Subgroup.prod_mem _ fun j _ => ?_
      obtain ⟨y, hyW, hy⟩ := hsingle j (v j)
      exact Subgroup.mem_map.2 ⟨y, Subgroup.mem_subgroupOf.2
        (le_iSup (fun j : Fin s => coordSub φ {l | l ≠ j}) j hyW), hy⟩
    obtain ⟨y, hyK, hy⟩ := Subgroup.mem_map.1 (himg (Multiplicative.toAdd (φ ⟨x, hx⟩)))
    rw [ofAdd_toAdd] at hy
    have hz : (y : Γ)⁻¹ * x ∈ Z := by
      have h1 := (hφk (y⁻¹ * ⟨x, hx⟩)).1 (by rw [map_mul, map_inv, hy, inv_mul_cancel])
      simpa using h1
    have e : x = y * ((y : Γ)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.1 hyK) (hZK hz)
  ·
    rintro i x ⟨hxi, hxo⟩
    have hle : (⨆ j, ⨆ (_ : j ≠ i), coordSub φ {l | l ≠ j}) ≤ coordSub φ {i} :=
      iSup₂_le fun j hj y hyW => by
        obtain ⟨hy, hy0⟩ := (mem_coordSub φ).1 hyW
        refine (mem_coordSub φ).2 ⟨hy, fun l hl => hy0 l ?_⟩
        rw [Set.mem_singleton_iff] at hl
        rw [Set.mem_setOf_eq, hl]
        exact Ne.symm hj
    obtain ⟨hxP, hx0⟩ := (mem_coordSub φ).1 hxi
    obtain ⟨hxP', hx1⟩ := (mem_coordSub φ).1 (hle hxo)
    refine (hφk ⟨x, hxP⟩).1 ?_
    apply Multiplicative.toAdd.injective
    funext l
    rw [toAdd_one, Pi.zero_apply]
    by_cases hl : l = i
    · rw [hl]
      exact hx1 i rfl
    · exact hx0 l hl

end Coord

theorem statedSL_exists_mulVec_eq {F : Type} [Field F] {u w : Fin 2 → F} (hu : u ≠ 0)
    (hw : w ≠ 0) :
    ∃ x ∈ StatedSL 2 F, ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec u = w := by
  obtain ⟨A, hA⟩ := exists_smul_eq u w hu hw
  exact ⟨(specialLinearGroupEquivStatedSL 2 F A : GL (Fin 2) F),
    (specialLinearGroupEquivStatedSL 2 F A).2, hA⟩

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain in
theorem statedSp_exists_mulVec_eq {F : Type} [Field F] [CharP F 2] {u w : Fin 2 ⊕ Fin 2 → F}
    (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ x ∈ StatedSp 2 F,
      ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec u = w := by
  have hne : ∀ v : Fin 2 ⊕ Fin 2 → F, v ≠ 0 → v ∘ antiIdx.symm ≠ 0 := by
    intro v hv h0
    apply hv
    funext i
    simpa using congrFun h0 (antiIdx i)
  obtain ⟨y, hy⟩ := CFSG.QuasithinUnique.Setup.X7b.antiSp_exists_mulVec_eq (hne u hu) (hne w hw)
  refine ⟨(antiSpEquiv F y : GL (Fin 2 ⊕ Fin 2) F), (antiSpEquiv F y).2, ?_⟩
  have h1 : ((antiSpEquiv F y : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (glMat (y : GL (Fin 4) F)).submatrix antiIdx antiIdx := spMat_antiSpEquiv y
  rw [h1, Matrix.submatrix_mulVec_equiv, hy]
  funext i
  simp

theorem exists_conj_of_isNaturalSection {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {I U Z J : Subgroup Γ} {S : Subgroup (Matrix.GeneralLinearGroup ι F)}
    (htr : ∀ u w : ι → F, u ≠ 0 → w ≠ 0 →
      ∃ x ∈ S, ((x : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec u = w)
    (hN : IsNaturalSection I U Z J S) {x b : Γ} (hx : x ∈ U) (hxZ : x ∉ Z) (hb : b ∈ U)
    (hbZ : b ∉ Z) : ∃ i ∈ I, i * b * i⁻¹ ∈ U ∧ (i * b * i⁻¹)⁻¹ * x ∈ Z := by
  obtain ⟨-, -, hIU, -, ρ, ψ, hρs, -, -, hψk, heq⟩ := hN
  have hne : ∀ y : ↥U, (y : Γ) ∉ Z → Multiplicative.toAdd (ψ y) ≠ 0 := by
    intro y hy h0
    apply hy
    have h1 : y ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
    rw [hψk, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨m, hmS, hm⟩ := htr _ _ (hne ⟨b, hb⟩ hbZ) (hne ⟨x, hx⟩ hxZ)
  obtain ⟨i, hi⟩ := hρs ⟨m, hmS⟩
  have hibU : (i : Γ) * b * (i : Γ)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hIU i.2) b).mp hb
  refine ⟨i, i.2, hibU, ?_⟩
  have h1 := heq i ⟨b, hb⟩ ⟨_, hibU⟩ rfl
  rw [hi] at h1
  have h2 : ψ ⟨_, hibU⟩ = ψ ⟨x, hx⟩ := by
    rw [h1]
    exact (congrArg Multiplicative.ofAdd hm).trans (ofAdd_toAdd _)
  have h3 : (⟨_, hibU⟩ : ↥U)⁻¹ * ⟨x, hx⟩ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
  rw [hψk, Subgroup.mem_subgroupOf] at h3
  simpa using h3

theorem exists_equiv_mem_Rg_iff {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F]
    [CharP F 2] {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) (θ₁ : X ≃* SL(2, F)) :
    ∃ θ : X ≃* SL(2, F), ∀ t, t ∈ S ↔ θ t ∈ Rg F := by
  have hT1 : IsSylowTwoOf (S.map θ₁.toMonoidHom) ⊤ := by
    refine ⟨le_top, hS.2.1.map θ₁.toMonoidHom, ?_⟩
    rw [show ((S.map θ₁.toMonoidHom).subgroupOf ⊤).index = (S.map θ₁.toMonoidHom).index from
      Subgroup.relIndex_top_right _, Subgroup.index_map_of_bijective θ₁.bijective]
    have h := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h
  have hR : IsSylowTwoOf (Rg F) ⊤ := by
    refine ⟨le_top, Rg_isPGroup, ?_⟩
    rw [show ((Rg F).subgroupOf ⊤).index = (Rg F).index from Subgroup.relIndex_top_right _]
    exact Rg_index_odd
  obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj hR hT1
  refine ⟨θ₁.trans (MulAut.conj c⁻¹), fun t => ?_⟩
  have hθapp : (θ₁.trans (MulAut.conj c⁻¹)) t = c⁻¹ * θ₁ t * c⁻¹⁻¹ := rfl
  rw [hθapp, inv_inv, ← B6.mem_conjSub, ← hc]
  constructor
  · intro ht
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t', ht', he⟩
    rwa [θ₁.injective he] at ht'

theorem e12_mul_e21_ne {F : Type} [Field F] :
    e12 (1 : F) * e21 1 ≠ e21 1 * e12 1 := by
  intro h
  have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem comm_of_mem_Rg {F : Type} [Field F] {a b : SL(2, F)} (ha : a ∈ Rg F) (hb : b ∈ Rg F) :
    a * b = b * a := by
  obtain ⟨x, rfl⟩ := mem_Rg.1 ha
  obtain ⟨y, rfl⟩ := mem_Rg.1 hb
  rw [← e12_add, ← e12_add, add_comm]

theorem mem_Rg_of_lower_left_eq_zero {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {A : SL(2, F)} (hA : A.1 1 0 = 0) : A ∈ Rg F := by
  have hdet := det_eq_one' A
  rw [hA, mul_zero, sub_zero] at hdet
  have ha : A.1 0 0 = 1 := by
    rcases eq_zero_or_one_of_card_two hF (A.1 0 0) with h | h
    · rw [h, zero_mul] at hdet
      exact absurd hdet zero_ne_one
    · exact h
  rw [ha, one_mul] at hdet
  have hAe : A = e12 (A.1 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hA, hdet]
  exact mem_Rg.2 ⟨_, hAe.symm⟩

end E214N

end CFSG.Quasithin.SimsE2
