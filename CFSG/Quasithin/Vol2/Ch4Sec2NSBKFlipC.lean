module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKFlipB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k j : ℕ}
variable {D : StdData G T L I K m k (m + 1) j} {hj : 0 < j}

@[expose] def AInv (D : StdData G T L I K m k (m + 1) j) (l' : ↥K) : Prop :=
  ∀ a : Fin (m + 1) → ZMod 2, a (Fin.last m) = 0 →
    ((D.α l' : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).mulVec a
      (Fin.last m) = 0

theorem pure_conj (F : RForm D) {g : G} (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I) (E : FlipEq D hj g)
    (hKU : ∀ x : ↥K, ∀ z ∈ uZero I K, (x : G) * z * (x : G)⁻¹ ∈ uZero I K)
    {l' : ↥K} (hl' : AInv D l') {c₂ : G} (hc₂ : c₂ ∈ uZero I K) {b : ↥(astd m)}
    {y : Fin j → ZMod 2} (hcb : coG D c₂ = tens (b : Fin (m + 1) → ZMod 2) y) :
    g * (l' : G) * g⁻¹ * c₂ * (g * (l' : G) * g⁻¹)⁻¹ ∈ uZero I K ∧
      coG D (g * (l' : G) * g⁻¹ * c₂ * (g * (l' : G) * g⁻¹)⁻¹) =
        tens (b : Fin (m + 1) → ZMod 2)
          (E.ab.symm ⟨((D.α l' : GL (Fin (m + 1)) (ZMod 2)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).mulVec (E.ab y : Fin (m + 1) → ZMod 2),
            (mem_astd _).mpr (hl' _ ((mem_astd _).mp (E.ab y).2))⟩) := by
  obtain ⟨c₁, hc₁Z, hc₁c, hc₁Z', hc₁c'⟩ := exists_pure_flip hj F h1 h2 E (E.ab y) (E.ab'.symm b)
  have hc₂c₁ : g * c₁ * g⁻¹ = c₂ := by
    apply coG_injOn D hc₁Z' hc₂
    rw [hc₁c', hcb, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  have hc₃Z : (l' : G) * c₁ * (l' : G)⁻¹ ∈ uZero I K := hKU l' c₁ hc₁Z
  have hc₃c : coG D ((l' : G) * c₁ * (l' : G)⁻¹) = tens
      ((((D.α l' : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).mulVec
        (E.ab y : Fin (m + 1) → ZMod 2))) (E.ab'.symm b) := by
    funext i
    rw [coG_conj_K D hc₁Z hc₃Z i, hc₁c]
    exact congrFun (tens_mulVec _ _ _) i
  obtain ⟨c₄, hc₄Z, hc₄c, hc₄Z', hc₄c'⟩ := exists_pure_flip hj F h1 h2 E
    ⟨_, (mem_astd _).mpr (hl' _ ((mem_astd _).mp (E.ab y).2))⟩ (E.ab'.symm b)
  have hc₄ : c₄ = (l' : G) * c₁ * (l' : G)⁻¹ := coG_injOn D hc₄Z hc₃Z (by rw [hc₄c, hc₃c])
  have hconj : g * (l' : G) * g⁻¹ * c₂ * (g * (l' : G) * g⁻¹)⁻¹ =
      g * ((l' : G) * c₁ * (l' : G)⁻¹) * g⁻¹ := by
    rw [← hc₂c₁]
    group
  rw [hconj, ← hc₄]
  exact ⟨hc₄Z', by rw [hc₄c', AddEquiv.apply_symm_apply]⟩

private theorem add_add_cancel_nsbkfc {n : ℕ} (x y : Fin j → Fin n → ZMod 2) : x + (x + y) = y := by
  funext i b
  simp only [Pi.add_apply]
  have h : ∀ u v : ZMod 2, u + (u + v) = v := by decide
  exact h _ _

@[expose] def pureSet (D : StdData G T L I K m k (m + 1) j) : Set G :=
  {c | c ∈ uZero I K ∧ ∃ (a₀ : Fin (m + 1) → ZMod 2) (x : Fin j → ZMod 2),
    a₀ (Fin.last m) = 0 ∧ coG D c = tens a₀ x}

theorem mem_closure_pure {t : G} (ht : t ∈ uZero I K) (hw : wZ D t = 0) :
    t ∈ Subgroup.closure (pureSet D) := by
  classical
  have key : ∀ s : Finset (Fin (m + 1)), ∀ z ∈ uZero I K,
      coG D z = ∑ b ∈ s, tens (Pi.single b (1 : ZMod 2) : Fin (m + 1) → ZMod 2)
        (fun i => coG D t i b) → z ∈ Subgroup.closure (pureSet D) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z hz h
      rw [Finset.sum_empty] at h
      have : z = 1 := coG_injOn D hz (one_mem _) (by rw [h, coG_one D])
      rw [this]
      exact one_mem _
    | insert b s hb ih =>
      intro z hz h
      rw [Finset.sum_insert hb] at h
      by_cases hbl : b = Fin.last m
      · have h0 : tens (Pi.single b (1 : ZMod 2) : Fin (m + 1) → ZMod 2)
            (fun i => coG D t i b) = 0 := by
          rw [hbl]
          have : (fun i => coG D t i (Fin.last m)) = (0 : Fin j → ZMod 2) := hw
          rw [this]
          exact tens_zero_right _
        rw [h0, zero_add] at h
        exact ih z hz h
      · set p : G := zE D (tens (Pi.single b (1 : ZMod 2) : Fin (m + 1) → ZMod 2)
          (fun i => coG D t i b)) with hp
        have hpZ : p ∈ uZero I K := zE_mem D _
        have hpc : coG D p = tens (Pi.single b (1 : ZMod 2) : Fin (m + 1) → ZMod 2)
            (fun i => coG D t i b) := coG_zE D _
        have hpP : p ∈ pureSet D :=
          ⟨hpZ, _, _, by simp [Pi.single_apply, Ne.symm hbl], hpc⟩
        have hz' : p⁻¹ * z ∈ uZero I K :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ hpZ) hz
        have h' : coG D (p⁻¹ * z) = ∑ b ∈ s, tens (Pi.single b (1 : ZMod 2) : Fin (m + 1) → ZMod 2)
            (fun i => coG D t i b) := by
          rw [coG_mul D (Subgroup.inv_mem _ hpZ) hz, coG_inv D hpZ, hpc, h]
          exact add_add_cancel_nsbkfc _ _
        have h'' := ih _ hz' h'
        have hzp : z = p * (p⁻¹ * z) := by group
        rw [hzp]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure hpP) h''
  refine key Finset.univ t ht ?_
  rw [← sum_tens (coG D t)]

@[expose] def wSub (D : StdData G T L I K m k (m + 1) j) : Subgroup G where
  carrier := {z | z ∈ uZero I K ∧ wZ D z = 0}
  mul_mem' := by
    rintro x y ⟨hx, hwx⟩ ⟨hy, hwy⟩
    exact ⟨Subgroup.mul_mem _ hx hy, by rw [wZ_mul D hx hy, hwx, hwy, add_zero]⟩
  one_mem' := ⟨one_mem _, wZ_one D⟩
  inv_mem' := by
    rintro x ⟨hx, hwx⟩
    exact ⟨Subgroup.inv_mem _ hx, by rw [wZ_inv D hx, hwx]⟩

theorem flip_maps_V (F : RForm D) {g : G} (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I) (E : FlipEq D hj g) {t : G}
    (ht : t ∈ wSub D) : g * t * g⁻¹ ∈ wSub D := by
  have hP : Subgroup.closure (pureSet D) ≤ (wSub D).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro c ⟨hcZ, a₀, x, ha₀, hcc⟩
    obtain ⟨c₁, hc₁Z, hc₁c, hc₁Z', hc₁c'⟩ :=
      exists_pure_flip hj F h1 h2 E ⟨a₀, (mem_astd _).mpr ha₀⟩ x
    have hcc₁ : c₁ = c := coG_injOn D hc₁Z hcZ (by rw [hc₁c]; exact hcc.symm)
    show g * c * g⁻¹ ∈ wSub D
    rw [← hcc₁]
    refine ⟨hc₁Z', ?_⟩
    funext i
    have h := congrFun (congrFun hc₁c' i) (Fin.last m)
    have hast : (E.ab' x : Fin (m + 1) → ZMod 2) (Fin.last m) = 0 := (mem_astd _).mp (E.ab' x).2
    simp only [wZ, tens_apply_apply] at h ⊢
    rw [h, hast, mul_zero]
    rfl
  exact hP (mem_closure_pure ht.1 ht.2)

theorem flip_commutes (F : RForm D) {g : G} (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I) (E : FlipEq D hj g)
    (hKU : ∀ x : ↥K, ∀ z ∈ uZero I K, (x : G) * z * (x : G)⁻¹ ∈ uZero I K)
    {l l' : ↥K} (hl : AInv D l) (hl' : AInv D l') {t : G} (ht : t ∈ wSub D) :
    (g * (l' : G) * g⁻¹ * (l : G)) * t * (g * (l' : G) * g⁻¹ * (l : G))⁻¹ =
      ((l : G) * (g * (l' : G) * g⁻¹)) * t * ((l : G) * (g * (l' : G) * g⁻¹))⁻¹ := by
  have hS : Subgroup.closure (pureSet D) ≤ MonoidHom.eqLocus
      (MulAut.conj (g * (l' : G) * g⁻¹ * (l : G))).toMonoidHom
      (MulAut.conj ((l : G) * (g * (l' : G) * g⁻¹))).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro c ⟨hcZ, a₀, x₀, ha₀, hcc⟩
    have hc₂Z : (l : G) * c * (l : G)⁻¹ ∈ uZero I K := hKU l c hcZ
    have hc₂c : coG D ((l : G) * c * (l : G)⁻¹) = tens
        (((D.α l : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).mulVec
          a₀) x₀ := by
      funext i
      rw [coG_conj_K D hcZ hc₂Z i, hcc]
      exact congrFun (tens_mulVec _ _ _) i
    have hla₀ : ((D.α l : GL (Fin (m + 1)) (ZMod 2)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).mulVec a₀ (Fin.last m) = 0 := hl a₀ ha₀
    obtain ⟨hAZ, hAc⟩ := pure_conj F h1 h2 E hKU hl' hc₂Z
      (b := ⟨_, (mem_astd _).mpr hla₀⟩) (y := x₀) hc₂c
    obtain ⟨hBZ, hBc⟩ := pure_conj F h1 h2 E hKU hl' hcZ (b := ⟨a₀, (mem_astd _).mpr ha₀⟩)
      (y := x₀) hcc
    have hc₄Z : (l : G) * (g * (l' : G) * g⁻¹ * c * (g * (l' : G) * g⁻¹)⁻¹) * (l : G)⁻¹ ∈
        uZero I K := hKU l _ hBZ
    have hc₄c : coG D ((l : G) * (g * (l' : G) * g⁻¹ * c * (g * (l' : G) * g⁻¹)⁻¹) *
        (l : G)⁻¹) = tens
        (((D.α l : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).mulVec
          a₀) (E.ab.symm ⟨((D.α l' : GL (Fin (m + 1)) (ZMod 2)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).mulVec (E.ab x₀ : Fin (m + 1) → ZMod 2),
            (mem_astd _).mpr (hl' _ ((mem_astd _).mp (E.ab x₀).2))⟩) := by
      funext i
      rw [coG_conj_K D hBZ hc₄Z i, hBc]
      exact congrFun (tens_mulVec _ _ _) i
    have heq : g * (l' : G) * g⁻¹ * ((l : G) * c * (l : G)⁻¹) * (g * (l' : G) * g⁻¹)⁻¹ =
        (l : G) * (g * (l' : G) * g⁻¹ * c * (g * (l' : G) * g⁻¹)⁻¹) * (l : G)⁻¹ :=
      coG_injOn D hAZ hc₄Z (by rw [hAc, hc₄c])
    show (g * (l' : G) * g⁻¹ * (l : G)) * c * (g * (l' : G) * g⁻¹ * (l : G))⁻¹ =
      ((l : G) * (g * (l' : G) * g⁻¹)) * c * ((l : G) * (g * (l' : G) * g⁻¹))⁻¹
    calc (g * (l' : G) * g⁻¹ * (l : G)) * c * (g * (l' : G) * g⁻¹ * (l : G))⁻¹
        = g * (l' : G) * g⁻¹ * ((l : G) * c * (l : G)⁻¹) * (g * (l' : G) * g⁻¹)⁻¹ := by group
      _ = (l : G) * (g * (l' : G) * g⁻¹ * c * (g * (l' : G) * g⁻¹)⁻¹) * (l : G)⁻¹ := heq
      _ = ((l : G) * (g * (l' : G) * g⁻¹)) * c * ((l : G) * (g * (l' : G) * g⁻¹))⁻¹ := by group
  exact hS (mem_closure_pure ht.1 ht.2)

end CFSG.Quasithin.H13.Ch4.NSB
