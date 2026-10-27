module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4Thm
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.Open
  CFSG.Assembly

theorem ggIsReflection_mul_inv {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {φ : MulAut ↥Bs}
    (h : GGIsReflection p φ) (ψ : MulAut ↥Bs) : GGIsReflection p (ψ * φ * ψ⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [conj_pow, h.1, mul_one, mul_inv_cancel]
  · rw [← h.2]
    congr 1
    exact Nat.card_congr
      { toFun := fun b => ⟨ψ⁻¹ b.1, by
          have hb := b.2
          simp only [MulAut.mul_apply] at hb
          have := congrArg (fun c => ψ⁻¹ c) hb
          simpa using this⟩
        invFun := fun b => ⟨ψ b.1, by simp [MulAut.mul_apply, b.2]⟩
        left_inv := fun b => Subtype.ext (by simp)
        right_inv := fun b => Subtype.ext (by simp) }

theorem ggFrameA4Input_of_twoClasses {ι : Type} {M : CoxeterMatrix ι} (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) (i₀ i₁ : ι)
    (hconj : ∀ i, ∃ w : M.Group, w * M.simple i₀ = M.simple i * w ∨
      w * M.simple i₁ = M.simple i * w)
    (hnc : ∀ j, (j = i₀ ∨ j = i₁) → ∃ a b c d : M.Group, (∃ w, w * M.simple j = a * w) ∧
      (∃ w, w * M.simple j = b * w) ∧ (∃ w, w * M.simple j = c * w) ∧
      (∃ w, w * M.simple j = d * w) ∧ a * b * (c * d) ≠ c * d * (a * b)) :
    GGFrameA4Input M := by
  intro G _ _ B Bs x L D J hR hW hAt _ z hzB hz1
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  obtain ⟨y, K, hN, e, he⟩ := hAt
  have hc := hR.1
  have hBsE : IsElemAbelian 3 Bs := hR.1.2.1.2.1
  have hzBs : z ∈ Bs := hc.2.1.1 hzB
  letI : CommGroup ↥Bs :=
    { (inferInstance : Group ↥Bs) with mul_comm := fun a b => hBsE.1.is_comm.comm a b }
  let z' : ↥Bs := ⟨z, hzBs⟩
  have hz'3 : z' ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hBsE.2 z hzBs)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  let S : Subgroup (MulAut ↥Bs) :=
    { carrier := {φ | φ z' ∈ Subgroup.zpowers z' ∧ φ⁻¹ z' ∈ Subgroup.zpowers z'}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, ?_⟩
        · rw [MulAut.mul_apply]; exact map_mem_zpowers ha hb
        · rw [mul_inv_rev, MulAut.mul_apply]; exact map_mem_zpowers hb' ha'
      one_mem' := ⟨Subgroup.mem_zpowers z', Subgroup.mem_zpowers z'⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨ha', by rw [inv_inv]; exact ha⟩ }
  have key : ∀ h : G, ∀ ψ : MulAut ↥Bs, (∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = h * b * h⁻¹) →
      ψ z' ∈ Subgroup.zpowers z' := by
    intro h ψ hψ
    have e1 : ((ψ z' : ↥Bs) : G) = h * z * h⁻¹ := hψ z'
    have hmem : h * z * h⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      rw [Set.mem_singleton_iff.mp hw, ← e1]
      exact congrArg Subtype.val (mul_comm z' (ψ z'))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcon h hmem)
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨k, Subtype.ext (by rw [SubgroupClass.coe_zpow, e1]; exact hk)⟩
  have hgen : ∀ H : Subgroup G, ggInduced H Bs ⊆ S := by
    rintro H φ ⟨g, -, -, hφ⟩
    refine ⟨key g φ hφ, key g⁻¹ φ⁻¹ fun b => ?_⟩
    have h1 := hφ (φ⁻¹ b)
    rw [MulAut.apply_inv_self] at h1
    rw [inv_inv, h1]
    group
  have hAleS : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ S :=
    sup_le ((Subgroup.closure_le _).mpr (hgen L)) ((Subgroup.closure_le _).mpr (hgen K))
  set E : M.Group → MulAut ↥Bs :=
    fun w => ((e w : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) with hEdef
  have hEmul : ∀ a b, E (a * b) = E a * E b := fun a b => by simp [hEdef]
  have hEinv : ∀ a, E a⁻¹ = (E a)⁻¹ := fun a => by simp [hEdef]
  have hAS : ∀ w : M.Group, E w ∈ S := fun w => hAleS (e w).2
  have hconjact : ∀ (w : M.Group) (j : ι), E (w * M.simple j * w⁻¹) z' = E (M.simple j) z' := by
    intro w j
    refine apply_eq_of_conj (ψ := E w) ?_ (hAS w).2 (hAS _).1
    rw [← hEmul, ← hEmul]
    congr 1
    group
  have hrefl : ∀ (w : M.Group) (j : ι), GGIsReflection 3 (E (w * M.simple j * w⁻¹)) := by
    intro w j
    rw [hEmul, hEmul, hEinv]
    exact ggIsReflection_mul_inv (he j) (E w)
  have hsame : ∀ i, E (M.simple i) z' = E (M.simple i₀) z' ∨
      E (M.simple i) z' = E (M.simple i₁) z' := by
    intro i
    obtain ⟨w, hw | hw⟩ := hconj i
    · left
      have : M.simple i = w * M.simple i₀ * w⁻¹ := by rw [hw]; group
      rw [this]
      exact hconjact w i₀
    · right
      have : M.simple i = w * M.simple i₁ * w⁻¹ := by rw [hw]; group
      rw [this]
      exact hconjact w i₁
  by_cases h0 : E (M.simple i₀) z' = z' ∧ E (M.simple i₁) z' = z'
  ·
    have hfixall : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ψ z' = z' := by
      intro ψ hψ
      obtain ⟨w, rfl⟩ : ∃ w, ((e w : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) = ψ :=
        ⟨e.symm ⟨ψ, hψ⟩, by simp⟩
      let T : Subgroup M.Group :=
        (MulAction.stabilizer (MulAut ↥Bs) z').comap
          ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).subtype.comp e.toMonoidHom)
      have hT : (⊤ : Subgroup M.Group) ≤ T := by
        rw [← M.toCoxeterSystem.subgroup_closure_range_simple, Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        simp only [CoxeterMatrix.toCoxeterSystem_simple]
        rw [SetLike.mem_coe, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
        rcases hsame i with h | h
        · exact h.trans h0.1
        · exact h.trans h0.2
      exact hT (Subgroup.mem_top w)
    exact hz'1 (eq_one_of_fix_join hTBF hWI hR hW hN z' hfixall)
  ·
    obtain ⟨j, hj, hjz⟩ : ∃ j, (j = i₀ ∨ j = i₁) ∧ E (M.simple j) z' ≠ z' := by
      by_cases ha : E (M.simple i₀) z' = z'
      · exact ⟨i₁, Or.inr rfl, fun hb => h0 ⟨ha, hb⟩⟩
      · exact ⟨i₀, Or.inl rfl, ha⟩
    have hφ1 : E (M.simple j) z' ≠ 1 :=
      fun h => hz'1 ((map_eq_one_iff _ (MulEquiv.injective _)).mp h)
    have hinv : E (M.simple j) z' = z'⁻¹ := eq_inv_of_mem_zpowers hz'3 (hAS _).1 hφ1 hjz
    have hinvw : ∀ w : M.Group, E (w * M.simple j * w⁻¹) z' = z'⁻¹ :=
      fun w => (hconjact w j).trans hinv
    obtain ⟨a, b, c, d, ⟨w₁, ha⟩, ⟨w₂, hb⟩, ⟨w₃, hc⟩, ⟨w₄, hd⟩, hne⟩ := hnc j hj
    obtain rfl := eq_mul_inv_of_mul_eq ha.symm
    obtain rfl := eq_mul_inv_of_mul_eq hb.symm
    obtain rfl := eq_mul_inv_of_mul_eq hc.symm
    obtain rfl := eq_mul_inv_of_mul_eq hd.symm
    have hu := unip_of_refl hz'3 hz'1 (hrefl w₁ j).2 (hinvw w₁) (hrefl w₂ j).2 (hinvw w₂)
    have hu' := unip_of_refl hz'3 hz'1 (hrefl w₃ j).2 (hinvw w₃) (hrefl w₄ j).2 (hinvw w₄)
    have hcomm := commute_of_unip hu hu'
    apply hne
    apply e.injective
    apply Subtype.ext
    set a := w₁ * M.simple j * w₁⁻¹
    set b := w₂ * M.simple j * w₂⁻¹
    set c := w₃ * M.simple j * w₃⁻¹
    set d := w₄ * M.simple j * w₄⁻¹
    show E (a * b * (c * d)) = E (c * d * (a * b))
    calc E (a * b * (c * d)) = E a * E b * (E c * E d) := by
          rw [hEmul (a * b) (c * d), hEmul a b, hEmul c d]
      _ = E c * E d * (E a * E b) := hcomm
      _ = E (c * d * (a * b)) := by rw [hEmul (c * d) (a * b), hEmul c d, hEmul a b]

theorem ggIntCartan_transpose {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (h : GGIntCartan M C) : GGIntCartan M C.transpose := by
  refine ⟨fun i => by simpa using h.1 i, fun i j hij => ?_⟩
  simp only [Matrix.transpose_apply]
  rcases h.2 i j hij with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, h3, h2⟩
  · exact Or.inr (Or.inl ⟨h1, h3, h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, by rw [mul_comm]; exact h2, h4, h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, by rw [mul_comm]; exact h2, h4, h3⟩))

theorem ggIntCartan_F₄_tag : GGIntCartan CoxeterMatrix.F₄ (Tag.cartan .F4) := by
  have h : Tag.cartan .F4 = CartanMatrix.F₄.transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h]
  exact ggIntCartan_transpose ggIntCartan_F₄

theorem coxeterF4_eq : CoxeterMatrix.F₄ = coxeterMatrix (isFiniteType_cartan .F4) :=
  (coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .F4) ggIntCartan_F₄_tag).symm

@[expose] def iF4 (n : Fin 4) : Fin Tag.F4.rank := n

def cwF4Raw : Fin 4 → List (Fin 4) := ![[], [0, 1], [3, 2], []]

def cwF4 : Fin Tag.F4.rank → List (Fin Tag.F4.rank) := cwF4Raw

def repF4 (i : Fin Tag.F4.rank) : Fin Tag.F4.rank := if i.val < 2 then iF4 0 else iF4 3

theorem cwF4_act : ∀ i k : Fin Tag.F4.rank,
    TableBExc.wordAct .F4 (cwF4 i) (reflect .F4 (repF4 i) (Pi.single k 1)) =
      reflect .F4 i (TableBExc.wordAct .F4 (cwF4 i) (Pi.single k 1)) := by
  decide +kernel

theorem conj_simple_F4 : ∀ i : Fin Tag.F4.rank, ∃ w : WeylGroup .F4,
    w * simple .F4 (iF4 0) = simple .F4 i * w ∨ w * simple .F4 (iF4 3) = simple .F4 i * w := by
  intro i
  have hw : wordW .F4 (cwF4 i) * simple .F4 (repF4 i) = simple .F4 i * wordW .F4 (cwF4 i) :=
    ext_single fun k => by
      simp only [mul_smul, wordW_smul, simple_smul]
      exact cwF4_act i k
  refine ⟨wordW .F4 (cwF4 i), ?_⟩
  unfold repF4 at hw
  split_ifs at hw
  · exact Or.inl hw
  · exact Or.inr hw

def ncF4Raw (j : Fin 2) : Fin 4 → List (Fin 4) :=
  if j = 0 then ![[0], [1], [1], [2, 1, 2]] else ![[3], [2], [2], [1, 2, 1]]

def ncF4Conj (j : Fin 2) : Fin 4 → List (Fin 4) :=
  if j = 0 then ![[], [0, 1], [0, 1], [2, 0, 1]] else ![[], [3, 2], [3, 2], [1, 3, 2]]

def ncF4 (j : Fin 2) (t : Fin 4) : List (Fin Tag.F4.rank) := ncF4Raw j t

def ncF4C (j : Fin 2) (t : Fin 4) : List (Fin Tag.F4.rank) := ncF4Conj j t

@[expose] def jF4 (j : Fin 2) : Fin Tag.F4.rank := if j = 0 then iF4 0 else iF4 3

theorem ncF4_conj_act : ∀ (j : Fin 2) (t : Fin 4) (k : Fin Tag.F4.rank),
    TableBExc.wordAct .F4 (ncF4C j t) (reflect .F4 (jF4 j) (Pi.single k 1)) =
      TableBExc.wordAct .F4 (ncF4 j t) (TableBExc.wordAct .F4 (ncF4C j t) (Pi.single k 1)) := by
  decide +kernel

theorem ncF4_act : ∀ j : Fin 2, ∃ k : Fin Tag.F4.rank,
    TableBExc.wordAct .F4 (ncF4 j 0) (TableBExc.wordAct .F4 (ncF4 j 1)
      (TableBExc.wordAct .F4 (ncF4 j 2) (TableBExc.wordAct .F4 (ncF4 j 3) (Pi.single k 1)))) ≠
    TableBExc.wordAct .F4 (ncF4 j 2) (TableBExc.wordAct .F4 (ncF4 j 3)
      (TableBExc.wordAct .F4 (ncF4 j 0) (TableBExc.wordAct .F4 (ncF4 j 1) (Pi.single k 1)))) := by
  decide +kernel

theorem noncomm_F4 (j : Fin 2) : ∃ a b c d : WeylGroup .F4,
    (∃ w, w * simple .F4 (jF4 j) = a * w) ∧ (∃ w, w * simple .F4 (jF4 j) = b * w) ∧
    (∃ w, w * simple .F4 (jF4 j) = c * w) ∧ (∃ w, w * simple .F4 (jF4 j) = d * w) ∧
    a * b * (c * d) ≠ c * d * (a * b) := by
  have hc : ∀ t : Fin 4, wordW .F4 (ncF4C j t) * simple .F4 (jF4 j) =
      wordW .F4 (ncF4 j t) * wordW .F4 (ncF4C j t) := fun t =>
    ext_single fun k => by
      simp only [mul_smul, wordW_smul, simple_smul]
      exact ncF4_conj_act j t k
  refine ⟨wordW .F4 (ncF4 j 0), wordW .F4 (ncF4 j 1), wordW .F4 (ncF4 j 2), wordW .F4 (ncF4 j 3),
    ⟨_, hc 0⟩, ⟨_, hc 1⟩, ⟨_, hc 2⟩, ⟨_, hc 3⟩, fun h => ?_⟩
  obtain ⟨k, hk⟩ := ncF4_act j
  apply hk
  have h2 := congrArg (· • (Pi.single k 1 : Fin Tag.F4.rank → ℤ)) h
  simp only [mul_smul, wordW_smul] at h2
  exact h2

theorem ggFrameA4Input_F4 (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGFrameA4Input CoxeterMatrix.F₄ := by
  rw [coxeterF4_eq]
  refine ggFrameA4Input_of_twoClasses hTBF hWI (iF4 0) (iF4 3) conj_simple_F4 ?_
  rintro j (rfl | rfl)
  · exact noncomm_F4 0
  · exact noncomm_F4 1

end CFSG.StandardType.FrameRoute

end
