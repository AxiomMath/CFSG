module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6FrameDef
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Sigma
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Chain
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6A2Set
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Decomp
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Form
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6Disc

public section

namespace CFSG.StandardType.TableCRes

open CFSG.StandardType.KGCentE6 (iform_comm_E6 iform_add_left_E6 iform_smul_left_E6
  iform_sub_left_E6 iform_right_neg_E6)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem e6d_mem_left (α β : Fin Tag.E6.rank → ℤ) : α ∈ tcA2Set α β := by
  simp [tcA2Set]

theorem e6d_mem_right (α β : Fin Tag.E6.rank → ℤ) : β ∈ tcA2Set α β := by
  simp [tcA2Set]

theorem e6d_tab12_split : ∀ u ∈ tab12, u ∈ wtTab ∨ u ∈ tcRootTab := by
  decide

theorem e6d_wtTab_rep : ∀ u ∈ wtTab, ∃ u₀ ∈ wtRep, u = u₀ ∨ u = (-u₀.1, -u₀.2) := by
  decide

theorem e6d_pm_iff (w x y : ℤ × ℤ) (hy : y = w ∨ y = (-w.1, -w.2)) :
    (x = w ∨ x = (-w.1, -w.2)) ↔ (x = y ∨ x = (-y.1, -y.2)) := by
  rcases hy with rfl | rfl
  · exact Iff.rfl
  · obtain ⟨a, b⟩ := w
    obtain ⟨c, d⟩ := x
    simp only [Prod.mk.injEq, neg_neg]
    tauto

theorem e6d_pm_dvd {p s t : ℤ} {x y : ℤ × ℤ} (h : x = y ∨ x = (-y.1, -y.2))
    (hy : p ∣ s * y.1 + t * y.2) : p ∣ s * x.1 + t * x.2 := by
  rcases h with rfl | rfl
  · exact hy
  · have e : s * (-y.1) + t * (-y.2) = -(s * y.1 + t * y.2) := by ring
    show p ∣ s * (-y.1) + t * (-y.2)
    rw [e]
    exact dvd_neg.2 hy

theorem e6d_chainVec_five (c : List ℤ) (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) :
    tcChainVec c δ = c.getD 0 0 • δ 0 + c.getD 1 0 • δ 1 + c.getD 2 0 • δ 2 +
      c.getD 3 0 • δ 3 + c.getD 4 0 • δ 4 := by
  unfold tcChainVec
  rw [Fin.sum_univ_five]
  rfl

theorem e6d_chainVec_list (c0 c1 c2 c3 c4 : ℤ) (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) :
    tcChainVec [c0, c1, c2, c3, c4] δ = c0 • δ 0 + c1 • δ 1 + c2 • δ 2 + c3 • δ 3 + c4 • δ 4 := by
  rw [e6d_chainVec_five]
  rfl

theorem e6d_iform_chainVec (c : List ℤ) (δ : Fin 5 → (Fin Tag.E6.rank → ℤ))
    (x : Fin Tag.E6.rank → ℤ) :
    iform (tcChainVec c δ) x = c.getD 0 0 * iform (δ 0) x + c.getD 1 0 * iform (δ 1) x +
      c.getD 2 0 * iform (δ 2) x + c.getD 3 0 * iform (δ 3) x + c.getD 4 0 * iform (δ 4) x := by
  rw [e6d_chainVec_five]
  simp only [iform_add_left_E6, iform_smul_left_E6]

theorem e6d_std30_fneg : ∀ c ∈ std30, c.getD 2 0 = -1 → c ∈ stdFneg := by
  decide

theorem e6d_two_mem (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) : δ 2 ∈ tcChainSet δ := by
  show ∃ c ∈ std30, δ 2 = tcChainVec c δ
  refine ⟨intv 2 3, by decide, ?_⟩
  rw [show intv 2 3 = [0, 0, 1, 0, 0] by decide, e6d_chainVec_list]
  simp

theorem e6d_mem_X1 (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) :
    ∀ x ∈ tcA2Set (δ 0) (δ 1), ∃ c ∈ stdX1, x = tcChainVec c δ := by
  intro x hx
  simp only [tcA2Set, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨intv 0 1, by decide, ?_⟩
    rw [show intv 0 1 = [1, 0, 0, 0, 0] by decide, e6d_chainVec_list]
    simp
  · refine ⟨intv 1 2, by decide, ?_⟩
    rw [show intv 1 2 = [0, 1, 0, 0, 0] by decide, e6d_chainVec_list]
    simp
  · refine ⟨intv 0 2, by decide, ?_⟩
    rw [show intv 0 2 = [1, 1, 0, 0, 0] by decide, e6d_chainVec_list]
    simp
  · refine ⟨tcNegS (intv 0 1), by decide, ?_⟩
    rw [show tcNegS (intv 0 1) = [-1, 0, 0, 0, 0] by decide, e6d_chainVec_list]
    simp
  · refine ⟨tcNegS (intv 1 2), by decide, ?_⟩
    rw [show tcNegS (intv 1 2) = [0, -1, 0, 0, 0] by decide, e6d_chainVec_list]
    simp
  · refine ⟨tcNegS (intv 0 2), by decide, ?_⟩
    rw [show tcNegS (intv 0 2) = [-1, -1, 0, 0, 0] by decide, e6d_chainVec_list]
    simp only [zero_smul, neg_smul, one_smul, zero_add, add_zero]
    abel

theorem e6d_mem_X2 (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) :
    ∀ x ∈ tcA2Set (δ 3) (δ 4), ∃ c ∈ stdX2, x = tcChainVec c δ := by
  intro x hx
  simp only [tcA2Set, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨intv 3 4, by decide, ?_⟩
    rw [show intv 3 4 = [0, 0, 0, 1, 0] by decide, e6d_chainVec_list]
    simp
  · refine ⟨intv 4 5, by decide, ?_⟩
    rw [show intv 4 5 = [0, 0, 0, 0, 1] by decide, e6d_chainVec_list]
    simp
  · refine ⟨intv 3 5, by decide, ?_⟩
    rw [show intv 3 5 = [0, 0, 0, 1, 1] by decide, e6d_chainVec_list]
    simp
  · refine ⟨tcNegS (intv 3 4), by decide, ?_⟩
    rw [show tcNegS (intv 3 4) = [0, 0, 0, -1, 0] by decide, e6d_chainVec_list]
    simp
  · refine ⟨tcNegS (intv 4 5), by decide, ?_⟩
    rw [show tcNegS (intv 4 5) = [0, 0, 0, 0, -1] by decide, e6d_chainVec_list]
    simp
  · refine ⟨tcNegS (intv 3 5), by decide, ?_⟩
    rw [show tcNegS (intv 3 5) = [0, 0, 0, -1, -1] by decide, e6d_chainVec_list]
    simp only [zero_smul, neg_smul, one_smul, zero_add, add_zero]
    abel

theorem e6d_orth_blocks {V : Type*} (R : V → V → Prop) (hsymm : ∀ x y, R x y → R y x)
    (G : Fin 6 → V)
    (h02 : R (G 0) (G 2)) (h03 : R (G 0) (G 3)) (h04 : R (G 0) (G 4)) (h05 : R (G 0) (G 5))
    (h12 : R (G 1) (G 2)) (h13 : R (G 1) (G 3)) (h14 : R (G 1) (G 4)) (h15 : R (G 1) (G 5))
    (h24 : R (G 2) (G 4)) (h25 : R (G 2) (G 5)) (h34 : R (G 3) (G 4)) (h35 : R (G 3) (G 5)) :
    ∀ i j : Fin 6, i.val / 2 ≠ j.val / 2 → R (G i) (G j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd (by decide) hij
    | assumption
    | exact hsymm _ _ (by assumption)

theorem line_dichotomy {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {α₁ β₁ α₂ β₂ α₃ β₃ : Fin Tag.E6.rank → ℤ}
    (r1 : IsRoot .E6 α₁) (r2 : IsRoot .E6 β₁) (r3 : IsRoot .E6 α₂) (r4 : IsRoot .E6 β₂)
    (a1 : iform α₁ β₁ = -1) (a2 : iform α₂ β₂ = -1)
    (o1 : iform α₁ α₂ = 0) (o2 : iform α₁ β₂ = 0) (o3 : iform β₁ α₂ = 0) (o4 : iform β₁ β₂ = 0)
    (fr : E6Frame α₁ β₁ α₂ β₂ α₃ β₃) (v : Fin Tag.E6.rank → ℤ)
    (hvan : ∀ γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂, (p : ℤ) ∣ ∑ j, γ j * v j)
    (hne : ¬ ∀ j, (p : ℤ) ∣ v j) :
    (∀ γ, IsRoot .E6 γ → (p : ℤ) ∣ (∑ j, γ j * v j) →
        γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ∨ ∀ m ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂, iform γ m = 0) ∨
    (∃ u₀ ∈ wtRep, ∀ γ, IsRoot .E6 γ → ((p : ℤ) ∣ (∑ j, γ j * v j) ↔
        (γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ∨
          (γ ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ∧
            ((iform γ α₃, iform γ β₃) = u₀ ∨ (iform γ α₃, iform γ β₃) = (-u₀.1, -u₀.2)))))) := by
  set m : Fin 6 → (Fin Tag.E6.rank → ℤ) := ![α₁, β₁, α₂, β₂, α₃, β₃]
  have hn : ∀ i, iform (m i) (m i) = 2 := by
    intro i
    fin_cases i
    · exact e6_iform_self _ (mem_rootFinset.2 r1)
    · exact e6_iform_self _ (mem_rootFinset.2 r2)
    · exact e6_iform_self _ (mem_rootFinset.2 r3)
    · exact e6_iform_self _ (mem_rootFinset.2 r4)
    · exact e6_iform_self _ (mem_rootFinset.2 fr.root₃)
    · exact e6_iform_self _ (mem_rootFinset.2 fr.root₃')
  obtain ⟨e1, e2, e3, e4⟩ := fr.orth₁
  obtain ⟨f1, f2, f3, f4⟩ := fr.orth₂
  have horth : ∀ i j : Fin 6, i.val / 2 ≠ j.val / 2 → iform (m i) (m j) = 0 :=
    e6d_orth_blocks (fun x y => iform x y = 0)
      (fun x y (h : iform x y = 0) => (iform_comm_E6 y x).trans h) m
      o1 o2 e1 e2 o3 o4 e3 e4 f1 f2 f3 f4
  have mA : α₁ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ := Set.mem_union_left _ (e6d_mem_left _ _)
  have mB : β₁ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ := Set.mem_union_left _ (e6d_mem_right _ _)
  have mC : α₂ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ := Set.mem_union_right _ (e6d_mem_left _ _)
  have mD : β₂ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ := Set.mem_union_right _ (e6d_mem_right _ _)
  obtain ⟨s, t, hdec⟩ := pair_decomp_of_frame hp hp5 m hn a1 a2 fr.ip₃ horth v
    (hvan _ mA) (hvan _ mB) (hvan _ mC) (hvan _ mD)
  have hdec' : ∀ γ : Fin Tag.E6.rank → ℤ,
      (p : ℤ) ∣ (∑ j, γ j * v j) - (s * iform γ α₃ + t * iform γ β₃) := hdec
  have key : ∀ γ : Fin Tag.E6.rank → ℤ,
      (p : ℤ) ∣ (∑ j, γ j * v j) ↔ (p : ℤ) ∣ s * iform γ α₃ + t * iform γ β₃ := by
    intro γ
    constructor
    · intro hd
      have h := dvd_sub hd (hdec' γ)
      rwa [sub_sub_cancel] at h
    · intro hd
      have h := dvd_add (hdec' γ) hd
      rwa [sub_add_cancel] at h
  have hnd : ¬ ((p : ℤ) ∣ s ∧ (p : ℤ) ∣ t) := by
    rintro ⟨hs, ht⟩
    apply hne
    intro j
    have hV : (p : ℤ) ∣ s * iform (Pi.single j 1) α₃ + t * iform (Pi.single j 1) β₃ :=
      dvd_add (dvd_mul_of_dvd_left hs _) (dvd_mul_of_dvd_left ht _)
    have hS := (key (Pi.single j 1)).2 hV
    simpa [Pi.single_apply] using hS
  by_cases hw : ∃ γ₁, IsRoot .E6 γ₁ ∧ γ₁ ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ∧
      (p : ℤ) ∣ (∑ j, γ₁ j * v j) ∧ (iform γ₁ α₃, iform γ₁ β₃) ∈ wtTab
  · right
    obtain ⟨γ₁, hγ₁, hnX₁, hdvd₁, hwt₁⟩ := hw
    obtain ⟨u₀, hu₀, hu₀'⟩ := e6d_wtTab_rep _ hwt₁
    refine ⟨u₀, hu₀, fun γ hγ => ?_⟩
    have hv₁ : (p : ℤ) ∣ s * iform γ₁ α₃ + t * iform γ₁ β₃ := (key γ₁).1 hdvd₁
    constructor
    · intro hdvd
      by_cases hX : γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂
      · exact Or.inl hX
      · refine Or.inr ⟨hX, ?_⟩
        have h' : (p : ℤ) ∣ s * iform γ α₃ + t * iform γ β₃ := (key γ).1 hdvd
        have hcl := line_class_arith hp hp5 hnd (fr.tab γ₁ hγ₁ hnX₁) (fr.tab γ hγ hX) hv₁ h'
        exact (e6d_pm_iff u₀ _ _ hu₀').2 hcl
    · rintro (hX | ⟨hX, hline⟩)
      · exact hvan γ hX
      · apply (key γ).2
        have hline' := (e6d_pm_iff u₀ _ _ hu₀').1 hline
        exact e6d_pm_dvd hline' hv₁
  · left
    intro γ hγ hdvd
    by_cases hX : γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂
    · exact Or.inl hX
    · right
      have hrt := (e6d_tab12_split _ (fr.tab γ hγ hX)).resolve_left
        (fun hwt => hw ⟨γ, hγ, hX, hdvd, hwt⟩)
      exact fr.rootT γ hγ hX hrt

theorem rho_image_X₂ {α₁ β₁ α₂ β₂ : Fin Tag.E6.rank → ℤ}
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hdisj : Disjoint (tcA2Set α₁ β₁) (tcA2Set α₂ β₂))
    (hX : Set.Finite (tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂))
    (h12 : (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcA2Set α₁ β₁ = tcA2Set α₂ β₂)
    (hst : ∀ γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂, ρ γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂) :
    (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcA2Set α₂ β₂ = tcA2Set α₁ β₁ := by
  haveI : Finite ↥(tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂) := hX.to_subtype
  let f : ↥(tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂) → ↥(tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂) :=
    fun x => ⟨ρ x, hst x x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact ρ.injective (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hf
  have hZ : ∀ y ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂, ∃ z ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂, ρ z = y := by
    intro y hy
    obtain ⟨⟨z, hz⟩, hzy⟩ := hsurj ⟨y, hy⟩
    exact ⟨z, hz, congrArg Subtype.val hzy⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hst z (Set.mem_union_right _ hz) with h | h
    · exact h
    · exfalso
      rw [← h12] at h
      obtain ⟨w, hw, hwz⟩ := h
      have hwz' : w = z := ρ.injective hwz
      subst hwz'
      exact Set.disjoint_left.1 hdisj hw hz
  · intro hy
    obtain ⟨z, hz, hzy⟩ := hZ y (Set.mem_union_left _ hy)
    rcases hz with hz1 | hz2
    · exfalso
      have hρz : ρ z ∈ tcA2Set α₂ β₂ := by
        rw [← h12]
        exact ⟨z, hz1, rfl⟩
      rw [hzy] at hρz
      exact Set.disjoint_left.1 hdisj hy hρz
    · exact ⟨z, hz2, hzy⟩

theorem a5Swap_of_frame
    {α₁ β₁ α₂ β₂ α₃ β₃ : Fin Tag.E6.rank → ℤ} (fr : E6Frame α₁ β₁ α₂ β₂ α₃ β₃)
    (r1 : IsRoot .E6 α₁) (r2 : IsRoot .E6 β₁) (a1 : iform α₁ β₁ = -1)
    (r3 : IsRoot .E6 α₂) (r4 : IsRoot .E6 β₂) (a2 : iform α₂ β₂ = -1)
    {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)} (hδ : A5Chain δ)
    (h0 : δ 0 ∈ tcA2Set α₁ β₁) (h1 : δ 1 ∈ tcA2Set α₁ β₁) (h3 : δ 3 ∈ tcA2Set α₂ β₂)
    (h4 : δ 4 ∈ tcA2Set α₂ β₂) (h2 : δ 2 ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρ1 : (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcA2Set α₁ β₁ = tcA2Set α₂ β₂)
    (hρ2 : (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcA2Set α₂ β₂ = tcA2Set α₁ β₁)
    (hu : ∀ γ, IsRoot .E6 γ → iform (ρ γ) α₃ = - iform γ α₃ ∧ iform (ρ γ) β₃ = - iform γ β₃)
    (hst : ∀ γ ∈ tcChainSet δ, ρ γ ∈ tcChainSet δ) :
    A5Swap (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) δ := by
  have g01 : iform (δ 0) (δ 1) = -1 := by
    rw [hδ.gram 0 1]
    decide
  have g34 : iform (δ 3) (δ 4) = -1 := by
    rw [hδ.gram 3 4]
    decide
  have hX1 : tcA2Set (δ 0) (δ 1) = tcA2Set α₁ β₁ := a2Set_eq_of_mem r1 r2 a1 h0 h1 g01
  have hX2 : tcA2Set (δ 3) (δ 4) = tcA2Set α₂ β₂ := a2Set_eq_of_mem r3 r4 a2 h3 h4 g34
  have z0 : iform (δ 0) α₃ = 0 ∧ iform (δ 0) β₃ = 0 :=
    (fr.mem (δ 0) (hδ.root 0)).1 (Set.mem_union_left _ h0)
  have z1 : iform (δ 1) α₃ = 0 ∧ iform (δ 1) β₃ = 0 :=
    (fr.mem (δ 1) (hδ.root 1)).1 (Set.mem_union_left _ h1)
  have z3 : iform (δ 3) α₃ = 0 ∧ iform (δ 3) β₃ = 0 :=
    (fr.mem (δ 3) (hδ.root 3)).1 (Set.mem_union_right _ h3)
  have z4 : iform (δ 4) α₃ = 0 ∧ iform (δ 4) β₃ = 0 :=
    (fr.mem (δ 4) (hδ.root 4)).1 (Set.mem_union_right _ h4)
  have nz2 : ¬ (iform (δ 2) α₃ = 0 ∧ iform (δ 2) β₃ = 0) :=
    fun h => h2 ((fr.mem (δ 2) (hδ.root 2)).2 h)
  have hX1mem : ∀ x ∈ tcA2Set α₁ β₁, ∃ c ∈ stdX1, x = tcChainVec c δ := by
    intro x hx
    rw [← hX1] at hx
    exact e6d_mem_X1 δ x hx
  have hX2mem : ∀ x ∈ tcA2Set α₂ β₂, ∃ c ∈ stdX2, x = tcChainVec c δ := by
    intro x hx
    rw [← hX2] at hx
    exact e6d_mem_X2 δ x hx
  have hs0 : ρ (δ 0) ∈ tcA2Set α₂ β₂ := by
    rw [← hρ1]
    exact ⟨δ 0, h0, rfl⟩
  have hs1 : ρ (δ 1) ∈ tcA2Set α₂ β₂ := by
    rw [← hρ1]
    exact ⟨δ 1, h1, rfl⟩
  have hs3 : ρ (δ 3) ∈ tcA2Set α₁ β₁ := by
    rw [← hρ2]
    exact ⟨δ 3, h3, rfl⟩
  have hs4 : ρ (δ 4) ∈ tcA2Set α₁ β₁ := by
    rw [← hρ2]
    exact ⟨δ 4, h4, rfl⟩
  obtain ⟨c, hc30, hcρ⟩ : ∃ c ∈ std30, ρ (δ 2) = tcChainVec c δ :=
    hst (δ 2) (e6d_two_mem δ)
  have hk : c.getD 2 0 = -1 := by
    have ha : c.getD 2 0 * iform (δ 2) α₃ = -iform (δ 2) α₃ := by
      have h := (hu (δ 2) (hδ.root 2)).1
      rw [hcρ, e6d_iform_chainVec, z0.1, z1.1, z3.1, z4.1] at h
      linear_combination h
    have hb : c.getD 2 0 * iform (δ 2) β₃ = -iform (δ 2) β₃ := by
      have h := (hu (δ 2) (hδ.root 2)).2
      rw [hcρ, e6d_iform_chainVec, z0.2, z1.2, z3.2, z4.2] at h
      linear_combination h
    by_contra hne
    have hne' : c.getD 2 0 + 1 ≠ 0 := fun h => hne (by linarith)
    have hk1 : (c.getD 2 0 + 1) * iform (δ 2) α₃ = 0 := by linear_combination ha
    have hk2 : (c.getD 2 0 + 1) * iform (δ 2) β₃ = 0 := by linear_combination hb
    exact nz2 ⟨(mul_eq_zero.1 hk1).resolve_left hne', (mul_eq_zero.1 hk2).resolve_left hne'⟩
  have hcFneg : c ∈ stdFneg := e6d_std30_fneg c hc30 hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨c0, hc0, hce0⟩ := hX2mem _ hs0
    exact ⟨c0, hc0, hce0⟩
  · obtain ⟨c1, hc1, hce1⟩ := hX2mem _ hs1
    exact ⟨c1, hc1, hce1⟩
  · exact ⟨c, hcFneg, hcρ⟩
  · obtain ⟨c3, hc3, hce3⟩ := hX1mem _ hs3
    exact ⟨c3, hc3, hce3⟩
  · obtain ⟨c4, hc4, hce4⟩ := hX1mem _ hs4
    exact ⟨c4, hc4, hce4⟩

end CFSG.StandardType.TableCRes

end
