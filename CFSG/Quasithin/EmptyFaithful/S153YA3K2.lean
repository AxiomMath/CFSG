module

public import CFSG.Quasithin.EmptyFaithful.S153YA3Baum
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDK1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCFin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDBasis

public section

namespace CFSG.Quasithin.YG.AppD

open CFSG.QuasithinUnique.AppD
open CFSG.QuasithinUnique.DoubleA3
open CFSG.Quasithin.YG.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
open CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.AppC (t1_mem_Eset t2_mem_Eset)

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G} {s : G}

omit [Finite G] in
theorem mem_normalizer_conj_of {A : Subgroup G} {g b : G}
    (h : g * b * g⁻¹ ∈ Subgroup.normalizer (A : Set G)) :
    b ∈ Subgroup.normalizer ((conjSubgroup A g : Subgroup G) : Set G) := by
  rw [← C5.conjSubgroup_normalizer, mem_conjSubgroup_iff]
  exact h

section Fin

theorem mem_Dset_of_part : ∀ σ : Perm (Fin 5), σ 4 = 4 →
    (((σ 0 = 0 ∨ σ 0 = 1) ∧ (σ 1 = 0 ∨ σ 1 = 1)) ∨
      ((σ 0 = 2 ∨ σ 0 = 3) ∧ (σ 1 = 2 ∨ σ 1 = 3))) → σ ∈ Dset := by
  decide +kernel

theorem mem_Eset_of_part : ∀ σ : Perm (Fin 5), σ 4 = 4 → (σ 0 = 0 ∨ σ 0 = 1) →
    (σ 1 = 0 ∨ σ 1 = 1) → (σ 2 = 2 ∨ σ 2 = 3) → (σ 3 = 2 ∨ σ 3 = 3) → σ ∈ Eset := by
  decide +kernel

theorem Eset_zero : ∀ σ ∈ Eset, σ 0 = 0 ∨ σ 0 = 1 := by decide +kernel

theorem Dset_cosets : ∀ σ ∈ Dset, σ ∉ Eset → ∀ τ ∈ Dset, τ ∈ Eset ∨ τ * σ⁻¹ ∈ Eset := by
  decide +kernel

theorem eq_swap01 : ∀ σ : Perm (Fin 5), σ 0 = 1 → σ 1 = 0 → σ 2 = 2 → σ 3 = 3 → σ 4 = 4 →
    σ = swap 0 1 := by
  decide +kernel

theorem eq_swap23 : ∀ σ : Perm (Fin 5), σ 0 = 0 → σ 1 = 1 → σ 2 = 3 → σ 3 = 2 → σ 4 = 4 →
    σ = swap 2 3 := by
  decide +kernel

end Fin

omit [Finite G] in
theorem conj_mem_of_conjR {X Y : Subgroup G} {g : G} (hXY : conjR X g⁻¹ = Y) {u : G}
    (hu : u ∈ X) : g * u * g⁻¹ ∈ Y := by
  rw [← hXY, C56.conjR_eq, mem_conjSubgroup_iff]
  have e : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
  rw [e]
  exact hu

theorem baum_le_S' {G : Type} [Group G] (S : Subgroup G) : baum S ≤ S := inf_le_left

theorem conjSubgroup_baum {G : Type} [Group G] {S : Subgroup G} {g : G} (hg : g ∈ S) :
    conjSubgroup (baum S) g = baum S :=
  C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum S (Subgroup.le_normalizer hg))

namespace A3x

variable (h : A3A3 H S L s)
include h

theorem hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L) := C56.blockU0_eq_pCoreOf h

theorem hUeq : blockU0 S L = blockU L ⊔ blockU2 L s := h.blockU0_eq (hU0 h)

theorem B_pgroup : IsPGroup 2 ↥(baum S) := h.cs.sylow.isPGroup.to_le (baum_le_S' S)

theorem U₁_le_B : blockU L ≤ baum S := (C56.baumann_double_A3 h.cs h.a3 h.conjJoin_ne).1

theorem B_le_N_L : baum S ≤ Subgroup.normalizer (L : Set G) :=
  (C56.baumann_double_A3 h.cs h.a3 h.conjJoin_ne).2.1

theorem U₂_le_B : blockU2 L s ≤ baum S := by
  have := C5.conjSubgroup_mono (U₁_le_B h) s
  rwa [conjSubgroup_baum h.s_mem] at this

theorem B_le_N_U₁ : baum S ≤ Subgroup.normalizer (blockU L : Set G) := fun _ hb =>
  C1.mem_normalizer_blockU (B_le_N_L h hb)

theorem B_le_N_U₂ : baum S ≤ Subgroup.normalizer (blockU2 L s : Set G) := by
  intro b hb
  refine mem_normalizer_conj_of ?_
  have hsb : s * b * s⁻¹ ∈ baum S := by
    have hs : s ∈ Subgroup.normalizer (baum S : Set G) :=
      normalizer_le_normalizer_baum S (Subgroup.le_normalizer h.s_mem)
    exact (Subgroup.mem_normalizer_iff.1 hs b).1 hb
  exact B_le_N_U₁ h hsb

theorem not_B_le_C₁ : ¬ baum S ≤ Subgroup.centralizer (blockU L : Set G) := fun hle =>
  C56.a3_not_le_centralizer h.isShort h.a3 h.cs.thompson
    ((C5.thompsonJ_le_baum' S).trans hle)

theorem not_B_le_C₂ : ¬ baum S ≤ Subgroup.centralizer (blockU2 L s : Set G) := by
  intro hle
  apply not_B_le_C₁ h
  have h1 := C5.conjSubgroup_mono hle s⁻¹
  rw [conjSubgroup_baum (S.inv_mem h.s_mem)] at h1
  have e : conjSubgroup (Subgroup.centralizer (blockU2 L s : Set G)) s⁻¹ =
      Subgroup.centralizer (blockU L : Set G) := by
    rw [C5.conjSubgroup_centralizer]
    congr 2
    show conjSubgroup (conjSubgroup (blockU L) s) s⁻¹ = blockU L
    exact C5.conjSubgroup_conjSubgroup_inv _ _
  rwa [e] at h1

structure Spec (h : A3A3 H S L s) where
  z₁ : G
  z₂ : G
  y₁ : G
  y₂ : G
  kp : KPair (blockU L) (blockU2 L s) z₁ y₁ z₂ y₂
  idx₁ : (baum S ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex (baum S) = 2
  idx₂ : (baum S ⊓ Subgroup.centralizer (blockU2 L s : Set G)).relIndex (baum S) = 2
  cent₁ : ∀ y ∈ baum S, y ∉ Subgroup.centralizer (blockU L : Set G) →
    ∀ u ∈ blockU L, (u ∈ Subgroup.zpowers z₁ ↔ u * y = y * u)
  cent₂ : ∀ y ∈ baum S, y ∉ Subgroup.centralizer (blockU2 L s : Set G) →
    ∀ u ∈ blockU2 L s, (u ∈ Subgroup.zpowers z₂ ↔ u * y = y * u)
  zC₁ : blockU L ⊓ Subgroup.centralizer (baum S : Set G) = Subgroup.zpowers z₁
  zC₂ : blockU2 L s ⊓ Subgroup.centralizer (baum S : Set G) = Subgroup.zpowers z₂

omit h in
theorem exists_not_mem_zpowers {V : Subgroup G} {z : G} (hV : Nat.card V = 4)
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) : ∃ y ∈ V, y ∉ Subgroup.zpowers z := by
  by_contra hcon
  push Not at hcon
  have hle : V ≤ Subgroup.zpowers z := fun u hu => hcon u hu
  have h1 := Subgroup.card_le_of_le hle
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  rw [Nat.card_zpowers, hord, hV] at h1
  omega

theorem exists_spec : Nonempty (Spec h) := by
  have hA := h.isA4
  have hAs := h.isA4s
  obtain ⟨z₁, hz₁U, hz₁1, hidx₁, hzC₁, -, hcent₁⟩ := klein_structure hA.card_U hA.sq_U
    (U₁_le_B h) (B_le_N_U₁ h) (B_pgroup h) (not_B_le_C₁ h)
  obtain ⟨z₂, hz₂U, hz₂1, hidx₂, hzC₂, -, hcent₂⟩ := klein_structure hAs.card_U hAs.sq_U
    (U₂_le_B h) (B_le_N_U₂ h) (B_pgroup h) (not_B_le_C₂ h)
  obtain ⟨y₁, hy₁U, hy₁⟩ := exists_not_mem_zpowers hA.card_U hz₁1 (hA.sq_U z₁ hz₁U)
  obtain ⟨y₂, hy₂U, hy₂⟩ := exists_not_mem_zpowers hAs.card_U hz₂1 (hAs.sq_U z₂ hz₂U)
  refine ⟨⟨z₁, z₂, y₁, y₂, ⟨hA.card_U, hAs.card_U, hA.sq_U, hAs.sq_U,
    fun a ha b hb => h.comm_elem a (hA.le ha) b (hAs.le hb),
    le_bot_iff.mp ((inf_le_inf hA.le hAs.le).trans (le_of_eq h.inf_Ls)), hz₁U, hz₂U, hy₁U, hy₂U,
    hz₁1, hz₂1, hy₁, hy₂⟩, hidx₁, hidx₂, hcent₁, hcent₂, hzC₁, hzC₂⟩⟩

theorem U₁_ne_U₂ : blockU L ≠ blockU2 L s := by
  intro heq
  have h1 : blockU L ≤ L ⊓ conjR L s := le_inf h.isA4.le (heq ▸ h.isA4s.le)
  rw [h.inf_Ls, le_bot_iff] at h1
  have := h.isA4.card_U
  rw [h1, Subgroup.card_bot] at this
  omega

theorem conj_swap_cases {g : G} (hg : g ∈ S) :
    (conjR (blockU L) g⁻¹ = blockU L ∧ conjR (blockU2 L s) g⁻¹ = blockU2 L s) ∨
      (conjR (blockU L) g⁻¹ = blockU2 L s ∧ conjR (blockU2 L s) g⁻¹ = blockU L) := by
  have hg' : g⁻¹ ∈ S := S.inv_mem hg
  have hsg : s * g⁻¹ ∈ S := S.mul_mem h.s_mem hg'
  have c1 := h.conj_cases (hU0 h) hg'
  have c2 := h.conj_cases (hU0 h) hsg
  have e : conjR (blockU2 L s) g⁻¹ = conjR (blockU L) (s * g⁻¹) :=
    conjSubgroup_conjSubgroup (blockU L) s g⁻¹
  have hinj : conjR (blockU L) g⁻¹ ≠ conjR (blockU2 L s) g⁻¹ := by
    intro heq
    apply U₁_ne_U₂ h
    have this : conjR (conjR (blockU L) g⁻¹) g = conjR (conjR (blockU2 L s) g⁻¹) g := by rw [heq]
    have e1 : conjR (conjR (blockU L) g⁻¹) g = blockU L := C5.conjSubgroup_inv_conjSubgroup _ _
    have e2 : conjR (conjR (blockU2 L s) g⁻¹) g = blockU2 L s :=
      C5.conjSubgroup_inv_conjSubgroup _ _
    rw [e1, e2] at this
    exact this
  rcases c1 with ⟨a1, -⟩ | ⟨a1, -⟩ <;> rcases c2 with ⟨a2, -⟩ | ⟨a2, -⟩
  · exact absurd (a1.trans (a2.symm.trans e.symm)) hinj
  · exact Or.inl ⟨a1, by rw [e, a2]⟩
  · exact Or.inr ⟨a1, by rw [e, a2]⟩
  · exact absurd (a1.trans (a2.symm.trans e.symm)) hinj

variable {h}

section Action

variable (sp : Spec h)

@[expose] def lab : Fin 5 → G := klabel sp.y₁ sp.z₁ sp.y₂ sp.z₂

theorem lab_four : lab sp 4 = 1 := rfl

theorem lab_inj : Function.Injective (lab sp) := sp.kp.lab_inj

theorem mem_U₁_lab {j : Fin 5} (hj : lab sp j ∈ blockU L) : j = 0 ∨ j = 1 ∨ j = 4 := by
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd (sp.kp.cross hj sp.kp.hy₂ rfl) sp.kp.y₂_ne_one
  · exact absurd (sp.kp.cross hj sp.kp.y₂z₂_mem rfl) sp.kp.y₂z₂_ne_one
  · exact Or.inr (Or.inr rfl)

theorem mem_U₂_lab {j : Fin 5} (hj : lab sp j ∈ blockU2 L s) : j = 2 ∨ j = 3 ∨ j = 4 := by
  fin_cases j
  · exact absurd (sp.kp.cross sp.kp.hy₁ hj rfl) sp.kp.y₁_ne_one
  · exact absurd (sp.kp.cross sp.kp.y₁z₁_mem hj rfl) sp.kp.y₁z₁_ne_one
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem lab_not_central {i : Fin 5} (hi : i ≠ 4) :
    lab sp i ∉ Subgroup.centralizer (baum S : Set G) := by
  intro hc
  fin_cases i
  · have : sp.y₁ ∈ blockU L ⊓ Subgroup.centralizer (baum S : Set G) := ⟨sp.kp.hy₁, hc⟩
    rw [sp.zC₁] at this
    exact sp.kp.y₁_nmem this
  · have h1 : sp.y₁ * sp.z₁ ∈ blockU L ⊓ Subgroup.centralizer (baum S : Set G) :=
      ⟨sp.kp.y₁z₁_mem, hc⟩
    rw [sp.zC₁] at h1
    apply sp.kp.y₁_nmem
    have := mul_mem h1 (inv_mem (Subgroup.mem_zpowers sp.z₁))
    simpa using this
  · have : sp.y₂ ∈ blockU2 L s ⊓ Subgroup.centralizer (baum S : Set G) := ⟨sp.kp.hy₂, hc⟩
    rw [sp.zC₂] at this
    exact sp.kp.y₂_nmem this
  · have h1 : sp.y₂ * sp.z₂ ∈ blockU2 L s ⊓ Subgroup.centralizer (baum S : Set G) :=
      ⟨sp.kp.y₂z₂_mem, hc⟩
    rw [sp.zC₂] at h1
    apply sp.kp.y₂_nmem
    have := mul_mem h1 (inv_mem (Subgroup.mem_zpowers sp.z₂))
    simpa using this
  · exact absurd rfl hi

theorem exists_lab_of_mem {v : G} (hv : v ∈ blockU L ∨ v ∈ blockU2 L s)
    (hvc : v ∉ Subgroup.centralizer (baum S : Set G)) : ∃ j : Fin 5, j ≠ 4 ∧ v = lab sp j := by
  have hz₁C : sp.z₁ ∈ Subgroup.centralizer (baum S : Set G) := by
    have : sp.z₁ ∈ blockU L ⊓ Subgroup.centralizer (baum S : Set G) := by
      rw [sp.zC₁]; exact Subgroup.mem_zpowers _
    exact this.2
  have hz₂C : sp.z₂ ∈ Subgroup.centralizer (baum S : Set G) := by
    have : sp.z₂ ∈ blockU2 L s ⊓ Subgroup.centralizer (baum S : Set G) := by
      rw [sp.zC₂]; exact Subgroup.mem_zpowers _
    exact this.2
  rcases hv with hv | hv
  · rcases sp.kp.elems₁ v hv with rfl | rfl | rfl | rfl
    · exact absurd (one_mem _) hvc
    · exact absurd hz₁C hvc
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
  · rcases sp.kp.elems₂ v hv with rfl | rfl | rfl | rfl
    · exact absurd (one_mem _) hvc
    · exact absurd hz₂C hvc
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨3, by decide, rfl⟩

theorem stab (sp : Spec h) {g : G} (hg : g ∈ S) (i : Fin 5) :
    ∃ j, g * lab sp i * g⁻¹ = lab sp j := by
  by_cases hi : i = 4
  · subst hi
    exact ⟨4, by simp [lab_four]⟩
  · have hmem : lab sp i ∈ blockU L ∨ lab sp i ∈ blockU2 L s := by
      fin_cases i
      · exact Or.inl sp.kp.hy₁
      · exact Or.inl sp.kp.y₁z₁_mem
      · exact Or.inr sp.kp.hy₂
      · exact Or.inr sp.kp.y₂z₂_mem
      · exact absurd rfl hi
    have hmem' : g * lab sp i * g⁻¹ ∈ blockU L ∨ g * lab sp i * g⁻¹ ∈ blockU2 L s := by
      have key : ∀ (X Y : Subgroup G), conjR X g⁻¹ = Y → ∀ u ∈ X, g * u * g⁻¹ ∈ Y :=
        fun X Y hXY u hu => conj_mem_of_conjR hXY hu
      rcases conj_swap_cases h hg with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hmem with hu | hu
      · exact Or.inl (key _ _ a _ hu)
      · exact Or.inr (key _ _ b _ hu)
      · exact Or.inr (key _ _ a _ hu)
      · exact Or.inl (key _ _ b _ hu)
    have hnc : g * lab sp i * g⁻¹ ∉ Subgroup.centralizer (baum S : Set G) := by
      intro hc
      apply lab_not_central sp hi
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro b hb
      have hb' : g * b * g⁻¹ ∈ baum S :=
        (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_baum S
          (Subgroup.le_normalizer hg)) b).1 hb
      have h2 := hc _ hb'
      have e : g * (b * lab sp i) * g⁻¹ = g * (lab sp i * b) * g⁻¹ := by
        calc g * (b * lab sp i) * g⁻¹ = (g * b * g⁻¹) * (g * lab sp i * g⁻¹) := by group
          _ = (g * lab sp i * g⁻¹) * (g * b * g⁻¹) := h2
          _ = g * (lab sp i * b) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e)
    obtain ⟨j, -, hj⟩ := exists_lab_of_mem sp hmem' hnc
    exact ⟨j, hj⟩

end Action

section Action2

variable (sp : Spec h)

theorem pi_four {g : G} {π : Perm (Fin 5)} (hπ : ∀ i, g * lab sp i * g⁻¹ = lab sp (π i)) :
    π 4 = 4 := by
  apply lab_inj sp
  rw [← hπ 4, lab_four]
  simp

theorem pi_ne_four {g : G} {π : Perm (Fin 5)} (hπ : ∀ i, g * lab sp i * g⁻¹ = lab sp (π i))
    {i : Fin 5} (hi : i ≠ 4) : π i ≠ 4 := by
  intro h4
  apply hi
  apply π.injective
  rw [h4, pi_four sp hπ]

theorem pi_pres {g : G} {π : Perm (Fin 5)} (hπ : ∀ i, g * lab sp i * g⁻¹ = lab sp (π i))
    (h₁ : ∀ u ∈ blockU L, g * u * g⁻¹ ∈ blockU L)
    (h₂ : ∀ u ∈ blockU2 L s, g * u * g⁻¹ ∈ blockU2 L s) :
    (π 0 = 0 ∨ π 0 = 1) ∧ (π 1 = 0 ∨ π 1 = 1) ∧ (π 2 = 2 ∨ π 2 = 3) ∧ (π 3 = 2 ∨ π 3 = 3) := by
  have f1 : ∀ i : Fin 5, i ≠ 4 → lab sp i ∈ blockU L → π i = 0 ∨ π i = 1 := by
    intro i hi hu
    have := h₁ _ hu
    rw [hπ i] at this
    rcases mem_U₁_lab sp this with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (pi_ne_four sp hπ hi)
  have f2 : ∀ i : Fin 5, i ≠ 4 → lab sp i ∈ blockU2 L s → π i = 2 ∨ π i = 3 := by
    intro i hi hu
    have := h₂ _ hu
    rw [hπ i] at this
    rcases mem_U₂_lab sp this with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (pi_ne_four sp hπ hi)
  exact ⟨f1 0 (by decide) sp.kp.hy₁, f1 1 (by decide) sp.kp.y₁z₁_mem,
    f2 2 (by decide) sp.kp.hy₂, f2 3 (by decide) sp.kp.y₂z₂_mem⟩

theorem pi_swap {g : G} {π : Perm (Fin 5)} (hπ : ∀ i, g * lab sp i * g⁻¹ = lab sp (π i))
    (h₁ : ∀ u ∈ blockU L, g * u * g⁻¹ ∈ blockU2 L s)
    (h₂ : ∀ u ∈ blockU2 L s, g * u * g⁻¹ ∈ blockU L) :
    (π 0 = 2 ∨ π 0 = 3) ∧ (π 1 = 2 ∨ π 1 = 3) ∧ (π 2 = 0 ∨ π 2 = 1) ∧ (π 3 = 0 ∨ π 3 = 1) := by
  have f1 : ∀ i : Fin 5, i ≠ 4 → lab sp i ∈ blockU L → π i = 2 ∨ π i = 3 := by
    intro i hi hu
    have := h₁ _ hu
    rw [hπ i] at this
    rcases mem_U₂_lab sp this with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (pi_ne_four sp hπ hi)
  have f2 : ∀ i : Fin 5, i ≠ 4 → lab sp i ∈ blockU2 L s → π i = 0 ∨ π i = 1 := by
    intro i hi hu
    have := h₂ _ hu
    rw [hπ i] at this
    rcases mem_U₁_lab sp this with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (pi_ne_four sp hπ hi)
  exact ⟨f1 0 (by decide) sp.kp.hy₁, f1 1 (by decide) sp.kp.y₁z₁_mem,
    f2 2 (by decide) sp.kp.hy₂, f2 3 (by decide) sp.kp.y₂z₂_mem⟩

end Action2

section PiSpart

variable (sp : Spec h)

theorem exists_piS : ∃ P : PiS S (blockU L ⊔ blockU2 L s),
    ∀ (y : ↥S) (i : Fin 5), (y : G) * lab sp i * (y : G)⁻¹ = lab sp (P.π y i) := by
  refine exists_PiS ?_ sp.kp.elemAbelian_sup sp.kp.card_sup (lab sp) sp.kp.lab_mem (lab_four sp)
    (lab_inj sp) sp.kp.lab_gen ?_
  · rw [← hUeq h]
    exact fun g hg => C56.S_le_normalizer_conjJoin (blockU L) hg
  · exact fun y hy i => stab sp hy i

noncomputable def piS : PiS S (blockU L ⊔ blockU2 L s) := Classical.choose (exists_piS sp)

theorem piS_spec (y : ↥S) (i : Fin 5) :
    (y : G) * lab sp i * (y : G)⁻¹ = lab sp ((piS sp).π y i) :=
  Classical.choose_spec (exists_piS sp) y i

theorem piS_mem_Dset (y : ↥S) : (piS sp).π y ∈ Dset := by
  have hπ := piS_spec sp y
  apply mem_Dset_of_part _ (pi_four sp hπ)
  rcases conj_swap_cases h y.2 with ⟨a, b⟩ | ⟨a, b⟩
  · obtain ⟨p0, p1, -, -⟩ := pi_pres sp hπ (fun u hu => conj_mem_of_conjR a hu)
      (fun u hu => conj_mem_of_conjR b hu)
    exact Or.inl ⟨p0, p1⟩
  · obtain ⟨p0, p1, -, -⟩ := pi_swap sp hπ (fun u hu => conj_mem_of_conjR a hu)
      (fun u hu => conj_mem_of_conjR b hu)
    exact Or.inr ⟨p0, p1⟩

theorem piS_B_mem {b : G} (hb : b ∈ baum S) :
    (piS sp).π ⟨b, baum_le_S' S hb⟩ ∈ Eset := by
  have hπ := piS_spec sp ⟨b, baum_le_S' S hb⟩
  obtain ⟨p0, p1, p2, p3⟩ := pi_pres sp hπ
    (fun u hu => (Subgroup.mem_normalizer_iff.1 (B_le_N_U₁ h hb) u).1 hu)
    (fun u hu => (Subgroup.mem_normalizer_iff.1 (B_le_N_U₂ h hb) u).1 hu)
  exact mem_Eset_of_part _ (pi_four sp hπ) p0 p1 p2 p3

theorem piS_s_not_mem : (piS sp).π ⟨s, h.s_mem⟩ ∉ Eset := by
  intro hE
  have hπ := piS_spec sp ⟨s, h.s_mem⟩
  rcases conj_swap_cases h h.s_mem with ⟨a, -⟩ | ⟨a, b⟩
  · apply U₁_ne_U₂ h
    have e : conjR (conjR (blockU L) s⁻¹) s = blockU L := C5.conjSubgroup_inv_conjSubgroup _ _
    rw [a] at e
    exact e.symm
  · obtain ⟨p0, -, -, -⟩ := pi_swap sp hπ (fun u hu => conj_mem_of_conjR a hu)
      (fun u hu => conj_mem_of_conjR b hu)
    rcases Eset_zero _ hE with h0 | h0 <;> rw [h0] at p0 <;> revert p0 <;> decide

theorem piS_swap01 {b : G} (hb : b ∈ baum S) (hb1 : b ∉ Subgroup.centralizer (blockU L : Set G))
    (hb2 : b ∈ Subgroup.centralizer (blockU2 L s : Set G)) :
    (piS sp).π ⟨b, baum_le_S' S hb⟩ = Equiv.swap 0 1 := by
  have hπ := piS_spec sp ⟨b, baum_le_S' S hb⟩
  obtain ⟨p0, p1, p2, p3⟩ := pi_pres sp hπ
    (fun u hu => (Subgroup.mem_normalizer_iff.1 (B_le_N_U₁ h hb) u).1 hu)
    (fun u hu => (Subgroup.mem_normalizer_iff.1 (B_le_N_U₂ h hb) u).1 hu)
  set π := (piS sp).π ⟨b, baum_le_S' S hb⟩ with hπdef
  have hfix : ∀ u ∈ blockU2 L s, b * u * b⁻¹ = u := fun u hu => by
    have := Subgroup.mem_centralizer_iff.1 hb2 u hu
    calc b * u * b⁻¹ = (b * u) * b⁻¹ := rfl
      _ = (u * b) * b⁻¹ := by rw [← this]
      _ = u := by group
  have h2 : π 2 = 2 := by
    apply lab_inj sp
    rw [← hπ 2]
    exact hfix _ sp.kp.hy₂
  have h3 : π 3 = 3 := by
    apply lab_inj sp
    rw [← hπ 3]
    exact hfix _ sp.kp.y₂z₂_mem
  have h0 : π 0 ≠ 0 := by
    intro h00
    have hc : sp.y₁ * b = b * sp.y₁ := by
      have := hπ 0
      rw [h00] at this
      have e : b * lab sp 0 * b⁻¹ = lab sp 0 := this
      have e2 : b * sp.y₁ = sp.y₁ * b := by
        calc b * sp.y₁ = (b * sp.y₁ * b⁻¹) * b := by group
          _ = sp.y₁ * b := by rw [show b * sp.y₁ * b⁻¹ = sp.y₁ from e]
      exact e2.symm
    exact sp.kp.y₁_nmem ((sp.cent₁ b hb hb1 sp.y₁ sp.kp.hy₁).2 hc)
  have h0' : π 0 = 1 := by
    rcases p0 with h | h
    · exact absurd h h0
    · exact h
  have h1' : π 1 = 0 := by
    rcases p1 with h | h
    · exact h
    · exfalso
      have : π 1 = π 0 := h.trans h0'.symm
      exact absurd (π.injective this) (by decide)
  exact eq_swap01 π h0' h1' h2 h3 (pi_four sp hπ)

theorem piS_swap23 {b : G} (hb : b ∈ baum S) (hb1 : b ∈ Subgroup.centralizer (blockU L : Set G))
    (hb2 : b ∉ Subgroup.centralizer (blockU2 L s : Set G)) :
    (piS sp).π ⟨b, baum_le_S' S hb⟩ = Equiv.swap 2 3 := by
  have hπ := piS_spec sp ⟨b, baum_le_S' S hb⟩
  obtain ⟨p0, p1, p2, p3⟩ := pi_pres sp hπ
    (fun u hu => (Subgroup.mem_normalizer_iff.1 (B_le_N_U₁ h hb) u).1 hu)
    (fun u hu => (Subgroup.mem_normalizer_iff.1 (B_le_N_U₂ h hb) u).1 hu)
  set π := (piS sp).π ⟨b, baum_le_S' S hb⟩ with hπdef
  have hfix : ∀ u ∈ blockU L, b * u * b⁻¹ = u := fun u hu => by
    have := Subgroup.mem_centralizer_iff.1 hb1 u hu
    calc b * u * b⁻¹ = (b * u) * b⁻¹ := rfl
      _ = (u * b) * b⁻¹ := by rw [← this]
      _ = u := by group
  have h0 : π 0 = 0 := by
    apply lab_inj sp
    rw [← hπ 0]
    exact hfix _ sp.kp.hy₁
  have h1 : π 1 = 1 := by
    apply lab_inj sp
    rw [← hπ 1]
    exact hfix _ sp.kp.y₁z₁_mem
  have h2 : π 2 ≠ 2 := by
    intro h22
    have hc : sp.y₂ * b = b * sp.y₂ := by
      have := hπ 2
      rw [h22] at this
      have e : b * lab sp 2 * b⁻¹ = lab sp 2 := this
      have e2 : b * sp.y₂ = sp.y₂ * b := by
        calc b * sp.y₂ = (b * sp.y₂ * b⁻¹) * b := by group
          _ = sp.y₂ * b := by rw [show b * sp.y₂ * b⁻¹ = sp.y₂ from e]
      exact e2.symm
    exact sp.kp.y₂_nmem ((sp.cent₂ b hb hb2 sp.y₂ sp.kp.hy₂).2 hc)
  have h2' : π 2 = 3 := by
    rcases p2 with h | h
    · exact absurd h h2
    · exact h
  have h3' : π 3 = 2 := by
    rcases p3 with h | h
    · exact h
    · exfalso
      have : π 3 = π 2 := h.trans h2'.symm
      exact absurd (π.injective this) (by decide)
  exact eq_swap23 π h0 h1 h2' h3' (pi_four sp hπ)

end PiSpart

end A3x

end CFSG.Quasithin.YG.AppD
