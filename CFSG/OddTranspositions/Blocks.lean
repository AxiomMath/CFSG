module

public import CFSG.Timmesfeld.Bridge.Asc72Basic

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def IsBlock (D α : Set G) : Prop :=
  α ⊆ D ∧ α.Nonempty ∧ α ≠ D ∧
    ∀ g : G, g ∉ Subgroup.normalizer α →
      Disjoint α ((fun x => g * x * g⁻¹) '' α)

@[expose] def blockClass (α : Set G) : Set (Set G) :=
  {β | ∃ g : ConjAct G, β = g • α}

@[expose] def Dalpha (D α : Set G) : Set (Set G) :=
  {β | β ∈ blockClass α ∧ β ⊆ D ∧ β ≠ α ∧ ∀ a ∈ α, ∀ b ∈ β, Commute a b}

@[expose] def DalphaStar (D α : Set G) : Set G :=
  {x | ∃ β ∈ Dalpha D α, x ∈ β}

@[expose] def perp (D α : Set G) : Set (Set G) := Dalpha D α ∪ {α}

@[expose] def Aalpha (D α : Set G) : Set (Set G) := blockClass α \ perp D α

@[expose] def AalphaStar (D α : Set G) : Set G :=
  {x | ∃ β ∈ Aalpha D α, x ∈ β}

@[expose] def Valpha (D α : Set G) : Set (Set G) :=
  {β | β ∈ blockClass α ∧ perp D β = perp D α}

@[expose] def Walpha (D α : Set G) : Set (Set G) :=
  {β | β ∈ blockClass α ∧ Dalpha D β = Dalpha D α}

@[expose] def Halpha (D α : Set G) : Subgroup G := Subgroup.closure (DalphaStar D α)

@[expose] def Malpha (D α : Set G) : Subgroup G :=
  (CFSG.solvableRadical (Halpha D α)).map (Halpha D α).subtype

theorem IsBlock.subset {D α : Set G} (h : IsBlock D α) : α ⊆ D := h.1

theorem IsBlock.nonempty {D α : Set G} (h : IsBlock D α) : α.Nonempty := h.2.1

theorem IsBlock.ne_univ {D α : Set G} (h : IsBlock D α) : α ≠ D := h.2.2.1

theorem IsBlock.disjoint_conj {D α : Set G} (h : IsBlock D α) {g : G}
    (hg : g ∉ Subgroup.normalizer α) :
    Disjoint α ((fun x => g * x * g⁻¹) '' α) := h.2.2.2 g hg

theorem smul_ne_self_of_not_mem_normalizer {S : Set G} {t : G}
    (ht : t ∉ Subgroup.normalizer S) : ConjAct.toConjAct t • S ≠ S := by
  intro hEq
  apply ht
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have himg : ConjAct.toConjAct t • S = MulAut.conj t '' S := by
    rw [← Set.image_smul]
    rfl
  rwa [himg] at hEq

theorem IsBlock.isBlock {D α : Set G} (h : IsBlock D α) :
    MulAction.IsBlock (ConjAct G) α := by
  rw [MulAction.isBlock_iff_disjoint_smul_of_ne]
  intro g hg
  have hgn : ConjAct.ofConjAct g ∉ Subgroup.normalizer α := by
    intro hmem
    apply hg
    have himg : g • α = MulAut.conj (ConjAct.ofConjAct g) '' α := by
      rw [← Set.image_smul]
      rfl
    rw [himg, Subgroup.mem_normalizer_iff_conj_image_eq.mp hmem]
  have hd := h.2.2.2 (ConjAct.ofConjAct g) hgn
  have himg : g • α =
      (fun x => ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹) '' α := by
    rw [← Set.image_smul]
    rfl
  rw [himg]
  exact hd.symm

theorem mem_blockClass_iff {α β : Set G} :
    β ∈ blockClass α ↔ ∃ g : G, β = (fun x => g * x * g⁻¹) '' α := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨ConjAct.ofConjAct g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨ConjAct.toConjAct g, rfl⟩

theorem mem_blockClass_iff' {α β : Set G} :
    β ∈ blockClass α ↔ ∃ g : ConjAct G, β = g • α := Iff.rfl

theorem mem_blockClass_self (α : Set G) : α ∈ blockClass α :=
  ⟨1, by simp⟩

theorem IsBlock.conj {D α : Set G} (hN : IsNormalSet D) (h : IsBlock D α) (g : ConjAct G) :
    IsBlock D (g • α) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← Set.image_smul] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [ConjAct.smul_def] using hN (ConjAct.ofConjAct g) y (h.subset hy)
  · rw [← Set.image_smul]
    exact h.nonempty.image _
  · intro hEq
    apply h.ne_univ
    have hDinv : ∀ t : ConjAct G, t • D = D := by
      intro t
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [ConjAct.smul_def] using hN (ConjAct.ofConjAct t) y hy
      · intro hx
        refine ⟨(ConjAct.ofConjAct t)⁻¹ * x * ConjAct.ofConjAct t, ?_, ?_⟩
        · simpa [ConjAct.smul_def] using hN (ConjAct.ofConjAct t)⁻¹ x hx
        · simp only [ConjAct.smul_def]
          group
    have hα : α = g⁻¹ • D := by
      calc α = g⁻¹ • (g • α) := (inv_smul_smul g α).symm
        _ = g⁻¹ • D := by rw [hEq]
    rw [hDinv g⁻¹] at hα
    exact hα
  · intro t ht
    have hne : ConjAct.toConjAct t • (g • α) ≠ g • α :=
      smul_ne_self_of_not_mem_normalizer ht
    have hd := (MulAction.isBlock_iff_disjoint_smul_of_ne.mp (h.isBlock.translate g)) hne
    exact hd.symm

theorem DalphaStar_subset {D α : Set G} (h : IsBlock D α) : DalphaStar D α ⊆ D := by
  rintro x ⟨β, hβ, hxβ⟩
  exact hβ.2.1 hxβ

theorem mem_Dalpha_iff {D α β : Set G} :
    β ∈ Dalpha D α ↔ β ∈ blockClass α ∧ β ⊆ D ∧ β ≠ α ∧
      ∀ a ∈ α, ∀ b ∈ β, Commute a b := Iff.rfl

theorem mem_DalphaStar_iff {D α : Set G} {x : G} :
    x ∈ DalphaStar D α ↔ ∃ β ∈ Dalpha D α, x ∈ β := Iff.rfl

theorem mem_perp_iff {D α β : Set G} :
    β ∈ perp D α ↔ β ∈ Dalpha D α ∨ β = α := Iff.rfl

theorem mem_Valpha_iff {D α β : Set G} :
    β ∈ Valpha D α ↔ β ∈ blockClass α ∧ perp D β = perp D α := Iff.rfl

theorem mem_Walpha_iff {D α β : Set G} :
    β ∈ Walpha D α ↔ β ∈ blockClass α ∧ Dalpha D β = Dalpha D α := Iff.rfl

theorem mem_Valpha_self (D α : Set G) : α ∈ Valpha D α :=
  ⟨mem_blockClass_self α, rfl⟩

theorem mem_Walpha_self (D α : Set G) : α ∈ Walpha D α :=
  ⟨mem_blockClass_self α, rfl⟩

theorem mem_Aalpha_iff {D α β : Set G} :
    β ∈ Aalpha D α ↔ β ∈ blockClass α ∧ β ∉ perp D α := Iff.rfl

theorem mem_AalphaStar_iff {D α : Set G} {x : G} :
    x ∈ AalphaStar D α ↔ ∃ β ∈ Aalpha D α, x ∈ β := by
  rfl

theorem AalphaStar_subset {D α : Set G} (hN : IsNormalSet D) (hα : IsBlock D α) :
    AalphaStar D α ⊆ D := by
  rintro x ⟨β, hβ, hxβ⟩
  obtain ⟨hclass, -⟩ := mem_Aalpha_iff.mp hβ
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hclass
  rw [hg] at hxβ
  obtain ⟨y, hy, rfl⟩ := hxβ
  exact hN g y (hα.subset hy)

theorem disjoint_alpha_AalphaStar {D α : Set G} (hα : IsBlock D α) :
    Disjoint α (AalphaStar D α) := by
  rw [Set.disjoint_left]
  rintro x hxα ⟨β, hβ, hxβ⟩
  obtain ⟨hclass, hnotperp⟩ := mem_Aalpha_iff.mp hβ
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hclass
  have hβne : β ≠ α := fun h => hnotperp (mem_perp_iff.mpr (Or.inr h))
  have hdisj : Disjoint α β := by
    rw [hg]
    by_cases hgN : g ∈ Subgroup.normalizer α
    · exfalso
      have himg : (fun y => g * y * g⁻¹) '' α = α :=
        Subgroup.mem_normalizer_iff_conj_image_eq.mp hgN
      exact hβne (hg.trans himg)
    · exact hα.disjoint_conj hgN
  exact (Set.disjoint_left.mp hdisj hxα) hxβ

theorem subset_DalphaStar {D α : Set G} {β : Set G} (hβ : β ∈ Dalpha D α) :
    β ⊆ DalphaStar D α :=
  fun _ hx => ⟨β, hβ, hx⟩

theorem commute_of_isOddTransp_invariant_partition {T P Q : Set G} (hodd : IsOddTransp T)
    (hPT : P ⊆ T) (hQT : Q ⊆ T)
    (hP : ∀ g ∈ Subgroup.closure T, ∀ x ∈ P, g * x * g⁻¹ ∈ P)
    (hQ : ∀ g ∈ Subgroup.closure T, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q)
    (hdisj : Disjoint P Q) :
    ∀ x ∈ P, ∀ y ∈ Q, Commute x y := by
  intro x hx y hy
  by_contra hxy
  obtain ⟨g, hg, hgx⟩ :=
    CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul (hodd.mul_self_eq_one (hPT hx))
      (hodd.mul_self_eq_one (hQT hy)) (hodd.odd_of_not_commute (hPT hx) (hQT hy) hxy)
  have hgT : g ∈ Subgroup.closure T :=
    Subgroup.closure_mono (show ({x, y} : Set G) ⊆ T from by
      rintro z (rfl | rfl)
      · exact hPT hx
      · exact hQT hy) hg
  have hyP : y ∈ P := by
    rw [← hgx]
    exact hP g hgT x hx
  exact (Set.disjoint_left.mp hdisj hyP) hy

theorem commute_of_mem_block {D β : Set G} (hN : IsNormalSet D) (hodd : IsOddTransp D)
    (hβ : IsBlock D β) {A B : G} (hA : A ∈ β) (hB : B ∈ D) (hBβ : B ∉ β)
    (hAB : Commute A B) : ∀ x ∈ β, Commute B x := by
  have hBnorm : ConjAct.toConjAct B • β = β := by
    refine MulAction.IsBlock.smul_eq_of_mem hβ.isBlock hA ?_
    rw [ConjAct.toConjAct_smul]
    have hBA : B * A * B⁻¹ = A := by
      rw [hAB.eq.symm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hBA]
    exact hA
  have hβnorm : β ⊆ (MulAction.stabilizer (ConjAct G) β).comap
      (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom := by
    intro x hx
    change ConjAct.toConjAct x ∈ MulAction.stabilizer (ConjAct G) β
    rw [MulAction.mem_stabilizer_iff]
    exact MulAction.IsBlock.smul_eq_of_mem hβ.isBlock hx (by
      simpa [ConjAct.toConjAct_smul] using hx)
  set H : Subgroup G := Subgroup.closure (β ∪ {B}) with hH
  have hHnorm : H ≤ (MulAction.stabilizer (ConjAct G) β).comap
      (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom := by
    rw [hH, Subgroup.closure_le]
    rintro x (hx | rfl)
    · exact hβnorm hx
    · change ConjAct.toConjAct x ∈ MulAction.stabilizer (ConjAct G) β
      rw [MulAction.mem_stabilizer_iff]
      exact hBnorm
  have hβinv : ∀ h ∈ H, ∀ x ∈ β, h * x * h⁻¹ ∈ β := by
    intro h hh x hx
    have hh' : ConjAct.toConjAct h • β = β := hHnorm hh
    have : ConjAct.toConjAct h • x ∈ ConjAct.toConjAct h • β :=
      Set.smul_mem_smul_set hx
    rw [hh'] at this
    simpa [ConjAct.toConjAct_smul] using this
  set Γ : Set G := (H : Set G) ∩ D with hΓ
  have hΓH : Subgroup.closure Γ ≤ H := by
    rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  have hβΓ : β ⊆ Γ :=
    fun x hx => ⟨Subgroup.subset_closure (Or.inl hx), hβ.subset hx⟩
  have hBΓ : B ∈ Γ :=
    ⟨Subgroup.subset_closure (Or.inr (by simp)), hB⟩
  have hoddΓ : IsOddTransp Γ :=
    ⟨fun x hx => hodd.1 x hx.2, fun x hx y hy => hodd.2 x hx.2 y hy.2⟩
  have hPinv : ∀ g ∈ Subgroup.closure Γ, ∀ x ∈ β, g * x * g⁻¹ ∈ β :=
    fun g hg => hβinv g (hΓH hg)
  have hQinv : ∀ g ∈ Subgroup.closure Γ, ∀ x ∈ Γ \ β, g * x * g⁻¹ ∈ Γ \ β := by
    intro g hg x hx
    have hgH : g ∈ H := hΓH hg
    have hxH : x ∈ H := hx.1.1
    have hxD : x ∈ D := hx.1.2
    refine ⟨⟨H.mul_mem (H.mul_mem hgH hxH) (H.inv_mem hgH), ?_⟩, ?_⟩
    · simpa [ConjAct.smul_def] using hN g x hxD
    · intro hxβ
      have hxβ' : g⁻¹ * (g * x * g⁻¹) * g ∈ β := by
        simpa using hβinv g⁻¹ (H.inv_mem hgH) (g * x * g⁻¹) hxβ
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [e] at hxβ'
      exact hx.2 hxβ'
  have hdisj : Disjoint β (Γ \ β) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.2 hx
  have hcomm := commute_of_isOddTransp_invariant_partition hoddΓ hβΓ (fun x hx => hx.1)
    hPinv hQinv hdisj
  intro x hx
  exact (hcomm x hx B ⟨hBΓ, hBβ⟩).symm

theorem commute_block_of_mem {D α : Set G} (hN : IsNormalSet D) (hodd : IsOddTransp D)
    (h : IsBlock D α) {g : ConjAct G} (hne : g • α ≠ α) {A B : G} (hA : A ∈ α)
    (hB : B ∈ g • α) (hAB : Commute A B) :
    ∀ a ∈ α, ∀ b ∈ g • α, Commute a b := by
  have hβ : IsBlock D (g • α) := h.conj hN g
  have hBD : B ∈ D := hβ.subset hB
  have hdisj : Disjoint (g • α) α :=
    (MulAction.isBlock_iff_disjoint_smul_of_ne.mp h.isBlock) hne
  have hBα : B ∉ α := fun hBα => (Set.disjoint_left.mp hdisj hB) hBα
  have hBcomm : ∀ x ∈ α, Commute B x :=
    commute_of_mem_block hN hodd h hA hBD hBα hAB
  intro a ha b hb
  have haD : a ∈ D := h.subset ha
  have haβ : a ∉ g • α := fun haβ => (Set.disjoint_left.mp hdisj haβ) ha
  exact commute_of_mem_block hN hodd hβ hB haD haβ (hBcomm a ha) b hb

theorem commute_block_of_mem_apply {D α : Set G} (hN : IsNormalSet D) (hodd : IsOddTransp D)
    (h : IsBlock D α) {g : G} (hne : (fun x => g * x * g⁻¹) '' α ≠ α) {A B : G}
    (hA : A ∈ α) (hB : B ∈ (fun x => g * x * g⁻¹) '' α) (hAB : Commute A B) :
    ∀ a ∈ α, ∀ b ∈ (fun x => g * x * g⁻¹) '' α, Commute a b := by
  have himg : ConjAct.toConjAct g • α = (fun x => g * x * g⁻¹) '' α := by
    rw [← Set.image_smul]
    rfl
  have hne' : ConjAct.toConjAct g • α ≠ α := by
    rwa [himg]
  have hB' : B ∈ ConjAct.toConjAct g • α := by
    rwa [himg]
  have hcomm := commute_block_of_mem hN hodd h hne' hA hB' hAB
  intro a ha b hb
  exact hcomm a ha b (by rwa [himg])

theorem Dalpha.conj {D α β : Set G} (hN : IsNormalSet D) (hβ : β ∈ Dalpha D α) (g : G) :
    (fun x => g * x * g⁻¹) '' β ∈ Dalpha D ((fun x => g * x * g⁻¹) '' α) := by
  obtain ⟨hclass, hsub, hne, hcomm⟩ := hβ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_blockClass_iff] at hclass
    obtain ⟨h, rfl⟩ := hclass
    rw [mem_blockClass_iff]
    refine ⟨g * h * g⁻¹, ?_⟩
    simp only [Set.image_image]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by group⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by group⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hN g z (hsub hz)
  · have hinj : Function.Injective (fun x : G => g * x * g⁻¹) := by
      intro x y hxy
      have hxy' : g * x * g⁻¹ = g * y * g⁻¹ := by simpa using hxy
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hxy']
        _ = y := by group
    intro hEq
    exact hne ((Set.image_injective.mpr hinj) hEq)
  · intro a ha b hb
    rw [Set.mem_image] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact (hcomm a' ha' b' hb').conj g

theorem Dalpha.subset {D α β : Set G} (hβ : β ∈ Dalpha D α) : β ⊆ D := hβ.2.1

theorem Dalpha.ne_self {D α β : Set G} (hβ : β ∈ Dalpha D α) : β ≠ α := hβ.2.2.1

theorem DalphaStar.conj {D α : Set G} (hN : IsNormalSet D) {x : G}
    (hx : x ∈ DalphaStar D α) (g : G) :
    g * x * g⁻¹ ∈ DalphaStar D ((fun y => g * y * g⁻¹) '' α) := by
  obtain ⟨β, hβ, hxβ⟩ := hx
  exact ⟨(fun y => g * y * g⁻¹) '' β, Dalpha.conj hN hβ g, ⟨x, hxβ, rfl⟩⟩

theorem perp.conj {D α β : Set G} (hN : IsNormalSet D) (hβ : β ∈ perp D α) (g : G) :
    (fun x => g * x * g⁻¹) '' β ∈ perp D ((fun x => g * x * g⁻¹) '' α) := by
  rw [mem_perp_iff] at hβ
  rw [mem_perp_iff]
  rcases hβ with h | rfl
  · exact Or.inl (Dalpha.conj hN h g)
  · exact Or.inr rfl

theorem Aalpha.conj {D α β : Set G} (hN : IsNormalSet D) (hβ : β ∈ Aalpha D α) (g : G) :
    (fun x => g * x * g⁻¹) '' β ∈ Aalpha D ((fun x => g * x * g⁻¹) '' α) := by
  rw [mem_Aalpha_iff] at hβ
  rw [mem_Aalpha_iff]
  obtain ⟨hclass, hnotperp⟩ := hβ
  refine ⟨?_, ?_⟩
  · rw [mem_blockClass_iff] at hclass
    obtain ⟨h, rfl⟩ := hclass
    rw [mem_blockClass_iff]
    refine ⟨g * h * g⁻¹, ?_⟩
    simp only [Set.image_image]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by group⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by group⟩
  · intro hperp
    have h' := perp.conj hN hperp g⁻¹
    simp only [inv_inv] at h'
    have hconj (s : Set G) :
        (fun x => g⁻¹ * x * g) '' ((fun x => g * x * g⁻¹) '' s) = s := by
      simp only [Set.image_image]
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        have h : g⁻¹ * (g * b * g⁻¹) * g = b := by group
        change g⁻¹ * (g * b * g⁻¹) * g ∈ s
        rwa [h]
      · intro ha
        exact ⟨a, ha, by group⟩
    rw [hconj β, hconj α] at h'
    exact hnotperp h'

theorem Halpha_le_normalizer {D α : Set G} (hN : IsNormalSet D) :
    Halpha D α ≤ Subgroup.normalizer (DalphaStar D α) := by
  have key : ∀ (x : G) (β : Set G), (∀ a ∈ α, Commute a x) → β ∈ Dalpha D α →
      (fun y => x * y * x⁻¹) '' β ∈ Dalpha D α := by
    intro x β hx hβ
    obtain ⟨hclass, hsub, hne, hcomm⟩ := hβ
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mem_blockClass_iff] at hclass
      obtain ⟨k, rfl⟩ := hclass
      rw [mem_blockClass_iff]
      refine ⟨x * k, ?_⟩
      simp only [Set.image_image]
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, by group⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, by group⟩
    · rintro y ⟨z, hz, rfl⟩
      exact hN x z (hsub hz)
    · have hxfix : (fun y => x * y * x⁻¹) '' α = α := by
        ext a
        constructor
        · rintro ⟨b, hb, rfl⟩
          have hbx : x * b = b * x := (hx b hb).symm.eq
          simpa [hbx]
        · intro ha
          refine ⟨a, ha, ?_⟩
          have hax : x * a = a * x := (hx a ha).symm.eq
          simpa [hax]
      have hinj : Function.Injective (fun y : G => x * y * x⁻¹) := by
        intro y z hyz
        have hyz' : x * y * x⁻¹ = x * z * x⁻¹ := by simpa using hyz
        calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = x⁻¹ * (x * z * x⁻¹) * x := by rw [hyz']
          _ = z := by group
      intro hEq
      exact hne ((Set.image_injective.mpr hinj) (hEq.trans hxfix.symm))
    · intro a ha y hy
      rw [Set.mem_image] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      have hax : Commute a x := hx a ha
      have hab : Commute a b := hcomm a ha b hb
      exact (hax.mul_right hab).mul_right hax.inv_right
  rw [Halpha, Subgroup.closure_le]
  intro x hx
  obtain ⟨β, hβ, hxβ⟩ := hx
  have hxcomm : ∀ a ∈ α, Commute a x := fun a ha => hβ.2.2.2 a ha x hxβ
  change x ∈ Subgroup.normalizer (DalphaStar D α)
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨γ, hγ, hyγ⟩ := hy
    exact ⟨(fun z => x * z * x⁻¹) '' γ, key x γ hxcomm hγ, ⟨y, hyγ, rfl⟩⟩
  · intro hy
    obtain ⟨γ, hγ, hyγ⟩ := hy
    have hxinv : ∀ a ∈ α, Commute a x⁻¹ := fun a ha => (hxcomm a ha).inv_right
    refine ⟨(fun z => x⁻¹ * z * x) '' γ, ?_,
      ⟨x * y * x⁻¹, hyγ, by group⟩⟩
    simpa only [inv_inv] using key x⁻¹ γ hxinv hγ

theorem DalphaStar.invariant_normalizer {D α : Set G} (hN : IsNormalSet D) {g : G}
    (hg : g ∈ Subgroup.normalizer α) :
    ∀ x ∈ DalphaStar D α, g * x * g⁻¹ ∈ DalphaStar D α := by
  intro x hx
  have himg : (fun y => g * y * g⁻¹) '' α = α :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp hg
  have h := DalphaStar.conj hN hx g
  rwa [himg] at h

theorem normalizer_conj_mem_Halpha {D α : Set G} (hN : IsNormalSet D) {g : G}
    (hg : g ∈ Subgroup.normalizer α) {y : G} (hy : y ∈ Halpha D α) :
    g * y * g⁻¹ ∈ Halpha D α :=
  Subgroup.closure_induction (p := fun z _ => g * z * g⁻¹ ∈ Halpha D α)
    (fun x hx => Subgroup.subset_closure (DalphaStar.invariant_normalizer hN hg x hx))
    (by simpa using Subgroup.one_mem (Halpha D α))
    (fun x z _ _ hx hz => by
      rw [show g * (x * z) * g⁻¹ = (g * x * g⁻¹) * (g * z * g⁻¹) by group]
      exact Subgroup.mul_mem _ hx hz)
    (fun x _ hx => by
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ hx)
    hy

theorem normalizer_le_normalizer_Halpha {D α : Set G} (hN : IsNormalSet D) :
    Subgroup.normalizer α ≤ Subgroup.normalizer (Halpha D α) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact normalizer_conj_mem_Halpha hN hg hy
  · intro hy
    have hg' : g⁻¹ ∈ Subgroup.normalizer α := Subgroup.inv_mem _ hg
    have h := normalizer_conj_mem_Halpha hN hg' (y := g * y * g⁻¹) hy
    have h' : g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ = y := by group
    rwa [h'] at h

theorem Dalpha_conj_image {D β : Set G} (hN : IsNormalSet D) (g : G) :
    (fun γ => (fun x => g * x * g⁻¹) '' γ) '' Dalpha D β =
      Dalpha D ((fun x => g * x * g⁻¹) '' β) := by
  ext γ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact Dalpha.conj hN hδ g
  · intro hγ
    have h : (fun x => g⁻¹ * x * g) '' γ ∈
        Dalpha D ((fun x => g⁻¹ * x * g) '' ((fun x => g * x * g⁻¹) '' β)) := by
      have h0 := Dalpha.conj hN hγ g⁻¹
      simpa only [inv_inv] using h0
    have hβ : (fun x => g⁻¹ * x * g) '' ((fun x => g * x * g⁻¹) '' β) = β := by
      rw [Set.image_image]
      have hfun : (fun x => g⁻¹ * (g * x * g⁻¹) * g) = id := by
        funext x
        show g⁻¹ * (g * x * g⁻¹) * g = x
        group
      rw [hfun, Set.image_id]
    rw [hβ] at h
    refine ⟨_, h, ?_⟩
    show (fun x => g * x * g⁻¹) '' ((fun x => g⁻¹ * x * g) '' γ) = γ
    rw [Set.image_image]
    have hfun : (fun x => g * (g⁻¹ * x * g) * g⁻¹) = id := by
      funext x
      show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
    rw [hfun, Set.image_id]

theorem perp_conj_image {D β : Set G} (hN : IsNormalSet D) (g : G) :
    (fun γ => (fun x => g * x * g⁻¹) '' γ) '' perp D β =
      perp D ((fun x => g * x * g⁻¹) '' β) := by
  rw [perp, perp, Set.image_union, Dalpha_conj_image hN]
  simp

theorem smul_perp {D β : Set G} (hN : IsNormalSet D) (g : ConjAct G) :
    g • perp D β = perp D (g • β) := by
  have hfun : (fun γ : Set G => g • γ) =
      (fun γ => (fun x => ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹) '' γ) := by
    funext γ
    rw [← Set.image_smul]
    rfl
  have himg : g • β =
      (fun x => ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹) '' β := by
    rw [← Set.image_smul]
    rfl
  rw [← Set.image_smul, hfun, perp_conj_image hN, ← himg]

theorem smul_Dalpha {D β : Set G} (hN : IsNormalSet D) (g : ConjAct G) :
    g • Dalpha D β = Dalpha D (g • β) := by
  have hfun : (fun γ : Set G => g • γ) =
      (fun γ => (fun x => ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹) '' γ) := by
    funext γ
    rw [← Set.image_smul]
    rfl
  have himg : g • β =
      (fun x => ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹) '' β := by
    rw [← Set.image_smul]
    rfl
  rw [← Set.image_smul, hfun, Dalpha_conj_image hN, ← himg]

theorem isBlockSet_Valpha {D α : Set G} (hN : IsNormalSet D) :
    MulAction.IsBlock (ConjAct G) (Valpha D α) := by
  classical
  rw [MulAction.isBlock_iff_disjoint_smul_of_ne]
  intro g hg
  by_contra hne
  rw [Set.not_disjoint_iff] at hne
  obtain ⟨β, hβgV, hβV⟩ := hne
  obtain ⟨γ, hγV, hβγ⟩ := Set.mem_smul_set.mp hβgV
  have hfix : g • perp D α = perp D α := by
    calc g • perp D α = g • perp D γ := by rw [hγV.2]
      _ = perp D (g • γ) := smul_perp (β := γ) hN g
      _ = perp D β := by rw [← hβγ]
      _ = perp D α := hβV.2
  have hsub : ∀ δ ∈ Valpha D α, g • δ ∈ Valpha D α := by
    intro δ hδ
    refine ⟨?_, ?_⟩
    · obtain ⟨h, rfl⟩ := mem_blockClass_iff'.mp hδ.1
      exact mem_blockClass_iff'.mpr ⟨g * h, (mul_smul g h α).symm⟩
    · calc perp D (g • δ) = g • perp D δ := (smul_perp (β := δ) hN g).symm
        _ = g • perp D α := by rw [hδ.2]
        _ = perp D α := hfix
  have hgV : g • Valpha D α ⊆ Valpha D α := by
    rintro δ ⟨ε, hε, rfl⟩
    exact hsub ε hε
  have hfix' : g⁻¹ • perp D α = perp D α := by
    have h := congrArg (fun s : Set (Set G) => g⁻¹ • s) hfix
    simpa [← mul_smul] using h.symm
  have hsub' : ∀ δ ∈ Valpha D α, g⁻¹ • δ ∈ Valpha D α := by
    intro δ hδ
    refine ⟨?_, ?_⟩
    · obtain ⟨h, rfl⟩ := mem_blockClass_iff'.mp hδ.1
      exact mem_blockClass_iff'.mpr ⟨g⁻¹ * h, (mul_smul g⁻¹ h α).symm⟩
    · calc perp D (g⁻¹ • δ) = g⁻¹ • perp D δ := (smul_perp (β := δ) hN g⁻¹).symm
        _ = g⁻¹ • perp D α := by rw [hδ.2]
        _ = perp D α := hfix'
  have hle : Valpha D α ⊆ g • Valpha D α := by
    intro δ hδ
    have h1 : g⁻¹ • δ ∈ Valpha D α := hsub' δ hδ
    have h2 : g • (g⁻¹ • δ) ∈ g • Valpha D α := ⟨_, h1, rfl⟩
    simpa [← mul_smul] using h2
  exact hg (Set.Subset.antisymm hgV hle)

theorem isBlockSet_Walpha {D α : Set G} (hN : IsNormalSet D) :
    MulAction.IsBlock (ConjAct G) (Walpha D α) := by
  classical
  rw [MulAction.isBlock_iff_disjoint_smul_of_ne]
  intro g hg
  by_contra hne
  rw [Set.not_disjoint_iff] at hne
  obtain ⟨β, hβgV, hβV⟩ := hne
  obtain ⟨γ, hγV, hβγ⟩ := Set.mem_smul_set.mp hβgV
  have hfix : g • Dalpha D α = Dalpha D α := by
    calc g • Dalpha D α = g • Dalpha D γ := by rw [hγV.2]
      _ = Dalpha D (g • γ) := smul_Dalpha (β := γ) hN g
      _ = Dalpha D β := by rw [← hβγ]
      _ = Dalpha D α := hβV.2
  have hsub : ∀ δ ∈ Walpha D α, g • δ ∈ Walpha D α := by
    intro δ hδ
    refine ⟨?_, ?_⟩
    · obtain ⟨h, rfl⟩ := mem_blockClass_iff'.mp hδ.1
      exact mem_blockClass_iff'.mpr ⟨g * h, (mul_smul g h α).symm⟩
    · calc Dalpha D (g • δ) = g • Dalpha D δ := (smul_Dalpha (β := δ) hN g).symm
        _ = g • Dalpha D α := by rw [hδ.2]
        _ = Dalpha D α := hfix
  have hgV : g • Walpha D α ⊆ Walpha D α := by
    rintro δ ⟨ε, hε, rfl⟩
    exact hsub ε hε
  have hfix' : g⁻¹ • Dalpha D α = Dalpha D α := by
    have h := congrArg (fun s : Set (Set G) => g⁻¹ • s) hfix
    simpa [← mul_smul] using h.symm
  have hsub' : ∀ δ ∈ Walpha D α, g⁻¹ • δ ∈ Walpha D α := by
    intro δ hδ
    refine ⟨?_, ?_⟩
    · obtain ⟨h, rfl⟩ := mem_blockClass_iff'.mp hδ.1
      exact mem_blockClass_iff'.mpr ⟨g⁻¹ * h, (mul_smul g⁻¹ h α).symm⟩
    · calc Dalpha D (g⁻¹ • δ) = g⁻¹ • Dalpha D δ := (smul_Dalpha (β := δ) hN g⁻¹).symm
        _ = g⁻¹ • Dalpha D α := by rw [hδ.2]
        _ = Dalpha D α := hfix'
  have hle : Walpha D α ⊆ g • Walpha D α := by
    intro δ hδ
    have h1 : g⁻¹ • δ ∈ Walpha D α := hsub' δ hδ
    have h2 : g • (g⁻¹ • δ) ∈ g • Walpha D α := ⟨_, h1, rfl⟩
    simpa [← mul_smul] using h2
  exact hg (Set.Subset.antisymm hgV hle)

end CFSG.OddTranspositions