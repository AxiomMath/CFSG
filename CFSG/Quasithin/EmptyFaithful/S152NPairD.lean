module

public import CFSG.Quasithin.EmptyFaithful.S152NPairC
public import CFSG.Quasithin.EmptyFaithful.S152N9

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152Fin

variable {H U L N B F₁ F₂ X₁ X₂ : Subgroup G}

namespace PairStep

variable (P : PairStep H U L N B F₁ F₂ X₁ X₂)

include P in
theorem cSecIn_F₁_eq : cSecIn F₁ L X₁ = F₁ ⊓ pCoreOf 2 H := by
  have hF : F₁ ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_conj fun f hf l hl => P.H_norm_L f (P.F₁_le hf) l hl
  apply le_antisymm
  · intro f hf
    obtain ⟨hfF, hfX⟩ := mem_cSecIn hF hf
    refine ⟨hfF, P.C_inf_le ⟨?_, ?_⟩⟩
    · exact P.mem_C₁.mpr ⟨P.F₁_le_B hfF, hfX⟩
    · exact P.mem_C₂.mpr ⟨P.F₁_le_B hfF, P.F₁_triv f hfF⟩
  · rintro f ⟨hfF, hfQ⟩
    apply Subgroup.subset_closure
    exact ⟨hfF, fun x hx => (P.mem_C₁.mp (P.Q_le_C₁ hfQ)).2 x hx⟩

include P in
theorem cSecIn_F₂_eq : cSecIn F₂ L X₂ = F₂ ⊓ pCoreOf 2 H := by
  have hF : F₂ ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_conj fun f hf l hl => P.H_norm_L f (P.F₂_le hf) l hl
  apply le_antisymm
  · intro f hf
    obtain ⟨hfF, hfX⟩ := mem_cSecIn hF hf
    refine ⟨hfF, P.C_inf_le ⟨?_, ?_⟩⟩
    · exact P.mem_C₁.mpr ⟨P.F₂_le_B hfF, P.F₂_triv f hfF⟩
    · exact P.mem_C₂.mpr ⟨P.F₂_le_B hfF, hfX⟩
  · rintro f ⟨hfF, hfQ⟩
    apply Subgroup.subset_closure
    exact ⟨hfF, fun x hx => (P.mem_C₂.mp (P.Q_le_C₂ hfQ)).2 x hx⟩

include P in
theorem iso₁ : Nonempty (↥(imageOTwoQuot H (F₁ ⊔ pCoreOf 2 H)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨θ, hθs, hθk⟩ := P.θ₁
  refine imageOTwoQuot_equiv P.F₁_le θ hθs fun f => ?_
  have h : θ f = 1 ↔ f ∈ θ.ker := MonoidHom.mem_ker.symm
  rw [h, hθk, Subgroup.mem_subgroupOf, P.cSecIn_F₁_eq]
  exact ⟨fun h => h.2, fun h => ⟨f.2, h⟩⟩

include P in
theorem iso₂ : Nonempty (↥(imageOTwoQuot H (F₂ ⊔ pCoreOf 2 H)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨θ, hθs, hθk⟩ := P.θ₂
  refine imageOTwoQuot_equiv P.F₂_le θ hθs fun f => ?_
  have h : θ f = 1 ↔ f ∈ θ.ker := MonoidHom.mem_ker.symm
  rw [h, hθk, Subgroup.mem_subgroupOf, P.cSecIn_F₂_eq]
  exact ⟨fun h => h.2, fun h => ⟨f.2, h⟩⟩

include P in
theorem conjSub_eq_of_mem_B₂ {g : G} (hg : g ∈ B) : conjSub g X₂ = X₂ := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro h
    have := P.B_norm₂ g hg _ h
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at this
  · intro h
    have := P.B_norm₂ g⁻¹ (B.inv_mem hg) x h
    simpa using this

include P in
theorem conjSub_eq_of_mem_B₁ {g : G} (hg : g ∈ B) : conjSub g X₁ = X₁ := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro h
    have := P.B_norm₁ g hg _ h
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at this
  · intro h
    have := P.B_norm₁ g⁻¹ (B.inv_mem hg) x h
    simpa using this

include P in
theorem conjSub_H₁ [Finite G] {g : G} (hg : g ∈ H) :
    conjSub g (F₁ ⊔ pCoreOf 2 H) = F₁ ⊔ pCoreOf 2 H ∨
      conjSub g (F₁ ⊔ pCoreOf 2 H) = F₂ ⊔ pCoreOf 2 H := by
  by_cases hgB : g ∈ B
  · left
    rw [← P.C₂_eq, P.conjSub_cSecIn hg, P.conjSub_eq_of_mem_B₂ hgB]
  · right
    rw [← P.C₂_eq, P.conjSub_cSecIn hg, P.conjSub_eq_of_not_mem' hg hgB, P.C₁_eq]

include P in
theorem conjSub_H₂ [Finite G] {g : G} (hg : g ∈ H) :
    conjSub g (F₂ ⊔ pCoreOf 2 H) = F₂ ⊔ pCoreOf 2 H ∨
      conjSub g (F₂ ⊔ pCoreOf 2 H) = F₁ ⊔ pCoreOf 2 H := by
  by_cases hgB : g ∈ B
  · left
    rw [← P.C₁_eq, P.conjSub_cSecIn hg, P.conjSub_eq_of_mem_B₁ hgB]
  · right
    rw [← P.C₁_eq, P.conjSub_cSecIn hg, P.conjSub_eq_of_not_mem hg hgB, P.C₂_eq]

include P in
theorem four_le_of_both [Finite G] {X : Subgroup G} (hXB : X ≤ B) {x₁ x₂ n₁ n₂ : G} (hx₁ : x₁ ∈ X)
    (hx₂ : x₂ ∈ X) (hn₁ : n₁ ∈ X₁) (hn₂ : n₂ ∈ X₂) (hc₁ : x₁ * n₁ * x₁⁻¹ * n₁⁻¹ ∉ L)
    (hc₂ : x₂ * n₂ * x₂⁻¹ * n₂⁻¹ ∉ L) :
    4 ≤ (fixMod X L N P.N_abelian P.L_le_N).relIndex N := by
  have hN2 : IsPGroup 2 N :=
    (F7.isPGroup_of_isElemAbelian P.elemAbelian).to_le P.step.1.1
  have h₃ : n₁ ∉ fixMod X L N P.N_abelian P.L_le_N := fun h => hc₁ (h.2 x₁ hx₁)
  have h₄ : n₂ ∉ fixMod X L N P.N_abelian P.L_le_N := fun h => hc₂ (h.2 x₂ hx₂)
  have h₅ : n₁ * n₂⁻¹ ∉ fixMod X L N P.N_abelian P.L_le_N := by
    intro h
    have hL := h.2 x₁ hx₁
    have hx₁H : x₁ ∈ H := P.B_le (hXB hx₁)
    rw [P.conj_comm_mul hx₁H (P.X₁_le hn₁) (N.inv_mem (P.X₂_le hn₂) : n₂⁻¹ ∈ N)] at hL
    have haX₁ : x₁ * n₁ * x₁⁻¹ * n₁⁻¹ ∈ X₁ :=
      X₁.mul_mem (P.B_norm₁ x₁ (hXB hx₁) n₁ hn₁) (X₁.inv_mem hn₁)
    have hbX₂ : x₁ * n₂⁻¹ * x₁⁻¹ * n₂⁻¹⁻¹ ∈ X₂ :=
      X₂.mul_mem (P.B_norm₂ x₁ (hXB hx₁) _ (X₂.inv_mem hn₂)) (X₂.inv_mem (X₂.inv_mem hn₂))
    have haX₂ : x₁ * n₁ * x₁⁻¹ * n₁⁻¹ ∈ X₂ := by
      have h1 := X₂.mul_mem (P.L_le₂ hL) (X₂.inv_mem hbX₂)
      rwa [mul_inv_cancel_right] at h1
    have : x₁ * n₁ * x₁⁻¹ * n₁⁻¹ ∈ X₁ ⊓ X₂ := ⟨haX₁, haX₂⟩
    rw [P.inf_eq] at this
    exact hc₁ this
  exact four_le_relIndex_of_three hN2 (P.X₁_le hn₁) (P.X₂_le hn₂) h₃ h₄ h₅

include P in
theorem delta_le_aux [Finite G] {A : Subgroup G} (hAH : A ≤ H)
    (hfix : (fixMod A L N P.N_abelian P.L_le_N).relIndex N ≤ 2) :
    A ≤ F₁ ⊔ pCoreOf 2 H ∨ A ≤ F₂ ⊔ pCoreOf 2 H := by
  have hAB : A ≤ B := by
    intro σ hσ
    by_contra hσB
    have h4 := four_le_relIndex_of_not_mem_base P.elemAbelian P.step hAH P.L_le₁ P.X₁_le P.card₁
      P.B_normal P.B_norm₁ P.F₁_le_B P.irr₁ (fun σ hσ h => P.stab hσ h) hσ hσB
    have hfixU : fixU H U L N A P.elemAbelian P.step = fixMod A L N P.N_abelian P.L_le_N := rfl
    rw [hfixU] at h4
    omega
  by_contra hcon
  push Not at hcon
  obtain ⟨hA₁, hA₂⟩ := hcon
  obtain ⟨x₂, hx₂A, hx₂⟩ := IsConcreteLE.not_le_iff_exists.mp hA₁
  obtain ⟨x₁, hx₁A, hx₁⟩ := IsConcreteLE.not_le_iff_exists.mp hA₂
  rw [← P.C₂_eq] at hx₂
  rw [← P.C₁_eq] at hx₁
  have hn₂ : ∃ n₂ ∈ X₂, x₂ * n₂ * x₂⁻¹ * n₂⁻¹ ∉ L := by
    by_contra h
    push Not at h
    exact hx₂ (P.mem_C₂.mpr ⟨hAB hx₂A, h⟩)
  have hn₁ : ∃ n₁ ∈ X₁, x₁ * n₁ * x₁⁻¹ * n₁⁻¹ ∉ L := by
    by_contra h
    push Not at h
    exact hx₁ (P.mem_C₁.mpr ⟨hAB hx₁A, h⟩)
  obtain ⟨n₂, hn₂X, hc₂⟩ := hn₂
  obtain ⟨n₁, hn₁X, hc₁⟩ := hn₁
  have h4 := P.four_le_of_both hAB hx₁A hx₂A hn₁X hn₂X hc₁ hc₂
  omega

end PairStep

theorem fixSecIn_eq_fixMod {A L N : Subgroup G} (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hLN : L ≤ N) : fixSecIn A L N = fixMod A L N hab hLN :=
  le_antisymm ((Subgroup.closure_le _).mpr fun _ hx => hx) fun _ hx => Subgroup.subset_closure hx

theorem delta_le_of [Finite G] {T M V H L N B F₁ F₂ X₁ X₂ : Subgroup G}
    (P : PairStep H (conjClosure V H) L N B F₁ F₂ X₁ X₂) (hnc : ¬ IsCentralStep H L N)
    (hC : Concl319 T M V H True) (hT : IsSylowTwoOf T H)
    (hord : ∀ A ∈ deltaSet H V, (A ⊓ pCoreOf 2 H).relIndex A = 2) :
    ∀ A ∈ deltaSet H V, A ≤ F₁ ⊔ pCoreOf 2 H ∨ A ≤ F₂ ⊔ pCoreOf 2 H := by
  intro A hA
  have hAord := hord A hA
  obtain ⟨h, hh, hmin⟩ := S152N.exists_conj_isMinOffender hT hA hAord
  have hA'H : cjSub h A ≤ H := cjSub_le (Subgroup.le_normalizer hh) hA.1.1
  obtain ⟨-, hcount⟩ := hC.count_four _ hmin L N P.step hnc
  have hQ := S152N.cjSub_pCoreOf hh
  have h4 : cjSub h A ⊓ pCoreOf 2 H = cjSub h (A ⊓ pCoreOf 2 H) := by
    rw [B2F.cjSub_inf, hQ]
  have h3 : (cjSub h A ⊓ pCoreOf 2 H).relIndex (cjSub h A) = 2 := by
    rw [h4]
    exact (Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj h).toMonoidHom)
      (A ⊓ pCoreOf 2 H) A (MulAut.conj h).injective).trans hAord
  have hcard : 2 * Nat.card ↥(cjSub h A ⊓ pCoreOf 2 H) = Nat.card ↥(cjSub h A) := by
    have := Subgroup.relIndex_mul_card (cjSub h A ⊓ pCoreOf 2 H) (cjSub h A)
    rw [h3, inf_eq_left.mpr inf_le_left] at this
    exact this
  rw [fixSecIn_eq_fixMod P.N_abelian P.L_le_N, ← hcard] at hcount
  have hpos : 0 < Nat.card ↥(cjSub h A ⊓ pCoreOf 2 H) := Nat.card_pos
  have hfixN : 2 * Nat.card ↥(fixMod (cjSub h A) L N P.N_abelian P.L_le_N) = Nat.card ↥N := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← hcount]
    ring
  have hfix : (fixMod (cjSub h A) L N P.N_abelian P.L_le_N).relIndex N ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card (fixMod (cjSub h A) L N P.N_abelian P.L_le_N) N
    rw [inf_eq_left.mpr fixMod_le] at h1
    have hpos' : 0 < Nat.card ↥(fixMod (cjSub h A) L N P.N_abelian P.L_le_N) := Nat.card_pos
    have : (fixMod (cjSub h A) L N P.N_abelian P.L_le_N).relIndex N = 2 := by
      apply Nat.eq_of_mul_eq_mul_right hpos'
      rw [h1, ← hfixN]
    exact this.le
  have hA' : A = conjSub h⁻¹ (conjSub h A) := (conjSub_conjSub_inv h A).symm
  have hcj : cjSub h A = conjSub h A := rfl
  rw [hcj] at hA'H hfix
  rcases P.delta_le_aux hA'H hfix with h1 | h1
  · have h5 : A ≤ conjSub h⁻¹ (F₁ ⊔ pCoreOf 2 H) := hA' ▸ conjSub_mono h⁻¹ h1
    rcases P.conjSub_H₁ (H.inv_mem hh) with h6 | h6
    · left
      rwa [h6] at h5
    · right
      rwa [h6] at h5
  · have h5 : A ≤ conjSub h⁻¹ (F₂ ⊔ pCoreOf 2 H) := hA' ▸ conjSub_mono h⁻¹ h1
    rcases P.conjSub_H₂ (H.inv_mem hh) with h6 | h6
    · right
      rwa [h6] at h5
    · left
      rwa [h6] at h5

end S152Fin

open CFSG.Quasithin.S152N in
theorem stagePair152_of
    (h15112 : StageLemma15112) (h15208 : StageLemma15208)
    (hord : Input15209Order) : StagePair152 := by
  intro G _ _ T Mc M hs H hH
  obtain ⟨φ⟩ := h15208 G T Mc M hs H hH
  have hc := (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
  have hTsyl := isSylowTwoOf_hStar hs hH
  obtain ⟨L, N, hs', hnc, -⟩ := S152Fin.exists_noncentral_of_series hc.chief (by norm_num : 1 ≤ 2)
  have hshape := hc.shape trivial L N hs' hnc
  obtain ⟨B, F₁, F₂, X₁, X₂, P⟩ := S152Fin.pairStep_of_shape hc.elemAbelian hs' ⟨φ⟩ hshape
  refine ⟨F₁ ⊔ pCoreOf 2 H, F₂ ⊔ pCoreOf 2 H, ?_⟩
  exact
    { le₁ := ⟨le_sup_right, sup_le P.F₁_le (pCoreOf_le 2 H)⟩
      le₂ := ⟨le_sup_right, sup_le P.F₂_le (pCoreOf_le 2 H)⟩
      iso₁ := P.iso₁
      iso₂ := P.iso₂
      comm := fun a ha b hb => P.comm_H ha hb
      inf_eq := P.inf_H
      swap := P.swap
      delta_le := S152Fin.delta_le_of P hnc hc hTsyl (hord G T Mc M hs H hH) }

end CFSG.Quasithin
