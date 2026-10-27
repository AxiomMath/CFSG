module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.U3S1347J

public section

namespace CFSG.Quasithin.H13.U3

namespace L32Mod

open CFSG.Quasithin.H6

@[expose] def borelList : List Γ :=
  [1, tb1, tb2, tb1 * tb2, tb2 * tb1, tb1 * tb2 * tb1, tb2 * tb1 * tb2, tb1 * tb2 * tb1 * tb2]

theorem mem_borelList {t : Γ} (ht : t ∈ H6.borel) : t ∈ borelList := by
  rcases borel_words t ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [borelList]

theorem no_E8 : ∀ a ∈ borelList, ∀ b ∈ borelList, ∀ c ∈ borelList, a * a = 1 → a ≠ 1 →
    b * b = 1 → b ≠ 1 → a ≠ b → a * b = b * a → c * c = 1 → c * a = a * c → c * b = b * c →
    c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
  decide +kernel

theorem core_card :
    (Finset.univ.filter fun f : Fin 8 → ZMod 2 => f 0 = 0 ∧ ∑ i, f i = 0).card = 64 := by
  decide +kernel

theorem core_fix_one : ∀ g ∈ borelList, g * g = 1 → g ≠ 1 →
    (Finset.univ.filter fun f : Fin 8 → ZMod 2 =>
      (f 0 = 0 ∧ ∑ i, f i = 0) ∧ actF g f = f).card ≤ 16 := by
  decide +kernel

theorem core_fix_two : ∀ a ∈ borelList, ∀ b ∈ borelList, a * a = 1 → a ≠ 1 → b * b = 1 →
    b ≠ 1 → a ≠ b → a * b = b * a → (Finset.univ.filter fun f : Fin 8 → ZMod 2 =>
      (f 0 = 0 ∧ ∑ i, f i = 0) ∧ actF a f = f ∧ actF b f = f).card ≤ 8 := by
  decide +kernel

theorem borelList_mem : ∀ g ∈ borelList, g ∈ H6.borel := by
  decide +kernel

theorem sum_fix_one : ∀ g ∈ borelList, g * g = 1 → g ≠ 1 →
    (Finset.univ.filter fun p : V3 × V3 => g • p.1 = p.1 ∧ graph g • p.2 = p.2).card ≤ 16 := by
  decide +kernel

theorem sum_fix_two : ∀ a ∈ borelList, ∀ b ∈ borelList, a * a = 1 → a ≠ 1 → b * b = 1 →
    b ≠ 1 → a ≠ b → a * b = b * a → (Finset.univ.filter fun p : V3 × V3 =>
      (a • p.1 = p.1 ∧ graph a • p.2 = p.2) ∧ b • p.1 = p.1 ∧ graph b • p.2 = p.2).card ≤ 8 := by
  decide +kernel

section Fix

variable {M N : Type} [AddCommGroup M] [AddCommGroup N]

abbrev Fix (ρ : Γ →* AddMonoid.End M) (S : Set Γ) : Type := {m : M // ∀ x ∈ S, ρ x m = m}

theorem card_fix_of_iso {ρ : Γ →* AddMonoid.End M} {σ : Γ →* AddMonoid.End N} (f : N →+ M)
    (hf : Function.Bijective f) (hfe : ∀ g n, f (σ g n) = ρ g (f n)) (S : Set Γ) :
    Nat.card (Fix ρ S) = Nat.card (Fix σ S) := by
  symm
  refine Nat.card_congr ((Equiv.ofBijective f hf).subtypeEquiv fun n => ?_)
  constructor
  · intro h x hx
    show ρ x (f n) = f n
    rw [← hfe, h x hx]
  · intro h x hx
    apply hf.1
    rw [hfe]
    exact h x hx

theorem card_fix_mono [Finite M] (ρ : Γ →* AddMonoid.End M) {S S' : Set Γ} (h : S ⊆ S') :
    Nat.card (Fix ρ S') ≤ Nat.card (Fix ρ S) :=
  Nat.card_le_card_of_injective (fun m => ⟨m.1, fun x hx => m.2 x (h hx)⟩)
    fun a b hab => Subtype.ext (by
      have := congrArg Subtype.val hab
      exact this)

theorem noOffender_of [Finite M] (ρ : Γ →* AddMonoid.End M) (hM : Nat.card M = 64)
    (h1 : ∀ g ∈ borelList, g * g = 1 → g ≠ 1 → Nat.card (Fix ρ {g}) ≤ 16)
    (h2 : ∀ a ∈ borelList, ∀ b ∈ borelList, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → a ≠ b →
      a * b = b * a → Nat.card (Fix ρ {a, b}) ≤ 8)
    {A : Subgroup Γ} (hAT : A ≤ H6.borel) (hA : A ≠ ⊥) (hA2 : ∀ a ∈ A, a * a = 1) :
    Nat.card A * Nat.card (Fix ρ A) < Nat.card M := by
  obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hA2 x hx)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hA2 y hy)
    have h3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hA2 _ (A.mul_mem hx hy))
    rw [mul_inv_rev, hxi, hyi] at h3
    exact h3.symm
  have haL := mem_borelList (hAT haA)
  rw [hM]
  by_cases hb : ∃ b ∈ A, b ≠ 1 ∧ b ≠ a
  · obtain ⟨b, hbA, hb1, hba⟩ := hb
    have hbL := mem_borelList (hAT hbA)
    have hab := hcomm a haA b hbA
    have hsub : (A : Set Γ) ⊆ ((({1, a, b, a * b} : Finset Γ)) : Set Γ) := by
      intro c hc
      have hcL := mem_borelList (hAT hc)
      rcases no_E8 a haL b hbL c hcL (hA2 a haA) ha1' (hA2 b hbA) hb1 (fun h => hba h.symm)
        hab (hA2 c hc) (hcomm c hc a haA) (hcomm c hc b hbA) with h | h | h | h <;>
        simp [h]
    have hcardA : Nat.card A ≤ 4 := by
      calc Nat.card A = (A : Set Γ).ncard := Nat.card_coe_set_eq _
        _ ≤ ((({1, a, b, a * b} : Finset Γ)) : Set Γ).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = ({1, a, b, a * b} : Finset Γ).card := Set.ncard_coe_finset _
        _ ≤ 4 := Finset.card_le_four
    have hfix : Nat.card (Fix ρ A) ≤ 8 := by
      refine (card_fix_mono ρ (S := {a, b}) ?_).trans
        (h2 a haL b hbL (hA2 a haA) ha1' (hA2 b hbA) hb1 (fun h => hba h.symm) hab)
      intro x hx
      rcases hx with rfl | rfl
      · exact haA
      · exact hbA
    calc Nat.card A * Nat.card (Fix ρ A) ≤ 4 * 8 := Nat.mul_le_mul hcardA hfix
      _ < 64 := by norm_num
  · push Not at hb
    have hsub : (A : Set Γ) ⊆ ((({1, a} : Finset Γ)) : Set Γ) := by
      intro c hc
      by_cases hc1 : c = 1
      · simp [hc1]
      · simp [hb c hc hc1]
    have hcardA : Nat.card A ≤ 2 := by
      calc Nat.card A = (A : Set Γ).ncard := Nat.card_coe_set_eq _
        _ ≤ ((({1, a} : Finset Γ)) : Set Γ).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = ({1, a} : Finset Γ).card := Set.ncard_coe_finset _
        _ ≤ 2 := Finset.card_le_two
    have hfix : Nat.card (Fix ρ A) ≤ 16 := by
      refine (card_fix_mono ρ (S := {a}) ?_).trans (h1 a haL (hA2 a haA) ha1')
      intro x hx
      rw [Set.mem_singleton_iff.1 hx]
      exact haA
    calc Nat.card A * Nat.card (Fix ρ A) ≤ 2 * 16 := Nat.mul_le_mul hcardA hfix
      _ < 64 := by norm_num

theorem card_core : Nat.card Core = 64 := by
  rw [← core_card, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun f => mem_coreSub)

theorem card_fix_core_one (g : Γ) : Nat.card (Fix ρCore {g}) =
    (Finset.univ.filter fun f : Fin 8 → ZMod 2 =>
      (f 0 = 0 ∧ ∑ i, f i = 0) ∧ actF g f = f).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun c => ⟨c.1.1, mem_coreSub.1 c.1.2, congrArg Subtype.val (c.2 g rfl)⟩
      invFun := fun f => ⟨⟨f.1, mem_coreSub.2 f.2.1⟩, fun x hx => by
        rw [Set.mem_singleton_iff.1 hx]
        exact Subtype.ext f.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_fix_core_two (a b : Γ) : Nat.card (Fix ρCore {a, b}) =
    (Finset.univ.filter fun f : Fin 8 → ZMod 2 =>
      (f 0 = 0 ∧ ∑ i, f i = 0) ∧ actF a f = f ∧ actF b f = f).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun c => ⟨c.1.1, mem_coreSub.1 c.1.2, congrArg Subtype.val (c.2 a (Or.inl rfl)),
        congrArg Subtype.val (c.2 b (Or.inr rfl))⟩
      invFun := fun f => ⟨⟨f.1, mem_coreSub.2 f.2.1⟩, fun x hx => by
        rcases hx with rfl | hx
        · exact Subtype.ext f.2.2.1
        · rw [Set.mem_singleton_iff.1 hx]
          exact Subtype.ext f.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

abbrev ρSum : Γ →* AddMonoid.End (V3 × V3) := prodRep ρV (ρV.comp graph.toMonoidHom)

theorem card_fix_sum_one (g : Γ) : Nat.card (Fix ρSum {g}) =
    (Finset.univ.filter fun p : V3 × V3 => g • p.1 = p.1 ∧ graph g • p.2 = p.2).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
  simp only [Set.mem_singleton_iff, forall_eq]
  exact Prod.ext_iff

theorem card_fix_sum_two (a b : Γ) : Nat.card (Fix ρSum {a, b}) =
    (Finset.univ.filter fun p : V3 × V3 =>
      (a • p.1 = p.1 ∧ graph a • p.2 = p.2) ∧ b • p.1 = p.1 ∧ graph b • p.2 = p.2).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact and_congr Prod.ext_iff Prod.ext_iff

theorem card_sum : Nat.card (V3 × V3) = 64 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem noOffender_core {ρ : Γ →* AddMonoid.End M} (h : IsoMod ρ ρCore) {A : Subgroup Γ}
    (hAT : A ≤ H6.borel) (hA : A ≠ ⊥) (hA2 : ∀ a ∈ A, a * a = 1) :
    Nat.card A * Nat.card (Fix ρ A) < Nat.card M := by
  obtain ⟨f, hf, hfe⟩ := h
  have : Finite M := Finite.of_surjective f hf.2
  refine noOffender_of ρ ?_ (fun g hg hg2 hg1 => ?_) (fun a ha b hb ha2 ha1 hb2 hb1 hab hc => ?_)
    hAT hA hA2
  · rw [← card_core]
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  · rw [card_fix_of_iso f hf hfe, card_fix_core_one]
    exact core_fix_one g hg hg2 hg1
  · rw [card_fix_of_iso f hf hfe, card_fix_core_two]
    exact core_fix_two a ha b hb ha2 ha1 hb2 hb1 hab hc

theorem graph_mem_borelList {g : Γ} (hg : g ∈ borelList) : graph g ∈ borelList :=
  mem_borelList ((graph_mem_borel_iff g).2 (borelList_mem g hg))

theorem noOffender_core_graph {ρ : Γ →* AddMonoid.End M}
    (h : IsoMod (ρ.comp graph.toMonoidHom) ρCore) {A : Subgroup Γ} (hAT : A ≤ H6.borel)
    (hA : A ≠ ⊥) (hA2 : ∀ a ∈ A, a * a = 1) :
    Nat.card A * Nat.card (Fix ρ A) < Nat.card M := by
  obtain ⟨f, hf, hfe⟩ := h
  have : Finite M := Finite.of_surjective f hf.2
  have hfe' : ∀ g c, f ((ρCore.comp graph.toMonoidHom) g c) = ρ g (f c) := by
    intro g c
    have := hfe (graph g) c
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, graph_graph] at this
    exact this
  have hfix1 : ∀ g, Nat.card (Fix (ρCore.comp graph.toMonoidHom) {g}) =
      Nat.card (Fix ρCore {graph g}) := fun g =>
    Nat.card_congr (Equiv.subtypeEquivRight fun c => by
      simp only [Set.mem_singleton_iff, forall_eq]
      exact Iff.rfl)
  have hfix2 : ∀ a b, Nat.card (Fix (ρCore.comp graph.toMonoidHom) {a, b}) =
      Nat.card (Fix ρCore {graph a, graph b}) := fun a b =>
    Nat.card_congr (Equiv.subtypeEquivRight fun c => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
      exact Iff.rfl)
  have hinj : ∀ a b : Γ, graph a = graph b → a = b := fun a b h => graph.injective h
  refine noOffender_of ρ ?_ (fun g hg hg2 hg1 => ?_) (fun a ha b hb ha2 ha1 hb2 hb1 hab hc => ?_)
    hAT hA hA2
  · rw [← card_core]
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  · rw [card_fix_of_iso f hf hfe', hfix1, card_fix_core_one]
    refine core_fix_one _ (graph_mem_borelList hg) (by rw [← map_mul, hg2, map_one]) ?_
    intro h1
    exact hg1 (hinj g 1 (by rw [h1, map_one]))
  · rw [card_fix_of_iso f hf hfe', hfix2, card_fix_core_two]
    refine core_fix_two _ (graph_mem_borelList ha) _ (graph_mem_borelList hb)
      (by rw [← map_mul, ha2, map_one]) (fun h1 => ha1 (hinj a 1 (by rw [h1, map_one])))
      (by rw [← map_mul, hb2, map_one]) (fun h1 => hb1 (hinj b 1 (by rw [h1, map_one])))
      (fun h1 => hab (hinj a b h1)) (by rw [← map_mul, ← map_mul, hc])

theorem noOffender_sum {ρ : Γ →* AddMonoid.End M} (h : IsoMod ρ ρSum) {A : Subgroup Γ}
    (hAT : A ≤ H6.borel) (hA : A ≠ ⊥) (hA2 : ∀ a ∈ A, a * a = 1) :
    Nat.card A * Nat.card (Fix ρ A) < Nat.card M := by
  obtain ⟨f, hf, hfe⟩ := h
  have : Finite M := Finite.of_surjective f hf.2
  refine noOffender_of ρ ?_ (fun g hg hg2 hg1 => ?_) (fun a ha b hb ha2 ha1 hb2 hb1 hab hc => ?_)
    hAT hA hA2
  · rw [← card_sum]
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  · rw [card_fix_of_iso f hf hfe, card_fix_sum_one]
    exact sum_fix_one g hg hg2 hg1
  · rw [card_fix_of_iso f hf hfe, card_fix_sum_two]
    exact sum_fix_two a ha b hb ha2 ha1 hb2 hb1 hab hc

theorem isoMod_sum {ρ : Γ →* AddMonoid.End M} {U₁ U₂ : AddSubgroup M} (hsup : U₁ ⊔ U₂ = ⊤)
    (hinf : U₁ ⊓ U₂ = ⊥) (e₁ : ↥U₁ ≃+ V3) (he₁ : ∀ (g : Γ) (m : M) (hm : m ∈ U₁)
      (hgm : ρ g m ∈ U₁), e₁ ⟨ρ g m, hgm⟩ = g • e₁ ⟨m, hm⟩)
    (hinv₁ : ∀ g, ∀ m ∈ U₁, ρ g m ∈ U₁) (hinv₂ : ∀ g, ∀ m ∈ U₂, ρ g m ∈ U₂)
    (e₂ : ↥U₂ ≃+ V3) (he₂ : ∀ (g : Γ) (m : M) (hm : m ∈ U₂) (hgm : ρ g m ∈ U₂),
      e₂ ⟨ρ g m, hgm⟩ = graph g • e₂ ⟨m, hm⟩) :
    IsoMod ρ ρSum := by
  have h1 : ∀ g v, ((e₁.symm (g • v) : ↥U₁) : M) = ρ g (e₁.symm v) := by
    intro g v
    have := he₁ g (e₁.symm v) (e₁.symm v).2 (hinv₁ g _ (e₁.symm v).2)
    rw [show (⟨(e₁.symm v : M), (e₁.symm v).2⟩ : ↥U₁) = e₁.symm v from rfl,
      AddEquiv.apply_symm_apply] at this
    rw [← this, AddEquiv.symm_apply_apply]
  have h2 : ∀ g w, ((e₂.symm (graph g • w) : ↥U₂) : M) = ρ g (e₂.symm w) := by
    intro g w
    have := he₂ g (e₂.symm w) (e₂.symm w).2 (hinv₂ g _ (e₂.symm w).2)
    rw [show (⟨(e₂.symm w : M), (e₂.symm w).2⟩ : ↥U₂) = e₂.symm w from rfl,
      AddEquiv.apply_symm_apply] at this
    rw [← this, AddEquiv.symm_apply_apply]
  let f : V3 × V3 →+ M := (U₁.subtype.comp e₁.symm.toAddMonoidHom).coprod
    (U₂.subtype.comp e₂.symm.toAddMonoidHom)
  have hf : ∀ p : V3 × V3, f p = (e₁.symm p.1 : M) + (e₂.symm p.2 : M) := fun _ => rfl
  refine ⟨f, ⟨(injective_iff_map_eq_zero f).2 fun p hp => ?_, fun m => ?_⟩, fun g p => ?_⟩
  · rw [hf] at hp
    have hmem : (e₁.symm p.1 : M) ∈ U₁ ⊓ U₂ := by
      refine AddSubgroup.mem_inf.2 ⟨(e₁.symm p.1).2, ?_⟩
      have : (e₁.symm p.1 : M) = -(e₂.symm p.2 : M) := eq_neg_of_add_eq_zero_left hp
      rw [this]
      exact U₂.neg_mem (e₂.symm p.2).2
    rw [hinf, AddSubgroup.mem_bot] at hmem
    have hp2 : (e₂.symm p.2 : M) = 0 := by rw [hmem, zero_add] at hp; exact hp
    have ha : e₁.symm p.1 = 0 := Subtype.ext hmem
    have hb : e₂.symm p.2 = 0 := Subtype.ext hp2
    rw [AddEquiv.map_eq_zero_iff] at ha hb
    exact Prod.ext ha hb
  · have hm : m ∈ U₁ ⊔ U₂ := hsup ▸ AddSubgroup.mem_top m
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hm
    refine ⟨(e₁ ⟨a, ha⟩, e₂ ⟨b, hb⟩), ?_⟩
    rw [hf, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  · rw [hf, hf, map_add]
    show ((e₁.symm (g • p.1) : ↥U₁) : M) + ((e₂.symm (graph g • p.2) : ↥U₂) : M) = _
    rw [h1, h2]

end Fix

end L32Mod

end CFSG.Quasithin.H13.U3
