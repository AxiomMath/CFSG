module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSetting
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSubgroup
public import CFSG.LocalAnalysis.WeakClosure81.Twelve

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

section Klein

theorem sum_eq_zero_of_klein_free {X V : Type*} [DecidableEq X] [AddCommMonoid V]
    (σ τ : Equiv.Perm X) (S : Finset X) (hσ : ∀ x ∈ S, σ x ∈ S) (hτ : ∀ x ∈ S, τ x ∈ S)
    (hσ2 : ∀ x, σ (σ x) = x) (hτ2 : ∀ x, τ (τ x) = x) (hστ : ∀ x, σ (τ x) = τ (σ x))
    (hσf : ∀ x ∈ S, σ x ≠ x) (hτf : ∀ x ∈ S, τ x ≠ x) (hστf : ∀ x ∈ S, σ (τ x) ≠ x)
    (f : X → V) (hf : ∀ x ∈ S, f x + f (σ x) + f (τ x) + f (σ (τ x)) = 0) :
    ∑ x ∈ S, f x = 0 := by
  classical
  have main : ∀ T : Finset X, (∀ x ∈ T, σ x ∈ T) → (∀ x ∈ T, τ x ∈ T) →
      (∀ x ∈ T, σ x ≠ x) → (∀ x ∈ T, τ x ≠ x) → (∀ x ∈ T, σ (τ x) ≠ x) →
      (∀ x ∈ T, f x + f (σ x) + f (τ x) + f (σ (τ x)) = 0) → ∑ x ∈ T, f x = 0 := by
    intro T
    induction T using Finset.strongInductionOn with
    | _ T ih =>
      intro hσT hτT hσfT hτfT hστfT hfT
      rcases T.eq_empty_or_nonempty with hT | ⟨x, hx⟩
      · rw [hT, Finset.sum_empty]
      · let O : Finset X := insert x (insert (σ x) (insert (τ x) {σ (τ x)}))
        have hxO : x ∈ O := by simp [O]
        have hOT : O ⊆ T := by
          intro y hy
          simp only [O, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl | rfl
          · exact hx
          · exact hσT x hx
          · exact hτT x hx
          · exact hσT (τ x) (hτT x hx)
        have hne1 : x ≠ σ x := (hσfT x hx).symm
        have hne2 : x ≠ τ x := (hτfT x hx).symm
        have hne3 : x ≠ σ (τ x) := (hστfT x hx).symm
        have hne23 : σ x ≠ τ x := by
          intro h
          exact hστfT x hx (by rw [← h, hσ2 x])
        have hne13 : σ x ≠ σ (τ x) := by
          intro h
          have h' : x = τ x := by
            have := congrArg σ h
            rwa [hσ2 x, hσ2 (τ x)] at this
          exact hτfT x hx h'.symm
        have hne24 : τ x ≠ σ (τ x) := by
          intro h
          exact hσfT (τ x) (hτT x hx) h.symm
        have hsumO : ∑ y ∈ O, f y = 0 := by
          have h1 : x ∉ insert (σ x) (insert (τ x) ({σ (τ x)} : Finset X)) := by
            simp [hne1, hne2, hne3]
          have h2 : σ x ∉ insert (τ x) ({σ (τ x)} : Finset X) := by
            simp [hne23, hne13]
          have h3 : τ x ∉ ({σ (τ x)} : Finset X) := by simp [hne24]
          dsimp only [O]
          rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
            Finset.sum_singleton]
          rw [← hfT x hx]
          abel
        have hOσ : ∀ y ∈ O, σ y ∈ O := by
          intro y hy
          simp only [O, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          rcases hy with rfl | rfl | rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl (hσ2 x)
          · exact Or.inr (Or.inr (Or.inr rfl))
          · exact Or.inr (Or.inr (Or.inl (hσ2 (τ x))))
        have hOτ : ∀ y ∈ O, τ y ∈ O := by
          intro y hy
          simp only [O, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          rcases hy with rfl | rfl | rfl | rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (hστ x).symm))
          · exact Or.inl (hτ2 x)
          · exact Or.inr (Or.inl (by rw [hστ x, hτ2 (σ x)]))
        have hσres : ∀ y ∈ T \ O, σ y ∈ T \ O := by
          intro y hy
          rw [Finset.mem_sdiff] at hy ⊢
          exact ⟨hσT y hy.1, fun hc => hy.2 (by rw [← hσ2 y]; exact hOσ (σ y) hc)⟩
        have hτres : ∀ y ∈ T \ O, τ y ∈ T \ O := by
          intro y hy
          rw [Finset.mem_sdiff] at hy ⊢
          exact ⟨hτT y hy.1, fun hc => hy.2 (by rw [← hτ2 y]; exact hOτ (τ y) hc)⟩
        have hrest : ∑ y ∈ T \ O, f y = 0 :=
          ih (T \ O) (Finset.sdiff_ssubset hOT ⟨x, hxO⟩) hσres hτres
            (fun y hy => hσfT y (Finset.mem_sdiff.mp hy).1)
            (fun y hy => hτfT y (Finset.mem_sdiff.mp hy).1)
            (fun y hy => hστfT y (Finset.mem_sdiff.mp hy).1)
            (fun y hy => hfT y (Finset.mem_sdiff.mp hy).1)
        have hsd := Finset.sum_sdiff (f := f) hOT
        rw [hrest, hsumO, zero_add] at hsd
        exact hsd.symm
  exact main S hσ hτ hσf hτf hστf hf

end Klein

section PermMod

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] {n : ℕ}

private theorem b12_TwelvePermMod_isElemAbelian_of_le {G : Type} [Group G] {A B : Subgroup G}
    (h : A ≤ B) (hB : IsElemAbelian 2 B) : IsElemAbelian 2 A := by
  have hcommB : ∀ a b : ↥B, (a : G) * b = (b : G) * a := fun a b =>
    congrArg Subtype.val (hB.1.is_comm.comm a b)
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => hB.2 x (h hx)⟩
  exact hcommB ⟨a.1, h a.2⟩ ⟨b.1, h b.2⟩

theorem rankOne_free_off_borel
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {B A : Subgroup G}
    (hB : CFSG.Quasithin.IsBorelIn (⊤ : Subgroup G) B) (hAB : A ≤ B) (hA : IsElemAbelian 2 A)
    {g : G} (hg : g ∉ B) {a : G} (ha : a ∈ A) (hga : g⁻¹ * a * g ∈ B) : a = 1 := by
  by_contra hne
  let A' : Subgroup G := Subgroup.zpowers a
  have hA'B : A' ≤ B := Subgroup.zpowers_le.mpr ha |>.trans hAB
  have hA'elem : IsElemAbelian 2 A' :=
    b12_TwelvePermMod_isElemAbelian_of_le (Subgroup.zpowers_le.mpr ha) hA
  have hA'1 : A' ≠ ⊥ := fun h => hne (Subgroup.zpowers_eq_bot.mp h)
  have hg' : g⁻¹ ∉ B := fun h => hg (by simpa using B.inv_mem h)
  refine rankOne_conj_not_le_borel hG hB hA'B hA'elem hA'1 hg' ?_
  dsimp only [A']
  rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
  simpa [MulAut.conj_apply, inv_inv] using hga

theorem permMod_fixed (ρ : G →* LGL 2 V) {B A : Subgroup G} (hAB : A ≤ B)
    (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) (hq : RepQuad ρ A)
    (hfree : ∀ g : G, g ∉ B → ∀ a ∈ A, g⁻¹ * a * g ∈ B → a = 1) {z : V}
    (hz : ∀ b ∈ B, ρ b z = z) : ∀ g : G, ρ g z = z := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ B) := Fintype.ofFinite (G ⧸ B)
  let f : G ⧸ B → V := fun ω =>
    Quotient.liftOn' ω (fun g : G => ρ g z) (fun g₁ g₂ h => by
      have hmem : g₁⁻¹ * g₂ ∈ B := QuotientGroup.leftRel_apply.mp h
      have h2 : ρ g₂ z = ρ g₁ z := by
        conv_lhs => rw [show g₂ = g₁ * (g₁⁻¹ * g₂) from by group]
        rw [map_mul]
        change ρ g₁ (ρ (g₁⁻¹ * g₂) z) = ρ g₁ z
        rw [hz (g₁⁻¹ * g₂) hmem]
      exact h2.symm)
  have hf_mk : ∀ g : G, f ((g : G) : G ⧸ B) = ρ g z := fun g => rfl
  have hf_smul : ∀ (h : G) (ω : G ⧸ B), f (h • ω) = ρ h (f ω) := by
    intro h ω
    refine QuotientGroup.induction_on ω ?_
    intro g
    rw [show h • (g : G ⧸ B) = ((h * g : G) : G ⧸ B) from rfl, hf_mk, hf_mk]
    change ρ (h * g) z = ρ h (ρ g z)
    rw [map_mul]
    rfl
  have hcardA : 2 < Fintype.card ↥A := by
    have h := hA4
    rw [Nat.card_eq_fintype_card] at h
    omega
  obtain ⟨x₀, y₀, z₀, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hcardA
  have hex : ∃ a b : G, a ∈ A ∧ b ∈ A ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
    by_cases hx1 : (x₀ : G) = 1
    · exact ⟨(y₀ : G), (z₀ : G), y₀.2, z₀.2,
        fun hy1 => hxy (Subtype.ext (hx1.trans hy1.symm)),
        fun hz1 => hxz (Subtype.ext (hx1.trans hz1.symm)),
        fun hyz' => hyz (Subtype.ext hyz')⟩
    · by_cases hy1 : (y₀ : G) = 1
      · exact ⟨(x₀ : G), (z₀ : G), x₀.2, z₀.2, hx1,
          fun hz1 => hyz (Subtype.ext (hy1.trans hz1.symm)),
          fun hxz' => hxz (Subtype.ext hxz')⟩
      · exact ⟨(x₀ : G), (y₀ : G), x₀.2, y₀.2, hx1, hy1,
          fun hxy' => hxy (Subtype.ext hxy')⟩
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := hex
  have haa : a * a = 1 := by simpa [pow_two] using hA.2 a ha
  have hbb : b * b = 1 := by simpa [pow_two] using hA.2 b hb
  have hcomm : a * b = b * a := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hab1 : a * b ≠ 1 := by
    intro h
    have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [inv_eq_of_mul_eq_one_right haa] at h1
    exact hab h1.symm
  let ω₀ : G ⧸ B := ((1 : G) : G ⧸ B)
  let S : Finset (G ⧸ B) := Finset.univ.erase ω₀
  let σ : Equiv.Perm (G ⧸ B) := MulAction.toPerm a
  let τ : Equiv.Perm (G ⧸ B) := MulAction.toPerm b
  have hσ_eq : ∀ ω : G ⧸ B, σ ω = a • ω := fun ω => rfl
  have hτ_eq : ∀ ω : G ⧸ B, τ ω = b • ω := fun ω => rfl
  have hsmul_B : ∀ c ∈ B, c • ω₀ = ω₀ := by
    intro c hc
    change c • ((1 : G) : G ⧸ B) = ((1 : G) : G ⧸ B)
    rw [show c • ((1 : G) : G ⧸ B) = ((c * 1 : G) : G ⧸ B) from rfl, mul_one]
    exact QuotientGroup.eq.mpr (by simpa using B.inv_mem hc)
  have hfree_smul : ∀ c ∈ A, c ≠ 1 → ∀ ω ∈ S, c • ω ≠ ω := by
    intro c hc hc1 ω hω hfix
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
    have hgB : g ∉ B := by
      intro hg
      exact (Finset.mem_erase.mp hω).1 (by
        show (g : G ⧸ B) = ((1 : G) : G ⧸ B)
        rw [QuotientGroup.eq]
        simpa using B.inv_mem hg)
    have h1 : (g : G ⧸ B) = ((c * g : G) : G ⧸ B) := by
      have h2 : c • (g : G ⧸ B) = ((c * g : G) : G ⧸ B) := rfl
      rw [h2] at hfix
      exact hfix.symm
    have hmem : g⁻¹ * c * g ∈ B := by
      have := QuotientGroup.eq.mp h1
      simpa [mul_assoc] using this
    exact hc1 (hfree g hgB c hc hmem)
  have hσ : ∀ ω ∈ S, σ ω ∈ S := by
    intro ω hω
    rw [Finset.mem_erase] at hω ⊢
    refine ⟨?_, Finset.mem_univ _⟩
    intro hcon
    apply hω.1
    have h := congrArg (fun y => a⁻¹ • y) hcon
    rw [hσ_eq] at h
    simp only [← mul_smul, inv_mul_cancel, one_smul] at h
    rw [h]
    exact hsmul_B a⁻¹ (hAB (A.inv_mem ha))
  have hτ : ∀ ω ∈ S, τ ω ∈ S := by
    intro ω hω
    rw [Finset.mem_erase] at hω ⊢
    refine ⟨?_, Finset.mem_univ _⟩
    intro hcon
    apply hω.1
    have h := congrArg (fun y => b⁻¹ • y) hcon
    rw [hτ_eq] at h
    simp only [← mul_smul, inv_mul_cancel, one_smul] at h
    rw [h]
    exact hsmul_B b⁻¹ (hAB (A.inv_mem hb))
  have hσ2 : ∀ ω : G ⧸ B, σ (σ ω) = ω := by
    intro ω
    change a • (a • ω) = ω
    rw [← mul_smul, haa, one_smul]
  have hτ2 : ∀ ω : G ⧸ B, τ (τ ω) = ω := by
    intro ω
    change b • (b • ω) = ω
    rw [← mul_smul, hbb, one_smul]
  have hστ : ∀ ω : G ⧸ B, σ (τ ω) = τ (σ ω) := by
    intro ω
    change a • (b • ω) = b • (a • ω)
    rw [← mul_smul, ← mul_smul, hcomm]
  have hσf : ∀ ω ∈ S, σ ω ≠ ω := by
    intro ω hω
    rw [hσ_eq]
    exact hfree_smul a ha ha1 ω hω
  have hτf : ∀ ω ∈ S, τ ω ≠ ω := by
    intro ω hω
    rw [hτ_eq]
    exact hfree_smul b hb hb1 ω hω
  have hστf : ∀ ω ∈ S, σ (τ ω) ≠ ω := by
    intro ω hω
    have hst : σ (τ ω) = (a * b) • ω := by
      change a • (b • ω) = (a * b) • ω
      rw [mul_smul]
    rw [hst]
    exact hfree_smul (a * b) (A.mul_mem ha hb) hab1 ω hω
  have h2 : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from by decide, zero_smul]
  have hfour : ∀ v : V, v + ρ a v + ρ b v + ρ a (ρ b v) = 0 := by
    intro v
    have hw : ρ b v - v ∈ commSub (A.map ρ) :=
      Submodule.subset_span ⟨ρ b, Subgroup.mem_map_of_mem ρ hb, v, rfl⟩
    have hfixw : ρ a (ρ b v - v) = ρ b v - v :=
      (commSub_le_fixSub_of_quadratic (A := A.map ρ) hq hw)
        (ρ a) (Subgroup.mem_map_of_mem ρ ha)
    have hpre : ρ a (ρ b v) = ρ a v + ρ b v - v := by
      have h1 : ρ a (ρ b v) - ρ a v = ρ b v - v := by
        rw [← map_sub]
        exact hfixw
      have h3 : ρ a (ρ b v) = ρ b v - v + ρ a v := by
        rw [← h1, sub_add_cancel]
      rw [h3]
      abel
    rw [hpre]
    have heq : v + ρ a v + ρ b v + (ρ a v + ρ b v - v) =
        (v - v) + (ρ a v + ρ a v) + (ρ b v + ρ b v) := by abel
    rw [heq, sub_self, h2 (ρ a v), h2 (ρ b v)]
    abel
  have hf : ∀ ω ∈ S, f ω + f (σ ω) + f (τ ω) + f (σ (τ ω)) = 0 := by
    intro ω _
    have h1 : σ ω = a • ω := rfl
    have h2' : τ ω = b • ω := rfl
    have h3 : σ (τ ω) = a • (b • ω) := rfl
    rw [h1, h3, h2', hf_smul a ω, hf_smul b ω, hf_smul a (b • ω), hf_smul b ω]
    exact hfour (f ω)
  have hzero : ∑ ω ∈ S, f ω = 0 :=
    sum_eq_zero_of_klein_free σ τ S hσ hτ hσ2 hτ2 hστ hσf hτf hστf f hf
  have hsum : ∑ ω : G ⧸ B, f ω = z := by
    have h2' : f ω₀ + ∑ ω ∈ S, f ω = ∑ ω : G ⧸ B, f ω := by
      dsimp only [S]
      exact Finset.add_sum_erase Finset.univ f (Finset.mem_univ ω₀)
    rw [hzero, add_zero] at h2'
    rw [← h2']
    rw [show ω₀ = ((1 : G) : G ⧸ B) from rfl, hf_mk, map_one]
    rfl
  have hfixed : ∀ h : G, ρ h (∑ ω : G ⧸ B, f ω) = ∑ ω : G ⧸ B, f ω := by
    intro h
    calc ρ h (∑ ω : G ⧸ B, f ω) = ∑ ω : G ⧸ B, ρ h (f ω) :=
          map_sum (ρ h) f Finset.univ
      _ = ∑ ω : G ⧸ B, f (h • ω) := by
          refine Finset.sum_congr rfl (fun ω _ => ?_)
          exact (hf_smul h ω).symm
      _ = ∑ ω : G ⧸ B, f ω := by
          simpa only [MulAction.toPerm_apply] using Equiv.sum_comp (MulAction.toPerm h) f
  intro g
  calc ρ g z = ρ g (∑ ω : G ⧸ B, f ω) := by rw [hsum]
    _ = ∑ ω : G ⧸ B, f ω := hfixed g
    _ = z := hsum

end PermMod

end CFSG.LocalAnalysis.WeakClosure81
