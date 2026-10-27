module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeModGrp
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeModule

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

section Module

variable {Γ Ω : Type*} [Group Γ] [Finite Γ] [Fintype Ω]

theorem nineThree_perm_fixed (σ : Γ →* Equiv.Perm Ω) (hodd : Odd (Fintype.card Ω))
    (htrans : ∀ a b : Ω, ∃ γ : Γ, σ γ a = b) (v : Ω) (Q : Subgroup Γ) (hQ : IsPGroup 2 Q)
    (hQv : ∀ q ∈ Q, σ q v = v) (hQt : ∀ a b : Ω, a ≠ v → b ≠ v → ∃ q ∈ Q, σ q a = b)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Γ →* LinearMap.GeneralLinearGroup (ZMod 2) M) (m : Ω → M)
    (hm : ∀ γ ω, (ρ γ : M →ₗ[ZMod 2] M) (m ω) = m (σ γ ω))
    (hspan : Submodule.span (ZMod 2) (Set.range m) = ⊤) (hne : ∃ a b, m a ≠ m b)
    (f : Ω → ZMod 2)
    (hf : ∀ q ∈ Q, (ρ q : M →ₗ[ZMod 2] M) (Fintype.linearCombination (ZMod 2) m f) =
      Fintype.linearCombination (ZMod 2) m f) :
    ∀ q ∈ Q, ∀ ω, f (σ q ω) = f ω := by
  classical
  obtain ⟨a, b, hab⟩ := hne
  let φ : (Ω → ZMod 2) →ₗ[ZMod 2] M := Fintype.linearCombination (ZMod 2) m
  have hφ : ∀ (γ : Γ) (f : Ω → ZMod 2),
      φ (fun ω => f ((σ γ).symm ω)) = (ρ γ : M →ₗ[ZMod 2] M) (φ f) := by
    intro γ f
    simp only [φ, Fintype.linearCombination_apply, map_sum, map_smul, hm]
    have := Equiv.sum_comp (σ γ) (fun i => f ((σ γ).symm i) • m i)
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm
  have hKinv : ∀ γ : Γ, ∀ f ∈ LinearMap.ker φ,
      (fun ω => f ((σ γ).symm ω)) ∈ LinearMap.ker φ := by
    intro γ f hf
    rw [LinearMap.mem_ker] at hf ⊢
    rw [hφ, hf, map_zero]
  have hP : (Pi.single a 1 + Pi.single b 1 : Ω → ZMod 2) ∈ nineThreeEven Ω := by
    show ∑ ω, (Pi.single a 1 + Pi.single b 1 : Ω → ZMod 2) ω = 0
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
    simp
    decide
  have hnotK : (Pi.single a 1 + Pi.single b 1 : Ω → ZMod 2) ∉ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, map_add, Fintype.linearCombination_apply_single,
      Fintype.linearCombination_apply_single, one_smul, one_smul]
    intro h
    exact hab ((eq_neg_of_add_eq_zero_left h).trans (ZModModule.neg_eq_self _))
  have hK : LinearMap.ker φ = ⊥ ∨ LinearMap.ker φ = nineThreeConst Ω := by
    rcases nineThree_perm_trichotomy σ hodd htrans v Q hQ hQt _ hKinv with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (by rw [h]; exact hP) hnotK
    · exact absurd (by rw [h]; exact Submodule.mem_top) hnotK
  have hker0 : ∀ g ∈ LinearMap.ker φ, g v = 0 → g = 0 := by
    intro g hg hgv
    rcases hK with h | h
    · rw [h, Submodule.mem_bot] at hg; exact hg
    · rw [h] at hg
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hg
      have : c = 0 := by simpa using hgv
      rw [this, zero_smul]
  intro q hq ω
  have h1 : (fun ω => f ((σ q).symm ω)) - f ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, map_sub, hφ, hf q hq, sub_self]
  have hsv : (σ q).symm v = v := (Equiv.symm_apply_eq _).2 (hQv q hq).symm
  have h2 : ((fun ω => f ((σ q).symm ω)) - f) v = 0 := by
    simp [hsv]
  have h3 := hker0 _ h1 h2
  have := congrFun h3 (σ q ω)
  simp only [Pi.sub_apply, Equiv.symm_apply_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this.symm

end Module

section Group

variable {G : Type} [Group G] [Finite G]

theorem nineThree_group_not_fixed {W W₀ L Q V : Subgroup G} {Δ : Set (Subgroup G)}
    (hW : IsElemAbelian 2 W) (hW₀ : W₀ ≤ W)
    (hLW : L ≤ normalizer (W : Set G)) (hLW₀ : L ≤ normalizer (W₀ : Set G))
    (hΔW : ∀ B ∈ Δ, B ≤ W) (hgen : ⨆ B ∈ Δ, B = W)
    (hperm : ∀ B ∈ Δ, ∀ l ∈ L, conjSubgroup B l ∈ Δ) (hodd : Odd (Nat.card Δ))
    (htrans : ∀ B ∈ Δ, ∀ B' ∈ Δ, ∃ l ∈ L, conjSubgroup B l = B')
    (hidx : ∀ B ∈ Δ, (B ⊓ W₀).relIndex B = 2)
    (hnc : ∃ B ∈ Δ, ∃ B' ∈ Δ, ¬ B ≤ B' ⊔ W₀)
    (hV : V ∈ Δ) (hQL : Q ≤ L) (hQ : IsPGroup 2 Q) (hQV : ∀ q ∈ Q, conjSubgroup V q = V)
    (hQt : ∀ B ∈ Δ, B ≠ V → ∀ B' ∈ Δ, B' ≠ V → ∃ q ∈ Q, conjSubgroup B q = B')
    (h6 : 6 ≤ Nat.card Δ)
    {B₁ B₂ B₃ B₄ : Subgroup G} (h₁ : B₁ ∈ Δ) (h₂ : B₂ ∈ Δ) (h₃ : B₃ ∈ Δ) (h₄ : B₄ ∈ Δ)
    (h₁V : B₁ ≠ V) (h₂V : B₂ ≠ V) (h₃V : B₃ ≠ V) (h₄V : B₄ ≠ V)
    (h₁₂ : B₁ ≠ B₂) (h₁₃ : B₁ ≠ B₃) (h₁₄ : B₁ ≠ B₄) (h₂₃ : B₂ ≠ B₃) (h₂₄ : B₂ ≠ B₄)
    (h₃₄ : B₃ ≠ B₄)
    {c₁ c₂ c₃ c₄ : G} (hc₁ : c₁ ∈ B₁) (hc₂ : c₂ ∈ B₂) (hc₃ : c₃ ∈ B₃) (hc₄ : c₄ ∈ B₄)
    (hc₁W : c₁ ∉ W₀) (hc₂W : c₂ ∉ W₀) (hc₃W : c₃ ∉ W₀) (hc₄W : c₄ ∉ W₀) :
    ∃ q ∈ Q, ⁅c₁ * c₂ * c₃ * c₄, q⁆ ∉ W₀ := by
  classical
  obtain ⟨M, _, _, ρ, π, hsurj, hker, hequiv⟩ := nineThree_exists_rep hW hW₀ hLW hLW₀
  haveI : Finite M := Finite.of_surjective π hsurj
  haveI : Fintype ↥Δ := Fintype.ofFinite _
  let σ : ↥L →* Equiv.Perm ↥Δ :=
    { toFun := fun l =>
        { toFun := fun B => ⟨conjSubgroup B.1 (l : G)⁻¹, hperm B.1 B.2 _ (L.inv_mem l.2)⟩
          invFun := fun B => ⟨conjSubgroup B.1 (l : G), hperm B.1 B.2 _ l.2⟩
          left_inv := fun B => Subtype.ext (by
            show conjSubgroup (conjSubgroup B.1 (l : G)⁻¹) (l : G) = B.1
            rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
              CFSG.Quasithin.conjSubgroup_one])
          right_inv := fun B => Subtype.ext (by
            show conjSubgroup (conjSubgroup B.1 (l : G)) (l : G)⁻¹ = B.1
            rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
              CFSG.Quasithin.conjSubgroup_one]) }
      map_one' := Equiv.ext fun B => Subtype.ext (by
        show conjSubgroup B.1 ((1 : ↥L) : G)⁻¹ = B.1
        rw [Subgroup.coe_one, inv_one, CFSG.Quasithin.conjSubgroup_one])
      map_mul' := fun l₁ l₂ => Equiv.ext fun B => Subtype.ext (by
        show conjSubgroup B.1 ((l₁ * l₂ : ↥L) : G)⁻¹ =
          conjSubgroup (conjSubgroup B.1 (l₂ : G)⁻¹) (l₁ : G)⁻¹
        rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, Subgroup.coe_mul, mul_inv_rev]) }
  have hσ : ∀ (l : ↥L) (B : ↥Δ), (σ l B).1 = conjSubgroup B.1 (l : G)⁻¹ := fun l B => rfl
  have hex : ∀ B : ↥Δ, ∃ b : G, b ∈ B.1 ∧ b ∉ W₀ := by
    intro B
    by_contra hcon
    push Not at hcon
    have h1 : (B.1 ⊓ W₀).relIndex B.1 = 1 :=
      Subgroup.relIndex_eq_one.2 (fun x hx => ⟨hx, hcon x hx⟩)
    rw [hidx B.1 B.2] at h1
    omega
  choose b hbB hbW using hex
  let m : ↥Δ → M := fun B => π (Additive.ofMul ⟨b B, hΔW B.1 B.2 (hbB B)⟩)
  have huniq : ∀ (B : ↥Δ) (c : G) (hc : c ∈ B.1) (hcW : c ∉ W₀),
      π (Additive.ofMul ⟨c, hΔW B.1 B.2 hc⟩) = m B := by
    intro B c hc hcW
    have hind : ((B.1 ⊓ W₀).subgroupOf B.1).index = 2 := hidx B.1 B.2
    have hx : (⟨b B, hbB B⟩⁻¹ : ↥B.1) ∉ (B.1 ⊓ W₀).subgroupOf B.1 := by
      intro h
      apply hbW B
      have h' : (b B)⁻¹ ∈ W₀ := (h : ((b B)⁻¹ : G) ∈ B.1 ⊓ W₀).2
      simpa using W₀.inv_mem h'
    have hy : (⟨c, hc⟩ : ↥B.1) ∉ (B.1 ⊓ W₀).subgroupOf B.1 := fun h => hcW h.2
    have hxy := (Subgroup.mul_mem_iff_of_index_two hind).2 (iff_of_false hx hy)
    have hW0 : (b B)⁻¹ * c ∈ W₀ := (hxy : (b B)⁻¹ * c ∈ B.1 ⊓ W₀).2
    have h1 : (⟨c, hΔW B.1 B.2 hc⟩ : ↥W) =
        ⟨b B, hΔW B.1 B.2 (hbB B)⟩ * ⟨(b B)⁻¹ * c, hW₀ hW0⟩ := Subtype.ext (by simp)
    rw [h1, ofMul_mul, map_add, (hker ⟨(b B)⁻¹ * c, hW₀ hW0⟩).2 hW0, add_zero]
  have hm : ∀ (l : ↥L) (B : ↥Δ), (ρ l : M →ₗ[ZMod 2] M) (m B) = m (σ l B) := by
    intro l B
    have hcW' : (l : G) * b B * (l : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hLW l.2) (b B)).mp (hΔW B.1 B.2 (hbB B))
    have hcB : (l : G) * b B * (l : G)⁻¹ ∈ (σ l B).1 := by
      rw [hσ, mem_conjSubgroup_iff]
      simpa [mul_assoc] using hbB B
    have hcW : (l : G) * b B * (l : G)⁻¹ ∉ W₀ := by
      intro h
      exact hbW B ((Subgroup.mem_normalizer_iff.mp (hLW₀ l.2) (b B)).2 h)
    rw [← huniq (σ l B) _ hcB hcW]
    exact (hequiv l ⟨b B, hΔW B.1 B.2 (hbB B)⟩ ⟨_, hcW'⟩ rfl).symm
  have hspan : Submodule.span (ZMod 2) (Set.range m) = ⊤ := by
    let T : Subgroup ↥W :=
      { carrier := {w | π (Additive.ofMul w) ∈ Submodule.span (ZMod 2) (Set.range m)}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, ofMul_mul, map_add]
          exact Submodule.add_mem _ ha hb
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq, ofMul_inv, map_neg]
          exact Submodule.neg_mem _ ha }
    have hBT : ∀ B ∈ Δ, B ≤ T.map W.subtype := by
      intro B hB x hx
      refine ⟨⟨x, hΔW B hB hx⟩, ?_, rfl⟩
      show π (Additive.ofMul ⟨x, hΔW B hB hx⟩) ∈ Submodule.span (ZMod 2) (Set.range m)
      by_cases hxW : x ∈ W₀
      · rw [(hker ⟨x, hΔW B hB hx⟩).2 hxW]
        exact Submodule.zero_mem _
      · rw [huniq ⟨B, hB⟩ x hx hxW]
        exact Submodule.subset_span ⟨⟨B, hB⟩, rfl⟩
    have hWT : W ≤ T.map W.subtype := by
      have h := iSup₂_le (f := fun B (_ : B ∈ Δ) => B) hBT
      rwa [hgen] at h
    rw [eq_top_iff]
    intro v _
    obtain ⟨w, rfl⟩ := hsurj v
    obtain ⟨t, ht, htw⟩ := hWT (Additive.toMul w).2
    have : t = Additive.toMul w := Subtype.ext htw
    rw [this] at ht
    exact ht
  have hne : ∃ a b, m a ≠ m b := by
    obtain ⟨B, hB, B', hB', hnot⟩ := hnc
    refine ⟨⟨B, hB⟩, ⟨B', hB'⟩, fun heq => hnot ?_⟩
    intro x hx
    by_cases hxW : x ∈ W₀
    · exact Subgroup.mem_sup_right hxW
    · have h1 := huniq ⟨B, hB⟩ x hx hxW
      have h2 : π (Additive.ofMul ⟨x, hΔW B hB hx⟩) =
          π (Additive.ofMul ⟨b ⟨B', hB'⟩, hΔW B' hB' (hbB ⟨B', hB'⟩)⟩) := h1.trans heq
      have h3 : x * (b ⟨B', hB'⟩)⁻¹ ∈ W₀ := by
        have hxW' : (⟨x, hΔW B hB hx⟩ : ↥W) *
            (⟨b ⟨B', hB'⟩, hΔW B' hB' (hbB ⟨B', hB'⟩)⟩ : ↥W)⁻¹ =
            ⟨x * (b ⟨B', hB'⟩)⁻¹,
              W.mul_mem (hΔW B hB hx) (W.inv_mem (hΔW B' hB' (hbB ⟨B', hB'⟩)))⟩ :=
          rfl
        have := (hker ((⟨x, hΔW B hB hx⟩ : ↥W) *
            (⟨b ⟨B', hB'⟩, hΔW B' hB' (hbB ⟨B', hB'⟩)⟩ : ↥W)⁻¹)).1 (by
          rw [ofMul_mul, ofMul_inv, map_add, map_neg, h2, add_neg_cancel])
        exact this
      have : x = (x * (b ⟨B', hB'⟩)⁻¹) * b ⟨B', hB'⟩ := by simp
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h3)
        (Subgroup.mem_sup_left (hbB ⟨B', hB'⟩))
  have htr : ∀ a b : ↥Δ, ∃ γ : ↥L, σ γ a = b := by
    intro a b
    obtain ⟨l, hl, hlab⟩ := htrans a.1 a.2 b.1 b.2
    exact ⟨⟨l, hl⟩⁻¹, Subtype.ext (by
      rw [hσ]
      simpa using hlab)⟩
  have hodd' : Odd (Fintype.card ↥Δ) := by rwa [← Nat.card_eq_fintype_card]
  let Q' : Subgroup ↥L := Q.subgroupOf L
  have hQ' : IsPGroup 2 Q' := hQ.comap_subtype
  have hQv : ∀ q ∈ Q', σ q ⟨V, hV⟩ = ⟨V, hV⟩ := by
    intro q hq
    have hqQ : (q : G) ∈ Q := hq
    exact Subtype.ext (by
      rw [hσ]
      exact hQV _ (Q.inv_mem hqQ))
  have hQt' : ∀ a b : ↥Δ, a ≠ ⟨V, hV⟩ → b ≠ ⟨V, hV⟩ → ∃ q ∈ Q', σ q a = b := by
    intro a b ha hb
    obtain ⟨q, hq, hqab⟩ := hQt a.1 a.2 (fun h => ha (Subtype.ext h)) b.1 b.2
      (fun h => hb (Subtype.ext h))
    refine ⟨⟨(q : G)⁻¹, L.inv_mem (hQL hq)⟩, ?_, Subtype.ext ?_⟩
    · show (q : G)⁻¹ ∈ Q
      exact Q.inv_mem hq
    · rw [hσ]
      simpa using hqab
  by_contra hcon
  push Not at hcon
  have hyW : c₁ * c₂ * c₃ * c₄ ∈ W :=
    W.mul_mem (W.mul_mem (W.mul_mem (hΔW B₁ h₁ hc₁) (hΔW B₂ h₂ hc₂))
      (hΔW B₃ h₃ hc₃)) (hΔW B₄ h₄ hc₄)
  let yW : ↥W := ⟨c₁ * c₂ * c₃ * c₄, hyW⟩
  have hπy : π (Additive.ofMul yW) =
      m ⟨B₁, h₁⟩ + m ⟨B₂, h₂⟩ + m ⟨B₃, h₃⟩ + m ⟨B₄, h₄⟩ := by
    have hy : yW = (⟨c₁, hΔW B₁ h₁ hc₁⟩ : ↥W) * ⟨c₂, hΔW B₂ h₂ hc₂⟩ *
        ⟨c₃, hΔW B₃ h₃ hc₃⟩ * ⟨c₄, hΔW B₄ h₄ hc₄⟩ := Subtype.ext rfl
    rw [hy]
    simp only [ofMul_mul, map_add]
    rw [huniq ⟨B₁, h₁⟩ c₁ hc₁ hc₁W, huniq ⟨B₂, h₂⟩ c₂ hc₂ hc₂W,
      huniq ⟨B₃, h₃⟩ c₃ hc₃ hc₃W, huniq ⟨B₄, h₄⟩ c₄ hc₄ hc₄W]
  let f : ↥Δ → ZMod 2 := Pi.single ⟨B₁, h₁⟩ 1 + Pi.single ⟨B₂, h₂⟩ 1 +
    Pi.single ⟨B₃, h₃⟩ 1 + Pi.single ⟨B₄, h₄⟩ 1
  have hφf : Fintype.linearCombination (ZMod 2) m f =
      m ⟨B₁, h₁⟩ + m ⟨B₂, h₂⟩ + m ⟨B₃, h₃⟩ + m ⟨B₄, h₄⟩ := by
    simp only [f, map_add, Fintype.linearCombination_apply_single, one_smul]
  have hfixφ : ∀ q ∈ Q', (ρ q : M →ₗ[ZMod 2] M) (π (Additive.ofMul yW)) =
      π (Additive.ofMul yW) := by
    intro q hq
    have hqQ : (q : G) ∈ Q := hq
    have hc : ⁅(yW : G), (q : G)⁆ ∈ W₀ := hcon (q : G) hqQ
    have hcW : ⁅(yW : G), (q : G)⁆⁻¹ ∈ W := hW₀ (W₀.inv_mem hc)
    have hw'W : (q : G) * (yW : G) * (q : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hLW q.2) (yW : G)).mp yW.2
    have e1 := hequiv q yW ⟨_, hw'W⟩ rfl
    have e2 : (⟨(q : G) * (yW : G) * (q : G)⁻¹, hw'W⟩ : ↥W) =
        ⟨⁅(yW : G), (q : G)⁆⁻¹, hcW⟩ * yW :=
      Subtype.ext (by
        show (q : G) * (yW : G) * (q : G)⁻¹ = ⁅(yW : G), (q : G)⁆⁻¹ * (yW : G)
        rw [commutatorElement_def]
        group)
    rw [← e1, e2, ofMul_mul, map_add, (hker ⟨_, hcW⟩).2 (W₀.inv_mem hc), zero_add]
  have hf : ∀ q ∈ Q', (ρ q : M →ₗ[ZMod 2] M)
      (Fintype.linearCombination (ZMod 2) m f) = Fintype.linearCombination (ZMod 2) m f := by
    intro q hq
    simpa only [hφf, ← hπy] using hfixφ q hq
  have hfixed := nineThree_perm_fixed σ hodd' htr ⟨V, hV⟩ Q' hQ' hQv hQt' ρ m hm hspan hne f hf
  have hex5 : ∃ B ∈ Δ, B ∉ ({V, B₁, B₂, B₃, B₄} : Set (Subgroup G)) := by
    by_contra hno
    push Not at hno
    have hsub : Δ ⊆ ({V, B₁, B₂, B₃, B₄} : Set (Subgroup G)) := fun B hB => hno B hB
    have hle : Δ.ncard ≤ ({V, B₁, B₂, B₃, B₄} : Set (Subgroup G)).ncard :=
      Set.ncard_le_ncard hsub
    have hT : ({V, B₁, B₂, B₃, B₄} : Set (Subgroup G)).ncard ≤ 5 := by
      have h4 : ({B₄} : Set (Subgroup G)).ncard ≤ 1 := by simp
      have h3 := Set.ncard_insert_le B₃ ({B₄} : Set (Subgroup G))
      have h2 := Set.ncard_insert_le B₂ (insert B₃ ({B₄} : Set (Subgroup G)))
      have h1 := Set.ncard_insert_le B₁ (insert B₂ (insert B₃ ({B₄} : Set (Subgroup G))))
      have h0 : ({V, B₁, B₂, B₃, B₄} : Set (Subgroup G)).ncard ≤
          (insert B₁ (insert B₂ (insert B₃ ({B₄} : Set (Subgroup G))))).ncard + 1 :=
        Set.ncard_insert_le V _
      omega
    have h6' : 6 ≤ Δ.ncard := h6
    omega
  obtain ⟨B, hB, hBnot⟩ := hex5
  have hBV : B ≠ V := fun h => hBnot (by rw [h]; simp)
  have hBB₁ : B ≠ B₁ := fun h => hBnot (by rw [h]; simp)
  have hBB₂ : B ≠ B₂ := fun h => hBnot (by rw [h]; simp)
  have hBB₃ : B ≠ B₃ := fun h => hBnot (by rw [h]; simp)
  have hBB₄ : B ≠ B₄ := fun h => hBnot (by rw [h]; simp)
  have hneq : ∀ {B' B'' : Subgroup G} (hB' : B' ∈ Δ) (hB'' : B'' ∈ Δ), B' ≠ B'' →
      (⟨B', hB'⟩ : ↥Δ) ≠ ⟨B'', hB''⟩ :=
    fun hB' hB'' h hh => h (congrArg Subtype.val hh)
  have hfB₁ : f ⟨B₁, h₁⟩ = 1 := by
    simp only [f, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (hneq h₁ h₂ h₁₂),
      Pi.single_eq_of_ne (hneq h₁ h₃ h₁₃), Pi.single_eq_of_ne (hneq h₁ h₄ h₁₄),
      add_zero, zero_add]
  have hfB : f ⟨B, hB⟩ = 0 := by
    simp only [f, Pi.add_apply, Pi.single_eq_of_ne (hneq hB h₁ hBB₁),
      Pi.single_eq_of_ne (hneq hB h₂ hBB₂), Pi.single_eq_of_ne (hneq hB h₃ hBB₃),
      Pi.single_eq_of_ne (hneq hB h₄ hBB₄), add_zero, zero_add]
  have hVB₁ : (⟨B₁, h₁⟩ : ↥Δ) ≠ ⟨V, hV⟩ := fun h => h₁V (congrArg Subtype.val h)
  have hVB : (⟨B, hB⟩ : ↥Δ) ≠ ⟨V, hV⟩ := fun h => hBV (congrArg Subtype.val h)
  obtain ⟨q, hq, hqB⟩ := hQt' ⟨B₁, h₁⟩ ⟨B, hB⟩ hVB₁ hVB
  have hqfix := hfixed q hq ⟨B₁, h₁⟩
  rw [hqB] at hqfix
  rw [hfB, hfB₁] at hqfix
  exact one_ne_zero hqfix.symm

end Group

end CFSG.LocalAnalysis.WeakClosure81
