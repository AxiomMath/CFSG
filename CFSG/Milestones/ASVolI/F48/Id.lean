module

public import CFSG.Milestones.ASVolI.F48.G2

public section

namespace CFSG.ASVolI

@[expose] def burnsideF48_img {X E : Type} [Group X] [Group E] {Gp : Subgroup E} (ε : X ≃* ↥Gp)
    (Q : Subgroup X) : Subgroup E :=
  (Q.map ε.toMonoidHom).map Gp.subtype

section Img

variable {X E : Type} [Group X] [Group E] {Gp : Subgroup E} (ε : X ≃* ↥Gp)

theorem burnsideF48_mem_img_iff (Q : Subgroup X) (y : E) :
    y ∈ burnsideF48_img ε Q ↔ ∃ x ∈ Q, ((ε x : ↥Gp) : E) = y := by
  unfold burnsideF48_img
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨ε x, ⟨x, hx, rfl⟩, rfl⟩

theorem burnsideF48_mem_img (Q : Subgroup X) (x : X) :
    ((ε x : ↥Gp) : E) ∈ burnsideF48_img ε Q ↔ x ∈ Q :=
  burnsideF48_mem_map_map ε Q x

theorem burnsideF48_img_le (Q : Subgroup X) : burnsideF48_img ε Q ≤ Gp :=
  Subgroup.map_subtype_le _

theorem burnsideF48_img_le_iff {Q Q' : Subgroup X} :
    burnsideF48_img ε Q ≤ burnsideF48_img ε Q' ↔ Q ≤ Q' := by
  constructor
  · intro h x hx
    exact (burnsideF48_mem_img ε Q' x).1 (h ((burnsideF48_mem_img ε Q x).2 hx))
  · exact fun h => Subgroup.map_mono (Subgroup.map_mono h)

theorem burnsideF48_img_injective : Function.Injective (burnsideF48_img ε) :=
  fun _ _ h => le_antisymm ((burnsideF48_img_le_iff ε).1 h.le) ((burnsideF48_img_le_iff ε).1 h.ge)

theorem burnsideF48_img_top : burnsideF48_img ε ⊤ = Gp := by
  refine le_antisymm (burnsideF48_img_le ε _) fun y hy => ?_
  obtain ⟨x, hx⟩ : ∃ x, ((ε x : ↥Gp) : E) = y := ⟨ε.symm ⟨y, hy⟩, by simp⟩
  rw [← hx]
  exact (burnsideF48_mem_img ε ⊤ x).2 (Subgroup.mem_top _)

theorem burnsideF48_exists_img {R : Subgroup E} (hR : R ≤ Gp) :
    ∃ Q : Subgroup X, burnsideF48_img ε Q = R := by
  refine ⟨R.comap ((Gp.subtype).comp ε.toMonoidHom), ?_⟩
  ext y
  rw [burnsideF48_mem_img_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨ε.symm ⟨y, hR hy⟩, ?_, by simp⟩
    show ((ε (ε.symm ⟨y, hR hy⟩) : ↥Gp) : E) ∈ R
    simpa using hy

theorem burnsideF48_img_normalizer (T : Subgroup X) :
    burnsideF48_img ε (Subgroup.normalizer (T : Set X)) =
      Gp ⊓ Subgroup.normalizer (burnsideF48_img ε T : Set E) := by
  ext y
  rw [Subgroup.mem_inf, burnsideF48_mem_img_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(ε x).2, Subgroup.mem_normalizer_iff.2 fun h => ?_⟩
    constructor
    · intro hh
      obtain ⟨t, ht, rfl⟩ := (burnsideF48_mem_img_iff ε T h).1 hh
      refine (burnsideF48_mem_img_iff ε T _).2 ⟨x * t * x⁻¹, ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.1 hx t).1 ht
    · intro hh
      obtain ⟨t, ht, ht'⟩ := (burnsideF48_mem_img_iff ε T _).1 hh
      have hh' : h = ((ε (x⁻¹ * t * x) : ↥Gp) : E) := by
        have : h = ((ε x : ↥Gp) : E)⁻¹ * (((ε x : ↥Gp) : E) * h * ((ε x : ↥Gp) : E)⁻¹) *
            ((ε x : ↥Gp) : E) := by group
        rw [this, ← ht']
        simp [map_mul, map_inv]
      rw [hh']
      refine (burnsideF48_mem_img ε T _).2 ?_
      have := (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * t * x)).2
      refine this ?_
      simpa [mul_assoc] using ht
  · rintro ⟨hy, hn⟩
    obtain ⟨x, hx⟩ : ∃ x, ((ε x : ↥Gp) : E) = y := ⟨ε.symm ⟨y, hy⟩, by simp⟩
    refine ⟨x, ?_, hx⟩
    refine Subgroup.mem_normalizer_iff.2 fun t => ?_
    rw [← burnsideF48_mem_img ε T t, Subgroup.mem_normalizer_iff.1 hn, ← hx,
      ← burnsideF48_mem_img ε T (x * t * x⁻¹)]
    simp [map_mul, map_inv]

theorem burnsideF48_img_conj (g : ↥Gp) (Q : Subgroup X) :
    burnsideF48_img (ε.trans (MulAut.conj g)) Q =
      (burnsideF48_img ε Q).map (MulAut.conj (g : E)).toMonoidHom := by
  ext y
  rw [burnsideF48_mem_img_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨((ε x : ↥Gp) : E), (burnsideF48_mem_img ε Q x).2 hx, by simp [MulAut.conj_apply]⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (burnsideF48_mem_img_iff ε Q z).1 hz
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩

end Img

open scoped Pointwise in
theorem burnsideF48_sylow_conj {p : ℕ} [Fact p.Prime] {E : Type} [Group E] {Gp : Subgroup E}
    [Finite ↥Gp] {S S₀ : Subgroup E} (hS : ChF.IsSylowOf p S Gp) (hS₀ : ChF.IsSylowOf p S₀ Gp) :
    ∃ g : ↥Gp, S = S₀.map (MulAut.conj (g : E)).toMonoidHom := by
  have hP : IsPGroup p (S.subgroupOf Gp) := hS.2.1.comap_subtype
  have hP₀ : IsPGroup p (S₀.subgroupOf Gp) := hS₀.2.1.comap_subtype
  have hPi : ¬ p ∣ (S.subgroupOf Gp).index := hS.2.2
  have hP₀i : ¬ p ∣ (S₀.subgroupOf Gp).index := hS₀.2.2
  let P : Sylow p ↥Gp := hP.toSylow hPi
  let P₀ : Sylow p ↥Gp := hP₀.toSylow hP₀i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Gp P₀ P
  have hgS : (S.subgroupOf Gp) = MulAut.conj g • (S₀.subgroupOf Gp) := by
    have := congrArg (fun Q : Sylow p ↥Gp => (Q : Subgroup ↥Gp)) hg
    simpa [Sylow.coe_subgroup_smul, P, P₀, IsPGroup.toSylow_coe] using this.symm
  refine ⟨g, ?_⟩
  ext y
  rw [Subgroup.mem_map]
  constructor
  · intro hy
    have hyG : y ∈ Gp := hS.1 hy
    have hy' : (⟨y, hyG⟩ : ↥Gp) ∈ S.subgroupOf Gp := hy
    rw [hgS, Subgroup.mem_smul_pointwise_iff_exists] at hy'
    obtain ⟨s, hs, hsy⟩ := hy'
    refine ⟨(s : E), hs, ?_⟩
    have := congrArg Subtype.val hsy
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  · rintro ⟨s, hs, rfl⟩
    have hsG : s ∈ Gp := hS₀.1 hs
    have hs' : (⟨s, hsG⟩ : ↥Gp) ∈ S₀.subgroupOf Gp := hs
    have : MulAut.conj g • (⟨s, hsG⟩ : ↥Gp) ∈ MulAut.conj g • (S₀.subgroupOf Gp) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hs'
    rw [← hgS] at this
    have h2 : MulAut.conj g • (⟨s, hsG⟩ : ↥Gp) = g * ⟨s, hsG⟩ * g⁻¹ := rfl
    rw [h2] at this
    exact this

theorem burnsideF48_identify {p : ℕ} [Fact p.Prime] {X E : Type} [Group X] [Group E]
    {Gp M₁ M₂ : Subgroup E} [Finite ↥Gp] (ε₀ : X ≃* ↥Gp) {B P₁ P₂ : Subgroup X}
    (hX : ChF.IsLieParabolics p (⊤ : Subgroup X) B P₁ P₂)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) :
    ∃ ε : X ≃* ↥Gp, burnsideF48_img ε B = Gp ⊓ (M₁ ⊓ M₂) ∧
      ((burnsideF48_img ε P₁ = Gp ⊓ M₁ ∧ burnsideF48_img ε P₂ = Gp ⊓ M₂) ∨
        (burnsideF48_img ε P₁ = Gp ⊓ M₂ ∧ burnsideF48_img ε P₂ = Gp ⊓ M₁)) := by
  obtain ⟨⟨S₀, hS₀, hB⟩, hne, -, hmax⟩ := hX
  obtain ⟨⟨S, hS, hB'⟩, -, -, hmax'⟩ := hP
  have hS₀img : ChF.IsSylowOf p (burnsideF48_img ε₀ S₀) Gp :=
    burnsideF48_isSylowOf_of_equiv_top ε₀ hS₀
  obtain ⟨g, hg⟩ := burnsideF48_sylow_conj hS hS₀img
  set ε : X ≃* ↥Gp := ε₀.trans (MulAut.conj g) with hε
  have hSimg : burnsideF48_img ε S₀ = S := by
    rw [hε, burnsideF48_img_conj, ← hg]
  have hBimg : burnsideF48_img ε B = Gp ⊓ (M₁ ⊓ M₂) := by
    rw [hB', hB, top_inf_eq, burnsideF48_img_normalizer, hSimg]
  have hkey : ∀ Q : Subgroup X,
      (B ≤ Q ∧ Q ≤ ⊤ ∧ Q ≠ ⊤ ∧ ∀ R : Subgroup X, Q < R → R ≤ ⊤ → R = ⊤) →
      (burnsideF48_img ε Q = Gp ⊓ M₁ ∨ burnsideF48_img ε Q = Gp ⊓ M₂) := by
    rintro Q ⟨hBQ, -, hQtop, hQmax⟩
    refine (hmax' (burnsideF48_img ε Q)).1 ⟨?_, burnsideF48_img_le ε Q, ?_, ?_⟩
    · rw [← hBimg]
      exact (burnsideF48_img_le_iff ε).2 hBQ
    · intro h
      apply hQtop
      apply burnsideF48_img_injective ε
      rw [h, burnsideF48_img_top]
    · intro R hQR hRG
      obtain ⟨R₀, rfl⟩ := burnsideF48_exists_img ε hRG
      have hlt : Q < R₀ := lt_of_le_of_ne ((burnsideF48_img_le_iff ε).1 hQR.le)
        (fun h => hQR.ne (by rw [h]))
      have := hQmax R₀ hlt le_top
      rw [this, burnsideF48_img_top]
  have h1 := hkey P₁ ((hmax P₁).2 (Or.inl rfl))
  have h2 := hkey P₂ ((hmax P₂).2 (Or.inr rfl))
  have hne2 : burnsideF48_img ε P₁ ≠ burnsideF48_img ε P₂ := fun h =>
    hne (burnsideF48_img_injective ε h)
  refine ⟨ε, hBimg, ?_⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne2
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne2

end CFSG.ASVolI
