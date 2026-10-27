module

public import CFSG.Milestones.ASVolI.F411.Ident

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

variable {E : Type} [Group E]

theorem burnsideF411_normalizer_parabolic_le [Finite E] {p : ℕ} [Fact p.Prime]
    {Gp B P₁ P₂ : Subgroup E} (hP : IsLieParabolics p Gp B P₁ P₂) :
    Gp ⊓ Subgroup.normalizer (P₁ : Set E) ≤ P₁ := by
  obtain ⟨⟨S, hS, hB⟩, hne, hinf, hmax⟩ := hP
  obtain ⟨hBP₁, hP₁Gp, hP₁ne, hP₁max⟩ := (hmax P₁).mpr (Or.inl rfl)
  obtain ⟨hBP₂, hP₂Gp, hP₂ne, hP₂max⟩ := (hmax P₂).mpr (Or.inr rfl)
  by_contra hle
  have hlt : P₁ < Gp ⊓ Subgroup.normalizer (P₁ : Set E) :=
    lt_of_le_of_ne (le_inf hP₁Gp Subgroup.le_normalizer) fun h => hle h.ge
  have hNGp := hP₁max _ hlt inf_le_left
  have hGpN : ∀ g ∈ Gp, g ∈ Subgroup.normalizer (P₁ : Set E) := fun g hg => by
    have : g ∈ Gp ⊓ Subgroup.normalizer (P₁ : Set E) := by rw [hNGp]; exact hg
    exact this.2
  have hSB : S ≤ B := hB ▸ le_inf hS.1 Subgroup.le_normalizer
  have hBN : B ≤ Subgroup.normalizer (S : Set E) := hB ▸ inf_le_right
  have hP₂B : P₂ ≤ B := by
    intro g hg
    have hgGp : g ∈ Gp := hP₂Gp hg
    let Sg : Subgroup E := S.map (MulAut.conj g).toMonoidHom
    have hSgB : Sg ≤ B := by
      rw [← hinf]
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hGpN g hgGp) s).mp (hBP₁ (hSB hs))
      · exact P₂.mul_mem (P₂.mul_mem hg (hBP₂ (hSB hs))) (P₂.inv_mem hg)
    have hSgN : Sg ≤ Subgroup.normalizer (S : Set E) := hSgB.trans hBN
    have hp : IsPGroup p (S ⊔ Sg : Subgroup E) :=
      IsPGroup.to_sup_of_normal_left' hS.2.1 (hS.2.1.map _) hSgN
    have hle' : S ⊔ Sg ≤ Gp := sup_le hS.1 (hSgB.trans (hBP₁.trans hP₁Gp))
    have heq := burnsideF411_eq_of_isSylowOf hS le_sup_left hle' hp
    have hSgS : Sg ≤ S := heq ▸ le_sup_right
    have hcard : Nat.card Sg = Nat.card S :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hSg : Sg = S := Subgroup.eq_of_le_of_card_ge hSgS (by rw [hcard])
    have hgN : g ∈ Subgroup.normalizer (S : Set E) := by
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        have : g * s * g⁻¹ ∈ Sg := ⟨s, hs, rfl⟩
        rwa [hSg] at this
      · intro hs
        have : g * s * g⁻¹ ∈ Sg := by rw [hSg]; exact hs
        obtain ⟨t, ht, hts⟩ := this
        have : t = s := by
          have := congrArg (fun z => g⁻¹ * z * g) hts
          simpa [MulAut.conj_apply, mul_assoc] using this
        rw [← this]
        exact ht
    rw [hB]
    exact ⟨hgGp, hgN⟩
  have hP₂eq : P₂ = B := le_antisymm hP₂B hBP₂
  have hlt₂ : P₂ < P₁ := by
    rw [hP₂eq]
    exact lt_of_le_of_ne hBP₁ fun h => hne (h.symm.trans hP₂eq.symm)
  exact hP₁ne (hP₂max P₁ hlt₂ hP₁Gp)

theorem burnsideF411_eq_normalizer [Finite E] {p : ℕ} [Fact p.Prime] {Gp M M' B P' : Subgroup E}
    (hN : Gp.Normal) (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M ⊓ M', e = n * h)
    (hP : IsLieParabolics p Gp B (Gp ⊓ M) P') :
    Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) = M := by
  apply le_antisymm
  · have hMN : M ≤ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
      rw [inf_comm]
      exact burnsideF411_le_normalizer_inf hN M
    exact burnsideF411_normalizer_le inf_le_left hsplit hMN
      ((burnsideF411_normalizer_parabolic_le hP).trans inf_le_right)
  · rw [inf_comm]
    exact burnsideF411_le_normalizer_inf hN M

theorem burnsideF411_swap_of_aut [Finite E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    (hC : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hM₁ : Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E) = M₁)
    (hM₂ : Subgroup.normalizer ((Gp ⊓ M₂ : Subgroup E) : Set E) = M₂)
    (ζ : MulAut ↥Gp)
    (hζE : ∀ e : E, ∃ e' : E, MulAut.conjNormal e' = ζ * MulAut.conjNormal e * ζ⁻¹)
    (hζ1 : ((Gp ⊓ M₁).subgroupOf Gp).map ζ.toMonoidHom = (Gp ⊓ M₂).subgroupOf Gp)
    (hζ2 : ((Gp ⊓ M₂).subgroupOf Gp).map ζ.toMonoidHom = (Gp ⊓ M₁).subgroupOf Gp) :
    burnsideF411_Swap M₁ M₂ := by
  classical
  intro _ _ _ _ _ _ _
  have hcinj : Function.Injective (MulAut.conjNormal : E →* MulAut ↥Gp) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := congrArg (fun φ : MulAut ↥Gp => ((φ ⟨n, hn⟩ : ↥Gp) : E)) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc n * x = (x * n * x⁻¹) * x := by rw [h1]
      _ = x * n := by group
  choose θ₀ hθ₀ using hζE
  have hθmul : ∀ a b, θ₀ (a * b) = θ₀ a * θ₀ b := by
    intro a b
    apply hcinj
    rw [map_mul, hθ₀, hθ₀, hθ₀, map_mul]
    group
  have hθinj : Function.Injective θ₀ := by
    intro a b h
    apply hcinj
    have h1 := hθ₀ a
    rw [h, hθ₀ b] at h1
    have h2 := congrArg (fun φ => ζ⁻¹ * φ * ζ) h1
    simpa [mul_assoc] using h2.symm
  let θ : E ≃* E := MulEquiv.ofBijective (MonoidHom.mk' θ₀ hθmul)
    ⟨hθinj, Finite.injective_iff_surjective.mp hθinj⟩
  have hθ : ∀ e, MulAut.conjNormal (θ e) = ζ * MulAut.conjNormal e * ζ⁻¹ := hθ₀
  have key : ∀ {X Y : Subgroup E},
      ((Gp ⊓ X).subgroupOf Gp).map ζ.toMonoidHom = (Gp ⊓ Y).subgroupOf Gp →
      (Subgroup.normalizer ((Gp ⊓ X : Subgroup E) : Set E)).map θ.toMonoidHom ≤
        Subgroup.normalizer ((Gp ⊓ Y : Subgroup E) : Set E) := by
    intro X Y hXY
    rintro _ ⟨e, he, rfl⟩
    change θ e ∈ Subgroup.normalizer ((Gp ⊓ Y : Subgroup E) : Set E)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hconj : ∀ y : ↥Gp, (θ e : E) * (y : E) * (θ e)⁻¹ =
        ((ζ ⟨e * ((ζ⁻¹ y : ↥Gp) : E) * e⁻¹,
          ‹Gp.Normal›.conj_mem _ (ζ⁻¹ y).2 e⟩ : ↥Gp) : E) := by
      intro y
      have h1 := congrArg (fun φ : MulAut ↥Gp => ((φ y : ↥Gp) : E)) (hθ e)
      simp only [MulAut.conjNormal_apply, MulAut.mul_apply] at h1
      rw [h1]
      rfl
    have hmemY : ∀ y : ↥Gp, (y : E) ∈ Gp ⊓ Y ↔ ζ⁻¹ y ∈ (Gp ⊓ X).subgroupOf Gp := by
      intro y
      have h1 : (y : E) ∈ Gp ⊓ Y ↔ y ∈ (Gp ⊓ Y).subgroupOf Gp := Iff.rfl
      rw [h1, ← hXY, Subgroup.mem_map_equiv]
      rfl
    constructor
    · intro hx
      have hxGp : x ∈ Gp := hx.1
      have h := hconj ⟨x, hxGp⟩
      rw [h, hmemY]
      simp only [MulAut.inv_apply, MulEquiv.symm_apply_apply]
      have hy : ((ζ⁻¹ ⟨x, hxGp⟩ : ↥Gp) : E) ∈ Gp ⊓ X := (hmemY ⟨x, hxGp⟩).mp hx
      exact (Subgroup.mem_normalizer_iff.mp he _).mp hy
    · intro hx
      have hxGp : x ∈ Gp := by
        have := ‹Gp.Normal›.conj_mem _ hx.1 (θ e)⁻¹
        simpa [mul_assoc] using this
      have h := hconj ⟨x, hxGp⟩
      rw [h, hmemY] at hx
      simp only [MulAut.inv_apply, MulEquiv.symm_apply_apply] at hx
      refine (hmemY ⟨x, hxGp⟩).mpr ?_
      have hz : e * ((ζ.symm ⟨x, hxGp⟩ : ↥Gp) : E) * e⁻¹ ∈ Gp ⊓ X := hx
      show ((ζ.symm ⟨x, hxGp⟩ : ↥Gp) : E) ∈ Gp ⊓ X
      exact (Subgroup.mem_normalizer_iff.mp he _).mpr hz
  have h12 := key hζ1
  have h21 := key hζ2
  rw [hM₁, hM₂] at h12 h21
  have hc12 : Nat.card M₁ ≤ Nat.card M₂ := by
    rw [← Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]
    exact Subgroup.card_le_of_le h12
  have hc21 : Nat.card M₂ ≤ Nat.card M₁ := by
    rw [← Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]
    exact Subgroup.card_le_of_le h21
  refine ⟨θ, Subgroup.eq_of_le_of_card_ge h12 ?_, Subgroup.eq_of_le_of_card_ge h21 ?_⟩
  · rw [Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]
    exact hc21
  · rw [Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]
    exact hc12

theorem burnsideF411_le_pCoreOf {p : ℕ} {N H : Subgroup E} (hNH : N ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set E)) (hp : IsPGroup p N) : N ≤ pCoreOf p H := by
  have hnorm : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hN
  have hp' : IsPGroup p (N.subgroupOf H) := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hle : N.subgroupOf H ≤ CFSG.pCore p ↥H := le_sSup ⟨hnorm, hp'⟩
  intro x hx
  exact ⟨⟨x, hNH hx⟩, hle hx, rfl⟩

theorem burnsideF411_pCoreOf_le {p : ℕ} (H : Subgroup E) : pCoreOf p H ≤ H :=
  Subgroup.map_subtype_le _

theorem burnsideF411_pCoreOf_isPGroup {p : ℕ} (H : Subgroup E) : IsPGroup p (pCoreOf p H) :=
  CFSG.pCore_isPGroup.map H.subtype

theorem burnsideF411_le_normalizer_pCoreOf {p : ℕ} (H : Subgroup E) :
    H ≤ Subgroup.normalizer (pCoreOf p H : Set E) :=
  Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p H)

end CFSG.ASVolI
