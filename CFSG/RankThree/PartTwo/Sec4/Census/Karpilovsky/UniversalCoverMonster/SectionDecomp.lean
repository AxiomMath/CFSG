module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.HopfPrimaryBridge

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

section Decomp

variable {G E : Type} [Group G] [Group E] (π : E →* G)

theorem section_conj_eq {K W : Subgroup G} (hKn : ∀ w ∈ W, ∀ k ∈ K, w * k * w⁻¹ ∈ K)
    (σK : K →* E) (hσK : ∀ k, π (σK k) = k)
    (hKu : ∀ τ : K →* E, (∀ k, π (τ k) = k) → τ = σK) (σW : W →* E)
    (hσW : ∀ w, π (σW w) = w) (w : W) (k : K) :
    σW w * σK k * (σW w)⁻¹ = σK ⟨(w : G) * k * (w : G)⁻¹, hKn w w.2 k k.2⟩ := by
  let τ : K →* E :=
    { toFun := fun k => (σW w)⁻¹ * σK ⟨(w : G) * k * (w : G)⁻¹, hKn w w.2 k k.2⟩ * σW w
      map_one' := by
        have e : (⟨(w : G) * ((1 : K) : G) * (w : G)⁻¹, hKn w w.2 1 K.one_mem⟩ : K) = 1 :=
          Subtype.ext (by simp)
        show (σW w)⁻¹ * σK ⟨(w : G) * ((1 : K) : G) * (w : G)⁻¹, hKn w w.2 1 K.one_mem⟩ *
          σW w = 1
        rw [e, map_one]
        group
      map_mul' := fun a b => by
        have : (⟨(w : G) * ((a * b : K) : G) * (w : G)⁻¹, hKn w w.2 _ (a * b).2⟩ : K) =
            ⟨(w : G) * a * (w : G)⁻¹, hKn w w.2 a a.2⟩ *
              ⟨(w : G) * b * (w : G)⁻¹, hKn w w.2 b b.2⟩ :=
          Subtype.ext (by simp [mul_assoc])
        rw [this, map_mul]
        group }
  have hτ : ∀ k, π (τ k) = k := fun k => by
    show π ((σW w)⁻¹ * σK ⟨(w : G) * k * (w : G)⁻¹, hKn w w.2 k k.2⟩ * σW w) = k
    rw [map_mul, map_mul, map_inv, hσW, hσK]
    show ((w : G))⁻¹ * ((w : G) * k * (w : G)⁻¹) * w = k
    group
  have h := congrArg (fun f : K →* E => f k) (hKu τ hτ)
  have h' : (σW w)⁻¹ * σK ⟨(w : G) * k * (w : G)⁻¹, hKn w w.2 k k.2⟩ * σW w = σK k := h
  calc σW w * σK k * (σW w)⁻¹
      = σW w * ((σW w)⁻¹ * σK ⟨(w : G) * k * (w : G)⁻¹, hKn w w.2 k k.2⟩ * σW w) *
          (σW w)⁻¹ := by rw [h']
    _ = _ := by group

theorem exists_section_of_decomp {N K W : Subgroup G} (hKN : K ≤ N)
    (hKn : ∀ w ∈ W, ∀ k ∈ K, w * k * w⁻¹ ∈ K)
    (hdec : ∀ g ∈ N, ∃ k ∈ K, ∃ w ∈ W, g = k * w) (σK : K →* E)
    (hσK : ∀ k, π (σK k) = k) (hKu : ∀ τ : K →* E, (∀ k, π (τ k) = k) → τ = σK)
    (σW : W →* E) (hσW : ∀ w, π (σW w) = w)
    (hagree : ∀ x (hK : x ∈ K) (hW : x ∈ W), σK ⟨x, hK⟩ = σW ⟨x, hW⟩) :
    ∃ σ : N →* E, (∀ g, π (σ g) = g) ∧ ∀ (k : G) (hk : k ∈ K), σ ⟨k, hKN hk⟩ = σK ⟨k, hk⟩ := by
  classical
  have wd : ∀ (k k' : K) (w w' : W), (k : G) * w = k' * w' →
      σK k * σW w = σK k' * σW w' := by
    intro k k' w w' h
    have h1 : ((k' : G))⁻¹ * k = w' * (w : G)⁻¹ := by
      calc ((k' : G))⁻¹ * k = ((k' : G))⁻¹ * ((k : G) * w) * (w : G)⁻¹ := by group
        _ = ((k' : G))⁻¹ * ((k' : G) * w') * (w : G)⁻¹ := by rw [h]
        _ = w' * (w : G)⁻¹ := by group
    have hxK : ((k' : G))⁻¹ * k ∈ K := K.mul_mem (K.inv_mem k'.2) k.2
    have hxW : ((k' : G))⁻¹ * k ∈ W := by rw [h1]; exact W.mul_mem w'.2 (W.inv_mem w.2)
    have h2 := hagree _ hxK hxW
    have e1 : (⟨((k' : G))⁻¹ * k, hxK⟩ : K) = k'⁻¹ * k := Subtype.ext (by simp)
    have e2 : (⟨((k' : G))⁻¹ * k, hxW⟩ : W) = w' * w⁻¹ := Subtype.ext (by simpa using h1)
    rw [e1, e2, map_mul, map_mul, map_inv, map_inv] at h2
    calc σK k * σW w = σK k' * ((σK k')⁻¹ * σK k) * σW w := by group
      _ = σK k' * (σW w' * (σW w)⁻¹) * σW w := by rw [h2]
      _ = σK k' * σW w' := by group
  have hex : ∀ g : N, ∃ (k : K) (w : W), (g : G) = k * w := fun g => by
    obtain ⟨k, hk, w, hw, h⟩ := hdec g g.2
    exact ⟨⟨k, hk⟩, ⟨w, hw⟩, h⟩
  let f : N → E := fun g => σK (hex g).choose * σW (hex g).choose_spec.choose
  have key : ∀ (k : K) (w : W) (hg : (k : G) * w ∈ N), f ⟨k * w, hg⟩ = σK k * σW w := by
    intro k w hg
    exact wd _ _ _ _ (hex ⟨k * w, hg⟩).choose_spec.choose_spec.symm
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ?_, ?_⟩
  · have := key 1 1 (by simp)
    simpa using this
  · intro g₁ g₂
    obtain ⟨k₁, w₁, h₁⟩ := hex g₁
    obtain ⟨k₂, w₂, h₂⟩ := hex g₂
    have hk' : (w₁ : G) * k₂ * (w₁ : G)⁻¹ ∈ K := hKn w₁ w₁.2 k₂ k₂.2
    have hprod : (g₁ * g₂ : N) = ⟨(k₁ * ⟨(w₁ : G) * k₂ * (w₁ : G)⁻¹, hk'⟩ : K) * (w₁ * w₂ : W),
        by rw [← show ((g₁ * g₂ : N) : G) = (k₁ * ⟨(w₁ : G) * k₂ * (w₁ : G)⁻¹, hk'⟩ : K) *
          (w₁ * w₂ : W) from by
            simp only [Subgroup.coe_mul, h₁, h₂]; group]; exact (g₁ * g₂).2⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, h₁, h₂]
      group
    have e₁ : g₁ = ⟨k₁ * w₁, by rw [← h₁]; exact g₁.2⟩ := Subtype.ext h₁
    have e₂ : g₂ = ⟨k₂ * w₂, by rw [← h₂]; exact g₂.2⟩ := Subtype.ext h₂
    show f (g₁ * g₂) = f g₁ * f g₂
    rw [hprod, key, e₁, e₂, key, key, map_mul, map_mul,
      ← section_conj_eq π hKn σK hσK hKu σW hσW w₁ k₂]
    group
  · intro g
    obtain ⟨k, w, h⟩ := hex g
    have : g = ⟨k * w, by rw [← h]; exact g.2⟩ := Subtype.ext h
    show π (f g) = g
    rw [this, key, map_mul, hσK, hσW]
  · intro k hk
    have := key ⟨k, hk⟩ 1 (by simpa using hKN hk)
    simpa using this

end Decomp

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
