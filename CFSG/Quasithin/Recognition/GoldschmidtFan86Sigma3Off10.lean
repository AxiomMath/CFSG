module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off3

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup

@[expose] def smallClass (G : Type*) [Group G] : Set G :=
  {t | t * t = 1 ∧ ∀ g₁ g₂ g₃ : G, g₁ * t * g₁⁻¹ = g₂ * t * g₂⁻¹ ∨
    g₁ * t * g₁⁻¹ = g₃ * t * g₃⁻¹ ∨ g₂ * t * g₂⁻¹ = g₃ * t * g₃⁻¹}

theorem smallClass_char {G : Type*} [Group G] :
    (Subgroup.closure (smallClass G)).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨t, ⟨ht2, htc⟩, rfl⟩
  refine ⟨by simpa using congrArg φ ht2, fun g₁ g₂ g₃ => ?_⟩
  rcases htc (φ.symm g₁) (φ.symm g₂) (φ.symm g₃) with e | e | e
  · exact Or.inl (by simpa using congrArg φ e)
  · exact Or.inr (Or.inl (by simpa using congrArg φ e))
  · exact Or.inr (Or.inr (by simpa using congrArg φ e))

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H} {x : H}

theorem Hyp3.conj_nQ (h : Hyp3 H S x) {a s : H} (ha : a ∈ S) (haQ : a ∉ oQ H) (hs : s ∈ S)
    (hsQ : s ∉ oQ H) {n : H} (hn : n ∈ nQ H x) : s * n * s⁻¹ = a * n * a⁻¹ := by
  rcases h.sig.mul_inv_mem hs ha haQ with h1 | h1
  · exact absurd h1 hsQ
  · have han : a * n * a⁻¹ ∈ oneCenter (oQ H) := nQ_le x ((h.sig.nQ_normal h.ord).conj_mem n hn a)
    have hc := (mem_oneCenter.1 han).2.2 _ h1
    calc s * n * s⁻¹ = (s * a⁻¹) * (a * n * a⁻¹) * (s * a⁻¹)⁻¹ := by group
      _ = a * n * a⁻¹ := by rw [← hc]; group

omit [Finite H] in
theorem conj_nQ_Q {g : H} (hg : g ∈ oQ H) {n : H} (hn : n ∈ nQ H x) : g * n * g⁻¹ = n := by
  have := (mem_oneCenter.1 (nQ_le x hn)).2.2 g hg
  rw [← this]
  group

theorem nQ_le_S (h : Sig3 H S) {n : H} (hn : n ∈ nQ H x) : n ∈ S :=
  h.Q_le_S (oneCenter_le (nQ_le x hn))

theorem Hyp3.nQ_mem_smallClass (h : Hyp3 H S x) {a : H} (ha : a ∈ S) (haQ : a ∉ oQ H) {n : H}
    (hn : n ∈ nQ H x) : (⟨n, nQ_le_S h.sig hn⟩ : ↥S) ∈ smallClass ↥S := by
  refine ⟨Subtype.ext (mem_oneCenter.1 (nQ_le x hn)).2.1, fun g₁ g₂ g₃ => ?_⟩
  have key : ∀ g : ↥S, g * ⟨n, nQ_le_S h.sig hn⟩ * g⁻¹ = ⟨n, nQ_le_S h.sig hn⟩ ∨
      g * ⟨n, nQ_le_S h.sig hn⟩ * g⁻¹ =
        ⟨a, ha⟩ * ⟨n, nQ_le_S h.sig hn⟩ * (⟨a, ha⟩ : ↥S)⁻¹ := by
    intro g
    by_cases hg : (g : H) ∈ oQ H
    · exact Or.inl (Subtype.ext (conj_nQ_Q hg hn))
    · exact Or.inr (Subtype.ext (h.conj_nQ ha haQ g.2 hg hn))
  rcases key g₁ with e1 | e1 <;> rcases key g₂ with e2 | e2 <;> rcases key g₃ with e3 | e3 <;>
    first
    | exact Or.inl (e1.trans e2.symm)
    | exact Or.inr (Or.inl (e1.trans e3.symm))
    | exact Or.inr (Or.inr (e2.trans e3.symm))

end CFSG.Quasithin.Fan86.Sigma3
