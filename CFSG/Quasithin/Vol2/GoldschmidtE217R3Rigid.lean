module

public import CFSG.Quasithin.EmptyFaithful.S146yBorelBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab2

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer

namespace E217R3

section Single

variable {X : Type} [Group X]

theorem mem_normalizer_of_subgroupOf {L S : Subgroup X} (hSL : S ≤ L) (b : ↥L)
    (hb : b ∈ Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)) :
    (b : X) ∈ Subgroup.normalizer (S : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hb ⊢
  intro g
  constructor
  · intro hg
    have := (hb ⟨g, hSL hg⟩).mp (by rw [Subgroup.mem_subgroupOf]; exact hg)
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  · intro hg
    have hgL : g ∈ L := by
      have h1 : (b : X) * g * (b : X)⁻¹ ∈ L := hSL hg
      have h2 : (b : X)⁻¹ * ((b : X) * g * (b : X)⁻¹) * (b : X) ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem b.2) h1) b.2
      simpa [mul_assoc] using h2
    have := (hb ⟨g, hgL⟩).mpr (by rw [Subgroup.mem_subgroupOf]; exact hg)
    rw [Subgroup.mem_subgroupOf] at this
    exact this

theorem centralizes_of_borelRigid {L S : Subgroup X} (hrig : BorelRigid ↥L)
    (hS : IsSylowTwoOf S L) {v : X} (hv2 : v * v = 1)
    (hvL : v ∈ Subgroup.normalizer (L : Set X))
    (hvB : ∀ b ∈ L ⊓ Subgroup.normalizer (S : Set X), v * b = b * v) :
    ∀ k ∈ L, v * k = k * v := by
  have happ : ∀ k : ↥L, ((L.normalizerMonoidHom ⟨v, hvL⟩ k : ↥L) : X) = v * k * v⁻¹ :=
    fun k => rfl
  have hβ : L.normalizerMonoidHom ⟨v, hvL⟩ = 1 := by
    refine hrig (S.subgroupOf L) (isSylowTwoOf_subgroupOf_top' hS) _ (fun y => ?_) (fun b hb => ?_)
    · apply Subtype.ext
      rw [happ, happ]
      calc v * (v * (y : X) * v⁻¹) * v⁻¹ = (v * v) * (y : X) * (v * v)⁻¹ := by group
        _ = y := by rw [hv2]; group
    · apply Subtype.ext
      rw [happ]
      have hbn := mem_normalizer_of_subgroupOf hS.1 b hb
      have := hvB b ⟨b.2, hbn⟩
      rw [this]
      group
  intro k hk
  have h := congrArg (fun f : MulAut ↥L => ((f ⟨k, hk⟩ : ↥L) : X)) hβ
  simp only [happ] at h
  have h' : v * k * v⁻¹ = k := h
  calc v * k = (v * k * v⁻¹) * v := by group
    _ = k * v := by rw [h']

end Single

theorem isBorelIn_map {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {X B : Subgroup Y}
    (h : E2.IsBorelIn X B) :
    E2.IsBorelIn (X.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine ⟨S.map e.toMonoidHom, (isSylowTwoOf_map_mulEquiv e).2 hS, ?_⟩
  rw [Subgroup.map_inf_eq _ _ _ e.injective, Subgroup.map_equiv_normalizer_eq]

theorem mem_normalizer_of_paired {Y : Type} [Group Y] [Finite Y] {K₁ K₂ B : Subgroup Y}
    (hKn : (K₁ ⊔ K₂).Normal) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hsimp : IsSimpleGroup ↥K₁) (hBK : B ≤ K₁) (hB : B ≠ ⊥) {v : Y}
    (hvB : ∀ b ∈ B, v * b = b * v) : v ∈ Subgroup.normalizer (K₁ : Set Y) := by
  set f : Y →* Y := (MulAut.conj v).toMonoidHom with hf
  have happ : ∀ x : Y, f x = v * x * v⁻¹ := fun x => rfl
  set L : Subgroup Y := K₁.map f with hL
  have hLN : L ≤ K₁ ⊔ K₂ := by
    rintro _ ⟨k, hk, rfl⟩
    exact hKn.conj_mem k (Subgroup.mem_sup_left hk) v
  have hK₂N : K₂ ≤ Subgroup.normalizer (K₁ : Set Y) :=
    (show K₂ ≤ Subgroup.centralizer (K₁ : Set Y) from fun b hb =>
      Subgroup.mem_centralizer_iff.2 fun a ha => hc a ha b hb).trans
      (Subgroup.centralizer_le_normalizer _)
  have hNorm : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set Y) := sup_le Subgroup.le_normalizer hK₂N
  have hLs : IsSimpleGroup ↥L :=
    haveI := hsimp
    (K₁.equivMapOfInjective f (MulAut.conj v).injective).symm.isSimpleGroup
  have hnorm : ((L ⊓ K₁).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hn.1) (L.inv_mem g.2), ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (hNorm (hLN g.2)) (n : Y)).1 hn.2
    simpa using this
  have hLK : L ≤ K₁ := by
    have := hLs
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ K₁).subgroupOf L) with h | h
    · exfalso
      obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB
      have hbL : (b : Y) ∈ L := ⟨b, hBK b.2, by
        rw [happ, hvB b b.2]
        group⟩
      have hmem : (⟨b, hbL⟩ : ↥L) ∈ (L ⊓ K₁).subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨hbL, hBK b.2⟩
      rw [h, Subgroup.mem_bot] at hmem
      have h1 : (b : Y) = 1 := congrArg Subtype.val hmem
      exact hb1 (Subtype.ext h1)
    · intro x hx
      have hmem : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ K₁).subgroupOf L := by
        rw [h]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hmem).2
  have hLeq : L = K₁ := by
    refine Subgroup.eq_of_le_of_card_ge hLK ?_
    rw [hL, Subgroup.card_map_of_injective (MulAut.conj v).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have : f k ∈ L := ⟨k, hk, rfl⟩
    rw [hLeq] at this
    simpa [happ] using this
  · intro h
    have h' : f k ∈ L := by
      rw [hLeq]
      simpa [happ] using h
    obtain ⟨x, hx, hxk⟩ := h'
    have : x = k := (MulAut.conj v).injective hxk
    rwa [← this]

theorem commute_of_mem_map_conj {Y : Type} [Group Y] {K : Subgroup Y} {t v : Y}
    (hvt : v * t = t * v) (hvK : ∀ k ∈ K, v * k = k * v) :
    ∀ k ∈ K.map (MulAut.conj t).toMonoidHom, v * k = k * v := by
  rintro _ ⟨k, hk, rfl⟩
  have h1 : Commute v t := hvt
  exact ((h1.mul_right (hvK k hk)).mul_right h1.inv_right).eq

end E217R3

end CFSG.Quasithin
