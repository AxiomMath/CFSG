module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinK
public import CFSG.Quasithin.EmptyFaithful.S146zNFinQ

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

@[expose] def bxA : A6 := ⟨bx, mem_alternatingGroup.mpr sign_bx⟩

@[expose] def u1A : A6 := ⟨u1, mem_alternatingGroup.mpr (by unfold u1; decide)⟩

@[expose] def u2A : A6 := ⟨u2, mem_alternatingGroup.mpr (by unfold u2; decide)⟩

@[expose] def u3A : A6 := ⟨u3, mem_alternatingGroup.mpr (by unfold u3; decide)⟩

@[expose] def u4A : A6 := ⟨u4, mem_alternatingGroup.mpr (by unfold u4; decide)⟩

@[expose] def NormA (g c d : A6) : Prop :=
  (g * c * g⁻¹ = c ∨ g * c * g⁻¹ = d ∨ g * c * g⁻¹ = c * d) ∧
    (g * d * g⁻¹ = c ∨ g * d * g⁻¹ = d ∨ g * d * g⁻¹ = c * d)

theorem normA_iff (g c d : A6) : NormA g c d ↔ NormV g.1 c.1 d.1 := by
  unfold NormA NormV
  simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_inv]

theorem NormA.map (α : MulAut A6) {g c d : A6} (h : NormA g c d) : NormA (α g) (α c) (α d) := by
  obtain ⟨h1, h2⟩ := h
  have key : ∀ x y : A6, g * x * g⁻¹ = y → α g * α x * (α g)⁻¹ = α y := fun x y e => by
    rw [← map_inv, ← map_mul, ← map_mul, e]
  refine ⟨?_, ?_⟩
  · rcases h1 with e | e | e
    · exact Or.inl (key _ _ e)
    · exact Or.inr (Or.inl (key _ _ e))
    · exact Or.inr (Or.inr ((key _ _ e).trans (map_mul α c d)))
  · rcases h2 with e | e | e
    · exact Or.inl (key _ _ e)
    · exact Or.inr (Or.inl (key _ _ e))
    · exact Or.inr (Or.inr ((key _ _ e).trans (map_mul α c d)))


theorem pow3_iff (g : A6) : g ^ 3 = 1 ↔ g.1 * g.1 * g.1 = 1 := by
  constructor
  · intro h
    simpa [pow_succ, mul_assoc] using congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    simpa [pow_succ, mul_assoc] using h

@[expose] def FamB (c d : A6) : Prop :=
  ∃ r : A6, r * c * r⁻¹ = bxA ∧ (r * d * r⁻¹ = u1A ∨ r * d * r⁻¹ = u2A)

@[expose] def FamA (c d : A6) : Prop :=
  ∃ r : A6, r * c * r⁻¹ = bxA ∧ (r * d * r⁻¹ = u3A ∨ r * d * r⁻¹ = u4A)

@[expose] def HasU (c d : A6) : Prop := ∃ g : A6, IsU g ∧ NormA g c d

@[expose] def HasT (c d : A6) : Prop := ∃ g : A6, IsT g ∧ NormA g c d

theorem fam_cases (c d : A6) (hcd : c ≠ d) (hc1 : c ≠ 1) (hd1 : d ≠ 1) (hc2 : c * c = 1)
    (hd2 : d * d = 1) (hcomm : c * d = d * c) : FamB c d ∨ FamA c d := by
  obtain ⟨r, hr, h1, h2⟩ := klein_conj c.1 d.1 (mem_alternatingGroup.mp c.2)
    (mem_alternatingGroup.mp d.2) (fun e => hc1 (Subtype.ext e)) (fun e => hd1 (Subtype.ext e))
    (fun e => hcd (Subtype.ext e)) (by simpa using congrArg Subtype.val hc2)
    (by simpa using congrArg Subtype.val hd2) (by simpa using congrArg Subtype.val hcomm)
  let r' : A6 := ⟨r, mem_alternatingGroup.mpr hr⟩
  have e1 : r' * c * r'⁻¹ = bxA := Subtype.ext h1
  rcases h2 with h | h | h | h
  · exact Or.inl ⟨r', e1, Or.inl (Subtype.ext h)⟩
  · exact Or.inl ⟨r', e1, Or.inr (Subtype.ext h)⟩
  · exact Or.inr ⟨r', e1, Or.inl (Subtype.ext h)⟩
  · exact Or.inr ⟨r', e1, Or.inr (Subtype.ext h)⟩

theorem FamB.type {c d : A6} (h : FamB c d) : HasU c d ∧ ¬ HasT c d := by
  obtain ⟨r, e1, e2⟩ := h
  obtain ⟨u, hu, hd⟩ : ∃ u : A6, (u = u1A ∨ u = u2A) ∧ r * d * r⁻¹ = u := by
    rcases e2 with e | e
    · exact ⟨u1A, Or.inl rfl, e⟩
    · exact ⟨u2A, Or.inr rfl, e⟩
  have hu' : u.1 = u1 ∨ u.1 = u2 := by
    rcases hu with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  constructor
  · obtain ⟨g₀, hs, h3, h1, hN, hnf⟩ := exists_B u.1 hu'
    let G₀ : A6 := ⟨g₀, mem_alternatingGroup.mpr hs⟩
    let α : MulAut A6 := MulAut.conj r⁻¹
    refine ⟨α G₀, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [← map_pow, (pow3_iff G₀).mpr h3, map_one]
    · intro e
      exact h1 (congrArg Subtype.val (α.injective (e.trans (map_one α).symm)))
    · exact nofix_conj r⁻¹ G₀ hnf
    · have := NormA.map α ((normA_iff G₀ bxA u).mpr hN)
      have hc : α bxA = c := by
        simp only [α, MulAut.conj_apply, inv_inv]
        rw [← e1]; group
      have hd' : α u = d := by
        simp only [α, MulAut.conj_apply, inv_inv]
        rw [← hd]; group
      rwa [hc, hd'] at this
  · rintro ⟨g, ⟨h3, h1, ⟨i, hi⟩⟩, hN⟩
    let α : MulAut A6 := MulAut.conj r
    have hN' := NormA.map α hN
    have hc : α c = bxA := by
      simp only [α, MulAut.conj_apply]; exact e1
    have hd' : α d = u := by
      simp only [α, MulAut.conj_apply]; exact hd
    rw [hc, hd', normA_iff] at hN'
    have hα3 : α g ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    have hα1 : (α g).1 ≠ 1 := fun e => h1 (α.injective ((Subtype.ext e).trans (map_one α).symm))
    have hnf := normV_B u.1 hu' (α g).1 (mem_alternatingGroup.mp (α g).2)
      ((pow3_iff _).mp hα3) hα1 hN'
    have hfix := fix_conj r g i hi
    exact hnf (r.1 i) hfix


theorem FamA.type {c d : A6} (h : FamA c d) : HasT c d ∧ ¬ HasU c d := by
  obtain ⟨r, e1, e2⟩ := h
  obtain ⟨u, hu, hd⟩ : ∃ u : A6, (u = u3A ∨ u = u4A) ∧ r * d * r⁻¹ = u := by
    rcases e2 with e | e
    · exact ⟨u3A, Or.inl rfl, e⟩
    · exact ⟨u4A, Or.inr rfl, e⟩
  have hu' : u.1 = u3 ∨ u.1 = u4 := by
    rcases hu with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  constructor
  · obtain ⟨g₀, hs, h3, h1, hN, hf⟩ := exists_A u.1 hu'
    let G₀ : A6 := ⟨g₀, mem_alternatingGroup.mpr hs⟩
    let α : MulAut A6 := MulAut.conj r⁻¹
    refine ⟨α G₀, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [← map_pow, (pow3_iff G₀).mpr h3, map_one]
    · intro e
      exact h1 (congrArg Subtype.val (α.injective (e.trans (map_one α).symm)))
    · obtain ⟨i, hi⟩ := hf
      exact ⟨r⁻¹.1 i, by
        have := fix_conj r⁻¹ G₀ i hi
        simpa [α, MulAut.conj_apply] using this⟩
    · have := NormA.map α ((normA_iff G₀ bxA u).mpr hN)
      have hc : α bxA = c := by
        simp only [α, MulAut.conj_apply, inv_inv]
        rw [← e1]; group
      have hd' : α u = d := by
        simp only [α, MulAut.conj_apply, inv_inv]
        rw [← hd]; group
      rwa [hc, hd'] at this
  · rintro ⟨g, ⟨h3, h1, hn⟩, hN⟩
    let α : MulAut A6 := MulAut.conj r
    have hN' := NormA.map α hN
    have hc : α c = bxA := by
      simp only [α, MulAut.conj_apply]; exact e1
    have hd' : α d = u := by
      simp only [α, MulAut.conj_apply]; exact hd
    rw [hc, hd', normA_iff] at hN'
    have hα3 : α g ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    have hα1 : (α g).1 ≠ 1 := fun e => h1 (α.injective ((Subtype.ext e).trans (map_one α).symm))
    obtain ⟨j, hj⟩ := normV_A u.1 hu' (α g).1 (mem_alternatingGroup.mp (α g).2)
      ((pow3_iff _).mp hα3) hα1 hN'
    have hnf := nofix_conj r g hn
    exact hnf j (by simpa [α, MulAut.conj_apply] using hj)

end CFSG.Quasithin.A6Fin
