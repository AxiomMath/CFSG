module

public import CFSG.RankThree.PartOne.CTP.SeitzThree

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne (IsStronglyPEmbedded IsSylowOf omegaOne ExtSPE)
open CFSG.RankThree.PartOne.Census3 (IsoLie TheoremThreeList)
open CFSG.RankThree.PartOne.StrongP
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

section Thm3

variable {q : TauCeti.PrimePower}

theorem thm3_A1_odd (h2 : q.p ≠ 2) (h5 : 5 ≤ q.card) : Thm3LieIndex (.A 1 q) :=
  Or.inl ⟨q, h2, h5, rfl⟩

theorem thm3_A2 (h2 : q.p ≠ 2) (he : q.exponent ≤ 3) : Thm3LieIndex (.A 2 q) :=
  Or.inr (Or.inl ⟨q, h2, he, Or.inl rfl⟩)

theorem thm3_twistedA2 (h2 : q.p ≠ 2) (he : q.exponent ≤ 3) : Thm3LieIndex (.twistedA 2 q) :=
  Or.inr (Or.inl ⟨q, h2, he, Or.inr rfl⟩)

theorem thm3_reeG2 : Thm3LieIndex (.reeG2 1) := Or.inr (Or.inr (Or.inl rfl))

theorem thm3_G2_odd (h2 : q.p ≠ 2) (he : q.exponent = 1) : Thm3LieIndex (.G2 q) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨q, h2, he, Or.inl rfl⟩)))

theorem thm3_B2_odd (h2 : q.p ≠ 2) (he : q.exponent = 1) : Thm3LieIndex (.B 2 q) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨q, h2, he, Or.inr (Or.inl rfl)⟩)))

theorem thm3_twistedA3_odd (h2 : q.p ≠ 2) (he : q.exponent = 1) :
    Thm3LieIndex (.twistedA 3 q) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨q, h2, he, Or.inr (Or.inr (Or.inl rfl))⟩)))

theorem thm3_A3_odd (h2 : q.p ≠ 2) (he : q.exponent = 1) : Thm3LieIndex (.A 3 q) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨q, h2, he, Or.inr (Or.inr (Or.inr rfl))⟩)))

theorem thm3_A1_even (h2 : q.p = 2) : Thm3LieIndex (.A 1 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, h2, rfl⟩))))

theorem thm3_suzuki (m : ℕ) : Thm3LieIndex (.suzuki m) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩)))))

theorem thm3_twistedA2_even (h2 : q.p = 2) : Thm3LieIndex (.twistedA 2 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, h2, Or.inl rfl⟩))))))

theorem thm3_A2_even (h2 : q.p = 2) : Thm3LieIndex (.A 2 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, h2, Or.inr (Or.inl rfl)⟩))))))

theorem thm3_B2_even (h2 : q.p = 2) : Thm3LieIndex (.B 2 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨q, h2, Or.inr (Or.inr (Or.inl rfl))⟩))))))

theorem thm3_G2_even (h2 : q.p = 2) : Thm3LieIndex (.G2 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨q, h2, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩))))))

theorem thm3_twistedA3_even (h2 : q.p = 2) : Thm3LieIndex (.twistedA 3 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨q, h2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩))))))

theorem thm3_twistedA4_even (h2 : q.p = 2) : Thm3LieIndex (.twistedA 4 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨q, h2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩))))))

theorem thm3_trialityD4_even (h2 : q.p = 2) : Thm3LieIndex (.trialityD4 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨q, h2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩))))))

theorem thm3_reeF4 (m : ℕ) : Thm3LieIndex (.reeF4 m) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩)))))))

theorem thm3_tits : Thm3LieIndex .tits :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))

theorem thm3_A3_even (h2 : q.p = 2) : Thm3LieIndex (.A 3 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨q, h2, Or.inl rfl⟩)))))))))

theorem thm3_B3_even (h2 : q.p = 2) : Thm3LieIndex (.B 3 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨q, h2, Or.inr (Or.inl rfl)⟩)))))))))

theorem thm3_twistedD4_even (h2 : q.p = 2) : Thm3LieIndex (.twistedD 4 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨q, h2, Or.inr (Or.inr rfl)⟩)))))))))

theorem thm3_A4_two (h2 : q.p = 2) (he : q.exponent = 1) : Thm3LieIndex (.A 4 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨q, h2, he, Or.inl rfl⟩)))))))))

theorem thm3_A5_two (h2 : q.p = 2) (he : q.exponent = 1) : Thm3LieIndex (.A 5 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨q, h2, he, Or.inr (Or.inl rfl)⟩)))))))))

theorem thm3_A6_two (h2 : q.p = 2) (he : q.exponent = 1) : Thm3LieIndex (.A 6 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨q, h2, he, Or.inr (Or.inr (Or.inl rfl))⟩)))))))))

theorem thm3_twistedA5_two (h2 : q.p = 2) (he : q.exponent = 1) :
    Thm3LieIndex (.twistedA 5 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨q, h2, he, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩)))))))))

theorem thm3_B4_two (h2 : q.p = 2) (he : q.exponent = 1) : Thm3LieIndex (.B 4 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨q, h2, he, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩)))))))))

theorem thm3_D4_two (h2 : q.p = 2) (he : q.exponent = 1) : Thm3LieIndex (.D 4 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨q, h2, he, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩)))))))))

theorem thm3_F4_two (h2 : q.p = 2) (he : q.exponent = 1) : Thm3LieIndex (.F4 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨q, h2, he, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩)))))))))

end Thm3

section Route

variable {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H]

theorem seitzAt_stronglyPEmbedded {d : TauCeti.LieTypeIndex} (hAt : ExtSeitzAt d) (hp5 : 5 ≤ p)
    (S : Subgroup H) [S.Normal] [IsSimpleGroup ↥S] (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    (hiso : IsoLie ↥S d) (hpd : p ≠ d.characteristic)
    (hSc : Subgroup.centralizer (S : Set H) = ⊥) [hout : Group.IsSolvable (Outer ↥S)]
    {Y : Subgroup H} (hY : IsStronglyPEmbedded p Y) {E : Subgroup H} (hEY : E ≤ Y)
    [CFSG.IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2) :
    p = 5 ∧ (d = .tits ∨ d = .suzuki 2) := by
  have hρ := conjNormal_injective_of_centralizer S hSc
  have hE'ab : CFSG.IsElementaryAbelian p (E.map (MulAut.conjNormal (H := S))) :=
    CFSG.IsElementaryAbelian.map _
  have hE'card : Nat.card (E.map (MulAut.conjNormal (H := S))) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hρ, hE]
  rcases hAt ↥S hnab hiso p Fact.out hp5 hpd _ hE'ab hE'card with hgen | hexc
  · exfalso
    refine IsStronglyPEmbedded.false_of_generation hY hEY hE (S := S) ?_
      (solvable_quotient_of_outer S hSc)
    intro s hs
    have hmem : (⟨s, hs⟩ : ↥S) ∈ Subgroup.closure
        {k : ↥S | ∃ F : Subgroup (MulAut ↥S), F ≤ E.map (MulAut.conjNormal (H := S)) ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} := hgen ▸ Subgroup.mem_top _
    have hle : Subgroup.closure
        {k : ↥S | ∃ F : Subgroup (MulAut ↥S), F ≤ E.map (MulAut.conjNormal (H := S)) ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} ≤
        (Subgroup.closure {k : H | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k}).comap S.subtype := by
      rw [Subgroup.closure_le]
      rintro k ⟨F, hFE, hF1, hFk⟩
      obtain ⟨⟨φ, hφF⟩, hφ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF1
      obtain ⟨x, hxE, rfl⟩ := hFE hφF
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hφ1 (Subtype.ext (map_one _))
      refine Subgroup.subset_closure ⟨x, hxE, hx1, ?_⟩
      have h1 := congrArg (fun a : ↥S => (a : H)) (hFk _ hφF)
      simp only [MulAut.conjNormal_apply] at h1
      calc (k : H) * x = x * k * x⁻¹ * x := by rw [h1]
        _ = x * k := by group
    exact hle hmem
  · exact hexc

end Route

end CFSG.RankThree.PartOne.CTP
