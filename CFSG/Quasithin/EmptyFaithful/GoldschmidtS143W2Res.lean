module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Gen

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

@[expose] def ResWAny (F : ∀ (L : Type) [Group L], Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
    ∀ (Gc : Type) [Group Gc] [Finite Gc] (ρ : Gc →* MulAut L) (ž : Gc) (Ŝ Kh : Subgroup Gc),
      InspInput ρ ž Ŝ Kh → False

@[expose] def ResW (F : ∀ (L : Type) [Group L], Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
    ∀ (Gc : Type) [Group Gc] [Finite Gc] (ρ : Gc →* MulAut L) (ž : Gc) (Ŝ Kh : Subgroup Gc),
      InspInput ρ ž Ŝ Kh → (∃ z : L, z * z = 1 ∧ ρ ž = MulAut.conj z) → False

theorem resW_of_resWAny {F : ∀ (L : Type) [Group L], Prop} (h : ResWAny F) : ResW F :=
  fun L _ _ hq hF Gc _ _ ρ ž Ŝ Kh hin _ => h L hq hF Gc ρ ž Ŝ Kh hin

theorem resW_of_numFactW {F : ∀ (L : Type) [Group L], Prop} (h : NumFactW F) : ResW F :=
  fun _ _ _ hq hF _ _ _ _ _ _ _ hin hz => false_of_numFactW h hq hF hin hz

theorem resW_of_union {F G' H : ∀ (L : Type) [Group L], Prop}
    (hFGH : ∀ (L : Type) [Group L], F L → G' L ∨ H L) (hG : ResW G') (hH : ResW H) : ResW F := by
  intro L _ _ hq hFL Gc _ _ ρ ž Ŝ Kh hin hz
  rcases hFGH L hFL with h | h
  · exact hG L hq h Gc ρ ž Ŝ Kh hin hz
  · exact hH L hq h Gc ρ ž Ŝ Kh hin hz

theorem resWAny_of_union {F G' H : ∀ (L : Type) [Group L], Prop}
    (hFGH : ∀ (L : Type) [Group L], F L → G' L ∨ H L) (hG : ResWAny G') (hH : ResWAny H) :
    ResWAny F := by
  intro L _ _ hq hFL Gc _ _ ρ ž Ŝ Kh hin
  rcases hFGH L hFL with h | h
  · exact hG L hq h Gc ρ ž Ŝ Kh hin
  · exact hH L hq h Gc ρ ž Ŝ Kh hin

theorem resW_cover {F G' : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      G' (L ⧸ Subgroup.center L)) (hG : ResW G') : ResW F := by
  intro L _ _ hq hFL Gc _ _ ρ ž Ŝ Kh hin hz
  obtain ⟨z, hz2, hž⟩ := hz
  obtain ⟨ρb, hρb, hinnb, hžb, hqb, -⟩ := cover_data hq ρ hin.inj hin.inn
  exact hG (L ⧸ Subgroup.center L) hqb (hF L hq hFL) Gc ρb ž Ŝ Kh
    { hin with inj := hρb, inn := hinnb }
    ⟨QuotientGroup.mk z, by rw [← QuotientGroup.mk_mul, hz2, QuotientGroup.mk_one],
      hžb ž z hž⟩

theorem resWAny_cover {F G' : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      G' (L ⧸ Subgroup.center L)) (hG : ResWAny G') : ResWAny F := by
  intro L _ _ hq hFL Gc _ _ ρ ž Ŝ Kh hin
  obtain ⟨ρb, hρb, hinnb, -, hqb, -⟩ := cover_data hq ρ hin.inj hin.inn
  exact hG (L ⧸ Subgroup.center L) hqb (hF L hq hFL) Gc ρb ž Ŝ Kh
    { hin with inj := hρb, inn := hinnb }

theorem resWAny_of_not_dvd_aut {F : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      ¬ 2 ^ 5 ∣ Nat.card (MulAut L)) : ResWAny F := by
  intro L _ _ hq hFL Gc _ _ ρ ž Ŝ Kh hin
  apply hF L hq hFL
  have h1 : Nat.card Gc ∣ Nat.card (MulAut L) := by
    rw [← Nat.card_range_of_injective hin.inj]
    exact Subgroup.card_subgroup_dvd_card ρ.range
  have h2 : Nat.card Ŝ ∣ Nat.card Gc := Subgroup.card_subgroup_dvd_card Ŝ
  have h3 : 2 ^ 5 ∣ Nat.card Ŝ := by
    rcases hin.card_S with h | h
    · rw [h]
    · rw [h]
      exact pow_dvd_pow 2 (by norm_num)
  exact h3.trans (h2.trans h1)

end InspW2

end S143

end CFSG.Quasithin
