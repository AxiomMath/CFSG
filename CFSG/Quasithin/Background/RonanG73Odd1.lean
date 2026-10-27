module

public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.RonanG73

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.Blueprint CFSG.SectionRank


theorem sqt_quotient_center
    {S : Type} [Group S] [Finite S] (hS : IsSQTKCat S)
    (hq : CFSG.IsQuasisimple S) : CFSG.IsStronglyQuasithin (S ⧸ Subgroup.center S) := by
  let φ : S →* S ⧸ Subgroup.center S := QuotientGroup.mk' _
  have hsurj : Function.Surjective (φ.comp (⊤ : Subgroup S).subtype) := by
    intro y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨s, Subgroup.mem_top s⟩, rfl⟩
  let N : Subgroup (⊤ : Subgroup S) := (φ.comp (⊤ : Subgroup S).subtype).ker
  let e : ((⊤ : Subgroup S) ⧸ N) ≃* S ⧸ Subgroup.center S :=
    QuotientGroup.quotientKerEquivOfSurjective _ hsurj
  haveI : IsSimpleGroup (S ⧸ Subgroup.center S) := hq.2.1
  haveI : IsSimpleGroup ((⊤ : Subgroup S) ⧸ N) := e.isSimpleGroup
  have hnonab : ∃ a b : (⊤ : Subgroup S) ⧸ N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  exact isStronglyQuasithin_of_mulEquiv e.symm
    (sqt_catalog_of_simple_section_of_sqtk hS ⊤ N hnonab).1

theorem false_of_exceptional_odd
    {X : Type} [Group X] [Finite X]
    (hX : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 2)
    {t : StatedLieTag} {p f : ℕ} (hp2 : p ≠ 2) (hm : ChevalleyExceptionalModel X t p f) :
    False := by
  obtain ⟨⟨hp, hf, hadm⟩, hm'⟩ := hm
  haveI : Fact p.Prime := ⟨hp⟩
  have hfalse : ∀ r : ℕ, r.Prime → r ≠ 2 → 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) → False :=
    fun r hr hr2 hrk => by
      have := hX r hr hr2
      omega
  cases t with
  | G2 => exact hfalse p hp hp2 (le_trans (by omega) (three_mul_le_pRank_of_G2Model hm'))
  | F4 => exact hfalse p hp hp2 (le_trans (by omega)
      (four_mul_le_pRank_of_untwistedModel (by simp) hm'))
  | E6 => exact hfalse p hp hp2 (le_trans (by omega)
      (four_mul_le_pRank_of_untwistedModel (by simp) hm'))
  | E7 => exact hfalse p hp hp2 (le_trans (by omega)
      (four_mul_le_pRank_of_untwistedModel (by simp) hm'))
  | E8 => exact hfalse p hp hp2 (le_trans (by omega)
      (four_mul_le_pRank_of_untwistedModel (by simp) hm'))
  | twistedE6 => exact hfalse p hp hp2 (le_trans (by norm_num)
      (four_le_pRank_of_twistedE6Model hf hm'))
  | trialityD4 => exact hfalse p hp hp2 (le_trans (by norm_num)
      (four_le_pRank_of_trialityD4Model hf hm'))
  | _ => exact hm'.elim

theorem false_of_ree_odd
    {X : Type} [Group X] [Finite X]
    (hX : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 2)
    {t : StatedLieTag} {p f : ℕ} (hp2 : p ≠ 2) (hm : ReeTitsModel X t p f) : False := by
  have hfalse : ∀ r : ℕ, r.Prime → r ≠ 2 → 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) → False :=
    fun r hr hr2 hrk => by
      have := hX r hr hr2
      omega
  cases t with
  | twistedG2 =>
    obtain ⟨-, hf3, hrk⟩ := smallReeModel_rank hm
    exact hfalse 3 Nat.prime_three (by norm_num) (le_trans (by omega) hrk)
  | twistedF4 =>
    obtain ⟨-, -, -, hp, -⟩ := hm.1
    exact hp2 hp
  | Tits =>
    obtain ⟨-, -, -, hp, -⟩ := hm.1
    exact hp2 hp
  | _ =>
    obtain ⟨-, a, -, hm'⟩ := hm
    exact hm'.elim

theorem odd_model_restriction
    {X : Type} [Group X] [Finite X] (hX : CFSG.IsStronglyQuasithin X)
    (hodd : ∃ (t : StatedLieTag) (n p f : ℕ), p ≠ 2 ∧
      (StatedClassicalModel X t n p f ∨ ChevalleyExceptionalModel X t p f ∨
        ReeTitsModel X t p f)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel X .PSL 2 p f) ∨
        StatedClassicalModel X .PSL 3 p 1 ∨ StatedClassicalModel X .PSU 3 p 1) := by
  obtain ⟨t, n, p, f, hp2, hmod⟩ := hodd
  have hX' := isStronglyQuasithin_iff.1 hX
  rcases hmod with hm | hm | hm
  · have hp : p.Prime := hm.1.1
    refine ⟨p, hp, hp2, ?_⟩
    rcases sqt_odd_classical_restriction hX' hp2 hm with ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨f, hf, hm⟩
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hm)
  · exact (false_of_exceptional_odd hX' hp2 hm).elim
  · exact (false_of_ree_odd hX' hp2 hm).elim

end CFSG.Quasithin.RonanG73
