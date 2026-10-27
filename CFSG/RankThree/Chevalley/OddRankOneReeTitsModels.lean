module

public import CFSG.RankThree.Chevalley.OddRankOneExceptionalModel
public import CFSG.LocalAnalysis.SectionRank.LargeRee.Torus
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Assembly.LowTwoRank CFSG.SectionRank.LargeRee

theorem exists_two_le_pRank_of_largeReeModel {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ReeTitsModel S .twistedF4 p f) : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S := by
  obtain ⟨K, _, _, _, a, ha, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model h
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one (f := 2 * a + 1) (by omega)
  let T₀ := reeTorusHom a hK fi_zero_mem_longSet
  let T₁ := reeTorusHom a hK fi_one_mem_longSet
  have hcomm : ∀ u v, Commute (T₀ u) (T₁ v) := fun u v =>
    commute_of_mem_reeTorusPart (reeTorusSub_le_reeTorusPart hK _ ⟨u, rfl⟩)
      (reeTorusSub_le_reeTorusPart hK _ ⟨v, rfl⟩)
  have hchar1 : ∀ k, simpleChar (1 : adjointGroup ReeTag.F4.tag K) k = 1 := fun k => by
    simp [simpleChar]
  have hT₀ : ∀ u, T₀ u = 1 → u = 1 := fun u hu => by
    have h1 : ReeTag.F4.reeTorus a (fi 0) u = 1 := congrArg Subtype.val hu
    have h2 := congrArg (fun g => simpleChar g (fi 0)) h1
    simp only [simpleChar_reeTorus, reeExp_zero_zero, hchar1] at h2
    have h3 : ((u : K)) ^ 2 = 1 ^ 2 := by
      rw [one_pow, ← Units.val_pow_eq_pow_val, ← zpow_natCast]
      exact h2
    exact Units.ext (CharTwo.sq_injective h3)
  have hT₁ : ∀ v, T₁ v = 1 → v = 1 := fun v hv => by
    have h1 : ReeTag.F4.reeTorus a (fi 1) v = 1 := congrArg Subtype.val hv
    have h2 := congrArg (fun g => simpleChar g (fi 0)) h1
    simp only [simpleChar_reeTorus, reeExp_one_zero, hchar1] at h2
    have h3 : v⁻¹ = 1 := Units.ext (by rw [← zpow_neg_one]; exact h2)
    exact inv_eq_one.1 h3
  let Ψ : Kˣ × Kˣ →* reeFixed ReeTag.F4 K a := MonoidHom.noncommCoprod T₀ T₁ hcomm
  have hΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, v⟩ huv
    have h1 : T₀ u * T₁ v = 1 := huv
    have hmem : T₀ u ∈ reeTorusSub a hK fi_zero_mem_longSet ⊓
        reeTorusSub a hK fi_one_mem_longSet :=
      ⟨⟨u, rfl⟩, ⟨v⁻¹, by rw [map_inv]; exact (eq_inv_of_mul_eq_one_left h1).symm⟩⟩
    rw [reeTorusSub_inf hK, Subgroup.mem_bot] at hmem
    have hu := hT₀ u hmem
    rw [hmem, one_mul] at h1
    have hv := hT₁ v h1
    rw [hu, hv]
    rfl
  have hcard : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hrd
  exact ⟨r, hr, hr2, two_le_pRank_of_injective_prod hr hcard hcard
    (e.symm.toMonoidHom.comp Ψ) (e.symm.injective.comp hΨ)⟩

theorem two_le_pRank_five_of_titsModel {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ReeTitsModel S .Tits p f) : 2 ≤ CFSG.pRank 5 S := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model h
  obtain ⟨x, y, -, hx, hy, hxy, hcard, -⟩ := CFSG.SectionRank.Tits_sylow5_square_witness (K := K) hK
  let D := commutator (reeFixed ReeTag.F4 K 0)
  have hgen : ∀ a ∈ ({x, y} : Set D), ∀ b ∈ ({x, y} : Set D), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
    · exact hxy
    · exact hxy.symm
  have hcomm : ∀ a ∈ Subgroup.closure ({x, y} : Set D), ∀ b ∈ Subgroup.closure ({x, y} : Set D),
      a * b = b * a :=
    closure_commute hgen
  have hpow : ∀ z ∈ Subgroup.closure ({x, y} : Set D), z ^ 5 = 1 := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem w hw =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw <;> rw [hw]
      · exact hx
      · exact hy
    | one => exact one_pow 5
    | mul a b ha hb iha ihb =>
      rw [Commute.mul_pow (show Commute a b from hcomm a ha b hb), iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hE : CFSG.Open.IsElemAbelian 5 (Subgroup.closure ({x, y} : Set D)) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hpow⟩
  have h2 : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup D) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE hcard
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact h2

theorem odd_rank_one_excludes_all_Ree_Tits_models (S : Type) [Group S] [Finite S]
    (hS : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r S ≤ 1) (t : StatedLieTag) (p f : ℕ) :
    ¬ ReeTitsModel S t p f := by
  intro h
  have hex : ∀ r : ℕ, r.Prime → r ≠ 2 → 2 ≤ CFSG.pRank r S → False := fun r hr hr2 h2 => by
    have := hS r hr hr2
    omega
  cases t
  case twistedG2 =>
    obtain ⟨-, hf3, hrk⟩ := CFSG.SectionRank.smallReeModel_rank h
    exact hex 3 Nat.prime_three (by norm_num)
      (by rw [CFSG.SectionRank.pRank_eq_open_pRank_top]; omega)
  case twistedF4 =>
    obtain ⟨r, hr, hr2, h2⟩ := exists_two_le_pRank_of_largeReeModel h
    exact hex r hr hr2 h2
  case Tits => exact hex 5 (by norm_num) (by norm_num) (two_le_pRank_five_of_titsModel h)
  all_goals exact (h.2.choose_spec.2 : False).elim

end CFSG.RankThree.Chevalley
