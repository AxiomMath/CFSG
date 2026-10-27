module

public import CFSG.Quasithin.H13.NQCatLieCentralCore
public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelInterface

public section

namespace CFSG.Quasithin.H13.NQCat.LieCentral

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender
  CFSG.Blueprint CFSG.LieType.Ree

theorem centralIndex_linear {K : Type} [Group K] [Finite K] {n : ℕ} (h : BenderType K n 1 1) :
    CentralIndex K := by
  obtain ⟨hn, ⟨e⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSL2Model n) := by
    cases h with
    | linear n hn e => exact ⟨hn, ⟨e⟩⟩
  intro P hP x hx _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : ¬ 2 ∣ P.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hP.2.2
  obtain ⟨t, hc⟩ := exists_benderCore_psl2 e hn (hP.2.1.toSylow hP')
  rw [IsPGroup.toSylow_coe] at hc
  have hPZ : rootCenter P = P :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc.card_center, hc.card_eq, pow_one])
  rw [← hPZ] at hx
  exact hx.2

theorem centralIndex_suzuki {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CentralIndex (suzukiGroup a K) := by
  obtain ⟨h2, -, hθθ⟩ := suzuki_frob_data a hK
  have hUP := CFSG.LocalAnalysis.ComponentInitial.suzukiU_isPGroup_index hK
  have hU : IsSylowTwoOf (suzukiU a K) ⊤ :=
    ⟨le_top, hUP.1, by rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]; exact hUP.2⟩
  refine centralIndex_of_sylow hU fun x hx hidx => ?_
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  by_cases hu : u = 0
  · subst hu
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hy
    exact (suzukiSElt_zero_commute hK v c d).symm
  exfalso
  have hC : ∀ c d : K, suzukiSElt a K c d * suzukiSElt a K u v =
      suzukiSElt a K u v * suzukiSElt a K c d → c = 0 ∨ c = u := by
    intro c d hcd
    rw [suzukiSElt_mul hK, suzukiSElt_mul hK, suzukiSElt_inj] at hcd
    have h1 : c ^ 2 ^ (a + 1) * u = u ^ 2 ^ (a + 1) * c := by linear_combination hcd.2
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    have hl : (c / u) ^ 2 ^ (a + 1) = c / u := by
      rw [div_pow, div_eq_div_iff (pow_ne_zero _ hu) hu, h1, mul_comm]
    have hl2 : (c / u) ^ 2 = c / u := by rw [← hθθ, hl, hl]
    have hl3 : c / u = 1 := by
      have h3 : c / u * (c / u - 1) = 0 := by linear_combination hl2
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left (div_ne_zero hc hu))
    exact (div_eq_one_iff_eq hu).1 hl3
  have hcardC : Nat.card ↥(suzukiU a K ⊓ Subgroup.centralizer ({suzukiSElt a K u v} :
      Set (suzukiGroup a K))) ≤ 2 * Nat.card K := by
    classical
    have hcoord : ∀ y : ↥(suzukiU a K ⊓ Subgroup.centralizer ({suzukiSElt a K u v} :
        Set (suzukiGroup a K))), ∃ c d : K, (y : suzukiGroup a K) = suzukiSElt a K c d ∧
          (c = 0 ∨ c = u) := by
      intro y
      obtain ⟨hyU, hyx⟩ := Subgroup.mem_inf.1 y.2
      obtain ⟨c, d, hcd⟩ := (mem_suzukiU_iff hK).1 hyU
      rw [Subgroup.mem_centralizer_singleton_iff, ← hcd] at hyx
      exact ⟨c, d, hcd.symm, hC c d hyx⟩
    choose c d hcd hc using hcoord
    have hinj : Function.Injective fun y =>
        ((⟨c y, by rcases hc y with h | h <;> simp [h]⟩ : ↥({0, u} : Set K)), d y) := by
      intro y y' hyy
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hyy
      exact Subtype.ext (by rw [hcd y, hcd y', hyy.1, hyy.2])
    calc _ ≤ Nat.card (↥({0, u} : Set K) × K) := Nat.card_le_card_of_injective _ hinj
      _ = 2 * Nat.card K := by
        rw [Nat.card_prod, Nat.card_coe_set_eq, Set.ncard_pair (Ne.symm hu)]
  have h3 := Subgroup.relIndex_mul_card (suzukiU a K ⊓ Subgroup.centralizer
    ({suzukiSElt a K u v} : Set (suzukiGroup a K))) (suzukiU a K)
  rw [inf_assoc, inf_comm (Subgroup.centralizer _), ← inf_assoc, inf_idem,
    (suzuki_unipotent_structure hK).2.1] at h3
  have h4 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hK] at hcardC
  nlinarith

end CFSG.Quasithin.H13.NQCat.LieCentral
