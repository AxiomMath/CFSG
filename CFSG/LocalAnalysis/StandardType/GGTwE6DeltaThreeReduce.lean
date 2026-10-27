module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeDefs
import CFSG.LocalAnalysis.StandardType.GGIOneExcOuterTwE6
import CFSG.LocalAnalysis.StandardType.GGTwE6LangThree
import CFSG.LocalAnalysis.StandardType.GGSmallKGInputsTwE6
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly

section Pure

variable {K : Type} [Field K] [Finite K] {n : ℕ} {L' : Type} [Group L']
  {ψ : L' →* TwE6Delta.RecipeR K n} {A As : Subgroup (MulAut L')}

theorem Cfg.odd_center [Finite L'] (h : Cfg ψ A As) :
    Odd (Nat.card (Subgroup.center L')) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center L') := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.center L')) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L') 2 h2
  let U : Subgroup L' :=
    { carrier := {x | x ∈ Subgroup.center L' ∧ x ^ 2 = 1}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨mul_mem hx.1 hy.1, ?_⟩
        have hc : Commute x y := (Subgroup.mem_center_iff.mp hx.1 y).symm
        rw [hc.mul_pow, hx.2, hy.2, one_mul]
      one_mem' := ⟨one_mem _, one_pow 2⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hzU : (z : L') ∈ U := ⟨z.2, by
    have h1 := pow_orderOf_eq_one z
    rw [hz] at h1
    exact congrArg Subtype.val h1⟩
  have hz1 : (z : L') ≠ 1 := by
    intro h1
    have h2' : z = 1 := Subtype.ext h1
    rw [h2', orderOf_one] at hz
    omega
  have hU1 : U ≠ ⊥ := fun hb => by
    rw [hb] at hzU
    exact hz1 (Subgroup.mem_bot.mp hzU)
  have hU2 : IsPGroup 2 U := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext g.2.2⟩
  have hinv : ∀ a ∈ As, ∀ u ∈ U, a u ∈ U := by
    intro a _ u hu
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      have h1 := Subgroup.mem_center_iff.mp hu.1 (a⁻¹ g)
      have h2' : a (a⁻¹ g * u) = a (u * a⁻¹ g) := by rw [h1]
      rw [map_mul, map_mul, MulAut.apply_inv_self] at h2'
      exact h2'
    · rw [← map_pow, hu.2, map_one]
  exact hU1 (h.none As h.lt le_rfl U hU2 hinv)

theorem Cfg.induces_iff_mem [Finite L'] (h : Cfg ψ A As)
    (hF : ∃ a ∈ As, ¬ Induces ψ a) : ∀ a ∈ As, Induces ψ a ↔ a ∈ A := by
  intro a ha
  refine ⟨fun hind => ?_, fun haA => h.induces a haA⟩
  set S : Subgroup (MulAut L') := As ⊓ inducedSub ψ with hS
  have hAS : A ≤ S := fun x hx => ⟨h.lt.le hx, mem_inducedSub.2 (h.induces x hx)⟩
  have hSel : IsElemAbelian 3 S := TableB.isElemAbelian_mono h.hAs inf_le_left
  have hSA : S ≤ A := by
    by_contra hnle
    have hlt : A < S := lt_of_le_of_ne hAS (fun heq => hnle (heq ▸ le_rfl))
    have hSs : S < As := by
      refine lt_of_le_of_ne inf_le_left (fun heq => ?_)
      obtain ⟨b, hb, hnb⟩ := hF
      have hbS : b ∈ S := by rw [heq]; exact hb
      exact hnb (mem_inducedSub.1 hbS.2)
    have h1 := ggIE_mul_card_le Nat.prime_three h.hA hSel hlt
    have h2 := ggIE_mul_card_le Nat.prime_three hSel h.hAs hSs
    have h3 := h.card_le
    have hpos : 0 < Nat.card A := Nat.card_pos
    omega
  exact hSA ⟨ha, mem_inducedSub.2 hind⟩

end Pure

section Cover


variable {K : Type} [Field K] [Finite K] {n : ℕ} {L' : Type} [Group L'] [Finite L']
  {ψ : L' →* TwE6Delta.RecipeR K n} {A As : Subgroup (MulAut L')}

theorem Cfg.five_le_card (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    (h : Cfg ψ A As) : 3 ^ 5 ≤ Nat.card A := by
  obtain ⟨⟨E5, hE5, hE5c⟩, hC6⟩ := ggTwE6ThreeCoverRankInput_holds K n hn hK h3 L' ψ h.surj
    h.ker_le h.perfect
  obtain ⟨-, hcase⟩ := h.adm
  rcases hcase with ⟨-, hb⟩ | ⟨hz, hb, -⟩
  · exact hE5c.trans (hb E5 hE5)
  · obtain ⟨E6, hE6, hE6c⟩ := hC6 (Or.inr hz)
    refine Nat.le_of_mul_le_mul_left ?_ (by norm_num : 0 < 3)
    calc 3 * 3 ^ 5 = 3 ^ 6 := by norm_num
      _ ≤ Nat.card E6 := hE6c
      _ ≤ 3 * Nat.card A := hb E6 hE6

end Cover

section Outer


variable {K : Type} [Field K] [Finite K] {n : ℕ} {L' : Type} [Group L'] [Finite L']
  {ψ : L' →* TwE6Delta.RecipeR K n} {A As : Subgroup (MulAut L')}

theorem Cfg.three_dvd_of_not_induces (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) (h : Cfg ψ A As) {a : MulAut L'} (ha : a ∈ As)
    (hna : ¬ Induces ψ a) : 3 ∣ n := by
  have hZ := TwE6Delta.center_recipeR_eq_bot hn hK
  refine ggTwE6OuterPowInput_holds K n 3 hn hK Nat.prime_three h3
    (ggIE_indAutHom h.surj hZ h.ker_le a) ?_ ?_
  · rw [← map_pow, h.hAs.2 a ha, map_one]
  · intro hI
    exact hna ⟨_, hI, fun l => ggIE_indAut_apply h.surj hZ h.ker_le a l⟩

theorem Cfg.card_of_caseI (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    (h5 : 3 ^ 5 ≤ Nat.card A) (h : Cfg ψ A As) (hI : ∀ a ∈ As, Induces ψ a) :
    Nat.card A = 3 ^ 5 ∧ Nat.card As = 3 ^ 6 := by
  have hZ := TwE6Delta.center_recipeR_eq_bot hn hK
  have hinj := ggIE_indAutHom_injective h.surj hZ h.ker_le h.perfect
  have hEl : IsElemAbelian 3 (As.map (ggIE_indAutHom h.surj hZ h.ker_le)) :=
    ggIE_isElemAbelian_map _ h.hAs
  have hsub : ((As.map (ggIE_indAutHom h.surj hZ h.ker_le) : Subgroup _) :
      Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφ, hφa⟩ := hI a ha
    have h1 := ggIE_eq_indAut_of_forall h.surj hZ h.ker_le hφa
    show ggIE_indAut h.surj hZ h.ker_le a ∈ TwE6Delta.RecipeI K n
    rw [← h1]
    exact hφ
  have h6 := ggTwE6ThreeInndiagRankInput_holds K n hn hK h3 _ hEl hsub
  rw [Subgroup.card_map_of_injective hinj] at h6
  have hmul := ggIE_mul_card_le Nat.prime_three h.hA h.hAs h.lt
  have e5 : (3 : ℕ) ^ 5 = 243 := by norm_num
  have e6 : (3 : ℕ) ^ 6 = 729 := by norm_num
  rw [e5] at h5 ⊢
  rw [e6] at h6 ⊢
  constructor <;> omega

end Outer

end CFSG.StandardType.TwE6D3
