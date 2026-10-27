module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeTorality
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreePure
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeInn
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeReduce

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly

section Medium


variable {K : Type} [Field K] [Finite K] {n : ℕ} {L' : Type} [Group L'] [Finite L']
  {ψ : L' →* TwE6Delta.RecipeR K n} {A As : Subgroup (MulAut L')}

theorem Cfg.card_le_three_mul_inf_conj (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h : Cfg ψ A As) (hI : ∀ a ∈ As, Induces ψ a) :
    Nat.card As ≤ 3 * Nat.card
      (As ⊓ (MulAut.conj : L' →* MulAut L').range : Subgroup (MulAut L')) := by
  have hZ := TwE6Delta.center_recipeR_eq_bot hn hK
  have hinj := ggIE_indAutHom_injective h.surj hZ h.ker_le h.perfect
  have hsub : ((As.map (ggIE_indAutHom h.surj hZ h.ker_le) :
      Subgroup (MulAut (TwE6Delta.RecipeR K n))) : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆
        TwE6Delta.RecipeI K n := by
    rintro _ ⟨a, ha, rfl⟩
    exact rho_mem_recipeI h.surj hZ h.ker_le (hI a ha)
  have h1 := recipe_inn_index hn hK hsub
  have h2 : (As.map (ggIE_indAutHom h.surj hZ h.ker_le)) ⊓
      (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range =
      (As ⊓ (MulAut.conj : L' →* MulAut L').range).map (ggIE_indAutHom h.surj hZ h.ker_le) := by
    ext φ
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hmem⟩
      exact ⟨a, ⟨ha, (rho_mem_range_conj_iff h.surj hZ h.ker_le h.perfect a).1 hmem⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hai⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, (rho_mem_range_conj_iff h.surj hZ h.ker_le h.perfect a).2 hai⟩
  rw [h2, Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective hinj] at h1
  exact h1

theorem Cfg.false_of_caseI_Rtype (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h : Cfg ψ A As)
    (hI : ∀ a ∈ As, Induces ψ a) (hZ1 : Nat.card (Subgroup.center L') = 1) : False := by
  have hB2 := h.card_le_three_mul_inf_conj hn hK hI
  have hmul := ggIE_mul_card_le Nat.prime_three h.hA h.hAs h.lt
  have hinj := conj_injective_of_center_card_eq_one hZ1
  have hE : IsElemAbelian 3 (lam As) := isElemAbelian_comap_of_injective hinj h.hAs
  have hEcard : Nat.card (lam As) = Nat.card
      (As ⊓ (MulAut.conj : L' →* MulAut L').range : Subgroup (MulAut L')) := by
    have h1 : (As.comap (MulAut.conj : L' →* MulAut L')).map (MulAut.conj : L' →* MulAut L') =
        (MulAut.conj : L' →* MulAut L').range ⊓ As := Subgroup.map_comap_eq _ _
    have h2 := Subgroup.card_map_of_injective (f := (MulAut.conj : L' →* MulAut L'))
      (K := As.comap (MulAut.conj : L' →* MulAut L')) hinj
    rw [h1, inf_comm] at h2
    exact h2.symm
  refine false_of_fixed h.adm hE ?_ ?_
  · intro a ha e he
    have hcomm : a * MulAut.conj e = MulAut.conj e * a :=
      TableB.IsElemAbelian.comm h.hAs (h.lt.le ha) (Subgroup.mem_comap.1 he)
    apply hinj
    rw [conj_apply_aut, hcomm, mul_inv_cancel_right]
  · rw [hZ1, one_mul, hEcard]
    omega

theorem Cfg.false_of_caseF_Rtype (hB1 : RankFiveInnInput) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h9 : 9 ∣ 2 ^ n + 1) (h : Cfg ψ A As)
    (h5 : 3 ^ 5 ≤ Nat.card A) (hZ1 : Nat.card (Subgroup.center L') = 1) : False := by
  have hZ := TwE6Delta.center_recipeR_eq_bot hn hK
  have hinj := ggIE_indAutHom_injective h.surj hZ h.ker_le h.perfect
  have hX := ggIE_isElemAbelian_map (ggIE_indAutHom h.surj hZ h.ker_le) h.hA
  have hXI : ((A.map (ggIE_indAutHom h.surj hZ h.ker_le) :
      Subgroup (MulAut (TwE6Delta.RecipeR K n))) : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆
        TwE6Delta.RecipeI K n := by
    rintro _ ⟨a, ha, rfl⟩
    exact rho_mem_recipeI h.surj hZ h.ker_le (h.induces a ha)
  have hXc : 3 ^ 5 ≤ Nat.card (A.map (ggIE_indAutHom h.surj hZ h.ker_le)) := by
    rw [Subgroup.card_map_of_injective hinj]
    exact h5
  have hXinn := hB1 K n hn hK h9 _ hX hXI hXc
  have hAinn : ∀ a ∈ A, a ∈ (MulAut.conj : L' →* MulAut L').range := fun a ha =>
    (rho_mem_range_conj_iff h.surj hZ h.ker_le h.perfect a).1 (hXinn ⟨a, ha, rfl⟩)
  obtain ⟨-, hcase⟩ := h.adm
  rcases hcase with ⟨⟨a, ha, hna⟩, -⟩ | ⟨hdvd, -⟩
  · exact hna (hAinn a ha)
  · rw [hZ1] at hdvd
    exact absurd (Nat.le_of_dvd one_pos hdvd) (by norm_num)

end Medium

section Free

variable {K : Type} [Field K] [Finite K] {n : ℕ} {L' : Type} [Group L'] [Finite L']
  {ψ : L' →* TwE6Delta.RecipeR K n} {A As : Subgroup (MulAut L')}

theorem Cfg.false_of_caseF_Utype_five (hNine : TorusLiftNineInput) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) (h9 : 9 ∣ 2 ^ n + 1) (h : Cfg ψ A As)
    (hZ3 : Nat.card (Subgroup.center L') = 3) (hA5 : Nat.card A = 3 ^ 5) : False := by
  obtain ⟨E, hE, hEc, hfix⟩ := hNine K n hn hK h3 h9 L' ψ h.surj h.ker_le h.perfect hZ3 A h.hA
    hA5.ge fun a ha => h.induces a ha
  refine false_of_fixed h.adm hE hfix ?_
  rw [hZ3, hA5]
  calc 3 * 3 ^ 5 = 3 ^ 6 := by norm_num
    _ ≤ Nat.card E := hEc

theorem Cfg.false_of_caseI_Utype (hSix : TorusLiftSixInput) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) (h : Cfg ψ A As)
    (hI : ∀ a ∈ As, Induces ψ a) (hZ3 : Nat.card (Subgroup.center L') = 3)
    (hA5 : Nat.card A = 3 ^ 5) (hAs6 : Nat.card As = 3 ^ 6) : False := by
  obtain ⟨E, hE, hEc, hfix⟩ := hSix K n hn hK h3 L' ψ h.surj h.ker_le h.perfect hZ3 As h.hAs
    hAs6 hI
  refine false_of_fixed h.adm hE (fun a ha e he => hfix a (h.lt.le ha) e he) ?_
  rw [hZ3, hA5]
  calc 3 * 3 ^ 5 = 3 ^ 6 := by norm_num
    _ ≤ Nat.card E := hEc

end Free

section Big


variable {K : Type} [Field K] [Finite K] {n : ℕ} {L' : Type} [Group L'] [Finite L']
  {ψ : L' →* TwE6Delta.RecipeR K n} {A As : Subgroup (MulAut L')}

theorem Cfg.card_eq_five_or_six (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) (h : Cfg ψ A As) : Nat.card A = 3 ^ 5 ∨ Nat.card A = 3 ^ 6 := by
  have h5 := h.five_le_card hn hK h3
  have hZ := TwE6Delta.center_recipeR_eq_bot hn hK
  have hinj := ggIE_indAutHom_injective h.surj hZ h.ker_le h.perfect
  have hEl := ggIE_isElemAbelian_map (ggIE_indAutHom h.surj hZ h.ker_le) h.hA
  have hsub : ((A.map (ggIE_indAutHom h.surj hZ h.ker_le) :
      Subgroup (MulAut (TwE6Delta.RecipeR K n))) : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆
        TwE6Delta.RecipeI K n := by
    rintro _ ⟨a, ha, rfl⟩
    exact rho_mem_recipeI h.surj hZ h.ker_le (h.induces a ha)
  have h6 := ggTwE6ThreeInndiagRankInput_holds K n hn hK h3 _ hEl hsub
  rw [Subgroup.card_map_of_injective hinj] at h6
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (TableB.isPGroup_of_isElemAbelian h.hA)
  rw [hk] at h5 h6 ⊢
  have hk5 : 5 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).1 h5
  have hk6 : k ≤ 6 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h6
  have : k = 5 ∨ k = 6 := by omega
  rcases this with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end Big

end CFSG.StandardType.TwE6D3
