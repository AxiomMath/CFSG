module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightDF
public import CFSG.GroupTheory.BinaryFixedFreeRank
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}
  {z k a : MulAut W} {N : Subgroup (MulAut W)}

private theorem w16g_orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (x := (2 : ZMod 3)) (p := 2) (by decide) (by decide)

private theorem w16g_odd_card_zpowers_z (hD : Data8 A t z N) :
    Odd (Nat.card ↥(Subgroup.zpowers z)) := by
  rw [Nat.card_zpowers, hD.hz3]
  norm_num

private theorem w16g_s13Comp8_inf_fixV_zpowers (h : Cfg133 A t 3) (hD : Data8 A t z N)
    (i : Fin 3) :
    s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ))) ⊓ fixV (Subgroup.zpowers z) = ⊥ := by
  have hoddz := w16g_odd_card_zpowers_z hD
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.hW w
  rw [s13Comp8]
  apply le_bot_iff.mp
  calc (commSub ⊤ N ⊓ fixV (Subgroup.zpowers (k * z ^ (i : ℕ)))) ⊓
        fixV (Subgroup.zpowers z)
      ≤ commSub ⊤ N ⊓ fixV (Subgroup.zpowers z) := inf_le_inf_right _ inf_le_left
    _ = commSub ⊤ (Subgroup.zpowers z) ⊓ fixV (Subgroup.zpowers z) := by rw [hD.hNV]
    _ = fixV (Subgroup.zpowers z) ⊓ commSub ⊤ (Subgroup.zpowers z) := inf_comm _ _
    _ = ⊥ := CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW2 hoddz

theorem s13_eight_comp_irr (h : Cfg133 A t 3) (hD : Data8 A t z N) (hG : Gen8 A t z N k a)
    (i : Fin 3) : IsIrrOn N (s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ)))) ⊥ := by
  let R : Subgroup (MulAut W) := Subgroup.zpowers (k * z ^ (i : ℕ))
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.hW w
  have hfixz := w16g_s13Comp8_inf_fixV_zpowers (k := k) h hD i
  have hrkC : rk ↥(s13Comp8 N R) = 2 := by
    change rk ↥(s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ)))) = 2
    exact (s13_eight_decomp h hD hG).2.2 i
  have hRleN : R ≤ N := by
    change Subgroup.zpowers (k * z ^ (i : ℕ)) ≤ N
    refine Subgroup.zpowers_le.mpr ?_
    exact N.mul_mem hG.hkN (N.pow_mem hD.hzN _)
  have hCstab : StableUnder N (s13Comp8 N R) := by
    rw [s13Comp8]
    refine stableUnder_inf ?_ ?_
    · refine stableUnder_commSub ?_ (fun _ _ _ _ => Subgroup.mem_top _)
      intro y hy x hx
      exact N.mul_mem (N.mul_mem hy hx) (N.inv_mem hy)
    · refine stableUnder_fixV ?_
      intro y hy r hr
      have hrN : r ∈ N := hRleN hr
      have hyr : y * r = r * y :=
        congrArg Subtype.val
          ((w16g_isElemAbelianOfRank_comm_pow hD.hN).1 ⟨y, hy⟩ ⟨r, hrN⟩)
      have h : y * r * y⁻¹ = r := by rw [hyr, mul_assoc, mul_inv_cancel, mul_one]
      simpa [h] using hr
  have hbotstab : StableUnder N (⊥ : Subgroup W) := by
    intro x hx u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  have hCne : s13Comp8 N R ≠ ⊥ := by
    intro hbot
    have h0 : rk ↥(s13Comp8 N R) = 0 := by rw [hbot, rk_bot]
    omega
  refine ⟨bot_lt_iff_ne_bot.mpr hCne, hCstab, hbotstab, ?_⟩
  intro J hJstab hbotJ hJle
  by_cases hJ : J = ⊥
  · exact Or.inl hJ
  · refine Or.inr ?_
    have hJfixz : J ⊓ fixV (Subgroup.zpowers z) = ⊥ := by
      apply le_bot_iff.mp
      calc J ⊓ fixV (Subgroup.zpowers z)
          ≤ s13Comp8 N R ⊓ fixV (Subgroup.zpowers z) := inf_le_inf_right _ hJle
        _ = ⊥ := hfixz
    have hzstabJ : StableUnder (Subgroup.zpowers z) J :=
      fun x hx => hJstab x (Subgroup.zpowers_le.mpr hD.hzN hx)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hYp : IsPGroup 3 ↥(Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hD.hz3, pow_one])
    have hdvd : orderOf (2 : ZMod 3) ∣ rk ↥J :=
      CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot hW2 hYp hzstabJ hJfixz
    have hd3 : orderOf (2 : ZMod 3) = 2 := w16g_orderOf_two_zmod_three
    have hdvd2 : 2 ∣ rk ↥J := by simpa [hd3] using hdvd
    obtain ⟨m, hm⟩ := hdvd2
    have hrk_le : rk ↥J ≤ 2 := by
      calc rk ↥J ≤ rk ↥(s13Comp8 N R) := rk_mono hJle
        _ = 2 := hrkC
    have hJpos : 0 < rk ↥J := by
      apply Nat.pos_of_ne_zero
      intro h0
      exact hJ ((rk_eq_zero_iff hW2).mp h0)
    have hrkJ : rk ↥J = 2 := by omega
    exact eq_of_le_of_rk_le hW2 hJle (by rw [hrkC, hrkJ])

theorem s13_eight_comp_isotypic (h : Cfg133 A t 3) (hD : Data8 A t z N) (hG : Gen8 A t z N k a)
    (i : Fin 3) : IsEntireIsotypic N (s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ)))) := by
  let R : Subgroup (MulAut W) := Subgroup.zpowers (k * z ^ (i : ℕ))
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.hW w
  have hoddz := w16g_odd_card_zpowers_z hD
  have hfixz := w16g_s13Comp8_inf_fixV_zpowers (k := k) h hD i
  have hRleN : R ≤ N := by
    change Subgroup.zpowers (k * z ^ (i : ℕ)) ≤ N
    refine Subgroup.zpowers_le.mpr ?_
    exact N.mul_mem hG.hkN (N.pow_mem hD.hzN _)
  have hirrC : IsIrrOn N (s13Comp8 N R) ⊥ := by
    change IsIrrOn N (s13Comp8 N (Subgroup.zpowers (k * z ^ (i : ℕ)))) ⊥
    exact s13_eight_comp_irr h hD hG i
  intro V₁ V₀ hV₀U hirr₀ hirr₁ hsec
  have hV₀eqC : V₀ = s13Comp8 N R := by
    rcases hirrC.2.2.2 V₀ hirr₀.2.1 bot_le hV₀U with h | h
    · exfalso
      rw [h] at hirr₀
      exact lt_irrefl ⊥ hirr₀.1
    · exact h
  have hV₀fixR : V₀ ≤ fixV R := by
    rw [hV₀eqC]
    exact inf_le_right
  have hV₀botz : V₀ ⊓ fixV (Subgroup.zpowers z) = ⊥ := by
    rw [hV₀eqC]
    exact hfixz
  obtain ⟨-, -, -, -, -, -, β, hβV₀, hβiff, -, hβeq⟩ := hsec
  have hβone : ∀ a : ↥V₁, β a = 1 ↔ (a : W) = 1 := fun a => by simpa using hβiff a
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by
      calc β (a * b⁻¹) = β a * (β b)⁻¹ := by rw [map_mul, map_inv]
        _ = β b * (β b)⁻¹ := by rw [hab]
        _ = 1 := mul_inv_cancel _
    have h2 : ((a * b⁻¹ : ↥V₁) : W) = 1 := (hβone (a * b⁻¹)).mp h1
    exact Subtype.ext (mul_inv_eq_one.mp (by simpa using h2))
  have hV₁botz : V₁ ⊓ fixV (Subgroup.zpowers z) = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hβfix : β ⟨v, hv.1⟩ ∈ fixV (Subgroup.zpowers z) := by
      rw [mem_fixV]
      intro zz hz
      have h1 : β ⟨v, hv.1⟩ * (zz (β ⟨v, hv.1⟩))⁻¹ ∈ (⊥ : Subgroup W) := by
        refine hβeq zz (Subgroup.zpowers_le.mpr hD.hzN hz) ⟨v, hv.1⟩ ⟨v, hv.1⟩ ?_
        exact (mem_fixV.mp hv.2 zz hz).symm
      exact (mul_inv_eq_one.mp (by simpa using h1)).symm
    have hmem : β ⟨v, hv.1⟩ ∈ V₀ ⊓ fixV (Subgroup.zpowers z) := ⟨hβV₀ _, hβfix⟩
    rw [hV₀botz] at hmem
    have hβv1 : β ⟨v, hv.1⟩ = 1 := Subgroup.mem_bot.mp hmem
    have h1 : ((⟨v, hv.1⟩ : ↥V₁) : W) = 1 := (hβone _).mp hβv1
    simpa using h1
  have hV₁zstab : StableUnder (Subgroup.zpowers z) V₁ :=
    fun x hx => hirr₁.2.1 x (Subgroup.zpowers_le.mpr hD.hzN hx)
  have hdecomp := CFSG.Quasithin.B1.coprime_decomp hW2 hoddz (M := V₁) hV₁zstab
  have hV₁eq : commSub V₁ (Subgroup.zpowers z) = V₁ := by
    rw [hV₁botz, bot_sup_eq] at hdecomp
    exact hdecomp.1
  have hV₁le_commN : V₁ ≤ commSub ⊤ N := by
    rw [← hV₁eq]
    calc commSub V₁ (Subgroup.zpowers z)
        ≤ commSub ⊤ (Subgroup.zpowers z) := commSub_mono le_top le_rfl
      _ = commSub ⊤ N := hD.hNV.symm
  have hV₁fixR : V₁ ≤ fixV R := by
    intro v hv
    rw [mem_fixV]
    intro x hx
    have hxN : x ∈ N := hRleN hx
    have hmem : x v ∈ V₁ := hirr₁.2.1 x hxN v hv
    have hxβ : x (β ⟨v, hv⟩) = β ⟨v, hv⟩ := by
      have hmem' : β ⟨v, hv⟩ ∈ fixV R := hV₀fixR (hβV₀ ⟨v, hv⟩)
      exact (mem_fixV.mp hmem') x hx
    have h1 : β ⟨x v, hmem⟩ = β ⟨v, hv⟩ := by
      have heq : β ⟨x v, hmem⟩ * (x (β ⟨v, hv⟩))⁻¹ ∈ (⊥ : Subgroup W) :=
        hβeq x hxN ⟨v, hv⟩ ⟨x v, hmem⟩ rfl
      calc β ⟨x v, hmem⟩ = x (β ⟨v, hv⟩) := mul_inv_eq_one.mp (by simpa using heq)
        _ = β ⟨v, hv⟩ := hxβ
    have h3 : (⟨x v, hmem⟩ : ↥V₁) = ⟨v, hv⟩ := hβinj h1
    exact congrArg Subtype.val h3
  have hfin : V₁ ≤ commSub ⊤ N ⊓ fixV R := le_inf hV₁le_commN hV₁fixR
  simpa [s13Comp8] using hfin

end CFSG.LocalAnalysis.WeakClosure81
