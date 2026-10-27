module

public import CFSG.Quasithin.Vol2.Ch10SecI1Defs
public import CFSG.Quasithin.Vol2.Ch10SecI1Dual
public import CFSG.Quasithin.SteinbergCBI16
public import CFSG.Quasithin.Background.SmithB51P2Coh
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank
open CFSG.Open (quasithinG2 quasithinZorn)

namespace C10KH

section Split

variable {W : Type} [CommGroup W]

theorem index_eq_one_of_h1 {Gm : Subgroup (MulAut W)} (hfix : fixV Gm = ⊥)
    (hLW : ∀ g ∈ Gm, ∀ w ∈ commV Gm, g w ∈ commV Gm)
    (hH1 : ∀ f ∈ Z1A (FFC.muW hLW), f ∈ B1A (FFC.muW hLW)) : (commV Gm).index = 1 := by
  have h := FFC.sup_fixV_eq_top_of_h1 hLW (fun g hg v => comm_mem_commV hg v) hH1
  rw [hfix, sup_bot_eq] at h
  rw [h, Subgroup.index_top]

end Split

section Bridges

variable {Γ : Type} [Group Γ] {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

theorem altNat_of_isModel {n : ℕ} {ρ : Representation (ZMod 2) Γ M}
    (h : (FFModel.altDn n).IsModel ρ) : Explicit.AlternatingNatural ρ n .alternating := by
  obtain ⟨θ, β, hw⟩ := h
  exact ⟨MulEquiv.refl _, θ, β, hw⟩

theorem sp4Derived_of_isModel {K : Type} [Field K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {ρ : Representation (ZMod 2) Γ M} (h : (FFModel.nat (StatedSp 2 K)).IsModel ρ) :
    Explicit.BinaryNaturalSp4Derived ρ K := by
  have : Group.IsPerfect ↥(StatedSp 2 K) :=
    CFSG.LieType.Steinberg.CentralExt.SpClosed.isPerfect_statedSp 2 K hK
  have hsp : StatedSp 2 K = ⁅Explicit.sp4 K, Explicit.sp4 K⁆ := by
    rw [Explicit.sp4_eq_statedSp K]
    exact Subgroup.commutator_eq_self.symm
  exact (congrArg (fun X => (FFModel.nat X).IsModel ρ) hsp).mp h

theorem g2Derived_of_isModel {K : Type} [Field K] [CharP K 2] {ρ : Representation (ZMod 2) Γ M}
    (h : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).IsModel ρ) :
    Explicit.G2Natural ρ K .derived := by
  have hD : FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆ =
      FFModel.zornQ (Explicit.cayleyActor K .derived) := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
    rfl
  exact (congrArg (fun X : FFModel => X.IsModel ρ) hD).mp h

theorem finite_zornAut (K : Type) [Field K] [Finite K] :
    Finite (quasithinZorn K ≃ₗ[K] quasithinZorn K) :=
  Finite.of_injective (fun e : quasithinZorn K ≃ₗ[K] quasithinZorn K => (e : quasithinZorn K →
    quasithinZorn K)) fun _ _ h => LinearEquiv.ext (congrFun h)

end Bridges

end C10KH


theorem as_I_1_6_dual_holds : AS_I_1_6_dual := by
  intro W _ _ hW2 Gm d hfix hmod
  obtain ⟨-, t5, t6, t7, t8, t2, tO, -, t3, tSp, tG2, t45, -, -, -, -, -⟩ :=
    SteinbergCB.I16.natural_binary_module_first_cohomology.{0, 0}
  have hLW : ∀ g ∈ Gm, ∀ w ∈ commV Gm, g w ∈ commV Gm := fun g hg w hw =>
    C10KH.map_mem_commV hg hw
  have hone : (commV Gm).index = 1 → (commV Gm).index ≤ 2 ^ 0 := fun h => by
    rw [h, pow_zero]
  rcases hmod with ⟨m, hm, hd, hR⟩ | ⟨m, hm, hd, hR⟩ | ⟨a, ha, hd, K, _, _, hK, hR⟩ |
    ⟨a, ha, hd, K, _, _, _, hK, hR⟩ | ⟨a, ha, hd, K, _, _, hK, hR⟩ | ⟨hd, K, _, _, hK, hR⟩ |
    ⟨a, ha, hd, K, _, _, hK, hR⟩ | ⟨a, ha, hd, K, _, _, hK, hR⟩ | ⟨m, hm, hd, K, _, _, hK, hR⟩ |
    ⟨hd, π, hR⟩ | ⟨hd, α, π, hR⟩ | ⟨hd, hR⟩
  ·
    have : Finite (FFModel.altDn m).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin m)))
    refine C10KH.dualCover_le (D := FFModel.altDn m) hW2 hfix hR fun ρ hρ => ?_
    have h := C10KH.altNat_of_isModel hρ
    rcases hm with rfl | rfl
    · have := (t5 h).1
      omega
    · have := t7 h
      omega
  ·
    have : Finite (FFModel.altDn m).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin m)))
    refine C10KH.dualCover_le (D := FFModel.altDn m) hW2 hfix hR fun ρ hρ => ?_
    have h := C10KH.altNat_of_isModel hρ
    rcases hm with rfl | rfl
    · have := t6 h
      omega
    · have := t8 h
      omega
  ·
    let _ := Fintype.ofFinite K
    have : Finite (FFModel.nat (StatedSL 2 K)).Gam := inferInstanceAs (Finite ↥(StatedSL 2 K))
    have hK' : Fintype.card K = 2 ^ a := by rw [Fintype.card_eq_nat_card]; exact hK
    refine C10KH.dualCover_le (D := FFModel.nat (StatedSL 2 K)) hW2 hfix hR fun ρ hρ => ?_
    have := t2 hK' ha hρ
    omega
  ·
    let _ := Fintype.ofFinite K
    have : Finite (FFModel.twistTensor a (StatedSL 2 K)).Gam :=
      inferInstanceAs (Finite ↥(StatedSL 2 K))
    have hK' : Fintype.card K = 2 ^ (2 * a) := by rw [Fintype.card_eq_nat_card]; exact hK
    refine C10KH.dualCover_le (D := FFModel.twistTensor a (StatedSL 2 K)) hW2 hfix hR
      fun ρ hρ => ?_
    have := tO hK' (by omega) hρ
    omega
  ·
    let _ := Fintype.ofFinite K
    have : Finite (FFModel.nat (StatedSL 3 K)).Gam := inferInstanceAs (Finite ↥(StatedSL 3 K))
    have hK' : Fintype.card K = 2 ^ a := by rw [Fintype.card_eq_nat_card]; exact hK
    refine C10KH.dualCover_le (D := FFModel.nat (StatedSL 3 K)) hW2 hfix hR fun ρ hρ => ?_
    have := t3 (ε := .natural) hK' (by omega) hρ
    split_ifs at this <;> omega
  ·
    let _ := Fintype.ofFinite K
    have : Finite (FFModel.nat (StatedSL 3 K)).Gam := inferInstanceAs (Finite ↥(StatedSL 3 K))
    have hK' : Fintype.card K = 2 ^ 1 := by rw [Fintype.card_eq_nat_card]; exact hK
    refine C10KH.dualCover_le (D := FFModel.nat (StatedSL 3 K)) hW2 hfix hR fun ρ hρ => ?_
    have := t3 (ε := .natural) hK' (by omega) hρ
    split_ifs at this <;> omega
  ·
    let _ := Fintype.ofFinite K
    have : CharP K 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    have : Finite (FFModel.nat (StatedSp 2 K)).Gam := inferInstanceAs (Finite ↥(StatedSp 2 K))
    have hK' : Fintype.card K = 2 ^ a := by rw [Fintype.card_eq_nat_card]; exact hK
    refine C10KH.dualCover_le (D := FFModel.nat (StatedSp 2 K)) hW2 hfix hR fun ρ hρ => ?_
    have := tSp hK' (by omega) (C10KH.sp4Derived_of_isModel hK4 hρ)
    omega
  ·
    let _ := Fintype.ofFinite K
    have : CharP K 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
    have := C10KH.finite_zornAut K
    have : Finite (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Gam :=
      inferInstanceAs (Finite ↥⁅quasithinG2 K, quasithinG2 K⁆)
    have hK' : Fintype.card K = 2 ^ a := by rw [Fintype.card_eq_nat_card]; exact hK
    refine C10KH.dualCover_le (D := FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) hW2 hfix hR
      fun ρ hρ => ?_
    have := tG2 hK' (by omega) (C10KH.g2Derived_of_isModel hρ)
    omega
  ·
    let _ := Fintype.ofFinite K
    have : Finite (FFModel.nat (StatedSL m K)).Gam := inferInstanceAs (Finite ↥(StatedSL m K))
    have hK' : Fintype.card K = 2 := by rw [Fintype.card_eq_nat_card, hK, pow_one]
    refine C10KH.dualCover_le (D := FFModel.nat (StatedSL m K)) hW2 hfix hR fun ρ hρ => ?_
    have := t45 (ε := .natural) hm hK' hρ
    omega
  ·
    rw [hd]
    exact hone (C10KH.index_eq_one_of_h1 hfix hLW (B5.P2.h1_wedge hLW hR))
  ·
    rw [hd]
    exact hone (C10KH.index_eq_one_of_h1 hfix hLW (B5.P2.h1_a7Four hLW hR))
  ·
    rw [hd]
    exact hone (C10KH.index_eq_one_of_h1 hfix hLW (B5.P2.h1_tripleA6Six hLW hR))

end CFSG.Quasithin.ASInputs
