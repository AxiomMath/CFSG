module

public import CFSG.LocalAnalysis.StandardType.FF81.ConstructYSix
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.LargeExtraspecial.A2ModSLc
import CFSG.ClassicalInvolution.WeakCT.Amalgam

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT (blockSL2 blockSL2_transvection_up blockSL2_injective)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular exists_sylow_unitriangular)
open CFSG.StandardType.FrameRoute.FS81 (IsSylow2In)
open Matrix
open scoped MatrixGroups

namespace Blocks

theorem sl2_involution_conj (T : SL(2, ZMod 2)) (h1 : T ≠ 1) (h2 : T * T = 1) :
    ∃ g : SL(2, ZMod 2), g * tvU * g⁻¹ = T := by
  revert T
  decide

theorem transvection_last_mem_unitriangular {m : ℕ} (hm0 : (0 : Fin (m + 1)) ≠ Fin.last m) :
    SpecialLinearGroup.transvection hm0 (1 : ZMod 2) ∈ unitriangular (m + 1) (ZMod 2) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply_ne (ne_of_lt hji).symm,
      single_apply, if_neg (fun h => by rw [← h.1] at hji; exact absurd hji (Fin.not_lt_zero _)),
      zero_add]
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply_eq, single_apply,
      if_neg (fun h => hm0 (h.1.trans h.2.symm)), add_zero]

theorem commute_transvection_last {m : ℕ} (hm0 : (0 : Fin (m + 1)) ≠ Fin.last m)
    {u : SL(m + 1, ZMod 2)} (hu : u ∈ unitriangular (m + 1) (ZMod 2)) :
    Commute u (SpecialLinearGroup.transvection hm0 (1 : ZMod 2)) := by
  obtain ⟨hlow, hdiag⟩ := hu
  refine commute_of_single_comm hm0 (commute_single_of_entries (fun k hk => ?_) (fun l hl => ?_) ?_)
  · exact hlow k 0 (lt_of_le_of_ne (Fin.zero_le k) (Ne.symm hk))
  · exact hlow (Fin.last m) l (lt_of_le_of_ne (Fin.le_last l) hl)
  · rw [hdiag, hdiag]

theorem exists_sylow_central_block_zero {m : ℕ} (hm : 1 ≤ m) (T : SL(2, ZMod 2)) (h1 : T ≠ 1)
    (h2 : T * T = 1) :
    ∃ S : Subgroup SL(m + 1, ZMod 2), IsPGroup 2 S ∧
      (∀ S' : Subgroup SL(m + 1, ZMod 2), IsPGroup 2 S' → S ≤ S' → S' = S) ∧
      blockSL2 (ZMod 2) m ⟨0, hm⟩ T ∈ S ∧
      ∀ s ∈ S, s * blockSL2 (ZMod 2) m ⟨0, hm⟩ T = blockSL2 (ZMod 2) m ⟨0, hm⟩ T * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := sl2_involution_conj T h1 h2
  set i0 : Fin m := ⟨0, hm⟩
  have hm0 : (0 : Fin (m + 1)) ≠ Fin.last m := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  set Z : SL(m + 1, ZMod 2) := SpecialLinearGroup.transvection hm0 1
  have hτ : blockSL2 (ZMod 2) m i0 tvU = SpecialLinearGroup.transvection
      (show i0.castSucc ≠ i0.succ from Fin.castSucc_lt_succ.ne) 1 :=
    blockSL2_transvection_up i0 1
  have hZ : Z ∈ conjugatesOf (SpecialLinearGroup.transvection
      (show i0.castSucc ≠ i0.succ from Fin.castSucc_lt_succ.ne) (1 : ZMod 2)) := by
    rw [CFSG.LargeExtraspecial.A2Mod.conjugatesOf_transvection]
    exact CFSG.LargeExtraspecial.A2Mod.transvection_mem_transvectionSet hm0 one_ne_zero
  obtain ⟨h, hh⟩ := isConj_iff.1 hZ
  rw [← hτ] at hh
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (Nat.succ_le_succ (Nat.zero_le m))
  set k : SL(m + 1, ZMod 2) := blockSL2 (ZMod 2) m i0 g * h⁻¹ with hk
  have hkZ : blockSL2 (ZMod 2) m i0 T = k * Z * k⁻¹ := by
    rw [← hg, map_mul, map_mul, map_inv, ← hh, hk]
    group
  refine ⟨(unitriangular (m + 1) (ZMod 2)).map (MulAut.conj k).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [← hP]
    exact P.isPGroup'.map _
  · intro S' hS' hle
    have hle' : (P : Subgroup SL(m + 1, ZMod 2)) ≤ S'.map (MulAut.conj k⁻¹).toMonoidHom := by
      rw [hP]
      intro u hu
      refine ⟨k * u * k⁻¹, hle ⟨u, hu, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hmax := P.is_maximal' (hS'.map _) hle'
    rw [hP] at hmax
    rw [← hmax, Subgroup.map_map]
    convert (Subgroup.map_id S').symm
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  · rw [hkZ]
    exact ⟨Z, transvection_last_mem_unitriangular hm0, rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [hkZ]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc := (commute_transvection_last hm0 hu).eq
    calc k * u * k⁻¹ * (k * Z * k⁻¹) = k * (u * Z) * k⁻¹ := by group
      _ = k * (Z * u) * k⁻¹ := by rw [hc]
      _ = k * Z * k⁻¹ * (k * u * k⁻¹) := by group

end Blocks

theorem syl_of_marking {G : Type} [Group G] {Y : Subgroup G} {m : ℕ} (hm : 1 ≤ m)
    {ψ : SL(m + 1, ZMod 2) →* G} (hinj : Function.Injective ψ) (hrange : ψ.range = Y) {t : G}
    (ht : t ∈ (blockSL2 (ZMod 2) m ⟨0, hm⟩).range.map ψ) (ht2 : orderOf t = 2) :
    ∃ S : Subgroup G, IsSylow2In S Y ∧ t ∈ S ∧ orderOf t = 2 ∧ ∀ s ∈ S, s * t = t * s := by
  obtain ⟨_, ⟨T, rfl⟩, rfl⟩ := ht
  have hT1 : T ≠ 1 := by
    rintro rfl
    rw [map_one, map_one, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hT2 : T * T = 1 := by
    apply blockSL2_injective (K := ZMod 2) m ⟨0, hm⟩
    apply hinj
    rw [map_mul, map_mul, map_one, map_one, ← pow_two, ← orderOf_dvd_iff_pow_eq_one, ht2]
  obtain ⟨S0, hS0p, hS0max, hS0t, hS0c⟩ := Blocks.exists_sylow_central_block_zero hm T hT1 hT2
  refine ⟨S0.map ψ, ⟨?_, hS0p.map ψ, fun T' hT'Y hT'p hle => ?_⟩, ⟨_, hS0t, rfl⟩, ht2, ?_⟩
  · rw [← hrange]
    exact Subgroup.map_le_range ψ S0
  · have hle0 : S0 ≤ T'.comap ψ := fun x hx => hle ⟨x, hx, rfl⟩
    have heq := hS0max _ (hT'p.comap_of_injective ψ hinj) hle0
    rw [← heq, Subgroup.map_comap_eq, inf_of_le_right (hrange ▸ hT'Y)]
  · rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hS0c s hs]

variable {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G} {K : ℕ → Subgroup G}
  {t : G}

theorem FrameSystem.exists_marking_join (hF : FrameSystem n b L K t) (hn : 3 ≤ n)
    (h1n : ∀ a ∈ K 1, ∀ c ∈ K n, a * c = c * a) :
    ∃ ψ : SL(n + 2 + 1, ZMod 2) →* G, Function.Injective ψ ∧
      ψ.range = ⨆ i : Fin (n + 2), K (i : ℕ) ∧
      ∀ i : Fin (n + 2), (blockSL2 (ZMod 2) (n + 2) i).range.map ψ = K (i : ℕ) :=
  (hF.a2System_of_commute hn h1n).exists_injective_marking (by omega)

theorem FrameSystem.syl_of_commute (hF : FrameSystem n b L K t) (hn : 3 ≤ n)
    (h1n : ∀ a ∈ K 1, ∀ c ∈ K n, a * c = c * a) :
    ∃ S : Subgroup G, IsSylow2In S (⨆ i : Fin (n + 2), K (i : ℕ)) ∧ t ∈ S ∧ orderOf t = 2 ∧
      ∀ s ∈ S, s * t = t * s := by
  obtain ⟨ψ, hinj, hrange, hblk⟩ := hF.exists_marking_join hn h1n
  have ht : t ∈ K 0 := by rw [hF.K0]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  rw [← hblk ⟨0, by omega⟩] at ht
  exact syl_of_marking (by omega) hinj hrange ht hF.ord_t

end CFSG.StandardType.FF81
