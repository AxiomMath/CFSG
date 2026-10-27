module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainLift
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut
import CFSG.LocalAnalysis.StandardType.FS81.S7ModelCent
import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1
local notation "sθ" => rootThree Tag.E8 (GaloisField 2 1) (highRoot Tag.E8)
local notation "Dθ" => EPilot.perpLevi Tag.E8 (GaloisField 2 1)

private theorem isConjLine_zpowers_conj_iff {G : Type} [Group G] (x t z : G) :
    IsConjLine x (Subgroup.zpowers (t * z * t⁻¹)) ↔ IsConjLine x (Subgroup.zpowers z) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨t⁻¹ * g, ?_⟩
    have h1 : (t⁻¹ * g) * x * (t⁻¹ * g)⁻¹ = t⁻¹ * (g * x * g⁻¹) * t := by group
    rw [h1]
    have h2 : Subgroup.zpowers (t⁻¹ * (g * x * g⁻¹) * t) =
        (Subgroup.zpowers (g * x * g⁻¹)).map (MulAut.conj t⁻¹).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      congr 1
      change t⁻¹ * (g * x * g⁻¹) * t = (MulAut.conj t⁻¹) (g * x * g⁻¹)
      rw [MulAut.conj_apply]
      group
    rw [h2, hg, MonoidHom.map_zpowers]
    congr 1
    change (MulAut.conj t⁻¹) (t * z * t⁻¹) = z
    rw [MulAut.conj_apply]
    group
  · rintro ⟨g, hg⟩
    refine ⟨t * g, ?_⟩
    have h1 : (t * g) * x * (t * g)⁻¹ = t * (g * x * g⁻¹) * t⁻¹ := by group
    rw [h1]
    have h2 : Subgroup.zpowers (t * (g * x * g⁻¹) * t⁻¹) =
        (Subgroup.zpowers (g * x * g⁻¹)).map (MulAut.conj t).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      congr 1
    rw [h2, hg, MonoidHom.map_zpowers]
    congr 1

private theorem ell_wt :
    wt (Pi.single 0 1 + Pi.single 1 2 : Coords (Row.twD7.n + 1)) = 2 := by
  decide +kernel

private theorem ell_wt_shift :
    ∀ c : ZMod 3, c ≠ 0 →
      wt (c • (Pi.single 0 1 + Pi.single 1 1) +
        (Pi.single 0 1 + Pi.single 1 2) : Coords (Row.twD7.n + 1)) = 1 := by
  decide +kernel

section Row


theorem b₀_mul_inv_b₁_mem_map_perpLevi {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (Row.twD7.n + 1)} {Y : Subgroup G}
    (h : RootSetting Row.twD7 b₀ K E B Y) (ι : adjointGroup .E8 GF₂ →* G)
    (hι : Function.Injective ι) (hrange : ι.range = Y) (hβ : ι sθ = b₀ * B.b 1) :
    b₀ * (B.b 1)⁻¹ ∈ (Dθ).map ι := by
  have hEab : IsElemAbelian 3 E := h.std.2.1.2.1.2.1
  have hEY : E ≤ Y := h.torus_le
  have hK2 : Nat.card GF₂ = 2 := natCard_galoisField_two_one
  have h0E : b₀ ∈ E := by
    rw [← h.adapted.2.1]; exact h.adapted.1 ▸ B.b_mem_span 0
  have h1E : B.b 1 ∈ E := h.adapted.1 ▸ B.b_mem_span 1
  have hβE : b₀ * B.b 1 ∈ E := E.mul_mem h0E h1E
  have hℓE : b₀ * (B.b 1)⁻¹ ∈ E := E.mul_mem h0E (E.inv_mem h1E)
  have hℓCβ : b₀ * (B.b 1)⁻¹ ∈
      Subgroup.centralizer ({b₀ * B.b 1} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact congrArg Subtype.val (hEab.1.is_comm.comm
      ⟨b₀ * B.b 1, hβE⟩ ⟨b₀ * (B.b 1)⁻¹, hℓE⟩)
  have hℓCY : b₀ * (B.b 1)⁻¹ ∈
      Subgroup.centralizer ({b₀ * B.b 1} : Set G) ⊓ Y :=
    ⟨hℓCβ, hEY hℓE⟩
  have hkey : Subgroup.centralizer ({b₀ * B.b 1} : Set G) ⊓ Y =
      (Subgroup.centralizer ({sθ} : Set (adjointGroup .E8 GF₂))).map ι := by
    rw [← hβ, ← hrange]
    exact centralizer_singleton_inf_range_eq_map ι hι sθ
  have hℓMap : b₀ * (B.b 1)⁻¹ ∈
      (Subgroup.centralizer ({sθ} : Set (adjointGroup .E8 GF₂))).map ι := by
    rw [← hkey]; exact hℓCY
  obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.mp hℓMap
  obtain ⟨k, d, hd, hmd⟩ := exists_zpow_mul_of_mem_centralizer_rootThree hK2 hm
  have hℓ_eq : b₀ * (B.b 1)⁻¹ = (b₀ * B.b 1) ^ k * ι d := by
    rw [← hmeq, hmd, map_mul, map_zpow, hβ]
  have hordβ : orderOf (b₀ * B.b 1) = 3 := by
    have hvec : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 1) =
        b₀ * B.b 1 := by
      rw [B.vec_add, B.vec_single, B.vec_single, h.adapted.2.1]
    refine orderOf_eq_prime ?_ ?_
    · rw [← hvec]
      exact hEab.2 _ (h.adapted.1 ▸ B.vec_mem_span _)
    · intro h1
      have h1' : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 1) = 1 := by
        rw [hvec, h1]
      have he0 := B.indep _ h1'
      have h00 := congrFun he0 0
      simp only [Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (by decide : (0 : Fin (Row.twD7.n + 1)) ≠ 1),
        Pi.zero_apply, add_zero] at h00
      exact one_ne_zero h00
  have hLt₀ : (Dθ).map ι ≤ Subgroup.centralizer
      ({ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂))} : Set G) :=
    (map_le_centralizer_map_pinnedElt_highRoot (K := GF₂) ι).2
  have hDt₀ : ∀ d ∈ Dθ, Commute (ι d)
      (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂))) :=
    fun d hd => Subgroup.mem_centralizer_singleton_iff.mp
      (hLt₀ (Subgroup.mem_map_of_mem ι hd))
  have htβ : ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) * (b₀ * B.b 1) *
      (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹ = (b₀ * B.b 1)⁻¹ := by
    have h := pinnedElt_mul_rootThree_mul_inv (K := GF₂) (α := highRoot .E8)
      (isRoot_highRoot .E8)
    have h2 : ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) * ι sθ *
        (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹ = ι (sθ⁻¹) := by
      have h3 : ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) * ι sθ *
          (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹ =
          ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂) * sθ *
            (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂))⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [h3, h]
    rwa [map_inv, hβ] at h2
  have htβpow : ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) *
      (b₀ * B.b 1) ^ k *
      (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹ = (b₀ * B.b 1) ^ (-k) := by
    have h1 : ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) * (b₀ * B.b 1) ^ k *
        (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹ =
        ((MulAut.conj (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂))))
          (b₀ * B.b 1)) ^ k := by
      rw [← map_zpow]
      rfl
    rw [h1, MulAut.conj_apply, htβ, inv_zpow']
  have htd : ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) * ι d *
      (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹ = ι d := by
    rw [(hDt₀ d hd).eq.symm]; group
  have hιd : ι d = (b₀ * B.b 1) ^ (-k) * (b₀ * (B.b 1)⁻¹) := by
    rw [hℓ_eq, ← mul_assoc, ← zpow_add]
    simp
  have hconj_eq : ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) *
      (b₀ * (B.b 1)⁻¹) *
      (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹ =
      (b₀ * B.b 1) ^ (-2 * k) * (b₀ * (B.b 1)⁻¹) := by
    have hsub : ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) *
        (b₀ * (B.b 1)⁻¹) *
        (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹ =
        (b₀ * B.b 1) ^ (-k) * ι d := by
      rw [hℓ_eq]
      calc ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) *
              ((b₀ * B.b 1) ^ k * ι d) *
              (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹
          = (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) *
              (b₀ * B.b 1) ^ k *
              (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹) *
              (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) * ι d *
              (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹) := by group
        _ = (b₀ * B.b 1) ^ (-k) * ι d := by rw [htβpow, htd]
    rw [hsub, hιd, ← mul_assoc, ← zpow_add,
      show -k + -k = -2 * k by ring]
  have hβvec : B.vec (Pi.single 0 1 + Pi.single 1 1 : Coords (Row.twD7.n + 1)) =
      b₀ * B.b 1 := by
    rw [B.vec_add, B.vec_single, B.vec_single, h.adapted.2.1]
  have hneg : (Pi.single 1 2 : Coords (Row.twD7.n + 1)) = -Pi.single 1 1 := by
    decide +kernel
  have hellvec : B.vec (Pi.single 0 1 + Pi.single 1 2 : Coords (Row.twD7.n + 1)) =
      b₀ * (B.b 1)⁻¹ := by
    rw [hneg, B.vec_add, B.vec_neg_eq_inv, B.vec_single, B.vec_single, h.adapted.2.1]
  have hvvec : B.vec ((-2 * k : ℤ) •
        (Pi.single 0 1 + Pi.single 1 1 : Coords (Row.twD7.n + 1)) +
        (Pi.single 0 1 + Pi.single 1 2 : Coords (Row.twD7.n + 1))) =
      (b₀ * B.b 1) ^ (-2 * k) * (b₀ * (B.b 1)⁻¹) := by
    rw [B.vec_add, B.vec_zsmul, hβvec, hellvec]
  have hc0 : ((-2 * k : ℤ) : ZMod 3) = 0 := by
    by_contra hc
    have hvc : ((-2 * k : ℤ) : ZMod 3) •
        (Pi.single 0 1 + Pi.single 1 1 : Coords (Row.twD7.n + 1)) +
        (Pi.single 0 1 + Pi.single 1 2 : Coords (Row.twD7.n + 1)) =
        (-2 * k : ℤ) • (Pi.single 0 1 + Pi.single 1 1 : Coords (Row.twD7.n + 1)) +
        (Pi.single 0 1 + Pi.single 1 2 : Coords (Row.twD7.n + 1)) := by
      rw [Int.cast_smul_eq_zsmul]
    have hwt_v : wt ((-2 * k : ℤ) •
        (Pi.single 0 1 + Pi.single 1 1 : Coords (Row.twD7.n + 1)) +
        (Pi.single 0 1 + Pi.single 1 2 : Coords (Row.twD7.n + 1))) = 1 := by
      rw [← hvc]
      exact ell_wt_shift ((-2 * k : ℤ) : ZMod 3) hc
    have hv_ne : (-2 * k : ℤ) •
        (Pi.single 0 1 + Pi.single 1 1 : Coords (Row.twD7.n + 1)) +
        (Pi.single 0 1 + Pi.single 1 2 : Coords (Row.twD7.n + 1)) ≠ 0 := by
      intro h0
      have hzero : wt (0 : Coords (Row.twD7.n + 1)) = 0 := by simp [wt]
      rw [h0, hzero] at hwt_v
      norm_num at hwt_v
    have hconjLine_v : IsConjLine b₀ (B.line ((-2 * k : ℤ) •
        (Pi.single 0 1 + Pi.single 1 1 : Coords (Row.twD7.n + 1)) +
        (Pi.single 0 1 + Pi.single 1 2 : Coords (Row.twD7.n + 1)))) :=
      (h.recOut.2.1 _ hv_ne).mpr (Or.inl hwt_v)
    have hline_eq : B.line ((-2 * k : ℤ) •
        (Pi.single 0 1 + Pi.single 1 1 : Coords (Row.twD7.n + 1)) +
        (Pi.single 0 1 + Pi.single 1 2 : Coords (Row.twD7.n + 1))) =
        Subgroup.zpowers (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) *
          (b₀ * (B.b 1)⁻¹) *
          (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹) := by
      rw [Basis3.line, hvvec, hconj_eq]
    have hconjLine_ℓ : IsConjLine b₀ (Subgroup.zpowers (b₀ * (B.b 1)⁻¹)) := by
      have h' : IsConjLine b₀ (Subgroup.zpowers
          (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)) *
            (b₀ * (B.b 1)⁻¹) *
            (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))⁻¹)) := by
        rw [← hline_eq]; exact hconjLine_v
      exact (isConjLine_zpowers_conj_iff b₀
        (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂)))
        (b₀ * (B.b 1)⁻¹)).mp h'
    have he_ne : (Pi.single 0 1 + Pi.single 1 2 : Coords (Row.twD7.n + 1)) ≠ 0 := by
      intro h0
      have hwe : wt (Pi.single 0 1 + Pi.single 1 2 : Coords (Row.twD7.n + 1)) = 2 := ell_wt
      have hzero : wt (0 : Coords (Row.twD7.n + 1)) = 0 := by simp [wt]
      rw [h0, hzero] at hwe
      norm_num at hwe
    have hconjLine_e : IsConjLine b₀
        (B.line (Pi.single 0 1 + Pi.single 1 2 : Coords (Row.twD7.n + 1))) := by
      rw [Basis3.line, hellvec]
      exact hconjLine_ℓ
    have hpred := (h.recOut.2.1 _ he_ne).mp hconjLine_e
    have hwe8 : wt (Pi.single 0 1 + Pi.single 1 2 : Coords 8) = 2 := by decide +kernel
    have hpred8 : wt (Pi.single 0 1 + Pi.single 1 2 : Coords 8) = 1 ∨
        wt (Pi.single 0 1 + Pi.single 1 2 : Coords 8) = 4 ∨
        wt (Pi.single 0 1 + Pi.single 1 2 : Coords 8) = 7 := hpred
    rcases hpred8 with h | h | h <;> omega
  have hk0 : ((k : ℤ) : ZMod 3) = 0 := by
    have h := hc0
    rw [show (-2 * k : ℤ) = (-2 : ℤ) * k by ring, Int.cast_mul] at h
    have hone : ((-2 : ℤ) : ZMod 3) = 1 := by decide
    rwa [hone, one_mul] at h
  have h3dvd : (3 : ℤ) ∣ k := (ZMod.intCast_zmod_eq_zero_iff_dvd k 3).mp hk0
  have hβk : (b₀ * B.b 1) ^ k = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hordβ]
    exact h3dvd
  rw [hℓ_eq, hβk, one_mul]
  exact Subgroup.mem_map_of_mem ι hd

end Row

end CFSG.StandardType.FrameRoute.FS81

end
