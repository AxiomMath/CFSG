module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.FS81.S7R120
import CFSG.LocalAnalysis.StandardType.FS81.S7AutAt
import CFSG.LocalAnalysis.StandardType.FS81.S7ModelIdent
import CFSG.LocalAnalysis.StandardType.FS81.S7ModelCent
import CFSG.LocalAnalysis.StandardType.FS81.Realized
import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs
import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SeitzReduction CFSG.Blueprint.Chevalley

private theorem radTwD7_wt_eq_three :
    ∀ (i : Fin (Row.twD7.n + 1)), i ≠ 0 → i ≠ 1 → ∀ c : ZMod 3, c ≠ 0 →
      wt (Pi.single i 1 + c • (Pi.single 0 1 + Pi.single 1 1) :
        Coords (Row.twD7.n + 1)) = 3 := by
  decide +kernel

private theorem radTwD7_zpowers_conj_congr {G : Type} [Group G] {a b c : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.zpowers (c * a * c⁻¹) = Subgroup.zpowers (c * b * c⁻¹) := by
  have h1 : Subgroup.zpowers (c * a * c⁻¹) =
      (Subgroup.zpowers a).map (MulAut.conj c).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  have h2 : Subgroup.zpowers (c * b * c⁻¹) =
      (Subgroup.zpowers b).map (MulAut.conj c).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [h1, h2, h]

theorem radTwD7_s79A_le
    {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} {B : Basis3 G (Row.twD7.n + 1)} {Y : Subgroup G}
    (h : RootSetting Row.twD7 b₀ K E B Y)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hK2 : Nat.card F = 2)
    (ι' : adjointGroup .E8 F →* G) (hι'_inj : Function.Injective ι')
    (hι'_rangeY : ι'.range = Y)
    (hι'_sθ : ι' (rootThree .E8 F (highRoot .E8)) = b₀ * B.b 1)
    (hordβ : orderOf (b₀ * B.b 1) = 3)
    (hLt₀ : (EPilot.perpLevi .E8 F).map ι' ≤ Subgroup.centralizer
        ({ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F))} : Set G)) :
    s79A Row.twD7 B ≤ (EPilot.perpLevi .E8 F).map ι' := by
  have hEab : IsElemAbelian 3 E := h.std.2.1.2.1.2.1
  have hEY : E ≤ Y := h.torus_le
  have hβE : b₀ * B.b 1 ∈ E := by
    have h0 : b₀ ∈ E := by rw [← h.adapted.2.1]; exact h.adapted.1 ▸ B.b_mem_span 0
    exact E.mul_mem h0 (h.adapted.1 ▸ B.b_mem_span 1)
  have hkey : Subgroup.centralizer ({b₀ * B.b 1} : Set G) ⊓ Y =
      (Subgroup.centralizer ({rootThree .E8 F (highRoot .E8)} :
        Set (adjointGroup .E8 F))).map ι' := by
    rw [← hι'_sθ, ← hι'_rangeY]
    exact centralizer_singleton_inf_range_eq_map (M := adjointGroup .E8 F) ι' hι'_inj _
  have hzpow : ∀ x ∈ Subgroup.centralizer ({rootThree .E8 F (highRoot .E8)} :
      Set (adjointGroup .E8 F)),
      ∃ k : ℤ, ∃ d ∈ EPilot.perpLevi .E8 F,
        x = rootThree .E8 F (highRoot .E8) ^ k * d :=
    fun x hx => exists_zpow_mul_of_mem_centralizer_rootThree hK2 hx
  have hDβ : ∀ d ∈ EPilot.perpLevi .E8 F, Commute (ι' d) (b₀ * B.b 1) := by
    intro d hd
    have hdC : d ∈ Subgroup.centralizer ({rootThree .E8 F (highRoot .E8)} :
        Set (adjointGroup .E8 F)) := perpLevi_le_centralizer_rootThree (K := F) hd
    have hc : Commute d (rootThree .E8 F (highRoot .E8)) :=
      Subgroup.mem_centralizer_singleton_iff.mp hdC
    rw [← hι'_sθ]
    exact hc.map ι'
  have htβ : ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) * (b₀ * B.b 1) *
      (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹ = (b₀ * B.b 1)⁻¹ := by
    have h := pinnedElt_mul_rootThree_mul_inv (K := F) (α := highRoot .E8) (isRoot_highRoot .E8)
    have h2 : ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) *
        ι' (rootThree .E8 F (highRoot .E8)) *
        (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹ =
        ι' ((rootThree .E8 F (highRoot .E8))⁻¹) := by
      have h3 : ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) *
          ι' (rootThree .E8 F (highRoot .E8)) *
          (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹ =
          ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F) *
            rootThree .E8 F (highRoot .E8) *
            (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F))⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [h3, h]
    rwa [map_inv, hι'_sθ] at h2
  have hbgen : ∀ i : Fin (Row.twD7.n + 1), i ≠ 0 → i ≠ 1 →
      B.b i ∈ (EPilot.perpLevi .E8 F).map ι' := by
    intro i hi hi1
    have hbiE : B.b i ∈ E := h.adapted.1 ▸ B.b_mem_span i
    have hbiCβ : B.b i ∈ Subgroup.centralizer ({b₀ * B.b 1} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hcomm := hEab.1.is_comm.comm (⟨b₀ * B.b 1, hβE⟩ : ↥E) (⟨B.b i, hbiE⟩ : ↥E)
      simpa using congrArg Subtype.val hcomm
    have hbiCY : B.b i ∈ Subgroup.centralizer ({b₀ * B.b 1} : Set G) ⊓ Y :=
      ⟨hbiCβ, hEY hbiE⟩
    have hbiMap : B.b i ∈ (Subgroup.centralizer ({rootThree .E8 F (highRoot .E8)} :
        Set (adjointGroup .E8 F))).map ι' := by
      rw [← hkey]; exact hbiCY
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hbiMap
    obtain ⟨k, d, hd, hxd⟩ := hzpow x hx
    have hbi_eq : B.b i = (b₀ * B.b 1) ^ k * ι' d := by
      rw [← hxeq, hxd, map_mul, map_zpow, hι'_sθ]
    have hd' : ι' d ∈ (EPilot.perpLevi .E8 F).map ι' := Subgroup.mem_map_of_mem ι' hd
    have hDt₀ : Commute (ι' d) (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F))) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLt₀ hd')
    have htβpow : ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) *
        (b₀ * B.b 1) ^ k *
        (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹ = (b₀ * B.b 1) ^ (-k) := by
      have h1 : ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) * (b₀ * B.b 1) ^ k *
          (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹ =
          ((MulAut.conj (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F))))
            (b₀ * B.b 1)) ^ k := by
        rw [← map_zpow]
        rfl
      rw [h1, MulAut.conj_apply, htβ, inv_zpow']
    have htd : ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) * ι' d *
        (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹ = ι' d := by
      rw [hDt₀.eq.symm]; group
    have hconj_eq : ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) * B.b i *
        (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹ =
        B.b i * (b₀ * B.b 1) ^ (-2 * k) := by
      rw [hbi_eq]
      calc ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) *
              ((b₀ * B.b 1) ^ k * ι' d) *
              (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹
          = (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) * (b₀ * B.b 1) ^ k *
              (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹) *
              (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) * ι' d *
              (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹) := by group
        _ = (b₀ * B.b 1) ^ (-k) * ι' d := by rw [htβpow, htd]
        _ = ((b₀ * B.b 1) ^ k * ι' d) * (b₀ * B.b 1) ^ (-2 * k) := by
              have hcz := (hDβ d hd).zpow_right (-2 * k)
              calc (b₀ * B.b 1) ^ (-k) * ι' d
                  = (b₀ * B.b 1) ^ k * ((b₀ * B.b 1) ^ (-2 * k) * ι' d) := by
                    rw [← mul_assoc, ← zpow_add]
                    congr 1
                    ring_nf
                _ = (b₀ * B.b 1) ^ k * (ι' d * (b₀ * B.b 1) ^ (-2 * k)) := by rw [hcz.eq]
                _ = ((b₀ * B.b 1) ^ k * ι' d) * (b₀ * B.b 1) ^ (-2 * k) := by group
    have hβv : B.vec (Pi.single 0 1 + Pi.single 1 1 : Coords (Row.twD7.n + 1)) =
        b₀ * B.b 1 := by
      rw [B.vec_add, B.vec_single, B.vec_single, h.adapted.2.1]
    have hvec : B.b i * (b₀ * B.b 1) ^ (-2 * k) =
        B.vec (Pi.single i 1 + ((-2 * k : ℤ) : ZMod 3) •
          (Pi.single 0 1 + Pi.single 1 1) : Coords (Row.twD7.n + 1)) := by
      rw [← hβv, ← B.vec_single, ← B.vec_zsmul, ← B.vec_add]
      congr 1
      rw [Int.cast_smul_eq_zsmul]
    have he : (Pi.single i 1 : Coords (Row.twD7.n + 1)) ≠ 0 := by
      intro h0
      have h1 := congrFun h0 i
      rw [Pi.single_eq_same, Pi.zero_apply] at h1
      exact one_ne_zero h1
    have hwt_e : wt (Pi.single i 1 : Coords (Row.twD7.n + 1)) = 1 := by
      fin_cases i <;> decide +kernel
    have hconjLine_e : IsConjLine b₀ (B.line (Pi.single i 1 : Coords (Row.twD7.n + 1))) :=
      (h.recOut.2.1 _ he).mpr (Or.inl hwt_e)
    obtain ⟨g, hg⟩ := hconjLine_e
    have hconjLine_shift : IsConjLine b₀
        (B.line (Pi.single i 1 + ((-2 * k : ℤ) : ZMod 3) •
          (Pi.single 0 1 + Pi.single 1 1) : Coords (Row.twD7.n + 1))) := by
      refine ⟨ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) * g, ?_⟩
      have h1 : (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) * g) * b₀ *
          (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) * g)⁻¹ =
          ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) * (g * b₀ * g⁻¹) *
          (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹ := by group
      have h2 : Subgroup.zpowers (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) *
          (g * b₀ * g⁻¹) *
          (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹) =
          Subgroup.zpowers (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) *
          B.vec (Pi.single i 1 : Coords (Row.twD7.n + 1)) *
          (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹) :=
        radTwD7_zpowers_conj_congr (by simpa only [Basis3.line] using hg)
      have h3 : ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)) *
          B.vec (Pi.single i 1 : Coords (Row.twD7.n + 1)) *
          (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F)))⁻¹ =
          B.vec (Pi.single i 1 + ((-2 * k : ℤ) : ZMod 3) •
            (Pi.single 0 1 + Pi.single 1 1) : Coords (Row.twD7.n + 1)) := by
        rw [B.vec_single]
        exact hconj_eq.trans hvec
      rw [h1, h2, h3]
      rfl
    have hc0 : ((-2 * k : ℤ) : ZMod 3) = 0 := by
      by_contra hc
      have hwt3 : wt (Pi.single i 1 + ((-2 * k : ℤ) : ZMod 3) •
          (Pi.single 0 1 + Pi.single 1 1) : Coords (Row.twD7.n + 1)) = 3 :=
        radTwD7_wt_eq_three i hi hi1 ((-2 * k : ℤ) : ZMod 3) hc
      have hne : (Pi.single i 1 + ((-2 * k : ℤ) : ZMod 3) •
          (Pi.single 0 1 + Pi.single 1 1) : Coords (Row.twD7.n + 1)) ≠ 0 := by
        intro h0
        have hwt0 : wt (0 : Coords (Row.twD7.n + 1)) = 0 := by
          unfold wt
          simp
        rw [h0, hwt0] at hwt3
        omega
      have hpred := (h.recOut.2.1 _ hne).mp hconjLine_shift
      rcases hpred with h1 | h1 | h1
      · exact absurd (h1.symm.trans hwt3) (by norm_num)
      · exact absurd (h1.symm.trans hwt3) (by norm_num)
      · exact absurd (h1.symm.trans hwt3) (by norm_num)
    have hk0 : ((k : ℤ) : ZMod 3) = 0 := by
      have h := hc0
      rw [show (-2 * k : ℤ) = (-2 : ℤ) * k by ring, Int.cast_mul] at h
      have hone : ((-2 : ℤ) : ZMod 3) = 1 := by decide
      rwa [hone, one_mul] at h
    have h3dvd : (3 : ℤ) ∣ k := (ZMod.intCast_zmod_eq_zero_iff_dvd k 3).mp hk0
    have hβk : (b₀ * B.b 1) ^ k = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hordβ]
      exact h3dvd
    rw [hbi_eq, hβk, one_mul]
    exact hd'
  change Subgroup.closure ({B.b 2, B.b 3, B.b 4 * B.b 5} : Set G) ≤
    (EPilot.perpLevi .E8 F).map ι'
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hbgen 2 (by decide) (by decide)
  · exact hbgen 3 (by decide) (by decide)
  · exact Subgroup.mul_mem _ (hbgen 4 (by decide) (by decide)) (hbgen 5 (by decide) (by decide))

theorem e8RadicalAt_twD7 :
    E8RadicalAt Row.twD7 := by
  intro G _ _ b₀ K E B Y h
  let F := GaloisField 2 1
  have hK2 : Nat.card F = 2 := natCard_galoisField_two_one
  have hA : E8AutAt Row.twD7 := e8AutAt_twD7
  obtain ⟨ι, hι_inj, hι_range⟩ := exists_injective_hom_range_eq_of_isEm_eight h.isEm
  have hβE : b₀ * B.b 1 ∈ E := by
    have h0 : b₀ ∈ E := by rw [← h.adapted.2.1]; exact h.adapted.1 ▸ B.b_mem_span 0
    exact E.mul_mem h0 (h.adapted.1 ▸ B.b_mem_span 1)
  have hordβ : orderOf (b₀ * B.b 1) = 3 := by
    have hvec : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 1) =
        b₀ * B.b 1 := by
      rw [B.vec_add, B.vec_single, B.vec_single, h.adapted.2.1]
    refine orderOf_eq_prime ?_ ?_
    · rw [← hvec]
      exact h.std.2.1.2.1.2.1.2 _ (h.adapted.1 ▸ B.vec_mem_span _)
    · intro h1
      have h1' : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 1) = 1 := by
        rw [hvec, h1]
      have he0 := B.indep _ h1'
      have h0 := congrFun he0 0
      simp only [Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (by decide : (0 : Fin (Row.twD7.n + 1)) ≠ 1),
        Pi.zero_apply, add_zero] at h0
      exact one_ne_zero h0
  have hβ1 : b₀ * B.b 1 ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hordβ
    norm_num at hordβ
  have h120 : (normalizerLines ι.range E (b₀ * B.b 1)).ncard = 120 := by
    rw [hι_range]
    exact ncard_normalizerLines_eq_120_twD7 h (hA G b₀ K E B Y h)
  have hEY : E ≤ ι.range := by rw [hι_range]; exact h.torus_le
  have hEab : IsElemAbelian 3 E := h.std.2.1.2.1.2.1
  have hEcard : 3 ^ 8 ≤ Nat.card E := by
    rw [h.std.2.1.2.2.2.1]
    norm_num [Row.m, Row.n]
  obtain ⟨ι', hι'_inj, hι'_range, hι'_sθ⟩ :=
    exists_hom_range_eq_apply_rootThree_eq hK2 ι hι_inj hEY hEab hEcard hβE hβ1 h120
  have hι'_rangeY : ι'.range = Y := hι'_range.trans hι_range
  let t₀ : G := ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F))
  let U : Subgroup G := (EPilot.highRadical .E8 F).map ι'
  let L : Subgroup G := (EPilot.perpLevi .E8 F).map ι'
  have hmapcent := map_le_centralizer_map_pinnedElt_highRoot (K := F) ι'
  have ht₀ord : orderOf t₀ = 2 := by
    change orderOf (ι' (EPilot.pinnedElt .E8 (highRoot .E8) (1 : F))) = 2
    rw [orderOf_injective ι' hι'_inj]
    exact orderOf_pinnedElt_one (τ := .E8) (K := F) (highRoot .E8)
  have hLY : L ≤ Y := (Subgroup.map_le_range ι' _).trans_eq hι'_rangeY
  have hLt₀ : L ≤ Subgroup.centralizer ({t₀} : Set G) := hmapcent.2
  have hU2 : IsPGroup 2 U := by
    obtain ⟨-, -, -, hQ, -⟩ := centralizer_pinnedElt_highRoot_E8 (K := F)
    exact hQ.map ι'
  have ht₀U : t₀ ∈ U :=
    Subgroup.mem_map_of_mem ι' (pinnedElt_highRoot_mem_highRadical (K := F))
  have hUY : U ≤ Y := (Subgroup.map_le_range ι' _).trans_eq hι'_rangeY
  have hUt₀ : U ≤ Subgroup.centralizer ({t₀} : Set G) := hmapcent.1
  have hUmax : ∀ P : Subgroup G, IsPGroup 2 P →
      P ≤ Subgroup.centralizer ({t₀} : Set G) ⊓ Y →
      Subgroup.centralizer ({t₀} : Set G) ⊓ Y ≤ Subgroup.normalizer (P : Set G) →
      P ≤ U := by
    intro P hP hPC hN
    exact hUmax_E8_range (K := F) ι' hι'_inj P hP (by simpa [hι'_rangeY] using hPC)
      (by simpa [hι'_rangeY] using hN)
  have hirr : ∀ V : Subgroup G, Subgroup.zpowers t₀ ≤ V → V ≤ U →
      L ≤ Subgroup.normalizer (V : Set G) → V = Subgroup.zpowers t₀ ∨ V = U :=
    hirr_E8_range (K := F) hK2 ι' hι'_inj (L := L) le_rfl
  have hs79 : s79A Row.twD7 B ≤ L :=
    radTwD7_s79A_le h hK2 ι' hι'_inj hι'_rangeY hι'_sθ hordβ hLt₀
  refine ⟨t₀, L, U, ht₀ord, hLY, hLt₀, hU2, ht₀U, hUY, hUt₀, hUmax, hirr, hs79⟩

end CFSG.StandardType.FrameRoute.FS81

end
