module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyOneMcClurg
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.SmithB45TorF4
import CFSG.Quasithin.Background.FLc2Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.Quasithin
open CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem twistedF4IrredBound_holds :
    TwistedF4IrredBound := by
  intro X _ _ n h2F4 U _ _ hU ρ _ l hl2 hρl
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_2f4_simplicity X 2 n h2F4).2
  have hZX : Subgroup.center X = ⊥ :=
    (CFSG.QuasithinUnique.Setup.X6.large_Ree_model_two_extensions h2F4).1
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e₀⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model h2F4
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hinj : Function.Injective ρ := FLc.injective_of_ne_one ρ ⟨l, hρl⟩
  let L : Subgroup (MulAut U) := ρ.range
  let eL : X ≃* L := MonoidHom.ofInjective (f := ρ) hinj
  have hZL : Subgroup.center L = ⊥ := by
    have h : (Subgroup.center L).map eL.symm.toMonoidHom = Subgroup.center X :=
      Subgroup.map_center_eq eL.symm
    rw [hZX] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ eL.symm.injective).1 h
  let e : L ⧸ Subgroup.center L ≃* F4.reeGamma K a :=
    (QuotientGroup.quotientMulEquivOfEq hZL).trans
      ((QuotientGroup.quotientBot (G := L)).trans (eL.symm.trans e₀))
  let x : L := ⟨ρ l, MonoidHom.mem_range.mpr ⟨l, rfl⟩⟩
  have hl : l * l = 1 := by simpa [hl2, pow_two] using pow_orderOf_eq_one l
  have hx2 : x * x = 1 := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [← map_mul, hl, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    have h' : (x : MulAut U) = 1 := by
      simpa using congrArg (fun z : L => (z : MulAut U)) h
    exact hρl h'
  have hπ1 : CFSG.Quasithin.B42Disp.modelProj L e x ≠ 1 := fun h =>
    hx1 (CFSG.Quasithin.B45Tor.modelProj_injective L hZL e (h.trans (map_one _).symm))
  let y : ModGL F4.tag K :=
    ((CFSG.Quasithin.B42Disp.modelProj L e x : F4.reeGamma K a) : ModGL F4.tag K)
  have hy : y ∈ F4.reeGamma K a := (CFSG.Quasithin.B42Disp.modelProj L e x).2
  have hsq : y ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, sq, ← map_mul, hx2, map_one, Subgroup.coe_one]
  have hy1 : y ≠ 1 := fun h => hπ1 (Subtype.ext h)
  have hV : ∀ v : U, v * v = 1 := fun v => by rw [← pow_two]; exact hU v
  have hindex : 2 ^ (6 * (2 * a + 1)) ≤
      (fixV (Subgroup.zpowers (x : MulAut U))).index := by
    rcases CFSG.Quasithin.B42F4.isZConj_or_isTConj ha hK' hy hsq hy1 with hz | ht
    · exact CFSG.Quasithin.B45Tor.two_pow_le_index_classZ (x := x) ha hK' hV L hZL e hz
    · exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
        (CFSG.Quasithin.B45Tor.two_pow_le_index_classT (x := x) ha hK' hV L hZL e ht)
  have hVP : IsPGroup 2 U :=
    isPGroup_iff_pow_pow_eq_one.mpr fun u => ⟨1, by simpa using hU u⟩
  have hidx := CFSG.Quasithin.H.index_eq_two_pow_rkIdx hVP
    (fixV (Subgroup.zpowers (x : MulAut U)))
  rw [hidx] at hindex
  have h6 : 6 * (2 * a + 1) ≤ rkIdx (fixV (Subgroup.zpowers (x : MulAut U))) :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hindex
  have h4 : 4 * n + 3 ≤ 6 * (2 * a + 1) := by omega
  change 4 * n + 3 ≤ rkIdx (fixV (Subgroup.zpowers (x : MulAut U)))
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
