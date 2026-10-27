module

public import CFSG.Quasithin.H13.AS91Sec4EightFus
public import CFSG.Quasithin.Vol2.Asc94.TSCaseII
public import CFSG.Quasithin.Vol2.Asc94.TSF6Model
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Quasithin.H13.AS91Sec4EightS

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour
open scoped Pointwise

theorem card_of_lieModel_PSL_five {X : Type} [Group X]
    (hX : CFSG.Blueprint.LieModel X .PSL 5 2 1) : Nat.card X = 9999360 := by
  have hc := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hc).1 rfl]
  decide

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem ncard_conj_tr_le (e : ↥(CFSG.Quasithin.A94.Cz D.tb) ≃* CFSG.Quasithin.A94.L52.Hc) :
    ∃ A : Subgroup CFSG.Quasithin.A94.L52.Hc, (A = CFSG.Quasithin.A94.L52.A1 ∨
      A = CFSG.Quasithin.A94.L52.A2) ∧
      {a : ↥D.Mb | a ∈ CFSG.Quasithin.A94.tr e A ∧ a ≠ 1 ∧
        CFSG.Quasithin.A94.InZG D.tb a}.ncard ≤ 27 := by
  obtain ⟨X, hX⟩ := CFSG.Quasithin.A94.exists_tr_eq_of_le_Cz e (D.Rstar_le_Cb hOut hTw hHat)
  have hXab : IsElemAbelian 2 X := CFSG.Quasithin.A94.isElemAbelian_of_tr e
    (hX ▸ D.isElemAbelian_Rstar hOut hTw hHat)
  have hXcard : Nat.card X = 64 := by
    rw [← CFSG.Quasithin.A94.card_tr e, hX, D.card_Rstar hOut hTw hHat]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXp : IsPGroup 2 X := IsPGroup.of_card (n := 6) (by rw [hXcard]; norm_num)
  obtain ⟨P, hXP⟩ := hXp.exists_le_sylow
  have hfac : (Nat.card CFSG.Quasithin.A94.L52.Hc).factorization 2 = 10 := by
    rw [CFSG.Quasithin.A94.L52.card_Hc, show (21504 : ℕ) = 2 ^ 10 * 21 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd]
  let T : Sylow 2 CFSG.Quasithin.A94.L52.Hc :=
    Sylow.ofCard CFSG.Quasithin.A94.L52.Tm (by rw [CFSG.Quasithin.A94.L52.card_Tm, hfac])
  have hT : (T : Subgroup CFSG.Quasithin.A94.L52.Hc) = CFSG.Quasithin.A94.L52.Tm :=
    Sylow.coe_ofCard _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq CFSG.Quasithin.A94.L52.Hc P T
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup CFSG.Quasithin.A94.L52.Hc,
      Y = X.map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hYT : Y ≤ CFSG.Quasithin.A94.L52.Tm := by
    rw [hYdef]
    rw [← hT, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hXP
  have hYab : IsElemAbelian 2 Y := by
    subst hYdef
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      change (a : CFSG.Quasithin.A94.L52.Hc) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hXab.1.is_comm.comm (⟨a', ha'⟩ : X) ⟨b', hb'⟩))
    · obtain ⟨y', hy', rfl⟩ := hy
      rw [← map_pow, hXab.2 y' hy', map_one]
  have hYcard : Nat.card Y = 64 := by
    rw [hYdef, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, hXcard]
  set c : ↥D.Mb := CFSG.Quasithin.A94.emb e g with hc
  have htr : CFSG.Quasithin.A94.tr e Y = (D.Rstar).map (MulAut.conj c).toMonoidHom := by
    rw [← hX, hYdef]
    exact CFSG.Quasithin.A94.tr_cj e g X
  have hset : {a : ↥D.Mb | a ∈ CFSG.Quasithin.A94.tr e Y ∧ a ≠ 1 ∧
        CFSG.Quasithin.A94.InZG D.tb a} =
      (fun a => c * a * c⁻¹) '' {a : ↥D.Mb | a ∈ D.Rstar ∧ a ≠ 1 ∧
        CFSG.Quasithin.A94.InZG D.tb a} := by
    ext b
    rw [htr]
    constructor
    · rintro ⟨⟨a, haR, rfl⟩, hb1, x, hx⟩
      refine ⟨a, ⟨haR, fun h1 => hb1 (by rw [h1, map_one]), x * c, ?_⟩, rfl⟩
      have : c⁻¹ * ((MulAut.conj c).toMonoidHom a) * c = a := by
        change c⁻¹ * (c * a * c⁻¹) * c = a
        group
      rw [← this, hx]
      group
    · rintro ⟨a, ⟨haR, ha1, x, hx⟩, rfl⟩
      refine ⟨⟨a, haR, rfl⟩, fun h1 => ha1 ?_, x * c⁻¹, ?_⟩
      · have h1' : c * a * c⁻¹ = 1 := h1
        calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
          _ = 1 := by rw [h1']; group
      · rw [hx]
        group
  refine ⟨Y, CFSG.Quasithin.A94.L52.f6Model_holds Y hYT hYab hYcard, ?_⟩
  rw [hset, Set.ncard_image_of_injective _ (fun a b hab => by
    have : c⁻¹ * (c * a * c⁻¹) * c = c⁻¹ * (c * b * c⁻¹) * c := by rw [hab]
    simpa using this)]
  exact D.ncard_conj_Rstar_le hOut hTw hHat

theorem not_caseII (e : ↥(CFSG.Quasithin.A94.Cz D.tb) ≃* CFSG.Quasithin.A94.L52.Hc)
    (h1 : normalizer (CFSG.Quasithin.A94.tr e CFSG.Quasithin.A94.L52.U1 : Set ↥D.Mb) =
      CFSG.Quasithin.A94.Cz D.tb)
    (h2 : normalizer (CFSG.Quasithin.A94.tr e CFSG.Quasithin.A94.L52.U2 : Set ↥D.Mb) =
      CFSG.Quasithin.A94.Cz D.tb) : False := by
  have S := D.setting hOut hTw hHat e
  obtain ⟨-, -, hA1, hA2, -, -⟩ :=
    CFSG.Quasithin.A94.caseII_facts CFSG.Quasithin.A94.L52.f6Model_holds S h1 h2
  obtain ⟨A, hA, hle⟩ := D.ncard_conj_tr_le hOut hTw hHat e
  rcases hA with rfl | rfl
  · change {a : ↥D.Mb | a ∈ CFSG.Quasithin.A94.tr e CFSG.Quasithin.A94.L52.A1 ∧ a ≠ 1 ∧
      CFSG.Quasithin.A94.InZG D.tb a}.ncard = 45 at hA1
    omega
  · change {a : ↥D.Mb | a ∈ CFSG.Quasithin.A94.tr (CFSG.Quasithin.A94.swapIso e)
      CFSG.Quasithin.A94.L52.A1 ∧ a ≠ 1 ∧ CFSG.Quasithin.A94.InZG D.tb a}.ncard = 45 at hA2
    rw [CFSG.Quasithin.A94.tr_swap_A1] at hA2
    omega

theorem nonempty_mulEquiv_m24 (hM : CFSG.CGT.T75P.M24SylowInput) [IsSimpleGroup ↥D.Mb] :
    Nonempty (↥D.Mb ≃* CFSG.Blueprint.NativeSporadic.M24) := by
  obtain ⟨e⟩ := D.nonempty_cb_mulEquiv hOut hTw hHat
  have S := D.setting hOut hTw hHat e
  have hne : normalizer (CFSG.Quasithin.A94.tr e CFSG.Quasithin.A94.L52.U1 : Set ↥D.Mb) ≠
        CFSG.Quasithin.A94.Cz D.tb ∨
      normalizer (CFSG.Quasithin.A94.tr e CFSG.Quasithin.A94.L52.U2 : Set ↥D.Mb) ≠
        CFSG.Quasithin.A94.Cz D.tb := by
    by_contra hcon
    push Not at hcon
    exact D.not_caseII hOut hTw hHat e hcon.1 hcon.2
  rcases CFSG.Quasithin.A94.caseLM hM S hne with hL | hM24
  · exfalso
    have hcard := card_of_lieModel_PSL_five hL
    have hdvd : Nat.card D.Mz ∣ Nat.card ↥D.Mb := Subgroup.card_subgroup_dvd_card _
    rw [D.card_Mz hOut hTw hHat, hcard] at hdvd
    norm_num at hdvd
  · exact hM24

end Data41

end CFSG.Quasithin.H13.AS91
