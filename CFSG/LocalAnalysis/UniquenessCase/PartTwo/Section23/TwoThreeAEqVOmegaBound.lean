module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVOmegaW
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Dickson
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKSchur
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bL2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTransportModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem one_le_of_isOmegaMinus_four {X : Type} [Group X] {k : ℕ}
    (h : IsOmegaMinus X 4 k) : 1 ≤ k := by
  obtain ⟨-, K, hKf, hKfin, b, c, hcard, hbc, -⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have h2 : 1 < Nat.card K := Finite.one_lt_card
  have hk : 1 < 2 ^ k := hcard ▸ h2
  by_contra hk1
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos (by omega)
  rw [hk0, pow_zero] at hk
  omega

private theorem isL2_barSub_L_of_omegaMinus {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) {k : ℕ}
    (hOm : IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k) :
    IsL2 ↥(barSub ⊥ A hA c.L) (2 * k) :=
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.isL2_of_isOmegaMinus_four
    (one_le_of_isOmegaMinus_four hOm) hOm

private theorem inf_Z_ne_bot_of_normalizer {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) : A ⊓ D.Z ≠ ⊥ :=
  Ctx23L.inf_Z_ne_bot c hAV hAne ((Ctx23L.T_le_N c).trans hAN)

private theorem centralizer_le_M_of_inf_Z {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    Subgroup.centralizer (A : Set G) ≤ D.M := by
  obtain ⟨a, ha1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (inf_Z_ne_bot_of_normalizer c hAV hAne hAN)
  have haU : (a : G) ∈ D.U := Data.Z_le_U D a.2.2
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  refine (Subgroup.centralizer_le ?_).trans (Ctx23.centralizer_le_M c.toCtx23 haU ha1')
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact a.2.1

private theorem le_M_of_barSub_eq_bot {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hL0stab : c.L0 ≤ stabTil (⊥ : Subgroup G) A)
    (hbot : barSub (⊥ : Subgroup G) A hA c.L0 = ⊥) : c.L0 ≤ D.M := by
  have hL0C : c.L0 ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hxmem : actTil (⊥ : Subgroup G) A hA ⟨x, hL0stab hx⟩ ∈
        barSub (⊥ : Subgroup G) A hA c.L0 :=
      actTil_mem_barSub (⊥ : Subgroup G) A hA hx (hL0stab hx)
    rw [hbot] at hxmem
    have hact : actTil (⊥ : Subgroup G) A hA ⟨x, hL0stab hx⟩ = 1 :=
      Subgroup.mem_bot.mp hxmem
    have h1 := (actTil_eq_one_iff (⊥ : Subgroup G) A hA ⟨x, hL0stab hx⟩).1 hact a ha
    rw [Subgroup.mem_bot] at h1
    have h2 : x * a * x⁻¹ = a := mul_inv_eq_one.mp h1
    calc a * x = (x * a * x⁻¹) * x := by rw [h2]
      _ = x * a := by group
  obtain ⟨a, ha1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (inf_Z_ne_bot_of_normalizer c hAV hAne hAN)
  have haU : (a : G) ∈ D.U := Data.Z_le_U D a.2.2
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hCAM : Subgroup.centralizer (A : Set G) ≤ D.M := by
    refine (Subgroup.centralizer_le ?_).trans (Ctx23.centralizer_le_M c.toCtx23 haU ha1')
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact a.2.1
  exact hL0C.trans hCAM

private theorem Ctx23L.barSub_L0_eq_of_top {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A P : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hPL : P ≤ c.L) (hL0P : c.L0 = Hinf P)
    (hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A)
    (hmem : barSub (⊥ : Subgroup G) A hA P ≤ barSub (⊥ : Subgroup G) A hA c.L)
    (hPtop : (barSub (⊥ : Subgroup G) A hA P).subgroupOf
      (barSub (⊥ : Subgroup G) A hA c.L) = ⊤) :
    barSub (⊥ : Subgroup G) A hA c.L0 = barSub (⊥ : Subgroup G) A hA c.L := by
  have hPeq : barSub (⊥ : Subgroup G) A hA P = barSub (⊥ : Subgroup G) A hA c.L :=
    le_antisymm hmem (Subgroup.subgroupOf_eq_top.mp hPtop)
  have hperfP : ⁅barSub (⊥ : Subgroup G) A hA P, barSub (⊥ : Subgroup G) A hA P⁆ =
      barSub (⊥ : Subgroup G) A hA P := by
    rw [hPeq]
    exact barSub_commutator hA hLstab c.hL.1.2.1
  have hself : Hinf (barSub (⊥ : Subgroup G) A hA P) = barSub (⊥ : Subgroup G) A hA P :=
    le_antisymm (uc22p21c_Hinf_le _) (uc22p21c_le_Hinf le_rfl hperfP)
  have hH := Ctx23L.Hinf_barSub c (A := A) (P := P) hA hAN hPL
  rw [← hL0P, hself] at hH
  exact hH.symm.trans hPeq

private theorem Ctx23L.false_of_parabolic_proper {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A P : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAne : A ≠ ⊥) (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hPL : P ≤ c.L) (hL0P : c.L0 = Hinf P)
    (hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A)
    (hL0stab : c.L0 ≤ stabTil (⊥ : Subgroup G) A)
    {S_A : Sylow 2 ↥(barSub (⊥ : Subgroup G) A hA c.L)}
    (hSA : (S_A : Subgroup ↥(barSub (⊥ : Subgroup G) A hA c.L)) ≤
      (barSub (⊥ : Subgroup G) A hA P).subgroupOf (barSub (⊥ : Subgroup G) A hA c.L))
    {k : ℕ} (hL2 : IsL2 ↥(barSub (⊥ : Subgroup G) A hA c.L) (2 * k))
    (h2k : 2 ≤ 2 * k)
    (hmem : barSub (⊥ : Subgroup G) A hA P ≤ barSub (⊥ : Subgroup G) A hA c.L)
    (hPtop : (barSub (⊥ : Subgroup G) A hA P).subgroupOf
      (barSub (⊥ : Subgroup G) A hA c.L) ≠ ⊤) : False := by
  have hbotA : Hinf ((barSub (⊥ : Subgroup G) A hA P).subgroupOf
      (barSub (⊥ : Subgroup G) A hA c.L)) = ⊥ :=
    KTabD.hinf_eq_bot_of_isL2_of_sylow_le h2k hL2 S_A _ hSA hPtop
  have hsub : Hinf ((barSub (⊥ : Subgroup G) A hA P).subgroupOf
      (barSub (⊥ : Subgroup G) A hA c.L)) =
      (Hinf (barSub (⊥ : Subgroup G) A hA P)).subgroupOf
        (barSub (⊥ : Subgroup G) A hA c.L) :=
    Hinf_subgroupOf_of_le hmem
  have hHinfBot : Hinf (barSub (⊥ : Subgroup G) A hA P) = ⊥ := by
    refine le_bot_iff.mp fun x hx => ?_
    have hxK : (⟨x, (uc22p21c_Hinf_le _).trans hmem hx⟩ :
        ↥(barSub (⊥ : Subgroup G) A hA c.L)) ∈
        Hinf ((barSub (⊥ : Subgroup G) A hA P).subgroupOf
          (barSub (⊥ : Subgroup G) A hA c.L)) := by
      rw [hsub]
      exact hx
    rw [hbotA] at hxK
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxK)
  have hH := Ctx23L.Hinf_barSub c (A := A) (P := P) hA hAN hPL
  rw [← hL0P, hHinfBot] at hH
  exact absurd (le_M_of_barSub_eq_bot c hA hAV hAne hAN hL0stab hH.symm)
    (Ctx23L.L0_not_le_M c)

private theorem Ctx23L.barSub_L0_eq_of_parabolic {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    {P : Subgroup G} (hPL : P ≤ c.L) (hL0P : c.L0 = Hinf P)
    (hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A)
    (hL0stab : c.L0 ≤ stabTil (⊥ : Subgroup G) A)
    {S : Sylow 2 ↥c.L} (hSP : (S : Subgroup ↥c.L) ≤ P.subgroupOf c.L)
    {k : ℕ} (hOm : IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k) (h2k : 2 ≤ 2 * k) :
    barSub ⊥ A hA c.L0 = barSub ⊥ A hA c.L := by
  classical
  let ψ := barSubHom hA c.L hLstab
  have hψ : Function.Surjective ψ := barSubHom_surjective hA c.L hLstab
  let L_A : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)) := barSub ⊥ A hA c.L
  let P_A : Subgroup ↥L_A := (barSub ⊥ A hA P).subgroupOf L_A
  let S_A : Sylow 2 ↥L_A := S.mapSurjective (f := ψ) hψ
  have hSA : (S_A : Subgroup ↥L_A) ≤ P_A := by
    rw [show (S_A : Subgroup ↥L_A) = (S : Subgroup ↥c.L).map ψ from
      Sylow.coe_mapSurjective (P := S) (f := ψ) hψ]
    exact (Subgroup.map_mono hSP).trans_eq
      (barSubHom_map_subgroupOf hA hPL hLstab)
  have hL2 : IsL2 ↥L_A (2 * k) := isL2_barSub_L_of_omegaMinus c hA hOm
  have hmem : barSub ⊥ A hA P ≤ L_A := barSub_mono (⊥ : Subgroup G) A hA hPL
  by_cases hPtop : P_A = ⊤
  · exact Ctx23L.barSub_L0_eq_of_top c hA hAN hPL hL0P hLstab hmem hPtop
  · exact (Ctx23L.false_of_parabolic_proper c hA hAV hAne hAN hPL hL0P hLstab hL0stab
      hSA hL2 h2k hmem hPtop).elim

theorem Ctx23L.barSub_L0_eq_of_omegaMinus {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h209 : S20_9 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) {k : ℕ}
    (hOm : IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k) :
    barSub ⊥ A hA c.L0 = barSub ⊥ A hA c.L := by
  classical
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A :=
    le_inf ((Ctx23L.L_le_N c).trans hAN) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hL0stab : c.L0 ≤ stabTil (⊥ : Subgroup G) A := c.hL0L.trans hLstab
  obtain ⟨P, hP, hL0P⟩ := Ctx23L.exists_minTInvParabolic c h209 h1930
  have hPL : P ≤ c.L := (parabolicOf_iff.mp hP.1.1).1
  obtain ⟨S, hS⟩ := (parabolicOf_iff.mp hP.1.1).2
  have hSP : (S : Subgroup ↥c.L) ≤ P.subgroupOf c.L := Subgroup.le_normalizer.trans hS
  have h2k : 2 ≤ 2 * k := by have := one_le_of_isOmegaMinus_four hOm; omega
  exact barSub_L0_eq_of_parabolic c hA hAV hAne hAN hPL hL0P hLstab hL0stab hSP hOm h2k

private theorem pCoreOf_le_inf_centralizer_of_omegaMinus {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1930 : H1930 D) (h209 : S20_9 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) {k : ℕ}
    (hOm : IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k) :
    CFSG.Open.pCoreOf 2 c.L0 ≤ c.L0 ⊓ Subgroup.centralizer (A : Set G) := by
  classical
  have hL : barSub ⊥ A hA c.L0 = barSub ⊥ A hA c.L :=
    Ctx23L.barSub_L0_eq_of_omegaMinus c h1930 h209 hA hAV hAne hAN hOm
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A :=
    le_inf ((Ctx23L.L_le_N c).trans hAN) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hL0stab : c.L0 ≤ stabTil (⊥ : Subgroup G) A := c.hL0L.trans hLstab
  have hL2 : IsL2 ↥(barSub ⊥ A hA c.L) (2 * k) := isL2_barSub_L_of_omegaMinus c hA hOm
  let f : ↥c.L0 →* ↥(barSub ⊥ A hA c.L0) := barSubHom hA c.L0 hL0stab
  have hf : Function.Surjective f := barSubHom_surjective hA c.L0 hL0stab
  let eL : ↥(barSub ⊥ A hA c.L0) ≃* ↥(barSub ⊥ A hA c.L) := MulEquiv.subgroupCongr hL
  let f' : ↥c.L0 →* ↥(barSub ⊥ A hA c.L) := eL.toMonoidHom.comp f
  have hf' : Function.Surjective f' := eL.surjective.comp hf
  have hmap : ((CFSG.pCore 2 ↥c.L0).map f).map eL.toMonoidHom ≤
      CFSG.pCore 2 ↥(barSub ⊥ A hA c.L) := by
    have h := CFSG.LieType.BorelTits.map_pCore_le 2 f' hf'
    simpa [f', Subgroup.map_map] using h
  rw [pCore_eq_bot_of_isL2 hL2] at hmap
  have hmapbot : (CFSG.pCore 2 ↥c.L0).map f = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (H := (CFSG.pCore 2 ↥c.L0).map f) (f := eL.toMonoidHom) eL.injective).mp
      (le_bot_iff.mp hmap)
  have hO2ker : CFSG.pCore 2 ↥c.L0 ≤ f.ker :=
    (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥c.L0) (f := f)).mp hmapbot
  have hO2Ksub : CFSG.pCore 2 ↥c.L0 ≤
      (c.L0 ⊓ Subgroup.centralizer (A : Set G)).subgroupOf c.L0 := by
    rw [← barSubHom_ker hA c.L0 hL0stab]
    exact hO2ker
  intro x hx
  have hxL0 : x ∈ c.L0 := CFSG.LieType.BorelTits.pCoreOf_le 2 c.L0 hx
  have hxN : (⟨x, hxL0⟩ : ↥c.L0) ∈ CFSG.pCore 2 ↥c.L0 :=
    (CFSG.mem_openPCoreOf_iff ⟨x, hxL0⟩).1 hx
  exact Subgroup.mem_subgroupOf.mp (hO2Ksub hxN)

private abbrev schurN {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) : Subgroup ↥c.L0 :=
  CFSG.pCore 2 ↥c.L0

private theorem schur_hker {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hL0stab : c.L0 ≤ stabTil (⊥ : Subgroup G) A)
    (hK : K = c.L0 ⊓ Subgroup.centralizer (A : Set G))
    (hcomm : ⁅K, c.L0⁆ ≤ CFSG.Open.pCoreOf 2 c.L0) :
    ∀ x ∈ (barSubHom hA c.L0 hL0stab).ker, ∀ y : ↥c.L0,
      x * y * x⁻¹ * y⁻¹ ∈ schurN c := by
  intro x hx y
  have hxK : (x : G) ∈ K := by
    rw [barSubHom_ker, ← hK] at hx
    exact Subgroup.mem_subgroupOf.mp hx
  have hmem : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈
      CFSG.Open.pCoreOf 2 c.L0 :=
    hcomm (Subgroup.commutator_mem_commutator hxK y.2)
  exact (CFSG.mem_openPCoreOf_iff _).1 (by simpa using hmem)

private abbrev schurX {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) : Type :=
  ↥c.L0 ⧸ schurN c

private abbrev schurZ {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) (K : Subgroup G) :
    Subgroup (schurX c) :=
  (K.subgroupOf c.L0).map (QuotientGroup.mk' (schurN c))

private theorem schurZ_center_odd {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hL0stab : c.L0 ≤ stabTil (⊥ : Subgroup G) A)
    (hK : K = c.L0 ⊓ Subgroup.centralizer (A : Set G))
    (hcomm : ⁅K, c.L0⁆ ≤ CFSG.Open.pCoreOf 2 c.L0) :
    schurZ c K ≤ Subgroup.center (schurX c) ∧ Odd (Nat.card (schurZ c K)) := by
  have hker := schur_hker c hA hL0stab hK hcomm
  have hZcenter : schurZ c K ≤ Subgroup.center (schurX c) := by
    rw [show schurZ c K = (barSubHom hA c.L0 hL0stab).ker.map
        (QuotientGroup.mk' (schurN c)) by rw [barSubHom_ker, ← hK]]
    exact image_ker_le_center_of_commutator_le (N := schurN c) hker
  have hO2X : CFSG.pCore 2 (schurX c) = ⊥ :=
    CFSG.Timmesfeld.Bridge.RootClosure.pCore_quotient_pCore_eq_bot (K := ↥c.L0)
  exact ⟨hZcenter, (odd_card_center_bar2 (schurX c) hO2X).of_dvd_nat
    (Subgroup.card_dvd_of_le hZcenter)⟩

private theorem schurZ_eq_bot_to_le {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A K : Subgroup G} (hK : K = c.L0 ⊓ Subgroup.centralizer (A : Set G))
    (hZbot : schurZ c K = ⊥) : K ≤ CFSG.Open.pCoreOf 2 c.L0 := by
  have hmapbot : (K.subgroupOf c.L0).map (QuotientGroup.mk' (schurN c)) = ⊥ := hZbot
  have hKsubN : K.subgroupOf c.L0 ≤ schurN c := by
    have h := (Subgroup.map_eq_bot_iff (H := K.subgroupOf c.L0)
      (f := QuotientGroup.mk' (schurN c))).mp hmapbot
    rwa [QuotientGroup.ker_mk'] at h
  intro x hx
  have hx' : x ∈ c.L0 ⊓ Subgroup.centralizer (A : Set G) := hK ▸ hx
  have hxL0 : x ∈ c.L0 := hx'.1
  have hxK : (⟨x, hxL0⟩ : ↥c.L0) ∈ K.subgroupOf c.L0 := by
    rw [Subgroup.mem_subgroupOf, hK]
    exact hx'
  exact (CFSG.mem_openPCoreOf_iff ⟨x, hxL0⟩).2 (hKsubN hxK)

private theorem inf_centralizer_le_pCoreOf_of_schur {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A K : Subgroup G} (hA : IsElemAbelian 2 A) {k : ℕ}
    (hL : barSub ⊥ A hA c.L0 = barSub ⊥ A hA c.L)
    (hL0stab : c.L0 ≤ stabTil (⊥ : Subgroup G) A)
    (hL2 : IsL2 ↥(barSub ⊥ A hA c.L) (2 * k))
    (hK : K = c.L0 ⊓ Subgroup.centralizer (A : Set G))
    (hKnormalL0 : (K.subgroupOf c.L0).Normal)
    (hcomm : ⁅K, c.L0⁆ ≤ CFSG.Open.pCoreOf 2 c.L0)
    (hO2le : CFSG.Open.pCoreOf 2 c.L0 ≤ K) :
    K ≤ CFSG.Open.pCoreOf 2 c.L0 := by
  classical
  have hNleK : schurN c ≤ K.subgroupOf c.L0 := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hO2le ((CFSG.mem_openPCoreOf_iff x).2 hx))
  haveI : (schurZ c K).Normal :=
    hKnormalL0.map (QuotientGroup.mk' (schurN c)) (QuotientGroup.mk'_surjective _)
  obtain ⟨hZcenter, hZodd⟩ := schurZ_center_odd c hA hL0stab hK hcomm
  haveI : Group.IsPerfect ↥c.L0 := Subgroup.isPerfect_iff.mpr c.hL0.1.2.1
  haveI : Group.IsPerfect (schurX c) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (schurN c))
      (QuotientGroup.mk'_surjective _)
  have hperfX : ⁅(⊤ : Subgroup (schurX c)), (⊤ : Subgroup (schurX c))⁆ = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  let f : ↥c.L0 →* ↥(barSub ⊥ A hA c.L0) := barSubHom hA c.L0 hL0stab
  let eL : ↥(barSub ⊥ A hA c.L0) ≃* ↥(barSub ⊥ A hA c.L) := MulEquiv.subgroupCongr hL
  let f' : ↥c.L0 →* ↥(barSub ⊥ A hA c.L) := eL.toMonoidHom.comp f
  have hf' : Function.Surjective f' := eL.surjective.comp (barSubHom_surjective hA c.L0 hL0stab)
  have hker' : f'.ker = K.subgroupOf c.L0 := by
    rw [show f' = eL.toMonoidHom.comp f from rfl,
      MonoidHom.ker_comp_of_injective f eL.toMonoidHom eL.injective,
      barSubHom_ker, ← hK]
  let e : (schurX c ⧸ schurZ c K) ≃* ↥(barSub ⊥ A hA c.L) :=
    (QuotientGroup.quotientQuotientEquivQuotient (schurN c) (K.subgroupOf c.L0) hNleK).trans
      ((QuotientGroup.quotientMulEquivOfEq hker').symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective f' hf'))
  have hshape : IsL2 (schurX c ⧸ schurZ c K) (2 * k) :=
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL2
  have hZbot : schurZ c K = ⊥ :=
    kSchurL2_holds (schurX c) (2 * k) hperfX (schurZ c K) hZcenter hZodd (Or.inl hshape)
  exact schurZ_eq_bot_to_le c hK hZbot

theorem Ctx23L.inf_centralizer_le_pCore_of_omegaMinus {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1930 : H1930 D) (h209 : S20_9 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) {k : ℕ}
    (hOm : IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k) :
    c.L0 ⊓ Subgroup.centralizer (A : Set G) ≤ CFSG.Open.pCoreOf 2 c.L0 := by
  classical
  have hL : barSub ⊥ A hA c.L0 = barSub ⊥ A hA c.L :=
    Ctx23L.barSub_L0_eq_of_omegaMinus c h1930 h209 hA hAV hAne hAN hOm
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A :=
    le_inf ((Ctx23L.L_le_N c).trans hAN) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hL0stab : c.L0 ≤ stabTil (⊥ : Subgroup G) A := c.hL0L.trans hLstab
  have hL2 : IsL2 ↥(barSub ⊥ A hA c.L) (2 * k) := isL2_barSub_L_of_omegaMinus c hA hOm
  let K : Subgroup G := c.L0 ⊓ Subgroup.centralizer (A : Set G)
  have hKleL0 : K ≤ c.L0 := inf_le_left
  have hKH : K ≤ c.L0 ⊔ D.T := hKleL0.trans le_sup_left
  have hHnA : c.L0 ⊔ D.T ≤ Subgroup.normalizer (A : Set G) :=
    sup_le (c.hL0L.trans ((Ctx23L.L_le_N c).trans hAN))
      ((Ctx23L.T_le_N c).trans hAN)
  have hHnL0 : c.L0 ⊔ D.T ≤ Subgroup.normalizer (c.L0 : Set G) :=
    sup_le Subgroup.le_normalizer c.hL0.1.1
  have hHnC : c.L0 ⊔ D.T ≤
      Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) :=
    hHnA.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer A)
  have hHnK : c.L0 ⊔ D.T ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf hHnL0 hHnC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hKnormalH : (K.subgroupOf (c.L0 ⊔ D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHnK
  have hKM : K ≤ D.M :=
    inf_le_right.trans (centralizer_le_M_of_inf_Z c hAV hAne hAN)
  have hcomm : ⁅K, c.L0⁆ ≤ CFSG.Open.pCoreOf 2 c.L0 :=
    Ctx23L.commutator_le_pCoreOf c hKH hKnormalH hKM
  have hKnormalL0 : (K.subgroupOf c.L0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleL0).mpr
      (le_sup_left.trans hHnK)
  have hO2le : CFSG.Open.pCoreOf 2 c.L0 ≤ K :=
    pCoreOf_le_inf_centralizer_of_omegaMinus c h1930 h209 hA hAV hAne hAN hOm
  exact inf_centralizer_le_pCoreOf_of_schur c hA hL hL0stab hL2 rfl hKnormalL0 hcomm hO2le

private theorem T_le_normalizer_W23_1 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) :
    D.T ≤ Subgroup.normalizer (W23_1 c : Set G) := by
  rw [W23_1]
  intro t ht
  refine uc22p22v_mem_normalizer_conjClosure (N := c.L0) (E := D.Z) ?_ ?_
  · intro x hx z hz
    refine ⟨t * x * t⁻¹, ?_, t * z * t⁻¹, ?_, by group⟩
    · exact (Subgroup.mem_normalizer_iff.mp (c.hL0.1.1 ht) x).1 hx
    · have hzt : z * t = t * z :=
        Subgroup.mem_centralizer_iff.mp (uc22main1_T_le_centralizer D ht) z hz
      rw [show t * z * t⁻¹ = z by rw [← hzt]; group]
      exact hz
  · intro x hx z hz
    refine ⟨t⁻¹ * x * t, ?_, t⁻¹ * z * t, ?_, by group⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp (c.hL0.1.1 (D.T.inv_mem ht)) x).1 hx
    · have hzt : z * t⁻¹ = t⁻¹ * z :=
        Subgroup.mem_centralizer_iff.mp (uc22main1_T_le_centralizer D (D.T.inv_mem ht)) z hz
      rw [show t⁻¹ * z * t = z by rw [← hzt]; group]
      exact hz

theorem Ctx23L.aBar_W23_1_le_of_omegaMinus {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h209 : S20_9 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hirr : IrrOn c.L A) {k : ℕ}
    (hOm : IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k)
    (hNat : NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k) (hW : IsElemAbelian 2 (W23_1 c)) :
    aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k := by
  have hL : barSub ⊥ A hA c.L0 = barSub ⊥ A hA c.L :=
    Ctx23L.barSub_L0_eq_of_omegaMinus c h1930 h209 hA hAV hAne hAN hOm
  have hCA : c.L0 ⊓ Subgroup.centralizer (A : Set G) ≤ CFSG.Open.pCoreOf 2 c.L0 :=
    Ctx23L.inf_centralizer_le_pCore_of_omegaMinus c h1930 h209 hA hAV hAne hAN hOm
  have hT : D.T ≤ Subgroup.normalizer (A : Set G) := (Ctx23L.T_le_N c).trans hAN
  have hAL : c.L ≤ Subgroup.normalizer (A : Set G) := (Ctx23L.L_le_N c).trans hAN
  have hAL0 : c.L0 ≤ Subgroup.normalizer (A : Set G) := c.hL0L.trans hAL
  have hAW : A ≤ W23_1 c := A_le_W23_1 c hA hAV hAne hT hAL hAL0 hirr hL
  have hM₁ : c.L0 ⊔ D.T ≤ Subgroup.normalizer (A : Set G) := sup_le hAL0 hT
  have hM₂ : c.L0 ⊔ D.T ≤ Subgroup.normalizer (W23_1 c : Set G) :=
    sup_le (uc22p22v_le_normalizer_conjClosure c.L0 D.Z) (T_le_normalizer_W23_1 c)
  have hfaith : ∀ x ∈ c.L0 ⊔ D.T, (∀ a ∈ A, x * a * x⁻¹ = a) →
      ∀ w ∈ W23_1 c, x * w * x⁻¹ = w := by
    intro x hx hfix w hw
    have hxCA : x ∈ (c.L0 ⊔ D.T) ⊓ Subgroup.centralizer (A : Set G) := by
      refine ⟨hx, ?_⟩
      change x ∈ Subgroup.centralizer (A : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      calc a * x = (x * a * x⁻¹) * x := by rw [hfix a ha]
        _ = x * a := by group
    have hxW : x ∈ Subgroup.centralizer (W23_1 c : Set G) :=
      Ctx23L.le_centralizer_W23_1 c hM₁ hCA hxCA
    have hwx : w * x = x * w := Subgroup.mem_centralizer_iff.mp hxW w hw
    calc x * w * x⁻¹ = (w * x) * x⁻¹ := by rw [← hwx]
      _ = w := by group
  calc aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW
      ≤ aBar (c.L0 ⊔ D.T) ⊥ A hA :=
        aBar_le_of_le_of_faithful hA hW hAW hM₁ hM₂ hfaith
    _ ≤ k := aBar_le_of_omegaMinus_of_barSub_eq c hA hL hOm hNat

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
