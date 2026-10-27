module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourL1
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourKGCentUnitary
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourKGCentOm
import CFSG.LocalAnalysis.StandardType.GGKGCentPSUShort
import CFSG.LocalAnalysis.StandardType.GGKGPosLocalHypTw
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGKGPosSpStd
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOrb
import CFSG.LocalAnalysis.StandardType.GGF4SharedRefl
import CFSG.LocalAnalysis.StandardType.GGRankOneShared
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross
import CFSG.LocalAnalysis.StandardType.GGKGCentSpMatrix
import CFSG.LocalAnalysis.StandardType.GGReflectionBasic
import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4Facts
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.Timmesfeld.Transvection.PresSp
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher


theorem ggF4QGeFourKGCentInput_S1 (hMp : GGInnerDiagMpInput) (ha₀ : GGLNoncyclicInput)
    (hTBF : GGTBFixInput) (hFC : GGResNbrFixCentralizesInput) : GGF4QGeFourKGCentInput .S1 := by
  intro G _ _ p B Bs x L D J y K hcfg hRC e hpres f hf hpf hrow X Y hXY t ht2 htB htX
  have : NeZero f := ⟨by omega⟩
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hodd : Odd p := hpp.odd_of_ne_two hp2
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  obtain ⟨hDB, -, -, hxD, -⟩ := hcfg.1.1.2.2.1
  have hxB : x ∈ Bs := hcfg.1.1.2.1.1 (hDB hxD)
  have hyB : y ∈ Bs := by
    refine hcfg.1.1.2.1.1 (hDB ?_)
    rw [hcfg.2.2.2.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hmem : ∀ Z : Subgroup G, Z = L ∨ Z = K → ∃ z, z ∈ Bs ∧
      CFSG.Assembly.IsSubnormal Z (Subgroup.centralizer ({z} : Set G)) := by
    rintro Z (rfl | rfl)
    · exact ⟨x, hxB, hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.2.1⟩
    · exact ⟨y, hyB, hcfg.2.2.2.1.2.2.2.2.1.2.1⟩
  have hXm : X = L ∨ X = K := by rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hYm : Y = L ∨ Y = K := by rcases hXY with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hXA : ggAutomizer X Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    rcases hXm with rfl | rfl
    exacts [le_sup_left, le_sup_right]
  have hYA : ggAutomizer Y Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    rcases hYm with rfl | rfl
    exacts [le_sup_left, le_sup_right]
  obtain ⟨xX, hxXB, hXx⟩ := hmem X hXm
  obtain ⟨yY, hyYB, hYy⟩ := hmem Y hYm
  obtain ⟨ψX, hkerX, hrX, hTBX⟩ := ggKGPosSp_of_f4_mp hMp hcfg hf hpf hrow X hXm
  obtain ⟨ψ, ζ, hker, hrY, hTBY, hζ, htor⟩ := ggKGPosSp_of_f4_mp_toral hMp hcfg hf hpf hrow Y hYm
  have hposX : GGTableBPosImage p Bs .PSp 3 f X := ⟨ψX, hkerX, hrX, hTBX⟩
  have hposY : GGTableBPosImage p Bs .PSp 3 f Y := ⟨ψ, hker, hrY, hTBY⟩
  obtain ⟨εX, hεX, -, -⟩ := hTBX
  obtain ⟨εY, hεY, hlevY, -⟩ := hTBY
  have hcen : Subgroup.center (ggU .PSp 3 f).K = ⊥ :=
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (K := GaloisField 2 f) (n := 3)
      (by norm_num)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hcen.le
  have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_PSp_three]
    rfl
  obtain ⟨φX, hφX, hrefX, hX01, hX12, hX02, -⟩ :=
    exists_f4Triple_map_of_weyl hpp hp2 hEl hNT hAind hpres hXA εX hεX (Equiv.refl _) hM
  obtain ⟨φY, hφY, hrefY, hY01, hY12, hY02, -⟩ :=
    exists_f4Triple_map_of_weyl hpp hp2 hEl hNT hAind hpres hYA εY hεY (Equiv.refl _) hM
  obtain ⟨R, hRs⟩ := F4Model.exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  obtain ⟨u, v, c, d, huv⟩ := R.exists_shared_refl
    (fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (hrefX k)) hX01 hX12 hX02
    (fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (hrefY k)) hY01 hY12 hY02
  have hprod : ∀ (φ : (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).Group →*
      CoxeterMatrix.F₄.Group) (l : List (Fin 3)),
      φ ((l.map fun j => (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple
          ((Equiv.refl (Fin 3)) j)).prod) =
        (l.map fun j => φ ((coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple
            ((Equiv.refl (Fin 3)) j))).prod := by
    intro φ l
    rw [map_list_prod, List.map_map]
    rfl
  obtain ⟨wX, hwX⟩ : ∃ w : (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).Group,
      w = (u.map fun j => (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple
        ((Equiv.refl (Fin 3)) j)).prod := ⟨_, rfl⟩
  obtain ⟨wY, hwY⟩ : ∃ w : (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).Group,
      w = (v.map fun j => (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple
        ((Equiv.refl (Fin 3)) j)).prod := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : MulAut ↥Bs, r = ((εY (wY *
      (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple ((Equiv.refl (Fin 3)) d) * wY⁻¹) :
        ↥(ggAutomizer Y Bs)) : MulAut ↥Bs) := ⟨_, rfl⟩
  have hrX : r = ((εX (wX * (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple
      ((Equiv.refl (Fin 3)) c) * wX⁻¹) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
    have key : ∀ (φ : (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).Group →*
        CoxeterMatrix.F₄.Group) (l : List (Fin 3)) (k : Fin 3),
        φ ((l.map fun j => (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple
            ((Equiv.refl (Fin 3)) j)).prod *
          (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple ((Equiv.refl (Fin 3)) k) *
          ((l.map fun j => (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple
            ((Equiv.refl (Fin 3)) j)).prod)⁻¹) =
        (l.map fun j => φ ((coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple
            ((Equiv.refl (Fin 3)) j))).prod *
          φ ((coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple ((Equiv.refl (Fin 3)) k)) *
          ((l.map fun j => φ ((coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple
            ((Equiv.refl (Fin 3)) j))).prod)⁻¹ := by
      intro φ l k
      rw [map_mul, map_mul, map_inv, hprod]
    have hYX : φY (wY * (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple
          ((Equiv.refl (Fin 3)) d) * wY⁻¹) =
        φX (wX * (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple
          ((Equiv.refl (Fin 3)) c) * wX⁻¹) := by
      rw [hwX, hwY]
      exact (key φY v d).trans (huv.symm.trans (key φX u c).symm)
    rw [hr, ← hφY, hYX, hφX]
  have hrAY : r ∈ ggAutomizer Y Bs := hr ▸ (εY _).2
  have hrAX : r ∈ ggAutomizer X Bs := hrX ▸ (εX _).2
  have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hεY ⟨wY, _, hr⟩
  have hr1 : r ≠ 1 := GGIsReflection.ne_one hpp hrefl
  have hqX := isQuasisimple_ggRankOneIn_of_tableBPosImage_PSp hpp hp2 hEl hNT hf hposX hrAX hrefl
  have hqY := isQuasisimple_ggRankOneIn_of_tableBPosImage_PSp hpp hp2 hEl hNT hf hposY hrAY hrefl
  have hSYX : ggRankOneIn Y Bs r = ggRankOneIn X Bs r :=
    ggRankOneIn_eq_of_mem_ggAutomizer hodd hEl hyYB hxXB hYy hXx (hcfg.bstar_le_normalizer hXm)
      hrAY hrAX hqY hqX hrefl.1 hr1
  have hγ : weylAction (ggU .PSp 3 f).D.isFiniteType wY
      (Pi.single ((Equiv.refl (Fin 3)) d) 1) ∈ roots (isFiniteType_cartanC 3) ∅ :=
    Set.mem_union_left _ ⟨wY, _, rfl⟩
  obtain ⟨ρ, hρ⟩ := exists_stdVec_of_mem_roots hγ
  have hfix : ∀ c : GaloisField 2 f, t * ψ (elt ρ c) * t⁻¹ = ψ (elt ρ c) := by
    intro c
    have hS : ψ (elt ρ c) ∈ ggRankOneIn X Bs r := by
      rw [← hSYX, hr, hlevY wY ((Equiv.refl (Fin 3)) d)]
      exact ⟨elt ρ c, Subgroup.mem_sup_left (elt_mem_rootGroup hρ c), rfl⟩
    have hSX : ggRankOneIn X Bs r ≤ X := (ggOTwoPrime_le _).trans inf_le_left
    have hc := Subgroup.mem_centralizer_iff.mp htX _ (hSX hS)
    rw [← hc, mul_inv_cancel_right]
  let ψS : StatedSp 3 (GaloisField 2 f) →* G := ψ
  have hinjS : Function.Injective ψS := hinj
  have hrS : ψS.range = Y := hrY
  have hcenS : Subgroup.center (StatedSp 3 (GaloisField 2 f)) = ⊥ := hcen
  have hfixS : ∀ c : GaloisField 2 f, t * ψS (elt ρ c) * t⁻¹ = ψS (elt ρ c) := hfix
  have htorS : ∀ i : Fin 3, ∃ b ∈ Bs, ∀ z, b * ψS z * b⁻¹ =
      ψS (KGCentSp.diagSp (Pi.mulSingle i ζ) * z * (KGCentSp.diagSp (Pi.mulSingle i ζ))⁻¹) :=
    htor
  have htH : t ∈ Subgroup.centralizer (ggHyperplane Bs 1 : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (Subgroup.map_subtype_le _)) htB
  have hNY : t ∈ Subgroup.normalizer (ψS.range : Set G) := by
    rw [hrS]
    rcases hYm with rfl | rfl
    · exact ggF4QGeFour_centralizer_le_normalizer_L ha₀ hcfg (one_mem _) htH
    · exact ggF4QGeFour_centralizer_le_normalizer_K_S1 ha₀ hTBF hFC hcfg hRC e hpres hrow
        (one_mem _) htH
  obtain ⟨β, hβ⟩ := ggF4_exists_pullAut hinjS hNY
  obtain ⟨g, σ, hβgσ⟩ := KGCentSp.exists_eq_conj_mul_fieldSp (n := 3) (F := GaloisField 2 f)
    (by norm_num) β
  have hσ : σ = RingEquiv.refl _ := by
    refine KGCentSp.eq_refl_of_conj_fieldSp_elt (g := g) (r := ρ) fun c => ?_
    have h1 : β (elt ρ c) = elt ρ c := hinjS ((hβ _).trans (hfixS c))
    rw [hβgσ, MulAut.mul_apply, MulAut.conj_apply] at h1
    exact h1
  have hβg : ∀ z, β z = g * z * g⁻¹ := by
    intro z
    rw [hβgσ, hσ, KGCentSp.fieldSp_refl, mul_one, MulAut.conj_apply]
  have hcomm : ∀ i : Fin 3,
      Commute g (KGCentSp.diagSp (n := 3) (F := GaloisField 2 f) (Pi.mulSingle i ζ)) := by
    intro i
    obtain ⟨b, hbB, hbD⟩ := htorS i
    set Dg : StatedSp 3 (GaloisField 2 f) := KGCentSp.diagSp (Pi.mulSingle i ζ) with hDg
    have htb : t * b = b * t := (Subgroup.mem_centralizer_iff.mp htB b hbB).symm
    have hDz : ∀ z, β (Dg * z * Dg⁻¹) = Dg * β z * Dg⁻¹ := by
      intro z
      apply hinjS
      rw [hβ, ← hbD, ← hbD, hβ]
      calc t * (b * ψS z * b⁻¹) * t⁻¹ = (t * b) * ψS z * (t * b)⁻¹ := by group
        _ = (b * t) * ψS z * (b * t)⁻¹ := by rw [htb]
        _ = b * (t * ψS z * t⁻¹) * b⁻¹ := by group
    have hcz : (Dg * g)⁻¹ * (g * Dg) ∈ Subgroup.center (StatedSp 3 (GaloisField 2 f)) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h1 := hDz w
      rw [hβg, hβg] at h1
      have h2 : g * (Dg * w * Dg⁻¹) * g⁻¹ = (g * Dg) * w * (g * Dg)⁻¹ := by group
      have h3 : Dg * (g * w * g⁻¹) * Dg⁻¹ = (Dg * g) * w * (Dg * g)⁻¹ := by group
      rw [h2, h3] at h1
      calc w * ((Dg * g)⁻¹ * (g * Dg))
          = (Dg * g)⁻¹ * ((Dg * g) * w * (Dg * g)⁻¹) * (g * Dg) := by group
        _ = (Dg * g)⁻¹ * ((g * Dg) * w * (g * Dg)⁻¹) * (g * Dg) := by rw [← h1]
        _ = (Dg * g)⁻¹ * (g * Dg) * w := by group
    rw [hcenS, Subgroup.mem_bot, inv_mul_eq_one] at hcz
    exact hcz.symm
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hpp.one_lt.ne hζ
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hgq : g ^ (Fintype.card (GaloisField 2 f) - 1) = 1 :=
    KGCentSp.pow_card_sub_one_eq_one fun a b hab =>
      KGCentSp.mat_eq_zero_of_commute_diagSp hζ1 hζ2 hcomm hab
  obtain ⟨k, hk⟩ := ht2
  have hβpow : ∀ (n : ℕ) (z : StatedSp 3 (GaloisField 2 f)),
      ψS ((β ^ n) z) = t ^ n * ψS z * (t ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, MulAut.mul_apply, ih, hβ, pow_succ]
      group
  have hβc : β = MulAut.conj g := MulEquiv.ext fun z => by rw [hβg, MulAut.conj_apply]
  have hg2 : g ^ (2 ^ k) = 1 := by
    have hc : g ^ (2 ^ k) ∈ Subgroup.center (StatedSp 3 (GaloisField 2 f)) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 : ψS ((β ^ (2 ^ k)) z) = ψS z := by rw [hβpow, hk, one_mul, inv_one, mul_one]
      have h2 : (β ^ (2 ^ k)) z = (g ^ (2 ^ k)) * z * (g ^ (2 ^ k))⁻¹ := by
        rw [hβc, ← map_pow, MulAut.conj_apply]
      have h3 : (g ^ (2 ^ k)) * z * (g ^ (2 ^ k))⁻¹ = z := h2.symm.trans (hinjS h1)
      calc z * g ^ 2 ^ k = g ^ 2 ^ k * z * (g ^ 2 ^ k)⁻¹ * g ^ 2 ^ k := by rw [h3]
        _ = g ^ 2 ^ k * z := by group
    rwa [hcenS, Subgroup.mem_bot] at hc
  have hg : g = 1 := by
    have hcop : Nat.Coprime (2 ^ k) (Fintype.card (GaloisField 2 f) - 1) := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
      refine Nat.Coprime.pow_left k ?_
      rw [Nat.coprime_two_left]
      exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hg2) hcop)
      (orderOf_dvd_of_pow_eq_one hgq))
  rw [← hrS, Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, rfl⟩
  have h1 := hβ z
  rw [hβg, hg, one_mul, inv_one, mul_one] at h1
  calc ψS z * t = t * ψS z * t⁻¹ * t := by rw [← h1]
    _ = t * ψS z := by group

section RowS2


theorem ggF4QGeFourKGCent_S2_unitaryTarget
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (hL : GGCentralImage .POmegaMinus 4 f L) (hK : GGCentralImage .PSU 6 f K)
    (hposL : GGTableBPosImage p Bs .POmegaMinus 4 f L) {t : G}
    (ht2 : ∃ m : ℕ, t ^ (2 ^ m) = 1) (htB : t ∈ Subgroup.centralizer (Bs : Set G))
    (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    t ∈ Subgroup.centralizer (K : Set G) := by
  have htN := F4KGPosition.centralizer_bstar_le_normalizer_K_unitary hcfg hf hpf hL hK htB
  obtain ⟨ψ, hadm, hker, hrange⟩ := hK
  have hloc := ggKGPosLocalHypTw_of_f4_member ggInnerDiagMpInput_holds hcfg (Or.inr rfl)
    hf hpf (by decide) ψ hadm hker hrange
  obtain ⟨ψ', -, hker', hrange', ε, hrefl, hlev, hcard, -, hcrit⟩ :=
    KGCentSU.exists_tableBPos_centCriterion_PSU hloc
  have hposK : GGTableBPos p Bs K .PSU 6 f ψ' := ⟨ε, hrefl, hlev, hcard⟩
  obtain ⟨w, k, hk, hfix⟩ := F4KGPosition.exists_shared_short_root_fixed_of_tableBPos
    hcfg e hpres hf hposL hker' hrange' hposK htL
  exact hcrit t ht2 htB htN w k hk hfix

theorem ggF4QGeFourKGCentInput_S2 (ha₀ : GGLNoncyclicInput) (hTBF : GGTBFixInput)
    (hFC : GGResNbrFixCentralizesInput) (hKG : GGF4QGeFourKGPosInput .S2)
    (hM : GGF4QGeFourRk2MissedInput .S2) : GGF4QGeFourKGCentInput .S2 := by
  intro G _ _ p B Bs x L D J y K hcfg hRC e hpres f hf hpf hrow X Y hXY t ht2 htB htX
  obtain ⟨hposL, hposK⟩ := hKG G p B Bs x L D J y K hcfg ⟨e, hpres.2⟩ f hf hpf hrow
  rcases hXY with ⟨hXL, hYK⟩ | ⟨hXK, hYL⟩
  · subst X
    subst Y
    rcases hposK with hposK | hposK
    · have hK : GGCentralImage .PSU 6 f K := by
        obtain ⟨ψ, hker, hrange, -⟩ := hposK
        exact ⟨ψ, ⟨Nat.prime_two, by omega, by norm_num, by simp⟩, hker, hrange⟩
      exact ggF4QGeFourKGCent_S2_unitaryTarget hcfg e hpres hf hpf hrow.1 hK hposL
        ht2 htB htX
    · exact ggF4QGeFourKGCent_S2_omegaMinusTarget ha₀ hTBF hFC hKG hM hcfg hRC e hpres
        hf hpf hrow (Or.inl ⟨rfl, rfl⟩) hposK ht2 htB htX
  · subst X
    subst Y
    exact ggF4QGeFourKGCent_S2_omegaMinusTarget ha₀ hTBF hFC hKG hM hcfg hRC e hpres
      hf hpf hrow (Or.inr ⟨rfl, rfl⟩) hposL ht2 htB htX

end RowS2

end CFSG.StandardType

end
