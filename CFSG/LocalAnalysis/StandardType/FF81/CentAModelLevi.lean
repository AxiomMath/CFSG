module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelBeta
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinInv
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinO2
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFieldNormalize
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.G11Stmts
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M24
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin

private theorem caLevi_orderOf_rhoTwo : orderOf rhoTwo = 3 := by
  have h3 : rhoTwo ^ 3 = 1 := by decide
  have hne : rhoTwo ≠ 1 := by decide
  have hdvd : orderOf rhoTwo ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

private theorem caLevi_pairGL_mem_suppGL {κ : Type*} [Fintype κ] [DecidableEq κ] {p q : κ}
    (hpq : p ≠ q) (M : GL (Fin 2) (ZMod 2)) :
    pairGL hpq M ∈ CFSG.SeitzReduction.SymplecticPilot.suppGL (ZMod 2) ({p, q} : Set κ) := by
  rw [CFSG.SeitzReduction.SymplecticPilot.mem_suppGL, coe_pairGL]
  intro a b hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hab
  rcases not_and_or.mp hab with h | h
  · have hap : a ≠ p := fun hp => h (Or.inl hp)
    have haq : a ≠ q := fun hq => h (Or.inr hq)
    rw [CFSG.LieType.Steinberg.Sp.blockMat]
    simp [Matrix.of_apply, hap, haq]
  · have hbp : b ≠ p := fun hp => h (Or.inl hp)
    have hbq : b ≠ q := fun hq => h (Or.inr hq)
    by_cases hap : a = p
    · subst hap
      rw [CFSG.LieType.Steinberg.Sp.blockMat]
      simp [Matrix.of_apply, hbp, hbq, Matrix.one_apply, Ne.symm hbp]
    · by_cases haq : a = q
      · subst haq
        rw [CFSG.LieType.Steinberg.Sp.blockMat]
        simp [Matrix.of_apply, hbp, hbq, Matrix.one_apply, Ne.symm hbq]
      · rw [CFSG.LieType.Steinberg.Sp.blockMat]
        simp [Matrix.of_apply, hap, haq]

theorem le_uSub_of_normal_centBStar {m : ℕ} (hm : 4 ≤ m)
    (D : Subgroup (GL (BlkIdx 1 m) (ZMod 2)))
    (hD : D ≤ Cent 1 m ⊓ Subgroup.centralizer {bStar m}) (hD2 : IsPGroup 2 D)
    (hn : ∀ g ∈ Cent 1 m ⊓ Subgroup.centralizer {bStar m}, ∀ d ∈ D, g * d * g⁻¹ ∈ D) :
    D ≤ uSub 1 m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hpq : (Fin.castSucc (Fin.last k) : Fin (k + 2)) ≠ Fin.last (k + 1) := by
    simp [Fin.ext_iff]
  set ρ' : GL (Fin (k + 2)) (ZMod 2) := pairGL hpq rhoTwo with hρ'def
  have hbStar : bStar (k + 2) = leviOne (k + 2) ρ' := by
    show leviOne (k + 2) (lastTwo (k + 2) rhoTwo) = leviOne (k + 2) ρ'
    rw [show lastTwo (k + 2) rhoTwo = ρ' from rfl]
  set S : Subgroup (GL (Fin (k + 2)) (ZMod 2)) :=
    CFSG.SeitzReduction.SymplecticPilot.suppGL (ZMod 2)
      {i : Fin (k + 2) | i ≠ Fin.castSucc (Fin.last k) ∧ i ≠ Fin.last (k + 1)} with hSdef
  set T : Subgroup (GL (Fin (k + 2)) (ZMod 2)) := Subgroup.zpowers ρ' with hTdef
  have hK : Subgroup.centralizer ({ρ'} : Set (GL (Fin (k + 2)) (ZMod 2))) = S ⊔ T := by
    rw [hρ'def, hSdef, hTdef]
    exact centralizer_pairGL (p := Fin.castSucc (Fin.last k)) (q := Fin.last (k + 1))
      hpq caLevi_orderOf_rhoTwo
  have hS_le_K : S ≤ Subgroup.centralizer ({ρ'} : Set (GL (Fin (k + 2)) (ZMod 2))) := by
    rw [hK]
    exact le_sup_left
  have hρ'notS : ρ' ∉ S := by
    rw [hρ'def, hSdef, CFSG.SeitzReduction.SymplecticPilot.mem_suppGL, coe_pairGL]
    intro h
    have h1 := h (Fin.castSucc (Fin.last k)) (Fin.last (k + 1)) (fun hc => hc.1.1 rfl)
    rw [CFSG.LieType.Steinberg.Sp.blockMat] at h1
    simp [Matrix.of_apply, Matrix.one_apply, Ne.symm hpq] at h1
    have h2 : (↑rhoTwo : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1 = 1 := by decide
    rw [h2] at h1
    exact one_ne_zero h1
  have hTcard : Nat.card T = 3 := by
    rw [hTdef, Nat.card_zpowers, hρ'def]
    exact (orderOf_injective (pairGL hpq) (pairGL_injective hpq) rhoTwo).trans
      caLevi_orderOf_rhoTwo
  have hST : S ⊓ T = ⊥ := by
    by_contra hne
    have hne1 : Nat.card ↥(S ⊓ T) ≠ 1 := by
      intro h1
      exact hne (Subgroup.card_eq_one.mp h1)
    have hdvd : Nat.card ↥(S ⊓ T) ∣ 3 := by
      rw [← hTcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hcard : Nat.card ↥(S ⊓ T) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hle : T ≤ S := by
      have h1 : S ⊓ T = T :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (hTcard.trans hcard.symm))
      rw [← h1]
      exact inf_le_left
    exact hρ'notS (hle (Subgroup.mem_zpowers ρ'))
  let Rmat : Cent 1 (k + 2) →* GL (Fin (k + 2)) (ZMod 2) :=
    (MonoidHom.snd (GL (Fin 1) (ZMod 2)) (GL (Fin (k + 2)) (ZMod 2))).comp
      (centBlockHom 1 (k + 2))
  have hRmat_levi : ∀ (R : GL (Fin (k + 2)) (ZMod 2))
      (hg : leviOne (k + 2) R ∈ Cent 1 (k + 2)), Rmat ⟨leviOne (k + 2) R, hg⟩ = R := by
    intro R hg
    show (centBlockHom 1 (k + 2) ⟨leviOne (k + 2) R, hg⟩).2 = R
    exact congrArg Prod.snd (centBlockHom_levi (r := 1) (m := k + 2) (P := 1) R)
  have hblockB_comm : ∀ g : Cent 1 (k + 2),
      g.1 ∈ Subgroup.centralizer {bStar (k + 2)} →
      Rmat g ∈ Subgroup.centralizer ({ρ'} : Set (GL (Fin (k + 2)) (ZMod 2))) := by
    intro g hg
    let g' : Cent 1 (k + 2) :=
      ⟨levi (r := 1) (m := k + 2) 1 ρ', levi_mem_cent 1 (k + 2) 1 ρ'⟩
    have hval : Rmat g' = ρ' := hRmat_levi ρ' _
    have hcomm : g.1 * g'.1 = g'.1 * g.1 := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hg
      rwa [hbStar] at h
    have hgg : (g * g' : Cent 1 (k + 2)) = g' * g := Subtype.ext hcomm
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc Rmat g * ρ' = Rmat g * Rmat g' := by rw [hval]
      _ = Rmat (g * g') := (map_mul _ g g').symm
      _ = Rmat (g' * g) := by rw [hgg]
      _ = Rmat g' * Rmat g := map_mul _ g' g
      _ = ρ' * Rmat g := by rw [hval]
  let Dcent : Subgroup (Cent 1 (k + 2)) := D.subgroupOf (Cent 1 (k + 2))
  let Dbar : Subgroup (GL (Fin (k + 2)) (ZMod 2)) := Dcent.map Rmat
  have hDbar2 : IsPGroup 2 Dbar := (hD2.comap_subtype).map Rmat
  have hDbar_le_K : Dbar ≤
      Subgroup.centralizer ({ρ'} : Set (GL (Fin (k + 2)) (ZMod 2))) := by
    rintro x ⟨g, hg, rfl⟩
    exact hblockB_comm g (hD hg).2
  have hDbar_normal : ∀ R' ∈ Subgroup.centralizer ({ρ'} : Set (GL (Fin (k + 2)) (ZMod 2))),
      ∀ x ∈ Dbar, R' * x * R'⁻¹ ∈ Dbar := by
    rintro R' hR' x ⟨g, hg, rfl⟩
    have hd : g.1 ∈ D := hg
    have hlevi : leviOne (k + 2) R' ∈
        Cent 1 (k + 2) ⊓ Subgroup.centralizer {bStar (k + 2)} := by
      refine ⟨levi_mem_cent 1 (k + 2) 1 R', ?_⟩
      change leviOne (k + 2) R' ∈ Subgroup.centralizer ({bStar (k + 2)} : Set _)
      rw [Subgroup.mem_centralizer_singleton_iff, hbStar, ← map_mul, ← map_mul]
      exact congrArg (leviOne (k + 2)) (Subgroup.mem_centralizer_singleton_iff.mp hR')
    let g' : Cent 1 (k + 2) := ⟨leviOne (k + 2) R', hlevi.1⟩
    have hval : Rmat g' = R' := hRmat_levi R' hlevi.1
    have hconj : (g' * g * g'⁻¹).1 ∈ D :=
      hn (leviOne (k + 2) R') hlevi (g.1) hd
    refine Subgroup.mem_map.mpr ⟨g' * g * g'⁻¹, hconj, ?_⟩
    rw [map_mul, map_mul, map_inv, hval]
  have hdisj : Disjoint
      {i : Fin (k + 2) | i ≠ Fin.castSucc (Fin.last k) ∧ i ≠ Fin.last (k + 1)}
      ({Fin.castSucc (Fin.last k), Fin.last (k + 1)} : Set (Fin (k + 2))) := by
    refine Set.disjoint_left.mpr (fun x hx hx' => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rcases hx' with rfl | rfl
    · exact hx.1 rfl
    · exact hx.2 rfl
  have ht_supp : ∀ t ∈ T, t ∈ CFSG.SeitzReduction.SymplecticPilot.suppGL (ZMod 2)
      ({Fin.castSucc (Fin.last k), Fin.last (k + 1)} : Set (Fin (k + 2))) := by
    intro t ht
    refine Subgroup.zpowers_le.mpr ?_ ht
    rw [hρ'def]
    exact caLevi_pairGL_mem_suppGL hpq rhoTwo
  have hcomm_ST : ∀ s ∈ S, ∀ t ∈ T, Commute s t := by
    intro s hs t ht
    rw [hSdef] at hs
    exact CFSG.SeitzReduction.OmegaPilot.commute_of_mem_suppGL_of_disjoint hdisj hs
      (ht_supp t ht)
  have hS_normT : S ≤ Subgroup.normalizer T := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs t ht
    rw [(hcomm_ST s hs t ht).eq, mul_assoc, mul_inv_cancel, mul_one]
    exact ht
  have hDbar_le_S : Dbar ≤ S := by
    intro x hx
    have hxK : x ∈ Subgroup.centralizer ({ρ'} : Set (GL (Fin (k + 2)) (ZMod 2))) :=
      hDbar_le_K hx
    rw [hK] at hxK
    have hxST : x ∈ (↑(S ⊔ T) : Set (GL (Fin (k + 2)) (ZMod 2))) := hxK
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S T hS_normT] at hxST
    obtain ⟨s, hs, t, ht, hst⟩ := hxST
    have hcomm : Commute s t := hcomm_ST s hs t ht
    obtain ⟨n, hn'⟩ := hDbar2 ⟨x, hx⟩
    have hn1 : x ^ 2 ^ n = 1 := by
      have h := congrArg Subtype.val hn'
      simpa using h
    have hn2 : t ^ 2 ^ n * s ^ 2 ^ n = 1 := by
      rw [← (hcomm.pow_pow (2 ^ n) (2 ^ n)).eq, ← hcomm.mul_pow]
      have hst' : s * t = x := hst
      rw [hst']
      exact hn1
    have ht2n : t ^ 2 ^ n = 1 := by
      have hmem : t ^ 2 ^ n ∈ S ⊓ T := by
        refine ⟨?_, Subgroup.pow_mem T ht _⟩
        have h1 : t ^ 2 ^ n = (s ^ 2 ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hn2
        rw [h1]
        exact Subgroup.inv_mem S (Subgroup.pow_mem S hs _)
      rw [hST] at hmem
      exact Subgroup.mem_bot.mp hmem
    have ht3 : t ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← hTcard]
      exact Subgroup.orderOf_dvd_natCard T ht
    have hgcd : (2 ^ n).gcd 3 = 1 := by
      have hdvd : (2 ^ n).gcd 3 ∣ 3 := Nat.gcd_dvd_right _ _
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact h
      · exfalso
        have h3 : 3 ∣ 2 ^ n := h ▸ Nat.gcd_dvd_left (2 ^ n) 3
        have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
        norm_num at h32
    have ht1 : t = 1 := by
      have h1 : t ^ (2 ^ n).gcd 3 = 1 := pow_gcd_eq_one.mpr ⟨ht2n, ht3⟩
      rwa [hgcd, pow_one] at h1
    rw [← hst, ht1]
    simpa using hs
  set e : Fin k → Fin (k + 2) := Fin.castAdd 2 with hedef
  have he : Function.Injective e := by
    rw [hedef]
    exact Fin.castAdd_injective k 2
  have hrange : Set.range e =
      {i : Fin (k + 2) | i ≠ Fin.castSucc (Fin.last k) ∧ i ≠ Fin.last (k + 1)} := by
    ext i
    constructor
    · rintro ⟨j, rfl⟩
      constructor
      · intro h
        have h2 := congrArg Fin.val h
        simp [hedef, Fin.castAdd, Fin.castSucc, Fin.last] at h2
        omega
      · intro h
        have h2 := congrArg Fin.val h
        simp [hedef, Fin.castAdd, Fin.last] at h2
        omega
    · rintro ⟨h1, h2⟩
      have hk : i.1 ≠ k := by
        intro h
        exact h1 (Fin.ext (by simpa [Fin.castSucc, Fin.last] using h))
      have hk1 : i.1 ≠ k + 1 := by
        intro h
        exact h2 (Fin.ext (by simpa [Fin.last] using h))
      refine ⟨⟨i.1, by omega⟩, ?_⟩
      ext
      simp [hedef, Fin.castAdd]
  have hS_range : S = CFSG.SeitzReduction.SymplecticPilot.suppGL (ZMod 2) (Set.range e) := by
    rw [hSdef, hrange]
  have hrange_eq : (CFSG.SeitzReduction.F4Pilot.coordEmbedGL e he).range =
      CFSG.SeitzReduction.SymplecticPilot.suppGL (ZMod 2) (Set.range e) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨g, rfl⟩
      exact CFSG.SeitzReduction.F4Pilot.coordEmbedGL_mem_suppGL he g
    · intro x hx
      obtain ⟨g, rfl⟩ :=
        CFSG.SeitzReduction.F4Pilot.exists_coordEmbedGL_eq_of_mem_suppGL he hx
      exact ⟨g, rfl⟩
  have hDbar_le_range : Dbar ≤ (CFSG.SeitzReduction.F4Pilot.coordEmbedGL e he).range := by
    rw [hrange_eq, ← hS_range]
    exact hDbar_le_S
  let Dk : Subgroup (GL (Fin k) (ZMod 2)) :=
    Dbar.comap (CFSG.SeitzReduction.F4Pilot.coordEmbedGL e he)
  have hDk2 : IsPGroup 2 Dk :=
    hDbar2.comap_of_injective _ (CFSG.SeitzReduction.F4Pilot.coordEmbedGL_injective he)
  have hDkn : Dk.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_comap] at hn ⊢
    have h1 : CFSG.SeitzReduction.F4Pilot.coordEmbedGL e he (g * n * g⁻¹) =
        CFSG.SeitzReduction.F4Pilot.coordEmbedGL e he g *
          CFSG.SeitzReduction.F4Pilot.coordEmbedGL e he n *
          (CFSG.SeitzReduction.F4Pilot.coordEmbedGL e he g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [h1]
    refine hDbar_normal _ ?_ _ hn
    exact hS_le_K (by
      rw [hS_range, ← hrange_eq]
      exact ⟨g, rfl⟩)
  have hDk_bot : Dk = ⊥ := eq_bot_of_isPGroup_of_normal k Dk hDk2
  have hDbar_bot : Dbar = ⊥ := by
    have h1 : Dk.map (CFSG.SeitzReduction.F4Pilot.coordEmbedGL e he) = Dbar :=
      Subgroup.map_comap_eq_self hDbar_le_range
    rw [← h1, hDk_bot, Subgroup.map_bot]
  intro d hd
  have hdCent : d ∈ Cent 1 (k + 2) := (hD hd).1
  have hmem : Rmat ⟨d, hdCent⟩ ∈ Dbar :=
    Subgroup.mem_map.mpr ⟨⟨d, hdCent⟩, hd, rfl⟩
  rw [hDbar_bot] at hmem
  have h1 : Rmat ⟨d, hdCent⟩ = 1 := Subgroup.mem_bot.mp hmem
  have hpair : centBlockHom 1 (k + 2) ⟨d, hdCent⟩ = 1 := by
    refine Prod.ext (glOne_eq_one _) ?_
    exact h1
  exact (centBlockHom_eq_one_iff 1 (k + 2) ⟨d, hdCent⟩).mp hpair

theorem exists_sl3_bStar {m : ℕ} (hm : 3 ≤ m) :
    ∃ P : Subgroup (GL (BlkIdx 1 m) (ZMod 2)), P ≤ leviB m ∧ bStar m ∈ P ∧
      Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have he : Function.Injective (Fin.natAdd k : Fin 3 → Fin (k + 3)) := Fin.natAdd_injective 3 k
  set f : GL (Fin 3) (ZMod 2) →* GL (BlkIdx 1 (k + 3)) (ZMod 2) :=
    (leviOne (k + 3)).comp (CFSG.SeitzReduction.F4Pilot.coordEmbedGL (Fin.natAdd k) he) with hf
  have hfinj : Function.Injective f := by
    intro x y h
    have h' : (leviOne (k + 3))
        (CFSG.SeitzReduction.F4Pilot.coordEmbedGL (Fin.natAdd k) he x) =
        (leviOne (k + 3))
          (CFSG.SeitzReduction.F4Pilot.coordEmbedGL (Fin.natAdd k) he y) := h
    exact CFSG.SeitzReduction.F4Pilot.coordEmbedGL_injective he
      (leviOne_injective (k + 3) h')
  refine ⟨f.range, ?hle, ?hmem, ?hiso⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨_, rfl⟩
  · have hsupp : (lastTwo (k + 3) rhoTwo : GL (Fin (k + 3)) (ZMod 2)) ∈
        CFSG.SeitzReduction.SymplecticPilot.suppGL (ZMod 2)
          (Set.range (Fin.natAdd k : Fin 3 → Fin (k + 3))) := by
      have h1 : (lastTwo (k + 3) rhoTwo : GL (Fin (k + 3)) (ZMod 2)) ∈
          CFSG.SeitzReduction.SymplecticPilot.suppGL (ZMod 2)
            ({Fin.castSucc (Fin.last (k + 1)), Fin.last (k + 2)} : Set (Fin (k + 3))) := by
        rw [show lastTwo (k + 3) rhoTwo = pairGL (p := Fin.castSucc (Fin.last (k + 1)))
          (q := Fin.last (k + 2)) (by simp [Fin.ext_iff]) rhoTwo from rfl]
        exact caLevi_pairGL_mem_suppGL (by simp [Fin.ext_iff]) rhoTwo
      refine CFSG.SeitzReduction.SymplecticPilot.suppGL_mono (fun x hx => ?_) h1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨1, by ext; simp [Fin.natAdd]⟩
      · exact ⟨2, by ext; simp [Fin.natAdd]⟩
    obtain ⟨g, hg⟩ :=
      CFSG.SeitzReduction.F4Pilot.exists_coordEmbedGL_eq_of_mem_suppGL he hsupp
    refine ⟨g, ?_⟩
    show leviOne (k + 3) (CFSG.SeitzReduction.F4Pilot.coordEmbedGL (Fin.natAdd k) he g) =
      bStar (k + 3)
    rw [hg, bStar]
  · have hbij : Function.Bijective f.rangeRestrict :=
      ⟨fun x y h => hfinj (congrArg Subtype.val h), MonoidHom.rangeRestrict_surjective f⟩
    refine ⟨(MulEquiv.ofBijective f.rangeRestrict hbij).symm.trans ?_⟩
    exact (MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL (toGL_bijective 3)).symm

end CFSG.StandardType.FF81.CentA

end
