module

public import CFSG.LocalAnalysis.StandardType.GGHalfJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfFusionOm8Data
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.StandardType.GGHalfJoinSLCard
import CFSG.HardMathSupport.Foote.E27.LieTwo.OrthModel
import CFSG.GH74.GLS.IVK.Proofs2.SylowCommute
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixSRoot
import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWHom
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWSmall
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalGraph
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace HalfFusOm8

open CFSG.RankThree.PartTwo.Sec4.RonanK429F (Om8)
open CFSG.RankThree.PartTwo.Sec4.RonanK429F.Om8
open CFSG.Open (StatedOmega StatedQuadMinus StatedClassicalModel StatedLieAdmissible)

private theorem commutator_map_conj {G : Type*} [Group G] {J : Subgroup G}
    (hJ : commutator ↥J = ⊤) (g : G) :
    commutator ↥(J.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  let e : ↥J ≃* ↥(J.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective J (MulAut.conj g).toMonoidHom (MulEquiv.injective _)
  have hmap : Subgroup.map e.toMonoidHom (commutator ↥J) =
      commutator ↥(J.map (MulAut.conj g).toMonoidHom) := by
    simp only [commutator]
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  rw [hJ, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hmap
  exact hmap.symm

private theorem conj_normalizer_mem {G : Type*} [Group G] {g n a : G} {T : Subgroup G}
    (hn : n ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ T : Subgroup G) : Set G))
    (hT : n * a * n⁻¹ ∈ T) (hne : n * a * n⁻¹ ≠ 1) :
    g * n * g⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers (g * a * g⁻¹) ⊔
        T.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ∧
      (g * n * g⁻¹) * (g * a * g⁻¹) * (g * n * g⁻¹)⁻¹ ∈
        T.map (MulAut.conj g).toMonoidHom ∧
      (g * n * g⁻¹) * (g * a * g⁻¹) * (g * n * g⁻¹)⁻¹ ≠ 1 := by
  have hmap : ((Subgroup.zpowers a ⊔ T : Subgroup G).map (MulAut.conj g).toMonoidHom) =
      (Subgroup.zpowers (g * a * g⁻¹) ⊔ T.map (MulAut.conj g).toMonoidHom :
        Subgroup G) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmap]
    exact Subgroup.le_normalizer_map (MulAut.conj g).toMonoidHom
      (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
  · have heq : (g * n * g⁻¹) * (g * a * g⁻¹) * (g * n * g⁻¹)⁻¹ =
        (MulAut.conj g) (n * a * n⁻¹) := by
      rw [MulAut.conj_apply]
      group
    rw [heq]
    exact Subgroup.mem_map.mpr ⟨n * a * n⁻¹, hT, rfl⟩
  · intro h
    apply hne
    have h' : g * (n * a * n⁻¹) * g⁻¹ = 1 := by
      calc g * (n * a * n⁻¹) * g⁻¹ =
          (g * n * g⁻¹) * (g * a * g⁻¹) * (g * n * g⁻¹)⁻¹ := by group
        _ = 1 := h
    calc n * a * n⁻¹ = g⁻¹ * (g * (n * a * n⁻¹) * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h']
      _ = 1 := by group

private theorem factorization_three_20160 : (20160 : ℕ).factorization 3 = 2 := by
  rw [show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem statedClassicalModel_of_hasLabel {X : Type} [Group X] (hX : GGHasLabel ⟨.twD, 4, 1⟩ X) :
    StatedClassicalModel X .POmegaMinus 4 2 1 := by
  obtain ⟨K, hF, hfin, hK, b, c, hbc, ⟨e⟩⟩ := hX
  refine ⟨by simp only [StatedLieAdmissible]; norm_num, K, hF, hfin, hK, b, c, hbc,
    ⟨e.trans (omegaMinusProjEquiv 4 b c)⟩⟩

theorem exists_om8Lift {G : Type} [Group G] {K' : Subgroup G} (hZ : Subgroup.center ↥K' = ⊥)
    (hlab : GGHasLabel ⟨.twD, 4, 1⟩ (↥K' ⧸ Subgroup.center ↥K')) :
    ∃ φ : Om8 →* G, Function.Injective φ ∧ φ.range = K' := by
  obtain ⟨e⟩ := CFSG.HardMathSupport.Foote.E27.nonempty_mulEquiv_omegaMinus
    (statedClassicalModel_of_hasLabel hlab)
  let ψ : (↥K' ⧸ Subgroup.center ↥K') ≃* ↥K' :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let φ : Om8 →* G := K'.subtype.comp (e.symm.trans ψ).toMonoidHom
  refine ⟨φ, ?_, ?_⟩
  · intro p q hpq
    exact (e.symm.trans ψ).injective (Subtype.ext hpq)
  · apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact ((e.symm.trans ψ) y).2
    · intro x hx
      obtain ⟨y, hy⟩ := (e.symm.trans ψ).surjective ⟨x, hx⟩
      exact ⟨y, by
        show K'.subtype ((e.symm.trans ψ) y) = x
        rw [hy]
        rfl⟩

theorem fusion_core {a : Om8} (ha : orderOf a = 3) {J T : Subgroup Om8} (hJ : commutator ↥J = ⊤)
    (hJa : J ≤ Subgroup.centralizer ({a} : Set Om8)) (h7 : 7 ∣ Nat.card ↥J) (hTJ : T ≤ J)
    (hTcard : Nat.card ↥T = 9) :
    ∃ n' : Om8, n' ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ T : Subgroup Om8) : Set Om8) ∧
      n' * a * n'⁻¹ ∈ T ∧ n' * a * n'⁻¹ ≠ 1 := by
  have hbc : ∀ s : GaloisField 2 1, s ^ 2 + 1 * s + 1 ≠ 0 := by
    intro s
    rcases CFSG.RankThree.PartTwo.Sec4.RonanK429F.gf2_eq_zero_or_one s with rfl | rfl
    · simp
    · rw [one_pow, one_mul,
        CFSG.RankThree.PartTwo.Sec4.RonanK429F.gf2_one_add_one, zero_add]
      exact one_ne_zero
  have hdvd : 7 ∣ Nat.card (Subgroup.centralizer ({a} : Set Om8)) :=
    h7.trans (Subgroup.card_dvd_of_le hJa)
  obtain ⟨x, hx⟩ :=
    CFSG.RankThree.PartTwo.Sec4.RonanK429F.exists_conj_commute_of_dvd
      (r := 7) (by norm_num) orderOf_y7 (not_sq_seven_dvd hbc) (s := a) hdvd
  let t : Om8 := x⁻¹ * a * x
  have htcomm : t * y7 = y7 * t := hx
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hconj : (MulAut.conj x⁻¹) a = x⁻¹ * a * x := by
    rw [MulAut.conj_apply, inv_inv]
  have ht3 : t ^ 3 = 1 := by
    show (x⁻¹ * a * x) ^ 3 = 1
    rw [← hconj, ← map_pow, ha3, map_one]
  have htne : t ≠ 1 := by
    intro h
    have ha1 : a = 1 := by
      calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
        _ = x * t * x⁻¹ := rfl
        _ = x * 1 * x⁻¹ := by rw [h]
        _ = 1 := by group
    have h1 : orderOf a = 1 := by rw [ha1, orderOf_one]
    rw [ha] at h1
    exact absurd h1 (by norm_num)
  have htf := t_form htcomm ht3 htne
  have hT : IsTForm t := isTForm_of htf
  let J₁ : Subgroup Om8 := J.map (MulAut.conj x⁻¹).toMonoidHom
  have hJ₁perf : commutator ↥J₁ = ⊤ := commutator_map_conj hJ x⁻¹
  have hJ₁a : J₁ ≤ Cen t := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    show (MulAut.conj x⁻¹).toMonoidHom j ∈ Subgroup.centralizer ({t} : Set Om8)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj2 : (MulAut.conj x⁻¹).toMonoidHom j = x⁻¹ * j * x := by
      change (MulAut.conj x⁻¹) j = x⁻¹ * j * x
      rw [MulAut.conj_apply, inv_inv]
    rw [hconj2]
    change (x⁻¹ * j * x) * (x⁻¹ * a * x) = (x⁻¹ * a * x) * (x⁻¹ * j * x)
    have hja : j * a = a * j := Subgroup.mem_centralizer_singleton_iff.mp (hJa hj)
    calc (x⁻¹ * j * x) * (x⁻¹ * a * x) = x⁻¹ * (j * a) * x := by group
      _ = x⁻¹ * (a * j) * x := by rw [hja]
      _ = (x⁻¹ * a * x) * (x⁻¹ * j * x) := by group
  have hJ₁D : J₁ ≤ psiD.range :=
    CFSG.RankThree.PartTwo.Sec4.RonanK429F.le_of_commutator_mem
      (C := Cen t) (D := psiD.range) (K := J₁)
      (fun p hp q hq => comm_mem_D hT hp hq) hJ₁a (Group.IsPerfect.mk hJ₁perf)
  let T₁ : Subgroup Om8 := T.map (MulAut.conj x⁻¹).toMonoidHom
  have hT₁J₁ : T₁ ≤ J₁ := Subgroup.map_mono hTJ
  have hT₁D : T₁ ≤ psiD.range := hT₁J₁.trans hJ₁D
  have hT₁card : Nat.card ↥T₁ = 9 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
      (MulEquiv.injective _), hTcard]
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hT0card' : Nat.card ↥T0 = 3 ^ (Nat.card ↥(psiD.range)).factorization 3 := by
    rw [card_T0, card_D, factorization_three_20160]
    norm_num
  have hT1card' : Nat.card ↥T₁ = 3 ^ (Nat.card ↥(psiD.range)).factorization 3 := by
    rw [hT₁card, card_D, factorization_three_20160]
    norm_num
  obtain ⟨d, hdD, hdconj⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.SylowCommute.exists_conj_of_card_eq
      (p := 3) (K := psiD.range) (T := T0) (X := T₁) T0_le_D hT₁D hT0card' hT1card'
  have hdt : d * t = t * d := by
    obtain ⟨P, hP⟩ := hdD
    rw [← hP]
    exact Subgroup.mem_centralizer_singleton_iff.mp (psiD_mem_cent hT P)
  have hT0map : T0.map (MulAut.conj d).toMonoidHom = T₁ := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, hsy⟩
      change d * s * d⁻¹ = y at hsy
      exact (hdconj y).mpr ⟨s, hs, hsy⟩
    · intro hy
      obtain ⟨s, hs, hsy⟩ := (hdconj y).mp hy
      exact ⟨s, hs, by
        change d * s * d⁻¹ = y
        exact hsy⟩
  have hdtd : d * t * d⁻¹ = t := by rw [hdt]; group
  obtain ⟨hn0norm, hn0T, hn0ne⟩ := n0_fusion htf
  obtain ⟨h1norm, h1mem, h1ne⟩ :=
    conj_normalizer_mem (g := d) (n := n0) (a := t) (T := T0) hn0norm hn0T hn0ne
  rw [hdtd] at h1norm h1mem h1ne
  rw [hT0map] at h1norm h1mem
  obtain ⟨h2norm, h2mem, h2ne⟩ :=
    conj_normalizer_mem (g := x) (n := d * n0 * d⁻¹) (a := t) (T := T₁) h1norm h1mem h1ne
  have hxt : x * t * x⁻¹ = a := by
    show x * (x⁻¹ * a * x) * x⁻¹ = a
    group
  have hT1map : T₁.map (MulAut.conj x).toMonoidHom = T := by
    show (T.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom = T
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom =
        MonoidHom.id Om8 := by
      apply MonoidHom.ext
      intro z
      show (MulAut.conj x) ((MulAut.conj x⁻¹) z) = z
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  rw [hxt] at h2norm h2mem h2ne
  rw [hT1map] at h2norm h2mem
  exact ⟨x * (d * n0 * d⁻¹) * x⁻¹, h2norm, h2mem, h2ne⟩

end HalfFusOm8

theorem ggHalfFusionOmega8Input_holds : GGHalfFusionOmega8Input := by
  show GGHalfFusionAt ⟨.twD, 4, 1⟩ 3
  intro G _ _ K' J T kx hq hZ hlabK hkx hkxK hJc hZJ hlabJ hTJ hT hTcard
  obtain ⟨φ, hφi, hφr⟩ := HalfFusOm8.exists_om8Lift hZ hlabK
  rw [← hφr, MonoidHom.range_eq_map] at hkxK
  obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hkxK
  have ha : orderOf a = 3 := (orderOf_injective φ hφi a).symm.trans hkx
  have hJK' : J ≤ K' := fun x hx => (hJc.1 hx).1
  have hJrange : J ≤ φ.range := by rw [hφr]; exact hJK'
  have hmapJ : (J.comap φ).map φ = J := Subgroup.map_comap_eq_self hJrange
  let e : ↥(J.comap φ) ≃* ↥J :=
    (Subgroup.equivMapOfInjective (J.comap φ) φ hφi).trans (MulEquiv.subgroupCongr hmapJ)
  have hq₀ : CFSG.Assembly.IsQuasisimple ↥(J.comap φ) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e hJc.2.2
  have hJ₀a : J.comap φ ≤ Subgroup.centralizer ({a} : Set _) := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hφx : φ x * φ a = φ a * φ x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hJc.1 hx).2
    apply hφi
    rw [map_mul, map_mul]
    exact hφx
  have hF2card : Nat.card GGHalf.F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  have hcardJ : Nat.card ↥J = Nat.card (Matrix.SpecialLinearGroup (Fin (3 + 1)) GGHalf.F2) :=
    GGHalfJoin.card_eq_of_hasLabel_typeA (m := 3) (by norm_num) hZJ hlabJ
  have hcard : Nat.card ↥(J.comap φ) = 20160 := by
    rw [Nat.card_congr e.toEquiv, hcardJ]
    exact CFSG.SeitzReduction.LinearPilot.card_specialLinearGroup_fin_four_eq_sixS
      (K := GGHalf.F2) hF2card
  have h7 : 7 ∣ Nat.card ↥(J.comap φ) := by rw [hcard]; norm_num
  have hTrange : T ≤ φ.range := by rw [hφr]; exact hTJ.trans hJK'
  have hTmap : (T.comap φ).map φ = T := Subgroup.map_comap_eq_self hTrange
  have hcardT : Nat.card ↥(T.comap φ) = Nat.card ↥T := by
    have h1 : Nat.card ↥(T.comap φ) = Nat.card ↥((T.comap φ).map φ) :=
      (Subgroup.card_map_of_injective (f := φ) hφi).symm
    rw [hTmap] at h1
    exact h1
  have hT₀card : Nat.card ↥(T.comap φ) = 9 := by
    rw [hcardT, hTcard]
    norm_num
  have hT₀J₀ : T.comap φ ≤ J.comap φ := Subgroup.comap_mono hTJ
  obtain ⟨n₀, hn₀norm, hn₀T, hn₀ne⟩ :=
    HalfFusOm8.fusion_core (a := a) ha hq₀.1 hJ₀a h7 hT₀J₀ hT₀card
  refine ⟨φ n₀, ?_, ?_, ?_, ?_⟩
  · rw [← hφr, MonoidHom.range_eq_map]
    exact Subgroup.mem_map.mpr ⟨n₀, Subgroup.mem_top n₀, rfl⟩
  · have hmap : ((Subgroup.zpowers a ⊔ T.comap φ).map φ) =
        Subgroup.zpowers (φ a) ⊔ T := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, hTmap]
    have hmem : φ n₀ ∈ Subgroup.normalizer
        (((Subgroup.zpowers a ⊔ T.comap φ).map φ) : Set G) :=
      Subgroup.le_normalizer_map φ (Subgroup.mem_map.mpr ⟨n₀, hn₀norm, rfl⟩)
    rwa [hmap] at hmem
  · have hmemT : φ (n₀ * a * n₀⁻¹) ∈ T := by
      rw [← hTmap]
      exact Subgroup.mem_map.mpr ⟨n₀ * a * n₀⁻¹, hn₀T, rfl⟩
    simpa only [map_mul, map_inv] using hmemT
  · intro h
    apply hn₀ne
    apply hφi
    simpa only [map_mul, map_inv, map_one] using h

end CFSG.StandardType

end
