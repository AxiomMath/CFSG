module

public import CFSG.RankThree.PartTwo.Sec14.Item148PointProof142
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCoreDefs
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCore
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofInndiag
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
public import CFSG.RankThree.PartTwo.Sec14.Item148StepKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec14.Proof142Res
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped commutatorElement

namespace Item148PtRes2

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_sec14 (hspor : SporadicModels131) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
  obtain ⟨⟨-, hM22z⟩, ⟨-, hM12z⟩, ⟨-, hJ2z⟩⟩ := hspor
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.toSec13Data.mem_thetaComponentsAt
  rcases (h.chosen136.2 c h.toSec13Data.zpowers_mem_omegaA L h.toSec13Data.mem_lA).1 with
    ⟨⟨φ⟩⟩ | hL3 | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact center_eq_bot_of_mulEquiv148 φ hJ2z
  · exact kf148CenterL3 _ hq.1 (Or.inl hL3)
  · exact center_eq_bot_of_mulEquiv148 φ
      (alternatingGroup.center_eq_bot
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num))
  · exact center_eq_bot_of_mulEquiv148 φ hM22z
  · exact center_eq_bot_of_mulEquiv148 φ hM12z

theorem eq_zpowers_sup_of_card {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) (hcL : c ∉ L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hD.mem_A
  have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A := sup_le hcA inf_le_left
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
    hD.commute (hcA hx) hy.1
  have hdisj : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
    rw [eq_bot_iff, ← Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hD.orderOf_eq hcL]
    exact fun x hx => ⟨hx.2.2, hx.1⟩
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hD.orderOf_eq, h9] at hcard
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hA.2])).symm

theorem exists_inndiag_model {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A)) (hxA' : ∃ x ∈ A, InducesTypeOn L x 3) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), PiField π p f K ∧ ModThree π (p ^ f) ∧
      2 < p ^ f ∧ ∃ ψ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projImage (slPi π 3 (p ^ f) K),
        ∀ (a : G) (ha : a ∈ Subgroup.normalizer (L : Set G)), a ∈ A →
          MulAut.congr ψ (thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, ha⟩)) ∈
            inndiagPi π (p ^ f) K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hA := hD.isElemAbelian
  have h27 := hD.card_eq
  have hcA := hD.mem_A
  have hAN := hD.le_normalizer
  have hLc := hD.le_centralizer
  have hLθ := hD.mem_thetaComponentsAt
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hD.commute ha hb
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAN hcA
  obtain ⟨d, hdAL, hd1, -⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
    (Sec16.Proof1614Trans.card_inf_eq_three_of_pgl hD hPGL)
  have hdA : d ∈ A := hdAL.1
  have hdL : d ∈ L := hdAL.2
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  have hZL := (Sec13.facts_of_isZ3PGLThreePi hD hPGL).2.1
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot hD hZL
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL (Subgroup.zpowers_le.mpr hdL h)
  have h9 := card_zpowers_sup_zpowers_eq_nine hA h27 hcA hdA hd1 hcd
  obtain ⟨x, hxA, hx⟩ := hxA'
  have hxcd := not_mem_sup_of_inducesTypeOn_three hLθ hLc hcN (hcomm c hcA d hdA) hdL hx
  have hcdA : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA)
  have hAeq := sup_zpowers_eq_of_card h27 hcdA h9 hxA hxcd
  obtain ⟨hxN, π, p, f, K, _, hK, hq, ψ, y, hyH, -, hact⟩ := hx
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hqs := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLθ
  have hLp : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hqs.1
  have : IsSimpleGroup ((L ⧸ aschbacherSolvableCore 3 L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := hqs.2.1
  have hLnt : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) :=
    (QuotientGroup.mk_surjective
      (s := Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))).nontrivial
  have hq2 : 2 < p ^ f := by
    by_contra h2
    have hp := hK.prime
    have hf := hK.one_le
    have h2' : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    cases π
    · have := Sec13.isSolvable_projImage_slPi_two hK h2'
      have : Group.IsSolvable (L ⧸ aschbacherSolvableCore 3 L) :=
        Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
      exact Group.IsPerfect.not_isSolvable _ this
    · change p ^ f % 3 = 1 at hq
      omega
  refine ⟨π, p, f, K, inferInstance, hK, hq, hq2, ψ, ?_⟩
  set ρ : Subgroup.normalizer (L : Set G) →* MulAut (projImage (slPi π 3 (p ^ f) K)) :=
    (MulAut.congr ψ).toMonoidHom.comp ((thetaQuotMulAut L).comp L.normalizerMonoidHom) with hρdef
  have hρ : ∀ (g : Subgroup.normalizer (L : Set G)) (s : projImage (slPi π 3 (p ^ f) K)),
      ρ g s = ψ (thetaQuotMulAut L (L.normalizerMonoidHom g) (ψ.symm s)) := fun g s => rfl
  set S : Subgroup G := ((inndiagPi π (p ^ f) K).comap ρ).map
    (Subgroup.normalizer (L : Set G)).subtype with hS
  have hmemS : ∀ g : G, g ∈ S ↔ ∃ hg : g ∈ Subgroup.normalizer (L : Set G),
      ρ ⟨g, hg⟩ ∈ inndiagPi π (p ^ f) K := by
    intro g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g'.2, hg'⟩
    · rintro ⟨hg, hgI⟩
      exact ⟨⟨g, hg⟩, hgI, rfl⟩
  have hσc := thetaQuotMulAut_eq_one_of_commute hcN (fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLc hl))
  have hcS : c ∈ S := (hmemS c).mpr ⟨hcN, by
    have : ρ ⟨c, hcN⟩ = 1 := by
      change MulAut.congr ψ (thetaQuotMulAut L (L.normalizerMonoidHom ⟨c, hcN⟩)) = 1
      rw [hσc, map_one]
    rw [this]
    exact one_mem _⟩
  set db : L ⧸ aschbacherSolvableCore 3 L := QuotientGroup.mk' _ (⟨d, hdL⟩ : L) with hdb
  obtain ⟨sd, hsd, hsde⟩ := Subgroup.mem_map.mp (ψ db).2
  have hρd : ρ ⟨d, hdN⟩ = MulAut.conj (ψ db) := by
    ext s
    rw [hρ, thetaQuotMulAut_of_mem hdL, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply, MulAut.conj_apply]
  have hdS : d ∈ S := (hmemS d).mpr ⟨hdN, ⟨sd, slPi_le_glPi hπ hsd, fun s => by
    rw [hρd, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hsde]⟩⟩
  have hxS : x ∈ S := (hmemS x).mpr ⟨hxN, ⟨y, hyH, fun s => by
    rw [hρ, hact, MulEquiv.apply_symm_apply]⟩⟩
  have hAS : A ≤ S := by
    rw [← hAeq]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr hcS) (Subgroup.zpowers_le.mpr hdS))
      (Subgroup.zpowers_le.mpr hxS)
  intro a ha haA
  obtain ⟨ha', haI⟩ := (hmemS a).mp (hAS haA)
  exact haI

omit [Finite G] in
theorem le_normalizer_of_conj_mem {H M : Subgroup G}
    (h : ∀ g ∈ H, ∀ m ∈ M, g * m * g⁻¹ ∈ M) : H ≤ Subgroup.normalizer (M : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨h g hg m, fun hm => ?_⟩
  have h1 := h g⁻¹ (inv_mem hg) _ hm
  have e : g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m := by group
  rwa [e] at h1

omit [Finite G] in
theorem pPrimeCoreOf_centralizer_le [Finite G] (c : G) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)) ≤
      pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_pPrimeCoreOf ((pPrimeCoreOf_le 3 _).trans
    (centralizer_singleton_le_normalizer_zpowers c)) ?_ (coprime_card_pPrimeCoreOf 3 _)
  refine le_trans ?_ (normalizer_le_normalizer_pPrimeCoreOf 3 _)
  have := CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup (Subgroup.zpowers c)
  rwa [centralizer_zpowers148] at this

theorem commutator_le_of_inndiag (hKer : Step142PGLKer) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A))
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (ψ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projImage (slPi π 3 (p ^ f) K))
    (hAI : ∀ (a : G) (ha : a ∈ Subgroup.normalizer (L : Set G)), a ∈ A →
      MulAut.congr ψ (thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, ha⟩)) ∈
        inndiagPi π (p ^ f) K)
    {V : Subgroup G} (hVc : V ≤ Subgroup.centralizer ({c} : Set G)) (hV3 : ¬ 3 ∣ Nat.card V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    ⁅V, A⁆ ≤ L ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hAN := hD.le_normalizer
  have hLc := hD.le_centralizer
  have hLθ := hD.mem_thetaComponentsAt
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := hD.A_le_centralizer
  have := hK.finite
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hCcN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h h3L
  set Z := ⁅V, A⁆ with hZ
  have hZV : Z ≤ V := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing V A hAV
  have hZ3 : ¬ 3 ∣ Nat.card Z := fun h3 => hV3 (h3.trans (Subgroup.card_dvd_of_le hZV))
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A V hAV
  have hZc : Z ≤ Subgroup.centralizer ({c} : Set G) := hZV.trans hVc
  have hZN : Z ≤ Subgroup.normalizer (L : Set G) := hZc.trans hCcN
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := hVc.trans hCcN
  set ρ : Subgroup.normalizer (L : Set G) →* MulAut (projImage (slPi π 3 (p ^ f) K)) :=
    (MulAut.congr ψ).toMonoidHom.comp ((thetaQuotMulAut L).comp L.normalizerMonoidHom) with hρdef
  have hρ : ∀ (g : Subgroup.normalizer (L : Set G)) (s : projImage (slPi π 3 (p ^ f) K)),
      ρ g s = ψ (thetaQuotMulAut L (L.normalizerMonoidHom g) (ψ.symm s)) := fun g s => rfl
  have hNorm := ks142InndiagNormal π p f K hK hq hq2
  have hqs := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLθ
  have hLp : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hqs.1
  have hPp : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hZP : Subgroup.center (projImage (slPi π 3 (p ^ f) K)) = ⊥ := center_projImage_eq_bot hK hq
  have hinj : Function.Injective
      (MulAut.conj : projImage (slPi π 3 (p ^ f) K) →*
        MulAut (projImage (slPi π 3 (p ^ f) K))) := by
    intro a b hab
    have h1 : b⁻¹ * a ∈ Subgroup.center (projImage (slPi π 3 (p ^ f) K)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut (projImage (slPi π 3 (p ^ f) K)) => φ g) hab
      simp only [MulAut.conj_apply] at this
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [this]
        _ = b⁻¹ * a * g := by group
    rw [hZP, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  set S : Subgroup G := ((inndiagPi π (p ^ f) K).comap ρ).map
    (Subgroup.normalizer (L : Set G)).subtype with hS
  have hmemS : ∀ g : G, g ∈ S ↔ ∃ hg : g ∈ Subgroup.normalizer (L : Set G),
      ρ ⟨g, hg⟩ ∈ inndiagPi π (p ^ f) K := by
    intro g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g'.2, hg'⟩
    · rintro ⟨hg, hgI⟩
      exact ⟨⟨g, hg⟩, hgI, rfl⟩
  have hZS : Z ≤ S := by
    rw [hZ, Subgroup.commutator_le]
    intro v hv a ha
    have hvN := hVN hv
    have haN := hAN ha
    have haI : ρ ⟨a, haN⟩ ∈ inndiagPi π (p ^ f) K := hAI a haN ha
    have hm : ⁅v, a⁆ ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (mul_mem (mul_mem hvN haN) (inv_mem hvN)) (inv_mem haN)
    refine (hmemS _).mpr ⟨hm, ?_⟩
    have e : (⟨⁅v, a⁆, hm⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨v, hvN⟩ * ⟨a, haN⟩ * (⟨v, hvN⟩ : Subgroup.normalizer (L : Set G))⁻¹ *
          (⟨a, haN⟩ : Subgroup.normalizer (L : Set G))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact mul_mem (hNorm.conj_mem _ haI _) (inv_mem haI)
  have hinner : ∀ z (hz : z ∈ Z), ∃ u : projImage (slPi π 3 (p ^ f) K),
      ρ ⟨z, hZN hz⟩ = MulAut.conj u := by
    intro z hz
    obtain ⟨hzN', hzI⟩ := (hmemS z).mp (hZS hz)
    refine exists_eq_conj_of_mem_inndiagPi hK hzI ?_
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hZ3 ?_
    refine h3.trans ((orderOf_map_dvd ρ _).trans ?_)
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard Z hz
  set U : Subgroup (projImage (slPi π 3 (p ^ f) K)) :=
    ((Z.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ).comap MulAut.conj with hU
  have hU3 : ¬ 3 ∣ Nat.card U := by
    intro h3
    apply hZ3
    have h1 : Nat.card (U.map MulAut.conj) = Nat.card U := Subgroup.card_map_of_injective hinj
    have h2 : U.map MulAut.conj ≤ (Z.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ :=
      Subgroup.map_comap_le _ _
    have h4 : Nat.card (Z.subgroupOf (Subgroup.normalizer (L : Set G))) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv
    rw [← h1] at h3
    exact h4 ▸ (h3.trans (Subgroup.card_dvd_of_le h2)).trans (Subgroup.card_map_dvd _ _)
  have hρU : ∀ (g : Subgroup.normalizer (L : Set G)),
      (g : G) ∈ Subgroup.normalizer (Z : Set G) → ∀ u ∈ U, ρ g u ∈ U := by
    intro g hgZ u hu
    obtain ⟨n, hn, hnu⟩ := hu
    have hn' : ((g * n * g⁻¹ : Subgroup.normalizer (L : Set G)) : G) ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp hgZ n).mp (Subgroup.mem_subgroupOf.mp hn)
    refine ⟨g * n * g⁻¹, Subgroup.mem_subgroupOf.mpr hn', ?_⟩
    change ρ (g * n * g⁻¹) = MulAut.conj (ρ g u)
    rw [map_mul, map_mul, map_inv, hnu]
    ext s
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set M₀ : Subgroup ↥L := (U.comap ψ.toMonoidHom).comap (QuotientGroup.mk' θ) with hM₀
  set M : Subgroup G := M₀.map L.subtype with hM
  have hW3 : ¬ 3 ∣ Nat.card (U.comap ψ.toMonoidHom) := by
    refine not_three_dvd_card_comap ψ.toMonoidHom hU3 ?_
    rw [(MonoidHom.ker_eq_bot_iff _).mpr ψ.injective, Subgroup.card_bot]
    norm_num
  have hM3 : ¬ 3 ∣ Nat.card M := by
    rw [hM, Subgroup.card_map_of_injective L.subtype_injective]
    exact not_three_dvd_card_comap _ hW3 (by rw [QuotientGroup.ker_mk']; exact hθ3)
  have hmemM : ∀ l : ↥L, (l : G) ∈ M ↔ ψ (QuotientGroup.mk' θ l) ∈ U := by
    intro l
    constructor
    · rintro ⟨l', hl', hll'⟩
      have : l' = l := Subtype.ext hll'
      rw [← this]
      exact hl'
    · intro hl
      exact ⟨l, hl, rfl⟩
  have hconjM : ∀ (g : G) (hgL : g ∈ Subgroup.normalizer (L : Set G)),
      g ∈ Subgroup.normalizer (Z : Set G) → ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    intro g hgL hgZ m hm
    obtain ⟨l, hl, rfl⟩ := hm
    have hl' : g * (l : G) * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hgL l).mp l.2
    refine (hmemM ⟨_, hl'⟩).mpr ?_
    have e : QuotientGroup.mk' θ ⟨_, hl'⟩ =
        thetaQuotMulAut L (L.normalizerMonoidHom ⟨g, hgL⟩) (QuotientGroup.mk' θ l) := rfl
    rw [e]
    have h1 := hρU ⟨g, hgL⟩ hgZ _ hl
    simp only [hρ, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h1
    exact h1
  have hAM : A ≤ Subgroup.normalizer (M : Set G) :=
    le_normalizer_of_conj_mem fun a ha => hconjM a (hAN ha) (hAZ ha)
  have hZM : Z ≤ Subgroup.normalizer (M : Set G) :=
    le_normalizer_of_conj_mem fun z hz => hconjM z (hZN hz) (Subgroup.le_normalizer hz)
  set K₀ := Subgroup.centralizer ({c} : Set G) ⊓ thetaQuotCentralizer L with hK₀
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)) with hO
  set D := (Z ⊔ M) ⊓ K₀ with hDdef
  have hD3 : ¬ 3 ∣ Nat.card D := by
    intro h3
    have h1 : 3 ∣ Nat.card (Z ⊔ M : Subgroup G) := h3.trans (Subgroup.card_dvd_of_le inf_le_left)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h1.trans (card_sup_dvd_card_mul hZM)) with
      h4 | h4
    · exact hZ3 h4
    · exact hM3 h4
  have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
    Late.le_normalizer_inf (le_normalizer_sup_of hAZ hAM)
      (Late.le_normalizer_inf (hAc.trans Subgroup.le_normalizer)
        (hAN.trans (normalizer_le_normalizer_thetaQuotCentralizer L)))
  have hDO : D ≤ O := hKer G A c L h hPGL D (inf_le_right.trans le_sup_left) hD3 hAD
  intro z hz
  obtain ⟨u, hzu⟩ := hinner z hz
  have huU : u ∈ U := ⟨⟨z, hZN hz⟩, Subgroup.mem_subgroupOf.mpr hz, hzu⟩
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective θ (ψ.symm u)
  have hwM : (w : G) ∈ M := (hmemM w).mpr (by rw [hw, MulEquiv.apply_symm_apply]; exact huU)
  set k := (w : G)⁻¹ * z with hk
  have hwN : (w : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer w.2
  have hkN : k ∈ Subgroup.normalizer (L : Set G) := mul_mem (inv_mem hwN) (hZN hz)
  have hσw : thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) = MulAut.conj (ψ.symm u) := by
    have := thetaQuotMulAut_of_mem (L := L) w.2
    rw [this, ← hw]
  have hσz : thetaQuotMulAut L (L.normalizerMonoidHom ⟨z, hZN hz⟩) = MulAut.conj (ψ.symm u) := by
    ext v
    apply ψ.injective
    have h1 := congrArg (fun φ : MulAut (projImage (slPi π 3 (p ^ f) K)) => φ (ψ v)) hzu
    simp only [hρ, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hkθ : k ∈ thetaQuotCentralizer L := by
    refine mem_thetaQuotCentralizer_iff'.mpr ⟨hkN, ?_⟩
    have e : (⟨k, hkN⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨w, hwN⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨z, hZN hz⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, map_inv, hσw, hσz, inv_mul_cancel]
  have hkc : k ∈ Subgroup.centralizer ({c} : Set G) :=
    mul_mem (inv_mem (hLc w.2)) (hZc hz)
  have hkD : k ∈ D :=
    ⟨mul_mem (Subgroup.mem_sup_right (inv_mem hwM)) (Subgroup.mem_sup_left hz), hkc, hkθ⟩
  have hzwk : z = (w : G) * k := by rw [hk, mul_inv_cancel_left]
  rw [hzwk]
  exact mul_mem (Subgroup.mem_sup_left w.2) (Subgroup.mem_sup_right (hDO hkD))

end Item148PtRes2

open Item148PtRes2 in
theorem step142UpperPGLS14_of (h131 : Item131) (hspor : SporadicModels131)
    (hKer : Step142PGLKer) : Step142UpperPGLS14 := by
  intro G _ _ A c L h hAc Q _
  refine Or.inr fun V hV => ?_
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hcA := hD.mem_A
  have hZ := center_eq_bot_of_sec14 hspor h
  obtain ⟨hPGL, hx⟩ : Sec8.IsZ3PGLThreePi (lBarA c L A) ∧ ∃ x ∈ A, InducesTypeOn L x 3 := by
    rcases cases131 h131 hspor slTwoCenter hD with ⟨hcL, h9, -⟩ | ⟨hcL, h9, -⟩ |
        ⟨-, hPGL, -, hx⟩ | ⟨hcL, -⟩
    · exact absurd (eq_zpowers_sup_of_card hD hcL h9) hAc
    · exact absurd (eq_zpowers_sup_of_card hD hcL h9) hAc
    · exact ⟨hPGL, hx⟩
    · exact absurd hcL (not_mem_of_center_eq_bot hD hZ)
  obtain ⟨π, p, f, K, _, hK, hq, hq2, ψ, hAI⟩ := exists_inndiag_model h hPGL hx
  have hVc := le_centralizer_of_mem_invariantPiSubgroups hcA hD.orderOf_eq hV
  have hV3 : ¬ 3 ∣ Nat.card V := (isPiSubgroup_piCompl_iff Nat.prime_three V).mp hV.2.1
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hD.isElemAbelian.2 a a.2)⟩
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
    Nat.prime_three A V hA3 hV3 hV.2.2]
  refine sup_le ?_ ((inf_centralizer_le_xA (Sec14Std.maximal_isElemAbelian h) hV3).trans
    le_sup_right)
  refine (commutator_le_of_inndiag hKer h hPGL hK hq hq2 ψ hAI hVc hV3 hV.2.2).trans ?_
  exact sup_le (le_sup_left.trans le_sup_left)
    ((pPrimeCoreOf_centralizer_le c).trans (le_sup_right.trans le_sup_left))

end CFSG.RankThree.PartTwo.Sec14
