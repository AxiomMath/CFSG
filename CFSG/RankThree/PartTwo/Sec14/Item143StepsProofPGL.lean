module

public import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def thetaFix (L : Subgroup G) {e : G}
    (he : e ∈ Subgroup.normalizer (L : Set G)) :
    Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  ((Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, he⟩)).toMonoidHom).eqLocus
    (MonoidHom.id _)

theorem mem_thetaFix_iff {L : Subgroup G} {e : G} (he : e ∈ Subgroup.normalizer (L : Set G))
    {z : ↥L ⧸ aschbacherSolvableCore 3 ↥L} :
    z ∈ thetaFix L he ↔ Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, he⟩) z = z :=
  Iff.rfl

theorem mem_thetaFix_of_mem_centralizer {L : Subgroup G} {e : G}
    (he : e ∈ Subgroup.normalizer (L : Set G)) {g : ↥L}
    (hg : (g : G) ∈ Subgroup.centralizer ({e} : Set G)) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) g ∈ thetaFix L he := by
  rw [mem_thetaFix_iff, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
  congr 1
  apply Subtype.ext
  change e * (g : G) * e⁻¹ = g
  rw [← Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]

theorem le_pPrimeCoreOf_of_signalFix {L : Subgroup G} {e : G}
    (he : e ∈ Subgroup.normalizer (L : Set G))
    {W : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)} (hW3 : ¬ 3 ∣ Nat.card W)
    (hWN : thetaFix L he ≤ Subgroup.normalizer (W : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    {B : Subgroup G}
    (hBC : L ⊓ Subgroup.centralizer ({e} : Set G) ≤ Subgroup.centralizer (B : Set G))
    (hCB : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) : Set G))
    {Z : Subgroup G} (hZ : Z ≤ L ⊓ Subgroup.centralizer ({e} : Set G))
    (hZW : (Z.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤ W) :
    Z ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set π := QuotientGroup.mk' θ with hπ
  set CL := (Subgroup.centralizer ({e} : Set G)).subgroupOf L with hCL
  set R := ((W.comap π) ⊓ CL).map L.subtype with hR
  have hZL : Z ≤ L := hZ.trans inf_le_left
  have hZR : Z ≤ R := by
    intro z hz
    have hzL := hZL hz
    have hzC : (⟨z, hzL⟩ : ↥L) ∈ CL := Subgroup.mem_subgroupOf.mpr (hZ hz).2
    exact ⟨⟨z, hzL⟩, ⟨hZW ⟨⟨z, hzL⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩, hzC⟩, rfl⟩
  have hRle : R ≤ L ⊓ Subgroup.centralizer ({e} : Set G) := by
    rw [inf_comm, ← Subgroup.subgroupOf_map_subtype]
    exact Subgroup.map_mono inf_le_right
  have hR3 : ¬ 3 ∣ Nat.card R := by
    rw [hR, Subgroup.card_map_of_injective L.subtype_injective]
    intro h3
    have hker : ¬ 3 ∣ Nat.card π.ker := by
      rw [hπ, QuotientGroup.ker_mk']
      exact hθ3
    exact not_three_dvd_card_comap π hW3 hker (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hRn : L ⊓ Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    have hgL : g ∈ L := hg.1
    set g' : ↥L := ⟨g, hgL⟩
    have hg'C : g' ∈ CL := Subgroup.mem_subgroupOf.mpr hg.2
    have hπg : π g' ∈ Subgroup.normalizer (W : Set (↥L ⧸ θ)) :=
      hWN (mem_thetaFix_of_mem_centralizer he hg.2)
    have hg'N : g' ∈ Subgroup.normalizer (((W.comap π) ⊓ CL : Subgroup ↥L) : Set ↥L) :=
      Late.le_normalizer_inf (A := Subgroup.zpowers g')
        (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer_comap π hπg))
        (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hg'C)) (Subgroup.mem_zpowers g')
    exact Subgroup.le_normalizer_map L.subtype ⟨g', hg'N, rfl⟩
  have hRO : R ≤ pPrimeCoreOf 3 (L ⊓ Subgroup.centralizer ({e} : Set G)) :=
    le_pPrimeCoreOf hRle hRn ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR3)
  have hOO : pPrimeCoreOf 3 (L ⊓ Subgroup.centralizer ({e} : Set G)) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
    le_pPrimeCoreOf ((pPrimeCoreOf_le 3 _).trans hBC)
      (hCB.trans (normalizer_le_normalizer_pPrimeCoreOf 3 _)) (coprime_card_pPrimeCoreOf 3 _)
  exact hZR.trans (hRO.trans hOO)

theorem commutator_le_of_eq_sup_inf {A B L Y : Subgroup G} (hAB : A = B ⊔ (A ⊓ L))
    (hBA : B ≤ A) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hYB : Y ≤ Subgroup.centralizer (B : Set G))
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) : ⁅Y, A⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro y hy α hα
  have hcomm : ∀ x ∈ B, ∀ z ∈ A ⊓ L, x * z = z * x := fun x hx z hz => hAab x (hBA hx) z hz.1
  have hα' : α ∈ ((B ⊔ (A ⊓ L) : Subgroup G) : Set G) := by rw [← hAB]; exact hα
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [hset] at hα'
  obtain ⟨β, hβ, l, hl, rfl⟩ := hα'
  have hyβ : y * β = β * y := (Subgroup.mem_centralizer_iff.mp (hYB hy) β hβ).symm
  have key : ⁅y, β * l⁆ = β * (y * l * y⁻¹ * l⁻¹) * β⁻¹ := by
    rw [commutatorElement_def]
    calc y * (β * l) * y⁻¹ * (β * l)⁻¹ = (y * β) * l * y⁻¹ * l⁻¹ * β⁻¹ := by group
      _ = (β * y) * l * y⁻¹ * l⁻¹ * β⁻¹ := by rw [hyβ]
      _ = β * (y * l * y⁻¹ * l⁻¹) * β⁻¹ := by group
  rw [key]
  have hyl : y * l * y⁻¹ * l⁻¹ ∈ L :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hYL hy) l).mp hl.2) (inv_mem hl.2)
  exact (Subgroup.mem_normalizer_iff.mp (hAL (hBA hβ)) _).mp hyl

@[expose] def KS142SignalPGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → Sec8.IsZ3PGLThreePi (lBarA c L A) →
      (∃ x ∈ A, Sec4.InducesTypeOn L x 3) →
      ∀ B : Subgroup G, IsHyperplane A B → c ∈ B → ¬ A ⊓ L ≤ B →
        ∀ e ∈ B, e ∉ Subgroup.zpowers c → ∀ he : e ∈ Subgroup.normalizer (L : Set G),
          ∃ W : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), ¬ 3 ∣ Nat.card W ∧
            thetaFix L he ≤ Subgroup.normalizer (W : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ∧
            ∀ U : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), U ≤ thetaFix L he →
              ¬ 3 ∣ Nat.card U → U ≤ W

@[expose] def Step142PGLCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Sec8.IsZ3PGLThreePi (lBarA c L A) →
      Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) → (∃ x ∈ A, Sec4.InducesTypeOn L x 3) →
      (∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥) →
      ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
          (piCompl 3),
        ∀ B : Subgroup G, IsHyperplane A B → c ∈ B → A ⊓ L ≤ B →
          ⁅Q ⊓ Subgroup.centralizer (B : Set G), A⁆ ≤
            pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))

theorem eq_sup_of_not_le {A B X : Subgroup G} (hA : Late.IsE27 A) (hB : IsHyperplane A B)
    (hXA : X ≤ A) (hXB : ¬ X ≤ B) : A = B ⊔ X := by
  have hle : B ⊔ X ≤ A := sup_le hB.1 hXA
  have hlt : B < B ⊔ X := lt_of_le_of_ne le_sup_left fun h => hXB (h ▸ le_sup_right)
  have hdvd : Nat.card (B ⊔ X : Subgroup G) ∣ 27 := hA.2 ▸ Subgroup.card_dvd_of_le hle
  have hB9 : Nat.card B = 9 := by have := hB.2; rw [hA.2] at this; omega
  have hBdvd : 9 ∣ Nat.card (B ⊔ X : Subgroup G) := hB9 ▸ Subgroup.card_dvd_of_le le_sup_left
  have hne : Nat.card (B ⊔ X : Subgroup G) ≠ 9 := by
    intro h9
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h9, hB9]))
  have h27 : Nat.card (B ⊔ X : Subgroup G) = 27 := by
    obtain ⟨k, hk⟩ := hBdvd
    rw [hk] at hdvd hne
    have hk3 : k ∣ 3 := by
      rw [show (27 : ℕ) = 9 * 3 by norm_num] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 9) hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
    · exact absurd (by simp) hne
    · rw [hk]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h27, hA.2])).symm

theorem exists_closure_pair_of_mem {A B : Subgroup G} (hA : Late.IsE27 A) (hB : IsHyperplane A B)
    {c : G} (hcB : c ∈ B) (hc3 : Nat.card (Subgroup.zpowers c) = 3) :
    ∃ e ∈ B, e ∉ Subgroup.zpowers c ∧ B = Subgroup.closure {c, e} := by
  have hB9 : Nat.card B = 9 := by have := hB.2; rw [hA.2] at this; omega
  have hlt : Subgroup.zpowers c < B := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hcB) fun h => ?_
    have := congrArg (fun S : Subgroup G => Nat.card S) h
    simp only [hc3, hB9] at this
    omega
  obtain ⟨e, heB, heC⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨e, heB, heC, ?_⟩
  have hle : Subgroup.closure {c, e} ≤ B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hcB
    · exact heB
  have hlt' : Subgroup.zpowers c < Subgroup.closure {c, e} := by
    refine lt_of_le_of_ne ?_ fun h => heC (h ▸ Subgroup.subset_closure (by simp))
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_mono (by simp)
  have hdvd : Nat.card (Subgroup.closure {c, e} : Subgroup G) ∣ 9 :=
    hB9 ▸ Subgroup.card_dvd_of_le hle
  have h3dvd : 3 ∣ Nat.card (Subgroup.closure {c, e} : Subgroup G) :=
    hc3 ▸ Subgroup.card_dvd_of_le hlt'.le
  have hne3 : Nat.card (Subgroup.closure {c, e} : Subgroup G) ≠ 3 := by
    intro h3
    exact hlt'.ne (Subgroup.eq_of_le_of_card_ge hlt'.le (by rw [h3, hc3]))
  have h9 : Nat.card (Subgroup.closure {c, e} : Subgroup G) = 9 := by
    obtain ⟨k, hk⟩ := h3dvd
    rw [hk] at hdvd hne3
    have hk3 : k ∣ 3 := by
      rw [show (9 : ℕ) = 3 * 3 by norm_num] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
    · exact absurd (by simp) hne3
    · rw [hk]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hB9])).symm

theorem step142LThreePiPGL_of (hsig : KS142SignalPGL) (hcore : Step142PGLCore) :
    Step142LThreePiPGL := by
  intro G _ _ A c L h hPGL hstar hx hLB Q hQ B hB hcB
  by_cases hAL : A ⊓ L ≤ B
  · exact hcore G A c L h hPGL hstar hx hLB Q hQ B hB hcB hAL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := h.isE27'
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hcA := hD.mem_A
  have hLc := hD.le_centralizer
  have hAL' : A ≤ Subgroup.normalizer (L : Set G) := hD.mem_lA.2.1
  have h3L : 3 ∣ Nat.card L := by
    obtain ⟨-, -, D, hDL, -, hD9⟩ := facts_of_isZ3PGLThreePi hD hPGL
    exact (show 3 ∣ 9 by norm_num).trans (hD9 ▸ Subgroup.card_dvd_of_le hDL)
  have hCL := centralizer_le_normalizer_of_three_dvd h h3L
  have hQc := le_centralizer_of_mem_invariantPiSubgroups hcA hD.orderOf_eq hQ.prop
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.prop.2.1
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hD.orderOf_eq]
  obtain ⟨e, heB, hec, hBeq⟩ := exists_closure_pair_of_mem hA hB hcB hc3
  have heA : e ∈ A := hB.1 heB
  have heN : e ∈ Subgroup.normalizer (L : Set G) := hAL' heA
  have hAeq : A = B ⊔ (A ⊓ L) := eq_sup_of_not_le hA hB inf_le_left hAL
  set Y' := Q ⊓ Subgroup.centralizer (B : Set G) with hY'
  have hY'3 : ¬ 3 ∣ Nat.card Y' := fun h3 => hQ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) :=
    le_normalizer_inf_centralizer hA.1.1 hQ.prop.2.2 hB.1
  have hCBe : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heB)
  have hCBc : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)
  set Z := ⁅Y', A⁆ with hZdef
  have hZY' : Z ≤ Y' := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Y' A hAY'
  have hZL : Z ≤ L :=
    commutator_le_of_eq_sup_inf hAeq hB.1 hAab hAL' inf_le_right
      ((inf_le_left.trans hQc).trans hCL)
  have hZe : Z ≤ L ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_inf hZL (hZY'.trans (inf_le_right.trans hCBe))
  have hZ3 : ¬ 3 ∣ Nat.card Z := fun h3 => hY'3 (h3.trans (Subgroup.card_dvd_of_le hZY'))
  have hBC : L ⊓ Subgroup.centralizer ({e} : Set G) ≤ Subgroup.centralizer (B : Set G) := by
    intro x hx
    rw [hBeq, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hLc hx.1)).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
  have hCB : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (hCBc.trans hCL) (hCBe.trans Subgroup.le_normalizer)
  obtain ⟨W, hW3, hWN, hWle⟩ := hsig G A c L hD hPGL hx B hB hcB hAL e heB hec heN
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set U := (Z.subgroupOf L).map π with hU
  have hUF : U ≤ thetaFix L heN := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_thetaFix_of_mem_centralizer heN (hZe (Subgroup.mem_subgroupOf.mp hx)).2
  have hU3 : ¬ 3 ∣ Nat.card U := by
    intro h3
    apply hZ3
    refine h3.trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv]
  exact le_pPrimeCoreOf_of_signalFix heN hW3 hWN hBC hCB hZe (hWle U hUF hU3)

theorem step142LThreePi_of' (h131 : Item131) (hspor : SporadicModels131)
    (hsig : KS142SignalLThreePi) (hsigPGL : KS142SignalPGL) (hcore : Step142PGLCore) :
    Step142LThreePi :=
  step142LThreePi_of h131 hspor hsig (step142LThreePiPGL_of hsigPGL hcore)

end CFSG.RankThree.PartTwo.Sec14
