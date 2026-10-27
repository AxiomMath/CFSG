module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res10ProofR
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGen
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Late.Transitivity

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open CFSG.Assembly.RankThreeEven (projSp)
open Item812Res3 (IsMaxPSub)

namespace Item812Res10

variable {G : Type} [Group G] [Finite G]

theorem card_le_card_inf_of_isMaxPSub {Q K C P : Subgroup G} (hQ : IsMaxPSub 3 Q K)
    (hCK : C ≤ K) (hQC : Q ≤ Subgroup.normalizer (C : Set G)) (hP : IsPGroup 3 P)
    (hPC : P ≤ C) : Nat.card P ≤ Nat.card (Q ⊓ C : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Q ⊔ C with hH
  have hHN : H ≤ Subgroup.normalizer (C : Set G) := sup_le hQC Subgroup.le_normalizer
  have hHK : H ≤ K := sup_le hQ.1 hCK
  let QH : Sylow 3 H :=
    { toSubgroup := Q.subgroupOf H
      isPGroup' := hQ.2.1.comap_subtype
      is_maximal' := by
        intro R hR hle
        have hRmap : IsPGroup 3 (R.map H.subtype) := hR.map H.subtype
        have hQR : Q ≤ R.map H.subtype := fun x hx => ⟨⟨x, Subgroup.mem_sup_left hx⟩, hle hx, rfl⟩
        have hRK : R.map H.subtype ≤ K := (Subgroup.map_subtype_le R).trans hHK
        have heq := hQ.2.2 _ hRmap hQR hRK
        refine le_antisymm (fun y hy => ?_) hle
        have hy' : (y : G) ∈ R.map H.subtype := ⟨y, hy, rfl⟩
        rw [heq] at hy'
        exact hy' }
  obtain ⟨R, hR⟩ := (hP.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H QH R
  have hmem : ∀ p ∈ P, (g : G)⁻¹ * p * g ∈ Q ⊓ C := by
    intro p hp
    have hpH : p ∈ H := Subgroup.mem_sup_right (hPC hp)
    have h1 : (⟨p, hpH⟩ : H) ∈ (R : Subgroup H) := hR hp
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 : ((MulAut.conj g)⁻¹ • (⟨p, hpH⟩ : H) : H) = g⁻¹ * ⟨p, hpH⟩ * g := by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]
    rw [h2] at h1
    refine ⟨h1, ?_⟩
    have hgN : (g : G)⁻¹ ∈ Subgroup.normalizer (C : Set G) := Subgroup.inv_mem _ (hHN g.2)
    have h3 := (Subgroup.mem_normalizer_iff.mp hgN p).mp (hPC hp)
    rwa [inv_inv] at h3
  refine Nat.card_le_card_of_injective
    (fun p : P => (⟨(g : G)⁻¹ * p * g, hmem p p.2⟩ : (Q ⊓ C : Subgroup G))) ?_
  intro p q hpq
  have h1 := congrArg Subtype.val hpq
  simp only at h1
  exact Subtype.ext (by simpa using h1)

theorem commute_of_injective {H M : Type*} [Group H] [Group M] {f : H →* M}
    (hf : Function.Injective f) (e : ↥f.range ≃* Multiplicative (ZMod 9 × ZMod 9)) (y z : H) :
    y * z = z * y := by
  have h1 : e (f.rangeRestrict y) * e (f.rangeRestrict z) =
      e (f.rangeRestrict z) * e (f.rangeRestrict y) := mul_comm _ _
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul] at h1
  exact hf (congrArg Subtype.val (e.injective h1))

theorem factorization_card_X {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X Y : Subgroup G} {n : ℕ} (h : Sec8Final G A c L a b X Y n) :
    (Nat.card X).factorization 3 = 4 := by
  obtain ⟨-, -, h3, -⟩ := solvable_prime_complement_core_characterization
    (H := X) Nat.prime_three
  have hQ : Nat.card (X ⧸ aschbacherSolvableCore 3 X) = 1056706560 := by
    rw [Nat.card_congr h.item89_X.some.toEquiv, Item812Res2.card_projSp_two_three]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 X), hQ,
    Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
    factorization_card_sp48_three, Nat.factorization_eq_zero_of_not_dvd h3, add_zero]

end Item812Res10

open Item812Res10

theorem fin812Q2Card_of (h45 : Sec4.Item4_5) : Fin812Q2Card := by
  intro G _ _ A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAab := h.mem_partTwoF.1
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb1 : b ≠ 1 := h.isGammaIndex.2.1
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hXb : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hXC : X ≤ Subgroup.centralizer ({b} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt_three hXb
  have hupper : Nat.card (Q ⊓ X : Subgroup G) ≤ 81 := by
    set φ : ↥(Q ⊓ X) →* X ⧸ aschbacherSolvableCore 3 X :=
      (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp
        (Subgroup.inclusion (inf_le_right : Q ⊓ X ≤ X)) with hφ
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro y hy
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
      exact Subtype.ext (eq_one_of_mem_theta hQ.2.1 y.2.1 ⟨_, hy, rfl⟩)
    have hp : IsPGroup 3 φ.range :=
      (hQ.2.1.to_le inf_le_left).of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have hdvd : 3 ^ k ∣ Nat.card (X ⧸ aschbacherSolvableCore 3 X) := by
      rw [← hk]
      exact Subgroup.card_subgroup_dvd_card _
    have hk4 : k ≤ 4 := by
      by_contra hk5
      push Not at hk5
      exact not_dvd_card h ((Nat.pow_dvd_pow 3 hk5).trans hdvd)
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hk]
    calc 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
      _ = 81 := by norm_num
  obtain ⟨x, hxA, hxk⟩ := h.mem_pairOmega.2.2.2.1
  have hxout : InducesOuterTheta x X := by
    rcases hxk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  obtain ⟨S₀, hS₀A, -, -, -, -, hBS⟩ := Item812Res2.sec8B_structure_of_projSp
    h.toTheoremFourHyp.localRank_three.le h.mem_partTwoF h.card_eq hbA hb1 hXb h.item89_X hxA
    hxout
  have hS₀p : IsPGroup 3 S₀ := fun s =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hAab.2 _ (hS₀A ⟨s, s.2, rfl⟩)))⟩
  obtain ⟨P, hS₀P⟩ := hS₀p.exists_le_sylow
  have hP81 : Nat.card (P : Subgroup X) = 81 := by
    rw [Sylow.card_eq_multiplicity, factorization_card_X h]
    norm_num
  set P' : Subgroup G := (P : Subgroup X).map X.subtype with hP'
  have hP'p : IsPGroup 3 P' := P.isPGroup'.map X.subtype
  have hP'card : Nat.card P' = 81 := by
    rw [hP', Subgroup.card_map_of_injective X.subtype_injective, hP81]
  set ψ : ↥(P : Subgroup X) →* ↥(projSp 2 (GaloisField 2 3)) :=
    h.item89_X.some.toMonoidHom.comp ((QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp
      (P : Subgroup X).subtype) with hψ
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 X) (y : X) = 1 := by
      have := congrArg h.item89_X.some.symm hy
      simpa [hψ] using this
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : ((y : X) : G) = 1 :=
      eq_one_of_mem_theta hP'p ⟨(y : X), y.2, rfl⟩ ⟨_, h1, rfl⟩
    exact Subtype.ext (Subtype.ext h2)
  have hψcard : Nat.card ψ.range = 81 := by
    rw [← hP81, ← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
  obtain ⟨eP⟩ := kFSp48SylowThree_holds ψ.range hψcard
  have hPab : ∀ y ∈ P', ∀ z ∈ P', y * z = z * y := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    have := commute_of_injective hψinj eP ⟨y, hy⟩ ⟨z, hz⟩
    exact congrArg (fun w : ↥(P : Subgroup X) => ((w : X) : G)) this
  have hBC : sec8B A X ≤ Subgroup.centralizer (P' : Set G) := by
    rw [hBS]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, -, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp (hXC y.2)
    · rintro _ ⟨s, hs, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hPab y hy _ ⟨s, hS₀P hs, rfl⟩
  have hPB : P' ≤ Subgroup.centralizer (sec8B A X : Set G) :=
    Subgroup.le_centralizer_iff.mp hBC
  have hPX : P' ≤ X := Subgroup.map_subtype_le _
  have hbB : b ∈ sec8B A X :=
    ⟨hbA, Subgroup.mem_sup_right (Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hXb)⟩
  have hQb : Q ≤ Subgroup.centralizer ({b} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hQ.1 hg) b hbB).symm)
  have hQN : Q ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hb3 hb1 hQ.2.1
      hQb X hXb
  have hQC : Q ≤ Subgroup.normalizer
      ((X ⊓ Subgroup.centralizer (sec8B A X : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hQN (hQ.1.trans Subgroup.le_normalizer)
  have hlow := card_le_card_inf_of_isMaxPSub hQ inf_le_right hQC hP'p (le_inf hPX hPB)
  have hle : Nat.card (Q ⊓ (X ⊓ Subgroup.centralizer (sec8B A X : Set G)) : Subgroup G) ≤
      Nat.card (Q ⊓ X : Subgroup G) :=
    Subgroup.card_le_of_le (inf_le_inf_left _ inf_le_left)
  rw [hP'card] at hlow
  omega

theorem fin812QR_of_res10' (h45 : Sec4.Item4_5) (h84 : Pair84A)
    (hQ1 : Fin812Q1Cyclic) : Fin812QR :=
  fin812QR_of_res10 h45 h84 (fin812Q2Card_of h45) hQ1

end CFSG.RankThree.PartTwo.Sec8
