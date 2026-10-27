module

public import CFSG.RankThree.PartTwo.Sec15.Item1510StepsProofPGL
import CFSG.RankThree.PartTwo.Sec15.Gagen1510Lift
import CFSG.RankThree.PartTwo.Sec15.Gagen1510Kernel
import CFSG.RankThree.PartTwo.Sec15.Gagen1510Commutator
import CFSG.RankThree.PartTwo.Sec15.Gagen1510Singer
import CFSG.RankThree.PartTwo.Sec15.Gagen1510Torus
import CFSG.RankThree.PartTwo.KFacts.L34PGLFusionFacts
import CFSG.RankThree.PartTwo.KFacts.L34PGLFusionDichotomy
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.RankThree.PartTwo.Sec18.SylowFiveCent
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

private theorem card_galoisField_two_two : Nat.card (GaloisField 2 2) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

private theorem kfacts_data {X : Type*} [Group X]
    (χ : X ≃* projectiveSL 3 (GaloisField 2 2)) :
    (∀ α : MulAut X, IsPGroup 3 (Subgroup.zpowers α) → α ^ 3 = 1) ∧
    (∀ R : Subgroup (MulAut X), IsPGroup 3 R → Nat.card R ∣ 27) ∧
    (∀ Q : Subgroup X, IsPGroup 3 Q → Nat.card Q ∣ 9) ∧
    (∀ E : Subgroup X, Nat.card E = 9 → ∃ t : X, ∀ z ∈ E, t * z * t⁻¹ = z⁻¹) ∧
    (∀ E : Subgroup X, Nat.card E = 9 → ∀ α : MulAut X, α ^ 3 = 1 →
      (∀ e ∈ E, α e = e) → ∃ e ∈ E, α = MulAut.conj e) := by
  have hk := card_galoisField_two_two
  refine ⟨fun α => KFacts.L34.pow_three_eq_one_of_isPGroup_zpowers (α := α) hk χ,
    fun R => KFacts.L34.card_dvd_27_of_isPGroup (R := R) hk χ,
    fun Q => KFacts.L34.card_dvd_9_of_isPGroup (Q := Q) hk χ,
    fun E => KFacts.L34.exists_inverting_of_card_eq_nine (E := E) hk χ, ?_⟩
  intro E hE α hα3 hfix
  exact Sec18.SylowFive.exists_mem_conj_eq_of_fixes hk χ hE hfix (m := 1) (by simpa using hα3)

private theorem map_conj_inv_le_of_le_normalizer {A P : Subgroup G} {x : G}
    (hxP : x ∈ Subgroup.normalizer (P : Set G)) (hAP : A ≤ P) :
    A.map (MulAut.conj x⁻¹).toMonoidHom ≤ P := by
  have hP : P.map (MulAut.conj x⁻¹).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hxP)
  rw [← hP]
  exact Subgroup.map_mono hAP

private theorem le_map_conj_inv_of_le_normalizer {A B : Subgroup G} {x : G}
    (hxB : x ∈ Subgroup.normalizer (B : Set G)) (hBA : B ≤ A) :
    B ≤ A.map (MulAut.conj x⁻¹).toMonoidHom := by
  have hB : B.map (MulAut.conj x⁻¹).toMonoidHom = B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hxB)
  rw [← hB]
  exact Subgroup.map_mono hBA

private theorem conj_toMonoidHom_apply (x y : G) :
    (MulAut.conj x).toMonoidHom y = x * y * x⁻¹ := rfl

private theorem map_conj_inv_map_conj (A : Subgroup G) (x : G) :
    (A.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom = A := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    have h : (MulAut.conj x).toMonoidHom ((MulAut.conj x⁻¹).toMonoidHom a) = a := by
      rw [conj_toMonoidHom_apply, conj_toMonoidHom_apply]
      group
    rwa [h]
  · intro hz
    refine ⟨(MulAut.conj x⁻¹).toMonoidHom z, Subgroup.mem_map_of_mem _ hz, ?_⟩
    rw [conj_toMonoidHom_apply, conj_toMonoidHom_apply]
    group

private theorem commute_of_mem_map_conj_inv {A : Subgroup G} (hA : IsMulCommutative A)
    {x u v : G} (hu : u ∈ A.map (MulAut.conj x⁻¹).toMonoidHom)
    (hv : v ∈ A.map (MulAut.conj x⁻¹).toMonoidHom) : u * v = v * u := by
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hv
  have hcomm : u' * v' = v' * u' :=
    congrArg Subtype.val (hA.is_comm.comm ⟨u', hu'⟩ ⟨v', hv'⟩)
  rw [conj_toMonoidHom_apply, conj_toMonoidHom_apply]
  simp only [inv_inv]
  calc x⁻¹ * u' * x * (x⁻¹ * v' * x) = x⁻¹ * (u' * v') * x := by group
    _ = x⁻¹ * (v' * u') * x := by rw [hcomm]
    _ = x⁻¹ * v' * x * (x⁻¹ * u' * x) := by group

private theorem thetaQuotMulAut_normalizerMonoidHom_eq_one {L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hcN : c ∈ Subgroup.normalizer (L : Set G)) :
    Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨c, hcN⟩) = 1 := by
  have h1 : L.normalizerMonoidHom ⟨c, hcN⟩ = 1 := by
    ext ℓ
    rw [Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply]
    have hcomm : (ℓ : G) * c = c * (ℓ : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLc ℓ.2)
    rw [← hcomm]
    group
  rw [h1, map_one]

private theorem mem_theta_of_fixes {L : Subgroup G} {e y : G}
    (heN : e ∈ Subgroup.normalizer (L : Set G)) (hyL : y ∈ L)
    (hfix : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩)
        (((⟨y, hyL⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L))) =
      ((⟨y, hyL⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :
    ∀ q ∈ Subgroup.zpowers e, y * q * y⁻¹ * q⁻¹ ∈
      inSubgroup (aschbacherSolvableCore 3) L := by
  intro q hq
  have hqN : q ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpowers_le.mpr heN hq
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  set s : (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    ((⟨y, hyL⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)) with hs
  have hstab : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩) ∈
      MulAction.stabilizer (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) s := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact hfix
  have hfixq : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e ^ k, hqN⟩) s = s := by
    have hqsub : (⟨e ^ k, hqN⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨e, heN⟩ : Subgroup.normalizer (L : Set G)) ^ k := by
      apply Subtype.ext
      simp
    rw [hqsub]
    simp only [map_zpow]
    have hk := Subgroup.zpow_mem
      (MulAction.stabilizer (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) s) hstab k
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hk
  rw [Sec4.thetaQuotMulAut_mk] at hfixq
  have hdiv : L.normalizerMonoidHom ⟨e ^ k, hqN⟩ ⟨y, hyL⟩ / ⟨y, hyL⟩ ∈
      aschbacherSolvableCore 3 ↥L := QuotientGroup.eq_iff_div_mem.mp hfixq
  have hmem : e ^ k * y * (e ^ k)⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    refine Subgroup.mem_map.mpr ⟨_, hdiv, ?_⟩
    simp [Sec4.normalizerMonoidHom_apply_coe hqN, div_eq_mul_inv]
  rw [show y * e ^ k * y⁻¹ * (e ^ k)⁻¹ = (e ^ k * y * (e ^ k)⁻¹ * y⁻¹)⁻¹ by group]
  exact (inSubgroup (aschbacherSolvableCore 3) L).inv_mem hmem

private theorem not_mem_zpowers_of_outer {L : Subgroup G} {c e : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hcN : c ∈ Subgroup.normalizer (L : Set G))
    (heN : e ∈ Subgroup.normalizer (L : Set G))
    {ε : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)}
    (hεeq : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩) = ε)
    (hεout : ε ∉ (MulAut.conj :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
        MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range) :
    e ∉ Subgroup.zpowers c := by
  intro he
  have hρc := thetaQuotMulAut_normalizerMonoidHom_eq_one hLc hcN
  have hρe : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩) = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp he
    have hsub : (⟨e, heN⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨c, hcN⟩ : Subgroup.normalizer (L : Set G)) ^ k := by
      apply Subtype.ext
      simpa using hk.symm
    rw [hsub]
    simp only [map_zpow]
    rw [hρc, one_zpow]
  have hε1 : ε = 1 := by rw [← hεeq]; exact hρe
  exact hεout ⟨1, by rw [hε1]; simp⟩

private theorem eq_sup_zpowers_of_card_nine {A B L : Subgroup G} {c b : G}
    (hA : IsMulCommutative A) (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    (hcB : c ∈ B) (hbB : b ∈ B) (hbL : b ∈ L) (hcL : c ∉ L) (hc3 : orderOf c = 3)
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    B = Subgroup.zpowers c ⊔ Subgroup.zpowers b := by
  have hcA : c ∈ A := hBA hcB
  have hbA : b ∈ A := hBA hbB
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hcb : c * b = b * c :=
    congrArg Subtype.val (hA.is_comm.comm ⟨c, hcA⟩ ⟨b, hbA⟩)
  have hcomm : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer (s := (Subgroup.zpowers b : Set G)) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((show Commute c b from hcb).symm.zpow_left n).eq
  have hinf : Subgroup.zpowers c ⊓ Subgroup.zpowers b = ⊥ := by
    have hbot : L ⊓ Subgroup.zpowers c = ⊥ :=
      Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hc3 hcL
    have hle : Subgroup.zpowers c ⊓ Subgroup.zpowers b ≤ L ⊓ Subgroup.zpowers c :=
      le_inf (le_trans inf_le_right (Subgroup.zpowers_le.mpr hbL)) inf_le_left
    exact le_antisymm (hbot ▸ hle) bot_le
  have hcard : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers b : Subgroup G) = 9 := by
    have h := Sec6.card_sup_mul_card_inf hcomm
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hc3, hbord] at h
    omega
  have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers b ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr hcB) (Subgroup.zpowers_le.mpr hbB)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hB9, hcard])).symm

private theorem eq_sup_zpowers_of_gt_of_dvd {A' B : Subgroup G} {e : G}
    (hle : B ⊔ Subgroup.zpowers e ≤ A') (hB9 : Nat.card B = 9)
    (heB : e ∉ B) (hA'27 : Nat.card A' = 27) :
    A' = B ⊔ Subgroup.zpowers e := by
  have hN : Nat.card (B ⊔ Subgroup.zpowers e : Subgroup G) ∣ 27 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hA'27] at this
  have h9 : 9 ∣ Nat.card (B ⊔ Subgroup.zpowers e : Subgroup G) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : B ≤ B ⊔ Subgroup.zpowers e)
    rwa [hB9] at this
  have hgt : 9 < Nat.card (B ⊔ Subgroup.zpowers e : Subgroup G) := by
    have hne : B ⊔ Subgroup.zpowers e ≠ B := by
      intro h
      exact heB (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
    have hle' : Nat.card B ≤ Nat.card (B ⊔ Subgroup.zpowers e : Subgroup G) :=
      Subgroup.card_le_of_le le_sup_left
    have hne' : Nat.card B ≠ Nat.card (B ⊔ Subgroup.zpowers e : Subgroup G) := by
      intro heq
      exact hne (Subgroup.eq_of_le_of_card_ge le_sup_left heq.ge).symm
    omega
  obtain ⟨a, ha⟩ := h9
  obtain ⟨m, hm⟩ := hN
  have hab : a * m = 3 := by
    have h27 : 27 = 9 * (a * m) := by
      rw [hm, ha]
      ring
    omega
  have ha13 : a = 1 ∨ a = 3 := (Nat.dvd_prime Nat.prime_three).mp ⟨m, hab.symm⟩
  have hcard : Nat.card (B ⊔ Subgroup.zpowers e : Subgroup G) = 27 := by
    rcases ha13 with h | h
    · rw [ha, h] at hgt
      omega
    · rw [ha, h]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hA'27, hcard])).symm

private theorem not_mem_of_outer {B L : Subgroup G} {c b e : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hcN : c ∈ Subgroup.normalizer (L : Set G))
    (hbL : b ∈ L) (hB_eq : B = Subgroup.zpowers c ⊔ Subgroup.zpowers b)
    (heN : e ∈ Subgroup.normalizer (L : Set G))
    {ε : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)}
    (hεeq : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩) = ε)
    (hεout : ε ∉ (MulAut.conj :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
        MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range) :
    e ∉ B := by
  let ρ : Subgroup.normalizer (L : Set G) →*
      MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom
  have hρc : ρ ⟨c, hcN⟩ = 1 :=
    thetaQuotMulAut_normalizerMonoidHom_eq_one hLc hcN
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hbL
  have hρb : ρ ⟨b, hbN⟩ = MulAut.conj ((⟨b, hbL⟩ : ↥L) :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    change Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨b, hbN⟩) =
      MulAut.conj ((⟨b, hbL⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    exact KFacts.thetaQuotMulAut_compAction_of_mem hbL hbN
  let K : Subgroup (Subgroup.normalizer (L : Set G)) :=
    (MulAut.conj :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
        MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range.comap ρ
  let H : Subgroup G := K.map (Subgroup.normalizer (L : Set G)).subtype
  have hcH : c ∈ H := by
    refine Subgroup.mem_map.mpr ⟨⟨c, hcN⟩, ?_, rfl⟩
    change ρ ⟨c, hcN⟩ ∈ (MulAut.conj :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
        MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range
    exact ⟨1, by rw [hρc]; simp⟩
  have hbH : b ∈ H := by
    refine Subgroup.mem_map.mpr ⟨⟨b, hbN⟩, ?_, rfl⟩
    change ρ ⟨b, hbN⟩ ∈ (MulAut.conj :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
        MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range
    exact ⟨_, hρb.symm⟩
  have hBH : B ≤ H := by
    rw [hB_eq]
    exact sup_le (Subgroup.zpowers_le.mpr hcH) (Subgroup.zpowers_le.mpr hbH)
  have heH : e ∉ H := by
    rintro ⟨⟨g, hgN⟩, hgK, hge⟩
    change ρ ⟨g, hgN⟩ ∈ (MulAut.conj :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
        MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range at hgK
    have hgeq : (⟨g, hgN⟩ : Subgroup.normalizer (L : Set G)) = ⟨e, heN⟩ :=
      Subtype.ext hge
    rw [hgeq] at hgK
    obtain ⟨p, hp⟩ := hgK
    exact hεout ⟨p, by rw [← hεeq]; exact hp⟩
  intro heB
  exact heH (hBH heB)

private theorem singer_finish {A A' L : Subgroup G} {c b x e : G}
    (hD : Sec13Data G A c L) (hcL : c ∉ L)
    (hCN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hAxx : A'.map (MulAut.conj x).toMonoidHom = A)
    (hA'c : A' ≤ Subgroup.centralizer ({c} : Set G))
    (hcA' : c ∈ A') (hbA' : b ∈ A') (hbL : b ∈ L)
    (heA' : e ∈ A') (heN : e ∈ Subgroup.normalizer (L : Set G)) (he3 : e ^ 3 = 1)
    (hec : e ∉ Subgroup.zpowers c)
    {ε : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)}
    (hεeq : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩) = ε)
    {s : (↥L ⧸ aschbacherSolvableCore 3 ↥L)}
    (hs : s ∈ inSubgroup (aschbacherSolvableCore 3) (GL3TwoFixedModel.autFixed ε))
    (hbs : ((⟨b, hbL⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)) * s *
        (((⟨b, hbL⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)))⁻¹ ≠ s) :
    (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ∈ omegaA A := by
  obtain ⟨y₀, hy₀eq⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) s
  have hsfix : ε s = s := by
    have hle : s ∈ GL3TwoFixedModel.autFixed ε :=
      Subgroup.map_subtype_le (aschbacherSolvableCore 3 (GL3TwoFixedModel.autFixed ε)) hs
    exact GL3TwoFixedModel.mem_autFixed.mp hle
  have hfix : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩)
      ((⟨(y₀ : G), y₀.2⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)) =
      ((⟨(y₀ : G), y₀.2⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    rw [show ((⟨(y₀ : G), y₀.2⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)) = s
      from hy₀eq, hεeq]
    exact hsfix
  have hf : ∀ q ∈ Subgroup.zpowers e,
      (y₀ : G) * q * (y₀ : G)⁻¹ * q⁻¹ ∈
        inSubgroup (aschbacherSolvableCore 3) L :=
    mem_theta_of_fixes heN y₀.2 hfix
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : IsPGroup 3 (Subgroup.zpowers e) := by
    have hdvd : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one he3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hQK : Subgroup.zpowers e ≤
      Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) :=
    Subgroup.zpowers_le.mpr (Sec6.normalizer_le_normalizer_theta L heN)
  obtain ⟨n, hnK, hncomm⟩ := exists_mul_conj_eq_of_coprime (p := 3)
    (K := inSubgroup (aschbacherSolvableCore 3) L) (Q := Subgroup.zpowers e)
    (Proof1510Steps.not_three_dvd_card_theta L) hQ hQK (h := (y₀ : G)) (f := id)
    (fun _ hq => hq) hf
  have hyL : n * (y₀ : G) ∈ L :=
    L.mul_mem (Proof1510Steps.inSubgroup_theta_le L hnK) y₀.2
  have hye : e * (n * (y₀ : G)) = (n * (y₀ : G)) * e := by
    have h := hncomm e (Subgroup.mem_zpowers e)
    simp only [id] at h
    calc e * (n * (y₀ : G)) =
        (n * (y₀ : G) * e * (n * (y₀ : G))⁻¹) * (n * (y₀ : G)) := by rw [h]
      _ = (n * (y₀ : G)) * e := by group
  have hyt : ((⟨n * (y₀ : G), hyL⟩ : ↥L) :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L)) = s := by
    obtain ⟨w, hwθ, hwn⟩ := Subgroup.mem_map.mp hnK
    have hwn' : (w : G) = n := hwn
    have hprod : (⟨n * (y₀ : G), hyL⟩ : ↥L) = w * y₀ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      show n * (y₀ : G) = (w : G) * (y₀ : G)
      rw [hwn']
    have hw1 : ((w : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact hwθ
    rw [hprod, QuotientGroup.mk_mul, hw1, one_mul]
    simpa using hy₀eq
  have hs_y : ((⟨n * (y₀ : G), hyL⟩ : ↥L) :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ∈
      inSubgroup (aschbacherSolvableCore 3)
        (GL3TwoFixedModel.autFixed
          (Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩))) := by
    rw [hεeq, hyt]
    exact hs
  have hbs' : ((⟨b, hbL⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)) *
      ((⟨n * (y₀ : G), hyL⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)) *
      (((⟨b, hbL⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)))⁻¹ ≠
      ((⟨n * (y₀ : G), hyL⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    rw [hyt]
    exact hbs
  have hstar : ¬ StarConditionAt A' c :=
    not_starConditionAt_of_singer hD.orderOf_eq hD.le_centralizer hcL hCN hA'c hbL hbA'
      heA' heN hec hyL hye hs_y hbs'
  have hom : Subgroup.zpowers c ∈ omegaA A' :=
    (Sec13.zpowers_mem_omegaA_iff).mpr ⟨hcA', hD.card_zpowers, hstar⟩
  have hfin : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ∈ omegaA A := by
    have h := (Sec13.mem_omegaA_map_conj_iff (A := A')
      (F := Subgroup.zpowers c) x).mpr hom
    rwa [hAxx] at h
  exact hfin

private theorem torus_finish {A A' B L : Subgroup G} {c b x e : G}
    (hD : Sec13Data G A c L) (hcL : c ∉ L)
    (hS9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hinv : ∀ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), Nat.card E = 9 →
      ∃ t : ↥L ⧸ aschbacherSolvableCore 3 ↥L, ∀ z ∈ E, t * z * t⁻¹ = z⁻¹)
    (hxb : (Subgroup.zpowers b).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers b)
    (hB9 : Nat.card B = 9)
    (hB_eq : B = Subgroup.zpowers c ⊔ Subgroup.zpowers b)
    (hxB : x ∈ Subgroup.normalizer
      ((Subgroup.zpowers c ⊔ Subgroup.zpowers b : Subgroup G) : Set G))
    (hBA' : B ≤ A') (hA'card : Nat.card A' = 27) (heB : e ∉ B)
    (heA' : e ∈ A') (he3 : e ^ 3 = 1)
    (heb : e * b = b * e)
    (hbS : b ∈ A ⊓ L) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hA'def : A' = A.map (MulAut.conj x⁻¹).toMonoidHom)
    (heN : e ∈ Subgroup.normalizer (L : Set G))
    {ε : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)}
    (hεeq : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩) = ε)
    {t : (↥L ⧸ aschbacherSolvableCore 3 ↥L)}
    (htfix : ε t = t)
    (htconj : t * ((⟨b, hbS.2⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)) * t⁻¹ =
      (((⟨b, hbS.2⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)))⁻¹) :
    (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ∈ omegaA A := by
  have hA'B : A' = B ⊔ Subgroup.zpowers e :=
    eq_sup_zpowers_of_gt_of_dvd (sup_le hBA' (Subgroup.zpowers_le.mpr heA'))
      hB9 heB hA'card
  have hA'_eq : A.map (MulAut.conj x⁻¹).toMonoidHom =
      Subgroup.zpowers c ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers e := by
    rw [← hA'def, hA'B, hB_eq]
  have ht : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩) t = t := by
    rw [hεeq]
    exact htfix
  exact mem_omegaA_of_torus hD.zpowers_mem_omegaA hS9 hAeq hinv hD.le_centralizer hcL
    hbS hb1 hb3 hxB hxb hA'_eq heN he3 heb ht htconj

theorem step1510PGLFuse_holds : Step1510PGLFuse := by
  intro G _ _ A c L h hall B hB hcB _ P hP hAP _ houter x hx hxc
  have hD := h.toSec13Data
  obtain ⟨⟨χ⟩, hS9, hcL, hAeq, hCN⟩ := setting h hall
  let χ' : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃*
      projectiveSL 3 (GaloisField 2 2) :=
    χ.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))
  obtain ⟨hexp, hcard, hsyl, hinv, hcent⟩ := kfacts_data χ'
  obtain ⟨hexp3, hK⟩ := exponent_and_kernel h hall hcB hP hAP hx.2 hxc hexp
  by_cases hxA : x ∈ Subgroup.normalizer (A : Set G)
  · exact (Sec13.map_conj_mem_omegaA_iff hxA).mpr hD.zpowers_mem_omegaA
  ·
    set A' : Subgroup G := A.map (MulAut.conj x⁻¹).toMonoidHom with hA'def
    have hAxx : A'.map (MulAut.conj x).toMonoidHom = A := by
      rw [hA'def]
      exact map_conj_inv_map_conj A x
    have hne : A' ≠ A := by
      intro hEq
      apply hxA
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
      have h := hAxx
      rw [hEq] at h
      exact h
    have hB9 : Nat.card B = 9 := by
      have h27 := hB.2
      rw [hD.card_eq] at h27
      omega
    obtain ⟨b, hbB, hbS, hb1⟩ :=
      Proof1510Steps.exists_mem_inf_ne_one hD.isElemAbelian.1 hD.card_eq hB.1 hB9
        inf_le_left hS9
    have hbL : b ∈ L := hbS.2
    have hb3 : b ^ 3 = 1 := hexp3 b (hAP hbS.1)
    set bbar : (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
      ((⟨b, hbL⟩ : ↥L) : (↥L ⧸ aschbacherSolvableCore 3 ↥L)) with hbbar
    have hbbar3 : orderOf bbar = 3 := by
      have hbL3 : (⟨b, hbL⟩ : ↥L) ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hb3, Subgroup.coe_one]
      have hdvd : orderOf bbar ∣ 3 := by
        have h1 : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)
            ⟨b, hbL⟩) ∣ orderOf (⟨b, hbL⟩ : ↥L) := orderOf_map_dvd _ _
        have h2 : orderOf (⟨b, hbL⟩ : ↥L) ∣ 3 := orderOf_dvd_of_pow_eq_one hbL3
        exact h1.trans h2
      have hne1 : bbar ≠ 1 := Proof1510Steps.mk_ne_one_of_mem inf_le_right hS9 hbS hb1
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hne1
      · exact h
    have hA'P : A' ≤ P := map_conj_inv_le_of_le_normalizer hx.2 hAP
    have hBA' : B ≤ A' := le_map_conj_inv_of_le_normalizer hx.1 hB.1
    have hcA' : c ∈ A' := hBA' hcB
    have hbA' : b ∈ A' := hBA' hbB
    have hA'card : Nat.card A' = 27 := by
      rw [hA'def, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hD.card_eq]
    have hA'c : A' ≤ Subgroup.centralizer ({c} : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commute_of_mem_map_conj_inv hD.isElemAbelian.1 hu hcA'
    have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
      hCN (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    obtain ⟨hM9, -, hcentM, houtM⟩ :=
      autThetaQuot_conj_props h hall hB hcB hP hAP hx hK hsyl hbB hbL hne
    rcases KFacts.L34.outer_dichotomy card_galoisField_two_two χ' hbbar3 hM9 hcentM houtM with
      ⟨ε, hεM, hεout, s, hs, hbs⟩ | ⟨ε, hεM, hεout, t, htfix, htconj⟩
    ·
      obtain ⟨e, heN, heA', hεeq⟩ := Sec4.mem_autThetaQuot_iff.mp hεM
      have he3 : e ^ 3 = 1 := hexp3 e (hA'P heA')
      have hec : e ∉ Subgroup.zpowers c :=
        not_mem_zpowers_of_outer hD.le_centralizer hcN heN hεeq hεout
      exact singer_finish hD hcL hCN hAxx hA'c hcA' hbA' hbL heA' heN he3 hec hεeq hs hbs
    ·
      obtain ⟨e, heN, heA', hεeq⟩ := Sec4.mem_autThetaQuot_iff.mp hεM
      have he3 : e ^ 3 = 1 := hexp3 e (hA'P heA')
      have hec : e ∉ Subgroup.zpowers c :=
        not_mem_zpowers_of_outer hD.le_centralizer hcN heN hεeq hεout
      have heb : e * b = b * e :=
        commute_of_mem_map_conj_inv hD.isElemAbelian.1 heA' hbA'
      have hxb : (Subgroup.zpowers b).map (MulAut.conj x).toMonoidHom =
          Subgroup.zpowers b :=
        map_conj_zpowers_eq h hall hB hcB hP hAP houter hx.2 hexp3 hK hcard hcent
          hbB hbL hb1
      have hB_eq : B = Subgroup.zpowers c ⊔ Subgroup.zpowers b :=
        eq_sup_zpowers_of_card_nine hD.isElemAbelian.1 hB.1 hB9 hcB hbB hbL hcL
          hD.orderOf_eq hb3 hb1
      have hxB : x ∈ Subgroup.normalizer
          ((Subgroup.zpowers c ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
        rw [← hB_eq]
        exact hx.1
      have heB : e ∉ B :=
        not_mem_of_outer hD.le_centralizer hcN hbL hB_eq heN hεeq hεout
      exact torus_finish hD hcL hS9 hAeq hinv hxb hB9 hB_eq hxB hBA' hA'card heB
        heA' he3 heb hbS hb1 hb3 hA'def heN hεeq htfix htconj

end CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse
