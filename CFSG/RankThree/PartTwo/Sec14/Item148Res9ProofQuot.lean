module

public import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProofCore
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ProofLift

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec14.Item148OneRepair

variable {Γ : Type} [Group Γ] [Finite Γ]

@[expose] noncomputable def thetaIn (L : Subgroup Γ) : Subgroup Γ :=
  (aschbacherSolvableCore 3 L).map L.subtype

@[expose] noncomputable def thetaNorm (L : Subgroup Γ) :
    Subgroup (Subgroup.normalizer (L : Set Γ)) :=
  (thetaIn L).subgroupOf (Subgroup.normalizer (L : Set Γ))

omit [Finite Γ] in
theorem mem_thetaIn_iff {L : Subgroup Γ} (x : L) :
    (x : Γ) ∈ thetaIn L ↔ x ∈ aschbacherSolvableCore 3 L :=
  Subgroup.mem_map_iff_mem L.subtype_injective

omit [Finite Γ] in
theorem thetaIn_le (L : Subgroup Γ) : thetaIn L ≤ L := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem conj_mem_thetaIn {L : Subgroup Γ} {g : Γ} (hg : g ∈ Subgroup.normalizer (L : Set Γ))
    {x : Γ} (hx : x ∈ thetaIn L) : g * x * g⁻¹ ∈ thetaIn L := by
  obtain ⟨t, ht, rfl⟩ := hx
  have h1 : compAction L ⟨g, hg⟩ t ∈ aschbacherSolvableCore 3 L := by
    rw [← map_aschbacherSolvableCore (compAction L ⟨g, hg⟩)]
    exact Subgroup.mem_map_of_mem _ ht
  exact ⟨_, h1, rfl⟩

instance thetaNorm_normal (L : Subgroup Γ) : (thetaNorm L).Normal :=
  ⟨fun n hn g => by
    rw [thetaNorm, Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_thetaIn g.2 hn⟩

theorem not_three_dvd_card_thetaIn (L : Subgroup Γ) : ¬ 3 ∣ Nat.card (thetaIn L) := by
  rw [thetaIn, Subgroup.card_map_of_injective L.subtype_injective]
  exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1

theorem eq_one_of_mem_thetaIn_of_pow {L : Subgroup Γ} {x : Γ} (hx : x ∈ thetaIn L) {s : ℕ}
    (hxs : x ^ (3 ^ s) = 1) : x = 1 := by
  have h1 : orderOf x ∣ 3 ^ s := orderOf_dvd_of_pow_eq_one hxs
  have h2 : orderOf x ∣ Nat.card (thetaIn L) := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : thetaIn L)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exfalso
    apply not_three_dvd_card_thetaIn L
    exact (dvd_pow_self 3 (Nat.succ_ne_zero k)).trans (hk ▸ h2)

variable (L : Subgroup Γ)

@[expose] noncomputable def piTheta :
    Subgroup.normalizer (L : Set Γ) →* Subgroup.normalizer (L : Set Γ) ⧸ thetaNorm L :=
  QuotientGroup.mk' (thetaNorm L)

@[expose] noncomputable def barL : Subgroup (Subgroup.normalizer (L : Set Γ) ⧸ thetaNorm L) :=
  (L.subgroupOf (Subgroup.normalizer (L : Set Γ))).map (piTheta L)

instance barL_normal : (barL L).Normal :=
  (Subgroup.normal_in_normalizer).map _ (QuotientGroup.mk'_surjective _)

@[expose] noncomputable def toBarL : L →* barL L :=
  ((piTheta L).comp (Subgroup.inclusion (Subgroup.le_normalizer : L ≤ _))).codRestrict
    (barL L) fun x => Subgroup.mem_map_of_mem _ (by
      rw [Subgroup.mem_subgroupOf]
      exact x.2)

theorem coe_toBarL (x : L) :
    ((toBarL L x : barL L) : Subgroup.normalizer (L : Set Γ) ⧸ thetaNorm L) =
      piTheta L ⟨x, Subgroup.le_normalizer x.2⟩ :=
  rfl

theorem toBarL_surjective : Function.Surjective (toBarL L) := by
  rintro ⟨_, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

theorem ker_toBarL : (toBarL L).ker = aschbacherSolvableCore 3 L := by
  ext x
  rw [MonoidHom.mem_ker, ← mem_thetaIn_iff]
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [coe_toBarL, piTheta, QuotientGroup.mk'_apply, OneMemClass.coe_one,
      QuotientGroup.eq_one_iff, thetaNorm, Subgroup.mem_subgroupOf] at h1
    exact h1
  · intro h
    apply Subtype.ext
    rw [coe_toBarL, piTheta, QuotientGroup.mk'_apply, OneMemClass.coe_one,
      QuotientGroup.eq_one_iff, thetaNorm, Subgroup.mem_subgroupOf]
    exact h

@[expose] noncomputable def barLEquiv : (L ⧸ aschbacherSolvableCore 3 L) ≃* barL L :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toBarL L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toBarL_surjective L))

theorem barLEquiv_mk (x : L) :
    barLEquiv L (x : L ⧸ aschbacherSolvableCore 3 L) = toBarL L x :=
  rfl

theorem mem_normalizer_barL (y : Subgroup.normalizer (L : Set Γ) ⧸ thetaNorm L) :
    y ∈ Subgroup.normalizer (barL L : Set _) :=
  Subgroup.le_normalizer_of_normal (Subgroup.mem_top y)

theorem congr_thetaQuotMulAut_eq (g : Subgroup.normalizer (L : Set Γ)) :
    MulAut.congr (barLEquiv L) (thetaQuotMulAut L (compAction L g)) =
      (barL L).normalizerMonoidHom ⟨piTheta L g, mem_normalizer_barL L _⟩ := by
  ext y
  obtain ⟨x, rfl⟩ := (barLEquiv L).surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rw [congr_apply_apply148, thetaQuotMulAut_mk, barLEquiv_mk, barLEquiv_mk]
  rw [coe_normalizerMonoidHom148, coe_toBarL, coe_toBarL, ← map_inv,
    ← map_mul, ← map_mul]
  congr 1

variable {L} {E : Subgroup Γ} (hEN : E ≤ Subgroup.normalizer (L : Set Γ))

@[expose] noncomputable def barE : Subgroup (Subgroup.normalizer (L : Set Γ) ⧸ thetaNorm L) :=
  (E.subgroupOf (Subgroup.normalizer (L : Set Γ))).map (piTheta L)

include hEN in
theorem mem_barE {e : Γ} (he : e ∈ E) : piTheta L ⟨e, hEN he⟩ ∈ barE (L := L) (E := E) :=
  Subgroup.mem_map_of_mem _ (by rw [Subgroup.mem_subgroupOf]; exact he)

theorem eq_one_of_mem_E_of_mem_thetaIn (hE : CFSG.Assembly.IsElemAbelian 3 E) {e : Γ}
    (he : e ∈ E) (heθ : e ∈ thetaIn L) : e = 1 :=
  eq_one_of_mem_thetaIn_of_pow heθ (s := 1) (by rw [pow_one]; exact hE.2 e he)

include hEN in
theorem card_barE (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    Nat.card (barE (L := L) (E := E)) = Nat.card E := by
  set f := (piTheta L).comp (E.subgroupOf (Subgroup.normalizer (L : Set Γ))).subtype with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hf, MonoidHom.comp_apply, piTheta, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      thetaNorm, Subgroup.mem_subgroupOf] at hx
    have hxE : ((x : Subgroup.normalizer (L : Set Γ)) : Γ) ∈ E := Subgroup.mem_subgroupOf.mp x.2
    exact Subtype.ext (Subtype.ext (eq_one_of_mem_E_of_mem_thetaIn hE hxE hx))
  have hrange : f.range = barE (L := L) (E := E) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv]

theorem barE_comm_pow (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    (∀ x ∈ barE (L := L) (E := E), ∀ y ∈ barE (L := L) (E := E), x * y = y * x) ∧
      ∀ x ∈ barE (L := L) (E := E), x ^ 3 = 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hc := hE.1.is_comm.comm (⟨x, Subgroup.mem_subgroupOf.mp hx⟩ : E)
      ⟨y, Subgroup.mem_subgroupOf.mp hy⟩
    have hxy : x * y = y * x := Subtype.ext (by simpa using congrArg Subtype.val hc)
    rw [← map_mul, ← map_mul, hxy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact hE.2 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [this, map_one]

theorem barE_inf_centralizer {z : Γ}
    (hzE : Late.sectionCentralizer E L (thetaIn L) = (Subgroup.zpowers z : Set Γ)) :
    ∃ hz : z ∈ E, barE (L := L) (E := E) ⊓ Subgroup.centralizer (barL L : Set _) =
      Subgroup.zpowers (piTheta L ⟨z, hEN hz⟩) := by
  have hzmem : z ∈ Late.sectionCentralizer E L (thetaIn L) := by
    rw [hzE]
    exact Subgroup.mem_zpowers z
  obtain ⟨hz, hzL⟩ := hzmem
  refine ⟨hz, le_antisymm ?_ ?_⟩
  · rintro _ ⟨⟨x, hx, rfl⟩, hxc⟩
    have hxE : (x : Γ) ∈ E := Subgroup.mem_subgroupOf.mp hx
    have hsec : (x : Γ) ∈ Late.sectionCentralizer E L (thetaIn L) := by
      refine ⟨hxE, fun y hy => ?_⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hxc (piTheta L ⟨y, Subgroup.le_normalizer hy⟩)
        (Subgroup.mem_map_of_mem _ (by rw [Subgroup.mem_subgroupOf]; exact hy))
      rw [← map_mul, ← map_mul, piTheta, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, thetaNorm, Subgroup.mem_subgroupOf] at h1
      have hg : (x : Γ) * y ∈ Subgroup.normalizer (L : Set Γ) :=
        Subgroup.mul_mem _ x.2 (Subgroup.le_normalizer hy)
      have h2 := conj_mem_thetaIn hg h1
      have h3 : (x : Γ) * y * (x : Γ)⁻¹ * y⁻¹ = (x : Γ) * y *
          (((⟨y, Subgroup.le_normalizer hy⟩ * x)⁻¹ * (x * ⟨y, Subgroup.le_normalizer hy⟩) :
            Subgroup.normalizer (L : Set Γ)) : Γ) * ((x : Γ) * y)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h3]
      exact h2
    rw [hzE] at hsec
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsec
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
  · rw [Subgroup.zpowers_le]
    refine ⟨mem_barE hEN hz, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have hyL : (y : Γ) ∈ L := Subgroup.mem_subgroupOf.mp hy
    have h1 := hzL _ hyL
    rw [← map_mul, ← map_mul, piTheta, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, thetaNorm, Subgroup.mem_subgroupOf]
    have hg : z⁻¹ * (y : Γ)⁻¹ ∈ Subgroup.normalizer (L : Set Γ) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hEN hz)) (Subgroup.inv_mem _ y.2)
    have h2 := conj_mem_thetaIn hg h1
    have h3 : (((y * ⟨z, hEN hz⟩)⁻¹ * (⟨z, hEN hz⟩ * y) : Subgroup.normalizer (L : Set Γ)) :
        Γ) = z⁻¹ * (y : Γ)⁻¹ * (z * y * z⁻¹ * (y : Γ)⁻¹) * (z⁻¹ * (y : Γ)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h3]
    exact h2

include hEN in
theorem mem_barE_of_mem_centralizer (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hcent : ∀ g ∈ Subgroup.centralizer (E : Set Γ), g ^ 3 = 1 → g ∈ E)
    {g' : Subgroup.normalizer (L : Set Γ) ⧸ thetaNorm L}
    (hg' : g' ∈ Subgroup.centralizer (barE (L := L) (E := E) : Set _)) (hg'3 : g' ^ 3 = 1) :
    g' ∈ barE (L := L) (E := E) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (thetaNorm L) g'
  have hA : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hE.2 _ x.2)⟩
  set α : E →* MulAut (Subgroup.normalizer (L : Set Γ)) :=
    MulAut.conj.comp (Subgroup.inclusion hEN) with hα
  have hN : ∀ x : E, ∀ n ∈ thetaNorm L, α x n ∈ thetaNorm L := fun x n hn =>
    (thetaNorm_normal L).conj_mem n hn _
  have hcop : ¬ 3 ∣ Nat.card (thetaNorm L) := by
    have hle : thetaIn L ≤ Subgroup.normalizer (L : Set Γ) :=
      (thetaIn_le L).trans Subgroup.le_normalizer
    rw [thetaNorm, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact not_three_dvd_card_thetaIn L
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hA α (thetaNorm L) hN
    hcop
  have hq : QuotientGroup.mk' (thetaNorm L) g ∈
      {q | ∀ x : E, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α
        (thetaNorm L) hN x q = q} := by
    intro x
    rw [QuotientGroup.mk'_apply, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    have h1 := Subgroup.mem_centralizer_iff.mp hg' _ (mem_barE hEN x.2)
    have h2 : (α x g : Subgroup.normalizer (L : Set Γ)) = ⟨x, hEN x.2⟩ * g * ⟨x, hEN x.2⟩⁻¹ :=
      rfl
    rw [h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change piTheta L ⟨x, hEN x.2⟩ * piTheta L g * (piTheta L ⟨x, hEN x.2⟩)⁻¹ = piTheta L g
    have h1' : piTheta L ⟨x, hEN x.2⟩ * piTheta L g = piTheta L g * piTheta L ⟨x, hEN x.2⟩ :=
      h1
    rw [h1', mul_inv_cancel_right]
  rw [hlift] at hq
  obtain ⟨c, hc, hcg⟩ := hq
  obtain ⟨M, s, hM, hcs⟩ := exists_pow_mod_three_eq_one c
  have hcomm : ∀ x ∈ E, x * (c : Γ) = c * x := by
    intro x hx
    have h1 := congrArg Subtype.val (hc ⟨x, hx⟩)
    change x * (c : Γ) * x⁻¹ = c at h1
    calc x * (c : Γ) = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [h1]
  have hcent' : ((c ^ M : Subgroup.normalizer (L : Set Γ)) : Γ) ∈
      Subgroup.centralizer (E : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Subgroup.coe_pow]
    exact ((Commute.pow_right (hcomm x hx : Commute x (c : Γ)) M)).eq
  have hpi : piTheta L (c ^ M) = piTheta L g := by
    rw [map_pow]
    change QuotientGroup.mk' (thetaNorm L) c ^ M = _
    rw [hcg, ← Nat.div_add_mod M 3, hM, pow_add, pow_mul, hg'3, one_pow, one_mul, pow_one]
    rfl
  have hc3 : ((c ^ M : Subgroup.normalizer (L : Set Γ)) : Γ) ^ 3 = 1 := by
    have h1 : piTheta L ((c ^ M) ^ 3) = 1 := by
      rw [map_pow, hpi]
      exact hg'3
    rw [piTheta, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, thetaNorm,
      Subgroup.mem_subgroupOf] at h1
    rw [← Subgroup.coe_pow]
    refine eq_one_of_mem_thetaIn_of_pow h1 (s := s) ?_
    rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, hcs, one_pow, OneMemClass.coe_one]
  exact ⟨c ^ M, Subgroup.mem_subgroupOf.mpr (hcent _ hcent' hc3), hpi⟩

theorem inducedAut_mem_of_autFacts148 (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27)
    (hcent : ∀ g ∈ Subgroup.centralizer (E : Set Γ), g ^ 3 = 1 → g ∈ E) {z : Γ} (hz1 : z ≠ 1)
    (hzE : Late.sectionCentralizer E L (thetaIn L) = (Subgroup.zpowers z : Set Γ))
    {M : Type*} [Group M] (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) {D : Subgroup (MulAut M)}
    (hD : AutFacts148 M D) {a : Γ} (ha : a ∈ E) :
    MulAut.congr e (thetaQuotMulAut L (compAction L ⟨a, hEN ha⟩)) ∈ D := by
  set e' : barL L ≃* M := (barLEquiv L).symm.trans e with he'
  have hX := hD.congr e'
  set τ := thetaQuotMulAut L (compAction L ⟨a, hEN ha⟩) with hτdef
  have hτ : MulAut.congr e τ = MulAut.congr e'
      ((barL L).normalizerMonoidHom ⟨piTheta L ⟨a, hEN ha⟩, mem_normalizer_barL L _⟩) := by
    rw [← congr_thetaQuotMulAut_eq, ← congr_trans]
    congr 1
    ext x
    simp [he']
  by_cases hin : IsInnerAut (MulAut.congr e τ)
  · obtain ⟨w, hw⟩ := hin
    rw [← hw]
    exact hD.conj_mem w
  · have hEN' : barE (L := L) (E := E) ≤ Subgroup.normalizer (barL L : Set _) :=
      fun y _ => mem_normalizer_barL L y
    have ha' : ¬ IsInnerAut ((barL L).normalizerMonoidHom
        ⟨piTheta L ⟨a, hEN ha⟩, hEN' (mem_barE hEN ha)⟩) := by
      intro h
      apply hin
      rw [hτ]
      exact (isInnerAut_congr e' _).mpr h
    obtain ⟨hEc', hE3'⟩ := barE_comm_pow (L := L) hE
    have hE27' : Nat.card (barE (L := L) (E := E)) = 27 := by rw [card_barE hEN hE, hE27]
    obtain ⟨hz, hzE'⟩ := barE_inf_centralizer hEN hzE
    have hz1' : piTheta L ⟨z, hEN hz⟩ ≠ 1 := by
      intro h1
      rw [piTheta, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, thetaNorm,
        Subgroup.mem_subgroupOf] at h1
      exact hz1 (eq_one_of_mem_E_of_mem_thetaIn hE hz h1)
    have hcent' := fun g' (hg' : g' ∈ Subgroup.centralizer (barE (L := L) (E := E) : Set _))
      (hg'3 : g' ^ 3 = 1) => mem_barE_of_mem_centralizer hEN hE hcent hg' hg'3
    obtain ⟨u, -, hW⟩ := exists_inf_eq_zpowers148 hX.center_eq_bot hEN' hEc' hE3' hE27' hz1'
      hzE' (mem_barE hEN ha) ha'
    have hmem := mem_of_not_isInnerAut148 _ hX.center_eq_bot hX.inner_mul_pow hX.fixed_e9 hEN'
      hEc' hE3' hcent' (mem_barE hEN ha) ha' hW
    rw [hτ]
    exact hmem

end CFSG.RankThree.PartTwo.Sec14.Item148Res9
