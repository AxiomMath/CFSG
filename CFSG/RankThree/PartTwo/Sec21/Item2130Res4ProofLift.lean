module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res3ProofLift
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofU4Plus
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofCenter
import CFSG.RankThree.PartTwo.Sec18.Transport
import CFSG.RankThree.PartTwo.KFacts.K72SLPiCField
import CFSG.RankThree.PartTwo.Sec9.Item95
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofON
public import CFSG.Assembly.OrderReductions.InvariantSylow
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLocal
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSU)
open scoped commutatorElement

namespace Item2130Res4Proof

theorem eq_one_of_pow_three_of_mem {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    (hN3 : ¬ 3 ∣ Nat.card N) {g : X} (hg : g ∈ N) (hg3 : g ^ 3 = 1) : g = 1 := by
  have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  have h2 : orderOf g ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk g hg]
    exact orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h2) hN3

end Item2130Res4Proof

open Item2130Res3Proof Item2130Res4Proof

theorem item2130ThreeIPlus_holds :
    ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
      Config2130 G A E U c L → 27 ≤ Nat.card (A ⊓ L : Subgroup G) →
      (∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (lBar L ≃* projSU 4 2 n)) → Nat.card A = 3 ^ 4 →
        ∃ b ∈ A ⊓ L, b ≠ 1 ∧ ∃ I : Subgroup G, I ≤ L ∧
          I ∈ thetaComponentsIn
            (Subgroup.centralizer ((Subgroup.closure {c, b} : Subgroup G) : Set G)) ∧
          inSubgroup (CFSG.pCore 3) (I ⊓ Subgroup.centralizer (I : Set G)) = Subgroup.zpowers b ∧
          (∃ n : ℕ, 1 < n ∧ Sec4.IsSLThreePiAt (lBar I) (2 ^ n)) ∧
          A ⊓ L ≤ Subgroup.normalizer (I : Set G) ∧
          A ⊓ L ⊓ Sec4.thetaQuotCentralizer I ≤ Subgroup.zpowers b ∧
          ∃ x ∈ A ⊓ L, ∃ U' : Subgroup G, U' ≤ I ∧
            IsPGroup 2 U' ∧ x ∈ Subgroup.normalizer (U' : Set G) ∧
            ¬ ⁅U', Subgroup.zpowers x⁆ ≤ inSubgroup (aschbacherSolvableCore 3) I := by
  intro G _ _ A E U c L hcfg h27 hL h81
  obtain ⟨n, hn, hno, ⟨φ⟩⟩ := hL
  have hAe0 : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hB27 : Nat.card (A ⊓ L : Subgroup G) = 3 ^ 3 := by
    have h := hcfg.card_eq
    rw [h81] at h
    norm_num at h ⊢
    omega
  have hBe : IsElemAbelian 3 (A ⊓ L : Subgroup G) := Sec4.isElemAbelian_of_le hAe0 inf_le_left
  have hBbar := Item211Res3Proof.isE27_image hBe hB27 (inf_le_right : A ⊓ L ≤ L)
  have : Finite (projSU 4 2 n) := Finite.of_equiv _ φ.toEquiv
  obtain ⟨x', hU4⟩ := ku4OrderThreeSU3Plus_holds n hn hno _ (hBbar.map φ)
  obtain ⟨hx'E, hx'1, hxR, hRSL, hα', y', hy'E, Ubar, hUR, hU2, hyN, hyC⟩ := hU4
  obtain ⟨bbar, ⟨⟨b, hbL⟩, hbB, rfl⟩, rfl⟩ := hx'E
  have hbAL : b ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hbB
  have hbA : b ∈ A := hbAL.1
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hx'1
    have h1 : (⟨1, hbL⟩ : L) = 1 := rfl
    simp [h1]
  replace hxR : φ ((⟨b, hbL⟩ : L) : lBar L) ∈ inSubgroup perfectResidual
      (Subgroup.centralizer ({φ ((⟨b, hbL⟩ : L) : lBar L)} : Set (projSU 4 2 n))) := hxR
  replace hRSL : Sec4.IsSLThreePiAt (inSubgroup perfectResidual
      (Subgroup.centralizer ({φ ((⟨b, hbL⟩ : L) : lBar L)} : Set (projSU 4 2 n)))) (2 ^ n) := hRSL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hbz : IsPGroup 3 (Subgroup.zpowers b) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1, pow_one])
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  obtain ⟨hLCc, hL'⟩ := mem_thetaComponentsIn_iff.mp hLc
  have : Finite (projSU 4 2 n) := Finite.of_equiv _ φ.toEquiv
  set β : L := ⟨b, hbL⟩ with hβ
  set N := aschbacherSolvableCore 3 ↥L with hN
  obtain ⟨hNsol, -, hN3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set π := QuotientGroup.mk' N with hπ
  set CL := Subgroup.centralizer ({β} : Set L) with hCL
  set I₀ := inSubgroup perfectResidual CL with hI₀
  set x := φ (β : lBar L) with hx
  set CM := Subgroup.centralizer ({x} : Set (projSU 4 2 n)) with hCM
  set R := inSubgroup perfectResidual CM with hR
  have hlift : Subgroup.centralizer ({(β : lBar L)} : Set (lBar L)) = CL.map π :=
    map_centralizer_eq_of_coprime hNsol hN3 hbL hbz
  have hφC : (Subgroup.centralizer ({(β : lBar L)} : Set (lBar L))).map φ.toMonoidHom = CM := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      change φ z * φ (β : lBar L) = φ (β : lBar L) * φ z
      rw [← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
  have hRI : I₀.map (φ.toMonoidHom.comp π) = R := by
    rw [← Subgroup.map_map, Item2130Res3Proof.map_inSubgroup_perfectResidual_of_finite π CL,
      ← hlift, Item2130Res3Proof.map_inSubgroup_perfectResidual_of_finite φ.toMonoidHom, hφC]
  set ρ : I₀ →* R := (MulEquiv.subgroupCongr hRI).toMonoidHom.comp
    ((φ.toMonoidHom.comp π).subgroupMap I₀) with hρ
  have hρs : Function.Surjective ρ :=
    (MulEquiv.subgroupCongr hRI).surjective.comp
      ((φ.toMonoidHom.comp π).subgroupMap_surjective I₀)
  have hρker : ∀ i : I₀, ρ i = 1 ↔ (i : L) ∈ N := by
    intro i
    constructor
    · intro h
      have h1 := congrArg Subtype.val h
      change φ (π i) = 1 at h1
      rw [MulEquiv.map_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    · intro h
      apply Subtype.ext
      change φ (π i) = 1
      rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr h, map_one]
  have hRq : IsQuasisimple R := KFacts.isQuasisimple_of_isSLThreePiAt_two_pow (by omega) hRSL
  have hRZ : Nat.card (Subgroup.center R) = 3 :=
    Sec13.Res5Proof.card_center_of_isSLThreePiAt Nat.prime_two (by omega) hRSL
  have hRZ3 : IsPGroup 3 (Subgroup.center R) := IsPGroup.of_card (n := 1) (by rw [hRZ, pow_one])
  have hθR : aschbacherSolvableCore 3 R = ⊥ :=
    Sec13.aschbacherSolvableCore_eq_bot_of_isQuasisimple hRq hRZ3
  let ι : ρ.ker →* N := {
    toFun := fun k => ⟨((k : I₀) : L), (hρker k).mp k.2⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun k₁ k₂ h => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : N => (z : L)) h
  have hks : Group.IsSolvable ρ.ker := by
    have := hNsol
    exact Group.isSolvable_of_isSolvable_injective hι
  have hk3 : ¬ 3 ∣ Nat.card ρ.ker := fun h => hN3 (h.trans (Subgroup.card_dvd_of_injective ι hι))
  have hθI₀ := theta_eq_ker_of_surjective ρ hρs hθR hks hk3
  let eI₀ : I₀ ⧸ aschbacherSolvableCore 3 I₀ ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hθI₀).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)
  set I := I₀.map L.subtype with hIdef
  let eI : I₀ ≃* I := I₀.equivMapOfInjective L.subtype L.subtype_injective
  let eIbar : lBar I ≃* R := (Sec14.quotThetaEquiv eI).symm.trans eI₀
  have hISL : Sec4.IsSLThreePiAt (lBar I) (2 ^ n) := Sec9.isSLThreePiAt_of_mulEquiv eIbar.symm hRSL
  have hIZ : Nat.card (Subgroup.center (lBar I)) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr eIbar).toEquiv, hRZ]
  have hIL : I ≤ L := Subgroup.map_subtype_le _
  have hI₀CL : I₀ ≤ CL := Subgroup.map_subtype_le _
  have hIC : ∀ y ∈ I, y * b = b * y := by
    rintro _ ⟨z, hz, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hI₀CL hz)
    exact congrArg Subtype.val h
  have hbI : b ∈ I := by
    have hxR' : x ∈ I₀.map (φ.toMonoidHom.comp π) := hRI ▸ hxR
    obtain ⟨i, hi, hix⟩ := hxR'
    have h1 : π i = π β := φ.injective hix
    have h2 : i⁻¹ * β ∈ N := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      exact h1
    have hcomm : Commute β (i⁻¹ * β) := by
      have hiβ : i * β = β * i := Subgroup.mem_centralizer_singleton_iff.mp (hI₀CL hi)
      have hc : Commute β i := hiβ.symm
      exact (hc.inv_right).mul_right (Commute.refl β)
    have hord : Nat.Coprime (orderOf (i⁻¹ * β)) 3 := by
      have h3 := orderOf_dvd_natCard (⟨i⁻¹ * β, h2⟩ : N)
      rw [Subgroup.orderOf_mk] at h3
      exact Nat.Coprime.coprime_dvd_left h3
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3))
    have hβi : β ∈ Subgroup.zpowers i :=
      mem_zpowers_of_eq_mul (Subtype.ext (by simpa using hb3)) (by group) hcomm hord
    exact ⟨β, (Subgroup.zpowers_le.mpr hi) hβi, rfl⟩
  have hbCI : b ∈ Subgroup.centralizer (I : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => hIC y hy
  have hImem : I ∈ thetaComponentsIn
      (Subgroup.centralizer ((Subgroup.closure {c, b} : Subgroup G) : Set G)) := by
    set CB := Subgroup.centralizer ((Subgroup.closure {c, b} : Subgroup G) : Set G) with hCBdef
    have hcC : ∀ y ∈ L, y * c = c * y := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLCc hy)
    have hmemCB : ∀ y : G, y * c = c * y → y * b = b * y → y ∈ CB := by
      intro y hyc hyb
      rw [hCBdef, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro g hg
      rcases hg with rfl | rfl
      · exact hyc.symm
      · exact hyb.symm
    have hICB : I ≤ CB := fun y hy => hmemCB y (hcC y (hIL hy)) (hIC y hy)
    have hCBc : CB ≤ Subgroup.centralizer ({c} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hy c (Subgroup.subset_closure (by simp))).symm
    have hCBb : CB ≤ Subgroup.centralizer ({b} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hy b (Subgroup.subset_closure (by simp))).symm
    set X := L ⊓ Subgroup.centralizer ({b} : Set G) with hXdef
    have hCLX : CL.map L.subtype = X := by
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_inf, hXdef, hCL,
        Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, congrArg Subtype.val hz⟩
      · rintro ⟨hyL, hyb⟩
        exact ⟨⟨y, hyL⟩, Subtype.ext hyb, rfl⟩
    have hIX : I = inSubgroup perfectResidual X := by
      rw [hIdef, hI₀, ← Sec18.inSubgroup_perfectResidual_map L.subtype L.subtype_injective, hCLX]
    refine mem_thetaComponentsIn_iff.mpr ⟨hICB, ?_, ?_, ?_⟩
    ·
      let e : I.subgroupOf CB ≃* I₀ := (Subgroup.subgroupOfEquivOfLe hICB).trans eI.symm
      have : Group.IsPerfect (perfectResidual CL) :=
        (CFSG.perfect_residual_characterization (G := CL)).2.2.1
      have hI₀p : Group.IsPerfect I₀ := Group.IsPerfect.ofSurjective
        (f := ((perfectResidual CL).equivMapOfInjective CL.subtype
          CL.subtype_injective).toMonoidHom)
        (MulEquiv.surjective _)
      exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    ·
      have hXsn : (X.subgroupOf CB).IsSubnormal := by
        have heq : X.subgroupOf CB = (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).comap
            (Subgroup.inclusion hCBc) := by
          rw [Subgroup.comap_inclusion_subgroupOf]
          ext y
          simp only [hXdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
          exact ⟨fun h => h.1, fun h => ⟨h, hCBb y.2⟩⟩
        rw [heq]
        exact hL'.2.1.comap _
      have hIXle : I ≤ X := hIX ▸ Subgroup.map_subtype_le _
      refine Subgroup.IsSubnormal.step _ (X.subgroupOf CB) (fun y hy => hIXle hy) hXsn ?_
      rw [Subgroup.normal_subgroupOf_iff (show I.subgroupOf CB ≤ X.subgroupOf CB from
        fun y hy => hIXle hy)]
      intro h k hh hk
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      rw [hIX] at hh ⊢
      exact RankThree.GroupTheory.conj_mem_inSubgroup_perfectResidual
        (Subgroup.mem_subgroupOf.mp hk) hh
    ·
      let e : I.subgroupOf CB ≃* I := Subgroup.subgroupOfEquivOfLe hICB
      exact LocalCores.isQuasisimple_of_mulEquiv ((Sec14.quotThetaEquiv e).trans eIbar).symm hRq
  have hθGI : ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) I, ∃ ht : t ∈ L,
      (⟨t, ht⟩ : L) ∈ N := by
    rintro _ ⟨t', ht', rfl⟩
    have hmap := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eI
    rw [← hmap, hθI₀] at ht'
    obtain ⟨t'', ht''ker, rfl⟩ := ht'
    exact ⟨((t'' : I₀) : L).2, (hρker t'').mp ht''ker⟩
  have hα : A ⊓ L ⊓ Sec4.thetaQuotCentralizer I ≤ Subgroup.zpowers b := by
    intro d hd
    obtain ⟨⟨hdA, hdL⟩, hdC⟩ := hd
    obtain ⟨-, hdθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hdC
    set δ : L := ⟨d, hdL⟩ with hδ
    have hcent : R ≤ Subgroup.centralizer ({φ (π δ)} : Set (projSU 4 2 n)) := by
      rw [← hRI]
      rintro _ ⟨i, hi, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hiI : ((i : L) : G) ∈ I := ⟨i, hi, rfl⟩
      obtain ⟨hmL, hmN⟩ := hθGI _ (hdθ _ hiI)
      have he : (⟨((i : L) : G)⁻¹ * (d * (i : L) * d⁻¹), hmL⟩ : L) = i⁻¹ * (δ * i * δ⁻¹) :=
        Subtype.ext rfl
      rw [he] at hmN
      have h1 : π (i⁻¹ * (δ * i * δ⁻¹)) = 1 := by
        rw [hπ, QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr hmN
      have h2 : π δ * π i = π i * π δ := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
        have h3 : (π i)⁻¹ * (π δ * π i * (π δ)⁻¹) * π δ = π δ := by rw [h1, one_mul]
        calc π δ * π i = π i * ((π i)⁻¹ * (π δ * π i * (π δ)⁻¹) * π δ) := by group
          _ = π i * π δ := by rw [h3]
      change φ (π i) * φ (π δ) = φ (π δ) * φ (π i)
      have h3 := congrArg φ h2
      rw [map_mul, map_mul] at h3
      exact h3.symm
    have hmemE : φ (π δ) ∈ (((A ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L))).map φ.toMonoidHom :=
      ⟨π δ, ⟨δ, Subgroup.mem_subgroupOf.mpr ⟨hdA, hdL⟩, rfl⟩, rfl⟩
    have hz0 := hα' _ hmemE hcent
    have hz : φ (π δ) ∈ (Subgroup.zpowers β).map (φ.toMonoidHom.comp π) := by
      rw [MonoidHom.map_zpowers]
      exact hz0
    obtain ⟨z, hz, hzδ⟩ := hz
    have hzN : z⁻¹ * δ ∈ N := by
      have h1 : π z = π δ := φ.injective hzδ
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      exact h1
    have hz3 : (z⁻¹ * δ) ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      apply Subtype.ext
      have hbk : b ^ k ∈ A := A.zpow_mem hbA k
      have hm : (b ^ k)⁻¹ * d ∈ A := A.mul_mem (A.inv_mem hbk) hdA
      simpa using hAe0.2 _ hm
    have h1 := eq_one_of_pow_three_of_mem hN3 hzN hz3
    have hzd : z = δ := inv_mul_eq_one.mp h1
    have hdz : (δ : G) = d := rfl
    rw [← hdz, ← hzd]
    have hzb := Subgroup.mem_map_of_mem L.subtype hz
    rw [MonoidHom.map_zpowers] at hzb
    exact hzb

  obtain ⟨_, ⟨ξ, hξB, rfl⟩, rfl⟩ := hy'E
  set Φ : L →* projSU 4 2 n := φ.toMonoidHom.comp π with hΦ
  have hξB' : (ξ : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hξB
  have hBI₀ : ∀ (δ : L), (δ : G) ∈ A ⊓ L → δ ∈ Subgroup.normalizer (I₀ : Set L) := by
    intro δ hδ
    have hδCL : δ ∈ CL := by
      rw [hCL, Subgroup.mem_centralizer_singleton_iff]
      have e := congrArg Subtype.val (hAe0.1.is_comm.comm ⟨δ, hδ.1⟩ ⟨b, hbA⟩)
      exact Subtype.ext e
    exact GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual CL
      (Subgroup.le_normalizer hδCL)
  have hBN : A ⊓ L ≤ Subgroup.normalizer (I : Set G) := by
    intro d hd
    apply GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq
    have hsq : (MulAut.conj d).toMonoidHom.comp L.subtype =
        L.subtype.comp (MulAut.conj (⟨d, hd.2⟩ : L)).toMonoidHom := by
      ext g
      rfl
    rw [hIdef, Subgroup.map_map, hsq, ← Subgroup.map_map,
      GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer (hBI₀ ⟨d, hd.2⟩ hd)]
  have hξI₀ : ξ ∈ Subgroup.normalizer (I₀ : Set L) := hBI₀ ξ hξB'
  set J₀ := I₀ ⊓ Ubar.comap Φ with hJ₀
  have hξJ : ξ ∈ Subgroup.normalizer (J₀ : Set L) := by
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hξI₀, ?_⟩
    show ξ ∈ Subgroup.normalizer ((Ubar.comap Φ : Subgroup L) : Set L)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hyN (Φ g)
  have hJ3 : ¬ 3 ∣ Nat.card J₀ := by
    intro h3
    obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' (G := J₀) 3 h3
    have hjL : orderOf (j : L) = 3 := by rw [Subgroup.orderOf_coe, hj]
    have hΦj : Φ (j : L) ∈ Ubar := j.2.2
    have hΦj1 : Φ (j : L) = 1 := by
      obtain ⟨k, hk⟩ := hU2 ⟨Φ (j : L), hΦj⟩
      have h1 : Φ (j : L) ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have h2 : Φ (j : L) ^ 3 = 1 := by rw [← map_pow, ← hjL, pow_orderOf_eq_one, map_one]
      have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2))
    have hπj : π (j : L) = 1 := (MulEquiv.map_eq_one_iff φ).mp hΦj1
    have hjN : (j : L) ∈ N := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπj
      exact hπj
    have hdvd := orderOf_dvd_natCard (⟨(j : L), hjN⟩ : N)
    rw [Subgroup.orderOf_mk, hjL] at hdvd
    exact hN3 hdvd
  have hξ3 : ξ ^ 3 = 1 := Subtype.ext (by simpa using hAe0.2 _ hξB'.1)
  have hzp3 : IsPGroup 3 (Subgroup.zpowers ξ) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hξ3)
  have hzle : Subgroup.zpowers ξ ≤ Subgroup.normalizer (J₀ : Set L) :=
    Subgroup.zpowers_le.mpr hξJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime 3 2
    hzp3 hJ3 (J₀.normalizerMonoidHom.comp (Subgroup.inclusion hzle))
  set U' : Subgroup G := ((S : Subgroup J₀).map J₀.subtype).map L.subtype with hU'
  have hU'I : U' ≤ I := by
    rw [hU', hIdef]
    exact Subgroup.map_mono ((Subgroup.map_subtype_le _).trans inf_le_left)
  have hU'2 : IsPGroup 2 U' := (S.isPGroup'.map _).map _
  have hξU' : (ξ : G) ∈ Subgroup.normalizer (U' : Set G) := by
    apply GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq
    have hS1 := hS ⟨ξ, Subgroup.mem_zpowers ξ⟩
    have hcomm : ((MulAut.conj (ξ : G)).toMonoidHom.comp L.subtype).comp J₀.subtype =
        (L.subtype.comp J₀.subtype).comp
          ((J₀.normalizerMonoidHom.comp (Subgroup.inclusion hzle))
            ⟨ξ, Subgroup.mem_zpowers ξ⟩).toMonoidHom := by
      ext j
      rfl
    rw [hU', Subgroup.map_map, Subgroup.map_map, hcomm, ← Subgroup.map_map, hS1,
      Subgroup.map_map]
  have hΦJ : ∀ w ∈ Ubar, ∃ j : J₀, Φ (j : L) = w := by
    intro w hw
    have hwR : w ∈ R := hUR hw
    rw [← hRI] at hwR
    obtain ⟨i, hi, hiw⟩ := hwR
    refine ⟨⟨i, hi, ?_⟩, hiw⟩
    show Φ i ∈ Ubar
    rw [show Φ i = w from hiw]
    exact hw
  let ψ : J₀ →* Ubar := (Φ.comp J₀.subtype).codRestrict Ubar (fun j => j.2.2)
  have hψs : Function.Surjective ψ := fun w => by
    obtain ⟨j, hj⟩ := hΦJ w w.2
    exact ⟨j, Subtype.ext hj⟩
  have hSψ : (S : Subgroup J₀).map ψ = ⊤ := by
    have h1 : ((S : Subgroup J₀).map ψ).index ∣ (S : Subgroup J₀).index :=
      Subgroup.index_map_dvd _ hψs
    have h2 : ¬ 2 ∣ (S : Subgroup J₀).index := S.not_dvd_index
    have h3 : ((S : Subgroup J₀).map ψ).index ∣ Nat.card Ubar := Subgroup.index_dvd_card _
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU2
    rw [hk] at h3
    obtain ⟨m, -, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    rw [← Subgroup.index_eq_one]
    rcases m with _ | m
    · simpa using hm'
    · exfalso
      apply h2
      rw [hm'] at h1
      exact (dvd_pow_self 2 (Nat.succ_ne_zero m)).trans h1
  refine ⟨b, hbAL, hb1, I, hIL, hImem, inSubgroup_pCore_eq hbI hbCI hb3 hb1 hIZ, ⟨n, hn, hISL⟩,
    hBN, hα, ξ, hξB', U', hU'I, hU'2, hξU', fun hle => ?_⟩
  apply hyC
  intro w hw
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨s, hs, hsw⟩ : ∃ s ∈ (S : Subgroup J₀), ψ s = ⟨w, hw⟩ := by
    have : (⟨w, hw⟩ : Ubar) ∈ (S : Subgroup J₀).map ψ := hSψ ▸ Subgroup.mem_top _
    exact this
  have hsU : (((s : J₀) : L) : G) ∈ U' := ⟨(s : L), ⟨s, hs, rfl⟩, rfl⟩
  have hc := hle (Subgroup.commutator_mem_commutator hsU (Subgroup.mem_zpowers (ξ : G)))
  obtain ⟨hcL, hcN⟩ := hθGI _ hc
  have he : (⟨⁅(((s : J₀) : L) : G), (ξ : G)⁆, hcL⟩ : L) = ⁅((s : J₀) : L), ξ⁆ :=
    Subtype.ext rfl
  rw [he] at hcN
  have h1 : Φ ⁅((s : J₀) : L), ξ⁆ = 1 := by
    rw [hΦ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff _).mpr hcN, map_one]
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  have hw' : Φ ((s : J₀) : L) = w := congrArg Subtype.val hsw
  rw [hw'] at h1
  exact h1

end CFSG.RankThree.PartTwo.Sec21
