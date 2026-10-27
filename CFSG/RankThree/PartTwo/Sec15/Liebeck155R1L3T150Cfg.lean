module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150Defs
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Pump
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsAssembly
import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwo
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofCases
import CFSG.RankThree.PartTwo.Sec19.RonanCensus1915ImageCfg
import CFSG.RankThree.PartTwo.Sec14.Item148StepFieldTypes
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.LocalRank

@[expose] noncomputable def imageS {Y : Type} [Group Y] (Λ L : Subgroup Y) :
    Subgroup (Liebeck155R1T150.Pump.ThetaCenterQuot Λ) :=
  ((L.subgroupOf Λ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Λ))).map
    (QuotientGroup.mk' (Subgroup.center (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ)))

private theorem isSimpleGroup_of_isoLThreePi {X : Type} [Group X] [Group.IsPerfect X] {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e) (h : Sec4.IsoLThreePi X p e) : IsSimpleGroup X := by
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have := Sec4.Item462AltProof.isSimpleGroup_projSL_three (GaloisField p e)
    exact φ.isSimpleGroup
  · by_cases hpe : p ^ e = 2
    · obtain ⟨hp2, he1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hpe
      subst hp2 he1
      exfalso
      have := Sec12.Hering129L.OTwo.nontrivial_projSU_three_two_one
      have : Nontrivial X := φ.toEquiv.nontrivial
      have := Sec13.isSolvable_projSU_two
      exact Group.IsPerfect.not_isSolvable X
        (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
    · have := Sec4.Item462AltProof.isSimpleGroup_projSU_three p e he hpe
      exact φ.isSimpleGroup

section Core

variable {Y : Type} [Group Y] [Finite Y]

theorem cfgS429_type_of_acts {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y)
    {A : Subgroup Y} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (Λ : Set Y))
    {c : Y} (hcA : c ∈ A) (hc : c ∉ Sec4.thetaQuotCentralizer Λ)
    {L : Subgroup Y} (hL : L ∈ thetaComponentsAt 3 c) (hLΛ : L ≤ Λ)
    (hAL : A ≤ Subgroup.normalizer (L : Set Y)) (hAL9 : Nat.card ↥(A ⊓ L) = 9)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hJ : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L) :
    Sec4.RonanK429.CfgS429 (Liebeck155R1T150.Pump.ThetaCenterQuot Λ)
      ((A.subgroupOf (Subgroup.normalizer (Λ : Set Y))).map (Liebeck155R1T150.Pump.actOnS Λ))
      (Liebeck155R1T150.Pump.actOnS Λ ⟨c, hAN hcA⟩) (imageS Λ L) ∧
    IsSimpleGroup (↥(imageS Λ L) ⧸ CFSG.pCore 2 ↥(imageS Λ L)) ∧
    Sec4.IsoLThreePi (↥(imageS Λ L) ⧸ CFSG.pCore 2 ↥(imageS Λ L)) p e := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (Λ : Set Y) with hN
  have hΛN : Λ ≤ N := Subgroup.le_normalizer
  set θΛ := aschbacherSolvableCore 3 ↥Λ with hθΛ
  let πS : ↥Λ →* Liebeck155R1T150.Pump.ThetaCenterQuot Λ :=
    (QuotientGroup.mk' (Subgroup.center (↥Λ ⧸ θΛ))).comp (QuotientGroup.mk' θΛ)
  let ρ := Liebeck155R1T150.Pump.actOnS Λ
  have hρapp : ∀ (x : ↥N) (l : ↥Λ), ρ x (πS l) = πS (Λ.normalizerMonoidHom x l) :=
    fun x l => rfl
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hcN : c ∈ N := hAN hcA
  obtain ⟨hLc, hLsub, hLperf⟩ := Sylow155R3.Thm90.thetaComponentsAt_facts hL
  have : Group.IsPerfect ↥L := hLperf
  have hJp : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
      (QuotientGroup.mk'_surjective _)
  have hJs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := isSimpleGroup_of_isoLThreePi he hJ
  have hcfg := Liebeck155R1T150.Pump.config_of_component hJs hL (MulEquiv.refl _) hΛ hcN hc3 hc hLΛ
  have hmemK : ∀ l : ↥L, πS (Subgroup.inclusion hLΛ l) ∈ imageS Λ L := by
    intro l
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' θΛ (Subgroup.inclusion hLΛ l),
      Subgroup.mem_map.mpr ⟨Subgroup.inclusion hLΛ l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩, rfl⟩
  let ψ : ↥L →* ↥(imageS Λ L) :=
    (πS.comp (Subgroup.inclusion hLΛ)).codRestrict (imageS Λ L) hmemK
  have hψs : Function.Surjective ψ := by
    rintro ⟨k, hk⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hk
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    exact ⟨⟨(v : Y), Subgroup.mem_subgroupOf.mp hv⟩, Subtype.ext rfl⟩
  have hπS : Function.Surjective πS :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hinner : ∀ (x : Y) (hx : x ∈ Λ), ρ ⟨x, hΛN hx⟩ = MulAut.conj (πS ⟨x, hx⟩) := by
    intro x hx
    ext t : 1
    obtain ⟨l, rfl⟩ := hπS t
    rw [hρapp, MulAut.conj_apply]
    have h1 : Λ.normalizerMonoidHom ⟨x, hΛN hx⟩ l = ⟨x, hx⟩ * l * ⟨x, hx⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
  have : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hJs
  have hKperf : Group.IsPerfect ↥(imageS Λ L) := hcfg.perfect
  have hKnt : Nontrivial ↥(imageS Λ L) := by
    obtain ⟨N', _, ⟨f⟩⟩ := hcfg.quotient
    have := hJs.toNontrivial
    have : Nontrivial (↥(imageS Λ L) ⧸ N') := f.toEquiv.nontrivial
    exact (QuotientGroup.mk'_surjective N').nontrivial
  have hLs2 : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (QuotientGroup.quotientMulEquivOfEq hθ.symm).isSimpleGroup
  have hcomap : (CFSG.pCore 2 ↥(imageS Λ L)).comap ψ = CFSG.pCore 2 ↥L :=
    Sec19.Census1915ImageProof.comap_pCore_eq_of_surjective_of_perfect ψ hψs hKperf hLs2
  let eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(imageS Λ L) ⧸ CFSG.pCore 2 ↥(imageS Λ L) :=
    Sec19.Census1915ImageProof.quotientPCoreEquivOfPerfect ψ hψs hKperf hLs2
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
    Liebeck155R1T150.Pump.center_eq_bot_of_simple hJs hJp
  have hLθ : ∀ l : ↥L, (∀ m : ↥L, ψ (l * m * l⁻¹ * m⁻¹) ∈ CFSG.pCore 2 ↥(imageS Λ L)) →
      l ∈ aschbacherSolvableCore 3 ↥L := by
    intro l hl
    have hmk : (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∈
        Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      have h1 : l * m * l⁻¹ * m⁻¹ ∈ CFSG.pCore 2 ↥L := by
        rw [← hcomap]
        exact hl m
      rw [← hθ] at h1
      have h2 := (QuotientGroup.eq_one_iff _).mpr h1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv] at h2
      have h3 := mul_inv_eq_one.mp h2
      calc (m : ↥L ⧸ aschbacherSolvableCore 3 ↥L) * l
          = ((l : ↥L ⧸ aschbacherSolvableCore 3 ↥L) * m * (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L)⁻¹)
              * l := by rw [h3]
        _ = l * m := by group
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmk
    exact hmk
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hLcomm : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
  have hALΛ : A ⊓ L ≤ Λ := inf_le_right.trans hLΛ
  have hb1 : ∀ (b : Y) (hb : b ∈ A ⊓ L),
      (∀ m : ↥L, ψ (⟨b, hb.2⟩ * m * ⟨b, hb.2⟩⁻¹ * m⁻¹) ∈ CFSG.pCore 2 ↥(imageS Λ L)) → b = 1 := by
    intro b hb h
    have hθb := hLθ ⟨b, hb.2⟩ h
    have hb3 : b ^ 3 = 1 := hA.2 b hb.1
    let k : ↥(aschbacherSolvableCore 3 ↥L) := ⟨⟨b, hb.2⟩, hθb⟩
    have hk3 : k ^ 3 = 1 := Subtype.ext (Subtype.ext (by simpa using hb3))
    have hko : orderOf k ∣ 3 := orderOf_dvd_of_pow_eq_one hk3
    rcases (Nat.dvd_prime Nat.prime_three).mp hko with h' | h'
    · have := orderOf_eq_one_iff.mp h'
      exact congrArg (fun x : ↥(aschbacherSolvableCore 3 ↥L) => ((x : ↥L) : Y)) this
    · exact absurd (h' ▸ orderOf_dvd_natCard k) three_not_dvd_card_aschbacherSolvableCore
  have hcL : c ∉ A ⊓ L := by
    intro hcAL
    have hc1 : c = 1 := by
      refine hb1 c hcAL fun m => ?_
      have : (⟨c, hcAL.2⟩ : ↥L) * m * (⟨c, hcAL.2⟩ : ↥L)⁻¹ * m⁻¹ = 1 :=
        Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
          rw [← hLcomm m m.2]
          group)
      rw [this, map_one]
      exact Subgroup.one_mem _
    exact hc (hc1 ▸ (Sec4.thetaQuotCentralizer Λ).one_mem)
  have hnormAL : ∀ x ∈ A,
      Subgroup.zpowers x ≤ Subgroup.normalizer ((A ⊓ L : Subgroup Y) : Set Y) := by
    intro x hx
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      hcommA a (Subgroup.mem_inf.mp ha).1 x hx)
  have hgen : ∀ x ∈ A, x ∉ A ⊓ L → (A ⊓ L) ⊔ Subgroup.zpowers x = A := by
    intro x hxA hxL
    have hDA : (A ⊓ L) ⊔ Subgroup.zpowers x ≤ A := sup_le inf_le_left (Subgroup.zpowers_le.mpr hxA)
    have h9 : 9 ∣ Nat.card ↥((A ⊓ L) ⊔ Subgroup.zpowers x) :=
      hAL9 ▸ Subgroup.card_dvd_of_le le_sup_left
    have h27 : Nat.card ↥((A ⊓ L) ⊔ Subgroup.zpowers x) ∣ 27 :=
      hA27 ▸ Subgroup.card_dvd_of_le hDA
    have hne : Nat.card ↥((A ⊓ L) ⊔ Subgroup.zpowers x) ≠ 9 := by
      intro h
      have h' := Subgroup.eq_of_le_of_card_ge (le_sup_left : A ⊓ L ≤ (A ⊓ L) ⊔ Subgroup.zpowers x)
        (by rw [h, hAL9])
      exact hxL (h' ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    have hD27 : Nat.card ↥((A ⊓ L) ⊔ Subgroup.zpowers x) = 27 := by
      generalize Nat.card ↥((A ⊓ L) ⊔ Subgroup.zpowers x) = d at h9 h27 hne
      have hle : d ≤ 27 := Nat.le_of_dvd (by norm_num) h27
      interval_cases d <;> omega
    exact Subgroup.eq_of_le_of_card_ge hDA (by rw [hD27, hA27])
  have hAeq : (A ⊓ L) ⊔ Subgroup.zpowers c = A := hgen c hcA hcL
  let cN : ↥N := ⟨c, hcN⟩
  have hdec : ∀ a ∈ A.subgroupOf N, ∃ (b : Y) (hb : b ∈ A ⊓ L) (k : ℤ),
      a = (⟨b, hΛN (hALΛ hb)⟩ : ↥N) * cN ^ k := by
    intro a ha
    have haD : (a : Y) ∈ (((A ⊓ L) ⊔ Subgroup.zpowers c : Subgroup Y) : Set Y) := by
      rw [SetLike.mem_coe, hAeq]
      exact Subgroup.mem_subgroupOf.mp ha
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hnormAL _ hcA)] at haD
    obtain ⟨b, hb, w, hw, hbw⟩ := Set.mem_mul.mp haD
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨b, hb, k, ?_⟩
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_zpow]; exact hbw.symm)
  let σ : MulAut (Liebeck155R1T150.Pump.ThetaCenterQuot Λ) := ρ cN
  have hfixk : ∀ (k : ℤ) (y : Liebeck155R1T150.Pump.ThetaCenterQuot Λ), σ y = y →
      (σ ^ k) y = y := by
    intro k y hy
    have hmem : σ ∈ MulAction.stabilizer (MulAut (Liebeck155R1T150.Pump.ThetaCenterQuot Λ)) y := hy
    exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpow_mem _ hmem k)
  have hσfix : ∀ y ∈ imageS Λ L, σ y = y := fun y hy => hcfg.fixed y hy
  have hact : ∀ (b : Y) (hb : b ∈ A ⊓ L) (k : ℤ) (y : Liebeck155R1T150.Pump.ThetaCenterQuot Λ),
      y ∈ imageS Λ L → ρ ((⟨b, hΛN (hALΛ hb)⟩ : ↥N) * cN ^ k) y =
        πS ⟨b, hALΛ hb⟩ * y * (πS ⟨b, hALΛ hb⟩)⁻¹ := by
    intro b hb k y hy
    rw [map_mul, map_zpow, MulAut.mul_apply, hfixk k y (hσfix y hy), hinner b (hALΛ hb),
      MulAut.conj_apply]
  have hbk : ∀ (b : Y) (hb : b ∈ A ⊓ L) (k : ℤ),
      (∀ y ∈ imageS Λ L, ρ ((⟨b, hΛN (hALΛ hb)⟩ : ↥N) * cN ^ k) y * y⁻¹ ∈
        CFSG.Open.pCoreOf 2 (imageS Λ L)) → b = 1 := by
    intro b hb k h
    refine hb1 b hb fun m => ?_
    have h1 := h (ψ m) (ψ m).2
    rw [hact b hb k _ (ψ m).2] at h1
    rw [← CFSG.mem_openPCoreOf_iff]
    convert h1 using 1
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  have hσ3 : σ ^ 3 = 1 := hcfg.pow_three
  have hσ1 : σ ≠ 1 := hcfg.ne_one
  have hordσ : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hcN3 : cN ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hAinj : ∀ a ∈ A.subgroupOf N, ρ a = 1 → a = 1 := by
    intro a ha h1
    obtain ⟨b, hb, k, rfl⟩ := hdec a ha
    have hb1' : b = 1 := hbk b hb k (fun y _ => by
      rw [h1, MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _)
    subst hb1'
    have hσk : σ ^ k = 1 := by
      have : ρ ((⟨1, hΛN (hALΛ hb)⟩ : ↥N) * cN ^ k) = σ ^ k := by
        rw [map_mul, map_zpow]
        have : (⟨1, hΛN (hALΛ hb)⟩ : ↥N) = 1 := rfl
        rw [this, map_one, one_mul]
      rw [← this]
      exact h1
    have h3 : (3 : ℤ) ∣ k := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr hσk
      rwa [hordσ] at this
    obtain ⟨j, rfl⟩ := h3
    have : (⟨1, hΛN (hALΛ hb)⟩ : ↥N) = 1 := rfl
    rw [this, one_mul, zpow_mul]
    simp [hcN3]
  have hE27 : Late.IsE27 ((A.subgroupOf N).map ρ) := by
    refine ⟨?_, ?_⟩
    · refine CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 ρ _ ⟨⟨⟨fun a b => ?_⟩⟩,
        fun x hx => ?_⟩
      · exact Subtype.ext (Subtype.ext (hcommA _ (Subgroup.mem_subgroupOf.mp a.2) _
          (Subgroup.mem_subgroupOf.mp b.2)))
      · exact Subtype.ext (by simpa using hA.2 _ (Subgroup.mem_subgroupOf.mp hx))
    · have hinj : Function.Injective (ρ.subgroupMap (A.subgroupOf N)) := by
        intro x y hxy
        have h1 : ρ ((x : ↥N)⁻¹ * (y : ↥N)) = 1 := by
          rw [map_mul, map_inv, inv_mul_eq_one]
          exact congrArg Subtype.val hxy
        have hmem : (x : ↥N)⁻¹ * (y : ↥N) ∈ A.subgroupOf N :=
          (A.subgroupOf N).mul_mem ((A.subgroupOf N).inv_mem x.2) y.2
        exact Subtype.ext (inv_mul_eq_one.mp (hAinj _ hmem h1))
      rw [← Nat.card_congr (Equiv.ofBijective _
        ⟨hinj, MonoidHom.subgroupMap_surjective ρ (A.subgroupOf N)⟩),
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hA27]
  have hKtype : Sec4.IsoLThreePi (↥(imageS Λ L) ⧸ CFSG.pCore 2 ↥(imageS Λ L)) p e := by
    have hI1 : Sec4.IsoLThreePi (↥L ⧸ CFSG.pCore 2 ↥L) p e :=
      Sec4.RonanK429.isoLThreePi_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hθ.symm) hJ
    exact Sec4.RonanK429.isoLThreePi_of_mulEquiv eL.symm hI1
  have hKs : IsSimpleGroup (↥(imageS Λ L) ⧸ CFSG.pCore 2 ↥(imageS Λ L)) := eL.symm.isSimpleGroup
  refine ⟨?_, hKs, hKtype⟩
  have hfs : Sylow155R3.Thm90.fixedSubgroup σ = Sec4.autFix σ := Subgroup.ext fun _ => Iff.rfl
  exact
    { isE27 := hE27
      mem := Subgroup.mem_map.mpr ⟨cN, Subgroup.mem_subgroupOf.mpr hcA, rfl⟩
      ne_one := hσ1
      le_autFix := fun x hx => hσfix x hx
      isSubnormal := by
        have h := hcfg.subnormal
        rw [hfs] at h
        exact h
      isPerfect := hKperf
      map_mem := by
        intro x hx y hy
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
        obtain ⟨m, hm⟩ := hψs ⟨y, hy⟩
        have hya : y = πS ⟨(m : Y), hLΛ m.2⟩ := congrArg Subtype.val hm.symm
        rw [hya, hρapp a ⟨(m : Y), hLΛ m.2⟩]
        have haA : (a : Y) ∈ A := Subgroup.mem_subgroupOf.mp ha
        have hamL : (a : Y) * (m : Y) * (a : Y)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hAL haA) m).mp m.2
        exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' θΛ (Λ.normalizerMonoidHom a ⟨m, hLΛ m.2⟩),
          Subgroup.mem_map.mpr ⟨Λ.normalizerMonoidHom a ⟨m, hLΛ m.2⟩,
            Subgroup.mem_subgroupOf.mpr hamL, rfl⟩, rfl⟩
      isType := Or.inl ⟨p, e, inferInstance, he, hKtype⟩
      faithful := by
        intro x hx hxK
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
        obtain ⟨b, hb, k, rfl⟩ := hdec a ha
        have hb1' : b = 1 := hbk b hb k hxK
        subst hb1'
        rw [map_mul, map_zpow]
        have : (⟨1, hΛN (hALΛ hb)⟩ : ↥N) = 1 := rfl
        rw [this, map_one, one_mul]
        exact Subgroup.zpow_mem_zpowers σ k }

theorem cfgS429_of_acts {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y)
    {A : Subgroup Y} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (Λ : Set Y))
    {c : Y} (hcA : c ∈ A) (hc : c ∉ Sec4.thetaQuotCentralizer Λ)
    {L : Subgroup Y} (hL : L ∈ thetaComponentsAt 3 c) (hLΛ : L ≤ Λ)
    (hAL : A ≤ Subgroup.normalizer (L : Set Y)) (hAL9 : Nat.card ↥(A ⊓ L) = 9)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hJ : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L) :
    Sec4.RonanK429.CfgS429 (Liebeck155R1T150.Pump.ThetaCenterQuot Λ)
      ((A.subgroupOf (Subgroup.normalizer (Λ : Set Y))).map (Liebeck155R1T150.Pump.actOnS Λ))
      (Liebeck155R1T150.Pump.actOnS Λ ⟨c, hAN hcA⟩) (imageS Λ L) :=
  (cfgS429_type_of_acts hΛ hA hA27 hAN hcA hc hL hLΛ hAL hAL9 he hJ hθ).1

end Core

section Rows

theorem conclS429_and_iso_of_acts (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    {Y : Type} [Group Y] [Finite Y] (hY : SectionFourHyp Y)
    {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y)
    {A : Subgroup Y} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (Λ : Set Y))
    {c : Y} (hcA : c ∈ A) (hc : c ∉ Sec4.thetaQuotCentralizer Λ)
    {L : Subgroup Y} (hL : L ∈ thetaComponentsAt 3 c) (hLΛ : L ≤ Λ)
    (hAL : A ≤ Subgroup.normalizer (L : Set Y)) (hAL9 : Nat.card ↥(A ⊓ L) = 9)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hJ : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L) :
    Sec4.RonanK429.ConclS429 (Liebeck155R1T150.Pump.ThetaCenterQuot Λ)
        (Liebeck155R1T150.Pump.actOnS Λ ⟨c, hAN hcA⟩) (imageS Λ L) ∧
      IsSimpleGroup ↥(imageS Λ L) ∧ Sec4.IsoLThreePi ↥(imageS Λ L) p e := by
  have hq : CFSG.IsQuasisimple (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ) := hΛ.2.2
  have hΛS : SectionFourHyp (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ) :=
    Sec4.Item41Narrow.sectionFourHyp_thetaQuotient h1 hY hΛ
  have hlist : Census.List42 (Liebeck155R1T150.Pump.ThetaCenterQuot Λ) :=
    Census.rank3II_4_2 _ (Sec4.Item41Narrow.sectionFourHyp_quotient_center h1 h2 hΛS hq)
      hq.2.1 hq.2.2
  obtain ⟨hcfg, hKs, hKtype⟩ :=
    cfgS429_type_of_acts hΛ hA hA27 hAN hcA hc hL hLΛ hAL hAL9 he hJ hθ
  have hrow := Sec4.RonanK429.K429RowsS.rowS_of_list42 Sec4.RonanK429.k429RowsS_holds
    hq.2.1 hq.2.2 hlist _ _ _ hcfg
  have h1' := Sec19.Census1915ImageProof.pCore_eq_bot_of_isSubnormal hcfg.isSubnormal hrow.1
  have h2' : CFSG.pCore 2 ↥(imageS Λ L) = ⊥ := by
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2
      (Subgroup.subgroupOfEquivOfLe hcfg.le_autFix), h1', Subgroup.map_bot]
  let eK : ↥(imageS Λ L) ≃* (↥(imageS Λ L) ⧸ CFSG.pCore 2 ↥(imageS Λ L)) :=
    ((QuotientGroup.quotientMulEquivOfEq h2').trans QuotientGroup.quotientBot).symm
  exact ⟨hrow, eK.isSimpleGroup, Sec4.RonanK429.isoLThreePi_of_mulEquiv eK hKtype⟩

theorem survivors_of_acts (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h44 : Sec4.Item4_4) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {Y : Type} [Group Y] [Finite Y] (hY : SectionFourHyp Y)
    {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y)
    {A : Subgroup Y} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (Λ : Set Y))
    {c : Y} (hcA : c ∈ A) (hc : c ∉ Sec4.thetaQuotCentralizer Λ)
    {L : Subgroup Y} (hL : L ∈ thetaComponentsAt 3 c) (hLΛ : L ≤ Λ)
    (hAL : A ≤ Subgroup.normalizer (L : Set Y)) (hAL9 : Nat.card ↥(A ⊓ L) = 9)
    {e : ℕ} (he : 1 ≤ e) (hJ : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 e) :
    IsSimpleGroup ↥(imageS Λ L) ∧
      (Sec4.RonanK429.SurvL3 (Liebeck155R1T150.Pump.ThetaCenterQuot Λ)
          (Liebeck155R1T150.Pump.actOnS Λ ⟨c, hAN hcA⟩) (imageS Λ L) ∨
        SurvD4 (Liebeck155R1T150.Pump.ThetaCenterQuot Λ)
          (Liebeck155R1T150.Pump.actOnS Λ ⟨c, hAN hcA⟩) (imageS Λ L)) := by
  obtain ⟨-, -, hLperf⟩ := Sylow155R3.Thm90.thetaComponentsAt_facts hL
  have hθ := Sec12.Hering129L.OTwo.theta_eq_pCore_two_of_isoLThreePi_even h44 hGA
    (Sec4.sectionFourHyp_subgroup hY L) hLperf he hJ
  obtain ⟨hconcl, hKs, hKiso⟩ :=
    conclS429_and_iso_of_acts h1 h2 hY hΛ hA hA27 hAN hcA hc hL hLΛ hAL hAL9 he hJ hθ
  refine ⟨hKs, ?_⟩
  rcases hconcl.2 with (⟨⟨φ⟩, -⟩ | hD4) | hL3
  · exact (Sec14.isEmpty_mulEquiv_a7_of_isoLThreePi_two he hKiso).elim φ
  · exact Or.inr hD4
  · exact Or.inl hL3

end Rows

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150
