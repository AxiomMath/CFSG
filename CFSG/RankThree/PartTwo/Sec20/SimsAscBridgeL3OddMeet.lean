module

public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3Odd
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL2Odd
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeHyp
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBasicsFixedSet
import CFSG.Models.PGL
public import CFSG.GH74.KGroups.L3EpsInvLin
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeSimple
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3OddInv
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3OddAut
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeSL2Comp
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L35
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U37
import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryTwoRank

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)
open scoped commutatorElement

namespace AscBridge

variable {G : Type} [Group G] [Finite G]
variable {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4} {P X : Subgroup G}

theorem exists_involution_commute_kAlpha (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    (h2 : CFSG.Open.pRank 2 (yAlpha M X T c) ≤ 2) (hD : rAlpha M X T c ⊓ yAlpha M X T c ≠ ⊥) :
    ∃ t ∈ rAlpha M X T c ⊓ yAlpha M X T c, orderOf t = 2 ∧
      ∀ k ∈ kAlpha M X T c, k * t = t * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := rAlpha M X T c ⊓ yAlpha M X T c with hDdef
  have hR2 : IsPGroup 2 (rAlpha M X T c) :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_subtype
      (K := yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map _
  have hD2 : IsPGroup 2 D := hR2.to_inf_left
  have hKR : kTwenty M c ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  haveI := yAlpha_normal hX
  have hKD : ∀ k ∈ kAlpha M X T c, ∀ d ∈ D, k * d * k⁻¹ ∈ D := by
    intro k hk d hd
    obtain ⟨k', hk', rfl⟩ := hk
    have hkN := mk_mem_normalizer_rAlpha (hKR (Subgroup.mem_subgroupOf.mp hk'))
    refine ⟨(Subgroup.mem_normalizer_iff.mp hkN d).mp hd.1, ?_⟩
    exact (inferInstance : (yAlpha M X T c).Normal).conj_mem d hd.2 _
  let E : Subgroup _ :=
    { carrier := {g | g ∈ D ∧ (∀ d ∈ D, g * d = d * g) ∧ g * g = 1}
      one_mem' := ⟨D.one_mem, fun d _ => by simp, by simp⟩
      mul_mem' := by
        rintro a b ⟨haD, haC, ha2⟩ ⟨hbD, hbC, hb2⟩
        refine ⟨D.mul_mem haD hbD, fun d hd => ?_, ?_⟩
        · rw [mul_assoc, hbC d hd, ← mul_assoc, haC d hd, mul_assoc]
        · have hab : a * b = b * a := haC b hbD
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hab]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨haD, haC, ha2⟩
        refine ⟨D.inv_mem haD, fun d hd => ?_, ?_⟩
        · have h := haC d hd
          calc a⁻¹ * d = a⁻¹ * (d * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * d) * a⁻¹ := by rw [h]
            _ = d * a⁻¹ := by group
        · rw [← mul_inv_rev, ha2, inv_one] }
  have hED : ∀ g ∈ E, g ∈ D := fun g hg => hg.1
  have hEelem : CFSG.Open.IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (x.2.2.1 y (hED _ y.2))⟩⟩, fun x hx => ?_⟩
    rw [sq]
    exact hx.2.2
  have hE2 : IsPGroup 2 E := hD2.to_le fun g hg => hg.1
  obtain ⟨n, hn⟩ := hE2.exists_card_eq
  have hEY : E ≤ yAlpha M X T c := fun g hg => (hED g hg).2
  have hnle : n ≤ 2 := (CFSG.SectionRank.le_pRank one_lt_two hEY hEelem hn).trans h2
  have hEcard : Nat.card E ≤ 4 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hnle
      _ = 4 := by norm_num
  have hE1 : ∃ t ∈ E, orderOf t = 2 := by
    haveI : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot _).mpr hD
    haveI : Nontrivial ↥(Subgroup.center ↥D) := hD2.center_nontrivial
    have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥D) := hD2.to_subgroup _
    obtain ⟨n', hn', hcard⟩ := hZ2.nontrivial_iff_card.mp inferInstance
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥D)) 2
      (hcard ▸ dvd_pow_self 2 hn'.ne')
    refine ⟨((z : ↥D) : _), ⟨(z : ↥D).2, fun d hd => ?_, ?_⟩, ?_⟩
    · have h := Subgroup.mem_center_iff.mp z.2 ⟨d, hd⟩
      exact (congrArg Subtype.val h).symm
    · have h := pow_orderOf_eq_one z
      rw [hz, sq] at h
      have h1 := congrArg Subtype.val (congrArg Subtype.val h)
      simpa using h1
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hz
  obtain ⟨t, htE, ht2⟩ := hE1
  refine ⟨t, hED t htE, ht2, ?_⟩
  have hKE : ∀ k ∈ kAlpha M X T c, ∀ g ∈ E, k * g * k⁻¹ ∈ E := by
    intro k hk g hg
    obtain ⟨hgD, hgC, hg2⟩ := hg
    refine ⟨hKD k hk g hgD, fun d hd => ?_, ?_⟩
    · have hd' : k⁻¹ * d * k ∈ D := by
        have := hKD k⁻¹ (inv_mem hk) d hd
        simpa using this
      have h := hgC _ hd'
      calc k * g * k⁻¹ * d = k * (g * (k⁻¹ * d * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * d * k) * g) * k⁻¹ := by rw [h]
        _ = d * (k * g * k⁻¹) := by group
    · calc k * g * k⁻¹ * (k * g * k⁻¹) = k * (g * g) * k⁻¹ := by group
        _ = 1 := by rw [hg2, mul_one, mul_inv_cancel]
  let ρ : ↥(kAlpha M X T c) →* Equiv.Perm ↥E :=
    { toFun := fun k =>
        { toFun := fun x => ⟨k * x * k⁻¹, hKE k k.2 x x.2⟩
          invFun := fun x => ⟨k⁻¹ * x * k, by
            have := hKE k⁻¹ (inv_mem k.2) x x.2
            simpa using this⟩
          left_inv := fun x => Subtype.ext (by simp [mul_assoc])
          right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
      map_one' := Equiv.ext fun x => Subtype.ext (by simp)
      map_mul' := fun a b => Equiv.ext fun x => Subtype.ext (by simp [mul_assoc]) }
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hKY : kTwenty M c ≤ yTwenty X c :=
    Res6.kTwenty_le_yTwenty hset (le_sup_left.trans hKTX)
  haveI hKperf : Group.IsPerfect ↥(kAlpha M X T c) := by
    haveI := isPerfect_range_kToYAlpha hset hKY
    have e₁ := (Subgroup.equivMapOfInjective _ (yAlpha M X T c).subtype
      (Subgroup.subtype_injective _)).trans (MulEquiv.subgroupCongr (map_range_kToYAlpha hKY))
    exact Group.IsPerfect.ofSurjective (f := e₁.toMonoidHom) e₁.surjective
  haveI : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  haveI : Group.IsSolvable (Equiv.Perm ↥E) := Equiv.Perm.isSolvable hEcard
  have hρ : ρ.range = ⊥ := by
    by_contra hne
    haveI : Nontrivial ρ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable ρ.range inferInstance
  intro k hk
  have hk1 : ρ ⟨k, hk⟩ = 1 := by
    have h : ρ ⟨k, hk⟩ ∈ ρ.range := ⟨_, rfl⟩
    rw [hρ, Subgroup.mem_bot] at h
    exact h
  have h := congrArg Subtype.val (Equiv.ext_iff.mp hk1 ⟨t, htE⟩)
  have h' : k * t * k⁻¹ = t := h
  calc k * t = k * t * k⁻¹ * k := by group
    _ = t * k := by rw [h']

theorem commutator_mem_kAlpha_inf_rAlpha (hset : Setting204 G A M L N c T i j P) :
    ∀ k ∈ kAlpha M X T c, ∀ r ∈ rAlpha M X T c,
      k * r * k⁻¹ * r⁻¹ ∈ kAlpha M X T c ⊓ rAlpha M X T c := by
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  have hKR : K ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hRK : R ≤ Subgroup.normalizer (K : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le Subgroup.le_normalizer
      (hset.sylow.le.trans (le_normalizer_normalClosureIn M c)))
  rintro _ ⟨k, hk, rfl⟩ _ ⟨r, hr, rfl⟩
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
  have hkR : (k : G) ∈ Subgroup.normalizer (R : Set G) := hKR hkK
  have hrK : (r : G) ∈ Subgroup.normalizer (K : Set G) := hRK hrR
  have hKmem : k * r * k⁻¹ * r⁻¹ ∈ K.subgroupOf (yTwenty X c ⊔ R) := by
    refine Subgroup.mem_subgroupOf.mpr ?_
    have e : ((k * r * k⁻¹ * r⁻¹ : ↥(yTwenty X c ⊔ R)) : G) =
        (k : G) * ((r : G) * (k : G)⁻¹ * (r : G)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact K.mul_mem hkK ((Subgroup.mem_normalizer_iff.mp hrK _).mp (K.inv_mem hkK))
  have hRmem : k * r * k⁻¹ * r⁻¹ ∈ R.subgroupOf (yTwenty X c ⊔ R) := by
    refine Subgroup.mem_subgroupOf.mpr ?_
    have e : ((k * r * k⁻¹ * r⁻¹ : ↥(yTwenty X c ⊔ R)) : G) =
        ((k : G) * (r : G) * (k : G)⁻¹) * (r : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp hkR _).mp hrR) (R.inv_mem hrR)
  simp only [← map_mul, ← map_inv]
  exact ⟨⟨_, hKmem, rfl⟩, ⟨_, hRmem, rfl⟩⟩

theorem commute_of_inf_le_centralizer (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    (h : ∀ z ∈ kAlpha M X T c ⊓ rAlpha M X T c, ∀ k ∈ kAlpha M X T c, z * k = k * z) :
    ∀ k ∈ kAlpha M X T c, ∀ r ∈ rAlpha M X T c, k * r = r * k := by
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hKY : kTwenty M c ≤ yTwenty X c :=
    Res6.kTwenty_le_yTwenty hset (le_sup_left.trans hKTX)
  haveI := yAlpha_normal hX
  have hKperf : Group.IsPerfect ↥(kAlpha M X T c) := by
    haveI := isPerfect_range_kToYAlpha hset hKY
    have e₁ := (Subgroup.equivMapOfInjective _ (yAlpha M X T c).subtype
      (Subgroup.subtype_injective _)).trans (MulEquiv.subgroupCongr (map_range_kToYAlpha hKY))
    exact Group.IsPerfect.ofSurjective (f := e₁.toMonoidHom) e₁.surjective
  have hKK : ⁅kAlpha M X T c, kAlpha M X T c⁆ = kAlpha M X T c :=
    (Subgroup.isPerfect_iff).mp hKperf
  intro k hk r hr
  have hz : ∀ a ∈ kAlpha M X T c, r⁻¹ * a * r = a * (a⁻¹ * r⁻¹ * a * r) ∧
      a⁻¹ * r⁻¹ * a * r ∈ kAlpha M X T c ⊓ rAlpha M X T c := by
    intro a ha
    refine ⟨by group, ?_⟩
    have := commutator_mem_kAlpha_inf_rAlpha hset a⁻¹ (inv_mem ha) r⁻¹ (inv_mem hr)
    simpa only [inv_inv] using this
  have hcomm : ∀ a ∈ kAlpha M X T c, ∀ b ∈ kAlpha M X T c,
      r⁻¹ * ⁅a, b⁆ * r = ⁅a, b⁆ := by
    intro a ha b hb
    obtain ⟨ea, hza⟩ := hz a ha
    obtain ⟨eb, hzb⟩ := hz b hb
    set za := a⁻¹ * r⁻¹ * a * r
    set zb := b⁻¹ * r⁻¹ * b * r
    have hzab : za * (b * zb) = (b * zb) * za :=
      h za hza _ (mul_mem hb hzb.1)
    have hzba : zb * a = a * zb := h zb hzb a ha
    calc r⁻¹ * ⁅a, b⁆ * r = ⁅r⁻¹ * a * r, r⁻¹ * b * r⁆ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅a * za, b * zb⁆ := by rw [ea, eb]
      _ = a * (za * (b * zb)) * za⁻¹ * a⁻¹ * (b * zb)⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = a * ((b * zb) * za) * za⁻¹ * a⁻¹ * (b * zb)⁻¹ := by rw [hzab]
      _ = a * b * (zb * a⁻¹) * zb⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * zb) * zb⁻¹ * b⁻¹ := by
          have : zb * a⁻¹ = a⁻¹ * zb := by
            calc zb * a⁻¹ = a⁻¹ * (a * zb) * a⁻¹ := by group
              _ = a⁻¹ * (zb * a) * a⁻¹ := by rw [hzba]
              _ = a⁻¹ * zb := by group
          rw [this]
      _ = ⁅a, b⁆ := by
          simp only [commutatorElement_def]
          group
  have hle : kAlpha M X T c ≤ Subgroup.centralizer ({r} : Set _) := by
    rw [← hKK, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e := hcomm a ha b hb
    calc ⁅a, b⁆ * r = r * (r⁻¹ * ⁅a, b⁆ * r) := by group
      _ = r * ⁅a, b⁆ := by rw [e]
  have hk' := Subgroup.mem_centralizer_singleton_iff.mp (hle hk)
  exact hk'


theorem covered_of_asc1411_pRank (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] (hnab : ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a)
    {Lm : Type} [Group Lm] (eY : ↥(yAlpha M X T c) ≃* Lm)
    (hRk : CFSG.Open.pRank 2 (rAlpha M X T c) ≤ 1)
    (h1411 : ∀ (X' : Type) [Group X'] [Finite X'] (L' S' : Subgroup X'), Hyp1411 X' L' S' →
      Nonempty (L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X')) ≃* Lm) →
      CFSG.pRank 2 ↥(S'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X'))) ≤ 1 →
      ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S' i₁).Normal ∧
        (Sec18.fourChar S' i₂).Normal) :
    CoveredByNormalizer M X T c i ∨ CoveredByNormalizer M X T c j := by
  obtain ⟨G₀, hG₀⟩ := exists_minimal_coverYR M X T c
  obtain ⟨hhyp, Ψ, hS, hL⟩ := hyp1411_of_simple hset hX hnab hG₀
  have hLiso : Nonempty ((perfectResidual ↥G₀).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀)) ≃*
      Lm) :=
    ⟨(Subgroup.equivMapOfInjective _ Ψ.toMonoidHom Ψ.injective).trans
      ((MulEquiv.subgroupCongr hL).trans eY)⟩
  have hSk : CFSG.pRank 2 ↥(((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf G₀).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀))) ≤ 1 := by
    have e₁ := (Subgroup.equivMapOfInjective _ Ψ.toMonoidHom Ψ.injective).trans
      (MulEquiv.subgroupCongr hS)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv one_lt_two e₁,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hRk
  obtain ⟨i₁, i₂, h12, h1, h2, hn1, hn2⟩ := h1411 ↥G₀ _ _ hhyp hLiso hSk
  exact covered_of_fourChar_normal hset hX
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1.1 hG₀ h12 h1 h2 hn1 hn2

theorem kAlpha_le_normalizer_rAlpha :
    kAlpha M X T c ≤ Subgroup.normalizer (SetLike.coe (rAlpha M X T c)) := by
  rintro _ ⟨k, hk, rfl⟩
  exact mk_mem_normalizer_rAlpha ((le_sup_left.trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)) (Subgroup.mem_subgroupOf.mp hk))

theorem meet_core (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] (hnab : ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a)
    (hKY : kTwenty M c ≤ yTwenty X c) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (h2 : CFSG.Open.pRank 2 (yAlpha M X T c) ≤ 2)
    (hInv : ∀ u : ↥(yAlpha M X T c), u * u = 1 → u ≠ 1 → ∃ S : Subgroup ↥(yAlpha M X T c),
      CFSG.GH74.KGroups.L3Eps.InvData p _ u S ∧
        Nonempty (↥S ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)))
    (hOut : ∀ σ : MulAut ↥(yAlpha M X T c), σ * σ = 1 →
      σ ∉ (MulAut.conj : ↥(yAlpha M X T c) →* MulAut ↥(yAlpha M X T c)).range →
      ∀ L : Subgroup ↥(yAlpha M X T c), Group.IsPerfect L → (∀ l ∈ L, σ l = l) →
      ∀ z ∈ L, z ≠ 1 → (∀ l ∈ L, z * l = l * z) → False)
    (hD : rAlpha M X T c ⊓ yAlpha M X T c ≠ ⊥) :
    (p = 5 ∨ p = 7) ∧ CFSG.Open.pRank 2 (rAlpha M X T c) ≤ 1 := by
  haveI := yAlpha_normal hX
  have hinj := conjNormal_yAlpha_injective hX hnab
  have hK'perf := isPerfect_range_kToYAlpha hset hKY
  have hK'1 := range_kToYAlpha_ne_bot hset hKY
  have hK'mem : ∀ y : ↥(yAlpha M X T c),
      y ∈ (kToYAlpha (T := T) hKY).range ↔ Subtype.val y ∈ kAlpha M X T c := by
    intro y
    rw [← map_range_kToYAlpha hKY]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y', hy', hy'e⟩
      have : y' = y := Subtype.ext hy'e
      rwa [← this]
  have hR2 : IsPGroup 2 (rAlpha M X T c) :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_subtype
      (K := yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map _
  obtain ⟨t, htD, ht2, htK⟩ := exists_involution_commute_kAlpha hset hX h2 hD
  set t' : ↥(yAlpha M X T c) := ⟨t, htD.2⟩ with ht'def
  have ht'2 : t' * t' = 1 := Subtype.ext (by
    show t * t = 1
    have h := pow_orderOf_eq_one t
    rw [ht2, sq] at h
    exact h)
  have ht'1 : t' ≠ 1 := by
    intro h
    have h1 : t = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  obtain ⟨S, hI, ⟨eS⟩⟩ := hInv t' ht'2 ht'1
  have hK'S : (kToYAlpha (T := T) hKY).range ≤ S :=
    L3OddAut.le_of_isPerfect_of_le_centralizer hI hK'perf fun y hy => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (htK _ ((hK'mem y).mp hy))
  obtain ⟨φ, hφ⟩ := exists_surjective_kBar hset hKY
  haveI := Res6.isSimpleGroup_of_setting204 hset
  obtain ⟨htK', hN, hLS⟩ := SL2Comp.sl2Comp_facts hp5 hI eS hK'S hK'perf hK'1 φ hφ
    hset.kType.symm
  have htKα : t ∈ kAlpha M X T c := (hK'mem t').mp htK'
  have hcomm : ∀ k ∈ kAlpha M X T c, ∀ r ∈ rAlpha M X T c, k * r = r * k := by
    apply commute_of_inf_le_centralizer hset hX
    set N' : Subgroup ↥(yAlpha M X T c) := (kToYAlpha (T := T) hKY).range ⊓
      (rAlpha M X T c).comap (yAlpha M X T c).subtype with hN'def
    have hN'2 : IsPGroup 2 N' :=
      (hR2.comap_of_injective _ (Subgroup.subtype_injective _)).to_le inf_le_right
    have hN'n : ∀ l ∈ (kToYAlpha (T := T) hKY).range, ∀ n ∈ N', l * n * l⁻¹ ∈ N' := by
      intro l hl n hn
      obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.mp hn
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hl hn1)
        (Subgroup.inv_mem _ hl), ?_⟩
      have hlN := kAlpha_le_normalizer_rAlpha ((hK'mem l).mp hl)
      have h := (Subgroup.mem_normalizer_iff.mp hlN _).mp (Subgroup.mem_comap.mp hn2)
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact h
    have hNc := hN N' inf_le_left hN'2 hN'n
    intro z hz k hk
    have hzY : z ∈ yAlpha M X T c := kAlpha_le_yAlpha hset hX hz.1
    have hkY : k ∈ yAlpha M X T c := kAlpha_le_yAlpha hset hX hk
    have hz' : (⟨z, hzY⟩ : ↥(yAlpha M X T c)) ∈ N' := ⟨(hK'mem _).mpr hz.1, hz.2⟩
    have hk' : (⟨k, hkY⟩ : ↥(yAlpha M X T c)) ∈ S := hK'S ((hK'mem _).mpr hk)
    exact congrArg Subtype.val (hNc _ hz' _ hk')
  have hRk : CFSG.Open.pRank 2 (rAlpha M X T c) ≤ 1 := by
    refine CFSG.ProperTwoGeneratedCore.Assembly.pRank_two_le_one_of_forall_involution_eq ht2
      fun x hx hx2 => ?_
    have hxx : x * x = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hx2, sq] at h
      exact h
    have hxK : ∀ k ∈ kAlpha M X T c, k * x = x * k := fun k hk => hcomm k hk x hx
    by_cases hxY : x ∈ yAlpha M X T c
    ·
      set x' : ↥(yAlpha M X T c) := ⟨x, hxY⟩ with hx'def
      have hx'2 : x' * x' = 1 := Subtype.ext hxx
      have hx'1 : x' ≠ 1 := by
        intro h
        have h1 : x = 1 := congrArg Subtype.val h
        rw [h1, orderOf_one] at hx2
        exact absurd hx2 (by norm_num)
      obtain ⟨Sx, hIx, -⟩ := hInv x' hx'2 hx'1
      have hK'Sx : (kToYAlpha (T := T) hKY).range ≤ Sx :=
        L3OddAut.le_of_isPerfect_of_le_centralizer hIx hK'perf fun y hy => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subtype.ext (hxK _ ((hK'mem y).mp hy))
      rcases hIx.involution t' (hK'Sx htK') ht'2 with h | h
      · exact absurd h ht'1
      · exact (congrArg Subtype.val h).symm
    ·
      exfalso
      set σ := MulAut.conjNormal (H := yAlpha M X T c) x with hσdef
      have hσ2 : σ * σ = 1 := by rw [hσdef, ← map_mul, hxx, map_one]
      have hσout : σ ∉ (MulAut.conj : ↥(yAlpha M X T c) →* MulAut ↥(yAlpha M X T c)).range := by
        rintro ⟨y, hy⟩
        rw [← conjNormal_eq_conj] at hy
        apply hxY
        rw [← hinj hy]
        exact y.2
      refine hOut σ hσ2 hσout _ hK'perf (fun l hl => ?_) t' htK' ht'1 (fun l hl => ?_)
      · apply Subtype.ext
        rw [hσdef, MulAut.conjNormal_apply, ← hxK _ ((hK'mem l).mp hl), mul_inv_cancel_right]
      · have h := hI.le_centralizer (hK'S hl)
        rw [Subgroup.mem_centralizer_singleton_iff] at h
        exact h.symm
  have hRS : ∀ x ∈ rAlpha M X T c, ∀ s ∈ S, x * Subtype.val s = Subtype.val s * x := by
    intro x hx s hs
    obtain ⟨a, ha⟩ := hR2 ⟨x, hx⟩
    set σ := MulAut.conjNormal (H := yAlpha M X T c) x with hσdef
    have hxa : x ^ 2 ^ a = 1 := congrArg Subtype.val ha
    have hσa : σ ^ 2 ^ a = 1 := by rw [hσdef, ← map_pow, hxa, map_one]
    have hσt : σ t' = t' := Subtype.ext (by
      rw [hσdef, MulAut.conjNormal_apply]
      show x * t * x⁻¹ = t
      rw [← hcomm t htKα x hx, mul_inv_cancel_right])
    have hfix : ∀ l ∈ (kToYAlpha (T := T) hKY).range, σ l = l := fun l hl => Subtype.ext (by
      rw [hσdef, MulAut.conjNormal_apply, ← hcomm _ ((hK'mem l).mp hl) x hx,
        mul_inv_cancel_right])
    have h := congrArg Subtype.val
      (L3OddAut.fixes_of_invData hp5 hI eS hσa hσt hK'S hK'perf hK'1 hfix s hs)
    rw [hσdef, MulAut.conjNormal_apply] at h
    calc x * Subtype.val s = x * Subtype.val s * x⁻¹ * x := by group
      _ = Subtype.val s * x := by rw [h]
  have hnorm : ((kToYAlpha (T := T) hKY).range.subgroupOf S).Normal := by
    refine ⟨fun l hl s => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    have hsN : Subtype.val (Subtype.val s) ∈
        Subgroup.normalizer (SetLike.coe (rAlpha M X T c)) := by
      refine Subgroup.mem_normalizer_fintype fun r hr => ?_
      rw [← hRS r hr s s.2, mul_inv_cancel_right]
      exact hr
    have hsK := normalizer_rAlpha_le_normalizer_kAlpha hset hX hsN
    have h := (Subgroup.mem_normalizer_iff.mp hsK _).mp ((hK'mem _).mp hl)
    exact (hK'mem _).mpr (by simpa using h)
  have hSK : S ≤ (kToYAlpha (T := T) hKY).range := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hI.quasisimple hnorm with htop | hc
    · exact Subgroup.subgroupOf_eq_top.mp htop
    · exfalso
      haveI : Nontrivial ↥(kToYAlpha (T := T) hKY).range :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hK'1
      haveI : IsMulCommutative ↥(kToYAlpha (T := T) hKY).range := ⟨⟨fun a b => by
        have ha : (⟨a, hK'S a.2⟩ : ↥S) ∈ Subgroup.center ↥S := hc a.2
        have h := Subgroup.mem_center_iff.mp ha ⟨b, hK'S b.2⟩
        exact Subtype.ext (congrArg Subtype.val h).symm⟩⟩
      haveI := hK'perf
      exact (Group.IsPerfect.not_isMulCommutative
        (G := ↥(kToYAlpha (T := T) hKY).range)) inferInstance
  exact ⟨hLS (le_antisymm hK'S hSK), hRk⟩

section Rank


theorem eq_one_of_yAlpha_mulEquiv_L3 (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] (hnab : ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a)
    {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 1 ≤ e)
    (eY : ↥(yAlpha M X T c) ≃* projSL 3 (GaloisField p e)) : e = 1 := by
  have hp := (Fact.out : p.Prime)
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 p e :=
    ⟨hp, he, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num),
      fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
  have hmod := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm eY
  have hrk := pRank_yAlpha_le_two hset hX hnab hp hp5
  obtain ⟨-, -, h⟩ := CFSG.SectionRank.classical_model_rank (by omega) hmod
  rcases h with ⟨-, ⟨h, -⟩ | ⟨-, h⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
  · exact absurd h (by decide)
  · omega
  · omega
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · omega

end Rank

end AscBridge

section Main


open AscBridge in
theorem step204AscL3OddMeet_holds : Step204AscL3OddMeet := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hL2m hYK h hD
  obtain ⟨hs, hnab⟩ := isSimpleGroup_yAlpha hset hX hm
  haveI := hs
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hKY : kTwenty M c ≤ yTwenty X c :=
    Res6.kTwenty_le_yTwenty hset (le_sup_left.trans hKTX)
  have hp3 : ∀ {p e : ℕ}, 1 ≤ e → p ^ e % 3 ≠ 0 → p ≠ 3 := by
    intro p e he hq h3
    subst h3
    apply hq
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
    rw [pow_add, pow_one, Nat.mul_mod_right]
  have hp5 : ∀ {p : ℕ}, p.Prime → p ≠ 2 → p ≠ 3 → 5 ≤ p := by
    intro p hp hp2 hp3
    have h2 := hp.two_le
    by_contra h
    push Not at h
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  rcases h with ⟨p, e, hpF, hp2, he, hq, ⟨eY⟩⟩ | ⟨p, e, hpF, hp2, he, hq, ⟨eY⟩⟩
  ·
    have hp5' := hp5 hpF.out hp2 (hp3 he (by omega))
    obtain rfl := eq_one_of_yAlpha_mulEquiv_L3 hset hX hnab hp5' he eY
    have hq' : p % 3 = 2 := by simpa using hq
    have h2 : CFSG.Open.pRank 2 (yAlpha M X T c) ≤ 2 := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact Sec4.HeringUnitary.twoRank_le_two_of_projSL_three hp2 le_rfl eY
    obtain ⟨h57, hRk⟩ := meet_core hset hX hnab hKY hp5' h2
      (fun u hu hu1 => L3OddInv.exists_invData_sl2_L3 hp2 hq' eY hu hu1)
      (fun σ hσ hout L hL hfix z hz hz1 hzc =>
        L3OddAut.false_of_fixes_center_L3 hp2 hq' eY hσ hout hL hfix hz hz1 hzc) hD
    rcases h57 with rfl | rfl
    · exact covered_of_asc1411_pRank hset hX hnab eY hRk
        fun X' _ _ L' S' h hL hS => asc82Item1411_L3_5_pRank X' L' S' h (Or.inr hL) hS
    · norm_num at hq'
  ·
    have hp5' := hp5 hpF.out hp2 (hp3 he (by omega))
    obtain rfl := eq_one_of_yAlpha_mulEquiv_U3 hset hX hnab hp5' he eY
    have hq' : p % 3 = 1 := by simpa using hq
    have h2 : CFSG.Open.pRank 2 (yAlpha M X T c) ≤ 2 := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact Sec4.HeringUnitary.twoRank_le_two_of_projSU_three hp2 le_rfl eY
    obtain ⟨h57, hRk⟩ := meet_core hset hX hnab hKY hp5' h2
      (fun u hu hu1 => L3OddInv.exists_invData_sl2_U3 hp2 hq' eY hu hu1)
      (fun σ hσ hout L hL hfix z hz hz1 hzc =>
        L3OddAut.false_of_fixes_center_U3 hp2 hq' eY hσ hout hL hfix hz hz1 hzc) hD
    rcases h57 with rfl | rfl
    · norm_num at hq'
    · exact covered_of_asc1411_pRank hset hX hnab eY hRk
        fun X' _ _ L' S' h hL hS => asc82Item1411_U3_7_pRank X' L' S' h (Or.inr hL) hS

theorem step204AscL3Odd_holds : Step204AscL3Odd :=
  step204AscL3Odd_of_meet step204AscL3OddMeet_holds

end Main

end CFSG.RankThree.PartTwo.Sec20
