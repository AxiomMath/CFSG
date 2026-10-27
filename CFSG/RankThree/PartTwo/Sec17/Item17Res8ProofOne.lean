module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofM22S
public import CFSG.RankThree.PartTwo.KFacts.KS14HJLocal
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16
open scoped Pointwise

namespace Proof17Res8

section HJ

variable {Λ : Type} [Group Λ] [Finite Λ]

theorem j2_maxInvariant_decomp
    (hΛ : Nonempty (Λ ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 Λ) {B : Subgroup Λ}
    (hBP : B ≤ P) (hB9 : Nat.card B = 9) {R : Subgroup Λ}
    (hR : R ∈ maxInvariantPiSubgroups ⊤ B (piOf 2)) :
    (∃ T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)),
        Nonempty (↥R ≃* ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))))) ∧
      ∃ a ∈ B, ∃ b ∈ B, Subgroup.closure {a, b} = B ∧
        R = inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set Λ)) ⊔
            inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set Λ)) ⊔
          (R ⊓ Subgroup.centralizer
            (((P : Subgroup Λ) ⊓ Subgroup.centralizer ((P : Subgroup Λ) : Set Λ) : Subgroup Λ) :
              Set Λ)) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨-, -, -, -, h5⟩ := h415 Λ hΛ P _ rfl _ rfl
  obtain ⟨S₀, -, hSP, -, ⟨T, ⟨eT⟩⟩, a, b, hab, hprod⟩ := h5 B ⟨hBP, hB9⟩
  set Z := (P : Subgroup Λ) ⊓ Subgroup.centralizer ((P : Subgroup Λ) : Set Λ) with hZ
  set Va := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set Λ)) with hVa
  set Vb := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set Λ)) with hVb
  set W := S₀ ⊓ Subgroup.centralizer (Z : Set Λ) with hW
  have hVaS : Va ≤ S₀ := by
    intro v hv
    have h := Set.mul_mem_mul (Set.mul_mem_mul (SetLike.mem_coe.mpr (one_mem W))
      (SetLike.mem_coe.mpr hv)) (SetLike.mem_coe.mpr (one_mem Vb))
    rw [hprod, one_mul, mul_one] at h
    exact h
  have hVbS : Vb ≤ S₀ := by
    intro v hv
    have h := Set.mul_mem_mul (Set.mul_mem_mul (SetLike.mem_coe.mpr (one_mem W))
      (SetLike.mem_coe.mpr (one_mem Va))) (SetLike.mem_coe.mpr hv)
    rw [hprod, mul_one, one_mul] at h
    exact h
  have hS₀ : S₀ = Va ⊔ Vb ⊔ W := by
    refine le_antisymm (fun s hs => ?_) (sup_le (sup_le hVaS hVbS) inf_le_left)
    rw [← SetLike.mem_coe, ← hprod] at hs
    obtain ⟨_, ⟨w, hw, v, hv, rfl⟩, v', hv', rfl⟩ := hs
    exact mul_mem (mul_mem (Subgroup.mem_sup_right hw)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hv)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hv'))
  rw [hSP] at hR
  obtain ⟨x, hxP, rfl⟩ := hR
  have hxB : x ∈ Subgroup.normalizer (B : Set Λ) :=
    KFacts.KS14.j2_le_normalizer_of_card_nine h415 hΛ P hBP hB9 hxP
  have hxZ : x ∈ Subgroup.centralizer (Z : Set Λ) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp hz.2 x hxP).symm
  have hCZ : conjugate (Subgroup.centralizer (Z : Set Λ)) x = Subgroup.centralizer (Z : Set Λ) :=
    KFacts.KS14.conjugate_eq_of_mem_normalizer (Subgroup.le_normalizer hxZ)
  have hconjB : ∀ y ∈ B, x⁻¹ * y * x ∈ B := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxB) y).mp hy
    simpa using this
  have hBx : conjugate B x = B := KFacts.KS14.conjugate_eq_of_mem_normalizer hxB
  have haB : a ∈ B := hab ▸ Subgroup.subset_closure (Set.mem_insert a {b})
  have hbB : b ∈ B := hab ▸ Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  refine ⟨⟨T, ⟨(S₀.equivMapOfInjective (MulAut.conj x⁻¹).toMonoidHom
    (MulAut.conj x⁻¹).injective).symm.trans eT⟩⟩, x⁻¹ * a * x, hconjB a haB, x⁻¹ * b * x,
    hconjB b hbB, ?_, ?_⟩
  ·
    rw [← hBx, ← hab, conjugate, MonoidHom.map_closure, Set.image_pair]
    simp
  ·
    have e1 : conjugate (Va ⊔ Vb ⊔ W) x = conjugate Va x ⊔ conjugate Vb x ⊔ conjugate W x := by
      simp only [conjugate, Subgroup.map_sup]
    have e2 : conjugate W x =
        conjugate S₀ x ⊓ conjugate (Subgroup.centralizer (Z : Set Λ)) x := by
      simp only [hW, conjugate]
      exact Subgroup.map_inf_eq _ _ _ (MulAut.conj x⁻¹).injective
    have ea : conjugate Va x =
        inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({x⁻¹ * a * x} : Set Λ)) :=
      KFacts.KS14.conjugate_inSubgroup_pCore_centralizer a x
    have eb : conjugate Vb x =
        inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({x⁻¹ * b * x} : Set Λ)) :=
      KFacts.KS14.conjugate_inSubgroup_pCore_centralizer b x
    calc conjugate S₀ x = conjugate (Va ⊔ Vb ⊔ W) x := by rw [← hS₀]
      _ = _ := by rw [e1, e2, hCZ, ea, eb]

end HJ

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_threeCentral {L Y₀ D : Subgroup G} (hLY : L ≤ Y₀)
    (hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀) (hDL : D ≤ L) (hD3 : IsPGroup 3 D) :
    ∃ P' : Sylow 3 (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀), Proof17Res6.kimg Y₀ D ≤ P' ∧
      ∀ y : ↥Y₀, (y : G) ∈ D →
        QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) y ∈
          Subgroup.centralizer ((P' : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) : Set _) →
        IsThreeCentralIn L (y : G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : ↥L →* ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp (Subgroup.inclusion hLY) with hπ
  have hπs : Function.Surjective π := by
    intro z
    obtain ⟨l, hl, hlz⟩ := Proof17Res6.exists_mem_L_mk_eq hLY hY z
    exact ⟨⟨l, hl⟩, hlz⟩
  have hD3' : IsPGroup 3 (D.subgroupOf L) := hD3.comap_subtype
  obtain ⟨SL, hDS⟩ := hD3'.exists_le_sylow
  set P' := SL.mapSurjective hπs with hP'
  have hP'coe : (P' : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) = (SL : Subgroup ↥L).map π := rfl
  have hinj : ∀ u ∈ (SL : Subgroup ↥L), π u = 1 → u = 1 := by
    intro u hu h1
    obtain ⟨k, hk⟩ := SL.isPGroup' ⟨u, hu⟩
    have hu2 : Subgroup.inclusion hLY u ∈ CFSG.pCore 2 ↥Y₀ :=
      (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀)) ⟨_, hu2⟩
    have hu3 : u ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hu2' : u ^ 2 ^ m = 1 := by
      apply Subgroup.inclusion_injective hLY
      have := congrArg Subtype.val hm
      simpa using this
    have hcop : Nat.Coprime (3 ^ k) (2 ^ m) := Nat.Coprime.pow k m (by norm_num)
    have h3 : orderOf u ∣ Nat.gcd (3 ^ k) (2 ^ m) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu3) (orderOf_dvd_of_pow_eq_one hu2')
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  refine ⟨P', ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hyD : (y : G) ∈ D := Subgroup.mem_subgroupOf.mp hy
    rw [hP'coe]
    exact ⟨⟨y, hDL hyD⟩, hDS (Subgroup.mem_subgroupOf.mpr hyD), rfl⟩
  · intro y hyD hyC
    have hyL : (y : G) ∈ L := hDL hyD
    have hlS : (⟨y, hyL⟩ : ↥L) ∈ (SL : Subgroup ↥L) := hDS (Subgroup.mem_subgroupOf.mpr hyD)
    refine ⟨hyL, SL, hlS, fun s hs => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hπl : π ⟨y, hyL⟩ = QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) y := rfl
    have hπsC : π s * π ⟨y, hyL⟩ = π ⟨y, hyL⟩ * π s := by
      have hmem : π s ∈ (P' : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) := by
        rw [hP'coe]
        exact ⟨s, hs, rfl⟩
      rw [hπl]
      exact Subgroup.mem_centralizer_iff.mp hyC (π s) hmem
    have h1 : π (s * ⟨y, hyL⟩ * (⟨y, hyL⟩ * s)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hπsC, mul_inv_cancel]
    have h2 := hinj _ (mul_mem (mul_mem hs hlS) (inv_mem (mul_mem hlS hs))) h1
    exact mul_inv_eq_one.mp h2

theorem kimg_inf_centralizer {Y₀ S : Subgroup G} (hS2 : IsPGroup 2 S) {d : ↥Y₀}
    (hd3 : (d : G) ^ 3 = 1) (hdS : (d : G) ∈ Subgroup.normalizer (S : Set G)) :
    Proof17Res6.kimg Y₀ (S ⊓ Y₀) ⊓
        Subgroup.centralizer {QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) d} =
      Proof17Res6.kimg Y₀ (S ⊓ Y₀ ⊓ Subgroup.centralizer {(d : G)}) := by
  apply le_antisymm
  · rintro z ⟨hzR, hzC⟩
    obtain ⟨u, huS, rfl⟩ := Proof17Res6.mem_kimg.mp hzR
    have hcomm : Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) u)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) d) :=
      Subgroup.mem_centralizer_singleton_iff.mp hzC
    set N := S ⊓ CFSG.Open.pCoreOf 2 Y₀ with hN
    have hN3 : ¬ 3 ∣ Nat.card N := Proof171.not_three_dvd_of_isPGroup_two (hS2.to_le inf_le_left)
    have hD3 := Proof171.isPGroup_zpowers_of_pow_three hd3
    have hNY : ∀ n ∈ N, n ∈ Y₀ := fun n hn =>
      CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀ hn.2
    have hκn : ∀ (n : G) (hn : n ∈ N),
        QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) (⟨n, hNY n hn⟩ : ↥Y₀) = 1 := fun n hn =>
      (QuotientGroup.eq_one_iff _).mpr ((Step163Alt.mem_pCore_two_iff _).mpr hn.2)
    obtain ⟨n, hnN, hfix⟩ := Sec12.exists_fixed_mem_coset hD3 hN3 (u : G) (fun e he n hn => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
      have hdk : (d : G) ^ k = ((d ^ k : ↥Y₀) : G) := by simp
      set w : ↥Y₀ := d ^ k * (u * ⟨n, hNY n hn⟩) * (d ^ k)⁻¹ with hw
      have hwG : (w : G) = (d : G) ^ k * ((u : G) * n) * ((d : G) ^ k)⁻¹ := by simp [hw]
      refine ⟨(u : G)⁻¹ * w, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, by rw [hwG]; group⟩
      · have huS' : (u : G) ∈ S := (Subgroup.mem_inf.mp huS).1
        have hwS : (w : G) ∈ S := by
          rw [hwG]
          exact (Subgroup.mem_normalizer_iff.mp (zpow_mem hdS k) _).mp
            (mul_mem huS' (Subgroup.mem_inf.mp hn).1)
        exact mul_mem (inv_mem huS') hwS
      · refine (Step163Alt.mk_eq_mk_iff u w).mp ?_
        rw [hw, map_mul, map_mul, map_mul, map_inv, hκn n hn, mul_one, map_zpow,
          ← (hcomm.zpow_right k).eq, mul_inv_cancel_right])
    have hnY := hNY n hnN
    have hunC : ((u * ⟨n, hnY⟩ : ↥Y₀) : G) ∈ Subgroup.centralizer {(d : G)} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hfix (d : G) (Subgroup.mem_zpowers _)
      simp only [Subgroup.coe_mul]
      calc (u : G) * n * d = ((d : G) * ((u : G) * n) * (d : G)⁻¹) * d := by rw [h1]
        _ = d * (u * n) := by group
    have hunS : ((u * ⟨n, hnY⟩ : ↥Y₀) : G) ∈ S ⊓ Y₀ :=
      Subgroup.mem_inf.mpr ⟨mul_mem (Subgroup.mem_inf.mp huS).1 (Subgroup.mem_inf.mp hnN).1,
        (u * ⟨n, hnY⟩).2⟩
    refine Proof17Res6.mem_kimg.mpr ⟨u * ⟨n, hnY⟩, Subgroup.mem_inf.mpr ⟨hunS, hunC⟩, ?_⟩
    rw [map_mul, hκn n hnN, mul_one]
  · intro z hz
    obtain ⟨u, hu, rfl⟩ := Proof17Res6.mem_kimg.mp hz
    obtain ⟨huS, huC⟩ := Subgroup.mem_inf.mp hu
    refine Subgroup.mem_inf.mpr ⟨Proof17Res6.mem_kimg.mpr ⟨u, huS, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp huC)

omit [Finite G] in
theorem nonempty_imgY0_equiv_kimg {A Y₀ : Subgroup G} [(kerAO2 A Y₀).Normal] {X : Subgroup G}
    (hX : X ≤ Y₀) : Nonempty (↥(imgY0 A Y₀ X) ≃* ↥(Proof17Res6.kimg Y₀ X)) := by
  set φ₁ : ↥X →* ↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀ :=
    (QuotientGroup.mk' (kerAO2 A Y₀)).comp (Subgroup.inclusion (hX.trans le_sup_right))
    with hφ₁
  set φ₂ : ↥X →* ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp (Subgroup.inclusion hX) with hφ₂
  have hk : φ₁.ker = φ₂.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hφ₁, hφ₂, MonoidHom.comp_apply,
      MonoidHom.comp_apply, ← map_one (QuotientGroup.mk' (kerAO2 A Y₀)),
      ← map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))]
    have e1 : Subgroup.inclusion (hX.trans le_sup_right) x =
        Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) (Subgroup.inclusion hX x) := rfl
    have e2 : (1 : ↥(A ⊔ Y₀)) = Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) 1 := rfl
    rw [e1, e2]
    exact Proof17Res6.mk_inclusion_eq_iff_mk_eq _ _
  have h1 : φ₁.range = imgY0 A Y₀ X := by
    ext z
    rw [MonoidHom.mem_range, Proof17Res6.mem_imgY0_iff' hX]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hX x, x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have h2 : φ₂.range = Proof17Res6.kimg Y₀ X := by
    ext z
    rw [MonoidHom.mem_range, Proof17Res6.mem_kimg]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hX x, x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  exact ⟨(MulEquiv.subgroupCongr h1).symm.trans
    (((QuotientGroup.quotientKerEquivRange φ₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivRange φ₂))).trans (MulEquiv.subgroupCongr h2))⟩

end Lift

section Clause

variable {G : Type} [Group G] [Finite G]

theorem item1717OneJ2Clause_at
    {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    [(kerAO2 A Y₀).Normal] (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h142 : Concl142 A (lB A))
    (hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀)
    (hJ2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    (∃ T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)),
        Nonempty (↥(imgY0 A Y₀ (S ⊓ Y₀)) ≃*
          ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))))) ∧
      ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A) (d : G),
        Subgroup.closure {a, b} = A ⊓ L ∧ d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn L d ∧
        imgY0 A Y₀ (S ⊓ Y₀) =
          oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊔ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) ⊔
            imgY0 A Y₀ (S ⊓ Y₀ ⊓ Subgroup.centralizer {d}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs := h.toSec17Std
  have hLY : L ≤ Y₀ := hs.le_y0
  obtain ⟨⟨fL⟩, h9, -, -, -, hAnorm⟩ := hs.j2_local hJ2
  obtain ⟨e₀⟩ := Proof17Res3.nonempty_quotient_pCore_two_equiv hLY hY
  have hΛ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨e₀.trans fL⟩
  have hLsurj := Proof17Res6.exists_mem_L_mk_eq hLY hY
  have hB9 : Nat.card (Proof17Res6.kimg Y₀ (A ⊓ L)) = 9 := Proof17Res6.card_kimg_inf hs h9
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hSQ : S ∈ scriptQ A (lB A) := h.mem_qStar_two.prop.1.1
  have hAS : A ≤ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hSQ.1.2.2 h.le_normalizer_y0
  have hBR : Proof17Res6.kimg Y₀ (A ⊓ L) ≤
      Subgroup.normalizer (Proof17Res6.kimg Y₀ (S ⊓ Y₀) : Set _) :=
    Proof17Res6.kimg_le_normalizer_kimg (inf_le_left.trans hAS)
  have hR2 : IsPGroup 2 (Proof17Res6.kimg Y₀ (S ⊓ Y₀)) :=
    ((hS2.to_le inf_le_left).comap_subtype).map _
  have hRmax : Proof17Res6.kimg Y₀ (S ⊓ Y₀) ∈
      maxInvariantPiSubgroups ⊤ (Proof17Res6.kimg Y₀ (A ⊓ L)) (piOf 2) :=
    ⟨⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hR2, hBR⟩, fun X hX hRX =>
      Proof17Res6.le_kimg_of_le h h142 hLsurj hAnorm
        ((isPiSubgroup_piOf_iff Nat.prime_two X).mp hX.2.1) hX.2.2 hRX⟩
  have hAL3 : IsPGroup 3 (A ⊓ L : Subgroup G) :=
    (HeadProof.isE27_of_std hs).isPGroup.to_le inf_le_left
  obtain ⟨P', hBP, hcent⟩ := exists_sylow_threeCentral hLY hY inf_le_right hAL3
  obtain ⟨⟨T, ⟨eT⟩⟩, a', ha', b', hb', hcl, hReq⟩ :=
    j2_maxInvariant_decomp hΛ P' hBP hB9 hRmax
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨hZ3, -, -⟩ := j2_sylow_facts h415 hΛ P'
  have hZB := KFacts.KS14.j2_inf_centralizer_le_of_card_nine h415 hΛ P' hBP hB9
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ3
    omega : (P' : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) ⊓
      Subgroup.centralizer ((P' : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) : Set _) ≠ ⊥)
  obtain ⟨y, hyAL, hyz⟩ := Proof17Res6.mem_kimg.mp (hZB z.2)
  have hZz : (P' : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) ⊓
      Subgroup.centralizer ((P' : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) : Set _) =
      Subgroup.zpowers (z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z.2) ?_
    rw [hZ3, Nat.card_zpowers]
    have hdvd : orderOf (z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) ∣ 3 := by
      have h1 := orderOf_dvd_natCard z
      rw [hZ3] at h1
      rwa [Subgroup.orderOf_coe]
    have hne : orderOf (z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) ≠ 1 := by
      rw [Ne, orderOf_eq_one_iff]
      intro h1
      exact hz1 (Subtype.ext h1)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · rw [h]
  have hCZ : Subgroup.centralizer (((P' : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) ⊓
      Subgroup.centralizer ((P' : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) : Set _) :
        Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) : Set _) =
      Subgroup.centralizer {QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) y} := by
    rw [hZz, ← hyz, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hdA : (y : G) ∈ A := (Subgroup.mem_inf.mp hyAL).1
  have hd1 : (y : G) ≠ 1 := by
    intro h1
    apply hz1
    apply Subtype.ext
    rw [← hyz, show y = 1 from Subtype.ext h1, map_one]
    rfl
  have hdc : IsThreeCentralIn L (y : G) := hcent y hyAL (by
    rw [hyz]
    exact (Subgroup.mem_inf.mp z.2).2)
  have hRC : Proof17Res6.kimg Y₀ (S ⊓ Y₀) ⊓ Subgroup.centralizer (((P' : Subgroup
      (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) ⊓ Subgroup.centralizer ((P' : Subgroup
        (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) : Set _) : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) : Set _) =
      Proof17Res6.kimg Y₀ (S ⊓ Y₀ ⊓ Subgroup.centralizer {(y : G)}) := by
    rw [hCZ]
    exact kimg_inf_centralizer hS2 (HeadProof.pow_three_of_std hs hdA) (hSQ.1.2.2 hdA)
  obtain ⟨a, haAL, rfl⟩ := Proof17Res6.mem_kimg.mp ha'
  obtain ⟨b, hbAL, rfl⟩ := Proof17Res6.mem_kimg.mp hb'
  have hOa := Proof17Res6.oTwoCY0_eq_kimg (A := A) (Subgroup.mem_inf.mp haAL).1
  have hOb := Proof17Res6.oTwoCY0_eq_kimg (A := A) (Subgroup.mem_inf.mp hbAL).1
  set Ta : Subgroup G := ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer
    {QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) a})).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))).map Y₀.subtype with hTa
  set Tb : Subgroup G := ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer
    {QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) b})).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))).map Y₀.subtype with hTb
  have hTaY : Ta ≤ Y₀ := Subgroup.map_subtype_le _
  have hTbY : Tb ≤ Y₀ := Subgroup.map_subtype_le _
  have hTcY : S ⊓ Y₀ ⊓ Subgroup.centralizer {(y : G)} ≤ Y₀ := inf_le_left.trans inf_le_right
  obtain ⟨eR⟩ := nonempty_imgY0_equiv_kimg (A := A) (inf_le_right : S ⊓ Y₀ ≤ Y₀)
  refine ⟨⟨T, ⟨eR.trans eT⟩⟩, a, (Subgroup.mem_inf.mp haAL).1, b, (Subgroup.mem_inf.mp hbAL).1,
    y, ?_, hdA, hd1, hdc, ?_⟩
  ·
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.closure_le _).mpr ?_) ?_
    · rintro _ (rfl | rfl)
      · exact haAL
      · exact hbAL
    · have hle : Proof17Res6.kimg Y₀ (A ⊓ L) ≤
          Proof17Res6.kimg Y₀ (Subgroup.closure {(a : G), (b : G)}) := by
        rw [← hcl, Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact Proof17Res6.mem_kimg.mpr ⟨a, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
        · exact Proof17Res6.mem_kimg.mpr
            ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
      have hclY : Subgroup.closure {(a : G), (b : G)} ≤ Y₀ := by
        rw [Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact a.2
        · exact b.2
      have hd : Nat.card (Proof17Res6.kimg Y₀ (Subgroup.closure {(a : G), (b : G)})) ∣
          Nat.card (Subgroup.closure {(a : G), (b : G)}) := by
        have := Subgroup.card_map_dvd ((Subgroup.closure {(a : G), (b : G)}).subgroupOf Y₀)
          (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hclY).toEquiv] at this
      have hpos : 0 < Nat.card (Subgroup.closure {(a : G), (b : G)}) := Nat.card_pos
      rw [h9]
      calc 9 = Nat.card (Proof17Res6.kimg Y₀ (A ⊓ L)) := hB9.symm
        _ ≤ Nat.card (Proof17Res6.kimg Y₀ (Subgroup.closure {(a : G), (b : G)})) :=
          Subgroup.card_le_of_le hle
        _ ≤ Nat.card (Subgroup.closure {(a : G), (b : G)}) := Nat.le_of_dvd hpos hd
  ·
    rw [hOa, hOb, ← Proof1712.imgY0_sup (hTaY.trans le_sup_right) (hTbY.trans le_sup_right),
      ← Proof1712.imgY0_sup ((sup_le hTaY hTbY).trans le_sup_right) (hTcY.trans le_sup_right)]
    refine Proof17Res6.imgY0_eq_of_kimg_eq inf_le_right (sup_le (sup_le hTaY hTbY) hTcY) ?_
    rw [Proof17Res6.kimg_sup (sup_le hTaY hTbY) hTcY, Proof17Res6.kimg_sup hTaY hTbY,
      Proof17Res6.kimg_preimage, Proof17Res6.kimg_preimage, ← hRC]
    rw [Proof17Res6.inSubgroup_pCore_two_eq, Proof17Res6.inSubgroup_pCore_two_eq] at hReq
    exact hReq

end Clause

end Proof17Res8

theorem item1717OneJ2Clause_statement
    (h1715 : Item1715) (h142 : Concl142S14) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
      (P : Subgroup G) (h : Sec17Y1 G A c L Y₀ Y₁ S p P),
      omegaA A = {Subgroup.zpowers c} →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      letI := kerAO2_normal h.le_normalizer_y0
      (∃ T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)),
          Nonempty (↥(imgY0 A Y₀ (S ⊓ Y₀)) ≃*
            ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))))) ∧
        ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A) (d : G),
          Subgroup.closure {a, b} = A ⊓ L ∧ d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn L d ∧
          imgY0 A Y₀ (S ⊓ Y₀) =
            oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊔ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) ⊔
              imgY0 A Y₀ (S ⊓ Y₀ ⊓ Subgroup.centralizer {d}) := by
  intro G _ _ A c L Y₀ Y₁ S p P h hΩ hJ2
  have := kerAO2_normal h.le_normalizer_y0
  have hs := h.toSec17Std
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    rcases h1715 G A c L Y₀ hs with ⟨-, hY, -, -⟩ | ⟨-, -, -, -, hT⟩
    · exact hY
    · exfalso
      have h3 := hT.1
      rw [hΩ, Set.ncard_singleton] at h3
      omega
  exact Proof17Res8.item1717OneJ2Clause_at h (h142 G A c L hs.toSec14Std) hY hJ2

end CFSG.RankThree.PartTwo.Sec17
