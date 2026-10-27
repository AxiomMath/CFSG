module

public import CFSG.Quasithin.Vol2.Ch12Sec6L11b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem isSimple_Kv (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) :
    IsSimpleGroup (↥Kv ⧸ CFSG.pCore 2 ↥Kv) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  set H := Gv v with hHdef
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hqtke : QuasithinUnique.QTKECore G :=
    QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke
  have hH2 : pCoreOf 2 H ≠ ⊥ := pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hK := hC.cComp
  have hLK := hC.lv_le
  have hcases := QuasithinUnique.Vol2Native.lemma_1_2_1_four hqtke.1 h36 hH2 hK
  obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection hK
  let eX : ↥Kv ⧸ CFSG.pCore 2 ↥Kv ≃* ↥(modO2Image H Kv) :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hKH : Kv ≤ H := le_of_mem_cComp hK
  have hLvH : Lv L v ≤ H := Lv_le_Gv L v
  let φ : ↥(Lv L v) →* ↥(modO2Image H Kv) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hLvH)).codRestrict
      (modO2Image H Kv) fun l => ⟨Subgroup.inclusion hLvH l, hLK l.2, rfl⟩
  have hφ : IsPGroup 2 ↥φ.ker := by
    intro k
    have hk : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (Subgroup.inclusion hLvH (k : ↥(Lv L v))) =
        1 := congrArg Subtype.val (k.2 : φ k = 1)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥H)) ⟨_, hk⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => ((z : ↥H) : G)) hn
    simpa using this
  have hP : (CFSG.pCore 2 ↥H).map H.subtype = pCoreOf 2 H := by
    rfl
  have hmemO : ∀ z : ↥H, z ∈ CFSG.pCore 2 ↥H ↔ (z : G) ∈ pCoreOf 2 H := by
    intro z
    rw [← hP]
    constructor
    · intro hz; exact ⟨z, hz, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      rwa [show w = z from Subtype.ext hwz] at hw
  rcases hcases with ⟨-, hs, -⟩ | ⟨-, hc3, -⟩ | h3 | h4
  · exact (MulEquiv.isSimpleGroup_congr eX).2 hs
  · exfalso
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.center ↥(modO2Image H Kv))) 3 (by rw [hc3])
    have hzc : ∀ w : ↥(modO2Image H Kv), w * (z : ↥(modO2Image H Kv)) = z * w :=
      fun w => (Subgroup.mem_center_iff.1 z.2 w)
    have hzo : orderOf ((z : ↥(modO2Image H Kv)) : ↥H ⧸ CFSG.pCore 2 ↥H) = 3 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    obtain ⟨y, hyK, hyz⟩ := ((z : ↥(modO2Image H Kv)) : ↥(modO2Image H Kv)).2
    have hy3 : y ^ 3 ∈ CFSG.pCore 2 ↥H := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      have : (QuotientGroup.mk y : ↥H ⧸ CFSG.pCore 2 ↥H) = (z : ↥(modO2Image H Kv)) := hyz
      rw [this, ← hzo]
      exact pow_orderOf_eq_one _
    obtain ⟨e, he⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥H)) ⟨_, hy3⟩
    have he' : (y ^ 3) ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    set y' := y ^ 2 ^ e with hy'
    have hy'3 : y' ^ 3 = 1 := by
      rw [hy', ← pow_mul, mul_comm, pow_mul, he']
    have hmk : (QuotientGroup.mk y' : ↥H ⧸ CFSG.pCore 2 ↥H) =
        ((z : ↥(modO2Image H Kv)) : ↥H ⧸ CFSG.pCore 2 ↥H) ^ 2 ^ e := by
      rw [hy', QuotientGroup.mk_pow]
      congr 1
    have hy'1 : (y' : G) ≠ 1 := by
      intro h1
      have h1' : y' = 1 := Subtype.ext h1
      have : ((z : ↥(modO2Image H Kv)) : ↥H ⧸ CFSG.pCore 2 ↥H) ^ 2 ^ e = 1 := by
        rw [← hmk, h1', QuotientGroup.mk_one]
      rw [← orderOf_dvd_iff_pow_eq_one, hzo] at this
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this) (by norm_num)
    refine false_of_three_comm h1222 F hH hv hβ y'.2 (by simpa using congrArg Subtype.val hy'3)
      hy'1 fun l hl => ?_
    have hlH : l ∈ H := hLvH hl
    have hw : (QuotientGroup.mk (⟨l, hlH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ modO2Image H Kv :=
      ⟨⟨l, hlH⟩, hLK hl, rfl⟩
    have hcomm := hzc ⟨_, hw⟩
    have hcomm' : (QuotientGroup.mk (⟨l, hlH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) *
        QuotientGroup.mk y' = QuotientGroup.mk y' * QuotientGroup.mk (⟨l, hlH⟩ : ↥H) := by
      rw [hmk]
      exact (Commute.pow_right (congrArg Subtype.val hcomm) _).eq
    have hmem : y' * ⟨l, hlH⟩ * y'⁻¹ * (⟨l, hlH⟩ : ↥H)⁻¹ ∈ CFSG.pCore 2 ↥H := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hcomm']
      group
    exact (hmemO _).1 hmem
  · exfalso
    obtain ⟨p, hp, hp3, -, -, -, ψ₃, -, hψ₃k, -⟩ := h3
    exact false_of_map_sl2 h1222 F hH hv hβ φ hφ hp (by omega) ψ₃ hψ₃k
  · exfalso
    obtain ⟨-, -, ⟨e5⟩, -⟩ := h4
    let ψ₄ := e5.toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.fittingSubgroup ↥(modO2Image H Kv)))
    have hψ₄k : ψ₄.ker = CFSG.fittingSubgroup ↥(modO2Image H Kv) := by
      ext x
      simp [ψ₄]
    exact false_of_map_sl2 h1222 F hH hv hβ φ hφ Nat.prime_five (by norm_num) ψ₄ hψ₄k

end S126T2

end CFSG.Quasithin.H13
