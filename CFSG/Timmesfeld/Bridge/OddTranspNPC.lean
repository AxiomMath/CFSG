module

public import CFSG.Timmesfeld.Bridge.OddTranspBasic
public import CFSG.Timmesfeld.Bridge.Asc72Central
public import CFSG.Timmesfeld.Bridge.Asc72NoPolar

public section

namespace CFSG.Timmesfeld.Bridge.OddTransp

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

variable {G : Type} [Group G] {D : Set G}

theorem commutator_eq_top_of_surjective {H : Type*} [Group H] {f : G →* H}
    (hf : Function.Surjective f) (h : commutator G = ⊤) : commutator H = ⊤ := by
  rw [commutator_def, ← Subgroup.map_top_of_surjective f hf, ← Subgroup.map_commutator,
    ← commutator_def, h]

theorem eq_one_of_isSolvable_of_perfect {K : Type*} [Group K] (hsol : Group.IsSolvable K)
    (hperf : commutator K = ⊤) (x : K) : x = 1 := by
  by_contra hx
  have : Nontrivial K := ⟨⟨x, 1, hx⟩⟩
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial K).ne hperf

theorem pCore_le_commutator_of_isBenderGroup [Finite G] (hS : Setup G D)
    (hperf : commutator G = ⊤) (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ zStar G)) :
    CFSG.pCore 2 G ≤ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 G with hQdef
  set N := ⁅Q, (⊤ : Subgroup G)⁆ with hNdef
  set R := zStar G with hRdef
  have hNQ : N ≤ Q := Subgroup.commutator_le_left _ _
  have hQR : Q ≤ R := pCore_le_zStar
  have hNR : N ≤ R := hNQ.trans hQR
  have hDR : ∀ d ∈ D, d ∉ R := by
    rcases hS.subset_or_disjoint R with h' | h'
    · exfalso
      have htop := hS.eq_top_of_subset R h'
      have hsol : Group.IsSolvable G := by
        have hR := isSolvable_zStar (G := G)
        exact Group.isSolvable_of_surjective (f := R.subtype)
          (fun g => ⟨⟨g, htop ▸ Subgroup.mem_top g⟩, rfl⟩)
      obtain ⟨d, hd⟩ := hS.nonempty
      exact hS.oddT.ne_one hd (eq_one_of_isSolvable_of_perfect hsol hperf d)
    · exact h'
  set π := QuotientGroup.mk' N with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hperf' : commutator (G ⧸ N) = ⊤ := commutator_eq_top_of_surjective hπs hperf
  have hQc : ∀ q ∈ Q, π q ∈ Subgroup.center (G ⧸ N) := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := hπs x
    rw [← map_mul, ← map_mul, hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have h1 : ⁅q⁻¹, g⁻¹⁆ ∈ N :=
      Subgroup.commutator_mem_commutator (Q.inv_mem hq) (Subgroup.mem_top _)
    convert h1 using 1
    rw [commutatorElement_def]
    group
  have hRc : ∀ r ∈ R, π r ∈ Subgroup.center (G ⧸ N) := by
    intro r hr
    have hcommQ : ∀ x : G ⧸ N, ⁅π r, x⁆ ∈ Subgroup.center (G ⧸ N) := by
      intro x
      obtain ⟨g, rfl⟩ := hπs x
      rw [← map_commutatorElement]
      exact hQc _ (mem_zStar_iff.mp hr g)
    let φ : G ⧸ N →* G ⧸ N :=
      { toFun := fun x => ⁅π r, x⁆
        map_one' := commutatorElement_one_right _
        map_mul' := fun x y => by
          rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅π r, x⁆ x,
            Subgroup.mem_center_iff.mp (hcommQ y) x, ← mul_assoc, mul_inv_cancel_right] }
    have hker : commutator (G ⧸ N) ≤ φ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact Subgroup.mem_center_iff.mp (hcommQ y) (φ x)
    rw [hperf'] at hker
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 : ⁅π r, x⁆ = 1 := hker (Subgroup.mem_top x)
    exact ((commutatorElement_eq_one_iff_commute).mp h1).symm.eq
  set Rb := R.map π with hRbdef
  have hRbc : Rb ≤ Subgroup.center (G ⧸ N) := by
    rintro _ ⟨r, hr, rfl⟩
    exact hRc r hr
  obtain ⟨k, m, hm2, hcard⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.card_pos (α := G ⧸ N)).ne' 2 (by norm_num)
  have hmodd : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm2)
  let O : Subgroup (G ⧸ N) :=
    { carrier := {x | x ∈ Rb ∧ x ^ m = 1}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨Rb.mul_mem hx.1 hy.1, ?_⟩
        have hc : Commute x y := Subgroup.mem_center_iff.mp (hRbc hy.1) x
        rw [hc.mul_pow, hx.2, hy.2, one_mul]
      one_mem' := ⟨Rb.one_mem, one_pow m⟩
      inv_mem' := fun {x} hx => ⟨Rb.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hOR : O ≤ Rb := fun x hx => hx.1
  have hOc : O ≤ Subgroup.center (G ⧸ N) := hOR.trans hRbc
  have hOn : O.Normal := Subgroup.normal_of_le_center hOc
  have hRbn : Rb.Normal := Subgroup.normal_of_le_center hRbc
  have hRO : ∀ x ∈ Rb, x ^ 2 ^ k ∈ O := by
    intro x hx
    refine ⟨Rb.pow_mem hx _, ?_⟩
    rw [← pow_mul, ← hcard, pow_card_eq_one']
  have hOodd : ∀ x ∈ O, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat hmodd (orderOf_dvd_of_pow_eq_one hx.2)
  set ψ := QuotientGroup.mk' O with hψdef
  have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective O
  set E := Rb.map ψ with hEdef
  have hEc : E ≤ Subgroup.center ((G ⧸ N) ⧸ O) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := hψs y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hRbc hx) g]
  have hEn : E.Normal := Subgroup.normal_of_le_center hEc
  have hE2 : IsPGroup 2 E := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hψdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hRO x hx
  have hB' : CFSG.BenderSuzuki.IsBenderGroup (((G ⧸ N) ⧸ O) ⧸ E) := by
    have e₁ : ((G ⧸ N) ⧸ O) ⧸ E ≃* (G ⧸ N) ⧸ Rb :=
      QuotientGroup.quotientQuotientEquivQuotient O Rb hOR
    have e₂ : (G ⧸ N) ⧸ Rb ≃* G ⧸ R := QuotientGroup.quotientQuotientEquivQuotient N R hNR
    exact isBenderGroup_of_mulEquiv (e₁.trans e₂) hB
  have hφ1 : ∀ d ∈ D, (ψ.comp π) d ≠ 1 := by
    intro d hd h1
    apply hDR d hd
    have hO : π d ∈ O := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨r, hr, hrd⟩ := hO.1
    have hrd' : r⁻¹ * d ∈ N := by
      rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hrd
      exact hrd
    have := R.mul_mem hr (hNR hrd')
    rwa [mul_inv_cancel_left] at this
  have hcomp : Function.Surjective (ψ.comp π) := by
    intro y
    obtain ⟨x, rfl⟩ := hψs y
    obtain ⟨g, rfl⟩ := hπs x
    exact ⟨g, rfl⟩
  have hS' := hS.map (ψ.comp π) hcomp hφ1
  have hinf := inf_commutator_eq_bot_of_isBenderGroup hS' hEc hE2 hB'
  rw [commutator_eq_top_of_surjective hcomp hperf, inf_top_eq] at hinf
  intro q hq
  have hqRb : π q ∈ Rb := ⟨q, hQR hq, rfl⟩
  have hqE : ψ (π q) ∈ E := ⟨π q, hqRb, rfl⟩
  rw [hinf, Subgroup.mem_bot, hψdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hqE
  have hQb : IsPGroup 2 (Q.map π) := CFSG.pCore_isPGroup.map π
  have h1 : π q = 1 := eq_one_of_isPGroup_of_odd hQb ⟨q, hq, rfl⟩ (hOodd _ hqE)
  exact (QuotientGroup.eq_one_iff q).mp h1

theorem noPerfectCentralExt_of_isBenderGroup [Finite G] (hS : Setup G D)
    (hperf : commutator G = ⊤) (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ zStar G)) :
    NoPerfectCentralExt G (CFSG.pCore 2 G) := fun _ _ _ hQ₀ =>
  inf_le_left.trans ((pCore_le_commutator_of_isBenderGroup hS hperf hB).trans hQ₀)

theorem mk_mem_center_of_mem {Q : Subgroup G} [Q.Normal] {q : G} (hq : q ∈ Q) :
    QuotientGroup.mk' ⁅Q, (⊤ : Subgroup G)⁆ q ∈ Subgroup.center (G ⧸ ⁅Q, (⊤ : Subgroup G)⁆) := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have h1 : ⁅q⁻¹, g⁻¹⁆ ∈ ⁅Q, (⊤ : Subgroup G)⁆ :=
    Subgroup.commutator_mem_commutator (Q.inv_mem hq) (Subgroup.mem_top _)
  convert h1 using 1
  rw [commutatorElement_def]
  group

theorem noPerfectCentralExt_of_isBenderGroup_quotient [Finite G] (hS : Setup G D)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ CFSG.pCore 2 G)) :
    NoPerfectCentralExt G (CFSG.pCore 2 G) := by
  intro Q₀ _ _ hQQ₀
  set Q := CFSG.pCore 2 G with hQdef
  set N := ⁅Q, (⊤ : Subgroup G)⁆ with hNdef
  refine le_trans ?_ hQQ₀
  have hNQ : N ≤ Q := Subgroup.commutator_le_left _ _
  have hDQ : ∀ d ∈ D, d ∉ Q := by
    rcases hS.subset_or_disjoint Q with h' | h'
    · exfalso
      have htop := hS.eq_top_of_subset Q h'
      have := (IsBenderGroup.isSimpleGroup hB).toNontrivial
      obtain ⟨x, y, hxy⟩ := exists_pair_ne (G ⧸ Q)
      apply hxy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Q y
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      exact htop ▸ Subgroup.mem_top _
    · exact h'
  set π := QuotientGroup.mk' N with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set E := Q.map π with hEdef
  have hEc : E ≤ Subgroup.center (G ⧸ N) := by
    rintro _ ⟨q, hq, rfl⟩
    exact mk_mem_center_of_mem hq
  have hE2 : IsPGroup 2 E := CFSG.pCore_isPGroup.map π
  have hEn : E.Normal := Subgroup.normal_of_le_center hEc
  have hB' : CFSG.BenderSuzuki.IsBenderGroup ((G ⧸ N) ⧸ E) :=
    isBenderGroup_of_mulEquiv (QuotientGroup.quotientQuotientEquivQuotient N Q hNQ) hB
  have hφ1 : ∀ d ∈ D, π d ≠ 1 := fun d hd h1 =>
    hDQ d hd (hNQ ((QuotientGroup.eq_one_iff d).mp h1))
  have hS' := hS.map π hπs hφ1
  have hinf := inf_commutator_eq_bot_of_isBenderGroup hS' hEc hE2 hB'
  have hmapG : (commutator G).map π ≤ commutator (G ⧸ N) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  rintro q ⟨hq, hqG⟩
  have h1 : π q ∈ E ⊓ commutator (G ⧸ N) := ⟨⟨q, hq, rfl⟩, hmapG ⟨q, hqG, rfl⟩⟩
  rw [hinf, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff q).mp h1

end CFSG.Timmesfeld.Bridge.OddTransp
