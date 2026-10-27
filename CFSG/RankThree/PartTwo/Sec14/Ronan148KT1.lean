module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Rows
public import CFSG.RankThree.PartTwo.Sec14.Item14Res3ProofLBal
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1List
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (descAut descAut_mk descAut_eq_one_iff)

section DescAut

variable {Γ : Type} [Group Γ]

theorem descAut_of_mem (K : Subgroup Γ) {k : Γ} (hk : k ∈ K)
    (hkN : k ∈ Subgroup.normalizer (K : Set Γ)) :
    descAut K ⟨k, hkN⟩ =
      MulAut.conj ((⟨k, hk⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H l =>
    rw [descAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1

end DescAut

theorem ks143LBalComp2_of_rows
    (h1 : Sec4.Item4_1LargePrime)
    (hrows : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Sec4.Census.List42 S → 3 ∣ Nat.card S → Row143 S) :
    KS143LBalComp2 := by
  intro C _ _ hC K hK b hb3 hbK hbc P hPK hPb hPN hPp hP3
  have hKq : IsQuasisimple ↥K := hK.1
  have hKp : Group.IsPerfect ↥K := hKq.1
  have hSs : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKq.2.1
  have hrow := hrows (↥K ⧸ Subgroup.center ↥K) hSs hKq.2.2 (list42_of_isComponent_quot h1 hC hK)
    (three_dvd_card_quot_center_of_isComponent_quot hK)
  have hZ3 : IsPGroup 3 (Subgroup.center ↥K) := isPGroup_three_center_of_isComponent_quot hK
  set β := descAut K ⟨b, hbK⟩ with hβ
  have hβ3 : β ^ 3 = 1 := by
    rw [hβ, ← map_pow]
    have : (⟨b, hbK⟩ : Subgroup.normalizer (K : Set _)) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  have hβ1 : β ≠ 1 := fun h => hbc ((descAut_eq_one_iff hKp _).mp h)
  have hβx : ∀ x : ↥K, β (x : ↥K ⧸ Subgroup.center ↥K) =
      ((⟨b * (x : _) * b⁻¹, (Subgroup.mem_normalizer_iff.mp hbK x).mp x.2⟩ : ↥K) :
        ↥K ⧸ Subgroup.center ↥K) := by
    intro x
    rw [hβ, descAut_mk]
    congr 1
  have hfix : ∀ x : ↥K, (x : ↥K ⧸ Subgroup.center ↥K) ∈ Sec4.autFix β →
      ∃ z ∈ Subgroup.center ↥K, b * (x : _) * b⁻¹ = (x : _) * (z : _) := by
    intro x hx
    have h1 : β (x : ↥K ⧸ Subgroup.center ↥K) = x := hx
    rw [hβx, QuotientGroup.eq] at h1
    refine ⟨x⁻¹ * ⟨b * (x : _) * b⁻¹, (Subgroup.mem_normalizer_iff.mp hbK x).mp x.2⟩, ?_, ?_⟩
    · have h2 := Subgroup.inv_mem _ h1
      rwa [mul_inv_rev, inv_inv] at h2
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
  have hcb : ∀ y, b * y * b⁻¹ = y → y ∈ Subgroup.centralizer ({b} : Set _) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * b = b * y * b⁻¹ * b := by rw [hy]
      _ = b * y := by group
  have hcb' : ∀ y, y ∈ Subgroup.centralizer ({b} : Set _) → b * y * b⁻¹ = y := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [← hy, mul_inv_cancel_right]
  set D : Subgroup (↥K ⧸ Subgroup.center ↥K) :=
    ((Subgroup.centralizer ({b} : Set _)).subgroupOf K).map
      (QuotientGroup.mk' (Subgroup.center ↥K)) with hD
  have hD1 : D ≤ Sec4.autFix β := by
    rintro _ ⟨k, hk, rfl⟩
    change β (k : ↥K ⧸ Subgroup.center ↥K) = k
    rw [hβx]
    congr 1
    exact Subtype.ext (hcb' _ hk)
  have hD2 : (D.subgroupOf (Sec4.autFix β)).Normal := by
    refine ⟨fun d hd y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    obtain ⟨k, hk, hkd⟩ := hd
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (y : ↥K ⧸ Subgroup.center ↥K)
    have hxfix : (x : ↥K ⧸ Subgroup.center ↥K) ∈ Sec4.autFix β := by
      change QuotientGroup.mk x ∈ _
      rw [hx]
      exact y.2
    obtain ⟨z, hz, hxz⟩ := hfix x hxfix
    have hk' : b * ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * b⁻¹ =
        ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) := hcb' _ hk
    have hzk : ((z : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) =
        ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * ((z : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) := by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz k).symm
      simpa only [Subgroup.coe_mul] using this
    have hmem : ((x * k * x⁻¹ : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) ∈
        Subgroup.centralizer ({b} : Set _) := by
      apply hcb
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      have e1 : b * (((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) *
            ((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C)⁻¹) * b⁻¹ =
          (b * ((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * b⁻¹) *
            (b * ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * b⁻¹) *
            (b * ((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * b⁻¹)⁻¹ := by group
      rw [e1, hxz, hk']
      calc ((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * ((z : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) *
            ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) *
            (((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * ((z : ↥K) : C ⧸ CFSG.pPrimeCore 3 C))⁻¹
          = ((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) *
              (((z : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C)) *
              ((z : ↥K) : C ⧸ CFSG.pPrimeCore 3 C)⁻¹ * ((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C)⁻¹ := by
            group
        _ = ((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) *
              (((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * ((z : ↥K) : C ⧸ CFSG.pPrimeCore 3 C)) *
              ((z : ↥K) : C ⧸ CFSG.pPrimeCore 3 C)⁻¹ * ((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C)⁻¹ := by
            rw [hzk]
        _ = ((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) *
              ((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C)⁻¹ := by group
    refine ⟨x * k * x⁻¹, hmem, ?_⟩
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv]
      rw [show (QuotientGroup.mk' (Subgroup.center ↥K)) k = (k : ↥K ⧸ Subgroup.center ↥K)
        from rfl] at hkd
      change (x : ↥K ⧸ Subgroup.center ↥K) * k * (x : ↥K ⧸ Subgroup.center ↥K)⁻¹ =
        (y : ↥K ⧸ Subgroup.center ↥K) * (d : ↥K ⧸ Subgroup.center ↥K) *
          (y : ↥K ⧸ Subgroup.center ↥K)⁻¹
      rw [hkd]
      change QuotientGroup.mk x * _ * (QuotientGroup.mk x)⁻¹ = _
      rw [hx]
  have hD3 : ∀ y ∈ Sec4.autFix β, ∃ n : ℕ, y ^ (3 ^ n) ∈ D := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨z, hz, hxz⟩ := hfix x hy
    obtain ⟨m, hm⟩ := hZ3 ⟨z, hz⟩
    have hz' : (z : ↥K) ^ (3 ^ m) = 1 := by
      have := congrArg (fun t : Subgroup.center ↥K => (t : ↥K)) hm
      simpa using this
    have hzx : Commute ((x : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) ((z : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) := by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz x)
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at this
      exact this
    have hz'' : ((z : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) ^ (3 ^ m) = 1 := by
      rw [← Subgroup.coe_pow, hz', Subgroup.coe_one]
    have hmem : ((x ^ (3 ^ m) : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) ∈
        Subgroup.centralizer ({b} : Set _) := by
      apply hcb
      rw [Subgroup.coe_pow, ← conj_pow, hxz, hzx.mul_pow, hz'', mul_one]
    refine ⟨m, ⟨x ^ (3 ^ m), hmem, ?_⟩⟩
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk_pow]
  set ι := (descAut K).comp (Subgroup.inclusion hPK) with hι
  have hKX : IsKGroup (C ⧸ CFSG.pPrimeCore 3 C) :=
    CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient hC.kGroup _
  have hPKg : IsKGroup ↥ι.range :=
    (hKX.subgroup P).of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  have hPβ : ι.range ≤ Subgroup.centralizer {β} := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxb : (x : _) * b = b * (x : _) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPb x.2)
    rw [hβ, hι, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxb
  have hPN' : ∀ d ∈ D, MulAut.conj d ∈ Subgroup.normalizer (ι.range : Set _) := by
    rintro _ ⟨k, hk, rfl⟩
    have hkK : ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) ∈ K := k.2
    have hkN : ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) ∈ Subgroup.normalizer (K : Set _) :=
      Subgroup.le_normalizer hkK
    have hkP : ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) ∈ Subgroup.normalizer (P : Set _) :=
      hPN ⟨hk, hkN⟩
    have hconj : MulAut.conj ((k : ↥K) : ↥K ⧸ Subgroup.center ↥K) = descAut K ⟨k, hkN⟩ :=
      (descAut_of_mem K hkK hkN).symm
    rw [QuotientGroup.mk'_apply, hconj]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      have hx' : ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C) * (x : C ⧸ CFSG.pPrimeCore 3 C) *
          ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C)⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp hkP x).mp x.2
      refine ⟨⟨_, hx'⟩, ?_⟩
      rw [hι, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
    · rintro ⟨x, hx⟩
      have hkinv : ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C)⁻¹ ∈ Subgroup.normalizer (P : Set _) :=
        inv_mem hkP
      have hx' : ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C)⁻¹ * (x : C ⧸ CFSG.pPrimeCore 3 C) *
          ((k : ↥K) : C ⧸ CFSG.pPrimeCore 3 C)⁻¹⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp hkinv x).mp x.2
      refine ⟨⟨_, hx'⟩, ?_⟩
      have h1 : y = (descAut K ⟨k, hkN⟩)⁻¹ * ι x * descAut K ⟨k, hkN⟩ := by
        rw [hx]
        group
      rw [h1, hι, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp
  have hPp' : Group.IsPerfect ↥ι.range := by
    haveI := hPp
    exact Group.IsPerfect.range ι
  have hP3' : ¬ 3 ∣ Nat.card ↥ι.range := fun h =>
    hP3 (h.trans (Subgroup.card_range_dvd ι))
  have hbot := hrow β hβ3 hβ1 D hD1 hD2 hD3 ι.range hPKg hPβ hPN' hPp' hP3'
  intro x hx
  have h1 : ι ⟨x, hx⟩ = 1 := by
    have : ι ⟨x, hx⟩ ∈ ι.range := ⟨⟨x, hx⟩, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  exact (descAut_eq_one_iff hKp _).mp h1

theorem ks143LBalComp2_of_k143Rows
    (h1 : Sec4.Item4_1LargePrime) (R : K143Rows) : KS143LBalComp2 :=
  ks143LBalComp2_of_rows h1 fun _ _ _ hs hnc hL h3 => R.row_of_list42 hs hnc hL h3

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
