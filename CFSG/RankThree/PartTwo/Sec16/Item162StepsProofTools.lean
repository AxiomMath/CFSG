module

public import CFSG.RankThree.PartTwo.Sec16.Item162Proof
public import CFSG.RankThree.PartTwo.Sec15.Item153
public import CFSG.RankThree.PartTwo.Sec15.Item1512
public import CFSG.RankThree.PartTwo.Sec15.Item15More
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof162

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem bot_mem_scriptQPi_two (Y : Subgroup G) :
    (⊥ : Subgroup G) ∈ scriptQPi A (lB A) Y (piOf 2) := by
  refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
    (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
  rw [bot_inf_eq]
  exact bot_le

theorem normalizer_le_normalizer_x (h153 : Item153Main A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) :
    Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNle : Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) hY.prop.2.2
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hYA : ((Y ⊔ A : Subgroup G) : Set G) ⊆ M := fun x hx =>
    hle (sup_le (Subgroup.le_normalizer.trans hNle) (hY.prop.1.1.2.trans hNle) hx)
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := ⟨hM, hYA⟩
  rw [(h153 Y hY).1, Set.mem_singleton_iff] at hMm
  exact (hNle.trans hle).trans hMm.le

theorem mem_qStarX_of_mem_qStarN (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2)) :
    S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G))
      (piOf 2) := by
  have hNX := normalizer_le_normalizer_x h153 hY
  have hSX : S ∈ scriptQPi A (lB A) (Subgroup.normalizer
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G))
      (piOf 2) := ⟨⟨hS.prop.1.1, hS.prop.1.2.trans hNX⟩, hS.prop.2⟩
  obtain ⟨S', hSS', hS'⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G))
      (piOf 2))) hSX
  have hS'mem : S' ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2) :=
    ⟨⟨hS'.prop.1.1, hobs Y hY S' hS'⟩, hS'.prop.2⟩
  have heq : S' = S := le_antisymm (hS.2 hS'mem hSS') hSS'
  exact heq ▸ hS'

theorem mem_qStarTop_of_mem_qStarN (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2)) :
    S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) :=
  ((h153 Y hY).2.1 S (mem_qStarX_of_mem_qStarN h153 hobs hY hS)).1

theorem normalizer_sup_le (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (hn : Claim153Normal A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2)) :
    Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
  have h3 := ((h153 Y hY).2.1 S (mem_qStarX_of_mem_qStarN h153 hobs hY hS)).2
  have hmem : Subgroup.normalizer
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [(h153 Y hY).1]
    exact Set.mem_singleton _
  exact h3.trans (hn Y hY _ hmem)

theorem normalizer_inf_le (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (hn : Claim153Normal A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2)) :
    Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Y : Set G) :=
  (Sec14.le_normalizer_sup inf_le_left inf_le_right).trans (normalizer_sup_le h153 hobs hn hY hS)

theorem exists_conj_mem_qStarN (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (h1411 : Item1411_1 A (lB A)) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) :
    ∃ w ∈ Subgroup.normalizer (A : Set G), S ∈ scriptQPiStar A (lB A)
      (Subgroup.normalizer ((Y.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G))
      (piOf 2) := by
  obtain ⟨S₀, -, hS₀⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2)))
    (bot_mem_scriptQPi_two (A := A) _)
  obtain ⟨w, hw, rfl⟩ := h1411 S₀ (mem_qStarTop_of_mem_qStarN h153 hobs hY hS₀) S hS
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
  refine ⟨w, hwA, ?_⟩
  have h := Sec17.HeadProof.map_conj_mem_scriptQPiStar hwA hS₀
  rwa [Subgroup.map_equiv_normalizer_eq] at h

omit [Finite G] in
theorem mem_of_mem_sup_of_pow_three_pow {P K : Subgroup G}
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P ⊔ K)
    {n : ℕ} (hxn : x ^ 3 ^ n = 1) : x ∈ K := by
  have hx' : x ∈ (P : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right P K hPK]
    exact hx
  obtain ⟨p, hp, k, hk, rfl⟩ := Set.mem_mul.mp hx'
  have hpow : ∀ m : ℕ, ∃ t ∈ K, (p * k) ^ m = p ^ m * t := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ m ih =>
      obtain ⟨t, ht, he⟩ := ih
      have hpt : p⁻¹ * t * p⁻¹⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hPK (inv_mem hp)) t).mp ht
      refine ⟨(p⁻¹ * t * p⁻¹⁻¹) * k, mul_mem hpt hk, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨t, ht, he⟩ := hpow (3 ^ n)
  rw [hxn] at he
  have hpK : p ^ 3 ^ n ∈ K := by
    have h1 : p ^ 3 ^ n = t⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact he.symm
    rw [h1]
    exact inv_mem ht
  have hcop : Nat.Coprime (3 ^ n) (orderOf p) := by
    obtain ⟨j, hj⟩ := hP ⟨p, hp⟩
    have hj' : p ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hj')
      (Nat.Coprime.pow n j (by norm_num))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hpK' : p ∈ K := by
    rw [← hm]
    exact pow_mem hpK m
  exact mul_mem hpK' hk

omit [Finite G] in
theorem le_of_le_sup_of_isPGroup_two {P K Z : Subgroup G}
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hP : IsPGroup 2 P) (hZ : Z ≤ P ⊔ K)
    (hZ3 : Z = oPrimeResidualOf 3 Z) : Z ≤ K := by
  rw [hZ3, Sec14.oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro x ⟨hx, n, hn⟩
  exact mem_of_mem_sup_of_pow_three_pow hPK hP (hZ hx) hn

omit [Finite G] in
theorem not_isSolvable_of_mem_scriptY4 {LB : Subgroup G → Subgroup G} {Y : Subgroup G}
    (hY : Y ∈ scriptY4 A LB) : ¬ Group.IsSolvable ↥Y := by
  intro hsol
  obtain ⟨-, -, -, hq⟩ := hY
  have hperf : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y) := hq.1
  have hnt : Nontrivial (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    have hne : a ≠ b := fun h => hab (by rw [h])
    have : Nontrivial ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸
        Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) := nontrivial_of_ne a b hne
    exact (QuotientGroup.mk'_surjective (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))).nontrivial
  have := hsol
  exact Group.IsPerfect.not_isSolvable (↥Y ⧸ CFSG.pCore 2 ↥Y) inferInstance

theorem conj_of_card_lt {LB : Subgroup G → Subgroup G} {Y₁ Y₂ S₁ S₂ : Subgroup G}
    (hmax : MaxCE162 A LB Y₁ Y₂ S₁ S₂) {Y₁' Y₂' S₁' S₂' : Subgroup G}
    (h₁ : Y₁' ∈ scriptY0Star A LB) (h₂ : Y₂' ∈ scriptY0Star A LB)
    (hs₁ : S₁' ∈ scriptQPiStar A LB (Subgroup.normalizer (Y₁' : Set G)) (piOf 2))
    (hs₂ : S₂' ∈ scriptQPiStar A LB (Subgroup.normalizer (Y₂' : Set G)) (piOf 2))
    (hlt : Nat.card (S₁ ⊓ S₂ : Subgroup G) < Nat.card (S₁' ⊓ S₂' : Subgroup G)) :
    ∃ x ∈ xA A, Y₁' = Y₂'.map (MulAut.conj x).toMonoidHom := by
  by_contra hnc
  have hne : S₁' ⊓ S₂' ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hlt
    have hpos : 0 < Nat.card (S₁ ⊓ S₂ : Subgroup G) := Nat.card_pos
    omega
  exact absurd (hmax.2 Y₁' Y₂' S₁' S₂' ⟨h₁, h₂, hs₁, hs₂, hne, hnc⟩) (not_le.mpr hlt)

omit [Finite G] in
theorem xA_le_normalizer (A : Subgroup G) : xA A ≤ Subgroup.normalizer (A : Set G) :=
  (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)

omit [Finite G] in
theorem conj_trans {Y₁ Y₂ Y₃ : Subgroup G} {x y : G} (hx : x ∈ xA A) (hy : y ∈ xA A)
    (h₁ : Y₁ = Y₂.map (MulAut.conj x).toMonoidHom) (h₂ : Y₂ = Y₃.map (MulAut.conj y).toMonoidHom) :
    ∃ z ∈ xA A, Y₁ = Y₃.map (MulAut.conj z).toMonoidHom :=
  ⟨x * y, mul_mem hx hy, by rw [h₁, h₂, Late.map_conj_map_conj]⟩

omit [Finite G] in
theorem conj_symm {Y₁ Y₂ : Subgroup G} {x : G} (hx : x ∈ xA A)
    (h : Y₁ = Y₂.map (MulAut.conj x).toMonoidHom) :
    ∃ z ∈ xA A, Y₂ = Y₁.map (MulAut.conj z).toMonoidHom :=
  ⟨x⁻¹, inv_mem hx, by rw [h, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]⟩

theorem not_conj_normalizer {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (hn : Claim153Normal A (lB A))
    (hW : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y)
    {Y₁ Y₂ S : Subgroup G} (hce : CE162 A (lB A) Y₁ Y₂ S S) :
    ¬ ∃ g ∈ Subgroup.normalizer (A : Set G), Y₂ = Y₁.map (MulAut.conj g).toMonoidHom := by
  rintro ⟨g, hg, hgY⟩
  have hY₂0 : Y₂ ∈ scriptY0 A (lB A) := hce.mem₂.prop
  have hNY₂ : Subgroup.normalizer (Y₂ : Set G) ∈ scriptY A :=
    normalizer_mem_scriptY h.isSimpleGroup hY₂0.1.1 (ne_bot_of_mem_scriptY0 hY₂0)
  set D := delta A (lB A) (Subgroup.normalizer (Y₂ : Set G)) with hD
  have hDY : D ∈ scriptY A := by
    refine ⟨fun htop => hNY₂.1 (top_le_iff.mp ?_), le_normalizer_sSup fun Q hQ => hQ.1.1.2.2⟩
    rw [← htop]
    exact delta_le _
  have hDΔ : D = delta A (lB A) D := (delta_delta _).symm
  have hY₂D : Y₂ ≤ D :=
    calc Y₂ = delta A (lB A) Y₂ := hY₂0.1.2.2.1
      _ ≤ D := delta_mono Subgroup.le_normalizer
  have hDsol : ¬ Group.IsSolvable ↥D := fun hsol => by
    have := hsol
    exact not_isSolvable_of_mem_scriptY4 hY₂0.1
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hY₂D))
  have htr := hW D hDΔ hDY hDsol
  have hSg : S.map (MulAut.conj g).toMonoidHom ∈
      scriptQPiStar A (lB A) (Subgroup.normalizer (Y₂ : Set G)) (piOf 2) := by
    have h1 := Sec17.HeadProof.map_conj_mem_scriptQPiStar hg hce.s₁
    rwa [Subgroup.map_equiv_normalizer_eq, ← hgY] at h1
  have hS₂ : S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Y₂ : Set G)) (piOf 2) := hce.s₂
  rw [← scriptQPiStar_delta] at hSg hS₂
  obtain ⟨y, hy, hyS⟩ := htr _ hSg _ hS₂
  rw [Late.map_conj_map_conj] at hyS
  have hyg : y * g ∈ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G) :=
    ⟨mul_mem (Subgroup.mem_inf.mp hy).1 hg, mem_normalizer_of_map_conj_eq hyS.symm⟩
  have hygY : y * g ∈ Subgroup.normalizer (Y₂ : Set G) :=
    normalizer_inf_le h153 hobs hn hce.mem₂ hce.s₂ hyg
  have hyY : y ∈ Subgroup.normalizer (Y₂ : Set G) := delta_le _ (Subgroup.mem_inf.mp hy).2
  have hgN : g ∈ Subgroup.normalizer (Y₂ : Set G) := by
    have h1 := mul_mem (inv_mem hyY) hygY
    rwa [inv_mul_cancel_left] at h1
  have hY₁ : Y₁ = Y₂ := by
    have h1 := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgY
    rw [Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one,
      Late.map_conj_eq_of_mem_normalizer (inv_mem hgN)] at h1
    exact h1.symm
  exact hce.not_conj ⟨1, one_mem _, by rw [Late.map_conj_one, hY₁]⟩

theorem eq_of_le_normalizer_of_mem_scriptY4 {LB : Subgroup G → Subgroup G}
    {K₁ K₂ X : Subgroup G} (h₁ : K₁ ∈ scriptY0Star A LB) (h₂ : K₂ ∈ scriptY0 A LB)
    (hX : X ∈ scriptY4 A LB) (hX₁ : X ≤ K₁) (hX₂ : X ≤ K₂)
    (hN : K₁ ≤ Subgroup.normalizer (K₂ : Set G)) : K₁ = K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 K₁) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K₁
  have hON : CFSG.Open.pCoreOf 2 K₁ ≤ Subgroup.normalizer (K₂ : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans hN
  suffices hle : K₁ ≤ CFSG.Open.pCoreOf 2 K₁ ⊔ K₂ from
    h₁.eq_of_le h₂ (le_of_le_sup_of_isPGroup_two hON hO2 hle h₁.prop.1.2.1)
  set P := CFSG.pCore 2 ↥K₁ with hP
  have hq : CFSG.IsQuasisimple (↥K₁ ⧸ P) := h₁.prop.1.2.2.2
  set D := (K₁ ⊓ K₂).subgroupOf K₁ with hD
  have hDn : D.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (Late.le_normalizer_inf Subgroup.le_normalizer hN)
  have hDmap : (D.map (QuotientGroup.mk' P)).Normal :=
    hDn.map (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
      (D.map (QuotientGroup.mk' P)) with hc | ht
  ·
    exfalso
    apply not_isSolvable_of_mem_scriptY4 hX
    set X' := X.subgroupOf K₁ with hX'
    set φ : ↥X' →* ↥K₁ ⧸ P := (QuotientGroup.mk' P).comp X'.subtype with hφ
    have hcen : ∀ x : ↥X', φ x ∈ Subgroup.center (↥K₁ ⧸ P) := by
      intro x
      refine hc ⟨(x : ↥K₁), ?_, rfl⟩
      have hxX : ((x : ↥K₁) : G) ∈ X := Subgroup.mem_subgroupOf.mp x.2
      exact Subgroup.mem_subgroupOf.mpr ⟨(x : ↥K₁).2, hX₂ hxX⟩
    have hcomm : ∀ a b : ↥φ.range, a * b = b * a := by
      rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hcen y) (φ x))
    have hsolR : Group.IsSolvable ↥φ.range := Group.isSolvable_of_comm hcomm
    have hker2 : IsPGroup 2 ↥φ.ker := by
      intro k
      have hkP : ((k : ↥X') : ↥K₁) ∈ P := by
        have hk := k.2
        rw [MonoidHom.mem_ker] at hk
        exact (QuotientGroup.eq_one_iff _).mp hk
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K₁) ⟨_, hkP⟩
      have h1 : ((k : ↥X') : ↥K₁) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      simpa using h1
    have hnil : Group.IsNilpotent ↥φ.ker := hker2.isNilpotent
    have hsolX' : Group.IsSolvable ↥X' :=
      Group.isSolvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict
        (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hX₁).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hX₁).symm.injective
  ·
    intro k hk
    have hkmem : QuotientGroup.mk' P (⟨k, hk⟩ : ↥K₁) ∈ D.map (QuotientGroup.mk' P) := by
      rw [ht]
      exact Subgroup.mem_top _
    obtain ⟨d, hd, hdk⟩ := Subgroup.mem_map.mp hkmem
    have hdk' : ((d : ↥K₁) : ↥K₁ ⧸ P) = ((⟨k, hk⟩ : ↥K₁) : ↥K₁ ⧸ P) := hdk
    have hdP : d⁻¹ * ⟨k, hk⟩ ∈ P := QuotientGroup.eq.mp hdk'
    have hdG : (d : G) ∈ K₂ := (Subgroup.mem_subgroupOf.mp hd).2
    have hpG : ((d⁻¹ * ⟨k, hk⟩ : ↥K₁) : G) ∈ CFSG.Open.pCoreOf 2 K₁ := by
      have h' : d⁻¹ * ⟨k, hk⟩ ∈ CFSG.Open.pCore 2 ↥K₁ := by
        exact hdP
      exact Subgroup.mem_map_of_mem K₁.subtype h'
    have hk' : k = (d : G) * ((d⁻¹ * ⟨k, hk⟩ : ↥K₁) : G) := by simp
    rw [hk']
    exact mul_mem (Subgroup.mem_sup_right hdG) (Subgroup.mem_sup_left hpG)

theorem eq_of_mem_gam155 (h155 : Item155 A (lB A)) (h153 : Item153Main A (lB A))
    {Y K₁ K₂ : Subgroup G} (hY : Y ∈ scriptY3 A (lB A))
    (hX : oPrimeResidualOf 3 Y ∈ scriptY4 A (lB A))
    (hcov : Y = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 Y)
    (hK₁ : K₁ ∈ gam155 A (lB A) Y (oPrimeResidualOf 3 Y))
    (hK₂ : K₂ ∈ gam155 A (lB A) Y (oPrimeResidualOf 3 Y))
    (hside : omg155 A (oPrimeResidualOf 3 Y) ∨
      K₂ = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 K₂) : K₁ = K₂ := by
  obtain ⟨hK₁0, hXK₁, hYK₁⟩ := hK₁
  have hNX := normalizer_le_normalizer_x h153 hK₁0
  have hMmax : Subgroup.normalizer
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (K₁ : Set G))) : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((K₁ ⊔ A : Subgroup G) : Set G) := by
    rw [(h153 K₁ hK₁0).1]
    exact Set.mem_singleton _
  have hMY : Subgroup.normalizer
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (K₁ : Set G))) : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G) :=
    ⟨hMmax.1, fun x hx => hNX (sup_le hK₁0.prop.1.1.2 hYK₁ hx)⟩
  have hΔ := (h155 Y hY hX hcov).2 K₂ hK₂ hside _ hMY
  have hK₁N : K₁ ≤ Subgroup.normalizer (K₂ : Set G) :=
    calc K₁ = delta A (lB A) K₁ := hK₁0.prop.1.2.2.1
      _ ≤ _ := delta_mono (Subgroup.le_normalizer.trans hNX)
      _ ≤ _ := hΔ
  exact eq_of_le_normalizer_of_mem_scriptY4 hK₁0 hK₂.1.prop hX hXK₁ hK₂.2.1 hK₁N

end CFSG.RankThree.PartTwo.Sec16.Proof162
