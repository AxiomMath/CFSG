module

public import CFSG.RankThree.PartTwo.Sec21.FF84S31Vstar
public import CFSG.RankThree.PartTwo.Sec21.FF84S3BCoprime
public import CFSG.RankThree.PartTwo.Sec21.FF84S3Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG
open scoped commutatorElement

@[expose] def A8TJStmt : Prop :=
  ∃ T J : Subgroup P8, T ≤ A8s ∧ J ≤ A8s ∧ IsElemAb 2 3 T ∧ J ≤ Nor T ∧ IsSimpleGroup J ∧
    Nat.card J = 168 ∧ m₁ ∈ J ∧
    ∀ y ∈ J, orderOf y = 3 → ∃ j ∈ J, j * m₁ * j⁻¹ = y

section Lift

variable {G : Type} [Group G] {L : Subgroup G} {θ : G → P8}

@[expose] def preL (P : PreTheta L θ) (K : Subgroup P8) : Subgroup G where
  carrier := {x | x ∈ L ∧ θ x ∈ K}
  mul_mem' := by
    rintro a c ⟨haL, haK⟩ ⟨hcL, hcK⟩
    refine ⟨L.mul_mem haL hcL, ?_⟩
    rw [P.mul a (Subgroup.le_normalizer haL) c (Subgroup.le_normalizer hcL)]
    exact K.mul_mem haK hcK
  one_mem' := ⟨L.one_mem, by rw [P.one]; exact K.one_mem⟩
  inv_mem' := by
    rintro a ⟨haL, haK⟩
    refine ⟨L.inv_mem haL, ?_⟩
    rw [P.inv (Subgroup.le_normalizer haL)]
    exact K.inv_mem haK

variable (P : PreTheta L θ) (K : Subgroup P8)

theorem preL_le_nor : preL P K ≤ Nor L := fun _ hx => Subgroup.le_normalizer hx.1

@[expose] def preLhom : ↥(preL P K) →* P8 where
  toFun x := θ (x : G)
  map_one' := P.one
  map_mul' a c := P.mul a (preL_le_nor P K a.2) c (preL_le_nor P K c.2)

variable {P K}

theorem sq_of_ker (hZ : ∀ z ∈ L, z ∈ CenS L → z ^ 2 = 1) {z : G} (hzL : z ∈ L) (hz : θ z = 1)
    (P : PreTheta L θ) : z ^ 2 = 1 :=
  hZ z hzL ((P.ker z (Subgroup.le_normalizer hzL)).1 hz)

theorem lemmaF_via [Finite G] (hF : LemmaF) (P : PreTheta L θ)
    (hZ : ∀ z ∈ L, z ∈ CenS L → z ^ 2 = 1) (K : Subgroup P8) (hKA : K ≤ A8s)
    (hK : IsSimpleGroup K) (hKc : Nat.card K = 168) {y : G} (hyJ : y ∈ preL P K)
    (hy3 : orderOf y = 3) {X N : Subgroup G} (hX : IsPGroup 2 X) (hNX : N ≤ X)
    (hNn : (N.subgroupOf X).Normal) (hJX : preL P K ≤ Nor X) (hJN : preL P K ≤ Nor N)
    (hfpf : ∀ x ∈ X, (∃ n ∈ N, y * x * y⁻¹ = x * n) → x ∈ N) : X ≤ N := by
  set J := preL P K with hJ
  let φ : ↥J →* P8 := preLhom P K
  let Z : Subgroup G := φ.ker.map J.subtype
  have hZJ : Z ≤ J := Subgroup.map_subtype_le _
  have hZsub : Z.subgroupOf J = φ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨k, hk, hkx⟩
      have : k = x := Subtype.ext hkx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  haveI hZn : (Z.subgroupOf J).Normal := by
    rw [hZsub]
    exact φ.normal_ker
  have hZ2 : IsPGroup 2 Z := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.1 g.2
    have h1 : θ (k : G) = 1 := hk
    have : (k : G) ^ 2 = 1 := sq_of_ker hZ k.2.1 h1 P
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hkg]
    simpa using this
  let φ' : ↥J →* ↥K := φ.codRestrict K (fun x => x.2.2)
  have hker : φ'.ker = Z.subgroupOf J := by
    rw [hZsub]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff]
    exact Iff.rfl
  have hsurj : Function.Surjective φ' := by
    rintro ⟨k, hk⟩
    obtain ⟨x, hxL, hx⟩ := P.surj k (hKA hk)
    refine ⟨⟨x, hxL, hx ▸ hk⟩, ?_⟩
    apply Subtype.ext
    exact hx
  let e : (↥J ⧸ Z.subgroupOf J) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ' hsurj)
  haveI := hK
  have hs : IsSimpleGroup (↥J ⧸ Z.subgroupOf J) := e.isSimpleGroup
  have hc : Nat.card (↥J ⧸ Z.subgroupOf J) = 168 := by
    rw [Nat.card_congr e.toEquiv]
    exact hKc
  exact hF G J Z X N y hZJ hZ2 hs hc hyJ hy3 hX hNX hNn hJX hJN hfpf

end Lift

section Eq

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem isSylowOf_ofABG {p : ℕ} [Fact p.Prime] {P H : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p P H) : IsSylowOf p P H := by
  obtain ⟨a, b, c⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 h
  exact ⟨a, b, (Nat.Prime.coprime_iff_not_dvd Fact.out).2 c⟩

theorem mem_Nor_Op (p : ℕ) {H : Subgroup G} {g : G} (hg : g ∈ Nor H) : g ∈ Nor (Op p H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => Op_conj_mem p hg hy, fun hy => ?_⟩
  have := Op_conj_mem p (Subgroup.inv_mem _ hg) hy
  simpa [mul_assoc] using this

theorem V_le_Vstar {V : Subgroup G} (hV2 : IsPGroup 2 V) : V ≤ Op 2 (Nor V) :=
  le_Op_of_normal 2 (Nor V) V Subgroup.le_normalizer hV2
    (fun n hn m hm => (Subgroup.mem_normalizer_iff.1 hn m).1 hm)

theorem Z_Vstar_eq (hF : LemmaF) (hA7 : A7TauStmt) (hA8 : A8TJStmt)
    (hZ : Nat.card (Subgroup.center L) ∣ 2) (h : FF84Sec3 b L B b₁ b₂) (V : Subgroup G)
    (hV : IsSylowOf 2 V (Opp 3 (Cen b))) : Op 2 (Nor V) = V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, H⟩ := exists_theta h hZ
  have P : PreTheta L θ := H.toPreTheta
  obtain ⟨T, K, hTA, hKA, -, -, hKs, hKc, hm₁, -⟩ := hA8
  have hV2 : IsPGroup 2 V := hV.2.1
  have hVX : V ≤ Opp 3 (Cen b) := hV.1
  have hLV := L_le_Nor_of_le_X h hVX
  have hVs := V_le_Vstar hV2
  have hX2 : IsPGroup 2 (Op 2 (Nor V)) := Op_isPGroup 2 (Nor V)
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₁J : b₁ ∈ preL P K := ⟨hb₁L, by rw [H.hb₁]; exact hm₁⟩
  have hVn : (V.subgroupOf (Op 2 (Nor V))).Normal :=
    normal_subgroupOf_of_conj hVs
      (fun n hn m hm => (Subgroup.mem_normalizer_iff.1 (Op_le 2 _ hn) m).1 hm)
  have hJX : preL P K ≤ Nor (Op 2 (Nor V)) := fun j hj =>
    mem_Nor_Op 2 (Subgroup.le_normalizer (hLV (hj.1)))
  have hJN : preL P K ≤ Nor V := fun j hj => hLV hj.1
  have hb₁ord := orderOf_b₁ h
  have hb₁X : b₁ ∈ Nor (Op 2 (Nor V)) := hJX hb₁J
  have hb₁N : b₁ ∈ Nor V := hJN hb₁J
  have hfpf : ∀ x ∈ Op 2 (Nor V), (∃ n ∈ V, b₁ * x * b₁⁻¹ = x * n) → x ∈ V := by
    intro x hx hxn
    obtain ⟨q, hq, n', hn', rfl⟩ := B_coprime_quot 2 (Op 2 (Nor V)) V b₁ hX2 hVs hVn hb₁X hb₁N
      (by rw [hb₁ord]; omega) x hx hxn
    have hqV : q ∈ V := by
      rw [← Z_Vstar_b₁ hA7 hZ h V hV]
      exact hq
    exact V.mul_mem hqV hn'
  have hle := lemmaF_via hF P (fun z hz hzC => center_sq hZ hz hzC) K hKA hKs hKc hb₁J hb₁ord hX2
    hVs hVn hJX hJN hfpf
  exact le_antisymm hle hVs

theorem Z_odd (hF : LemmaF) (hA7 : A7TauStmt) (hA8 : A8TJStmt)
    (hZ : Nat.card (Subgroup.center L) ∣ 2) (h : FF84Sec3 b L B b₁ b₂) :
    Odd (Nat.card (Opp 3 (Cen b))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have heven : 2 ∣ Nat.card (Opp 3 (Cen b)) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨V', hV'⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (Opp 3 (Cen b))
  have hV := isSylowOf_ofABG hV'
  have hcard := hV'.card_eq
  have hpos : 0 < (Nat.card (Opp 3 (Cen b))).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' heven
  have hV1 : V' ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    have : 2 ≤ 2 ^ (Nat.card (Opp 3 (Cen b))).factorization 2 :=
      Nat.le_self_pow hpos.ne' 2
    omega
  have hV2 : IsPGroup 2 V' := hV.2.1
  have hVX : V' ≤ Opp 3 (Cen b) := hV.1
  have heq := Z_Vstar_eq hF hA7 hA8 hZ h V' hV
  have hBN : B ≤ Nor V' := fun β hβ =>
    mem_Nor_of_comm (fun w hw => Subgroup.mem_centralizer_iff.1 (X_le_CenS_B h (hVX hw)) β hβ)
  have hBC : B ≤ CenS (Op 2 (Nor V')) := by
    rw [heq]
    intro β hβ
    exact Subgroup.mem_centralizer_iff.2 (fun w hw =>
      (Subgroup.mem_centralizer_iff.1 (X_le_CenS_B h (hVX hw)) β hβ).symm)
  have hbV : b ∈ Op 2 (Nor V') :=
    B_charTwo h.hyp.char2 V' hV1 hV2 (Subgroup.mem_inf.2 ⟨hBN (mem_B_b h), hBC (mem_B_b h)⟩)
  rw [heq] at hbV
  exact not_isPGroup_two_of_orderOf_three hbV h.hyp.ord hV2

end Eq

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
