module

public import CFSG.RankThree.PartTwo.Sec20.OneStepsProof
public import CFSG.RankThree.PartTwo.Sec20.KFactL3OddRank
import CFSG.RankThree.PartTwo.Sec18.Item181b
public import CFSG.RankThree.PartTwo.Sec20.OneStepsProofX

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.LowTwoRank (StatedSL)

theorem mem_zpowers_of_commute_sl3 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hq : Nat.card F % 3 = 2) {a b : Matrix.SpecialLinearGroup (Fin 3) F}
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hab : a * b = b * a) :
    b ∈ Subgroup.zpowers a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F with he
  set a' : GL (Fin 3) F := ((e a : StatedSL 3 F) : GL (Fin 3) F) with ha'
  set b' : GL (Fin 3) F := ((e b : StatedSL 3 F) : GL (Fin 3) F) with hb'
  have hcomm : a' * b' = b' * a' := by
    rw [ha', hb', ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab]
  set E : Subgroup (GL (Fin 3) F) := Subgroup.closure {a', b'} with hE
  have hES : E ≤ StatedSL 3 F := by
    rw [hE, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact (e a).2
    · exact (e b).2
  have hpair : ({a', b'} : Set (GL (Fin 3) F)).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hcomm
    · exact hcomm.symm
    · exact Commute.refl _
  have hEc : IsMulCommutative E := Subgroup.isMulCommutative_closure hpair
  have ha'3 : a' ^ 3 = 1 := by
    rw [ha', ← Subgroup.coe_pow, ← map_pow, ha3, map_one, Subgroup.coe_one]
  have hb'3 : b' ^ 3 = 1 := by
    rw [hb', ← Subgroup.coe_pow, ← map_pow, hb3, map_one, Subgroup.coe_one]
  have hE3 : ∀ y ∈ E, y ^ 3 = 1 := by
    intro y hy
    refine Subgroup.closure_induction (p := fun x hx => x ^ 3 = 1) ?_ ?_ ?_ ?_ hy
    · rintro x (rfl | rfl)
      · exact ha'3
      · exact hb'3
    · exact one_pow 3
    · intro x w hx hw ihx ihw
      have hxw : Commute x w := congrArg Subtype.val (hEc.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
      rw [hxw.mul_pow, ihx, ihw, one_mul]
    · intro x _ ihx
      rw [inv_pow, ihx, inv_one]
  have hcard := card_le_three_of_isElemAbelian hq hES ⟨hEc, hE3⟩
  have ha'1 : a' ≠ 1 := by
    intro h
    apply ha1
    apply e.injective
    rw [map_one]
    exact Subtype.ext h
  have hord : orderOf a' = 3 := orderOf_eq_prime ha'3 ha'1
  have hle : Subgroup.zpowers a' ≤ E :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
  have heq : Subgroup.zpowers a' = E :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord]; exact hcard)
  have hb'E : b' ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  rw [← heq, Subgroup.mem_zpowers_iff] at hb'E
  obtain ⟨k, hk⟩ := hb'E
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, e.injective ?_⟩
  apply Subtype.ext
  rw [map_zpow, Subgroup.coe_zpow]
  exact hk

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_zpowers_of_commute_of_hom {K V : Subgroup G} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hq : Nat.card F % 3 = 2) (α : ↥K →* Matrix.SpecialLinearGroup (Fin 3) F)
    (hαk : α.ker = V.subgroupOf K) (hV : IsPGroup 2 V) {x z : G} (hxK : x ∈ K) (hzK : z ∈ K)
    (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) (hx1 : x ≠ 1) (hxz : x * z = z * x) :
    z ∈ Subgroup.zpowers x := by
  set x' : ↥K := ⟨x, hxK⟩ with hx'
  set z' : ↥K := ⟨z, hzK⟩ with hz'
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa [hx'] using hx3)
  have hz'3 : z' ^ 3 = 1 := Subtype.ext (by simpa [hz'] using hz3)
  have hker : ∀ w : ↥K, w ^ 3 = 1 → α w = 1 → w = 1 := by
    intro w hw3 hw
    have hwV : (w : G) ∈ V := by
      have hw' : w ∈ α.ker := hw
      rw [hαk, Subgroup.mem_subgroupOf] at hw'
      exact hw'
    obtain ⟨j, hj⟩ := hV ⟨w, hwV⟩
    have hj' : (w : G) ^ (2 ^ j) = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hw3' : (w : G) ^ 3 = 1 := by
      have := congrArg Subtype.val hw3
      simpa using this
    exact Subtype.ext (Sec18.eq_one_of_pow_three_of_pow_two_pow hw3' hj')
  have ha1 : α x' ≠ 1 := fun h => hx1 (congrArg Subtype.val (hker x' hx'3 h))
  have hc : Commute x' z' := Subtype.ext hxz
  have hab : α x' * α z' = α z' * α x' := by
    rw [← map_mul, ← map_mul, hc.eq]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_commute_sl3 hq (by rw [← map_pow, hx'3, map_one])
      (by rw [← map_pow, hz'3, map_one]) ha1 hab)
  have hc' : Commute z' (x' ^ k)⁻¹ := (hc.symm.zpow_right k).inv_right
  have hxk3 : ((x' ^ k)⁻¹) ^ 3 = 1 := by
    rw [inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx'3, one_zpow,
      inv_one]
  have hw : z' * (x' ^ k)⁻¹ = 1 := by
    apply hker
    · rw [hc'.mul_pow, hz'3, hxk3, one_mul]
    · rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
  have hzx : z' = x' ^ k := mul_inv_eq_one.mp hw
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := congrArg Subtype.val hzx
  rw [Subgroup.coe_zpow] at this
  exact this.symm

theorem exists_central_pow_three {P : Subgroup G} (hP : IsPGroup 3 P) (hP1 : P ≠ ⊥) :
    ∃ z ∈ P, z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ w ∈ P, w * z = z * w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  have hZ := hP.center_nontrivial
  have hdvd : 3 ∣ Nat.card (Subgroup.center P) := by
    obtain ⟨k, hk⟩ := (IsPGroup.of_equiv (hP.to_subgroup (Subgroup.center P))
      (MulEquiv.refl _)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center P) :=
      Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hk] at h1 ⊢
    exact dvd_pow_self 3 (by rintro rfl; simp at h1)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨((z : P) : G), (z : P).2, ?_, ?_, ?_⟩
  · intro h
    have hz1 : z = 1 := Subtype.ext (Subtype.ext h)
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · have h3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have := congrArg (fun w : Subgroup.center P => ((w : P) : G)) h3
    simpa using this
  · intro w hw
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨w, hw⟩)

theorem exists_mem_zpowers_conj {K V Y : Subgroup G} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hq : Nat.card F % 3 = 2) (α : ↥K →* Matrix.SpecialLinearGroup (Fin 3) F)
    (hαk : α.ker = V.subgroupOf K) (hV : IsPGroup 2 V) (hYK : Y ≤ K) {a b : G}
    (haY : a ∈ Y) (hbY : b ∈ Y) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) :
    ∃ y ∈ Y, b ∈ Subgroup.zpowers (y * a * y⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP, hbP⟩ := exists_isSylowOf_le (isPGroup_zpowers_of_pow_three hb3)
    (Subgroup.zpowers_le.mpr hbY)
  obtain ⟨P', hP', haP'⟩ := exists_isSylowOf_le (isPGroup_zpowers_of_pow_three ha3)
    (Subgroup.zpowers_le.mpr haY)
  obtain ⟨y, hyY, hPy⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hP' hP
  refine ⟨y, hyY, ?_⟩
  have ha'P : y * a * y⁻¹ ∈ P := by
    rw [hPy]
    exact ⟨a, haP' (Subgroup.mem_zpowers a), rfl⟩
  have hbP' : b ∈ P := hbP (Subgroup.mem_zpowers b)
  have hPK : P ≤ K := hP.le.trans hYK
  have ha'1 : y * a * y⁻¹ ≠ 1 := by
    intro h
    apply ha1
    have : a = y⁻¹ * (y * a * y⁻¹) * y := by group
    rw [this, h]
    group
  have ha'3 : (y * a * y⁻¹) ^ 3 = 1 := by rw [conj_pow, ha3]; group
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at ha'P
    exact ha'1 ha'P
  obtain ⟨z, hzP, hz1, hz3, hzc⟩ := exists_central_pow_three hP.isPGroup hP1
  have hza : z ∈ Subgroup.zpowers (y * a * y⁻¹) :=
    mem_zpowers_of_commute_of_hom hq α hαk hV (hPK ha'P) (hPK hzP) ha'3 hz3 ha'1
      (hzc _ ha'P)
  have hbz : b ∈ Subgroup.zpowers z :=
    mem_zpowers_of_commute_of_hom hq α hαk hV (hPK hzP) (hPK hbP') hz3 hb3 hz1
      (hzc b hbP').symm
  exact (Subgroup.zpowers_le.mpr hza) hbz

theorem step209LNormal_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hO2L : CFSG.Open.pCoreOf 2 L ≤ M)
    (hTN : T ≤ N)
    (h8 : IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n) :
    L ≤ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) := by
  obtain ⟨-, hVO, n, hn, -, F, _, _, hF, α, -, hαk, -⟩ := h8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hq : Nat.card F % 3 = 2 := by
    rw [Nat.card_eq_fintype_card, hF]
    exact two_pow_mod_three_of_odd hn
  have hV2 : IsPGroup 2 (vTwenty M c T) :=
    hVO ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kTwenty M c)
  by_cases hc1 : c = 1
  · have hX : normalClosureIn (kTwenty M c ⊓ N) c = ⊥ := by
      rw [eq_bot_iff, normalClosureIn, Subgroup.closure_le]
      rintro _ ⟨m, -, rfl⟩
      rw [hc1, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    intro l _
    rw [hX]
    exact mem_normalizer_of_map_conj_le (le_of_eq (Subgroup.map_bot _))
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hc3 : c ^ 3 = 1 := hT.mem_partTwoE.1.2 c hcA
  have hcK : c ∈ kTwenty M c := self_mem_normalClosureIn M c
  have hcN : c ∈ N := by
    rw [hN]
    exact hAL hcA
  have hMK : M ≤ Subgroup.normalizer (kTwenty M c : Set G) := le_normalizer_normalClosureIn M c
  have hkey : ∀ y ∈ kTwenty M c ⊓ N, y ^ 3 = 1 → y ∈ normalClosureIn (kTwenty M c ⊓ N) c := by
    intro y hy hy3
    obtain ⟨k, hk, hyk⟩ := exists_mem_zpowers_conj hq α hαk hV2 inf_le_left ⟨hcK, hcN⟩ hy hc3
      hy3 hc1
    have hkc : k * c * k⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c :=
      Subgroup.subset_closure ⟨k, hk, rfl⟩
    exact (Subgroup.zpowers_le.mpr hkc) hyk
  have hcKN : c ∈ kTwenty M c ⊓ N := ⟨hcK, hcN⟩
  have hTX : T ≤ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) := by
    intro t ht
    have htKN : t ∈ Subgroup.normalizer ((kTwenty M c ⊓ N : Subgroup G) : Set G) :=
      mem_normalizer_inf_of_mem (hMK (hT.sylow.le ht)) (Subgroup.le_normalizer (hTN ht))
    apply mem_normalizer_of_map_conj_le
    rw [normalClosureIn, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hkcKN : k * c * k⁻¹ ∈ kTwenty M c ⊓ N :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hcKN) (Subgroup.inv_mem _ hk)
    show t * (k * c * k⁻¹) * t⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c
    refine hkey _ ((Subgroup.mem_normalizer_iff.mp htKN _).mp hkcKN) ?_
    rw [conj_pow, conj_pow, hc3]
    group
  have hOX : CFSG.Open.pCoreOf 2 L ≤
      Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) :=
    (pCoreOf_le_core hT hN hO2L hTN).trans hTX
  have hLXO := le_normalizer_normalClosureIn_sup_pCoreOf_core hT hN hAL
  intro l hl
  apply mem_normalizer_of_map_conj_le
  rw [normalClosureIn, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have hmem : k * c * k⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c ⊔ CFSG.Open.pCoreOf 2 L :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨k, hk, rfl⟩)
  show l * (k * c * k⁻¹) * l⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c
  refine mem_of_pow_three_eq_one hOX (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    ((Subgroup.mem_normalizer_iff.mp (hLXO hl) _).mp hmem) ?_
  rw [conj_pow, conj_pow, hc3]
  group

theorem step209LNormal_proof : Step209LNormal := by
  intro G _ _ A M L N c T hT hTN _ h8
  obtain ⟨H, -, -, -, hN⟩ := exists_sec18H_of_ctx20One hT
  exact step209LNormal_core hT.toCtx20 hN (le_normalizer_of_hyp201One hT.hyp201One)
    (pCoreOf_le_of_hyp201One hT.hyp201One) hTN h8

theorem item209One_of_step209LCentral (h207 : Item207One) (h208 : Item208One)
    (hC : Step209LCentral) : Item209One :=
  item209One_of_step209L_parts h207 h208 step209LNormal_proof hC

end CFSG.RankThree.PartTwo.Sec20
