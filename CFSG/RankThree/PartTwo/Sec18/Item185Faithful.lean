module

public import CFSG.RankThree.PartTwo.Sec18.Item185Ctx
import CFSG.RankThree.PartTwo.Sec18.Item185Quot
import CFSG.RankThree.PartTwo.Sec18.Item185Count
import CFSG.RankThree.PartTwo.Sec18.Item185O23
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec18.SylowTop
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec4.T444.Step452
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G] [Finite G]

private def ActsTrivially (K : Subgroup G) (x : G) : Prop :=
  ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K

private theorem actsTrivially_iff_quotAct {K : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    ActsTrivially K x ↔ Sec19.SimsC198.quotAct K ⟨x, hx⟩ = 1 :=
  (Sec19.SimsC198.quotAct_eq_one_iff K ⟨x, hx⟩).symm

private theorem actsTrivially_mul {K : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) (hy : y ∈ Subgroup.normalizer (K : Set G))
    (h1 : ActsTrivially K x) (h2 : ActsTrivially K y) : ActsTrivially K (x * y) := by
  have hxy : x * y ∈ Subgroup.normalizer (K : Set G) := mul_mem hx hy
  refine (actsTrivially_iff_quotAct hxy).mpr ?_
  have e : (⟨x * y, hxy⟩ : Subgroup.normalizer (K : Set G)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [e, map_mul, (actsTrivially_iff_quotAct hx).mp h1, (actsTrivially_iff_quotAct hy).mp h2,
    mul_one]

private theorem actsTrivially_inv {K : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) (h : ActsTrivially K x) :
    ActsTrivially K x⁻¹ := by
  have hxi : x⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem hx
  refine (actsTrivially_iff_quotAct hxi).mpr ?_
  have e : (⟨x⁻¹, hxi⟩ : Subgroup.normalizer (K : Set G)) = (⟨x, hx⟩)⁻¹ := rfl
  rw [e, map_inv, (actsTrivially_iff_quotAct hx).mp h, inv_one]

private theorem actsTrivially_conj {K : Subgroup G} {w x : G}
    (hw : w ∈ Subgroup.normalizer (K : Set G)) (hx : x ∈ Subgroup.normalizer (K : Set G))
    (h : ActsTrivially K x) : ActsTrivially K (w * x * w⁻¹) := by
  have hwx : w * x * w⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    mul_mem (mul_mem hw hx) (inv_mem hw)
  refine (actsTrivially_iff_quotAct hwx).mpr ?_
  have e : (⟨w * x * w⁻¹, hwx⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨w, hw⟩ * ⟨x, hx⟩ * (⟨w, hw⟩)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, (actsTrivially_iff_quotAct hx).mp h, mul_one,
    mul_inv_cancel]

private abbrev oSub (K : Subgroup G) : Subgroup (Subgroup.normalizer (K : Set G)) :=
  (CFSG.Open.pCoreOf 2 K).subgroupOf (Subgroup.normalizer (K : Set G))

private theorem oSub_normal (K : Subgroup G) : (oSub K).Normal := by
  have hOKN : CFSG.Open.pCoreOf 2 K ≤ Subgroup.normalizer (K : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans Subgroup.le_normalizer
  have hON : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hOKN).mpr hON

private theorem actImage_mono {K D D' : Subgroup G} (h : D ≤ D') :
    Sec19.SimsC198.actImage K D ≤ Sec19.SimsC198.actImage K D' := by
  intro φ hφ
  obtain ⟨d, hd, hdD, rfl⟩ := Sec19.SimsC198.mem_actImage hφ
  exact Subgroup.mem_map.mpr ⟨⟨d, hd⟩, Subgroup.mem_subgroupOf.mpr (h hdD), rfl⟩

private theorem le_of_isSylowOf_sub {p : ℕ} {P K : Subgroup G} (h : IsSylowOf p P K) :
    P ≤ K := by
  obtain ⟨Q, rfl⟩ := h
  exact Subgroup.map_subtype_le _

private theorem isPGroup_of_isSylowOf_top {p : ℕ} {P : Subgroup G} (h : IsSylowOf p P ⊤) :
    IsPGroup p P := by
  obtain ⟨Q, rfl⟩ := h
  exact Q.isPGroup'.map (⊤ : Subgroup G).subtype

private theorem isSylowOf_map_hom_185 {X Y : Type} [Group X] [Group Y] [Finite X] {p : ℕ}
    [Fact p.Prime] {P K : Subgroup X} (h : IsSylowOf p P K) (f : X →* Y) :
    IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem isSylowOf_actImage {K P : Subgroup G} [Fact (Nat.Prime 3)]
    (hsyl : IsSylowOf 3 (P ⊓ K) K) :
    IsSylowOf 3 (Sec19.SimsC198.actImage K (P ⊓ K)) (Sec19.SimsC198.actImage K K) := by
  have hKN : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
  have hPKN : P ⊓ K ≤ Subgroup.normalizer (K : Set G) := inf_le_right.trans hKN
  have hsylN : IsSylowOf 3 ((P ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G)))
      (K.subgroupOf (Subgroup.normalizer (K : Set G))) := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff
      (Subgroup.normalizer (K : Set G))).mp ?_
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hPKN, inf_eq_left.mpr hKN]
    exact hsyl
  exact isSylowOf_map_hom_185 hsylN (Sec19.SimsC198.quotAct K)

private theorem exists_central_triv {K P : Subgroup G} (hP : IsPGroup 3 P)
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) {x : G} (hxP : x ∈ P) (hx1 : x ≠ 1)
    (hxT : ActsTrivially K x) :
    ∃ z : G, z ∈ P ∧ z ≠ 1 ∧ ActsTrivially K z ∧ orderOf z = 3 ∧
      ∀ g ∈ P, g * z = z * g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent P := IsPGroup.isNilpotent hP
  let φ : P →* MulAut (K ⧸ CFSG.pCore 2 K) :=
    (Sec19.SimsC198.quotAct K).comp (Subgroup.inclusion hPK)
  have hxker : (⟨x, hxP⟩ : P) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    exact (actsTrivially_iff_quotAct (hPK hxP)).mp hxT
  have hne : φ.ker ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hxker
    exact hx1 (congrArg Subtype.val hxker)
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hukerm, hucen⟩ := Subgroup.mem_inf.mp w.2
  have hu1 : (w : P) ≠ 1 := fun h => hw (Subtype.ext h)
  obtain ⟨n, hn⟩ := hP (w : P)
  have hu_ne : orderOf (w : P) ≠ 1 := fun h => hu1 (orderOf_eq_one_iff.mp h)
  obtain ⟨i, -, hi⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hn)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hu_ne (by rw [hi, pow_zero])
  have h3 : 3 ∣ orderOf (w : P) := by
    rw [hi]
    exact dvd_pow_self 3 hi0
  have hpos : orderOf (w : P) ≠ 0 := by
    rw [hi]
    exact pow_ne_zero _ (by norm_num)
  have ht : orderOf ((w : P) ^ (orderOf (w : P) / 3)) = 3 :=
    orderOf_pow_orderOf_div hpos h3
  set y : P := (w : P) ^ (orderOf (w : P) / 3) with hy
  have hy1 : y ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht
    norm_num at ht
  have hyker : y ∈ φ.ker := pow_mem hukerm _
  have hycen : y ∈ Subgroup.center P := pow_mem hucen _
  have hyT : ActsTrivially K (y : G) :=
    (actsTrivially_iff_quotAct (hPK y.2)).mpr (MonoidHom.mem_ker.mp hyker)
  refine ⟨(y : G), y.2, fun h => hy1 (Subtype.ext h), hyT, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, ht]
  · intro g hg
    have := Subgroup.mem_center_iff.mp hycen ⟨g, hg⟩
    exact congrArg Subtype.val this

private theorem mem_of_central_order_three {A M : Subgroup G} (h : Sec18Std G A M)
    (hA : IsE27 A) {z : G} (hzM : z ∈ M) (hz3 : orderOf z = 3)
    (hcomm : ∀ a ∈ A, z * a = a * z) : z ∈ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNM : Subgroup.normalizer (A : Set G) ≤ M :=
    (normalizer_le_gamma le_rfl (by rw [hA.pRank_eq]; norm_num)).trans h.mem_scriptM.2
  have hAM : A ≤ M := Subgroup.le_normalizer.trans hNM
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hS : ∀ x ∈ (A : Set G) ∪ {z}, ∀ y ∈ (A : Set G) ∪ {z}, x * y = y * x := by
    rintro x (hx | hx) y (hy | hy)
    · exact hAc x hx y hy
    · rw [Set.mem_singleton_iff.mp hy]
      exact (hcomm x hx).symm
    · rw [Set.mem_singleton_iff.mp hx]
      exact hcomm y hy
    · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
  letI : CommGroup (Subgroup.closure ((A : Set G) ∪ {z})) :=
    Subgroup.closureCommGroupOfComm fun x hx y hy _ => hS x hx y hy
  have hEc : ∀ x ∈ Subgroup.closure ((A : Set G) ∪ {z}),
      ∀ y ∈ Subgroup.closure ((A : Set G) ∪ {z}), x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Subgroup.closure ((A : Set G) ∪ {z}))
      ⟨y, hy⟩)
  have hz3' : z ^ 3 = 1 := by
    rw [← hz3]
    exact pow_orderOf_eq_one z
  have hEe : ∀ x ∈ Subgroup.closure ((A : Set G) ∪ {z}), x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hyA | hyz
      · exact hA.1.2 y hyA
      · rw [Set.mem_singleton_iff.mp hyz]
        exact hz3'
    | one => exact one_pow 3
    | mul a b ha hb ha' hb' =>
      rw [(show Commute a b from hEc a ha b hb).mul_pow, ha', hb', one_mul]
    | inv a ha ha' =>
      rw [inv_pow, ha', inv_one]
  have hEab : IsElemAbelian 3 (Subgroup.closure ((A : Set G) ∪ {z})) :=
    ⟨⟨⟨fun a b => Subtype.ext (hEc a.1 a.2 b.1 b.2)⟩⟩, hEe⟩
  have hEM : Subgroup.closure ((A : Set G) ∪ {z}) ≤ M :=
    (Subgroup.closure_le _).mpr (Set.union_subset (fun x hx => hAM hx)
      (Set.singleton_subset_iff.mpr hzM))
  have hcardE := card_le_of_le_M h hEM hEab
  have hAE : A ≤ Subgroup.closure ((A : Set G) ∪ {z}) := fun a ha =>
    Subgroup.subset_closure (Set.mem_union_left _ ha)
  have hAeq : A = Subgroup.closure ((A : Set G) ∪ {z}) :=
    Subgroup.eq_of_le_of_card_ge hAE (by rw [hA.2]; exact hcardE)
  rw [hAeq]
  exact Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton z))

private theorem exists_pow_mul_of_sup {A B : Subgroup G} {c : G}
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hcA : c ∈ A) (hBA : B ≤ A)
    (hsup : A = Subgroup.zpowers c ⊔ B) (hc3 : orderOf c = 3) {z : G} (hzA : z ∈ A)
    (hzB : z ∉ B) : ∃ j : ℕ, (j = 1 ∨ j = 2) ∧ ∃ b ∈ B, z = c ^ j * b := by
  let T : Subgroup G :=
    { carrier := {g | ∃ i : ℤ, ∃ b ∈ B, g = c ^ i * b}
      mul_mem' := by
        rintro _ _ ⟨i, b, hb, rfl⟩ ⟨j, b', hb', rfl⟩
        have hbc : Commute b c := hAc b (hBA hb) c hcA
        refine ⟨i + j, b * b', B.mul_mem hb hb', ?_⟩
        calc c ^ i * b * (c ^ j * b') = c ^ i * (b * c ^ j) * b' := by group
          _ = c ^ i * (c ^ j * b) * b' := by rw [(hbc.zpow_right j).eq]
          _ = c ^ (i + j) * (b * b') := by rw [zpow_add]; group
      one_mem' := ⟨0, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, b, hb, rfl⟩
        refine ⟨-i, b⁻¹, B.inv_mem hb, ?_⟩
        have hbc : Commute b⁻¹ (c ^ (-i)) :=
          ((show Commute b c from hAc b (hBA hb) c hcA).inv_left).zpow_right (-i)
        calc (c ^ i * b)⁻¹ = b⁻¹ * c ^ (-i) := by rw [mul_inv_rev, zpow_neg]
          _ = c ^ (-i) * b⁻¹ := hbc.eq }
  have hle : A ≤ T := by
    rw [hsup]
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact ⟨i, 1, B.one_mem, by simp⟩
    · intro b hb
      exact ⟨0, b, hb, by simp⟩
  have hzT : z ∈ T := hle hzA
  obtain ⟨i, b, hb, hz⟩ : ∃ i : ℤ, ∃ b ∈ B, z = c ^ i * b := hzT
  have hci : c ^ i = c ^ (i % 3) := by
    have h := zpow_mod_orderOf c i
    rw [hc3] at h
    exact_mod_cast h.symm
  have hr : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hr with h0 | h1 | h2
  · exfalso
    apply hzB
    rw [hz, hci, h0, zpow_zero, one_mul]
    exact hb
  · refine ⟨1, Or.inl rfl, b, hb, ?_⟩
    rw [hz, hci, h1, zpow_one, pow_one]
  · refine ⟨2, Or.inr rfl, b, hb, ?_⟩
    rw [hz, hci, h2]
    simp

private theorem exists_centralizer_of_triv {K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) (hc3 : orderOf c = 3)
    (hcT : ActsTrivially K c) {k : G} (hk : k ∈ K) :
    ∃ e ∈ K, e * c = c * e ∧ e⁻¹ * k ∈ CFSG.Open.pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKN : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
  have hON : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  have hOp : IsPGroup 2 (CFSG.Open.pCoreOf 2 K) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hOK : CFSG.Open.pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  haveI := oSub_normal K
  have hOp' : IsPGroup 2 (oSub K) := hOp.comap_subtype
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hOp'
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (oSub K)).ker := by
    rw [QuotientGroup.ker_mk', hn]
    intro h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  have hsurj : Function.Surjective (QuotientGroup.mk' (oSub K)) :=
    QuotientGroup.mk'_surjective _
  have hc'3 : orderOf (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G)) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hc3
  have hZ3 : IsPGroup 3 (Subgroup.zpowers (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc'3, pow_one])
  have hcomm_k : Commute (QuotientGroup.mk' (oSub K) ⟨c, hcN⟩)
      (QuotientGroup.mk' (oSub K) ⟨k, hKN hk⟩) := by
    show QuotientGroup.mk' (oSub K) ⟨c, hcN⟩ * QuotientGroup.mk' (oSub K) ⟨k, hKN hk⟩ =
      QuotientGroup.mk' (oSub K) ⟨k, hKN hk⟩ * QuotientGroup.mk' (oSub K) ⟨c, hcN⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hm : c⁻¹ * k * c⁻¹⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
      actsTrivially_inv hcN hcT k hk
    have hm2 : k⁻¹ * (c⁻¹ * k * c⁻¹⁻¹ * k⁻¹) * k⁻¹⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (hON (inv_mem (hKN hk))) _).mp hm
    have e : (c * k)⁻¹ * (k * c) = k⁻¹ * (c⁻¹ * k * c⁻¹⁻¹ * k⁻¹) * k⁻¹⁻¹ := by group
    show (c * k)⁻¹ * (k * c) ∈ CFSG.Open.pCoreOf 2 K
    rw [e]
    exact hm2
  have htarget : QuotientGroup.mk' (oSub K) ⟨k, hKN hk⟩ ∈ Subgroup.centralizer
      (((Subgroup.zpowers (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G))).map
        (QuotientGroup.mk' (oSub K)) : Subgroup _) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [map_zpow]
    exact (hcomm_k.zpow_left m).eq
  obtain ⟨e', he', hπe⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_centralizer_preimage_of_pGroup_prime_complement_kernel
      3 Nat.prime_three (QuotientGroup.mk' (oSub K)) hsurj hker _ hZ3 _ htarget
  have hce : (e' : G) * c = c * (e' : G) := by
    have h := Subgroup.mem_centralizer_iff.mp he' (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G))
      (Subgroup.mem_zpowers _)
    exact (congrArg Subtype.val h).symm
  have hkO : (e' : G)⁻¹ * k ∈ CFSG.Open.pCoreOf 2 K := by
    have h : (e' : Subgroup.normalizer (K : Set G))⁻¹ * ⟨k, hKN hk⟩ ∈ oSub K :=
      QuotientGroup.eq.mp hπe
    exact Subgroup.mem_subgroupOf.mp h
  have he'K : (e' : G) ∈ K := by
    have h := K.mul_mem hk (K.inv_mem (hOK hkO))
    rwa [show k * ((e' : G)⁻¹ * k)⁻¹ = (e' : G) by group] at h
  exact ⟨(e' : G), he'K, hce, hkO⟩

private theorem oTwoP_three_le_center {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) : Sec4.oTwoP 3 X ≤ Subgroup.center X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect X := hq.1
  haveI := Sec4.oTwoP_normal 3 X
  have hq' : CFSG.Open.IsQuasisimple X := ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩
  have hnt : Nontrivial X := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    haveI : Nontrivial (X ⧸ Subgroup.center X) := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    exact (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq'
      (Sec4.oTwoP 3 X) with h | h
  · exact h
  · exfalso
    haveI : Group.IsSolvable (Sec4.oTwoP 3 X) := Sec4.isSolvable_oTwoP 3
    have hXs : Group.IsSolvable X :=
      Group.isSolvable_of_surjective (f := (Sec4.oTwoP 3 X).subtype)
        (fun x => ⟨⟨x, by rw [h]; exact Subgroup.mem_top x⟩, rfl⟩)
    exact Group.IsPerfect.not_isSolvable X hXs

private theorem false_of_triv_c {A M H : Subgroup G} {c : G} {P : Subgroup G}
    (hC : Ctx G A M H c P) {K : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    (hBK : A ⊓ inSubgroup perfectResidual H ≤ K)
    (hnc : ∃ b ∈ A ⊓ inSubgroup perfectResidual H, ∃ k ∈ K,
      b * k * b⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    (hΩ : A ⊓ inSubgroup perfectResidual H ≤
      (Sec4.oTwoP 3 ↥(M ⊓ Subgroup.centralizer ({c} : Set G))).map
        (M ⊓ Subgroup.centralizer ({c} : Set G)).subtype)
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) (hc3 : orderOf c = 3)
    (hcT : ActsTrivially K c)
    (hfB : ∀ b ∈ A ⊓ inSubgroup perfectResidual H, ActsTrivially K b → b = 1) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcA : c ∈ A := hC.planeQ8.mem
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hC.planeQ8.isElemAbelian.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  obtain ⟨b0, hb0B, k0, hk0, hb0k⟩ := hnc
  have hb0K : b0 ∈ K := hBK hb0B
  have hSK : K ⊓ Subgroup.centralizer ({c} : Set G) ≤ K := inf_le_left
  have hSM : K ⊓ Subgroup.centralizer ({c} : Set G) ≤
      M ⊓ Subgroup.centralizer ({c} : Set G) :=
    inf_le_inf_right _ (le_of_mem_oTwoComponentsIn hK)
  have hcomm_c : ∀ x ∈ A ⊓ inSubgroup perfectResidual H,
      x ∈ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff.mp hh]
    exact hAc c hcA x (Subgroup.mem_inf.mp hx).1
  have hBS : ∀ x ∈ A ⊓ inSubgroup perfectResidual H,
      x ∈ K ⊓ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    ⟨hBK hx, hcomm_c x hx⟩
  have hb0S : b0 ∈ (Sec4.oTwoP 3 ↥(K ⊓ Subgroup.centralizer ({c} : Set G))).map
      (K ⊓ Subgroup.centralizer ({c} : Set G)).subtype :=
    inf_oTwoP_le hSM ⟨hΩ hb0B, hBS b0 hb0B⟩
  have hcover : ∀ k ∈ K, ∃ e ∈ K ⊓ Subgroup.centralizer ({c} : Set G),
      e⁻¹ * k ∈ CFSG.Open.pCoreOf 2 K := by
    intro k hk
    obtain ⟨e, heK, hec, hek⟩ := exists_centralizer_of_triv hcN hc3 hcT hk
    refine ⟨e, ⟨heK, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩, hek⟩
    rw [Set.mem_singleton_iff.mp hh]
    exact hec.symm
  let f : ↥(K ⊓ Subgroup.centralizer ({c} : Set G)) →* (K ⧸ CFSG.pCore 2 K) :=
    (QuotientGroup.mk' (CFSG.pCore 2 K)).comp (Subgroup.inclusion hSK)
  have hfs : Function.Surjective f := by
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) x
    obtain ⟨e, heS, hek⟩ := hcover k.1 k.2
    refine ⟨⟨e, heS⟩, ?_⟩
    exact QuotientGroup.eq.mpr
      ((Sec19.SimsC198.Transport.mem_pCore_iff_mem_pCoreOf K _).mpr hek)
  obtain ⟨s, hs, hsb⟩ := Subgroup.mem_map.mp hb0S
  have hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) :=
    isQuasisimple_of_mem_oTwoComponentsIn hK
  have hfs_mem : f s ∈ Sec4.oTwoP 3 (K ⧸ CFSG.pCore 2 K) :=
    oTwoP_map_le_of_surjective f hfs (Subgroup.mem_map_of_mem f hs)
  have hfb : f s = QuotientGroup.mk' (CFSG.pCore 2 K) ⟨b0, hb0K⟩ :=
    congrArg (QuotientGroup.mk' (CFSG.pCore 2 K)) (Subtype.ext hsb)
  have hcen : QuotientGroup.mk' (CFSG.pCore 2 K) ⟨b0, hb0K⟩ ∈
      Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [← hfb]
    exact oTwoP_three_le_center hq hfs_mem
  have hON : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  have hTriv : ActsTrivially K b0 := by
    intro k hk
    have hk' : k⁻¹ ∈ K := K.inv_mem hk
    have hcomm := Subgroup.mem_center_iff.mp hcen
      (QuotientGroup.mk' (CFSG.pCore 2 K) ⟨k⁻¹, hk'⟩)
    rw [← map_mul, ← map_mul] at hcomm
    have hv : (⟨k⁻¹, hk'⟩ * ⟨b0, hb0K⟩ : K)⁻¹ * (⟨b0, hb0K⟩ * ⟨k⁻¹, hk'⟩) ∈
        CFSG.pCore 2 K :=
      QuotientGroup.eq.mp hcomm
    have hv' : (k⁻¹ * b0)⁻¹ * (b0 * k⁻¹) ∈ CFSG.Open.pCoreOf 2 K :=
      (Sec19.SimsC198.Transport.mem_pCore_iff_mem_pCoreOf K _).mp hv
    have hcj : b0 * ((k⁻¹ * b0)⁻¹ * (b0 * k⁻¹)) * b0⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (hON (Subgroup.le_normalizer hb0K)) _).mp hv'
    have e : (b0 * ((k⁻¹ * b0)⁻¹ * (b0 * k⁻¹)) * b0⁻¹)⁻¹ = b0 * k * b0⁻¹ * k⁻¹ := by
      group
    rw [← e]
    exact (CFSG.Open.pCoreOf 2 K).inv_mem hcj
  have hb0_one : b0 = 1 := hfB b0 hb0B hTriv
  apply hb0k
  rw [hb0_one]
  simp

private theorem eq_one_of_centralized {A B K' : Subgroup G} {c : G}
    (hBA : B ≤ A) (hsup : A = Subgroup.zpowers c ⊔ B)
    (hK'c : ∀ k ∈ K', k * c = c * k)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn K' B))
    (hquat : ∃ f : QuaternionGroup 2 →* Sec4.autIn K' A, Function.Injective f)
    {b : G} (hb : b ∈ B) (hfix : ∀ k ∈ K', k * b = b * k) : b = 1 := by
  let C : Subgroup B := (Subgroup.centralizer (K' : Set G)).subgroupOf B
  have hbC : (⟨b, hb⟩ : B) ∈ C :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_iff.mpr fun k hk => hfix k hk)
  have hinv : ∀ φ ∈ Sec4.autIn K' B, C.map φ.toMonoidHom = C := by
    intro φ hφ
    obtain ⟨w, hwN, hwK, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
    have hfixC : ∀ y ∈ C, (B.normalizerMonoidHom ⟨w, hwN⟩).toMonoidHom y = y := by
      intro y hy
      apply Subtype.ext
      show ((B.normalizerMonoidHom ⟨w, hwN⟩ y : B) : G) = (y : G)
      rw [Sec4.normalizerMonoidHom_apply_coe]
      have hyc : w * (y : G) = (y : G) * w :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hy) w hwK
      rw [hyc]
      group
    apply Subgroup.ext
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hfixC z hz]
      exact hz
    · intro hy
      exact ⟨y, hy, hfixC y hy⟩
  rcases hirr C hinv with hC0 | hCtop
  · have hmem := hbC
    rw [hC0, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    have hBK' : ∀ y ∈ B, ∀ k ∈ K', k * y = y * k := fun y hy k hk => by
      have hmem : (⟨y, hy⟩ : B) ∈ C := by
        rw [hCtop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hmem) k hk
    have hAK' : A ≤ Subgroup.centralizer (K' : Set G) := by
      rw [hsup]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_iff.mpr fun k hk => hK'c k hk
      · intro y hy
        exact Subgroup.mem_centralizer_iff.mpr fun k hk => hBK' y hy k hk
    have hσ : ∀ σ ∈ Sec4.autIn K' A, σ = 1 := by
      intro σ hσ
      obtain ⟨w, hwN, hwK, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
      ext a
      rw [Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply]
      have hac : w * (a : G) = (a : G) * w :=
        Subgroup.mem_centralizer_iff.mp (hAK' a.2) w hwK
      rw [hac]
      group
    obtain ⟨f, hf⟩ := hquat
    have h1 : (QuaternionGroup.a 1 : QuaternionGroup 2) = 1 :=
      hf (Subtype.ext ((hσ _ (f (QuaternionGroup.a 1)).2).trans (hσ _ (f 1).2).symm))
    exact absurd h1 (by decide)

theorem faithful_P {A M H : Subgroup G} {c : G} {P : Subgroup G}
    (hC : Ctx G A M H c P) {K : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    (hWK : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hBK : A ⊓ inSubgroup perfectResidual H ≤ K)
    (hnc : ∃ b ∈ A ⊓ inSubgroup perfectResidual H, ∃ k ∈ K,
      b * k * b⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    (hΩ : A ⊓ inSubgroup perfectResidual H ≤
      (Sec4.oTwoP 3 ↥(M ⊓ Subgroup.centralizer ({c} : Set G))).map
        (M ⊓ Subgroup.centralizer ({c} : Set G)).subtype) :
    ∀ x ∈ P, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → x = 1 := by
  intro x hxP hxT
  by_contra hx1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd : Sec18Std G A M := hC.toSec18H.toSec18Std
  have hP3 : IsPGroup 3 P := isPGroup_of_isSylowOf_top hC.sylow_G
  have hPW : P ≤ Subgroup.normalizer (A : Set G) := le_of_isSylowOf_sub hC.sylow_W
  have hPK : P ≤ Subgroup.normalizer (K : Set G) := hPW.trans hWK
  have hA : IsE27 A := ⟨hC.planeQ8.isElemAbelian, hC.planeQ8.card_eq⟩
  have hNM : Subgroup.normalizer (A : Set G) ≤ M :=
    (normalizer_le_gamma le_rfl (by rw [hA.pRank_eq]; norm_num)).trans hstd.mem_scriptM.2
  have hPM : P ≤ M := hPW.trans hNM
  have hcA : c ∈ A := hC.planeQ8.mem
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hC.planeQ8.isElemAbelian.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hBA : A ⊓ inSubgroup perfectResidual H ≤ A := inf_le_left
  have hsup : A = Subgroup.zpowers c ⊔ (A ⊓ inSubgroup perfectResidual H) :=
    hC.planeQ8.eq_sup
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hC.planeQ8.not_mem (A ⊓ inSubgroup perfectResidual H).one_mem
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA.1.2 c hcA) hc1
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hWK (Subgroup.le_normalizer hcA)
  obtain ⟨z, hzP, hz1, hzT, hz3, hzc⟩ := exists_central_triv hP3 hPK hxP hx1 hxT
  have hzM : z ∈ M := hPM hzP
  have hzN : z ∈ Subgroup.normalizer (K : Set G) := hPK hzP
  have hAp3 : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian hA.1
  have hAP : A ≤ P := by
    haveI : (A.subgroupOf (Subgroup.normalizer (A : Set G))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
    exact SylowTop.le_of_isSylowOf Subgroup.le_normalizer hAp3 hC.sylow_W
  have hcomm : ∀ a ∈ A, z * a = a * z := fun a ha => (hzc a (hAP ha)).symm
  have hzA : z ∈ A := mem_of_central_order_three hstd hA hzM hz3 hcomm
  have hfB : ∀ b ∈ A ⊓ inSubgroup perfectResidual H, ActsTrivially K b → b = 1 := by
    have hBS : A ⊓ inSubgroup perfectResidual H ≤
        Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (K : Set G) := fun x hx =>
      ⟨Subgroup.le_normalizer (hBA hx), Subgroup.le_normalizer (hBK hx)⟩
    have hSB : Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
        Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G) :=
      fun w hw => hC.normalizer_le hw.1
    exact faithful_B hstd hK hBS inf_le_right hSB (isIrreducibleOn_normalizer_inf hC hK) hnc
  have hzB : z ∉ A ⊓ inSubgroup perfectResidual H := fun hzB => hz1 (hfB z hzB hzT)
  obtain ⟨j, hj, b, hbB, hzeq⟩ := exists_pow_mul_of_sup hAc hcA hBA hsup hc3 hzA hzB
  have hfixK : ∀ w ∈ lc H c ⊓ Subgroup.normalizer (A : Set G), w * b = b * w := by
    intro w hw
    have hwN : w ∈ Subgroup.normalizer (A : Set G) := hw.2
    have hwNK : w ∈ Subgroup.normalizer (K : Set G) := hWK hwN
    have hwNB : w ∈ Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G) :=
      hC.planeQ8.le_normalizer_plane hw
    have hwc : Commute w c := hC.planeQ8.commute w hw
    have hwcj : w * c ^ j = c ^ j * w := (hwc.pow_right j).eq
    have hwb : w * b * w⁻¹ ∈ A ⊓ inSubgroup perfectResidual H :=
      (Subgroup.mem_normalizer_iff.mp hwNB b).mp hbB
    have hcb : ∀ x ∈ A ⊓ inSubgroup perfectResidual H, c ^ j * x = x * c ^ j := fun x hx =>
      ((show Commute c x from hAc c hcA x (hBA hx)).pow_left j).eq
    have hv : w * z * w⁻¹ = c ^ j * (w * b * w⁻¹) := by
      rw [hzeq]
      calc w * (c ^ j * b) * w⁻¹ = (w * c ^ j) * b * w⁻¹ := by group
        _ = (c ^ j * w) * b * w⁻¹ := by rw [hwcj]
        _ = c ^ j * (w * b * w⁻¹) := by group
    have hu : w * z * w⁻¹ * z⁻¹ = (w * b * w⁻¹) * b⁻¹ := by
      rw [hv, hzeq]
      calc c ^ j * (w * b * w⁻¹) * (c ^ j * b)⁻¹
          = c ^ j * ((w * b * w⁻¹) * b⁻¹) * (c ^ j)⁻¹ := by group
        _ = ((w * b * w⁻¹) * b⁻¹) * c ^ j * (c ^ j)⁻¹ := by
          rw [hcb _ ((A ⊓ inSubgroup perfectResidual H).mul_mem hwb
            ((A ⊓ inSubgroup perfectResidual H).inv_mem hbB))]
        _ = (w * b * w⁻¹) * b⁻¹ := by group
    have hu_B : w * z * w⁻¹ * z⁻¹ ∈ A ⊓ inSubgroup perfectResidual H := by
      rw [hu]
      exact (A ⊓ inSubgroup perfectResidual H).mul_mem hwb
        ((A ⊓ inSubgroup perfectResidual H).inv_mem hbB)
    have hu_T : ActsTrivially K (w * z * w⁻¹ * z⁻¹) :=
      actsTrivially_mul (mul_mem (mul_mem hwNK hzN) (inv_mem hwNK)) (inv_mem hzN)
        (actsTrivially_conj hwNK hzN hzT) (actsTrivially_inv hzN hzT)
    have hu1 : w * z * w⁻¹ * z⁻¹ = 1 := hfB _ hu_B hu_T
    have hwz : w * z * w⁻¹ = z := mul_inv_eq_one.mp hu1
    have h2 : c ^ j * (w * b * w⁻¹) = c ^ j * b := hv.symm.trans (hwz.trans hzeq)
    have hwbw : w * b * w⁻¹ = b := mul_left_cancel h2
    calc w * b = (w * b * w⁻¹) * w := by group
      _ = b * w := by rw [hwbw]
  have hb1 : b = 1 :=
    eq_one_of_centralized hBA hsup hC.planeQ8.commute hC.planeQ8.irreducible
      hC.planeQ8.quaternion hbB hfixK
  have hzpow : z = c ^ j := by rw [hzeq, hb1, mul_one]
  have hcT : ActsTrivially K c := by
    rcases hj with rfl | rfl
    · have hcz : c = z := by rw [hzpow, pow_one]
      rw [hcz]
      exact hzT
    · have hc4 : c ^ 2 * c ^ 2 = c := by
        have h3 : c ^ 3 = 1 := by
          rw [← hc3]
          exact pow_orderOf_eq_one c
        calc c ^ 2 * c ^ 2 = c ^ 3 * c := by group
          _ = c := by rw [h3, one_mul]
      have hzz : ActsTrivially K (c ^ 2 * c ^ 2) := by
        rw [← hzpow]
        exact actsTrivially_mul hzN hzN hzT hzT
      rw [← hc4]
      exact hzz
  exact false_of_triv_c hC hK hBK hnc hΩ hcN hc3 hcT hfB

theorem mem_of_inducesInner {A M H : Subgroup G} {c : G} {P : Subgroup G}
    (hC : Ctx G A M H c P) {K : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hfaith : ∀ x ∈ P, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → x = 1) :
    ∀ x ∈ P, InducesInnerMod x K (CFSG.Open.pCoreOf 2 K) → x ∈ K := by
  intro x hxP hind
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxN, k, hk, hkx⟩ := hind
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
  have hON : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  have htN : k⁻¹ * x ∈ Subgroup.normalizer (K : Set G) := mul_mem (inv_mem hkN) hxN
  have htT : ActsTrivially K (k⁻¹ * x) := by
    intro y hy
    have hu : x * y * x⁻¹ * (k * y * k⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 K := hkx y hy
    have hu' : k⁻¹ * (x * y * x⁻¹ * (k * y * k⁻¹)⁻¹) * k⁻¹⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (hON (inv_mem hkN)) _).mp hu
    have e : k⁻¹ * x * y * (k⁻¹ * x)⁻¹ * y⁻¹ =
        k⁻¹ * (x * y * x⁻¹ * (k * y * k⁻¹)⁻¹) * k⁻¹⁻¹ := by
      group
    rw [e]
    exact hu'
  have ht1 : Sec19.SimsC198.quotAct K ⟨k⁻¹ * x, htN⟩ = 1 :=
    (actsTrivially_iff_quotAct htN).mp htT
  have hQx : Sec19.SimsC198.quotAct K ⟨x, hxN⟩ ∈ Sec19.SimsC198.actImage K K := by
    have hkey : Sec19.SimsC198.quotAct K ⟨x, hxN⟩ = Sec19.SimsC198.quotAct K ⟨k, hkN⟩ := by
      have e : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) =
          ⟨k, hkN⟩ * ⟨k⁻¹ * x, htN⟩ := by
        apply Subtype.ext
        show x = k * (k⁻¹ * x)
        group
      rw [e, map_mul, ht1, mul_one]
    rw [hkey]
    exact Subgroup.mem_map.mpr ⟨⟨k, hkN⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hsylPK : IsSylowOf 3 P (P ⊔ K) := hC.sylow_G.of_le le_sup_left le_top
  have hsylI : IsSylowOf 3 (P ⊓ K) K :=
    hsylPK.inf_of_le_normalizer le_sup_right (sup_le hPK Subgroup.le_normalizer)
  haveI : Finite (MulAut (K ⧸ CFSG.pCore 2 K)) :=
    Finite.of_injective
      (fun σ : MulAut (K ⧸ CFSG.pCore 2 K) => (σ : (K ⧸ CFSG.pCore 2 K) → (K ⧸ CFSG.pCore 2 K)))
      DFunLike.coe_injective
  have hR : IsSylowOf 3 (Sec19.SimsC198.actImage K (P ⊓ K)) (Sec19.SimsC198.actImage K K) :=
    isSylowOf_actImage hsylI
  have hP' : IsPGroup 3 (P.subgroupOf (Subgroup.normalizer (K : Set G))) :=
    (isPGroup_of_isSylowOf_top hC.sylow_G).comap_subtype
  have hPb3 : IsPGroup 3 (Sec19.SimsC198.actImage K P) :=
    hP'.map (Sec19.SimsC198.quotAct K)
  have hmax : Sec19.SimsC198.actImage K P ⊓ Sec19.SimsC198.actImage K K =
      Sec19.SimsC198.actImage K (P ⊓ K) :=
    hR.eq_of_le (le_inf (actImage_mono inf_le_left) (actImage_mono inf_le_right))
      inf_le_right (hPb3.to_le inf_le_left)
  have hQPx : Sec19.SimsC198.quotAct K ⟨x, hxN⟩ ∈ Sec19.SimsC198.actImage K P :=
    Subgroup.mem_map.mpr ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
  have hmem : Sec19.SimsC198.quotAct K ⟨x, hxN⟩ ∈ Sec19.SimsC198.actImage K (P ⊓ K) := by
    rw [← hmax]
    exact Subgroup.mem_inf.mpr ⟨hQPx, hQx⟩
  obtain ⟨d, hdN, hdD, hdx⟩ := Sec19.SimsC198.mem_actImage hmem
  have hdP : d ∈ P := (Subgroup.mem_inf.mp hdD).1
  have hdK : d ∈ K := (Subgroup.mem_inf.mp hdD).2
  have hs : d⁻¹ * x ∈ P := P.mul_mem (P.inv_mem hdP) hxP
  have hsN : d⁻¹ * x ∈ Subgroup.normalizer (K : Set G) := hPK hs
  have hs1 : Sec19.SimsC198.quotAct K ⟨d⁻¹ * x, hsN⟩ = 1 := by
    have e : (⟨d⁻¹ * x, hsN⟩ : Subgroup.normalizer (K : Set G)) =
        (⟨d, hdN⟩)⁻¹ * ⟨x, hxN⟩ := rfl
    rw [e, map_mul, map_inv, hdx, inv_mul_cancel]
  have hsT : ActsTrivially K (d⁻¹ * x) := (actsTrivially_iff_quotAct hsN).mpr hs1
  have hs_one : d⁻¹ * x = 1 := hfaith _ hs hsT
  have hxd : x = d := by
    calc x = d * (d⁻¹ * x) := by group
      _ = d := by rw [hs_one, mul_one]
  rw [hxd]
  exact hdK

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
