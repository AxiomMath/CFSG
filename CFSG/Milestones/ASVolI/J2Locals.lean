module

public import CFSG.Milestones.ASVolI.J2
public import CFSG.Quasithin.Recognition.RuTypeJ27l
public import CFSG.Quasithin.Recognition.RuTypeJ31c
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6M10
public import CFSG.Quasithin.Recognition.RuTypeJ36a
public import CFSG.Quasithin.Recognition.RuTypeAutA6b
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.GH74.GLS.C3.Layer1.BkA6K
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import CFSG.Quasithin.Recognition.RuTypeJ31b
public import CFSG.GH74.GLS.C3.Layer1.Back91
public import CFSG.GH74.GLS.C3.Layer1.BkL27K
public import CFSG.GH74.GLS.C3.Layer1.Split
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.IVK.A7.Glue
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Lemma113
public import CFSG.GH74.GLS.IVK.L2.Lemma114
public import CFSG.GH74.GLS.IVK.L2.Lemma12ib
public import CFSG.GH74.GLS.IVK.L2.Lemma12j
public import CFSG.GH74.GLS.IVK.L2.Lemma12k
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.GH74.GLS.IVK.L2.Lemma14f
public import CFSG.GH74.GLS.IVK.L2.Lemma14j
public import CFSG.GH74.GLS.IVK.L2.Lemma19b
public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hb
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13d
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13e
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.ASVolI

open CFSG.Open

theorem burnsideJ27_quotEquiv_conj {G : Type} [Group G] {C₁ C₂ A₁ A₂ : Subgroup G} (l : G)
    (hC : ∀ x : G, x ∈ C₂ ↔ l⁻¹ * x * l ∈ C₁) (hA : ∀ x : G, x ∈ A₂ ↔ l⁻¹ * x * l ∈ A₁)
    [(A₁.subgroupOf C₁).Normal] [(A₂.subgroupOf C₂).Normal] :
    Nonempty ((↥C₁ ⧸ A₁.subgroupOf C₁) ≃* (↥C₂ ⧸ A₂.subgroupOf C₂)) := by
  let e : ↥C₁ ≃* ↥C₂ :=
    { toFun := fun x => ⟨l * x * l⁻¹, (hC _).mpr (by simpa [mul_assoc] using x.2)⟩
      invFun := fun y => ⟨l⁻¹ * y * l, (hC _).mp y.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  refine ⟨QuotientGroup.congr (A₁.subgroupOf C₁) (A₂.subgroupOf C₂) e ?_⟩
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hx
    refine (hA _).mpr ?_
    show l⁻¹ * (l * (x : G) * l⁻¹) * l ∈ A₁
    simpa [mul_assoc] using hx
  · intro hy
    refine ⟨e.symm y, Subgroup.mem_subgroupOf.mpr ((hA _).mp hy), e.apply_symm_apply y⟩

theorem burnsideJ27_mem_conjClass_iff {G : Type} [Group G] (z x : G) :
    x ∈ CFSG.ASVolI.ChIJK.conjClass z ↔ IsConj z x := by
  rw [isConj_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by group⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c⁻¹, by group⟩

theorem burnsideJ27_mem_conjugate {G : Type*} [Group G] {H : Subgroup G} {g y : G} :
    y ∈ CFSG.conjugate H g ↔ g * y * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_apply]

theorem burnsideJ27_conjugate_conjugate {G : Type*} [Group G] (A : Subgroup G) (g h : G) :
    CFSG.conjugate (CFSG.conjugate A g) h = CFSG.conjugate A (g * h) := by
  ext y
  rw [burnsideJ27_mem_conjugate, burnsideJ27_mem_conjugate, burnsideJ27_mem_conjugate]
  have : g * (h * y * h⁻¹) * g⁻¹ = (g * h) * y * (g * h)⁻¹ := by group
  rw [this]

theorem burnsideJ27_conjugate_one {G : Type*} [Group G] (A : Subgroup G) :
    CFSG.conjugate A 1 = A := by
  ext y
  rw [burnsideJ27_mem_conjugate]
  simp

theorem burnsideJ27_card_conjugate {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate A g) = Nat.card A := by
  unfold CFSG.conjugate
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem burnsideJ27_conjugate_le {G : Type*} [Group G] {A N : Subgroup G} {g : G} (hA :
    A ≤ N)
    (hg : g ∈ N) : CFSG.conjugate A g ≤ N := by
  intro y hy
  rw [burnsideJ27_mem_conjugate] at hy
  have h1 := N.mul_mem (N.mul_mem (N.inv_mem hg) (hA hy)) hg
  simpa [mul_assoc] using h1

theorem burnsideJ27_normalizer_conjugate {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Subgroup.normalizer ((CFSG.conjugate A g : Subgroup G) : Set G) =
      CFSG.conjugate (Subgroup.normalizer (A : Set G)) g := by
  ext y
  rw [burnsideJ27_mem_conjugate, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h a
    have := h (g⁻¹ * a * g)
    rw [burnsideJ27_mem_conjugate, burnsideJ27_mem_conjugate] at this
    have e : g * (y * (g⁻¹ * a * g) * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * a * (g * y * g⁻¹)⁻¹ := by group
    simpa [e, mul_assoc] using this
  · intro h a
    rw [burnsideJ27_mem_conjugate, burnsideJ27_mem_conjugate]
    have := h (g * a * g⁻¹)
    have e : g * (y * a * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * (g * a * g⁻¹) * (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact this

theorem burnsideJ27_centralizer_conjugate {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Subgroup.centralizer ((CFSG.conjugate A g : Subgroup G) : Set G) =
      CFSG.conjugate (Subgroup.centralizer (A : Set G)) g := by
  ext y
  rw [burnsideJ27_mem_conjugate, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    have h1 := h (g⁻¹ * a * g) (by
      rw [SetLike.mem_coe, burnsideJ27_mem_conjugate]
      have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [e]; exact ha)
    have e : g * (g⁻¹ * a * g * y) * g⁻¹ = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
    calc a * (g * y * g⁻¹) = g * (g⁻¹ * a * g * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * a * g)) * g⁻¹ := e
      _ = g * y * g⁻¹ * a := by group
  · intro h a ha
    rw [SetLike.mem_coe, burnsideJ27_mem_conjugate] at ha
    have h1 := h (g * a * g⁻¹) ha
    calc a * y = g⁻¹ * (g * a * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * (g * a * g⁻¹)) * g := by rw [h1]
      _ = y * a := by group

theorem burnsideJ27_exists_conj_of_card {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact
    p.Prime]
    (hK : ¬ p ^ 2 ∣ Nat.card K) {A A' : Subgroup K} (hA : Nat.card A = p)
    (hA' : Nat.card A' = p) : ∃ g : K, A' = CFSG.conjugate A g⁻¹ := by
  have key : ∀ {C : Subgroup K}, Nat.card C = p → ∃ P : Sylow p K, (P : Subgroup K) = C := by
    intro C hC
    have hp : IsPGroup p C := IsPGroup.of_card (n := 1) (by simpa using hC)
    have hidx : ¬ p ∣ C.index := by
      intro hd
      apply hK
      rw [← Subgroup.card_mul_index C, hC, pow_two]
      exact Nat.mul_dvd_mul_left p hd
    exact ⟨hp.toSylow hidx, rfl⟩
  obtain ⟨P, hP⟩ := key hA
  obtain ⟨P', hP'⟩ := key hA'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P P'
  refine ⟨g, ?_⟩
  rw [← hP', ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, ← hP]
  unfold CFSG.conjugate
  simp only [inv_inv]
  rfl

theorem burnsideJ27_conj_in_subgroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N B B' : Subgroup G} (hN : ¬ p ^ 2 ∣ Nat.card N) (hB : Nat.card B = p)
    (hB' : Nat.card B' = p) (hBN : B ≤ N) (hBN' : B' ≤ N) :
    ∃ n ∈ N, B' = CFSG.conjugate B n⁻¹ := by
  have e1 : Nat.card (B.subgroupOf N) = p := by
    rw [← hB]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  have e2 : Nat.card (B'.subgroupOf N) = p := by
    rw [← hB']; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN').toEquiv
  obtain ⟨n, hn⟩ := burnsideJ27_exists_conj_of_card hN e1 e2
  refine ⟨(n : G), n.2, ?_⟩
  ext y
  rw [burnsideJ27_mem_conjugate]
  constructor
  · intro hy
    have hyN : y ∈ N := hBN' hy
    have h1 : (⟨y, hyN⟩ : N) ∈ B'.subgroupOf N := hy
    rw [hn, burnsideJ27_mem_conjugate, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · intro hy
    have hyN : y ∈ N := by
      have : (n : G)⁻¹ * y * ((n : G)⁻¹)⁻¹ ∈ B := hy
      have hb : (n : G)⁻¹ * y * ((n : G)⁻¹)⁻¹ ∈ N := hBN this
      have := N.mul_mem (N.mul_mem n.2 hb) (N.inv_mem n.2)
      simpa [mul_assoc] using this
    have h1 : (⟨y, hyN⟩ : N) ∈ CFSG.conjugate (B.subgroupOf N) n⁻¹ := by
      rw [burnsideJ27_mem_conjugate]
      exact hy
    rw [← hn] at h1
    exact h1

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_L1_eq {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) :
    L1Ru L T = CFSG.GorensteinWalter.pResidualOf M.LT1 2 := by
  have hZ : ZRu T = CFSG.Quasithin.RuType.ruZ M.T := by
    rw [hMT]; exact h.ZRu_eq_ruZ
  have h1 : Subgroup.centralizer (ZRu T : Set G) ⊓ L = M.LT1 := by
    rw [hZ, ← hML, inf_comm]
    exact M.L_inf_H
  unfold L1Ru
  rw [h1]
  rfl

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_L1_le {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) : L1Ru L T ≤ L := by
  rw [burnsideJ27_L1_eq h M hML hMT]
  exact (CFSG.GorensteinWalter.pResidualOf_le _ _).trans (hML ▸ M.LT1_le_L)

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_B_le_L1 {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) : M.B ≤ L1Ru L T := by
  rw [burnsideJ27_L1_eq h M hML hMT, Subgroup.zpowers_le]
  refine CFSG.GorensteinWalter.mem_pResidualOf_of_order_coprime _ 2 Nat.prime_two ?_ ?_
  · have : (M.bel : G) ∈ M.L ⊓ CFSG.Quasithin.RuType.ruH M.T := ⟨M.bel.2, M.bel_mem_H⟩
    rwa [M.L_inf_H] at this
  · rw [M.orderOf_bel]; norm_num

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_card_L1 {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) : 3 ∣ Nat.card (L1Ru L T) ∧ ¬ 9 ∣ Nat.card (L1Ru L T) := by
  constructor
  · have := Subgroup.card_dvd_of_le (burnsideJ27_B_le_L1 h M hML hMT)
    rwa [M.card_B] at this
  · intro hd
    have h1 : Nat.card (L1Ru L T) ∣ Nat.card M.LT1 :=
      Subgroup.card_dvd_of_le (by
        rw [burnsideJ27_L1_eq h M hML hMT]
        exact CFSG.GorensteinWalter.pResidualOf_le _ _)
    rw [M.card_LT1] at h1
    have := hd.trans h1
    norm_num at this

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_step_B {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) {B : Subgroup G} (hB : IsSylowIn 3 B (L1Ru L T)) :
    ∃ x ∈ L1Ru L T, B = CFSG.conjugate M.B x⁻¹ := by
  obtain ⟨hBle, hBp, hBidx⟩ := hB
  obtain ⟨h3, h9⟩ := burnsideJ27_card_L1 h M hML hMT
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcardB : Nat.card B = 3 := by
    obtain ⟨k, hk⟩ := hBp.exists_card_eq
    have hmul := Subgroup.card_mul_index (B.subgroupOf (L1Ru L T))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv, hk] at hmul
    rcases k with _ | _ | k
    · exact absurd (by rw [← hmul, pow_zero, one_mul] at h3; exact h3) hBidx
    · simpa using hk
    · exact absurd (by rw [← hmul]; exact Dvd.dvd.mul_right ⟨3 ^ k, by ring⟩ _) h9
  exact burnsideJ27_conj_in_subgroup (p := 3) (N := L1Ru L T) (B := M.B) (B' := B)
    (fun hd => h9 (by simpa using hd)) M.card_B hcardB (burnsideJ27_B_le_L1 h M hML hMT) hBle

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_reduce_aux {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) {B B7 : Subgroup G} (hB : IsSylowIn 3 B (L1Ru L T))
    (hB7L : B7 ≤ L) (hB7 : Nat.card B7 = 7) (hBN : B ≤ Subgroup.normalizer (B7 : Set G)) :
    ∃ x ∈ L, B = CFSG.conjugate M.B x⁻¹ ∧ B7 = CFSG.conjugate M.B7 x⁻¹ := by
  obtain ⟨x₁, hx₁X, hBx₁⟩ := burnsideJ27_step_B h M hML hMT hB
  have hXL := burnsideJ27_L1_le h M hML hMT
  have hx₁L : x₁ ∈ L := hXL hx₁X
  have hBL : B ≤ L := hB.1.trans hXL
  have hB3 : Nat.card B = 3 := by rw [hBx₁, burnsideJ27_card_conjugate, M.card_B]
  have hB7M : M.B7 ≤ L := hML ▸ (Subgroup.zpowers_le.mpr M.cel.2)
  have hBM : M.B ≤ Subgroup.normalizer (M.B7 : Set G) := by
    rw [Subgroup.zpowers_le]
    exact CFSG.Quasithin.RuType.mem_normalizer_of_conj_mem fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact M.bel_conj_cel k
  set C := CFSG.conjugate M.B7 x₁⁻¹ with hC
  have hCL : C ≤ L := burnsideJ27_conjugate_le hB7M (L.inv_mem hx₁L)
  have hCc : Nat.card C = 7 := by rw [hC, burnsideJ27_card_conjugate, M.card_B7]
  have hBC : B ≤ Subgroup.normalizer (C : Set G) := by
    rw [hC, burnsideJ27_normalizer_conjugate, hBx₁]
    exact Subgroup.map_mono hBM
  have hL49 : ¬ 7 ^ 2 ∣ Nat.card L := by
    rw [← hML, M.card_L]; norm_num
  have hL9 : ∀ N : Subgroup G, N ≤ L → ¬ 3 ^ 2 ∣ Nat.card N := fun N hN hd => by
    have := hd.trans (Subgroup.card_dvd_of_le hN)
    rw [← hML, M.card_L] at this
    norm_num at this
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨g, hgL, hg⟩ := burnsideJ27_conj_in_subgroup (p := 7) (N := L) (B := C) (B' := B7)
    hL49 hCc hB7 hCL hB7L
  have hB2 : CFSG.conjugate B g⁻¹ ≤ Subgroup.normalizer (B7 : Set G) := by
    rw [hg, burnsideJ27_normalizer_conjugate]
    exact Subgroup.map_mono hBC
  have hB2L : CFSG.conjugate B g⁻¹ ≤ L := burnsideJ27_conjugate_le hBL (L.inv_mem hgL)
  have hNL : Subgroup.normalizer (B7 : Set G) ⊓ L ≤ L := inf_le_right
  obtain ⟨n, hn, hBn⟩ := burnsideJ27_conj_in_subgroup (p := 3)
    (N := Subgroup.normalizer (B7 : Set G) ⊓ L) (B := B) (B' := CFSG.conjugate B g⁻¹)
    (hL9 _ hNL) hB3 (by rw [burnsideJ27_card_conjugate, hB3]) (le_inf hBN hBL) (le_inf hB2 hB2L)
  have hnN : n ∈ Subgroup.normalizer (B7 : Set G) := hn.1
  have hnL : n ∈ L := hn.2
  refine ⟨n⁻¹ * g * x₁, ?_, ?_, ?_⟩
  · exact L.mul_mem (L.mul_mem (L.inv_mem hnL) hgL) hx₁L
  · have e : (n⁻¹ * g * x₁)⁻¹ = x₁⁻¹ * (g⁻¹ * n) := by group
    rw [e, ← burnsideJ27_conjugate_conjugate, ← hBx₁, ← burnsideJ27_conjugate_conjugate, hBn,
      burnsideJ27_conjugate_conjugate, inv_mul_cancel, burnsideJ27_conjugate_one]
  · have e : (n⁻¹ * g * x₁)⁻¹ = x₁⁻¹ * (g⁻¹ * n) := by group
    rw [e, ← burnsideJ27_conjugate_conjugate, ← hC, ← burnsideJ27_conjugate_conjugate, ← hg]
    ext y
    rw [burnsideJ27_mem_conjugate]
    exact Subgroup.mem_normalizer_iff.mp hnN y

theorem burnsideJ27_conjugate_inf {G : Type*} [Group G] (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊓ B) g = CFSG.conjugate A g ⊓ CFSG.conjugate B g := by
  ext y
  simp only [burnsideJ27_mem_conjugate, Subgroup.mem_inf]

theorem burnsideJ27_conjugate_sup {G : Type*} [Group G] (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g := by
  unfold CFSG.conjugate
  exact Subgroup.map_sup _ _ _

theorem burnsideJ27_cen_conjugate {G : Type*} [Group G] (s g : G) :
    Subgroup.centralizer ({g⁻¹ * s * g} : Set G) =
      CFSG.conjugate (Subgroup.centralizer ({s} : Set G)) g := by
  ext y
  rw [burnsideJ27_mem_conjugate, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * y * g⁻¹ * s = g * (y * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s * g) * y) * g⁻¹ := by rw [h]
      _ = s * (g * y * g⁻¹) := by group
  · intro h
    calc y * (g⁻¹ * s * g) = g⁻¹ * ((g * y * g⁻¹) * s) * g := by group
      _ = g⁻¹ * (s * (g * y * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * s * g) * y := by group

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_S0_conjugate {G : Type} [Group G] {L B7 : Subgroup G} {g : G} (hg :
    g ∈ L) :
    S0Ru L (CFSG.conjugate B7 g) = CFSG.conjugate (S0Ru L B7) g := by
  unfold S0Ru SRu
  have hS : CFSG.conjugate (pCoreOf 2 L) g = pCoreOf 2 L := by
    ext y
    rw [burnsideJ27_mem_conjugate]
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hg) y).symm
  rw [burnsideJ27_conjugate_inf, hS, burnsideJ27_centralizer_conjugate]

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_reduce (hSt : CFSG.Quasithin.RuType.StUniqueStatement) {G : Type}
    [Group G]
    [Finite G] {L V T : Subgroup G} (h : RuType G L V T) {B B7 : Subgroup G}
    (hB : IsSylowIn 3 B (L1Ru L T)) (hB7L : B7 ≤ L) (hB7 : Nat.card B7 = 7)
    (hBN : B ≤ Subgroup.normalizer (B7 : Set G)) :
    ∃ (M : CFSG.Quasithin.RuType.RuDataM G) (g : G), M.L = L ∧ M.T = h.sylowT ∧ g ∈ L ∧
      B = CFSG.conjugate M.B g ∧ B7 = CFSG.conjugate M.B7 g := by
  obtain ⟨M, hML, hMT⟩ := h.exists_ruDataM hSt
  obtain ⟨x, hxL, hBx, hB7x⟩ := burnsideJ27_reduce_aux h M hML hMT hB hB7L hB7 hBN
  exact ⟨M, x⁻¹, hML, hMT, L.inv_mem hxL, hBx, hB7x⟩

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_z_eq {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hMT : M.T = h.sylowT) {z : G}
    (hz : Subgroup.zpowers z = ZRu T) : z = M.z := by
  have hZ : ZRu T = CFSG.Quasithin.RuType.ruZ M.T := by
    rw [hMT]; exact h.ZRu_eq_ruZ
  have hzmem : z ∈ CFSG.Quasithin.RuType.ruZ M.T := by
    rw [← hZ, ← hz]; exact Subgroup.mem_zpowers z
  rcases M.mem_Z_iff.mp hzmem with h1 | h1
  · exfalso
    have hmz : M.z ∈ ZRu T := by rw [hZ]; exact M.z_mem_Z
    rw [← hz, h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hmz
    exact M.z_ne_one hmz
  · exact h1

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_isSylowIn_conjugate {G : Type} [Group G] {p : ℕ} {B X : Subgroup G}
    (g : G)
    (h : IsSylowIn p B X) : IsSylowIn p (CFSG.conjugate B g) (CFSG.conjugate X g) := by
  obtain ⟨hle, hp, hidx⟩ := h
  refine ⟨Subgroup.map_mono hle, hp.of_equiv (Subgroup.equivMapOfInjective B
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective), ?_⟩
  have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) B X
    (MulAut.conj g⁻¹).injective
  unfold Subgroup.relIndex at this
  unfold CFSG.conjugate
  rwa [this]

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_reduce_H (hSt : CFSG.Quasithin.RuType.StUniqueStatement) {G : Type} [Group G]
    [Finite G] {L V T : Subgroup G} (h : RuType G L V T) {B B7 : Subgroup G}
    (hB : IsSylowIn 3 B (L1Ru L T)) (hB7L : B7 ≤ L) (hB7 : Nat.card B7 = 7)
    (hBN : B ≤ Subgroup.normalizer (B7 : Set G)) :
    ∃ (M : CFSG.Quasithin.RuType.RuDataM G) (g : G), M.L = L ∧ M.T = h.sylowT ∧ g ∈ L ∧
      g ∈ HRu T ∧ B = CFSG.conjugate M.B g ∧ B7 = CFSG.conjugate M.B7 g := by
  obtain ⟨M, g, hML, hMT, hgL, hBg, hB7g⟩ := burnsideJ27_reduce hSt h hB hB7L hB7 hBN
  refine ⟨M, g, hML, hMT, hgL, ?_, hBg, hB7g⟩
  have hH : HRu T = CFSG.Quasithin.RuType.ruH M.T := by
    rw [hMT]; exact h.HRu_eq_ruH
  have hBH : B ≤ CFSG.Quasithin.RuType.ruH M.T := by
    refine hB.1.trans ?_
    rw [burnsideJ27_L1_eq h M hML hMT]
    exact (CFSG.GorensteinWalter.pResidualOf_le _ _).trans M.LT1_le_H
  rw [hH, M.mem_H_iff_comm]
  have hV' : g * M.z * g⁻¹ ∈ CFSG.Quasithin.RuType.ruV M.L :=
    M.toRuData.conj_mem_V (hML ▸ hgL) M.z_mem_V
  have hb₁ : g⁻¹ * (M.bel : G) * g ∈ B := by
    rw [hBg, burnsideJ27_mem_conjugate]
    have e : g * (g⁻¹ * (M.bel : G) * g) * g⁻¹ = M.bel := by group
    rw [e]; exact Subgroup.mem_zpowers _
  have hb₁z : g⁻¹ * (M.bel : G) * g * M.z = M.z * (g⁻¹ * (M.bel : G) * g) :=
    ((M.mem_H_iff_comm).mp (hBH hb₁)).symm
  have hbelz' : (M.bel : G) * (g * M.z * g⁻¹) = (g * M.z * g⁻¹) * M.bel := by
    calc (M.bel : G) * (g * M.z * g⁻¹) = g * ((g⁻¹ * M.bel * g) * M.z) * g⁻¹ := by group
      _ = g * (M.z * (g⁻¹ * M.bel * g)) * g⁻¹ := by rw [hb₁z]
      _ = (g * M.z * g⁻¹) * M.bel := by group
  rcases M.eq_of_mem_V_comm_bel hV' hbelz' with h1 | h1
  · exfalso
    apply M.z_ne_one
    have : M.z = g⁻¹ * (g * M.z * g⁻¹) * g := by group
    rw [this, h1]; group
  · calc M.z * g = (g * M.z * g⁻¹) * g := by rw [h1]
      _ = g * M.z := by group

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_ident {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) :
    (M.T : Subgroup G) = T ∧ V = CFSG.Quasithin.RuType.ruV M.L ∧
      ZRu T = CFSG.Quasithin.RuType.ruZ M.T ∧ HRu T = CFSG.Quasithin.RuType.ruH M.T ∧
      QRu T = CFSG.Quasithin.RuType.ruQ M.T ∧ URu V T = CFSG.Quasithin.RuType.ruU M.L M.T := by
  have hT : (M.T : Subgroup G) = T := by rw [hMT]; exact h.coe_sylowT
  have hV : V = CFSG.Quasithin.RuType.ruV M.L := by
    rw [hML]; exact RuType.V_eq_ruV h
  refine ⟨hT, hV, ?_, ?_, ?_, ?_⟩
  · rw [hMT]; exact RuType.ZRu_eq_ruZ h
  · rw [hMT]; exact RuType.HRu_eq_ruH h
  · rw [hMT]; exact RuType.QRu_eq_ruQ h
  · rw [hMT, hML]; exact RuType.URu_eq_ruU h

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_twoResidual_le_K {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) :
    twoResidual (CFSG.Quasithin.RuType.ruH M.T) ≤ M.K ∧
      (M.K.subgroupOf (CFSG.Quasithin.RuType.ruH M.T)).index = 2 := by
  have hker : M.K.subgroupOf (CFSG.Quasithin.RuType.ruH M.T) =
      (SemidirectProduct.rightHom.comp M.φ).ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply,
      CFSG.Quasithin.RuType.RuDataN.mem_K_iff]
    constructor
    · rintro ⟨_, h1⟩
      exact h1
    · intro h1
      exact ⟨x.2, h1⟩
  have hKn : (M.K.subgroupOf (CFSG.Quasithin.RuType.ruH M.T)).Normal := by
    rw [hker]
    infer_instance
  have hKi : (M.K.subgroupOf (CFSG.Quasithin.RuType.ruH M.T)).index = 2 ^ 1 := by
    rw [hker, Subgroup.index_ker]
    have hr : (SemidirectProduct.rightHom.comp M.φ).range = ⊤ := by
      rw [MonoidHom.range_eq_top]
      exact SemidirectProduct.rightHom_surjective.comp M.φ_surj
    rw [hr, Subgroup.card_top, Nat.card_eq_fintype_card]
    rfl
  refine ⟨?_, by simpa using hKi⟩
  calc twoResidual (CFSG.Quasithin.RuType.ruH M.T)
      = (sInf {N : Subgroup ↥(CFSG.Quasithin.RuType.ruH M.T) |
          N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}).map
            (CFSG.Quasithin.RuType.ruH M.T).subtype := rfl
    _ ≤ (M.K.subgroupOf (CFSG.Quasithin.RuType.ruH M.T)).map
          (CFSG.Quasithin.RuType.ruH M.T).subtype :=
        Subgroup.map_mono (sInf_le ⟨hKn, 1, hKi⟩)
    _ = M.K := Subgroup.map_subgroupOf_eq_of_le M.K_le_H

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_KRu_eq {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) : KRu T = M.K := by
  obtain ⟨hT, hV, hZ, hH, hQ, hU⟩ := burnsideJ27_ident h M hML hMT
  obtain ⟨hle0, hKi⟩ := burnsideJ27_twoResidual_le_K M
  have hle : KRu T ≤ M.K := by
    unfold KRu
    rw [hH]
    exact hle0
  obtain ⟨⟨-, -, -, hQK⟩, -, ⟨-, hex⟩, -, -⟩ := as_J_2_2 G L V T h
  obtain ⟨hN, e, -⟩ := hex
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((QRu T).subgroupOf (KRu T))
  rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.RuType.card_subgroupOf_of_le hQK, hQ,
    M.toRuData.card_Q] at h1
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F4) = 60 := by
    letI : Fintype F4 := Fintype.ofFinite _
    have hc : Fintype.card F4 = 4 := by
      rw [← Nat.card_eq_fintype_card]
      show Nat.card (GaloisField 2 2) = 4
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    rw [Matrix.card_SL_field]
    simp [hc]
  rw [hSL] at h1
  have h2 : Nat.card M.K * 2 = Nat.card (CFSG.Quasithin.RuType.ruH M.T) := by
    have h3 := Subgroup.card_mul_index (M.K.subgroupOf (CFSG.Quasithin.RuType.ruH M.T))
    rw [CFSG.Quasithin.RuType.card_subgroupOf_of_le M.K_le_H, hKi] at h3
    exact h3
  rw [M.toRuData.card_H] at h2
  omega

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_LBRu_le {G : Type} [Group G] (B : Subgroup G) :
    LBRu B ≤ Subgroup.centralizer (B : Set G) :=
  Subgroup.map_subtype_le _

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_mem_conjClass_conj_iff {G : Type} [Group G] (s g x : G) :
    x ∈ conjClass (g⁻¹ * s * g) ↔ IsConj s x := by
  rw [burnsideJ27_mem_conjClass_iff]
  constructor
  · intro h
    exact (isConj_iff.mpr ⟨g⁻¹, by group⟩ : IsConj s (g⁻¹ * s * g)).trans h
  · intro h
    exact (isConj_iff.mpr ⟨g, by group⟩ : IsConj (g⁻¹ * s * g) s).trans h

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_part9 {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) (g : G) :
    ∀ i ∈ involutionsOf (Subgroup.centralizer ((CFSG.conjugate M.B g : Subgroup G) : Set G)),
      i ∈ conjClass M.z := by
  rintro i ⟨hi, hi2, hi1⟩
  rw [burnsideJ27_centralizer_conjugate, burnsideJ27_mem_conjugate] at hi
  have hx2 : (g * i * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hi2]; group
  have hx1 : g * i * g⁻¹ ≠ 1 := fun h => hi1 (by
    have : i = g⁻¹ * (g * i * g⁻¹) * g := by group
    rw [this, h]; group)
  obtain ⟨k, hk, hkz⟩ := M.lemma_J27_9 hi hx2 hx1
  refine ⟨k⁻¹ * g, ?_⟩
  calc i = g⁻¹ * (g * i * g⁻¹) * g := by group
    _ = g⁻¹ * (k * M.z * k⁻¹) * g := by rw [hkz]
    _ = (k⁻¹ * g)⁻¹ * M.z * (k⁻¹ * g) := by group

section Cert17

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_part4 {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) (g : G) :
    (∀ i ∈ involutionsOf (⊤ : Subgroup G),
        i ∈ conjClass (g⁻¹ * s * g) ∨ i ∈ conjClass M.z) ∧
      g⁻¹ * s * g ∉ conjClass M.z := by
  obtain ⟨hnz, hcl⟩ := M.lemma_J27_4 hs hs1
  refine ⟨?_, ?_⟩
  · rintro i ⟨-, hi2, hi1⟩
    rcases hcl i hi2 hi1 with h | h
    · exact Or.inr ((burnsideJ27_mem_conjClass_iff _ _).mpr h)
    · exact Or.inl ((burnsideJ27_mem_conjClass_conj_iff s g i).mpr h)
  · intro hmem
    rw [burnsideJ27_mem_conjClass_iff] at hmem
    exact hnz (hmem.trans (isConj_iff.mpr ⟨g, by group⟩))

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_part8bc {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {g : G}
    (hgH : g ∈ CFSG.Quasithin.RuType.ruH M.T) :
    (∀ x ∈ CFSG.Quasithin.RuType.ruH M.T, x ∈ conjClass (g⁻¹ * s * g) →
        ∃ h ∈ CFSG.Quasithin.RuType.ruH M.T, x = h⁻¹ * (g⁻¹ * s * g) * h) ∧
      (∀ x ∈ CFSG.Quasithin.RuType.ruH M.T, x ∈ conjClass (g⁻¹ * s * g) →
        x ∈ M.K ∧ x ∉ CFSG.Quasithin.RuType.ruQ M.T) := by
  constructor
  · intro x hxH hx
    rw [burnsideJ27_mem_conjClass_conj_iff] at hx
    obtain ⟨⟨h, hh, hhs⟩, -, -⟩ := M.lemma_J27_8 hs hs1 hxH hx
    refine ⟨g⁻¹ * h⁻¹, mul_mem (inv_mem hgH) (inv_mem hh), ?_⟩
    rw [← hhs]
    group
  · intro x hxH hx
    rw [burnsideJ27_mem_conjClass_conj_iff] at hx
    obtain ⟨-, hK, hQ⟩ := M.lemma_J27_8 hs hs1 hxH hx
    exact ⟨hK, hQ⟩

theorem burnsideJ27_sylow5_cyclic {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) {B5 : Subgroup G}
    (hB5 : CFSG.ASVolI.ChIJK.IsSylowIn 5 B5 (CFSG.Quasithin.RuType.ruH M.T)) :
    ∃ b ∈ CFSG.Quasithin.RuType.ruH M.T, orderOf b = 5 ∧ B5 = Subgroup.zpowers b := by
  obtain ⟨hle, hp, hidx⟩ := hB5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hmul := Subgroup.card_mul_index (B5.subgroupOf (CFSG.Quasithin.RuType.ruH M.T))
  rw [CFSG.Quasithin.RuType.card_subgroupOf_of_le hle, hn, M.toRuData.card_H] at hmul
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      apply hidx
      rw [pow_zero, one_mul] at hmul
      rw [hmul]
      norm_num
    · rfl
    · exfalso
      have h25 : (5 : ℕ) ^ 2 ∣ 2 ^ 11 * 120 :=
        (pow_dvd_pow 5 (by omega : 2 ≤ n + 1 + 1)).trans (Dvd.intro _ hmul)
      norm_num at h25
  subst hn1
  have hcard : Nat.card B5 = 5 := by rw [hn]; norm_num
  have hnt : Nontrivial B5 := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨⟨b, hbB⟩, hb1⟩ := exists_ne (1 : B5)
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hord : orderOf b = 5 := by
    have h1 : orderOf b ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard B5 hbB
      rwa [hcard] at this
    rcases (Nat.dvd_prime (by norm_num)).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1'
    · exact h
  refine ⟨b, hle hbB, hord, ?_⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB) ?_
  rw [Nat.card_zpowers, hord, hcard]

end Cert17

theorem burnsideJ27_conjugate_self {G : Type} [Group G] {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : CFSG.conjugate X g = X := by
  ext y
  rw [burnsideJ27_mem_conjugate]
  exact (Subgroup.mem_normalizer_iff.mp hg y).symm

theorem burnsideJ27_conjugate_commutator {G : Type} [Group G] (A B : Subgroup G) (g : G) :
    CFSG.conjugate ⁅A, B⁆ g = ⁅CFSG.conjugate A g, CFSG.conjugate B g⁆ := by
  unfold CFSG.conjugate
  exact Subgroup.map_commutator _ _ _

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_isSylowTwoIn_of_sylow {G : Type} [Group G] [Finite G] {C D : Subgroup G}
    (hle : D ≤ C) (h : ∃ P : Sylow 2 ↥C, (P : Subgroup ↥C) = D.subgroupOf C) :
    IsSylowTwoIn D C := by
  obtain ⟨P, hP⟩ := h
  refine ⟨hle, ?_, ?_⟩
  · have h1 : IsPGroup 2 ↥(D.subgroupOf C) := by
      rw [← hP]
      exact P.isPGroup'
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hle)
  · rw [← hP]
    exact P.not_dvd_index

section Cert17

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_part10 {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {g : G}
    (hgL : g ∈ M.L) (hgH : g ∈ CFSG.Quasithin.RuType.ruH M.T) :
    S0Ru M.L (CFSG.conjugate M.B7 g) ⊔
        ⁅SRu M.L ⊓ Subgroup.centralizer ({g⁻¹ * s * g} : Set G), CFSG.conjugate M.B7 g⁆ =
      CFSG.Quasithin.RuType.ruH M.T ⊓ Subgroup.centralizer ({g⁻¹ * s * g} : Set G) ∧
    IsSylowTwoIn (CFSG.Quasithin.RuType.ruH M.T ⊓ Subgroup.centralizer ({g⁻¹ * s * g} : Set G))
      (Subgroup.centralizer ({g⁻¹ * s * g} : Set G)) := by
  obtain ⟨hA, hP⟩ := M.lemma_J27_10 hs hs1
  have hSL : CFSG.conjugate (CFSG.Quasithin.RuType.ruS M.L) g = CFSG.Quasithin.RuType.ruS M.L :=
    burnsideJ27_conjugate_self (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L hgL)
  have hHH : CFSG.conjugate (CFSG.Quasithin.RuType.ruH M.T) g =
      CFSG.Quasithin.RuType.ruH M.T := by
    refine burnsideJ27_conjugate_self ?_
    exact Subgroup.le_normalizer hgH
  have hcen : Subgroup.centralizer ({g⁻¹ * s * g} : Set G) =
      CFSG.conjugate (Subgroup.centralizer ({s} : Set G)) g := burnsideJ27_cen_conjugate s g
  have e1 : S0Ru M.L (CFSG.conjugate M.B7 g) = CFSG.conjugate M.S0 g :=
    burnsideJ27_S0_conjugate hgL
  have e2 : SRu M.L ⊓ Subgroup.centralizer ({g⁻¹ * s * g} : Set G) =
      CFSG.conjugate (CFSG.Quasithin.RuType.ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)) g := by
    rw [burnsideJ27_conjugate_inf, hSL, hcen]
    rfl
  have e3 : CFSG.Quasithin.RuType.ruH M.T ⊓ Subgroup.centralizer ({g⁻¹ * s * g} : Set G) =
      CFSG.conjugate (CFSG.Quasithin.RuType.ruH M.T ⊓ Subgroup.centralizer ({s} : Set G)) g := by
    rw [burnsideJ27_conjugate_inf, hHH, hcen]
  refine ⟨?_, ?_⟩
  · rw [e1, e2, e3, ← burnsideJ27_conjugate_commutator, ← burnsideJ27_conjugate_sup, hA]
  · have h1 : IsSylowTwoIn (CFSG.Quasithin.RuType.ruH M.T ⊓ Subgroup.centralizer ({s} : Set G))
        (Subgroup.centralizer ({s} : Set G)) :=
      burnsideJ27_isSylowTwoIn_of_sylow inf_le_right hP
    have h2 := burnsideJ27_isSylowIn_conjugate (p := 2) g h1
    rw [← e3, ← hcen] at h2
    exact h2

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_P5_eq {G : Type} [Group G] [Finite G] {b : G}
    (hP : Nat.card (CFSG.Quasithin.RuType.P5 b) = 5 ^ 3) :
    CFSG.Quasithin.RuType.P5 b = pCoreOf 5 (CFSG.Quasithin.RuType.G5 b) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hO : Nat.card (CFSG.Quasithin.RuType.O5 b) = 5 ^ 3 := by
    rw [← CFSG.Quasithin.RuType.card_P5, hP]
  have h1 : CFSG.Quasithin.RuType.O5 b ≤ CFSG.pCore 5 ↥(CFSG.Quasithin.RuType.G5 b) := by
    unfold CFSG.pCore
    exact le_sSup ⟨inferInstance, IsPGroup.of_card hO⟩
  have h2 : CFSG.pCore 5 ↥(CFSG.Quasithin.RuType.G5 b) ≤ CFSG.Quasithin.RuType.O5 b := by
    unfold CFSG.Quasithin.RuType.O5 CFSG.oddCore
    refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 5) (G := ↥(CFSG.Quasithin.RuType.G5 b))).exists_card_eq
    rw [hn]
    exact Odd.pow (by decide)
  have h3 : CFSG.Quasithin.RuType.O5 b = CFSG.pCore 5 ↥(CFSG.Quasithin.RuType.G5 b) :=
    le_antisymm h1 h2
  unfold CFSG.Quasithin.RuType.P5 pCoreOf
  rw [h3]

end Cert17

section Cert17

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_part56 {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) (g0 : G) :
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (CFSG.Quasithin.RuType.ruH M.T) →
      Subgroup.centralizer (B5 : Set G) =
          pCoreOf 5 (Subgroup.centralizer (B5 : Set G)) ⊔
            (CFSG.Quasithin.RuType.ruQ M.T ⊓ Subgroup.centralizer (B5 : Set G)) ∧
        Nonempty (↥(CFSG.Quasithin.RuType.ruQ M.T ⊓ Subgroup.centralizer (B5 : Set G)) ≃*
          QuaternionGroup 2) ∧
        Nat.card ↥(pCoreOf 5 (Subgroup.centralizer (B5 : Set G))) = 5 ^ 3 ∧
        ∀ g : G, ¬ IsSylowIn 5 (CFSG.conjugate B5 g) (LBRu (CFSG.conjugate M.B g0)) := by
  intro B5 hB5
  obtain ⟨b, hbH, hb5, rfl⟩ := burnsideJ27_sylow5_cyclic M hB5
  obtain ⟨hP, -, hGeq, -, ⟨eT⟩⟩ := CFSG.Quasithin.RuType.RuDataM.lemma_J27_5 (M := M) hbH hb5
  rw [CFSG.Quasithin.RuType.centralizer_zpowers_eq, ← burnsideJ27_P5_eq hP]
  refine ⟨?_, ⟨eT⟩, hP, ?_⟩
  · refine le_antisymm (fun x hx => ?_) (sup_le (CFSG.Quasithin.RuType.P5_le_G5 b) inf_le_right)
    obtain ⟨p, hp, t, ht, rfl⟩ := hGeq x hx
    exact Subgroup.mul_mem_sup hp ht
  · intro g hg
    have hle : CFSG.conjugate (Subgroup.zpowers b) g ≤
        Subgroup.centralizer ((CFSG.conjugate M.B g0 : Subgroup G) : Set G) :=
      hg.1.trans (burnsideJ27_LBRu_le _)
    have hmem : g⁻¹ * b * g ∈ CFSG.conjugate (Subgroup.zpowers b) g := by
      rw [burnsideJ27_mem_conjugate]
      have e : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
      rw [e]
      exact Subgroup.mem_zpowers b
    have h1 := hle hmem
    rw [burnsideJ27_centralizer_conjugate, burnsideJ27_mem_conjugate] at h1
    apply CFSG.Quasithin.RuType.RuDataM.lemma_J27_6 (M := M) hbH hb5 (g0 * g⁻¹)
    have e : g0 * g⁻¹ * b * (g0 * g⁻¹)⁻¹ = g0 * (g⁻¹ * b * g) * g0⁻¹ := by group
    rw [e]
    exact h1

end Cert17

section Cert15

theorem burnsideJ27_normal_centralizer {G : Type} [Group G] (B : Subgroup G) :
    (B.subgroupOf (Subgroup.centralizer (B : Set G))).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have hc := Subgroup.mem_centralizer_iff.mp g.2 x hx
  have e : ((g * x * g⁻¹ : ↥(Subgroup.centralizer (B : Set G))) : G) = x := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [← hc]
    group
  rw [e]
  exact hx

section Cert110

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_part2 {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) (g : G) :
    ∃ (_ : ((CFSG.conjugate M.B g).subgroupOf
          (Subgroup.centralizer ((CFSG.conjugate M.B g : Subgroup G) : Set G))).Normal),
      Nonempty (↥(Subgroup.centralizer ((CFSG.conjugate M.B g : Subgroup G) : Set G)) ⧸
        (CFSG.conjugate M.B g).subgroupOf
          (Subgroup.centralizer ((CFSG.conjugate M.B g : Subgroup G) : Set G)) ≃*
        ↥(CFSG.Blueprint.NativeSporadic.M11 ⊓
          MulAction.stabilizer (Equiv.Perm (Fin 11)) (0 : Fin 11))) := by
  haveI hN1 := burnsideJ27_normal_centralizer (CFSG.conjugate M.B g)
  refine ⟨hN1, ?_⟩
  obtain ⟨e1⟩ := M.lemma_J27_2
  obtain ⟨e2⟩ := burnsideJ27_quotEquiv_conj (C₁ := Subgroup.centralizer (M.B : Set G))
    (C₂ := Subgroup.centralizer ((CFSG.conjugate M.B g : Subgroup G) : Set G))
    (A₁ := M.B) (A₂ := CFSG.conjugate M.B g) g⁻¹
    (fun x => by
      rw [burnsideJ27_centralizer_conjugate, burnsideJ27_mem_conjugate, inv_inv])
    (fun x => by
      rw [burnsideJ27_mem_conjugate, inv_inv])
  have e3 : ↥CFSG.QuasithinUnique.A6Models.m10 ≃*
      ↥(CFSG.Blueprint.NativeSporadic.M11 ⊓
        MulAction.stabilizer (Equiv.Perm (Fin 11)) (0 : Fin 11)) :=
    (Subgroup.equivMapOfInjective CFSG.QuasithinUnique.A6Models.m10
      CFSG.QuasithinUnique.Unc25G2.psi CFSG.QuasithinUnique.Unc25G2.psi_injective).trans
      (MulEquiv.subgroupCongr CFSG.QuasithinUnique.Unc25G2.map_m10_eq_stab1)
  exact ⟨e2.symm.trans (e1.trans e3)⟩

end Cert110

theorem burnsideJ27_part3 {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) (g : G) :
    ∃ (_ : ((CFSG.conjugate M.B g).subgroupOf
          (Subgroup.normalizer ((CFSG.conjugate M.B g : Subgroup G) : Set G))).Normal),
      Nonempty (↥(Subgroup.normalizer ((CFSG.conjugate M.B g : Subgroup G) : Set G)) ⧸
        (CFSG.conjugate M.B g).subgroupOf
          (Subgroup.normalizer ((CFSG.conjugate M.B g : Subgroup G) : Set G)) ≃*
        MulAut ↥(alternatingGroup (Fin 6))) := by
  haveI hN1 : ((CFSG.conjugate M.B g).subgroupOf
      (Subgroup.normalizer ((CFSG.conjugate M.B g : Subgroup G) : Set G))).Normal :=
    Subgroup.normal_in_normalizer
  refine ⟨hN1, ?_⟩
  obtain ⟨e1⟩ := M.lemma_J27_3
  obtain ⟨e2⟩ := burnsideJ27_quotEquiv_conj (C₁ := Subgroup.normalizer (M.B : Set G))
    (C₂ := Subgroup.normalizer ((CFSG.conjugate M.B g : Subgroup G) : Set G))
    (A₁ := M.B) (A₂ := CFSG.conjugate M.B g) g⁻¹
    (fun x => by
      rw [burnsideJ27_normalizer_conjugate, burnsideJ27_mem_conjugate, inv_inv])
    (fun x => by
      rw [burnsideJ27_mem_conjugate, inv_inv])
  obtain ⟨-, ψ, -, -⟩ := CFSG.QuasithinUnique.Unc25K1.A6Model.exists_pslEquiv
  have e3 : ↥CFSG.QuasithinUnique.A6Models.autA6 ≃* MulAut ↥(alternatingGroup (Fin 6)) :=
    CFSG.QuasithinUnique.Unc25K1.A6Model.conjEquiv.trans (MulAut.congr ψ)
  exact ⟨e2.symm.trans (e1.trans e3)⟩

end Cert15

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_E0perms : List P10 :=
  [1,
    A6Models.perm10 [[0, 1, 7], [2, 9, 4], [3, 8, 5]],
    A6Models.perm10 [[0, 2, 8], [1, 9, 5], [3, 7, 4]],
    A6Models.perm10 [[0, 3, 9], [1, 8, 4], [2, 7, 5]],
    A6Models.perm10 [[0, 4, 5], [1, 2, 3], [7, 9, 8]],
    A6Models.perm10 [[0, 5, 4], [1, 3, 2], [7, 8, 9]],
    A6Models.perm10 [[0, 7, 1], [2, 4, 9], [3, 5, 8]],
    A6Models.perm10 [[0, 8, 2], [1, 5, 9], [3, 4, 7]],
    A6Models.perm10 [[0, 9, 3], [1, 4, 8], [2, 5, 7]]]

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_E0c : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    [1, 7, 9, 8, 2, 3, 6, 0, 5, 4],
    [2, 9, 8, 7, 3, 1, 6, 4, 0, 5],
    [3, 8, 7, 9, 1, 2, 6, 5, 4, 0],
    [4, 2, 3, 1, 5, 0, 6, 9, 7, 8],
    [5, 3, 1, 2, 0, 4, 6, 8, 9, 7],
    [7, 0, 4, 5, 9, 8, 6, 1, 3, 2],
    [8, 5, 0, 4, 7, 9, 6, 3, 2, 1],
    [9, 4, 5, 0, 8, 7, 6, 2, 1, 3]]

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_T0perms : List P10 :=
  [1,
    A6Models.perm10 [[1, 2], [4, 5], [7, 8]],
    A6Models.perm10 [[0, 1], [2, 9], [5, 8]],
    A6Models.perm10 [[0, 1, 9, 2], [4, 8, 7, 5]],
    A6Models.perm10 [[0, 2, 9, 1], [4, 5, 7, 8]],
    A6Models.perm10 [[0, 2], [1, 9], [4, 7]],
    A6Models.perm10 [[0, 4, 9, 7], [1, 5, 2, 8]],
    A6Models.perm10 [[0, 4, 2, 5, 9, 7, 1, 8]],
    A6Models.perm10 [[0, 5, 1, 4, 9, 8, 2, 7]],
    A6Models.perm10 [[0, 5, 9, 8], [1, 7, 2, 4]],
    A6Models.perm10 [[0, 7, 2, 8, 9, 4, 1, 5]],
    A6Models.perm10 [[0, 7, 9, 4], [1, 8, 2, 5]],
    A6Models.perm10 [[0, 8, 9, 5], [1, 4, 2, 7]],
    A6Models.perm10 [[0, 8, 1, 7, 9, 5, 2, 4]],
    A6Models.perm10 [[0, 9], [4, 8], [5, 7]],
    A6Models.perm10 [[0, 9], [1, 2], [4, 7], [5, 8]]]

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_T0c : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    [0, 2, 1, 3, 5, 4, 6, 8, 7, 9],
    [1, 0, 9, 3, 4, 8, 6, 7, 5, 2],
    [1, 9, 0, 3, 8, 4, 6, 5, 7, 2],
    [2, 0, 9, 3, 5, 7, 6, 8, 4, 1],
    [2, 9, 0, 3, 7, 5, 6, 4, 8, 1],
    [4, 5, 8, 3, 9, 2, 6, 0, 1, 7],
    [4, 8, 5, 3, 2, 9, 6, 1, 0, 7],
    [5, 4, 7, 3, 9, 1, 6, 0, 2, 8],
    [5, 7, 4, 3, 1, 9, 6, 2, 0, 8],
    [7, 5, 8, 3, 1, 0, 6, 2, 9, 4],
    [7, 8, 5, 3, 0, 1, 6, 9, 2, 4],
    [8, 4, 7, 3, 2, 0, 6, 1, 9, 5],
    [8, 7, 4, 3, 0, 2, 6, 9, 1, 5],
    [9, 1, 2, 3, 8, 7, 6, 5, 4, 0],
    [9, 2, 1, 3, 7, 8, 6, 4, 5, 0]]

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_E0perms_code : burnsideJ27_E0perms.map code = burnsideJ27_E0c := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_T0perms_code : burnsideJ27_T0perms.map code = burnsideJ27_T0c := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_perms_iff {perms : List P10} {cs : List (List ℕ)}
    (h : perms.map code = cs) (x : P10) : x ∈ perms ↔ code x ∈ cs := by
  rw [← h]
  constructor
  · intro hx
    exact List.mem_map_of_mem hx
  · intro hx
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
    rw [← code_injective hyx]
    exact hy

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_E0c_mul : ∀ a ∈ burnsideJ27_E0c, ∀ b ∈ burnsideJ27_E0c,
    Core.cmul a b ∈ burnsideJ27_E0c := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_E0c_cube : ∀ a ∈ burnsideJ27_E0c, Core.cmul a (Core.cmul a a) = Core.cid := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_E0c_comm : ∀ a ∈ burnsideJ27_E0c, ∀ b ∈ burnsideJ27_E0c,
    Core.cmul a b = Core.cmul b a := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_E0c_psl : ∀ a ∈ burnsideJ27_E0c, a ∈ Core.pslLit := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_E0 : Subgroup P10 where
  carrier := {x | code x ∈ burnsideJ27_E0c}
  mul_mem' := fun {x y} hx hy => by
    show code (x * y) ∈ burnsideJ27_E0c
    rw [code_mul]
    exact burnsideJ27_E0c_mul _ hx _ hy
  one_mem' := by
    show code (1 : P10) ∈ burnsideJ27_E0c
    rw [code_one]
    decide +kernel
  inv_mem' := fun {x} hx => by
    have h1 : x * (x * x) = 1 := by
      apply code_injective
      rw [code_mul, code_mul, code_one]
      exact burnsideJ27_E0c_cube _ hx
    have h2 : x⁻¹ = x * x := inv_eq_of_mul_eq_one_right h1
    show code x⁻¹ ∈ burnsideJ27_E0c
    rw [h2, code_mul]
    exact burnsideJ27_E0c_mul _ hx _ hx

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_E0 {x : P10} : x ∈ burnsideJ27_E0 ↔ code x ∈ burnsideJ27_E0c := Iff.rfl

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_E0_perms {x : P10} : x ∈ burnsideJ27_E0 ↔ x ∈ burnsideJ27_E0perms :=
  (burnsideJ27_mem_perms_iff burnsideJ27_E0perms_code x).symm

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_E0perms_nodup : burnsideJ27_E0perms.Nodup := by
  have h : (burnsideJ27_E0perms.map code).Nodup := by
    rw [burnsideJ27_E0perms_code]
    decide +kernel
  exact List.Nodup.of_map _ h

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_card_E0 : Nat.card burnsideJ27_E0 = 9 := by
  have h : (burnsideJ27_E0 : Set P10) = ↑burnsideJ27_E0perms.toFinset := by
    ext x
    simp [burnsideJ27_mem_E0_perms]
  have h2 : Nat.card burnsideJ27_E0 = Nat.card (burnsideJ27_E0 : Set P10) := rfl
  rw [h2, h, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup burnsideJ27_E0perms_nodup]
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_E0_le_psl : burnsideJ27_E0 ≤ A6Models.psl29 := fun x hx =>
  (mem_psl29_iff x).2 (burnsideJ27_E0c_psl _ hx)

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_E0_comm {x y : P10} (hx : x ∈ burnsideJ27_E0) (hy : y ∈ burnsideJ27_E0) :
    x * y = y * x := by
  apply code_injective
  rw [code_mul, code_mul]
  exact burnsideJ27_E0c_comm _ hx _ hy

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_E0_cube {x : P10} (hx : x ∈ burnsideJ27_E0) : x * (x * x) = 1 := by
  apply code_injective
  rw [code_mul, code_mul, code_one]
  exact burnsideJ27_E0c_cube _ hx

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_f0 : P10 := A6Models.perm10 [[1, 2], [4, 5], [7, 8]]

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_zeta0_code : code A6Models.tInv = [9, 2, 1, 3, 7, 8, 6, 4, 5, 0] := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_f0_code : code burnsideJ27_f0 = [0, 2, 1, 3, 5, 4, 6, 8, 7, 9] := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_zeta0_sq : A6Models.tInv * A6Models.tInv = 1 := by decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_f0_sq : burnsideJ27_f0 * burnsideJ27_f0 = 1 := by decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_f0_comm_zeta0 :
    burnsideJ27_f0 * A6Models.tInv = A6Models.tInv * burnsideJ27_f0 := by decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_f0_mem_s6 : burnsideJ27_f0 ∈ s6 := by
  rw [mem_s6_iff]
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_f0_not_mem_m10 : burnsideJ27_f0 ∉ A6Models.m10 := by
  rw [CFSG.Quasithin.RuType.AutA6.mem_m10_iff]
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_zeta0_inv : ∀ x ∈ burnsideJ27_E0,
    A6Models.tInv * x * A6Models.tInv⁻¹ = x⁻¹ := by
  intro x hx
  have h2 : x⁻¹ = x * x := inv_eq_of_mul_eq_one_right (burnsideJ27_E0_cube hx)
  have h3 : A6Models.tInv⁻¹ = A6Models.tInv := inv_eq_of_mul_eq_one_right burnsideJ27_zeta0_sq
  rw [h2, h3]
  apply code_injective
  rw [code_mul, code_mul, code_mul]
  have hc : ∀ a ∈ burnsideJ27_E0c, Core.cmul (Core.cmul (code A6Models.tInv) a) (code A6Models.tInv) =
      Core.cmul a a := by
    rw [burnsideJ27_zeta0_code]
    decide +kernel
  exact hc _ hx

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_f0_fix : ∃ e ∈ burnsideJ27_E0, e ≠ 1 ∧
    burnsideJ27_f0 * e = e * burnsideJ27_f0 := by
  have hc : ∃ a ∈ burnsideJ27_E0c, a ≠ Core.cid ∧ Core.cmul (code burnsideJ27_f0) a =
      Core.cmul a (code burnsideJ27_f0) := by
    rw [burnsideJ27_f0_code]
    decide +kernel
  obtain ⟨a, ha, ha1, hcomm⟩ := hc
  obtain ⟨e, he, hea⟩ := List.mem_map.mp (by
    rw [burnsideJ27_E0perms_code]; exact ha : a ∈ burnsideJ27_E0perms.map code)
  refine ⟨e, (burnsideJ27_mem_E0_perms).2 he, ?_, ?_⟩
  · intro h1
    apply ha1
    rw [← hea, h1, code_one]
  · apply code_injective
    rw [code_mul, code_mul, hea]
    exact hcomm

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_f0z_fix : ∃ e ∈ burnsideJ27_E0, e ≠ 1 ∧
    (burnsideJ27_f0 * A6Models.tInv) * e = e * (burnsideJ27_f0 * A6Models.tInv) := by
  have hc : ∃ a ∈ burnsideJ27_E0c, a ≠ Core.cid ∧
      Core.cmul (Core.cmul (code burnsideJ27_f0) (code A6Models.tInv)) a =
      Core.cmul a (Core.cmul (code burnsideJ27_f0) (code A6Models.tInv)) := by
    rw [burnsideJ27_f0_code, burnsideJ27_zeta0_code]
    decide +kernel
  obtain ⟨a, ha, ha1, hcomm⟩ := hc
  obtain ⟨e, he, hea⟩ := List.mem_map.mp (by
    rw [burnsideJ27_E0perms_code]; exact ha : a ∈ burnsideJ27_E0perms.map code)
  refine ⟨e, (burnsideJ27_mem_E0_perms).2 he, ?_, ?_⟩
  · intro h1
    apply ha1
    rw [← hea, h1, code_one]
  · apply code_injective
    rw [code_mul, code_mul, code_mul, code_mul, hea]
    exact hcomm

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_T0c_mul : ∀ a ∈ burnsideJ27_T0c, ∀ b ∈ burnsideJ27_T0c,
    Core.cmul a b ∈ burnsideJ27_T0c := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_T0c_pow8 : ∀ a ∈ burnsideJ27_T0c, Core.cmul a (Core.cpow a 7) = Core.cid := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_T0c_pow7 : ∀ a ∈ burnsideJ27_T0c, Core.cpow a 7 ∈ burnsideJ27_T0c := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_T0 : Subgroup P10 where
  carrier := {x | code x ∈ burnsideJ27_T0c}
  mul_mem' := fun {x y} hx hy => by
    show code (x * y) ∈ burnsideJ27_T0c
    rw [code_mul]
    exact burnsideJ27_T0c_mul _ hx _ hy
  one_mem' := by
    show code (1 : P10) ∈ burnsideJ27_T0c
    rw [code_one]
    decide +kernel
  inv_mem' := fun {x} hx => by
    have h1 : x * x ^ 7 = 1 := by
      apply code_injective
      rw [code_mul, code_pow, code_one]
      exact burnsideJ27_T0c_pow8 _ hx
    have h2 : x⁻¹ = x ^ 7 := inv_eq_of_mul_eq_one_right h1
    show code x⁻¹ ∈ burnsideJ27_T0c
    rw [h2, code_pow]
    exact burnsideJ27_T0c_pow7 _ hx

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_T0_perms {x : P10} : x ∈ burnsideJ27_T0 ↔ x ∈ burnsideJ27_T0perms :=
  (burnsideJ27_mem_perms_iff burnsideJ27_T0perms_code x).symm

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_T0perms_nodup : burnsideJ27_T0perms.Nodup := by
  have h : (burnsideJ27_T0perms.map code).Nodup := by
    rw [burnsideJ27_T0perms_code]
    decide +kernel
  exact List.Nodup.of_map _ h

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_card_T0 : Nat.card burnsideJ27_T0 = 16 := by
  have h : (burnsideJ27_T0 : Set P10) = ↑burnsideJ27_T0perms.toFinset := by
    ext x
    simp [burnsideJ27_mem_T0_perms]
  have h2 : Nat.card burnsideJ27_T0 = Nat.card (burnsideJ27_T0 : Set P10) := rfl
  rw [h2, h, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup burnsideJ27_T0perms_nodup]
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_T0c_aut : ∀ a ∈ burnsideJ27_T0c, a ∈ Core.autL := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_T0_le_aut : burnsideJ27_T0 ≤ A6Models.autA6 := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := CFSG.Quasithin.RuType.AutA6.exists_of_mem_autL
    (burnsideJ27_T0c_aut _ hx)
  rw [← code_injective hyx]
  exact hy

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_T0c_norm : ∀ a ∈ burnsideJ27_T0c, ∀ e ∈ burnsideJ27_E0c,
    Core.cmul (Core.cmul a e) (Core.cpow a 7) ∈ burnsideJ27_E0c := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_T0_norm {t x : P10} (ht : t ∈ burnsideJ27_T0) (hx : x ∈ burnsideJ27_E0) :
    t * x * t⁻¹ ∈ burnsideJ27_E0 := by
  have h1 : t * t ^ 7 = 1 := by
    apply code_injective
    rw [code_mul, code_pow, code_one]
    exact burnsideJ27_T0c_pow8 _ ht
  have h2 : t⁻¹ = t ^ 7 := inv_eq_of_mul_eq_one_right h1
  rw [h2, burnsideJ27_mem_E0, code_mul, code_mul, code_pow]
  exact burnsideJ27_T0c_norm _ ht _ hx

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_e1 : P10 := A6Models.perm10 [[0, 3, 9], [1, 8, 4], [2, 7, 5]]

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_e1_code : code burnsideJ27_e1 = [3, 8, 7, 9, 1, 2, 6, 5, 4, 0] := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_Kc : List (List ℕ) :=
  [[0, 5, 9, 1, 8, 2, 6, 4, 3, 7],
    [0, 4, 9, 2, 7, 1, 6, 5, 3, 8],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    [0, 1, 8, 4, 3, 9, 6, 7, 2, 5],
    [0, 2, 7, 5, 3, 9, 6, 8, 1, 4],
    [0, 3, 4, 7, 8, 2, 6, 9, 5, 1],
    [0, 3, 5, 8, 7, 1, 6, 9, 4, 2],
    [0, 7, 8, 9, 5, 4, 6, 1, 2, 3]]

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Kc_check : ∀ a ∈ burnsideJ27_E0c, a = Core.cid ∨
    ∃ c ∈ burnsideJ27_Kc, c ∈ Core.autL ∧ Core.cmul c (code burnsideJ27_e1) = Core.cmul a c ∧
      ∀ x ∈ burnsideJ27_E0c, ∃ x' ∈ burnsideJ27_E0c, Core.cmul c x = Core.cmul x' c := by
  rw [burnsideJ27_e1_code]
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_trans : ∀ e ∈ burnsideJ27_E0, e ≠ 1 → ∃ k ∈ A6Models.autA6,
    (∀ x ∈ burnsideJ27_E0, k * x * k⁻¹ ∈ burnsideJ27_E0) ∧
      k * burnsideJ27_e1 * k⁻¹ = e := by
  intro e he he1
  rcases burnsideJ27_Kc_check _ he with h | ⟨c, -, hcaut, hconj, hnorm⟩
  · exact absurd (by apply code_injective; rw [h, code_one]) he1
  obtain ⟨y, hy, hyc⟩ := CFSG.Quasithin.RuType.AutA6.exists_of_mem_autL hcaut
  refine ⟨y, hy, fun x hx => ?_, ?_⟩
  · obtain ⟨x', hx', hxx⟩ := hnorm _ hx
    have hx'perm : ∃ x'' ∈ burnsideJ27_E0perms, code x'' = x' := by
      have : x' ∈ burnsideJ27_E0perms.map code := by
        rw [burnsideJ27_E0perms_code]; exact hx'
      obtain ⟨x'', hx'', h⟩ := List.mem_map.mp this
      exact ⟨x'', hx'', h⟩
    obtain ⟨x'', hx''mem, hx''c⟩ := hx'perm
    have hyx : y * x = x'' * y := by
      apply code_injective
      rw [code_mul, code_mul, hyc, hx''c]
      exact hxx
    have : y * x * y⁻¹ = x'' := by rw [hyx, mul_inv_cancel_right]
    rw [this]
    exact burnsideJ27_mem_E0_perms.2 hx''mem
  · have hyc' : y * burnsideJ27_e1 = e * y := by
      apply code_injective
      rw [code_mul, code_mul, hyc]
      exact hconj
    rw [hyc', mul_inv_cancel_right]

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_psl_inv_class_check : Core.pslLit.all (fun c =>
    Core.cmul c c != Core.cid || c == Core.cid ||
      Core.pslLit.any fun p => Core.cmul p c == Core.cmul [9, 2, 1, 3, 7, 8, 6, 4, 5, 0] p) =
      true := by
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_m10_cent_check : Core.autL.all (fun c =>
    !(CFSG.Quasithin.RuType.AutA6.inM10L c) ||
      !(burnsideJ27_E0c.all fun e => Core.cmul c e == Core.cmul e c) ||
      burnsideJ27_E0c.contains c) = true := by
  have h : Core.autL.all (fun c =>
      !(Core.cmul c [1, 7, 9, 8, 2, 3, 6, 0, 5, 4] == Core.cmul [1, 7, 9, 8, 2, 3, 6, 0, 5, 4] c) ||
        !(burnsideJ27_E0c.all fun e => Core.cmul c e == Core.cmul e c) ||
        !(CFSG.Quasithin.RuType.AutA6.inM10L c) || burnsideJ27_E0c.contains c) = true := by
    decide +kernel
  have key : ∀ x a m k : Bool, (!x || !a || !m || k) = true → (a = true → x = true) →
      (!m || !a || k) = true := by decide
  rw [List.all_eq_true] at h ⊢
  intro c hc
  refine key _ _ _ _ (h c hc) fun ha => ?_
  rw [List.all_eq_true] at ha
  exact ha _ (by decide)

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_psl_inv_class {ζ : P10} (hζ : ζ ∈ A6Models.psl29) (hζ2 : ζ * ζ = 1)
    (hζ1 : ζ ≠ 1) : ∃ p ∈ A6Models.psl29, p * ζ = A6Models.tInv * p := by
  have h := burnsideJ27_psl_inv_class_check
  rw [List.all_eq_true] at h
  have h1 := h (code ζ) ((mem_psl29_iff ζ).1 hζ)
  have hsq : Core.cmul (code ζ) (code ζ) = Core.cid := by
    rw [← code_mul, hζ2, code_one]
  have hne : code ζ ≠ Core.cid := by
    intro hc
    apply hζ1
    apply code_injective
    rw [hc, code_one]
  simp only [hsq, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h2 | h2
  · exact absurd h2 hne
  · rw [List.any_eq_true] at h2
    obtain ⟨pc, hpc, hpcmul⟩ := h2
    obtain ⟨p, hp, hpcode⟩ := exists_psl29_of_code hpc
    refine ⟨p, hp, ?_⟩
    apply code_injective
    rw [code_mul, code_mul, hpcode, burnsideJ27_zeta0_code]
    simpa using hpcmul

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_m10_le_aut : A6Models.m10 ≤ A6Models.autA6 := by
  unfold A6Models.m10
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact psl29_le_autA6 Out21.A6.tAdd_mem_psl29
  · exact psl29_le_autA6 Out21.A6.tSq_mem_psl29
  · exact psl29_le_autA6 Out21.A6.tInv_mem_psl29
  · exact Out21.A6.tMulFrob_mem_autA6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_m10_cent {x : P10} (hx : x ∈ A6Models.m10)
    (hc : ∀ e ∈ burnsideJ27_E0, x * e = e * x) : x ∈ burnsideJ27_E0 := by
  have h := burnsideJ27_m10_cent_check
  rw [List.all_eq_true] at h
  have h1 := h (code x) (code_mem_autL (burnsideJ27_m10_le_aut hx))
  have hm : CFSG.Quasithin.RuType.AutA6.inM10L (code x) = true :=
    (CFSG.Quasithin.RuType.AutA6.mem_m10_iff x).1 hx
  have hcomm : (burnsideJ27_E0c.all fun e => Core.cmul (code x) e == Core.cmul e (code x)) =
      true := by
    rw [List.all_eq_true]
    intro a ha
    obtain ⟨e, he, hea⟩ := List.mem_map.mp (by
      rw [burnsideJ27_E0perms_code]; exact ha : a ∈ burnsideJ27_E0perms.map code)
    have := hc e (burnsideJ27_mem_E0_perms.2 he)
    have h2 := congrArg code this
    rw [code_mul, code_mul, hea] at h2
    simpa using h2
  simp only [hm, hcomm, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.contains_eq_any_beq,
    List.any_eq_true, beq_iff_eq] at h1
  obtain ⟨a, ha, hax⟩ := h1
  rw [burnsideJ27_mem_E0]
  rw [← hax] at ha
  exact ha

section Lines

variable {R : Type} [Group R] [Finite R]

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem burnsideJ27_aut_lines (hab : ∀ x y : R, x * y = y * x) (d : MulAut R)
    (h : ∀ r : R, d r = r ∨ d r = r⁻¹) : (∀ r : R, d r = r) ∨ (∀ r : R, d r = r⁻¹) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcon
  have ha' : d a = a⁻¹ := (h a).resolve_left ha
  have hb' : d b = b := (h b).resolve_right hb
  have hane : a⁻¹ ≠ a := fun e => ha (by rw [ha', e])
  have hbne : b ≠ b⁻¹ := fun e => hb (by rw [hb', ← e])
  rcases h (a * b) with h1 | h1
  · rw [map_mul, ha', hb'] at h1
    exact hane (mul_right_cancel h1)
  · rw [map_mul, ha', hb', mul_inv_rev, hab b⁻¹ a⁻¹] at h1
    exact hbne (mul_left_cancel h1)

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem burnsideJ27_card_le_two (hab : ∀ x y : R, x * y = y * x) (D : Subgroup (MulAut R))
    (h : ∀ d ∈ D, ∀ r : R, d r = r ∨ d r = r⁻¹) : Nat.card D ≤ 2 := by
  let ι : MulAut R :=
    { toFun := fun x => x⁻¹
      invFun := fun x => x⁻¹
      left_inv := fun x => inv_inv x
      right_inv := fun x => inv_inv x
      map_mul' := fun x y => by rw [mul_inv_rev, hab] }
  have hsub : (D : Set (MulAut R)) ⊆ {1, ι} := by
    intro d hd
    rcases burnsideJ27_aut_lines hab d (h d hd) with h1 | h1
    · left
      exact MulEquiv.ext h1
    · right
      exact MulEquiv.ext h1
  calc Nat.card D = (D : Set (MulAut R)).ncard := Nat.card_coe_set_eq _ |>.symm
    _ ≤ ({1, ι} : Set (MulAut R)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
open scoped Pointwise in
theorem burnsideJ27_card_lines (hexp : ∀ x : R, x ^ 3 = 1) (hcard : Nat.card R = 27) :
    Nat.card {L : Subgroup R // Nat.card L = 3} ≤ 13 := by
  classical
  have hgen : ∀ L : {L : Subgroup R // Nat.card L = 3}, ∃ x : R, x ≠ 1 ∧ Subgroup.zpowers x = L.1 := by
    intro L
    have hnt : Nontrivial L.1 := Finite.one_lt_card_iff_nontrivial.mp (by rw [L.2]; norm_num)
    obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : L.1)
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    refine ⟨x, hx1', ?_⟩
    have hord : orderOf x = 3 := by
      have h1 : orderOf x ∣ 3 := by
        have := Subgroup.orderOf_dvd_natCard L.1 hx
        rwa [L.2] at this
      rcases (Nat.dvd_prime (by norm_num)).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1'
      · exact h
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) (by
      rw [Nat.card_zpowers, hord, L.2])
  choose g hg1 hgL using hgen
  let f : {L : Subgroup R // Nat.card L = 3} × Bool → {x : R // x ≠ 1} := fun p =>
    if p.2 then ⟨g p.1, hg1 p.1⟩ else ⟨(g p.1)⁻¹, inv_ne_one.mpr (hg1 p.1)⟩
  have hf : Function.Injective f := by
    rintro ⟨L, b⟩ ⟨L', b'⟩ h
    have hval : ∀ (L : {L : Subgroup R // Nat.card L = 3}) (b : Bool), (f (L, b)).1 =
        if b then g L else (g L)⁻¹ := by
      intro L b
      cases b <;> rfl
    have hzp : ∀ (L : {L : Subgroup R // Nat.card L = 3}) (b : Bool),
        Subgroup.zpowers (f (L, b)).1 = L.1 := by
      intro L b
      rw [hval]
      cases b
      · simp only [Bool.false_eq_true, ite_false, Subgroup.zpowers_inv]
        exact hgL L
      · simp only [ite_true]
        exact hgL L
    have hLL : L = L' := by
      apply Subtype.ext
      rw [← hzp L b, ← hzp L' b', h]
    subst hLL
    have hbb : b = b' := by
      by_contra hne
      have hval1 := hval L b
      have hval2 := hval L b'
      have e : (f (L, b)).1 = (f (L, b')).1 := by rw [h]
      have h3 := hexp (g L)
      cases b <;> cases b' <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hval1 hval2
      · exact hne rfl
      · rw [hval1, hval2] at e
        have e2 : g L * g L = 1 := mul_eq_one_iff_eq_inv.mpr e.symm
        have : g L = 1 := by
          calc g L = g L ^ 3 * (g L * g L)⁻¹ := by group
            _ = 1 := by rw [h3, e2]; simp
        exact hg1 L this
      · rw [hval1, hval2] at e
        have e2 : g L * g L = 1 := mul_eq_one_iff_eq_inv.mpr e
        have : g L = 1 := by
          calc g L = g L ^ 3 * (g L * g L)⁻¹ := by group
            _ = 1 := by rw [h3, e2]; simp
        exact hg1 L this
      · exact hne rfl
    rw [hbb]
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card {x : R // x ≠ 1} = 26 := by
    letI : Fintype R := Fintype.ofFinite R
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hcard]
  rw [h2, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  omega

end Lines

section Main

variable {R : Type} [Group R] [Finite R]

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem burnsideJ27_smul_eq (Γ : Subgroup (MulAut R)) (γ : ↥Γ) (H : Subgroup R) :
    γ • H = H.map (γ : MulAut R).toMonoidHom := by
  show ((γ : MulAut R) • H) = _
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem burnsideJ27_GT1 (hab : ∀ x y : R, x * y = y * x) (hexp : ∀ x : R, x ^ 3 = 1)
    (hcard : Nat.card R = 27)
    (Γ : Subgroup (MulAut R)) (h3 : ¬ 3 ∣ Nat.card Γ)
    (B : Subgroup R) (hB : Nat.card B = 3)
    (T : Subgroup (MulAut R)) (hTΓ : T ≤ Γ) (hT2 : IsPGroup 2 T) (hT16 : 16 ∣ Nat.card T)
    (hTB : ∀ t ∈ T, B.map t.toMonoidHom = B)
    (g1 g2 : MulAut R) (hg1 : g1 ∈ Γ) (hg2 : g2 ∈ Γ)
    (h1 : B.map g1.toMonoidHom ≠ B) (h2 : B.map g2.toMonoidHom ≠ B)
    (h12 : B.map g1.toMonoidHom ≠ B.map g2.toMonoidHom) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite (MulAut R) :=
    Finite.of_injective (fun f : MulAut R => (f : R → R)) DFunLike.coe_injective
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3) (n := 3) hab hexp
    (by rw [hcard]; norm_num)
  have hAut : Nat.card (MulAut R) = 11232 := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
      CFSG.SectionRank.Ccomm.card_GL_zmod (p := 3) 3]
    simp [Fin.prod_univ_three]
  have hΓ416 : Nat.card Γ ∣ 416 := by
    have h1 : Nat.card Γ ∣ 11232 := hAut ▸ Subgroup.card_subgroup_dvd_card Γ
    have hcop : Nat.Coprime (Nat.card Γ) 27 := by
      have : Nat.Coprime (Nat.card Γ) 3 := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3 |>.symm
      simpa using Nat.Coprime.pow_right 3 this
    have h2 : Nat.card Γ ∣ 27 * 416 := by simpa using h1
    exact hcop.dvd_of_dvd_mul_left h2
  set stab : Subgroup ↥Γ := MulAction.stabilizer ↥Γ B with hstab
  set X : Set (Subgroup R) := MulAction.orbit ↥Γ B with hX
  have hindex := MulAction.index_stabilizer ↥Γ B
  have hmul : Nat.card stab * X.ncard = Nat.card Γ := by
    rw [← hindex]
    exact Subgroup.card_mul_index stab
  have hTstab : T.subgroupOf Γ ≤ stab := by
    intro t ht
    rw [hstab, MulAction.mem_stabilizer_iff, burnsideJ27_smul_eq]
    exact hTB _ (Subgroup.mem_subgroupOf.mp ht)
  have h16 : 16 ∣ Nat.card stab := by
    have h := Subgroup.card_dvd_of_le hTstab
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTΓ).toEquiv] at h
    exact hT16.trans h
  have hX3 : 3 ≤ X.ncard := by
    have hsub : ({B, B.map g1.toMonoidHom, B.map g2.toMonoidHom} : Set (Subgroup R)) ⊆ X := by
      intro L hL
      rcases hL with h | h | h
      · rw [h]; exact MulAction.mem_orbit_self B
      · rw [h]; exact ⟨⟨g1, hg1⟩, burnsideJ27_smul_eq Γ ⟨g1, hg1⟩ B⟩
      · rw [h]; exact ⟨⟨g2, hg2⟩, burnsideJ27_smul_eq Γ ⟨g2, hg2⟩ B⟩
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_eq_three.mpr ⟨_, _, _, h1.symm, h2.symm, h12, rfl⟩] at h
  have hlines : ∀ L ∈ X, Nat.card L = 3 := by
    rintro L ⟨γ, rfl⟩
    show Nat.card ↥(γ • B) = 3
    rw [burnsideJ27_smul_eq, Subgroup.card_map_of_injective (γ : MulAut R).injective]
    exact hB
  have hS3 : ({L : Subgroup R | Nat.card L = 3}).ncard ≤ 13 := by
    have h := burnsideJ27_card_lines hexp hcard
    exact (Nat.card_coe_set_eq {L : Subgroup R | Nat.card L = 3}).symm.trans_le h
  have hX13 : X.ncard ≤ 13 :=
    (Set.ncard_le_ncard (fun L hL => hlines L hL) (Set.toFinite _)).trans hS3
  have key : X.ncard = 13 ∧ (Nat.card stab = 16 ∨ Nat.card stab = 32) := by
    obtain ⟨k, hk⟩ := h16
    have hdiv : Nat.card Γ ∈ Nat.divisors 416 := Nat.mem_divisors.mpr ⟨hΓ416, by norm_num⟩
    have hdivset : Nat.divisors 416 = {1, 2, 4, 8, 13, 16, 26, 32, 52, 104, 208, 416} := by
      decide +kernel
    rw [hdivset] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    rw [hk] at hmul ⊢
    generalize X.ncard = o at *
    interval_cases o <;> omega
  obtain ⟨hX13e, hs⟩ := key
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hΓ13 : Nat.card Γ = 13 * Nat.card stab := by rw [← hmul, hX13e]; ring
  have hs0 : Nat.card stab ≠ 0 := Nat.card_pos.ne'
  have h13s : ¬ 13 ∣ Nat.card stab := by rcases hs with h | h <;> rw [h] <;> norm_num
  obtain ⟨P⟩ : Nonempty (Sylow 13 ↥Γ) := inferInstance
  have hP13 : Nat.card P = 13 := by
    have hfac : (Nat.card Γ).factorization 13 = 1 := by
      rw [hΓ13, Nat.factorization_mul (by norm_num) hs0, Finsupp.add_apply,
        Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd h13s]
    rw [Sylow.card_eq_multiplicity, hfac]
    norm_num
  have hn1 : Nat.card (Sylow 13 ↥Γ) = 1 := by
    have h1 := Sylow.card_dvd_index P
    have h2 := card_sylow_modEq_one 13 ↥Γ
    have h3 : (P : Subgroup ↥Γ).index = Nat.card stab := by
      have h := Subgroup.card_mul_index (P : Subgroup ↥Γ)
      rw [hP13, hΓ13] at h
      omega
    rw [h3] at h1
    unfold Nat.ModEq at h2
    have hle : Nat.card (Sylow 13 ↥Γ) ≤ 32 := by
      have := Nat.le_of_dvd Nat.card_pos h1
      rcases hs with h | h <;> omega
    generalize Nat.card (Sylow 13 ↥Γ) = n at *
    rcases hs with hs | hs <;> rw [hs] at h1 <;> interval_cases n <;> omega
  haveI : Subsingleton (Sylow 13 ↥Γ) := (Nat.card_eq_one_iff_unique.mp hn1).1
  haveI hPn : (P : Subgroup ↥Γ).Normal := Sylow.normal_of_subsingleton P
  let incl : ↥T →* ↥Γ := Subgroup.inclusion hTΓ
  let ψT : ↥T →* MulAut ↥(P : Subgroup ↥Γ) :=
    (MulAut.conjNormal (H := (P : Subgroup ↥Γ))).comp incl
  have hPcyc : IsCyclic ↥(P : Subgroup ↥Γ) := isCyclic_of_prime_card hP13
  have hAutP : Nat.card (MulAut ↥(P : Subgroup ↥Γ)) = 12 := by
    rw [IsCyclic.card_mulAut, hP13, Nat.totient_prime (by norm_num)]
  have hrange12 : Nat.card ψT.range ∣ 12 := by
    have := Subgroup.card_subgroup_dvd_card ψT.range
    rwa [hAutP] at this
  have hkr := Subgroup.card_ker_mul_card_range ψT
  obtain ⟨m, hm⟩ := hT2.exists_card_eq
  have hrangeT : Nat.card ψT.range ∣ 2 ^ m := by
    rw [← hm, ← hkr]
    exact Dvd.intro_left _ rfl
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrangeT
  have hrange4 : Nat.card ψT.range ≤ 4 := by
    rw [hjeq] at hrange12 ⊢
    have hj2 : j ≤ 2 := by
      by_contra hj3
      push Not at hj3
      have h8 : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 hj3).trans hrange12
      norm_num at h8
    calc 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj2
      _ = 4 := by norm_num
  have hkerge : 4 ≤ Nat.card ψT.ker := by
    have hTpos : 16 ≤ Nat.card T := Nat.le_of_dvd Nat.card_pos hT16
    by_contra hlt
    push Not at hlt
    have : Nat.card ψT.ker * Nat.card ψT.range ≤ 3 * 4 := Nat.mul_le_mul (by omega) hrange4
    omega
  let D : Subgroup (MulAut R) := ψT.ker.map T.subtype
  have hDcard : Nat.card D = Nat.card ψT.ker :=
    Subgroup.card_map_of_injective T.subtype_injective
  set XP : Set (Subgroup R) := MulAction.orbit ↥(P : Subgroup ↥Γ) B with hXP
  have hstabP : MulAction.stabilizer ↥(P : Subgroup ↥Γ) B = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [MulAction.mem_stabilizer_iff] at hy
    have hyst : (y : ↥Γ) ∈ stab := by
      rw [hstab, MulAction.mem_stabilizer_iff]
      exact hy
    have hd1 : orderOf (y : ↥Γ) ∣ Nat.card stab := Subgroup.orderOf_dvd_natCard stab hyst
    have hd2 : orderOf (y : ↥Γ) ∣ 13 := by
      have := Subgroup.orderOf_dvd_natCard (P : Subgroup ↥Γ) y.2
      rwa [hP13] at this
    have hcop : Nat.Coprime 13 (Nat.card stab) :=
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h13s
    have hord1 : orderOf (y : ↥Γ) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
    exact Subgroup.mem_bot.mpr (Subtype.ext (orderOf_eq_one_iff.mp hord1))
  have hXPcard : XP.ncard = 13 := by
    have h := MulAction.index_stabilizer ↥(P : Subgroup ↥Γ) B
    rw [hstabP, Subgroup.index_bot] at h
    rw [← h]
    exact hP13
  have hXPX : XP ⊆ X := by
    rintro L ⟨y, rfl⟩
    exact ⟨(y : ↥Γ), rfl⟩
  have hXPeq : XP = X :=
    Set.eq_of_subset_of_ncard_le hXPX (by rw [hXPcard, hX13e]) (Set.toFinite _)
  have hXS3 : X = {L : Subgroup R | Nat.card L = 3} :=
    Set.eq_of_subset_of_ncard_le (fun L hL => hlines L hL) (by rw [hX13e]; exact hS3)
      (Set.toFinite _)
  have hDfix : ∀ d ∈ D, ∀ r : R, d r = r ∨ d r = r⁻¹ := by
    intro d hd r
    obtain ⟨t, htker, rfl⟩ := Subgroup.mem_map.mp hd
    show (t : MulAut R) r = r ∨ (t : MulAut R) r = r⁻¹
    by_cases hr : r = 1
    · left
      rw [hr, map_one]
    have hord : orderOf r = 3 := orderOf_eq_prime (hexp r) hr
    have hline : Subgroup.zpowers r ∈ X := by
      rw [hXS3]
      show Nat.card (Subgroup.zpowers r) = 3
      rw [Nat.card_zpowers, hord]
    rw [← hXPeq] at hline
    obtain ⟨y, hy⟩ := hline
    have hcomm : (incl t : ↥Γ) * (y : ↥Γ) = (y : ↥Γ) * (incl t : ↥Γ) := by
      have h1 := congrArg (fun φ : MulAut ↥(P : Subgroup ↥Γ) => ((φ y : ↥(P : Subgroup ↥Γ)) : ↥Γ))
        (MonoidHom.mem_ker.mp htker)
      simp only [ψT, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc (incl t : ↥Γ) * (y : ↥Γ) = (incl t * y * (incl t)⁻¹) * incl t := by group
        _ = (y : ↥Γ) * incl t := by rw [h1]
    have htB : (incl t : ↥Γ) • B = B := by
      rw [burnsideJ27_smul_eq]
      exact hTB _ t.2
    have hfix : Subgroup.map (t : MulAut R).toMonoidHom (Subgroup.zpowers r) =
        Subgroup.zpowers r := by
      have hy' : (y : ↥Γ) • B = Subgroup.zpowers r := hy
      have e1 : (incl t : ↥Γ) • (Subgroup.zpowers r) = Subgroup.zpowers r := by
        rw [← hy', ← mul_smul, hcomm, mul_smul, htB]
      have e2 : (incl t : ↥Γ) • (Subgroup.zpowers r) =
          Subgroup.map (t : MulAut R).toMonoidHom (Subgroup.zpowers r) := by
        rw [burnsideJ27_smul_eq]
        rfl
      exact e2.symm.trans e1
    have hmem : (t : MulAut R) r ∈ Subgroup.zpowers r := by
      rw [← hfix]
      exact ⟨r, Subgroup.mem_zpowers r, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← zpow_mod_orderOf, hord] at hk
    have h0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h3' : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
    generalize k % ((3 : ℕ) : ℤ) = q at h0 h3' hk
    interval_cases q
    · exfalso
      apply hr
      apply (t : MulAut R).injective
      rw [← hk, zpow_zero, map_one]
    · left
      rw [← hk, zpow_one]
    · right
      rw [← hk]
      have h3 := hexp r
      calc r ^ (2 : ℤ) = r ^ 2 := zpow_ofNat r 2
        _ = r⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← pow_succ, h3]
  have hD2 : Nat.card D ≤ 2 := burnsideJ27_card_le_two hab D hDfix
  omega

end Main

section GT2

variable {G : Type} [Group G] [Finite G]

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem burnsideJ27_mem_map_conj {g x : G} {X : Subgroup G} :
    x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ X := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem burnsideJ27_sylow_conj' {p : ℕ} [Fact p.Prime] {X B₁ B₂ : Subgroup G}
    (hle₁ : B₁ ≤ X) (hp₁ : IsPGroup p B₁) (hi₁ : ¬ p ∣ (B₁.subgroupOf X).index)
    (hle₂ : B₂ ≤ X) (hp₂ : IsPGroup p B₂) (hi₂ : ¬ p ∣ (B₂.subgroupOf X).index) :
    ∃ l ∈ X, ∀ x : G, x ∈ B₂ ↔ l⁻¹ * x * l ∈ B₁ := by
  have hP₁ : IsPGroup p ↥(B₁.subgroupOf X) :=
    hp₁.of_equiv (Subgroup.subgroupOfEquivOfLe hle₁).symm
  have hP₂ : IsPGroup p ↥(B₂.subgroupOf X) :=
    hp₂.of_equiv (Subgroup.subgroupOfEquivOfLe hle₂).symm
  let S₁ : Sylow p ↥X := hP₁.toSylow hi₁
  let S₂ : Sylow p ↥X := hP₂.toSylow hi₂
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥X S₁ S₂
  have key : ∀ z : ↥X, z ∈ (S₂ : Subgroup ↥X) ↔ ∃ s ∈ (S₁ : Subgroup ↥X), y * s * y⁻¹ = z := by
    intro z
    rw [← hy, Sylow.coe_subgroup_smul]
    exact Iff.rfl
  refine ⟨y, y.2, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨s, hs, hsx⟩ := (key ⟨x, hle₂ hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
    have : s = y⁻¹ * ⟨x, hle₂ hx⟩ * y := by rw [← hsx]; group
    rw [this] at hs
    exact Subgroup.mem_subgroupOf.mp hs
  · intro hx
    have hxX : x ∈ X := by
      have h3 : (y : G) * ((y : G)⁻¹ * x * y) * (y : G)⁻¹ ∈ X :=
        X.mul_mem (X.mul_mem y.2 (hle₁ hx)) (X.inv_mem y.2)
      have : (y : G) * ((y : G)⁻¹ * x * y) * (y : G)⁻¹ = x := by group
      rwa [this] at h3
    have hs : (⟨(y : G)⁻¹ * x * y, hle₁ hx⟩ : ↥X) ∈ (S₁ : Subgroup ↥X) :=
      Subgroup.mem_subgroupOf.mpr hx
    have := (key ⟨x, hxX⟩).mpr ⟨_, hs, Subtype.ext (by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group)⟩
    exact Subgroup.mem_subgroupOf.mp this

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem burnsideJ27_TR (R L1 L2 : Subgroup G) (hR : Nat.card R = 27)
    (hRab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (hG81 : ¬ 81 ∣ Nat.card G)
    (hL1 : L1 ≤ R) (hL2 : L2 ≤ R) (g : G)
    (hg : L2 = L1.map (MulAut.conj g⁻¹).toMonoidHom) :
    ∃ k ∈ Subgroup.normalizer (R : Set G), L2 = L1.map (MulAut.conj k).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set C : Subgroup G := Subgroup.centralizer (L2 : Set G) with hC
  set R' : Subgroup G := R.map (MulAut.conj g⁻¹).toMonoidHom with hR'
  have hRC : R ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_iff]
    intro y hy
    exact hRab y (hL2 hy) x hx
  have hR'C : R' ≤ C := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
    rw [hC, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hg] at hy
    obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.mp hy
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hRab ℓ (hL1 hℓ) x hx]
  have hRc : Nat.card R' = 27 := by
    rw [hR', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hR]
  have hidx : ∀ S : Subgroup G, S ≤ C → Nat.card S = 27 → ¬ 3 ∣ (S.subgroupOf C).index := by
    intro S hSC hS h3
    have h1 := Subgroup.card_mul_index (S.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv, hS] at h1
    apply hG81
    obtain ⟨m, hm⟩ := h3
    have hdvd : Nat.card C ∣ Nat.card G := Subgroup.card_subgroup_dvd_card C
    have : 81 ∣ Nat.card C := ⟨m, by rw [← h1, hm]; ring⟩
    exact this.trans hdvd
  have hpg : ∀ S : Subgroup G, Nat.card S = 27 → IsPGroup 3 S := fun S hS =>
    IsPGroup.of_card (n := 3) (by rw [hS]; norm_num)
  obtain ⟨l, hl, hlR⟩ := burnsideJ27_sylow_conj' (p := 3) (X := C) (B₁ := R') (B₂ := R)
    hR'C (hpg _ hRc) (hidx _ hR'C hRc) hRC (hpg _ hR) (hidx _ hRC hR)
  have hcomm : ∀ z ∈ L2, z * l = l * z := fun z hz => (Subgroup.mem_centralizer_iff.mp hl) z hz
  have hc1 : ∀ z ∈ L2, l * z * l⁻¹ = z := by
    intro z hz
    calc l * z * l⁻¹ = (z * l) * l⁻¹ := by rw [← hcomm z hz]
      _ = z := by group
  have hc2 : ∀ z ∈ L2, l⁻¹ * z * l = z := by
    intro z hz
    calc l⁻¹ * z * l = l⁻¹ * (z * l) := by group
      _ = l⁻¹ * (l * z) := by rw [hcomm z hz]
      _ = z := by group
  have hL2mem : ∀ y, y ∈ L2 ↔ g * y * g⁻¹ ∈ L1 := by
    intro y
    rw [hg, burnsideJ27_mem_map_conj, inv_inv]
  refine ⟨l * g⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := hlR (l * g⁻¹ * h * (l * g⁻¹)⁻¹)
    rw [hR', burnsideJ27_mem_map_conj, inv_inv] at h1
    have e : g * (l⁻¹ * (l * g⁻¹ * h * (l * g⁻¹)⁻¹) * l) * g⁻¹ = h := by group
    rw [e] at h1
    exact h1.symm
  · ext y
    rw [burnsideJ27_mem_map_conj]
    have e0 : (l * g⁻¹)⁻¹ * y * (l * g⁻¹) = g * (l⁻¹ * y * l) * g⁻¹ := by group
    rw [e0]
    constructor
    · intro hy
      rw [hc2 y hy]
      exact (hL2mem y).mp hy
    · intro hy
      have hz : l⁻¹ * y * l ∈ L2 := (hL2mem _).mpr hy
      have h4 := hc1 _ hz
      have e2 : l * (l⁻¹ * y * l) * l⁻¹ = y := by group
      rw [e2] at h4
      rw [h4]
      exact hz

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
@[expose] def burnsideJ27_conjAut (R : Subgroup G) (k : G)
    (hk : k ∈ Subgroup.normalizer (R : Set G)) : MulAut ↥R where
  toFun r := ⟨k * r * k⁻¹, (Subgroup.mem_normalizer_iff.mp hk r).mp r.2⟩
  invFun r := ⟨k⁻¹ * r * k, (Subgroup.mem_normalizer_iff.mp hk (k⁻¹ * r * k)).mpr (by
    have : k * (k⁻¹ * (r : G) * k) * k⁻¹ = r := by group
    rw [this]
    exact r.2)⟩
  left_inv r := Subtype.ext (by simp only; group)
  right_inv r := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
@[expose] def burnsideJ27_psi (R : Subgroup G) :
    ↥(Subgroup.normalizer (R : Set G)) →* MulAut ↥R where
  toFun k := burnsideJ27_conjAut R k k.2
  map_one' := by
    ext r
    show (1 : G) * r * (1 : G)⁻¹ = r
    group
  map_mul' a b := by
    ext r
    show ((a * b : ↥(Subgroup.normalizer (R : Set G))) : G) * r * ((a * b : ↥(Subgroup.normalizer
      (R : Set G))) : G)⁻¹ = (a : G) * ((b : G) * r * (b : G)⁻¹) * (a : G)⁻¹
    simp only [Subgroup.coe_mul]
    group

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem burnsideJ27_psi_apply (R : Subgroup G) (k : ↥(Subgroup.normalizer (R : Set G)))
    (r : ↥R) : ((burnsideJ27_psi R k r : ↥R) : G) = (k : G) * r * (k : G)⁻¹ := rfl

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem burnsideJ27_psi_ker (R : Subgroup G)
    (hab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (hC : ∀ x : G, (∀ r ∈ R, x * r = r * x) → x ∈ R) :
    (burnsideJ27_psi R).ker = R.subgroupOf (Subgroup.normalizer (R : Set G)) := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hk
    apply hC
    intro r hr
    have := congrArg (fun f : MulAut ↥R => ((f ⟨r, hr⟩ : ↥R) : G)) hk
    simp only [burnsideJ27_psi_apply, MulAut.one_apply] at this
    calc (k : G) * r = ((k : G) * r * (k : G)⁻¹) * (k : G) := by group
      _ = r * k := by rw [this]
  · intro hk
    ext r
    rw [burnsideJ27_psi_apply]
    show (k : G) * r * (k : G)⁻¹ = r
    rw [hab _ hk _ r.2]
    group

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem burnsideJ27_psi_map (R L : Subgroup G) (k : ↥(Subgroup.normalizer (R : Set G))) :
    (L.subgroupOf R).map (burnsideJ27_psi R k).toMonoidHom =
      (L.map (MulAut.conj (k : G)).toMonoidHom).subgroupOf R := by
  ext r
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    burnsideJ27_mem_map_conj]
  exact Iff.rfl

open scoped Pointwise in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem burnsideJ27_GT2 (R B T B1 B2 : Subgroup G) (hR : Nat.card R = 27)
    (hab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (hexp : ∀ x ∈ R, x ^ 3 = 1)
    (hG81 : ¬ 81 ∣ Nat.card G)
    (hC : ∀ x : G, (∀ r ∈ R, x * r = r * x) → x ∈ R)
    (hBR : B ≤ R) (hB : Nat.card B = 3)
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hTB : T ≤ Subgroup.normalizer (B : Set G))
    (hT2 : IsPGroup 2 T) (hT16 : 16 ∣ Nat.card T)
    (h1R : B1 ≤ R) (h2R : B2 ≤ R) (g1 g2 : G)
    (hg1 : B1 = B.map (MulAut.conj g1⁻¹).toMonoidHom)
    (hg2 : B2 = B.map (MulAut.conj g2⁻¹).toMonoidHom)
    (h1 : B1 ≠ B) (h2 : B2 ≠ B) (h12 : B1 ≠ B2) : False := by
  classical
  set N : Subgroup G := Subgroup.normalizer (R : Set G) with hN
  set ψ := burnsideJ27_psi R with hψ
  have hker := burnsideJ27_psi_ker R hab hC
  have hkerc : Nat.card ψ.ker = 27 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hR]
  have hcard := Subgroup.card_ker_mul_card_range ψ
  have hNG : Nat.card N ∣ Nat.card G := Subgroup.card_subgroup_dvd_card N
  have h3 : ¬ 3 ∣ Nat.card ψ.range := by
    intro h3
    apply hG81
    obtain ⟨m, hm⟩ := h3
    have : 81 ∣ Nat.card N := ⟨m, by rw [← hcard, hkerc, hm]; ring⟩
    exact this.trans hNG
  set TN : Subgroup N := T.subgroupOf N with hTN
  set ψT : ↥TN →* MulAut ↥R := ψ.comp TN.subtype with hψT
  have hψT_inj : Function.Injective ψT := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have hR' : ((t : N) : G) ∈ R := by
      have : (t : N) ∈ ψ.ker := ht
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact this
    have hT' : ((t : N) : G) ∈ T := t.2
    have h27 : ((t : N) : G) ^ 27 = 1 := by
      have := pow_card_eq_one' (G := ↥R) (x := ⟨((t : N) : G), hR'⟩)
      rw [hR] at this
      exact congrArg Subtype.val this
    obtain ⟨k, hk⟩ := hT2 ⟨((t : N) : G), hT'⟩
    have hk' : ((t : N) : G) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h1' : ((t : N) : G) ^ ((2 ^ k).gcd 27) = 1 := pow_gcd_eq_one.mpr ⟨hk', h27⟩
    have hcop : (2 ^ k).gcd 27 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rw [hcop, pow_one] at h1'
    exact Subtype.ext (Subtype.ext h1')
  have hTNcard : Nat.card TN = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv
  have hTRcard : Nat.card ψT.range = Nat.card T := by
    rw [← hTNcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hψT_inj).toEquiv).symm
  have hTRle : ψT.range ≤ ψ.range := by
    rintro _ ⟨t, rfl⟩
    exact ⟨(t : N), rfl⟩
  have hTRp : IsPGroup 2 ψT.range := by
    have hTNp : IsPGroup 2 TN := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTR).symm
    exact hTNp.of_surjective ψT.rangeRestrict ψT.rangeRestrict_surjective
  have hBnorm : ∀ n ∈ T, B.map (MulAut.conj n).toMonoidHom = B := by
    intro n hn
    ext x
    rw [burnsideJ27_mem_map_conj]
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hTB hn)) x)
    simp only [inv_inv] at this
    exact this.symm
  have hTBR : ∀ t ∈ ψT.range, (B.subgroupOf R).map t.toMonoidHom = B.subgroupOf R := by
    rintro _ ⟨n, rfl⟩
    have := burnsideJ27_psi_map R B (n : N)
    have e : ψT n = burnsideJ27_psi R (n : N) := rfl
    rw [e, this, hBnorm ((n : N) : G) n.2]
  obtain ⟨k1, hk1N, hk1⟩ := burnsideJ27_TR R B B1 hR hab hG81 hBR h1R g1 hg1
  obtain ⟨k2, hk2N, hk2⟩ := burnsideJ27_TR R B B2 hR hab hG81 hBR h2R g2 hg2
  have hcc : ∀ (L : Subgroup G), L ≤ R → ∀ (k : G) (hk : k ∈ N),
      L.map (MulAut.conj k).toMonoidHom ≤ R →
      (L.subgroupOf R).map (burnsideJ27_psi R ⟨k, hk⟩).toMonoidHom =
        (L.map (MulAut.conj k).toMonoidHom).subgroupOf R := fun L _ k hk _ =>
    burnsideJ27_psi_map R L ⟨k, hk⟩
  have e1 := hcc B hBR k1 hk1N (hk1 ▸ h1R)
  have e2 := hcc B hBR k2 hk2N (hk2 ▸ h2R)
  rw [← hk1] at e1
  rw [← hk2] at e2
  have hBc : Nat.card (B.subgroupOf R) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBR).toEquiv, hB]
  have hinj : ∀ L L' : Subgroup G, L ≤ R → L' ≤ R → L.subgroupOf R = L'.subgroupOf R → L = L' := by
    intro L L' hL hL' h
    have := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hL, inf_eq_left.mpr hL'] at this
  haveI : Finite ↥R := inferInstance
  refine burnsideJ27_GT1 (R := ↥R)
    (fun x y => Subtype.ext (hab x x.2 y y.2)) (fun x => Subtype.ext (hexp x x.2)) hR
    ψ.range h3 (B.subgroupOf R) hBc ψT.range hTRle hTRp (by rw [hTRcard]; exact hT16) hTBR
    (burnsideJ27_psi R ⟨k1, hk1N⟩) (burnsideJ27_psi R ⟨k2, hk2N⟩)
    ⟨_, rfl⟩ ⟨_, rfl⟩ ?_ ?_ ?_
  · rw [e1]
    intro h
    exact h1 (hinj _ _ h1R hBR h)
  · rw [e2]
    intro h
    exact h2 (hinj _ _ h2R hBR h)
  · rw [e1, e2]
    intro h
    exact h12 (hinj _ _ h1R h2R h)

end GT2

theorem burnsideJ27_mem_perfectResidual_iff {X : Type*} [Group X] {x : X} :
    x ∈ CFSG.perfectResidual X ↔ ∀ n : ℕ, x ∈ derivedSeries X n := by
  unfold CFSG.perfectResidual
  rw [Subgroup.mem_iInf]

theorem burnsideJ27_perfectResidual_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    e x ∈ CFSG.perfectResidual Y ↔ x ∈ CFSG.perfectResidual X := by
  rw [burnsideJ27_mem_perfectResidual_iff, burnsideJ27_mem_perfectResidual_iff]
  refine forall_congr' fun n => ?_
  have h := map_derivedSeries_eq (f := e.toMonoidHom) e.surjective n
  rw [← h]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have : y = x := e.injective hyx
    rw [← this]
    exact hy
  · intro hx
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

theorem burnsideJ27_perfectResidual_eq {X : Type*} [Group X] (P : Subgroup X) (hP : ⁅P, P⁆ = P)
    (hd : commutator X ≤ P) : CFSG.perfectResidual X = P := by
  apply le_antisymm
  · unfold CFSG.perfectResidual
    refine le_trans (iInf_le _ 1) ?_
    rw [derivedSeries_one]
    exact hd
  · unfold CFSG.perfectResidual
    apply le_iInf
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc P = ⁅P, P⁆ := hP.symm
        _ ≤ ⁅derivedSeries X n, derivedSeries X n⁆ := Subgroup.commutator_mono ih ih

@[expose] def burnsideJ27_conjEquiv {G : Type} [Group G] {X₁ X₂ : Subgroup G} (l : G)
    (h : ∀ x : G, x ∈ X₂ ↔ l⁻¹ * x * l ∈ X₁) : ↥X₁ ≃* ↥X₂ where
  toFun x := ⟨l * x * l⁻¹, (h _).mpr (by simpa [mul_assoc] using x.2)⟩
  invFun y := ⟨l⁻¹ * y * l, (h _).mp y.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem burnsideJ27_conjEquiv_apply {G : Type} [Group G] {X₁ X₂ : Subgroup G} (l : G)
    (h : ∀ x : G, x ∈ X₂ ↔ l⁻¹ * x * l ∈ X₁) (x : ↥X₁) :
    ((burnsideJ27_conjEquiv l h x : ↥X₂) : G) = l * x * l⁻¹ := rfl

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_LBRu_conj {G : Type} [Group G] (B : Subgroup G) (g : G) :
    LBRu (CFSG.conjugate B g) = CFSG.conjugate (LBRu B) g := by
  ext x
  have hC : ∀ x : G, x ∈ Subgroup.centralizer ((CFSG.conjugate B g : Subgroup G) : Set G) ↔
      g * x * g⁻¹ ∈ Subgroup.centralizer (B : Set G) := fun x => by
    rw [burnsideJ27_centralizer_conjugate, burnsideJ27_mem_conjugate]
  let e := burnsideJ27_conjEquiv (X₁ := Subgroup.centralizer ((CFSG.conjugate B g :
    Subgroup G) : Set G)) (X₂ := Subgroup.centralizer (B : Set G)) g (fun y => by
      rw [hC]
      have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [this])
  rw [burnsideJ27_mem_conjugate]
  unfold LBRu
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨e y, (burnsideJ27_perfectResidual_equiv e y).mpr hy, ?_⟩
    simp [e, burnsideJ27_conjEquiv_apply]
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hxC : x ∈ Subgroup.centralizer ((CFSG.conjugate B g : Subgroup G) : Set G) := by
      rw [hC, ← hyx]; exact y.2
    refine Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, ?_, rfl⟩
    rw [← burnsideJ27_perfectResidual_equiv e]
    have : e ⟨x, hxC⟩ = y := Subtype.ext (by
      simp [e, burnsideJ27_conjEquiv_apply, ← hyx])
    rw [this]
    exact hy

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_isHatCover_of_equiv {X X' S : Type} [Group X] [Group X'] [Group S]
    (e : X ≃* X') (h : IsHatCover X S) : IsHatCover X' S := by
  obtain ⟨⟨hperf, hsimp, a, b, hab⟩, hcard, ⟨eq⟩⟩ := h
  have hc : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro hx y
      have := hx (e.symm y)
      have h2 := congrArg e this
      simpa using h2
    · intro hx y
      have := hx (e y)
      have h2 := congrArg e.symm this
      simpa using h2
  let eQ : X ⧸ Subgroup.center X ≃* X' ⧸ Subgroup.center X' :=
    QuotientGroup.congr (Subgroup.center X) (Subgroup.center X') e hc
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ⟨eQ.symm.trans eq⟩⟩
  · exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · haveI := hsimp
    haveI : Nontrivial (X' ⧸ Subgroup.center X') := eQ.symm.toEquiv.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective eQ.toMonoidHom eQ.surjective
  · refine ⟨eQ a, eQ b, fun hh => hab ?_⟩
    apply eQ.injective
    rw [map_mul, map_mul]
    exact hh
  · rw [← hc, Subgroup.card_map_of_injective e.injective]
    exact hcard

section Phi

variable {G : Type} [Group G] [Finite G]
  (M : CFSG.Quasithin.RuType.RuDataM G) (e : M.NP ≃* CFSG.QuasithinUnique.A6Models.psl29)

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] noncomputable def burnsideJ27_Phi : ↥M.GP →* Equiv.Perm (Fin 10) :=
  A6Models.autA6.subtype.comp ((M.ρ e).comp (QuotientGroup.mk' (M.B.subgroupOf M.GP)))

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Phi_apply (g : M.GP) :
    burnsideJ27_Phi M e g =
      ((M.ρ e (QuotientGroup.mk g) : A6Models.autA6) : Equiv.Perm (Fin 10)) := rfl

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Phi_mem (g : M.GP) : burnsideJ27_Phi M e g ∈ A6Models.autA6 :=
  (M.ρ e (QuotientGroup.mk g)).2

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Phi_surj {σ : Equiv.Perm (Fin 10)} (hσ : σ ∈ A6Models.autA6) :
    ∃ g : M.GP, burnsideJ27_Phi M e g = σ := by
  obtain ⟨x, hx⟩ := (M.ρ_bijective e).2 ⟨σ, hσ⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨g, congrArg Subtype.val hx⟩

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Phi_eq_one_iff (g : M.GP) :
    burnsideJ27_Phi M e g = 1 ↔ (g : G) ∈ M.B := by
  constructor
  · intro h
    have h1 : (QuotientGroup.mk g : M.XP) = 1 := by
      apply M.ρ_injective e
      rw [map_one]
      exact Subtype.ext h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  · intro h
    have h1 : (QuotientGroup.mk g : M.XP) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact h
    show ((M.ρ e (QuotientGroup.mk g) : A6Models.autA6) : Equiv.Perm (Fin 10)) = 1
    rw [h1, map_one]
    rfl

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Phi_m10 (g : M.GP) :
    burnsideJ27_Phi M e g ∈ A6Models.m10 ↔ (g : G) ∈ M.GB := M.ρ_mk_mem_m10_iff e g

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Phi_ker_eq : (burnsideJ27_Phi M e).ker = M.B.subgroupOf M.GP := by
  ext g
  rw [MonoidHom.mem_ker, burnsideJ27_Phi_eq_one_iff, Subgroup.mem_subgroupOf]

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_card_Phi_ker : Nat.card (burnsideJ27_Phi M e).ker = 3 := by
  rw [burnsideJ27_Phi_ker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe M.B_le_GP).toEquiv]
  exact M.card_B

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_card_comap (S : Subgroup (Equiv.Perm (Fin 10))) (hS : S ≤ A6Models.autA6) :
    Nat.card (S.comap (burnsideJ27_Phi M e)) = 3 * Nat.card S := by
  let Ψ : ↥(S.comap (burnsideJ27_Phi M e)) →* ↥S := (burnsideJ27_Phi M e).subgroupComap S
  have hΨ : Function.Surjective Ψ := by
    rintro ⟨σ, hσ⟩
    obtain ⟨g, hg⟩ := burnsideJ27_Phi_surj M e (hS hσ)
    exact ⟨⟨g, by rw [Subgroup.mem_comap, hg]; exact hσ⟩, Subtype.ext hg⟩
  have h := Subgroup.card_ker_mul_card_of_surjective hΨ
  have hkerle : (burnsideJ27_Phi M e).ker ≤ S.comap (burnsideJ27_Phi M e) := by
    intro g hg
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hg]
    exact S.one_mem
  have hker : Ψ.ker = (burnsideJ27_Phi M e).ker.subgroupOf (S.comap (burnsideJ27_Phi M e)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      exact Subtype.ext hx
  have hk3 : Nat.card Ψ.ker = 3 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv]
    exact burnsideJ27_card_Phi_ker M e
  rw [← h, hk3]

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] noncomputable def burnsideJ27_R0Y : Subgroup ↥M.GP :=
  burnsideJ27_E0.comap (burnsideJ27_Phi M e)

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] noncomputable def burnsideJ27_R0 : Subgroup G :=
  (burnsideJ27_R0Y M e).map M.GP.subtype

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_R0 {x : G} :
    x ∈ burnsideJ27_R0 M e ↔ ∃ g : M.GP, (g : G) = x ∧ burnsideJ27_Phi M e g ∈ burnsideJ27_E0 := by
  unfold burnsideJ27_R0 burnsideJ27_R0Y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, rfl, hg⟩
  · rintro ⟨g, rfl, hg⟩
    exact ⟨g, hg, rfl⟩

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_card_R0 : Nat.card (burnsideJ27_R0 M e) = 27 := by
  unfold burnsideJ27_R0
  rw [Subgroup.card_map_of_injective M.GP.subtype_injective]
  unfold burnsideJ27_R0Y
  rw [burnsideJ27_card_comap M e _ (burnsideJ27_E0_le_psl.trans psl29_le_autA6),
    burnsideJ27_card_E0]

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_B_le_R0 : M.B ≤ burnsideJ27_R0 M e := by
  intro b hb
  rw [burnsideJ27_mem_R0]
  refine ⟨⟨b, M.B_le_GP hb⟩, rfl, ?_⟩
  rw [(burnsideJ27_Phi_eq_one_iff M e _).mpr hb]
  exact burnsideJ27_E0.one_mem

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_R0_le_GB : burnsideJ27_R0 M e ≤ M.GB := by
  intro x hx
  obtain ⟨g, rfl, hg⟩ := (burnsideJ27_mem_R0 M e).mp hx
  exact (burnsideJ27_Phi_m10 M e g).mp (Out21.A6.psl29_le_m10 (burnsideJ27_E0_le_psl hg))

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_GB_of_psl (g : M.GP) (hg : burnsideJ27_Phi M e g ∈ A6Models.psl29) :
    (g : G) ∈ M.GB :=
  (burnsideJ27_Phi_m10 M e g).mp (Out21.A6.psl29_le_m10 hg)

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_exists_T :
    ∃ T : Subgroup G, T ≤ M.GP ∧ IsPGroup 2 T ∧ 16 ∣ Nat.card T ∧
      ∀ t ∈ T, ∃ g : M.GP, (g : G) = t ∧ burnsideJ27_Phi M e g ∈ burnsideJ27_T0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T0Y : Subgroup ↥M.GP := burnsideJ27_T0.comap (burnsideJ27_Phi M e) with hT0Y
  have hc : Nat.card T0Y = 48 := by
    rw [hT0Y, burnsideJ27_card_comap M e _ burnsideJ27_T0_le_aut, burnsideJ27_card_T0]
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥T0Y) 2 (n := 4)
    (by rw [hc]; norm_num)
  have hcard : Nat.card ((K.map T0Y.subtype).map M.GP.subtype) = 2 ^ 4 := by
    rw [Subgroup.card_map_of_injective M.GP.subtype_injective,
      Subgroup.card_map_of_injective T0Y.subtype_injective, hK]
  refine ⟨(K.map T0Y.subtype).map M.GP.subtype, ?_, IsPGroup.of_card hcard, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.2
  · rw [hcard]
    norm_num
  · intro t ht
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨k.1, rfl, k.2⟩

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_exists_zlift :
    ∃ z : M.GP, (z : G) ∈ M.GB ∧ (z : G) * z = 1 ∧ burnsideJ27_Phi M e z = A6Models.tInv := by
  have hmem : A6Models.tInv ∈ A6Models.psl29 := Out21.A6.tInv_mem_psl29
  obtain ⟨z0, hz0⟩ := burnsideJ27_Phi_surj M e (psl29_le_autA6 hmem)
  have hz0GB : (z0 : G) ∈ M.GB := burnsideJ27_mem_GB_of_psl M e z0 (hz0 ▸ hmem)
  have hsq : z0 * z0 ∈ (burnsideJ27_Phi M e).ker := by
    rw [MonoidHom.mem_ker, map_mul, hz0]
    exact burnsideJ27_zeta0_sq
  have hB : ((z0 * z0 : M.GP) : G) ∈ M.B := by
    rw [burnsideJ27_Phi_ker_eq, Subgroup.mem_subgroupOf] at hsq
    exact hsq
  have h3 : ((z0 : G) * z0) ^ 3 = 1 := M.pow_three_of_mem_B hB
  refine ⟨z0 ^ 3, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact pow_mem hz0GB 3
  · rw [Subgroup.coe_pow, ← pow_add, show 3 + 3 = 2 * 3 by norm_num, pow_mul, sq]
    exact h3
  · rw [map_pow, hz0]
    calc A6Models.tInv ^ 3 = A6Models.tInv * (A6Models.tInv * A6Models.tInv) := pow_three _
      _ = A6Models.tInv := by rw [burnsideJ27_zeta0_sq, mul_one]

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_R0_exp3 : ∀ x ∈ burnsideJ27_R0 M e, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨g, rfl, hg⟩ := (burnsideJ27_mem_R0 M e).mp hx
  obtain ⟨z, hzGB, hz2, hzΦ⟩ := burnsideJ27_exists_zlift M e
  have hgGB : (g : G) ∈ M.GB := burnsideJ27_mem_GB_of_psl M e g (burnsideJ27_E0_le_psl hg)
  set a : G := (g : G) with ha
  have hu : burnsideJ27_Phi M e (z * g * z⁻¹ * g) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hzΦ, burnsideJ27_zeta0_inv _ hg, inv_mul_cancel]
  have hc : (((z * g * z⁻¹ * g : M.GP)) : G) ∈ M.B :=
    (burnsideJ27_Phi_eq_one_iff M e _).mp hu
  set c : G := (z : G) * a * (z : G)⁻¹ * a with hcdef
  have hc' : c ∈ M.B := hc
  have hcomm : c * a = a * c := (Subgroup.mem_centralizer_iff.mp hgGB) c hc'
  have hc3 : c ^ 3 = 1 := M.pow_three_of_mem_B hc'
  have ha3 : a ^ 3 ∈ M.B := by
    have : burnsideJ27_Phi M e (g ^ 3) = 1 := by
      rw [map_pow]
      calc burnsideJ27_Phi M e g ^ 3 = burnsideJ27_Phi M e g * (burnsideJ27_Phi M e g *
          burnsideJ27_Phi M e g) := pow_three _
        _ = 1 := burnsideJ27_E0_cube hg
    exact (burnsideJ27_Phi_eq_one_iff M e _).mp this
  have hzaz : (z : G) * a * (z : G)⁻¹ = c * a⁻¹ := by rw [hcdef]; group
  have h1 : (z : G) * a ^ 3 * (z : G)⁻¹ = (c * a⁻¹) ^ 3 := by
    rw [← hzaz, conj_pow]
  have h2 : (c * a⁻¹) ^ 3 = (a ^ 3)⁻¹ := by
    rw [(Commute.inv_right (show Commute c a from hcomm)).mul_pow, hc3, one_mul, inv_pow]
  have h3 : (z : G) * a ^ 3 * (z : G)⁻¹ = a ^ 3 := by
    have := (Subgroup.mem_centralizer_iff.mp hzGB) (a ^ 3) ha3
    calc (z : G) * a ^ 3 * (z : G)⁻¹ = (a ^ 3 * z) * (z : G)⁻¹ := by rw [this]
      _ = a ^ 3 := by group
  have h4 : a ^ 3 * a ^ 3 = 1 := by
    have : a ^ 3 = (a ^ 3)⁻¹ := h3.symm.trans (h1.trans h2)
    calc a ^ 3 * a ^ 3 = (a ^ 3)⁻¹ * a ^ 3 := by rw [← this]
      _ = 1 := inv_mul_cancel _
  have h5 : (a ^ 3) ^ 3 = 1 := M.pow_three_of_mem_B ha3
  calc a ^ 3 = (a ^ 3) ^ 3 * (a ^ 3 * a ^ 3)⁻¹ := by group
    _ = 1 := by rw [h5, h4]; group

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_T_normalizes {T : Subgroup G}
    (hT : ∀ t ∈ T, ∃ g : M.GP, (g : G) = t ∧ burnsideJ27_Phi M e g ∈ burnsideJ27_T0)
    {t : G} (ht : t ∈ T) : t ∈ Subgroup.normalizer ((burnsideJ27_R0 M e : Subgroup G) : Set G) := by
  have key : ∀ t ∈ T, ∀ x ∈ burnsideJ27_R0 M e, t * x * t⁻¹ ∈ burnsideJ27_R0 M e := by
    intro t ht x hx
    obtain ⟨k, rfl, hk⟩ := hT t ht
    obtain ⟨g, rfl, hg⟩ := (burnsideJ27_mem_R0 M e).mp hx
    rw [burnsideJ27_mem_R0]
    refine ⟨k * g * k⁻¹, by simp, ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact burnsideJ27_T0_norm hk hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key t ht x hx
  · intro hx
    have := key t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_R0_cent {x : G} (hx : ∀ r ∈ burnsideJ27_R0 M e, x * r = r * x) :
    x ∈ burnsideJ27_R0 M e := by
  have hxGB : x ∈ M.GB := by
    rw [M.mem_GB]
    exact (hx _ (burnsideJ27_B_le_R0 M e (Subgroup.mem_zpowers _))).symm
  have hxGP : x ∈ M.GP := M.GB_le_GP hxGB
  set y : M.GP := ⟨x, hxGP⟩ with hy
  have hym : burnsideJ27_Phi M e y ∈ A6Models.m10 := (burnsideJ27_Phi_m10 M e y).mpr hxGB
  have hcomm : ∀ ε ∈ burnsideJ27_E0, burnsideJ27_Phi M e y * ε = ε * burnsideJ27_Phi M e y := by
    intro ε hε
    obtain ⟨r, hr⟩ := burnsideJ27_Phi_surj M e (psl29_le_autA6 (burnsideJ27_E0_le_psl hε))
    have hrR : (r : G) ∈ burnsideJ27_R0 M e := (burnsideJ27_mem_R0 M e).mpr ⟨r, rfl, hr ▸ hε⟩
    have h1 : y * r = r * y := Subtype.ext (hx _ hrR)
    have h2 := congrArg (burnsideJ27_Phi M e) h1
    rw [map_mul, map_mul, hr] at h2
    exact h2
  exact (burnsideJ27_mem_R0 M e).mpr ⟨y, rfl, burnsideJ27_m10_cent hym hcomm⟩

end Phi

section Main

variable {G : Type} [Group G] [Finite G]
  (M : CFSG.Quasithin.RuType.RuDataM G) (e : M.NP ≃* CFSG.QuasithinUnique.A6Models.psl29)

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_exists_xf {σ a : Equiv.Perm (Fin 10)} (hσ : σ ∈ A6Models.autA6)
    (hσ2 : σ * σ = 1) (hσm : σ ∉ A6Models.m10) (hσs : σ ∈ s6)
    (ha : a ∈ burnsideJ27_E0) (hcomm : σ * a = a * σ) :
    ∃ f x : M.GP, burnsideJ27_Phi M e f = σ ∧ burnsideJ27_Phi M e x = a ∧
      (f : G) * f = 1 ∧ (f : G) ∉ M.GB ∧ IsConj M.z (f : G) ∧ (f : G) * x = x * f := by
  obtain ⟨f, hfσ, hfB, hf2, hfinv⟩ := M.exists_lift_inv e hσ hσ2 hσm
  have hfΦ : burnsideJ27_Phi M e f = σ := hfσ
  have hfz : IsConj M.z (f : G) := (M.outer_inv_classes e f hfB hf2).1 (by rw [hfσ]; exact hσs)
  have haE : a ∈ A6Models.psl29 := burnsideJ27_E0_le_psl ha
  obtain ⟨ê, hê⟩ := burnsideJ27_Phi_surj M e (psl29_le_autA6 haE)
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  set b0' : M.GP := ê⁻¹ * (f * ê * f⁻¹) with hb0'
  have hb0Φ : burnsideJ27_Phi M e b0' = 1 := by
    rw [hb0', map_mul, map_mul, map_mul, map_inv, map_inv, hê, hfΦ, hσinv]
    calc a⁻¹ * (σ * a * σ) = a⁻¹ * (a * σ * σ) := by rw [hcomm]
      _ = 1 := by rw [mul_assoc, hσ2]; group
  have hb0 : ((b0' : M.GP) : G) ∈ M.B := (burnsideJ27_Phi_eq_one_iff M e _).mp hb0Φ
  set b0 : G := ((b0' : M.GP) : G) with hb0def
  have hb0eq : b0 = (ê : G)⁻¹ * ((f : G) * ê * (f : G)⁻¹) := by
    rw [hb0def, hb0']
    simp
  have e1 : (f : G) * ê = ê * b0 * f := by
    rw [hb0eq]
    group
  have e2 : (f : G) * b0⁻¹ = b0 * f := by
    have := M.conj_B_of_inv hfinv (inv_mem hb0)
    calc (f : G) * b0⁻¹ = ((f : G) * b0⁻¹ * (f : G)⁻¹) * f := by group
      _ = b0 * f := by rw [this, inv_inv]
  have hb03 : b0 ^ 3 = 1 := M.pow_three_of_mem_B hb0
  have hb02 : b0 * b0 = b0⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_three']
    exact hb03
  refine ⟨f, ê * b0'⁻¹, hfΦ, ?_, hf2, hfB, hfz, ?_⟩
  · rw [map_mul, map_inv, hb0Φ, hê]
    simp
  · simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    change (f : G) * ((ê : G) * b0⁻¹) = ((ê : G) * b0⁻¹) * f
    calc (f : G) * ((ê : G) * b0⁻¹) = ((f : G) * ê) * b0⁻¹ := by group
      _ = (ê * b0 * f) * b0⁻¹ := by rw [e1]
      _ = ê * b0 * ((f : G) * b0⁻¹) := by group
      _ = ê * b0 * (b0 * f) := by rw [e2]
      _ = ê * (b0 * b0) * f := by group
      _ = ((ê : G) * b0⁻¹) * f := by rw [hb02]

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_zpowers_eq_conj {x w : G}
    (hw : w * x * w⁻¹ = M.bel ∨ w * x * w⁻¹ = (M.bel : G)⁻¹) :
    Subgroup.zpowers x = M.B.map (MulAut.conj w⁻¹).toMonoidHom := by
  ext y
  rw [burnsideJ27_mem_map_conj, inv_inv]
  constructor
  · rintro ⟨k, rfl⟩
    have h : w * x ^ k * w⁻¹ = (w * x * w⁻¹) ^ k := conj_zpow.symm
    rw [h]
    rcases hw with hw | hw
    · rw [hw]
      exact zpow_mem (Subgroup.mem_zpowers _) k
    · rw [hw]
      exact zpow_mem (inv_mem (Subgroup.mem_zpowers _)) k
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    rcases hw with hw | hw
    · refine ⟨k, ?_⟩
      calc x ^ k = w⁻¹ * (w * x ^ k * w⁻¹) * w := by group
        _ = w⁻¹ * (w * x * w⁻¹) ^ k * w := by rw [conj_zpow]
        _ = w⁻¹ * (M.bel : G) ^ k * w := by rw [hw]
        _ = w⁻¹ * (w * y * w⁻¹) * w := by rw [hk]
        _ = y := by group
    · refine ⟨-k, ?_⟩
      calc x ^ (-k) = w⁻¹ * (w * x ^ (-k) * w⁻¹) * w := by group
        _ = w⁻¹ * (w * x * w⁻¹) ^ (-k) * w := by rw [conj_zpow]
        _ = w⁻¹ * ((M.bel : G)⁻¹) ^ (-k) * w := by rw [hw]
        _ = w⁻¹ * (M.bel : G) ^ k * w := by rw [inv_zpow, zpow_neg, inv_inv]
        _ = w⁻¹ * (w * y * w⁻¹) * w := by rw [hk]
        _ = y := by group

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_conj_to_B {f x : G} (hfz : IsConj M.z f) (hfx : f * x = x * f)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ w : G, Subgroup.zpowers x = M.B.map (MulAut.conj w⁻¹).toMonoidHom := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hfz
  set y : G := c⁻¹ * x * c with hy
  have hyz : y * M.z = M.z * y := by
    have hfc : f * c = c * M.z := by rw [← hc]; group
    calc y * M.z = c⁻¹ * x * (c * M.z) := by rw [hy]; group
      _ = c⁻¹ * x * (f * c) := by rw [hfc]
      _ = c⁻¹ * (x * f) * c := by group
      _ = c⁻¹ * (f * x) * c := by rw [hfx]
      _ = (c⁻¹ * f * c) * (c⁻¹ * x * c) := by group
      _ = M.z * y := by rw [← hc, hy]; group
  have hyH : y ∈ ruH M.T := by
    rw [← M.centralizer_z_eq_H]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hyz
  have hy3 : y ^ 3 = 1 := by
    calc y ^ 3 = y * y * y := pow_three' y
      _ = c⁻¹ * (x * x * x) * c := by rw [hy]; group
      _ = 1 := by rw [← pow_three', hx3]; group
  have hy1 : y ≠ 1 := fun h => hx1 (by
    have : x = c * y * c⁻¹ := by rw [hy]; group
    rw [this, h]
    group)
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨h, -, hh⟩ := M.exists_conj_bel hyH (orderOf_eq_prime hy3 hy1)
  refine ⟨h * c⁻¹, burnsideJ27_zpowers_eq_conj M ?_⟩
  have hw : (h * c⁻¹) * x * (h * c⁻¹)⁻¹ = h * y * h⁻¹ := by rw [hy]; group
  rw [hw]
  exact hh

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_R0_not_comm :
    ¬ (∀ x ∈ burnsideJ27_R0 M e, ∀ y ∈ burnsideJ27_R0 M e, x * y = y * x) := by
  intro hab
  obtain ⟨T, hTGP, hT2, hT16, hTΦ⟩ := burnsideJ27_exists_T M e
  have h81 : ¬ 81 ∣ Nat.card G := by
    rw [M.card_eq]
    norm_num
  obtain ⟨e1, he1, he11, hf1⟩ := burnsideJ27_f0_fix
  obtain ⟨e2, he2, he21, hf2⟩ := burnsideJ27_f0z_fix
  have hζ : A6Models.tInv ∈ A6Models.psl29 := Out21.A6.tInv_mem_psl29
  have hf0aut : burnsideJ27_f0 ∈ A6Models.autA6 := s6_le_autA6 burnsideJ27_f0_mem_s6
  have hzm : A6Models.tInv ∈ A6Models.m10 := Out21.A6.psl29_le_m10 hζ
  have hfz0 : burnsideJ27_f0 * A6Models.tInv ∈ A6Models.autA6 :=
    A6Models.autA6.mul_mem hf0aut (psl29_le_autA6 hζ)
  have hfz2 : (burnsideJ27_f0 * A6Models.tInv) * (burnsideJ27_f0 * A6Models.tInv) = 1 := by
    calc burnsideJ27_f0 * A6Models.tInv * (burnsideJ27_f0 * A6Models.tInv)
        = burnsideJ27_f0 * (A6Models.tInv * burnsideJ27_f0) * A6Models.tInv := by group
      _ = burnsideJ27_f0 * (burnsideJ27_f0 * A6Models.tInv) * A6Models.tInv := by
          rw [← burnsideJ27_f0_comm_zeta0]
      _ = (burnsideJ27_f0 * burnsideJ27_f0) * (A6Models.tInv * A6Models.tInv) := by group
      _ = 1 := by rw [burnsideJ27_f0_sq, burnsideJ27_zeta0_sq, one_mul]
  have hfzm : burnsideJ27_f0 * A6Models.tInv ∉ A6Models.m10 := fun h =>
    burnsideJ27_f0_not_mem_m10 (by
      have := A6Models.m10.mul_mem h (A6Models.m10.inv_mem hzm)
      simpa using this)
  have hfzs : burnsideJ27_f0 * A6Models.tInv ∈ s6 :=
    s6.mul_mem burnsideJ27_f0_mem_s6 (psl29_le_s6 hζ)
  obtain ⟨f, x, hfΦ, hxΦ, hff, hfB, hfz, hfx⟩ := burnsideJ27_exists_xf M e hf0aut
    burnsideJ27_f0_sq burnsideJ27_f0_not_mem_m10 burnsideJ27_f0_mem_s6 he1 hf1
  obtain ⟨f', x', hf'Φ, hx'Φ, hf'f', hf'B, hf'z, hf'x'⟩ := burnsideJ27_exists_xf M e hfz0
    hfz2 hfzm hfzs he2 hf2
  have hxR : (x : G) ∈ burnsideJ27_R0 M e :=
    (burnsideJ27_mem_R0 M e).mpr ⟨x, rfl, hxΦ ▸ he1⟩
  have hx'R : (x' : G) ∈ burnsideJ27_R0 M e :=
    (burnsideJ27_mem_R0 M e).mpr ⟨x', rfl, hx'Φ ▸ he2⟩
  have hx1' : (x : G) ≠ 1 := fun h => he11 (by
    rw [← hxΦ, show x = 1 from Subtype.ext h, map_one])
  have hx'1' : (x' : G) ≠ 1 := fun h => he21 (by
    rw [← hx'Φ, show x' = 1 from Subtype.ext h, map_one])
  obtain ⟨w1, hw1⟩ := burnsideJ27_conj_to_B M hfz hfx (burnsideJ27_R0_exp3 M e _ hxR) hx1'
  obtain ⟨w2, hw2⟩ := burnsideJ27_conj_to_B M hf'z hf'x' (burnsideJ27_R0_exp3 M e _ hx'R) hx'1'
  refine burnsideJ27_GT2 (burnsideJ27_R0 M e) M.B T (Subgroup.zpowers (x : G))
    (Subgroup.zpowers (x' : G)) (burnsideJ27_card_R0 M e) hab (burnsideJ27_R0_exp3 M e) h81
    (fun y hy => burnsideJ27_R0_cent M e hy) (burnsideJ27_B_le_R0 M e) M.card_B
    (fun t ht => burnsideJ27_T_normalizes M e hTΦ ht) hTGP hT2 hT16
    (Subgroup.zpowers_le.mpr hxR) (Subgroup.zpowers_le.mpr hx'R) w1 w2 hw1 hw2 ?_ ?_ ?_
  · intro h
    have hxB : (x : G) ∈ M.B := h ▸ Subgroup.mem_zpowers _
    exact he11 (hxΦ ▸ (burnsideJ27_Phi_eq_one_iff M e x).mpr hxB)
  · intro h
    have hxB : (x' : G) ∈ M.B := h ▸ Subgroup.mem_zpowers _
    exact he21 (hx'Φ ▸ (burnsideJ27_Phi_eq_one_iff M e x').mpr hxB)
  · intro h
    have hmem : (x' : G) ∈ Subgroup.zpowers (x : G) := h ▸ Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hc : Commute (f : G) (x : G) := hfx
    have hc' : (f : G) * x' = x' * f := by
      have := hc.zpow_right k
      rw [hk] at this
      exact this
    have h1 : f * x' = x' * f := Subtype.ext hc'
    have h2 := congrArg (burnsideJ27_Phi M e) h1
    rw [map_mul, map_mul, hfΦ, hx'Φ] at h2
    have hz : A6Models.tInv * e2 = e2 * A6Models.tInv := by
      calc A6Models.tInv * e2 = burnsideJ27_f0⁻¹ * (burnsideJ27_f0 * A6Models.tInv * e2) := by
            group
        _ = burnsideJ27_f0⁻¹ * (e2 * (burnsideJ27_f0 * A6Models.tInv)) := by rw [hf2]
        _ = burnsideJ27_f0⁻¹ * ((e2 * burnsideJ27_f0) * A6Models.tInv) := by group
        _ = burnsideJ27_f0⁻¹ * ((burnsideJ27_f0 * e2) * A6Models.tInv) := by rw [← h2]
        _ = e2 * A6Models.tInv := by group
    have hinv := burnsideJ27_zeta0_inv e2 he2
    have hee : e2 * e2 = 1 := by
      have h3 : A6Models.tInv * e2 * A6Models.tInv⁻¹ = e2 := by rw [hz]; group
      have h4 : e2 = e2⁻¹ := h3.symm.trans hinv
      calc e2 * e2 = e2⁻¹ * e2 := by rw [← h4]
        _ = 1 := inv_mul_cancel _
    apply he21
    calc e2 = e2 * (e2 * e2) := by rw [hee, mul_one]
      _ = 1 := burnsideJ27_E0_cube he2

end Main

section N

variable {G : Type} [Group G] [Finite G]
  (M : CFSG.Quasithin.RuType.RuDataM G) (e : M.NP ≃* CFSG.QuasithinUnique.A6Models.psl29)

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_NXG_le_GB : M.NXG ≤ M.GB := Subgroup.map_subtype_le _

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_NXG_le_GP : M.NXG ≤ M.GP := (burnsideJ27_NXG_le_GB M).trans M.GB_le_GP

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_B_le_NXG : M.B ≤ M.NXG := by
  intro b hb
  refine Subgroup.mem_map.mpr ⟨⟨b, M.B_le_GB hb⟩, M.BX_le_NX (Subgroup.mem_subgroupOf.mpr hb), rfl⟩

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_NXG_iff (g : M.GP) :
    (g : G) ∈ M.NXG ↔ burnsideJ27_Phi M e g ∈ A6Models.psl29 := by
  constructor
  · intro hg
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
    have hn : M.ι (QuotientGroup.mk x) ∈ M.NP := ⟨QuotientGroup.mk x, ⟨x, hx, rfl⟩, rfl⟩
    have h1 : M.ι (QuotientGroup.mk x) = (QuotientGroup.mk g : M.XP) := by
      rw [M.ι_mk]
      congr 1
      exact Subtype.ext hxg
    have h2 := M.ρ_NP e ⟨M.ι (QuotientGroup.mk x), hn⟩
    rw [burnsideJ27_Phi_apply]
    have h3 : ((M.ρ e (QuotientGroup.mk g) : A6Models.autA6) : Equiv.Perm (Fin 10)) =
        (e ⟨M.ι (QuotientGroup.mk x), hn⟩ : Equiv.Perm (Fin 10)) := by
      rw [← h1]
      exact h2
    rw [h3]
    exact (e _).2
  · intro hg
    set n : M.NP := e.symm ⟨burnsideJ27_Phi M e g, hg⟩ with hn
    have h1 : ((M.ρ e (n : M.XP) : A6Models.autA6) : Equiv.Perm (Fin 10)) =
        (e n : Equiv.Perm (Fin 10)) := M.ρ_NP e n
    have h2 : e n = ⟨burnsideJ27_Phi M e g, hg⟩ := by
      rw [hn]
      exact e.apply_symm_apply _
    have h3 : M.ρ e (n : M.XP) = M.ρ e (QuotientGroup.mk g) := by
      apply Subtype.ext
      rw [h1, h2]
      rfl
    have h4 : (n : M.XP) = QuotientGroup.mk g := M.ρ_injective e h3
    have hmem : (QuotientGroup.mk g : M.XP) ∈ M.NP := h4 ▸ n.2
    obtain ⟨w, hw, hwg⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    have hwg' : M.ι (QuotientGroup.mk x) = QuotientGroup.mk g := hwg
    rw [M.ι_mk, QuotientGroup.eq] at hwg'
    have hb := Subgroup.mem_subgroupOf.mp hwg'
    have hb' : ((Subgroup.inclusion M.GB_le_GP x)⁻¹ * g : M.GP) = ⟨(x : G)⁻¹ * g, by
        simpa using M.GP.mul_mem (M.GP.inv_mem (M.GB_le_GP x.2)) g.2⟩ := rfl
    have hbB : (x : G)⁻¹ * (g : G) ∈ M.B := by
      have := hb
      simpa using this
    refine Subgroup.mem_map.mpr ⟨x * ⟨(x : G)⁻¹ * g, M.B_le_GB hbB⟩, ?_, ?_⟩
    · exact mul_mem hx (M.BX_le_NX (Subgroup.mem_subgroupOf.mpr hbB))
    · simp

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] noncomputable def burnsideJ27_pi : ↥M.NXG →* ↥A6Models.psl29 :=
  ((burnsideJ27_Phi M e).comp (Subgroup.inclusion (burnsideJ27_NXG_le_GP M))).codRestrict
    A6Models.psl29
    (fun x => (burnsideJ27_mem_NXG_iff M e ⟨x, burnsideJ27_NXG_le_GP M x.2⟩).mp x.2)

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_pi_apply (x : ↥M.NXG) :
    ((burnsideJ27_pi M e x : ↥A6Models.psl29) : Equiv.Perm (Fin 10)) =
      burnsideJ27_Phi M e ⟨x, burnsideJ27_NXG_le_GP M x.2⟩ := rfl

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_pi_surj : Function.Surjective (burnsideJ27_pi M e) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨g, hg⟩ := burnsideJ27_Phi_surj M e (psl29_le_autA6 hσ)
  have hgN : (g : G) ∈ M.NXG := (burnsideJ27_mem_NXG_iff M e g).mpr (hg ▸ hσ)
  exact ⟨⟨g, hgN⟩, Subtype.ext hg⟩

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_pi_ker : (burnsideJ27_pi M e).ker = M.B.subgroupOf M.NXG := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : burnsideJ27_Phi M e ⟨x, burnsideJ27_NXG_le_GP M x.2⟩ = 1 :=
      congrArg Subtype.val h
    exact (burnsideJ27_Phi_eq_one_iff M e _).mp h1
  · intro h
    apply Subtype.ext
    exact (burnsideJ27_Phi_eq_one_iff M e ⟨x, burnsideJ27_NXG_le_GP M x.2⟩).mpr h

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
include e in
theorem burnsideJ27_card_pi_ker : Nat.card (burnsideJ27_pi M e).ker = 3 := by
  rw [burnsideJ27_pi_ker, Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (burnsideJ27_B_le_NXG M)).toEquiv]
  exact M.card_B

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_psl_center {w : ↥A6Models.psl29} (hw : ∀ v : ↥A6Models.psl29, w * v = v * w) :
    w = 1 := by
  obtain ⟨-, ψ, -, -⟩ := Unc25K1.A6Model.exists_pslEquiv
  have hz : ψ w ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨v, rfl⟩ := ψ.surjective a
    rw [← map_mul, ← map_mul, hw v]
  rw [alternatingGroup.center_eq_bot (α := Fin 6) (by simp), Subgroup.mem_bot,
    MulEquiv.map_eq_one_iff] at hz
  exact hz

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_psl_simple : IsSimpleGroup ↥A6Models.psl29 := by
  obtain ⟨-, ψ, -, -⟩ := Unc25K1.A6Model.exists_pslEquiv
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : Nontrivial ↥A6Models.psl29 := ψ.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective ψ.symm.toMonoidHom ψ.symm.surjective

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_psl_perfect : Group.IsPerfect ↥A6Models.psl29 := by
  obtain ⟨-, ψ, -, -⟩ := Unc25K1.A6Model.exists_pslEquiv
  haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  exact Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_center_NXG : Subgroup.center ↥M.NXG = (burnsideJ27_pi M e).ker := by
  ext z
  rw [Subgroup.mem_center_iff, MonoidHom.mem_ker]
  constructor
  · intro hz
    apply burnsideJ27_psl_center
    intro v
    obtain ⟨n, rfl⟩ := burnsideJ27_pi_surj M e v
    rw [← map_mul, ← map_mul, hz n]
  · intro hz g
    have hzB : (z : G) ∈ M.B := by
      have : z ∈ (burnsideJ27_pi M e).ker := hz
      rw [burnsideJ27_pi_ker, Subgroup.mem_subgroupOf] at this
      exact this
    have := (Subgroup.mem_centralizer_iff.mp (burnsideJ27_NXG_le_GB M g.2)) z hzB
    exact Subtype.ext this.symm

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
include e in
theorem burnsideJ27_card_center_NXG : Nat.card (Subgroup.center ↥M.NXG) = 3 := by
  rw [burnsideJ27_center_NXG]
  exact burnsideJ27_card_pi_ker M e

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_NXG_eq_commutator_mul (x : ↥M.NXG) :
    ∃ d ∈ commutator ↥M.NXG, ∃ b ∈ (burnsideJ27_pi M e).ker, x = d * b := by
  haveI := burnsideJ27_psl_perfect
  have h1 : (commutator ↥M.NXG).map (burnsideJ27_pi M e) = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ (burnsideJ27_pi_surj M e)]
    exact Group.IsPerfect.commutator_eq_top (G := ↥A6Models.psl29)
  have hx : burnsideJ27_pi M e x ∈ (commutator ↥M.NXG).map (burnsideJ27_pi M e) := by
    rw [h1]
    exact Subgroup.mem_top _
  obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp hx
  refine ⟨d, hd, d⁻¹ * x, ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]

end N

section N18

variable {G : Type} [Group G] [Finite G]
  (M : CFSG.Quasithin.RuType.RuDataM G) (e : M.NP ≃* CFSG.QuasithinUnique.A6Models.psl29)

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
open scoped commutatorElement in
theorem burnsideJ27_NXG_perfect : commutator ↥M.NXG = ⊤ := by
  classical
  obtain ⟨e⟩ := M.nonempty_NP_psl29
  have hnc := burnsideJ27_R0_not_comm M e
  push Not at hnc
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  obtain ⟨gx, rfl, hgx⟩ := (burnsideJ27_mem_R0 M e).mp hx
  obtain ⟨gy, rfl, hgy⟩ := (burnsideJ27_mem_R0 M e).mp hy
  have hxN : (gx : G) ∈ M.NXG :=
    (burnsideJ27_mem_NXG_iff M e gx).mpr (burnsideJ27_E0_le_psl hgx)
  have hyN : (gy : G) ∈ M.NXG :=
    (burnsideJ27_mem_NXG_iff M e gy).mpr (burnsideJ27_E0_le_psl hgy)
  set x' : ↥M.NXG := ⟨gx, hxN⟩ with hx'
  set y' : ↥M.NXG := ⟨gy, hyN⟩ with hy'
  set c : ↥M.NXG := ⁅x', y'⁆ with hc
  have hcmem : c ∈ commutator ↥M.NXG := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hck : c ∈ (burnsideJ27_pi M e).ker := by
    rw [MonoidHom.mem_ker, hc, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact burnsideJ27_E0_comm hgx hgy
  have hc1 : c ≠ 1 := by
    intro h
    apply hxy
    have h1 : x' * y' = y' * x' := commutatorElement_eq_one_iff_mul_comm.mp h
    exact congrArg Subtype.val h1
  have hcB : (c : G) ∈ M.B := by
    rw [burnsideJ27_pi_ker, Subgroup.mem_subgroupOf] at hck
    exact hck
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hc3 : c ^ 3 = 1 := Subtype.ext (M.pow_three_of_mem_B hcB)
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hker : (burnsideJ27_pi M e).ker = Subgroup.zpowers c :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hck)
      (by rw [Nat.card_zpowers, hord, burnsideJ27_card_pi_ker M e])).symm
  rw [eq_top_iff]
  intro z _
  obtain ⟨d, hd, b, hb, rfl⟩ := burnsideJ27_NXG_eq_commutator_mul M e z
  refine mul_mem hd ?_
  rw [hker] at hb
  exact (Subgroup.zpowers_le.mpr hcmem) hb

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_isHatCover_NXG : IsHatCover ↥M.NXG (alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := M.nonempty_NP_psl29
  have hperf : Group.IsPerfect ↥M.NXG := Group.isPerfect_def.mpr (burnsideJ27_NXG_perfect M)
  let eQ : ↥M.NXG ⧸ Subgroup.center ↥M.NXG ≃* ↥A6Models.psl29 :=
    (QuotientGroup.quotientMulEquivOfEq (burnsideJ27_center_NXG M e)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (burnsideJ27_pi M e) (burnsideJ27_pi_surj M e))
  obtain ⟨-, ψ, -, -⟩ := Unc25K1.A6Model.exists_pslEquiv
  haveI := burnsideJ27_psl_simple
  haveI : Nontrivial (↥M.NXG ⧸ Subgroup.center ↥M.NXG) := eQ.toEquiv.nontrivial
  refine ⟨⟨hperf, ?_, ?_⟩, burnsideJ27_card_center_NXG M e, ⟨eQ.trans ψ⟩⟩
  · exact IsSimpleGroup.isSimpleGroup_of_surjective eQ.symm.toMonoidHom eQ.symm.surjective
  · by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative (↥M.NXG ⧸ Subgroup.center ↥M.NXG)
      ⟨⟨fun a b => hcon a b⟩⟩

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
open CFSG.ASVolI.ChIJK in
open scoped commutatorElement in
theorem burnsideJ27_LBRu_eq : LBRu M.B = M.NXG := by
  have hP : ⁅M.NX, M.NX⁆ = M.NX := by
    apply Subgroup.map_injective (M.GB.subtype_injective)
    rw [Subgroup.map_commutator]
    exact (Subgroup.isPerfect_iff).mp (Group.isPerfect_def.mpr (burnsideJ27_NXG_perfect M))
  have hd : commutator ↥M.GB ≤ M.NX := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g1 _ g2 _
    show M.Vtr ⁅g1, g2⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  unfold LBRu
  rw [burnsideJ27_perfectResidual_eq M.NX hP hd]

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_part1 (g : G) :
    IsHatCover ↥(LBRu (CFSG.conjugate M.B g)) (alternatingGroup (Fin 6)) := by
  rw [burnsideJ27_LBRu_conj]
  exact burnsideJ27_isHatCover_of_equiv
    (burnsideJ27_conjEquiv (X₁ := LBRu M.B) (X₂ := CFSG.conjugate (LBRu M.B) g) g⁻¹
      (fun y => by rw [burnsideJ27_mem_conjugate, inv_inv]))
    (by
      have h := burnsideJ27_isHatCover_NXG M
      rw [← burnsideJ27_LBRu_eq M] at h
      exact h)

end N18

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_norm_inv {X : Type*} [Group X] (S : Subgroup X) [Finite S] {k : X}
    (h : ∀ x ∈ S, k * x * k⁻¹ ∈ S) : ∀ x ∈ S, k⁻¹ * x * k ∈ S := by
  have hle : S.map (MulAut.conj k).toMonoidHom ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : S.map (MulAut.conj k).toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj k).injective])
  intro x hx
  rw [← heq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa [MulAut.conj_apply, mul_assoc] using hy

section Class

variable {G : Type} [Group G] [Finite G]
  (M : CFSG.Quasithin.RuType.RuDataM G) (e : M.NP ≃* CFSG.QuasithinUnique.A6Models.psl29)

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_noncentral {u : G} (hu : u ∈ burnsideJ27_R0 M e) (huB : u ∉ M.B) :
    ∃ y ∈ burnsideJ27_R0 M e, y * u ≠ u * y := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set Rg : Subgroup G := burnsideJ27_R0 M e with hRg
  have hcard : Nat.card Rg = 3 ^ 3 := by
    rw [hRg, burnsideJ27_card_R0 M e]
    norm_num
  have hp : IsPGroup 3 Rg := IsPGroup.of_card hcard
  set Z : Subgroup Rg := Subgroup.center Rg with hZ
  set BR : Subgroup Rg := M.B.subgroupOf Rg with hBR
  have hBRle : BR ≤ Z := by
    intro b hb
    rw [hZ, Subgroup.mem_center_iff]
    intro g
    have hbB : (b : G) ∈ M.B := Subgroup.mem_subgroupOf.mp hb
    have := (Subgroup.mem_centralizer_iff.mp (burnsideJ27_R0_le_GB M e g.2)) b hbB
    exact Subtype.ext this.symm
  have hBRcard : Nat.card BR = 3 := by
    rw [hBR, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (burnsideJ27_B_le_R0 M e)).toEquiv]
    exact M.card_B
  have huZ : (⟨u, hu⟩ : Rg) ∈ Z := by
    rw [hZ, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcon g g.2)
  have huBR : (⟨u, hu⟩ : Rg) ∉ BR := fun h => huB (Subgroup.mem_subgroupOf.mp h)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp (hp.to_subgroup Z)
  have h3Z : 3 ∣ Nat.card Z := hBRcard ▸ Subgroup.card_dvd_of_le hBRle
  have hne3 : Nat.card Z ≠ 3 := by
    intro h
    have : BR = Z := Subgroup.eq_of_le_of_card_ge hBRle (by rw [h, hBRcard])
    exact huBR (this ▸ huZ)
  have hZdvd : Nat.card Z ∣ 27 := by
    have := Subgroup.card_subgroup_dvd_card Z
    rwa [hcard] at this
  have hj3 : j ≤ 3 := by
    have h' : 3 ^ j ∣ 3 ^ 3 := by rw [← hj]; exact hZdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h'
  have hj2 : 2 ≤ j := by
    by_contra hlt
    have hlt' : j = 0 ∨ j = 1 := by omega
    rcases hlt' with rfl | rfl
    · rw [pow_zero] at hj
      rw [hj] at h3Z
      omega
    · rw [pow_one] at hj
      exact hne3 hj
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  rw [hcard, hj] at hq
  have hqdvd : Nat.card (Rg ⧸ Z) ∣ 3 := by
    have hj' : j = 2 ∨ j = 3 := by omega
    rcases hj' with rfl | rfl
    · norm_num at hq
      have : Nat.card (Rg ⧸ Z) = 3 := by omega
      rw [this]
    · norm_num at hq
      have : Nat.card (Rg ⧸ Z) = 1 := by omega
      rw [this]
      exact one_dvd _
  haveI : IsCyclic (Rg ⧸ Z) := isCyclic_of_card_dvd_prime hqdvd
  haveI := isMulCommutative_of_isCyclic_quotient_center_self Rg
  apply burnsideJ27_R0_not_comm M e
  intro x hx y hy
  have := (IsMulCommutative.is_comm (M := Rg)).comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_exists_Rf :
    ∃ (a : Equiv.Perm (Fin 10)) (x : M.GP), a ∈ burnsideJ27_E0 ∧ a ≠ 1 ∧
      burnsideJ27_Phi M e x = a ∧ IsConj (M.bel : G) (x : G) := by
  obtain ⟨e1, he1, he11, hf1⟩ := burnsideJ27_f0_fix
  have hf0aut : burnsideJ27_f0 ∈ A6Models.autA6 := s6_le_autA6 burnsideJ27_f0_mem_s6
  obtain ⟨f, x, hfΦ, hxΦ, hff, hfB, hfz, hfx⟩ := burnsideJ27_exists_xf M e hf0aut
    burnsideJ27_f0_sq burnsideJ27_f0_not_mem_m10 burnsideJ27_f0_mem_s6 he1 hf1
  have hxR : (x : G) ∈ burnsideJ27_R0 M e :=
    (burnsideJ27_mem_R0 M e).mpr ⟨x, rfl, hxΦ ▸ he1⟩
  have hx1' : (x : G) ≠ 1 := fun h => he11 (by
    rw [← hxΦ, show x = 1 from Subtype.ext h, map_one])
  obtain ⟨w, hw⟩ := burnsideJ27_conj_to_B M hfz hfx (burnsideJ27_R0_exp3 M e _ hxR) hx1'
  refine ⟨e1, x, he1, he11, hxΦ, ?_⟩
  have hmem : (x : G) ∈ M.B.map (MulAut.conj w⁻¹).toMonoidHom := hw ▸ Subgroup.mem_zpowers _
  rw [burnsideJ27_mem_map_conj, inv_inv] at hmem
  obtain ⟨n, -, hn⟩ := M.exists_inv_GP
  have hbb : IsConj (M.bel : G) (M.bel : G)⁻¹ := isConj_iff.mpr ⟨n, hn⟩
  have hxw : (x : G) = w⁻¹ * (w * x * w⁻¹) * w := by group
  rcases M.mem_B_iff.mp hmem with h | h | h
  · exact absurd (by rw [hxw, h]; group) hx1'
  · have : IsConj (M.bel : G) (x : G) := isConj_iff.mpr ⟨w⁻¹, by rw [hxw, h]; group⟩
    exact this
  · have : IsConj (M.bel : G)⁻¹ (x : G) := isConj_iff.mpr ⟨w⁻¹, by rw [hxw, h]; group⟩
    exact hbb.trans this

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_R0_class {r : G} (hr : r ∈ burnsideJ27_R0 M e) (hr1 : r ≠ 1) :
    IsConj (M.bel : G) r := by
  classical
  obtain ⟨n, -, hn⟩ := M.exists_inv_GP
  have hbb : IsConj (M.bel : G) (M.bel : G)⁻¹ := isConj_iff.mpr ⟨n, hn⟩
  by_cases hrB : r ∈ M.B
  · rcases M.mem_B_iff.mp hrB with h | h | h
    · exact absurd h hr1
    · rw [h]
    · rw [h]
      exact hbb
  obtain ⟨af, xf, haf, haf1, hxfΦ, hxfconj⟩ := burnsideJ27_exists_Rf M e
  obtain ⟨g, rfl, hg⟩ := (burnsideJ27_mem_R0 M e).mp hr
  have hga1 : burnsideJ27_Phi M e g ≠ 1 := fun h => hrB ((burnsideJ27_Phi_eq_one_iff M e g).mp h)
  obtain ⟨kf, hkf, hkfn, hkfe⟩ := burnsideJ27_trans af haf haf1
  obtain ⟨kr, hkr, hkrn, hkre⟩ := burnsideJ27_trans _ hg hga1
  set k : Equiv.Perm (Fin 10) := kr * kf⁻¹ with hk
  have hkaut : k ∈ A6Models.autA6 :=
    A6Models.autA6.mul_mem hkr (A6Models.autA6.inv_mem hkf)
  have hkaf : k * af * k⁻¹ = burnsideJ27_Phi M e g := by
    calc k * af * k⁻¹ = kr * kf⁻¹ * (kf * burnsideJ27_e1 * kf⁻¹) * (kr * kf⁻¹)⁻¹ := by
          rw [hkfe]
      _ = kr * burnsideJ27_e1 * kr⁻¹ := by group
      _ = _ := hkre
  have hkn : ∀ x ∈ burnsideJ27_E0, k * x * k⁻¹ ∈ burnsideJ27_E0 := by
    intro x hx
    have h1 := burnsideJ27_norm_inv burnsideJ27_E0 hkfn x hx
    have h2 := hkrn _ h1
    have : k * x * k⁻¹ = kr * (kf⁻¹ * x * kf) * kr⁻¹ := by rw [hk]; group
    rw [this]
    exact h2
  obtain ⟨κ, hκ⟩ := burnsideJ27_Phi_surj M e hkaut
  set uY : M.GP := κ * xf * κ⁻¹ with huY
  have huΦ : burnsideJ27_Phi M e uY = burnsideJ27_Phi M e g := by
    rw [huY, map_mul, map_mul, map_inv, hκ, hxfΦ, hkaf]
  have huR : (uY : G) ∈ burnsideJ27_R0 M e :=
    (burnsideJ27_mem_R0 M e).mpr ⟨uY, rfl, huΦ ▸ hg⟩
  have huB : (uY : G) ∉ M.B := fun h => hga1 (huΦ ▸ (burnsideJ27_Phi_eq_one_iff M e uY).mpr h)
  have hb'Φ : burnsideJ27_Phi M e (uY⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, huΦ, inv_mul_cancel]
  have hb'B : ((uY⁻¹ * g : M.GP) : G) ∈ M.B := (burnsideJ27_Phi_eq_one_iff M e _).mp hb'Φ
  set b' : G := ((uY⁻¹ * g : M.GP) : G) with hb'
  have hrub : (g : G) = (uY : G) * b' := by
    rw [hb']
    simp
  obtain ⟨y0, hy0, hy0u⟩ := burnsideJ27_noncentral M e huR huB
  set u : G := (uY : G) with hu
  set c : G := y0 * u * y0⁻¹ * u⁻¹ with hc
  have hy0GB : y0 ∈ M.GB := burnsideJ27_R0_le_GB M e hy0
  have huGB : u ∈ M.GB := burnsideJ27_R0_le_GB M e huR
  have hcB : c ∈ M.B := by
    obtain ⟨gy, hgy, hgyΦ⟩ := (burnsideJ27_mem_R0 M e).mp hy0
    have hΦc : burnsideJ27_Phi M e (gy * uY * gy⁻¹ * uY⁻¹) = 1 := by
      have := burnsideJ27_E0_comm hgyΦ (huΦ ▸ hg)
      simp only [map_mul, map_inv]
      rw [this]
      group
    have := (burnsideJ27_Phi_eq_one_iff M e _).mp hΦc
    rw [hc, ← hgy]
    simpa using this
  have hc1 : c ≠ 1 := by
    intro h
    apply hy0u
    have : y0 * u * y0⁻¹ = u := by
      have h1 : y0 * u * y0⁻¹ * u⁻¹ = 1 := h
      calc y0 * u * y0⁻¹ = (y0 * u * y0⁻¹ * u⁻¹) * u := by group
        _ = u := by rw [h1, one_mul]
    calc y0 * u = (y0 * u * y0⁻¹) * y0 := by group
      _ = u * y0 := by rw [this]
  have hcu : c * u = u * c := (Subgroup.mem_centralizer_iff.mp huGB) c hcB
  have hcy : c * y0 = y0 * c := (Subgroup.mem_centralizer_iff.mp hy0GB) c hcB
  have hy0u' : y0 * u * y0⁻¹ = c * u := by rw [hc]; group
  have hB3 : b' = 1 ∨ b' = c ∨ b' = c⁻¹ := by
    rcases M.mem_B_iff.mp hb'B with h1 | h1 | h1 <;> rcases M.mem_B_iff.mp hcB with h2 | h2 | h2 <;>
      first
        | exact Or.inl h1
        | exact absurd h2 hc1
        | (right; left; rw [h1, h2]; done)
        | (right; right; rw [h1, h2, inv_inv]; done)
        | (right; right; rw [h1, h2]; done)
  have hcomm : Commute c u := hcu
  have hcomm' : Commute c y0 := hcy
  have h2 : y0⁻¹ * u * y0 = c⁻¹ * u := by
    have e1 : y0 * u = c * u * y0 := by
      calc y0 * u = (y0 * u * y0⁻¹) * y0 := by group
        _ = c * u * y0 := by rw [hy0u']
    have e2 : y0⁻¹ * (c * u * y0) = u := by rw [← e1]; group
    have e3 : c * (y0⁻¹ * u * y0) = u := by
      calc c * (y0⁻¹ * u * y0) = (c * y0⁻¹) * u * y0 := by group
        _ = (y0⁻¹ * c) * u * y0 := by rw [hcomm'.inv_right.eq]
        _ = y0⁻¹ * (c * u * y0) := by group
        _ = u := e2
    calc y0⁻¹ * u * y0 = c⁻¹ * (c * (y0⁻¹ * u * y0)) := by group
      _ = c⁻¹ * u := by rw [e3]
  have hur : IsConj u (g : G) := by
    rw [hrub]
    rcases hB3 with h | h | h
    · rw [h, mul_one]
    · refine isConj_iff.mpr ⟨y0, ?_⟩
      rw [h, hy0u', hcu]
    · refine isConj_iff.mpr ⟨y0⁻¹, ?_⟩
      rw [h, inv_inv, h2, hcomm.inv_left.eq]
  have hxu : IsConj (xf : G) u := isConj_iff.mpr ⟨κ, by rw [hu, huY]; simp⟩
  exact hxfconj.trans (hxu.trans hur)

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_order3_conj_R0 {x : G} (hx : orderOf x = 3) :
    ∃ c : G, c * x * c⁻¹ ∈ burnsideJ27_R0 M e := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Nat.card (burnsideJ27_R0 M e) = 3 ^ 3 := by
    rw [burnsideJ27_card_R0 M e]
    norm_num
  have hp : IsPGroup 3 (burnsideJ27_R0 M e) := IsPGroup.of_card hcard
  have hidx : ¬ 3 ∣ (burnsideJ27_R0 M e).index := by
    have h := Subgroup.card_mul_index (burnsideJ27_R0 M e)
    rw [burnsideJ27_card_R0 M e, M.card_eq] at h
    norm_num at h
    omega
  let P : Sylow 3 G := hp.toSylow hidx
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hx]
    exact ⟨1, by norm_num⟩
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨c, ?_⟩
  have : c * x * c⁻¹ ∈ (P : Subgroup G) := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨x, hQ (Subgroup.mem_zpowers x), by simp [MulAut.conj_apply]⟩
  exact this

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
include M in
theorem burnsideJ27_part11 :
    ∀ x y : G, orderOf x = 3 → orderOf y = 3 → ∃ g : G, y = g⁻¹ * x * g := by
  obtain ⟨e⟩ := M.nonempty_NP_psl29
  intro x y hx hy
  obtain ⟨c1, hc1⟩ := burnsideJ27_order3_conj_R0 M e hx
  obtain ⟨c2, hc2⟩ := burnsideJ27_order3_conj_R0 M e hy
  have hx1 : c1 * x * c1⁻¹ ≠ 1 := by
    intro h
    have : x = 1 := by
      calc x = c1⁻¹ * (c1 * x * c1⁻¹) * c1 := by group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hy1 : c2 * y * c2⁻¹ ≠ 1 := by
    intro h
    have : y = 1 := by
      calc y = c2⁻¹ * (c2 * y * c2⁻¹) * c2 := by group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have h1 := burnsideJ27_R0_class M e hc1 hx1
  have h2 := burnsideJ27_R0_class M e hc2 hy1
  obtain ⟨d, hd⟩ := isConj_iff.mp (h1.symm.trans h2)
  refine ⟨c1⁻¹ * d⁻¹ * c2, ?_⟩
  have : y = c2⁻¹ * (d * (c1 * x * c1⁻¹) * d⁻¹) * c2 := by rw [hd]; group
  rw [this]
  group

end Class

theorem burnsideJ27_center_map {X X' : Type*} [Group X] [Group X'] (κ : X ≃* X') :
    (Subgroup.center X).map κ.toMonoidHom = Subgroup.center X' := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro hx y
    have := hx (κ.symm y)
    have h2 := congrArg κ this
    simpa using h2
  · intro hx y
    have := hx (κ y)
    have h2 := congrArg κ.symm this
    simpa using h2

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_induces_transp_conj {G : Type} [Group G] {X : Subgroup G} {g i : G}
    (h : InducesTranspositionOn i (CFSG.conjugate X g)) :
    InducesTranspositionOn (g * i * g⁻¹) X := by
  obtain ⟨hnorm, e', τ, hτ, hrel⟩ := h
  let κ : ↥X ≃* ↥(CFSG.conjugate X g) :=
    burnsideJ27_conjEquiv (X₁ := X) (X₂ := CFSG.conjugate X g) g⁻¹
      (fun y => by rw [burnsideJ27_mem_conjugate, inv_inv])
  let eQ : ↥X ⧸ Subgroup.center ↥X ≃*
      ↥(CFSG.conjugate X g) ⧸ Subgroup.center ↥(CFSG.conjugate X g) :=
    QuotientGroup.congr _ _ κ (burnsideJ27_center_map κ)
  refine ⟨?_, eQ.trans e', τ, hτ, ?_⟩
  · rw [burnsideJ27_normalizer_conjugate, burnsideJ27_mem_conjugate] at hnorm
    exact hnorm
  · intro n n' hnn
    have hκ : ∀ x : ↥X, ((κ x : ↥(CFSG.conjugate X g)) : G) = g⁻¹ * x * g := fun x => by
      show g⁻¹ * (x : G) * g⁻¹⁻¹ = g⁻¹ * x * g
      rw [inv_inv]
    have hrel' := hrel (κ n) (κ n') (by
      rw [hκ, hκ, hnn]
      group)
    show e' (eQ (QuotientGroup.mk n')) = τ * e' (eQ (QuotientGroup.mk n)) * τ⁻¹
    have h1 : ∀ x : ↥X, eQ (QuotientGroup.mk x) = QuotientGroup.mk (κ x) := fun x =>
      QuotientGroup.congr_mk _ _ κ _ x
    rw [h1, h1]
    exact hrel'

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_induces_diag_conj {G : Type} [Group G] {X : Subgroup G} {g i : G}
    (h : InducesDiagonalOn i (CFSG.conjugate X g)) :
    InducesDiagonalOn (g * i * g⁻¹) X := by
  obtain ⟨hnorm, e', M, hM, hrel⟩ := h
  let κ : ↥X ≃* ↥(CFSG.conjugate X g) :=
    burnsideJ27_conjEquiv (X₁ := X) (X₂ := CFSG.conjugate X g) g⁻¹
      (fun y => by rw [burnsideJ27_mem_conjugate, inv_inv])
  let eQ : ↥X ⧸ Subgroup.center ↥X ≃*
      ↥(CFSG.conjugate X g) ⧸ Subgroup.center ↥(CFSG.conjugate X g) :=
    QuotientGroup.congr _ _ κ (burnsideJ27_center_map κ)
  refine ⟨?_, eQ.trans e', M, hM, ?_⟩
  · rw [burnsideJ27_normalizer_conjugate, burnsideJ27_mem_conjugate] at hnorm
    exact hnorm
  · intro n n' hnn
    have hκ : ∀ x : ↥X, ((κ x : ↥(CFSG.conjugate X g)) : G) = g⁻¹ * x * g := fun x => by
      show g⁻¹ * (x : G) * g⁻¹⁻¹ = g⁻¹ * x * g
      rw [inv_inv]
    have hrel' := hrel (κ n) (κ n') (by
      rw [hκ, hκ, hnn]
      group)
    show e' (eQ (QuotientGroup.mk n')) =
      conjPSL (GaloisField 3 2) M (e' (eQ (QuotientGroup.mk n)))
    have h1 : ∀ x : ↥X, eQ (QuotientGroup.mk x) = QuotientGroup.mk (κ x) := fun x =>
      QuotientGroup.congr_mk _ _ κ _ x
    rw [h1, h1]
    exact hrel'

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_swap_five : ∀ a : Equiv.Perm (Fin 6), a ^ 5 = 1 → a ≠ 1 →
    ∀ x y : Fin 6, x ≠ y → Equiv.swap x y * a ≠ a * Equiv.swap x y := by
  intro a ha5 ha1 x y hxy hc
  have hs : ∀ z, Equiv.swap x y (a z) = a (Equiv.swap x y z) := fun z => by
    have := congrArg (fun f : Equiv.Perm (Fin 6) => f z) hc
    simpa only [Equiv.Perm.mul_apply] using this
  have hx : a x = x ∧ a y = y := by
    have h0 := hs x
    rw [Equiv.swap_apply_left x y] at h0
    by_cases h : a x = x
    · rw [h, Equiv.swap_apply_left] at h0
      exact ⟨h, h0.symm⟩
    by_cases h' : a x = y
    · exfalso
      rw [h', Equiv.swap_apply_right] at h0
      have h2 : (a * a) x = x := by rw [Equiv.Perm.mul_apply, h', ← h0]
      have h6 : (a * a) ^ 3 = a := by
        rw [← pow_two, ← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_succ, ha5, one_mul]
      have h3 := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h2 3
      rw [h6, h'] at h3
      exact hxy h3.symm
    · rw [Equiv.swap_apply_of_ne_of_ne h h'] at h0
      exact absurd (a.injective h0) hxy
  obtain ⟨hax, hay⟩ := hx
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) (σ := a)
    (by rw [pow_one]; exact ha5)
  have h2 : 2 ≤ a.supportᶜ.card := by
    rw [← Finset.card_pair hxy]
    refine Finset.card_le_card fun z hz => ?_
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [Finset.mem_compl, Equiv.Perm.notMem_support]
    rcases hz with rfl | rfl
    · exact hax
    · exact hay
  have hcompl := Finset.card_compl a.support
  have hle := Finset.card_le_univ a.support
  rw [Fintype.card_fin] at hcompl hle hmod
  unfold Nat.ModEq at hmod
  have hsupp : a.support.card = 0 := by omega
  exact ha1 (Equiv.Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp hsupp))

section Pic

variable {G : Type} [Group G] [Finite G]
  (M : CFSG.Quasithin.RuType.RuDataM G) (e : M.NP ≃* CFSG.QuasithinUnique.A6Models.psl29)

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
include e in
theorem burnsideJ27_norm_B {w : G} (hw : w ∈ Subgroup.normalizer (M.NXG : Set G)) {b : G}
    (hb : b ∈ M.B) : w * b * w⁻¹ ∈ M.B := by
  have hbN : b ∈ M.NXG := burnsideJ27_B_le_NXG M hb
  have hbc : (⟨b, hbN⟩ : ↥M.NXG) ∈ Subgroup.center ↥M.NXG := by
    rw [burnsideJ27_center_NXG M e, burnsideJ27_pi_ker, Subgroup.mem_subgroupOf]
    exact hb
  have h1 : w * b * w⁻¹ ∈ M.NXG := (Subgroup.mem_normalizer_iff.mp hw b).mp hbN
  have h2 : (⟨w * b * w⁻¹, h1⟩ : ↥M.NXG) ∈ Subgroup.center ↥M.NXG := by
    rw [Subgroup.mem_center_iff]
    intro n
    have hn' : w⁻¹ * (n : G) * w ∈ M.NXG := by
      have := (Subgroup.mem_normalizer_iff.mp hw (w⁻¹ * (n : G) * w)).mp
      have e1 : w * (w⁻¹ * (n : G) * w) * w⁻¹ = n := by group
      by_contra hcon
      exact hcon ((Subgroup.mem_normalizer_iff.mp hw _).mpr (by rw [e1]; exact n.2))
    have := (Subgroup.mem_center_iff.mp hbc) ⟨w⁻¹ * (n : G) * w, hn'⟩
    have h3 : w⁻¹ * (n : G) * w * b = b * (w⁻¹ * (n : G) * w) := congrArg Subtype.val this
    apply Subtype.ext
    show (n : G) * (w * b * w⁻¹) = w * b * w⁻¹ * n
    calc (n : G) * (w * b * w⁻¹) = w * (w⁻¹ * (n : G) * w * b) * w⁻¹ := by group
      _ = w * (b * (w⁻¹ * (n : G) * w)) * w⁻¹ := by rw [h3]
      _ = w * b * w⁻¹ * n := by group
  rw [burnsideJ27_center_NXG M e, burnsideJ27_pi_ker, Subgroup.mem_subgroupOf] at h2
  exact h2

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
include e in
theorem burnsideJ27_normN_le_GP : Subgroup.normalizer (M.NXG : Set G) ≤ M.GP := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact burnsideJ27_norm_B M e hw hb
  · intro hb
    have := burnsideJ27_norm_B M e (inv_mem hw) hb
    simpa [mul_assoc] using this

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_conj_pi {i : G} (hi : i ∈ Subgroup.normalizer (M.NXG : Set G))
    (n n' : ↥M.NXG) (h : (n' : G) = i⁻¹ * n * i) :
    ((burnsideJ27_pi M e n' : ↥A6Models.psl29) : Equiv.Perm (Fin 10)) =
      (burnsideJ27_Phi M e ⟨i, burnsideJ27_normN_le_GP M e hi⟩)⁻¹ *
        ((burnsideJ27_pi M e n : ↥A6Models.psl29) : Equiv.Perm (Fin 10)) *
        burnsideJ27_Phi M e ⟨i, burnsideJ27_normN_le_GP M e hi⟩ := by
  rw [burnsideJ27_pi_apply, burnsideJ27_pi_apply]
  have : (⟨n', burnsideJ27_NXG_le_GP M n'.2⟩ : M.GP) =
      (⟨i, burnsideJ27_normN_le_GP M e hi⟩ : M.GP)⁻¹ *
        ⟨n, burnsideJ27_NXG_le_GP M n.2⟩ * ⟨i, burnsideJ27_normN_le_GP M e hi⟩ :=
    Subtype.ext h
  rw [this, map_mul, map_mul, map_inv]

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_N7b {i : G} (hi2 : i ^ 2 = 1) (hi1 : i ≠ 1)
    (h : InducesTranspositionOn i M.NXG) : IsConj M.z i := by
  classical
  obtain ⟨e⟩ := M.nonempty_NP_psl29
  obtain ⟨hnorm, e'', τ, hτ, hrel⟩ := h
  have hGP : i ∈ M.GP := burnsideJ27_normN_le_GP M e hnorm
  set y : M.GP := ⟨i, hGP⟩ with hy
  have hy2 : (y : G) * y = 1 := by
    rw [← pow_two]
    exact hi2
  by_cases hGB : i ∈ M.GB
  · obtain ⟨g, -, hg⟩ := M.lemma_J27_9 hGB hi2 hi1
    exact isConj_iff.mpr ⟨g, hg⟩
  by_cases hs6 : burnsideJ27_Phi M e y ∈ s6
  · exact (M.outer_inv_classes e y hGB hy2).1 hs6
  exfalso
  set ν : Equiv.Perm (Fin 10) := burnsideJ27_Phi M e y with hν
  have hνaut : ν ∈ A6Models.autA6 := burnsideJ27_Phi_mem M e y
  have hν2 : ν * ν = 1 := by
    rw [hν, ← map_mul]
    have : y * y = 1 := Subtype.ext hy2
    rw [this, map_one]
  have hνm : ν ∉ A6Models.m10 := fun hm => hGB ((burnsideJ27_Phi_m10 M e y).mp hm)
  obtain ⟨m, hm, hmν⟩ := AutA6.out_classes_d hνaut hν2 hνm hs6
  have hmaut : m ∈ A6Models.autA6 := burnsideJ27_m10_le_aut hm
  have hx5ps : x5 ∈ A6Models.psl29 :=
    mul_mem (mul_mem Out21.A6.tAdd_mem_psl29 Out21.A6.tSq_mem_psl29) Out21.A6.tInv_mem_psl29
  set p : Equiv.Perm (Fin 10) := m⁻¹ * x5 * m with hp
  have hpps : p ∈ A6Models.psl29 := by
    have := psl29_normal _ (A6Models.autA6.inv_mem hmaut) _ hx5ps
    simpa [hp] using this
  have hp5 : p ^ 5 = 1 := by
    have h5 := conj_pow (a := m⁻¹) (b := x5) (i := 5)
    simp only [inv_inv] at h5
    rw [hp, h5, x5_pow_five]
    group
  have hp1 : p ≠ 1 := by
    intro h1
    apply x5_ne_one
    calc x5 = m * (m⁻¹ * x5 * m) * m⁻¹ := by group
      _ = 1 := by rw [← hp, h1]; group
  have hν_eq : ν = m⁻¹ * AutA6.dInv * m := by rw [← hmν]; group
  have hdc : AutA6.dInv * x5 = x5 * AutA6.dInv := AutA6.dInv_comm
  have hνp : ν * p = p * ν := by
    calc ν * p = m⁻¹ * (AutA6.dInv * x5) * m := by rw [hν_eq, hp]; group
      _ = m⁻¹ * (x5 * AutA6.dInv) * m := by rw [hdc]
      _ = p * ν := by rw [hν_eq, hp]; group
  obtain ⟨n, hn⟩ := burnsideJ27_pi_surj M e ⟨p, hpps⟩
  have hn'mem : i⁻¹ * (n : G) * i ∈ M.NXG := by
    refine (Subgroup.mem_normalizer_iff.mp hnorm _).mpr ?_
    have e1 : i * (i⁻¹ * (n : G) * i) * i⁻¹ = n := by group
    rw [e1]
    exact n.2
  set n' : ↥M.NXG := ⟨i⁻¹ * (n : G) * i, hn'mem⟩ with hn'
  have hpi : ((burnsideJ27_pi M e n : ↥A6Models.psl29) : Equiv.Perm (Fin 10)) = p := by
    rw [hn]
  have hpi' : ((burnsideJ27_pi M e n' : ↥A6Models.psl29) : Equiv.Perm (Fin 10)) = p := by
    rw [burnsideJ27_conj_pi M e hnorm n n' rfl, hpi]
    calc ν⁻¹ * p * ν = ν⁻¹ * (p * ν) := by group
      _ = ν⁻¹ * (ν * p) := by rw [hνp]
      _ = p := by group
  have hmk : (QuotientGroup.mk n' : ↥M.NXG ⧸ Subgroup.center ↥M.NXG) = QuotientGroup.mk n := by
    rw [QuotientGroup.eq, burnsideJ27_center_NXG M e, MonoidHom.mem_ker, map_mul, map_inv]
    have : burnsideJ27_pi M e n' = burnsideJ27_pi M e n := Subtype.ext (hpi'.trans hpi.symm)
    rw [this, inv_mul_cancel]
  have hr := hrel n n' rfl
  rw [hmk] at hr
  set a : alternatingGroup (Fin 6) := e'' (QuotientGroup.mk n) with ha
  have hcomm : τ * (a : Equiv.Perm (Fin 6)) = (a : Equiv.Perm (Fin 6)) * τ := by
    calc τ * (a : Equiv.Perm (Fin 6)) = (τ * (a : Equiv.Perm (Fin 6)) * τ⁻¹) * τ := by group
      _ = (a : Equiv.Perm (Fin 6)) * τ := by rw [← hr]
  have hn5 : (QuotientGroup.mk n : ↥M.NXG ⧸ Subgroup.center ↥M.NXG) ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, burnsideJ27_center_NXG M e,
      MonoidHom.mem_ker, map_pow, hn]
    apply Subtype.ext
    exact hp5
  have ha5 : (a : Equiv.Perm (Fin 6)) ^ 5 = 1 := by
    have : a ^ 5 = 1 := by
      rw [ha, ← map_pow, hn5, map_one]
    have := congrArg Subtype.val this
    simpa using this
  have ha1 : (a : Equiv.Perm (Fin 6)) ≠ 1 := by
    intro h1
    have h2 : a = 1 := Subtype.ext h1
    rw [ha] at h2
    have h3 : (QuotientGroup.mk n : ↥M.NXG ⧸ Subgroup.center ↥M.NXG) = 1 := by
      apply e''.injective
      rw [h2, map_one]
    rw [QuotientGroup.eq_one_iff, burnsideJ27_center_NXG M e, MonoidHom.mem_ker] at h3
    apply hp1
    rw [← hpi, h3]
    rfl
  obtain ⟨x, x', hxx', rfl⟩ := hτ
  exact burnsideJ27_swap_five _ ha5 ha1 x x' hxx' hcomm

end Pic

open scoped MatrixGroups in
open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_toPGL_conjPSL (F : Type) [Field F] (M : GL (Fin 2) F) (s : PSL(2, F)) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (conjPSL F M s) =
      Matrix.ProjGenLinGroup.mk M * Matrix.ProjectiveSpecialLinearGroup.toPGL s *
        (Matrix.ProjGenLinGroup.mk M)⁻¹ := by
  induction s using QuotientGroup.induction_on with
  | H A =>
    show Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (conjSL F M A)) = _
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
      ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    simp only [Units.val_mul]
    rfl

open scoped MatrixGroups in
theorem burnsideJ27_isSquare_units {F : Type} [Field F] (u : Fˣ) (h : IsSquare (u : F)) :
    IsSquare u := by
  obtain ⟨a, ha⟩ := h
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by simpa using ha)
  exact ⟨Units.mk0 a ha0, Units.ext (by simpa using ha)⟩

section Diag

variable {G : Type} [Group G] [Finite G]
  (M : CFSG.Quasithin.RuType.RuDataM G)

open scoped MatrixGroups in
open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GorensteinWalter in
theorem burnsideJ27_N7c {i : G} (hi2 : i ^ 2 = 1) (hi1 : i ≠ 1)
    (h : InducesDiagonalOn i M.NXG) {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) : IsConj s i := by
  classical
  obtain ⟨e⟩ := M.nonempty_NP_psl29
  obtain ⟨hnorm, e', Mx, hMx, hrel⟩ := h
  have hGP : i ∈ M.GP := burnsideJ27_normN_le_GP M e hnorm
  set y : M.GP := ⟨i, hGP⟩ with hy
  have hnz : ¬ IsConj M.z i := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let _ : Fintype (GaloisField 3 2) := Fintype.ofFinite _
    have hc9 : Nat.card (GaloisField 3 2) = 9 := by
      rw [GaloisField.card 3 2 (by norm_num)]
      norm_num
    have hF : L2Field (GaloisField 3 2) := ⟨by rw [hc9]; decide, by rw [hc9]; norm_num⟩
    let eL : (↥M.NXG ⧸ Subgroup.center ↥M.NXG) ≃* L2 (GaloisField 3 2) :=
      e'.trans (L2.equivPSL (GaloisField 3 2)).symm
    have htoPSL : toPSL eL = e' := by
      ext x
      simp [toPSL, eL]
    let g0 : Matrix.ProjGenLinGroup (Fin 2) (GaloisField 3 2) := Matrix.ProjGenLinGroup.mk Mx
    let v : MulAut (↥M.NXG ⧸ Subgroup.center ↥M.NXG) := innDiagHom eL g0
    have hv_apply : ∀ x : ↥M.NXG ⧸ Subgroup.center ↥M.NXG,
        e' (v x) = conjPSL (GaloisField 3 2) Mx (e' x) := by
      intro x
      apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      rw [burnsideJ27_toPGL_conjPSL]
      have := toPGL_toPSL_innDiagHom eL g0 x
      rw [htoPSL] at this
      exact this
    have hi_mem : ∀ n : ↥M.NXG, i⁻¹ * (n : G) * i ∈ M.NXG := by
      intro n
      refine (Subgroup.mem_normalizer_iff.mp hnorm _).mpr ?_
      have e1 : i * (i⁻¹ * (n : G) * i) * i⁻¹ = n := by group
      rw [e1]
      exact n.2
    have hv_mk : ∀ n : ↥M.NXG, v (QuotientGroup.mk n) =
        QuotientGroup.mk (⟨i⁻¹ * (n : G) * i, hi_mem n⟩ : ↥M.NXG) := by
      intro n
      apply e'.injective
      rw [hv_apply]
      exact (hrel n ⟨i⁻¹ * (n : G) * i, hi_mem n⟩ rfl).symm
    have hii : i * i = 1 := by
      rw [← pow_two]
      exact hi2
    have hi' : i⁻¹ = i := inv_eq_of_mul_eq_one_right hii
    have hv2 : v ^ 2 = 1 := by
      ext x
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
      rw [pow_two, MulAut.mul_apply, hv_mk, hv_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      show i⁻¹ * (i⁻¹ * (n : G) * i) * i = n
      rw [hi']
      calc i * (i * (n : G) * i) * i = (i * i) * n * (i * i) := by group
        _ = n := by rw [hii]; group
    have hvD : v ∈ innDiagSub eL := ⟨g0, rfl⟩
    have hvI : v ∉ innAut (↥M.NXG ⧸ Subgroup.center ↥M.NXG) := by
      intro hmem
      have h1 := (innDiagHom_mem_innAut_iff eL g0).mp hmem
      have h2 := (pgl2_mk_mem_psl2_range_iff_det_isSquare Mx).mp h1
      exact hMx (burnsideJ27_isSquare_units _ h2)
    have hv1 : v ≠ 1 := fun h1 => hvI (h1 ▸ Subgroup.one_mem _)
    have hvo : orderOf v = 2 := orderOf_eq_prime hv2 hv1
    have hcard := CFSG.GH74.GLS.C3.Layer1.Bk.card_fixedSubgroup_of_outer_nine hF hc9 eL hvD hvI hvo
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨x5, hx5⟩ := exists_prime_orderOf_dvd_card' (G := ↥(fixedSubgroup
      (↥M.NXG ⧸ Subgroup.center ↥M.NXG) v)) 5 (by rw [hcard]; norm_num)
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (x5 : ↥M.NXG ⧸ Subgroup.center ↥M.NXG)
    have hfix : v (QuotientGroup.mk n) = QuotientGroup.mk n := by
      rw [hn]
      exact x5.2
    rw [hv_mk] at hfix
    have hpin : burnsideJ27_pi M e ⟨i⁻¹ * (n : G) * i, hi_mem n⟩ = burnsideJ27_pi M e n := by
      rw [QuotientGroup.eq, burnsideJ27_center_NXG M e, MonoidHom.mem_ker, map_mul, map_inv] at hfix
      exact (inv_mul_eq_one.mp hfix)
    have hconj := burnsideJ27_conj_pi M e hnorm n ⟨i⁻¹ * (n : G) * i, hi_mem n⟩ rfl
    rw [hpin] at hconj
    set q : Equiv.Perm (Fin 10) := ((burnsideJ27_pi M e n : ↥A6Models.psl29) : Equiv.Perm (Fin 10))
      with hq
    set ν : Equiv.Perm (Fin 10) := burnsideJ27_Phi M e y with hν
    have hνq : ν * q = q * ν := by
      calc ν * q = ν * (ν⁻¹ * q * ν) := by rw [← hconj]
        _ = q * ν := by group
    have hxo : orderOf (QuotientGroup.mk n : ↥M.NXG ⧸ Subgroup.center ↥M.NXG) = 5 := by
      rw [hn, Subgroup.orderOf_coe]
      exact hx5
    have hn5 : (QuotientGroup.mk n : ↥M.NXG ⧸ Subgroup.center ↥M.NXG) ^ 5 = 1 := by
      rw [← hxo]
      exact pow_orderOf_eq_one _
    have hq5 : q ^ 5 = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, burnsideJ27_center_NXG M e,
        MonoidHom.mem_ker, map_pow] at hn5
      have := congrArg Subtype.val hn5
      simpa [hq] using this
    have hq1 : q ≠ 1 := by
      intro h1
      have h2 : burnsideJ27_pi M e n = 1 := Subtype.ext h1
      have h3 : (QuotientGroup.mk n : ↥M.NXG ⧸ Subgroup.center ↥M.NXG) = 1 := by
        rw [QuotientGroup.eq_one_iff, burnsideJ27_center_NXG M e, MonoidHom.mem_ker]
        exact h2
      rw [h3, orderOf_one] at hxo
      exact absurd hxo (by norm_num)
    obtain ⟨y5, hy5GB, hy5o, hy5c, -⟩ := M.exists_comm_five_of_ρ e y
      (burnsideJ27_pi M e n).2 hq5 hq1 hνq
    exact M.not_isConj_z_of_comm_five (d := i) hy5GB hy5o hy5c
  exact ((M.lemma_J27_4 hs hs1).2 i hi2 hi1).resolve_left hnz

end Diag

section Part7

variable {G : Type} [Group G] [Finite G]
  (M : CFSG.Quasithin.RuType.RuDataM G)

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_part7 (g : G) {s' : G} (hs' : s' ∈ M.S0) (hs1' : s' ≠ 1) :
    (∀ i ∈ involutionsOf (LBRu (CFSG.conjugate M.B g)), i ∈ conjClass M.z) ∧
    (∀ i ∈ involutionsOf (⊤ : Subgroup G),
      InducesTranspositionOn i (LBRu (CFSG.conjugate M.B g)) → i ∈ conjClass M.z) ∧
    (∀ i ∈ involutionsOf (⊤ : Subgroup G),
      InducesDiagonalOn i (LBRu (CFSG.conjugate M.B g)) → i ∈ conjClass (g⁻¹ * s' * g)) := by
  have hL : LBRu (CFSG.conjugate M.B g) = CFSG.conjugate M.NXG g := by
    rw [burnsideJ27_LBRu_conj, burnsideJ27_LBRu_eq M]
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · exact burnsideJ27_part9 M g i ⟨burnsideJ27_LBRu_le _ hi.1, hi.2.1, hi.2.2⟩
  · rintro i ⟨-, hi2, hi1⟩ hind
    rw [hL] at hind
    have h0 := burnsideJ27_induces_transp_conj hind
    have hi02 : (g * i * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hi2]; group
    have hi01 : g * i * g⁻¹ ≠ 1 := fun h => hi1 (by
      have : i = g⁻¹ * (g * i * g⁻¹) * g := by group
      rw [this, h]; group)
    obtain ⟨c, hc⟩ := isConj_iff.mp (burnsideJ27_N7b M hi02 hi01 h0)
    refine ⟨c⁻¹ * g, ?_⟩
    calc i = g⁻¹ * (g * i * g⁻¹) * g := by group
      _ = g⁻¹ * (c * M.z * c⁻¹) * g := by rw [hc]
      _ = (c⁻¹ * g)⁻¹ * M.z * (c⁻¹ * g) := by group
  · rintro i ⟨-, hi2, hi1⟩ hind
    rw [hL] at hind
    have h0 := burnsideJ27_induces_diag_conj hind
    have hi02 : (g * i * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hi2]; group
    have hi01 : g * i * g⁻¹ ≠ 1 := fun h => hi1 (by
      have : i = g⁻¹ * (g * i * g⁻¹) * g := by group
      rw [this, h]; group)
    obtain ⟨c, hc⟩ := isConj_iff.mp (burnsideJ27_N7c M hi02 hi01 h0 hs' hs1')
    rw [burnsideJ27_mem_conjClass_conj_iff]
    refine isConj_iff.mpr ⟨g⁻¹ * c, ?_⟩
    calc g⁻¹ * c * s' * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * s' * c⁻¹) * g := by group
      _ = g⁻¹ * (g * i * g⁻¹) * g := by rw [hc]
      _ = i := by group

end Part7

section BurnsideJ27J28

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private def burnsideJ27_j28_matDec (n : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => if n.testBit (3 * i.val + j.val) then 1 else 0

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private def burnsideJ27_j28_matDet3 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : ZMod 2 :=
  A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0 +
    A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private def burnsideJ27_j28_matEnc (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : ℕ :=
  (A 0 0).val + 2 * (A 0 1).val + 4 * (A 0 2).val + 8 * (A 1 0).val + 16 * (A 1 1).val +
    32 * (A 1 2).val + 64 * (A 2 0).val + 128 * (A 2 1).val + 256 * (A 2 2).val

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ27_j28_mat_dec_enc : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2),
    burnsideJ27_j28_matDec (burnsideJ27_j28_matEnc A) = A := by
  decide +kernel

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ27_j28_stAct_of_mul {g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    {A B : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A = B * (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    stAct g A = B := by
  unfold stAct
  rw [h, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private def burnsideJ27_j28_nilpData : List (ℕ × ℕ × ℕ) :=
  [(2, 161, 4), (4, 161, 2), (6, 161, 6), (8, 98, 4), (27, 225, 4), (32, 98, 2), (36, 225, 2),
    (40, 98, 6), (63, 225, 6), (64, 84, 4), (72, 114, 4), (128, 84, 2), (130, 169, 4),
    (192, 84, 6), (219, 233, 4), (325, 169, 2), (365, 233, 2), (432, 114, 2), (438, 233, 6),
    (455, 169, 6), (504, 114, 6)]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private def burnsideJ27_j28_cubicData : List (ℕ × ℕ × ℕ) :=
  [(95, 86, 370), (102, 95, 370), (106, 84, 172), (115, 92, 172), (142, 92, 478), (157, 84, 370),
    (172, 87, 478), (187, 93, 172), (204, 94, 478), (226, 85, 172), (247, 84, 478),
    (253, 92, 370), (335, 93, 478), (355, 94, 172), (370, 87, 172), (382, 85, 478),
    (397, 95, 478), (412, 85, 370), (431, 94, 370), (442, 86, 172), (478, 87, 370),
    (485, 86, 478), (491, 95, 172), (500, 93, 370)]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ27_j28_nilp_cover : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2),
    A.trace = 0 → A * A = 0 → A ≠ 0 →
      ∃ t ∈ burnsideJ27_j28_nilpData, t.1 = burnsideJ27_j28_matEnc A := by
  decide +kernel

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ27_j28_nilp_check : ∀ t ∈ burnsideJ27_j28_nilpData,
    burnsideJ27_j28_matDet3 (burnsideJ27_j28_matDec t.2.1) = 1 ∧
      burnsideJ27_j28_matDec t.2.1 * burnsideJ27_j28_matDec t.1 =
        burnsideJ27_j28_matDec t.2.2 * burnsideJ27_j28_matDec t.2.1 ∧
      SL3.IsRow0 (burnsideJ27_j28_matDec t.2.2) := by
  decide +kernel

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ27_j28_cubic_cover : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2),
    A * A * A + A + 1 = 0 → ∃ t ∈ burnsideJ27_j28_cubicData, t.1 = burnsideJ27_j28_matEnc A := by
  decide +kernel

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ27_j28_cubic_check : ∀ t ∈ burnsideJ27_j28_cubicData,
    burnsideJ27_j28_matDet3 (burnsideJ27_j28_matDec t.2.1) = 1 ∧
      burnsideJ27_j28_matDec t.2.1 * burnsideJ27_j28_matDec t.1 =
        burnsideJ27_j28_matDec t.2.2 * burnsideJ27_j28_matDec t.2.1 ∧
      burnsideJ27_j28_matDec t.2.2 ∈ SL3.fixC0List := by
  decide +kernel

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_nilp_conj : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → A * A = 0 →
    A ≠ 0 → ∃ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), SL3.IsRow0 (stAct g A) := by
  intro A h1 h2 h3
  obtain ⟨t, ht, hA⟩ := burnsideJ27_j28_nilp_cover A h1 h2 h3
  obtain ⟨hdet, hconj, hrow⟩ := burnsideJ27_j28_nilp_check t ht
  rw [← burnsideJ27_j28_mat_dec_enc A, ← hA]
  have hg : (burnsideJ27_j28_matDec t.2.1).det = 1 := by rw [Matrix.det_fin_three]; exact hdet
  refine ⟨⟨_, hg⟩, ?_⟩
  rw [burnsideJ27_j28_stAct_of_mul (g := ⟨_, hg⟩) hconj]
  exact hrow

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_cubic_conj : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A * A * A + A + 1 = 0 →
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), stAct g A ∈ SL3.fixC0List := by
  intro A h1
  obtain ⟨t, ht, hA⟩ := burnsideJ27_j28_cubic_cover A h1
  obtain ⟨hdet, hconj, hfix⟩ := burnsideJ27_j28_cubic_check t ht
  rw [← burnsideJ27_j28_mat_dec_enc A, ← hA]
  have hg : (burnsideJ27_j28_matDec t.2.1).det = 1 := by rw [Matrix.det_fin_three]; exact hdet
  refine ⟨⟨_, hg⟩, ?_⟩
  rw [burnsideJ27_j28_stAct_of_mul (g := ⟨_, hg⟩) hconj]
  exact hfix

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_E :
    Fintype.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) //
      A.trace = 0 ∧ (A * A = 0 ∨ A * A * A + A + 1 = 0)} = 46 := by
  decide +kernel

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_stAct_eq_iff (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    stAct g A = A ↔
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A = A * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  have h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    rfl
  have h2 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    rfl
  unfold stAct
  constructor
  · intro h
    calc (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A
        = ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A *
            ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
              Matrix (Fin 3) (Fin 3) (ZMod 2))) * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
          rw [Matrix.mul_assoc _ _ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)), h2, Matrix.mul_one]
      _ = A * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by rw [h]
  · intro h
    calc (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A *
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
        = A * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2)) := by rw [h]
      _ = A := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private def burnsideJ27_j28_stabRepCodes : List ℕ := [10, 12, 17, 85]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private def burnsideJ27_j28_stabData : List (ℕ × ℕ × ℕ) :=
  [(10, 266, 10), (12, 273, 12), (14, 270, 10), (17, 266, 17), (19, 267, 10), (21, 277, 17),
    (23, 303, 10), (25, 275, 10), (29, 286, 10), (31, 271, 12), (34, 266, 12), (38, 270, 12),
    (42, 277, 10), (44, 277, 12), (46, 302, 10), (49, 270, 17), (51, 285, 10), (53, 285, 17),
    (55, 271, 10), (57, 311, 10), (59, 267, 12), (61, 279, 10), (66, 161, 12), (68, 140, 10),
    (70, 142, 10), (74, 394, 10), (76, 396, 10), (78, 401, 12), (81, 330, 17), (83, 459, 10),
    (85, 85, 85), (87, 213, 85), (89, 339, 10), (91, 225, 12), (93, 125, 85), (96, 84, 12),
    (98, 254, 85), (100, 204, 10), (104, 85, 12), (108, 460, 10), (110, 157, 85), (113, 375, 10),
    (117, 93, 85), (119, 470, 12), (121, 334, 17), (123, 183, 85), (125, 117, 85),
    (127, 207, 10), (132, 140, 12), (134, 142, 12), (136, 98, 12), (138, 330, 10),
    (140, 253, 85), (145, 394, 17), (147, 395, 10), (149, 431, 10), (151, 405, 17),
    (153, 467, 10), (155, 226, 12), (159, 111, 85), (160, 84, 10), (162, 340, 10),
    (164, 212, 10), (166, 468, 10), (168, 85, 10), (170, 330, 12), (174, 94, 85), (177, 142, 85),
    (179, 190, 85), (181, 158, 85), (183, 174, 85), (185, 206, 85), (189, 461, 12),
    (191, 215, 10), (194, 163, 12), (196, 156, 10), (198, 158, 10), (200, 99, 12),
    (202, 458, 10), (206, 239, 85), (209, 458, 17), (211, 331, 10), (213, 215, 85),
    (215, 87, 85), (217, 403, 10), (221, 397, 12), (223, 412, 10), (224, 92, 10), (228, 204, 12),
    (230, 110, 85), (232, 93, 10), (234, 247, 85), (236, 181, 85), (238, 477, 17),
    (241, 207, 85), (243, 331, 12), (245, 494, 10), (249, 143, 85), (251, 348, 10),
    (255, 207, 12), (257, 140, 17), (259, 156, 17), (261, 141, 10), (263, 159, 10),
    (265, 204, 17), (267, 99, 85), (269, 461, 10), (271, 230, 85), (272, 84, 17), (274, 212, 17),
    (276, 340, 17), (278, 468, 17), (280, 92, 17), (282, 98, 85), (284, 351, 10), (286, 102, 85),
    (289, 396, 17), (291, 415, 10), (293, 397, 10), (295, 412, 17), (297, 460, 17),
    (299, 165, 85), (301, 205, 10), (303, 103, 85), (304, 86, 10), (306, 470, 10),
    (308, 342, 10), (310, 214, 10), (312, 95, 10), (314, 229, 85), (316, 348, 17),
    (318, 167, 85), (321, 165, 10), (323, 174, 10), (327, 143, 12), (329, 229, 10),
    (331, 123, 85), (333, 337, 12), (336, 85, 17), (338, 239, 10), (340, 84, 85), (342, 86, 85),
    (344, 93, 17), (346, 114, 85), (348, 116, 85), (350, 477, 10), (353, 485, 10),
    (357, 340, 12), (359, 95, 85), (361, 421, 10), (363, 395, 12), (367, 405, 10), (368, 94, 10),
    (372, 124, 85), (374, 206, 12), (376, 87, 10), (378, 458, 12), (380, 92, 85), (385, 142, 17),
    (387, 157, 17), (389, 157, 10), (391, 143, 10), (393, 247, 10), (395, 107, 85),
    (399, 465, 12), (400, 102, 10), (402, 230, 10), (404, 486, 10), (406, 358, 10),
    (408, 110, 10), (410, 122, 85), (414, 334, 12), (417, 140, 85), (419, 172, 85),
    (421, 188, 85), (423, 156, 85), (425, 141, 85), (427, 478, 10), (429, 205, 12),
    (434, 394, 12), (436, 396, 12), (440, 87, 12), (444, 159, 85), (446, 334, 10),
    (449, 183, 10), (451, 167, 10), (453, 141, 12), (457, 206, 17), (459, 115, 85),
    (461, 244, 85), (463, 335, 10), (464, 111, 10), (466, 213, 17), (468, 214, 85),
    (470, 212, 85), (472, 103, 10), (474, 106, 85), (476, 460, 12), (481, 205, 85),
    (483, 459, 12), (487, 359, 10), (489, 204, 85), (493, 213, 10), (495, 335, 12),
    (496, 86, 12), (498, 236, 85), (502, 206, 10), (506, 407, 10), (508, 423, 10), (510, 407, 12)]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ27_j28_stab_data_cover :
    ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → ¬ (A * A = 0 ∨ A * A * A + A + 1 = 0) →
      ∃ t ∈ burnsideJ27_j28_stabData, t.1 = burnsideJ27_j28_matEnc A := by
  decide +kernel

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ27_j28_stab_data_check : ∀ t ∈ burnsideJ27_j28_stabData,
    burnsideJ27_j28_matDet3 (burnsideJ27_j28_matDec t.2.1) = 1 ∧
      burnsideJ27_j28_matDec t.2.1 * burnsideJ27_j28_matDec t.1 =
        burnsideJ27_j28_matDec t.2.2 * burnsideJ27_j28_matDec t.2.1 ∧
      t.2.2 ∈ burnsideJ27_j28_stabRepCodes := by
  decide +kernel

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ27_j28_stab_reps_card : ∀ r ∈ burnsideJ27_j28_stabRepCodes,
    Fintype.card {g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) //
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * burnsideJ27_j28_matDec r =
        burnsideJ27_j28_matDec r * (g : Matrix (Fin 3) (Fin 3) (ZMod 2))} ≤ 6 := by
  decide +kernel

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ27_j28_stab_reps_conj :
    ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → ¬ (A * A = 0 ∨ A * A * A + A + 1 = 0) →
      ∃ h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), ∃ r ∈ burnsideJ27_j28_stabRepCodes,
        (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A =
          burnsideJ27_j28_matDec r * (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  intro A h1 h2
  obtain ⟨t, ht, hA⟩ := burnsideJ27_j28_stab_data_cover A h1 h2
  rw [← burnsideJ27_j28_mat_dec_enc A, ← hA]
  obtain ⟨hdet, hconj, hr⟩ := burnsideJ27_j28_stab_data_check t ht
  have hg : (burnsideJ27_j28_matDec t.2.1).det = 1 := by rw [Matrix.det_fin_three]; exact hdet
  exact ⟨⟨_, hg⟩, t.2.2, hr, hconj⟩

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ27_j28_stab_card_conj (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    {A R : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hAR : (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A = R * (h : Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    Fintype.card {g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) //
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A = A * (g : Matrix (Fin 3) (Fin 3) (ZMod 2))} =
      Fintype.card {g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) //
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * R = R * (g : Matrix (Fin 3) (Fin 3) (ZMod 2))} := by
  set H : Matrix (Fin 3) (Fin 3) (ZMod 2) := (h : Matrix (Fin 3) (Fin 3) (ZMod 2))
  set H' : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
    ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
  have h1 : H * H' = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : H' * H = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hR : R = H * A * H' := by
    rw [hAR, Matrix.mul_assoc, h1, Matrix.mul_one]
  refine Fintype.card_congr (Equiv.subtypeEquiv (MulAut.conj h).toEquiv fun g => ?_)
  show _ ↔ ((h * g * h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) * R = R * ((h * g * h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2))
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  set G : Matrix (Fin 3) (Fin 3) (ZMod 2) := (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
  rw [hR]
  have e1 : H * G * H' * (H * A * H') = H * (G * A) * H' := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc H' H, h2, Matrix.one_mul]
  have e2 : H * A * H' * (H * G * H') = H * (A * G) * H' := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc H' H, h2, Matrix.one_mul]
  rw [e1, e2]
  have key : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), H' * (H * X * H') * H = X := fun X =>
    calc H' * (H * X * H') * H = (H' * H) * X * (H' * H) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  constructor
  · intro hc; rw [hc]
  · intro hc; rw [← key (G * A), hc, key]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_stab_le_comm :
    ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → ¬ (A * A = 0 ∨ A * A * A + A + 1 = 0) →
      Fintype.card {g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) //
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A = A * (g : Matrix (Fin 3) (Fin 3) (ZMod 2))} ≤
          6 := by
  intro A h1 h2
  obtain ⟨h, r, hr, hAR⟩ := burnsideJ27_j28_stab_reps_conj A h1 h2
  rw [burnsideJ27_j28_stab_card_conj h hAR]
  exact burnsideJ27_j28_stab_reps_card r hr

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_stab_le :
    ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → ¬ (A * A = 0 ∨ A * A * A + A + 1 = 0) →
      Fintype.card {g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) // stAct g A = A} ≤ 6 := by
  intro A h1 h2
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun g => burnsideJ27_j28_stAct_eq_iff g A)]
  exact burnsideJ27_j28_stab_le_comm A h1 h2

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_dec_R0 : ∀ r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), r ∈ SL3.R0 → r ≠ 1 →
    Fintype.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // A.trace = 0 ∧ stAct r A = A} = 16 ∧
    (∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → stAct r A = A →
      ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B.trace = 0 ∧ stAct r B + B = A) ∧
    Fintype.card {u : Fin 3 → ZMod 2 // natAct3 r u = u} = 4 := by
  decide +kernel

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_U0_sq : ∀ u : SigmaL2F4, u ∈ Sigma.U0 → u ^ 2 = 1 := by
  decide +kernel

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private def burnsideJ27_j28_t0 : SigmaL2F4 := ⟨⟨!![1, 1; 0, 1], by decide⟩, 1⟩

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ27_j28_sl_inv_conj_t0 : ∀ A : SigmaL2F4, A ^ 2 = 1 → A.right = 1 →
    A ≠ 1 → ∃ g : SigmaL2F4, g * A * g⁻¹ = burnsideJ27_j28_t0 := by
  decide +kernel

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_sl_inv_conj : ∀ A A' : SigmaL2F4, A ^ 2 = 1 → A.right = 1 → A ≠ 1 →
    A' ^ 2 = 1 → A'.right = 1 → A' ≠ 1 → ∃ g : SigmaL2F4, g * A * g⁻¹ = A' := by
  intro A A' h1 h2 h3 h1' h2' h3'
  obtain ⟨g, hg⟩ := burnsideJ27_j28_sl_inv_conj_t0 A h1 h2 h3
  obtain ⟨g', hg'⟩ := burnsideJ27_j28_sl_inv_conj_t0 A' h1' h2' h3'
  refine ⟨g'⁻¹ * g, ?_⟩
  calc g'⁻¹ * g * A * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * A * g⁻¹) * g' := by group
    _ = g'⁻¹ * (g' * A' * g'⁻¹) * g' := by rw [hg, hg']
    _ = A' := by group

section BurnsideJ28Cnt

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_sq_mul_V {G : Type} [Group G] [Finite G] (M : RuDataM G) {s v : G}
    (hs : s ∈ ruS M.L) (hv : v ∈ ruV M.L) : (s * v) ^ 2 = s ^ 2 := by
  have hc : s * v = v * s := M.V_comm_S hv hs
  have hv2 : v * v = 1 := by rw [← pow_two]; exact M.sq_eq_one_of_V hv
  calc (s * v) ^ 2 = s * (v * s) * v := by rw [pow_two]; group
    _ = s * (s * v) * v := by rw [← hc]
    _ = s * s * (v * v) := by group
    _ = s ^ 2 := by rw [hv2, mul_one, pow_two]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_zq_conj {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {A : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hA : ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd A ∧ (s : G) ^ 2 = 1)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd (stAct g A) ∧ (s : G) ^ 2 = 1 := by
  obtain ⟨s, hs, hs2⟩ := hA
  obtain ⟨l, rfl⟩ := M.θ_surj g
  have hmem : (l : G) * s * (l : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L l.2) s).mp s.2
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [M.χ_equiv l s ⟨_, hmem⟩ rfl, hs, toAdd_ofAdd]
  · show ((l : G) * s * (l : G)⁻¹) ^ 2 = 1
    rw [conj_pow, hs2]
    group

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_inv_S {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Nat.card {s : ruS M.L // (s : G) ^ 2 = 1} =
      8 * Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) //
        A.trace = 0 ∧ ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd A ∧ (s : G) ^ 2 = 1} := by
  classical
  let P := {s : ruS M.L // (s : G) ^ 2 = 1}
  let f : P → Matrix (Fin 3) (Fin 3) (ZMod 2) := fun s => Multiplicative.toAdd (M.χ s.1)
  have hsum : Nat.card P = ∑ B : Matrix (Fin 3) (Fin 3) (ZMod 2), Nat.card {s : P // f s = B} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  have hχB : ∀ (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (s : {s : P // f s = B}),
      M.χ s.1.1 = Multiplicative.ofAdd B := fun B s =>
    calc M.χ s.1.1 = Multiplicative.ofAdd (Multiplicative.toAdd (M.χ s.1.1)) :=
          (ofAdd_toAdd _).symm
      _ = Multiplicative.ofAdd B := congrArg _ s.2
  have hfib : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), Nat.card {s : P // f s = B} =
      if (B.trace = 0 ∧ ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd B ∧ (s : G) ^ 2 = 1)
        then 8 else 0 := by
    intro B
    by_cases hB : B.trace = 0 ∧ ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd B ∧ (s : G) ^ 2 = 1
    · rw [if_pos hB]
      obtain ⟨-, s0, hs0, hs02⟩ := hB
      rw [← M.toRuData.card_V]
      have hmemV : ∀ s : {s : P // f s = B}, (s0 : G)⁻¹ * (s.1.1 : G) ∈ ruV M.L := by
        intro s
        have hk : s0⁻¹ * s.1.1 ∈ M.χ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hχB B s, hs0]
          exact inv_mul_cancel _
        rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
        exact hk
      have hχV : ∀ v : ruV M.L, M.χ ⟨(v : G), M.toRuData.V_le_S v.2⟩ = 1 := by
        intro v
        have : (⟨(v : G), M.toRuData.V_le_S v.2⟩ : ruS M.L) ∈ M.χ.ker := by
          rw [M.χ_ker, Subgroup.mem_subgroupOf]
          exact v.2
        exact this
      refine Nat.card_congr
        { toFun := fun s => ⟨(s0 : G)⁻¹ * (s.1.1 : G), hmemV s⟩
          invFun := fun v => ⟨⟨s0 * ⟨v.1, M.toRuData.V_le_S v.2⟩, by
              show ((s0 : G) * (v : G)) ^ 2 = 1
              rw [burnsideJ27_j28_sq_mul_V M s0.2 v.2, hs02]⟩, by
              show Multiplicative.toAdd (M.χ (s0 * ⟨v.1, M.toRuData.V_le_S v.2⟩)) = B
              rw [map_mul, hχV v, mul_one, hs0, toAdd_ofAdd]⟩
          left_inv := fun s => ?_
          right_inv := fun v => ?_ }
      · apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        show (s0 : G) * ((s0 : G)⁻¹ * (s.1.1 : G)) = (s.1.1 : G)
        group
      · apply Subtype.ext
        show (s0 : G)⁻¹ * ((s0 : G) * (v : G)) = (v : G)
        group
    · rw [if_neg hB]
      have : IsEmpty {s : P // f s = B} := ⟨fun s => hB ⟨by
        have h := M.χ_trace s.1.1
        rwa [show Multiplicative.toAdd (M.χ s.1.1) = B from s.2] at h, s.1.1, hχB B s, s.1.2⟩⟩
      exact Nat.card_of_isEmpty
  rw [hsum]
  simp_rw [hfib]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_stAct_mul (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (A B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : stAct g (A * B) = stAct g A * stAct g B := by
  have h : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  unfold stAct
  calc (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (A * B) *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
      = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A * (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * B *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
        rw [Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A *
          (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) * B *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
        rw [h]
    _ = _ := by simp only [Matrix.mul_assoc]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_stAct_one (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    stAct g (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
  unfold stAct
  rw [Matrix.mul_one, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_stAct_zero (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    stAct g (0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
  unfold stAct
  simp

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_E_conj (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hA : A * A = 0 ∨ A * A * A + A + 1 = 0) :
    stAct g A * stAct g A = 0 ∨ stAct g A * stAct g A * stAct g A + stAct g A + 1 = 0 := by
  rcases hA with h | h
  · left
    rw [← burnsideJ27_j28_stAct_mul, h, burnsideJ27_j28_stAct_zero]
  · right
    have := congrArg (stAct g) h
    rw [SL3.stAct_add, SL3.stAct_add, burnsideJ27_j28_stAct_mul, burnsideJ27_j28_stAct_mul,
      burnsideJ27_j28_stAct_one, burnsideJ27_j28_stAct_zero] at this
    exact this

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_row0_inv {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hB : IsTraceZero B) (hr : SL3.IsRow0 B) :
    ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd B ∧ (s : G) ^ 2 = 1 := by
  have hmem : ((M.sOf B : ruS M.L) : G) ∈ ruU M.L M.T := by
    refine (M.mem_U_iff (M.sOf B).2).mpr ?_
    have : M.χ ⟨((M.sOf B : ruS M.L) : G), (M.sOf B).2⟩ = Multiplicative.ofAdd B :=
      M.χ_sOf hB
    rw [this, toAdd_ofAdd]
    exact hr
  exact ⟨M.sOf B, M.χ_sOf hB, M.U_sq hmem⟩

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_fixC0_inv {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hB : B ∈ SL3.fixC0List) :
    ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd B ∧ (s : G) ^ 2 = 1 := by
  obtain ⟨x, hx, hxχ⟩ := M.exists_S0_χ hB
  exact ⟨⟨x, (M.mem_S0.mp hx).1⟩, by rw [← hxχ, ofAdd_toAdd], M.S0_elem.2 x hx⟩

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_E_sub_Z {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (htr : A.trace = 0)
    (hA : A * A = 0 ∨ A * A * A + A + 1 = 0) :
    ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd A ∧ (s : G) ^ 2 = 1 := by
  rcases hA with h0 | h3
  · by_cases hA0 : A = 0
    · subst hA0
      exact ⟨1, by simp, by simp⟩
    · obtain ⟨g, hg⟩ := burnsideJ27_j28_nilp_conj A htr h0 hA0
      have hB : IsTraceZero (stAct g A) := by
        unfold IsTraceZero
        rw [SL3.trace_stAct]
        exact htr
      have := burnsideJ27_j28_zq_conj M (burnsideJ27_j28_row0_inv M hB hg) g⁻¹
      rwa [← SL3.stAct_mul, inv_mul_cancel, SL3.stAct_one] at this
  · obtain ⟨g, hg⟩ := burnsideJ27_j28_cubic_conj A h3
    have := burnsideJ27_j28_zq_conj M (burnsideJ27_j28_fixC0_inv M hg) g⁻¹
    rwa [← SL3.stAct_mul, inv_mul_cancel, SL3.stAct_one] at this

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_Z_eq (Z : Set (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hE : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 →
      (A * A = 0 ∨ A * A * A + A + 1 = 0) → A ∈ Z)
    (hZtr : ∀ A ∈ Z, A.trace = 0)
    (hconj : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)),
      A ∈ Z → stAct g A ∈ Z)
    (hcard : Nat.card Z ≤ 58) :
    ∀ A ∈ Z, A * A = 0 ∨ A * A * A + A + 1 = 0 := by
  classical
  intro A hA
  by_contra hnot
  let Es : Set (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    {B | B.trace = 0 ∧ (B * B = 0 ∨ B * B * B + B + 1 = 0)}
  let D : Set (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    {B | B ∈ Z ∧ ¬ (B * B = 0 ∨ B * B * B + B + 1 = 0)}
  have hEs : Nat.card Es = 46 := by
    have := burnsideJ27_j28_card_E
    rw [← Nat.card_eq_fintype_card] at this
    exact this
  have hEsZ : Es ⊆ Z := fun B hB => hE B hB.1 hB.2
  have hDZ : D ⊆ Z := fun B hB => hB.1
  have hdisj : Disjoint Es D := Set.disjoint_left.mpr fun B hB hD => hD.2 hB.2
  have hsum : Nat.card Es + Nat.card D ≤ Nat.card Z := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      ← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    exact Set.ncard_le_ncard (Set.union_subset hEsZ hDZ) (Set.toFinite _)
  have hAD : A ∈ D := ⟨hA, hnot⟩
  have hf : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), stAct g A ∈ D := by
    intro g
    refine ⟨hconj g A hA, fun h => hnot ?_⟩
    have := burnsideJ27_j28_E_conj g⁻¹ _ h
    rwa [← SL3.stAct_mul, inv_mul_cancel, SL3.stAct_one] at this
  let f : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) → D := fun g => ⟨stAct g A, hf g⟩
  have hfib : ∀ B : D, Nat.card {g // f g = B} ≤ 6 := by
    intro B
    by_cases hne : Nonempty {g // f g = B}
    · obtain ⟨⟨g0, hg0⟩⟩ := hne
      have hB : stAct g0 A = (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) := congrArg Subtype.val hg0
      have hstab : Fintype.card {h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) // stAct h A = A}
          ≤ 6 := burnsideJ27_j28_stab_le A (hZtr A hA) hnot
      calc Nat.card {g // f g = B}
          ≤ Nat.card {h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) // stAct h A = A} := by
            refine Nat.card_le_card_of_injective (fun g => ⟨g0⁻¹ * g.1, ?_⟩) ?_
            · have h1 : stAct g.1 A = (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
                congrArg Subtype.val g.2
              rw [SL3.stAct_mul, h1, ← hB, ← SL3.stAct_mul, inv_mul_cancel, SL3.stAct_one]
            · intro a b hab
              have h1 : g0⁻¹ * a.1 = g0⁻¹ * b.1 := congrArg Subtype.val hab
              exact Subtype.ext (mul_left_cancel h1)
        _ = Fintype.card {h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) // stAct h A = A} :=
            Nat.card_eq_fintype_card
        _ ≤ 6 := hstab
    · rw [not_nonempty_iff] at hne
      rw [Nat.card_of_isEmpty]
      omega
  have hD := card_le_mul_of_fiber f 6 hfib
  rw [SL3.card_SL3] at hD
  omega

open CFSG.ASVolI.ChIJK in
theorem burnsideJ27_j28_inv_iff {G : Type} [Group G] {x0 s : G} (hx : x0 ^ 2 = 1) :
    (x0 * s) ^ 2 = 1 ↔ x0 * s * x0⁻¹ = s⁻¹ := by
  have hxx : x0 * x0 = 1 := by rw [← pow_two]; exact hx
  have hinv : x0⁻¹ = x0 := inv_eq_of_mul_eq_one_right hxx
  rw [hinv, pow_two]
  constructor
  · intro h
    have : x0 * s * x0 * s = 1 := by simpa [mul_assoc] using h
    exact eq_inv_of_mul_eq_one_left this
  · intro h
    calc x0 * s * (x0 * s) = (x0 * s * x0) * s := by group
      _ = s⁻¹ * s := by rw [h]
      _ = 1 := inv_mul_cancel s

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_inv_mul_V {G : Type} [Group G] [Finite G] (M : RuDataM G) {x0 s v : G}
    (hx : x0 ^ 2 = 1) (hs : s ∈ ruS M.L) (hv : v ∈ ruV M.L) (hxs : (x0 * s) ^ 2 = 1) :
    (x0 * (s * v)) ^ 2 = 1 ↔ x0 * v * x0⁻¹ = v := by
  have h1 : x0 * s * x0⁻¹ = s⁻¹ := (burnsideJ27_j28_inv_iff hx).mp hxs
  have hc : s * v = v * s := M.V_comm_S hv hs
  have hv2 : v * v = 1 := by rw [← pow_two]; exact M.sq_eq_one_of_V hv
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  rw [burnsideJ27_j28_inv_iff hx]
  constructor
  · intro h
    have h2 : x0 * (s * v) * x0⁻¹ = (x0 * s * x0⁻¹) * (x0 * v * x0⁻¹) := by group
    rw [h2, h1, mul_inv_rev, hvinv] at h
    have hcs : s⁻¹ * v = v * s⁻¹ := by
      have := congrArg (fun y => s⁻¹ * y * s⁻¹) hc
      simpa [mul_assoc] using this.symm
    calc x0 * v * x0⁻¹ = s * (s⁻¹ * (x0 * v * x0⁻¹)) := by group
      _ = s * (v * s⁻¹) := by rw [h]
      _ = s * (s⁻¹ * v) := by rw [hcs]
      _ = v := by group
  · intro h
    have h2 : x0 * (s * v) * x0⁻¹ = (x0 * s * x0⁻¹) * (x0 * v * x0⁻¹) := by group
    rw [h2, h1, h, mul_inv_rev, hvinv]
    have hcs : s⁻¹ * v = v * s⁻¹ := by
      have := congrArg (fun y => s⁻¹ * y * s⁻¹) hc
      simpa [mul_assoc] using this.symm
    exact hcs

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_CV {G : Type} [Group G] [Finite G] (M : RuDataM G) (x0L : M.L)
    (h4 : Fintype.card {u : Fin 3 → ZMod 2 // natAct3 (M.θ x0L) u = u} = 4) :
    Nat.card {v : ruV M.L // (x0L : G) * v * (x0L : G)⁻¹ = v} = 4 := by
  rw [← h4, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd (M.ψV v.1), (M.toRuData.conj_eq_iff x0L v.1).mp v.2⟩
      invFun := fun u => ⟨M.ψV.symm (Multiplicative.ofAdd u.1), (M.toRuData.conj_eq_iff x0L _).mpr (by
          simpa using u.2)⟩
      left_inv := fun v => by simp
      right_inv := fun u => by simp }

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_coset_inv {G : Type} [Group G] [Finite G] (M : RuDataM G) {x0 : G}
    (hx0L : x0 ∈ M.L) (hx02 : x0 ^ 2 = 1) (hr0 : M.θ ⟨x0, hx0L⟩ ∈ SL3.R0)
    (hr1 : M.θ ⟨x0, hx0L⟩ ≠ 1) :
    Nat.card {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = M.θ ⟨x0, hx0L⟩ ∧ x ^ 2 = 1} = 64 := by
  classical
  obtain ⟨D1, D2, D3⟩ := burnsideJ27_j28_dec_R0 _ hr0 hr1
  have hxx : x0 * x0 = 1 := by rw [← pow_two]; exact hx02
  have hinv : x0⁻¹ = x0 := inv_eq_of_mul_eq_one_right hxx
  let x0L : M.L := ⟨x0, hx0L⟩
  let P := {s : ruS M.L // (x0 * (s : G)) ^ 2 = 1}
  have hθS : ∀ s : ruS M.L, M.θ ⟨(s : G), M.toRuData.S_le_L s.2⟩ = 1 := by
    intro s
    have : (⟨(s : G), M.toRuData.S_le_L s.2⟩ : M.L) ∈ M.θ.ker := by
      rw [M.θ_ker, Subgroup.mem_subgroupOf]
      exact s.2
    exact this
  have e1 : Nat.card {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = M.θ x0L ∧ x ^ 2 = 1} =
      Nat.card P := by
    have hfwd : ∀ x : {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = M.θ x0L ∧ x ^ 2 = 1},
        x0⁻¹ * x.1 ∈ ruS M.L := by
      intro x
      obtain ⟨hx, hθ, -⟩ := x.2
      have hkL : x0⁻¹ * x.1 ∈ M.L := mul_mem (inv_mem hx0L) hx
      have hk : (⟨x0⁻¹ * x.1, hkL⟩ : M.L) ∈ M.θ.ker := by
        rw [MonoidHom.mem_ker]
        have e : (⟨x0⁻¹ * x.1, hkL⟩ : M.L) = x0L⁻¹ * ⟨x.1, hx⟩ := rfl
        rw [e, map_mul, map_inv, hθ]
        exact inv_mul_cancel _
      rw [M.θ_ker, Subgroup.mem_subgroupOf] at hk
      exact hk
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x0⁻¹ * x.1, hfwd x⟩, by
          obtain ⟨-, -, hx2⟩ := x.2
          show (x0 * (x0⁻¹ * x.1)) ^ 2 = 1
          rw [mul_inv_cancel_left]
          exact hx2⟩
        invFun := fun s => ⟨x0 * (s.1 : G), ⟨mul_mem hx0L (M.toRuData.S_le_L s.1.2), by
          have e : (⟨x0 * (s.1 : G), mul_mem hx0L (M.toRuData.S_le_L s.1.2)⟩ : M.L) =
              x0L * ⟨(s.1 : G), M.toRuData.S_le_L s.1.2⟩ := rfl
          rw [e, map_mul, hθS s.1, mul_one], s.2⟩⟩
        left_inv := fun x => Subtype.ext (by
          show x0 * (x0⁻¹ * x.1) = x.1
          group)
        right_inv := fun s => Subtype.ext (Subtype.ext (by
          show x0⁻¹ * (x0 * (s.1 : G)) = (s.1 : G)
          group)) }
  rw [e1]
  let f : P → Matrix (Fin 3) (Fin 3) (ZMod 2) := fun s => Multiplicative.toAdd (M.χ s.1)
  have hsum : Nat.card P = ∑ A : Matrix (Fin 3) (Fin 3) (ZMod 2), Nat.card {s : P // f s = A} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  have hχA : ∀ (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (s : {s : P // f s = A}),
      M.χ s.1.1 = Multiplicative.ofAdd A := fun A s =>
    calc M.χ s.1.1 = Multiplicative.ofAdd (Multiplicative.toAdd (M.χ s.1.1)) :=
          (ofAdd_toAdd _).symm
      _ = Multiplicative.ofAdd A := congrArg _ s.2
  have hχV : ∀ v : ruV M.L, M.χ ⟨(v : G), M.toRuData.V_le_S v.2⟩ = 1 := by
    intro v
    have : (⟨(v : G), M.toRuData.V_le_S v.2⟩ : ruS M.L) ∈ M.χ.ker := by
      rw [M.χ_ker, Subgroup.mem_subgroupOf]
      exact v.2
    exact this
  have hfix : ∀ s : ruS M.L, M.χ ⟨x0 * (s : G) * x0⁻¹,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hx0L) s).mp s.2⟩ =
      Multiplicative.ofAdd (stAct (M.θ x0L) (Multiplicative.toAdd (M.χ s))) := fun s =>
    M.χ_equiv x0L s _ rfl
  have hfib : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), Nat.card {s : P // f s = A} =
      if (A.trace = 0 ∧ stAct (M.θ x0L) A = A) then 4 else 0 := by
    intro A
    by_cases hA : A.trace = 0 ∧ stAct (M.θ x0L) A = A
    · rw [if_pos hA]
      obtain ⟨htr, hfixA⟩ := hA
      obtain ⟨B, hBtr, hB⟩ := D2 A htr hfixA
      have hBtr' : IsTraceZero B := hBtr
      set t : ruS M.L := M.sOf B with ht
      have hχt : M.χ t = Multiplicative.ofAdd B := M.χ_sOf hBtr'
      have hconjt : x0 * (t : G) * x0⁻¹ ∈ ruS M.L :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hx0L) t).mp t.2
      set sA : ruS M.L := ⟨x0 * (t : G) * x0⁻¹, hconjt⟩ * t⁻¹ with hsA
      have hsAχ : M.χ sA = Multiplicative.ofAdd A := by
        apply Multiplicative.toAdd.injective
        rw [hsA, M.toAdd_χ_mul, M.toAdd_χ_inv, hχt, hfix t, hχt, toAdd_ofAdd, toAdd_ofAdd,
          toAdd_ofAdd]
        exact hB
      have hsAsq : (x0 * (sA : G)) ^ 2 = 1 := by
        have hcoe : (sA : G) = x0 * (t : G) * x0⁻¹ * (t : G)⁻¹ := rfl
        have h1 : x0 * (sA : G) = (t : G) * x0 * (t : G)⁻¹ := by
          rw [hcoe]
          calc x0 * (x0 * (t : G) * x0⁻¹ * (t : G)⁻¹)
              = (x0 * x0) * (t : G) * x0⁻¹ * (t : G)⁻¹ := by group
            _ = (t : G) * x0 * (t : G)⁻¹ := by rw [hxx, one_mul, hinv]
        rw [h1, conj_pow, hx02]
        group
      have hsAP : (x0 * (sA : G)) ^ 2 = 1 := hsAsq
      rw [← burnsideJ27_j28_card_CV M x0L D3]
      have hvmem : ∀ s : {s : P // f s = A}, (sA : G)⁻¹ * (s.1.1 : G) ∈ ruV M.L := by
        intro s
        have hk : sA⁻¹ * s.1.1 ∈ M.χ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hχA A s, hsAχ]
          exact inv_mul_cancel _
        rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
        exact hk
      refine Nat.card_congr
        { toFun := fun s => ⟨⟨(sA : G)⁻¹ * (s.1.1 : G), hvmem s⟩, ?_⟩
          invFun := fun v => ⟨⟨sA * ⟨(v.1 : G), M.toRuData.V_le_S v.1.2⟩, ?_⟩, ?_⟩
          left_inv := fun s => ?_
          right_inv := fun v => ?_ }
      ·
        have h2 : (x0 * ((sA : G) * ((sA : G)⁻¹ * (s.1.1 : G)))) ^ 2 = 1 := by
          rw [mul_inv_cancel_left]
          exact s.1.2
        exact (burnsideJ27_j28_inv_mul_V M hx02 sA.2 (hvmem s) hsAP).mp h2
      · show (x0 * ((sA : G) * (v.1 : G))) ^ 2 = 1
        exact (burnsideJ27_j28_inv_mul_V M hx02 sA.2 v.1.2 hsAP).mpr v.2
      · show Multiplicative.toAdd (M.χ (sA * ⟨(v.1 : G), M.toRuData.V_le_S v.1.2⟩)) = A
        rw [map_mul, hχV v.1, mul_one, hsAχ, toAdd_ofAdd]
      · apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        show (sA : G) * ((sA : G)⁻¹ * (s.1.1 : G)) = (s.1.1 : G)
        group
      · apply Subtype.ext
        apply Subtype.ext
        show (sA : G)⁻¹ * ((sA : G) * (v.1 : G)) = (v.1 : G)
        group
    · rw [if_neg hA]
      have : IsEmpty {s : P // f s = A} := ⟨fun s => hA ⟨by
        have h := M.χ_trace s.1.1
        rwa [show Multiplicative.toAdd (M.χ s.1.1) = A from s.2] at h, by
        have h1 : x0 * (s.1.1 : G) * x0⁻¹ = (s.1.1 : G)⁻¹ := (burnsideJ27_j28_inv_iff hx02).mp s.1.2
        have h2 := hfix s.1.1
        have h3 : (⟨x0 * (s.1.1 : G) * x0⁻¹,
            (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hx0L) s.1.1).mp
              s.1.1.2⟩ : ruS M.L) = s.1.1⁻¹ := Subtype.ext h1
        rw [h3] at h2
        have h4 := congrArg Multiplicative.toAdd h2
        rw [M.toAdd_χ_inv, toAdd_ofAdd] at h4
        have h5 : Multiplicative.toAdd (M.χ s.1.1) = A := s.2
        rw [h5] at h4
        exact h4.symm⟩⟩
      exact Nat.card_of_isEmpty
  rw [hsum]
  simp_rw [hfib]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcard : (Finset.univ.filter fun A : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
      A.trace = 0 ∧ stAct (M.θ x0L) A = A).card = 16 := by
    rw [← Fintype.card_subtype]
    exact D1
  rw [hcard]
  norm_num

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_Cset {G : Type} [Group G] [Finite G] (M : RuDataM G) {x1 : G}
    (hx1L : x1 ∈ M.L) (hx12 : x1 ^ 2 = 1) (hr0 : M.θ ⟨x1, hx1L⟩ ∈ SL3.R0)
    (hr1 : M.θ ⟨x1, hx1L⟩ ≠ 1) {r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hr : r ∈ SL3.R0) (hr' : r ≠ 1) :
    Nat.card {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = r ∧ x ^ 2 = 1} = 64 := by
  obtain ⟨g, -, hg⟩ := SL3.conj_R0_transitive _ hr0 hr1 r hr hr'
  obtain ⟨l, hl⟩ := M.θ_surj g
  rw [← burnsideJ27_j28_card_coset_inv M hx1L hx12 hr0 hr1]
  symm
  have hto : ∀ x : {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = M.θ ⟨x1, hx1L⟩ ∧ x ^ 2 = 1},
      ∃ hx : (l : G) * x.1 * (l : G)⁻¹ ∈ M.L,
        M.θ ⟨(l : G) * x.1 * (l : G)⁻¹, hx⟩ = r ∧ ((l : G) * x.1 * (l : G)⁻¹) ^ 2 = 1 := by
    intro x
    obtain ⟨hx, hθ, hx2⟩ := x.2
    have hmem : (l : G) * x.1 * (l : G)⁻¹ ∈ M.L := mul_mem (mul_mem l.2 hx) (inv_mem l.2)
    refine ⟨hmem, ?_, ?_⟩
    · have e : (⟨(l : G) * x.1 * (l : G)⁻¹, hmem⟩ : M.L) = l * ⟨x.1, hx⟩ * l⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hθ, hl, hg]
    · rw [conj_pow, hx2]
      group
  have hfrom : ∀ x : {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = r ∧ x ^ 2 = 1},
      ∃ hx : (l : G)⁻¹ * x.1 * (l : G) ∈ M.L,
        M.θ ⟨(l : G)⁻¹ * x.1 * (l : G), hx⟩ = M.θ ⟨x1, hx1L⟩ ∧
          ((l : G)⁻¹ * x.1 * (l : G)) ^ 2 = 1 := by
    intro x
    obtain ⟨hx, hθ, hx2⟩ := x.2
    have hmem : (l : G)⁻¹ * x.1 * (l : G) ∈ M.L := mul_mem (mul_mem (inv_mem l.2) hx) l.2
    refine ⟨hmem, ?_, ?_⟩
    · have e : (⟨(l : G)⁻¹ * x.1 * (l : G), hmem⟩ : M.L) = l⁻¹ * ⟨x.1, hx⟩ * l := rfl
      rw [e, map_mul, map_mul, map_inv, hθ, hl, ← hg]
      group
    · have : ((l : G)⁻¹ * x.1 * (l : G)) ^ 2 = (l : G)⁻¹ * x.1 ^ 2 * (l : G) := by
        have := conj_pow (a := (l : G)⁻¹) (b := x.1) (i := 2)
        simpa using this
      rw [this, hx2]
      group
  exact Nat.card_congr
    { toFun := fun x => ⟨(l : G) * x.1 * (l : G)⁻¹, hto x⟩
      invFun := fun x => ⟨(l : G)⁻¹ * x.1 * (l : G), hfrom x⟩
      left_inv := fun x => Subtype.ext (by
        show (l : G)⁻¹ * ((l : G) * x.1 * (l : G)⁻¹) * (l : G) = x.1
        group)
      right_inv := fun x => Subtype.ext (by
        show (l : G) * ((l : G)⁻¹ * x.1 * (l : G)) * (l : G)⁻¹ = x.1
        group) }

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_inv_R1_L {G : Type} [Group G] [Finite G] (M : RuDataM G) {x1 : G}
    (hx1L : x1 ∈ M.L) (hx12 : x1 ^ 2 = 1) (hr0 : M.θ ⟨x1, hx1L⟩ ∈ SL3.R0)
    (hr1 : M.θ ⟨x1, hx1L⟩ ≠ 1) :
    Nat.card {x : G // x ∈ M.R1 ∧ x ^ 2 = 1} =
      Nat.card {s : ruS M.L // (s : G) ^ 2 = 1} + 3 * 64 := by
  classical
  have hR1L : M.R1 ≤ M.L := Subgroup.map_subtype_le _
  let P := {x : G // x ∈ M.R1 ∧ x ^ 2 = 1}
  let f : P → Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := fun x => M.θ ⟨x.1, hR1L x.2.1⟩
  have hsum : Nat.card P = ∑ r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Nat.card {x : P // f x = r} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  have hfR0 : ∀ x : P, f x ∈ SL3.R0 := by
    intro x
    obtain ⟨h, hh⟩ := mem_pullL.mp x.2.1
    exact hh
  have hmemR1 : ∀ (z : G) (hz : z ∈ M.L), M.θ ⟨z, hz⟩ ∈ SL3.R0 → z ∈ M.R1 := fun z hz h =>
    mem_pullL.mpr ⟨hz, h⟩
  have hfib : ∀ r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), Nat.card {x : P // f x = r} =
      if r ∈ SL3.R0 then (if r = 1 then Nat.card {s : ruS M.L // (s : G) ^ 2 = 1} else 64)
        else 0 := by
    intro r
    by_cases hr : r ∈ SL3.R0
    · rw [if_pos hr]
      have hcset : Nat.card {x : P // f x = r} =
          Nat.card {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = r ∧ x ^ 2 = 1} := by
        refine Nat.card_congr
          { toFun := fun x => ⟨x.1.1, hR1L x.1.2.1, x.2, x.1.2.2⟩
            invFun := fun z => ⟨⟨z.1, hmemR1 z.1 z.2.choose (by rw [z.2.choose_spec.1]; exact hr),
              z.2.choose_spec.2⟩, z.2.choose_spec.1⟩
            left_inv := fun x => rfl
            right_inv := fun z => rfl }
      rw [hcset]
      by_cases hr1' : r = 1
      · rw [if_pos hr1']
        subst hr1'
        have hθS : ∀ s : ruS M.L, M.θ ⟨(s : G), M.toRuData.S_le_L s.2⟩ = 1 := by
          intro s
          have : (⟨(s : G), M.toRuData.S_le_L s.2⟩ : M.L) ∈ M.θ.ker := by
            rw [M.θ_ker, Subgroup.mem_subgroupOf]
            exact s.2
          exact this
        refine Nat.card_congr
          { toFun := fun z => ⟨⟨z.1, ?_⟩, z.2.choose_spec.2⟩
            invFun := fun s => ⟨(s.1 : G), M.toRuData.S_le_L s.1.2, hθS s.1, s.2⟩
            left_inv := fun z => rfl
            right_inv := fun s => rfl }
        have hk : (⟨z.1, z.2.choose⟩ : M.L) ∈ M.θ.ker := by
          rw [MonoidHom.mem_ker]
          exact z.2.choose_spec.1
        rw [M.θ_ker, Subgroup.mem_subgroupOf] at hk
        exact hk
      · rw [if_neg hr1']
        exact burnsideJ27_j28_card_Cset M hx1L hx12 hr0 hr1 hr hr1'
    · rw [if_neg hr]
      have : IsEmpty {x : P // f x = r} := ⟨fun x => hr (x.2 ▸ hfR0 x.1)⟩
      exact Nat.card_of_isEmpty
  rw [hsum]
  simp_rw [hfib]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  set F := Finset.univ.filter
    (fun r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) => r ∈ SL3.R0) with hF
  have h1F : (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∈ F := by
    simp [hF]
  have hcardF : F.card = 4 := by
    have := SL3.card_R0
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    exact this
  rw [← Finset.add_sum_erase F _ h1F, if_pos rfl]
  have h64 : ∑ x ∈ F.erase 1, (if x = 1 then Nat.card {s : ruS M.L // (s : G) ^ 2 = 1} else 64) =
      ∑ x ∈ F.erase 1, 64 :=
    Finset.sum_congr rfl fun x hx => if_neg (Finset.ne_of_mem_erase hx)
  rw [h64, Finset.sum_const, Finset.card_erase_of_mem h1F, hcardF, smul_eq_mul]

end BurnsideJ28Cnt

section BurnsideJ28Hside

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_fib_conj {G : Type} [Group G] [Finite G] (M : RuDataM G)
    (A : SigmaL2F4) (h : ruH M.T) :
    Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = M.φ h * A * (M.φ h)⁻¹ ∧ x ^ 2 = 1} =
      Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1} := by
  symm
  have hto : ∀ x : {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1},
      ∃ hx : (h : G) * x.1 * (h : G)⁻¹ ∈ ruH M.T,
        M.φ ⟨(h : G) * x.1 * (h : G)⁻¹, hx⟩ = M.φ h * A * (M.φ h)⁻¹ ∧
          ((h : G) * x.1 * (h : G)⁻¹) ^ 2 = 1 := by
    intro x
    obtain ⟨hx, hφ, hx2⟩ := x.2
    have hmem : (h : G) * x.1 * (h : G)⁻¹ ∈ ruH M.T := mul_mem (mul_mem h.2 hx) (inv_mem h.2)
    refine ⟨hmem, ?_, ?_⟩
    · have e : (⟨(h : G) * x.1 * (h : G)⁻¹, hmem⟩ : ruH M.T) = h * ⟨x.1, hx⟩ * h⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hφ]
    · rw [conj_pow, hx2]
      group
  have hfrom : ∀ y : {x : G // ∃ hx : x ∈ ruH M.T,
        M.φ ⟨x, hx⟩ = M.φ h * A * (M.φ h)⁻¹ ∧ x ^ 2 = 1},
      ∃ hx : (h : G)⁻¹ * y.1 * (h : G) ∈ ruH M.T,
        M.φ ⟨(h : G)⁻¹ * y.1 * (h : G), hx⟩ = A ∧ ((h : G)⁻¹ * y.1 * (h : G)) ^ 2 = 1 := by
    intro y
    obtain ⟨hy, hφ, hy2⟩ := y.2
    have hmem : (h : G)⁻¹ * y.1 * (h : G) ∈ ruH M.T := mul_mem (mul_mem (inv_mem h.2) hy) h.2
    refine ⟨hmem, ?_, ?_⟩
    · have e : (⟨(h : G)⁻¹ * y.1 * (h : G), hmem⟩ : ruH M.T) = h⁻¹ * ⟨y.1, hy⟩ * h := rfl
      rw [e, map_mul, map_mul, map_inv, hφ]
      group
    · have : ((h : G)⁻¹ * y.1 * (h : G)) ^ 2 = (h : G)⁻¹ * y.1 ^ 2 * (h : G) := by
        have := conj_pow (a := (h : G)⁻¹) (b := y.1) (i := 2)
        simpa using this
      rw [this, hy2]
      group
  exact Nat.card_congr
    { toFun := fun x => ⟨(h : G) * x.1 * (h : G)⁻¹, hto x⟩
      invFun := fun y => ⟨(h : G)⁻¹ * y.1 * (h : G), hfrom y⟩
      left_inv := fun x => Subtype.ext (by
        show (h : G)⁻¹ * ((h : G) * x.1 * (h : G)⁻¹) * (h : G) = x.1
        group)
      right_inv := fun y => Subtype.ext (by
        show (h : G) * ((h : G)⁻¹ * y.1 * (h : G)) * (h : G)⁻¹ = y.1
        group) }

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_fib_conj' {G : Type} [Group G] [Finite G] (M : RuDataM G)
    (A g : SigmaL2F4) :
    Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = g * A * g⁻¹ ∧ x ^ 2 = 1} =
      Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1} := by
  obtain ⟨h, rfl⟩ := M.φ_surj g
  exact burnsideJ27_j28_card_fib_conj M A h

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_fib_inv {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {A A' : SigmaL2F4} (hA2 : A ^ 2 = 1) (hAr : A.right = 1) (hA1 : A ≠ 1)
    (hA2' : A' ^ 2 = 1) (hAr' : A'.right = 1) (hA1' : A' ≠ 1) :
    Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A' ∧ x ^ 2 = 1} =
      Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1} := by
  obtain ⟨g, hg⟩ := burnsideJ27_j28_sl_inv_conj A A' hA2 hAr hA1 hA2' hAr' hA1'
  rw [← hg]
  exact burnsideJ27_j28_card_fib_conj' M A g

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_fib_le {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {A : SigmaL2F4} (hA1 : A ≠ 1) :
    Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1} ≤ 128 := by
  by_cases hne : Nonempty {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1}
  · obtain ⟨⟨k, hkH, hkA, hk2⟩⟩ := hne
    have hkQ : k ∉ ruQ M.T := by
      intro hq
      apply hA1
      rw [← hkA]
      have hk : (⟨k, hkH⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [M.φ_ker, Subgroup.mem_subgroupOf]
        exact hq
      exact MonoidHom.mem_ker.mp hk
    have hQ : ∀ x : {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1},
        k⁻¹ * x.1 ∈ ruQ M.T := by
      intro x
      obtain ⟨hx, hφ, -⟩ := x.2
      have hker : (⟨k, hkH⟩ : ruH M.T)⁻¹ * ⟨x.1, hx⟩ ∈ M.φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hkA, inv_mul_cancel]
      rw [M.φ_ker, Subgroup.mem_subgroupOf] at hker
      simpa using hker
    refine (Nat.card_le_card_of_injective (fun x =>
      (⟨⟨k⁻¹ * x.1, hQ x⟩, by
        show (k * (k⁻¹ * x.1)) ^ 2 = 1
        rw [mul_inv_cancel_left]
        obtain ⟨hx, -, hx2⟩ := x.2
        exact hx2⟩ : {q : ruQ M.T // (k * (q : G)) ^ 2 = 1})) ?_).trans
      (M.card_inv_coset_le hkH hkQ hk2)
    intro x y h
    have h' : k⁻¹ * x.1 = k⁻¹ * y.1 := congrArg (fun w => ((w.1 : ruQ M.T) : G)) h
    exact Subtype.ext (mul_left_cancel h')
  · have := not_nonempty_iff.mp hne
    rw [Nat.card_of_isEmpty]
    omega

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_R1_le_H {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    M.R1 ≤ ruH M.T := by
  have hSH : ruS M.L ≤ ruH M.T := M.toRuData.S_le_T.trans M.toRuData.T_le_H
  have hQH : ruQ M.T ≤ ruH M.T := pCoreOf_le 2 _
  rw [← M.Q_sup_S]
  exact sup_le hQH hSH

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_φ_R1 {G : Type} [Group G] [Finite G] (M : RuDataM G) {x : G}
    (hx : x ∈ M.R1) : M.φ ⟨x, burnsideJ27_j28_R1_le_H M hx⟩ ∈ Sigma.U0 := by
  have hSH : ruS M.L ≤ ruH M.T := M.toRuData.S_le_T.trans M.toRuData.T_le_H
  have hQH : ruQ M.T ≤ ruH M.T := pCoreOf_le 2 _
  have hR : (M.R1.subgroupOf (ruH M.T)).map M.φ = ((ruS M.L).subgroupOf (ruH M.T)).map M.φ := by
    rw [← M.Q_sup_S, Subgroup.subgroupOf_sup hQH hSH, Subgroup.map_sup]
    have : ((ruQ M.T).subgroupOf (ruH M.T)).map M.φ = ⊥ := by
      rw [← M.φ_ker]
      exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
    rw [this, bot_sup_eq]
  have hmem : M.φ ⟨x, burnsideJ27_j28_R1_le_H M hx⟩ ∈ (M.R1.subgroupOf (ruH M.T)).map M.φ :=
    ⟨⟨x, burnsideJ27_j28_R1_le_H M hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rw [hR] at hmem
  obtain ⟨⟨s, hsH⟩, hs, he⟩ := hmem
  rw [← he]
  exact M.φ_S_mem (Subgroup.mem_subgroupOf.mp hs)

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_mem_R1_of_φ {G : Type} [Group G] [Finite G] (M : RuDataM G) {x : G}
    (hxH : x ∈ ruH M.T) (hx : M.φ ⟨x, hxH⟩ ∈ Sigma.U0) : x ∈ M.R1 := by
  obtain ⟨s, hs, hφs⟩ := M.exists_S_of_U0 hx
  have hsH : s ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T hs)
  have hk : (⟨x, hxH⟩ : ruH M.T) * ⟨s, hsH⟩⁻¹ ∈ M.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφs, mul_inv_cancel]
  rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
  have hk' : x * s⁻¹ ∈ ruQ M.T := hk
  rw [← M.Q_sup_S]
  have e : x = (x * s⁻¹) * s := by group
  rw [e]
  exact Subgroup.mul_mem_sup hk' hs

set_option linter.constructorNameAsVariable false in
open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_inv_R1_H {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {u : SigmaL2F4} (hu2 : u ^ 2 = 1) (hur : u.right = 1) (hu1 : u ≠ 1) :
    Nat.card {x : G // x ∈ M.R1 ∧ x ^ 2 = 1} =
      Nat.card {x : G // x ∈ ruQ M.T ∧ x ^ 2 = 1} +
        3 * Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = u ∧ x ^ 2 = 1} := by
  classical
  have hR1H := burnsideJ27_j28_R1_le_H M
  let P := {x : G // x ∈ M.R1 ∧ x ^ 2 = 1}
  let f : P → SigmaL2F4 := fun x => M.φ ⟨x.1, hR1H x.2.1⟩
  have hsum : Nat.card P = ∑ A : SigmaL2F4, Nat.card {x : P // f x = A} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  have hfib : ∀ A : SigmaL2F4, Nat.card {x : P // f x = A} =
      if A ∈ Sigma.U0 then
        Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1} else 0 := by
    intro A
    by_cases hA : A ∈ Sigma.U0
    · rw [if_pos hA]
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1.1, hR1H x.1.2.1, x.2, x.1.2.2⟩
          invFun := fun z => ⟨⟨z.1, burnsideJ27_j28_mem_R1_of_φ M z.2.choose
              (by rw [z.2.choose_spec.1]; exact hA), z.2.choose_spec.2⟩, z.2.choose_spec.1⟩
          left_inv := fun x => rfl
          right_inv := fun z => rfl }
    · rw [if_neg hA]
      have : IsEmpty {x : P // f x = A} :=
        ⟨fun x => hA (x.2 ▸ burnsideJ27_j28_φ_R1 M x.1.2.1)⟩
      exact Nat.card_of_isEmpty
  rw [hsum]
  simp_rw [hfib]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [← Finset.add_sum_erase (Finset.univ.filter (fun A : SigmaL2F4 => A ∈ Sigma.U0)) _
    (a := 1) (by simp)]
  have hcardF : ((Finset.univ.filter (fun A : SigmaL2F4 => A ∈ Sigma.U0)).erase 1).card = 3 := by
    rw [Finset.card_erase_of_mem (by simp)]
    have := Sigma.card_U0
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    rw [this]
  have h1 : Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = 1 ∧ x ^ 2 = 1} =
      Nat.card {x : G // x ∈ ruQ M.T ∧ x ^ 2 = 1} := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1, ?_, x.2.choose_spec.2⟩
        invFun := fun y => ⟨y.1, pCoreOf_le 2 _ y.2.1, ?_, y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have hk : (⟨x.1, x.2.choose⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [MonoidHom.mem_ker]
        exact x.2.choose_spec.1
      rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
      exact hk
    · have hk : (⟨y.1, pCoreOf_le 2 _ y.2.1⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [M.φ_ker, Subgroup.mem_subgroupOf]
        exact y.2.1
      exact MonoidHom.mem_ker.mp hk
  have h3 : ∑ A ∈ (Finset.univ.filter (fun A : SigmaL2F4 => A ∈ Sigma.U0)).erase 1,
      Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1} =
      ∑ A ∈ (Finset.univ.filter (fun A : SigmaL2F4 => A ∈ Sigma.U0)).erase 1,
        Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = u ∧ x ^ 2 = 1} := by
    refine Finset.sum_congr rfl fun A hA => ?_
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    obtain ⟨hA1, hAU⟩ := hA
    exact burnsideJ27_j28_card_fib_inv M hu2 hur hu1 (burnsideJ27_j28_U0_sq A hAU) hAU.2 hA1
  rw [h3, Finset.sum_const, hcardF, smul_eq_mul, h1]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_inv_Q {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Nat.card {x : G // x ∈ ruQ M.T ∧ x ^ 2 = 1} = 272 := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨l, hl, hne, w, hwl, hwQ, hwC, hw2⟩ := burnsideJ28_exists_w M
  have hI := burnsideJ28_card_I M hwQ hwC hw2
  have hUc := M.toRuData.card_U
  rw [natCard_subtype_eq] at hI ⊢
  have hUc' : (Finset.univ.filter fun x : G => x ∈ ruU M.L M.T).card = 32 := by
    rw [← natCard_subtype_eq]
    exact hUc
  have hsplit : (Finset.univ.filter fun x : G => x ∈ ruQ M.T ∧ x ^ 2 = 1) =
      (Finset.univ.filter fun x : G => x ∈ ruQ M.T ∧ x ∉ ruU M.L M.T ∧ x ^ 2 = 1) ∪
        (Finset.univ.filter fun x : G => x ∈ ruU M.L M.T) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hQ, hx2⟩
      by_cases hU : x ∈ ruU M.L M.T
      · exact Or.inr hU
      · exact Or.inl ⟨hQ, hU, hx2⟩
    · rintro (⟨hQ, -, hx2⟩ | hU)
      · exact ⟨hQ, hx2⟩
      · exact ⟨M.U_le_Q hU, M.U_sq hU⟩
  have hdisj : Disjoint
      (Finset.univ.filter fun x : G => x ∈ ruQ M.T ∧ x ∉ ruU M.L M.T ∧ x ^ 2 = 1)
      (Finset.univ.filter fun x : G => x ∈ ruU M.L M.T) :=
    Finset.disjoint_filter.mpr fun x _ h1 h2 => h1.2.1 h2
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hI, hUc']

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_exists_x1 {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ∃ x1 : G, ∃ hx1L : x1 ∈ M.L, x1 ^ 2 = 1 ∧ M.θ ⟨x1, hx1L⟩ ∈ SL3.R0 ∧
      M.θ ⟨x1, hx1L⟩ ≠ 1 := by
  obtain ⟨l, hl, hne, w, hwl, hwQ, hwC, hw2⟩ := burnsideJ28_exists_w M
  obtain ⟨k, hkK, hkS⟩ := M.exists_conj_not_mem_S hwQ hwC
  have hkH : k ∈ ruH M.T := M.K_le_H hkK
  have hx1Q : k * w * k⁻¹ ∈ ruQ M.T := M.conj_mem_Q hkH hwQ
  have hx1L : k * w * k⁻¹ ∈ M.L := M.Q_le_L hx1Q
  refine ⟨k * w * k⁻¹, hx1L, ?_, ?_, ?_⟩
  · rw [conj_pow, hw2]
    group
  · rw [← M.θQ_eq]
    exact ⟨⟨k * w * k⁻¹, hx1L⟩, Subgroup.mem_subgroupOf.mpr hx1Q, rfl⟩
  · intro h1
    apply hkS
    have hk : (⟨k * w * k⁻¹, hx1L⟩ : M.L) ∈ M.θ.ker := h1
    rw [M.θ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_inv_K {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {u : SigmaL2F4} (hu2 : u ^ 2 = 1) (hur : u.right = 1) (hu1 : u ≠ 1) :
    Nat.card {x : G // x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1} =
      15 * Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = u ∧ x ^ 2 = 1} := by
  classical
  have hKH := M.K_le_H
  let g : {x : G // x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1} →
      {A : SigmaL2F4 // A ^ 2 = 1 ∧ A.right = 1 ∧ A ≠ 1} := fun x =>
    ⟨M.φ ⟨x.1, hKH x.2.1⟩, by
      rw [← map_pow]
      have : (⟨x.1, hKH x.2.1⟩ : ruH M.T) ^ 2 = 1 := Subtype.ext (by simpa using x.2.2.2)
      rw [this, map_one], by
      obtain ⟨hk, h1⟩ := M.mem_K_iff.mp x.2.1
      exact h1, M.φ_ne_one (hKH x.2.1) x.2.2.1⟩
  have hsum : Nat.card {x : G // x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1} =
      ∑ A : {A : SigmaL2F4 // A ^ 2 = 1 ∧ A.right = 1 ∧ A ≠ 1}, Nat.card {x // g x = A} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma]
  have hfib : ∀ A : {A : SigmaL2F4 // A ^ 2 = 1 ∧ A.right = 1 ∧ A ≠ 1},
      Nat.card {x // g x = A} =
        Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = u ∧ x ^ 2 = 1} := by
    intro A
    rw [← burnsideJ27_j28_card_fib_inv M hu2 hur hu1 A.2.1 A.2.2.1 A.2.2.2]
    have hfrom : ∀ y : {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A.1 ∧ x ^ 2 = 1},
        y.1 ∈ M.K ∧ y.1 ∉ ruQ M.T ∧ y.1 ^ 2 = 1 := by
      intro y
      obtain ⟨hy, hφ, hy2⟩ := y.2
      refine ⟨M.mem_K_iff.mpr ⟨hy, by rw [hφ]; exact A.2.2.1⟩, fun hq => A.2.2.2 ?_, hy2⟩
      rw [← hφ]
      have hk : (⟨y.1, hy⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [M.φ_ker, Subgroup.mem_subgroupOf]
        exact hq
      exact MonoidHom.mem_ker.mp hk
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, hKH x.1.2.1, congrArg Subtype.val x.2, x.1.2.2.2⟩
        invFun := fun y => ⟨⟨y.1, hfrom y⟩, Subtype.ext y.2.choose_spec.1⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hsum, Finset.sum_congr rfl (fun A _ => hfib A), Finset.sum_const, Finset.card_univ,
    Sigma.card_inv_sl, smul_eq_mul]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_N {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {u : SigmaL2F4} (hu2 : u ^ 2 = 1) (hur : u.right = 1) (hu1 : u ≠ 1) :
    Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = u ∧ x ^ 2 = 1} = 96 := by
  classical
  obtain ⟨x1, hx1L, hx12, hr0, hr1⟩ := burnsideJ27_j28_exists_x1 M
  have hS := burnsideJ27_j28_card_inv_S M
  have hL := burnsideJ27_j28_card_inv_R1_L M hx1L hx12 hr0 hr1
  have hH := burnsideJ27_j28_card_inv_R1_H M hu2 hur hu1
  have hQ := burnsideJ27_j28_card_inv_Q M
  have hNle := burnsideJ27_j28_card_fib_le M hu1
  have hz58 : Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) //
      A.trace = 0 ∧ ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd A ∧ (s : G) ^ 2 = 1} ≤ 58 := by
    omega
  let Z : Set (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    {A | A.trace = 0 ∧ ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd A ∧ (s : G) ^ 2 = 1}
  have hZe : ∀ A ∈ Z, A * A = 0 ∨ A * A * A + A + 1 = 0 :=
    burnsideJ27_j28_Z_eq Z (fun A htr hA => ⟨htr, burnsideJ27_j28_E_sub_Z M htr hA⟩) (fun A hA => hA.1)
      (fun g A hA => ⟨by rw [SL3.trace_stAct]; exact hA.1, burnsideJ27_j28_zq_conj M hA.2 g⟩) hz58
  have hZeq : Z = {B : Matrix (Fin 3) (Fin 3) (ZMod 2) |
      B.trace = 0 ∧ (B * B = 0 ∨ B * B * B + B + 1 = 0)} := by
    ext A
    exact ⟨fun hA => ⟨hA.1, hZe A hA⟩, fun hA => ⟨hA.1, burnsideJ27_j28_E_sub_Z M hA.1 hA.2⟩⟩
  have hZ46 : Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) //
      A.trace = 0 ∧ ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd A ∧ (s : G) ^ 2 = 1} = 46 := by
    have h1 : Nat.card Z = 46 := by
      rw [hZeq]
      have := burnsideJ27_j28_card_E
      rw [← Nat.card_eq_fintype_card] at this
      exact this
    exact h1
  omega

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_inv_K_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Nat.card {x : G // x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1} = 1440 := by
  obtain ⟨⟨u, hu2, hur, hu1⟩⟩ : Nonempty {g : SigmaL2F4 // g ^ 2 = 1 ∧ g.right = 1 ∧ g ≠ 1} := by
    rw [← Fintype.card_pos_iff, Sigma.card_inv_sl]
    norm_num
  rw [burnsideJ27_j28_card_inv_K M hu2 hur hu1, burnsideJ27_j28_card_N M hu2 hur hu1]

end BurnsideJ28Hside
end BurnsideJ27J28

section BurnsideJ27J28Cert

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_sH {G : Type} [Group G] [Finite G] (M : RuDataM G) {s : G}
    (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    Nat.card {x : G // IsConj s x ∧ x ∈ ruH M.T} = 960 := by
  let _ : MulAction (ruH M.T) G := MulAction.compHom G ((MulAut.conj).comp (ruH M.T).subtype)
  have hsmul : ∀ (l : ruH M.T) (x : G), l • x = (l : G) * x * (l : G)⁻¹ := fun _ _ => rfl
  have hsH : s ∈ ruH M.T := M.S0_le_H hs
  have horb : MulAction.orbit (ruH M.T) s = {u : G | IsConj s u ∧ u ∈ ruH M.T} := by
    ext u
    simp only [MulAction.mem_orbit_iff, hsmul]
    show _ ↔ IsConj s u ∧ u ∈ ruH M.T
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨isConj_iff.mpr ⟨l, rfl⟩, mul_mem (mul_mem l.2 hsH) (inv_mem l.2)⟩
    · rintro ⟨hsu, huH⟩
      obtain ⟨⟨h, hh, rfl⟩, -, -⟩ := M.lemma_J27_8 hs hs1 huH hsu
      exact ⟨⟨h, hh⟩, rfl⟩
  have hstab : MulAction.stabilizer (ruH M.T) s =
      (ruH M.T ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf (ruH M.T) := by
    ext l
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨l.2, ?_⟩
      calc (l : G) * s = ((l : G) * s * (l : G)⁻¹) * l := by group
        _ = s * (l : G) := by rw [h]
    · rintro ⟨-, h⟩
      calc (l : G) * s * (l : G)⁻¹ = s * (l : G) * (l : G)⁻¹ := by rw [h]
        _ = s := by group
  have hstabcard : Nat.card (MulAction.stabilizer (ruH M.T) s) = 2 ^ 8 := by
    rw [hstab, card_subgroupOf_of_le inf_le_left, M.centralizer_H_eq hs hs1,
      M.card_centralizer_S (M.mem_S0.mp hs).1 (M.not_mem_V_of_S0 hs hs1)]
  have hcard : Nat.card (MulAction.orbit (ruH M.T) s) = 960 := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ruH M.T) s)]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MulAction.stabilizer (ruH M.T) s)
    rw [hstabcard, M.toRuData.card_H] at h
    omega
  rw [← hcard, horb]
  rfl

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ27_j28_card_zG_KQ {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Nat.card {x : G // IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T} = 480 := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨s, hs, hs1⟩ := M.exists_S0_ne_one
  have hs2 : s ^ 2 = 1 := M.S0_elem.2 s hs
  obtain ⟨hzs, hall⟩ := M.lemma_J27_4 hs hs1
  have hI := burnsideJ27_j28_card_inv_K_eq M
  have hB := burnsideJ27_j28_card_sH M hs hs1
  rw [natCard_subtype_eq] at hI hB ⊢
  have hsplit : (Finset.univ.filter fun x : G => x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1) =
      (Finset.univ.filter fun x : G => IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T) ∪
        (Finset.univ.filter fun x : G => IsConj s x ∧ x ∈ ruH M.T) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hK, hQ, hx2⟩
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hQ (one_mem _)
      rcases hall x hx2 hx1 with hz | hsx
      · exact Or.inl ⟨hz, hK, hQ⟩
      · exact Or.inr ⟨hsx, M.K_le_H hK⟩
    · rintro (⟨hz, hK, hQ⟩ | ⟨hsx, hH⟩)
      · refine ⟨hK, hQ, ?_⟩
        obtain ⟨g, rfl⟩ := isConj_iff.mp hz
        rw [conj_pow, M.z_sq]
        group
      · obtain ⟨-, hK, hQ⟩ := M.lemma_J27_8 hs hs1 hH hsx
        refine ⟨hK, hQ, ?_⟩
        obtain ⟨g, rfl⟩ := isConj_iff.mp hsx
        rw [conj_pow, hs2]
        group
  have hdisj : Disjoint (Finset.univ.filter fun x : G => IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T)
      (Finset.univ.filter fun x : G => IsConj s x ∧ x ∈ ruH M.T) :=
    Finset.disjoint_filter.mpr fun x _ h1 h2 => hzs (h1.1.trans h2.1.symm)
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hB] at hI
  omega

end BurnsideJ27J28Cert

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_zc : List ℕ := [9, 2, 1, 3, 7, 8, 6, 4, 5, 0]

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_Dc : List (List ℕ) :=
  Core.autL.filter fun c => Core.cmul c burnsideJ27_zc == Core.cmul burnsideJ27_zc c

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_Sigc : List (List ℕ) :=
  Core.autL.filter fun c => Core.cmul c c == Core.cid && !(CFSG.Quasithin.RuType.AutA6.inM10L c) &&
    Core.inS6 c && Core.cmul c burnsideJ27_zc == Core.cmul burnsideJ27_zc c

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_Delc : List (List ℕ) :=
  Core.autL.filter fun c => Core.cmul c c == Core.cid && !(CFSG.Quasithin.RuType.AutA6.inM10L c) &&
    !(Core.inS6 c) && Core.cmul c burnsideJ27_zc == Core.cmul burnsideJ27_zc c

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_Q8c : List (List ℕ) :=
  Core.autL.filter fun c => CFSG.Quasithin.RuType.AutA6.inM10L c &&
    Core.cmul c burnsideJ27_zc == Core.cmul burnsideJ27_zc c && Core.cpow c 4 == Core.cid &&
    (Core.cmul c c != Core.cid || c == Core.cid || c == burnsideJ27_zc)

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] def burnsideJ27_Ed (d : List ℕ) : List (List ℕ) :=
  burnsideJ27_Q8c ++ burnsideJ27_Q8c.map fun q => Core.cmul q d

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
private theorem burnsideJ27_Q8c_reorder : burnsideJ27_Q8c =
    Core.autL.filter fun c => Core.cmul c burnsideJ27_zc == Core.cmul burnsideJ27_zc c &&
      CFSG.Quasithin.RuType.AutA6.inM10L c && Core.cpow c 4 == Core.cid &&
      (Core.cmul c c != Core.cid || c == Core.cid || c == burnsideJ27_zc) := by
  unfold burnsideJ27_Q8c
  congr 1
  funext c
  rw [Bool.and_comm (CFSG.Quasithin.RuType.AutA6.inM10L c)]

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
private theorem burnsideJ27_Delc_reorder : burnsideJ27_Delc =
    Core.autL.filter fun c => Core.cmul c burnsideJ27_zc == Core.cmul burnsideJ27_zc c &&
      (Core.cmul c c == Core.cid && !(CFSG.Quasithin.RuType.AutA6.inM10L c) && !(Core.inS6 c)) := by
  unfold burnsideJ27_Delc
  congr 1
  funext c
  exact Bool.and_comm _ _

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
private theorem burnsideJ27_Sigc_reorder : burnsideJ27_Sigc =
    Core.autL.filter fun c => Core.cmul c burnsideJ27_zc == Core.cmul burnsideJ27_zc c &&
      (Core.cmul c c == Core.cid && !(CFSG.Quasithin.RuType.AutA6.inM10L c) && Core.inS6 c) := by
  unfold burnsideJ27_Sigc
  congr 1
  funext c
  exact Bool.and_comm _ _

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
private theorem burnsideJ27_Q8c_eq' : burnsideJ27_Q8c =
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [9, 2, 1, 3, 7, 8, 6, 4, 5, 0],
      [2, 0, 9, 3, 5, 7, 6, 8, 4, 1], [1, 9, 0, 3, 8, 4, 6, 5, 7, 2],
      [7, 8, 5, 3, 0, 1, 6, 9, 2, 4], [4, 5, 8, 3, 9, 2, 6, 0, 1, 7],
      [5, 7, 4, 3, 1, 9, 6, 2, 0, 8], [8, 4, 7, 3, 2, 0, 6, 1, 9, 5]] := by
  rw [burnsideJ27_Q8c_reorder]
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Dc_length : burnsideJ27_Dc.length = 32 := by decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Dc_nodup : burnsideJ27_Dc.Nodup := by decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Q8c_length : burnsideJ27_Q8c.length = 8 :=
  (congrArg List.length burnsideJ27_Q8c_eq').trans rfl

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Q8c_nodup : burnsideJ27_Q8c.Nodup := by
  rw [burnsideJ27_Q8c_eq']; decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Delc_eq : burnsideJ27_Delc =
    [[7, 8, 5, 6, 9, 2, 3, 0, 1, 4], [4, 5, 8, 6, 0, 1, 3, 9, 2, 7],
      [5, 7, 4, 6, 2, 0, 3, 1, 9, 8], [8, 4, 7, 6, 1, 9, 3, 2, 0, 5]] := by
  rw [burnsideJ27_Delc_reorder]
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Sigc_eq : burnsideJ27_Sigc =
    [[0, 1, 2, 6, 7, 8, 3, 4, 5, 9], [9, 2, 1, 6, 4, 5, 3, 7, 8, 0],
      [0, 2, 1, 3, 5, 4, 6, 8, 7, 9], [9, 1, 2, 3, 8, 7, 6, 5, 4, 0],
      [1, 0, 9, 3, 4, 8, 6, 7, 5, 2], [2, 9, 0, 3, 7, 5, 6, 4, 8, 1]] := by
  rw [burnsideJ27_Sigc_reorder]
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Q8c_eq : burnsideJ27_Q8c =
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [9, 2, 1, 3, 7, 8, 6, 4, 5, 0],
      [2, 0, 9, 3, 5, 7, 6, 8, 4, 1], [1, 9, 0, 3, 8, 4, 6, 5, 7, 2],
      [7, 8, 5, 3, 0, 1, 6, 9, 2, 4], [4, 5, 8, 3, 9, 2, 6, 0, 1, 7],
      [5, 7, 4, 3, 1, 9, 6, 2, 0, 8], [8, 4, 7, 3, 2, 0, 6, 1, 9, 5]] := by
  exact burnsideJ27_Q8c_eq'

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Ed_nodup : ∀ d ∈ burnsideJ27_Delc, (burnsideJ27_Ed d).Nodup := by
  rw [burnsideJ27_Delc_eq]
  simp only [burnsideJ27_Ed, burnsideJ27_Q8c_eq]
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Ed_length (d : List ℕ) : (burnsideJ27_Ed d).length = 16 := by
  unfold burnsideJ27_Ed
  rw [List.length_append, List.length_map, burnsideJ27_Q8c_length]

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Ed_sig : ∀ d ∈ burnsideJ27_Delc, ∀ σ ∈ burnsideJ27_Sigc,
    σ ∈ burnsideJ27_Ed d → σ = [0, 1, 2, 6, 7, 8, 3, 4, 5, 9] ∨
      σ = [9, 2, 1, 6, 4, 5, 3, 7, 8, 0] := by
  rw [burnsideJ27_Delc_eq, burnsideJ27_Sigc_eq]
  simp only [burnsideJ27_Ed, burnsideJ27_Q8c_eq]
  decide +kernel

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_g1_orbit : ∃ p ∈ burnsideJ27_Dc,
    Core.cmul p [0, 1, 2, 6, 7, 8, 3, 4, 5, 9] =
      Core.cmul [9, 2, 1, 6, 4, 5, 3, 7, 8, 0] p := by
  decide +kernel

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_ncard_code (L : List (List ℕ)) (hL : ∀ c ∈ L, c ∈ Core.autL)
    (hn : L.Nodup) : Set.ncard {σ : P10 | code σ ∈ L} = L.length := by
  classical
  have himg : code '' {σ : P10 | code σ ∈ L} = (↑L.toFinset : Set (List ℕ)) := by
    ext c
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      simpa using hσ
    · intro hc
      have hcL : c ∈ L := by simpa using hc
      obtain ⟨σ, -, hσc⟩ := AutA6.exists_of_mem_autL (hL c hcL)
      exact ⟨σ, by rw [Set.mem_setOf_eq, hσc]; exact hcL, hσc⟩
  rw [← Set.ncard_image_of_injective _ code_injective, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hn]

section Zeta

variable {G : Type} [Group G] [Finite G]
  (M : CFSG.Quasithin.RuType.RuDataM G)

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_rho_trans (e0 : M.NP ≃* A6Models.psl29) (a : ↥A6Models.autA6)
    (x : M.XP) :
    ((M.ρ (e0.trans (Unc25K1.A6Model.conjAut a)) x : A6Models.autA6) : Equiv.Perm (Fin 10)) =
      (a : P10) * ((M.ρ e0 x : A6Models.autA6) : P10) * (a : P10)⁻¹ := by
  set θ0 : ↥A6Models.autA6 := Unc25K1.A6Model.thetaEquiv e0 (MulAut.conjNormal x) with hθ0
  have hspec := fun k : M.NP => Unc25K1.A6Model.thetaEquiv_spec e0 (MulAut.conjNormal x) k
  have h : Unc25K1.A6Model.thetaEquiv (e0.trans (Unc25K1.A6Model.conjAut a))
      (MulAut.conjNormal x) =
      ⟨(a : P10) * (θ0 : P10) * (a : P10)⁻¹, by
        have := A6Models.autA6.mul_mem (A6Models.autA6.mul_mem a.2 θ0.2)
          (A6Models.autA6.inv_mem a.2)
        exact this⟩ := by
    apply Unc25K1.A6Model.thetaEquiv_eq
    intro k
    show ((Unc25K1.A6Model.conjAut a (e0 (MulAut.conjNormal x k)) : ↥A6Models.psl29) : P10) = _
    rw [Unc25K1.A6Model.conjAut_apply, hspec k]
    show (a : P10) * ((θ0 : P10) * ((e0 k : ↥A6Models.psl29) : P10) * (θ0 : P10)⁻¹) *
      (a : P10)⁻¹ = (a : P10) * (θ0 : P10) * (a : P10)⁻¹ *
        (((Unc25K1.A6Model.conjAut a (e0 k) : ↥A6Models.psl29)) : P10) *
          ((a : P10) * (θ0 : P10) * (a : P10)⁻¹)⁻¹
    rw [Unc25K1.A6Model.conjAut_apply]
    group
  show ((Unc25K1.A6Model.thetaEquiv (e0.trans (Unc25K1.A6Model.conjAut a))
    (MulAut.conjNormal x) : A6Models.autA6) : P10) = _
  rw [h]
  rfl

end Zeta

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_zc_eq : burnsideJ27_zc = code A6Models.tInv := burnsideJ27_zeta0_code.symm

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_Dc {σ : P10} (hσ : σ ∈ A6Models.autA6)
    (hc : σ * A6Models.tInv = A6Models.tInv * σ) : code σ ∈ burnsideJ27_Dc := by
  unfold burnsideJ27_Dc
  rw [List.mem_filter]
  refine ⟨code_mem_autL hσ, ?_⟩
  rw [beq_iff_eq, burnsideJ27_zc_eq, ← code_mul, ← code_mul, hc]

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_Sigc {σ : P10} (hσ : σ ∈ A6Models.autA6) (h2 : σ * σ = 1)
    (hm : σ ∉ A6Models.m10) (hs : σ ∈ s6) (hc : σ * A6Models.tInv = A6Models.tInv * σ) :
    code σ ∈ burnsideJ27_Sigc := by
  unfold burnsideJ27_Sigc
  rw [List.mem_filter]
  refine ⟨code_mem_autL hσ, ?_⟩
  have h2' : Core.cmul (code σ) (code σ) = Core.cid := by rw [← code_mul, h2, code_one]
  have hm' : AutA6.inM10L (code σ) = false := by
    rw [← Bool.not_eq_true, ← AutA6.mem_m10_iff]
    exact hm
  have hs' : Core.inS6 (code σ) = true := (mem_s6_iff σ).mp hs
  have hc' : (Core.cmul (code σ) burnsideJ27_zc == Core.cmul burnsideJ27_zc (code σ)) = true := by
    rw [beq_iff_eq, burnsideJ27_zc_eq, ← code_mul, ← code_mul, hc]
  simp [h2', hm', hs', hc']

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_Delc {σ : P10} (hσ : σ ∈ A6Models.autA6) (h2 : σ * σ = 1)
    (hm : σ ∉ A6Models.m10) (hs : σ ∉ s6) (hc : σ * A6Models.tInv = A6Models.tInv * σ) :
    code σ ∈ burnsideJ27_Delc := by
  unfold burnsideJ27_Delc
  rw [List.mem_filter]
  refine ⟨code_mem_autL hσ, ?_⟩
  have h2' : Core.cmul (code σ) (code σ) = Core.cid := by rw [← code_mul, h2, code_one]
  have hm' : AutA6.inM10L (code σ) = false := by
    rw [← Bool.not_eq_true, ← AutA6.mem_m10_iff]
    exact hm
  have hs' : Core.inS6 (code σ) = false := by
    rw [← Bool.not_eq_true, ← mem_s6_iff]
    exact hs
  have hc' : (Core.cmul (code σ) burnsideJ27_zc == Core.cmul burnsideJ27_zc (code σ)) = true := by
    rw [beq_iff_eq, burnsideJ27_zc_eq, ← code_mul, ← code_mul, hc]
  simp [h2', hm', hs', hc']

open CFSG.Quasithin.RuType CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_Q8c {σ : P10} (hσ : σ ∈ A6Models.autA6) (hm : σ ∈ A6Models.m10)
    (hc : σ * A6Models.tInv = A6Models.tInv * σ) (h4 : σ ^ 4 = 1)
    (hs : σ * σ = 1 → σ = 1 ∨ σ = A6Models.tInv) : code σ ∈ burnsideJ27_Q8c := by
  unfold burnsideJ27_Q8c
  rw [List.mem_filter]
  refine ⟨code_mem_autL hσ, ?_⟩
  have hm' : AutA6.inM10L (code σ) = true := (AutA6.mem_m10_iff σ).mp hm
  have hc' : (Core.cmul (code σ) burnsideJ27_zc == Core.cmul burnsideJ27_zc (code σ)) = true := by
    rw [beq_iff_eq, burnsideJ27_zc_eq, ← code_mul, ← code_mul, hc]
  have h4' : (Core.cpow (code σ) 4 == Core.cid) = true := by
    rw [beq_iff_eq, ← CFSG.QuasithinUnique.A6Facts.code_pow, h4, code_one]
  have hlast : (Core.cmul (code σ) (code σ) != Core.cid || code σ == Core.cid ||
      code σ == burnsideJ27_zc) = true := by
    by_cases hcc : Core.cmul (code σ) (code σ) = Core.cid
    · have h2 : σ * σ = 1 := code_injective (by rw [code_mul, hcc, code_one])
      rcases hs h2 with h | h
      · simp [h, code_one]
      · simp [h, burnsideJ27_zc_eq]
    · simp [hcc]
  simp [hm', hc', h4', hlast]

section TransX

variable {G : Type} [Group G] [Finite G]
  (M : CFSG.Quasithin.RuType.RuDataM G)

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_exists_e_zeta :
    ∃ e : M.NP ≃* A6Models.psl29, burnsideJ27_Phi M e M.zP = A6Models.tInv := by
  obtain ⟨e0⟩ := M.nonempty_NP_psl29
  obtain ⟨hζps, hζ2, hζ1⟩ := M.ρ_zP_props e0
  obtain ⟨p, hp, hpζ⟩ := burnsideJ27_psl_inv_class hζps hζ2 hζ1
  let a : ↥A6Models.autA6 := ⟨p, psl29_le_autA6 hp⟩
  refine ⟨e0.trans (Unc25K1.A6Model.conjAut a), ?_⟩
  show ((M.ρ (e0.trans (Unc25K1.A6Model.conjAut a)) (QuotientGroup.mk M.zP) :
    A6Models.autA6) : P10) = A6Models.tInv
  rw [burnsideJ27_rho_trans M e0 a]
  have h1 : (a : P10) * ((M.ρ e0 (QuotientGroup.mk M.zP) : A6Models.autA6) : P10) =
      A6Models.tInv * (a : P10) := hpζ
  calc (a : P10) * ((M.ρ e0 (QuotientGroup.mk M.zP) : A6Models.autA6) : P10) * (a : P10)⁻¹
      = (A6Models.tInv * (a : P10)) * (a : P10)⁻¹ := by rw [h1]
    _ = A6Models.tInv := by group

variable {M}
variable {e : M.NP ≃* CFSG.QuasithinUnique.A6Models.psl29} (he : burnsideJ27_Phi M e M.zP = CFSG.QuasithinUnique.A6Models.tInv)
include he

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_Phi_comm {h : M.GP} (hH : (h : G) ∈ ruH M.T) :
    burnsideJ27_Phi M e h * A6Models.tInv = A6Models.tInv * burnsideJ27_Phi M e h := by
  have := M.ρ_comm_zP e h hH
  rw [← he]
  exact this

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_HB_Phi {h : M.GP} (hh : (h : G) ∈ M.HB) :
    code (burnsideJ27_Phi M e h) ∈ burnsideJ27_Q8c := by
  have hGB : (h : G) ∈ M.GB := (Subgroup.mem_inf.mp hh).2
  have hQ : (h : G) ∈ ruQ M.T := (Subgroup.mem_inf.mp hh).1
  have hH : (h : G) ∈ ruH M.T := pCoreOf_le 2 _ hQ
  have hm10 : burnsideJ27_Phi M e h ∈ A6Models.m10 := (burnsideJ27_Phi_m10 M e h).mpr hGB
  have h4 : (burnsideJ27_Phi M e h) ^ 4 = 1 := by
    rw [← map_pow]
    have : h ^ 4 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      by_cases hZ : (h : G) ∈ ruZ M.T
      · rcases M.mem_Z_iff.mp hZ with h1 | h1
        · rw [h1]; simp
        · rw [h1, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, M.z_sq]; simp
      · rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, M.sq_eq_z_of_HB hh hZ, M.z_sq]
        simp
    rw [this, map_one]
  have hsq : burnsideJ27_Phi M e h * burnsideJ27_Phi M e h = 1 →
      burnsideJ27_Phi M e h = 1 ∨ burnsideJ27_Phi M e h = A6Models.tInv := by
    intro hs
    have hker : (h * h : M.GP) ∈ (burnsideJ27_Phi M e).ker := by
      rw [MonoidHom.mem_ker, map_mul, hs]
    rw [burnsideJ27_Phi_ker_eq, Subgroup.mem_subgroupOf] at hker
    have hhh : ((h * h : M.GP) : G) ∈ M.HB := by
      rw [Subgroup.coe_mul]
      exact mul_mem hh hh
    have h1 : ((h * h : M.GP) : G) = 1 := M.TB_inf_B _ (Or.inl hhh) hker
    by_cases hZ : (h : G) ∈ ruZ M.T
    · rcases M.mem_Z_iff.mp hZ with h2 | h2
      · left
        have : h = 1 := Subtype.ext h2
        rw [this, map_one]
      · right
        have : h = M.zP := Subtype.ext h2
        rw [this]
        exact he
    · exfalso
      have h3 := M.sq_eq_z_of_HB hh hZ
      rw [Subgroup.coe_mul, ← pow_two, h3] at h1
      exact M.z_ne_one h1
  exact burnsideJ27_mem_Q8c (burnsideJ27_Phi_mem M e h) hm10 (burnsideJ27_Phi_comm he hH) h4 hsq

end TransX

section TransX2

variable {G : Type} [Group G] [Finite G]
  (M : CFSG.Quasithin.RuType.RuDataM G)

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] noncomputable def burnsideJ27_Csub : Subgroup M.GP := Subgroup.centralizer ({M.zP} : Set M.GP)

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
@[expose] noncomputable def burnsideJ27_Wsub : Subgroup M.GP :=
  burnsideJ27_Csub M ⊓ M.K.subgroupOf M.GP

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_Wsub {y : M.GP} :
    y ∈ burnsideJ27_Wsub M ↔ y * M.zP = M.zP * y ∧ (y : G) ∈ M.K := by
  unfold burnsideJ27_Wsub burnsideJ27_Csub
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf]

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_HB_le_GP : M.HB ≤ M.GP := (inf_le_right).trans M.GB_le_GP

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_card_HB : Nat.card M.HB = 8 := by
  show Nat.card ↥(ruQ M.T ⊓ Subgroup.centralizer (M.B : Set G)) = 8
  rw [M.centralizer_Q_eq, M.card_centralizer_S_B]
  norm_num

variable {M}
variable {e : M.NP ≃* CFSG.QuasithinUnique.A6Models.psl29} (he : burnsideJ27_Phi M e M.zP = CFSG.QuasithinUnique.A6Models.tInv)
include he

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_PhiHB_eq :
    (((M.HB.subgroupOf M.GP).map (burnsideJ27_Phi M e) : Subgroup P10) : Set P10) =
      {σ : P10 | code σ ∈ burnsideJ27_Q8c} := by
  have hsub : (((M.HB.subgroupOf M.GP).map (burnsideJ27_Phi M e) : Subgroup P10) : Set P10) ⊆
      {σ : P10 | code σ ∈ burnsideJ27_Q8c} := by
    rintro _ ⟨y, hy, rfl⟩
    exact burnsideJ27_HB_Phi he (Subgroup.mem_subgroupOf.mp hy)
  have hQ8 : Set.ncard {σ : P10 | code σ ∈ burnsideJ27_Q8c} = 8 := by
    rw [burnsideJ27_ncard_code burnsideJ27_Q8c (fun c hc => (List.mem_filter.mp hc).1)
      burnsideJ27_Q8c_nodup, burnsideJ27_Q8c_length]
  have hinj : Set.InjOn (burnsideJ27_Phi M e) ((M.HB.subgroupOf M.GP : Subgroup M.GP) : Set M.GP) := by
    intro x hx y hy hxy
    have hker : x⁻¹ * y ∈ (burnsideJ27_Phi M e).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [burnsideJ27_Phi_ker_eq, Subgroup.mem_subgroupOf] at hker
    have hxy' : ((x⁻¹ * y : M.GP) : G) ∈ M.HB := by
      rw [Subgroup.coe_mul]
      exact mul_mem (by simpa using inv_mem (Subgroup.mem_subgroupOf.mp hx))
        (Subgroup.mem_subgroupOf.mp hy)
    have h1 : ((x⁻¹ * y : M.GP) : G) = 1 := M.TB_inf_B _ (Or.inl hxy') hker
    have h2 : x⁻¹ * y = 1 := Subtype.ext h1
    exact (inv_mul_eq_one.mp h2)
  have hcard : ((((M.HB.subgroupOf M.GP).map (burnsideJ27_Phi M e) : Subgroup P10)) :
      Set P10).ncard = 8 := by
    rw [Subgroup.coe_map, hinj.ncard_image, ← Nat.card_coe_set_eq]
    show Nat.card (M.HB.subgroupOf M.GP) = 8
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (burnsideJ27_HB_le_GP M)).toEquiv]
    exact burnsideJ27_card_HB M
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [hQ8, hcard])

end TransX2

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_g1_conj {a b : P10} (ha' : code a = [0, 1, 2, 6, 7, 8, 3, 4, 5, 9] ∨
      code a = [9, 2, 1, 6, 4, 5, 3, 7, 8, 0])
    (hb' : code b = [0, 1, 2, 6, 7, 8, 3, 4, 5, 9] ∨ code b = [9, 2, 1, 6, 4, 5, 3, 7, 8, 0]) :
    ∃ p ∈ A6Models.autA6, p * A6Models.tInv = A6Models.tInv * p ∧ p * a * p⁻¹ = b := by
  obtain ⟨p0, hp0D, hp0⟩ := burnsideJ27_g1_orbit
  have hp0L : p0 ∈ Core.autL := (List.mem_filter.mp hp0D).1
  have hp0c : Core.cmul p0 burnsideJ27_zc = Core.cmul burnsideJ27_zc p0 :=
    beq_iff_eq.mp (List.mem_filter.mp hp0D).2
  obtain ⟨π, hπ, hπc⟩ := AutA6.exists_of_mem_autL hp0L
  have hπcomm : π * A6Models.tInv = A6Models.tInv * π := by
    apply code_injective
    rw [code_mul, code_mul, hπc, ← burnsideJ27_zc_eq]
    exact hp0c
  have hSig1 : [0, 1, 2, 6, 7, 8, 3, 4, 5, 9] ∈ burnsideJ27_Sigc := by
    rw [burnsideJ27_Sigc_eq]
    simp
  have hSig2 : [9, 2, 1, 6, 4, 5, 3, 7, 8, 0] ∈ burnsideJ27_Sigc := by
    rw [burnsideJ27_Sigc_eq]
    simp
  obtain ⟨g1, -, hg1⟩ := AutA6.exists_of_mem_autL (List.mem_filter.mp hSig1).1
  obtain ⟨g2, -, hg2⟩ := AutA6.exists_of_mem_autL (List.mem_filter.mp hSig2).1
  have hrel : π * g1 = g2 * π := by
    apply code_injective
    rw [code_mul, code_mul, hπc, hg1, hg2]
    exact hp0
  have hrel' : g2 * π = π * g1 := hrel.symm
  have hcA : ∀ x : P10, (code x = [0, 1, 2, 6, 7, 8, 3, 4, 5, 9] ∨
      code x = [9, 2, 1, 6, 4, 5, 3, 7, 8, 0]) → x = g1 ∨ x = g2 := by
    intro x hx
    rcases hx with h | h
    · left
      exact code_injective (h.trans hg1.symm)
    · right
      exact code_injective (h.trans hg2.symm)
  rcases hcA a ha' with h1 | h1 <;> rcases hcA b hb' with h2 | h2
  · exact ⟨1, one_mem _, by simp, by rw [h1, h2]; simp⟩
  · exact ⟨π, hπ, hπcomm, by rw [h1, h2, hrel]; group⟩
  · refine ⟨π⁻¹, A6Models.autA6.inv_mem hπ, (Commute.inv_left (show Commute π A6Models.tInv from
      hπcomm)).eq, ?_⟩
    rw [h1, h2, inv_inv]
    calc π⁻¹ * g2 * π = π⁻¹ * (g2 * π) := by group
      _ = π⁻¹ * (π * g1) := by rw [hrel']
      _ = g1 := by group
  · exact ⟨1, one_mem _, by simp, by rw [h1, h2]; simp⟩

section TransX3

variable {G : Type} [Group G] [Finite G]
  {M : CFSG.Quasithin.RuType.RuDataM G}

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_mem_Csub {y : M.GP} : y ∈ burnsideJ27_Csub M ↔ y * M.zP = M.zP * y := by
  unfold burnsideJ27_Csub
  exact Subgroup.mem_centralizer_singleton_iff

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_HB_le_Wsub : M.HB.subgroupOf M.GP ≤ burnsideJ27_Wsub M := by
  intro y hy
  have hyHB : (y : G) ∈ M.HB := Subgroup.mem_subgroupOf.mp hy
  have hQ : (y : G) ∈ ruQ M.T := (Subgroup.mem_inf.mp hyHB).1
  have hH : (y : G) ∈ ruH M.T := pCoreOf_le 2 _ hQ
  rw [burnsideJ27_mem_Wsub]
  exact ⟨Subtype.ext (M.mem_H_iff_comm.mp hH).symm, M.Q_le_K hQ⟩

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_B_le_K : M.B ≤ M.K := by
  intro x hx
  rcases M.mem_B_iff.mp hx with h | h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact M.bel_mem_K
  · rw [h]; exact inv_mem M.bel_mem_K

variable {e : M.NP ≃* CFSG.QuasithinUnique.A6Models.psl29} (he : burnsideJ27_Phi M e M.zP = CFSG.QuasithinUnique.A6Models.tInv)
include he

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_PhiC_sub {y : M.GP} (hy : y ∈ burnsideJ27_Csub M) :
    code (burnsideJ27_Phi M e y) ∈ burnsideJ27_Dc := by
  apply burnsideJ27_mem_Dc (burnsideJ27_Phi_mem M e y)
  have hc := burnsideJ27_mem_Csub.mp hy
  rw [← he, ← map_mul, ← map_mul, hc]

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_card_PhiC_le :
    Nat.card ((burnsideJ27_Csub M).map (burnsideJ27_Phi M e)) ≤ 32 := by
  have hsub : (((burnsideJ27_Csub M).map (burnsideJ27_Phi M e) : Subgroup P10) : Set P10) ⊆
      {σ : P10 | code σ ∈ burnsideJ27_Dc} := by
    rintro _ ⟨y, hy, rfl⟩
    exact burnsideJ27_PhiC_sub he hy
  have h32 : Set.ncard {σ : P10 | code σ ∈ burnsideJ27_Dc} = 32 := by
    rw [burnsideJ27_ncard_code burnsideJ27_Dc (fun c hc => (List.mem_filter.mp hc).1)
      burnsideJ27_Dc_nodup,
      burnsideJ27_Dc_length]
  calc Nat.card ((burnsideJ27_Csub M).map (burnsideJ27_Phi M e))
      = Set.ncard (((burnsideJ27_Csub M).map (burnsideJ27_Phi M e) : Subgroup P10) : Set P10) :=
        (Nat.card_coe_set_eq _).symm
    _ ≤ Set.ncard {σ : P10 | code σ ∈ burnsideJ27_Dc} := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = 32 := h32

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_card_PhiW_le :
    Nat.card ((burnsideJ27_Wsub M).map (burnsideJ27_Phi M e)) ≤ 16 := by
  set A : Subgroup P10 := (burnsideJ27_Csub M).map (burnsideJ27_Phi M e) with hA
  set AW : Subgroup P10 := (burnsideJ27_Wsub M).map (burnsideJ27_Phi M e) with hAW
  have hle : AW ≤ A := Subgroup.map_mono inf_le_left
  have hA32 : Nat.card A ≤ 32 := burnsideJ27_card_PhiC_le he
  obtain ⟨hjH, hjK, -, -, -⟩ := M.jel_spec
  have hjGB : M.jel ∈ M.GB := M.TB_le_GB M.jel_mem_TB
  set j : M.GP := ⟨M.jel, M.GB_le_GP hjGB⟩ with hj
  have hjC : j ∈ burnsideJ27_Csub M := by
    rw [burnsideJ27_mem_Csub]
    exact Subtype.ext (M.mem_H_iff_comm.mp hjH).symm
  have hne : AW ≠ A := by
    intro heq
    have hjA : burnsideJ27_Phi M e j ∈ A := Subgroup.mem_map_of_mem _ hjC
    rw [← heq] at hjA
    obtain ⟨w, hw, hwj⟩ := hjA
    have hker : w⁻¹ * j ∈ (burnsideJ27_Phi M e).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwj, inv_mul_cancel]
    rw [burnsideJ27_Phi_ker_eq, Subgroup.mem_subgroupOf] at hker
    have hwK : (w : G) ∈ M.K := ((burnsideJ27_mem_Wsub M).mp hw).2
    have hBK : ((w⁻¹ * j : M.GP) : G) ∈ M.K := burnsideJ27_B_le_K hker
    apply hjK
    have : (M.jel : G) = (w : G) * ((w⁻¹ * j : M.GP) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [this]
    exact mul_mem hwK hBK
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · rw [mul_zero] at hk
      omega
    · rw [mul_one] at hk
      exact hne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hk))
  have h2 := Nat.mul_le_mul_left (Nat.card AW) hk2
  have h3 : Nat.card AW * k ≤ 32 := by rw [← hk]; exact hA32
  have h4 : Nat.card AW * 2 ≤ 32 := h2.trans h3
  show Nat.card AW ≤ 16
  omega

end TransX3

section TransX4

variable {G : Type} [Group G] [Finite G]
  {M : CFSG.Quasithin.RuType.RuDataM G}

variable {e : M.NP ≃* CFSG.QuasithinUnique.A6Models.psl29} (he : burnsideJ27_Phi M e M.zP = CFSG.QuasithinUnique.A6Models.tInv)
include he

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_exists_dW :
    ∃ d : M.GP, d ∈ burnsideJ27_Wsub M ∧ code (burnsideJ27_Phi M e d) ∈ burnsideJ27_Delc := by
  obtain ⟨s, hs, hs1⟩ := M.exists_S0_ne_one
  have hsH := M.S0_le_H hs
  have hs2 : s ^ 2 = 1 := M.S0_elem.2 _ hs
  have hsQ : s ∉ ruQ M.T := fun h => hs1 (M.eq_one_of_mem_S0_Q hs h)
  have hsz : ¬ IsConj M.z s := (M.lemma_J27_4 hs hs1).1
  obtain ⟨h, hh, hy, hyB, hy2, hys⟩ := M.exists_conj_diag e hsH hs2 hsQ hsz
  have hyH : h * s * h⁻¹ ∈ ruH M.T := mul_mem (mul_mem hh hsH) (inv_mem hh)
  have hyK : h * s * h⁻¹ ∈ M.K :=
    (M.lemma_J27_8 hs hs1 hyH (isConj_iff.mpr ⟨h, rfl⟩)).2.1
  refine ⟨⟨h * s * h⁻¹, hy⟩, ?_, ?_⟩
  · rw [burnsideJ27_mem_Wsub]
    exact ⟨Subtype.ext (M.mem_H_iff_comm.mp hyH).symm, hyK⟩
  · apply burnsideJ27_mem_Delc (burnsideJ27_Phi_mem M e _)
    · rw [← map_mul]
      have : (⟨h * s * h⁻¹, hy⟩ : M.GP) * ⟨h * s * h⁻¹, hy⟩ = 1 := Subtype.ext hy2
      rw [this, map_one]
    · exact fun hm => hyB ((burnsideJ27_Phi_m10 M e _).mp hm)
    · exact hys
    · exact burnsideJ27_Phi_comm he hyH

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_PhiW_sub {d : M.GP} (hd : d ∈ burnsideJ27_Wsub M)
    (hdc : code (burnsideJ27_Phi M e d) ∈ burnsideJ27_Delc) {w : M.GP}
    (hw : w ∈ burnsideJ27_Wsub M) :
    code (burnsideJ27_Phi M e w) ∈ burnsideJ27_Ed (code (burnsideJ27_Phi M e d)) := by
  set AW : Subgroup P10 := (burnsideJ27_Wsub M).map (burnsideJ27_Phi M e) with hAW
  set Es : Set P10 := {σ | code σ ∈ burnsideJ27_Ed (code (burnsideJ27_Phi M e d))} with hEs
  have hsub : Es ⊆ (AW : Set P10) := by
    intro σ hσ
    have hσ' : code σ ∈ burnsideJ27_Q8c ++ burnsideJ27_Q8c.map
        (fun q => Core.cmul q (code (burnsideJ27_Phi M e d))) := hσ
    rcases List.mem_append.mp hσ' with h1 | h2
    · have hmem : σ ∈ (((M.HB.subgroupOf M.GP).map (burnsideJ27_Phi M e) : Subgroup P10) :
          Set P10) := by
        rw [burnsideJ27_PhiHB_eq he]
        exact h1
      obtain ⟨y, hy, rfl⟩ := hmem
      exact ⟨y, burnsideJ27_HB_le_Wsub hy, rfl⟩
    · obtain ⟨q, hq, hqσ⟩ := List.mem_map.mp h2
      obtain ⟨τ, hτ, hτc⟩ := AutA6.exists_of_mem_autL ((List.mem_filter.mp hq).1)
      have hmem : τ ∈ (((M.HB.subgroupOf M.GP).map (burnsideJ27_Phi M e) : Subgroup P10) :
          Set P10) := by
        rw [burnsideJ27_PhiHB_eq he]
        show code τ ∈ burnsideJ27_Q8c
        rw [hτc]
        exact hq
      obtain ⟨y, hy, rfl⟩ := hmem
      have hσeq : σ = burnsideJ27_Phi M e y * burnsideJ27_Phi M e d := by
        apply code_injective
        rw [code_mul, hτc, hqσ]
      exact ⟨y * d, mul_mem (burnsideJ27_HB_le_Wsub hy) hd, by rw [map_mul, hσeq]⟩
  have hautL : ∀ c ∈ burnsideJ27_Ed (code (burnsideJ27_Phi M e d)), c ∈ Core.autL := by
    intro c hc
    rcases List.mem_append.mp hc with h1 | h2
    · exact (List.mem_filter.mp h1).1
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h2
      obtain ⟨τ, hτ, hτc⟩ := AutA6.exists_of_mem_autL ((List.mem_filter.mp hq).1)
      rw [← hτc, ← code_mul]
      exact code_mem_autL (A6Models.autA6.mul_mem hτ (burnsideJ27_Phi_mem M e d))
  have hcardEs : Es.ncard = 16 := by
    rw [hEs, burnsideJ27_ncard_code _ hautL (burnsideJ27_Ed_nodup _ hdc), burnsideJ27_Ed_length]
  have hcardAW : (AW : Set P10).ncard ≤ 16 := by
    rw [← Nat.card_coe_set_eq]
    exact burnsideJ27_card_PhiW_le he
  have heq : Es = (AW : Set P10) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcardEs]; exact hcardAW) (Set.toFinite _)
  have : burnsideJ27_Phi M e w ∈ Es := by
    rw [heq]
    exact ⟨w, hw, rfl⟩
  exact this

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_normal_form {d : M.GP} (hd : d ∈ burnsideJ27_Wsub M)
    (hdc : code (burnsideJ27_Phi M e d) ∈ burnsideJ27_Delc)
    {y : G} (hyz : IsConj M.z y) (hyK : y ∈ M.K) (hyQ : y ∉ ruQ M.T) :
    ∃ h ∈ ruH M.T, ∃ hy1 : h * y * h⁻¹ ∈ M.GP, h * y * h⁻¹ ∉ M.GB ∧
      (h * y * h⁻¹) * (h * y * h⁻¹) = 1 ∧
      (code (burnsideJ27_Phi M e ⟨h * y * h⁻¹, hy1⟩) = [0, 1, 2, 6, 7, 8, 3, 4, 5, 9] ∨
        code (burnsideJ27_Phi M e ⟨h * y * h⁻¹, hy1⟩) = [9, 2, 1, 6, 4, 5, 3, 7, 8, 0]) := by
  have hyH : y ∈ ruH M.T := M.K_le_H hyK
  have hy2 : y ^ 2 = 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hyz
    rw [← hg, conj_pow, M.z_sq]
    group
  obtain ⟨h, hh, hinv⟩ := M.exists_conj_inv_bel hyH hy2 hyQ
  have hyGP : h * y * h⁻¹ ∈ M.GP := M.mem_GP_of_inv hinv
  have hyB : h * y * h⁻¹ ∉ M.GB := fun hm => M.bel_ne_inv (by
    rw [← hinv, M.mem_GB_iff_conj.mp hm])
  have hy2' : (h * y * h⁻¹) * (h * y * h⁻¹) = 1 := by
    calc (h * y * h⁻¹) * (h * y * h⁻¹) = h * (y * y) * h⁻¹ := by group
      _ = 1 := by rw [← pow_two, hy2]; group
  have hy1H : h * y * h⁻¹ ∈ ruH M.T := mul_mem (mul_mem hh hyH) (inv_mem hh)
  have hy1K : h * y * h⁻¹ ∈ M.K := M.conj_mem_K hh hyK
  have hy1z : IsConj M.z (h * y * h⁻¹) := hyz.trans (isConj_iff.mpr ⟨h, rfl⟩)
  refine ⟨h, hh, hyGP, hyB, hy2', ?_⟩
  have hs6 : ((M.ρ e (QuotientGroup.mk (⟨h * y * h⁻¹, hyGP⟩ : M.GP)) : A6Models.autA6) :
      Equiv.Perm (Fin 10)) ∈ s6 := by
    by_contra hns
    obtain ⟨s, hs, hs1⟩ := M.exists_S0_ne_one
    have h1 := (M.outer_inv_classes e ⟨_, hyGP⟩ hyB hy2').2 hns s hs hs1
    exact (M.lemma_J27_4 hs hs1).1 (hy1z.trans h1.symm)
  have hmemW : (⟨h * y * h⁻¹, hyGP⟩ : M.GP) ∈ burnsideJ27_Wsub M := by
    rw [burnsideJ27_mem_Wsub]
    exact ⟨Subtype.ext (M.mem_H_iff_comm.mp hy1H).symm, hy1K⟩
  have hSig : code (burnsideJ27_Phi M e ⟨h * y * h⁻¹, hyGP⟩) ∈ burnsideJ27_Sigc := by
    apply burnsideJ27_mem_Sigc (burnsideJ27_Phi_mem M e _)
    · rw [← map_mul]
      have : (⟨h * y * h⁻¹, hyGP⟩ : M.GP) * ⟨h * y * h⁻¹, hyGP⟩ = 1 := Subtype.ext hy2'
      rw [this, map_one]
    · exact fun hm => hyB ((burnsideJ27_Phi_m10 M e _).mp hm)
    · exact hs6
    · exact burnsideJ27_Phi_comm he hy1H
  have hEd := burnsideJ27_PhiW_sub he hd hdc hmemW
  exact burnsideJ27_Ed_sig _ hdc _ hSig hEd

end TransX4

section TransX5

variable {G : Type} [Group G] [Finite G]

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem burnsideJ27_transX (M : RuDataM G) {x x' : G} (hx : IsConj M.z x) (hxK : x ∈ M.K)
    (hxQ : x ∉ ruQ M.T) (hx' : IsConj M.z x') (hx'K : x' ∈ M.K) (hx'Q : x' ∉ ruQ M.T) :
    ∃ m ∈ ruH M.T, m * x * m⁻¹ = x' := by
  obtain ⟨e, he⟩ := burnsideJ27_exists_e_zeta M
  obtain ⟨d, hd, hdc⟩ := burnsideJ27_exists_dW he
  obtain ⟨h, hh, hy, hyB, hy2, hΦ⟩ := burnsideJ27_normal_form he hd hdc hx hxK hxQ
  obtain ⟨h', hh', hy', hyB', hy2', hΦ'⟩ := burnsideJ27_normal_form he hd hdc hx' hx'K hx'Q
  obtain ⟨p, hp, hpc, hpa⟩ := burnsideJ27_g1_conj hΦ hΦ'
  have hz : ((M.ρ e (QuotientGroup.mk (⟨M.z, M.GB_le_GP (M.TB_le_GB M.z_mem_TB)⟩ : M.GP)) :
      A6Models.autA6) : Equiv.Perm (Fin 10)) = A6Models.tInv := he
  obtain ⟨k, hk, hkk⟩ := M.isConj_H_of_ρ_conj e (y := ⟨h * x * h⁻¹, hy⟩)
    (y' := ⟨h' * x' * h'⁻¹, hy'⟩) hyB hp (by rw [hz]; exact hpc) hpa
  refine ⟨h'⁻¹ * k * h, mul_mem (mul_mem (inv_mem hh') hk) hh, ?_⟩
  have e1 : k * (h * x * h⁻¹) * k⁻¹ = h' * x' * h'⁻¹ := hkk
  calc h'⁻¹ * k * h * x * (h'⁻¹ * k * h)⁻¹ = h'⁻¹ * (k * (h * x * h⁻¹) * k⁻¹) * h' := by group
    _ = x' := by rw [e1]; group

end TransX5

section Part8

open CFSG.ASVolI.ChIJK CFSG.Quasithin.RuType in
theorem burnsideJ27_part8 {G : Type} [Group G] [Finite G] (M : RuDataM G) {s : G}
    (hs : s ∈ M.S0) (hs1 : s ≠ 1) {g : G} (hgH : g ∈ ruH M.T) :
    ((∃ a ∈ involutionsOf M.K, a ∉ ruQ M.T ∧ ∃ b ∈ involutionsOf M.K, b ∉ ruQ M.T ∧
        (∀ i ∈ involutionsOf M.K, i ∉ ruQ M.T →
          (∃ h ∈ ruH M.T, i = h⁻¹ * a * h) ∨ (∃ h ∈ ruH M.T, i = h⁻¹ * b * h)) ∧
        (¬ ∃ h ∈ ruH M.T, b = h⁻¹ * a * h) ∧ a ∈ conjClass (g⁻¹ * s * g) ∧
        b ∈ conjClass M.z) ∧
      (∀ x ∈ ruH M.T, x ∈ conjClass (g⁻¹ * s * g) → ∃ h ∈ ruH M.T, x = h⁻¹ * (g⁻¹ * s * g) * h) ∧
      (∀ x ∈ ruH M.T, x ∈ conjClass (g⁻¹ * s * g) → x ∈ M.K ∧ x ∉ ruQ M.T) ∧
      (conjClass M.z ∩ ((M.K : Set G) \ (ruQ M.T : Set G))).ncard = 480) := by
  classical
  have hs2 : s ^ 2 = 1 := M.S0_elem.2 s hs
  have hsH : s ∈ ruH M.T := M.S0_le_H hs
  have hsgH : g⁻¹ * s * g ∈ ruH M.T := mul_mem (mul_mem (inv_mem hgH) hsH) hgH
  have hsgcl : g⁻¹ * s * g ∈ conjClass (g⁻¹ * s * g) := ⟨1, by group⟩
  obtain ⟨h8b, h8c⟩ := burnsideJ27_part8bc M hs hs1 hgH
  obtain ⟨hsgK, hsgQ⟩ := h8c _ hsgH hsgcl
  have hsg2 : (g⁻¹ * s * g) ^ 2 = 1 := by
    have := conj_pow (a := g⁻¹) (b := s) (i := 2)
    simp only [inv_inv] at this
    rw [this, hs2]
    group
  have hsg1 : g⁻¹ * s * g ≠ 1 := fun h => hs1 (by
    have : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
    rw [this, h]; group)
  obtain ⟨hcl, hnz⟩ := burnsideJ27_part4 M hs hs1 g
  have hcard := burnsideJ27_j28_card_zG_KQ M
  have hne : Nonempty {x : G // IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T} :=
    (Nat.card_pos_iff.mp (by rw [hcard]; norm_num)).1
  obtain ⟨⟨b, hbz, hbK, hbQ⟩⟩ := hne
  have hb2 : b ^ 2 = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hbz
    rw [← hc, conj_pow, M.z_sq]
    group
  have hb1 : b ≠ 1 := fun h => hbQ (h ▸ one_mem _)
  refine ⟨⟨_, ⟨hsgK, hsg2, hsg1⟩, hsgQ, b, ⟨hbK, hb2, hb1⟩, hbQ, ?_, ?_, hsgcl,
    (burnsideJ27_mem_conjClass_iff _ _).mpr hbz⟩, h8b, h8c, ?_⟩
  · rintro i ⟨hiK, hi2, hi1⟩ hiQ
    rcases hcl i ⟨Subgroup.mem_top _, hi2, hi1⟩ with hi | hi
    · exact Or.inl (h8b i (M.K_le_H hiK) hi)
    · right
      have hiz : IsConj M.z i := (burnsideJ27_mem_conjClass_iff _ _).mp hi
      obtain ⟨m, hm, hmi⟩ := burnsideJ27_transX M hbz hbK hbQ hiz hiK hiQ
      exact ⟨m⁻¹, inv_mem hm, by rw [← hmi]; group⟩
  · rintro ⟨h, -, hbh⟩
    apply hnz
    rw [burnsideJ27_mem_conjClass_iff]
    have h1 : IsConj (g⁻¹ * s * g) b := isConj_iff.mpr ⟨h⁻¹, by rw [hbh]; group⟩
    exact hbz.trans h1.symm
  · have hset : (conjClass M.z ∩ ((M.K : Set G) \ (ruQ M.T : Set G))) =
        {x : G | IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_diff, SetLike.mem_coe, Set.mem_setOf_eq,
        burnsideJ27_mem_conjClass_iff]
    rw [hset, ← Nat.card_coe_set_eq]
    exact hcard

end Part8

section

open CFSG.ASVolI.ChIJK in
theorem as_J_2_7 : J_2_7 := by
  intro G _ _ L V T h B B7 hB hB7L hB7 hBN z s hz hs hs1
  obtain ⟨M, g, hML, hMT, hgL, hgH, rfl, rfl⟩ :=
    burnsideJ27_reduce_H CFSG.Quasithin.RuType.stUnique h hB hB7L hB7 hBN
  subst hML
  obtain ⟨hT, hV, hZ, hH, hQ, hU⟩ := burnsideJ27_ident h M rfl hMT
  have hK := burnsideJ27_KRu_eq h M rfl hMT
  obtain rfl := burnsideJ27_z_eq h M hMT hz
  obtain ⟨s', rfl⟩ : ∃ s', s = g⁻¹ * s' * g := ⟨g * s * g⁻¹, by group⟩
  have hS0 : S0Ru M.L (CFSG.conjugate M.B7 g) = CFSG.conjugate M.S0 g :=
    burnsideJ27_S0_conjugate hgL
  have hs' : s' ∈ M.S0 := by
    rw [hS0, burnsideJ27_mem_conjugate] at hs
    have e : g * (g⁻¹ * s' * g) * g⁻¹ = s' := by group
    rw [e] at hs
    exact hs
  have hs1' : s' ≠ 1 := fun h1 => hs1 (by rw [h1]; group)
  have hgH' : g ∈ CFSG.Quasithin.RuType.ruH M.T := hH ▸ hgH
  rw [hH, hQ, hK]
  exact ⟨burnsideJ27_part1 M g, burnsideJ27_part2 M g, burnsideJ27_part3 M g,
    burnsideJ27_part4 M hs' hs1' g, burnsideJ27_part56 M g, burnsideJ27_part7 M g hs' hs1',
    burnsideJ27_part8 M hs' hs1' hgH', burnsideJ27_part9 M g,
    burnsideJ27_part10 M hs' hs1' hgL hgH', burnsideJ27_part11 M⟩

end

end CFSG.ASVolI
