module

public import CFSG.RankThree.PartOne.SEITZ10.SzBorel
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.Dihedral.DisconnectedInvolutionGraph.StrongEmbeddingSylow
public import CFSG.Dihedral.BrauerSuzuki.Helpers

public section

namespace CFSG.RankThree.PartOne.SEITZ10

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Open

section General

theorem stronglyEmbedded_inf_subgroupOf {Y : Type*} [Group Y] [Finite Y] {B H : Subgroup Y}
    (hB : fusionStronglyEmbedded B) (hHB : ¬ H ≤ B) (hev : ∃ u ∈ H ⊓ B, orderOf u = 2) :
    fusionStronglyEmbedded ((H ⊓ B).subgroupOf H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hHB (htop.trans inf_le_right)
  · obtain ⟨u, hu, hu2⟩ := hev
    have hmem : (⟨u, hu.1⟩ : H) ∈ (H ⊓ B).subgroupOf H := hu
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [Subgroup.orderOf_mk, hu2] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  · intro g hg
    have hgB : (g : Y) ∉ B := fun hgB => hg ⟨g.2, hgB⟩
    have hodd := hB.2.2 (g : Y) hgB
    have hle : ((((H ⊓ B).subgroupOf H) ⊓
        ((H ⊓ B).subgroupOf H).map (MulAut.conj g⁻¹).toMonoidHom).map H.subtype) ≤
        B ⊓ B.map (MulAut.conj (g : Y)⁻¹).toMonoidHom := by
      rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨hy1.2, ?_⟩
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy2
      refine Subgroup.mem_map.mpr ⟨(z : Y), hz.2, ?_⟩
      simp
    have hdvd : Nat.card ↥(((H ⊓ B).subgroupOf H ⊓
        ((H ⊓ B).subgroupOf H).map (MulAut.conj g⁻¹).toMonoidHom).map H.subtype) ∣
        Nat.card ↥(B ⊓ B.map (MulAut.conj (g : Y)⁻¹).toMonoidHom) :=
      Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective H.subtype_injective] at hdvd
    exact hodd.of_dvd_nat hdvd

theorem fusionStronglyEmbedded_toHelpers {X : Type*} [Group X] {M : Subgroup X}
    (hM : fusionStronglyEmbedded M) :
    CFSG.DisconnectedInvolutionGraph.Helpers.IsStronglyEmbedded M := by
  refine ⟨hM.1, hM.2.1, fun g hg => ?_⟩
  have h := hM.2.2 g⁻¹ (by simpa using hg)
  have e : CFSG.DisconnectedInvolutionGraph.Helpers.conjugateSubgroup M g =
      M.map (MulAut.conj g⁻¹⁻¹).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      have hx0 : (MulAut.conj g⁻¹).toMonoidHom x ∈ M := hx
      have hx' : g⁻¹ * x * g ∈ M := by simpa [MulAut.conj_apply] using hx0
      refine ⟨g⁻¹ * x * g, hx', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    · rintro ⟨y, hy, rfl⟩
      have h1 : (MulAut.conj g⁻¹) ((MulAut.conj g⁻¹⁻¹) y) = y := by
        simp [MulAut.conj_apply]
        group
      show (MulAut.conj g⁻¹) ((MulAut.conj g⁻¹⁻¹) y) ∈ M
      rw [h1]
      exact hy
  rw [e]
  exact h

theorem eq_of_orderOf_two_of_isCyclic {A : Type*} [Group A] [Finite A] [IsCyclic A] {x y : A}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have hd : 2 ∣ Fintype.card A := hx ▸ orderOf_dvd_card
  have hcard := IsCyclic.card_orderOf_eq_totient hd
  rw [Nat.totient_two] at hcard
  exact Finset.card_le_one.1 hcard.le x (by simp [hx]) y (by simp [hy])

theorem conj_eq_inv_of_fixed_point_free {X : Type*} [Group X] (M : Subgroup X) [M.Normal]
    [Finite M] (w : X) (hw : w * w = 1) (hfix : ∀ m ∈ M, w * m * w⁻¹ = m → m = 1) :
    ∀ m ∈ M, w * m * w⁻¹ = m⁻¹ := by
  classical
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  let ψ : M → M := fun m => ⟨(m : X)⁻¹ * (w * m * w⁻¹),
    mul_mem (inv_mem m.2) (Subgroup.Normal.conj_mem inferInstance _ m.2 w)⟩
  have hψ : Function.Injective ψ := by
    intro m m' h
    have h' : (m : X)⁻¹ * (w * m * w⁻¹) = (m' : X)⁻¹ * (w * m' * w⁻¹) := congrArg Subtype.val h
    have hB : w * (m' : X) * w⁻¹ = m' * ((m : X)⁻¹ * (w * m * w⁻¹)) :=
      inv_mul_eq_iff_eq_mul.1 h'.symm
    have hd : w * ((m' : X) * (m : X)⁻¹) * w⁻¹ = (m' : X) * (m : X)⁻¹ := by
      calc w * ((m' : X) * (m : X)⁻¹) * w⁻¹
          = (w * (m' : X) * w⁻¹) * (w * (m : X) * w⁻¹)⁻¹ := by group
        _ = (m' : X) * ((m : X)⁻¹ * (w * m * w⁻¹)) * (w * (m : X) * w⁻¹)⁻¹ := by rw [hB]
        _ = (m' : X) * (m : X)⁻¹ := by group
    have h1 : (m' : X) * (m : X)⁻¹ = 1 := hfix _ (mul_mem m'.2 (inv_mem m.2)) hd
    exact (Subtype.ext (mul_inv_eq_one.1 h1)).symm
  have hsurj := Finite.injective_iff_surjective.1 hψ
  intro m hm
  obtain ⟨⟨n, hn⟩, hnm⟩ := hsurj ⟨m, hm⟩
  have hn' : (n : X)⁻¹ * (w * n * w⁻¹) = m := congrArg Subtype.val hnm
  rw [← hn']
  rw [hw']
  simp only [mul_inv_rev, inv_inv, mul_assoc, hw', hw, mul_one]

theorem eq_one_of_pow_two_pow_eq_one_of_odd {X : Type*} [Group X] (M : Subgroup X)
    (hM : Odd (Nat.card M)) {m : X} (hm : m ∈ M) (hn : ∃ n : ℕ, m ^ 2 ^ n = 1) : m = 1 := by
  obtain ⟨n, hn⟩ := hn
  have h1 : orderOf m ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf m ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M hm
  have hcop : Nat.Coprime (2 ^ n) (Nat.card M) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hM)
  exact orderOf_eq_one_iff.1 ((hcop.coprime_dvd_left h1).eq_one_of_dvd h2)

theorem fusionIsBenderGroup_of_mulEquiv {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (h : fusionIsBenderGroup K) : fusionIsBenderGroup L := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans e'⟩⟩)

end General

section Suzuki

variable {a : ℕ} {K : Type} [Field K] [Finite K]

variable (hK : Nat.card K = 2 ^ (2 * a + 1)) {H : Subgroup (suzukiGroup a K)}

include hK

theorem inf_stronglyEmbedded (hW : suzukiWElt a K ∈ H) (hz : suzukiSElt a K 0 1 ∈ H) :
    fusionStronglyEmbedded ((H ⊓ suzukiB a K).subgroupOf H) := by
  have hHB : ¬ H ≤ suzukiB a K := by
    intro hle
    have h1 : suzukiWElt a K ∈ MulAction.stabilizer (suzukiGroup a K) (suzukiInfty K) := by
      rw [(suzuki_ovoid_stabilizer hK).1]
      exact hle hW
    rw [MulAction.mem_stabilizer_iff,
      CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiWElt_smul_suzukiInfty hK] at h1
    exact suzukiLine_ne_suzukiInfty 0 0 h1
  have hev : ∃ u ∈ H ⊓ suzukiB a K, orderOf u = 2 :=
    ⟨suzukiSElt a K 0 1, ⟨hz, suzukiU_le_suzukiB a K (suzukiSElt_mem_suzukiU a K 0 1)⟩,
      CFSG.ShultStronglyClosedTI.SuzukiModel.orderOf_suzukiSElt_zero hK one_ne_zero⟩
  exact stronglyEmbedded_inf_subgroupOf
    (CFSG.ShultStronglyClosedTI.SuzukiModel.fusionStronglyEmbedded_suzukiB hK) hHB hev

theorem exists_pow_two_pow_eq_one {g : suzukiGroup a K} (hg : g ∈ suzukiU a K) :
    ∃ n : ℕ, g ^ 2 ^ n = 1 := by
  obtain ⟨hcard, -⟩ : Nat.card (suzukiU a K) = (2 ^ (2 * a + 1)) ^ 2 ∧ True :=
    ⟨(suzuki_unipotent_structure hK).2.1, trivial⟩
  have hp : IsPGroup 2 (suzukiU a K) := by
    refine IsPGroup.of_card (n := (2 * a + 1) * 2) ?_
    rw [hcard, ← pow_mul]
  obtain ⟨n, hn⟩ := hp ⟨g, hg⟩
  exact ⟨n, congrArg Subtype.val hn⟩

theorem exists_sylow_inf_U (hW : suzukiWElt a K ∈ H) (hz : suzukiSElt a K 0 1 ∈ H) :
    ∃ S : Sylow 2 ↥H, (S : Subgroup ↥H) = (H ⊓ suzukiU a K).subgroupOf H := by
  classical
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  have hSE := inf_stronglyEmbedded hK hW hz
  set M : Subgroup ↥H := (H ⊓ suzukiB a K).subgroupOf H with hM
  set S' : Subgroup ↥H := (H ⊓ suzukiU a K).subgroupOf H with hS'
  have hS'M : S' ≤ M := fun x hx => ⟨hx.1, suzukiU_le_suzukiB a K hx.2⟩
  have hS'p : IsPGroup 2 S' := by
    intro x
    obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one hK x.2.2
    exact ⟨n, Subtype.ext (Subtype.ext hn)⟩
  have hSMp : IsPGroup 2 (S'.subgroupOf M) :=
    hS'p.of_equiv (Subgroup.subgroupOfEquivOfLe hS'M).symm
  obtain ⟨T0, hT0⟩ := hSMp.exists_le_sylow
  obtain ⟨amb, hamb⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.stronglyEmbedded_sylow_inheritance
      M (fusionStronglyEmbedded_toHelpers hSE) T0
  refine ⟨amb, le_antisymm ?_ ?_⟩
  · intro y hy
    have hyM : y ∈ M := by
      rw [← hamb] at hy
      obtain ⟨m, -, rfl⟩ := hy
      exact m.2
    obtain ⟨n, hn⟩ := amb.isPGroup' ⟨y, hy⟩
    have hpow : (y : suzukiGroup a K) ^ 2 ^ n = 1 :=
      congrArg (fun z : ↥H => (z : suzukiGroup a K)) (congrArg Subtype.val hn)
    exact ⟨y.2, mem_suzukiU_of_pow_two hK hyM.2 hpow⟩
  · intro x hx
    rw [← hamb]
    exact ⟨⟨x, hS'M hx⟩, hT0 hx, rfl⟩

section Bender


theorem exists_bender_section {v : K} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (hW : suzukiWElt a K ∈ H) (hz : suzukiSElt a K 0 1 ∈ H) (hzv : suzukiSElt a K 0 v ∈ H) :
    ∃ (M N : Subgroup ↥H) (_ : M.Normal) (_ : N.Normal) (_ : (M.subgroupOf N).Normal),
      M ≤ N ∧ Odd (Nat.card M) ∧ Odd N.index ∧ fusionIsBenderGroup (N ⧸ M.subgroupOf N) := by
  classical
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  obtain ⟨S, hS⟩ := exists_sylow_inf_U hK hW hz
  have hSE := inf_stronglyEmbedded hK hW hz
  rcases bender_strongly_embedded_normal_series ↥H _ hSE with hlow | hnorm
  · exfalso
    let z : ↥H := ⟨suzukiSElt a K 0 1, hz⟩
    let z' : ↥H := ⟨suzukiSElt a K 0 v, hzv⟩
    have hzS : z ∈ (S : Subgroup ↥H) := by
      rw [hS]
      exact ⟨hz, suzukiSElt_mem_suzukiU a K 0 1⟩
    have hz'S : z' ∈ (S : Subgroup ↥H) := by
      rw [hS]
      exact ⟨hzv, suzukiSElt_mem_suzukiU a K 0 v⟩
    have hz2 : orderOf z = 2 := by
      rw [Subgroup.orderOf_mk]
      exact CFSG.ShultStronglyClosedTI.SuzukiModel.orderOf_suzukiSElt_zero hK one_ne_zero
    have hz'2 : orderOf z' = 2 := by
      rw [Subgroup.orderOf_mk]
      exact CFSG.ShultStronglyClosedTI.SuzukiModel.orderOf_suzukiSElt_zero hK hv0
    have hne : z ≠ z' := fun h => hv1 (suzukiSElt_inj.1 (congrArg Subtype.val h)).2.symm
    rcases hlow S with hcyc | ⟨r, -, ⟨e⟩⟩
    · have hz2S : orderOf (⟨z, hzS⟩ : (S : Subgroup ↥H)) = 2 := by
        rw [Subgroup.orderOf_mk, hz2]
      have hz'2S : orderOf (⟨z', hz'S⟩ : (S : Subgroup ↥H)) = 2 := by
        rw [Subgroup.orderOf_mk, hz'2]
      have := eq_of_orderOf_two_of_isCyclic hz2S hz'2S
      exact hne (congrArg Subtype.val this)
    · exact hne (CFSG.BrauerSuzuki.Helpers.unique_order_two_in_quaternion_sylow r S ⟨e⟩ hzS hz'S
        hz2 hz'2)
  · exact hnorm

end Bender

theorem bender_M_eq_bot {v : K} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (hz : suzukiSElt a K 0 1 ∈ H) (hzv : suzukiSElt a K 0 v ∈ H)
    (M : Subgroup ↥H) [M.Normal] (hM : Odd (Nat.card M)) : M = ⊥ := by
  classical
  have hfin : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  have hchar : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  have hMU : ∀ m ∈ M, ((m : ↥H) : suzukiGroup a K) ∈ suzukiU a K → m = 1 := by
    intro m hm hmU
    refine eq_one_of_pow_two_pow_eq_one_of_odd M hM hm ?_
    obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one hK hmU
    exact ⟨n, Subtype.ext hn⟩
  have hinv : ∀ t : K, t ≠ 0 → ∀ ht : suzukiSElt a K 0 t ∈ H,
      ∀ m ∈ M, (⟨suzukiSElt a K 0 t, ht⟩ : ↥H) * m * (⟨suzukiSElt a K 0 t, ht⟩ : ↥H)⁻¹ = m⁻¹ := by
    intro t ht0 ht
    have hord := CFSG.ShultStronglyClosedTI.SuzukiModel.orderOf_suzukiSElt_zero hK ht0
    have hsq : suzukiSElt a K 0 t ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    have hne1 : suzukiSElt a K 0 t ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
    have hcent := CFSG.RankThree.centralizer_eq_suzukiU hK (suzukiSElt_mem_suzukiU a K 0 t) hsq
      hne1
    refine conj_eq_inv_of_fixed_point_free M _ ?_ ?_
    · apply Subtype.ext
      change suzukiSElt a K 0 t * suzukiSElt a K 0 t = 1
      rw [← pow_two, hsq]
    · intro m hm hfix
      apply hMU m hm
      rw [← hcent, Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have h1 : (⟨suzukiSElt a K 0 t, ht⟩ : ↥H) * m = m * ⟨suzukiSElt a K 0 t, ht⟩ := by
        rw [mul_inv_eq_iff_eq_mul] at hfix
        exact hfix
      exact congrArg Subtype.val h1
  have h1 := hinv 1 one_ne_zero hz
  have h2 := hinv v hv0 hzv
  have hsum : suzukiSElt a K 0 1 * suzukiSElt a K 0 v = suzukiSElt a K 0 (1 + v) := by
    rw [suzukiSElt_mul hK]
    have : (2 : ℕ) ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
    simp [zero_pow this]
  have hv1' : (1 : K) + v ≠ 0 := by
    intro h0
    apply hv1
    have : v = -1 := eq_neg_of_add_eq_zero_right h0
    rw [this, CharTwo.neg_eq]
  have hord := CFSG.ShultStronglyClosedTI.SuzukiModel.orderOf_suzukiSElt_zero hK hv1'
  have hsq : suzukiSElt a K 0 (1 + v) ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hne1 : suzukiSElt a K 0 (1 + v) ≠ 1 := by
    intro h1'
    rw [h1', orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hcent := CFSG.RankThree.centralizer_eq_suzukiU hK (suzukiSElt_mem_suzukiU a K 0 (1 + v))
    hsq hne1
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_bot]
  apply hMU m hm
  rw [← hcent, Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  set w1 : ↥H := ⟨suzukiSElt a K 0 1, hz⟩
  set w2 : ↥H := ⟨suzukiSElt a K 0 v, hzv⟩
  have hcomm : w1 * w2 * m * (w1 * w2)⁻¹ = m := by
    have e : w1 * w2 * m * (w1 * w2)⁻¹ = w1 * (w2 * m * w2⁻¹) * w1⁻¹ := by group
    rw [e, h2 m hm]
    have : w1 * m⁻¹ * w1⁻¹ = (w1 * m * w1⁻¹)⁻¹ := by group
    rw [this, h1 m hm, inv_inv]
  have h3 : w1 * w2 * m = m * (w1 * w2) := by
    rw [mul_inv_eq_iff_eq_mul] at hcomm
    exact hcomm
  have h4 := congrArg Subtype.val h3
  change suzukiSElt a K 0 1 * suzukiSElt a K 0 v * (m : suzukiGroup a K) =
    (m : suzukiGroup a K) * (suzukiSElt a K 0 1 * suzukiSElt a K 0 v) at h4
  rw [hsum] at h4
  exact h4

theorem exists_bender_normal {v : K} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (hW : suzukiWElt a K ∈ H) (hz : suzukiSElt a K 0 1 ∈ H) (hzv : suzukiSElt a K 0 v ∈ H) :
    ∃ N : Subgroup ↥H, N.Normal ∧ Odd N.index ∧ fusionIsBenderGroup ↥N := by
  obtain ⟨M, N, hMn, hNn, hMN', hMN, hMo, hNo, hB⟩ := exists_bender_section hK hv0 hv1 hW hz hzv
  have hM : M = ⊥ := bender_M_eq_bot hK hv0 hv1 hz hzv M hMo
  subst hM
  refine ⟨N, hNn, hNo, ?_⟩
  refine fusionIsBenderGroup_of_mulEquiv ?_ hB
  exact (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf N)).trans
    (QuotientGroup.quotientBot)

end Suzuki

end CFSG.RankThree.PartOne.SEITZ10
