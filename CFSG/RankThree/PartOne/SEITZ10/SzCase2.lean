module

public import CFSG.RankThree.PartOne.SEITZ10.SzCount
public import CFSG.RankThree.PartOne.SEITZ10.BenderTools
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.RankThree.PartOne.SEITZ10.SzBend

public section

namespace CFSG.RankThree.PartOne.SEITZ10

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Open CFSG.RankThree.PartOne.SEITZ9

variable {a : ℕ} {K : Type} [Field K] [Finite K]

@[expose] def IsUSylow {H : Subgroup (suzukiGroup a K)} (N : Subgroup ↥H) (Q : Sylow 2 ↥N) : Prop :=
  ∀ n : ↥N, n ∈ (Q : Subgroup ↥N) ↔ ((n : ↥H) : suzukiGroup a K) ∈ suzukiU a K

theorem mem_N_of_mem_U (hK : Nat.card K = 2 ^ (2 * a + 1)) {H : Subgroup (suzukiGroup a K)}
    (N : Subgroup ↥H) [N.Normal] (hN : Odd N.index) {h : ↥H}
    (hh : ((h : ↥H) : suzukiGroup a K) ∈ suzukiU a K) : h ∈ N := by
  obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one hK hh
  exact mem_of_pow_two_pow_eq_one_of_odd_index N hN ⟨n, Subtype.ext hn⟩

theorem exists_sylow_N {H : Subgroup (suzukiGroup a K)} (Sy : Sylow 2 ↥H)
    (hSy : (Sy : Subgroup ↥H) = (H ⊓ suzukiU a K).subgroupOf H) (N : Subgroup ↥H) [N.Normal]
    (hN : Odd N.index) : ∃ Q : Sylow 2 ↥N, IsUSylow N Q := by
  classical
  set S : Subgroup ↥H := (Sy : Subgroup ↥H) with hS
  have hSN : S ≤ N := by
    intro x hx
    obtain ⟨n, hn⟩ := Sy.isPGroup' ⟨x, hx⟩
    exact mem_of_pow_two_pow_eq_one_of_odd_index N hN ⟨n, congrArg Subtype.val hn⟩
  have hp : IsPGroup 2 (S.subgroupOf N) :=
    Sy.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
  have hidx : ¬ 2 ∣ (S.subgroupOf N).index := by
    intro h2
    have h1 : (S.subgroupOf N).index = S.relIndex N := rfl
    have h3 := Subgroup.relIndex_mul_index hSN
    exact Sy.not_dvd_index (h3 ▸ (h1 ▸ h2).mul_right N.index)
  refine ⟨hp.toSylow hidx, fun n => ?_⟩
  change (n ∈ S.subgroupOf N) ↔ _
  rw [Subgroup.mem_subgroupOf, hSy, Subgroup.mem_subgroupOf]
  exact ⟨fun h => h.2, fun h => ⟨(n : ↥H).2, h⟩⟩

@[expose] def toG (H : Subgroup (suzukiGroup a K)) (N : Subgroup ↥H) (Q : Subgroup ↥N) :
    ↥Q →* suzukiGroup a K :=
  (H.subtype.comp N.subtype).comp Q.subtype

omit [Finite K] in
theorem toG_injective (H : Subgroup (suzukiGroup a K)) (N : Subgroup ↥H) (Q : Subgroup ↥N) :
    Function.Injective (toG H N Q) := fun _ _ h =>
  Subtype.ext (Subtype.ext (Subtype.ext h))

omit [Finite K] in
theorem toG_mem {H : Subgroup (suzukiGroup a K)} {N : Subgroup ↥H} {Q : Sylow 2 ↥N}
    (hQ : IsUSylow N Q) (q : ↥(Q : Subgroup ↥N)) : toG H N Q q ∈ H ⊓ suzukiU a K :=
  ⟨((q : ↥N) : ↥H).2, (hQ _).1 q.2⟩

theorem exists_toG_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) {H : Subgroup (suzukiGroup a K)}
    {N : Subgroup ↥H} [N.Normal] (hN : Odd N.index) {Q : Sylow 2 ↥N} (hQ : IsUSylow N Q)
    {g : suzukiGroup a K} (hg : g ∈ H ⊓ suzukiU a K) :
    ∃ q : ↥(Q : Subgroup ↥N), toG H N Q q = g := by
  obtain ⟨hgH, hgU⟩ := hg
  have hxN : (⟨g, hgH⟩ : ↥H) ∈ N := mem_N_of_mem_U hK N hN hgU
  exact ⟨⟨⟨⟨g, hgH⟩, hxN⟩, (hQ _).2 hgU⟩, rfl⟩

theorem card_Q_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) {H : Subgroup (suzukiGroup a K)}
    {N : Subgroup ↥H} [N.Normal] (hN : Odd N.index) {Q : Sylow 2 ↥N} (hQ : IsUSylow N Q) :
    Nat.card (Q : Subgroup ↥N) = Nat.card ↥(H ⊓ suzukiU a K) := by
  refine Nat.card_congr
    (Equiv.ofBijective (fun q => ⟨toG H N Q q, toG_mem hQ q⟩) ⟨?_, ?_⟩)
  · intro x y h
    have h' := Subtype.ext_iff.1 h
    exact toG_injective H N Q h'
  · rintro ⟨g, hg⟩
    obtain ⟨q, hq⟩ := exists_toG_eq hK hN hQ hg
    exact ⟨q, Subtype.ext hq⟩

theorem center_map_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) {H : Subgroup (suzukiGroup a K)}
    {N : Subgroup ↥H} [N.Normal] (hN : Odd N.index) {Q : Sylow 2 ↥N} (hQ : IsUSylow N Q)
    (hcenter : ∀ z ∈ Subgroup.center ↥(Q : Subgroup ↥N), z ^ 2 = 1) :
    (Subgroup.center ↥(Q : Subgroup ↥N)).map (toG H N Q) =
      (H ⊓ suzukiU a K) ⊓ suzukiZ0 a K := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨toG_mem hQ c, ?_⟩
    have hsq : (toG H N Q c) ^ 2 = 1 := by rw [← map_pow, hcenter c hc, map_one]
    by_cases h1 : toG H N Q c = 1
    · rw [h1]
      exact one_mem _
    · obtain ⟨v, -, hv⟩ := CFSG.RankThree.eq_suzukiSElt_zero_of_sq_eq_one hK
        ((toG_mem hQ c).2) hsq h1
      rw [hv]
      exact (mem_suzukiZ0_iff hK).2 ⟨v, rfl⟩
  · rintro ⟨hgSG, hgZ⟩
    obtain ⟨q, hq⟩ := exists_toG_eq hK hN hQ hgSG
    refine ⟨q, ?_, hq⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro y
    apply toG_injective H N Q
    rw [map_mul, map_mul, hq]
    exact ((suzuki_unipotent_structure hK).2.2.2.2.2.1 g hgZ _ (toG_mem hQ y).2).symm

theorem card_center_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) {H : Subgroup (suzukiGroup a K)}
    {N : Subgroup ↥H} [N.Normal] (hN : Odd N.index) {Q : Sylow 2 ↥N} (hQ : IsUSylow N Q)
    (hcenter : ∀ z ∈ Subgroup.center ↥(Q : Subgroup ↥N), z ^ 2 = 1) :
    Nat.card ↥(Subgroup.center ↥(Q : Subgroup ↥N)) =
      Nat.card ↥((H ⊓ suzukiU a K) ⊓ suzukiZ0 a K) := by
  rw [← center_map_eq hK hN hQ hcenter,
    Subgroup.card_map_of_injective (toG_injective H N Q)]

theorem bender_type (hK : Nat.card K = 2 ^ (2 * a + 1)) {H : Subgroup (suzukiGroup a K)}
    {N : Subgroup ↥H} [N.Normal] (hN : Odd N.index) {Q : Sylow 2 ↥N} (hQ : IsUSylow N Q)
    (hNB : fusionIsBenderGroup ↥N) (hu1 : suzukiSElt a K 1 0 ∈ H) :
    ∃ a' : ℕ, 1 ≤ a' ∧ Nonempty (↥N ≃* Sz a') ∧
      fusionBenderBorel ↥N (2 ^ (2 * a' + 1)) 2 ∧
      Nat.card ↥((H ⊓ suzukiU a K) ⊓ suzukiZ0 a K) = 2 ^ (2 * a' + 1) := by
  classical
  have hfinN : Finite ↥N := inferInstance
  have key : ∀ q k : ℕ, fusionBenderBorel ↥N q k → 2 ≤ q →
      (k = 1 → False) ∧ k ≤ 2 ∧ Nat.card ↥((H ⊓ suzukiU a K) ⊓ suzukiZ0 a K) = q := by
    intro q k hB hq2
    obtain ⟨-, -, hz, hcardZ, hcardQ⟩ := hB Q
    have h1 := card_center_eq hK hN hQ hz
    have h2 := card_Q_eq hK hN hQ
    have h3 := card_le_sq_card_inf_Z0 hK (S := H ⊓ suzukiU a K) inf_le_right
    have hq : Nat.card ↥((H ⊓ suzukiU a K) ⊓ suzukiZ0 a K) = q := h1.symm.trans hcardZ
    refine ⟨fun hk1 => ?_, ?_, hq⟩
    · subst hk1
      have hQcard : Nat.card ↥(H ⊓ suzukiU a K) = q := by
        rw [← h2, hcardQ, pow_one]
      have hle : (H ⊓ suzukiU a K) ⊓ suzukiZ0 a K ≤ H ⊓ suzukiU a K := inf_le_left
      have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hQcard, hq])
      have hmem : suzukiSElt a K 1 0 ∈ (H ⊓ suzukiU a K) ⊓ suzukiZ0 a K := by
        rw [heq]
        exact ⟨hu1, suzukiSElt_mem_suzukiU a K 1 0⟩
      obtain ⟨v, hv⟩ := (mem_suzukiZ0_iff hK).1 hmem.2
      exact one_ne_zero (suzukiSElt_inj.1 hv).1.symm
    · by_contra hk
      have hk3 : 3 ≤ k := by omega
      have : q ^ 3 ≤ q ^ 2 := by
        calc q ^ 3 ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk3
          _ = Nat.card ↥(H ⊓ suzukiU a K) := by rw [← hcardQ, h2]
          _ ≤ Nat.card ↥((H ⊓ suzukiU a K) ⊓ suzukiZ0 a K) ^ 2 := h3
          _ = q ^ 2 := by rw [hq]
      have := Nat.pow_le_pow_iff_right (by omega : 1 < q) |>.1 this
      omega
  rcases hNB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a', ha', ⟨e⟩⟩
  · exfalso
    have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
      Finite.of_equiv _ e.toEquiv
    have hB := (bender_psl2_borel_full f hf).map_mulEquiv e.symm
    have h4 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact (key _ _ hB h4).1 rfl
  · exfalso
    have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
    have hB := (bender_psu3_borel_full f hf).map_mulEquiv e.symm
    have h4 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := (key _ _ hB h4).2.1
    omega
  · have : Finite (Sz a') := Finite.of_equiv _ e.toEquiv
    have hB := (bender_suzuki_borel_full a' ha').map_mulEquiv e.symm
    have h4 : 2 ≤ 2 ^ (2 * a' + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ⟨a', ha', ⟨e⟩, hB, (key _ _ hB h4).2.2⟩

theorem exists_central_involution (hK : Nat.card K = 2 ^ (2 * a + 1))
    {H : Subgroup (suzukiGroup a K)} {N : Subgroup ↥H} [N.Normal] (hN : Odd N.index)
    {Q : Sylow 2 ↥N} (hQ : IsUSylow N Q)
    (hcenter : ∀ z ∈ Subgroup.center ↥(Q : Subgroup ↥N), z ^ 2 = 1)
    {w : K} (hw0 : w ≠ 0) (hwH : suzukiSElt a K 0 w ∈ H) :
    ∃ z : ↥N, z ∈ (Q : Subgroup ↥N) ∧ (∀ y ∈ (Q : Subgroup ↥N), y * z = z * y) ∧
      orderOf z = 2 ∧ ((z : ↥H) : suzukiGroup a K) = suzukiSElt a K 0 w := by
  have hmem : suzukiSElt a K 0 w ∈ (H ⊓ suzukiU a K) ⊓ suzukiZ0 a K :=
    ⟨⟨hwH, suzukiSElt_mem_suzukiU a K 0 w⟩, (mem_suzukiZ0_iff hK).2 ⟨w, rfl⟩⟩
  rw [← center_map_eq hK hN hQ hcenter] at hmem
  obtain ⟨c, hc, hcw⟩ := hmem
  rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hc
  refine ⟨(c : ↥N), c.2, fun y hy => ?_, ?_, hcw⟩
  · have := hc ⟨y, hy⟩
    exact congrArg Subtype.val this
  · have h1 : orderOf ((c : ↥N) : ↥H) = orderOf (c : ↥N) := Subgroup.orderOf_coe _
    have h2 : orderOf (((c : ↥N) : ↥H) : suzukiGroup a K) = orderOf ((c : ↥N) : ↥H) :=
      Subgroup.orderOf_coe _
    rw [← h1, ← h2]
    change orderOf (toG H N Q c) = 2
    rw [hcw]
    exact CFSG.ShultStronglyClosedTI.SuzukiModel.orderOf_suzukiSElt_zero hK hw0

theorem mem_of_Z0_mem_case2 (hK : Nat.card K = 2 ^ (2 * a + 1)) {k : Subfield K}
    {H : Subgroup (suzukiGroup a K)} {N : Subgroup ↥H} [N.Normal] (hN : Odd N.index)
    {Q : Sylow 2 ↥N} (hQ : IsUSylow N Q) (hW : suzukiWElt a K ∈ H) (hz : suzukiSElt a K 0 1 ∈ H)
    (hQs : fusionStronglyEmbedded (Subgroup.normalizer ((Q : Subgroup ↥N) : Set ↥N)))
    (hcenter : ∀ z ∈ Subgroup.center ↥(Q : Subgroup ↥N), z ^ 2 = 1)
    (hcase : ∀ g : suzukiB a K, (g : suzukiGroup a K) ∈ H →
      ((torusPart hK g : Kˣ) : K) ∈ k)
    {w : K} (hwH : suzukiSElt a K 0 w ∈ H) : w ∈ k := by
  classical
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  by_cases hw0 : w = 0
  · rw [hw0]
    exact k.zero_mem
  obtain ⟨z', hz'Q, -, hz'2, hz'G⟩ := exists_central_involution hK hN hQ hcenter hw0 hwH
  obtain ⟨z0, -, hz0c, hz02, hz0G⟩ :=
    exists_central_involution hK hN hQ hcenter one_ne_zero hz
  obtain ⟨n, hn, hnz⟩ := exists_mem_normalizer_conj_of_central_involutions Q hQs hz'Q hz02 hz'2 hz0c
  set M : Subgroup ↥H := (H ⊓ suzukiB a K).subgroupOf H with hMdef
  set S : Subgroup ↥H := (H ⊓ suzukiU a K).subgroupOf H with hSdef
  have hSM : S ≤ M := fun x hx => ⟨hx.1, suzukiU_le_suzukiB a K hx.2⟩
  have hSeven : Even (Nat.card S) := by
    have hmem : (⟨suzukiSElt a K 0 1, hz⟩ : ↥H) ∈ S :=
      ⟨hz, suzukiSElt_mem_suzukiU a K 0 1⟩
    have hdvd := Subgroup.orderOf_dvd_natCard S hmem
    rw [Subgroup.orderOf_mk,
      CFSG.ShultStronglyClosedTI.SuzukiModel.orderOf_suzukiSElt_zero hK one_ne_zero] at hdvd
    exact even_iff_two_dvd.2 hdvd
  have hMn := fusionStronglyEmbedded_toHelpers (inf_stronglyEmbedded hK hW hz)
  have hnorm :=
    CFSG.DisconnectedInvolutionGraph.Helpers.stronglyEmbedded_even_subgroup_normalizer_le
      M hMn S hSM hSeven
  have hnS : ((n : ↥N) : ↥H) ∈ Subgroup.normalizer (S : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhN : h ∈ N := mem_N_of_mem_U hK N hN hh.2
      have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨h, hhN⟩).1 ((hQ _).2 hh.2)
      exact ⟨(((n : ↥N) : ↥H) * h * ((n : ↥N) : ↥H)⁻¹).2, (hQ _).1 h1⟩
    · intro hh
      have hnhn : (n : ↥H) * h * (n : ↥H)⁻¹ ∈ N := mem_N_of_mem_U hK N hN hh.2
      have hhN : h ∈ N := by
        have := N.mul_mem (N.mul_mem (N.inv_mem n.2) hnhn) n.2
        simpa [mul_assoc] using this
      have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨h, hhN⟩).2 ((hQ _).2 hh.2)
      exact ⟨h.2, (hQ _).1 h1⟩
  have hnM : ((n : ↥N) : ↥H) ∈ M := hnorm hnS
  have hnB : (((n : ↥N) : ↥H) : suzukiGroup a K) ∈ suzukiB a K := hnM.2
  have hnH : (((n : ↥N) : ↥H) : suzukiGroup a K) ∈ H := ((n : ↥N) : ↥H).2
  have hχ := hcase ⟨_, hnB⟩ hnH
  have hconj := conj_suzukiSElt_zero hK ⟨_, hnB⟩ 1
  have hG : (((n : ↥N) : ↥H) : suzukiGroup a K) * suzukiSElt a K 0 1 *
      (((n : ↥N) : ↥H) : suzukiGroup a K)⁻¹ = suzukiSElt a K 0 w := by
    rw [← hz'G, ← hnz, ← hz0G]
    simp
  rw [hconj, suzukiSElt_inj] at hG
  have hw : w = ((((torusPart hK ⟨_, hnB⟩)⁻¹ : Kˣ) : K)) ^ (2 ^ (a + 1) + 1) * 1 := hG.2.symm
  rw [hw, mul_one]
  refine k.pow_mem ?_ _
  rw [Units.val_inv_eq_inv_val]
  exact k.inv_mem hχ

theorem bender_case2 {b : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1)) {k : Subfield K}
    (hk : Nat.card k = 2 ^ (2 * b + 1)) (hb : 1 ≤ b) {H : Subgroup (suzukiGroup a K)}
    (hS : ∀ u ∈ k, ∀ v ∈ k, suzukiSElt a K u v ∈ H) (hW : suzukiWElt a K ∈ H)
    (hcase : ∀ g : suzukiB a K, (g : suzukiGroup a K) ∈ H →
      ((torusPart hK g : Kˣ) : K) ∈ k) :
    ∃ N : Subgroup ↥H, N.Normal ∧ Odd N.index ∧
      Nat.card N = Nat.card k ^ 2 * (Nat.card k ^ 2 + 1) * (Nat.card k - 1) := by
  classical
  have hfin : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  obtain ⟨v, hvk, hv0, hv1⟩ : ∃ v ∈ k, v ≠ 0 ∧ v ≠ 1 := by
    by_contra hcon
    have hall : ∀ v ∈ k, v ≠ 0 → v = 1 := by
      intro v hv hv0
      by_contra hv1
      exact hcon ⟨v, hv, hv0, hv1⟩
    have hsub : (k : Set K) ⊆ {0, 1} := by
      intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · simp [hall x hx hx0]
    have h1 : Nat.card k ≤ 2 := by
      have h := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_pair zero_ne_one] at h
      have h' : Nat.card (k : Set K) = Set.ncard (k : Set K) := Nat.card_coe_set_eq _
      exact h'.symm ▸ h
    have h2 : 8 ≤ 2 ^ (2 * b + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hk] at h1
    omega
  have hz : suzukiSElt a K 0 1 ∈ H := hS 0 k.zero_mem 1 k.one_mem
  have hzv : suzukiSElt a K 0 v ∈ H := hS 0 k.zero_mem v hvk
  have hu1 : suzukiSElt a K 1 0 ∈ H := hS 1 k.one_mem 0 k.zero_mem
  obtain ⟨N, hNn, hNo, hNB⟩ := exists_bender_normal hK hv0 hv1 hW hz hzv
  obtain ⟨Sy, hSy⟩ := exists_sylow_inf_U hK hW hz
  obtain ⟨Q, hQ⟩ := exists_sylow_N Sy hSy N hNo
  obtain ⟨a', ha', ⟨e⟩, hB, hcardZ⟩ := bender_type hK hNo hQ hNB hu1
  have hQs := (hB Q).1
  have hcenter := (hB Q).2.2.1
  have hZk : ∀ w : K, suzukiSElt a K 0 w ∈ H → w ∈ k := fun w hw =>
    mem_of_Z0_mem_case2 hK hNo hQ hW hz hQs hcenter hcase hw
  have hle1 : Nat.card k ≤ Nat.card ↥((H ⊓ suzukiU a K) ⊓ suzukiZ0 a K) := by
    refine Nat.card_le_card_of_injective
      (fun z : k => (⟨suzukiSElt a K 0 z, ⟨⟨hS 0 k.zero_mem z z.2,
        suzukiSElt_mem_suzukiU a K 0 z⟩, (mem_suzukiZ0_iff hK).2 ⟨z, rfl⟩⟩⟩ :
          ↥((H ⊓ suzukiU a K) ⊓ suzukiZ0 a K))) ?_
    intro x y hxy
    exact Subtype.ext (suzukiSElt_inj.1 (congrArg Subtype.val hxy)).2
  have hle2 : Nat.card ↥((H ⊓ suzukiU a K) ⊓ suzukiZ0 a K) ≤ Nat.card k := by
    have hv : ∀ g : ↥((H ⊓ suzukiU a K) ⊓ suzukiZ0 a K),
        ∃ w : K, suzukiSElt a K 0 w = g := fun g => (mem_suzukiZ0_iff hK).1 g.2.2
    refine Nat.card_le_card_of_injective
      (fun g => (⟨Classical.choose (hv g), hZk _ ?_⟩ : k)) ?_
    · rw [Classical.choose_spec (hv g)]
      exact g.2.1.1
    · intro g g' hgg'
      have h1 : Classical.choose (hv g) = Classical.choose (hv g') := congrArg Subtype.val hgg'
      apply Subtype.ext
      rw [← Classical.choose_spec (hv g), ← Classical.choose_spec (hv g'), h1]
  have hqk : 2 ^ (2 * a' + 1) = Nat.card k := hcardZ.symm.trans (le_antisymm hle2 hle1)
  refine ⟨N, hNn, hNo, ?_⟩
  rw [Nat.card_congr e.toEquiv, CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz a',
    hqk]

end CFSG.RankThree.PartOne.SEITZ10
