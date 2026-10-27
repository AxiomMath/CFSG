module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.GL42SevenOrbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.Sporadic.He.Setup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GL42Seven

open Subgroup MulAction CFSG.Quasithin

variable {U : Type} [CommGroup U] [Finite U]

omit [Finite U] in
private lemma exists_ne_one_and_eq_pair_of_card_eq_two {F : Subgroup U} (hF : Nat.card F = 2) :
    ∃ f : U, f ∈ F ∧ f ≠ 1 ∧ (F : Set U) = {1, f} := by
  rw [Nat.card_eq_two_iff' (1 : F)] at hF
  obtain ⟨y, hyne, hyuniq⟩ := hF
  refine ⟨(y : U), y.2, fun h => hyne (Subtype.ext h), ?_⟩
  ext u
  constructor
  · intro hu
    by_cases h : (⟨u, hu⟩ : F) = 1
    · left; exact congrArg Subtype.val h
    · right
      have := hyuniq ⟨u, hu⟩ h
      exact congrArg Subtype.val this
  · rintro (rfl | rfl)
    · exact F.one_mem
    · exact y.2

omit [Finite U] in
private lemma orbit_smul_mem {M : Subgroup (MulAut U)} {v : U} {x : MulAut U} (hx : x ∈ M)
    {w : U} (hw : w ∈ orbit M v) : x • w ∈ orbit M v := by
  obtain ⟨y, rfl⟩ := MulAction.mem_orbit_iff.mp hw
  refine MulAction.mem_orbit_iff.mpr ⟨⟨x * (y : MulAut U), M.mul_mem hx y.2⟩, ?_⟩
  rw [Subgroup.smul_def, Subgroup.smul_def, mul_smul]

omit [Finite U] in
private lemma exists_avoid_three {V : Subgroup U} (hV : Nat.card V = 8) {a : U} :
    ∃ b : U, b ∈ V ∧ b ≠ 1 ∧ b ≠ a ∧ b ≠ a⁻¹ := by
  have hbex : ∃ b : U, b ∈ V ∧ b ∉ ({1, a, a⁻¹} : Set U) := by
    by_contra h
    push Not at h
    have hsub : (V : Set U) ⊆ ({1, a, a⁻¹} : Set U) := fun b hb => h b hb
    have hpair : ({a, a⁻¹} : Set U).ncard ≤ 2 := by
      have := Set.ncard_insert_le a ({a⁻¹} : Set U)
      rw [Set.ncard_singleton] at this
      simpa using this
    have h3 : ({1, a, a⁻¹} : Set U).ncard ≤ 3 := by
      have h1 := Set.ncard_insert_le (1 : U) ({a, a⁻¹} : Set U)
      have h2 := Set.ncard_insert_le a ({a⁻¹} : Set U)
      rw [Set.ncard_singleton] at h2
      omega
    have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans h3
    rw [← Nat.card_coe_set_eq] at this
    change Nat.card V ≤ 3 at this
    rw [hV] at this
    omega
  obtain ⟨b, hbV, hbS⟩ := hbex
  exact ⟨b, hbV, fun h => hbS (by simp [h]), fun h => hbS (by simp [h]),
    fun h => hbS (by simp [h])⟩

omit [Finite U] in
private lemma smul_mem_of_orbit_eq {M : Subgroup (MulAut U)} {V : Subgroup U} {v₁ : U}
    (hV : Nat.card V = 8) (hv₁V : v₁ ∉ V) {O : Set U}
    (hO : O = {v₁} ∪ ((V : Set U) \ {1}))
    (hOinv : ∀ x : ↥M, ∀ u ∈ O, x • u ∈ O)
    {x : MulAut U} (hx : x ∈ M) {a : U} (ha : a ∈ V) : x • a ∈ V := by
  classical
  by_cases ha1 : a = 1
  · rw [ha1, MulAut.smul_def, map_one]
    exact V.one_mem
  have haO : a ∈ O := by
    rw [hO]
    exact Or.inr ⟨ha, ha1⟩
  by_contra hxaV
  have hxaO : x • a ∈ O := hOinv ⟨x, hx⟩ a haO
  have hxa_v : x • a = v₁ := by
    rcases (hO ▸ hxaO) with h | h
    · exact h
    · exact absurd h.1 hxaV
  obtain ⟨b, hbV, hb1, hba, hbinv⟩ := exists_avoid_three hV
  have hbO : b ∈ O := by rw [hO]; exact Or.inr ⟨hbV, hb1⟩
  have habO : a * b ∈ O := by
    rw [hO]
    exact Or.inr ⟨V.mul_mem ha hbV, fun h => hbinv (mul_eq_one_iff_eq_inv'.mp h)⟩
  have hxbO : x • b ∈ O := hOinv ⟨x, hx⟩ b hbO
  have hxabO : x • (a * b) ∈ O := hOinv ⟨x, hx⟩ (a * b) habO
  have hxb_ne : x • b ≠ v₁ := by
    intro h
    have hba' : b = a := by
      rw [MulAut.smul_def] at h hxa_v
      exact x.injective (h.trans hxa_v.symm)
    exact hba hba'
  have hxbV : x • b ∈ V := by
    rcases (hO ▸ hxbO) with h | h
    · exact absurd h hxb_ne
    · exact h.1
  have hxb1 : x • b ≠ 1 := by
    intro h
    rw [MulAut.smul_def] at h
    exact hb1 ((MulEquiv.map_eq_one_iff x).mp h)
  have hxab_eq : x • (a * b) = x • a * x • b := by
    rw [MulAut.smul_def, MulAut.smul_def, MulAut.smul_def]
    exact map_mul x a b
  have hxab_ne : x • (a * b) ≠ v₁ := by
    rw [hxab_eq, hxa_v]
    intro h
    apply hxb1
    have : v₁ * (x • b) = v₁ * 1 := by rw [mul_one, h]
    exact mul_left_cancel this
  have hxabV : x • (a * b) ∉ V := by
    rw [hxab_eq, hxa_v]
    intro h
    have hmemV : v₁ * (x • b) * (x • b)⁻¹ ∈ V := V.mul_mem h (V.inv_mem hxbV)
    rw [mul_assoc, mul_inv_cancel, mul_one] at hmemV
    exact hv₁V hmemV
  rcases (hO ▸ hxabO) with h | h
  · exact hxab_ne h
  · exact hxabV h.1

omit [Finite U] in
private lemma smul_mem_of_orbit_eq_compl {M : Subgroup (MulAut U)} {V : Subgroup U}
    {O : Set U} (hO : O = (V : Set U)ᶜ)
    (hOinv : ∀ x : ↥M, ∀ u ∈ O, x • u ∈ O)
    {x : MulAut U} (hx : x ∈ M) {a : U} (ha : a ∈ V) : x • a ∈ V := by
  by_contra hxaV
  have hxaO : x • a ∈ O := by rw [hO]; exact hxaV
  have h := hOinv ⟨x⁻¹, M.inv_mem hx⟩ (x • a) hxaO
  rw [Subgroup.smul_def, inv_smul_smul] at h
  exact (hO ▸ h) ha

private lemma orbit_card_eight_case_zero (h16 : Nat.card U = 16) {M : Subgroup (MulAut U)}
    {V : Subgroup U} (hV : Nat.card V = 8) {v₁ : U}
    (hOinv : ∀ x : ↥M, ∀ u ∈ orbit M v₁, x • u ∈ orbit M v₁)
    (hO8 : (orbit M v₁).ncard = 8)
    (hOVempty : orbit M v₁ ∩ (V : Set U) = ∅) (hMV : ¬ StableUnder M V) : False := by
  have hOsub : orbit M v₁ ⊆ (V : Set U)ᶜ := by
    intro u hu huV
    have hmem : u ∈ (∅ : Set U) := by
      rw [← hOVempty]
      exact ⟨hu, huV⟩
    exact hmem
  have hcomplcard : ((V : Set U)ᶜ).ncard = 8 := by
    rw [Set.ncard_compl, h16, ← Nat.card_coe_set_eq]
    change 16 - Nat.card V = 8
    rw [hV]
  have hOcompl : orbit M v₁ = (V : Set U)ᶜ :=
    Set.eq_of_subset_of_ncard_le hOsub (by rw [hcomplcard, hO8])
  exact hMV fun x hx a ha => smul_mem_of_orbit_eq_compl hOcompl hOinv hx ha

private lemma orbit_card_eight_case_seven {M : Subgroup (MulAut U)} {V : Subgroup U}
    {v₁ : U} (hV : Nat.card V = 8)
    (hOinv : ∀ x : ↥M, ∀ u ∈ orbit M v₁, x • u ∈ orbit M v₁)
    (hO8 : (orbit M v₁).ncard = 8)
    (hv₁V : v₁ ∉ V)
    (hOVeq : orbit M v₁ ∩ (V : Set U) = (V : Set U) \ {1})
    (hMV : ¬ StableUnder M V) : False := by
  have hv₁O : v₁ ∈ orbit M v₁ := mem_orbit_self v₁
  have hVdiff : ((V : Set U) \ {1}).ncard = 7 := by
    rw [Set.ncard_diff (Set.singleton_subset_iff.mpr V.one_mem), Set.ncard_singleton,
      ← Nat.card_coe_set_eq]
    change Nat.card V - 1 = 7
    rw [hV]
  have h7 : (orbit M v₁ ∩ (V : Set U)).ncard = 7 := by
    rw [hOVeq, hVdiff]
  have hVdiffO : ((V : Set U) \ {1}) ⊆ orbit M v₁ := by
    intro u hu
    have : u ∈ orbit M v₁ ∩ (V : Set U) := by rw [hOVeq]; exact hu
    exact this.1
  have hOdiff : orbit M v₁ \ (V : Set U) = {v₁} := by
    have h := Set.ncard_inter_add_ncard_diff_eq_ncard (orbit M v₁) (V : Set U)
    rw [h7, hO8] at h
    have h1 : (orbit M v₁ \ (V : Set U)).ncard = 1 := by omega
    obtain ⟨a, ha⟩ := (Set.ncard_eq_one (s := orbit M v₁ \ (V : Set U))).mp h1
    have hv₁diff : v₁ ∈ orbit M v₁ \ (V : Set U) := ⟨hv₁O, hv₁V⟩
    rw [ha] at hv₁diff ⊢
    rw [Set.mem_singleton_iff] at hv₁diff
    rw [← hv₁diff]
  have hOeq : orbit M v₁ = {v₁} ∪ ((V : Set U) \ {1}) := by
    ext u
    constructor
    · intro hu
      by_cases huV : u ∈ V
      · right
        have : u ∈ orbit M v₁ ∩ (V : Set U) := ⟨hu, huV⟩
        rwa [hOVeq] at this
      · left
        have : u ∈ orbit M v₁ \ (V : Set U) := ⟨hu, huV⟩
        rw [hOdiff] at this
        exact this
    · rintro (hu | hu)
      · rw [Set.mem_singleton_iff] at hu
        rwa [hu]
      · exact hVdiffO hu
  exact hMV fun x hx a ha => smul_mem_of_orbit_eq hV hv₁V hOeq hOinv hx ha

private lemma orbit_card_eight_contradiction (h16 : Nat.card U = 16)
    {M : Subgroup (MulAut U)} {g : MulAut U} (hP : IsPGroup 7 (zpowers g))
    (hzg : zpowers g ≤ M) {V : Subgroup U} (hV : Nat.card V = 8)
    (hVinv : ∀ q : zpowers g, ∀ x ∈ V, q • x ∈ V)
    {v₁ : U} (hfixed : fixedPoints (zpowers g) U = ({1, v₁} : Set U))
    (hOinv : ∀ x : ↥M, ∀ u ∈ orbit M v₁, x • u ∈ orbit M v₁)
    (hO8 : (orbit M v₁).ncard = 8)
    (h1O : (1 : U) ∉ orbit M v₁) (hv₁V : v₁ ∉ V)
    (hMV : ¬ StableUnder M V) : False := by
  have hOVinv : ∀ q : zpowers g, ∀ x ∈ orbit M v₁ ∩ (V : Set U),
      q • x ∈ orbit M v₁ ∩ (V : Set U) := fun q x hx =>
    ⟨hOinv ⟨(q : MulAut U), hzg q.2⟩ x hx.1, hVinv q x hx.2⟩
  have hempty : (orbit M v₁ ∩ (V : Set U)) ∩ fixedPoints (zpowers g) U = ∅ := by
    rw [hfixed]
    ext u
    constructor
    · rintro ⟨⟨huO, huV⟩, huF⟩
      rcases huF with h | h
      · exact absurd (h ▸ huO) h1O
      · exact hv₁V (h ▸ huV)
    · intro h
      simp at h
  have hOVmod : (orbit M v₁ ∩ (V : Set U)).ncard ≡ 0 [MOD 7] := by
    have h := CFSG.GH72.ncard_modEq_ncard_inter_fixedPoints hP (Set.toFinite _) hOVinv
    have hzero : ((orbit M v₁ ∩ (V : Set U)) ∩ fixedPoints (zpowers g) U).ncard = 0 := by
      rw [hempty, Set.ncard_empty]
    rwa [hzero] at h
  have hVdiff : ((V : Set U) \ {1}).ncard = 7 := by
    rw [Set.ncard_diff (Set.singleton_subset_iff.mpr V.one_mem), Set.ncard_singleton,
      ← Nat.card_coe_set_eq]
    change Nat.card V - 1 = 7
    rw [hV]
  have hOVle : (orbit M v₁ ∩ (V : Set U)).ncard ≤ 7 := by
    have hsub : orbit M v₁ ∩ (V : Set U) ⊆ (V : Set U) \ {1} := by
      rintro u ⟨huO, huV⟩
      exact ⟨huV, fun h => h1O (h ▸ huO)⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [hVdiff] at this
  have hOVcases : (orbit M v₁ ∩ (V : Set U)).ncard = 0 ∨
      (orbit M v₁ ∩ (V : Set U)).ncard = 7 := by
    have hdvd : 7 ∣ (orbit M v₁ ∩ (V : Set U)).ncard := Nat.modEq_zero_iff_dvd.mp hOVmod
    obtain ⟨k, hk⟩ := hdvd
    have hk1 : k ≤ 1 := by omega
    interval_cases k <;> omega
  rcases hOVcases with h0 | h7
  · have hOVempty : orbit M v₁ ∩ (V : Set U) = ∅ :=
      (Set.ncard_eq_zero (s := orbit M v₁ ∩ (V : Set U))).mp h0
    exact orbit_card_eight_case_zero h16 hV hOinv hO8 hOVempty hMV
  · have hOVeq : orbit M v₁ ∩ (V : Set U) = (V : Set U) \ {1} := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_
      · rintro u ⟨huO, huV⟩
        exact ⟨huV, fun h => h1O (h ▸ huO)⟩
      · rw [h7, hVdiff]
    exact orbit_card_eight_case_seven hV hOinv hO8 hv₁V hOVeq hMV

omit [Finite U] in
private lemma orbit_card_one_contradiction {M : Subgroup (MulAut U)} {F : Subgroup U}
    {v₁ : U} (hMF : ¬ StableUnder M F) (hFpair : (F : Set U) = {1, v₁})
    (hO1 : (orbit M v₁).ncard = 1) : False := by
  obtain ⟨a, ha⟩ := (Set.ncard_eq_one (s := orbit M v₁)).mp hO1
  have hv₁a : v₁ = a := by
    have := mem_orbit_self (M := ↥M) v₁
    rw [ha] at this
    exact this
  have hOeq : orbit M v₁ = {v₁} := by rw [ha, hv₁a]
  apply hMF
  intro x hx u hu
  change u ∈ (F : Set U) at hu
  change x u ∈ (F : Set U)
  rw [hFpair] at hu ⊢
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with h | h
  · left; rw [h]; exact map_one x
  · right
    rw [h]
    have hxO : x • v₁ ∈ orbit M v₁ := orbit_smul_mem hx (mem_orbit_self v₁)
    rw [hOeq] at hxO
    simpa [MulAut.smul_def] using (Set.mem_singleton_iff.mp hxO)

omit [Finite U] in
private lemma ncard_inter_fixedPoints_eq_one {M : Subgroup (MulAut U)} {g : MulAut U} {v₁ : U}
    (hfixed : fixedPoints (zpowers g) U = ({1, v₁} : Set U))
    (h1O : (1 : U) ∉ orbit M v₁) :
    (orbit M v₁ ∩ fixedPoints (zpowers g) U).ncard = 1 := by
  have hEq : orbit M v₁ ∩ fixedPoints (zpowers g) U = {v₁} := by
    rw [hfixed]
    ext u
    constructor
    · rintro ⟨huO, huF⟩
      rcases huF with h | h
      · exact absurd (h ▸ huO) h1O
      · exact h
    · intro hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact ⟨mem_orbit_self v₁, by simp⟩
  rw [hEq, Set.ncard_singleton]

private lemma orbit_card_cases_of_modEq {n : ℕ} (hmod : n ≡ 1 [MOD 7]) (hpos : 1 ≤ n)
    (hle : n ≤ 15) : n = 1 ∨ n = 8 ∨ n = 15 := by
  have hdvd : 7 ∣ n - 1 := (Nat.modEq_iff_dvd' hpos).mp hmod.symm
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : k ≤ 2 := by omega
  interval_cases k <;> omega

omit [Finite U] in
private lemma fifteen_dvd_card_of_orbit_card_fifteen {M : Subgroup (MulAut U)} {v₁ : U}
    (hO15 : (orbit M v₁).ncard = 15) : 15 ∣ Nat.card M := by
  have hos := CFSG.GH72.card_stabilizer_mul_ncard_orbit (H := ↥M) v₁
  rw [hO15] at hos
  refine ⟨Nat.card (stabilizer ↥M v₁), ?_⟩
  rw [← hos, mul_comm]


omit [Finite U] in
private lemma sq_eq_one_of_mem_fixing_of_index_two (hU2 : ∀ u : U, u ^ 2 = 1)
    {V : Subgroup U} (hV : V.index = 2) {y : MulAut U} (hyV : ∀ v ∈ V, y v = v) :
    y ^ 2 = 1 := by
  apply MulEquiv.ext
  intro u
  by_cases hu : u ∈ V
  · rw [pow_two, MulAut.mul_apply, hyV u hu, hyV u hu]
    rfl
  · have hyu : y u ∉ V := by
      intro h
      apply hu
      have hfix : y (y u) = y u := hyV _ h
      exact (y.injective hfix).symm ▸ h
    have hwV : y u * u⁻¹ ∈ V :=
      (Subgroup.mul_mem_iff_of_index_two hV).mpr
        ⟨fun h => absurd h hyu, fun h => absurd (inv_mem_iff.mp h) hu⟩
    have hw : y (y u * u⁻¹) = y u * u⁻¹ := hyV _ hwV
    have hwu : y u * u⁻¹ * u = y u := by rw [mul_assoc, inv_mul_cancel, mul_one]
    calc y (y u) = y (y u * u⁻¹ * u) := by rw [hwu]
      _ = y (y u * u⁻¹) * y u := map_mul _ _ _
      _ = (y u * u⁻¹) * (y u * u⁻¹ * u) := by rw [hw, hwu]
      _ = u := by rw [← mul_assoc, ← pow_two, hU2, one_mul]

omit [Finite U] in
theorem not_stableUnder_of_index_eq_two (hU2 : ∀ u : U, u ^ 2 = 1) {M : Subgroup (MulAut U)}
    (hO2 : O2Trivial M) (hB : IsBasicModule M) {V : Subgroup U} (hV : V.index = 2) :
    ¬ StableUnder M V := by
  intro hMV
  let P : Subgroup (MulAut U) :=
    { carrier := {y | y ∈ M ∧ ∀ v ∈ V, y v = v}
      one_mem' := ⟨M.one_mem, fun v _ => rfl⟩
      mul_mem' := by
        rintro a b ⟨haM, haV⟩ ⟨hbM, hbV⟩
        exact ⟨M.mul_mem haM hbM, fun v hv => by
          rw [MulAut.mul_apply, haV (b v) (hMV b hbM v hv), hbV v hv]⟩
      inv_mem' := by
        rintro a ⟨haM, haV⟩
        refine ⟨M.inv_mem haM, fun v hv => ?_⟩
        have h := haV (a⁻¹ v) (hMV _ (M.inv_mem haM) v hv)
        rw [show a (a⁻¹ v) = v by simp] at h
        exact h.symm }
  have hPM : P ≤ M := fun y hy => hy.1
  have hPN : (P.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPM]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyM, hyV⟩
      refine ⟨M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm), fun v hv => ?_⟩
      change m (y (m⁻¹ v)) = v
      rw [hyV (m⁻¹ v) (hMV m⁻¹ (M.inv_mem hm) v hv)]
      simp
    · rintro ⟨hyM, hyV⟩
      refine ⟨?_, fun v hv => ?_⟩
      · have h : m⁻¹ * (m * y * m⁻¹) * m ∈ M :=
          M.mul_mem (M.mul_mem (M.inv_mem hm) hyM) hm
        simpa [mul_assoc] using h
      · have hfix := hyV (m v) (hMV m hm v hv)
        have : m (y v) = m v := by
          simpa [MulAut.mul_apply] using hfix
        exact m.injective this
  have hP2 : IsPGroup 2 P := by
    rw [IsPGroup.iff_orderOf]
    intro y
    have hy2 : (y : MulAut U) ^ 2 = 1 :=
      sq_eq_one_of_mem_fixing_of_index_two hU2 hV y.2.2
    have hy2' : y ^ 2 = 1 := Subtype.ext hy2
    have hd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2'
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have hPbot : P = ⊥ := hO2 P hPM hPN hP2
  have hVtop : V = ⊤ := hB.2 V hMV fun y hy hyV => by
    have : y ∈ P := ⟨hy, hyV⟩
    rwa [hPbot, mem_bot] at this
  rw [hVtop, Subgroup.index_top] at hV
  omega

omit [Finite U] in
theorem fixV_ne_bot_of_stableUnder_of_card {M : Subgroup (MulAut U)} {F : Subgroup U}
    (hMF : StableUnder M F) (hF : Nat.card F = 2) : fixV M ≠ ⊥ := by
  obtain ⟨f, hfF, hf1, hFeq⟩ := exists_ne_one_and_eq_pair_of_card_eq_two hF
  intro hbot
  have hfmem : f ∈ fixV M := by
    rw [mem_fixV]
    intro x hx
    have hxF : x f ∈ F := hMF x hx f hfF
    have hxne : x f ≠ 1 := by
      intro h
      exact hf1 ((MulEquiv.map_eq_one_iff x).mp h)
    change x f ∈ (F : Set U) at hxF
    rw [hFeq] at hxF
    rcases hxF with h | h
    · exact absurd h hxne
    · exact h
  have : f ∈ (⊥ : Subgroup U) := by rwa [hbot] at hfmem
  rw [mem_bot] at this
  exact hf1 this

theorem fifteen_dvd_card (h16 : Nat.card U = 16) {M : Subgroup (MulAut U)} {g : MulAut U}
    (hgM : g ∈ M) (hg : orderOf g = 7) {F V : Subgroup U} (hF : (F : Set U) = fixedBy U g)
    (hV : Nat.card V = 8) (hgV : ∀ v ∈ V, g v ∈ V) (hMF : ¬ StableUnder M F)
    (hMV : ¬ StableUnder M V) : 15 ∣ Nat.card M := by
  have hF2 : Nat.card F = 2 := by
    change Nat.card (F : Set U) = 2
    rw [Nat.card_coe_set_eq, hF, ← Nat.card_coe_set_eq]
    exact card_fixedBy_eq_two h16 hg
  obtain ⟨v₁, hv₁F, hv₁1, hFpair⟩ := exists_ne_one_and_eq_pair_of_card_eq_two hF2
  have hgv₁ : g v₁ = v₁ := by
    have h : v₁ ∈ (F : Set U) := hv₁F
    rw [hF] at h
    rwa [mem_fixedBy, MulAut.smul_def] at h
  have hv₁V : v₁ ∉ V := fun hvV =>
    hv₁1 (eq_one_of_mem_invariant_of_fixed h16 hg hV hgV hvV hgv₁)
  have h1O : (1 : U) ∉ orbit M v₁ := by
    intro h
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp h
    rw [Subgroup.smul_def, MulAut.smul_def] at hx
    have hx' : (x : MulAut U) v₁ = (x : MulAut U) 1 := by
      simpa using hx
    exact hv₁1 (by simpa using (x : MulAut U).injective hx')
  have hOinv : ∀ x : ↥M, ∀ u ∈ orbit M v₁, x • u ∈ orbit M v₁ :=
    fun x u hu => orbit_smul_mem x.2 hu
  have hfixed : fixedPoints (zpowers g) U = ({1, v₁} : Set U) := by
    rw [CFSG.GH72.fixedPoints_zpowers]
    exact hF.symm.trans hFpair
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hP : IsPGroup 7 (zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hOmod : (orbit M v₁).ncard ≡ 1 [MOD 7] := by
    have h := CFSG.GH72.ncard_modEq_ncard_inter_fixedPoints hP (Set.toFinite _)
      (fun q x hx => hOinv ⟨(q : MulAut U), (Subgroup.zpowers_le.mpr hgM) q.2⟩ x hx)
    rwa [ncard_inter_fixedPoints_eq_one hfixed h1O] at h
  have hOpos : 1 ≤ (orbit M v₁).ncard := by
    have h : 0 < (orbit M v₁).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨v₁, mem_orbit_self v₁⟩
    omega
  have hOle : (orbit M v₁).ncard ≤ 15 := by
    have hsub : orbit M v₁ ⊆ ({1}ᶜ : Set U) := by
      intro u hu h1
      rw [Set.mem_singleton_iff] at h1
      exact h1O (h1 ▸ hu)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [CFSG.GH72.ncard_compl_one h16] at this
  rcases orbit_card_cases_of_modEq hOmod hOpos hOle with hO1 | hO8 | hO15
  · exfalso
    exact orbit_card_one_contradiction hMF hFpair hO1
  · exfalso
    exact orbit_card_eight_contradiction h16 hP (Subgroup.zpowers_le.mpr hgM) hV
      (fun q _ hv => zpowers_smul_mem_of_apply_mem hg hgV q _ hv) hfixed hOinv hO8 h1O hv₁V hMV
  · exact fifteen_dvd_card_of_orbit_card_fifteen hO15


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GL42Seven
