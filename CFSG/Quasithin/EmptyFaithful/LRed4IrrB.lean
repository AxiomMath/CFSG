module

public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.EmptyFaithful.Insp9B56a
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearG2
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace LRed4

section Orders

@[expose] def inspOrders : Finset ℕ := {168, 360, 720, 1080, 2520, 5040, 6048, 12096}

theorem card_perm_fin (n : ℕ) : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem inspList_facts
    {X : Type} [Group X] [Finite X] (h : IsInspList X) :
    Nat.card X ∈ inspOrders ∧ (Nat.card X = 360 → IsAlt 6 X) ∧
      (Nat.card X = 720 → Nonempty (X ≃* Equiv.Perm (Fin 6))) := by
  unfold IsInspList at h
  rcases h with he | he | he | he | he | hhat | he | he
  · obtain ⟨e⟩ := he
    have hc : Nat.card X = 168 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) = 168
      rw [card_statedSL_three1527d, Nat.card_zmod]
      norm_num
    exact ⟨by simp [inspOrders, hc], fun h => by omega, fun h => by omega⟩
  · obtain ⟨e⟩ := he
    have hc : Nat.card X = 360 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
      norm_num [Nat.factorial]
    exact ⟨by simp [inspOrders, hc], fun _ => ⟨e⟩, fun h => by omega⟩
  · obtain ⟨e⟩ := he
    have hc : Nat.card X = 720 := by
      rw [Nat.card_congr e.toEquiv, card_perm_fin]
      norm_num [Nat.factorial]
    exact ⟨by simp [inspOrders, hc], fun h => by omega, fun _ => ⟨e⟩⟩
  · obtain ⟨e⟩ := he
    have hc : Nat.card X = 2520 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7 (by norm_num)]
      norm_num [Nat.factorial]
    exact ⟨by simp [inspOrders, hc], fun h => by omega, fun h => by omega⟩
  · obtain ⟨e⟩ := he
    have hc : Nat.card X = 5040 := by
      rw [Nat.card_congr e.toEquiv, card_perm_fin]
      norm_num [Nat.factorial]
    exact ⟨by simp [inspOrders, hc], fun h => by omega, fun h => by omega⟩
  · obtain ⟨-, hc3, ⟨e⟩⟩ := hhat
    have hc : Nat.card X = 1080 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
      rw [Nat.card_congr e.toEquiv, hc3, card_alternatingGroup1527d 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
      omega
    exact ⟨by simp [inspOrders, hc], fun h => by omega, fun h => by omega⟩
  · obtain ⟨e⟩ := he
    have hF : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
    have hc : Nat.card X = 12096 := by
      rw [Nat.card_congr e.toEquiv, card_quasithinG2_1527d hF, Nat.card_zmod]
      norm_num
    exact ⟨by simp [inspOrders, hc], fun h => by omega, fun h => by omega⟩
  · obtain ⟨e⟩ := he
    have hc : Nat.card X = 6048 := by
      rw [Nat.card_congr e.toEquiv]
      exact EmptyFaithfulMultiple.FFL.card_commutator_quasithinG2 (F := ZMod 2) (Nat.card_zmod 2)
    exact ⟨by simp [inspOrders, hc], fun h => by omega, fun h => by omega⟩

theorem sl2_card_cases {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) = 6 ∨ 2 ^ n * ((2 ^ n) ^ 2 - 1) = 60 ∨ 2 ^ n * ((2 ^ n) ^ 2 - 1) = 504 ∨
      4080 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · interval_cases n
    · left; norm_num
    · right; left; norm_num
    · right; right; left; norm_num
  · right; right; right
    have h16 : 16 ≤ 2 ^ n := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
    have h256 : 256 ≤ (2 ^ n) ^ 2 := by nlinarith
    calc 4080 = 16 * 255 := by norm_num
      _ ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h16 (by omega)

theorem factor_card_cases {X : Type} [Group X] [Finite X] (h : B56FactorList X) :
    Nat.card X = 6 ∨ Nat.card X = 60 ∨ Nat.card X = 120 ∨ Nat.card X = 168 ∨ Nat.card X = 504 ∨
      4080 ≤ Nat.card X := by
  rcases h with ⟨n, K, _, _, hn, hK, he⟩ | he | ⟨m, K, _, _, hm, hodd, hK, he⟩
  · obtain ⟨e⟩ := he
    have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
    rcases sl2_card_cases hn with h | h | h | h <;> rw [← hX] at h <;> omega
  · obtain ⟨e⟩ := he
    right; right; left
    rw [Nat.card_congr e.toEquiv, card_perm_fin]
    norm_num [Nat.factorial]
  · obtain ⟨e⟩ := he
    have hX : Nat.card X = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · have hm1 : m = 1 := by omega
      subst hm1
      right; right; right; left
      rw [hX]; norm_num
    · have hm3 : 3 ≤ m := by
        rcases Nat.lt_or_ge m 3 with h3 | h3
        · have : m = 2 := by omega
          subst this
          exact absurd hodd (by decide)
        · exact h3
      right; right; right; right; right
      rw [hX]
      have h8 : 8 ≤ 2 ^ m := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
      have h512 : 512 ≤ (2 ^ m) ^ 3 := by
        calc 512 = 8 ^ 3 := by norm_num
          _ ≤ (2 ^ m) ^ 3 := Nat.pow_le_pow_left h8 3
      have h64 : 64 ≤ (2 ^ m) ^ 2 := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h8 2
      have h1 : 63 ≤ (2 ^ m) ^ 2 - 1 := by omega
      have h2 : 511 ≤ (2 ^ m) ^ 3 - 1 := by omega
      calc 4080 ≤ 512 * (63 * 511) := by norm_num
        _ ≤ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
          Nat.mul_le_mul h512 (Nat.mul_le_mul h1 h2)

end Orders

section CardSup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_of_mem_sup_comm {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [hAB a' ha' b hb]
          _ = a * b * (a' * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h1 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := hAB a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
        rw [mul_inv_rev, h1] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

omit [Finite G] in
theorem card_sup_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hmem : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ A ⊔ B := fun a ha b hb =>
    (A ⊔ B).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  let φ : ↥A × ↥B → ↥(A ⊔ B) := fun p => ⟨(p.1 : G) * (p.2 : G), hmem _ p.1.2 _ p.2.2⟩
  have hinj : Function.Injective φ := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h1 : a * b = a' * b' := congrArg Subtype.val h
    have h2 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have hmem2 : a'⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem ha') ha, h2 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
    rw [hinf, Subgroup.mem_bot] at hmem2
    have hea : a = a' := by
      have : a' * (a'⁻¹ * a) = a' * 1 := by rw [hmem2]
      simpa using this
    subst hea
    have hbb : b = b' := mul_left_cancel h1
    subst hbb
    rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_comm hAB hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm

end CardSup

section NormalSubgroups

theorem normal_card_perm6 (M : Subgroup (Equiv.Perm (Fin 6))) (hM : M.Normal) :
    Nat.card ↥M ≤ 2 ∨ 360 ≤ Nat.card ↥M := by
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hn : (M.subgroupOf (alternatingGroup (Fin 6))).Normal := hM.subgroupOf _
  rcases hs.eq_bot_or_eq_top_of_normal (M.subgroupOf (alternatingGroup (Fin 6))) with h | h
  · left
    have hinj : Function.Injective ((Equiv.Perm.sign : Equiv.Perm (Fin 6) →* ℤˣ).comp M.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      rw [MonoidHom.mem_ker] at ha
      have hmem : (⟨(a : Equiv.Perm (Fin 6)), Equiv.Perm.mem_alternatingGroup.2 ha⟩ :
          ↥(alternatingGroup (Fin 6))) ∈ M.subgroupOf (alternatingGroup (Fin 6)) := a.2
      rw [h, Subgroup.mem_bot] at hmem
      have := congrArg Subtype.val hmem
      simpa using this
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  · right
    have hle : alternatingGroup (Fin 6) ≤ M := Subgroup.subgroupOf_eq_top.1 h
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_eq_fintype_card (α := ↥(alternatingGroup (Fin 6))), card_alternatingGroup,
      Fintype.card_fin] at this
    norm_num [Nat.factorial] at this
    exact this

variable {V : Type} [CommGroup V] [Finite V]

theorem normal_contra
    {H : Subgroup (MulAut V)} (hI : IsInspList ↥H)
    (hH : Nat.card ↥H = 360 ∨ Nat.card ↥H = 720) {N : Subgroup (MulAut V)} (hNH : N ≤ H)
    (hn : (N.subgroupOf H).Normal) (hN : Nat.card ↥N = 6 ∨ Nat.card ↥N = 60 ∨ Nat.card ↥N = 120) :
    False := by
  obtain ⟨-, hA, hS⟩ := inspList_facts hI
  have hcardN : Nat.card ↥(N.subgroupOf H) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  have := hn
  rcases hH with h360 | h720
  · obtain ⟨e⟩ := hA h360
    have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hsimple : IsSimpleGroup ↥H := e.isSimpleGroup
    rcases hsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf H) with h | h
    · rw [h, Subgroup.card_bot] at hcardN
      omega
    · rw [h, Subgroup.card_top, h360] at hcardN
      omega
  · obtain ⟨e⟩ := hS h720
    have hMn : ((N.subgroupOf H).map e.toMonoidHom).Normal := hn.map e.toMonoidHom e.surjective
    have hcardM : Nat.card ↥((N.subgroupOf H).map e.toMonoidHom) = Nat.card ↥N := by
      rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcardN]
    rcases normal_card_perm6 _ hMn with h | h <;> omega

end NormalSubgroups

section Cases

variable {V : Type} [CommGroup V] [Finite V]

theorem six_le_of_factor {X : Type} [Group X] [Finite X] (h : B56FactorList X) : 6 ≤ Nat.card X := by
  rcases factor_card_cases h with h | h | h | h | h | h <;> omega

theorem not_case3
    {H : Subgroup (MulAut V)} (hI : IsInspList ↥H) (h : B56Case3 H) :
    False := by
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, hF₁, hF₂, -⟩ := h
  have hle₁ : G₁ ≤ H := hsup ▸ le_sup_left
  have hcard : Nat.card ↥H = Nat.card ↥G₁ * Nat.card ↥G₂ := by
    rw [← hsup]; exact card_sup_of_commute hcomm hinf
  obtain ⟨hmem, -, -⟩ := inspList_facts hI
  have hn₁ : (G₁.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle₁).2 (Insp9.le_normalizer_of_commute hsup hcomm)
  simp only [inspOrders, Finset.mem_insert, Finset.mem_singleton] at hmem
  have hH12 : Nat.card ↥H ≤ 12096 := by rcases hmem with h | h | h | h | h | h | h | h <;> omega
  have h6₁ := six_le_of_factor hF₁
  have h6₂ := six_le_of_factor hF₂
  have hb₁ : Nat.card ↥G₁ * 6 ≤ Nat.card ↥H := by rw [hcard]; exact Nat.mul_le_mul_left _ h6₂
  have hb₂ : 6 * Nat.card ↥G₂ ≤ Nat.card ↥H := by rw [hcard]; exact Nat.mul_le_mul_right _ h6₁
  rcases factor_card_cases hF₁ with h1 | h1 | h1 | h1 | h1 | h1 <;>
    rcases factor_card_cases hF₂ with h2 | h2 | h2 | h2 | h2 | h2 <;>
    first
    | omega
    | (rw [h1, h2] at hcard
       first
       | omega
       | exact normal_contra hI (by omega) hle₁ hn₁ (by omega))

theorem not_case4
    {H : Subgroup (MulAut V)} (hI : IsInspList ↥H) (h : B56Case4 H) :
    False := by
  obtain ⟨G₁, G₂, t, hG, hinf, hcomm, ⟨e⟩, hcard₂, -, -, -, -, -, -, -, hout₁, -⟩ := h
  have hle₁ : G₁ ≤ H := hG ▸ le_sup_left.trans le_sup_left
  have hle₂ : G₂ ≤ H := hG ▸ le_sup_right.trans le_sup_left
  have hsupH : G₁ ⊔ G₂ ≤ H := sup_le hle₁ hle₂
  have hc1 : Nat.card ↥G₁ = 360 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
    norm_num [Nat.factorial]
  have hc12 : Nat.card ↥(G₁ ⊔ G₂) = 1080 := by rw [card_sup_of_commute hcomm hinf, hc1, hcard₂]
  have hdvd : 1080 ∣ Nat.card ↥H := hc12 ▸ Subgroup.card_dvd_of_le hsupH
  obtain ⟨hmem, -, -⟩ := inspList_facts hI
  simp only [inspOrders, Finset.mem_insert, Finset.mem_singleton] at hmem
  have hH : Nat.card ↥H = 1080 := by
    rcases hmem with h | h | h | h | h | h | h | h <;> rw [h] at hdvd ⊢ <;> omega
  have hHeq : G₁ ⊔ G₂ = H := Subgroup.eq_of_le_of_card_ge hsupH (by rw [hc12, hH])
  have htH : t ∈ H := hG ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  rw [← hHeq] at htH
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_comm hcomm htH
  apply hout₁
  refine ⟨a, ha, fun x hx => ?_⟩
  rw [← hab]
  have hbx : x * b = b * x := hcomm x hx b hb
  calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
    _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [hbx]
    _ = a * x * a⁻¹ := by group

theorem not_case5
    {H : Subgroup (MulAut V)} (hI : IsInspList ↥H) (h : B56Case5 H) :
    False := by
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, -, ⟨e⟩, -, -, hG₂⟩ := h
  have hcard : Nat.card ↥H = Nat.card ↥G₁ * Nat.card ↥G₂ := by
    rw [← hsup]; exact card_sup_of_commute hcomm hinf
  have hc1 : Nat.card ↥G₁ = 168 := by
    rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
    norm_num
  obtain ⟨hmem, -, -⟩ := inspList_facts hI
  simp only [inspOrders, Finset.mem_insert, Finset.mem_singleton] at hmem
  have hc2 : Nat.card ↥G₂ = 168 ∨ Nat.card ↥G₂ = 6 ∨ Nat.card ↥G₂ = 60 ∨ Nat.card ↥G₂ = 504 ∨
      4080 ≤ Nat.card ↥G₂ := by
    rcases hG₂ with ⟨⟨e2⟩, -⟩ | ⟨n, K, _, _, hK, π, hπ⟩
    · left
      rw [Nat.card_congr e2.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
      norm_num
    · have hn : 1 ≤ n := by
        by_contra hn0
        have hn0' : n = 0 := by omega
        subst hn0'
        have h1 : 1 < Nat.card K := Finite.one_lt_card
        rw [hK] at h1
        omega
      have hX : Nat.card ↥G₂ = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
        rw [card_eq_of_nat_realizes1527d hπ, card_statedSL_two1527d, hK]
      rcases sl2_card_cases hn with h | h | h | h <;> rw [← hX] at h <;> omega
  rw [hc1] at hcard
  rcases hmem with h | h | h | h | h | h | h | h <;> omega

end Cases

end LRed4

end CFSG.Quasithin
