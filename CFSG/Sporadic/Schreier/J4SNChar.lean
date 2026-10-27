module

public import CFSG.Sporadic.Schreier.J4SNCharCheck
public import CFSG.Sporadic.Schreier.J4SInvolution
public import CFSG.Sporadic.Schreier.J4SOuter
public import CFSG.Sporadic.Schreier.J4SOddLemmas

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem exists_nfElt
    {s : J} (hs : s ∈ S0) : ∃ n < 2048, ∃ e < 1024, s = nfElt n e := by
  obtain ⟨m, hm, u, hu, rfl⟩ := exists_mul_of_mem_S0 hs
  obtain ⟨n, hn, rfl⟩ := exists_η_eq hm
  obtain ⟨e, he, rfl⟩ := mem_U_iff.1 hu
  exact ⟨n, hn, e, he, rfl⟩

theorem app11_elem_lt
    {e : ℕ} (he : e < 1024) (v : ℕ) : app11 elementColumns[e]! v < 2 ^ 11 :=
  vecMulN_lt (fun j hj => by rw [← getElem!_eq_getD']; exact (elem_all e he).2.1 j hj) v

theorem nf_conj_η
    (n : ℕ) {e : ℕ} (he : e < 1024) (v : ℕ) :
    nfElt n e * η v * (nfElt n e)⁻¹ = η (app11 elementColumns[e]! v) := by
  have h1 : nfElt n e * η v * (nfElt n e)⁻¹ = η n * (uElt e * η v * (uElt e)⁻¹) * (η n)⁻¹ := by
    rw [nfElt]
    group
  have hx : n ^^^ app11 elementColumns[e]! v ^^^ n = app11 elementColumns[e]! v := by
    rw [Nat.xor_comm n, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [h1, uElt_acts he, η_inv', ← η_xor, ← η_xor, hx]

theorem kgen_inv_conj_nf
    {i : ℕ} (hi : i < 4) (n : ℕ) {e : ℕ} (he : e < 1024) :
    (kgen i)⁻¹ * nfElt n ((conjTab[i]!)[e]!) * kgen i =
      nfElt (app11 genInvColumns[i]! n) e := by
  have h1 : (kgen i)⁻¹ * nfElt n ((conjTab[i]!)[e]!) * kgen i =
      ((kgen i)⁻¹ * η n * kgen i) * ((kgen i)⁻¹ * uElt ((conjTab[i]!)[e]!) * kgen i) := by
    rw [nfElt]
    group
  have h2 : (kgen i)⁻¹ * uElt ((conjTab[i]!)[e]!) * kgen i = uElt e := by
    rw [← uElt_conj_kgen hi he]
    group
  rw [h1, h2, inv_conj_η_of_cols (kgen_acts hi) (genInv_all i hi) n]
  rfl

theorem classForestOK_spec {L : List (ℕ × ℕ × ℕ)} (h : classForestOK L = true) :
    ∀ k < L.length, (L[k]!).1 < 1024 ∧ (k = 0 ∨ ((L[k]!).2.1 < k ∧ (L[k]!).2.2 < 4 ∧
      (L[k]!).1 = (conjTab[(L[k]!).2.2]!)[(L[(L[k]!).2.1]!).1]!)) := by
  unfold classForestOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  intro k hk
  have h1 := h.2 k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  exact ⟨h1.1, by tauto⟩

theorem special_of_closed {P : ℕ → Prop}
    (hconj : ∀ i < 4, ∀ e < 1024, P e → P ((conjTab[i]!)[e]!))
    (hinv : ∀ i < 4, ∀ e < 1024, P ((conjTab[i]!)[e]!) → P e)
    (hquad : ∀ e < 1024, ∀ e' < 1024, P e → P e' → ∀ v < 2048, quadAt e e' v = true)
    {e : ℕ} (he : e < 1024) (he0 : e ≠ 0) (hP : P e) : e = 118 ∨ e = 448 ∨ e = 502 := by
  have hq : quadSelf e = true := by
    unfold quadSelf
    rw [List.all_eq_true]
    intro v hv
    exact hquad e he e he hP hP v (List.mem_range.1 hv)
  obtain ⟨c, hc, hmem⟩ := uClasses_check.2.2.2 e he he0 hq
  obtain ⟨hF, hW⟩ := uClasses_check.2.2.1 c hc
  have hsp := classForestOK_spec hF
  obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hmem
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
  have hLk : (uClasses[c]!)[k]! = x := by rw [getElem!_pos _ k hk, hkx]
  have hup : ∀ k < (uClasses[c]!).length, P ((uClasses[c]!)[k]!).1 →
      P ((uClasses[c]!)[0]!).1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hPk
      rcases (hsp k hk).2 with rfl | ⟨hp, hg, heq⟩
      · exact hPk
      · rw [heq] at hPk
        exact ih _ hp (hp.trans hk) (hinv _ hg _ (hsp _ (hp.trans hk)).1 hPk)
  have hdown : P ((uClasses[c]!)[0]!).1 → ∀ k < (uClasses[c]!).length,
      P ((uClasses[c]!)[k]!).1 := by
    intro h0 k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases (hsp k hk).2 with rfl | ⟨hp, hg, heq⟩
      · exact h0
      · rw [heq]
        exact hconj _ hg _ (hsp _ (hp.trans hk)).1 (ih _ hp (hp.trans hk))
  have hall := hdown (hup k hk (by rw [hLk, hxe]; exact hP))
  unfold classWitOK at hW
  rcases hw : uWitness[c]! with _ | ⟨a, b, v⟩
  · rw [hw] at hW
    have h1 := List.all_eq_true.1 hW x hx
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rw [← hxe]
    exact or_assoc.1 h1
  · rw [hw] at hW
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hW
    obtain ⟨⟨⟨ha, hb⟩, hv⟩, hfalse⟩ := hW
    have := hquad _ (hsp a ha).1 _ (hsp b hb).1 (hall a ha) (hall b hb) v hv
    rw [hfalse] at this
    exact absurd this (by decide)

section Uniq

variable {A : Subgroup J} (hAn : ∀ s ∈ S0, ∀ a ∈ A, s * a * s⁻¹ ∈ A)
  (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)

include hAn hAc in
theorem quadAt_of_mem
    {n e n' e' : ℕ} (he : e < 1024) (he' : e' < 1024)
    (ha : nfElt n e ∈ A) (ha' : nfElt n' e' ∈ A) {v : ℕ} (hv : v < 2048) :
    quadAt e e' v = true := by
  have hx : app11 elementColumns[e']! v ^^^ v < 2 ^ 11 :=
    Nat.xor_lt_two_pow (app11_elem_lt he' v) hv
  have hw : η (app11 elementColumns[e']! v ^^^ v) ∈ A := by
    have h2 : η v * (nfElt n' e')⁻¹ * (η v)⁻¹ ∈ A :=
      hAn _ (N_le_S0 (η_mem_N v)) _ (A.inv_mem ha')
    have h3 := A.mul_mem ha' h2
    rw [show nfElt n' e' * (η v * (nfElt n' e')⁻¹ * (η v)⁻¹) =
      nfElt n' e' * η v * (nfElt n' e')⁻¹ * (η v)⁻¹ by group, nf_conj_η n' he' v, η_inv',
      ← η_xor] at h3
    exact h3
  have hc : nfElt n e * η (app11 elementColumns[e']! v ^^^ v) * (nfElt n e)⁻¹ =
      η (app11 elementColumns[e']! v ^^^ v) := by
    rw [hAc _ ha _ hw, mul_inv_cancel_right]
  rw [nf_conj_η n he] at hc
  have h4 := η_injOn (app11_elem_lt he _) hx hc
  unfold quadAt
  simp only
  rw [h4, Nat.xor_self]
  rfl

@[expose] def InIdx
    (A : Subgroup J) (e : ℕ) : Prop := ∃ n, nfElt n e ∈ A

include hAn in
theorem inIdx_conj
    {i : ℕ} (hi : i < 4) {e : ℕ} (he : e < 1024) (h : InIdx A e) :
    InIdx A ((conjTab[i]!)[e]!) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨app11 generatorColumns[i]! n, ?_⟩
  rw [← kgen_conj_nf hi n he]
  exact hAn _ (kgen_mem_S0 ⟨i, hi⟩) _ hn

include hAn in
theorem inIdx_of_conj
    {i : ℕ} (hi : i < 4) {e : ℕ} (he : e < 1024)
    (h : InIdx A ((conjTab[i]!)[e]!)) : InIdx A e := by
  obtain ⟨n, hn⟩ := h
  refine ⟨app11 genInvColumns[i]! n, ?_⟩
  rw [← kgen_inv_conj_nf hi n he]
  have h1 := hAn _ (S0.inv_mem (kgen_mem_S0 ⟨i, hi⟩)) _ hn
  rwa [inv_inv] at h1

include hAn hAc in
theorem idx_special
    {n e : ℕ} (he : e < 1024) (he0 : e ≠ 0) (ha : nfElt n e ∈ A) :
    e = 118 ∨ e = 448 ∨ e = 502 :=
  special_of_closed (P := InIdx A) (fun _ hi _ he h => inIdx_conj hAn hi he h)
    (fun _ hi _ he h => inIdx_of_conj hAn hi he h)
    (fun _ he _ he' hP hP' _ hv => by
      obtain ⟨n, hn⟩ := hP
      obtain ⟨n', hn'⟩ := hP'
      exact quadAt_of_mem hAn hAc he he' hn hn' hv) he he0 ⟨n, ha⟩

theorem fixCount_special {e : ℕ} (h : e = 118 ∨ e = 448 ∨ e = 502) :
    fixCount elementColumns[e]! = 128 := by
  rcases h with rfl | rfl | rfl
  · exact uSpecial_check.1
  · exact uSpecial_check.2.1
  · exact uSpecial_check.2.2.1

include hAn hAc in
theorem eq_N_of_abelian_normal
    (hAS : A ≤ S0) (hcard : Nat.card A = 2 ^ 11) : A = N := by
  classical
  by_contra hne
  have hAN : ¬ A ≤ N := fun h => hne (Subgroup.eq_of_le_of_card_ge h (by rw [hcard, card_N]))
  obtain ⟨a0, ha0, ha0N⟩ := Set.not_subset.1 hAN
  obtain ⟨n0, -, e0, he0, rfl⟩ := exists_nfElt (hAS ha0)
  have he00 : e0 ≠ 0 := by
    rintro rfl
    apply ha0N
    rw [nfElt, uElt_zero, mul_one]
    exact η_mem_N n0
  have hspec := idx_special hAn hAc he0 he00 ha0
  have hAN' : ∀ a ∈ A, ∀ m ∈ N, a * m * a⁻¹ ∈ N := fun a ha m hm =>
    conj_mem_N_of_mem_H a (S0_le_H (hAS ha)) m hm
  have hker : Nat.card (conjOn hAN').ker ≤ 128 := by
    rw [← fixCount_special hspec,
      ← card_centralizer_N_of_actsBy (uElt_acts he0) fun j hj => by
        rw [← getElem!_eq_getD']; exact (elem_all e0 he0).2.1 j hj]
    refine Nat.card_le_card_of_injective (fun k => (⟨(k : A), ?_⟩ :
      (Subgroup.centralizer {uElt e0} ⊓ N : Subgroup J))) fun k k' h => ?_
    · have hk := MonoidHom.mem_ker.1 k.2
      have hkN : ((k : A) : J) ∈ N := by
        refine QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2.le
          (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun m hm => ?_,
            S0_le_H (hAS (k : A).2)⟩)
        have h1 := congrArg (fun φ : MulAut N => ((φ ⟨m, hm⟩ : N) : J)) hk
        change ((k : A) : J) * m * ((k : A) : J)⁻¹ = m at h1
        calc m * ((k : A) : J) = ((k : A) : J) * m * ((k : A) : J)⁻¹ * (k : A) := by rw [h1]
          _ = (k : A) * m := by group
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hkN⟩
      have h2 := hAc _ (k : A).2 _ ha0
      have h3 := N_comm _ hkN _ (η_mem_N n0)
      rw [nfElt] at h2
      calc ((k : A) : J) * uElt e0 = (η n0)⁻¹ * (η n0 * (k : A)) * uElt e0 := by group
        _ = (η n0)⁻¹ * ((k : A) * η n0) * uElt e0 := by rw [h3]
        _ = (η n0)⁻¹ * (((k : A) : J) * (η n0 * uElt e0)) := by group
        _ = (η n0)⁻¹ * (η n0 * uElt e0 * (k : A)) := by rw [h2]
        _ = uElt e0 * (k : A) := by group
    · have h1 := Subtype.ext_iff.1 h
      dsimp only at h1
      exact Subtype.ext (Subtype.ext h1)
  have hUN : ∀ u ∈ U, ∀ m ∈ N, u * m * u⁻¹ ∈ N := fun u hu m hm =>
    conj_mem_N_of_mem_H u (S0_le_H (U_le_S0 hu)) m hm
  have hrange : Nat.card (conjOn hAN').range ≤ 4 := by
    have hsub : ((conjOn hAN').range : Set (MulAut N)) ⊆
        (fun e => conjOn hUN ⟨uElt e, uElt_mem_U e⟩) '' {0, 118, 448, 502} := by
      rintro _ ⟨⟨a, ha⟩, rfl⟩
      obtain ⟨n, -, e, he, rfl⟩ := exists_nfElt (hAS ha)
      refine ⟨e, ?_, MulEquiv.ext fun m => Subtype.ext ?_⟩
      · by_cases he0 : e = 0
        · exact Or.inl he0
        · rcases idx_special hAn hAc he he0 ha with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
      · change uElt e * m * (uElt e)⁻¹ = nfElt n e * m * (nfElt n e)⁻¹
        have h1 := N_comm _ (η_mem_N n) _ (hUN _ (uElt_mem_U e) m m.2)
        rw [nfElt]
        calc uElt e * m * (uElt e)⁻¹ = (η n)⁻¹ * (η n * (uElt e * m * (uElt e)⁻¹)) := by group
          _ = (η n)⁻¹ * ((uElt e * m * (uElt e)⁻¹) * η n) := by rw [h1]
          _ = η n * uElt e * m * (η n * uElt e)⁻¹ := by
            rw [show (η n * uElt e)⁻¹ = (uElt e)⁻¹ * η n by rw [mul_inv_rev, η_inv'], η_inv']
            group
    have hc : Nat.card (conjOn hAN').range = ((conjOn hAN').range : Set (MulAut N)).ncard :=
      Nat.card_coe_set_eq _
    rw [hc]
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      ((Set.ncard_image_le (Set.toFinite _)).trans ?_)
    refine (Set.ncard_insert_le _ _).trans ?_
    have h1 := Set.ncard_insert_le (118 : ℕ) ({448, 502} : Set ℕ)
    have h2 := Set.ncard_insert_le (448 : ℕ) ({502} : Set ℕ)
    rw [Set.ncard_singleton] at h2
    omega
  have h := card_ker_mul_card_range (conjOn hAN')
  rw [hcard] at h
  have : Nat.card (conjOn hAN').ker * Nat.card (conjOn hAN').range ≤ 128 * 4 :=
    Nat.mul_le_mul hker hrange
  omega

end Uniq

theorem characteristic_of_unique {G : Type*} [Group G] [Finite G] {S N : Subgroup G}
    (hNS : N ≤ S) (hNn : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N)
    (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (huniq : ∀ A : Subgroup G, A ≤ S → (∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A = Nat.card N → A = N) :
    (N.subgroupOf S).Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.2 fun φ => ?_
  set A := ((N.subgroupOf S).map φ.toMonoidHom).map S.subtype with hA
  have hmemA : ∀ x : S, (x : G) ∈ A ↔ φ.symm x ∈ N.subgroupOf S := by
    intro x
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, hy⟩
      have h1 : φ.toMonoidHom z = x := Subtype.ext hy
      rw [← h1, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact hz
    · intro hx
      exact ⟨x, ⟨φ.symm x, hx, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]⟩, rfl⟩
  have hAS : A ≤ S := Subgroup.map_subtype_le _
  have hAn : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A := by
    intro s hs a ha
    have haS := hAS ha
    have h1 := (hmemA ⟨a, haS⟩).1 ha
    have h2 : φ.symm (⟨s, hs⟩ * ⟨a, haS⟩ * ⟨s, hs⟩⁻¹) ∈ N.subgroupOf S := by
      rw [map_mul, map_mul, map_inv, Subgroup.mem_subgroupOf]
      exact hNn _ (φ.symm ⟨s, hs⟩).2 _ (Subgroup.mem_subgroupOf.1 h1)
    exact (hmemA ⟨s * a * s⁻¹, S.mul_mem (S.mul_mem hs haS) (S.inv_mem hs)⟩).2 h2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩ _ ⟨x', ⟨y', hy', rfl⟩, rfl⟩
    have h := hNc _ (Subgroup.mem_subgroupOf.1 hy) _ (Subgroup.mem_subgroupOf.1 hy')
    have h' : y * y' = y' * y := Subtype.ext h
    change ((φ y : S) : G) * (φ y' : S) = (φ y' : S) * (φ y : S)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h']
  have hcard : Nat.card A = Nat.card N := by
    rw [hA, Subgroup.card_map_of_injective S.subtype_injective,
      Subgroup.card_map_of_injective φ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNS).toEquiv
  have hAN := huniq A hAS hAn hAc hcard
  ext x
  constructor
  · intro hx
    have h1 : (x : G) ∈ A := ⟨x, hx, rfl⟩
    rw [hAN] at h1
    exact Subgroup.mem_subgroupOf.2 h1
  · intro hx
    have h1 : (x : G) ∈ A := by
      rw [hAN]
      exact Subgroup.mem_subgroupOf.1 hx
    obtain ⟨y, hy, hyx⟩ := h1
    have h2 : y = x := Subtype.ext hyx
    rw [← h2]
    exact hy

@[expose] def QuadOn (B : Subgroup J) : Prop :=
  ∀ b ∈ B, ∀ c ∈ B, ∀ m ∈ N, b * (c * m * c⁻¹ * m⁻¹) * b⁻¹ = c * m * c⁻¹ * m⁻¹

theorem uElt_comm_η
    {e e' : ℕ} (he : e < 1024) (he' : e' < 1024) (v : ℕ) :
    uElt e * (uElt e' * η v * (uElt e')⁻¹ * (η v)⁻¹) * (uElt e)⁻¹ =
        η (app11 elementColumns[e]! (app11 elementColumns[e']! v ^^^ v)) ∧
      uElt e' * η v * (uElt e')⁻¹ * (η v)⁻¹ = η (app11 elementColumns[e']! v ^^^ v) := by
  have h1 : uElt e' * η v * (uElt e')⁻¹ * (η v)⁻¹ = η (app11 elementColumns[e']! v ^^^ v) := by
    rw [uElt_acts he', η_inv', ← η_xor]
  exact ⟨by rw [h1, uElt_acts he], h1⟩

theorem quad_iff
    {e e' v : ℕ} (he : e < 1024) (he' : e' < 1024) (hv : v < 2048) :
    uElt e * (uElt e' * η v * (uElt e')⁻¹ * (η v)⁻¹) * (uElt e)⁻¹ =
      uElt e' * η v * (uElt e')⁻¹ * (η v)⁻¹ ↔ quadAt e e' v = true := by
  obtain ⟨h1, h2⟩ := uElt_comm_η he he' v
  rw [h1, h2]
  have hx : app11 elementColumns[e']! v ^^^ v < 2 ^ 11 :=
    Nat.xor_lt_two_pow (app11_elem_lt he' v) hv
  unfold quadAt
  simp only [beq_iff_eq]
  constructor
  · intro h
    rw [η_injOn (app11_elem_lt he _) hx h, Nat.xor_self]
  · intro h
    rw [xor_eq_zero_iff.1 h]

theorem conj_inv_mem_of_finite {G : Type*} [Group G] {B : Subgroup G} [Finite B] {g : G}
    (h : ∀ b ∈ B, g * b * g⁻¹ ∈ B) : ∀ b ∈ B, g⁻¹ * b * g ∈ B := by
  intro b hb
  have hinj : Function.Injective fun x : B => (⟨g * x * g⁻¹, h x x.2⟩ : B) := by
    intro x y hxy
    have h1 := Subtype.ext_iff.1 hxy
    dsimp only at h1
    exact Subtype.ext (by simpa using h1)
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨b, hb⟩
  have h1 := Subtype.ext_iff.1 hx
  dsimp only at h1
  rw [← h1]
  simp [mul_assoc]

@[expose] def B2 :
    Subgroup J where
  carrier := {g | ∃ c ∈ [0, 118, 448, 502], g = uElt c}
  one_mem' := ⟨0, by simp, uElt_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    obtain ⟨d, hd, hdc⟩ := uSpecial_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c hc c' hc'
    have hlt : ∀ x ∈ [0, 118, 448, 502], x < 1024 := by decide
    refine ⟨d, hd, eq_of_actsBy (K.mul_mem (U_le_K (uElt_mem_U c)) (U_le_K (uElt_mem_U c')))
      (U_le_K (uElt_mem_U d)) ?_ (uElt_acts (hlt d hd))⟩
    rw [← hdc]
    exact actsBy_mul (uElt_acts (hlt c hc)) (uElt_acts (hlt c' hc'))
  inv_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨c, hc, ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc1
    · rw [uElt_zero, inv_one]
    · have hlt : ∀ x ∈ [118, 448, 502], x < 1024 := by decide
      have h1 := actsBy_mul (uElt_acts (hlt c hc1)) (uElt_acts (hlt c hc1))
      rw [uSpecial_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c hc1, elem_zero] at h1
      exact inv_eq_of_mul_eq_one_right (eq_of_actsBy
        (K.mul_mem (U_le_K (uElt_mem_U c)) (U_le_K (uElt_mem_U c))) K.one_mem h1 actsBy_one)

@[expose] def B1 :
    Subgroup J where
  carrier := {g | g = 1 ∨ g = uElt 118}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have hsq : uElt 118 * uElt 118 = 1 := by
      have h1 := actsBy_mul (uElt_acts (by norm_num : 118 < 1024))
        (uElt_acts (by norm_num : 118 < 1024))
      rw [uSpecial_check.2.2.2.2.2.1] at h1
      exact eq_of_actsBy (K.mul_mem (U_le_K (uElt_mem_U _)) (U_le_K (uElt_mem_U _))) K.one_mem
        h1 actsBy_one
    rintro _ _ (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl hsq
  inv_mem' := by
    rintro _ (rfl | rfl)
    · exact Or.inl inv_one
    · refine Or.inr (inv_eq_of_mul_eq_one_right ?_)
      have h1 := actsBy_mul (uElt_acts (by norm_num : 118 < 1024))
        (uElt_acts (by norm_num : 118 < 1024))
      rw [uSpecial_check.2.2.2.2.2.1] at h1
      exact eq_of_actsBy (K.mul_mem (U_le_K (uElt_mem_U _)) (U_le_K (uElt_mem_U _))) K.one_mem
        h1 actsBy_one

theorem mem_B2_iff
    {g : J} : g ∈ B2 ↔ ∃ c ∈ [0, 118, 448, 502], g = uElt c := Iff.rfl

theorem mem_B1_iff
    {g : J} : g ∈ B1 ↔ g = 1 ∨ g = uElt 118 := Iff.rfl

theorem uElt_mul_special
    {c c' : ℕ} (hc : c < 1024) (hc' : c' < 1024) {d : ℕ} (hd : d < 1024)
    (h : comp11 elementColumns[c]! elementColumns[c']! = elementColumns[d]!) :
    uElt c * uElt c' = uElt d := by
  have h1 := actsBy_mul (uElt_acts hc) (uElt_acts hc')
  rw [h] at h1
  exact eq_of_actsBy (K.mul_mem (U_le_K (uElt_mem_U _)) (U_le_K (uElt_mem_U _)))
    (U_le_K (uElt_mem_U _)) h1 (uElt_acts hd)

theorem quad_normal_eq
    {B : Subgroup J} (hBU : B ≤ U)
    (hBn : ∀ u ∈ U, ∀ b ∈ B, u * b * u⁻¹ ∈ B) (hq : QuadOn B) : B = ⊥ ∨ B = B1 ∨ B = B2 := by
  have hconj : ∀ i < 4, ∀ e < 1024, uElt e ∈ B → uElt ((conjTab[i]!)[e]!) ∈ B := by
    intro i hi e he h
    rw [← uElt_conj_kgen hi he]
    exact hBn _ (kgen_mem_U ⟨i, hi⟩) _ h
  have hinv : ∀ i < 4, ∀ e < 1024, uElt ((conjTab[i]!)[e]!) ∈ B → uElt e ∈ B := by
    intro i hi e he h
    have h1 := hBn _ (U.inv_mem (kgen_mem_U ⟨i, hi⟩)) _ h
    rwa [← uElt_conj_kgen hi he, inv_inv,
      show (kgen i)⁻¹ * (kgen i * uElt e * (kgen i)⁻¹) * kgen i = uElt e by group] at h1
  have hquad : ∀ e < 1024, ∀ e' < 1024, uElt e ∈ B → uElt e' ∈ B → ∀ v < 2048,
      quadAt e e' v = true := fun e he e' he' h h' v hv =>
    (quad_iff he he' hv).1 (hq _ h _ h' _ (η_mem_N v))
  have hidx : ∀ e < 1024, uElt e ∈ B → e = 0 ∨ e = 118 ∨ e = 448 ∨ e = 502 := by
    intro e he h
    by_cases he0 : e = 0
    · exact Or.inl he0
    · exact Or.inr (special_of_closed (P := fun e => uElt e ∈ B) hconj hinv hquad he he0 h)
  have hmem : ∀ b ∈ B, ∃ e, (e = 0 ∨ e = 118 ∨ e = 448 ∨ e = 502) ∧ b = uElt e := by
    intro b hb
    obtain ⟨e, he, rfl⟩ := mem_U_iff.1 (hBU hb)
    exact ⟨e, hidx e he hb, rfl⟩
  obtain ⟨i0, hi0, h448⟩ := uSpecial_check.2.2.2.2.2.2.2.2.2.2.1
  by_cases h4 : uElt 448 ∈ B ∨ uElt 502 ∈ B
  · have h448B : uElt 448 ∈ B := by
      rcases h4 with h | h
      · exact h
      · exact hinv i0 hi0 448 (by norm_num) (h448 ▸ h)
    have h502B : uElt 502 ∈ B := h448 ▸ hconj i0 hi0 448 (by norm_num) h448B
    have h118B : uElt 118 ∈ B := by
      rw [← uElt_mul_special (by norm_num) (by norm_num) (by norm_num) uSpecial_check.2.2.2.1]
      exact B.mul_mem h448B h502B
    right; right
    ext g
    constructor
    · intro hg
      obtain ⟨e, he, rfl⟩ := hmem g hg
      exact ⟨e, by rcases he with rfl | rfl | rfl | rfl <;> simp, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · rw [uElt_zero]; exact B.one_mem
      · exact h118B
      · exact h448B
      · exact h502B
  · push Not at h4
    by_cases h1 : uElt 118 ∈ B
    · right; left
      ext g
      constructor
      · intro hg
        obtain ⟨e, he, rfl⟩ := hmem g hg
        rcases he with rfl | rfl | rfl | rfl
        · exact Or.inl uElt_zero
        · exact Or.inr rfl
        · exact absurd hg h4.1
        · exact absurd hg h4.2
      · rintro (rfl | rfl)
        · exact B.one_mem
        · exact h1
    · left
      rw [eq_bot_iff]
      intro g hg
      obtain ⟨e, he, rfl⟩ := hmem g hg
      rcases he with rfl | rfl | rfl | rfl
      · exact (Subgroup.mem_bot).2 uElt_zero
      · exact absurd hg h1
      · exact absurd hg h4.1
      · exact absurd hg h4.2

theorem B1_le_B2 :
    B1 ≤ B2 := by
  rintro _ (rfl | rfl)
  · exact B2.one_mem
  · exact ⟨118, by simp, rfl⟩

theorem B2_le_U :
    B2 ≤ U := by
  rintro _ ⟨c, -, rfl⟩
  exact uElt_mem_U c

theorem quadOn_B2 :
    QuadOn B2 := by
  rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ m hm
  obtain ⟨v, hv, rfl⟩ := exists_η_eq hm
  have hlt : ∀ x ∈ [0, 118, 448, 502], x < 1024 := by decide
  exact (quad_iff (hlt c hc) (hlt c' hc') hv).2
    (uSpecial_check.2.2.2.2.2.2.2.2.2.2.2.2.1 c hc c' hc' v hv)

theorem quadOn_mono {B B' : Subgroup J} (h : B ≤ B') (hq : QuadOn B') : QuadOn B :=
  fun b hb c hc m hm => hq b (h hb) c (h hc) m hm

theorem conj_mem_of_closure {B : Subgroup J} [Finite B]
    (hgen : ∀ i < 4, ∀ b ∈ B, kgen i * b * (kgen i)⁻¹ ∈ B) {u : J} (hu : u ∈ U) :
    ∀ b ∈ B, u * b * u⁻¹ ∈ B := by
  unfold U at hu
  induction hu using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    exact hgen i i.isLt
  | one => intro b hb; rw [one_mul, inv_one, mul_one]; exact hb
  | mul g h _ _ ihg ihh =>
    intro b hb
    rw [show g * h * b * (g * h)⁻¹ = g * (h * b * h⁻¹) * g⁻¹ by group]
    exact ihg _ (ihh b hb)
  | inv g _ ih => exact conj_inv_mem_of_finite ih

theorem conj_mem_B2
    {u : J} (hu : u ∈ U) : ∀ b ∈ B2, u * b * u⁻¹ ∈ B2 := by
  refine conj_mem_of_closure (fun i hi => ?_) hu
  rintro _ ⟨c, hc, rfl⟩
  have hlt : ∀ x ∈ [0, 118, 448, 502], x < 1024 := by decide
  rw [uElt_conj_kgen hi (hlt c hc)]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · rw [← uElt_conj_kgen hi (by norm_num), uElt_zero, mul_one, mul_inv_cancel]
    exact B2.one_mem
  · exact ⟨118, by simp, by rw [uSpecial_check.2.2.2.2.2.2.2.1 i hi]⟩
  · rcases uSpecial_check.2.2.2.2.2.2.2.2.1 i hi with h | h <;> rw [h] <;> exact ⟨_, by simp, rfl⟩
  · rcases uSpecial_check.2.2.2.2.2.2.2.2.2.1 i hi with h | h <;> rw [h] <;>
      exact ⟨_, by simp, rfl⟩

theorem conj_mem_B1
    {u : J} (hu : u ∈ U) : ∀ b ∈ B1, u * b * u⁻¹ ∈ B1 := by
  refine conj_mem_of_closure (fun i hi => ?_) hu
  rintro _ (rfl | rfl)
  · rw [mul_one, mul_inv_cancel]
    exact B1.one_mem
  · rw [uElt_conj_kgen hi (by norm_num), uSpecial_check.2.2.2.2.2.2.2.1 i hi]
    exact Or.inr rfl

theorem uElt_118_ne_one :
    uElt 118 ≠ 1 := fun h =>
  absurd (uElt_injOn (by norm_num) (by norm_num) (h.trans uElt_zero.symm)) (by norm_num)

theorem card_B1 :
    Nat.card B1 = 2 := by
  have e : (B1 : Set J) = {1, uElt 118} := by
    ext g
    simp only [SetLike.mem_coe, mem_B1_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_pair uElt_118_ne_one.symm]

theorem card_B2 :
    Nat.card B2 = 4 := by
  have e : (B2 : Set J) = uElt '' {0, 118, 448, 502} := by
    ext g
    simp only [SetLike.mem_coe, mem_B2_iff, Set.mem_image, List.mem_cons, List.mem_nil_iff,
      or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
  have hinj : Set.InjOn uElt ({0, 118, 448, 502} : Set ℕ) := by
    intro x hx y hy h
    have hlt : ∀ z ∈ ({0, 118, 448, 502} : Set ℕ), z < 1024 := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      omega
    exact uElt_injOn (hlt x hx) (hlt y hy) h
  rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, hinj.ncard_image]
  rw [Set.ncard_insert_of_notMem (by simp), Set.ncard_insert_of_notMem (by simp),
    Set.ncard_pair (by norm_num)]

theorem mem_centralizer_η_iff {g : J} {C : Array ℕ} (hg : ActsBy g C)
    (hC : ∀ j < 11, C[j]?.getD 0 < 2 ^ 11) {a : ℕ} (ha : a < 2048) :
    η a ∈ Subgroup.centralizer {g} ↔ app11 C a = a := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h1
    have e : g * η a * g⁻¹ = η a := by rw [← h1, mul_inv_cancel_right]
    rw [hg] at e
    exact η_injOn (vecMulN_lt hC a) (by omega) e
  · intro h
    have e := hg a
    rw [h] at e
    calc η a * g = g * η a * g⁻¹ * g := by rw [e]
      _ = g * η a := by group

theorem card_centralizer_two_N
    {g g' : J} {C C' : Array ℕ} (hg : ActsBy g C)
    (hg' : ActsBy g' C') (hC : ∀ j < 11, C[j]?.getD 0 < 2 ^ 11)
    (hC' : ∀ j < 11, C'[j]?.getD 0 < 2 ^ 11) :
    Nat.card (Subgroup.centralizer {g} ⊓ Subgroup.centralizer {g'} ⊓ N : Subgroup J) =
      ((Finset.range 2048).filter fun a => app11 C a = a ∧ app11 C' a = a).card := by
  classical
  have hmem : ∀ a, a < 2048 → (η a ∈ (Subgroup.centralizer {g} ⊓ Subgroup.centralizer {g'} ⊓ N :
      Subgroup J) ↔ app11 C a = a ∧ app11 C' a = a) := by
    intro a ha
    rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_centralizer_η_iff hg hC ha,
      mem_centralizer_η_iff hg' hC' ha]
    exact ⟨fun h => h.1, fun h => ⟨h, η_mem_N a⟩⟩
  let f : {a // a ∈ (Finset.range 2048).filter fun a => app11 C a = a ∧ app11 C' a = a} →
      (Subgroup.centralizer {g} ⊓ Subgroup.centralizer {g'} ⊓ N : Subgroup J) := fun a =>
    ⟨η a.1, (hmem a.1 (Finset.mem_range.1 (Finset.mem_filter.1 a.2).1)).2
      (Finset.mem_filter.1 a.2).2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      have h' := Subtype.ext_iff.1 h
      dsimp only [f] at h'
      exact Subtype.ext (η_injOn (by simpa using (Finset.mem_filter.1 ha).1)
        (by simpa using (Finset.mem_filter.1 hb).1) h')
    · rintro ⟨n, hn⟩
      obtain ⟨a, ha, rfl⟩ := exists_η_eq (Subgroup.mem_inf.1 hn).2
      exact ⟨⟨a, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, (hmem a ha).1 hn⟩⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem elem_bound
    {e : ℕ} (he : e < 1024) : ∀ j < 11, (elementColumns[e]!)[j]?.getD 0 < 2 ^ 11 :=
  fun j hj => by rw [← getElem!_eq_getD']; exact (elem_all e he).2.1 j hj

theorem centralizer_B1 :
    Subgroup.centralizer (B1 : Set J) = Subgroup.centralizer {uElt 118} := by
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h _ (Or.inr rfl)).symm
  · rintro h _ (rfl | rfl)
    · rw [one_mul, mul_one]
    · exact h.symm

theorem centralizer_B2 :
    Subgroup.centralizer (B2 : Set J) =
    Subgroup.centralizer {uElt 118} ⊓ Subgroup.centralizer {uElt 448} := by
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨(h _ ⟨118, by simp, rfl⟩).symm, (h _ ⟨448, by simp, rfl⟩).symm⟩
  · rintro ⟨h1, h2⟩ _ ⟨c, hc, rfl⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · rw [uElt_zero, one_mul, mul_one]
    · exact h1.symm
    · exact h2.symm
    · rw [← uElt_mul_special (by norm_num) (by norm_num) (by norm_num)
        uSpecial_check.2.2.2.2.1]
      rw [mul_assoc, ← h2, ← mul_assoc, ← h1, mul_assoc]

theorem card_centralizer_B1 :
    Nat.card (N ⊓ Subgroup.centralizer (B1 : Set J) : Subgroup J) = 2 ^ 7 := by
  rw [centralizer_B1, inf_comm,
    card_centralizer_N_of_actsBy (uElt_acts (by norm_num)) (elem_bound (by norm_num)),
    uSpecial_check.1]
  norm_num

theorem card_centralizer_B2 :
    Nat.card (N ⊓ Subgroup.centralizer (B2 : Set J) : Subgroup J) = 2 ^ 5 := by
  rw [centralizer_B2, inf_comm,
    card_centralizer_two_N (uElt_acts (by norm_num)) (uElt_acts (by norm_num))
      (elem_bound (by norm_num)) (elem_bound (by norm_num)),
    uSpecial_check.2.2.2.2.2.2.2.2.2.2.2.1]
  norm_num

theorem card_centralizer_bot :
    Nat.card (N ⊓ Subgroup.centralizer ((⊥ : Subgroup J) : Set J) : Subgroup J) = 2 ^ 11 := by
  have h : Subgroup.centralizer ((⊥ : Subgroup J) : Set J) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset, Subgroup.coe_bot, Set.singleton_subset_iff]
    exact Subgroup.one_mem _
  rw [h, inf_top_eq, card_N]

theorem R3E_J4_normal_eleven_space_characteristic_in_Sylow_two :
    (N ≤ S0 ∧ (∀ s ∈ S0, ∀ n ∈ N, s * n * s⁻¹ ∈ N) ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧
      Nat.card N = 2048) ∧
    (∀ A : Subgroup J, A ≤ S0 → (∀ s ∈ S0, ∀ a ∈ A, s * a * s⁻¹ ∈ A) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A = 2048 → A = N) ∧
    (N.subgroupOf S0).Characteristic ∧
    (∀ B : Subgroup J, B ≤ U → (∀ u ∈ U, ∀ b ∈ B, u * b * u⁻¹ ∈ B) → QuadOn B →
      B = ⊥ ∨ B = B1 ∨ B = B2) ∧
    (∀ B ∈ [(⊥ : Subgroup J), B1, B2], B ≤ U ∧ (∀ u ∈ U, ∀ b ∈ B, u * b * u⁻¹ ∈ B) ∧
      QuadOn B) ∧
    (Nat.card (⊥ : Subgroup J) = 2 ^ 0 ∧
      Nat.card (N ⊓ Subgroup.centralizer ((⊥ : Subgroup J) : Set J) : Subgroup J) = 2 ^ 11) ∧
    (Nat.card B1 = 2 ^ 1 ∧ Nat.card (N ⊓ Subgroup.centralizer (B1 : Set J) : Subgroup J) = 2 ^ 7) ∧
    (Nat.card B2 = 2 ^ 2 ∧
      Nat.card (N ⊓ Subgroup.centralizer (B2 : Set J) : Subgroup J) = 2 ^ 5) := by
  have hNn : ∀ s ∈ S0, ∀ n ∈ N, s * n * s⁻¹ ∈ N := fun s hs n hn =>
    conj_mem_N_of_mem_H s (S0_le_H hs) n hn
  have huniq : ∀ A : Subgroup J, A ≤ S0 → (∀ s ∈ S0, ∀ a ∈ A, s * a * s⁻¹ ∈ A) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A = 2048 → A = N :=
    fun A hAS hAn hAc hcard => eq_N_of_abelian_normal hAn hAc hAS hcard
  refine ⟨⟨N_le_S0, hNn, N_comm, by rw [card_N]; norm_num⟩, huniq, ?_, fun B hBU hBn hq =>
    quad_normal_eq hBU hBn hq, ?_, ⟨by rw [Subgroup.card_bot, pow_zero], card_centralizer_bot⟩,
    ⟨by rw [card_B1, pow_one], card_centralizer_B1⟩,
    ⟨by rw [card_B2]; norm_num, card_centralizer_B2⟩⟩
  · have h := @characteristic_of_unique J (Subgroup.toGroup J) _ S0 N N_le_S0 hNn N_comm
      (fun A hAS hAn hAc hcard => huniq A hAS hAn hAc (by rw [hcard, card_N]; norm_num))
    exact h
  · intro B hB
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB
    rcases hB with rfl | rfl | rfl
    · refine ⟨bot_le, fun u _ b hb => ?_, quadOn_mono bot_le quadOn_B2⟩
      rw [Subgroup.mem_bot] at hb ⊢
      rw [hb, mul_one, mul_inv_cancel]
    · exact ⟨B1_le_B2.trans B2_le_U, fun u hu => conj_mem_B1 hu, quadOn_mono B1_le_B2 quadOn_B2⟩
    · exact ⟨B2_le_U, fun u hu => conj_mem_B2 hu, quadOn_B2⟩

end CFSG.Sporadic.J4Schreier
