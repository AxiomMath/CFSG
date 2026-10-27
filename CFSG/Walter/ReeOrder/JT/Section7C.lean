module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.Assembly.Defs
public import CFSG.Walter.ReeOrder.JT.Section7A

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups

@[expose] def IsInvolved (X : Type*) [Group X] (G : Type*) [Group G] : Prop :=
  ∃ (K : Subgroup G) (L : Subgroup K) (_ : L.Normal), Nonempty (K ⧸ L ≃* X)

section PSL24

variable {L : Type*} [Group L] [Finite L]

theorem exists_orderOf_three_mem_normalizer_of_psl24 (e : L ≃* PSL(2, GaloisField 2 2))
    (T : Sylow 2 L) :
    ∃ y ∈ Subgroup.normalizer ((T : Subgroup L) : Set L), orderOf y = 3 := by
  have hcard := card_of_psl24 e
  have hT := card_sylow_of_psl24 e T
  have hV := isKleinFour_sylow_of_psl24 e T
  have hsimple := isSimpleGroup_of_psl24 e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyT, hy1⟩ : ∃ y ∈ (T : Subgroup L), y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : (T : Subgroup L) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hT
    omega
  have hCT : Subgroup.centralizer ((T : Subgroup L) : Set L) ≤ T := by
    intro z hz
    have hzy : z ∈ Subgroup.centralizer ({y} : Set L) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyT) hz
    rwa [centralizer_le_of_psl24 e T hyT hy1] at hzy
  have hNC : ¬ Subgroup.normalizer ((T : Subgroup L) : Set L) ≤
      Subgroup.centralizer ((T : Subgroup L) : Set L) := by
    intro hle
    obtain ⟨K, hK, -, hKi, -⟩ := CFSG.GroupTheory.burnside_normal_complement T hle
    rcases hsimple.eq_bot_or_eq_top_of_normal K with h1 | h1
    · rw [h1, Subgroup.index_bot, hcard, hT] at hKi
      omega
    · rw [h1, Subgroup.index_top, hT] at hKi
      omega
  set N := Subgroup.normalizer ((T : Subgroup L) : Set L) with hNdef
  have hTN : (T : Subgroup L) ≤ N := Subgroup.le_normalizer
  have h6 := relIndex_inf_centralizer_dvd_six hV ⊤
  simp only [top_inf_eq] at h6
  have hCeq : Subgroup.centralizer ((T : Subgroup L) : Set L) = T := le_antisymm hCT
    (fun z hz => Subgroup.mem_centralizer_iff.mpr fun w hw =>
      congrArg Subtype.val (hV.isMulCommutative.is_comm.comm ⟨w, hw⟩ ⟨z, hz⟩))
  rw [hCeq] at h6
  have hrel := Subgroup.relIndex_mul_card (T : Subgroup L) N
  rw [inf_eq_left.mpr hTN, hT] at hrel
  have hN60 : Nat.card N ∣ 60 := hcard ▸ Subgroup.card_subgroup_dvd_card N
  have hr15 : (T : Subgroup L).relIndex N ∣ 15 := by
    rw [← hrel] at hN60
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 4)
      (by rw [show (60 : ℕ) = 15 * 4 by norm_num] at hN60; exact hN60)
  have hr1 : (T : Subgroup L).relIndex N ≠ 1 := by
    intro h1
    apply hNC
    rw [hCeq]
    exact Subgroup.relIndex_eq_one.mp h1
  have hr3 : (T : Subgroup L).relIndex N = 3 := by
    have h3 : (T : Subgroup L).relIndex N ∣ Nat.gcd 6 15 := Nat.dvd_gcd h6 hr15
    rw [show Nat.gcd 6 15 = 3 by norm_num] at h3
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h0 | h0
    · exact absurd h0 hr1
    · exact h0
  obtain ⟨⟨z, hz⟩, hzo⟩ := exists_prime_orderOf_dvd_card' (G := N) 3
    (by rw [← hrel, hr3]; norm_num)
  exact ⟨z, hz, by rw [← hzo, Subgroup.orderOf_mk]⟩

end PSL24

theorem three_pow_odd_mod_five (n : ℕ) : 3 ^ (2 * n + 1) % 5 = 2 ∨ 3 ^ (2 * n + 1) % 5 = 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem q_mod_five :
    h.q % 5 = 2 ∨ h.q % 5 = 3 := by
  obtain ⟨n, -, hn⟩ := lemma_4_1 h (h.p_ne_two_of_eq_three hp3) ⟨h.f, by rw [JTHyp.q_eq, hp3]⟩
  rw [hn]
  exact three_pow_odd_mod_five n

omit hp3 in
theorem exists_setup_card_normalizer
    (hp : h.p ≠ 2) {V : Subgroup G} (hV : IsKleinFour V) :
    ∃ s : Setup h, Nat.card (Subgroup.normalizer (V : Set G)) = 24 * Nat.card s.Q := by
  have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV.card_four]; norm_num)
  obtain ⟨⟨v, hvV⟩, hv1⟩ := exists_ne (1 : V)
  have hv2 : orderOf v = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact mul_self_of_isKleinFour' hV hvV)
      (fun h0 => hv1 (Subtype.ext h0))
  obtain ⟨a, ha⟩ := h.exists_conj_eq_t hp hv2
  set V' := V.map (MulAut.conj a).toMonoidHom with hV'def
  have eV : V' ≃* V := (V.equivMapOfInjective _ (MulAut.conj a).injective).symm
  have hV' : IsKleinFour V' :=
    ⟨by rw [Nat.card_congr eV.toEquiv, hV.card_four],
      by rw [Monoid.exponent_eq_of_mulEquiv eV, hV.exponent_two]⟩
  have htV' : h.t ∈ V' := ⟨v, hvV, ha⟩
  have hV'2 : IsPGroup 2 V' := IsPGroup.of_card (n := 2) (by rw [hV'.card_four]; norm_num)
  obtain ⟨S', hS'⟩ := hV'2.exists_le_sylow
  let s : Setup h := ⟨S', hS' htV', V', hS', hV', htV'⟩
  refine ⟨s, ?_⟩
  have hNN : Nat.card (Subgroup.normalizer (V : Set G)) =
      Nat.card (Subgroup.normalizer (V' : Set G)) := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom)
      (MulAut.conj a).injective, Subgroup.map_equiv_normalizer_eq]
  rw [hNN]
  change Nat.card (Subgroup.normalizer (s.T : Set G)) = 24 * Nat.card s.Q
  have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (s.T : Set G))
    (Subgroup.normalizer (s.T : Set G))
  rw [s.relIndex_centralizer_T_normalizer_T hp, inf_eq_left.mpr
    s.centralizer_T_le_normalizer_T, s.card_centralizer_T hp] at h2
  omega

omit hp3 in
theorem card_centralizer_of_orderOf_eq_two
    (hp : h.p ≠ 2) {u : G} (hu : orderOf u = 2) :
    Nat.card (Subgroup.centralizer ({u} : Set G)) = h.q * (h.q ^ 2 - 1) := by
  obtain ⟨a, ha⟩ := h.exists_conj_eq_t hp hu
  have hCC : Nat.card (Subgroup.centralizer ({u} : Set G)) =
      Nat.card (Subgroup.centralizer ({h.t} : Set G)) := by
    have := map_centralizer_singleton_of_injective (MulAut.conj a).toMonoidHom
      (MulAut.conj a).injective u
    rw [MonoidHom.range_eq_top.mpr (MulAut.conj a).surjective, top_inf_eq] at this
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom)
      (MulAut.conj a).injective, this]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ha]
  rw [hCC, h.centralizer_eq]
  have htF : Subgroup.zpowers h.t ≤ Subgroup.normalizer (h.F : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    exact h.commute_of_mem_F hy
  have hdisj : Disjoint (Subgroup.zpowers h.t) h.F := by
    rw [Subgroup.disjoint_def]
    intro y hy hyF
    rcases (mem_zpowers_of_orderOf_eq_two h.orderOf_t).mp hy with rfl | rfl
    · rfl
    · exact absurd hyF h.t_not_mem
  rw [card_sup_eq_mul_of_disjoint htF hdisj, Nat.card_zpowers, h.orderOf_t,
    (h.facts hp).card, ← JTHyp.q_eq]
  have hev : 2 ∣ h.q * (h.q ^ 2 - 1) := by
    have hq := (h.facts hp).odd_p.pow (n := h.f)
    rw [← JTHyp.q_eq] at hq
    obtain ⟨k, hk⟩ := hq
    exact Dvd.dvd.mul_left ⟨2 * k * k + 2 * k, by rw [hk]; ring_nf; omega⟩ _
  omega

theorem five_not_dvd_card_normalizer
    {E : Subgroup G} (hE : IsPGroup 2 E) (hE1 : E ≠ ⊥) :
    ¬ 5 ∣ Nat.card (Subgroup.normalizer (E : Set G)) := by
  have hp := h.p_ne_two_of_eq_three hp3
  have h5 := h.q_mod_five hp3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := hE.exists_le_sylow
  have hS'8 := ((lemma_2_1 h hp).2.1 S').2
  have hE8 : Nat.card E ∣ 8 := hS'8 ▸ Subgroup.card_dvd_of_le hS'
  obtain ⟨k, hk, hEk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card E ∣ 2 ^ 3 by norm_num; exact hE8)
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => h.mul_self_of_isPGroup_two hp3 hE hx
  interval_cases k
  · exact absurd (Subgroup.card_eq_one.mp (by rw [hEk]; rfl)) hE1
  ·
    obtain ⟨u, huE, hu1⟩ : ∃ u ∈ E, u ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hE1 ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq u huE) hu1
    have hEu : E = Subgroup.zpowers u :=
      (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr huE)
        (by rw [Nat.card_zpowers, hu2, hEk]; norm_num)).symm
    rw [hEu, normalizer_zpowers_of_orderOf_eq_two hu2,
      h.card_centralizer_of_orderOf_eq_two hp hu2]
    intro h5'
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h5' with h1 | h1
    · omega
    · have : (h.q ^ 2 - 1) % 5 = 3 := by
        rcases h5 with h2 | h2
        · have : h.q ^ 2 % 5 = 4 := by rw [pow_two, Nat.mul_mod, h2]
          omega
        · have : h.q ^ 2 % 5 = 4 := by rw [pow_two, Nat.mul_mod, h2]
          omega
      omega
  ·
    have hV : IsKleinFour E := by
      refine ⟨by rw [hEk]; norm_num, ?_⟩
      have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hEk]; norm_num)
      refine (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun x hx1 => ?_
      refine orderOf_eq_prime (Subtype.ext ?_) hx1
      rw [SubgroupClass.coe_pow, pow_two]
      exact hsq x x.2
    obtain ⟨s, hs⟩ := h.exists_setup_card_normalizer hp hV
    rw [hs]
    intro h5'
    have h4 := s.four_mul_card_Q hp
    rw [h.eps_eq_one_of_eq_three hp3] at h4
    have h4' : 4 * Nat.card s.Q = h.q + 1 := by exact_mod_cast h4
    have : 5 ∣ Nat.card s.Q := (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 5 24)).mp h5'
    omega
  ·
    have hES : E = S' := Subgroup.eq_of_le_of_card_ge hS' (by rw [hS'8, hEk]; norm_num)
    have h21 := ((lemma_2_1 h hp).2.2.2.2.1 S').1
    have h1 := Subgroup.card_mul_index
      ((S' : Subgroup G).subgroupOf (Subgroup.normalizer ((S' : Subgroup G) : Set G)))
    rw [h21, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv,
      hS'8] at h1
    rw [hES, ← h1]
    norm_num

end JTHyp

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem eq_bot_of_isPGroup_three_of_le_normalizer
    {P W : Subgroup G} (hP : IsPGroup 3 P)
    (hW : IsPGroup 2 W) (hW4 : 4 ∣ Nat.card W)
    (hWP : W ≤ Subgroup.normalizer (P : Set G)) : P = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hW
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdisj : Disjoint W P := by
    rw [Subgroup.disjoint_def]
    intro y hyW hyP
    have h1 : orderOf y ∣ 2 ^ a := ha ▸ Subgroup.orderOf_dvd_natCard W hyW
    have h2 : orderOf y ∣ 3 ^ k := hk ▸ Subgroup.orderOf_dvd_natCard P hyP
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow _ _ (by norm_num)) h1 h2)
  set H := W ⊔ P with hHdef
  have hHcard : Nat.card H = 2 ^ a * 3 ^ k := by
    rw [hHdef, card_sup_eq_mul_of_disjoint hWP hdisj, ha, hk]
  have hHprimes : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 3 := by
    intro r hr hrH
    rw [hHcard] at hrH
    rcases (Nat.Prime.dvd_mul hr).mp hrH with h1 | h1
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h1))
  have hW4' : 4 ∣ Nat.card H := hW4.trans (Subgroup.card_dvd_of_le le_sup_left)
  obtain ⟨⟨P₂, hP₂⟩, -⟩ := h.lemma_7_2 hp3 hHprimes hW4'
  have hWH : W ≤ H := le_sup_left
  have hfacH : (Nat.card H).factorization 2 = a := by
    rw [hHcard, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by
        intro h2
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp
          (Nat.prime_two.dvd_of_dvd_pow h2)
        omega), add_zero]
  let WH : Sylow 2 H := Sylow.ofCard (W.subgroupOf H) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv, ha, hfacH])
  have hWHn : (W.subgroupOf H).Normal := by
    have : Unique (Sylow 2 H) := Sylow.unique_of_normal P₂ hP₂
    have hWP' : WH = P₂ := Subsingleton.elim _ _
    have : (WH : Subgroup H) = W.subgroupOf H := rfl
    rw [← this, hWP']
    exact hP₂
  have hPC : P ≤ Subgroup.centralizer (W : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : y * v * y⁻¹ ∈ W := by
      have := hWHn.conj_mem ⟨v, hWH hv⟩ (by rw [Subgroup.mem_subgroupOf]; exact hv)
        ⟨y, Subgroup.mem_sup_right hy⟩
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    have h2 : v * y⁻¹ * v⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hWP hv) y⁻¹).mp (P.inv_mem hy)
    have h3 : y * v * y⁻¹ * v⁻¹ = 1 := (Subgroup.disjoint_def.mp hdisj)
      (W.mul_mem h1 (W.inv_mem hv))
      (by rw [show y * v * y⁻¹ * v⁻¹ = y * (v * y⁻¹ * v⁻¹) by group]; exact P.mul_mem hy h2)
    calc v * y = (y * v * y⁻¹ * v⁻¹)⁻¹ * y * v := by group
      _ = y * v := by rw [h3, inv_one, one_mul]
  obtain ⟨V₀, hV₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := W) 2 (n := 2)
    (by norm_num; exact hW4)
  set V := V₀.map W.subtype with hVdef
  have hVcard : Nat.card V = 4 := by
    rw [Subgroup.card_map_of_injective W.subtype_injective, hV₀]
    norm_num
  have hVW : V ≤ W := Subgroup.map_subtype_le _
  have hV : IsKleinFour V := by
    refine ⟨hVcard, ?_⟩
    have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hVcard]; norm_num)
    refine (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun x hx1 => ?_
    refine orderOf_eq_prime (Subtype.ext ?_) hx1
    rw [SubgroupClass.coe_pow, pow_two]
    exact h.mul_self_of_isPGroup_two hp3 hW (hVW x.2)
  have hPV : P ≤ Subgroup.centralizer (V : Set G) := hPC.trans (Subgroup.centralizer_le hVW)
  rw [← Subgroup.card_eq_one, hk]
  rcases k with _ | k
  · rfl
  · exfalso
    apply h.three_not_dvd_card_centralizer hp3 hV
    exact (dvd_pow_self 3 (Nat.succ_ne_zero k)).trans (hk ▸ Subgroup.card_dvd_of_le hPV)

theorem exists_commute_of_mem_normalizer_kleinFour
    {V : Subgroup G} (hV : IsKleinFour V)
    {y : G} (hyV : y ∈ Subgroup.normalizer (V : Set G)) (hy : orderOf y = 3) :
    ∃ u : G, orderOf u = 2 ∧ y * u = u * y := by
  have hp := h.p_ne_two_of_eq_three hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV.card_four]; norm_num)
  obtain ⟨⟨v, hvV⟩, hv1⟩ := exists_ne (1 : V)
  have hv2 : orderOf v = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact mul_self_of_isKleinFour' hV hvV)
      (fun h0 => hv1 (Subtype.ext h0))
  obtain ⟨a, ha⟩ := h.exists_conj_eq_t hp hv2
  set V' := V.map (MulAut.conj a).toMonoidHom with hV'def
  have eV : V' ≃* V := (V.equivMapOfInjective _ (MulAut.conj a).injective).symm
  have hV' : IsKleinFour V' :=
    ⟨by rw [Nat.card_congr eV.toEquiv, hV.card_four],
      by rw [Monoid.exponent_eq_of_mulEquiv eV, hV.exponent_two]⟩
  have htV' : h.t ∈ V' := ⟨v, hvV, ha⟩
  have hV'2 : IsPGroup 2 V' := IsPGroup.of_card (n := 2) (by rw [hV'.card_four]; norm_num)
  obtain ⟨S', hS'⟩ := hV'2.exists_le_sylow
  let s : Setup h := ⟨S', hS' htV', V', hS', hV', htV'⟩
  obtain ⟨c, hc⟩ := s.exists_config hp
  set y' := a * y * a⁻¹ with hy'def
  have hy' : orderOf y' = 3 := by rw [hy'def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  have hy'N : y' ∈ Subgroup.normalizer (c.T : Set G) := by
    rw [hc]
    change a * y * a⁻¹ ∈ Subgroup.normalizer ((V.map (MulAut.conj a).toMonoidHom : Subgroup G) :
      Set G)
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨y, hyV, rfl⟩
  set N := Subgroup.normalizer (c.T : Set G) with hNdef
  have hNcard : Nat.card N = 24 * Nat.card c.Q := by
    have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (c.T : Set G)) N
    rw [c.toSetup.relIndex_centralizer_T_normalizer_T hp, inf_eq_left.mpr
      c.toSetup.centralizer_T_le_normalizer_T, c.toSetup.card_centralizer_T hp] at h2
    omega
  have h3Q := c.toSetup.three_not_dvd_card_Q hp3
  have hfac : (Nat.card N).factorization 3 = 1 := by
    rw [hNcard, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
      show (24 : ℕ) = 3 * 8 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd h3Q]
  let P₁ : Sylow 3 N := Sylow.ofCard (Subgroup.zpowers (⟨y', hy'N⟩ : N)) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hy', hfac, pow_one])
  let P₂ : Sylow 3 N := Sylow.ofCard (Subgroup.zpowers (⟨c.μ, c.μ_mem_NT⟩ : N)) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, c.orderOf_μ, hfac, pow_one])
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N P₂ P₁
  have hy'mem : (⟨y', hy'N⟩ : N) ∈ (n • P₂ : Sylow 3 N) := by
    rw [hn]
    exact Subgroup.mem_zpowers _
  obtain ⟨z, hz, hzy⟩ := hy'mem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hy'eq : y' = (n : G) * c.μ ^ k * (n : G)⁻¹ := by
    have := congrArg Subtype.val hzy
    simpa using this.symm
  refine ⟨a⁻¹ * ((n : G) * c.t₁ * (n : G)⁻¹) * a, ?_, ?_⟩
  · rw [show a⁻¹ * ((n : G) * c.t₁ * (n : G)⁻¹) * a =
      (a⁻¹ * (n : G)) * c.t₁ * (a⁻¹ * (n : G))⁻¹ by group, ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, c.orderOf_t₁]
  · have hcomm : c.μ ^ k * c.t₁ = c.t₁ * c.μ ^ k := (Commute.zpow_left c.comm k).eq
    have hy : y = a⁻¹ * y' * a := by rw [hy'def]; group
    rw [hy, hy'eq]
    calc a⁻¹ * ((n : G) * c.μ ^ k * (n : G)⁻¹) * a * (a⁻¹ * ((n : G) * c.t₁ * (n : G)⁻¹) * a) =
        a⁻¹ * (n : G) * (c.μ ^ k * c.t₁) * (n : G)⁻¹ * a := by group
      _ = a⁻¹ * (n : G) * (c.t₁ * c.μ ^ k) * (n : G)⁻¹ * a := by rw [hcomm]
      _ = _ := by group

end JTHyp

section Quotient

theorem map_normalizer_le {G : Type*} [Group G] [Finite G] {K : Subgroup G} (E : Subgroup K) :
    (Subgroup.normalizer (E : Set K)).map K.subtype ≤
      Subgroup.normalizer ((E.map K.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨n, hn, rfl⟩
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨e, he, rfl⟩ := hx
  exact ⟨n * e * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn e).mp he, rfl⟩

theorem card_quotient_dvd_of_sup_eq_top {K : Type*} [Group K] [Finite K] {L N : Subgroup K}
    [L.Normal] (hNL : N ⊔ L = ⊤) : Nat.card (K ⧸ L) ∣ Nat.card N := by
  have hmap : N.map (QuotientGroup.mk' L) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective L x
    have hk : k ∈ N ⊔ L := hNL ▸ Subgroup.mem_top k
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      Subgroup.le_normalizer_of_normal] at hk
    obtain ⟨n, hn, l, hl, rfl⟩ := hk
    refine ⟨n, hn, ?_⟩
    have hl1 : (QuotientGroup.mk' L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [map_mul, hl1, mul_one]
  have := Subgroup.card_map_dvd (H := N) (QuotientGroup.mk' L)
  rwa [hmap, Subgroup.card_top] at this

end Quotient

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem odd_card_of_psl24_section
    {K : Subgroup G} {L : Subgroup K} [L.Normal]
    (e : K ⧸ L ≃* PSL(2, GaloisField 2 2)) : ¬ 2 ∣ Nat.card L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA60 : Nat.card (K ⧸ L) = 60 := card_of_psl24 e
  intro h2
  obtain ⟨S₂⟩ : Nonempty (Sylow 2 L) := inferInstance
  have hS₂2 : 2 ∣ Nat.card (S₂ : Subgroup L) := by
    have := Sylow.pow_dvd_card_of_pow_dvd_card S₂ (n := 1) (by rw [pow_one]; exact h2)
    rwa [pow_one] at this
  set E := (S₂ : Subgroup L).map L.subtype with hEdef
  have h60 := card_quotient_dvd_of_sup_eq_top (Sylow.normalizer_sup_eq_top S₂)
  rw [hA60] at h60
  set E' := E.map K.subtype with hE'def
  have hE'card : Nat.card E' = Nat.card (S₂ : Subgroup L) := by
    rw [hE'def, Subgroup.card_map_of_injective K.subtype_injective, hEdef,
      Subgroup.card_map_of_injective L.subtype_injective]
  have hE'2 : IsPGroup 2 E' := (S₂.isPGroup'.map _).map _
  have hE'1 : E' ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hE'card
    rw [← hE'card] at hS₂2
    omega
  apply h.five_not_dvd_card_normalizer hp3 hE'2 hE'1
  have := Subgroup.card_dvd_of_le (map_normalizer_le E)
  rw [Subgroup.card_map_of_injective K.subtype_injective] at this
  exact ((by norm_num : 5 ∣ 60).trans h60).trans this

theorem three_not_dvd_card_of_psl24_section
    {K : Subgroup G} {L : Subgroup K} [L.Normal]
    (e : K ⧸ L ≃* PSL(2, GaloisField 2 2)) : ¬ 3 ∣ Nat.card L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA60 : Nat.card (K ⧸ L) = 60 := card_of_psl24 e
  intro h3
  obtain ⟨S₃⟩ : Nonempty (Sylow 3 L) := inferInstance
  have hS₃3 : 3 ∣ Nat.card (S₃ : Subgroup L) := by
    have := Sylow.pow_dvd_card_of_pow_dvd_card S₃ (n := 1) (by rw [pow_one]; exact h3)
    rwa [pow_one] at this
  set E := (S₃ : Subgroup L).map L.subtype with hEdef
  set N₂ := Subgroup.normalizer (E : Set K) with hN₂def
  have h60 := card_quotient_dvd_of_sup_eq_top (Sylow.normalizer_sup_eq_top S₃)
  rw [hA60] at h60
  obtain ⟨W₀, hW₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := N₂) 2 (n := 2)
    (((by norm_num : 2 ^ 2 ∣ 60)).trans h60)
  set W := (W₀.map N₂.subtype).map K.subtype with hWdef
  have hWcard : Nat.card W = 4 := by
    rw [hWdef, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective N₂.subtype_injective, hW₀]
    norm_num
  set E' := E.map K.subtype with hE'def
  have hWE' : W ≤ Subgroup.normalizer (E' : Set G) :=
    (Subgroup.map_mono (Subgroup.map_subtype_le W₀)).trans (map_normalizer_le E)
  have hE'3 : IsPGroup 3 E' := (S₃.isPGroup'.map _).map _
  have hE'card : Nat.card E' = Nat.card (S₃ : Subgroup L) := by
    rw [hE'def, Subgroup.card_map_of_injective K.subtype_injective, hEdef,
      Subgroup.card_map_of_injective L.subtype_injective]
  have hbot := h.eq_bot_of_isPGroup_three_of_le_normalizer hp3 hE'3
    (IsPGroup.of_card (n := 2) (by rw [hWcard]; norm_num)) (by rw [hWcard]) hWE'
  rw [hbot, Subgroup.card_bot] at hE'card
  rw [← hE'card] at hS₃3
  omega

end JTHyp

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem lemma_7_6 :
    ¬ IsInvolved PSL(2, GaloisField 2 2) G := by
  classical
  rintro ⟨K, L, hL, ⟨e⟩⟩
  have hp := h.p_ne_two_of_eq_three hp3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA60 : Nat.card (K ⧸ L) = 60 := card_of_psl24 e
  have hKL : Nat.card K = 60 * Nat.card L := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup L, hA60]
  have hL2 := h.odd_card_of_psl24_section hp3 e
  have hL3 := h.three_not_dvd_card_of_psl24_section hp3 e
  set φ : K →* K ⧸ L := QuotientGroup.mk' L with hφdef
  have hφeq : ∀ a b : K, φ a = φ b ↔ a⁻¹ * b ∈ L := fun a b => QuotientGroup.eq
  have hfacK : (Nat.card K).factorization 2 = 2 := by
    rw [hKL, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
      show (60 : ℕ) = 2 ^ 2 * 15 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hL2]
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hT₀card : Nat.card (T₀ : Subgroup K) = 4 := by
    rw [Sylow.card_eq_multiplicity, hfacK]
    norm_num
  set T₀' := (T₀ : Subgroup K).map K.subtype with hT₀'def
  have hT₀'card : Nat.card T₀' = 4 := by
    rw [hT₀'def, Subgroup.card_map_of_injective K.subtype_injective, hT₀card]
  have hT₀'2 : IsPGroup 2 T₀' := T₀.isPGroup'.map _
  have hV : IsKleinFour T₀' := by
    refine ⟨hT₀'card, ?_⟩
    have : Nontrivial T₀' := Finite.one_lt_card_iff_nontrivial.mp (by rw [hT₀'card]; norm_num)
    refine (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun x hx1 => ?_
    refine orderOf_eq_prime (Subtype.ext ?_) hx1
    rw [SubgroupClass.coe_pow, pow_two]
    exact h.mul_self_of_isPGroup_two hp3 hT₀'2 x.2
  have hdisj : Disjoint (T₀ : Subgroup K) L := by
    rw [Subgroup.disjoint_def]
    intro x hxT hxL
    have h1 : orderOf x ∣ 4 := hT₀card ▸ Subgroup.orderOf_dvd_natCard _ hxT
    have h2 : orderOf x ∣ Nat.card L := Subgroup.orderOf_dvd_natCard _ hxL
    have hcop : Nat.Coprime 4 (Nat.card L) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hL2)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hinj : Set.InjOn φ ((T₀ : Subgroup K) : Set K) := by
    intro x hx y hy hxy
    have := (hφeq x y).mp hxy
    have h1 : x⁻¹ * y = 1 := (Subgroup.disjoint_def.mp hdisj)
      ((T₀ : Subgroup K).mul_mem ((T₀ : Subgroup K).inv_mem hx) hy) this
    calc x = x * (x⁻¹ * y) := by rw [h1, mul_one]
      _ = y := by group
  set Tb := (T₀ : Subgroup K).map φ with hTbdef
  have hTbcard : Nat.card Tb = 4 := by
    rw [← hT₀card, ← SetLike.coe_sort_coe, hTbdef, Subgroup.coe_map,
      Nat.card_image_of_injOn hinj]
    rfl
  have hfacA : (Nat.card (K ⧸ L)).factorization 2 = 2 := by
    rw [hA60, show (60 : ℕ) = 2 ^ 2 * 15 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let TbS : Sylow 2 (K ⧸ L) := Sylow.ofCard Tb (by rw [hTbcard, hfacA]; norm_num)
  obtain ⟨yb, hybN, hyb3⟩ := exists_orderOf_three_mem_normalizer_of_psl24 e TbS
  change yb ∈ Subgroup.normalizer (Tb : Set (K ⧸ L)) at hybN
  set X := (T₀ : Subgroup K) ⊔ L with hXdef
  have hXcomap : X = Tb.comap φ := by
    apply le_antisymm
    · refine sup_le (Subgroup.le_comap_map _ _) (fun l hl => ?_)
      change φ l ∈ Tb
      have hl1 : φ l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
      rw [hl1]
      exact Tb.one_mem
    · intro k hk
      obtain ⟨τ, hτ, hτk⟩ := hk
      have := (hφeq τ k).mp hτk
      rw [show k = τ * (τ⁻¹ * k) by group]
      exact X.mul_mem (Subgroup.mem_sup_left hτ) (Subgroup.mem_sup_right this)
  have hLN : (T₀ : Subgroup K) ≤ Subgroup.normalizer (L : Set K) :=
    fun _ _ => Subgroup.le_normalizer_of_normal (Subgroup.mem_top _)
  have hXcard : Nat.card X = 4 * Nat.card L := by
    rw [hXdef, card_sup_eq_mul_of_disjoint hLN hdisj, hT₀card]
  have hfacX : (Nat.card X).factorization 2 = 2 := by
    rw [hXcard, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
      show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hL2]
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective L yb
  change φ a = yb at ha
  have haX : ∀ τ ∈ (T₀ : Subgroup K), a * τ * a⁻¹ ∈ X := by
    intro τ hτ
    rw [hXcomap]
    change φ (a * τ * a⁻¹) ∈ Tb
    rw [map_mul, map_mul, map_inv, ha]
    exact (Subgroup.mem_normalizer_iff.mp hybN (φ τ)).mp ⟨τ, hτ, rfl⟩
  have hT₀X : (T₀ : Subgroup K) ≤ X := le_sup_left
  have haT₀X : (T₀ : Subgroup K).map (MulAut.conj a).toMonoidHom ≤ X := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact haX τ hτ
  let P₁ : Sylow 2 X := Sylow.ofCard ((T₀ : Subgroup K).subgroupOf X) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₀X).toEquiv, hT₀card, hfacX]
    norm_num)
  let P₂ : Sylow 2 X := Sylow.ofCard
    (((T₀ : Subgroup K).map (MulAut.conj a).toMonoidHom).subgroupOf X) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe haT₀X).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj a).injective, hT₀card, hfacX]
    norm_num)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X P₂ P₁
  have hy₁N : (x : K) * a ∈ Subgroup.normalizer ((T₀ : Subgroup K) : Set K) := by
    refine mem_normalizer_of_conj_mem fun τ hτ => ?_
    have hmem : (⟨a * τ * a⁻¹, haX τ hτ⟩ : X) ∈ (P₂ : Subgroup X) := by
      change _ ∈ ((T₀ : Subgroup K).map (MulAut.conj a).toMonoidHom).subgroupOf X
      rw [Subgroup.mem_subgroupOf]
      exact ⟨τ, hτ, rfl⟩
    have hmem' : x * ⟨a * τ * a⁻¹, haX τ hτ⟩ * x⁻¹ ∈ (P₁ : Subgroup X) := by
      rw [← hx]
      exact ⟨_, hmem, rfl⟩
    change _ ∈ (T₀ : Subgroup K).subgroupOf X at hmem'
    rw [Subgroup.mem_subgroupOf] at hmem'
    simpa [mul_assoc] using hmem'
  have hxTb : φ x ∈ Tb := by
    have : (x : K) ∈ Tb.comap φ := hXcomap ▸ x.2
    exact this
  obtain ⟨τ₀, hτ₀, hτ₀x⟩ := hxTb
  set y₂ := τ₀⁻¹ * ((x : K) * a) with hy₂def
  have hy₂N : y₂ ∈ Subgroup.normalizer ((T₀ : Subgroup K) : Set K) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hτ₀)) hy₁N
  have hy₂φ : φ y₂ = yb := by
    rw [hy₂def, map_mul, map_mul, map_inv, hτ₀x, ha]
    group
  obtain ⟨e₃, m, hm3, ho⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y₂).ne' 3
    (by norm_num)
  set y := y₂ ^ m with hydef
  have hm0 : m ≠ 0 := fun h0 => by rw [h0, mul_zero] at ho; exact (orderOf_pos y₂).ne' ho
  have hyo : orderOf y = 3 ^ e₃ := by
    rw [hydef, orderOf_pow_of_dvd hm0 (ho ▸ dvd_mul_left m _), ho,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hφy : orderOf (φ y) = 3 := by
    rw [hydef, map_pow, hy₂φ, Nat.Coprime.orderOf_pow (by
      rw [hyb3]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3), hyb3]
  have hyN : y ∈ Subgroup.normalizer ((T₀ : Subgroup K) : Set K) := Subgroup.pow_mem _ hy₂N m
  have hyN' : (y : G) ∈ Subgroup.normalizer (T₀' : Set G) := map_normalizer_le _ ⟨y, hyN, rfl⟩
  have hy3 : orderOf (y : G) = 3 := by
    rw [Subgroup.orderOf_coe, hyo]
    rcases e₃ with _ | _ | e₃
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hyo
      rw [hyo, map_one, orderOf_one] at hφy
      omega
    · rfl
    · exfalso
      obtain ⟨s, hs⟩ := h.exists_setup_card_normalizer hp hV
      have h9 : 3 ^ (e₃ + 2) ∣ Nat.card (Subgroup.normalizer (T₀' : Set G)) := by
        rw [← hyo, ← Subgroup.orderOf_coe]
        exact Subgroup.orderOf_dvd_natCard _ hyN'
      rw [hs] at h9
      have h9' : 3 ^ 2 ∣ 24 * Nat.card s.Q := (pow_dvd_pow 3 (by omega)).trans h9
      have := s.three_not_dvd_card_Q hp3
      apply this
      have h3 : 3 ∣ 8 * Nat.card s.Q := by
        rw [show (24 : ℕ) = 3 * 8 by norm_num, mul_assoc, show (3 : ℕ) ^ 2 = 3 * 3 by norm_num]
          at h9'
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9'
      exact (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 3 8)).mp h3
  obtain ⟨u, hu2, hyu⟩ := h.exists_commute_of_mem_normalizer_kleinFour hp3 hV hyN' hy3
  obtain ⟨ab, -, hab⟩ := exists_inv_of_orderOf_three_of_psl24 e hφy
  obtain ⟨a₁, ha₁⟩ := QuotientGroup.mk'_surjective L ab
  change φ a₁ = ab at ha₁
  have hyK3 : orderOf y = 3 := by rw [← hy3, Subgroup.orderOf_coe]
  set Z := Subgroup.zpowers y ⊔ L with hZdef
  have hdisjZ : Disjoint (Subgroup.zpowers y) L := by
    rw [Subgroup.disjoint_def]
    intro z hz hzL
    have h1 : orderOf z ∣ 3 := hyK3 ▸ orderOf_dvd_of_mem_zpowers hz
    have h2 : orderOf z ∣ Nat.card L := Subgroup.orderOf_dvd_natCard _ hzL
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hL3) h1 h2)
  have hyLN : Subgroup.zpowers y ≤ Subgroup.normalizer (L : Set K) :=
    fun _ _ => Subgroup.le_normalizer_of_normal (Subgroup.mem_top _)
  have hZcard : Nat.card Z = 3 * Nat.card L := by
    rw [hZdef, card_sup_eq_mul_of_disjoint hyLN hdisjZ, Nat.card_zpowers, hyK3]
  have hfacZ : (Nat.card Z).factorization 3 = 1 := by
    rw [hZcard, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd hL3]
  have hyZ : Subgroup.zpowers y ≤ Z := le_sup_left
  have ha₁Z : a₁ * y * a₁⁻¹ ∈ Z := by
    have h1 : φ (a₁ * y * a₁⁻¹) = φ y⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv, ha₁, hab]
    have h2 := (hφeq _ _).mp h1.symm
    rw [show a₁ * y * a₁⁻¹ = y⁻¹ * ((y⁻¹)⁻¹ * (a₁ * y * a₁⁻¹)) by group]
    exact Z.mul_mem (hyZ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)))
      (Subgroup.mem_sup_right h2)
  have hzZ : Subgroup.zpowers (a₁ * y * a₁⁻¹) ≤ Z := (Subgroup.zpowers_le).mpr ha₁Z
  let P₃ : Sylow 3 Z := Sylow.ofCard ((Subgroup.zpowers y).subgroupOf Z) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyZ).toEquiv, Nat.card_zpowers, hyK3,
      hfacZ, pow_one])
  let P₄ : Sylow 3 Z := Sylow.ofCard ((Subgroup.zpowers (a₁ * y * a₁⁻¹)).subgroupOf Z) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzZ).toEquiv, Nat.card_zpowers,
      ← MulAut.conj_apply, MulEquiv.orderOf_eq, hyK3, hfacZ, pow_one])
  obtain ⟨x', hx'⟩ := MulAction.exists_smul_eq Z P₄ P₃
  set g := (x' : K) * a₁ with hgdef
  have hgy : g * y * g⁻¹ ∈ Subgroup.zpowers y := by
    have hmem : (⟨a₁ * y * a₁⁻¹, ha₁Z⟩ : Z) ∈ (P₄ : Subgroup Z) := by
      change _ ∈ (Subgroup.zpowers (a₁ * y * a₁⁻¹)).subgroupOf Z
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_zpowers _
    have hmem' : x' * ⟨a₁ * y * a₁⁻¹, ha₁Z⟩ * x'⁻¹ ∈ (P₃ : Subgroup Z) := by
      rw [← hx']
      exact ⟨_, hmem, rfl⟩
    change _ ∈ (Subgroup.zpowers y).subgroupOf Z at hmem'
    rw [Subgroup.mem_subgroupOf] at hmem'
    rw [hgdef]
    simpa [mul_assoc] using hmem'
  have hφx' : φ x' * φ y = φ y * φ x' := by
    have hx'Z : (x' : K) ∈ Subgroup.zpowers y ⊔ L := x'.2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hyLN] at hx'Z
    obtain ⟨z, hz, l, hl, hzl⟩ := hx'Z
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hl1 : φ l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [← hzl, map_mul, hl1, mul_one, map_zpow]
    exact (Commute.zpow_left (Commute.refl (φ y)) k).eq
  have hφg : φ (g * y * g⁻¹) = (φ y)⁻¹ := by
    have hg' : φ g = φ x' * ab := by rw [hgdef, map_mul, ha₁]
    rw [map_mul, map_mul, map_inv, hg']
    calc φ ↑x' * ab * φ y * (φ ↑x' * ab)⁻¹ = φ ↑x' * (ab * φ y * ab⁻¹) * (φ ↑x')⁻¹ := by
          group
      _ = φ ↑x' * (φ y)⁻¹ * (φ ↑x')⁻¹ := by rw [hab]
      _ = (φ ↑x' * φ y * (φ ↑x')⁻¹)⁻¹ := by group
      _ = (φ y)⁻¹ := by rw [hφx', mul_inv_cancel_right]
  have hgy' : g * y * g⁻¹ = y⁻¹ := by
    rcases (mem_zpowers_iff_of_orderOf_three hyK3).mp hgy with h1 | h1 | h1
    · exfalso
      have : y = 1 := by
        have := congrArg (fun w => g⁻¹ * w * g) h1
        simpa [mul_assoc] using this
      rw [this, orderOf_one] at hyK3
      omega
    · exfalso
      rw [h1] at hφg
      have : φ y ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 1 [hφg]
        exact inv_mul_cancel _
      have := orderOf_dvd_of_pow_eq_one this
      rw [hφy] at this
      omega
    · rw [h1, ← inv_eq_of_mul_eq_one_right (show y * y ^ 2 = 1 by
        rw [← pow_succ']; exact pow_three_eq_one_of_orderOf hyK3)]
  refine h.lemma_7_1_a hp3 (x := (y : G)) (u := u) hy3 hu2 hyu (g : G) ?_
  have := congrArg Subtype.val hgy'
  simpa using this

end JTHyp

end CFSG.Walter.JT
