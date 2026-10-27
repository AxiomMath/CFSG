module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Setting
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Cases
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace L15422

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_isSylowTwoOf_of_le {S S' H : Subgroup G} (hS : IsSylowTwoOf S H) (hSS' : S ≤ S')
    (hS'H : S' ≤ H) (hS' : IsPGroup 2 S') : S' = S := by
  have hmul := Subgroup.relIndex_mul_relIndex S S' H hSS' hS'H
  have hSH : ¬ 2 ∣ S.relIndex H := hS.2.2
  have hodd : ¬ 2 ∣ S.relIndex S' := fun h => hSH (hmul ▸ Dvd.dvd.mul_right h _)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS'
  have hdvd : S.relIndex S' ∣ 2 ^ a := ha ▸ Subgroup.relIndex_dvd_card S S'
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hb0 : b = 0 := by
    by_contra hb0
    exact hodd (hb ▸ dvd_pow_self 2 hb0)
  rw [hb0, pow_zero] at hb
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hb) hSS'

omit [Finite G] in
theorem isPGroup_zpowers_of_sq {z : G} (hz : z ^ 2 = 1) : IsPGroup 2 (Subgroup.zpowers z) := by
  have hdvd : orderOf z ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact hz)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

end Sylow

variable {G : Type} [Group G] [Finite G] {T : Subgroup G} (s : Setting15419 G T)

omit [Finite G] in
theorem isSylowTwoOf_T₀ (h19 : Stmt15419 G T) (h20 : Stmt15420 G T) :
    IsSylowTwoOf s.T₀ s.I :=
  h20 s s.I ⟨le_rfl, (h19 s).2.2.1⟩

omit [Finite G] in
theorem T₀_le_I : s.T₀ ≤ s.I := le_sup_right.trans le_sup_left

omit [Finite G] in
theorem omegaOneCenter_le_T₀ : quasithinOmegaOneCenter T ≤ s.T₀ := by
  have hZ : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun z hz => hz.1
  have hET : omegaOneCenterOf (thompsonJ T) ≤ T :=
    ((B2F.omegaOneCenterOf_le_centerOf _).trans inf_le_left).trans (thompsonJ_le_self T)
  exact (hZ.trans (le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le hET)))).trans
    (baum_le_T₀ s)

theorem inf_normalizer_eq_T₀ (hyp : MultipleCentralizerHypothesis G T) (h19 : Stmt15419 G T)
    (h20 : Stmt15420 G T) :
    T ⊓ Subgroup.normalizer (pCoreOf 2 s.I : Set G) = s.T₀ ∧
      IsSylowTwoOf s.T₀ (Subgroup.normalizer (pCoreOf 2 s.I : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (pCoreOf 2 s.I : Set G) with hHdef
  have hIH : s.I ≤ H := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 s.I
  have hle : pCoreOf 2 s.I ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 s.I).trans hIH) le_rfl
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 s.I)
  have hH : InH s.I H := ⟨hIH, fun hb => (h19 s).2.2.1 (le_bot_iff.mp (hb ▸ hle))⟩
  have hsyl := h20 s H hH
  refine ⟨eq_of_isSylowTwoOf_of_le hsyl (le_inf (T₀_le s) ((T₀_le_I s).trans hIH)) inf_le_right
    (hyp.sylow.1.to_le inf_le_left), hsyl⟩

theorem stmt15417_apply (hyp : MultipleCentralizerHypothesis G T) (h17 : Stmt15417 G T)
    (h19 : Stmt15419 G T) (h20 : Stmt15420 G T) :
    (∀ z ∈ quasithinOmegaOneCenter T, z ≠ 1 → ∀ Mz : Subgroup G,
      InM (Subgroup.centralizer ({z} : Set G)) Mz → Lemma115Hyp s.I s.T₀ Mz z) ∧
    (quasithinOmegaOneCenter T ⊓ pCoreOf 2 s.I ≠ ⊥ → CharTwo s.I) := by
  have hT₀ := isSylowTwoOf_T₀ s h19 h20
  obtain ⟨heq, hsyl⟩ := inf_normalizer_eq_T₀ s hyp h19 h20
  have h := h17 (pCoreOf 2 s.I) (Subgroup.normalizer (pCoreOf 2 s.I : Set G)) s.I
    (h19 s).2.2.1 ((CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hT₀).trans (T₀_le s))
    (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)) le_rfl
    (by rw [heq]; exact hsyl) (by rw [heq]; exact T₀_le_I s)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 s.I)
  rw [heq] at h
  exact h

theorem omegaOneCenter_inf_pCoreOf_eq_bot (hyp : MultipleCentralizerHypothesis G T)
    (h17 : Stmt15417 G T) (h19 : Stmt15419 G T) (h20 : Stmt15420 G T) (hI : ¬ CharTwo s.I) :
    quasithinOmegaOneCenter T ⊓ pCoreOf 2 s.I = ⊥ := by
  by_contra h
  exact hI ((stmt15417_apply s hyp h17 h19 h20).2 h)

theorem exists_lemma115Hyp (hyp : MultipleCentralizerHypothesis G T) (h17 : Stmt15417 G T)
    (h19 : Stmt15419 G T) (h20 : Stmt15420 G T) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    ∃ Mz : Subgroup G, Lemma115Hyp s.I s.T₀ Mz z := by
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hz).2.2
  have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers z : Set G)) :=
    ⟨Subgroup.zpowers z, Subgroup.zpowers_ne_bot.mpr hz1, isPGroup_zpowers_of_sq hz2, rfl⟩
  obtain ⟨M, hM, hle⟩ := exists_maxTwoLocal_ge hloc
  have hC : Subgroup.centralizer ({z} : Set G) ≤ M := by
    have h : Subgroup.centralizer ({z} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [h]
    exact (Subgroup.centralizer_le_normalizer _).trans hle
  exact ⟨M, (stmt15417_apply s hyp h17 h19 h20).1 z hz hz1 M ⟨hM, hC⟩⟩

theorem charTwo_inf_centralizer (hyp : MultipleCentralizerHypothesis G T) (h17 : Stmt15417 G T)
    (h19 : Stmt15419 G T) (h20 : Stmt15420 G T) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    CharTwo (s.I ⊓ Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨Mz, h⟩ := exists_lemma115Hyp s hyp h17 h19 h20 hz hz1
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hz).2.2
  have hzI : z ∈ s.I := T₀_le_I s (omegaOneCenter_le_T₀ s hz)
  have hzM : z ∈ Mz := h.centralizer_z_le (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hX : Subgroup.zpowers z ≤ s.I ⊓ Mz := Subgroup.zpowers_le.mpr ⟨hzI, hzM⟩
  have hc := h.charTwo_inf.inf_centralizer hX (isPGroup_zpowers_of_sq hz2)
  have heq : s.I ⊓ Mz ⊓ Subgroup.centralizer (Subgroup.zpowers z : Set G) =
      s.I ⊓ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    refine le_antisymm (inf_le_inf_right _ inf_le_left)
      (le_inf (le_inf inf_le_left ?_) inf_le_right)
    exact fun x hx => h.centralizer_z_le hx.2
  rwa [heq] at hc

theorem inverts_oddCoreIn (hyp : MultipleCentralizerHypothesis G T) (h17 : Stmt15417 G T)
    (h19 : Stmt15419 G T) (h20 : Stmt15420 G T) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    ∀ y ∈ oddCoreIn s.I, z⁻¹ * y * z = y⁻¹ := by
  obtain ⟨Mz, h⟩ := exists_lemma115Hyp s hyp h17 h19 h20 hz hz1
  exact h.inverts_oddCoreIn

theorem sq_eq_one_of_mem_oddCoreIn (hyp : MultipleCentralizerHypothesis G T)
    (hnot : ¬ IsLThreeTwoOrASix G) (h14 : Stmt15414 G T) (h17 : Stmt15417 G T)
    (h19 : Stmt15419 G T) (h20 : Stmt15420 G T) {y : G} (hy : y ∈ oddCoreIn s.I) :
    y ^ 2 = 1 := by
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_ne_of_card_eq_four (h14 hnot).2
  have hab1 : a * b ≠ 1 := by
    intro h
    have hb2 : b ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hb).2.2
    apply hab
    calc a = a * b * b := by rw [mul_assoc, ← sq, hb2, mul_one]
      _ = b := by rw [h, one_mul]
  have h1 := inverts_oddCoreIn s hyp h17 h19 h20 ha ha1 y hy
  have h2 := inverts_oddCoreIn s hyp h17 h19 h20 hb hb1 y hy
  have h3 := inverts_oddCoreIn s hyp h17 h19 h20 (Subgroup.mul_mem _ ha hb) hab1 y hy
  have h4 : (a * b)⁻¹ * y * (a * b) = y := by
    calc (a * b)⁻¹ * y * (a * b) = b⁻¹ * (a⁻¹ * y * a) * b := by group
      _ = b⁻¹ * y⁻¹ * b := by rw [h1]
      _ = (b⁻¹ * y * b)⁻¹ := by group
      _ = y := by rw [h2, inv_inv]
  rw [h4] at h3
  calc y ^ 2 = y * y := sq y
    _ = y * y⁻¹ := by rw [← h3]
    _ = 1 := mul_inv_cancel y

omit [Finite G] in
theorem exists_mem_centralizer_of_isYFamily (hnot : ¬ IsLThreeTwoOrASix G)
    (h14 : Stmt15414 G T) {X : Subgroup G} (hX : IsYFamily T X) :
    ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧ z ∈ Subgroup.centralizer (X : Set G) := by
  have h1 := (h14 hnot).1 X hX
  have h2 := (h14 hnot).2
  have h3 := Subgroup.relIndex_mul_card
    (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (X : Set G)) (quasithinOmegaOneCenter T)
  rw [h1, h2, inf_right_comm, inf_idem] at h3
  have hne : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at h3
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨z, hz.1, fun h => hz1 (Subtype.ext h), hz.2⟩

omit [Finite G] in
theorem mem_centralizer_sup {L : Subgroup G} {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hzL : z ∈ Subgroup.centralizer (L : Set G)) :
    z ∈ Subgroup.centralizer ((L ⊔ s.T₀ : Subgroup G) : Set G) := by
  have hzT : z ∈ Subgroup.centralizer (T : Set G) := (mem_quasithinOmegaOneCenter_iff.mp hz).2.1
  have hle : L ⊔ s.T₀ ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hzL) x hx)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hzT) x (T₀_le s hx))
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

omit [Finite G] in
theorem exists_mem_centralizer_G₁ (hnot : ¬ IsLThreeTwoOrASix G) (h14 : Stmt15414 G T) :
    ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧ z ∈ Subgroup.centralizer (s.G₁ : Set G) := by
  obtain ⟨z, hz, hz1, hzX⟩ := exists_mem_centralizer_of_isYFamily hnot h14 s.famX
  exact ⟨z, hz, hz1, mem_centralizer_sup s hz
    (Subgroup.centralizer_le (factor_L₁ s).le hzX)⟩

omit [Finite G] in
theorem exists_mem_centralizer_G₂ (hnot : ¬ IsLThreeTwoOrASix G) (h14 : Stmt15414 G T) :
    ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧ z ∈ Subgroup.centralizer (s.G₂ : Set G) := by
  obtain ⟨z, hz, hz1, hzY⟩ := exists_mem_centralizer_of_isYFamily hnot h14 s.famY
  exact ⟨z, hz, hz1, mem_centralizer_sup s hz
    (Subgroup.centralizer_le (factor_L₂ s).le hzY)⟩

theorem exists_mem_L₁ (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (h19 : Stmt15419 G T) :
    ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧ ∃ v ∈ s.L₁, z * v⁻¹ ∈ pCoreOf 2 s.I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨z, hzZ, hzCV⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (h19 s).2.2.2.2.2
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hf := factor_L₁ s
  have hV₁O : s.V₁ ≤ pCoreOf 2 s.L₁ :=
    hf.commutator_le_pCoreOf hyp h12 s.inM₁ s.famX s.le_X
  have hV₁L : s.V₁ ≤ s.L₁ := hV₁O.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 s.L₁)
  have hLI : s.L₁ ≤ s.I := le_sup_left.trans le_sup_left
  have hV₁T : s.V₁ ≤ T := (hV₁O.trans (sixTwoFactor_pCoreOf_le_baum h12 s.inM₁ s.famX s.le_X
    hf)).trans ((baum_le_T₀ s).trans (T₀_le s))
  have hV₁V : s.V₁ ≤ VZ T s.M₁ := hf.commutator_le_vZ s.le_X
  have hVe := (vZ_le_pCoreOf hyp s.inM₁).2
  have hCN : centerOf s.I ≤ Subgroup.normalizer (s.V₁ : Set G) := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le (hV₁L.trans hLI) hc.2)
  have hz' : (z : G) ∈ ((centerOf s.I ⊔ s.V₁ : Subgroup G) : Set G) := hzCV
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCN] at hz'
  obtain ⟨c, hc, v, hv, rfl⟩ := Set.mem_mul.mp hz'
  have hzC : c * v ∈ Subgroup.centralizer (T : Set G) :=
    (mem_quasithinOmegaOneCenter_iff.mp hzZ).2.1
  have hcomm : Commute v (c * v) := (Subgroup.mem_centralizer_iff.mp hzC) v (hV₁T hv)
  have hc2 : c ^ 2 = 1 := by
    have hw2 : (c * v) ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hzZ).2.2
    have hv2 : v ^ 2 = 1 := hVe.2 v (hV₁V hv)
    calc c ^ 2 = ((c * v) * v⁻¹) ^ 2 := by rw [mul_inv_cancel_right]
      _ = (c * v) ^ 2 * (v⁻¹) ^ 2 := hcomm.symm.inv_right.mul_pow 2
      _ = 1 := by rw [hw2, inv_pow, hv2, inv_one, one_mul]
  have hcN : s.I ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hc.2)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcO : c ∈ pCoreOf 2 s.I :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr hc.1) hcN
      (isPGroup_zpowers_of_sq hc2) (Subgroup.mem_zpowers c)
  exact ⟨c * v, hzZ, hz1, v, hV₁L hv, by rw [mul_inv_cancel_right]; exact hcO⟩

end L15422

end CFSG.Quasithin.EmptyFaithfulMultiple
