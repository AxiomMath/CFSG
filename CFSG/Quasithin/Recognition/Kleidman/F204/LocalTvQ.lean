module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalFive

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem exists_pow_centralizes_of_transvections {V : Subgroup G} (hV2 : ∀ v ∈ V, v * v = 1)
    {a b : G} (ha : a ∈ Subgroup.normalizer (V : Set G)) (hb : b ∈ Subgroup.normalizer (V : Set G))
    (hia : (V ⊓ Subgroup.centralizer {a}).relIndex V ≤ 2)
    (hib : (V ⊓ Subgroup.centralizer {b}).relIndex V ≤ 2) :
    ∃ n : ℕ, 0 < n ∧ ¬ 5 ∣ n ∧ (a * b) ^ n ∈ Subgroup.centralizer (V : Set G) := by
  let ρ := V.normalizerMonoidHom
  let na : Subgroup.normalizer (V : Set G) := ⟨a, ha⟩
  let nb : Subgroup.normalizer (V : Set G) := ⟨b, hb⟩
  have hV2' : ∀ v : V, v * v = 1 := fun v => Subtype.ext (hV2 v v.2)
  have hσ : (FA5.fixSub (ρ na)).index ≤ 2 := by
    rw [FA5.fixSub_normalizerMonoidHom V na]; exact hia
  have hτ : (FA5.fixSub (ρ nb)).index ≤ 2 := by
    rw [FA5.fixSub_normalizerMonoidHom V nb]; exact hib
  set ξ : MulAut V := ρ na * ρ nb with hξ
  have hK : (FA5.fixSub (ρ na) ⊓ FA5.fixSub (ρ nb)).index ≤ 4 := by
    calc (FA5.fixSub (ρ na) ⊓ FA5.fixSub (ρ nb)).index
        ≤ (FA5.fixSub (ρ na)).index * (FA5.fixSub (ρ nb)).index := Subgroup.index_inf_le
      _ ≤ 2 * 2 := Nat.mul_le_mul hσ hτ
      _ = 4 := by norm_num
  have hξK : ∀ k ∈ FA5.fixSub (ρ na) ⊓ FA5.fixSub (ρ nb), ξ k = k := by
    intro k hk
    rw [hξ, MulAut.mul_apply, FA5.mem_fixSub.mp hk.2, FA5.mem_fixSub.mp hk.1]
  have hn5 : ¬ 5 ∣ orderOf ξ := by
    intro h5
    obtain ⟨m, hm⟩ := h5
    have hpos : 0 < orderOf ξ := orderOf_pos ξ
    set η : MulAut V := ξ ^ m with hη
    have hη5 : η ^ 5 = 1 := by
      rw [hη, ← pow_mul, mul_comm, ← hm]; exact pow_orderOf_eq_one ξ
    have hηK : ∀ k ∈ FA5.fixSub (ρ na) ⊓ FA5.fixSub (ρ nb), η k = k := by
      intro k hk
      have hpow : ∀ n : ℕ, (ξ ^ n) k = k := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hξK k hk, ih]
      exact hpow m
    have h1 : η = 1 := FA5.eq_one_of_fix_index_le_four hV2' hK hηK hη5
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0] at hm; omega
      · exact h0
    have := orderOf_dvd_of_pow_eq_one (show ξ ^ m = 1 from h1)
    have hle := Nat.le_of_dvd hmpos this
    omega
  refine ⟨orderOf ξ, orderOf_pos ξ, hn5, ?_⟩
  have hrho : ρ (na * nb) = ξ := by rw [map_mul]
  have : ρ ((na * nb) ^ orderOf ξ) = 1 := by
    rw [map_pow, hrho]; exact pow_orderOf_eq_one ξ
  have h2 := (FA5.normalizerMonoidHom_eq_one_iff V _).mp this
  simpa using h2

omit [Finite G] in
theorem relIndex_conj_normalizer {V : Subgroup G} {n a : G}
    (hn : n ∈ Subgroup.normalizer (V : Set G)) (ha : a ∈ Subgroup.normalizer (V : Set G)) :
    (V ⊓ Subgroup.centralizer {n * a * n⁻¹}).relIndex V = (V ⊓ Subgroup.centralizer {a}).relIndex V := by
  let ρ := V.normalizerMonoidHom
  let nn : Subgroup.normalizer (V : Set G) := ⟨n, hn⟩
  let na : Subgroup.normalizer (V : Set G) := ⟨a, ha⟩
  have h1 := FA5.fixSub_normalizerMonoidHom V (nn * na * nn⁻¹)
  have h2 := FA5.fixSub_normalizerMonoidHom V na
  have h3 := FA5.index_fixSub_conj (ρ nn) (ρ na)
  have h4 : ρ nn * ρ na * (ρ nn)⁻¹ = ρ (nn * na * nn⁻¹) := by simp [map_mul, map_inv]
  rw [h4, h1, h2] at h3
  exact h3

theorem exists_centralizing_five (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hN : stab δ ≤ Subgroup.normalizer (V : Set G)) {a : G} (ha : a ∈ stab δ) (haQ : a ∉ Qv δ)
    (ha2 : a * a ∈ Qv δ) (hidx : (V ⊓ Subgroup.centralizer {a}).relIndex V ≤ 2) :
    ∃ e ∈ stab δ, e ∈ Subgroup.centralizer (V : Set G) ∧ e ∉ Qv δ ∧ e ^ 5 ∈ Qv δ := by
  obtain ⟨g, hg1, hg2⟩ := exists_conj_stab_false (L1 := L1) (L2 := L2) (S := S) hδ
  have hV2 : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← pow_two]; exact hV.2 v hv
  obtain ⟨x0, hx0, hx05, hx01, -⟩ := F.exists_gen
  have hxP : x0 ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx0
  have hx0st : g⁻¹ * x0 * g ∈ stab δ := by
    have : x0 ∈ conjSub g (stab δ) := by rw [hg1]; exact hxP
    exact mem_conjSub.mp this
  set a' := g * a * g⁻¹ with ha'
  have ha'P : a' ∈ P1 L1 L2 S := by rw [← hg1]; exact mem_conjSub_of_mem' ha
  have ha'Q : a' ∉ Q1 L1 L2 S := by
    intro h
    rw [← hg2, ha', mem_conjSub] at h
    apply haQ
    have e : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    rwa [e] at h
  have ha'2 : a' * a' ∈ Q1 L1 L2 S := by
    rw [← hg2]
    have e : a' * a' = g * (a * a) * g⁻¹ := by rw [ha']; group
    rw [e]
    exact mem_conjSub_of_mem' ha2
  obtain ⟨q, hq, hinv⟩ := inv_of_involution_P1 F ha'P ha'2 ha'Q hx0
  set b := (g⁻¹ * x0 * g) * a * (g⁻¹ * x0 * g)⁻¹ with hb
  have hbst : b ∈ stab δ :=
    (stab δ).mul_mem ((stab δ).mul_mem hx0st ha) ((stab δ).inv_mem hx0st)
  have hib : (V ⊓ Subgroup.centralizer {b}).relIndex V ≤ 2 := by
    rw [hb, relIndex_conj_normalizer (hN hx0st) (hN ha)]; exact hidx
  obtain ⟨n, hn0, hn5, hnc⟩ := exists_pow_centralizes_of_transvections hV2 (hN ha) (hN hbst) hidx hib
  have habst : a * b ∈ stab δ := (stab δ).mul_mem ha hbst
  set π := Frame.pi1 L1 L2 S with hπ
  set A : ↥(P1 L1 L2 S) := ⟨a', ha'P⟩ with hA
  set Xe : ↥(P1 L1 L2 S) := ⟨x0, hxP⟩ with hXe
  have hσσ : π A * π A = 1 := by
    rw [← map_mul, Frame.pi1_eq_one_iff]; exact ha'2
  have hσ' : (π A)⁻¹ = π A := inv_eq_of_mul_eq_one_right hσσ
  have hu5 : π Xe ^ 5 = 1 := by
    rw [← map_pow]
    have : Xe ^ 5 = 1 := Subtype.ext (by simpa using hx05)
    rw [this, map_one]
  have hu1 : π Xe ≠ 1 := by
    intro h
    have h2 : x0 ∈ Q1 L1 L2 S := (Frame.pi1_eq_one_iff Xe).mp h
    have h3 : x0 ∈ S := F.Q1_le_S h2
    obtain ⟨k, hk⟩ := F.pair.hyp.hyp.h1.pgroup ⟨x0, h3⟩
    have hk' : x0 ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hg' : Nat.gcd (2 ^ k) 5 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hk', hx05⟩
    rw [hg', pow_one] at this
    exact hx01 this
  have hconj : π (A * Xe * A⁻¹) = (π Xe)⁻¹ := by
    have h1 : A * Xe * A⁻¹ = Xe⁻¹ * ⟨q, (pCoreOf_le 2 _ hq)⟩ := Subtype.ext (by simpa using hinv)
    have hπq : π (⟨q, pCoreOf_le 2 _ hq⟩ : ↥(P1 L1 L2 S)) = 1 := (Frame.pi1_eq_one_iff _).mpr hq
    rw [h1, map_mul, hπq, mul_one, map_inv]
  set G0 : ↥(P1 L1 L2 S) := A * (Xe * A * Xe⁻¹) with hG0
  have hπG0 : π G0 = ((π Xe)⁻¹) ^ 2 := by
    have : π G0 = π A * π Xe * π A * (π Xe)⁻¹ := by
      rw [hG0, map_mul, map_mul, map_mul, map_inv]; group
    rw [this]
    have h2 : π A * π Xe * π A = (π Xe)⁻¹ := by
      have := hconj
      rw [map_mul, map_mul, map_inv, hσ'] at this
      exact this
    rw [h2]; group
  have hG0val : ((G0 : ↥(P1 L1 L2 S)) : G) = a' * (x0 * a' * x0⁻¹) := by simp [hG0, hA, hXe]
  have hh : g * (a * b) * g⁻¹ = a' * (x0 * a' * x0⁻¹) := by rw [hb, ha']; group
  refine ⟨(a * b) ^ n, (stab δ).pow_mem habst n, hnc, ?_, ?_⟩
  · intro hmem
    have h1 : g * (a * b) ^ n * g⁻¹ ∈ Q1 L1 L2 S := by
      rw [← hg2]; exact mem_conjSub_of_mem' hmem
    have h2 : ((G0 ^ n : ↥(P1 L1 L2 S)) : G) ∈ Q1 L1 L2 S := by
      rw [Subgroup.coe_pow, hG0val, ← hh, conj_pow]; exact h1
    have h3 : π (G0 ^ n) = 1 := (Frame.pi1_eq_one_iff _).mpr h2
    rw [map_pow, hπG0, ← pow_mul] at h3
    have hord : orderOf (π Xe) = 5 := by
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact orderOf_eq_prime hu5 hu1
    rw [inv_pow, inv_eq_one] at h3
    have h5 := orderOf_dvd_of_pow_eq_one h3
    rw [hord] at h5
    exact hn5 (by omega)
  · have hq5 : (a * b) ^ 5 ∈ Qv δ := by
      have h1 : π (G0 ^ 5) = 1 := by
        rw [map_pow, hπG0, ← pow_mul, mul_comm, pow_mul, inv_pow, hu5]; simp
      have h2 : ((G0 ^ 5 : ↥(P1 L1 L2 S)) : G) ∈ Q1 L1 L2 S := (Frame.pi1_eq_one_iff _).mp h1
      rw [Subgroup.coe_pow, hG0val, ← hh, conj_pow, ← hg2] at h2
      have := mem_conjSub.mp h2
      simpa [mul_assoc] using this
    rw [← pow_mul, mul_comm, pow_mul]
    exact (Qv δ).pow_mem hq5 n

end CFSG.Quasithin.Kleidman.F204
