module

public import CFSG.Walter.W67.Section6.Util
public import CFSG.Walter.W67.Section5.Lemma57
public import CFSG.Walter.W67.Section5.Prop52

public section

namespace CFSG.Walter.W67

namespace Sec6

variable {L : Type} [Group L] [Finite L]

structure SylowData (hL : JRGroup L) (r : ℕ) (P C W : Subgroup L) : Prop where
  P_le_C : P ≤ C
  C_comm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a
  C_hall : Nat.Coprime (Nat.card C) C.index
  C_cent : ∀ c ∈ C, c ≠ 1 → Subgroup.centralizer ({c} : Set L) = C
  CW_inf : C ⊓ W = ⊥
  CW_sup : C ⊔ W = Subgroup.normalizer (P : Set L)
  C_norm : Subgroup.normalizer (P : Set L) ≤ Subgroup.normalizer (C : Set L)
  W_cyc : IsCyclic W
  W_card : Nat.card W = 6 ∨ (hL.q = 5 ∧ r = 11 ∧ Nat.card W = 10)

theorem exists_cyclic_complement {C N : Subgroup L} (hCN : C ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (C : Set L)) (hcop : Nat.Coprime (Nat.card C) (C.relIndex N))
    (hgen : ∃ g ∈ N, Subgroup.zpowers g ⊔ C = N) :
    ∃ W : Subgroup L, W ≤ N ∧ C ⊓ W = ⊥ ∧ C ⊔ W = N ∧ IsCyclic W ∧
      Nat.card W = C.relIndex N := by
  obtain ⟨W, hWN, hi, hs, hcard⟩ := exists_complement_in hCN hnorm hcop
  have hrel : C.relIndex N * Nat.card C = Nat.card N := by
    have := Subgroup.relIndex_mul_card (H := C) (K := N)
    rwa [inf_eq_left.mpr hCN] at this
  have hWcard : Nat.card W = C.relIndex N := by
    have hpos : 0 < Nat.card C := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [hcard, ← hrel, mul_comm])
  refine ⟨W, hWN, hi, hs, ?_, hWcard⟩
  obtain ⟨g, hgN, hgen⟩ := hgen
  have hWnorm : W ≤ Subgroup.normalizer (C : Set L) := hWN.trans hnorm
  have hg : g ∈ C ⊔ W := hs ▸ hgN
  obtain ⟨c, hc, w, hw, rfl⟩ := (mem_sup_iff_of_le_normalizer hWnorm).mp hg
  have hle : N ≤ Subgroup.zpowers w ⊔ C := by
    rw [← hgen]
    refine sup_le ?_ le_sup_right
    rw [Subgroup.zpowers_le]
    exact mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left (Subgroup.mem_zpowers w))
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (C : Set L) :=
    (Subgroup.zpowers_le.mpr hw).trans hWnorm
  have hcard2 := Sec52.card_sup_mul_card_inf hwN
  have hlt : Nat.card W ≤ Nat.card (Subgroup.zpowers w) := by
    have h1 : Nat.card N ≤ Nat.card (Subgroup.zpowers w ⊔ C : Subgroup L) :=
      Subgroup.card_le_of_le hle
    have h2 : Nat.card (Subgroup.zpowers w ⊔ C : Subgroup L) ≤
        Nat.card C * Nat.card (Subgroup.zpowers w) := by
      rw [← hcard2]
      exact Nat.le_mul_of_pos_right _ Nat.card_pos
    have h3 : Nat.card C * Nat.card W ≤ Nat.card C * Nat.card (Subgroup.zpowers w) := by
      rw [hcard]
      exact h1.trans h2
    exact Nat.le_of_mul_le_mul_left h3 Nat.card_pos
  have heq : Subgroup.zpowers w = W :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw) hlt
  rw [← heq]
  exact Subgroup.isCyclic_zpowers w

theorem eq_of_le_comm {r : ℕ} [Fact r.Prime] {C P Q : Subgroup L}
    (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) (hPC : P ≤ C) (hQC : Q ≤ C)
    (hPc : Nat.card P = r ^ (Nat.card C).factorization r)
    (hQc : Nat.card Q = r ^ (Nat.card C).factorization r) : P = Q := by
  obtain ⟨ℓ, hℓC, hℓ⟩ := exists_conj_of_sylowIn hPC hQC hPc hQc
  rw [hℓ]
  symm
  refine cj_eq_self_of_mem_normalizer ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : ℓ * x * ℓ⁻¹ = x := by rw [hC ℓ hℓC x (hPC hx), mul_inv_cancel_right]
    rwa [this]
  · intro hx
    have hxC : x ∈ C := by
      have h1 := hPC hx
      have h2 : x = ℓ⁻¹ * (ℓ * x * ℓ⁻¹) * ℓ := by group
      rw [h2]
      exact C.mul_mem (C.mul_mem (C.inv_mem hℓC) h1) hℓC
    have : ℓ * x * ℓ⁻¹ = x := by rw [hC ℓ hℓC x hxC, mul_inv_cancel_right]
    rwa [this] at hx

omit [Finite L] in
theorem centralizer_eq_of_mem_ne_one {C P : Subgroup L}
    (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) (hPC : P ≤ C)
    (hcent : ∀ c ∈ C, c ≠ 1 → Subgroup.centralizer ({c} : Set L) = C) (hP : P ≠ ⊥) :
    Subgroup.centralizer (P : Set L) = C := by
  obtain ⟨c, hcP, hc1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hP
  apply le_antisymm
  · rw [← hcent c (hPC hcP) hc1]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcP)
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hC y (hPC hy) x hx

theorem relIndex_cj_cj (g : L) (H K : Subgroup L) : (cj g H).relIndex (cj g K) = H.relIndex K := by
  have h1 := Subgroup.relIndex_mul_card (H := cj g H) (K := cj g K)
  have h2 := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [← cj_inf, card_cj, card_cj] at h1
  have hpos : 0 < Nat.card ↥(H ⊓ K) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem index_cj (g : L) (H : Subgroup L) : (cj g H).index = H.index := by
  have h1 := Subgroup.card_mul_index (cj g H)
  have h2 := Subgroup.card_mul_index H
  rw [card_cj] at h1
  have hpos : 0 < Nat.card H := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

omit [Finite L] in
theorem cj_zpowers (g x : L) : cj g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) := by
  rw [cj, MonoidHom.map_zpowers]
  rfl

omit [Finite L] in
theorem dvd_card_of_ne_bot {r : ℕ} [Fact r.Prime] {P : Subgroup L}
    (hPc : Nat.card P = r ^ (Nat.card L).factorization r) (hP : P ≠ ⊥) : r ∣ Nat.card L := by
  have hv : (Nat.card L).factorization r ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hPc
    exact hP (Subgroup.card_eq_one.mp hPc)
  exact Nat.dvd_of_factorization_pos hv

theorem factorization_hall {r : ℕ} [Fact r.Prime] {C : Subgroup L}
    (hC : Nat.Coprime (Nat.card C) C.index) (hr : r ∣ Nat.card C) :
    (Nat.card C).factorization r = (Nat.card L).factorization r := by
  have hri : ¬ r ∣ C.index := fun h =>
    (Nat.Prime.not_dvd_one Fact.out) (hC ▸ Nat.dvd_gcd hr h)
  rw [← Subgroup.card_mul_index C, Nat.factorization_mul Nat.card_pos.ne'
    (Subgroup.index_ne_zero_of_finite), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hri, add_zero]

theorem not_isSolvable_of_three_lt (hL : JRGroup L) (hq3 : 3 < hL.q) : ¬ Group.IsSolvable L := by
  intro hsol
  have hFcard : Nat.card (GaloisField hL.p hL.f) = hL.q := GaloisField.card _ _ hL.f_pos.ne'
  apply Sec57.not_isSolvable_psl2 (hFcard ▸ hq3)
  have : Group.IsSolvable hL.K := inferInstance
  exact Group.isSolvable_of_surjective (f := hL.iso.toMonoidHom) hL.iso.surjective

theorem exists_sylowData_of_R (hR : RFacts) (hL : JRGroup L) (hq5 : hL.q ≠ 5) (hq3 : 3 < hL.q)
    {r : ℕ} [Fact r.Prime] (hr : ¬ r ∣ hL.q * (hL.q ^ 2 - 1)) {P : Subgroup L}
    (hPc : Nat.card P = r ^ (Nat.card L).factorization r) (hP : P ≠ ⊥) :
    ∃ C W : Subgroup L, SylowData hL r P C W := by
  obtain ⟨⟨⟨n, hn, hqn⟩, hcard, -, -⟩, -, -, -, -, hR6, -⟩ := hR L hL hq5
  have hLcard := hcard (not_isSolvable_of_three_lt hL hq3)
  set q := hL.q with hqdef
  set m := 3 ^ ((n + 1) / 2) with hmdef
  have hm : m ^ 2 = 3 * q := by
    rw [hmdef, ← pow_mul, hqn, ← pow_succ']
    congr 1
    obtain ⟨k, rfl⟩ := hn
    omega
  have hrp : r.Prime := Fact.out
  have hrL : r ∣ Nat.card L := dvd_card_of_ne_bot hPc hP
  have hrq : ¬ r ∣ q := fun h => hr (Dvd.dvd.mul_right h _)
  have hq1 : 1 ≤ q := by omega
  have hrq1 : ¬ r ∣ q - 1 := fun h => hr (Dvd.dvd.mul_left (h.trans (by
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [Nat.one_le_pow 2 q hq1, hq1]
      ring
    rw [this]
    exact dvd_mul_right _ _)) _)
  have hrq2 : ¬ r ∣ q + 1 := fun h => hr (Dvd.dvd.mul_left (h.trans (by
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [Nat.one_le_pow 2 q hq1, hq1]
      ring
    rw [this]
    exact dvd_mul_left _ _)) _)
  have hqq : q ≤ q ^ 2 := by nlinarith
  have hcyc : r ∣ q ^ 2 - q + 1 := by
    rw [hLcard] at hrL
    have h3 : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
      zify [hqq]
      ring
    rcases (hrp.dvd_mul).mp hrL with h | h
    · rcases (hrp.dvd_mul).mp h with h | h
      · rw [h3] at h
        rcases (hrp.dvd_mul).mp h with h | h
        · exact absurd h hrq2
        · exact h
      · exact absurd (hrp.dvd_of_dvd_pow h) hrq
    · exact absurd h hrq1
  have hmq : m ≤ q + 1 := by
    have : m ^ 2 ≤ (q + 1) ^ 2 := by rw [hm]; nlinarith
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
  have hfac : (q + 1 + m) * (q + 1 - m) = q ^ 2 - q + 1 := by
    zify [hqq, hmq]
    have : (m : ℤ) ^ 2 = 3 * q := by exact_mod_cast hm
    linear_combination -this
  obtain ⟨b, hb⟩ : ∃ b : Bool, r ∣ (if b then q + 1 + m else q + 1 - m) := by
    rw [← hfac] at hcyc
    rcases (hrp.dvd_mul).mp hcyc with h | h
    · exact ⟨true, by simpa using h⟩
    · exact ⟨false, by simpa using h⟩
  obtain ⟨C₀, hC₀comm, hC₀card, hC₀hall, hC₀gen, hC₀idx, hC₀cent⟩ := hR6 hq3 m hm b
  rw [← hC₀card] at hb
  have hfC₀ := factorization_hall hC₀hall hb
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow r C₀))
  set Q := (Q₀ : Subgroup C₀).map C₀.subtype with hQdef
  have hQC₀ : Q ≤ C₀ := Subgroup.map_subtype_le _
  have hQc : Nat.card Q = r ^ (Nat.card L).factorization r := by
    rw [hQdef, Subgroup.card_map_of_injective C₀.subtype_injective, Sylow.card_eq_multiplicity,
      hfC₀]
  obtain ⟨g, -, hgP⟩ := exists_conj_of_sylowIn (G := L) (L := ⊤) (P := Q) (Q := P) le_top le_top
    (by rw [Subgroup.card_top]; exact hQc) (by rw [Subgroup.card_top]; exact hPc)
  set C := cj g C₀ with hCdef
  have hC₀comm' : ∀ a ∈ C₀, ∀ b ∈ C₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hC₀comm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hC₀1 : C₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hb
    exact hrp.one_lt.ne' (Nat.dvd_one.mp hb)
  have hCC₀ : Subgroup.centralizer (C₀ : Set L) = C₀ :=
    centralizer_eq_of_mem_ne_one hC₀comm' le_rfl hC₀cent hC₀1
  have hPC : P ≤ C := by rw [hgP]; exact cj_mono hQC₀
  have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := comm_cj hC₀comm'
  have hCcent : ∀ c ∈ C, c ≠ 1 → Subgroup.centralizer ({c} : Set L) = C := by
    rintro _ ⟨c₀, hc₀, rfl⟩ hc1
    have hc₀1 : c₀ ≠ 1 := fun h => hc1 (by rw [h]; simp)
    rw [hCdef, ← hC₀cent c₀ hc₀ hc₀1, cj_centralizer_singleton]
    rfl
  have hCc : Nat.card C = Nat.card C₀ := card_cj g C₀
  have hCidx : C.index = C₀.index := index_cj g C₀
  have hChall : Nat.Coprime (Nat.card C) C.index := by rw [hCc, hCidx]; exact hC₀hall
  have hCP : Subgroup.centralizer (P : Set L) = C := centralizer_eq_of_mem_ne_one hCcomm hPC
    hCcent hP
  have hNPC : Subgroup.normalizer (P : Set L) = Subgroup.normalizer (C : Set L) := by
    apply le_antisymm
    · have := Huppert.normalizer_le_normalizer_centralizer P
      rwa [hCP] at this
    · intro x hx
      have hPc' : Nat.card P = r ^ (Nat.card C).factorization r := by
        rw [hPc, hCc, hfC₀]
      have hxP : cj x P ≤ C := by
        rw [← cj_eq_self_of_mem_normalizer hx]
        exact cj_mono hPC
      have heq := eq_of_le_comm hCcomm hPC hxP hPc' (by rw [card_cj, hPc'])
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have : x * y * x⁻¹ ∈ cj x P := conj_mem_cj hy
        rwa [← heq] at this
      · intro hy
        rw [heq, mem_cj] at hy
        simpa [mul_assoc] using hy
  have hidx6 : C.relIndex (Subgroup.normalizer (C : Set L)) = 6 := by
    rw [hCdef, ← cj_normalizer, relIndex_cj_cj]
    rw [hCC₀] at hC₀idx
    exact hC₀idx
  have hcop6 : Nat.Coprime (Nat.card C) (C.relIndex (Subgroup.normalizer (C : Set L))) := by
    have hdvd : C.relIndex (Subgroup.normalizer (C : Set L)) ∣ C.index :=
      Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
    exact Nat.Coprime.coprime_dvd_right hdvd hChall
  have hgen : ∃ x ∈ Subgroup.normalizer (C : Set L),
      Subgroup.zpowers x ⊔ C = Subgroup.normalizer (C : Set L) := by
    obtain ⟨g₀, hg₀, hgen₀⟩ := hC₀gen
    rw [hCC₀] at hgen₀
    refine ⟨g * g₀ * g⁻¹, ?_, ?_⟩
    · rw [hCdef, ← cj_normalizer]
      exact conj_mem_cj hg₀
    · rw [hCdef, ← cj_normalizer, ← hgen₀, cj_sup, cj_zpowers]
  obtain ⟨W, -, hi, hs, hWcyc, hWcard⟩ := exists_cyclic_complement Subgroup.le_normalizer le_rfl
    hcop6 hgen
  refine ⟨C, W, ⟨hPC, hCcomm, hChall, hCcent, hi, ?_, hNPC.le, hWcyc,
    Or.inl (hWcard.trans hidx6)⟩⟩
  rw [hs, hNPC]

theorem exists_sylowData_of_J (hJ : JFacts) (hL : JRGroup L) (hq5 : hL.q = 5) {r : ℕ}
    [Fact r.Prime] (hr : ¬ r ∣ 120) {P : Subgroup L}
    (hPc : Nat.card P = r ^ (Nat.card L).factorization r) (hP : P ≠ ⊥) :
    ∃ C W : Subgroup L, SylowData hL r P C W := by
  obtain ⟨⟨-, hLcard, -⟩, ⟨-, -, hJ23⟩, ⟨hJE1, hJE2, -⟩, -, -⟩ := hJ L hL hq5
  have hrp : r.Prime := Fact.out
  have hrL : r ∣ Nat.card L := dvd_card_of_ne_bot hPc hP
  have hr3 : r = 7 ∨ r = 11 ∨ r = 19 := by
    rw [hLcard, show 2 ^ 3 * 3 * 5 * 7 * 11 * 19 = 120 * 7 * 11 * 19 by norm_num] at hrL
    rcases (hrp.dvd_mul).mp hrL with h | h
    · rcases (hrp.dvd_mul).mp h with h | h
      · rcases (hrp.dvd_mul).mp h with h | h
        · exact absurd h hr
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hrp (by norm_num)).mp h)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hrp (by norm_num)).mp h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hrp (by norm_num)).mp h))
  have hr2 : r ≠ 2 := by rcases hr3 with h | h | h <;> rw [h] <;> norm_num
  set S : Sylow r L := Sylow.ofCard P hPc with hSdef
  have hSP : (S : Subgroup L) = P := rfl
  have hPr : Nat.card P = r := by
    rcases hJE1 r hr2 S with h | h
    · rw [hSP] at h
      exact absurd (Subgroup.card_eq_one.mp h) hP
    · rwa [hSP] at h
  have hCP : Subgroup.centralizer (P : Set L) = P := by
    have := hJE2 r hr3 S
    rwa [hSP] at this
  have hPcyc : IsCyclic P := isCyclic_of_prime_card hPr
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup P := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : P) ⟨b, hb⟩)
  have hPhall : Nat.Coprime (Nat.card P) P.index := by
    rw [hPr]
    refine (Nat.Prime.coprime_iff_not_dvd hrp).mpr fun hdvd => ?_
    have h1 := Subgroup.card_mul_index P
    rw [hPr, hLcard] at h1
    have : r ^ 2 ∣ 2 ^ 3 * 3 * 5 * 7 * 11 * 19 := by
      rw [← h1, pow_two]
      exact Nat.mul_dvd_mul_left r hdvd
    rcases hr3 with h | h | h <;> subst h <;> norm_num at this
  have hPcent : ∀ c ∈ P, c ≠ 1 → Subgroup.centralizer ({c} : Set L) = P := by
    intro c hc hc1
    have hz : Subgroup.zpowers c = P := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc) ?_
      rw [hPr, Nat.card_zpowers]
      have hdvd : orderOf c ∣ r := hPr ▸ Subgroup.orderOf_dvd_natCard P hc
      rcases (Nat.dvd_prime hrp).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hc1
      · exact h.ge
    rw [← Sec52.centralizer_zpowers_eq, hz, hCP]
  obtain ⟨hgen, hidx⟩ := hJ23 r S hr3
  simp only [hSP, hCP] at hgen hidx
  have hrel : P.relIndex (Subgroup.normalizer (P : Set L)) = if r = 11 then 10 else 6 := hidx
  have hcop : Nat.Coprime (Nat.card P) (P.relIndex (Subgroup.normalizer (P : Set L))) := by
    rw [hrel, hPr]
    rcases hr3 with h | h | h <;> subst h <;> norm_num
  obtain ⟨W, -, hi, hs, hWcyc, hWcard⟩ := exists_cyclic_complement Subgroup.le_normalizer le_rfl
    hcop hgen
  refine ⟨P, W, ⟨le_rfl, hPcomm, hPhall, hPcent, hi, hs, le_rfl, hWcyc, ?_⟩⟩
  rw [hWcard, hrel]
  by_cases h11 : r = 11
  · exact Or.inr ⟨hq5, h11, by simp [h11]⟩
  · exact Or.inl (by simp [h11])

end Sec6

end CFSG.Walter.W67
