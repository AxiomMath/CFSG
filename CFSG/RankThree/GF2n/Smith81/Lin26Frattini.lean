module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.GF2n.Smith81

variable {G : Type} [Group G] [Finite G]


private theorem frattini_aux {M A P : Subgroup G} {p : ℕ} [hp : Fact p.Prime]
    (hAn : M ≤ Subgroup.normalizer (A : Set G)) (hPA : P ≤ A)
    (hP : IsPGroup p P) (hidx : ¬ p ∣ (P.subgroupOf A).index) :
    ∀ m ∈ M, ∃ a ∈ A, a⁻¹ * m ∈ Subgroup.normalizer (P : Set G) := by
  intro m hm
  have hPa : IsPGroup p (P.subgroupOf A) := hP.comap_subtype
  let S1 : Sylow p ↥A := hPa.toSylow hidx
  have hS1 : (S1 : Subgroup ↥A) = P.subgroupOf A := rfl
  have hmA : ∀ z, z ∈ A ↔ m * z * m⁻¹ ∈ A := fun z => by
    have := Subgroup.mem_set_normalizer_iff.mp (hAn hm) z
    simpa using this
  let P2 : Subgroup G := P.map (MulAut.conj m).toMonoidHom
  have hP2A : P2 ≤ A := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hmA y).mp (hPA hy)
  have hP2mem : ∀ z, z ∈ P2 ↔ m⁻¹ * z * m ∈ P := by
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : m⁻¹ * (m * y * m⁻¹) * m = y := by group
      show m⁻¹ * (m * y * m⁻¹) * m ∈ P
      rw [this]; exact hy
    · intro h
      exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hc1 : Nat.card (P.subgroupOf A) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv
  have hc2 : Nat.card (P2.subgroupOf A) = Nat.card P := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP2A).toEquiv]
    exact Subgroup.card_map_of_injective (MulAut.conj m).injective
  have hc3 : Nat.card (P2.subgroupOf A) = p ^ (Nat.card A).factorization p := by
    rw [hc2, ← hc1]
    exact S1.card_eq_multiplicity
  let S2 : Sylow p ↥A := Sylow.ofCard (P2.subgroupOf A) hc3
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (↥A) S1 S2
  have ha' : ((a • S1 : Sylow p ↥A) : Subgroup ↥A) = P2.subgroupOf A := by
    rw [ha]; rfl
  refine ⟨a, a.2, ?_⟩
  have key : ∀ z : ↥A, (a⁻¹ * z * a : ↥A) ∈ P.subgroupOf A ↔ z ∈ P2.subgroupOf A := by
    intro z
    rw [← ha', Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_apply, hS1]
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  have hconj : (↑a)⁻¹ * m * y * ((↑a)⁻¹ * m)⁻¹ = (a : G)⁻¹ * (m * y * m⁻¹) * a := by group
  have hy : m⁻¹ * (m * y * m⁻¹) * m = y := by group
  show y ∈ P ↔ _
  rw [hconj]
  by_cases hyA : y ∈ A
  · have hzA : m * y * m⁻¹ ∈ A := (hmA y).mp hyA
    have h := key ⟨m * y * m⁻¹, hzA⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hP2mem, hy] at h
    exact h.symm
  · have hzA : m * y * m⁻¹ ∉ A := fun h => hyA ((hmA y).mpr h)
    have h1 : y ∉ P := fun h => hyA (hPA h)
    have h2 : (a : G)⁻¹ * (m * y * m⁻¹) * a ∉ P := by
      intro h
      apply hzA
      have := A.mul_mem (A.mul_mem a.2 (hPA h)) (A.inv_mem a.2)
      simpa [mul_assoc] using this
    exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

theorem exists_compl_mem_of_frattini {M Q A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hQ2 : IsPGroup 2 Q) (hQA : Q ≤ A) (hAM : A ≤ M)
    (hQn : M ≤ Subgroup.normalizer (Q : Set G)) (hAn : M ≤ Subgroup.normalizer (A : Set G))
    (hpow : ∀ a ∈ A, ∃ k : ℕ, a ^ p ^ k ∈ Q)
    {c : G} (hcA : c ∈ A) (hfpf : ∀ u ∈ Q, ∀ y ∈ Q, y * (c * u) = c * u * y → y = 1)
    {x : G} (hxM : x ∈ M) (hC7 : ∀ a ∈ A, ∃ q ∈ Q, a * x * a⁻¹ = q * x * q⁻¹) :
    ∃ K : Subgroup G, K ≤ M ∧ K ⊓ Q = ⊥ ∧ K ⊔ Q = M ∧ x ∈ K := by
  classical
  have hQA' : A ≤ Subgroup.normalizer (Q : Set G) := hAM.trans hQn
  haveI hN : (Q.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQA).mpr hQA'
  set C : Subgroup G := A ⊓ Subgroup.centralizer {x} with hC
  have hCA : C ≤ A := inf_le_left
  have hCx : ∀ c ∈ C, x * c = c * x := fun c hc =>
    (Subgroup.mem_centralizer_iff.mp hc.2) x (Set.mem_singleton x)
  have step1 : ∀ a ∈ A, ∃ q ∈ Q, ∃ c ∈ C, a = q * c := by
    intro a ha
    obtain ⟨q, hq, h⟩ := hC7 a ha
    have h1 : a * x = q * x * q⁻¹ * a := by
      calc a * x = (a * x * a⁻¹) * a := by group
        _ = _ := by rw [h]
    refine ⟨q, hq, q⁻¹ * a, ⟨A.mul_mem (A.inv_mem (hQA hq)) ha, ?_⟩, by group⟩
    show q⁻¹ * a ∈ Subgroup.centralizer {x}
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    calc h' * (q⁻¹ * a) = q⁻¹ * (q * h' * q⁻¹ * a) := by group
      _ = q⁻¹ * (a * h') := by rw [h1]
      _ = q⁻¹ * a * h' := by group
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ2
  have hquot : IsPGroup p (↥A ⧸ Q.subgroupOf A) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨k, hk⟩ := hpow a a.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hquot
  have hQaidx : (Q.subgroupOf A).index = p ^ n := by rw [Subgroup.index_eq_card]; exact hn
  have hcQa : Nat.card (Q.subgroupOf A) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQA).toEquiv
  have hAcard : Nat.card A = 2 ^ m * p ^ n := by
    rw [← Subgroup.card_mul_index (Q.subgroupOf A), hcQa, hQaidx, hm]
  have hcop : Nat.Coprime (p ^ n) (2 ^ m) :=
    Nat.Coprime.pow n m ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp2)
  have hpn_dvd : p ^ n ∣ Nat.card C := by
    have hsup : (C.subgroupOf A) ⊔ (Q.subgroupOf A) = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨a, ha⟩ -
      obtain ⟨q, hq, c, hc, rfl⟩ := step1 a ha
      have e : (⟨q * c, ha⟩ : ↥A) = ⟨q, hQA hq⟩ * ⟨c, hCA hc⟩ := rfl
      rw [e]
      exact Subgroup.mul_mem_sup (show (⟨q, hQA hq⟩ : ↥A) ∈ Q.subgroupOf A from hq)
        (show (⟨c, hCA hc⟩ : ↥A) ∈ C.subgroupOf A from hc) |> fun h => by
          rw [sup_comm]; exact h
    have h1 := Subgroup.relIndex_sup_right (H := C.subgroupOf A) (K := Q.subgroupOf A)
    rw [hsup, Subgroup.relIndex_top_right, hQaidx] at h1
    have h2 := Subgroup.relIndex_dvd_card (H := Q.subgroupOf A) (K := C.subgroupOf A)
    rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv] at h2
    exact h2
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p ↥C))
  let P : Subgroup G := (S : Subgroup ↥C).map C.subtype
  have hPC : P ≤ C := Subgroup.map_subtype_le _
  have hPA : P ≤ A := hPC.trans hCA
  have hPp : IsPGroup p P := S.isPGroup'.map C.subtype
  have hcP : Nat.card P = Nat.card S := Subgroup.card_map_of_injective C.subtype_injective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hnk : n ≤ k := by
    have h1 : p ^ n ∣ p ^ k * (S : Subgroup ↥C).index := by
      rw [← hk, Subgroup.card_mul_index]; exact hpn_dvd
    have hc : Nat.Coprime (p ^ n) (S : Subgroup ↥C).index :=
      (Nat.Coprime.symm (Nat.Prime.coprime_pow_of_not_dvd (Fact.out : p.Prime) S.not_dvd_index))
    exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp (hc.dvd_of_dvd_mul_right h1)
  have hkn : k ≤ n := by
    have h1 : p ^ k ∣ 2 ^ m * p ^ n := by
      rw [← hAcard, ← hk, ← hcP]; exact Subgroup.card_dvd_of_le hPA
    have hc : Nat.Coprime (p ^ k) (2 ^ m) :=
      Nat.Coprime.pow k m ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp2)
    exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp (hc.dvd_of_dvd_mul_left h1)
  have hPcard : Nat.card P = p ^ n := by rw [hcP, hk, le_antisymm hkn hnk]
  have hPcard' : Nat.card (P.subgroupOf A) = p ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv, hPcard]
  have hPidx2 : (P.subgroupOf A).index = 2 ^ m := by
    have := Subgroup.card_mul_index (P.subgroupOf A)
    rw [hPcard', hAcard, mul_comm (2 ^ m)] at this
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos n) this)
  have hPidx : ¬ p ∣ (P.subgroupOf A).index := by
    rw [hPidx2]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow h)
    exact hp2 this
  have hPQ : P ⊓ Q = ⊥ := disjoint_iff.mp (IsPGroup.disjoint_of_ne p 2 hp2 P Q hPp hQ2)
  have hPx : ∀ b ∈ P, x * b = b * x := fun b hb => hCx b (hPC hb)
  have F4 : ∀ a ∈ A, ∃ u ∈ Q, ∃ b ∈ P, a = u * b := by
    have hsup : (Q.subgroupOf A) ⊔ (P.subgroupOf A) = ⊤ := by
      rw [← Subgroup.index_eq_one]
      refine Nat.eq_one_of_dvd_coprimes hcop ?_ ?_
      · rw [← hQaidx]; exact Subgroup.index_dvd_of_le le_sup_left
      · rw [← hPidx2]; exact Subgroup.index_dvd_of_le le_sup_right
    intro a ha
    have : (⟨a, ha⟩ : ↥A) ∈ (Q.subgroupOf A) ⊔ (P.subgroupOf A) := by rw [hsup]; trivial
    obtain ⟨u, hu, b, hb, h⟩ := Subgroup.mem_sup_of_normal_left.mp this
    refine ⟨u, hu, b, hb, ?_⟩
    have := congrArg Subtype.val h
    simpa using this.symm
  have hAn : M ≤ Subgroup.normalizer (A : Set G) := hAn
  refine ⟨M ⊓ Subgroup.normalizer (P : Set G), inf_le_left, ?_, ?_, ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    rintro y ⟨⟨hyM, hyN⟩, hyQ⟩
    obtain ⟨u', hu', b', hb', hcc⟩ := F4 c⁻¹ (A.inv_mem hcA)
    have hcomm : ∀ b ∈ P, y * b = b * y := by
      intro b hb
      have h1 : y * b * y⁻¹ * b⁻¹ ∈ P :=
        P.mul_mem ((Subgroup.mem_set_normalizer_iff.mp hyN b).mp hb) (P.inv_mem hb)
      have h2 : y * b * y⁻¹ * b⁻¹ ∈ Q := by
        have hbM : b ∈ M := hAM (hPA hb)
        have h3 : b * y⁻¹ * b⁻¹ ∈ Q :=
          (Subgroup.mem_set_normalizer_iff.mp (hQn hbM) y⁻¹).mp (Q.inv_mem hyQ)
        have := Q.mul_mem hyQ h3
        simpa [mul_assoc] using this
      have h3 : y * b * y⁻¹ * b⁻¹ = 1 := by
        have : y * b * y⁻¹ * b⁻¹ ∈ P ⊓ Q := ⟨h1, h2⟩
        rw [hPQ] at this
        exact this
      calc y * b = (y * b * y⁻¹ * b⁻¹) * (b * y) := by group
        _ = b * y := by rw [h3, one_mul]
    apply hfpf u' hu' y hyQ
    have : c * u' = b'⁻¹ := by
      calc c * u' = c * (u' * b') * b'⁻¹ := by group
        _ = c * c⁻¹ * b'⁻¹ := by rw [← hcc]
        _ = b'⁻¹ := by group
    rw [this]
    exact hcomm _ (P.inv_mem hb')
  · apply le_antisymm
    · exact sup_le inf_le_left (hQA.trans hAM)
    · intro m hm
      obtain ⟨a, haA, han⟩ := frattini_aux hAn hPA hPp hPidx m hm
      obtain ⟨u, hu, b, hb, hab⟩ := F4 a haA
      have hbK : b ∈ M ⊓ Subgroup.normalizer (P : Set G) :=
        ⟨hAM (hPA hb), Subgroup.le_normalizer hb⟩
      have hkK : a⁻¹ * m ∈ M ⊓ Subgroup.normalizer (P : Set G) :=
        ⟨M.mul_mem (M.inv_mem (hAM haA)) hm, han⟩
      have e : u * (b * (a⁻¹ * m)) = m := by rw [← mul_assoc, ← hab]; group
      rw [← e, sup_comm]
      exact Subgroup.mul_mem_sup hu (Subgroup.mul_mem _ hbK hkK)
  · refine ⟨hxM, ?_⟩
    show x ∈ Subgroup.normalizer (P : Set G)
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      have e : x * h * x⁻¹ = h := by rw [hPx h hh]; group
      rw [e]; exact hh
    · intro hh
      have e1 := hPx _ hh
      have : x * h * x⁻¹ = h := by
        have : x * (x * h * x⁻¹) = x * h := by rw [e1]; group
        exact mul_left_cancel this
      rw [this] at hh; exact hh

end CFSG.RankThree.GF2n.Smith81
