module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Perf
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Stellmacher.CD.L3YC

theorem false_of_alt5_quotient {B : Type} [Group B] [Finite B]
    (hq : IsPSL 3 2 1 (B ⧸ CFSG.pCore 2 B)) (ρ : B →* alternatingGroup (Fin 5))
    (hρ : Function.Surjective ρ) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup (B ⧸ CFSG.pCore 2 B) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hq).2
  have hc168 : Nat.card (B ⧸ CFSG.pCore 2 B) = 168 := CFSG.Quasithin.SBc11.card_of_isPSL_three_two hq
  have hA5 : IsSimpleGroup (alternatingGroup (Fin 5)) := CFSG.QuasithinUnique.Vol2Native.A312L.Seven.alt5_simple
  have hc60 : Nat.card (alternatingGroup (Fin 5)) = 60 := J4Fam.card_alt5
  set P : Subgroup B := CFSG.pCore 2 B with hP
  have hPn : P.Normal := inferInstance
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hKn : (P.map ρ).Normal := Subgroup.Normal.map hPn ρ hρ
  have hK2 : IsPGroup 2 (P.map ρ) := hP2.map ρ
  have hK : P.map ρ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map ρ) with h | h
    · exact h
    · exfalso
      rw [h] at hK2
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hK2)
      rw [Subgroup.card_top, hc60] at hn
      have hn5 : n < 6 := by
        by_contra hlt
        push Not at hlt
        have : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hlt
        omega
      interval_cases n <;> omega
  have hPR : P ≤ ρ.ker := by
    intro x hx
    have : ρ x ∈ P.map ρ := Subgroup.mem_map_of_mem ρ hx
    rw [hK, Subgroup.mem_bot] at this
    exact this
  have hRn : (ρ.ker.map (QuotientGroup.mk' P)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective P)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map (QuotientGroup.mk' P)) with h | h
  ·
    have hRP : ρ.ker ≤ P := by
      intro x hx
      have : QuotientGroup.mk' P x ∈ ρ.ker.map (QuotientGroup.mk' P) := Subgroup.mem_map_of_mem _ hx
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).mp this
    have hker : ρ.ker = P := le_antisymm hRP hPR
    have hidx : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
    rw [MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top, hc60, hker] at hidx
    have : P.index = Nat.card (B ⧸ P) := rfl
    omega
  ·
    have hRt : ρ.ker = ⊤ := by
      rw [eq_top_iff]
      intro b _
      have hb : QuotientGroup.mk' P b ∈ ρ.ker.map (QuotientGroup.mk' P) := by rw [h]; trivial
      obtain ⟨r, hr, hrb⟩ := hb
      have hmem : r⁻¹ * b ∈ P := by
        rw [← QuotientGroup.eq]
        exact hrb
      have hb' : b = r * (r⁻¹ * b) := by group
      rw [hb']
      exact ρ.ker.mul_mem hr (hPR hmem)
    have : Subsingleton (alternatingGroup (Fin 5)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := hρ a
      obtain ⟨y, rfl⟩ := hρ b
      have hx : ρ x = 1 := by rw [← MonoidHom.mem_ker, hRt]; trivial
      have hy : ρ y = 1 := by rw [← MonoidHom.mem_ker, hRt]; trivial
      rw [hx, hy]
    have h1 : Nat.card (alternatingGroup (Fin 5)) = 1 := Nat.card_unique
    omega

theorem pow_conj_eq_self {G : Type*} [Group G] {t q : G} (h : t * q * t⁻¹ = q) (n : ℕ) :
    t ^ n * q * (t ^ n)⁻¹ = q := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc t ^ (n + 1) * q * (t ^ (n + 1))⁻¹ = t * (t ^ n * q * (t ^ n)⁻¹) * t⁻¹ := by
          rw [pow_succ']; group
      _ = q := by rw [ih, h]

theorem exists_three_part {G H : Type*} [Group G] [Finite G] [Group H] (ρ : G →* H) {t : G}
    (hρ : ρ t ≠ 1) {e : ℕ} (he : (ρ t) ^ 3 ^ e = 1) :
    ∃ s : G, (∃ e2 : ℕ, s ^ 3 ^ e2 = 1) ∧ ρ s ≠ 1 ∧ ∀ q : G, t * q * t⁻¹ = q → s * q * s⁻¹ = q := by
  obtain ⟨e2, n2, hn2, hn2eq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos t).ne' 3 (by norm_num)
  refine ⟨t ^ n2, ⟨e2, ?_⟩, ?_, fun q hq => pow_conj_eq_self hq n2⟩
  · rw [← pow_mul, mul_comm, ← hn2eq]
    exact pow_orderOf_eq_one t
  · intro h
    rw [map_pow] at h
    have hd1 : orderOf (ρ t) ∣ n2 := orderOf_dvd_of_pow_eq_one h
    have hd2 : orderOf (ρ t) ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one he
    obtain ⟨f, hf, hf'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd2
    have hf0 : f ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hf'
      exact hρ hf'
    exact hn2 (dvd_trans (hf' ▸ dvd_pow_self 3 hf0) hd1)

theorem pow_three_of_three_power {G : Type*} [Group G] [Finite G] (hcard : ¬ 9 ∣ Nat.card G) {g : G}
    {e : ℕ} (he : g ^ 3 ^ e = 1) : g ^ 3 = 1 := by
  have hd : orderOf g ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one he
  obtain ⟨f, hf, hf'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  have hdc : orderOf g ∣ Nat.card G := orderOf_dvd_natCard g
  have hf1 : f ≤ 1 := by
    by_contra hlt
    push Not at hlt
    apply hcard
    have h9 : 9 ∣ 3 ^ f := by
      have : 3 ^ 2 ∣ 3 ^ f := pow_dvd_pow 3 hlt
      simpa using this
    exact h9.trans (hf' ▸ hdc)
  rw [← orderOf_dvd_iff_pow_eq_one, hf']
  calc 3 ^ f ∣ 3 ^ 1 := pow_dvd_pow 3 hf1
    _ = 3 := pow_one 3

end Stellmacher.CD.L3YC

end CFSG.Quasithin
