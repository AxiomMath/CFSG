module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch10SecB3A5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_sup_of_odd {N O : Subgroup G}
    (hO : O ≤ Subgroup.normalizer (N : Set G)) (hO2 : IsPGroup 2 O) {x : G} (hx : x ∈ N ⊔ O)
    (hodd : Odd (orderOf x)) : x ∈ N := by
  have hx' : x ∈ ((N ⊔ O : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N O hO] at hx'
  obtain ⟨n, hn, o, ho, rfl⟩ := Set.mem_mul.mp hx'
  have key : ∀ k : ℕ, ∃ n' ∈ N, (n * o) ^ k = n' * o ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨n', hn', e⟩ := ih
      have hc : o ^ k * n * (o ^ k)⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hO (O.pow_mem ho k)) n).mp hn
      refine ⟨n' * (o ^ k * n * (o ^ k)⁻¹), N.mul_mem hn' hc, ?_⟩
      rw [pow_succ, e, pow_succ]
      group
  obtain ⟨m, hm⟩ := hO2 ⟨o, ho⟩
  have hom : o ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨n', hn', e⟩ := key (2 ^ m)
  rw [hom, mul_one] at e
  have hxN : (n * o) ^ 2 ^ m ∈ N := e ▸ hn'
  rcases Nat.lt_or_ge 1 (orderOf (n * o)) with h1 | h1
  · have hcop : Nat.Coprime (2 ^ m) (orderOf (n * o)) :=
      Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hodd)
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have e2 : n * o = ((n * o) ^ 2 ^ m) ^ u := by
      rw [← pow_mul, ← pow_mod_orderOf, hu, pow_one]
    rw [e2]
    exact N.pow_mem hxN u
  · have h1' : orderOf (n * o) = 1 := by
      have := orderOf_pos (n * o)
      omega
    rw [orderOf_eq_one_iff.mp h1']
    exact N.one_mem

theorem le_of_normal_of_not_le {L N : Subgroup G} (hLp : ⁅L, L⁆ = L)
    {α : ↥L →* alternatingGroup (Fin 5)} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hxN : x ∈ N) (hxL : x ∈ L) (hαx : α ⟨x, hxL⟩ ≠ 1) : L ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' := (N ⊓ L).subgroupOf L with hN'
  have hN'n : N'.Normal := ⟨fun n hn g => by
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hLN g.2) n).mp hn.1, ?_⟩
    exact L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩
  have hmapn : (N'.map α).Normal := Subgroup.Normal.map hN'n α hαs
  have hmap : N'.map α = ⊤ := by
    refine (hmapn.eq_bot_or_eq_top).resolve_left fun hb => hαx ?_
    have : α ⟨x, hxL⟩ ∈ N'.map α :=
      ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr ⟨hxN, hxL⟩, rfl⟩
    rw [hb] at this
    exact this
  have hO2 : IsPGroup 2 (pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hON : pCoreOf 2 L ≤ Subgroup.normalizer (N : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLN
  have hLsup : L ≤ N ⊔ pCoreOf 2 L := by
    intro l hl
    obtain ⟨n, hn, hnl⟩ : α ⟨l, hl⟩ ∈ N'.map α := hmap ▸ Subgroup.mem_top _
    have hk : n⁻¹ * ⟨l, hl⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnl, inv_mul_cancel]
    rw [hαk] at hk
    have hk' : ((n⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ pCoreOf 2 L := Subgroup.mem_map_of_mem L.subtype hk
    have hnN : (n : G) ∈ N := (Subgroup.mem_subgroupOf.mp hn).1
    have e : l = (n : G) * ((n⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right hk')
  rw [eq_oTwoUpper_of_perfect hLp]
  refine (Subgroup.closure_le _).mpr fun y hy => ?_
  exact mem_of_mem_sup_of_odd hON hO2 (hLsup hy.1) hy.2

theorem nine_dvd_card_sup {a b : G} (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : a * b = b * a) (hba : b ∉ Subgroup.zpowers a) :
    9 ∣ Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ∀ {c : G}, orderOf c = 3 → IsPGroup 3 (Subgroup.zpowers c) := fun hc =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have hN : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (Commute.symm hab) k).eq)
  have hP : IsPGroup 3 ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) :=
    IsPGroup.to_sup_of_normal_right' (h3 ha) (h3 hb) hN
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hcard : 3 < 3 ^ k := by
    by_contra hle
    push Not at hle
    have heq : Subgroup.zpowers a = Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk, Nat.card_zpowers, ha]; exact hle)
    exact hba (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  rw [hk]
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp at hcard
  calc 9 = 3 ^ 2 := by norm_num
    _ ∣ 3 ^ k := pow_dvd_pow 3 hk2

theorem not_nine_dvd_card {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 5)}
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L) : ¬ 9 ∣ Nat.card L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hq : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
    rw [← SecB.card_alt5, ← hαk]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv
  have hc := (CFSG.pCore 2 ↥L).card_mul_index
  rw [Subgroup.index, hq] at hc
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  rw [hm] at hc
  have h9 : 9 ∣ 2 ^ m * 60 := hc ▸ h
  have hcop : Nat.Coprime 9 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
  have := (Nat.Coprime.dvd_of_dvd_mul_left hcop h9)
  norm_num at this

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
