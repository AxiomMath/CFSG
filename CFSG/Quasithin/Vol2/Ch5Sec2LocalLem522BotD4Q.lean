module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotD4Aut
public import CFSG.Quasithin.EmptyFaithful.S1422Center
public import CFSG.RankThree.Literature.SemiExtraspecialRank

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Special

variable {G : Type} [Group G] [Finite G]

theorem isSpecialPow_central_facts {Q : Subgroup G} {w : ℕ} (hw : 1 ≤ w)
    (hQ : IsSpecialPow 2 2 w ↥Q) :
    ∃ z ∈ Q, z ≠ 1 ∧ z * z = 1 ∧ (∀ q ∈ Q, q * z = z * q) ∧
      (∀ c ∈ Q, (∀ q ∈ Q, q * c = c * q) → c = 1 ∨ c = z) ∧
      (∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z) ∧ ∀ x ∈ Q, x * x = 1 ∨ x * x = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hQ2, hsp⟩, hcard, hZ⟩ := hQ
  have : Fact (IsPGroup 2 ↥Q) := ⟨hQ2⟩
  obtain ⟨w0, hw1, hwc, hwu⟩ := centerOrderTwo_of_card_center_two hZ
  rcases hsp with ⟨hab, -⟩ | ⟨hcomm, hfr, hZ2⟩
  · exfalso
    have htop : Subgroup.center ↥Q = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact hab.is_comm.comm y x
    rw [htop, Subgroup.card_top, hcard] at hZ
    have : 2 ^ 3 ≤ 2 ^ (1 + 2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hw0c : w0 ∈ Subgroup.center ↥Q := Subgroup.mem_center_iff.mpr fun y => (hwc y).symm
  have hcen : ∀ c : ↥Q, c ∈ Subgroup.center ↥Q → c = 1 ∨ c = w0 := fun c hc =>
    hwu c fun y => (Subgroup.mem_center_iff.mp hc y).symm
  refine ⟨w0, w0.2, fun h => hw1 (Subtype.ext h), ?_, fun q hq => ?_, fun c hc hcq => ?_,
    fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h := hZ2 w0 hw0c
    rw [sq] at h
    exact congrArg Subtype.val h
  · exact congrArg Subtype.val (hwc ⟨q, hq⟩).symm
  · rcases hwu ⟨c, hc⟩ (fun y => Subtype.ext (hcq y y.2).symm) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · have hm : ⁅(⟨x, hx⟩ : ↥Q), ⟨y, hy⟩⁆ ∈ Subgroup.center ↥Q := by
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rcases hcen _ hm with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · have hm : (⟨x, hx⟩ : ↥Q) ^ 2 ∈ Subgroup.center ↥Q := by
      rw [← hfr]
      exact CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) _
    rcases hcen _ hm with h | h
    · left
      have := congrArg Subtype.val h
      simpa [sq] using this
    · right
      have := congrArg Subtype.val h
      simpa [sq] using this

theorem card_le_two_mul_card_inf_centralizer {Q : Subgroup G} {z c : G} (hzz : z * z = 1)
    (hzc : ∀ q ∈ Q, q * z = z * q) (hc : ∀ q ∈ Q, ⁅c, q⁆ = 1 ∨ ⁅c, q⁆ = z) :
    Nat.card Q ≤ 2 * Nat.card ↥(Q ⊓ Subgroup.centralizer ({c} : Set G)) := by
  have hmem : ∀ q ∈ Q, ⁅c, q⁆ ∈ Subgroup.zpowers z := fun q hq => by
    rcases hc q hq with h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers z
  let f : ↥Q →* ↥(Subgroup.zpowers z) :=
    { toFun := fun q => ⟨⁅c, (q : G)⁆, hmem q q.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        show ⁅c, (a : G) * b⁆ = ⁅c, (a : G)⁆ * ⁅c, (b : G)⁆
        have hb : (a : G) * ⁅c, (b : G)⁆ = ⁅c, (b : G)⁆ * a := by
          rcases hc b b.2 with h | h <;> rw [h]
          · group
          · exact hzc a a.2
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def] at *
        calc c * (↑a * ↑b) * c⁻¹ * (↑a * ↑b)⁻¹ =
            (c * ↑a * c⁻¹ * (↑a)⁻¹) * (↑a * (c * ↑b * c⁻¹ * (↑b)⁻¹)) * (↑a)⁻¹ := by group
          _ = (c * ↑a * c⁻¹ * (↑a)⁻¹) * ((c * ↑b * c⁻¹ * (↑b)⁻¹) * ↑a) * (↑a)⁻¹ := by rw [hb]
          _ = c * ↑a * c⁻¹ * (↑a)⁻¹ * (c * ↑b * c⁻¹ * (↑b)⁻¹) := by group }
  have hker : f.ker = (Q ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf Q := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : ⁅c, (q : G)⁆ = 1 := congrArg Subtype.val h
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact ⟨q.2, h1.symm⟩
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show ⁅c, (q : G)⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact h.symm
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hrange : Nat.card (↥Q ⧸ f.ker) ≤ 2 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    calc Nat.card ↥f.range ≤ Nat.card ↥(Subgroup.zpowers z) := by
          rw [← Subgroup.card_top (G := ↥(Subgroup.zpowers z))]
          exact Subgroup.card_le_of_le le_top
      _ = orderOf z := Nat.card_zpowers z
      _ ≤ 2 := orderOf_le_of_pow_eq_one two_pos (by rw [sq]; exact hzz)
  have hk : Nat.card ↥f.ker = Nat.card ↥(Q ⊓ Subgroup.centralizer ({c} : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hcard, ← hk]
  exact Nat.mul_le_mul_right _ hrange

theorem card_inf_centralizer_le_eight {Q : Subgroup G} (hQ : IsSpecialPow 2 2 4 ↥Q) {b : G}
    (hb : b ∈ Subgroup.normalizer (Q : Set G)) (h7 : b ^ 7 = 1)
    (hbQ : ¬ Q ≤ Subgroup.centralizer ({b} : Set G)) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({b} : Set G)) ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hQ512 : Nat.card Q = 512 := by rw [hQ.2.1]; norm_num
  have hQ2 : IsPGroup 2 ↥Q := hQ.1.1
  obtain ⟨z, hzQ, hz1, hzz, hzc, hcen, hcomm, hsq⟩ := isSpecialPow_central_facts (by norm_num) hQ
  set C := Q ⊓ Subgroup.centralizer ({b} : Set G) with hCdef
  have hCQ : C ≤ Q := inf_le_left
  have hbz : z ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz' : b * z * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hb z).mp hzQ
    have hc : b * z * b⁻¹ = 1 ∨ b * z * b⁻¹ = z := by
      refine hcen _ hz' fun q hq => ?_
      have hq' : b⁻¹ * q * b⁻¹⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb) q).mp hq
      rw [inv_inv] at hq'
      have h1 := hzc _ hq'
      calc q * (b * z * b⁻¹) = b * ((b⁻¹ * q * b) * z) * b⁻¹ := by group
        _ = b * (z * (b⁻¹ * q * b)) * b⁻¹ := by rw [h1]
        _ = b * z * b⁻¹ * q := by group
    rcases hc with h | h
    · exfalso
      apply hz1
      calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
        _ = 1 := by rw [h]; group
    · calc z * b = b * z * b⁻¹ * b := by rw [h]
        _ = b * z := by group
  have hzC : z ∈ C := ⟨hzQ, hbz⟩
  have hmodQ : Nat.card Q ≡ Nat.card C [MOD 7] := card_modEq_card_inf_centralizer hb h7
  rw [hQ512] at hmodQ
  have hZC : ∀ c ∈ C, (∀ d ∈ C, d * c = c * d) → c = 1 ∨ c = z := by
    intro c hc hcd
    set K := Q ⊓ Subgroup.centralizer ({c} : Set G) with hKdef
    have hbc : b ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hc.2).symm
    have hbK : b ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hb, Subgroup.le_normalizer hbc⟩
    have hmodK := card_modEq_card_inf_centralizer (p := 7) hbK h7
    have hKC : K ⊓ Subgroup.centralizer ({b} : Set G) = C := by
      apply le_antisymm
      · exact fun x hx => ⟨hx.1.1, hx.2⟩
      · intro x hx
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩, hx.2⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcd x hx
    rw [hKC] at hmodK
    have hidx := card_le_two_mul_card_inf_centralizer (Q := Q) hzz hzc
      (fun q hq => hcomm c hc.1 q hq)
    rw [hQ512] at hidx
    have hKdvd : Nat.card K ∣ 2 ^ 9 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : K ≤ Q)
      rwa [hQ512] at this
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hKdvd
    have hK512 : Nat.card K = 512 := by
      rw [hk'] at hidx hmodK ⊢
      have hk8 : 8 ≤ k := by
        by_contra hlt
        have : 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k
      · exact absurd (hmodK.trans hmodQ.symm) (by decide)
      · rfl
    have hKQ : K = Q := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hK512, hQ512])
    refine hcen c hc.1 fun q hq => ?_
    have hqK : q ∈ K := hKQ ▸ hq
    exact Subgroup.mem_centralizer_singleton_iff.mp hqK.2
  by_cases hab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c
  ·
    have hle : C ≤ Subgroup.zpowers z := fun c hc => by
      rcases hZC c hc (fun d hd => hab d hd c hc) with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    calc Nat.card C ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hle
      _ = orderOf z := Nat.card_zpowers z
      _ ≤ 2 := orderOf_le_of_pow_eq_one two_pos (by rw [sq]; exact hzz)
      _ ≤ 8 := by norm_num
  push Not at hab
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := hab
  set zC : ↥C := ⟨z, hzC⟩ with hzCdef
  have hzC1 : zC ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hcenP : ∀ x : ↥C, x ∈ Subgroup.center ↥C ↔ x = 1 ∨ x = zC := by
    intro x
    constructor
    · intro hx
      rcases hZC x x.2 (fun d hd => congrArg Subtype.val
          (Subgroup.mem_center_iff.mp hx ⟨d, hd⟩)) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (hzc y (hCQ y.2))
  have hcommC : ∀ x y : ↥C, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = zC := by
    intro x y
    rcases hcomm x (hCQ x.2) y (hCQ y.2) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hsqC : ∀ x : ↥C, x ^ 2 = 1 ∨ x ^ 2 = zC := by
    intro x
    rcases hsq x (hCQ x.2) with h | h
    · exact Or.inl (Subtype.ext (by simpa [sq] using h))
    · exact Or.inr (Subtype.ext (by simpa [sq] using h))
  have hne : ⁅(⟨a₀, ha₀⟩ : ↥C), ⟨b₀, hb₀⟩⁆ = zC := by
    rcases hcommC ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩ with h | h
    · exfalso
      rw [commutatorElement_eq_one_iff_mul_comm] at h
      exact hab₀ (congrArg Subtype.val h)
    · exact h
  have hP2 : IsPGroup 2 ↥C := hQ2.to_le hCQ
  have : Fact (IsPGroup 2 ↥C) := ⟨hP2⟩
  have hcommP : commutator ↥C = Subgroup.center ↥C := by
    apply le_antisymm
    · rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      exact (hcenP _).mpr (hcommC x y)
    · intro x hx
      rcases (hcenP x).mp hx with rfl | rfl
      · exact Subgroup.one_mem _
      · rw [← hne, _root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hfrP : frattini ↥C = Subgroup.center ↥C := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (hx | ⟨y, rfl⟩)
      · rw [← hcommP]
        exact hx
      · exact (hcenP _).mpr (hsqC y)
    · intro x hx
      apply Subgroup.subset_closure
      left
      rw [hcommP]
      exact hx
  have hxP : ∀ x : ↥C, x ∉ Subgroup.center ↥C →
      Subgroup.closure (Set.range fun y => ⁅x, y⁆) = Subgroup.center ↥C := by
    intro x hx
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨y, rfl⟩
      exact (hcenP _).mpr (hcommC x y)
    · intro c hc
      rcases (hcenP c).mp hc with rfl | rfl
      · exact Subgroup.one_mem _
      · obtain ⟨y, hy⟩ : ∃ y : ↥C, ⁅x, y⁆ ≠ 1 := by
          by_contra hcon
          push Not at hcon
          apply hx
          rw [Subgroup.mem_center_iff]
          intro y
          exact ((commutatorElement_eq_one_iff_mul_comm).mp (hcon y)).symm
        have hxy : ⁅x, y⁆ = zC := (hcommC x y).resolve_left hy
        rw [← hxy]
        exact Subgroup.subset_closure ⟨y, rfl⟩
  have : Nontrivial ↥C := ⟨⟨zC, 1, hzC1⟩⟩
  have hS := CFSG.RankThree.Literature.isSemiExtraspecial_of_special Nat.prime_two hP2 hcommP
    hfrP hxP
  obtain ⟨n, -, hn, hidx, -⟩ := hS.rank_data Nat.prime_two hP2
  have hZ2 : Nat.card (Subgroup.center ↥C) = 2 := by
    have heq : Subgroup.center ↥C = Subgroup.zpowers zC := by
      apply le_antisymm
      · intro x hx
        rcases (hcenP x).mp hx with rfl | rfl
        · exact Subgroup.one_mem _
        · exact Subgroup.mem_zpowers _
      · exact Subgroup.zpowers_le.mpr ((hcenP zC).mpr (Or.inr rfl))
    rw [heq, Nat.card_zpowers]
    exact orderOf_eq_prime (Subtype.ext (by simpa [sq] using hzz)) hzC1
  have hCcard : Nat.card ↥C = 2 * 2 ^ (2 * n) := by
    rw [← Subgroup.card_mul_index (Subgroup.center ↥C), hZ2, hidx]
  have hCdvd : Nat.card ↥C ∣ 2 ^ 9 := by
    have := Subgroup.card_dvd_of_le hCQ
    rwa [hQ512] at this
  rw [hCcard] at hCdvd hmodQ ⊢
  have hn4 : n ≤ 4 := by
    have h1 : 2 ^ (1 + 2 * n) ∣ 2 ^ 9 := by rwa [pow_add, pow_one]
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h1
    omega
  interval_cases n
  · norm_num
  · exact absurd hmodQ (by decide)
  · exact absurd hmodQ (by decide)
  · exfalso
    apply hbQ
    have hCQeq : C = Q := Subgroup.eq_of_le_of_card_ge hCQ (by rw [hCcard, hQ512]; norm_num)
    intro q hq
    rw [← hCQeq] at hq
    exact hq.2

end Special

end CFSG.Quasithin.H13
