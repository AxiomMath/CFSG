module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.FLc

open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def conjSub (h : G) (N : Subgroup G) : Subgroup G := N.map (MulAut.conj h).toMonoidHom

theorem mem_conjSub {h : G} {N : Subgroup G} {x : G} : x ∈ conjSub h N ↔ h⁻¹ * x * h ∈ N := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    have e : h⁻¹ * (h * n * h⁻¹) * h = n := by group
    show h⁻¹ * (h * n * h⁻¹) * h ∈ N
    rw [e]
    exact hn
  · intro hx
    refine ⟨h⁻¹ * x * h, hx, ?_⟩
    show h * (h⁻¹ * x * h) * h⁻¹ = x
    group

theorem conjSub_mono (h : G) {N N' : Subgroup G} (hN : N ≤ N') : conjSub h N ≤ conjSub h N' :=
  fun _ hx => mem_conjSub.2 (hN (mem_conjSub.1 hx))

theorem conjSub_inv_conjSub (h : G) (N : Subgroup G) : conjSub h⁻¹ (conjSub h N) = N := by
  ext x
  rw [mem_conjSub, mem_conjSub]
  have e : h⁻¹⁻¹ * x * h⁻¹ = h * x * h⁻¹ := by group
  have e2 : h⁻¹ * (h * x * h⁻¹) * h = x := by group
  rw [e, e2]

theorem conjSub_conjSub_inv (h : G) (N : Subgroup G) : conjSub h (conjSub h⁻¹ N) = N := by
  have := conjSub_inv_conjSub h⁻¹ N
  rwa [inv_inv] at this

theorem conjSub_lt_conjSub (h : G) {N N' : Subgroup G} (hN : N < N') :
    conjSub h N < conjSub h N' := by
  refine lt_of_le_of_ne (conjSub_mono h hN.le) fun he => ?_
  have := congrArg (conjSub h⁻¹) he
  rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  exact hN.ne this

theorem conjSub_eq_of_mem {P : Subgroup G} {h : G} (hh : h ∈ P) : conjSub h P = P := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro hx
    have := P.mul_mem (P.mul_mem hh hx) (P.inv_mem hh)
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rwa [e] at this
  · intro hx
    exact P.mul_mem (P.mul_mem (P.inv_mem hh) hx) hh

theorem card_conjSub (h : G) (N : Subgroup G) : Nat.card (conjSub h N) = Nat.card N :=
  Subgroup.card_map_of_injective (MulAut.conj h).injective

theorem le_of_normalizes_of_sylow [Finite G] {L P B T : Subgroup G} (hT : IsSylowTwoOf T L)
    (hTP : T ≤ P) (hPL : P ≤ L) (hBL : B ≤ L) (hB2 : IsPGroup 2 B)
    (hBN : B ≤ Subgroup.normalizer (P : Set G)) : B ≤ P := by
  have hTD : IsSylowTwoOf T (B ⊔ P) :=
    A4.isSylowTwoOf_mono hT (hTP.trans le_sup_right) (sup_le hBL hPL)
  have h1 : P.relIndex (B ⊔ P) = P.relIndex B := A4.relIndex_sup_eq_of_le_normalizer' hBN
  have h2 : T.relIndex P * P.relIndex (B ⊔ P) = T.relIndex (B ⊔ P) :=
    Subgroup.relIndex_mul_relIndex T P (B ⊔ P) hTP le_sup_right
  have hodd' : ¬ 2 ∣ T.relIndex (B ⊔ P) := hTD.2.2
  have hodd : ¬ 2 ∣ P.relIndex (B ⊔ P) := fun hd => hodd' (by rw [← h2]; exact hd.mul_left _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hB2.index (P.subgroupOf B)
  have h3 : P.relIndex B = 2 ^ k := hk
  rw [h1, h3] at hodd
  have hk0 : k = 0 := by
    by_contra hne
    exact hodd (dvd_pow_self 2 hne)
  rw [hk0, pow_zero] at h3
  exact Subgroup.relIndex_eq_one.1 h3

theorem isMaxSubgroupIn_conjSub {P N : Subgroup G} {h : G} (hh : h ∈ P)
    (hN : IsMaxSubgroupIn P N) : IsMaxSubgroupIn P (conjSub h N) := by
  refine ⟨?_, fun K hNK hKP => ?_⟩
  · have := conjSub_lt_conjSub h hN.1
    rwa [conjSub_eq_of_mem hh] at this
  · have h1 : conjSub h⁻¹ K ≤ P := by
      have := conjSub_mono h⁻¹ hKP
      rwa [conjSub_eq_of_mem (P.inv_mem hh)] at this
    have h2 : N < conjSub h⁻¹ K := by
      have := conjSub_lt_conjSub h⁻¹ hNK
      rwa [conjSub_inv_conjSub] at this
    have h3 := hN.2 _ h2 h1
    have h4 := congrArg (conjSub h) h3
    rw [conjSub_conjSub_inv, conjSub_eq_of_mem hh] at h4
    exact h4

theorem minParabolic_transfer [Finite G] {L P B : Subgroup G} (hpar : IsMinParabolicOf L P)
    (hB : IsSylowTwoOf B L) (hBN : B ≤ Subgroup.normalizer (P : Set G)) :
    B < P ∧ P ≤ L ∧ ∀ N₁ N₂ : Subgroup G, IsMaxSubgroupIn P N₁ → B ≤ N₁ → IsMaxSubgroupIn P N₂ →
      B ≤ N₂ → N₁ = N₂ := by
  obtain ⟨T, hT, hPT⟩ := hpar
  obtain ⟨⟨hPL, hTP, hn1⟩, -⟩ := hPT
  have hBP : B ≤ P := le_of_normalizes_of_sylow hT hTP.le hPL hB.1 hB.2.1 hBN
  have hTP' : IsSylowTwoOf T P := A4.isSylowTwoOf_mono hT hTP.le hPL
  have hBP' : IsSylowTwoOf B P := A4.isSylowTwoOf_mono hB hBP hPL
  obtain ⟨h, hhP, hconj⟩ := A4.exists_conj_of_isSylowTwoOf hTP' hBP'
  have hBT : B = conjSub h T := by
    ext x
    rw [hconj x, mem_conjSub]
  refine ⟨?_, hPL, fun N₁ N₂ hN₁ hBN₁ hN₂ hBN₂ => ?_⟩
  · rw [hBT]
    have := conjSub_lt_conjSub h hTP
    rwa [conjSub_eq_of_mem hhP] at this
  ·
    have key : ∀ N : Subgroup G, IsMaxSubgroupIn P N → B ≤ N →
        IsMaxSubgroupIn P (conjSub h⁻¹ N) ∧ T ≤ conjSub h⁻¹ N := by
      intro N hN hBN'
      refine ⟨isMaxSubgroupIn_conjSub (P.inv_mem hhP) hN, ?_⟩
      intro t ht
      rw [mem_conjSub]
      apply hBN'
      rw [hBT, mem_conjSub]
      have e : h⁻¹ * ((h⁻¹)⁻¹ * t * h⁻¹) * h = t := by group
      rw [e]
      exact ht
    obtain ⟨N, hN⟩ := Set.ncard_eq_one.1 hn1
    have e1 : conjSub h⁻¹ N₁ ∈ ({N} : Set (Subgroup G)) := by
      rw [← hN]
      exact key N₁ hN₁ hBN₁
    have e2 : conjSub h⁻¹ N₂ ∈ ({N} : Set (Subgroup G)) := by
      rw [← hN]
      exact key N₂ hN₂ hBN₂
    have e3 : conjSub h⁻¹ N₁ = conjSub h⁻¹ N₂ :=
      (Set.mem_singleton_iff.1 e1).trans (Set.mem_singleton_iff.1 e2).symm
    have e4 := congrArg (conjSub h) e3
    rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at e4

theorem isMaxSubgroupIn_of_card [Finite G] {P B : Subgroup G} (hBP : B ≤ P)
    (h : Nat.card P = 3 * Nat.card B) : IsMaxSubgroupIn P B := by
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hlt : B < P := by
    refine lt_of_le_of_ne hBP fun he => ?_
    rw [he] at h
    have : 0 < Nat.card P := Nat.card_pos
    omega
  refine ⟨hlt, fun K hBK hKP => ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hBK.le
  have hKdvd := Subgroup.card_dvd_of_le hKP
  have hKlt := Subgroup.card_lt_of_lt hBK
  rw [h, hm] at hKdvd
  have hm3 : m ∣ 3 := by
    have : Nat.card B * m ∣ Nat.card B * 3 := by
      rw [mul_comm (Nat.card B) 3]
      exact hKdvd
    exact Nat.dvd_of_mul_dvd_mul_left hpos this
  rcases (Nat.dvd_prime Nat.prime_three).1 hm3 with rfl | rfl
  · rw [mul_one] at hm
    omega
  · exact Subgroup.eq_of_le_of_card_ge hKP (by rw [h, hm]; omega)

end CFSG.Quasithin.FLc
