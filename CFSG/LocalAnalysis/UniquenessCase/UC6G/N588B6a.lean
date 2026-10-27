module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588B4
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B6a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

open CFSG.Sporadic.Schreier.Tits

variable {G : Type} [Group G] [Finite G] {Dat : Data G}

structure TitsSetup (m : Mz614 Dat) where
  a : ↥titsD
  b : ↥titsD
  g : ↥titsD
  ha : a ^ 5 = 1
  hb : b ^ 5 = 1
  hab : a * b = b * a
  hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
    a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j'
  hga : g * a * g⁻¹ = a ^ 3 * b ^ 4
  hgb : g * b * g⁻¹ = a ^ 2 * b ^ 4
  ψ : ↥m.L ≃* ↥titsD
  mem_iff : ∀ x : ↥m.L, x ∈ (m.A ⊓ m.L).subgroupOf m.L ↔ ψ x ∈ planeSub_uc6 hab ha hb

namespace TitsSetup

variable {m : Mz614 Dat} (T : TitsSetup m)

@[expose] def plane : Subgroup ↥titsD := planeSub_uc6 T.hab T.ha T.hb

@[expose] noncomputable def n : G := ((T.ψ.symm T.g : ↥m.L) : G)

@[expose] noncomputable def y : G := ((T.ψ.symm (T.g ^ 3) : ↥m.L) : G)

theorem exists_exp {x : G} (hx : x ∈ m.A ⊓ m.L) :
    ∃ i j : ℕ, T.ψ ⟨x, hx.2⟩ = T.a ^ i * T.b ^ j := by
  obtain ⟨i, j, hij⟩ := (T.mem_iff ⟨x, hx.2⟩).1 hx
  exact ⟨i, j, hij⟩

theorem psi_conj (h : ↥titsD) {x : G} (hx : x ∈ m.L) :
    T.ψ ⟨((T.ψ.symm h : ↥m.L) : G) * x * ((T.ψ.symm h : ↥m.L) : G)⁻¹,
      m.L.mul_mem (m.L.mul_mem (T.ψ.symm h).2 hx) (m.L.inv_mem (T.ψ.symm h).2)⟩ =
      h * T.ψ ⟨x, hx⟩ * h⁻¹ := by
  have e1 : (⟨((T.ψ.symm h : ↥m.L) : G) * x * ((T.ψ.symm h : ↥m.L) : G)⁻¹,
      m.L.mul_mem (m.L.mul_mem (T.ψ.symm h).2 hx) (m.L.inv_mem (T.ψ.symm h).2)⟩ : ↥m.L) =
      T.ψ.symm h * ⟨x, hx⟩ * (T.ψ.symm h)⁻¹ := Subtype.ext (by simp)
  rw [e1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem conj_mem_of_normalizes (h : ↥titsD)
    (hh : ∀ i j : ℕ, h * (T.a ^ i * T.b ^ j) * h⁻¹ ∈ T.plane) :
    ∀ x ∈ m.A ⊓ m.L,
      ((T.ψ.symm h : ↥m.L) : G) * x * ((T.ψ.symm h : ↥m.L) : G)⁻¹ ∈ m.A ⊓ m.L := by
  intro x hx
  obtain ⟨i, j, hij⟩ := T.exists_exp hx
  have h1 := T.psi_conj h hx.2
  rw [hij] at h1
  have h2 : T.ψ ⟨_, m.L.mul_mem (m.L.mul_mem (T.ψ.symm h).2 hx.2)
      (m.L.inv_mem (T.ψ.symm h).2)⟩ ∈ T.plane := h1 ▸ hh i j
  exact (T.mem_iff _).2 h2

theorem g_mem (i j : ℕ) : T.g * (T.a ^ i * T.b ^ j) * T.g⁻¹ ∈ T.plane :=
  ⟨_, _, conj_plane_tits_uc6 T.hab T.ha T.hb T.hga T.hgb i j⟩

theorem g_cube_mem (i j : ℕ) : T.g ^ 3 * (T.a ^ i * T.b ^ j) * (T.g ^ 3)⁻¹ ∈ T.plane := by
  rw [conj_cube_tits_uc6 T.hab T.ha T.hb T.hga T.hgb, plane_pow_uc6 T.hab]
  exact ⟨_, _, rfl⟩

theorem n_mem (h620 : m.C620) : T.n ∈ m.L ⊓ m.W :=
  ⟨(T.ψ.symm T.g).2, mem_W_of_mem_L h620 (T.ψ.symm T.g).2 (T.conj_mem_of_normalizes T.g T.g_mem)⟩

theorem y_mem (h620 : m.C620) : T.y ∈ m.L ⊓ m.W :=
  ⟨(T.ψ.symm (T.g ^ 3)).2, mem_W_of_mem_L h620 (T.ψ.symm (T.g ^ 3)).2
    (T.conj_mem_of_normalizes (T.g ^ 3) T.g_cube_mem)⟩

theorem y_conj : ∀ x ∈ m.A ⊓ m.L, T.y * x * T.y⁻¹ = x ^ 2 := by
  intro x hx
  obtain ⟨i, j, hij⟩ := T.exists_exp hx
  have h1 := T.psi_conj (T.g ^ 3) hx.2
  rw [hij, conj_cube_tits_uc6 T.hab T.ha T.hb T.hga T.hgb, ← hij, ← map_pow] at h1
  have h2 := congrArg Subtype.val (T.ψ.injective h1)
  simpa [y] using h2

theorem map_le_plane {X : Subgroup G} (hX : X ≤ m.A ⊓ m.L) :
    (X.subgroupOf m.L).map T.ψ.toMonoidHom ≤ T.plane ∧
      Nat.card ((X.subgroupOf m.L).map T.ψ.toMonoidHom) = Nat.card X := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (T.mem_iff x).1 (hX hx)
  · rw [Subgroup.card_map_of_injective T.ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hX.trans inf_le_right)).toEquiv]

theorem map_normalized {X : Subgroup G} (hX : X ≤ m.A ⊓ m.L)
    (hXn : X.map (MulAut.conj (T.n ^ 2)).toMonoidHom = X) :
    ∀ u ∈ (X.subgroupOf m.L).map T.ψ.toMonoidHom, T.g ^ 2 * u * (T.g ^ 2)⁻¹ ∈
      (X.subgroupOf m.L).map T.ψ.toMonoidHom := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (T.n ^ 2) * (x : G) * (T.n ^ 2)⁻¹ ∈ X := by
    rw [← hXn]
    exact ⟨x, hx, rfl⟩
  refine ⟨⟨(T.n ^ 2) * (x : G) * (T.n ^ 2)⁻¹, m.L.mul_mem (m.L.mul_mem
    (m.L.pow_mem (T.ψ.symm T.g).2 2) x.2) (m.L.inv_mem (m.L.pow_mem (T.ψ.symm T.g).2 2))⟩, hx',
    ?_⟩
  have h1 := T.psi_conj (T.g ^ 2) x.2
  simp only [map_pow, Subgroup.coe_pow] at h1
  simpa [n] using h1

theorem not_normalizes {Y : Subgroup ↥titsD} (hY : Y ≤ T.plane) (hY5 : Nat.card Y = 5)
    (hgY : ∀ y ∈ Y, T.g ^ 2 * y * (T.g ^ 2)⁻¹ ∈ Y) : False :=
  tits_sq_not_normalizes_uc6 T.hab T.ha T.hb T.hinj T.hga T.hgb hY hY5 hgY

end TitsSetup

theorem c621_of_titsSetup {m : Mz614 Dat} (T : TitsSetup m) (h620 : m.C620) (hr : m.r = 5) :
    m.C621 := by
  intro W' hW'B hW'N
  by_contra hcon
  push Not at hcon
  have hdvd : Nat.card W' ∣ 5 ^ 2 := by
    rw [← hr, ← m.card_A_inf_L h620]
    exact Subgroup.card_dvd_of_le hW'B
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
  interval_cases k
  · exact hcon.1 (Subgroup.eq_bot_of_card_eq W' (by simpa using hk'))
  · obtain ⟨hY1, hY2⟩ := T.map_le_plane hW'B
    have hn2 : W'.map (MulAut.conj (T.n ^ 2)).toMonoidHom = W' := by
      apply le_antisymm
      · rintro _ ⟨w, hw, rfl⟩
        exact (mem_normalizer_iff.1 (hW'N ((m.L ⊓ m.W).pow_mem (T.n_mem h620) 2)) w).1 hw
      · intro w hw
        refine ⟨(T.n ^ 2)⁻¹ * w * (T.n ^ 2), ?_, ?_⟩
        swap
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        have := (mem_normalizer_iff.1 (hW'N ((m.L ⊓ m.W).inv_mem
          ((m.L ⊓ m.W).pow_mem (T.n_mem h620) 2))) w).1 hw
        simpa using this
    exact T.not_normalizes hY1 (by rw [hY2, hk', pow_one]) (T.map_normalized hW'B hn2)
  · exact hcon.2 (Subgroup.eq_of_le_of_card_ge hW'B (by
      rw [hk', m.card_A_inf_L h620, hr]))


theorem exists_titsSetup (m : Mz614 Dat) (h620 : m.C620) (hr : m.r = 5)
    (hL : IsoLie ↥m.L .tits) : Nonempty (TitsSetup m) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := titsModelEquiv ↥m.L 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits hL)
  obtain ⟨a, b, g, ha, hb, hab, hinj, hga, hgb⟩ := tits_plane_uc6
  set S₀ := planeSub_uc6 hab ha hb with hS₀def
  have hS₀ : Nat.card S₀ = 5 ^ (Nat.card ↥titsD).factorization 5 := by
    rw [card_planeSub_uc6 hab ha hb hinj, factorization_card_titsD_uc6]
    norm_num
  set S0 : Subgroup ↥m.L := (m.A ⊓ m.L).subgroupOf m.L with hS0
  have hS0card : Nat.card S0 = 5 ^ (Nat.card ↥m.L).factorization 5 := by
    rw [hS0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
      m.card_A_inf_L h620, hr, Nat.card_congr e.toEquiv, factorization_card_titsD_uc6]
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_sylow_eq_uc6 e S₀ hS₀ (Sylow.ofCard S0 hS0card)
  exact ⟨⟨a, b, g, ha, hb, hab, hinj, hga, hgb, ψ, fun x => hψ x⟩⟩

theorem c621_of_tits (m : Mz614 Dat) (h620 : m.C620) (hr : m.r = 5) (hL : IsoLie ↥m.L .tits) :
    m.C621 := by
  obtain ⟨T⟩ := exists_titsSetup m h620 hr hL
  exact c621_of_titsSetup T h620 hr

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
