module

public import CFSG.Quasithin.H13.A6S1515b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] def InK4ext (σ : Perm (Fin 6)) : Prop := σ ∈ K4L ∨ σ * swap 4 5 ∈ K4L

instance : DecidablePred InK4ext := fun σ => by unfold InK4ext; infer_instance

theorem pow_eq_sixtyfour {a n : ℕ} (h : 256 * n = 2 ^ a * 36) (hodd : ¬ 2 ∣ n) : 2 ^ a = 64 := by
  have h1 : 64 ∣ 2 ^ a := by
    have : 64 ∣ 2 ^ a * 9 := ⟨n, by linarith⟩
    exact Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) this
  have h6 : 6 ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 (by simpa using h1)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h6
  rcases b with _ | b
  · rfl
  · exfalso
    apply hodd
    exact ⟨2 ^ b * 9, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 256) (by rw [h]; ring)⟩

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Data

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hhat : ¬ IsHatA6 L)
  (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
  {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (hl : S.frame.ρ l = lK)
  (hobl : Obl13_5_14Six) (hctk : Input13515CTK)
include hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk

theorem cT_eq_V : T ⊓ Subgroup.centralizer (V : Set G) = V :=
  S.cT.trans (S.pCoreOf_LT_six hNS h13315 h1356two hH hn hna hhat hlL hl hobl hctk)

omit hctk in
theorem V_le_L : V ≤ L := by
  obtain ⟨-, -, -, hO2K, -, -⟩ := S.obl_data hNS hH hn hna hhat hlL hl hobl
  exact hO2K ▸ (pCoreOf_le 2 _).trans (S.KH_le_L hNS h13315 h1356two hH hn hna hlL)

theorem pCoreOf_M_eq_V
    : pCoreOf 2 (Subgroup.normalizer (L : Set G)) = V := by
  rw [S.normalizer_L_six hNS h13315 h1356two hH hn hna hhat hlL hl hobl hctk,
    S.pCoreOf_LT_six hNS h13315 h1356two hH hn hna hhat hlL hl hobl hctk]

theorem mem_L_of_sign {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgM : (g : G) ∈ Subgroup.normalizer (L : Set G)) (hs : Perm.sign (S.frame.ρ g) = 1) :
    (g : G) ∈ L := by
  have hOM := S.pCoreOf_M_eq_V hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk
  obtain ⟨l', hlL', hl'⟩ := (S.frame.image_L _).2 (Perm.mem_alternatingGroup.2 hs)
  have hk : S.frame.ρ (l'⁻¹ * g) = 1 := by rw [map_mul, map_inv, hl', inv_mul_cancel]
  have hkC := (S.rho_eq_one_iff _).1 hk
  have hkM : ((l'⁻¹ * g : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
      Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hlL')) hgM
  have hkC' : ((l'⁻¹ * g : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
      Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (L : Set G)) : Set G) := by
    rw [hOM]
    exact hkC
  have hkV : ((l'⁻¹ * g : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ V := by
    have h := S.charTwo_M ⟨hkM, hkC'⟩
    rwa [hOM] at h
  have e : (g : G) = l' * ((l'⁻¹ * g : ↥(Subgroup.normalizer (V : Set G))) : G) := by
    simp
  rw [e]
  exact L.mul_mem hlL' (S.V_le_L hNS h13315 h1356two hH hhat hn hna hlL hl hobl hkV)

theorem exists_odd (hTL : ¬ T ≤ L) :
    ∃ t : ↥(Subgroup.normalizer (V : Set G)), (t : G) ∈ T ∧ Perm.sign (S.frame.ρ t) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hTL
  intro t ht
  exact S.mem_L_of_sign hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk
    (g := ⟨t, S.frame.T_le ht⟩) (S.T_le_NL ht) (hcon _ ht)

theorem rho_T_surj
    (hTL : ¬ T ≤ L) (σ : Perm (Fin 6)) (hσ : InD6 σ) :
    ∃ t : ↥(Subgroup.normalizer (V : Set G)), (t : G) ∈ T ∧ S.frame.ρ t = σ := by
  by_cases hs : Perm.sign σ = 1
  · exact S.frame.DA_T σ hσ (Perm.mem_alternatingGroup.2 hs)
  obtain ⟨t₀, ht₀T, ht₀⟩ := S.exists_odd hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
  have hD : σ * (S.frame.ρ t₀)⁻¹ ∈ D6sub :=
    D6sub.mul_mem hσ (D6sub.inv_mem (S.frame.T_D t₀ ht₀T))
  have hsgn : Perm.sign (σ * (S.frame.ρ t₀)⁻¹) = 1 := by
    rw [Perm.sign_mul, Perm.sign_inv]
    rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
    · exact absurd h1 hs
    rcases Int.units_eq_one_or (Perm.sign (S.frame.ρ t₀)) with h2 | h2
    · exact absurd h2 ht₀
    rw [h1, h2]
    rfl
  obtain ⟨t₁, ht₁T, ht₁⟩ := S.frame.DA_T _ hD (Perm.mem_alternatingGroup.2 hsgn)
  refine ⟨t₁ * t₀, T.mul_mem ht₁T ht₀T, ?_⟩
  rw [map_mul, ht₁, inv_mul_cancel_right]

theorem card_T_six (hTL : ¬ T ≤ L) : Nat.card T = 256 := by
  have hTV := S.cT_eq_V hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk
  let f : ↥T →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion S.frame.T_le)
  have hker : f.ker = V.subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show S.frame.ρ (Subgroup.inclusion S.frame.T_le t) = 1 ↔ (t : G) ∈ V
    rw [S.rho_eq_one_iff]
    constructor
    · intro h
      rw [← hTV]
      exact ⟨t.2, h⟩
    · intro h
      exact S.V_le_centralizer_V h
  have hrange : f.range = D6sub := by
    ext σ
    constructor
    · rintro ⟨t, rfl⟩
      exact S.frame.T_D _ t.2
    · intro hσ
      obtain ⟨t, htT, ht⟩ :=
        S.rho_T_surj hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL σ hσ
      exact ⟨⟨t, htT⟩, ht⟩
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange, card_D6sub, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.V_le_T).toEquiv, S.card_V] at h1
  exact h1.symm

theorem card_Q_six
    (hTL : ¬ T ≤ L) : Nat.card (pCoreOf 2 H) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := S.nonempty_pf15_six hNS h13315 h1356two hH hn hna hhat hlL hl hobl
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hH36 : Nat.card H = Nat.card (pCoreOf 2 H) * 36 := by
    rw [P.card_H, S.card_range_six hNS h13315 h1356two hH hhat hna P]
  have hidx := Subgroup.card_mul_index (T.subgroupOf H)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF.T_le_H).toEquiv,
    S.card_T_six hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL] at hidx
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 H).exists_card_eq
  rw [ha] at hH36 ⊢
  exact pow_eq_sixtyfour (hidx.trans hH36) hF.sylow_H.2.2

end Data

end Setting4

end CFSG.Quasithin.H13.A6
