module

public import CFSG.Quasithin.H13.NQCoreP134X27Cfg
public import CFSG.Quasithin.Vol2.F134LieU3

public section

namespace CFSG.Quasithin.H13.NQCore.X27U3

open CFSG.Quasithin CFSG.Quasithin.P134 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.F134 CFSG.Quasithin.F134.LieU3
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem not_dvd_twentyseven_mul_cube {q : ℕ} (hq : 3 ≤ q) : ¬ q ^ 3 + 1 ∣ 27 * q ^ 3 := by
  intro hdvd
  have hcop : (q ^ 3 + 1).Coprime (q ^ 3) := Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have h27 := Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hdvd)
  have : 3 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  omega

theorem not_isCyclic_of_card_twentyseven {X : Type*} [Group X] {Q : Subgroup X}
    (hQ : Nat.card Q = 27) (hexp : ∀ x ∈ Q, x ^ 3 = 1) : ¬ IsCyclic Q := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  have h3 : g ^ 3 = 1 := Subtype.ext (by simpa using hexp g g.2)
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hg, hQ] at this
  norm_num at this

theorem three_le_of_model {X : Type} [Group X] {n : ℕ} (hL : StatedClassicalModel X .PSU 3 2 n) :
    3 ≤ 2 ^ n := by
  obtain ⟨-, hn1, -, hne⟩ := hL.1
  have hn : 2 ≤ n := by
    by_contra hlt
    obtain rfl : n = 1 := by omega
    exact hne rfl
  calc 3 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem noX27Simple_psu3Even (n : ℕ) :
    NoX27Simple fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 n := by
  intro A _ _ L P T hcfg h27 hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := three_le_of_model hL
  have hS := OddConfig.isSylowTwoOf_inf hcfg
  obtain ⟨K, _, h, Φ, hΦ, hrange, hTU⟩ := exists_perm_comap_rkOneUStar_eq hL
    ((hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).toSylow hS.2.2)
  replace hTU : (rkOneUStar h).comap Φ = (T ⊓ L).subgroupOf L := hTU
  have hcardU : Nat.card (T ⊓ L : Subgroup A) = (2 ^ n) ^ 3 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, ← hTU,
      ← Subgroup.card_map_of_injective hΦ, Subgroup.map_comap_eq, hrange,
      inf_eq_right.2 (rkOneUStar_le_rkOneG h), card_rkOneUStar h]
  have hUH : rkOneUStar h ≤ ((P ⊔ T ⊓ L).subgroupOf L).map Φ := by
    intro x hx
    have hx' : x ∈ Φ.range := by
      rw [hrange]
      exact rkOneUStar_le_rkOneG h hx
    obtain ⟨y, rfl⟩ := hx'
    have hy : y ∈ (rkOneUStar h).comap Φ := hx
    rw [hTU] at hy
    exact ⟨y, Subgroup.subgroupOf_mono _ le_sup_right hy, rfl⟩
  have hcardH : Nat.card (((P ⊔ T ⊓ L).subgroupOf L).map Φ) = 27 * (2 ^ n) ^ 3 := by
    rw [Subgroup.card_map_of_injective hΦ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddConfig.sup_inf_le hcfg)).toEquiv,
      OddConfig.card_sup_inf_x27 hcfg h27, hcardU]
  have hfix := le_stabilizer_infL_of_not_dvd h hUH (by
    rw [hcardH]
    exact not_dvd_twentyseven_mul_cube hq)
  have hQinf : (P.subgroupOf L).map Φ ≤ rkOneGInf h := fun x hx =>
    ⟨hrange ▸ Subgroup.map_le_range Φ _ hx,
      hfix (Subgroup.map_mono (Subgroup.subgroupOf_mono _ le_sup_left) hx)⟩
  have hQcard : Nat.card ((P.subgroupOf L).map Φ) = 27 := by
    rw [Subgroup.card_map_of_injective hΦ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, h27]
  have hQexp : ∀ x ∈ (P.subgroupOf L).map Φ, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy3 : y ^ 3 = 1 :=
      Subtype.ext (by simpa using hcfg.exp y (Subgroup.mem_subgroupOf.mp hy))
    rw [← map_pow, hy3, map_one]
  exact not_isCyclic_of_card_twentyseven hQcard hQexp
    (isCyclic_of_le_rkOneGInf h hQinf (by rw [hQcard]; norm_num))

theorem noE9Cfg_psu3Even (n : ℕ) :
    NoE9Cfg fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 n := by
  intro A _ _ L P T hL hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := three_le_of_model hL
  have hS := E9Cfg.isSylowTwoOf_inf hcfg
  obtain ⟨K, _, h, Φ, hΦ, hrange, hTU⟩ := exists_perm_comap_rkOneUStar_eq hL
    ((hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).toSylow hS.2.2)
  replace hTU : (rkOneUStar h).comap Φ = (T ⊓ L).subgroupOf L := hTU
  have hcardU : Nat.card (T ⊓ L : Subgroup A) = (2 ^ n) ^ 3 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, ← hTU,
      ← Subgroup.card_map_of_injective hΦ, Subgroup.map_comap_eq, hrange,
      inf_eq_right.2 (rkOneUStar_le_rkOneG h), card_rkOneUStar h]
  have hUH : rkOneUStar h ≤ ((P ⊔ T ⊓ L).subgroupOf L).map Φ := by
    intro x hx
    have hx' : x ∈ Φ.range := by
      rw [hrange]
      exact rkOneUStar_le_rkOneG h hx
    obtain ⟨y, rfl⟩ := hx'
    have hy : y ∈ (rkOneUStar h).comap Φ := hx
    rw [hTU] at hy
    exact ⟨y, Subgroup.subgroupOf_mono _ le_sup_right hy, rfl⟩
  have hcardH : Nat.card (((P ⊔ T ⊓ L).subgroupOf L).map Φ) = 9 * (2 ^ n) ^ 3 := by
    rw [Subgroup.card_map_of_injective hΦ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E9Cfg.sup_inf_le hcfg)).toEquiv,
      E9Cfg.card_sup_inf hcfg, hcardU]
  have hfix := le_stabilizer_infL_of_not_dvd h hUH (by
    rw [hcardH]
    exact not_dvd_nine_mul_cube hq)
  have hQinf : (P.subgroupOf L).map Φ ≤ rkOneGInf h := fun x hx =>
    ⟨hrange ▸ Subgroup.map_le_range Φ _ hx,
      hfix (Subgroup.map_mono (Subgroup.subgroupOf_mono _ le_sup_left) hx)⟩
  have hQcard : Nat.card ((P.subgroupOf L).map Φ) = 9 := by
    rw [Subgroup.card_map_of_injective hΦ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, hcfg.card]
  have hQexp : ∀ x ∈ (P.subgroupOf L).map Φ, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy3 : y ^ 3 = 1 :=
      Subtype.ext (by simpa using hcfg.exp y (Subgroup.mem_subgroupOf.mp hy))
    rw [← map_pow, hy3, map_one]
  exact not_isCyclic_of_card_nine hQcard hQexp
    (isCyclic_of_le_rkOneGInf h hQinf (by rw [hQcard]; norm_num))

theorem facts134X27_psu3Even : ∀ f : ℕ, 2 ≤ f →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 f := fun f _ =>
  noX27ConfigQ_of_noE9Cfg (fun _ _ _ _ e h => CFSG.SectionRank.statedClassicalModel_of_mulEquiv
    e.symm h) (noX27Simple_psu3Even f) (noE9Cfg_psu3Even f)

end CFSG.Quasithin.H13.NQCore.X27U3
