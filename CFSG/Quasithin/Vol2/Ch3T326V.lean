module

public import CFSG.Quasithin.Vol2.Ch3T326E
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem not_isPGroup_two_of_isPSL {X : Type} [Group X] [Finite X] (h : IsPSL 3 2 1 X) :
    ¬ IsPGroup 2 X := by
  intro hp
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [SBc11.card_of_isPSL_three_two h] at hn
  have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 168)
  have h4 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at h4

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem H_le_NVM : L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ≤ Subgroup.normalizer
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) :=
  sup_le c.L_le_NVM (inf_le_left.trans c.T_le_NVM)

omit c in
theorem H_le_NL (_c : Ctx T L V₀) :
    L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ≤ Subgroup.normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer inf_le_right

theorem commute_of_mem_pCoreOf [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hL32 : IsPSL 3 2 1 ↥(autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))))
    {p : G} (hp : p ∈ pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G))))
    (hpVM : p ∈ Subgroup.normalizer (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)) : Set G)) :
    ∀ b ∈ autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))),
      conjAct _ ⟨p, hpVM⟩ * b = b * conjAct _ ⟨p, hpVM⟩ := by
  have hLVM := c.L_le_NVM
  have hHL := c.H_le_NL
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVMdef
  set H := L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) with hHdef
  set P := pCoreOf 2 H with hPdef
  have hPH : P ≤ H := Subgroup.map_subtype_le _
  have hLP : L ≤ Subgroup.normalizer (P : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hpL : p ∈ Subgroup.normalizer (L : Set G) := hHL (hPH hp)
  have hN₂VM : P ⊓ L ≤ Subgroup.normalizer (VM : Set G) := inf_le_right.trans hLVM
  have hLN₂ : L ≤ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G) :=
    (le_inf hLP Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hsimp : IsSimpleGroup ↥(autOn L VM) := SBc11.isSimpleGroup_of_list (Or.inl hL32)
  have hA2le : autOn (P ⊓ L) VM ≤ autOn L VM := InternalSec.autOn_le_autOn_of_le inf_le_right
  have hA2p : IsPGroup 2 ↥(autOn (P ⊓ L) VM) :=
    (((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe hN₂VM).symm).map (conjAct VM)
  have hA2n : ((autOn (P ⊓ L) VM).subgroupOf (autOn L VM)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA2le).mpr
      (H13.autOn_le_normalizer hN₂VM hLVM hLN₂)
  have hA2 : autOn (P ⊓ L) VM = ⊥ := by
    rcases hsimp.eq_bot_or_eq_top_of_normal ((autOn (P ⊓ L) VM).subgroupOf (autOn L VM)) with
      h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact disjoint_self.mp (h.mono_right hA2le)
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      exact not_isPGroup_two_of_isPSL hL32 (hA2p.to_le h)
  intro b hb
  obtain ⟨m, hm, rfl⟩ := Setup.mem_autOn_iff.mp hb
  have hcP : p * ((m : G) * p⁻¹ * (m : G)⁻¹) ∈ P :=
    P.mul_mem hp ((Subgroup.mem_normalizer_iff.mp (hLP hm) p⁻¹).mp (P.inv_mem hp))
  have hcL : p * (m : G) * p⁻¹ * (m : G)⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp hpL m).mp hm) (L.inv_mem hm)
  have hc : ((⟨p, hpVM⟩ * m * ⟨p, hpVM⟩⁻¹ * m⁻¹ : Subgroup.normalizer (VM : Set G)) : G) ∈
      P ⊓ L := by
    refine ⟨?_, hcL⟩
    have e : p * (m : G) * p⁻¹ * (m : G)⁻¹ = p * ((m : G) * p⁻¹ * (m : G)⁻¹) := by group
    show p * (m : G) * p⁻¹ * (m : G)⁻¹ ∈ P
    rw [e]
    exact hcP
  have h1 : conjAct VM (⟨p, hpVM⟩ * m * ⟨p, hpVM⟩⁻¹ * m⁻¹) ∈ autOn (P ⊓ L) VM :=
    Setup.mem_autOn_iff.mpr ⟨_, hc, rfl⟩
  rw [hA2, Subgroup.mem_bot, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc conjAct VM ⟨p, hpVM⟩ * conjAct VM m =
      (conjAct VM ⟨p, hpVM⟩ * conjAct VM m * (conjAct VM ⟨p, hpVM⟩)⁻¹ * (conjAct VM m)⁻¹) *
        conjAct VM m * conjAct VM ⟨p, hpVM⟩ := by group
    _ = conjAct VM m * conjAct VM ⟨p, hpVM⟩ := by rw [h1, one_mul]

end Ctx

end CFSG.Quasithin.H13.T326
