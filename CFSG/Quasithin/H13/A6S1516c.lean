module

public import CFSG.Quasithin.H13.A6S1516b
public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth

theorem exists_conj_mem_of_isPGroup2 {X : Type} [Group X] [Finite X] {R S : Subgroup X}
    (hR : IsPGroup 2 R) (hS : quasithinIsSylowTwo S) : ∃ g : X, ∀ t ∈ R, g * t * g⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  obtain ⟨P, hP⟩ : ∃ P : Sylow 2 X, (P : Subgroup X) = S := ⟨hS.1.toSylow hS.2, rfl⟩
  subst hP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  refine ⟨g, fun t ht => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have : (MulAut.conj g)⁻¹ • (g * t * g⁻¹) = t := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]
    group
  rw [this]
  exact hRQ ht

namespace A5SitPf15

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  {S : A5Sit G T V V₁ V₃ L₁ H} {SY : A5SitY S L₁} (P : A5SitPf15 S SY)
include P

theorem exists_sq_z : ∃ u ∈ conjClosure V₃ H, u * u = P.C.z := by
  obtain ⟨u, hu⟩ := P.C.θ_surj (Multiplicative.ofAdd (idc 0))
  refine ⟨u, u.2, ?_⟩
  rcases P.C.sq u with ⟨h, -⟩ | ⟨-, h⟩
  · rw [hu, toAdd_ofAdd] at h
    exact absurd h (by decide)
  · rw [← pow_two]
    exact h

variable (hQ : Nat.card (pCoreOf 2 H) = 64)
include hQ

omit hQ in
theorem V1_le_Z1 : V₁ ≤ P.Z1 := by
  intro v hv
  have h : v ∈ conjClosure V₃ H ⊓ P.Z1 := by
    rw [P.U_inf_Z1]
    exact hv
  exact h.2

theorem index_V1_Z1 : (V₁.subgroupOf P.Z1).index = 2 := by
  have h := Subgroup.relIndex_mul_card V₁ P.Z1
  rw [inf_eq_left.2 P.V1_le_Z1, S.card_V1, P.card_Z1 hQ] at h
  show V₁.relIndex P.Z1 = 2
  omega

theorem mul_inv_mem_V1 {x y : G} (hx : x ∈ P.Z1) (hy : y ∈ P.Z1) (hxV : x ∉ V₁) (hyV : y ∉ V₁) :
    x * y⁻¹ ∈ V₁ := by
  have key := Subgroup.mul_mem_iff_of_index_two (P.index_V1_Z1 hQ) (a := ⟨x, hx⟩)
    (b := (⟨y, hy⟩ : ↥P.Z1)⁻¹)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at key
  rw [key]
  exact ⟨fun h => absurd h hxV, fun h => absurd (by simpa using V₁.inv_mem h) hyV⟩

theorem sq_mem_V1 {q : G} (hq : q ∈ pCoreOf 2 H) : q * q ∈ V₁ := by
  obtain ⟨u, hu, j, hj, rfl⟩ := P.decomp hQ hq
  have hju : u * j = j * u := Subgroup.mem_centralizer_iff.mp hj.2 u hu
  have hu2 : u * u ∈ V₁ := by
    rcases P.C.sq ⟨u, hu⟩ with ⟨-, h⟩ | ⟨-, h⟩
    · rw [← pow_two]
      exact (P.Cz _).2 (Or.inl h)
    · rw [← pow_two]
      exact (P.Cz _).2 (Or.inr h)
  have hj2 : j * j ∈ V₁ := by
    by_cases hjV : j ∈ V₁
    · exact V₁.mul_mem hjV hjV
    · have h := P.mul_inv_mem_V1 hQ hj (P.Z1.inv_mem hj) hjV (fun h => hjV (by
        simpa using V₁.inv_mem h))
      simpa using h
  have e : u * j * (u * j) = u * u * (j * j) := by
    calc u * j * (u * j) = u * (j * u) * j := by group
      _ = u * (u * j) * j := by rw [hju]
      _ = u * u * (j * j) := by group
  rw [e]
  exact V₁.mul_mem hu2 hj2

theorem normalizer_Q_le :
    Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ Subgroup.centralizer ({P.C.z} : Set G) := by
  intro x hx
  obtain ⟨u, hu, hu2⟩ := P.exists_sq_z
  have hxu : x * u * x⁻¹ ∈ pCoreOf 2 H := (Subgroup.mem_normalizer_iff.mp hx u).mp (S.U_le_Q hu)
  have h := P.sq_mem_V1 hQ hxu
  have e : x * u * x⁻¹ * (x * u * x⁻¹) = x * P.C.z * x⁻¹ := by
    rw [← hu2]
    group
  rw [e] at h
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases (P.Cz _).1 h with h1 | h1
  · exfalso
    apply P.C.z_ne
    calc P.C.z = x⁻¹ * (x * P.C.z * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  · calc x * P.C.z = x * P.C.z * x⁻¹ * x := by group
      _ = P.C.z * x := by rw [h1]

end A5SitPf15

namespace A6

@[expose] def wK : Perm (Fin 6) := swap 0 2 * swap 2 4 * (swap 1 3 * swap 3 5)

theorem wK_facts : Perm.sign wK = 1 ∧ wK * wK * wK = 1 ∧
    InW2 (act4f wK⁻¹ e0123) ∧ InW2 (act4f wK⁻¹ (act4f wK⁻¹ e0123)) ∧
    act4f wK⁻¹ e0123 ≠ e0123 ∧ act4f wK⁻¹ (act4f wK⁻¹ e0123) ≠ e0123 ∧
    e0123 * act4f wK⁻¹ e0123 * act4f wK⁻¹ (act4f wK⁻¹ e0123) = 1 := by
  decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_V2_of_psi {x : G} (hx : x ∈ V) (h : InW2 (S.frame.ψ ⟨x, hx⟩ : P6)) : x ∈ S.V2 :=
  S.mem_pre.2 ⟨hx, h⟩

section Data

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hhat : ¬ IsHatA6 L)
  (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
  {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (hl : S.frame.ρ l = lK)
  (hobl : Obl13_5_14Six) (hctk : Input13515CTK) (hTL : ¬ T ≤ L)
include hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL

theorem relIndex_TL : (T ⊓ L).relIndex T = 2 := by
  let f : ↥T →* ℤˣ := Perm.sign.comp (S.frame.ρ.comp (Subgroup.inclusion S.frame.T_le))
  have hker : f.ker = (T ⊓ L).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨t.2, S.mem_L_of_sign hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk
        (g := ⟨t, S.frame.T_le t.2⟩) (S.T_le_NL t.2) h⟩
    · rintro ⟨-, htL⟩
      exact Perm.mem_alternatingGroup.1
        ((S.frame.image_L _).1 ⟨⟨t, S.frame.T_le t.2⟩, htL, rfl⟩)
  have hrange : f.range = ⊤ := by
    obtain ⟨t₀, ht₀T, ht₀⟩ := S.exists_odd hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
    rw [eq_top_iff]
    intro s _
    rcases Int.units_eq_one_or s with rfl | rfl
    · exact f.range.one_mem
    · refine ⟨⟨t₀, ht₀T⟩, ?_⟩
      rcases Int.units_eq_one_or (Perm.sign (S.frame.ρ t₀)) with h | h
      · exact absurd h ht₀
      · exact h
  show ((T ⊓ L).subgroupOf T).index = 2
  rw [← hker, Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
    Fintype.card_units_int]

theorem false_of_not_conj {x : G} (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxz : ∀ g : G, g * S.z * g⁻¹ ≠ x) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup2 hxp S.h13.sylow
  set x' := g * x * g⁻¹ with hx'
  have hx'T : x' ∈ T := hg x (Subgroup.mem_zpowers x)
  have hnotL : ∀ k : G, k⁻¹ * x' * k ∉ L := by
    intro k hk
    have hk2 : k⁻¹ * x' * k * (k⁻¹ * x' * k) = 1 := by
      calc k⁻¹ * x' * k * (k⁻¹ * x' * k) = k⁻¹ * g * (x * x) * g⁻¹ * k := by rw [hx']; group
        _ = 1 := by rw [hx2]; group
    have hk1 : k⁻¹ * x' * k ≠ 1 := by
      intro h
      apply hx1
      calc x = g⁻¹ * k * (k⁻¹ * x' * k) * k⁻¹ * g := by rw [hx']; group
        _ = 1 := by rw [h]; group
    obtain ⟨g', hg'⟩ := S.exists_conj_z_of_L hNS h13315 h1356two hH hna hhat hn hlL hl hobl hctk
      hk hk2 hk1
    apply hxz (g⁻¹ * k * g')
    calc g⁻¹ * k * g' * S.z * (g⁻¹ * k * g')⁻¹ = g⁻¹ * k * (g' * S.z * g'⁻¹) * k⁻¹ * g := by group
      _ = x := by rw [hg', hx']; group
  have hTsyl := S.h13.sylow
  obtain ⟨N, hNn, hN⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hTsyl.1 hTsyl.2
    inf_le_left (S.relIndex_TL hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL) hx'T
    (fun h => hnotL 1 (by simpa using h.2))
    (fun y hyT hyU => by
      have hord' : orderOf x' = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · rw [hx', pow_two]
          calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
            _ = 1 := by rw [hx2]; group
        · intro h
          apply hx1
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = 1 := by rw [← hx', h]; group
      rw [hord']
      have hy1 : y ≠ 1 := fun h => hyU (h ▸ (T ⊓ L).one_mem)
      have := orderOf_pos y
      have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
      omega)
    (fun k hk => hnotL k hk.2)
  have hsimp := S.h13.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h, Subgroup.index_bot] at hN
    have hT : Nat.card T ∣ Nat.card G := Subgroup.card_subgroup_dvd_card T
    rw [S.card_T_six hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL, hN] at hT
    norm_num at hT
  · rw [h, Subgroup.index_top] at hN
    omega

end Data

end Setting4

end A6

end CFSG.Quasithin.H13
