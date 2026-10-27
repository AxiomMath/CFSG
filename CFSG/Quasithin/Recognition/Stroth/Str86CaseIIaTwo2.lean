module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwo
public import CFSG.Quasithin.Recognition.F112WChief

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_one_lt_relIndex_sup_of_not_le {Lo X : Subgroup G} (h : ¬ X ≤ Lo) :
    1 < Lo.relIndex (X ⊔ Lo) := by
  have hle : Lo ≤ X ⊔ Lo := le_sup_right
  have hne : Lo.relIndex (X ⊔ Lo) ≠ 1 := by
    intro h1
    exact h (le_trans le_sup_left (Subgroup.relIndex_eq_one.mp h1))
  have hpos : 0 < Lo.relIndex (X ⊔ Lo) := by
    have : Lo.subgroupOf (X ⊔ Lo) ≠ ⊤ := by
      intro htop
      apply hne
      rw [Subgroup.relIndex, htop, Subgroup.index_top]
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  omega

theorem str86_commutator_mem_of_mem_sup {Nβ S K H X Lo : Subgroup G}
    (hNβ : Nβ = S ⊔ K) (hSN : Nβ ≤ Subgroup.normalizer (S : Set G))
    (hSH : S ≤ H) (hKH : K ≤ H)
    (hSX : ∀ s ∈ S, ∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ Lo)
    (hKX : ∀ k ∈ K, ∀ x ∈ X, k * x * k⁻¹ * x⁻¹ ∈ Lo)
    (hLoH : ∀ h ∈ H, ∀ y ∈ Lo, h * y * h⁻¹ ∈ Lo) :
    ∀ n ∈ Nβ, ∀ x ∈ X, n * x * n⁻¹ * x⁻¹ ∈ Lo := by
  classical
  intro n hn x hx
  have hNβle : Nβ ≤ Subgroup.normalizer (S : Set G) := hSN
  have hSNβ : S ≤ Nβ := hNβ.symm ▸ le_sup_left
  have hKNβ : K ≤ Nβ := hNβ.symm ▸ le_sup_right
  have hsup : S.subgroupOf Nβ ⊔ K.subgroupOf Nβ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hSNβ hKNβ, ← hNβ, Subgroup.subgroupOf_self]
  have hSNormal : (S.subgroupOf Nβ).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNβle
  letI : (S.subgroupOf Nβ).Normal := hSNormal
  have hmem : (⟨n, hn⟩ : ↥Nβ) ∈ (⊤ : Subgroup ↥Nβ) := Subgroup.mem_top _
  rw [← hsup] at hmem
  obtain ⟨s, hs, k, hk, hsk⟩ := (Subgroup.mem_sup_of_normal_left).mp hmem
  have hs' : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
  have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  have hn_eq : n = (s : G) * (k : G) := by
    have := congrArg (Subtype.val) hsk
    simpa using this.symm
  rw [hn_eq]
  change ⁅(s : G) * (k : G), x⁆ ∈ Lo
  rw [commutator_mul_eq]
  exact Lo.mul_mem (hLoH (s : G) (hSH hs') _ (hKX (k : G) hk' x hx))
    (hSX (s : G) hs' x hx)

theorem isChiefSeriesFrom_of_le_module {H U U' N : Subgroup G} {n : ℕ}
    (hU'U : U' ≤ U) (hNU' : N ≤ U') (h : IsChiefSeriesFrom H U N n) :
    IsChiefSeriesFrom H U' N n := by
  induction h with
  | bot => exact .bot
  | @central N L n hstep hc hs ih =>
    have hLNU' : L ≤ U' := hstep.2.2.1.le.trans hNU'
    have hstep' : IsChiefStep H U' L N := by
      refine ⟨⟨hNU', hstep.1.2⟩, ⟨hLNU', hstep.2.1.2⟩, hstep.2.2.1, ?_⟩
      intro K hK hLK hKN
      exact hstep.2.2.2 K ⟨hK.1.trans hU'U, hK.2⟩ hLK hKN
    exact .central hstep' hc (ih hLNU')
  | @noncentral N L n hstep hnc hs ih =>
    have hLNU' : L ≤ U' := hstep.2.2.1.le.trans hNU'
    have hstep' : IsChiefStep H U' L N := by
      refine ⟨⟨hNU', hstep.1.2⟩, ⟨hLNU', hstep.2.1.2⟩, hstep.2.2.1, ?_⟩
      intro K hK hLK hKN
      exact hstep.2.2.2 K ⟨hK.1.trans hU'U, hK.2⟩ hLK hKN
    exact .noncentral hstep' hnc (ih hLNU')

theorem str86_two_section_bookkeeping {H U U₂ U₁ U_N : Subgroup G}
    (hUH : U ≤ H) (hU₂U₁ : U₂ ≤ U₁) (hU₁UN : U₁ ≤ U_N) (hUNU : U_N ≤ U)
    (hU₂n : IsNormalIn H U U₂) (hU₁n : IsNormalIn H U U₁) (hUNn : IsNormalIn H U U_N)
    (hUn : IsNormalIn H U U)
    (hcentral : H ≤ Subgroup.centralizer (U₂ : Set G))
    (hc : IsChiefSeriesFrom H U U 2)
    (hUNnoncentral : ¬ IsChiefSeriesFrom H U U_N 0) :
    ∃ n₀ n₁ : ℕ,
      F112W.IsChiefSeriesBetween H U U₁ U_N n₀ ∧
      F112W.IsChiefSeriesBetween H U U₂ U₁ n₁ ∧
      1 ≤ n₀ + n₁ ∧ n₀ + n₁ ≤ 2 := by
  classical
  obtain ⟨n₂, h₂⟩ := F112W.exists_isChiefSeriesBetween hUNn U hUn hUNU
  obtain ⟨n₀, h₀⟩ := F112W.exists_isChiefSeriesBetween hU₁n U_N hUNn hU₁UN
  obtain ⟨n₁, h₁⟩ := F112W.exists_isChiefSeriesBetween hU₂n U₁ hU₁n hU₂U₁
  obtain ⟨nbot, hbot⟩ := D15Proof.exists_isChiefSeriesFrom (H := H) (U := U) U₂ hU₂n
  have hbot0 : nbot = 0 := isChiefSeriesFrom_zero_of_le_centralizer hcentral hbot
  subst hbot0
  have hfromU₁ : IsChiefSeriesFrom H U U₁ n₁ := by
    simpa using h₁.append hbot
  have hfromUN : IsChiefSeriesFrom H U U_N (n₀ + n₁) := h₀.append hfromU₁
  have hfromU : IsChiefSeriesFrom H U U (n₂ + (n₀ + n₁)) := h₂.append hfromUN
  have heq : n₂ + (n₀ + n₁) = 2 :=
    F112W.isChiefSeriesFrom_unique hUH hfromU hc
  have hle : n₀ + n₁ ≤ 2 := by omega
  have hge : 1 ≤ n₀ + n₁ := by
    by_contra hlt
    have hzero : n₀ + n₁ = 0 := by omega
    exact hUNnoncentral (hzero ▸ hfromUN)
  exact ⟨n₀, n₁, h₀, h₁, hge, hle⟩

theorem str86_two_section_indices {S U U₂ U₁ N p P : Subgroup G} {k : ℕ}
    (hk : 2 ≤ k) (hUe : IsElemAbelian 2 U) (hU₂U : U₂ ≤ U) (hPU : P ≤ U)
    (hU₂C : U₂ ≤ Subgroup.centralizer (S : Set G))
    (hp : p = N ⊓ Subgroup.centralizer (S : Set G))
    (hPN : P ≤ N) (hpP : p ≤ P) (hpU₂ : p ≤ U₂)
    (hrelP : p.relIndex P = (2 ^ k) ^ 2)
    (hNnotU₁ : ¬ N ≤ U₁) :
    U₂ ⊓ P = p ∧ U₂.relIndex (U₂ ⊔ P) = (2 ^ k) ^ 2 ∧
      1 < U₁.relIndex (N ⊔ U₁) ∧ 1 < U₂.relIndex (P ⊔ U₂) := by
  classical
  have hU₂normP : U₂ ≤ Subgroup.normalizer (P : Set G) := by
    have hU₂C : U₂ ≤ Subgroup.centralizer (P : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (congrArg Subtype.val (hUe.1.is_comm.comm ⟨y, hU₂U hy⟩
        ⟨x, hPU hx⟩)).symm
    exact hU₂C.trans (Subgroup.centralizer_le_normalizer (P : Set G))
  have hinf : U₂ ⊓ P = p := by
    refine le_antisymm ?_ (le_inf hpU₂ hpP)
    intro x hx
    obtain ⟨hxU₂, hxP⟩ := Subgroup.mem_inf.mp hx
    exact hp ▸ ⟨hPN hxP, hU₂C hxU₂⟩
  have hrelU₂ : U₂.relIndex (U₂ ⊔ P) = (2 ^ k) ^ 2 := by
    rw [← CFSG.Quasithin.B6.relIndex_inf_eq_relIndex_sup hU₂normP, hinf, hrelP]
  have hPnotU₂ : ¬ P ≤ U₂ := by
    intro hPU₂
    have : U₂ ⊓ P = P := inf_eq_right.mpr hPU₂
    have hcard : p.relIndex P = 1 := by
      rw [← hinf, this, Subgroup.relIndex_self]
    rw [hcard] at hrelP
    have hk2 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hq : (2 ^ k) ^ 2 ≠ 1 := by nlinarith
    exact hq hrelP.symm
  exact ⟨hinf, hrelU₂, str86_one_lt_relIndex_sup_of_not_le hNnotU₁,
    str86_one_lt_relIndex_sup_of_not_le hPnotU₂⟩

end CFSG.Quasithin.Stroth
