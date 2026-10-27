module

public import CFSG.Quasithin.H13.GoldschmidtM22EndS3
public import CFSG.Quasithin.H13.GoldschmidtM22EndN2c

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

theorem le_of_isPGroup_of_le {T X : Subgroup G} (hT : quasithinIsSylowTwo T) (hTX : T ≤ X)
    (hX : IsPGroup 2 X) : X ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hX.index (T.subgroupOf X)
  have h2 : T.relIndex X ∣ T.index := Subgroup.relIndex_dvd_index_of_le hTX
  have hn' : T.relIndex X = 2 ^ n := hn
  rw [hn'] at h2
  have h3 : n = 0 := by
    by_contra hne
    exact hT.2 (dvd_trans (dvd_pow_self 2 hne) h2)
  rw [h3, pow_zero] at hn'
  exact Subgroup.relIndex_eq_one.mp hn'

namespace PsiData

variable (P : PsiData T L V 3) (h : Hyp6Sec2 G T M L V)

include h in
theorem exists_a (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h6210 : Stmt6_2_10) :
    ∃ a : ↥(HH T), (a : G) ∈ V ∧ (a : G) ∉ CHU T L V := by
  obtain ⟨v₀, hv₀V, hv₀C⟩ : ∃ v₀ ∈ V, v₀ ∉ CHU T L V := by
    by_contra hcon
    push Not at hcon
    exact not_V_le_CHU h h6210 fun v hv => hcon v hv
  exact ⟨⟨v₀, V_le_HH h hZ hv₀V⟩, hv₀V, hv₀C⟩

include P h in
theorem psi_eq_of_mem_M (h629 : Stmt6_2_9) (a : ↥(HH T)) (haV : (a : G) ∈ V)
    (haC : (a : G) ∉ CHU T L V) (x : ↥(HH T)) (hx : (x : G) ∈ M) :
    P.ψ x = 1 ∨ P.ψ x = P.ψ a := by
  obtain ⟨hτ, hNa⟩ := P.swap_norm a haV haC
  have hxN : (x : G) ∈ Subgroup.normalizer (V : Set G) := by
    have hxHM : (x : G) ∈ HH T ⊓ M := Subgroup.mem_inf.mpr ⟨x.2, hx⟩
    rw [(h629 G T M L V h).1] at hxHM
    exact (Subgroup.mem_inf.mp hxHM).2
  have hc := (hNa x).mp hxN
  exact perm3_centralizer_swap _ _ (Equiv.Perm.card_support_eq_two.mpr hτ) hc

include P h in
theorem isPGroup_HH_inf_M (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h629 : Stmt6_2_9)
    (h6210 : Stmt6_2_10) (h6212 : Stmt6_2_12) : IsPGroup 2 ↥(HH T ⊓ M) := by
  obtain ⟨a, haV, haC⟩ := exists_a h hZ h6210
  have hτ : (P.ψ a).support.card = 2 :=
    Equiv.Perm.card_support_eq_two.mpr (P.swap_norm a haV haC).1
  have hCHU : CHU T L V = pCoreOf 2 (HH T) := (h6212 G T M L V h).2.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro ⟨x, hx⟩
  set x' : ↥(HH T) := ⟨x, (Subgroup.mem_inf.mp hx).1⟩ with hx'
  have hsq : P.ψ x' ^ 2 = 1 := by
    rcases psi_eq_of_mem_M P h h629 a haV haC x' (Subgroup.mem_inf.mp hx).2 with h1 | h1
    · rw [h1, one_pow]
    · rw [h1]
      exact perm3_swap_sq _ hτ
  have hker : ((x' ^ 2 : ↥(HH T)) : G) ∈ CHU T L V := (P.ker _).mp (by rw [map_pow, hsq])
  have hmem : x ^ 2 ∈ pCoreOf 2 (HH T) := hCHU ▸ hker
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (HH T) ⟨x ^ 2, hmem⟩
  refine ⟨k + 1, ?_⟩
  apply Subtype.ext
  have hk' : (x ^ 2) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  show x ^ 2 ^ (k + 1) = 1
  rw [pow_succ', pow_mul]
  exact hk'

include P h in
theorem HH_inf_M_eq_T (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h629 : Stmt6_2_9)
    (h6210 : Stmt6_2_10) (h6212 : Stmt6_2_12) : HH T ⊓ M = T :=
  le_antisymm (le_of_isPGroup_of_le h.sylow (le_inf (T_le_HH T) h.T_le)
    (isPGroup_HH_inf_M P h hZ h629 h6210 h6212)) (le_inf (T_le_HH T) h.T_le)

end PsiData

end CFSG.Quasithin.H13.GM22
