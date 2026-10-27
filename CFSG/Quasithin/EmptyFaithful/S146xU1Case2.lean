module

public import CFSG.Quasithin.EmptyFaithful.S146xU1Sec
public import CFSG.Quasithin.EmptyFaithful.S146xThreeA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section Case2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem Setting146.u1_case2 (S : Setting146 G T M) (c23 : Conc14623 T M) {K : Subgroup G} {u t : G}
    (hK : K ∈ cComp (mcOf T)) (htT : t ∈ T) (htn : t ∉ Subgroup.normalizer (K : Set G))
    (hper : perfectCore (mcOf T) = K ⊔ conjSub t K)
    (huK : u ∈ ⁅uOfL22 T M, K⁆) (huZ : u ∉ Zz)
    (hN : T ⊓ Subgroup.normalizer (K : Set G) ≤ tZero T u) :
    IsSylowTwoOf (tU T u) (mcOf T ⊓ Subgroup.centralizer ({u} : Set G)) ∧
      (tZero T u).relIndex T = 2 := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hTsyl : IsSylowTwoOf T (mcOf T) := S.isSylowTwoOf_mcOf
  have hUZ : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _
  have huU : u ∈ uOfL22 T M := by
    have hle : ⁅uOfL22 T M, K⁆ ≤ uOfL22 T M := by
      rw [Subgroup.commutator_le]
      intro a ha k hk
      have hkU : k ∈ Subgroup.normalizer (uOfL22 T M : Set G) := hHU (le_of_mem_cComp hK hk)
      have h1 : k * a⁻¹ * k⁻¹ ∈ uOfL22 T M :=
        (Subgroup.mem_normalizer_iff.mp hkU _).mp ((uOfL22 T M).inv_mem ha)
      have e : ⁅a, k⁆ = a * (k * a⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact (uOfL22 T M).mul_mem ha h1
    exact hle huK
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hG huU
  set Kt := conjSub t K with hKt_def
  have hKt : Kt ∈ cComp (mcOf T) := map_conj_mem_cComp hK (hTH htT)
  have hKtK : Kt ≠ K := fun h => htn (A38.map_conj_eq_iff.mp h)
  have hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kt := fun L hL =>
    cComp_eq_of_le_sup hL hK hKt
      (hper ▸ le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL))
  have hswap : ∀ b ∈ mcOf T, b ∉ Subgroup.normalizer (K : Set G) → conjSub b K = Kt := by
    intro b hb hbn
    rcases hcomps _ (map_conj_mem_cComp hK hb) with h | h
    · exact absurd (mem_normalizer_of_conjSub_eq h) hbn
    · exact h
  have hswap2 : ∀ b ∈ mcOf T, b ∉ Subgroup.normalizer (K : Set G) → conjSub b Kt = K := by
    intro b hb hbn
    rcases hcomps _ (map_conj_mem_cComp hKt hb) with h | h
    · exact h
    · exfalso
      apply hKtK
      have h1 : conjSub b K = Kt := hswap b hb hbn
      have h2 : conjSub b Kt = conjSub b K := h.trans h1.symm
      exact Subgroup.map_injective (f := (MulAut.conj b).toMonoidHom)
        (MulAut.conj b).injective h2
  have hdirect : ∀ b ∈ mcOf T, b ∉ Subgroup.normalizer (K : Set G) →
      b * u * b⁻¹ * u⁻¹ ∉ Zz := by
    intro b hb hbn hbz
    have hbU : b ∈ Subgroup.normalizer (uOfL22 T M : Set G) := hHU hb
    have huN : u ∈ Subgroup.normalizer (Zz : Set G) := hUZ huU
    have hbuU : b * u * b⁻¹ ∈ uOfL22 T M :=
      (Subgroup.mem_normalizer_iff.mp hbU _).mp huU
    have hbuN : b * u * b⁻¹ ∈ Subgroup.normalizer (Zz : Set G) := hUZ hbuU
    have h1 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨u, huN⟩ ∈
        tildeOf Zz ⁅uOfL22 T M, K⁆ := secMk_mem_secImg huK
    have hbu : b * u * b⁻¹ ∈ ⁅uOfL22 T M, Kt⁆ := by
      have h2 : b * u * b⁻¹ ∈ conjSub b ⁅uOfL22 T M, K⁆ := mul_mem_conjSub huK
      rwa [← conjSub_commutator, F7.conjSub_eq_of_mem_normalizer hbU, hswap b hb hbn] at h2
    have h3 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨u, huN⟩ =
        secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨b * u * b⁻¹, hbuN⟩ := by
      refine secMk_eq_secMk_iff.mpr ?_
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huN) _).mp hbz
      have e : u⁻¹ * (b * u * b⁻¹ * u⁻¹) * u⁻¹⁻¹ = u⁻¹ * (b * u * b⁻¹) := by group
      rw [e] at this
      exact this
    have h4 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨u, huN⟩ ∈
        tildeOf Zz ⁅uOfL22 T M, Kt⁆ := h3 ▸ secMk_mem_secImg hbu
    have h5 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨u, huN⟩ ∈
        ⨆ K' ∈ {K' | K' ∈ cComp (mcOf T) ∧ K' ≠ K}, tildeOf Zz ⁅uOfL22 T M, K'⁆ :=
      (le_iSup₂_of_le (f := fun K' (_ : K' ∈ {K' | K' ∈ cComp (mcOf T) ∧ K' ≠ K}) =>
        tildeOf Zz ⁅uOfL22 T M, K'⁆) Kt ⟨hKt, hKtK⟩ le_rfl) h4
    have h6 := c23.2.2.2 K hK
    have h7 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨u, huN⟩ ∈
        tildeOf Zz ⁅uOfL22 T M, K⁆ ⊓ ⨆ K' ∈ {K' | K' ∈ cComp (mcOf T) ∧ K' ≠ K},
          tildeOf Zz ⁅uOfL22 T M, K'⁆ := ⟨h1, h5⟩
    rw [h6] at h7
    exact huZ (secMk_eq_one_iff.mp (Subgroup.mem_bot.mp h7))
  have hT₀eq : tZero T u = T ⊓ Subgroup.normalizer (K : Set G) := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      by_contra hxn
      exact hdirect x (hTH hx.1) hxn (hx.2.2 u (Subgroup.mem_zpowers u))
    · exact fun hx => hN hx
  have h2 : (tZero T u).relIndex T = 2 := by
    refine Subgroup.relIndex_eq_two_iff.mpr ⟨t, htT, fun b hb => ?_⟩
    rw [hT₀eq]
    by_cases hbn : b ∈ Subgroup.normalizer (K : Set G)
    · right
      refine ⟨⟨hb, hbn⟩, fun h => htn ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hbn) h.2
      simpa using this
    · left
      refine ⟨⟨T.mul_mem hb htT, ?_⟩, fun h => hbn h.2⟩
      exact mem_normalizer_of_conjSub_eq (by rw [conjSub_mul]; exact hswap2 b (hTH hb) hbn)
  refine ⟨?_, h2⟩
  set H₂ := centralizerMod Zz (mcOf T) (Subgroup.zpowers u) with hH₂
  set H₁ : Subgroup G := mcOf T ⊓ Subgroup.normalizer (K : Set G) with hH₁
  have hH₁H : H₁ ≤ mcOf T := inf_le_left
  have hH₂H₁ : H₂ ≤ H₁ := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    by_contra hxn
    exact hdirect x hx.1 hxn (hx.2.2 u (Subgroup.mem_zpowers u))
  have hTH₂ : T ⊓ H₁ ≤ H₂ := by
    intro x hx
    have hx' : x ∈ tZero T u := hN ⟨hx.1, hx.2.2⟩
    exact ⟨hTH hx.1, hx'.2.1, hx'.2.2⟩
  have hT₀H₂eq : tZero T u = T ⊓ H₂ := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hTH hx.1, hx.2.1, hx.2.2⟩
    · intro hx
      exact ⟨hx.1, hx.2.2.1, hx.2.2.2⟩
  have hmul : ∀ h ∈ mcOf T, ∃ a ∈ H₁, ∃ b ∈ T, h = a * b := by
    intro h hh
    by_cases hhn : h ∈ Subgroup.normalizer (K : Set G)
    · exact ⟨h, ⟨hh, hhn⟩, 1, T.one_mem, by simp⟩
    · refine ⟨h * t, ⟨(mcOf T).mul_mem hh (hTH htT), ?_⟩, t⁻¹, T.inv_mem htT, by group⟩
      exact mem_normalizer_of_conjSub_eq (by rw [conjSub_mul]; exact hswap2 h hh hhn)
  have hodd₂ : ¬ 2 ∣ (tZero T u).relIndex H₂ := by
    rw [hT₀H₂eq]
    exact not_two_dvd_relIndex_inf_of_forall_mul hH₁H hH₂H₁ hTH₂ hmul hTsyl.2.2
  exact S.isSylowTwoOf_tU_of_odd huG hodd₂

end Case2

end CFSG.Quasithin
