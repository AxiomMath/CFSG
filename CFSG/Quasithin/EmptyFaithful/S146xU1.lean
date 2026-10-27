module

public import CFSG.Quasithin.EmptyFaithful.S146xU1Norm
public import CFSG.Quasithin.EmptyFaithful.S146xU1Case2
public import CFSG.Quasithin.EmptyFaithful.S146F22

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

@[expose] def U1A6Res : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), Ctx24 T M K U₁ U₂ s u → KbarIsA6 K →
      centralizerMod (quasithinOmegaOneCenter T) (mcOf T) (Subgroup.zpowers u) ≤
          Subgroup.normalizer (U₁ : Set G) ∧
        (tZero T u).relIndex T = 2

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem exists_mul_of_perfectCore (hTH : T ≤ mcOf T) (c23 : Conc14623 T M) :
    ∀ h ∈ mcOf T, ∃ a ∈ perfectCore (mcOf T), ∃ b ∈ T, h = a * b := by
  intro h hh
  have hTN : T ≤ Subgroup.normalizer (perfectCore (mcOf T) : Set G) := fun t ht =>
    normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer (hTH ht))
  have hc := Subgroup.coe_mul_of_right_le_normalizer_left (perfectCore (mcOf T)) T hTN
  have hh' : h ∈ ((perfectCore (mcOf T) ⊔ T : Subgroup G) : Set G) := by
    rw [← c23.1.2]
    exact hh
  rw [hc] at hh'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hh'
  exact ⟨a, ha, b, hb, rfl⟩

theorem input14624U1_of_A6 (hA6 : U1A6Res) : Input14624U1 := by
  intro G _ _ T M S hB K U₁ U₂ s u hctx
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  by_cases hA : KbarIsA6 K
  ·
    obtain ⟨hH₂U, h2⟩ := hA6 G T M S hB K U₁ U₂ s u hctx hA
    obtain ⟨-, -, c23, hK, c21, -, hdec, hchoice⟩ := hctx
    have hKG : K ≤ mcOf T := le_of_mem_cComp hK
    have hper : perfectCore (mcOf T) = K := by
      rcases c21 with ⟨hper, -⟩ | ⟨⟨-, -⟩, hL3⟩ | ⟨-, -, -, -, -, -, hL3, -⟩
      · exact hper
      · exact (not_kbarIsA6_of_kbarIsL3Two hL3 hA).elim
      · exact (not_kbarIsA6_of_kbarIsL3Two hL3 hA).elim
    have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
      rw [← hper]
      exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
    obtain ⟨huU, hN⟩ : u ∈ U₁ ∧ T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u := by
      rcases hchoice with ⟨-, huU, -, hN⟩ | ⟨⟨t, ht, htn, -⟩, -⟩
      · exact ⟨huU, hN⟩
      · exact absurd (hKn (hTH ht)) htn
    have hKZ : K ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun k hk =>
      S.normalizer_Z.ge (hKG hk)
    have hKU₁ : K ≤ Subgroup.normalizer (U₁ : Set G) := by
      rcases hdec.natural with ⟨hL3', -⟩ | ⟨-, hnat⟩
      · exact (not_kbarIsA6_of_kbarIsL3Two hL3' hA).elim
      · rcases hnat with ⟨-, hirr, -⟩ | ⟨-, hcomm⟩
        · exact hirr.2.1
        · rw [← hcomm]
          exact le_normalizer_sup_of_le (Subgroup.normalizer_commutator_ge_right U₁ K) hKZ
    have hU₁U : U₁ ≤ uOfL22 T M := by
      have hKU : K ≤ Subgroup.normalizer (uOfL22 T M : Set G) :=
        hKG.trans (le_normalizer_conjClosure _ _)
      have h1 : ⁅uOfL22 T M, K⁆ ≤ uOfL22 T M := S145.commutator_le_of_le_normalizer hKU
      have hZU : quasithinOmegaOneCenter T ≤ uOfL22 T M := Z_le_conjClosure_VZ T M (mcOf T)
      have h2 : U₁ ⊔ U₂ ≤ uOfL22 T M := by
        rw [← hdec.sup]
        exact sup_le h1 hZU
      exact le_sup_left.trans h2
    have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hG (hU₁U huU)
    have hmulK : ∀ h ∈ mcOf T, ∃ a ∈ K, ∃ b ∈ T, h = a * b := by
      rw [← hper]
      exact exists_mul_of_perfectCore hTH c23
    exact ⟨S.isSylowTwoOf_tU_of_normalizes huG hH₂U hKG hKU₁ hmulK hN, h2⟩
  obtain ⟨c19, -, c23, hK, c21, c22, hdec, hchoice⟩ := hctx
  have hmul := exists_mul_of_perfectCore hTH c23
  rcases c21 with ⟨hper, hL⟩ | ⟨⟨t, ht, htn, hper⟩, hL3⟩ | ⟨Kp, hKp, hKpK, hHK, hHKp, hper, hL3, -⟩
  ·
    have hL3 : KbarIsL3Two K := hL.resolve_right hA
    have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
      rw [← hper]
      exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
    obtain ⟨huU, hunc, hN⟩ : u ∈ U₁ ∧ ¬ ⁅Subgroup.zpowers u, K⁆ ≤ quasithinOmegaOneCenter T ∧
        T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u := by
      rcases hchoice with ⟨-, huU, hunc, hN⟩ | ⟨⟨t, ht, htn, -⟩, -⟩
      · exact ⟨huU, hunc, hN⟩
      · exact absurd (hKn (hTH ht)) htn
    obtain ⟨hSec, -, -⟩ := S.sec8_of_decomp hK hL3 hdec
    exact S.u1_normal c19 hK hL3 hdec hKn (perfectCore_le _)
      (by rw [hper]; exact hSec.KU) hmul huU hunc hN
  ·
    obtain ⟨huK, huZ, hN⟩ : u ∈ ⁅uOfL22 T M, K⁆ ∧ u ∉ quasithinOmegaOneCenter T ∧
        T ⊓ Subgroup.normalizer (K : Set G) ≤ tZero T u := by
      rcases hchoice with ⟨hnc, -⟩ | ⟨-, huK, huZ, hN⟩
      · exact absurd ⟨t, ht, htn, hper⟩ hnc
      · exact ⟨huK, huZ, hN⟩
    exact S.u1_case2 c23 hK ht htn hper huK huZ hN
  ·
    obtain ⟨huU, hunc, hN⟩ : u ∈ U₁ ∧ ¬ ⁅Subgroup.zpowers u, K⁆ ≤ quasithinOmegaOneCenter T ∧
        T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u := by
      rcases hchoice with ⟨-, huU, hunc, hN⟩ | ⟨⟨t, ht, htn, -⟩, -⟩
      · exact ⟨huU, hunc, hN⟩
      · exact absurd (hHK (hTH ht)) htn
    obtain ⟨hSec, -, -⟩ := S.sec8_of_decomp hK hL3 hdec
    have hKpU : Kp ≤ Subgroup.centralizer (U₁ : Set G) := by
      have hUK : ⁅uOfL22 T M, K⁆ ≤ Subgroup.centralizer (Kp : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (c22.2 Kp hKp hKpK)
      have hZ : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (Kp : Set G) := fun z hz =>
        Subgroup.mem_centralizer_iff.mpr fun k hk =>
          S146T.comm_Z (le_of_mem_cComp hKp hk) hz
      have hsup : ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T ≤ Subgroup.centralizer (Kp : Set G) :=
        sup_le hUK hZ
      intro k hk
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have hx' : x ∈ ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T := by
        rw [hdec.sup]
        exact Subgroup.mem_sup_left hx
      exact (Subgroup.mem_centralizer_iff.mp (hsup hx') k hk).symm
    exact S.u1_normal c19 hK hL3 hdec hHK (perfectCore_le _)
      (by rw [hper]; exact sup_le hSec.KU (hKpU.trans (Subgroup.centralizer_le_normalizer _)))
      hmul huU hunc hN

end Main

end CFSG.Quasithin
