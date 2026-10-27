module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRNat
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRFrat

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Mod
  Equiv

variable {G : Type} [Group G] [Finite G] {X P Z : Subgroup G}

omit [Finite G] in
theorem relIndex_core_eq_sixty (e : OTwoQuot X ≃* ↥(alternatingGroup (Fin 5))) :
    (pCoreOf 2 X).relIndex X = 60 := by
  rw [relIndex_core_eq_card, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
    card_alternatingGroup]
  simp [Nat.factorial]

theorem relIndex_core_sylow_a5 (h : PushHyp X P Z) (e : OTwoQuot X ≃* ↥(alternatingGroup (Fin 5))) :
    (pCoreOf 2 X).relIndex P = 4 := by
  obtain ⟨n, hn, hmul, hodd⟩ := relIndex_core_sylow_dvd h
  rw [relIndex_core_eq_sixty e, hn] at hmul
  rw [hn]
  rcases n with _ | _ | _ | n
  · simp at hmul; omega
  · simp at hmul; omega
  · rfl
  · have : 2 ^ (n + 3) = 8 * 2 ^ n := by ring
    rw [this] at hmul
    have : 60 = 8 * (2 ^ n * P.relIndex X) := by rw [← hmul]; ring
    omega

theorem natFacts_of_a5 (h : PushHyp X P Z) (e : OTwoQuot X ≃* ↥(alternatingGroup (Fin 5)))
    (hnat : IsNatSecA5 X (zZero X Z) Z) : NatFacts X P Z := by
  obtain ⟨hnorm, θ, β, hθs, hθk, hsd⟩ := hnat
  obtain ⟨φ, hφs, hφk⟩ := exists_hom_of_quot e
  have hle : φ.ker ≤ θ.ker := fun x hx =>
    (mem_cSecIn_iff_of_ker_hom hθk x.2).mpr (core_le_cSecIn h _ ((hφk x).mp hx))
  have hker : ∀ x : ↥X, ((alternatingGroup (Fin 5)).subtype.comp θ) x = 1 →
      (x : G) ∈ pCoreOf 2 X := fun x hx =>
    (hφk x).mp (ker_le_of_surjective hφs hθs hle (Subtype.ext (by simpa using hx)))
  have hZ₀Z : zZero X Z ≤ Z := inf_le_left
  refine ⟨exists_odd_notin_core h (fun n hn => ?_), ?_, ?_⟩
  · rw [relIndex_core_eq_sixty e] at hn
    rcases n with _ | _ | _ | n
    · simp at hn
    · simp at hn
    · simp at hn
    · have : 2 ^ (n + 3) = 8 * 2 ^ n := by ring
      rw [this] at hn
      omega
  ·
    intro W hWZ hXW
    set U : Subgroup G := W ⊔ zZero X Z with hU
    have hLU : zZero X Z ≤ U := le_sup_right
    have hUZ : U ≤ Z := sup_le hWZ hZ₀Z
    have hinv : ∀ k ∈ X, ∀ u ∈ U, k * u * k⁻¹ ∈ U := by
      intro k hk u hu
      have hkU : cj k U = U := by
        rw [hU]
        unfold cj
        rw [Subgroup.map_sup]
        have h1 : cj k W = W := cj_eq_of_mem_normalizer (hXW hk)
        have h2 : cj k (zZero X Z) = zZero X Z := cj_eq_of_mem_normalizer (h.le_normalizer_Z0 hk)
        unfold cj at h1 h2
        rw [h1, h2]
      have : k * u * k⁻¹ ∈ cj k U := by
        rw [mem_cj]; simpa [mul_assoc] using hu
      rwa [hkU] at this
    obtain ⟨Y, hY, hYm⟩ := (hsd.invariant_iff_sub (K₀ := X) le_rfl hLU hUZ).mp hinv
    have hirr : Y = ⊥ ∨ Y = ⊤ := by
      by_cases hbot : ∀ u ∈ Y, u = 1
      · exact Or.inl ((Subgroup.eq_bot_iff_forall Y).mpr hbot)
      · right
        push Not at hbot
        obtain ⟨x, hxY, hx1⟩ := hbot
        rw [eq_top_iff]
        intro y _
        by_cases hy1 : y = 1
        · rw [hy1]; exact Y.one_mem
        · obtain ⟨σ, hσ, hσy⟩ := nat_transitive x y hx1 hy1
          obtain ⟨k, hk⟩ := hθs ⟨σ, hσ⟩
          have hkσ : ((alternatingGroup (Fin 5)).subtype.comp θ) k = σ := congrArg Subtype.val hk
          rw [← hσy]
          exact hY σ ⟨k, Subgroup.mem_subgroupOf.mpr k.2, hkσ⟩ x hxY
    rcases hirr with rfl | rfl
    · left
      refine le_trans (le_sup_left : W ≤ U) (fun u hu => ?_)
      have hu' : (QuotientGroup.mk' ((zZero X Z).subgroupOf Z)) ⟨u, hUZ hu⟩ ∈
          (U.subgroupOf Z).map (QuotientGroup.mk' ((zZero X Z).subgroupOf Z)) :=
        ⟨⟨u, hUZ hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
      rw [← hYm, Subgroup.map_bot, Subgroup.mem_bot] at hu'
      have := (QuotientGroup.eq_one_iff _).mp hu'
      exact Subgroup.mem_subgroupOf.mp this
    · right
      intro x hx
      have hx' : (QuotientGroup.mk (⟨x, hx⟩ : ↥Z) : ↥Z ⧸ (zZero X Z).subgroupOf Z) ∈
          (U.subgroupOf Z).map (QuotientGroup.mk' ((zZero X Z).subgroupOf Z)) := by
        rw [← hYm, Subgroup.map_top_of_surjective _ hsd.surj]
        exact Subgroup.mem_top _
      obtain ⟨c, hc, hcx⟩ := hx'
      have h1 : (x : G) * (c : G)⁻¹ ∈ zZero X Z := mk_eq_iff_mem.mp hcx
      have h2 : x = (x * (c : G)⁻¹) * (c : G) := by group
      rw [h2]
      exact U.mul_mem (hLU h1) (Subgroup.mem_subgroupOf.mp hc)
  ·
    intro x hxP hxQ
    rw [relIndex_core_sylow_a5 h e]
    have hxX : x ∈ X := h.le_self hxP
    have hΨ : ((alternatingGroup (Fin 5)).subtype.comp θ) ⟨x, hxX⟩ ≠ 1 := fun h1 => hxQ (hker _ h1)
    have h1 := hsd.secIdx_eq_idx hZ₀Z hxX
    have h2 := (transvections _ hΨ).1
    unfold secIdx at h1
    rw [h1]
    exact h2

end CFSG.Quasithin.F53Push
