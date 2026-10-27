module

public import CFSG.RankThree.PartTwo.Sec12.Hering129GTrans
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129G

variable {G : Type} [Group G] [Finite G]

theorem exists_zpow_mul_of_mem_sup_zpowers_sup {E F : Subgroup G} {x : G}
    (hEdec : E = Subgroup.zpowers x ⊔ F) (hxF : ∀ f ∈ F, x * f = f * x) :
    ∀ e ∈ E, ∃ k : ℤ, ∃ f ∈ F, e = x ^ k * f := by
  intro e he
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers x) F (fun u hu v hv => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (Commute.zpow_left (hxF v hv) k).eq)
  have he' : e ∈ ((Subgroup.zpowers x ⊔ F : Subgroup G) : Set G) := hEdec ▸ he
  rw [hset] at he'
  obtain ⟨u, hu, f, hf, rfl⟩ := he'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact ⟨k, f, hf, rfl⟩

theorem card_eq_nine_of_sup {E F : Subgroup G} {x : G} (hE : Late.IsE27 E)
    (hEdec : E = Subgroup.zpowers x ⊔ F) (hxF : x ∉ F) (hx3 : x ^ 3 = 1) :
    Nat.card F = 9 := by
  have hEc : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hFE : F ≤ E := hEdec ▸ le_sup_right
  have hxE : x ∈ E := hEdec ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hx1 : x ≠ 1 := fun h => hxF (h ▸ F.one_mem)
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers x) F (fun u hu v hv => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (Commute.zpow_left (hEc v (hFE hv) x hxE).symm k).eq)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hinf : Subgroup.zpowers x ⊓ F = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers x ⊓ F : Subgroup G) ∣ 3 := by
      rw [← hxo, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      apply hxF
      have heq : Subgroup.zpowers x ⊓ F = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hxo])
      have : x ∈ Subgroup.zpowers x ⊓ F := by
        rw [heq]; exact Subgroup.mem_zpowers x
      exact this.2
  rw [hinf, Subgroup.card_bot, mul_one, ← hEdec, hE.2, Nat.card_zpowers, hxo] at hcard
  omega

theorem exists_conj_of_autIn_sl23 {E F M : Subgroup G} {x : G} (hxE : x ∈ E) (hFE : F ≤ E)
    (hEdec : E = Subgroup.zpowers x ⊔ F) (hF9 : Nat.card F = 9)
    (hMx : ∀ m ∈ M, m * x = x * m)
    (hMF : ∀ m ∈ M, m ∈ Subgroup.normalizer (E : Set G) → ∀ f ∈ F, m * f * m⁻¹ ∈ F)
    (hxF : ∀ f ∈ F, x * f = f * x)
    (hΓ : Nonempty (Sec4.autIn M E ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) :
    ∀ u ∈ F, u ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      ∃ m ∈ M, m ∈ Subgroup.normalizer (E : Set G) ∧ m * u * m⁻¹ = v := by
  set Ω : Set E := {w | (w : G) ∈ F ∧ w ≠ 1} with hΩdef
  have hdec := exists_zpow_mul_of_mem_sup_zpowers_sup hEdec hxF
  have hΩ : Ω.ncard = 8 := by
    have h1 : Ω = ((F.subgroupOf E : Subgroup E) : Set E) \ {1} := by
      ext w
      simp [hΩdef, Subgroup.mem_subgroupOf]
    rw [h1, Set.ncard_diff_singleton_of_mem (Subgroup.one_mem _), ← Nat.card_coe_set_eq]
    have h2 : Nat.card (F.subgroupOf E) = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv
    rw [SetLike.coe_sort_coe, h2, hF9]
  have hinv : ∀ γ ∈ Sec4.autIn M E, ∀ w ∈ Ω, γ w ∈ Ω := by
    intro γ hγ w hw
    obtain ⟨m, hN, hM, rfl⟩ := Sec4.mem_autIn_iff.mp hγ
    refine ⟨?_, ?_⟩
    · rw [Sec4.normalizerMonoidHom_apply_coe]
      exact hMF m hM hN w hw.1
    · intro h1
      apply hw.2
      have h2 := congrArg (fun y : E => (y : G)) h1
      simp only [Sec4.normalizerMonoidHom_apply_coe, Subgroup.coe_one] at h2
      apply Subtype.ext
      simpa using h2
  have hfaith : ∀ γ ∈ Sec4.autIn M E, (∀ w ∈ Ω, γ w = w) → γ = 1 := by
    intro γ hγ hfix
    obtain ⟨m, hN, hM, rfl⟩ := Sec4.mem_autIn_iff.mp hγ
    ext e
    obtain ⟨k, f, hf, hef⟩ := hdec e e.2
    have hxcoe : ((E.normalizerMonoidHom ⟨m, hN⟩ ⟨x, hxE⟩ : E) : G) = x := by
      rw [Sec4.normalizerMonoidHom_apply_coe, hMx m hM]
      group
    have hfe : E.normalizerMonoidHom ⟨m, hN⟩ ⟨f, hFE hf⟩ = ⟨f, hFE hf⟩ := by
      by_cases hf1 : f = 1
      · have h1 : (⟨f, hFE hf⟩ : E) = 1 := Subtype.ext hf1
        rw [h1, map_one]
      · exact hfix _ ⟨hf, fun h1 => hf1 (congrArg Subtype.val h1)⟩
    have hxfix : E.normalizerMonoidHom ⟨m, hN⟩ ⟨x, hxE⟩ = ⟨x, hxE⟩ := Subtype.ext hxcoe
    have hee : e = (⟨x, hxE⟩ : E) ^ k * ⟨f, hFE hf⟩ := Subtype.ext (by simpa using hef)
    rw [hee, map_mul, map_zpow, hfe, hxfix]
    rfl
  intro u hu hu1 v hv hv1
  have hu' : (⟨u, hFE hu⟩ : E) ∈ Ω := ⟨hu, fun h => hu1 (congrArg Subtype.val h)⟩
  have hv' : (⟨v, hFE hv⟩ : E) ∈ Ω := ⟨hv, fun h => hv1 (congrArg Subtype.val h)⟩
  obtain ⟨γ, hγ, hγuv⟩ := transitive_of_sl23 (Sec4.autIn M E) hΓ Ω hΩ hinv hfaith _ hu' _ hv'
  obtain ⟨m, hN, hM, rfl⟩ := Sec4.mem_autIn_iff.mp hγ
  refine ⟨m, hM, hN, ?_⟩
  have := congrArg (fun y : E => (y : G)) hγuv
  simpa only [Sec4.normalizerMonoidHom_apply_coe] using this

end Hering129G

end CFSG.RankThree.PartTwo.Sec12
