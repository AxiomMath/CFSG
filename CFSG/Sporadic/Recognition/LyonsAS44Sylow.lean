module

public import CFSG.Sporadic.Recognition.LyonsAS44Pts
public import CFSG.Sporadic.Recognition.LyonsAS44SylowGen

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.McLAS CFSG.Quasithin

section Gen

variable {G : Type*} [Group G]

omit [Group G] in
theorem mem_normalizer_zpowers_iff' {G : Type*} [Group G] {a g : G} :
    g ∈ normalizer (zpowers a : Set G) ↔ zpowers (g * a * g⁻¹) = zpowers a := by
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  rfl

theorem conj_mem_normalizer_zpowers {x w c g : G} (hw : c * x * c⁻¹ = w)
    (hg : g ∈ normalizer (zpowers w : Set G)) :
    c⁻¹ * g * c ∈ normalizer (zpowers x : Set G) := by
  rw [mem_normalizer_zpowers_iff'] at hg ⊢
  have h1 : c⁻¹ * g * c * x * (c⁻¹ * g * c)⁻¹ = c⁻¹ * (g * w * g⁻¹) * c := by
    rw [← hw]; group
  rw [h1]
  have h2 := congrArg (Subgroup.map (MulAut.conj c⁻¹).toMonoidHom) hg
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
  have h3 : (MulAut.conj c⁻¹).toMonoidHom w = x := by
    rw [← hw]
    show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x
    group
  rw [h3] at h2
  simpa [MulAut.conj_apply] using h2

theorem card_dvd_normalizer_of_conj {x w c : G} (hw : c * x * c⁻¹ = w) {Q : Subgroup G}
    (hQ : Q ≤ normalizer (zpowers w : Set G)) :
    Nat.card Q ∣ Nat.card ↥(normalizer (zpowers x : Set G)) := by
  have hle : Q.map (MulAut.conj c⁻¹).toMonoidHom ≤ normalizer (zpowers x : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    have := conj_mem_normalizer_zpowers hw (hQ hq)
    simpa [MulAut.conj_apply] using this
  have h1 := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective] at h1

end Gen

section Sylow

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
  {R T A : Subgroup (CentQuot (x₁ : G))} {Y : Fin 10 → CentQuot (x₁ : G)}

namespace LyData

variable (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (F : LyAFacts D S R T A Y)

include D S F

theorem card_TG_eq : Nat.card ↥(preimQ (x₁ : G) T) = 3 ^ (Nat.card G).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard := D.card_TG S F
  have hMhat : Nat.card ↥(NormX (x₁ : G)) = 2 * (2 ^ 7 * 3 ^ 7 * 5 ^ 3 * 7 * 11) := by
    rw [D.card_normX S.pow₁ S.rho₁, F.card_M]
  refine card_eq_pow_factorization_of_fixed_point (p := 3)
    (IsPGroup.of_card (n := 7) hcard) (deltaIn (x₁ : G) (preimQ (x₁ : G) T)) ?_ ?_ ?_
  · rw [D.deltaIn_TG_eq S F, D.ncard_deltaIn_AG S F]
    norm_num
  · intro g hg B hB
    obtain ⟨w, hwc, hwT, rfl⟩ := mem_deltaIn_iff.1 hB
    refine mem_deltaIn_iff.2 ⟨g * w * g⁻¹, ?_, ?_, ?_⟩
    · exact hwc.trans (isConj_iff.2 ⟨g, rfl⟩)
    · exact (mem_normalizer_iff.1 hg w).1 hwT
    · rw [MonoidHom.map_zpowers]; rfl
  · intro B hB Q hQ hQB
    obtain ⟨w, hwc, hwT, rfl⟩ := mem_deltaIn_iff.1 hB
    obtain ⟨c, hc⟩ := isConj_iff.1 hwc
    have hdvd := card_dvd_normalizer_of_conj hc hQB
    obtain ⟨a, ha⟩ := hQ.exists_card_eq
    have hN : Nat.card ↥(normalizer (zpowers (x₁ : G) : Set G)) =
        2 * (2 ^ 7 * 3 ^ 7 * 5 ^ 3 * 7 * 11) := hMhat
    rw [hN, ha] at hdvd
    rw [ha, hcard]
    by_contra hlt
    have ha7 : 7 < a := by
      by_contra h
      exact hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h8 : 3 ^ 8 ∣ 3 ^ a := pow_dvd_pow 3 (by omega)
    have := h8.trans hdvd
    norm_num at this

noncomputable def sylowTG : Sylow 3 G :=
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  Sylow.ofCard (preimQ (x₁ : G) T) (D.card_TG_eq S F)

theorem coe_sylowTG : (D.sylowTG S F : Subgroup G) = preimQ (x₁ : G) T := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact Sylow.coe_ofCard (preimQ (x₁ : G) T) (D.card_TG_eq S F)

theorem isWeaklyClosedIn_AG :
    IsWeaklyClosedIn (preimQ (x₁ : G) A) (preimQ (x₁ : G) T) := by
  intro g hg
  have hmain : ∀ a ∈ preimQ (x₁ : G) A, g⁻¹ * a * g ∈ preimQ (x₁ : G) A := by
    intro a ha
    have ha' : a ∈ closure {w : G | w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w} :=
      (D.AG_eq_closure S F).le ha
    clear ha
    induction ha' using Subgroup.closure_induction with
    | mem w hw =>
      have h1 : g⁻¹ * w * g ∈ conjSubgroup (preimQ (x₁ : G) A) g := by
        rw [mem_conjSubgroup_iff]
        have : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
        rw [this]; exact hw.1
      refine D.mem_AG_of_mem_TG S F (hg h1) ?_
      exact hw.2.trans (isConj_iff.2 ⟨g⁻¹, by simp⟩)
    | one => simp
    | mul a b ha hb iha ihb =>
      have : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
      rw [this]; exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
      have : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ iha
  have hle : conjSubgroup (preimQ (x₁ : G) A) g ≤ preimQ (x₁ : G) A := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have := hmain _ hy
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at this
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

theorem exists_mem_normalizer_of_isConj {w₁ w₂ : G} (h₁ : w₁ ∈ preimQ (x₁ : G) A)
    (h₂ : w₂ ∈ preimQ (x₁ : G) A) (hc : IsConj w₁ w₂) :
    ∃ k ∈ normalizer (preimQ (x₁ : G) A : Set G), k * w₁ * k⁻¹ = w₂ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  have hcentr : ∀ w ∈ preimQ (x₁ : G) A,
      w ∈ centralizer ((preimQ (x₁ : G) A : Subgroup G) : Set G) := fun w hw => by
    rw [mem_centralizer_iff]
    intro a ha
    exact D.AG_comm S F a ha w hw
  have hT : (preimQ (x₁ : G) A) ≤ (D.sylowTG S F : Subgroup G) := by
    rw [D.coe_sylowTG S F]; exact preimQ_mono F.mcl.A_le_T
  have hW : IsWeaklyClosedIn (preimQ (x₁ : G) A) (D.sylowTG S F : Subgroup G) := by
    rw [D.coe_sylowTG S F]; exact D.isWeaklyClosedIn_AG S F
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨n, hn, hnx⟩ := burnside_fusion_lemma_centralizer (D.sylowTG S F) hT hW
    (hcentr w₁ h₁) (hcentr w₂ h₂) (g := c⁻¹) (by simpa using hc)
  exact ⟨n⁻¹, Subgroup.inv_mem _ hn, by simpa using hnx⟩

end LyData

end Sylow

end CFSG.Sporadic.Recognition.LyonsSims
