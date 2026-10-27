module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsI
import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSUElt
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsH
import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfField

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits CFSG.LocalAnalysis.WeakClosure81

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

private theorem exists_conj_suProjTv_eq (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {e : Fin m → F} (he0 : e ≠ 0) (he : herm (unitaryInvolution F 2 n) e e = 0) {c : F}
    (hcσ : unitaryInvolution F 2 n c = c) (hc0 : c ≠ 0) :
    ∃ g : StatedProj (StatedSU m (2 ^ n) F),
      g * kFactsSuProjTv hF m e 1 * g⁻¹ = kFactsSuProjTv hF m e c := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have h1 : (1 : F) + unitaryInvolution F 2 n 1 = 0 := by
    rw [map_one]; exact CharTwo.add_self_eq_zero 1
  obtain ⟨f, hf, hef⟩ := exists_partner hσ he0 he
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [hl, mul_zero])
  have hσl : unitaryInvolution F 2 n l = l := by
    apply CharTwo.sq_injective
    change (unitaryInvolution F 2 n l) ^ 2 = l ^ 2
    rw [pow_two, pow_two, ← map_mul, ← hl, hcσ]
  refine ⟨kFactsSuProj hF m (suConfY hσ e f l), ?_⟩
  rw [kFacts_suProj_conj_suProjTv hF (suConfY hσ e f l) he h1,
    (suConfY_apply (hσ := hσ) he hf hef hσl hl0).1, kFacts_suProjTv_smul_vec hF he h1 l, hσl,
    ← hl, mul_one]

private theorem meetsSq_of_suProjTv {G : Type} [Group G] {D : Set G}
    (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g}) {s : G} (hs : s ∈ D) {m : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) {e : Fin m → F} (he0 : e ≠ 0)
    (he : herm (unitaryInvolution F 2 n) e e = 0) (ψ : G →* StatedProj (StatedSU m (2 ^ n) F))
    (hψinj : Function.Injective ψ) (hψsurj : Function.Surjective ψ)
    (hψs : ψ s = kFactsSuProjTv hF m e 1) {s₀ : F} (hs₀σ : unitaryInvolution F 2 n s₀ = s₀)
    (hs₀0 : s₀ ≠ 0) (hs₀1 : s₀ ≠ 1) :
    ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have htr : ∀ c : F, unitaryInvolution F 2 n c = c → c + unitaryInvolution F 2 n c = 0 :=
    fun c hc => by rw [hc]; exact CharTwo.add_self_eq_zero c
  have h1σ : unitaryInvolution F 2 n 1 = 1 := map_one _
  have hconj : ∀ c : F, unitaryInvolution F 2 n c = c → c ≠ 0 →
      ∃ v ∈ D, ψ v = kFactsSuProjTv hF m e c := by
    intro c hc hc0
    obtain ⟨g, hg⟩ := exists_conj_suProjTv_eq hF he0 he hc hc0
    obtain ⟨x, rfl⟩ := hψsurj g
    obtain ⟨d₀, rfl⟩ := hcls
    exact ⟨x * s * x⁻¹, hs.trans (isConj_iff.mpr ⟨x, rfl⟩), by simp [hψs, hg]⟩
  have hmul : ∀ a b : F, unitaryInvolution F 2 n a = a → unitaryInvolution F 2 n b = b →
      kFactsSuProjTv hF m e a * kFactsSuProjTv hF m e b = kFactsSuProjTv hF m e (a + b) := by
    intro a b ha hb
    unfold kFactsSuProjTv
    rw [← map_mul, suTv_mul_suTv hσ he (htr a ha) (htr b hb)]
  have hsum : unitaryInvolution F 2 n (1 + s₀) = 1 + s₀ := by rw [map_add, h1σ, hs₀σ]
  have hsum0 : (1 : F) + s₀ ≠ 0 := fun h =>
    hs₀1 (by rw [← CharTwo.neg_eq (1 : F)]; linear_combination h)
  obtain ⟨v, hvD, hvψ⟩ := hconj s₀ hs₀σ hs₀0
  obtain ⟨w, hwD, hwψ⟩ := hconj (1 + s₀) hsum hsum0
  refine ⟨s, hs, v, hvD, fun h => hs₀1 ?_, hψinj ?_, ?_⟩
  · have h' := congrArg ψ h
    rw [hψs, hvψ] at h'
    exact (kFacts_suProjTv_injective hF he0 he (htr 1 h1σ) (htr s₀ hs₀σ) h').symm
  · rw [map_mul, map_mul, hψs, hvψ, hmul 1 s₀ h1σ hs₀σ, hmul s₀ 1 hs₀σ h1σ, add_comm]
  · have hsv : s * v = w := hψinj (by rw [map_mul, hψs, hvψ, hmul 1 s₀ h1σ hs₀σ, hwψ])
    exact hsv ▸ hwD

theorem meetsSq_of_isUnitaryTransvection {G : Type} [Group G] {D : Set G}
    (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hZ : Subgroup.center G = ⊥) {s : G} (hs : s ∈ D)
    {m f : ℕ} (hf : 2 ≤ f)
    (hut : CFSG.LocalAnalysis.WeakClosure81.SevenK.IsUnitaryTransvection G m f s) :
    ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D := by
  obtain ⟨F, hFfield, hFfinite, hcard, e, hvt⟩ := hut
  let : Field F := hFfield
  let : Finite F := hFfinite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_sq (p := 2) (f := f) hcard
  let ψ : G →* StatedProj (StatedSU m (2 ^ f) F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hψinj : Function.Injective ψ := by
    intro a b hab
    obtain ⟨z, hz, hzb⟩ := (QuotientGroup.mk'_eq_mk' _).1 (e.injective hab)
    rw [hZ, Subgroup.mem_bot] at hz
    rwa [hz, mul_one] at hzb
  obtain ⟨e₀, he₀0, he₀, hψs⟩ := kFacts_su_exists_centre hcard hvt
  obtain ⟨s₀, hs₀σ, hs₀0, hs₀1, -⟩ := exists_zech_unitary hcard (lt_of_lt_of_le one_lt_two hf)
  exact meetsSq_of_suProjTv hcls hs hcard he₀0 he₀ ψ hψinj
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hψs hs₀σ hs₀0 hs₀1

end CFSG.OddTranspositions.PartFour

end
