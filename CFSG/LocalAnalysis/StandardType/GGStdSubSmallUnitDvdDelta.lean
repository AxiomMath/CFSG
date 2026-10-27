module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdCore

public section

namespace CFSG.StandardType.SmallU

open scoped commutatorElement

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.StandardType.TableBUE

variable {K : Type} [Field K] [Finite K] {n d p : ℕ}

theorem torus_le_block {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    {S : Finset (Fin d)} {E : Subgroup L'}
    (hdesc : ∀ e ∈ E, ∃ (g : ↥(unitarySU 2 n K d)) (τ : Fin d → Kˣ), φ g = e ∧
      (g : GL (Fin d) K) = diagHom d τ ∧ ∀ k, k ∉ S → τ k = 1) :
    E ≤ (blockSU S).map φ := by
  intro e he
  obtain ⟨g, τ, rfl, hg, hoff⟩ := hdesc e he
  refine ⟨g, ?_, rfl⟩
  change g ∈ blockSU S
  rw [mem_blockSU, hg]
  exact StdSubRestU.isBlockOn_diagHom hoff

theorem conj_injective_torus {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hM : Model φ) (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 5 ≤ d) {k₀ : Fin d} {E : Subgroup L'}
    (hdesc : ∀ e ∈ E, ∃ (g : ↥(unitarySU 2 n K d)) (τ : Fin d → Kˣ), φ g = e ∧
      (g : GL (Fin d) K) = diagHom d τ ∧ τ k₀ = 1) :
    ∀ e ∈ E, MulAut.conj e = 1 → e = 1 := by
  intro e he h1
  obtain ⟨g, τ, rfl, hg, hk₀⟩ := hdesc e he
  have h : ∀ y : ↥(unitarySU 2 n K d), φ (g * y * g⁻¹) = φ y := by
    intro y
    have := congrArg (fun f : MulAut L' => f (φ y)) h1
    simpa [MulAut.conj_apply, map_mul, map_inv] using this
  obtain ⟨c, hc⟩ := scalar_of_map_conj_eq hM hK (by omega) h
  rw [hg, coe_diagHom] at hc
  have hf := Matrix.diagonal_injective hc
  have hc1 : c = 1 := by
    rw [← congrFun hf k₀, hk₀]
    rfl
  have hτ : τ = 1 := funext fun k => Units.ext (by rw [congrFun hf k, hc1]; rfl)
  have hg1 : g = 1 := by
    apply Subtype.ext
    rw [hg, hτ, map_one]
    rfl
  rw [hg1, map_one]


theorem ggStdSubTwoTorusDeltaSmall_unitDvd
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ p = 3)) :
    GGStdSubTwoTorusDeltaSmall p (d - 3) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hδ a ha ha1 hEcomp hcentA hsmall
  exfalso
  obtain ⟨φ, hM, hdiag⟩ := exists_model hK hn hd hp hpq hpd hnd hψ hker hperf hA hAI hr h3
  have hpK := dvd_card_sub_one hK hpq
  have hd3 : 3 ≤ d := by omega
  have hAp : ∀ g ∈ A, g ^ p = 1 := hA.2
  obtain ⟨t₀, ht₀⟩ := hdiag a ha
  obtain ⟨σ, -, hσ⟩ := ActsU.of_actsDiagU ht₀
  obtain ⟨i₀, hbig'⟩ := exists_bigOK_cls hM (by omega) hn hσ hEcomp
  have hS := cls_isCls σ i₀
  have hi₀S : i₀ ∈ cls σ i₀ := mem_cls.mpr rfl
  set S := cls σ i₀ with hSdef
  have hSd : ∃ k₀, k₀ ∉ S := by
    by_contra hall
    push Not at hall
    exact ha1 (hσ.eq_one_of_const hM i₀ fun i j => by
      rw [mem_cls.mp (hall i), mem_cls.mp (hall j)])
  obtain ⟨k₀, hk₀⟩ := hSd
  have hlayer : LargeEvenLayer (ggFix a) = (blockSU S).map φ :=
    layer_eq_block hM hσ hS (isQuasisimple_block hM hbig') hEcomp
  have hcardA := card_A_le_of_class (T := {i₀}) hM hd3 hp hpK hA hdiag ha hσ hS hbig' hEcomp
    hcentA (s₀ := i₀) (Finset.singleton_subset_iff.mpr hi₀S)
    (fun a' _ τ _ k hk => by rw [Finset.mem_singleton.mp hk])
  rw [Finset.card_singleton] at hcardA
  obtain ⟨E, hEcard, hEdesc⟩ := exists_torus hM hK hp hpq hk₀ id (fun k hk => hk)
  rw [Finset.image_id] at hEcard
  have hEab : CFSG.Open.IsElemAbelian p E := isElemAbelian_torus fun e he => by
    obtain ⟨g, τ, h1, h2, h3, -⟩ := hEdesc e he
    exact ⟨g, τ, h1, h2, h3⟩
  have hElayer : E ≤ LargeEvenLayer (ggFix a) := by
    rw [hlayer]
    exact torus_le_block fun e he => by
      obtain ⟨g, τ, h1, h2, -, h4, -⟩ := hEdesc e he
      exact ⟨g, τ, h1, h2, h4⟩
  have hEfix : ∀ a' ∈ A, ∀ e ∈ E, a' e = e := by
    intro a' ha'
    obtain ⟨t', ht'⟩ := hdiag a' ha'
    obtain ⟨σ', -, hσ'⟩ := ActsU.of_actsDiagU ht'
    exact fix_of_torus hσ' fun e he => by
      obtain ⟨g, τ, h1, h2, -⟩ := hEdesc e he
      exact ⟨g, τ, h1, h2⟩
  have hEconj : ∀ e ∈ E, MulAut.conj e ∈ A := fun e he =>
    hδ.1 e (hEab.2 e he) (fun a' ha' => hEfix a' ha' e he)
  have hEsmall : Nat.card E < p ^ 3 := hsmall E hEab hElayer hEfix (Or.inl hEconj)
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨i₀, hi₀S⟩
  have hSle : S.card ≤ 3 := by
    by_contra hc
    push Not at hc
    have := Nat.pow_le_pow_right hp.pos (show 3 ≤ S.card - 1 by omega)
    omega
  have hA3 : Nat.card A = p ^ 3 := by
    refine le_antisymm ?_ h3
    calc Nat.card A ≤ p * p ^ (S.card - 1) := hcardA
      _ ≤ p * p ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.pos (by omega))
      _ = p ^ 3 := by ring
  obtain ⟨E2, hE2card, hE2desc⟩ := exists_torus hM hK hp hpq (S := Finset.univ.erase i₀)
    (k₀ := i₀) (by simp) id (fun k hk => hk)
  rw [Finset.image_id, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
    Fintype.card_fin] at hE2card
  have hE2ab : CFSG.Open.IsElemAbelian p E2 := isElemAbelian_torus fun e he => by
    obtain ⟨g, τ, h1, h2, h3, -⟩ := hE2desc e he
    exact ⟨g, τ, h1, h2, h3⟩
  have hE2fix : ∀ a' ∈ A, ∀ e ∈ E2, a' e = e := by
    intro a' ha'
    obtain ⟨t', ht'⟩ := hdiag a' ha'
    obtain ⟨σ', -, hσ'⟩ := ActsU.of_actsDiagU ht'
    exact fix_of_torus hσ' fun e he => by
      obtain ⟨g, τ, h1, h2, -⟩ := hE2desc e he
      exact ⟨g, τ, h1, h2⟩
  have hE2conj : ∀ e ∈ E2, MulAut.conj e ∈ A := fun e he =>
    hδ.1 e (hE2ab.2 e he) (fun a' ha' => hE2fix a' ha' e he)
  let ι : E2 →* MulAut L' := (MulAut.conj : L' →* MulAut L').comp E2.subtype
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    refine conj_injective_torus hM hK hd (k₀ := i₀) (E := E2) (fun e he => ?_) x.1 x.2 hx
    obtain ⟨g, τ, h1, h2, -, h4, -⟩ := hE2desc e he
    exact ⟨g, τ, h1, h2, h4 i₀ (by simp)⟩
  have hιle : ι.range ≤ A := by
    rintro _ ⟨x, rfl⟩
    exact hE2conj x.1 x.2
  have hιcard : Nat.card A ≤ Nat.card ι.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv, hA3]
    refine le_trans (Nat.pow_le_pow_right hp.pos (by omega)) hE2card
  have hιeq : ι.range = A := Subgroup.eq_of_le_of_card_ge hιle hιcard
  have hAll : ∀ g ∈ A, ∃ l : L', MulAut.conj l = g ∧ l ^ p = 1 := by
    intro g hg
    rw [← hιeq] at hg
    obtain ⟨x, rfl⟩ := hg
    exact ⟨x.1, rfl, hE2ab.2 x.1 x.2⟩
  rcases hδ.2 with ⟨⟨g, hgA, hgout⟩, -⟩ | ⟨-, -, g, hgA, hg⟩
  · obtain ⟨l, hl, -⟩ := hAll g hgA
    exact hgout ⟨l, hl⟩
  · obtain ⟨l, hl, hlp⟩ := hAll g hgA
    rcases hg with hout | hall
    · exact hout ⟨l, hl⟩
    · have h1 := hall l hl
      rw [hlp, orderOf_one] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

end CFSG.StandardType.SmallU

end
