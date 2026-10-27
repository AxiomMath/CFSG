module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3Cent
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentConfig
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentTransport
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3TwoLocal
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.Foundations.QuasisimpleMulEquiv
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

local notation "pmk" => Matrix.ProjGenLinGroup.mk


theorem exists_centConfig_of_kfact {X : Type} [Group X] [Finite X] {D E : Subgroup X} {p f : ℕ}
    [Fact p.Prime] (hf : 1 ≤ f) (hD : Sec4.IsoLThreePi ↥D p f) (hq2 : 2 < p ^ f)
    (hED : E ≤ Subgroup.normalizer (D : Set X)) (hEc : IsMulCommutative ↥E)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE27 : Nat.card E = 27)
    (ha : ∃ a ∈ E, a ≠ 1 ∧ a ∈ Subgroup.centralizer (D : Set X)) {e : X} (heED : e ∈ E ⊓ D)
    (he1 : e ≠ 1)
    (heE : E ⊓ D ≤ Subgroup.zpowers e)
    (hF3 : ∀ w ∈ Subgroup.centralizer (E : Set X), w ^ 3 = 1 → w ∈ E)
    (hV : ∀ V : Subgroup X, V ≤ D → ¬ 3 ∣ Nat.card V → E ≤ Subgroup.normalizer (V : Set X) →
      ⁅V, E⁆ = ⊥) :
    ∃ (π : Bool) (K : Type) (_ : Field K) (_ : CharP K p), PiField π p f K ∧
      ModThree π (p ^ f) ∧ ∃ (α : ↥E → MulAut (projImage (slPi π 3 (p ^ f) K)))
        (e₀ : projImage (slPi π 3 (p ^ f) K)), CentConfig π p f K α e₀ ∧ e₀ ≠ 1 ∧
        e₀ ^ 3 = 1 ∧ Nat.card (Subgroup.closure (Set.range α)) ∣ 9 ∧
        ((∃ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 ∧
            (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ)) ∨
          (∃ ε : Kˣ, (ε : K) ^ 3 = 1 ∧ ε ≠ 1 ∧
            (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagE ε) ∧ ModNine π (p ^ f))) := by
  have heE' : e ∈ E := (Subgroup.mem_inf.mp heED).1
  have heD : e ∈ D := (Subgroup.mem_inf.mp heED).2
  obtain ⟨π, K, _, hchar, hK, hq, ⟨φ⟩⟩ := exists_projImage_model hf hD
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hperf := Sec13.isPerfect_projImage_slPi hK hq2
  haveI hsimp := Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  have hMq : CFSG.IsQuasisimple (projImage (slPi π 3 (p ^ f) K)) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      (Sec8.Item8KFacts2Proof.exists_ne_comm_of_isPerfect hperf)).1
  have hθ := aschbacherSolvableCore_eq_bot_proj hK hq (CFSG.IsQuasisimple.of_mulEquiv φ hMq) φ
  have hφe1 : φ ⟨e, heD⟩ ≠ 1 := fun h => he1 (by
    have := congrArg Subtype.val (φ.injective (h.trans (map_one φ).symm))
    exact this)
  have hφe3 : φ ⟨e, heD⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨e, heD⟩ : ↥D) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hE3 e heE')
    rw [this, map_one]
  obtain ⟨s, hs, hse⟩ := (φ ⟨e, heD⟩).2
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hsH : s ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hs
  have hsZ : s ∉ zPi π 3 (p ^ f) K := fun h => hφe1 (Subtype.ext (by
    rw [← hse, mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h)]
    rfl))
  have hs3 : s ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    refine Subgroup.mem_inf.mpr ⟨pow_mem hsH 3, ?_⟩
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hse]
    exact congrArg Subtype.val hφe3
  have hnf := (rank3II_4_10_two hK hq hτ hτ1 hsH hsZ hs3).mp ⟨s, hs, fun _ _ => rfl⟩
  obtain ⟨g, hg, hd⟩ : ∃ g ∈ glPi π 3 (p ^ f) K,
      (pmk (g⁻¹ * s * g) = pmk (diagTau hτ)) ∨
      (∃ ε : Kˣ, (ε : K) ^ 3 = 1 ∧ ε ≠ 1 ∧ pmk (g⁻¹ * s * g) = pmk (diagE ε) ∧
        ModNine π (p ^ f)) := by
    have hmk : ∀ (g z : GL (Fin 3) K), z ∈ zPi π 3 (p ^ f) K →
        pmk (g⁻¹ * (s * z) * g) = pmk (g⁻¹ * s * g) := by
      intro g z hz
      rw [map_mul, map_mul, map_mul, map_mul, map_mul,
        mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz),
        mul_one]
    rcases hnf with ⟨y, ⟨z, hz, rfl⟩, g, hg, hgy⟩ | ⟨⟨y, ⟨z, hz, rfl⟩, g, hg, ε, hε, hgy⟩, h9⟩
    · exact ⟨g, hg, Or.inl (by rw [← hmk g z hz, hgy])⟩
    · have hε3 : (ε : K) ^ 3 = 1 := by
        rcases hε with h | h <;> rw [h]
        · exact hτ
        · rw [← pow_mul, pow_mul', hτ, one_pow]
      have hε1 : ε ≠ 1 := by
        rintro rfl
        rw [Units.val_one] at hε
        rcases hε with h | h
        · exact hτ1 h.symm
        · apply hτ1
          calc τ = τ ^ 3 / τ ^ 2 := by
                have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
                field_simp
            _ = 1 := by rw [hτ, ← h, div_one]
      exact ⟨g, hg, Or.inr ⟨ε, hε3, hε1, by rw [← hmk g z hz, hgy], h9⟩⟩
  set φ' := φ.trans (conjModel hπ hg) with hφ'
  set e₀ := φ' ⟨e, heD⟩ with he₀
  have he₀c : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (g⁻¹ * s * g) := by
    rw [he₀, hφ', MulEquiv.trans_apply, coe_conjModel, ← hse]
    simp only [map_mul, map_inv, inv_inv]
  have he₀1 : e₀ ≠ 1 := fun h => hφe1 ((conjModel hπ hg).injective (h.trans (map_one _).symm))
  have he₀3 : e₀ ^ 3 = 1 := by
    rw [he₀, hφ', MulEquiv.trans_apply, ← map_pow, hφe3, map_one]
  set α : ↥E → MulAut (projImage (slPi π 3 (p ^ f) K)) :=
    fun x => slAct φ' ⟨(x : X), hED x.2⟩ with hα
  have hx3 : ∀ x : ↥E, (⟨(x : X), hED x.2⟩ : Subgroup.normalizer (D : Set X)) ^ 3 = 1 :=
    fun x => Subtype.ext (by rw [Subgroup.coe_pow]; exact hE3 x x.2)
  have hc : CentConfig π p f K α e₀ := by
    refine ⟨fun x => ?_, fun x => ?_, fun x y => ?_, ?_, ?_, ?_, fun x => ?_⟩
    · exact slAct_apply_self_of_commute φ' heD _
        (congrArg Subtype.val (hEc.is_comm.comm x ⟨e, heE'⟩))
    · rw [hα, ← map_pow, hx3, map_one]
    · rw [hα, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (show (x : X) * y = y * x from
        congrArg Subtype.val (hEc.is_comm.comm x y))
    · exact ⟨⟨e, heE'⟩, slAct_of_mem φ' heD _⟩
    · intro W hW3 hWinv x w hw
      exact slAct_eq_self_of_hV φ' hED hV W hW3 (fun y hy => hWinv ⟨y, hy⟩) x x.2 w hw
    · intro u hu3 hfix
      exact mem_zpowers_of_slAct_fixed φ' hED hF3 heD heE u hu3 fun y hy => hfix ⟨y, hy⟩
    · rcases pslAct_pgl_or_field hK hq2 hθ φ' ⟨(x : X), hED x.2⟩ (hx3 x) with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
  have hcard : Nat.card (Subgroup.closure (Set.range α)) ∣ 9 := by
    set ψ : ↥E →* MulAut (projImage (slPi π 3 (p ^ f) K)) :=
      (slAct φ').comp (Subgroup.inclusion hED) with hψ
    have hαψ : Set.range α = Set.range ψ := rfl
    rw [hαψ, ← MonoidHom.coe_range, Subgroup.closure_eq]
    obtain ⟨a, haE, ha1, haC⟩ := ha
    have haker : (⟨a, haE⟩ : ↥E) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      ext m
      change ((φ' (⟨a * (φ'.symm m : X) * a⁻¹, _⟩ : ↥D)) : ProjGenLinGroup (Fin 3) K) = m
      have : (⟨a * (φ'.symm m : X) * a⁻¹, by
          exact (D.normalizerMonoidHom ⟨a, hED haE⟩ (φ'.symm m)).2⟩ : ↥D) = φ'.symm m := by
        apply Subtype.ext
        change a * (φ'.symm m : X) * a⁻¹ = φ'.symm m
        rw [(Subgroup.mem_centralizer_iff.mp haC _ (φ'.symm m).2).symm, mul_inv_cancel_right]
      rw [this, MulEquiv.apply_symm_apply]
    have hker1 : Nat.card ψ.ker ≠ 1 := by
      intro h1
      have hbot : ψ.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      have := (Subgroup.mem_bot.mp (hbot ▸ haker))
      exact ha1 (congrArg Subtype.val this)
    have hmul : Nat.card ψ.range * Nat.card ψ.ker = 27 := by
      rw [← hE27, Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    have hker0 : Nat.card ψ.ker ≠ 0 := Nat.card_pos.ne'
    have hdvd : Nat.card ψ.range ∣ 3 ^ 3 := Dvd.intro _ hmul
    obtain ⟨k, hk, hkR⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hkR]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exfalso
      rw [hkR] at hmul
      have : Nat.card ψ.ker = 1 := by omega
      exact hker1 this
  refine ⟨π, K, inferInstance, hchar, hK, hq, α, e₀, hc, he₀1, he₀3, hcard, ?_⟩
  rcases hd with hd | ⟨ε, hε3, hε1, hd, h9⟩
  · exact Or.inl ⟨τ, hτ, hτ1, he₀c.trans hd⟩
  · exact Or.inr ⟨ε, hε3, hε1, he₀c.trans hd, h9⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
