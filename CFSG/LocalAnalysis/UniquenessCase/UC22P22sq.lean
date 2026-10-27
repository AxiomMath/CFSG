module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sp
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge3
import CFSG.Open.StatedAPI
public import CFSG.Quasithin.Background.B610

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x
open scoped Matrix commutatorElement

namespace P22sq

theorem natL2Prime_one_of {G : Type} [Group G] {L V : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (hLN : L ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G))
    (α : ↥L →* ↥(CFSG.Open.StatedSL 2 F)) (hαk : α.ker = (L ⊓ centralizer (V : Set G)).subgroupOf L)
    (hα3 : Nat.card α.range = 3)
    (β : ↥⁅V, L⁆ →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβk : β.ker = (⁅V, L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅V, L⁆)
    (hβα : ∀ (l : ↥L) (u v : ↥⁅V, L⁆), (v : G) = l * u * l⁻¹ →
      Multiplicative.toAdd (β v) = (((α l : ↥(CFSG.Open.StatedSL 2 F)) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) :
    CFSG.Quasithin.IsNaturalL2Prime 1 L V := by
  classical
  set e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hF).symm with he
  set gm : GL (Fin 2) F →* GL (Fin 2) (ZMod 2) := Matrix.GeneralLinearGroup.map e.toRingHom with hgm
  have hgm_inj : Function.Injective gm := by
    intro x y hxy
    ext i j
    have h := congrArg (fun g : GL (Fin 2) (ZMod 2) => (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j) hxy
    simpa [hgm] using h
  set ι : ↥(CFSG.Open.StatedSL 2 F) →* GL (Fin 2) (ZMod 2) := gm.comp (CFSG.Open.StatedSL 2 F).subtype with hι
  have hι_inj : Function.Injective ι := hgm_inj.comp Subtype.val_injective
  set α₁ : ↥L →* GL (Fin 2) (ZMod 2) := ι.comp α with hα₁
  set Γ : Subgroup (GL (Fin 2) (ZMod 2)) := α₁.range with hΓ
  set ev : (Fin 2 → F) ≃+ (Fin 2 → ZMod 2) := AddEquiv.piCongrRight fun _ => e.toAddEquiv with hev
  set β₁ : ↥⁅V, L⁆ →* Multiplicative (Fin 2 → ZMod 2) :=
    (AddMonoidHom.toMultiplicative ev.toAddMonoidHom).comp β with hβ₁
  refine Or.inr ⟨rfl, Γ, ?_, hLN, α₁.rangeRestrict, α₁.rangeRestrict_surjective, ?_, β₁, ?_, ?_, ?_⟩
  · rw [hΓ, hα₁, MonoidHom.range_comp, Subgroup.card_map_of_injective hι_inj, hα3]
  · rw [MonoidHom.ker_rangeRestrict, hα₁, MonoidHom.ker_comp_of_injective α ι hι_inj, hαk]
  · intro y
    obtain ⟨x, hx⟩ := hβ (Multiplicative.ofAdd (ev.symm (Multiplicative.toAdd y)))
    refine ⟨x, ?_⟩
    simp [hβ₁, hx]
  · rw [hβ₁, MonoidHom.ker_comp_of_injective β _ ?_, hβk]
    intro a b hab
    have := congrArg (fun w => ev.symm (Multiplicative.toAdd w)) hab
    simpa using this
  · intro l u v huv
    have h := hβα l u v huv
    funext i
    have h' := congrArg (fun w => e (w i)) h
    simp only [hβ₁, MonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.toMultiplicative_apply_apply,
      toAdd_ofAdd]
    rw [show (ev.toAddMonoidHom (Multiplicative.toAdd (β v))) i = e (Multiplicative.toAdd (β v) i) from rfl, h']
    exact RingHom.map_mulVec e.toRingHom _ _ i

theorem eq_zero_of_mulVec_eq_self {F : Type} [Field F] [CharP F 2] {g : ↥(CFSG.Open.StatedSL 2 F)}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) {v : Fin 2 → F}
    (hv : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) : v = 0 := by
  set M : Matrix (Fin 2) (Fin 2) F := ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet : M.det = 1 := CFSG.Open.StatedAPI.det_of_mem_statedSL g.2
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hCH : M * M = (M 0 0 + M 1 1) • M - 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-1 : F) * hdet
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-1 : F) * hdet
  have hMv : (M * M) *ᵥ v = v := by rw [← Matrix.mulVec_mulVec, hv, hv]
  rw [hCH, Matrix.sub_mulVec, Matrix.smul_mulVec, hv, Matrix.one_mulVec] at hMv
  have ht : (M 0 0 + M 1 1) • v = 0 := by
    have h3 : (M 0 0 + M 1 1) • v = v + v := sub_eq_iff_eq_add.mp hMv
    rw [h3, ← two_smul F v, h2, zero_smul]
  by_contra hv0
  have ht0 : M 0 0 + M 1 1 = 0 := by
    by_contra hne
    apply hv0
    have h4 := congrArg (fun w => (M 0 0 + M 1 1)⁻¹ • w) ht
    simpa [smul_smul, inv_mul_cancel₀ hne] using h4
  rw [ht0, zero_smul, zero_sub] at hCH
  have hneg : (-1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
    ext i j
    simp [CharTwo.neg_eq]
  have hg2 : g ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [pow_two]
    show ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [← hM, hCH, hneg]
  apply hg1
  calc g = g ^ 3 * (g ^ 2)⁻¹ := by group
    _ = 1 := by rw [hg3, hg2]; group

theorem exists_mulVec_sub_eq {F : Type} [Field F] [Finite F] [CharP F 2] {g : ↥(CFSG.Open.StatedSL 2 F)}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (y : Fin 2 → F) :
    ∃ u : Fin 2 → F, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ u - u = y := by
  set M : Matrix (Fin 2) (Fin 2) F := ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hM
  have hinj : Function.Injective fun u : Fin 2 → F => M *ᵥ u - u := by
    intro u u' h
    have h1 : M *ᵥ (u - u') = u - u' := by
      rw [Matrix.mulVec_sub]
      have h' : M *ᵥ u - u = M *ᵥ u' - u' := h
      rw [sub_eq_sub_iff_sub_eq_sub] at h'
      rw [h']
    exact sub_eq_zero.1 (eq_zero_of_mulVec_eq_self hg3 hg1 h1)
  exact Finite.injective_iff_surjective.1 hinj y

variable {G : Type} [Group G] [Finite G]

end P22sq

open P22sq

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.UniquenessCase.UC22
