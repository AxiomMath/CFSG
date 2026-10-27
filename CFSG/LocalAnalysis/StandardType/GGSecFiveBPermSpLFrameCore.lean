module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import CFSG.LocalAnalysis.StandardType.GGStdPosACore
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJFrame
import CFSG.LocalAnalysis.StandardType.GGTypeAFarActsVec
import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagLin
import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
import CFSG.LocalAnalysis.StandardType.GGLinearFusionFrame
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGSixLinearModelOmega
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameAlign
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameSplit
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPerm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear Matrix

namespace LFrameCore

private theorem lfc_exists_perm_of_mem_aPermutationFull {n p : ℕ}
    {a : MulAut (Fin n → Multiplicative (ZMod p))} (ha : a ∈ aPermutationFull n p) :
    ∃ τ : Equiv.Perm (Fin n), a = SpCoord.permAut τ := by
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨i, j, -, rfl⟩ := ha
    exact ⟨Equiv.swap i j, rfl⟩
  | one => exact ⟨1, by ext f k; rfl⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨σ, rfl⟩ := iha
    obtain ⟨τ, rfl⟩ := ihb
    exact ⟨σ * τ, by ext f k; rfl⟩
  | inv a _ iha =>
    obtain ⟨σ, rfl⟩ := iha
    exact ⟨σ⁻¹, by ext f k; rfl⟩

private theorem lfc_ggAutomizer_fix {G : Type} [Group G] {Bs X : Subgroup G} {a : MulAut ↥Bs}
    (ha : a ∈ ggAutomizer X Bs) (c : ↥Bs) (hc : (c : G) ∈ Subgroup.centralizer (X : Set G)) :
    a c = c := by
  have hle : ggAutomizer X Bs ≤ MulAction.stabilizer (MulAut ↥Bs) c := by
    refine (Subgroup.closure_le _).2 ?_
    rintro a ⟨g, hgX, -, hg⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
    apply Subtype.ext
    rw [hg c, Subgroup.mem_centralizer_iff.mp hc g hgX, mul_inv_cancel_right]
  exact MulAction.mem_stabilizer_iff.mp (hle ha)

private theorem lfc_eta_const {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (c : ↥Bs) (hc : (c : G) ∈ Subgroup.centralizer (X : Set G)) (k k' : Fin n) :
    eta c k = eta c k' := by
  by_cases hkk : k = k'
  · rw [hkk]
  have hmem : SpCoord.permAut (p := p) (Equiv.swap k k') ∈ aPermutationFull n p :=
    Subgroup.subset_closure ⟨k, k', hkk, rfl⟩
  rw [← hA] at hmem
  obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hmem
  have h1 : (MulAut.congr eta a) (eta c) = eta c := by
    change eta (a (eta.symm (eta c))) = eta c
    rw [MulEquiv.symm_apply_apply, lfc_ggAutomizer_fix ha c hc]
  have h3 : SpCoord.permAut (p := p) (Equiv.swap k k') (eta c) = eta c := by
    have h4 := congrArg (fun φ : MulAut _ => φ (eta c)) hae
    rw [← h4]
    exact h1
  have h2 := congrFun h3 k
  rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.Perm.inv_def, Equiv.symm_swap,
    Equiv.swap_apply_left] at h2
  exact h2.symm

section Log

variable {F : Type} [Field F] {p : ℕ} [NeZero p] {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ p)

private noncomputable def lfcExp (a : ZMod p) : Fˣ :=
  ((Additive.toMul (hζ.zmodEquivZPowers a) : Subgroup.zpowers ζ) : Fˣ)

private noncomputable def lfcLog (z : Fˣ) : ZMod p :=
  if hz : z ∈ Subgroup.zpowers ζ then hζ.zmodEquivZPowers.symm (Additive.ofMul ⟨z, hz⟩) else 0

include hζ in
private theorem lfc_mem_zpowers {z : Fˣ} (hz : z ^ p = 1) : z ∈ Subgroup.zpowers ζ := by
  rw [hζ.zpowers_eq]
  exact (mem_rootsOfUnity p z).mpr hz

omit [NeZero p] in
private theorem lfcExp_add (a b : ZMod p) : lfcExp hζ (a + b) = lfcExp hζ a * lfcExp hζ b := by
  unfold lfcExp
  rw [map_add, toMul_add, Subgroup.coe_mul]

omit [NeZero p] in
private theorem lfcExp_zero : lfcExp hζ 0 = 1 := by
  unfold lfcExp
  rw [map_zero]
  rfl

private theorem lfcExp_pow (a : ZMod p) : lfcExp hζ a ^ p = 1 := by
  have h : lfcExp hζ a ∈ rootsOfUnity p F := by
    rw [← hζ.zpowers_eq]
    exact (Additive.toMul (hζ.zmodEquivZPowers a)).2
  exact (mem_rootsOfUnity p _).mp h

omit [NeZero p] in
private theorem lfcExp_injective : Function.Injective (lfcExp hζ) := by
  intro a b h
  apply hζ.zmodEquivZPowers.injective
  apply Additive.toMul.injective
  exact Subtype.ext h

private theorem lfcExp_lfcLog {z : Fˣ} (hz : z ^ p = 1) : lfcExp hζ (lfcLog hζ z) = z := by
  have hm := lfc_mem_zpowers hζ hz
  unfold lfcLog
  rw [dif_pos hm]
  unfold lfcExp
  rw [AddEquiv.apply_symm_apply]
  rfl

private theorem lfcLog_lfcExp (a : ZMod p) : lfcLog hζ (lfcExp hζ a) = a :=
  lfcExp_injective hζ (lfcExp_lfcLog hζ (lfcExp_pow hζ a))

private theorem lfcLog_mul {z z' : Fˣ} (hz : z ^ p = 1) (hz' : z' ^ p = 1) :
    lfcLog hζ (z * z') = lfcLog hζ z + lfcLog hζ z' := by
  apply lfcExp_injective hζ
  rw [lfcExp_add, lfcExp_lfcLog hζ hz, lfcExp_lfcLog hζ hz',
    lfcExp_lfcLog hζ (by rw [mul_pow, hz, hz', one_mul])]

private theorem lfcLog_one : lfcLog hζ (1 : Fˣ) = 0 := by
  have h := lfcLog_mul hζ (z := 1) (z' := 1) (one_pow p) (one_pow p)
  rw [mul_one] at h
  linear_combination -h

end Log

private theorem lfc_ker_comp_conj {K G : Type*} [Group K] [Group G] {ψ : K →* G}
    (hker : ψ.ker ≤ Subgroup.center K) (u : K) :
    (ψ.comp (MulAut.conj u).toMonoidHom).ker ≤ Subgroup.center K := by
  intro z hz
  have hc := hker (show ψ (u * z * u⁻¹) = 1 from hz)
  have := Subgroup.Normal.conj_mem inferInstance _ hc u⁻¹
  simpa [mul_assoc] using this

private theorem lfc_range_comp_conj {K G : Type*} [Group K] [Group G] (ψ : K →* G) (u : K) :
    (ψ.comp (MulAut.conj u).toMonoidHom).range = ψ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj u).surjective,
    Subgroup.map_top]

end LFrameCore

section Certs


open LFrameCore in
theorem exists_lFrame_of_innerDiagOn (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hmark : GGInnerDiagOn Bs X)
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    {m : ℕ} (hm : 3 ≤ m) (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p)))
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull (m + 1) p)
    {f : ℕ} (hf : 1 ≤ f)
    {ψ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (hrange : ψ.range = X) (π : Equiv.Perm (Fin (m + 1))) :
    ∃ (σ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
      σ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) ∧
      σ.range = X ∧ Function.Injective χ ∧
      ∀ b : ↥Bs, ((b : G), InnerDiagA.diagGL (fun k => χ (eta b (π k)))) ∈
        LinFusion.ggInducedPairs σ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f with hFdef
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hcardBs : Nat.card Bs = p ^ (m + 1) := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_multiplicative, ZMod.card, Fintype.card_fin]
  have hC' : Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ p := by
    rw [hrange]; exact hC
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 f :=
    ⟨Nat.prime_two, hf, by omega, fun h => by simp at h; omega, fun h => by simp at h; omega⟩
  have hQ : ∀ b ∈ Bs, GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ b := by
    let ψu : (ggU .PSL (m + 1) f).K →* G := ψ
    have hrk : 2 ≤ (ggU .PSL (m + 1) f).D.rank := by
      show 2 ≤ m
      omega
    have hmk := hMp G .PSL (m + 1) f ψu hadm hrk hker X hrange _ hmark
    exact largeEvenMarking_elim_const
      (Q := ∀ b ∈ Bs, GGPsiInnerDiag (ggU .PSL (m + 1) f).D ψu b)
      (largeEvenMarking_mono (fun _ _ _ _ _ _ h b hb => h.2 b (h.1.1 hb) (h.1.2 b hb)) hmk)
  have hinn : ∀ b ∈ Bs, ∃ A : GL (Fin (m + 1)) F, (b, A) ∈ LinFusion.ggInducedPairs ψ :=
    fun b hb => LinFusion.exists_mem_ggInducedPairs (by omega) ψ hker (hQ b⁻¹ (Bs.inv_mem hb))
  have hpq : p ∣ Nat.card F - 1 :=
    LFrameSplit.dvd_card_sub_one_of_ggInducedPairs (by omega) hker hp hp2 hBs hinn (by
      rw [hcardBs, pow_succ]
      exact Nat.mul_le_mul_left _ hC')
  obtain ⟨s, hstd⟩ := StdPosA.exists_stdPos_sl (F := F) (by omega) hp hp2 hpq hker hBs hQ
    (by
      rw [hcardBs]
      calc p ^ (m - 1) * _ ≤ p ^ (m - 1) * p := Nat.mul_le_mul_left _ hC'
        _ = p ^ m := by rw [← pow_succ]; congr 1; omega
        _ ≤ p ^ (m + 1) := Nat.pow_le_pow_right hp.pos (by omega))
    (by
      rw [hcardBs]
      calc p ^ 3 * _ ≤ p ^ 3 * p := Nat.mul_le_mul_left _ hC'
        _ = p ^ 4 := by rw [← pow_succ]
        _ ≤ p ^ (m + 1) := Nat.pow_le_pow_right hp.pos (by omega))
  set ψ' := ψ.comp (MulAut.conj s).toMonoidHom with hψ'
  have hker' : ψ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) :=
    lfc_ker_comp_conj hker s
  have hrange' : ψ'.range = X := by rw [hψ', lfc_range_comp_conj, hrange]
  obtain ⟨δ, hδ, hδp, -, hfull⟩ := ggDk_exists_diagFrame (F := F) (by omega) hker' hp hBs hstd
    hcardBs (by rw [hrange']; exact hC)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fˣ, IsPrimitiveRoot ζ p := by
    have h1 : p ∣ Nat.card Fˣ := by
      rw [Nat.card_units]
      exact hpq
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p h1
    exact ⟨y, by simpa [hy] using IsPrimitiveRoot.orderOf y⟩
  let Ev : (Fin (m + 1) → ZMod p) → ↥Bs := fun v => eta.symm (fun k => Multiplicative.ofAdd (v k))
  have hEv_eta : ∀ b : ↥Bs, Ev (fun k => Multiplicative.toAdd (eta b k)) = b := fun b => by
    simp only [Ev, ofAdd_toAdd]
    exact eta.symm_apply_apply b
  have hEta_Ev : ∀ v k, Multiplicative.toAdd (eta (Ev v) k) = v k := fun v k => by
    simp only [Ev, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hEv_add : ∀ v w, Ev (v + w) = Ev v * Ev w := fun v w => by
    simp only [Ev, ← map_mul]
    rfl
  have hEv_zero : Ev 0 = 1 := by
    simp only [Ev]
    exact map_one eta.symm
  let M : (Fin (m + 1) → ZMod p) →+ (Fin (m + 1) → ZMod p) :=
    { toFun := fun v k => lfcLog hζ (δ (Ev v) k)
      map_zero' := by
        funext k
        rw [hEv_zero, map_one, Pi.one_apply, lfcLog_one]
        rfl
      map_add' := fun v w => by
        funext k
        rw [hEv_add, map_mul, Pi.mul_apply, Pi.add_apply, lfcLog_mul hζ (hδp _ k) (hδp _ k)] }
  have hM : ∀ v k, M v k = lfcLog hζ (δ (Ev v) k) := fun _ _ => rfl
  have hcent : ∀ b : ↥Bs, (∃ c : Fˣ, ∀ k, δ b k = c) →
      (b : G) ∈ Subgroup.centralizer (X : Set G) := by
    rintro b ⟨c, hc⟩
    have h1 := LinModel.scalar_mul_mem_ggInducedPairs (hδ b) c⁻¹
    have h3 : (fun i => c⁻¹ * δ b i) = 1 := funext fun i => by
      rw [hc i, inv_mul_cancel]
      rfl
    rw [LinModel.scalar_mul_diagGL, h3, LinFusion.diagGL_one] at h1
    rw [← hrange']
    exact LinFusion.mem_centralizer_of_mem_ggInducedPairs_one h1
  have hinj : ∀ v, (∃ s, ∀ k, M v k = s) → ∃ s, ∀ k, v k = s := by
    rintro v ⟨s, hs⟩
    have hc : ((Ev v : ↥Bs) : G) ∈ Subgroup.centralizer (X : Set G) :=
      hcent (Ev v) ⟨lfcExp hζ s, fun k => by rw [← hs k, hM, lfcExp_lfcLog hζ (hδp _ k)]⟩
    refine ⟨v ⟨0, by omega⟩, fun k => ?_⟩
    rw [← hEta_Ev v k, ← hEta_Ev v ⟨0, by omega⟩,
      lfc_eta_const eta hA (Ev v) hc k ⟨0, by omega⟩]
  have hsurj : ∀ y : Fin (m + 1) → ZMod p, ∃ v s, ∀ k, y k = M v k + s := by
    intro y
    obtain ⟨b, c, hbc⟩ := hfull (fun k => lfcExp hζ (y k)) (fun k => lfcExp_pow hζ (y k))
    have hcp : c ^ p = 1 := by
      have h1 := hδp b 0
      rw [hbc 0, mul_pow, lfcExp_pow, mul_one] at h1
      exact h1
    refine ⟨fun k => Multiplicative.toAdd (eta b k), -lfcLog hζ c, fun k => ?_⟩
    rw [hM, hEv_eta, hbc k, lfcLog_mul hζ hcp (lfcExp_pow hζ _), lfcLog_lfcExp]
    exact (add_neg_cancel_comm (lfcLog hζ c) (y k)).symm
  have hacts : ∀ b : ↥Bs, GGActsVec ψ' (b : G) (δ b) := fun b =>
    ggActsVec_iff_mem_ggInducedPairs.mpr (hδ b)
  have hnorm : ∀ w : Equiv.Perm (Fin (m + 1)),
      ψ' (slPerm h2 w) ∈ Subgroup.normalizer (Bs : Set G) :=
    slPerm_mem_normalizer_of_actsDiag h2 hBs.2 hBsC hker' (fun b hb => ⟨δ ⟨b, hb⟩, hacts ⟨b, hb⟩⟩)
  have hΦ : ∀ w : Equiv.Perm (Fin (m + 1)), ∃ τ : Equiv.Perm (Fin (m + 1)),
      ∀ v, ∃ s, ∀ k, M (v ∘ τ.symm) k = M v (w.symm k) + s := by
    intro w
    have hgX : ψ' (slPerm h2 w) ∈ X := hrange' ▸ ⟨slPerm h2 w, rfl⟩
    have hα : ggConjAut Bs (hnorm w) ∈ ggAutomizer X Bs :=
      Subgroup.subset_closure (ggConjAut_mem_ggInduced hgX (hnorm w))
    have hmem : (MulAut.congr eta).toMonoidHom (ggConjAut Bs (hnorm w)) ∈
        aPermutationFull (m + 1) p := by
      rw [← hA]
      exact Subgroup.mem_map_of_mem _ hα
    obtain ⟨τ, hτ⟩ := lfc_exists_perm_of_mem_aPermutationFull hmem
    refine ⟨τ, fun v => ?_⟩
    have hconj : Ev (v ∘ τ.symm) = ggConjAut Bs (hnorm w) (Ev v) := by
      apply eta.injective
      have h1 := congrArg (fun φ : MulAut _ => φ (eta (Ev v))) hτ
      change eta (ggConjAut Bs (hnorm w) (eta.symm (eta (Ev v)))) =
        SpCoord.permAut τ (eta (Ev v)) at h1
      rw [MulEquiv.symm_apply_apply] at h1
      rw [h1]
      funext k
      apply Multiplicative.toAdd.injective
      rw [hEta_Ev, SpCoord.permAut_apply]
      exact (hEta_Ev v (τ.symm k)).symm
    have hv1 := GGActsVec.conj_perm h2 (hacts (Ev v)) w
    have hv2 : GGActsVec ψ' (ψ' (slPerm h2 w) * ((Ev v : ↥Bs) : G) * (ψ' (slPerm h2 w))⁻¹)
        (δ (Ev (v ∘ τ.symm))) := by
      have h1 := hacts (Ev (v ∘ τ.symm))
      have h3 : ((Ev (v ∘ τ.symm) : ↥Bs) : G) =
          ψ' (slPerm h2 w) * ((Ev v : ↥Bs) : G) * (ψ' (slPerm h2 w))⁻¹ := by
        rw [hconj, ggConjAut_apply]
      rwa [h3] at h1
    obtain ⟨c, hc⟩ := ggVecEq_iff_exists.mp (hv2.vecEq hker' hv1)
    have hcp : c ^ p = 1 := by
      have h1 := hδp (Ev (v ∘ τ.symm)) 0
      rw [hc 0, mul_pow, Function.comp_apply, hδp, mul_one] at h1
      exact h1
    refine ⟨lfcLog hζ c, fun k => ?_⟩
    rw [hM, hM, hc k, Function.comp_apply, lfcLog_mul hζ hcp (hδp _ _), add_comm]
  obtain ⟨f₀, c, hc0, hfc⟩ :=
    LFrameAlign.exists_perm_smul_of_modConst hp2 (by omega) M hinj hsurj hΦ
  let χ : Multiplicative (ZMod p) →* Fˣ :=
    { toFun := fun a => lfcExp hζ (c * Multiplicative.toAdd a)
      map_one' := by
        rw [toAdd_one, mul_zero, lfcExp_zero]
      map_mul' := fun a b => by
        rw [toAdd_mul, mul_add, lfcExp_add] }
  have hχinj : Function.Injective χ := fun a b h =>
    Multiplicative.toAdd.injective (mul_left_cancel₀ hc0 (lfcExp_injective hζ h))
  have hframe0 : ∀ b : ↥Bs, GGActsVec ψ' (b : G) (fun k => χ (eta b (f₀ k))) := by
    intro b
    obtain ⟨s', hs'⟩ := hfc (fun k => Multiplicative.toAdd (eta b k))
    refine (hacts b).of_vecEq (ggVecEq_iff_exists.mpr ⟨lfcExp hζ s', fun k => ?_⟩)
    have h1 := hs' k
    rw [hM, hEv_eta] at h1
    rw [← lfcExp_lfcLog hζ (hδp b k), h1, lfcExp_add, mul_comm]
    rfl
  set ρ : Equiv.Perm (Fin (m + 1)) := f₀⁻¹ * π with hρ
  refine ⟨ψ'.comp (MulAut.conj (slPerm h2 ρ)).toMonoidHom, χ, lfc_ker_comp_conj hker' _,
    by rw [lfc_range_comp_conj, hrange'], hχinj, fun b => ?_⟩
  rw [← ggActsVec_iff_mem_ggInducedPairs]
  intro u
  have h1 := hframe0 b (slPerm h2 ρ * u * (slPerm h2 ρ)⁻¹)
  have hd : (fun k => χ (eta b (π k))) ∘ ρ.symm = fun k => χ (eta b (f₀ k)) := by
    funext k
    have h3 : π (ρ.symm k) = f₀ k := by
      have h4 : ρ.symm k = π.symm (f₀ k) := by
        rw [Equiv.symm_apply_eq, hρ, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
          Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      rw [h4, Equiv.apply_symm_apply]
    simp only [Function.comp_apply, h3]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [h1, slPerm_mul_ggDiagConj h2 ρ, hd]

end Certs

end CFSG.StandardType

end
