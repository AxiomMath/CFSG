module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideA8Frame
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideA8Fix
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideGe
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreAmbientRefl

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
  {T₀ : Subgroup (ModGL τ L)} {m : Fin 6}

theorem ExcCoordDatum.tuple_eq_of_rootChar_eq (d : ExcCoordDatum S T₀ m)
    {a b : Fin τ.rank → Lˣ} (h : ∀ i, rootChar a (d.γ i) = rootChar b (d.γ i)) : a = b := by
  funext k
  have hsingle : ∀ c : Fin τ.rank → Lˣ, rootChar c (Pi.single k 1) = c k := by
    intro c
    simpa using rootChar_nsmul_single c k 1
  rw [← hsingle a, ← hsingle b]
  obtain ⟨j, hj | hj⟩ := d.exists_eq (Pi.single k 1) (isRoot_single τ k)
  · rw [hj]
    exact h j
  · have hneg : ∀ c : Fin τ.rank → Lˣ,
        rootChar c (-(d.γ j)) = (rootChar c (d.γ j))⁻¹ := by
      intro c
      have hc := rootChar_sub c 0 (d.γ j)
      rw [zero_sub, rootChar_zero, one_mul] at hc
      exact hc
    rw [hj, hneg a, hneg b, h j]

theorem rootChar_chainExp_a8Chain (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (d : ExcCoordDatum S T₀ m) {c : Finset (ExcRaw.Root m)} (w : ExcRaw.A8Witness m c)
    (μ : Lˣ) (t : ExcRaw.Root m) :
    rootChar (fun k => μ ^ chainExp (a8Chain d w) 8 k) (d.γ t) =
      μ ^ ∑ a : Fin 8, ((a : ℕ) + 1 : ℤ) * ExcRaw.pairing m t (w.b a) := by
  classical
  have hsimply : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  have hroot : ∀ a : Fin 8, IsRoot τ (a8Chain d w a) := fun a => d.isRoot (w.b a)
  have hv : (∑ k, d.γ t k • (Pi.single k 1 : Fin τ.rank → ℤ)) = d.γ t :=
    (pi_eq_sum_univ' (d.γ t)).symm
  have hlin : ∀ a : Fin 8,
      ∑ k, corootPair (a8Chain d w a) (Pi.single k 1) * d.γ t k =
        ExcRaw.pairing m t (w.b a) := by
    intro a
    calc ∑ k, corootPair (a8Chain d w a) (Pi.single k 1) * d.γ t k
        = ∑ k, iform (a8Chain d w a) (Pi.single k 1) * d.γ t k := by
          refine Finset.sum_congr rfl fun k _ => by
            rw [corootPair_eq_iform_of_simplyLaced hsimply (hroot a)]
      _ = iform (a8Chain d w a) (d.γ t) := by
          conv_rhs => rw [← hv]
          rw [iform_finset_sum_right]
          refine Finset.sum_congr rfl fun k _ => by
            rw [iform_smul_right]
            ring
      _ = corootPair (a8Chain d w a) (d.γ t) := by
          rw [corootPair_eq_iform_of_simplyLaced hsimply (hroot a)]
      _ = ExcRaw.pairing m t (w.b a) := (d.pairing_eq t (w.b a)).symm
  have hchain : ∀ k, chainExp (a8Chain d w) 8 k =
      ∑ a : Fin 8, ((a : ℤ) + 1) * corootPair (a8Chain d w a) (Pi.single k 1) := by
    intro k
    rw [chainExp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [if_pos a.isLt]
  have hkey : ∑ k, chainExp (a8Chain d w) 8 k * d.γ t k =
      ∑ a : Fin 8, ((a : ℕ) + 1 : ℤ) * ExcRaw.pairing m t (w.b a) := by
    calc ∑ k, chainExp (a8Chain d w) 8 k * d.γ t k
        = ∑ k, (∑ a : Fin 8, ((a : ℤ) + 1) *
            corootPair (a8Chain d w a) (Pi.single k 1)) * d.γ t k := by
          refine Finset.sum_congr rfl fun k _ => by rw [hchain k]
      _ = ∑ k, ∑ a : Fin 8, (((a : ℤ) + 1) *
            corootPair (a8Chain d w a) (Pi.single k 1)) * d.γ t k := by
          refine Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
      _ = ∑ a : Fin 8, ∑ k, (((a : ℤ) + 1) *
            corootPair (a8Chain d w a) (Pi.single k 1)) * d.γ t k := by
          rw [Finset.sum_comm]
      _ = ∑ a : Fin 8, ((a : ℤ) + 1) *
            ∑ k, corootPair (a8Chain d w a) (Pi.single k 1) * d.γ t k := by
          refine Finset.sum_congr rfl fun a _ => by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ a : Fin 8, ((a : ℕ) + 1 : ℤ) * ExcRaw.pairing m t (w.b a) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          have hcoef : ((a : ℤ) + 1) = ((a : ℕ) + 1 : ℤ) := by ring
          rw [hlin a, hcoef]
  calc rootChar (fun k => μ ^ chainExp (a8Chain d w) 8 k) (d.γ t)
      = ∏ k, μ ^ (chainExp (a8Chain d w) 8 k * d.γ t k) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← zpow_mul]
    _ = μ ^ ∑ k, chainExp (a8Chain d w) 8 k * d.γ t k :=
        Finset.prod_zpow_eq_zpow_sum _ _ _
    _ = μ ^ ∑ a : Fin 8, ((a : ℕ) + 1 : ℤ) * ExcRaw.pairing m t (w.b a) := by
        rw [hkey]


private theorem cz_eq_zero_of_mem_ggLinImage (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hS : NegLangTwo S) (d : ExcCoordDatum S T₀ m) {c : Finset (ExcRaw.Root m)}
    (w : ExcRaw.A8Witness m c)
    (hcz : w.cz ∈ ggLinImage (p := 3) d.coord (codeComponent S d.γ c)) : w.cz = 0 := by
  classical
  let z₀ : ↥T₀ := Additive.toMul (d.coord.symm w.cz)
  have hz₀coord : d.coord (Additive.ofMul z₀) = w.cz := by
    change d.coord (d.coord.symm w.cz) = w.cz
    exact d.coord.apply_symm_apply w.cz
  have hz₀mem : (z₀ : ModGL τ L) ∈ codeComponent S d.γ c := by
    simpa [z₀] using (mem_ggLinImage d.coord (codeComponent S d.γ c) w.cz).mp hcz
  obtain ⟨ψ, hψ⟩ := exists_a8ChainHom hτ d w
  have hβ : ∀ a, IsRoot τ (a8Chain d w a) := fun a => d.isRoot (w.b a)
  have hframe : IsSLFrame ψ (chainσ (a8Chain d w)) :=
    isSLFrame_chainHom (m := 8) (β := a8Chain d w) (Or.inr hτ) hβ
      (iform_a8Chain hτ d w) hψ
  have hker : ψ.ker ≤ Subgroup.center (SL(8 + 1, L)) :=
    ker_le_center_of_isSLFrame (ν := 8 + 1) (by norm_num) hframe
  obtain ⟨F', hcomm, hscal⟩ :=
    exists_unitaryLift_of_frame (ν := 8 + 1) hS (by norm_num) hframe
  have hΨ : codeRoots d.γ c ⊆ frameRoots (chainσ (a8Chain d w)) :=
    codeRoots_subset_frameRoots_a8Chain hτ d w
  have hcode : codeComponent S d.γ c ≤ (F'.eqLocus (MonoidHom.id _)).map ψ :=
    commutator_le_map_eqLocus_of_frame (ν := 8 + 1) hframe hΨ hker F' hcomm
  obtain ⟨Y, hY, hψY⟩ := Subgroup.mem_map.mp (hcode hz₀mem)
  have hYfix : F' Y = Y := hY
  obtain ⟨ω₀, hω₀⟩ := IsAlgClosed.exists_pow_nat_eq (d.ζ : L) (by norm_num : 0 < 3)
  have hω₀ne : ω₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at hω₀
    exact Units.ne_zero d.ζ hω₀.symm
  let ω : Lˣ := Units.mk0 ω₀ hω₀ne
  have hω3 : ω ^ 3 = d.ζ := by
    apply Units.ext
    simpa [ω] using hω₀
  have hω9 : ω ^ (8 + 1) = 1 := by
    have e : ω ^ (8 + 1) = (ω ^ 3) ^ 3 := by
      rw [show 8 + 1 = 3 * 3 by norm_num, pow_mul]
    rw [e, hω3, d.ζ_pow_three]
  let Q : SL(8 + 1, L) := blockTorusProd (m := 8) ω 8
  have hQmat : (Q : Matrix (Fin (8 + 1)) (Fin (8 + 1)) L) =
      Matrix.scalar (Fin (8 + 1)) (ω : L) :=
    coe_blockTorusProd_eq_scalar (m := 8) ω hω9
  have hψQ : ψ Q = rootDiagUnit τ (fun k => ω ^ chainExp (a8Chain d w) 8 k) :=
    chainHom_blockTorusProd (m := 8) (β := a8Chain d w) hβ hψ ω 8 le_rfl
  obtain ⟨b₀, hb₀⟩ := d.exists_rootDiagUnit z₀
  have hrootChar_b₀ (t : ExcRaw.Root m) :
      rootChar b₀ (d.γ t) = d.ζ ^ (ExcRaw.root m t w.cz).val := by
    rw [d.rootChar_eq z₀ b₀ hb₀ t, hz₀coord]
  have hζpow (t : ExcRaw.Root m) (ℓ : ℤ)
      (hmod : (ℓ : ZMod 3) = ExcRaw.root m t w.cz) :
      d.ζ ^ ℓ = d.ζ ^ (ExcRaw.root m t w.cz).val := by
    have hcast : (((ExcRaw.root m t w.cz).val : ℤ) : ZMod 3) = (ℓ : ZMod 3) := by
      push_cast
      rw [ZMod.natCast_zmod_val, hmod]
    have hmod3 : ((ExcRaw.root m t w.cz).val : ℤ) % 3 = ℓ % 3 :=
      (ZMod.intCast_eq_intCast_iff' _ _ 3).1 hcast
    calc d.ζ ^ ℓ = d.ζ ^ (ℓ % 3) := zpow_eq_zpow_emod' ℓ d.ζ_pow_three
      _ = d.ζ ^ (((ExcRaw.root m t w.cz).val : ℤ) % 3) := by rw [hmod3]
      _ = d.ζ ^ ((ExcRaw.root m t w.cz).val : ℤ) :=
        (zpow_eq_zpow_emod' _ d.ζ_pow_three).symm
      _ = d.ζ ^ (ExcRaw.root m t w.cz).val := zpow_natCast _ _
  have hrootChar_ω (t : ExcRaw.Root m) :
      rootChar (fun k => ω ^ chainExp (a8Chain d w) 8 k) (d.γ t) =
        d.ζ ^ (ExcRaw.root m t w.cz).val := by
    rw [rootChar_chainExp_a8Chain hτ d w ω t]
    obtain ⟨ℓ, hsum, hmod⟩ := w.root_cz t
    have hω3z : ω ^ (3 : ℤ) = d.ζ := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact hω3
    rw [hsum, zpow_mul, hω3z]
    exact hζpow t ℓ hmod
  have hb₀eq : b₀ = fun k => ω ^ chainExp (a8Chain d w) 8 k := by
    apply ExcCoordDatum.tuple_eq_of_rootChar_eq d
    intro t
    rw [hrootChar_b₀ t, hrootChar_ω t]
  have hz₀ω : (z₀ : ModGL τ L) =
      rootDiagUnit τ (fun k => ω ^ chainExp (a8Chain d w) 8 k) := by
    rw [hb₀, hb₀eq]
  have hψQz : ψ Q = (z₀ : ModGL τ L) := hψQ.trans hz₀ω.symm
  have hkerQ : Y⁻¹ * Q ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψY, hψQz]
    simp
  have hcenter : Y⁻¹ * Q ∈ Subgroup.center (SL(8 + 1, L)) := hker hkerQ
  obtain ⟨r, hr, hrS⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcenter
  have hr9 : r ^ 9 = 1 := by simpa using hr
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 9 ≠ 0)] at hr9
    exact zero_ne_one hr9
  let μ : L := (ω : L) * r⁻¹
  have hμne : μ ≠ 0 := mul_ne_zero (Units.ne_zero ω) (inv_ne_zero hr0)
  have hYmat : (Y : Matrix (Fin (8 + 1)) (Fin (8 + 1)) L) =
      Matrix.scalar (Fin (8 + 1)) μ := by
    have hYS : Y * (Y⁻¹ * Q) = Q := by group
    have hmul : (Y : Matrix (Fin (8 + 1)) (Fin (8 + 1)) L) *
        Matrix.scalar (Fin (8 + 1)) r = Matrix.scalar (Fin (8 + 1)) (ω : L) := by
      rw [hrS, ← Matrix.SpecialLinearGroup.coe_mul, hYS, hQmat]
    have hrinv : Matrix.scalar (Fin (8 + 1)) r * Matrix.scalar (Fin (8 + 1)) r⁻¹ = 1 := by
      rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, mul_inv_cancel₀ hr0, one_smul]
    have h1 := congrArg (fun M : Matrix (Fin (8 + 1)) (Fin (8 + 1)) L =>
      M * Matrix.scalar (Fin (8 + 1)) r⁻¹) hmul
    rw [mul_assoc, hrinv, mul_one, Matrix.scalar_apply, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, Matrix.smul_one_eq_diagonal] at h1
    simpa [μ, Matrix.scalar_apply] using h1
  have hμinv : (μ ^ 2)⁻¹ = μ := by
    have hscalY := hscal μ Y hYmat
    have hscalar : Matrix.scalar (Fin (8 + 1)) ((μ ^ 2)⁻¹) =
        Matrix.scalar (Fin (8 + 1)) μ := by
      rw [← hscalY, hYfix, hYmat]
    have h00 := congrFun (congrFun hscalar ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa [Matrix.scalar_apply] using h00
  have hμ3 : μ ^ 3 = 1 := by
    have h2 : μ ^ 2 ≠ 0 := pow_ne_zero 2 hμne
    calc μ ^ 3 = μ * μ ^ 2 := by ring
      _ = (μ ^ 2)⁻¹ * μ ^ 2 := by rw [hμinv]
      _ = 1 := inv_mul_cancel₀ h2
  let μu : Lˣ := Units.mk0 μ hμne
  have hμu3 : μu ^ 3 = 1 := by
    apply Units.ext
    simpa [μu] using hμ3
  have hμu9 : μu ^ (8 + 1) = 1 := by
    have e : μu ^ (8 + 1) = (μu ^ 3) ^ 3 := by
      rw [show 8 + 1 = 3 * 3 by norm_num, pow_mul]
    rw [e, hμu3, one_pow]
  have hYQ : Y = blockTorusProd (m := 8) μu 8 := by
    apply Subtype.ext
    rw [hYmat]
    simpa [μu] using (coe_blockTorusProd_eq_scalar (m := 8) μu hμu9).symm
  have hψYQ : ψ (blockTorusProd (m := 8) μu 8) =
      rootDiagUnit τ (fun k => μu ^ chainExp (a8Chain d w) 8 k) :=
    chainHom_blockTorusProd (m := 8) (β := a8Chain d w) hβ hψ μu 8 le_rfl
  have htuple1 : (fun k => μu ^ chainExp (a8Chain d w) 8 k) = 1 := by
    apply ExcCoordDatum.tuple_eq_of_rootChar_eq d
    intro t
    rw [rootChar_chainExp_a8Chain hτ d w μu t]
    have hone : rootChar (1 : Fin τ.rank → Lˣ) (d.γ t) = 1 := by simp [rootChar]
    rw [hone]
    obtain ⟨ℓ, hsum, hmod⟩ := w.root_cz t
    have hμu3z : μu ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact hμu3
    rw [hsum, zpow_mul, hμu3z, one_zpow]
  have hz₀μ : (z₀ : ModGL τ L) =
      rootDiagUnit τ (fun k => μu ^ chainExp (a8Chain d w) 8 k) := by
    rw [← hψY, hYQ]
    exact hψYQ
  have hz₀1 : (z₀ : ModGL τ L) = 1 := by
    rw [hz₀μ, htuple1, rootDiagUnit_one]
  have hz₀1' : z₀ = 1 := Subtype.ext hz₀1
  calc w.cz = d.coord (Additive.ofMul z₀) := hz₀coord.symm
    _ = d.coord (Additive.ofMul 1) := by rw [hz₀1']
    _ = 0 := by simp

theorem ggLinImage_codeComponent_le_inside_of_a8 (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hS : NegLangTwo S) (d : ExcCoordDatum S T₀ m) {c : Finset (ExcRaw.Root m)}
    (w : ExcRaw.A8Witness m c) :
    ggLinImage (p := 3) d.coord (codeComponent S d.γ c) ≤ ExcRaw.inside m c := by
  intro v hv
  obtain ⟨x, hx⟩ := w.hyper v
  have himg : v - x • w.cz ∈ ggLinImage (p := 3) d.coord (codeComponent S d.γ c) :=
    inside_le_ggLinImage_codeComponent (Or.inr hτ) hS d c hx
  have hximg : x • w.cz ∈ ggLinImage (p := 3) d.coord (codeComponent S d.γ c) := by
    have := (ggLinImage (p := 3) d.coord (codeComponent S d.γ c)).sub_mem hv himg
    simpa [sub_sub_cancel] using this
  by_cases hx0 : x = 0
  · simpa [hx0] using hx
  · have hcz : w.cz ∈ ggLinImage (p := 3) d.coord (codeComponent S d.γ c) := by
      have := (ggLinImage (p := 3) d.coord (codeComponent S d.γ c)).smul_mem x⁻¹ hximg
      rwa [inv_smul_smul₀ hx0] at this
    have hcz0 : w.cz = 0 := cz_eq_zero_of_mem_ggLinImage hτ hS d w hcz
    simpa [hcz0] using hx

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
