module

public import CFSG.Quasithin.Vol2.Ch10SecKHK3B
public import CFSG.Quasithin.Vol2.Ch11SecB23Two
public import CFSG.Quasithin.Vol2.Ch11SecFFacts3
public import CFSG.Quasithin.Vol2.Ch11SecO2D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Vol2Native.A312L (spLevi spMat spMat_lam spLevi_mem_perfectCore)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (pairMat)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer flag)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (gammaW_pre_eq pCoreOf_Q0_eq)
open scoped IsMulCommutative commutatorElement

namespace O2

variable {K : Type} [Field K]

def IsNF (M : StatedSp 2 K) (a b c : K) : Prop :=
  ∀ v : Fin 2 ⊕ Fin 2 → K, mat 2 K M *ᵥ v =
    vec4 (v (.inl 0) + a * v (.inl 1) + b * v (.inr 0) + c * v (.inr 1))
      (v (.inl 1) + c * v (.inr 0)) (v (.inr 0)) (v (.inr 1) + a * v (.inr 0))

theorem isNF_mul {M M' : StatedSp 2 K} {a b c a' b' c' : K} (h : IsNF M a b c)
    (h' : IsNF M' a' b' c') : IsNF (M * M') (a + a') (b + b' + a * c' + a' * c) (c + c') := by
  intro v
  rw [map_mul, ← Matrix.mulVec_mulVec, h', h]
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp only [vec4, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

theorem isNF_congr {M : StatedSp 2 K} {a b c a' b' c' : K} (h : IsNF M a b c) (ha : a = a')
    (hb : b = b') (hc : c = c') : IsNF M a' b' c' := by
  subst ha hb hc
  exact h

theorem eq_of_isNF {M M' : StatedSp 2 K} {a b c : K} (h : IsNF M a b c) (h' : IsNF M' a b c) :
    M = M' :=
  SecB.K7.sp_ext fun v => by rw [h, h']

theorem mulVec_levi0 (B : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (spLevi 0 B) *ᵥ v = vec4 (v (.inl 0))
      ((B : Matrix (Fin 2) (Fin 2) K) 0 0 * v (.inl 1) + (B : Matrix (Fin 2) (Fin 2) K) 0 1 *
        v (.inr 1)) (v (.inr 0))
      ((B : Matrix (Fin 2) (Fin 2) K) 1 0 * v (.inl 1) + (B : Matrix (Fin 2) (Fin 2) K) 1 1 *
        v (.inr 1)) := by
  rw [show mat 2 K (spLevi 0 B) = spMat (spLevi 0 B) from rfl, spMat_lam]
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, pairMat, vec4, Matrix.one_apply]

variable [CharP K 2]

theorem mul_self_of_isNF {M : StatedSp 2 K} {a b c : K} (h : IsNF M a b c) : M * M = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 := isNF_mul h h
  refine SecB.K7.sp_ext fun v => ?_
  rw [h1, map_one, Matrix.one_mulVec]
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp only [vec4, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
  · linear_combination (a * v (.inl 1) + (b + a * c) * v (.inr 0) + c * v (.inr 1)) * h2
  · linear_combination c * v (.inr 0) * h2
  · linear_combination a * v (.inr 0) * h2

theorem inv_of_isNF {M : StatedSp 2 K} {a b c : K} (h : IsNF M a b c) : M⁻¹ = M :=
  inv_eq_of_mul_eq_one_right (mul_self_of_isNF h)

theorem isNF_levi_conj {M : StatedSp 2 K} {a b c : K} (h : IsNF M a b c)
    (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    IsNF (spLevi 0 B * M * (spLevi 0 B)⁻¹)
      ((B : Matrix (Fin 2) (Fin 2) K) 1 0 * c + (B : Matrix (Fin 2) (Fin 2) K) 1 1 * a) b
      ((B : Matrix (Fin 2) (Fin 2) K) 0 0 * c + (B : Matrix (Fin 2) (Fin 2) K) 0 1 * a) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet := Matrix.SpecialLinearGroup.det_coe B
  rw [Matrix.det_fin_two] at hdet
  have hinv : (spLevi (K := K) 0 B)⁻¹ = spLevi 0 B⁻¹ := (map_inv _ _).symm
  have hBi : ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(B : Matrix (Fin 2) (Fin 2) K) 1 1, -(B : Matrix (Fin 2) (Fin 2) K) 0 1;
        -(B : Matrix (Fin 2) (Fin 2) K) 1 0, (B : Matrix (Fin 2) (Fin 2) K) 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  intro v
  rw [hinv, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_levi0, h,
    mulVec_levi0, hBi]
  set B₀₀ := (B : Matrix (Fin 2) (Fin 2) K) 0 0
  set B₀₁ := (B : Matrix (Fin 2) (Fin 2) K) 0 1
  set B₁₀ := (B : Matrix (Fin 2) (Fin 2) K) 1 0
  set B₁₁ := (B : Matrix (Fin 2) (Fin 2) K) 1 1
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp only [vec4, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  · linear_combination (-(c * B₁₀ * v (.inl 1)) - a * B₀₁ * v (.inr 1)) * h2
  · linear_combination v (.inl 1) * hdet
  · linear_combination v (.inr 1) * hdet

theorem isNF_comm_levi {M : StatedSp 2 K} {a b c : K} (h : IsNF M a b c)
    (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    IsNF (M * spLevi 0 B * M⁻¹ * (spLevi 0 B)⁻¹)
      (a + ((B : Matrix (Fin 2) (Fin 2) K) 1 0 * c + (B : Matrix (Fin 2) (Fin 2) K) 1 1 * a))
      (a * ((B : Matrix (Fin 2) (Fin 2) K) 0 0 * c + (B : Matrix (Fin 2) (Fin 2) K) 0 1 * a) +
        ((B : Matrix (Fin 2) (Fin 2) K) 1 0 * c + (B : Matrix (Fin 2) (Fin 2) K) 1 1 * a) * c)
      (c + ((B : Matrix (Fin 2) (Fin 2) K) 0 0 * c + (B : Matrix (Fin 2) (Fin 2) K) 0 1 * a)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [inv_of_isNF h, show M * spLevi 0 B * M * (spLevi 0 B)⁻¹ =
    M * (spLevi 0 B * M * (spLevi 0 B)⁻¹) by group]
  exact isNF_congr (isNF_mul h (isNF_levi_conj h B)) rfl
    (by linear_combination b * h2) rfl

end O2

open O2 in
theorem factSp4RL_holds : FactSp4RL := by
  intro G _ _ T L I n V₁ V₃ X hS hk hV₁ hV₃ hX P hP hL₁P _ _ hne
  have := SecO1.isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, _, hK, π, f, hf, g, hπ, -, hV₁g, -, hV₃g⟩ := exists_coord hS hk
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have hinj := SecO1.IsCoord.injective_of_bot hf
  have hψ := psiSp_injective hf g
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  have hcommP : ⁅P, LOf L V₁⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro p hp l hl
    have h1 : l * p⁻¹ * l⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hL₁P hl) _).mp (P.inv_mem hp)
    have := P.mul_mem hp h1
    rwa [← mul_assoc, ← mul_assoc] at this
  have hcommL : ⁅P, LOf L V₁⁆ ≤ LOf L V₁ := by
    rw [Subgroup.commutator_le]
    intro p hp l hl
    have h1 : p * l * p⁻¹ ∈ LOf L V₁ :=
      (Subgroup.mem_normalizer_iff.mp (r1_le hS hV₁ (hP hp)).2 l).mp hl
    exact (LOf L V₁).mul_mem h1 ((LOf L V₁).inv_mem hl)
  set C := (autOn ⁅P, LOf L V₁⁆ (fsuV T I)).comap (psiSp π g) with hC
  have hlevi : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K,
      psiSp π g (spLevi 0 B) ∈ autOn (LOf L V₁) (fsuV T I) := by
    intro B
    rw [SecA.autOn_lOf hS.le_normalizer hV₁V, hV₁g V₁ hV₁]
    change _ ∈ SecS.gammaW _ _
    rw [gammaW_pre_eq hf g 0 _ flag_one_eq]
    exact ⟨_, spLevi_mem_perfectCore hK4 0 B, rfl⟩
  have hcommC : ∀ {M : StatedSp 2 K} {p : G} (hp : p ∈ P)
      (hpV : p ∈ Subgroup.normalizer (fsuV T I : Set G)),
      SecA.conjV (fsuV T I) p hpV = psiSp π g M →
      ∀ B : Matrix.SpecialLinearGroup (Fin 2) K,
        M * spLevi 0 B * M⁻¹ * (spLevi 0 B)⁻¹ ∈ C := by
    intro M p hp hpV hpM B
    obtain ⟨l, hl, hlV, hleq⟩ := SecA.mem_autOn_iff.mp (hlevi B)
    have hc : p * l * p⁻¹ * l⁻¹ ∈ ⁅P, LOf L V₁⁆ := Subgroup.commutator_mem_commutator hp hl
    show psiSp π g (M * spLevi 0 B * M⁻¹ * (spLevi 0 B)⁻¹) ∈ autOn ⁅P, LOf L V₁⁆ (fsuV T I)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hpM, hleq, ← SecA.conjV_inv,
      ← SecA.conjV_inv, ← SecA.conjV_mul, ← SecA.conjV_mul, ← SecA.conjV_mul]
    exact SecA.conjV_mem_autOn hc _
  have hcommC' : ∀ {M : StatedSp 2 K}, M ∈ C → ∀ B : Matrix.SpecialLinearGroup (Fin 2) K,
      M * spLevi 0 B * M⁻¹ * (spLevi 0 B)⁻¹ ∈ C := by
    intro M hM B
    obtain ⟨w, hw, hwV, hweq⟩ := SecA.mem_autOn_iff.mp hM
    exact hcommC (hcommP hw) hwV hweq.symm B
  obtain ⟨p₀, hp₀, u, hu, hpu⟩ : ∃ p ∈ P, ∃ u ∈ V₃, p * u ≠ u * p := by
    by_contra hall
    push Not at hall
    apply hne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro u hu p hp
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (hall p hp u hu).symm
  have hp₀V := (r1_le hS hV₁ (hP hp₀)).1.1.1
  obtain ⟨M₀, hM₀, hp₀M⟩ := exists_core_r1 hS hK hπ hf hV₁ (hV₁g V₁ hV₁) (hP hp₀)
  obtain ⟨a₀, b₀, c₀, hM₀v⟩ := mulVec_of_mem_pCoreOf hK4 hM₀
  have huV : u ∈ fsuV T I := SecA.IsVi.le_fsuV hV₃ hu
  have hac : ![c₀, a₀] ≠ 0 := by
    intro h0
    have hc0 : c₀ = 0 := by simpa using congrFun h0 0
    have ha0 : a₀ = 0 := by simpa using congrFun h0 1
    apply hpu
    have hu2 : (mat 2 K g⁻¹ *ᵥ f ⟨u, huV⟩) (.inr 0) = 0 :=
      (mem_iff_of_eq (hV₃g V₃ hV₃) ⟨u, huV⟩).mp hu
    have hfix : SecA.conjV (fsuV T I) p₀ hp₀V ⟨u, huV⟩ = ⟨u, huV⟩ := by
      apply hinj
      have h1 : mat 2 K g⁻¹ *ᵥ f (SecA.conjV (fsuV T I) p₀ hp₀V ⟨u, huV⟩) =
          mat 2 K M₀ *ᵥ (mat 2 K g⁻¹ *ᵥ f ⟨u, huV⟩) := by
        rw [hp₀M, psiSp_apply, hf.act4, conj_mulVec_sp]
      rw [hM₀v, ha0, hc0, hu2] at h1
      have h3 : mat 2 K g⁻¹ *ᵥ f (SecA.conjV (fsuV T I) p₀ hp₀V ⟨u, huV⟩) =
          mat 2 K g⁻¹ *ᵥ f ⟨u, huV⟩ := by
        rw [h1]
        refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4, hu2]
      have h4 := congrArg (fun x => mat 2 K g *ᵥ x) h3
      simpa only [mat_mulVec_inv] using h4
    have h5 := congrArg Subtype.val hfix
    rw [SecA.conjV_apply_coe] at h5
    calc p₀ * u = p₀ * u * p₀⁻¹ * p₀ := by group
      _ = u * p₀ := by rw [h5]
  obtain ⟨t, ht0, ht1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
  have hs0 : 1 + t ≠ 0 := by
    intro h
    apply ht1
    linear_combination h - h2
  obtain ⟨B₁, hB₁⟩ := Ch10.SecC.C10KH.exists_sl2_mulVec_eq hac (smul_ne_zero ht0 hac)
  have hB₁0 := congrFun hB₁ 0
  have hB₁1 := congrFun hB₁ 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul] at hB₁0 hB₁1
  obtain ⟨a₁, ha₁⟩ : ∃ x : K, x = (1 + t) * a₀ := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ x : K, x = (1 + t) * c₀ := ⟨_, rfl⟩
  have hM₁ : M₀ * spLevi 0 B₁ * M₀⁻¹ * (spLevi 0 B₁)⁻¹ ∈ C := hcommC hp₀ hp₀V hp₀M B₁
  have hM₁nf : IsNF (M₀ * spLevi 0 B₁ * M₀⁻¹ * (spLevi 0 B₁)⁻¹) a₁ 0 c₁ :=
    isNF_congr (isNF_comm_levi hM₀v B₁) (by linear_combination hB₁1 - ha₁)
      (by linear_combination a₀ * hB₁0 + c₀ * hB₁1 + t * a₀ * c₀ * h2)
      (by linear_combination hB₁0 - hc₁)
  have hw₁ : ![c₁, a₁] ≠ 0 := by
    intro h0
    apply hac
    have e0 : c₁ = 0 := by simpa using congrFun h0 0
    have e1 : a₁ = 0 := by simpa using congrFun h0 1
    rw [hc₁] at e0
    rw [ha₁] at e1
    rw [(mul_eq_zero.mp e0).resolve_left hs0, (mul_eq_zero.mp e1).resolve_left hs0]
    ext i
    fin_cases i <;> simp
  have hE : ∀ x₁ x₂ : K, ∃ E ∈ C, IsNF E x₂ (a₁ * x₁ + x₂ * c₁) x₁ := by
    intro x₁ x₂
    by_cases hx : ![c₁ + x₁, a₁ + x₂] = 0
    · have hx1 : x₁ = c₁ := by
        have := congrFun hx 0
        simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
        linear_combination this - c₁ * h2
      have hx2 : x₂ = a₁ := by
        have := congrFun hx 1
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at this
        linear_combination this - a₁ * h2
      refine ⟨_, hM₁, isNF_congr hM₁nf hx2.symm ?_ hx1.symm⟩
      rw [hx1, hx2]
      linear_combination (-(a₁ * c₁)) * h2
    · obtain ⟨B, hB⟩ := Ch10.SecC.C10KH.exists_sl2_mulVec_eq hw₁ hx
      have hB0 := congrFun hB 0
      have hB1 := congrFun hB 1
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one] at hB0 hB1
      refine ⟨_, hcommC' hM₁ B, isNF_congr (isNF_comm_levi hM₁nf B) ?_ ?_ ?_⟩
      · linear_combination hB1 + a₁ * h2
      · linear_combination a₁ * hB0 + c₁ * hB1 + a₁ * c₁ * h2
      · linear_combination hB0 + c₁ * h2
  have hZ : ∀ z : K, ∃ Z ∈ C, IsNF Z 0 z 0 := by
    intro z
    obtain ⟨E₁, hE₁, hE₁v⟩ := hE 0 1
    obtain ⟨E₂, hE₂, hE₂v⟩ := hE z 0
    obtain ⟨E₃, hE₃, hE₃v⟩ := hE z 1
    refine ⟨E₃ * E₁ * E₂, C.mul_mem (C.mul_mem hE₃ hE₁) hE₂,
      isNF_congr (isNF_mul (isNF_mul hE₃v hE₁v) hE₂v) (by linear_combination h2) ?_ ?_⟩
    · linear_combination (a₁ * z + c₁ + z) * h2
    · linear_combination z * h2
  have hall : ∀ a b c : K, ∃ M ∈ C, IsNF M a b c := by
    intro a b c
    obtain ⟨E, hEC, hEv⟩ := hE c a
    obtain ⟨Z, hZC, hZv⟩ := hZ (b + (a₁ * c + a * c₁))
    refine ⟨E * Z, C.mul_mem hEC hZC, isNF_congr (isNF_mul hEv hZv) (by ring) ?_ (by ring)⟩
    linear_combination (a₁ * c + a * c₁) * h2
  rw [← SecO1.inf_centralizer_eq hS]
  intro r hr
  have hrL : r ∈ L ⊓ Subgroup.normalizer (V₁ : Set G) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hr
  have hrV := hS.le_normalizer hrL.1
  have hr1 : SecA.conjV (fsuV T I) r hrV ∈
      pCoreOf 2 (autOn (L ⊓ Subgroup.normalizer (V₁ : Set G)) (fsuV T I)) :=
    SecB.autOn_pCoreOf_le _ _ (SecA.conjV_mem_autOn hr hrV)
  rw [SecA.autOn_inf_normalizer hV₁V, hV₁g V₁ hV₁, ← map_stabilizer_eq hf g,
    Ch11.SecS.C11P9A.pCoreOf_map_of_injective _ hψ, ← flag_one_eq,
    show (stabilizer 2 K (flag 2 K 1) : Subgroup (StatedSp 2 K)) = Q2 K 0 from rfl,
    pCoreOf_Q0_eq hK4] at hr1
  obtain ⟨M, hM, hMr⟩ := hr1
  obtain ⟨a, b, c, hMv⟩ := mulVec_of_mem_pCoreOf hK4 hM
  obtain ⟨M', hM'C, hM'v⟩ := hall a b c
  have hMM' : M = M' := eq_of_isNF hMv hM'v
  obtain ⟨w, hw, hwV, hweq⟩ := SecA.mem_autOn_iff.mp
    (show psiSp π g M' ∈ autOn ⁅P, LOf L V₁⁆ (fsuV T I) from hM'C)
  have hwL : w ∈ L := ((perfectCore_le _).trans inf_le_left) (hcommL hw)
  have h1 : w⁻¹ * r ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine ⟨L.mul_mem (L.inv_mem hwL) hrL.1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h5 : SecA.conjV (fsuV T I) w hwV = SecA.conjV (fsuV T I) r hrV := by
      rw [← hweq, ← hMM', hMr]
    have h6 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) h5
    simp only [SecA.conjV_apply_coe] at h6
    calc v * (w⁻¹ * r) = w⁻¹ * (w * v * w⁻¹) * w * (w⁻¹ * r) := by group
      _ = w⁻¹ * (r * v * r⁻¹) * w * (w⁻¹ * r) := by rw [h6]
      _ = w⁻¹ * r * v := by group
  have := Subgroup.mul_mem_sup hw h1
  rwa [mul_inv_cancel_left] at this

end CFSG.Quasithin.Vol2.Ch11.SecF
