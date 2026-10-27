module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeAIrred

public section

namespace CFSG.StandardType

open Matrix Multiplicative
open scoped MatrixGroups

namespace GGSecFiveBPermSpLFrame

variable {G : Type} [Group G] {p n r f : ℕ} {Bs L : Subgroup G}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
  {σ : SL(r + 2, GaloisField 2 f) →* G} {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}

private theorem exists_perm_of_mem {a : MulAut (Fin n → Multiplicative (ZMod p))}
    (ha : a ∈ aPermutationFull n p) : ∃ τ : Equiv.Perm (Fin n), a = SpCoord.permAut τ := by
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨i, j, -, rfl⟩ := ha
    exact ⟨Equiv.swap i j, rfl⟩
  | one => exact ⟨1, by ext g k; rfl⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨σ, rfl⟩ := iha
    obtain ⟨τ, rfl⟩ := ihb
    exact ⟨σ * τ, by ext g k; rfl⟩
  | inv a _ iha =>
    obtain ⟨σ, rfl⟩ := iha
    exact ⟨σ⁻¹, by ext g k; rfl⟩

private theorem permMatrix_conj_diagonal {F : Type} [Field F] {d : ℕ} (τ : Equiv.Perm (Fin d))
    (t : Fin d → F) :
    τ.permMatrix F * diagonal t * τ⁻¹.permMatrix F = diagonal (t ∘ τ) := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix,
    Equiv.Perm.inv_def, Equiv.symm_symm]
  exact submatrix_diagonal_equiv t τ

private theorem transvection_coeff_eq {F : Type} [Field F] {d : ℕ} {ψ : SL(d, F) →* G}
    (hψ : ψ.ker ≤ Subgroup.center SL(d, F)) {k l : Fin d} (hkl : k ≠ l) {a b : F}
    (h : ψ (Matrix.SpecialLinearGroup.transvection hkl a) =
      ψ (Matrix.SpecialLinearGroup.transvection hkl b)) : a = b := by
  have hmem : Matrix.SpecialLinearGroup.transvection hkl (-a + b) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, Matrix.SpecialLinearGroup.transvection_add, map_mul,
      ← Matrix.SpecialLinearGroup.transvection_inv, map_inv, ← h, inv_mul_cancel]
  have h0 := (Matrix.SpecialLinearGroup.transvection_mem_center_iff hkl _).mp (hψ hmem)
  rw [neg_add_eq_zero] at h0
  exact h0

theorem permSL_swap_normalizer [Fact p.Prime] (hLF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ p = 1 → x ∈ Bs)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hr : 1 ≤ r) {i j : Fin (r + 2)} (hij : i ≠ j) :
    ∃ hg : σ (TypeA.permSL (Equiv.swap i j)) ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π i) (π j)) := by
  classical
  set F := GaloisField 2 f
  set τ : Equiv.Perm (Fin (r + 2)) := Equiv.swap i j with hτ
  set P : SL(r + 2, F) := TypeA.permSL τ with hP
  set g : G := σ P with hgdef
  have hPinv : P⁻¹ = P := by rw [hP, TypeA.permSL_inv, hτ, Equiv.swap_inv]
  have hPP : P * P = 1 := by
    calc P * P = P * P⁻¹ := by rw [hPinv]
      _ = 1 := mul_inv_cancel P
  have hginv : g⁻¹ = g := by rw [hgdef, ← map_inv, hPinv]
  have hgg : g * g = 1 := by rw [hgdef, ← map_mul, hPP, map_one]
  set e : ↥Bs → Fin (r + 2) → Fˣ := fun b m => χ (eta b (π (τ m)) / eta b (π m)) with he
  set Δ : ↥Bs → SL(r + 2, F) :=
    fun b => P * InnerDiagA.conjSL (InnerDiagA.diagGL fun m => χ (eta b (π m))) P with hΔdef
  have hΔ : ∀ b, ((Δ b : SL(r + 2, F)) : Matrix (Fin (r + 2)) (Fin (r + 2)) F) =
      diagonal fun m => (e b m : F) := by
    intro b
    simp only [hΔdef, Matrix.SpecialLinearGroup.coe_mul, InnerDiagA.coe_conjSL,
      InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL_inv, hP, TypeA.coe_permSL]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    have h1 : τ.permMatrix F = τ⁻¹.permMatrix F := by rw [hτ, Equiv.swap_inv]
    conv_lhs => rw [show τ.permMatrix F * diagonal (fun k => ((χ (eta b (π k)) : Fˣ) : F)) *
        τ.permMatrix F = τ.permMatrix F * diagonal (fun k => ((χ (eta b (π k)) : Fˣ) : F)) *
        τ⁻¹.permMatrix F by rw [← h1]]
    rw [permMatrix_conj_diagonal, diagonal_mul_diagonal]
    congr 1
    funext m
    simp only [Function.comp_apply, he, map_div, Units.val_div_eq_div_val]
    rw [div_eq_mul_inv, Units.val_inv_eq_inv_val]
  have hΔconj : ∀ b (u : SL(r + 2, F)),
      Δ b * u * (Δ b)⁻¹ = InnerDiagA.conjSL (InnerDiagA.diagGL (e b)) u := by
    intro b u
    have hinv : (((Δ b)⁻¹ : SL(r + 2, F)) : Matrix (Fin (r + 2)) (Fin (r + 2)) F) =
        (((InnerDiagA.diagGL (e b))⁻¹ : GL (Fin (r + 2)) F) :
          Matrix (Fin (r + 2)) (Fin (r + 2)) F) := by
      have h1 : (((Δ b)⁻¹ : SL(r + 2, F)) : Matrix (Fin (r + 2)) (Fin (r + 2)) F) *
          ((Δ b : SL(r + 2, F)) : Matrix (Fin (r + 2)) (Fin (r + 2)) F) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      have h2 : ((InnerDiagA.diagGL (e b) : GL (Fin (r + 2)) F) :
          Matrix (Fin (r + 2)) (Fin (r + 2)) F) *
          (((InnerDiagA.diagGL (e b))⁻¹ : GL (Fin (r + 2)) F) :
            Matrix (Fin (r + 2)) (Fin (r + 2)) F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hΔ, ← InnerDiagA.coe_diagGL] at h1
      calc (((Δ b)⁻¹ : SL(r + 2, F)) : Matrix (Fin (r + 2)) (Fin (r + 2)) F)
          = (((Δ b)⁻¹ : SL(r + 2, F)) : Matrix (Fin (r + 2)) (Fin (r + 2)) F) *
              (((InnerDiagA.diagGL (e b) : GL (Fin (r + 2)) F) :
                Matrix (Fin (r + 2)) (Fin (r + 2)) F) *
              (((InnerDiagA.diagGL (e b))⁻¹ : GL (Fin (r + 2)) F) :
                Matrix (Fin (r + 2)) (Fin (r + 2)) F)) := by rw [h2, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    apply Subtype.ext
    rw [InnerDiagA.coe_conjSL, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hinv, hΔ, InnerDiagA.coe_diagGL]
  have hconj : ∀ b : ↥Bs, g * b * g⁻¹ = σ (Δ b) * b := by
    intro b
    have h := hLF.2.2.2 b P
    calc g * b * g⁻¹ = g * ((b : G) * g * (b : G)⁻¹) * b := by rw [hginv]; group
      _ = σ (Δ b) * b := by rw [hgdef, h, ← map_mul]
  have hΔB : ∀ b : ↥Bs, σ (Δ b) ∈ Bs := by
    intro b
    refine hBs _ ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have h := hLF.2.2.2 ⟨c, hc⟩ (Δ b)
      have hcomm : InnerDiagA.conjSL (InnerDiagA.diagGL fun m => χ (eta ⟨c, hc⟩ (π m))) (Δ b) =
          Δ b := by
        apply Subtype.ext
        rw [InnerDiagA.coe_conjSL, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL_inv, hΔ,
          diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext m
        rw [mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      calc c * σ (Δ b) = (c * σ (Δ b) * c⁻¹) * c := by group
        _ = σ (Δ b) * c := by rw [show c * σ (Δ b) * c⁻¹ = σ (Δ b) from h.trans (by rw [hcomm])]
    · rw [← map_pow]
      have hp : Δ b ^ p = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow, hΔ, diagonal_pow, Matrix.SpecialLinearGroup.coe_one,
          ← diagonal_one]
        congr 1
        funext m
        rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val, ← map_pow]
        have hz : (eta b (π (τ m)) / eta b (π m)) ^ p = 1 := by
          apply toAdd.injective
          rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
        rw [hz, map_one, Units.val_one]
      rw [hp, map_one]
  have hgB : ∀ b ∈ Bs, g * b * g⁻¹ ∈ Bs := fun b hb => by
    rw [show b = ((⟨b, hb⟩ : ↥Bs) : G) from rfl, hconj]
    exact Bs.mul_mem (hΔB _) hb
  have hgN : g ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨hgB b, fun h => ?_⟩
    have h1 := hgB _ h
    have e1 : g * (g * b * g⁻¹) * g⁻¹ = b := by
      rw [hginv]
      calc g * (g * b * g) * g = (g * g) * b * (g * g) := by group
        _ = b := by rw [hgg, one_mul, mul_one]
    rwa [e1] at h1
  refine ⟨hgN, ?_⟩
  have hcoordΔ : ∀ b : ↥Bs, ∃ c₀ : ZMod p, ∀ m : Fin (r + 2),
      toAdd (eta ⟨σ (Δ b), hΔB b⟩ (π m)) =
        c₀ + (toAdd (eta b (π (τ m))) - toAdd (eta b (π m))) := by
    intro b
    set c : ↥Bs := ⟨σ (Δ b), hΔB b⟩ with hc
    have key : ∀ k l : Fin (r + 2), k ≠ l →
        toAdd (eta c (π k)) - toAdd (eta c (π l)) =
          (toAdd (eta b (π (τ k))) - toAdd (eta b (π k))) -
            (toAdd (eta b (π (τ l))) - toAdd (eta b (π l))) := by
      intro k l hkl
      have h1 := hLF.2.2.2 c (Matrix.SpecialLinearGroup.transvection hkl 1)
      have h2 : (c : G) * σ (Matrix.SpecialLinearGroup.transvection hkl 1) * (c : G)⁻¹ =
          σ (Δ b * Matrix.SpecialLinearGroup.transvection hkl 1 * (Δ b)⁻¹) := by
        show σ (Δ b) * σ (Matrix.SpecialLinearGroup.transvection hkl 1) * (σ (Δ b))⁻¹ = _
        rw [← map_inv σ, ← map_mul, ← map_mul]
      rw [h2, hΔconj, InnerDiagA.conjSL_diagGL_transvection,
        InnerDiagA.conjSL_diagGL_transvection] at h1
      have h3 := transvection_coeff_eq hLF.1 hkl h1
      simp only [mul_one] at h3
      have h4 : e b k * (e b l)⁻¹ = χ (eta c (π k)) * (χ (eta c (π l)))⁻¹ := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        exact h3
      rw [he] at h4
      simp only [← map_inv, ← map_mul] at h4
      have h5 := hLF.2.2.1 h4
      have h6 := congrArg toAdd h5
      simp only [toAdd_mul, toAdd_inv, toAdd_div] at h6
      linear_combination -h6
    refine ⟨toAdd (eta c (π i)) - (toAdd (eta b (π (τ i))) - toAdd (eta b (π i))), fun m => ?_⟩
    by_cases hmi : m = i
    · subst hmi
      ring
    · have := key m i hmi
      linear_combination this
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Equiv.Perm (Fin n), MulAut.congr eta (ggConjAut Bs hgN) =
      SpCoord.permAut ρ := by
    have hgL : g ∈ L := hLF.2.1 ▸ ⟨P, rfl⟩
    have hmem : MulAut.congr eta (ggConjAut Bs hgN) ∈ aPermutationFull n p := by
      rw [← hA]
      exact Subgroup.mem_map.mpr ⟨_, ggConjAut_mem_ggAutomizer hgL hgN, rfl⟩
    exact exists_perm_of_mem hmem
  have hρapply : ∀ (b : ↥Bs) (y : Fin n), eta (ggConjAut Bs hgN b) y = eta b (ρ⁻¹ y) := by
    intro b y
    have h := congrArg (fun φ : MulAut (Fin n → Multiplicative (ZMod p)) => φ (eta b) y) hρ
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
    rw [h, SpCoord.permAut_apply]
    rfl
  have hn3 : 3 ≤ n := by
    have := Fintype.card_congr π
    simp only [Fintype.card_fin] at this
    omega
  have hρeq : ρ = Equiv.swap (π i) (π j) := by
    ext x
    set b : ↥Bs := eta.symm (Pi.mulSingle x (ofAdd 1)) with hb
    have hηb : ∀ y, toAdd (eta b y) = if y = x then 1 else 0 := by
      intro y
      rw [hb, MulEquiv.apply_symm_apply, Pi.mulSingle_apply]
      split_ifs <;> rfl
    obtain ⟨c₀, hc₀⟩ := hcoordΔ b
    have hgb : ∀ y, toAdd (eta (ggConjAut Bs hgN b) y) =
        c₀ + toAdd (eta b (π (τ (π.symm y)))) := by
      intro y
      have e1 : (ggConjAut Bs hgN b : ↥Bs) = ⟨σ (Δ b), hΔB b⟩ * b :=
        Subtype.ext (by rw [ggConjAut_apply, hconj]; rfl)
      rw [e1, map_mul, Pi.mul_apply, toAdd_mul, ← π.apply_symm_apply y, hc₀ (π.symm y),
        π.apply_symm_apply]
      ring
    have hcomp : ∀ y, (if y = ρ x then (1 : ZMod p) else 0) =
        c₀ + if y = π (τ (π.symm x)) then 1 else 0 := by
      intro y
      have h1 := hgb y
      rw [hρapply, hηb, hηb] at h1
      have e2 : (ρ⁻¹ y = x) ↔ (y = ρ x) := by
        constructor
        · rintro rfl
          simp
        · rintro rfl
          simp
      have e3 : (π (τ (π.symm y)) = x) ↔ (y = π (τ (π.symm x))) := by
        constructor
        · intro h
          rw [← h, π.symm_apply_apply, hτ, Equiv.swap_apply_self, π.apply_symm_apply]
        · intro h
          rw [h, π.symm_apply_apply, hτ, Equiv.swap_apply_self, π.apply_symm_apply]
      simp only [e2, e3] at h1
      exact h1
    obtain ⟨y₀, -, hy₀⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({ρ x, π (τ (π.symm x))} : Finset (Fin n))) (t := Finset.univ)
      (by
        rw [Finset.card_univ, Fintype.card_fin]
        exact lt_of_le_of_lt (Finset.card_le_two) (by omega))
    have hy₀1 : y₀ ≠ ρ x := fun h => hy₀ (by simp [h])
    have hy₀2 : y₀ ≠ π (τ (π.symm x)) := fun h => hy₀ (by simp [h])
    have hc0 : c₀ = 0 := by
      have := hcomp y₀
      rw [if_neg hy₀1, if_neg hy₀2, add_zero] at this
      exact this.symm
    have h1 := hcomp (ρ x)
    rw [if_pos rfl, hc0, zero_add] at h1
    have hρx : ρ x = π (τ (π.symm x)) := by
      by_contra h
      rw [if_neg h] at h1
      exact one_ne_zero h1
    rw [hρx, hτ, Equiv.swap_apply_def, Equiv.swap_apply_def]
    by_cases hxi : x = π i
    · subst hxi
      simp
    · by_cases hxj : x = π j
      · subst hxj
        simp [hij.symm]
      · have h1' : π.symm x ≠ i := fun h => hxi (by rw [← h, π.apply_symm_apply])
        have h2' : π.symm x ≠ j := fun h => hxj (by rw [← h, π.apply_symm_apply])
        simp [h1', h2', hxi, hxj]
  rw [hρ, hρeq]

end GGSecFiveBPermSpLFrame

end CFSG.StandardType

end
