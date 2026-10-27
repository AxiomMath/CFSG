module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalGen
import CFSG.LocalAnalysis.StandardType.FS81.OmMonomial
import CFSG.LocalAnalysis.StandardType.FS81.AutMat

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

variable {G : Type} [Group G]

namespace Basis3

variable {k : ℕ}

theorem vec_single_eq_pow (B : Basis3 G k) (i : Fin k) (c : ZMod 3) :
    B.vec (Pi.single i c) = B.b i ^ c.val := by
  have hc : c = 0 ∨ c = 1 ∨ c = 2 := by revert c; decide
  rcases hc with rfl | rfl | rfl
  · rw [Pi.single_zero, B.vec_zero, ZMod.val_zero, pow_zero]
  · rw [B.vec_single, ZMod.val_one, pow_one]
  · have h2 : (Pi.single i (2 : ZMod 3) : Coords k) = Pi.single i 1 + Pi.single i 1 := by
      rw [← Pi.single_add]
      rfl
    rw [h2, B.vec_add, B.vec_single, show (2 : ZMod 3).val = 2 from rfl, pow_two]

end Basis3

variable {n : ℕ} {b₀ : G} {K E : Subgroup G}

private theorem vec_mem_of_zero {B : Basis3 G (n + 1)} (hB : Adapted B b₀ K E)
    {e : Coords (n + 1)} (he : e 0 = 0) : B.vec e ∈ K := by
  refine K.list_prod_mem fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  by_cases hi : i = 0
  · subst hi
    rw [he, ZMod.val_zero, pow_zero]
    exact K.one_mem
  · exact K.pow_mem (hB.2.2 i hi) _

private theorem coord_zero_of_vec_mem (hdisj : Disjoint (Subgroup.zpowers b₀) K)
    {B : Basis3 G (n + 1)} (hB : Adapted B b₀ K E) {e : Coords (n + 1)} (h : B.vec e ∈ K) :
    e 0 = 0 := by
  set e' : Coords (n + 1) := e - Pi.single 0 (e 0) with he'
  have he'0 : e' 0 = 0 := by simp [he']
  have hsplit : B.vec e = b₀ ^ (e 0).val * B.vec e' := by
    rw [← hB.2.1, ← B.vec_single_eq_pow, ← B.vec_add, he']
    congr 1
    abel
  have hpow : b₀ ^ (e 0).val ∈ K := by
    have := K.mul_mem h (K.inv_mem (vec_mem_of_zero hB he'0))
    rwa [hsplit, mul_inv_cancel_right] at this
  have h1 : b₀ ^ (e 0).val = 1 :=
    (Subgroup.disjoint_def.mp hdisj) (Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) _) hpow
  have hord : orderOf b₀ = 3 := by rw [← hB.2.1]; exact B.ord 0
  have h3 : orderOf b₀ ∣ (e 0).val := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at h3
  have hlt : (e 0).val < 3 := ZMod.val_lt (e 0)
  have h0 : (e 0).val = 0 := by omega
  exact (ZMod.val_eq_zero (e 0)).mp h0

private theorem decomposeFin_symm_zero_succ (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    Equiv.Perm.decomposeFin.symm (0, σ) x.succ = (σ x).succ := by
  rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]

private theorem exists_perm_succ {σ : Equiv.Perm (Fin (n + 1))} (h0 : σ 0 = 0) :
    ∃ σ' : Equiv.Perm (Fin n), ∀ x : Fin n, σ x.succ = (σ' x).succ := by
  obtain ⟨⟨p, σ'⟩, hq⟩ : ∃ q, Equiv.Perm.decomposeFin.symm q = σ :=
    ⟨_, Equiv.Perm.decomposeFin.symm_apply_apply σ⟩
  have hp : p = 0 := by rw [← h0, ← hq, Equiv.Perm.decomposeFin_symm_apply_zero]
  subst hp
  exact ⟨σ', fun x => by rw [← hq, decomposeFin_symm_zero_succ]⟩

private theorem spMat_succ_succ {σ : Equiv.Perm (Fin (n + 1))} {σ' : Equiv.Perm (Fin n)}
    (hσ : ∀ x : Fin n, σ x.succ = (σ' x).succ) (s : Fin (n + 1) → ZMod 3) (i j : Fin n) :
    spMat σ s i.succ j.succ = spMat σ' (fun x => s x.succ) i j := by
  simp only [spMat, hσ, Fin.succ_inj]

private theorem spMat_succ_zero {σ : Equiv.Perm (Fin (n + 1))} (h0 : σ 0 = 0)
    (s : Fin (n + 1) → ZMod 3) (i : Fin n) : spMat σ s i.succ 0 = 0 := by
  simp only [spMat, h0, Fin.succ_ne_zero, if_false]

theorem exists_eq_or_eq_inv_of_realized_evenFix0 [Finite G] (hn : 5 ≤ n)
    (hdisj : Disjoint (Subgroup.zpowers b₀) K) {B B' : Basis3 G (n + 1)}
    (hB : Adapted B b₀ K E) (hB' : Adapted B' b₀ K E) (hR : B.realized K ⊆ evenFix0 n)
    (hR' : evenFix0 n ⊆ B'.realized K) (i : Fin n) :
    ∃ j : Fin n, B.b i.succ = B'.b j.succ ∨ B.b i.succ = (B'.b j.succ)⁻¹ := by
  classical
  have hspan : B.span = B'.span := hB.1.trans hB'.1.symm
  let Φ : Coords (n + 1) → Coords (n + 1) := fun e =>
    B'.coords ⟨B.vec e, hspan ▸ B.vec_mem_span e⟩
  have hΦ : ∀ e, B'.vec (Φ e) = B.vec e := fun e => B'.vec_coords _
  have hΦadd : ∀ e e', Φ (e + e') = Φ e + Φ e' := fun e e' =>
    B'.vec_injective (by rw [B'.vec_add, hΦ, hΦ, hΦ, B.vec_add])
  have hΦzero : Φ 0 = 0 := B'.vec_injective (by rw [hΦ, B.vec_zero, B'.vec_zero])
  let Φadd : Coords (n + 1) →+ Coords (n + 1) :=
    { toFun := Φ, map_zero' := hΦzero, map_add' := hΦadd }
  let Φlin : Coords (n + 1) →ₗ[ZMod 3] Coords (n + 1) :=
    { toFun := Φ
      map_add' := hΦadd
      map_smul' := fun c e => by
        rw [RingHom.id_apply, ← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul,
          Nat.cast_smul_eq_nsmul]
        exact map_nsmul Φadd c.val e }
  set P8 : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3) := LinearMap.toMatrix' Φlin with hP8def
  have hP8 : ∀ e, P8 *ᵥ e = Φ e := fun e => LinearMap.toMatrix'_mulVec Φlin e
  have hP8col : ∀ r j, Φ (Pi.single j 1) r = P8 r j := fun r j => by
    rw [← hP8, Matrix.mulVec_single_one]
    rfl
  have hΦ0 : Φ (Pi.single 0 1) = Pi.single 0 1 := B'.vec_injective (by
    rw [hΦ, B.vec_single, B'.vec_single, hB.2.1, hB'.2.1])
  have hP8r0 : ∀ j : Fin n, P8 0 j.succ = 0 := fun j => by
    rw [← hP8col]
    refine coord_zero_of_vec_mem hdisj hB' ?_
    rw [hΦ, B.vec_single]
    exact hB.2.2 j.succ (Fin.succ_ne_zero j)
  have hP8c0 : ∀ r : Fin n, P8 r.succ 0 = 0 := fun r => by
    rw [← hP8col, hΦ0, Pi.single_eq_of_ne (Fin.succ_ne_zero r)]
  set P : Matrix (Fin n) (Fin n) (ZMod 3) := P8.submatrix Fin.succ Fin.succ with hPdef
  have hconj : ∀ (σ : Equiv.Perm (Fin n)) (s : Fin n → ZMod 3), IsSign s → ∏ i, s i = 1 →
      ∃ (σ' : Equiv.Perm (Fin n)) (s' : Fin n → ZMod 3), IsSign s' ∧ ∏ i, s' i = 1 ∧
        spMat σ s * P = P * spMat σ' s' := by
    intro σ s hs hprod
    set σ₈ : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm (0, σ) with hσ₈
    set s₈ : Fin (n + 1) → ZMod 3 := Fin.cons 1 s with hs₈
    have hσ₈0 : σ₈ 0 = 0 := Equiv.Perm.decomposeFin_symm_apply_zero _ _
    have hσ₈s : ∀ x : Fin n, σ₈ x.succ = (σ x).succ := decomposeFin_symm_zero_succ σ
    have hS : spMat σ₈ s₈ ∈ evenFix0 n := by
      refine ⟨σ₈, s₈, fun x => ?_, ⟨hσ₈0, rfl, ?_⟩, rfl⟩
      · refine Fin.cases (Or.inl rfl) (fun y => ?_) x
        simpa [hs₈] using hs y
      · simpa [hs₈] using hprod
    obtain ⟨g, hgK, hg'⟩ := hR' hS
    have hgN : g ∈ Subgroup.normalizer (B.span : Set G) := by
      rw [hspan]
      exact B'.mem_normalizer_of_acts hg'
    obtain ⟨M, hM⟩ := B.exists_acts hgN
    obtain ⟨σ₈', s₈', hs₈', ⟨h0, -, hprod'⟩, rfl⟩ := hR ⟨g, hgK, hM⟩
    obtain ⟨σ', hσ'⟩ := exists_perm_succ h0
    refine ⟨σ', fun x => s₈' x.succ, fun x => hs₈' x.succ, hprod', ?_⟩
    have hvec : ∀ e, spMat σ₈ s₈ *ᵥ (P8 *ᵥ e) = P8 *ᵥ (spMat σ₈' s₈' *ᵥ e) := fun e =>
      B'.vec_injective (by
        rw [← B'.acts_vec hg', hP8, hP8, hΦ, hΦ, B.acts_vec hM])
    have hmat : spMat σ₈ s₈ * P8 = P8 * spMat σ₈' s₈' := by
      ext r c
      have h := congrFun (hvec (Pi.single c 1)) r
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
        Matrix.mulVec_single_one] at h
    ext r c
    have h := congrFun (congrFun hmat r.succ) c.succ
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ,
      spMat_succ_zero hσ₈0, hP8c0, zero_mul, zero_mul, zero_add, zero_add] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simpa only [spMat_succ_succ hσ₈s, spMat_succ_succ hσ', hPdef, Matrix.submatrix_apply,
      show (fun x : Fin n => s₈ x.succ) = s from rfl] using h
  have hinj : Function.Injective P.mulVec := by
    intro x y hxy
    have hcons : ∀ z : Fin n → ZMod 3, P8 *ᵥ (Fin.cons 0 z) = Fin.cons 0 (P *ᵥ z) := by
      intro z
      funext r
      refine Fin.cases ?_ (fun r => ?_) r
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hP8r0]
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hP8c0, hPdef]
    have h1 : B.vec (Fin.cons 0 x) = B.vec (Fin.cons 0 y) := by
      rw [← hΦ, ← hΦ, ← hP8, ← hP8, hcons, hcons, hxy]
    have h2 := B.vec_injective h1
    funext r
    simpa using congrFun h2 r.succ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨σ, s, hs, hPσ⟩ := monomial_of_conj_even hn P hdet hconj
  refine ⟨σ i, ?_⟩
  have hcol : Φ (Pi.single i.succ 1) = Pi.single (σ i).succ (s i) := by
    funext r
    refine Fin.cases ?_ (fun r => ?_) r
    · rw [hP8col, hP8r0, Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm]
    · rw [hP8col]
      have h := congrFun (congrFun hPσ r) i
      simp only [hPdef, Matrix.submatrix_apply] at h
      rw [h, spMat, Pi.single_apply]
      simp only [Fin.succ_inj]
  have hb : B.b i.succ = B'.b (σ i).succ ^ (s i).val := by
    rw [← B.vec_single, ← hΦ, hcol, B'.vec_single_eq_pow]
  rcases hs i with h | h
  · left
    rw [hb, h, ZMod.val_one, pow_one]
  · right
    have hord := pow_orderOf_eq_one (B'.b (σ i).succ)
    rw [B'.ord (σ i).succ] at hord
    rw [hb, h, show (-1 : ZMod 3).val = 2 from rfl, eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hord

end CFSG.StandardType.FrameRoute.FS81
