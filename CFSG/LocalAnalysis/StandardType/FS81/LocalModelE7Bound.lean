module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalModelE7Torus
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthTorus
public import CFSG.LocalAnalysis.StandardType.FS81.RealizedNormalizer
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvOrth

public section

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.StandardType.FrameRoute.FS81

namespace GGTorusTorWit

variable {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}

noncomputable def e7Tau (w : GGTorusTorWit 3 7 L' A)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)) :
    (Fin 7 → Multiplicative (ZMod 3)) →* L' :=
  (w.coordHom hcomm).comp ((matVecHom e7LocalR).comp
    (MulEquiv.piMultiplicative (fun _ : Fin 7 => ZMod 3)).symm.toMonoidHom)

private theorem e7Tau_apply (w : GGTorusTorWit 3 7 L' A)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ))
    (v : Fin 7 → Multiplicative (ZMod 3)) :
    w.e7Tau hcomm v =
      w.coordHom hcomm (Multiplicative.ofAdd (e7LocalR *ᵥ fun i => (v i).toAdd)) := by
  rw [e7Tau, MonoidHom.comp_apply, MonoidHom.comp_apply]
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.piMultiplicative_symm_apply, matVecHom_ofAdd]

private theorem e7Tau_mulSingle (w : GGTorusTorWit 3 7 L' A)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)) (j : Fin 7) :
    w.e7Tau hcomm (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))) =
      w.coordHom hcomm (Multiplicative.ofAdd (e7LocalR *ᵥ Pi.single j 1)) := by
  rw [e7Tau_apply]
  have hvec : (fun i : Fin 7 => Multiplicative.toAdd
      ((Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3)) :
        Fin 7 → Multiplicative (ZMod 3)) i)) = Pi.single j 1 := by
    funext i
    by_cases h : i = j <;> simp [Pi.mulSingle_apply, Pi.single_apply, h]
  rw [hvec]

private theorem matVecHom_e7LocalR_surjective : Function.Surjective (matVecHom e7LocalR) := by
  intro v
  have hv : v = Multiplicative.ofAdd (Multiplicative.toAdd v) := (ofAdd_toAdd v).symm
  refine ⟨matVecHom e7LocalRinv v, ?_⟩
  rw [hv, matVecHom_ofAdd, matVecHom_ofAdd, Matrix.mulVec_mulVec, e7LocalR_mul_Rinv,
    Matrix.one_mulVec]

private theorem matVecHom_e7LocalR_injective : Function.Injective (matVecHom e7LocalR) := by
  have hleft : ∀ x, matVecHom e7LocalRinv (matVecHom e7LocalR x) = x := by
    intro x
    have hx : x = Multiplicative.ofAdd (Multiplicative.toAdd x) := (ofAdd_toAdd x).symm
    rw [hx, matVecHom_ofAdd, matVecHom_ofAdd, Matrix.mulVec_mulVec, e7LocalRinv_mul_R,
      Matrix.one_mulVec]
  intro v v' h
  have h2 := congrArg (matVecHom e7LocalRinv) h
  rwa [hleft v, hleft v'] at h2

theorem e7Tau_range (w : GGTorusTorWit 3 7 L' A)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)) :
    (w.e7Tau hcomm).range = ⨆ k, (w.cor k).range := by
  have htop : (MulEquiv.piMultiplicative (fun _ : Fin 7 => ZMod 3)).symm.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (MulEquiv.surjective _)
  rw [e7Tau, MonoidHom.range_comp, MonoidHom.range_comp, htop, Subgroup.map_top,
    MonoidHom.range_eq_top.mpr matVecHom_e7LocalR_surjective, Subgroup.map_top, coordHom_range]

theorem e7Tau_injective (w : GGTorusTorWit 3 7 L' A)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ))
    (hcard : Nat.card ↥(⨆ k, (w.cor k).range) = 3 ^ 7) :
    Function.Injective (w.e7Tau hcomm) := by
  have hdom : Nat.card (Multiplicative (Fin 7 → ZMod 3)) = 3 ^ 7 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hcinj : Function.Injective (w.coordHom hcomm) := by
    have hker : Nat.card ↥(w.coordHom hcomm).ker = 1 := by
      have h := Subgroup.card_ker_mul_card_range (w.coordHom hcomm)
      rw [coordHom_range, hcard, hdom] at h
      exact Nat.eq_of_mul_eq_mul_right (m := 3 ^ 7) (k := 1) (by norm_num)
        (by rw [one_mul]; exact h)
    have hbot : (w.coordHom hcomm).ker = ⊥ :=
      (Subgroup.card_eq_one (H := (w.coordHom hcomm).ker)).mp hker
    exact (MonoidHom.ker_eq_bot_iff (w.coordHom hcomm)).mp hbot
  exact hcinj.comp (matVecHom_e7LocalR_injective.comp
    (MulEquiv.injective (MulEquiv.piMultiplicative (fun _ : Fin 7 => ZMod 3)).symm))

end GGTorusTorWit

namespace FrameRoute.FS81

open CFSG.StandardType

variable {G : Type} [Group G] {k : ℕ}

namespace Basis3

private theorem vec_torusBasis {n : ℕ} {b₀ : G} {K : Subgroup G} {L : Type} [Group L]
    (φ : ↥K ≃* L) {τ : (Fin n → Multiplicative (ZMod 3)) →* L}
    (hτ : Function.Injective τ) (hb₀ : orderOf b₀ = 3)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hdisj : Disjoint (Subgroup.zpowers b₀) K) (c : Coords (n + 1)) :
    (torusBasis φ hτ hb₀ hKC hdisj).vec c =
      b₀ ^ (c 0).val * (φ.symm (τ (fun i => Multiplicative.ofAdd (c i.succ))) : G) := by
  classical
  let F : (Fin n → Multiplicative (ZMod 3)) →* G :=
    (Subgroup.subtype K).comp (φ.symm.toMonoidHom.comp τ)
  have hF : ∀ x, F x = (φ.symm (τ x) : G) := fun _ => rfl
  rw [Basis3.vec, List.ofFn_succ, List.prod_cons, torusBasis_b_zero]
  congr 1
  have h1 : (List.ofFn fun i : Fin n =>
        (torusBasis φ hτ hb₀ hKC hdisj).b i.succ ^ (c i.succ).val) =
      (List.ofFn fun i : Fin n =>
        (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3)) :
          Fin n → Multiplicative (ZMod 3)) ^ (c i.succ).val).map F := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply, torusBasis_b_succ, map_pow]
    rfl
  rw [h1, ← map_list_prod]
  have h2 : (List.ofFn fun i : Fin n =>
        (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3)) :
          Fin n → Multiplicative (ZMod 3)) ^ (c i.succ).val).prod =
      fun i => Multiplicative.ofAdd (c i.succ) := by
    rw [Fin.prod_ofFn, ← Finset.univ_prod_mulSingle
      (fun i : Fin n => Multiplicative.ofAdd (c i.succ))]
    exact Finset.prod_congr rfl fun i _ =>
      (SpCoord.mulSingle_ofAdd_eq_pow i (c i.succ)).symm
  rw [h2, hF]

end Basis3

section E7Torus

open CFSG.StandardType
open CFSG.StandardType.GGTorusTorWit

variable {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
variable {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
variable {w : GGTorusTorWit 3 7 L' A}
variable {hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)}

private theorem e7LocalR_mul_conj (S : Matrix (Fin 7) (Fin 7) (ZMod 3)) :
    e7LocalR * (e7LocalRinv * S * e7LocalR) = S * e7LocalR := by
  rw [show e7LocalRinv * S * e7LocalR = e7LocalRinv * (S * e7LocalR) from
    Matrix.mul_assoc _ _ _]
  rw [← Matrix.mul_assoc, e7LocalR_mul_Rinv, Matrix.one_mul]

private theorem e7LocalR_mulVec_conj (S : Matrix (Fin 7) (Fin 7) (ZMod 3)) (j : Fin 7) :
    Matrix.mulVec e7LocalR (Matrix.col (e7LocalRinv * S * e7LocalR) j) =
      Matrix.mulVec S (Matrix.mulVec e7LocalR (Pi.single j 1)) := by
  have hmv : Matrix.col (e7LocalRinv * S * e7LocalR) j =
      Matrix.mulVec (e7LocalRinv * S * e7LocalR) (Pi.single j 1) :=
    (Matrix.mulVec_single_one _ j).symm
  calc Matrix.mulVec e7LocalR (Matrix.col (e7LocalRinv * S * e7LocalR) j)
      = Matrix.mulVec e7LocalR
          (Matrix.mulVec (e7LocalRinv * S * e7LocalR) (Pi.single j 1)) := by rw [hmv]
    _ = Matrix.mulVec (e7LocalR * (e7LocalRinv * S * e7LocalR)) (Pi.single j 1) :=
        Matrix.mulVec_mulVec _ _ _
    _ = Matrix.mulVec (S * e7LocalR) (Pi.single j 1) := by rw [e7LocalR_mul_conj]
    _ = Matrix.mulVec S (Matrix.mulVec e7LocalR (Pi.single j 1)) :=
        (Matrix.mulVec_mulVec _ _ _).symm


private theorem e7Tau_e7LocalGen (k j' : Fin 7) :
    w.e7Tau hcomm (fun i => Multiplicative.ofAdd (e7LocalGen k i.succ j'.succ)) =
      w.coordHom hcomm (Multiplicative.ofAdd
        (e7CorootRefl k *ᵥ (e7LocalR *ᵥ Pi.single j' 1))) := by
  rw [show (fun i => Multiplicative.ofAdd (e7LocalGen k i.succ j'.succ)) =
      (fun i => Multiplicative.ofAdd ((e7LocalRinv * e7CorootRefl k * e7LocalR) i j')) from rfl]
  rw [e7Tau_apply]
  exact congrArg (fun u => w.coordHom hcomm (Multiplicative.ofAdd u))
    (e7LocalR_mulVec_conj (e7CorootRefl k) j')

private theorem vec_e7LocalGen_succ {e : ↥K ≃* L'} {hτ : Function.Injective (w.e7Tau hcomm)}
    {hb₀ : orderOf b₀ = 3} {hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)}
    {hdisj : Disjoint (Subgroup.zpowers b₀) K} (k j' : Fin 7) :
    (torusBasis e hτ hb₀ hKC hdisj).vec (fun i => e7LocalGen k i j'.succ) =
      (e.symm (w.coordHom hcomm (Multiplicative.ofAdd
        (e7CorootRefl k *ᵥ (e7LocalR *ᵥ Pi.single j' 1)))) : G) := by
  rw [show (torusBasis e hτ hb₀ hKC hdisj).vec (fun i => e7LocalGen k i j'.succ) =
      b₀ ^ (e7LocalGen k 0 j'.succ).val *
        (e.symm (w.e7Tau hcomm (fun i => Multiplicative.ofAdd
          (e7LocalGen k i.succ j'.succ))) : G) from by
    rw [Basis3.vec_torusBasis]]
  rw [e7Tau_e7LocalGen]
  have hc0 : e7LocalGen k 0 j'.succ = 0 := rfl
  rw [hc0, ZMod.val_zero, pow_zero, one_mul]

private theorem exists_inv_mem_closure {M : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hM : M ∈ Submonoid.closure (Set.range e7LocalGen)) :
    ∃ M' ∈ Submonoid.closure (Set.range e7LocalGen), M * M' = 1 ∧ M' * M = 1 := by
  refine Submonoid.closure_induction (s := Set.range e7LocalGen)
    (motive := fun M _ => ∃ M' ∈ Submonoid.closure (Set.range e7LocalGen),
      M * M' = 1 ∧ M' * M = 1) ?_ ?_ ?_ hM
  · rintro M ⟨k, rfl⟩
    exact ⟨e7LocalGen k, Submonoid.subset_closure ⟨k, rfl⟩, e7LocalGen_mul_self k,
      e7LocalGen_mul_self k⟩
  · exact ⟨1, Submonoid.one_mem _, mul_one 1, one_mul 1⟩
  · rintro M N _ _ ⟨M', hM', hMM', hM'M⟩ ⟨N', hN', hNN', hN'N⟩
    refine ⟨N' * M', Submonoid.mul_mem _ hN' hM', ?_, ?_⟩
    · calc (M * N) * (N' * M') = M * (N * (N' * M')) := mul_assoc _ _ _
        _ = M * ((N * N') * M') := by rw [mul_assoc]
        _ = M * (1 * M') := by rw [hNN']
        _ = M * M' := by rw [one_mul]
        _ = 1 := hMM'
    · calc (N' * M') * (M * N) = N' * (M' * (M * N)) := mul_assoc _ _ _
        _ = N' * ((M' * M) * N) := by rw [mul_assoc]
        _ = N' * (1 * N) := by rw [hM'M]
        _ = N' * N := by rw [one_mul]
        _ = 1 := hN'N

theorem e7LocalGen_acts (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hZ : Subgroup.center L' = ⊥)
    {e : ↥K ≃* L'} {hτ : Function.Injective (w.e7Tau hcomm)}
    {hb₀ : orderOf b₀ = 3} {hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)}
    {hdisj : Disjoint (Subgroup.zpowers b₀) K} (k : Fin 7) :
    (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm (w.n k) : ↥K) : G) (e7LocalGen k) := by
  intro j
  cases j using Fin.cases with
  | zero =>
    have hcol : (fun i : Fin 8 => e7LocalGen k i 0) = Pi.single (0 : Fin 8) 1 := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i' => rfl
    rw [hcol, Basis3.vec_single, torusBasis_b_zero]
    have hx := Subgroup.mem_centralizer_singleton_iff.mp (hKC (e.symm (w.n k)).2)
    rw [hx]
    group
  | succ j' =>
    rw [torusBasis_b_succ, vec_e7LocalGen_succ]
    have hgen : w.n k * w.e7Tau hcomm (Pi.mulSingle j' (Multiplicative.ofAdd (1 : ZMod 3))) *
        (w.n k)⁻¹ =
        w.coordHom hcomm (Multiplicative.ofAdd
          (e7CorootRefl k *ᵥ (e7LocalR *ᵥ Pi.single j' 1))) := by
      rw [e7Tau_mulSingle, coordHom_conj w hw hZ]
    have hx : ((e.symm (w.n k) : ↥K) : G) *
        ((e.symm (w.e7Tau hcomm (Pi.mulSingle j' (Multiplicative.ofAdd (1 : ZMod 3)))) : ↥K) : G) *
        (((e.symm (w.n k) : ↥K) : G))⁻¹ =
        (e.symm (w.n k * w.e7Tau hcomm (Pi.mulSingle j' (Multiplicative.ofAdd (1 : ZMod 3))) *
          (w.n k)⁻¹) : G) := by
      have hxK : e.symm (w.n k) *
          e.symm (w.e7Tau hcomm (Pi.mulSingle j' (Multiplicative.ofAdd (1 : ZMod 3)))) *
          (e.symm (w.n k))⁻¹ =
          e.symm (w.n k * w.e7Tau hcomm (Pi.mulSingle j' (Multiplicative.ofAdd (1 : ZMod 3))) *
            (w.n k)⁻¹) := by
        rw [map_mul, map_inv, map_mul]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        congrArg (fun z : ↥K => (z : G)) hxK
    rw [hx, hgen]


theorem exists_acts_of_mem_closure (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hZ : Subgroup.center L' = ⊥)
    {e : ↥K ≃* L'} {hτ : Function.Injective (w.e7Tau hcomm)}
    {hb₀ : orderOf b₀ = 3} {hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)}
    {hdisj : Disjoint (Subgroup.zpowers b₀) K} :
    ∀ y ∈ Subgroup.closure (Set.range w.n),
      ∃ M ∈ Submonoid.closure (Set.range e7LocalGen),
        (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y : ↥K) : G) M := by
  intro y hy
  refine Subgroup.closure_induction (k := Set.range w.n) (p := fun y _ =>
    ∃ M ∈ Submonoid.closure (Set.range e7LocalGen),
      (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y : ↥K) : G) M) ?_ ?_ ?_ ?_ hy
  · rintro y ⟨k, rfl⟩
    exact ⟨e7LocalGen k, Submonoid.subset_closure ⟨k, rfl⟩, e7LocalGen_acts hw hZ k⟩
  · exact ⟨1, Submonoid.one_mem _,
      by simpa using Basis3.acts_one (torusBasis e hτ hb₀ hKC hdisj)⟩
  · rintro y z _ _ ⟨M, hM, hMy⟩ ⟨N, hN, hNz⟩
    refine ⟨M * N, Submonoid.mul_mem _ hM hN, ?_⟩
    have h1 : ((e.symm (y * z) : ↥K) : G) =
        ((e.symm y : ↥K) : G) * ((e.symm z : ↥K) : G) := by
      rw [map_mul]
      rfl
    rw [h1]
    exact Basis3.acts_mul _ hMy hNz
  · rintro y _ ⟨M, hM, hMy⟩
    obtain ⟨M', hM', hMM', hM'M⟩ := exists_inv_mem_closure hM
    refine ⟨M', hM', ?_⟩
    have hinv : ((e.symm y⁻¹ : ↥K) : G) = (((e.symm y : ↥K) : G))⁻¹ := by
      rw [map_inv]
      rfl
    rw [hinv]
    have hconj : ∀ v : Coords 8,
        (((e.symm y : ↥K) : G))⁻¹ * (torusBasis e hτ hb₀ hKC hdisj).vec v *
            ((e.symm y : ↥K) : G) =
          (torusBasis e hτ hb₀ hKC hdisj).vec (M' *ᵥ v) := by
      intro v
      have h := Basis3.acts_vec (torusBasis e hτ hb₀ hKC hdisj) hMy (M' *ᵥ v)
      rw [Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec] at h
      calc (((e.symm y : ↥K) : G))⁻¹ * (torusBasis e hτ hb₀ hKC hdisj).vec v *
            ((e.symm y : ↥K) : G)
          = (((e.symm y : ↥K) : G))⁻¹ * (((e.symm y : ↥K) : G) *
              (torusBasis e hτ hb₀ hKC hdisj).vec (M' *ᵥ v) *
              (((e.symm y : ↥K) : G))⁻¹) * ((e.symm y : ↥K) : G) := by rw [h]
        _ = (torusBasis e hτ hb₀ hKC hdisj).vec (M' *ᵥ v) := by group
    intro j
    rw [inv_inv, ← Basis3.vec_single (torusBasis e hτ hb₀ hKC hdisj) j,
      hconj (Pi.single j 1), Matrix.mulVec_single_one]
    rfl

theorem conj_mem_normalizer_of_mem_closure
    (hwn : ∀ k, MulAut.conj (w.n k) ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ∀ y ∈ Subgroup.closure (Set.range w.n),
      MulAut.conj y ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  intro y hy
  refine Subgroup.closure_induction (k := Set.range w.n) (p := fun y _ =>
    MulAut.conj y ∈ Subgroup.normalizer (A : Set (MulAut L'))) ?_ ?_ ?_ ?_ hy
  · rintro y ⟨k, rfl⟩
    exact hwn k
  · simpa using Subgroup.one_mem _
  · rintro y z _ _ hy hz
    rw [map_mul]
    exact Subgroup.mul_mem _ hy hz
  · rintro y _ hy
    rw [map_inv]
    exact Subgroup.inv_mem _ hy

theorem exists_closure_eq_ggConjAut (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇) :
    ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
      ∃ (y : L') (hy : y ∈ Subgroup.closure (Set.range w.n)),
        φ = ggConjAut A (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y hy) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hAut, -⟩ := hw
  intro φ hφ
  rw [hAut] at hφ
  have hconj_one : ∀ (h : MulAut.conj (1 : L') ∈
      Subgroup.normalizer (A : Set (MulAut L'))), ggConjAut A h = 1 := by
    intro h
    ext b
    rw [ggConjAut_apply, map_one]
    simp
  have hconj_inv : ∀ (y : L') (hy : y ∈ Subgroup.closure (Set.range w.n)),
      (ggConjAut A (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y hy))⁻¹ =
        ggConjAut A (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y⁻¹
          (Subgroup.inv_mem _ hy)) := by
    intro y hy
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [inv_apply_of_forall
        (fun b => ggConjAut_apply A
          (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y hy) b),
      ggConjAut_apply]
    simp only [zpow_neg_one, map_inv]
    group
  refine Subgroup.closure_induction (k := Set.range fun k => ggConjAut A (w.hn k))
    (p := fun φ _ => ∃ (y : L') (hy : y ∈ Subgroup.closure (Set.range w.n)),
      φ = ggConjAut A (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y hy))
    ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨k, rfl⟩
    refine ⟨w.n k, Subgroup.subset_closure ⟨k, rfl⟩, ?_⟩
    rw [show conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) (w.n k)
        (Subgroup.subset_closure ⟨k, rfl⟩) = w.hn k from Subsingleton.elim _ _]
  · have h1N : MulAut.conj (1 : L') ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
      rw [map_one]
      exact Subgroup.one_mem _
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [show conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) 1
        (Subgroup.one_mem _) = h1N from Subsingleton.elim _ _]
    exact (hconj_one h1N).symm
  · rintro φ ψ _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    refine ⟨y * z, Subgroup.mul_mem _ hy hz, ?_⟩
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply, ggConjAut_apply]
    simp only [map_mul, zpow_neg_one, mul_inv_rev]
    group
  · rintro φ _ ⟨y, hy, rfl⟩
    refine ⟨y⁻¹, Subgroup.inv_mem _ hy, hconj_inv y hy⟩



section FrameAction

variable {L' : Type} [Group L'] [Finite L'] {A' : Subgroup L'}
variable {w : GGTorusTorWit 3 7 L' (A'.map (MulAut.conj : L' →* MulAut L'))}
variable {hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)}
variable {e : ↥K ≃* L'} {hτ : Function.Injective (w.e7Tau hcomm)}
variable {hb₀ : orderOf b₀ = 3} {hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)}
variable {hdisj : Disjoint (Subgroup.zpowers b₀) K}
variable {hZ : Subgroup.center L' = ⊥}


private theorem conj_eq_of_acts_vec {y : L'} {M : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hM : (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y : ↥K) : G) M)
    {a : L'} {u : Coords 8} (hu : ((e.symm a : ↥K) : G) = (torusBasis e hτ hb₀ hKC hdisj).vec u) :
    y * a * y⁻¹ = e ⟨(torusBasis e hτ hb₀ hKC hdisj).vec (M *ᵥ u), by
      rw [← Basis3.acts_vec (torusBasis e hτ hb₀ hKC hdisj) hM u, ← hu]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (Subgroup.mul_mem K (Subgroup.mul_mem K (e.symm y).2 (e.symm a).2)
          (Subgroup.inv_mem K (e.symm y).2))⟩ := by
  have h1 : y * a * y⁻¹ = e (e.symm y * e.symm a * (e.symm y)⁻¹) := by
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [h1]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hu]
  exact Basis3.acts_vec (torusBasis e hτ hb₀ hKC hdisj) hM u

theorem ggConjAut_eq_of_acts {y y' : L'}
    (hyN : MulAut.conj y ∈ Subgroup.normalizer
      ((A'.map (MulAut.conj : L' →* MulAut L')) : Set (MulAut L')))
    (hyN' : MulAut.conj y' ∈ Subgroup.normalizer
      ((A'.map (MulAut.conj : L' →* MulAut L')) : Set (MulAut L')))
    {M : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hM : (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y : ↥K) : G) M)
    (hM' : (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y' : ↥K) : G) M)
    {E : Subgroup G} (hspan : (torusBasis e hτ hb₀ hKC hdisj).span = E)
    (hA'E : ∀ x : ↥K, e x ∈ A' ↔ (x : G) ∈ E) :
    ggConjAut (A'.map (MulAut.conj : L' →* MulAut L')) hyN =
      ggConjAut (A'.map (MulAut.conj : L' →* MulAut L')) hyN' := by
  have hkey : ∀ a ∈ A', y * a * y⁻¹ = y' * a * y'⁻¹ := by
    intro a ha
    have hmem : ((e.symm a : ↥K) : G) ∈ (torusBasis e hτ hb₀ hKC hdisj).span := by
      rw [hspan]
      exact (hA'E _).mp (by simpa using ha)
    obtain ⟨u, hu⟩ := Basis3.exists_vec_eq (torusBasis e hτ hb₀ hKC hdisj) hmem
    rw [conj_eq_of_acts_vec hM hu.symm, conj_eq_of_acts_vec hM' hu.symm]
  refine MulEquiv.ext fun b => ?_
  obtain ⟨a, ha, hb⟩ := Subgroup.mem_map.mp b.2
  have hb' : b = ⟨MulAut.conj a,
      Subgroup.mem_map_of_mem (MulAut.conj : L' →* MulAut L') ha⟩ := Subtype.ext hb.symm
  rw [hb']
  refine Subtype.ext ?_
  rw [ggConjAut_apply, ggConjAut_apply]
  have h1 : MulAut.conj y * MulAut.conj a * (MulAut.conj y)⁻¹ = MulAut.conj (y * a * y⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  have h2 : MulAut.conj y' * MulAut.conj a * (MulAut.conj y')⁻¹ =
      MulAut.conj (y' * a * y'⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [h1, h2, hkey a ha]

theorem acts_unique_of_ggConjAut_eq (hZ : Subgroup.center L' = ⊥) {y y' : L'}
    (hyN : MulAut.conj y ∈ Subgroup.normalizer
      ((A'.map (MulAut.conj : L' →* MulAut L')) : Set (MulAut L')))
    (hyN' : MulAut.conj y' ∈ Subgroup.normalizer
      ((A'.map (MulAut.conj : L' →* MulAut L')) : Set (MulAut L')))
    (hrange : (w.e7Tau hcomm).range = A')
    (heq : ggConjAut (A'.map (MulAut.conj : L' →* MulAut L')) hyN =
      ggConjAut (A'.map (MulAut.conj : L' →* MulAut L')) hyN')
    {M M' : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hM : (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y : ↥K) : G) M)
    (hM' : (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y' : ↥K) : G) M') :
    M = M' := by
  have hkey : ∀ a ∈ A', y * a * y⁻¹ = y' * a * y'⁻¹ := by
    intro a ha
    have hb : MulAut.conj a ∈ A'.map (MulAut.conj : L' →* MulAut L') :=
      Subgroup.mem_map_of_mem _ ha
    have h := congrArg (fun φ : MulAut ↥(A'.map (MulAut.conj : L' →* MulAut L')) =>
      ((φ ⟨MulAut.conj a, hb⟩ : ↥(A'.map (MulAut.conj : L' →* MulAut L'))) : MulAut L')) heq
    rw [ggConjAut_apply, ggConjAut_apply] at h
    apply mulAut_conj_injective hZ
    rw [show MulAut.conj (y * a * y⁻¹) =
        MulAut.conj y * MulAut.conj a * (MulAut.conj y)⁻¹ from by rw [map_mul, map_mul, map_inv],
      show MulAut.conj (y' * a * y'⁻¹) =
        MulAut.conj y' * MulAut.conj a * (MulAut.conj y')⁻¹ from by rw [map_mul, map_mul, map_inv]]
    exact h
  have hzero : ∀ i : Fin 8, M i 0 = M' i 0 := by
    intro i
    have hcommy := Subgroup.mem_centralizer_singleton_iff.mp (hKC (e.symm y).2)
    have hcommy' := Subgroup.mem_centralizer_singleton_iff.mp (hKC (e.symm y').2)
    have h1 : ((e.symm y : ↥K) : G) * (torusBasis e hτ hb₀ hKC hdisj).b 0 *
        ((e.symm y : ↥K) : G)⁻¹ = b₀ := by
      rw [torusBasis_b_zero, hcommy]
      group
    have h1' : ((e.symm y' : ↥K) : G) * (torusBasis e hτ hb₀ hKC hdisj).b 0 *
        ((e.symm y' : ↥K) : G)⁻¹ = b₀ := by
      rw [torusBasis_b_zero, hcommy']
      group
    have hv : (torusBasis e hτ hb₀ hKC hdisj).vec (fun i => M i 0) =
        (torusBasis e hτ hb₀ hKC hdisj).vec (fun i => M' i 0) := by
      rw [← hM 0, ← hM' 0, h1, h1']
    exact congrFun (Basis3.vec_injective _ hv) i
  have hsucc : ∀ (j' : Fin 7) (i : Fin 8), M i j'.succ = M' i j'.succ := by
    intro j' i
    have ha : w.e7Tau hcomm (Pi.mulSingle j' (Multiplicative.ofAdd (1 : ZMod 3))) ∈ A' :=
      hrange.le (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    have hb : ((e.symm (w.e7Tau hcomm (Pi.mulSingle j' (Multiplicative.ofAdd (1 : ZMod 3)))) :
        ↥K) : G) = (torusBasis e hτ hb₀ hKC hdisj).b j'.succ :=
      (torusBasis_b_succ ..).symm
    have h' : ((e.symm y : ↥K) : G) * ((e.symm (w.e7Tau hcomm (Pi.mulSingle j'
          (Multiplicative.ofAdd (1 : ZMod 3)))) : ↥K) : G) * (((e.symm y : ↥K) : G))⁻¹ =
        ((e.symm y' : ↥K) : G) * ((e.symm (w.e7Tau hcomm (Pi.mulSingle j'
          (Multiplicative.ofAdd (1 : ZMod 3)))) : ↥K) : G) * (((e.symm y' : ↥K) : G))⁻¹ := by
      have h := congrArg (fun z : ↥K => (z : G))
        (congrArg (fun z : L' => e.symm z) (hkey _ ha))
      simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h
    have hv : (torusBasis e hτ hb₀ hKC hdisj).vec (fun i => M i j'.succ) =
        (torusBasis e hτ hb₀ hKC hdisj).vec (fun i => M' i j'.succ) := by
      rw [← hM j'.succ, ← hM' j'.succ, ← hb, h']
    exact congrFun (Basis3.vec_injective _ hv) i
  ext i j
  cases j using Fin.cases with
  | zero => exact hzero i
  | succ j' => exact hsucc j' i

end FrameAction

end E7Torus

end FrameRoute.FS81

end CFSG.StandardType

end
