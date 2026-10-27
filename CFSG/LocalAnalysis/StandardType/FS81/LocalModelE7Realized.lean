module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalModelE7Bound
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux

public section

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.StandardType.FrameRoute.FS81

namespace FrameRoute.FS81

section E7Realized

variable {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
variable {L' : Type} [Group L'] [Finite L'] {A' : Subgroup L'}
variable {w : GGTorusTorWit 3 7 L' (A'.map (MulAut.conj : L' →* MulAut L'))}
variable {hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)}
variable {e : ↥K ≃* L'} {hτ : Function.Injective (w.e7Tau hcomm)}
variable {hb₀ : orderOf b₀ = 3} {hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)}
variable {hdisj : Disjoint (Subgroup.zpowers b₀) K}

private theorem conj_apply_eq_of_inner
    {hKN : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G)}
    {g : G} (hgC : g ∈ Subgroup.centralizer ({b₀} : Set G)) {y : L'}
    (hInner : e.symm.trans ((ggConjAut K (hKN hgC)).trans e) = MulAut.conj y) (x : ↥K) :
    g * (x : G) * g⁻¹ =
      ((e.symm y : ↥K) : G) * (x : G) * (((e.symm y : ↥K) : G))⁻¹ := by
  have h1 : e (ggConjAut K (hKN hgC) x) = y * e x * y⁻¹ := by
    have h := congrArg (fun f : MulAut L' => f (e x)) hInner
    simpa [MulAut.conj_apply, MulEquiv.trans_apply] using h
  have h2 : e (e.symm y * x * (e.symm y)⁻¹) = y * e x * y⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h3 : ggConjAut K (hKN hgC) x = e.symm y * x * (e.symm y)⁻¹ :=
    e.injective (h1.trans h2.symm)
  rw [← ggConjAut_apply K (hKN hgC) x, h3]
  rfl

private theorem acts_of_acts_of_inner
    {hKN : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G)}
    {g : G} (hgC : g ∈ Subgroup.centralizer ({b₀} : Set G)) {y : L'}
    (hInner : e.symm.trans ((ggConjAut K (hKN hgC)).trans e) = MulAut.conj y)
    {M : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hActs : (torusBasis e hτ hb₀ hKC hdisj).Acts g M) :
    (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y : ↥K) : G) M := by
  intro j
  cases j using Fin.cases with
  | zero =>
    have hgy : g * b₀ * g⁻¹ = b₀ := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hgC
      rw [h]
      group
    have hyy : ((e.symm y : ↥K) : G) * b₀ * (((e.symm y : ↥K) : G))⁻¹ = b₀ := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hKC (e.symm y).2)
      rw [h]
      group
    have hActs0 : g * b₀ * g⁻¹ =
        (torusBasis e hτ hb₀ hKC hdisj).vec (fun i => M i 0) := by
      simpa [torusBasis_b_zero] using hActs 0
    calc ((e.symm y : ↥K) : G) * (torusBasis e hτ hb₀ hKC hdisj).b 0 *
          (((e.symm y : ↥K) : G))⁻¹
        = ((e.symm y : ↥K) : G) * b₀ * (((e.symm y : ↥K) : G))⁻¹ := by
          rw [torusBasis_b_zero]
      _ = b₀ := hyy
      _ = g * b₀ * g⁻¹ := hgy.symm
      _ = (torusBasis e hτ hb₀ hKC hdisj).vec (fun i => M i 0) := hActs0
  | succ i =>
    have hx := conj_apply_eq_of_inner (hKN := hKN) hgC hInner
      (e.symm (w.e7Tau hcomm (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3)))))
    have hActs' : g * (((e.symm (w.e7Tau hcomm
          (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3)))) : ↥K) : G)) * g⁻¹ =
        (torusBasis e hτ hb₀ hKC hdisj).vec (fun j => M j i.succ) := by
      simpa [torusBasis_b_succ] using hActs i.succ
    rw [torusBasis_b_succ]
    exact hx.symm.trans hActs'

private theorem conj_mem_of_mem_normalizer
    (hA'E : ∀ x : ↥K, e x ∈ A' ↔ (x : G) ∈ E) {z : L'}
    (hz : ((e.symm z : ↥K) : G) ∈
      Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G))
    {t : L'} (ht : t ∈ A') : z * t * z⁻¹ ∈ A' := by
  have htA : ((e.symm t : ↥K) : G) ∈ E ⊓ K := by
    rw [Subgroup.mem_inf]
    exact ⟨(hA'E (e.symm t)).mp (by simpa using ht), (e.symm t).2⟩
  have hmem : ((e.symm z : ↥K) : G) * ((e.symm t : ↥K) : G) *
      (((e.symm z : ↥K) : G))⁻¹ ∈ E ⊓ K :=
    (Subgroup.mem_normalizer_iff.mp hz (e.symm t)).mp htA
  have heq : z * t * z⁻¹ = e (e.symm z * e.symm t * (e.symm z)⁻¹) := by
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [heq]
  exact (hA'E _).mpr (by simpa using (Subgroup.mem_inf.mp hmem).1)

private theorem conj_mem_normalizer_of_acts
    (hspan : (torusBasis e hτ hb₀ hKC hdisj).span = E)
    (hA'E : ∀ x : ↥K, e x ∈ A' ↔ (x : G) ∈ E)
    {y : L'} {M : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hActs : (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y : ↥K) : G) M) :
    MulAut.conj y ∈ Subgroup.normalizer
      ((A'.map (MulAut.conj : L' →* MulAut L')) : Set (MulAut L')) := by
  have huN : ((e.symm y : ↥K) : G) ∈ Subgroup.normalizer (E : Set G) := by
    rw [← hspan]
    exact Basis3.mem_normalizer_of_acts _ hActs
  have huA : ((e.symm y : ↥K) : G) ∈
      Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at huN ⊢
    intro z
    have hKz : z ∈ K ↔ ((e.symm y : ↥K) : G) * z * (((e.symm y : ↥K) : G))⁻¹ ∈ K :=
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (H := K) (e.symm y).2) z
    rw [Subgroup.mem_inf, Subgroup.mem_inf, huN z, hKz]
  have hAy : ∀ t ∈ A', y * t * y⁻¹ ∈ A' := fun t ht =>
    conj_mem_of_mem_normalizer hA'E huA ht
  have hAyinv : ∀ t ∈ A', y⁻¹ * t * y ∈ A' := by
    intro t ht
    simpa using conj_mem_of_mem_normalizer (z := y⁻¹) hA'E
      (by simpa using Subgroup.inv_mem _ huA) ht
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hconj : MulAut.conj y * MulAut.conj t * (MulAut.conj y)⁻¹ =
        MulAut.conj (y * t * y⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [hconj]
    exact Subgroup.mem_map_of_mem _ (hAy t ht)
  · rintro ⟨t, ht, hbt⟩
    have hb : b = MulAut.conj (y⁻¹ * t * y) := by
      have h1 : b = (MulAut.conj y)⁻¹ * MulAut.conj t * MulAut.conj y := by
        rw [hbt]
        group
      have h2 : MulAut.conj (y⁻¹ * t * y) =
          (MulAut.conj y)⁻¹ * MulAut.conj t * MulAut.conj y := by
        rw [map_mul, map_mul, map_inv]
      rw [h1, ← h2]
    rw [hb]
    exact Subgroup.mem_map_of_mem _ (hAyinv t ht)

private theorem realized_centralizer_subset_closure
    (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hKN : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hOut : ∀ φ : MulAut L', φ ∈ (MulAut.conj : L' →* MulAut L').range)
    (hZ : Subgroup.center L' = ⊥)
    (hrange : (w.e7Tau hcomm).range = A')
    (hspan : (torusBasis e hτ hb₀ hKC hdisj).span = E)
    (hA'E : ∀ x : ↥K, e x ∈ A' ↔ (x : G) ∈ E) :
    (torusBasis e hτ hb₀ hKC hdisj).realized
        (Subgroup.centralizer ({b₀} : Set G)) ⊆
      (Submonoid.closure (Set.range e7LocalGen) :
        Set (Matrix (Fin 8) (Fin 8) (ZMod 3))) := by
  rintro M ⟨g, hgC, hActs⟩
  obtain ⟨y, hInner⟩ := hOut (e.symm.trans ((ggConjAut K (hKN hgC)).trans e))
  have hActsY := acts_of_acts_of_inner (hKN := hKN) hgC hInner.symm hActs
  have hyN : MulAut.conj y ∈ Subgroup.normalizer
      ((A'.map (MulAut.conj : L' →* MulAut L')) : Set (MulAut L')) :=
    conj_mem_normalizer_of_acts hspan hA'E hActsY
  have hmem : ggConjAut (A'.map (MulAut.conj : L' →* MulAut L')) hyN ∈
      ggAutomizer (MulAut.conj : L' →* MulAut L').range
        (A'.map (MulAut.conj : L' →* MulAut L')) :=
    ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
      (Bs := A'.map (MulAut.conj : L' →* MulAut L')) (g := MulAut.conj y)
      (MonoidHom.mem_range.mpr ⟨y, rfl⟩) hyN
  obtain ⟨y', hy', hU⟩ := exists_closure_eq_ggConjAut (w := w)
    (A := A'.map (MulAut.conj : L' →* MulAut L')) hw _ hmem
  obtain ⟨M', hM', hActs'⟩ :=
    exists_acts_of_mem_closure (w := w) (hcomm := hcomm) (e := e) (hτ := hτ)
      (hb₀ := hb₀) (hKC := hKC) (hdisj := hdisj) hw hZ (y := y') hy'
  have heq : ggConjAut (A'.map (MulAut.conj : L' →* MulAut L')) hyN =
      ggConjAut (A'.map (MulAut.conj : L' →* MulAut L'))
        (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y' hy') := hU
  have hMM : M = M' := acts_unique_of_ggConjAut_eq hZ hyN
    (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y' hy')
    hrange heq hActsY hActs'
  rw [hMM]
  exact hM'

private theorem closure_subset_realized_centralizer
    (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hZ : Subgroup.center L' = ⊥) :
    (Submonoid.closure (Set.range e7LocalGen) :
        Set (Matrix (Fin 8) (Fin 8) (ZMod 3))) ⊆
      (torusBasis e hτ hb₀ hKC hdisj).realized
        (Subgroup.centralizer ({b₀} : Set G)) := by
  intro M hM
  refine Submonoid.closure_induction (s := Set.range e7LocalGen)
    (motive := fun M _ => M ∈ (torusBasis e hτ hb₀ hKC hdisj).realized
      (Subgroup.centralizer ({b₀} : Set G))) ?_ ?_ ?_ hM
  · rintro M ⟨k, rfl⟩
    exact ⟨((e.symm (w.n k) : ↥K) : G), hKC (e.symm (w.n k)).2,
      e7LocalGen_acts (hcomm := hcomm) hw hZ k⟩
  · exact ⟨1, Subgroup.one_mem _,
      by simpa using Basis3.acts_one (torusBasis e hτ hb₀ hKC hdisj)⟩
  · intro M N _ _ hMM hNN
    obtain ⟨g, hgC, hActs⟩ := hMM
    obtain ⟨h, hhC, hActs'⟩ := hNN
    exact ⟨g * h, Subgroup.mul_mem _ hgC hhC, Basis3.acts_mul _ hActs hActs'⟩

theorem realized_centralizer_eq_closure
    (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hKN : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hOut : ∀ φ : MulAut L', φ ∈ (MulAut.conj : L' →* MulAut L').range)
    (hZ : Subgroup.center L' = ⊥)
    (hrange : (w.e7Tau hcomm).range = A')
    (hspan : (torusBasis e hτ hb₀ hKC hdisj).span = E)
    (hA'E : ∀ x : ↥K, e x ∈ A' ↔ (x : G) ∈ E) :
    (torusBasis e hτ hb₀ hKC hdisj).realized
        (Subgroup.centralizer ({b₀} : Set G)) =
      (Submonoid.closure (Set.range e7LocalGen) :
        Set (Matrix (Fin 8) (Fin 8) (ZMod 3))) :=
  le_antisymm
    (realized_centralizer_subset_closure hw hKN hOut hZ hrange hspan hA'E)
    (closure_subset_realized_centralizer hw hZ)

abbrev e7FrameAut (A' : Subgroup L') :
    Subgroup (MulAut ↥(A'.map (MulAut.conj : L' →* MulAut L'))) :=
  ggAutomizer (MulAut.conj : L' →* MulAut L').range
    (A'.map (MulAut.conj : L' →* MulAut L'))

private theorem exists_realized_of_aut
    (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hZ : Subgroup.center L' = ⊥) (φ : ↥(e7FrameAut A')) :
    ∃ M, M ∈ (torusBasis e hτ hb₀ hKC hdisj).realized
        (Subgroup.centralizer ({b₀} : Set G)) ∧
      ∃ (y : L') (hy : y ∈ Subgroup.closure (Set.range w.n)),
        (φ : MulAut ↥(A'.map (MulAut.conj : L' →* MulAut L'))) =
          ggConjAut (A'.map (MulAut.conj : L' →* MulAut L'))
            (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y hy) ∧
        (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y : ↥K) : G) M := by
  obtain ⟨y, hy, heq⟩ := exists_closure_eq_ggConjAut (w := w)
    (A := A'.map (MulAut.conj : L' →* MulAut L')) hw φ φ.2
  obtain ⟨M, hM, hActs⟩ :=
    exists_acts_of_mem_closure (w := w) (hcomm := hcomm) (e := e) (hτ := hτ)
      (hb₀ := hb₀) (hKC := hKC) (hdisj := hdisj) hw hZ (y := y) hy
  exact ⟨M, ⟨e.symm y, hKC (e.symm y).2, hActs⟩, y, hy, heq, hActs⟩

private noncomputable def autMatrix
    (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hZ : Subgroup.center L' = ⊥) (φ : ↥(e7FrameAut A')) :
    ↥((torusBasis e hτ hb₀ hKC hdisj).realized
      (Subgroup.centralizer ({b₀} : Set G))) :=
  ⟨Classical.choose (exists_realized_of_aut (e := e) (hτ := hτ) (hb₀ := hb₀)
      (hKC := hKC) (hdisj := hdisj) (w := w) (hcomm := hcomm) hw hZ φ),
    (Classical.choose_spec (exists_realized_of_aut (e := e) (hτ := hτ) (hb₀ := hb₀)
      (hKC := hKC) (hdisj := hdisj) (w := w) (hcomm := hcomm) hw hZ φ)).1⟩

private theorem autMatrix_eq
    (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hZ : Subgroup.center L' = ⊥)
    (hrange : (w.e7Tau hcomm).range = A')
    {φ : ↥(e7FrameAut A')}
    {y : L'} (hy : y ∈ Subgroup.closure (Set.range w.n))
    (heq : (φ : MulAut ↥(A'.map (MulAut.conj : L' →* MulAut L'))) =
      ggConjAut (A'.map (MulAut.conj : L' →* MulAut L'))
        (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y hy))
    {M : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hM : M ∈ (torusBasis e hτ hb₀ hKC hdisj).realized
      (Subgroup.centralizer ({b₀} : Set G)))
    (hActs : (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y : ↥K) : G) M) :
    autMatrix hw hZ φ = ⟨M, hM⟩ := by
  obtain ⟨-, hRest⟩ :=
    Classical.choose_spec (exists_realized_of_aut (e := e) (hτ := hτ) (hb₀ := hb₀)
      (hKC := hKC) (hdisj := hdisj) (w := w) (hcomm := hcomm) hw hZ φ)
  obtain ⟨y₀, hRest⟩ := hRest
  obtain ⟨hy₀, hRest⟩ := hRest
  obtain ⟨heq₀, hActs₀⟩ := hRest
  apply Subtype.ext
  exact (acts_unique_of_ggConjAut_eq hZ
    (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y hy)
    (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y₀ hy₀)
    hrange (heq.symm.trans heq₀) hActs hActs₀).symm

private theorem autMatrix_injective
    (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hZ : Subgroup.center L' = ⊥)
    (hspan : (torusBasis e hτ hb₀ hKC hdisj).span = E)
    (hA'E : ∀ x : ↥K, e x ∈ A' ↔ (x : G) ∈ E) :
    Function.Injective (fun φ : ↥(e7FrameAut A') =>
      (autMatrix hw hZ φ : ↥((torusBasis e hτ hb₀ hKC hdisj).realized
        (Subgroup.centralizer ({b₀} : Set G))))) := by
  intro φ ψ h
  obtain ⟨-, hRest⟩ :=
    Classical.choose_spec (exists_realized_of_aut (e := e) (hτ := hτ) (hb₀ := hb₀)
      (hKC := hKC) (hdisj := hdisj) (w := w) (hcomm := hcomm) hw hZ φ)
  obtain ⟨y, hRest⟩ := hRest
  obtain ⟨hy, hRest⟩ := hRest
  obtain ⟨heq, hActs⟩ := hRest
  obtain ⟨-, hRest'⟩ :=
    Classical.choose_spec (exists_realized_of_aut (e := e) (hτ := hτ) (hb₀ := hb₀)
      (hKC := hKC) (hdisj := hdisj) (w := w) (hcomm := hcomm) hw hZ ψ)
  obtain ⟨y', hRest'⟩ := hRest'
  obtain ⟨hy', hRest'⟩ := hRest'
  obtain ⟨heq', hActs'⟩ := hRest'
  have hMM : Classical.choose (exists_realized_of_aut (e := e) (hτ := hτ) (hb₀ := hb₀)
        (hKC := hKC) (hdisj := hdisj) (w := w) (hcomm := hcomm) hw hZ φ) =
      Classical.choose (exists_realized_of_aut (e := e) (hτ := hτ) (hb₀ := hb₀)
        (hKC := hKC) (hdisj := hdisj) (w := w) (hcomm := hcomm) hw hZ ψ) := by
    simpa [autMatrix] using congrArg Subtype.val h
  have hActs'' : (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y' : ↥K) : G)
      (Classical.choose (exists_realized_of_aut (e := e) (hτ := hτ) (hb₀ := hb₀)
        (hKC := hKC) (hdisj := hdisj) (w := w) (hcomm := hcomm) hw hZ φ)) := by
    rw [hMM]
    exact hActs'
  have heqAut := ggConjAut_eq_of_acts
    (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y hy)
    (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y' hy')
    hActs hActs'' hspan hA'E
  apply Subtype.ext
  rw [heq, heq', heqAut]

private theorem autMatrix_surjective
    (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hKN : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hOut : ∀ φ : MulAut L', φ ∈ (MulAut.conj : L' →* MulAut L').range)
    (hZ : Subgroup.center L' = ⊥)
    (hrange : (w.e7Tau hcomm).range = A')
    (hspan : (torusBasis e hτ hb₀ hKC hdisj).span = E)
    (hA'E : ∀ x : ↥K, e x ∈ A' ↔ (x : G) ∈ E) :
    Function.Surjective (fun φ : ↥(e7FrameAut A') =>
      (autMatrix hw hZ φ : ↥((torusBasis e hτ hb₀ hKC hdisj).realized
        (Subgroup.centralizer ({b₀} : Set G))))) := by
  rintro ⟨M, hM⟩
  have hMmem : M ∈ (torusBasis e hτ hb₀ hKC hdisj).realized
      (Subgroup.centralizer ({b₀} : Set G)) := hM
  obtain ⟨g, hgC, hActs⟩ := hM
  obtain ⟨y₀, hInner⟩ := hOut (e.symm.trans ((ggConjAut K (hKN hgC)).trans e))
  have hActsY : (torusBasis e hτ hb₀ hKC hdisj).Acts ((e.symm y₀ : ↥K) : G) M :=
    acts_of_acts_of_inner (hKN := hKN) hgC hInner.symm hActs
  have hyN₀ : MulAut.conj y₀ ∈ Subgroup.normalizer
      ((A'.map (MulAut.conj : L' →* MulAut L')) : Set (MulAut L')) :=
    conj_mem_normalizer_of_acts hspan hA'E hActsY
  have hmem : ggConjAut (A'.map (MulAut.conj : L' →* MulAut L')) hyN₀ ∈
      ggAutomizer (MulAut.conj : L' →* MulAut L').range
        (A'.map (MulAut.conj : L' →* MulAut L')) :=
    ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
      (Bs := A'.map (MulAut.conj : L' →* MulAut L')) (g := MulAut.conj y₀)
      (MonoidHom.mem_range.mpr ⟨y₀, rfl⟩) hyN₀
  let φ : ↥(e7FrameAut A') :=
    ⟨ggConjAut (A'.map (MulAut.conj : L' →* MulAut L')) hyN₀, hmem⟩
  obtain ⟨y, hy, hU⟩ := exists_closure_eq_ggConjAut (w := w)
    (A := A'.map (MulAut.conj : L' →* MulAut L')) hw φ φ.2
  obtain ⟨M', hM', hActs'⟩ :=
    exists_acts_of_mem_closure (w := w) (hcomm := hcomm) (e := e) (hτ := hτ)
      (hb₀ := hb₀) (hKC := hKC) (hdisj := hdisj) hw hZ (y := y) hy
  have hMM : M' = M := acts_unique_of_ggConjAut_eq hZ
    (conj_mem_normalizer_of_mem_closure (w := w) (fun k => w.hn k) y hy) hyN₀
    hrange (by simpa using hU.symm) hActs' hActsY
  have hM'M : M' ∈ (torusBasis e hτ hb₀ hKC hdisj).realized
      (Subgroup.centralizer ({b₀} : Set G)) := by
    rw [hMM]
    exact hMmem
  refine ⟨φ, ?_⟩
  have hfin : autMatrix hw hZ φ = ⟨M, hMmem⟩ := by
    rw [autMatrix_eq (e := e) (hτ := hτ) (hb₀ := hb₀) (hKC := hKC) (hdisj := hdisj)
      (w := w) (hcomm := hcomm) hw hZ hrange hy hU hM'M hActs']
    exact Subtype.ext hMM
  simpa using hfin

theorem card_realized_centralizer
    (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hKN : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hOut : ∀ φ : MulAut L', φ ∈ (MulAut.conj : L' →* MulAut L').range)
    (hZ : Subgroup.center L' = ⊥)
    (hrange : (w.e7Tau hcomm).range = A')
    (hspan : (torusBasis e hτ hb₀ hKC hdisj).span = E)
    (hA'E : ∀ x : ↥K, e x ∈ A' ↔ (x : G) ∈ E)
    (hAutCard : Nat.card ↥(e7FrameAut A') = 2903040) :
    Nat.card ↥((torusBasis e hτ hb₀ hKC hdisj).realized
      (Subgroup.centralizer ({b₀} : Set G))) = 2903040 := by
  rw [← Nat.card_congr (Equiv.ofBijective
    (fun φ : ↥(e7FrameAut A') =>
      (autMatrix hw hZ φ : ↥((torusBasis e hτ hb₀ hKC hdisj).realized
        (Subgroup.centralizer ({b₀} : Set G)))))
    ⟨autMatrix_injective hw hZ hspan hA'E,
      autMatrix_surjective hw hKN hOut hZ hrange hspan hA'E⟩)]
  exact hAutCard

theorem card_closure_eq_2903040
    (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hKN : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hOut : ∀ φ : MulAut L', φ ∈ (MulAut.conj : L' →* MulAut L').range)
    (hZ : Subgroup.center L' = ⊥)
    (hrange : (w.e7Tau hcomm).range = A')
    (hspan : (torusBasis e hτ hb₀ hKC hdisj).span = E)
    (hA'E : ∀ x : ↥K, e x ∈ A' ↔ (x : G) ∈ E)
    (hAutCard : Nat.card ↥(e7FrameAut A') = 2903040) :
    Nat.card ↥(Submonoid.closure (Set.range e7LocalGen)) = 2903040 := by
  refine (Nat.card_congr (Set.equivOfEq
    (realized_centralizer_eq_closure hw hKN hOut hZ hrange hspan hA'E).symm)).trans ?_
  exact card_realized_centralizer hw hKN hOut hZ hrange hspan hA'E hAutCard

theorem card_e7FrameAut_eq_2903040
    (hAut : Nonempty ((CoxeterMatrix.E₇).Group ≃* ↥(e7FrameAut A'))) :
    Nat.card ↥(e7FrameAut A') = 2903040 := by
  obtain ⟨φ⟩ := hAut
  rw [Nat.card_congr φ.symm.toEquiv]
  exact card_coxeterE7_group

end E7Realized

end FrameRoute.FS81

end CFSG.StandardType

end
