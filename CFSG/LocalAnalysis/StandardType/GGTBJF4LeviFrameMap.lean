module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTBTorTransport
public import CFSG.LocalAnalysis.ComponentClassification.Components

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem f4lm_holds_of_eq_subgroup {m N : ℕ} {L' : Type} [Group L']
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {A A' : Subgroup (MulAut L')} (h : A = A') (w : GGTorusTorWit m N L' A')
    (hw : w.Holds C M) : (h.symm ▸ w).Holds C M := by
  cases h
  exact hw

private theorem f4lm_n_of_eq_subgroup {m N : ℕ} {L' : Type} [Group L']
    {A A' : Subgroup (MulAut L')} (h : A = A') (w : GGTorusTorWit m N L' A') (k : Fin N) :
    (h.symm ▸ w).n k = w.n k := by
  cases h
  rfl

private theorem f4lm_congr_conj {R R' : Type} [Group R] [Group R'] (φ : R ≃* R') :
    (MulAut.congr φ).toMonoidHom.comp (MulAut.conj : R →* MulAut R) =
      (MulAut.conj : R' →* MulAut R').comp φ.toMonoidHom := by
  refine MonoidHom.ext fun r => MulEquiv.ext fun x => ?_
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem f4lm_map_centralizer {R R' : Type} [Group R] [Group R'] (φ : R ≃* R') (x : R) :
    (Subgroup.centralizer ({φ x} : Set R')).map φ.symm.toMonoidHom =
      Subgroup.centralizer ({x} : Set R) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y', hy', rfl⟩
    apply φ.injective
    simpa using hy'
  · intro h
    refine ⟨φ y, ?_, by simp⟩
    simpa using congrArg φ h

theorem GGF4LeviFrame.of_mulEquiv {p : ℕ} [NeZero p] {R R' : Type}
    [Group R] [Group R'] (φ : R ≃* R') {E : Subgroup R} (hF : GGF4LeviFrame p E) :
    GGF4LeviFrame p (E.map φ.toMonoidHom) := by
  classical
  obtain ⟨Lf, hLf, ζ, hζ, ι₀, nk, m, wt, hζo, hinj, hrange, hact, hwn, hwt, hcl⟩ := hF
  have hA' : (E.map (MulAut.conj : R →* MulAut R)).map (MulAut.congr φ).toMonoidHom =
      (E.map φ.toMonoidHom).map (MulAut.conj : R' →* MulAut R') := by
    rw [Subgroup.map_map, Subgroup.map_map, f4lm_congr_conj]
  let w'' : GGTorusTorWit m 4 R'
      ((E.map (MulAut.conj : R →* MulAut R)).map (MulAut.congr φ).toMonoidHom) :=
    wt.transport φ
  have hw'' : w''.Holds CartanMatrix.F₄ CoxeterMatrix.F₄ := wt.holds_transport φ hwt
  let w' : GGTorusTorWit m 4 R' ((E.map φ.toMonoidHom).map (MulAut.conj : R' →* MulAut R')) :=
    hA' ▸ w''
  have hw' : w'.Holds CartanMatrix.F₄ CoxeterMatrix.F₄ :=
    f4lm_holds_of_eq_subgroup hA'.symm w'' hw''
  have hwn' : ∀ k, w'.n k = φ (nk k) := by
    intro k
    have h1 : w'.n k = w''.n k := f4lm_n_of_eq_subgroup hA'.symm w'' k
    rw [h1, GGTorusTorWit.transport_n, hwn]
  refine ⟨Lf, hLf, ζ, hζ, φ.toMonoidHom.comp ι₀, fun k => φ (nk k), m, w', hζo,
    φ.injective.comp hinj, ?_, ?_, hwn', hw', ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · intro k s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hact k s]
  · intro t ht Y' hY'
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at ht hY'
    have ht1 : ι₀ (Multiplicative.ofAdd t) ≠ 1 := fun h => ht (by rw [h, map_one])
    have hYo := CFSG.Assembly.isComponentOf_iff_open.1 hY'
    have hY : IsComponentOf (Y'.map φ.symm.toMonoidHom)
        (Subgroup.centralizer ({ι₀ (Multiplicative.ofAdd t)} : Set R)) := by
      rw [← f4lm_map_centralizer φ (ι₀ (Multiplicative.ofAdd t))]
      exact CFSG.Assembly.isComponentOf_iff_open.2 ⟨Subgroup.map_mono hYo.1,
        CFSG.ComponentClassification.Components.chain_map _ hYo.2.1,
        CFSG.ComponentClassification.Components.quasisimple_of_equiv
          (Y'.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective).symm hYo.2.2⟩
    obtain ⟨i, hcen, hreal⟩ := hcl t ht1 _ hY
    refine ⟨i, ?_, ?_⟩
    · intro s hs
      have h1 := hcen s hs
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [Subgroup.mem_centralizer_iff]
      intro y' hy'
      have hy : φ.symm y' ∈ Y'.map φ.symm.toMonoidHom := ⟨y', hy', rfl⟩
      have h2 := Subgroup.mem_centralizer_iff.mp h1 (φ.symm y') hy
      apply φ.symm.injective
      simpa using h2
    · intro v Sd hSd hroots c hc
      obtain ⟨y, hyY, hy⟩ := hreal v Sd hSd hroots c hc
      obtain ⟨y', hy', rfl⟩ := hyY
      refine ⟨y', hy', fun s => ?_⟩
      have h3 := hy s
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      apply φ.symm.injective
      simpa using h3

theorem GGF4LeviFrame.of_map_eq {p : ℕ} [NeZero p] {R R' : Type}
    [Group R] [Group R'] (φ : R ≃* R') {E : Subgroup R} {E' : Subgroup R'}
    (h : E.map φ.toMonoidHom = E') (hF : GGF4LeviFrame p E') : GGF4LeviFrame p E := by
  have h2 : E'.map φ.symm.toMonoidHom = E := by
    rw [← h, Subgroup.map_map]
    have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id R := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  rw [← h2]
  exact GGF4LeviFrame.of_mulEquiv φ.symm hF

end CFSG.StandardType

end
