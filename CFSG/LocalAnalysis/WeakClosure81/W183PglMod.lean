module

public import CFSG.LocalAnalysis.WeakClosure81.W183Asch66Pgl
public import CFSG.LocalAnalysis.WeakClosure81.W183PglBridge
public import CFSG.LocalAnalysis.WeakClosure81.W183PglOuter
import CFSG.LocalAnalysis.ComponentClassification.ElementaryAbelianFour
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup Matrix

section Stage

variable {Q : Type} [Group Q] {V : Type} [CommGroup V]

theorem w183Pgl_restrict (ρ : Q →* MulAut V) {L : Subgroup Q} {I : Subgroup V}
    (hI : ∀ l ∈ L, ∀ i ∈ I, ρ l i ∈ I) (e : ↥L ≃* GL (Fin 3) (ZMod 2)) :
    ∃ σ : GL (Fin 3) (ZMod 2) →* MulAut ↥I,
      ∀ (l : ↥L) (i : ↥I), ((σ (e l) i : ↥I) : V) = ρ (l : Q) (i : V) := by
  have hcomp : ∀ (l : Q) (i : V), ρ l⁻¹ (ρ l i) = i := fun l i => by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hcomp' : ∀ (l : Q) (i : V), ρ l (ρ l⁻¹ i) = i := fun l i => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  let f : ↥L → MulAut ↥I := fun l =>
    { toFun := fun i => ⟨ρ (l : Q) (i : V), hI l l.2 i i.2⟩
      invFun := fun i => ⟨ρ ((l : Q)⁻¹) (i : V), hI _ (L.inv_mem l.2) i i.2⟩
      left_inv := fun i => Subtype.ext (hcomp l i)
      right_inv := fun i => Subtype.ext (hcomp' l i)
      map_mul' := fun a b => Subtype.ext (map_mul (ρ (l : Q)) (a : V) (b : V)) }
  let ρI : ↥L →* MulAut ↥I :=
    { toFun := f
      map_one' := MulEquiv.ext fun i => Subtype.ext (by
        change ρ ((1 : ↥L) : Q) (i : V) = (i : V)
        simp)
      map_mul' := fun a b => MulEquiv.ext fun i => Subtype.ext (by
        change ρ ((a * b : ↥L) : Q) (i : V) = ρ (a : Q) (ρ (b : Q) (i : V))
        rw [Subgroup.coe_mul, map_mul]
        rfl) }
  refine ⟨ρI.comp e.symm.toMonoidHom, fun l i => ?_⟩
  change ((f (e.symm (e l)) i : ↥I) : V) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem w183Pgl_irr_abstract (ρ : Q →* MulAut V) {L : Subgroup Q} {I : Subgroup V}
    (hirr : IsIrr ρ L I) (e : ↥L ≃* GL (Fin 3) (ZMod 2))
    (σ : GL (Fin 3) (ZMod 2) →* MulAut ↥I)
    (hσ : ∀ (l : ↥L) (i : ↥I), ((σ (e l) i : ↥I) : V) = ρ (l : Q) (i : V)) :
    (∃ i : ↥I, i ≠ 1) ∧
      (∀ i : ↥I, i ∈ Subgroup.closure
        {x : ↥I | ∃ (g : GL (Fin 3) (ZMod 2)) (j : ↥I), x = σ g j * j⁻¹}) ∧
      ∀ J : Subgroup ↥I, (∀ g, ∀ j ∈ J, σ g j ∈ J) → W183PglFixed σ ≤ J →
        J = W183PglFixed σ ∨ J = ⊤ := by
  obtain ⟨hne, hgen, hmin⟩ := hirr
  have hLmem : ∀ (g : GL (Fin 3) (ZMod 2)) (j : ↥I),
      ((σ g j : ↥I) : V) = ρ ((e.symm g : ↥L) : Q) (j : V) := fun g j => by
    have := hσ (e.symm g) j
    rwa [MulEquiv.apply_symm_apply] at this
  refine ⟨Subgroup.ne_bot_iff_exists_ne_one.1 hne, ?_, ?_⟩
  · intro i
    have hle : I ≤ (Subgroup.closure
        {x : ↥I | ∃ (g : GL (Fin 3) (ZMod 2)) (j : ↥I), x = σ g j * j⁻¹}).map I.subtype := by
      refine hgen.le.trans ((Subgroup.closure_le _).2 ?_)
      rintro _ ⟨j, hj, l, hl, rfl⟩
      refine ⟨σ (e ⟨l, hl⟩) ⟨j, hj⟩ * ⟨j, hj⟩⁻¹, Subgroup.subset_closure ⟨_, _, rfl⟩, ?_⟩
      change ((σ (e ⟨l, hl⟩) ⟨j, hj⟩ : ↥I) : V) * (j : V)⁻¹ = ρ l j * j⁻¹
      rw [hσ]
    obtain ⟨t, ht, hti⟩ := hle i.2
    have : t = i := Subtype.ext hti
    rwa [this] at ht
  · intro J hJ hFJ
    have hJ'inv : ∀ l ∈ L, ∀ j ∈ J.map I.subtype, ρ l j ∈ J.map I.subtype := by
      rintro l hl _ ⟨j₀, hj₀, rfl⟩
      refine ⟨σ (e ⟨l, hl⟩) j₀, hJ _ j₀ hj₀, ?_⟩
      change ((σ (e ⟨l, hl⟩) j₀ : ↥I) : V) = ρ l (j₀ : V)
      rw [hσ]
    have hfixed : ∀ i : ↥I, (∀ l ∈ L, ρ l (i : V) = (i : V)) → i ∈ W183PglFixed σ := by
      intro i hi g
      apply Subtype.ext
      rw [hLmem]
      exact hi _ (e.symm g).2
    have hFJ' : fixedIn ρ L I ≤ J.map I.subtype := by
      rintro i ⟨hiI, hiF⟩
      exact ⟨⟨i, hiI⟩, hFJ (hfixed ⟨i, hiI⟩ hiF), rfl⟩
    rcases hmin (J.map I.subtype) (by rintro _ ⟨j, -, rfl⟩; exact j.2) hJ'inv hFJ' with h | h
    · left
      apply le_antisymm
      · intro j hj g
        have hjF : (j : V) ∈ fixedIn ρ L I := by
          rw [← h]
          exact ⟨j, hj, rfl⟩
        apply Subtype.ext
        rw [hLmem]
        exact hjF.2 _ (e.symm g).2
      · exact hFJ
    · right
      rw [eq_top_iff]
      intro i _
      have : (i : V) ∈ J.map I.subtype := by
        rw [h]
        exact i.2
      obtain ⟨j, hj, hji⟩ := this
      have : j = i := Subtype.ext hji
      rwa [this] at hj

private theorem w183Pgl_conj_quad (ρ : Q →* MulAut V) {l₁ l₂ g : Q}
    (hq : ∀ v : V, ρ l₂ (ρ l₁ v * v⁻¹) = ρ l₁ v * v⁻¹) (i : V) :
    ρ (g * l₂ * g⁻¹) (ρ (g * l₁ * g⁻¹) i * i⁻¹) = ρ (g * l₁ * g⁻¹) i * i⁻¹ := by
  have hρc : ∀ (l : Q) (v : V), ρ (g * l * g⁻¹) v = ρ g (ρ l (ρ g⁻¹ v)) := fun l v => by
    rw [map_mul, map_mul]
    rfl
  have hgi : ρ g (ρ g⁻¹ i) = i := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hgi' : ∀ v : V, ρ g⁻¹ (ρ g v) = v := fun v => by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hEmul : ∀ a b : V, ρ g⁻¹ (a * b) = ρ g⁻¹ a * ρ g⁻¹ b := fun a b => map_mul (ρ g⁻¹) a b
  have hEinv : ∀ a : V, ρ g⁻¹ a⁻¹ = (ρ g⁻¹ a)⁻¹ := fun a => map_inv (ρ g⁻¹) a
  have hw := hq (ρ g⁻¹ i)
  calc ρ (g * l₂ * g⁻¹) (ρ (g * l₁ * g⁻¹) i * i⁻¹)
      = ρ g (ρ l₂ (ρ g⁻¹ (ρ (g * l₁ * g⁻¹) i * i⁻¹))) := hρc _ _
    _ = ρ g (ρ l₂ (ρ l₁ (ρ g⁻¹ i) * (ρ g⁻¹ i)⁻¹)) := by
        rw [hEmul, hEinv, hρc l₁ i, hgi']
    _ = ρ g (ρ l₁ (ρ g⁻¹ i) * (ρ g⁻¹ i)⁻¹) := by rw [hw]
    _ = ρ (g * l₁ * g⁻¹) i * i⁻¹ := by
        rw [map_mul (ρ g), map_inv (ρ g), hρc l₁ i, hgi]

theorem w183Pgl_quad_pairs (ρ : Q →* MulAut V) {L A : Subgroup Q} [L.Normal]
    (hcent : Subgroup.centralizer (L : Set Q) ≤ L) (e : ↥L ≃* GL (Fin 3) (ZMod 2)) [Finite Q]
    (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A) (hAL : A ≤ L) (hq : IsQuadraticOn ρ A)
    {g : Q} (hg : g ∉ L) {I : Subgroup V} (σ : GL (Fin 3) (ZMod 2) →* MulAut ↥I)
    (hσ : ∀ (l : ↥L) (i : ↥I), ((σ (e l) i : ↥I) : V) = ρ (l : Q) (i : V)) :
    (∃ x y : GL (Fin 3) (ZMod 2), W183PglAxis x y ∧ W183PglQuad σ x y) ∧
      ∃ x y : GL (Fin 3) (ZMod 2), W183PglAxis x y ∧
        W183PglQuad (σ.comp w183PglTau.toMonoidHom) x y := by
  classical
  obtain ⟨a, b, ha1, hb1, hab, ha2, hb2, hcomm, hab1⟩ :=
    CFSG.ComponentClassification.ElementaryAbelianFour.exists_distinct_involutions A hAe hA
  let a₀ : ↥L := ⟨(a : Q), hAL a.2⟩
  let b₀ : ↥L := ⟨(b : Q), hAL b.2⟩
  have hcoe_a : ((a₀ : ↥L) : Q) = (a : Q) := rfl
  have hcoe_b : ((b₀ : ↥L) : Q) = (b : Q) := rfl
  set x : GL (Fin 3) (ZMod 2) := e a₀ with hx
  set y : GL (Fin 3) (ZMod 2) := e b₀ with hy
  have ha1' : (a : Q) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : (b : Q) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hab' : (a : Q) ≠ (b : Q) := fun h => hab (Subtype.ext h)
  have ha2' : (a : Q) * (a : Q) = 1 := congrArg Subtype.val ha2
  have hb2' : (b : Q) * (b : Q) = 1 := congrArg Subtype.val hb2
  have hcomm' : (a : Q) * (b : Q) = (b : Q) * (a : Q) := congrArg Subtype.val hcomm.eq
  have hKl : W183PglKlein x y := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have : a₀ = 1 := e.injective (h.trans e.map_one.symm)
      exact ha1' (congrArg Subtype.val this)
    · intro h
      have : b₀ = 1 := e.injective (h.trans e.map_one.symm)
      exact hb1' (congrArg Subtype.val this)
    · intro h
      have : a₀ = b₀ := e.injective h
      have h2 : ((a₀ : ↥L) : Q) = ((b₀ : ↥L) : Q) := congrArg Subtype.val this
      exact hab' h2
    · rw [hx, ← map_mul]
      have : a₀ * a₀ = 1 := Subtype.ext ha2'
      rw [this, e.map_one]
    · rw [hy, ← map_mul]
      have : b₀ * b₀ = 1 := Subtype.ext hb2'
      rw [this, e.map_one]
    · rw [hx, hy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm'
  have hquadA : ∀ (l₁ l₂ : ↥L), (l₁ : Q) ∈ A → (l₂ : Q) ∈ A → ∀ i : ↥I,
      σ (e l₂) (σ (e l₁) i * i⁻¹) = σ (e l₁) i * i⁻¹ := by
    intro l₁ l₂ h₁ h₂ i
    apply Subtype.ext
    have key := hq l₁ h₁ l₂ h₂ (i : V)
    change ((σ (e l₂) (σ (e l₁) i * i⁻¹) : ↥I) : V) = ((σ (e l₁) i * i⁻¹ : ↥I) : V)
    rw [hσ, Subgroup.coe_mul, Subgroup.coe_inv, hσ]
    exact key
  have hmemx : ∀ c : GL (Fin 3) (ZMod 2), (c = x ∨ c = y ∨ c = x * y) →
      ∃ l : ↥L, (l : Q) ∈ A ∧ c = e l := by
    rintro c (rfl | rfl | rfl)
    · exact ⟨a₀, a.2, rfl⟩
    · exact ⟨b₀, b.2, rfl⟩
    · exact ⟨a₀ * b₀, A.mul_mem a.2 b.2, (map_mul e a₀ b₀).symm⟩
  have hQσ : W183PglQuad σ x y := by
    intro c d hc hd i
    obtain ⟨l₁, h₁, rfl⟩ := hmemx c hc
    obtain ⟨l₂, h₂, rfl⟩ := hmemx d hd
    exact hquadA l₁ l₂ h₁ h₂ i
  let α : MulAut (GL (Fin 3) (ZMod 2)) := MulAut.congr e (MulAut.conjNormal (H := L) g)
  have hαe : ∀ l : ↥L, α (e l) = e (MulAut.conjNormal (H := L) g l) := fun l => by
    simp [α, MulAut.congr_apply]
  have hconjcoe : ∀ l : ↥L, ((MulAut.conjNormal (H := L) g l : ↥L) : Q) = g * (l : Q) * g⁻¹ :=
    fun l => MulAut.conjNormal_apply g l
  have hαout : ∀ s : GL (Fin 3) (ZMod 2), α ≠ MulAut.conj s := by
    intro s hs
    have hg' : g⁻¹ ∉ L := fun h => hg (inv_mem_iff.mp h)
    let e₂ : ↥L ≃* GL (Fin 3) (ZMod 2) := (MulAut.conjNormal (H := L) g).trans e
    have he₂ : ∀ (l l' : ↥L), (l' : Q) = g⁻¹⁻¹ * (l : Q) * g⁻¹ → e₂ l = e l' := by
      intro l l' hl'
      have : MulAut.conjNormal (H := L) g l = l' :=
        Subtype.ext (by rw [hconjcoe, hl', inv_inv])
      show e (MulAut.conjNormal (H := L) g l) = e l'
      rw [this]
    obtain ⟨l, hl⟩ := w183Pgl_outer_not_inner hcent hg' e e₂ he₂ s
    apply hl
    have := congrArg (fun φ : MulAut (GL (Fin 3) (ZMod 2)) => φ (e l)) hs
    simp only [hαe, MulAut.conj_apply] at this
    exact this
  obtain ⟨s, hs⟩ : ∃ s : GL (Fin 3) (ZMod 2),
      α = MulAut.conj s *
        CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 (ZMod 2) := by
    rcases CFSG.QuasithinUnique.Setup.Family.aut_GL32_cases α with ⟨s, hs⟩ | h
    · exact absurd hs (hαout s)
    · exact h
  have hαapp : ∀ c : GL (Fin 3) (ZMod 2), α c = s * w183PglTau c * s⁻¹ := fun c => by
    rw [hs]
    rfl
  set z : GL (Fin 3) (ZMod 2) := α x with hz
  set w : GL (Fin 3) (ZMod 2) := α y with hw
  have hmemz : ∀ c : GL (Fin 3) (ZMod 2), (c = z ∨ c = w ∨ c = z * w) →
      ∃ l : ↥L, (l : Q) ∈ A ∧ c = e (MulAut.conjNormal (H := L) g l) := by
    rintro c (rfl | rfl | rfl)
    · exact ⟨a₀, a.2, hαe a₀⟩
    · exact ⟨b₀, b.2, hαe b₀⟩
    · refine ⟨a₀ * b₀, A.mul_mem a.2 b.2, ?_⟩
      have h1 : x * y = e (a₀ * b₀) := (map_mul e a₀ b₀).symm
      calc α x * α y = α (x * y) := (map_mul α x y).symm
        _ = α (e (a₀ * b₀)) := by rw [h1]
        _ = e (MulAut.conjNormal (H := L) g (a₀ * b₀)) := hαe _
  have hQz : W183PglQuad σ z w := by
    intro c d hc hd i
    obtain ⟨l₁, h₁, rfl⟩ := hmemz c hc
    obtain ⟨l₂, h₂, rfl⟩ := hmemz d hd
    apply Subtype.ext
    have key := w183Pgl_conj_quad ρ (g := g) (hq l₁ h₁ l₂ h₂) (i : V)
    simp only [hσ, Subgroup.coe_mul, Subgroup.coe_inv, hconjcoe]
    exact key
  have hz' : z = s * w183PglTau x * s⁻¹ := hαapp x
  have hw' : w = s * w183PglTau y * s⁻¹ := hαapp y
  have hττ : ∀ c : GL (Fin 3) (ZMod 2), w183PglTau (w183PglTau c) = c := fun c =>
    Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose c
  have htz : w183PglTau z = w183PglTau s * x * (w183PglTau s)⁻¹ := by
    rw [hz', map_mul, map_mul, map_inv, hττ]
  have htw : w183PglTau w = w183PglTau s * y * (w183PglTau s)⁻¹ := by
    rw [hw', map_mul, map_mul, map_inv, hττ]
  rcases w183Pgl_axis_or_centre hKl with hAx | hAx
  · refine ⟨⟨x, y, hAx, hQσ⟩, ⟨w183PglTau z, w183PglTau w, ?_, ?_⟩⟩
    · rw [htz, htw]
      exact w183Pgl_axis_conj hAx _
    · apply w183Pgl_quad_comp_tau
      rw [hττ, hττ]
      exact hQz
  · refine ⟨⟨z, w, ?_, hQz⟩, ⟨w183PglTau x, w183PglTau y, hAx, ?_⟩⟩
    · rw [hz', hw']
      exact w183Pgl_axis_conj hAx s
    · apply w183Pgl_quad_comp_tau
      rw [hττ, hττ]
      exact hQσ

theorem w183Pgl_natural [Finite Q] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (ρ : Q →* MulAut V)
    {L A : Subgroup Q} [L.Normal] (hcent : Subgroup.centralizer (L : Set Q) ≤ L)
    (e : ↥L ≃* GL (Fin 3) (ZMod 2)) (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A)
    (hAL : A ≤ L) (hq : IsQuadraticOn ρ A) {g : Q} (hg : g ∉ L) {I : Subgroup V}
    (hI : IsIrr ρ L I) : IsNaturalL3Two ρ L I := by
  have hLI : ∀ l ∈ L, ∀ i ∈ I, ρ l i ∈ I := fun l hl i hi => hI.map_mem hl hi
  obtain ⟨σ, hσ⟩ := w183Pgl_restrict ρ hLI e
  obtain ⟨hnt, hgen, hirr⟩ := w183Pgl_irr_abstract ρ hI e σ hσ
  obtain ⟨hq₁, hq₂⟩ := w183Pgl_quad_pairs ρ hcent e hA hAe hAL hq hg σ hσ
  have hIexp : ∀ x : ↥I, x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa [Subgroup.coe_pow] using hV (x : V))
  have hact : ∀ (l : ↥L) (i j : ↥I), (j : V) = ρ (l : Q) (i : V) → j = σ (e l) i :=
    fun l i j hj => Subtype.ext (by rw [hσ]; exact hj)
  rcases w183Pgl_natural_abstract hIexp σ hnt hgen hirr hq₁ hq₂ with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · refine ⟨e, φ, fun l i j hj => ?_⟩
    rw [hact l i j hj]
    exact hφ (e l) i
  · refine ⟨e.trans w183PglTau, φ, fun l i j hj => ?_⟩
    rw [hact l i j hj]
    exact hφ (e l) i

end Stage

theorem asch6_6PglMod : Asch6_6PglMod := by
  intro Q _ _ V _ _ hV ρ hρ L A hL hA hAe hq hQ hAL I hI
  obtain ⟨hL2, hQcard, hLcard⟩ := w183_pgl2Seven_fstar hQ hL
  have hLn : L.Normal := by
    rw [← hL]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal Q
  have hcent : Subgroup.centralizer (L : Set Q) ≤ L := by
    rw [← hL]
    exact CFSG.ComponentClassification.GeneralizedFitting.centralizer_le Q
  have hidx : L.index = 2 := by
    have h := Subgroup.card_mul_index L
    rw [hQcard, hLcard] at h
    omega
  obtain ⟨e⟩ := w183Pgl_equiv_L hL2
  have hLI : ∀ l ∈ L, ∀ i ∈ I, ρ l i ∈ I := fun l hl i hi => hI.map_mem hl hi
  have hex : ∃ g₀ : Q, g₀ ∉ L := by
    by_contra hcon
    have htop : L = ⊤ := eq_top_iff.2 fun x _ => by
      by_contra hx
      exact hcon ⟨x, hx⟩
    rw [htop, Subgroup.index_top] at hidx
    omega
  obtain ⟨g₀, hg₀⟩ := hex
  haveI := hLn
  have hnat : IsNaturalL3Two ρ L I := w183Pgl_natural hV ρ hcent e hA hAe hAL hq hg₀ hI
  refine ⟨hnat, fun g hg => ?_⟩
  obtain ⟨hd, hp⟩ := w183Pgl_outer ρ hcent hLI hnat hg
  exact ⟨w183Pgl_sup_eq ρ hidx hLI hg, hd, hp⟩

end CFSG.LocalAnalysis.WeakClosure81

end
