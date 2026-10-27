module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise Matrix

structure w1369_ta_Proj {Q : Type} [CommGroup Q] {k : ℕ} (I : Fin k → Subgroup Q)
    (Λ : Subgroup (MulAut Q)) where
  e : Fin k → Q →* Q
  e_mem : ∀ i x, e i x ∈ I i
  e_self : ∀ i x (hx : x ∈ I i), e i x = x
  e_other : ∀ i j, j ≠ i → ∀ x (hx : x ∈ I j), e i x = 1
  e_prod : ∀ x, ∏ i, e i x = x
  e_equiv : ∀ i, ∀ g ∈ Λ, ∀ x, e i (g x) = g (e i x)

noncomputable def w1369_ta_mkProj {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q}
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hspan : ⨆ i, I i = ⊤)
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥) :
    w1369_ta_Proj I Λ := by
  classical
  have hcomm : Pairwise fun i j : Fin k => ∀ x y : Q, x ∈ I i → y ∈ I j → Commute x y :=
    fun i j _ x y _ _ => mul_comm x y
  let φ : (∀ i : Fin k, I i) →* Q := Subgroup.noncommPiCoprod hcomm
  have hInd : iSupIndep I := iSupIndep_def.mpr (fun i => disjoint_iff.mpr (hind i))
  have hφinj : Function.Injective φ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hInd
  have hφrange : φ.range = ⊤ := by
    rw [Subgroup.noncommPiCoprod_range, hspan]
  have hφsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hφrange
  let e : (∀ i : Fin k, I i) ≃* Q := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hφprod : ∀ f : (∀ i : Fin k, I i), φ f = ∏ i, (f i : Q) := by
    intro f
    rw [Subgroup.noncommPiCoprod_apply]
    exact Finset.noncommProd_eq_prod _ _
  let ei (i : Fin k) : Q →* I i :=
    (Pi.evalMonoidHom (fun j => I j) i).comp e.symm.toMonoidHom
  let eQ (i : Fin k) : Q →* Q := (I i).subtype.comp (ei i)
  have hmul : ∀ (i : Fin k) (x : Q) (hx : x ∈ I i), e.symm x = Pi.mulSingle i ⟨x, hx⟩ := by
    intro i x hx
    apply e.injective
    rw [e.apply_symm_apply]
    change x = φ (Pi.mulSingle i ⟨x, hx⟩)
    rw [Subgroup.noncommPiCoprod_mulSingle]
  have hself : ∀ (i : Fin k) (x : Q) (hx : x ∈ I i), eQ i x = x := by
    intro i x hx
    change (I i).subtype ((Pi.evalMonoidHom (fun j => I j) i) (e.symm x)) = x
    rw [hmul i x hx]
    simp
  have hother : ∀ (i j : Fin k), j ≠ i → ∀ (x : Q) (hx : x ∈ I j), eQ i x = 1 := by
    intro i j hij x hx
    change (I i).subtype ((Pi.evalMonoidHom (fun j => I j) i) (e.symm x)) = 1
    rw [hmul j x hx]
    simp [Pi.mulSingle_eq_of_ne (Ne.symm hij)]
  have hequiv : ∀ (i : Fin k) (g : MulAut Q), g ∈ Λ → ∀ x, eQ i (g x) = g (eQ i x) := by
    intro i g hg x
    have hgPi : ∀ f : (∀ j : Fin k, I j),
        φ (fun j => ⟨g (f j : Q), hstab j g hg (f j : Q) (f j).2⟩) = g (φ f) := by
      intro f
      rw [hφprod, hφprod]
      exact (map_prod (g : Q →* Q) (fun j => (f j : Q)) Finset.univ).symm
    have hsymm : e.symm (g x) =
        fun j => ⟨g ((e.symm x) j : Q), hstab j g hg ((e.symm x) j : Q) ((e.symm x j).2)⟩ := by
      apply e.injective
      rw [e.apply_symm_apply]
      change g x = φ (fun j => ⟨g ((e.symm x) j : Q),
        hstab j g hg ((e.symm x) j : Q) ((e.symm x j).2)⟩)
      rw [hgPi]
      have h2 : φ (e.symm x) = x := e.apply_symm_apply x
      rw [h2]
    change (I i).subtype ((Pi.evalMonoidHom (fun j => I j) i) (e.symm (g x))) =
      g ((I i).subtype ((Pi.evalMonoidHom (fun j => I j) i) (e.symm x)))
    rw [hsymm]
    rfl
  have hprod : ∀ x : Q, ∏ i : Fin k, eQ i x = x := by
    intro x
    have h : φ (e.symm x) = x := e.apply_symm_apply x
    rw [hφprod] at h
    simpa [eQ, ei] using h
  exact { e := eQ
          e_mem := fun i x => (ei i x).2
          e_self := hself
          e_other := hother
          e_prod := hprod
          e_equiv := hequiv }

abbrev w1369_ta_IsSimple {Q : Type} [CommGroup Q] (Λ : Subgroup (MulAut Q))
    (S : Subgroup Q) : Prop :=
  S ≠ ⊥ ∧ StableUnder Λ S ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ S → J = ⊥ ∨ J = S

lemma w1369_simple_map {Q : Type} [CommGroup Q] {Λ N : Subgroup (MulAut Q)}
    (hnorm : ∀ n ∈ N, ∀ l ∈ Λ, n * l * n⁻¹ ∈ Λ)
    {S : Subgroup Q} (hS : w1369_ta_IsSimple Λ S) {n : MulAut Q} (hn : n ∈ N) :
    w1369_ta_IsSimple Λ (S.map n.toMonoidHom) := by
  have happ : ∀ (a : MulAut Q) (x : Q), a (a⁻¹ x) = x := fun a x => MulEquiv.apply_symm_apply a x
  have hinv : ∀ (a : MulAut Q) (x : Q), a⁻¹ (a x) = x := fun a x => MulEquiv.symm_apply_apply a x
  have hmul : ∀ (a b : MulAut Q) (x : Q), (a * b) x = a (b x) := fun a b x => rfl
  have hiff : ∀ l ∈ Λ, n⁻¹ * l * n ∈ Λ := fun l hl => hnorm n⁻¹ (N.inv_mem hn) l hl
  have hstab : StableUnder Λ (S.map n.toMonoidHom) := by
    intro l hl x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨(n⁻¹ * l * n) y, hS.2.1 _ (hiff l hl) y hy, ?_⟩
    rw [hmul, hmul]
    exact happ n (l (n y))
  refine ⟨?_, hstab, ?_⟩
  · intro hbot
    have : S ≤ ⊥ := by
      intro y hy
      have : n y ∈ S.map n.toMonoidHom := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      rw [hbot] at this
      simpa using this
    exact hS.1 (le_bot_iff.mp this)
  · intro J hJ hJle
    have hJstab : StableUnder Λ (J.map (n⁻¹ : MulAut Q).toMonoidHom) := by
      intro l hl x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨(n * l * n⁻¹) y, hJ _ (hnorm n hn l hl) y hy, ?_⟩
      rw [hmul, hmul]
      exact hinv n (l ((n⁻¹ : MulAut Q) y))
    have hJle' : J.map (n⁻¹ : MulAut Q).toMonoidHom ≤ S := by
      rintro x ⟨y, hy, rfl⟩
      have hy' : y ∈ S.map n.toMonoidHom := hJle hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
      rw [← hzy]
      change (n⁻¹ : MulAut Q) (n z) ∈ S
      rw [hinv n z]
      exact hz
    rcases hS.2.2 _ hJstab hJle' with h | h
    · left
      rw [← le_bot_iff]
      intro y hy
      have hmem : (n⁻¹ : MulAut Q) y ∈ J.map (n⁻¹ : MulAut Q).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      rw [h] at hmem
      have h1 : (n⁻¹ : MulAut Q) y = 1 := by simpa using hmem
      calc y = n ((n⁻¹ : MulAut Q) y) := (happ n y).symm
        _ = n 1 := by rw [h1]
        _ = 1 := map_one n
    · right
      rw [← h]
      have hcomp : (MulEquiv.toMonoidHom n).comp (MulEquiv.toMonoidHom n⁻¹)
          = MonoidHom.id Q := by
        ext y
        exact happ n y
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]

lemma w1369_orbit_span {Q : Type} [CommGroup Q] {Λ N : Subgroup (MulAut Q)}
    (hirr : ∀ M : Subgroup Q, StableUnder N M → M = ⊥ ∨ M = ⊤)
    {S : Subgroup Q} (hS : S ≠ ⊥) :
    (⨆ n : N, S.map ((n : MulAut Q)).toMonoidHom) = ⊤ := by
  classical
  set M : Subgroup Q := ⨆ n : N, S.map ((n : MulAut Q)).toMonoidHom with hM
  have hle : ∀ m : N, M.map ((m : MulAut Q)).toMonoidHom ≤ M := by
    intro m
    rw [hM, Subgroup.map_iSup]
    apply iSup_le
    intro n
    have hcomp : (S.map ((n : MulAut Q)).toMonoidHom).map ((m : MulAut Q)).toMonoidHom
        = S.map (((m * n : N) : MulAut Q)).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [hcomp]
    exact le_iSup (fun n : N => S.map ((n : MulAut Q)).toMonoidHom) (m * n)
  have hstable : StableUnder N M := by
    intro m hm x hx
    exact hle ⟨m, hm⟩ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hne : M ≠ ⊥ := by
    intro hbot
    have hle_one : S.map (((1 : N) : MulAut Q)).toMonoidHom = S := Subgroup.map_id S
    have h1 : S ≤ M := by
      have h2 : S.map (((1 : N) : MulAut Q)).toMonoidHom ≤ M := by
        rw [hM]
        exact le_iSup (fun n : N => S.map ((n : MulAut Q)).toMonoidHom) (1 : N)
      rw [hle_one] at h2
      exact h2
    rw [hbot] at h1
    exact hS (le_bot_iff.mp h1)
  exact (hirr M hstable).resolve_left hne

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
