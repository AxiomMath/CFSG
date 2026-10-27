module

public import CFSG.Quasithin.EmptyFaithful.LRed2EbA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7A5
public import CFSG.Quasithin.Background.D36GluedL24Model
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13AltModule
public import CFSG.Quasithin.Background.F6CatSmall
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Suz.Simple
public import Certificates.Data.A5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

theorem eq_one_of_fixed_of_binaryNaturalSL {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} (hI : BinaryNaturalSL L I ⊥ 2 2) {z : MulAut W} (hz : z ∈ L)
    (hz3 : orderOf z = 3) {u : W} (hu : u ∈ I) (hzu : z u = u) : u = 1 := by
  obtain ⟨K, hKfield, hKfin, hKcard, π, hπ⟩ := hI
  letI := hKfield
  haveI := hKfin
  have hbot : u ∈ (⊥ : Subgroup W) :=
    lred2_natural_fixed (V := W) (L := L) (U := I) (Z := ⊥) hKcard hπ hz hz3 hu hzu
  exact Subgroup.mem_bot.mp hbot

theorem exists_fixed_of_alternatingNatural {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} (hI : AlternatingNatural L I ⊥ 5) :
    ∃ z ∈ L, orderOf z = 3 ∧ ∃ u ∈ I, u ≠ 1 ∧ z u = u := by
  obtain ⟨π, ε, -, hHU, heq⟩ := s15_T7_exists_iso hI
  let c : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2
  have hc : c ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    norm_num
  let γ : ↥(alternatingGroup (Fin 5)) := ⟨c, hc⟩
  have hγ3 : γ ^ 3 = 1 := by
    apply Subtype.ext
    change (Equiv.swap 0 1 * Equiv.swap 1 2) ^ 3 = 1
    decide +kernel
  have hγ1 : γ ≠ 1 := by
    intro h
    have h0 := congrArg (fun p : Equiv.Perm (Fin 5) => p 0) (congrArg Subtype.val h)
    simp [γ, c] at h0
    exact (by decide +kernel : ((Equiv.swap 0 1) ((Equiv.swap 1 2) 0) : Fin 5) ≠ 0) h0
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ₀ hγ₀
    have hact : G6.coreAct 5 γ₀ = 1 := by
      apply MulEquiv.ext
      intro w
      obtain ⟨u, rfl⟩ := ε.surjective w
      have hmem : ((π γ₀ : ↥L) : MulAut W) (u : W) ∈ I := hHU (π γ₀) u u.2
      have h1 := heq γ₀ u hmem
      have h2 : ((π γ₀ : ↥L) : MulAut W) (u : W) = (u : W) := by rw [hγ₀]; rfl
      have h3 : (⟨((π γ₀ : ↥L) : MulAut W) (u : W), hmem⟩ : ↥I) = u := Subtype.ext h2
      rw [h3] at h1
      exact h1.symm
    exact Subtype.ext (s15_T7_coreAct_injective (hact.trans (map_one (G6.coreAct 5)).symm))
  let v : ↥(G6.coreMod 5) :=
    ⟨Multiplicative.ofAdd (Pi.single 3 1 + Pi.single 4 1), by
      rw [G6.mem_coreMod]
      decide +kernel⟩
  have hv1 : v ≠ 1 := by decide +kernel
  have hvfix : G6.coreAct 5 γ v = v := by
    apply Subtype.ext
    rw [G6.coreAct_coe]
    change G6.permAct 5 (Equiv.swap 0 1 * Equiv.swap 1 2)
      (Multiplicative.ofAdd (Pi.single 3 1 + Pi.single 4 1)) =
      Multiplicative.ofAdd (Pi.single 3 1 + Pi.single 4 1)
    decide +kernel
  let u : ↥I := ε.symm v
  refine ⟨((π γ : ↥L) : MulAut W), (π γ).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    refine orderOf_eq_prime ?_ ?_
    · calc
        (π γ) ^ 3 = π (γ ^ 3) := (map_pow π γ 3).symm
        _ = 1 := by rw [hγ3, map_one]
    · exact fun h => hγ1 (hinj (h.trans (map_one π).symm))
  · refine ⟨u, u.2, ?_, ?_⟩
    · intro hu1
      have hε : ε u = v := by simp [u]
      have : v = 1 := by
        rw [← hε]
        rw [show u = 1 from Subtype.ext hu1, map_one]
      exact hv1 this
    · have hmem : ((π γ : ↥L) : MulAut W) (u : W) ∈ I := hHU (π γ) u u.2
      have hkey := heq γ u hmem
      have hfix : G6.coreAct 5 γ (ε u) = ε u := by
        rw [show ε u = v from by simp [u]]
        exact hvfix
      have hsub : (⟨((π γ : ↥L) : MulAut W) (u : W), hmem⟩ : ↥I) = u := by
        apply ε.injective
        rw [hkey, hfix]
      exact congrArg Subtype.val hsub

theorem exists_endo_of_binaryNaturalSL {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} (hI : BinaryNaturalSL L I ⊥ 2 2) :
    ∃ f : ↥I →* W, (∀ u, f u ∈ I) ∧ (∀ l ∈ L, ∀ u u' : ↥I, (u' : W) = l u → f u' = l (f u)) ∧
      (∃ u, f u ≠ 1) ∧ ∃ u, f u ≠ (u : W) := by
  classical
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, -, ⟨D⟩⟩ := natural24_data hI
  letI := hKfield
  haveI := hKfin
  haveI := hKchar
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by simpa [Nat.card_eq_fintype_card] using hKcard
  have hsub : Fintype.card {x : K // x ≠ 0} = 3 := by
    have h := Fintype.card_subtype_compl (α := K) (p := fun x : K => x = 0)
    simpa [hcard] using h
  have hlt : 1 < Fintype.card {x : K // x ≠ 0} := by rw [hsub]; norm_num
  obtain ⟨ω, hω⟩ := Fintype.exists_ne_of_one_lt_card hlt (⟨1, one_ne_zero⟩ : {x : K // x ≠ 0})
  have hω0 : (ω : K) ≠ 0 := ω.2
  have hω1 : (ω : K) ≠ 1 := fun h => hω (Subtype.ext h)
  have hker : ∀ u : ↥I, D.φ u = 1 ↔ u = 1 := by
    intro u
    rw [D.φ_ker u]
    simp
  have hinjφ : Function.Injective D.φ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact (hker u).mp hu
  let e : ↥I ≃* Multiplicative (Fin 2 → K) := MulEquiv.ofBijective D.φ ⟨hinjφ, D.φ_surj⟩
  let s : Multiplicative (Fin 2 → K) →* Multiplicative (Fin 2 → K) :=
    { toFun := fun x => Multiplicative.ofAdd ((ω : K) • Multiplicative.toAdd x)
      map_one' := by
        apply Multiplicative.toAdd.injective
        simp
      map_mul' := by
        intro x y
        apply Multiplicative.toAdd.injective
        simp [smul_add] }
  let g : ↥I →* ↥I := e.symm.toMonoidHom.comp (s.comp e.toMonoidHom)
  let f : ↥I →* W := I.subtype.comp g
  have hgs : ∀ x : ↥I, e (g x) = s (e x) := fun x => by simp [g]
  have hgω : ∀ x : ↥I, Multiplicative.toAdd (e (g x)) =
      (ω : K) • Multiplicative.toAdd (e x) := by
    intro x
    rw [hgs x]
    simp [s]
  refine ⟨f, fun u => (g u).2, ?_, ?_, ?_⟩
  · intro l hl u u' hu'
    have hmem : (l : MulAut W) (u : W) ∈ I := D.H_U ⟨l, hl⟩ u u.2
    have hmemg : (l : MulAut W) ((g u : ↥I) : W) ∈ I := D.H_U ⟨l, hl⟩ (g u) (g u).2
    have hu'eq : u' = ⟨(l : MulAut W) (u : W), hmem⟩ := Subtype.ext hu'
    rw [hu'eq]
    have hφy : e ⟨(l : MulAut W) (u : W), hmem⟩ =
        Multiplicative.ofAdd (D.M ⟨l, hl⟩ *ᵥ Multiplicative.toAdd (e u)) := by
      show D.φ ⟨(l : MulAut W) (u : W), hmem⟩ = _
      exact D.φ_act ⟨l, hl⟩ u hmem
    have hφg : e ⟨(l : MulAut W) ((g u : ↥I) : W), hmemg⟩ =
        Multiplicative.ofAdd (D.M ⟨l, hl⟩ *ᵥ Multiplicative.toAdd (e (g u))) := by
      show D.φ ⟨(l : MulAut W) ((g u : ↥I) : W), hmemg⟩ = _
      exact D.φ_act ⟨l, hl⟩ (g u) hmemg
    have hL : e (g ⟨(l : MulAut W) (u : W), hmem⟩) =
        Multiplicative.ofAdd ((ω : K) •
          (D.M ⟨l, hl⟩ *ᵥ Multiplicative.toAdd (e u))) := by
      rw [hgs, hφy]
      rfl
    have hR : e ⟨(l : MulAut W) ((g u : ↥I) : W), hmemg⟩ =
        Multiplicative.ofAdd ((ω : K) •
          (D.M ⟨l, hl⟩ *ᵥ Multiplicative.toAdd (e u))) := by
      rw [hφg, hgω u, Matrix.mulVec_smul]
    have hkey : g ⟨(l : MulAut W) (u : W), hmem⟩ =
        ⟨(l : MulAut W) ((g u : ↥I) : W), hmemg⟩ := by
      apply e.injective
      rw [hL, hR]
    exact congrArg Subtype.val hkey
  · let v₀ : Fin 2 → K := Pi.single 0 1
    have hv₀ : v₀ ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      simp [v₀] at h0
    obtain ⟨u, hu⟩ := D.φ_surj (Multiplicative.ofAdd v₀)
    refine ⟨u, ?_⟩
    intro hf
    have hgu : g u = 1 := Subtype.ext hf
    have h1 : Multiplicative.toAdd (e (g u)) = (ω : K) • v₀ := by
      rw [hgω u, show e u = Multiplicative.ofAdd v₀ from hu]
      rfl
    have h2 : Multiplicative.toAdd (e (g u)) = 0 := by rw [hgu, map_one]; rfl
    have h3 : (ω : K) • v₀ = 0 := by rw [← h1, h2]
    exact (smul_ne_zero hω0 hv₀) h3
  · let v₀ : Fin 2 → K := Pi.single 0 1
    have hv₀ : v₀ ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      simp [v₀] at h0
    obtain ⟨u, hu⟩ := D.φ_surj (Multiplicative.ofAdd v₀)
    refine ⟨u, ?_⟩
    intro hf
    have hgu : g u = u := Subtype.ext hf
    have h1 : (ω : K) • v₀ = v₀ := by
      have h := hgω u
      rw [hgu, show e u = Multiplicative.ofAdd v₀ from hu] at h
      exact h.symm
    have h2 : ((ω : K) - 1) • v₀ = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    have hωm1 : (ω : K) - 1 ≠ 0 := sub_ne_zero.mpr hω1
    exact (smul_ne_zero hωm1 hv₀) h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
