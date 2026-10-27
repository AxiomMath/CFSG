module

public import CFSG.LocalAnalysis.StandardType.GGTBE6Torus
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
public import CFSG.LocalAnalysis.StandardType.GGTDModelDefs
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS4aAuxA
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAAux

public noncomputable section

namespace CFSG.StandardType.TBE6

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.StandardType.E6ThreeModel CFSG.StandardType.TableBExc.E6Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {K L : Type} [Field K] [Finite K] [Group L] [Finite L]
  {A : Subgroup (MulAut L)}
  (ρ : MulAut L →* MulAut (adjointGroup .E6 K))
  (e : Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1)))
  (φ : e6Data_valid.minGroup K →* L)
  (n : Fin Tag.E6.rank → L)
  (hn : ∀ i, MulAut.conj (n i) ∈ Subgroup.normalizer (A : Set (MulAut L)))

@[expose] def witness : GGTorusTorWit (Nat.card K - 1) 6 L A where
  T := torus ρ
  α := root ρ e
  cor := coroot e φ
  n := n
  hn := hn
  Tsc := (φ.comp (minTorus e6Data_valid K)).range

omit [Finite L] in
theorem cartan_pairing
    (ψ : L →* adjointGroup .E6 K) (hψ : Function.Surjective ψ)
    (hρ : ∀ a l, ρ a (ψ l) = ψ (a l))
    (hφ : ∀ x, ψ (φ x) = e6Isogeny K x)
    (i j : Fin 6) (s : Multiplicative (ZMod (Nat.card K - 1))) :
    root ρ e i (MulAut.conj (coroot e φ j s)) = s ^ CartanMatrix.E₆ i j := by
  rw [root_coroot ψ φ hφ ρ hρ hψ e j i]
  congr 1
  change Tag.cartanE 6 j i = CartanMatrix.E₆ i j
  rw [cartanE_eq]
  change CartanMatrix.E 6 j i = CartanMatrix.E 6 i j
  unfold CartanMatrix.E
  simp only [Matrix.of_apply]
  split_ifs <;> omega

omit
  [Finite K] [Finite L] in
theorem root_nontrivial
    {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {Φ : A →* Multiplicative (Fin 6 → ZMod 3)}
    (hΦ : ∀ a : A, (eFrame K ζ hζ).diag (Φ a) = ρ a)
    (hr : Φ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6)
    (i : Fin 6) : ∃ a ∈ A, root ρ e i a ≠ 1 := by
  have hv : (fun _ : Fin Tag.E6.rank => (1 : ZMod 3)) ∈ NoOffRest.hypE6 := by
    rw [NoOffRest.mem_hypE6]
    decide
  have hm : Multiplicative.ofAdd (fun _ : Fin 6 => (1 : ZMod 3)) ∈ Φ.range := by
    rcases hr with h | h
    · rw [h]; exact Subgroup.mem_top _
    · exact (h _).2 hv
  obtain ⟨a, ha⟩ := hm
  have hρa : ρ a = rootDiagAutHom .E6 K (fun _ => ζ) := by
    rw [← hΦ a, ha]
    change rootDiagAutHom .E6 K (zetaVec ζ hζ (fun _ => (1 : ZMod 3))) = _
    congr 1
    funext j
    rw [zetaVec_apply]
    rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
  refine ⟨a, a.2, ?_⟩
  rw [root_apply ρ e i hρa]
  intro h
  have hζ1 : ζ = 1 := e.injective (h.trans (map_one e).symm)
  have hbad : orderOf ζ = 1 := hζ1 ▸ orderOf_one
  omega

omit [Finite L] in
theorem holdsOne
    (ψ : L →* adjointGroup .E6 K) (hψ : Function.Surjective ψ)
    (hρ : ∀ a l, ρ a (ψ l) = ψ (a l)) (hρi : Function.Injective ρ)
    (hφ : ∀ x, ψ (φ x) = e6Isogeny K x) (hA : A ≤ torus ρ)
    (hfix : ∀ τ ∈ torus ρ, ∀ i s, τ (φ (e6Data_valid.hm K i s)) =
      φ (e6Data_valid.hm K i s)) :
    GGTDHoldsOne (witness ρ e φ n hn) CartanMatrix.E₆ := by
  refine ⟨fun _ hτ _ hυ => torus_comm ρ hρi hτ hυ, hA,
    coroot_mem_torus ψ φ hφ ρ hρ hψ e,
    fun i _ hτ _ hυ => root_mul ρ e i hτ hυ,
    coroot_injective ψ φ hφ e, coroot_commute φ e, ?_, cartan_pairing ρ e φ ψ hψ hρ hφ⟩
  intro τ hτ i s
  exact hfix τ hτ i (e.symm s)

omit
  [Finite L] in
theorem reflection_of_coboundary {τ : MulAut L} {x h : L}
    (hfix : τ h = h) (hmove : x * (τ x)⁻¹ = h⁻¹) :
    MulAut.conj x * τ * (MulAut.conj x)⁻¹ = τ * (MulAut.conj h)⁻¹ := by
  apply MulEquiv.ext
  intro y
  change x * τ (x⁻¹ * y * x) * x⁻¹ = τ (h⁻¹ * y * h)
  simp only [map_mul, map_inv, hfix]
  calc
    x * ((τ x)⁻¹ * τ y * τ x) * x⁻¹ =
        (x * (τ x)⁻¹) * τ y * (x * (τ x)⁻¹)⁻¹ := by group
    _ = h⁻¹ * τ y * h := by rw [hmove, inv_inv]

omit
  [Finite K] [Finite L] in
theorem holdsTwo
    (hρi : Function.Injective ρ)
    (hroot : ∀ i : Fin 6, ∃ a ∈ A, root ρ e i a ≠ 1)
    (hfix : ∀ τ ∈ torus ρ, ∀ i s, τ (φ (e6Data_valid.hm K i s)) =
      φ (e6Data_valid.hm K i s))
    (hmove : ∀ τ ∈ torus ρ, ∀ i,
      n i * (τ (n i))⁻¹ = (coroot e φ i (root ρ e i τ))⁻¹) :
    GGTDHoldsTwo (witness ρ e φ n hn) := by
  refine ⟨?_, fun i τ hτ => hmove τ hτ i, fun τ hτ => root_separates ρ e hρi hτ,
    hroot⟩
  intro i τ hτ
  exact reflection_of_coboundary
    (hfix τ hτ i (e.symm (root ρ e i τ))) (hmove τ hτ i)

omit [Finite L] in
theorem holdsThree
    [CharP K 2]
    (ψ : L →* adjointGroup .E6 K) (hψ : Function.Surjective ψ)
    (_hρ : ∀ a l, ρ a (ψ l) = ψ (a l))
    (hφ : ∀ x, ψ (φ x) = e6Isogeny K x) (hφs : Function.Surjective φ)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcent : ∀ l : L, (∀ a ∈ A, MulAut.conj l * a = a * MulAut.conj l) →
      l ∈ (φ.comp (minTorus e6Data_valid K)).range)
    (hfix : ∀ τ ∈ torus ρ, ∀ i s, τ (φ (e6Data_valid.hm K i s)) =
      φ (e6Data_valid.hm K i s)) :
    GGTDHoldsThree (witness ρ e φ n hn) := by
  have hfixed : ∀ τ ∈ torus ρ, ∀ t ∈ (φ.comp (minTorus e6Data_valid K)).range, τ t = t := by
    intro τ hτ t ht
    obtain ⟨u, rfl⟩ := ht
    induction u using CFSG.LieType.Chevalley.ExceptionalCover.torusVec_induction with
    | h1 => simp
    | hmul u v hu hv =>
      simpa only [MonoidHom.comp_apply, map_mul] using
        (congrArg₂ (fun x y : L => x * y) hu hv)
    | hsingle i s =>
      simp only [MonoidHom.comp_apply, minTorus_mulSingle]
      exact hfix τ hτ i s
  refine ⟨?_, ?_, ?_, hfixed, ?_⟩
  · intro a ha hainner
    obtain ⟨l, rfl⟩ := hainner
    have hl := hcent l fun b hb => hcomm _ ha _ hb
    exact ⟨l, by
      change l ∈ ⨆ i, (coroot e φ i).range
      rw [iSup_coroot_range φ e]
      exact hl, rfl⟩
  · intro z hz _
    have hψz : ψ z = 1 := by
      have hzR : ψ z ∈ Subgroup.center (adjointGroup .E6 K) := by
        rw [Subgroup.mem_center_iff]
        intro x
        obtain ⟨l, rfl⟩ := hψ x
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
      rwa [eFrame_center, Subgroup.mem_bot] at hzR
    exact mem_coroot_torus_of_map_mem_torus ψ φ hφ hφs e
      (by rw [hψz, OneMemClass.coe_one]; exact (torusGroup .E6 K).one_mem)
  · intro l hl
    exact Subgroup.mem_sup_left (hcent l hl)
  · intro t ht _
    change t ∈ ⨆ i, (coroot e φ i).range
    rwa [iSup_coroot_range φ e]

omit
  [Finite K] in
theorem holdsFour
    {Z T : Subgroup L} {Φ : A →* Multiplicative (Fin 6 → ZMod 3)}
    (h : GGE6ThreeData Z A Φ T n) :
    GGTDHoldsFour (witness ρ e φ n hn) CoxeterMatrix.E₆ := by
  have hconj : h.conjAut = fun i => ggConjAut A (hn i) := rfl
  refine ⟨?_, ?_⟩
  · change ggAutomizer (MulAut.conj : L →* MulAut L).range A =
      Subgroup.closure (Set.range fun i => ggConjAut A (hn i))
    rw [← hconj]
    exact h.automizer_eq_reflGen
  · have hmat : CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E6) =
        CoxeterMatrix.E₆ := by
      refine coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E6) ?_
      rw [show Tag.E6.cartan = CartanMatrix.E 6 from cartanE_eq 6]
      exact ggIntCartan_E₆
    obtain ⟨ew, hew⟩ := HdRo7SU.Small.hdRo7SmAAux_groupEquiv_of_eq
      (M := (CoxeterMatrix.E₆ : CoxeterMatrix (Fin 6)))
      (M' := CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E6)) hmat.symm
    refine ⟨ew.trans h.automizerEquivWeyl, ?_⟩
    intro i
    exact (congrArg (fun w : WeylGroup .E6 =>
      (h.automizerEquivWeyl w : MulAut ↥A)) (hew i)).trans
      (h.automizerEquivWeyl_simple i)

theorem ggTDHoldsFour_of_actData {m : ℕ} {L : Type} [Group L] [Finite L]
    {A : Subgroup (MulAut L)}
    (W : GGTorusTorWit m 6 L A) {Φ : A →* Multiplicative (Fin 6 → ZMod 3)}
    (h : GGE6ThreeActData A Φ W.n)
    (hcard : Nat.card (ggAutomizer (MulAut.conj : L →* MulAut L).range A) ≤
      Nat.card (WeylGroup .E6)) :
    GGTDHoldsFour W CoxeterMatrix.E₆ := by
  have hconj : h.conjAut = fun i => ggConjAut A (W.hn i) := rfl
  refine ⟨?_, ?_⟩
  · change ggAutomizer (MulAut.conj : L →* MulAut L).range A =
      Subgroup.closure (Set.range fun i => ggConjAut A (W.hn i))
    rw [← hconj]
    exact h.automizer_eq_reflGen_of_card_le hcard
  · have hmat : CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E6) =
        CoxeterMatrix.E₆ := by
      refine coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E6) ?_
      rw [show Tag.E6.cartan = CartanMatrix.E 6 from cartanE_eq 6]
      exact ggIntCartan_E₆
    obtain ⟨ew, hew⟩ := HdRo7SU.Small.hdRo7SmAAux_groupEquiv_of_eq
      (M := (CoxeterMatrix.E₆ : CoxeterMatrix (Fin 6)))
      (M' := CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E6)) hmat.symm
    refine ⟨ew.trans (h.automizerEquivWeylOfCardLe hcard), ?_⟩
    intro i
    exact (congrArg (fun w : WeylGroup .E6 =>
      (h.automizerEquivWeylOfCardLe hcard w : MulAut ↥A)) (hew i)).trans
      (h.automizerEquivWeylOfCardLe_simple hcard i)

include hn in
theorem torData_of_aligned
    [CharP K 2]
    (ψ : L →* adjointGroup .E6 K) (hψ : Function.Surjective ψ)
    (hρ : ∀ a l, ρ a (ψ l) = ψ (a l)) (hρi : Function.Injective ρ)
    (hφ : ∀ x, ψ (φ x) = e6Isogeny K x) (hφs : Function.Surjective φ)
    (hA : IsElemAbelian 3 A)
    {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {Z T : Subgroup L} {Φ : A →* Multiplicative (Fin 6 → ZMod 3)}
    (h : GGE6ThreeData Z A Φ T n)
    (hΦ : ∀ a : A, (eFrame K ζ hζ).diag (Φ a) = ρ a)
    (hfix : ∀ τ ∈ torus ρ, ∀ i s, τ (φ (e6Data_valid.hm K i s)) =
      φ (e6Data_valid.hm K i s))
    (hmove : ∀ τ ∈ torus ρ, ∀ i,
      n i * (τ (n i))⁻¹ = (coroot e φ i (root ρ e i τ))⁻¹) :
    GGTorusTorData (Nat.card K - 1) 6 CartanMatrix.E₆ CoxeterMatrix.E₆ L A := by
  have hAT : A ≤ torus ρ := by
    intro a ha
    refine ⟨zetaVec ζ hζ (Multiplicative.toAdd (Φ ⟨a, ha⟩)), ?_⟩
    exact hΦ ⟨a, ha⟩
  have hcent : ∀ l : L,
      (∀ a ∈ A, MulAut.conj l * a = a * MulAut.conj l) →
      l ∈ (φ.comp (minTorus e6Data_valid K)).range := by
    intro l hl
    have hlR : ∀ v ∈ NoOffRest.hypE6, (eFrame K ζ hζ).ad v (ψ l) = ψ l := by
      intro v hv
      have hvR : Multiplicative.ofAdd v ∈ Φ.range := by
        rcases h.range with h | h
        · rw [h]; exact Subgroup.mem_top _
        · exact (h v).2 hv
      obtain ⟨a, ha⟩ := hvR
      have hc := congrArg ρ (hl a a.2)
      rw [map_mul, map_mul, E6ThreeModel.rho_conj hψ hρ, ← hΦ a, ha] at hc
      exact E6ThreeModel.fix_of_conj_eq (eFrame_center (K := K))
        (mul_inv_eq_iff_eq_mul.2 hc)
    have hlT : (ψ l : ModGL .E6 K) ∈ torusGroup .E6 K :=
      ((eFrame_cent hζo hζ (ψ l)).1 hlR)
    exact mem_coroot_torus_of_map_mem_torus ψ φ hφ hφs e hlT
  refine ⟨witness ρ e φ n hn, ggTDHolds_of_parts
    (holdsOne ρ e φ n hn ψ hψ hρ hρi hφ hAT hfix)
    (holdsTwo ρ e φ n hn hρi (root_nontrivial ρ e hζ hζo hΦ h.range) hfix hmove)
    (holdsThree ρ e φ n hn ψ hψ hρ hφ hφs
      (fun a ha b hb => TableB.IsElemAbelian.comm hA ha hb) hcent hfix)
    (holdsFour ρ e φ n hn h)⟩

end CFSG.StandardType.TBE6
