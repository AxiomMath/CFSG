module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL3d
import CFSG.LocalAnalysis.SteinbergBVGL3UnrestrictedOffenderModules
import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdSmall
import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL3c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.QuasithinUnique.Setup.Offender (weight commGL fixGL mem_fixGL)
open Module CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem inner_imgGL {H L X : Subgroup G} {U : Submodule (ZMod 2) V} (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H U) (hLH : L ≤ H)
    (hX : ∀ g ∈ X, ∃ l ∈ L, ∀ m ∈ L, g * m * g⁻¹ = l * m * l⁻¹) :
    ∀ t ∈ imgGL ρ H U hU X, ∃ x ∈ imgGL ρ H U hU L, ∀ y ∈ imgGL ρ H U hU L,
      t * y * t⁻¹ = x * y * x⁻¹ := by
  intro t ht
  obtain ⟨b, hbX, rfl⟩ := mem_imgGL.1 ht
  obtain ⟨l, hlL, hl⟩ := hX b hbX
  refine ⟨resGL ρ H U hU ⟨l, hLH hlL⟩, resGL_mem_imgGL hlL (hLH hlL), fun y hy => ?_⟩
  obtain ⟨m, hmL, rfl⟩ := mem_imgGL.1 hy
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (resGL ρ H U hU) (Subtype.ext (hl m hmL))

theorem exists_eV_of_transportGL {L B : Subgroup G} [IsSimpleGroup ↥L]
    {hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤)} (hT : TransportGL ρ L B hinv)
    (eL : ↥L ≃* GL (Fin 3) (ZMod 2)) :
    ∃ (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃*
        ↥(imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L))
      (κ : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥L),
      IsSimpleGroup ↥(imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L) ∧
      ∀ g (u : ↥(commOn ρ L ⊤)),
        ((((eV g : ↥(imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L)) :
          ↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤)) u : ↥(commOn ρ L ⊤)) : V) = ρ (κ g : G) u := by
  obtain ⟨e, he⟩ := hT.iso
  let rV : GL (Fin 3) (ZMod 2) ≃* ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)
  refine ⟨rV.symm.trans (eL.symm.trans e), rV.symm.trans eL.symm, e.symm.isSimpleGroup, fun g u => ?_⟩
  simp only [MulEquiv.trans_apply]
  rw [he]
  rfl

theorem imgGL_le_of_transportGL [Finite V] {L B : Subgroup G} [IsSimpleGroup ↥L]
    {hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤)} (hT : TransportGL ρ L B hinv)
    (eL : ↥L ≃* GL (Fin 3) (ZMod 2)) (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B ≤ imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L := by
  obtain ⟨eV, -, hsimp, -⟩ := exists_eV_of_transportGL hT eL
  haveI := hsimp
  haveI : FiniteDimensional (ZMod 2) ↥(commOn ρ L ⊤) := Module.Finite.of_finite
  exact le_of_offender_of_cen eV hT.center hT.commU hT.elem
    (inner_imgGL hinv le_sup_left fun g hg => exists_inner_of_mem_normalizer hT eL (hBN hg)) hT.cen hT.off

section ModuleShape

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] {𝓛 : Subgroup (E ≃ₗ[ZMod 2] E)}

@[expose] noncomputable def repGL3 (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛) :
    Representation (ZMod 2) ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) E :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (𝓛.subtype.comp eV.toMonoidHom)

theorem repGL3_apply (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛)
    (g : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (x : E) :
    repGL3 eV g x = ((eV g : ↥𝓛) : E ≃ₗ[ZMod 2] E) x :=
  rfl

theorem module_shape_GL3 [Finite E] (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛)
    (hE : commGL 𝓛 ⊤ = ⊤) {T : Subgroup (E ≃ₗ[ZMod 2] E)} (hTL : T ≤ 𝓛)
    (hTe : CFSG.IsElementaryAbelian 2 ↥T) (hT1 : T ≠ ⊥)
    (hoff : Nat.card E ≤ Nat.card ↥T * Nat.card ↥(fixGL T)) :
    finrank (ZMod 2) E ≤ 6 ∧
      ((∃ φ : E →ₗ[ZMod 2] (Fin 3 → ZMod 2),
          (∀ g x, φ (repGL3 eV g x) = natRep (Fin 3 → ZMod 2) g (φ x)) ∧ Function.Surjective φ ∧
            LinearMap.ker φ = Representation.invariants (repGL3 eV)) ∨
        Nonempty ((repGL3 eV).Equiv ((natRep (Fin 3 → ZMod 2)).prod (natRep (Fin 3 → ZMod 2)))) ∨
        (∃ φ : E →ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin 3 → ZMod 2),
          (∀ g x, φ (repGL3 eV g x) = dualRep (Fin 3 → ZMod 2) g (φ x)) ∧ Function.Surjective φ ∧
            LinearMap.ker φ = Representation.invariants (repGL3 eV)) ∨
        Nonempty ((repGL3 eV).Equiv ((dualRep (Fin 3 → ZMod 2)).prod (dualRep (Fin 3 → ZMod 2))))) ∧
      ∃ eD : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃*
          (Module.Dual (ZMod 2) (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin 3 → ZMod 2)),
        ∀ g f, eD g f = dualRep (Fin 3 → ZMod 2) g f := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  haveI : Finite ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
    Finite.of_injective (fun f : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) =>
      (f : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))) DFunLike.coe_injective
  haveI : Nontrivial E := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hT1
    rw [eq_bot_iff]
    intro t _
    rw [Subgroup.mem_bot]
    exact LinearEquiv.ext fun x => @Subsingleton.elim _ h _ _
  have hE' : Submodule.span (ZMod 2)
      {w | ∃ (s : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (v : E), w = repGL3 eV s v - v} = ⊤ := by
    refine eq_top_iff.2 (hE.symm.le.trans (Submodule.span_mono ?_))
    rintro w ⟨b, hb, u, -, rfl⟩
    refine ⟨eV.symm ⟨b, hb⟩, u, ?_⟩
    rw [repGL3_apply, MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨Tp, hTp⟩ : ∃ Tp : Subgroup ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      Tp = (T.subgroupOf 𝓛).map eV.symm.toMonoidHom := ⟨_, rfl⟩
  have hTpmem : ∀ g ∈ Tp, ((eV g : ↥𝓛) : E ≃ₗ[ZMod 2] E) ∈ T := by
    intro g hg
    rw [hTp] at hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    show ((eV (eV.symm y) : ↥𝓛) : E ≃ₗ[ZMod 2] E) ∈ T
    rw [MulEquiv.apply_symm_apply]
    exact Subgroup.mem_subgroupOf.1 hy
  have hTpcard : Nat.card ↥Tp = Nat.card ↥T := by
    rw [hTp, Subgroup.card_map_of_injective (f := eV.symm.toMonoidHom) eV.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
  haveI := hTe
  haveI : CFSG.IsElementaryAbelian 2 ↥(T.subgroupOf 𝓛) := CFSG.IsElementaryAbelian.subgroupOf hTL
  have hTpe : CFSG.IsElementaryAbelian 2 ↥Tp := by
    rw [hTp]
    exact CFSG.IsElementaryAbelian.map _
  have hTp1 : Tp ≠ ⊥ := by
    intro h
    apply hT1
    rw [← Subgroup.card_eq_one, ← hTpcard, h, Subgroup.card_bot]
  haveI := hTpe
  obtain ⟨r, hr⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 ↥Tp).exists_card_eq
  have hoff' : finrank (ZMod 2) E -
      finrank (ZMod 2) ↥(Representation.invariants ((repGL3 eV).comp Tp.subtype)) ≤ r := by
    have hfix : fixGL T ≤ Representation.invariants ((repGL3 eV).comp Tp.subtype) := by
      intro x hx
      rw [Representation.mem_invariants]
      intro g
      show repGL3 eV g x = x
      rw [repGL3_apply]
      exact (mem_fixGL.1 hx) _ (hTpmem g g.2)
    have h1 : 2 ^ finrank (ZMod 2) E ≤ 2 ^ (r + finrank (ZMod 2) ↥(fixGL T)) := by
      have h2 := hoff
      rw [← hTpcard, hr, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E),
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(fixGL T)), Nat.card_zmod] at h2
      rw [pow_add]
      exact h2
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
    have h4 := Submodule.finrank_mono hfix
    omega
  obtain ⟨hdim, hshape, -, heD⟩ :=
    CFSG.LocalAnalysis.SteinbergBV.GL3_offender_unrestricted_explicit_module_production
      (Module.finrank_fin_fun (ZMod 2)) (repGL3 eV) hE' Tp
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 Tp).1 hTpe) hTp1 r hr hoff'
  refine ⟨hdim, ?_, heD⟩
  rcases hshape with h | ⟨h, -⟩ | h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end ModuleShape

theorem module_shape_of_transportGL [Finite V] {L B : Subgroup G} [IsSimpleGroup ↥L]
    {hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤)} (hT : TransportGL ρ L B hinv)
    (eL : ↥L ≃* GL (Fin 3) (ZMod 2)) (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    finrank (ZMod 2) ↥(commOn ρ L ⊤) ≤ 6 ∧
      (NatL3 ρ L (commOn ρ L ⊤) (commOn ρ L ⊤ ⊓ fixSub ρ L) ∨
        (commOn ρ L ⊤ ⊓ fixSub ρ L = ⊥ ∧
          SecSum (fun A B => NatL3 ρ L A B) 2 (commOn ρ L ⊤) ⊥)) := by
  obtain ⟨eV, κ, -, hκ⟩ := exists_eV_of_transportGL hT eL
  obtain ⟨hdim, hshape, eD, heD⟩ :=
    module_shape_GL3 eV hT.commU (imgGL_le_of_transportGL hT eL hBN) hT.elem hT.ne_bot hT.off
  have hρ₁V : ∀ g (u : ↥(commOn ρ L ⊤)), ((repGL3 eV g u : ↥(commOn ρ L ⊤)) : V) = ρ (κ g : G) u :=
    fun g u => by rw [repGL3_apply]; exact hκ g u
  have hUL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (commOn ρ L ⊤) := isInvariant_commOn_top Subgroup.le_normalizer
  have hW3 : finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 := Module.finrank_fin_fun (ZMod 2)
  have hD3 : finrank (ZMod 2) (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) = 3 := by
    rw [Subspace.dual_finrank_eq, Module.finrank_fin_fun]
  refine ⟨hdim, ?_⟩
  rcases hshape with ⟨φ, hφ, hsurj, hker⟩ | hN | ⟨φ, hφ, hsurj, hker⟩ | hN
  · exact Or.inl (natL3_of_surjective (eW := MulEquiv.refl _) hUL hρ₁V hW3
      (fun g u => by rw [hφ]; rfl) hsurj hker)
  · obtain ⟨Φ⟩ := hN
    exact Or.inr (secSum_of_equiv (eW := MulEquiv.refl _) (σ := natRep (Fin 3 → ZMod 2)) hρ₁V hW3
      (fun _ _ => rfl) (fun _ h => eq_zero_of_forall_apply_eq h) Φ)
  · exact Or.inl (natL3_of_surjective (eW := eD) hUL hρ₁V hD3 (fun g u => by rw [hφ, heD]) hsurj hker)
  · obtain ⟨Φ⟩ := hN
    exact Or.inr (secSum_of_equiv (eW := eD) (σ := dualRep (Fin 3 → ZMod 2)) hρ₁V hD3
      (fun g f => (heD g f).symm) (fun f h => eq_zero_of_forall_dualRep_eq fun g => by rw [← heD]; exact h g)
      Φ)

theorem exists_eq_apply_of_transportGL [Finite G] [Finite V] {L B : Subgroup G} [IsSimpleGroup ↥L]
    {hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤)} (hT : TransportGL ρ L B hinv)
    (eL : ↥L ≃* GL (Fin 3) (ZMod 2)) (hdim : finrank (ZMod 2) ↥(commOn ρ L ⊤) ≤ 6)
    {S : Subgroup G} (hSe : CFSG.IsElementaryAbelian 2 ↥S) (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hoff : Nat.card ↥(commOn ρ L ⊤) * Nat.card ↥(cenOn ρ S (commOn ρ L ⊤)) ≤
      Nat.card ↥S * Nat.card ↥(fixOn ρ S (commOn ρ L ⊤))) :
    ∀ s ∈ S, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ s u = ρ l u := by
  classical
  obtain ⟨eV, -, hsimp, -⟩ := exists_eV_of_transportGL hT eL
  haveI := hsimp
  haveI : FiniteDimensional (ZMod 2) ↥(commOn ρ L ⊤) := Module.Finite.of_finite
  have hUN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (Subgroup.normalizer (L : Set G)) (commOn ρ L ⊤) := isInvariant_commOn_top le_rfl
  have hcongr : imgGL ρ (Subgroup.normalizer (L : Set G)) (commOn ρ L ⊤) hUN L =
      imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L :=
    imgGL_congr hUN hinv Subgroup.le_normalizer le_sup_left
  have hT' : ∀ t ∈ imgGL ρ (Subgroup.normalizer (L : Set G)) (commOn ρ L ⊤) hUN S,
      ∃ x ∈ imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L, ∀ y ∈ imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L,
        t * y * t⁻¹ = x * y * x⁻¹ := by
    rw [← hcongr]
    exact inner_imgGL hUN Subgroup.le_normalizer fun g hg => exists_inner_of_mem_normalizer hT eL (hSN hg)
  have hoff' : Nat.card ↥(commOn ρ L ⊤) ≤
      Nat.card ↥(imgGL ρ (Subgroup.normalizer (L : Set G)) (commOn ρ L ⊤) hUN S) *
        Nat.card ↥(fixGL (imgGL ρ (Subgroup.normalizer (L : Set G)) (commOn ρ L ⊤) hUN S)) := by
    have h1 := card_imgGL_mul_card_cenOn (hU := hUN) hSN
    have h2 : Nat.card ↥(fixGL (imgGL ρ (Subgroup.normalizer (L : Set G)) (commOn ρ L ⊤) hUN S)) =
        Nat.card ↥(fixOn ρ S (commOn ρ L ⊤)) := card_fixSub_imgGL hSN
    rw [h2]
    rw [← h1] at hoff
    have hcpos : 0 < Nat.card ↥(cenOn ρ S (commOn ρ L ⊤)) := Nat.card_pos
    exact Nat.le_of_mul_le_mul_right (hoff.trans_eq (mul_right_comm _ _ _)) hcpos
  have hle := le_of_offender_of_finrank_le_six eV hT.center hT.commU hdim
    (isElementaryAbelian_imgGL (hU := hUN) hSN hSe le_rfl) hT' hoff'
  intro s hs
  obtain ⟨⟨l, hlH⟩, hlL, hl⟩ := mem_imgGL.1 (hle (resGL_mem_imgGL (hU := hUN) hs (hSN hs)))
  refine ⟨l, hlL, fun u hu => ?_⟩
  have h1 := congrArg (fun f : ↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤) =>
    ((f ⟨u, hu⟩ : ↥(commOn ρ L ⊤)) : V)) hl
  exact h1.symm

theorem exists_eq_apply_of_mem_hP_of_transportGL [Finite G] [Finite V] (hρ : Function.Injective ρ)
    {L B : Subgroup G} (hL : IsComponentOf L ⊤) [IsSimpleGroup ↥L]
    {hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤)} (hT : TransportGL ρ L B hinv)
    (eL : ↥L ≃* GL (Fin 3) (ZMod 2)) (hdim : finrank (ZMod 2) ↥(commOn ρ L ⊤) ≤ 6) :
    ∀ g ∈ hP ρ, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u := by
  let T : Subgroup G :=
    { carrier := {g | ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u}
      mul_mem' := by
        rintro a b ⟨l, hl, ha⟩ ⟨m, hm, hb⟩
        refine ⟨l * m, mul_mem hl hm, fun u hu => ?_⟩
        rw [glRep_mul_apply, glRep_mul_apply, hb u hu,
          ha _ (commOn_top_mapsTo (Subgroup.le_normalizer hm) hu)]
      one_mem' := ⟨1, one_mem _, fun u _ => rfl⟩
      inv_mem' := by
        rintro a ⟨l, hl, ha⟩
        refine ⟨l⁻¹, inv_mem hl, fun u hu => ?_⟩
        have hu' := commOn_top_mapsTo (Subgroup.le_normalizer (inv_mem hl)) hu
        calc ρ a⁻¹ u = ρ a⁻¹ (ρ a (ρ l⁻¹ u)) := by rw [ha _ hu', glRep_apply_inv]
          _ = ρ l⁻¹ u := glRep_inv_apply ρ _ _ }
  have hle : hP ρ ≤ T := iSup₂_le fun A hA s hs =>
    exists_eq_apply_of_transportGL hT eL hdim (isElementaryAbelian_of_mem_calP hA)
      (le_normalizer_of_mem_calP hρ hL hA) ((isBestOffenderOn_of_mem_calP hρ hA).isOffenderOn_of_le _).2 s hs
  exact fun g hg => hle hg

theorem l3_component_identification [Finite G] [Finite V] (hρ : Function.Injective ρ) {L : Subgroup G}
    (hL : IsComponentOf L ⊤) (hX : IsL2Odd ↥L 7) {A : Subgroup G} (hA : A ∈ calP ρ) (hLA : ⁅L, A⁆ ≠ ⊥) :
    (∀ g ∈ Subgroup.normalizer (L : Set G), ∃ l ∈ L, ∀ m ∈ L, g * m * g⁻¹ = l * m * l⁻¹) ∧
      finrank (ZMod 2) ↥(commOn ρ L ⊤) ≤ 6 ∧
      (NatL3 ρ L (commOn ρ L ⊤) (commOn ρ L ⊤ ⊓ fixSub ρ L) ∨
        (commOn ρ L ⊤ ⊓ fixSub ρ L = ⊥ ∧
          SecSum (fun A B => NatL3 ρ L A B) 2 (commOn ρ L ⊤) ⊥)) ∧
      ∀ g ∈ hP ρ, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u := by
  haveI : IsSimpleGroup ↥L := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hX
  obtain ⟨eL⟩ := nonempty_equiv_GL32_of_isL2Odd_seven hX
  obtain ⟨B, hinv, hBA, -, -, -, -, hT⟩ := exists_transportGL hρ hL inferInstance hA hLA
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBA.trans (le_normalizer_of_mem_calP hρ hL hA)
  obtain ⟨hdim, hshape⟩ := module_shape_of_transportGL hT eL hBN
  exact ⟨fun g hg => exists_inner_of_mem_normalizer hT eL hg, hdim, hshape,
    exists_eq_apply_of_mem_hP_of_transportGL hρ hL hT eL hdim⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
