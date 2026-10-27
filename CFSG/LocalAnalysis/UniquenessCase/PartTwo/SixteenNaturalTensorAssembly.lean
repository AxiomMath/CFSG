module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalMultiplicity
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalFourCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalFourCocycle
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalTensorCover
public import CFSG.RepresentationTheory.BinaryTensorMovement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped TensorProduct

variable {G : Type} [Group G] [Finite G]

theorem s168e3_threeNatSeven_l3_mBarGT_three_of_fixV_ne_bot
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL3 : IsL3 ↥(lBar V₀ V hV L) 1)
    (hZ : fixV (lBar V₀ V hV L) ≠ ⊥) :
    MBarGT D.M V₀ V 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T) :=
    s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs
  letI : Module (ZMod 2) (Additive (Vtil V₀ V hV)) := MulAutTwo.zmod2Module h.elem
  obtain ⟨m⟩ := h.exists_naturalThreeMultiplicityData h7 hL3
  letI : AddCommGroup m.Q := m.qAdd
  letI : Module (ZMod 2) m.Q := m.qModule
  letI : Finite m.Q := m.qFinite
  letI : AddCommGroup m.X := m.xAdd
  letI : Module (ZMod 2) m.X := m.xModule
  letI : Finite m.X := m.xFinite
  let Vg := Vtil V₀ V hV
  let A := Mbar D.M V₀ V hV
  let B := lBar V₀ V hV L
  let K₀ := s1t3KBar A B
  let W := Additive Vg
  let Z₀ := s16smSubmod (fixV B)
  let ρW : Representation (ZMod 2) ↥B W := s16smRepW (MonoidHom.id ↥B)
  let κW : Representation (ZMod 2) ↥K₀ W := s16smRepW (MonoidHom.id ↥K₀)
  let α : Representation (ZMod 2) ↥A W := s16smRepW (MonoidHom.id ↥A)
  let i : Z₀ →ₗ[ZMod 2] W := Z₀.subtype
  haveI : Finite Vg := inferInstance
  haveI : Finite W := inferInstance
  haveI : Finite (MulAut Vg) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := MulAut Vg))
  haveI : Finite ↥B := inferInstance
  haveI : Finite ↥A := inferInstance
  haveI : Finite ↥K₀ := inferInstance
  haveI : Finite Z₀ := inferInstance
  have hZne : Z₀ ≠ ⊥ := by
    intro hbot
    apply hZ
    rw [eq_bot_iff]
    intro z hz
    have hmem : Additive.ofMul z ∈ Z₀ := hz
    rw [hbot] at hmem
    have hz1 : Additive.ofMul z = (0 : W) := by simpa using hmem
    have : z = 1 := Additive.ofMul.injective (by simpa using hz1)
    exact Subgroup.mem_bot.mpr this
  haveI : Nontrivial Z₀ := (Submodule.nontrivial_iff_ne_bot (p := Z₀)).mpr hZne
  have hnat : Explicit.BinaryNaturalSL m.rhoQ 3 (ZMod 2) .natural := by
    show (FFModel.nat (StatedSL 3 (ZMod 2))).IsModel m.rhoQ
    let e := JonesParshall.secEquivAmb (FFModel.nat (StatedSL 3 (ZMod 2))) rfl rfl
    let βa : m.Q ≃+ Additive (FFModel.nat (StatedSL 3 (ZMod 2))).Amb :=
      m.coordQ.toAddEquiv.trans (JonesParshall.additiveVec 3 (ZMod 2)).symm
    have hamb : ∀ (l : ↥B) (q : m.Q),
        βa (m.rhoQ l q) =
          Additive.ofMul ((FFModel.nat (StatedSL 3 (ZMod 2))).act (m.theta l)
            (Additive.toMul (βa q))) := by
      intro l q
      change Additive.ofMul (Multiplicative.ofAdd (m.coordQ (m.rhoQ l q))) =
        Additive.ofMul ((FFModel.nat (StatedSL 3 (ZMod 2))).act (m.theta l)
          (Multiplicative.ofAdd (m.coordQ q)))
      rw [m.coordQ_apply]
      rfl
    refine ⟨m.theta, βa.trans e.symm.toAdditive, ?_, ?_, ?_, ?_⟩
    · exact bot_le
    · intro g mm _
      exact Subgroup.mem_top _
    · intro g mm hm
      have hm1 : mm = 1 := Subgroup.mem_bot.mp hm
      subst hm1
      refine Subgroup.mem_bot.mpr ?_
      change natAct (StatedSL 3 (ZMod 2)) g (1 : Multiplicative (Fin 3 → ZMod 2)) = 1
      simp [natAct]
    · intro l q mm hm hw
      have key : ∀ y : Additive (FFModel.nat (StatedSL 3 (ZMod 2))).Amb,
          e.toAdditive (e.symm.toAdditive y) = y := by
        intro y
        show Additive.ofMul (e (e.symm (Additive.toMul y))) = y
        rw [e.apply_symm_apply]
        rfl
      have h1 : βa q = Additive.ofMul (mm : (FFModel.nat (StatedSL 3 (ZMod 2))).Amb) := by
        have hh := congrArg e.toAdditive hw
        rw [show (βa.trans e.symm.toAdditive) q = e.symm.toAdditive (βa q) from rfl,
          key] at hh
        exact hh
      have h2 : βa (m.rhoQ l q) =
          Additive.ofMul ((FFModel.nat (StatedSL 3 (ZMod 2))).act (m.theta l)
            (mm : (FFModel.nat (StatedSL 3 (ZMod 2))).Amb)) := by
        rw [hamb, h1]
        rfl
      apply e.toAdditive.injective
      rw [show (βa.trans e.symm.toAdditive) (m.rhoQ l q) =
        e.symm.toAdditive (βa (m.rhoQ l q)) from rfl, key, h2]
      rfl
  have hH1eq : Module.finrank (ZMod 2) (JonesParshall.H1 (Representation.dual m.rhoQ)) = 1 := by
    have hh := JonesParshall.finrank_H1_SL3 (ρ := Representation.dual m.rhoQ) (a := 1)
      (by simp [ZMod.card]) (by norm_num) m.dual_model
    simpa using hh
  have hH1 : Module.finrank (ZMod 2) (JonesParshall.H1 (Representation.dual m.rhoQ)) ≤ 1 := hH1eq.le
  obtain ⟨d, hd, hdn⟩ := naturalThree_exists_dual_cocycle_not_coboundary m.rhoQ hnat
  let E := ZMod 2 × m.Q
  let ρE : Representation (ZMod 2) ↥B E :=
    JonesParshall.trivialLineExtension m.rhoQ d hd
  let eE : E ≃ₗ[ZMod 2] (ZMod 2 × m.Q) := LinearEquiv.refl (ZMod 2) E
  have hE : ∀ (g : ↥B) (e : E),
      eE (ρE g e) =
        ((eE e).1 + d g (m.rhoQ g (eE e).2), m.rhoQ g (eE e).2) := by
    intro g e
    exact JonesParshall.trivialLineExtension_apply m.rhoQ d hd g e.1 e.2
  have hi : Function.Injective i := fun x y h => Subtype.ext h
  have hqW : Function.Surjective m.qW := m.qW_surjective
  have hker : LinearMap.range i = LinearMap.ker m.qW := by
    rw [Submodule.range_subtype]
    exact m.ker_qW.symm
  have hfix : ∀ (g : ↥B) (z : Z₀), ρW g (i z) = i z := by
    intro g z
    show s16smRepW (MonoidHom.id ↥B) g (z : W) = (z : W)
    rw [← ofMul_toMul (z : W)]
    rw [s16smRepW_apply, MonoidHom.id_apply]
    have hz : Additive.toMul (z : W) ∈ fixV B := z.2
    rw [mem_fixV] at hz
    rw [hz (g : MulAut Vg) g.2]
  have hqρ : ∀ (g : ↥B) (w : W),
      m.qW (ρW g w) = TensorProduct.map (m.rhoQ g) LinearMap.id (m.qW w) := by
    intro g w
    exact m.qW_L g w
  have hW : ∀ ψ : W →ₗ[ZMod 2] ZMod 2,
      (∀ (g : ↥B) (w : W), ψ (ρW g w) = ψ w) → ψ = 0 := by
    intro ψ hψ
    exact m.no_invariant_W ψ hψ
  have hcomm : ∀ (k : ↥K₀) (g : ↥B) (w : W),
      κW k (ρW g w) = ρW g (κW k w) := by
    intro k g w
    have hkg : (k : MulAut Vg) * (g : MulAut Vg) = (g : MulAut Vg) * (k : MulAut Vg) := by
      have hk : (k : MulAut Vg) ∈ Subgroup.centralizer (B : Set (MulAut Vg)) :=
        (Subgroup.mem_inf.mp k.2).2
      exact (Subgroup.mem_centralizer_iff.mp hk (g : MulAut Vg) g.2).symm
    rw [← ofMul_toMul w]
    change s16smRepW (MonoidHom.id ↥K₀) k
        (s16smRepW (MonoidHom.id ↥B) g (Additive.ofMul (Additive.toMul w))) =
      s16smRepW (MonoidHom.id ↥B) g
        (s16smRepW (MonoidHom.id ↥K₀) k (Additive.ofMul (Additive.toMul w)))
    rw [s16smRepW_apply, s16smRepW_apply, s16smRepW_apply, s16smRepW_apply,
      MonoidHom.id_apply, MonoidHom.id_apply]
    rw [show (k : MulAut Vg) ((g : MulAut Vg) (Additive.toMul w)) =
      (g : MulAut Vg) ((k : MulAut Vg) (Additive.toMul w)) from by
        have := congrArg (fun f : MulAut Vg => f (Additive.toMul w)) hkg
        simpa [MulAut.mul_apply] using this]
  have hiκ : ∀ (k : ↥K₀) (z : Z₀), κW k (i z) = i (m.kappaZ k z) := by
    intro k z
    show s16smRepW (MonoidHom.id ↥K₀) k (z : W) = ((m.kappaZ k z : Z₀) : W)
    exact (m.kappaZ_apply k z).symm
  have hqκ : ∀ (k : ↥K₀) (w : W),
      m.qW (κW k w) = TensorProduct.map LinearMap.id (m.kappaX k) (m.qW w) := by
    intro k w
    exact m.qW_K k w
  obtain ⟨eC, heB, heK, heq⟩ :=
    exists_tensor_equiv_of_irreducible_multiplicity
      (B := ↥B) (K := ↥K₀) (Q := m.Q) (X := m.X) (Z := Z₀) (E := E) (W := W)
      m.rhoQ ρE ρW d hd hdn hH1 m.no_invariant_Q eE hE i m.qW hi hqW hker hfix hqρ hW
      κW m.kappaX m.kappaZ hcomm hiκ hqκ m.irreducible_X
  have hBK : B ⊓ K₀ = ⊥ := by
    obtain ⟨N, _, hBN, _, _, hNK, _⟩ := h.structure_of_seven h7
    exact le_antisymm ((inf_le_inf_right K₀ hBN).trans hNK.le) bot_le
  have hc : Nat.card ↥B = 168 := CFSG.LocalAnalysis.WeakClosure81.card_eq_of_isL3 hL3
  have hbound : ∀ τ ∈ A, τ ^ 2 = 1 → τ ≠ 1 →
      2 ^ (3 + 1) ≤ Nat.card ↥(commSub (⊤ : Subgroup Vg) (Subgroup.zpowers τ)) := by
    intro τ hτA hτ2 hτne
    obtain ⟨l, hlB, k, hkK, hlk⟩ :=
      h.exists_mul_kBar_of_card_eq_168 h7 hc hτA
    have hkl : (k : MulAut Vg) * (l : MulAut Vg) = (l : MulAut Vg) * (k : MulAut Vg) := by
      have hk : (k : MulAut Vg) ∈ Subgroup.centralizer (B : Set (MulAut Vg)) :=
        (Subgroup.mem_inf.mp hkK).2
      exact (Subgroup.mem_centralizer_iff.mp hk (l : MulAut Vg) hlB).symm
    have hsq : l * l * (k * k) = 1 := by
      have hτ2v : τ ^ 2 = 1 := hτ2
      calc l * l * (k * k) = (l * k) * (l * k) := by
            symm
            calc (l * k) * (l * k) = l * (k * l) * k := by group
              _ = l * (l * k) * k := by rw [hkl]
              _ = l * l * (k * k) := by group
        _ = τ ^ 2 := by rw [← hlk, pow_two]
        _ = 1 := hτ2v
    have hl2K : (l : MulAut Vg) ^ 2 ∈ K₀ := by
      have hk2 : (k : MulAut Vg) ^ 2 ∈ K₀ := K₀.pow_mem hkK 2
      have heq : l ^ 2 = (k ^ 2)⁻¹ := by
        exact mul_eq_one_iff_eq_inv.mp (by simpa [pow_two] using hsq)
      rw [heq]
      exact K₀.inv_mem hk2
    have hl2 : (l : MulAut Vg) ^ 2 ∈ B := B.pow_mem hlB 2
    have hl2one : (l : MulAut Vg) ^ 2 = 1 := by
      have hmem : (l : MulAut Vg) ^ 2 ∈ B ⊓ K₀ := Subgroup.mem_inf.mpr ⟨hl2, hl2K⟩
      rw [hBK] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hk2one : k ^ 2 = 1 := by
      have hh : l ^ 2 * k ^ 2 = 1 := by simpa [pow_two] using hsq
      rw [hl2one, one_mul] at hh
      exact hh
    let lb : ↥B := ⟨l, hlB⟩
    let kb : ↥K₀ := ⟨k, hkK⟩
    have hlb2 : lb ^ 2 = 1 := Subtype.ext (by simpa [lb, pow_two] using hl2one)
    have hkb2 : kb ^ 2 = 1 := Subtype.ext (by simpa [kb, pow_two] using hk2one)
    let T : E →ₗ[ZMod 2] E := ρE lb
    let S : m.X →ₗ[ZMod 2] m.X := m.kappaX kb
    have hT : T.comp T = 1 := by
      change (ρE lb).comp (ρE lb) = 1
      rw [← Module.End.mul_eq_comp, ← map_mul,
        show lb * lb = 1 from by rw [← pow_two]; exact hlb2, map_one]
    have hS : S.comp S = 1 := by
      change (m.kappaX kb).comp (m.kappaX kb) = 1
      rw [← Module.End.mul_eq_comp, ← map_mul,
        show kb * kb = 1 from by rw [← pow_two]; exact hkb2, map_one]
    have hcomp_eq : ∀ u : E ⊗[ZMod 2] m.X,
        eC (TensorProduct.map T S u) = α ⟨τ, hτA⟩ (eC u) := by
      intro u
      have hmap : TensorProduct.map T S u =
          TensorProduct.map T LinearMap.id
            (TensorProduct.map LinearMap.id S u) := by
        rw [TensorProduct.map_map]
        simp
      rw [hmap, heB lb, heK kb]
      have hρκα : ρW lb (κW kb (eC u)) = α ⟨τ, hτA⟩ (eC u) := by
        rw [← ofMul_toMul (eC u)]
        change s16smRepW (MonoidHom.id ↥B) lb
            (s16smRepW (MonoidHom.id ↥K₀) kb
              (Additive.ofMul (Additive.toMul (eC u)))) =
          s16smRepW (MonoidHom.id ↥A) ⟨τ, hτA⟩
            (Additive.ofMul (Additive.toMul (eC u)))
        rw [s16smRepW_apply, s16smRepW_apply, s16smRepW_apply,
          MonoidHom.id_apply, MonoidHom.id_apply]
        rw [← MulAut.mul_apply, ← hlk]
        rfl
      exact hρκα
    have hne_tensor : TensorProduct.map T S ≠ 1 := by
      intro h1
      apply hτne
      have hfixW : ∀ w : W, α ⟨τ, hτA⟩ w = w := by
        intro w
        obtain ⟨u, rfl⟩ := eC.surjective w
        rw [← hcomp_eq u, h1]
        simp
      ext v
      have hv := hfixW (Additive.ofMul v)
      have hvα : α ⟨τ, hτA⟩ (Additive.ofMul v) =
          Additive.ofMul ((τ : MulAut Vg) v) := by
        simpa [α] using s16smRepW_apply (MonoidHom.id ↥A) ⟨τ, hτA⟩ v
      rw [hvα] at hv
      simpa using Additive.ofMul.injective hv
    have hE4 : Module.finrank (ZMod 2) E = 4 :=
      naturalThree_finrank_trivialLineExtension m.rhoQ hnat
    have hX3 : Module.finrank (ZMod 2) m.X = 3 := m.finrank_X
    have hTmove : T ≠ 1 → Module.finrank (ZMod 2) (LinearMap.range (T - 1)) = 2 := by
      intro hTne
      exact naturalThree_trivialLineExtension_involution_finrank m.rhoQ hnat d hd hdn
        lb hlb2 hTne
    have hTrank := CFSG.RepresentationTheory.four_le_finrank_range_tensor_sub_one
      (K := ZMod 2) (E := E) (X := m.X) hE4 hX3 T hT S hS hTmove hne_tensor
    have hrank_eq :=
      CFSG.HardMathSupport.GuralnickMalle.finrank_range_sub_one_eq_of_intertwines
        eC (TensorProduct.map T S) (α ⟨τ, hτA⟩) hcomp_eq
    have hrankW : 4 ≤ Module.finrank (ZMod 2)
        (LinearMap.range (α ⟨τ, hτA⟩ - 1)) := by
      rw [hrank_eq]
      exact hTrank
    let Vt := Multiplicative (Additive Vg)
    let τ' : MulAut Vt := FFModel.repMulAut α ⟨τ, hτA⟩
    have hη : ∀ x : Vt, (MulEquiv.multiplicativeAdditive Vg) (τ' x) =
        (τ : MulAut Vg) ((MulEquiv.multiplicativeAdditive Vg) x) := by
      intro x
      have hx : x = Multiplicative.ofAdd (Multiplicative.toAdd x) :=
        (ofAdd_toAdd x).symm
      rw [hx, show τ' (Multiplicative.ofAdd (Multiplicative.toAdd x)) =
        Multiplicative.ofAdd (α ⟨τ, hτA⟩ (Multiplicative.toAdd x)) from
          FFModel.repMulAut_apply α ⟨τ, hτA⟩ (Multiplicative.toAdd x)]
      show Additive.toMul (α ⟨τ, hτA⟩ (Multiplicative.toAdd x)) =
        (τ : MulAut Vg) (Additive.toMul (Multiplicative.toAdd x))
      rw [show α ⟨τ, hτA⟩ (Multiplicative.toAdd x) =
        Additive.ofMul ((τ : MulAut Vg) (Additive.toMul (Multiplicative.toAdd x))) from by
          simpa [α] using s16smRepW_apply (MonoidHom.id ↥A) ⟨τ, hτA⟩
            (Additive.toMul (Multiplicative.toAdd x))]
      rfl
    have hT' : ∀ x : Additive Vg,
        Multiplicative.toAdd (τ' (Multiplicative.ofAdd x)) = α ⟨τ, hτA⟩ x := by
      intro x
      rw [show τ' (Multiplicative.ofAdd x) =
        Multiplicative.ofAdd (α ⟨τ, hτA⟩ x) from
          FFModel.repMulAut_apply α ⟨τ, hτA⟩ x]
      rfl
    have hbridge := card_commSub_eq_two_pow_finrank_range_sub_one τ' (α ⟨τ, hτA⟩) hT'
    have hcard4 : 2 ^ 4 ≤ Nat.card ↥(commSub (⊤ : Subgroup Vt)
        (Subgroup.zpowers τ')) := by
      rw [hbridge]
      exact Nat.pow_le_pow_right (by norm_num) hrankW
    have hcard_eq : Nat.card ↥(commSub (⊤ : Subgroup Vt) (Subgroup.zpowers τ')) =
        Nat.card ↥(commSub (⊤ : Subgroup Vg) (Subgroup.zpowers τ)) := by
      let η := MulEquiv.multiplicativeAdditive Vg
      have hmap : (commSub (⊤ : Subgroup Vt) (Subgroup.zpowers τ')).map η.toMonoidHom =
          commSub (⊤ : Subgroup Vg) (Subgroup.zpowers τ) := by
        rw [commSub_zpowers_eq_map (fun x _ w _ => Subgroup.mem_top _),
          commSub_zpowers_eq_map (fun x _ w _ => Subgroup.mem_top _)]
        rw [Subgroup.map_map]
        have hηcomp : η.toMonoidHom.comp (CFSG.Quasithin.commHom τ') =
            (CFSG.Quasithin.commHom τ).comp η.toMonoidHom := by
          refine MonoidHom.ext fun x => ?_
          show (MulEquiv.multiplicativeAdditive Vg) (CFSG.Quasithin.commHom τ' x) =
            CFSG.Quasithin.commHom τ ((MulEquiv.multiplicativeAdditive Vg) x)
          rw [CFSG.Quasithin.commHom_apply, CFSG.Quasithin.commHom_apply,
            map_mul, map_inv, hη]
        rw [hηcomp, ← Subgroup.map_map,
          Subgroup.map_top_of_surjective η.toMonoidHom η.surjective]
      rw [← hmap, Subgroup.card_map_of_injective η.injective]
    rw [← hcard_eq]
    simpa using hcard4
  have hex : ∃ τ ∈ A, τ ^ 2 = 1 ∧ τ ≠ 1 := by
    have hdvdB : 2 ∣ Nat.card ↥B := by rw [hc]; norm_num
    have hdvd : 2 ∣ Nat.card ↥A := hdvdB.trans (Subgroup.card_dvd_of_le h.le)
    obtain ⟨τ, hτo⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have h2 := orderOf_eq_prime_iff.mp hτo
    refine ⟨(τ : MulAut Vg), τ.2, ?_, ?_⟩
    · simpa using congrArg Subtype.val h2.1
    · intro h1
      exact h2.2 (Subtype.ext h1)
  exact s16h_e3_mBarGT_of_rank D c.setting.hyp16.hyp125 hbound hex

theorem s168e3_threeNatSeven_l3_fixV_eq_bot
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL3 : IsL3 ↥(lBar V₀ V hV L) 1) :
    wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) = ⊥ := by
  have hfix : fixV (lBar V₀ V hV L) = ⊥ := by
    by_contra hZ
    exact c.setting.hyp16.not_gt
      (s168e3_threeNatSeven_l3_mBarGT_three_of_fixV_ne_bot
        c hcomp hsum htrans hs h7 hL3 hZ)
  rw [hfix, inf_bot_eq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
