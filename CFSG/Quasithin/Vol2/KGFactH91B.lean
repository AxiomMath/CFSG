module

public import CFSG.Quasithin.Vol2.KGFactSLnTwoHom
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch12Sec1Stmts

public section

namespace CFSG.Quasithin.H13.KGH91

open Matrix CFSG.Quasithin.SLnTwo CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBGraphForm
open scoped IsMulCommutative

variable {G : Type} [Group G] {n : ℕ}

structure NatCoord (L W : Subgroup G) (n : ℕ) where
  E : G → Fin n → ZMod 2
  ρ : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2)
  le : L ≤ Subgroup.normalizer (W : Set G)
  map_mul : ∀ a ∈ W, ∀ b ∈ W, E (a * b) = E a + E b
  inj : ∀ a ∈ W, ∀ b ∈ W, E a = E b → a = b
  surj : ∀ x, ∃ a ∈ W, E a = x
  conj : ∀ (l : ↥L), ∀ a ∈ W,
    E ((l : G) * a * (l : G)⁻¹) = (ρ l : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ E a
  ρ_surj : Function.Surjective ρ

namespace NatCoord

variable {L W : Subgroup G} (C : NatCoord L W n)

include C in
theorem conj_mem (l : ↥L) {a : G} (ha : a ∈ W) : (l : G) * a * (l : G)⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.1 (C.le l.2) a).1 ha

theorem E_one : C.E 1 = 0 := by
  have h := C.map_mul 1 W.one_mem 1 W.one_mem
  rw [mul_one] at h
  have h2 : C.E 1 + C.E 1 = C.E 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem eq_one_of_E {a : G} (ha : a ∈ W) (h : C.E a = 0) : a = 1 :=
  C.inj a ha 1 W.one_mem (by rw [h, C.E_one])

noncomputable def inv (x : Fin n → ZMod 2) : G := (C.surj x).choose

theorem inv_mem (x : Fin n → ZMod 2) : C.inv x ∈ W := (C.surj x).choose_spec.1

theorem E_inv (x : Fin n → ZMod 2) : C.E (C.inv x) = x := (C.surj x).choose_spec.2

theorem inv_E {a : G} (ha : a ∈ W) : C.inv (C.E a) = a :=
  C.inj _ (C.inv_mem _) a ha (C.E_inv _)

theorem inv_add (x y : Fin n → ZMod 2) : C.inv (x + y) = C.inv x * C.inv y :=
  C.inj _ (C.inv_mem _) _ (W.mul_mem (C.inv_mem x) (C.inv_mem y)) (by
    rw [C.E_inv, C.map_mul _ (C.inv_mem x) _ (C.inv_mem y), C.E_inv, C.E_inv])

theorem inv_mulVec (l : ↥L) (x : Fin n → ZMod 2) :
    C.inv ((C.ρ l : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = (l : G) * C.inv x * (l : G)⁻¹ :=
  C.inj _ (C.inv_mem _) _ (C.conj_mem l (C.inv_mem x)) (by
    rw [C.E_inv, C.conj l _ (C.inv_mem x), C.E_inv])

noncomputable def conjBy (A : GL (Fin n) (ZMod 2)) : NatCoord L W n where
  E g := ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ C.E g
  ρ := (slConjugation n (ZMod 2) A⁻¹).toMonoidHom.comp C.ρ
  le := C.le
  map_mul a ha b hb := by
    rw [C.map_mul a ha b hb, Matrix.mulVec_add]
  inj a ha b hb h := C.inj a ha b hb (by
    have := congrArg (fun x => (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) h
    simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] using this)
  surj x := by
    obtain ⟨a, ha, hax⟩ := C.surj ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x)
    exact ⟨a, ha, by rw [hax, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]⟩
  conj l a ha := by
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [C.conj l a ha, coe_slConjugation, inv_inv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc _ (A : Matrix (Fin n) (Fin n) (ZMod 2)), Units.mul_inv, Matrix.mul_one]
  ρ_surj := (slConjugation n (ZMod 2) A⁻¹).surjective.comp C.ρ_surj

theorem eq_bot_of_normal_isPGroup (hn : 3 ≤ n)
    {N : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} [N.Normal] (hN : IsPGroup 2 N) :
    N = ⊥ := by
  have hs : IsSimpleGroup (SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) hn
  rcases hs.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hN' : IsPGroup 2 ↥(⊤ : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) := h ▸ hN
    have h2 : IsPGroup 2 (SpecialLinearGroup (Fin n) (ZMod 2)) := hN'.of_equiv Subgroup.topEquiv
    have hc := h2.center_nontrivial
    rw [center_eq_bot] at hc
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hc rfl

theorem ker_eq [Finite G] (hn : 3 ≤ n)
    (ι : ↥L ⧸ CFSG.pCore 2 ↥L ≃* SpecialLinearGroup (Fin n) (ZMod 2)) :
    C.ρ.ker = CFSG.pCore 2 ↥L := by
  have hle : CFSG.pCore 2 ↥L ≤ C.ρ.ker := by
    have : ((CFSG.pCore 2 ↥L).map C.ρ).Normal :=
      Subgroup.Normal.map CFSG.pCore_normal C.ρ C.ρ_surj
    have h := eq_bot_of_normal_isPGroup hn (CFSG.pCore_isPGroup.map C.ρ)
    rwa [Subgroup.map_eq_bot_iff] at h
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 : Nat.card (↥L ⧸ C.ρ.ker) = Nat.card (SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective C.ρ C.ρ_surj).toEquiv
  have h2 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Nat.card_congr ι.toEquiv
  have hk := Subgroup.card_mul_index C.ρ.ker
  have hp := Subgroup.card_mul_index (CFSG.pCore 2 ↥L)
  rw [Subgroup.index_eq_card, h1] at hk
  rw [Subgroup.index_eq_card, h2] at hp
  have hpos : 0 < Nat.card (SpecialLinearGroup (Fin n) (ZMod 2)) := Nat.card_pos
  have := Nat.eq_of_mul_eq_mul_right hpos (hk.trans hp.symm)
  omega

theorem exists_adapted [Finite G] (hn : 3 ≤ n)
    (ι : ↥L ⧸ CFSG.pCore 2 ↥L ≃* SpecialLinearGroup (Fin n) (ZMod 2)) {W' : Subgroup G}
    (C' : NatCoord L W' n) :
    ∃ C'' : NatCoord L W' n, (∀ l, C''.ρ l = C.ρ l) ∨
      ∀ l, C''.ρ l = slGraphAut n (ZMod 2) (C.ρ l) := by
  have hk : C.ρ.ker = C'.ρ.ker := (C.ker_eq hn ι).trans (C'.ker_eq hn ι).symm
  let α : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) :=
    (QuotientGroup.quotientKerEquivOfSurjective C.ρ C.ρ_surj).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective C'.ρ C'.ρ_surj))
  have hα : ∀ l, α (C.ρ l) = C'.ρ l := by
    intro l
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective C.ρ C.ρ_surj).symm (C.ρ l) =
        (l : ↥L ⧸ C.ρ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [α, MulEquiv.trans_apply, h1]
    rfl
  obtain ⟨A, ε, hε, hσ⟩ := SLnTwo.exists_conj_graph hn α
  have hcancel : ∀ g, slConjugation n (ZMod 2) A⁻¹ (slConjugation n (ZMod 2) A g) = g := by
    intro g
    rw [← MulAut.mul_apply, ← _root_.map_mul, inv_mul_cancel, _root_.map_one, MulAut.one_apply]
  refine ⟨C'.conjBy A, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · left
    intro l
    show slConjugation n (ZMod 2) A⁻¹ (C'.ρ l) = C.ρ l
    rw [← hα, hσ, pow_zero, mul_one, hcancel]
  · right
    intro l
    show slConjugation n (ZMod 2) A⁻¹ (C'.ρ l) = slGraphAut n (ZMod 2) (C.ρ l)
    rw [← hα, hσ, pow_one, MulAut.mul_apply, hcancel]

theorem eq_one_of_dual (hn : 3 ≤ n) {W' : Subgroup G} {C' : NatCoord L W' n}
    (hd : ∀ l, C'.ρ l = slGraphAut n (ZMod 2) (C.ρ l)) {f : G → G}
    (hfW : ∀ a ∈ W, f a ∈ W') (hf : ∀ a ∈ W, ∀ b ∈ W, f (a * b) = f a * f b)
    (hfl : ∀ (l : ↥L), ∀ a ∈ W, f ((l : G) * a * (l : G)⁻¹) = (l : G) * f a * (l : G)⁻¹) :
    ∀ a ∈ W, f a = 1 := by
  let φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) :=
    AddMonoidHom.mk' (fun x => C'.E (f (C.inv x))) fun x y => by
      rw [C.inv_add, hf _ (C.inv_mem x) _ (C.inv_mem y),
        C'.map_mul _ (hfW _ (C.inv_mem x)) _ (hfW _ (C.inv_mem y))]
  have hφ : φ = 0 := additive_twisted_eq_zero hn fun g x => by
    obtain ⟨l, rfl⟩ := C.ρ_surj g
    show C'.E (f (C.inv _)) = _ *ᵥ C'.E (f (C.inv x))
    rw [C.inv_mulVec, hfl l _ (C.inv_mem x), C'.conj l _ (hfW _ (C.inv_mem x)), hd]
  intro a ha
  have h1 : C'.E (f a) = 0 := by
    have := congrArg (fun ψ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) => ψ (C.E a)) hφ
    simpa only [φ, AddMonoidHom.mk'_apply, AddMonoidHom.zero_apply, C.inv_E ha] using this
  exact C'.eq_one_of_E (hfW a ha) h1

theorem isXSectionIso {W' : Subgroup G} {C' : NatCoord L W' n} (he : ∀ l, C'.ρ l = C.ρ l) :
    IsXSectionIso₂ L W ⊥ W' ⊥ := by
  let φ : ↥W ≃* ↥W' :=
    { toFun := fun a => ⟨C'.inv (C.E a), C'.inv_mem _⟩
      invFun := fun b => ⟨C.inv (C'.E b), C.inv_mem _⟩
      left_inv := fun a => Subtype.ext (by simp only; rw [C'.E_inv, C.inv_E a.2])
      right_inv := fun b => Subtype.ext (by simp only; rw [C.E_inv, C'.inv_E b.2])
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        rw [C.map_mul _ a.2 _ b.2, C'.inv_add]) }
  have hmap : ((⊥ : Subgroup G).subgroupOf W).map (φ : ↥W →* ↥W') =
      (⊥ : Subgroup G).subgroupOf W' := by
    rw [Subgroup.bot_subgroupOf, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have hq : ∀ {K : Subgroup G} (x y : ↥K), (x : ↥K ⧸ (⊥ : Subgroup G).subgroupOf K) = y →
      x = y := by
    intro K x y hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hxy
    have : x⁻¹ * y = 1 := Subtype.ext hxy
    exact (inv_mul_eq_one.1 this)
  refine ⟨inferInstance, inferInstance, QuotientGroup.congr _ _ φ hmap, ?_⟩
  intro x hx j k hj hk hjk
  rw [QuotientGroup.congr_mk] at hjk
  have hjk' : φ j = k := hq _ _ hjk
  rw [QuotientGroup.congr_mk]
  congr 1
  apply Subtype.ext
  show C'.inv (C.E (x * j * x⁻¹)) = x * k * x⁻¹
  have h1 := C.conj ⟨x, hx⟩ j j.2
  have h2 := C'.inv_mulVec ⟨x, hx⟩ (C.E j)
  simp only at h1 h2
  rw [h1, ← he, h2]
  have h3 : C'.inv (C.E j) = k := congrArg Subtype.val hjk'
  rw [h3]

end NatCoord

theorem exists_natCoord {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (h : ∃ _ : IsMulCommutative ↥W, BinaryNaturalSL (V := ↥W) (autOn L W) ⊤ ⊥ n 1) :
    Nonempty (NatCoord L W n) := by
  classical
  obtain ⟨_, hnat⟩ := h
  obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hnat
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv
    (D := FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) rfl hπ
  have hinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful (FFModel.nat_faithful _) hπ
  let πe := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  let σ : ↥L →* ↥(autOn L W) := (Setup.rho W L hLW).codRestrict (autOn L W)
    fun l => (Setup.mem_autOn_self_iff hLW).2 ⟨l, rfl⟩
  have hσ : Function.Surjective σ := by
    rintro ⟨φ, hφ⟩
    obtain ⟨l, rfl⟩ := (Setup.mem_autOn_self_iff hLW).1 hφ
    exact ⟨l, rfl⟩
  let eSL := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)
  let ρ : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2) :=
    (eSL.symm.toMonoidHom.comp πe.symm.toMonoidHom).comp σ
  let coord : ↥W → Fin n → ZMod 2 := fun w => Multiplicative.toAdd (E w).1
  have hcoord : ∀ a b : ↥W, coord (a * b) = coord a + coord b := by
    intro a b
    simp only [coord, map_mul, Subgroup.coe_mul]
    rfl
  have hcinj : ∀ a b : ↥W, coord a = coord b → a = b := by
    intro a b hab
    apply E.injective
    exact Subtype.ext (Multiplicative.toAdd.injective hab)
  refine ⟨⟨fun g => if hg : g ∈ W then coord ⟨g, hg⟩ else 0, ρ, hLW, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro a ha b hb
    simp only [dite_eq_left ha, dite_eq_left hb, dite_eq_left (W.mul_mem ha hb)]
    exact hcoord ⟨a, ha⟩ ⟨b, hb⟩
  · intro a ha b hb hab
    simp only [dite_eq_left ha, dite_eq_left hb] at hab
    exact congrArg Subtype.val (hcinj ⟨a, ha⟩ ⟨b, hb⟩ hab)
  · intro x
    refine ⟨(E.symm ⟨Multiplicative.ofAdd x, Subgroup.mem_top _⟩ : ↥W), Subtype.prop _, ?_⟩
    simp only [Subtype.coe_eta, dite_eq_left (Subtype.prop _)]
    simp only [coord, MulEquiv.apply_symm_apply]
    rfl
  · intro l a ha
    have hla : (l : G) * a * (l : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (hLW l.2) a).1 ha
    simp only [dite_eq_left ha, dite_eq_left hla]
    set γ := πe.symm (σ l) with hγ
    have hπγ : π γ = σ l := πe.apply_symm_apply (σ l)
    have h1 : (⟨(l : G) * a * (l : G)⁻¹, hla⟩ : ↥W) =
        (((π γ : ↥(autOn L W)) : MulAut ↥W) ⟨a, ha⟩) := by
      rw [hπγ]
      apply Subtype.ext
      exact (Setup.rho_apply_coe hLW l ⟨a, ha⟩).symm
    have h2 := hE γ ⟨a, ha⟩
    have h3 : ((ρ l : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        (((γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) : GL (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)) := by
      have := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe n (ZMod 2)
        (eSL.symm γ)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [h1, h3]
    exact congrArg Multiplicative.toAdd h2
  · exact (eSL.symm.surjective.comp πe.symm.surjective).comp hσ

theorem exists_dualCoord [Finite G] {T L V V₁ V₂ : Subgroup G} (hyp : Hyp121 G T L V V₁ V₂ n) :
    ∃ (C₁ : NatCoord L V₁ n) (C₂ : NatCoord L V₂ n),
      ∀ l, C₂.ρ l = slGraphAut n (ZMod 2) (C₁.ρ l) := by
  have hn : 3 ≤ n := by rcases hyp.rank with h | h <;> omega
  obtain ⟨ι⟩ := hyp.iso
  obtain ⟨C₁⟩ := exists_natCoord hyp.norm₁ hyp.nat₁
  obtain ⟨C₂⟩ := exists_natCoord hyp.norm₂ hyp.nat₂
  obtain ⟨C₂', h | h⟩ := C₁.exists_adapted hn ι C₂
  · exact absurd (C₁.isXSectionIso h) hyp.dual
  · exact ⟨C₁, C₂', h⟩

theorem dot_graph (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x z : Fin n → ZMod 2) :
    ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) ⬝ᵥ
      ((slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) = x ⬝ᵥ z := by
  rw [slGraphAut_matrix, Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, coe_inv_mul, Matrix.vecMul_one, dotProduct_comm]

@[expose] def pairing {L V₁ V₂ : Subgroup G} (C₁ : NatCoord L V₁ n) (C₂ : NatCoord L V₂ n)
    (a c : G) : ZMod 2 :=
  C₁.E a ⬝ᵥ C₂.E c

theorem isDualPairing {L V₁ V₂ : Subgroup G} (C₁ : NatCoord L V₁ n) (C₂ : NatCoord L V₂ n)
    (hd : ∀ l, C₂.ρ l = slGraphAut n (ZMod 2) (C₁.ρ l)) :
    IsDualPairing121 L V₁ V₂ (pairing C₁ C₂) := by
  refine ⟨fun a ha b hb c _ => ?_, fun a _ c hc d hd' => ?_, fun a ha ha1 => ?_,
    fun c hc hc1 => ?_, fun l hl a ha c hc => ?_⟩
  · simp only [pairing]
    rw [C₁.map_mul a ha b hb, add_dotProduct]
  · simp only [pairing]
    rw [C₂.map_mul c hc d hd', dotProduct_add]
  · have h0 : C₁.E a ≠ 0 := fun h => ha1 (C₁.eq_one_of_E ha h)
    obtain ⟨k, hk⟩ := exists_eq_one_of_ne_zero h0
    refine ⟨C₂.inv (Pi.single k 1), C₂.inv_mem _, ?_⟩
    simp only [pairing]
    rw [C₂.E_inv, dotProduct_single, hk, mul_one]
  · have h0 : C₂.E c ≠ 0 := fun h => hc1 (C₂.eq_one_of_E hc h)
    obtain ⟨k, hk⟩ := exists_eq_one_of_ne_zero h0
    refine ⟨C₁.inv (Pi.single k 1), C₁.inv_mem _, ?_⟩
    simp only [pairing]
    rw [C₁.E_inv, single_dotProduct, hk, one_mul]
  · simp only [pairing]
    have h1 := C₁.conj ⟨l, hl⟩ a ha
    have h2 := C₂.conj ⟨l, hl⟩ c hc
    simp only at h1 h2
    rw [h1, h2, hd, dot_graph]

theorem eq_pairing (hn : 3 ≤ n) {L V₁ V₂ : Subgroup G} (C₁ : NatCoord L V₁ n)
    (C₂ : NatCoord L V₂ n) (hd : ∀ l, C₂.ρ l = slGraphAut n (ZMod 2) (C₁.ρ l))
    {P : G → G → ZMod 2}
    (hP₁ : ∀ a ∈ V₁, ∀ b ∈ V₁, ∀ c ∈ V₂, P (a * b) c = P a c + P b c)
    (hP₂ : ∀ a ∈ V₁, ∀ c ∈ V₂, ∀ d ∈ V₂, P a (c * d) = P a c + P a d)
    (hL : ∀ l ∈ L, ∀ a ∈ V₁, ∀ c ∈ V₂, P (l * a * l⁻¹) (l * c * l⁻¹) = P a c)
    (hne : ∃ a ∈ V₁, ∃ c ∈ V₂, P a c ≠ 0) :
    ∀ a ∈ V₁, ∀ c ∈ V₂, P a c = pairing C₁ C₂ a c := by
  have _ := hn
  let P' : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2 := fun x z => P (C₁.inv x) (C₂.inv z)
  have h := pairing_eq_zero_or_dot (P := P')
    (fun x x' z => by
      simp only [P']
      rw [C₁.inv_add, hP₁ _ (C₁.inv_mem x) _ (C₁.inv_mem x') _ (C₂.inv_mem z)])
    (fun x z z' => by
      simp only [P']
      rw [C₂.inv_add, hP₂ _ (C₁.inv_mem x) _ (C₂.inv_mem z) _ (C₂.inv_mem z')])
    (fun g x z => by
      obtain ⟨l, rfl⟩ := C₁.ρ_surj g
      simp only [P']
      rw [← hd, C₁.inv_mulVec, C₂.inv_mulVec]
      exact hL _ l.2 _ (C₁.inv_mem x) _ (C₂.inv_mem z))
  have key : ∀ a ∈ V₁, ∀ c ∈ V₂, P a c = P' (C₁.E a) (C₂.E c) := fun a ha c hc => by
    simp only [P']
    rw [C₁.inv_E ha, C₂.inv_E hc]
  rcases h with h0 | h1
  · obtain ⟨a, ha, c, hc, hac⟩ := hne
    exact absurd (by rw [key a ha c hc, h0]) hac
  · intro a ha c hc
    rw [key a ha c hc, h1, pairing, dotProduct_comm]

theorem exists_zpowers [Finite G] {T L V V₁ V₂ : Subgroup G} (hyp : Hyp121 G T L V V₁ V₂ n)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (C₁ : NatCoord L V₁ n) :
    ∃ v₁ : G, V₁ ⊓ Subgroup.centralizer
        ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) =
      Subgroup.zpowers v₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 1 ≤ n := by rcases hyp.rank with h | h <;> omega
  obtain ⟨hT2, hTodd⟩ := hyp.sylow
  have hTM2 : IsPGroup 2 (T.subgroupOf (Subgroup.normalizer (L : Set G))) := hT2.comap_subtype
  have hTModd : ¬ 2 ∣ (T.subgroupOf (Subgroup.normalizer (L : Set G))).index := fun h2 =>
    hTodd (h2.trans (Subgroup.relIndex_dvd_index_of_le hTL))
  let S : Sylow 2 ↥(Subgroup.normalizer (L : Set G)) := hTM2.toSylow hTModd
  have hLM : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal S
    (N := L.subgroupOf (Subgroup.normalizer (L : Set G)))
  let e : ↥(L.subgroupOf (Subgroup.normalizer (L : Set G))) ≃* ↥L :=
    Subgroup.subgroupOfEquivOfLe hLM
  let ψ : ↥(L.subgroupOf (Subgroup.normalizer (L : Set G))) →*
      SpecialLinearGroup (Fin n) (ZMod 2) := C₁.ρ.comp e.toMonoidHom
  have hψ : Function.Surjective ψ := C₁.ρ_surj.comp e.surjective
  let S₁ : Sylow 2 (SpecialLinearGroup (Fin n) (ZMod 2)) := P.mapSurjective hψ
  have hS₁ : ∀ s ∈ (S₁ : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))),
      ∃ l : ↥L, (l : G) ∈ T ∧ C₁.ρ l = s := by
    intro s hs
    rw [Sylow.coe_mapSurjective, Subgroup.mem_map] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    have hx' : x ∈ ((S : Subgroup ↥(Subgroup.normalizer (L : Set G))) ⊓
        L.subgroupOf (Subgroup.normalizer (L : Set G))).subgroupOf
          (L.subgroupOf (Subgroup.normalizer (L : Set G))) := by
      rw [← hP]
      exact hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx'
    exact ⟨e x, hx'.1, rfl⟩
  set X := V₁ ⊓ Subgroup.centralizer
    ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) with hX
  have hfix : ∀ v ∈ X, ∀ s ∈ (S₁ : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))),
      (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ C₁.E v = C₁.E v := by
    intro v hv s hs
    obtain ⟨l, hlT, rfl⟩ := hS₁ s hs
    rw [← C₁.conj l v hv.1]
    have hl1 : (l : G) ∈ T ⊓ Subgroup.normalizer (V₁ : Set G) := ⟨hlT, C₁.le l.2⟩
    have hc := Subgroup.mem_centralizer_iff.1 hv.2 (l : G) hl1
    rw [hc, mul_inv_cancel_right]
  by_cases h : ∃ v, v ∈ X ∧ v ≠ 1
  · obtain ⟨v, hv, hv1⟩ := h
    refine ⟨v, le_antisymm (fun w hw => ?_) (Subgroup.zpowers_le.2 hv)⟩
    by_cases hw1 : w = 1
    · rw [hw1]
      exact Subgroup.one_mem _
    · have hvw := eq_of_fixed_sylow hn S₁ (hfix v hv) (hfix w hw)
        (fun h0 => hv1 (C₁.eq_one_of_E hv.1 h0)) (fun h0 => hw1 (C₁.eq_one_of_E hw.1 h0))
      rw [← C₁.inj v hv.1 w hw.1 hvw]
      exact Subgroup.mem_zpowers v
  · refine ⟨1, ?_⟩
    rw [Subgroup.zpowers_one_eq_bot, eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    by_contra hw1
    exact h ⟨w, hw, hw1⟩

end CFSG.Quasithin.H13.KGH91
