module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.RankThree.FFModules.BinaryTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CommutingBlocks
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

structure w1369_s16h_Proj {Q : Type} [CommGroup Q] {k : ℕ} (I : Fin k → Subgroup Q)
    (Λ : Subgroup (MulAut Q)) where
  e : Fin k → Q →* Q
  e_mem : ∀ i x, e i x ∈ I i
  e_self : ∀ i x (hx : x ∈ I i), e i x = x
  e_other : ∀ i j, j ≠ i → ∀ x (hx : x ∈ I j), e i x = 1
  e_prod : ∀ x, ∏ i, e i x = x
  e_equiv : ∀ i, ∀ g ∈ Λ, ∀ x, e i (g x) = g (e i x)

@[expose] noncomputable def w1369_s16h_mkProj {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q}
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hspan : ⨆ i, I i = ⊤)
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥) :
    w1369_s16h_Proj I Λ := by
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

@[expose] noncomputable def w1369_s16h_block {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ) (c : MulAut Q) (i j : Fin k) :
    I j →* I i :=
  MonoidHom.codRestrict ((P.e i).comp (c.toMonoidHom.comp (I j).subtype)) (I i)
    (fun x => P.e_mem i _)

lemma w1369_s16h_block_coe {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ) (c : MulAut Q) (i j : Fin k)
    (x : I j) : ((w1369_s16h_block P c i j x : I i) : Q) = P.e i (c (x : Q)) := rfl

lemma w1369_s16h_block_equivariant {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i) {c : MulAut Q}
    (hc : ∀ g ∈ Λ, ∀ x, c (g x) = g (c x)) (i j : Fin k) :
    ∀ g (hg : g ∈ Λ) (x : I j),
      ((w1369_s16h_block P c i j ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : I i) : Q) =
        g ((w1369_s16h_block P c i j x : I i) : Q) := by
  intro g hg x
  rw [w1369_s16h_block_coe, w1369_s16h_block_coe, hc g hg (x : Q), P.e_equiv i g hg]

lemma w1369_s16h_hom_zero_or_bij {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q}
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    {i j : Fin k} (φ : I j →* I i)
    (heq : ∀ g (hg : g ∈ Λ) (x : I j),
      (φ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : Q) = g (φ x : Q)) :
    φ = 1 ∨ Function.Bijective φ := by
  classical
  let K : Subgroup Q := φ.ker.map (I j).subtype
  have hK_le : K ≤ I j := by
    rintro y ⟨a, _, rfl⟩
    exact a.2
  have hK_stable : ∀ g ∈ Λ, ∀ y ∈ K, g y ∈ K := by
    rintro g hg y ⟨a, ha, rfl⟩
    refine Subgroup.mem_map.mpr ⟨⟨g (a : Q), hstab j g hg (a : Q) a.2⟩, ?_, rfl⟩
    have h := heq g hg a
    rw [MonoidHom.mem_ker.mp ha] at h
    exact Subtype.ext (by simpa using h)
  let L : Subgroup Q := φ.range.map (I i).subtype
  have hL_le : L ≤ I i := by
    rintro y ⟨z, _, rfl⟩
    exact z.2
  have hL_stable : ∀ g ∈ Λ, ∀ y ∈ L, g y ∈ L := by
    rintro g hg y ⟨z, hz, rfl⟩
    rcases MonoidHom.mem_range.mp hz with ⟨x, rfl⟩
    exact Subgroup.mem_map.mpr ⟨φ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩, ⟨_, rfl⟩,
      heq g hg x⟩
  by_cases hLbot : L = ⊥
  · left
    have hφ1 : φ = 1 := by
      ext x
      have hxL : (I i).subtype (φ x) ∈ L :=
        Subgroup.mem_map.mpr ⟨φ x, ⟨x, rfl⟩, rfl⟩
      rw [hLbot] at hxL
      simpa using hxL
    exact hφ1
  · right
    have hL : L = I i := by
      rcases (hsimple i).2 L hL_stable hL_le with h | h
      · exact absurd h hLbot
      · exact h
    have hφ1_of_K : φ.ker.map (I j).subtype = I j → φ = 1 := by
      intro htop
      ext x
      have hxK : (I j).subtype x ∈ K := by
        change (I j).subtype x ∈ φ.ker.map (I j).subtype
        rw [htop]
        exact x.2
      rcases Subgroup.mem_map.mp hxK with ⟨a, ha, hax⟩
      have ha' : a = x := Subtype.ext hax
      have ha1 : φ a = 1 := by simpa using ha
      rw [← ha', ha1]
      rfl
    have hK : φ.ker = ⊥ := by
      rcases (hsimple j).2 K hK_stable hK_le with hbot | htop
      · rw [← le_bot_iff]
        intro x hx
        have hxK : (I j).subtype x ∈ K := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        rw [hbot] at hxK
        exact Subtype.ext (by simpa using hxK)
      · exfalso
        apply hLbot
        have hφ1 : φ = 1 := hφ1_of_K htop
        change φ.range.map (I i).subtype = ⊥
        rw [hφ1]
        simp
    refine ⟨(MonoidHom.ker_eq_bot_iff φ).mp hK, ?_⟩
    intro y
    have hy : (y : Q) ∈ L := by
      rw [hL]
      exact y.2
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
    rcases MonoidHom.mem_range.mp hz with ⟨x, hx⟩
    exact ⟨x, Subtype.ext (by rw [hx]; exact hzy)⟩

lemma w1369_s16h_endomorphism_id {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {i : Fin k} (φ : I i →* I i) (hbij : Function.Bijective φ)
    (heq : ∀ g (hg : g ∈ Λ) (x : I i),
      (φ ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩ : Q) = g (φ x : Q)) :
    φ = MonoidHom.id (I i) := by
  classical
  let ei' : Q →* I i := MonoidHom.codRestrict (P.e i) (I i) (fun x => P.e_mem i x)
  have hei_self : ∀ x (hx : x ∈ I i), ei' x = ⟨x, hx⟩ := by
    intro x hx
    apply Subtype.ext
    exact P.e_self i x hx
  have hei_other : ∀ j, j ≠ i → ∀ x (hx : x ∈ I j), ei' x = 1 := by
    intro j hj x hx
    apply Subtype.ext
    exact P.e_other i j hj x hx
  let f : Q →* Q := (I i).subtype.comp (φ.comp ei')
  have hfcomm : ∀ g ∈ Λ, ∀ x, f (g x) = g (f x) := by
    intro g hg x
    change (φ (ei' (g x)) : Q) = g (φ (ei' x) : Q)
    have h1 : (ei' (g x) : Q) = g (ei' x : Q) := P.e_equiv i g hg x
    have hgx : ei' (g x) = ⟨g (ei' x : Q), hstab i g hg (ei' x : Q) (ei' x).2⟩ :=
      Subtype.ext h1
    rw [hgx]
    exact heq g hg (ei' x)
  have hfmem : ∀ x ∈ I i, f x ∈ I i := fun x _ => (φ (ei' x)).2
  have hfkill : ∀ j, j ≠ i → ∀ x ∈ I j, f x = 1 := by
    intro j hj x hx
    change (φ (ei' x) : Q) = 1
    rw [hei_other j hj x hx, map_one]
    rfl
  rcases hend i f hfcomm hfmem hfkill with hid | hone
  · ext x
    have h := hid (x : Q) x.2
    have h2 : (φ x : Q) = (x : Q) := by
      calc (φ x : Q) = (φ (ei' (x : Q)) : Q) := by rw [hei_self (x : Q) x.2]
        _ = (f (x : Q) : Q) := rfl
        _ = (x : Q) := h
    exact h2
  · exfalso
    have hφ1 : φ = 1 := by
      ext x
      have h := hone (x : Q) x.2
      have h2 : (φ x : Q) = 1 := by
        calc (φ x : Q) = (φ (ei' (x : Q)) : Q) := by rw [hei_self (x : Q) x.2]
          _ = (f (x : Q) : Q) := rfl
          _ = 1 := h
      exact h2
    obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hsimple i).1
    have hx1 : x = 1 := hbij.1 (by rw [hφ1]; rfl)
    exact hxne hx1

lemma w1369_s16h_inv_equivariant {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q}
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    {i j : Fin k} (φ : I j →* I i) (hbij : Function.Bijective φ)
    (heq : ∀ g (hg : g ∈ Λ) (x : I j),
      (φ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : Q) = g (φ x : Q)) :
    ∀ g (hg : g ∈ Λ) (y : I i),
      (((MulEquiv.ofBijective φ hbij).symm ⟨g (y : Q), hstab i g hg (y : Q) y.2⟩ : I j) : Q) =
        g (((MulEquiv.ofBijective φ hbij).symm y : I j) : Q) := by
  intro g hg y
  let Φ : I j ≃* I i := MulEquiv.ofBijective φ hbij
  change ((Φ.symm ⟨g (y : Q), hstab i g hg (y : Q) y.2⟩ : I j) : Q) =
    g ((Φ.symm y : I j) : Q)
  rw [show g ((Φ.symm y : I j) : Q) =
      ((⟨g ((Φ.symm y : I j) : Q), hstab j g hg ((Φ.symm y : I j) : Q) (Φ.symm y).2⟩ :
        I j) : Q) from rfl]
  apply congrArg (fun z : I j => (z : Q))
  apply hbij.1
  change Φ (Φ.symm ⟨g (y : Q), hstab i g hg (y : Q) y.2⟩) =
    Φ ⟨g ((Φ.symm y : I j) : Q), hstab j g hg ((Φ.symm y : I j) : Q) (Φ.symm y).2⟩
  rw [Φ.apply_symm_apply]
  apply Subtype.ext
  change (g (y : Q)) = ((φ ⟨g ((Φ.symm y : I j) : Q),
    hstab j g hg ((Φ.symm y : I j) : Q) (Φ.symm y).2⟩ : I i) : Q)
  have h2 : φ (Φ.symm y) = y := Φ.apply_symm_apply y
  rw [heq g hg (Φ.symm y), h2]

lemma w1369_s16h_bijective_unique {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {i j : Fin k} (φ ψ : I j →* I i)
    (hφ : Function.Bijective φ) (hψ : Function.Bijective ψ)
    (hφe : ∀ g (hg : g ∈ Λ) (x : I j),
      (φ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : Q) = g (φ x : Q))
    (hψe : ∀ g (hg : g ∈ Λ) (x : I j),
      (ψ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : Q) = g (ψ x : Q)) :
    φ = ψ := by
  classical
  by_cases hij : i = j
  · subst hij
    rw [w1369_s16h_endomorphism_id P hstab hsimple hend φ hφ hφe,
      w1369_s16h_endomorphism_id P hstab hsimple hend ψ hψ hψe]
  · let Φ : I j ≃* I i := MulEquiv.ofBijective φ hφ
    let Ψ : I j ≃* I i := MulEquiv.ofBijective ψ hψ
    let τ : I j ≃* I j := Ψ.trans Φ.symm
    have hτbij : Function.Bijective τ := τ.bijective
    have hτe : ∀ g (hg : g ∈ Λ) (x : I j),
        (τ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : Q) = g (τ x : Q) := by
      intro g hg x
      change ((Φ.symm (Ψ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩) : I j) : Q) =
        g ((Φ.symm (Ψ x) : I j) : Q)
      have h1 : Ψ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ =
          ⟨g (Ψ x : Q), hstab i g hg (Ψ x : Q) (Ψ x).2⟩ :=
        Subtype.ext (hψe g hg x)
      rw [h1]
      exact w1369_s16h_inv_equivariant hstab φ hφ hφe g hg (Ψ x)
    have hτid : τ.toMonoidHom = MonoidHom.id (I j) :=
      w1369_s16h_endomorphism_id P hstab hsimple hend τ.toMonoidHom hτbij hτe
    ext x
    have hx : (Φ.symm (Ψ x) : I j) = x := by
      have := congrArg (fun f : I j →* I j => f x) hτid
      simpa [τ] using this
    have h2 : Ψ x = Φ x := by
      calc Ψ x = Φ (Φ.symm (Ψ x)) := (Φ.apply_symm_apply (Ψ x)).symm
        _ = Φ x := by rw [hx]
    exact congrArg (fun z : I i => (z : Q)) h2.symm

lemma w1369_s16h_block_one_or_bij {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    {c : MulAut Q} (hc : ∀ g ∈ Λ, ∀ x, c (g x) = g (c x)) (i j : Fin k) :
    w1369_s16h_block P c i j = 1 ∨ Function.Bijective (w1369_s16h_block P c i j) :=
  w1369_s16h_hom_zero_or_bij hstab hsimple _ (w1369_s16h_block_equivariant P hstab hc i j)

noncomputable def w1369_s16h_comp_block {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ) (c c' : MulAut Q)
    (i l j : Fin k) : I j →* I i :=
  (w1369_s16h_block P c i l).comp (w1369_s16h_block P c' l j)

lemma w1369_s16h_comp_block_bijective {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ) {c c' : MulAut Q}
    (i l j : Fin k) (h1 : Function.Bijective (w1369_s16h_block P c i l))
    (h2 : Function.Bijective (w1369_s16h_block P c' l j)) :
    Function.Bijective (w1369_s16h_comp_block P c c' i l j) := h1.comp h2

lemma w1369_s16h_comp_block_equivariant {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    {c c' : MulAut Q} (hc : ∀ g ∈ Λ, ∀ x, c (g x) = g (c x))
    (hc' : ∀ g ∈ Λ, ∀ x, c' (g x) = g (c' x)) (i l j : Fin k) :
    ∀ g (hg : g ∈ Λ) (x : I j),
      ((w1369_s16h_comp_block P c c' i l j ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : I i) : Q) =
        g ((w1369_s16h_comp_block P c c' i l j x : I i) : Q) := by
  intro g hg x
  have h2 := w1369_s16h_block_equivariant P hstab hc' l j g hg x
  have h2' : w1369_s16h_block P c' l j ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ =
      ⟨g ((w1369_s16h_block P c' l j x : I l) : Q),
        hstab l g hg ((w1369_s16h_block P c' l j x : I l) : Q) (w1369_s16h_block P c' l j x).2⟩ :=
    Subtype.ext h2
  change ((w1369_s16h_block P c i l (w1369_s16h_block P c' l j
    ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩) : I i) : Q) =
    g ((w1369_s16h_block P c i l (w1369_s16h_block P c' l j x) : I i) : Q)
  rw [h2']
  exact w1369_s16h_block_equivariant P hstab hc i l g hg (w1369_s16h_block P c' l j x)

lemma w1369_s16h_block_prod_formula {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ) (c c' : MulAut Q)
    (i j : Fin k) (x : I j) :
    ((w1369_s16h_block P (c * c') i j x : I i) : Q) =
      ∏ l : Fin k, ((w1369_s16h_block P c i l (w1369_s16h_block P c' l j x) : I i) : Q) := by
  calc
    ((w1369_s16h_block P (c * c') i j x : I i) : Q) = P.e i ((c * c') (x : Q)) := rfl
    _ = P.e i (c (c' (x : Q))) := rfl
    _ = P.e i (c (∏ l : Fin k, P.e l (c' (x : Q)))) := by
      rw [P.e_prod (c' (x : Q))]
    _ = P.e i (∏ l : Fin k, c (P.e l (c' (x : Q)))) := by
      congr 1
      exact map_prod (c : Q →* Q) (fun l => P.e l (c' (x : Q))) Finset.univ
    _ = ∏ l : Fin k, P.e i (c (P.e l (c' (x : Q)))) := by
      exact map_prod (P.e i) (fun l => c (P.e l (c' (x : Q)))) Finset.univ
    _ = ∏ l : Fin k, ((w1369_s16h_block P c i l (w1369_s16h_block P c' l j x) : I i) : Q) := by
      apply Finset.prod_congr rfl
      intro l _
      rfl

lemma w1369_s16h_pow_even {G : Type} [Group G] {y : G} (hy : y ^ 2 = 1) (m : ℕ) :
    y ^ (2 * m) = 1 := by
  rw [pow_mul, hy, one_pow]

lemma w1369_s16h_pow_odd {G : Type} [Group G] {y : G} (hy : y ^ 2 = 1) (m : ℕ) :
    y ^ (2 * m + 1) = y := by
  rw [pow_succ, w1369_s16h_pow_even hy, one_mul]

@[expose] noncomputable def w1369_s16h_matrix {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ) (c : MulAut Q) :
    Matrix (Fin k) (Fin k) (ZMod 2) := by
  classical
  exact Matrix.of fun i j => if w1369_s16h_block P c i j = 1 then 0 else 1

lemma w1369_s16h_matrix_one {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i) :
    w1369_s16h_matrix P 1 = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij
    have hblock : w1369_s16h_block P (1 : MulAut Q) i i = MonoidHom.id (I i) := by
      ext x
      rw [w1369_s16h_block_coe P (1 : MulAut Q) i i x]
      simpa using P.e_self i (x : Q) x.2
    have hne : w1369_s16h_block P (1 : MulAut Q) i i ≠ 1 := by
      intro h1
      obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hsimple i).1
      have h := congrArg (fun f : I i →* I i => f x) h1
      have hx' : (x : I i) = 1 := by simpa [hblock] using h
      exact hx hx'
    rw [w1369_s16h_matrix, Matrix.of_apply, if_neg hne, Matrix.one_apply_eq]
  · have h1 : w1369_s16h_block P (1 : MulAut Q) i j = 1 := by
      ext x
      rw [w1369_s16h_block_coe P (1 : MulAut Q) i j x, MulAut.one_apply]
      rw [P.e_other i j (Ne.symm hij) (x : Q) x.2, MonoidHom.one_apply]
      rfl
    rw [w1369_s16h_matrix, Matrix.of_apply, if_pos h1, Matrix.one_apply_ne hij]

lemma w1369_s16h_block_mul_eq_one_iff {Q : Type} [CommGroup Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {c c' : MulAut Q} (hc : ∀ g ∈ Λ, ∀ x, c (g x) = g (c x))
    (hc' : ∀ g ∈ Λ, ∀ x, c' (g x) = g (c' x)) (i j : Fin k) :
    w1369_s16h_block P (c * c') i j = 1 ↔
      Even (@Finset.filter (Fin k) (fun l =>
        w1369_s16h_block P c i l ≠ 1 ∧ w1369_s16h_block P c' l j ≠ 1)
        (fun l => Classical.dec _) Finset.univ).card := by
  classical
  let S : Finset (Fin k) :=
    @Finset.filter (Fin k) (fun l => w1369_s16h_block P c i l ≠ 1 ∧ w1369_s16h_block P c' l j ≠ 1)
      (fun l => Classical.dec _) Finset.univ
  have hmemS : ∀ l, l ∈ S ↔ w1369_s16h_block P c i l ≠ 1 ∧ w1369_s16h_block P c' l j ≠ 1 := by
    intro l
    simp [S]
  have hcomp_bij : ∀ l ∈ S, Function.Bijective (w1369_s16h_comp_block P c c' i l j) := by
    intro l hl
    rw [hmemS] at hl
    have hb1 := (w1369_s16h_block_one_or_bij P hstab hsimple hc i l).resolve_left hl.1
    have hb2 := (w1369_s16h_block_one_or_bij P hstab hsimple hc' l j).resolve_left hl.2
    exact w1369_s16h_comp_block_bijective P i l j hb1 hb2
  have hterm_out : ∀ (x : I j) (l : Fin k), l ∉ S →
      ((w1369_s16h_comp_block P c c' i l j x : I i) : Q) = 1 := by
    intro x l hl
    by_cases h1 : w1369_s16h_block P c i l = 1
    · simp [w1369_s16h_comp_block, h1]
    · have h2 : w1369_s16h_block P c' l j = 1 := by
        by_contra h2
        exact hl (by rw [hmemS]; exact ⟨h1, h2⟩)
      simp [w1369_s16h_comp_block, h2]
  have hprod_subset : ∀ x : I j,
      (∏ l : Fin k, ((w1369_s16h_comp_block P c c' i l j x : I i) : Q)) =
        ∏ l ∈ S, ((w1369_s16h_comp_block P c c' i l j x : I i) : Q) := by
    intro x
    symm
    exact Finset.prod_subset (Finset.subset_univ S) (fun l _ hl => hterm_out x l hl)
  constructor
  · intro hblock
    by_contra hne
    have hodd : Odd S.card := Nat.not_even_iff_odd.mp hne
    have hSpos : 0 < S.card := by
      rcases hodd with ⟨m, hm⟩
      omega
    obtain ⟨l0, hl0⟩ := Finset.card_pos.mp hSpos
    have hterm_eq : ∀ (x : I j) (l : Fin k), l ∈ S →
        ((w1369_s16h_comp_block P c c' i l j x : I i) : Q) =
          ((w1369_s16h_comp_block P c c' i l0 j x : I i) : Q) := by
      intro x l hl
      have hcomp_eq : w1369_s16h_comp_block P c c' i l j =
          w1369_s16h_comp_block P c c' i l0 j :=
        w1369_s16h_bijective_unique P hstab hsimple hend _ _ (hcomp_bij l hl) (hcomp_bij l0 hl0)
          (w1369_s16h_comp_block_equivariant P hstab hc hc' i l j)
          (w1369_s16h_comp_block_equivariant P hstab hc hc' i l0 j)
      rw [hcomp_eq]
    have hcomp1 : w1369_s16h_comp_block P c c' i l0 j = 1 := by
      ext x
      have hprod1 : (∏ l : Fin k, ((w1369_s16h_comp_block P c c' i l j x : I i) : Q)) = 1 := by
        change (∏ l : Fin k,
          ((w1369_s16h_block P c i l (w1369_s16h_block P c' l j x) : I i) : Q)) = 1
        rw [← w1369_s16h_block_prod_formula P c c' i j x]
        exact congrArg (fun z : I i => (z : Q))
          (by simpa using congrArg (fun f : I j →* I i => f x) hblock)
      have hpow : (∏ l ∈ S, ((w1369_s16h_comp_block P c c' i l j x : I i) : Q)) =
          ((w1369_s16h_comp_block P c c' i l0 j x : I i) : Q) ^ S.card := by
        apply Finset.prod_eq_pow_card
        intro l hl
        exact hterm_eq x l hl
      rw [hprod_subset x, hpow] at hprod1
      rcases hodd with ⟨m, hm⟩
      rw [hm, w1369_s16h_pow_odd (hQ _) m] at hprod1
      exact hprod1
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hsimple j).1
    have hx1 : x = 1 := (hcomp_bij l0 hl0).1 (by rw [hcomp1]; rfl)
    exact hx hx1
  · intro heven
    by_cases hS : S.Nonempty
    · obtain ⟨l0, hl0⟩ := hS
      have hterm_eq : ∀ (x : I j) (l : Fin k), l ∈ S →
          ((w1369_s16h_comp_block P c c' i l j x : I i) : Q) =
            ((w1369_s16h_comp_block P c c' i l0 j x : I i) : Q) := by
        intro x l hl
        have hcomp_eq : w1369_s16h_comp_block P c c' i l j =
            w1369_s16h_comp_block P c c' i l0 j :=
          w1369_s16h_bijective_unique P hstab hsimple hend _ _ (hcomp_bij l hl) (hcomp_bij l0 hl0)
            (w1369_s16h_comp_block_equivariant P hstab hc hc' i l j)
            (w1369_s16h_comp_block_equivariant P hstab hc hc' i l0 j)
        rw [hcomp_eq]
      ext x
      have hpow : (∏ l ∈ S, ((w1369_s16h_comp_block P c c' i l j x : I i) : Q)) =
          ((w1369_s16h_comp_block P c c' i l0 j x : I i) : Q) ^ S.card := by
        apply Finset.prod_eq_pow_card
        intro l hl
        exact hterm_eq x l hl
      rw [w1369_s16h_block_prod_formula P c c' i j x]
      change (∏ l : Fin k, ((w1369_s16h_comp_block P c c' i l j x : I i) : Q)) = (1 : Q)
      rw [hprod_subset x, hpow]
      rcases heven with ⟨m, hm⟩
      rw [hm]
      simpa only [two_mul] using w1369_s16h_pow_even (hQ _) m
    · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      ext x
      rw [w1369_s16h_block_prod_formula P c c' i j x]
      change (∏ l : Fin k, ((w1369_s16h_comp_block P c c' i l j x : I i) : Q)) = (1 : Q)
      rw [hprod_subset x, hSempty]
      simp

lemma w1369_s16h_matrix_mul {Q : Type} [CommGroup Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {c c' : MulAut Q} (hc : ∀ g ∈ Λ, ∀ x, c (g x) = g (c x))
    (hc' : ∀ g ∈ Λ, ∀ x, c' (g x) = g (c' x)) :
    w1369_s16h_matrix P (c * c') = w1369_s16h_matrix P c * w1369_s16h_matrix P c' := by
  classical
  ext i j
  simp only [w1369_s16h_matrix, Matrix.of_apply, Matrix.mul_apply]
  let S : Finset (Fin k) :=
    @Finset.filter (Fin k) (fun l =>
      w1369_s16h_block P c i l ≠ 1 ∧ w1369_s16h_block P c' l j ≠ 1)
      (fun l => Classical.dec _) Finset.univ
  have hS : ∀ l, l ∈ S ↔ w1369_s16h_block P c i l ≠ 1 ∧ w1369_s16h_block P c' l j ≠ 1 := by
    simp [S]
  have hterm : ∀ l : Fin k,
      (if w1369_s16h_block P c i l = 1 then 0 else 1) *
        (if w1369_s16h_block P c' l j = 1 then 0 else 1) =
        (if l ∈ S then (1 : ZMod 2) else 0) := by
    intro l
    by_cases h : l ∈ S
    · rw [if_pos h]
      obtain ⟨h1, h2⟩ := (hS l).mp h
      simp [h1, h2]
    · rw [if_neg h]
      have h' : ¬ (w1369_s16h_block P c i l ≠ 1 ∧ w1369_s16h_block P c' l j ≠ 1) :=
        fun hc => h ((hS l).mpr hc)
      simp only [not_and_or, not_not] at h'
      rcases h' with h1 | h2
      · simp [h1]
      · simp [h2]
  have hsum : (∑ l : Fin k, (if w1369_s16h_block P c i l = 1 then 0 else 1) *
      (if w1369_s16h_block P c' l j = 1 then 0 else 1)) = ((S.card : ℕ) : ZMod 2) := by
    rw [Finset.sum_congr rfl (fun l _ => hterm l)]
    simp [Finset.sum_ite_mem]
  rw [hsum, w1369_s16h_block_mul_eq_one_iff hQ P hstab hsimple hend hc hc' i j]
  by_cases he : Even S.card
  · rw [if_pos he, ZMod.natCast_eq_zero_iff_even.mpr he]
  · rw [if_neg he, ZMod.natCast_eq_one_iff_odd.mpr (Nat.not_even_iff_odd.mp he)]

lemma w1369_s16h_cent_comm {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {c : MulAut Q} (hc : c ∈ Subgroup.centralizer (Λ : Set (MulAut Q))) :
    ∀ g ∈ Λ, ∀ x, c (g x) = g (c x) := by
  intro g hg x
  have h := Subgroup.mem_centralizer_iff.mp hc g hg
  exact (congrArg (fun f : MulAut Q => f x) h).symm

@[expose] noncomputable def w1369_s16h_matrixHom {Q : Type} [CommGroup Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1)) :
    Subgroup.centralizer (Λ : Set (MulAut Q)) →* GL (Fin k) (ZMod 2) where
  toFun c :=
    { val := w1369_s16h_matrix P (c : MulAut Q)
      inv := w1369_s16h_matrix P ((c : MulAut Q)⁻¹)
      val_inv := by
        rw [← w1369_s16h_matrix_mul hQ P hstab hsimple hend (w1369_s16h_cent_comm c.2)
          (w1369_s16h_cent_comm (Subgroup.inv_mem _ c.2))]
        simp [w1369_s16h_matrix_one P hsimple]
      inv_val := by
        rw [← w1369_s16h_matrix_mul hQ P hstab hsimple hend
          (w1369_s16h_cent_comm (Subgroup.inv_mem _ c.2)) (w1369_s16h_cent_comm c.2)]
        simp [w1369_s16h_matrix_one P hsimple] }
  map_one' := by
    apply Units.ext
    exact w1369_s16h_matrix_one P hsimple
  map_mul' := fun c c' => by
    apply Units.ext
    rw [Units.val_mul]
    exact w1369_s16h_matrix_mul hQ P hstab hsimple hend (w1369_s16h_cent_comm c.2)
      (w1369_s16h_cent_comm c'.2)

lemma w1369_s16h_matrixHom_eq_one {Q : Type} [CommGroup Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {c : MulAut Q} (hc : c ∈ Subgroup.centralizer (Λ : Set (MulAut Q)))
    (hM : w1369_s16h_matrix P c = 1) : c = 1 := by
  classical
  have hc' := w1369_s16h_cent_comm hc
  have hdiag : ∀ i, w1369_s16h_block P c i i = MonoidHom.id (I i) := by
    intro i
    have hne : w1369_s16h_block P c i i ≠ 1 := by
      intro h1
      have h2 : (w1369_s16h_matrix P c) i i = 0 := by
        simp [w1369_s16h_matrix, h1]
      have h3 : (w1369_s16h_matrix P c) i i = 1 := by
        rw [hM, Matrix.one_apply_eq]
      rw [h2] at h3
      exact zero_ne_one h3
    rcases w1369_s16h_block_one_or_bij P hstab hsimple hc' i i with h1 | hbij
    · exact absurd h1 hne
    · exact w1369_s16h_endomorphism_id P hstab hsimple hend _ hbij
        (w1369_s16h_block_equivariant P hstab hc' i i)
  have hoff : ∀ i j, i ≠ j → w1369_s16h_block P c i j = 1 := by
    intro i j hij
    by_contra h1
    have h2 : (w1369_s16h_matrix P c) i j = 1 := by
      simp [w1369_s16h_matrix, h1]
    have h3 : (w1369_s16h_matrix P c) i j = 0 := by
      rw [hM]
      exact Matrix.one_apply_ne hij
    rw [h2] at h3
    exact one_ne_zero h3
  ext x
  have h_on : ∀ i (y : I i), c (y : Q) = (y : Q) := by
    intro i y
    calc c (y : Q) = ∏ l : Fin k, P.e l (c (y : Q)) := (P.e_prod (c (y : Q))).symm
      _ = ∏ l : Fin k, P.e l (y : Q) := by
        apply Finset.prod_congr rfl
        intro l _
        by_cases hli : l = i
        · subst hli
          have h := congrArg (fun f : I l →* I l => f y) (hdiag l)
          rw [show P.e l (c (y : Q)) = (w1369_s16h_block P c l l y : Q) from
            (w1369_s16h_block_coe P c l l y).symm]
          rw [show P.e l (y : Q) = (y : Q) from P.e_self l (y : Q) y.2]
          exact congrArg (fun z : I l => (z : Q)) h
        · have h := congrArg (fun f : I i →* I l => f y) (hoff l i hli)
          have h1 : P.e l (c (y : Q)) = 1 := by
            rw [show P.e l (c (y : Q)) = (w1369_s16h_block P c l i y : Q) from
              (w1369_s16h_block_coe P c l i y).symm]
            exact congrArg (fun z : I l => (z : Q)) h
          have h2 : P.e l (y : Q) = 1 := P.e_other l i (Ne.symm hli) (y : Q) y.2
          rw [h1, h2]
      _ = (y : Q) := P.e_prod y
  calc c x = c (∏ i : Fin k, P.e i x) := by rw [P.e_prod x]
    _ = ∏ i : Fin k, c (P.e i x) := by rw [map_prod]
    _ = ∏ i : Fin k, P.e i x := by
      apply Finset.prod_congr rfl
      intro i _
      exact h_on i ⟨P.e i x, P.e_mem i x⟩
    _ = x := P.e_prod x

lemma w1369_s16h_matrixHom_injective {Q : Type} [CommGroup Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1)) :
    Function.Injective (w1369_s16h_matrixHom hQ P hstab hsimple hend) := by
  intro c c' hcc'
  have h : (w1369_s16h_matrixHom hQ P hstab hsimple hend) (c * c'⁻¹) = 1 := by
    rw [map_mul, map_inv, hcc', mul_inv_cancel]
  have h' : w1369_s16h_matrix P
      ((c * c'⁻¹ : Subgroup.centralizer (Λ : Set (MulAut Q))) : MulAut Q) = 1 :=
    congrArg Units.val h
  have h2 := w1369_s16h_matrixHom_eq_one hQ P hstab hsimple hend (c * c'⁻¹).2 h'
  have h3 : c * c'⁻¹ = 1 := Subtype.ext h2
  rw [mul_inv_eq_one] at h3
  exact h3


variable {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q}

abbrev w1369_Iso (Λ : Subgroup (MulAut Q)) (I : Fin k → Subgroup Q) (i j : Fin k) : Prop :=
  XMod.Iso ↥Λ (I i) (I j)

abbrev w1369_Singleton (Λ : Subgroup (MulAut Q)) (I : Fin k → Subgroup Q) (i : Fin k) :
    Prop :=
  ∀ j : Fin k, j ≠ i → ¬ w1369_Iso Λ I i j

theorem w1369_secIsoOn_of_iso {A B : Subgroup Q}
    (hA : StableUnder Λ A) (hB : StableUnder Λ B) (h : XMod.Iso ↥Λ A B) :
    SecIsoOn Λ A ⊥ B ⊥ := by
  classical
  obtain ⟨e, he⟩ := h
  refine ⟨bot_le, bot_le, hA, ?_, hB, ?_, B.subtype.comp e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro x hx u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro x hx u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro a
    exact (e a).2
  · intro a
    constructor
    · intro h1
      have h2 : e a = 1 := Subtype.ext (Subgroup.mem_bot.mp h1)
      have ha1 : a = 1 := e.injective (by rw [h2, map_one])
      simpa using congrArg Subtype.val ha1
    · intro h1
      have h1' : a = 1 := Subtype.ext (Subgroup.mem_bot.mp h1)
      rw [h1', map_one]
      exact Subgroup.one_mem (⊥ : Subgroup Q)
  · intro b hb
    refine ⟨e.symm ⟨b, hb⟩, ?_⟩
    simp
  · intro x hx a a' ha'
    rw [Subgroup.mem_bot]
    have h := he ⟨x, hx⟩ a a' (by simpa [Subgroup.smul_def, MulAut.smul_def] using ha'.symm)
    exact mul_inv_eq_one.mpr (by simpa [Subgroup.smul_def, MulAut.smul_def] using h.symm)

theorem w1369_iso_of_bij_block {P : w1369_s16h_Proj I Λ}
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i) {f : MulAut Q}
    (hf : ∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) (i j : Fin k)
    (hbij : Function.Bijective (w1369_s16h_block P f j i)) :
    w1369_Iso Λ I i j := by
  classical
  let e : I i ≃* I j := MulEquiv.ofBijective (w1369_s16h_block P f j i) hbij
  refine ⟨e, fun a l l' hl => ?_⟩
  have heq := w1369_s16h_block_equivariant P hstab hf j i (a : MulAut Q) a.2 l
  have hll' : (⟨(a : MulAut Q) (l : Q),
      hstab i (a : MulAut Q) a.2 (l : Q) l.2⟩ : I i) = l' :=
    Subtype.ext (by simpa [Subgroup.smul_def, MulAut.smul_def] using hl)
  have h1 : ((e l' : I j) : Q) = (a : MulAut Q) ((e l : I j) : Q) := by
    rw [← hll']
    exact heq
  simpa [Subgroup.smul_def, MulAut.smul_def] using h1.symm

theorem w1369_cent_preserves_singleton {P : w1369_s16h_Proj I Λ}
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ I i →
      J = ⊥ ∨ J = I i)
    {f : MulAut Q} (hf : f ∈ Subgroup.centralizer (Λ : Set (MulAut Q))) {i : Fin k}
    (hs : w1369_Singleton Λ I i) : ∀ v ∈ I i, f v ∈ I i := by
  classical
  have hc := w1369_s16h_cent_comm hf
  intro v hv
  have hblocks : ∀ j : Fin k, j ≠ i → P.e j (f v) = 1 := by
    intro j hj
    have hbj := w1369_s16h_block_one_or_bij P hstab hsimple hc j i
    rcases hbj with h1 | hbij
    · have h := congrArg (fun g : I i →* I j => (g ⟨v, hv⟩ : Q)) h1
      rw [w1369_s16h_block_coe P f j i ⟨v, hv⟩] at h
      exact h
    · exact absurd (w1369_iso_of_bij_block hstab hc i j hbij) (hs j hj)
  have hprod : ∏ j, P.e j (f v) = P.e i (f v) :=
    Finset.prod_eq_single_of_mem (s := Finset.univ) (f := fun j => P.e j (f v)) i
      (Finset.mem_univ i) (fun j _ hj => hblocks j hj)
  rw [← P.e_prod (f v), hprod]
  exact P.e_mem i (f v)



theorem w1369_isInv_of_stable {A : Subgroup Q} (h : StableUnder Λ A) :
    XMod.IsInv ↥Λ A := by
  intro a x hx
  exact h a a.2 x hx

theorem w1369_iso_refl (i : Fin k) : w1369_Iso Λ I i i := XMod.Iso.refl (I i)

theorem w1369_iso_trans {i j l : Fin k} (h : w1369_Iso Λ I i j)
    (h' : w1369_Iso Λ I j l) : w1369_Iso Λ I i l := XMod.Iso.trans h h'

theorem w1369_iso_symm {i j : Fin k} (hstab : ∀ i, StableUnder Λ (I i))
    (h : w1369_Iso Λ I i j) : w1369_Iso Λ I j i :=
  XMod.Iso.symm (w1369_isInv_of_stable (hstab i)) h

theorem w1369_perfect_trivial_of_simple {Q : Type} [CommGroup Q] [Finite Q]
    (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ X : Subgroup (MulAut Q)} {I : Subgroup Q} (hΛ : StableUnder Λ I)
    (hsimple : I ≠ ⊥ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ I → J = ⊥ ∨ J = I)
    (hX : StableUnder X I) (hXc : X ≤ Subgroup.centralizer (Λ : Set (MulAut Q)))
    (hXp : ⁅X, X⁆ = X) : ∀ x ∈ X, ∀ v ∈ I, x v = v := by
  classical
  haveI : Module (ZMod 2) (Additive ↥I) :=
    CFSG.RankThree.FFModules.moduleOfSq (E := ↥I) (fun e => by
      apply Subtype.ext
      simpa using hQ (e : Q))
  haveI : Module.Finite (ZMod 2) (Additive ↥I) := Module.Finite.of_finite
  have hΛstab : Λ ≤ stabSub I := by
    intro g hg
    rw [mem_stabSub]
    intro u
    exact ⟨fun h => by simpa using hΛ (g⁻¹ : MulAut Q) (Λ.inv_mem hg) (g u) h,
      fun h => hΛ g hg u h⟩
  have hXstab : X ≤ stabSub I := by
    intro g hg
    rw [mem_stabSub]
    intro u
    exact ⟨fun h => by simpa using hX (g⁻¹ : MulAut Q) (X.inv_mem hg) (g u) h,
      fun h => hX g hg u h⟩
  let AΛ : ↥Λ →* MulAut ↥I := (resHom I).comp (Subgroup.inclusion hΛstab)
  let AX : ↥X →* MulAut ↥I := (resHom I).comp (Subgroup.inclusion hXstab)
  let ρ : ↥Λ →* Module.End (ZMod 2) (Additive ↥I) :=
    (CFSG.RankThree.FFModules.autRep ↥I).comp AΛ
  let σ : ↥X →* Module.End (ZMod 2) (Additive ↥I) :=
    (CFSG.RankThree.FFModules.autRep ↥I).comp AX
  have hsimple' : ∀ U : Submodule (ZMod 2) (Additive ↥I),
      (∀ a : ↥Λ, ∀ w ∈ U, (ρ a) w ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    let Ua : AddSubgroup (Additive ↥I) := (AddSubgroup.toZModSubmodule (n := 2)).symm U
    let Js : Subgroup ↥I := AddSubgroup.toSubgroup' Ua
    let Jq : Subgroup Q := Js.map I.subtype
    have hmem : ∀ v : ↥I, v ∈ Js ↔ Additive.ofMul v ∈ U := by
      intro v
      rw [AddSubgroup.mem_toSubgroup']
      rfl
    have hJq : StableUnder Λ Jq := by
      intro l hl x hx
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hx
      have hUj : (AΛ ⟨l, hl⟩) j ∈ Js := by
        apply (hmem _).mpr
        have h1 : (ρ ⟨l, hl⟩) (Additive.ofMul j) ∈ U := hU ⟨l, hl⟩ _ ((hmem j).mp hj)
        rwa [show (ρ ⟨l, hl⟩) (Additive.ofMul j) =
          Additive.ofMul ((AΛ ⟨l, hl⟩) j) from
          CFSG.RankThree.FFModules.autRep_apply _ _] at h1
      refine Subgroup.mem_map.mpr ⟨_, hUj, ?_⟩
      exact CFSG.Quasithin.resHom_apply I _ j
    rcases hsimple.2 Jq hJq (Subgroup.map_subtype_le Js) with hbot | htop
    · left
      have hJs : Js = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro j hj
        have : (j : Q) ∈ Jq := Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
        rw [hbot] at this
        exact Subtype.ext (Subgroup.mem_bot.mp this)
      apply (Submodule.eq_bot_iff U).mpr
      intro w hw
      have hv : w.toMul ∈ Js := (hmem w.toMul).mpr (by simpa using hw)
      rw [hJs] at hv
      have h1 : w.toMul = 1 := Subgroup.mem_bot.mp hv
      change Additive.ofMul w.toMul = 0
      rw [h1]
      rfl
    · right
      apply Submodule.eq_top_iff'.mpr
      intro w
      have hv : w.toMul ∈ Js := by
        have hw' : (w.toMul : Q) ∈ Jq := by
          rw [htop]
          exact w.toMul.2
        obtain ⟨j, hj, hje⟩ := Subgroup.mem_map.mp hw'
        have hjj : j = w.toMul := Subtype.ext hje
        rwa [hjj] at hj
      have h1 := (hmem w.toMul).mp hv
      simpa using h1
  have hcommI : ∀ (g : ↥X) (a : ↥Λ), AX g * AΛ a = AΛ a * AX g := by
    intro g a
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    have h1 : ((AX g * AΛ a) v : Q) = (g : MulAut Q) ((a : MulAut Q) (v : Q)) := rfl
    have h2 : ((AΛ a * AX g) v : Q) = (a : MulAut Q) ((g : MulAut Q) (v : Q)) := rfl
    rw [h1, h2]
    exact w1369_s16h_cent_comm (hXc g.2) a a.2 (v : Q)
  have hcomm : ∀ (g : ↥X) (a : ↥Λ), σ g * ρ a = ρ a * σ g := by
    intro g a
    change (CFSG.RankThree.FFModules.autRep ↥I) (AX g) *
        (CFSG.RankThree.FFModules.autRep ↥I) (AΛ a) =
      (CFSG.RankThree.FFModules.autRep ↥I) (AΛ a) *
        (CFSG.RankThree.FFModules.autRep ↥I) (AX g)
    rw [← map_mul, ← map_mul, hcommI]
  have hΓ : commutator ↥X = ⊤ := by
    haveI : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hXp
    exact Group.IsPerfect.commutator_eq_top
  intro x hx v hv
  have hσ : σ ⟨x, hx⟩ = 1 :=
    CFSG.AGLEmbeddingD2.McLaughlin.eq_one_of_perfect_of_simple ρ σ hsimple' hcomm hΓ ⟨x, hx⟩
  have h := congrArg (fun f : Module.End (ZMod 2) (Additive ↥I) =>
    f (Additive.ofMul (⟨v, hv⟩ : ↥I))) hσ
  rw [Module.End.one_apply] at h
  rw [show σ ⟨x, hx⟩ (Additive.ofMul (⟨v, hv⟩ : ↥I)) =
      Additive.ofMul ((AX ⟨x, hx⟩) (⟨v, hv⟩ : ↥I)) from
      CFSG.RankThree.FFModules.autRep_apply _ _] at h
  have h2 := Additive.ofMul.injective h
  have h4 : ((resHom I) (Subgroup.inclusion hXstab ⟨x, hx⟩) (⟨v, hv⟩ : ↥I) : ↥I) =
      ⟨v, hv⟩ := h2
  have h3 := congrArg (fun u : ↥I => (u : Q)) h4
  rw [CFSG.Quasithin.resHom_apply] at h3
  exact h3

theorem w1369_nonsing_iso (hstab : ∀ i, StableUnder Λ (I i)) (hk : k ≤ 3)
    {i j : Fin k} (hi : ¬ w1369_Singleton Λ I i) (hj : ¬ w1369_Singleton Λ I j) :
    w1369_Iso Λ I i j := by
  by_cases hij : i = j
  · subst hij
    exact w1369_iso_refl i
  · by_cases h : w1369_Iso Λ I i j
    · exact h
    · exfalso
      have hi' : ∃ j, j ≠ i ∧ w1369_Iso Λ I i j := by
        by_contra hcon
        exact hi fun j hj hji => hcon ⟨j, hj, hji⟩
      obtain ⟨i', hi'ne, hii'⟩ := hi'
      have hj' : ∃ j', j' ≠ j ∧ w1369_Iso Λ I j j' := by
        by_contra hcon
        exact hj fun j' hj' hjj' => hcon ⟨j', hj', hjj'⟩
      obtain ⟨j', hj'ne, hjj'⟩ := hj'
      have hii : i ≠ i' := fun h' => hi'ne h'.symm
      have hjj : j ≠ j' := fun h' => hj'ne h'.symm
      have hij' : i ≠ j' := fun h' => h (w1369_iso_symm hstab (h'.symm ▸ hjj'))
      have hi'j : i' ≠ j := fun h' => h (h' ▸ hii')
      have hi'j' : i' ≠ j' := by
        intro h'
        exact h (w1369_iso_trans (h' ▸ hii') (w1369_iso_symm hstab hjj'))
      have hc : ({i, i', j, j'} : Finset (Fin k)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hii, hij, hij']),
          Finset.card_insert_of_notMem (by simp [hi'j, hi'j']),
          Finset.card_insert_of_notMem (by simp [hjj]), Finset.card_singleton]
      have hle : ({i, i', j, j'} : Finset (Fin k)).card ≤ k := by
        simpa using Finset.card_le_univ ({i, i', j, j'} : Finset (Fin k))
      omega


end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
