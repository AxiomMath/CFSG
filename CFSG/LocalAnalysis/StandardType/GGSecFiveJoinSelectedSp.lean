module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelected
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpSelected
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeOneGFTwo
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSp

public section
namespace CFSG.StandardType
open CFSG CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks


theorem GGPresentsG0.injective_PSp
    {G : Type} [Group G] {G0 : Subgroup G} {n f : ℕ}
    {psi : (ggU .PSp n f).K →* G}
    (hpres : GGPresentsG0 G0 (ggU .PSp n f).D .PSp n f psi) : Function.Injective psi := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcenter : Subgroup.center (ggU .PSp n f).K = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot n
  exact (MonoidHom.ker_eq_bot_iff psi).mp
    (le_antisymm (hpres.2.1.2.trans_eq hcenter) bot_le)

theorem ggActualMember_PSp_block
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ} (psi : (ggU .PSp n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .PSp n f).D .PSp n f psi)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ z : StatedSp n (GaloisField 2 f), Odd (orderOf z) ∧
      ((X = L ∧ psi z = x) ∨ GGNbr p B x D J (psi z) X) ∧
      ∃ ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f),
        IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          (Algebra.adjoin (GaloisField 2 f)
            (Units.val '' ({(z : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
              Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))))) ε ∧
        CFSG.Assembly.IsComponentOf (X.comap psi)
          (glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype
            ({(z : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
              Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) ε) ∧
        (X.comap psi).map psi = X := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : NeZero f := ⟨by have hf : 1 ≤ f := hpres.1.1.2.1; omega⟩
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hinj : Function.Injective psi := hpres.injective_PSp
  have hq : CFSG.Assembly.IsQuasisimple ↥X := isQuasisimple_of_largeEvenMarking hmark
  obtain ⟨z, hodd, hz, hX, hmap⟩ :=
    ggActualMember_injective_model hcfg psi hinj hpres.2.1.1 horigin hq
  obtain ⟨ε, hε, hXε⟩ :=
    ClassicalBlocks.exists_isPrimAdjIdemIn_isComponentOf_glBlockCentralizer_Sp z hodd
      (X.comap psi) hX
  exact ⟨z, hodd, hz, ε, hε, hXε, hmap⟩


section GuardedBlocks


theorem GuardedLargeEvenLabel.false_of_component_iso_unitaryFull
    {H : Type} [Group H] {F C : Subgroup H} {lab : LargeEvenLabel}
    (hg : GuardedLargeEvenLabel lab) (hΛ : LargeEvenInLambda2 lab)
    (hh : GGHasLabel lab (↥C ⧸ Subgroup.center ↥C))
    {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = Q ^ 2) (e : ↥F ≃* ↥(GUFull m Q E))
    (hC : CFSG.Assembly.IsComponentOf C F) : False := by
  obtain ⟨g, _, _, hlabel⟩ := exists_unitary_label_of_isComponentOf_iso_unitaryFull hE e hC
  rcases hlabel with ⟨_, hΛ', hh'⟩ | ⟨_, hΛ', hh'⟩
  · have hi := ggLabelRigidInput_holds lab ⟨.A, 1, g⟩ _ hΛ hΛ' hh hh'
    have hbound := (hg.linear_bounds_of_ggLabelIso hi).1
    omega
  · exact hg.not_ggLabelIso_unitary (m - 1) g
      (ggLabelRigidInput_holds lab ⟨.twA, m - 1, g⟩ _ hΛ hΛ' hh hh')

theorem fixed_sp_block_of_guarded_component
    {n f : ℕ} [NeZero f]
    (b : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) (hb : b ∈ StatedSp n (GaloisField 2 f))
    (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' ({b} :
        Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))))) ε)
    {C : Subgroup (StatedSp n (GaloisField 2 f))}
    (hC : CFSG.Assembly.IsComponentOf C
      (glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype {b} ε))
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hh : GGHasLabel lab (↥C ⧸ Subgroup.center ↥C)) (hg : GuardedLargeEvenLabel lab) :
    (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε = ε := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    Matrix.fromBlocks 0 1 (-1) 0
  have hG : IsUnit G.det := spBlockGram_isUnit_det
  have hGt : Matrix.transpose G = G := spBlockGram_transpose
  have hbG : Matrix.transpose (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) * G * (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) = G := CFSG.Open.StatedAPI.mem_statedSp_iff.mp hb
  have hS : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      ∀ s' ∈ ({b} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))), Commute s s' := by
    intro s hs s' hs'
    have hs0 := Set.mem_singleton_iff.mp hs
    have hs1 := Set.mem_singleton_iff.mp hs'
    subst s; subst s'
    rfl
  have hSU : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      Matrix.transpose (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * G *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = G := by
    intro s hs
    have hs0 := Set.mem_singleton_iff.mp hs
    subst s
    exact hbG
  have hSUmap : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      Matrix.transpose ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) * G *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = G := by
    simpa [Matrix.map_id] using hSU
  obtain ⟨e, he, heε, hcases⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn
    (RingHom.id (GaloisField 2 f)) (fun _ => rfl) hG
    (by simpa [Matrix.map_id] using hGt) hS hSUmap hε
  rcases hcases with heq | ⟨hneε, hneadj, hεstar⟩
  · subst e
    by_contra h1
    obtain ⟨m, Q, E, hEF, hfinE, hcharE, hEcard, ⟨iso⟩⟩ :=
      spBlockGroup_moved_eq_unitary b hb hodd hε he h1
    let : Field E := hEF
    let : Finite E := hfinE
    let : CharP E 2 := hcharE
    exact hg.false_of_component_iso_unitaryFull hΛ hh hEcard iso hC
  · rcases CFSG.StandardType.TableC.isPrimIdemIn_cases hG hGt hS hSU hε he heε with
      heq | ⟨_, e', he', hne, hεe⟩
    · exact (hneε heq).elim
    · obtain ⟨d, m, E, hEF, hfinE, hd, hEcard, _, hdeg, ⟨iso⟩⟩ :=
        blockGroup_iso_Sp_linear b hb hodd hε he he' hne hεe
      let : Field E := hEF
      let : Fintype E := hfinE
      have hKcard : Fintype.card (GaloisField 2 f) = 2 ^ f := by
        rw [← Nat.card_eq_fintype_card]
        exact GaloisField.card 2 f (NeZero.ne f)
      have hEtwo : Fintype.card E = 2 ^ (f * d) := by
        rw [hEcard, hKcard, ← pow_mul]
      let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * d) hEtwo
      obtain ⟨g, _, hcardg, hΛ', hh'⟩ :=
        exists_linear_label_of_isComponentOf_iso_generalLinear iso hC
      have hi := ggLabelRigidInput_holds lab ⟨.A, m - 1, g⟩ _ hΛ hΛ' hh hh'
      have hg1 := (hg.linear_bounds_of_ggLabelIso hi).2
      have hpow : 2 ^ (f * d) = 2 ^ 1 := by
        rw [← hEtwo, ← Nat.card_eq_fintype_card, hcardg, hg1]
      have hfd : f * d = 1 := Nat.pow_right_injective le_rfl hpow
      have hfp : 1 ≤ f := Nat.pos_of_ne_zero (NeZero.ne f)
      have hf1 : f = 1 := by nlinarith
      have hd1 : d = 1 := by simpa [hf1] using hfd
      subst f
      subst d
      have hself := formAdj_eq_self_of_blockDegree_lt_two_gf2 hG hbG he (by omega)
      exact (hneadj hself).elim


theorem ggActualMember_PSp_fixed_block
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ} (psi : (ggU .PSp n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .PSp n f).D .PSp n f psi)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ z : StatedSp n (GaloisField 2 f), Odd (orderOf z) ∧
      ((X = L ∧ psi z = x) ∨ GGNbr p B x D J (psi z) X) ∧
      ∃ ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f),
        IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          (Algebra.adjoin (GaloisField 2 f)
            (Units.val '' ({(z : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
              Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))))) ε ∧
        ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε = ε ∧
        CFSG.Assembly.IsComponentOf (X.comap psi)
          (glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype
            ({(z : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
              Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) ε) ∧
        (X.comap psi).map psi = X := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : NeZero f := ⟨by have hf : 1 ≤ f := hpres.1.1.2.1; omega⟩
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  obtain ⟨z, hodd, hz, ε, hε, hC, hmap⟩ :=
    ggActualMember_PSp_block hcfg psi hpres horigin hmark
  obtain ⟨lab, hΛ, hh, hprop⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨_, _, _, _, _, hg⟩ := hprop
  let ec : ↥(X.comap psi) ≃* ↥X :=
    ((X.comap psi).equivMapOfInjective psi hpres.injective_PSp).trans
      (MulEquiv.subgroupCongr hmap)
  let eQ : ↥(X.comap psi) ⧸ Subgroup.center ↥(X.comap psi) ≃*
      ↥X ⧸ Subgroup.center ↥X := QuotientGroup.congr _ _ ec (Subgroup.map_center_eq (f := ec))
  have hhnative : GGHasLabel lab (↥(X.comap psi) ⧸ Subgroup.center ↥(X.comap psi)) := by
    unfold GGHasLabel at hh ⊢
    refine largeEvenRawDatum_mono ?_ hh
    rintro R _ I F ⟨θ⟩
    exact ⟨eQ.trans θ⟩
  have hodd' : Odd (orderOf (z : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) := by
    simpa using hodd
  have hfixed := fixed_sp_block_of_guarded_component
    (z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) z.2 hodd' hε hC hΛ hhnative hg
  exact ⟨z, hodd, hz, ε, hε, hfixed, hC, hmap⟩


theorem GuardedLargeEvenLabel.isEmpty_altSix
    {X : Type} [Group X] {lab : LargeEvenLabel} (hg : GuardedLargeEvenLabel lab)
    (hM : MarkedModel lab (X ⧸ Subgroup.center X)) :
    IsEmpty (X ≃* alternatingGroup (Fin 6)) := by
  have ht : lab.tag ≠ .B2der := by
    intro h
    simpa [GuardedLargeEvenLabel, h] using hg
  have hne := ggMarkedModel_card_ne_three_sixty ht hM
  refine ⟨fun e => ?_⟩
  let eQ : X ⧸ Subgroup.center X ≃*
      alternatingGroup (Fin 6) ⧸ Subgroup.center (alternatingGroup (Fin 6)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq (f := e))
  let eBot : alternatingGroup (Fin 6) ⧸ Subgroup.center (alternatingGroup (Fin 6)) ≃*
      alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 6)))).trans
      (QuotientGroup.quotientBot)
  apply hne
  rw [Nat.card_congr (eQ.trans eBot).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide


theorem ggActualMember_PSp_explicit_source
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ} (psi : (ggU .PSp n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .PSp n f).D .PSp n f psi)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ (r : ℕ) (ι : (ggU .PSp r f).K →* StatedSp n (GaloisField 2 f))
      (β : Fin (ggU .PSp r f).D.rank → ℤ),
      Function.Injective ι ∧ ι.range = X.comap psi ∧ (X.comap psi).map psi = X ∧
      GGLongRoot (ggU .PSp r f).D β ∧
      ∃ v w : Fin n ⊕ Fin n → GaloisField 2 f,
        v ⬝ᵥ Matrix.mulVec
          (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) w = 1 ∧
        (((ggU .PSp r f).D.rootGroup β).map ι).map (StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0) v) ∧
        (((ggU .PSp r f).D.rootGroup (-β)).map ι).map (StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup w (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0) w) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : NeZero f := ⟨by have hf : 1 ≤ f := hpres.1.1.2.1; omega⟩
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  obtain ⟨z, hodd, hz, ε, hε, hfixed, hC, hmap⟩ :=
    ggActualMember_PSp_fixed_block hcfg psi hpres horigin hmark
  have hprim := isPrimIdemIn_and_blockDegree_eq_one_of_mul_eq_self
    (z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) hε.1 hε.2.1 hε.2.2.1 hfixed
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_markedModel hmark
  obtain ⟨R, _, I, F, _, _, θ, hg, hMR⟩ := largeEvenRawDatum_exists hraw
  have hM : MarkedModel lab (↥X ⧸ Subgroup.center ↥X) := MarkedModel.of_mulEquiv θ.symm hMR
  have hA6X : IsEmpty (↥X ≃* alternatingGroup (Fin 6)) := hg.isEmpty_altSix hM
  let ec : ↥(X.comap psi) ≃* ↥X :=
    ((X.comap psi).equivMapOfInjective psi hpres.injective_PSp).trans (MulEquiv.subgroupCongr hmap)
  have hA6 : IsEmpty (↥(X.comap psi) ≃* alternatingGroup (Fin 6)) :=
    ⟨fun e => hA6X.false (ec.symm.trans e)⟩
  let B0 : Subgroup (StatedSp n (GaloisField 2 f)) :=
    glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype
      ({(z : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
        Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) ε
  let Xn : Subgroup (StatedSp n (GaloisField 2 f)) := X.comap psi
  have hCn : CFSG.Assembly.IsComponentOf Xn B0 := hC
  have hperf : ⁅Xn, Xn⁆ = Xn := by
    have h := Subgroup.map_subtype_commutator Xn
    rw [hCn.2.2.1, Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.symm
  have hle : Xn ≤ ⁅B0, B0⁆ := by
    rw [← hperf]
    exact Subgroup.commutator_mono hCn.1 hCn.1
  have hCDer : CFSG.Assembly.IsComponentOf Xn ⁅B0, B0⁆ :=
    hCn.of_le_of_le hle (Subgroup.commutator_le_self B0)
  have hS : ∀ s ∈ ({(z : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
      Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      ∀ s' ∈ ({(z : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
        Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))), Commute s s' := by
    intro s hs s' hs'
    have hs0 := Set.mem_singleton_iff.mp hs
    have hs1 := Set.mem_singleton_iff.mp hs'
    subst s; subst s'
    rfl
  obtain ⟨r, ι, β, hdim, hβ, hcenter, hrange, v, w, hvw, hv, hw⟩ :=
    exists_blockModel_selfDual_PSp_explicit n f
      ({(z : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
        Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) hS hprim.1 hε.2.2.2.1
        (by omega) hCDer hA6
  have hCtr : Subgroup.center (ggU .PSp r f).K = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot r
  have hi : Function.Injective ι := by
    apply (MonoidHom.ker_eq_bot_iff ι).mp
    refine le_antisymm ?_ bot_le
    intro g hg
    have hc := hcenter g (by rw [MonoidHom.mem_ker.mp hg]; exact Subgroup.one_mem _)
    simpa [hCtr] using hc
  exact ⟨r, ι, β, hi, hrange, hmap, hβ, v, w, hvw, hv, hw⟩

end GuardedBlocks

end CFSG.StandardType
end
