module

public import CFSG.LocalAnalysis.StandardType.GGTBJLinearMinusComp
public import CFSG.LocalAnalysis.StandardType.GGTBJLinearMinusWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBJLinearMinusSide
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBShape
public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyStages

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Polynomial Matrix CFSG.RankThree.CALinearPlane
open CoordSL TypeBDatum SpCoord SpJoin Multiplicative

theorem ggTBJ_linMinus_of_frame
    {G : Type} [Group G] [Finite G] {p n m t : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2] {g : F[X]} [Fact (Irreducible g)]
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hpF : p ∣ Nat.card F + 1) (hgd : g ∣ cyclotomic p F)
    (hζ : AdjoinRoot.root g ^ p = 1) (hm : 3 ≤ m)
    (ψ : SpecialLinearGroup (Fin n) F →* G) (A₁ : SpecialLinearGroup (Fin n) F)
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin m) ⊕ Fin t)
    {hC : (rootMat g).det = 1} {hCp : rootMat g ^ p = 1}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hrange : ψ.range = X)
    (hframe : (frameHom ψ A₁ ε hC hCp).range = Bs ⊓ X)
    (hsup : (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) = Bs)
    (hdisj : Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (hJne : J ≠ X) (β : Fin m → ZMod p)
    (hshape : (∃ i j : Fin m, (∀ k, k ≠ i → k ≠ j → β k = 0) ∧
        J = (coordBlockSL F (zeroCoords ε β)).map (SLRep.ggFrame ψ A₁)) ∨
      (∃ (k : Fin m) (c : ZMod p), c ≠ 0 ∧ (∀ i, i ≠ k → β i = c) ∧
        J = (coordBlockSL (AdjoinRoot g) (classSet β c)).map
          ((SLRep.ggFrame ψ A₁).comp (theta g ε)))) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hJX : J ≤ X := by
    rcases hshape with ⟨i, j, hpattern, hJeq⟩ | ⟨k, c, hc, hpattern, hJeq⟩
    · rw [hJeq]
      rintro z ⟨w, hw, rfl⟩
      rw [← hrange, ← SLRep.range_ggFrame ψ A₁]
      exact ⟨w, rfl⟩
    · rw [hJeq]
      rintro z ⟨w, hw, rfl⟩
      rw [← hrange, ← SLRep.range_ggFrame ψ A₁]
      exact ⟨theta g ε w, rfl⟩
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpF
  have hpK : ¬ p ∣ Nat.card F - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpF
  have hpcast : (p : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F 2 p]
    intro h
    rcases (Nat.dvd_prime hp).mp h with hbad | htwo
    · norm_num at hbad
    · exact hp2 htwo.symm
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨Θ, hΘ⟩ := prodEquiv_of_frameHom hBs ψ A₁ ε hC hCp hker
    (rootPB g).dim_pos (isUnit_rootMat_pow_sub hp hpK hpcast hgd)
    hframe hsup hdisj
  let T := frameSigned ψ A₁ ε hC hCp
  have hΘT : ∀ w c, (Θ (w, c) : G) = T w * c := hΘ
  have hTrange : T.range = Bs ⊓ X := by
    let e := (MulEquiv.piMultiplicative fun _ : Fin m => ZMod p).symm
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      rw [← hframe]
      exact ⟨e w, rfl⟩
    · intro hz
      rw [← hframe] at hz
      obtain ⟨w, rfl⟩ := hz
      refine ⟨e.symm w, ?_⟩
      change frameHom ψ A₁ ε hC hCp (e (e.symm w)) = _
      rw [e.apply_symm_apply]
  have hTinj : Function.Injective T := by
    intro w v h
    have h1 : Θ (w, 1) = Θ (v, 1) := Subtype.ext (by simpa [hΘT] using h)
    exact congrArg Prod.fst (Θ.injective h1)
  have hCfix : ∀ z ∈ X, ∀ c : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)),
      z * (c : G) * z⁻¹ = c := by
    intro z hz c
    rw [(Subgroup.mem_centralizer_iff.mp c.2.2 z hz), mul_assoc, mul_inv_cancel, mul_one]
  have hnorm : ∀ z ∈ X, (∀ w, ∃ w', z * T w * z⁻¹ = T w') →
      z ∈ Subgroup.normalizer (Bs : Set G) := by
    intro z hz ha
    have hNT : z ∈ Subgroup.normalizer (T.range : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine Subgroup.eq_of_le_of_card_ge ?_
        (Subgroup.card_map_of_injective (MulAut.conj z).injective).ge
      rintro _ ⟨x, ⟨w, rfl⟩, rfl⟩
      obtain ⟨w', hw'⟩ := ha w
      exact ⟨w', hw'.symm⟩
    have hNC : z ∈ Subgroup.normalizer
        ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_iff.mp hc.2 z hz).symm
    have h := Subgroup.inf_normalizer_le_normalizer_sup T.range
      (Bs ⊓ Subgroup.centralizer (X : Set G)) ⟨hNT, hNC⟩
    rwa [hTrange, hsup] at h
  have hlift : ∀ z (hz : z ∈ X) (hzN : z ∈ Subgroup.normalizer (Bs : Set G))
      (τ : MulAut (Fin m → Multiplicative (ZMod p))),
      (∀ w, z * T w * z⁻¹ = T (τ w)) → ggConjAut Bs hzN = liftBs Θ τ := by
    intro z hz hzN τ ha
    apply eq_liftBs_of_apply Θ
    · intro w
      apply Subtype.ext
      rw [ggConjAut_apply, hΘT, hΘT]
      simpa using ha w
    · intro c
      apply Subtype.ext
      simp only [ggConjAut_apply, hΘT, map_one, one_mul]
      exact hCfix z hz c
  obtain ⟨hupper, hlower⟩ := signed_of_frame hpF hgd hζ ε ψ hker A₁
  have hX : ggAutomizer X Bs = (signedAut m p).map (liftBs Θ) := by
    apply ggAutomizer_eq_map_liftBs T Θ hΘT
    · intro z hz hzN
      have hzE : z ∈ Subgroup.normalizer ((Bs ⊓ X : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hzN, X.le_normalizer hz⟩
      apply hupper z (hrange.symm ▸ hz)
      intro w
      have hw : T w ∈ Bs ⊓ X := hTrange ▸ ⟨w, rfl⟩
      have hzw := (Subgroup.mem_normalizer_iff.mp hzE (T w)).mp hw
      rw [← hTrange] at hzw
      obtain ⟨w', hw'⟩ := hzw
      exact ⟨w', hw'.symm⟩
    · intro i
      obtain ⟨z, hz, ha⟩ := hlower i
      have hzX : z ∈ X := hrange ▸ hz
      exact ⟨z, hzX, hnorm z hzX (fun w => ⟨_, ha w⟩), ha⟩
  have hconj : ∀ (τ : MulAut (Fin m → Multiplicative (ZMod p)))
      (ha : liftBs Θ τ ∈ ggAutomizer J Bs),
      ∃ z ∈ J, ∀ w, z * T w * z⁻¹ = T (τ w) := by
    intro τ ha
    obtain ⟨z, hzJ, hzN, haz⟩ := mem_ggAutomizer_iff.mp ha
    refine ⟨z, hzJ, fun w => ?_⟩
    have h := haz (Θ (w, 1))
    rw [liftBs_apply, hΘT, hΘT] at h
    simpa using h.symm
  have hmem : ∀ z ∈ J, ∀ (τ : MulAut (Fin m → Multiplicative (ZMod p))),
      (∀ w, z * T w * z⁻¹ = T (τ w)) → liftBs Θ τ ∈ ggAutomizer J Bs := by
    intro z hzJ τ ha
    have hzX : z ∈ X := hJX hzJ
    have hzN := hnorm z hzX (fun w => ⟨_, ha w⟩)
    rw [← hlift z hzX hzN τ ha]
    exact ggConjAut_mem_ggAutomizer hzJ hzN
  rcases hshape with ⟨i, j, hsparse, hJeq⟩ | ⟨k, c, hc, hclass, hJeq⟩
  · have hβ : β ≠ 0 := by
      intro hzero
      have hZ : zeroCoords ε β = Finset.univ := by
        subst β
        ext a
        rcases h : ε a with x | y <;> simp [zeroCoords]
      have htop : coordBlockSL F (Finset.univ : Finset (Fin n)) = ⊤ := by
        ext a
        simp [mem_coordBlockSL_iff]
      apply hJne
      simpa [hZ, htop, ← MonoidHom.range_eq_map, SLRep.range_ggFrame, hrange] using hJeq
    let S := Finset.univ.filter fun i => β i = 0
    obtain ⟨hfix, hswap, hneg⟩ := zeroBlock_automizer hpF hζ ε ψ A₁ β
    have hJ : ggAutomizer J Bs = (signedSupportedAut m p S).map (liftBs Θ) := by
      apply le_antisymm
      · intro a ha
        have haX := ggAutomizer_mono Bs hJX ha
        rw [hX] at haX
        obtain ⟨τ, hτ, rfl⟩ := haX
        obtain ⟨z, hz, haT⟩ := hconj τ ha
        refine ⟨τ, mem_signedSupportedAut_of_fix hp hτ S ?_, rfl⟩
        intro i hi
        apply hTinj
        have hcomm := hfix z (hJeq ▸ hz) (Pi.mulSingle i (ofAdd 1)) (by
          intro j hj
          have hij : j ≠ i := by rintro rfl; exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
          simp [hij])
        rw [← haT, hcomm, mul_assoc, mul_inv_cancel, mul_one]
      · apply map_liftBs_signedSupportedAut_le Θ S
        · intro i hi
          obtain ⟨z, hz, ha⟩ := hneg i (Finset.mem_filter.mp hi).2
          exact hmem z (hJeq.symm ▸ hz) (sgnAut i) ha
        · intro i hi j hj hij
          obtain ⟨z, hz, ha⟩ := hswap i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
          exact hmem z (hJeq.symm ▸ hz) (permAut (Equiv.swap i j)) ha
    exact sideDatum_of_zero_pattern hp2 hm hBs Θ hX β hβ ⟨i, j, hsparse⟩ hJ
  · let S := classSet β c
    obtain ⟨hfix, hswap⟩ := classBlock_automizer ε ψ A₁ β c
    have hJ : ggAutomizer J Bs = (permSupportedAut m p S).map (liftBs Θ) := by
      apply le_antisymm
      · intro a ha
        have haX := ggAutomizer_mono Bs hJX ha
        rw [hX] at haX
        obtain ⟨τ, hτ, rfl⟩ := haX
        obtain ⟨z, hz, haT⟩ := hconj τ ha
        refine ⟨τ, mem_permSupportedAut_of_fix hp hτ S ?_ ?_, rfl⟩
        · intro i hi
          apply hTinj
          have hcomm := hfix z (hJeq ▸ hz) (Pi.mulSingle i (ofAdd 1)) (by
            intro j hj l hl
            have hji : j ≠ i := by rintro rfl; exact hi hj
            have hli : l ≠ i := by rintro rfl; exact hi hl
            simp [hji, hli])
          rw [← haT, hcomm, mul_assoc, mul_inv_cancel, mul_one]
        · apply hTinj
          have hcomm := hfix z (hJeq ▸ hz)
            (fun j => if j ∈ S then ofAdd (1 : ZMod p) else 1) (by
              intro j hj l hl
              rw [if_pos hj, if_pos hl])
          rw [← haT, hcomm, mul_assoc, mul_inv_cancel, mul_one]
      · unfold permSupportedAut
        rw [MonoidHom.map_closure, Subgroup.closure_le]
        rintro a ⟨τ, ⟨i, hi, j, hj, hij, rfl⟩, rfl⟩
        obtain ⟨z, hz, ha⟩ := hswap i hi j hj
        exact hmem z (hJeq.symm ▸ hz) (permAut (Equiv.swap i j)) ha
    have hs : ∀ i : Fin m, (1 : ZMod p) * 1 = 1 := fun _ => by simp
    have htwist : twistedPermAut m p S (fun _ => 1) hs = permSupportedAut m p S := by
      have hdiag : diagAut (fun _ : Fin m => (1 : ZMod p)) hs = 1 := by
        ext f i
        simp [diagAut_apply]
      unfold twistedPermAut
      rw [hdiag]
      change (permSupportedAut m p S).map (MonoidHom.id _) = _
      exact Subgroup.map_id _
    have hJtw : ggAutomizer J Bs = (twistedPermAut m p S (fun _ => 1) hs).map (liftBs Θ) := by
      rwa [htwist]
    exact sideDatum_of_class_pattern hp2 hm hBs Θ hX β c ⟨k, hclass⟩ (fun _ => 1) hs hJtw

theorem ggTBJLeft_linMinus_of_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {r f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs L) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  obtain ⟨F, hField, hFinite, hChar, g, hIrr, hC, hCp, m, t, ε, ψ, A₁, β,
    hF, hgd, hζ, hrange, hker, hm, hframe, hdisj, hsup, hshape⟩ :=
    exists_comp_of_linMinus_L hH hpq hmark
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  let : Fact (Irreducible g) := hIrr
  have hpF : p ∣ Nat.card F + 1 := by rwa [hF]
  exact ggTBJ_linMinus_of_frame hH.1.2.1.2.1 hpF hgd hζ hm ψ A₁ ε hker hrange
    hframe hsup hdisj (ggResHyp_J_ne_L hH) β hshape

theorem ggTBJNbr_linMinus_of_marking (hI3 : GGNbrSubcomponentInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {r f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  obtain ⟨F, hField, hFinite, hChar, g, hIrr, hC, hCp, m, t, ε, ψ, A₁, β,
    hF, hgd, hζ, hrange, hker, hm, hframe, hdisj, hsup, hshape⟩ :=
    exists_comp_of_linMinus_K hI3 hH hpq hmark
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  let : Fact (Irreducible g) := hIrr
  have hpF : p ∣ Nat.card F + 1 := by rwa [hF]
  exact ggTBJ_linMinus_of_frame hH.1.2.1.2.1 hpF hgd hζ hm ψ A₁ ε hker hrange
    hframe hsup hdisj (ggResHyp_J_ne_K hH) β hshape

theorem ggTBJLeftOn_linMinus (hRig : GGLabelRigidInput) :
    GGTBJLeftOn ggTBJLinMinusLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hL _hX
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hL
  rcases lab with ⟨tag, r, f⟩
  obtain ⟨ht, _hr, hpq⟩ := hP.1
  dsimp only at ht hpq
  subst tag
  have hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs L :=
    ggInnerDiagOn_relabel hRig hH.2.2.1.1 hΛ hhas
  rcases ggTBJLeft_linMinus_of_marking hH hpq hmark with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJNbrOn_linMinus (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput) :
    GGTBJNbrOn ggTBJLinMinusLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hK _hX
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hK
  rcases lab with ⟨tag, r, f⟩
  obtain ⟨ht, _hr, hpq⟩ := hP.1
  dsimp only at ht hpq
  subst tag
  have hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs K :=
    ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hΛ hhas
  rcases ggTBJNbr_linMinus_of_marking hI3 hH hpq hmark with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end CFSG.StandardType
