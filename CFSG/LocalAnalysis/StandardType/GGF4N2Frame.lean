module

public import CFSG.LocalAnalysis.StandardType.GGF4N2Torus
public import CFSG.RankThree.CentralLift.ClassicalCenterTrivial
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.RankThree.Classical2
  Module Multiplicative

section NativeModel

theorem ggN2OrthDerived_model_of_centralImage
    {G : Type} [Group G] {L : Subgroup G}
    (hL : GGCentralImage .POmegaMinus 4 2 L) :
    Nonempty (L ≃* orthDerived (quadMinus 4 (GaloisField 2 2)
      (minusCoeffs 2 2).1 (minusCoeffs 2 2).2)) := by
  classical
  obtain ⟨ψ, -, hker, hrange⟩ := hL
  let F := GaloisField 2 2
  let b : F := (minusCoeffs 2 2).1
  let c : F := (minusCoeffs 2 2).2
  let Q := quadMinus 4 F b c
  let S := spinGroup Q
  have hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0 := minusCoeffs_irr 2 2
  have hZ : Subgroup.center S = ⊥ := PsiDiag.SpinM.center_eq_bot hbc (by norm_num)
  have hker' : ψ.ker = ⊥ := le_antisymm (hker.trans_eq hZ) bot_le
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker'
  let eL : S ≃* L := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let eZ : S ≃* S ⧸ Subgroup.center S :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let eQ : (S ⧸ Subgroup.center S) ≃* StatedProj (StatedOmega (StatedQuadMinus 4 F b c)) :=
    spinQuotientCenterEquivQuadMinus (by norm_num) hbc
  obtain ⟨eO⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadMinus 4 F b c)
  obtain ⟨hQ, -⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (by norm_num : 4 ≤ 4) hbc
  have hSc := OrthRestOdd.scalars_subgroupOf_orthDerived_eq_bot Q hQ
  let eP : ProjOrthDerived Q ≃* orthDerived Q :=
    (QuotientGroup.quotientMulEquivOfEq hSc).trans QuotientGroup.quotientBot
  exact ⟨eL.symm.trans (eZ.trans (eQ.trans (eO.trans eP)))⟩

end NativeModel

@[expose] noncomputable def ggF4N2Bstar_signedAction
    {G : Type} [Group G] {Bs : Subgroup G}
    (κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs) :
    ↥(SpJoin.spSignedGroup 3 5) →* MulAut Bs :=
  (MulAut.congr κ).toMonoidHom.comp
    ((MulAut.prodRightHom (G := Multiplicative (ZMod 5))).comp (ggSpSigned_rho 5 3))

theorem ggF4N2Bstar_signedAction_injective
    {G : Type} [Group G] {Bs : Subgroup G}
    (κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs) :
    Function.Injective (ggF4N2Bstar_signedAction κ) :=
  (MulAut.congr κ).injective.comp
    (MulAut.prodRightHom_injective.comp (ggSpSigned_rho_injective 5 3))

theorem ggF4N2Bstar_signedAction_simple
    {G : Type} [Group G] {Bs : Subgroup G}
    (κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs) (i : Fin 3) :
    ggF4N2Bstar_signedAction κ
        ⟨SpJoin.spReflPerm 3 5 i, SpJoin.spReflPerm_mem_spSignedGroup 3 5 i⟩ =
      MulAut.congr κ (MulAut.prodRightHom (ggSpSigned_spReflAut 5 3 i)) := by
  change MulAut.congr κ (MulAut.prodRightHom (ggSpSigned_rho 5 3 _)) = _
  rw [ggSpSigned_rho_spReflPerm]

theorem ggF4N2Bstar_mem_signedAction_range_of_central
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (χ : Multiplicative (ZMod 5) →* G)
    (hCX : ∀ m, χ m ∈ Subgroup.centralizer (L : Set G))
    (κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs)
    (τ : (Fin 3 → Multiplicative (ZMod 5)) →* L)
    (hτinj : Function.Injective τ) (hτP : τ.range = (Bs ⊓ L).subgroupOf L)
    (hκ : ∀ m f, ((κ (m, f) : Bs) : G) = χ m * (τ f : G))
    (hnorm : ∀ n : L, n ∈ Subgroup.normalizer (((Bs ⊓ L).subgroupOf L : Subgroup L) : Set L) →
      ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 5), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', n * τ f * n⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i))
    {φ : MulAut Bs} (hφA : φ ∈ ggAutomizer L Bs) :
    φ ∈ (ggF4N2Bstar_signedAction κ).range := by
  classical
  obtain ⟨g, hgL, hgN, hφ⟩ := mem_ggAutomizer_iff.mp hφA
  let w : L := ⟨g, hgL⟩
  let P : Subgroup L := (Bs ⊓ L).subgroupOf L
  have hwP : w ∈ Subgroup.normalizer (P : Set L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      change (c : G) ∈ Bs ⊓ L at hc
      change ((w * c * w⁻¹ : L) : G) ∈ Bs ⊓ L
      exact ⟨(Subgroup.mem_normalizer_iff.mp hgN (c : G)).mp hc.1, (w * c * w⁻¹).2⟩
    · intro hc
      change ((w * c * w⁻¹ : L) : G) ∈ Bs ⊓ L at hc
      change (c : G) ∈ Bs ⊓ L
      exact ⟨(Subgroup.mem_normalizer_iff.mp hgN (c : G)).mpr hc.1, c.2⟩
  let eT : (Fin 3 → Multiplicative (ZMod 5)) ≃* P :=
    (MonoidHom.ofInjective hτinj).trans (MulEquiv.subgroupCongr hτP)
  let a : MulAut (Fin 3 → Multiplicative (ZMod 5)) := MulAut.congr eT.symm (ggConjAut P hwP)
  have hconj (f : Fin 3 → Multiplicative (ZMod 5)) : w * τ f * w⁻¹ = τ (a f) := by
    have he : eT (a f) = ggConjAut P hwP (eT f) := by
      change eT (eT.symm (ggConjAut P hwP (eT f))) = _
      exact eT.apply_symm_apply _
    have h := congrArg (fun v : P => (v : L)) he
    change τ (a f) = w * τ f * w⁻¹ at h
    exact h.symm
  obtain ⟨π, ε, hε, hcoords⟩ := hnorm w hwP
  have ha : SpCoord.IsSignedPerm ⇑a :=
    ⟨π, ε, hε, fun f i => hcoords f (a f) (hconj f) i⟩
  obtain ⟨u, hu⟩ := ggSpSigned_isSignedPerm_mem_range (by decide : 1 ≤ 3) ha
  obtain ⟨hwN, he⟩ := ggConjAut_congr_prod_of_conj κ
    χ τ hκ w a
    (fun m => (Subgroup.mem_centralizer_iff.mp (hCX m) g hgL).symm) hconj
  refine ⟨u, ?_⟩
  change MulAut.congr κ (MulAut.prodRightHom (ggSpSigned_rho 5 3 u)) = φ
  rw [hu]
  change MulAut.congr κ (MulEquiv.prodCongr (MulEquiv.refl _) a) = φ
  rw [he]
  apply MulEquiv.ext
  intro b
  exact Subtype.ext ((hφ b).symm)

theorem ggF4N2Bstar_signedAction_range_le_of_central
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (χ : Multiplicative (ZMod 5) →* G)
    (hCX : ∀ m, χ m ∈ Subgroup.centralizer (L : Set G))
    (κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs)
    (τ : (Fin 3 → Multiplicative (ZMod 5)) →* L)
    (hκ : ∀ m f, ((κ (m, f) : Bs) : G) = χ m * (τ f : G))
    (hperm : ∀ σ : Equiv.Perm (Fin 3), ∃ w : L, ∀ f,
      w * τ f * w⁻¹ = τ (SpCoord.permAut σ f))
    (hsgn : ∀ i : Fin 3, ∃ w : L, ∀ f,
      w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f)) :
    (ggF4N2Bstar_signedAction κ).range ≤ ggAutomizer L Bs := by
  let U : Subgroup ↥(SpJoin.spSignedGroup 3 5) :=
    (ggAutomizer L Bs).comap (ggF4N2Bstar_signedAction κ)
  let gen : Fin 3 → ↥(SpJoin.spSignedGroup 3 5) := fun i =>
    ⟨SpJoin.spReflPerm 3 5 i, SpJoin.spReflPerm_mem_spSignedGroup 3 5 i⟩
  have hgen : Subgroup.closure (Set.range gen) = ⊤ :=
    ggSpSigned_closure_range_subtype (fun i => SpJoin.spReflPerm 3 5 i)
      (fun i => SpJoin.spReflPerm_mem_spSignedGroup 3 5 i) rfl
  have hU : (⊤ : Subgroup ↥(SpJoin.spSignedGroup 3 5)) ≤ U := by
    rw [← hgen]
    apply (Subgroup.closure_le U).mpr
    rintro _ ⟨i, rfl⟩
    change ggF4N2Bstar_signedAction κ (gen i) ∈ ggAutomizer L Bs
    rw [ggF4N2Bstar_signedAction_simple]
    by_cases hi : i.val + 1 < 3
    · rw [ggSpSigned_spReflAut, dif_pos hi]
      obtain ⟨w, hw⟩ := hperm (Equiv.swap i ⟨i.val + 1, hi⟩)
      exact Subgroup.subset_closure (ggInduced_congr_prod_of_conj κ χ τ hκ w _
        (fun m => (Subgroup.mem_centralizer_iff.mp (hCX m) w w.2).symm) hw)
    · rw [ggSpSigned_spReflAut, dif_neg hi]
      obtain ⟨w, hw⟩ := hsgn i
      exact Subgroup.subset_closure (ggInduced_congr_prod_of_conj κ χ τ hκ w _
        (fun m => (Subgroup.mem_centralizer_iff.mp (hCX m) w w.2).symm) hw)
  rintro _ ⟨u, rfl⟩
  exact hU (Subgroup.mem_top u)

theorem ggF4N2Bstar_mem_signedAction_range
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (χ : Multiplicative (ZMod 5) ≃* Subgroup.zpowers x)
    (κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs)
    (τ : (Fin 3 → Multiplicative (ZMod 5)) →* L)
    (hτinj : Function.Injective τ) (hτP : τ.range = (Bs ⊓ L).subgroupOf L)
    (hκ : ∀ m f, ((κ (m, f) : Bs) : G) = (χ m : G) * (τ f : G))
    (hnorm : ∀ n : L, n ∈ Subgroup.normalizer (((Bs ⊓ L).subgroupOf L : Subgroup L) : Set L) →
      ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 5), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', n * τ f * n⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i))
    {φ : MulAut Bs} (hφA : φ ∈ ggAutomizer L Bs) :
    φ ∈ (ggF4N2Bstar_signedAction κ).range := by
  obtain ⟨_, _, _, _, _, _, hS, _⟩ := hR.1.1
  have hXC : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) := by
    apply Subgroup.zpowers_le.mpr
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS.2.2.2.1.1 hl)
  exact ggF4N2Bstar_mem_signedAction_range_of_central
    ((Subgroup.zpowers x).subtype.comp χ.toMonoidHom) (fun m => hXC (χ m).2)
    κ τ hτinj hτP hκ hnorm hφA

theorem ggF4N2Bstar_signedAction_range_le
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (χ : Multiplicative (ZMod 5) ≃* Subgroup.zpowers x)
    (κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs)
    (τ : (Fin 3 → Multiplicative (ZMod 5)) →* L)
    (hκ : ∀ m f, ((κ (m, f) : Bs) : G) = (χ m : G) * (τ f : G))
    (hperm : ∀ σ : Equiv.Perm (Fin 3), ∃ w : L, ∀ f,
      w * τ f * w⁻¹ = τ (SpCoord.permAut σ f))
    (hsgn : ∀ i : Fin 3, ∃ w : L, ∀ f,
      w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f)) :
    (ggF4N2Bstar_signedAction κ).range ≤ ggAutomizer L Bs := by
  obtain ⟨_, _, _, _, _, _, hS, _⟩ := hR.1.1
  have hXC : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) := by
    apply Subgroup.zpowers_le.mpr
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS.2.2.2.1.1 hl)
  exact ggF4N2Bstar_signedAction_range_le_of_central
    ((Subgroup.zpowers x).subtype.comp χ.toMonoidHom) (fun m => hXC (χ m).2)
    κ τ hκ hperm hsgn

theorem ggF4N2Bstar_coxeter_of_coordinates
    {G : Type} [Group G] {Bs : Subgroup G} {H : Subgroup (MulAut Bs)}
    (κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs)
    (hFull : (ggF4N2Bstar_signedAction κ).range = H) :
    ∃ e : (CoxeterMatrix.B 3).Group ≃* H, ∀ i,
      (e ((CoxeterMatrix.B 3).simple i) : MulAut Bs) =
        MulAut.congr κ (MulAut.prodRightHom (ggSpSigned_spReflAut 5 3 i)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e₀, he₀⟩ := ggRC_coxeterB_equiv_spSigned (p := 5) (by decide) (by decide : 2 ≤ 3)
  let η : ↥(SpJoin.spSignedGroup 3 5) ≃* H :=
    (MonoidHom.ofInjective (ggF4N2Bstar_signedAction_injective κ)).trans
      (MulEquiv.subgroupCongr hFull)
  let e : (CoxeterMatrix.B 3).Group ≃* H := e₀.trans η
  refine ⟨e, fun i => ?_⟩
  have hi : e₀ ((CoxeterMatrix.B 3).simple i) =
      ⟨SpJoin.spReflPerm 3 5 i, SpJoin.spReflPerm_mem_spSignedGroup 3 5 i⟩ :=
    Subtype.ext (he₀ i)
  change ggF4N2Bstar_signedAction κ (e₀ ((CoxeterMatrix.B 3).simple i)) = _
  rw [hi]
  exact ggF4N2Bstar_signedAction_simple κ i

section OriginalFrame

theorem ggF4N2Bstar_whole_coordinates
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L) :
    ∃ τ : (Fin 3 → Multiplicative (ZMod 5)) →* L,
      Function.Injective τ ∧ τ.range = (Bs ⊓ L).subgroupOf L ∧
      (∃ P : Sylow 5 L, (P : Subgroup L) = τ.range) ∧
      ∃ χ : Multiplicative (ZMod 5) ≃* Subgroup.zpowers x,
        χ (Multiplicative.ofAdd 1) = ⟨x, Subgroup.mem_zpowers x⟩ ∧
      ∃ κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs,
        (κ (Multiplicative.ofAdd 1, 1) : G) = x ∧
        (∀ f, (κ (1, f) : G) = (τ f : G)) ∧
        (∀ m f, (κ (m, f) : G) = (χ m : G) * (τ f : G)) ∧
        (ggF4N2Bstar_signedAction κ).range = ggAutomizer L Bs := by
  classical
  let F := GaloisField 2 2
  let b : F := (minusCoeffs 2 2).1
  let c : F := (minusCoeffs 2 2).2
  have hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0 := minusCoeffs_irr 2 2
  obtain ⟨e⟩ := ggN2OrthDerived_model_of_centralImage hL
  have hF : Nat.card F = 4 := by simpa using GaloisField.card 2 2 (by decide)
  have hV : finrank F (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) = 8 := by simp
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (by norm_num : 4 ≤ 4) hbc
  obtain ⟨τ, hτinj, hτP, hperm, hsgn, hnorm⟩ :=
    ggF4N2Bstar_internal_torus hR hL hF hV hQ hT e
  obtain ⟨χ, hχ, κ, hx, hτ, hκ⟩ :=
    ggF4N2Bstar_coordinates_of_internal_torus hR hL τ hτinj hτP
  obtain ⟨P, hP⟩ := ggF4N2Bstar_inf_L_sylow hR hL
  refine ⟨τ, hτinj, hτP, ⟨P, hP.trans hτP.symm⟩, χ, hχ, κ, hx, hτ, hκ, ?_⟩
  exact le_antisymm (ggF4N2Bstar_signedAction_range_le hR χ κ τ hκ hperm hsgn)
    (fun φ hφ => ggF4N2Bstar_mem_signedAction_range hR χ κ τ hτinj hτP hκ hnorm hφ)

theorem ggF4N2Bstar_B3_frame
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L) :
    ∃ κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs,
      (κ (Multiplicative.ofAdd 1, 1) : G) = x ∧
      ∃ e : (CoxeterMatrix.B 3).Group ≃* ggAutomizer L Bs,
        (∀ i, (e ((CoxeterMatrix.B 3).simple i) : MulAut Bs) =
          MulAut.congr κ (MulAut.prodRightHom (ggSpSigned_spReflAut 5 3 i))) ∧
        GGCoxeterPres 5 (ggAutomizer L Bs) (CoxeterMatrix.B 3) e := by
  obtain ⟨-, -, -, -, -, -, κ, hx, -, -, hFull⟩ := ggF4N2Bstar_whole_coordinates hR hL
  obtain ⟨e, he⟩ := ggF4N2Bstar_coxeter_of_coordinates κ hFull
  have hB : GGIsWeylMatrix (CoxeterMatrix.B 3) :=
    Or.inl ⟨3, Equiv.refl _, by decide, Or.inr (Or.inl ⟨by decide, rfl⟩)⟩
  refine ⟨κ, hx, e, he, hB, fun i => ?_⟩
  rw [he]
  by_cases hi : i.val + 1 < 3
  · rw [ggSpSigned_spReflAut, dif_pos hi]
    have hij : i ≠ (⟨i.val + 1, hi⟩ : Fin 3) := by
      intro heq
      exact (Nat.ne_of_lt (Nat.lt_succ_self i.val)) (congrArg Fin.val heq)
    exact ggF4N2Bstar_swap_reflection κ hij
  · rw [ggSpSigned_spReflAut, dif_neg hi]
    exact ggF4N2Bstar_sgn_reflection κ i

end OriginalFrame

end CFSG.StandardType
