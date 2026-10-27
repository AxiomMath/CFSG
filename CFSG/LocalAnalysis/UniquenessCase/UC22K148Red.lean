module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdSmall
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

@[expose] def K148Concl (ρ : Representation (ZMod 2) G V) : Prop :=
  ∃ (m : ℕ) (Hs : Fin m → Subgroup G),
    IsInternalDirect (hP ρ) Hs ∧
    IsDirectSumMod (uP ρ) (cUP ρ) (fun i => commOn ρ (Hs i) (uP ρ)) ∧
    ∀ i, Shape148 ρ (Hs i) (commOn ρ (Hs i) (uP ρ)) (cUP ρ)

@[expose] def K148Top : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V), CFSG.IsKGroup G → CFSG.pCore 2 G = ⊥ → Function.Injective ρ →
    (∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2)))) →
    hP ρ = ⊤ → hP ρ ≠ ⊥ → K148Concl ρ

theorem fixSub_comp_subtype (K : Subgroup G) (X : Subgroup ↥K) :
    fixSub (ρ.comp K.subtype) X = fixSub ρ (X.map K.subtype) := by
  ext w
  simp only [mem_fixSub, Subgroup.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, MonoidHom.comp_apply, Subgroup.coe_subtype]

theorem commOn_comp_subtype (K : Subgroup G) (X : Subgroup ↥K) (U : Submodule (ZMod 2) V) :
    commOn (ρ.comp K.subtype) X U = commOn ρ (X.map K.subtype) U := by
  rw [commOn, commOn]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Subgroup.mem_map, exists_exists_and_eq_and, MonoidHom.comp_apply,
    Subgroup.coe_subtype]

theorem isInvariant_comp_subtype_iff (K : Subgroup G) (X : Subgroup ↥K)
    (U : Submodule (ZMod 2) V) :
    CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (ρ.comp K.subtype) X U ↔ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (X.map K.subtype) U := by
  simp only [CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant, Subgroup.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, MonoidHom.comp_apply,
    Subgroup.coe_subtype]

namespace RedAux

theorem isBestOffender_comp_subtype_iff (K : Subgroup G) (A : Subgroup ↥K) :
    IsBestOffender (ρ.comp K.subtype) A ↔ IsBestOffender ρ (A.map K.subtype) := by
  have hc : ∀ B : Subgroup ↥K, Nat.card ↥(B.map K.subtype) = Nat.card ↥B := fun B =>
    Subgroup.card_map_of_injective K.subtype_injective
  constructor
  · intro h B hB
    have hBK : B ≤ K.subtype.range := by
      rw [Subgroup.range_subtype]
      exact hB.trans (Subgroup.map_subtype_le A)
    obtain ⟨B, rfl⟩ : ∃ B' : Subgroup ↥K, B'.map K.subtype = B :=
      ⟨_, Subgroup.map_comap_eq_self hBK⟩
    have := h B ((Subgroup.map_le_map_iff_of_injective K.subtype_injective).1 hB)
    rwa [fixSub_comp_subtype, fixSub_comp_subtype, ← hc B, ← hc A] at this
  · intro h B hB
    have := h (B.map K.subtype) (Subgroup.map_mono hB)
    rwa [← fixSub_comp_subtype, ← fixSub_comp_subtype, hc, hc] at this

end RedAux

theorem mem_calP_comp_subtype_iff (K : Subgroup G) (A : Subgroup ↥K) :
    A ∈ calP (ρ.comp K.subtype) ↔ A.map K.subtype ∈ calP ρ := by
  have e := A.equivMapOfInjective K.subtype K.subtype_injective
  simp only [mem_calP_iff, IsElemBestOffender, ne_eq,
    Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective,
    RedAux.isBestOffender_comp_subtype_iff]
  exact and_congr_right fun _ => and_congr_left fun _ =>
    ⟨CFSG.IsElementaryAbelian.of_mulEquiv e, CFSG.IsElementaryAbelian.of_mulEquiv e.symm⟩

theorem map_hP_comp_subtype {K : Subgroup G} (hK : hP ρ ≤ K) :
    (hP (ρ.comp K.subtype)).map K.subtype = hP ρ := by
  refine le_antisymm ?_ (iSup₂_le fun B hB => ?_)
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_hP_of_mem_calP ((mem_calP_comp_subtype_iff K A).1 hA)
  · have hBK : B ≤ K.subtype.range := by
      rw [Subgroup.range_subtype]
      exact (le_hP_of_mem_calP hB).trans hK
    rw [← Subgroup.map_comap_eq_self hBK] at hB ⊢
    exact Subgroup.map_mono (le_hP_of_mem_calP ((mem_calP_comp_subtype_iff K _).2 hB))

theorem uP_comp_subtype {K : Subgroup G} (hK : hP ρ ≤ K) : uP (ρ.comp K.subtype) = uP ρ := by
  rw [uP, uP, commOn_comp_subtype, map_hP_comp_subtype hK]

theorem cUP_comp_subtype {K : Subgroup G} (hK : hP ρ ≤ K) : cUP (ρ.comp K.subtype) = cUP ρ := by
  rw [cUP, cUP, uP_comp_subtype hK, fixSub_comp_subtype, map_hP_comp_subtype hK]

theorem secNat_comp_subtype_iff {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (K : Subgroup G) (H₁ : Subgroup ↥K) (A B : Submodule (ZMod 2) V) (H' : Subgroup (GL ι F)) :
    SecNat (ρ.comp K.subtype) H₁ A B H' ↔ SecNat ρ (H₁.map K.subtype) A B H' := by
  simp only [SecNat, isInvariant_comp_subtype_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨φ, ψ, h0, h1, h2, h3⟩
    refine ⟨(H₁.equivMapOfInjective _ K.subtype_injective).symm.trans φ, ψ, h0, h1, h2,
      fun h' x hx => ?_⟩
    obtain ⟨h, rfl⟩ := (H₁.equivMapOfInjective _ K.subtype_injective).surjective h'
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact h3 h x hx
  · rintro ⟨φ, ψ, h0, h1, h2, h3⟩
    exact ⟨(H₁.equivMapOfInjective _ K.subtype_injective).trans φ, ψ, h0, h1, h2,
      fun h x hx => h3 ((H₁.equivMapOfInjective _ K.subtype_injective) h) x hx⟩

theorem natL2_comp_subtype_iff (K : Subgroup G) (H₁ : Subgroup ↥K) (A B : Submodule (ZMod 2) V)
    (n : ℕ) : NatL2 (ρ.comp K.subtype) H₁ A B n ↔ NatL2 ρ (H₁.map K.subtype) A B n := by
  simp only [NatL2, secNat_comp_subtype_iff]

theorem natL3_comp_subtype_iff (K : Subgroup G) (H₁ : Subgroup ↥K) (A B : Submodule (ZMod 2) V) :
    NatL3 (ρ.comp K.subtype) H₁ A B ↔ NatL3 ρ (H₁.map K.subtype) A B :=
  secNat_comp_subtype_iff K H₁ A B _

theorem secNatS5_comp_subtype_iff (K : Subgroup G) (H₁ : Subgroup ↥K)
    (A B : Submodule (ZMod 2) V) :
    SecNatS5 (ρ.comp K.subtype) H₁ A B ↔ SecNatS5 ρ (H₁.map K.subtype) A B := by
  simp only [SecNatS5, isInvariant_comp_subtype_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨φ, ψ, h0, h1, h2, h3, h4⟩
    refine ⟨(H₁.equivMapOfInjective _ K.subtype_injective).symm.trans φ, ψ, h0, h1, h2, h3,
      fun h' x hx => ?_⟩
    obtain ⟨h, rfl⟩ := (H₁.equivMapOfInjective _ K.subtype_injective).surjective h'
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact h4 h x hx
  · rintro ⟨φ, ψ, h0, h1, h2, h3, h4⟩
    exact ⟨(H₁.equivMapOfInjective _ K.subtype_injective).trans φ, ψ, h0, h1, h2, h3,
      fun h x hx => h4 ((H₁.equivMapOfInjective _ K.subtype_injective) h) x hx⟩

theorem shape148_comp_subtype_iff (K : Subgroup G) (Hi : Subgroup ↥K) (U C : Submodule (ZMod 2) V) :
    Shape148 (ρ.comp K.subtype) Hi U C ↔ Shape148 ρ (Hi.map K.subtype) U C := by
  simp only [Shape148, natL2_comp_subtype_iff, natL3_comp_subtype_iff, secNatS5_comp_subtype_iff]

theorem isInternalDirect_map_subtype_iff {m : ℕ} (K : Subgroup G) (H : Subgroup ↥K)
    (Hs : Fin m → Subgroup ↥K) :
    IsInternalDirect H Hs ↔ IsInternalDirect (H.map K.subtype) (fun i => (Hs i).map K.subtype) := by
  have hf := K.subtype_injective
  have hsup : ∀ i, (⨆ j ∈ {j | j ≠ i}, Hs j).map K.subtype =
      ⨆ j ∈ {j | j ≠ i}, (Hs j).map K.subtype := fun i => by
    simp only [Subgroup.map_iSup]
  refine and_congr ?_ (and_congr ?_ (forall_congr' fun i => ?_))
  · rw [← Subgroup.map_iSup]
    exact (Subgroup.map_injective hf).eq_iff.symm
  · simp only [Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      ← map_mul, hf.eq_iff]
  · rw [← hsup, ← Subgroup.map_inf_eq _ _ _ hf, Subgroup.map_eq_bot_iff_of_injective _ hf]

theorem hP_normal : (hP ρ).Normal := by
  rw [hP_eq_bestOffenderSub]
  exact bestOffenderSub_normal ρ

theorem hP_comp_subtype_eq_top : hP (ρ.comp (hP ρ).subtype) = ⊤ := by
  apply Subgroup.map_injective (hP ρ).subtype_injective
  rw [map_hP_comp_subtype le_rfl, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem injective_comp_subtype (hρ : Function.Injective ρ) (K : Subgroup G) :
    Function.Injective (ρ.comp K.subtype) :=
  hρ.comp K.subtype_injective

theorem pCore_subgroup_eq_bot [Finite G] (hO : CFSG.pCore 2 G = ⊥) {K : Subgroup G}
    (hK : K.Normal) : CFSG.pCore 2 ↥K = ⊥ := by
  have h := CFSG.ABGLocalTools.map_pCore_le_of_injective_of_normal (p := 2) K.subtype
    K.subtype_injective (by rw [Subgroup.range_subtype]; exact hK)
  rw [hO, le_bot_iff] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h

theorem isComponentOf_map_subtype {K : Subgroup G} (hK : K.Normal) {L : Subgroup ↥K}
    (hL : IsComponentOf L ⊤) : IsComponentOf (L.map K.subtype) ⊤ := by
  have hLK : CFSG.Open.IsSubnormal (L.map K.subtype) K := by
    have h := hL.2.1.map K.subtype
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact ⟨le_top, hLK.trans (.step le_top (hK.subgroupOf ⊤) (.refl ⊤)),
    (CFSG.Open.IsQuasisimple.congr (L.equivMapOfInjective _ K.subtype_injective)).1 hL.2.2⟩

namespace RedAux

theorem allowedShape_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : (∃ n : ℕ, 2 ≤ n ∧ IsL2 Y n) ∨ (IsL2Odd Y 7 ∧ Nonempty (Y ≃* GL (Fin 3) (ZMod 2)))) :
    (∃ n : ℕ, 2 ≤ n ∧ IsL2 X n) ∨ (IsL2Odd X 7 ∧ Nonempty (X ≃* GL (Fin 3) (ZMod 2))) := by
  rcases h with ⟨n, hn, h⟩ | ⟨h, ⟨f⟩⟩
  · exact Or.inl ⟨n, hn, CFSG.Blueprint.LieModel.of_mulEquiv e.symm h⟩
  · exact Or.inr ⟨CFSG.Blueprint.LieModel.of_mulEquiv e.symm h, ⟨e.trans f⟩⟩

theorem commutator_ne_bot_of_le {L M : Subgroup G} (hL : IsComponentOf L ⊤) (hLM : L ≤ M) :
    ⁅L, M⁆ ≠ ⊥ := by
  haveI : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  haveI := hL.2.2.2
  haveI : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  intro h
  have hle : L ≤ ⁅L, M⁆ :=
    Subgroup.commutator_eq_self.symm.le.trans (Subgroup.commutator_mono le_rfl hLM)
  rw [h] at hle
  exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance (le_bot_iff.1 hle)

end RedAux

theorem allowed_shape_comp_subtype
    [Finite G] [Finite V] (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ → CompShape148 L) {L : Subgroup ↥(hP ρ)}
    (hL : IsComponentOf L ⊤) :
    (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))) := by
  have hL' := isComponentOf_map_subtype hP_normal hL
  exact RedAux.allowedShape_of_mulEquiv (L.equivMapOfInjective _ (hP ρ).subtype_injective)
    (allowed_shape hρ hL' (hshape _ hL')
      (RedAux.commutator_ne_bot_of_le hL' (Subgroup.map_subtype_le L)))

theorem allowed_shape_of_normal {K : Subgroup G} (hK : K.Normal)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    {L : Subgroup ↥K} (hL : IsComponentOf L ⊤) :
    (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))) :=
  RedAux.allowedShape_of_mulEquiv (L.equivMapOfInjective _ K.subtype_injective)
    (hshape _ (isComponentOf_map_subtype hK hL))

theorem k148Concl_of_comp_subtype {K : Subgroup G} (hK : hP ρ ≤ K)
    (h : K148Concl (ρ.comp K.subtype)) : K148Concl ρ := by
  obtain ⟨m, Hs, hdir, hsum, hshape⟩ := h
  refine ⟨m, fun i => (Hs i).map K.subtype, ?_, ?_, fun i => ?_⟩
  · rw [← map_hP_comp_subtype hK]
    exact (isInternalDirect_map_subtype_iff K _ Hs).1 hdir
  · rw [uP_comp_subtype hK, cUP_comp_subtype hK] at hsum
    simpa only [commOn_comp_subtype] using hsum
  · have := hshape i
    rwa [uP_comp_subtype hK, cUP_comp_subtype hK, commOn_comp_subtype,
      shape148_comp_subtype_iff] at this

theorem k148Concl_of_top [Finite G] [Finite V] (hK : CFSG.IsKGroup G) (hO : CFSG.pCore 2 G = ⊥)
    (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup ↥(hP ρ), IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hne : hP ρ ≠ ⊥)
    (h : ∀ (G' : Type) [Group G'] [Finite G'] (ρ' : Representation (ZMod 2) G' V),
      Nat.card G' ≤ Nat.card G → CFSG.IsKGroup G' → CFSG.pCore 2 G' = ⊥ → Function.Injective ρ' →
      (∀ L : Subgroup G', IsComponentOf L ⊤ →
        (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2)))) →
      hP ρ' = ⊤ → hP ρ' ≠ ⊥ → K148Concl ρ') :
    K148Concl ρ := by
  refine k148Concl_of_comp_subtype le_rfl (h ↥(hP ρ) (ρ.comp (hP ρ).subtype)
    (hP ρ).card_le_card_group (hK.subgroup _) (pCore_subgroup_eq_bot hO hP_normal)
    (injective_comp_subtype hρ _) hshape hP_comp_subtype_eq_top fun h0 => hne ?_)
  rw [← map_hP_comp_subtype (le_refl (hP ρ)), h0, Subgroup.map_bot]

theorem k148_of_top
    (h : K148Top) : UC22.Ext.K148 := by
  intro G _ _ V _ _ _ ρ hK hO hρ hshape hne
  exact k148Concl_of_top hK hO hρ (fun L hL => allowed_shape_comp_subtype hρ hshape hL) hne
    fun G' _ _ ρ' _ => h G' V ρ'

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
