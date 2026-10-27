module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecSB
public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecSt
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXY
public import CFSG.Quasithin.Vol2.Ch12Sec6P31PropAFrame
public import CFSG.Quasithin.Vol2.Ch12Sec6P31PropAStar
public import CFSG.GroupTheory.PCore.OpenTransport

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31Sec

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S126 S126P31
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

section Generic

variable {G : Type} [Group G] [Finite G]

theorem allNS_of_star {H Y : Subgroup G} (hYH : Y ≤ H) {S : Type} [Group S]
    (h : AllNS S ↥(S126.star H Y)) : AllNS S ↥Y := by
  have hsol : Group.IsSolvable ↥(CFSG.pCore 2 ↥H) := by
    haveI := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).isNilpotent
    infer_instance
  have h1 : AllNS S ↥(Y.subgroupOf H) :=
    allNS_of_map_solvable (CFSG.pCore 2 ↥H) hsol (Y.subgroupOf H) h
  exact AllNS.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYH) h1

theorem isQuasisimple_star {H K : Subgroup G} (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K)) :
    CFSG.IsQuasisimple ↥(S126.star H K) := by
  obtain ⟨e⟩ := modO2_mulEquiv hK
  have hq' : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.IsQuasisimple.of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (CFSG.openPCoreOf_subgroupOf 2 K)).symm hq
  exact CFSG.IsQuasisimple.of_mulEquiv e.symm hq'

theorem map_conj_mem_cComp {H L : Subgroup G} (hL : L ∈ cComp H) {t : G} (ht : t ∈ H) :
    L.map (MulAut.conj t).toMonoidHom ∈ cComp H := by
  have h := cComp_map_mulEquiv (MulAut.conj t) hL
  have hH : H.map (MulAut.conj t).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer ht)
  rwa [hH] at h

theorem conjClosure_eq_iSup (K T : Subgroup G) :
    conjClosure K T = ⨆ t : ↥T, K.map (MulAut.conj (t : G)).toMonoidHom := by
  apply le_antisymm
  · refine conjClosure_le fun h hh z hz => ?_
    have hmem : h * z * h⁻¹ ∈ K.map (MulAut.conj h).toMonoidHom :=
      ⟨z, hz, by simp [MulAut.conj_apply]⟩
    exact (le_iSup (fun t : ↥T => K.map (MulAut.conj (t : G)).toMonoidHom) (⟨h, hh⟩ : ↥T)) hmem
  · refine iSup_le fun t => ?_
    rintro _ ⟨z, hz, rfl⟩
    exact Subgroup.subset_closure ⟨(t : G), t.2, z, hz, by simp [MulAut.conj_apply]⟩

theorem allNS_conjClosure {H K T : Subgroup G} (hK : K ∈ cComp H) (hTH : T ≤ H) {S : Type}
    [Group S] (hKS : AllNS S ↥K) : AllNS S ↥(conjClosure K T) := by
  classical
  haveI : Fintype ↥T := Fintype.ofFinite _
  let f : ↥T → Subgroup G := fun t => K.map (MulAut.conj (t : G)).toMonoidHom
  have hsup : conjClosure K T = Finset.univ.sup f := by
    rw [conjClosure_eq_iSup, Finset.sup_univ_eq_iSup]
  have hfc : ∀ t, f t ∈ cComp H := fun t => map_conj_mem_cComp hK (hTH t.2)
  have hle : ∀ t, f t ≤ conjClosure K T := fun t => by
    rw [hsup]
    exact Finset.le_sup (f := f) (Finset.mem_univ t)
  have hnorm : ∀ t, conjClosure K T ≤ Subgroup.normalizer (f t : Set G) := fun t => by
    rw [hsup]
    exact Finset.sup_le fun s _ => le_normalizer_of_mem_cComp (hfc t) (hfc s)
  have hall : ∀ t, AllNS S ↥(f t) := fun t =>
    AllNS.of_mulEquiv (Subgroup.equivMapOfInjective K _ (MulAut.conj (t : G)).injective) hKS
  have := allNS_finset_sup f (conjClosure K T) hle hnorm hall Finset.univ
  rwa [← hsup] at this

end Generic

section Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]
  {H K : Subgroup G}

theorem allNS_of_K0 (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    (hIs : IsHK T L F.V1 H K) (h918 : HypF918 T V L F.V1 F.V5 H K) {S : Type} [Group S]
    (hK0 : AllNS S ↥(conjClosure K T)) : AllNS S ↥H := by
  have hHeq : H = conjClosure K T ⊔ (Li L F.V1 ⊔ T) := hIs.2.2
  have hL1 : Group.IsSolvable ↥(Li L F.V1) := P31A.isSolvable_L1 h1222 F hH
  have hTsol : Group.IsSolvable ↥T := by
    haveI := hH.hyp.sylow.1.isNilpotent
    infer_instance
  have hTn : T ≤ Subgroup.normalizer (Li L F.V1 : Set G) :=
    S126L19b.T_le_normalizer_L1 h1222 hH
  have hY : Group.IsSolvable ↥(Li L F.V1 ⊔ T) := isSolvable_sup_of_normalizes _ _ hTn hL1 hTsol
  have hB : Li L F.V1 ⊔ T ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    h918.L₁T_le_H.trans h918.K₀_normal
  have h := AllNS.sup_of_normalizes (conjClosure K T) (Li L F.V1 ⊔ T) hB hK0
    (haveI := hY; AllNS.of_solvable)
  exact AllNS.of_mulEquiv (MulEquiv.subgroupCongr hHeq.symm) h

end Setting

section E114

theorem lieFam1_w31_of_mulEquiv {m : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : lieFam1_w31 m Y) : lieFam1_w31 m X := by
  unfold lieFam1_w31 at h ⊢
  rcases h with h | h | h | h | h | ⟨hm, ⟨e'⟩⟩ | h | ⟨hm, h⟩
  · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)
  · exact Or.inr (Or.inl (CFSG.SectionRank.suzukiModel_of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, ⟨e.trans e'⟩⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hm,
      CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h⟩))))))

@[expose] def E114Used_w31 : Prop :=
  ∀ (G' : Type) [Group G'] [Finite G'] (T' : Subgroup G'), SQTKGroup G' →
    IsSimpleGroup ↥(CFSG.generalizedFitting G') → IsSylowIn 2 T' ⊤ →
    CFSG.generalizedFitting G' ⊔ T' = ⊤ →
      (∀ n : ℕ, 1 ≤ n → lieFam1_w31 n ↥(CFSG.generalizedFitting G') →
        E1.nParam (⊤ : Subgroup G') = (n : ℕ∞)) ∧
      (IsPSL 4 2 1 ↥(CFSG.generalizedFitting G') ∨ IsPSL 5 2 1 ↥(CFSG.generalizedFitting G') →
        E1.nParam (⊤ : Subgroup G') = 1) ∧
      (IsAlt 7 ↥(CFSG.generalizedFitting G') → E1.nParam (⊤ : Subgroup G') = 1) ∧
      (IsSporadic .M22 ↥(CFSG.generalizedFitting G') → E1.nParam (⊤ : Subgroup G') ≤ 2)

theorem eBound_lie {S : Type} [Group S] (hE : E114Used_w31) {m : ℕ} (hm : 1 ≤ m)
    (hS : lieFam1_w31 m S) : EBound S (m : ℕ∞) :=
  fun G' _ _ T' hsqtk hsimple hsyl hFT ⟨e⟩ =>
    ((hE G' T' hsqtk hsimple hsyl hFT).1 m hm (lieFam1_w31_of_mulEquiv e hS)).le

theorem eBound_one {S : Type} [Group S] (hE : E114Used_w31)
    (hS : IsPSL 4 2 1 S ∨ IsPSL 5 2 1 S ∨ IsAlt 7 S) : EBound S ((1 : ℕ) : ℕ∞) := by
  intro G' _ _ T' hsqtk hsimple hsyl hFT ⟨e⟩
  obtain ⟨-, h45, h7, -⟩ := hE G' T' hsqtk hsimple hsyl hFT
  rw [Nat.cast_one]
  rcases hS with h | h | h
  · exact (h45 (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h))).le
  · exact (h45 (Or.inr (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h))).le
  · obtain ⟨e'⟩ := h
    exact (h7 ⟨e.trans e'⟩).le

theorem eBound_M22 {S : Type} [Group S] (hE : E114Used_w31)
    (hS : IsSporadic .M22 S) : EBound S ((2 : ℕ) : ℕ∞) := by
  intro G' _ _ T' hsqtk hsimple hsyl hFT ⟨e⟩
  obtain ⟨-, -, -, h22⟩ := hE G' T' hsqtk hsimple hsyl hFT
  obtain ⟨e'⟩ := hS
  rw [Nat.cast_ofNat]
  exact h22 ⟨e.trans e'⟩

end E114

section Main

theorem lemmaFBound_w31_of (h1222 : Stmt12_2_2) (hE114 : E114Used_w31)
    (hSec : SimpleSectionSQT)
    (hM22 : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
      ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier .M22, a * b ≠ b * a) :
    LemmaFBound_w31 := by
  intro G _ _ T L V _ F hH hV H K hIs h918
  have h91 := h918.toHypF98.toHypF91
  have hTH : T ≤ H := P31A.T_le_H F hIs
  have hKc : K ∈ cComp H := h918.K_cComp
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hHeq : H = conjClosure K T ⊔ (Li L F.V1 ⊔ T) := hIs.2.2
  have hK0H : conjClosure K T ≤ H := by
    rw [hHeq]
    exact le_sup_left
  have hSQTK : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple hH.hyp.nonabelian (pCoreOf_ne_bot h91)
  have hSQT : CFSG.SectionRank.IsSQTKCat ↥H :=
    ⟨CFSG.SectionRank.isStronglyQuasithin_iff.2 hSQTK.1, hSQTK.2⟩
  have hTG : IsSylowIn 2 T ⊤ :=
    ⟨le_top, hH.hyp.sylow.1, by rw [Subgroup.relIndex_top_right]; exact hH.hyp.sylow.2⟩
  have hTH' : IsSylowIn 2 T H := by
    refine ⟨hTH, hTG.2.1, fun h2 => hTG.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex T H ⊤ hTH le_top
    rw [← this]
    exact Dvd.dvd.mul_right h2 _
  have hTsyl : IsSylowIn 2 (T.subgroupOf H) ⊤ := by
    rw [← E1.isSylowIn_map_of_injective H.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hTH, Subgroup.map_top, Subgroup.range_subtype]
    exact hTH'
  have key : ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 1 ≤ n → EBound S (n : ℕ∞) →
      (∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2) → AllNS S ↥H →
      E1.nParam H ≤ (n : ℕ∞) := by
    intro S _ _ n hn hE hrk hNS
    rw [E1.nParam_subgroupOf H]
    exact nParam_le_of_allNS hn hE hSQTK.2 hrk hNS hTsyl
  have hq : CFSG.IsQuasisimple ↥(S126.star H K) := isQuasisimple_star hKc h918.K_quasisimple
  haveI hsimple : IsSimpleGroup (starMod_w31 H K) := hq.2.1
  have hnab : ∃ a b : starMod_w31 H K, a * b ≠ b * a := hq.2.2
  have hNSK : AllNS (starMod_w31 H K) ↥H :=
    allNS_of_K0 h1222 hH hIs h918
      (allNS_conjClosure hKc hTH
        (allNS_of_star hKH (AllNS.of_quasisimple hq.2.1 (MulEquiv.refl _))))
  have hrkK : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup (starMod_w31 H K)) ≤ 2 := by
    let φ : ↥(K.subgroupOf H) →* starMod_w31 H K :=
      (QuotientGroup.mk' (Subgroup.center ↥(S126.star H K))).comp
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (K.subgroupOf H))
    have hφ : Function.Surjective φ :=
      (QuotientGroup.mk'_surjective _).comp (MonoidHom.subgroupMap_surjective _ _)
    exact CFSG.SectionRank.isStronglyQuasithin_iff.1
      (isStronglyQuasithin_of_simple_image hSec hSQT (K.subgroupOf H) hnab φ hφ)
  refine ⟨?_, ?_, ?_⟩
  · intro m hm hfam
    exact key (starMod_w31 H K) m hm (eBound_lie hE114 hm hfam) hrkK hNSK
  · intro hfam
    have := key (starMod_w31 H K) 1 le_rfl (eBound_one hE114 hfam) hrkK hNSK
    simpa using this
  · intro hK0
    have hstar : ∃ (φ : ↥((conjClosure K T).subgroupOf H) →*
          CFSG.Blueprint.NativeSporadic.Carrier .M22), Function.Surjective φ ∧
        AllNS (CFSG.Blueprint.NativeSporadic.Carrier .M22) ↥(S126.star H (conjClosure K T)) := by
      rcases hK0 with h | ⟨hqK0, -, he⟩
      · obtain ⟨e⟩ := h
        haveI := hM22.1
        haveI : IsSimpleGroup ↥(S126.star H (conjClosure K T)) := e.isSimpleGroup
        exact ⟨e.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap
            ((conjClosure K T).subgroupOf H)),
          e.surjective.comp (MonoidHom.subgroupMap_surjective _ _),
          AllNS.of_simple inferInstance e⟩
      · obtain ⟨e⟩ := he
        exact ⟨e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center
            ↥(S126.star H (conjClosure K T)))).comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap
            ((conjClosure K T).subgroupOf H))),
          e.surjective.comp ((QuotientGroup.mk'_surjective _).comp
            (MonoidHom.subgroupMap_surjective _ _)),
          AllNS.of_quasisimple hqK0.2.1 e⟩
    obtain ⟨φ, hφ, hNS⟩ := hstar
    haveI hfin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) := Finite.of_surjective φ hφ
    haveI := hM22.1
    have hNSH : AllNS (CFSG.Blueprint.NativeSporadic.Carrier .M22) ↥H :=
      allNS_of_K0 h1222 hH hIs h918 (allNS_of_star hK0H hNS)
    have hrk := CFSG.SectionRank.isStronglyQuasithin_iff.1
      (isStronglyQuasithin_of_simple_image hSec hSQT ((conjClosure K T).subgroupOf H) hM22.2 φ hφ)
    have := key (CFSG.Blueprint.NativeSporadic.Carrier .M22) 2 (by norm_num)
      (eBound_M22 hE114 ⟨MulEquiv.refl _⟩) hrk hNSH
    simpa using this

end Main

end CFSG.Quasithin.H13.P31Sec
