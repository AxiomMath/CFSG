module

public import CFSG.Quasithin.Vol2.Ch4Sec1Defs
public import CFSG.Quasithin.Background.A4

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4

variable {G : Type} [Group G] [Finite G] {T M Mp Mm : Subgroup G}

omit [Finite G] in
theorem isSylowTwoOf_of_le {T H : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) :
    IsSylowTwoOf T H :=
  ⟨hTH, hT.1, fun h => hT.2 (h.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTH))⟩

omit [Finite G] in
theorem mem_sup_of_le_normalizer {H N : Subgroup G} (hH : H ≤ Subgroup.normalizer (N : Set G))
    {x : G} : x ∈ H ⊔ N ↔ ∃ h ∈ H, ∃ n ∈ N, h * n = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right H N hH]
  rfl

omit [Finite G] in
theorem le_normalizer_centralizerSection' {M X : Subgroup G}
    (hX : M ≤ Subgroup.normalizer (X : Set G)) :
    M ≤ Subgroup.normalizer (centralizerSection M X (pCoreOf 2 X) : Set G) :=
  fun _ hm => le_normalizer_centralizerSection M X ⟨hm, hX hm⟩

omit [Finite G] in
theorem map_conj_inf_normalizer {M P : Subgroup G} {c : G} (hc : c ∈ M) :
    (M ⊓ Subgroup.normalizer (P : Set G)).map (MulAut.conj c).toMonoidHom =
      M ⊓ Subgroup.normalizer ((P.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective,
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hc), Subgroup.map_equiv_normalizer_eq]

namespace Hyp4_1_1

variable (h : Hyp4_1_1 G T M Mp)
include h

theorem isSylowTwoOf_T : IsSylowTwoOf T M := isSylowTwoOf_of_le h.sylow h.T_le

theorem le_normalizer_C :
    M ≤ Subgroup.normalizer (centralizerSection M Mp (pCoreOf 2 Mp) : Set G) :=
  le_normalizer_centralizerSection' h.normal

theorem le_normalizer_pCoreOf_Mp : M ≤ Subgroup.normalizer (pCoreOf 2 Mp : Set G) :=
  h.normal.trans (normalizer_le_normalizer_pCoreOf 2 Mp)

theorem subnormal_Mp : IsSubnormal Mp M :=
  subnormal_of_normal h.Mp_le (Subgroup.normal_subgroupOf_of_le_normalizer h.normal)

theorem Mp_eq_oTwoUpper : Mp = oTwoUpper Mp := h.oTwoUpper_eq.symm

theorem isSylowTwoOf_T_inf_C :
    IsSylowTwoOf (T ⊓ centralizerSection M Mp (pCoreOf 2 Mp))
      (centralizerSection M Mp (pCoreOf 2 Mp)) := by
  have hT : IsSylowTwoOf T (M ⊓ Subgroup.normalizer (Mp : Set G)) := by
    rw [inf_eq_left.mpr h.normal]
    exact h.isSylowTwoOf_T
  exact isSylowTwoOf_inf_centralizerSection hT

theorem Mp_le_normalizer {R : Subgroup G}
    (hR : IsSylowTwoOf R (centralizerSection M Mp (pCoreOf 2 Mp))) :
    Mp ≤ Subgroup.normalizer (R : Set G) :=
  (isSignalizer_of_isSylowTwoOf_centralizerSection h.Mp_le hR).2.2

theorem pCoreOf_Mp_le {R : Subgroup G}
    (hR : IsSylowTwoOf R (centralizerSection M Mp (pCoreOf 2 Mp))) : pCoreOf 2 Mp ≤ R :=
  pCoreOf_le_of_isSylowTwoOf_centralizerSection h.Mp_le hR

end Hyp4_1_1

theorem lemma_4_1_2 (h : Hyp4_1_1 G T M Mp) {Rp : Subgroup G}
    (hR : IsSylowTwoOf Rp (centralizerSection M Mp (pCoreOf 2 Mp))) :
    IsUniqueM (M ⊓ Subgroup.normalizer (Rp : Set G)) M := by
  set C := centralizerSection M Mp (pCoreOf 2 Mp) with hCdef
  have hTC := h.isSylowTwoOf_T_inf_C
  have hU : IsUniqueM (M ⊓ Subgroup.normalizer ((T ⊓ C : Subgroup G) : Set G)) M := by
    refine h.unique _ inf_le_left ?_ ?_
    · refine sup_le (le_inf h.Mp_le (h.Mp_le_normalizer hTC)) ?_
      exact le_inf (inf_le_right.trans (centralizerSection_le_left M Mp (pCoreOf 2 Mp)))
        Subgroup.le_normalizer
    · exact sup_inf_normalizer_eq (centralizerSection_le_left M Mp (pCoreOf 2 Mp))
        h.le_normalizer_C hTC
  obtain ⟨c, hc, hcR⟩ := exists_conj_of_isSylowTwoOf hTC hR
  have hRc : Rp = (T ⊓ C).map (MulAut.conj c).toMonoidHom := by
    ext x
    rw [mem_map_conj_iff]
    exact hcR x
  have hcM : c ∈ M := (centralizerSection_le_left M Mp (pCoreOf 2 Mp)) hc
  rw [hRc, ← map_conj_inf_normalizer hcM]
  exact isUniqueM_map_conj hU hcM

theorem lemma_4_1_3_one (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm) {I I₀ I₁ : Subgroup G}
    (hI : IsIota M Mp Mm I) (hII₀ : I ≤ I₀) (hI₀ : I₀ ≤ Mm) (hI₁I₀ : I₁ ≤ I₀)
    (hI₁ : pCoreOf 2 I₁ ≠ ⊥) (hI₀eq : I₁ ⊔ centralizerSection I₀ Mp (pCoreOf 2 Mp) = I₀)
    (hMpI₀ : Mp ⊓ I₀ ≤ I₁ ⊔ pCoreOf 2 Mp) : IsIota M Mp Mm I₁ := by
  set C := centralizerSection M Mp (pCoreOf 2 Mp) with hCdef
  have hCMm : C ≤ Mm := le_sup_right.trans hS.2
  have hI₀M : I₀ ≤ M := hI₀.trans hS.1
  have h0 : I₀ ⊔ C = Mm :=
    le_antisymm (sup_le hI₀ hCMm) (hI.2.1.symm.le.trans (sup_le_sup_right hII₀ C))
  have hC₀ : centralizerSection I₀ Mp (pCoreOf 2 Mp) ≤ C := centralizerSection_mono hI₀M _ _
  have h1 : I₁ ⊔ C = Mm := by
    refine le_antisymm (sup_le (hI₁I₀.trans hI₀) hCMm) ?_
    rw [← h0, ← hI₀eq, sup_assoc]
    exact sup_le_sup_left (sup_le hC₀ le_rfl) I₁
  have hI₀n : I₀ ≤ Subgroup.normalizer (pCoreOf 2 Mp : Set G) :=
    hI₀M.trans h.le_normalizer_pCoreOf_Mp
  have h2 : Mp ≤ I₁ ⊔ pCoreOf 2 Mp := by
    intro m hm
    have hm' : m ∈ I₀ ⊔ pCoreOf 2 Mp := sup_le_sup_right hII₀ _ (hI.2.2.1 hm)
    obtain ⟨i, hi, o, ho, rfl⟩ := (mem_sup_of_le_normalizer hI₀n).mp hm'
    have hiMp : i ∈ Mp := by
      have := Mp.mul_mem hm (Mp.inv_mem (pCoreOf_le 2 Mp ho))
      simpa using this
    exact Subgroup.mul_mem _ (hMpI₀ ⟨hiMp, hi⟩) (Subgroup.mem_sup_right ho)
  exact ⟨hI₁I₀.trans hI₀, h1, h2, hI₁⟩

theorem exists_inH_not_le_of_not_isUniqueM {M I : Subgroup G} (hM : quasithinIsMaxTwoLocal M)
    (hIM : I ≤ M) (hU : ¬ IsUniqueM I M) : ∃ H : Subgroup G, InH I H ∧ ¬ H ≤ M := by
  have : ∃ M', InM I M' ∧ M' ≠ M := by
    by_contra hne
    exact hU ⟨⟨hM, hIM⟩, fun M' hM' => by_contra fun h' => hne ⟨M', hM', h'⟩⟩
  obtain ⟨M', hM', hne⟩ := this
  refine ⟨M', inH_of_inM hM', fun hle => hne ?_⟩
  exact (hM'.1.2 M hM.1 hle).symm

theorem lemma_4_1_3_two (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm) {I I₀ I₁ : Subgroup G}
    (hI : IsGammaStar M Mp Mm I) (hII₀ : I ≤ I₀) (hI₀ : I₀ ≤ Mm) (hI₁I₀ : I₁ ≤ I₀)
    (hI₁ : pCoreOf 2 I₁ ≠ ⊥) (hI₀eq : I₁ ⊔ centralizerSection I₀ Mp (pCoreOf 2 Mp) = I₀)
    (hMpI₀ : Mp ⊓ I₀ ≤ I₁ ⊔ pCoreOf 2 Mp) (hle : OrdLE Mp I I₁)
    (hlt : pCoreOf 2 I < pCoreOf 2 I₁) : IsUniqueM I₁ M := by
  have hι := lemma_4_1_3_one h hS hI.1.1 hII₀ hI₀ hI₁I₀ hI₁ hI₀eq hMpI₀
  by_contra hU
  have hΓ : IsGamma M Mp Mm I₁ :=
    ⟨hι, exists_inH_not_le_of_not_isUniqueM h.maxTwoLocal (hι.1.trans hS.1) hU⟩
  exact hI.2 I₁ hΓ hle hlt

end CFSG.Quasithin.H13.Ch4
