module

public import CFSG.Quasithin.Vol2.Ch3xLem317
public import CFSG.Quasithin.Background.A4Local

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.A4

namespace Ch3n

variable {G : Type} [Group G]

theorem conj_inf_le {T R D B : Subgroup G} (hBD : B ≤ Subgroup.normalizer (D : Set G))
    (hTD : T ⊓ D ≤ R) (hRD : R ≤ D) {y : G} (hy : y ∈ B) : B6.conjSub y R ⊓ T ≤ R := by
  intro x hx
  have hxR : y⁻¹ * x * y ∈ R := B6.mem_conjSub.mp hx.1
  have hyD : y ∈ Subgroup.normalizer (D : Set G) := hBD hy
  have hxD : x ∈ D := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hyD (y⁻¹ * x * y)).mp (hRD hxR)
    simpa [mul_assoc] using h1
  exact hTD ⟨hx.2, hxD⟩

@[expose] def genBy (T K R B : Subgroup G) : Subgroup G :=
  ⨆ y ∈ B ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G), B6.conjSub y R ⊓ T

theorem inf_le_genBy {T K R B : Subgroup G} : R ⊓ T ≤ genBy T K R B := by
  refine le_trans ?_ (le_iSup₂_of_le (1 : G) ⟨B.one_mem, Subgroup.one_mem _⟩ le_rfl)
  intro x hx
  exact ⟨by simpa [B6.mem_conjSub] using hx.1, hx.2⟩

theorem inf_le_of_genBy {T K R D B : Subgroup G} (hBD : B ≤ Subgroup.normalizer (D : Set G))
    (hTD : T ⊓ D ≤ R) (hRD : R ≤ D) (hgen : T ⊓ K ≤ genBy T K R B) : T ⊓ K ≤ R := by
  refine hgen.trans (iSup₂_le fun y hy => ?_)
  exact conj_inf_le hBD hTD hRD hy.1

section Finite

variable [Finite G]

theorem isSylowTwoOf_sup_of_inf_le {T R K H : Subgroup G} (hT : IsSylowTwoOf T H) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hRT : R ≤ T) (hTK : T ⊓ K ≤ R) :
    IsSylowTwoOf R (K ⊔ R) := by
  have h1 : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hT hKH hHK
  have h2 : T ⊓ K = R ⊓ K := le_antisymm (le_inf hTK inf_le_right) (inf_le_inf_right K hRT)
  rw [h2] at h1
  refine isSylowTwoOf_sup_of_le (K := K) (S := R ⊓ K) (R := R) (H := H) hHK inf_le_left
    (hRT.trans hT.1) (hT.2.1.to_le hRT) ?_
  rwa [sup_eq_left.mpr inf_le_right]

theorem sylow_of_genBy {T R D B H : Subgroup G} (hT : IsSylowTwoOf T H)
    (hBD : B ≤ Subgroup.normalizer (D : Set G)) (hTD : T ⊓ D ≤ R) (hRD : R ≤ D) (hRT : R ≤ T)
    (hgen : T ⊓ twoResidual H ≤ genBy T (twoResidual H) R B) :
    IsSylowTwoOf R (oTwoUpper H ⊔ R) := by
  rw [← F6.twoResidual_eq_oTwoUpper]
  exact isSylowTwoOf_sup_of_inf_le hT (twoResidual_le H) (le_normalizer_twoResidual H) hRT
    (inf_le_of_genBy hBD hTD hRD hgen)

variable {T M M₀ H V : Subgroup G}

theorem exists_normal_D_caseII (h : Hyp315Base T M M₀ H V) (hII : Hyp315.CaseII M H V) :
    ∃ D : Subgroup G, H ⊓ M ≤ Subgroup.normalizer (D : Set G) ∧ T ⊓ D ≤ pCoreOf 2 M₀ ∧
      pCoreOf 2 M₀ ≤ D := by
  have hTB : T ≤ H ⊓ M := le_inf h.hStar.1.1 h.T_le_M
  refine ⟨(H ⊓ M) ⊓ Subgroup.centralizer (V : Set G), ?_, ?_, ?_⟩
  · intro b hb
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    refine ⟨(H ⊓ M).mul_mem ((H ⊓ M).mul_mem hb hx.1) ((H ⊓ M).inv_mem hb), ?_⟩
    show b * x * b⁻¹ ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : b⁻¹ * v * b ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hII ((H ⊓ M).inv_mem hb)) v).mp hv
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hv'
    calc v * (b * x * b⁻¹) = b * ((b⁻¹ * v * b) * x) * b⁻¹ := by group
      _ = b * (x * (b⁻¹ * v * b)) * b⁻¹ := by rw [hc]
      _ = (b * x * b⁻¹) * v := by group
  · rintro x ⟨hxT, hxD⟩
    rw [h.centralizer]
    exact ⟨hxT, hxD.2⟩
  · rw [h.centralizer]
    exact le_inf (inf_le_left.trans hTB) inf_le_right

theorem exists_normal_D_caseI (hT : quasithinIsSylowTwo T) (h : Hyp315Base T M M₀ H V)
    (hI : Hyp315.CaseI M M₀ H) :
    ∃ D : Subgroup G, H ⊓ M ≤ Subgroup.normalizer (D : Set G) ∧ T ⊓ D ≤ pCoreOf 2 M₀ ∧
      pCoreOf 2 M₀ ≤ D := by
  set L := oTwoUpper M₀ with hL
  have hTB : T ≤ H ⊓ M := le_inf h.hStar.1.1 h.T_le_M
  have hLM₀ : L ≤ M₀ := oTwoUpper_le M₀
  have hLfix : L = oTwoUpper L := (A4.oTwoUpper_oTwoUpper M₀).symm
  have hMN : M₀ ≤ Subgroup.normalizer (L : Set G) := le_normalizer_oTwoUpper M₀
  have hsub : IsSubnormal L M₀ :=
    A4.subnormal_of_normal hLM₀ (Subgroup.normal_subgroupOf_of_le_normalizer hMN)
  have hTsyl : IsSylowTwoOf T M₀ := isSylowTwoOf_of_isSylowTwo hT h.T_le
  have hTsyl' : IsSylowTwoOf T (M₀ ⊓ Subgroup.normalizer (L : Set G)) := by
    rwa [inf_eq_left.mpr hMN]
  have hRsyl : IsSylowTwoOf (pCoreOf 2 M₀) (centralizerSection M₀ L (pCoreOf 2 L)) := by
    have h5 := a4_2_5 hLfix hsub hTsyl'
    have hsup : L ⊔ T = M₀ := B6.sup_eq_of_isTwoQuotient hLM₀ hMN
      (fun d hd => exists_pow_mem_oTwoUpper M₀ hd) hTsyl
    rw [hsup] at h5
    exact (a4_2_4 hLfix hsub _).mp h5
  have hRT : pCoreOf 2 M₀ ≤ T := h.pCoreOf_le_T
  refine ⟨centralizerSection (H ⊓ M) L (pCoreOf 2 L), ?_, ?_, ?_⟩
  · intro b hb
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := hI hb
    have hbN2 : b ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 L hbN
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨hxB, hxN, hxN2, hxc⟩ := mem_centralizerSection.mp hx
    refine mem_centralizerSection.mpr ⟨(H ⊓ M).mul_mem ((H ⊓ M).mul_mem hb hxB) ((H ⊓ M).inv_mem hb),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hbN hxN) (Subgroup.inv_mem _ hbN),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hbN2 hxN2) (Subgroup.inv_mem _ hbN2), fun l hl => ?_⟩
    have hl' : b⁻¹ * l * b ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) l).mp hl
      simpa using this
    have h1 := hxc _ hl'
    have h2 := (Subgroup.mem_normalizer_iff.mp hbN2 _).mp h1
    have e : b * ((b⁻¹ * l * b) * x * (b⁻¹ * l * b)⁻¹ * x⁻¹) * b⁻¹ =
        l * (b * x * b⁻¹) * l⁻¹ * (b * x * b⁻¹)⁻¹ := by group
    rwa [e] at h2
  · rintro x ⟨hxT, hxD⟩
    obtain ⟨hxB, hxN, hxN2, hxc⟩ := mem_centralizerSection.mp hxD
    have hxC : x ∈ centralizerSection M₀ L (pCoreOf 2 L) :=
      mem_centralizerSection.mpr ⟨h.T_le hxT, hxN, hxN2, hxc⟩
    have hRP : pCoreOf 2 M₀ ≤ T ⊓ centralizerSection (H ⊓ M) L (pCoreOf 2 L) := by
      refine le_inf hRT fun r hr => ?_
      obtain ⟨-, hrN, hrN2, hrc⟩ := mem_centralizerSection.mp (hRsyl.1 hr)
      exact mem_centralizerSection.mpr ⟨hTB (hRT hr), hrN, hrN2, hrc⟩
    have hPC : T ⊓ centralizerSection (H ⊓ M) L (pCoreOf 2 L) ≤
        centralizerSection M₀ L (pCoreOf 2 L) := by
      intro y hy
      obtain ⟨-, hyN, hyN2, hyc⟩ := mem_centralizerSection.mp hy.2
      exact mem_centralizerSection.mpr ⟨h.T_le hy.1, hyN, hyN2, hyc⟩
    have hmax := (isSylowTwoOf_iff_maximal.mp hRsyl).2.2
      (T ⊓ centralizerSection (H ⊓ M) L (pCoreOf 2 L)) hPC
      (hTsyl.2.1.to_le inf_le_left) hRP
    exact hmax ⟨hxT, hxD⟩
  · intro r hr
    obtain ⟨-, hrN, hrN2, hrc⟩ := mem_centralizerSection.mp (hRsyl.1 hr)
    exact mem_centralizerSection.mpr ⟨hTB (hRT hr), hrN, hrN2, hrc⟩

theorem exists_normal_D (hT : quasithinIsSylowTwo T) (h : Hyp315 T M M₀ H V) :
    ∃ D : Subgroup G, H ⊓ M ≤ Subgroup.normalizer (D : Set G) ∧ T ⊓ D ≤ pCoreOf 2 M₀ ∧
      pCoreOf 2 M₀ ≤ D := by
  rcases h.case with hI | hII
  · exact exists_normal_D_caseI hT h.toHyp315Base hI
  · exact exists_normal_D_caseII h.toHyp315Base hII

end Finite

end Ch3n

end CFSG.Quasithin
