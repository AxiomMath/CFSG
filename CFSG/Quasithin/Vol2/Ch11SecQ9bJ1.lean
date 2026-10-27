module

public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar
public import CFSG.Quasithin.Vol2.Ch11SecA12O3
public import CFSG.Quasithin.Vol2.Ch11SecA12Setup
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch11SecSQuot

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₁ K : Subgroup G} {n : ℕ}

namespace C11P9B

omit [Finite G] in
theorem pCore_modO2Image_eq_bot {H K : Subgroup G} (hn : (K.subgroupOf H).Normal) :
    CFSG.pCore 2 ↥(modO2Image H K) = ⊥ := by
  have : (modO2Image H K).Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  have h1 := map_pCore_le_pCore (modO2Image H K)
  rw [pCore_two_quotient_pCore_two, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1

theorem modO2Image_equiv {H K : Subgroup G} (hKH : K ≤ H) (hn : (K.subgroupOf H).Normal) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(modO2Image H K)) := by
  obtain ⟨e⟩ := modO2Image_quotEquiv hKH
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq (pCore_modO2Image_eq_bot hn)).trans
    QuotientGroup.quotientBot)⟩

omit [Finite G] in
theorem conj_mem_of_mk_mem_normalizer {H T : Subgroup G} (hTH : T ≤ H) (hOT : pCoreOf 2 H ≤ T)
    {g : ↥H} (hg : QuotientGroup.mk' (CFSG.pCore 2 ↥H) g ∈
      Subgroup.normalizer (modO2Image H T : Set (↥H ⧸ CFSG.pCore 2 ↥H)))
    {t : G} (ht : t ∈ T) : (g : G) * t * (g : G)⁻¹ ∈ T := by
  have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (g * ⟨t, hTH ht⟩ * g⁻¹) ∈ modO2Image H T := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp
      ⟨⟨t, hTH ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hmem : ((g * ⟨t, hTH ht⟩ * g⁻¹ : ↥H) : G) ∈
      ((modO2Image H T).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype :=
    ⟨_, hmk, rfl⟩
  rw [map_comap_modO2Image hTH, sup_eq_left.mpr hOT] at hmem
  simpa using hmem

omit [Finite G] in
theorem mem_normalizer_of_mk_mem_normalizer {H T : Subgroup G} (hTH : T ≤ H)
    (hOT : pCoreOf 2 H ≤ T) {g : ↥H} (hg : QuotientGroup.mk' (CFSG.pCore 2 ↥H) g ∈
      Subgroup.normalizer (modO2Image H T : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    (g : G) ∈ Subgroup.normalizer (T : Set G) := by
  have hg' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) g⁻¹ ∈
      Subgroup.normalizer (modO2Image H T : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hg
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨fun ht => conj_mem_of_mk_mem_normalizer hTH hOT hg ht, fun ht => ?_⟩
  have := conj_mem_of_mk_mem_normalizer hTH hOT hg' ht
  simpa [mul_assoc] using this

theorem le_normalizer_of_J1 (hFb : Facts12b) (h331 : Stmt3_3_1) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hNK : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₁ ≤ K) (hJ : IsSporadic .J1 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    K ≤ Subgroup.normalizer (L : Set G) := by
  set H := K ⊔ T with hH
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := (IsVi.le_normalizer hV₁).trans hNK
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTN)
  have hSn : (modO2Image H K).Normal := hKn.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := modO2Image_equiv le_sup_left hKn
  obtain ⟨j⟩ := hJ
  have hSJ : IsSporadic .J1 ↥(modO2Image H K) := ⟨e.symm.trans j⟩
  have hTsyl : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right
  have hOT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hL₁H : LOf L V₁ ≤ H := hLK.trans le_sup_left
  have hJ1 := hFb.j1 _ (modO2Image H K) (modO2Image H T) (modO2Image H (LOf L V₁)) hSn hSJ
    (isSylowTwoOf_modO2Image hTsyl)
    (Subgroup.map_mono fun y hy => Subgroup.mem_subgroupOf.mpr
      (hLK (Subgroup.mem_subgroupOf.mp hy)))
    (modO2Image_ne_bot hL₁H (perfectCore_perfect _) (lOf_ne_bot hN h1102 h hV₁ (Or.inl rfl)))
    (modO2Image_perfect hL₁H (perfectCore_perfect _))
    (modO2Image_le_normalizer (T_le_normalizer_lOf h.normal (IsVi.le_normalizer hV₁)))
  set A := Subgroup.normalizer (L : Set G) ⊓ H with hA
  have hL₁M : LOf L V₁ ≤ Subgroup.normalizer (L : Set G) :=
    ((perfectCore_le _).trans inf_le_left).trans Subgroup.le_normalizer
  have hBA : modO2Image H (LOf L V₁) ≤ modO2Image H A :=
    Subgroup.map_mono fun y hy => Subgroup.mem_subgroupOf.mpr
      ⟨hL₁M (Subgroup.mem_subgroupOf.mp hy), hL₁H (Subgroup.mem_subgroupOf.mp hy)⟩
  have hNA : Subgroup.normalizer (modO2Image H T : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ≤
      modO2Image H A := by
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact ⟨g, Subgroup.mem_subgroupOf.mpr
      ⟨normalizer_T_le h331 h (mem_normalizer_of_mk_mem_normalizer le_sup_right hOT hq), g.2⟩,
      rfl⟩
  have hSA := hJ1.trans (sup_le hBA hNA)
  intro k hk
  have hkH : k ∈ H := Subgroup.mem_sup_left hk
  have hk' : k ∈ ((modO2Image H A).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map
      H.subtype := ⟨⟨k, hkH⟩, hSA ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, rfl⟩
  rw [map_comap_modO2Image inf_le_right] at hk'
  exact (sup_le inf_le_left (hOT.trans h.normal)) hk'

theorem false_of_J1 (hFb : Facts12b) (h331 : Stmt3_3_1) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hK : K ∈ cComp (Subgroup.normalizer (V₁ : Set G)))
    (hNK : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hlt : LOf L V₁ < K) (hJ : IsSporadic .J1 (↥K ⧸ CFSG.pCore 2 ↥K)) : False :=
  not_le_normalizer_of_lt hN h1102 h hV₁ (Or.inl rfl) hK hlt
    (le_normalizer_of_J1 hFb h331 hN h1102 h hV₁ hNK hlt.le hJ)

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
