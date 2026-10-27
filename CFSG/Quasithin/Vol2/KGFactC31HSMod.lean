module

public import CFSG.Quasithin.Vol2.KGFactC31HSGen
public import CFSG.Quasithin.Vol2.KGFactC31Concl
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.KGFactC31HSRef8

public section

namespace CFSG.Quasithin.KGC31.HS

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin.KGC31
  CFSG.RankThree.Native Matrix CFSG.LieType.BorelTits

variable {A : Type} [Group A]

theorem isZ4Cubed_of_mulEquiv : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) →
    IsZ4Cubed V → IsZ4Cubed W := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩

theorem concl_a6 [Finite A]
    {S M₀ R M V : Subgroup A} (hSs : IsSporadic .HS ↥S)
    (hcS : Subgroup.center ↥S = ⊥) (hM₀S : M₀ ≤ S) (hper : ⁅M₀, M₀⁆ = M₀)
    (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hcomm : ⁅V, M₀⁆ = V) (ι : G₀ →* A)
    (hι : Function.Injective ι) (hV : V = (eSub basis_u16).map ι)
    (hO : pCoreOf 2 M₀ = (eSub basis_u16).map ι) (hM : M₀ = M16.map ι)
    (hC : M₀ ⊓ Subgroup.centralizer (((eSub basis_u16).map ι : Subgroup A) : Set A) ≤
      (eSub basis_u16).map ι) :
    Concl S M₀ R M V := by
  have hvA : EBasis fun i => ι (vU16 i) := basis_u16.map hι
  have hVA : (eSub basis_u16).map ι = eSub hvA := eSub_map basis_u16 hι
  rw [hVA] at hV hO hC
  have hLs : M₀ ≤ Hex.ovStab hvA := by
    rw [hM, Subgroup.map_le_iff_le_comap]
    refine genOf_le fun j hj => ?_
    have hj2 : j < 2 := by rw [m16GenW_length] at hj; exact hj
    have hconj := conj_map (fun i => conj_m16 hj2 i) ι
    have hN : ι (elt (m16GenW.getD j [])) ∈ eNorm hvA := mem_eNorm hvA _ hconj
    refine ⟨hN, fun i => ?_⟩
    rw [Hex.ovImg, eMat_eq hvA ⟨_, hN⟩ _ hconj]
    exact m16Mat_perm j hj2 i
  have hcard : Nat.card M₀ = 360 * 16 := by
    rw [hM, Subgroup.card_map_of_injective hι, card_M16]
  obtain ⟨hblock, hext⟩ := Hex.isAltBlockType_of_ovoids hvA hLs hper hO (hV ▸ hcomm) hC hcard
  have hM₀ : conjClosure M₀ M = M₀ := conjClosure_eq_self' hMN
  have hsp := isSporadic_quot_center hcS hSs
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hsp, Or.inr ?_⟩)))),
    Or.inr (Or.inr (Or.inl ⟨Or.inr hsp, hblock⟩)), ?_⟩
  · rw [hM₀]
    exact isExt_of_mulEquiv (imageModCenterEquiv hM₀S hcS).symm (isE2_of_mulEquiv 4)
      (isAlt_of_mulEquiv 6) hext
  · refine summand_of_card ?_
    rw [hV, card_eSub]
    norm_num

theorem N8_le_normalizer_Q8 :
    N8 ≤ Subgroup.normalizer (Q8 : Set G₀) := by
  rw [← cent_u8_eq, N8_eq]
  exact normalizer_le_normalizer_centralizer _

theorem N8_normal_eq
    (K : Subgroup G₀) (hKN : K ≤ N8)
    (hNK : N8 ≤ Subgroup.normalizer (K : Set G₀)) (_hK : ⁅K, K⁆ = K) (hKQ : ¬ K ≤ Q8) :
    K = N8 := by
  have := E8.isSimpleGroup_statedSL3
  exact perfect_normal_eq Q8_le_N8 N8_perfect Q8_comm N8_le_normalizer_Q8
    (simple_of_surj n8Hom n8Hom_surjective ker_n8Hom) K hKN hNK hKQ

theorem config_u8 [Finite A]
    {S M₀ R M V : Subgroup A} (hS : S.Normal)
    (hA2 : Nat.card A ≤ 2 * Nat.card S) (hM₀S : M₀ ≤ S) (hper : ⁅M₀, M₀⁆ = M₀)
    (hR : IsPGroup 2 ↥R) (hRM : R ≤ M) (hMN : M ≤ Subgroup.normalizer (M₀ : Set A))
    (hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A))
    (hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀)))
    (hVM₀ : V ≤ M₀) (hV : IsElemAbelian 2 V) (hcomm : ⁅V, M₀⁆ = V)
    (hVc : V ≤ CFSG.Quasithin.centerOf (pCoreOf 2 (M₀ ⊔ R)))
    (hNR : Subgroup.normalizer (R : Set A) ≤ M) {y t : A} (hy : y ∈ M₀) (ht : t ∈ V)
    (hyt : y * t * y⁻¹ ≠ t) (ι : G₀ →* A) (hι : Function.Injective ι) (hιS : ι.range = S)
    (hU : orbSub y t = (eSub basis_u8).map ι) :
    V = (eSub basis_u8).map ι ∧ pCoreOf 2 M₀ = Q8.map ι ∧ M₀ = N8.map ι ∧
      R = Subgroup.centralizer (((eSub basis_u8).map ι : Subgroup A) : Set A) := by
  have hQ2 : IsPGroup 2 ↥Q8 := IsPGroup.of_card (n := 6) (by rw [card_Q8]; norm_num)
  exact config_of_abelCent hS hA2 hM₀S hper hR hRM hMN hM₀R hsyl hVM₀ hV hcomm hVc hNR hy ht hyt
    ι hι hιS cent_u8_eq hQ2 (fun q hq hq2 => mem_u8_of_sq hq hq2) Q8_le_N8 N8_eq.symm
    N8_normal_eq hU

theorem mem_centralizer_u8_iff
    (ι : G₀ →* A) (hι : Function.Injective ι) {x : A}
    (hx : x ∈ ι.range) :
    x ∈ Subgroup.centralizer (((eSub basis_u8).map ι : Subgroup A) : Set A) ↔ x ∈ Q8.map ι := by
  rw [← cent_u8_eq, map_centralizer_eq ι hι]
  exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

theorem concl_z4 [Finite A]
    {S M₀ R M V : Subgroup A} (hSs : IsSporadic .HS ↥S)
    (hcS : Subgroup.center ↥S = ⊥) (hM₀S : M₀ ≤ S) (hMN : M ≤ Subgroup.normalizer (M₀ : Set A))
    (hcomm : ⁅V, M₀⁆ = V) (ι : G₀ →* A) (hι : Function.Injective ι)
    (hV : V = (eSub basis_u8).map ι) (hO : pCoreOf 2 M₀ = Q8.map ι) (hM : M₀ = N8.map ι)
    (hR : R = Subgroup.centralizer (((eSub basis_u8).map ι : Subgroup A) : Set A)) :
    Concl S M₀ R M V := by
  have hvA : EBasis fun i => ι (vU8 i) := basis_u8.map hι
  have hVA : (eSub basis_u8).map ι = eSub hvA := eSub_map basis_u8 hι
  have hcent : ∀ x ∈ M₀, x ∈ Subgroup.centralizer (V : Set A) ↔ x ∈ Q8.map ι := by
    intro x hx
    have hxr : x ∈ ι.range := by
      rw [hM] at hx
      obtain ⟨n, -, rfl⟩ := hx
      exact ⟨n, rfl⟩
    rw [hV]
    exact mem_centralizer_u8_iff ι hι hxr
  rw [hVA] at hV hR
  subst hV
  set V := eSub hvA with hVdef
  have hM₀N : M₀ ≤ eNorm hvA := le_normalizer_of_comm hcomm
  have hRC : R ≤ Subgroup.centralizer (V : Set A) := hR.le
  have hRN' : R ≤ eNorm hvA := fun r hr => mem_eNorm_of_cent hvA (hRC hr)
  have hXN : M₀ ⊔ R ≤ eNorm hvA := sup_le hM₀N hRN'
  have hQ8le : Q8.map ι ≤ M₀ := hM ▸ Subgroup.map_mono Q8_le_N8
  let α₀ := E8.e3Hom hvA hM₀N
  have hker₀ : α₀.ker = (Q8.map ι).subgroupOf M₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E8.e3Hom_eq_one_iff]
    exact hcent x x.2
  have hcM : Nat.card M₀ = 10752 := by
    rw [hM, Subgroup.card_map_of_injective hι, card_N8]
  have hsurj₀ : Function.Surjective α₀ := by
    have h1 := card_range_eq hQ8le α₀ hker₀
    rw [Subgroup.card_map_of_injective hι, card_Q8, hcM] at h1
    have h2 : Nat.card α₀.range = Nat.card ↥(StatedSL 3 (ZMod 2)) := by
      rw [E8.card_statedSL3]; omega
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ h2
  have hpk : CFSG.pCore 2 ↥M₀ = α₀.ker := by rw [← Hex.pCoreOf_subgroupOf', hO, hker₀]
  have hpsl : IsPSL 3 2 1 (ModO2 M₀) := E8.isPSL_of_equiv3
    ((QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α₀ hsurj₀))
  have hext : IsExt ↥M₀ (fun N _ => IsZ4Cubed N) (fun Y _ => IsPSL 3 2 1 Y) := by
    have hn : ((Q8.map ι).subgroupOf M₀).Normal := by rw [← hker₀]; exact α₀.normal_ker
    refine ⟨(Q8.map ι).subgroupOf M₀, hn, ⟨?_⟩, E8.isPSL_of_equiv3
      ((QuotientGroup.quotientMulEquivOfEq hker₀.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α₀ hsurj₀))⟩
    exact ((Subgroup.subgroupOfEquivOfLe hQ8le).trans
      (Q8.equivMapOfInjective ι hι).symm).trans q8Equiv.symm
  have hXC : (M₀ ⊔ R) ⊓ Subgroup.centralizer (V : Set A) = R :=
    le_antisymm (inf_le_right.trans hR.symm.le) (le_inf le_sup_right hRC)
  let α := E8.e3Hom hvA hXN
  have hker : α.ker = R.subgroupOf (M₀ ⊔ R) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E8.e3Hom_eq_one_iff]
    constructor
    · intro h
      have h3 : (x : A) ∈ (M₀ ⊔ R) ⊓ Subgroup.centralizer (V : Set A) := ⟨x.2, h⟩
      rw [hXC] at h3
      exact h3
    · intro hx; exact hRC hx
  have hsurj : Function.Surjective α := by
    intro σ
    obtain ⟨m, hm⟩ := hsurj₀ σ
    exact ⟨⟨m, le_sup_left (a := M₀) m.2⟩, Subtype.ext (Units.ext (by
      rw [← hm]; rfl))⟩
  let β : ↥V →* Multiplicative (Fin 3 → ZMod 2) := (ecoords hvA).toMonoidHom
  have hsec : IsNaturalSection (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R)) (StatedSL 3 (ZMod 2)) := by
    refine ⟨hXN, α, hsurj, hker, β, (ecoords hvA).surjective, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      exact (MonoidHom.ker_eq_bot_iff β).mpr (ecoords hvA).injective
    · intro a u w hw
      exact ecoords_conj hvA ⟨a, hXN a.2⟩ u w hw
  have hsum : IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R))
      (StatedSL 3 (ZMod 2)) false 1 :=
    (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hsec
  have hM₀ : conjClosure M₀ M = M₀ := conjClosure_eq_self' hMN
  have hsp := isSporadic_quot_center hcS hSs
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hsp, Or.inl ?_⟩)))),
    Or.inr (Or.inl ⟨3, Or.inl rfl, hpsl, Or.inl ⟨1, le_rfl, hsum⟩⟩), ?_⟩
  · rw [hM₀]
    exact isExt_of_mulEquiv (imageModCenterEquiv hM₀S hcS).symm isZ4Cubed_of_mulEquiv
      (isPSL_of_mulEquiv 3 2 1) hext
  · refine summand_of_card ?_
    rw [card_eSub]
    norm_num

end CFSG.Quasithin.KGC31.HS

end
