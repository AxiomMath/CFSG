module

public import CFSG.Quasithin.Vol2.KGFactC31M23Cases
public import CFSG.Quasithin.Vol2.KGFactC31Concl
import CFSG.Quasithin.Vol2.KGFactC31M22Mod

public section

namespace CFSG.Quasithin.KGC31.M23

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.KGC31 Matrix
  CFSG.LieType.BorelTits
open scoped Pointwise

variable {A : Type} [Group A]

theorem map_genOf_eq (ws : List (List ℤ)) (ι : G₀ →* A) :
    (genOf ws).map ι = Subgroup.closure {x | ∃ w ∈ ws, ι (elt w) = x} := by
  rw [genOf, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩; exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

theorem elt_mem_genOf {ws : List (List ℤ)} {j : ℕ} (hj : j < ws.length) :
    elt (ws.getD j []) ∈ genOf ws :=
  Subgroup.subset_closure ⟨_, by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj,
    rfl⟩

@[expose] def trU : Matrix.SpecialLinearGroup (Fin 2) Duad.F4 := ⟨!![1, 1; 0, 1], by decide⟩
@[expose] def trL : Matrix.SpecialLinearGroup (Fin 2) Duad.F4 := ⟨!![1, 0; 1, 1], by decide⟩

theorem fix_eq_zero : ∀ y : Fin 2 → Duad.F4, (trU : Matrix (Fin 2) (Fin 2) Duad.F4) *ᵥ y = y →
    (trL : Matrix (Fin 2) (Fin 2) Duad.F4) *ᵥ y = y → y = 0 := by decide

theorem mem_statedSL2 (g : Matrix.SpecialLinearGroup (Fin 2) Duad.F4) :
    Matrix.SpecialLinearGroup.toGL g ∈ StatedSL 2 Duad.F4 :=
  CFSG.Quasithin.KGC31.M22.mem_statedSL2 g

theorem concl_duad [Finite A]
    {S M₀ R M V : Subgroup A} (hSs : IsSporadic .M23 ↥S)
    (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hRM : R ≤ M)
    (ι : G₀ →* A) (hι : Function.Injective ι)
    (hV : V = (eSub basis_duad).map ι) (hO : pCoreOf 2 M₀ = (eSub basis_duad).map ι)
    (hM : M₀ = Mduad.map ι)
    (hC : M₀ ⊓ Subgroup.centralizer (((eSub basis_duad).map ι : Subgroup A) : Set A) ≤
      (eSub basis_duad).map ι)
    (hVR : V ≤ R) (hRC : R ≤ Subgroup.centralizer (V : Set A)) :
    Concl S M₀ R M V := by
  have hvA : EBasis fun i => ι (vDuad i) := basis_duad.map hι
  have hVA : (eSub basis_duad).map ι = eSub hvA := eSub_map basis_duad hι
  rw [hVA] at hV hO hC
  subst hV
  set V := eSub hvA with hVdef
  have hgen : ∀ j < 2, ∃ hN : ι (elt (tGenW.getD j [])) ∈ eNorm hvA,
      eMat hvA ⟨_, hN⟩ = matOf 4 tMasks j := fun j hj => by
    have hconj := conj_map (fun i => conj_duad hj i) ι
    exact ⟨mem_eNorm hvA _ hconj, eMat_eq hvA _ _ hconj⟩
  have hM₀f : M₀ ≤ Duad.f4Stab hvA := by
    rw [hM, Mduad, map_genOf_eq, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨j, hj, rfl⟩ := exists_index_of_mem tGenW_length hw
    obtain ⟨hN, hmat⟩ := hgen j hj
    exact ⟨hN, by rw [hmat]; exact duadMat_comm j hj⟩
  have hRf : R ≤ Duad.f4Stab hvA := fun r hr => by
    have hN := mem_eNorm_of_cent hvA (hRC hr)
    refine ⟨hN, ?_⟩
    rw [(eMat_eq_one_iff hvA ⟨r, hN⟩).mpr (hRC hr), one_mul, mul_one]
  have hXf : M₀ ⊔ R ≤ Duad.f4Stab hvA := sup_le hM₀f hRf
  let D : ↥(Duad.f4Stab hvA) →* (Duad.F4)ˣ :=
    Matrix.GeneralLinearGroup.det.comp (Duad.f4Rep hvA)
  let K : Subgroup A := D.ker.map (Duad.f4Stab hvA).subtype
  have hmemK : ∀ (y : A) (hy : y ∈ Duad.f4Stab hvA),
      (Duad.f4Mat (eMat hvA ⟨y, hy.1⟩)).det = 1 → y ∈ K := by
    intro y hy hd
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    show D ⟨y, hy⟩ = 1
    apply Units.ext
    simpa [D, Duad.f4Rep_coe] using hd
  have hXK : M₀ ⊔ R ≤ K := by
    refine sup_le ?_ fun r hr => hmemK r (hRf hr) ?_
    · rw [hM, Mduad, map_genOf_eq, Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨j, hj, rfl⟩ := exists_index_of_mem tGenW_length hw
      obtain ⟨hN, hmat⟩ := hgen j hj
      exact hmemK _ ⟨hN, by rw [hmat]; exact duadMat_comm j hj⟩ (by
        rw [hmat]; exact duadMat_det j hj)
    · rw [(eMat_eq_one_iff hvA ⟨r, (hRf hr).1⟩).mpr (hRC hr), Duad.f4Mat_one]
      exact Matrix.det_one
  have hdetK : ∀ (y : A) (hy : y ∈ Duad.f4Stab hvA), y ∈ K →
      (Duad.f4Mat (eMat hvA ⟨y, hy.1⟩)).det = 1 := by
    rintro y hy ⟨z, hz, rfl⟩
    have h3 := congrArg Units.val (show D z = 1 from hz)
    simpa [D, Duad.f4Rep_coe] using h3
  have hdetX : ∀ x : ↥(M₀ ⊔ R), (Duad.f4Mat (eMat hvA ⟨x, (hXf x.2).1⟩)).det = 1 :=
    fun x => hdetK x (hXf x.2) (hXK x.2)
  have hdet₀ : ∀ x : ↥M₀, (Duad.f4Mat (eMat hvA ⟨x, (hM₀f x.2).1⟩)).det = 1 :=
    fun x => hdetK x (hM₀f x.2) (hXK (le_sup_left (a := M₀) x.2))
  let α₀ := Duad.f4Hom hvA hM₀f hdet₀
  have hVM₀ : V ≤ M₀ := hO ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 M₀
  have hker₀ : α₀.ker = V.subgroupOf M₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : Duad.f4Rep hvA (Subgroup.inclusion hM₀f x) = 1 := congrArg Subtype.val h1
      exact hC ⟨x.2, (Duad.f4Rep_eq_one_iff hvA _).mp h2⟩
    · intro hx
      apply Subtype.ext
      refine (Duad.f4Rep_eq_one_iff hvA (Subgroup.inclusion hM₀f x)).mpr ?_
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm hvA _ _ hy hx
  have hcM : Nat.card M₀ = 960 := by rw [hM, Subgroup.card_map_of_injective hι, card_Mduad]
  have hsurj₀ : Function.Surjective α₀ := by
    have h1 := card_range_eq hVM₀ α₀ hker₀
    rw [card_eSub, hcM] at h1
    have h2 : Nat.card α₀.range = Nat.card ↥(StatedSL 2 Duad.F4) := by
      rw [Duad.card_statedSL]; omega
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ h2
  have hpk : CFSG.pCore 2 ↥M₀ = α₀.ker := by rw [← Hex.pCoreOf_subgroupOf', hO, hker₀]
  let eQ : ModO2 M₀ ≃* ↥(StatedSL 2 Duad.F4) :=
    (QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α₀ hsurj₀)
  have hpsl : IsPSL 2 2 2 (ModO2 M₀) := Duad.isPSL_of_equiv eQ
  have hext : IsExt ↥M₀ (fun N _ => IsE2 4 N) (fun Y _ => IsPSL 2 2 2 Y) := by
    have hn : (V.subgroupOf M₀).Normal := by rw [← hker₀]; exact α₀.normal_ker
    exact ⟨V.subgroupOf M₀, hn, ⟨(Subgroup.subgroupOfEquivOfLe hVM₀).trans (ecoords hvA)⟩,
      Duad.isPSL_of_equiv ((QuotientGroup.quotientMulEquivOfEq hker₀.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α₀ hsurj₀))⟩
  have hRN : R ≤ Subgroup.normalizer (M₀ : Set A) := hRM.trans hMN
  have hXC : (M₀ ⊔ R) ⊓ Subgroup.centralizer (V : Set A) = R :=
    sup_inf_centralizer_eq hRN hRC hC hVR
  let α := Duad.f4Hom hvA hXf hdetX
  have hker : α.ker = R.subgroupOf (M₀ ⊔ R) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : Duad.f4Rep hvA (Subgroup.inclusion hXf x) = 1 := congrArg Subtype.val h1
      have h3 : (x : A) ∈ (M₀ ⊔ R) ⊓ Subgroup.centralizer (V : Set A) :=
        ⟨x.2, (Duad.f4Rep_eq_one_iff hvA _).mp h2⟩
      rw [hXC] at h3
      exact h3
    · intro hx
      apply Subtype.ext
      exact (Duad.f4Rep_eq_one_iff hvA (Subgroup.inclusion hXf x)).mpr (hRC hx)
  have hsurj : Function.Surjective α := by
    intro σ
    obtain ⟨m, hm⟩ := hsurj₀ σ
    exact ⟨⟨m, le_sup_left (a := M₀) m.2⟩, Subtype.ext (Units.ext (by
      rw [← hm]; rfl))⟩
  let β : ↥V →* Multiplicative (Fin 2 → Duad.F4) :=
    (AddMonoidHom.toMultiplicative Duad.toF4Hom).comp (ecoords hvA).toMonoidHom
  have hβ : ∀ x, Multiplicative.toAdd (β x) = Duad.toF4 (Multiplicative.toAdd (ecoords hvA x)) :=
    fun _ => rfl
  have hβinj : Function.Injective β :=
    (Multiplicative.ofAdd.injective.comp Duad.toF4_injective).comp (ecoords hvA).injective
  have hβsurj : Function.Surjective β := by
    intro y
    obtain ⟨c, hc⟩ := Duad.toF4_surjective (Multiplicative.toAdd y)
    refine ⟨(ecoords hvA).symm (Multiplicative.ofAdd c), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hβ, MulEquiv.apply_symm_apply, toAdd_ofAdd, hc]
  have hβeq : ∀ (a : ↥(M₀ ⊔ R)) (u w : ↥V), (w : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β w) =
        ((α a : GL (Fin 2) Duad.F4) : Matrix (Fin 2) (Fin 2) Duad.F4).mulVec
          (Multiplicative.toAdd (β u)) := by
    intro a u w hw
    rw [hβ, hβ, ecoords_conj hvA ⟨a, (hXf a.2).1⟩ u w hw]
    exact Duad.toF4_conj hvA (Subgroup.inclusion hXf a) _
  have hZ : V ⊓ Subgroup.centralizer (M₀ : Set A) = ⊥ := by
    refine eq_bot_iff.mpr fun x ⟨hxV, hxC⟩ => ?_
    have hfix : ∀ m : ↥M₀, ((α₀ m : GL (Fin 2) Duad.F4) : Matrix (Fin 2) (Fin 2) Duad.F4) *ᵥ
        Multiplicative.toAdd (β ⟨x, hxV⟩) = Multiplicative.toAdd (β ⟨x, hxV⟩) := by
      intro m
      have h1 := hβeq ⟨m, le_sup_left (a := M₀) m.2⟩ ⟨x, hxV⟩ ⟨x, hxV⟩ (by
        show x = (m : A) * x * (m : A)⁻¹
        rw [Subgroup.mem_centralizer_iff.mp hxC m m.2, mul_inv_cancel_right])
      exact h1.symm
    obtain ⟨mU, hmU⟩ := hsurj₀ ⟨_, mem_statedSL2 trU⟩
    obtain ⟨mL, hmL⟩ := hsurj₀ ⟨_, mem_statedSL2 trL⟩
    have h1 := hfix mU
    have h2 := hfix mL
    rw [hmU] at h1
    rw [hmL] at h2
    have h0 := fix_eq_zero _ h1 h2
    have : β ⟨x, hxV⟩ = 1 := h0
    have := hβinj (this.trans (map_one β).symm)
    exact congrArg Subtype.val this
  have hsec : IsNaturalSection (M₀ ⊔ R) V (V ⊓ Subgroup.centralizer (M₀ : Set A))
      (R.subgroupOf (M₀ ⊔ R)) (StatedSL 2 Duad.F4) := by
    refine ⟨fun x hx => (hXf hx).1, α, hsurj, hker, β, hβsurj, ?_, hβeq⟩
    rw [hZ, Subgroup.bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff β).mpr hβinj
  have hM₀ : conjClosure M₀ M = M₀ := conjClosure_eq_self' hMN
  refine ⟨Or.inr (Or.inl ⟨hSs, Or.inl ?_⟩), Or.inl ⟨2, hpsl, Or.inl ⟨Duad.F4, inferInstance,
    inferInstance, by decide, hsec⟩⟩, ?_⟩
  · rw [hM₀]
    exact hext
  · refine summand_of_card ?_
    rw [card_eSub]
    norm_num

theorem concl_e8 [Finite A]
    {S M₀ R M V : Subgroup A} (hSs : IsSporadic .M23 ↥S)
    (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hRM : R ≤ M)
    (hcomm : ⁅V, M₀⁆ = V) (ι : G₀ →* A) (hι : Function.Injective ι)
    (hV : V = (eSub basis_e8).map ι) (hO : pCoreOf 2 M₀ = (eSub basis_e8).map ι)
    (hM : M₀ = (eNorm basis_e8).map ι)
    (hC : M₀ ⊓ Subgroup.centralizer (((eSub basis_e8).map ι : Subgroup A) : Set A) ≤
      (eSub basis_e8).map ι)
    (hVR : V ≤ R) (hRC : R ≤ Subgroup.centralizer (V : Set A)) :
    Concl S M₀ R M V := by
  have hvA : EBasis fun i => ι (vE8 i) := basis_e8.map hι
  have hVA : (eSub basis_e8).map ι = eSub hvA := eSub_map basis_e8 hι
  rw [hVA] at hV hO hC
  subst hV
  set V := eSub hvA with hVdef
  have hM₀N : M₀ ≤ eNorm hvA := le_normalizer_of_comm hcomm
  have hRN' : R ≤ eNorm hvA := fun r hr => mem_eNorm_of_cent hvA (hRC hr)
  have hXN : M₀ ⊔ R ≤ eNorm hvA := sup_le hM₀N hRN'
  have hVM₀ : V ≤ M₀ := hO ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 M₀
  let α₀ := E8.e3Hom hvA hM₀N
  have hker₀ : α₀.ker = V.subgroupOf M₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E8.e3Hom_eq_one_iff]
    constructor
    · intro h; exact hC ⟨x.2, h⟩
    · intro hx
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm hvA _ _ hy hx
  have hcM : Nat.card M₀ = 1344 := by
    rw [hM, Subgroup.card_map_of_injective hι, card_eNorm_e8]
  have hsurj₀ : Function.Surjective α₀ := by
    have h1 := card_range_eq hVM₀ α₀ hker₀
    rw [card_eSub, hcM] at h1
    have h2 : Nat.card α₀.range = Nat.card ↥(StatedSL 3 (ZMod 2)) := by
      rw [E8.card_statedSL3]; omega
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ h2
  have hpk : CFSG.pCore 2 ↥M₀ = α₀.ker := by rw [← Hex.pCoreOf_subgroupOf', hO, hker₀]
  have hpsl : IsPSL 3 2 1 (ModO2 M₀) := E8.isPSL_of_equiv3
    ((QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α₀ hsurj₀))
  have hext : IsExt ↥M₀ (fun N _ => IsE2 3 N) (fun Y _ => IsPSL 3 2 1 Y) := by
    have hn : (V.subgroupOf M₀).Normal := by rw [← hker₀]; exact α₀.normal_ker
    exact ⟨V.subgroupOf M₀, hn, ⟨(Subgroup.subgroupOfEquivOfLe hVM₀).trans (ecoords hvA)⟩,
      E8.isPSL_of_equiv3 ((QuotientGroup.quotientMulEquivOfEq hker₀.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α₀ hsurj₀))⟩
  have hRN : R ≤ Subgroup.normalizer (M₀ : Set A) := hRM.trans hMN
  have hXC : (M₀ ⊔ R) ⊓ Subgroup.centralizer (V : Set A) = R :=
    sup_inf_centralizer_eq hRN hRC hC hVR
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
  refine ⟨Or.inr (Or.inl ⟨hSs, Or.inr (Or.inr ?_)⟩),
    Or.inr (Or.inl ⟨3, Or.inl rfl, hpsl, Or.inl ⟨1, le_rfl, hsum⟩⟩), ?_⟩
  · rw [hM₀]
    exact hext
  · refine summand_of_card ?_
    rw [card_eSub]
    norm_num

theorem conj_wGen (ι : G₀ →* A) {j : ℕ} (hj : j < 2) (i : Fin 4) :
    ι (elt (wGenW.getD j [])) * ι (vW i) * (ι (elt (wGenW.getD j [])))⁻¹ =
      eElt (fun i => ι (vW i)) fun r => matOf 4 wMasks j r i :=
  conj_map (fun i => conj_w hj i) ι i

theorem wGen_mem_map (ι : G₀ →* A) {j : ℕ} (hj : j < 2) :
    ι (elt (wGenW.getD j [])) ∈ Mw.map ι :=
  ⟨_, elt_mem_genOf (by rw [wGenW_length]; exact hj), rfl⟩

theorem irr_map (ι : G₀ →* A) (hι : Function.Injective ι)
    {W' : Subgroup A} (hW' : W' ≤ (eSub basis_w).map ι)
    (hN : Mw.map ι ≤ Subgroup.normalizer (W' : Set A)) :
    W' = ⊥ ∨ W' = (eSub basis_w).map ι := by
  rw [eSub_map basis_w hι] at hW' ⊢
  exact irr_of_gens (basis_w.map hι) (conj_wGen ι (by norm_num)) (conj_wGen ι (by norm_num)) hW'
    (hN (wGen_mem_map ι (by norm_num))) (hN (wGen_mem_map ι (by norm_num)))

theorem concl_w [Finite A]
    {S M₀ R M V : Subgroup A} (hSs : IsSporadic .M23 ↥S) (hper : ⁅M₀, M₀⁆ = M₀)
    (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hcomm : ⁅V, M₀⁆ = V) (ι : G₀ →* A)
    (hι : Function.Injective ι) (hV : V = (eSub basis_w).map ι)
    (hO : pCoreOf 2 M₀ = (eSub basis_w).map ι) (hM : M₀ = Mw.map ι)
    (hC : M₀ ⊓ Subgroup.centralizer (((eSub basis_w).map ι : Subgroup A) : Set A) ≤
      (eSub basis_w).map ι) :
    Concl S M₀ R M V := by
  have hvA : EBasis fun i => ι (vW i) := basis_w.map hι
  have hVA : (eSub basis_w).map ι = eSub hvA := eSub_map basis_w hι
  have hirr : ∀ W' : Subgroup A, W' ≤ eSub hvA → M₀ ≤ Subgroup.normalizer (W' : Set A) →
      W' = ⊥ ∨ W' = eSub hvA := fun W' hW' hN => by
    rw [← hVA] at hW' ⊢
    exact irr_map ι hι hW' (hM ▸ hN)
  rw [hVA] at hV hO hC
  subst hV hM
  let e : ↥Mw ≃* ↥(Mw.map ι) := Mw.equivMapOfInjective ι hι
  have hex : ∀ x : ↥(Mw.map ι), ι ((e.symm x : ↥Mw) : G₀) = x := fun x => by
    have h := congrArg Subtype.val (e.apply_symm_apply x)
    rwa [Subgroup.coe_equivMapOfInjective_apply] at h
  let α : ↥(Mw.map ι) →* ↥(alternatingGroup (Fin 7)) := wAlt.comp e.symm.toMonoidHom
  have hsurj : Function.Surjective α := wAlt_surjective.comp e.symm.surjective
  have hker : α.ker = (eSub hvA).subgroupOf (Mw.map ι) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hVA, ← hex x,
      Subgroup.mem_map_iff_mem hι]
    show wAlt (e.symm x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, ker_wAlt, Subgroup.mem_subgroupOf]
  obtain ⟨hblock, hext⟩ := A7.isExcA7Block_of hvA hper hO hcomm hC α hsurj hker hirr
  have hM₀ : conjClosure (Mw.map ι) M = Mw.map ι := conjClosure_eq_self' hMN
  refine ⟨Or.inr (Or.inl ⟨hSs, Or.inr (Or.inl ?_)⟩),
    Or.inr (Or.inr (Or.inr (Or.inl ⟨hSs, hblock⟩))), ?_⟩
  · rw [hM₀]
    exact hext
  · refine summand_of_card ?_
    rw [card_eSub]
    norm_num

theorem config_s [Finite A]
    {S M₀ R M V : Subgroup A} (hA : Nat.card A ≤ Nat.card S) (hR : IsPGroup 2 ↥R) (hRM : R ≤ M)
    (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A))
    (hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀)))
    (hVM₀ : V ≤ M₀) (hV : IsElemAbelian 2 V) (hcomm : ⁅V, M₀⁆ = V)
    (hVc : V ≤ CFSG.Quasithin.centerOf (pCoreOf 2 (M₀ ⊔ R)))
    (hNR : Subgroup.normalizer (R : Set A) ≤ M) {y t : A} (hy : y ∈ M₀) (ht : t ∈ V)
    (hyt : y * t * y⁻¹ ≠ t) (ι : G₀ →* A) (hι : Function.Injective ι) (hιS : ι.range = S)
    (hU : orbSub y t = (eSub basis_s).map ι) :
    V = (eSub basis_w).map ι ∧ pCoreOf 2 M₀ = (eSub basis_w).map ι ∧ M₀ = Mw.map ι ∧
      M₀ ⊓ Subgroup.centralizer (((eSub basis_w).map ι : Subgroup A) : Set A) ≤
        (eSub basis_w).map ι := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hOR, hRC, hNRM⟩ := orb_facts hR hRM hMN hM₀R hsyl hVM₀ hV hcomm hVc hNR
  have hM₀V := le_normalizer_of_comm hcomm
  set Wt := (eSub basis_w).map ι with hWt
  have hUV : (eSub basis_s).map ι ≤ V := hU ▸ orbSub_le (hM₀V hy) ht
  have hStop : S = ⊤ :=
    Subgroup.eq_top_of_card_eq S (le_antisymm (Subgroup.card_le_card_group S) hA)
  have hrange : ι.range = ⊤ := hιS.trans hStop
  have hCW0 : Subgroup.centralizer (eSub basis_w : Set G₀) = eSub basis_w :=
    le_antisymm cent_w fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm basis_w _ _ hy hx
  have hCW : Subgroup.centralizer (Wt : Set A) = Wt := by
    have h := map_centralizer_eq ι hι (eSub basis_w)
    rw [hrange, top_inf_eq, hCW0] at h
    exact h.symm
  have hCU : Subgroup.centralizer (((eSub basis_s).map ι : Subgroup A) : Set A) = Wt := by
    have h := map_centralizer_eq ι hι (eSub basis_s)
    rw [hrange, top_inf_eq, centralizer_s_eq] at h
    exact h.symm
  have hVC : V ≤ Subgroup.centralizer (V : Set A) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1
  have hCVle : Subgroup.centralizer (V : Set A) ≤ Wt := by
    rw [← hCU]
    exact Subgroup.centralizer_le hUV
  have hVW : V ≤ Wt := hVC.trans hCVle
  have hCV : Subgroup.centralizer (V : Set A) = Wt := by
    refine le_antisymm hCVle ?_
    rw [← hCW]
    exact Subgroup.centralizer_le hVW
  have hRW : R ≤ Wt := hRC.trans hCVle
  have hW2 : IsPGroup 2 ↥Wt := IsPGroup.of_card (n := 4) (by
    rw [hWt, Subgroup.card_map_of_injective hι, card_eSub])
  have hWM : Wt ≤ M :=
    ((le_of_eq hCW.symm).trans (Subgroup.centralizer_le hRW)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNR)
  have hM₀W : M₀ ≤ Subgroup.normalizer (Wt : Set A) := by
    have h := hM₀V.trans (normalizer_le_normalizer_centralizer V)
    rwa [hCV] at h
  have hWO : M₀ ⊓ Wt ≤ pCoreOf 2 M₀ :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm) (hM₀W hm))
      (hW2.to_le inf_le_right)
  have hWsec : Wt ≤ CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀) := by
    intro w hw
    have hwN : w ∈ Subgroup.normalizer (M₀ : Set A) := hMN (hWM hw)
    refine ⟨hWM hw, hwN, normalizer_le_normalizer_pCoreOf 2 M₀ hwN, fun x hx => hWO ⟨?_, ?_⟩⟩
    · have h1 : w * x⁻¹ * w⁻¹ ∈ M₀ := (Subgroup.mem_normalizer_iff.mp hwN _).mp (M₀.inv_mem hx)
      have h2 := M₀.mul_mem hx h1
      rwa [show x * (w * x⁻¹ * w⁻¹) = x * w * x⁻¹ * w⁻¹ by group] at h2
    · have h1 : x * w * x⁻¹ ∈ Wt := (Subgroup.mem_normalizer_iff.mp (hM₀W hx) w).mp hw
      exact Wt.mul_mem h1 (Wt.inv_mem hw)
  have hRWeq : Wt = R := eq_of_isSylowTwoOf_le hsyl hRW hWsec hW2
  have hNW : Subgroup.normalizer (Wt : Set A) = Mw.map ι := by
    have h := map_normalizer_eq ι hι (eSub basis_w)
    rw [hrange, top_inf_eq] at h
    rw [Mw_eq, h]
  have hNWM₀ : Subgroup.normalizer (Wt : Set A) ≤ Subgroup.normalizer (M₀ : Set A) := by
    rw [hRWeq]
    exact hNRM
  have hM₀Mw : M₀ ≤ Mw.map ι := hNW ▸ hM₀W
  have hWMw : Wt ≤ Mw.map ι := hNW ▸ Subgroup.le_normalizer
  have hWab : ∀ a ∈ Wt, ∀ b ∈ Wt, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, eSub_comm basis_w a b ha hb]
  have hsup : M₀ ⊔ Wt = Mw.map ι := by
    rcases simple_map ι hι refData_w.simple (M₀ ⊔ Wt) le_sup_right (sup_le hM₀Mw hWMw)
        (fun g hg => by
          rw [← hNW] at hg
          exact mem_normalizer_sup (hNWM₀ hg) hg) with h | h
    · exfalso
      have hM₀le : M₀ ≤ Wt := le_sup_left.trans h.le
      exact hyt (by rw [hWab y (hM₀le hy) t (hVW ht), mul_inv_cancel_right])
    · exact h
  have hInf : M₀ ⊓ Wt = Wt := by
    have hN : Mw.map ι ≤ Subgroup.normalizer ((M₀ ⊓ Wt : Subgroup A) : Set A) := fun g hg => by
      rw [← hNW] at hg
      exact mem_normalizer_inf (hNWM₀ hg) hg
    rcases irr_map ι hι inf_le_right hN with h | h
    · exfalso
      have htM : t ∈ M₀ ⊓ Wt := ⟨hVM₀ ht, hVW ht⟩
      rw [h, Subgroup.mem_bot] at htM
      exact hyt (by rw [htM, mul_one, mul_inv_cancel])
    · exact h
  have hWM₀ : Wt ≤ M₀ := hInf ▸ inf_le_left
  have hM₀eq : M₀ = Mw.map ι := by
    rw [← hsup]
    exact (sup_eq_left.mpr hWM₀).symm
  have hO : pCoreOf 2 M₀ = Wt :=
    le_antisymm (hOR.trans hRWeq.symm.le) (le_pCoreOf_of_le_normalizer 2 hWM₀ hM₀W hW2)
  have hVeq : V = Wt := by
    rcases irr_map ι hι hVW (hM₀eq ▸ hM₀V) with h | h
    · exfalso
      rw [h, Subgroup.mem_bot] at ht
      exact hyt (by rw [ht, mul_one, mul_inv_cancel])
    · exact h
  refine ⟨hVeq, hO, hM₀eq, ?_⟩
  rw [hCW]
  exact inf_le_right

end CFSG.Quasithin.KGC31.M23

end
