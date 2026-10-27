module

public import CFSG.Quasithin.Vol2.KGFactC31M22Ref
public import CFSG.Quasithin.Vol2.KGFactC31Shape

public section

namespace CFSG.Quasithin.KGC31.M22

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.KGC31 Matrix
open scoped Pointwise

@[expose] def Concl {A : Type} [Group A] (S M₀ R M V : Subgroup A) : Prop :=
  (C31Case3 ⊤ R M M₀ V S ∨ C31Case4 ⊤ R M M₀ V S ∨ C31Case5 ⊤ R M M₀ V S ∨
      C31Case6 ⊤ R M M₀ V S ∨ C31Case7 ⊤ R M M₀ V S ∨ C31Case8 ⊤ R M M₀ V S ∨
      C31Case9 ⊤ R M M₀ V S) ∧
    (C48Case1 ⊤ R M M₀ V S ∨ C48Case2 ⊤ R M M₀ V S ∨ C48Case3 ⊤ R M M₀ V S ∨
      C48Case4 ⊤ R M M₀ V S ∨ C48Case5 ⊤ R M M₀ V S ∨ C48Case6 ⊤ R M M₀ V S ∨
      C48Case7 ⊤ R M M₀ V S) ∧
    ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 M₀) →
      IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R)) (StatedSL m (ZMod 2)) false k →
      k ≤ 2

variable {A : Type} [Group A]

theorem sup_inf_centralizer_eq {M₀ R V : Subgroup A}
    (hRN : R ≤ Subgroup.normalizer (M₀ : Set A)) (hRC : R ≤ Subgroup.centralizer (V : Set A))
    (hM₀C : M₀ ⊓ Subgroup.centralizer (V : Set A) ≤ V) (hVR : V ≤ R) :
    (M₀ ⊔ R) ⊓ Subgroup.centralizer (V : Set A) = R := by
  refine le_antisymm (fun x ⟨hx, hxC⟩ => ?_) (le_inf le_sup_right hRC)
  have hx' : x ∈ ((M₀ : Set A) * (R : Set A)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M₀ R hRN]
    exact hx
  obtain ⟨m, hm, r, hr, rfl⟩ := hx'
  have hmC : m ∈ Subgroup.centralizer (V : Set A) := by
    have : m = m * r * r⁻¹ := by group
    rw [this]
    exact (Subgroup.centralizer (V : Set A)).mul_mem hxC
      ((Subgroup.centralizer (V : Set A)).inv_mem (hRC hr))
  exact R.mul_mem (hVR (hM₀C ⟨hm, hmC⟩)) hr

theorem summand_of_card [Finite A] {M₀ R V : Subgroup A} (hV : Nat.card V ≤ 16) :
    ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 M₀) →
      IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R)) (StatedSL m (ZMod 2)) false k →
      k ≤ 2 := by
  intro m k hm _ h
  have := summand_le hV (by omega) h
  omega

theorem map_genOf_eq (ws : List (List ℤ)) (ι : G₀ →* A) :
    (genOf ws).map ι = Subgroup.closure {x | ∃ w ∈ ws, ι (elt w) = x} := by
  rw [genOf, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩; exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

theorem conj_map {k : ℕ} {v : Fin k → G₀} {g : G₀} {M : Matrix (Fin k) (Fin k) (ZMod 2)}
    (h : ∀ i, g * v i * g⁻¹ = eElt v fun r => M r i) (ι : G₀ →* A) (i : Fin k) :
    ι g * ι (v i) * (ι g)⁻¹ = eElt (fun i => ι (v i)) fun r => M r i := by
  rw [← map_inv, ← map_mul, ← map_mul, h i, map_eElt]

@[expose] noncomputable def ecoords {Γ : Type*} [Group Γ] {n : ℕ} {v : Fin n → Γ}
    (hv : EBasis v) : ↥(eSub hv) ≃* Multiplicative (Fin n → ZMod 2) :=
  (MonoidHom.ofInjective (f := eHom hv)
    (fun c d hcd => (eElt_injective hv hcd : Multiplicative.toAdd c = Multiplicative.toAdd d))).symm

theorem eElt_ecoords {Γ : Type*} [Group Γ] {n : ℕ} {v : Fin n → Γ} (hv : EBasis v)
    (x : ↥(eSub hv)) : eElt v (Multiplicative.toAdd (ecoords hv x)) = (x : Γ) := by
  have h := (MonoidHom.ofInjective (f := eHom hv)
    (fun c d hcd => (eElt_injective hv hcd : Multiplicative.toAdd c =
      Multiplicative.toAdd d))).apply_symm_apply x
  exact congrArg Subtype.val h

theorem ecoords_conj {Γ : Type*} [Group Γ] {n : ℕ} {v : Fin n → Γ} (hv : EBasis v)
    (g : ↥(eNorm hv)) (u w : ↥(eSub hv)) (hw : (w : Γ) = g * u * g⁻¹) :
    Multiplicative.toAdd (ecoords hv w) = eMat hv g *ᵥ Multiplicative.toAdd (ecoords hv u) := by
  apply eElt_injective hv
  rw [eElt_ecoords, ← conj_eq_eElt_mulVec, eElt_ecoords]
  exact hw

theorem mem_eNorm_of_cent {Γ : Type*} [Group Γ] {n : ℕ} {v : Fin n → Γ} (hv : EBasis v) {r : Γ}
    (hr : r ∈ Subgroup.centralizer (eSub hv : Set Γ)) : r ∈ eNorm hv := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h := Subgroup.mem_centralizer_iff.mp hr x hx
    rw [← h, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h := Subgroup.mem_centralizer_iff.mp hr _ hx
    have hx' : x = r * x * r⁻¹ := by
      calc x = r⁻¹ * ((r * x * r⁻¹) * r) := by group
        _ = r⁻¹ * (r * (r * x * r⁻¹)) := by rw [h]
        _ = r * x * r⁻¹ := by group
    rw [hx']
    exact hx

theorem concl_hex [Finite A]
    {S M₀ R M V : Subgroup A} (hSs : IsSporadic .M22 ↥S) (hcS : Subgroup.center ↥S = ⊥)
    (hM₀S : M₀ ≤ S) (hper : ⁅M₀, M₀⁆ = M₀) (hMN : M ≤ Subgroup.normalizer (M₀ : Set A))
    (hcomm : ⁅V, M₀⁆ = V) (ι : G₀ →* A) (hι : Function.Injective ι)
    (hV : V = (eSub basis_hex).map ι) (hO : pCoreOf 2 M₀ = (eSub basis_hex).map ι)
    (hM : M₀ = Mhex.map ι)
    (hC : M₀ ⊓ Subgroup.centralizer (((eSub basis_hex).map ι : Subgroup A) : Set A) ≤
      (eSub basis_hex).map ι) :
    Concl S M₀ R M V := by
  have hvA : EBasis fun i => ι (vHex i) := basis_hex.map hι
  have hVA : (eSub basis_hex).map ι = eSub hvA := eSub_map basis_hex hι
  rw [hVA] at hV hO hC
  have hLs : M₀ ≤ Hex.ovStab hvA := by
    rw [hM, Mhex, map_genOf_eq, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨j, hj, rfl⟩ := exists_index_of_mem hexGenW_length hw
    have hconj := conj_map (fun i => conj_hex hj i) ι
    have hN : ι (elt (hexGenW.getD j [])) ∈ eNorm hvA := mem_eNorm hvA _ hconj
    refine ⟨hN, fun i => ?_⟩
    rw [Hex.ovImg, eMat_eq hvA ⟨_, hN⟩ _ hconj]
    exact hexMat_perm j hj i
  have hcard : Nat.card M₀ = 360 * 16 := by
    rw [hM, Subgroup.card_map_of_injective hι, card_Mhex]
  obtain ⟨hblock, hext⟩ := Hex.isAltBlockType_of_ovoids hvA hLs hper hO (hV ▸ hcomm) hC hcard
  have hM₀ : conjClosure M₀ M = M₀ := conjClosure_eq_self' hMN
  have hsp := isSporadic_quot_center hcS hSs
  refine ⟨Or.inl ⟨hsp, Or.inr (Or.inl ?_)⟩, Or.inr (Or.inr (Or.inl ⟨Or.inl hsp, hblock⟩)), ?_⟩
  · rw [hM₀]
    exact isExt_of_mulEquiv (imageModCenterEquiv hM₀S hcS).symm (isE2_of_mulEquiv 4)
      (isAlt_of_mulEquiv 6) hext
  · refine summand_of_card ?_
    rw [hV, card_eSub]
    norm_num

@[expose] def trU : Matrix.SpecialLinearGroup (Fin 2) Duad.F4 := ⟨!![1, 1; 0, 1], by decide⟩
@[expose] def trL : Matrix.SpecialLinearGroup (Fin 2) Duad.F4 := ⟨!![1, 0; 1, 1], by decide⟩

theorem fix_eq_zero : ∀ y : Fin 2 → Duad.F4, (trU : Matrix (Fin 2) (Fin 2) Duad.F4) *ᵥ y = y →
    (trL : Matrix (Fin 2) (Fin 2) Duad.F4) *ᵥ y = y → y = 0 := by decide

theorem mem_statedSL2 (g : Matrix.SpecialLinearGroup (Fin 2) Duad.F4) :
    Matrix.SpecialLinearGroup.toGL g ∈ StatedSL 2 Duad.F4 := by
  rw [statedSL_eq_range_toGL]
  exact ⟨g, rfl⟩

theorem concl_duad [Finite A]
    {S M₀ R M V : Subgroup A} (hSs : IsSporadic .M22 ↥S) (hcS : Subgroup.center ↥S = ⊥)
    (hM₀S : M₀ ≤ S) (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hRM : R ≤ M)
    (hcomm : ⁅V, M₀⁆ = V) (ι : G₀ →* A) (hι : Function.Injective ι)
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
  have hgen : ∀ j < 2, ∃ hN : ι (elt (duadGenW.getD j [])) ∈ eNorm hvA,
      eMat hvA ⟨_, hN⟩ = matOf duadMasks j := fun j hj => by
    have hconj := conj_map (fun i => conj_duad hj i) ι
    exact ⟨mem_eNorm hvA _ hconj, eMat_eq hvA _ _ hconj⟩
  have hM₀f : M₀ ≤ Duad.f4Stab hvA := by
    rw [hM, Mduad, map_genOf_eq, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨j, hj, rfl⟩ := exists_index_of_mem duadGenW_length hw
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
      obtain ⟨j, hj, rfl⟩ := exists_index_of_mem duadGenW_length hw
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
    sup_inf_centralizer_eq hRN hRC hC (hVR)
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
  have hsp := isSporadic_quot_center hcS hSs
  refine ⟨Or.inl ⟨hsp, Or.inl ?_⟩, Or.inl ⟨2, hpsl, Or.inl ⟨Duad.F4, inferInstance, inferInstance,
    by decide, hsec⟩⟩, ?_⟩
  · rw [hM₀]
    exact isExt_of_mulEquiv (imageModCenterEquiv hM₀S hcS).symm (isE2_of_mulEquiv 4)
      (isPSL_of_mulEquiv 2 2 2) hext
  · refine summand_of_card ?_
    rw [card_eSub]
    norm_num

theorem concl_e8 [Finite A]
    {S M₀ R M V : Subgroup A} (hSs : IsSporadic .M22 ↥S) (hcS : Subgroup.center ↥S = ⊥)
    (hM₀S : M₀ ≤ S) (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hRM : R ≤ M)
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
  have hM₀N : M₀ ≤ eNorm hvA := by
    have h := le_normalizer_of_comm hcomm
    exact h
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
  have hsp := isSporadic_quot_center hcS hSs
  refine ⟨Or.inl ⟨hsp, Or.inr (Or.inr ?_)⟩,
    Or.inr (Or.inl ⟨3, Or.inl rfl, hpsl, Or.inl ⟨1, le_rfl, hsum⟩⟩), ?_⟩
  · rw [hM₀]
    exact isExt_of_mulEquiv (imageModCenterEquiv hM₀S hcS).symm (isE2_of_mulEquiv 3)
      (isPSL_of_mulEquiv 3 2 1) hext
  · refine summand_of_card ?_
    rw [card_eSub]
    norm_num

end CFSG.Quasithin.KGC31.M22

end
