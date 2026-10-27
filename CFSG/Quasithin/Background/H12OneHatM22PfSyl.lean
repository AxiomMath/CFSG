module

public import CFSG.Quasithin.Background.H12OneHatM22PfModel
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H.Mathieu.H12Pf

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu.H12Cert CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}

@[expose] def IsModelPair (ψ : ↥G ≃* ↥L) (θ : W ≃* Multiplicative (Fin 12 → ZMod 2)) : Prop :=
  ∀ (g : ↥G) (w : W), Multiplicative.toAdd (θ (((ψ g : ↥L) : MulAut W) w)) =
    ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (Multiplicative.toAdd (θ w))

@[expose] def glMul (g : GL (Fin 12) (ZMod 2)) :
    Multiplicative (Fin 12 → ZMod 2) ≃* Multiplicative (Fin 12 → ZMod 2) where
  toFun m := Multiplicative.ofAdd
    ((g : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (Multiplicative.toAdd m))
  invFun m := Multiplicative.ofAdd
    (((g⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (Multiplicative.toAdd m))
  left_inv m := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec, ofAdd_toAdd]
  right_inv m := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' a b := by
    simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem toAdd_glMul (g : GL (Fin 12) (ZMod 2)) (m : Multiplicative (Fin 12 → ZMod 2)) :
    Multiplicative.toAdd (glMul g m) =
      (g : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (Multiplicative.toAdd m) := rfl

theorem isModelPair_conj {ψ : ↥G ≃* ↥L} {θ : W ≃* Multiplicative (Fin 12 → ZMod 2)}
    (h : IsModelPair ψ θ) (g : ↥G) :
    IsModelPair ((MulAut.conj g).trans ψ)
      (θ.trans (glMul ((g⁻¹ : ↥G) : GL (Fin 12) (ZMod 2)))) := by
  intro t w
  show (((g⁻¹ : ↥G) : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (Multiplicative.toAdd (θ (((ψ (MulAut.conj g t) : ↥L) : MulAut W) w))) =
    ((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      ((((g⁻¹ : ↥G) : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (Multiplicative.toAdd (θ w)))
  have key : ((g⁻¹ : ↥G) : GL (Fin 12) (ZMod 2)) * ((MulAut.conj g t : ↥G) : GL (Fin 12) (ZMod 2)) =
      (t : GL (Fin 12) (ZMod 2)) * ((g⁻¹ : ↥G) : GL (Fin 12) (ZMod 2)) := by
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, key]

theorem card_inf_eq {X S : Subgroup (MulAut W)} [Finite W] (hLX : L ≤ X)
    (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut W))) (hS : IsSylowTwoOf S X)
    (hXLS : X = L ⊔ S) (hcardL : Nat.card L = 1330560) : Nat.card ↥(S ⊓ L) = 128 := by
  have hSX : S ≤ X := hS.1
  set S' := S.subgroupOf X with hS'
  set L' := L.subgroupOf X with hL'
  have hN : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hXN
  have htop : S' ⊔ L' = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hSX,
      Subgroup.map_subgroupOf_eq_of_le hLX, sup_comm, ← hXLS, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have h1 := Subgroup.relIndex_sup_right S' L'
  rw [htop] at h1
  have h2 := Subgroup.relIndex_mul_card L' (⊤ : Subgroup ↥X)
  have h3 := Subgroup.relIndex_mul_card L' S'
  rw [inf_top_eq, Subgroup.card_top, h1] at h2
  have hcS' : Nat.card S' = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv
  have hcL' : Nat.card L' = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv
  have hcI : Nat.card ↥(L' ⊓ S') = Nat.card ↥(S ⊓ L) := by
    have : L' ⊓ S' = (S ⊓ L).subgroupOf X := by
      rw [hL', hS', inf_comm]
      rfl
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hSX)).toEquiv
  rw [hcL'] at h2
  rw [hcI, hcS'] at h3
  have hprod : Nat.card ↥X * Nat.card ↥(S ⊓ L) = Nat.card S * Nat.card L := by
    rw [← h2, ← h3]
    ring
  have hidx := S'.card_mul_index
  rw [hcS'] at hidx
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hiL : S'.index * Nat.card ↥(S ⊓ L) = 1330560 := by
    rw [← hcardL]
    apply Nat.eq_of_mul_eq_mul_left hSpos
    rw [← mul_assoc, hidx, hprod]
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (hS.2.1.to_le inf_le_left)
  rw [hk] at hiL
  have hodd : Nat.Coprime 2 S'.index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hS.2.2
  have hk7 : k ≤ 7 := by
    have hdvd : 2 ^ k ∣ 2 ^ 7 * 10395 :=
      ⟨S'.index, by rw [mul_comm (2 ^ k), hiL]; norm_num⟩
    have := (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 10395)).dvd_of_dvd_mul_right
      hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hk7' : 7 ≤ k := by
    have hdvd : 2 ^ 7 ∣ S'.index * 2 ^ k := ⟨10395, by rw [hiL]; norm_num⟩
    have := (Nat.Coprime.pow_left 7 hodd).dvd_of_dvd_mul_left hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  rw [hk, show k = 7 by omega]
  norm_num

theorem exists_isModelPair_T0 {ψ : ↥G ≃* ↥L}
    {θ : W ≃* Multiplicative (Fin 12 → ZMod 2)} (h : IsModelPair ψ θ) {T : Subgroup (MulAut W)}
    (hTL : T ≤ L) (hcard : Nat.card T = 128) :
    ∃ (ψ' : ↥G ≃* ↥L) (θ' : W ≃* Multiplicative (Fin 12 → ZMod 2)), IsModelPair ψ' θ' ∧
      ∀ t : ↥G, ((ψ' t : ↥L) : MulAut W) ∈ T ↔ (t : GL (Fin 12) (ZMod 2)) ∈ T0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T' : Subgroup ↥G := (T.subgroupOf L).map ψ.symm.toMonoidHom with hT'
  set T₀' : Subgroup ↥G := T0.subgroupOf G with hT₀'
  have hT'card : Nat.card T' = 128 := by
    rw [hT', Subgroup.card_map_of_injective ψ.symm.injective, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
  have hT₀'card : Nat.card T₀' = 128 := by
    rw [hT₀', ← card_T0]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe T0_le_G).toEquiv
  have hidx : ∀ P : Subgroup ↥G, Nat.card P = 128 → ¬ 2 ∣ P.index := by
    intro P hP h2
    have := P.card_mul_index
    rw [hP, card_G] at this
    omega
  have hp : ∀ P : Subgroup ↥G, Nat.card P = 128 → IsPGroup 2 P := fun P hP =>
    IsPGroup.of_card (n := 7) (by rw [hP]; norm_num)
  obtain ⟨P₁, hP₁⟩ : ∃ P : Sylow 2 ↥G, (P : Subgroup ↥G) = T' :=
    ⟨_, IsPGroup.toSylow_coe (hp T' hT'card) (hidx T' hT'card)⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P : Sylow 2 ↥G, (P : Subgroup ↥G) = T₀' :=
    ⟨_, IsPGroup.toSylow_coe (hp T₀' hT₀'card) (hidx T₀' hT₀'card)⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥G P₂ P₁
  have hgT : ∀ t : ↥G, g * t * g⁻¹ ∈ T' ↔ t ∈ T₀' := by
    intro t
    have h3 := Sylow.coe_subgroup_smul (g := g) (P := P₂)
    rw [hg, hP₁, hP₂] at h3
    rw [h3, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, mul_assoc]
  refine ⟨(MulAut.conj g).trans ψ, θ.trans (glMul ((g⁻¹ : ↥G) : GL (Fin 12) (ZMod 2))),
    isModelPair_conj h g, fun t => ?_⟩
  have h1 : (t : GL (Fin 12) (ZMod 2)) ∈ T0 ↔ t ∈ T₀' := Subgroup.mem_subgroupOf.symm
  rw [h1, ← hgT, hT', Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf]
  rfl

@[expose] def toL (ψ : ↥G ≃* ↥L) (R : Subgroup (GL (Fin 12) (ZMod 2))) : Subgroup (MulAut W) :=
  ((R.subgroupOf G).map ψ.toMonoidHom).map L.subtype

@[expose] def fromL (ψ : ↥G ≃* ↥L) (R' : Subgroup (MulAut W)) :
    Subgroup (GL (Fin 12) (ZMod 2)) :=
  ((R'.subgroupOf L).map ψ.symm.toMonoidHom).map G.subtype

theorem mem_toL {ψ : ↥G ≃* ↥L} {R : Subgroup (GL (Fin 12) (ZMod 2))} {x : MulAut W} :
    x ∈ toL ψ R ↔ ∃ g : ↥G, (g : GL (Fin 12) (ZMod 2)) ∈ R ∧ ((ψ g : ↥L) : MulAut W) = x := by
  simp only [toL, Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩

theorem mem_fromL {ψ : ↥G ≃* ↥L} {R' : Subgroup (MulAut W)} {g : GL (Fin 12) (ZMod 2)} :
    g ∈ fromL ψ R' ↔ ∃ h : g ∈ G, ((ψ ⟨g, h⟩ : ↥L) : MulAut W) ∈ R' := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    refine ⟨g'.2, ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulEquiv.symm_symm,
      Subgroup.mem_subgroupOf] at hg'
    exact hg'
  · rintro ⟨h, hg⟩
    refine ⟨⟨g, h⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf]
    exact hg

theorem toL_le (ψ : ↥G ≃* ↥L) (R : Subgroup (GL (Fin 12) (ZMod 2))) : toL ψ R ≤ L := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem fromL_le (ψ : ↥G ≃* ↥L) (R' : Subgroup (MulAut W)) : fromL ψ R' ≤ G := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem card_toL (ψ : ↥G ≃* ↥L) {R : Subgroup (GL (Fin 12) (ZMod 2))} (hR : R ≤ G) :
    Nat.card (toL ψ R) = Nat.card R := by
  rw [toL, Subgroup.card_map_of_injective L.subtype_injective,
    Subgroup.card_map_of_injective ψ.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv

theorem card_fromL (ψ : ↥G ≃* ↥L) {R' : Subgroup (MulAut W)} (hR' : R' ≤ L) :
    Nat.card (fromL ψ R') = Nat.card R' := by
  rw [fromL, Subgroup.card_map_of_injective G.subtype_injective,
    Subgroup.card_map_of_injective ψ.symm.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR').toEquiv

theorem toL_fromL (ψ : ↥G ≃* ↥L) {R' : Subgroup (MulAut W)} (hR' : R' ≤ L) :
    toL ψ (fromL ψ R') = R' := by
  ext x
  rw [mem_toL]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨h, hx⟩ := mem_fromL.mp hg
    exact hx
  · intro hx
    obtain ⟨g, hg⟩ := ψ.surjective ⟨x, hR' hx⟩
    refine ⟨g, mem_fromL.mpr ⟨g.2, ?_⟩, by rw [hg]⟩
    have : (⟨(g : GL (Fin 12) (ZMod 2)), g.2⟩ : ↥G) = g := rfl
    rw [this, hg]
    exact hx

end CFSG.Quasithin.H.Mathieu.H12Pf
