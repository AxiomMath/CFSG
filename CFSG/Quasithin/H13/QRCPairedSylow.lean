module

public import CFSG.Quasithin.H13.QRCPairedCoord
public import CFSG.Quasithin.H13.QRCBenderAmbient

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField CFSG.GorensteinWalter
  CFSG.Glauberman.Dickson CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups

variable {A : Type*} [Group A] {k : Type} [Field k]

theorem isPGroup_of_complement {K S R : Subgroup A} [K.Normal] (hKS : K ⊔ S = ⊤)
    (hS : IsPGroup 2 S) (hKR : K ⊓ R = ⊥) : IsPGroup 2 R := by
  rintro ⟨r, hr⟩
  have hrKS : r ∈ K ⊔ S := hKS ▸ mem_top r
  rw [← SetLike.mem_coe, normal_mul K S] at hrKS
  obtain ⟨x, hx, s, hs, rfl⟩ := hrKS
  obtain ⟨m, hm⟩ := hS ⟨s, hs⟩
  have hsm : s ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have h1 : (x * s) ^ 2 ^ m ∈ K := by
    have h2 : (QuotientGroup.mk (x * s) : A ⧸ K) ^ 2 ^ m = 1 := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff x).2 hx, one_mul,
        ← QuotientGroup.mk_pow, hsm, QuotientGroup.mk_one]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
    exact h2
  have h3 : (x * s) ^ 2 ^ m ∈ K ⊓ R := ⟨h1, R.pow_mem hr _⟩
  rw [hKR, mem_bot] at h3
  exact ⟨m, Subtype.ext (by simpa using h3)⟩

variable {K₁ K₂ : Subgroup A}

theorem IsFieldPerm.map_stdSub_le {θ₁ : K₁ ≃* SL(2, k)} {θ₂ : K₂ ≃* SL(2, k)} {r : A}
    (hr : IsFieldPerm θ₁ θ₂ r) {Z : Subgroup SL(2, k)}
    (hZ : ∀ σ : RingAut k, ∀ g ∈ Z, Matrix.SpecialLinearGroup.map σ.toRingHom g ∈ Z) {x : A}
    (hx : x ∈ stdSub θ₁ Z ⊔ stdSub θ₂ Z) : r * x * r⁻¹ ∈ stdSub θ₁ Z ⊔ stdSub θ₂ Z := by
  have key : (stdSub θ₁ Z ⊔ stdSub θ₂ Z).map (MulAut.conj r).toMonoidHom ≤
      stdSub θ₁ Z ⊔ stdSub θ₂ Z := by
    rw [Subgroup.map_sup]
    obtain ⟨σ₁, σ₂, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := hr
    · refine sup_le ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact mem_sup_left (h₁.conj_mem_stdSub (hZ σ₁) hy)
      · rintro _ ⟨y, hy, rfl⟩
        exact mem_sup_right (h₂.conj_mem_stdSub (hZ σ₂) hy)
    · refine sup_le ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact mem_sup_right (h₁.conj_mem_stdSub (hZ σ₁) hy)
      · rintro _ ⟨y, hy, rfl⟩
        exact mem_sup_left (h₂.conj_mem_stdSub (hZ σ₂) hy)
  exact key ⟨x, hx, rfl⟩

theorem fieldPerm_le_normalizer {θ₁ : K₁ ≃* SL(2, k)} {θ₂ : K₂ ≃* SL(2, k)} {R : Subgroup A}
    (hR : ∀ r ∈ R, IsFieldPerm θ₁ θ₂ r) {Z : Subgroup SL(2, k)}
    (hZ : ∀ σ : RingAut k, ∀ g ∈ Z, Matrix.SpecialLinearGroup.map σ.toRingHom g ∈ Z) :
    R ≤ normalizer ((stdSub θ₁ Z ⊔ stdSub θ₂ Z : Subgroup A) : Set A) := by
  intro r hr
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => (hR r hr).map_stdSub_le hZ hy, fun hy => ?_⟩
  have h1 := (hR r⁻¹ (R.inv_mem hr)).map_stdSub_le hZ hy
  rwa [show r⁻¹ * (r * y * r⁻¹) * r⁻¹⁻¹ = y by group] at h1

theorem upperUnipotent_fieldStable (σ : RingAut k) (g : SL(2, k))
    (hg : g ∈ sl2UpperUnipotentSubgroup k) :
    Matrix.SpecialLinearGroup.map σ.toRingHom g ∈ sl2UpperUnipotentSubgroup k :=
  sl2_map_mem_upperUnipotent σ hg

theorem torus_fieldStable (σ : RingAut k) (g : SL(2, k)) (hg : g ∈ (splitTorusSLHom k).range) :
    Matrix.SpecialLinearGroup.map σ.toRingHom g ∈ (splitTorusSLHom k).range := by
  obtain ⟨a, rfl⟩ := hg
  exact ⟨_, (sl2_map_splitTorus σ a).symm⟩

theorem borel_fieldStable [CharP k 2] (σ : RingAut k) (g : SL(2, k)) (hg : g ∈ sl2Borel k) :
    Matrix.SpecialLinearGroup.map σ.toRingHom g ∈ sl2Borel k := by
  rw [← sl2_upperUnipotent_sup_torus] at hg ⊢
  have h1 : (sl2UpperUnipotentSubgroup k ⊔ (splitTorusSLHom k).range).map
      (Matrix.SpecialLinearGroup.map σ.toRingHom) ≤
        sl2UpperUnipotentSubgroup k ⊔ (splitTorusSLHom k).range := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact upperUnipotent_fieldStable σ y hy
    · rintro _ ⟨y, hy, rfl⟩
      exact torus_fieldStable σ y hy
  exact h1 ⟨g, hg, rfl⟩

theorem stdSub_conj {X : Subgroup A} (θ : X ≃* SL(2, k)) (Z : Subgroup SL(2, k)) {c : A}
    (hX : X.map (MulAut.conj c⁻¹).toMonoidHom = X) :
    stdSub ((conjEquiv c⁻¹ hX).trans θ) Z = (stdSub θ Z).map (MulAut.conj c).toMonoidHom := by
  ext x
  rw [mem_stdSub]
  constructor
  · rintro ⟨hx, hxZ⟩
    have hmem : c⁻¹ * x * c⁻¹⁻¹ ∈ X := by
      rw [← hX]
      exact ⟨x, hx, rfl⟩
    refine ⟨c⁻¹ * x * c⁻¹⁻¹, mem_stdSub.2 ⟨hmem, ?_⟩, ?_⟩
    · exact hxZ
    · change c * (c⁻¹ * x * c⁻¹⁻¹) * c⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyX, hyZ⟩ := mem_stdSub.1 hy
    have hmem : c * y * c⁻¹ ∈ X := by
      have h1 : X.map (MulAut.conj c).toMonoidHom = X := by
        conv_lhs => rw [← hX]
        rw [← map_conj_mul, mul_inv_cancel]
        have : (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A := by
          ext y
          simp
        rw [this, map_id]
      rw [← h1]
      exact ⟨y, hyX, rfl⟩
    refine ⟨hmem, ?_⟩
    change θ (conjEquiv c⁻¹ hX ⟨c * y * c⁻¹, hmem⟩) ∈ Z
    have : conjEquiv c⁻¹ hX ⟨c * y * c⁻¹, hmem⟩ = ⟨y, hyX⟩ :=
      Subtype.ext (by rw [coe_conjEquiv]; group)
    rw [this]
    exact hyZ

section Sylow

open CFSG.ABGLocalTools

variable [Finite A] {n : ℕ}

omit [Finite A] in
theorem card_stdSub {X : Subgroup A} (θ : X ≃* SL(2, k)) (Z : Subgroup SL(2, k)) :
    Nat.card (stdSub θ Z) = Nat.card Z := by
  rw [stdSub, card_map_of_injective X.subtype_injective,
    card_map_of_injective (f := θ.symm.toMonoidHom) θ.symm.injective]

omit [Finite A] in
theorem isPGroup_stdSub_upperUnipotent [CharP k 2] [Finite k] (hk : Nat.card k = 2 ^ n)
    {X : Subgroup A} (θ : X ≃* SL(2, k)) : IsPGroup 2 (stdSub θ (sl2UpperUnipotentSubgroup k)) :=
  ((benderData_sl2 hk).isPGroup.map θ.symm.toMonoidHom).map X.subtype

theorem exists_fieldPerm_coords [CharP k 2] [Finite k] (hk : Nat.card k = 2 ^ n) (hn : 2 ≤ n)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥) (hKn : (K₁ ⊔ K₂).Normal)
    (S : Sylow 2 A) (hKS : K₁ ⊔ K₂ ⊔ (S : Subgroup A) = ⊤) (θ₁ : K₁ ≃* SL(2, k))
    (θ₂ : K₂ ≃* SL(2, k)) (hsw : ∃ a : A, K₁.map (MulAut.conj a).toMonoidHom = K₂) :
    ∃ (θ₁' : K₁ ≃* SL(2, k)) (θ₂' : K₂ ≃* SL(2, k)) (R : Subgroup A),
      R ≤ S ∧ IsPGroup 2 R ∧ (K₁ ⊔ K₂) ⊓ R = ⊥ ∧ (K₁ ⊔ K₂) ⊔ R = ⊤ ∧
      (∀ r ∈ R, IsFieldPerm θ₁' θ₂' r) ∧ (∃ r ∈ R, K₁.map (MulAut.conj r).toMonoidHom = K₂) ∧
      (S : Subgroup A) = stdSub θ₁' (sl2UpperUnipotentSubgroup k) ⊔
        stdSub θ₂' (sl2UpperUnipotentSubgroup k) ⊔ R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hKn
  set K := K₁ ⊔ K₂ with hKdef
  set R := fieldPermGroup θ₁ θ₂ with hRdef
  set Ū := sl2UpperUnipotentSubgroup k with hŪ
  set U := stdSub θ₁ Ū ⊔ stdSub θ₂ Ū with hUdef
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hKR : K ⊓ R = ⊥ := sup_inf_fieldPermGroup_eq_bot hk hc hd θ₁ θ₂
  have hKRt : K ⊔ R = ⊤ := sup_sup_fieldPermGroup_eq_top hk hn hc hd hKn θ₁ θ₂
  have hR2 : IsPGroup 2 R := isPGroup_of_complement hKS S.isPGroup' hKR
  have hRU : R ≤ normalizer (U : Set A) :=
    fieldPerm_le_normalizer (fun r hr => hr) upperUnipotent_fieldStable
  have hUK : U ≤ K := sup_le_sup (stdSub_le _ _) (stdSub_le _ _)
  have hcU : ∀ a ∈ stdSub θ₁ Ū, ∀ b ∈ stdSub θ₂ Ū, a * b = b * a := fun a ha b hb =>
    hc a (stdSub_le _ _ ha) b (stdSub_le _ _ hb)
  have hU2 : IsPGroup 2 U :=
    (isPGroup_stdSub_upperUnipotent hk θ₁).to_sup_of_normal_left'
      (isPGroup_stdSub_upperUnipotent hk θ₂) (le_normalizer_of_commute hcU)
  set P := U ⊔ R with hPdef
  have hP2 : IsPGroup 2 P := hU2.to_sup_of_normal_left' hR2 hRU
  have hPK : P ⊓ K = U := by
    refine le_antisymm (fun p hp => ?_) (le_inf le_sup_left hUK)
    obtain ⟨hp1, hp2⟩ := mem_inf.1 hp
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left U R hRU] at hp1
    obtain ⟨u, hu, r, hr, rfl⟩ := hp1
    have hrK : r ∈ K := by
      have := K.mul_mem (K.inv_mem (hUK hu)) hp2
      rwa [inv_mul_cancel_left] at this
    have hr1 : r = 1 := by
      have : r ∈ K ⊓ R := ⟨hrK, hr⟩
      rwa [hKR, mem_bot] at this
    subst hr1
    simpa using hu
  have hKP : K ⊔ P = ⊤ := eq_top_iff.2 (hKRt ▸ sup_le_sup_left le_sup_right K)
  have hcK : Nat.card K = Nat.card Ū * Ū.index * (Nat.card Ū * Ū.index) := by
    rw [card_sup_of_commute hc hd, Nat.card_congr θ₁.toEquiv, Nat.card_congr θ₂.toEquiv,
      card_mul_index]
  have hcUU : Nat.card U = Nat.card Ū * Nat.card Ū := by
    rw [card_sup_of_commute hcU (eq_bot_iff.2 ((inf_le_inf (stdSub_le _ _) (stdSub_le _ _)).trans
      hd.le)), card_stdSub, card_stdSub]
  have hrel : U.relIndex K * Nat.card U = Nat.card K := by
    have := relIndex_mul_card U K
    rwa [inf_eq_left.2 hUK] at this
  have hpos : 0 < Nat.card Ū := Nat.card_pos
  have hidx : U.relIndex K = Ū.index * Ū.index := by
    rw [hcK, hcUU] at hrel
    have h2 : U.relIndex K * (Nat.card Ū * Nat.card Ū) =
        (Ū.index * Ū.index) * (Nat.card Ū * Nat.card Ū) := by
      rw [hrel]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
  have hodd := (benderData_sl2 hk).not_dvd_index
  have hPidx : ¬ 2 ∣ P.index := by
    have h1 : P.relIndex (K ⊔ P) = P.relIndex K := relIndex_sup_eq_relIndex_of_normal K P
    rw [hKP, relIndex_top_right, ← inf_relIndex_right, hPK, hidx] at h1
    rw [h1]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h <;> exact hodd h
  obtain ⟨c, hc''⟩ := MulAction.exists_smul_eq A (hP2.toSylow hPidx) S
  have hSP : (S : Subgroup A) = P.map (MulAut.conj c).toMonoidHom := by
    rw [← hc'']
    ext x
    rw [Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists, IsPGroup.toSylow_coe]
    exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩⟩
  have hcKR : c ∈ K ⊔ R := hKRt ▸ mem_top c
  rw [← SetLike.mem_coe, normal_mul K R] at hcKR
  obtain ⟨g, hg, r, hr, rfl⟩ := hcKR
  have hSP' : (S : Subgroup A) = P.map (MulAut.conj g).toMonoidHom := by
    rw [hSP, map_conj_mul,
      map_conj_eq_of_mem_normalizer' (le_normalizer ((le_sup_right : R ≤ P) hr))]
  have hKN₁ : K ≤ normalizer (K₁ : Set A) := sup_le le_normalizer (le_normalizer_of_commute hc)
  have hKN₂ : K ≤ normalizer (K₂ : Set A) := sup_le (le_normalizer_of_commute hc') le_normalizer
  have hg₁ : K₁.map (MulAut.conj g⁻¹).toMonoidHom = K₁ :=
    map_conj_eq_of_mem_normalizer' (hKN₁ (K.inv_mem hg))
  have hg₂ : K₂.map (MulAut.conj g⁻¹).toMonoidHom = K₂ :=
    map_conj_eq_of_mem_normalizer' (hKN₂ (K.inv_mem hg))
  have hKg : K.map (MulAut.conj g).toMonoidHom = K :=
    map_conj_eq_of_mem_normalizer' (le_normalizer hg)
  refine ⟨(conjEquiv g⁻¹ hg₁).trans θ₁, (conjEquiv g⁻¹ hg₂).trans θ₂,
    R.map (MulAut.conj g).toMonoidHom, ?_, hR2.map _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSP']
    exact map_mono le_sup_right
  · have h1 := congrArg (map (MulAut.conj g).toMonoidHom) hKR
    rwa [map_inf_eq _ _ _ (MulAut.conj g).injective, hKg, Subgroup.map_bot] at h1
  · have h1 := congrArg (map (MulAut.conj g).toMonoidHom) hKRt
    rwa [Subgroup.map_sup, hKg, map_top_of_surjective _ (MulAut.conj g).surjective] at h1
  · rintro _ ⟨r, ⟨σ₁, σ₂, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩, rfl⟩
    · exact ⟨σ₁, σ₂, Or.inl ⟨h₁.conj hg₁ hg₁, h₂.conj hg₂ hg₂⟩⟩
    · exact ⟨σ₁, σ₂, Or.inr ⟨h₁.conj hg₁ hg₂, h₂.conj hg₂ hg₁⟩⟩
  · obtain ⟨a, ha⟩ := hsw
    have haKR : a ∈ K ⊔ R := hKRt ▸ mem_top a
    rw [← SetLike.mem_coe, normal_mul K R] at haKR
    obtain ⟨g', hg', r', hr', rfl⟩ := haKR
    have hr'sw : K₁.map (MulAut.conj r').toMonoidHom = K₂ := by
      have h1 : K₁.map (MulAut.conj (g'⁻¹ * (g' * r'))).toMonoidHom = K₂ := by
        rw [map_conj_mul, ha, map_conj_eq_of_mem_normalizer' (hKN₂ (K.inv_mem hg'))]
      rwa [inv_mul_cancel_left] at h1
    refine ⟨(MulAut.conj g).toMonoidHom r', ⟨r', hr', rfl⟩, ?_⟩
    change K₁.map (MulAut.conj (g * r' * g⁻¹)).toMonoidHom = K₂
    rw [map_conj_mul, map_conj_mul, hg₁, hr'sw,
      map_conj_eq_of_mem_normalizer' (hKN₂ hg)]
  · rw [hSP', hPdef, hUdef, Subgroup.map_sup, Subgroup.map_sup, stdSub_conj, stdSub_conj]

end Sylow

end CFSG.Quasithin.H13.QRC
