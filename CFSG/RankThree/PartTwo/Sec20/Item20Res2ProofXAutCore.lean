module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSL3

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.T75N

variable {G : Type} [Group G]

structure NatData (G : Type) [Group G] (K V : Subgroup G) (F : Type) [Field F] : Type where
  α : ↥K →* SpecialLinearGroup (Fin 3) F
  surj : Function.Surjective α
  ker : α.ker = V.subgroupOf K
  β : ↥V ≃* Multiplicative (Fin 3 → F)
  equiv : ∀ (k : ↥K) (v w : ↥V), (w : G) = k * v * (k : G)⁻¹ →
    Multiplicative.toAdd (β w) = (α k : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β v)

namespace NatData

variable {K V : Subgroup G} {F : Type} [Field F]

noncomputable abbrev vec (d : NatData G K V F) (v : ↥V) : Fin 3 → F := Multiplicative.toAdd (d.β v)

theorem vec_mul (d : NatData G K V F) (v w : ↥V) : d.vec (v * w) = d.vec v + d.vec w := by
  simp [vec, map_mul, toAdd_mul]

theorem vec_injective (d : NatData G K V F) : Function.Injective d.vec := fun _ _ h =>
  d.β.injective (Multiplicative.toAdd.injective h)

theorem vec_surjective (d : NatData G K V F) : Function.Surjective d.vec := fun x =>
  ⟨d.β.symm (Multiplicative.ofAdd x), by simp [vec]⟩

theorem vec_one (d : NatData G K V F) : d.vec 1 = 0 := by simp [vec]

theorem vec_inv (d : NatData G K V F) (v : ↥V) : d.vec v⁻¹ = - d.vec v := by
  have := d.vec_mul v⁻¹ v
  rw [inv_mul_cancel, d.vec_one] at this
  exact eq_neg_of_add_eq_zero_left this.symm

theorem le_normalizer (d : NatData G K V F) (hVK : V ≤ K) :
    K ≤ Subgroup.normalizer (V : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    have hv' : (⟨v, hVK hv⟩ : ↥K) ∈ d.α.ker := by
      rw [d.ker]
      exact hv
    have : (⟨k, hk⟩ * ⟨v, hVK hv⟩ * (⟨k, hk⟩ : ↥K)⁻¹ : ↥K) ∈ d.α.ker := by
      rw [MonoidHom.mem_ker] at hv' ⊢
      rw [map_mul, map_mul, hv', mul_one, map_inv, mul_inv_cancel]
    rw [d.ker, Subgroup.mem_subgroupOf] at this
    simpa using this
  · intro hv
    have hvK : v ∈ K := by
      have : v = k⁻¹ * (k * v * k⁻¹) * k := by group
      rw [this]
      exact K.mul_mem (K.mul_mem (K.inv_mem hk) (hVK hv)) hk
    have hv' : (⟨k * v * k⁻¹, hVK hv⟩ : ↥K) ∈ d.α.ker := by
      rw [d.ker]
      exact hv
    have : ((⟨k, hk⟩ : ↥K)⁻¹ * ⟨k * v * k⁻¹, hVK hv⟩ * ⟨k, hk⟩ : ↥K) ∈ d.α.ker := by
      rw [MonoidHom.mem_ker] at hv' ⊢
      rw [map_mul, map_mul, hv', mul_one, map_inv, inv_mul_cancel]
    rw [d.ker, Subgroup.mem_subgroupOf] at this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rwa [show k⁻¹ * (k * v * k⁻¹) * k = v by group] at this

theorem mem_of_forall_commute (d : NatData G K V F) {k : G} (hk : k ∈ K)
    (hkV : ∀ v ∈ V, k * v * k⁻¹ = v) : k ∈ V := by
  have h1 : d.α ⟨k, hk⟩ = 1 := by
    apply eq_one_of_forall_mulVec_eq
    intro x
    obtain ⟨v, rfl⟩ := d.vec_surjective x
    have h := d.equiv ⟨k, hk⟩ v v (hkV v v.2).symm
    exact h.symm
  have : (⟨k, hk⟩ : ↥K) ∈ d.α.ker := h1
  rw [d.ker, Subgroup.mem_subgroupOf] at this
  exact this

theorem card_V (d : NatData G K V F) [Fintype F] : Nat.card V = Fintype.card F ^ 3 := by
  rw [Nat.card_congr d.β.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_fin]

theorem isPGroup_V (d : NatData G K V F) [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n) :
    IsPGroup 2 V := by
  refine IsPGroup.of_card (n := n * 3) ?_
  rw [d.card_V, hF, pow_mul]

end NatData

variable {K V : Subgroup G} {F : Type} [Field F]

structure XData (d : NatData G K V F) (X : Subgroup G) : Prop where
  V_le : V ≤ X
  le_K : X ≤ K
  image_le : (X.subgroupOf K).map d.α ≤ vstab F
  irred : IrredModE0 F ((X.subgroupOf K).map d.α)
  urad_le : urad F ≤ (X.subgroupOf K).map d.α

variable {d : NatData G K V F} {X : Subgroup G}

theorem XData.pCoreOf_le_K (hX : XData d X) : CFSG.Open.pCoreOf 2 X ≤ K :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hX.le_K

theorem XData.V_le_pCoreOf [Finite G] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    (hX : XData d X) : V ≤ CFSG.Open.pCoreOf 2 X :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hX.V_le
    (hX.le_K.trans (d.le_normalizer (hX.V_le.trans hX.le_K))) (d.isPGroup_V hF)

theorem XData.image_pCoreOf_le_urad [Finite G] [Fintype F] [CharP F 2] (hX : XData d X)
    {q : G} (hq : q ∈ CFSG.Open.pCoreOf 2 X) : d.α ⟨q, hX.pCoreOf_le_K hq⟩ ∈ urad F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := ((CFSG.Open.pCoreOf 2 X).subgroupOf K).map d.α with hR
  have hR2 : IsPGroup 2 R :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).comap_subtype (K := K)).map _ |>.of_equiv
      (MulEquiv.refl _)
  have hnorm : (X.subgroupOf K).map d.α ≤
      Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin 3) F)) := by
    rintro _ ⟨x, hx, rfl⟩
    apply Sec20.mem_normalizer_of_map_conj_le
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    refine ⟨x * r * x⁻¹, ?_, by simp⟩
    have hx' : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hr' : (r : G) ∈ CFSG.Open.pCoreOf 2 X := Subgroup.mem_subgroupOf.mp hr
    refine Subgroup.mem_subgroupOf.mpr ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx') _).mp hr'
  exact le_urad_of_isPGroup hX.image_le hX.irred hR2 hnorm
    ⟨⟨q, hX.pCoreOf_le_K hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩

theorem XData.exists_mem_pCoreOf_of_mem_urad [Finite G] [Fintype F] [CharP F 2] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) (hX : XData d X) {u : SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ urad F) :
    ∃ (q : G) (hq : q ∈ CFSG.Open.pCoreOf 2 X), d.α ⟨q, hX.pCoreOf_le_K hq⟩ = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Qt : Subgroup G := X ⊓ (((urad F).comap d.α).map K.subtype) with hQt
  have hQtX : Qt ≤ X := inf_le_left
  have hmemQt : ∀ x (hx : x ∈ X), x ∈ Qt ↔ d.α ⟨x, hX.le_K hx⟩ ∈ urad F := by
    intro x hx
    constructor
    · rintro ⟨-, ⟨k, hk, rfl⟩⟩
      exact hk
    · intro h
      exact ⟨hx, ⟨⟨x, hX.le_K hx⟩, h, rfl⟩⟩
  have hQt2 : IsPGroup 2 Qt := by
    intro ⟨x, hx⟩
    have hxX := hQtX hx
    have hxu := (hmemQt x hxX).mp hx
    have hsq : d.α (⟨x, hX.le_K hxX⟩ ^ 2) = 1 := by
      rw [map_pow]
      exact sq_eq_one_of_mem_urad hxu
    have hx2V : x ^ 2 ∈ V := by
      have : (⟨x, hX.le_K hxX⟩ ^ 2 : ↥K) ∈ d.α.ker := hsq
      rw [d.ker, Subgroup.mem_subgroupOf] at this
      simpa using this
    obtain ⟨k, hk⟩ := d.isPGroup_V hF ⟨x ^ 2, hx2V⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : (x ^ 2) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_succ, pow_mul', hk']
  have hXQt : X ≤ Subgroup.normalizer (Qt : Set G) := by
    intro x hx
    apply Sec20.mem_normalizer_of_map_conj_le
    rintro _ ⟨q, hq, rfl⟩
    have hqX := hQtX hq
    have hxqX : x * q * x⁻¹ ∈ X := X.mul_mem (X.mul_mem hx hqX) (X.inv_mem hx)
    show x * q * x⁻¹ ∈ Qt
    rw [hmemQt _ hxqX]
    have hxv : d.α ⟨x, hX.le_K hx⟩ ∈ vstab F :=
      hX.image_le ⟨⟨x, hX.le_K hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have := conj_mem_urad (vstab_le_lstab hxv) ((hmemQt q hqX).mp hq)
    have he : d.α ⟨x * q * x⁻¹, hX.le_K hxqX⟩ =
        d.α ⟨x, hX.le_K hx⟩ * d.α ⟨q, hX.le_K hqX⟩ * (d.α ⟨x, hX.le_K hx⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [he]
    exact this
  have hQtQ : Qt ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQtX hXQt hQt2
  obtain ⟨⟨x, hxK⟩, hx, hxu⟩ := hX.urad_le hu
  have hxX : x ∈ X := Subgroup.mem_subgroupOf.mp hx
  refine ⟨x, hQtQ ((hmemQt x hxX).mpr ?_), hxu⟩
  rw [show (⟨x, hX.le_K hxX⟩ : ↥K) = ⟨x, hxK⟩ from rfl, hxu]
  exact hu

noncomputable abbrev zQ (X : Subgroup G) : Subgroup G :=
  CFSG.Open.pCoreOf 2 X ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G)

theorem forall_urad_mulVec_eq_iff (x : Fin 3 → F) :
    (∀ u ∈ urad F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) ↔ x 1 = 0 ∧ x 2 = 0 := by
  constructor
  · intro h
    have h1 := h (uelt (Pi.single 1 1) (by simp)) (uelt_mem _ _)
    have h2 := h (uelt (Pi.single 2 1) (by simp)) (uelt_mem _ _)
    rw [coe_rowSL, rowMat_zero_mulVec, add_eq_left, smul_eq_zero] at h1 h2
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact ⟨by simpa [single_dotProduct] using h1, by simpa [single_dotProduct] using h2⟩
      · simp at h2
    · simp at h1
  · rintro ⟨h1, h2⟩ u hu
    rw [eq_smul_e0 h1 h2, mulVec_smul, (mem_urad_iff.mp hu).1]

theorem XData.mem_zQ_iff [Finite G] [Fintype F] [CharP F 2] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) (hX : XData d X) (v : ↥V) :
    (v : G) ∈ zQ X ↔ d.vec v 1 = 0 ∧ d.vec v 2 = 0 := by
  have hVQ := hX.V_le_pCoreOf hF
  have hVK : V ≤ K := hX.V_le.trans hX.le_K
  rw [← forall_urad_mulVec_eq_iff]
  constructor
  · rintro ⟨-, hv⟩ u hu
    obtain ⟨q, hq, rfl⟩ := hX.exists_mem_pCoreOf_of_mem_urad hF hu
    have hc : q * v * q⁻¹ = v := by
      rw [Subgroup.mem_centralizer_iff.mp hv q hq]
      group
    exact (d.equiv ⟨q, hX.pCoreOf_le_K hq⟩ v v hc.symm).symm
  · intro h
    refine ⟨hVQ v.2, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have hqK := hX.pCoreOf_le_K hq
    have hw : q * v * q⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (d.le_normalizer hVK hqK) v).mp v.2
    have h1 := d.equiv ⟨q, hqK⟩ v ⟨_, hw⟩ rfl
    rw [h _ (hX.image_pCoreOf_le_urad hq)] at h1
    have h2 : (⟨q * v * q⁻¹, hw⟩ : ↥V) = v := d.vec_injective h1
    have h3 : q * v * q⁻¹ = v := congrArg Subtype.val h2
    calc q * (v : G) = q * v * q⁻¹ * q := by group
      _ = v * q := by rw [h3]

theorem XData.zQ_le [Finite G] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    (hX : XData d X) : zQ X ≤ V := by
  rintro z ⟨hzQ, hz⟩
  refine d.mem_of_forall_commute (hX.pCoreOf_le_K hzQ) fun v hv => ?_
  rw [← Subgroup.mem_centralizer_iff.mp hz v (hX.V_le_pCoreOf hF hv)]
  group

theorem XData.eq_or_eq_of_invariant [Finite G] [Fintype F] [CharP F 2] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) (hX : XData d X) {R : Subgroup G} (hZR : zQ X ≤ R)
    (hRV : R ≤ V) (hXR : X ≤ Subgroup.normalizer (R : Set G)) : R = zQ X ∨ R = V := by
  have hVK : V ≤ K := hX.V_le.trans hX.le_K
  let S : AddSubgroup (Fin 3 → F) :=
    { carrier := {x | ∃ v : ↥V, (v : G) ∈ R ∧ d.vec v = x}
      zero_mem' := ⟨1, R.one_mem, d.vec_one⟩
      add_mem' := by
        rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
        exact ⟨v * w, R.mul_mem hv hw, d.vec_mul v w⟩
      neg_mem' := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨v⁻¹, R.inv_mem hv, d.vec_inv v⟩ }
  have hS : ∀ k ∈ (X.subgroupOf K).map d.α, ∀ w ∈ S, (k : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ S := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨v, hv, rfl⟩
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hw : (x : G) * v * (x : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (d.le_normalizer hVK x.2) v).mp v.2
    refine ⟨⟨_, hw⟩, (Subgroup.mem_normalizer_iff.mp (hXR hxX) v).mp hv, ?_⟩
    exact d.equiv x v ⟨_, hw⟩ rfl
  by_cases hoff : ∃ u ∈ S, u 1 ≠ 0 ∨ u 2 ≠ 0
  · right
    obtain ⟨u, hu, hu'⟩ := hoff
    have htop := hX.irred S hS u hu hu'
    refine le_antisymm hRV fun v hv => ?_
    have : d.vec ⟨v, hv⟩ ∈ S := htop ▸ AddSubgroup.mem_top _
    obtain ⟨w, hwR, hw⟩ := this
    have h' : (w : G) = v := congrArg Subtype.val (d.vec_injective hw)
    rw [← h']
    exact hwR
  · left
    push Not at hoff
    refine le_antisymm (fun v hv => ?_) hZR
    have := hoff (d.vec ⟨v, hRV hv⟩) ⟨⟨v, hRV hv⟩, hv, rfl⟩
    exact (hX.mem_zQ_iff hF ⟨v, hRV hv⟩).mpr this

theorem XData.commutator_le [Finite G] [Fintype F] [CharP F 2] (hX : XData d X) :
    ⁅CFSG.Open.pCoreOf 2 X, CFSG.Open.pCoreOf 2 X⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haK := hX.pCoreOf_le_K ha
  have hbK := hX.pCoreOf_le_K hb
  have hcomm : d.α ⟨a, haK⟩ * d.α ⟨b, hbK⟩ = d.α ⟨b, hbK⟩ * d.α ⟨a, haK⟩ := by
    obtain ⟨x, hx0, hx⟩ := exists_eq_uelt (hX.image_pCoreOf_le_urad ha)
    obtain ⟨y, hy0, hy⟩ := exists_eq_uelt (hX.image_pCoreOf_le_urad hb)
    rw [hx, hy, uelt_mul, uelt_mul]
    congr 1
    exact add_comm x y
  have hker : (⟨a, haK⟩ * ⟨b, hbK⟩ * (⟨a, haK⟩ : ↥K)⁻¹ * (⟨b, hbK⟩ : ↥K)⁻¹ : ↥K) ∈ d.α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, hcomm, map_inv, map_inv]
    group
  rw [d.ker, Subgroup.mem_subgroupOf] at hker
  simpa [commutatorElement_def] using hker

end CFSG.RankThree.PartTwo.Sec20.Res2
