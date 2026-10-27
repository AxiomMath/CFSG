module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22FChiefA
public import CFSG.Quasithin.Background.D1Statement

public section

namespace CFSG.Quasithin.H13.M22F

open CFSG.Open CFSG.Quasithin

section Trans

variable {G : Type} [Group G] [Finite G]

structure OrdThreeAct_m22f (V X : Subgroup G) (y : G) : Prop where
  hV : IsElemAbelian 2 V
  hyN : y ∈ Subgroup.normalizer (V : Set G)
  hy3 : ∀ v ∈ V, y ^ 3 * v * (y ^ 3)⁻¹ = v
  hyX : y ∈ X
  hX : ∀ g ∈ X, ∃ j : ℕ, ∀ v ∈ V, g * v * g⁻¹ = y ^ j * v * (y ^ j)⁻¹

variable {V X : Subgroup G} {y : G}

theorem OrdThreeAct_m22f.hyV (S : OrdThreeAct_m22f V X y) : ∀ v ∈ V, y * v * y⁻¹ ∈ V :=
  fun v hv => (Subgroup.mem_normalizer_iff.mp S.hyN v).mp hv

theorem isNormalIn_of_yinv_m22f (S : OrdThreeAct_m22f V X y) {M : Subgroup G} (hMV : M ≤ V)
    (hy : ∀ x ∈ M, y * x * y⁻¹ ∈ M) : IsNormalIn X V M := by
  refine ⟨hMV, fun g hg x hx => ?_⟩
  obtain ⟨j, hj⟩ := S.hX g hg
  rw [hj x (hMV hx)]
  clear hj
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    have e : y ^ (j + 1) * x * (y ^ (j + 1))⁻¹ = y * (y ^ j * x * (y ^ j)⁻¹) * y⁻¹ := by group
    rw [e]
    exact hy _ ih

theorem yinv_of_isNormalIn_m22f (S : OrdThreeAct_m22f V X y) {M : Subgroup G} (hM : IsNormalIn X V M) :
    ∀ x ∈ M, y * x * y⁻¹ ∈ M :=
  fun x hx => hM.2 y S.hyX x hx

theorem isCentralStep_iff_m22f (S : OrdThreeAct_m22f V X y) {L N : Subgroup G} (hLN : L ≤ N) (hNV : N ≤ V)
    (hLy : ∀ x ∈ L, y * x * y⁻¹ ∈ L) :
    IsCentralStep X L N ↔ ∀ x ∈ N, y * x * y⁻¹ * x⁻¹ ∈ L := by
  constructor
  · intro h x hx
    have := h y S.hyX x hx
    simpa [mul_assoc] using this
  · intro h g hg x hx
    obtain ⟨j, hj⟩ := S.hX g hg
    rw [hj x (hNV hx)]
    have key : ∀ j : ℕ, y ^ j * x * (y ^ j)⁻¹ * x⁻¹ ∈ L := by
      intro j
      induction j with
      | zero => simpa using L.one_mem
      | succ j ih =>
        have e : y ^ (j + 1) * x * (y ^ (j + 1))⁻¹ * x⁻¹ =
            (y * (y ^ j * x * (y ^ j)⁻¹ * x⁻¹) * y⁻¹) * (y * x * y⁻¹ * x⁻¹) := by group
        rw [e]
        exact L.mul_mem (hLy _ ih) (h x hx)
    exact key j

end Trans

section Abstract

variable {G : Type} [Group G] [Finite G]
variable {V X : Subgroup G} {y : G}

@[expose] def sigmaA_m22f (S : OrdThreeAct_m22f V X y) : ↥V →* ↥V :=
  MonoidHom.mk' (fun a => ⟨y * (a : G) * y⁻¹, S.hyV a a.2⟩) (fun a b => by
    apply Subtype.ext
    show y * ((a : G) * (b : G)) * y⁻¹ = (y * (a : G) * y⁻¹) * (y * (b : G) * y⁻¹)
    group)

theorem sigmaA_coe_m22f (S : OrdThreeAct_m22f V X y) (a : ↥V) : ((sigmaA_m22f S a : ↥V) : G) = y * (a : G) * y⁻¹ := rfl

theorem normalA_subgroupOf_m22f (S : OrdThreeAct_m22f V X y) {M : Subgroup G} (hMV : M ≤ V) :
    @NormalA_m22f ↥V (commGroupOfElemAbelian S.hV) (sigmaA_m22f S) (M.subgroupOf V) ↔
      ∀ x ∈ M, y * x * y⁻¹ ∈ M := by
  letI := commGroupOfElemAbelian S.hV
  constructor
  · intro h x hx
    have h1 := h ⟨x, hMV hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_subgroupOf.mp h1
  · intro h a ha
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    rw [sigmaA_coe_m22f]
    exact h _ ha

theorem conjAct_apply_m22f (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ((conjAct V g v : ↥V) : G) = (g : G) * (v : G) * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

theorem chiefStep_translate_m22f (S : OrdThreeAct_m22f V X y) {L N : Subgroup G}
    (h : IsChiefStep X V L N) :
    @ChiefStepA_m22f ↥V (commGroupOfElemAbelian S.hV) (sigmaA_m22f S) (L.subgroupOf V) (N.subgroupOf V) := by
  letI := commGroupOfElemAbelian S.hV
  obtain ⟨hN, hL, hLN, hmax⟩ := h
  have hNV : N ≤ V := hN.1
  have hLV : L ≤ V := hL.1
  refine ⟨(normalA_subgroupOf_m22f S hNV).2 (yinv_of_isNormalIn_m22f S hN),
    (normalA_subgroupOf_m22f S hLV).2 (yinv_of_isNormalIn_m22f S hL), ?_, ?_⟩
  · refine lt_of_le_of_ne ?_ ?_
    · intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hLN.le (Subgroup.mem_subgroupOf.mp hx))
    · intro heq
      apply hLN.ne
      have h1 := congrArg (fun K : Subgroup ↥V => K.map V.subtype) heq
      simp only [Subgroup.subgroupOf_map_subtype] at h1
      rw [inf_eq_left.mpr hLV, inf_eq_left.mpr hNV] at h1
      exact h1
  · intro K hK hLK hKN
    obtain ⟨K', hK'def⟩ : ∃ K' : Subgroup G, K' = K.map V.subtype := ⟨_, rfl⟩
    have hK'V : K' ≤ V := by rw [hK'def]; exact Subgroup.map_subtype_le K
    have hK'y : ∀ x ∈ K', y * x * y⁻¹ ∈ K' := by
      intro x hx
      rw [hK'def] at hx ⊢
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨sigmaA_m22f S a, hK a ha, rfl⟩
    have hK'n : IsNormalIn X V K' := isNormalIn_of_yinv_m22f S hK'V hK'y
    have hLK' : L ≤ K' := by
      intro x hx
      rw [hK'def]
      exact Subgroup.mem_map.mpr ⟨⟨x, hLV hx⟩, hLK (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hKN' : K' ≤ N := by
      intro x hx
      rw [hK'def] at hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_subgroupOf.mp (hKN ha)
    have hKK : K'.subgroupOf V = K := by
      rw [hK'def]
      ext a
      simp [Subgroup.mem_subgroupOf]
    rcases hmax K' hK'n hLK' hKN' with h | h
    · left
      rw [← hKK, h]
    · right
      rw [← hKK, h]

theorem chief_translate_m22f (S : OrdThreeAct_m22f V X y) {N : Subgroup G} {k : ℕ}
    (h : IsChiefSeriesFrom X V N k) :
    N ≤ V ∧ @ChiefA_m22f ↥V (commGroupOfElemAbelian S.hV) (sigmaA_m22f S) (N.subgroupOf V) k := by
  letI := commGroupOfElemAbelian S.hV
  induction h with
  | bot =>
    refine ⟨bot_le, ?_⟩
    have hbot : (⊥ : Subgroup G).subgroupOf V = ⊥ := by
      ext a
      simp [Subgroup.mem_subgroupOf]
    rw [hbot]
    exact ChiefA_m22f.bot
  | central hstep hc _ ih =>
    obtain ⟨_, hLc⟩ := ih
    have hLN : _ ≤ _ := hstep.2.2.1.le
    have hNV : _ ≤ V := hstep.1.1
    have hLy : ∀ x ∈ _, y * x * y⁻¹ ∈ _ := yinv_of_isNormalIn_m22f S hstep.2.1
    have hcen := (isCentralStep_iff_m22f S hLN hNV hLy).mp hc
    refine ⟨hNV, ChiefA_m22f.central (chiefStep_translate_m22f S hstep) ?_ hLc⟩
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    show y * (a : G) * y⁻¹ * (a : G)⁻¹ ∈ _
    exact hcen (a : G) (Subgroup.mem_subgroupOf.mp ha)
  | noncentral hstep hnc _ ih =>
    obtain ⟨_, hLc⟩ := ih
    have hLN : _ ≤ _ := hstep.2.2.1.le
    have hNV : _ ≤ V := hstep.1.1
    have hLy : ∀ x ∈ _, y * x * y⁻¹ ∈ _ := yinv_of_isNormalIn_m22f S hstep.2.1
    refine ⟨hNV, ChiefA_m22f.noncentral (chiefStep_translate_m22f S hstep) ?_ hLc⟩
    intro hCA
    apply hnc
    rw [isCentralStep_iff_m22f S hLN hNV hLy]
    intro x hx
    exact Subgroup.mem_subgroupOf.mp (hCA ⟨x, hNV hx⟩ (Subgroup.mem_subgroupOf.mpr hx))

end Abstract

section TopImage

variable {A : Type} [CommGroup A]

theorem imgA_top_eq_range_m22f (σ : A →* A) : imgA_m22f σ (⊤ : Subgroup A) = (psiA_m22f σ).range := by
  ext w
  constructor
  · rintro ⟨⟨a, _⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩

end TopImage

section Final

variable {G : Type} [Group G] [Finite G]
variable {V X : Subgroup G} {y : G}

@[expose] def centV_m22f (S : OrdThreeAct_m22f V X y) : Subgroup ↥V where
  carrier := {v | y * (v : G) * y⁻¹ = (v : G)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul] at ha hb ⊢
    rw [show y * ((a : G) * (b : G)) * y⁻¹ = (y * (a : G) * y⁻¹) * (y * (b : G) * y⁻¹) by group, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at ha ⊢
    rw [show y * (a : G)⁻¹ * y⁻¹ = (y * (a : G) * y⁻¹)⁻¹ by group, ha]

theorem three_le_of_codim_m22f (S : OrdThreeAct_m22f V X y)
    (hcodim : 6 ≤ rkIdx (centV_m22f S)) {k : ℕ}
    (hk : IsChiefSeriesFrom X V V k) : 3 ≤ k := by
  letI := commGroupOfElemAbelian S.hV
  obtain ⟨-, hc⟩ := chief_translate_m22f S hk
  rw [Subgroup.subgroupOf_self] at hc
  have h3 : ∀ a : ↥V, sigmaA_m22f S (sigmaA_m22f S (sigmaA_m22f S a)) = a := fun a => by
    apply Subtype.ext
    have e := S.hy3 a a.2
    rw [pow_three] at e
    calc y * (y * (y * (a : G) * y⁻¹) * y⁻¹) * y⁻¹ = y * (y * y) * (a : G) * (y * (y * y))⁻¹ := by group
      _ = (a : G) := e
  have hexp : ∀ a : ↥V, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using S.hV.2 a a.2)
  have hbound := card_imgA_le_pow_of_chief_m22f h3 hexp hc
  rw [imgA_top_eq_range_m22f] at hbound
  have hK : centV_m22f S = (psiA_m22f (sigmaA_m22f S)).ker := by
    ext v
    rw [MonoidHom.mem_ker, psiA_apply_m22f, mul_inv_eq_one]
    change (y * (v : G) * y⁻¹ = (v : G)) ↔ _
    constructor
    · intro h
      apply Subtype.ext
      rw [sigmaA_coe_m22f]
      exact h
    · intro h
      have h' := congrArg Subtype.val h
      rw [sigmaA_coe_m22f] at h'
      exact h'
  rw [hK] at hcodim
  have hidx : (psiA_m22f (sigmaA_m22f S)).ker.index = Nat.card (psiA_m22f (sigmaA_m22f S)).range :=
    Subgroup.index_ker _
  have hpos : 0 < (psiA_m22f (sigmaA_m22f S)).ker.index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h64 : 2 ^ 6 ∣ (psiA_m22f (sigmaA_m22f S)).ker.index :=
    (pow_dvd_pow 2 hcodim).trans (pow_padicValNat_dvd)
  have h64' : 2 ^ 6 ≤ Nat.card (psiA_m22f (sigmaA_m22f S)).range := by
    rw [← hidx]
    exact Nat.le_of_dvd hpos h64
  by_contra hlt
  push Not at hlt
  have h4 : 4 ^ k ≤ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := le_trans h64' hbound
  norm_num at this h4
  omega

end Final

end CFSG.Quasithin.H13.M22F
