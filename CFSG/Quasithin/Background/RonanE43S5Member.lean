module

public import CFSG.Quasithin.Background.RonanE43S5
public import CFSG.Quasithin.Background.RonanE43Normal
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42

variable {G : Type} [Group G] [Finite G]

theorem relIndex_two_power {T H A : Subgroup G} (hT : IsPGroup 2 T)
    (hAn : H ≤ Subgroup.normalizer (A : Set G)) (hAH : A ≤ H) (hH : A ⊔ T = H) :
    ∃ k : ℕ, A.relIndex H = 2 ^ k := by
  have h1 := card_sup_eq_relIndex_mul (P := A) (T := T) (le_sup_right.trans (hH.le.trans hAn))
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := T)
  have h4 := Subgroup.relIndex_mul_card (H := A) (K := H)
  rw [inf_eq_left.mpr hAH] at h4
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hT
  have h3 : A.relIndex T ∣ 2 ^ m := ⟨Nat.card ↥(A ⊓ T), by rw [← hm, ← h2]⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  refine ⟨k, ?_⟩
  rw [hH, hk] at h1
  have hApos : 0 < Nat.card A := Nat.card_pos
  have : A.relIndex H * Nat.card A = 2 ^ k * Nat.card A := by rw [h4, h1]
  exact Nat.eq_of_mul_eq_mul_right hApos this

theorem s5_good {T H A V : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H) (hAH : A ≤ H)
    (hVA : V ≤ A) (hAn : H ≤ Subgroup.normalizer (A : Set G))
    (hVn : H ≤ Subgroup.normalizer (V : Set G)) (hV2 : IsPGroup 2 V)
    (φ : ↥A →* alternatingGroup (Fin 5)) (hφs : Function.Surjective φ)
    (hφk : φ.ker = V.subgroupOf A) (hHA : A ⊔ T = H)
    {Y : Subgroup G} (hYH : Y ≤ H) (hYn : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y)
    (hYT : ¬ (Y ⊓ T ≤ pCoreOf 2 H)) :
    H ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) := by
  set R := pCoreOf 2 H with hR
  have hRT : R ≤ T := pCoreOf_le_of_sylow hT hTH
  have hVR : V ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hVA.trans hAH) hVn hV2
  have hVT : V ≤ T := hVR.trans hRT
  have hYnorm : H ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_of_conj_mem hYn
  have hYAn : H ≤ Subgroup.normalizer ((Y ⊓ A : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_inf]
    have hYh := Subgroup.mem_normalizer_iff.mp (hYnorm hh) x
    have hAh := Subgroup.mem_normalizer_iff.mp (hAn hh) x
    rw [hYh, hAh]
  have hMn : H ≤ Subgroup.normalizer (((Y ⊓ A) ⊔ V : Subgroup G) : Set G) :=
    le_normalizer_sup_pair hYAn hVn
  have hMA : (Y ⊓ A) ⊔ V ≤ A := sup_le inf_le_right hVA
  have hMnorm : (((Y ⊓ A) ⊔ V).subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMA).mpr (hAH.trans hMn)
  haveI := hMnorm
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI hmapn : ((((Y ⊓ A) ⊔ V).subgroupOf A).map φ).Normal := hMnorm.map φ hφs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((((Y ⊓ A) ⊔ V).subgroupOf A).map φ) with hbot | htop
  ·
    exfalso
    have h1 : ((Y ⊓ A) ⊔ V).subgroupOf A ≤ V.subgroupOf A := by
      rw [← hφk]
      intro x hx
      have := Subgroup.mem_map_of_mem φ hx
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have hYAV : Y ⊓ A ≤ V := fun x hx =>
      (Subgroup.mem_subgroupOf.mp (h1 (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_left hx : x ∈ (Y ⊓ A) ⊔ V) : (⟨x, hx.2⟩ : ↥A) ∈ _)))
    obtain ⟨k, hk⟩ := relIndex_two_power hT.isPGroup hAn hAH hHA
    haveI : (A.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAn
    have hpow : ∀ y ∈ H, y ^ (2 ^ k) ∈ A := by
      intro y hy
      have h2 := (A.subgroupOf H).pow_index_mem (⟨y, hy⟩ : ↥H)
      have h3 : (A.subgroupOf H).index = 2 ^ k := hk
      rw [h3] at h2
      exact Subgroup.mem_subgroupOf.mp h2
    have hY2 : IsPGroup 2 Y := by
      intro y
      have hyA : (y : G) ^ (2 ^ k) ∈ Y ⊓ A :=
        ⟨Y.pow_mem y.2 _, hpow y (hYH y.2)⟩
      obtain ⟨j, hj⟩ := hV2 ⟨_, hYAV hyA⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have := congrArg Subtype.val hj
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
      rw [pow_add, pow_mul]
      exact this
    have hYR : Y ≤ R :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYH hYnorm hY2
    exact hYT (inf_le_left.trans hYR)
  ·
    have h1 : ((Y ⊓ A) ⊔ V).subgroupOf A = ⊤ := by
      have h2 := Subgroup.comap_map_eq φ (((Y ⊓ A) ⊔ V).subgroupOf A)
      rw [htop, Subgroup.comap_top, hφk] at h2
      have h3 : V.subgroupOf A ≤ ((Y ⊓ A) ⊔ V).subgroupOf A :=
        Subgroup.subgroupOf_mono A le_sup_right
      rw [sup_eq_left.mpr h3] at h2
      exact h2.symm
    have hAM : A ≤ (Y ⊓ A) ⊔ V := Subgroup.subgroupOf_eq_top.mp h1
    have hAYT : A ≤ Y ⊔ T :=
      hAM.trans (sup_le (inf_le_left.trans le_sup_left) (hVT.trans le_sup_right))
    have hHYT : H ≤ Y ⊔ T := by
      rw [← hHA]
      exact sup_le hAYT le_sup_right
    exact hHYT.trans (by
      intro x hx
      exact (sup_le (le_sup_of_le_right le_sup_right) (le_sup_of_le_right le_sup_left)
        : Y ⊔ T ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y)) hx)

theorem s5_pRank {T H A V : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hAH : A ≤ H)
    (hVA : V ≤ A) (hAn : H ≤ Subgroup.normalizer (A : Set G))
    (hVn : H ≤ Subgroup.normalizer (V : Set G)) (hV2 : IsPGroup 2 V)
    (φ : ↥A →* alternatingGroup (Fin 5)) (hφs : Function.Surjective φ)
    (hφk : φ.ker = V.subgroupOf A) (hHA : A ⊔ T = H) :
    CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  set R' : Subgroup ↥H := CFSG.pCore 2 ↥H with hR'
  set A' : Subgroup ↥H := A.subgroupOf H with hA'
  haveI hA'n : A'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAn
  let q : ↥H →* ↥H ⧸ R' := QuotientGroup.mk' R'
  let ι : ↥A' ≃* ↥A := Subgroup.subgroupOfEquivOfLe hAH
  let θ : ↥A' →* alternatingGroup (Fin 5) := φ.comp ι.toMonoidHom
  have hθs : Function.Surjective θ := hφs.comp ι.surjective
  have hVR : V ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hVA.trans hAH) hVn hV2
  have hθk : ∀ a : ↥A', θ a = 1 ↔ (((a : ↥H) : H) : G) ∈ V := by
    intro a
    have h1 : θ a = 1 ↔ ι a ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      rfl
    rw [h1, hφk, Subgroup.mem_subgroupOf]
    rfl
  have hVR' : ∀ a : ↥H, ((a : H) : G) ∈ V → a ∈ R' := by
    intro a ha
    obtain ⟨r, hr, hra⟩ := hVR ha
    have : r = a := Subtype.ext hra
    rwa [← this]
  set W : Subgroup ↥A' := R'.subgroupOf A' with hW
  haveI hWn : W.Normal := (CFSG.pCore_normal (p := 2) (G := ↥H)).comap A'.subtype
  have hW2 : IsPGroup 2 W := by
    intro w
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨((w : ↥A') : ↥H), w.2⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun x : ↥R' => ((x : ↥H))) hn
    simpa using this
  have hmapn : (W.map θ).Normal := hWn.map θ hθs
  have hWk : W ≤ θ.ker := by
    have hcases := IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map θ)
    rcases hcases with hbot | htop
    · intro w hw
      have := Subgroup.mem_map_of_mem θ hw
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have h2 : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 5))) := htop ▸ hW2.map θ
      obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp h2
      have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
        decide
      rw [Subgroup.card_top, h60] at hm
      have h3 : (3 : ℕ) ∣ 2 ^ m := by rw [← hm]; norm_num
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  let qA : ↥A' →* ↥H ⧸ R' := q.comp A'.subtype
  have hqAker : qA.ker = θ.ker := by
    apply le_antisymm
    · intro a ha
      apply hWk
      show (a : ↥H) ∈ R'
      have : q (a : ↥H) = 1 := ha
      exact (QuotientGroup.eq_one_iff _).mp this
    · intro a ha
      have h1 : (((a : ↥H) : H) : G) ∈ V := (hθk a).mp ha
      show q (a : ↥H) = 1
      exact (QuotientGroup.eq_one_iff _).mpr (hVR' _ h1)
  let N : Subgroup (↥H ⧸ R') := qA.range
  haveI hNn : N.Normal := by
    have hrange : qA.range = A'.map q := by
      show (q.comp A'.subtype).range = A'.map q
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    show qA.range.Normal
    rw [hrange]
    exact hA'n.map q (QuotientGroup.mk'_surjective R')
  let e : ↥N ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientKerEquivRange qA).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hqAker).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ hθs))
  obtain ⟨k, hk⟩ := relIndex_two_power hT.isPGroup hAn hAH hHA
  have h2 : ∀ x : ↥H ⧸ R', ∃ n : ℕ, x ^ 2 ^ n ∈ N := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective R' x
    refine ⟨k, ?_⟩
    have h1 := A'.pow_index_mem h
    have h3 : A'.index = 2 ^ k := hk
    rw [h3] at h1
    exact ⟨⟨h ^ 2 ^ k, h1⟩, by simp [qA, q]⟩
  have hO2 : CFSG.pCore 2 (↥H ⧸ R') = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k' ⟨E, -, hE, hEk⟩
  have h4 := card_le_four_of_A5 N e h2 hO2 hE
  rw [hEk] at h4
  by_contra hk'
  push Not at hk'
  have : 2 ^ 3 ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) hk'
  omega

end CFSG.Quasithin.RonanE43
