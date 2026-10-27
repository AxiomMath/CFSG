module

public import CFSG.Quasithin.EmptyFaithful.SBc15R3W
public import CFSG.Quasithin.EmptyFaithful.SBc15C2Dec
public import CFSG.Quasithin.Background.GoldschmidtS146PMain
public import CFSG.Quasithin.EmptyFaithful.SBc15Transfer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc15

namespace R3

section Hom

variable {Γ Ŵ : Type} [Group Γ] [Group Ŵ]

theorem map_inf_of_ker_le (ψ : Γ →* Ŵ) {A B : Subgroup Γ} (h : ψ.ker ≤ A) :
    (A ⊓ B).map ψ = A.map ψ ⊓ B.map ψ := by
  refine le_antisymm (Subgroup.map_inf_le A B ψ) ?_
  rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
  have hz : a⁻¹ * b ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  have hbA : b ∈ A := by
    have : b = a * (a⁻¹ * b) := by group
    rw [this]
    exact A.mul_mem ha (h hz)
  exact ⟨b, ⟨hbA, hb⟩, hab⟩

theorem isSylowTwoOf_map_top (ψ : Γ →* Ŵ) (hψ : Function.Surjective ψ) {T : Subgroup Γ}
    (hT : IsSylowTwoOf T ⊤) : IsSylowTwoOf (T.map ψ) ⊤ := by
  refine ⟨le_top, hT.2.1.map ψ, ?_⟩
  have h1 : ((T.map ψ).subgroupOf ⊤).index = (T.map ψ).index := Subgroup.relIndex_top_right _
  have h2 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right _
  rw [h1]
  exact fun hd => hT.2.2 (h2 ▸ hd.trans (Subgroup.index_map_dvd T hψ))

theorem isSylowTwoOf_subgroupOf_top {G : Type} [Group G] {T G₁ : Subgroup G}
    (h : IsSylowTwoOf T G₁) : IsSylowTwoOf (T.subgroupOf G₁) ⊤ := by
  refine ⟨le_top, A4.isPGroup_subgroupOf_of_le h.1 h.2.1, ?_⟩
  have h1 : ((T.subgroupOf G₁).subgroupOf ⊤).index = (T.subgroupOf G₁).index :=
    Subgroup.relIndex_top_right _
  rw [h1]
  exact h.2.2

theorem exists_card_map [Finite Γ] (ψ : Γ →* Ŵ) (hker : IsPGroup 2 ψ.ker) {X : Subgroup Γ}
    {m : ℕ} (hX : Nat.card X = 9 * 2 ^ m) : ∃ a : ℕ, Nat.card (X.map ψ) = 9 * 2 ^ a := by
  have h1 := Subgroup.relIndex_mul_card (H := ψ.ker) (K := X)
  rw [Subgroup.relIndex_ker, hX] at h1
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp (hker.to_inf_left (K := X))
  rw [hb] at h1
  have hdvd : 2 ^ b ∣ 2 ^ m * 9 := ⟨Nat.card (X.map ψ), by rw [mul_comm] at h1; linarith⟩
  have hcop : Nat.Coprime (2 ^ b) 9 := Nat.Coprime.pow_left b (by norm_num)
  have hbm : b ≤ m :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  refine ⟨m - b, Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ b) ?_⟩
  rw [h1, mul_assoc, ← pow_add, Nat.sub_add_cancel hbm]

end Hom

section Top

variable {Γ : Type} [Group Γ] [Finite Γ] {D : Type} [Group D] [Finite D]

theorem parabolicWeak_top_of_wreath (D' : Subgroup D) [D'.Normal] [IsSimpleGroup D']
    (hnc : ∃ a b : D', a * b ≠ b * a) [Group.IsSolvable (D ⧸ D')] (h : WeakW D D')
    (ψ : Γ →* D ≀ᵣ Multiplicative (ZMod 2)) (hψ : Function.Surjective ψ)
    (hker : IsPGroup 2 ψ.ker) {T X K : Subgroup Γ} (hT : IsSylowTwoOf T ⊤) (hKn : K.Normal)
    (hKp : ⁅K, K⁆ = K) (hKne : K ≠ ⊥) (hXK : X ≤ K)
    (hTX : T ≤ Subgroup.normalizer (X : Set Γ)) (hXO : oTwoUpper X = X)
    (h9 : ∃ m : ℕ, Nat.card X = 9 * 2 ^ m) : ParabolicWeak T X K ⊤ := by
  have hkerT : ψ.ker ≤ T := A4.le_of_normal_of_isSylowTwoOf hT le_top inferInstance hker
  have hKmap : K.map ψ = wrPerf D' := by
    have : (K.map ψ).Normal := hKn.map ψ hψ
    refine eq_wrPerf_of_normal_perfect D' hnc ?_ ?_
    · rw [← Subgroup.map_commutator, hKp]
    · intro hbot
      have hle : K ≤ ψ.ker := (Subgroup.map_eq_bot_iff K).mp hbot
      have hK2 : IsPGroup 2 K := hker.to_le hle
      have : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hKp
      have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
      have : Group.IsNilpotent K := hK2.isNilpotent
      exact Group.IsPerfect.not_isSolvable K inferInstance
  have hTmap : IsSylowTwoOf (T.map ψ) ⊤ := isSylowTwoOf_map_top ψ hψ hT
  have hinf : (T ⊓ K).map ψ = T.map ψ ⊓ wrPerf D' := by
    rw [map_inf_of_ker_le ψ hkerT, hKmap]
  have hXP : X.map ψ ≤ wrPerf D' := hKmap ▸ Subgroup.map_mono hXK
  have hTn : T.map ψ ≤ Subgroup.normalizer (X.map ψ : Set (D ≀ᵣ Multiplicative (ZMod 2))) := by
    rintro _ ⟨t, ht, rfl⟩
    exact Subgroup.le_normalizer_map ψ ⟨t, hTX ht, rfl⟩
  have hXO' : oTwoUpper (X.map ψ) = X.map ψ := by rw [oTwoUpper_map, hXO]
  obtain ⟨m, hm⟩ := h9
  obtain ⟨a, ha⟩ := exists_card_map ψ hker hm
  refine parabolicWeak_of_quotient ψ hker hkerT hXK ?_ ?_
  · intro g
    obtain ⟨k, hk, y, hy, hg⟩ := h.1 (T.map ψ) hTmap (ψ g)
    exact ⟨k, hKmap ▸ hk, y, hy, hg⟩
  · intro k hk hw
    rw [hinf] at hw ⊢
    rw [hKmap] at hk
    exact h.2 (T.map ψ) (X.map ψ) hTmap hXP hTn hXO' ⟨a, ha⟩ k hk hw

end Top

section Gctx

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}
  {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem parabolicWeak_of_wreath (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) (hp : p = 3)
    (hdec : IsDecP T M H p H₀ H₁ H₂ t) {D : Type} [Group D] [Finite D] (D' : Subgroup D)
    [D'.Normal] [IsSimpleGroup D'] (hnc : ∃ a b : D', a * b ≠ b * a)
    [Group.IsSolvable (D ⧸ D')] (hW : WeakW D D') {K₁ : Subgroup G} {s : G}
    (hK₁ : K₁ ∈ cComp (mcOf T)) (hK : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    (e : OTwoQuot (mcOf T) ≃* (D ≀ᵣ Multiplicative (ZMod 2))) :
    ParabolicWeak T (oTwoUpper H) (conjClosure (oTwoUpper H) (mcOf T)) (mcOf T) := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hTG : T ≤ mcOf T := hTH.trans hHG
  have hXG : oTwoUpper H ≤ mcOf T := (oTwoUpper_le H).trans hHG
  have hKG : conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T := SBc13.kz_le_mcOf S hred
  have hsyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTG
  refine parabolicWeak_of_subtype hXG hTG hKG ?_
  let ψ : ↥(mcOf T) →* D ≀ᵣ Multiplicative (ZMod 2) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(mcOf T)))
  have hψ : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : IsPGroup 2 ψ.ker := by
    have h : ψ.ker = CFSG.Open.pCore 2 ↥(mcOf T) := by
      ext x
      rw [MonoidHom.mem_ker]
      show e (QuotientGroup.mk x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    rw [h]
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hKperf : ⁅conjClosure (oTwoUpper H) (mcOf T), conjClosure (oTwoUpper H) (mcOf T)⁆ =
      conjClosure (oTwoUpper H) (mcOf T) := by
    rw [hK]
    exact GoldS146P.perfect_sup_conjSub (perfect_of_mem_cComp hK₁) s
  have hKn : ((conjClosure (oTwoUpper H) (mcOf T)).subgroupOf (mcOf T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mpr (le_normalizer_conjClosure _ _)
  have hKp : ⁅(conjClosure (oTwoUpper H) (mcOf T)).subgroupOf (mcOf T),
      (conjClosure (oTwoUpper H) (mcOf T)).subgroupOf (mcOf T)⁆ =
      (conjClosure (oTwoUpper H) (mcOf T)).subgroupOf (mcOf T) := by
    apply Subgroup.map_injective (mcOf T).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKG, hKperf]
  have hKne : (conjClosure (oTwoUpper H) (mcOf T)).subgroupOf (mcOf T) ≠ ⊥ := by
    intro h
    have hbot : conjClosure (oTwoUpper H) (mcOf T) = ⊥ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hKG, h, Subgroup.map_bot]
    have h1 : K₁ ≤ conjClosure (oTwoUpper H) (mcOf T) := by
      rw [hK]
      exact le_sup_left
    exact ne_bot_of_mem_cComp hK₁ (le_bot_iff.mp (hbot ▸ h1))
  have hXK : (oTwoUpper H).subgroupOf (mcOf T) ≤
      (conjClosure (oTwoUpper H) (mcOf T)).subgroupOf (mcOf T) :=
    Subgroup.comap_mono (le_conjClosure _ _)
  have hTX : T.subgroupOf (mcOf T) ≤
      Subgroup.normalizer (((oTwoUpper H).subgroupOf (mcOf T) : Subgroup ↥(mcOf T)) :
        Set ↥(mcOf T)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hXG]
    exact Subgroup.comap_mono (hTH.trans (le_normalizer_oTwoUpper H))
  have hXO : oTwoUpper ((oTwoUpper H).subgroupOf (mcOf T)) = (oTwoUpper H).subgroupOf (mcOf T) := by
    rw [A4.oTwoUpper_subgroupOf hXG, oTwoUpper_idem_P]
  have h9 : ∃ m : ℕ, Nat.card ((oTwoUpper H).subgroupOf (mcOf T)) = 9 * 2 ^ m := by
    have hrel := relIndex_pCoreOf_oTwoUpper_eq_nine S hred hp hdec
    have hcard := Subgroup.relIndex_mul_card (H := pCoreOf 2 (oTwoUpper H)) (K := oTwoUpper H)
    rw [inf_eq_left.mpr (pCoreOf_le 2 _), hrel] at hcard
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (pCoreOf_isPGroup 2 (oTwoUpper H))
    refine ⟨m, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXG).toEquiv, ← hcard, hm]
  exact parabolicWeak_top_of_wreath D' hnc hW ψ hψ hker (isSylowTwoOf_subgroupOf_top hsyl) hKn hKp
    hKne hXK hTX hXO h9

end Gctx

end R3

end SBc15

end CFSG.Quasithin
