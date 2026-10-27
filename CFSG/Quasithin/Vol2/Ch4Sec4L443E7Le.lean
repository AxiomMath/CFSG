module

public import CFSG.Quasithin.Vol2.Ch4Sec4L443E6Loc

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem mem_normalizer_inf_sup {A B : Subgroup H} {x : H}
    (hA : x ∈ Subgroup.normalizer (A : Set H)) (hB : x ∈ Subgroup.normalizer (B : Set H)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup H) : Set H) ∧
      x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine ⟨?_, by rw [Subgroup.map_sup, hA, hB]⟩
  rw [Subgroup.map_inf _ _ _ (MulAut.conj x).injective, hA, hB]

omit [Finite H] in
theorem isPGroup_quotient_sup {V K : Subgroup H} [hK : K.Normal] (hV : IsPGroup 2 V) :
    IsPGroup 2 (↥(V ⊔ K) ⧸ K.subgroupOf (V ⊔ K)) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hx : (x : H) ∈ (V : Set H) * (K : Set H) := by
    rw [← Subgroup.mul_normal V K]
    exact x.2
  obtain ⟨v, hv, k, hk, hvk⟩ := hx
  obtain ⟨n, hn⟩ := hV ⟨v, hv⟩
  refine ⟨n, ?_⟩
  have e : (x : ↥(V ⊔ K) ⧸ K.subgroupOf (V ⊔ K)) =
      ((⟨v, Subgroup.mem_sup_left hv⟩ : ↥(V ⊔ K)) : ↥(V ⊔ K) ⧸ K.subgroupOf (V ⊔ K)) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : ((x : H))⁻¹ * v = k⁻¹ := by rw [← hvk]; group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [this]
    exact K.inv_mem hk
  rw [e, ← QuotientGroup.mk_pow]
  have hv1 : (⟨v, Subgroup.mem_sup_left hv⟩ : ↥(V ⊔ K)) ^ 2 ^ n = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hn)
  rw [hv1, QuotientGroup.mk_one]

theorem le_of_normal {V L S M : Subgroup H} (hc : LocConf H V L S M) {K : Subgroup H}
    [hKn : K.Normal] (hKM : ¬ K ≤ M) (hVY : V ≤ K ⊔ Subgroup.centralizer (K : Set H)) :
    V ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (K : Set H) with hC
  set W := (V ⊔ K) ⊓ C with hW
  have hKN : ∀ x : H, x ∈ Subgroup.normalizer (K : Set H) := fun x => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
    trivial
  have hCN : ∀ x : H, x ∈ Subgroup.normalizer (C : Set H) := fun x =>
    CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer K (hKN x)
  have hWN : L ⊔ S ≤ Subgroup.normalizer (W : Set H) := fun x hx =>
    (mem_normalizer_inf_sup (mem_normalizer_inf_sup (hc.v_norm hx) (hKN x)).2 (hCN x)).1
  have hR : pCoreOf 2 W = ⊥ := by
    by_contra hR
    have h1 := hc.uniq _ hR (pCoreOf_isPGroup 2 W)
      (hWN.trans (normalizer_le_normalizer_pCoreOf 2 W))
    apply hKM
    have hKR : K ≤ Subgroup.centralizer (pCoreOf 2 W : Set H) :=
      Subgroup.le_centralizer_iff.mp ((pCoreOf_le 2 W).trans inf_le_right)
    exact hKR.trans ((Subgroup.centralizer_le_normalizer _).trans h1)
  set ψ : ↥W →* ↥(V ⊔ K) ⧸ K.subgroupOf (V ⊔ K) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion (inf_le_left : W ≤ V ⊔ K)) with hψ
  have hmemK : ∀ w : ↥W, ψ w = 1 → (w : H) ∈ K := fun w hw => by
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hw
    exact hw
  have hker : ψ.ker ≤ Subgroup.center ↥W := fun w hw => by
    rw [Subgroup.mem_center_iff]
    intro w'
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp w'.2.2 _ (hmemK w hw)).symm
  have hQ2 : IsPGroup 2 (↥(V ⊔ K) ⧸ K.subgroupOf (V ⊔ K)) := isPGroup_quotient_sup hc.v_two
  have : Group.IsNilpotent (↥(V ⊔ K) ⧸ K.subgroupOf (V ⊔ K)) := hQ2.isNilpotent
  have hWnil : Group.IsNilpotent ↥W := Subgroup.isNilpotent_of_ker_le_center ψ hker
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥W))
  have hPn := Sylow.normal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent P
  have hPW : W ≤
      Subgroup.normalizer (((P : Subgroup ↥W).map W.subtype : Subgroup H) : Set H) := by
    have h1 := Subgroup.le_normalizer_map (H := (P : Subgroup ↥W)) W.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hPn, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    exact h1
  have hPle : (P : Subgroup ↥W).map W.subtype ≤ pCoreOf 2 W :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _) hPW
      (P.isPGroup'.map W.subtype)
  rw [hR, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective] at hPle
  have hodd : Nat.Coprime 2 (Nat.card ↥W) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h2 =>
      Sylow.ne_bot_of_dvd_card P h2 hPle
  have hWK : W ≤ K := fun w hw => by
    obtain ⟨k, hk⟩ := hQ2 (ψ ⟨w, hw⟩)
    have h1 : ψ ⟨w, hw⟩ ^ Nat.card ↥W = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
    have h2 := pow_gcd_eq_one.mpr ⟨hk, h1⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k hodd), pow_one] at h2
    exact hmemK ⟨w, hw⟩ h2
  have hKC : K ≤ Subgroup.normalizer (C : Set H) := fun k _ => hCN k
  intro v hv
  have hv' : v ∈ (K : Set H) * (C : Set H) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K C hKC]
    exact hVY hv
  obtain ⟨k, hk, c, hc', rfl⟩ := hv'
  have hcW : c ∈ W := by
    refine ⟨?_, hc'⟩
    have e : c = k⁻¹ * (k * c) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (K.inv_mem hk)) (Subgroup.mem_sup_left hv)
  exact K.mul_mem hk (hWK hcW)

end CFSG.Quasithin.H13.Ch4.E443
