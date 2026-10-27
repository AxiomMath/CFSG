module

public import CFSG.Monster.B.GSide.RecognitionAssembly
public import CFSG.Monster.B.GSide.GenericGeneration
public import CFSG.Monster.B.Recog.GenericStrongEmbedding
public import CFSG.Monster.B.CTIB.SylowCenter
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3059
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate3080
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate16042
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069
public import CFSG.Assembly.OddCoreSpan
public import CFSG.Goldschmidt.Statements
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.CTIB CFSG.BenderSuzuki

variable {G : Type*} [Group G]

theorem cV0_ne_one :
    cV0 ≠ 1 := by
  intro h
  have h2 := orderOf_cV0
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem injective_of_map_cV0_ne_one
    (Φ : Shat →* G) (h : Φ (cV0 : Shat) ≠ 1) :
    Function.Injective Φ := by
  have := isSimpleGroup_Shat
  rcases Φ.normal_ker.eq_bot_or_eq_top with hk | hk
  · exact (MonoidHom.ker_eq_bot_iff Φ).1 hk
  · refine absurd ?_ h
    rw [← Φ.mem_ker, hk]
    exact Subgroup.mem_top _

theorem exists_injective_completion
    (φv : vStab cv0 →* G) (hφv : Function.Injective φv) (φe : cvSetStab {cv0, cw0} →* G)
    (φt : ∀ j, cvSetStab {cv0, cw0, cu j} →* G)
    (hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0, cu j}),
      φv ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ cvSetStab {cv0, cw0}) (hb : a ∈ cvSetStab {cv0, cw0, cu j}),
      φe ⟨a, ha⟩ = φt j ⟨a, hb⟩) :
    ∃ Φ : Shat →* G, Function.Injective Φ ∧ (∀ a : vStab cv0, Φ a = φv a) ∧
      (∀ a : cvSetStab {cv0, cw0}, Φ a = φe a) ∧
      ∀ j (a : cvSetStab {cv0, cw0, cu j}), Φ a = φt j a := by
  have hU := native_universal_completion φv φe φt hve hvt het
  obtain ⟨Φ, ⟨hΦv, hΦe, hΦt⟩, -⟩ := hU
  refine ⟨Φ, injective_of_map_cV0_ne_one Φ fun h => cV0_ne_one (hφv ?_), hΦv, hΦe, hΦt⟩
  exact (hΦv cV0).symm.trans (h.trans (map_one φv).symm)

@[expose] def psiInvHom
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0) : vStab cv0 →* G :=
  (Subgroup.centralizer {d}).subtype.comp ψ.symm.toMonoidHom

theorem psiInvHom_apply
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (a : vStab cv0) :
    psiInvHom ψ a = ((ψ.symm a : Subgroup.centralizer {d}) : G) := rfl

theorem psiInvHom_injective
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0) :
    Function.Injective (psiInvHom ψ) :=
  Subtype.val_injective.comp ψ.symm.injective

theorem map_cV0_of_psiInvHom
    {d : G} (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    {Φ : Shat →* G} (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a) : Φ (cV0 : Shat) = d := by
  rw [hΦ, psiInvHom_apply, ← centralizer_equiv_self_eq_cV0 hd ψ, MulEquiv.symm_apply_apply]

theorem centralizer_le_range_of_psiInvHom
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    {Φ : Shat →* G} (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a) :
    Subgroup.centralizer {d} ≤ Φ.range := fun x hx =>
  ⟨ψ ⟨x, hx⟩, by rw [hΦ, psiInvHom_apply, MulEquiv.symm_apply_apply]⟩

theorem centralizer_conj_le_range {d : G} {Φ : Shat →* G}
    (hd : Subgroup.centralizer {d} ≤ Φ.range) {g : G} (hg : g ∈ Φ.range) :
    Subgroup.centralizer {g * d * g⁻¹} ≤ Φ.range := fun x hx => by
  have h := hd (centralizerConjEquiv g rfl ⟨x, hx⟩).2
  rw [coe_centralizerConjEquiv] at h
  have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [e]
  exact Φ.range.mul_mem (Φ.range.mul_mem hg h) (Φ.range.inv_mem hg)

theorem completion_centralizer
    {d : G} (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (Φ : Shat →* G) (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a) :
    Φ (cV0 : Shat) = d ∧ Subgroup.centralizer {d} ≤ Φ.range ∧
      ∀ g ∈ Φ.range, Subgroup.centralizer {g * d * g⁻¹} ≤ Φ.range :=
  ⟨map_cV0_of_psiInvHom hd ψ hΦ, centralizer_le_range_of_psiInvHom ψ hΦ,
    fun _ hg => centralizer_conj_le_range (centralizer_le_range_of_psiInvHom ψ hΦ) hg⟩

theorem centralizer_cV0 :
    Subgroup.centralizer {(cV0 : Shat)} = vStab cv0 := by
  rw [coe_cV0, show clabelS cv0 = cS from Subtype.ext clabel_cv0,
    centralizer_cS native_global_label_bijection_and_full_vertex_centralizer.2.2.2.1,
    vStab_cv0_eq]

theorem natCard_centralizer_cV0 :
    Nat.card (Subgroup.centralizer {(cV0 : Shat)}) = 306129918735099415756800 := by
  rw [centralizer_cV0]
  exact natCard_vStab_eq cv0

theorem conj_cV0_ne_sEquiv_xs
    (s : Shat) : s * (cV0 : Shat) * s⁻¹ ≠ sEquiv xs := by
  intro hsc
  have hN := native_sylow_two_center
  obtain ⟨-, ⟨T₀, hT₀c, -⟩, hall, -⟩ := hN
  have hT : (T₀ : Subgroup Sbp).map sEquiv.toMonoidHom ≤
      Subgroup.centralizer {(sEquiv xs : Shat)} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 (hT₀c hy)]
  have hdvd := Subgroup.card_dvd_of_le hT
  rw [Subgroup.card_map_of_injective (f := sEquiv.toMonoidHom) sEquiv.injective, (hall T₀).1,
    Nat.card_congr (centralizerConjEquiv s hsc).toEquiv, natCard_centralizer_cV0] at hdvd
  exact absurd hdvd (by norm_num)

theorem exists_sylow_two_unique_center
    [Finite G] {Ψ : Sbp →* G} (hΨ : Function.Injective Ψ)
    (hC : ∀ t ∈ Ψ.range, orderOf t = 2 → Subgroup.centralizer {t} ≤ Ψ.range) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Ψ.range ∧ Ψ xs ∈ (S : Subgroup G) ∧
      (∀ s ∈ (S : Subgroup G), Ψ xs * s = s * Ψ xs) ∧
      ∀ x ∈ (S : Subgroup G), orderOf x = 2 → (∀ s ∈ (S : Subgroup G), x * s = s * x) →
        x = Ψ xs := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := native_sylow_two_center
  obtain ⟨-, ⟨T₀, hT₀c, hT₀⟩, hall, -⟩ := hN
  have hxT₀ : xs ∈ (T₀ : Subgroup Sbp) :=
    (CFSG.Monster.mem_map_center_iff.1 (hT₀ ▸ Subgroup.mem_zpowers xs)).1
  have hPcard : Nat.card ((T₀ : Subgroup Sbp).map Ψ) = 2 ^ 41 := by
    rw [Subgroup.card_map_of_injective hΨ]
    exact (hall T₀).1
  have hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Ψ.range →
      Nat.card Q ≤ Nat.card ((T₀ : Subgroup Sbp).map Ψ) := by
    intro Q hQ hQM
    obtain ⟨T, hT⟩ := (hQ.comap_of_injective Ψ hΨ).exists_le_sylow
    rw [hPcard, ← (hall T).1, ← Subgroup.map_comap_eq_self hQM,
      Subgroup.card_map_of_injective hΨ]
    exact Subgroup.card_le_of_le hT
  have hP1 : (T₀ : Subgroup Sbp).map Ψ ≠ ⊥ := fun h => by
    have h' := hPcard
    rw [h, Subgroup.card_bot] at h'
    exact absurd h' (by norm_num)
  obtain ⟨S, hS⟩ := Recog.StrongEmbedding.exists_sylow_eq hC (T₀.isPGroup'.map Ψ)
    (Subgroup.map_le_range Ψ _) hP1 hmax
  refine ⟨S, hS ▸ Subgroup.map_le_range Ψ _, hS ▸ Subgroup.mem_map_of_mem Ψ hxT₀, ?_, ?_⟩
  · intro s hs
    rw [hS] at hs
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hs
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hT₀c hy)]
  · intro x hx hx2 hxc
    rw [hS] at hx hxc
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hyc : y ∈ (Subgroup.center (T₀ : Subgroup Sbp)).map (T₀ : Subgroup Sbp).subtype :=
      CFSG.Monster.mem_map_center_iff.2 ⟨hy, fun w hw => hΨ (by
        rw [map_mul, map_mul]
        exact (hxc _ (Subgroup.mem_map_of_mem Ψ hw)).symm)⟩
    rw [hT₀] at hyc
    rw [orderOf_injective Ψ hΨ] at hx2
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyc
    rw [← zpow_mod_orderOf, orderOf_xs] at hx2 ⊢
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [Nat.cast_ofNat, h, zpow_zero, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    · rw [Nat.cast_ofNat, h, zpow_one]

theorem range_eq_top_of_centralizer_le
    [Finite G] (Φ : Shat →* G) (hΦ : Function.Injective Φ)
    (hC : ∀ t ∈ Φ.range, orderOf t = 2 → Subgroup.centralizer {t} ≤ Φ.range) :
    Φ.range = ⊤ := by
  by_contra hM
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : Sbp →* G, Ψ = Φ.comp sEquiv.toMonoidHom := ⟨_, rfl⟩
  have hΨ : Function.Injective Ψ := hΨdef ▸ hΦ.comp sEquiv.injective
  have hΨr : Ψ.range = Φ.range := by
    rw [hΨdef, MonoidHom.range_comp,
      (MonoidHom.range_eq_top (f := sEquiv.toMonoidHom)).2 sEquiv.surjective,
      ← MonoidHom.range_eq_map]
  have hΨx : Ψ xs = Φ (sEquiv xs) := by rw [hΨdef]; rfl
  rw [← hΨr] at hC hM
  obtain ⟨S, hSM, hzS, hzc, huniq⟩ := exists_sylow_two_unique_center hΨ hC
  have hz2 : orderOf (Ψ xs) = 2 := by rw [orderOf_injective Ψ hΨ, orderOf_xs]
  have hSE : IsStronglyEmbeddedOrder Ψ.range :=
    Recog.isStronglyEmbeddedOrder_of_centralizer_le_of_unique hM hC S hSM hzS hz2 hzc huniq
  have hcM : Φ (cV0 : Shat) ∈ Ψ.range := by
    rw [hΨr]
    exact ⟨_, rfl⟩
  have hc2 : orderOf (Φ (cV0 : Shat)) = 2 := by
    rw [orderOf_injective Φ hΦ, Subgroup.orderOf_coe, orderOf_cV0]
  obtain ⟨-, hconj, hfus⟩ := isStronglyEmbeddedOrder_fusion hSE
  obtain ⟨m, hm, hmc⟩ := hfus _ hcM _ (hSM hzS) hc2 (hconj _ hcM _ (hSM hzS) hc2 hz2)
  rw [hΨr] at hm
  obtain ⟨s, rfl⟩ := hm
  exact conj_cV0_ne_sEquiv_xs s (hΦ (by rw [map_mul, map_mul, map_inv, hmc, hΨx]))

theorem nonempty_mulEquiv_B_of_range_eq_top
    (Φ : Shat →* G) (hΦ : Function.Injective Φ)
    (htop : Φ.range = ⊤) : Nonempty (G ≃* NativeSporadic.B) :=
  ⟨(MulEquiv.ofBijective Φ ⟨hΦ, MonoidHom.range_eq_top.1 htop⟩).symm.trans shatEquivB⟩

theorem nonempty_mulEquiv_B_of_centralizer_le
    [Finite G] (Φ : Shat →* G)
    (hΦ : Φ (cV0 : Shat) ≠ 1)
    (hC : ∀ t ∈ Φ.range, orderOf t = 2 → Subgroup.centralizer {t} ≤ Φ.range) :
    Nonempty (G ≃* NativeSporadic.B) :=
  nonempty_mulEquiv_B_of_range_eq_top Φ (injective_of_map_cV0_ne_one Φ hΦ)
    (range_eq_top_of_centralizer_le Φ (injective_of_map_cV0_ne_one Φ hΦ) hC)

theorem gside_reduction
    [Finite G] (d₀ : NativeSporadic.B) (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860) {d : G}
    (φ : Subgroup.centralizer {d} ≃* Subgroup.centralizer {d₀})
    (φe : cvSetStab {cv0, cw0} →* G) (φt : ∀ j, cvSetStab {cv0, cw0, cu j} →* G)
    (hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}),
      psiInvHom (psiOf hd₀ hrank φ) ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0, cu j}),
      psiInvHom (psiOf hd₀ hrank φ) ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ cvSetStab {cv0, cw0}) (hb : a ∈ cvSetStab {cv0, cw0, cu j}),
      φe ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (hC : ∀ Φ : Shat →* G, (∀ a : vStab cv0, Φ a = psiInvHom (psiOf hd₀ hrank φ) a) →
      (∀ a : cvSetStab {cv0, cw0}, Φ a = φe a) →
      (∀ j (a : cvSetStab {cv0, cw0, cu j}), Φ a = φt j a) →
      ∀ t ∈ Φ.range, orderOf t = 2 → Subgroup.centralizer {t} ≤ Φ.range) :
    Nonempty (G ≃* NativeSporadic.B) := by
  obtain ⟨Φ, hΦ, hΦv, hΦe, hΦt⟩ := exists_injective_completion _
    (psiInvHom_injective (psiOf hd₀ hrank φ)) φe φt hve hvt het
  exact nonempty_mulEquiv_B_of_range_eq_top Φ hΦ
    (range_eq_top_of_centralizer_le Φ hΦ (hC Φ hΦv hΦe hΦt))

end CFSG.Monster.B.GSide
