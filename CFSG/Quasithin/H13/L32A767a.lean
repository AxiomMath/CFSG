module

public import CFSG.Quasithin.H13.L32AL24

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem sl24_sq_of_fix : ∀ A : SL(2, F4), ∀ v : Fin 2 → F4, v ≠ 0 →
    (A : Matrix (Fin 2) (Fin 2) F4).mulVec v = v → A ^ 2 = 1 := by
  decide +kernel

theorem le_of_isPGroup_of_le_normalizer (h : Hyp147 G T L V) {X : Subgroup G}
    (hX : IsPGroup 2 ↥X) (hTX : T ≤ Subgroup.normalizer (X : Set G)) : X ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(T ⊔ X) := IsPGroup.to_sup_of_normal_right' h.fsu.sylow.1 hX hTX
  have h1 : T ⊔ X ≤ pCoreOf 2 (T ⊔ X) :=
    le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hp
  exact le_sup_right.trans (h1.trans (pCoreOf_le_of_le h le_sup_left))

theorem centralizer_V2_le (h : Hyp147 G T L V) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h63 : Thm14_7_63) (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂) : Subgroup.centralizer (V₂ : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz0, hz1, ha, haV, -, -⟩ := S14.exists_basis
  have haVV : a ∈ V := hV2.2.1 ha
  have haU : a ∈ fsuU T V := le_conjClosure V _ haVV
  have hau0 : a ∉ u0 T V := fun h' => haV (by
    rw [← inf_u0_eq h hMod h63 hF]
    exact Subgroup.mem_inf.mpr ⟨haVV, h'⟩)
  obtain ⟨hKU, π, β, -, hπk, -, hβk, hβe⟩ := isL24Section_u0 h hMod h63
  have hβa : Multiplicative.toAdd (β ⟨a, haU⟩) ≠ 0 := fun h0 => hau0 (by
    have h1 : β ⟨a, haU⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h0, toAdd_one]
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf] at h1
    exact h1)
  have hCH : Subgroup.centralizer (V₂ : Set G) ≤ hz T V :=
    Subgroup.centralizer_le hV2.1
  have hX2 : IsPGroup 2 ↥(Subgroup.centralizer (V₂ : Set G)) := by
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      fun {q} hq hqd => ?_)
    by_contra hq2
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hqd
    have hyo : orderOf (y : G) = q := by rw [Subgroup.orderOf_coe, hy]
    have hyodd : Odd (orderOf (y : G)) := by
      rw [hyo]
      exact hq.odd_of_ne_two hq2
    have hyK : (y : G) ∈ kz T V := mem_oTwoUpper_of_odd (hCH y.2) hyodd
    have hya : (y : G) * a * (y : G)⁻¹ = a := by
      have := Subgroup.mem_centralizer_iff.mp y.2 a ha
      rw [← this, mul_inv_cancel_right]
    have hfix : ((π ⟨y, hyK⟩ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
        (Multiplicative.toAdd (β ⟨a, haU⟩)) = Multiplicative.toAdd (β ⟨a, haU⟩) := by
      have h1 := hβe ⟨y, hyK⟩ ⟨a, haU⟩ ⟨a, haU⟩ hya.symm
      have := congrArg Multiplicative.toAdd h1
      rw [toAdd_ofAdd] at this
      exact this.symm
    have h2 := sl24_sq_of_fix _ _ hβa hfix
    have hq' : π ⟨y, hyK⟩ ^ q = 1 := by
      rw [← map_pow]
      have e : (⟨y, hyK⟩ : ↥(kz T V)) ^ q = 1 :=
        Subtype.ext (by simpa [← hyo] using pow_orderOf_eq_one (y : G))
      rw [e, map_one]
    have hπ1 : π ⟨y, hyK⟩ = 1 := by
      have hord := Nat.eq_one_of_dvd_coprimes
        ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
        (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hq')
      exact orderOf_eq_one_iff.mp hord
    have hyO : (y : G) ∈ pCoreOf 2 (kz T V) := by
      have : (⟨y, hyK⟩ : ↥(kz T V)) ∈ π.ker := hπ1
      rw [hπk, Subgroup.mem_subgroupOf] at this
      exact this
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (kz T V)) ⟨_, hyO⟩
    have hk' : (y : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hqd2 : q ∣ 2 ^ k := hyo ▸ orderOf_dvd_of_pow_eq_one hk'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqd2))
  refine le_of_isPGroup_of_le_normalizer h hX2 fun t ht => ?_
  rw [← conjSub_eq_self_iff, ← conjSub_centralizer, conjSub_eq_self_iff.mpr (hV2.2.2.1 ht)]

theorem normalizer_V2_le (h : Hyp147 G T L V) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h63 : Thm14_7_63) (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂) : Subgroup.normalizer (V₂ : Set G) ≤ L ⊔ T := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have h13322 := stmt13_3_2_two_of h1332
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz0, hz1, ha, haV, -, -⟩ := S14.exists_basis
  have hzV2 : z ∈ V₂ := hV2.1 hz0
  have hza : z ≠ a := fun e => haV (e ▸ hz0)
  have ha1 : a ≠ 1 := fun e => haV (e ▸ one_mem _)
  intro g hg
  have hgz : g * z * g⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hg z).mp hzV2
  have hga : g * a * g⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  obtain ⟨l, hl, hlz, hla⟩ := exists_conj_eq_pair (h.hyp1281One h13322 hMod) (hV2.2.1 hzV2)
    (hV2.2.1 ha) (hV2.2.1 hgz) (hV2.2.1 hga) hz1 ha1
    (fun e => hz1 (by rw [show z = g⁻¹ * (g * z * g⁻¹) * g by group, e]; group))
    (fun e => ha1 (by rw [show a = g⁻¹ * (g * a * g⁻¹) * g by group, e]; group)) hza
    (fun e => hza (by rw [show z = g⁻¹ * (g * z * g⁻¹) * g by group, e]; group))
  have hc : l⁻¹ * g ∈ Subgroup.centralizer (V₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    have hcz : z * (l⁻¹ * g) = (l⁻¹ * g) * z := by
      calc z * (l⁻¹ * g) = l⁻¹ * (l * z * l⁻¹) * g := by group
        _ = l⁻¹ * (g * z * g⁻¹) * g := by rw [hlz]
        _ = (l⁻¹ * g) * z := by group
    have hca : a * (l⁻¹ * g) = (l⁻¹ * g) * a := by
      calc a * (l⁻¹ * g) = l⁻¹ * (l * a * l⁻¹) * g := by group
        _ = l⁻¹ * (g * a * g⁻¹) * g := by rw [hla]
        _ = (l⁻¹ * g) * a := by group
    have hca' : a⁻¹ * (l⁻¹ * g) = (l⁻¹ * g) * a⁻¹ := by
      calc a⁻¹ * (l⁻¹ * g) = a⁻¹ * ((l⁻¹ * g) * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * (l⁻¹ * g)) * a⁻¹ := by rw [hca]
        _ = (l⁻¹ * g) * a⁻¹ := by group
    intro v hv
    rcases S14.mem_V2 ha haV hv with h1 | h1
    · rcases S14.eq_of_mem_V1 hz0 hz1 h1 with rfl | rfl
      · group
      · exact hcz
    · rcases S14.eq_of_mem_V1 hz0 hz1 h1 with h2 | h2
      · rw [eq_inv_of_mul_eq_one_right h2]
        exact hca'
      · have : v = a⁻¹ * z := by rw [← h2]; group
        rw [this]
        calc a⁻¹ * z * (l⁻¹ * g) = a⁻¹ * (z * (l⁻¹ * g)) := by group
          _ = a⁻¹ * ((l⁻¹ * g) * z) := by rw [hcz]
          _ = (a⁻¹ * (l⁻¹ * g)) * z := by group
          _ = ((l⁻¹ * g) * a⁻¹) * z := by rw [hca']
          _ = (l⁻¹ * g) * (a⁻¹ * z) := by group
  have hcT := centralizer_V2_le h h1222 h1332 h1334 h63 hF hV2 hc
  rw [show g = l * (l⁻¹ * g) by group]
  exact mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hcT)

theorem normalizer_V_eq (h : Hyp147 G T L V) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h63 : Thm14_7_63) (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) :
    L ⊔ T = Subgroup.normalizer (V : Set G) := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨-, -, hLTV, -, -⟩ := hMod G T L V h.hyp h.fsu
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  refine le_antisymm hLTV fun g hg => ?_
  obtain ⟨l, hl, hlv⟩ := exists_conj_of_autOn_eq_top
    (autOn_eq_top_of_hyp1281One (h.hyp1281One h13322 hMod))
    (V.normalizerMonoidHom ⟨g, hg⟩)
  have hc : l⁻¹ * g ∈ Subgroup.centralizer (V₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := hlv ⟨v, hV2.2.1 hv⟩
    rw [V.normalizerMonoidHom_apply_apply_coe] at h1
    calc v * (l⁻¹ * g) = l⁻¹ * (l * v * l⁻¹) * g := by group
      _ = l⁻¹ * (g * v * g⁻¹) * g := by rw [h1]
      _ = (l⁻¹ * g) * v := by group
  have hcT := centralizer_V2_le h h1222 h1332 h1334 h63 hF hV2 hc
  rw [show g = l * (l⁻¹ * g) by group]
  exact mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hcT)

omit [Finite G] in
theorem exists_two_of_card_four {F : Subgroup G} (hF : Nat.card ↥F = 4) :
    ∃ f₁ ∈ F, ∃ f₂ ∈ F, f₁ ≠ 1 ∧ f₂ ≠ 1 ∧ f₁ ≠ f₂ := by
  have hfin : Finite ↥F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  by_contra hne
  push Not at hne
  obtain ⟨f₁, hf₁, hf₁1⟩ : ∃ f₁ ∈ F, f₁ ≠ 1 := by
    by_contra h0
    push Not at h0
    have : F = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h0
    rw [this, Subgroup.card_bot] at hF
    omega
  have hsub : (F : Set G) ⊆ {1, f₁} := fun f hf => by
    by_cases hf1 : f = 1
    · exact Or.inl hf1
    · exact Or.inr (hne f₁ hf₁ f hf hf₁1 hf1).symm
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_insert_le (1 : G) {f₁}
  rw [Set.ncard_singleton] at h2
  rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hF] at h1
  omega

theorem exists_conj_V2 (h : Hyp147 G T L V) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂) {F : Subgroup G}
    (hFV : F ≤ V) (hF4 : Nat.card ↥F = 4) : ∃ l ∈ L, conjSub l V₂ = F := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have h13322 := stmt13_3_2_two_of h1332
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz0, hz1, ha, haV, -, -⟩ := S14.exists_basis
  have hzV2 : z ∈ V₂ := hV2.1 hz0
  have hza : z ≠ a := fun e => haV (e ▸ hz0)
  have ha1 : a ≠ 1 := fun e => haV (e ▸ one_mem _)
  obtain ⟨f₁, hf₁, f₂, hf₂, hf₁1, hf₂1, hf₁₂⟩ := exists_two_of_card_four hF4
  obtain ⟨l, hl, hlz, hla⟩ := exists_conj_eq_pair (h.hyp1281One h13322 hMod) (hV2.2.1 hzV2)
    (hV2.2.1 ha) (hFV hf₁) (hFV hf₂) hz1 ha1 hf₁1 hf₂1 hza hf₁₂
  refine ⟨l, hl, (Subgroup.eq_of_le_of_card_ge ?_ ?_)⟩
  · intro w hw
    rw [mem_conjSub] at hw
    have hv := hw
    set v := l⁻¹ * w * l with hvdef
    have hw' : w = l * v * l⁻¹ := by rw [hvdef]; group
    rw [hw']
    rcases S14.mem_V2 ha haV hv with h1 | h1
    · rcases S14.eq_of_mem_V1 hz0 hz1 h1 with h2 | h2
      · rw [h2]; simp
      · rw [h2, hlz]; exact hf₁
    · rcases S14.eq_of_mem_V1 hz0 hz1 h1 with h2 | h2
      · rw [eq_inv_of_mul_eq_one_right h2, show l * a⁻¹ * l⁻¹ = (l * a * l⁻¹)⁻¹ by group, hla]
        exact inv_mem hf₂
      · rw [show v = a⁻¹ * z by rw [← h2]; group,
          show l * (a⁻¹ * z) * l⁻¹ = (l * a * l⁻¹)⁻¹ * (l * z * l⁻¹) by group, hla, hlz]
        exact mul_mem (inv_mem hf₂) hf₁
  · rw [hF4, conjSub, Subgroup.card_map_of_injective (MulAut.conj l).injective, hV2.2.2.2]

theorem conjSub_V_eq (h : Hyp147 G T L V) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h63 : Thm14_7_63) (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card ↥F = 4) {g : G} (hFg : F ≤ conjSub g V) :
    conjSub g V = V := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨-, -, hLTV, -, -⟩ := hMod G T L V h.hyp h.fsu
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have hF' : conjSub g⁻¹ F ≤ V := (conjSub_le_iff g⁻¹ ).mpr (by rwa [inv_inv])
  have hF'4 : Nat.card ↥(conjSub g⁻¹ F) = 4 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hF4]
  obtain ⟨l₁, hl₁, hl₁F⟩ := exists_conj_V2 h h1222 h1332 h1334 hV2 hFV hF4
  obtain ⟨l₂, hl₂, hl₂F⟩ := exists_conj_V2 h h1222 h1332 h1334 hV2 hF' hF'4
  have hn : l₁⁻¹ * g * l₂ ∈ Subgroup.normalizer (V₂ : Set G) := by
    rw [← conjSub_eq_self_iff, conjSub_mul, hl₂F, ← conjSub_mul,
      show l₁⁻¹ * g * g⁻¹ = l₁⁻¹ by group, ← hl₁F, conjSub_conjSub_inv]
  have hnV := hLTV (normalizer_V2_le h h1222 h1332 h1334 h63 hF hV2 hn)
  have hl₁V := hLTV (Subgroup.mem_sup_left hl₁)
  have hl₂V := hLTV (Subgroup.mem_sup_left hl₂)
  have e : g = l₁ * (l₁⁻¹ * g * l₂) * l₂⁻¹ := by group
  rw [e, conjSub_eq_self_iff]
  exact mul_mem (mul_mem hl₁V hnV) (inv_mem hl₂V)

theorem lemma14_7_67_one_two_five (h : Hyp147 G T L V) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) :
    (∀ V₂ : Subgroup G, A6.IsV2 T V V₂ →
      Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
    (∀ F : Subgroup G, F ≤ V → Nat.card F = 4 → ∀ g : G, F ≤ conjSub g V → conjSub g V = V) ∧
    L ⊔ T = Subgroup.normalizer (V : Set G) := by
  have h13322 := stmt13_3_2_two_of h1332
  refine ⟨fun V₂ hV2 => (normalizer_V2_le h h1222 h1332 h1334 h63 hF hV2).trans
      (sup_le Subgroup.le_normalizer fun t ht => h.normalizes h13322 ht),
    fun F hFV hF4 g hFg => conjSub_V_eq h h1222 h1332 h1334 h63 hF hFV hF4 hFg,
    normalizer_V_eq h h1222 h1332 h1334 h63 hF⟩

end CFSG.Quasithin.H13.L32A
