module

public import CFSG.Quasithin.Vol2.E2SevenKG7Bender
public import CFSG.Quasithin.Vol2.Ch3E213MP6BI
public import CFSG.Quasithin.Vol2.E2SevenKG7Data

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp antiUnipotent
  antiUnipotentCenter uElt minorAut)
open CFSG.Quasithin.SteinbergBS (rootLong rootShort)

namespace E2

open Ch3E213M

variable {G : Type} [Group G] [Finite G]

theorem isSp4Prime_oTwoUpper_star {X T M K : Subgroup G} (hP : MinParabolic X T M)
    (hker : kerIn M X = ⊥) (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set G))
    (hC : X ⊓ Subgroup.centralizer (K : Set G) = ⊥) (hKT : K ⊔ T = X) {n : ℕ}
    (hSp : IsSp4Prime n ↥K) : IsSp4Prime n ↥(oTwoUpper (⊤ : Subgroup (StarQuot M X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsK := isSimpleGroup_of_isSp4Prime hSp
  obtain ⟨a, b, hab⟩ := (asHyp_subgroupOf hP hKX hXN hC hKT hsK).nonab
  set eK := Subgroup.subgroupOfEquivOfLe hKX
  have hab' : eK a * eK b ≠ eK b * eK a := fun h => hab (eK.injective (by rw [map_mul, map_mul, h]))
  have hKK : K = oTwoUpper K := by
    refine le_antisymm ?_ (oTwoUpper_le K)
    have hN : ((oTwoUpper K).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le K)).mpr
        (le_normalizer_oTwoUpper K)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((oTwoUpper K).subgroupOf K) with hb | ht
    · exfalso
      have h2 : IsPGroup 2 ↥K := fun x => by
        obtain ⟨j, hj⟩ := exists_pow_mem_oTwoUpper K x.2
        have hx : x ^ 2 ^ j ∈ (oTwoUpper K).subgroupOf K := by
          rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
          exact hj
        rw [hb, Subgroup.mem_bot] at hx
        exact ⟨j, hx⟩
      have : Nontrivial ↥K := ⟨⟨eK a * eK b, eK b * eK a, hab'⟩⟩
      have hZ := h2.center_nontrivial
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with hz | hz
      · rw [hz] at hZ
        exact (Subgroup.nontrivial_iff_ne_bot _).mp hZ rfl
      · apply hab'
        have hc : eK b ∈ Subgroup.center ↥K := hz ▸ Subgroup.mem_top _
        exact Subgroup.mem_center_iff.mp hc (eK a)
    · intro x hx
      have hx' : (⟨x, hx⟩ : ↥K) ∈ (oTwoUpper K).subgroupOf K := ht ▸ Subgroup.mem_top _
      exact hx'
  have hKn : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN
  have hT2 : IsPGroup 2 (T.subgroupOf X) := hP.isSylow.2.1.comap_subtype
  have hXK : K = oTwoUpper X := by
    refine eq_oTwoUpper_of_pow_mem hKX (fun x hx => ?_) hKK
    obtain ⟨j, hj⟩ := Ch3E213M.exists_two_pow_mem_of_sup_eq_top hT2
      (Ch3E213M.subgroupOf_sup_eq_top hKT.symm) (⟨x, hx⟩ : ↥X)
    exact ⟨j, by simpa [Subgroup.mem_subgroupOf] using hj⟩
  have := E2P.finite_starQuot M X
  let e : StarQuot M X ≃* ↥X :=
    (QuotientGroup.quotientMulEquivOfEq (by rw [hker, Subgroup.bot_subgroupOf])).trans
      QuotientGroup.quotientBot
  have hmap : (oTwoUpper (⊤ : Subgroup (StarQuot M X))).map e.toMonoidHom =
      oTwoUpper (⊤ : Subgroup ↥X) := by
    rw [← oTwoUpper_map, Subgroup.map_top_of_surjective _ e.surjective]
  have hmapX : (oTwoUpper (⊤ : Subgroup ↥X)).map X.subtype = K := by
    rw [← oTwoUpper_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype, ← hXK]
  exact isSp4Prime_of_mulEquiv (((e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)).trans
    (((oTwoUpper (⊤ : Subgroup ↥X)).equivMapOfInjective X.subtype X.subtype_injective).trans
      (MulEquiv.subgroupCongr hmapX))) hSp

variable {X T M V K : Subgroup G} {k : Type} [Field k] [Finite k] [CharP k 2]

omit [Finite G] in
theorem le_of_sp4Data (D : Sp4Data X T M V K k) (hker : kerIn M X = ⊥) (hMX : M ≤ X)
    (hVX : V ≤ X) : V ≤ K := by
  intro v hv
  have h1 : QuotientGroup.mk' (kerIn (M.subgroupOf X) ⊤) (⟨v, hVX hv⟩ : ↥X) ∈ barIn M X K := by
    rw [← D.kZero_eq]
    exact D.V_le ⟨⟨v, hVX hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
  obtain ⟨x, hx, hxe⟩ := h1
  rw [mk'_kerIn_injective hker hMX hxe] at hx
  exact Subgroup.mem_subgroupOf.mp hx

theorem swap_data_of_hyp (h : Hyp28 X T M V) (D : Sp4Data X T M V K k) :
    ∃ (g : antiSp k) (r : ℕ), IsUpper g ∧
      ∀ w ∈ coordIn D.θ V, (MulAut.conj g * minorAut k ^ (2 * r + 1)) w ∈ coordIn D.θ V := by
  obtain ⟨s, hs, g, j, hj, hact, -⟩ := D.swap
  obtain ⟨r, rfl⟩ := hj
  have hU : ∀ u ∈ antiUnipotent k,
      (MulAut.conj g * minorAut k ^ (2 * r + 1)) u ∈ antiUnipotent k := by
    rw [← D.sylow]
    exact P6B.mem_coordIn_of_swap D hs hact Subgroup.le_normalizer
  have hUeq : (antiUnipotent k).map (MulAut.conj g * minorAut k ^ (2 * r + 1)).toMonoidHom =
      antiUnipotent k :=
    SteinbergBS.map_eq_of_map_le (by rintro _ ⟨u, hu, rfl⟩; exact hU u hu) le_rfl
  exact ⟨g, r, SteinbergBS.upper_of_mem_normalizer
    (SteinbergBS.mem_normalizer_of_conj_mul_pow hUeq), P6B.mem_coordIn_of_swap D hs hact h.normal_T⟩

omit [Finite G] in
theorem exists_zl_zs_of_inf_rootLong (D : Sp4Data X T M V K k)
    (hl : coordIn D.θ V ⊓ rootLong k ≠ ⊥) :
    ∃ t b : k, t ≠ 0 ∧ b ≠ 0 ∧ uElt 0 0 t 0 ∈ coordIn D.θ V ∧ uElt 0 b 0 0 ∈ coordIn D.θ V := by
  obtain ⟨⟨x, hxW, t, rfl⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hl
  have ht : t ≠ 0 := by
    rintro rfl
    apply hx1
    apply Subtype.ext
    exact CFSG.QuasithinUnique.Setup.X7b.uElt_zero_eq_one
  obtain ⟨-, -, h, j, -, -, -, -, hsw⟩ := D.swap
  have h1 : (MulAut.conj h * minorAut k ^ j) (uElt 0 0 t 0) ∈
      coordIn D.θ V ⊓ rootShort k := by
    rw [← hsw]
    exact ⟨_, ⟨hxW, t, rfl⟩, rfl⟩
  obtain ⟨b, hb⟩ := h1.2
  have hbne : b ≠ 0 := by
    rintro rfl
    have h2 : (MulAut.conj h * minorAut k ^ j) (uElt 0 0 t 0) =
        (MulAut.conj h * minorAut k ^ j) 1 := by
      rw [hb, map_one]
      exact CFSG.QuasithinUnique.Setup.X7b.uElt_zero_eq_one
    exact ht (uElt_long_eq_one ((MulAut.conj h * minorAut k ^ j).injective h2))
  exact ⟨t, b, ht, hbne, hxW, hb ▸ h1.1⟩

theorem exists_isInIHTVC_sp4_two_le (hKG2L2 : KGBenderSubL2)
    (hKG2Sz : KGBenderSubSz) (hIrr : IrrStatement) (hG41 : FactSp4TransvW)
    (hCTwo : FactSp4CTwo) (h : Hyp28 X T M V) (hker : kerIn M X = ⊥) (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hC : X ⊓ Subgroup.centralizer (K : Set G) = ⊥)
    (hKT : K ⊔ T = X) {n : ℕ} (hn : 2 ≤ n) (hSp : IsSp4Prime n ↥K)
    (hMK : M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hnX : E1.nParam X = n) (hV4 : 4 ≤ Nat.card V) :
    ∃ I : Subgroup G, ASInputs.IsInIHTVC X T M V I := by
  have hmp := h.minParabolic
  have hMX : M ≤ X := hmp.maximal.1.le
  have hTX : T ≤ X := hmp.isSylow.1
  have hVX : V ≤ X := h.le_H
  have hV : IsElemAbelian 2 V := h.elem
  obtain ⟨k, _, _, _, hk, ⟨D⟩⟩ := exists_sp4Data_of_kg7 h hker hKX hXN hC hKT hn hSp hV4
  obtain ⟨φ, hφ, hrange, hcomap⟩ := exists_coordEmb D hker hMX hKX
  obtain ⟨hT, hM⟩ := comap_coordEmb_M D hφ hrange hcomap hTX hMK
  have hφX : φ.range ≤ X := hrange ▸ hKX
  have hVr : V ≤ φ.range := hrange ▸ le_of_sp4Data D hker hMX hVX
  have hW : V.comap φ = coordIn D.θ V := hcomap V hVX
  have hWZ : V.comap φ ≤ antiUnipotentCenter k := hW ▸ D.V_le_center
  have hSpX := isSp4Prime_oTwoUpper_star hmp hker hKX hXN hC hKT hSp
  by_cases hdiag : ∃ μ : k, μ ≠ 0 ∧ coordIn D.θ V ≤ zLine 1 μ
  · obtain ⟨μ, hμ, hle⟩ := hdiag
    exact exists_isInIHTVC_of_diag hKG2L2 hKG2Sz hφ hφX hT hM hVr hWZ hk hn hμ (hW ▸ hle) hV
      hV4 hnX
  push Not at hdiag
  have hsp := P6B.spansCenter_coordIn D hdiag
  have hsub : ∀ (F₀ : Subfield k) (c g : antiSp k), IsUpper c →
      g ∈ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom →
      coordIn D.θ V ⊔ (coordIn D.θ V).map (MulAut.conj g).toMonoidHom =
        (subfieldSp F₀).map (MulAut.conj c).toMonoidHom →
      ∃ I : Subgroup G, ASInputs.IsInIHTVC X T M V I := by
    intro F₀ c g hc hgY hY
    obtain ⟨m, d, hm1, hF₀, hnd⟩ := exists_card_subfield hk F₀
    exact ⟨_, isInIHTVC_of_subfieldSp hφ hφX hT hM hVr hc hgY (hW ▸ hY) hWZ (hW ▸ hsp)
      ⟨n, hSpX⟩ hF₀ hm1 ⟨d, by rw [hnX, hnd]⟩⟩
  by_cases hl : coordIn D.θ V ⊓ rootLong k = ⊥
  ·
    obtain ⟨g₀, r, hg₀, hσ⟩ := swap_data_of_hyp h D
    rcases P6B.exists_member_or_suzuki hG41 hCTwo hn hk D.V_le_center hl hsp hg₀ hσ with
      ⟨F₀, c, g, hc, hgY, hY⟩ | ⟨F₀, a, ha, hcard, d, hd, hWs⟩
    · exact hsub F₀ c g hc hgY hY
    · obtain ⟨m, e, -, hF₀, hne⟩ := exists_card_subfield hk F₀
      have hma : m = 2 * a + 1 := Nat.pow_right_injective le_rfl (hF₀.symm.trans hcard)
      exact exists_isInIHTVC_of_sz hKG2L2 hKG2Sz hφ hφX hT hM hVr hWZ ha hcard hd (hW ▸ hWs) hV
        hV4 ⟨e, by rw [hnX, hne, hma]⟩
  ·
    obtain ⟨t, b, ht, hb, hxW, hsb⟩ := exists_zl_zs_of_inf_rootLong D hl
    obtain ⟨F₀, c, g, hc, hgY, hY⟩ :=
      exists_subfieldSp_member hIrr hG41 hk D.V_le_center hsp ht hb hxW hsb
    exact hsub F₀ c g hc hgY hY

end E2

end CFSG.Quasithin
