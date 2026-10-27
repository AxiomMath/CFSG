module

public import CFSG.Quasithin.Vol2.Ch11SecA15Inner
public import CFSG.Quasithin.Vol2.Ch11SecA15Excl
public import CFSG.Quasithin.Vol2.Ch11SecA15Z1c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem exp2_omegaOneCenterOf (X : Subgroup G) : ∀ z ∈ omegaOneCenterOf X, z * z = 1 := by
  intro z hz
  have hle : omegaOneCenterOf X ≤ centerOf X :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1
  induction hz using Subgroup.closure_induction with
  | mem x hx => rw [← sq]; exact hx.2
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab : a * b = b * a := Subgroup.mem_centralizer_iff.mp (hle hb).2 a (hle ha).1
    calc a * b * (a * b) = a * a * (b * b) := by
          rw [mul_assoc, ← mul_assoc b, ← hab]; group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha =>
    rw [← mul_inv_rev, iha, inv_one]

theorem conj_mem_centerOf {X : Subgroup G} {y s : G} (hy : y ∈ Subgroup.normalizer (X : Set G))
    (hs : s ∈ centerOf X) : y * s * y⁻¹ ∈ centerOf X := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hy s).mp hs.1,
    Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have hx' : y⁻¹ * x * y ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) x).mp hx
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hs.2 _ hx'
  calc x * (y * s * y⁻¹) = y * ((y⁻¹ * x * y) * s) * y⁻¹ := by group
    _ = y * (s * (y⁻¹ * x * y)) * y⁻¹ := by rw [h1]
    _ = y * s * y⁻¹ * x := by group

theorem normalizer_le_normalizer_omegaOneCenterOf (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (omegaOneCenterOf X : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, omegaOneCenterOf, omegaOneOf,
    MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨s, ⟨hs, hs2⟩, rfl⟩
    change y * s * y⁻¹ ∈ centerOf X ∧ (y * s * y⁻¹) ^ 2 = 1
    exact ⟨conj_mem_centerOf hy hs, by rw [conj_pow, hs2]; group⟩
  · rintro ⟨hx, hx2⟩
    refine ⟨y⁻¹ * x * y, ⟨?_, ?_⟩, ?_⟩
    · have := conj_mem_centerOf (Subgroup.inv_mem _ hy) hx
      simpa using this
    · have : (y⁻¹ * x * y) ^ 2 = y⁻¹ * x ^ 2 * y := by
        rw [show y⁻¹ * x * y = y⁻¹ * x * y⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
      rw [this, hx2]
      group
    · change y * (y⁻¹ * x * y) * y⁻¹ = x
      group

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem kind_of_block (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hB : IsSL3Block L ∨ IsSp4Block L) :
    KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n := by
  rcases hB with ⟨-, m, F, _, _, hF, α, hα, hker, -⟩ | ⟨-, F, _, _, hF, α, hα, hker, -⟩
  · exact Or.inl (kindSL3_of_modO2Surj hG2 h1102 h hF ⟨hα, hker⟩).1
  · exact Or.inr (kindSp4_of_modO2Surj hG2 h1102 h (m := 2) (by rw [hF]; norm_num)
      ⟨hα, hker⟩).1

theorem V1_le_Z1 (hFc : Facts15c) (hF11 : Facts11) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) :
    V₁ ≤ omegaOneCenterOf (ROf T L V₁) := by
  intro u hu
  have huV := IsVi.le_fsuV hU hu
  refine Subgroup.subset_closure ⟨⟨fsuV_le_ROf h huV, Subgroup.mem_centralizer_iff.mpr
    fun r hr => ?_⟩, (isElemAbelian_fsuV h).2 u huV⟩
  exact (Subgroup.mem_centralizer_iff.mp
    (ROf_le_centralizer_V1' hFc hF11 hG2 h1102 h hU hk hr) u hu).symm

theorem inv_mul_mem_zC (hFc : Facts15c) (hF11 : Facts11) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) {z u : G}
    (hz : z ∈ centerOf (ROf T L V₁)) (hz2 : z ^ 2 = 1) (hu : u ∈ V₁)
    (hc : u⁻¹ * z ∈ Subgroup.centralizer (L : Set G)) :
    u⁻¹ * z ∈ omegaOneCenterOf (ROf T L V₁) ⊓ Subgroup.centralizer (L : Set G) := by
  have huZ := V1_le_Z1 hFc hF11 hG2 h1102 h hU hk hu
  have huc := (Subgroup.closure_le _).mpr (fun x hx => hx.1) huZ
  have huz : u * z = z * u := Subgroup.mem_centralizer_iff.mp hz.2 u huc.1
  refine ⟨Subgroup.subset_closure ⟨⟨(ROf T L V₁).mul_mem ((ROf T L V₁).inv_mem huc.1) hz.1,
    Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩, ?_⟩, hc⟩
  · have h1 := Subgroup.mem_centralizer_iff.mp huc.2 r hr
    have h2 := Subgroup.mem_centralizer_iff.mp hz.2 r hr
    calc r * (u⁻¹ * z) = u⁻¹ * (u * r) * u⁻¹ * z := by group
      _ = u⁻¹ * (r * u) * u⁻¹ * z := by rw [h1]
      _ = u⁻¹ * (r * z) := by group
      _ = u⁻¹ * (z * r) := by rw [h2]
      _ = u⁻¹ * z * r := by group
  · have hu2 : u ^ 2 = 1 := (isElemAbelian_fsuV h).2 u (IsVi.le_fsuV hU hu)
    have hcomm' : z * u⁻¹ = u⁻¹ * z := by
      calc z * u⁻¹ = u⁻¹ * (u * z) * u⁻¹ := by group
        _ = u⁻¹ * (z * u) * u⁻¹ := by rw [huz]
        _ = u⁻¹ * z := by group
    calc (u⁻¹ * z) ^ 2 = u⁻¹ * (z * u⁻¹) * z := by rw [sq]; group
      _ = u⁻¹ * (u⁻¹ * z) * z := by rw [hcomm']
      _ = (u * u)⁻¹ * (z * z) := by group
      _ = 1 := by rw [← sq, ← sq, hu2, hz2]; group

theorem Z1_le_sup (hF : Facts15) (hFc : Facts15c) (hF11 : Facts11) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hB : IsSL3Block L ∨ IsSp4Block L) :
    omegaOneCenterOf (ROf T L V₁) ≤
      V₁ ⊔ (omegaOneCenterOf (ROf T L V₁) ⊓ Subgroup.centralizer (L : Set G)) := by
  have hk := kind_of_block hG2 h1102 h hB
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨hz, hz2⟩
  rcases hB with hB | hB
  · have hkS : KindSL3 L (fsuV T I) n := by
      obtain ⟨-, m, F, _, _, hF, α, hα, hker, -⟩ := hB
      exact (kindSL3_of_modO2Surj hG2 h1102 h hF ⟨hα, hker⟩).1
    have hCV := cV_eq_bot_of_kindSL3 hG2 h1103 h hkS
    obtain ⟨u₀, hu₀, hc⟩ := exists_blockU_of_sl3Block hG2 h1102 h hB hz
    have hmem : u₀ ∈ ((fsuV T I ⊔ blockZ L : Subgroup G) : Set G) := by
      rw [fsuV_sup_blockZ h1102 h hB.1]; exact hu₀
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      ((blockZ_le_centralizer_fsuV h1102 h hB.1).trans
        (Subgroup.centralizer_le_normalizer _))] at hmem
    obtain ⟨v, hv, c₀, hc₀, rfl⟩ := hmem
    have hvc : v⁻¹ * z ∈ Subgroup.centralizer (L : Set G) := by
      have e : v⁻¹ * z = c₀ * ((v * c₀)⁻¹ * z) := by group
      rw [e]
      exact Subgroup.mul_mem _ hc₀.2 hc
    have hvV₁ : v ∈ V₁ := mem_V1_of_fixed hF h1102 h hU hv fun r hr => by
      have hrT := ROf_le_T h hr
      have hrz : r * z * r⁻¹ = z := by
        rw [Subgroup.mem_centralizer_iff.mp hz.2 r hr, mul_inv_cancel_right]
      have hrc : r * (v⁻¹ * z) * r⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer (h.normal hrT)) _).mp hvc
      have hrv : r * v * r⁻¹ ∈ fsuV T I :=
        (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_fsuV T I hrT) v).mp hv
      have e : v⁻¹ * (r * v * r⁻¹) = (v⁻¹ * z) * (r * (v⁻¹ * z) * r⁻¹)⁻¹ := by
        calc v⁻¹ * (r * v * r⁻¹) = v⁻¹ * (r * z * r⁻¹) * (r * (v⁻¹ * z) * r⁻¹)⁻¹ := by group
          _ = (v⁻¹ * z) * (r * (v⁻¹ * z) * r⁻¹)⁻¹ := by rw [hrz]
      have hmemV : v⁻¹ * (r * v * r⁻¹) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) :=
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) hrv,
          e ▸ Subgroup.mul_mem _ hvc (Subgroup.inv_mem _ hrc)⟩
      rw [hCV, Subgroup.mem_bot] at hmemV
      calc r * v * r⁻¹ = v * (v⁻¹ * (r * v * r⁻¹)) := by group
        _ = v := by rw [hmemV, mul_one]
    have hczC := inv_mul_mem_zC hFc hF11 hG2 h1102 h hU hk hz hz2 hvV₁ hvc
    have e : z = v * (v⁻¹ * z) := by group
    rw [SetLike.mem_coe, e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hvV₁) (Subgroup.mem_sup_right hczC)
  · obtain ⟨u, hu, hc⟩ := exists_V1_of_sp4Block hFc hG2 h1102 h hU hB hz
    have hczC := inv_mul_mem_zC hFc hF11 hG2 h1102 h hU hk hz hz2 hu hc
    have e : z = u * (u⁻¹ * z) := by group
    rw [SetLike.mem_coe, e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hczC)

theorem zC_ne_bot (h : Hyp11 G T L I n) (hC : T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    omegaOneCenterOf (ROf T L V₁) ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 T := h.fsu.sylow.1
  set U := T ⊓ Subgroup.centralizer (L : Set G) with hUdef
  have hUn : T ≤ Subgroup.normalizer (U : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, mem_normalizer_centralizer (h.normal ht)⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hUT : U ≤ T := inf_le_left
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h0
    apply hC
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h0, Subgroup.map_bot]
  have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hW2 : IsPGroup 2 ↥(U.subgroupOf T ⊓ Subgroup.center ↥T) := hT.to_subgroup _
  have hcard : 2 ∣ Nat.card ↥(U.subgroupOf T ⊓ Subgroup.center ↥T) := by
    rcases hW2.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hW
    · exact h1
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(U.subgroupOf T ⊓ Subgroup.center ↥T))
    2 hcard
  set y : G := ((g : ↥T) : G) with hy
  have hyU : y ∈ U := Subgroup.mem_subgroupOf.mp g.2.1
  have hyZ : ∀ t ∈ T, t * y = y * t := fun t ht => by
    have := Subgroup.mem_center_iff.mp g.2.2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  have hy2 : orderOf y = 2 := by
    rw [hy, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]
  rw [Ne, eq_bot_iff, IsConcreteLE.not_le_iff_exists]
  refine ⟨y, ⟨Subgroup.subset_closure ⟨⟨inf_centralizer_le_ROf h hyU,
    Subgroup.mem_centralizer_iff.mpr fun r hr => hyZ r (ROf_le_T h hr)⟩, ?_⟩, hyU.2⟩, ?_⟩
  · rw [← hy2]; exact pow_orderOf_eq_one y
  · intro h1
    rw [Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)

end CFSG.Quasithin.Vol2.Ch11.SecA
