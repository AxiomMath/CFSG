module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6L1

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_three {X : Type*} [Group X] [Finite X] {x y : X} (hx : orderOf x = 3)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x * x := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hx] at hy
  simp only [Finset.mem_image, Finset.mem_range] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  interval_cases k <;> simp [pow_two]

theorem exists_conj_mem_sylow {X : Type*} [Group X] [Finite X] (P : Sylow 3 X) {x : X}
    (hx : x * x * x = 1) : ∃ k : X, k * x * k⁻¹ ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by rw [pow_three', hx]
  have hp : IsPGroup 3 (Subgroup.zpowers x) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq X Q P
  refine ⟨k, ?_⟩
  rw [← hk]
  have hxQ : x ∈ Q := hQ (Subgroup.mem_zpowers x)
  have h1 : k * x * k⁻¹ ∈ ((k • Q : Sylow 3 X) : Set X) := by
    rw [Sylow.coe_smul]
    exact ⟨x, hxQ, rfl⟩
  exact h1

omit [Finite G] in
theorem centralizer_conjSub (g : G) (X : Subgroup G) :
    Subgroup.centralizer (B6.conjSub g X : Set G) =
      B6.conjSub g (Subgroup.centralizer (X : Set G)) := by
  ext x
  rw [B6.mem_conjSub, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have h1 := h (g * y * g⁻¹) (by rw [SetLike.mem_coe, B6.mem_conjSub]; simpa [mul_assoc] using hy)
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * x * g) * y := by group
  · intro h y hy
    rw [SetLike.mem_coe, B6.mem_conjSub] at hy
    have h1 := h _ hy
    calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = x * y := by group

theorem oTwoUpper_conjSub (g : G) (X : Subgroup G) :
    oTwoUpper (B6.conjSub g X) = B6.conjSub g (oTwoUpper X) :=
  oTwoUpper_map (MulAut.conj g).toMonoidHom X

omit [Finite G] in
theorem mem_normalizer_conjSub {g h : G} {X : Subgroup G}
    (hg : h⁻¹ * g * h ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (B6.conjSub h X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [B6.mem_conjSub, B6.mem_conjSub]
  have h1 := (Subgroup.mem_normalizer_iff.1 hg (h⁻¹ * x * h))
  rw [show h⁻¹ * g * h * (h⁻¹ * x * h) * (h⁻¹ * g * h)⁻¹ = h⁻¹ * (g * x * g⁻¹) * h by group] at h1
  exact h1

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem Cz_eq_NV : Subgroup.centralizer ({z} : Set G) = Subgroup.normalizer (V : Set G) := by
  rw [← c.M_eq, c.f.MN]

theorem CE_le_NV : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  rw [← c.f.MN]; exact c.CE_le_M

theorem rho_of_mem_CE (h12210 : Stmt12_2_10) (D : L3Data (autOn L V) ⊤ (fixV (autOn L V)))
    {k : G} (hk : k ∈ Subgroup.centralizer (E : Set G))
    (hkN : k ∈ Subgroup.normalizer (V : Set G)) :
    ∃ γ : Γ, D.rho γ = conjAct V ⟨k, hkN⟩ ∧ act γ (c.cv D) = c.cv D := by
  have hyp := c.cx.hyp
  obtain ⟨-, -, hMV⟩ := h12210 G T L V hyp
  have hkM : k ∈ hyp.MV := ⟨c.CE_le_M hk, hkN⟩
  have hmem : conjAct V ⟨k, hkN⟩ ∈ hyp.MVbar :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hkM)
  rw [hMV] at hmem
  have hle : autOn L V ⊔ autOn T V ≤ autOn L V := sup_le le_rfl ((le_of_eq c.Tbar).trans c.Tsyl.1)
  obtain ⟨γ, hγ⟩ := D.exists_rho (hle hmem)
  exact ⟨γ, hγ, c.act_cv_of_normalizes D hkN (Subgroup.centralizer_le_normalizer (E : Set G) hk) hγ⟩

theorem card_autOn_dvd_three (h12210 : Stmt12_2_10) {P : Subgroup G}
    (hPK : P ≤ Subgroup.centralizer (E : Set G)) (hP3 : IsPGroup 3 P) :
    Nat.card (autOn P V) ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D⟩ := c.nat.toL3Coord
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPK.trans c.CE_le_NV
  have hle : autOn P V ≤ (StabSub (c.cv D)).map D.rho := by
    intro φ hφ
    obtain ⟨⟨p, hpN⟩, hpP, rfl⟩ := Subgroup.mem_map.1 hφ
    obtain ⟨γ, hγ, hγc⟩ := c.rho_of_mem_CE h12210 D (hPK (Subgroup.mem_subgroupOf.1 hpP)) hpN
    exact ⟨γ, hγc, hγ⟩
  have h24 : Nat.card ((StabSub (c.cv D)).map D.rho) = 24 := by
    rw [Subgroup.card_map_of_injective D.rho_injective, card_StabSub (c.cv_ne D)]
  have hdvd : Nat.card (autOn P V) ∣ 24 := h24 ▸ Subgroup.card_dvd_of_le hle
  have hp : IsPGroup 3 (autOn P V) :=
    (hP3.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm).map _
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk] at hdvd ⊢
  have h1 : 3 ^ k ∣ 8 * 3 := hdvd
  exact (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 3 8)).dvd_of_dvd_mul_left h1

theorem three_sub_facts (h12210 : Stmt12_2_10) {P : Subgroup G}
    (hPK : P ≤ Subgroup.centralizer (E : Set G)) (hP3 : IsPGroup 3 P) :
    (∀ s ∈ P, ∀ s' ∈ P, s * s' * s⁻¹ * s'⁻¹ ∈ Subgroup.centralizer (V : Set G)) ∧
    (∀ s ∈ P, s * s * s ∈ Subgroup.centralizer (V : Set G)) ∧
    (∀ s ∈ P, s ∉ Subgroup.centralizer (V : Set G) → ∀ y ∈ P,
      y ∈ Subgroup.centralizer (V : Set G) ∨ s⁻¹ * y ∈ Subgroup.centralizer (V : Set G) ∨
        (s * s)⁻¹ * y ∈ Subgroup.centralizer (V : Set G)) := by
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPK.trans c.CE_le_NV
  have hcard := c.card_autOn_dvd_three h12210 hPK hP3
  set Pb := autOn P V with hPb
  have hmem : ∀ s (hs : s ∈ P), conjAct V ⟨s, hPN hs⟩ ∈ Pb := fun s hs =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
  let χ : ↥P →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion hPN)
  have hmemχ : ∀ x : ↥P, χ x ∈ Pb := fun x =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 x.2)
  have hCV : ∀ x : ↥P, χ x = 1 → (x : G) ∈ Subgroup.centralizer (V : Set G) := fun x hx =>
    A4.conjAct_eq_one_iff.1 hx
  have hord : ∀ φ ∈ Pb, φ ^ 3 = 1 := by
    intro φ hφ
    have h1 : orderOf (⟨φ, hφ⟩ : ↥Pb) ∣ 3 := (orderOf_dvd_natCard _).trans hcard
    have h2 : (⟨φ, hφ⟩ : ↥Pb) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
    exact congrArg Subtype.val h2
  have hgen : ∀ φ ∈ Pb, φ ≠ 1 → ∀ ψ ∈ Pb, ψ = 1 ∨ ψ = φ ∨ ψ = φ * φ := by
    intro φ hφ hφ1 ψ hψ
    have hφo : orderOf φ = 3 := orderOf_eq_prime (hord φ hφ) hφ1
    have hz : Subgroup.zpowers φ ≤ Pb := Subgroup.zpowers_le.2 hφ
    have hzeq : Subgroup.zpowers φ = Pb := by
      refine Subgroup.eq_of_le_of_card_ge hz ?_
      rw [Nat.card_zpowers, hφo]
      exact Nat.le_of_dvd (by norm_num) hcard
    exact mem_zpowers_three hφo (hzeq ▸ hψ)
  have hcomm : ∀ φ ∈ Pb, ∀ ψ ∈ Pb, φ * ψ = ψ * φ := by
    intro φ hφ ψ hψ
    by_cases hφ1 : φ = 1
    · rw [hφ1, one_mul, mul_one]
    rcases hgen φ hφ hφ1 ψ hψ with h | h | h <;> rw [h] <;> group
  refine ⟨fun s hs s' hs' => ?_, fun s hs => ?_, fun s hs hsV y hy => ?_⟩
  · have h1 := hCV ((⟨s, hs⟩ : ↥P) * ⟨s', hs'⟩ * (⟨s, hs⟩)⁻¹ * (⟨s', hs'⟩)⁻¹) (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm _ (hmemχ _) _ (hmemχ _)]
      group)
    exact h1
  · have h1 := hCV ((⟨s, hs⟩ : ↥P) * ⟨s, hs⟩ * ⟨s, hs⟩) (by
      rw [map_mul, map_mul, ← pow_three']
      exact hord _ (hmemχ _))
    exact h1
  · have hs1 : χ ⟨s, hs⟩ ≠ 1 := fun h => hsV (hCV _ h)
    rcases hgen _ (hmemχ ⟨s, hs⟩) hs1 _ (hmemχ ⟨y, hy⟩) with h | h | h
    · exact Or.inl (hCV _ h)
    · refine Or.inr (Or.inl ?_)
      have h1 := hCV ((⟨s, hs⟩ : ↥P)⁻¹ * ⟨y, hy⟩) (by rw [map_mul, map_inv, h, inv_mul_cancel])
      exact h1
    · refine Or.inr (Or.inr ?_)
      have h1 := hCV ((⟨s, hs⟩ * ⟨s, hs⟩ : ↥P)⁻¹ * ⟨y, hy⟩) (by
        rw [map_mul, map_inv, map_mul, h, inv_mul_cancel])
      exact h1

theorem charTwo_CE : QuasithinUnique.CharTwo (Subgroup.centralizer (E : Set G)) := by
  have hyp := c.cx.hyp
  have hE1 : E ≠ ⊥ := fun h => by
    have := c.E4
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  have hE2 : IsPGroup 2 ↥E := hyp.sylow.1.to_le (c.EV.trans c.f.le_T)
  have hloc : IsTwoLocal (Subgroup.normalizer (E : Set G)) := ⟨E, hE1, hE2, rfl⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo c.sylow
  have hNE : QuasithinUnique.CharTwo (Subgroup.normalizer (E : Set G)) :=
    c.even _ hloc ⟨S, hS ▸ c.TE⟩
  refine CT.CharTwo.of_normal hNE (Subgroup.centralizer_le_normalizer (E : Set G)) ?_
  refine ⟨fun a ha b => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  exact (Subgroup.mem_normalizer_iff.1
    (F7.normalizer_le_normalizer_centralizer E b.2) a).1 ha

theorem le_two_of_elem3 {P : Subgroup G} (hPM : P ≤ Subgroup.normalizer (L : Set G))
    (hP : IsElemAbelian 3 P) {k : ℕ} (hk : Nat.card P = 3 ^ k) : k ≤ 2 := by
  have h3 := c.sqtkM.1 3 Nat.prime_three (by norm_num)
  set P' : Subgroup ↥(Subgroup.normalizer (L : Set G)) := P.subgroupOf _ with hP'
  have hcard : Nat.card P' = 3 ^ k := by
    rw [hP', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hk]
  have hP'e : IsElemAbelian 3 P' := by
    obtain ⟨hc, he⟩ := hP
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have h1 := hc.is_comm.comm ⟨((a : ↥(Subgroup.normalizer (L : Set G))) : G), a.2⟩
        ⟨((b : ↥(Subgroup.normalizer (L : Set G))) : G), b.2⟩
      have h2 : ((a : ↥(Subgroup.normalizer (L : Set G))) : G) *
          ((b : ↥(Subgroup.normalizer (L : Set G))) : G) =
          ((b : ↥(Subgroup.normalizer (L : Set G))) : G) *
          ((a : ↥(Subgroup.normalizer (L : Set G))) : G) := congrArg Subtype.val h1
      exact h2
    · simpa using he (x : G) hx
  refine le_trans ?_ h3
  refine le_csSup ⟨Nat.card ↥(Subgroup.normalizer (L : Set G)), fun j hj => ?_⟩
    ⟨P', le_top, hP'e, hcard⟩
  obtain ⟨E', -, -, hE'⟩ := hj
  calc j ≤ 3 ^ j := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card E' := hE'.symm
    _ ≤ _ := Subgroup.card_le_card_group E'

end Ctx

end N1246

end CFSG.Quasithin.H13
