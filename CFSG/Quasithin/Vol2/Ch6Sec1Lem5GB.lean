module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FN

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.ComponentClassification.OuterAutomorphisms

section Centred

variable {Γ : Type*} [Group Γ]

theorem exists_inner_of_odd_centred_ch615 [Finite Γ] {F Y S Zc : Subgroup Γ}
    (hout : ∀ α : MulAut ↥F, Odd (orderOf α) → ∃ g : ↥F, α = MulAut.conj g)
    (hZc : ∀ z ∈ Zc, ∀ x ∈ F, z * x = x * z)
    (hcen : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g ∈ Zc) (hZodd : ∀ z ∈ Zc, Odd (orderOf z))
    (hSF : S ≤ F)
    (hNS : ∀ g ∈ F, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → ∃ s ∈ S, ∃ z ∈ Zc, g = s * z)
    (hself : ∀ R : Subgroup Γ, S ≤ R → R ≤ F → R ≠ S → Group.IsSolvable ↥R →
      ∀ g ∈ F, (∀ r ∈ R, g * r * g⁻¹ ∈ R) → ∃ r ∈ R, ∃ z ∈ Zc, g = r * z)
    (hSY : S ≤ Y) (hY : Group.IsSolvable ↥Y) {δ : Γ} (hδY : δ ∈ Y)
    (hδN : δ ∈ Subgroup.normalizer (F : Set Γ)) (hδodd : Odd (orderOf δ)) :
    ∃ g ∈ Y ⊓ F, Odd (orderOf g) ∧ ∀ x ∈ F, δ * x * δ⁻¹ = g * x * g⁻¹ := by
  classical
  set φ := F.normalizerMonoidHom with hφ
  set α := φ ⟨δ, hδN⟩ with hα
  have hαo : orderOf α ∣ orderOf δ := by
    have := orderOf_map_dvd φ ⟨δ, hδN⟩
    rwa [Subgroup.orderOf_mk] at this
  have hαodd : Odd (orderOf α) := Odd.of_dvd_nat hδodd hαo
  obtain ⟨g, hg⟩ := hout α hαodd
  have hδg : ∀ x ∈ F, δ * x * δ⁻¹ = (g : Γ) * x * (g : Γ)⁻¹ := fun x hx => by
    have := congrArg (fun β : MulAut ↥F => ((β ⟨x, hx⟩ : ↥F) : Γ)) hg
    simpa [hα, hφ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using this
  have hgm : ((g : Γ) ^ orderOf α) ∈ Zc := by
    refine hcen _ (F.pow_mem g.2 _) fun x hx => ?_
    have h1 : MulAut.conj (g ^ orderOf α) = 1 := by rw [map_pow, ← hg, pow_orderOf_eq_one]
    have h2 := congrArg (fun β : MulAut ↥F => ((β ⟨x, hx⟩ : ↥F) : Γ)) h1
    simp only [MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_pow] at h2
    calc (g : Γ) ^ orderOf α * x = (g : Γ) ^ orderOf α * x * ((g : Γ) ^ orderOf α)⁻¹ *
          (g : Γ) ^ orderOf α := by group
      _ = x * (g : Γ) ^ orderOf α := by rw [h2]
  have hgodd : Odd (orderOf (g : Γ)) := by
    have h1 : (g : Γ) ^ (orderOf α * orderOf ((g : Γ) ^ orderOf α)) = 1 := by
      rw [pow_mul, pow_orderOf_eq_one]
    exact Odd.of_dvd_nat (hαodd.mul (hZodd _ hgm)) (orderOf_dvd_of_pow_eq_one h1)
  have hrepl : ∀ r ∈ Y ⊓ F, ∀ z ∈ Zc, (g : Γ) = r * z →
      ∃ g' ∈ Y ⊓ F, Odd (orderOf g') ∧ ∀ x ∈ F, δ * x * δ⁻¹ = g' * x * g'⁻¹ := by
    intro r hr z hz hgrz
    have hcomm : Commute (g : Γ) z⁻¹ := by
      have h1 : Commute z (g : Γ) := hZc z hz g g.2
      exact h1.symm.inv_right
    refine ⟨r, hr, ?_, fun x hx => ?_⟩
    · have hr' : r = (g : Γ) * z⁻¹ := by rw [hgrz]; group
      rw [hr']
      have hzo : Odd (orderOf z⁻¹) := by rw [orderOf_inv]; exact hZodd z hz
      exact Odd.of_dvd_nat (hgodd.mul hzo) (hcomm.orderOf_mul_dvd_mul_orderOf)
    · rw [hδg x hx, hgrz]
      have h1 := hZc z hz x hx
      calc r * z * x * (r * z)⁻¹ = r * (z * x) * z⁻¹ * r⁻¹ := by group
        _ = r * (x * z) * z⁻¹ * r⁻¹ := by rw [h1]
        _ = r * x * r⁻¹ := by group
  by_cases hgS : ∀ s ∈ S, (g : Γ) * s * (g : Γ)⁻¹ ∈ S
  · obtain ⟨s, hs, z, hz, hgsz⟩ := hNS g g.2 hgS
    exact hrepl s ⟨hSY hs, hSF hs⟩ z hz hgsz
  have hex : ∃ s ∈ S, (g : Γ) * s * (g : Γ)⁻¹ ∉ S := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    exact hgS hall
  obtain ⟨s, hs, hgs⟩ := hex
  have hsG : s ∈ F := hSF hs
  have hxe : δ * s * δ⁻¹ = (g : Γ) * s * (g : Γ)⁻¹ := hδg s hsG
  have hxY : δ * s * δ⁻¹ * s⁻¹ ∈ Y :=
    Y.mul_mem (Y.mul_mem (Y.mul_mem hδY (hSY hs)) (Y.inv_mem hδY)) (Y.inv_mem (hSY hs))
  have hxG : δ * s * δ⁻¹ * s⁻¹ ∈ F := by
    rw [hxe]
    exact F.mul_mem (F.mul_mem (F.mul_mem g.2 hsG) (F.inv_mem g.2)) (F.inv_mem hsG)
  have hxS : δ * s * δ⁻¹ * s⁻¹ ∉ S := fun hx => hgs (by
    have := S.mul_mem hx hs
    rwa [hxe, inv_mul_cancel_right] at this)
  have hRS : Y ⊓ F ≠ S := fun h => hxS (h ▸ ⟨hxY, hxG⟩)
  have hRs : Group.IsSolvable ↥(Y ⊓ F) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (inf_le_left : Y ⊓ F ≤ Y))
  have hgR : ∀ r ∈ Y ⊓ F, (g : Γ) * r * (g : Γ)⁻¹ ∈ Y ⊓ F := by
    intro r hr
    have hrG : r ∈ F := hr.2
    rw [← hδg r hrG]
    refine ⟨Y.mul_mem (Y.mul_mem hδY hr.1) (Y.inv_mem hδY), ?_⟩
    rw [hδg r hrG]
    exact F.mul_mem (F.mul_mem g.2 hrG) (F.inv_mem g.2)
  obtain ⟨r, hr, z, hz, hgrz⟩ :=
    hself (Y ⊓ F) (le_inf hSY hSF) inf_le_right hRS hRs g g.2 hgR
  exact hrepl r hr z hz hgrz

theorem exists_mem_of_not_le_centralizer_centred_ch615 [Finite Γ] {F Y B D S Zc : Subgroup Γ}
    (hout : ∀ α : MulAut ↥F, Odd (orderOf α) → ∃ g : ↥F, α = MulAut.conj g)
    (hZc : ∀ z ∈ Zc, ∀ x ∈ F, z * x = x * z)
    (hcen : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g ∈ Zc) (hZodd : ∀ z ∈ Zc, Odd (orderOf z))
    (hSF : S ≤ F)
    (hNS : ∀ g ∈ F, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → ∃ s ∈ S, ∃ z ∈ Zc, g = s * z)
    (hself : ∀ R : Subgroup Γ, S ≤ R → R ≤ F → R ≠ S → Group.IsSolvable ↥R →
      ∀ g ∈ F, (∀ r ∈ R, g * r * g⁻¹ ∈ R) → ∃ r ∈ R, ∃ z ∈ Zc, g = r * z)
    (hSY : S ≤ Y) (hY : Group.IsSolvable ↥Y) (hDY : D ≤ Y)
    (hDN : D ≤ Subgroup.normalizer (F : Set Γ)) (hDodd : ∀ d ∈ D, Odd (orderOf d))
    (hYB : ∀ y ∈ Y, Odd (orderOf y) → y ∈ B)
    (hp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x ∈ B, ∀ y ∈ B, x ^ p = 1 → y ^ p = 1 → x * y = y * x →
      x ≠ 1 → y ∈ Subgroup.zpowers x)
    (hD : ¬ D ≤ Subgroup.centralizer (F : Set Γ)) :
    ∃ d ∈ D, d ∈ F ∧ d ≠ 1 := by
  classical
  obtain ⟨δ, hδ, hδC⟩ : ∃ δ ∈ D, δ ∉ Subgroup.centralizer (F : Set Γ) := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hD h
  obtain ⟨g, hgYF, hgodd, hδg⟩ := exists_inner_of_odd_centred_ch615 hout hZc hcen hZodd hSF hNS
    hself hSY hY (hDY hδ) (hDN hδ) (hDodd δ hδ)
  have hgF : g ∈ F := hgYF.2
  set α : MulAut ↥F := MulAut.conj (⟨g, hgF⟩ : ↥F) with hα
  have hαδ : ∀ x : ↥F, ((α x : ↥F) : Γ) = δ * x * δ⁻¹ := fun x => by
    rw [hδg x x.2]
    rfl
  have hα1 : α ≠ 1 := by
    intro h
    apply hδC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hαδ ⟨x, hx⟩
    rw [h, MulAut.one_apply] at h1
    calc x * δ = δ * x * δ⁻¹ * δ := by rw [← h1]
      _ = δ * x := by group
  have hαg : orderOf α ∣ orderOf g := by
    have := orderOf_map_dvd (MulAut.conj : ↥F →* MulAut ↥F) ⟨g, hgF⟩
    rwa [Subgroup.orderOf_mk] at this
  have hαδo : orderOf α ∣ orderOf δ := by
    have hpow : α ^ orderOf δ = 1 := by
      ext x
      have key : ∀ m : ℕ, ((α ^ m) x : Γ) = δ ^ m * x * (δ ^ m)⁻¹ := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ', MulAut.mul_apply, hαδ, ih]
          group
      rw [key, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
      rfl
    exact orderOf_dvd_of_pow_eq_one hpow
  set p := (orderOf α).minFac with hpdef
  have hα1' : orderOf α ≠ 1 := fun h => hα1 (orderOf_eq_one_iff.mp h)
  have hp' : p.Prime := Nat.minFac_prime hα1'
  have hpα : p ∣ orderOf α := Nat.minFac_dvd _
  have hpδ : p ∣ orderOf δ := hpα.trans hαδo
  have hpg : p ∣ orderOf g := hpα.trans hαg
  have hp2 : p ≠ 2 := by
    rintro h
    rw [h] at hpδ
    exact (Nat.not_even_iff_odd.mpr (hDodd δ hδ)) (even_iff_two_dvd.mpr hpδ)
  set δ₁ := δ ^ (orderOf δ / p) with hδ₁
  set g₁ := g ^ (orderOf g / p) with hg₁
  have hδ₁o : orderOf δ₁ = p := by
    rw [hδ₁, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos δ) hpδ) hp'.pos).ne'
      (Nat.div_dvd_of_dvd hpδ)]
    exact Nat.div_div_self hpδ (orderOf_pos δ).ne'
  have hg₁o : orderOf g₁ = p := by
    rw [hg₁, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos g) hpg) hp'.pos).ne'
      (Nat.div_dvd_of_dvd hpg)]
    exact Nat.div_div_self hpg (orderOf_pos g).ne'
  have hgB : g ∈ B := hYB g hgYF.1 hgodd
  have hδB : δ ∈ B := hYB δ (hDY hδ) (hDodd δ hδ)
  have hcomm : Commute δ g := by
    have h1 := hδg g hgF
    rw [mul_inv_cancel_right] at h1
    calc δ * g = δ * g * δ⁻¹ * δ := by group
      _ = g * δ := by rw [h1]
  have hδ₁1 : δ₁ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hδ₁o
    exact hp'.one_lt.ne' hδ₁o.symm
  have hg₁1 : g₁ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hg₁o
    exact hp'.one_lt.ne' hg₁o.symm
  have hmem := hp p hp' hp2 g₁ (B.pow_mem hgB _) δ₁ (B.pow_mem hδB _)
    (by rw [← hg₁o]; exact pow_orderOf_eq_one g₁) (by rw [← hδ₁o]; exact pow_orderOf_eq_one δ₁)
    ((hcomm.pow_pow _ _).symm.eq) hg₁1
  refine ⟨δ₁, D.pow_mem hδ _, (Subgroup.zpowers_le.mpr (F.pow_mem hgF _)) hmem, hδ₁1⟩

end Centred

section Hat

variable {Γ : Type} [Group Γ] [Finite Γ] {F : Subgroup Γ}

theorem hout_of_isHat_ch615 (hh : IsHat ↥F ↥(alternatingGroup (Fin 6))) :
    ∀ α : MulAut ↥F, Odd (orderOf α) → ∃ g : ↥F, α = MulAut.conj g := by
  have : Group.IsPerfect ↥F := hh.1.1
  obtain ⟨e⟩ := hh.2.2
  have h1 : IsPGroup 2 (Outer (↥F ⧸ Subgroup.center ↥F)) :=
    CFSG.LieType.SteinbergBR.OddSylow.isPGroup_outer_of_equiv e
      CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six
  exact exists_eq_conj_of_outer_ch615 (h1.of_injective _ (centerQuotient_outer_injective ↥F))

omit [Finite Γ] in
theorem mem_map_center_iff_ch615 {g : Γ} :
    g ∈ (Subgroup.center ↥F).map F.subtype ↔ g ∈ F ∧ ∀ x ∈ F, g * x = x * g := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun x hx => ?_⟩
    have := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc) ⟨x, hx⟩)
    exact this.symm
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (h y y.2).symm, rfl⟩

omit [Finite Γ] in
theorem exists_quot_hat_ch615 (hh : IsHat ↥F ↥(alternatingGroup (Fin 6))) :
    ∃ φ : ↥F →* ↥(alternatingGroup (Fin 6)), Function.Surjective φ ∧
      ∀ x : ↥F, φ x = 1 ↔ x ∈ Subgroup.center ↥F := by
  obtain ⟨e⟩ := hh.2.2
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥F)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun x => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

omit [Finite Γ] in
theorem exists_mul_center_of_normalizes_ch615 (hh : IsHat ↥F ↥(alternatingGroup (Fin 6)))
    {S R : Subgroup Γ} (hS : IsSylowTwoOf S F) (hSR : S ≤ R) (hRF : R ≤ F)
    (hR : Group.IsSolvable ↥R) {g : Γ} (hg : g ∈ F) (hgR : ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    ∃ r ∈ R, ∃ z ∈ (Subgroup.center ↥F).map F.subtype, g = r * z := by
  obtain ⟨φ, hφs, hker⟩ := exists_quot_hat_ch615 hh
  set S₀ := (S.subgroupOf F).map φ with hS₀def
  set R₀ := (R.subgroupOf F).map φ with hR₀def
  have hS₀ : IsSylowTwoOf S₀ ⊤ := by
    have := CFSG.QuasithinUnique.Setup.Wreath.isSylowTwoOf_map_hom hS φ
    rwa [MonoidHom.range_eq_top.mpr hφs] at this
  have hSR₀ : S₀ ≤ R₀ := Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
    (hSR (Subgroup.mem_subgroupOf.mp hx))
  have hR₀s : Group.IsSolvable ↥R₀ := by
    have : Group.IsSolvable ↥(R.subgroupOf F) := Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hRF).toMonoidHom) (MulEquiv.injective _)
    exact Group.isSolvable_of_surjective (φ.subgroupMap_surjective _)
  have hn : ∀ s ∈ R₀, φ ⟨g, hg⟩ * s * (φ ⟨g, hg⟩)⁻¹ ∈ R₀ := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨⟨g, hg⟩ * t * ⟨g, hg⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_,
      by simp only [map_mul, map_inv]⟩
    exact hgR _ (Subgroup.mem_subgroupOf.mp ht)
  have hgR₀ : φ ⟨g, hg⟩ ∈ R₀ := by
    by_cases hRS : R₀ = S₀
    · rw [hRS] at hn ⊢
      exact selfNormalizing_alt_six_ch615 S₀ hS₀ _ hn
    · exact mem_of_conj_mem_overgroup_alt_six_ch615 hS₀ hSR₀ hRS hR₀s _ hn
  obtain ⟨t, ht, hte⟩ := hgR₀
  refine ⟨t, Subgroup.mem_subgroupOf.mp ht, ((t⁻¹ * ⟨g, hg⟩ : ↥F) : Γ),
    ⟨t⁻¹ * ⟨g, hg⟩, (hker _).mp (by rw [map_mul, map_inv, hte, inv_mul_cancel]), rfl⟩, ?_⟩
  simp

theorem exists_mem_of_not_le_centralizer_hat_ch615 (hh : IsHat ↥F ↥(alternatingGroup (Fin 6)))
    {Y B D S : Subgroup Γ} (hS : IsSylowTwoOf S F) (hSY : S ≤ Y) (hY : Group.IsSolvable ↥Y)
    (hDY : D ≤ Y) (hDN : D ≤ Subgroup.normalizer (F : Set Γ)) (hDodd : ∀ d ∈ D, Odd (orderOf d))
    (hYB : ∀ y ∈ Y, Odd (orderOf y) → y ∈ B)
    (hp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x ∈ B, ∀ y ∈ B, x ^ p = 1 → y ^ p = 1 → x * y = y * x →
      x ≠ 1 → y ∈ Subgroup.zpowers x)
    (hD : ¬ D ≤ Subgroup.centralizer (F : Set Γ)) :
    ∃ d ∈ D, d ∈ F ∧ d ≠ 1 := by
  have hZc : ∀ z ∈ (Subgroup.center ↥F).map F.subtype, ∀ x ∈ F, z * x = x * z :=
    fun z hz => (mem_map_center_iff_ch615.mp hz).2
  have hcen : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g ∈ (Subgroup.center ↥F).map F.subtype :=
    fun g hg h => mem_map_center_iff_ch615.mpr ⟨hg, h⟩
  have hZodd : ∀ z ∈ (Subgroup.center ↥F).map F.subtype, Odd (orderOf z) := by
    rintro _ ⟨c, hc, rfl⟩
    have h1 : orderOf (⟨c, hc⟩ : ↥(Subgroup.center ↥F)) ∣ 3 :=
      hh.2.1 ▸ orderOf_dvd_natCard _
    have h2 : orderOf ((c : ↥F) : Γ) = orderOf (⟨c, hc⟩ : ↥(Subgroup.center ↥F)) := by
      rw [Subgroup.orderOf_coe]
      exact (Subgroup.orderOf_mk c hc).symm
    rw [Subgroup.coe_subtype, h2]
    exact Odd.of_dvd_nat (by decide) h1
  exact exists_mem_of_not_le_centralizer_centred_ch615 (hout_of_isHat_ch615 hh) hZc hcen hZodd
    hS.le (fun g hg hgS => exists_mul_center_of_normalizes_ch615 hh hS le_rfl hS.le
      (by have := hS.isPGroup.isNilpotent; infer_instance) hg hgS)
    (fun R hSR hRF _ hR g hg hgR => exists_mul_center_of_normalizes_ch615 hh hS hSR hRF hR hg hgR)
    hSY hY hDY hDN hDodd hYB hp hD

end Hat

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_case1_hat_fix_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hh : IsHat ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))
      ↥(alternatingGroup (Fin 6)))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  classical
  set F := quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) with hFdef
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hKF := c.autI_oTwoUpper_le_genFitting_ch615 hU (hout_of_isHat_ch615 hh)
  have hXF := le_normalizer_genFitting_ch615 hU
  have hS := c.isSylowTwoOf_genFitting_ch615 hU
  have hTF : autI hU T ≤ Subgroup.normalizer (F : Set (MulAut _)) :=
    fun x hx => hXF (autI_mono hU (c.hH.1.1.trans le_sup_right) hx)
  have hDF : autI hU D ≤ Subgroup.normalizer (F : Set (MulAut _)) :=
    fun x hx => hXF (autI_mono hU (hD.1.trans le_sup_left) hx)
  by_cases hDc : autI hU D ≤ Subgroup.centralizer (F : Set (MulAut _))
  · apply c.not_hall_normalizes_ch615 hU hD hN
    intro y hy k hk
    rw [← Subgroup.mem_centralizer_iff.mp (hDc hy) k (hKF hk), mul_inv_cancel_right]
    exact hk
  have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
    have hodd : Odd (Nat.card (autI hU D)) := by
      rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
      exact hD.2.1
    exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
  obtain ⟨d, hdD, hdF, hd1⟩ := exists_mem_of_not_le_centralizer_hat_ch615 hh hS
    (inf_le_left.trans (autI_mono hU le_sup_right)) (c.isSolvable_autI_ch615 hU)
    (autI_mono hU (hD.1.trans le_sup_left)) hDF hDsodd
    (fun y hy ho => c.mem_autI_borelL_of_odd_ch615 hU hy ho)
    (fun p hp hp2 x hx y hy hxp hyp hxy hx1 =>
      c.mem_zpowers_of_autI_borelL_prime_ch615 hU hp hp2 hx hy hxp hyp hxy hx1) hDc
  obtain ⟨w, hwF, hw1, hwT⟩ := exists_fix_ch615 IntMod.sq_eq_one (c.isPGroup_autI_ch615 hU)
    hfix fun t ht w hw => mem_fixV_of_conj_ch615 (hTF ht) hw
  exact c.false_of_fix_ch615 h432 hU hD hw1 hwT (fun k hk => hwF k (hKF hk)) hdD hd1
    (hwF d hdF)

end Cx615C

end CFSG.Quasithin.H13
