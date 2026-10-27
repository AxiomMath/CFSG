module

public import CFSG.Quasithin.Recognition.RuTypeJ27g

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem mem_B_iff {x : G} : x ∈ M.B ↔ x = 1 ∨ x = M.bel ∨ x = (M.bel : G)⁻¹ := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, M.orderOf_bel]
    have h0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
    generalize k % ((3 : ℕ) : ℤ) = r at h0 h3
    interval_cases r
    · exact Or.inl (zpow_zero _)
    · exact Or.inr (Or.inl (zpow_one _))
    · refine Or.inr (Or.inr (eq_inv_of_mul_eq_one_left ?_))
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← pow_succ, M.bel_pow_three]
  · rintro (rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
    · exact inv_mem (Subgroup.mem_zpowers _)

theorem conj_bel_of_mem_GP {g : G} (hg : g ∈ M.GP) :
    g * M.bel * g⁻¹ = M.bel ∨ g * M.bel * g⁻¹ = (M.bel : G)⁻¹ := by
  rcases M.mem_B_iff.mp (M.conj_mem_B hg (Subgroup.mem_zpowers (M.bel : G))) with h | h | h
  · exfalso
    apply M.bel_ne_one
    calc (M.bel : G) = g⁻¹ * (g * M.bel * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · exact Or.inl h
  · exact Or.inr h

theorem mem_GB_iff_conj {g : G} : g ∈ M.GB ↔ g * M.bel * g⁻¹ = M.bel := by
  rw [M.mem_GB]
  constructor
  · intro h
    rw [← h, mul_inv_cancel_right]
  · intro h
    calc (M.bel : G) * g = (g * M.bel * g⁻¹) * g := by rw [h]
      _ = g * M.bel := by group

theorem conj_bel_of_not_mem_GB {g : G} (hg : g ∈ M.GP) (hgB : g ∉ M.GB) :
    g * M.bel * g⁻¹ = (M.bel : G)⁻¹ :=
  (M.conj_bel_of_mem_GP hg).resolve_left fun h => hgB (M.mem_GB_iff_conj.mpr h)

theorem bel_ne_inv : (M.bel : G) ≠ (M.bel : G)⁻¹ := by
  intro h
  apply M.bel_ne_one
  have h2 : (M.bel : G) * M.bel = 1 := by
    calc (M.bel : G) * M.bel = M.bel * (M.bel : G)⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel _
  calc (M.bel : G) = (M.bel : G) ^ 3 * ((M.bel : G) * M.bel)⁻¹ := by group
    _ = 1 := by rw [M.bel_pow_three, h2]; group

theorem mem_GP_of_inv {g : G} (hg : g * M.bel * g⁻¹ = (M.bel : G)⁻¹) : g ∈ M.GP := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow, hg, inv_zpow]
  exact inv_mem (Subgroup.zpow_mem_zpowers _ _)

theorem exists_inv_GP : ∃ n ∈ M.GP, n * M.bel * n⁻¹ = (M.bel : G)⁻¹ := by
  obtain ⟨n, -, hn⟩ := M.exists_inverter
  exact ⟨n, M.mem_GP_of_inv hn, hn⟩

theorem index_GB_GP : (M.GB.subgroupOf M.GP).index = 2 := by
  obtain ⟨n, hn, hninv⟩ := M.exists_inv_GP
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨n, hn⟩, fun b => ?_⟩
  show Xor ((b : G) * n ∈ M.GB) ((b : G) ∈ M.GB)
  rw [M.mem_GB_iff_conj, M.mem_GB_iff_conj]
  have e : (b : G) * n * M.bel * ((b : G) * n)⁻¹ = ((b : G) * M.bel * (b : G)⁻¹)⁻¹ := by
    calc (b : G) * n * M.bel * ((b : G) * n)⁻¹ = b * (n * M.bel * n⁻¹) * (b : G)⁻¹ := by group
      _ = ((b : G) * M.bel * (b : G)⁻¹)⁻¹ := by rw [hninv]; group
  rw [e]
  rcases M.conj_bel_of_mem_GP b.2 with h | h
  · rw [h]
    exact Or.inr ⟨rfl, M.bel_ne_inv.symm⟩
  · rw [h, inv_inv]
    exact Or.inl ⟨rfl, M.bel_ne_inv.symm⟩

theorem card_XQ
    : Nat.card M.XQ = 720 := by
  obtain ⟨e⟩ := M.lemma_J27_2
  rw [Nat.card_congr e.toEquiv, Out21.A6.card_m10]

theorem card_BGB : Nat.card (M.B.subgroupOf M.GB) = 3 := by
  rw [card_subgroupOf_of_le M.B_le_GB, M.card_B]

theorem card_GB
    : Nat.card M.GB = 2160 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (M.B.subgroupOf M.GB)]
  show Nat.card M.XQ * Nat.card (M.B.subgroupOf M.GB) = 2160
  rw [M.card_XQ, M.card_BGB]

theorem card_GP
    : Nat.card M.GP = 4320 := by
  have h := (M.GB.subgroupOf M.GP).card_mul_index
  rw [M.index_GB_GP, card_subgroupOf_of_le M.GB_le_GP, M.card_GB] at h
  omega

instance BP_normal : (M.B.subgroupOf M.GP).Normal := Subgroup.normal_in_normalizer

abbrev XP : Type := M.GP ⧸ M.B.subgroupOf M.GP

theorem card_XP
    : Nat.card M.XP = 1440 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (M.B.subgroupOf M.GP)
  rw [M.card_GP, card_subgroupOf_of_le M.B_le_GP, M.card_B] at h
  show Nat.card (M.GP ⧸ M.B.subgroupOf M.GP) = 1440
  omega

@[expose] noncomputable def ι : M.XQ →* M.XP :=
  QuotientGroup.map (M.B.subgroupOf M.GB) (M.B.subgroupOf M.GP) (Subgroup.inclusion M.GB_le_GP)
    (fun _ hx => Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx))

theorem ι_mk (x : M.GB) :
    M.ι (QuotientGroup.mk x) = QuotientGroup.mk (Subgroup.inclusion M.GB_le_GP x) := rfl

theorem ι_injective : Function.Injective M.ι := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  rw [M.ι_mk, QuotientGroup.eq_one_iff] at ha
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp ha)

theorem card_range_ι
    : Nat.card M.ι.range = 720 := by
  rw [← M.card_XQ]
  exact Nat.card_congr (MonoidHom.ofInjective M.ι_injective).toEquiv.symm

theorem index_range_ι
    : M.ι.range.index = 2 := by
  have h := M.ι.range.card_mul_index
  rw [M.card_range_ι, M.card_XP] at h
  omega

theorem mk_mem_range_ι_iff (g : M.GP) :
    (QuotientGroup.mk g : M.XP) ∈ M.ι.range ↔ (g : G) ∈ M.GB := by
  constructor
  · rintro ⟨a, ha⟩
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [M.ι_mk, QuotientGroup.eq] at ha
      have h := Subgroup.mem_subgroupOf.mp ha
      have e : (g : G) = x * ((Subgroup.inclusion M.GB_le_GP x)⁻¹ * g : M.GP) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
        group
      rw [e]
      exact mul_mem x.2 (M.B_le_GB h)
  · intro hg
    exact ⟨QuotientGroup.mk ⟨g, hg⟩, rfl⟩

theorem conjGB_mem_NX
    {g : G} (hg : g ∈ M.GP) {y : M.GB} (hy : y ∈ M.NX) :
    M.conjGB hg y ∈ M.NX := by
  let W := M.Vtr.comp (M.conjGB hg)
  have hW2 : ∀ u : M.GB, u ^ 2 = 1 → W u = 1 := by
    intro u hu
    apply M.Vtr_of_sq
    rw [← map_pow, hu, map_one]
  have hWB : ∀ u : M.GB, (u : G) ∈ M.B → W u = 1 := by
    intro u hu
    have h1 : ((M.conjGB hg u : M.GB) : G) ∈ M.B := M.conj_mem_B hg hu
    exact M.mem_NX_of_mem_B h1
  exact M.NX_le_ker W hW2 hWB hy

noncomputable abbrev NP : Subgroup M.XP := M.NQ.map M.ι

instance NP_normal
    : M.NP.Normal where
  conj_mem n hn g := by
    obtain ⟨w, hw, rfl⟩ := hn
    obtain ⟨y, hy, rfl⟩ := hw
    induction g using QuotientGroup.induction_on with
    | H g =>
      refine ⟨QuotientGroup.mk (M.conjGB g.2 y), ⟨M.conjGB g.2 y, M.conjGB_mem_NX g.2 hy, rfl⟩,
        ?_⟩
      show M.ι (QuotientGroup.mk (M.conjGB g.2 y)) =
        (QuotientGroup.mk g : M.XP) * M.ι (QuotientGroup.mk y) * (QuotientGroup.mk g)⁻¹
      rw [M.ι_mk, M.ι_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl

theorem nonempty_NP_psl29
    : Nonempty (M.NP ≃* A6Models.psl29) := by
  obtain ⟨e⟩ := M.nonempty_NQ_alt6
  obtain ⟨-, ψ, -, -⟩ := Unc25K1.A6Model.exists_pslEquiv
  exact ⟨((M.NQ.equivMapOfInjective M.ι M.ι_injective).symm.trans e).trans ψ.symm⟩

theorem eq_one_of_central_NQ
    {w : M.XQ} (hw : w ∈ M.NQ) (hc : ∀ v ∈ M.NQ, w * v = v * w) :
    w = 1 := by
  obtain ⟨e⟩ := M.nonempty_NQ_alt6
  have hz := alternatingGroup.center_eq_bot (α := Fin 6) (by simp)
  have hmem : e ⟨w, hw⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨v, rfl⟩ := e.surjective a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc v v.2).symm
  rw [hz, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hmem
  exact congrArg Subtype.val hmem

theorem eq_one_of_centralizes_NQ
    {w : M.XQ} (hc : ∀ v ∈ M.NQ, w * v = v * w) : w = 1 := by
  have hw2 : w * w ∈ M.NQ := Subgroup.mul_self_mem_of_index_two M.NQ_index w
  have hc2 : ∀ v ∈ M.NQ, w * w * v = v * (w * w) := fun v hv => by
    rw [mul_assoc, hc v hv, ← mul_assoc, hc v hv, mul_assoc]
  have hsq : w * w = 1 := M.eq_one_of_central_NQ hw2 hc2
  have hwN : w ∈ M.NQ := M.mem_NQ_of_sq (by rw [pow_two, hsq])
  exact M.eq_one_of_central_NQ hwN hc

@[expose] noncomputable def ρ
    (e : M.NP ≃* A6Models.psl29) : M.XP →* A6Models.autA6 :=
  (Unc25K1.A6Model.thetaEquiv e).toMonoidHom.comp MulAut.conjNormal

theorem ρ_eq_one_iff
    (e : M.NP ≃* A6Models.psl29) (x : M.XP) :
    M.ρ e x = 1 ↔ ∀ n ∈ M.NP, x * n * x⁻¹ = n := by
  rw [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  constructor
  · intro h n hn
    have := congrArg (fun f : MulAut M.NP => ((f ⟨n, hn⟩ : M.NP) : M.XP)) h
    simpa [MulAut.conjNormal_apply] using this
  · intro h
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact h n n.2

theorem eq_one_of_ρ_ι
    (e : M.NP ≃* A6Models.psl29) {w : M.XQ} (hw : M.ρ e (M.ι w) = 1) :
    w = 1 := by
  rw [ρ_eq_one_iff] at hw
  apply M.eq_one_of_centralizes_NQ
  intro v hv
  have h := hw (M.ι v) ⟨v, hv, rfl⟩
  apply M.ι_injective
  rw [map_mul, map_mul]
  calc M.ι w * M.ι v = (M.ι w * M.ι v * (M.ι w)⁻¹) * M.ι w := by group
    _ = M.ι v * M.ι w := by rw [h]

theorem ρ_dichotomy
    (e : M.NP ≃* A6Models.psl29) :
    Function.Injective (M.ρ e) ∨
      ∃ c : M.XP, c ∉ M.ι.range ∧ c * c = 1 ∧ M.ρ e c = 1 ∧ ∀ y : M.XP, y * c = c * y := by
  by_cases hinj : Function.Injective (M.ρ e)
  · exact Or.inl hinj
  right
  rw [injective_iff_map_eq_one] at hinj
  push Not at hinj
  obtain ⟨c, hc, hc1⟩ := hinj
  have hcR : c ∉ M.ι.range := by
    rintro ⟨w, rfl⟩
    exact hc1 (by rw [M.eq_one_of_ρ_ι e hc, map_one])
  have hker : ∀ x ∈ M.ι.range, M.ρ e x = 1 → x = 1 := by
    rintro _ ⟨w, rfl⟩ hw
    rw [M.eq_one_of_ρ_ι e hw, map_one]
  have hidx := M.index_range_ι
  refine ⟨c, hcR, ?_, hc, fun y => ?_⟩
  · refine hker _ ?_ (by rw [map_mul, hc, mul_one])
    exact (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hcR hcR)
  · have hn : M.ι.range.Normal := Subgroup.normal_of_index_eq_two hidx
    have hyc : y * c * y⁻¹ ∉ M.ι.range := fun h => hcR (by
      have := hn.conj_mem _ h y⁻¹
      simpa [mul_assoc] using this)
    have hcinv : c⁻¹ ∉ M.ι.range := fun h => hcR (by simpa using inv_mem h)
    have h1 : y * c * y⁻¹ * c⁻¹ = 1 := by
      refine hker _ ((Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hyc hcinv)) ?_
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    calc y * c = y * c * y⁻¹ * c⁻¹ * (c * y) := by group
      _ = c * y := by rw [h1, one_mul]

end RuDataM

end CFSG.Quasithin.RuType
