module

public import CFSG.Quasithin.EmptyFaithful.S153EB6E
public import CFSG.Quasithin.EmptyFaithful.S153EB6D
public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W]

structure Ctx (H K : Subgroup (MulAut W)) (a : MulAut W) : Prop where
  sq : G64.IsQuotientOfSQTKCat ↥H
  KH : K ≤ H
  Kn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K
  aH : a ∈ H
  a2 : a ^ 2 = 1
  syl : ∃ T : Subgroup (MulAut W), IsSylowTwoOf T H ∧ a ∈ T ∧ ∀ x ∈ T, x * a = a * x

structure SumCtx (K : Subgroup (MulAut W)) (a : MulAut W) (U : Subgroup W) : Prop where
  KU : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U
  aU : ∀ u ∈ U, a u ∈ U
  irr : IsIrrOn153 K U
  card : Nat.card ↥(commIn153 (Subgroup.zpowers a) U) = 2

section Induced

variable {H K : Subgroup (MulAut W)} {a : MulAut W} {U : Subgroup W}

theorem Ctx.le_stab (hC : Ctx H K a) (hS : SumCtx K a U) : K ⊔ Subgroup.zpowers a ≤ stabSub U :=
  sup_zpowers_le_stabSub hC.a2 hS.KU hS.aU

theorem mem_Xg (K : Subgroup (MulAut W)) (a : MulAut W) : a ∈ K ⊔ Subgroup.zpowers a :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers a)

@[expose] noncomputable def indRes (hC : Ctx H K a) (hS : SumCtx K a U) :
    ↥(K ⊔ Subgroup.zpowers a) →* MulAut ↥U :=
  resX _ U (hC.le_stab hS)

@[expose] noncomputable def indG (hC : Ctx H K a) (hS : SumCtx K a U) : Subgroup (MulAut ↥U) :=
  (indRes hC hS).range

@[expose] noncomputable def indK (hC : Ctx H K a) (hS : SumCtx K a U) : Subgroup (MulAut ↥U) :=
  ((K.subgroupOf (K ⊔ Subgroup.zpowers a)).map (indRes hC hS))

@[expose] noncomputable def indA (hC : Ctx H K a) (hS : SumCtx K a U) : MulAut ↥U :=
  indRes hC hS ⟨a, mem_Xg K a⟩

theorem indA_mem (hC : Ctx H K a) (hS : SumCtx K a U) : indA hC hS ∈ indG hC hS :=
  ⟨_, rfl⟩

theorem indA_sq (hC : Ctx H K a) (hS : SumCtx K a U) : indA hC hS ^ 2 = 1 := by
  have h1 : (⟨a, mem_Xg K a⟩ : ↥(K ⊔ Subgroup.zpowers a)) ^ 2 = 1 := Subtype.ext hC.a2
  show indRes hC hS ⟨a, mem_Xg K a⟩ ^ 2 = 1
  rw [← map_pow, h1, map_one]

theorem indRes_zpow_apply (hC : Ctx H K a) (hS : SumCtx K a U) (m : ℤ) (u : ↥U) :
    (((indA hC hS ^ m : MulAut ↥U) u : ↥U) : W) = (a ^ m : MulAut W) (u : W) := by
  have h1 : indA hC hS ^ m = indRes hC hS ((⟨a, mem_Xg K a⟩ : ↥(K ⊔ Subgroup.zpowers a)) ^ m) :=
    (map_zpow _ _ _).symm
  rw [h1]
  show (((⟨a, mem_Xg K a⟩ : ↥(K ⊔ Subgroup.zpowers a)) ^ m : ↥(K ⊔ Subgroup.zpowers a)) :
    MulAut W) (u : W) = _
  rw [Subgroup.coe_zpow]

theorem map_commV_indA (hC : Ctx H K a) (hS : SumCtx K a U) :
    (commV (Subgroup.zpowers (indA hC hS))).map U.subtype = commIn153 (Subgroup.zpowers a) U := by
  unfold commV commIn153
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨y, hy, v, rfl⟩, rfl⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨a ^ m, Subgroup.mem_zpowers_iff.2 ⟨m, rfl⟩, (v : W), v.2, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, indRes_zpow_apply hC hS m v]
  · rintro ⟨y, hy, w, hw, rfl⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨((indA hC hS ^ m : MulAut ↥U) ⟨w, hw⟩) * (⟨w, hw⟩ : ↥U)⁻¹,
      ⟨indA hC hS ^ m, Subgroup.mem_zpowers_iff.2 ⟨m, rfl⟩, ⟨w, hw⟩, rfl⟩, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, indRes_zpow_apply hC hS m ⟨w, hw⟩]

theorem card_commV_indA (hC : Ctx H K a) (hS : SumCtx K a U) :
    Nat.card ↥(commV (Subgroup.zpowers (indA hC hS))) = 2 := by
  rw [← hS.card, ← map_commV_indA hC hS]
  exact (Subgroup.card_map_of_injective U.subtype_injective).symm

theorem indK_le (hC : Ctx H K a) (hS : SumCtx K a U) : indK hC hS ≤ indG hC hS :=
  Subgroup.map_le_range _ _

theorem mem_indK (hC : Ctx H K a) (hS : SumCtx K a U) {k : MulAut W} (hk : k ∈ K) :
    indRes hC hS ⟨k, Subgroup.mem_sup_left hk⟩ ∈ indK hC hS :=
  ⟨⟨k, Subgroup.mem_sup_left hk⟩, hk, rfl⟩

theorem ind_irr (hC : Ctx H K a) (hS : SumCtx K a U) (B : Subgroup ↥U)
    (hB : ∀ k ∈ indK hC hS, ∀ b ∈ B, k b ∈ B) : B = ⊥ ∨ B = ⊤ := by
  have hB' : ∀ k ∈ K, ∀ b ∈ B.map U.subtype, k b ∈ B.map U.subtype := by
    rintro k hk _ ⟨b, hb, rfl⟩
    exact ⟨_, hB _ (mem_indK hC hS hk) b hb, rfl⟩
  rcases hS.irr.2.2 (B.map U.subtype) (by rintro _ ⟨b, -, rfl⟩; exact b.2) hB' with h | h
  · left
    rw [eq_bot_iff]
    intro b hb
    have : (b : W) ∈ B.map U.subtype := ⟨b, hb, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  · right
    rw [eq_top_iff]
    intro b _
    have : (b : W) ∈ B.map U.subtype := by rw [h]; exact b.2
    obtain ⟨b', hb', hbb⟩ := this
    have : b' = b := Subtype.ext hbb
    rw [← this]
    exact hb'

theorem pCoreOf_indG [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) (hC : Ctx H K a) (hS : SumCtx K a U) :
    pCoreOf 2 (indG hC hS) = ⊥ :=
  pCoreOf_two_eq_bot_of_irr (V := ↥U) (fun v => Subtype.ext (hexp v)) (indK_le hC hS)
    (ind_irr hC hS)

theorem indA_ne_one (hC : Ctx H K a) (hS : SumCtx K a U) : indA hC hS ≠ 1 := by
  intro h1
  have hfix : ∀ u ∈ U, a u = u := by
    intro u hu
    have h2 := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : W)) h1
    simp only [MulAut.one_apply] at h2
    exact h2
  have hbot : commIn153 (Subgroup.zpowers a) U = ⊥ := by
    rw [eq_bot_iff, commIn153, Subgroup.closure_le]
    rintro _ ⟨y, hy, w, hw, rfl⟩
    have hy' : y ∈ centSub U := (Subgroup.zpowers_le.2 (show a ∈ centSub U from hfix)) hy
    show y w * w⁻¹ ∈ (⊥ : Subgroup W)
    rw [Subgroup.mem_bot, hy' w hw]
    simp
  have := hS.card
  rw [hbot, Subgroup.card_bot] at this
  omega

theorem ind_span (hC : Ctx H K a) (hS : SumCtx K a U) :
    (⨆ (g : MulAut ↥U) (_ : g ∈ indG hC hS),
      (commV (Subgroup.zpowers (indA hC hS))).map g.toMonoidHom) = ⊤ := by
  set S := (⨆ (g : MulAut ↥U) (_ : g ∈ indG hC hS),
      (commV (Subgroup.zpowers (indA hC hS))).map g.toMonoidHom) with hSdef
  have hSinv : ∀ g ∈ indG hC hS, ∀ s ∈ S, g s ∈ S := by
    intro g hg s hs
    have : S.map g.toMonoidHom ≤ S := by
      rw [hSdef, Subgroup.map_iSup]
      refine iSup_le fun g' => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hg' => ?_
      rw [Subgroup.map_map]
      exact le_iSup_of_le (g * g') (le_iSup_of_le ((indG hC hS).mul_mem hg hg') le_rfl)
    exact this ⟨s, hs, rfl⟩
  have hCS : commV (Subgroup.zpowers (indA hC hS)) ≤ S := by
    refine le_iSup_of_le 1 (le_iSup_of_le (one_mem _) ?_)
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hne : S ≠ ⊥ := by
    intro hbot
    have h1 : commV (Subgroup.zpowers (indA hC hS)) = ⊥ := le_bot_iff.1 (hbot ▸ hCS)
    have := card_commV_indA hC hS
    rw [h1, Subgroup.card_bot] at this
    omega
  exact (ind_irr hC hS S fun k hk b hb => hSinv k (indK_le hC hS hk) b hb).resolve_left hne

theorem hyp61_ind [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) (hC : Ctx H K a) (hS : SumCtx K a U) :
    G64.Hyp61 (indG hC hS) (indA hC hS) where
  pCore_eq_bot := pCoreOf_indG hexp hC hS
  quotient_sqtk :=
    isQuotientOfSQTKCat_of_surjective (sup_le hC.KH (Subgroup.zpowers_le.2 hC.aH)) hC.sq
      (indRes hC hS).rangeRestrict (indRes hC hS).rangeRestrict_surjective
  mem := indA_mem hC hS
  ne_one := indA_ne_one hC hS
  sq_eq_one := indA_sq hC hS
  card_comm_le := by rw [card_commV_indA hC hS]; norm_num
  span := ind_span hC hS

theorem exists_sylow_ind [Finite W] (hC : Ctx H K a) (hS : SumCtx K a U) :
    ∃ T, IsSylowTwoOf T (indG hC hS) ∧ indA hC hS ∈ T ∧ ∀ x ∈ T, x * indA hC hS = indA hC hS * x := by
  obtain ⟨T, hT, haT, hac⟩ := hC.syl
  have hX := isSylowTwoOf_X hT hC.KH hC.Kn haT hac
  have hTX := isSylowTwoOf_map_range (indRes hC hS) hX
  refine ⟨_, hTX, ⟨⟨a, mem_Xg K a⟩, ⟨haT, mem_Xg K a⟩, rfl⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have h1 : t * ⟨a, mem_Xg K a⟩ = ⟨a, mem_Xg K a⟩ * t :=
    Subtype.ext (hac _ (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ht)).1)
  show indRes hC hS t * indRes hC hS ⟨a, mem_Xg K a⟩ = indRes hC hS ⟨a, mem_Xg K a⟩ * indRes hC hS t
  rw [← map_mul, ← map_mul, h1]

end Induced

end S153EB6

end CFSG.Quasithin
