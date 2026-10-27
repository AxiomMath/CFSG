module

public import CFSG.Quasithin.H13.VolIC113c1
public import CFSG.LieType.CentralExt.SL2Lift
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

theorem card_sl2_five : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_zmod]
  norm_num

theorem card_center_sl2_five :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) = 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv,
    show max (Fintype.card (Fin 2)) 1 = 2 by simp]
  exact (IsPrimitiveRoot.neg_one 5 (by norm_num)).card_rootsOfUnity

theorem card_psl2_five : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) = 60 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)))
  rw [card_sl2_five, card_center_sl2_five] at h
  show Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) ⧸
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) = 60
  omega

theorem exists_sl2_five_alt5 : ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) →*
    alternatingGroup (Fin 5), Function.Surjective ψ ∧
      ψ.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
  obtain ⟨e⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty card_psl2_five
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem card_alt5' : Nat.card (alternatingGroup (Fin 5)) = 60 := A5.Delta5.a5_card

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G}

theorem blockQ_le_pCoreOf (hTN : T ≤ Subgroup.normalizer (L : Set G)) :
    blockQ L ≤ pCoreOf 2 (L ⊔ T) :=
  C1.le_pCoreOf_of_normalized ((C1.blockQ_le L).trans le_sup_left)
    (fun _ hg => C1.mem_normalizer_blockQ (sup_le_normalizer hTN hg)) (C1.blockQ_isPGroup L)

omit [Finite G] in
theorem card_center_eq_inf (L : Subgroup G) :
    Nat.card (Subgroup.center ↥L) = Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set G)) := by
  have h : (Subgroup.center ↥L).map L.subtype = L ⊓ Subgroup.centralizer (L : Set G) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have := Subgroup.mem_center_iff.mp hk ⟨y, hy⟩
      exact congrArg Subtype.val this
    · rintro ⟨hxL, hxc⟩
      refine ⟨⟨x, hxL⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hxc y y.2
  rw [← h, Subgroup.card_map_of_injective L.subtype_injective]

omit [Finite G] in
theorem pCore_eq_subgroupOf (L : Subgroup G) :
    CFSG.pCore 2 ↥L = (blockQ L).subgroupOf L := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  exact AppC.mem_pCore_iff_mem_blockQ x

theorem card_center_eq_two (hL : IsShort2 L) (hT : IsSylowTwoOf T (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (h5 : IsAltType L 5)
    (hQ : Nat.card ↥(blockQ L) = 2 * Nat.card ↥(blockU L)) :
    Nat.card (Subgroup.center ↥L) = 2 := by
  obtain ⟨hO, hUC⟩ := stmtC113c G L T hT hTN hL h5
  set D := blockQ L ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) with hD
  have hUQ : blockU L ≤ blockQ L := C1.blockU_le_blockQ hL
  have hUL : blockU L ≤ L := hUQ.trans (C1.blockQ_le L)
  have hcomm : ∀ u ∈ blockU L, ∀ d ∈ D, u * d = d * u := fun u hu d hd =>
    Subgroup.mem_centralizer_iff.mp hd.2.2 u (hUL hu)
  have hsup : blockU L ⊔ D = blockQ L := by
    refine le_antisymm (sup_le hUQ inf_le_left) fun n hn => ?_
    have hn' : n ∈ blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [← hO]; exact blockQ_le_pCoreOf hTN hn
    obtain ⟨u, hu, d, hd, rfl⟩ := C5.mem_sup_of_commute (A := blockU L)
      (B := T ⊓ Subgroup.centralizer (L : Set G))
      (fun u hu d hd => Subgroup.mem_centralizer_iff.mp hd.2 u (hUL hu)) hn'
    refine mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ⟨?_, hd⟩)
    have := mul_mem (inv_mem (hUQ hu)) hn
    simpa using this
  have hinf : blockU L ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← hUC]
    exact ⟨hx.1, hx.2.2⟩
  have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hsup, hinf, Subgroup.card_bot, mul_one, hQ] at hcard
  have hUpos : 0 < Nat.card ↥(blockU L) := Nat.card_pos
  have hD2 : Nat.card ↥D = 2 := by
    have : Nat.card ↥(blockU L) * 2 = Nat.card ↥(blockU L) * Nat.card ↥D := by
      rw [← hcard]; ring
    exact (Nat.eq_of_mul_eq_mul_left hUpos this).symm
  have hZD : L ⊓ Subgroup.centralizer (L : Set G) = D := by
    refine le_antisymm (fun z hz => ?_) (fun d hd => ⟨C1.blockQ_le L hd.1, hd.2.2⟩)
    have hzQ : z ∈ blockQ L := hL.2.1 ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun q hq =>
      Subgroup.mem_centralizer_iff.mp hz.2 q (C1.blockQ_le L hq)⟩
    exact ⟨hzQ, hT.pCoreOf_le (blockQ_le_pCoreOf hTN hzQ), hz.2⟩
  rw [card_center_eq_inf, hZD, hD2]

theorem alt5_cover_cases {E : Type} [Group E] [Finite E] (ρ : E →* alternatingGroup (Fin 5))
    (hρs : Function.Surjective ρ) (hkerc : ρ.ker ≤ Subgroup.center E) (hker2 : IsPGroup 2 ρ.ker)
    (hno2 : ∀ I : Subgroup E, I.Normal → (∀ e : E, ∃ n : ℕ, e ^ 2 ^ n ∈ I) → I = ⊤) :
    Function.Injective ρ ∨
      (Nonempty (E ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧ Nat.card ρ.ker = 2) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ, hψs, -⟩ := exists_sl2_five_alt5
  have hk : ringChar (ZMod 5) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hk hρs hkerc hker2 ψ
  have hβx : ∀ g, ρ (β g) = ψ g := fun g => DFunLike.congr_fun hβ g
  have hdecomp : ∀ e : E, ∃ g, (β g)⁻¹ * e ∈ ρ.ker := by
    intro e
    obtain ⟨g, hg⟩ := hψs (ρ e)
    refine ⟨g, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβx, hg, inv_mul_cancel]
  have hIn : β.range.Normal := by
    refine ⟨fun i hi e => ?_⟩
    obtain ⟨g, hg⟩ := hdecomp e
    have he : e = β g * ((β g)⁻¹ * e) := by group
    have hkc := Subgroup.mem_center_iff.mp (hkerc hg)
    obtain ⟨g', rfl⟩ := hi
    rw [he]
    have : β g * ((β g)⁻¹ * e) * β g' * (β g * ((β g)⁻¹ * e))⁻¹ = β g * β g' * (β g)⁻¹ := by
      calc β g * ((β g)⁻¹ * e) * β g' * (β g * ((β g)⁻¹ * e))⁻¹ =
          β g * (((β g)⁻¹ * e) * β g') * ((β g)⁻¹ * e)⁻¹ * (β g)⁻¹ := by group
        _ = β g * (β g' * ((β g)⁻¹ * e)) * ((β g)⁻¹ * e)⁻¹ * (β g)⁻¹ := by rw [← hkc]
        _ = β g * β g' * (β g)⁻¹ := by group
    rw [this, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, rfl⟩
  have hpow : ∀ e : E, ∃ n : ℕ, e ^ 2 ^ n ∈ β.range := by
    intro e
    obtain ⟨g, hg⟩ := hdecomp e
    obtain ⟨n, hn⟩ := hker2 ⟨_, hg⟩
    have hn' : ((β g)⁻¹ * e) ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have hkc := Subgroup.mem_center_iff.mp (hkerc hg)
    have hcomm : Commute (β g) ((β g)⁻¹ * e) := hkc (β g)
    refine ⟨n, ?_⟩
    have : e = β g * ((β g)⁻¹ * e) := by group
    rw [this, hcomm.mul_pow, hn', mul_one, ← map_pow]
    exact ⟨_, rfl⟩
  have htop := hno2 β.range hIn hpow
  have hβs : Function.Surjective β := fun e => by
    have : e ∈ β.range := by rw [htop]; trivial
    exact this
  have hcardE : Nat.card E = 60 * Nat.card ρ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).toEquiv,
      card_alt5'] at h1
    exact h1
  have hle : Nat.card E ≤ 120 := card_sl2_five ▸ Nat.card_le_card_of_surjective β hβs
  obtain ⟨j, hj⟩ := hker2.exists_card_eq
  have hj1 : j ≤ 1 := by
    by_contra hj1
    have h4 : 4 ≤ 2 ^ j := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hcardE, hj] at hle
    omega
  interval_cases j
  · left
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hj, pow_zero])
  · right
    have hE : Nat.card E = 120 := by rw [hcardE, hj]; norm_num
    have hβi : Function.Injective β :=
      ((Nat.bijective_iff_surjective_and_card β).2 ⟨hβs, by rw [card_sl2_five, hE]⟩).1
    exact ⟨⟨(MulEquiv.ofBijective β ⟨hβi, hβs⟩).symm⟩, by rw [hj, pow_one]⟩

theorem exists_quotient_hom_of_alt5 (hL : IsShort2 L) (h5 : IsAltType L 5)
    [((blockU L).subgroupOf L).Normal] :
    ∃ ρ : ↥L ⧸ (blockU L).subgroupOf L →* alternatingGroup (Fin 5),
      Function.Surjective ρ ∧ ρ.ker ≤ Subgroup.center (↥L ⧸ (blockU L).subgroupOf L) ∧
      IsPGroup 2 ρ.ker ∧
      (∀ l : ↥L, (l : ↥L ⧸ (blockU L).subgroupOf L) ∈ ρ.ker ↔ (l : G) ∈ blockQ L) := by
  obtain ⟨α, hαs, hαk, -⟩ := h5
  have hNk : (blockU L).subgroupOf L ≤ α.ker := by
    rw [hαk, pCore_eq_subgroupOf]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (C1.blockU_le_blockQ hL (Subgroup.mem_subgroupOf.mp hx))
  refine ⟨QuotientGroup.lift _ α hNk, ?_, ?_, ?_, ?_⟩
  · intro σ
    obtain ⟨l, rfl⟩ := hαs σ
    exact ⟨(l : ↥L ⧸ (blockU L).subgroupOf L), rfl⟩
  · intro e he
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective e
    have hlQ : (l : G) ∈ blockQ L := by
      have hl : l ∈ α.ker := he
      rw [hαk, pCore_eq_subgroupOf, Subgroup.mem_subgroupOf] at hl
      exact hl
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hmem : ⁅(l : G)⁻¹, (k : G)⁻¹⁆ ∈ blockU L :=
      Subgroup.commutator_mem_commutator ((blockQ L).inv_mem hlQ) (L.inv_mem k.2)
    rw [commutatorElement_def, inv_inv, inv_inv] at hmem
    simpa [mul_assoc] using hmem
  · rintro ⟨e, he⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective e
    have hlQ : (l : G) ∈ blockQ L := by
      have hl : l ∈ α.ker := he
      rw [hαk, pCore_eq_subgroupOf, Subgroup.mem_subgroupOf] at hl
      exact hl
    obtain ⟨n, hn⟩ := C1.exists_pow_eq_one_of_isPGroup (C1.blockQ_isPGroup L) hlQ
    refine ⟨n, Subtype.ext ?_⟩
    show ((l : ↥L ⧸ (blockU L).subgroupOf L)) ^ 2 ^ n = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow, hn]
    exact one_mem _
  · intro l
    show α l = 1 ↔ _
    rw [← MonoidHom.mem_ker, hαk, pCore_eq_subgroupOf, Subgroup.mem_subgroupOf]

theorem quotient_dichotomy_of_alt5 (hL : IsShort2 L) (hT : IsSylowTwoOf T (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (h5 : IsAltType L 5) :
    ∃ _ : ((blockU L).subgroupOf L).Normal,
      Nonempty (↥L ⧸ (blockU L).subgroupOf L ≃* alternatingGroup (Fin 5)) ∨
        (Nonempty (↥L ⧸ (blockU L).subgroupOf L ≃*
            Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
          Nat.card (Subgroup.center ↥L) = 2) := by
  classical
  have hN : ((blockU L).subgroupOf L).Normal := blockU_subgroupOf_normal hL
  refine ⟨hN, ?_⟩
  obtain ⟨ρ, hρs, hkerc, hker2, hker_mk⟩ := exists_quotient_hom_of_alt5 hL h5
  have hno2 : ∀ I : Subgroup (↥L ⧸ (blockU L).subgroupOf L), I.Normal →
      (∀ e, ∃ n : ℕ, e ^ 2 ^ n ∈ I) → I = ⊤ := by
    intro I hI hpow
    have hI' : (I.comap (QuotientGroup.mk' ((blockU L).subgroupOf L))).Normal := hI.comap _
    have hp : IsPGroup 2 (↥L ⧸ I.comap (QuotientGroup.mk' ((blockU L).subgroupOf L))) := by
      intro x
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨n, hn⟩ := hpow (l : ↥L ⧸ (blockU L).subgroupOf L)
      refine ⟨n, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_comap,
        QuotientGroup.mk'_apply, QuotientGroup.mk_pow]
      exact hn
    have htop := hL.1 _ hp
    rw [eq_top_iff]
    intro e _
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective e
    have hl : l ∈ I.comap (QuotientGroup.mk' ((blockU L).subgroupOf L)) := by
      rw [htop]; trivial
    exact hl
  rcases alt5_cover_cases ρ hρs hkerc hker2 hno2 with hinj | ⟨he, hk2⟩
  · exact Or.inl ⟨MulEquiv.ofBijective ρ ⟨hinj, hρs⟩⟩
  · refine Or.inr ⟨he, card_center_eq_two hL hT hTN h5 ?_⟩
    obtain ⟨e⟩ := he
    have hE : Nat.card (↥L ⧸ (blockU L).subgroupOf L) = 120 := by
      rw [Nat.card_congr e.toEquiv, card_sl2_five]
    obtain ⟨α, hαs, hαk, -⟩ := h5
    have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hL).trans (C1.blockQ_le L)
    have hQL : blockQ L ≤ L := C1.blockQ_le L
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((blockU L).subgroupOf L)
    rw [hE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv,
      card_alt5', hαk, pCore_eq_subgroupOf,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv] at h2
    omega

end CFSG.Quasithin.H13.VolI
