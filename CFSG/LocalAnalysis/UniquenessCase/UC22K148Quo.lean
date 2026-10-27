module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Sec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

abbrev SecQ (Y Z : Submodule (ZMod 2) V) : Type := ↥Y ⧸ Z.comap Y.subtype

variable {H : Subgroup G} {Y Z : Submodule (ZMod 2) V}

@[expose] noncomputable def secRep (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z) :
    Representation (ZMod 2) ↥H (SecQ Y Z) :=
  Representation.quotient
    (Representation.subrepresentation (ρ.comp H.subtype) Y fun h y hy => hY h h.2 y hy)
    (Z.comap Y.subtype) fun h y hy => hZ h h.2 y hy

@[expose] noncomputable def secHom (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z) :
    ↥H →* (SecQ Y Z ≃ₗ[ZMod 2] SecQ Y Z) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (SecQ Y Z)).toMonoidHom.comp
    (secRep hY hZ).asGroupHom

variable {hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y} {hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z}

theorem secHom_mk (h : ↥H) (y : ↥Y) :
    secHom hY hZ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk ⟨ρ h y, hY h h.2 y y.2⟩ :=
  rfl

theorem secHom_mk_eq_mk_iff (h : ↥H) (y : ↥Y) :
    secHom hY hZ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk y ↔ ρ h y - y ∈ Z := by
  rw [secHom_mk, Submodule.Quotient.eq, Submodule.mem_comap]
  rfl

theorem secHom_eq_one_iff (h : ↥H) : secHom hY hZ h = 1 ↔ ∀ y ∈ Y, ρ h y - y ∈ Z := by
  constructor
  · intro h1 y hy
    have h2 : secHom hY hZ h (Submodule.Quotient.mk ⟨y, hy⟩) = Submodule.Quotient.mk ⟨y, hy⟩ := by
      rw [h1]
      rfl
    exact (secHom_mk_eq_mk_iff h ⟨y, hy⟩).1 h2
  · intro h1
    refine LinearEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact (secHom_mk_eq_mk_iff h y).2 (h1 y y.2)

theorem finrank_secQ [Finite V] (hZY : Z ≤ Y) :
    finrank (ZMod 2) (SecQ Y Z) = finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥Z := by
  have h1 := Submodule.finrank_quotient_add_finrank (Z.comap Y.subtype)
  rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hZY)] at h1
  change finrank (ZMod 2) (↥Y ⧸ Z.comap Y.subtype) = _
  omega

theorem card_secQ [Finite V] (hZY : Z ≤ Y) :
    Nat.card (SecQ Y Z) = 2 ^ (finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥Z) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_secQ hZY]

theorem card_secQ_sub [Finite V] {P : Submodule (ZMod 2) V} (hZY : Z ≤ Y) (hZP : Z ≤ P) (hPY : P ≤ Y)
    (p : SecQ Y Z → Prop) (hp : ∀ y : ↥Y, p (Submodule.Quotient.mk y) ↔ (y : V) ∈ P) :
    Nat.card {q // p q} = 2 ^ (finrank (ZMod 2) ↥P - finrank (ZMod 2) ↥Z) := by
  set N := Z.comap Y.subtype with hN
  set P' := P.comap Y.subtype with hP'
  set S := P'.map N.mkQ with hS
  have hpS : ∀ q, p q ↔ q ∈ S := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [hp]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y', hy', hyy'⟩
      have h1 : y' - y ∈ N := (Submodule.Quotient.eq N).1 hyy'
      have h2 : (y : V) = y' - (y' - y : ↥Y) := by simp
      rw [h2]
      exact P.sub_mem hy' (hZP h1)
  have hcard : Nat.card {q // p q} = Nat.card ↥S := Nat.card_congr (Equiv.subtypeEquivRight hpS)
  have hNP : N ≤ P' := Submodule.comap_mono hZP
  have hr : LinearMap.range (N.mkQ ∘ₗ P'.subtype) = S := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker (N.mkQ ∘ₗ P'.subtype) = N.comap P'.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have h1 := LinearMap.finrank_range_add_finrank_ker (N.mkQ ∘ₗ P'.subtype)
  rw [hr, hk, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hNP),
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hZY),
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hPY)] at h1
  rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  congr 1
  omega

@[expose] noncomputable def secImg (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z) (D : Subgroup G) :
    Subgroup (SecQ Y Z ≃ₗ[ZMod 2] SecQ Y Z) :=
  (D.subgroupOf H).map (secHom hY hZ)

theorem card_fix_secImg [Finite V] (hZY : Z ≤ Y) {D : Subgroup G} (hDH : D ≤ H) :
    Nat.card {q : SecQ Y Z // ∀ a ∈ secImg hY hZ D, a q = q} =
      2 ^ (finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z D) - finrank (ZMod 2) ↥Z) := by
  refine card_secQ_sub hZY (le_inf hZY (le_modFix fun d hd => hZ d (hDH hd))) inf_le_left _ fun y => ?_
  constructor
  · intro h
    refine ⟨y.2, fun d hd => ?_⟩
    have h1 := h (secHom hY hZ ⟨d, hDH hd⟩) ⟨⟨d, hDH hd⟩, hd, rfl⟩
    exact (secHom_mk_eq_mk_iff _ y).1 h1
  · rintro ⟨-, hy⟩ a ⟨h, hh, rfl⟩
    exact (secHom_mk_eq_mk_iff h y).2 (hy h hh)

theorem card_fix_secHom [Finite V] (hZY : Z ≤ Y) (h : ↥H) :
    Nat.card {q : SecQ Y Z // secHom hY hZ h q = q} =
      2 ^ (finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z (Subgroup.zpowers (h : G))) - finrank (ZMod 2) ↥Z) := by
  have hle : Subgroup.zpowers (h : G) ≤ H := (Subgroup.zpowers_le).2 h.2
  refine card_secQ_sub hZY (le_inf hZY (le_modFix fun a ha => hZ a (hle ha))) inf_le_left _ fun y => ?_
  rw [secHom_mk_eq_mk_iff, Submodule.mem_inf, mem_modFix_zpowers (hZ h h.2) (hZ _ (inv_mem h.2))]
  exact ⟨fun hy => ⟨y.2, hy⟩, fun hy => hy.2⟩

theorem card_secImg_mul {D : Subgroup G} (hDH : D ≤ H) :
    Nat.card (secImg hY hZ D) * Nat.card ↥(D ⊓ secKer ρ Y Z) = Nat.card ↥D := by
  set f : ↥D →* (SecQ Y Z ≃ₗ[ZMod 2] SecQ Y Z) := (secHom hY hZ).comp (Subgroup.inclusion hDH) with hf
  have hrange : secImg hY hZ D = f.range := by
    ext a
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
    · rintro ⟨d, rfl⟩
      exact ⟨Subgroup.inclusion hDH d, d.2, rfl⟩
  have hmem : ∀ d : ↥D, d ∈ f.ker ↔ (d : G) ∈ secKer ρ Y Z := by
    intro d
    rw [MonoidHom.mem_ker]
    change secHom hY hZ (Subgroup.inclusion hDH d) = 1 ↔ _
    rw [secHom_eq_one_iff]
    exact ⟨fun h => mem_secKer_of hZ (hDH d.2) h, fun h => h.1⟩
  have hker : Nat.card f.ker = Nat.card ↥(D ⊓ secKer ρ Y Z) :=
    Nat.card_congr
      { toFun := fun d => ⟨d.1, d.1.2, (hmem d.1).1 d.2⟩
        invFun := fun x => ⟨⟨x, x.2.1⟩, (hmem ⟨x, x.2.1⟩).2 x.2.2⟩
        left_inv := fun d => rfl
        right_inv := fun x => rfl }
  rw [hrange, ← hker, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker).symm

theorem secHom_irr {L : Subgroup G} (hLH : L ≤ H) (hZY : Z ≤ Y)
    (hirr : ∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L W → Z ≤ W → W ≤ Y → W = Z ∨ W = Y)
    (U : Submodule (ZMod 2) (SecQ Y Z))
    (hU : ∀ l : ↥L, ∀ u ∈ U, secHom hY hZ (Subgroup.inclusion hLH l) u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  set N := Z.comap Y.subtype with hN
  set W : Submodule (ZMod 2) V := (U.comap N.mkQ).map Y.subtype with hW
  have hmemW : ∀ y : ↥Y, (y : V) ∈ W ↔ Submodule.Quotient.mk y ∈ U := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      rw [Subtype.ext hyy'] at hy'
      exact hy'
    · intro hy
      exact Submodule.mem_map.2 ⟨y, hy, rfl⟩
  have hZW : Z ≤ W := by
    intro z hz
    refine (hmemW ⟨z, hZY hz⟩).2 ?_
    rw [(Submodule.Quotient.mk_eq_zero N (x := ⟨z, hZY hz⟩)).2 hz]
    exact U.zero_mem
  have hWY : W ≤ Y := Submodule.map_subtype_le _ _
  have hWinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L W := by
    intro l hl w hw
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
    have hy' := (hmemW y).1 ((hmemW y).2 hy)
    have h1 := hU ⟨l, hl⟩ _ hy'
    rw [secHom_mk] at h1
    exact (hmemW _).2 h1
  rcases hirr W hWinv hZW hWY with hWe | hWe
  · left
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
    have hyW : (y : V) ∈ W := (hmemW y).2 hq
    rw [hWe] at hyW
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hyW
  · right
    rw [eq_top_iff]
    rintro q -
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
    have hyW : (y : V) ∈ W := by rw [hWe]; exact y.2
    exact (hmemW y).1 hyW

theorem secQ_nontrivial {y : V} (hy : y ∈ Y) (hyZ : y ∉ Z) : Nontrivial (SecQ Y Z) := by
  refine nontrivial_of_ne (Submodule.Quotient.mk ⟨y, hy⟩) 0 fun h => hyZ ?_
  exact (Submodule.Quotient.mk_eq_zero (Z.comap Y.subtype) (x := ⟨y, hy⟩)).1 h

theorem secImg_normalizes {L D : Subgroup G} (hLH : L ≤ H) (hDN : D ≤ Subgroup.normalizer (L : Set G))
    {a : SecQ Y Z ≃ₗ[ZMod 2] SecQ Y Z} (ha : a ∈ secImg hY hZ D) (x : ↥L) :
    ∃ y : ↥L, a * secHom hY hZ (Subgroup.inclusion hLH x) * a⁻¹ = secHom hY hZ (Subgroup.inclusion hLH y) := by
  obtain ⟨h, hh, rfl⟩ := ha
  have hx : (h : G) * x * (h : G)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (hDN (Subgroup.mem_subgroupOf.1 hh)) x).1 x.2
  refine ⟨⟨_, hx⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem secImg_isElementaryAbelian {D : Subgroup G} (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    CFSG.IsElementaryAbelian 2 ↥(secImg hY hZ D) := by
  obtain ⟨hc, hp⟩ := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 D).1 hD
  refine (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).2 ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨h, hh, rfl⟩⟩ := x
    obtain ⟨_, ⟨k, hk, rfl⟩⟩ := y
    have hhk : h * k = k * h := by
      have h0 := hc.is_comm.comm ⟨h, Subgroup.mem_subgroupOf.1 hh⟩ ⟨k, Subgroup.mem_subgroupOf.1 hk⟩
      have h1 : (h : G) * k = k * h := congrArg Subtype.val h0
      exact Subtype.ext h1
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul, hhk])
  · rintro _ ⟨h, hh, rfl⟩
    have h2 : h ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hp _ (Subgroup.mem_subgroupOf.1 hh), Subgroup.coe_one])
    rw [← map_pow, h2, map_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
