module

public import CFSG.Quasithin.H13.NQRigidCPUCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDefs
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorLayer
public import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.Family (IsComp IsBestOffender)

section Action

variable {Γ : Type} [Group Γ] {V : Subgroup Γ} [V.Normal]

theorem conjNormal_eq_one_iff (g : Γ) :
    (MulAut.conjNormal : Γ →* MulAut ↥V) g = 1 ↔ g ∈ centralizer (V : Set Γ) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h v hv
    have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : Γ)) h
    simp only [MulAut.one_apply, MulAut.conjNormal_apply] at h1
    calc v * g = g * v * g⁻¹ * g := by rw [h1]
      _ = g * v := by group
  · intro h
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.one_apply, ← h v v.2, mul_inv_cancel_right]

theorem eq_bot_of_normal_of_isPGroup_range
    (hVO : CFSG.pCore 2 (Γ ⧸ centralizer (V : Set Γ)) = ⊥) (N : Subgroup (MulAut ↥V))
    (hNG : N ≤ (MulAut.conjNormal : Γ →* MulAut ↥V).range)
    (hGN : (MulAut.conjNormal : Γ →* MulAut ↥V).range ≤ normalizer (N : Set (MulAut ↥V)))
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : Γ →* MulAut ↥V := MulAut.conjNormal
  have hN'n : (N.comap ρ).Normal := by
    refine ⟨fun x hx b => ?_⟩
    show ρ (b * x * b⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hGN ⟨b, rfl⟩) (ρ x)).mp hx
  have hN''n : ((N.comap ρ).map (QuotientGroup.mk' (centralizer (V : Set Γ)))).Normal :=
    hN'n.map _ (QuotientGroup.mk'_surjective _)
  have hN''2 : IsPGroup 2 ↥((N.comap ρ).map (QuotientGroup.mk' (centralizer (V : Set Γ)))) := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    obtain ⟨n, hn⟩ := hN2 ⟨ρ x, hx⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : ρ (x ^ 2 ^ n) = 1 := by
      rw [map_pow]
      have := congrArg Subtype.val hn
      simpa using this
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact (conjNormal_eq_one_iff _).mp h1
  have hle := SteinbergCC.le_pCore_of_normal_of_isPGroup hN''n hN''2
  rw [hVO, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := hNG hy
  have h1 : QuotientGroup.mk' (centralizer (V : Set Γ)) x ∈
      (N.comap ρ).map (QuotientGroup.mk' (centralizer (V : Set Γ))) := mem_map_of_mem _ hy
  rw [hle, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact (mem_bot).mpr ((conjNormal_eq_one_iff x).mpr h1)

theorem isTwoReducedIn_top (hVe : CFSG.IsElementaryAbelian 2 ↥V)
    (hVO : CFSG.pCore 2 (Γ ⧸ centralizer (V : Set Γ)) = ⊥) : IsTwoReducedIn (⊤ : Subgroup Γ) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, (normalizer_eq_top_iff.mpr inferInstance).ge,
    (CFSG.Quasithin.BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mpr hVe,
    fun D _ hDN hD2 => ?_⟩
  have hDn : D.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp hDN)
  have hD'n : (D.map (QuotientGroup.mk' (centralizer (V : Set Γ)))).Normal :=
    hDn.map _ (QuotientGroup.mk'_surjective _)
  have hD'2 : IsPGroup 2 ↥(D.map (QuotientGroup.mk' (centralizer (V : Set Γ)))) := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    obtain ⟨k, hk⟩ := hD2 x hx
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hk
  have hle := SteinbergCC.le_pCore_of_normal_of_isPGroup hD'n hD'2
  rw [hVO, le_bot_iff] at hle
  intro x hx
  have h1 : QuotientGroup.mk' (centralizer (V : Set Γ)) x ∈
      D.map (QuotientGroup.mk' (centralizer (V : Set Γ))) := mem_map_of_mem _ hx
  rw [hle, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem autOn_top_eq_range :
    autOn (⊤ : Subgroup Γ) V = (MulAut.conjNormal : Γ →* MulAut ↥V).range := by
  have hVN : (⊤ : Subgroup Γ) ≤ normalizer (V : Set Γ) :=
    (normalizer_eq_top_iff.mpr inferInstance).ge
  ext φ
  rw [CFSG.QuasithinUnique.Setup.mem_autOn_iff]
  constructor
  · rintro ⟨g, -, rfl⟩
    refine ⟨g, MulEquiv.ext fun v => Subtype.ext ?_⟩
    rw [MulAut.conjNormal_apply, CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
  · rintro ⟨g, rfl⟩
    refine ⟨⟨g, hVN (mem_top g)⟩, mem_top g, MulEquiv.ext fun v => Subtype.ext ?_⟩
    rw [MulAut.conjNormal_apply, CFSG.QuasithinUnique.Setup.coe_conjAct_apply]

omit [V.Normal] in
theorem charTwo_top_of_isCharacteristicP (hchar : CFSG.IsCharacteristicP 2 Γ) :
    CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup Γ) := by
  rw [CFSG.QuasithinUnique.charTwo_iff_internal]
  exact CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv topEquiv.symm hchar

end Action

section Complement

variable {Γ₀ : Type} [Group Γ₀] [Finite Γ₀] {G₀ L₀ P₀ : Subgroup Γ₀}

theorem eq_one_of_mem_centralizer
    (hO2 : ∀ N : Subgroup Γ₀, N ≤ G₀ → G₀ ≤ normalizer (N : Set Γ₀) → IsPGroup 2 N → N = ⊥)
    (hGL : G₀ ≤ normalizer (L₀ : Set Γ₀)) (hP₀2 : IsPGroup 2 P₀) (hPG : P₀ ≤ G₀)
    (hGLP : ∀ g ∈ G₀, ∃ l ∈ L₀, ∃ s ∈ P₀, g = l * s) (hZ : center ↥L₀ = ⊥) :
    ∀ g ∈ G₀, g ∈ centralizer (L₀ : Set Γ₀) → g = 1 := by
  have hE2 : IsPGroup 2 ↥(G₀ ⊓ centralizer (L₀ : Set Γ₀)) := by
    rintro ⟨x, hx⟩
    obtain ⟨hxG, hxC⟩ := mem_inf.mp hx
    obtain ⟨l, hl, s, hs, hls⟩ := hGLP x hxG
    obtain ⟨k, hk⟩ := hP₀2 ⟨s, hs⟩
    have hsk : s ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨l', hl', he⟩ := exists_pow_eq_mul_pow (hGL (hPG hs)) hl (2 ^ k)
    have hxk : x ^ 2 ^ k = l' := by rw [hls, he, hsk, mul_one]
    have hl'c : l' ∈ centralizer (L₀ : Set Γ₀) := hxk ▸ pow_mem hxC _
    have hl'Z : (⟨l', hl'⟩ : ↥L₀) ∈ center ↥L₀ := by
      rw [mem_center_iff]
      intro z
      exact Subtype.ext (mem_centralizer_iff.mp hl'c z z.2)
    rw [hZ, mem_bot] at hl'Z
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    show x ^ 2 ^ k = 1
    rw [hxk]
    exact congrArg Subtype.val hl'Z
  have h0 := eq_bot_of_le_centralizer hO2 hGL hP₀2 hPG hGLP hE2 inf_le_left inf_le_right
  intro g hg hgc
  have hmem : g ∈ G₀ ⊓ centralizer (L₀ : Set Γ₀) := mem_inf.mpr ⟨hg, hgc⟩
  rw [h0, mem_bot] at hmem
  exact hmem

theorem isCompList_one (hL : IsComp L₀ G₀)
    (hE : ∀ g ∈ G₀, g ∈ centralizer (L₀ : Set Γ₀) → g = 1) :
    CFSG.QuasithinUnique.Setup.Lift.IsCompList G₀ 1 (fun _ => L₀) := by
  refine ⟨fun i j _ => Subsingleton.elim i j, fun _ => hL, fun D hD => ⟨0, ?_⟩⟩
  by_contra hne
  have hcomm := CFSG.QuasithinUnique.Setup.Layer.Actor.commutator_eq_bot_of_isComponentIn_ne'
    ((CFSG.QuasithinUnique.Setup.Layer.Actor.isComp_iff _ _).mp hD)
    ((CFSG.QuasithinUnique.Setup.Layer.Actor.isComp_iff _ _).mp hL) (Ne.symm hne)
  rw [commutator_eq_bot_iff_le_centralizer] at hcomm
  have hall : ∀ d : ↥D, d = 1 := fun d => Subtype.ext (hE d (hD.1 d.2) (hcomm d.2))
  have : Nontrivial (↥D ⧸ center ↥D) := hD.2.2.2.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥D ⧸ center ↥D)
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y => exact hab (by rw [hall x, hall y])

end Complement

section Offender

variable {V : Type} [CommGroup V] [Finite V] {G₀ L₀ P₀ B₀ : Subgroup (MulAut V)}

theorem exists_bestOffender_le
    (hO2 : ∀ N : Subgroup (MulAut V), N ≤ G₀ → G₀ ≤ normalizer (N : Set (MulAut V)) →
      IsPGroup 2 N → N = ⊥)
    (hGL : G₀ ≤ normalizer (L₀ : Set (MulAut V))) (hP₀2 : IsPGroup 2 P₀) (hPG : P₀ ≤ G₀)
    (hGLP : ∀ g ∈ G₀, ∃ l ∈ L₀, ∃ s ∈ P₀, g = l * s) (hB₀P : B₀ ≤ P₀) (hB₀ne : B₀ ≠ ⊥)
    (hB₀el : CFSG.IsElementaryAbelian 2 ↥B₀)
    (hbest : ∀ D : Subgroup (MulAut V), D ≤ B₀ →
      Nat.card D * Nat.card {v : V // ∀ d ∈ D, d v = v} ≤
        Nat.card B₀ * Nat.card {v : V // ∀ d ∈ B₀, d v = v}) :
    ∃ X : Subgroup (MulAut V), X ≤ B₀ ∧ IsBestOffender G₀ X ∧ ⁅L₀, X⁆ ≠ ⊥ := by
  classical
  have hB₀G : B₀ ≤ G₀ := hB₀P.trans hPG
  have hB₀2 : IsPGroup 2 B₀ := hP₀2.to_le hB₀P
  let w : Subgroup (MulAut V) → ℕ := fun X => Nat.card X * Nat.card (fixV X)
  have hwfix : ∀ X : Subgroup (MulAut V),
      Nat.card X * Nat.card {v : V // ∀ d ∈ X, d v = v} = w X := fun X => rfl
  have hbest' : ∀ X ≤ B₀, w X ≤ w B₀ := fun X hX => by
    rw [← hwfix, ← hwfix]
    exact hbest X hX
  have hex : ∃ n, ∃ X : Subgroup (MulAut V), X ≤ B₀ ∧ X ≠ ⊥ ∧ w X = w B₀ ∧ Nat.card X = n :=
    ⟨_, B₀, le_rfl, hB₀ne, rfl, rfl⟩
  obtain ⟨X, hXB₀, hX1, hXw, hXn⟩ := Nat.find_spec hex
  have hXmin : ∀ Y : Subgroup (MulAut V), Y ≤ B₀ → Y ≠ ⊥ → w Y = w B₀ →
      Nat.find hex ≤ Nat.card Y := fun Y hY1 hY2 hY3 => Nat.find_min' hex ⟨Y, hY1, hY2, hY3, rfl⟩
  have hXbest : IsBestOffender G₀ X := by
    refine ⟨hXB₀.trans hB₀G, hX1, ⟨fun a ha b hb => ?_, fun a ha => ?_⟩, ?_, ?_⟩
    · exact congrArg Subtype.val
        (hB₀el.toIsMulCommutative.is_comm.comm ⟨a, hXB₀ ha⟩ ⟨b, hXB₀ hb⟩)
    · have h1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hB₀el.exponent_dvd_p ⟨a, hXB₀ ha⟩
      exact congrArg Subtype.val h1
    · have h1 := hbest' ⊥ bot_le
      rw [← hXw] at h1
      have h2 : w ⊥ = Nat.card V := by
        show Nat.card ↥(⊥ : Subgroup (MulAut V)) * Nat.card ↥(fixV ⊥) = Nat.card V
        rw [card_bot, one_mul]
        exact Nat.card_congr ((Equiv.subtypeUnivEquiv fun v => by
          intro x hx
          rw [mem_bot] at hx
          rw [hx, MulAut.one_apply]))
      rw [h2] at h1
      exact h1
    · intro Y hYX hY1 hYX'
      have hYw : w Y ≤ w X := hXw ▸ hbest' Y (hYX.trans hXB₀)
      refine lt_of_le_of_ne hYw fun heq => ?_
      have h1 := hXmin Y (hYX.trans hXB₀) hY1 (heq.trans hXw)
      rw [← hXn] at h1
      have h2 : Nat.card Y < Nat.card X :=
        card_lt_of_lt (lt_of_le_of_ne hYX hYX')
      omega
  refine ⟨X, hXB₀, hXbest, fun h0 => hX1 ?_⟩
  refine eq_bot_of_le_centralizer hO2 hGL hP₀2 hPG hGLP (hB₀2.to_le hXB₀)
    (hXB₀.trans hB₀G) ?_
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at h0
  exact h0

end Offender


section Image

variable {Γ Γ₀ : Type} [Group Γ] [Group Γ₀]

theorem sylow_max_of_image (ρ : Γ →* Γ₀) {S : Subgroup Γ} {U : Subgroup Γ₀}
    (hS2 : IsPGroup 2 S) (hker : ρ.ker ≤ S)
    (hO2 : ∀ N : Subgroup Γ₀, N ≤ ρ.range → ρ.range ≤ normalizer (N : Set Γ₀) →
      IsPGroup 2 N → N = ⊥)
    (hU2 : IsPGroup 2 U) (hUle : U ≤ ρ.range) (hU1 : U ≠ ⊥)
    (hidx : ¬ 2 ∣ (S.map ρ).relIndex ρ.range) (hPU : S.map ρ ≤ normalizer (U : Set Γ₀))
    (hmaxU : ∀ Y : Subgroup Γ₀, S.map ρ ≤ Y → Y ≤ ρ.range → Y ≠ ρ.range →
      Y ≤ normalizer (U : Set Γ₀))
    (hP1 : S.map ρ ≠ ⊥) :
    CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ ∧ ¬ (S.subgroupOf (⊤ : Subgroup Γ)).Normal ∧
      (S ≤ (normalizer (U : Set Γ₀)).comap ρ ∧ (normalizer (U : Set Γ₀)).comap ρ < ⊤ ∧
        ∀ Y : Subgroup Γ, S ≤ Y → Y < ⊤ → Y ≤ (normalizer (U : Set Γ₀)).comap ρ) := by
  have hfull : ∀ Y : Subgroup Γ, ρ.ker ≤ Y → Y.map ρ = ρ.range → Y = ⊤ := by
    intro Y hkY h
    rw [eq_top_iff]
    intro x _
    have hx : ρ x ∈ Y.map ρ := h ▸ ⟨x, rfl⟩
    obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
    have h1 : y⁻¹ * x ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have h3 : x = y * (y⁻¹ * x) := by group
    rw [h3]
    exact mul_mem hy (hkY h1)
  refine ⟨⟨le_top, hS2, fun h2 => hidx ?_⟩, fun hnorm => hP1 ?_,
    fun s hs => hPU (mem_map_of_mem ρ hs), lt_top_iff_ne_top.mpr fun h => hU1 ?_,
    fun Y hSY hYt => ?_⟩
  ·
    have hcomap : ((S.map ρ).subgroupOf ρ.range).comap ρ.rangeRestrict = S := by
      ext x
      rw [mem_comap, mem_subgroupOf]
      constructor
      · intro hx
        obtain ⟨s, hs, hsx⟩ := mem_map.mp hx
        have h1 : s⁻¹ * x ∈ ρ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv]
          have hsx' : ρ s = ρ x := hsx
          rw [hsx', inv_mul_cancel]
        have h3 : x = s * (s⁻¹ * x) := by group
        rw [h3]
        exact mul_mem hs (hker h1)
      · intro hx
        exact mem_map_of_mem ρ hx
    have h1 := index_comap_of_surjective ((S.map ρ).subgroupOf ρ.range) ρ.rangeRestrict_surjective
    rw [hcomap] at h1
    have h3 : (S.subgroupOf (⊤ : Subgroup Γ)).index = S.index := relIndex_top_right S
    rw [h3, h1] at h2
    exact h2
  ·
    have hSN : (⊤ : Subgroup Γ) ≤ normalizer (S : Set Γ) :=
      (normal_subgroupOf_iff_le_normalizer le_top).mp hnorm
    refine hO2 _ (map_le_range ρ S) ?_ (hS2.map ρ)
    rintro _ ⟨x, rfl⟩
    exact le_normalizer_map ρ ⟨x, hSN (mem_top x), rfl⟩
  ·
    refine hO2 U hUle ?_ hU2
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ (normalizer (U : Set Γ₀)).comap ρ := h ▸ mem_top x
    exact hx
  ·
    have hYne : Y.map ρ ≠ ρ.range := fun h => hYt.ne (hfull Y (hker.trans hSY) h)
    exact map_le_iff_le_comap.mp (hmaxU _ (map_mono hSY) (map_le_range ρ Y) hYne)

end Image

theorem not_le_normalizer_of_char_baum {Γ : Type} [Group Γ] {L S M : Subgroup Γ}
    (hLM : ¬ L ≤ M)
    (hM : ∀ D : Subgroup ↥S, D.Characteristic → D ≠ ⊥ →
      normalizer ((D.map S.subtype : Subgroup Γ) : Set Γ) ≤ M) :
    ∀ Rc : Subgroup Γ, Rc ≠ ⊥ → Rc ≤ baum S → (Rc.subgroupOf (baum S)).Characteristic →
      ¬ (⊤ : Subgroup Γ) ≤ normalizer (Rc : Set Γ) := by
  intro Rc hne hle hch htop
  have hRcS : Rc ≤ S := hle.trans (C1GN.baum_le S)
  have hch' : (Rc.subgroupOf S).Characteristic :=
    C1GN.characteristic_subgroupOf_trans (C1GN.baum_le S) hle (C1GN.characteristic_baum S) hch
  have hD1 : Rc.subgroupOf S ≠ ⊥ := by
    intro h0
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hRcS hx⟩ : ↥S) ∈ Rc.subgroupOf S := hx
    rw [h0, mem_bot] at h1
    exact (mem_bot).mpr (congrArg Subtype.val h1)
  have h1 := hM (Rc.subgroupOf S) hch' hD1
  rw [subgroupOf_map_subtype, inf_eq_left.mpr hRcS] at h1
  exact hLM (le_top.trans (htop.trans h1))

end CFSG.Quasithin.H13.NQRigid
