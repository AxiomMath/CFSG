module

public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Defs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction
public import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseOut

public section

section OutRed

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.Out

theorem central_hom_eq_one {G : Type*} [Group G] (hperf : Group.IsPerfect G) (ψ : G →* G)
    (hψ : ∀ g, ψ g ∈ Subgroup.center G) : ∀ g, ψ g = 1 := by
  have hcomm : ∀ a b : G, ψ ⁅a, b⁆ = 1 := by
    intro a b
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hψ a) (ψ b)).symm
  have hle : commutator G ≤ ψ.ker := by
    refine Subgroup.commutator_le.mpr ?_
    intro a _ b _
    exact MonoidHom.mem_ker.mpr (hcomm a b)
  rw [hperf.commutator_eq_top] at hle
  intro g
  exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top g))

theorem conj_trivial_of_perfect {G : Type*} [Group G] (hperf : Group.IsPerfect G) (c : G →* G)
    (hc : ∀ g, c g * g⁻¹ ∈ Subgroup.center G) : ∀ g, c g = g := by
  have hmul : ∀ a b : G, c (a * b) * (a * b)⁻¹ = (c a * a⁻¹) * (c b * b⁻¹) := by
    intro a b
    have hb' : (c b * b⁻¹) * a⁻¹ = a⁻¹ * (c b * b⁻¹) :=
      (Subgroup.mem_center_iff.mp (hc b) a⁻¹).symm
    calc c (a * b) * (a * b)⁻¹ = c a * ((c b * b⁻¹) * a⁻¹) := by rw [map_mul]; group
      _ = c a * (a⁻¹ * (c b * b⁻¹)) := by rw [hb']
      _ = (c a * a⁻¹) * (c b * b⁻¹) := by rw [mul_assoc]
  let ψ : G →* G := MonoidHom.mk' (fun g => c g * g⁻¹) hmul
  have h := central_hom_eq_one hperf ψ hc
  intro g
  have h' : c g * g⁻¹ = 1 := h g
  exact mul_inv_eq_one.mp h'

theorem persist_outer {K M : Type*} [Group K] [Group M] {L B : Subgroup K}
    (hperf : Group.IsPerfect ↥L) (hBN : B ≤ Subgroup.normalizer (L : Set K))
    (hcent : (L ⊔ B) ⊓ Subgroup.centralizer (L : Set K) ≤ L) (hBL : B ⊓ L = ⊥)
    (τ : ↥(L ⊔ B) →* M)
    (hker : ∀ l : ↥L, τ (Subgroup.inclusion le_sup_left l) = 1 → l ∈ Subgroup.center ↥L) :
    (τ.comp (Subgroup.inclusion (le_sup_right : B ≤ L ⊔ B))).range ⊓
      (τ.comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ B))).range = ⊥ := by
  rw [eq_bot_iff]
  intro e he
  rw [Subgroup.mem_bot]
  obtain ⟨hB, hL⟩ := Subgroup.mem_inf.mp he
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hB
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hL
  have hb' : τ (Subgroup.inclusion (le_sup_right : B ≤ L ⊔ B) b) = e := hb
  have hl' : τ (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ B) l) = e := hl
  obtain ⟨x, hxdef⟩ : ∃ x : ↥(L ⊔ B),
      x = (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ B) l)⁻¹ *
        Subgroup.inclusion (le_sup_right : B ≤ L ⊔ B) b := ⟨_, rfl⟩
  have hτx : τ x = 1 := by
    rw [hxdef, map_mul, map_inv, hl', hb', inv_mul_cancel]
  have hxK : (x : K) = (l : K)⁻¹ * (b : K) := by
    subst hxdef
    rfl
  have hxN : ∀ g : ↥L, (x : K) * (g : K) * (x : K)⁻¹ ∈ L := by
    intro g
    have hbg : (b : K) * (g : K) * (b : K)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hBN b.2) (g : K)).mp g.2
    have key : (x : K) * (g : K) * (x : K)⁻¹ =
        (l : K)⁻¹ * ((b : K) * (g : K) * (b : K)⁻¹) * (l : K) := by
      rw [hxK]
      group
    rw [key]
    exact L.mul_mem (L.mul_mem (L.inv_mem l.2) hbg) l.2
  let c : ↥L →* ↥L :=
    { toFun := fun g => ⟨(x : K) * (g : K) * (x : K)⁻¹, hxN g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun p q => Subtype.ext (by simp [mul_assoc]) }
  have hcg : ∀ g : ↥L, Subgroup.inclusion (le_sup_left : L ≤ L ⊔ B) (c g) =
      x * Subgroup.inclusion (le_sup_left : L ≤ L ⊔ B) g * x⁻¹ :=
    fun g => Subtype.ext rfl
  have hc : ∀ g : ↥L, c g * g⁻¹ ∈ Subgroup.center ↥L := by
    intro g
    apply hker
    rw [map_mul, map_inv, hcg]
    simp [map_mul, map_inv, hτx]
  have hcid := conj_trivial_of_perfect hperf c hc
  have hxC : (x : K) ∈ Subgroup.centralizer (L : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : c ⟨h, hh⟩ = ⟨h, hh⟩ := hcid ⟨h, hh⟩
    have h2 : (x : K) * h * (x : K)⁻¹ = h := congrArg Subtype.val h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  have hxL : (x : K) ∈ L :=
    hcent (show (x : K) ∈ (L ⊔ B) ⊓ Subgroup.centralizer (L : Set K) from ⟨x.2, hxC⟩)
  have hbK : (b : K) = (l : K) * (x : K) := by
    rw [hxK, mul_inv_cancel_left]
  have hbL : (b : K) ∈ L := by
    rw [hbK]
    exact L.mul_mem l.2 hxL
  have hb1 : (b : K) = 1 := by
    have hmem : (b : K) ∈ B ⊓ L := Subgroup.mem_inf.mpr ⟨b.2, hbL⟩
    rw [hBL, Subgroup.mem_bot] at hmem
    exact hmem
  have hb1' : b = 1 := Subtype.ext hb1
  rw [← hb', hb1']
  simp

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.StructureLie

@[expose] def NoOuterIrrFFOffender (Y : Type) [Group Y] : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L →
      CFSG.QuasithinUnique.Setup.X1.IsIrrOn L →
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* Y) →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E →
      IsQuadratic E → E ⊓ L = ⊥ → Nat.card E ≤ 4 →
        Nat.card E * Nat.card (fixV E) < Nat.card W

theorem noOuterFFOffender_of_noOuterIrr {Y : Type} [Group Y] (hout : OutTwoRank Y)
    (h : NoOuterIrrFFOffender Y) : F153L3C2.NoOuterFFOffender Y := by
  intro V _ _ hV H L hhyp ⟨e⟩ A hAH hAne hAel hAL
  by_contra hcon
  have hAoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := not_lt.1 hcon
  obtain ⟨hLF, hLq, hO2, -⟩ := hhyp
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨B, hBA, hB⟩ := exists_isBestOffender_le hAH hAne hAel hAoff
  have hLH : L ≤ H := hLF ▸ quasithinGenFitting_le H
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting H
  have hLcomp : Family.IsComp L H :=
    ⟨hLH, IsSubnormal.step hLH ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN)
      (IsSubnormal.refl H), ⟨hLq.1.commutator_eq_top, hLq.2.1⟩⟩
  have hLB : ⁅L, B⁆ ≠ ⊥ := commutator_ne_bot_of_elemAbelian hLF hO2 hB.1 hB.2.1 hB.2.2.1
  obtain ⟨hBN, -, ⟨sec⟩⟩ := Layer.Actor.irreducibleSectionProp V hV' H L B hLcomp hB hLB
  have hcentH : H ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L := by
    have h1 := centralizer_quasithinGenFitting_le H
    rwa [← hLF] at h1
  have hA2 : IsPGroup 2 ↥A := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hAel.2 (x : MulAut V) x.2⟩
  have hout' : OutTwoRank (↥L ⧸ Subgroup.center ↥L) := OutTwoRank.of_mulEquiv e.symm hout
  have hB4 : Nat.card B ≤ 4 :=
    (out_bound H L A (Subgroup.isPerfect_iff.mp hLq.1) hLH hHN hcentH hAH hA2 hAL hout').2 B hBA
      (fun a ha => hB.2.2.1.2 a ha)
  set ρ : ↥L →* MulAut sec.W := sec.τW.comp (Subgroup.inclusion le_sup_left) with hρ
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hφ : ∃ k, ρ.rangeRestrict k ≠ 1 := by
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 sec.lbar_ne_bot
    obtain ⟨k, hk⟩ := hsurj a
    exact ⟨k, hk ▸ ha⟩
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hLq hφ
  let eL := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hLq hsurj hker
  have hBL : B ⊓ L = ⊥ := eq_bot_iff.2 (fun x hx => by
    have : x ∈ A ⊓ L := ⟨hBA hx.1, hx.2⟩
    rw [hAL] at this
    exact this)
  have hperf : Group.IsPerfect ↥L := hLq.1
  have hLBH : L ⊔ B ≤ H := sup_le hLH hB.1
  have hcentLB : (L ⊔ B) ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L :=
    (inf_le_inf_right _ hLBH).trans hcentH
  have hker' : ∀ l : ↥L, sec.τW (Subgroup.inclusion le_sup_left l) = 1 → l ∈ Subgroup.center ↥L :=
    fun l hl => hker (by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext hl)
  have hpers := persist_outer hperf hBN hcentLB hBL sec.τW hker'
  have hEb4 : Nat.card (sec.τW.comp (Subgroup.inclusion (le_sup_right : B ≤ L ⊔ B))).range ≤ 4 :=
    (Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)).trans hB4
  have hlt := h sec.W (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.irrSection_sq hV' sec) ρ.range
    (sec.τW.comp (Subgroup.inclusion le_sup_right)).range sec.lbar_quasisimple
    (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.irrSection_isIrrOn sec) ⟨eL.symm.trans e⟩
    (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.irrSection_range_le_normalizer sec hBN) sec.abar_ne_bot
    sec.abar_elem sec.abar_quadratic hpers hEb4
  exact absurd sec.abar_offender (not_le.2 hlt)

end CFSG.RankThree.PartTwo.Sec15.F153L3K.Out

end OutRed
