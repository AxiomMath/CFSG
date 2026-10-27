module

public import CFSG.Quasithin.Vol2.Ch3Sec3HatXS3
public import CFSG.Quasithin.Vol2.Ch3Sec3HatB
public import CFSG.Quasithin.Vol2.Ch3Sec3G2Step28
public import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Par32
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

namespace HatQ

open CFSG.Quasithin.H13.HatC CFSG.Quasithin.H13.HatM

variable {G : Type} [Group G]

theorem card_A0 : Nat.card A0 = 4 := by
  rw [A0, card_codeSub chk_A0.2.2.1 fun c hc => word_of_Pl (chk_incl.1 c (chk_incl.2.2.2.1 c hc))]
  exact chk_A0.2.2.2

theorem isElemAbelian_sup {H K : Subgroup G} (hH : IsElemAbelian 2 H) (hK : IsElemAbelian 2 K)
    (hHK : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) : IsElemAbelian 2 (H ⊔ K) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hH hK hHK

section Count

variable {L : Subgroup G} (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut W6)
  (β : ↥(blockU L) ≃* W6)

theorem rho_eq_one_of_mem_centralizer
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = ρ g (β u))
    (g : ↥(Subgroup.normalizer (L : Set G)))
    (hg : (g : G) ∈ Subgroup.centralizer (blockU L : Set G)) : ρ g = 1 := by
  refine MulEquiv.ext fun m => ?_
  obtain ⟨u, rfl⟩ := β.surjective m
  have hu : (u : G) = g * u * (g : G)⁻¹ := by
    rw [← Subgroup.mem_centralizer_iff.mp hg _ u.2]
    group
  rw [MulAut.one_apply, ← hβe g u u hu]

theorem card_cU_le [Finite G]
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = ρ g (β u))
    {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer (B : Set G)) ≤
      Nat.card ↥(fixV (ρ.comp (Subgroup.inclusion hBN)).range) := by
  refine Nat.card_le_card_of_injective (fun u => ⟨β ⟨u, u.2.1⟩, ?_⟩) ?_
  · refine mem_fixV.mpr ?_
    rintro _ ⟨b, rfl⟩
    have hbu : ((⟨u, u.2.1⟩ : ↥(blockU L)) : G) = (b : G) * u * (b : G)⁻¹ := by
      show (u : G) = b * u * (b : G)⁻¹
      rw [Subgroup.mem_centralizer_iff.mp u.2.2 b b.2]
      group
    exact (hβe ⟨b, hBN b.2⟩ ⟨u, u.2.1⟩ ⟨u, u.2.1⟩ hbu).symm
  · intro u v h
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (congrArg (fun x : ↥(blockU L) => (x : G)) (β.injective h1))

theorem le_card_mul_of_max [Finite G] (hL : IsShort2 L)
    (hρC : ∀ g, ρ g = 1 → (g : G) ∈ Subgroup.centralizer (blockU L : Set G))
    {R A : Subgroup G} (hUR : blockU L ≤ R) (hA : IsMaxElemAbelian R A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(blockU L) ≤ Nat.card ↥(ρ.comp (Subgroup.inclusion hAN)).range *
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) := by
  set A₁ := A ⊓ Subgroup.centralizer (blockU L : Set G) with hA₁
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    ThreeL32.comm_of_isElemAbelian hA.2.1 ha hb
  have hUe : IsElemAbelian 2 (blockU L) :=
    ⟨⟨⟨fun a b => Subtype.ext (HatR.blockU_comm hL a.2 b.2)⟩⟩, hL.2.2.1.2⟩
  have hA₁e : IsElemAbelian 2 A₁ :=
    ⟨⟨⟨fun a b => Subtype.ext (hAc _ a.2.1 _ b.2.1)⟩⟩, fun x hx => hA.2.1.2 x hx.1⟩
  have hA₁U : ∀ a ∈ A₁, ∀ u ∈ blockU L, a * u = u * a := fun a ha u hu =>
    (Subgroup.mem_centralizer_iff.mp ha.2 u hu).symm
  have h1 : Nat.card ↥A ≤ Nat.card ↥(ρ.comp (Subgroup.inclusion hAN)).range * Nat.card ↥A₁ := by
    have := G2Step28.card_le_range_mul ρ hAN (K := Subgroup.centralizer (blockU L : Set G))
      fun a _ h1 => hρC _ h1
    exact this
  have h2 : Nat.card ↥(A₁ ⊔ blockU L) ≤ Nat.card ↥A :=
    hA.2.2 _ (sup_le (inf_le_left.trans hA.1) hUR) (isElemAbelian_sup hA₁e hUe hA₁U)
  have hUN : blockU L ≤ Subgroup.normalizer (A₁ : Set G) := fun u hu =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hA₁U a ha u hu)
  have h3 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hUN
  have h4 : Nat.card ↥(A₁ ⊓ blockU L) ≤ Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) :=
    Subgroup.card_le_of_le fun x hx =>
      ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun a ha => hAc a ha x hx.1.1⟩
  have hA₁0 : 0 < Nat.card ↥A₁ := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hA₁0
  calc Nat.card ↥A₁ * Nat.card ↥(blockU L) =
        Nat.card ↥(A₁ ⊔ blockU L) * Nat.card ↥(A₁ ⊓ blockU L) := h3.symm
    _ ≤ Nat.card ↥A * Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) :=
        Nat.mul_le_mul h2 h4
    _ ≤ Nat.card ↥(ρ.comp (Subgroup.inclusion hAN)).range * Nat.card ↥A₁ *
          Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) := Nat.mul_le_mul_right _ h1
    _ = _ := by ring

theorem le_qL_of_max [Finite G] {T : Subgroup G} (hH : CFSG.Quasithin.IsHatA6Block L)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = ρ g (β u))
    (hρC : ∀ g, ρ g = 1 → (g : G) ∈ Subgroup.centralizer (blockU L : Set G))
    (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G))
    (hK : ∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 →
      g ∈ qL L T)
    {R : Subgroup G} (hRLT : R ≤ L ⊔ T) (hRr : ∀ x (hx : x ∈ R), ρ ⟨x, hLTN (hRLT hx)⟩ ∈ R0)
    (hUR : blockU L ≤ R) {A : Subgroup G} (hA : IsMaxElemAbelian R A) : A ≤ qL L T := by
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := (hA.1.trans hRLT).trans hLTN
  set RA := (ρ.comp (Subgroup.inclusion hAN)).range with hRA
  by_cases hRA1 : RA = ⊥
  · intro a ha
    refine hK a (hRLT (hA.1 ha)) (hAN ha) ?_
    have h1 : (ρ.comp (Subgroup.inclusion hAN)) ⟨a, ha⟩ ∈ RA := ⟨_, rfl⟩
    rw [hRA1, Subgroup.mem_bot] at h1
    exact h1
  exfalso
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    ThreeL32.comm_of_isElemAbelian hA.2.1 ha hb
  have hRAR : RA ≤ R0 := by
    rintro _ ⟨a, rfl⟩
    exact hRr a.1 (hA.1 a.2)
  have hoff := offender_R0 hRAR hRA1 (G2Step28.range_comm ρ hAN hAc)
    (G2Step28.range_sq ρ hAN hA.2.1.2)
  have h1 := le_card_mul_of_max ρ hH.1 hρC hUR hA hAN
  have h2 := card_cU_le ρ β hβe hAN
  have hU : Nat.card ↥(blockU L) = 64 := hH.2.2.1
  have h3 : Nat.card ↥(blockU L) ≤ Nat.card ↥RA * Nat.card ↥(fixV RA) :=
    h1.trans (Nat.mul_le_mul_left _ h2)
  omega

theorem card_le_of_rho [Finite G] {T Q : Subgroup G}
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = ρ g (β u))
    (hU : Nat.card ↥(blockU L) = 64) (hUQ : blockU L ≤ Q)
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTN ht⟩ ∈ S0)
    (hKT : ∀ t (ht : t ∈ T), ρ ⟨t, hTN ht⟩ = 1 → t ∈ Q)
    {B : Subgroup G} (hBT : B ≤ T) (hBe : IsElemAbelian 2 B) :
    Nat.card ↥B ≤ Nat.card ↥Q ∧ (Nat.card ↥Q ≤ Nat.card ↥B → ¬ B ≤ Q →
      (ρ.comp (Subgroup.inclusion (hBT.trans hTN))).range = A0 ∧
      (Q ⊓ Subgroup.centralizer (B : Set G)).relIndex Q ≤ 4) := by
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBT.trans hTN
  set RB := (ρ.comp (Subgroup.inclusion hBN)).range with hRBdef
  set Y := Q ⊓ Subgroup.centralizer (B : Set G) with hYdef
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    ThreeL32.comm_of_isElemAbelian hBe ha hb
  have hRBS : RB ≤ S0 := by
    rintro _ ⟨b, rfl⟩
    exact hρT b.1 (hBT b.2)
  have hcard : Nat.card ↥B ≤ Nat.card ↥RB * Nat.card ↥Y := by
    have h1 := G2Step28.card_le_range_mul ρ hBN (K := Y) fun b hb h1 =>
      ⟨hKT b (hBT hb) h1, Subgroup.mem_centralizer_iff.mpr fun c hc => hBc c hc b hb⟩
    exact h1.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le inf_le_right))
  have hQY : Y.relIndex Q * Nat.card ↥Y = Nat.card ↥Q := by
    have h1 := Subgroup.relIndex_mul_card Y Q
    rwa [inf_of_le_left (inf_le_left : Y ≤ Q)] at h1
  have hY0 : 0 < Nat.card ↥Y := Nat.card_pos
  have hUY : Y.relIndex (blockU L) ≤ Y.relIndex Q :=
    Subgroup.relIndex_le_of_le_right hUQ Subgroup.index_ne_zero_of_finite
  by_cases hRB1 : RB = ⊥
  · have hBQ : B ≤ Q := fun b hb => hKT b (hBT hb) (by
      have h1 : (ρ.comp (Subgroup.inclusion hBN)) ⟨b, hb⟩ ∈ RB := ⟨_, rfl⟩
      rw [hRB1, Subgroup.mem_bot] at h1
      exact h1)
    exact ⟨Subgroup.card_le_of_le hBQ, fun _ h => absurd hBQ h⟩
  obtain ⟨hle64, hA0⟩ := offender_S0 hRBS hRB1 (G2Step28.range_comm ρ hBN hBc)
    (G2Step28.range_sq ρ hBN hBe.2)
  have hfix0 : 0 < Nat.card ↥(fixV RB) := Nat.card_pos
  have h64 : 64 ≤ Y.relIndex Q * Nat.card ↥(fixV RB) := by
    have h1 := Subgroup.relIndex_mul_card Y (blockU L)
    rw [G2Step28.inf_centralizer_inf hUQ, hU] at h1
    have h2 := card_cU_le ρ β hβe hBN
    calc 64 = Y.relIndex (blockU L) *
          Nat.card ↥(blockU L ⊓ Subgroup.centralizer (B : Set G)) := h1.symm
      _ ≤ Y.relIndex Q * Nat.card ↥(fixV RB) := Nat.mul_le_mul hUY h2
  have hRBY : Nat.card ↥RB ≤ Y.relIndex Q :=
    Nat.le_of_mul_le_mul_right (hle64.trans h64) hfix0
  refine ⟨?_, fun hQB hBQ => ?_⟩
  · calc Nat.card ↥B ≤ Nat.card ↥RB * Nat.card ↥Y := hcard
      _ ≤ Y.relIndex Q * Nat.card ↥Y := Nat.mul_le_mul_right _ hRBY
      _ = Nat.card ↥Q := hQY
  · have hYRB : Y.relIndex Q ≤ Nat.card ↥RB := by
      refine Nat.le_of_mul_le_mul_right ?_ hY0
      rw [hQY]
      exact hQB.trans hcard
    have hRBA := hA0 (h64.trans (Nat.mul_le_mul_right _ hYRB))
    refine ⟨hRBA, ?_⟩
    have h4 : Nat.card ↥RB = 4 := by rw [hRBA, card_A0]
    omega

theorem centralizer_eq_of_rho [Finite G] {Q : Subgroup G}
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = ρ g (β u))
    (hU : Nat.card ↥(blockU L) = 64) (hUQ : blockU L ≤ Q)
    {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hRB : (ρ.comp (Subgroup.inclusion hBN)).range = A0)
    (hY4 : (Q ⊓ Subgroup.centralizer (B : Set G)).relIndex Q ≤ 4) :
    ∃ b ∈ B, Q ⊓ Subgroup.centralizer (B : Set G) = Q ⊓ Subgroup.centralizer ({b} : Set G) := by
  obtain ⟨a, haA, haR⟩ := chk_offA.2.2.1
  obtain ⟨w, hw⟩ := word_of_Pl (chk_incl.1 a (chk_incl.2.2.2.1 a haA))
  have hxA : welt w ∈ A0 := show mcode ⇑(welt w) ∈ A0l by rw [mcode_welt, hw]; exact haA
  have ha1 : a ≠ idc := fun h => haR (h ▸ chk_R.1)
  rw [← hRB] at hxA
  obtain ⟨⟨b, hbB⟩, hb⟩ := hxA
  refine ⟨b, hbB, ?_⟩
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBN hbB
  have hρb : ρ ⟨b, hbN⟩ = welt w := hb
  have hzN : Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set G) := Subgroup.zpowers_le.mpr hbN
  have hfix : Nat.card ↥(fixV (ρ.comp (Subgroup.inclusion hzN)).range) ≤ 16 := by
    have h1 := card_fixV_le (B := (ρ.comp (Subgroup.inclusion hzN)).range) (M := [a])
      (by
        intro m hm
        rw [List.mem_singleton] at hm
        subst hm
        exact ⟨welt w, ⟨⟨b, Subgroup.mem_zpowers b⟩, hρb⟩, by rw [mcode_welt, hw]⟩)
    rw [chk_offA.2.1 a haA ha1] at h1
    exact h1
  have hcz : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) =
      Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcU := card_cU_le ρ β hβe hzN
  rw [hcz] at hcU
  have h4U : 4 ≤ (Q ⊓ Subgroup.centralizer ({b} : Set G)).relIndex (blockU L) := by
    have h1 := Subgroup.relIndex_mul_card (Q ⊓ Subgroup.centralizer ({b} : Set G)) (blockU L)
    rw [G2Step28.inf_centralizer_inf hUQ, hU] at h1
    have h2 : Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ 16 := hcU.trans hfix
    by_contra h3
    push Not at h3
    have h5 : (Q ⊓ Subgroup.centralizer ({b} : Set G)).relIndex (blockU L) *
        Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ 3 * 16 :=
      Nat.mul_le_mul (by omega) h2
    omega
  have hUY : (Q ⊓ Subgroup.centralizer ({b} : Set G)).relIndex (blockU L) ≤
      (Q ⊓ Subgroup.centralizer ({b} : Set G)).relIndex Q :=
    Subgroup.relIndex_le_of_le_right hUQ Subgroup.index_ne_zero_of_finite
  have hYY : Q ⊓ Subgroup.centralizer (B : Set G) ≤ Q ⊓ Subgroup.centralizer ({b} : Set G) :=
    inf_le_inf_left Q (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))
  exact le_antisymm hYY
    (G2Step28.le_of_relIndex_le hYY inf_le_left (hY4.trans (h4U.trans hUY)))

theorem le_sup_of_range {T Q : Subgroup G} (hTN : T ≤ Subgroup.normalizer (L : Set G))
    (hKT : ∀ t (ht : t ∈ T), ρ ⟨t, hTN ht⟩ = 1 → t ∈ Q) {B B' : Subgroup G} (hBT : B ≤ T)
    (hB'T : B' ≤ T)
    (hle : (ρ.comp (Subgroup.inclusion (hBT.trans hTN))).range ≤
      (ρ.comp (Subgroup.inclusion (hB'T.trans hTN))).range) :
    B ≤ B' ⊔ Q := by
  intro x hx
  obtain ⟨⟨x', hx'⟩, hx'e⟩ := hle ⟨⟨x, hx⟩, rfl⟩
  have hmem : x'⁻¹ * x ∈ T := T.mul_mem (T.inv_mem (hB'T hx')) (hBT hx)
  have hq : x'⁻¹ * x ∈ Q := by
    refine hKT _ hmem ?_
    have e : (⟨x'⁻¹ * x, hTN hmem⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨x', hTN (hB'T hx')⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ * ⟨x, hTN (hBT hx)⟩ := rfl
    have e' : ρ ⟨x', hTN (hB'T hx')⟩ = ρ ⟨x, hTN (hBT hx)⟩ := hx'e
    rw [e, map_mul, map_inv, e', inv_mul_cancel]
  have e : x = x' * (x'⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hx' hq

end Count

theorem insp3_3_25HatRest_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hE : HatA6Embed) (hN : HatA6Normalizer) :
    HatB.Insp3_3_25HatRest := by
  intro G _ _ T M L D h hTL hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hG, ρ, β, hβe, hρN, hρL, hρL', hρT, hρC, hK⟩ := HatR.exists_rho hE hN h hTL hH
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hX := HatX.cZ_eq h38 h39 h hTL hH hG ρ β hβe hρN hρL hρL' hρT
  obtain ⟨hXT, -, hRP⟩ := HatX.parabolic_of_rho h hTL ρ hρN hρL' hρT hK
  have hPeq : oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T =
      pre ρ hLTN P0 := by
    rw [hX, hXT]
  have hR : pCoreOf 2 (oTwoUpper (L ⊓ Subgroup.centralizer
      (quasithinOmegaOneCenter T : Set G)) ⊔ T) = pre ρ hLTN R0 := by
    rw [hPeq, hRP]
  have hU : Nat.card ↥(blockU L) = 64 := hH.2.2.1
  have hUL : blockU L ≤ L := commutator_le_right_of_le_normalizer
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans Subgroup.le_normalizer)
  refine ⟨fun A hA => ?_, fun hVQ => ?_⟩
  ·
    rw [hR] at hA
    have hRLT : pre ρ hLTN R0 ≤ L ⊔ T := pre_le_sup ρ hLTN R0
    refine le_qL_of_max ρ β hH hβe hρC hLTN hK hRLT
      (fun x hx => ((mem_pre ρ hLTN).mp hx).2) (fun u hu => ?_) hA
    refine (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_left (hUL hu), ?_⟩
    rw [rho_eq_one_of_mem_centralizer ρ β hβe _ (Subgroup.mem_centralizer_iff.mpr
      fun v hv => HatR.blockU_comm hH.1 hv hu)]
    exact R0.one_mem
  ·
    have hred := Hyp331.vPlus_reduced h.toSetup331
    have hUV : blockU L ≤ vPlus L T := h.blockU_le_vPlus h38 h39 hH.1 hTL
    have hQT : vPlus L T ≤ T := by rw [hVQ]; exact ThreeL32.qL_le h
    have hKT : ∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ = 1 → t ∈ vPlus L T := fun t ht h1 => by
      rw [hVQ]
      exact hK t (Subgroup.mem_sup_right ht) (hTL ht) h1
    have hcount := fun B (hBT : B ≤ T) (hBe : IsElemAbelian 2 B) =>
      card_le_of_rho ρ β hβe hU hUV hTL hρT hKT hBT hBe
    refine ⟨fun B hBT hBe => (hcount B hBT hBe).1, fun B hBm hBV => ?_,
      fun B B' hBm hB'm hBV hB'V => ?_⟩
    · obtain ⟨hRB, hY4⟩ := (hcount B hBm.1 hBm.2.1).2 (hBm.2.2 _ hQT hred.2.1) hBV
      exact centralizer_eq_of_rho ρ β hβe hU hUV (hBm.1.trans hTL) hRB hY4
    · obtain ⟨hRB, -⟩ := (hcount B hBm.1 hBm.2.1).2 (hBm.2.2 _ hQT hred.2.1) hBV
      obtain ⟨hRB', -⟩ := (hcount B' hB'm.1 hB'm.2.1).2 (hB'm.2.2 _ hQT hred.2.1) hB'V
      exact le_antisymm
        (sup_le (le_sup_of_range ρ hTL hKT hBm.1 hB'm.1 (by rw [hRB, hRB'])) le_sup_right)
        (sup_le (le_sup_of_range ρ hTL hKT hB'm.1 hBm.1 (by rw [hRB, hRB'])) le_sup_right)

end HatQ

end CFSG.Quasithin.H13
