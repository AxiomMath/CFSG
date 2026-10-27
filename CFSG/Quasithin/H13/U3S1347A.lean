module

public import CFSG.Quasithin.H13.GoldEdgeS3
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCZ
public import CFSG.Quasithin.H13.U3S13227H
public import CFSG.Quasithin.H13.U3S1349B

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s1347_relIndex_three (S : A6.Setting134 G T L V) {H : Subgroup G} (hTH : T ≤ H)
    (hq : quasithinO2QuotientIso H (Perm (Fin 3))) : T.relIndex H = 3 :=
  relIndex_eq_three_of_quot hq (A5.isSylowTwoOf_of_le S.h13.sylow hTH)

theorem s1347_inf_eq (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂) :
    H₁ ⊓ H₂ = T := by
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  rcases eq_or_eq_of_relIndex_three h3₁ (le_inf h.inH₁.1 h.inH₂.1) inf_le_left with h1 | h1
  · exact h1
  · exfalso
    have hle : H₁ ≤ H₂ := h1 ▸ inf_le_right
    rcases eq_or_eq_of_relIndex_three h3₂ h.inH₁.1 hle with h2 | h2
    · rw [h2, relIndex_self] at h3₁
      omega
    · exact h.ne h2

theorem s1347_triple (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂) :
    F6.IsGoldschmidtTripleIn (H₁ ⊔ H₂) H₁ H₂ := by
  have hiso : ∀ {H : Subgroup G}, quasithinO2QuotientIso H (Perm (Fin 3)) →
      Nonempty (↥H ⧸ Open.pCore 2 ↥H ≃* Perm (Fin 3)) := fun hq => by
    obtain ⟨e⟩ := (quasithinO2QuotientIso_iff _ _).1 hq
    exact ⟨(QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open _ 2).symm).trans e⟩
  refine ⟨rfl, hiso h.s3₁, hiso h.s3₂, ?_⟩
  rw [s1347_inf_eq S h]
  exact A5.isSylowTwoOf_of_le S.h13.sylow (h.inH₁.1.trans le_sup_left)

theorem s134_card_T_ge (S : A6.Setting134 G T L V) : 2 ^ 8 ≤ Nat.card T := by
  set ρ := S.frame.ρ with hρ
  set T' := T.subgroupOf (normalizer (V : Set G)) with hT'
  have hTN : T ≤ normalizer (V : Set G) := S.frame.T_le
  have himg : A6.QA6sub ≤ T'.map ρ := by
    intro σ hσ
    obtain ⟨hD, hA⟩ := mem_inf.1 hσ
    obtain ⟨g, hgT, hgσ⟩ := s134_exists_TL S hD hA
    exact ⟨g, mem_subgroupOf.2 (mem_inf.1 hgT).1, hgσ⟩
  have h8 : 8 ≤ Nat.card ↥(T'.map ρ) := by
    rw [← A6.card_QA6sub]
    exact card_le_of_le himg
  have hker : (V.subgroupOf (normalizer (V : Set G))) ≤ ρ.ker ⊓ T' := by
    intro x hx
    rw [mem_subgroupOf] at hx
    refine mem_inf.2 ⟨?_, mem_subgroupOf.2 (S.V_le_T hx)⟩
    rw [MonoidHom.mem_ker, s134_rho_eq_one_iff]
    refine mem_centralizer_iff.2 fun v hv => ?_
    have h1 : (⟨v, hv⟩ : ↥V) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨v, hv⟩ :=
      S.frame.ψ.injective (by rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h1
  have h32 : 32 ≤ Nat.card ↥(ρ.ker ⊓ T') := by
    have := card_le_of_le hker
    rwa [Nat.card_congr (subgroupOfEquivOfLe (le_normalizer : V ≤ _)).toEquiv,
      S.card_V] at this
  have hcard : Nat.card ↥(T'.map ρ) * Nat.card ↥(ρ.ker ⊓ T') = Nat.card T := by
    have h1 := relIndex_mul_card ρ.ker T'
    rw [relIndex_ker] at h1
    rw [h1, hT', Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv]
  calc 2 ^ 8 = 8 * 32 := by norm_num
    _ ≤ Nat.card ↥(T'.map ρ) * Nat.card ↥(ρ.ker ⊓ T') := Nat.mul_le_mul h8 h32
    _ = Nat.card T := hcard

theorem s1347_inH (hedge : GoldschmidtEdgeBoundS3) (S : A6.Setting134 G T L V)
    {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂) : InH T (H₁ ⊔ H₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨h.inH₁.1.trans le_sup_left, fun hO => ?_⟩
  have htr := (s1347_triple S h).subgroupOf
  have hpc : CFSG.pCore 2 ↥(H₁ ⊔ H₂) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxO : (x : G) ∈ pCoreOf 2 (H₁ ⊔ H₂) := (AppC.mem_pCore_iff_mem_blockQ x).1 hx
    rw [hO, mem_bot] at hxO
    exact Subtype.ext hxO
  have hpc' : Open.pCore 2 ↥(H₁ ⊔ H₂) = ⊥ := by
    exact hpc
  have hb := card_inf_le_of_goldschmidtEdgeBoundS3 hedge ⟨htr, hpc'⟩
  have hT : Nat.card ↥(H₁.subgroupOf (H₁ ⊔ H₂) ⊓ H₂.subgroupOf (H₁ ⊔ H₂)) = Nat.card T := by
    have e : H₁.subgroupOf (H₁ ⊔ H₂) ⊓ H₂.subgroupOf (H₁ ⊔ H₂) =
        (H₁ ⊓ H₂).subgroupOf (H₁ ⊔ H₂) := by
      ext x
      simp only [mem_inf, mem_subgroupOf]
    rw [e, s1347_inf_eq S h]
    exact Nat.card_congr (subgroupOfEquivOfLe (h.inH₁.1.trans le_sup_left)).toEquiv
  have := s134_card_T_ge S
  omega

end CFSG.Quasithin.H13.U3
