module

public import CFSG.Quasithin.H13.NQCoreA6EOne
public import CFSG.Quasithin.Background.E1Sec7Two

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open scoped commutatorElement

theorem commutator_mul_mul_of_commute {X : Type*} [Group X] {a b c d : X}
    (hcb : Commute c b) (had : Commute a d) (hbd : Commute b d) :
    ⁅a * b, c * d⁆ = ⁅a, c⁆ := by
  have h1 : b * (c * d) * b⁻¹ = c * d := by
    rw [mul_inv_eq_iff_eq_mul]
    exact ((hcb.symm.mul_right hbd)).eq
  have h2 : d * a⁻¹ = a⁻¹ * d := had.inv_left.eq.symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  calc a * b * (c * d) * (b⁻¹ * a⁻¹) * (d⁻¹ * c⁻¹)
      = a * (b * (c * d) * b⁻¹) * a⁻¹ * d⁻¹ * c⁻¹ := by group
    _ = a * c * (d * a⁻¹) * d⁻¹ * c⁻¹ := by rw [h1]; group
    _ = a * c * a⁻¹ * c⁻¹ := by rw [h2]; group

theorem le_of_perfect_of_central {Q : Type*} [Group Q] {M J Y R : Subgroup Q} [J.Normal]
    [Y.Normal] [R.Normal] (hY : ⁅Y, Y⁆ = Y) (hRM : R ≤ M) (hJ : J ≤ R ⊔ (Y ⊓ J))
    (hc : ∀ c ∈ Y ⊓ J, ∀ y ∈ Y, ⁅c, y⁆ ∈ R) (hMJ : M ⊔ J = ⊤) : Y ≤ M := by
  have hC : (Y ⊓ J).Normal := Subgroup.normal_inf_normal Y J
  have hdec : ∀ y ∈ Y, ∃ m ∈ Y ⊓ M, ∃ c ∈ Y ⊓ J, m * c = y := by
    intro y hy
    have h1 : y ∈ M ⊔ (Y ⊓ J) := by
      have h2 : y ∈ M ⊔ J := hMJ ▸ mem_top y
      have h3 : M ⊔ J ≤ M ⊔ (Y ⊓ J) :=
        sup_le le_sup_left (hJ.trans (sup_le (hRM.trans le_sup_left) le_sup_right))
      exact h3 h2
    obtain ⟨m, hm, c, hc', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp h1
    have hmY : m ∈ Y := by
      have := Y.mul_mem hy (Y.inv_mem (mem_inf.mp hc').1)
      rwa [mul_inv_cancel_right] at this
    exact ⟨m, mem_inf.mpr ⟨hmY, hm⟩, c, hc', rfl⟩
  set ρ := QuotientGroup.mk' R with hρ
  have hcomm : ∀ c ∈ Y ⊓ J, ∀ y ∈ Y, Commute (ρ y) (ρ c) := by
    intro c hc' y hy
    have h1 : ρ ⁅c, y⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hc c hc' y hy)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h1
    exact h1.symm
  rw [← hY, Subgroup.commutator_le]
  intro y₁ hy₁ y₂ hy₂
  obtain ⟨m₁, hm₁, c₁, hc₁, rfl⟩ := hdec y₁ hy₁
  obtain ⟨m₂, hm₂, c₂, hc₂, rfl⟩ := hdec y₂ hy₂
  have hm₁Y := (mem_inf.mp hm₁).1
  have hm₂Y := (mem_inf.mp hm₂).1
  have hc₂Y := (mem_inf.mp hc₂).1
  have h1 : ρ ⁅m₁ * c₁, m₂ * c₂⁆ = ρ ⁅m₁, m₂⁆ := by
    rw [map_commutatorElement, map_commutatorElement, map_mul, map_mul]
    exact commutator_mul_mul_of_commute (hcomm c₁ hc₁ m₂ hm₂Y) (hcomm c₂ hc₂ m₁ hm₁Y)
      (hcomm c₁ hc₁ c₂ hc₂Y).symm
  have h2 : ⁅m₁, m₂⁆⁻¹ * ⁅m₁ * c₁, m₂ * c₂⁆ ∈ R := by
    rw [← QuotientGroup.eq_one_iff]
    show ρ (⁅m₁, m₂⁆⁻¹ * ⁅m₁ * c₁, m₂ * c₂⁆) = 1
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h3 : ⁅m₁, m₂⁆ ∈ M := by
    rw [commutatorElement_def]
    have hm₁M := (mem_inf.mp hm₁).2
    have hm₂M := (mem_inf.mp hm₂).2
    exact M.mul_mem (M.mul_mem (M.mul_mem hm₁M hm₂M) (M.inv_mem hm₁M)) (M.inv_mem hm₂M)
  have h4 := M.mul_mem h3 (hRM h2)
  rwa [mul_inv_cancel_left] at h4

theorem isE_one_of_typeOne {B : Type*} [Group B] [Finite B]
    (hO2 : pCoreOf 2 (⊤ : Subgroup B) = ⊥) {T A K : Subgroup B} (h : E1TypeOne ⊤ T A K) :
    IsE 1 ⊤ T A K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAK := h.A_le
  have hamb : EOneAmb K A := by
    obtain ⟨P, p, hp, hOP, hPK, hPn, hPcard, ⟨b, hb⟩, hPeq⟩ := h.core
    have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
    have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
    have hOn : ((pCoreOf 2 K).subgroupOf P).Normal :=
      (normal_subgroupOf_iff_le_normalizer hOP).mpr
        (hPK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
    have hOpos : 0 < Nat.card (pCoreOf 2 K) := Nat.card_pos
    have hPpos : 0 < Nat.card P := Nat.card_pos
    have hidxO : ((pCoreOf 2 K).subgroupOf P).index = p := by
      have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 K) P
      rw [inf_of_le_left hOP, hPcard] at h1
      have h2 : (pCoreOf 2 K).relIndex P = p :=
        Nat.eq_of_mul_eq_mul_right hOpos (by rw [h1, mul_comm])
      exact h2
    have hidxP : (P.subgroupOf K).index = 2 ^ b := by
      have h1 := Subgroup.relIndex_mul_card P K
      rw [inf_of_le_left hPK, hb] at h1
      have h2 : P.relIndex K = 2 ^ b :=
        Nat.eq_of_mul_eq_mul_right hPpos (by rw [h1, mul_comm])
      exact h2
    refine ⟨p, hpp, hp2, P, hPK, (normal_subgroupOf_iff_le_normalizer hPK).mp hPn, hOP,
      fun x hx => ⟨1, ?_⟩, fun s hs => ⟨b, ?_⟩, fun heq => ?_,
      (hPeq.trans (sup_comm _ _)).le, ?_⟩
    · have h1 := Subgroup.pow_index_mem ((pCoreOf 2 K).subgroupOf P) ⟨x, hx⟩
      rw [hidxO, mem_subgroupOf, Subgroup.coe_pow] at h1
      rwa [pow_one]
    · have h1 := Subgroup.pow_index_mem (P.subgroupOf K) ⟨s, hs⟩
      rw [hidxP, mem_subgroupOf, Subgroup.coe_pow] at h1
      exact h1
    · rw [heq] at hPcard
      have : p = 1 := by
        have h1 : Nat.card (pCoreOf 2 K) * 1 = Nat.card (pCoreOf 2 K) * p := by
          rw [mul_one]
          exact hPcard
        exact (Nat.eq_of_mul_eq_mul_left hOpos h1).symm
      exact hpp.one_lt.ne' this
    · have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 K) A
      rw [h.index_two, inf_comm] at h1
      have hApos : 0 < Nat.card (A ⊓ pCoreOf 2 K : Subgroup B) := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hApos h1
  have hEOne : EOne ↥K (A.subgroupOf K) := (eOne_iff_amb hAK).mpr hamb
  refine ⟨le_top, fun t ht => ?_, h.sylow, Or.inl ⟨hEOne, ?_⟩⟩
  · rw [mem_tauOf] at ht
    obtain ⟨htT, -, hta⟩ := ht
    refine mem_inf.mpr ⟨htT, h.centralizer_le (mem_inf.mpr ⟨htT, ?_⟩)⟩
    rw [mem_centralizer_iff]
    intro a ha
    have h1 := hta a ha
    rw [hO2, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  · obtain ⟨-, -, -, -, -, -, hcard⟩ := hEOne
    rw [hcard]
    norm_num

theorem inEFor_one_of_alt6_quotient {Q : Type} [Group Q]
    [Finite Q] {J Y T : Subgroup Q} [J.Normal] [Y.Normal] (hT : IsSylowIn 2 T ⊤)
    (hJ : J ≤ CFSG.Open.pCore 2 Q ⊔ (Y ⊓ J))
    (hc : ∀ c ∈ Y ⊓ J, ∀ y ∈ Y, ⁅c, y⁆ ∈ CFSG.Open.pCore 2 Q) (hY : ⁅Y, Y⁆ = Y)
    (he : Nonempty (↥(Y.map (QuotientGroup.mk' J)) ≃* alternatingGroup (Fin 6)))
    (hC : centralizer ((Y.map (QuotientGroup.mk' J) : Subgroup (Q ⧸ J)) : Set (Q ⧸ J)) = ⊥)
    (hO2 : pCoreOf 2 (⊤ : Subgroup (Q ⧸ J)) = ⊥) : InEFor 1 ⊤ T := by
  intro Ω hΩ
  set π := QuotientGroup.mk' J with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J
  set W := weakClosure T Ω with hW
  set M := eGen 1 ⊤ T Ω ⊔ ((⊤ : Subgroup Q) ⊓ normalizer (W : Set Q)) with hM
  have hTM : T ≤ M := (le_normalizer_weakClosure hΩ).trans fun x hx =>
    mem_sup_right (mem_inf.mpr ⟨mem_top x, hx⟩)
  have hRM : CFSG.Open.pCore 2 Q ≤ M := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← pCoreOf_top_eq]
    exact (pCoreOf_le_of_isSylowIn hT).trans hTM
  have hYn : (Y.map π).Normal := Subgroup.Normal.map ‹_› π hπs
  obtain ⟨F, hF, hgen⟩ := stmtA6AutEOneWitnessesAll (Q ⧸ J) (Y.map π) he hC (T.map π)
    (isSylowIn_two_map_top hπs hT) (Subgroup.map π '' Ω) (isInvColl_map_of_surjective π hπs hΩ)
  have hTMb : T.map π ≤ M.map π := map_mono hTM
  have hMtop : M.map π = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sup_le (iSup₂_le fun AK hAK => ?_) ?_
    · obtain ⟨hAΩ, hAT, hTO⟩ := hF AK hAK
      obtain ⟨A₀, hA₀, hA₀eq⟩ := hAΩ
      obtain ⟨n, hnJ, hn⟩ := exists_mem_conj_le_of_map_le hT
        (isPGroup_of_isElemAbelian (hΩ.isElemAbelian A₀ hA₀)) (hA₀eq ▸ hAT)
      have hA : conjSub n A₀ ∈ Ω := hΩ.conj A₀ hA₀ n (mem_top n)
      have hAT' : conjSub n A₀ ≤ T := by
        rintro _ ⟨a, ha, rfl⟩
        exact hn a ha
      have hπn : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hnJ
      have hAmap : (conjSub n A₀).map π = AK.1 := by
        rw [← hA₀eq]
        unfold conjSub
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, hπn]
      have hIsE : IsE 1 ⊤ (T.map π) ((conjSub n A₀).map π) AK.2 := by
        rw [hAmap]
        exact isE_one_of_typeOne hO2 hTO
      obtain ⟨K, hK, hres⟩ := ten_seven hT hAT' (hΩ.isElemAbelian _ hA) hIsE
      have h1 : twoResidual AK.2 ≤ M.map π := by
        rw [hres]
        exact map_mono ((twoResidual_le K).trans ((le_eGen hA hAT' hK).trans le_sup_left))
      exact (le_twoResidual_sup_of_isSylowIn hTO.sylow).trans
        (sup_le h1 (inf_le_left.trans hTMb))
    · rw [weakClosure_map_quotient hT hΩ]
      intro b hb
      obtain ⟨g, rfl⟩ := hπs b
      obtain ⟨g', hg', hgg'⟩ := exists_mem_normalizer_of_mem_normalizer_map hT hΩ hb
      exact ⟨g', mem_sup_right (mem_inf.mpr ⟨mem_top g', hg'⟩), hgg'⟩
  have hMJ : M ⊔ J = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : π x ∈ M.map π := hMtop ▸ mem_top (π x)
    obtain ⟨m, hm, hmx⟩ := hx
    have h1 : m⁻¹ * x ∈ J := by
      have h2 : π (m⁻¹ * x) = 1 := by rw [map_mul, map_inv, hmx, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h2
    have h3 : x = m * (m⁻¹ * x) := by group
    rw [h3]
    exact mul_mem_sup hm h1
  have hYM : Y ≤ M := le_of_perfect_of_central hY hRM hJ hc hMJ
  have hJM : J ≤ M := hJ.trans (sup_le hRM (inf_le_left.trans hYM))
  exact eq_top_iff.mpr (hMJ ▸ sup_le le_rfl hJM)

end CFSG.Quasithin.H13.NQCore
