module

public import CFSG.Quasithin.Vol2.Ch11SecO11C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.J4U

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem isL24Sub_subgroupOf {S B C : Subgroup G} (hB : IsL24Sub S B) (hBC : B ≤ C) :
    IsL24Sub (S.subgroupOf C) (B.subgroupOf C) := by
  obtain ⟨hB1, hBp, hSB, F, _, _, hF, ⟨e⟩⟩ := hB
  let f : ↥(B.subgroupOf C) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBC
  refine ⟨?_, ?_, ?_, F, inferInstance, inferInstance, hF,
    ⟨(QuotientGroup.congr _ _ f (CFSG.pCore_map_iso 2 f)).trans e⟩⟩
  · intro h
    apply hB1
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hBC hx⟩ : ↥C) ∈ B.subgroupOf C := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  · apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hBC, hBp]
  · intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hSB (Subgroup.mem_subgroupOf.mp hs)) b

theorem comap_pCore_quotient (p : ℕ) {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (hNp : IsPGroup p N) :
    (CFSG.pCore p (H ⧸ N)).comap (QuotientGroup.mk' N) = CFSG.pCore p H := by
  apply le_antisymm
  · rw [show CFSG.pCore p H = sSup {K : Subgroup H | K.Normal ∧ IsPGroup p K} from rfl]
    refine le_sSup ⟨(CFSG.pCore_normal (G := H ⧸ N) (p := p)).comap (QuotientGroup.mk' N), ?_⟩
    refine (CFSG.pCore_isPGroup (G := H ⧸ N) (p := p)).comap_of_ker_isPGroup _ ?_
    rwa [QuotientGroup.ker_mk']
  · rw [← Subgroup.map_le_iff_le_comap,
      show CFSG.pCore p (H ⧸ N) = sSup {K : Subgroup (H ⧸ N) | K.Normal ∧ IsPGroup p K} from rfl]
    exact le_sSup ⟨(CFSG.pCore_normal (G := H) (p := p)).map _ (QuotientGroup.mk'_surjective N),
      (CFSG.pCore_isPGroup (G := H) (p := p)).map _⟩

theorem isL24Sub_map_of_isPGroup [Finite G] {G' : Type} [Group G'] {S B : Subgroup G}
    (hB : IsL24Sub S B) (π : G →* G') (hk : IsPGroup 2 ↥(π.ker.subgroupOf B)) :
    IsL24Sub (S.map π) (B.map π) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hB1, hBp, hSB, F, _, _, hF, ⟨e⟩⟩ := hB
  set ρ : ↥B →* G' := π.comp B.subtype with hρ
  set N := π.ker.subgroupOf B with hN
  have hρk : ρ.ker = N := by
    rw [hρ, hN, ← MonoidHom.comap_ker]
    rfl
  have : N.Normal := hρk ▸ ρ.normal_ker
  have hρr : ρ.range = B.map π := by rw [hρ, MonoidHom.range_comp, Subgroup.range_subtype]
  let f1 : ↥B ⧸ N ≃* ↥(B.map π) :=
    (QuotientGroup.quotientMulEquivOfEq hρk.symm).trans
      ((QuotientGroup.quotientKerEquivRange ρ).trans (MulEquiv.subgroupCongr hρr))
  have : (CFSG.pCore 2 ↥B).Normal := CFSG.pCore_normal
  have hNO : N ≤ CFSG.pCore 2 ↥B := by
    rw [show CFSG.pCore 2 ↥B = sSup {K : Subgroup ↥B | K.Normal ∧ IsPGroup 2 K} from rfl]
    exact le_sSup ⟨inferInstance, hk⟩
  have hcore : CFSG.pCore 2 (↥B ⧸ N) = (CFSG.pCore 2 ↥B).map (QuotientGroup.mk' N) := by
    rw [← comap_pCore_quotient 2 N hk,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)]
  let f2 : (↥B ⧸ N) ⧸ CFSG.pCore 2 (↥B ⧸ N) ≃* ↥B ⧸ CFSG.pCore 2 ↥B :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans
      (QuotientGroup.quotientQuotientEquivQuotient N (CFSG.pCore 2 ↥B) hNO)
  have hc60 : Nat.card ((↥B ⧸ N) ⧸ CFSG.pCore 2 (↥B ⧸ N)) = 60 := by
    rw [Nat.card_congr (f2.trans e).toEquiv, O11.card_sl2_four hF]
  refine ⟨fun h => ?_, by rw [← Subgroup.map_commutator, hBp],
    (Subgroup.map_mono hSB).trans (Subgroup.le_normalizer_map π), F, inferInstance,
    inferInstance, hF,
    ⟨(QuotientGroup.congr _ _ f1.symm (CFSG.pCore_map_iso 2 f1.symm)).trans (f2.trans e)⟩⟩
  have h1 : Nat.card (↥B ⧸ N) = 1 := by
    rw [Nat.card_congr f1.toEquiv, h, Subgroup.card_bot]
  have h2 : Nat.card ((↥B ⧸ N) ⧸ CFSG.pCore 2 (↥B ⧸ N)) ∣ Nat.card (↥B ⧸ N) :=
    Subgroup.card_quotient_dvd_card _
  rw [hc60, h1] at h2
  norm_num at h2

theorem le_of_perfect_of_index_two {X : Type} [Group X] {D B : Subgroup X} (hD : D.index = 2)
    (hB : ⁅B, B⁆ = B) : B ≤ D := by
  have hDn : D.Normal := Subgroup.normal_of_index_eq_two hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (X ⧸ D) := isCyclic_of_prime_card (p := 2) hD
  have hcomm : ∀ a b : X ⧸ D, a * b = b * a := by
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    intro a b
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    exact (Commute.zpow_zpow_self g m n).eq
  rw [← hB, Subgroup.commutator_le]
  intro x _ y _
  rw [← QuotientGroup.eq_one_iff (N := D), commutatorElement_def, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
    hcomm (x : X ⧸ D) (y : X ⧸ D), mul_assoc, mul_assoc, mul_inv_cancel_left,
    mul_inv_cancel]

end CFSG.Quasithin.Vol2.Ch11.SecS.J4U
