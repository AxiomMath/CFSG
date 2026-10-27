module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Frame
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Concl
public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.Walter.AStar.Subnormal
import CFSG.LieType.BorelTits.Basic
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.ASVolI.ChIJK (IsGraphFieldAut F4 graphFieldPSL3 graphFieldSL3)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL scalars)
open scoped MatrixGroups

section Models

noncomputable abbrev pslEquiv : PSL(3, F4) ≃* projectiveSL 3 F4 :=
  CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F4

theorem pslEquiv_graphField (y : PSL(3, F4)) :
    pslEquiv (graphFieldPSL3 y) =
      CFSG.RankThree.PartTwo.KFacts.L34.betaAut (frobeniusEquiv F4 2) (pslEquiv y) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : graphFieldSL3 g =
      Matrix.SpecialLinearGroup.map (frobeniusEquiv F4 2).toRingHom (g⁻¹).transpose := by
    change CFSG.ASVolI.ChIJK.invTransposeSL (Fin 3) F4 (CFSG.ASVolI.ChIJK.fieldSL3 g) = _
    rw [← CFSG.ASVolI.ChIJK.fieldSL3_invTranspose]
    rfl
  have h2 : graphFieldPSL3 (QuotientGroup.mk g) = QuotientGroup.mk (graphFieldSL3 g) :=
    QuotientGroup.congr_mk _ _ _ _ g
  rw [h2, h1]
  change (QuotientGroup.mk _ : projectiveSL 3 F4) =
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 F4 (frobeniusEquiv F4 2)
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut 3 F4
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F4 g))
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut_proj,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut_proj]
  rfl

end Models

namespace Hyp36

open Odd

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem odd_card_center_of_normal (h : Hyp36 G M p E) (L : Subgroup G) [L.Normal] :
    Odd (Nat.card (Subgroup.center ↥L)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ a ∈ centerOf L, ∀ b ∈ centerOf L, a * b = b * a := fun a ha b hb =>
    ((mem_centerOf.1 ha).2 b (mem_centerOf.1 hb).1).symm
  let T : Subgroup G :=
    { carrier := {z | z ∈ centerOf L ∧ z * z = 1}
      one_mem' := ⟨(centerOf L).one_mem, mul_one 1⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨(centerOf L).mul_mem ha hb, ?_⟩
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hcomm b hb a ha]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
        rw [Set.mem_setOf_eq, hai]
        exact ⟨ha, ha2⟩ }
  have hT2 : IsPGroup 2 T := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
    exact x.2.2)⟩
  have hTn : T.Normal := ⟨fun z hz g => ⟨conj_mem_centerOf L hz.1 g, by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.2, mul_one, mul_inv_cancel]⟩⟩
  have hTn' : (T.subgroupOf ⊤).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top, Subgroup.normalizer_eq_top_iff.2 hTn]
  have hle : T ≤ pCoreOf 2 (⊤ : Subgroup G) := CFSG.LieType.BorelTits.le_pCoreOf 2 le_top hTn' hT2
  rw [h.pCoreOf_top_eq_bot] at hle
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥L)) 2 h2
  have hxT : (((x : ↥L) : G)) ∈ T := by
    refine ⟨(mem_center_iff_mem_centerOf L (x : ↥L)).1 x.2, ?_⟩
    have hx2 : x ^ 2 = 1 := by rw [← hx, pow_orderOf_eq_one]
    have := congrArg (fun y : ↥(Subgroup.center ↥L) => ((y : ↥L) : G)) hx2
    simpa [sq] using this
  have hx1 : x = 1 := Subtype.ext (Subtype.ext (Subgroup.mem_bot.1 (hle hxT)))
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem exists_sylow_normalizes (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    {K : Type} [Group K] (φ : ↥L ⧸ Subgroup.center ↥L ≃* K) :
    ∃ S : Sylow p K, ∀ g ∈ (S : Subgroup K), MulAut.conj g ∈
      normalizer (((pCoreOf 2 M).map (psi L φ) : Subgroup (MulAut K)) : Set (MulAut K)) := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow h.isPGroup
  have hPM : (P : Subgroup G) ≤ M := h.le_of_isPGroup P.isPGroup' hEP
  obtain ⟨R, hRP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hL.2
  let S : Sylow p K :=
    (R.mapSurjective (f := QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)).mapSurjective
      (f := φ.toMonoidHom) φ.surjective
  have hSeq : (S : Subgroup K) =
      ((R : Subgroup ↥L).map (QuotientGroup.mk' (Subgroup.center ↥L))).map φ.toMonoidHom := rfl
  refine ⟨S, fun g hg => ?_⟩
  rw [hSeq] at hg
  obtain ⟨c, ⟨r, hr, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hg
  have hrP : (r : G) ∈ (P : Subgroup G) := by
    have : (r : G) ∈ (P : Subgroup G) ⊓ L := by
      rw [← hRP]
      exact Subgroup.mem_map_of_mem L.subtype hr
    exact this.1
  have hconj : MulAut.conj (φ.toMonoidHom (QuotientGroup.mk' (Subgroup.center ↥L) r)) = psi L φ (r : G) :=
    (psi_eq_conj L φ r.2).symm
  rw [hconj]
  exact Subgroup.le_normalizer_map (psi L φ)
    (Subgroup.mem_map_of_mem (psi L φ) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hPM hrP)))

theorem concl_of_projectiveSL
    (h : Hyp36 G M p E) (hp : p = 3) {L : Subgroup G} [L.Normal]
    (hL : CFSG.IsComponent L) (hLM : L ⊔ M = ⊤) (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥)
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 F4) : K36Concl M p := by
  classical
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : Nat.card F4 = 4 := CFSG.RankThree.PartTwo.KFacts.L34.card_galoisField_two_two
  have hσ : ∀ a : F4, frobeniusEquiv F4 2 a = a ^ 2 := fun a => frobeniusEquiv_apply F4 2 a
  have hLc : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  set β := CFSG.RankThree.PartTwo.KFacts.L34.betaAut (frobeniusEquiv F4 2) with hβ
  set Ψ := psi L φ with hΨ
  set X : Subgroup (MulAut (projectiveSL 3 F4)) := (pCoreOf 2 M).map Ψ with hX
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := by
    rw [pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  have hX2 : IsPGroup 2 X := hQ2.map Ψ
  have hX3 : ¬ 3 ∣ Nat.card X := by
    obtain ⟨n, hn⟩ := hX2.exists_card_eq
    rw [hn]
    intro h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  obtain ⟨S, hSX⟩ := h.exists_sylow_normalizes hL φ
  have hS9 : Nat.card (S : Subgroup (projectiveSL 3 F4)) = 9 := by
    rw [S.card_eq_multiplicity, CFSG.RankThree.PartTwo.KFacts.L34.factorization_card hk]
    norm_num
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.L34.exists_eq_map_conj_eZero hk hS9
  set τ := MulAut.conj g * β * (MulAut.conj g)⁻¹ with hτ
  have hXτ : ∀ x ∈ X, x = 1 ∨ x = τ := by
    intro x hx
    have hfixS : ∀ e ∈ (S : Subgroup (projectiveSL 3 F4)), x e = e := fun e he =>
      CFSG.RankThree.PartTwo.KFacts.L34.forall_apply_eq_of_invariant hk hS9 hX3 hSX hx he
    set x' := (MulAut.conj g)⁻¹ * x * MulAut.conj g with hx'
    have hfix' : ∀ e ∈ CFSG.RankThree.PartTwo.KFacts.L34.eZero F4, x' e = e := by
      intro e he
      have hmem : g * e * g⁻¹ ∈ (S : Subgroup (projectiveSL 3 F4)) := by
        rw [hg]
        exact ⟨e, he, rfl⟩
      have h1 := hfixS _ hmem
      rw [hx', MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, h1, MulAut.conj_inv_apply]
      group
    have h3 : ¬ 3 ∣ orderOf x' := by
      have hord : orderOf x' = orderOf x := by
        have : x' = MulAut.conj (MulAut.conj g)⁻¹ x := by
          rw [hx', MulAut.conj_apply, inv_inv]
        rw [this]
        exact orderOf_injective (MulAut.conj (MulAut.conj g)⁻¹).toMonoidHom
          (MulAut.conj (MulAut.conj g)⁻¹).injective x
      rw [hord]
      exact fun h3 => hX3 (h3.trans (by rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _))
    rcases CFSG.RankThree.PartTwo.KFacts.L34.eq_one_or_eq_betaAut hk hσ hfix' h3 with h1 | h1
    · left
      calc x = MulAut.conj g * x' * (MulAut.conj g)⁻¹ := by rw [hx']; group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    · right
      calc x = MulAut.conj g * x' * (MulAut.conj g)⁻¹ := by rw [hx']; group
        _ = τ := by rw [h1]
  obtain ⟨t, htQ, htΨ⟩ : ∃ t ∈ pCoreOf 2 M, Ψ t ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hcomm : ∀ y ∈ L, q * y * q⁻¹ * y⁻¹ ∈ centerOf L := by
      intro y hy
      rw [← psi_mk_eq_iff L φ q y hy, ← hΨ, hall q hq]
      rfl
    exact centralizes_of_forall_comm_mem L hLc hcomm y hy
  have htτ : Ψ t = τ := (hXτ _ (Subgroup.mem_map_of_mem Ψ htQ)).resolve_left htΨ
  have hββ : β * β = 1 := CFSG.RankThree.PartTwo.KFacts.L34.betaAut_mul_self hk hσ
  have hττ : τ * τ = 1 := by
    calc τ * τ = MulAut.conj g * (β * β) * (MulAut.conj g)⁻¹ := by rw [hτ]; group
      _ = 1 := by rw [hββ, mul_one, mul_inv_cancel]
  have hinj : ∀ q ∈ pCoreOf 2 M, Ψ q = 1 → q = 1 := fun q hq hq1 =>
    h.eq_one_of_psi_eq_one hLc hLM φ hq hq1
  have htt : t * t = 1 := hinj _ ((pCoreOf 2 M).mul_mem htQ htQ) (by rw [map_mul, htτ, hττ])
  have ht1 : t ≠ 1 := fun h1 => htΨ (by rw [h1, map_one])
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact htt) ht1
  have hQt : pCoreOf 2 M = zpowers t := by
    apply le_antisymm
    · intro q hq
      rcases hXτ _ (Subgroup.mem_map_of_mem Ψ hq) with hq1 | hqτ
      · rw [hinj q hq hq1]
        exact one_mem _
      · have hqt : q * t⁻¹ = 1 := hinj _ ((pCoreOf 2 M).mul_mem hq ((pCoreOf 2 M).inv_mem htQ))
          (by rw [map_mul, map_inv, hqτ, htτ, mul_inv_cancel])
        rw [mul_inv_eq_one.1 hqt]
        exact mem_zpowers t
    · exact (zpowers_le).2 htQ
  have htN : t ∈ normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
    exact Subgroup.mem_top t
  have hgf : IsGraphFieldAut (UC6.conjOn L htN) := by
    set a := pslEquiv.symm g with ha
    refine ⟨φ.trans pslEquiv.symm, a * (graphFieldPSL3 a)⁻¹, fun k => ?_⟩
    have hk1 : (QuotientGroup.mk (UC6.conjOn L htN k) : ↥L ⧸ Subgroup.center ↥L) =
        actHom L t (QuotientGroup.mk k) := by
      rw [actHom_apply_mk]
      congr 1
    have hk2 : φ (actHom L t (QuotientGroup.mk k)) = τ (φ (QuotientGroup.mk k)) := by
      rw [← htτ, hΨ]
      exact (psi_apply_mk L φ t k k.2).symm
    set z := pslEquiv.symm (φ (QuotientGroup.mk k)) with hz
    have hy : φ (QuotientGroup.mk k) = pslEquiv z := by rw [hz, MulEquiv.apply_symm_apply]
    have hga : g = pslEquiv a := by rw [ha, MulEquiv.apply_symm_apply]
    have hτy : τ (pslEquiv z) = pslEquiv (a * graphFieldPSL3 (a⁻¹ * z * a) * a⁻¹) := by
      rw [hτ, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply, hga, ← map_inv,
        ← map_mul, ← map_mul, ← pslEquiv_graphField, ← map_mul, ← map_mul]
    change pslEquiv.symm (φ (QuotientGroup.mk (UC6.conjOn L htN k))) =
      a * (graphFieldPSL3 a)⁻¹ * graphFieldPSL3 z * (a * (graphFieldPSL3 a)⁻¹)⁻¹
    rw [hk1, hk2, hy, hτy, MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv]
    group
  have hodd := h.odd_card_center_of_normal L
  haveI : Group.IsPerfect ↥L := hL.1.1
  obtain ⟨Φ, hΦs, -, hΦZ⟩ := CFSG.QuasithinUnique.Ch1.exists_cover_map_of_odd_splitting
    (H := SL(3, F4)) (D := scalars 3 F4) hodd φ (fun E _ _ π hπ hcen hoddk => by
      obtain ⟨s, hs, -⟩ :=
        CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting (by norm_num) hπ hcen hoddk
      exact ⟨s, hs⟩)
  have hD : Nat.card (scalars 3 F4) ∣ 3 := by
    have := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_scalars_dvd (K := F4) (n := 3) (by norm_num)
    rwa [hk] at this
  have hZ3 : Nat.card (Subgroup.center ↥L) ∣ 3 := by
    rw [← hΦZ]
    exact (Subgroup.card_map_dvd _ Φ).trans hD
  have hshape : Nonempty (↥L ≃* PSL(3, F4)) ∨ Nonempty (↥L ≃* SL(3, F4)) := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hZ3 with h1 | h3
    · left
      have hZ : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      exact ⟨QuotientGroup.quotientBot.symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans (φ.trans pslEquiv.symm))⟩
    · right
      obtain ⟨-, hbij⟩ := CFSG.QuasithinUnique.Ch1.bijective_of_scalar_cover φ h3 hD hΦs
      exact ⟨(MulEquiv.ofBijective Φ hbij).symm⟩
  exact ⟨rfl, t, hto, hQt, L, inferInstance, hLM, Or.inl (Or.inl ⟨hshape, htN, hgf⟩)⟩

theorem concl_of_l34
    (h : Hyp36 G M p E) (hp : p = 3) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L) (hLM : L ⊔ M = ⊤)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q)
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) : K36Concl M p := by
  obtain ⟨⟨q₀, n₀, hq₀, hn₀⟩, hq2, hq1, hd⟩ := hd
  simp only at hq2 hq1
  subst hq2 hq1
  obtain ⟨x, hv⟩ := d
  simp only at hd
  subst hd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.concl_of_projectiveSL hp hL hLM hne
    (φ.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 _ hv).trans pslEquiv))

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
