module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpAut
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpUnitaryLin
import CFSG.Adapters.LieModelUnitaryOuter
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6Nine
import CFSG.HardMathSupport.Curtis.UnitaryLevi.NormalizerConj

public section

namespace CFSG.GGQ2Prime

open Subgroup Module CFSG.Open CFSG.Fischer CFSG.ComponentClassification.OuterAutomorphisms

private theorem le_inner_of_card_outer_dvd_six {L : Type*} [Group L] [Finite L]
    (hL : Nat.card (Outer L) ∣ 6) {ζ : MulAut L} {Q : Subgroup (MulAut L)}
    (hQ : Nat.card Q = 4) (hζQ : ζ ∈ normalizer (Q : Set (MulAut L)))
    (hfpf : ∀ q ∈ Q, ζ * q * ζ⁻¹ = q → q = 1) : Q ≤ inner L := by
  haveI : Finite (MulAut L) :=
    Finite.of_injective (fun e : MulAut L => (e : L → L)) fun a b h => MulEquiv.ext (congrFun h)
  set π := QuotientGroup.mk' (inner L)
  have hπ : ∀ g, π g = 1 ↔ g ∈ inner L := fun g => QuotientGroup.eq_one_iff g
  let πQ : Q →* Outer L := π.comp Q.subtype
  have hkr := Subgroup.card_ker_mul_card_range πQ
  have hmemker : ∀ q : Q, q ∈ πQ.ker ↔ (q : MulAut L) ∈ inner L := fun q => hπ q
  rw [hQ] at hkr
  have hrange : Nat.card πQ.range ∣ 2 := by
    have h6 : Nat.card πQ.range ∣ 6 := (card_subgroup_dvd_card _).trans hL
    have h4 : Nat.card πQ.range ∣ 4 := ⟨_, by rw [← hkr, mul_comm]⟩
    have := Nat.dvd_gcd h6 h4
    rwa [show Nat.gcd 6 4 = 2 by rfl] at this
  have hker : Nat.card πQ.ker = 4 ∨ Nat.card πQ.ker = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hrange with h | h <;> rw [h] at hkr <;> omega
  rcases hker with h4 | h2
  · have htop : πQ.ker = ⊤ := Subgroup.eq_top_of_card_eq _ (h4.trans hQ.symm)
    intro q hq
    exact (hmemker ⟨q, hq⟩).1 (htop ▸ mem_top _)
  · exfalso
    obtain ⟨x, hx1, hxu⟩ := (Nat.card_eq_two_iff' (1 : πQ.ker)).1 h2
    have hxinn : ((x : Q) : MulAut L) ∈ inner L := (hmemker x).1 x.2
    set q : MulAut L := ((x : Q) : MulAut L)
    have hqQ : q ∈ Q := (x : Q).2
    have hq1 : q ≠ 1 := fun h => hx1 (Subtype.ext (Subtype.ext h))
    have hq'Q : ζ * q * ζ⁻¹ ∈ Q := (mem_normalizer_iff.1 hζQ q).1 hqQ
    have hq'inn : ζ * q * ζ⁻¹ ∈ inner L := (inner_normal L).conj_mem q hxinn ζ
    let x' : πQ.ker := ⟨⟨ζ * q * ζ⁻¹, hq'Q⟩, (hmemker _).2 hq'inn⟩
    have hx'1 : x' ≠ 1 := fun h => hq1 (by
      have h' : ζ * q * ζ⁻¹ = 1 := congrArg (fun u : πQ.ker => ((u : Q) : MulAut L)) h
      calc q = ζ⁻¹ * (ζ * q * ζ⁻¹) * ζ := by group
        _ = 1 := by rw [h']; group)
    have hxx : x' = x := hxu x' hx'1
    have hfix : ζ * q * ζ⁻¹ = q := congrArg (fun u : πQ.ker => ((u : Q) : MulAut L)) hxx
    exact hq1 (hfpf q hqQ hfix)

private theorem mem_inner_of_card_outer_dvd_two {L : Type*} [Group L] [Finite L]
    (hL : Nat.card (Outer L) ∣ 2) {ζ : MulAut L} (hζ : ζ ^ 3 = 1) : ζ ∈ inner L := by
  haveI : Finite (MulAut L) :=
    Finite.of_injective (fun e : MulAut L => (e : L → L)) fun a b h => MulEquiv.ext (congrFun h)
  set π := QuotientGroup.mk' (inner L)
  have h3 : π ζ ^ 3 = 1 := by rw [← map_pow, hζ, map_one]
  have h2 : π ζ ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard (π ζ)).trans hL)
  have h1 : π ζ = 1 := by
    have : π ζ = π ζ ^ 3 * (π ζ ^ 2)⁻¹ := by group
    rw [this, h3, h2, inv_one, one_mul]
  exact (QuotientGroup.eq_one_iff ζ).1 h1

private theorem sq_eq_one_of_fpf {G : Type*} [Group G] {Q : Subgroup G} (hQ : Nat.card Q = 4)
    {ζ : G} (hζQ : ζ ∈ normalizer (Q : Set G)) (hfpf : ∀ q ∈ Q, ζ * q * ζ⁻¹ = q → q = 1) :
    ∀ q ∈ Q, q ^ 2 = 1 := by
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  intro q hq
  by_contra hq2
  have hdvd : orderOf q ∣ 4 := by
    rw [← Subgroup.orderOf_mk q hq, ← hQ]
    exact orderOf_dvd_natCard _
  have hpos : 0 < orderOf q := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hord : orderOf q = 4 := by
    have hle : orderOf q ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : orderOf q
    · exact absurd (by rw [orderOf_eq_one_iff.1 h, one_pow]) hq2
    · exact absurd (h ▸ pow_orderOf_eq_one q) hq2
    · norm_num at hdvd
    · rfl
  have hQz : zpowers q = Q := by
    apply Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 hq)
    rw [hQ, Nat.card_zpowers, hord]
  have hr : ζ * q * ζ⁻¹ ∈ zpowers q := hQz ▸ (mem_normalizer_iff.1 hζQ q).1 hq
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hr
  have hq4 : (q ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = orderOf q by rw [hord], pow_orderOf_eq_one]
  have hsq : ζ * q ^ 2 * ζ⁻¹ = (q ^ 2) ^ k := by
    have : ζ * q ^ 2 * ζ⁻¹ = (ζ * q * ζ⁻¹) ^ 2 := by rw [sq, sq]; group
    rw [this, ← hk, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
  have hk2 : (q ^ 2) ^ k = 1 ∨ (q ^ 2) ^ k = q ^ 2 := by
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, show ((q ^ 2) ^ (2 : ℤ)) = (q ^ 2) ^ 2 from zpow_natCast _ 2, hq4,
        one_zpow]
    · right
      rw [zpow_add, zpow_mul, show ((q ^ 2) ^ (2 : ℤ)) = (q ^ 2) ^ 2 from zpow_natCast _ 2, hq4,
        one_zpow, one_mul, zpow_one]
  rcases hk2 with h1 | h1
  · apply hq2
    have : ζ * q ^ 2 * ζ⁻¹ = 1 := hsq.trans h1
    calc q ^ 2 = ζ⁻¹ * (ζ * q ^ 2 * ζ⁻¹) * ζ := by group
      _ = 1 := by rw [this]; group
  · exact hq2 (hfpf (q ^ 2) (Q.pow_mem hq 2) (hsq.trans h1))

open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (hF4) in
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6 in
private theorem false_of_u6_config {L : Type} [Group L] (e : L ≃* S6) {ζ : MulAut L}
    (hζ3 : ζ ^ 3 = 1)
    (hζ1 : ζ ≠ 1) {W Wk : Subgroup L} [IsSimpleGroup W] [IsSimpleGroup Wk]
    (hWc : Nat.card W = 13685760) (hWkc : Nat.card Wk = 25920) (hWk : Wk ≤ W)
    (hζW : ∀ x ∈ W, ζ x = x) {w : L} (hwW : w ∈ W) (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1)
    (hwWk : ∀ x ∈ Wk, w * x = x * w) {P : Subgroup L} (hP : Nat.card P = 4)
    (hP2 : ∀ p ∈ P, p ^ 2 = 1) (hPWk : ∀ p ∈ P, ∀ x ∈ Wk, p * x = x * p) : False := by
  let β : MulAut S6 := (e.symm.trans ζ).trans e
  have hβ : ∀ s, β s = e (ζ (e.symm s)) := fun s => rfl
  have hz : ∀ x, ζ (ζ (ζ x)) = x := fun x => by
    have := congrArg (fun φ : MulAut L => φ x) hζ3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun s => ?_
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, hβ, hβ, hβ, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply, hz, MulEquiv.apply_symm_apply, MulAut.one_apply]
  obtain ⟨B, hB, hc3, hconj⟩ := exists_unitary_of_pow_three β hβ3
  have hBM : ∀ u ∈ StatedSU 6 (2 ^ 1) F4, B * u * B⁻¹ ∈ StatedSU 6 (2 ^ 1) F4 := fun u hu => by
    have := (conjM6 ⟨B, hB⟩ ⟨u, hu⟩).2
    rwa [conjM6_apply] at this
  refine false_of_psu_le_seven_pumpUp_config (n := 6) (by norm_num) e hζ1 (z := B)
    ((CFSG.HardMathSupport.Curtis.UnitaryLevi.mem_primeFormUnitary_one_iff_isometry hF4 B).1 hB)
    hc3 ?_ hBM ?_ hWc hWkc hWk hζW hwW hw1 hw3 hwWk hP hP2 hPWk
  · intro c hc1 hc J hJ hJp
    exact CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.u6NineFact_holds ⟨B, hB⟩ c hc1 hc J
      (fun u hu => mem_CenD.2 (hJ u hu)) hJp
  · intro u
    exact (hconj u _ rfl).symm

open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (hF4) in
private theorem false_of_u7_config {L : Type} [Group L]
    (e : L ≃* StatedProj (StatedSU 7 (2 ^ 1) F4))
    {x : L} (hx1 : MulAut.conj x ≠ 1) (hx3 : x ^ 3 = 1) {W Wk : Subgroup L} [IsSimpleGroup W]
    [IsSimpleGroup Wk] (hWc : Nat.card W = 13685760) (hWkc : Nat.card Wk = 25920) (hWk : Wk ≤ W)
    (hxW : ∀ y ∈ W, x * y * x⁻¹ = y) {w : L} (hwW : w ∈ W) (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1)
    (hwWk : ∀ y ∈ Wk, w * y = y * w) {P : Subgroup L} (hP : Nat.card P = 4)
    (hP2 : ∀ p ∈ P, p ^ 2 = 1) (hPWk : ∀ p ∈ P, ∀ y ∈ Wk, p * y = y * p) : False := by
  classical
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (e x)
  have hM : ∀ v ∈ StatedSU 7 (2 ^ 1) F4, (u : GL (Fin 7) F4) * v * (u : GL (Fin 7) F4)⁻¹ ∈
      StatedSU 7 (2 ^ 1) F4 := fun v hv =>
    (StatedSU 7 (2 ^ 1) F4).mul_mem ((StatedSU 7 (2 ^ 1) F4).mul_mem u.2 hv)
      ((StatedSU 7 (2 ^ 1) F4).inv_mem u.2)
  have hu3 : ((u ^ 3 : StatedSU 7 (2 ^ 1) F4) : GL (Fin 7) F4) ∈ StatedScalars (Fin 7) F4 := by
    have : (QuotientGroup.mk (u ^ 3) : StatedProj (StatedSU 7 (2 ^ 1) F4)) = 1 := by
      rw [QuotientGroup.mk_pow, hu, ← map_pow, hx3, map_one]
    rwa [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
  refine false_of_psu_le_seven_pumpUp_config (n := 7) (by norm_num) e (ζ := MulAut.conj x) hx1
    (z := (u : GL (Fin 7) F4))
    (((CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff_isometry hF4).1 u.2).2) ?_ ?_ hM ?_
    hWc hWkc hWk (fun y hy => by rw [MulAut.conj_apply]; exact hxW y hy) hwW hw1 hw3 hwWk hP hP2
    hPWk
  · obtain ⟨c, hc⟩ := hu3
    exact ⟨c, by rw [hc, Subgroup.coe_pow]⟩
  · intro c hc1 hc
    exfalso
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin 7) c ∈ StatedSU 7 (2 ^ 1) F4 := by
      rw [← hc, ← Subgroup.coe_pow]
      exact (u ^ 3).2
    have hdet := ((CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff hF4).1 hmem).1
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    have hc3 : c ^ 3 = 1 := by
      have h := pow_card_eq_one (G := F4ˣ) (x := c)
      rwa [Fintype.card_units, F4.card] at h
    apply hc1
    apply Units.ext
    have : (c : F4) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
    rw [Units.val_one]
    linear_combination hdet - (c : F4) * ((c : F4) ^ 3 + 1) * this
  · intro v
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hu]
    show (QuotientGroup.mk (u * v * u⁻¹) : StatedProj (StatedSU 7 (2 ^ 1) F4)) = _
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem pumpUpUnitarySmallInput_holds : PumpUpUnitarySmallInput := by
  intro K _ _ W Wk ζ ξ Q A h hmodel
  classical
  haveI : Group.IsPerfect K := Group.isPerfect_def.2 h.quasi.1
  haveI : IsSimpleGroup (K ⧸ center K) := h.quasi.2
  let π : K →* K ⧸ center K := QuotientGroup.mk' (center K)
  have hWcl : StatedClassicalModel W .PSU 5 2 1 := by
    obtain ⟨-, hc | ⟨h0, -⟩⟩ := h.W_model
    · exact hc
    · omega
  have hWkcl : StatedClassicalModel Wk .PSU 4 2 1 := by
    obtain ⟨-, hc | ⟨h0, -⟩⟩ := h.Wk_model
    · exact hc
    · omega
  haveI : IsSimpleGroup W := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hWcl
  haveI : IsSimpleGroup Wk := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hWkcl
  have hWc : Nat.card W = 13685760 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hWcl
  have hWkc : Nat.card Wk = 25920 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two hWkcl
  have hnp : ∀ {n : ℕ}, 3 ∣ n → n ≠ 3 → ¬ n.Prime := fun {n} h3 hn3 hp => by
    rcases hp.eq_one_or_self_of_dvd 3 h3 with h | h
    · norm_num at h
    · exact hn3 h.symm
  have hone : ∀ {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y], ¬ (Nat.card Y).Prime →
      ∀ a : Y, (∀ b, a * b = b * a) → a = 1 := fun hY a ha => by
    have ha' : a ∈ center _ := mem_center_iff.2 fun b => (ha b).symm
    rwa [CFSG.EvenSporadicStandard.HypOne.center_eq_bot_of_isSimpleGroup hY, mem_bot] at ha'
  have hinjS : ∀ (S : Subgroup K) [IsSimpleGroup S], ¬ (Nat.card S).Prime →
      Function.Injective (π.comp S.subtype) := fun S _ hS => by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    exact mem_bot.2 (hone hS s fun b =>
      Subtype.ext ((mem_center_iff.1 hs b).symm))
  have hπW := hinjS W (hnp (by rw [hWc]; norm_num) (by rw [hWc]; norm_num))
  have hπWk := hinjS Wk (hnp (by rw [hWkc]; norm_num) (by rw [hWkc]; norm_num))
  let cq := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K
  have hcq : Function.Injective cq :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  have hcq_apply : ∀ (α : MulAut K) (g : K), cq α (π g) = π (α g) := fun α g =>
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk α g
  have hKbar : ¬ (Nat.card (K ⧸ center K)).Prime := by
    intro hp
    have hdvd : Nat.card W ∣ Nat.card (K ⧸ center K) := by
      rw [Nat.card_congr (MonoidHom.ofInjective hπW).toEquiv]
      exact card_subgroup_dvd_card _
    rw [hWc] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · norm_num at h1
    · rw [← h1] at hp
      exact hnp (by norm_num) (by norm_num) hp
  have hconj : Function.Injective (MulAut.conj : K ⧸ center K →* MulAut (K ⧸ center K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    refine mem_bot.2 (hone hKbar a fun b => ?_)
    have hb := congrArg (fun φ : MulAut (K ⧸ center K) => φ b) ((MonoidHom.mem_ker).1 ha)
    simp only [MulAut.conj_apply, MulAut.one_apply] at hb
    calc a * b = a * b * a⁻¹ * a := by group
      _ = b * a := by rw [hb]
  have hcl : StatedClassicalModel (K ⧸ center K) .PSU 6 2 1 ∨
      StatedClassicalModel (K ⧸ center K) .PSU 7 2 1 := by
    rcases hmodel with ⟨-, hc | ⟨h0, -⟩⟩ | ⟨-, hc | ⟨h0, -⟩⟩
    · exact Or.inl hc
    · omega
    · exact Or.inr hc
    · omega
  have hout6 : StatedClassicalModel (K ⧸ center K) .PSU 6 2 1 →
      Nat.card (Outer (K ⧸ center K)) = 6 := fun hc => by
    rw [CFSG.Blueprint.LieModel.card_outer_psu (Or.inl ⟨by decide, hc⟩) (by norm_num)
      (by norm_num)]
    rfl
  have hout7 : StatedClassicalModel (K ⧸ center K) .PSU 7 2 1 →
      Nat.card (Outer (K ⧸ center K)) = 2 := fun hc => by
    rw [CFSG.Blueprint.LieModel.card_outer_psu (Or.inl ⟨by decide, hc⟩) (by norm_num)
      (by norm_num)]
    rfl
  have hout : Nat.card (Outer (K ⧸ center K)) ∣ 6 := by
    rcases hcl with hc | hc
    · rw [hout6 hc]
    · rw [hout7 hc]; norm_num
  have hQ4 : Nat.card (Q.map cq) = 4 := by rw [card_map_of_injective hcq, h.Q_card]
  have hQin := le_inner_of_card_outer_dvd_six hout (ζ := cq ζ) hQ4
    (le_normalizer_map cq (mem_map_of_mem cq h.ζ_norm_Q))
    (by
      rintro _ ⟨q, hq, rfl⟩ hfix
      rw [← map_inv, ← map_mul, ← map_mul] at hfix
      rw [h.ζ_fpf q hq (hcq hfix), map_one])
  have hQ2 : ∀ q ∈ Q, q ^ 2 = 1 := sq_eq_one_of_fpf h.Q_card h.ζ_norm_Q h.ζ_fpf
  let P : Subgroup (K ⧸ center K) := (Q.map cq).comap MulAut.conj
  have hPmap : P.map MulAut.conj = Q.map cq := by
    refine le_antisymm (map_comap_le _ _) fun y hy => ?_
    obtain ⟨x, hx⟩ := hQin hy
    exact ⟨x, by show MulAut.conj x ∈ Q.map cq; rw [hx]; exact hy, hx⟩
  have hP4 : Nat.card P = 4 := by rw [← card_map_of_injective hconj, hPmap, hQ4]
  have hP2 : ∀ p ∈ P, p ^ 2 = 1 := fun p hp => by
    obtain ⟨q, hq, hqp⟩ := hp
    apply hconj
    rw [map_pow, ← hqp, ← map_pow, hQ2 q hq, map_one, map_one]
  let Wb : Subgroup (K ⧸ center K) := (π.comp W.subtype).range
  let Wkb : Subgroup (K ⧸ center K) := (π.comp Wk.subtype).range
  haveI : IsSimpleGroup Wb := (MonoidHom.ofInjective hπW).symm.isSimpleGroup
  haveI : IsSimpleGroup Wkb := (MonoidHom.ofInjective hπWk).symm.isSimpleGroup
  have hWbc : Nat.card Wb = 13685760 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hπW).toEquiv, hWc]
  have hWkbc : Nat.card Wkb = 25920 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hπWk).toEquiv, hWkc]
  have hWkb : Wkb ≤ Wb := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x, h.Wk_le x.2⟩, rfl⟩
  have hWfix : ∀ y ∈ W, ζ y = y := fun y hy => mem_autFix.1 (h.W_comp.1 hy)
  have hζW : ∀ x ∈ Wb, cq ζ x = x := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hcq_apply, hWfix y y.2]
  have hPWk : ∀ p ∈ P, ∀ x ∈ Wkb, p * x = x * p := by
    rintro p ⟨q, hq, hqp⟩ _ ⟨y, rfl⟩
    have e : MulAut.conj p (π y) = π y := by
      rw [← hqp, hcq_apply, h.Q_fix q hq y y.2]
    rw [MulAut.conj_apply] at e
    calc p * (π.comp Wk.subtype) y = p * π y * p⁻¹ * p := by
          rw [MonoidHom.comp_apply, Subgroup.coe_subtype]
          group
      _ = (π.comp Wk.subtype) y * p := by rw [e]; rfl
  obtain ⟨w, hwW, β', hβ', hξ⟩ := h.A_gen ξ h.ξ_mem
  have hβ'A : β' ∈ A := (Subgroup.zpowers_le.2 h.ζ_mem) hβ'
  have hcw : MulAut.conj w = ξ * β'⁻¹ := by rw [hξ]; group
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.A_elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.A_elem.2
  have hcw3 : MulAut.conj w ^ 3 = 1 := by
    rw [hcw, (Commute.mul_pow (hAc ξ h.ξ_mem _ (A.inv_mem hβ'A)) 3), hA3 ξ h.ξ_mem,
      hA3 _ (A.inv_mem hβ'A), one_mul]
  have hcwWk : ∀ y ∈ Wk, w * y * w⁻¹ = y := fun y hy => by
    have h1 : MulAut.conj w y = y := by
      rw [hcw, MulAut.mul_apply]
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hβ'
      have hk : (ζ ^ k)⁻¹ y = y := by
        have hmem : ζ ∈ MulAction.stabilizer (MulAut K) y := by
          rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
          exact hWfix y (h.Wk_le hy)
        have := Subgroup.zpow_mem _ hmem (-k)
        rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def, zpow_neg] at this
      rw [hk, h.ξ_fixWk y hy]
    rwa [MulAut.conj_apply] at h1
  have hcw1 : MulAut.conj w ≠ 1 := by
    intro h1
    have hξβ : ξ = β' := by rw [← mul_inv_eq_one, ← hcw, h1]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hβ'
    have hζord : orderOf ζ = 3 := orderOf_eq_prime h.ζ_cube h.ζ_ne
    have hξk : ξ = ζ ^ (k % 3) := by
      rw [hξβ, ← hk, ← zpow_mod_orderOf, hζord]
      rfl
    have hξQ : ∀ q ∈ Q, q * ξ = ξ * q := fun q hq => Subgroup.mem_centralizer_iff.1 h.ξ_Q q hq
    have hζQ : ¬ ∀ q ∈ Q, q * ζ = ζ * q := fun hc => by
      have hbot : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).2 fun q hq =>
        h.ζ_fpf q hq (by rw [← hc q hq]; group)
      have := h.Q_card
      rw [hbot, card_bot] at this
      norm_num at this
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h1' | h2'
    ·
      have hξ1 : ξ = 1 := by rw [hξk, h0, zpow_zero]
      have hnorm : ∀ g : K, MulAut.conj g ∈ normalizer (Q : Set (MulAut K)) := fun g =>
        h.ξ_norm g (by rw [hξ1]; rfl)
      have hcqconj : ∀ g : K, cq (MulAut.conj g) = MulAut.conj (π g) := fun g =>
        MulEquiv.ext fun x => by
          obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
          rw [hcq_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
      have hPn : P.Normal := ⟨fun p hp x => by
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
        show MulAut.conj (π g * p * (π g)⁻¹) ∈ Q.map cq
        rw [map_mul, map_mul, map_inv, ← hcqconj]
        exact (mem_normalizer_iff.1 (le_normalizer_map cq (mem_map_of_mem cq (hnorm g))) _).1 hp⟩
      rcases hPn.eq_bot_or_eq_top with hb | ht
      · rw [hb, card_bot] at hP4
        norm_num at hP4
      · rw [ht, card_top] at hP4
        have hdvd : Nat.card W ∣ Nat.card (K ⧸ center K) := by
          rw [Nat.card_congr (MonoidHom.ofInjective hπW).toEquiv]
          exact card_subgroup_dvd_card _
        rw [hWc, hP4] at hdvd
        norm_num at hdvd
    ·
      apply hζQ
      intro q hq
      have := hξQ q hq
      rwa [hξk, h1', zpow_one] at this
    ·
      apply hζQ
      intro q hq
      have h2 := hξQ q hq
      rw [hξk, h2', show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast] at h2
      have hζ4 : ζ = ζ ^ 2 * ζ ^ 2 := by
        rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, h.ζ_cube, one_mul]
      rw [hζ4, ← mul_assoc, h2, mul_assoc, h2, mul_assoc]
  have hπw1 : π w ≠ 1 := fun h1 => hcw1 (by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact MulEquiv.ext fun g => by
      rw [MulAut.conj_apply, MulAut.one_apply, (mem_center_iff.1 h1 g).symm]
      group)
  have hπw3 : π w ^ 3 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut K => φ g) hcw3
    simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at this
    calc g * w ^ 3 = w ^ 3 * g * (w ^ 3)⁻¹ * w ^ 3 := by rw [this]
      _ = w ^ 3 * g := by group
  have hπwW : π w ∈ Wb := ⟨⟨w, hwW⟩, rfl⟩
  have hπwWk : ∀ x ∈ Wkb, π w * x = x * π w := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← map_mul, ← map_mul]
    congr 1
    calc w * y = w * y * w⁻¹ * w := by group
      _ = y * w := by rw [hcwWk y y.2]
  have hζ3 : cq ζ ^ 3 = 1 := by rw [← map_pow, h.ζ_cube, map_one]
  have hζ1 : cq ζ ≠ 1 := fun h1 => h.ζ_ne (hcq (h1.trans (map_one cq).symm))
  rcases hcl with h6 | h7
  · obtain ⟨-, K₀, _, _, hK₀, ⟨e₀⟩⟩ := h6
    haveI : Fintype K₀ := Fintype.ofFinite K₀
    have hc : Fintype.card K₀ = Fintype.card F4 := by
      rw [← Nat.card_eq_fintype_card, hK₀, F4.card]
      norm_num
    exact false_of_u6_config (e₀.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 6 (2 ^ 1))) hζ3 hζ1 hWbc hWkbc hWkb hζW hπwW hπw1 hπw3
      hπwWk hP4 hP2 hPWk
  · have h7' := h7
    obtain ⟨-, K₀, _, _, hK₀, ⟨e₀⟩⟩ := h7
    haveI : Fintype K₀ := Fintype.ofFinite K₀
    have hc : Fintype.card K₀ = Fintype.card F4 := by
      rw [← Nat.card_eq_fintype_card, hK₀, F4.card]
      norm_num
    obtain ⟨x, hx⟩ := mem_inner_of_card_outer_dvd_two (by rw [hout7 h7']) hζ3
    have hx3 : x ^ 3 = 1 := hconj (by rw [map_pow, hx, hζ3, map_one])
    refine false_of_u7_config (e₀.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 7 (2 ^ 1))) (x := x) (by rw [hx]; exact hζ1) hx3
      hWbc hWkbc hWkb (fun y hy => ?_) hπwW hπw1 hπw3 hπwWk hP4 hP2 hPWk
    have := hζW y hy
    rw [← hx, MulAut.conj_apply] at this
    exact this

end CFSG.GGQ2Prime
