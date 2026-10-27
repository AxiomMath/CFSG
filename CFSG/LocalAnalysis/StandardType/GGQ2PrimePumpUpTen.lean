module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpAut
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpTenLin
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClEl
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO10CentOut
import CFSG.RankThree.Classical.SteinbergR3EHigherSymplecticOuterOrder
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Open.StatedZModTwo
import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentModel

public section

namespace CFSG.GGQ2Prime

open Subgroup Module CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks (fixedByEnd mem_fixedByEnd)

private theorem false_of_ten_rep {X : Type*} [Group X] {F V : Type*} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] (hF : Nat.card F = 2) (hV : finrank F V = 10)
    (ι : X →* (V ≃ₗ[F] V)) (hι : Function.Injective ι) {z y : X} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hy : y ^ 11 = 1) (hy1 : y ≠ 1) (hzy : z * y = y * z) {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hY : 3 ^ 4 ∣ Nat.card Y) (β : Y →* X) (hβ : Function.Injective β)
    (hzβ : ∀ u, z * β u = β u * z) {P : Subgroup X} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥)
    (hPz : z ∈ normalizer (P : Set X)) (hPβ : ∀ p ∈ P, ∀ u, p * β u = β u * p) : False := by
  have hfixB := CFSG.LocalAnalysis.GLTheoremA.S265.BSCl.fixedByEnd_eq_bot_of_commute_eleven hF hV
    (d := ι z) (y := ι y) (fun h => hz1 (hι (h.trans (map_one ι).symm)))
    (by rw [← map_pow, hy, map_one]) (fun h => hy1 (hι (h.trans (map_one ι).symm)))
    (by rw [← map_mul, ← map_mul, hzy])
  have hfix : ∀ v, ι z v = v → v = 0 := fun v hv => by
    have hv' : v ∈ fixedByEnd (ι z) := mem_fixedByEnd.2 hv
    rw [hfixB] at hv'
    exact (Submodule.mem_bot F).1 hv'
  have hbot := eq_bot_of_commute_simple_finrank_ten hF hV hY (ι.comp β) (hι.comp hβ)
    (by rw [← map_pow, hz3, map_one]) hfix
    (fun u => by rw [MonoidHom.comp_apply, ← map_mul, ← map_mul, hzβ])
    (P := P.map ι) (hP.map ι) (le_normalizer_map ι (mem_map_of_mem ι hPz))
    (by
      rintro _ ⟨p, hp, rfl⟩ u
      rw [MonoidHom.comp_apply, ← map_mul, ← map_mul, hPβ p hp u])
  apply hP1
  rw [eq_bot_iff]
  intro p hp
  have hp' : ι p ∈ P.map ι := mem_map_of_mem ι hp
  rw [hbot] at hp'
  exact mem_bot.2 (hι ((mem_bot.1 hp').trans (map_one ι).symm))

private theorem inner_of_card_outer_dvd_two {L : Type*} [Group L] [Finite L]
    (hL : Nat.card (Outer L) ∣ 2) {ζ : MulAut L} (hζ : ζ ^ 3 = 1) {Q : Subgroup (MulAut L)}
    (hQ : Nat.card Q = 4) (hζQ : ζ ∈ normalizer (Q : Set (MulAut L)))
    (hfpf : ∀ q ∈ Q, ζ * q * ζ⁻¹ = q → q = 1) : ζ ∈ inner L ∧ Q ≤ inner L := by
  haveI : Finite (MulAut L) :=
    Finite.of_injective (fun e : MulAut L => (e : L → L)) fun a b h => MulEquiv.ext (congrFun h)
  set π := QuotientGroup.mk' (inner L)
  have hπ : ∀ g, π g = 1 ↔ g ∈ inner L := fun g => QuotientGroup.eq_one_iff g
  refine ⟨?_, ?_⟩
  · have h3 : π ζ ^ 3 = 1 := by rw [← map_pow, hζ, map_one]
    have h2 : π ζ ^ 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard (π ζ)).trans hL)
    have h1 : π ζ = 1 := by
      have : π ζ = π ζ ^ 3 * (π ζ ^ 2)⁻¹ := by group
      rw [this, h3, h2, inv_one, one_mul]
    exact (hπ ζ).1 h1
  · let πQ : Q →* Outer L := π.comp Q.subtype
    have hkr := Subgroup.card_ker_mul_card_range πQ
    have hrange : Nat.card πQ.range ∣ 2 := (card_subgroup_dvd_card _).trans hL
    have hmemker : ∀ q : Q, q ∈ πQ.ker ↔ (q : MulAut L) ∈ inner L := fun q => hπ q
    rw [hQ] at hkr
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

private theorem card_outer_dvd_two_of_ten {L : Type} [Group L]
    (h : StatedClassicalModel L .PSp 5 2 1 ∨ StatedClassicalModel L .POmegaMinus 5 2 1) :
    Nat.card (Outer L) ∣ 2 := by
  rcases h with h | h
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have h1 :=
      (CFSG.RankThree.Classical.higher_symplectic_outer_order_divides_field_multiplier_bound
        Nat.prime_two le_rfl (by norm_num : 3 ≤ 5) hK).1
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact ((by simpa using h1 : _ ∣ 1)).trans (one_dvd 2)
  · exact CFSG.AGLEmbedding.O10Cent.card_outer_dvd_two (by norm_num) h

private theorem exists_injective_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (hK : Nat.card K = 2) (H : Subgroup (GL ι K)) :
    ∃ ρ : StatedProj H →* ((ι → K) ≃ₗ[K] (ι → K)), Function.Injective ρ := by
  have hS : (StatedScalars ι K).subgroupOf H = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK, Subgroup.bot_subgroupOf]
  let e₁ : StatedProj H ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hS).trans QuotientGroup.quotientBot
  let e₂ : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))
  exact ⟨e₂.toMonoidHom.comp (H.subtype.comp e₁.toMonoidHom),
    e₂.injective.comp (H.subtype_injective.comp e₁.injective)⟩

private theorem exists_injective_rep_of_ten {L : Type} [Group L]
    (h : StatedClassicalModel L .PSp 5 2 1 ∨ StatedClassicalModel L .POmegaMinus 5 2 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (V : Type) (_ : AddCommGroup V) (_ : Module F V)
      (ι : L →* (V ≃ₗ[F] V)), Nat.card F = 2 ∧ finrank F V = 10 ∧ Function.Injective ι := by
  rcases h with h | h
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    obtain ⟨ρ, hρ⟩ := exists_injective_statedProj hK2 (StatedSp 5 K)
    refine ⟨K, inferInstance, inferInstance, _, inferInstance, inferInstance,
      ρ.comp e.toMonoidHom, hK2, ?_, hρ.comp e.injective⟩
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  · obtain ⟨-, K, _, _, hK, b, c, -, ⟨e⟩⟩ := h
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    obtain ⟨ρ, hρ⟩ := exists_injective_statedProj hK2 (StatedOmega (StatedQuadMinus 5 K b c))
    refine ⟨K, inferInstance, inferInstance, _, inferInstance, inferInstance,
      ρ.comp e.toMonoidHom, hK2, ?_, hρ.comp e.injective⟩
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]

theorem pumpUpTenInput_holds : PumpUpTenInput := by
  intro K _ _ W Wk ζ ξ Q A h hmodel
  classical
  haveI : Group.IsPerfect K := Group.isPerfect_def.2 h.quasi.1
  haveI : IsSimpleGroup (K ⧸ center K) := h.quasi.2
  let π : K →* K ⧸ center K := QuotientGroup.mk' (center K)
  have hcl : StatedClassicalModel (K ⧸ center K) .PSp 5 2 1 ∨
      StatedClassicalModel (K ⧸ center K) .POmegaMinus 5 2 1 := by
    rcases hmodel with ⟨-, hc | ⟨h0, -⟩⟩ | ⟨-, hc | ⟨h0, -⟩⟩
    · exact Or.inl hc
    · omega
    · exact Or.inr hc
    · omega
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
  have hone : ∀ {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y], ¬ (Nat.card Y).Prime →
      ∀ a : Y, (∀ b, a * b = b * a) → a = 1 := fun hY a ha => by
    have ha' : a ∈ center _ := mem_center_iff.2 fun b => (ha b).symm
    rwa [CFSG.EvenSporadicStandard.HypOne.center_eq_bot_of_isSimpleGroup hY, mem_bot] at ha'
  have hnp : ∀ {n : ℕ}, 3 ∣ n → n ≠ 3 → ¬ n.Prime := fun {n} h3 hn3 hp => by
    rcases hp.eq_one_or_self_of_dvd 3 h3 with h | h
    · norm_num at h
    · exact hn3 h.symm
  have hinjS : ∀ (S : Subgroup K) [IsSimpleGroup S], ¬ (Nat.card S).Prime →
      Function.Injective (π.comp S.subtype) := fun S _ hS => by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    exact mem_bot.2 (hone hS s fun b => Subtype.ext ((mem_center_iff.1 hs b).symm))
  have hπW := hinjS W (hnp (by rw [hWc]; norm_num) (by rw [hWc]; norm_num))
  have hπWk := hinjS Wk (hnp (by rw [hWkc]; norm_num) (by rw [hWkc]; norm_num))
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := W) 11 (by rw [hWc]; norm_num)
  let cq := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K
  have hcq : Function.Injective cq :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  have hcq_apply : ∀ (α : MulAut K) (g : K), cq α (π g) = π (α g) := fun α g =>
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk α g
  have hQ4 : Nat.card (Q.map cq) = 4 := by rw [card_map_of_injective hcq, h.Q_card]
  obtain ⟨hζin, hQin⟩ := inner_of_card_outer_dvd_two (card_outer_dvd_two_of_ten hcl)
    (ζ := cq ζ) (by rw [← map_pow, h.ζ_cube, map_one]) (Q := Q.map cq) hQ4
    (le_normalizer_map cq (mem_map_of_mem cq h.ζ_norm_Q))
    (by
      rintro _ ⟨q, hq, rfl⟩ hfix
      rw [← map_inv, ← map_mul, ← map_mul] at hfix
      rw [h.ζ_fpf q hq (hcq hfix), map_one])
  obtain ⟨zb, hzb⟩ := hζin
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
  have hfixz : ∀ g : K, ζ g = g → zb * π g = π g * zb := fun g hg => by
    have e : MulAut.conj zb (π g) = π g := by rw [hzb, hcq_apply, hg]
    rw [MulAut.conj_apply] at e
    calc zb * π g = zb * π g * zb⁻¹ * zb := by group
      _ = π g * zb := by rw [e]
  have hWfix : ∀ w ∈ W, ζ w = w := fun w hw => mem_autFix.1 (h.W_comp.1 hw)
  let P : Subgroup (K ⧸ center K) := (Q.map cq).comap MulAut.conj
  obtain ⟨F, _, _, V, _, _, ι, hF, hV, hι⟩ := exists_injective_rep_of_ten hcl
  refine false_of_ten_rep hF hV ι hι (z := zb) (y := π y) ?_ ?_ ?_ ?_ ?_ (Y := Wk)
    (by rw [hWkc]; norm_num) (π.comp Wk.subtype) hπWk ?_ (P := P) ?_ ?_ ?_ ?_
  · apply hconj
    rw [map_pow, hzb, ← map_pow, h.ζ_cube, map_one, map_one]
  · intro h1
    apply h.ζ_ne
    apply hcq
    rw [← hzb, h1, map_one, map_one]
  · rw [← map_pow, ← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one, map_one]
  · intro h1
    have hy1 : y = 1 := hπW (h1.trans (map_one _).symm)
    rw [hy1, orderOf_one] at hy
    norm_num at hy
  · exact hfixz y (hWfix y y.2)
  · intro u
    exact hfixz u (hWfix u (h.Wk_le u.2))
  · intro x
    obtain ⟨k, hk⟩ := (h.Q_two.map cq) ⟨MulAut.conj (x : K ⧸ center K), x.2⟩
    refine ⟨k, Subtype.ext (hconj ?_)⟩
    have hk' := congrArg Subtype.val hk
    simpa [map_pow] using hk'
  · obtain ⟨⟨q, hqQ⟩, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (fun hbot : Q.map cq = ⊥ => by
      rw [hbot, card_bot] at hQ4
      norm_num at hQ4)
    obtain ⟨x, hx⟩ := hQin hqQ
    rw [Ne, eq_bot_iff]
    intro hle
    have hxP : x ∈ P := by
      change MulAut.conj x ∈ Q.map cq
      rw [hx]
      exact hqQ
    have hx1 : x = 1 := mem_bot.1 (hle hxP)
    apply hq1
    apply Subtype.ext
    change q = 1
    rw [← hx, hx1, map_one]
  · rw [mem_normalizer_iff]
    intro x
    change MulAut.conj x ∈ Q.map cq ↔ MulAut.conj (zb * x * zb⁻¹) ∈ Q.map cq
    rw [map_mul, map_mul, map_inv, hzb]
    exact mem_normalizer_iff.1 (le_normalizer_map cq (mem_map_of_mem cq h.ζ_norm_Q)) _
  · intro x hx u
    obtain ⟨q, hq, hqx⟩ := hx
    have e : MulAut.conj x (π u) = π u := by
      rw [← hqx, hcq_apply, h.Q_fix q hq u u.2]
    rw [MulAut.conj_apply] at e
    calc x * (π.comp Wk.subtype) u = x * π u * x⁻¹ * x := by
          rw [MonoidHom.comp_apply, Subgroup.coe_subtype]
          group
      _ = (π.comp Wk.subtype) u * x := by rw [e]; rfl

end CFSG.GGQ2Prime
