module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpAut
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpOmegaMinusTwelveLin
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpTwelve
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpTwelveLin
import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO10CentOut
import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

private theorem exists_omegaMinus_model {K : Type} [Group K] (hZ : center K = ⊥)
    (h : StatedClassicalModel (K ⧸ center K) .POmegaMinus 6 2 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧ ∃ b c : F,
      (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ φ : K →* ((Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2 → F) ≃ₗ[F]
        (Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2 → F)), Function.Injective φ ∧
        φ.range = CFSG.RankThree.Classical2.orthDerived
          (CFSG.LieType.Universal.Spin.quadMinus 6 F b c) := by
  obtain ⟨-, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := h
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF])
  have hcoe := CFSG.LieType.Universal.Spin.coe_quadMinus 6 F b c
  have hv : ∃ v, (CFSG.LieType.Universal.Spin.quadMinus 6 F b c) v ≠ 0 := by
    refine ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, ?_⟩
    rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp
  have hS := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot hcoe hv
  let e₁ : StatedProj (StatedOmega (StatedQuadMinus 6 F b c)) ≃*
      StatedOmega (StatedQuadMinus 6 F b c) :=
    (QuotientGroup.quotientMulEquivOfEq hS).trans QuotientGroup.quotientBot
  let e₂ := CFSG.RankThree.PartOne.statedOmegaOrthEquiv hcoe
  let eK : K ≃* K ⧸ center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let ψ := eK.trans (e.trans (e₁.trans e₂))
  refine ⟨F, inferInstance, inferInstance, hF2, b, c, hirr,
    (Subgroup.subtype _).comp ψ.toMonoidHom, (Subgroup.subtype_injective _).comp ψ.injective, ?_⟩
  ext g
  constructor
  · rintro ⟨k, rfl⟩
    exact (ψ k).2
  · intro hg
    exact ⟨ψ.symm ⟨g, hg⟩, by simp⟩

private theorem inner_of_card_outer_dvd_two {L : Type*} [Group L] [Finite L]
    (hL : Nat.card (Outer L) ∣ 2) {ζ : MulAut L} (hζ : ζ ^ 3 = 1) {Q : Subgroup (MulAut L)}
    (hQ : Nat.card Q = 4) (hζQ : ζ ∈ normalizer (Q : Set (MulAut L)))
    (hfpf : ∀ q ∈ Q, ζ * q * ζ⁻¹ = q → q = 1) : ζ ∈ inner L ∧ Q ≤ inner L := by
  haveI : Finite (MulAut L) :=
    Finite.of_injective (fun e : MulAut L => (e : L → L)) fun a b h => MulEquiv.ext (congrFun h)
  set π := QuotientGroup.mk' (inner L)
  have hπ : ∀ g, π g = 1 ↔ g ∈ inner L := fun g => QuotientGroup.eq_one_iff g
  refine ⟨?_, ?_⟩
  · refine CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer ?_ (by decide) hζ
    rcases (Nat.dvd_prime Nat.prime_two).1 hL with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
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

private theorem mem_normalizer_comap_conj {L : Type} [Group L] {Q : Subgroup (MulAut L)} {g : L}
    (hg : MulAut.conj g ∈ normalizer (Q : Set (MulAut L))) :
    g ∈ normalizer ((Q.comap (MulAut.conj : L →* MulAut L) : Subgroup L) : Set L) := by
  rw [mem_normalizer_iff]
  intro p
  change MulAut.conj p ∈ Q ↔ MulAut.conj (g * p * g⁻¹) ∈ Q
  rw [map_mul, map_mul, map_inv]
  exact (mem_normalizer_iff.1 hg) _

theorem pumpUpOmegaMinusTwelveInput_holds :
    PumpUpOmegaMinusTwelveInput := by
  intro K _ _ W Wk ζ ξ Q A h hmodel
  classical
  have hc : StatedClassicalModel (K ⧸ center K) .POmegaMinus 6 2 1 := by
    obtain ⟨-, hc | ⟨h0, -⟩⟩ := hmodel
    · exact hc
    · omega
  have hZ : center K = ⊥ := center_eq_bot_of_twelve h.quasi (Or.inr (Or.inr hc))
  let eK : K ≃* K ⧸ center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hout : Nat.card (Outer K) ∣ 2 := by
    rw [Nat.card_congr (equivalence eK).toEquiv]
    exact CFSG.AGLEmbedding.O10Cent.card_outer_dvd_two (by norm_num) hc
  obtain ⟨⟨z, hz⟩, hQin⟩ :=
    inner_of_card_outer_dvd_two hout h.ζ_cube h.Q_card h.ζ_norm_Q h.ζ_fpf
  have hζ : ζ = MulAut.conj z := hz.symm
  have hconj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [← hZ, mem_center_iff]
    intro b
    have hb := congrArg (fun α : MulAut K => α b) ((MonoidHom.mem_ker).1 ha)
    simp only [MulAut.conj_apply, MulAut.one_apply] at hb
    calc b * a = a * b * a⁻¹ * a := by rw [hb]
      _ = a * b := by group
  set PQ : Subgroup K := Q.comap (MulAut.conj : K →* MulAut K) with hPQdef
  have hPQmap : PQ.map (MulAut.conj : K →* MulAut K) = Q := Subgroup.map_comap_eq_self hQin
  have hPQcard : Nat.card PQ = 4 := by
    rw [← h.Q_card, ← hPQmap, Subgroup.card_map_of_injective hconj]
  have hPQWk : ∀ p ∈ PQ, ∀ x ∈ Wk, p * x = x * p := fun p hp x hx => by
    have h1 := h.Q_fix _ hp x hx
    rw [MulAut.conj_apply] at h1
    calc p * x = p * x * p⁻¹ * p := by group
      _ = x * p := by rw [h1]
  have hzPQ : z ∈ normalizer (PQ : Set K) := mem_normalizer_comap_conj (hζ ▸ h.ζ_norm_Q)
  have hPQfpf : ∀ p ∈ PQ, z * p * z⁻¹ = p → p = 1 := fun p hp hzp => by
    have h1 := h.ζ_fpf (MulAut.conj p) hp (by rw [hζ, ← map_inv, ← map_mul, ← map_mul, hzp])
    exact hconj (h1.trans (map_one _).symm)
  obtain ⟨w, hwW, β, hβ, hξ⟩ := h.A_gen ξ h.ξ_mem
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hβ
  have hξ' : ξ = MulAut.conj (w * z ^ j) := by rw [hξ, hζ, ← map_zpow, ← map_mul]
  obtain ⟨F, _, _, hF, b, c, hirr, φ, hφ, hrange⟩ := exists_omegaMinus_model hZ hc
  set Q' := CFSG.LieType.Universal.Spin.quadMinus 6 F b c
  have hQnd : (QuadraticMap.polarBilin Q').Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 6 F hirr
  have hnplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q' :=
    CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by norm_num) hirr
  have hV : Module.finrank F (Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2 → F) = 12 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  obtain ⟨hz3, hz1, hWs, hWc, hWz, hcomp, -⟩ := pumpUpAut_map_config h hZ hζ φ hφ
  rw [hrange] at hcomp
  have hzΩ : φ z ∈ CFSG.RankThree.Classical2.orthDerived Q' := hrange ▸ ⟨z, rfl⟩
  have hrangeΩ : ∀ k : K, φ k ∈ CFSG.RankThree.Classical2.orthDerived Q' := fun k =>
    hrange ▸ ⟨k, rfl⟩
  haveI := hWs
  obtain ⟨h2, htr⟩ := twelve_orth_fixed_two hF hV hQnd hzΩ hz3 hz1 hWc hcomp
  have hWkcl : StatedClassicalModel Wk .PSU 4 2 1 := by
    obtain ⟨-, hc | ⟨h0, -⟩⟩ := h.Wk_model
    · exact hc
    · omega
  haveI : IsSimpleGroup Wk := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hWkcl
  have hWkc : Nat.card Wk = 25920 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two hWkcl
  let eWk : Wk ≃* Wk.map φ := Wk.equivMapOfInjective φ hφ
  haveI : IsSimpleGroup (Wk.map φ) := MulEquiv.isSimpleGroup eWk.symm
  have hWkc' : Nat.card (Wk.map φ) = 25920 := by rw [← Nat.card_congr eWk.toEquiv, hWkc]
  have hWkW : Wk.map φ ≤ W.map φ := Subgroup.map_mono h.Wk_le
  have hzW : ∀ x ∈ W, z * x = x * z := fun x hx => by
    have h1 : ζ x = x := mem_autFix.1 (h.W_comp.1 hx)
    rw [hζ, MulAut.conj_apply] at h1
    calc z * x = z * x * z⁻¹ * z := by group
      _ = x * z := by rw [h1]
  have hw1 : w ∉ Subgroup.zpowers z → φ w ∉ Subgroup.zpowers (φ z) := fun hw hmem => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact hw ⟨k, hφ (by rw [map_zpow, hk])⟩
  have hz3K : z ^ 3 = 1 := hφ (by rw [map_pow, hz3, map_one])
  have hWcl : StatedClassicalModel W .PSU 5 2 1 := by
    obtain ⟨-, hc | ⟨h0, -⟩⟩ := h.W_model
    · exact hc
    · omega
  haveI : IsSimpleGroup W := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hWcl
  have hWcK : Nat.card W = 13685760 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hWcl
  have hWZK : Subgroup.center W = ⊥ :=
    CFSG.EvenSporadicStandard.HypOne.center_eq_bot_of_isSimpleGroup (by rw [hWcK]; norm_num)
  have hcentg : ∀ p ∈ PQ, (w * z ^ j) * p = p * (w * z ^ j) := fun p hp => by
    have h1 := (mem_centralizer_iff.1 h.ξ_Q) _ hp
    rw [hξ', ← map_mul, ← map_mul] at h1
    exact (hconj h1).symm
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hc1 : (⟨w, hwW⟩ : W) ∈ Subgroup.center W := mem_center_iff.2 fun x => Subtype.ext (by
      show x.1 * w = w * x.1
      rw [← hk]
      exact ((Commute.zpow_left (hzW x.1 x.2) k).eq).symm)
    rw [hWZK, mem_bot] at hc1
    have hw1' : w = 1 := congrArg Subtype.val hc1
    have hcz : ∀ p ∈ PQ, z ^ j * p = p * z ^ j := fun p hp => by
      have := hcentg p hp
      rwa [hw1', one_mul] at this
    have hzj : z ^ j = z ^ (j % 3) := zpow_eq_zpow_emod j (by
      rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, hz3K])
    have hPQbot : ∀ p ∈ PQ, p = 1 := by
      rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h0 | h1 | h2'
      · exfalso
        have hξ1 : ξ = 1 := by rw [hξ', hw1', one_mul, hzj, h0, zpow_zero, map_one]
        have hnorm : ∀ g : K, g ∈ normalizer (PQ : Set K) := fun g =>
          mem_normalizer_comap_conj (h.ξ_norm g (by rw [hξ1]; rfl))
        haveI : PQ.Normal := ⟨fun p hp g => (mem_normalizer_iff.1 (hnorm g) p).1 hp⟩
        haveI : IsSimpleGroup (K ⧸ center K) := h.quasi.2
        haveI : IsSimpleGroup K := MulEquiv.isSimpleGroup eK
        rcases (inferInstance : PQ.Normal).eq_bot_or_eq_top with hb | ht
        · rw [hb, Subgroup.card_bot] at hPQcard
          norm_num at hPQcard
        · have hdvd := Subgroup.card_subgroup_dvd_card W
          rw [hWcK, ← Subgroup.card_top (G := K), ← ht, hPQcard] at hdvd
          norm_num at hdvd
      · intro p hp
        apply hPQfpf p hp
        have := hcz p hp
        rw [hzj, h1, zpow_one] at this
        rw [this, mul_inv_cancel_right]
      · intro p hp
        apply hPQfpf p hp
        have h3 : Commute (z ^ (2 : ℤ)) p := by
          have := hcz p hp
          rwa [hzj, h2'] at this
        have h4 : Commute ((z ^ (2 : ℤ)) ^ (2 : ℤ)) p := h3.zpow_left 2
        have hz4 : (z ^ (2 : ℤ)) ^ (2 : ℤ) = z := by
          rw [← zpow_mul, show (2 : ℤ) * 2 = 3 + 1 by norm_num, zpow_add, zpow_one,
            show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, hz3K, one_mul]
        rw [hz4] at h4
        rw [h4.eq, mul_inv_cancel_right]
    obtain ⟨⟨p₀, hp₀⟩, hp₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (fun hb : PQ = ⊥ => by
      rw [hb, Subgroup.card_bot] at hPQcard
      norm_num at hPQcard)
    exact hp₀1 (Subtype.ext (hPQbot p₀ hp₀))
  have hw3 : w ^ 3 = 1 := by
    have h1 : ξ ^ 3 = 1 := h.A_elem.2 ξ h.ξ_mem
    rw [hξ', ← map_pow] at h1
    have h2 : (w * z ^ j) ^ 3 = 1 := hconj (h1.trans (map_one _).symm)
    have hcw : Commute w (z ^ j) := (Commute.zpow_right (hzW w hwW).symm j)
    have hzj3 : (z ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3K, one_zpow]
    rw [hcw.mul_pow, hzj3, mul_one] at h2
    exact h2
  have hwWk : ∀ x ∈ Wk, w * x = x * w := fun x hx => by
    have h1 := h.ξ_fixWk x hx
    rw [hξ', MulAut.conj_apply] at h1
    have hzx : z ^ j * x = x * z ^ j := (Commute.zpow_left (hzW x (h.Wk_le hx)) j).eq
    have e : w * z ^ j * x * (w * z ^ j)⁻¹ = w * x * w⁻¹ := by
      rw [mul_assoc w, hzx]
      group
    rw [e] at h1
    calc w * x = w * x * w⁻¹ * w := by group
      _ = x * w := by rw [h1]
  have hmapΩ : ∀ {H : Subgroup K}, H.map φ ≤ CFSG.RankThree.Classical2.orthDerived Q' :=
    fun {H} => by
      rintro _ ⟨k, -, rfl⟩
      exact hrangeΩ k
  have hP'card : Nat.card (PQ.map φ) = 4 := by
    rw [Subgroup.card_map_of_injective hφ, hPQcard]
  refine false_of_twelve_omegaMinus_config hF hV hQnd hnplus hzΩ hz3 h2 (Wk := Wk.map φ)
    (P := PQ.map φ) hWkc' (fun x hx => hWz x (hWkW hx)) (fun x hx => htr x (hWkW hx)) hmapΩ
    hP'card
    (by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, hPQWk p hp x hx])
    (le_normalizer_map φ (mem_map_of_mem φ hzPQ))
    (by
      rintro _ ⟨p, hp, rfl⟩ hzp
      rw [← map_inv, ← map_mul, ← map_mul] at hzp
      rw [hPQfpf p hp (hφ (hzp.trans rfl)), map_one])
    (hrangeΩ w) (by rw [← map_pow, hw3, map_one]) (hWz _ (mem_map_of_mem φ hwW))
    (htr _ (mem_map_of_mem φ hwW)) (hw1 hwz)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, hwWk x hx])
    j
    (by
      rintro _ ⟨p, hp, rfl⟩
      rw [← map_zpow, ← map_mul, ← map_mul, ← map_mul, hcentg p hp])
    fun t htΩ htg => ?_
  obtain ⟨k, hk⟩ : t ∈ φ.range := hrange ▸ htΩ
  have hξk : ξ k = k := by
    rw [hξ', MulAut.conj_apply]
    apply hφ
    rw [map_mul, map_mul, map_inv, map_mul, map_zpow, hk]
    rw [← htg]
    group
  have hkN := mem_normalizer_comap_conj (h.ξ_norm k hξk)
  exact hk ▸ le_normalizer_map φ (mem_map_of_mem φ hkN)

end CFSG.GGQ2Prime
