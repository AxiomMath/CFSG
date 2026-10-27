module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Datum
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UG3
import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeDiag
import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartAutomizer
import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextRankAux
import CFSG.LocalAnalysis.StandardType.GGTwE6TorusMeetGamma
import CFSG.LocalAnalysis.StandardType.GGLangCoroot
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.QTwoCav
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest

section General

private theorem twIn_zmodPowHom_pow_three {M : Type*} [Group M] {ζ : M} (hζ : ζ ^ 3 = 1)
    (z : Multiplicative (ZMod 3)) : (CFSG.RankThree.CentralCover.zmodPowHom ζ hζ z) ^ 3 = 1 := by
  rw [← map_pow]
  have hz : z ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul,
      show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]
  rw [hz, map_one]

private theorem twIn_zetaVec_pow_three {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (x : Fin Tag.E6.rank → ZMod 3) (i : Fin Tag.E6.rank) :
    zetaVec ζ hζ x i ^ 3 = 1 := by
  rw [zetaVec_apply, ← pow_mul, Nat.mul_comm, pow_mul, hζ, one_pow]

private theorem twIn_rootChar_neg {τ : Tag} {L : Type} [Field L]
    (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]


private theorem twIn_corootPair_single_single (j l : Fin Tag.E6.rank) :
    corootPair (Pi.single j 1 : Fin Tag.E6.rank → ℤ) (Pi.single l 1) =
      Tag.E6.cartan j l := by
  have h := corootPair_smul_single (τ := Tag.E6) (1 : WeylGroup Tag.E6) j (Pi.single l 1)
  simpa [Pi.single_apply] using h

private theorem twIn_fullThreeTorus_subset_top {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) : fullThreeTorus S ≤ zetaTorus ζ hζ ⊤ := by
  intro t ht
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (τ := Tag.E6) (K := L)
    ((inf_le_left : S.D.torus ≤ torusGroup Tag.E6 L) ht.1)
  have hb3 : b ^ 3 = 1 := by
    apply rootDiagUnit_injective
    rw [← rootDiagUnit_pow, rootDiagUnit_one, ← hb, ht.2]
  obtain ⟨x, hx⟩ := exists_zetaVec_eq (τ := Tag.E6) (p := 3) hζo hζ hb3
  rw [mem_zetaTorus]
  exact ⟨x, trivial, by rw [hx]; exact hb.symm⟩

end General


private theorem twIn_zetaTorus_subset_top {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) (hS : NegLangTwo S) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) :
    zetaTorus ζ hζ ⊤ ≤ fullThreeTorus S := by
  intro t ht
  rw [mem_zetaTorus] at ht
  obtain ⟨x, -, rfl⟩ := ht
  rw [mem_fullThreeTorus]
  refine ⟨(CFSG.StandardType.TableCRes.rootDiagUnit_mem_langTorus_iff S
    (zetaVec ζ hζ x)).mpr ?_, ?_⟩
  · intro γ hγ
    have h3 : rootChar (zetaVec ζ hζ x) γ ^ 3 = 1 := by
      rw [CFSG.StandardType.NoOffE8Five.rootChar_zetaVec]
      exact twIn_zmodPowHom_pow_three hζ _
    have h2 : rootChar (zetaVec ζ hζ x) γ ^ 2 = (rootChar (zetaVec ζ hζ x) γ)⁻¹ := by
      have h3' : rootChar (zetaVec ζ hζ x) γ ^ 2 * rootChar (zetaVec ζ hζ x) γ = 1 := by
        calc rootChar (zetaVec ζ hζ x) γ ^ 2 * rootChar (zetaVec ζ hζ x) γ
            = rootChar (zetaVec ζ hζ x) γ ^ (2 + 1) :=
              (pow_succ (rootChar (zetaVec ζ hζ x) γ) 2).symm
          _ = rootChar (zetaVec ζ hζ x) γ ^ 3 := by norm_num
          _ = 1 := h3
      exact eq_inv_of_mul_eq_one_left h3'
    rw [hS.2.2 γ hγ, twIn_rootChar_neg]
    simpa [hS.1] using h2.symm
  · rw [rootDiagUnit_pow, ← rootDiagUnit_one]
    congr 1
    funext i
    exact twIn_zetaVec_pow_three hζ x i

theorem zetaTorus_top_eq_fullThreeTorus {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) (hS : NegLangTwo S) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) : zetaTorus ζ hζ ⊤ = fullThreeTorus S :=
  le_antisymm (twIn_zetaTorus_subset_top S hS hζ)
    (twIn_fullThreeTorus_subset_top S hζ hζo)

private theorem twIn_card_fullThreeTorus {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) (hS : NegLangTwo S) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) : Nat.card (fullThreeTorus S) = 3 ^ 6 := by
  rw [← zetaTorus_top_eq_fullThreeTorus S hS hζ hζo, card_zetaTorus hζo,
    AddSubgroup.card_top, Nat.card_fun]
  norm_num [ZMod.card, Tag.rank]

private theorem twIn_torusElt_mem_Γ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (j : Fin Tag.E6.rank) : torusElt Tag.E6 L j ζ ∈ S.Γ := by
  rw [torusElt_eq_rootDiagUnit]
  have htuple : (fun l => ζ ^ Tag.E6.cartan j l) =
      (fun l => ζ ^ corootPair (Pi.single j 1 : Fin Tag.E6.rank → ℤ) (Pi.single l 1)) := by
    funext l
    rw [twIn_corootPair_single_single]
  rw [htuple]
  exact corootTuple_mem_Γ_of_rho_neg S hq hρ (isRoot_single Tag.E6 j) hζ

private theorem twIn_zetaTorus_le_Γ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) :
    zetaTorus ζ hζ hypE6 ≤ S.Γ := by
  intro t ht
  rw [mem_zetaTorus] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  obtain ⟨y, hy⟩ := NoOffE6Three.zetaVec_eq_cartanChar_of_mem_hyp ζ hζ hx
  have hprod : rootDiagUnit Tag.E6 (zetaVec ζ hζ x) =
      ((List.finRange Tag.E6.rank).map fun j =>
        torusElt Tag.E6 L j (zetaVec ζ hζ y j)).prod := by
    rw [hy, ← list_prod_torusElt_eq_rootDiagUnit]
  rw [hprod]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  simp only [List.mem_map, List.mem_finRange] at hg
  obtain ⟨j, -, rfl⟩ := hg
  have hpow : torusElt Tag.E6 L j (zetaVec ζ hζ y j) =
      (torusElt Tag.E6 L j ζ) ^ (y j).val := by
    rw [zetaVec_apply]
    exact map_pow (torusEltHom Tag.E6 L j) ζ (y j).val
  rw [hpow]
  exact S.Γ.pow_mem (twIn_torusElt_mem_Γ S hq hρ hζ j) _

private theorem twIn_twisted_frobenius_form {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ) :
    ∃ Fr : L →+* L, (∀ c, Fr c = c ^ 2) ∧
      S.D.Φ = twistHom TwistTag.E6 L Fr := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  rcases hP with rfl | ⟨t, ht, rfl⟩
  · exfalso
    obtain ⟨w, hn⟩ := S.D.n_weyl
    have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext g
      rw [hΦ g, one_mul, inv_one, mul_one]
    obtain ⟨γ, hγ, hne⟩ := no_weyl_neg_one_E6 w
    have h1 : S.ρ γ = w • γ := S.rho_eq_smul_of_frob hFr hΦ' hn hγ
    exact hne (by rw [← h1, hρ γ hγ])
  · refine ⟨Fr, fun c => by rw [hFr c, hq], ?_⟩
    cases t with
    | E6 =>
        cases ht
        ext g
        rw [hΦ g]
        rfl
    | D4 => exact absurd ht (by decide)

theorem fullThreeTorus_inf_Γ_eq_zetaTorus {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) (hS : NegLangTwo S) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) : fullThreeTorus S ⊓ S.Γ = zetaTorus ζ hζ hypE6 := by
  have : CharP L 2 :=
    CFSG.StandardType.LangRat.charP_two_of_langSetup_q_eq_two_pow (f := 1) S
      (by rw [hS.1]; norm_num)
  obtain ⟨Fr, hFr, hΦ⟩ := twIn_twisted_frobenius_form S hS.1 hS.2.2
  have halg : ∀ c : L, ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c := by
    intro c
    obtain ⟨n, hn, hc⟩ := hS.2.1 c
    exact ⟨n, hn, by simpa [hS.1] using hc⟩
  have hdvd := CFSG.StandardType.TwE6Tori.twE6_torus_meet_gamma_dvd Fr halg S.D hFr hΦ
  have hsub : Nat.card ↥(S.D.torus.subgroupOf S.D.Γ) = Nat.card ↥(S.D.torus ⊓ S.D.Γ) := by
    rw [← Subgroup.card_map_of_injective S.D.Γ.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  have hdvd' : Nat.card ↥(S.D.torus ⊓ S.D.Γ) * 3 ∣ Nat.card S.D.torus := hsub ▸ hdvd
  rw [← fullThreeTorus_eq_torus S hS.1 hS.2.2] at hdvd'
  rw [twIn_card_fullThreeTorus S hS hζ hζo] at hdvd'
  have hdiv : Nat.card ↥(fullThreeTorus S ⊓ S.D.Γ) ∣ 3 ^ 5 := by
    have h3 : 3 * Nat.card ↥(fullThreeTorus S ⊓ S.D.Γ) ∣ 3 * 3 ^ 5 := by
      rwa [mul_comm (Nat.card ↥(fullThreeTorus S ⊓ S.D.Γ)) 3,
        show (3 : ℕ) ^ 6 = 3 * 3 ^ 5 by norm_num] at hdvd'
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  have hZleT : zetaTorus ζ hζ hypE6 ≤ fullThreeTorus S := by
    intro t ht
    rw [mem_zetaTorus] at ht
    obtain ⟨x, hx, rfl⟩ := ht
    rw [← zetaTorus_top_eq_fullThreeTorus S hS hζ hζo, mem_zetaTorus]
    exact ⟨x, AddSubgroup.mem_top x, rfl⟩
  have hZleΓ : zetaTorus ζ hζ hypE6 ≤ S.Γ := twIn_zetaTorus_le_Γ S hS.1 hS.2.2 hζ
  have hZle : zetaTorus ζ hζ hypE6 ≤ fullThreeTorus S ⊓ S.Γ := le_inf hZleT hZleΓ
  have hfinModel : Finite ↥S.D.model := S.finite
  have hleModel : fullThreeTorus S ⊓ S.Γ ≤ S.D.model := by
    intro x hx
    exact S.D.torus_le_model ((fullThreeTorus_le_torus S) hx.1)
  have hfinInf : Finite ↥(fullThreeTorus S ⊓ S.Γ) :=
    Finite.of_injective
      (fun x : ↥(fullThreeTorus S ⊓ S.Γ) => (⟨x.1, hleModel x.2⟩ : ↥S.D.model))
      (fun x y h => Subtype.ext
        (congrArg (fun z : ↥S.D.model => (z : ModGL Tag.E6 L)) h))
  have hZcard : Nat.card (zetaTorus ζ hζ hypE6) = 3 ^ 5 := by
    rw [card_zetaTorus hζo]
    exact card_hypE6
  have hlecard : 3 ^ 5 ≤ Nat.card ↥(fullThreeTorus S ⊓ S.Γ) := by
    rw [← hZcard]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hZle)
  have hup : Nat.card ↥(fullThreeTorus S ⊓ S.Γ) ≤ 3 ^ 5 :=
    Nat.le_of_dvd (by norm_num) hdiv
  have hcardeq : Nat.card ↥(fullThreeTorus S ⊓ S.Γ) = 3 ^ 5 := le_antisymm hup hlecard
  exact (Subgroup.eq_of_le_of_card_ge hZle (by rw [hcardeq, hZcard])).symm

theorem card_fullThreeTorus_inf_Γ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) (hS : NegLangTwo S) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) : Nat.card ↥(fullThreeTorus S ⊓ S.Γ) = 3 ^ 5 := by
  rw [fullThreeTorus_inf_Γ_eq_zetaTorus S hS hζ hζo, card_zetaTorus hζo]
  exact card_hypE6

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
