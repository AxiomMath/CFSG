module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.RadSzCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.RadSzLevi
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParReeF4
import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelLevi
import CFSG.ClassicalGroups.PCoreSection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic
public import CFSG.LieType.Ree.Duality
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.LocalAnalysis.EvenBN.TwoF4
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

private lemma four_pow_mod_five (k : ℕ) : 4 ^ k % 5 = 1 ∨ 4 ^ k % 5 = 4 := by
  induction k with
  | zero => left; norm_num
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

private lemma odd_pow_mod_five (f : ℕ) (hf : Odd f) : 2 ^ f % 5 = 2 ∨ 2 ^ f % 5 = 3 := by
  obtain ⟨k, rfl⟩ := hf
  have h : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [h, Nat.mul_mod]
  rw [show (2 : ℕ) % 5 = 2 by norm_num]
  rcases four_pow_mod_five k with hm | hm <;> rw [hm] <;> norm_num

private lemma not_five_dvd_two_pow_mul_sq_sub_one (f : ℕ) (hf : Odd f) :
    ¬ 5 ∣ 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  intro hdvd
  have hp : Nat.Prime 5 := by norm_num
  rcases hp.dvd_mul.mp hdvd with h1 | h2
  · have h5 : 5 ∣ 2 := hp.dvd_of_dvd_pow h1
    norm_num at h5
  · have hq := odd_pow_mod_five f hf
    have hsq : (2 ^ f) ^ 2 % 5 = 4 := by
      rw [Nat.pow_mod]
      rcases hq with hq | hq <;> rw [hq]
    obtain ⟨m, hm⟩ : ∃ m, (2 ^ f) ^ 2 = m * 5 + 4 := by
      refine ⟨(2 ^ f) ^ 2 / 5, ?_⟩
      have hdm := Nat.div_add_mod ((2 ^ f) ^ 2) 5
      omega
    have hge : 1 ≤ (2 ^ f) ^ 2 := by
      have hx1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      calc 1 = 1 * 1 := by norm_num
        _ ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul hx1 hx1
        _ = (2 ^ f) ^ 2 := by ring
    have hsub : (2 ^ f) ^ 2 - 1 = m * 5 + 3 := by omega
    have h3 : (m * 5 + 3) % 5 = 3 := by
      rw [show m * 5 + 3 = 3 + m * 5 by omega, Nat.add_mul_mod_self_right]
    rw [hsub, Nat.dvd_iff_mod_eq_zero, h3] at h2
    omega

private lemma two_pow_dvd_sz (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (2 * n) ∣ (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) ∧
      ¬ 2 ^ (2 * n + 1) ∣ (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) := by
  have hx2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul]; ring_nf
  constructor
  · rw [hx2]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · intro h
    have heq : (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) =
        2 ^ (2 * n) * ((2 ^ n - 1) * ((2 ^ n) ^ 2 + 1)) := by
      rw [hx2]; ring
    rw [heq] at h
    have hfac : 2 ^ (2 * n + 1) = 2 ^ (2 * n) * 2 := by rw [pow_succ]
    rw [hfac] at h
    have h2 : 2 ∣ (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) :=
      (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ (2 * n))).1 h
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hxeven : Even (2 ^ (k + 1)) := ⟨2 ^ k, by rw [pow_succ]; ring⟩
    have hxodd : Odd (2 ^ (k + 1) - 1) :=
      Nat.Even.sub_odd (Nat.one_le_two_pow) hxeven odd_one
    have hx2even : Even ((2 ^ (k + 1)) ^ 2) := by
      obtain ⟨c, hc⟩ := hxeven
      exact ⟨2 * c * c, by rw [pow_two, hc]; ring⟩
    have hx21odd : Odd ((2 ^ (k + 1)) ^ 2 + 1) := hx2even.add_one
    obtain ⟨a, ha⟩ := Odd.mul hxodd hx21odd
    obtain ⟨b, hb⟩ := h2
    omega

private lemma eq_of_sz_card_eq (n f : ℕ) (hn : 1 ≤ n) (hf : 1 ≤ f)
    (h : (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) =
      (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1)) : n = f := by
  have hn' := (two_pow_dvd_sz n hn)
  have hf' := (two_pow_dvd_sz f hf)
  have h1 : 2 ^ (2 * n) ∣ (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
    rw [← h]; exact hn'.1
  have h2 : ¬ 2 ^ (2 * n + 1) ∣ (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
    rw [← h]; exact hn'.2
  have h3 : 2 ^ (2 * f) ∣ (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := hf'.1
  have h4 : ¬ 2 ^ (2 * f + 1) ∣ (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := hf'.2
  have hle : 2 * n ≤ 2 * f := by
    by_contra hlt
    exact h4 (dvd_trans (pow_dvd_pow 2 (by omega)) h1)
  have hle' : 2 * f ≤ 2 * n := by
    by_contra hlt
    exact h2 (dvd_trans (pow_dvd_pow 2 (by omega)) h3)
  omega

private lemma leviN_image_facts
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    {S : Type} [Group S] [Finite S] (Φ : ↥(F4.reeGamma K a) ≃* S) (i : Idx)
    (hi : i.isCenter = false) (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSimpleGroup ↥(((leviN K a i).subgroupOf (F4.reeGamma K a)).map Φ.toMonoidHom) ∧
    ¬ IsPGroup 2 ↥(((leviN K a i).subgroupOf (F4.reeGamma K a)).map Φ.toMonoidHom) ∧
    ((leviN K a i).subgroupOf (F4.reeGamma K a)).map Φ.toMonoidHom ≤
      Subgroup.centralizer ((((torusHi K a i).subgroupOf (F4.reeGamma K a)).map Φ.toMonoidHom :
        Subgroup S) : Set S) ∧
    (∀ x ∈ ((torusHi K a i).subgroupOf (F4.reeGamma K a)).map Φ.toMonoidHom,
      ∀ y ∈ ((torusHi K a i).subgroupOf (F4.reeGamma K a)).map Φ.toMonoidHom,
        x * y = y * x) := by
  set N' : Subgroup S := ((leviN K a i).subgroupOf (F4.reeGamma K a)).map Φ.toMonoidHom with hN'
  set H' : Subgroup S := ((torusHi K a i).subgroupOf (F4.reeGamma K a)).map Φ.toMonoidHom with hH'
  obtain ⟨hs, hna⟩ := isSimpleGroup_leviN ha hK i
  let eN : ↥(leviN K a i) ≃* ↥N' :=
    (Subgroup.subgroupOfEquivOfLe (leviN_le_reeGamma hK i)).symm.trans
      (Subgroup.equivMapOfInjective _ Φ.toMonoidHom Φ.injective)
  have hsimple : IsSimpleGroup ↥N' := (MulEquiv.isSimpleGroup_congr eN).mp hs
  refine ⟨hsimple, ?_, ?_, ?_⟩
  · intro hp
    have hne : Subgroup.center ↥N' ≠ ⊥ := by
      intro hbot
      have hnt : Nontrivial ↥(Subgroup.center ↥N') := hp.center_nontrivial
      rw [hbot] at hnt
      exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥N') with h | h
    · exact hne h
    · have hcomm : ∀ p q : ↥N', p * q = q * p := by
        intro p q
        have hp' : p ∈ Subgroup.center ↥N' := by rw [h]; trivial
        exact (Subgroup.mem_center_iff.1 hp' q).symm
      obtain ⟨x, y, hxy⟩ := hna
      have hxy' : eN x * eN y ≠ eN y * eN x := by
        intro he
        apply hxy
        apply eN.injective
        simpa [map_mul] using he
      exact hxy' (hcomm _ _)
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨m, hm, rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1
      ((miyamoto_2_2 ha hK hi).2.1 (Subgroup.mem_subgroupOf.1 hn))
      (m : ModGL F4.tag K) (Subgroup.mem_subgroupOf.1 hm))
  · intro x hx y hy
    obtain ⟨n, hn, rfl⟩ := hx
    obtain ⟨m, hm, rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (torusH_mul_comm (torusHi_le_torusH i (Subgroup.mem_subgroupOf.1 hn))
      (torusHi_le_torusH i (Subgroup.mem_subgroupOf.1 hm)))

theorem eq_of_lieModel_twistedF4_of_isComponentOf
    {S : Type} [Group S] [Finite S] {f : ℕ} (h : CFSG.Blueprint.LieModel S .twistedF4 0 2 f)
    {U : Subgroup S} (hrad : CFSG.Open.pCoreOf 2 (normalizer (U : Set S)) = U) (T : Sylow 2 S)
    (hTU : normalizer ((T : Subgroup S) : Set S) ≤ normalizer (U : Set S))
    (hPtop : normalizer (U : Set S) ≠ ⊤)
    (hPT : normalizer (U : Set S) ≠ normalizer ((T : Subgroup S) : Set S)) {n : ℕ}
    {B : Subgroup (↥(normalizer (U : Set S)) ⧸ CFSG.pCore 2 ↥(normalizer (U : Set S)))}
    (hB : CFSG.Open.IsComponentOf B ⊤) (hBsz : IsSz ↥B n) : n = f := by
  classical
  obtain ⟨-, hree⟩ := CFSG.Blueprint.LieModel.reeTitsModel h (by decide)
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hcardf, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model (X := S) hree
  let _ : Field K := hKF
  let _ : Finite K := hKFin
  let _ : CharP K F4.prime := hcp
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hcardf, hfa]
  let Γ : Subgroup (ModGL F4.tag K) := F4.reeGamma K a
  let U₀ : Subgroup (ModGL F4.tag K) := F4.reeFixedPosUnipotent K a
  let P₀ : Subgroup (ModGL F4.tag K) := F4.reeLocalParabolic K a ⟨0, by decide⟩
  let P₁ : Subgroup (ModGL F4.tag K) := F4.reeLocalParabolic K a ⟨1, by decide⟩
  have hTP : TwoPar ↥Γ (U₀.subgroupOf Γ) (P₀.subgroupOf Γ) (P₁.subgroupOf Γ) :=
    twoPar_reeF4 (K := K) (a := a) ha hK
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf (T : Subgroup S) ⊤ :=
    ⟨le_top, T.isPGroup', by
      rw [show ((T : Subgroup S).subgroupOf ⊤).index = (T : Subgroup S).index from
        Subgroup.relIndex_top_right _]
      exact T.not_dvd_index⟩
  have h1 : TwoPar S ((U₀.subgroupOf Γ).map e.symm.toMonoidHom)
      ((P₀.subgroupOf Γ).map e.symm.toMonoidHom)
      ((P₁.subgroupOf Γ).map e.symm.toMonoidHom) := hTP.map e.symm
  obtain ⟨g, hg⟩ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.exists_conj_of_sylowTwo h1.sylow hT
  let Φ : ↥Γ ≃* S := e.symm.trans (MulAut.conj g)
  have hΦX : ∀ X : Subgroup (ModGL F4.tag K),
      ((X.subgroupOf Γ).map e.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (X.subgroupOf Γ).map Φ.toMonoidHom := by
    intro X
    rw [Subgroup.map_map]
    rfl
  have hU₀Φ : (U₀.subgroupOf Γ).map Φ.toMonoidHom = (T : Subgroup S) := by
    rw [← hΦX U₀]
    exact hg
  let Q₀ : Subgroup S := (P₀.subgroupOf Γ).map Φ.toMonoidHom
  let Q₁ : Subgroup S := (P₁.subgroupOf Γ).map Φ.toMonoidHom
  have h2 : TwoPar S T Q₀ Q₁ := by
    have hh := h1.map (MulAut.conj g)
    rw [hΦX U₀, hΦX P₀, hΦX P₁, hU₀Φ] at hh
    exact hh
  have hQcases : Subgroup.normalizer (U : Set S) = Q₀ ∨
      Subgroup.normalizer (U : Set S) = Q₁ := by
    rcases h2.hover (Subgroup.normalizer (U : Set S)) hTU with h' | h' | h' | h'
    · exact absurd h' hPT
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd h' hPtop
  have hU₀Γ : U₀ ≤ Γ := reeFixedPosUnipotent_le_reeGamma
  have hP₀Γ : P₀ ≤ Γ := inf_le_left
  have hP₁Γ : P₁ ≤ Γ := inf_le_left
  have hRSΓ : radS K a ≤ Γ := by
    show radS K a ≤ F4.reeGamma K a
    rw [(radS_spec hK).1]
    exact inf_le_right
  have hRRΓ : radR K a ≤ Γ := by
    show radR K a ≤ F4.reeGamma K a
    rw [(radR_spec hK).1]
    exact inf_le_right
  have hN₁Γ : leviN K a .i1 ≤ Γ := by
    show leviN K a .i1 ≤ F4.reeGamma K a
    exact leviN_le_reeGamma hK .i1
  have hN₃Γ : leviN K a .i3 ≤ Γ := by
    show leviN K a .i3 ≤ F4.reeGamma K a
    exact leviN_le_reeGamma hK .i3
  have hH₁Γ : torusHi K a .i1 ≤ Γ := by
    show torusHi K a .i1 ≤ F4.reeGamma K a
    exact (torusHi_le_torusH .i1).trans (torusH_le_reeGamma hK)
  have hH₃Γ : torusHi K a .i3 ≤ Γ := by
    show torusHi K a .i3 ≤ F4.reeGamma K a
    exact (torusHi_le_torusH .i3).trans (torusH_le_reeGamma hK)
  have hmiy := miyamoto_2_3 (K := K) (a := a) ha hK
  have hP₀eq : P₀ = radS K a ⊔ leviN K a .i3 ⊔ torusHi K a .i3 :=
    hmiy.2.2.2.symm.trans hmiy.2.1
  have hP₁eq : P₁ = radR K a ⊔ leviN K a .i1 ⊔ torusHi K a .i1 :=
    hmiy.2.2.1.symm.trans hmiy.1
  have hsub₀ : P₀.subgroupOf Γ = (radS K a).subgroupOf Γ ⊔ (leviN K a .i3).subgroupOf Γ ⊔
      (torusHi K a .i3).subgroupOf Γ := by
    rw [hP₀eq, Subgroup.subgroupOf_sup (sup_le hRSΓ hN₃Γ) hH₃Γ,
      Subgroup.subgroupOf_sup hRSΓ hN₃Γ]
  have hsub₁ : P₁.subgroupOf Γ = (radR K a).subgroupOf Γ ⊔ (leviN K a .i1).subgroupOf Γ ⊔
      (torusHi K a .i1).subgroupOf Γ := by
    rw [hP₁eq, Subgroup.subgroupOf_sup (sup_le hRRΓ hN₁Γ) hH₁Γ,
      Subgroup.subgroupOf_sup hRRΓ hN₁Γ]
  let RS' : Subgroup S := ((radS K a).subgroupOf Γ).map Φ.toMonoidHom
  let RR' : Subgroup S := ((radR K a).subgroupOf Γ).map Φ.toMonoidHom
  let N₃' : Subgroup S := ((leviN K a .i3).subgroupOf Γ).map Φ.toMonoidHom
  let N₁' : Subgroup S := ((leviN K a .i1).subgroupOf Γ).map Φ.toMonoidHom
  let H₃' : Subgroup S := ((torusHi K a .i3).subgroupOf Γ).map Φ.toMonoidHom
  let H₁' : Subgroup S := ((torusHi K a .i1).subgroupOf Γ).map Φ.toMonoidHom
  have hQ₀eq : Q₀ = RS' ⊔ N₃' ⊔ H₃' := by
    show (P₀.subgroupOf Γ).map Φ.toMonoidHom = _
    rw [hsub₀, Subgroup.map_sup, Subgroup.map_sup]
  have hQ₁eq : Q₁ = RR' ⊔ N₁' ⊔ H₁' := by
    show (P₁.subgroupOf Γ).map Φ.toMonoidHom = _
    rw [hsub₁, Subgroup.map_sup, Subgroup.map_sup]
  have hfacts₃ := leviN_image_facts Φ .i3 (by decide) ha hK
  have hfacts₁ := leviN_image_facts Φ .i1 (by decide) ha hK
  have hRS2 : IsPGroup 2 RS' := by
    have h : IsPGroup 2 ↥(radS K a) :=
      IsPGroup.of_card (n := (2 * a + 1) * 11) (by rw [(radS_spec hK).2.2.1, pow_mul])
    exact ((h.of_equiv (Subgroup.subgroupOfEquivOfLe hRSΓ).symm)).map Φ.toMonoidHom
  have hRR2 : IsPGroup 2 RR' := by
    have h : IsPGroup 2 ↥(radR K a) :=
      IsPGroup.of_card (n := (2 * a + 1) * 10) (by rw [(radR_spec hK).2.2.1, pow_mul])
    exact ((h.of_equiv (Subgroup.subgroupOfEquivOfLe hRRΓ).symm)).map Φ.toMonoidHom
  have hcardN₃ : Nat.card N₃' = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    show Nat.card (((leviN K a .i3).subgroupOf Γ).map Φ.toMonoidHom) = _
    rw [Subgroup.card_map_of_injective Φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₃Γ).toEquiv,
      card_leviN_of_isLin hK (by decide), ← hfa]
  have hcardN₁ : Nat.card N₁' = (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
    show Nat.card (((leviN K a .i1).subgroupOf Γ).map Φ.toMonoidHom) = _
    rw [Subgroup.card_map_of_injective Φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₁Γ).toEquiv,
      card_leviN_of_not_isLin ha hK (by decide), ← hfa]
  have hnorm₀ : Q₀ ≤ Subgroup.normalizer (RS' : Set S) := by
    show (P₀.subgroupOf Γ).map Φ.toMonoidHom ≤ _
    have hle : P₀.subgroupOf Γ ≤
        Subgroup.normalizer ((radS K a).subgroupOf Γ : Set ↥Γ) := by
      rw [show P₀ = Γ ⊓ Subgroup.normalizer (radS K a : Set (ModGL F4.tag K)) from
          hmiy.2.2.2.symm,
        CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer Γ (radS K a)
          hRSΓ]
    calc (P₀.subgroupOf Γ).map Φ.toMonoidHom
        ≤ (Subgroup.normalizer ((radS K a).subgroupOf Γ : Set ↥Γ)).map Φ.toMonoidHom :=
          Subgroup.map_mono hle
      _ = Subgroup.normalizer (((radS K a).subgroupOf Γ).map Φ.toMonoidHom : Set S) :=
          Subgroup.map_equiv_normalizer_eq _ Φ
  have hnorm₁ : Q₁ ≤ Subgroup.normalizer (RR' : Set S) := by
    show (P₁.subgroupOf Γ).map Φ.toMonoidHom ≤ _
    have hle : P₁.subgroupOf Γ ≤
        Subgroup.normalizer ((radR K a).subgroupOf Γ : Set ↥Γ) := by
      rw [show P₁ = Γ ⊓ Subgroup.normalizer (radR K a : Set (ModGL F4.tag K)) from
          hmiy.2.2.1.symm,
        CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer Γ (radR K a)
          hRRΓ]
    calc (P₁.subgroupOf Γ).map Φ.toMonoidHom
        ≤ (Subgroup.normalizer ((radR K a).subgroupOf Γ : Set ↥Γ)).map Φ.toMonoidHom :=
          Subgroup.map_mono hle
      _ = Subgroup.normalizer (((radR K a).subgroupOf Γ).map Φ.toMonoidHom : Set S) :=
          Subgroup.map_equiv_normalizer_eq _ Φ
  rcases hQcases with hQ₀ | hQ₁
  ·
    have hP : Subgroup.normalizer (U : Set S) = RS' ⊔ N₃' ⊔ H₃' := hQ₀.trans hQ₀eq
    have hRU : RS' ≤ U := by
      have hle : RS' ≤ Subgroup.normalizer (U : Set S) := by
        rw [hP]
        exact (le_sup_left : RS' ≤ RS' ⊔ N₃').trans le_sup_left
      have hnorm : ∀ x ∈ Subgroup.normalizer (U : Set S), ∀ y ∈ RS', x * y * x⁻¹ ∈ RS' := by
        intro x hx y hy
        have hx' : x ∈ Q₀ := by rw [← hQ₀]; exact hx
        exact (Subgroup.mem_normalizer_iff.1 (hnorm₀ hx') y).1 hy
      have h := CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hle hnorm hRS2
      rwa [hrad] at h
    have hcardB := card_eq_of_isComponentOf_sup hrad hP hRU hfacts₃.1 hfacts₃.2.1
      hfacts₃.2.2.1 hfacts₃.2.2.2 hB
    exfalso
    have h5 : 5 ∣ Nat.card B := (isSz_facts hBsz).2.2.2.2.2.2
    rw [hcardB, hcardN₃] at h5
    exact (not_five_dvd_two_pow_mul_sq_sub_one f ⟨a, hfa⟩) h5
  ·
    have hP : Subgroup.normalizer (U : Set S) = RR' ⊔ N₁' ⊔ H₁' := hQ₁.trans hQ₁eq
    have hRU : RR' ≤ U := by
      have hle : RR' ≤ Subgroup.normalizer (U : Set S) := by
        rw [hP]
        exact (le_sup_left : RR' ≤ RR' ⊔ N₁').trans le_sup_left
      have hnorm : ∀ x ∈ Subgroup.normalizer (U : Set S), ∀ y ∈ RR', x * y * x⁻¹ ∈ RR' := by
        intro x hx y hy
        have hx' : x ∈ Q₁ := by rw [← hQ₁]; exact hx
        exact (Subgroup.mem_normalizer_iff.1 (hnorm₁ hx') y).1 hy
      have h := CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hle hnorm hRR2
      rwa [hrad] at h
    have hcardB := card_eq_of_isComponentOf_sup hrad hP hRU hfacts₁.1 hfacts₁.2.1
      hfacts₁.2.2.1 hfacts₁.2.2.2 hB
    have hBcard : Nat.card B = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) :=
      (isSz_facts hBsz).2.2.2.1
    have hn : 1 ≤ n := by
      have := (isSz_facts hBsz).2.2.1
      omega
    refine eq_of_sz_card_eq n f hn (by omega) ?_
    rw [← hBcard, hcardB, hcardN₁]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
