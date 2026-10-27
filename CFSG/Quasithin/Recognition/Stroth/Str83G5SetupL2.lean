module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Setup
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame

import CFSG.Quasithin.Recognition.Stroth.Str83G4Shape4
import CFSG.Quasithin.Recognition.Stroth.Str83G5Rep

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.Quasithin.OperatorJH

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

private theorem q2_lt_s (hfr : Str83G4Frame L1 L2 S a) :
    Q2 L1 L2 S < S := by
  have hQ2S : Q2 L1 L2 S ≤ S := str83G4_q2_le_s hfr
  obtain ⟨hF, hB, ha, -, hL2, -⟩ := hfr
  have hrel : (Q2 L1 L2 S).relIndex S = 2 ^ (2 * a + 1) :=
    str86_relIndex_q2_s (n := 2 * a + 1) hF hB (by omega) hL2
  have hq1 : 1 < 2 ^ (2 * a + 1) :=
    Nat.one_lt_two_pow (n := 2 * a + 1) (by omega)
  have hne : Q2 L1 L2 S ≠ S := by
    intro h
    rw [h, Subgroup.relIndex_self] at hrel
    omega
  exact lt_of_le_of_ne hQ2S hne

private theorem d2_le_normalizer_q2 (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    d.D2 ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) := by
  intro δ hδ
  exact le_normalizer_pCoreOf 2 (P2 L1 L2 S)
    ((le_sup_left : L2 ≤ P2 L1 L2 S) (F1.borelOf_le L2 S (d.hD2hall.1 hδ)))

private theorem d2_le_normalizer_s (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) : d.D2 ≤ Subgroup.normalizer (S : Set G) := by
  obtain ⟨-, hB, -, -, -, -⟩ := hfr
  have hle : borelOf L2 S ≤ bigB L1 L2 S :=
    (le_sup_right : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans le_sup_left
  exact fun δ hδ => hB (hle (d.hD2hall.1 hδ))

private theorem s_le_normalizer_q2 :
    S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
  (le_sup_right : S ≤ bigB L1 L2 S).trans
    ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S)))

private theorem q2_orbitMap_injective
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) {J : Subgroup G} {x : G}
    (hxJ : x ∈ J) (hxQ : x ∉ Q2 L1 L2 S) (hJS : J ≤ S)
    (hDJ : d.D2 ≤ Subgroup.normalizer (J : Set G))
    (hmemJ : ∀ δ ∈ d.D2, δ * x * δ⁻¹ ∈ J) :
    Function.Injective (fun δ : d.D2 =>
      (QuotientGroup.mk (s := (Q2 L1 L2 S).subgroupOf J)
        (⟨δ * x * δ⁻¹, hmemJ δ δ.2⟩ : ↥J) :
        ↥J ⧸ (Q2 L1 L2 S).subgroupOf J)) := by
  classical
  intro δ δ' hq
  have hxS : x ∈ S := hJS hxJ
  have hmem : (⟨δ * x * δ⁻¹, hmemJ δ δ.2⟩ : ↥J)⁻¹ *
      (⟨δ' * x * δ'⁻¹, hmemJ δ' δ'.2⟩ : ↥J) ∈
        (Q2 L1 L2 S).subgroupOf J :=
    QuotientGroup.eq.mp hq
  have hmemG : (δ * x * δ⁻¹)⁻¹ * (δ' * x * δ'⁻¹) ∈ Q2 L1 L2 S :=
    Subgroup.mem_subgroupOf.mp hmem
  have hD2conj : ∀ y ∈ d.D2, ∀ q ∈ Q2 L1 L2 S,
      y * q * y⁻¹ ∈ Q2 L1 L2 S :=
    Subgroup.le_normalizer_iff.mp (d2_le_normalizer_q2 hfr d)
  have hSconj : ∀ y ∈ S, ∀ q ∈ Q2 L1 L2 S, y * q * y⁻¹ ∈ Q2 L1 L2 S :=
    Subgroup.le_normalizer_iff.mp s_le_normalizer_q2
  let E : G := ↑(δ⁻¹ * δ')
  have h1 : x⁻¹ * E * x * E⁻¹ ∈ Q2 L1 L2 S := by
    have h := hD2conj δ⁻¹ (d.D2.inv_mem δ.2) _
      (by simpa only [Subgroup.coe_inv, Subgroup.coe_mul] using hmemG)
    have e : x⁻¹ * E * x * E⁻¹ =
        (↑δ)⁻¹ * ((↑δ * x * (↑δ)⁻¹)⁻¹ * (↑δ' * x * (↑δ')⁻¹)) * (↑δ)⁻¹⁻¹ := by
      dsimp only [E]
      simp only [Subgroup.coe_inv, Subgroup.coe_mul]
      group
    rw [e]
    exact h
  have h2 : E * x * E⁻¹ * x⁻¹ ∈ Q2 L1 L2 S := by
    have h := hSconj x hxS _ h1
    have e : x * (x⁻¹ * E * x * E⁻¹) * x⁻¹ = E * x * E⁻¹ * x⁻¹ := by
      group
    rwa [e] at h
  by_cases hε : δ⁻¹ * δ' = 1
  · exact inv_mul_eq_one.mp hε
  · have hεG : E ≠ 1 := by
      intro h
      have h' : (↑(δ⁻¹ * δ') : G) = 1 := by simpa only [E] using h
      exact hε (Subtype.ext (by simpa only [Subgroup.coe_one] using h'))
    exact absurd (str83G4_fpf_D2 hfr d (by simpa only [E] using (δ⁻¹ * δ').2)
      hεG hxS h2) hxQ

private theorem q2_card_le_of_cartan
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hcard : Nat.card d.D2 = 2 ^ (2 * a + 1) - 1) {J : Subgroup G}
    (hQJ : Q2 L1 L2 S ≤ J) (hJS : J ≤ S)
    (hDJ : d.D2 ≤ Subgroup.normalizer (J : Set G)) (hJQ : J ≠ Q2 L1 L2 S) :
    Nat.card d.D2 ≤ Nat.card (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) - 1 := by
  classical
  have hlt : Q2 L1 L2 S < J := lt_of_le_of_ne hQJ (Ne.symm hJQ)
  obtain ⟨x, hxJ, hxQ⟩ := SetLike.exists_of_lt hlt
  haveI hQn : ((Q2 L1 L2 S).subgroupOf J).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hJS.trans s_le_normalizer_q2)
  have hmemJ : ∀ δ ∈ d.D2, δ * x * δ⁻¹ ∈ J := fun δ hδ =>
    (Subgroup.mem_normalizer_iff.mp (hDJ hδ) x).mp hxJ
  have hmemQ : ∀ δ ∈ d.D2, δ * x * δ⁻¹ ∉ Q2 L1 L2 S := by
    intro δ hδ hq
    have h1 : δ⁻¹ * (δ * x * δ⁻¹) * δ ∈ Q2 L1 L2 S := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp
          (d2_le_normalizer_q2 hfr d (d.D2.inv_mem hδ)) _).mp hq
    have h1x : δ⁻¹ * (δ * x * δ⁻¹) * δ = x := by group
    exact hxQ (by rwa [h1x] at h1)
  let f : d.D2 → {c : (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) // c ≠ 1} := fun δ =>
    ⟨QuotientGroup.mk (⟨δ * x * δ⁻¹, hmemJ δ δ.2⟩ : ↥J),
      fun h => hmemQ δ δ.2 (Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff (⟨δ * x * δ⁻¹, hmemJ δ δ.2⟩ : ↥J)).mp h))⟩
  have hinj : Function.Injective f := by
    intro δ δ' hff
    have hq : (QuotientGroup.mk (⟨δ * x * δ⁻¹, hmemJ δ δ.2⟩ : ↥J) :
        (↥J ⧸ (Q2 L1 L2 S).subgroupOf J)) =
        (QuotientGroup.mk (⟨δ' * x * δ'⁻¹, hmemJ δ' δ'.2⟩ : ↥J) :
        (↥J ⧸ (Q2 L1 L2 S).subgroupOf J)) :=
      congrArg Subtype.val hff
    exact q2_orbitMap_injective hfr d hxJ hxQ hJS hDJ hmemJ hq
  have hcard_le : Nat.card d.D2 ≤
      Nat.card {c : (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) // c ≠ 1} :=
    Nat.card_le_card_of_injective f hinj
  have hsub : Nat.card {c : (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) // c ≠ 1} =
      Nat.card (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) - 1 := by
    let : Fintype (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) := Fintype.ofFinite _
    let : Fintype {c : (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) // c ≠ 1} :=
      Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl
        (fun c : (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) => c = 1),
      Fintype.card_subtype_eq]
  rw [← hsub]
  exact hcard_le

private theorem q2_maximal_of_cartan
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hcard : Nat.card d.D2 = 2 ^ (2 * a + 1) - 1) {J : Subgroup G}
    (hQJ : Q2 L1 L2 S ≤ J) (hJS : J ≤ S)
    (hDJ : d.D2 ≤ Subgroup.normalizer (J : Set G)) :
    J = Q2 L1 L2 S ∨ J = S := by
  classical
  have ha : 1 ≤ a := hfr.2.2.1
  by_cases hJQ : J = Q2 L1 L2 S
  · exact Or.inl hJQ
  · right
    have hleJ := q2_card_le_of_cartan hfr d hcard hQJ hJS hDJ hJQ
    have hcardpos : 0 < Nat.card (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) := Nat.card_pos
    have hqle : 2 ^ (2 * a + 1) ≤ Nat.card (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) := by
      have h1 : Nat.card d.D2 + 1 ≤
          Nat.card (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) := by omega
      have h2 : Nat.card d.D2 + 1 = 2 ^ (2 * a + 1) := by
        rw [hcard]
        exact Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)
      omega
    have hrelJ : Nat.card (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) =
        (Q2 L1 L2 S).relIndex J := by
      change Nat.card (↥J ⧸ (Q2 L1 L2 S).subgroupOf J) =
        ((Q2 L1 L2 S).subgroupOf J).index
      rw [Subgroup.index_eq_card]
    have hqa : 2 ^ (2 * a + 1) ≤ (Q2 L1 L2 S).relIndex J := by
      rw [← hrelJ]
      exact hqle
    have hrelS : (Q2 L1 L2 S).relIndex S = 2 ^ (2 * a + 1) :=
      str86_relIndex_q2_s (n := 2 * a + 1) hfr.1 hfr.2.1 (by omega)
        hfr.2.2.2.2.1
    have hmul : (Q2 L1 L2 S).relIndex J * J.relIndex S = 2 ^ (2 * a + 1) := by
      rw [Subgroup.relIndex_mul_relIndex (Q2 L1 L2 S) J S hQJ hJS, hrelS]
    have hJpos : 0 < J.relIndex S := by
      change 0 < (J.subgroupOf S).index
      rw [Subgroup.index_eq_card]
      exact Nat.card_pos
    have hone : J.relIndex S = 1 := by
      have h1 : (Q2 L1 L2 S).relIndex J ≤
          (Q2 L1 L2 S).relIndex J * J.relIndex S :=
        Nat.le_mul_of_pos_right _ hJpos
      have h2 : (Q2 L1 L2 S).relIndex J * J.relIndex S ≤
          (Q2 L1 L2 S).relIndex J := by
        rw [hmul]
        exact hqa
      have h3 : (Q2 L1 L2 S).relIndex J * J.relIndex S =
          (Q2 L1 L2 S).relIndex J := le_antisymm h2 h1
      have hpos : (Q2 L1 L2 S).relIndex J ≠ 0 := by omega
      exact (Nat.mul_eq_left hpos).mp h3
    exact le_antisymm hJS (Subgroup.relIndex_eq_one.mp hone)

private theorem isYSimple_q2_of_cartan
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hcard : Nat.card d.D2 = 2 ^ (2 * a + 1) - 1) :
    IsYSimple d.D2 (Q2 L1 L2 S) S := by
  refine ⟨q2_lt_s hfr, s_le_normalizer_q2, d2_le_normalizer_q2 hfr d,
    d2_le_normalizer_s hfr d, ?_⟩
  intro J hQJ hJS _ hDJ
  exact q2_maximal_of_cartan hfr d hcard hQJ hJS hDJ

private theorem exists_mul_eq_zero_of_not_isUnit {N : ℕ} [NeZero N] (hN : 1 < N)
    {x : ZMod N} (hx : ¬ IsUnit x) :
    ∃ e, 0 < e ∧ e < N ∧ ((x.val * e : ℕ) : ZMod N) = 0 := by
  classical
  have hnotcop : ¬ Nat.Coprime x.val N := by
    intro hc
    apply hx
    rw [← ZMod.natCast_zmod_val (n := N) x]
    exact (ZMod.isUnit_iff_coprime x.val N).mpr hc
  have hgcd : Nat.gcd x.val N ≠ 1 := by
    rwa [Nat.coprime_iff_gcd_eq_one] at hnotcop
  obtain ⟨p, hp, hpgcd⟩ := Nat.exists_prime_and_dvd hgcd
  have hpN : p ∣ N := hpgcd.trans (Nat.gcd_dvd_right _ _)
  have hpx : p ∣ x.val := hpgcd.trans (Nat.gcd_dvd_left _ _)
  obtain ⟨e, he⟩ := hpN
  obtain ⟨u, hu⟩ := hpx
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exfalso
      rw [h, mul_zero] at he
      omega
    · exact h
  have helt : e < N := by
    rw [he]
    calc e = 1 * e := (one_mul e).symm
      _ < p * e := Nat.mul_lt_mul_of_pos_right hp.one_lt hepos
  refine ⟨e, hepos, helt, (ZMod.natCast_eq_zero_iff (x.val * e) N).mpr ⟨u, ?_⟩⟩
  rw [hu, he]
  ring

private theorem isUnit_label_of_chiEmb
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) {g : G}
    (hg : Subgroup.zpowers g = d.D2)
    (hgord : orderOf g = 2 ^ (2 * a + 1) - 1)
    {ζ : GaloisField 2 (2 * a + 1)} (hζ : orderOf ζ = 2 ^ (2 * a + 1) - 1)
    {φ : Coord (2 * a + 1)} {β : G → GaloisField 2 (2 * a + 1)}
    (hβ : IsChiEmb ζ g g (Q2 L1 L2 S) S φ β) : IsUnit φ.1 := by
  classical
  have ha : 1 ≤ a := hfr.2.2.1
  let N : ℕ := 2 ^ (2 * a + 1) - 1
  have hN1 : 1 < N := by
    have hq8 : 8 ≤ 2 ^ (2 * a + 1) := by
      have h : (2 : ℕ) ^ 3 ≤ 2 ^ (2 * a + 1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
          (by omega : 3 ≤ 2 * a + 1)
      norm_num at h
      exact h
    dsimp only [N]
    omega
  haveI : NeZero N := ⟨by omega⟩
  by_contra hnot
  obtain ⟨e, hepos, helt, hmod0⟩ := exists_mul_eq_zero_of_not_isUnit hN1 hnot
  have hzeta0 : ζ ^ (φ.1.val * e) = 1 := by
    have hmod0' : ((φ.1.val * e : ℕ) : ZMod (2 ^ (2 * a + 1) - 1)) = 0 := by
      simpa only [N] using hmod0
    simpa using pow_eq_pow_of_natCast_eq hζ (m₁ := φ.1.val * e) (m₂ := 0)
      (by simpa using hmod0')
  have hgD2 : g ∈ d.D2 := by
    rw [← hg]
    exact Subgroup.mem_zpowers g
  have hS1 : g ∈ Subgroup.normalizer (S : Set G) := d2_le_normalizer_s hfr d hgD2
  obtain ⟨s, hsS, hsQ⟩ := SetLike.exists_of_lt (q2_lt_s hfr)
  have hβe : ∀ t ∈ S, β (g ^ e * t * (g ^ e)⁻¹) = β t := by
    intro t ht
    have h := (hβ.conj₁_pow hS1 e t ht).2
    rw [h, ← pow_mul, hzeta0, one_mul]
  have hβinv : β s⁻¹ = -β s := by
    have h := hβ.map_mul s hsS s⁻¹ (S.inv_mem hsS)
    rw [mul_inv_cancel, hβ.map_one] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hconjS : g ^ e * s * (g ^ e)⁻¹ ∈ S := (hβ.conj₁_pow hS1 e s hsS).1
  have hβprod : β ((g ^ e * s * (g ^ e)⁻¹) * s⁻¹) = 0 := by
    rw [hβ.map_mul _ hconjS _ (S.inv_mem hsS), hβe s hsS, hβinv, add_neg_cancel]
  have hmemQ : (g ^ e * s * (g ^ e)⁻¹) * s⁻¹ ∈ Q2 L1 L2 S :=
    (hβ.eq_zero_iff _ (S.mul_mem hconjS (S.inv_mem hsS))).mp hβprod
  have hgeD2 : g ^ e ∈ d.D2 := by
    rw [← hg]
    exact Subgroup.npow_mem_zpowers g e
  have hge1 : g ^ e ≠ 1 := by
    intro h
    have hdvd' : orderOf g ∣ e := orderOf_dvd_of_pow_eq_one h
    rw [hgord] at hdvd'
    exact Nat.not_dvd_of_pos_of_lt hepos helt hdvd'
  exact hsQ (str83G4_fpf_D2 hfr d hgeD2 hge1 hsS hmemQ)

theorem exists_l2Emb
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    {ζ : GaloisField 2 (2 * a + 1)} (hζ : orderOf ζ = 2 ^ (2 * a + 1) - 1) :
    ∃ (d₂ : G) (β : G → GaloisField 2 (2 * a + 1)), zpowers d₂ = d.D2 ∧
      orderOf d₂ = 2 ^ (2 * a + 1) - 1 ∧
      IsChiEmb₁ ζ d₂ (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) S 1 β := by
  classical
  have hfr' := hfr
  obtain ⟨hF, hB, ha, -, hL2, -⟩ := hfr
  have hBt₂ : BenderType (oTwoQuot ↥L2) (2 * a + 1) 1 1 :=
    BenderType.linear (2 * a + 1) (by omega : 2 ≤ 2 * a + 1) (Classical.choice hL2)
  obtain ⟨hcard, hcyc⟩ :=
    card_isCyclic_of_hallTwoPrime (i := 1) hF.1.h2.sylow d.hD2hall d.hD2sup hBt₂
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top d.D2).mp hcyc
  have hgord : orderOf g = 2 ^ (2 * a + 1) - 1 := by
    rw [← Nat.card_zpowers (a := g), hg, hcard]
  have hY : IsYSimple (Subgroup.zpowers g ⊔ Subgroup.zpowers g) (Q2 L1 L2 S) S := by
    rw [sup_idem, hg]
    exact isYSimple_q2_of_cartan hfr' d hcard
  have hS : IsPGroup 2 S := (str83G4_isSylowTwoOf_sup_left hfr').2.1
  have hgpow : g ^ (2 ^ (2 * a + 1) - 1) = 1 := by
    rw [← hgord]
    exact pow_orderOf_eq_one g
  obtain ⟨φ, β, hβ⟩ := exists_isChiEmb (n := 2 * a + 1) hY hS (Commute.refl g)
    hgpow hgpow (by omega) hζ
  have hxunit : IsUnit φ.1 := isUnit_label_of_chiEmb hfr' d hg hgord hζ hβ
  let N : ℕ := 2 ^ (2 * a + 1) - 1
  have hN7 : 7 ≤ N := by
    have hq8 : 8 ≤ 2 ^ (2 * a + 1) := by
      have h : (2 : ℕ) ^ 3 ≤ 2 ^ (2 * a + 1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
          (by omega : 3 ≤ 2 * a + 1)
      norm_num at h
      exact h
    dsimp only [N]
    omega
  haveI : NeZero N := ⟨by omega⟩
  let k : ℕ := ((hxunit.unit⁻¹ : (ZMod N)ˣ) : ZMod N).val
  let d₂ : G := g ^ k
  have hkZ : (k : ZMod N) = ((hxunit.unit : ZMod N)⁻¹) := by
    dsimp only [k]
    rw [ZMod.natCast_zmod_val, ZMod.inv_coe_unit]
  have hxk : (φ.1.val : ZMod N) * (k : ZMod N) = 1 := by
    rw [ZMod.natCast_zmod_val, hkZ]
    exact ZMod.mul_inv_of_unit φ.1 hxunit
  have hcast : ((φ.1.val * k : ℕ) : ZMod N) = (1 : ZMod N) := by
    push_cast
    exact hxk
  have hcop : Nat.Coprime k N := by
    dsimp only [k]
    exact ZMod.val_coe_unit_coprime (hxunit.unit⁻¹)
  have hcop' : (orderOf g).Coprime k := by
    rw [hgord]
    exact hcop.symm
  have hord : orderOf d₂ = 2 ^ (2 * a + 1) - 1 := by
    dsimp only [d₂]
    rw [Nat.Coprime.orderOf_pow (y := g) (m := k) hcop', hgord]
  have hzp : Subgroup.zpowers d₂ = d.D2 := by
    dsimp only [d₂]
    have hmem : g ^ k ∈ d.D2 := by
      rw [← hg]
      exact Subgroup.npow_mem_zpowers g k
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) ?_
    rw [Nat.card_zpowers, hord, hcard]
  refine ⟨d₂, β, hzp, hord, hβ.map_mul, hβ.eq_zero_iff, ?_⟩
  intro s hs
  have hgD2 : g ∈ d.D2 := by
    rw [← hg]
    exact Subgroup.mem_zpowers g
  have hS1 : g ∈ Subgroup.normalizer (S : Set G) := d2_le_normalizer_s hfr' d hgD2
  have h := (hβ.conj₁_pow hS1 k s hs).2
  dsimp only [d₂]
  have hζ1 : ζ ^ (φ.1.val * k) = ζ ^ (1 : ZMod N).val := by
    rw [ZMod.val_one'' (by omega : N ≠ 1)]
    exact pow_eq_pow_of_natCast_eq hζ (by simpa using hcast)
  rw [h, (pow_mul ζ φ.1.val k).symm, hζ1]

end CFSG.Quasithin.Stroth.G5

end
