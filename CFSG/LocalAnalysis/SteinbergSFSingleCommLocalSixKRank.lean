module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixKDefs

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixK_k5_aux_sylow (hS : SCSetting L K n φ t i) :
    ∃ Syl : Sylow 2 ↥(centralizer ({t} : Set G)),
      P φ ⊔ zpowers t ≤
        (Syl : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype := by
  have hQC : P φ ⊔ zpowers t ≤ centralizer ({t} : Set G) := hS.fc.setup.Q_le_C
  obtain ⟨Syl, hQSyl⟩ :=
    (hS.fc.setup.Q_two.of_equiv (subgroupOfEquivOfLe hQC).symm).exists_le_sylow
  exact ⟨Syl, fun q hq => ⟨⟨q, hQC hq⟩, hQSyl (mem_subgroupOf.mpr hq), rfl⟩⟩

theorem sixK_k5
    (hS : SCSetting L K n φ t i) : K5Concl n φ t := by
  intro E hEC hEX hEc
  obtain ⟨Syl, hQSyl⟩ := sixK_k5_aux_sylow hS
  have hRGC : (Syl : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype ≤ centralizer ({t} : Set G) :=
    Subgroup.map_subtype_le _
  have hRG2 : IsPGroup 2 ((Syl : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype) :=
    Syl.isPGroup'.map _
  have hEXs : ∀ x : E, x * x = 1 := fun x => Subtype.ext (hEX (x : G) x.2)
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (two_pow_rank_eq_card_of_sq hEXs).symm
  obtain ⟨c, -, hconj⟩ := GomiFusion.Setup.exists_conj_le_sylow Syl hEC hE2
  obtain ⟨E', hE'⟩ : ∃ E' : Subgroup G, E' = E.map (MulAut.conj c⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hmemE' : ∀ x ∈ E', ∃ y ∈ E, (MulAut.conj c⁻¹).toMonoidHom y = x := by
    intro x hx
    rw [hE'] at hx
    exact Subgroup.mem_map.mp hx
  have hE'RG : E' ≤ (Syl : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hmemE' x hx
    have e : (MulAut.conj c⁻¹).toMonoidHom y = c⁻¹ * y * c := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [e]
    exact hconj y hy
  have hcard : Nat.card E' = Nat.card E := by
    rw [hE']
    exact Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  have hE'X : ∀ x ∈ E', x * x = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hmemE' x hx
    rw [← map_mul, hEX y hy, map_one]
  have hE'c : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := hmemE' x hx
    obtain ⟨b, hb, rfl⟩ := hmemE' y hy
    rw [← map_mul, ← map_mul, hEc a ha b hb]
  haveI : IsMulCommutative E' := isMulCommutative_iff_of_setLike.mpr hE'c
  have hrank : Group.rank E' ≤ 3 * n + 1 :=
    (hS.fc.setup.rank_bound hRGC hRG2 hQSyl hE'RG).1
  have h2 : 2 ^ Group.rank E' = Nat.card E' :=
    two_pow_rank_eq_card_of_sq (fun x : E' => Subtype.ext (hE'X (x : G) x.2))
  rw [← hcard, ← h2]
  exact Nat.pow_le_pow_right (by norm_num) hrank

theorem sixK_k6_aux_mulAut (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (H : Subgroup (MulAut (antiSp K))) (k : ℕ) (hk : Nat.card H = 2 ^ k) :
    Nat.card H ≤ Nat.card K ^ 4 * (2 * n) := by
  obtain ⟨hinj, -, hOut, -⟩ :=
    even_symplectic_four_outer_involution_rank_and_perfect_residual hn hK
  have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K)) =
      Nat.card (antiSp K) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hcardM : Nat.card (MulAut (antiSp K)) = Nat.card (antiSp K) * (2 * n) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K)), hOut, hinner]
    ring
  have hX : Nat.card (antiSp K) =
      Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) :=
    card_antiSp rfl
  have hqpos : 0 < Nat.card K := by
    rw [hK]
    exact pow_pos (by norm_num) n
  have hq2 : 2 ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self 2 (by omega)
  have hodd1 : ¬ 2 ∣ Nat.card K ^ 2 - 1 := by
    have h2a : 2 ∣ Nat.card K ^ 2 := dvd_pow hq2 two_ne_zero
    have h1a : 0 < Nat.card K ^ 2 := pow_pos hqpos 2
    generalize Nat.card K ^ 2 = a at h2a h1a ⊢
    omega
  have hodd2 : ¬ 2 ∣ Nat.card K ^ 4 - 1 := by
    have h2a : 2 ∣ Nat.card K ^ 4 := dvd_pow hq2 (by norm_num)
    have h1a : 0 < Nat.card K ^ 4 := pow_pos hqpos 4
    generalize Nat.card K ^ 4 = a at h2a h1a ⊢
    omega
  have hcop : Nat.Coprime (Nat.card H) ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.Coprime.mul_right
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd1)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd2))
  have hdvd : Nat.card H ∣
      Nat.card K ^ 4 * (2 * n) * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
    have h := Subgroup.card_subgroup_dvd_card H
    rw [hcardM, hX] at h
    have e : Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) * (2 * n) =
        Nat.card K ^ 4 * (2 * n) * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
      ring
    rw [e] at h
    exact h
  exact Nat.le_of_dvd (Nat.mul_pos (pow_pos hqpos 4) (by omega))
    (hcop.dvd_of_dvd_mul_right hdvd)

theorem sixK_k6
    (hS : SCSetting L K n φ t i) : K6Concl n φ t := by
  intro R hR hRC
  have hRN : R ≤ normalizer (L : Set G) := hRC.trans hS.fc.setup.cent_le
  have hker : Nat.card (subAct φ hRN).ker ≤ 2 := by
    have hsub : ((subAct φ hRN).ker).map R.subtype ≤ zpowers t := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      have hxL : (x : G) ∈ centralizer (L : Set G) :=
        (subAct_eq_one_iff φ hRN x).mp (MonoidHom.mem_ker.mp hx)
      have hxC : (x : G) ∈ centralizer ({t} : Set G) := hRC x.2
      rw [← hS.fc.setup.cent_inf]
      exact Subgroup.mem_inf.mpr ⟨hxL, hxC⟩
    have hmap : Nat.card (((subAct φ hRN).ker).map R.subtype) = Nat.card (subAct φ hRN).ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective R)
    rw [← hmap]
    calc Nat.card (((subAct φ hRN).ker).map R.subtype) ≤ Nat.card (zpowers t) :=
          Subgroup.card_le_of_le hsub
      _ = 2 := by rw [Nat.card_zpowers, hS.fc.setup.order_t]
  have hq := Nat.card_congr (QuotientGroup.quotientKerEquivRange (subAct φ hRN)).toEquiv
  have hdec : Nat.card R = Nat.card (subAct φ hRN).ker * Nat.card (subAct φ hRN).range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (subAct φ hRN).ker, hq]
    ring
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR
  have hdvdR : Nat.card (subAct φ hRN).range ∣ 2 ^ m := by
    rw [← hm, hdec]
    exact dvd_mul_left _ _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdR
  have himg := sixK_k6_aux_mulAut hS.fc.setup.two_le hS.fc.setup.card_K
    (subAct φ hRN).range k hk
  rw [hdec]
  calc Nat.card (subAct φ hRN).ker * Nat.card (subAct φ hRN).range
      ≤ 2 * (Nat.card K ^ 4 * (2 * n)) := Nat.mul_le_mul hker himg
    _ = 4 * n * Nat.card K ^ 4 := by ring

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
