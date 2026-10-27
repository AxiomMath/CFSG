module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProof2125

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

@[expose] def Item2125UniqueOf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ Le ∈ thetaComponentsAt 3 e,
        Nonempty (lBar Le ≃* lBar L) → d ∈ Le → Sec4.InducesTypeOn Le d 1 →
        ∀ K ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card K → K = Le

namespace Item2119End3Proof

open Item2119EndProof

theorem exists_lOf2125
    (h211 : Item211) (h2116 : Item2116) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hGen : Item2125Generic) {G : Type} [Group G] [Finite G]
    {A E U L U₀ X : Subgroup G} {c d a : G} (hE : Config2119End G A E U c L d U₀ a X)
    (h23 : Concl2123 L X c d) (h24 : Concl2124 A L X d) {e : G} (he : e ∈ A)
    (hed : e ∉ Subgroup.zpowers d) :
    ∃ Le ∈ thetaComponentsAt 3 e, Nonempty (lBar Le ≃* lBar L) ∧ d ∈ Le ∧
      Sec4.InducesTypeOn Le d 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h23' := h23
  obtain ⟨⟨eXL⟩, hdX, hdTX, hcTX⟩ := h23
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  obtain ⟨n, -, -, ⟨eL⟩⟩ := hcfg.lthree
  have hpair' : Sec21Pair G A E U₀ a X :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hE.mem_U₀.1
      mem_pair := hE.mem_pair }
  obtain ⟨hn', he', hC', h27', hS3'⟩ :=
    Item21LateProof.case7_of_lBar_L3 h211 h2116 hpair' (eXL.trans eL)
  have hcfgX : Config2119 G A E U₀ a X :=
    ⟨hpair', ⟨n, hn', he', ⟨eXL.trans eL⟩⟩, hC', h27', hS3'⟩
  obtain ⟨hcL, d₀, -, -, -, hTU, -, -, -, ⟨w, ⟨hwL, hwN⟩, -, hwd₀, hwA, hwmove⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfg
  obtain ⟨-, d', -, -, -, hTU', -, -, -, ⟨w', ⟨hw'X, hw'N⟩, -, hw'd', hw'A, hw'move⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfgX
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairs' := mem_lThreeStarPairs_iff.mp hE.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have haA : a ∈ A := hpair.mem_E.2 hpairs'.1.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hXa : X ∈ thetaComponentsAt 3 a := lZeroStarAt_subset A a hpairs'.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  have hwc : w * c * w⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hwL), mul_inv_cancel_right]
  have hw'a : w' * a * w'⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hXC hw'X), mul_inv_cancel_right]
  have hZ₀ : Subgroup.zpowers d₀ = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU d hE.mem_d hd1 hE.type_d)
  have hZ' : Subgroup.zpowers d' = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU' d ⟨hdA, hdX⟩ hd1 hdTX)
  have hwd : w * d * w⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hwd₀ (by rw [hZ₀]; exact Subgroup.mem_zpowers d)
  have hw'd : w' * d * w'⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hw'd' (by rw [hZ']; exact Subgroup.mem_zpowers d)
  rw [hZ₀] at hwA
  rw [hZ'] at hw'A
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have haB : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
    rw [sup_comm]
    exact not_mem_sup_of_config2119End hE
  have hB9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm d hdA c hcA) hd3 (h3 c hcA) hd1 hcd
  obtain ⟨k₁, hk₁, hk₁e⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hwA a haA)
  have hwa : w * a * w⁻¹ = a * d ^ k₁ := by
    rw [← hk₁e]
    group
  have hk₁0 : k₁ ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hwa
    obtain ⟨y, hyA, hy⟩ := hwmove
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA haA hB9 haB hwa hwd hwc y hyA)
  obtain ⟨k₂, hk₂, hk₂e⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hw'A c hcA)
  have hw'c : w' * c * w'⁻¹ = c * d ^ k₂ := by
    rw [← hk₂e]
    group
  have hk₂0 : k₂ ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hw'c
    obtain ⟨y, hyA, hy⟩ := hw'move
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA haA hB9 haB hw'a hw'd hw'c y hyA)
  have hconjL : ∀ v : G, v * d * v⁻¹ = d → d ∈ L.map (MulAut.conj v).toMonoidHom := by
    intro v hv
    refine ⟨d, hdL, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hv
  have hconjX : ∀ v : G, v * d * v⁻¹ = d → d ∈ X.map (MulAut.conj v).toMonoidHom := by
    intro v hv
    refine ⟨d, hdX, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hv
  by_cases hecd : e ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d
  ·
    obtain ⟨i, hi, j, -, rfl⟩ :=
      Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm c hcA d hdA) (h3 c hcA) hd3 hecd
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply hed
      rw [pow_zero, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j
    obtain ⟨m, hm⟩ := exists_pow_conj_eq hd3 hw'd hk₂ hk₂0 hw'c ((i * j) % 3)
      (Nat.mod_lt _ (by norm_num))
    have hgd : w' ^ m * d * (w' ^ m)⁻¹ = d := conj_pow_eq_of_conj_eq hw'd m
    have hzp : Subgroup.zpowers ((MulAut.conj (w' ^ m)) c) =
        Subgroup.zpowers (c ^ i * d ^ j) := by
      rw [MulAut.conj_apply, hm]
      exact zpowers_mul_pow_eq (h3 c hcA) hd3 (hcomm c hcA d hdA) hi hi0
    have hmem : L.map (MulAut.conj (w' ^ m)).toMonoidHom ∈
        thetaComponentsAt 3 (c ^ i * d ^ j) := by
      rw [← thetaComponentsAt_eq_of_zpowers_eq hzp]
      exact map_mem_thetaComponentsAt (MulAut.conj (w' ^ m)) hLc
    refine ⟨L.map (MulAut.conj (w' ^ m)).toMonoidHom, hmem, ⟨(lBarMapConj (w' ^ m) L).symm⟩,
      hconjL _ hgd, ?_⟩
    have h1 := inducesTypeOn_map_conj (w' ^ m) hE.type_d
    rwa [hgd] at h1
  by_cases head : e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d
  ·
    obtain ⟨i, hi, j, -, rfl⟩ :=
      Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm a haA d hdA) (h3 a haA) hd3 head
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply hed
      rw [pow_zero, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j
    obtain ⟨m, hm⟩ := exists_pow_conj_eq hd3 hwd hk₁ hk₁0 hwa ((i * j) % 3)
      (Nat.mod_lt _ (by norm_num))
    have hhd : w ^ m * d * (w ^ m)⁻¹ = d := conj_pow_eq_of_conj_eq hwd m
    have hzp : Subgroup.zpowers ((MulAut.conj (w ^ m)) a) =
        Subgroup.zpowers (a ^ i * d ^ j) := by
      rw [MulAut.conj_apply, hm]
      exact zpowers_mul_pow_eq (h3 a haA) hd3 (hcomm a haA d hdA) hi hi0
    have hmem : X.map (MulAut.conj (w ^ m)).toMonoidHom ∈
        thetaComponentsAt 3 (a ^ i * d ^ j) := by
      rw [← thetaComponentsAt_eq_of_zpowers_eq hzp]
      exact map_mem_thetaComponentsAt (MulAut.conj (w ^ m)) hXa
    refine ⟨X.map (MulAut.conj (w ^ m)).toMonoidHom, hmem,
      ⟨(lBarMapConj (w ^ m) X).symm.trans eXL⟩, hconjX _ hhd, ?_⟩
    have h1 := inducesTypeOn_map_conj (w ^ m) hdTX
    rwa [hhd] at h1
  obtain ⟨Le, hLe, -, ⟨eLe⟩, hdLe, hdTLe, -⟩ := hGen G A E U c L d U₀ a X hE h23' h24 e he hecd head
  exact ⟨Le, hLe, ⟨eLe⟩, hdLe, hdTLe⟩

end Item2119End3Proof

open Item2119End3Proof

theorem item2125Unique_of
    (h211 : Item211) (h2116 : Item2116) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hUO : Item2125UniqueOf) (hGen : Item2125Generic) : Item2125Unique := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 e he hed K₁ hK₁ hK₁3 K₂ hK₂ hK₂3
  obtain ⟨Le, hLe, hLeL, hdLe, hdTLe⟩ :=
    exists_lOf2125 h211 h2116 h45 h66 hGen hE h23 h24 he hed
  rw [hUO G A E U c L d U₀ a X hE h23 h24 e he hed Le hLe hLeL hdLe hdTLe K₁ hK₁ hK₁3,
    hUO G A E U c L d U₀ a X hE h23 h24 e he hed Le hLe hLeL hdLe hdTLe K₂ hK₂ hK₂3]

end CFSG.RankThree.PartTwo.Sec21
