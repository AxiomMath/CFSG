module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofM22
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Defs
import CFSG.RankThree.PartTwo.Sec17.Item17Res2ProofL3
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

namespace Proof17Res7

section Coprime

variable {Λ : Type} [Group Λ] [Finite Λ]

@[expose] def conjHom {B Y : Subgroup Λ} (hBY : B ≤ Subgroup.normalizer (Y : Set Λ)) :
    ↥B →* MulAut ↥Y :=
  Y.normalizerMonoidHom.comp (Subgroup.inclusion hBY)

omit [Finite Λ] in
theorem conjHom_apply_coe {B Y : Subgroup Λ} (hBY : B ≤ Subgroup.normalizer (Y : Set Λ))
    (b : B) (y : Y) : ((conjHom hBY b y : Y) : Λ) = (b : Λ) * y * (b : Λ)⁻¹ :=
  rfl

theorem map_conjHom_subgroupOf {B Y R : Subgroup Λ} (hBY : B ≤ Subgroup.normalizer (Y : Set Λ))
    (hBR : B ≤ Subgroup.normalizer (R : Set Λ)) (b : B) :
    (R.subgroupOf Y).map (conjHom hBY b).toMonoidHom = R.subgroupOf Y := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : Λ) ∈ R := Subgroup.mem_subgroupOf.mp hy
    refine Subgroup.mem_subgroupOf.mpr ?_
    change ((conjHom hBY b y : Y) : Λ) ∈ R
    rw [conjHom_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hBR b.2) _).mp hy'
  · exact (Subgroup.card_map_of_injective (f := (conjHom hBY b).toMonoidHom)
      (MulEquiv.injective _)).ge

theorem eq_of_not_three_dvd {B R R' : Subgroup Λ} (hB3 : IsPGroup 3 B)
    (hC : IsPGroup 3 (Subgroup.centralizer (B : Set Λ))) (hR2 : IsPGroup 2 R)
    (hBR : B ≤ Subgroup.normalizer (R : Set Λ))
    (hmax : ∀ X : Subgroup Λ, IsPGroup 2 X → B ≤ Subgroup.normalizer (X : Set Λ) → R ≤ X →
      X ≤ R)
    (hBR' : B ≤ Subgroup.normalizer (R' : Set Λ)) (hcard : Nat.card R' = Nat.card R)
    (h3 : ¬ 3 ∣ Nat.card (R ⊔ R' : Subgroup Λ)) : R' = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := R ⊔ R' with hY
  have hBY : B ≤ Subgroup.normalizer (Y : Set Λ) := Sec14.le_normalizer_sup hBR hBR'
  set φ := conjHom hBY with hφ
  have hRY : R ≤ Y := le_sup_left
  have hR'Y : R' ≤ Y := le_sup_right
  have hR2' : IsPGroup 2 (R.subgroupOf Y) :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm
  obtain ⟨P₁, hRP₁, hP₁⟩ :=
    CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_containing_of_coprime 3 2 hB3 h3 φ
      (R.subgroupOf Y) hR2' (map_conjHom_subgroupOf hBY hBR)
  have hP₁R : ((P₁ : Subgroup Y)).map Y.subtype ≤ R := by
    refine hmax _ (P₁.isPGroup'.map _) ?_ ?_
    · intro b hb
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := hx
      have h1 := hP₁ ⟨b, hb⟩
      have hy' : conjHom hBY ⟨b, hb⟩ y ∈ (P₁ : Subgroup Y) := by
        rw [← h1]
        exact Subgroup.mem_map_of_mem _ hy
      exact ⟨_, hy', rfl⟩
    · intro r hr
      exact ⟨⟨r, hRY hr⟩, hRP₁ (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
  have hcardR : Nat.card (R.subgroupOf Y) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRY).toEquiv
  have hcardR' : Nat.card (R'.subgroupOf Y) = Nat.card R' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR'Y).toEquiv
  have hP₁eq : (P₁ : Subgroup Y) = R.subgroupOf Y := by
    refine (Subgroup.eq_of_le_of_card_ge hRP₁ ?_).symm
    rw [hcardR, ← Subgroup.card_map_of_injective Y.subtype_injective]
    exact Subgroup.card_le_of_le hP₁R
  set P₂ : Sylow 2 Y := Sylow.ofCard (R'.subgroupOf Y) (by
    rw [hcardR', hcard, ← hcardR, ← hP₁eq, Sylow.card_eq_multiplicity]) with hP₂
  have hP₂inv : ∀ b : B, ((P₂ : Subgroup Y)).map (φ b).toMonoidHom = P₂ := fun b =>
    map_conjHom_subgroupOf hBY hBR' b
  obtain ⟨y, hyP, hyfix⟩ :=
    CFSG.OrderReductions.FixedConjugator.invariant_sylows_conjugate_of_coprime 3 2 hB3 h3 φ P₁ P₂
      hP₁ hP₂inv
  have hyC : (y : Λ) ∈ Subgroup.centralizer (B : Set Λ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := congrArg Subtype.val (hyfix ⟨b, hb⟩)
    rw [hφ, conjHom_apply_coe] at h1
    calc b * (y : Λ) = b * y * b⁻¹ * b := by group
      _ = y * b := by rw [h1]
  have hy1 : y = 1 := by
    obtain ⟨k, hk⟩ := hC ⟨y, hyC⟩
    have hk' : y ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h1 : orderOf y ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf y ∣ Nat.card Y := orderOf_dvd_natCard y
    have hcop : Nat.Coprime (3 ^ k) (Nat.card Y) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    have h3' : orderOf y ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one hcop]
      exact Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3')
  rw [hy1, map_one] at hyP
  have hPP : (P₁ : Subgroup Y) = (P₂ : Subgroup Y) := by
    rw [← hyP]
    exact (Subgroup.map_id _).symm
  rw [hP₁eq] at hPP
  have h' : R'.subgroupOf Y = R.subgroupOf Y := hPP.symm
  rw [← Subgroup.map_subgroupOf_eq_of_le hR'Y, h', Subgroup.map_subgroupOf_eq_of_le hRY]

end Coprime

variable {G : Type} [Group G] [Finite G] {A L Y₀ : Subgroup G} {c : G}

theorem three_dvd_of_centralizer [(kerAO2 A Y₀).Normal] {T : Subgroup G} (hTY : T ≤ Y₀) {w : G}
    (hwY : w ∈ Y₀) {B : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)} (hB3 : IsPGroup 3 B)
    (hC : IsPGroup 3 (Subgroup.centralizer (B : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))))
    (hT2 : IsPGroup 2 (Proof17Res6.kimg Y₀ T))
    (hB : B ≤ Subgroup.normalizer (Proof17Res6.kimg Y₀ T : Set _))
    (hB' : B ≤ Subgroup.normalizer
      (Proof17Res6.kimg Y₀ (T.map (MulAut.conj w).toMonoidHom) : Set _))
    (hmax : ∀ X : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀), IsPGroup 2 X →
      B ≤ Subgroup.normalizer (X : Set _) → Proof17Res6.kimg Y₀ T ≤ X →
        X ≤ Proof17Res6.kimg Y₀ T)
    (hne : imgY0 A Y₀ (T.map (MulAut.conj w).toMonoidHom) ≠ imgY0 A Y₀ T) :
    3 ∣ Nat.card ↥(imgY0 A Y₀ T ⊔ imgY0 A Y₀ (T.map (MulAut.conj w).toMonoidHom)) := by
  set T' := T.map (MulAut.conj w).toMonoidHom with hT'
  have hT'Y : T' ≤ Y₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hwY (hTY hx)) (inv_mem hwY)
  by_contra h3
  rw [← Proof1712.imgY0_sup (hTY.trans le_sup_right) (hT'Y.trans le_sup_right),
    Proof17Res6.card_imgY0_eq_card_kimg (sup_le hTY hT'Y), Proof17Res6.kimg_sup hTY hT'Y] at h3
  have hcard : Nat.card (Proof17Res6.kimg Y₀ T') = Nat.card (Proof17Res6.kimg Y₀ T) := by
    rw [hT']
    exact Proof17Res6.card_kimg_map_conj hTY ⟨w, hwY⟩
  have heq := eq_of_not_three_dvd hB3 hC hT2 hB hmax hB' hcard h3
  exact hne (Proof17Res6.imgY0_eq_of_kimg_eq hT'Y hTY heq)

theorem isoLThreePi_of_mulEquiv {X X' : Type} [Group X] [Group X'] {p e : ℕ} [Fact p.Prime]
    (φ : X' ≃* X) (h : Sec4.IsoLThreePi X p e) : Sec4.IsoLThreePi X' p e := by
  rcases h with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
  · exact Or.inl ⟨hq, ⟨φ.trans ψ⟩⟩
  · exact Or.inr ⟨hq, ⟨φ.trans ψ⟩⟩

theorem exists_l3Pic
    (h1715 : Item1715) (h135 : Item135) (h138 : Item138N)
    {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G} (h : Sec17Y1 G A c L Y₀ Y₁ S p P)
    (hΩ : omegaA A = {Subgroup.zpowers c})
    (hL3 : ∃ (q : ℕ) (_ : Fact q.Prime), 3 < q ∧
      Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) q 1) :
    Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ ∧
      ∃ (q : ℕ) (_ : Fact q.Prime), 3 < q ∧ q % 9 ≠ 1 ∧ q % 9 ≠ 8 ∧
        Sec4.IsoLThreePi (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) q 1 := by
  have hs := h.toSec17Std
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    rcases h1715 G A c L Y₀ hs with ⟨-, hY, -, -⟩ | ⟨-, -, -, -, hT⟩
    · exact hY
    · exfalso
      have h3 := hT.1
      rw [hΩ, Set.ncard_singleton] at h3
      omega
  refine ⟨hY, ?_⟩
  obtain ⟨q, hq, hq3, hiso⟩ := hL3
  have hL3' : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := ⟨q, 1, hq, le_rfl, hiso⟩
  have h27L := claim1721SylL3_of h1715 h138 G A c L Y₀ Y₁ S p P h hL3'
  have h27 : ¬ 27 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := fun h27 =>
    h27L (h27.trans (Subgroup.card_quotient_dvd_card _))
  obtain ⟨h91, h98⟩ := Proof17Res2.not_modNine_of_not_dvd le_rfl hiso h27
  rw [pow_one] at h91 h98
  have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    have h9 := Sec13.Item138Proof.factorization_card_three_eq_two le_rfl hiso (by
      rw [pow_one]; omega)
    rw [← Finite.one_lt_card_iff_nontrivial]
    by_contra hle
    have hpos : 0 < Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := Nat.card_pos
    have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 1 := by omega
    rw [h1] at h9
    simp at h9
  have hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
    Proof1515.theta_eq_pCore_two_of_multFree (h135 G A c L hs.toSec13Data hs.hypS_or_hypT)
      ⟨MulEquiv.refl _⟩ (Proof1515.multFree_of_isLThreePi hL3')
  obtain ⟨e⟩ := Proof17Res6.nonempty_quot_equiv_of_theta hs.le_y0 hY hθ (MulEquiv.refl _)
  exact ⟨q, hq, hq3, h91, h98, isoLThreePi_of_mulEquiv e hiso⟩

theorem isPGroup_centralizer_of_l3 (hA : KS17L3AutCent) {q : ℕ} [Fact q.Prime] (hq3 : 3 < q)
    (h91 : q % 9 ≠ 1) (h98 : q % 9 ≠ 8) (hiso : Sec4.IsoLThreePi (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) q 1)
    {B : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)} (hB9 : Nat.card B = 9) :
    IsPGroup 3 (Subgroup.centralizer (B : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) := by
  rw [centralizer_eq_of_autCent hA hq3 hiso h91 h98 hB9]
  exact IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)

end Proof17Res7

theorem claim1718QuotOneL3_of_autCent
    (hA : KS17L3AutCent) (h1715 : Item1715) (h135 : Item135)
    (h142 : Concl142S14) (h9 : CardInfNineS17) (h138 : Item138N) : Claim1718QuotOneL3 := by
  intro G _ _ A c L Y₀ Y₁ S p P h hΩ hL3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := h.toSec17Std
  have := kerAO2_normal h.le_normalizer_y0
  obtain ⟨hY, q, hq, hq3, h91, h98, hiso⟩ := Proof17Res7.exists_l3Pic h1715 h135 h138 h hΩ hL3
  have h9' := h9 G A c L Y₀ hs
  have hLsurj := Proof17Res6.exists_mem_L_mk_eq hs.le_y0 hY
  have hAnorm := Proof17Res6.le_normalizer_of_inf hs h9'
  have hB9 := Proof17Res6.card_kimg_inf hs h9'
  have h142' := h142 G A c L hs.toSec14Std
  have hC := Proof17Res7.isPGroup_centralizer_of_l3 hA hq3 h91 h98 hiso hB9
  have hB3 : IsPGroup 3 (Proof17Res6.kimg Y₀ (A ⊓ L)) := IsPGroup.of_card (n := 2) (by
    rw [hB9]; norm_num)
  intro w hw hne
  set T := S ⊓ Y₀ with hT
  set T' := T.map (MulAut.conj w).toMonoidHom with hT'
  obtain ⟨hwA, hwY⟩ := Subgroup.mem_inf.mp hw
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    Late.le_normalizer_inf h.mem_qStar_two.prop.1.1.1.2.2 h.le_normalizer_y0
  have hAT' : A ≤ Subgroup.normalizer (T' : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := hx
    have ha' : w⁻¹ * a * w ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hwA) a).mp ha
      simpa using this
    have hat : (w⁻¹ * a * w) * t * (w⁻¹ * a * w)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hAT ha') t).mp ht
    refine ⟨(w⁻¹ * a * w) * t * (w⁻¹ * a * w)⁻¹, hat, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hB := Proof17Res6.kimg_le_normalizer_kimg (Y₀ := Y₀) ((inf_le_left : A ⊓ L ≤ A).trans hAT)
  have hB' := Proof17Res6.kimg_le_normalizer_kimg (Y₀ := Y₀)
    ((inf_le_left : A ⊓ L ≤ A).trans hAT')
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hT2 : IsPGroup 2 (Proof17Res6.kimg Y₀ T) := ((hS2.to_le inf_le_left).comap_subtype).map _
  exact Proof17Res7.three_dvd_of_centralizer inf_le_right hwY hB3 hC hT2 hB hB'
    (fun X hX2 hBX hTX => Proof17Res6.le_kimg_of_le h h142' hLsurj hAnorm hX2 hBX hTX) hne

end CFSG.RankThree.PartTwo.Sec17
