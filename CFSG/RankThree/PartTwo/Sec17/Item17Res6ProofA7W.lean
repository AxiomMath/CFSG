module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofA7S
public import CFSG.RankThree.PartTwo.Sec17.Item17Res4ProofItem1717
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 Equiv
open CFSG.RankThree.PartTwo.KFacts.KP2

namespace Proof17Res6

theorem rFour_not_normalizes : (∀ n : Fin 4, rFour * vOneF 1 * rFour⁻¹ ≠ vOneF n) ∧
    (∀ n : Fin 4, rFour * vTwoF 1 * rFour⁻¹ ≠ vTwoF n) := by
  decide +kernel

theorem rFour_conj_eNineF : ∀ i j : Fin 3, ∃ i' j' : Fin 3,
    rFour * eNineF i j * rFour⁻¹ = eNineF i' j' := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {A L Y₀ : Subgroup G}
  {φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 7)} {g : Perm (Fin 7)} {c : G}

theorem cimg_eq_of_invariant (hP : A7Pic A L Y₀ φ g) {X : Subgroup G} (hXY : X ≤ Y₀)
    (hAX : A ⊓ L ≤ Subgroup.normalizer (X : Set G)) (hX3 : ¬ 3 ∣ Nat.card X)
    (hX0 : cimgSeven Y₀ φ g X ≠ ⊥) :
    cimgSeven Y₀ φ g X = vOne ∨ cimgSeven Y₀ φ g X = vTwo := by
  have hER := eNine_le_normalizer_cimgSeven hP hAX
  rcases le_vOne_or_le_vTwo (not_three_dvd_card_cimgSeven hXY hX3) (hER cOne_mem_eNine)
      (hER cTwo_mem_eNine) with h1 | h1
  · exact Or.inl (vF_irreducible (Or.inl rfl) h1 hER hX0)
  · exact Or.inr (vF_irreducible (Or.inr rfl) h1 hER hX0)

omit [Finite G] in
theorem vF_one_mem : vOneF 1 ∈ vOne ∧ vTwoF 1 ∈ vTwo := ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩

omit [Finite G] in
theorem three_dvd_card_sup [(kerAO2 A Y₀).Normal] {X X' : Subgroup G} (hX : X ≤ Y₀)
    (hX' : X' ≤ Y₀) {x z : ↥Y₀} (hxJ : (x : G) ∈ X ⊔ X') (hzJ : (z : G) ∈ X ⊔ X')
    (hxe : g * projSeven Y₀ φ x * g⁻¹ = vOneF 1) (hze : g * projSeven Y₀ φ z * g⁻¹ = vTwoF 1) :
    3 ∣ Nat.card ↥(imgY0 A Y₀ X ⊔ imgY0 A Y₀ X') := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := projSeven Y₀ φ with hπ
  set κ : ↥Y₀ →* ↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀ :=
    (QuotientGroup.mk' (kerAO2 A Y₀)).comp (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀))
    with hκ
  obtain ⟨h6, h2⟩ := check_vOne_vTwo 1 1 (by decide) (by decide)
  set v : ↥Y₀ := (x * z) ^ 2 with hv
  have hve : g * π v * g⁻¹ = (vOneF 1 * vTwoF 1) ^ 2 := by
    rw [hv, ← hxe, ← hze, map_pow, map_mul, ← conj_pow]
    group
  have hvJ : (v : G) ∈ X ⊔ X' := by
    rw [hv]
    exact pow_mem (mul_mem hxJ hzJ) 2
  have hvbJ : κ v ∈ imgY0 A Y₀ X ⊔ imgY0 A Y₀ X' := by
    rw [← Proof1712.imgY0_sup (hX.trans le_sup_right) (hX'.trans le_sup_right)]
    exact (mem_imgY0_iff (sup_le hX hX') _).mpr ⟨v, hvJ, rfl⟩
  have hπv3 : π (v ^ 3) = π 1 := by
    have h' : g * π (v ^ 3) * g⁻¹ = 1 := by
      rw [map_pow, ← conj_pow, hve, ← pow_mul]
      exact h6
    rw [map_one]
    exact conj_eq_one_iff.mp h'
  have hvb3 : κ v ^ 3 = 1 := by
    rw [← map_pow, ← map_one κ]
    exact (mk_inclusion_eq_iff (v ^ 3) 1).mpr hπv3
  have hvb1 : κ v ≠ 1 := by
    intro h1
    rw [← map_one κ] at h1
    have h1' := (mk_inclusion_eq_iff (φ := φ) v 1).mp h1
    apply h2
    rw [← hve, h1', map_one, mul_one, mul_inv_cancel]
  rw [← orderOf_eq_prime hvb3 hvb1]
  exact Subgroup.orderOf_dvd_natCard _ hvbJ

theorem three_dvd_of_a7 [(kerAO2 A Y₀).Normal] {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A7Pic A L Y₀ φ g)
    (h142 : Concl142 A (lB A)) {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀)
    (hne : imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom) ≠ imgY0 A Y₀ (S ⊓ Y₀)) :
    3 ∣ Nat.card ↥(imgY0 A Y₀ (S ⊓ Y₀) ⊔
      imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := projSeven Y₀ φ with hπ
  set T := S ⊓ Y₀ with hT
  set T' := T.map (MulAut.conj w).toMonoidHom with hT'
  obtain ⟨hwA, hwY⟩ := Subgroup.mem_inf.mp hw
  have hTY : T ≤ Y₀ := inf_le_right
  have hT'Y : T' ≤ Y₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hwY (hTY hx)) (inv_mem hwY)
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hT3 : ¬ 3 ∣ Nat.card T := Proof171.not_three_dvd_of_isPGroup_two (hS2.to_le inf_le_left)
  have hT'3 : ¬ 3 ∣ Nat.card T' := by
    rw [hT', Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact hT3
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
  have hK := cimg_eq h hP h142
  have hT'0 : cimgSeven Y₀ φ g T' ≠ ⊥ := by
    intro h0
    obtain ⟨u, huT, hue⟩ : ∃ u : ↥Y₀, (u : G) ∈ T ∧ g * π u * g⁻¹ ≠ 1 := by
      rcases hK with hK | hK
      · obtain ⟨u, huT, hue⟩ := mem_cimgSeven.mp (hK ▸ vF_one_mem.1)
        exact ⟨u, huT, by rw [hue]; exact vF_ne_one.1⟩
      · obtain ⟨u, huT, hue⟩ := mem_cimgSeven.mp (hK ▸ vF_one_mem.2)
        exact ⟨u, huT, by rw [hue]; exact vF_ne_one.2⟩
    have huw : g * π (⟨w, hwY⟩ * u * ⟨w, hwY⟩⁻¹) * g⁻¹ ∈ cimgSeven Y₀ φ g T' :=
      mem_cimgSeven.mpr ⟨_, ⟨u, huT, by simp [MulAut.conj_apply]⟩, rfl⟩
    rw [h0, Subgroup.mem_bot, conj_eq_one_iff, map_mul, map_mul, map_inv] at huw
    apply hue
    have h1 : π u = 1 := by
      have := congrArg (fun z => (π ⟨w, hwY⟩)⁻¹ * z * π ⟨w, hwY⟩) huw
      simpa [mul_assoc] using this
    rw [h1, mul_one, mul_inv_cancel]
  have hK' := cimg_eq_of_invariant hP hT'Y (inf_le_left.trans hAT') hT'3 hT'0
  have hdiff : cimgSeven Y₀ φ g T ≠ cimgSeven Y₀ φ g T' := by
    intro he
    exact hne (le_antisymm (imgY0_le_of_cimgSeven_le hT'Y he.symm.le)
      (imgY0_le_of_cimgSeven_le hTY he.le))
  have hJ : ∀ V : Subgroup (Perm (Fin 7)), (V = vOne ∨ V = vTwo) →
      (cimgSeven Y₀ φ g T = V ∨ cimgSeven Y₀ φ g T' = V) → ∀ v ∈ V,
      ∃ x : ↥Y₀, (x : G) ∈ T ⊔ T' ∧ g * π x * g⁻¹ = v := by
    intro V _ hV v hv
    rcases hV with hV | hV
    · obtain ⟨x, hx, hxe⟩ := mem_cimgSeven.mp (hV ▸ hv)
      exact ⟨x, Subgroup.mem_sup_left hx, hxe⟩
    · obtain ⟨x, hx, hxe⟩ := mem_cimgSeven.mp (hV ▸ hv)
      exact ⟨x, Subgroup.mem_sup_right hx, hxe⟩
  have h1 : cimgSeven Y₀ φ g T = vOne ∨ cimgSeven Y₀ φ g T' = vOne := by
    rcases hK with hK | hK
    · exact Or.inl hK
    · rcases hK' with hK' | hK'
      · exact Or.inr hK'
      · exact absurd (hK.trans hK'.symm) hdiff
  have h2 : cimgSeven Y₀ φ g T = vTwo ∨ cimgSeven Y₀ φ g T' = vTwo := by
    rcases hK with hK | hK
    · rcases hK' with hK' | hK'
      · exact absurd (hK.trans hK'.symm) hdiff
      · exact Or.inr hK'
    · exact Or.inl hK
  obtain ⟨x, hxJ, hxe⟩ := hJ vOne (Or.inl rfl) h1 _ vF_one_mem.1
  obtain ⟨z, hzJ, hze⟩ := hJ vTwo (Or.inr rfl) h2 _ vF_one_mem.2
  exact three_dvd_card_sup hTY hT'Y hxJ hzJ hxe hze

theorem exists_w_of_a7 {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A7Pic A L Y₀ φ g)
    (h142 : Concl142 A (lB A)) :
    ∃ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
      w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
        w ∉ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := projSeven Y₀ φ with hπ
  set κL : ↥L →* Perm (Fin 7) := π.comp (Subgroup.inclusion hP.L_le) with hκL
  have hκker : IsPGroup 2 κL.ker := by
    rw [hκL, ← MonoidHom.comap_ker]
    exact (projSeven_ker_isPGroup Y₀ φ).comap_of_injective _
      (Subgroup.inclusion_injective hP.L_le)
  set B : Subgroup ↥L := (A ⊓ L).subgroupOf L with hB
  have hB3 : IsPGroup 3 B :=
    (h.toSec17Std.isE27.isPGroup.to_le inf_le_left).comap_subtype
  have hBmap : B.map L.subtype = A ⊓ L := by
    rw [hB, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have hBmem : ∀ x, x ∈ B.map κL ↔ g * x * g⁻¹ ∈ eNine := by
    intro x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hP.mem _ (Subgroup.mem_subgroupOf.mp hb)
    · intro hx
      obtain ⟨a, ha, hae⟩ := hP.surj _ hx
      refine ⟨⟨a, ha.2⟩, Subgroup.mem_subgroupOf.mpr ha, ?_⟩
      have h2 : projSeven Y₀ φ a = x := by
        have := congrArg (fun z => g⁻¹ * z * g) hae
        simpa [mul_assoc] using this
      exact h2
  have hBc : ∀ x ∈ B.map κL, ∀ z ∈ B.map κL, x * z = z * x := by
    intro x hx z hz
    obtain ⟨i, j, hij⟩ := (hBmem x).mp hx
    obtain ⟨k, l, hkl⟩ := (hBmem z).mp hz
    have h1 := eNineF_comm i j k l
    rw [← hij, ← hkl] at h1
    have := congrArg (fun u => g⁻¹ * u * g) h1
    simpa [mul_assoc] using this
  set h' := g⁻¹ * rFour * g with hh'
  have hh'A : h' ∈ alternatingGroup (Fin 7) := by
    have := (alternatingGroup.normal (α := Fin 7)).conj_mem rFour rFour_spec.1 g⁻¹
    simpa [hh'] using this
  have hh'range : h' ∈ κL.range := by
    obtain ⟨l, hl, hle⟩ := hP.L_surj h' hh'A
    exact ⟨⟨l, hl⟩, hle⟩
  have hh'N : h' ∈ Subgroup.normalizer ((B.map κL : Subgroup (Perm (Fin 7))) :
      Set (Perm (Fin 7))) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    refine (hBmem _).mpr ?_
    obtain ⟨i, j, hij⟩ := (hBmem x).mp hx
    obtain ⟨i', j', h1⟩ := rFour_conj_eNineF i j
    refine ⟨i', j', ?_⟩
    rw [← h1, ← hij, hh']
    group
  obtain ⟨y, hyN, hyκ⟩ := Step163Alt.exists_normalizer_lift κL hκker hB3 hBc hh'range hh'N
  set w : G := (y : G) with hw
  have hwL : w ∈ L := y.2
  have hwY : w ∈ Y₀ := hP.L_le hwL
  have hwAL : w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    have := Subgroup.le_normalizer_map L.subtype ⟨y, hyN, rfl⟩
    rwa [hBmap] at this
  refine ⟨w, Subgroup.mem_inf.mpr ⟨hP.L_norm w hwL hwAL, hwY⟩, hwAL, fun hwS => ?_⟩
  set τ := g * π ⟨w, hwY⟩ * g⁻¹ with hτ
  have hτconj : ∀ x ∈ eNine, τ * x * τ⁻¹ = rFour * x * rFour⁻¹ := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hP.surj x hx
    have hb : (⟨a, ha.2⟩ : ↥L) ∈ B := Subgroup.mem_subgroupOf.mpr ha
    have h1 := hyκ _ hb
    have e1 : κL (y * ⟨a, ha.2⟩ * y⁻¹) = π ⟨w, hwY⟩ * π a * (π ⟨w, hwY⟩)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      rfl
    have e2 : κL ⟨a, ha.2⟩ = π a := rfl
    rw [e1, e2, hh'] at h1
    rw [hτ]
    calc g * π ⟨w, hwY⟩ * g⁻¹ * (g * π a * g⁻¹) * (g * π ⟨w, hwY⟩ * g⁻¹)⁻¹
        = g * (π ⟨w, hwY⟩ * π a * (π ⟨w, hwY⟩)⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * rFour * g * π a * (g⁻¹ * rFour * g)⁻¹) * g⁻¹ := by rw [h1]
      _ = rFour * (g * π a * g⁻¹) * rFour⁻¹ := by group
  set u := rFour⁻¹ * τ with hu
  have hucomm : ∀ x ∈ eNine, x * u = u * x := by
    intro x hx
    have h1 := hτconj x hx
    calc x * u = rFour⁻¹ * (rFour * x * rFour⁻¹) * τ := by rw [hu]; group
      _ = rFour⁻¹ * (τ * x * τ⁻¹) * τ := by rw [h1]
      _ = u * x := by rw [hu]; group
  have huE : u ∈ eNine := by
    by_contra hne
    exact forall_not_of_card_filter_eq_zero card_filter_centralizer_eNine u
      ⟨(hucomm cOne cOne_mem_eNine).symm, (hucomm cTwo cTwo_mem_eNine).symm, hne⟩
  have hτK : ∀ z ∈ cimgSeven Y₀ φ g (S ⊓ Y₀), τ * z * τ⁻¹ ∈ cimgSeven Y₀ φ g (S ⊓ Y₀) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_cimgSeven.mp hz
    have hyx : w * x * w⁻¹ ∈ S ⊓ Y₀ := (Subgroup.mem_normalizer_iff.mp hwS x).mp hx
    refine mem_cimgSeven.mpr ⟨⟨w, hwY⟩ * x * ⟨w, hwY⟩⁻¹, by simpa using hyx, ?_⟩
    rw [map_mul, map_mul, map_inv, hτ, hπ]
    group
  have hτr : τ = rFour * u := by rw [hu]; group
  rcases cimg_eq h hP h142 with hK | hK
  · have hv' := eNine_conj_mem_vOne (inv_mem huE) vF_one_mem.1
    have hm := hτK _ (by rw [hK]; exact hv')
    rw [hK] at hm
    obtain ⟨n, hn⟩ := hm
    apply rFour_not_normalizes.1 n
    rw [← hn, hτr]
    group
  · have hv' := eNine_conj_mem_vTwo (inv_mem huE) vF_one_mem.2
    have hm := hτK _ (by rw [hK]; exact hv')
    rw [hK] at hm
    obtain ⟨n, hn⟩ := hm
    apply rFour_not_normalizes.2 n
    rw [← hn, hτr]
    group

end Proof17Res6

@[expose] noncomputable def Item1717OneNA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (h : Sec17Y1 G A c L Y₀ Y₁ S p P),
    omegaA A = {Subgroup.zpowers c} →
    IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    letI := kerAO2_normal h.le_normalizer_y0
    S = (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) ∧
      (((IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
            Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) ∧
          ∃ (a : G) (ha : a ∈ A), a ∈ L ∧ a ≠ 1 ∧
            imgY0 A Y₀ (S ⊓ Y₀) = oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha)) ∨
        (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
          (CFSG.Assembly.IsElemAbelian 2 (imgY0 A Y₀ (S ⊓ Y₀)) ∧
            Nat.card (imgY0 A Y₀ (S ⊓ Y₀)) = 16) ∧
          ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A), Subgroup.closure {a, b} = A ⊓ L ∧
            imgY0 A Y₀ (S ⊓ Y₀) =
              oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊔ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) ∧
            oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊓ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) = ⊥) ∨
        (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
          (∃ T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)),
            Nonempty (↥(imgY0 A Y₀ (S ⊓ Y₀)) ≃*
              ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))))) ∧
          ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A) (d : G),
            Subgroup.closure {a, b} = A ⊓ L ∧ d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn L d ∧
            imgY0 A Y₀ (S ⊓ Y₀) =
              oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊔ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) ⊔
                imgY0 A Y₀ (S ⊓ Y₀ ⊓ Subgroup.centralizer {d})))

@[expose] noncomputable def Claim1718QuotOneNA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (h : Sec17Y1 G A c L Y₀ Y₁ S p P),
    omegaA A = {Subgroup.zpowers c} →
    IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    letI := kerAO2_normal h.le_normalizer_y0
    ∀ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
      imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom) ≠ imgY0 A Y₀ (S ⊓ Y₀) →
        3 ∣ Nat.card ↥(imgY0 A Y₀ (S ⊓ Y₀) ⊔
          imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom))

theorem claim1718QuotOneNA7_of_one (h : Claim1718QuotOne) : Claim1718QuotOneNA7 :=
  fun G _ _ A c L Y₀ Y₁ S p P hY hΩ _ => h G A c L Y₀ Y₁ S p P hY hΩ

section Provers

theorem exists_a7Pic_of (h1715 : Item1715) (h135 : Item135) (h9 : CardInfNineS17) {G : Type}
    [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (hs : Sec17Std G A c L Y₀)
    (hΩ : omegaA A = {Subgroup.zpowers c})
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) :
    ∃ (φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 7)) (g : Perm (Fin 7)),
      Proof17Res6.A7Pic A L Y₀ φ g := by
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    rcases h1715 G A c L Y₀ hs with ⟨-, hY, -⟩ | ⟨-, -, -, -, hT⟩
    · exact hY
    · exfalso
      have h3 := hT.1
      rw [hΩ, Set.ncard_singleton] at h3
      omega
  exact Proof17Res6.exists_a7Pic h135 hs hY φL (h9 G A c L Y₀ hs)

theorem claim1718QuotOne_of (hN : Claim1718QuotOneNA7) (h1715 : Item1715) (h135 : Item135)
    (h142 : Concl142S14) (h9 : CardInfNineS17) : Claim1718QuotOne := by
  intro G _ _ A c L Y₀ Y₁ S p P h hΩ
  by_cases hA7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
  · obtain ⟨φL⟩ := hA7
    have hs := h.toSec17Std
    obtain ⟨φ, g, hP⟩ := exists_a7Pic_of h1715 h135 h9 hs hΩ φL
    have := kerAO2_normal h.le_normalizer_y0
    exact fun w hw hne => Proof17Res6.three_dvd_of_a7 h hP (h142 G A c L hs.toSec14Std) hw hne
  · exact hN G A c L Y₀ Y₁ S p P h hΩ (not_nonempty_iff.mp hA7)

theorem claim1718Quot_of_nA7 (hN : Claim1718QuotOneNA7) (h1715 : Item1715) (h135 : Item135)
    (h142 : Concl142S14) (h9 : CardInfNineS17) : Claim1718Quot :=
  claim1718Quot_of_one (claim1718QuotOne_of hN h1715 h135 h142 h9) h1715 h142

end Provers

end CFSG.RankThree.PartTwo.Sec17
