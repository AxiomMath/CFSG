module

public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b
open scoped commutatorElement

section Helpers

variable {Q : Type*} [Group Q]

theorem exists_pow_mem_of_pow_mem_sup {X N : Subgroup Q} [X.Normal] (hN : IsPGroup 2 N)
    {q : Q} {k : ℕ} (hq : q ^ 2 ^ k ∈ X ⊔ N) : ∃ j : ℕ, q ^ 2 ^ j ∈ X := by
  obtain ⟨x, hx, n, hn, hxn⟩ := Subgroup.mem_sup_of_normal_left.mp hq
  obtain ⟨m, hm⟩ := hN ⟨n, hn⟩
  have hnm : n ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  refine ⟨k + m, ?_⟩
  have e : q ^ 2 ^ (k + m) = (q ^ 2 ^ k) ^ 2 ^ m := by rw [← pow_mul, ← pow_add]
  rw [e, ← hxn, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff x).mpr hx, one_mul, ← QuotientGroup.mk_pow, hnm,
    QuotientGroup.mk_one]

theorem exists_pow_mem_of_mem_pCore [Finite Q] {M : Subgroup Q} [M.Normal]
    (h : ∀ q : Q, (q : Q ⧸ M) ∈ CFSG.Open.pCore 2 (Q ⧸ M)) (q : Q) :
    ∃ k : ℕ, q ^ 2 ^ k ∈ M := by
  have hP : IsPGroup 2 (CFSG.Open.pCore 2 (Q ⧸ M)) :=
    CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨k, hk⟩ := hP ⟨(q : Q ⧸ M), h q⟩
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  simpa using congrArg Subtype.val hk

theorem conjClosure_top_normal (B : Subgroup Q) : (conjClosure B ⊤).Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_conjClosure B ⊤))

theorem perfect_of_isComponent {P : Type*} [Group P] {L : Subgroup P} (hL : CFSG.IsComponent L) :
    ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.mp hL.1.1

theorem commutatorElement_mem_of_normal {N : Subgroup Q} [N.Normal] {g b : Q} (hb : b ∈ N) :
    ⁅g, b⁆ ∈ N := by
  have h1 : ⁅g, b⁆ = (g * b * g⁻¹) * b⁻¹ := by simp only [commutatorElement_def]
  rw [h1]
  exact N.mul_mem (Subgroup.Normal.conj_mem inferInstance b hb g) (N.inv_mem hb)

end Helpers

section EOne

variable {Q : Type*} [Group Q] [Finite Q]

theorem twoResidual_le_conjClosure_of_eOne {B : Subgroup Q} (h : EOne Q B) :
    twoResidual (⊤ : Subgroup Q) ≤ conjClosure B ⊤ := by
  obtain ⟨p, -, -, ha, -, hb2, -⟩ := h
  have : (conjClosure B ⊤).Normal := conjClosure_top_normal B
  set N := CFSG.Open.pCore 2 Q with hN
  set X := conjClosure B ⊤ with hX
  have hN2 : IsPGroup 2 N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hXbar : (X.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  have hB : barO2 Q B ≤ X.map (QuotientGroup.mk' N) :=
    Subgroup.map_mono (le_conjClosure B ⊤)
  have hP : CFSG.Open.pCore p (Q ⧸ N) ≤ X.map (QuotientGroup.mk' N) := by
    rw [hb2]
    exact (Subgroup.commutator_mono le_rfl hB).trans (Subgroup.commutator_le_right _ _)
  have hM : oTwoP Q p ≤ X ⊔ N := by
    intro m hm
    have hm' : (QuotientGroup.mk' N m) ∈ CFSG.Open.pCore p (Q ⧸ N) := hm
    obtain ⟨x, hx, hxm⟩ := hP hm'
    have hxN : x⁻¹ * m ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hxm]
      simp
    have : m = x * (x⁻¹ * m) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hxN)
  have h2 : ∀ y ∈ (⊤ : Subgroup Q), ∃ k : ℕ, y ^ 2 ^ k ∈ X := by
    intro y _
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_pCore (M := oTwoP Q p) (fun q => by
      have hq : q ∈ oTwoPTwo Q p := by rw [ha]; exact Subgroup.mem_top q
      exact hq) y
    exact exists_pow_mem_of_pow_mem_sup hN2 (hM hk)
  exact twoResidual_le_of_isTwoQuotient le_top
    (top_le_iff.mpr (Subgroup.normalizer_eq_top_iff.mpr inferInstance)) h2

end EOne

section ETwo

variable {Q : Type*} [Group Q] [Finite Q]

theorem twoResidual_le_conjClosure_of_eTwo {S B : Subgroup Q} (h : ETwo Q S B) :
    twoResidual (⊤ : Subgroup Q) ≤ conjClosure B ⊤ := by
  obtain ⟨-, ha2, ha3, L, hL, hlayer, hcase⟩ := h
  have : (conjClosure B ⊤).Normal := conjClosure_top_normal B
  set R := CFSG.solvableRadical Q with hR
  set X := conjClosure B ⊤ with hX
  have hRs : Group.IsSolvable R := A3.solvableRadical_isSolvable
  have hXbar : (X.map (QuotientGroup.mk' R)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective R)
  have hB : barRad Q B ≤ X.map (QuotientGroup.mk' R) :=
    Subgroup.map_mono (le_conjClosure B ⊤)
  have hLX : L ≤ X.map (QuotientGroup.mk' R) := by
    rcases hcase with h1 | ⟨h1, -⟩
    · calc L = ⁅L, barRad Q B⁆ := h1
        _ ≤ ⁅L, X.map (QuotientGroup.mk' R)⁆ := Subgroup.commutator_mono le_rfl hB
        _ ≤ X.map (QuotientGroup.mk' R) := Subgroup.commutator_le_right _ _
    · obtain ⟨b, hbB, hbN⟩ : ∃ b ∈ barRad Q B,
          b ∉ Subgroup.normalizer (L : Set (Q ⧸ R)) := by
        by_contra hcon
        refine h1 fun b hb => ?_
        by_contra hnb
        exact hcon ⟨b, hb, hnb⟩
      have hbX : b ∈ X.map (QuotientGroup.mk' R) := hB hbB
      have hL' : CFSG.IsComponent (conjSub b L) :=
        CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj b) hL
      have hne : conjSub b L ≠ L := fun h' =>
        hbN (conjSub_eq_iff_mem_normalizer.mp h')
      have hcomm : ⁅L, conjSub b L⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hL hL').resolve_left (Ne.symm hne)
      have hperf := perfect_of_isComponent hL
      rw [← hperf]
      refine Subgroup.commutator_le.mpr fun y hy z hz => ?_
      have hx : z⁻¹ ∈ L := L.inv_mem hz
      set v := b * z⁻¹ * b⁻¹ with hv
      have hvL' : v ∈ conjSub b L := mem_conjSub_of_mem hx
      have hyv : y * v = v * y := by
        have := Subgroup.commutator_mem_commutator hy hvL'
        rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
      set c := z * b * z⁻¹ * b⁻¹ with hc
      have hcX : c ∈ X.map (QuotientGroup.mk' R) := by
        have h1 : c = (z * b * z⁻¹) * b⁻¹ := rfl
        rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.Normal.conj_mem hXbar b hbX z) (Subgroup.inv_mem _ hbX)
      have hcv : c = z * v := by simp only [hc, hv]; group
      have hyc : ⁅y, c⁆ = ⁅y, z⁆ := by
        rw [hcv]
        have e1 : y * (z * v) * y⁻¹ * (z * v)⁻¹ = y * z * (v * y⁻¹ * v⁻¹) * z⁻¹ := by group
        have e2 : v * y⁻¹ * v⁻¹ = y⁻¹ := by
          have : v * y⁻¹ = y⁻¹ * v := by
            have := congrArg (fun w => y⁻¹ * w * y⁻¹) hyv
            simpa [mul_assoc] using this
          rw [this]; group
        simp only [commutatorElement_def]
        rw [e1, e2]
      rw [← hyc]
      exact commutatorElement_mem_of_normal hcX
  have hlayerX : CFSG.layer (Q ⧸ R) ≤ X.map (QuotientGroup.mk' R) := by
    rw [hlayer]
    refine iSup₂_le fun t _ x hx => ?_
    have hx' : t⁻¹ * x * t ∈ L := mem_conjSub_iff.mp hx
    have := hLX hx'
    have h2 := Subgroup.Normal.conj_mem hXbar _ this t
    simpa [mul_assoc] using h2
  have hoE : oInftyE Q ≤ X ⊔ R := by
    intro m hm
    have hm' : (QuotientGroup.mk' R m) ∈ CFSG.layer (Q ⧸ R) := hm
    obtain ⟨x, hx, hxm⟩ := hlayerX hm'
    have hxR : x⁻¹ * m ∈ R := by
      rw [← QuotientGroup.ker_mk' R, MonoidHom.mem_ker, map_mul, map_inv, hxm]
      simp
    have : m = x * (x⁻¹ * m) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hxR)
  have h2 : ∀ y ∈ (⊤ : Subgroup Q), ∃ k : ℕ, y ^ 2 ^ k ∈ X ⊔ R := by
    intro y _
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_pCore (M := oInftyE Q) (fun q => by
      rw [ha2]; exact Subgroup.mem_top _) y
    exact ⟨k, hoE hk⟩
  have hres : twoResidual (⊤ : Subgroup Q) ≤ X ⊔ R :=
    twoResidual_le_of_isTwoQuotient le_top
      (top_le_iff.mpr (Subgroup.normalizer_eq_top_iff.mpr inferInstance)) h2
  rw [ha3] at hres ⊢
  have hperfQ : ⁅perfectCore (⊤ : Subgroup Q), perfectCore (⊤ : Subgroup Q)⁆ =
      perfectCore (⊤ : Subgroup Q) := perfectCore_perfect _
  refine (le_perfectCore_of_perfect hres hperfQ).trans ?_
  exact perfectCore_le_of_sup_solvable le_sup_left Subgroup.normal_subgroupOf rfl hRs

end ETwo

section Ambient

variable {G : Type*} [Group G] [Finite G]

theorem twoResidual_le_conjClosure {H T A K : Subgroup G} (hK : IsEAny H T A K) :
    twoResidual K ≤ conjClosure A K := by
  obtain ⟨i, -, -, -, hcase⟩ := hK
  have hab : twoResidual (⊤ : Subgroup ↥K) ≤ conjClosure (A.subgroupOf K) ⊤ := by
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
    · exact twoResidual_le_conjClosure_of_eOne h
    · exact twoResidual_le_conjClosure_of_eTwo h
  set M : Subgroup ↥K := twoResidual (⊤ : Subgroup ↥K) with hM
  have hMnorm : Subgroup.normalizer (M : Set ↥K) = ⊤ := top_le_iff.mp (le_normalizer_twoResidual ⊤)
  have h1 : twoResidual K ≤ M.map K.subtype := by
    refine twoResidual_le_of_isTwoQuotient (Subgroup.map_subtype_le _) ?_ ?_
    · intro x hx
      exact Subgroup.le_normalizer_map K.subtype
        (Subgroup.mem_map_of_mem K.subtype (show (⟨x, hx⟩ : ↥K) ∈ Subgroup.normalizer (M : Set ↥K) from
          hMnorm ▸ Subgroup.mem_top _))
    · intro y hy
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup ↥K) ⟨y, hy⟩ (Subgroup.mem_top _)
      exact ⟨k, ⟨_, hk, by simp⟩⟩
  have h2 : (conjClosure (A.subgroupOf K) ⊤).map K.subtype ≤ conjClosure A K := by
    refine Subgroup.map_le_iff_le_comap.mpr (conjClosure_le fun h _ z hz => ?_)
    exact mem_conjClosure h.2 hz
  exact h1.trans ((Subgroup.map_mono hab).trans h2)

end Ambient

end E1

end CFSG.Quasithin
