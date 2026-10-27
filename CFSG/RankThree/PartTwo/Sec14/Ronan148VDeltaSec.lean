module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148VDelta
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VSection
import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofInner
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJRank
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4.Ronan148V (IsSec)

variable {G : Type} [Group G] [Finite G]

theorem not_isSolvable_j2 :
    ¬ Group.IsSolvable CFSG.Blueprint.NativeSporadic.J2 := by
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  rw [← IsSimpleGroup.comm_iff_isSolvable]
  intro hcomm
  have hc := KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15
  have htop : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro g
    exact hcomm g x
  have h1 := Subgroup.card_top (G := CFSG.Blueprint.NativeSporadic.J2)
  rw [← htop, hc, Subgroup.card_bot, KFacts.KS14.card_nativeJ2] at h1
  omega

theorem surjective_mk_comp_inclusion {X N : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    letI := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : N ≤ X ⊔ N)).mpr
      (sup_le hXN Subgroup.le_normalizer)
    Function.Surjective ((QuotientGroup.mk' (N.subgroupOf (X ⊔ N))).comp
      (Subgroup.inclusion (le_sup_left : X ≤ X ⊔ N))) := by
  letI := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : N ≤ X ⊔ N)).mpr
      (sup_le hXN Subgroup.le_normalizer)
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hy' : y ∈ ((X ⊔ N : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X N hXN] at hy'
  obtain ⟨x, hx, n, hn, rfl⟩ := hy'
  refine ⟨⟨x, hx⟩, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq]
  rw [Subgroup.mem_subgroupOf]
  simpa using hn

theorem not_isSec_j2_deltaQ
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) (h143 : Ronan148Q.Item143Q A (lB A))
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (haΩ : Subgroup.zpowers a ∉ omegaA A) :
    ¬ IsSec CFSG.Blueprint.NativeSporadic.J2
      ↥(delta A (lB A) (Subgroup.centralizer ({a} : Set G))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have : Finite CFSG.Blueprint.NativeSporadic.J2 :=
    Nat.finite_of_card_ne_zero (by rw [KFacts.KS14.card_nativeJ2]; norm_num)
  have hJc : Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800 := KFacts.KS14.card_nativeJ2
  have hJ3 : 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 := by rw [hJc]; norm_num
  have hJns := not_isSolvable_j2
  intro hsec
  obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A (piCompl 3)
  obtain ⟨-, hcase⟩ := h143 a haA ha1 haΩ Q hQ
  set N₁ := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hN₁def
  set N₂ := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hN₂def
  have hN₁ : ¬ 3 ∣ Nat.card N₁ :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hN₂ : ¬ 3 ∣ Nat.card N₂ :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hN₂C : N₂ ≤ Subgroup.centralizer ({a} : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  have hCN₁ : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (N₁ : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  rcases hcase with h1 | ⟨b, d, Lb, hbΩ, -, -, -, -, -, -, X, hX, hinv, hXcase⟩
  ·
    rw [h1] at hsec
    have hd := card_sup_dvd_card_mul (hN₂C.trans hCN₁)
    rw [sup_comm N₂ N₁] at hd
    have h3 := hJ3.trans (hsec.card_dvd.trans hd)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact hN₂ h
    · exact hN₁ h
  · have hXC : X ≤ Subgroup.centralizer ({a} : Set G) := by
      rcases hXcase with ⟨hXc, -, -⟩ | ⟨-, ⟨𝒳, h𝒳, -, rfl⟩, -⟩
      · exact le_centralizer_of_mem_thetaComponentsAt hXc
      · exact sSup_le fun K hK => le_centralizer_of_mem_thetaComponentsAt (h𝒳 hK)
    set D' := X ⊔ N₁ with hD'def
    have hXN' : N₂ ≤ Subgroup.normalizer (D' : Set G) := by
      rw [hD'def, sup_comm]
      exact (pPrimeCoreOf_le 3 _).trans (hinv.centralizer_le haA)
    have hΔ : delta A (lB A) (Subgroup.centralizer ({a} : Set G)) = N₂ ⊔ D' := by
      rw [hX, hD'def, sup_comm X N₁, sup_right_comm, sup_comm]
    rw [hΔ] at hsec
    have hD'le : D' ≤ N₂ ⊔ D' := le_sup_right
    have hnorm : (D'.subgroupOf (N₂ ⊔ D')).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hD'le).mpr
        (sup_le hXN' Subgroup.le_normalizer)
    have hidx : ¬ 3 ∣ (D'.subgroupOf (N₂ ⊔ D')).index := by
      have h1 := (D'.subgroupOf (N₂ ⊔ D')).index_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD'le).toEquiv] at h1
      have h2 := card_sup_dvd_card_mul hXN'
      rw [← h1] at h2
      have hpos : 0 < Nat.card D' := Nat.card_pos
      have h3 : (D'.subgroupOf (N₂ ⊔ D')).index ∣ Nat.card N₂ :=
        Nat.dvd_of_mul_dvd_mul_right hpos h2
      exact fun h => hN₂ (h.trans h3)
    have hsecD := Sec4.Ronan148V.IsSec.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hD'le)
      (hsec.of_index_not_dvd hJ3 hidx)
    have hDN₁ : D' ≤ Subgroup.normalizer (N₁ : Set G) :=
      sup_le (hXC.trans hCN₁) Subgroup.le_normalizer
    have hN₁le : N₁ ≤ D' := le_sup_right
    letI hnorm₁ : (N₁.subgroupOf D').Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN₁le).mpr hDN₁
    have hN₁' : ¬ 3 ∣ Nat.card (N₁.subgroupOf D') := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₁le).toEquiv]
    have hsecQ := hsecD.quotient_of_not_dvd hJ3 hN₁'
    have hsecX : IsSec CFSG.Blueprint.NativeSporadic.J2 ↥X :=
      hsecQ.of_surjective (surjective_mk_comp_inclusion (hXC.trans hCN₁))
    have hθs := (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).1
    have hsecθ := hsecX.quotient_of_isSolvable hJns (N := aschbacherSolvableCore 3 ↥X) hθs
    have hdvd := hsecθ.card_dvd
    rw [hJc] at hdvd
    rcases hXcase with ⟨-, hXeq, -⟩ | ⟨-, -, htype⟩
    ·
      set B := Subgroup.closure ({a, b} : Set G) with hBdef
      have hle0 : lB A B ≤ X :=
        calc lB A B ≤ lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) X := le_sup_left
          _ = X := hXeq.symm
      have hsurj : Function.Surjective ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)).comp
          (Subgroup.inclusion hle0)) := by
        intro q
        obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
        have hy' : y ∈ ((lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) X : Subgroup G) : Set G) :=
          hXeq ▸ hy
        rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
          (hle0.trans (le_normalizer_theta X))] at hy'
        obtain ⟨l, hl, t, ht, rfl⟩ := hy'
        refine ⟨⟨l, hl⟩, ?_⟩
        simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
        rw [QuotientGroup.eq]
        obtain ⟨t', ht', htt'⟩ := ht
        have : (Subgroup.inclusion hle0 ⟨l, hl⟩)⁻¹ * ⟨l * t, hy⟩ = t' := by
          apply Subtype.ext
          show (l : G)⁻¹ * (l * t) = t'
          rw [inv_mul_cancel_left]
          exact htt'.symm
        rw [this]
        exact ht'
      have hsecL : IsSec CFSG.Blueprint.NativeSporadic.J2 ↥(lB A B) :=
        hsecθ.of_surjective hsurj
      have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
      have hab : b ∉ Subgroup.zpowers a := by
        intro hb
        have hb3 := (zpowers_mem_omegaA_iff.mp hbΩ).2.1
        have ha3 : a ^ 3 = 1 := hS.toSec13Data.isElemAbelian.2 a haA
        have hacard : Nat.card (Subgroup.zpowers a) = 3 := by
          rw [Nat.card_zpowers]
          exact orderOf_eq_prime ha3 ha1
        have heq : Subgroup.zpowers b = Subgroup.zpowers a :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb) (by rw [hacard, hb3])
        exact haΩ (heq ▸ hbΩ)
      have hB : IsHyperplane A B := by
        have hAab := hS.toSec13Data.isElemAbelian.1
        have hcomm : a * b = b * a :=
          congrArg Subtype.val (hAab.is_comm.comm ⟨a, haA⟩ ⟨b, hbA⟩)
        have h9 := Ronan148J.card_zpowers_sup_zpowers_eq_nine hcomm
          (hS.toSec13Data.isElemAbelian.2 a haA) ha1 (hS.toSec13Data.isElemAbelian.2 b hbA) hab
        have hBeq : B = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
          rw [hBdef, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
            ← Subgroup.closure_union]
          rfl
        refine ⟨?_, ?_⟩
        · rw [hBeq]
          exact sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
        · rw [hBeq, h9, hS.isE27.2]
      by_cases hex : ∃ b' d' Lb', IsLBConfig A B b' d' Lb'
      · obtain ⟨b', d', Lb', hc⟩ := hex
        rw [Item148HJ.lB_eq_residual hS hB hc] at hsecL
        obtain ⟨hdL, -, -, -, -, h6, -⟩ := Item148HJ.resProj_facts hS hB hc
        set φ := Item148HJ.resProj Lb' d'
        have hrange : Nat.card φ.range = 1080 := HJRes2.card_of_isTripleCover_six h6
        have hkers : Group.IsSolvable φ.ker := by
          have hθL := (solvable_prime_complement_core_characterization (H := ↥Lb')
            Nat.prime_three).1
          let ι : φ.ker →* ↥(aschbacherSolvableCore 3 ↥Lb') :=
            { toFun := fun k => ⟨⟨((k : ↥(inSubgroup perfectResidual
                  (Lb' ⊓ Subgroup.centralizer ({d'} : Set G)))) : G),
                Item148HJ.residual_le Lb' d' (k : ↥(inSubgroup perfectResidual
                  (Lb' ⊓ Subgroup.centralizer ({d'} : Set G)))).2⟩, by
                have hk := (Item148HJ.mem_ker_resProj _).mp k.2
                obtain ⟨x, hx, hxk⟩ := hk
                have : x = ⟨_, Item148HJ.residual_le Lb' d' (k : ↥(inSubgroup perfectResidual
                    (Lb' ⊓ Subgroup.centralizer ({d'} : Set G)))).2⟩ := Subtype.ext hxk
                exact this ▸ hx⟩
              map_one' := rfl
              map_mul' := fun _ _ => rfl }
          have hinj : Function.Injective ι := fun x y hxy => by
            have h1 := congrArg (fun t : ↥(aschbacherSolvableCore 3 ↥Lb') => ((t : ↥Lb') : G)) hxy
            exact Subtype.ext (Subtype.ext h1)
          exact solvable_of_solvable_injective hinj
        have hsecK := hsecL.quotient_of_isSolvable hJns (N := φ.ker) hkers
        have hd := hsecK.card_dvd
        rw [hJc, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange] at hd
        norm_num at hd
      · push Not at hex
        rw [lB_eq_bot hex] at hsecL
        have hd := hsecL.card_dvd
        rw [hJc, Subgroup.card_bot] at hd
        norm_num at hd
    ·
      rcases htype with hON | hA6 | hcp
      · obtain ⟨hcZ, ⟨e⟩⟩ := hON
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center _), hcZ,
          Nat.card_congr e.toEquiv, CFSG.Sporadic.ON.card_ON] at hdvd
        norm_num at hdvd
      · rw [HJRes2.card_of_isTripleCover_six hA6] at hdvd
        norm_num at hdvd
      · rw [card_of_isCentralProductA6Covers hcp] at hdvd
        norm_num at hdvd

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
