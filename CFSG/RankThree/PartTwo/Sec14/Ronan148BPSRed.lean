module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSLift
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSSolv
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPoint
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig (thL
  card_thL_coprime normalizer_le_normalizer_thL isSolvable_thL_sub mk_eq_one_iff)


namespace PS

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem card_map_mul_card_ker_of_le {G G' : Type*} [Group G] [Group G'] [Finite G] (f : G →* G')
    {H : Subgroup G} (h : f.ker ≤ H) : Nat.card (H.map f) * Nat.card f.ker = Nat.card H := by
  have h1 := Subgroup.card_ker_mul_card_range (f.domRestrict H)
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  rw [mul_comm]
  exact h1

section ImageA

variable {L A : Subgroup Γ} {b : Γ}

theorem phi_eq_one_iff_mem_sectionCentralizer (hAL : A ≤ Subgroup.normalizer (L : Set Γ))
    {a : Γ} (ha : a ∈ A) :
    phi L ⟨a, hAL ha⟩ = 1 ↔ a ∈ Late.sectionCentralizer A L (thL L) := by
  constructor
  · intro h
    refine ⟨ha, fun x hx => ?_⟩
    have h1 := congrArg (fun φ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) =>
      φ ((⟨x, hx⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L)) h
    simp only [phi_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] at h1
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ aschbacherSolvableCore 3 ↥L, (y : Γ) = a * x * a⁻¹ * x⁻¹ :=
      ⟨_, h1, rfl⟩
    exact ⟨y, hy, hyx⟩
  · rintro ⟨-, h⟩
    ext z
    induction z using QuotientGroup.induction_on with
    | H y =>
      rw [phi_mk, MulAut.one_apply, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
      exact PS.mem_core_of_coe_mem (h y y.2)

@[expose] noncomputable def phiA (L : Subgroup Γ) {A : Subgroup Γ}
    (hAL : A ≤ Subgroup.normalizer (L : Set Γ)) :
    ↥A →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  (phi L).comp (Subgroup.inclusion hAL)

theorem bar_eq_map_phiA (hAL : A ≤ Subgroup.normalizer (L : Set Γ)) {U : Subgroup Γ}
    (hU : U ≤ A) : bar L U = (U.subgroupOf A).map (phiA L hAL) := by
  ext x
  rw [mem_bar]
  constructor
  · rintro ⟨g, hg, hgU, rfl⟩
    exact ⟨⟨g, hU hgU⟩, Subgroup.mem_subgroupOf.mpr hgU, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, hAL a.2, Subgroup.mem_subgroupOf.mp ha, rfl⟩

theorem ker_phiA (hAL : A ≤ Subgroup.normalizer (L : Set Γ))
    (hsec : Late.sectionCentralizer A L (thL L) = (Subgroup.zpowers b : Set Γ)) :
    (phiA L hAL).ker = (Subgroup.zpowers b).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change phi L ⟨a, hAL a.2⟩ = 1 ↔ _
  rw [phi_eq_one_iff_mem_sectionCentralizer hAL a.2, hsec]
  rfl

variable (hA : Late.IsE27 A) (hbA : b ∈ A) (hb1 : b ≠ 1)
  (hAL : A ≤ Subgroup.normalizer (L : Set Γ))
  (hsec : Late.sectionCentralizer A L (thL L) = (Subgroup.zpowers b : Set Γ))
include hA hbA hb1 hAL hsec

theorem card_ker_phiA : Nat.card (phiA L hAL).ker = 3 := by
  have hzA : Subgroup.zpowers b ≤ A := (Subgroup.zpowers_le).mpr hbA
  rw [ker_phiA hAL hsec, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzA).toEquiv,
    Nat.card_zpowers]
  exact orderOf_eq_prime (hA.1.2 b hbA) hb1

theorem card_bar_mul_three {U : Subgroup Γ} (hU : U ≤ A) (hbU : b ∈ U) :
    Nat.card (bar L U) * 3 = Nat.card U := by
  have hker : (phiA L hAL).ker ≤ U.subgroupOf A := by
    rw [ker_phiA hAL hsec]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr
      ((Subgroup.zpowers_le).mpr hbU (Subgroup.mem_subgroupOf.mp hx))
  have h := card_map_mul_card_ker_of_le (phiA L hAL) hker
  rw [card_ker_phiA hA hbA hb1 hAL hsec, ← bar_eq_map_phiA hAL hU,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv] at h
  exact h

theorem card_bar_A : Nat.card (bar L A) = 9 := by
  have h := card_bar_mul_three hA hbA hb1 hAL hsec le_rfl hbA
  rw [hA.2] at h
  omega

theorem isHyperplane_bar {B : Subgroup Γ} (hB : IsHyperplane A B) (hbB : b ∈ B) :
    IsHyperplane (bar L A) (bar L B) := by
  refine ⟨bar_mono hB.1, ?_⟩
  have h1 := card_bar_mul_three hA hbA hb1 hAL hsec hB.1 hbB
  have h2 := card_bar_A hA hbA hb1 hAL hsec
  have h3 := hB.2
  rw [hA.2] at h3
  omega

theorem exists_hyperplane_of_bar {D : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))}
    (hD : IsHyperplane (bar L A) D) :
    ∃ H : Subgroup Γ, IsHyperplane A H ∧ b ∈ H ∧ bar L H = D := by
  set ρ := phiA L hAL with hρ
  have hrange : ρ.range = bar L A := by
    rw [bar_eq_map_phiA hAL le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  have hDr : D ≤ ρ.range := hrange ▸ hD.1
  set H' : Subgroup ↥A := D.comap ρ with hH'
  set H : Subgroup Γ := H'.map A.subtype with hHdef
  have hHA : H ≤ A := Subgroup.map_subtype_le H'
  have hH'eq : H.subgroupOf A = H' := by
    rw [hHdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
  have hbH : b ∈ H := ⟨⟨b, hbA⟩, by
    change ρ ⟨b, hbA⟩ ∈ D
    have : ρ ⟨b, hbA⟩ = 1 := by
      have hk : (⟨b, hbA⟩ : ↥A) ∈ ρ.ker := by
        rw [hρ, ker_phiA hAL hsec, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_zpowers b
      exact hk
    rw [this]
    exact D.one_mem, rfl⟩
  have hbarH : bar L H = D := by
    rw [bar_eq_map_phiA hAL hHA, hH'eq, hH', Subgroup.map_comap_eq, inf_eq_right.mpr hDr]
  refine ⟨H, ⟨hHA, ?_⟩, hbH, hbarH⟩
  have h1 := card_bar_mul_three hA hbA hb1 hAL hsec hHA hbH
  have h2 := card_bar_A hA hbA hb1 hAL hsec
  have h3 := hD.2
  rw [hbarH] at h1
  rw [hA.2]
  omega

end ImageA

theorem exists_mul_of_le_normalizer {L R : Subgroup Γ} (hRL : R ≤ Subgroup.normalizer (L : Set Γ))
    {g : Γ} (hg : g ∈ L ⊔ R) : ∃ l ∈ L, ∃ r ∈ R, g = l * r := by
  have hconj : ∀ r ∈ R, ∀ l ∈ L, r * l * r⁻¹ ∈ L := fun r hr l hl =>
    (Subgroup.mem_normalizer_iff.mp (hRL hr) l).mp hl
  let S : Subgroup Γ :=
    { carrier := {g | ∃ l ∈ L, ∃ r ∈ R, g = l * r}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, r₁, hr₁, rfl⟩ ⟨l₂, hl₂, r₂, hr₂, rfl⟩
        refine ⟨l₁ * (r₁ * l₂ * r₁⁻¹), L.mul_mem hl₁ (hconj r₁ hr₁ l₂ hl₂), r₁ * r₂,
          R.mul_mem hr₁ hr₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨l, hl, r, hr, rfl⟩
        refine ⟨r⁻¹ * l⁻¹ * r⁻¹⁻¹, ?_, r⁻¹, R.inv_mem hr, ?_⟩
        · exact hconj r⁻¹ (R.inv_mem hr) l⁻¹ (L.inv_mem hl)
        · group }
  have hle : L ⊔ R ≤ S := sup_le (fun l hl => ⟨l, hl, 1, one_mem _, by simp⟩)
    (fun r hr => ⟨1, one_mem _, r, hr, by simp⟩)
  exact hle hg

namespace LRData

variable {L R : Subgroup Γ} (d : LRData L R)
include d

theorem sig_bar {A W : Subgroup Γ} {b : Γ} (hA : Late.IsE27 A) (hbA : b ∈ A) (hb1 : b ≠ 1)
    (hAL : A ≤ Subgroup.normalizer (L : Set Γ)) (hAR : A ≤ Subgroup.normalizer (R : Set Γ))
    (hsec : Late.sectionCentralizer A L (thL L) = (Subgroup.zpowers b : Set Γ))
    (hW : W ≤ L ⊔ R) (hAW : A ≤ Subgroup.normalizer (W : Set Γ))
    (hsig : ∀ H : Subgroup Γ, IsHyperplane A H → ∀ V : Subgroup Γ,
      V ≤ W ⊓ Subgroup.centralizer (H : Set Γ) → V ∈ invariantPiSubgroups ⊤ A (piCompl 3) →
      V = ⁅V, A⁆ → V ≤ pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (H : Set Γ))) :
    ∀ H' : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)), IsHyperplane (bar L A) H' →
      ∀ V' : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)),
        V' ≤ bar L W ⊓
          Subgroup.centralizer (↑H' : Set (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))) →
        V' ∈ invariantPiSubgroups ⊤ (bar L A) (piCompl 3) → V' = ⁅V', bar L A⁆ →
        V' ≤ pPrimeCoreOf 3 (bar L W ⊓
          Subgroup.centralizer (↑H' : Set (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)))) := by
  intro H' hH' V' hV' hV'inv hV'c
  have hAp : IsPGroup 3 A := hA.isPGroup
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨H, hH, -, rfl⟩ := exists_hyperplane_of_bar hA hbA hb1 hAL hsec hH'
  obtain ⟨V, hVle, hVinv, hVc, hV'V⟩ := d.exists_lift_signalizer hAp hAc hAL hAR hW hH.1 hAW
    (le_inf_iff.mp hV').1 (le_inf_iff.mp hV').2 hV'inv hV'c
  have h1 := hsig H hH V hVle hVinv hVc
  have hK : W ⊓ Subgroup.centralizer (H : Set Γ) ≤ Subgroup.normalizer (L : Set Γ) :=
    (inf_le_left.trans hW).trans d.sup_le_normalizer
  have h2 := bar_pPrimeCoreOf_le hK
  rw [d.bar_inf_centralizer hW (hAp.to_le hH.1) (hH.1.trans hAL) (hH.1.trans hAR)
    (hH.1.trans hAW)] at h2
  exact hV'V.trans ((bar_mono h1).trans h2)

end LRData

section Types


theorem isSimpleGroup_of_types148 {X : Type} [Group X] [Finite X]
    (hT : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) ∨ IsLThreePi X ∨
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hns : ¬ Group.IsSolvable X) : IsSimpleGroup X := by
  rcases hT with ⟨⟨φ⟩⟩ | hL | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · haveI := CFSG.Sporadic.J2.isSimpleGroup_J2
    exact φ.isSimpleGroup
  · exact Ronan148K.isSimpleGroup_of_isLThreePi_not_solvable hL hns
  · haveI := Ronan148K.isSimpleGroup_alt_seven
    exact φ.isSimpleGroup
  · haveI := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact φ.isSimpleGroup
  · haveI := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    exact φ.isSimpleGroup

end Types

theorem lrData_of_simple {L R : Subgroup Γ} (hR : Nat.Coprime 3 (Nat.card R))
    (hLR : L ≤ Subgroup.normalizer (R : Set Γ)) (hRL : R ≤ Subgroup.normalizer (L : Set Γ))
    (hs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hns : ¬ Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L)) (h3 : 3 ∣ Nat.card L) :
    LRData L R := by
  refine ⟨hR, hLR, hRL, inf_le_thL_of hR hLR fun N hN hN3 => ?_, ?_⟩
  · haveI := hs
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      apply hN3
      rw [h, Subgroup.card_top]
      have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L)
      have hθ := card_thL_coprime L
      rw [thL, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective] at hθ
      rw [hcard] at h3
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h' | h'
      · exact h'
      · exact absurd h' hθ
  · haveI := hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)) with h | h
    · exact h
    · exfalso
      apply hns
      have hcomm : ∀ x y : ↥L ⧸ aschbacherSolvableCore 3 ↥L, x * y = y * x := by
        intro x y
        have hx : x ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
          rw [h]; exact Subgroup.mem_top x
        exact (Subgroup.mem_center_iff.mp hx y).symm
      exact Group.isSolvable_of_comm hcomm

end PS

section Certs


theorem kf148PointSigF_of_img (h : KF148PointSigImg) : KF148PointSigF := by
  intro Γ _ _ A L R W Q B b hA hbA hb1 hLb hAL hsec hF h131 hT h46 hloc hR3 hLR hRL hAR hWLR hAW hB
    hbB hQW hQ hQA hsig hQW'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := hA.isPGroup
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hQW0 : Q ≤ W := hQW.trans inf_le_left
  have hQB : Q ≤ Subgroup.centralizer (B : Set Γ) := hQW.trans inf_le_right
  have hQOB : Q ≤ pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (B : Set Γ)) := hsig B hB Q hQW hQ hQA
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_types148 hT
  by_cases hsolX : Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L)
  ·
    exfalso
    apply hQW'
    set N₀ : Subgroup Γ := thL L ⊔ R with hN₀
    have hRθ : R ≤ Subgroup.normalizer (thL L : Set Γ) := hRL.trans (normalizer_le_normalizer_thL L)
    have hLRN : L ⊔ R ≤ Subgroup.normalizer (N₀ : Set Γ) :=
      Sec14.le_normalizer_sup
        (sup_le ((Subgroup.le_normalizer).trans (normalizer_le_normalizer_thL L)) hRθ)
        (sup_le hLR Subgroup.le_normalizer)
    have hN₀LR : N₀ ≤ L ⊔ R :=
      sup_le ((Subgroup.map_subtype_le _).trans le_sup_left) le_sup_right
    haveI hnorm : (N₀.subgroupOf (L ⊔ R)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀LR).mpr hLRN
    set f : ↥W →* ↥(L ⊔ R) ⧸ N₀.subgroupOf (L ⊔ R) :=
      (QuotientGroup.mk' (N₀.subgroupOf (L ⊔ R))).comp (Subgroup.inclusion hWLR) with hf
    have hsolL : Group.IsSolvable ↥L := by
      haveI := hsolX
      haveI : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥L) :=
        (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
      exact Group.isSolvable_of_ker_le_range (aschbacherSolvableCore 3 ↥L).subtype
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) (fun x hx => ⟨⟨x, by
          rwa [QuotientGroup.ker_mk'] at hx⟩, rfl⟩)
    have hsolM : Group.IsSolvable (↥(L ⊔ R) ⧸ N₀.subgroupOf (L ⊔ R)) := by
      haveI := hsolL
      refine Group.isSolvable_of_surjective
        (f := (QuotientGroup.mk' (N₀.subgroupOf (L ⊔ R))).comp
          (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ R))) ?_
      intro y
      obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk'_surjective _ y
      obtain ⟨l, hl, r, hr, rfl⟩ := PS.exists_mul_of_le_normalizer hRL hg
      refine ⟨⟨l, hl⟩, ?_⟩
      change ((⟨l, le_sup_left (a := L) hl⟩ : ↥(L ⊔ R)) : ↥(L ⊔ R) ⧸ N₀.subgroupOf (L ⊔ R)) =
        ((⟨l * r, hg⟩ : ↥(L ⊔ R)) : ↥(L ⊔ R) ⧸ N₀.subgroupOf (L ⊔ R))
      rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv, Subgroup.mem_subgroupOf]
      change l * (l * r)⁻¹ ∈ N₀
      have e : l * (l * r)⁻¹ = l * r⁻¹ * l⁻¹ := by group
      rw [e]
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hLR hl) r⁻¹).mp (R.inv_mem hr))
    have hrange : Group.IsSolvable f.range := by
      haveI := hsolM
      infer_instance
    have hker : Nat.Coprime 3 (Nat.card f.ker) := by
      let j : f.ker →* N₀ :=
        { toFun := fun k => ⟨((k : ↥W) : Γ), by
            have h1 : (QuotientGroup.mk' (N₀.subgroupOf (L ⊔ R)))
                (Subgroup.inclusion hWLR (k : ↥W)) = 1 := k.2
            rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
            exact h1⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hj : Function.Injective j := fun x y hxy => by
        have h1 : ((x : ↥W) : Γ) = ((y : ↥W) : Γ) := congrArg (fun z : ↥N₀ => (z : Γ)) hxy
        exact Subtype.ext (Subtype.ext h1)
      have hN₀3 : Nat.Coprime 3 (Nat.card N₀) := by
        have hθR : thL L ≤ Subgroup.normalizer (R : Set Γ) := (Subgroup.map_subtype_le _).trans hLR
        have hdvd := card_sup_dvd_card_mul hθR
        have hθ3 : Nat.Coprime 3 (Nat.card (thL L)) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (card_thL_coprime L)
        exact Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.mul_right hθ3 hR3)
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective j hj) hN₀3
    exact PS.le_pPrimeCoreOf_of_hom_solvable (hAp.to_le hB.1) (hB.1.trans hAW) hQW0 hQOB f
      hrange hker
  ·
    have hs := PS.isSimpleGroup_of_types148 hT hsolX
    have d := PS.lrData_of_simple hR3 hLR hRL hs hsolX h3L
    have hsec' : Late.sectionCentralizer A L (thL L) = (Subgroup.zpowers b : Set Γ) := hsec
    have hP : Sec4.autThetaQuot A L = PS.bar L A := by
      rw [Sec4.autThetaQuot, Sec4.autIn, Subgroup.map_map, inf_eq_left.mpr hAL]
      rfl
    have hImg := h Γ A L b hA hbA hb1 hLb hAL hsec hF h131 hT h46 hloc
    rw [hP] at hImg
    have hWN : W ≤ Subgroup.normalizer (L : Set Γ) := hWLR.trans d.sup_le_normalizer
    have hQN : Q ≤ Subgroup.normalizer (L : Set Γ) := hQW0.trans hWN
    have hWinn : PS.bar L W ≤ (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* _).range := by
      intro x hx
      obtain ⟨w, hw, hwW, rfl⟩ := PS.mem_bar.mp hx
      obtain ⟨l, hl, r, hr, rfl⟩ := d.exists_mul (hWLR hwW)
      rw [d.phi_mul_of_mem hl hr hw, PS.phi_of_mem L hl]
      exact ⟨_, rfl⟩
    have hPW := PS.bar_le_normalizer_bar (L := L) hAW
    have hD := PS.isHyperplane_bar hA hbA hb1 hAL hsec' hB hbB
    have hQC : PS.bar L Q ≤ PS.bar L W ⊓
        Subgroup.centralizer (↑(PS.bar L B) : Set (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))) := by
      refine le_inf (PS.bar_mono hQW0) ?_
      intro x hx
      obtain ⟨q, hqN, hqQ, rfl⟩ := PS.mem_bar.mp hx
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      obtain ⟨β, hβN, hβB, rfl⟩ := PS.mem_bar.mp hy
      have hcomm : β * q = q * β := Subgroup.mem_centralizer_iff.mp (hQB hqQ) β hβB
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm
    have hQinv : PS.bar L Q ∈ invariantPiSubgroups ⊤ (PS.bar L A) (piCompl 3) := by
      refine ⟨le_top, ?_, PS.bar_le_normalizer_bar hQ.2.2⟩
      intro q hq3
      have hQ3 : ¬ 3 ∣ Nat.card Q := fun h3 => (hQ.2.1 ⟨3, Nat.prime_three⟩ h3) rfl
      show (q : ℕ) ≠ 3
      intro hq3'
      exact hQ3 ((hq3' ▸ hq3).trans (PS.card_bar_dvd hQN))
    have hQcomm : PS.bar L Q = ⁅PS.bar L Q, PS.bar L A⁆ := by
      rw [← PS.bar_commutator hQN hAL, ← hQA]
    obtain ⟨T, hTmem, hPT, h3, hgen⟩ := hImg (PS.bar L W) (PS.bar L Q) (PS.bar L B) hWinn hPW hD
      hQC hQinv hQcomm (d.sig_bar hA hbA hb1 hAL hAR hsec' hWLR hAW hsig)
      (d.not_bar_le_core hWLR hQW0 hQW')
    exact d.exists_component_of_image hAp hAc hAL hAR hWLR hAW hTmem hPT h3 hgen

end Certs

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
