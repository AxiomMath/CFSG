module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPC
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneONan
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K3Holds
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Group
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeCardSubgroupIntersection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.RankThree.LocalRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem frame_mem_L_of_pow_three (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ∀ x ∈ P, x ^ 3 = 1 → x ∈ c.L := by
  intro x hxP hx3
  exact c.forall_pow_three_eq_one_mem_L_of_threeCover
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds
    (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Out_holds c.Lbar hON)
    hON hP x hxP hx3

theorem frame_pow_three_of_mem_inf_L (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ∀ x ∈ P ⊓ c.L, x ^ 3 = 1 :=
  c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP

theorem frame_card_zSub (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Nat.card ↥(zSub P c.L) = 3 :=
  c.card_inf_centralizer_of_onan hON hP

theorem frame_centralizer_card (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {e : G}
    (heQ : e ∈ P ⊓ c.L) (heZ : e ∉ zSub P c.L) :
    27 ≤ Nat.card ↥((P ⊓ c.L) ⊓ Subgroup.centralizer ({e} : Set G)) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Subgroup G := P ⊓ c.L
  have hZleQ : zSub P c.L ≤ Q := inf_le_left
  have hcardQ : Nat.card ↥Q = 3 ^ 5 := card_inf_L_of_onan_wPH7 c hON hP
  have hcenter : Subgroup.center ↥Q = (zSub P c.L).subgroupOf Q := by
    ext x
    rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf, zSub, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro hx
      refine ⟨x.2, fun y hy => ?_⟩
      exact congrArg (fun u : ↥Q => (u : G)) (hx ⟨y, hy⟩)
    · rintro ⟨-, hx⟩ y
      exact Subtype.ext (hx (y : G) y.2)
  have hcenterCard : Nat.card ↥(Subgroup.center ↥Q) = 3 := by
    rw [hcenter]
    calc Nat.card ↥((zSub P c.L).subgroupOf Q) = Nat.card ↥(zSub P c.L) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleQ).toEquiv
      _ = 3 := frame_card_zSub c hON hP
  have hcommQ : ∀ a b : ↥Q, ⁅a, b⁆ ∈ Subgroup.center ↥Q := by
    intro a b
    rw [hcenter, Subgroup.mem_subgroupOf]
    exact frame_commutator_le_Zs_wPH7 c hON hP
      (Subgroup.commutator_mem_commutator a.2 b.2)
  let eQ : ↥Q := ⟨e, heQ⟩
  have hCindex : (Subgroup.centralizer ({eQ} : Set ↥Q)).index ≤ 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.c25_index_centralizer_le hcenterCard hcommQ eQ
  have hcardC : 27 ≤ Nat.card ↥(Subgroup.centralizer ({eQ} : Set ↥Q)) := by
    have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({eQ} : Set ↥Q))
    have hle : Nat.card ↥(Subgroup.centralizer ({eQ} : Set ↥Q)) *
        (Subgroup.centralizer ({eQ} : Set ↥Q)).index ≤
        Nat.card ↥(Subgroup.centralizer ({eQ} : Set ↥Q)) * 3 :=
      Nat.mul_le_mul_left _ hCindex
    rw [hmul, hcardQ, show (3 : ℕ) ^ 5 = 243 by norm_num] at hle
    omega
  have hcenterC : Subgroup.centralizer ({eQ} : Set ↥Q) =
      (Q ⊓ Subgroup.centralizer ({e} : Set G)).subgroupOf Q := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      exact ⟨x.2, congrArg (fun u : ↥Q => (u : G)) hx⟩
    · rintro ⟨-, hx⟩
      exact Subtype.ext hx
  have hcardEq : Nat.card ↥(Q ⊓ Subgroup.centralizer ({e} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({eQ} : Set ↥Q)) := by
    calc Nat.card ↥(Q ⊓ Subgroup.centralizer ({e} : Set G)) =
          Nat.card ↥((Q ⊓ Subgroup.centralizer ({e} : Set G)).subgroupOf Q) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Q ⊓
            Subgroup.centralizer ({e} : Set G) ≤ Q)).toEquiv).symm
      _ = Nat.card ↥(Subgroup.centralizer ({eQ} : Set ↥Q)) := by rw [← hcenterC]
  calc 27 ≤ Nat.card ↥(Subgroup.centralizer ({eQ} : Set ↥Q)) := hcardC
    _ = Nat.card ↥(Q ⊓ Subgroup.centralizer ({e} : Set G)) := hcardEq.symm

theorem isElemAbelian_zSub (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    IsElemAbelian 3 (zSub P c.L) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · change (a : G) * (b : G) = (b : G) * (a : G)
    exact Subgroup.mem_centralizer_iff.mp (zSub_le_centralizer P c.L b.2) (a : G) a.2.1
  · intro x hx
    exact frame_pow_three_of_mem_inf_L c hON hP x (Subgroup.mem_inf.mp hx).1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G}

def Admissible (c : Ctx82E3 D) (P A : Subgroup G) : Prop :=
  IsElemAbelian 3 A ∧ Nat.card A = 27 ∧ zSub P c.L ≤ A ∧ A ≤ P ⊓ c.L

theorem hyperplane_of_card_nine {A E : Subgroup G} (hEA : E ≤ A)
    (hE : Nat.card E = 9) (hA : Nat.card A = 27) :
    E ∈ UC22.InS3.hyperplanes 3 A := by
  refine ⟨hEA, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := E) (K := A)
  rw [inf_eq_left.mpr hEA, hE, hA] at h
  omega

theorem thetaAlpha_eq_of_inf_card_nine {c : Ctx82E3 D} {P : Subgroup G}
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hlocal : ∀ A : Subgroup G, IsElemAbelian 3 A → Nat.card A = 27 →
      zSub P c.L ≤ A → A ≤ P ⊓ c.L →
      ∀ E ∈ UC22.InS3.hyperplanes 3 A, ∀ E' ∈ UC22.InS3.hyperplanes 3 A,
        thetaAlpha 3 E = thetaAlpha 3 E')
    {A B : Subgroup G} (hA : Admissible c P A) (hB : Admissible c P B)
    (hinf : Nat.card ↥(A ⊓ B) = 9)
    {E E' : Subgroup G} (hE : E ∈ UC22.InS3.hyperplanes 3 A)
    (hE' : E' ∈ UC22.InS3.hyperplanes 3 B) :
    thetaAlpha 3 E = thetaAlpha 3 E' := by
  have hI_A : (A ⊓ B) ≤ A := inf_le_left
  have hI_B : (A ⊓ B) ≤ B := inf_le_right
  have hI_A_hyp : A ⊓ B ∈ UC22.InS3.hyperplanes 3 A :=
    hyperplane_of_card_nine hI_A hinf hA.2.1
  have hI_B_hyp : A ⊓ B ∈ UC22.InS3.hyperplanes 3 B :=
    hyperplane_of_card_nine hI_B hinf hB.2.1
  have h1 := hlocal A hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 E hE (A ⊓ B) hI_A_hyp
  have h2 := hlocal B hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 (A ⊓ B) hI_B_hyp E' hE'
  exact h1.trans h2

theorem card_inf_admissible {c : Ctx82E3 D} {P : Subgroup G}
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {A B : Subgroup G} (hA : Admissible c P A) (hB : Admissible c P B) :
    Nat.card ↥(A ⊓ B) = 3 ∨ Nat.card ↥(A ⊓ B) = 9 ∨ Nat.card ↥(A ⊓ B) = 27 := by
  have hdvd : Nat.card ↥(A ⊓ B) ∣ 27 := by
    rw [← hA.2.1]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hdvd' : Nat.card ↥(A ⊓ B) ∣ 3 ^ 3 := by
    simpa [show (3 : ℕ) ^ 3 = 27 by norm_num] using hdvd
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd'
  have hZle : zSub P c.L ≤ A ⊓ B := le_inf hA.2.2.1 hB.2.2.1
  have hZcard : Nat.card ↥(zSub P c.L) = 3 := frame_card_zSub c hON hP
  have hge : 3 ≤ Nat.card ↥(A ⊓ B) := by
    calc 3 = Nat.card ↥(zSub P c.L) := hZcard.symm
      _ ≤ Nat.card ↥(A ⊓ B) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hZle)
          (Subgroup.inclusion_injective hZle)
  interval_cases k <;> simp_all

theorem exists_connecting_admissible {c : Ctx82E3 D} {P : Subgroup G}
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {A B : Subgroup G} (hA : Admissible c P A) (hB : Admissible c P B)
    (hinf : A ⊓ B = zSub P c.L) :
    ∃ A'' : Subgroup G, Admissible c P A'' ∧
      Nat.card ↥(A ⊓ A'') = 9 ∧ Nat.card ↥(B ⊓ A'') = 9 := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZcard : Nat.card ↥(zSub P c.L) = 3 := frame_card_zSub c hON hP
  have hZea : IsElemAbelian 3 (zSub P c.L) := isElemAbelian_zSub c hON hP
  have hAnZ : ¬ A ≤ zSub P c.L := by
    intro hle
    have hcardle : Nat.card ↥A ≤ Nat.card ↥(zSub P c.L) := Subgroup.card_le_of_le hle
    rw [hA.2.1, hZcard] at hcardle
    omega
  obtain ⟨a, haA, haZ⟩ := Set.not_subset.mp hAnZ
  have haQ : a ∈ P ⊓ c.L := hA.2.2.2 haA
  have ha3 : a ^ 3 = 1 := hA.1.2 a haA
  have ha1 : a ≠ 1 := fun h => haZ (h.symm ▸ (zSub P c.L).one_mem)
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hcommZa : ∀ z ∈ zSub P c.L, Commute z a := by
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (zSub_le_centralizer P c.L hz) a haQ).symm
  obtain ⟨hE1ea, hE1card⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers
    (p := 3) hZea haord hcommZa haZ
  let E1 : Subgroup G := zSub P c.L ⊔ Subgroup.zpowers a
  have hE1card9 : Nat.card E1 = 9 := by
    change Nat.card ↥(zSub P c.L ⊔ Subgroup.zpowers a) = 9
    rw [hE1card, hZcard]
  have hE1A : E1 ≤ A := by
    change zSub P c.L ⊔ Subgroup.zpowers a ≤ A
    exact sup_le hA.2.2.1 (Subgroup.zpowers_le.mpr haA)
  have hcommB : ∀ y : ↥B, ⁅a, (y : G)⁆ ∈ zSub P c.L := by
    intro y
    exact frame_commutator_le_Zs_wPH7 c hON hP
      (Subgroup.commutator_mem_commutator haQ (hB.2.2.2 y.2))
  let φ : ↥B →* ↥(zSub P c.L) :=
    { toFun := fun y => ⟨⁅a, (y : G)⁆, hcommB y⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun y₁ y₂ => by
        apply Subtype.ext
        have h2 : (y₁ : G) * ⁅a, (y₂ : G)⁆ * (y₁ : G)⁻¹ = ⁅a, (y₂ : G)⁆ := by
          have hcomm := Subgroup.mem_centralizer_iff.mp
            (zSub_le_centralizer P c.L (hcommB y₂)) (y₁ : G) (hB.2.2.2 y₁.2)
          rw [hcomm]
          group
        have h1 : ⁅a, (y₁ : G) * (y₂ : G)⁆ =
            ⁅a, (y₁ : G)⁆ * ((y₁ : G) * ⁅a, (y₂ : G)⁆ * (y₁ : G)⁻¹) := by
          simp only [commutatorElement_def]
          group
        show ⁅a, (y₁ : G) * (y₂ : G)⁆ = ⁅a, (y₁ : G)⁆ * ⁅a, (y₂ : G)⁆
        rw [h1, h2] }
  have hker9 : 9 ≤ Nat.card φ.ker := by
    have hmul := Subgroup.card_ker_mul_card_range φ
    have hrange : Nat.card φ.range ≤ 3 :=
      (Subgroup.card_le_card_group φ.range).trans (le_of_eq hZcard)
    rw [hB.2.1] at hmul
    have hle : Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * 3 :=
      Nat.mul_le_mul_left _ hrange
    rw [hmul] at hle
    omega
  let K : Subgroup G := φ.ker.map B.subtype
  have hKcard : 9 ≤ Nat.card K := by
    change 9 ≤ Nat.card ↥(φ.ker.map B.subtype)
    rw [Subgroup.card_map_of_injective B.subtype_injective]
    exact hker9
  have hnotKZ : ¬ K ≤ zSub P c.L := by
    intro hle
    have hcardle : Nat.card K ≤ Nat.card ↥(zSub P c.L) := Subgroup.card_le_of_le hle
    rw [hZcard] at hcardle
    omega
  obtain ⟨b, hbK, hbZ⟩ := Set.not_subset.mp hnotKZ
  obtain ⟨bB, hbBker, rfl⟩ := Subgroup.mem_map.mp hbK
  have hb1 : (bB : G) ≠ 1 := by
    intro h
    apply hbZ
    have h1 : (1 : G) ∈ zSub P c.L := (zSub P c.L).one_mem
    rw [← h] at h1
    exact h1
  have hb3 : (bB : G) ^ 3 = 1 := hB.1.2 (bB : G) bB.2
  have hbord : orderOf (bB : G) = 3 := orderOf_eq_prime hb3 hb1
  have hbE1 : (bB : G) ∉ E1 := by
    intro hb
    have hbA : (bB : G) ∈ A := hE1A hb
    have hbAB : (bB : G) ∈ A ⊓ B := ⟨hbA, bB.2⟩
    rw [hinf] at hbAB
    exact hbZ hbAB
  have hcommZb : ∀ z ∈ zSub P c.L, Commute z (bB : G) := by
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (zSub_le_centralizer P c.L hz) (bB : G)
      (hB.2.2.2 bB.2)).symm
  have hcomm_ab : Commute a (bB : G) := by
    rw [← commutatorElement_eq_one_iff_commute]
    have h := congrArg (fun z : ↥(zSub P c.L) => (z : G)) (MonoidHom.mem_ker.mp hbBker)
    change ⁅a, (bB : G)⁆ = 1 at h
    exact h
  have hE1bcomm : ∀ e ∈ E1, Commute e (bB : G) := by
    intro e he
    have hle : E1 ≤ Subgroup.centralizer ({(bB : G)} : Set G) := by
      change zSub P c.L ⊔ Subgroup.zpowers a ≤ _
      refine sup_le ?_ ?_
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcommZb z hz
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hcomm_ab
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  obtain ⟨hE2ea, hE2card⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers
    (p := 3) hZea hbord hcommZb hbZ
  let E2 : Subgroup G := zSub P c.L ⊔ Subgroup.zpowers (bB : G)
  have hE2card9 : Nat.card E2 = 9 := by
    change Nat.card ↥(zSub P c.L ⊔ Subgroup.zpowers (bB : G)) = 9
    rw [hE2card, hZcard]
  obtain ⟨hA''ea, hA''card0⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers
    (p := 3) hE1ea hbord hE1bcomm hbE1
  let A'' : Subgroup G := E1 ⊔ Subgroup.zpowers (bB : G)
  have hA''card : Nat.card A'' = 27 := by
    change Nat.card ↥(E1 ⊔ Subgroup.zpowers (bB : G)) = 27
    rw [hA''card0, hE1card9]
  have hA''adm : Admissible c P A'' := by
    refine ⟨hA''ea, hA''card, ?_, ?_⟩
    · change zSub P c.L ≤ E1 ⊔ Subgroup.zpowers (bB : G)
      exact (le_sup_left : zSub P c.L ≤ E1).trans le_sup_left
    · change E1 ⊔ Subgroup.zpowers (bB : G) ≤ P ⊓ c.L
      refine sup_le ?_ (Subgroup.zpowers_le.mpr (hB.2.2.2 bB.2))
      change zSub P c.L ⊔ Subgroup.zpowers a ≤ P ⊓ c.L
      exact sup_le (inf_le_left : zSub P c.L ≤ P ⊓ c.L) (Subgroup.zpowers_le.mpr haQ)
  have hE1le : E1 ≤ A ⊓ A'' := by
    refine le_inf hE1A ?_
    change E1 ≤ E1 ⊔ Subgroup.zpowers (bB : G)
    exact le_sup_left
  have hcardAint : Nat.card ↥(A ⊓ A'') = 9 := by
    have hdvd : Nat.card ↥(A ⊓ A'') ∣ 27 := by
      rw [← hA''card]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hge : 9 ≤ Nat.card ↥(A ⊓ A'') := by
      calc 9 = Nat.card E1 := hE1card9.symm
        _ ≤ Nat.card ↥(A ⊓ A'') := Nat.card_le_card_of_injective
            (Subgroup.inclusion hE1le) (Subgroup.inclusion_injective hE1le)
    have hne27 : Nat.card ↥(A ⊓ A'') ≠ 27 := by
      intro h27
      have hEq : A ⊓ A'' = A'' :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h27, hA''card])
      have hbA'' : (bB : G) ∈ A'' := by
        change (bB : G) ∈ E1 ⊔ Subgroup.zpowers (bB : G)
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      have hbAI : (bB : G) ∈ A ⊓ A'' := hEq.symm ▸ hbA''
      have hbA : (bB : G) ∈ A := hbAI.1
      have : (bB : G) ∈ A ⊓ B := ⟨hbA, bB.2⟩
      rw [hinf] at this
      exact hbZ this
    have hdvd' : Nat.card ↥(A ⊓ A'') ∣ 3 ^ 3 := by
      simpa [show (3 : ℕ) ^ 3 = 27 by norm_num] using hdvd
    obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd'
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk_cases with rfl | rfl | rfl | rfl
    · rw [hcard] at hge
      norm_num at hge
    · rw [hcard] at hge
      norm_num at hge
    · rw [hcard]; norm_num
    · exfalso
      exact hne27 (by rw [hcard]; norm_num)
  have hE2B : E2 ≤ B := by
    change zSub P c.L ⊔ Subgroup.zpowers (bB : G) ≤ B
    exact sup_le hB.2.2.1 (Subgroup.zpowers_le.mpr bB.2)
  have hE2A'' : E2 ≤ A'' := by
    change zSub P c.L ⊔ Subgroup.zpowers (bB : G) ≤
      E1 ⊔ Subgroup.zpowers (bB : G)
    exact sup_le ((le_sup_left : zSub P c.L ≤ E1).trans le_sup_left) le_sup_right
  have hE2le : E2 ≤ B ⊓ A'' := le_inf hE2B hE2A''
  have hcardBint : Nat.card ↥(B ⊓ A'') = 9 := by
    have hdvd : Nat.card ↥(B ⊓ A'') ∣ 27 := by
      rw [← hA''card]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hge : 9 ≤ Nat.card ↥(B ⊓ A'') := by
      calc 9 = Nat.card E2 := hE2card9.symm
        _ ≤ Nat.card ↥(B ⊓ A'') := Nat.card_le_card_of_injective
            (Subgroup.inclusion hE2le) (Subgroup.inclusion_injective hE2le)
    have hne27 : Nat.card ↥(B ⊓ A'') ≠ 27 := by
      intro h27
      have hEq : B ⊓ A'' = A'' :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h27, hA''card])
      have haA'' : a ∈ A'' := by
        change a ∈ E1 ⊔ Subgroup.zpowers (bB : G)
        exact Subgroup.mem_sup_left (by
          change a ∈ zSub P c.L ⊔ Subgroup.zpowers a
          exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
      have haBI : a ∈ B ⊓ A'' := hEq.symm ▸ haA''
      have haB : a ∈ B := haBI.1
      have : a ∈ A ⊓ B := ⟨haA, haB⟩
      rw [hinf] at this
      exact haZ this
    have hdvd' : Nat.card ↥(B ⊓ A'') ∣ 3 ^ 3 := by
      simpa [show (3 : ℕ) ^ 3 = 27 by norm_num] using hdvd
    obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd'
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk_cases with rfl | rfl | rfl | rfl
    · rw [hcard] at hge
      norm_num at hge
    · rw [hcard] at hge
      norm_num at hge
    · rw [hcard]; norm_num
    · exfalso
      exact hne27 (by rw [hcard]; norm_num)
  exact ⟨A'', hA''adm, hcardAint, hcardBint⟩

theorem thetaAlpha_eq_of_admissible {c : Ctx82E3 D} {P : Subgroup G}
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hlocal : ∀ A : Subgroup G, IsElemAbelian 3 A → Nat.card A = 27 →
      zSub P c.L ≤ A → A ≤ P ⊓ c.L →
      ∀ E ∈ UC22.InS3.hyperplanes 3 A, ∀ E' ∈ UC22.InS3.hyperplanes 3 A,
        thetaAlpha 3 E = thetaAlpha 3 E')
    {A B : Subgroup G} (hA : Admissible c P A) (hB : Admissible c P B)
    {E E' : Subgroup G} (hE : E ∈ UC22.InS3.hyperplanes 3 A)
    (hE' : E' ∈ UC22.InS3.hyperplanes 3 B) :
    thetaAlpha 3 E = thetaAlpha 3 E' := by
  rcases card_inf_admissible hON hP hA hB with h3 | h9 | h27
  · have hinf : A ⊓ B = zSub P c.L := by
      refine (Subgroup.eq_of_le_of_card_ge (le_inf hA.2.2.1 hB.2.2.1) ?_).symm
      rw [h3, frame_card_zSub c hON hP]
    obtain ⟨A'', hA'', h9A, h9B⟩ := exists_connecting_admissible hON hP hA hB hinf
    have hEA'' : thetaAlpha 3 E = thetaAlpha 3 (A ⊓ A'') :=
      thetaAlpha_eq_of_inf_card_nine hON hP hlocal hA hA'' h9A hE
        (hyperplane_of_card_nine inf_le_right h9A hA''.2.1)
    have hA''B : thetaAlpha 3 (A ⊓ A'') = thetaAlpha 3 (B ⊓ A'') :=
      thetaAlpha_eq_of_inf_card_nine hON hP hlocal hA'' hB (by rw [inf_comm]; exact h9B)
        (hyperplane_of_card_nine inf_le_right h9A hA''.2.1)
        (hyperplane_of_card_nine inf_le_left h9B hB.2.1)
    have hBE' : thetaAlpha 3 (B ⊓ A'') = thetaAlpha 3 E' :=
      (thetaAlpha_eq_of_inf_card_nine hON hP hlocal hB hA'' h9B hE'
        (hyperplane_of_card_nine inf_le_right h9B hA''.2.1)).symm
    exact hEA''.trans (hA''B.trans hBE')
  · exact thetaAlpha_eq_of_inf_card_nine hON hP hlocal hA hB h9 hE hE'
  · have hAB : A = B := by
      have hle : A ≤ B := by
        have h : A ⊓ B = A := by
          refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
          rw [h27, hA.2.1]
        rw [← h]
        exact inf_le_right
      exact le_antisymm hle (by
        have h : A ⊓ B = B := by
          refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
          rw [h27, hB.2.1]
        rw [← h]
        exact inf_le_left)
    subst hAB
    exact hlocal A hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 E hE E' hE'

theorem exists_admissible_of_card_nine {c : Ctx82E3 D} {P : Subgroup G}
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {E : Subgroup G} (hEP : E ≤ P) (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 9) :
    ∃ A : Subgroup G, Admissible c P A ∧ E ∈ UC22.InS3.hyperplanes 3 A := by
  classical
  have hEQ : E ≤ P ⊓ c.L := by
    refine le_inf hEP ?_
    intro x hx
    exact frame_mem_L_of_pow_three c hON hP x (hEP hx) (hE.2 x hx)
  have hQexp : ∀ x ∈ P ⊓ c.L, x ^ 3 = 1 := frame_pow_three_of_mem_inf_L c hON hP
  have hZcard : Nat.card ↥(zSub P c.L) = 3 := frame_card_zSub c hON hP
  have hZprime : Nat.Prime (Nat.card ↥(zSub P c.L)) := by rw [hZcard]; norm_num
  by_cases hZE : zSub P c.L ≤ E
  ·
    have hex : ∃ e ∈ E, e ∉ zSub P c.L := by
      by_contra h
      push Not at h
      have hle : E ≤ zSub P c.L := h
      have hcardle : Nat.card ↥E ≤ Nat.card ↥(zSub P c.L) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle)
      rw [hEcard, hZcard] at hcardle
      omega
    obtain ⟨e, heE, heZ⟩ := hex
    have he3 : e ^ 3 = 1 := hE.2 e heE
    have he1 : e ≠ 1 := by
      intro h
      exact heZ (h.symm ▸ (zSub P c.L).one_mem)
    have heord : orderOf e = 3 := orderOf_eq_prime he3 he1
    have hepcard : Nat.card ↥(Subgroup.zpowers e) = 3 := by
      rw [Nat.card_zpowers, heord]
    have hepprime : Nat.Prime (Nat.card ↥(Subgroup.zpowers e)) := by
      rw [hepcard]; norm_num
    have hnot_ep : ¬ Subgroup.zpowers e ≤ zSub P c.L := by
      intro hle
      exact heZ (hle (Subgroup.mem_zpowers e))
    have hdisj_Z_e : zSub P c.L ⊓ Subgroup.zpowers e = ⊥ :=
      CFSG.GorensteinWalter.inf_eq_bot_of_not_le_of_prime_card
        (zSub P c.L) (Subgroup.zpowers e) hepprime hnot_ep
    have heQ : e ∈ P ⊓ c.L := hEQ heE
    have he_cent : e ∈ Subgroup.centralizer (zSub P c.L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (zSub_le_centralizer P c.L hz) e heQ).symm
    have he_norm : e ∈ Subgroup.normalizer (zSub P c.L : Set G) :=
      Subgroup.centralizer_le_normalizer (zSub P c.L : Set G) he_cent
    have hnormal_e : Subgroup.zpowers e ≤ Subgroup.normalizer (zSub P c.L : Set G) :=
      Subgroup.zpowers_le.mpr he_norm
    have hBcard : Nat.card ↥(zSub P c.L ⊔ Subgroup.zpowers e) = 9 := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (zSub P c.L) (Subgroup.zpowers e) hnormal_e (disjoint_iff.mpr hdisj_Z_e)]
      rw [hZcard, hepcard]
    have hB_le_E : zSub P c.L ⊔ Subgroup.zpowers e ≤ E :=
      sup_le hZE (Subgroup.zpowers_le.mpr heE)
    have hE_eq_B : E = zSub P c.L ⊔ Subgroup.zpowers e := by
      refine (Subgroup.eq_of_le_of_card_ge hB_le_E ?_).symm
      rw [hBcard, hEcard]
    have hE_le_Ce : E ≤ (P ⊓ c.L) ⊓ Subgroup.centralizer ({e} : Set G) := by
      refine le_inf hEQ ?_
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact IsElemAbelian.comm hE hx heE
    have hex_f : ∃ f ∈ (P ⊓ c.L) ⊓ Subgroup.centralizer ({e} : Set G), f ∉ E := by
      by_contra h
      push Not at h
      have hle : (P ⊓ c.L) ⊓ Subgroup.centralizer ({e} : Set G) ≤ E := h
      have hcardle : Nat.card ↥((P ⊓ c.L) ⊓ Subgroup.centralizer ({e} : Set G)) ≤
          Nat.card ↥E :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle)
      rw [hEcard] at hcardle
      have hc := frame_centralizer_card c hON hP heQ heZ
      omega
    obtain ⟨f, hfC, hfE⟩ := hex_f
    have hfQ : f ∈ P ⊓ c.L := hfC.1
    have hf3 : f ^ 3 = 1 := hQexp f hfQ
    have hf1 : f ≠ 1 := by
      intro h
      exact hfE (h.symm ▸ E.one_mem)
    have hford : orderOf f = 3 := orderOf_eq_prime hf3 hf1
    have hfpcard : Nat.card ↥(Subgroup.zpowers f) = 3 := by
      rw [Nat.card_zpowers, hford]
    have hfpprime : Nat.Prime (Nat.card ↥(Subgroup.zpowers f)) := by
      rw [hfpcard]; norm_num
    have hnot_fp : ¬ Subgroup.zpowers f ≤ E := by
      intro hle
      exact hfE (hle (Subgroup.mem_zpowers f))
    have hdisj_E_f : E ⊓ Subgroup.zpowers f = ⊥ :=
      CFSG.GorensteinWalter.inf_eq_bot_of_not_le_of_prime_card
        E (Subgroup.zpowers f) hfpprime hnot_fp
    have hE_le_Cf : E ≤ Subgroup.centralizer ({f} : Set G) := by
      rw [hE_eq_B]
      refine sup_le ?_ ?_
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (zSub_le_centralizer P c.L hz) f hfQ).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hfC.2).symm
    have hf_cent : f ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hE_le_Cf hx)
    have hf_norm : f ∈ Subgroup.normalizer (E : Set G) :=
      Subgroup.centralizer_le_normalizer (E : Set G) hf_cent
    have hnormal_f : Subgroup.zpowers f ≤ Subgroup.normalizer (E : Set G) :=
      Subgroup.zpowers_le.mpr hf_norm
    have hAea : IsElemAbelian 3 (E ⊔ Subgroup.zpowers f) := by
      refine hE.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hf3) ?_
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hcomm : a * f = f * a := Subgroup.mem_centralizer_singleton_iff.mp (hE_le_Cf ha)
      exact ((show Commute a f from hcomm).zpow_right k).eq
    have hAcard : Nat.card ↥(E ⊔ Subgroup.zpowers f) = 27 := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        E (Subgroup.zpowers f) hnormal_f (disjoint_iff.mpr hdisj_E_f)]
      rw [hEcard, hfpcard]
    refine ⟨E ⊔ Subgroup.zpowers f, ⟨hAea, hAcard, hZE.trans le_sup_left,
      sup_le hEQ (Subgroup.zpowers_le.mpr hfQ)⟩, ?_⟩
    exact hyperplane_of_card_nine le_sup_left hEcard hAcard
  ·
    have hdisj_E_Z : E ⊓ zSub P c.L = ⊥ :=
      CFSG.GorensteinWalter.inf_eq_bot_of_not_le_of_prime_card
        E (zSub P c.L) hZprime hZE
    have hcomm : ∀ a ∈ E, ∀ b ∈ zSub P c.L, a * b = b * a := by
      intro a ha b hb
      exact Subgroup.mem_centralizer_iff.mp (zSub_le_centralizer P c.L hb) a (hEQ ha)
    have hZ_le_C_E : zSub P c.L ≤ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      intro a ha b hb
      exact (hcomm a ha b hb).symm
    have hnormal_Z : zSub P c.L ≤ Subgroup.normalizer (E : Set G) :=
      hZ_le_C_E.trans (Subgroup.centralizer_le_normalizer (E : Set G))
    have hAea : IsElemAbelian 3 (E ⊔ zSub P c.L) := by
      refine hE.sup_of_commute (isElemAbelian_zSub c hON hP) ?_
      intro a ha b hb
      exact hcomm a ha b hb
    have hAcard : Nat.card ↥(E ⊔ zSub P c.L) = 27 := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        E (zSub P c.L) hnormal_Z (disjoint_iff.mpr hdisj_E_Z)]
      rw [hEcard, hZcard]
    refine ⟨E ⊔ zSub P c.L, ⟨hAea, hAcard, le_sup_right,
      sup_le hEQ (inf_le_left : zSub P c.L ≤ P ⊓ c.L)⟩, ?_⟩
    exact hyperplane_of_card_nine le_sup_left hEcard hAcard

theorem alpha_const_of_local' {G} [Group G] [Finite G] {D : Data G} (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hlocal : ∀ A : Subgroup G, IsElemAbelian 3 A → Nat.card A = 27 →
      zSub P c.L ≤ A → A ≤ P ⊓ c.L →
      ∀ E ∈ UC22.InS3.hyperplanes 3 A, ∀ E' ∈ UC22.InS3.hyperplanes 3 A,
        thetaAlpha 3 E = thetaAlpha 3 E') :
    ∀ E E' : Subgroup G, E ≤ P → E' ≤ P → IsElemAbelian 3 E → Nat.card E = 9 →
      IsElemAbelian 3 E' → Nat.card E' = 9 → thetaAlpha 3 E = thetaAlpha 3 E' := by
  intro E E' hEP hE'P hEea hEcard hE'ea hE'card
  obtain ⟨A, hA, hEA⟩ := exists_admissible_of_card_nine hON hP hEP hEea hEcard
  obtain ⟨A', hA', hE'A'⟩ := exists_admissible_of_card_nine hON hP hE'P hE'ea hE'card
  exact thetaAlpha_eq_of_admissible hON hP hlocal hA hA' hEA hE'A'

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
