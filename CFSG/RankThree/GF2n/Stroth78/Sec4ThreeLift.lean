module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar

import CFSG.GroupTheory.OddOrderLift
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
import CFSG.RankThree.GF2n.Stroth78.Sec3Three
import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeZQ

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G} {S : Setting z E F}

noncomputable abbrev CH (a : G) : Subgroup (Hbar z) :=
  ((Subgroup.centralizer ({a} : Set G)).subgroupOf (H z)).map
    (QuotientGroup.mk' ((Q z).subgroupOf (H z)))

noncomputable abbrev preimageInH (P : Subgroup (Hbar z)) : Subgroup ↥(H z) :=
  P.comap (QuotientGroup.mk' ((Q z).subgroupOf (H z)))

theorem map_La_eq_of_mem_centralizer (S : Setting z E F) {a x : G} (hxH : x ∈ H z)
    (hxa : x ∈ Subgroup.centralizer ({a} : Set G)) :
    (La S a).map (MulAut.conj x).toMonoidHom = La S a := by
  have hxa' : x * a * x⁻¹ = a := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hxa
    calc
      x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [h]
      _ = a := by group
  have hQmap : (Q z).map (MulAut.conj x).toMonoidHom = Q z := by
    simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer_of_normal_subgroupOf (Q_le_H S) hxH)
  have hQamap : (QaOf a).map (MulAut.conj x).toMonoidHom = QaOf a := by
    have hcent : (Subgroup.centralizer ({a} : Set G)).map
        (MulAut.conj x).toMonoidHom = Subgroup.centralizer ({a} : Set G) := by
      simpa [hxa'] using (centralizer_map_conj a x).symm
    show (fStar (Subgroup.centralizer ({a} : Set G))).map
      (MulAut.conj x).toMonoidHom = _
    rw [← fStar_map_conj (Subgroup.centralizer ({a} : Set G)) x, hcent]
    rfl
  have hzfix : x * z * x⁻¹ = z := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hxH
    calc
      x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [h]
      _ = z := by group
  have hHmap : (H z).map (MulAut.conj x).toMonoidHom = H z := by
    change (Subgroup.centralizer ({z} : Set G)).map
      (MulAut.conj x).toMonoidHom = Subgroup.centralizer ({z} : Set G)
    rw [← centralizer_map_conj z x, hzfix]
  rw [La, Subgroup.map_sup, Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective,
    hQmap, hQamap, hHmap]

theorem CH_le_normalizer_Lbar (S : Setting z E F) (a : G) :
    CH (z := z) a ≤ Subgroup.normalizer (Lbar S a : Set (Hbar z)) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxH : (x : G) ∈ H z := x.2
  have hxa : (x : G) ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_subgroupOf.mp hx
  have hLamap := map_La_eq_of_mem_centralizer S hxH hxa
  have hxNG : (x : G) ∈ Subgroup.normalizer (La S a : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa using hLamap)
  have hxN : x ∈ Subgroup.normalizer ((La S a).subgroupOf (H z) : Set ↥(H z)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hy := Subgroup.mem_normalizer_iff.mp hxNG (y : G)
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hy
  have hmap : QuotientGroup.mk' ((Q z).subgroupOf (H z)) x ∈
      Subgroup.normalizer (((La S a).subgroupOf (H z)).map
        (QuotientGroup.mk' ((Q z).subgroupOf (H z))) : Set (Hbar z)) :=
    Subgroup.le_normalizer_map (f := QuotientGroup.mk' ((Q z).subgroupOf (H z)))
      (H := (La S a).subgroupOf (H z)) (Subgroup.mem_map_of_mem _ hxN)
  simpa [Lbar] using hmap

theorem mem_ZQ_of_rhoLin_apply_aVec_eq (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    {x : G} (hxH : x ∈ H z)
    (hfix : rhoLin S (QuotientGroup.mk ⟨x, hxH⟩) (aVec S haQ) = aVec S haQ) :
    x * a * x⁻¹ * a⁻¹ ∈ ZQ z := by
  have hfix' : conjQbar S ⟨x, hxH⟩ (aVec S haQ) = aVec S haQ := by
    simpa [rhoLin, rhoBar_apply_mk, rho_apply_mk] using hfix
  have hfix'' : conjQbar S ⟨x, hxH⟩ (Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩)) =
      Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩) := by
    simpa [aVec, mkQbar, QuotientGroup.mk'_apply] using hfix'
  rw [conjQbar_apply_mk] at hfix''
  have hq : (QuotientGroup.mk (conjAutQ S ⟨x, hxH⟩ ⟨a, haQ⟩) : QbarOf S) =
      QuotientGroup.mk ⟨a, haQ⟩ := Additive.ofMul.injective hfix''
  have hmem := (QuotientGroup.eq_iff_div_mem).mp hq
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa [conjAutQ_apply, div_eq_mul_inv] using hmem

theorem exists_monoidHom_preimage_commutator {a : G} {P : Subgroup (Hbar z)}
    (hPZ : ∀ x : ↥(H z), QuotientGroup.mk x ∈ P → ∀ v ∈ ZQ z,
      (x : G) * v * (x : G)⁻¹ = v)
    (hmemZ : ∀ x : ↥(preimageInH P),
      (x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹ ∈ ZQ z) :
    ∃ φ : ↥(preimageInH P) →* ↥(ZQ z),
      ∀ x, (φ x : G) = (x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹ := by
  classical
  let Phat : Subgroup ↥(H z) := preimageInH P
  let φ : ↥Phat →* ↥(ZQ z) :=
    { toFun := fun x => ⟨(x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹, hmemZ x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        have htriv := hPZ x.1 (Subgroup.mem_comap.mp x.2)
          ((y.1 : G) * a * (y.1 : G)⁻¹ * a⁻¹) (hmemZ y)
        have hy_eq : (y.1 : G) * a * (y.1 : G)⁻¹ =
            ((y.1 : G) * a * (y.1 : G)⁻¹ * a⁻¹) * a := by group
        have hcomm : ((y.1 : G) * a * (y.1 : G)⁻¹ * a⁻¹) *
            ((x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹) =
              ((x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹) *
                ((y.1 : G) * a * (y.1 : G)⁻¹ * a⁻¹) := by
          have hxZ := hmemZ x
          have hyZ := hmemZ y
          exact Subgroup.mem_centralizer_iff.mp hxZ.2
            ((y.1 : G) * a * (y.1 : G)⁻¹ * a⁻¹) hyZ.1
        calc
          (((x.1 : G) * (y.1 : G)) * a * (((x.1 : G) * (y.1 : G))⁻¹) * a⁻¹)
              = (x.1 : G) * ((y.1 : G) * a * (y.1 : G)⁻¹) * (x.1 : G)⁻¹ * a⁻¹ := by
                group
          _ = (x.1 : G) *
                (((y.1 : G) * a * (y.1 : G)⁻¹ * a⁻¹) * a) * (x.1 : G)⁻¹ * a⁻¹ := by
                nth_rewrite 1 [hy_eq]
                rfl
          _ = ((x.1 : G) * ((y.1 : G) * a * (y.1 : G)⁻¹ * a⁻¹) * (x.1 : G)⁻¹) *
                ((x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹) := by
                have hgen : ∀ (X Cy c : G), X * (Cy * c) * X⁻¹ * c⁻¹ =
                    (X * Cy * X⁻¹) * (X * c * X⁻¹ * c⁻¹) := by
                  intro X Cy c
                  group
                exact hgen (x.1 : G) ((y.1 : G) * a * (y.1 : G)⁻¹ * a⁻¹) a
          _ = ((y.1 : G) * a * (y.1 : G)⁻¹ * a⁻¹) *
                ((x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹) := by
                rw [htriv]
          _ = ((x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹) *
                ((y.1 : G) * a * (y.1 : G)⁻¹ * a⁻¹) := hcomm }
  exact ⟨φ, fun x => rfl⟩

theorem commutator_le_CH_of_fixes {a : G} (haQ : a ∈ Q z) {P : Subgroup (Hbar z)}
    (hfix : ∀ y ∈ P, rhoLin S y (aVec S haQ) = aVec S haQ)
    (hPZ : ∀ x : ↥(H z), QuotientGroup.mk x ∈ P → ∀ v ∈ ZQ z,
      (x : G) * v * (x : G)⁻¹ = v) :
    ⁅P, P⁆ ≤ CH a := by
  classical
  let f : ↥(H z) →* Hbar z := QuotientGroup.mk' ((Q z).subgroupOf (H z))
  let Phat : Subgroup ↥(H z) := preimageInH P
  have hmemZ : ∀ x : ↥Phat, (x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹ ∈ ZQ z := by
    intro x
    exact mem_ZQ_of_rhoLin_apply_aVec_eq S haQ x.1.2
      (hfix (f x.1) (Subgroup.mem_comap.mp x.2))
  obtain ⟨φ, hφ⟩ := exists_monoidHom_preimage_commutator (P := P) hPZ hmemZ
  have : IsMulCommutative ↥(ZQ z) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp x.2.2 (y : G) y.2.1).symm
  have hker_le : ⁅Phat, Phat⁆ ≤ φ.ker.map Phat.subtype := by
    rw [← Subgroup.map_subtype_commutator Phat]
    exact Subgroup.map_mono (Abelianization.commutator_subset_ker φ)
  have hmapP : Phat.map f = P :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) P
  have hPker_le : (φ.ker.map Phat.subtype) ≤
      (Subgroup.centralizer ({a} : Set G)).subgroupOf (H z) := by
    rintro y ⟨x, hx, rfl⟩
    have hx1 : (x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹ = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rw [hφ x] at h
      simpa using h
    have hx1' : (x.1 : G) * a * (x.1 : G)⁻¹ = a := by
      have h := congrArg (fun t => t * a) hx1
      simpa [mul_assoc] using h
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      (x.1 : G) * a = ((x.1 : G) * a * (x.1 : G)⁻¹) * (x.1 : G) := by group
      _ = a * (x.1 : G) := by rw [hx1']
  calc
    ⁅P, P⁆ = (⁅Phat, Phat⁆).map f := by
      rw [Subgroup.map_commutator, hmapP]
    _ ≤ (φ.ker.map Phat.subtype).map f := Subgroup.map_mono hker_le
    _ ≤ CH a := Subgroup.map_mono hPker_le

theorem le_CH_of_perfect {a : G} {w : ℕ} (h : Sec3Hyp S a w) {P : Subgroup (Hbar z)}
    (hP : ⁅P, P⁆ = P) {α : Hbar z} (hαA : α ∈ A2set S)
    (haα : aVec S h.mem_Q ∈ commSpace (rhoLin S α))
    (hPα : ∀ y ∈ P, y * α = α * y)
    (hPZ : ∀ x : ↥(H z), QuotientGroup.mk x ∈ P → ∀ v ∈ ZQ z,
      (x : G) * v * (x : G)⁻¹ = v) :
    P ≤ CH a := by
  have hfixP : ∀ y ∈ P, rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q :=
    fun y hy => rhoLin_apply_eq_self_of_perfect S hP hαA hPα y hy (aVec S h.mem_Q) haα
  rw [← hP]
  exact commutator_le_CH_of_fixes h.mem_Q hfixP hPZ

theorem le_CH_of_oddOrderClosure {a : G} (haQ : a ∈ Q z) {P : Subgroup (Hbar z)}
    (hfix : ∀ y ∈ P, rhoLin S y (aVec S haQ) = aVec S haQ)
    (hPZ : ∀ x : ↥(H z), QuotientGroup.mk x ∈ P → ∀ v ∈ ZQ z,
      (x : G) * v * (x : G)⁻¹ = v)
    (hodd : CFSG.GroupTheory.oddOrderClosure P = P) :
    P ≤ CH a := by
  classical
  rw [← hodd, CFSG.GroupTheory.oddOrderClosure_le_iff]
  rintro y ⟨hyP, hyodd⟩
  let f : ↥(H z) →* Hbar z := QuotientGroup.mk' ((Q z).subgroupOf (H z))
  let Phat : Subgroup ↥(H z) := preimageInH P
  let g : ↥Phat →* ↥P :=
    { toFun := fun x => ⟨f x.1, Subgroup.mem_comap.mp x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f x.1 y.1) }
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective ((Q z).subgroupOf (H z)) (y : Hbar z)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    exact Subgroup.mem_comap.mpr (by rw [hx]; exact y.2)
  have hmemZ : ∀ x : ↥Phat, (x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹ ∈ ZQ z := by
    intro x
    exact mem_ZQ_of_rhoLin_apply_aVec_eq S haQ x.1.2
      (hfix (f x.1) (Subgroup.mem_comap.mp x.2))
  obtain ⟨φ, hφ⟩ := exists_monoidHom_preimage_commutator (P := P) hPZ hmemZ
  have hyoddP : Odd (orderOf (⟨y, hyP⟩ : ↥P)) := by
    rwa [Subgroup.orderOf_mk]
  obtain ⟨x, hx, hxodd⟩ := CFSG.GroupTheory.exists_odd_orderOf_preimage g hg hyoddP
  have hoddφ : Odd (orderOf (φ x)) := hxodd.of_dvd_nat (orderOf_map_dvd φ x)
  have hsq : φ x * φ x = 1 := ZQ_mul_self S (φ x)
  have hdvd : orderOf (φ x) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
  have hφ1 : φ x = 1 :=
    orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hoddφ.coprime_two_right hdvd)
  have hval : (x.1 : G) * a * (x.1 : G)⁻¹ * a⁻¹ = 1 := by
    have h := congrArg (fun u : ↥(ZQ z) => (u : G)) hφ1
    rw [hφ x] at h
    simpa using h
  have hcent : (x.1 : G) ∈ Subgroup.centralizer ({a} : Set G) := by
    have hx1' : (x.1 : G) * a * (x.1 : G)⁻¹ = a := by
      have h := congrArg (fun t => t * a) hval
      simpa [mul_assoc] using h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      (x.1 : G) * a = ((x.1 : G) * a * (x.1 : G)⁻¹) * (x.1 : G) := by group
      _ = a * (x.1 : G) := by rw [hx1']
  have hxval : f x.1 = y := congrArg Subtype.val hx
  rw [← hxval]
  exact Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hcent)

theorem mem_A2set_and_aVec_mem_of_mem_Rbar {a : G} {w : ℕ} (h : Sec3Hyp S a w) {α : Hbar z}
    (hα : α ∈ Rbar S a) (hα1 : α ≠ 1) :
    α ∈ A2set S ∧ aVec S h.mem_Q ∈ commSpace (rhoLin S α) :=
  ⟨Tset_subset_A2set S a (h.mem_Tset_of_mem_Rbar hα hα1),
    aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
      h.centerIn_Qa_not_le_Q hα hα1⟩

end CFSG.RankThree.GF2n.Stroth78
