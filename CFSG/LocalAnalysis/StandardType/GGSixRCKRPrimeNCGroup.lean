module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplit
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.Open.QuasithinDefs
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.RCKRP

open Subgroup
open scoped commutatorElement
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)

theorem rck_eq_one_of_perfect_of_central {P : Type*} [Group P] [Group.IsPerfect P]
    (f : P → P) (hc : ∀ y, f y ∈ center P) (hmul : ∀ y z, f (y * z) = f y * f z) (y : P) :
    f y = 1 := by
  have h1 : f 1 = 1 := by
    have h := hmul 1 1
    rw [one_mul] at h
    exact (mul_left_cancel (a := f 1) (by rw [mul_one]; exact h)).symm
  let F : P →* P := { toFun := f, map_one' := h1, map_mul' := hmul }
  let F' : P →* center P := F.codRestrict (center P) hc
  have hker : commutator P ≤ F'.ker := Abelianization.commutator_subset_ker F'
  have htop : F'.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := P)]
    exact hker
  have hy : y ∈ F'.ker := by rw [htop]; exact Subgroup.mem_top y
  have := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
  simpa [F', F] using this

theorem rck_comm_mul {P : Type*} [Group P] (x y z : P) (hz : ⁅x, z⁆ ∈ center P) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have h : y * ⁅x, z⁆ = ⁅x, z⁆ * y := Subgroup.mem_center_iff.mp hz y
  have h2 : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [h2, h]; group

theorem rck_ker_comp_le_center {P Q Y : Type*} [Group P] [Group Q] [Group Y] [Group.IsPerfect P]
    (f : P →* Q) (g : Q →* Y) (hf : f.ker ≤ center P) (hg : g.ker ≤ center Q) :
    (g.comp f).ker ≤ center P := by
  intro x hx
  have hfx : f x ∈ center Q := hg hx
  have hcomm : ∀ y : P, ⁅x, y⁆ ∈ center P := fun y => by
    apply hf
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have h := Subgroup.mem_center_iff.mp hfx (f y)
    simp only [commutatorElement_def]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact h.symm
  have hmul : ∀ y z : P, ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := fun y z => rck_comm_mul x y z (hcomm z)
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  have h1 := rck_eq_one_of_perfect_of_central (fun y => ⁅x, y⁆) hcomm hmul y
  simp only [commutatorElement_def] at h1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem rck_conj_commutes_of_central {X : Type*} [Group X] (K : Subgroup X) [Group.IsPerfect ↥K]
    (d : X) (hd : d ∈ Subgroup.normalizer (K : Set X))
    (h : ∀ (x : ↥K) (hx : d * (x : X) * d⁻¹ ∈ K),
      (⟨d * (x : X) * d⁻¹, hx⟩ : ↥K) * x⁻¹ ∈ center ↥K) (x : ↥K) :
    d * (x : X) * d⁻¹ = (x : X) := by
  have hmem : ∀ x : ↥K, d * (x : X) * d⁻¹ ∈ K := fun x =>
    (Subgroup.mem_normalizer_iff.mp hd (x : X)).mp x.2
  let F : ↥K → ↥K := fun x => ⟨d * (x : X) * d⁻¹, hmem x⟩ * x⁻¹
  have hF : ∀ y, F y ∈ center ↥K := fun y => h y (hmem y)
  have hmul : ∀ y z, F (y * z) = F y * F z := fun y z => by
    have hz := congrArg Subtype.val (Subgroup.mem_center_iff.mp (hF z) y)
    apply Subtype.ext
    simp only [F, Subgroup.coe_mul, Subgroup.coe_inv] at hz ⊢
    have hW : (y : X) * (d * (z : X) * d⁻¹ * (z : X)⁻¹) * (y : X)⁻¹ =
        d * (z : X) * d⁻¹ * (z : X)⁻¹ := by
      rw [hz]; group
    calc d * ((y : X) * (z : X)) * d⁻¹ * ((y : X) * (z : X))⁻¹
        = (d * (y : X) * d⁻¹ * (y : X)⁻¹) *
            ((y : X) * (d * (z : X) * d⁻¹ * (z : X)⁻¹) * (y : X)⁻¹) := by group
      _ = (d * (y : X) * d⁻¹ * (y : X)⁻¹) * (d * (z : X) * d⁻¹ * (z : X)⁻¹) := by rw [hW]
  have h1 := rck_eq_one_of_perfect_of_central F hF hmul x
  have h2 := congrArg Subtype.val h1
  simp only [F, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
  rw [mul_inv_eq_one] at h2
  exact h2

theorem rck_exists_lift {X Y : Type} [Group X] [Finite X] [Group Y] (K J : Subgroup X)
    (hJK : J ≤ K) [Group.IsPerfect ↥J] (c : ↥K →* Y) (hcen : c.ker ≤ center ↥K)
    (hodd : Odd (Nat.card (center ↥K))) (M : Type) [Group M] [Finite M] (hM : OddCentralSplit M)
    (φ : M →* Y) (hrange : φ.range = (J.subgroupOf K).map c) :
    ∃ α : M →* ↥J, Function.Surjective α ∧ ∀ s, c ⟨(α s : X), hJK (α s).2⟩ = φ s := by
  have hmem : ∀ s : M, φ s ∈ (J.subgroupOf K).map c := fun s => by
    rw [← hrange]; exact ⟨s, rfl⟩
  let β : M →* ↥((J.subgroupOf K).map c) := φ.codRestrict _ hmem
  let η : ↥J →* ↥((J.subgroupOf K).map c) := (c.comp (Subgroup.inclusion hJK)).codRestrict _
    (fun x => ⟨⟨(x : X), hJK x.2⟩, (Subgroup.mem_subgroupOf).2 x.2, rfl⟩)
  have hβ : Function.Surjective β := by
    intro q
    have hq : (q : Y) ∈ φ.range := by rw [hrange]; exact q.2
    obtain ⟨s, hs⟩ := hq
    exact ⟨s, Subtype.ext hs⟩
  have hη : Function.Surjective η := by
    intro q
    obtain ⟨k, hk, hkq⟩ := q.2
    exact ⟨⟨(k : X), (Subgroup.mem_subgroupOf).1 hk⟩, Subtype.ext hkq⟩
  have hker1 : ∀ y : ↥J, y ∈ η.ker → c ⟨(y : X), hJK y.2⟩ = 1 := fun y hy => by
    have h1 : η y = 1 := hy
    have h2 : ((η y : ↥((J.subgroupOf K).map c)) : Y) = 1 := by rw [h1]; rfl
    exact h2
  have hηker : η.ker ≤ center ↥J := by
    intro x hx
    have hxK : (⟨(x : X), hJK x.2⟩ : ↥K) ∈ center ↥K := hcen (hker1 x hx)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have := Subgroup.mem_center_iff.mp hxK ⟨(y : X), hJK y.2⟩
    simpa using congrArg Subtype.val this
  have hηodd : Odd (Nat.card η.ker) := by
    let f : η.ker →* center ↥K :=
      { toFun := fun y => ⟨⟨((y : ↥J) : X), hJK (y : ↥J).2⟩, hcen (hker1 y y.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun y y' h => by
      have h1 : ((y : ↥J) : X) = ((y' : ↥J) : X) :=
        congrArg (fun z : ↥(center ↥K) => ((z : ↥K) : X)) h
      exact Subtype.ext (Subtype.ext h1)
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)
  obtain ⟨α, hα, hαs, -⟩ :=
    CFSG.SeitzReduction.SeitzQ2.exists_surjective_of_oddCentralSplit hM hβ hη hηker hηodd
  refine ⟨α, hαs, fun s => ?_⟩
  have h := congrArg Subtype.val (hα s)
  exact h

theorem rck_map_conj_map {M Y : Type*} [Group M] [Group Y] (U : Subgroup M) (u : M) (φ : M →* Y) :
    (U.map (MulAut.conj u).toMonoidHom).map φ = (U.map φ).map (MulAut.conj (φ u)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem rck_rootUnique {Y K : Type*} [Group Y] [Group K] [Finite K] (c : K →* Y)
    (hcen : c.ker ≤ center K) (hodd : Odd (Nat.card c.ker)) (T T' : Subgroup K)
    (hT : IsPGroup 2 T) (hT' : IsPGroup 2 T') (h : T.map c = T'.map c) : T = T' := by
  have key : ∀ (A B : Subgroup K), IsPGroup 2 A → IsPGroup 2 B → A.map c ≤ B.map c → A ≤ B := by
    intro A B hA hB hAB t ht
    obtain ⟨t', ht', hct⟩ := hAB ⟨t, ht, rfl⟩
    set z : K := t'⁻¹ * t with hz
    have hzk : z ∈ c.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hct, inv_mul_cancel]
    have hzc : z ∈ center K := hcen hzk
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hA) ⟨t, ht⟩
    obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hB) ⟨t', ht'⟩
    have hta : t ^ (2 ^ a) = 1 := by
      have := pow_orderOf_eq_one (⟨t, ht⟩ : A)
      rw [ha] at this
      exact congrArg Subtype.val this
    have htb : t' ^ (2 ^ b) = 1 := by
      have := pow_orderOf_eq_one (⟨t', ht'⟩ : B)
      rw [hb] at this
      exact congrArg Subtype.val this
    have htt : t = t' * z := by rw [hz]; group
    have hcomm : Commute t' z := Subgroup.mem_center_iff.mp hzc t'
    have hzpow : z ^ (2 ^ (a + b)) = 1 := by
      have e1 : t ^ (2 ^ (a + b)) = 1 := by
        rw [pow_add, pow_mul]; simp [hta]
      have e2 : t' ^ (2 ^ (a + b)) = 1 := by
        rw [add_comm, pow_add, pow_mul]; simp [htb]
      have e3 : t ^ (2 ^ (a + b)) = t' ^ (2 ^ (a + b)) * z ^ (2 ^ (a + b)) := by
        rw [htt]; exact hcomm.mul_pow _
      rw [e1, e2, one_mul] at e3
      exact e3.symm
    have hdvd1 : orderOf z ∣ 2 ^ (a + b) := orderOf_dvd_of_pow_eq_one hzpow
    have hdvd2 : orderOf z ∣ Nat.card c.ker := by
      have : orderOf (⟨z, hzk⟩ : c.ker) ∣ Nat.card c.ker := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ (a + b)) (Nat.card c.ker) :=
      (Nat.Coprime.pow_right _ (Odd.coprime_two_right hodd)).symm
    have : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    have hz1 : z = 1 := orderOf_eq_one_iff.mp this
    rw [htt, hz1, mul_one]
    exact ht'
  exact le_antisymm (key T T' hT hT' h.le) (key T' T hT' hT h.ge)

end CFSG.StandardType.RCKRP
