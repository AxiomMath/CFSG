module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res10ProofGTwo
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47fCenter
import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eOmega

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

namespace Proof17Res10

theorem three_eq_zero_of_dvd_card {K : Type} [Field K] [Finite K] (h : 3 ∣ Nat.card K) :
    (3 : K) = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' 3 h
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    norm_num at hx
  have h3x : (3 : K) * x = 0 := by
    have := addOrderOf_nsmul_eq_zero x
    rw [hx, nsmul_eq_mul] at this
    exact_mod_cast this
  exact (mul_eq_zero.mp h3x).resolve_right hx0

theorem hasCommOfZ_of_witness {X : Type*} [Group X] [Finite X] {Z : Subgroup X}
    (S : Sylow 3 X) (hcen : ∀ z ∈ Z, ∀ u ∈ (S : Subgroup X), u * z = z * u) {x y z₀ : X}
    (hx : x ∈ (S : Subgroup X)) (hy : y ∈ (S : Subgroup X)) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : ⁅x, y⁆ = z₀) (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) : Proof176Steps.HasCommOfZ Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨x, y, hx3, hy3, ?_, ?_, hxy ▸ hz₀, hxy ▸ hz₀1, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    exact fun z hz => (hcen z hz x hx).symm
  · rw [Subgroup.mem_centralizer_iff]
    exact fun z hz => (hcen z hz y hy).symm
  · refine (S.isPGroup').to_le ?_
    rw [Subgroup.closure_le]
    intro a ha
    rcases ha with rfl | ha
    · exact hx
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hy

open GH74.GLS.IVK.Proofs2.Ivk47 in
theorem pinnedX_pow_three
    {K : Type} [Field K] (h3 : (3 : K) = 0) (α : Fin Tag.G2.rank → ℤ) (x : K) :
    pinnedX .G2 K α x ^ 3 = 1 := by
  rw [pow_succ, pow_two, ← pinnedX_add, ← pinnedX_add]
  have : x + x + x = 0 := by linear_combination x * h3
  rw [this, pinnedX_zero]

@[expose] def i₀ : Fin Tag.G2.rank := ⟨0, by decide⟩

theorem cartan_sum_v : ∑ j, Tag.G2.cartan i₀ j * (![1, 2] : Fin Tag.G2.rank → ℤ) j = 0 := by
  decide +kernel

theorem cartan_sum_c : ∑ j, Tag.G2.cartan i₀ j * (![2, 3] : Fin Tag.G2.rank → ℤ) j = 1 := by
  decide +kernel

open GH74.GLS.IVK.Proofs2.Ivk47 in
theorem isRoot_v : IsRoot .G2 ![1, 2] :=
  (mem_posRootList_iff.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))).1

open GH74.GLS.IVK.Proofs2.Ivk47 in
theorem isRoot_c : IsRoot .G2 ![2, 3] :=
  (mem_posRootList_iff.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))))))).1

open GH74.GLS.IVK.Proofs2.Ivk47 in
theorem torus_conj_Xv_Xc {K : Type}
    [Field K] (s t : K) :
    torusElt .G2 K i₀ (-1) * (Xv s * Xc t) * (torusElt .G2 K i₀ (-1))⁻¹ = Xv s * Xc (-t) := by
  have hv : torusElt .G2 K i₀ (-1) * Xv s * (torusElt .G2 K i₀ (-1))⁻¹ = Xv s := by
    show torusElt .G2 K i₀ (-1) * pinnedX .G2 K ![1, 2] s * (torusElt .G2 K i₀ (-1))⁻¹ =
      pinnedX .G2 K ![1, 2] s
    rw [root_torus_conjugation i₀ isRoot_v, cartan_sum_v, zpow_zero, Units.val_one, one_mul]
  have hc : torusElt .G2 K i₀ (-1) * Xc t * (torusElt .G2 K i₀ (-1))⁻¹ = Xc (-t) := by
    show torusElt .G2 K i₀ (-1) * pinnedX .G2 K ![2, 3] t * (torusElt .G2 K i₀ (-1))⁻¹ =
      pinnedX .G2 K ![2, 3] (-t)
    rw [root_torus_conjugation i₀ isRoot_c, cartan_sum_c, zpow_one, Units.val_neg, Units.val_one,
      neg_one_mul]
  calc torusElt .G2 K i₀ (-1) * (Xv s * Xc t) * (torusElt .G2 K i₀ (-1))⁻¹
      = (torusElt .G2 K i₀ (-1) * Xv s * (torusElt .G2 K i₀ (-1))⁻¹) *
          (torusElt .G2 K i₀ (-1) * Xc t * (torusElt .G2 K i₀ (-1))⁻¹) := by group
    _ = Xv s * Xc (-t) := by rw [hv, hc]

section Three


open GH74.GLS.IVK.Proofs2.Ivk47 in
theorem exists_comm_Xv {K : Type} [Field K] (h3 : (3 : K) = 0) (s : K) :
    ∃ x₀ ∈ posUnipotent .G2 K, ∃ y₀ ∈ posUnipotent .G2 K,
      x₀ ^ 3 = 1 ∧ y₀ ^ 3 = 1 ∧ ⁅x₀, y₀⁆ = Xv s := by
  obtain ⟨e, he, hrel⟩ := rel_ru h3 (K := K)
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  refine ⟨Xr 1, Xr_mem 1, Xu (e * s), Xu_mem _, pinnedX_pow_three h3 ![0, 1] 1,
    pinnedX_pow_three h3 ![1, 1] (e * s), ?_⟩
  rw [hrel]
  congr 1
  linear_combination s * hee

open GH74.GLS.IVK.Proofs2.Ivk47 in
theorem exists_comm_Xc {K : Type} [Field K] (h3 : (3 : K) = 0) (t : K) :
    ∃ x₀ ∈ posUnipotent .G2 K, ∃ y₀ ∈ posUnipotent .G2 K,
      x₀ ^ 3 = 1 ∧ y₀ ^ 3 = 1 ∧ ⁅x₀, y₀⁆ = Xc t := by
  obtain ⟨e, he, hrel⟩ := rel_ab (K := K)
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  refine ⟨Xa 1, Xa_mem 1, Xb (e * t), Xb_mem _, pinnedX_pow_three h3 ![1, 0] 1,
    pinnedX_pow_three h3 ![1, 3] (e * t), ?_⟩
  rw [hrel]
  congr 1
  linear_combination t * hee

open GH74.GLS.IVK.Proofs2.Ivk47 in
theorem ks176GTwoChevThree_holds : KS176GTwoChevThree := by
  intro K _ _ h3K Z hZ3 hwc
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (3 : K) = 0 := three_eq_zero_of_dvd_card h3K
  have : CharP K 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr (by exact_mod_cast h3)
  have h2 : (2 : K) ≠ 0 := by
    intro h
    exact one_ne_zero (by linear_combination h3 - h : (1 : K) = 0)
  obtain ⟨S, hZS, hcen⟩ := exists_sylow_of_weaklyClosed hZ3 hwc
  have hUC : posUnipotent .G2 K ≤ adjointGroup .G2 K := posUnipotent_le_adjointGroup' .G2 K
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 3 hUC card_posUnipotent
  let PU : Sylow 3 ↥(adjointGroup .G2 K) := hUp.toSylow hUi
  have hPU : (PU : Subgroup ↥(adjointGroup .G2 K)) =
      (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) := IsPGroup.toSylow_coe hUp hUi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(adjointGroup .G2 K) PU S
  have hS : (S : Subgroup ↥(adjointGroup .G2 K)) =
      (PU : Subgroup ↥(adjointGroup .G2 K)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  let ι : ∀ u : ModGL .G2 K, u ∈ posUnipotent .G2 K → ↥(adjointGroup .G2 K) :=
    fun u hu => ⟨u, hUC hu⟩
  have hmemS : ∀ (u : ModGL .G2 K) (hu : u ∈ posUnipotent .G2 K),
      g * ι u hu * g⁻¹ ∈ (S : Subgroup ↥(adjointGroup .G2 K)) := fun u hu => by
    rw [hS, hPU]
    exact ⟨ι u hu, hu, rfl⟩
  have hSmem : ∀ w ∈ (S : Subgroup ↥(adjointGroup .G2 K)),
      ∃ (u : ModGL .G2 K) (hu : u ∈ posUnipotent .G2 K), w = g * ι u hu * g⁻¹ := by
    intro w hw
    rw [hS, hPU] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨v, hv, rfl⟩
  obtain ⟨z₀, hz₀, hz₀1⟩ := Proof176Steps.exists_ne_one_of_card_three hZ3
  have hZz : Z = Subgroup.zpowers z₀ := Proof176Steps.eq_zpowers_of_card_three hZ3 hz₀ hz₀1
  obtain ⟨u₀, hu₀, hz₀eq⟩ := hSmem z₀ (hZS hz₀)
  have hu₀c : ∀ h ∈ posUnipotent .G2 K, h * u₀ = u₀ * h := by
    intro h hh
    have h1 := hcen z₀ hz₀ (g * ι h hh * g⁻¹) (hmemS h hh)
    rw [hz₀eq] at h1
    have h2 : ι h hh * ι u₀ hu₀ = ι u₀ hu₀ * ι h hh := by
      have := congrArg (fun w => g⁻¹ * w * g) h1
      simpa [mul_assoc] using this
    exact congrArg Subtype.val h2
  obtain ⟨s, t, hst⟩ := eq_Xv_Xc_of_central h3 hu₀ hu₀c
  have hst1 : ¬ (s = 0 ∧ t = 0) := by
    rintro ⟨rfl, rfl⟩
    apply hz₀1
    rw [hz₀eq]
    have : ι u₀ hu₀ = 1 := Subtype.ext (show u₀ = (1 : ModGL .G2 K) by
      rw [hst, Xv_zero, Xc_zero, one_mul])
    rw [this, mul_one, mul_inv_cancel]
  have key : ∀ (x₀ y₀ : ModGL .G2 K) (hx₀ : x₀ ∈ posUnipotent .G2 K)
      (hy₀ : y₀ ∈ posUnipotent .G2 K), x₀ ^ 3 = 1 → y₀ ^ 3 = 1 → ⁅x₀, y₀⁆ = u₀ →
        Proof176Steps.HasCommOfZ Z := by
    intro x₀ y₀ hx₀ hy₀ hx3 hy3 hxy
    refine hasCommOfZ_of_witness S hcen (hmemS x₀ hx₀) (hmemS y₀ hy₀) ?_ ?_ ?_ hz₀ hz₀1
    · rw [conj_pow, show ι x₀ hx₀ ^ 3 = 1 from Subtype.ext (by simpa using hx3), mul_one,
        mul_inv_cancel]
    · rw [conj_pow, show ι y₀ hy₀ ^ 3 = 1 from Subtype.ext (by simpa using hy3), mul_one,
        mul_inv_cancel]
    · have hc : ⁅ι x₀ hx₀, ι y₀ hy₀⁆ = ι u₀ hu₀ := Subtype.ext (show ⁅x₀, y₀⁆ = u₀ from hxy)
      rw [hz₀eq, ← hc]
      simp only [commutatorElement_def]
      group
  by_cases ht : t = 0
  ·
    obtain ⟨x₀, hx₀, y₀, hy₀, hx3, hy3, hxy⟩ := exists_comm_Xv h3 s
    refine key x₀ y₀ hx₀ hy₀ hx3 hy3 ?_
    rw [hxy, hst, ht, Xc_zero, mul_one]
  by_cases hs : s = 0
  ·
    obtain ⟨x₀, hx₀, y₀, hy₀, hx3, hy3, hxy⟩ := exists_comm_Xc h3 t
    refine key x₀ y₀ hx₀ hy₀ hx3 hy3 ?_
    rw [hxy, hst, hs, Xv_zero, one_mul]
  exfalso
  set h₀ : ↥(adjointGroup .G2 K) := ⟨torusElt .G2 K i₀ (-1), torusElt_mem_adjointGroup i₀ (-1)⟩
    with hh₀
  have hu₁ : Xv s * Xc (-t) ∈ posUnipotent .G2 K := mem_Xv_Xc_posUnipotent s (-t)
  set k := g * h₀ * g⁻¹ with hk
  set z₁ := g * ι (Xv s * Xc (-t)) hu₁ * g⁻¹ with hz₁
  have hkz : k * z₀ * k⁻¹ = z₁ := by
    have hh : h₀ * ι u₀ hu₀ * h₀⁻¹ = ι (Xv s * Xc (-t)) hu₁ := Subtype.ext (by
      show torusElt .G2 K i₀ (-1) * u₀ * (torusElt .G2 K i₀ (-1))⁻¹ = Xv s * Xc (-t)
      rw [hst, torus_conj_Xv_Xc])
    rw [hk, hz₀eq, hz₁, ← hh]
    group
  have hz₁C : z₁ ∈ Subgroup.normalizer (Z : Set ↥(adjointGroup .G2 K)) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hSmem z (hZS hz)
    rw [hz₁]
    have hcomm : ι w hw * ι (Xv s * Xc (-t)) hu₁ = ι (Xv s * Xc (-t)) hu₁ * ι w hw :=
      Subtype.ext ((Xv_central h3 s w hw).mul_left (Xc_central (-t) w hw)).eq.symm
    calc g * ι w hw * g⁻¹ * (g * ι (Xv s * Xc (-t)) hu₁ * g⁻¹)
        = g * (ι w hw * ι (Xv s * Xc (-t)) hu₁) * g⁻¹ := by group
      _ = g * (ι (Xv s * Xc (-t)) hu₁ * ι w hw) * g⁻¹ := by rw [hcomm]
      _ = g * ι (Xv s * Xc (-t)) hu₁ * g⁻¹ * (g * ι w hw * g⁻¹) := by group
  have hmapk : Z.map (MulAut.conj k).toMonoidHom = Subgroup.zpowers z₁ := by
    rw [hZz, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hkz
  have hZk := hwc k (by
    rw [hmapk, Subgroup.zpowers_le]
    exact hz₁C)
  have hz₁Z : z₁ ∈ Subgroup.zpowers z₀ := by
    rw [← hZz, ← hZk, hmapk]
    exact Subgroup.mem_zpowers z₁
  have hoz : orderOf z₀ = 3 := by
    rw [← Nat.card_zpowers, ← hZz, hZ3]
  obtain ⟨n, hn, hzn⟩ : ∃ n : ℕ, n < 3 ∧ z₀ ^ n = z₁ := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz₁Z
    refine ⟨(m % 3).toNat, by omega, ?_⟩
    have h3o : (3 : ℤ) = ((orderOf z₀ : ℕ) : ℤ) := by rw [hoz]; rfl
    rw [← hm, ← zpow_natCast, Int.toNat_of_nonneg (by omega), h3o, zpow_mod_orderOf]
  have hpow : ∀ n : ℕ, (Xv s * Xc t) ^ n = Xv (n * s) * Xc (n * t) := by
    intro n
    induction n with
    | zero => simp [Xv_zero, Xc_zero]
    | succ n ih =>
      rw [pow_succ, ih]
      have hvc := (comm_vc s (n * t)).eq
      calc Xv (n * s) * Xc (n * t) * (Xv s * Xc t)
          = Xv (n * s) * (Xc (n * t) * Xv s) * Xc t := by group
        _ = Xv (n * s) * (Xv s * Xc (n * t)) * Xc t := by rw [hvc]
        _ = (Xv (n * s) * Xv s) * (Xc (n * t) * Xc t) := by group
        _ = Xv ((n + 1 : ℕ) * s) * Xc ((n + 1 : ℕ) * t) := by
          rw [← Xv_add, ← Xc_add]
          push_cast
          ring_nf
  have hU : (Xv s * Xc t) ^ n = Xv s * Xc (-t) := by
    have h1 : g * (ι u₀ hu₀) ^ n * g⁻¹ = g * ι (Xv s * Xc (-t)) hu₁ * g⁻¹ := by
      rw [← conj_pow, ← hz₀eq, hzn]
    have h2 : (ι u₀ hu₀) ^ n = ι (Xv s * Xc (-t)) hu₁ := by
      simpa using h1
    have h3' := congrArg Subtype.val h2
    simp only [SubgroupClass.coe_pow] at h3'
    rw [← hst]
    exact h3'
  rw [hpow] at hU
  obtain ⟨e1, e2⟩ := inj_vc hU
  interval_cases n
  · apply hs
    simpa using e1.symm
  · apply ht
    have : (2 : K) * t = 0 := by
      have := e2
      push_cast at this
      linear_combination this
    exact (mul_eq_zero.mp this).resolve_left h2
  · apply hs
    have : s = 0 := by
      push_cast at e1
      linear_combination e1
    exact this

end Three

end Proof17Res10

theorem ks176GTwoChev_holds :
    KS176GTwoChev :=
  ks176GTwoChev_of_three Proof17Res10.ks176GTwoChevThree_holds

theorem ks176GTwo_holds :
    KS176GTwo :=
  ks176GTwo_of_chev ks176GTwoChev_holds

end CFSG.RankThree.PartTwo.Sec17
