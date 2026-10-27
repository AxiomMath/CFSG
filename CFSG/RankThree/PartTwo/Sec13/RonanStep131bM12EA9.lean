module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12EA
import CFSG.RankThree.PartTwo.Sec19.Step198DProof
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bStruct
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19.Step198DProof

theorem cfgEA9_holds : CfgEA9 := by
  intro G _ _ A c L E hCfg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAE : A ≤ Subgroup.normalizer (E : Set G) := (struct_holds G A c L E hCfg).2.2
  obtain ⟨hD, hSL2, -, hEle, hEe, hE27, hEC, hEL, -⟩ := hCfg
  have hA27 : Nat.card A = 27 := hD.card_eq
  have hne : E ≠ A := by
    intro h
    have h9 : 9 ≤ Nat.card (E ⊓ L : Subgroup G) :=
      nine_le_card_of_not_isCyclic (fun x hx => hEe.2 x hx.1) hEL
    have hAL : A ⊓ L ≤ Subgroup.zpowers c := Res2Proof.inf_le_zpowers_of_isSLThreePiTwo hD hSL2
    have h3 := Subgroup.card_le_of_le (h ▸ hAL : E ⊓ L ≤ Subgroup.zpowers c)
    rw [Nat.card_zpowers, hD.orderOf_eq] at h3
    omega
  have hdvd : Nat.card (E ⊓ A : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hk27 : k ≠ 3 := by
    rintro rfl
    have h1 : E ⊓ A = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hE27]; norm_num)
    have h2 : E ⊓ A = A := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hk, hA27]; norm_num)
    exact hne (h1.symm.trans h2)
  suffices h9 : 9 ≤ Nat.card (E ⊓ A : Subgroup G) by
    have : k = 2 := by
      interval_cases k <;> simp_all
    rw [hk, this]
    norm_num
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData hSL2
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  set θH := aschbacherSolvableCore 3 H with hθH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛdef
  have hΛn : Λ.Normal := lBar_normal hD
  have hΛp : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar hD
  have hΛ1 : Λ ≠ ⊥ := subgroupOf_lBar_ne_bot hD
  have hq2 : 2 < p ^ f := by
    by_contra hq2
    have hp := D.piField.prime
    have hf := D.piField.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have := SLTwoData.isSolvable_of_two D h2
    have : Group.IsSolvable Λ := Group.isSolvable_of_isSolvable_injective Λ.subtype_injective
    have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hΛ1
    exact Group.IsPerfect.not_isSolvable Λ inferInstance
  have hL₀ : D.L₀ = Λ := le_antisymm (D.le_of_normal hq2 hΛn hΛp hΛ1) (D.le_of_isPerfect hΛp)
  have hLAH : L ⊔ A ≤ H :=
    sup_le (le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt) hD.A_le_normalizer_zpowers
  let ι : (L ⊔ A : Subgroup G) →* H := Subgroup.inclusion hLAH
  let φ : (L ⊔ A : Subgroup G) →* lBarA c L A :=
    ((QuotientGroup.mk' θH).comp ι).codRestrict (lBarA c L A) fun x =>
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
  have hφv : ∀ x : (L ⊔ A : Subgroup G), ((φ x : lBarA c L A) : H ⧸ θH) =
      QuotientGroup.mk' θH ⟨(x : G), hLAH x.2⟩ := fun x => rfl
  have hker : Nat.Coprime 3 (Nat.card φ.ker) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    apply (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.2.1
    let j : φ.ker →* θH :=
      { toFun := fun x => ⟨ι x, by
          have h1 : ((φ x : lBarA c L A) : H ⧸ θH) = 1 := by rw [MonoidHom.mem_ker.mp x.2]; rfl
          rw [hφv, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
          exact h1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := fun x y hxy => by
      have h1 : ((ι x : H) : G) = ((ι y : H) : G) := by
        have := congrArg (fun z : θH => ((z : H) : G)) hxy
        exact this
      exact Subtype.ext (Subtype.ext h1)
    exact h3.trans (Subgroup.card_dvd_of_injective j hj)
  have hELA : E ≤ L ⊔ A := hEle.trans inf_le_left
  have hEA : E ≤ Subgroup.normalizer (A : Set G) := hEle.trans inf_le_right
  have hP3 : IsPGroup 3 (E ⊔ A : Subgroup G) :=
    (CFSG.Open.IsElemAbelian.isPGroup hEe).to_sup_of_normal_right'
      (CFSG.Open.IsElemAbelian.isPGroup hD.isElemAbelian) hEA
  have hinj := CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_injective_on_pGroup 3
    Nat.prime_three φ hker ((E ⊔ A).subgroupOf (L ⊔ A)) hP3.comap_subtype
  have hinjT : ∀ x y : (L ⊔ A : Subgroup G), (x : G) ∈ E ⊔ A → (y : G) ∈ E ⊔ A →
      φ x = φ y → x = y := fun x y hx hy h =>
    congrArg Subtype.val (hinj (a₁ := ⟨x, Subgroup.mem_subgroupOf.mpr hx⟩)
      (a₂ := ⟨y, Subgroup.mem_subgroupOf.mpr hy⟩) h)
  set AT := A.subgroupOf (L ⊔ A) with hAT
  set ET := E.subgroupOf (L ⊔ A) with hET
  have hinjA : Set.InjOn φ (AT : Set (L ⊔ A : Subgroup G)) := fun x hx y hy h =>
    hinjT x y (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hy)) h
  have hinjE : Set.InjOn φ (ET : Set (L ⊔ A : Subgroup G)) := fun x hx y hy h =>
    hinjT x y (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy)) h
  have hAb27 : Nat.card (AT.map φ) = 27 := by
    rw [card_map_of_injOn φ hinjA, ← hA27]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hEb27 : Nat.card (ET.map φ) = 27 := by
    rw [card_map_of_injOn φ hinjE, ← hE27]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hELA).toEquiv
  have hAbe : CFSG.Assembly.IsElemAbelian 3 (AT.map φ) :=
    isElemAbelian_map (isElemAbelian_subgroupOf hD.isElemAbelian _) φ
  have hEbe : CFSG.Assembly.IsElemAbelian 3 (ET.map φ) :=
    isElemAbelian_map (isElemAbelian_subgroupOf hEe _) φ
  have hAbEb := map_le_normalizer_map φ (subgroupOf_le_normalizer hAE (L ⊔ A))
  have hEbAb := map_le_normalizer_map φ (subgroupOf_le_normalizer hEA (L ⊔ A))
  have hcent : ∀ x : (L ⊔ A : Subgroup G), (x : G) ∈ Sec4.thetaQuotCentralizer L →
      φ x ∈ Subgroup.centralizer (D.L₀ : Set (lBarA c L A)) := by
    intro x hx
    rw [hL₀, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨l, hl, hly⟩ := Subgroup.mem_subgroupOf.mp hy
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    obtain ⟨-, hxl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hx
    have h1 := hxl l hlL
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt,
      inSubgroup_theta_centralizer] at h1
    obtain ⟨t, ht, hte⟩ := h1.2.2
    set x' : H := ⟨(x : G), hLAH x.2⟩ with hx'
    have h2 : l⁻¹ * (x' * l * x'⁻¹) ∈ θH := by
      have e : l⁻¹ * (x' * l * x'⁻¹) = t := Subtype.ext hte.symm
      rw [e]
      exact ht
    have h3 : QuotientGroup.mk' θH (l⁻¹ * (x' * l * x'⁻¹)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    apply Subtype.ext
    change (y : H ⧸ θH) * QuotientGroup.mk' θH x' = QuotientGroup.mk' θH x' * (y : H ⧸ θH)
    rw [← hly]
    calc QuotientGroup.mk' θH l * QuotientGroup.mk' θH x' =
        QuotientGroup.mk' θH l * ((QuotientGroup.mk' θH l)⁻¹ * (QuotientGroup.mk' θH x' *
          QuotientGroup.mk' θH l * (QuotientGroup.mk' θH x')⁻¹)) * QuotientGroup.mk' θH x' := by
          rw [h3, mul_one]
      _ = QuotientGroup.mk' θH x' * QuotientGroup.mk' θH l := by group
  have hCE9 : 9 ≤ Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) :=
    nine_le_card_of_not_isCyclic (fun x hx => hEe.2 x hx.1) hEC
  have hEC : 9 ≤ Nat.card (ET.map φ ⊓ Subgroup.centralizer (D.L₀ : Set (lBarA c L A)) :
      Subgroup (lBarA c L A)) := by
    refine hCE9.trans (Nat.card_le_card_of_injective
      (fun x : (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) =>
        (⟨φ ⟨(x : G), hELA x.2.1⟩, ⟨⟨(x : G), hELA x.2.1⟩, Subgroup.mem_subgroupOf.mpr x.2.1,
          rfl⟩, hcent _ x.2.2⟩ : (ET.map φ ⊓ Subgroup.centralizer (D.L₀ : Set (lBarA c L A)) :
            Subgroup (lBarA c L A)))) ?_)
    intro x y hxy
    have h1 := hinjT ⟨(x : G), hELA x.2.1⟩ ⟨(y : G), hELA y.2.1⟩ (Subgroup.mem_sup_left x.2.1)
      (Subgroup.mem_sup_left y.2.1) (congrArg Subtype.val hxy)
    exact Subtype.ext (congrArg (fun z : (L ⊔ A : Subgroup G) => (z : G)) h1)
  have hcA : φ ⟨c, Subgroup.mem_sup_right hD.mem_A⟩ ∈ AT.map φ :=
    ⟨⟨c, Subgroup.mem_sup_right hD.mem_A⟩, Subgroup.mem_subgroupOf.mpr hD.mem_A, rfl⟩
  have hcZ : φ ⟨c, Subgroup.mem_sup_right hD.mem_A⟩ ∈ Subgroup.center (lBarA c L A) :=
    mkC_mem_center hD
  have hc1 : φ ⟨c, Subgroup.mem_sup_right hD.mem_A⟩ ≠ 1 := mkC_ne_one hD
  have h9 := nine_le_card_inf D hAbe hAb27 hEbe hEb27 hAbEb hEbAb hEC hcA
    (Subgroup.center_le_centralizer _ hcZ) hc1
  refine h9.trans (Nat.card_le_card_of_surjective
    (fun x : (E ⊓ A : Subgroup G) => (⟨φ ⟨(x : G), Subgroup.mem_sup_right x.2.2⟩,
      ⟨⟨(x : G), Subgroup.mem_sup_right x.2.2⟩, Subgroup.mem_subgroupOf.mpr x.2.2, rfl⟩,
      ⟨⟨(x : G), Subgroup.mem_sup_right x.2.2⟩, Subgroup.mem_subgroupOf.mpr x.2.1, rfl⟩⟩ :
        (AT.map φ ⊓ ET.map φ : Subgroup (lBarA c L A)))) ?_)
  rintro ⟨z, ⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩⟩
  have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
  have hyE : (y : G) ∈ E := Subgroup.mem_subgroupOf.mp hy
  have hxy : y = x := hinjT y x (Subgroup.mem_sup_left hyE) (Subgroup.mem_sup_right hxA) hyx
  refine ⟨⟨(x : G), hxy ▸ hyE, hxA⟩, Subtype.ext ?_⟩
  rfl


end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
