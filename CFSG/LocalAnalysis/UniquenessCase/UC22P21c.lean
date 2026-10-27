module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.GroupTheory.LocalCores.FittingNormal
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

section Abstract

theorem uc22p21c_commutator_le_centralizer_of_cyclic {Q : Type*} [Group Q] (A : Subgroup Q)
    [A.Normal] [IsCyclic A] : commutator Q ≤ Subgroup.centralizer (A : Set Q) := by
  let φ : Q →* MulAut A := MulAut.conjNormal (H := A)
  let ψ : Q →* (ZMod (Nat.card A))ˣ := (IsCyclic.mulAutMulEquiv A).toMonoidHom.comp φ
  intro g hg
  have h1 : ψ g = 1 := Abelianization.commutator_subset_ker ψ hg
  have h2 : φ g = 1 := (IsCyclic.mulAutMulEquiv A).injective (by simpa [ψ] using h1)
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have h3 := congrArg (fun a : MulAut A => ((a ⟨n, hn⟩ : A) : Q)) h2
  simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h3
  calc n * g = (g * n * g⁻¹) * g := by rw [h3]
    _ = g * n := by group

theorem uc22p21c_mem_commutator_of_oResidual_eq_top {H : Type*} [Group H] {p : ℕ}
    (hgen : CFSG.GH74.GLS.oResidual p H = ⊤) {x : H} {k : ℕ} (hx : orderOf x ∣ p ^ k) :
    x ∈ commutator H := by
  have key : ∀ y ∈ CFSG.GH74.GLS.oResidual p H,
      Nat.Coprime (orderOf (Abelianization.of y)) p := by
    intro y hy
    unfold CFSG.GH74.GLS.oResidual at hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact Nat.Coprime.coprime_dvd_left (orderOf_map_dvd Abelianization.of y) hy
    | one => simp
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact Nat.Coprime.coprime_dvd_left (Commute.orderOf_mul_dvd_mul_orderOf (Commute.all _ _))
        (Nat.Coprime.mul_left ha hb)
    | inv a _ ha => simpa using ha
  have h1 := key x (hgen ▸ Subgroup.mem_top x)
  have h2 : orderOf (Abelianization.of x) ∣ p ^ k := (orderOf_map_dvd _ x).trans hx
  have h3 : orderOf (Abelianization.of x) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k h1) h2
  rw [orderOf_eq_one_iff] at h3
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  exact h3

theorem uc22p21c_perfectResidual_le_commutator (Q : Type*) [Group Q] :
    CFSG.perfectResidual Q ≤ commutator Q := by
  calc CFSG.perfectResidual Q ≤ derivedSeries Q 1 := iInf_le (fun n : ℕ => derivedSeries Q n) 1
    _ = commutator Q := derivedSeries_one Q

theorem uc22p21c_normal_centralizer {Q : Type*} [Group Q] (S : Subgroup Q) [hS : S.Normal] :
    (Subgroup.centralizer (S : Set Q)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro h hh
  have h1 : g⁻¹ * h * g ∈ S := by simpa using hS.conj_mem h hh g⁻¹
  have h2 := hn _ h1
  calc h * (g * n * g⁻¹) = g * ((g⁻¹ * h * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * h * g)) * g⁻¹ := by rw [h2]
    _ = g * n * g⁻¹ * h := by group

theorem uc22p21c_commutator_perfectResidual_fitting_eq_bot {Q : Type*} [Group Q] [Finite Q]
    (hcyc : IsCyclic ↥(CFSG.fittingSubgroup ↥(commutator Q))) :
    ⁅CFSG.perfectResidual Q, CFSG.fittingSubgroup Q⁆ = ⊥ := by
  set R := CFSG.perfectResidual Q with hR
  set F := CFSG.fittingSubgroup Q with hF
  set N := commutator Q with hN
  haveI hRperf : Group.IsPerfect R :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
  haveI hRc : R.Characteristic :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic (G := Q)
  haveI hRn : R.Normal := inferInstance
  haveI hFn : F.Normal := (CFSG.LocalCores.fitting_nilpotent (G := Q)).2.1
  have hC₁ : (CFSG.fittingSubgroup ↥N).map N.subtype = N ⊓ F :=
    CFSG.LocalCores.fitting_normal_intersection N
  haveI hcycC : IsCyclic ↥(N ⊓ F) := by
    rw [← hC₁]
    exact isCyclic_of_surjective
      ((CFSG.fittingSubgroup ↥N).equivMapOfInjective N.subtype N.subtype_injective).toMonoidHom
      ((CFSG.fittingSubgroup ↥N).equivMapOfInjective N.subtype N.subtype_injective).surjective
  have hNC : N ≤ Subgroup.centralizer ((N ⊓ F : Subgroup Q) : Set Q) :=
    uc22p21c_commutator_le_centralizer_of_cyclic (N ⊓ F)
  have hRN : R ≤ N := uc22p21c_perfectResidual_le_commutator Q
  have h1 : ⁅R, F⁆ ≤ N ⊓ F :=
    le_inf ((commutator_le_left R F).trans hRN) (commutator_le_right R F)
  have hRC : ⁅R, N ⊓ F⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hRN.trans hNC)
  have hCR : ⁅N ⊓ F, R⁆ = ⊥ := by rw [commutator_comm]; exact hRC
  have h2 : ⁅⁅R, F⁆, R⁆ = ⊥ := eq_bot_iff.mpr ((commutator_mono h1 le_rfl).trans hCR.le)
  have h3 : ⁅⁅F, R⁆, R⁆ = ⊥ := by rw [commutator_comm F R]; exact h2
  have h4 : ⁅⁅R, R⁆, F⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h2 h3
  rwa [Subgroup.isPerfect_iff.mp hRperf] at h4

theorem uc22p21c_isCyclic_centralizer_layer_inf_commutator {Q : Type*} [Group Q] [Finite Q]
    (hcyc : IsCyclic ↥(CFSG.fittingSubgroup ↥(commutator Q))) :
    IsCyclic ↥(Subgroup.centralizer (CFSG.layer Q : Set Q) ⊓ commutator Q) := by
  set N := commutator Q with hN
  set F := CFSG.fittingSubgroup Q with hF
  haveI hFn : F.Normal := (CFSG.LocalCores.fitting_nilpotent (G := Q)).2.1
  haveI hLn : (CFSG.layer Q).Normal := by
    rw [CFSG.layer_eq_componentClassification]
    exact CFSG.ComponentClassification.Layer.normal Q
  haveI hXn : (Subgroup.centralizer (CFSG.layer Q : Set Q)).Normal :=
    uc22p21c_normal_centralizer (CFSG.layer Q)
  set K := Subgroup.centralizer (CFSG.layer Q : Set Q) ⊓ N with hK
  haveI hKn : K.Normal := inferInstance
  have hKN : K ≤ N := inf_le_right
  have hC₁ : (CFSG.fittingSubgroup ↥N).map N.subtype = N ⊓ F :=
    CFSG.LocalCores.fitting_normal_intersection N
  haveI hcycC : IsCyclic ↥(N ⊓ F) := by
    rw [← hC₁]
    exact isCyclic_of_surjective
      ((CFSG.fittingSubgroup ↥N).equivMapOfInjective N.subtype N.subtype_injective).toMonoidHom
      ((CFSG.fittingSubgroup ↥N).equivMapOfInjective N.subtype N.subtype_injective).surjective
  have hNC : N ≤ Subgroup.centralizer ((N ⊓ F : Subgroup Q) : Set Q) :=
    uc22p21c_commutator_le_centralizer_of_cyclic (N ⊓ F)
  have hlayer : CFSG.layer ↥K = ⊥ := by
    apply CFSG.LocalCores.layer_eq_bot_of_forall
    intro B hB
    have hBo : CFSG.Open.IsComponentOf B ⊤ := (CFSG.isComponent_iff_open B).mp hB
    have hsub : CFSG.Open.IsSubnormal K ⊤ :=
      CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
        (inferInstance : K.Normal).isSubnormal
    have hB' := CFSG.ComponentClassification.LocalComponents.of_subnormal_subgroup K hsub B hBo
    have hle : B.map K.subtype ≤ CFSG.layer Q := by
      rw [CFSG.layer_eq_componentClassification]
      exact CFSG.ComponentClassification.Layer.component_le hB'
    have hKX : K ≤ Subgroup.centralizer (CFSG.layer Q : Set Q) := inf_le_left
    haveI hcomm : IsMulCommutative ↥B := by
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : ((a : ↥K) : Q) ∈ B.map K.subtype := ⟨a, a.2, rfl⟩
      have hb : ((b : ↥K) : Q) ∈ B.map K.subtype := ⟨b, b.2, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp (hKX (b : ↥K).2) _ (hle ha)
      exact Subtype.ext (Subtype.ext h1)
    haveI : Group.IsPerfect ↥B := hB.1.1
    have hsubs : Subsingleton ↥B := Group.IsPerfect.subsingleton_of_isMulCommutative
    haveI : Nontrivial ↥B := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
    exact not_subsingleton _ hsubs
  have hFstar : CFSG.generalizedFitting ↥K = CFSG.fittingSubgroup ↥K := by
    rw [CFSG.generalizedFitting.eq_sup, hlayer, sup_bot_eq]
  have hcent : Subgroup.centralizer (CFSG.fittingSubgroup ↥K : Set ↥K) ≤ CFSG.fittingSubgroup ↥K := by
    have := CFSG.centralizer_generalizedFitting_le ↥K
    rwa [hFstar] at this
  have hFK : (CFSG.fittingSubgroup ↥K).map K.subtype ≤ N ⊓ F := by
    rw [CFSG.LocalCores.fitting_normal_intersection K]
    exact inf_le_inf_right _ hKN
  have hall : (⊤ : Subgroup ↥K) ≤ Subgroup.centralizer (CFSG.fittingSubgroup ↥K : Set ↥K) := by
    intro k _
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfC : ((f : ↥K) : Q) ∈ N ⊓ F := hFK ⟨f, hf, rfl⟩
    have hkN : ((k : ↥K) : Q) ∈ Subgroup.centralizer ((N ⊓ F : Subgroup Q) : Set Q) := hNC (hKN k.2)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hkN _ hfC)
  have htop : CFSG.fittingSubgroup ↥K = ⊤ := top_unique (hall.trans hcent)
  have hKle : K ≤ N ⊓ F := by
    intro x hx
    apply hFK
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [htop]
    exact Subgroup.mem_top _
  exact isCyclic_of_injective (Subgroup.inclusion hKle) (Subgroup.inclusion_injective hKle)


theorem uc22p21c_normal_centralizer_layer_inf_commutator (Q : Type*) [Group Q] [Finite Q] :
    (Subgroup.centralizer (CFSG.layer Q : Set Q) ⊓ commutator Q).Normal := by
  haveI hLn : (CFSG.layer Q).Normal := by
    rw [CFSG.layer_eq_componentClassification]
    exact CFSG.ComponentClassification.Layer.normal Q
  haveI hXn : (Subgroup.centralizer (CFSG.layer Q : Set Q)).Normal :=
    uc22p21c_normal_centralizer (CFSG.layer Q)
  infer_instance

theorem uc22p21c_normal_of_le_cyclic_normal {Q : Type*} [Group Q] {K P : Subgroup Q} [hK : K.Normal]
    [hc : IsCyclic ↥K] (hPK : P ≤ K) : P.Normal := by
  obtain ⟨k, hk⟩ := hc.exists_generator
  refine ⟨fun x hx q => ?_⟩
  have hxK : x ∈ K := hPK hx
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hk ⟨x, hxK⟩)
  have hqk : q * (k : Q) * q⁻¹ ∈ K := hK.conj_mem _ k.2 q
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hk ⟨q * (k : Q) * q⁻¹, hqk⟩)
  have hx' : x = (k : Q) ^ b := by
    have := congrArg Subtype.val hb
    simpa using this.symm
  have hq' : q * (k : Q) * q⁻¹ = (k : Q) ^ a := by
    have := congrArg Subtype.val ha
    simpa using this.symm
  have h1 : q * x * q⁻¹ = x ^ a := by
    rw [hx', ← conj_zpow, hq', ← zpow_mul, ← zpow_mul, mul_comm]
  rw [h1]
  exact P.zpow_mem hx a

theorem uc22p21c_le_perfectResidual {H : Type*} [Group H] (P : Subgroup H) (hP : ⁅P, P⁆ = P) :
    P ≤ CFSG.perfectResidual H := by
  refine le_iInf fun n => ?_
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [derivedSeries_succ]
    calc P = ⁅P, P⁆ := hP.symm
      _ ≤ ⁅derivedSeries H n, derivedSeries H n⁆ := Subgroup.commutator_mono ih ih

theorem uc22p21c_map_perfectResidual {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) :
    (CFSG.perfectResidual A).map f = CFSG.perfectResidual B := by
  apply le_antisymm
  · apply le_iInf
    intro n
    exact (Subgroup.map_mono (iInf_le _ n)).trans (map_derivedSeries_le_derivedSeries f n)
  · obtain ⟨n, hn⟩ := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_derivedSeries
      (G := A)
    have hbound := derivedSeries_le_map_derivedSeries hf n
    have hn' : CFSG.perfectResidual A = derivedSeries A n := hn
    rw [← hn'] at hbound
    exact (iInf_le (fun k : ℕ => derivedSeries B k) n).trans hbound

end Abstract

section Bridge

variable {G : Type} [Group G] [Finite G]

abbrev uc22p21cPi (M : Subgroup G) : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)

theorem uc22p21c_pi_surjective (M : Subgroup G) : Function.Surjective (uc22p21cPi M) :=
  QuotientGroup.mk'_surjective _

theorem uc22p21c_mem_barPreimage {M : Subgroup G} {Y : Subgroup (Bar2 M)} {x : G} :
    x ∈ barPreimage M Y ↔ ∃ h : x ∈ M, uc22p21cPi M ⟨x, h⟩ ∈ Y := by
  unfold barPreimage
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem uc22p21c_barPreimage_le (M : Subgroup G) (Y : Subgroup (Bar2 M)) : barPreimage M Y ≤ M := by
  intro x hx
  exact ((uc22p21c_mem_barPreimage).1 hx).1

theorem uc22p21c_mem_barImage {M P : Subgroup G} {q : Bar2 M} :
    q ∈ barImage M P ↔ ∃ m : ↥M, (m : G) ∈ P ∧ uc22p21cPi M m = q := by
  unfold barImage
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩

theorem uc22p21c_mem_Hinf {K : Subgroup G} {x : G} :
    x ∈ Hinf K ↔ ∃ m ∈ CFSG.perfectResidual ↥K, (m : G) = x := by
  unfold Hinf CFSG.inSubgroup
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩

theorem uc22p21c_Hinf_le (K : Subgroup G) : Hinf K ≤ K := by
  intro x hx
  obtain ⟨m, _, rfl⟩ := uc22p21c_mem_Hinf.1 hx
  exact m.2

theorem uc22p21c_Hinf_perfect (K : Subgroup G) : ⁅Hinf K, Hinf K⁆ = Hinf K := by
  have h : ⁅CFSG.perfectResidual ↥K, CFSG.perfectResidual ↥K⁆ = CFSG.perfectResidual ↥K :=
    Subgroup.isPerfect_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect (G := ↥K))
  unfold Hinf CFSG.inSubgroup
  rw [← Subgroup.map_commutator, h]

theorem uc22p21c_le_Hinf {P K : Subgroup G} (hPK : P ≤ K) (hP : ⁅P, P⁆ = P) : P ≤ Hinf K := by
  have hP' : (P.subgroupOf K).map K.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPK]
  have hperf : ⁅P.subgroupOf K, P.subgroupOf K⁆ = P.subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, hP', hP]
  have h1 := uc22p21c_le_perfectResidual _ hperf
  calc P = (P.subgroupOf K).map K.subtype := hP'.symm
    _ ≤ Hinf K := Subgroup.map_mono h1

theorem uc22p21c_commutator_bar_eq_bot_iff (M : Subgroup G) :
    ⁅Hinf M, oTwoFOf M⁆ ≤ CFSG.Open.pCoreOf 2 M ↔
      ⁅CFSG.perfectResidual (Bar2 M), CFSG.fittingSubgroup (Bar2 M)⁆ = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro q₁ hq₁ q₂ hq₂
    have hq₁' : q₁ ∈ (CFSG.perfectResidual ↥M).map (uc22p21cPi M) := by
      rw [uc22p21c_map_perfectResidual _ (uc22p21c_pi_surjective M)]
      exact hq₁
    obtain ⟨m₁, hm₁, rfl⟩ := hq₁'
    obtain ⟨m₂, rfl⟩ := uc22p21c_pi_surjective M q₂
    have hx : (m₁ : G) ∈ Hinf M := uc22p21c_mem_Hinf.2 ⟨m₁, hm₁, rfl⟩
    have hy : (m₂ : G) ∈ oTwoFOf M := uc22p21c_mem_barPreimage.2 ⟨m₂.2, hq₂⟩
    have hc := h (Subgroup.commutator_mem_commutator hx hy)
    have hc' : ⁅m₁, m₂⁆ ∈ CFSG.pCore 2 ↥M := (CFSG.mem_openPCoreOf_iff ⁅m₁, m₂⁆).1 hc
    have h1 : uc22p21cPi M ⁅m₁, m₂⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hc'
    simpa [map_commutatorElement] using h1
  · intro h
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    obtain ⟨m₁, hm₁, rfl⟩ := uc22p21c_mem_Hinf.1 hx
    have hy' := (uc22p21c_mem_barPreimage.1 hy)
    obtain ⟨hyM, hyF⟩ := hy'
    have h1 : uc22p21cPi M m₁ ∈ CFSG.perfectResidual (Bar2 M) := by
      rw [← uc22p21c_map_perfectResidual _ (uc22p21c_pi_surjective M)]
      exact ⟨m₁, hm₁, rfl⟩
    have h2 : ⁅uc22p21cPi M m₁, uc22p21cPi M ⟨y, hyM⟩⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator h1 hyF
      rw [h] at this
      simpa using this
    have h3 : uc22p21cPi M ⁅m₁, ⟨y, hyM⟩⁆ = 1 := by simpa [map_commutatorElement] using h2
    have h4 : ⁅m₁, (⟨y, hyM⟩ : ↥M)⁆ ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 h3
    exact (CFSG.mem_openPCoreOf_iff ⁅m₁, (⟨y, hyM⟩ : ↥M)⁆).2 h4

theorem uc22p21c_Hinf_le_oTwoE_iff (M : Subgroup G) :
    Hinf M ≤ oTwoEOf M ↔ CFSG.perfectResidual (Bar2 M) ≤ CFSG.layer (Bar2 M) := by
  constructor
  · intro h q hq
    have hq' : q ∈ (CFSG.perfectResidual ↥M).map (uc22p21cPi M) := by
      rw [uc22p21c_map_perfectResidual _ (uc22p21c_pi_surjective M)]
      exact hq
    obtain ⟨m, hm, rfl⟩ := hq'
    obtain ⟨_, h2⟩ := uc22p21c_mem_barPreimage.1 (h (uc22p21c_mem_Hinf.2 ⟨m, hm, rfl⟩))
    exact h2
  · intro h x hx
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_Hinf.1 hx
    refine uc22p21c_mem_barPreimage.2 ⟨m.2, ?_⟩
    apply h
    rw [← uc22p21c_map_perfectResidual _ (uc22p21c_pi_surjective M)]
    exact ⟨m, hm, rfl⟩

theorem uc22p21c_Hinf_eq_iff (M : Subgroup G) :
    Hinf M = Hinf (oTwoEOf M) ↔ CFSG.perfectResidual (Bar2 M) = CFSG.layer (Bar2 M) := by
  have hlayer : CFSG.layer (Bar2 M) ≤ CFSG.perfectResidual (Bar2 M) :=
    uc22p21c_le_perfectResidual _ (CFSG.LocalCores.layer_perfect)
  constructor
  · intro h
    refine le_antisymm ?_ hlayer
    rw [← uc22p21c_Hinf_le_oTwoE_iff]
    exact h.le.trans ((uc22p21c_Hinf_le _).trans le_rfl)
  · intro h
    have h1 : Hinf M ≤ oTwoEOf M := (uc22p21c_Hinf_le_oTwoE_iff M).2 h.le
    apply le_antisymm
    · exact uc22p21c_le_Hinf h1 (uc22p21c_Hinf_perfect M)
    · exact uc22p21c_le_Hinf ((uc22p21c_Hinf_le _).trans (uc22p21c_barPreimage_le M _))
        (uc22p21c_Hinf_perfect _)

theorem uc22p21c_isPGroup_pCoreOf (K : Subgroup G) : IsPGroup 2 (pCoreOf 2 K) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype

theorem uc22p21c_pCoreOf_le (K : Subgroup G) : pCoreOf 2 K ≤ K :=
  Subgroup.map_subtype_le _

theorem uc22p21c_le_pCoreOf {K P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 2 P)
    (hn : ∀ k ∈ K, ∀ x ∈ P, k * x * k⁻¹ ∈ P) : P ≤ pCoreOf 2 K := by
  have hN : (P.subgroupOf K).Normal := ⟨fun x hx k => hn (k : G) k.2 x hx⟩
  have hQ : IsPGroup 2 (P.subgroupOf K) := hP.comap_subtype
  have hle : P.subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hN, hQ⟩
  intro x hx
  exact ⟨⟨x, hPK hx⟩, hle hx, rfl⟩

theorem uc22p21c_conj_mem_pCoreOf_self {K : Subgroup G} {k x : G} (hk : k ∈ K)
    (hx : x ∈ pCoreOf 2 K) : k * x * k⁻¹ ∈ pCoreOf 2 K := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥K)).conj_mem y hy ⟨k, hk⟩, rfl⟩

theorem uc22p21c_pCoreOf_le_of_subnormal {K L : Subgroup G} (h : CFSG.Open.IsSubnormal K L) :
    pCoreOf 2 K ≤ pCoreOf 2 L := by
  induction h with
  | refl => exact le_rfl
  | @step K M L hKM hN _ ih =>
    refine le_trans ?_ ih
    have hnorm : ∀ n ∈ M, ∀ k ∈ K, n * k * n⁻¹ ∈ K := fun n hn k hk =>
      (Subgroup.normal_subgroupOf_iff hKM).1 hN k n hk hn
    refine uc22p21c_le_pCoreOf ((uc22p21c_pCoreOf_le K).trans hKM) (uc22p21c_isPGroup_pCoreOf K) ?_
    intro m hm x hx
    have hPK : (pCoreOf 2 K).map (MulAut.conj m).toMonoidHom ≤ K := by
      rintro _ ⟨y, hy, rfl⟩
      exact hnorm m hm y (uc22p21c_pCoreOf_le K hy)
    have hP2 : IsPGroup 2 ((pCoreOf 2 K).map (MulAut.conj m).toMonoidHom) :=
      (uc22p21c_isPGroup_pCoreOf K).map _
    have hPn : ∀ k ∈ K, ∀ y ∈ (pCoreOf 2 K).map (MulAut.conj m).toMonoidHom,
        k * y * k⁻¹ ∈ (pCoreOf 2 K).map (MulAut.conj m).toMonoidHom := by
      rintro k hk _ ⟨y, hy, rfl⟩
      have hk' : m⁻¹ * k * m ∈ K := by simpa using hnorm m⁻¹ (M.inv_mem hm) k hk
      refine ⟨(m⁻¹ * k * m) * y * (m⁻¹ * k * m)⁻¹,
        uc22p21c_conj_mem_pCoreOf_self hk' hy, ?_⟩
      simp only [MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      group
    exact uc22p21c_le_pCoreOf hPK hP2 hPn ⟨x, hx, rfl⟩

theorem uc22p21c_mem_map_conj {K : Subgroup G} {g x : G} :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp

@[instance_reducible] noncomputable def uc22p21cAct (M : Subgroup G) : MulAction ↥M (Subgroup G) where
  smul m K := K.map (MulAut.conj (m : G)).toMonoidHom
  one_smul K := by
    show K.map (MulAut.conj (((1 : ↥M) : G))).toMonoidHom = K
    ext x
    rw [uc22p21c_mem_map_conj]
    simp
  mul_smul a b K := by
    show K.map (MulAut.conj (((a * b : ↥M) : G))).toMonoidHom =
      (K.map (MulAut.conj (b : G)).toMonoidHom).map (MulAut.conj (a : G)).toMonoidHom
    ext x
    rw [uc22p21c_mem_map_conj, uc22p21c_mem_map_conj, uc22p21c_mem_map_conj]
    simp [mul_assoc]

theorem uc22p21c_perfectResidual_normalizes {M L : Subgroup G}
    (h : (conjSetOf M L).ncard ≤ 2) :
    ∀ m ∈ CFSG.perfectResidual ↥M, ∀ x ∈ L, (m : G) * x * (m : G)⁻¹ ∈ L := by
  letI : MulAction ↥M (Subgroup G) := uc22p21cAct M
  have horb : MulAction.orbit ↥M L = conjSetOf M L := by
    ext K
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨(m : G), m.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hcard : Nat.card ↥(MulAction.orbit ↥M L) ≤ 2 := by
    rw [horb, Nat.card_coe_set_eq]
    exact h
  haveI : IsMulCommutative (Equiv.Perm ↥(MulAction.orbit ↥M L)) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr hcard
  let φ : ↥M →* Equiv.Perm ↥(MulAction.orbit ↥M L) :=
    MulAction.toPermHom ↥M ↥(MulAction.orbit ↥M L)
  intro m hm x hx
  have hker : m ∈ φ.ker :=
    Abelianization.commutator_subset_ker φ (uc22p21c_perfectResidual_le_commutator _ hm)
  have hfix : m • L = L := by
    have := congrArg (fun σ : Equiv.Perm ↥(MulAction.orbit ↥M L) =>
      (σ ⟨L, MulAction.mem_orbit_self L⟩ : Subgroup G)) (MonoidHom.mem_ker.mp hker)
    simpa [φ] using this
  have hx' : (m : G) * x * (m : G)⁻¹ ∈ m • L := ⟨x, hx, by simp⟩
  rwa [hfix] at hx'

theorem uc22p21c_exists_calC_of_component (M : Subgroup G) {C : Subgroup (Bar2 M)}
    (hC : CFSG.IsComponent C) : ∃ L ∈ calC M, barImage M L = C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCc : C ∈ CFSG.Quasithin.cComp (⊤ : Subgroup (Bar2 M)) :=
    CFSG.Quasithin.mem_cComp_top_of_isComponent hC
  haveI hPs : Group.IsSolvable ↥(CFSG.pCore 2 ↥M) := by
    haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥M) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
    infer_instance
  have hsolv : Group.IsSolvable (uc22p21cPi M).ker := by
    rw [QuotientGroup.ker_mk']
    exact hPs
  obtain ⟨L', hL', hmap⟩ := CFSG.Quasithin.map_surjOn_cComp_top (uc22p21cPi M)
    (uc22p21c_pi_surjective M) hsolv hCc
  have hLc : L'.map M.subtype ∈ CFSG.Quasithin.cComp M := CFSG.Quasithin.map_subtype_mem_cComp hL'
  set L := L'.map M.subtype with hL
  have hLM : L ≤ M := Subgroup.map_subtype_le _
  have hLsub : L.subgroupOf M = L' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective L'
  have hbar : barImage M L = C := by
    unfold barImage
    rw [hLsub]
    exact hmap
  have hsub : CFSG.Open.IsSubnormal L M := CFSG.Quasithin.subnormal_of_mem_cComp hLc
  refine ⟨L, ⟨hsub, CFSG.Quasithin.perfect_of_mem_cComp hLc, ?_⟩, hbar⟩
  let φ : ↥L →* Bar2 M := (uc22p21cPi M).comp (Subgroup.inclusion hLM)
  have hrange : φ.range = C := by
    rw [← hbar]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hLM x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : φ.ker = CFSG.pCore 2 ↥L := by
    have key : ∀ x : ↥L, x ∈ φ.ker ↔ ((x : ↥L) : G) ∈ pCoreOf 2 M := by
      intro x
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) (Subgroup.inclusion hLM x) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      constructor
      · intro h
        exact ⟨Subgroup.inclusion hLM x, h, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = Subgroup.inclusion hLM x := Subtype.ext hyx
        exact this ▸ hy
    ext x
    rw [key]
    have key2 : x ∈ CFSG.pCore 2 ↥L ↔ ((x : ↥L) : G) ∈ pCoreOf 2 L := by
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        exact this ▸ hy
    rw [key2]
    constructor
    · intro h
      refine uc22p21c_le_pCoreOf (K := L) (P := L ⊓ pCoreOf 2 M) inf_le_left
        ((uc22p21c_isPGroup_pCoreOf M).to_inf_right) ?_ ⟨x.2, h⟩
      intro k hk y hy
      exact ⟨L.mul_mem (L.mul_mem hk hy.1) (L.inv_mem hk),
        uc22p21c_conj_mem_pCoreOf_self (hLM hk) hy.2⟩
    · intro h
      exact uc22p21c_pCoreOf_le_of_subnormal hsub h
  let e : Bar2 L ≃* ↥C :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)
  exact CFSG.Open.IsQuasisimple.of_mulEquiv e (CFSG.Quasithin.A3.isQuasisimple_iff_open.1 hC.1)

theorem uc22p21c_inCatalog_component (D : Data G) {C : Subgroup (Bar2 D.M)}
    (hC : CFSG.IsComponent C) : CFSG.Assembly.InCatalog (↥C ⧸ Subgroup.center ↥C) := by
  haveI : (CFSG.pCore 2 ↥D.M).Normal := CFSG.pCore_normal
  haveI := D.standing.simple
  have hMtop : D.M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1
  have hKK : CFSG.Open.IsKGroup ↥D.M := D.standing.kProper.isKGroup D.M hMtop
  have hB : CFSG.Open.IsKGroup (Bar2 D.M) := hKK.quotient _
  haveI : IsSimpleGroup (↥C ⧸ Subgroup.center ↥C) := hC.1.2.1
  exact hB.isCatalogGroup_of_surjective C hC.1.2.2 (QuotientGroup.mk' (Subgroup.center ↥C))
    (QuotientGroup.mk'_surjective _)

theorem uc22p21c_perfectResidual_le_normalizer_component (D : Data G) (Ch : Choice2011 G)
    (h21_17 : S21_17 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {C : Subgroup (Bar2 D.M)}
    (hC : CFSG.IsComponent C) :
    CFSG.perfectResidual (Bar2 D.M) ≤ Subgroup.normalizer (C : Set (Bar2 D.M)) := by
  obtain ⟨L, hL, hbar⟩ := uc22p21c_exists_calC_of_component D.M hC
  have hS : (conjSetOf D.M L).ncard ≤ 2 := by
    rcases h21_17 h1930 c L hL with h | ⟨h, _⟩ | ⟨h, _⟩
    · have hK : ∀ K ∈ conjSetOf D.M L, K = L := by
        rintro K ⟨g, hg, rfl⟩
        have hle : L.map (MulAut.conj g).toMonoidHom ≤ L := by
          calc L.map (MulAut.conj g).toMonoidHom ≤ conjClosure D.M L :=
                le_iSup₂_of_le (L.map (MulAut.conj g).toMonoidHom) ⟨g, hg, rfl⟩ le_rfl
            _ = L := h.symm
        exact Subgroup.eq_of_le_of_card_ge hle
          (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
      have hsub : conjSetOf D.M L ⊆ {L} := fun K hK' => hK K hK'
      exact (Set.ncard_le_ncard hsub (Set.finite_singleton L)).trans (by simp)
    · exact h.le
    · exact h.le
  intro q hq
  have hq' : q ∈ (CFSG.perfectResidual ↥D.M).map (uc22p21cPi D.M) := by
    rw [uc22p21c_map_perfectResidual _ (uc22p21c_pi_surjective D.M)]
    exact hq
  obtain ⟨m, hm, rfl⟩ := hq'
  have hnorm := uc22p21c_perfectResidual_normalizes hS
  rw [← hbar, Subgroup.mem_normalizer_iff]
  intro y
  rw [uc22p21c_mem_barImage, uc22p21c_mem_barImage]
  constructor
  · rintro ⟨m', hm', rfl⟩
    exact ⟨m * m' * m⁻¹, by simpa using hnorm m hm _ hm', by simp⟩
  · rintro ⟨m', hm', hy⟩
    refine ⟨m⁻¹ * m' * m, ?_, ?_⟩
    · simpa using hnorm m⁻¹ (Subgroup.inv_mem _ hm) _ hm'
    · have : (uc22p21cPi D.M) m * y * ((uc22p21cPi D.M) m)⁻¹ = (uc22p21cPi D.M) m' := hy.symm
      simp only [map_mul, map_inv]
      calc (uc22p21cPi D.M) m⁻¹ * (uc22p21cPi D.M) m' * (uc22p21cPi D.M) m
          = (uc22p21cPi D.M) m⁻¹ * ((uc22p21cPi D.M) m * y * ((uc22p21cPi D.M) m)⁻¹) *
              (uc22p21cPi D.M) m := by rw [this]
        _ = y := by simp [mul_assoc]

theorem uc22p21c_perfectResidual_le_layer (D : Data G) (Ch : Choice2011 G) (h21_17 : S21_17 D Ch)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h1930 : H1930 D) (c : Ctx21 D Ch)
    (hF : ⁅CFSG.perfectResidual (Bar2 D.M), CFSG.fittingSubgroup (Bar2 D.M)⁆ = ⊥) :
    CFSG.perfectResidual (Bar2 D.M) ≤ CFSG.layer (Bar2 D.M) := by
  haveI hperf : Group.IsPerfect (CFSG.perfectResidual (Bar2 D.M)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
  rw [CFSG.layer_eq_componentClassification]
  refine CFSG.ComponentClassification.GeneralizedFitting.perfect_normalizer_enters_layer _ hF ?_ ?_
  · intro C hC
    exact uc22p21c_perfectResidual_le_normalizer_component D Ch h21_17 h1930 c
      ((CFSG.isComponent_iff_open C).2 hC)
  · intro C hC
    have hC' := (CFSG.isComponent_iff_open C).2 hC
    haveI : IsSimpleGroup (↥C ⧸ Subgroup.center ↥C) := hC'.1.2.1
    exact hSch _ hC'.1.2.2 (uc22p21c_inCatalog_component D hC')

theorem s21_18_of (D : Data G) (Ch : Choice2011 G) (h21_17 : S21_17 D Ch)
    (hSchreier : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog) :
    S21_18 D Ch := by
  intro h1930 c hcomm
  have hF := (uc22p21c_commutator_bar_eq_bot_iff D.M).1 hcomm
  have hres := uc22p21c_perfectResidual_le_layer D Ch h21_17 hSchreier h1930 c hF
  exact (uc22p21c_Hinf_eq_iff D.M).2
    (le_antisymm hres (uc22p21c_le_perfectResidual _ CFSG.LocalCores.layer_perfect))

end Bridge

section TwentyThree

variable {G : Type} [Group G] [Finite G]

theorem uc22p21c_oResidual_eq_top_of_opRes {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {X : Subgroup Y} (h : UC22.F10.OpRes p X = X) : CFSG.GH74.GLS.oResidual p ↥X = ⊤ := by
  apply Subgroup.map_injective X.subtype_injective
  rw [← UC6.opRes_eq_map_oResidual_uc6 hp, h, Subgroup.map_top, Subgroup.range_subtype]

theorem uc22p21c_oResidual_bar_eq_top {M : Subgroup G} {p : ℕ} (hp : p.Prime)
    (h : UC22.F10.OpRes p M = M) : CFSG.GH74.GLS.oResidual p (Bar2 M) = ⊤ := by
  have htop := uc22p21c_oResidual_eq_top_of_opRes hp h
  apply top_unique
  calc (⊤ : Subgroup (Bar2 M)) = (⊤ : Subgroup ↥M).map (uc22p21cPi M) :=
        (Subgroup.map_top_of_surjective _ (uc22p21c_pi_surjective M)).symm
    _ = (CFSG.GH74.GLS.oResidual p ↥M).map (uc22p21cPi M) := by rw [htop]
    _ ≤ CFSG.GH74.GLS.oResidual p (Bar2 M) := by
        rw [Subgroup.map_le_iff_le_comap, CFSG.GH74.GLS.oResidual, Subgroup.closure_le]
        intro x hx
        exact Subgroup.subset_closure (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd _ x) hx)

theorem uc22p21c_pow_eq_one_of_mem {M P : Subgroup G} {p : ℕ} (hPp : IsPGroup p ↥P) (hPM : P ≤ M)
    {x : ↥M} (hx : (x : G) ∈ P) : ∃ k : ℕ, (uc22p21cPi M x) ^ (p ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hPp ⟨x, hx⟩
  refine ⟨k, ?_⟩
  have h1 : x ^ (p ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  rw [← map_pow, h1, map_one]

theorem s21_23_of (D : Data G) (Ch : Choice2011 G) (h21_18 : S21_18 D Ch) (h638 : UC6.R6_38 D) :
    S21_23 D Ch := by
  intro h1930 c p hpσ P hP hcyc
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hpσ
  haveI : Fact p.Prime := ⟨hpp⟩
  set M := D.M with hMdef
  have hK : IsCyclic ↥(centE M ⊓ commutator (Bar2 M)) :=
    uc22p21c_isCyclic_centralizer_layer_inf_commutator hcyc
  haveI hKn : (centE M ⊓ commutator (Bar2 M)).Normal :=
    uc22p21c_normal_centralizer_layer_inf_commutator (Bar2 M)
  have hcomm_le : ⁅centE M, centE M⁆ ≤ centE M ⊓ commutator (Bar2 M) :=
    le_inf (Subgroup.commutator_le_self _) (Subgroup.commutator_mono le_top le_top)
  have h1 : IsCyclic ↥⁅centE M, centE M⁆ :=
    isCyclic_of_injective (Subgroup.inclusion hcomm_le) (Subgroup.inclusion_injective _)
  have hF := uc22p21c_commutator_perfectResidual_fitting_eq_bot hcyc
  have hcomm' := (uc22p21c_commutator_bar_eq_bot_iff M).2 hF
  have h2 : CFSG.perfectResidual (Bar2 M) = CFSG.layer (Bar2 M) :=
    (uc22p21c_Hinf_eq_iff M).1 (h21_18 h1930 c hcomm')
  have hgen : CFSG.GH74.GLS.oResidual p (Bar2 M) = ⊤ :=
    uc22p21c_oResidual_bar_eq_top hpp (h638 p hpp hp2 (Or.inl hpσ))
  have hPX : P ≤ barPreimage M (centE M) := hP.le
  have hPp : IsPGroup p ↥P := hP.isPGroup
  have hPM : P ≤ M := hPX.trans (uc22p21c_barPreimage_le M _)
  have hbound : ∀ x : ↥M, (x : G) ∈ P → uc22p21cPi M x ∈ centE M ⊓ commutator (Bar2 M) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · obtain ⟨_, h⟩ := uc22p21c_mem_barPreimage.1 (hPX hx)
      exact h
    · obtain ⟨k, hk⟩ := uc22p21c_pow_eq_one_of_mem hPp hPM hx
      exact uc22p21c_mem_commutator_of_oResidual_eq_top hgen (orderOf_dvd_of_pow_eq_one hk)
  have hPle : barImage M P ≤ centE M ⊓ commutator (Bar2 M) := by
    intro q hq
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
    exact hbound m hm
  have hnorm : (barImage M P).Normal := uc22p21c_normal_of_le_cyclic_normal hPle
  let ψ : ↥P →* ↥(centE M ⊓ commutator (Bar2 M)) :=
    ((uc22p21cPi M).comp (Subgroup.inclusion hPM)).codRestrict _ (fun x => hbound _ x.2)
  have hinj : Function.Injective ψ := by
    intro a b hab
    have hab' : (uc22p21cPi M) (Subgroup.inclusion hPM a) =
        (uc22p21cPi M) (Subgroup.inclusion hPM b) := congrArg Subtype.val hab
    have h3 : (Subgroup.inclusion hPM (a * b⁻¹) : ↥M) ∈ CFSG.pCore 2 ↥M := by
      apply (QuotientGroup.eq_one_iff _).1
      show (uc22p21cPi M) (Subgroup.inclusion hPM (a * b⁻¹)) = 1
      rw [map_mul, map_inv, map_mul, map_inv, hab', mul_inv_cancel]
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨_, h3⟩
    obtain ⟨j, hj⟩ := hPp (a * b⁻¹)
    have hk' : (a * b⁻¹) ^ (2 ^ k) = 1 := by
      apply Subgroup.inclusion_injective hPM
      have := congrArg (fun y : ↥(CFSG.pCore 2 ↥M) => (y : ↥M)) hk
      simpa using this
    have hcop : Nat.Coprime (2 ^ k) (p ^ j) :=
      Nat.Coprime.pow k j ((Nat.coprime_primes Nat.prime_two hpp).2 (Ne.symm hp2))
    have hdvd : orderOf (a * b⁻¹) ∣ Nat.gcd (2 ^ k) (p ^ j) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hj)
    rw [hcop.gcd_eq_one] at hdvd
    have hone : a * b⁻¹ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    exact mul_inv_eq_one.mp hone
  exact ⟨h1, h2, hPle, hnorm, isCyclic_of_injective ψ hinj⟩

end TwentyThree

end CFSG.LocalAnalysis.UniquenessCase.UC22
