module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Rec
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddOut
public import CFSG.Adapters.LieModelSimple
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

private theorem even_card_of_lieModel_psu5 {S : Type} [Group S]
    (h : LieModel S .PSU 5 2 2) : Even (Nat.card S) := by
  have hsc := h.statedClassicalModel (t := .PSU) (by decide)
  rw [CFSG.Open.StatedClassicalModel] at hsc
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hsc
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU
    (K := K) (p := 2) (f := 2) (n := 5) (by norm_num) (by norm_num) hKcard (by norm_num)
  have hcardS : Nat.card S = Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K)) :=
    Nat.card_congr e.toEquiv
  rw [hcardS, hcard]
  decide

private theorem mem_of_conjNormal_inner_of_odd
    {U : Type} [CommGroup U] [Finite U] {N S : Subgroup (MulAut U)} (hSN : S ≤ N)
    (hN : (S.subgroupOf N).Normal)
    (hZ : Subgroup.center (S.subgroupOf N) = ⊥)
    (hCodd : Odd (Nat.card (Subgroup.centralizer (S.subgroupOf N : Set ↥N))))
    {t : MulAut U} (htN : t ∈ N) (ht2 : orderOf t = 2)
    (hInner : MulAut.conjNormal (H := S.subgroupOf N) ⟨t, htN⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(S.subgroupOf N)) :
    t ∈ S := by
  classical
  let L : Subgroup ↥N := S.subgroupOf N
  let C : Subgroup ↥N := Subgroup.centralizer (L : Set ↥N)
  haveI hLnorm : L.Normal := hN
  have hmem : (⟨t, htN⟩ : ↥N) ∈ L ⊔ C :=
    CFSG.Quasithin.H13.NQCore.mem_sup_centralizer_of_conjNormal_inner hInner
  obtain ⟨s, hsL, c, hcC, hsc⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have htN2 : (⟨t, htN⟩ : ↥N) * ⟨t, htN⟩ = 1 := Subtype.ext htt
  have hcomm : Commute s c := Subgroup.mem_centralizer_iff.mp hcC s hsL
  have hsq : s ^ 2 * c ^ 2 = 1 := by
    have := hcomm.mul_pow 2
    rw [hsc] at this
    rw [show (⟨t, htN⟩ : ↥N) ^ 2 = 1 by simpa [pow_two] using htN2] at this
    exact this.symm
  have hs2eq : s ^ 2 = (c ^ 2)⁻¹ := by
    have h1 := congrArg (fun x : ↥N => x * (c ^ 2)⁻¹) hsq
    simpa [mul_assoc] using h1
  have hs2C : s ^ 2 ∈ C := by
    rw [hs2eq]
    exact C.inv_mem (C.pow_mem hcC 2)
  have hs2L : s ^ 2 ∈ L := L.pow_mem hsL 2
  have hs2center : (⟨s ^ 2, hs2L⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hs2C (z : ↥N) z.2
  have hs2 : s ^ 2 = 1 := by
    have hbot : (⟨s ^ 2, hs2L⟩ : ↥L) = 1 := by
      have := hs2center
      rw [hZ, Subgroup.mem_bot] at this
      exact this
    exact congrArg Subtype.val hbot
  have hc2 : c ^ 2 = 1 := by
    rw [hs2, one_mul] at hsq
    exact hsq
  have hcCodd : Odd (orderOf c) := by
    let cC : C := ⟨c, hcC⟩
    have hdvd : orderOf cC ∣ Nat.card C := orderOf_dvd_natCard cC
    have hcoe : orderOf c = orderOf cC := Subgroup.orderOf_coe cC
    rw [hcoe]
    exact hCodd.of_dvd_nat hdvd
  have hc1 : c = 1 := by
    have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hcCodd
      norm_num at hcCodd
  have htN_eq : (⟨t, htN⟩ : ↥N) = s := by
    rw [← hsc, hc1, mul_one]
  have htS : t ∈ S := by
    have hsN : s ∈ L := hsL
    have hsS : (s : MulAut U) ∈ S := Subgroup.mem_subgroupOf.mp hsN
    have ht_eq : t = (s : MulAut U) := by
      have := congrArg (fun z : ↥N => (z : MulAut U)) htN_eq
      simpa using this
    rw [ht_eq]
    exact hsS
  exact htS

private theorem orderOf_two_zmod_forty_one : orderOf (2 : ZMod 41) = 20 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · decide
  · intro k hk hk0
    interval_cases k <;> decide

private theorem nine_le_rkIdx_of_inverts_of_order_forty_one
    {U : Type} [CommGroup U] [Finite U] (hW : ∀ u : U, u ^ 2 = 1)
    {t y : MulAut U} (ht : t * t = 1) (hy : orderOf y = 41)
    (hty : t * y * t⁻¹ = y⁻¹) :
    9 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  have hodd : Odd 41 := by norm_num
  have hy41 : y ^ 41 = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    norm_num at hy
  have hsq := CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.index_fixV_le_sq_of_inverts
    (W := U) (p := 41) hodd hy41 ht hty
  have hW' : ∀ w : U, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  have hppd := CFSG.QuasithinUnique.Setup.X5.two_pow_orderOf_le_index_fixV
    (W := U) hW' (ℓ := 41) (by norm_num) hy41 hy1
  have h20le : 2 ^ 20 ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
    calc 2 ^ 20 = 2 ^ orderOf (2 : ZMod 41) := by rw [orderOf_two_zmod_forty_one]
      _ ≤ (fixV (Subgroup.zpowers y)).index := hppd
      _ ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := hsq
  have hidx : (fixV (Subgroup.zpowers t)).index =
      2 ^ rkIdx (fixV (Subgroup.zpowers t)) :=
    CFSG.Quasithin.B1.index_eq_two_pow hW _
  rw [hidx, ← pow_mul] at h20le
  have h20 : 20 ≤ rkIdx (fixV (Subgroup.zpowers t)) * 2 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h20le
  omega

private theorem centralizer_subgroupOf_odd
    {U : Type} [CommGroup U] [Finite U] {N S : Subgroup (MulAut U)} (hSN : S ≤ N)
    (hCodd : Odd (Nat.card (Subgroup.centralizer (S : Set (MulAut U))))) :
    Odd (Nat.card (Subgroup.centralizer (S.subgroupOf N : Set ↥N))) := by
  classical
  let C₁ : Subgroup ↥N := Subgroup.centralizer (S.subgroupOf N : Set ↥N)
  let C₂ : Subgroup (MulAut U) := Subgroup.centralizer (S : Set (MulAut U))
  have hmap : ∀ c : C₁, ((c : ↥N) : MulAut U) ∈ C₂ := by
    intro c
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxN : x ∈ N := hSN hx
    have hxL : (⟨x, hxN⟩ : ↥N) ∈ S.subgroupOf N := Subgroup.mem_subgroupOf.mpr hx
    have h := Subgroup.mem_centralizer_iff.mp c.2 (⟨x, hxN⟩ : ↥N) hxL
    exact congrArg (fun z : ↥N => (z : MulAut U)) h
  let φ : C₁ →* C₂ :=
    { toFun := fun c => ⟨((c : ↥N) : MulAut U), hmap c⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun z : C₂ => (z : MulAut U)) hab
    simpa [φ] using this
  exact hCodd.of_dvd_nat (Subgroup.card_dvd_of_injective φ hinj)

theorem k146ModU54_of (hin : K146U54InvRank) (hout : K146U54OuterInv) : K146ModU54 := by
  intro U _ _ hW N S hSN hN hLie hIrr
  classical
  have hUtriv : Nontrivial U := by
    have htopne : (⊤ : Subgroup U) ≠ ⊥ := ne_of_gt hIrr.1
    have hne : ∃ u : U, u ≠ 1 := by
      by_contra h
      apply htopne
      ext u
      simpa using not_exists.mp h u
    obtain ⟨u, hu⟩ := hne
    exact ⟨1, u, fun h1 => hu h1.symm⟩
  letI : Nontrivial U := hUtriv
  have hW' : ∀ w : U, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  have hIrrOn : ∀ H : Subgroup U, (∀ g ∈ S, ∀ u ∈ H, g u ∈ H) → H = ⊥ ∨ H = ⊤ :=
    fun H hH => hIrr.2.2.2 H hH bot_le le_top
  have hCoddS : Odd (Nat.card (Subgroup.centralizer (S : Set (MulAut U)))) :=
    CFSG.QuasithinUnique.Setup.X5.centralizer_odd hW' S hIrrOn
  have hCoddN : Odd (Nat.card (Subgroup.centralizer (S.subgroupOf N : Set ↥N))) :=
    centralizer_subgroupOf_odd hSN hCoddS
  let L : Subgroup ↥N := S.subgroupOf N
  let eL : ↥L ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSN
  have hZbotS : Subgroup.center ↥S = ⊥ :=
    (CFSG.Quasithin.H13.F431.Un.f431ModelFacts_un5 2 ↥S hLie).2
  have hZ : Subgroup.center L = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv eL hZbotS
  have hLieL : LieModel ↥L .PSU 5 2 2 := hLie.of_mulEquiv eL.symm
  have hSeven : Even (Nat.card S) := even_card_of_lieModel_psu5 hLie
  have hSdvd : Nat.card S ∣ Nat.card N := Subgroup.card_dvd_of_le hSN
  have hNeven : Even (Nat.card N) :=
    even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hSeven) hSdvd)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2dvd : 2 ∣ Nat.card S := even_iff_two_dvd.mp hSeven
  obtain ⟨lS, hlS⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 2 h2dvd
  have hNne : ∃ t ∈ N, orderOf t = 2 := by
    refine ⟨(lS : MulAut U), hSN lS.2, ?_⟩
    rw [Subgroup.orderOf_coe lS]
    exact hlS
  have hSsimple : IsSimpleGroup ↥S :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hLie
  have hfixS : fixV S = ⊥ := by
    have hstable : ∀ x ∈ S, ∀ u ∈ fixV S, x u ∈ fixV S := by
      intro x hx u hu
      rw [mem_fixV] at hu ⊢
      intro y hy
      rw [hu x hx]
      exact hu y hy
    rcases hIrr.2.2.2 (fixV S) hstable bot_le le_top with h | h
    · exact h
    · exfalso
      have hSbot : S = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        ext u
        have hu : u ∈ fixV S := by rw [h]; exact Subgroup.mem_top u
        exact (mem_fixV.mp hu) x hx
      have hSne : S ≠ ⊥ := by
        intro hbot
        have hmem : (lS : MulAut U) ∈ (⊥ : Subgroup (MulAut U)) := by
          rw [← hbot]; exact lS.2
        have h1 : (lS : MulAut U) = 1 := by simpa using hmem
        have h1' : lS = 1 := S.subtype_injective h1
        rw [h1', orderOf_one] at hlS
        omega
      exact hSne hSbot
  refine CFSG.Quasithin.le_mParam_of_forall_involutions N 9 hNeven hNne ?_
  intro t htN ht2
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  let tN : ↥N := ⟨t, htN⟩
  let α : MulAut ↥L := MulAut.conjNormal (H := L) tN
  have htN2 : tN * tN = 1 := Subtype.ext htt
  have hα2 : α ^ 2 = 1 := by
    change (MulAut.conjNormal (H := L) tN) ^ 2 = 1
    rw [← map_pow]
    rw [show tN ^ 2 = 1 by simpa [pow_two] using htN2, map_one]
  by_cases hInner : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L
  · have htS : t ∈ S := mem_of_conjNormal_inner_of_odd hSN hN hZ hCoddN htN ht2 hInner
    have ht1 : t ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at ht2
      omega
    have hb := CFSG.Quasithin.le_rkIdx_of_involution_mul_centralizing
      (W := U) hW S hSsimple hfixS 9 (hin ↥S hLie) htS
      (by rw [pow_two]; exact htt) ht1 (fun x hx => by rw [one_mul, mul_one])
      (by norm_num)
    simpa using hb
  · have hOuter : ¬ ∃ g : ↥L, ∀ x, α x = g * x * g⁻¹ := by
      rintro ⟨g, hg⟩
      apply hInner
      refine ⟨g, MulEquiv.ext fun x => ?_⟩
      rw [MulAut.conj_apply]
      exact (hg x).symm
    obtain ⟨y, hyord, hyinv⟩ := hout (S := ↥L) hLieL α hα2 hOuter
    have hyordN : orderOf (y : ↥N) = 41 := by
      rw [Subgroup.orderOf_coe y]
      exact hyord
    have hyordU : orderOf (y : MulAut U) = 41 := by
      rw [Subgroup.orderOf_coe (y : ↥N)]
      exact hyordN
    have hty : t * (y : MulAut U) * t⁻¹ = (y : MulAut U)⁻¹ := by
      have h := congrArg (fun z : ↥L => ((z : ↥N) : MulAut U)) hyinv
      simpa [α, MulAut.conjNormal_apply] using h
    exact nine_le_rkIdx_of_inverts_of_order_forty_one hW htt hyordU hty

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
