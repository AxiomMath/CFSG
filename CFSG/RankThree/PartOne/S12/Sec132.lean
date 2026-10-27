module

public import CFSG.RankThree.PartOne.S12.Sec12A
import CFSG.RankThree.PartOne.S12.PerfectOddPrime
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G]

theorem Sec12Hyp.mem_of_pow_eq_one_of_commute {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) {x : G} (hx : x ^ p = 1) (hxE : ∀ a ∈ E, a * x = x * a) :
    x ∈ E := by
  have := IsElementaryAbelian.zpowers_of_pow_eq_one hx
  have := h.E_elem
  have hF : IsElementaryAbelian p ↥(E ⊔ Subgroup.zpowers x) :=
    IsElementaryAbelian.sup_of_le_centralizer (E := E) (C := Subgroup.zpowers x) (by
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Commute.zpow_right (hxE a ha) k).eq)
  have heq := h.E_max_global (E ⊔ Subgroup.zpowers x) hF le_sup_left
  have hmem : x ∈ E ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rwa [heq] at hmem

omit [Finite G] in
theorem isPerfect_map_subtype' {H : Subgroup G} {L : Subgroup H} (hL : Group.IsPerfect L) :
    Group.IsPerfect (L.map H.subtype) :=
  Group.IsPerfect.ofSurjective (f := (L.equivMapOfInjective H.subtype
    H.subtype_injective).toMonoidHom) (MulEquiv.surjective _)

omit [Finite G] in
theorem isPerfect_sSup_of_forall_isPerfect' {S : Set (Subgroup G)}
    (h : ∀ M ∈ S, Group.IsPerfect M) : Group.IsPerfect (sSup S : Subgroup G) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) (sSup_le fun M hM => ?_)
  · rw [commutatorElement_def]
    exact (sSup S).mul_mem ((sSup S).mul_mem ((sSup S).mul_mem ha hb) ((sSup S).inv_mem ha))
      ((sSup S).inv_mem hb)
  · calc M = ⁅M, M⁆ := (Subgroup.isPerfect_iff.mp (h M hM)).symm
      _ ≤ ⁅sSup S, sSup S⁆ := Subgroup.commutator_mono (le_sSup hM) (le_sSup hM)

omit [Finite G] in
theorem mem_of_pow_eq_one_of_mem_sup_centralizer' {p : ℕ} {L' T : Subgroup G}
    (hT : T ≤ Subgroup.centralizer (L' : Set G)) (hcop : ∀ v ∈ T, Nat.Coprime (orderOf v) p)
    {y : G} (hy : y ∈ L' ⊔ T) {k : ℕ} (hyk : y ^ (p ^ k) = 1) : y ∈ L' := by
  have hN : T ≤ Subgroup.normalizer (L' : Set G) :=
    hT.trans (Subgroup.centralizer_le_normalizer _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L' T hN] at hy
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hy
  have hcomm : Commute u v := Subgroup.mem_centralizer_iff.mp (hT hv) u hu
  rw [hcomm.mul_pow] at hyk
  have hv3 : v ^ (p ^ k) ∈ L' := by
    rw [eq_inv_of_mul_eq_one_right hyk]
    exact L'.inv_mem (L'.pow_mem hu _)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (Nat.Coprime.pow_left k (hcop v hv).symm)
  have hvL : v ∈ L' := by
    rw [← hm]
    exact L'.pow_mem hv3 m
  exact L'.mul_mem hu hvL

theorem kZero_le_of_mem_torusImage {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hnorm : SelectedPrimeElementsNormalizeThetaComponents)
    {t : MulAut E} (ht : t ∈ torusImage E L)
    (hdec : E = autFixedInG E t ⊔ autMovedInG E t) : kZero p E t ≤ L := by
  classical
  have hp : p.Prime := h.prime
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have : Fact p.Prime := ⟨hp⟩
  have hEel : IsElementaryAbelian p E := h.E_elem
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEel.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hLθ : L ∈ thetaComponentsAt p c := h.L_mem.2
  obtain ⟨hLC, hLth⟩ := mem_thetaComponentsAt_iff.mp hLθ
  have hEL : E ≤ Subgroup.normalizer (L : Set G) :=
    h.E_normalizes_thetaComponentsAt hnorm hcE hLθ
  obtain ⟨n, hn, htn⟩ := Subgroup.mem_map.1 ht
  have hℓL : (n : G) ∈ L := Subgroup.mem_subgroupOf.mp hn
  have hℓt : ∀ e : E, ((t e : E) : G) = (n : G) * e * (n : G)⁻¹ := fun e => by
    rw [← htn]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe E n e
  have hℓc : (n : G) * c = c * (n : G) := Subgroup.mem_centralizer_singleton_iff.mp (hLC hℓL)
  have hcF : c ∈ autFixedInG E t := by
    refine ⟨⟨c, hcE⟩, ?_, rfl⟩
    show t ⟨c, hcE⟩ = ⟨c, hcE⟩
    apply Subtype.ext
    rw [hℓt]
    show (n : G) * c * (n : G)⁻¹ = c
    rw [hℓc, mul_inv_cancel_right]
  set X : Subgroup G := Subgroup.centralizer ((autFixedInG E t : Subgroup G) : Set G) with hXdef
  have hXc : X ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcF)
  have hFE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hME : autMovedInG E t ≤ E := Subgroup.map_subtype_le _
  have hEX : E ≤ X := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hEc b (hFE hb) a ha
  set Y : Subgroup X := (L ⊓ X).subgroupOf X with hYdef
  have hY : Y.IsSubnormal := by
    have h1 := hLth.2.1.comap (Subgroup.inclusion hXc)
    convert h1 using 1
    ext x
    simp only [hYdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap,
      Subgroup.coe_inclusion]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  have hYmap : Y.map X.subtype = L ⊓ X := by
    rw [hYdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have hMLX : autMovedInG E t ≤ L ⊓ X := by
    refine le_inf ?_ (hME.trans hEX)
    unfold autMovedInG
    rw [Subgroup.map_le_iff_le_comap]
    unfold autMoved
    rw [Subgroup.closure_le]
    rintro _ ⟨e, rfl⟩
    show ((t e * e⁻¹ : E) : G) ∈ L
    have h1 : (e : G) * (n : G)⁻¹ * (e : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hEL e.2) (n : G)⁻¹).mp (L.inv_mem hℓL)
    have h2 := L.mul_mem hℓL h1
    rw [Subgroup.coe_mul, hℓt, Subgroup.coe_inv]
    rwa [show (n : G) * ((e : G) * (n : G)⁻¹ * (e : G)⁻¹) =
      (n : G) * (e : G) * (n : G)⁻¹ * (e : G)⁻¹ by group] at h2
  set S : Set (Subgroup G) :=
    {M | ∃ K : Subgroup X, IsComponent K ∧ ⁅K, Y⁆ = ⊥ ∧ K.map X.subtype = M} with hSdef
  set T : Subgroup G := sSup S with hTdef
  have hSC : ∀ M ∈ S, M ≤ Subgroup.centralizer ((L ⊓ X : Subgroup G) : Set G) := by
    rintro M ⟨K, -, hKY, rfl⟩
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← hYmap, ← Subgroup.map_commutator,
      hKY, Subgroup.map_bot]
  have hSE : ∀ M ∈ S, M ≤ Subgroup.centralizer (E : Set G) := by
    intro M hM g hg
    have hgX : g ∈ X := by
      obtain ⟨K, -, -, rfl⟩ := hM
      exact Subgroup.map_subtype_le K hg
    have hgL := hSC M hM hg
    have h1 : autFixedInG E t ≤ Subgroup.centralizer ({g} : Set G) := fun b hb =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        exact (Subgroup.mem_centralizer_iff.mp hgX b hb).symm
    have h2 : autMovedInG E t ≤ Subgroup.centralizer ({g} : Set G) := fun b hb =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        exact (Subgroup.mem_centralizer_iff.mp hgL b (hMLX hb)).symm
    have h3 : autFixedInG E t ⊔ autMovedInG E t ≤ Subgroup.centralizer ({g} : Set G) :=
      sup_le h1 h2
    rw [← hdec] at h3
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (h3 ha) g rfl).symm
  have hSp : ∀ M ∈ S, Group.IsPerfect M := by
    rintro M ⟨K, hK, -, rfl⟩
    exact isPerfect_map_subtype' hK.1.1
  have hTC : T ≤ Subgroup.centralizer ((L ⊓ X : Subgroup G) : Set G) := sSup_le hSC
  have hTE : T ≤ Subgroup.centralizer (E : Set G) := sSup_le hSE
  have hTp : Group.IsPerfect T := isPerfect_sSup_of_forall_isPerfect' hSp
  have hT3 : ¬ p ∣ Nat.card T := by
    intro hdvd
    obtain ⟨e, he, hecenter⟩ := exists_pow_eq_one_not_mem_center_of_isPerfect hp2 hTp hdvd
    have heE : (e : G) ∈ E :=
      h.mem_of_pow_eq_one_of_commute (by simpa using congrArg Subtype.val he)
        (fun a ha => Subgroup.mem_centralizer_iff.mp (hTE e.2) a ha)
    apply hecenter
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hTE z.2) e heE).symm
  have hcop : ∀ v ∈ T, Nat.Coprime (orderOf v) p := by
    intro v hv
    have hdvd : orderOf v ∣ Nat.card T := by
      rw [← Subgroup.orderOf_mk v hv]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_left hdvd
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hT3).symm
  have hE : inSubgroup (fun K _ => CFSG.layer K) X ≤ (L ⊓ X) ⊔ T := by
    show (CFSG.layer ↥X).map X.subtype ≤ _
    rw [Subgroup.map_le_iff_le_comap, CFSG.layer]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    rcases CFSG.LocalCores.component_subnormal_subgroup hK hY with hKY | hKY
    · exact (Subgroup.map_mono hKY).trans (hYmap.le.trans le_sup_left)
    · exact (le_sSup ⟨K, hK, hKY, rfl⟩ : K.map X.subtype ≤ T).trans le_sup_right
  unfold kZero pElementSubgroup
  rw [Subgroup.closure_le]
  rintro x ⟨hxY, k, hk⟩
  have hxk : x ^ (p ^ k) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one x
  exact (mem_of_pow_eq_one_of_mem_sup_centralizer' hTC hcop (hE hxY) hxk).1

theorem isKt_le_of_mem_torusImage {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hnorm : SelectedPrimeElementsNormalizeThetaComponents)
    {t : MulAut E} (ht : t ∈ torusImage E L) (hdec : E = autFixedInG E t ⊔ autMovedInG E t)
    {K : Subgroup G} (hK : IsKt p E t K) : K ≤ L := by
  have hk : K ≤ kZero p E t := by
    by_cases hex : ∃ f, kExceptional p (kZero p E t) f
    · obtain ⟨f, hf⟩ := hex
      exact (hK.1 f hf).1
    · exact (hK.2 hex).le
  exact hk.trans (kZero_le_of_mem_torusImage h hnorm ht hdec)

end CFSG.RankThree.PartOne
