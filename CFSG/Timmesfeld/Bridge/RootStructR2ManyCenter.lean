module

public import CFSG.Timmesfeld.Bridge.RootStructR2ManySetting
public import CFSG.Timmesfeld.Bridge.RootStructR2ManyNat
public import CFSG.Timmesfeld.Bridge.RootStructR2ManySmall
public import CFSG.Timmesfeld.Bridge.RootClosureGen
public import CFSG.Timmesfeld.Bridge.RootStructWTIModStep

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open CFSG.Timmesfeld.ARS.NaturalModule (diagElt diagElt_inv diagElt_mul_diagElt
  diagElt_mem_normalizer_upperUnipotent weylElt weylElt_mul_self weylElt_mul_upperElt_mul_weylElt)
open CFSG.Timmesfeld.RankOne (mem_upperUnipotent_iff mem_lowerUnipotent_iff upperElt lowerElt)

namespace RootMany

variable {G : Type} [Group G] {D : Set G}

theorem le_normalizer_of_conj_mem {S T : Subgroup G} (h : ∀ g ∈ S, ∀ t ∈ T, g * t * g⁻¹ ∈ T) :
    S ≤ Subgroup.normalizer (T : Set G) := fun g hg => by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨h g hg t, fun ht => ?_⟩
  have := h g⁻¹ (inv_mem hg) _ ht
  simpa [mul_assoc] using this

variable [Finite G] (C : ThinGateCounter G D) {a d : G} (ha : a ∈ D) (hd : d ∈ D)
  (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)

include C ha hd had in
theorem nCore_le_normalizer_line :
    nCore D a ≤ Subgroup.normalizer ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun g hg t ht => ?_
  have h := (nCore_le_transv C ha hd had hg).2 t ht
  have e : g * t * g⁻¹ = (g * t * g⁻¹ * t⁻¹) * t := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left h) ht

omit [Finite G] in
include C ha hd had in
theorem mem_rootGroup_of_mem_line_of_commute (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D)
    (hax : Commute a x) (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {t : G}
    (ht : t ∈ rootGroup D a ⊔ rootGroup D d) (htx : Commute t x) : t ∈ rootGroup D a := by
  have hLS := lineSetting_of_counter C
  have hxa : x ∉ rootSet D a := fun h => hxT (Subgroup.mem_sup_left
    (rootSet_subset_rootGroup D a h))
  have hdL : d ∉ rootGroup D a ⊔ rootGroup D x := fun h =>
    hxT (by
      rw [hLS.sup_rootGroup_eq_of_mem_sup ha hd hx had hdT hax haxD hxa h]
      exact right_mem_line hx)
  have hbot := hLS.rootGroup_inf_centralizer_eq_bot ha hx hax haxD hxa hd had hdL
  obtain ⟨α, hα, δ, hδ, rfl⟩ := exists_mul_eq_of_mem_line hd had ht
  have hαx : Commute α x :=
    commute_of_mem_rootGroup_of_commute' hx hα (rootSet_subset_rootGroup D x (mem_rootSet_self hx))
      hax
  have hδx : Commute δ x := by
    have := hαx.inv_left.mul_left htx
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have : δ ∈ rootGroup D d ⊓ Subgroup.centralizer {x} :=
    ⟨hδ, Subgroup.mem_centralizer_singleton_iff.2 hδx.eq⟩
  rw [hbot, Subgroup.mem_bot] at this
  rw [this, mul_one]
  exact hα

section Torus

variable {q : ℕ} (K : ThinGateCount G D q 2 2)
include C K ha hd had hadD hdT

theorem nCenter_le_lineN₀ (hM : Nat.card (nCore D a) < q ^ 6) : nCenter D a ≤ lineN₀ D a d := by
  classical
  have hLS := lineSetting_of_counter C
  have hclass := C.hyp.isClass
  have hD := C.hyp.root
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have haT : a ∉ rootSet D d := fun h => hdT (mem_rootSet_comm hd h)
  obtain ⟨x, hx, hax, haxD, hxT⟩ := exists_point C ha hd had hadD hdT
  obtain ⟨y, hy, hdy, hdyD, hyT'⟩ := exists_point C hd ha had.symm hdaD haT
  have hyT : y ∉ rootGroup D a ⊔ rootGroup D d := by rwa [sup_comm] at hyT'
  obtain ⟨e, he, φ, hφx, hφy⟩ :=
    hLS.exists_mulEquiv_SL2_line ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT
  obtain ⟨k, Nf, θ, hθ, -, hsup, hcardN, -, -⟩ :=
    hLS.exists_natural_lineN ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT φ hφx hφy
  have hH := hLS.quotModHyp ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT
  set τ : (GaloisField 2 e)ˣ → G := fun t => ((φ.symm (diagElt t) :
    ↥(rootGroup D x ⊔ rootGroup D y)) : G) with hτ
  have hτX : ∀ t, τ t ∈ rootGroup D x ⊔ rootGroup D y := fun t => (φ.symm (diagElt t)).2
  have hτinv : ∀ t, (τ t)⁻¹ = τ t⁻¹ := by
    intro t
    simp only [hτ]
    rw [← Subgroup.coe_inv, ← map_inv, diagElt_inv]
  have hτmul : ∀ s t, (τ s)⁻¹ * τ t = τ (s⁻¹ * t) := by
    intro s t
    simp only [hτ]
    rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← map_inv, ← map_mul, diagElt_inv,
      diagElt_mul_diagElt]
  have hτAx : ∀ t, τ t ∈ Subgroup.normalizer (rootGroup D x : Set G) := fun t =>
    ARS.NaturalModule.coe_mem_normalizer hφx le_sup_left (by
      rw [MulEquiv.apply_symm_apply]
      exact diagElt_mem_normalizer_upperUnipotent t)
  have hXT : rootGroup D x ⊔ rootGroup D y ≤
      Subgroup.normalizer ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) := by
    refine sup_le ((hLS.rootGroup_le_nCore ha hax).trans (nCore_le_normalizer_line C ha hd had))
      ?_
    have := (hLS.rootGroup_le_nCore hd hdy).trans
      (nCore_le_normalizer_line C hd ha had.symm)
    rwa [sup_comm] at this
  have hτA : ∀ t, ∀ α ∈ rootGroup D a, τ t * α * (τ t)⁻¹ ∈ rootGroup D a := by
    intro t α hα
    have hαT : α ∈ rootGroup D a ⊔ rootGroup D d := Subgroup.mem_sup_left hα
    refine mem_rootGroup_of_mem_line_of_commute C ha hd had hdT hx hax haxD hxT
      ((Subgroup.mem_normalizer_iff.1 (hXT (hτX t)) α).1 hαT) ?_
    have hx' : (τ t)⁻¹ * x * (τ t)⁻¹⁻¹ ∈ rootGroup D x :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem (hτAx t)) x).1
        (rootSet_subset_rootGroup D x (mem_rootSet_self hx))
    have hc : Commute α ((τ t)⁻¹ * x * (τ t)⁻¹⁻¹) :=
      (commute_of_mem_nCore_of_mem_rootGroup (hLS.rootGroup_le_nCore ha hax hx') hα).symm
    have h := hc.map (MulAut.conj (τ t))
    simp only [MulAut.conj_apply] at h
    convert h using 1
    group
  have hτM : ∀ t, ∀ m ∈ nCore D a, τ t * m * (τ t)⁻¹ ∈ nCore D a := by
    intro t m hm
    have h1 := conj_mem_nCore_conj hclass hm (τ t)
    have hαA := hτA t a (rootSet_subset_rootGroup D a (mem_rootSet_self ha))
    have hαD : τ t * a * (τ t)⁻¹ ∈ D := C.hyp.conj_mem _ ha
    have hαT : τ t * a * (τ t)⁻¹ ∈ rootSet D a := by
      rcases (mem_rootGroup_iff_of_rootClosure hD C.closure ha).1 hαA with h | h
      · exact absurd h (hD.ne_one hαD)
      · exact h
    rwa [hLS.nCore_eq_of_mem_rootSet ha hαT] at h1
  have hτZ : ∀ t, ∀ z ∈ nCenter D a, τ t * z * (τ t)⁻¹ ∈ nCenter D a := by
    intro t z hz
    rw [mem_nCenter] at hz ⊢
    refine ⟨hτM t z hz.1, fun m hm => ?_⟩
    have hm' : (τ t)⁻¹ * m * (τ t)⁻¹⁻¹ ∈ nCore D a := by
      rw [hτinv]
      exact hτM _ m hm
    have h := (hz.2 _ hm').map (MulAut.conj (τ t))
    simp only [MulAut.conj_apply] at h
    convert h using 1
    group
  have hτN₀ : ∀ t, ∀ n ∈ lineN₀ D a d, τ t * n * (τ t)⁻¹ ∈ lineN₀ D a d :=
    fun t n hn => hH.conj₀ _ (hτX t) n hn
  intro z hz
  by_contra hzN
  have hdM : d ∈ nCore D a := hLS.sup_rootGroup_le_nCore ha hd had (right_mem_line hd)
  have hzN' : z ∈ lineN D a d := Subgroup.mem_sup_left
    ⟨(mem_nCenter.1 hz).1, Subgroup.mem_centralizer_singleton_iff.2 ((mem_nCenter.1 hz).2 d hdM).eq⟩
  have hback : ∀ t, τ t * z * (τ t)⁻¹ ∈ lineN₀ D a d → z ∈ lineN₀ D a d := by
    intro t h
    have := hτN₀ t⁻¹ _ h
    rwa [← hτinv, show (τ t)⁻¹ * (τ t * z * (τ t)⁻¹) * (τ t)⁻¹⁻¹ = z by group] at this
  let F : Option (GaloisField 2 e)ˣ → G := fun i => i.elim 1 fun t => τ t * z * (τ t)⁻¹
  have hFZ : ∀ i, F i ∈ nCenter D a := by
    rintro (_ | t)
    · exact one_mem _
    · exact hτZ t z hz
  have hFinj : ∀ i j, (F i)⁻¹ * F j ∈ lineN₀ D a d → i = j := by
    rintro (_ | s) (_ | t) h
    · rfl
    · exact absurd (hback t (by simpa [F] using h)) hzN
    · exact absurd (hback s (by simpa [F] using inv_mem h)) hzN
    · by_contra hst
      have hst' : s⁻¹ * t ≠ 1 := fun h' => hst (by
        rw [inv_mul_eq_one] at h'
        rw [h'])
      have h1 := hτN₀ s⁻¹ _ h
      have e1 : τ s⁻¹ * ((F (some s))⁻¹ * F (some t)) * (τ s⁻¹)⁻¹ =
          z⁻¹ * ((τ (s⁻¹ * t)) * z * (τ (s⁻¹ * t))⁻¹) := by
        simp only [F, Option.elim_some]
        rw [← hτmul, ← hτinv, inv_inv]
        group
      rw [e1] at h1
      exact hzN (QuotMod.mem_of_diag_conj hH φ hθ hsup hcardN hst' hzN' h1)
  let Φ : Option (GaloisField 2 e)ˣ × ↥(rootGroup D a) → ↥(nCenter D a) := fun p =>
    ⟨F p.1 * p.2, mul_mem (hFZ p.1) (rootGroup_le_nCenter C ha hd had p.2.2)⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨i, α⟩ ⟨j, β⟩ h
    have h' : F i * α = F j * β := congrArg Subtype.val h
    have hij : i = j := by
      refine (hFinj j i ?_).symm
      have : (F j)⁻¹ * F i = β * (α : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
      rw [this]
      exact hLS.line_le_lineN₀ ha hd had (Subgroup.mem_sup_left (mul_mem β.2 (inv_mem α.2)))
    subst hij
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h'))
  have h1 := Nat.card_le_card_of_injective Φ hΦ
  have hopt : Nat.card (Option (GaloisField 2 e)ˣ) = Nat.card (GaloisField 2 e)ˣ + 1 := by
    have : Fintype (GaloisField 2 e)ˣ := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]
  rw [Nat.card_prod, hopt, Nat.card_units, GaloisField.card 2 e (by
    rintro rfl
    rw [pow_zero, K.card_rootGroup a ha] at he
    have := two_le_q C K ha
    omega), ← he, K.card_rootGroup a ha] at h1
  have hq := two_le_q C K ha
  have h2 := card_nCenter_lt C K ha hd had hadD hdT hM
  have : q - 1 + 1 = q := by omega
  rw [this] at h1
  nlinarith

end Torus

section Weyl

variable {q : ℕ} (K : ThinGateCount G D q 2 2)
include C K ha hd had hadD hdT

omit [Finite G] C ha hd had hadD hdT K in
theorem nCore_inf_le_lineGroup : nCore D d ⊓ Subgroup.centralizer {a} ≤ lineGroup D a d :=
  fun u hu => Subgroup.mem_iSup_of_mem ⟨1, one_mem _⟩ ⟨u, Subgroup.mem_sup_left hu, by simp⟩

theorem exists_mul_mem_nCenter (hM : Nat.card (nCore D a) < q ^ 6) {z : G}
    (hz : z ∈ nCenter D a) : ∃ α ∈ rootGroup D a, z * α ∈ nCenter D d := by
  classical
  have hLS := lineSetting_of_counter C
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have haT : a ∉ rootSet D d := fun h => hdT (mem_rootSet_comm hd h)
  obtain ⟨x, hx, hax, haxD, hxT⟩ := exists_point C ha hd had hadD hdT
  obtain ⟨y, hy, hdy, hdyD, hyT'⟩ := exists_point C hd ha had.symm hdaD haT
  have hyT : y ∉ rootGroup D a ⊔ rootGroup D d := by rwa [sup_comm] at hyT'
  obtain ⟨e, -, φ, hφx, hφy⟩ :=
    hLS.exists_mulEquiv_SL2_line ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT
  have hzMd : z ∈ nCore D d := (nCenter_le_lineN₀ C ha hd had hadD hdT K hM hz).2
  have hzZ := mem_nCenter.1 hz
  have hTd : rootGroup D a ⊔ rootGroup D d ≤ nCore D d := by
    rw [sup_comm]
    exact hLS.sup_rootGroup_le_nCore hd ha had.symm
  have hNa := nCore_le_normalizer_line C ha hd had
  have hNd : nCore D d ≤
      Subgroup.normalizer ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) := by
    have := nCore_le_normalizer_line C hd ha had.symm
    rwa [sup_comm] at this
  let S : Subgroup G :=
    { carrier := {ξ | ξ ∈ Subgroup.normalizer ((rootGroup D a ⊔ rootGroup D d : Subgroup G) :
        Set G) ∧ z⁻¹ * (ξ * z * ξ⁻¹) ∈ rootGroup D a ⊔ rootGroup D d}
      mul_mem' := by
        rintro ξ ξ' ⟨hξ, h1⟩ ⟨hξ', h2⟩
        refine ⟨mul_mem hξ hξ', ?_⟩
        have e : z⁻¹ * (ξ * ξ' * z * (ξ * ξ')⁻¹) =
            (z⁻¹ * (ξ * z * ξ⁻¹)) * (ξ * (z⁻¹ * (ξ' * z * ξ'⁻¹)) * ξ⁻¹) := by group
        rw [e]
        exact mul_mem h1 ((Subgroup.mem_normalizer_iff.1 hξ _).1 h2)
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro ξ ⟨hξ, h1⟩
        refine ⟨inv_mem hξ, ?_⟩
        have e : z⁻¹ * (ξ⁻¹ * z * ξ⁻¹⁻¹) = ξ⁻¹ * (z⁻¹ * (ξ * z * ξ⁻¹))⁻¹ * ξ⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (inv_mem hξ) _).1 (inv_mem h1) }
  have hXS : rootGroup D x ⊔ rootGroup D y ≤ S := by
    refine sup_le (fun ξ hξ => ⟨hNa (hLS.rootGroup_le_nCore ha hax hξ), ?_⟩)
      (fun η hη => ⟨hNd (hLS.rootGroup_le_nCore hd hdy hη), ?_⟩)
    · rw [(hzZ.2 ξ (hLS.rootGroup_le_nCore ha hax hξ)).symm.eq, mul_inv_cancel_right,
        inv_mul_cancel]
      exact one_mem _
    · have h := nCoreCommutatorInRoot_of_hyp C.hyp C.closure d hd _ (inv_mem hzMd) η
        (hLS.rootGroup_le_nCore hd hdy hη)
      rw [inv_inv] at h
      exact Subgroup.mem_sup_right (by simpa [mul_assoc] using h)
  set w : G := ((φ.symm (weylElt (GaloisField 2 e)) : ↥(rootGroup D x ⊔ rootGroup D y)) : G)
    with hw
  have hwX : w ∈ rootGroup D x ⊔ rootGroup D y := (φ.symm _).2
  have hwy : ∀ η ∈ rootGroup D y, w⁻¹ * η * w ∈ rootGroup D x := by
    intro η hη
    have hηX : η ∈ rootGroup D x ⊔ rootGroup D y := Subgroup.mem_sup_right hη
    obtain ⟨t, ht⟩ := (mem_lowerUnipotent_iff _).1
      ((ARS.NaturalModule.coe_mem_iff hφy ⟨η, hηX⟩).1 hη)
    have e1 : w⁻¹ * η * w = (((φ.symm (weylElt _))⁻¹ * ⟨η, hηX⟩ * φ.symm (weylElt _) :
        ↥(rootGroup D x ⊔ rootGroup D y)) : G) := rfl
    rw [e1, ARS.NaturalModule.coe_mem_iff hφx, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
      ht]
    have hw1 : (weylElt (GaloisField 2 e))⁻¹ = weylElt (GaloisField 2 e) :=
      inv_eq_of_mul_eq_one_right (weylElt_mul_self (K := GaloisField 2 e))
    have e2 : (weylElt (GaloisField 2 e))⁻¹ * lowerElt (GaloisField 2 e) t *
        weylElt (GaloisField 2 e) = upperElt (GaloisField 2 e) t := by
      rw [hw1, ← weylElt_mul_upperElt_mul_weylElt, ← mul_assoc, ← mul_assoc,
        weylElt_mul_self, one_mul, mul_assoc, weylElt_mul_self, mul_one]
    rw [e2]
    exact (mem_upperUnipotent_iff _).2 ⟨t, rfl⟩
  obtain ⟨α, hα, δ, hδ, hαδ⟩ := exists_mul_eq_of_mem_line hd had (hXS hwX).2
  refine ⟨α, hα, mem_nCenter.2 ⟨mul_mem hzMd (hTd (Subgroup.mem_sup_left hα)), ?_⟩⟩
  have hzαZ : z * α ∈ nCenter D a := mul_mem hz (rootGroup_le_nCenter C ha hd had hα)
  have hwz : w * z * w⁻¹ = z * α * δ := by
    rw [mul_assoc z, ← hαδ, mul_inv_cancel_left]
  have hAy : ∀ η ∈ rootGroup D y, Commute (z * α) η := by
    intro η hη
    have h1 : Commute z (w⁻¹ * η * w) :=
      hzZ.2 _ (hLS.rootGroup_le_nCore ha hax (hwy η hη))
    have h2 := h1.map (MulAut.conj w)
    simp only [MulAut.conj_apply] at h2
    have e3 : w * (w⁻¹ * η * w) * w⁻¹ = η := by group
    rw [e3, hwz] at h2
    have hδη : Commute δ η :=
      (commute_of_mem_nCore_of_mem_rootGroup (hLS.rootGroup_le_nCore hd hdy hη) hδ).symm
    have := h2.mul_left hδη.inv_left
    rwa [mul_inv_cancel_right] at this
  have hU : ∀ u ∈ nCore D d ⊓ Subgroup.centralizer {a}, Commute (z * α) u := by
    intro u hu
    have hc1 : z * α * u * (z * α)⁻¹ * u⁻¹ ∈ rootGroup D d :=
      nCoreCommutatorInRoot_of_hyp C.hyp C.closure d hd _
        (mul_mem hzMd (hTd (Subgroup.mem_sup_left hα))) u hu.1
    have hc2 : z * α * u * (z * α)⁻¹ * u⁻¹ ∈ nCenter D a := by
      have h := conj_mem_nCenter_of_mem_lineGroup C
        (nCore_inf_le_lineGroup hu) (inv_mem hzαZ)
      have e : z * α * u * (z * α)⁻¹ * u⁻¹ = (z * α) * (u * (z * α)⁻¹ * u⁻¹) := by group
      rw [e]
      exact mul_mem hzαZ h
    have hxM : x ∈ nCore D a := hLS.rootGroup_le_nCore ha hax
      (rootSet_subset_rootGroup D x (mem_rootSet_self hx))
    have hcx : Commute (z * α * u * (z * α)⁻¹ * u⁻¹) x := (mem_nCenter.1 hc2).2 x hxM
    have hc3 := mem_rootGroup_of_mem_line_of_commute C ha hd had hdT hx hax haxD hxT
      (Subgroup.mem_sup_right hc1) hcx
    have hc4 : z * α * u * (z * α)⁻¹ * u⁻¹ = 1 := by
      by_contra hne
      have h1 := (mem_rootGroup_iff_of_rootClosure C.hyp.root C.closure hd).1 hc1
      have h2 := (mem_rootGroup_iff_of_rootClosure C.hyp.root C.closure ha).1 hc3
      rcases h1 with h1 | h1
      · exact hne h1
      rcases h2 with h2 | h2
      · exact hne h2
      have e1 := rootSet_eq_of_mem h1
      have e2 := rootSet_eq_of_mem h2
      exact hdT (by rw [← e2, e1]; exact mem_rootSet_self hd)
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc4
    exact hc4
  intro m hm
  rw [hLS.nCore_eq_rootGroup_sup hd ha had.symm hdaD haT hy hdy hdyD hyT'] at hm
  have hle : rootGroup D y ⊔ (nCore D d ⊓ Subgroup.centralizer {a}) ≤
      Subgroup.centralizer {z * α} :=
    sup_le (fun η hη => Subgroup.mem_centralizer_singleton_iff.2 (hAy η hη).symm.eq)
      (fun u hu => Subgroup.mem_centralizer_singleton_iff.2 (hU u hu).symm.eq)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hm)).symm

end Weyl

section Transport

variable {q : ℕ} (K : ThinGateCount G D q 2 2)

omit [Finite G] in
theorem exists_mem_rootLines_ne₃ {p : G} {L₁ L₂ L₃ : Subgroup G}
    (h4 : 4 ≤ (rootLines D p).ncard) : ∃ L ∈ rootLines D p, L ≠ L₁ ∧ L ≠ L₂ ∧ L ≠ L₃ := by
  by_contra hno
  push Not at hno
  have hsub : rootLines D p ⊆ {L₁, L₂, L₃} := fun L hL => by
    by_cases h1 : L = L₁
    · exact Or.inl h1
    by_cases h2 : L = L₂
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hno L hL h1 h2))
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({L₁, L₂, L₃} : Set (Subgroup G)).ncard ≤ 3 :=
    (Set.ncard_insert_le L₁ {L₂, L₃}).trans (by
      have := Set.ncard_insert_le L₂ {L₃}
      rw [Set.ncard_singleton] at this
      omega)
  omega

omit [Finite G] in
theorem conj_mem_nCenter_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {e z : G}
    (hz : z ∈ nCenter D e) (g : G) : g * z * g⁻¹ ∈ nCenter D (g * e * g⁻¹) := by
  rw [mem_nCenter] at hz ⊢
  refine ⟨conj_mem_nCore_conj hclass hz.1 g, fun m hm => ?_⟩
  have hm' := conj_mem_nCore_conj hclass hm g⁻¹
  rw [show g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e by group] at hm'
  have h := (hz.2 _ hm').map (MulAut.conj g)
  simp only [MulAut.conj_apply] at h
  convert h using 1
  group

include C in
theorem card_nCore_eq_of_mem {p : G} (hp : p ∈ D) (ha : a ∈ D) :
    Nat.card (nCore D p) = Nat.card (nCore D a) := by
  have hclass := C.hyp.isClass
  have key : ∀ {u v : G}, u ∈ D → v ∈ D → Nat.card (nCore D u) ≤ Nat.card (nCore D v) := by
    intro u v hu hv
    obtain ⟨g, hg⟩ := isConj_iff.1 (C.hyp.isConj hu hv)
    let φ : ↥(nCore D u) → ↥(nCore D v) := fun m =>
      ⟨g * m * g⁻¹, hg ▸ conj_mem_nCore_conj hclass m.2 g⟩
    have hφ : Function.Injective φ := fun m m' h => by
      have h' : g * (m : G) * g⁻¹ = g * m' * g⁻¹ := congrArg Subtype.val h
      exact Subtype.ext (by simpa using h')
    exact Nat.card_le_card_of_injective φ hφ
  exact le_antisymm (key hp ha) (key ha hp)

include C K in
theorem mem_nCenter_of_collinear {p e w z : G} (hp : p ∈ D) (he : e ∈ D) (hpe : Commute p e)
    (hpeD : p * e ∈ D) (heT : e ∉ rootSet D p) (hw : w ∈ D) (hpw : Commute p w)
    (hpwD : p * w ∈ D) (hwT : w ∉ rootSet D p) (hM : Nat.card (nCore D p) < q ^ 6)
    (hzp : z ∈ nCenter D p) (hze : z ∈ nCenter D e) : z ∈ nCenter D w := by
  classical
  have hLS := lineSetting_of_counter C
  have hclass := C.hyp.isClass
  have hq := two_le_q C K hp
  have hlines := K.ncard_rootLines p hp
  have h3 : 3 ≤ (rootLines D p).ncard := three_le_ncard_rootLines C K hp
  have h4 : 4 ≤ (rootLines D p).ncard := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have hLe : rootGroup D p ⊔ rootGroup D e ∈ rootLines D p := ⟨e, he, hpe, hpeD, heT, rfl⟩
  have hLw : rootGroup D p ⊔ rootGroup D w ∈ rootLines D p := ⟨w, hw, hpw, hpwD, hwT, rfl⟩
  obtain ⟨r, hr, hodd, hrL⟩ : ∃ r ∈ lineGroup D p e, Odd (orderOf r) ∧
      (rootGroup D p ⊔ rootGroup D e).map (MulAut.conj r).toMonoidHom =
        rootGroup D p ⊔ rootGroup D w := by
    by_cases hLL : rootGroup D p ⊔ rootGroup D e = rootGroup D p ⊔ rootGroup D w
    · refine ⟨1, one_mem _, by simp, ?_⟩
      rw [← hLL]
      ext g
      simp
    · obtain ⟨L₁, hL₁, h1e, h1w⟩ := exists_mem_rootLines_ne_ne
        (L₁ := rootGroup D p ⊔ rootGroup D e) (L₂ := rootGroup D p ⊔ rootGroup D w) h3
      obtain ⟨L₂, hL₂, h2e, h2w, h21⟩ := exists_mem_rootLines_ne₃
        (L₁ := rootGroup D p ⊔ rootGroup D e) (L₂ := rootGroup D p ⊔ rootGroup D w) (L₃ := L₁) h4
      obtain ⟨h, hh, hord, -, -, htrans⟩ := rootLinesTorusStep G D hLS p hp e he hpe hpeD heT h3
        L₁ hL₁ L₂ hL₂ (Ne.symm h21)
      obtain ⟨i, -, hi⟩ := htrans _ hLe _ hLw (Ne.symm h1e) (Ne.symm h2e) (Ne.symm h1w)
        (Ne.symm h2w)
      refine ⟨h ^ i, pow_mem hh i, ?_, hi⟩
      obtain ⟨m, hm, hqm, -⟩ := exists_l2 C K hp he hpe hpeD heT
      have hoh : Odd (orderOf h) := by
        have e1 : orderOf h = 2 ^ m - 1 := by omega
        rw [e1]
        have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        exact Nat.Even.sub_odd this (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
      exact Odd.of_dvd_nat hoh (orderOf_pow_dvd i)
  have hrz : Commute r z := commute_of_odd C K hp he hpe hpeD heT hM hzp hr hodd
  have he'L : r * e * r⁻¹ ∈ rootGroup D p ⊔ rootGroup D w := by
    rw [← hrL]
    exact ⟨e, right_mem_line he, rfl⟩
  have he'p : r * e * r⁻¹ ∉ rootGroup D p := by
    intro h'
    have hrN := hLS.lineGroup_le_normalizer (a := p) e hr
    have h'' := (Subgroup.mem_normalizer_iff.1 (inv_mem hrN) _).1 h'
    rw [show r⁻¹ * (r * e * r⁻¹) * r⁻¹⁻¹ = e by group] at h''
    exact not_mem_rootGroup C hp he heT h''
  obtain ⟨b, hb, hpb, hpbD, hbL⟩ := exists_point C hp hw hpw hpwD hwT
  obtain ⟨m, hm, hme⟩ := hLS.exists_conj_mem_rootSet hp hw hpw hpwD hwT hb hpb hpbD hbL
    (right_mem_line hw) (not_mem_rootGroup C hp hw hwT) he'L he'p
  have hmz : Commute m z := by
    rcases hm with rfl | hm
    · exact Commute.one_left z
    · exact ((mem_nCenter.1 hzp).2 m
        (hLS.rootGroup_le_nCore hp hpb (rootSet_subset_rootGroup D b hm))).symm
  have h1 := conj_mem_nCenter_conj hclass hze (m * r)
  have e1 : m * r * z * (m * r)⁻¹ = z := by
    have : m * r * z = z * (m * r) := by
      rw [mul_assoc, hrz.eq, ← mul_assoc, hmz.eq, mul_assoc]
    rw [this, mul_inv_cancel_right]
  have e2 : m * r * e * (m * r)⁻¹ = m * (r * e * r⁻¹) * m⁻¹ := by group
  rw [e1, e2] at h1
  have e3 : nCenter D (m * (r * e * r⁻¹) * m⁻¹) = nCenter D w := by
    unfold nCenter
    rw [hLS.nCore_eq_of_mem_rootSet hw hme]
  rwa [e3] at h1

end Transport

end RootMany

open RootMany in
theorem thinGateCenterStep : ThinGateCenterStep := by
  intro G _ D q C K a ha d hd had hadD hdT hN z hzM hzc
  have := C.hyp.finite
  have hD := C.hyp.root
  have hLS := lineSetting_of_counter C
  have hq := two_le_q C K ha
  have hM : Nat.card (nCore D a) < q ^ 6 := by
    rw [card_nCore_eq C K ha hd had hadD hdT]
    have : 0 < q ^ 3 := by positivity
    calc q ^ 3 * Nat.card ↥(nCore D a ⊓ nCore D d) < q ^ 3 * q ^ 3 :=
          Nat.mul_lt_mul_of_pos_left hN this
      _ = q ^ 6 := by ring
  have hMp : ∀ p ∈ D, Nat.card (nCore D p) < q ^ 6 := fun p hp =>
    (card_nCore_eq_of_mem C hp ha) ▸ hM
  have hz : z ∈ nCenter D a := mem_nCenter.2 ⟨hzM, hzc⟩
  by_contra hzA
  obtain ⟨α, hα, hzα⟩ := exists_mul_mem_nCenter C ha hd had hadD hdT K hM hz
  have hz₀a : z * α ∈ nCenter D a := mul_mem hz (rootGroup_le_nCenter C ha hd had hα)
  have hz₀1 : z * α ≠ 1 := fun h => hzA (by
    rw [eq_inv_of_mul_eq_one_left h]
    exact inv_mem hα)
  obtain ⟨B, hB⟩ : (oneOmega D a).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h := K.ncard_oneOmega a ha
    rw [hne, Set.ncard_empty, zero_mul] at h
    have : 0 < (q ^ 2 + 1) * q ^ (2 * 2 + 3) := by positivity
    omega
  obtain ⟨x, hx, -, hax, hodd, e, he, hae, haeD, h4⟩ := hB
  have h4' : orderOf (e * x) = 4 := by rw [orderOf_mul_comm_eq]; exact h4
  have heT : e ∉ rootSet D a := fun h => by
    have h' := (orderOf_mul_eq_four_iff_of_mem_rootSet hD ha h hx).1 h4'
    rw [h'] at hodd
    exact absurd hodd (by decide)
  have hze : z * α ∈ nCenter D e :=
    mem_nCenter_of_collinear C K ha hd had hadD hdT he hae haeD heT (hMp a ha) hz₀a hzα
  obtain ⟨hwD, hew, hxw, hxex⟩ := sq_mem_of_orderOf_eq_four hD he hx h4'
  have hewD : e * (e * x) ^ 2 ∈ D := by
    rw [← hxex]
    have := C.hyp.conj_mem x he
    rwa [hD.inv_eq hx] at this
  have hwT : (e * x) ^ 2 ∉ rootSet D e := fun h => by
    have hex : Commute e x := ((h.2 x hx).1 hxw.symm)
    have := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one he)
      (hD.mul_self_eq_one hx)).1 hex)
    rw [h4'] at this
    exact absurd this (by decide)
  have haT : a ∉ rootSet D e := fun h => heT (mem_rootSet_comm he h)
  have heaD : e * a ∈ D := by rw [← hae.eq]; exact haeD
  have hzw : z * α ∈ nCenter D ((e * x) ^ 2) :=
    mem_nCenter_of_collinear C K he ha hae.symm heaD haT hwD hew hewD hwT (hMp e he) hze hz₀a
  have hxM : x ∈ nCore D ((e * x) ^ 2) := hLS.mem_nCore_of_commute hwD hx hxw.symm
  have hz₀x : Commute (z * α) x := (mem_nCenter.1 hzw).2 x hxM
  have htop := Bridge.RootClosure.closure_insert_centralizer_eq_top C.hyp C.conn ha hx hax hodd
  have hle : Subgroup.closure (insert x {f | f ∈ D ∧ Commute a f}) ≤
      Subgroup.centralizer {z * α} := by
    rw [Subgroup.closure_le]
    rintro f (rfl | ⟨hf, haf⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hz₀x.symm.eq
    · exact Subgroup.mem_centralizer_singleton_iff.2
        ((mem_nCenter.1 hz₀a).2 f (hLS.mem_nCore_of_commute ha hf haf)).symm.eq
  have hcen : z * α ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer {z * α} := hle (htop ▸ Subgroup.mem_top g)
    exact Subgroup.mem_centralizer_singleton_iff.1 hg
  rw [C.hyp.center_eq_bot, Subgroup.mem_bot] at hcen
  exact hz₀1 hcen

end CFSG.Timmesfeld.Bridge
