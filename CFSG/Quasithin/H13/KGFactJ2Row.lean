module

public import CFSG.Quasithin.H13.A5Facts1321
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Main
public import CFSG.Quasithin.Background.JonesParshallG2Derived
public import CFSG.Quasithin.Background.B3Sec

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Quasithin CFSG.Blueprint
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.J2Excl
  CFSG.QuasithinUnique.Setup.Family CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open scoped commutatorElement

namespace KGJ2

theorem carrier_j2_not_comm :
    ¬ ∀ a b : NativeSporadic.Carrier .J2, a * b = b * a := by
  intro hc
  have hs : IsSimpleGroup (NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.fam_j2_simplicity.2.2
  have hf : Finite (NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.fam_j2_simplicity.1
  let _ : CommGroup (NativeSporadic.Carrier .J2) :=
    { (inferInstance : Group (NativeSporadic.Carrier .J2)) with mul_comm := hc }
  have hp := IsSimpleGroup.prime_card (α := NativeSporadic.Carrier .J2)
  have hcard : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  rw [hcard] at hp
  norm_num at hp

theorem isPerfect_carrier_j2 :
    Group.IsPerfect (NativeSporadic.Carrier .J2) := by
  have hs : IsSimpleGroup (NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.fam_j2_simplicity.2.2
  rw [Group.isPerfect_def]
  rcases hs.eq_bot_or_eq_top_of_normal (commutator (NativeSporadic.Carrier .J2)) with h | h
  · exfalso
    apply carrier_j2_not_comm
    intro a b
    have h1 : ⁅a, b⁆ ∈ commutator (NativeSporadic.Carrier .J2) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · exact h

theorem center_carrier_j2 :
    Subgroup.center (NativeSporadic.Carrier .J2) = ⊥ := by
  have hs : IsSimpleGroup (NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.fam_j2_simplicity.2.2
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (NativeSporadic.Carrier .J2)) with h | h
  · exact h
  · exfalso
    apply carrier_j2_not_comm
    intro a b
    have ha : a ∈ Subgroup.center (NativeSporadic.Carrier .J2) := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem j2_gen4_aut
    (b : MulAut (NativeSporadic.Carrier .J2)) (hb2 : b * b = 1) (hb1 : b ≠ 1) :
    ∃ cs : List (MulAut (NativeSporadic.Carrier .J2)), cs.length = 4 ∧
      (∀ c ∈ cs, c ∈ (MulAut.conj : NativeSporadic.Carrier .J2 →*
        MulAut (NativeSporadic.Carrier .J2)).range) ∧
      ∀ s : NativeSporadic.Carrier .J2,
        MulAut.conj s ∈ Subgroup.closure {y | ∃ c ∈ cs, y = c * b * c⁻¹} := by
  obtain ⟨Φ, hΦ⟩ := j2_aut_model
  set x : ↥j2R := Φ.symm b with hx
  have hxb : Φ x = b := by rw [hx, MulEquiv.apply_symm_apply]
  have hx2 : (x : Equiv.Perm (Fin 315)) ^ 2 = 1 := by
    have : x * x = 1 := Φ.injective (by rw [map_mul, hxb, hb2, map_one])
    rw [sq]
    exact congrArg Subtype.val this
  have hx1 : (x : Equiv.Perm (Fin 315)) ≠ 1 := by
    intro h
    apply hb1
    have : x = 1 := Subtype.ext h
    rw [← hxb, this, map_one]
  obtain ⟨gs, hlen, hgsP, hle⟩ := j2_gen4 x.2 hx2 hx1
  let cs : List (MulAut (NativeSporadic.Carrier .J2)) :=
    gs.attach.map fun g => Φ ⟨g.1, j2P_le_R (hgsP g.1 g.2)⟩
  have hΦA : ∀ (g : Equiv.Perm (Fin 315)) (hg : g ∈ j2P),
      Φ ⟨g, j2P_le_R hg⟩ = MulAut.conj (j2EquivC.symm ⟨g, hg⟩) := by
    intro g hg
    rw [← hΦ]
    congr 1
    apply Subtype.ext
    simp
  refine ⟨cs, by simp [cs, hlen], ?_, ?_⟩
  · intro c hc
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨j2EquivC.symm ⟨g.1, hgsP g.1 g.2⟩, (hΦA g.1 (hgsP g.1 g.2)).symm⟩
  · intro s
    set K' : Subgroup (MulAut (NativeSporadic.Carrier .J2)) :=
      Subgroup.closure {y | ∃ c ∈ cs, y = c * b * c⁻¹} with hK'
    set Kp : Subgroup (Equiv.Perm (Fin 315)) := (K'.comap Φ.toMonoidHom).map j2R.subtype
      with hKp
    have hsub : conjSet gs {(x : Equiv.Perm (Fin 315))} ⊆ (Kp : Set (Equiv.Perm (Fin 315))) := by
      rintro _ ⟨c, hc, t, ht, rfl⟩
      rw [Set.mem_singleton_iff] at ht
      subst ht
      have hcP : c ∈ j2P := hgsP c hc
      refine ⟨⟨c, j2P_le_R hcP⟩ * x * ⟨c, j2P_le_R hcP⟩⁻¹, ?_, rfl⟩
      show Φ (⟨c, j2P_le_R hcP⟩ * x * ⟨c, j2P_le_R hcP⟩⁻¹) ∈ K'
      rw [map_mul, map_mul, map_inv, hxb]
      exact Subgroup.subset_closure ⟨Φ ⟨c, j2P_le_R hcP⟩,
        List.mem_map.2 ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩, rfl⟩
    have hPKp : j2P ≤ Kp := hle.trans ((Subgroup.closure_le Kp).2 hsub)
    obtain ⟨y, hy, hyθ⟩ := hPKp (j2EquivC s).2
    have hy' : y = ⟨(j2EquivC s : Equiv.Perm (Fin 315)), j2P_le_R (j2EquivC s).2⟩ :=
      Subtype.ext hyθ
    rw [← hΦ s, ← hy']
    exact hy

section Module

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem j2Twelve_facts {L : Subgroup (MulAut V)} (h : J2Twelve L ⊤ ⊥) :
    (∀ v : V, v * v = 1) ∧ Nat.card V = 2 ^ 12 := by
  obtain ⟨K, _, _, Γ₀, hK, -, π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ 2 :=
    (Nat.card_eq_fintype_card (α := K)).symm.trans (hK.trans (by norm_num))
  have : CharP K 2 := charP_of_card_eq_prime_pow hKf
  set ε := JonesParshall.zornSecEquiv (F := K) Γ₀ with hε
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  refine ⟨fun w => ?_, ?_⟩
  · have hsq : ∀ q : (FFModel.zornQ Γ₀).Sec, q * q = 1 := by
      intro q
      apply ε.injective
      rw [map_mul, map_one]
      show Multiplicative.ofAdd (Multiplicative.toAdd (ε q) + Multiplicative.toAdd (ε q)) = 1
      have h0 : Multiplicative.toAdd (ε q) + Multiplicative.toAdd (ε q) = 0 := by
        funext i
        exact CharTwo.add_self_eq_zero _
      rw [h0]
      rfl
    have h1 : β ⟨w * w, Subgroup.mem_top _⟩ = 1 := by
      have e : (⟨w * w, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) =
          ⟨w, Subgroup.mem_top _⟩ * ⟨w, Subgroup.mem_top _⟩ := rfl
      rw [e, map_mul, hsq]
    have h2 := hβinj (h1.trans (map_one β).symm)
    exact congrArg Subtype.val h2
  · have e1 : Nat.card ↥(⊤ : Subgroup V) = Nat.card (FFModel.zornQ Γ₀).Sec :=
      Nat.card_congr (Equiv.ofBijective β ⟨hβinj, hβs⟩)
    rw [Subgroup.card_top, Nat.card_congr ε.toEquiv] at e1
    rw [e1]
    show Nat.card (JonesParshall.Ix3 → K) = 2 ^ 12
    rw [Nat.card_fun, hK, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
    norm_num

omit [Finite V] in
theorem sec_sq (hV : ∀ v : V, v * v = 1) {W N : Subgroup V} (q : B3.Sec W N) : q * q = 1 := by
  induction q using QuotientGroup.induction_on with
  | H w =>
    rw [← QuotientGroup.mk_mul]
    have : w * w = 1 := Subtype.ext (hV w)
    rw [this, QuotientGroup.mk_one]

theorem isIrrOn_of_card_j2
    (hV : ∀ v : V, v * v = 1) (hcard : Nat.card V = 2 ^ 12) {L : Subgroup (MulAut V)}
    (eL : ↥L ≃* NativeSporadic.Carrier .J2) : IsIrrOn L := by
  have hs : IsSimpleGroup (NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.fam_j2_simplicity.2.2
  refine ⟨Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num), fun U hU => ?_⟩
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hU0, hU1⟩ := hne
  let ρ : ↥L →* MulAut V := L.subtype
  have hUinv : B3.IsInv ρ U := fun g u hu => hU g g.2 u hu
  have hbot : B3.IsInv ρ ⊥ := fun g w hw => by
    rw [Subgroup.mem_bot] at hw ⊢
    rw [hw, map_one]
  have htop : B3.IsInv ρ ⊤ := fun _ _ _ => Subgroup.mem_top _
  have triv : ∀ {W N : Subgroup V} (hW : B3.IsInv ρ W) (hN : B3.IsInv ρ N),
      Nat.card (B3.Sec W N) < 2 ^ 12 → ∀ l : ↥L, B3.secAct ρ hW hN l = 1 := by
    intro W N hW hN hlt l
    set σ : NativeSporadic.Carrier .J2 →* MulAut (B3.Sec W N) :=
      (B3.secAct ρ hW hN).comp eL.symm.toMonoidHom with hσ
    rcases hs.eq_bot_or_eq_top_of_normal σ.ker with h | h
    · exfalso
      have hinj : Function.Injective σ := (MonoidHom.ker_eq_bot_iff σ).1 h
      have := j2_dim (B3.Sec W N) (sec_sq hV) σ hinj
      omega
    · have hl : eL l ∈ σ.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hl
      simpa [σ] using hl
  have hUlt : Nat.card U < 2 ^ 12 := by
    rw [← hcard]
    refine lt_of_le_of_ne (Subgroup.card_le_card_group U) fun h => hU1 ?_
    exact Subgroup.eq_top_of_card_eq U h
  have hUgt : 1 < Nat.card U := (Subgroup.one_lt_card_iff_ne_bot U).2 hU0
  have hcU : Nat.card (B3.Sec U ⊥) < 2 ^ 12 := by
    show ((⊥ : Subgroup V).subgroupOf U).index < 2 ^ 12
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot]
    exact hUlt
  have hcQ : Nat.card (B3.Sec ⊤ U) < 2 ^ 12 := by
    show (U.subgroupOf ⊤).index < 2 ^ 12
    rw [show (U.subgroupOf ⊤).index = U.relIndex ⊤ from rfl, Subgroup.relIndex_top_right]
    have h1 := Subgroup.card_mul_index U
    rw [hcard] at h1
    by_contra hge
    rw [not_lt] at hge
    have h2 : 2 * 2 ^ 12 ≤ Nat.card U * U.index := Nat.mul_le_mul hUgt hge
    omega
  have hfix := triv hUinv hbot hcU
  have hquot := triv htop hUinv hcQ
  have fixU : ∀ l : ↥L, ∀ u ∈ U, (l : MulAut V) u = u := by
    intro l u hu
    have h1 := congrArg (fun f : MulAut (B3.Sec U ⊥) => f (QuotientGroup.mk ⟨u, hu⟩)) (hfix l)
    simp only [MulAut.one_apply] at h1
    have h2 : (QuotientGroup.mk ⟨(l : MulAut V) u, hU l l.2 u hu⟩ : B3.Sec U ⊥) =
        QuotientGroup.mk ⟨u, hu⟩ := h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h2
    have h3 : ((l : MulAut V) u)⁻¹ * u = 1 := h2
    rw [inv_mul_eq_one] at h3
    exact h3
  have quotU : ∀ l : ↥L, ∀ x : V, x⁻¹ * (l : MulAut V) x ∈ U := by
    intro l x
    have h1 := congrArg (fun f : MulAut (B3.Sec ⊤ U) =>
      f (QuotientGroup.mk ⟨x, Subgroup.mem_top x⟩)) (hquot l)
    simp only [MulAut.one_apply] at h1
    have h2 : (QuotientGroup.mk ⟨(l : MulAut V) x, Subgroup.mem_top _⟩ : B3.Sec ⊤ U) =
        QuotientGroup.mk ⟨x, Subgroup.mem_top x⟩ := h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
    have h3 : ((l : MulAut V) x)⁻¹ * x ∈ U := h2
    have h4 := U.inv_mem h3
    rwa [mul_inv_rev, inv_inv] at h4
  apply carrier_j2_not_comm
  intro a b
  apply eL.symm.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  set l := eL.symm a
  set m := eL.symm b
  show (l : MulAut V) ((m : MulAut V) x) = (m : MulAut V) ((l : MulAut V) x)
  have e1 : (l : MulAut V) ((m : MulAut V) x) =
      (l : MulAut V) x * (x⁻¹ * (m : MulAut V) x) := by
    conv_lhs => rw [show (m : MulAut V) x = x * (x⁻¹ * (m : MulAut V) x) by
      rw [mul_inv_cancel_left]]
    rw [map_mul, fixU l _ (quotU m x)]
  have e2 : (m : MulAut V) ((l : MulAut V) x) =
      (m : MulAut V) x * (x⁻¹ * (l : MulAut V) x) := by
    conv_lhs => rw [show (l : MulAut V) x = x * (x⁻¹ * (l : MulAut V) x) by
      rw [mul_inv_cancel_left]]
    rw [map_mul, fixU m _ (quotU l x)]
  rw [e1, e2, mul_left_comm, mul_left_comm ((m : MulAut V) x), mul_comm ((l : MulAut V) x)]

end Module

end KGJ2

open KGJ2 in
theorem factJ2Row1321_holds :
    FactJ2Row1321 := by
  intro V _ _ G L _hLG hGN hsp hJ v hvG hv2
  obtain ⟨eL⟩ := hsp
  obtain ⟨hV, hcard⟩ := j2Twelve_facts hJ
  have hirr : IsIrrOn L := isIrrOn_of_card_j2 hV hcard eL
  have : Group.IsPerfect (NativeSporadic.Carrier .J2) := isPerfect_carrier_j2
  have hperf : Group.IsPerfect ↥L := Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom)
    eL.symm.surjective
  have hcent : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : eL x ∈ Subgroup.center (NativeSporadic.Carrier .J2) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := eL.surjective y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx z)]
    rw [center_carrier_j2, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact eL.injective (hx'.trans (map_one eL).symm)
  let e : CQ L ≃* NativeSporadic.Carrier .J2 :=
    (QuotientGroup.quotientMulEquivOfEq hcent).trans (QuotientGroup.quotientBot.trans eL)
  have hL : L ≠ ⊥ := by
    intro h
    apply carrier_j2_not_comm
    intro a b
    have hall : ∀ y : ↥L, y = 1 := by
      rintro ⟨y, hy⟩
      apply Subtype.ext
      show y = 1
      rw [h, Subgroup.mem_bot] at hy
      exact hy
    apply eL.symm.injective
    rw [hall (eL.symm (a * b)), hall (eL.symm (b * a))]
  set E := Subgroup.zpowers v with hEdef
  have hv1 : v ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hv2
    exact absurd hv2 (by norm_num)
  have hvsq : v * v = 1 := by rw [← sq, ← hv2, pow_orderOf_eq_one]
  have hE : E ≤ Subgroup.normalizer (L : Set (MulAut V)) := (Subgroup.zpowers_le).2 (hGN hvG)
  have hEel : IsElemAbelian2 E := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hvsq, one_zpow]
  have hvLE : v ∈ L ⊔ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  set b := actS hE e ⟨v, hvLE⟩ with hb
  have hinj := actS_injective_of_center hV hperf hirr hE hEel e hcent
  have hb2 : b * b = 1 := by
    rw [hb, ← map_mul]
    have : (⟨v, hvLE⟩ : ↥(L ⊔ E)) * ⟨v, hvLE⟩ = 1 := Subtype.ext hvsq
    rw [this, map_one]
  have hb1 : b ≠ 1 := by
    intro h
    apply hv1
    have : (⟨v, hvLE⟩ : ↥(L ⊔ E)) = 1 := hinj (h.trans (map_one _).symm)
    exact congrArg Subtype.val this
  obtain ⟨cs, hlen, hcsInn, hcsgen⟩ := j2_gen4_aut b hb2 hb1
  have hcs : ∀ c ∈ cs, c ∈ (actS hE e).range := by
    intro c hc
    obtain ⟨s, rfl⟩ := hcsInn c hc
    exact conj_mem_range_actS hE e s
  have hgen : ∀ s : NativeSporadic.Carrier .J2, MulAut.conj s ∈ Subgroup.closure
      {y : MulAut (NativeSporadic.Carrier .J2) | ∃ c ∈ cs, ∃ b' : ↥(L ⊔ E),
        (b' : MulAut V) ∈ E ∧ y = c * actS hE e b' * c⁻¹} := by
    intro s
    refine Subgroup.closure_mono ?_ (hcsgen s)
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, hc, ⟨v, hvLE⟩, Subgroup.mem_zpowers v, rfl⟩
  have hbound := card_le_index_pow_of_inn_le hV hperf hirr hL hE hEel e cs hcs hgen
  rw [hlen, hcard] at hbound
  have hdvd : (fixV E).index ∣ 2 ^ 12 := hcard ▸ Subgroup.index_dvd_card (fixV E)
  obtain ⟨m, -, hidx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  show 3 ≤ padicValNat 2 (fixV E).index
  rw [hidx, padicValNat.prime_pow]
  by_contra hlt
  rw [not_le] at hlt
  rw [hidx] at hbound
  have h1 : (2 ^ m) ^ 4 ≤ (2 ^ 2) ^ 4 :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (by omega)) 4
  exact absurd (hbound.trans h1) (by norm_num)

end CFSG.Quasithin.H13.A5
