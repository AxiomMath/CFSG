module

public import CFSG.LocalAnalysis.StandardType.GGInnLocal
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryLift

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGBstarBoundInnR (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ Eb Eh : Subgroup (MulAut R), (Eb : Set (MulAut R)) ⊆ I → IsElemAbelian p Eb →
    p ^ r ≤ Nat.card Eb → p ^ 3 ≤ Nat.card Eb →
    (∃ V : Subgroup R, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ φ ∈ Eb, ∀ v ∈ V, φ v ∈ V) →
    Eb ≤ Eh → IsElemAbelian p Eh → p ^ 2 * Nat.card Eb ≤ Nat.card Eh →
    ∃ E' : Subgroup (MulAut R), Eb < E' ∧ E' ≤ Eh ∧
      ∃ V : Subgroup R, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ φ ∈ E', ∀ v ∈ V, φ v ∈ V

namespace BstarDesc

variable {L R : Type} [Group L] [Group R]

theorem mulAut_mem_center (a : MulAut L) {z : L} (hz : z ∈ Subgroup.center L) :
    a z ∈ Subgroup.center L := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g', rfl⟩ := a.surjective g
  rw [← map_mul, ← map_mul, hz g']

theorem ker_eq_center {ψ : L →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hR : Subgroup.center R = ⊥) :
    ψ.ker = Subgroup.center L := by
  refine le_antisymm hker fun z hz => ?_
  have hψz : ψ z ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
  rw [hR, Subgroup.mem_bot] at hψz
  exact hψz

variable {ψ : L →* R} (hψ : Function.Surjective ψ) (hZ : ψ.ker = Subgroup.center L)

include hZ in
theorem map_eq_of_map_eq (a : MulAut L) {l l' : L} (h : ψ l = ψ l') : ψ (a l) = ψ (a l') := by
  have h1 : l⁻¹ * l' ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [hZ] at h1
  have h2 := mulAut_mem_center a h1
  rw [← hZ, MonoidHom.mem_ker] at h2
  simp only [map_mul, map_inv] at h2
  exact inv_mul_eq_one.mp h2

@[expose] noncomputable def descFun (a : MulAut L) : R → R :=
  fun r => ψ (a (Function.surjInv hψ r))

include hZ in
theorem descFun_apply (a : MulAut L) (l : L) : descFun hψ a (ψ l) = ψ (a l) :=
  map_eq_of_map_eq hZ a (Function.surjInv_eq hψ (ψ l))

@[expose] noncomputable def descAut : MulAut L →* MulAut R where
  toFun a :=
    { toFun := descFun hψ a
      invFun := descFun hψ a⁻¹
      left_inv := fun r => by
        obtain ⟨l, rfl⟩ := hψ r
        rw [descFun_apply hψ hZ, descFun_apply hψ hZ, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      right_inv := fun r => by
        obtain ⟨l, rfl⟩ := hψ r
        rw [descFun_apply hψ hZ, descFun_apply hψ hZ, MulAut.inv_apply, MulEquiv.apply_symm_apply]
      map_mul' := fun r s => by
        obtain ⟨l, rfl⟩ := hψ r
        obtain ⟨m, rfl⟩ := hψ s
        rw [← map_mul, descFun_apply hψ hZ, descFun_apply hψ hZ, descFun_apply hψ hZ, map_mul,
          map_mul] }
  map_one' := MulEquiv.ext fun r => by
    obtain ⟨l, rfl⟩ := hψ r
    change descFun hψ 1 (ψ l) = ψ l
    rw [descFun_apply hψ hZ]
    rfl
  map_mul' a b := MulEquiv.ext fun r => by
    obtain ⟨l, rfl⟩ := hψ r
    change descFun hψ (a * b) (ψ l) = descFun hψ a (descFun hψ b (ψ l))
    rw [descFun_apply hψ hZ, descFun_apply hψ hZ, descFun_apply hψ hZ]
    rfl

theorem descAut_apply (a : MulAut L) (l : L) : descAut hψ hZ a (ψ l) = ψ (a l) :=
  descFun_apply hψ hZ a l

theorem descAut_injective (hperf : commutator L = ⊤) : Function.Injective (descAut hψ hZ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hz : ∀ l, a l * l⁻¹ ∈ Subgroup.center L := fun l => by
    rw [← hZ, MonoidHom.mem_ker, map_mul, map_inv, ← descAut_apply hψ hZ, ha, MulAut.one_apply,
      mul_inv_cancel]
  let f : L →* L :=
    { toFun := fun l => a l * l⁻¹
      map_one' := by simp
      map_mul' := fun a' b' => by
        have h' := (Subgroup.mem_center_iff.mp (hz b')) a'⁻¹
        simp only [map_mul, _root_.mul_inv_rev]
        calc a a' * a b' * (b'⁻¹ * a'⁻¹) = a a' * ((a b' * b'⁻¹) * a'⁻¹) := by group
          _ = a a' * (a'⁻¹ * (a b' * b'⁻¹)) := by rw [h']
          _ = a a' * a'⁻¹ * (a b' * b'⁻¹) := by group }
  have hfker : commutator L ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro u _ v _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hz v)) (f u)
  ext l
  have h1 : f l = 1 := hfker (by rw [hperf]; exact Subgroup.mem_top _)
  exact mul_inv_eq_one.mp h1

end BstarDesc

section TwoSub

variable {L R : Type} [Group L] [Group R] [Finite L]

theorem exists_two_subgroup_preimage {ψ : L →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) {V : Subgroup R} (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V) :
    ∃ U : Subgroup L, U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ V.comap ψ ∧
      ∀ l : L, ψ l ∈ V → (∃ k : ℕ, l ^ 2 ^ k = 1) → l ∈ U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup L := V.comap ψ with hW
  set f' : ↥W →* R := ψ.comp W.subtype with hf'
  have hfr : f'.range ≤ V := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  have hker' : f'.ker ≤ Subgroup.center ↥W := by
    intro w hw
    have hz : (w : L) ∈ Subgroup.center L := hker hw
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro v
    exact Subtype.ext (hz v)
  have hrange2 : IsPGroup 2 f'.range := hV2.to_le hfr
  have : Finite f'.range := Finite.of_surjective _ f'.rangeRestrict_surjective
  have : Group.IsNilpotent f'.range := hrange2.isNilpotent
  have : Group.IsNilpotent ↥W :=
    Subgroup.isNilpotent_of_ker_le_center f'.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact hker')
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥W))
  have hPn : (P : Subgroup ↥W).Normal := inferInstance
  have := Sylow.unique_of_normal P hPn
  refine ⟨(P : Subgroup ↥W).map W.subtype, ?_, P.isPGroup'.map _, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective]
    obtain ⟨⟨v, hvV⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1
    have hv1' : v ≠ 1 := fun h' => hv1 (Subtype.ext h')
    obtain ⟨u, rfl⟩ := hψ v
    have huW : u ∈ W := hvV
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hV2 ⟨ψ u, hvV⟩
    rw [Subgroup.orderOf_mk] at hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hv1' hj
    have hdvd : 2 ∣ Nat.card ↥W := by
      have h1 : orderOf (ψ u) ∣ orderOf (⟨u, huW⟩ : ↥W) := by
        have h2 : f' ⟨u, huW⟩ = ψ u := rfl
        rw [← h2]
        exact orderOf_map_dvd f' _
      rw [hj] at h1
      exact (dvd_pow_self 2 hj0).trans (h1.trans (orderOf_dvd_natCard _))
    exact P.ne_bot_of_dvd_card hdvd
  · rintro _ ⟨w, -, rfl⟩
    exact w.2
  · intro l hl ⟨k, hk⟩
    have hlW : l ∈ W := hl
    have hk' : (⟨l, hlW⟩ : ↥W) ^ 2 ^ k = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hk)
    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (isPGroup_zpowers_of_pow Nat.prime_two hk')
    rw [Subsingleton.elim Q P] at hQ
    exact ⟨⟨l, hlW⟩, hQ (Subgroup.mem_zpowers _), rfl⟩

end TwoSub

open BstarDesc in
theorem ggBstarBoundInn_of_R {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hR : Subgroup.center R = ⊥) (hcore : GGBstarBoundInnR p r R I) :
    GGBstarBoundInn p r R I := by
  classical
  intro L' _ _ ψ hψ hker hL A Ah hA hAI hr h3 hU hAAh hAh hcard
  have hZ : ψ.ker = Subgroup.center L' := ker_eq_center hψ hker hR
  have hp2 : 2 ≤ p := hp.two_le
  have hlt : A < Ah := by
    refine lt_of_le_of_ne hAAh fun he => ?_
    rw [he] at hcard
    have h0 : 0 < Nat.card Ah := Nat.card_pos
    have h4 : 4 ≤ p ^ 2 := by nlinarith
    nlinarith
  by_cases h2 : 2 ∣ Nat.card (Subgroup.center L')
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨Ah, hlt, le_rfl, TableBU.twoPartOf (Subgroup.center L') le_rfl (Nat.card L'), ?_,
      TableBU.isPGroup_twoPartOf _ _ _, fun a _ u hu => ?_⟩
    · obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
      rw [Subgroup.ne_bot_iff_exists_ne_one]
      refine ⟨⟨z, TableBU.mem_twoPartOf_of_pow le_rfl z.2 (k := 1) ?_⟩, ?_⟩
      · rw [pow_one]
        have h1 := pow_orderOf_eq_one z
        rw [hz] at h1
        simpa using congrArg Subtype.val h1
      · intro h1
        have h1' : (z : L') = 1 := congrArg Subtype.val h1
        rw [← Subgroup.orderOf_coe, h1', orderOf_one] at hz
        exact absurd hz (by norm_num)
    · exact ⟨mulAut_mem_center a hu.1, by rw [← map_pow, hu.2, map_one]⟩
  ·
    set δ := descAut hψ hZ with hδ
    have hδinj := descAut_injective hψ hZ hL
    have hEbI : ((A.map δ : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨φ, hφI, hφ⟩ := hAI a ha
      have he : δ a = φ := MulEquiv.ext fun s => by
        obtain ⟨l, rfl⟩ := hψ s
        rw [hδ, descAut_apply, hφ]
      rw [he]
      exact hφI
    have hcA : Nat.card (A.map δ) = Nat.card A := Subgroup.card_map_of_injective hδinj
    have hcAh : Nat.card (Ah.map δ) = Nat.card Ah := Subgroup.card_map_of_injective hδinj
    obtain ⟨U, hU1, hU2, hAU⟩ := hU
    have hUinj : ∀ u ∈ U, ψ u = 1 → u = 1 := by
      intro u hu hu1
      have huZ : u ∈ Subgroup.center L' := hZ ▸ hu1
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hU2 ⟨u, hu⟩
      rw [Subgroup.orderOf_mk] at hk
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
        exact hk
      · exfalso
        have h1 : orderOf (⟨u, huZ⟩ : Subgroup.center L') ∣ Nat.card (Subgroup.center L') :=
          orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk, hk] at h1
        exact h2 ((dvd_pow_self 2 hk0.ne').trans h1)
    have hV1 : U.map ψ ≠ ⊥ := by
      obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU1
      rw [Subgroup.ne_bot_iff_exists_ne_one]
      refine ⟨⟨ψ u, u, hu, rfl⟩, fun h1 => hu1 (Subtype.ext (hUinj u hu ?_))⟩
      exact congrArg Subtype.val h1
    have hEbV : ∀ φ ∈ A.map δ, ∀ v ∈ U.map ψ, φ v ∈ U.map ψ := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨u, hu, rfl⟩
      rw [hδ, descAut_apply]
      exact ⟨a u, hAU a ha u hu, rfl⟩
    obtain ⟨E', hE'lt, hE'le, V, hV1', hV2', hE'V⟩ := hcore (A.map δ) (Ah.map δ) hEbI
      (isElemAbelian_map hA δ) (hcA ▸ hr) (hcA ▸ h3) ⟨U.map ψ, hV1, hU2.map ψ, hEbV⟩
      (Subgroup.map_mono hAAh) (isElemAbelian_map hAh δ) (by rw [hcA, hcAh]; exact hcard)
    refine ⟨Ah ⊓ E'.comap δ, lt_of_le_of_ne (le_inf hAAh fun a ha => ?_) fun he => ?_,
      inf_le_left, ?_⟩
    · exact hE'lt.le ⟨a, ha, rfl⟩
    · apply hE'lt.not_ge
      intro φ hφ
      obtain ⟨a, ha, rfl⟩ := hE'le hφ
      have haA : a ∈ A := by
        rw [he]
        exact ⟨ha, hφ⟩
      exact ⟨a, haA, rfl⟩
    · obtain ⟨U', hU'1, hU'2, hU'V, hU'mem⟩ := exists_two_subgroup_preimage hψ hker hV1' hV2'
      refine ⟨U', hU'1, hU'2, fun a ha u hu => hU'mem _ ?_ ?_⟩
      · rw [← descAut_apply hψ hZ]
        exact hE'V _ ha.2 _ (hU'V hu)
      · obtain ⟨k, hk⟩ := hU'2 ⟨u, hu⟩
        refine ⟨k, ?_⟩
        have hk' : u ^ 2 ^ k = 1 := by
          have := congrArg Subtype.val hk
          rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
        rw [← map_pow, hk', map_one]

end CFSG.StandardType
