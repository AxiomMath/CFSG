module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.Quasithin.H13.FiveNorm

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise

@[expose] def PowOver (W : Type) [Group W] (U : Subgroup W) (m : ℕ) : Prop :=
  ∀ H : Subgroup W, U ≤ H → Group.IsSolvable ↥H → ∀ x ∈ H, x ^ m ∈ U

theorem PowOver.map_of_ker_le_center {W W' : Type} [Group W] [Group W'] {U : Subgroup W}
    {m : ℕ} (h : PowOver W U m) (π : W →* W') (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center W) : PowOver W' (U.map π) m := by
  intro H hUH hH x hx
  have hUA : U ≤ H.comap π := fun u hu => hUH ⟨u, hu, rfl⟩
  have hcomm : ∀ a b : ↥(π.subgroupComap H).ker, a * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : (a : W) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
    apply Subtype.ext
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hker ha') (b : W)).symm
  have hkS : Group.IsSolvable ↥(π.subgroupComap H).ker := Group.isSolvable_of_comm hcomm
  have hAS : Group.IsSolvable ↥(H.comap π) :=
    Group.isSolvable_of_ker_le_range (π.subgroupComap H).ker.subtype (π.subgroupComap H)
      (by rw [Subgroup.range_subtype])
  obtain ⟨y, rfl⟩ := hπ x
  exact ⟨y ^ m, h _ hUA hAS y hx, map_pow π y m⟩

theorem PowOver.map_equiv {W W' : Type} [Group W] [Group W'] {U : Subgroup W} {m : ℕ}
    (h : PowOver W U m) (e : W ≃* W') : PowOver W' (U.map e.toMonoidHom) m :=
  h.map_of_ker_le_center e.toMonoidHom e.surjective (by
    intro x hx
    rw [MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom] at hx
    rw [e.map_eq_one_iff.mp hx]
    exact Subgroup.one_mem _)

theorem noFiveOver_of_powOver {W : Type} [Group W] [Finite W] {U : Subgroup W}
    (hU : IsSylowTwoOf U ⊤) {m : ℕ} (hm : Nat.Coprime m 5) (h : PowOver W U m) :
    NoFiveOver W := by
  intro S H hS hSH hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨h1, h2⟩ := isSylowTwoOf_top_index hU
  obtain ⟨h3, h4⟩ := isSylowTwoOf_top_index hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W (h1.toSylow h2) (h3.toSylow h4)
  have hmap : U.map (MulAut.conj g).toMonoidHom = S := by
    have h5 := congrArg (fun P : Sylow 2 W => (P : Subgroup W)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h5
    rw [← h5, Subgroup.pointwise_smul_def]
    rfl
  have hS' : PowOver W S m := hmap ▸ h.map_equiv (MulAut.conj g)
  obtain ⟨k, hk⟩ := h3.exists_card_eq
  have hHs : Group.IsSolvable ↥H := by
    let _ : Fintype ↥H := Fintype.ofFinite _
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := 5) (a := k) (b := 1) Nat.prime_two Nat.prime_five (by norm_num) ?_
    rw [← Nat.card_eq_fintype_card, hcard, hk]
    ring
  obtain ⟨⟨x, hxH⟩, hx5⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 5
    (by rw [hcard]; exact dvd_mul_right 5 _)
  have hxo : orderOf x = 5 := by rw [← Subgroup.orderOf_mk x hxH]; exact hx5
  have hxm := hS' H hSH hHs x hxH
  have hord : orderOf (x ^ m) = 5 := by
    rw [Nat.Coprime.orderOf_pow (by rw [hxo]; exact hm.symm), hxo]
  obtain ⟨j, hj⟩ := h3 ⟨_, hxm⟩
  have h6 : (x ^ m) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have h7 := orderOf_dvd_of_pow_eq_one h6
  rw [hord] at h7
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
    (Nat.prime_five.dvd_of_dvd_pow h7)
  omega

theorem pow_mem_of_mem_sup {G : Type*} [Group G] {T U : Subgroup G}
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) {m : ℕ} (hT : ∀ t ∈ T, t ^ m = 1) {x : G}
    (hx : x ∈ T ⊔ U) : x ^ m ∈ U := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right T U hTU] at hx
  obtain ⟨t, ht, u, hu, rfl⟩ := hx
  have key : ∀ n : ℕ, ∃ u' ∈ U, (t * u) ^ n = t ^ n * u' := by
    intro n
    induction n with
    | zero => exact ⟨1, U.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨u', hu', he⟩ := ih
      refine ⟨t⁻¹ * u' * t * u, ?_, ?_⟩
      · have h1 : t⁻¹ * u' * t⁻¹⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp (hTU (T.inv_mem ht)) u').mp hu'
        rw [inv_inv] at h1
        exact U.mul_mem h1 hu
      · rw [pow_succ, he]
        group
  obtain ⟨u', hu', he⟩ := key m
  rw [he, hT t ht, one_mul]
  exact hu'

theorem fiveInner_of_hom {W Q : Type} [Group W] [Group Q] (Θ : MulAut W →* Q)
    (hker : ∀ α : MulAut W, Θ α = 1 → ∃ x : W, α = MulAut.conj x)
    (hQ : ∀ q : Q, q ^ 5 = 1 → q = 1) : FiveInner W := fun α hα =>
  hker α (hQ _ (by rw [← map_pow, hα, map_one]))

theorem fiveInner_of_card_outer_coprime {W : Type} [Group W] [Finite W]
    (h : Nat.Coprime (Nat.card (Outer W)) 5) : FiveInner W := by
  intro α hα
  have : Finite (MulAut W) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (Outer W) := Finite.of_surjective _ (QuotientGroup.mk'_surjective (inner W))
  have h1 : (QuotientGroup.mk' (inner W) α) ^ 5 = 1 := by rw [← map_pow, hα, map_one]
  have h4 : orderOf (QuotientGroup.mk' (inner W) α) = 1 :=
    Nat.eq_one_of_dvd_coprimes h (orderOf_dvd_natCard _) (orderOf_dvd_of_pow_eq_one h1)
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
  obtain ⟨x, hx⟩ := h4
  exact ⟨x, hx.symm⟩

theorem eq_one_of_pow_five_eq_one {Q : Type*} [Group Q] (h : Nat.Coprime (Nat.card Q) 5)
    (q : Q) (hq : q ^ 5 = 1) : q = 1 :=
  orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes h (orderOf_dvd_natCard q) (orderOf_dvd_of_pow_eq_one hq))

theorem center_eq_bot_of_isPerfect {W : Type*} [Group W] [IsSimpleGroup W] [Group.IsPerfect W] :
    Subgroup.center W = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center W) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative W := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center W := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm⟩⟩
    exact Group.IsPerfect.not_isMulCommutative W hc

theorem fiveRigid_of_subsingleton {W : Type} [Group W] [Subsingleton W] : FiveRigid W := by
  refine ⟨Subgroup.eq_bot_of_subsingleton _, fun α _ => ⟨1, MulEquiv.ext fun _ =>
    Subsingleton.elim _ _⟩, fun S H _ _ hcard => ?_⟩
  have : Subsingleton ↥H := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have : Subsingleton ↥S := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  rw [Nat.card_of_subsingleton (1 : ↥H), Nat.card_of_subsingleton (1 : ↥S)] at hcard
  omega

theorem fiveRigid_quotCenter_of_mulEquiv {X P : Type} [Group X] [Group P] [IsSimpleGroup X]
    (e : X ≃* P) (hi : FiveInner P) (hn : NoFiveOver P) : FiveRigid (X ⧸ Subgroup.center X) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · have hP : Subgroup.center P = ⊥ := by rw [← Subgroup.map_center_eq e, h, Subgroup.map_bot]
    have hX := fiveRigid_of_mulEquiv e.symm ⟨hP, hi, hn⟩
    obtain ⟨-, ⟨e'⟩⟩ := nonempty_quotCenter_equiv (MulEquiv.refl X) h
    exact fiveRigid_of_mulEquiv e'.symm hX
  · have : Subsingleton (X ⧸ Subgroup.center X) := ⟨fun a b => by
      induction a using QuotientGroup.induction_on with | H a =>
      induction b using QuotientGroup.induction_on with | H b =>
      exact QuotientGroup.eq.mpr (by rw [h]; exact Subgroup.mem_top _)⟩
    exact fiveRigid_of_subsingleton

theorem ringEquiv_pow_eq_one {F : Type} [Field F] {e : ℕ} (he : 1 ≤ e)
    (hF : Nat.card F = 2 ^ e) (σ : F ≃+* F) : σ ^ e = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two he hF
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have := pow_card_eq_one' (G := F ≃+* F) (x := σ)
  rwa [hcard] at this

end CFSG.Quasithin.H13.FiveNorm
