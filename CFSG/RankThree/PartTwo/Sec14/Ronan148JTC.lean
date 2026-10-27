module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG.ComponentClassification

theorem fixed_of_mem_center_of_pow_three {T : Type*} [Group T]
    (hZ : Nat.card (Subgroup.center T) = 3) {σ : MulAut T} (hσ3 : σ ^ 3 = 1) {z : T}
    (hz : z ∈ Subgroup.center T) : σ z = z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Subgroup.center T) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  by_cases hz1 : z = 1
  · subst hz1
    exact map_one σ
  have hord_dvd : orderOf z ∣ 3 := by
    have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.center T) hz
    rwa [hZ] at h1
  have hord3 : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord_dvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hzpow : Subgroup.zpowers z = Subgroup.center T := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
    exact le_of_eq (by rw [Nat.card_zpowers, hord3, hZ])
  have hσz : σ z ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := MulEquiv.surjective σ g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) h]
  have hσz' : σ z ∈ Subgroup.zpowers z := by
    rw [hzpow]
    exact hσz
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hσz'
  have e1 : σ (σ z) = z ^ (a * a) := by
    calc σ (σ z) = σ (z ^ a) := by rw [ha]
      _ = σ z ^ a := map_zpow σ z a
      _ = (z ^ a) ^ a := by rw [ha]
      _ = z ^ (a * a) := (zpow_mul z a a).symm
  have e2 : σ (σ (σ z)) = z ^ (a * (a * a)) := by
    calc σ (σ (σ z)) = σ (z ^ (a * a)) := by rw [e1]
      _ = σ z ^ (a * a) := map_zpow σ z (a * a)
      _ = (z ^ a) ^ (a * a) := by rw [ha]
      _ = z ^ (a * (a * a)) := (zpow_mul z a (a * a)).symm
  have h3 : σ (σ (σ z)) = z := by
    have h := DFunLike.congr_fun hσ3 z
    simp only [pow_three, MulAut.mul_apply, MulAut.one_apply] at h
    exact h
  have hzpow3 : z ^ (a * (a * a)) = z := e2.symm.trans h3
  have hdvd3 : (3 : ℤ) ∣ a * (a * a) - 1 := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr
      (show z ^ (a * (a * a) - 1) = 1 by rw [zpow_sub_one, hzpow3, mul_inv_cancel])
    rw [hord3] at h
    exact_mod_cast h
  have hmod : (a : ZMod 3) = 1 := by
    have h1 : ((a * (a * a) - 1 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast hdvd3)
    push_cast at h1
    have h2 : (a : ZMod 3) ^ 3 = 1 := by linear_combination h1
    exact (ZMod.pow_card (a : ZMod 3)).symm.trans h2
  have hdvd2 : (3 : ℤ) ∣ a - 1 := by
    have h1 : ((a - 1 : ℤ) : ZMod 3) = 0 := by
      push_cast
      rw [hmod, sub_self]
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h1
  have hz1' : z ^ (a - 1) = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [hord3]
    exact_mod_cast hdvd2
  have hza : z ^ a = z := by
    calc z ^ a = z ^ ((a - 1) + 1) := by rw [sub_add_cancel]
      _ = z ^ (a - 1) * z := zpow_add_one z (a - 1)
      _ = z := by rw [hz1', one_mul]
  rw [← ha]
  exact hza

theorem eq_one_of_centerQuotientHom_eq_one {T : Type*} [Group T]
    (hZ : Nat.card (Subgroup.center T) = 3) [Group.IsPerfect (T ⧸ Subgroup.center T)]
    {σ : MulAut T} (hσ3 : σ ^ 3 = 1)
    (hbar : PerfectAutomorphisms.centerQuotientHom T σ = 1) : σ = 1 := by
  have hbar' : PerfectAutomorphisms.onCenterQuotient σ = 1 := hbar
  have hcentral : ∀ t : T, t⁻¹ * σ t ∈ Subgroup.center T := by
    intro t
    have h1 := PerfectAutomorphisms.onCenterQuotient_apply_mk σ t
    rw [hbar', MulAut.one_apply] at h1
    exact QuotientGroup.eq.mp h1
  let ζ : T →* Subgroup.center T :=
    { toFun := fun t => ⟨t⁻¹ * σ t, hcentral t⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        change (a * b)⁻¹ * σ (a * b) = (a⁻¹ * σ a) * (b⁻¹ * σ b)
        have hc := Subgroup.mem_center_iff.mp (hcentral a) b⁻¹
        rw [mul_inv_rev, map_mul]
        calc b⁻¹ * a⁻¹ * (σ a * σ b) = b⁻¹ * (a⁻¹ * σ a) * σ b := by group
          _ = a⁻¹ * σ a * b⁻¹ * σ b := by rw [hc]
          _ = a⁻¹ * σ a * (b⁻¹ * σ b) := by group }
  have hker : Subgroup.center T ≤ ζ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change z⁻¹ * σ z = 1
    rw [fixed_of_mem_center_of_pow_three hZ hσ3 hz, inv_mul_cancel]
  have hψ : QuotientGroup.lift (Subgroup.center T) ζ hker = 1 :=
    PerfectAutomorphisms.hom_eq_one_of_commutative _
  have hζ1 : ∀ t : T, ζ t = 1 := by
    intro t
    have h1 : QuotientGroup.lift (Subgroup.center T) ζ hker (QuotientGroup.mk t) = ζ t :=
      QuotientGroup.lift_mk (Subgroup.center T) hker t
    rw [← h1, hψ, MonoidHom.one_apply]
  ext t
  have h1 : t⁻¹ * σ t = 1 := congrArg Subtype.val (hζ1 t)
  show σ t = t
  exact (inv_mul_eq_one.mp h1).symm

theorem eq_one_of_commute_tripleCover {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6))) {e : X}
    (heK : e ∈ Subgroup.normalizer (K : Set X)) (he3 : e ^ 3 = 1)
    (he : ∃ k ∈ K, e * k ≠ k * e) {x : X} (hxK : x ∈ K) (hxe : x * e = e * x)
    (hx : Nat.Coprime (orderOf x) 3) : x = 1 := by
  obtain ⟨hZ, ⟨eQ⟩⟩ := hK
  haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  haveI : Group.IsPerfect (↥K ⧸ Subgroup.center ↥K) :=
    Group.IsPerfect.ofSurjective (f := eQ.symm.toMonoidHom) eQ.symm.surjective
  obtain ⟨σ, hσ⟩ : ∃ σ : MulAut ↥K, σ = Subgroup.normalizerMonoidHom K ⟨e, heK⟩ := ⟨_, rfl⟩
  have hσapp : ∀ t : ↥K, ((σ t : ↥K) : X) = e * (t : X) * e⁻¹ := fun t => by
    rw [hσ]
    rfl
  have hσ3 : σ ^ 3 = 1 := by
    have he3' : (⟨e, heK⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by simpa using he3)
    rw [hσ, ← map_pow, he3', map_one]
  have hσ1 : σ ≠ 1 := by
    obtain ⟨k, hk, hek⟩ := he
    intro h1
    apply hek
    have h2 : ((σ ⟨k, hk⟩ : ↥K) : X) = k := by
      rw [h1]
      rfl
    rw [hσapp] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2
  obtain ⟨σbar, hσbar⟩ : ∃ s : MulAut (↥K ⧸ Subgroup.center ↥K),
      s = PerfectAutomorphisms.centerQuotientHom ↥K σ := ⟨_, rfl⟩
  have hσbar_apply : ∀ t : ↥K, σbar (QuotientGroup.mk' (Subgroup.center ↥K) t) =
      QuotientGroup.mk' (Subgroup.center ↥K) (σ t) := by
    intro t
    rw [hσbar]
    exact PerfectAutomorphisms.onCenterQuotient_apply_mk σ t
  have hσbar3 : σbar ^ 3 = 1 := by
    rw [hσbar, ← map_pow, hσ3, map_one]
  have hτ3 : (MulAut.congr eQ σbar) ^ 3 = 1 := by
    rw [← map_pow, hσbar3, map_one]
  have hτ1 : MulAut.congr eQ σbar ≠ 1 := by
    intro h1
    apply hσ1
    have h2 : σbar = 1 := (MulAut.congr eQ).injective (h1.trans (map_one _).symm)
    exact eq_one_of_centerQuotientHom_eq_one hZ hσ3 (hσbar.symm.trans h2)
  have hxσ : σ ⟨x, hxK⟩ = ⟨x, hxK⟩ := by
    apply Subtype.ext
    rw [hσapp]
    show e * x * e⁻¹ = x
    rw [← hxe, mul_inv_cancel_right]
  have hxfix : MulAut.congr eQ σbar (eQ (QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hxK⟩)) =
      eQ (QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hxK⟩) := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hσbar_apply, hxσ]
  have hxk : (eQ (QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hxK⟩)) ^ orderOf x = 1 := by
    have h1 : (⟨x, hxK⟩ : ↥K) ^ orderOf x = 1 := Subtype.ext (by simp)
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  have hx1 := Item148PtRes.eq_one_of_fixed_alternating_six hτ3 hτ1 hxfix hxk hx
  have hxZ : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    have h1 : QuotientGroup.mk' (Subgroup.center ↥K) (⟨x, hxK⟩ : ↥K) = 1 :=
      eQ.injective (hx1.trans (map_one eQ).symm)
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hord : orderOf x ∣ 3 := by
    have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥K) hxZ
    rw [hZ, Subgroup.orderOf_mk] at h1
    exact h1
  have hd : orderOf x ∣ Nat.gcd (orderOf x) 3 := Nat.dvd_gcd dvd_rfl hord
  rw [hx, Nat.dvd_one] at hd
  exact orderOf_eq_one_iff.mp hd

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
