module

public import CFSG.Quasithin.Background.SmithB45HatA6Nine

public section

namespace CFSG.Quasithin.B45HatA6

open CFSG.Open

theorem case5_card_mod_nine {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}
    (hP : B42TypeHatA6 ↥L) (zL : ↥L) (hcen : Subgroup.center ↥L = Subgroup.zpowers zL)
    (h3 : (zL : MulAut V) ^ 3 = 1) (hz1 : (zL : MulAut V) ≠ 1)
    (hfp : ∀ v : V, (zL : MulAut V) v = v → v = 1) : Nat.card V % 9 = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hq, hZ3, ⟨eL⟩⟩ := hP
  have hL1080 : Nat.card ↥L = 1080 := (HatA6.quasisimple_card hq.1 hZ3 eL).2
  have : Group.IsPerfect ↥L := hq.1
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥L) := inferInstance
  have hP27 : Nat.card (P : Subgroup ↥L) = 27 := by
    rw [Sylow.card_eq_multiplicity, hL1080, factorization_1080_three]
    norm_num
  have hZp : IsPGroup 3 (Subgroup.center ↥L) := IsPGroup.of_card (n := 1) (by rw [hZ3]; norm_num)
  have hZP : Subgroup.center ↥L ≤ (P : Subgroup ↥L) := IsPGroup.le_sylow_of_normal hZp P
  have hzc : zL ∈ Subgroup.center ↥L := hcen ▸ Subgroup.mem_zpowers zL
  have hnc : ¬ ∀ a b : (P : Subgroup ↥L), a * b = b * a := by
    intro hab
    have hz := ShultStronglyClosedTI.central_element_mem_sylow_derived P ⟨zL, hZP hzc⟩ hzc
    have hbot : commutator (P : Subgroup ↥L) = ⊥ := by
      rw [eq_bot_iff, commutator_eq_closure, Subgroup.closure_le]
      rintro _ ⟨a, b, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab a b
    rw [hbot, Subgroup.mem_bot] at hz
    apply hz1
    have := congrArg (fun w : (P : Subgroup ↥L) => ((w : ↥L) : MulAut V)) hz
    simpa using this
  set P' : Subgroup (MulAut V) := (P : Subgroup ↥L).map L.subtype with hP'
  let eP : (P : Subgroup ↥L) ≃* ↥P' :=
    (P : Subgroup ↥L).equivMapOfInjective L.subtype L.subtype_injective
  have hP'27 : Nat.card P' = 27 := by rw [← Nat.card_congr eP.toEquiv, hP27]
  have hnc' : ¬ ∀ a b : ↥P', a * b = b * a := fun h =>
    hnc fun a b => eP.injective (by rw [map_mul, map_mul, h])
  have hzP' : (zL : MulAut V) ∈ P' := ⟨zL, hZP hzc, rfl⟩
  have hzfix : ∀ k : ℕ, ∀ v : V, ((zL : MulAut V) ^ k) v = v → v ≠ 1 → k % 3 = 0 := by
    intro k v hv hv1
    have hk : (zL : MulAut V) ^ k = (zL : MulAut V) ^ (k % 3) := by
      conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, h3, one_pow, one_mul]
    rw [hk] at hv
    have hk3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hkk : (k % 3)
    · rfl
    · exact absurd (hfp v (by simpa using hv)) hv1
    · exfalso
      apply hv1
      apply hfp v
      have h2 : (zL : MulAut V) ((zL : MulAut V) v) = v := by
        simpa [pow_two, MulAut.mul_apply] using hv
      calc (zL : MulAut V) v = (zL : MulAut V) ((zL : MulAut V) ((zL : MulAut V) v)) := by
            rw [h2]
        _ = v := by
          have := congrArg (fun y : MulAut V => y v) h3
          simpa [pow_succ, MulAut.mul_apply] using this
  set z' : ↥P' := ⟨(zL : MulAut V), hzP'⟩ with hz'
  set Zs : Subgroup ↥P' := Subgroup.zpowers z' with hZs
  have hz'3 : z' ^ 3 = 1 := Subtype.ext h3
  have hZs3 : Nat.card Zs = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz'3 fun h => hz1 (congrArg Subtype.val h)
  have hZcen : ∀ s : ↥P', ∀ w ∈ Zs, s * w = w * s := by
    intro s w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    apply Subtype.ext
    obtain ⟨s', -, hss⟩ := s.2
    have hcomm : (s' : MulAut V) * (zL : MulAut V) = (zL : MulAut V) * (s' : MulAut V) := by
      have := Subgroup.mem_center_iff.1 hzc s'
      exact congrArg Subtype.val this
    show (s : MulAut V) * ((zL : MulAut V) ^ k) = ((zL : MulAut V) ^ k) * (s : MulAut V)
    rw [← hss]
    exact (Commute.zpow_right hcomm k).eq
  have hstab : ∀ v : V, v ≠ 1 → 9 ∣ 27 / Nat.card (MulAction.stabilizer P' v) := by
    intro v hv1
    set S := MulAction.stabilizer P' v with hS
    have hSZ : S ⊓ Zs = ⊥ := by
      rw [eq_bot_iff]
      intro w ⟨hwS, hwZ⟩
      obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).2 hwZ
      rw [Subgroup.mem_bot, ← hn]
      have hwS' : w • v = v := hwS
      rw [← hn] at hwS'
      have hv' : ((zL : MulAut V) ^ n) v = v := hwS'
      have hn3 := hzfix n v hv' hv1
      apply Subtype.ext
      show (zL : MulAut V) ^ n = 1
      conv_lhs => rw [← Nat.div_add_mod n 3, hn3, add_zero, pow_mul, h3, one_pow]
    have hSdvd : Nat.card S ∣ 27 := hP'27 ▸ Subgroup.card_subgroup_dvd_card S
    have hprod : Nat.card S * 3 ≤ 27 := by
      have := Nat.card_le_card_of_injective _ (mul_injective_of_inf_eq_bot hSZ)
      rwa [Nat.card_prod, hZs3, hP'27] at this
    have hS9 : Nat.card S ≠ 9 := by
      intro h9
      apply hnc'
      have hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
        intro a ha b hb
        have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := S)
          (by rw [h9]; norm_num)
        exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      have hbij := (mul_injective_of_inf_eq_bot hSZ).bijective_of_nat_card_le
        (by rw [Nat.card_prod, h9, hZs3, hP'27])
      intro a b
      obtain ⟨⟨s₁, w₁⟩, rfl⟩ := hbij.2 a
      obtain ⟨⟨s₂, w₂⟩, rfl⟩ := hbij.2 b
      simp only
      calc (s₁ : ↥P') * w₁ * (s₂ * w₂) = s₁ * (w₁ * s₂) * w₂ := by group
        _ = s₁ * (s₂ * w₁) * w₂ := by rw [hZcen s₂ w₁ w₁.2]
        _ = (s₁ * s₂) * (w₁ * w₂) := by group
        _ = (s₂ * s₁) * (w₂ * w₁) := by
          rw [hSc _ s₁.2 _ s₂.2, show (w₁ : ↥P') * w₂ = w₂ * w₁ from hZcen w₁ w₂ w₂.2]
        _ = s₂ * (s₁ * w₂) * w₁ := by group
        _ = s₂ * (w₂ * s₁) * w₁ := by rw [hZcen s₁ w₂ w₂.2]
        _ = (s₂ : ↥P') * w₂ * (s₁ * w₁) := by group
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (show Nat.card S ∣ 3 ^ 3 by norm_num; exact hSdvd)
    interval_cases k
    · rw [hk]; norm_num
    · rw [hk]; norm_num
    · exact absurd (by rw [hk]; norm_num) hS9
    · rw [hk] at hprod; norm_num at hprod
  let _ : Fintype V := Fintype.ofFinite V
  let _ : Fintype ↥P' := Fintype.ofFinite _
  let _ : Fintype (Quotient (MulAction.orbitRel ↥P' V)) := Fintype.ofFinite _
  let _ : ∀ v : V, Fintype (MulAction.stabilizer ↥P' v) := fun _ => Fintype.ofFinite _
  have hcf := MulAction.card_eq_sum_card_group_div_card_stabilizer ↥P' V
  rw [Nat.card_eq_fintype_card, hcf]
  set ω₁ : Quotient (MulAction.orbitRel ↥P' V) := Quotient.mk'' (1 : V) with hω₁
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ω₁)]
  have hout₁ : ω₁.out = 1 := by
    have h : (Quotient.mk'' ω₁.out : Quotient (MulAction.orbitRel ↥P' V)) = ω₁ :=
      Quotient.out_eq' ω₁
    rw [hω₁, Quotient.eq'', MulAction.orbitRel_apply] at h
    obtain ⟨g, hg⟩ := h
    rw [← hg]
    exact map_one ((g : MulAut V))
  have hterm₁ : Fintype.card ↥P' / Fintype.card (MulAction.stabilizer ↥P' ω₁.out) = 1 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hout₁]
    have htop : MulAction.stabilizer ↥P' (1 : V) = ⊤ := by
      ext g
      simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
      exact map_one ((g : MulAut V))
    rw [htop, Subgroup.card_top]
    exact Nat.div_self Nat.card_pos
  have hrest : 9 ∣ ∑ ω ∈ Finset.univ.erase ω₁,
      Fintype.card ↥P' / Fintype.card (MulAction.stabilizer ↥P' ω.out) := by
    refine Finset.dvd_sum fun ω hω => ?_
    have hne : ω.out ≠ 1 := by
      intro h
      apply (Finset.mem_erase.1 hω).1
      rw [← Quotient.out_eq' ω, hω₁]
      exact congrArg _ h
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hP'27]
    exact hstab _ hne
  rw [hterm₁]
  omega

end CFSG.Quasithin.B45HatA6
