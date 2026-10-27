module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SecMod

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

theorem secSub_commutator_sup {G : Type} [Group G] {R P I U : Subgroup G} {M : Type}
    [AddCommGroup M] [DistribMulAction ↥R M] {κ : ↥P →* Multiplicative M}
    (hκ : IsSecMod R P I M κ) (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hIU : I ≤ U)
    (hUP : U ≤ P) (z : ↥R) (hU : ∀ x ∈ U, (z : G) * x * (z : G)⁻¹ ∈ U)
    (hU' : ∀ x ∈ U, (z : G)⁻¹ * x * (z : G) ∈ U) :
    secSub κ (⁅U, Subgroup.zpowers (z : G)⁆ ⊔ I) =
      (secSub κ U).map (CFSG.ClassicalGroups.F2Fixed.comm M z) := by
  have hIP : I ≤ P := hIU.trans hUP
  set T : AddSubgroup M := (secSub κ U).map (CFSG.ClassicalGroups.F2Fixed.comm M z)
  have hcP : ∀ (x : ↥P) (w : ↥R), ⁅(x : G), (w : G)⁆ ∈ P := by
    intro x w
    have e : ⁅(x : G), (w : G)⁆ = (x : G) * ((w : G) * (x : G)⁻¹ * (w : G)⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact P.mul_mem x.2 (hP (w : G) w.2 _ (P.inv_mem x.2))
  have hcval : ∀ (x : ↥P) (w : ↥R),
      Multiplicative.toAdd (κ ⟨⁅(x : G), (w : G)⁆, hcP x w⟩) =
        Multiplicative.toAdd (κ x) - w • Multiplicative.toAdd (κ x) := by
    intro x w
    obtain ⟨u, hu⟩ : ∃ u : ↥P, (u : G) = (w : G) * (x : G)⁻¹ * (w : G)⁻¹ :=
      ⟨⟨(w : G) * (x : G)⁻¹ * (w : G)⁻¹, hP (w : G) w.2 _ (P.inv_mem x.2)⟩, rfl⟩
    have hu' : (u : G) = (w : G) * ((x⁻¹ : ↥P) : G) * (w : G)⁻¹ := hu
    have hκu : κ u = Multiplicative.ofAdd (-(w • Multiplicative.toAdd (κ x))) := by
      rw [hκ.act w x⁻¹ u hu', map_inv, toAdd_inv, smul_neg]
    have hxu' : (x : G) * (u : G) = ⁅(x : G), (w : G)⁆ := by
      rw [hu, commutatorElement_def]
      group
    have hxu : x * u = ⟨⁅(x : G), (w : G)⁆, hcP x w⟩ := Subtype.ext hxu'
    rw [← hxu, map_mul, toAdd_mul, hκu, toAdd_ofAdd, sub_eq_add_neg]
  have hzW : ∀ b ∈ secSub κ U, z • b ∈ secSub κ U := by
    intro b hb
    obtain ⟨x, hxU, hxb⟩ := mem_secSub.mp hb
    have hy := hκ.act z x ⟨(z : G) * (x : G) * (z : G)⁻¹, hP (z : G) z.2 _ x.2⟩ rfl
    exact mem_secSub.mpr ⟨⟨(z : G) * (x : G) * (z : G)⁻¹, hP (z : G) z.2 _ x.2⟩, hU x hxU,
      by rw [hy, hxb, toAdd_ofAdd]⟩
  have hzW' : ∀ b ∈ secSub κ U, z⁻¹ • b ∈ secSub κ U := by
    intro b hb
    obtain ⟨x, hxU, hxb⟩ := mem_secSub.mp hb
    have hyP : (z : G)⁻¹ * (x : G) * (z : G) ∈ P := by
      simpa using hP (z : G)⁻¹ (R.inv_mem z.2) x x.2
    have he : (z : G)⁻¹ * (x : G) * (z : G) = (z : G)⁻¹ * (x : G) * ((z⁻¹ : ↥R) : G)⁻¹ := by
      rw [Subgroup.coe_inv, inv_inv]
    have hy := hκ.act z⁻¹ x ⟨(z : G)⁻¹ * (x : G) * (z : G), hyP⟩ he
    exact mem_secSub.mpr ⟨⟨(z : G)⁻¹ * (x : G) * (z : G), hyP⟩, hU' x hxU,
      by rw [hy, hxb, toAdd_ofAdd]⟩
  have hzT : ∀ b ∈ secSub κ U, z • b - b ∈ T := fun b hb =>
    AddSubgroup.mem_map.mpr ⟨b, hb, CFSG.ClassicalGroups.F2Fixed.comm_apply z b⟩
  let Z : Subgroup ↥R :=
    { carrier := {w | ∀ b ∈ secSub κ U,
        w • b ∈ secSub κ U ∧ w⁻¹ • b ∈ secSub κ U ∧ w • b - b ∈ T}
      mul_mem' := by
        intro w₁ w₂ h₁ h₂ b hb
        have hw₂ := h₂ b hb
        have hw₁ := h₁ _ hw₂.1
        have hwb : (w₁ * w₂) • b ∈ secSub κ U := by
          rw [mul_smul]
          exact hw₁.1
        refine ⟨hwb, ?_, ?_⟩
        · rw [mul_inv_rev, mul_smul]
          exact (h₂ _ (h₁ b hb).2.1).2.1
        · have e : w₁ • (w₂ • b) - b = (w₁ • (w₂ • b) - w₂ • b) + (w₂ • b - b) := by
            abel
          rw [mul_smul, e]
          exact T.add_mem hw₁.2.2 hw₂.2.2
      one_mem' := by
        intro b hb
        simp only [inv_one, one_smul, sub_self]
        exact ⟨hb, hb, T.zero_mem⟩
      inv_mem' := by
        intro w h b hb
        refine ⟨(h b hb).2.1, ?_, ?_⟩
        · rw [inv_inv]
          exact (h b hb).1
        · have hc := (h _ (h b hb).2.1).2.2
          rw [smul_inv_smul] at hc
          rw [← neg_sub]
          exact T.neg_mem hc }
  have hzZ : z ∈ Z := by
    intro b hb
    exact ⟨hzW b hb, hzW' b hb, hzT b hb⟩
  have hKn : ∀ (n : ℤ) (b : M), b ∈ secSub κ U → (z ^ n) • b - b ∈ T :=
    fun n b hb => (zpow_mem hzZ n b hb).2.2
  set Y : Subgroup G := ((AddSubgroup.toSubgroup T).comap κ).map P.subtype
  have hmemY : ∀ x : ↥P, (x : G) ∈ Y ↔ Multiplicative.toAdd (κ x) ∈ T := fun x =>
    Subgroup.mem_map_iff_mem P.subtype_injective
  have hIY : I ≤ Y := by
    intro x hx
    refine (hmemY ⟨x, hIP hx⟩).mpr ?_
    rw [(hκ.ker ⟨x, hIP hx⟩).mpr hx, toAdd_one]
    exact T.zero_mem
  have hY : ∀ (x : ↥P) (n : ℤ), (x : G) ∈ U → ⁅(x : G), (z : G) ^ n⁆ ∈ Y := by
    intro x n hx
    have hw : ((z ^ n : ↥R) : G) = (z : G) ^ n := by
      rw [Subgroup.coe_zpow]
    rw [← hw]
    refine (hmemY ⟨⁅(x : G), ((z ^ n : ↥R) : G)⁆, hcP x (z ^ n)⟩).mpr ?_
    rw [hcval x (z ^ n), ← neg_sub]
    exact T.neg_mem (hKn n _ ((toAdd_mem_secSub_iff hκ hIU x).mpr hx))
  have hSY : ⁅U, Subgroup.zpowers (z : G)⁆ ≤ Y := by
    rw [Subgroup.commutator_le]
    intro h hh k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact hY ⟨h, hUP hh⟩ n hh
  refine le_antisymm ?_ ?_
  · have hle : secSub κ (⁅U, Subgroup.zpowers (z : G)⁆ ⊔ I) ≤ secSub κ Y :=
      secSub_mono (sup_le hSY hIY)
    refine hle.trans ?_
    intro a ha
    obtain ⟨x, hx, hxa⟩ := mem_secSub.mp ha
    have e : Multiplicative.toAdd (κ x) = a := by
      rw [hxa, toAdd_ofAdd]
    rw [← e]
    exact (hmemY x).mp hx
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := AddSubgroup.mem_map.mp ha
    obtain ⟨p, hpU, hp⟩ := mem_secSub.mp hb
    obtain ⟨q, hq⟩ : ∃ q : ↥P, (q : G) = (z : G) * (p : G) * (z : G)⁻¹ :=
      ⟨⟨(z : G) * (p : G) * (z : G)⁻¹, hP (z : G) z.2 _ p.2⟩, rfl⟩
    have hκq : κ q = Multiplicative.ofAdd (z • b) := by
      rw [hκ.act z p q hq, hp, toAdd_ofAdd]
    have hzp : ⁅(z : G), (p : G)⁆ ∈ ⁅U, Subgroup.zpowers (z : G)⁆ := by
      have h1 : ⁅(p : G), (z : G)⁆ ∈ ⁅U, Subgroup.zpowers (z : G)⁆ :=
        Subgroup.commutator_mem_commutator hpU (Subgroup.mem_zpowers _)
      have h2 := inv_mem h1
      rwa [commutatorElement_inv] at h2
    have hxG : ((q * p⁻¹ : ↥P) : G) = ⁅(z : G), (p : G)⁆ := by
      show (q : G) * (p : G)⁻¹ = ⁅(z : G), (p : G)⁆
      rw [hq, commutatorElement_def]
    refine mem_secSub.mpr ⟨q * p⁻¹, ?_, ?_⟩
    · rw [hxG]
      exact Subgroup.mem_sup_left hzp
    · rw [map_mul, map_inv, hκq, hp, CFSG.ClassicalGroups.F2Fixed.comm_apply, sub_eq_add_neg,
        ofAdd_add, ← ofAdd_neg]

theorem natCard_commutator_sup_of_le {G : Type} [Group G] [Finite G] {R P I U : Subgroup G}
    {M : Type} [AddCommGroup M] [DistribMulAction ↥R M] {κ : ↥P →* Multiplicative M}
    (hκ : IsSecMod R P I M κ) (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hIU : I ≤ U)
    (hUP : U ≤ P) (z : ↥R) (hU : ∀ x ∈ U, (z : G) * x * (z : G)⁻¹ ∈ U) :
    Nat.card ↥(⁅U, Subgroup.zpowers (z : G)⁆ ⊔ I) =
      Nat.card ↥I * Nat.card ↥((secSub κ U).map (CFSG.ClassicalGroups.F2Fixed.comm M z)) := by
  have hIP : I ≤ P := hIU.trans hUP
  have hU' : ∀ x ∈ U, (z : G)⁻¹ * x * (z : G) ∈ U := by
    intro x hx
    let f : U → U := fun y => ⟨(z : G) * (y : G) * (z : G)⁻¹, hU y y.2⟩
    have hf : Function.Injective f := by
      intro y₁ y₂ hy
      have h' : (z : G) * (y₁ : G) * (z : G)⁻¹ = (z : G) * (y₂ : G) * (z : G)⁻¹ :=
        congrArg Subtype.val hy
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
    obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hf ⟨x, hx⟩
    have hyx : (z : G) * (y : G) * (z : G)⁻¹ = x := congrArg Subtype.val hy
    have e : (z : G)⁻¹ * x * (z : G) = (y : G) := by
      rw [← hyx]
      group
    rw [e]
    exact y.2
  have hSP : ⁅U, Subgroup.zpowers (z : G)⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro h hh k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hn : (z : G) ^ n ∈ R := zpow_mem z.2 n
    have e : h * (z : G) ^ n * h⁻¹ * ((z : G) ^ n)⁻¹ =
        h * ((z : G) ^ n * h⁻¹ * ((z : G) ^ n)⁻¹) := by
      group
    rw [commutatorElement_def, e]
    exact P.mul_mem (hUP hh) (hP _ hn _ (P.inv_mem (hUP hh)))
  have hUP' : ⁅U, Subgroup.zpowers (z : G)⁆ ⊔ I ≤ P := sup_le hSP hIP
  have hIU' : I ≤ ⁅U, Subgroup.zpowers (z : G)⁆ ⊔ I := le_sup_right
  have h1 := natCard_secSub_mul hIP hκ hIU' hUP'
  rw [secSub_commutator_sup hκ hP hIU hUP z hU hU'] at h1
  rw [← h1, mul_comm]

theorem natCard_commutator_sup {G : Type} [Group G] [Finite G] {R P I : Subgroup G} {M : Type}
    [AddCommGroup M] [DistribMulAction ↥R M] {κ : ↥P →* Multiplicative M}
    (hκ : IsSecMod R P I M κ) (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hIP : I ≤ P)
    (z : ↥R) :
    Nat.card ↥(⁅P, Subgroup.zpowers (z : G)⁆ ⊔ I) =
      Nat.card ↥I * Nat.card ↥(CFSG.ClassicalGroups.F2Fixed.comm M z).range := by
  have h := natCard_commutator_sup_of_le hκ hP hIP le_rfl z (hP z z.2)
  rwa [secSub_eq_top hκ, ← AddMonoidHom.range_eq_map] at h

end CFSG.RankThree.GF2n.Stroth80
