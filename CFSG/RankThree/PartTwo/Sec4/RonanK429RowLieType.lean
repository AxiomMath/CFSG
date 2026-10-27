module

public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsKS
public import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.RankThree.PartTwo.Sec13.Item136Pair

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo

section Lift

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_e9_lift (N : Subgroup Y) [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {E' : Subgroup (Y ⧸ N)} (hE' : CFSG.Assembly.IsElemAbelian 3 E') (h9 : Nat.card E' = 9) :
    ∃ P : Subgroup Y, P.map (QuotientGroup.mk' N) = E' ∧ Nat.card P = 9 ∧ P ⊓ N = ⊥ ∧
      CFSG.Assembly.IsElemAbelian 3 P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup Y := E'.comap (QuotientGroup.mk' N) with hH
  have hHmap : H.map (QuotientGroup.mk' N) = E' := by
    rw [hH, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N),
      top_inf_eq]
  have h9H : 3 ^ 2 ∣ Nat.card H := by
    have := Subgroup.card_map_dvd (H := H) (QuotientGroup.mk' N)
    rw [hHmap, h9] at this
    simpa using this
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9H
  set P : Subgroup Y := P₀.map H.subtype with hP
  have hP9 : Nat.card P = 9 := by
    rw [hP, Subgroup.card_map_of_injective (Subgroup.subtype_injective H), hP₀]
    norm_num
  have hPN : P ⊓ N = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hP9, show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN)
  have hPH : P ≤ H := by
    rw [hP]
    exact Subgroup.map_subtype_le P₀
  have hinj : ∀ a ∈ P, ∀ b ∈ P, QuotientGroup.mk' N a = QuotientGroup.mk' N b → a = b := by
    intro a ha b hb hab
    have hm : a * b⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff (N := N), QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change QuotientGroup.mk' N a * (QuotientGroup.mk' N b)⁻¹ = 1
      rw [hab, mul_inv_cancel]
    have hm' : a * b⁻¹ ∈ P ⊓ N := Subgroup.mem_inf.mpr ⟨mul_mem ha (inv_mem hb), hm⟩
    rw [hPN, Subgroup.mem_bot] at hm'
    exact mul_inv_eq_one.mp hm'
  have hPmap : P.map (QuotientGroup.mk' N) = E' := by
    have hle : P.map (QuotientGroup.mk' N) ≤ E' := by
      rw [← hHmap]
      exact Subgroup.map_mono hPH
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [h9]
    have hinj' : Function.Injective ((QuotientGroup.mk' N).comp P.subtype) := by
      intro a b hab
      exact Subtype.ext (hinj a a.2 b b.2 hab)
    have hrange : ((QuotientGroup.mk' N).comp P.subtype).range = P.map (QuotientGroup.mk' N) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv.symm, hP9]
  refine ⟨P, hPmap, hP9, hPN, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩⟩
  ·
    have hma : QuotientGroup.mk' N (a : Y) ∈ E' := hPmap ▸ ⟨a, a.2, rfl⟩
    have hmb : QuotientGroup.mk' N (b : Y) ∈ E' := hPmap ▸ ⟨b, b.2, rfl⟩
    have hc := congrArg Subtype.val (hE'.1.is_comm.comm ⟨_, hma⟩ ⟨_, hmb⟩)
    simp only [Subgroup.coe_mul] at hc
    rw [← map_mul, ← map_mul] at hc
    exact hinj _ (mul_mem a.2 b.2) _ (mul_mem b.2 a.2) hc
  ·
    have hma : QuotientGroup.mk' N a ∈ E' := hPmap ▸ ⟨a, ha, rfl⟩
    have h3 := hE'.2 _ hma
    rw [← map_pow] at h3
    exact hinj _ (pow_mem ha 3) _ (one_mem P) (by rw [h3, map_one])

end Lift

section Types


variable {S : Type} [Group S] [Finite S]

theorem exists_e9_of_type429 {K : Subgroup S} [hKperf : Group.IsPerfect K]
    (htype : (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi (K ⧸ CFSG.pCore 2 K) p e) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.M12) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.M22) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.J2)) :
    ∃ E : Subgroup S, E ≤ K ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 3 = 1) ∧
      Nat.card E = 9 ∧ ∀ z ∈ E, (∀ k ∈ K, z * k = k * z) → z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup K := CFSG.pCore 2 K with hNdef
  haveI hNn : N.Normal := CFSG.pCore_normal
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hN3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hQperf : Group.IsPerfect (K ⧸ N) := by
    rw [Group.isPerfect_def]
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hy : y ∈ commutator K := by
      rw [Group.isPerfect_def.mp hKperf]
      exact Subgroup.mem_top y
    have hmap := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hy
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N), ← commutator_def] at hmap
  have hEQ : ∃ E' : Subgroup (K ⧸ N), CFSG.Assembly.IsElemAbelian 3 E' ∧ Nat.card E' = 9 := by
    refine Sec15.ks153ThreeRank (K ⧸ N) ?_
    rcases htype with ⟨p, e, hp, he, hcase⟩ | h | h | h | h
    · exact Or.inr (Or.inl ⟨p, e, hp, he, hcase⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl h
  obtain ⟨E', hE', h9'⟩ := hEQ
  have hQnt : Nontrivial (K ⧸ N) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : Nat.card E' ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  have hZQ : Subgroup.center (K ⧸ N) = ⊥ := by
    obtain ⟨⟨-, hM22z⟩, ⟨-, hM12z⟩, ⟨-, hJ2z⟩⟩ := Sec13.sporadicModels131
    rcases htype with ⟨p, e, hp, he, hcase⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · rcases hcase with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
      · exact Sec13.center_eq_bot_of_mulEquiv φ (Sec13.isPerfect_center_projSL p e he hq3).2
      · by_cases hq2 : 2 < p ^ e
        · exact Sec13.center_eq_bot_of_mulEquiv φ (Sec13.isPerfect_center_projSU p e he hq3 hq2).2
        · exfalso
          have h2 : p ^ e = 2 := by
            have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
            omega
          obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two hp.out h2
          have := Sec13.isSolvable_projSU_two
          have hsol : Group.IsSolvable (K ⧸ N) :=
            Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
          exact Group.IsPerfect.not_isSolvable _ hsol
    · exact Sec13.center_eq_bot_of_mulEquiv φ Sec13.isPerfect_center_alt7.2
    · exact Sec13.center_eq_bot_of_mulEquiv φ hM12z
    · exact Sec13.center_eq_bot_of_mulEquiv φ hM22z
    · exact Sec13.center_eq_bot_of_mulEquiv φ hJ2z
  obtain ⟨P, hPmap, hP9, hPN, hP⟩ := exists_e9_lift N hN3 hE' h9'
  refine ⟨P.map K.subtype, Subgroup.map_subtype_le P, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩ |> congrArg Subtype.val)
  · rintro _ ⟨a, ha, rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_pow, hP.2 a ha, Subgroup.coe_one]
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective K), hP9]
  · rintro _ ⟨x, hx, rfl⟩ hcomm
    have hxc : x ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (hcomm k k.2).symm
    have hxQ : QuotientGroup.mk' N x ∈ Subgroup.center (K ⧸ N) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hxc k]
    rw [hZQ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxQ
    have hx1 : x ∈ P ⊓ N := Subgroup.mem_inf.mpr ⟨hx, hxQ⟩
    rw [hPN, Subgroup.mem_bot] at hx1
    simp [hx1]

end Types

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
