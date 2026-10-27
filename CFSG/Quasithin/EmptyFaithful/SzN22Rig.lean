module

public import CFSG.Quasithin.EmptyFaithful.SzN19Sel

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1549C
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace SzN22

section Generic

theorem inner_of_isPGroup_outer {N : Type} [Group N] (hN : IsPGroup 2 (Outer N)) {α : MulAut N}
    (h3 : α ^ 3 = 1) : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner N := by
  obtain ⟨k, hk⟩ := hN (QuotientGroup.mk α : Outer N)
  have h1 : (QuotientGroup.mk α : Outer N) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, h3]; rfl
  have hd1 : orderOf (QuotientGroup.mk α : Outer N) ∣ 3 := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf (QuotientGroup.mk α : Outer N) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h : orderOf (QuotientGroup.mk α : Outer N) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  rw [orderOf_eq_one_iff] at h
  exact (QuotientGroup.eq_one_iff α).mp h

theorem rig_of_isPGroup_outer {Ω : Type} [Group Ω] {K : Subgroup Ω} (hN : IsPGroup 2 (Outer ↥K))
    {z : Ω} (hzK : z ∈ Subgroup.normalizer (K : Set Ω)) (hz3 : z ^ 3 = 1) :
    ∃ x ∈ K, ∀ n ∈ K, z * n * z⁻¹ = x * n * x⁻¹ := by
  have hz3' : (⟨z, hzK⟩ : ↥(Subgroup.normalizer (K : Set Ω))) ^ 3 = 1 :=
    Subtype.ext (by simpa using hz3)
  have hα : (Subgroup.normalizerMonoidHom K ⟨z, hzK⟩) ^ 3 = 1 := by
    rw [← map_pow, hz3', map_one]
  obtain ⟨x, hx⟩ := inner_of_isPGroup_outer hN hα
  refine ⟨x, x.2, fun n hn => ?_⟩
  have := congrArg (fun φ : MulAut ↥K => ((φ ⟨n, hn⟩ : ↥K) : Ω)) hx
  simpa [MulAut.conj_apply] using this.symm

theorem isPGroup_outer_of_equiv {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (h : IsPGroup 2 (Outer H)) : IsPGroup 2 (Outer G) := by
  have : Finite (MulAut G) :=
    Finite.of_injective (fun f : MulAut G => (f : G → G)) DFunLike.coe_injective
  have : Finite (MulAut H) :=
    Finite.of_injective (fun f : MulAut H => (f : H → H)) DFunLike.coe_injective
  obtain ⟨m, hm⟩ := h.exists_card_eq
  exact IsPGroup.of_card (n := m)
    (by rw [CFSG.LieType.SteinbergBR.OddSylow.card_outer_congr e, hm])

end Generic

section Families

theorem isPGroup_outer_of_binary {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (e : X ≃* ↥(StatedSL n (ZMod 2))) : IsPGroup 2 (Outer X) := by
  let e' : X ≃* projectiveSL n (ZMod 2) :=
    e.trans ((specialLinearGroupEquivStatedSL n (ZMod 2)).symm.trans (SzN19.slEquivProjTwo n))
  exact isPGroup_outer_of_equiv e'
    (CFSG.LieType.SteinbergBR.BinaryLinear.binary_linear_key (k := ZMod 2) (n := n) hn
      (Nat.card_zmod 2)).2

theorem isPGroup_outer_of_alt6 {X : Type} [Group X] [Finite X] (h : IsAlt 6 X) :
    IsPGroup 2 (Outer X) := by
  obtain ⟨e⟩ := h
  exact isPGroup_outer_of_equiv e CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six

theorem isPGroup_outer_of_alt7 {X : Type} [Group X] [Finite X] (h : IsAlt 7 X) :
    IsPGroup 2 (Outer X) := by
  obtain ⟨e⟩ := h
  exact isPGroup_outer_of_equiv e CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_seven

section U33


theorem isPGroup_outer_u33G : IsPGroup 2 (Outer U33G) := by
  have hfin : Finite U33G := u33Pres_finite_card_le.1
  have hfinA : Finite (MulAut U33G) :=
    Finite.of_injective (fun f : MulAut U33G => (f : U33G → U33G)) DFunLike.coe_injective
  have hZ : Subgroup.center U33G = ⊥ := by
    refine u33Extra.eq_bot_of_normal _ inferInstance ?_
    refine u33Extra.syl.1.to_le ?_
    rw [← u33Extra.normalizer_T]
    exact Subgroup.center_le_normalizer _
  have hinj : Function.Injective (MulAut.conj : U33G →* MulAut U33G) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center U33G := Subgroup.mem_center_iff.2 fun x => by
      have h1 := congrArg (fun α : MulAut U33G => α x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc x * g = (g * x * g⁻¹) * g := by rw [h1]
        _ = g * x := by group
    rw [hZ] at hc
    exact hc
  have hin : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner U33G) = 6048 := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner,
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, card_u33Pres]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner U33G)
  rw [hin] at h1
  have h2 := card_mulAut_u33Pres_le
  have h3 : Nat.card (Outer U33G) * 6048 ≤ 12096 := by
    have h6 : Nat.card (Outer U33G) =
        Nat.card (MulAut U33G ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner U33G) := rfl
    rw [h6, ← h1]
    exact h2
  have h4 : 0 < Nat.card (Outer U33G) := Nat.card_pos
  have h5 : Nat.card (Outer U33G) = 1 ∨ Nat.card (Outer U33G) = 2 := by omega
  rcases h5 with h5 | h5
  · exact IsPGroup.of_card (n := 0) (by rw [h5]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [h5]; rfl)

end U33

theorem isPGroup_outer_of_g2two
    {X : Type} [Group X] [Finite X] (h : IsG2TwoDerived X) : IsPGroup 2 (Outer X) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  obtain ⟨g⟩ := CFSG.Quasithin.H13.nonempty_g2Two_commutator_equiv hF
  let e' : X ≃* U33G := e.trans (g.trans u33EquivSubG2.symm)
  have : Finite U33G := Finite.of_equiv X e'.toEquiv
  exact isPGroup_outer_of_equiv e' isPGroup_outer_u33G

end Families

section Rig

@[expose] def KRig {Ω : Type} [Group Ω] (K : Subgroup Ω) : Prop :=
  ∀ (S : Subgroup Ω) (z : Ω), IsSylowTwoOf S K → z ∈ Subgroup.normalizer (K : Set Ω) →
    z ∈ Subgroup.normalizer (S : Set Ω) → z ^ 3 = 1 →
    (∀ b ∈ Subgroup.normalizer (S : Set Ω) ⊓ K, orderOf b ≠ 3) →
    (∀ b ∈ Subgroup.normalizer (S : Set Ω) ⊓ K, z * b * z⁻¹ * b⁻¹ ∈ S) →
    ∃ x ∈ K, ∀ n ∈ K, z * n * z⁻¹ = x * n * x⁻¹

theorem mem_normalizer_of_central {Ω : Type} [Group Ω] {K S : Subgroup Ω} (hSK : S ≤ K) {b : Ω}
    (hb : ∀ k ∈ K, k * b = b * k) : b ∈ Subgroup.normalizer (S : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ∀ s ∈ S, b * s * b⁻¹ = s := fun s hs => by
    have := hb s (hSK hs)
    calc b * s * b⁻¹ = (s * b) * b⁻¹ := by rw [this]
      _ = s := by group
  constructor
  · intro hh
    rw [key h hh]
    exact hh
  · intro hh
    have h1 := key _ hh
    have e : b * h * b⁻¹ = h := by
      apply mul_left_cancel (a := b)
      calc b * (b * h * b⁻¹) = (b * (b * h * b⁻¹) * b⁻¹) * b := by group
        _ = (b * h * b⁻¹) * b := by rw [h1]
        _ = b * h := by group
    rw [e] at hh
    exact hh

theorem krig_of_hat {Ω : Type} [Group Ω] [Finite Ω] {K : Subgroup Ω}
    (h : IsHat ↥K ↥(alternatingGroup (Fin 6))) : KRig K := by
  intro S z hS _ _ _ hno _
  obtain ⟨-, hZ3, -⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥K)) 3 (by rw [hZ3])
  exfalso
  have hcK : ∀ k : ↥K, k * (c : ↥K) = (c : ↥K) * k := fun k => Subgroup.mem_center_iff.mp c.2 k
  have hb : ∀ k ∈ K, k * ((c : ↥K) : Ω) = ((c : ↥K) : Ω) * k := fun k hk => by
    have := congrArg Subtype.val (hcK ⟨k, hk⟩)
    simpa using this
  refine hno ((c : ↥K) : Ω) ⟨mem_normalizer_of_central hS.1 hb, (c : ↥K).2⟩ ?_
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]

theorem krig_of_listL
    {Ω : Type} [Group Ω] [Finite Ω] {K : Subgroup Ω} (hl : IsListL ↥K) : KRig K := by
  have key : IsPGroup 2 (Outer ↥K) → KRig K := fun hN _ z _ hzK _ hz3 _ _ =>
    rig_of_isPGroup_outer hN hzK hz3
  rcases hl with ⟨n, hn3, -, ⟨e⟩⟩ | h6 | hhat | h7 | hg2
  · exact key (isPGroup_outer_of_binary hn3 e)
  · exact key (isPGroup_outer_of_alt6 h6)
  · exact krig_of_hat hhat
  · exact key (isPGroup_outer_of_alt7 h7)
  · exact key (isPGroup_outer_of_g2two hg2)

end Rig

end SzN22

end CFSG.Quasithin
