module

public import CFSG.Quasithin.EmptyFaithful.S14610GT
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA0
public import CFSG.Quasithin.EmptyFaithful.S1469Eight
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.EmptyFaithful.T1531Cat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

private theorem mem_pCore_of_mem_pPrimeCore {D : Type} [Group D] [Finite D]
    (hQ : IsSylowTwoOf (Open.pCore 2 D) (CFSG.pPrimeCore 3 D)) {x : D}
    (hx : x ∈ CFSG.pPrimeCore 3 D) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ Open.pCore 2 D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (Open.pCore 2 D).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set ρ := QuotientGroup.mk' (Open.pCore 2 D)
  have hodd : ¬ 2 ∣ Nat.card ((CFSG.pPrimeCore 3 D).map ρ) := by
    rw [F6.card_map_mk]
    exact hQ.2.2
  have hρx : ρ x ∈ (CFSG.pPrimeCore 3 D).map ρ := ⟨x, hx, rfl⟩
  have h1 : orderOf (ρ x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
  have h2 : orderOf (ρ x) ∣ Nat.card ((CFSG.pPrimeCore 3 D).map ρ) :=
    Subgroup.orderOf_dvd_natCard _ hρx
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ((CFSG.pPrimeCore 3 D).map ρ)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h3 : orderOf (ρ x) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)

omit [Finite G] in
private theorem pCoreOf_subgroupOf_map {I X : Subgroup G} (hXI : X ≤ I) :
    (pCoreOf 2 (X.subgroupOf I)).map I.subtype = pCoreOf 2 X := by
  have h := map_pCore_mulEquiv 2 (Subgroup.subgroupOfEquivOfLe hXI)
  unfold pCoreOf
  rw [Subgroup.map_map, ← h, Subgroup.map_map]
  rfl

omit [Finite G] in
private theorem isElemAbelian_two_subgroupOf {I U : Subgroup G} (h : IsElemAbelian 2 U) :
    IsElemAbelian 2 (U.subgroupOf I) := CFSG.Open.IsElemAbelian.subgroupOf h I

private theorem isElemAbelian_two_map' {D E : Type*} [Group D] [Group E] {A : Subgroup D}
    (h : IsElemAbelian 2 A) (f : D →* E) : IsElemAbelian 2 (A.map f) :=
  CFSG.Open.IsElemAbelian.map h _

private theorem Setting146.left_14610 (S : Setting146 G T M) (hF618 : F6.TheoremF618Cat)
    {H : Subgroup G} {u : G} {I I₂ : Subgroup G} (c : Hyp14610 T M H u I I₂)
    (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hc2 : pCoreOf 2 (i1Of1469 T M I) ≠ pCoreOf 2 I₂) :
    ((i1Of1469 T M I).subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
        (I₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) =
      ((i1Of1469 T M I).subgroupOf I ⊓ I₂.subgroupOf I).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ∧
    IsGoldschmidtAmalgam
      (((i1Of1469 T M I).subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
      ((I₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ∧
    F6.F618ConclusionCat
      (((i1Of1469 T M I).subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
      ((I₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) := by
  have hSQ : IsSQTKTC I := S.isSQTKTC_of_pCoreOf_ne_bot c.hI.1.1.2
  rcases (S.isGoldschmidtTripleIn_14610 c hsyl hLT).f6_18Cat hF618 hSQ.2 hSQ.1 with
    ⟨h₁, h₂, -, h₄⟩ | ⟨h₁, h₂, -, -, -⟩
  · exact ⟨h₁, h₂, h₄⟩
  · exfalso
    apply hc2
    have hI₁ : i1Of1469 T M I ≤ I := i1Of1469_le T M I
    have hI₂ : I₂ ≤ I := c.gen ▸ le_sup_right
    rw [← pCoreOf_subgroupOf_map hI₁, ← pCoreOf_subgroupOf_map hI₂, h₁, h₂]

theorem Setting146.f618Cat_14610 (S : Setting146 G T M) (hF618 : F6.TheoremF618Cat)
    {H : Subgroup G} {u : G} {I I₂ : Subgroup G} (c : Hyp14610 T M H u I I₂)
    (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hc2 : pCoreOf 2 (i1Of1469 T M I) ≠ pCoreOf 2 I₂) :
    F6.F618ConclusionCat
      (((i1Of1469 T M I).subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
      ((I₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) :=
  (S.left_14610 hF618 c hsyl hLT hc2).2.2

theorem Setting146.facts14610_c4 (hF618 : F6.TheoremF618Cat) (i10 : Input14610Four)
    {H : Subgroup G} {u : G} {I I₂ : Subgroup G} (c : Hyp14610 T M H u I I₂)
    (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hc2 : pCoreOf 2 (i1Of1469 T M I) ≠ pCoreOf 2 I₂) : CharTwo I := by
  by_contra hchar
  have S := c.setting
  obtain ⟨hk1, hAm, hF⟩ := S.left_14610 hF618 c hsyl hLT hc2
  have hT := S.isGoldschmidtTripleIn_14610 c hsyl hLT
  have hI12 : i1Of1469 T M I ⊓ I₂ = T ⊓ I := S.i1_inf_i2 c hsyl hLT
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.hyp1281.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hO := S.oddCoreIn_eq_bot c.hH c.hu c.hI hsyl hzZ hz1'
  obtain ⟨K₀, hK₀⟩ := exists_isComponentIn_of_not_charTwo hO hchar
  have hzO : z ∉ pCoreOf 2 I :=
    S.not_mem_pCoreOf_of_isComponentIn c.hH c.hu c.hI hsyl hzZ hz1' hK₀
  have hzT : z ∈ T := S146T.Z_le hzZ
  have huQ : u ∈ pCoreOf 2 (mcOf T) := S.conjClosure_le_pCoreOf_mcOf c.hH c.hu.mem
  have hQ1T : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_mcOf_le
  have hzu : z ∈ tU T u := (S146T.mem_tU_iff).mpr ⟨hzT,
    commutatorElement_eq_one_iff_mul_comm.mpr (S146T.comm_Z_T (hQ1T huQ) hzZ).symm⟩
  have hzI : z ∈ I := c.hI.1.1.1 hzu
  have hzTI : z ∈ T ⊓ I := ⟨hzT, hzI⟩
  have hzsq : z ^ 2 = 1 := S146T.Z_sq hzZ
  have hQN : IsSylowTwoOf (Open.pCore 2 ↥I) (CFSG.pPrimeCore 3 ↥I) := hT.isSylowTwoOf_pCore_pPrimeCore
  have h2el : ∀ x ∈ CFSG.pPrimeCore 3 ↥I, x ^ 2 = 1 → x ∈ Open.pCore 2 ↥I := fun x hx hx2 =>
    mem_pCore_of_mem_pPrimeCore hQN hx (k := 1) (by simpa using hx2)
  have hzN : (⟨z, hzI⟩ : ↥I) ∉ CFSG.pPrimeCore 3 ↥I := fun hzN => hzO (by
    have h := h2el _ hzN (Subtype.ext (by simpa using hzsq))
    exact Subgroup.mem_map_of_mem I.subtype h)
  set U := conjClosure (VZ T M) H with hU
  have hUab : IsElemAbelian 2 U := S.lemma_14_5_15_two c.hH
  have hUT : U ≤ T := (S.conjClosure_le_pCoreOf c.hH).trans (S.pCoreOf_le_T c.hH)
  have hUu : U ≤ T ⊓ I := by
    intro a ha
    have hcomm : u * a = a * u :=
      congrArg Subtype.val (hUab.1.is_comm.comm (⟨u, c.hu.mem⟩ : U) ⟨a, ha⟩)
    exact ⟨hUT ha, c.hI.1.1.1 ((S146T.mem_tU_iff).mpr ⟨hUT ha,
      commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm⟩)⟩
  have hUI : U ≤ I := hUu.trans inf_le_right
  have hUI₂ : U ≤ I₂ := hUu.trans c.le_I₂
  have hrank : 4 ≤ mIdx U (pCoreOf 2 I) := c.hrank.trans (S.lemma_14_6_8 c.hH c.hu c.hI hsyl hchar)
  set N := CFSG.pPrimeCore 3 ↥I with hN
  set π := QuotientGroup.mk' N with hπ
  refine i10 (↥I ⧸ N) (((i1Of1469 T M I).subgroupOf I).map π) ((I₂.subgroupOf I).map π)
    (π ⟨z, hzI⟩) ((U.subgroupOf I).map π) hAm.toIsGoldschmidtTriple hF ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro h1
    exact hzN ((QuotientGroup.eq_one_iff _).mp h1)
  ·
    rw [← map_pow]
    have : (⟨z, hzI⟩ : ↥I) ^ 2 = 1 := Subtype.ext (by simpa using hzsq)
    rw [this, map_one]
  ·
    have hz12 : z ∈ i1Of1469 T M I ⊓ I₂ := hI12 ▸ hzTI
    exact ⟨Subgroup.mem_map_of_mem π hz12.1, Subgroup.mem_map_of_mem π hz12.2⟩
  ·
    intro t ht
    rw [hk1] at ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    have ht₀' : (t₀ : G) ∈ i1Of1469 T M I ⊓ I₂ := ⟨ht₀.1, ht₀.2⟩
    rw [hI12] at ht₀'
    have ht₀T : (t₀ : G) ∈ T := ht₀'.1
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (S146T.comm_Z_T ht₀T hzZ))
  ·
    intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rw [← map_mul, ← map_mul]
    refine congrArg π (Subtype.ext ?_)
    have hy₀G : (y₀ : G) ∈ mcOf T := S.le_mcOf c.hH (c.I₂_le hy₀)
    rw [S.mcOf_eq_centralizer hzZ hz1'] at hy₀G
    exact Subgroup.mem_centralizer_iff.mp hy₀G z rfl
  ·
    exact Subgroup.map_mono fun x hx => hUI₂ hx
  ·
    exact isElemAbelian_two_map' (isElemAbelian_two_subgroupOf hUab) π
  ·
    have h1 : I₂.subgroupOf I ≤ Subgroup.normalizer ((U.subgroupOf I : Subgroup ↥I) : Set ↥I) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have := Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure (VZ T M) H (c.I₂_le hy)) (x : G)
      simpa [Subgroup.mem_subgroupOf] using this
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map π)
  ·
    rw [F6.card_map_mk]
    set Ũ := U.subgroupOf I with hŨ
    have hrel : (pCoreOf 2 I).relIndex U = (Open.pCore 2 ↥I).relIndex Ũ := by
      have h := Subgroup.relIndex_map_map_of_injective (f := I.subtype) (Open.pCore 2 ↥I) Ũ
        I.subtype_injective
      rw [hŨ, Subgroup.map_subgroupOf_eq_of_le hUI] at h
      exact h
    have hle : N ⊓ Ũ ≤ Open.pCore 2 ↥I ⊓ Ũ := fun x hx =>
      ⟨h2el x hx.1 (Subtype.ext (hUab.2 (x : G) hx.2)), hx.2⟩
    have hdvd : (Open.pCore 2 ↥I).relIndex Ũ ∣ N.relIndex Ũ := by
      have := Subgroup.relIndex_dvd_of_le_left Ũ hle
      rwa [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at this
    have hpos : 0 < N.relIndex Ũ := by
      rw [← F6.card_map_mk Ũ N]
      exact Nat.card_pos
    have hv : 4 ≤ padicValNat 2 ((Open.pCore 2 ↥I).relIndex Ũ) := by
      rw [← hrel]
      exact hrank
    calc 2 ^ 4 ≤ 2 ^ padicValNat 2 ((Open.pCore 2 ↥I).relIndex Ũ) :=
          Nat.pow_le_pow_right (by norm_num) hv
      _ ≤ N.relIndex Ũ := Nat.le_of_dvd hpos (pow_padicValNat_dvd.trans hdvd)

end CFSG.Quasithin
