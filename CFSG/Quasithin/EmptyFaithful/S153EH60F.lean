module

public import CFSG.Quasithin.EmptyFaithful.S153EH60E
public import CFSG.Quasithin.EmptyFaithful.S153EH60D
public import CFSG.Quasithin.EmptyFaithful.S153EInputs
public import CFSG.Quasithin.EmptyFaithful.S153E59F

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace S153EH60

theorem card_eq_three_of_sylow {Γ : Type*} [Group Γ] [Finite Γ] {P K : Subgroup Γ}
    (hP : IsSylowThreeOf153 P K) {k : ℕ} (hK : Nat.card K = 2 ^ k * 336) : Nat.card P = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hP.2.1.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card P K
  rw [inf_eq_left.mpr hP.1, hn, hK] at h1
  have h3 : ¬ 3 ∣ P.relIndex K := hP.2.2
  have hc : Nat.Coprime 3 (2 ^ k * 112) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num)) (by norm_num)
  have h2 : 2 ^ k * 336 = 3 * (2 ^ k * 112) := by ring
  rcases n with _ | _ | n
  · exfalso
    apply h3
    rw [pow_zero, mul_one] at h1
    rw [h1, h2]
    exact Dvd.intro _ rfl
  · simpa using hn
  · exfalso
    have h4 : 3 ^ 2 ∣ 3 * (2 ^ k * 112) := by
      rw [← h2, ← h1]
      exact Dvd.dvd.mul_left (pow_dvd_pow 3 (by omega)) _
    have h5 : 3 ∣ 2 ^ k * 112 := by
      have : 3 * 3 ∣ 3 * (2 ^ k * 112) := by simpa [pow_two] using h4
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have := Nat.Coprime.eq_one_of_dvd hc h5
    omega

theorem pow_eq_four_of_odd {i c e : ℕ} (hi : ¬ 2 ∣ i) (hc : ¬ 2 ∣ c) (h : i * 2 ^ e = 16 * c) :
    e = 4 := by
  rcases Nat.lt_trichotomy e 4 with he | he | he
  · exfalso
    interval_cases e <;> simp at h <;> omega
  · exact he
  · exfalso
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt he
    have : i * 2 ^ j * 32 = 16 * c := by rw [← h]; ring
    omega

theorem exists_sylow_card_sixteen {Γ : Type*} [Group Γ] [Finite Γ] {C : Subgroup Γ} {c : ℕ}
    (hc : Odd c) (hC : Nat.card C = 16 * c) :
    ∃ R : Subgroup Γ, IsSylowTwoOf R C ∧ Nat.card R = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : IsPGroup 2 (⊥ : Subgroup Γ) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨R, -, hRC, hRp, hRidx⟩ := S153E.exists_sylow_ge hbot (bot_le : (⊥ : Subgroup Γ) ≤ C)
  refine ⟨R, ⟨hRC, hRp, ?_⟩, ?_⟩
  · exact hRidx
  · obtain ⟨e, he⟩ := hRp.exists_card_eq
    have h1 := Subgroup.relIndex_mul_card R C
    rw [inf_eq_left.mpr hRC, he, hC] at h1
    have hc' : ¬ 2 ∣ c := by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr hc
    have := pow_eq_four_of_odd hRidx hc' h1
    rw [he, this]
    norm_num

end S153EH60

namespace S153E

open S153EH60

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem lemma_60H (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G}
    {s : ℕ} {y t₁ : G} (c : Chain15359 cx N₁ N₂ g s y t₁) {DH : Subgroup G}
    (hDH : IsSylowThreeOf153 DH Mc) :
    Nat.card DH = 3 ∧ ∃ R : Subgroup G, IsSylowTwoOf R (Mc ⊓ Subgroup.centralizer (DH : Set G)) ∧
      Nat.card R = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h58 : Concl15358 cx s := c.h58
  have hUQ : UH153 T M V₁ Mc = pCoreOf 2 Mc := c.h59.one
  let _ : CommGroup ↥(S153E59.UT T M V₁ Mc) := commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  obtain ⟨hHs, hKs, hidx, -, -, -⟩ := S153E59.hstarFacts cx h58 c.ht₁.1 c.ht₁.2
  obtain ⟨π, U₁, -, -, hdir, hnat, hdual⟩ := h58.three t₁ c.ht₁.1 c.ht₁.2
  set ρ := S153E59.rho cx with hρ
  have hfinAut : Finite (MulAut ↥(S153E59.UT T M V₁ Mc)) :=
    Finite.of_injective (fun f : MulAut ↥(S153E59.UT T M V₁ Mc) => (f : ↥(S153E59.UT T M V₁ Mc) →
      ↥(S153E59.UT T M V₁ Mc))) (fun f g h => MulEquiv.ext (congrFun h))
  have hcardMc : Nat.card ↥Mc = Nat.card ρ.ker * 336 := by
    have := Subgroup.card_ker_mul_card_range ρ
    rw [S153E59.range_rho cx, hHs] at this
    exact this.symm
  obtain ⟨k, hk⟩ := (isPGroup_ker_rho cx).exists_card_eq
  rw [hk] at hcardMc
  have hD3 : Nat.card DH = 3 := card_eq_three_of_sylow hDH hcardMc
  refine ⟨hD3, ?_⟩
  set D' : Subgroup ↥Mc := DH.subgroupOf Mc with hD'
  have hD'card : Nat.card D' = 3 := by
    rw [hD', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH.1).toEquiv]
    exact hD3
  have hD'p : IsPGroup 3 D' := hDH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hDH.1).symm
  have hD'3 : ∀ d ∈ D', d ^ 3 = 1 := by
    intro d hd
    have h := pow_card_eq_one' (x := (⟨d, hd⟩ : ↥D'))
    rw [hD'card] at h
    exact congrArg Subtype.val h
  obtain ⟨d₀, hd₀D', hd₀ne⟩ : ∃ d₀ ∈ D', d₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : D' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.mpr (hcon x hx)
    rw [this, Subgroup.card_bot] at hD'card
    omega
  have hd₀3 : orderOf d₀ = 3 := orderOf_eq_prime (hD'3 d₀ hd₀D') hd₀ne
  have hDz : D' = Subgroup.zpowers d₀ := by
    symm
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hd₀D')
    rw [hD'card, Nat.card_zpowers, hd₀3]
  set a : MulAut ↥(S153E59.UT T M V₁ Mc) := ρ d₀ with ha
  have hker_bot : ρ.ker ⊓ D' = ⊥ := inf_eq_bot_of_isPGroup _ _ (isPGroup_ker_rho cx) hD'p
  have hρd₀ne : ρ d₀ ≠ 1 := by
    intro h
    have : d₀ ∈ ρ.ker ⊓ D' := ⟨MonoidHom.mem_ker.mpr h, hd₀D'⟩
    rw [hker_bot, Subgroup.mem_bot] at this
    exact hd₀ne this
  have ha3 : orderOf a = 3 := by
    refine orderOf_eq_prime ?_ hρd₀ne
    rw [ha, ← map_pow, hD'3 d₀ hd₀D', map_one]
  have haH : a ∈ HStar153 T M V₁ Mc := by
    rw [← S153E59.range_rho cx]
    exact ⟨d₀, rfl⟩
  have haK : a ∈ oTwoUpper (HStar153 T M V₁ Mc) :=
    mem_oTwoUpper_of_odd haH (by rw [ha3]; exact ⟨1, by norm_num⟩)
  have hπ : Function.Bijective π :=
    Function.Surjective.bijective_of_nat_card_le (α := L32) hnat.1
      (by rw [S153E59.card_statedSL_three_two, hKs])
  have hmap : D'.map ρ = Subgroup.zpowers a := by rw [hDz, MonoidHom.map_zpowers]
  have hcent := card_centralizer_eq ρ D' hD'p (isPGroup_ker_rho cx)
  have hU := card_ker_inf_centralizer cx hUQ hD'3
  have hfix4 : Nat.card {w : ↥(S153E59.UT T M V₁ Mc) // ∀ d ∈ D', ρ d w = w} = 4 := by
    have e : {w : ↥(S153E59.UT T M V₁ Mc) // ∀ d ∈ D', ρ d w = w} ≃ ↥(fixV (D'.map ρ)) :=
      Equiv.subtypeEquivRight fun w => by
        rw [mem_fixV]
        constructor
        · rintro h x ⟨d, hd, rfl⟩
          exact h d hd
        · intro h d hd
          exact h _ ⟨d, hd, rfl⟩
    rw [Nat.card_congr e, hmap]
    exact card_fixV_zpowers_eq_four hπ hdir.1 hdir.2 hnat hdual haK ha3
  obtain ⟨c', hc'odd, hc'⟩ := card_inf_centralizer (oTwoUpper_le (HStar153 T M V₁ Mc)) hidx hKs π hπ
    haK ha3
  have hcentstar : Nat.card ↥(Subgroup.centralizer ((D'.map ρ : Subgroup _) : Set _) ⊓ ρ.range) =
      2 * c' := by
    rw [hmap, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, S153E59.range_rho cx, inf_comm]
    exact hc'
  have hcard16 : Nat.card ↥(Subgroup.centralizer (D' : Set ↥Mc)) = 16 * c' := by
    rw [hcent, hU, hfix4, hcentstar]
    ring
  have hsub : (Mc ⊓ Subgroup.centralizer (DH : Set G)).subgroupOf Mc =
      Subgroup.centralizer (D' : Set ↥Mc) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hx⟩ d hd
      exact Subtype.ext (hx (d : G) hd)
    · intro hx
      refine ⟨x.2, fun h hh => ?_⟩
      exact congrArg Subtype.val (hx ⟨h, hDH.1 hh⟩ hh)
  have hcardC : Nat.card ↥(Mc ⊓ Subgroup.centralizer (DH : Set G)) = 16 * c' := by
    have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : Mc ⊓ Subgroup.centralizer (DH : Set G) ≤ Mc)).toEquiv
    rw [hsub, hcard16] at this
    exact this.symm
  exact exists_sylow_card_sixteen hc'odd hcardC

end S153E

end CFSG.Quasithin
