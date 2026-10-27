module

public import CFSG.RankThree.PartOne.S12.Sec15Lemmas
public import CFSG.RankThree.PartOne.S12.Sec1322Reflect

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

@[expose] def KF155Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ P : Subgroup G, IsSylowOf p P (torusNormalizer E) → Sylow155 p A E P

namespace Sec155

variable {G : Type} [Group G]

theorem mem_sup_of_commute {M : Type*} [Group M] {S T : Subgroup M}
    (hc : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) {x : M} (hx : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, s * t = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ s ∈ S, ∃ t ∈ T, s * t = x) ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, T.one_mem, mul_one x⟩
    · exact ⟨1, S.one_mem, x, hx, one_mul x⟩
  · exact ⟨1, S.one_mem, 1, T.one_mem, one_mul 1⟩
  · rintro x y - - ⟨s, hs, t, ht, rfl⟩ ⟨s', hs', t', ht', rfl⟩
    refine ⟨s * s', S.mul_mem hs hs', t * t', T.mul_mem ht ht', ?_⟩
    calc s * s' * (t * t') = s * (s' * t) * t' := by group
      _ = s * (t * s') * t' := by rw [hc s' hs' t ht]
      _ = s * t * (s' * t') := by group
  · rintro x - ⟨s, hs, t, ht, rfl⟩
    refine ⟨s⁻¹, S.inv_mem hs, t⁻¹, T.inv_mem ht, ?_⟩
    have h1 : s⁻¹ * t⁻¹ = t⁻¹ * s⁻¹ := by
      calc s⁻¹ * t⁻¹ = (t * s)⁻¹ := by group
        _ = (s * t)⁻¹ := by rw [hc s hs t ht]
        _ = t⁻¹ * s⁻¹ := by group
    rw [h1]
    group

theorem scalar_pElement {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : ∀ e : E, e ^ p = 1) {k : ℤ}
    {z : MulAut E} (hk : ∀ e : E, z e = e ^ k) {a : ℕ} (hz : z ^ (p ^ a) = 1) : z = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hpow : ∀ (n : ℕ) (e : E), (z ^ n) e = e ^ (k ^ n) := by
    intro n
    induction n with
    | zero => intro e; simp
    | succ n ih =>
      intro e
      rw [pow_succ', MulAut.mul_apply, ih, map_zpow, hk, ← zpow_mul, ← pow_succ']
  have hmod : k ^ (p ^ a) ≡ k [ZMOD p] := by
    have h1 : ((k ^ (p ^ a) : ℤ) : ZMod p) = (k : ZMod p) := by
      push_cast
      exact ZMod.pow_card_pow (k : ZMod p)
    exact (ZMod.intCast_eq_intCast_iff _ _ _).1 h1
  refine MulEquiv.ext fun e => ?_
  have h1 : (z ^ (p ^ a)) e = e := by rw [hz]; rfl
  rw [hpow] at h1
  have h2 : e ^ (k ^ (p ^ a)) = e ^ k := by
    rw [zpow_eq_zpow_iff_modEq]
    exact Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one (hE e))) hmod
  rw [h2] at h1
  show z e = (1 : MulAut E) e
  rw [hk, h1]
  rfl

theorem pElement_trivial {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : ∀ e : E, e ^ p = 1)
    {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀) (hle : reflectionGroup p E ≤ torusWeyl E)
    (hX : ¬ p ∣ Nat.card ↥(reflectionGroup p E)) :
    ∀ g ∈ torusWeyl E, ∀ a : ℕ, g ^ (p ^ a) = 1 → g = 1 := by
  obtain ⟨-, hW₀X, -, hsup, hinf, hscal⟩ := hW
  intro g hg a hga
  have hg' : g ∈ (Subgroup.center ↥(torusWeyl E)).map (torusWeyl E).subtype ⊔ W₀ := by
    rw [← hsup]
    exact hg
  have hcomm : ∀ s ∈ (Subgroup.center ↥(torusWeyl E)).map (torusWeyl E).subtype, ∀ t ∈ W₀,
      s * t = t * s := by
    rintro _ ⟨z, hz, rfl⟩ t ht
    have htW : t ∈ torusWeyl E := hle (hW₀X ht)
    have := Subgroup.mem_center_iff.1 hz ⟨t, htW⟩
    exact (congrArg Subtype.val this).symm
  obtain ⟨s, hs, t, ht, rfl⟩ := mem_sup_of_commute hcomm hg'
  have hst : Commute s t := hcomm s hs t ht
  rw [hst.mul_pow] at hga
  have hs' : s ^ (p ^ a) ∈ (Subgroup.center ↥(torusWeyl E)).map (torusWeyl E).subtype :=
    Subgroup.pow_mem _ hs _
  have ht' : t ^ (p ^ a) ∈ W₀ := Subgroup.pow_mem _ ht _
  have heq : s ^ (p ^ a) = (t ^ (p ^ a))⁻¹ := eq_inv_of_mul_eq_one_left hga
  have hmem : s ^ (p ^ a) ∈ (Subgroup.center ↥(torusWeyl E)).map (torusWeyl E).subtype ⊓ W₀ :=
    ⟨hs', by rw [heq]; exact W₀.inv_mem ht'⟩
  rw [hinf] at hmem
  have hs1 : s ^ (p ^ a) = 1 := Subgroup.mem_bot.1 hmem
  have ht1 : t ^ (p ^ a) = 1 := by
    rw [hs1, one_mul] at hga
    exact hga
  have hs0 : s = 1 := by
    obtain ⟨z, hz, rfl⟩ := hs
    obtain ⟨k, hk⟩ := hscal z hz
    exact scalar_pElement hp hE hk hs1
  have ht0 : t = 1 := by
    set t' : ↥(reflectionGroup p E) := ⟨t, hW₀X ht⟩ with ht'def
    have h1 : orderOf t ∣ p ^ a := orderOf_dvd_of_pow_eq_one ht1
    have h2 : orderOf t ∣ Nat.card ↥(reflectionGroup p E) := by
      have := orderOf_dvd_natCard t'
      rwa [ht'def, Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (p ^ a) (Nat.card ↥(reflectionGroup p E)) :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hX)
    have h3 := Nat.dvd_gcd h1 h2
    rw [hcop] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  rw [hs0, ht0, one_mul]

theorem omegaOne_eq [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hEA : E = A) {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀)
    (hX : ¬ p ∣ Nat.card ↥(reflectionGroup p E)) {P : Subgroup G}
    (hP : IsSylowOf p P (torusNormalizer E)) : omegaOne p P = E := by
  obtain ⟨hPW, hPp, hidx⟩ := hP
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hEel := h.E_elem
  have hE : ∀ e : E, e ^ p = 1 := fun e =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p E) e
  have hptriv := pElement_trivial hp hE hW (Sec1322.reflectionGroup_le E) hX
  have hPcent : ∀ x ∈ P, ∀ e ∈ E, x * e = e * x := by
    intro x hx e he
    have hxN : x ∈ Subgroup.normalizer (E : Set G) := hPW hx
    obtain ⟨a, ha⟩ := hPp ⟨x, hx⟩
    have hxa : x ^ (p ^ a) = 1 := congrArg Subtype.val ha
    have hg : conjAut E x hxN ∈ torusWeyl E := ⟨⟨x, hxN⟩, rfl⟩
    have h1 : (conjAut E x hxN) ^ (p ^ a) = 1 := by
      unfold conjAut
      rw [← map_pow]
      have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ (p ^ a) = 1 := Subtype.ext hxa
      rw [this, map_one]
    have h2 := hptriv _ hg a h1
    have h3 := Equivariance.coe_conjAut hxN ⟨e, he⟩
    rw [h2] at h3
    have h4 : e = x * e * x⁻¹ := h3
    rw [eq_mul_inv_iff_mul_eq] at h4
    exact h4.symm
  have hEP : E ≤ P := by
    have hEW : E ≤ torusNormalizer E := Subgroup.le_normalizer
    have hPp' : IsPGroup p (P.subgroupOf (torusNormalizer E)) :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPW).symm
    have hidx' : ¬ p ∣ (P.subgroupOf (torusNormalizer E)).index := hidx
    have hEp : IsPGroup p (E.subgroupOf (torusNormalizer E)) :=
      (IsElementaryAbelian.isPGroup p E).of_equiv (Subgroup.subgroupOfEquivOfLe hEW).symm
    have hnorm : (E.subgroupOf (torusNormalizer E)).Normal :=
      ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact (Subgroup.mem_normalizer_iff.1 g.2 n).1 hn⟩
    have hle := hEp.le_sylow_of_normal (hPp'.toSylow hidx')
    intro e he
    have h1 : (⟨e, hEW he⟩ : ↥(torusNormalizer E)) ∈ E.subgroupOf (torusNormalizer E) := he
    have h2 := (IsPGroup.mem_toSylow hPp' hidx').1 (hle h1)
    exact Subgroup.mem_subgroupOf.1 h2
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxP, hxp⟩
    have hz : IsElementaryAbelian p (Subgroup.zpowers x) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hxp
    have hcent : Subgroup.zpowers x ≤ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro e he
      exact (hPcent x hxP e he).symm
    have hsup := IsElementaryAbelian.sup_of_le_centralizer (p := p) hcent
    have hF : E ⊔ Subgroup.zpowers x = E := by
      refine h.E_max _ hsup ?_ le_sup_left
      refine sup_le h.E_le ?_
      rw [← hEA]
      exact hcent
    have hmem : x ∈ E ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rwa [hF] at hmem
  · intro e he
    exact Subgroup.subset_closure ⟨hEP he, elemPow_eq_one_of_isElementaryAbelian e he⟩

theorem not_dvd_24 {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : ¬ p ∣ 24 := by
  intro hd
  have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [h24] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow hp h)
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

theorem not_dvd_48 {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : ¬ p ∣ 48 := by
  intro hd
  have h48 : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
  rw [h48] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow hp h)
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

theorem card_perm4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

theorem card_gp : Nat.card (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) = 48 := by
  rw [Nat.card_prod, card_perm4]
  have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [this]

end Sec155

theorem node155_of_node154 (h154 : Node154) (hFive : KF155Five) : Node155 := by
  intro G _ _ p A c L E h hF12 hout P hP
  by_cases hT : Outcome152Five p E A (lieGenerated p E)
  · exact hFive G p A c L E h hF12 hT P hP
  · left
    obtain ⟨W₀, hW⟩ := h154 G p A c L E h hF12 hout
    have hp := h.h12.prime
    have h3 := h.h12.three_lt
    rcases hout with ⟨f, -, -, -, ⟨eX⟩, hEA, -⟩ | ⟨f, -, -, -, ⟨eX⟩, hEA, -⟩ |
        ⟨f, -, -, -, ⟨eX⟩, hEA, -⟩ | ⟨f, -, -, -, ⟨eX⟩, hEA, -⟩ | h5
    · exact Sec155.omegaOne_eq h.h12 hEA hW
        (by rw [Nat.card_congr eX.toEquiv, Sec155.card_perm4]; exact Sec155.not_dvd_24 hp h3) hP
    · exact Sec155.omegaOne_eq h.h12 hEA hW
        (by rw [Nat.card_congr eX.toEquiv, Sec155.card_gp]; exact Sec155.not_dvd_48 hp h3) hP
    · exact Sec155.omegaOne_eq h.h12 hEA hW
        (by rw [Nat.card_congr eX.toEquiv, Sec155.card_gp]; exact Sec155.not_dvd_48 hp h3) hP
    · exact Sec155.omegaOne_eq h.h12 hEA hW
        (by rw [Nat.card_congr eX.toEquiv, Sec155.card_gp]; exact Sec155.not_dvd_48 hp h3) hP
    · exact absurd h5 hT

end CFSG.RankThree.PartOne
