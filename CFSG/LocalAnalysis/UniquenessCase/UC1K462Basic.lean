module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open scoped MatrixGroups

section Pieces

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Finite V] {ρ : Representation (ZMod p) G V} {D : Subgroup G}

theorem fixV_ne_bot_of_pGroup [Nontrivial V] {A : Subgroup G} (hA : IsPGroup p A) :
    fixV ρ A ≠ ⊥ := by
  classical
  letI : MulAction A V :=
    { smul := fun a v => ρ a v
      one_smul := fun v => by
        show ρ (1 : A) v = v
        simp
      mul_smul := fun a b v => by
        show ρ ((a * b : A) : G) v = ρ a (ρ b v)
        simp }
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hcard : p ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    exact dvd_pow_self p (Module.finrank_pos (R := ZMod p) (M := V)).ne'
  have h0 : (0 : V) ∈ MulAction.fixedPoints A V := by
    rw [MulAction.mem_fixedPoints]
    intro a
    show ρ a 0 = 0
    simp
  obtain ⟨b, hb, hb0⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hcard h0
  intro hbot
  have hbmem : b ∈ fixV ρ A := fun a ha => by
    have := (MulAction.mem_fixedPoints.1 hb) ⟨a, ha⟩
    exact this
  rw [hbot] at hbmem
  exact hb0 (by simpa using hbmem.symm)

theorem p_ne_three (h : Hyp45 p G V ρ D) : p ≠ 3 := by
  intro hp3
  haveI := h.irred
  haveI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) G) ρ.asModule
  have hD3 : IsPGroup p D := by
    apply IsPGroup.of_card (n := 1)
    rw [h.card_three, hp3]; norm_num
  exact fixV_ne_bot_of_pGroup (ρ := ρ) hD3 h.fix

theorem no_abelian_two (hK42 : K42) (h : Hyp45 p G V ρ D) (A : Subgroup G) (hA2 : IsPGroup 2 A)
    (hAab : IsMulCommutative ↥A) (hA0 : A ≠ ⊥) (hN : D ≤ Subgroup.normalizer (A : Set G))
    (hDA : ⁅D, A⁆ = A) : False := by
  have h3 : p ≠ 3 := p_ne_three h
  have h2 : 2 ≠ p := by have := h.odd; omega
  exact (hK42 p (Fact.out) G h.kgroup V ρ h.faithful 2 3 Nat.prime_two Nat.prime_three h2
    (Ne.symm h3) (by norm_num) D h.card_three h.fix A hA2 hA0 hN hDA).1 hAab

theorem uc45_Op (h : Hyp45 p G V ρ D) : CFSG.pCore p G = ⊥ := by
  classical
  haveI := h.irred
  haveI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) G) ρ.asModule
  have hfix : fixV ρ (CFSG.pCore p G) ≠ ⊥ := fixV_ne_bot_of_pGroup (CFSG.pCore_isPGroup)
  let R : Subrepresentation ρ :=
    ⟨fixV ρ (CFSG.pCore p G), fun g v hv n hn => by
      have hn' : g⁻¹ * n * g ∈ CFSG.pCore p G := by
        have := (CFSG.pCore_normal (p := p) (G := G)).conj_mem n hn g⁻¹
        simpa using this
      have h1 : ρ n (ρ g v) = ρ g (ρ (g⁻¹ * n * g) v) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group
      rw [h1, hv _ hn']⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top R with hbot | htop
  · exact absurd (congrArg Subrepresentation.toSubmodule hbot) (by
      intro h0
      exact hfix h0)
  · have htop' : fixV ρ (CFSG.pCore p G) = ⊤ := congrArg Subrepresentation.toSubmodule htop
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    apply h.faithful
    rw [map_one]
    ext v
    have hv : v ∈ fixV ρ (CFSG.pCore p G) := by rw [htop']; trivial
    exact hv n hn

theorem uc45_center (h : Hyp45 p G V ρ D) : IsCyclic (Subgroup.center G) := by
  haveI := h.irred
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  exact CFSG.center_cyclic_of_representation_faithful_irreducible ρ h.faithful

end Pieces

theorem three_dvd_two_pow_sub_one {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  have := Nat.pow_sub_one_dvd_pow_sub_one 2 (even_iff_two_dvd.1 hn)
  simpa using this

theorem sl2_involution_eq_neg_one {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    {u : SL(2, F)} (hu : u ^ 2 = 1) (hu1 : u ≠ 1) :
    (u : Matrix (Fin 2) (Fin 2) F) = -1 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hchar : (2 : F) ≠ 0 := by
    intro h2
    haveI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    obtain ⟨k, hk⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, hk.2] at hF
    have : Even (2 ^ (k : ℕ)) := (Nat.even_pow.2 ⟨even_two, k.ne_zero⟩)
    exact (Nat.not_even_iff_odd.2 hF) this
  have hM2 : (u : Matrix (Fin 2) (Fin 2) F) * (u : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) hu
    simpa [pow_two] using this
  have hdet := u.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hM2 0) 0
  have e01 := congrFun (congrFun hM2 0) 1
  have e10 := congrFun (congrFun hM2 1) 0
  have e11 := congrFun (congrFun hM2 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
    Fin.zero_eta, Fin.mk_one, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true] at e00 e01 e10 e11
  set a := (u : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (u : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (u : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (u : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  by_cases had : a + d = 0
  · exfalso
    have hd' : d = -a := by linear_combination had
    rw [hd'] at hdet
    apply hchar
    linear_combination -hdet - e00
  · have hb0 : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right had
    have hc0 : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right had
    have haa : a * a = 1 := by rw [hb0, hc0] at e00; linear_combination e00
    have hdd : a * d = 1 := by rw [hb0, hc0] at hdet; linear_combination hdet
    have hda : d = a := by
      have h1 : a * (d - a) = 0 := by linear_combination hdd - haa
      have ha0 : a ≠ 0 := fun h0 => by rw [h0] at haa; simp at haa
      have := (mul_eq_zero.1 h1).resolve_left ha0
      linear_combination this
    rcases mul_self_eq_one_iff.1 haa with ha1 | ha1
    · exfalso
      apply hu1
      apply Subtype.ext
      apply Matrix.ext
      simp only [Fin.forall_fin_two]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · simpa [ha1] using ha.symm
      · simpa [hb0] using hb.symm
      · simpa [hc0] using hc.symm
      · simpa [hda, ha1] using hd.symm
    · apply Matrix.ext
      simp only [Fin.forall_fin_two]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · simpa [ha1] using ha.symm
      · simpa [hb0] using hb.symm
      · simpa [hc0] using hc.symm
      · simpa [hda, ha1] using hd.symm

section Central

variable {G : Type} [Group G]

theorem central_involution_neg {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ρ : Representation (ZMod p) G V) (hρ : Function.Injective ρ)
    [ρ.IsIrreducible] {z : G} (hz : z ∈ Subgroup.center G) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    ∀ v : V, ρ z v = -v := by
  obtain ⟨n, hn⟩ : ∃ n : Module.End (ZMod p) V, n = ρ z - 1 := ⟨_, rfl⟩
  have hzz : ρ z * ρ z = 1 := by rw [← map_mul, ← sq, hz2, map_one]
  have hcomm : ∀ (g : G) (v : V), n (ρ g v) = ρ g (n v) := by
    intro g v
    have h1 : ρ z * ρ g = ρ g * ρ z := by
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz g).symm]
    have := congrArg (fun f : Module.End (ZMod p) V => f v) h1
    rw [hn]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    simp only [Module.End.mul_apply] at this
    rw [this]
  let f : Representation.IntertwiningMap ρ ρ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ n hcomm
  have hfn : ∀ v, f v = n v := fun v => rfl
  rcases Representation.IsIrreducible.injective_or_eq_zero f with hinj | h0
  · intro v
    have h1 : n (ρ z v + v) = 0 := by
      have := congrArg (fun g : Module.End (ZMod p) V => g v) hzz
      simp only [Module.End.mul_apply, Module.End.one_apply] at this
      rw [hn]
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_add, this]
      abel
    have h2 : ρ z v + v = 0 := by
      apply hinj
      show f (ρ z v + v) = f 0
      rw [hfn, map_zero]
      exact h1
    exact eq_neg_of_add_eq_zero_left h2
  · exfalso
    apply hz1
    apply hρ
    rw [map_one]
    ext v
    have h3 : f v = 0 := by rw [h0]; rfl
    rw [hfn, hn] at h3
    simpa [sub_eq_zero] using h3

end Central

theorem sl2_semiregular {p : ℕ} [Fact p.Prime] (hp : 2 < p) {G : Type} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F)) (φ : G ≃* SL(2, F))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) G V) (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible)
    (hodd : ∀ (r : ℕ) (A : Subgroup G), r.Prime → r ≠ 2 → Nat.card A = r → fixV ρ A = ⊥) :
    ∀ g : G, g ≠ 1 → ∀ v : V, ρ g v = v → v = 0 := by
  haveI := hirr
  intro g hg v hv
  have hpow : ∀ n : ℕ, ρ (g ^ n) v = v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, hv, ih]
  have hm0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hm1 : orderOf g ≠ 1 := fun h => hg (orderOf_eq_one_iff.1 h)
  by_cases h2 : 2 ∣ orderOf g
  · have hu_ord : orderOf (g ^ (orderOf g / 2)) = 2 := orderOf_pow_orderOf_div hm0 h2
    have hu2 : (g ^ (orderOf g / 2)) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (g ^ (orderOf g / 2))
      rwa [hu_ord] at this
    have hu1 : g ^ (orderOf g / 2) ≠ 1 := by
      intro h; rw [h, orderOf_one] at hu_ord; omega
    have hφ2 : (φ (g ^ (orderOf g / 2))) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
    have hφ1 : φ (g ^ (orderOf g / 2)) ≠ 1 := fun h => hu1 (φ.injective (by rw [h, map_one]))
    have hmat := sl2_involution_eq_neg_one hF hφ2 hφ1
    have hucent : g ^ (orderOf g / 2) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply φ.injective
      rw [map_mul, map_mul]
      apply Subtype.ext
      show (φ x : Matrix (Fin 2) (Fin 2) F) * (φ (g ^ (orderOf g / 2)) : Matrix (Fin 2) (Fin 2) F)
        = (φ (g ^ (orderOf g / 2)) : Matrix (Fin 2) (Fin 2) F) * (φ x : Matrix (Fin 2) (Fin 2) F)
      rw [hmat]; simp
    have hneg := central_involution_neg ρ hρ hucent hu2 hu1 v
    have hfix := hpow (orderOf g / 2)
    have hv2 : (2 : ZMod p) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hfix]
      rw [hneg]
      simp
    have h20 : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
    exact (smul_eq_zero.1 hv2).resolve_left h20
  · have hr := Nat.minFac_prime hm1
    have hrd : (orderOf g).minFac ∣ orderOf g := Nat.minFac_dvd _
    have hr2 : (orderOf g).minFac ≠ 2 := fun h => h2 (h ▸ hrd)
    have hh_ord : orderOf (g ^ (orderOf g / (orderOf g).minFac)) = (orderOf g).minFac :=
      orderOf_pow_orderOf_div hm0 hrd
    have hcard : Nat.card (Subgroup.zpowers (g ^ (orderOf g / (orderOf g).minFac))) =
        (orderOf g).minFac := by rw [Nat.card_zpowers, hh_ord]
    have hbot := hodd _ _ hr hr2 hcard
    have hvmem : v ∈ fixV ρ (Subgroup.zpowers (g ^ (orderOf g / (orderOf g).minFac))) := by
      intro a ha
      rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at ha
      obtain ⟨k, rfl⟩ := ha
      rw [← pow_mul]
      exact hpow _
    rw [hbot] at hvmem
    simpa using hvmem

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
