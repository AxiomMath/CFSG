module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.Quasithin

namespace S1422Loc

open MulAction

section Odd5

theorem perm5_pow15 : ∀ w : Equiv.Perm (Fin 5), w ^ 15 = 1 → w ^ 3 = 1 ∨ w ^ 5 = 1 := by
  decide +kernel

theorem perm5_words : ∀ σ τ : Equiv.Perm (Fin 5), σ ^ 5 = 1 → σ ≠ 1 → τ ^ 3 = 1 → τ ≠ 1 →
    ((σ * τ) ^ 3 ≠ 1 ∧ (σ * τ) ^ 5 ≠ 1) ∨ ((σ * τ⁻¹) ^ 3 ≠ 1 ∧ (σ * τ⁻¹) ^ 5 ≠ 1) ∨
    ((σ ^ 2 * τ) ^ 3 ≠ 1 ∧ (σ ^ 2 * τ) ^ 5 ≠ 1) ∨ ((σ ^ 2 * τ⁻¹) ^ 3 ≠ 1 ∧ (σ ^ 2 * τ⁻¹) ^ 5 ≠ 1) := by
  decide +kernel

theorem card_eq_five_of_odd_transitive_fin (N' : Subgroup (Equiv.Perm (Fin 5)))
    (hodd : Odd (Nat.card N')) (htrans : ∀ i j : Fin 5, ∃ g ∈ N', g i = j) : Nat.card N' = 5 := by
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  have hdvd : Nat.card N' ∣ 120 := h120 ▸ Subgroup.card_subgroup_dvd_card N'
  have h5 : 5 ∣ Nat.card N' := by
    have horb : MulAction.orbit N' (0 : Fin 5) = Set.univ := by
      ext j
      simp only [Set.mem_univ, iff_true]
      obtain ⟨g, hg, hgj⟩ := htrans 0 j
      exact ⟨⟨g, hg⟩, hgj⟩
    have := Subgroup.card_mul_index (MulAction.stabilizer N' (0 : Fin 5))
    rw [MulAction.index_stabilizer, horb, Set.ncard_univ] at this
    have hc5 : Nat.card (Fin 5) = 5 := by simp
    rw [hc5] at this
    exact ⟨Nat.card (MulAction.stabilizer N' (0 : Fin 5)), by rw [← this]; ring⟩
  have h15 : Nat.card N' ∣ 15 := by
    have hcop : Nat.Coprime (Nat.card N') 8 := by
      have h2 : Nat.Coprime 2 (Nat.card N') := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (by rcases hodd with ⟨k, hk⟩; omega)
      have := Nat.Coprime.pow_left 3 h2
      simpa using this.symm
    have : Nat.card N' ∣ 15 * 8 := by simpa using hdvd
    exact hcop.dvd_of_dvd_mul_right this
  by_contra hne
  have h15' : Nat.card N' = 15 := by
    have : Nat.card N' ∈ Nat.divisors 15 := by simp [h15]
    have hd : Nat.divisors 15 = {1, 3, 5, 15} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hp5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := N') 5 (by rw [h15']; norm_num)
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' (G := N') 3 (by rw [h15']; norm_num)
  have hall : ∀ w : N', (w : Equiv.Perm (Fin 5)) ^ 3 = 1 ∨ (w : Equiv.Perm (Fin 5)) ^ 5 = 1 := by
    intro w
    apply perm5_pow15
    have := pow_card_eq_one' (G := N') (x := w)
    rw [h15'] at this
    exact congrArg Subtype.val this
  have hs5 : (σ : Equiv.Perm (Fin 5)) ^ 5 = 1 := by
    have := pow_orderOf_eq_one σ; rw [hσ] at this; exact congrArg Subtype.val this
  have hs1 : (σ : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro h; have : σ = 1 := Subtype.ext h; rw [this, orderOf_one] at hσ; omega
  have ht3 : (τ : Equiv.Perm (Fin 5)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one τ; rw [hτ] at this; exact congrArg Subtype.val this
  have ht1 : (τ : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro h; have : τ = 1 := Subtype.ext h; rw [this, orderOf_one] at hτ; omega
  have key := perm5_words σ τ hs5 hs1 ht3 ht1
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hall (σ * τ) with h | h
    · exact h1 (by simpa using h)
    · exact h2 (by simpa using h)
  · rcases hall (σ * τ⁻¹) with h | h
    · exact h1 (by simpa using h)
    · exact h2 (by simpa using h)
  · rcases hall (σ ^ 2 * τ) with h | h
    · exact h1 (by simpa using h)
    · exact h2 (by simpa using h)
  · rcases hall (σ ^ 2 * τ⁻¹) with h | h
    · exact h1 (by simpa using h)
    · exact h2 (by simpa using h)

theorem card_eq_five_of_odd_transitive {X : Type*} [Finite X] (hX : Nat.card X = 5)
    (N' : Subgroup (Equiv.Perm X)) (hodd : Odd (Nat.card N'))
    (htrans : ∀ i j : X, ∃ g ∈ N', g i = j) : Nat.card N' = 5 := by
  let e : X ≃ Fin 5 := Finite.equivFinOfCardEq hX
  let ε : Equiv.Perm X ≃* Equiv.Perm (Fin 5) := Equiv.permCongrHom e
  have hcard : Nat.card (N'.map ε.toMonoidHom) = Nat.card N' :=
    Subgroup.card_map_of_injective ε.injective
  have := card_eq_five_of_odd_transitive_fin (N'.map ε.toMonoidHom) (by rw [hcard]; exact hodd)
    (by
      intro i j
      obtain ⟨g, hg, hgij⟩ := htrans (e.symm i) (e.symm j)
      refine ⟨ε g, ⟨g, hg, rfl⟩, ?_⟩
      show e (g (e.symm i)) = j
      rw [hgij]; simp)
  rwa [hcard] at this

end Odd5

theorem card_modEq_fixed {V : Type*} [Group V] [Finite V] {c : MulAut V} (hc5 : c ^ 5 = 1)
    (S : Set V) (hS : ∀ w ∈ S, c w ∈ S) :
    Nat.card S ≡ Nat.card {w : S // c (w : V) = w} [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fintype V := Fintype.ofFinite V
  let f : Function.End S := fun w => ⟨c w, hS w w.2⟩
  have hfpow : ∀ n : ℕ, ∀ w : S, ((f ^ n) w : V) = (c ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rw [pow_zero, pow_zero]; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, pow_succ]
      show ((f ^ n) (f w) : V) = (c ^ n) (c w)
      rw [ih]
  have hf5 : f ^ 5 = 1 := by
    funext w
    apply Subtype.ext
    rw [hfpow, hc5]
    rfl
  have key := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) (f := f) (by simpa using hf5)
  have hfix : Nat.card ↑(Function.fixedPoints f) = Nat.card {w : S // c (w : V) = w} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    show f w = w ↔ c (w : V) = w
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hfix] at key
  exact key

theorem closure_eq_top_of_invariant {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 16)
    {c : MulAut V} (hc5 : c ^ 5 = 1) (hcfpf : ∀ v : V, c v = v → v = 1) (S : Set V)
    (hS : ∀ w ∈ S, c w ∈ S) {v : V} (hvS : v ∈ S) (hv1 : v ≠ 1) : Subgroup.closure S = ⊤ := by
  have hW : ∀ w ∈ Subgroup.closure S, c w ∈ Subgroup.closure S := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hS x hx)
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact (Subgroup.closure S).mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact (Subgroup.closure S).inv_mem hx
  have hmod := card_modEq_fixed hc5 ((Subgroup.closure S : Subgroup V) : Set V) hW
  have hfix : Nat.card {w : ((Subgroup.closure S : Subgroup V) : Set V) // c (w : V) = w} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨(1 : V), (Subgroup.closure S).one_mem⟩, map_one c⟩⟩
    apply Subtype.ext; apply Subtype.ext
    rw [hcfpf _ a.2, hcfpf _ b.2]
  rw [hfix] at hmod
  have hcard : Nat.card ((Subgroup.closure S : Subgroup V) : Set V) = Nat.card (Subgroup.closure S) := rfl
  rw [hcard] at hmod
  have hdvd : Nat.card (Subgroup.closure S) ∣ 16 := hV ▸ Subgroup.card_subgroup_dvd_card _
  have hne : Nat.card (Subgroup.closure S) ≠ 1 := by
    intro h
    have hbot : Subgroup.closure S = ⊥ := Subgroup.eq_bot_of_card_eq _ h
    have := Subgroup.subset_closure hvS
    rw [hbot, SetLike.mem_coe, Subgroup.mem_bot] at this
    exact hv1 this
  have h16 : Nat.card (Subgroup.closure S) = 16 := by
    have hle : Nat.card (Subgroup.closure S) ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hmod
    generalize Nat.card (Subgroup.closure S) = k at *
    obtain ⟨m, hm⟩ := hdvd
    interval_cases k <;> omega
  exact Subgroup.eq_top_of_card_eq _ (by rw [h16, hV])

theorem eq_one_of_isPGroup_of_pow_odd {X : Type*} [Group X] (hX : IsPGroup 2 X) {x : X} {m : ℕ}
    (hm : Odd m) (hxm : x ^ m = 1) : x = 1 := by
  obtain ⟨j, hj⟩ := hX x
  have hd1 : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hxm
  have hd2 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
  have hcop : Nat.Coprime m (2 ^ j) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (by rcases hm with ⟨t, ht⟩; omega))))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)

theorem ncard_orbit_dvd {G X : Type*} [Group G] [MulAction G X] (x : X) :
    (MulAction.orbit G x).ncard ∣ Nat.card G := by
  have := Subgroup.card_mul_index (MulAction.stabilizer G x)
  rw [MulAction.index_stabilizer] at this
  exact ⟨Nat.card (MulAction.stabilizer G x), by rw [← this]; ring⟩

theorem endgame_tits {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 16)
    {A B : Subgroup (MulAut V)} (hBA : B ≤ A)
    (hodd : ¬ 2 ∣ B.relIndex A) (hB20 : Nat.card B ∣ 20)
    (hcyc : ∀ S : Subgroup ↥B, IsPGroup 2 S → IsCyclic S)
    {c : MulAut V} (hcB : c ∈ B) (hc5 : c ^ 5 = 1) (hcfpf : ∀ v : V, c v = v → v = 1)
    {I : Set V} (hI1 : (1 : V) ∉ I) (hIne : I.Nonempty)
    (hIA : ∀ a ∈ A, ∀ v ∈ I, a v ∈ I) (hIB : ∀ v ∈ I, ∀ w ∈ I, ∃ b ∈ B, b v = w) :
    A = B := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨v₀, hv₀⟩ := hIne
  have hv₁ : v₀ ≠ 1 := fun h => hI1 (h ▸ hv₀)
  have hc1 : c ≠ 1 := by
    intro h
    apply hv₁
    apply hcfpf
    rw [h]; rfl
  have hcord : orderOf c = 5 := orderOf_eq_prime hc5 hc1
  have hIorb : I = MulAction.orbit B v₀ := by
    ext w
    constructor
    · intro hw
      obtain ⟨b, hb, hbw⟩ := hIB v₀ hv₀ w hw
      exact ⟨⟨b, hb⟩, hbw⟩
    · rintro ⟨b, rfl⟩
      exact hIA b (hBA b.2) v₀ hv₀
  have hIcard : I.ncard ≤ 10 := by
    have hdvd : I.ncard ∣ Nat.card B := by
      have := ncard_orbit_dvd (G := B) v₀
      rwa [← hIorb] at this
    have hdvd20 : I.ncard ∣ 20 := hdvd.trans hB20
    have hlt : I.ncard < 16 := by
      have : I.ncard < (Set.univ : Set V).ncard :=
        Set.ncard_lt_ncard ⟨Set.subset_univ _, fun h => hI1 (h (Set.mem_univ 1))⟩
      rwa [Set.ncard_univ, hV] at this
    obtain ⟨m, hm⟩ := hdvd20
    generalize I.ncard = k at *
    interval_cases k <;> omega
  obtain ⟨SB⟩ : Nonempty (Sylow 2 ↥B) := inferInstance
  set S'' : Subgroup (MulAut V) := (SB : Subgroup ↥B).map B.subtype with hS''
  have hS''B : S'' ≤ B := Subgroup.map_subtype_le _
  have hS''card : Nat.card S'' = Nat.card (SB : Subgroup ↥B) :=
    Subgroup.card_map_of_injective B.subtype_injective
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card (SB : Subgroup ↥B) = 2 ^ n :=
    IsPGroup.iff_card.mp SB.isPGroup'
  have hS''2 : IsPGroup 2 S'' := IsPGroup.of_card (by rw [hS''card]; exact hn)
  have hS''A : S'' ≤ A := hS''B.trans hBA
  set SA : Subgroup ↥A := S''.subgroupOf A with hSA
  have hSAcard : Nat.card SA = Nat.card S'' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS''A).toEquiv
  have hSA2 : IsPGroup 2 SA := IsPGroup.of_card (by rw [hSAcard, hS''card]; exact hn)
  have hSAidx : ¬ 2 ∣ SA.index := by
    have h1 : S''.relIndex B = (SB : Subgroup ↥B).index := by
      unfold Subgroup.relIndex
      congr 1
      exact Subgroup.comap_map_eq_self_of_injective B.subtype_injective _
    have h2' : ¬ 2 ∣ S''.relIndex B := by rw [h1]; exact SB.not_dvd_index
    have h3 : S''.relIndex B * B.relIndex A = S''.relIndex A :=
      Subgroup.relIndex_mul_relIndex _ _ _ hS''B hBA
    have h4 : SA.index = S''.relIndex A := rfl
    rw [h4, ← h3]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h | h
    · exact h2' h
    · exact hodd h
  let SylA : Sylow 2 ↥A := IsPGroup.toSylow hSA2 hSAidx
  have hcycSA : IsCyclic ↥SylA := by
    have hc0 : IsCyclic ↥(SB : Subgroup ↥B) := hcyc _ SB.isPGroup'
    let e1 : ↥(SB : Subgroup ↥B) ≃* ↥S'' :=
      Subgroup.equivMapOfInjective _ B.subtype B.subtype_injective
    let e2 : ↥S'' ≃* ↥SA := (Subgroup.subgroupOfEquivOfLe hS''A).symm
    have : IsCyclic ↥SA := isCyclic_of_surjective (e1.trans e2).toMonoidHom (e1.trans e2).surjective
    exact this
  obtain ⟨N, hNn, hNc⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two SylA hcycSA
  have hNodd : Odd (Nat.card N) := by
    have h := hNc.index_eq_card
    rw [← h]
    have h0 : ¬ 2 ∣ (SylA : Subgroup ↥A).index := hSAidx
    exact Nat.odd_iff.mpr (by omega)
  have hNcardA : Nat.card N * Nat.card ↥SylA = Nat.card ↥A := hNc.card_mul_card
  have hQidx : N.index = Nat.card ↥SylA := hNc.symm.index_eq_card
  have hSylAcard : Nat.card ↥SylA = 2 ^ n := by
    show Nat.card ↥SA = 2 ^ n
    rw [hSAcard, hS''card]; exact hn
  have hQ2 : IsPGroup 2 (↥A ⧸ N) := by
    refine IsPGroup.of_card (n := n) ?_
    have : Nat.card (↥A ⧸ N) = N.index := rfl
    rw [this, hQidx, hSylAcard]
  set c' : ↥A := ⟨c, hBA hcB⟩ with hc'
  have hc'5 : c' ^ 5 = 1 := Subtype.ext (by simpa using hc5)
  have hcN : c' ∈ N := by
    have h1 : (QuotientGroup.mk' N c') ^ 5 = 1 := by rw [← map_pow, hc'5, map_one]
    have := eq_one_of_isPGroup_of_pow_odd hQ2 (x := QuotientGroup.mk' N c') (m := 5) (by decide) h1
    exact (QuotientGroup.eq_one_iff c').mp this
  set O : Subgroup (MulAut V) := N.map A.subtype with hO
  have hOA : O ≤ A := Subgroup.map_subtype_le _
  have hOcard : Nat.card O = Nat.card N := Subgroup.card_map_of_injective A.subtype_injective
  have hOodd : Odd (Nat.card O) := by rw [hOcard]; exact hNodd
  have hcO : c ∈ O := ⟨c', hcN, rfl⟩
  set Ov : Set V := MulAction.orbit O v₀ with hOv
  have hOvI : Ov ⊆ I := by
    rintro _ ⟨o, rfl⟩
    exact hIA o (hOA o.2) v₀ hv₀
  have hv₀Ov : v₀ ∈ Ov := MulAction.mem_orbit_self v₀
  have hcOv : ∀ w ∈ Ov, c w ∈ Ov := by
    rintro _ ⟨o, rfl⟩
    refine ⟨⟨c, hcO⟩ * o, ?_⟩
    rfl
  have hOvdvd : Ov.ncard ∣ Nat.card O := ncard_orbit_dvd (G := O) v₀
  have hOvodd : Odd Ov.ncard := Odd.of_dvd_nat hOodd hOvdvd
  have h5Ov : 5 ∣ Ov.ncard := by
    have hmod := card_modEq_fixed hc5 Ov hcOv
    have hfix : Nat.card {w : Ov // c (w : V) = w} = 0 := by
      rw [Nat.card_eq_zero]; left
      refine ⟨fun ⟨w, hw⟩ => ?_⟩
      exact hI1 (hcfpf _ hw ▸ hOvI w.2)
    rw [hfix] at hmod
    have h0 : Nat.card ↥Ov = Ov.ncard := Nat.card_coe_set_eq Ov
    rw [h0] at hmod
    exact Nat.modEq_zero_iff_dvd.mp hmod
  have hOvcard : Ov.ncard = 5 := by
    have hle : Ov.ncard ≤ 10 := (Set.ncard_le_ncard hOvI (Set.toFinite _)).trans hIcard
    obtain ⟨m, hm⟩ := h5Ov
    obtain ⟨t, ht⟩ := hOvodd
    omega
  have hXcard : Nat.card ↥Ov = 5 := by rw [Nat.card_coe_set_eq]; exact hOvcard
  let ψ : O →* Equiv.Perm ↥Ov := MulAction.toPermHom O ↥Ov
  have hψtrans : ∀ i j : ↥Ov, ∃ g ∈ ψ.range, g i = j := by
    intro i j
    obtain ⟨o₁, ho₁⟩ := i.2
    obtain ⟨o₂, ho₂⟩ := j.2
    refine ⟨ψ (o₂ * o₁⁻¹), ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    show (o₂ * o₁⁻¹) • (i : V) = (j : V)
    rw [← ho₁, ← ho₂, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  have hψodd : Odd (Nat.card ψ.range) := by
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker] at h1
    exact Odd.of_dvd_nat hOodd ⟨Nat.card ψ.ker, by rw [← h1]; ring⟩
  have hψ5 : Nat.card ψ.range = 5 := card_eq_five_of_odd_transitive hXcard ψ.range hψodd hψtrans
  set cO : O := ⟨c, hcO⟩ with hcO'
  have hψc1 : ψ cO ≠ 1 := by
    intro h
    have h1 : ψ cO ⟨v₀, hv₀Ov⟩ = ⟨v₀, hv₀Ov⟩ := by rw [h]; rfl
    have h2 : c v₀ = v₀ := congrArg Subtype.val h1
    exact hv₁ (hcfpf _ h2)
  have hψc5 : (ψ cO) ^ 5 = 1 := by
    rw [← map_pow]
    have : cO ^ 5 = 1 := Subtype.ext (by simpa using hc5)
    rw [this, map_one]
  have hψord : orderOf (ψ cO) = 5 := orderOf_eq_prime hψc5 hψc1
  have hzp : Subgroup.zpowers (ψ cO) = ψ.range := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact (Subgroup.zpowers_le).mpr ⟨cO, rfl⟩
    · rw [Nat.card_zpowers, hψord, hψ5]
  have htop : Subgroup.closure Ov = ⊤ :=
    closure_eq_top_of_invariant hV hc5 hcfpf Ov hcOv hv₀Ov hv₁
  have hOle : O ≤ Subgroup.zpowers c := by
    intro o ho
    have hψo : ψ ⟨o, ho⟩ ∈ Subgroup.zpowers (ψ cO) := by rw [hzp]; exact ⟨_, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hψo
    set o' : O := cO ^ (-k) * ⟨o, ho⟩ with ho'
    have hker : o' ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ho', map_mul, map_zpow, zpow_neg, hk]
      simp
    have hfix : ∀ w ∈ Ov, (o' : MulAut V) w = w := by
      intro w hw
      have h1 : ψ o' ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [MonoidHom.mem_ker.mp hker]; rfl
      exact congrArg Subtype.val h1
    have ho'1 : (o' : MulAut V) = 1 := by
      ext x
      have hx : x ∈ Subgroup.closure Ov := by rw [htop]; trivial
      have hle : Subgroup.closure Ov ≤
          MonoidHom.eqLocus (o' : MulAut V).toMonoidHom (MonoidHom.id V) :=
        (Subgroup.closure_le _).mpr fun w hw => hfix w hw
      exact hle hx
    have h3 : cO ^ (-k) * (⟨o, ho⟩ : O) = 1 := Subtype.ext ho'1
    have h4 : (⟨o, ho⟩ : O) = cO ^ k := by
      calc (⟨o, ho⟩ : O) = cO ^ k * (cO ^ (-k) * ⟨o, ho⟩) := by group
        _ = cO ^ k := by rw [h3, mul_one]
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h5' := congrArg Subtype.val h4
    simpa using h5'.symm
  have hOcard5 : Nat.card O = 5 := by
    have hzp_le : Subgroup.zpowers c ≤ O := (Subgroup.zpowers_le).mpr hcO
    have h1 : Nat.card O ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le hOle
    have h2' : Nat.card (Subgroup.zpowers c) ≤ Nat.card O := Subgroup.card_le_of_le hzp_le
    rw [Nat.card_zpowers, hcord] at h1 h2'
    omega
  have hNcard5 : Nat.card N = 5 := by rw [← hOcard]; exact hOcard5
  have hAcard : Nat.card A = 5 * 2 ^ n := by
    rw [← hNcardA, hNcard5, hSylAcard]
  have hBdvd : 5 * 2 ^ n ∣ Nat.card B := by
    have h1 : 5 ∣ Nat.card B := by
      have : Nat.card (Subgroup.zpowers c) ∣ Nat.card B :=
        Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).mpr hcB)
      rwa [Nat.card_zpowers, hcord] at this
    have h2' : 2 ^ n ∣ Nat.card B := by
      have : Nat.card S'' ∣ Nat.card B := Subgroup.card_dvd_of_le hS''B
      rwa [hS''card, hn] at this
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_right n (by decide)) h1 h2'
  have hBle : Nat.card A ≤ Nat.card B := by
    rw [hAcard]; exact Nat.le_of_dvd Nat.card_pos hBdvd
  exact (Subgroup.eq_of_le_of_card_ge hBA hBle).symm

open scoped Pointwise in
theorem isCyclic_of_isPGroup_of_card_twenty {Y : Type*} [Group Y] [Finite Y] (hY : Nat.card Y = 20)
    (hx : ∃ x : Y, orderOf x = 4) (S : Subgroup Y) (hS : IsPGroup 2 S) : IsCyclic S := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx4⟩ := hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hSdvd : Nat.card S ∣ 20 := hY ▸ Subgroup.card_subgroup_dvd_card S
  have hk2 : k ≤ 2 := by
    by_contra h
    have h' : 3 ≤ k := by omega
    have h1 : 2 ^ k ∣ 20 := hk ▸ hSdvd
    have h3 : 2 ^ 3 ∣ 20 := (pow_dvd_pow 2 h').trans h1
    norm_num at h3
  interval_cases k
  · have : S = ⊥ := Subgroup.eq_bot_of_card_eq S (by simpa using hk)
    subst this
    infer_instance
  · have : Fact (Nat.Prime (Nat.card S)) := ⟨by rw [hk]; exact Nat.prime_two⟩
    exact isCyclic_of_prime_card rfl
  ·
    have hxcard : Nat.card (Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, hx4]
    have hidx : ∀ (P : Subgroup Y), Nat.card P = 4 → ¬ 2 ∣ P.index := by
      intro P hP h
      have := Subgroup.card_mul_index P
      rw [hP, hY] at this
      obtain ⟨m, hm⟩ := h
      omega
    have hx2 : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := 2) (by rw [hxcard]; norm_num)
    let S₁ : Sylow 2 Y := IsPGroup.toSylow hx2 (hidx _ hxcard)
    let S₂ : Sylow 2 Y := IsPGroup.toSylow hS (hidx S (by rw [hk]; norm_num))
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S₁ S₂
    have hg' : (MulAut.conj g) • (Subgroup.zpowers x) = S := by
      have h1 := congrArg (fun P : Sylow 2 Y => (P : Subgroup Y)) hg
      simp only [Sylow.coe_subgroup_smul] at h1
      exact h1
    have hmem : MulAut.conj g x ∈ S := by
      rw [← hg']
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x, Subgroup.mem_zpowers x, rfl⟩
    have hord : orderOf (MulAut.conj g x) = 4 := by
      rw [(MulAut.conj g).orderOf_eq x, hx4]
    refine isCyclic_of_orderOf_eq_card (⟨MulAut.conj g x, hmem⟩ : S) ?_
    rw [Subgroup.orderOf_mk, hord, hk]
    norm_num

theorem isCyclic_of_isPGroup_of_card_ten {Y : Type*} [Group Y] [Finite Y] (hY : Nat.card Y = 10)
    (S : Subgroup Y) (hS : IsPGroup 2 S) : IsCyclic S := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hSdvd : Nat.card S ∣ 10 := hY ▸ Subgroup.card_subgroup_dvd_card S
  have hk2 : k ≤ 1 := by
    by_contra h
    have h' : 2 ≤ k := by omega
    have h1 : 2 ^ k ∣ 10 := hk ▸ hSdvd
    have h3 : 2 ^ 2 ∣ 10 := (pow_dvd_pow 2 h').trans h1
    norm_num at h3
  interval_cases k
  · have : S = ⊥ := Subgroup.eq_bot_of_card_eq S (by simpa using hk)
    subst this
    infer_instance
  · have : Fact (Nat.Prime (Nat.card S)) := ⟨by rw [hk]; exact Nat.prime_two⟩
    exact isCyclic_of_prime_card rfl

end S1422Loc

end CFSG.Quasithin
