module

public import CFSG.Quasithin.H13.A5Quad6
public import CFSG.Quasithin.Background.B5FinS8Core

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem alternatingNatural_eight_of_extSq {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (h : SLExteriorTwo L ⊤ ⊥ 4) :
    ∃ π, (FFModel.altDn 8).RealizesVia L ⊤ ⊥ π := by
  obtain ⟨π, hπ⟩ := h
  refine ⟨π.comp B5FinS8.alpha, FFModel.RealizesVia.of_surjHom (FFModel.altDn_isActionModel 8) hπ
    B5FinS8.alpha B5FinS8.alpha_surjective B5FinS8.ehat8 B5FinS8.ehat8_surjective ?_ ?_⟩
  · intro σ m hm
    exact B5FinS8.qHom_alt σ m.1 m.2
  · intro m
    exact B5FinS8.ehat8_ker m

@[expose] def cyc3 (a b c : Fin 8) : Equiv.Perm (Fin 8) := Equiv.swap a b * Equiv.swap b c

theorem cyc3_sign {a b c : Fin 8} (hab : a ≠ b) (hbc : b ≠ c) :
    Equiv.Perm.sign (cyc3 a b c) = 1 := by
  rw [cyc3, map_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hbc]
  rfl

theorem move_pair8 {i j k : Fin 8} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ m : Fin 8, m ≠ j ∧ m ≠ k ∧ cyc3 j k m i = i ∧ cyc3 j k m j = k := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : Fin 8, m ∉ ({i, j, k} : Finset (Fin 8)) := by
    by_contra h
    push Not at h
    have h1 : (Finset.univ : Finset (Fin 8)).card ≤ ({i, j, k} : Finset (Fin 8)).card :=
      Finset.card_le_card fun x _ => h x
    have h2 : ({i, j, k} : Finset (Fin 8)).card ≤ 3 := Finset.card_le_three
    simp at h1
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  obtain ⟨hmi, hmj, hmk⟩ := hm
  refine ⟨m, hmj, hmk, ?_, ?_⟩
  · rw [cyc3, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hik (Ne.symm hmi),
      Equiv.swap_apply_of_ne_of_ne hij hik]
  · rw [cyc3, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hjk (Ne.symm hmj),
      Equiv.swap_apply_left]

theorem pair8_add : ∀ i j : Fin 8,
    (Pi.single (0 : Fin 8) (1 : ZMod 2) + Pi.single i 1 + (Pi.single 0 1 + Pi.single j 1) :
      Fin 8 → ZMod 2) = Pi.single i (1 : ZMod 2) + Pi.single j 1 := by
  decide +kernel

theorem d8_decomp : ∀ m : Fin 8 → ZMod 2, ∑ i, m i = 0 →
    ∑ k, (if m k = 1 then (Pi.single (0 : Fin 8) (1 : ZMod 2) + Pi.single k 1 :
      Fin 8 → ZMod 2) else 0) = m := by
  decide +kernel

theorem d8_pair_ne : ∀ i j : Fin 8, i ≠ j →
    (Pi.single i (1 : ZMod 2) + Pi.single j 1 : Fin 8 → ZMod 2) ≠ 0 ∧
      (Pi.single i (1 : ZMod 2) + Pi.single j 1 : Fin 8 → ZMod 2) ≠ (fun _ => 1) := by
  decide +kernel

theorem pair8_self : ∀ i : Fin 8,
    (Pi.single i (1 : ZMod 2) + Pi.single i 1 : Fin 8 → ZMod 2) = 0 := by
  decide +kernel

section PV

abbrev Q8 : Type :=
  ↥(G6.coreMod 8) ⧸ (Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8).subgroupOf (G6.coreMod 8)

@[expose] def pv8 (i j : Fin 8) : ↥(G6.coreMod 8) :=
  ⟨G64.pairVec i j, G64.pairVec_mem_coreMod i j⟩

theorem toAdd_pv8 (i j : Fin 8) :
    Multiplicative.toAdd ((pv8 i j : ↥(G6.coreMod 8)) : G6.PermMod 8) =
      Pi.single i 1 + Pi.single j 1 := rfl

theorem pv8_comm (i j : Fin 8) : pv8 i j = pv8 j i := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  rw [toAdd_pv8, toAdd_pv8]
  exact add_comm _ _

theorem pv8_self (i : Fin 8) : pv8 i i = 1 := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  rw [toAdd_pv8]
  exact pair8_self i

theorem pv8_mul (i j : Fin 8) : pv8 0 i * pv8 0 j = pv8 i j := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  rw [Subgroup.coe_mul, toAdd_mul, toAdd_pv8, toAdd_pv8, toAdd_pv8]
  exact pair8_add i j

theorem permAct_pv8 (σ : Equiv.Perm (Fin 8)) (i j : Fin 8) :
    G6.permAct 8 σ ((pv8 i j : ↥(G6.coreMod 8)) : G6.PermMod 8) =
      ((pv8 (σ i) (σ j) : ↥(G6.coreMod 8)) : G6.PermMod 8) :=
  G64.permAct_pairVec σ i j

theorem mk_pv8_ne_one {i j : Fin 8} (hij : i ≠ j) : (QuotientGroup.mk (pv8 i j) : Q8) ≠ 1 := by
  intro h
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  have hz := (mem_zpowers_of_mul_self (allOnes_mul_self 8)).mp (Subgroup.mem_inf.mp h).1
  obtain ⟨h1, h2⟩ := d8_pair_ne i j hij
  rcases hz with hz | hz
  · apply h1
    rw [← toAdd_pv8, hz]
    rfl
  · apply h2
    rw [← toAdd_pv8, hz]
    rfl

theorem sec8_eq_prod (m : ↥(G6.coreMod 8)) :
    m = ∏ k : Fin 8, (if Multiplicative.toAdd (m : G6.PermMod 8) k = 1 then pv8 0 k else 1) := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  have hp := map_prod (G6.coreMod 8).subtype
    (fun k : Fin 8 => if Multiplicative.toAdd (m : G6.PermMod 8) k = 1 then pv8 0 k else 1)
    Finset.univ
  rw [show ((∏ k : Fin 8, (if Multiplicative.toAdd (m : G6.PermMod 8) k = 1 then pv8 0 k else 1) :
      ↥(G6.coreMod 8)) : G6.PermMod 8) = ∏ k : Fin 8, (((if Multiplicative.toAdd (m : G6.PermMod 8)
        k = 1 then pv8 0 k else 1 : ↥(G6.coreMod 8))) : G6.PermMod 8) from hp, toAdd_prod]
  have h := d8_decomp (Multiplicative.toAdd (m : G6.PermMod 8)) (G6.mem_coreMod.mp m.2)
  conv_lhs => rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rfl
  · rfl

end PV
theorem exists_secHom' {V : Type} [CommGroup V] {D : FFModel} {H : Subgroup (MulAut V)}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H ⊤ ⊥ π) :
    ∃ β : ↥D.sec →* V, Function.Surjective β ∧ (∀ m : ↥D.sec, β m = 1 ↔ (m : D.Amb) ∈ D.ker) ∧
      ∀ (γ : D.Gam) (m : ↥D.sec) (hm : D.act γ (m : D.Amb) ∈ D.sec),
        β ⟨D.act γ (m : D.Amb), hm⟩ = ((π γ : ↥H) : MulAut V) (β m) := by
  obtain ⟨e, he⟩ := G64.RealizesVia.exists_modEquiv h
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' (D.ker.subgroupOf D.sec)), fun v => ?_,
    fun m => ?_, fun γ m hm => ?_⟩
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e v)
    exact ⟨m, by
      show e.symm (QuotientGroup.mk m) = v
      rw [hm, e.symm_apply_apply]⟩
  · show e.symm (QuotientGroup.mk m) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · show e.symm (QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩) =
      ((π γ : ↥H) : MulAut V) (e.symm (QuotientGroup.mk m))
    rw [MulEquiv.symm_apply_eq]
    exact (he γ (e.symm (QuotientGroup.mk m)) m hm (e.apply_symm_apply _)).symm

section D8

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
  {π : ↥(alternatingGroup (Fin 8)) →* ↥L} (hπ : (FFModel.altDn 8).RealizesVia L ⊤ ⊥ π)
include hπ

theorem quad_row_A8 (hV : ∀ w : V, w ^ 2 = 1) (q : V → ZMod 2)
    (hqL : ∀ x ∈ L, ∀ w, q (x w) = q w)
    (hβ : ∀ a b w, polarQ q (a * b) w = polarQ q a w + polarQ q b w)
    (hnd : ∀ a, a ≠ 1 → ∃ w, polarQ q a w ≠ 0) {c : MulAut V} (hc : c ∈ L) (hc3 : c ^ 3 = 1) :
    ∃ w, c w = w ∧ q w ≠ 0 := by
  classical
  obtain ⟨β0, hβs, hβk, hβe⟩ := exists_secHom' hπ
  let f : ↥(G6.coreMod 8) →* V :=
    β0.comp (MonoidHom.id _ : ↥(G6.coreMod 8) →* ↥(FFModel.altDn 8).sec)
  have hfsurj : ∀ v : V, ∃ m : ↥(G6.coreMod 8), f m = v := by
    intro v
    obtain ⟨m, hm⟩ := hβs v
    exact ⟨⟨m.1, m.2⟩, hm⟩
  have hfact : ∀ (σ : ↥(alternatingGroup (Fin 8))) (m : ↥(G6.coreMod 8)),
      ((π σ : ↥L) : MulAut V) (f m) =
        f ⟨G6.permAct 8 (σ : Equiv.Perm (Fin 8)) m, G6.permAct_mem_coreMod _ m.2⟩ :=
    fun σ m => (hβe σ ⟨m.1, m.2⟩ (G6.permAct_mem_coreMod _ m.2)).symm
  have hfker : ∀ m : ↥(G6.coreMod 8), f m = 1 ↔
      (m : G6.PermMod 8) ∈ Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8 :=
    fun m => hβk ⟨m.1, m.2⟩
  let w : Fin 8 → Fin 8 → V := fun i j => f (pv8 i j)
  have hwact : ∀ (σ : ↥(alternatingGroup (Fin 8))) (i j : Fin 8), ((π σ : ↥L) : MulAut V) (w i j) =
      w ((σ : Equiv.Perm (Fin 8)) i) ((σ : Equiv.Perm (Fin 8)) j) := by
    intro σ i j
    show ((π σ : ↥L) : MulAut V) (f (pv8 i j)) = f (pv8 _ _)
    rw [hfact]
    congr 1
    exact Subtype.ext (permAct_pv8 _ i j)
  have hsymm : ∀ i j, w i j = w j i := fun i j => by
    show f (pv8 i j) = f (pv8 j i)
    rw [pv8_comm]
  have hself : ∀ i, w i i = 1 := fun i => by
    show f (pv8 i i) = 1
    rw [pv8_self, map_one]
  have hmul : ∀ i j, w 0 i * w 0 j = w i j := fun i j => by
    show f (pv8 0 i) * f (pv8 0 j) = f (pv8 i j)
    rw [← map_mul, pv8_mul]
  have hmove : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → q (w i j) = q (w i k) := by
    intro i j k hij hik hjk
    obtain ⟨m, hmj, hmk, h1, h2⟩ := move_pair8 hij hik hjk
    let σ : ↥(alternatingGroup (Fin 8)) :=
      ⟨cyc3 j k m, by rw [Equiv.Perm.mem_alternatingGroup]; exact cyc3_sign hjk (Ne.symm hmk)⟩
    have h := hqL _ (π σ).2 (w i j)
    rw [hwact σ i j] at h
    have e1 : (σ : Equiv.Perm (Fin 8)) i = i := h1
    have e2 : (σ : Equiv.Perm (Fin 8)) j = k := h2
    rw [e1, e2] at h
    exact h.symm
  have hconst0 : ∀ j, j ≠ 0 → q (w 0 j) = q (w 0 1) := by
    intro j hj
    by_cases hj1 : j = 1
    · rw [hj1]
    · exact hmove 0 j 1 (Ne.symm hj) (by decide) hj1
  have hconst : ∀ i j, i ≠ j → q (w i j) = q (w 0 1) := by
    intro i j hij
    by_cases hi : i = 0
    · subst hi
      exact hconst0 j (Ne.symm hij)
    · by_cases hj : j = 0
      · subst hj
        rw [hsymm]
        exact hconst0 i hi
      · rw [hmove i j 0 hij hi hj, hsymm]
        exact hconst0 i hi
  have hq1 : q 1 = 0 := by
    have h := polarQ_one_left hβ 1
    rw [polarQ, mul_one] at h
    revert h
    generalize q 1 = t
    decide +revert
  have hw01 : w 0 1 ≠ 1 := by
    intro h
    apply mk_pv8_ne_one (i := 0) (j := 1) (by decide)
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact (hfker _).mp h
  have hq01 : q (w 0 1) ≠ 0 := by
    intro h0
    have hk : ∀ k, w 0 k ∈ perpQ hβ (w 0 1) := by
      intro k
      show polarQ q (w 0 1) (w 0 k) = 0
      by_cases hk0 : k = 0
      · subst hk0
        rw [hself, polarQ_comm, polarQ_one_left hβ]
      by_cases hk1 : k = 1
      · subst hk1
        rw [polarQ, ← pow_two, hV, hq1, h0]
        decide
      · rw [polarQ, hmul, hconst 1 k (Ne.symm hk1), hconst 0 k (Ne.symm hk0), h0]
        decide
    obtain ⟨v, hv⟩ := hnd (w 0 1) hw01
    apply hv
    obtain ⟨m, rfl⟩ := hfsurj v
    have hmem : f m ∈ perpQ hβ (w 0 1) := by
      rw [sec8_eq_prod m, map_prod]
      refine Subgroup.prod_mem _ fun k _ => ?_
      split_ifs
      · exact hk k
      · rw [map_one]
        exact Subgroup.one_mem _
    exact hmem
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥(alternatingGroup (Fin 8)), π σ = ⟨c, hc⟩ := hπ.1 ⟨c, hc⟩
  have hinj : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (G64.altDn_faithful (by norm_num)) hπ
  have hσ3 : σ ^ 3 = 1 := hinj (by
    rw [map_pow, hσ, map_one]
    exact Subtype.ext hc3)
  have hσ3' : (σ : Equiv.Perm (Fin 8)) ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    have := congrArg Subtype.val hσ3
    simpa using this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := Equiv.Perm.card_compl_support_modEq hσ3'
  rw [Fintype.card_fin] at hmod
  have hcard : 1 < (Equiv.Perm.support (σ : Equiv.Perm (Fin 8)))ᶜ.card := by
    have h' := hmod
    unfold Nat.ModEq at h'
    have hle : (Equiv.Perm.support (σ : Equiv.Perm (Fin 8)))ᶜ.card ≤ 8 := by
      calc _ ≤ (Finset.univ : Finset (Fin 8)).card := Finset.card_le_univ _
        _ = 8 := Finset.card_fin 8
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
  rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hi hj
  refine ⟨w i j, ?_, ?_⟩
  · have := hwact σ i j
    rw [hσ, hi, hj] at this
    exact this
  · rw [hconst i j hij]
    exact hq01

end D8

end CFSG.Quasithin.H13.A5
