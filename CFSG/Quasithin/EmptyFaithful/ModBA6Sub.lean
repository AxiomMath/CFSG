module

public import CFSG.Quasithin.H13.VolIAltCoverSixData

public section

namespace CFSG.Quasithin.ModB

open Equiv Equiv.Perm Subgroup CFSG.Quasithin CFSG.Quasithin.G6

abbrev A6 : Type := ↥(alternatingGroup (Fin 6))

theorem card_A6 : Nat.card A6 = 360 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

instance : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)

section Sub

def x5 : A6 :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem x5_pow : x5 ^ 5 = 1 := by decide +kernel

theorem x5_ne : x5 ≠ 1 := by decide +kernel

private theorem orderOf_x5 : orderOf x5 = 5 :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_eq_prime x5_pow x5_ne

private def P5 : Finset A6 := {1, x5, x5 ^ 2, x5 ^ 3, x5 ^ 4}

private theorem mem_zpowers_x5 (y : A6) : y ∈ Subgroup.zpowers x5 ↔ y ∈ P5 := by
  constructor
  · rintro ⟨k, rfl⟩
    show x5 ^ k ∈ P5
    have h : x5 ^ k = x5 ^ (k % 5) := by
      rw [← zpow_mod_orderOf, orderOf_x5]
      norm_cast
    have hk : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
    rw [h]
    simp only [P5, Finset.mem_insert, Finset.mem_singleton]
    rcases hk with hk | hk | hk | hk | hk <;> rw [hk] <;> simp
  · intro hy
    simp only [P5, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
    · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3
    · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 4

private def Nset : Finset A6 := Finset.univ.filter fun g => g * x5 * g⁻¹ ∈ P5

private theorem card_Nset : Nset.card = 10 := by
  unfold Nset P5
  decide +kernel

private theorem sub_le_Nset_of_normal (S : Subgroup A6) (hx : x5 ∈ S)
    (hn : ((Subgroup.zpowers x5).subgroupOf S).Normal) : ∀ s ∈ S, s ∈ Nset := by
  intro s hs
  have h1 : (⟨x5, hx⟩ : ↥S) ∈ (Subgroup.zpowers x5).subgroupOf S :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x5)
  have h2 := hn.conj_mem _ h1 ⟨s, hs⟩
  have h3 := Subgroup.mem_subgroupOf.mp h2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
  rw [mem_zpowers_x5] at h3
  simpa [Nset] using h3

theorem no_sub_20_45 (S : Subgroup A6) (hx : x5 ∈ S) (h : Nat.card S = 20 ∨ Nat.card S = 45) :
    False := by
  classical
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P : Subgroup ↥S := (Subgroup.zpowers x5).subgroupOf S
  have hPcard : Nat.card P = 5 := by
    have e : Nat.card P = Nat.card (Subgroup.zpowers x5) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hx)).toEquiv
    rw [e, Nat.card_zpowers, orderOf_x5]
  have hfact : (Nat.card S).factorization 5 = 1 := by
    rcases h with h | h <;> rw [h] <;> decide +kernel
  let PS : Sylow 5 ↥S := Sylow.ofCard P (by rw [hPcard, hfact]; norm_num)
  have hmod : Nat.card (Sylow 5 ↥S) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 ↥S
  have hdvd : Nat.card (Sylow 5 ↥S) ∣ (PS : Subgroup ↥S).index := PS.card_dvd_index
  have hidx : (PS : Subgroup ↥S).index * 5 = Nat.card S := by
    have := Subgroup.card_mul_index (PS : Subgroup ↥S)
    have hPS : Nat.card (PS : Subgroup ↥S) = 5 := hPcard
    rw [hPS] at this
    omega
  have hone : Nat.card (Sylow 5 ↥S) = 1 := by
    rcases h with h | h
    · have h4 : (PS : Subgroup ↥S).index = 4 := by omega
      rw [h4] at hdvd
      have hle : Nat.card (Sylow 5 ↥S) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < Nat.card (Sylow 5 ↥S) := Nat.card_pos
      unfold Nat.ModEq at hmod
      interval_cases hc : Nat.card (Sylow 5 ↥S) <;> simp_all
    · have h9 : (PS : Subgroup ↥S).index = 9 := by omega
      rw [h9] at hdvd
      have hle : Nat.card (Sylow 5 ↥S) ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < Nat.card (Sylow 5 ↥S) := Nat.card_pos
      unfold Nat.ModEq at hmod
      interval_cases hc : Nat.card (Sylow 5 ↥S) <;> simp_all
  have hsub : Subsingleton (Sylow 5 ↥S) := by
    rw [Nat.card_eq_one_iff_unique] at hone
    exact hone.1
  have hnorm : (PS : Subgroup ↥S).Normal := Sylow.normal_of_subsingleton PS
  have hSN := sub_le_Nset_of_normal S hx hnorm
  have hcardle : Nat.card S ≤ Nset.card := by
    have h1 : Nat.card S ≤ Nat.card (↥Nset) :=
      Nat.card_le_card_of_injective (fun s : S => (⟨(s : A6), hSN s s.2⟩ : ↥Nset))
        (fun a b hab => Subtype.ext (congrArg (fun z : ↥Nset => (z : A6)) hab))
    rwa [Nat.card_eq_fintype_card (α := ↥Nset), Fintype.card_coe] at h1
  rw [card_Nset] at hcardle
  omega

open CFSG.Quasithin.H13.VolI (a6c012 a6c234 a6c012_pow a6c234_pow alt6_words IsWord6)

private def B5 : Subgroup A6 := MulAction.stabilizer A6 (5 : Fin 6)

private theorem mem_B5 {g : A6} : g ∈ B5 ↔ (g : Perm (Fin 6)) 5 = 5 := Iff.rfl

private theorem card_B5 : Nat.card B5 = 60 := by
  have : Nat.card B5 = Nat.card {g : A6 // (g : Perm (Fin 6)) 5 = 5} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_B5)
  rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem x5_zero : ∀ k : Fin 5, ((x5 ^ (k : ℕ) : A6) : Perm (Fin 6)) 0 = Fin.castSucc k := by
  decide +kernel

private theorem inv_fix6 : ∀ g : A6, g * g = 1 → g ≠ 1 → ∃ p : Fin 6, (g : Perm (Fin 6)) p = p := by
  decide +kernel

private theorem a6c012_five : (a6c012 : Perm (Fin 6)) 5 = 5 := by decide

private theorem a6c234_five' : (a6c234 : Perm (Fin 6)) 5 = 5 := by decide

theorem no_sub_30 (S : Subgroup A6) (hx : x5 ∈ S) (h : Nat.card S = 30) : False := by
  classical
  by_cases h5 : ∃ s ∈ S, (s : Perm (Fin 6)) 0 = 5
  ·
    have htrans : ∀ p : Fin 6, ∃ s ∈ S, (s : Perm (Fin 6)) 0 = p := by
      intro p
      by_cases hp : p = 5
      · subst hp; exact h5
      · obtain ⟨k, hk⟩ : ∃ k : Fin 5, Fin.castSucc k = p := Fin.exists_castSucc_eq.mpr hp
        exact ⟨x5 ^ (k : ℕ), Subgroup.pow_mem _ hx _, by rw [x5_zero k, hk]⟩
    have htrans2 : ∀ p q : Fin 6, ∃ s ∈ S, (s : Perm (Fin 6)) p = q := by
      intro p q
      obtain ⟨s₁, hs₁, h₁⟩ := htrans p
      obtain ⟨s₂, hs₂, h₂⟩ := htrans q
      refine ⟨s₂ * s₁⁻¹, S.mul_mem hs₂ (S.inv_mem hs₁), ?_⟩
      show (s₂ : Perm (Fin 6)) ((s₁ : Perm (Fin 6))⁻¹ p) = q
      rw [Perm.inv_eq_iff_eq.mpr h₁.symm, h₂]
    have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 2 (by rw [h]; norm_num)
    have huu : (u : A6) * (u : A6) = 1 := by
      have : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
      have h' := congrArg (fun x : ↥S => (x : A6)) this
      simpa [pow_two] using h'
    have hu1 : (u : A6) ≠ 1 := by
      intro h1
      have : u = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hu
      omega
    obtain ⟨p, hp⟩ := inv_fix6 _ huu hu1
    have horb : MulAction.orbit ↥S p = Set.univ := by
      refine Set.eq_univ_iff_forall.mpr fun q => ?_
      obtain ⟨s, hs, hsq⟩ := htrans2 p q
      exact ⟨⟨s, hs⟩, hsq⟩
    have hos := Subgroup.card_mul_index (MulAction.stabilizer ↥S p)
    have h6 : (MulAction.stabilizer ↥S p).index = 6 := by
      rw [MulAction.index_stabilizer, horb, Set.ncard_univ, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    rw [h6, h] at hos
    have hst : Nat.card (MulAction.stabilizer ↥S p) = 5 := by omega
    have hup : u ∈ MulAction.stabilizer ↥S p := hp
    have h5' : (⟨u, hup⟩ : ↥(MulAction.stabilizer ↥S p)) ^ 5 = 1 := by
      have := pow_card_eq_one' (G := ↥(MulAction.stabilizer ↥S p)) (x := ⟨u, hup⟩)
      rwa [hst] at this
    have h5'' : u ^ 5 = 1 := by
      have := congrArg (fun x : ↥(MulAction.stabilizer ↥S p) => ((x : ↥S))) h5'
      simpa using this
    have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    have : u = 1 := by
      calc u = u ^ 5 * (u ^ 2)⁻¹ * (u ^ 2)⁻¹ := by group
        _ = 1 := by rw [hu2, h5'']; simp
    exact hu1 (by rw [this]; rfl)
  · push Not at h5
    have hfix5 : ∀ s ∈ S, (s : Perm (Fin 6)) 5 = 5 := by
      intro s hs
      by_contra hne
      obtain ⟨k, hk⟩ : ∃ k : Fin 5, Fin.castSucc k = (s : Perm (Fin 6)) 5 :=
        Fin.exists_castSucc_eq.mpr hne
      apply h5 (s⁻¹ * x5 ^ (k : ℕ)) (S.mul_mem (S.inv_mem hs) (Subgroup.pow_mem _ hx _))
      show (s : Perm (Fin 6))⁻¹ (((x5 ^ (k : ℕ) : A6) : Perm (Fin 6)) 0) = 5
      rw [x5_zero k, hk]
      simp
    have hSB : S ≤ B5 := fun s hs => hfix5 s hs
    let S' : Subgroup ↥B5 := S.subgroupOf B5
    have hS'card : Nat.card S' = 30 := by
      rw [← h]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv
    have hS'idx : S'.index = 2 := by
      have := Subgroup.card_mul_index S'
      rw [hS'card, card_B5] at this
      omega
    have hcyc : ∀ (g : A6), g ^ 3 = 1 → g ∈ B5 → g ∈ S := by
      intro g hg3 hgB
      have h1 := Subgroup.mul_self_mem_of_index_two hS'idx (⟨g, hgB⟩ : ↥B5)⁻¹
      have h2 : (g⁻¹ * g⁻¹ : A6) ∈ S := h1
      have h3 : (g⁻¹ * g⁻¹ : A6) = g := by
        calc g⁻¹ * g⁻¹ = g⁻¹ * g⁻¹ * g ^ 3 := by rw [hg3, mul_one]
          _ = g := by group
      rwa [h3] at h2
    have hc₁ : a6c012 ∈ S := hcyc _ a6c012_pow a6c012_five
    have hc₂ : a6c234 ∈ S := hcyc _ a6c234_pow a6c234_five'
    have hall : ∀ σ ∈ B5, σ ∈ S := by
      intro σ hσ
      obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, f, hf, rfl⟩ := alt6_words σ hσ
      have hmem1 : ∀ g ∈ S, ∀ y ∈ [1, g, g * g], y ∈ S := by
        intro g hg y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl
        · exact S.one_mem
        · exact hg
        · exact S.mul_mem hg hg
      exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (hmem1 _ hc₁ a ha)
        (hmem1 _ hc₂ b hb)) (hmem1 _ hc₁ c hc)) (hmem1 _ hc₂ d hd)) (hmem1 _ hc₁ e he))
        (hmem1 _ hc₂ f hf)
    have := Subgroup.card_le_of_le (fun σ hσ => hall σ hσ : B5 ≤ S)
    rw [card_B5, h] at this
    omega

end Sub

end CFSG.Quasithin.ModB
