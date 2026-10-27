module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2That

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 x45 xY repL_x)

@[expose] def e0L : PL := comp fhatL xL

@[expose] def othW : List (List ℕ) :=
  [[1, 0, 2, 3, 1, 0, 2], [], [2, 3, 1, 1, 3, 1, 0, 1], [1, 3, 1, 1, 0, 1, 0, 2],
    [2, 0, 2, 0, 1, 0, 1], [2, 3, 1, 0, 2, 3, 1], [2, 3, 0, 2, 2, 0, 2],
    [2, 3, 2, 0, 1, 0, 1, 1], [1, 3, 0, 1, 0, 2, 3, 1], [1, 3, 2, 3, 2, 2],
    [1, 0, 1, 0, 2, 0, 2], [1, 1, 0, 1, 3, 1, 0, 1, 1]]

@[expose] def eW37 : List (List ℕ) :=
  [[], [1], [2], [0, 1], [1, 1], [3, 1], [0, 2], [2, 2], [3, 2], [1, 0, 1], [2, 0, 1],
    [3, 0, 1], [0, 1, 1], [3, 1, 1], [1, 3, 1], [2, 3, 1], [1, 0, 2], [2, 0, 2], [3, 0, 2],
    [0, 2, 2], [3, 2, 2], [1, 3, 2], [2, 3, 2], [0, 1, 0, 1], [1, 1, 0, 1], [3, 1, 0, 1],
    [0, 2, 0, 1], [2, 2, 0, 1], [1, 3, 0, 1], [2, 3, 0, 1], [1, 0, 1, 1], [2, 0, 1, 1],
    [3, 0, 1, 1], [1, 3, 1, 1], [2, 3, 1, 1], [0, 1, 3, 1], [1, 1, 3, 1]]

@[expose] def e0A : Ah := fhatA * xA

theorem repL_e0A : RepL e0L (e0A : P45) := repL_mul repL_fhat repL_x

theorem outer_classify : ∀ l ∈ Thl, l ∉ Tl → comp l l = idL →
    (∃ m ∈ Thl, comp l m = comp m fhatL) ∨
      ∃ w ∈ othW, comp l (evalAL w) = comp (evalAL w) e0L := by
  decide +kernel

theorem eW37_nodup : (eW37.map fun w => comp (comp (evalAL w) e0L) (evalAL (invAL w))).Nodup := by
  decide +kernel

theorem eW37_length : eW37.length = 37 := by decide +kernel

@[expose] def cw (w : List ℕ) : Ah :=
  (⟨wordAP w, wordAP_mem w⟩ : Ah) * e0A * (⟨wordAP w, wordAP_mem w⟩ : Ah)⁻¹

theorem repL_cw (w : List ℕ) :
    RepL (comp (comp (evalAL w) e0L) (evalAL (invAL w))) (cw w : P45) := by
  have hinv : RepL (evalAL (invAL w)) (((⟨wordAP w, wordAP_mem w⟩ : Ah)⁻¹ : Ah) : P45) := by
    have : (((⟨wordAP w, wordAP_mem w⟩ : Ah)⁻¹ : Ah) : P45) = wordAP (invAL w) := by
      rw [wordAP_invAL]
      rfl
    rw [this]
    exact repL_wordAP _
  exact repL_mul (repL_mul (repL_wordAP w) repL_e0A) hinv

theorem card_cent_e0_lt :
    Nat.card ↥(Subgroup.centralizer ({e0A} : Set Ah)) < 1440 := by
  classical
  have hnd : (eW37.map cw).Nodup := by
    refine List.Nodup.of_map (fun a : Ah => permL (a : P45)) ?_
    rw [List.map_map]
    have : ((fun a : Ah => permL (a : P45)) ∘ cw) =
        fun w => comp (comp (evalAL w) e0L) (evalAL (invAL w)) :=
      funext fun w => permL_eq_of_repL (repL_cw w)
    rw [this]
    exact eW37_nodup
  have hsub : (↑(eW37.map cw).toFinset : Set Ah) ⊆ _root_.conjugatesOf e0A := by
    intro a ha
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ha)
    exact isConj_iff.2 ⟨(⟨wordAP w, wordAP_mem w⟩ : Ah), rfl⟩
  have h1 : (eW37.map cw).toFinset.card ≤ (_root_.conjugatesOf e0A).ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [List.toFinset_card_of_nodup hnd, List.length_map, eW37_length] at h1
  have h2 := Subgroup.card_mul_index (H := Subgroup.centralizer ({e0A} : Set Ah))
  rw [Subgroup.index_centralizer_eq_ncard, card_A] at h2
  by_contra hge
  push Not at hge
  have h3 : 1440 * 37 ≤ Nat.card ↥(Subgroup.centralizer ({e0A} : Set Ah)) *
      (_root_.conjugatesOf e0A).ncard := Nat.mul_le_mul hge h1
  omega

theorem card_centralizer_conj {G : Type*} [Group G] (f h : G) :
    Nat.card ↥(Subgroup.centralizer ({h * f * h⁻¹} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({f} : Set G)) := by
  have e := U42.centralizer_map (MulAut.conj h) f
  rw [show h * f * h⁻¹ = (MulAut.conj h) f from rfl, e]
  exact Subgroup.card_map_of_injective (MulAut.conj h).injective

theorem isPGroup_zpowers_of_sq {H : Type*} [Group H] {g : H} (h : g * g = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers g) := by
  have hdvd : orderOf g ∣ 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

theorem signA_conj (a g : Ah) : signA (a⁻¹ * g * a) = signA g := by
  calc signA (a⁻¹ * g * a) = (signA a)⁻¹ * signA g * signA a := by simp [map_mul, map_inv]
    _ = signA g := by rw [mul_comm ((signA a)⁻¹) (signA g), mul_assoc, inv_mul_cancel, mul_one]

theorem good_conj {g : Ah}
    (hg : IsGoodInv g) : ∃ a ∈ Bh, g = a * fhatA * a⁻¹ := by
  obtain ⟨hgB, hgY, hg2, hgc⟩ := hg
  have hg2' : g * g = 1 := by rw [← pow_two]; exact hg2
  obtain ⟨T', hT', hgT'⟩ := A4.exists_isSylowTwoOf_ge (Subgroup.zpowers_le.2 hgB)
    (isPGroup_zpowers_of_sq hg2')
  obtain ⟨a, haB, hTa⟩ := B6.isSylowTwoOf_exists_conj isSylowTwoOf_That_Bh hT'
  have hga : a⁻¹ * g * a ∈ That := by
    have : g ∈ T' := hgT' (Subgroup.mem_zpowers g)
    rw [hTa] at this
    exact B6.mem_conjSub.1 this
  have hsign : signA (a⁻¹ * g * a) = -1 := by
    rw [signA_conj]
    exact (signA_eq_neg_one_iff g).2 hgY
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff _).1 hga
  have hl_out : l ∉ Tl := fun hlT => by
    obtain ⟨y, -, hyrep⟩ := exists_T_of_mem_Tl hlT
    have : a⁻¹ * g * a = incl y := Subtype.ext (eq_of_repL hrep hyrep)
    rw [this, signA_incl] at hsign
    exact absurd hsign (by decide)
  have hg'2 : (a⁻¹ * g * a) * (a⁻¹ * g * a) = 1 := by
    calc (a⁻¹ * g * a) * (a⁻¹ * g * a) = a⁻¹ * (g * g) * a := by group
      _ = 1 := by rw [hg2']; group
  have hl2 : comp l l = idL :=
    repL_unique (repL_mul hrep hrep) (by
      have : (((a⁻¹ * g * a : Ah) : P45)) * ((a⁻¹ * g * a : Ah) : P45) = 1 :=
        congrArg Subtype.val hg'2
      rw [this]
      exact repL_one 45)
  rcases outer_classify l hl hl_out hl2 with ⟨m, hm, hmeq⟩ | ⟨w, hw, hweq⟩
  · obtain ⟨m', hm', hmrep⟩ := exists_That_of_mem_Thl hm
    have h1 : (a⁻¹ * g * a) * m' = m' * fhatA := by
      apply Subtype.ext
      apply eq_of_repL (l := comp l m)
      · exact repL_mul hrep hmrep
      · rw [hmeq]
        exact repL_mul hmrep repL_fhat
    refine ⟨a * m', Bh.mul_mem haB (That_le_Bh hm'), ?_⟩
    calc g = a * ((a⁻¹ * g * a) * m') * m'⁻¹ * a⁻¹ := by group
      _ = a * (m' * fhatA) * m'⁻¹ * a⁻¹ := by rw [h1]
      _ = a * m' * fhatA * (a * m')⁻¹ := by group
  · exfalso
    set h : Ah := ⟨wordAP w, wordAP_mem w⟩ with hh
    have h1 : (a⁻¹ * g * a) * h = h * e0A := by
      apply Subtype.ext
      apply eq_of_repL (l := comp l (evalAL w))
      · exact repL_mul hrep (repL_wordAP w)
      · rw [hweq]
        exact repL_mul (repL_wordAP w) repL_e0A
    have h2 : a⁻¹ * g * a = h * e0A * h⁻¹ := by
      calc a⁻¹ * g * a = ((a⁻¹ * g * a) * h) * h⁻¹ := by group
        _ = h * e0A * h⁻¹ := by rw [h1]
    have h3 : Nat.card ↥(Subgroup.centralizer ({a⁻¹ * g * a} : Set Ah)) =
        Nat.card ↥(Subgroup.centralizer ({g} : Set Ah)) :=
      card_centralizer_conj g a⁻¹ ▸ (by simp)
    have h4 : Nat.card ↥(Subgroup.centralizer ({a⁻¹ * g * a} : Set Ah)) =
        Nat.card ↥(Subgroup.centralizer ({e0A} : Set Ah)) := by
      rw [h2]
      exact card_centralizer_conj e0A h
    have := card_cent_e0_lt
    omega

end CFSG.Quasithin.H13.F431.U42Aut
