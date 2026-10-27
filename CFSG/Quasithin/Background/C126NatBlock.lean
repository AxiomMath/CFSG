module

public import CFSG.Quasithin.Background.C126NatSL2
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.E2Three

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B2F E2

section Family

variable {W : Type*} [CommGroup W]

theorem card_perm_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]; rfl

theorem twoPart_card_one_hundred_twenty {Γ : Type*} [Group Γ] (L : Subgroup Γ)
    (h : Nat.card L = 120) : twoPart L = 8 := by
  have h120 : (120 : ℕ) = 2 ^ 3 * 15 := by norm_num
  have h3 : Nat.factorization 120 2 = 3 := by
    rw [h120, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 15 by norm_num)]
  unfold twoPart
  rw [h, h3]
  norm_num

theorem six_le_card_of_type {L : Subgroup (MulAut W)} {C : Subgroup W}
    (h : (∃ n, IsL2Natural L C n) ∨ IsA5Module L) : 6 ≤ Nat.card L := by
  rcases h with ⟨n, hn1, F, iF, iFin, hF, e, -⟩ | ⟨θ, -⟩
  · have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
    have hc := Nat.card_congr e.toEquiv
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hq] at hc
    rw [hc]
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    have h4 : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    calc 6 = 2 * 3 := by norm_num
      _ ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h2 (by omega)
  · have hc := Nat.card_congr θ.toEquiv
    rw [card_perm_five] at hc
    omega

theorem all_natural_or_all_a5 {I : Finset (Subgroup (MulAut W))} {C : Subgroup W}
    (htrans : ∀ L ∈ I, ∀ L' ∈ I, ∃ t : MulAut W, B1.conjAut t L = L')
    (htype : ∀ L ∈ I, (∃ n, IsL2Natural L C n) ∨ IsA5Module L) :
    (∀ L ∈ I, ∃ n, IsL2Natural L C n) ∨ (∀ L ∈ I, IsA5Module L) := by
  by_cases hall : ∀ L ∈ I, ∃ n, IsL2Natural L C n
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨L₀, hL₀, hn0⟩ := hall
  have hA0 : IsA5Module L₀ := (htype L₀ hL₀).resolve_left (by simpa using hn0)
  intro L hL
  by_contra hA
  obtain ⟨n, hnat⟩ := (htype L hL).resolve_right hA
  obtain ⟨t, ht⟩ := htrans L₀ hL₀ L hL
  have hc : Nat.card L = 120 := by
    rw [← ht, B1.card_conjAut]
    obtain ⟨θ, -⟩ := hA0
    rw [Nat.card_congr θ.toEquiv, card_perm_five]
  obtain ⟨hn1, F, iF, iFin, hF, e, -⟩ := hnat
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  apply card_sl2_ne_one_hundred_twenty hn1 hq
  rw [← Nat.card_congr e.toEquiv, hc]

end Family

section Single

variable {G : Type} [Group G] [Finite G]

theorem single_block_aux {P S MP V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : MinParabolic P S MP) (hPN : P ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hV)))} (hKJ : twoResidual P ≤ thompsonJ P)
    (hcard : I.card = 1 ∨ I.card = 2) (hJeq : autI hV (thompsonJ P) = ⨆ L ∈ I, L)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (htrans : ∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ autI hV S, B1.conjAut t L = L')
    (hSb : autI hV S = autI hV (thompsonJ S)) (hLne : ∀ L ∈ I, L ≠ ⊥) :
    ∃ L, I = {L} ∧ autI hV P = L := by
  classical
  have hSP : S ≤ P := h.isSylow.1
  have hSJ : autI hV S ≤ ⨆ L ∈ I, L :=
    hSb ▸ ((autI_mono hV (B6.thompsonJ_le_of_sylow h.isSylow)).trans hJeq.le)
  have hI : ∃ L, I = {L} := by
    rcases hcard with h1 | h2
    · exact Finset.card_eq_one.1 h1
    · exfalso
      obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.1 h2
      have hm₁ : L₁ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hV)))) := by simp
      have hm₂ : L₂ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hV)))) := by simp
      obtain ⟨t, ht1, ht2⟩ := htrans L₁ hm₁ L₂ hm₂
      have hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := hcomm L₁ hm₁ L₂ hm₂ hne
      have hsup2 : (⨆ L ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hV)))), L) = L₁ ⊔ L₂ := by
        apply le_antisymm
        · refine iSup₂_le fun L hL => ?_
          rcases Finset.mem_insert.1 hL with rfl | hL
          · exact le_sup_left
          · rw [Finset.mem_singleton.1 hL]
            exact le_sup_right
        · exact sup_le (le_iSup₂_of_le L₁ hm₁ le_rfl) (le_iSup₂_of_le L₂ hm₂ le_rfl)
      have htsup : t ∈ L₁ ⊔ L₂ := hsup2 ▸ hSJ ht1
      have hxfix : ∀ a ∈ L₁, ∀ y ∈ L₂, a * y * a⁻¹ = y := fun a ha y hy => by
        rw [hc a ha y hy, mul_inv_cancel_right]
      have hnormL₂ : L₁ ≤ Subgroup.normalizer (L₂ : Set (MulAut (IntMod V hV))) := fun a ha => by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hxL
          rwa [hxfix a ha x hxL]
        · intro hxL
          have h1 := hxfix a⁻¹ (L₁.inv_mem ha) _ hxL
          have h2 : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
          rw [h2] at h1
          rw [h1]
          exact hxL
      obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hnormL₂).1 htsup
      have hinf : L₁ ⊓ L₂ = ⊥ := by
        refine le_bot_iff.1 ((inf_le_inf_left L₁ ?_).trans (hind L₁ hm₁).le)
        exact le_iSup₂_of_le L₂ hm₂ (le_iSup (fun _ : L₂ ≠ L₁ => L₂) hne.symm)
      apply hLne L₂ hm₂
      rw [eq_bot_iff]
      intro x hx
      have h1 : x ∈ B1.conjAut (a * b) L₁ := ht2 ▸ hx
      rw [B1.mem_conjAut] at h1
      have h2 : (a * b)⁻¹ * x * (a * b) ∈ L₂ := by
        have h3 : (a * b)⁻¹ * x * (a * b) = b⁻¹ * x * b := by
          have h4 := hxfix a⁻¹ (L₁.inv_mem ha) x hx
          calc (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
            _ = b⁻¹ * x * b := by
              have : a⁻¹ * x * a = x := by simpa using h4
              rw [this]
        rw [h3]
        exact L₂.mul_mem (L₂.mul_mem (L₂.inv_mem hb) hx) hb
      have h5 : (a * b)⁻¹ * x * (a * b) ∈ L₁ ⊓ L₂ := ⟨h1, h2⟩
      rw [hinf, Subgroup.mem_bot] at h5
      have : x = 1 := by
        have h6 : x = (a * b) * ((a * b)⁻¹ * x * (a * b)) * (a * b)⁻¹ := by group
        rw [h6, h5]
        group
      exact (Subgroup.mem_bot).2 this
  obtain ⟨L, rfl⟩ := hI
  refine ⟨L, rfl, ?_⟩
  have hJL : autI hV (thompsonJ P) = L := by simpa using hJeq
  apply le_antisymm
  · rw [← sup_twoResidual_eq h.isSylow,
      autI_sup hV (hSP.trans hPN) ((twoResidual_le P).trans hPN)]
    refine sup_le ?_ ?_
    · rw [hSb]
      exact (autI_mono hV (B6.thompsonJ_le_of_sylow h.isSylow)).trans hJL.le
    · exact (autI_mono hV hKJ).trans hJL.le
  · rw [← hJL]
    exact autI_mono hV (B6.thompsonJ_le P)

theorem exists_single_block_e23 {P S MP V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : MinParabolic P S MP) (hS : baum S = S) (hPN : P ≤ Subgroup.normalizer (V : Set G))
    (hc : E23Concl P S V hV) :
    ∃ (L : Subgroup (MulAut (IntMod V hV))) (n : ℕ),
      autI hV P = L ∧ IsL2Natural L (fixV (autI hV (twoResidual P))) n := by
  obtain ⟨hKJ, I, hcard, hJeq, hcomm, hind, htrans, htype, -, -, h2, h3⟩ := hc
  have hLne : ∀ L ∈ I, L ≠ ⊥ := by
    intro L hL hbot
    have h6 := six_le_card_of_type (htype L hL)
    rw [hbot, Subgroup.card_bot] at h6
    omega
  have htrans' : ∀ L ∈ I, ∀ L' ∈ I, ∃ t : MulAut (IntMod V hV), B1.conjAut t L = L' :=
    fun L hL L' hL' => (htrans L hL L' hL').imp fun t ht => ht.2
  rcases all_natural_or_all_a5 htrans' htype with hall | hall
  · obtain ⟨hSb, -⟩ := h2 hall
    rw [hS] at hSb
    obtain ⟨L, hI, hPL⟩ := single_block_aux hV h hPN hKJ hcard hJeq hcomm hind htrans hSb hLne
    obtain ⟨n, hn⟩ := hall L (hI ▸ Finset.mem_singleton_self L)
    exact ⟨L, n, hPL, hn⟩
  · exfalso
    obtain ⟨hSb, hJT, hc4⟩ := h3 hall
    rw [hS] at hSb
    obtain ⟨L, hI, hPL⟩ := single_block_aux hV h hPN hKJ hcard hJeq hcomm hind htrans hSb hLne
    have hLI : L ∈ I := hI ▸ Finset.mem_singleton_self L
    obtain ⟨hcard4, -⟩ := hc4 L hLI
    have hJL : autI hV (thompsonJ S) = L ⊓ autI hV (thompsonJ S) :=
      calc autI hV (thompsonJ S) = ⨆ L' ∈ I, (L' ⊓ autI hV (thompsonJ S)) := hJT
        _ = L ⊓ autI hV (thompsonJ S) := by rw [hI]; simp
    have hS4 : Nat.card (autI hV S) = 4 := by rw [hSb, hJL]; exact hcard4
    have hsyl := isSylowTwoOf_autI hV hPN h.isSylow
    obtain ⟨θ, -⟩ := hall L hLI
    have hc120 : Nat.card L = 120 := by rw [Nat.card_congr θ.toEquiv, card_perm_five]
    have h8 : Nat.card (autI hV S) = 8 := by
      rw [hsyl.card_eq, hPL]
      exact twoPart_card_one_hundred_twenty L hc120
    omega

end Single

end CFSG.Quasithin.C126.Nat
