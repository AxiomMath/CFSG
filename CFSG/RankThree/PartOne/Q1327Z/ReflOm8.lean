module

public import CFSG.RankThree.PartOne.Q1327Z.Transport
public import CFSG.RankThree.PartOne.Q1327C.BOm8
public import CFSG.RankThree.PartOne.Q1327Z.Refl

public section

namespace CFSG.RankThree.PartOne.Q1327Z

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFR4 CFSG.RankThree.PartOne.Q1327C
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem b3_noncommOK {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Γ : Type} [Group Γ] {T : Subgroup Γ}
    (D : B3Data p T) : NoncommOK p T := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  rintro g hgN S hST hSidx hgS hgT - - c hcT hcS -
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    have h1 : D.c (⟨a, ha⟩ * ⟨b, hb⟩) = D.c (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (D.c.injective h1)
  obtain ⟨x, hxT, hxne⟩ := hgT
  have hxC : x ∈ Subgroup.centralizer (S : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact hTcomm s (hST hs) x hxT
  have hgC : g ∈ Subgroup.centralizer (S : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have := hgS s hs
    calc s * g = (g * s * g⁻¹) * g := by rw [this]
      _ = g * s := by group
  have hnonab : ⁅Subgroup.centralizer (S : Set Γ), Subgroup.centralizer (S : Set Γ)⁆ ≠ ⊥ := by
    intro hbot
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    have := Subgroup.mem_centralizer_iff.1 (hle hxC) g hgC
    apply hxne
    calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [this]
      _ = x := by group
  have hex : ∃ i : Root, S ≤ hypS D.c i := by
    by_contra hno
    push Not at hno
    have hemp : IsEmpty {i : Root // S ≤ hypS D.c i} := ⟨fun i => hno i.1 i.2⟩
    have h1 := D.derived_le S hST (Or.inl hSidx)
    rw [iSup_of_empty] at h1
    exact hnonab (le_bot_iff.1 h1)
  obtain ⟨i, hSi⟩ := hex
  have hSeq : S = hypS D.c i := D.eq_hypS_of_le hp hSidx hSi
  have hBC : D.block i ≤ Subgroup.centralizer (S : Set Γ) := by
    rw [hSeq]
    exact D.block_cent i
  have hcS' : c ∉ hypS D.c i := hSeq ▸ hcS
  set ρ := i with hρ
  let xc : ↥T := ⟨c, hcT⟩
  let a : ZMod p := ρ.vecp p ⬝ᵥ lin D.c xc
  have ha : a ≠ 0 := by
    intro h0
    exact hcS' ⟨xc, h0, rfl⟩
  let n : ZMod p := ρ.vecp p ⬝ᵥ ρ.vecp p
  have hn : n ≠ 0 := by
    intro h0
    have h1 := nsq_mul_eq_zero hp (by omega) ρ (a := 1)
      (by rw [mul_one, ← dot_vecp_vecp_self p ρ]; exact h0)
    exact one_ne_zero h1
  let l : ↥T := D.c.symm (Multiplicative.ofAdd ((a * n⁻¹) • ρ.vecp p))
  have hlin : lin D.c l = (a * n⁻¹) • ρ.vecp p := lin_symm D.c _
  let d : ↥T := xc * l⁻¹
  have hdlin : ρ.vecp p ⬝ᵥ lin D.c d = 0 := by
    show ρ.vecp p ⬝ᵥ lin D.c (xc * l⁻¹) = 0
    rw [lin_mul, lin_inv, hlin, dotProduct_add, dotProduct_neg, dotProduct_smul, smul_eq_mul]
    change a + -(a * n⁻¹ * n) = 0
    rw [mul_assoc, inv_mul_cancel₀ hn, mul_one]
    exact add_neg_cancel a
  have hdS : (d : Γ) ∈ hypS D.c i := ⟨d, hdlin, rfl⟩
  have hlB : (l : Γ) ∈ D.block i := (D.block_T i l).2 ⟨a * n⁻¹, hlin⟩
  have hl1 : (l : Γ) ≠ 1 := by
    intro h1
    have hl1' : l = 1 := Subtype.ext h1
    have h2 : ρ.vecp p ⬝ᵥ lin D.c l = a := by
      rw [hlin, dotProduct_smul, smul_eq_mul]
      change a * n⁻¹ * n = a
      rw [mul_assoc, inv_mul_cancel₀ hn, mul_one]
    rw [hl1', lin_one, dotProduct_zero] at h2
    exact ha h2.symm
  have hdl : Commute (d : Γ) (l : Γ) := hTcomm _ d.2 _ l.2
  have hcdl : c = (d : Γ) * (l : Γ) := by
    have hxdl : d * l = xc := inv_mul_cancel_right xc l
    have h1 : ((d * l : ↥T) : Γ) = (xc : Γ) := congrArg Subtype.val hxdl
    rw [Subgroup.coe_mul] at h1
    exact h1.symm
  obtain ⟨y, hyB, hnc⟩ := exists_noncomm_of_simple (D.block_simple i) (D.block_perfect i)
    (D.block_ne_bot hp i) hlB hl1
  refine ⟨y, hBC hyB, fun hcomm => hnc ?_⟩
  have hBD : D.block i ≤ Subgroup.centralizer (hypS D.c i : Set Γ) := D.block_cent i
  rw [hcdl] at hcomm
  exact (commute_conj_iff hBD hdS hlB hdl hyB).1 hcomm

theorem refl_om8 {G : Type} [Group G] [Finite G] {p : ℕ} {X A₀ F : Subgroup G}
    (h : Q1327.T123Base p X A₀ F) (hm : Om8Cell p X) {t : MulAut ↥F} (ht : t ∈ torusImage F X)
    (hrefl : IsAutReflection p F t) {c₀ : G} (hc₀ : c₀ ∈ autMovedInG F t) (hc₀1 : c₀ ≠ 1) :
    ∃ y ∈ X ⊓ Subgroup.centralizer (autFixedInG F t : Set G), ¬ Commute c₀ (y * c₀ * y⁻¹) := by
  obtain ⟨f, hf1, hpq, hmod⟩ := hm
  obtain ⟨b, c, hbc, ⟨φ₀⟩⟩ := projOmegaMinus_of_statedClassicalModel hmod
  have hel := barF_elem h
  have hcomm : ∀ x ∈ bar X F, ∀ y ∈ bar X F, x * y = y * x := fun x hx y hy => by
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := bar X F)).comm ⟨x, hx⟩ ⟨y, hy⟩)
    simpa using this
  obtain ⟨Γ, _, T, D, ψ, hψ⟩ : ∃ (Γ : Type) (_ : Group Γ) (T : Subgroup Γ) (_ : B3Data p T)
      (ψ : (↥X ⧸ Subgroup.center ↥X) ≃* Γ), (bar X F).map ψ.toMonoidHom = T := by
    rcases hpq with h' | h'
    · exact exists_b3_split hf1 hbc φ₀ h.prime h.five_le h' (bar X F) (barF_card h) (barF_exp h)
        hcomm
    · exact exists_b3_nonsplit hf1 hbc φ₀ h.prime h.five_le h' (bar X F) (barF_card h)
        (barF_exp h) hcomm
  let ε : ↥X →* Γ := ψ.toMonoidHom.comp (proj X)
  have hT : (F.subgroupOf X).map ε = T := by
    rw [← hψ]
    exact (Subgroup.map_map _ _ _).symm
  refine refl_of_quotient h ε (ψ.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ ?_ ht hrefl
    hc₀ hc₀1
  · intro z hz
    have h1 : ψ (proj X z) = 1 := hz
    have h2 : proj X z = 1 := (map_eq_one_iff ψ ψ.injective).1 h1
    exact (QuotientGroup.eq_one_iff z).1 h2
  · rw [hT]
    exact b3_noncommOK h.prime h.five_le D

end CFSG.RankThree.PartOne.Q1327Z
