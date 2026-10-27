module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingElementaryCore

public section

namespace CFSG.RankThree.PartOne.Lifting36

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.RankThree.PartOne.Quotient36 SemidirectProduct
open scoped IsMulCommutative commutatorElement

variable {p q d : ℕ} {S : Type*} [Group S] {A : Type*} [Group A] {φ : A →* MulAut S}

theorem whole_group_lifting_core [Finite S] [IsElementaryAbelian 2 S] [Finite A]
    [IsElementaryAbelian p A] {D : Type*} [Group D] [Finite D] [MulDistribMulAction (S ⋊[φ] A) D]
    (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hpd : (p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4)) (hS : Nat.card S = 2 ^ d)
    (hφ : Nat.card φ.range = p)
    (hirr : ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hDq : IsPGroup q D) (hDexp : ∀ x : D, x ^ q = 1) (hDcl : commutator D ≤ Subgroup.center D)
    (hfaith : ∀ s : S, (∀ x : D, (inl s : S ⋊[φ] A) • x = x) → s = 1)
    (hrank : ∀ s : S, s ≠ 1 →
      CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) D) ≤ 3) :
    IsElementaryAbelian q D ∧ Nat.card D = q ^ p ∧
    (∀ Y : Subgroup D, (∀ γ : S ⋊[φ] A, ∀ y ∈ Y, γ • y ∈ Y) → Y = ⊥ ∨ Y = ⊤) ∧
    (p = 7 → ∀ s : S, s ≠ 1 →
      CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) D) = 3) ∧
    (p = 5 →
      Set.ncard {s : S | s ≠ 1 ∧
        CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) D) = 3} = 10 ∧
      Set.ncard {s : S | s ≠ 1 ∧
        CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) D) = 1} = 5) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q D) := ⟨hDq⟩
  have hq2' : (2 : ZMod q) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h1)
  have hNZ : NeZero (Nat.card (S ⋊[φ] A) : ZMod q) :=
    ⟨by rw [Ne, ZMod.natCast_eq_zero_iff]; exact not_dvd_card_semidirect hp hq hq2 hpq hS⟩
  let ρ : Representation (ZMod q) (S ⋊[φ] A) (Additive (D ⧸ frattini D)) :=
    frattiniRep (E := S ⋊[φ] A) (X := D) q
  have hdim4 : ∀ s : S, s ≠ 1 →
      Module.finrank (ZMod q) ↥(Module.End.eigenspace (ρ (inl s)) 1) ≤ 4 := fun s hs =>
    dim_fixed_le_four hq hq2 hS hDq hDexp hDcl hrank s hs
  have hS1 : ∃ s : S, s ≠ 1 := by
    have : 1 < Nat.card S := by
      rcases hpd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rw [hS] <;> norm_num
    obtain ⟨a, b, hab⟩ := Finite.one_lt_card_iff_nontrivial.mp this |>.exists_pair_ne
    by_cases ha : a = 1
    · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  have hnt : ∃ s : S, ∃ v, ρ (inl s) v ≠ v := by
    obtain ⟨s, hs1⟩ := hS1
    obtain ⟨x, hx⟩ : ∃ x : D, (inl s : S ⋊[φ] A) • x ≠ x := by
      by_contra h
      push Not at h
      exact hs1 (hfaith s h)
    by_contra hcon
    push Not at hcon
    have htriv : ∀ y : D, (((inl s : S ⋊[φ] A) • y : D) : D ⧸ frattini D) =
        (y : D ⧸ frattini D) := fun y => by
      have h1 := frattiniRep_apply_mk (E := S ⋊[φ] A) (X := D) q (inl s) y
      have h2 := hcon s (Additive.ofMul (y : D ⧸ frattini D))
      exact Additive.ofMul.injective (h1.symm.trans h2)
    exact hx (smul_eq_of_smul_mk_eq hDq (inl s) (not_dvd_orderOf_inl hq hq2 hS s) htriv x)
  obtain ⟨W, F₀, hWatom, hcompl, hF₀triv, hdimW, hdimF₀, ⟨s₃, hs₃, hd₃⟩, h1le, h7, h5, n, v, c,
    hspan, heig, hsign, hdist⟩ := rep_summary hpd hS hφ hirr hq2' ρ hdim4 hnt
  have hlift : ∀ s : S, s ≠ 1 → ∃ x : D, (inl s : S ⋊[φ] A) • x = x ∧ x ∉ frattini D := by
    intro s hs
    have h := h1le s hs
    have hne : W.toSubmodule ⊓ Module.End.eigenspace (ρ (inl s)) 1 ≠ ⊥ := fun h0 => by
      rw [h0, finrank_bot] at h
      omega
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact exists_fixed_lift hq hq2 hS hDq s w hw0
      (by simpa [Module.End.mem_eigenspace_iff] using hw.2)
  have hfixc := commutator_fixed hpd hq hq2 hS hφ hirr hDq hDexp hDcl hrank hlift
  have hab := abelian_of_family hq2' hq2 hDexp hDcl hfixc v c hspan heig hsign hdist
  have hcommD : IsMulCommutative D :=
    ⟨⟨fun a b => commutatorElement_eq_one_iff_mul_comm.mp (hab a b)⟩⟩
  have hEA : IsElementaryAbelian q D :=
    { toIsMulCommutative := hcommD
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hDexp }
  have hΦ : frattini D = ⊥ := frattini_eq_bot_of_isElementaryAbelian (R := D) (p := q)
  have hfixrank : ∀ s : S, CFSG.pRank q (fixedPointSubgroup
      (Subgroup.zpowers (inl s : S ⋊[φ] A)) D) =
      Module.finrank (ZMod q) ↥(Module.End.eigenspace (ρ (inl s)) 1) := fun s =>
    pRank_fixed_eq_finrank hq2 hS s
  have hF₀bot : F₀ = ⊥ := by
    by_contra hne
    have hpos : 1 ≤ Module.finrank (ZMod q) F₀.toSubmodule :=
      Submodule.one_le_finrank_iff.mpr fun h' => hne (Subrepresentation.ext h')
    have hdisj : (W.toSubmodule ⊓ Module.End.eigenspace (ρ (inl s₃)) 1) ⊓ F₀.toSubmodule = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ W ⊓ F₀ := ⟨hx.1.1, hx.2⟩
      rw [inf_comm, hcompl.inf_eq_bot] at this
      exact this
    have hF₀le : F₀.toSubmodule ≤ Module.End.eigenspace (ρ (inl s₃)) 1 := by
      intro x hx
      rw [Module.End.mem_eigenspace_iff, one_smul]
      exact hF₀triv s₃ x hx
    have h4 := finrank_add_le (inf_le_right : W.toSubmodule ⊓
      Module.End.eigenspace (ρ (inl s₃)) 1 ≤ Module.End.eigenspace (ρ (inl s₃)) 1) hF₀le hdisj
    have h3 := hrank s₃ hs₃
    rw [hfixrank] at h3
    omega
  have hWtop : W = ⊤ := by
    have h1 : F₀ ⊔ W = ⊤ := hcompl.sup_eq_top
    rw [hF₀bot, bot_sup_eq] at h1
    exact h1
  have hWtop' : W.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule hWtop
  have hWeig : ∀ s : S, W.toSubmodule ⊓ Module.End.eigenspace (ρ (inl s)) 1 =
      Module.End.eigenspace (ρ (inl s)) 1 := fun s => by rw [hWtop', top_inf_eq]
  have hfin : Module.finrank (ZMod q) (Additive (D ⧸ frattini D)) = p := by
    have h := congrArg (fun N : Submodule (ZMod q) (Additive (D ⧸ frattini D)) =>
      Module.finrank (ZMod q) ↥N) hWtop'
    simp only [finrank_top] at h
    rw [← h]
    exact hdimW
  have hDF : Nat.card D = Nat.card (D ⧸ frattini D) := by
    rw [hΦ]
    exact (Subgroup.index_bot (G := D)).symm
  have hcard : Nat.card D = q ^ p := by
    have h1 := hDF
    have h2 : Nat.card (Additive (D ⧸ frattini D)) =
        q ^ Module.finrank (ZMod q) (Additive (D ⧸ frattini D)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
    rw [h1, ← hfin]
    exact h2
  have hmkinj : Function.Injective (QuotientGroup.mk' (frattini D)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hΦ]
  have hirrD : ∀ Y : Subgroup D, (∀ γ : S ⋊[φ] A, ∀ y ∈ Y, γ • y ∈ Y) → Y = ⊥ ∨ Y = ⊤ := by
    intro Y hY
    let T : Subgroup (D ⧸ frattini D) := Y.map (QuotientGroup.mk' (frattini D))
    let U : Subrepresentation ρ :=
      { toSubmodule := toSubmodule q T
        apply_mem_toSubmodule := fun γ w hw => by
          rw [mem_toSubmodule] at hw ⊢
          obtain ⟨y, hy, hyw⟩ := hw
          have h1 := frattiniRep_apply_mk (E := S ⋊[φ] A) (X := D) q γ y
          have hw' : w = Additive.ofMul (y : D ⧸ frattini D) := by
            have : Additive.toMul w = (y : D ⧸ frattini D) := hyw.symm
            rw [← this]
            rfl
          have h2 : ρ γ w = Additive.ofMul (((γ • y : D)) : D ⧸ frattini D) := by
            rw [hw']
            exact h1
          rw [h2, toMul_ofMul]
          exact ⟨γ • y, hY γ y hy, rfl⟩ }
    have hUle : U ≤ W := by rw [hWtop]; exact le_top
    rcases hWatom.le_iff.mp hUle with h0 | h1
    · left
      have hT : T = ⊥ := by
        rw [← toSubgroup_toSubmodule q T]
        exact (toSubgroup_eq_bot_iff q _).mpr (congrArg Subrepresentation.toSubmodule h0)
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      have : QuotientGroup.mk' (frattini D) y ∈ T := ⟨y, hy, rfl⟩
      rw [hT, Subgroup.mem_bot] at this
      have h2 : y ∈ frattini D := (QuotientGroup.eq_one_iff y).mp this
      rwa [hΦ, Subgroup.mem_bot] at h2
    · right
      have hT : T = ⊤ := by
        rw [← toSubgroup_toSubmodule q T]
        exact (toSubgroup_eq_top_iff q _).mpr
          ((congrArg Subrepresentation.toSubmodule h1).trans hWtop')
      rw [Subgroup.eq_top_iff']
      intro e
      have : QuotientGroup.mk' (frattini D) e ∈ T := by rw [hT]; exact Subgroup.mem_top _
      obtain ⟨y, hy, hye⟩ := this
      have := hmkinj hye
      rw [← this]
      exact hy
  refine ⟨hEA, hcard, hirrD, ?_, ?_⟩
  · intro hp7 s hs
    rw [hfixrank s, ← hWeig s]
    exact h7 hp7 s hs
  · intro hp5
    obtain ⟨c1, c2⟩ := h5 hp5
    constructor
    · rw [← c1]
      congr 1
      ext s
      simp only [Set.mem_ofPred_eq, hfixrank s]
      rw [hWeig s]
    · rw [← c2]
      congr 1
      ext s
      simp only [Set.mem_ofPred_eq, hfixrank s]
      rw [hWeig s]

end CFSG.RankThree.PartOne.Lifting36
