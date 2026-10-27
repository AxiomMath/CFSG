module

public import CFSG.Quasithin.Vol2.Ch11SecBNPComp
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

theorem two_mul_card_psl2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [Nat.card_congr
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod p)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), Nat.card_zmod]
  have hg : Nat.gcd 2 (p - 1) = 2 := by
    have : 2 ∣ p - 1 := by
      obtain ⟨r, rfl⟩ := hodd
      exact ⟨r, by omega⟩
    exact Nat.gcd_eq_left this
  rw [show 2 * (2 - 1) / 2 = 1 from rfl, Finset.Icc_self, Finset.prod_singleton, hg, pow_one]
  have h2 : 2 ∣ p * (p ^ 2 - 1) := by
    obtain ⟨r, rfl⟩ := hodd
    refine Dvd.dvd.mul_left ⟨2 * r * r + 2 * r, ?_⟩ _
    have : (2 * r + 1) ^ 2 = 2 * (2 * r * r + 2 * r) + 1 := by ring
    omega
  exact Nat.mul_div_cancel' h2

theorem isSimpleGroup_psl2 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
  CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl
    (Or.inr (by rw [Nat.card_zmod]; omega)) (Or.inr (by rw [Nat.card_zmod]; omega))

theorem nonempty_mulEquiv_of_surjective_of_isQuasisimple {K S : Type} [Group K] [Group S]
    [Finite S] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) {N : Subgroup K} [N.Normal]
    (hN : IsPGroup 2 N) (hQ : CFSG.Open.IsQuasisimple (K ⧸ N)) (f : K →* S)
    (hf : Function.Surjective f) :
    Nonempty (((K ⧸ N) ⧸ Subgroup.center (K ⧸ N)) ≃* S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZS := center_eq_bot_of_nonabelian hS
  have hNf : N ≤ f.ker := by
    have hm : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with h | h
    · intro x hx
      have hx' : f x ∈ N.map f := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at hx'
      exact hx'
    · exfalso
      have hP : IsPGroup 2 S := by
        intro s
        have hs : s ∈ N.map f := by rw [h]; trivial
        obtain ⟨n, hn, rfl⟩ := hs
        obtain ⟨e, he⟩ := hN ⟨n, hn⟩
        exact ⟨e, by rw [← map_pow]; simpa using congrArg (fun x : N => f x) he⟩
      have hnt := hP.center_nontrivial
      rw [hZS] at hnt
      exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hnt
  set Q := K ⧸ N with hQdef
  set g : Q →* S := QuotientGroup.lift N f hNf with hg
  have hgs : Function.Surjective g := by
    intro s
    obtain ⟨x, rfl⟩ := hf s
    exact ⟨QuotientGroup.mk x, rfl⟩
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  have hZg : Subgroup.center Q ≤ g.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have : g z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨q, rfl⟩ := hgs s
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) q]
    rw [hZS, Subgroup.mem_bot] at this
    exact this
  have hgZ : g.ker ≤ Subgroup.center Q := by
    set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
    have hm : (g.ker.map π).Normal :=
      Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (g.ker.map π) with h | h
    · intro x hx
      have hx' : π x ∈ g.ker.map π := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at hx'
      exact (QuotientGroup.eq_one_iff x).mp hx'
    · exfalso
      have hcen : ∀ s : S, ∃ z ∈ Subgroup.center Q, g z = s := by
        intro s
        obtain ⟨x, rfl⟩ := hgs s
        have hx : π x ∈ g.ker.map π := by rw [h]; trivial
        obtain ⟨a, ha, hax⟩ := hx
        refine ⟨a⁻¹ * x, ?_, ?_⟩
        · rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hax
          exact hax
        · rw [map_mul, map_inv, MonoidHom.mem_ker.mp ha, inv_one, one_mul]
      obtain ⟨a, b, hab⟩ := hS
      obtain ⟨z, hz, rfl⟩ := hcen a
      obtain ⟨w, hw, rfl⟩ := hcen b
      apply hab
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) w]
  have heq : g.ker = Subgroup.center Q := le_antisymm hgZ hZg
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hgs)⟩

theorem card_eq_of_surjective_of_isQuasisimple {K S : Type} [Group K] [Group S] [Finite S]
    [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) {N : Subgroup K} [N.Normal]
    (hN : IsPGroup 2 N) (hQ : CFSG.Open.IsQuasisimple (K ⧸ N)) (f : K →* S)
    (hf : Function.Surjective f) :
    Nat.card S = Nat.card ((K ⧸ N) ⧸ Subgroup.center (K ⧸ N)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective_of_isQuasisimple hS hN hQ f hf
  exact (Nat.card_congr e.toEquiv).symm

theorem nonempty_mulEquiv_of_two_surjective {K S S' : Type} [Group K] [Group S] [Group S']
    [Finite S] [Finite S'] [IsSimpleGroup S] [IsSimpleGroup S'] (hS : ∃ a b : S, a * b ≠ b * a)
    (hS' : ∃ a b : S', a * b ≠ b * a) {N : Subgroup K} [N.Normal] (hN : IsPGroup 2 N)
    (hQ : CFSG.Open.IsQuasisimple (K ⧸ N)) (f : K →* S) (hf : Function.Surjective f)
    (f' : K →* S') (hf' : Function.Surjective f') : Nonempty (S ≃* S') := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective_of_isQuasisimple hS hN hQ f hf
  obtain ⟨e'⟩ := nonempty_mulEquiv_of_surjective_of_isQuasisimple hS' hN hQ f' hf'
  exact ⟨e.symm.trans e'⟩

theorem surjective_comp_subtype_of_sup_eq_top {Γ Q : Type} [Group Γ] [Group Q] (φ : Γ →* Q)
    (hφ : Function.Surjective φ) {A C : Subgroup Γ} (hAC : A ⊔ C = ⊤) (hC : C ≤ φ.ker) :
    Function.Surjective (φ.comp A.subtype) := by
  have hCb : C.map φ = ⊥ := (Subgroup.map_eq_bot_iff C).mpr hC
  have htop : A.map φ = ⊤ := by
    rw [← Subgroup.map_top_of_surjective φ hφ, ← hAC, Subgroup.map_sup, hCb, sup_bot_eq]
  intro q
  have hq : q ∈ A.map φ := by rw [htop]; trivial
  obtain ⟨a, ha, rfl⟩ := hq
  exact ⟨⟨a, ha⟩, rfl⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
