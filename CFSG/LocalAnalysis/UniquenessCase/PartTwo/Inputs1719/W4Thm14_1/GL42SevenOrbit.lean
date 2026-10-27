module

public import CFSG.LocalAnalysis.GH72.GL42

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GL42Seven

open Subgroup MulAction

variable {U : Type*} [CommGroup U] [Finite U]

omit [Finite U] in
private lemma isPGroup_zpowers_of_orderOf_eq_seven {g : MulAut U} (hg : orderOf g = 7) :
    IsPGroup 7 (zpowers g) :=
  IsPGroup.of_card (by rw [Nat.card_zpowers, hg, pow_one])

omit [Finite U] in
private lemma pow_apply_mem_of_apply_mem {g : MulAut U} {O : Set U} (hO : ∀ v ∈ O, g v ∈ O) :
    ∀ k : ℕ, ∀ v ∈ O, (g ^ k) v ∈ O := by
  intro k
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih =>
    intro v hv
    rw [pow_succ', MulAut.mul_apply U]
    exact hO _ (ih v hv)

omit [Finite U] in
private lemma zpow_apply_mem_of_apply_mem {g : MulAut U} {O : Set U} (hg : orderOf g = 7)
    (hO : ∀ v ∈ O, g v ∈ O) (n : ℤ) {v : U} (hv : v ∈ O) : (g ^ n) v ∈ O := by
  have h7 : g ^ 7 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hn : g ^ n = g ^ (n % 7).toNat := by
    rw [zpow_eq_zpow_emod' n h7, ← Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num)),
      zpow_natCast]
    rfl
  rw [hn]
  exact pow_apply_mem_of_apply_mem hO _ v hv

omit [Finite U] in
theorem zpowers_smul_mem_of_apply_mem {g : MulAut U} {O : Set U} (hg : orderOf g = 7)
    (hO : ∀ v ∈ O, g v ∈ O) : ∀ x : zpowers g, ∀ v ∈ O, x • v ∈ O := by
  rintro ⟨x, hx⟩ v hv
  rw [Subgroup.smul_def, MulAut.smul_def]
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  exact zpow_apply_mem_of_apply_mem hg hO n hv

private def commutatorHom (g : MulAut U) : U →* U :=
  MulEquiv.toMonoidHom g / MonoidHom.id U

omit [Finite U] in
private lemma commutatorHom_apply (g : MulAut U) (u : U) : commutatorHom g u = g u * u⁻¹ := by
  rw [commutatorHom, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_mul_inv]
  rfl

omit [Finite U] in
private lemma mem_commutatorHom_ker {g : MulAut U} {u : U} :
    u ∈ (commutatorHom g).ker ↔ u ∈ fixedBy U g := by
  rw [MonoidHom.mem_ker, commutatorHom_apply, mul_inv_eq_one, MulAction.mem_fixedBy,
    MulAut.smul_def]

theorem card_fixedBy_eq_two (h16 : Nat.card U = 16) {g : MulAut U} (hg : orderOf g = 7) :
    Nat.card (fixedBy U g) = 2 := by
  rcases CFSG.GH72.card_fixedBy_cases_of_prime h16 (r := 7) (by norm_num) (by norm_num) hg with
    h1 | h23
  · rcases h1.2 with h | h <;> omega
  · rcases h23 with h2 | h3
    · exact h2.1
    · omega

theorem eq_one_of_mem_invariant_of_fixed (h16 : Nat.card U = 16) {g : MulAut U}
    (hg : orderOf g = 7) {V : Subgroup U} (hV : Nat.card V = 8) (hgV : ∀ v ∈ V, g v ∈ V) {v : U}
    (hv : v ∈ V) (hfix : g v = v) : v = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmod := CFSG.GH72.ncard_modEq_ncard_inter_fixedPoints (P := zpowers g) (X := U) (p := 7)
    (isPGroup_zpowers_of_orderOf_eq_seven hg) (Set.toFinite (V : Set U))
    (zpowers_smul_mem_of_apply_mem hg hgV)
  rw [CFSG.GH72.fixedPoints_zpowers] at hmod
  have hVn : (V : Set U).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hV
  rw [hVn] at hmod
  have hIle : ((V : Set U) ∩ fixedBy U g).ncard ≤ 2 := by
    have h2 : (fixedBy U g).ncard = 2 := by
      rw [← Nat.card_coe_set_eq]
      exact card_fixedBy_eq_two h16 hg
    rw [← h2]
    exact Set.ncard_le_ncard (Set.inter_subset_right)
  have hI1 : (1 : U) ∈ (V : Set U) ∩ fixedBy U g :=
    ⟨V.one_mem, by rw [MulAction.mem_fixedBy, MulAut.smul_def, map_one]⟩
  have hIpos : 0 < ((V : Set U) ∩ fixedBy U g).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨1, hI1⟩
  have hIcard : ((V : Set U) ∩ fixedBy U g).ncard = 1 := by
    have hmod' : 8 % 7 = ((V : Set U) ∩ fixedBy U g).ncard % 7 := hmod
    omega
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hIcard
  have h1a : (1 : U) = a := by
    rw [ha] at hI1
    exact Set.mem_singleton_iff.mp hI1
  have hvI : v ∈ (V : Set U) ∩ fixedBy U g :=
    ⟨hv, by rw [MulAction.mem_fixedBy, MulAut.smul_def]; exact hfix⟩
  rw [ha] at hvI
  exact (Set.mem_singleton_iff.mp hvI).trans h1a.symm

private lemma card_ker_commutatorHom (h16 : Nat.card U = 16) {g : MulAut U}
    (hg : orderOf g = 7) : Nat.card (commutatorHom g).ker = 2 := by
  rw [← card_fixedBy_eq_two h16 hg]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_commutatorHom_ker)

private lemma card_range_commutatorHom (h16 : Nat.card U = 16) {g : MulAut U}
    (hg : orderOf g = 7) : Nat.card (commutatorHom g).range = 8 := by
  have h := Subgroup.card_ker_mul_card_range (commutatorHom g)
  rw [card_ker_commutatorHom h16 hg, h16] at h
  omega

theorem exists_invariant_card_eight (h16 : Nat.card U = 16) {g : MulAut U} (hg : orderOf g = 7) :
    ∃ V : Subgroup U, Nat.card V = 8 ∧ ∀ v ∈ V, g v ∈ V := by
  refine ⟨(commutatorHom g).range, card_range_commutatorHom h16 hg, ?_⟩
  rintro - ⟨u, rfl⟩
  exact ⟨g u, by rw [commutatorHom_apply, commutatorHom_apply, map_mul, map_inv]⟩

theorem eq_of_invariant_card_eight (h16 : Nat.card U = 16) {g : MulAut U} (hg : orderOf g = 7)
    {V W : Subgroup U} (hV : Nat.card V = 8) (hW : Nat.card W = 8) (hgV : ∀ v ∈ V, g v ∈ V)
    (hgW : ∀ w ∈ W, g w ∈ W) : V = W := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hXinv : ∀ x ∈ ((V ⊓ W : Subgroup U) : Set U),
      g x ∈ ((V ⊓ W : Subgroup U) : Set U) := by
    intro x hx
    obtain ⟨hxV, hxW⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hgV x hxV, hgW x hxW⟩
  have hmod := CFSG.GH72.ncard_modEq_ncard_inter_fixedPoints (P := zpowers g) (X := U) (p := 7)
    (isPGroup_zpowers_of_orderOf_eq_seven hg) (Set.toFinite ((V ⊓ W : Subgroup U) : Set U))
    (zpowers_smul_mem_of_apply_mem hg hXinv)
  rw [CFSG.GH72.fixedPoints_zpowers] at hmod
  have hI : ((V ⊓ W : Subgroup U) : Set U) ∩ fixedBy U g = {1} := by
    ext x
    constructor
    · rintro ⟨hx, hfix⟩
      have hxg : g x = x := by
        rw [MulAction.mem_fixedBy, MulAut.smul_def] at hfix
        exact hfix
      rw [Set.mem_singleton_iff]
      exact eq_one_of_mem_invariant_of_fixed h16 hg hV hgV (Subgroup.mem_inf.mp hx).1 hxg
    · rintro rfl
      exact ⟨Subgroup.one_mem _, by rw [MulAction.mem_fixedBy, MulAut.smul_def, map_one]⟩
  have hmod7 : Nat.card ↥(V ⊓ W) ≡ 1 [MOD 7] := by
    have h1 : ((V ⊓ W : Subgroup U) : Set U).ncard = Nat.card ↥(V ⊓ W) :=
      Nat.card_coe_set_eq _
    rw [hI, h1, Set.ncard_singleton] at hmod
    exact hmod
  have hXcard : Nat.card ↥(V ⊓ W) = 1 ∨ Nat.card ↥(V ⊓ W) = 8 := by
    have hdvd : Nat.card ↥(V ⊓ W) ∣ 8 := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : V ⊓ W ≤ V)
      rwa [hV] at h
    have hle : Nat.card ↥(V ⊓ W) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥(V ⊓ W) := Nat.card_pos
    have hmod' : Nat.card ↥(V ⊓ W) % 7 = 1 % 7 := hmod7
    omega
  rcases hXcard with h1 | h8
  · have hbot : V ⊓ W = ⊥ := by
      rw [Subgroup.eq_bot_iff_card]
      exact h1
    have hinj : Function.Injective (fun p : V × W => (p.1 : U) * p.2) := by
      rintro ⟨v, w⟩ ⟨v', w'⟩ h
      obtain ⟨hv, hw⟩ := CFSG.GH72.eq_of_mul_eq_mul_of_inf_eq_bot hbot v.2 v'.2 w.2 w'.2 h
      exact Prod.ext (Subtype.ext hv) (Subtype.ext hw)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hV, hW, h16] at hle
    omega
  · have hXV : V ⊓ W = V := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
      rw [h8, hV]
    have hXW : V ⊓ W = W := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
      rw [h8, hW]
    exact hXV.symm.trans hXW

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GL42Seven
