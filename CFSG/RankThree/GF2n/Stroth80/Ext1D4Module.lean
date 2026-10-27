module

public import CFSG.RankThree.GF2n.Stroth80.Ext1D4H1
public import CFSG.RankThree.GF2n.Stroth80.Ext1D4NFBasis
public import CFSG.RankThree.GF2n.Stroth80.Sec715TriKegel

public section

namespace CFSG.RankThree.GF2n.Stroth80.Ext1D4

open CFSG.LieType.D4Small CFSG.RankThree.GF2n.Stroth80.Tri Module

section General

variable {K : Type*} [Field K] {G : Type*} [Group G] {X : Type*} [AddCommGroup X] [Module K X]
  (ρ : G →* Module.End K X)

theorem exists_minimal_invariant [FiniteDimensional K X] (U : Submodule K X)
    (hU : ∀ g, ∀ x ∈ U, ρ g x ∈ U)
    (hU0 : U ≠ ⊥) : ∃ S ≤ U, (∀ g, ∀ x ∈ S, ρ g x ∈ S) ∧ S ≠ ⊥ ∧
      ∀ S' ≤ S, (∀ g, ∀ x ∈ S', ρ g x ∈ S') → S' = ⊥ ∨ S' = S := by
  classical
  have hex : ∃ n, ∃ S ≤ U, (∀ g, ∀ x ∈ S, ρ g x ∈ S) ∧ S ≠ ⊥ ∧ finrank K S = n :=
    ⟨_, U, le_rfl, hU, hU0, rfl⟩
  obtain ⟨S, hSU, hS, hS0, hSn⟩ := Nat.find_spec hex
  refine ⟨S, hSU, hS, hS0, fun S' hS'S hS' => ?_⟩
  by_cases h0 : S' = ⊥
  · exact Or.inl h0
  · right
    have hle := Nat.find_min' hex ⟨S', hS'S.trans hSU, hS', h0, rfl⟩
    rw [← hSn] at hle
    exact Submodule.eq_of_le_of_finrank_le hS'S hle

theorem finrank_span_fixed {v : X} (hv : v ≠ 0) (hfix : ∀ g, ρ g v = v) :
    (∀ g, ∀ x ∈ K ∙ v, ρ g x ∈ K ∙ v) ∧ K ∙ v ≠ ⊥ ∧ finrank K (K ∙ v) = 1 := by
  refine ⟨fun g x hx => ?_, by simpa using hv, finrank_span_singleton hv⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [map_smul, hfix]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

end General

section Frobenius

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem pow_two_pow_surjective (j : ℕ) : Function.Surjective fun x : K => x ^ 2 ^ j := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Finite.surjective_of_injective fun x y h => ?_
  have h' : (x - y) ^ 2 ^ j = 0 := by
    rw [sub_pow_char_pow]
    exact sub_eq_zero.2 h
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 h')

end Frobenius

section RootScale

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2] (D : D4Datum G K)
  {X : Type*} [AddCommGroup X] [Module K X]

theorem rootScale_of_nf (σ : Representation K G X) {j : ℕ}
    {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X}
    (hb : NF D σ j C b) : ∀ α, IsD4Root α → ∀ (c : K) (y : X),
      σ (D.x α c) y - y = c ^ 2 ^ j • (σ (D.x α 1) y - y) := by
  intro α hα c y
  have key : σ (D.x α c) - 1 = c ^ 2 ^ j • (σ (D.x α 1) - 1) := by
    refine LinearMap.ext_on hb.span_eq ?_
    rintro _ ⟨a, ha, rfl⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      hb.root α hα c a ha, hb.root α hα 1 a ha, one_pow, one_smul, add_sub_cancel_left]
    split_ifs <;> simp
  have := LinearMap.congr_fun key y
  simpa using this

end RootScale

section F2

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  (D : D4Datum G K) {X : Type*} [AddCommGroup X] [Module K X] (ρ : G →* Module.End K X)

theorem addSubgroup_eq_of_rootScale (S : Submodule K X) (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S) (j : ℕ)
    (hroot : ∀ α, IsD4Root α → ∀ (c : K), ∀ y ∈ S,
      ρ (D.x α c) y - y = c ^ 2 ^ j • (ρ (D.x α 1) y - y))
    (hirr : ∀ N ≤ S, (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N = ⊥ ∨ N = S)
    (hnt : ∃ y ∈ S, ∃ g, ρ g y ≠ y) (M : AddSubgroup X) (hMS : M ≤ S.toAddSubgroup)
    (hM : ∀ g, ∀ x ∈ M, ρ g x ∈ M) : M = ⊥ ∨ M = S.toAddSubgroup := by
  classical
  have hdiff : ∀ g, ∀ y ∈ M, ∀ k : K, k • (ρ g y - y) ∈ M := by
    intro g
    have hg : g ∈ Subgroup.closure {g | ∃ α, IsD4Root α ∧ ∃ c, D.x α c = g} := by
      rw [D.closure_eq]; trivial
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨α, hα, c, rfl⟩ := hg
      intro y hy k
      obtain ⟨c', hc'⟩ := pow_two_pow_surjective (K := K) j (k * c ^ 2 ^ j)
      rw [hroot α hα c y (hMS hy), smul_smul, ← hc']
      simp only
      rw [← hroot α hα c' y (hMS hy)]
      exact M.sub_mem (hM _ _ hy) hy
    | one =>
      intro y hy k
      rw [map_one, Module.End.one_apply, sub_self, smul_zero]
      exact M.zero_mem
    | mul g h _ _ ihg ihh =>
      intro y hy k
      have e : ρ (g * h) y - y = ρ g (ρ h y - y) + (ρ g y - y) := by
        rw [map_mul, Module.End.mul_apply, map_sub]
        abel
      rw [e, smul_add, ← map_smul]
      exact M.add_mem (hM _ _ (ihh y hy k)) (ihg y hy k)
    | inv g _ ihg =>
      intro y hy k
      have hy' : ρ g⁻¹ y ∈ M := hM _ _ hy
      have e : ρ g (ρ g⁻¹ y) = y := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      have := M.neg_mem (ihg _ hy' k)
      rw [e, ← smul_neg, neg_sub] at this
      exact this
  by_cases hM0 : M = ⊥
  · exact Or.inl hM0
  right
  obtain ⟨y, hyM, hy0⟩ : ∃ y ∈ M, y ≠ 0 := by
    by_contra h
    exact hM0 (eq_bot_iff.2 fun x hx => (AddSubgroup.mem_bot).2
      (by_contra fun hx0 => h ⟨x, hx, hx0⟩))
  set N := Submodule.span K (Set.range fun g => ρ g y - y) with hN
  have hNS : N ≤ S := Submodule.span_le.2 (by
    rintro _ ⟨g, rfl⟩
    exact S.sub_mem (hS g y (hMS hyM)) (hMS hyM))
  have hNinv : ∀ h, ∀ x ∈ N, ρ h x ∈ N := by
    intro h x hx
    have : N ≤ N.comap (ρ h) := Submodule.span_le.2 (by
      rintro _ ⟨g, rfl⟩
      have e : ρ h (ρ g y - y) = (ρ (h * g) y - y) - (ρ h y - y) := by
        rw [map_sub, map_mul, Module.End.mul_apply]
        abel
      show ρ h (ρ g y - y) ∈ N
      rw [e]
      exact N.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩))
    exact this hx
  have hNM : ∀ x ∈ N, x ∈ M := by
    intro x hx
    have : ∀ k : K, k • x ∈ M := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact fun k => hdiff g y hyM k
      | zero => exact fun k => by rw [smul_zero]; exact M.zero_mem
      | add x z _ _ hx hz => exact fun k => by rw [smul_add]; exact M.add_mem (hx k) (hz k)
      | smul c x _ hx => exact fun k => by rw [smul_smul]; exact hx _
    simpa using this 1
  rcases hirr N hNS hNinv with hN0 | hNS'
  ·
    exfalso
    have hfix : ∀ g, ρ g y = y := fun g => by
      have : ρ g y - y ∈ N := Submodule.subset_span ⟨g, rfl⟩
      rw [hN0, Submodule.mem_bot] at this
      exact sub_eq_zero.1 this
    have hline : K ∙ y ≤ S := (Submodule.span_singleton_le_iff_mem _ _).2 (hMS hyM)
    rcases hirr _ hline (finrank_span_fixed ρ hy0 hfix).1 with h | h
    · exact hy0 (by simpa using h)
    · obtain ⟨z, hz, g, hgz⟩ := hnt
      rw [← h] at hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      exact hgz (by rw [map_smul, hfix])
  · refine le_antisymm hMS fun x hx => hNM x ?_
    rw [hNS']
    exact hx

end F2

section Small

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Fintype K] [CharP K 2]
  (D : D4Datum G K)

theorem IsMinWt.card {W : Finset (Fin 4 → ℤ)} (hW : IsMinWt W) : W.card = 8 := by
  rcases hW with rfl | rfl | rfl <;> decide

theorem exists_wtBasis_of_irreducible (hNF : SmallNFStatement) {f m : ℕ}
    (hf : Fintype.card K = 2 ^ f) (hm : 2 * m = Fintype.card K) (hq : 4 ≤ Fintype.card K)
    {Y : Type} [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] (σ : Representation K G Y)
    (hirr : ∀ S : Submodule K Y, (∀ g, ∀ y ∈ S, σ g y ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : ∃ g, σ g ≠ 1) (hdim : finrank K Y ≤ 16) :
    ∃ a < f, ∃ W, IsMinWt W ∧ ∃ v : Module.Basis W K Y,
      (∀ β ∈ posRoot, ∀ t χ, σ (posX D β t) (v χ) = ∑ ψ, rootElt W β (t ^ 2 ^ a) ψ χ • v ψ) ∧
      (∀ z χ, σ (D.h z) (v χ) = (wtChar m a (χ : Fin 4 → ℤ) z : K) • v χ) ∧
      (∀ α, IsD4Root α → ∀ (c : K) (y : Y),
        σ (D.x α c) y - y = c ^ 2 ^ a • (σ (D.x α 1) y - y)) ∧
      finrank K Y = 8 := by
  obtain ⟨j, C, b, hj, hC, hb⟩ :=
    hNF D (by rw [Nat.card_eq_fintype_card]; exact hq) σ hirr hnt hdim
  obtain ⟨hjf, W, hW, v, hvx, hvh⟩ := exists_basis_of_nf D σ hf hm hq hj hC hb
  refine ⟨j, hjf, W, hW, v, hvx, hvh, rootScale_of_nf D σ hb, ?_⟩
  rw [finrank_eq_card_basis v, Fintype.card_coe, hW.card]

variable {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  (ρ : Representation K G X)

theorem subrep_irreducible {Y : Type} [AddCommGroup Y] [Module K Y] (σ : Representation K G Y)
    (S : Submodule K Y) (hS : ∀ g, S ≤ S.comap (σ g))
    (hmin : ∀ S' ≤ S, (∀ g, ∀ x ∈ S', σ g x ∈ S') → S' = ⊥ ∨ S' = S) :
    ∀ T : Submodule K S, (∀ g, ∀ y ∈ T, σ.subrepresentation S hS g y ∈ T) → T = ⊥ ∨ T = ⊤ := by
  intro T hT
  have hTinv : ∀ g, ∀ x ∈ T.map S.subtype, σ g x ∈ T.map S.subtype := by
    rintro g _ ⟨y, hy, rfl⟩
    exact ⟨_, hT g y hy, rfl⟩
  have hinj := Submodule.map_injective_of_injective (f := S.subtype) S.injective_subtype
  rcases hmin _ (Submodule.map_subtype_le S T) hTinv with h | h
  · left
    apply hinj
    rw [h, Submodule.map_bot]
  · right
    apply hinj
    rw [h, Submodule.map_subtype_top]

end Small

section Compl

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Fintype K] [CharP K 2]
  (D : D4Datum G K) {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  (ρ : Representation K G X)

theorem exists_compl_of_minDim (hNF : SmallNFStatement) {f m : ℕ} (hf : Fintype.card K = 2 ^ f)
    (hm : 2 * m = Fintype.card K) (hq : 4 ≤ Fintype.card K) (hB : ((borel D).index : K) ≠ 0)
    (hdim : finrank K X ≤ 16)
    (hmin : ∀ U : Submodule K X, (∀ g, ∀ x ∈ U, ρ g x ∈ U) → U ≠ ⊥ → 8 ≤ finrank K U)
    (U : Submodule K X) (hU : ∀ g, ∀ x ∈ U, ρ g x ∈ U) (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤) :
    finrank K U = 8 ∧ ∃ C : Submodule K X, IsCompl U C ∧ ∀ g, ∀ x ∈ C, ρ g x ∈ C := by
  classical
  have hline : ∀ v : X, v ≠ 0 → ¬ ∀ g, ρ g v = v := fun v hv hfix => by
    have h := finrank_span_fixed ρ hv hfix
    have := hmin _ h.1 h.2.1
    omega
  obtain ⟨S, hSU, hS, hS0, hSmin⟩ := exists_minimal_invariant ρ U hU hU0
  have hSle : ∀ g, S ≤ S.comap (ρ g) := fun g x hx => hS g x hx
  have hSnt : ∃ g, ρ.subrepresentation S hSle g ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    obtain ⟨y, hyS, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
    refine hline y hy0 fun g => ?_
    have := congrArg (fun φ : Module.End K S => (φ ⟨y, hyS⟩ : X)) (h g)
    simpa using this
  obtain ⟨aS, haS, W₁, hW₁, bS, hbSx, hbSh, -, hSdim⟩ := exists_wtBasis_of_irreducible D hNF hf
    hm hq _ (subrep_irreducible _ S hSle hSmin) hSnt ((Submodule.finrank_le S).trans hdim)
  have hbSx' : ∀ β ∈ posRoot, ∀ t χ,
      ρ (posX D β t) (bS χ) = ∑ ψ, rootElt W₁ β (t ^ 2 ^ aS) ψ χ • (bS ψ : X) :=
    fun β hβ t χ => by simpa using congrArg Subtype.val (hbSx β hβ t χ)
  have hbSh' : ∀ z χ, ρ (D.h z) (bS χ) = (wtChar m aS (χ : Fin 4 → ℤ) z : K) • (bS χ : X) :=
    fun z χ => by simpa using congrArg Subtype.val (hbSh z χ)
  set σQ := ρ.quotient S hSle with hσQdef
  have hσQ : ∀ g (x : X), σQ g (S.mkQ x) = S.mkQ (ρ g x) := fun g x => rfl
  have hQfix : ∀ q : X ⧸ S, (∀ g, σQ g q = q) → q = 0 := by
    intro q hq'
    obtain ⟨v, rfl⟩ := S.mkQ_surjective q
    have hv : ∀ g, ρ g v - v ∈ S := fun g => by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      have := hq' g
      rw [hσQ] at this
      simp only [Submodule.mkQ_apply] at this
      rw [this, sub_self]
    obtain ⟨s, hs, hfix⟩ := exists_add_fixed_of_minWt D hm hq hB ρ S hS hW₁ bS hbSh' v hv
    by_contra hne
    refine hline (v + s) (fun h => hne ?_) hfix
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, eq_neg_of_add_eq_zero_left h]
    exact S.neg_mem hs
  have hQmin : ∀ R : Submodule K (X ⧸ S), (∀ g, ∀ q ∈ R, σQ g q ∈ R) → R ≠ ⊥ →
      8 ≤ finrank K R := by
    intro R hR hR0
    obtain ⟨R₀, hR₀R, hR₀, hR₀0, hR₀min⟩ := exists_minimal_invariant σQ R hR hR0
    have hR₀le : ∀ g, R₀ ≤ R₀.comap (σQ g) := fun g x hx => hR₀ g x hx
    by_cases hRnt : ∃ g, σQ.subrepresentation R₀ hR₀le g ≠ 1
    · obtain ⟨-, -, -, -, -, -, -, -, hRdim⟩ := exists_wtBasis_of_irreducible D hNF hf hm hq _
        (subrep_irreducible _ R₀ hR₀le hR₀min) hRnt
        ((Submodule.finrank_le R₀).trans ((Submodule.finrank_quotient_le S).trans hdim))
      rw [← hRdim]
      exact Submodule.finrank_mono hR₀R
    · exfalso
      simp only [not_exists, not_not] at hRnt
      obtain ⟨q, hqR, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR₀0
      refine hq0 (hQfix q fun g => ?_)
      have := congrArg (fun φ : Module.End K R₀ => (φ ⟨q, hqR⟩ : X ⧸ S)) (hRnt g)
      simpa using this
  have hQdim : finrank K (X ⧸ S) + 8 = finrank K X := by
    rw [← hSdim, Submodule.finrank_quotient_add_finrank]
  have hSne : S ≠ ⊤ := fun h => hU1 (eq_top_iff.2 (h ▸ hSU))
  have hQ0 : (⊤ : Submodule K (X ⧸ S)) ≠ ⊥ := by
    intro h
    have h1 : finrank K (X ⧸ S) = 0 := by
      rw [← finrank_top K (X ⧸ S), h, finrank_bot]
    exact hSne (Submodule.eq_top_of_finrank_eq (by omega))
  have hQirr : ∀ R : Submodule K (X ⧸ S), (∀ g, ∀ q ∈ R, σQ g q ∈ R) → R = ⊥ ∨ R = ⊤ := by
    intro R hR
    by_cases hR0 : R = ⊥
    · exact Or.inl hR0
    · right
      have h8 := hQmin R hR hR0
      exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le R) (by omega))
  have hQnt : ∃ g, σQ g ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    obtain ⟨q, -, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
    exact hq0 (hQfix q fun g => by rw [h g]; rfl)
  obtain ⟨aQ, haQ, W₂, hW₂, bQ, hbQx, hbQh, -, -⟩ := exists_wtBasis_of_irreducible D hNF hf hm hq
    σQ hQirr hQnt (by omega)
  obtain ⟨C, hSC, hC⟩ := exists_invariant_compl_of_datum D hf hm hq hB ρ S hS hW₁ hW₂ haS haQ
    bS hbSx' hbSh' bQ (fun β hβ t χ e he => by rw [← hσQ, he]; exact hbQx β hβ t χ)
    (fun z χ e he => by rw [← hσQ, he]; exact hbQh z χ)
  have hUC : C ⊓ U = ⊥ := by
    by_contra h
    have h8 := hmin (C ⊓ U) (fun g x hx => ⟨hC g x hx.1, hU g x hx.2⟩) h
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq S (C ⊓ U)
    have hdisj : S ⊓ (C ⊓ U) = ⊥ := eq_bot_iff.2 fun x hx => hSC.inf_eq_bot ▸ ⟨hx.1, hx.2.1⟩
    rw [hdisj, finrank_bot, add_zero] at hsum
    have hle : finrank K ↥(S ⊔ C ⊓ U) ≤ finrank K U :=
      Submodule.finrank_mono (sup_le hSU inf_le_right)
    exact hU1 (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le U) (by omega)))
  have hUS : U = S := by
    calc U = (S ⊔ C) ⊓ U := by rw [hSC.sup_eq_top, top_inf_eq]
      _ = S ⊔ C ⊓ U := sup_inf_assoc_of_le C hSU
      _ = S := by rw [hUC, sup_bot_eq]
  subst hUS
  exact ⟨hSdim, C, hSC, hC⟩

end Compl

section AddCompl

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Fintype K] [CharP K 2]
  (D : D4Datum G K) {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  (ρ : Representation K G X)

include D in
theorem addSubgroup_eq_of_irreducible (hNF : SmallNFStatement) {f m : ℕ}
    (hf : Fintype.card K = 2 ^ f) (hm : 2 * m = Fintype.card K) (hq : 4 ≤ Fintype.card K)
    (V : Submodule K X) (hV : ∀ g, ∀ x ∈ V, ρ g x ∈ V)
    (hirr : ∀ V' ≤ V, (∀ g, ∀ x ∈ V', ρ g x ∈ V') → V' = ⊥ ∨ V' = V)
    (hnt : ∃ y ∈ V, ∃ g, ρ g y ≠ y) (hdim : finrank K V ≤ 16) (M : AddSubgroup X)
    (hMV : M ≤ V.toAddSubgroup) (hM : ∀ g, ∀ x ∈ M, ρ g x ∈ M) :
    M = ⊥ ∨ M = V.toAddSubgroup := by
  have hVle : ∀ g, V ≤ V.comap (ρ g) := fun g x hx => hV g x hx
  have hVnt : ∃ g, ρ.subrepresentation V hVle g ≠ 1 := by
    obtain ⟨y, hyV, g, hg⟩ := hnt
    refine ⟨g, fun h => hg ?_⟩
    have := congrArg (fun φ : Module.End K V => (φ ⟨y, hyV⟩ : X)) h
    simpa using this
  obtain ⟨a, -, -, -, -, -, -, hroot, -⟩ := exists_wtBasis_of_irreducible D hNF hf hm hq _
    (subrep_irreducible _ V hVle hirr) hVnt hdim
  refine addSubgroup_eq_of_rootScale D ρ V hV a (fun α hα c y hy => ?_) hirr hnt M hMV hM
  simpa using congrArg Subtype.val (hroot α hα c ⟨y, hy⟩)

theorem exists_addCompl_of_minDim (hNF : SmallNFStatement) {f m : ℕ}
    (hf : Fintype.card K = 2 ^ f) (hm : 2 * m = Fintype.card K) (hq : 4 ≤ Fintype.card K)
    (hB : ((borel D).index : K) ≠ 0) (hdim : finrank K X ≤ 16)
    (hmin : ∀ U : Submodule K X, (∀ g, ∀ x ∈ U, ρ g x ∈ U) → U ≠ ⊥ → 8 ≤ finrank K U)
    (A : AddSubgroup X) (hA : ∀ g, ∀ x ∈ A, ρ g x ∈ A) :
    ∃ A' : AddSubgroup X, IsCompl A A' ∧ ∀ g, ∀ x ∈ A', ρ g x ∈ A' := by
  classical
  have hline : ∀ v : X, v ≠ 0 → ¬ ∀ g, ρ g v = v := fun v hv hfix => by
    have h := finrank_span_fixed ρ hv hfix
    have := hmin _ h.1 h.2.1
    omega
  have hnt : ∀ V : Submodule K X, V ≠ ⊥ → ∃ y ∈ V, ∃ g, ρ g y ≠ y := fun V hV0 => by
    obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
    by_contra h
    exact hline y hy0 fun g => by_contra fun hg => h ⟨y, hyV, g, hg⟩
  have hsmall : ∀ V : Submodule K X, (∀ g, ∀ x ∈ V, ρ g x ∈ V) → finrank K V ≤ 8 →
      ∀ V' ≤ V, (∀ g, ∀ x ∈ V', ρ g x ∈ V') → V' = ⊥ ∨ V' = V := by
    intro V hV hV8 V' hV'V hV'
    by_cases h0 : V' = ⊥
    · exact Or.inl h0
    · exact Or.inr (Submodule.eq_of_le_of_finrank_le hV'V (by have := hmin V' hV' h0; omega))
  have hcompl : ∀ A A' : AddSubgroup X, Disjoint A A' → (∀ x, ∃ a ∈ A, ∃ a' ∈ A', a + a' = x) →
      IsCompl A A' := fun A A' hd hc =>
    ⟨hd, codisjoint_iff.2 (eq_top_iff.2 fun x _ => by
      obtain ⟨a, ha, a', ha', rfl⟩ := hc x
      exact AddSubgroup.add_mem_sup ha ha')⟩
  by_cases hred : ∃ U : Submodule K X, (∀ g, ∀ x ∈ U, ρ g x ∈ U) ∧ U ≠ ⊥ ∧ U ≠ ⊤
  · obtain ⟨U, hU, hU0, hU1⟩ := hred
    obtain ⟨hU8, C, hUC, hC⟩ := exists_compl_of_minDim D ρ hNF hf hm hq hB hdim hmin U hU hU0 hU1
    have hC0 : C ≠ ⊥ := fun h => hU1 (by simpa [h] using hUC.sup_eq_top)
    have hCdim : finrank K C ≤ 8 := by
      have := Submodule.finrank_sup_add_finrank_inf_eq U C
      rw [hUC.sup_eq_top, hUC.inf_eq_bot, finrank_top, finrank_bot, add_zero] at this
      omega
    have hF2U := addSubgroup_eq_of_irreducible D ρ hNF hf hm hq U hU (hsmall U hU hU8.le)
      (hnt U hU0) (by omega)
    have hF2C := addSubgroup_eq_of_irreducible D ρ hNF hf hm hq C hC (hsmall C hC hCdim)
      (hnt C hC0) (by omega)
    have hdec : ∀ x : X, ∃ u ∈ U, ∃ c ∈ C, u + c = x := fun x => by
      have hx : x ∈ U ⊔ C := by rw [hUC.sup_eq_top]; trivial
      obtain ⟨u, hu, c, hc, h⟩ := Submodule.mem_sup.1 hx
      exact ⟨u, hu, c, hc, h⟩
    have hUCz : ∀ x ∈ U, x ∈ C → x = 0 := fun x hU' hC' => by
      have : x ∈ U ⊓ C := ⟨hU', hC'⟩
      rwa [hUC.inf_eq_bot, Submodule.mem_bot] at this
    have hAU : ∀ g, ∀ x ∈ A ⊓ U.toAddSubgroup, ρ g x ∈ A ⊓ U.toAddSubgroup :=
      fun g x hx => ⟨hA g x hx.1, hU g x hx.2⟩
    rcases hF2U (A ⊓ U.toAddSubgroup) inf_le_right hAU with h1 | h1
    ·
      have hAUC : ∀ g, ∀ x ∈ (A ⊔ U.toAddSubgroup) ⊓ C.toAddSubgroup,
          ρ g x ∈ (A ⊔ U.toAddSubgroup) ⊓ C.toAddSubgroup := by
        rintro g x ⟨hx1, hx2⟩
        refine ⟨?_, hC g x hx2⟩
        obtain ⟨a, ha, u, hu, rfl⟩ := AddSubgroup.mem_sup.1 hx1
        rw [map_add]
        exact AddSubgroup.add_mem_sup (hA g a ha) (hU g u hu)
      rcases hF2C _ inf_le_right hAUC with h2 | h2
      ·
        refine ⟨⊤, ?_, fun g x _ => trivial⟩
        have hA0 : A = ⊥ := eq_bot_iff.2 fun x hx => by
          obtain ⟨u, hu, c, hc, rfl⟩ := hdec x
          have hc' : c ∈ (A ⊔ U.toAddSubgroup) ⊓ C.toAddSubgroup := by
            refine ⟨?_, hc⟩
            have : c = (u + c) + -u := by abel
            rw [this]
            exact AddSubgroup.add_mem_sup hx (U.toAddSubgroup.neg_mem hu)
          rw [h2, AddSubgroup.mem_bot] at hc'
          subst hc'
          rw [add_zero] at hx ⊢
          have : u ∈ A ⊓ U.toAddSubgroup := ⟨hx, hu⟩
          rwa [h1] at this
        rw [hA0]
        exact isCompl_bot_top
      ·
        refine ⟨U.toAddSubgroup, hcompl _ _ ?_ fun x => ?_, fun g x hx => hU g x hx⟩
        · rw [disjoint_iff]
          exact h1
        · obtain ⟨u, hu, c, hc, rfl⟩ := hdec x
          have hc' : c ∈ (A ⊔ U.toAddSubgroup) ⊓ C.toAddSubgroup := by rw [h2]; exact hc
          obtain ⟨a, ha, u', hu', hc''⟩ := AddSubgroup.mem_sup.1 hc'.1
          exact ⟨a, ha, u + u', U.add_mem hu hu', by rw [← hc'']; abel⟩
    ·
      have hAC : ∀ g, ∀ x ∈ A ⊓ C.toAddSubgroup, ρ g x ∈ A ⊓ C.toAddSubgroup :=
        fun g x hx => ⟨hA g x hx.1, hC g x hx.2⟩
      have hUA : ∀ u ∈ U, u ∈ A := fun u hu => by
        have : u ∈ U.toAddSubgroup := hu
        rw [← h1] at this
        exact this.1
      rcases hF2C (A ⊓ C.toAddSubgroup) inf_le_right hAC with h2 | h2
      ·
        refine ⟨C.toAddSubgroup, hcompl _ _ ?_ fun x => ?_, fun g x hx => hC g x hx⟩
        · rw [disjoint_iff]
          exact h2
        · obtain ⟨u, hu, c, hc, rfl⟩ := hdec x
          exact ⟨u, hUA u hu, c, hc, rfl⟩
      ·
        refine ⟨⊥, ?_, fun g x hx => by rw [AddSubgroup.mem_bot] at hx ⊢; rw [hx, map_zero]⟩
        have hAtop : A = ⊤ := eq_top_iff.2 fun x _ => by
          obtain ⟨u, hu, c, hc, rfl⟩ := hdec x
          have hcA : c ∈ A ⊓ C.toAddSubgroup := by rw [h2]; exact hc
          exact A.add_mem (hUA u hu) hcA.1
        rw [hAtop]
        exact isCompl_top_bot
  ·
    simp only [not_exists, not_and, not_not] at hred
    by_cases hX : (⊤ : Submodule K X) = ⊥
    · refine ⟨⊤, ?_, fun g x _ => trivial⟩
      have hA0 : A = ⊥ := eq_bot_iff.2 fun x _ => by
        have : x ∈ (⊤ : Submodule K X) := trivial
        rw [hX, Submodule.mem_bot] at this
        rw [this]
        exact AddSubgroup.zero_mem _
      rw [hA0]
      exact isCompl_bot_top
    · have hirr : ∀ V' ≤ (⊤ : Submodule K X), (∀ g, ∀ x ∈ V', ρ g x ∈ V') → V' = ⊥ ∨ V' = ⊤ :=
        fun V' _ hV' => by
          by_cases h0 : V' = ⊥
          · exact Or.inl h0
          · exact Or.inr (hred V' hV' h0)
      rcases addSubgroup_eq_of_irreducible D ρ hNF hf hm hq ⊤ (fun g x _ => trivial) hirr
        (hnt ⊤ hX) ((Submodule.finrank_le _).trans hdim) A le_top hA with h | h
      · refine ⟨⊤, ?_, fun g x _ => trivial⟩
        rw [h]
        exact isCompl_bot_top
      · refine ⟨⊥, ?_, fun g x hx => by rw [AddSubgroup.mem_bot] at hx ⊢; rw [hx, map_zero]⟩
        rw [h, Submodule.top_toAddSubgroup]
        exact isCompl_top_bot

end AddCompl

end CFSG.RankThree.GF2n.Stroth80.Ext1D4
