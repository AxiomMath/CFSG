module

public import CFSG.Quasithin.Background.G2A5Iso
public import CFSG.Quasithin.Recognition.F112J2Split

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.A5Model
open scoped MatrixGroups

namespace F112J2

theorem center_sl_two_eq_bot' {K : Type*} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hchar : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h1 : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * hchar
  have h2 : r = 1 := sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h1)
  subst h2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrz]
  simp

noncomputable def pslEquivSl' (K : Type*) [Field K] [CharP K 2] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.quotientMulEquivOfEq center_sl_two_eq_bot').trans QuotientGroup.quotientBot

theorem nonempty_psl_four_equiv_alt5 :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2) ≃* A5) := by
  obtain ⟨e⟩ := sl2_four_equiv_alt5 (GaloisField 2 2) card_gf4 card_sl2_gf4
  exact ⟨(pslEquivSl' (GaloisField 2 2)).trans e⟩

theorem a5_two_trans {a b c d : Fin 5} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : A5, (g : Equiv.Perm (Fin 5)) a = c ∧ (g : Equiv.Perm (Fin 5)) b = d := by
  have h3 := alternatingGroup.isMultiplyPretransitive (Fin 5)
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 5)) (Fin 5) 2 :=
    MulAction.isMultiplyPretransitive_of_le (m := 2) (n := 3) (by omega) (by simp)
  obtain ⟨g, hg1, hg2⟩ := MulAction.is_two_pretransitive_iff.mp h2 hab hcd
  exact ⟨g, hg1, hg2⟩

theorem a5_trans (a c : Fin 5) : ∃ g : A5, (g : Equiv.Perm (Fin 5)) a = c := by
  by_cases hac : a = c
  · exact ⟨1, by simp [hac]⟩
  · obtain ⟨g, hg1, -⟩ := a5_two_trans (a := a) (b := c) (c := c) (d := a) hac (Ne.symm hac)
    exact ⟨g, hg1⟩

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem exists_theta (h : R1SettingLegacyBare K1 L2 S Zs) (hL24 : IsL2Quot 2 (OTwoQuot K1)) :
    ∃ θ : ↥K1 →* A5, Function.Surjective θ ∧ ∀ k : ↥K1, θ k ∈ A4s ↔ (k : G) ∈ borelOf K1 S := by
  classical
  obtain ⟨e1⟩ := hL24
  obtain ⟨e2⟩ := nonempty_psl_four_equiv_alt5
  let e : OTwoQuot K1 ≃* A5 := e1.trans e2
  let N : Subgroup ↥K1 := CFSG.Open.pCore 2 ↥K1
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  let θ₀ : ↥K1 →* A5 := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hθ₀s : Function.Surjective θ₀ := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker₀ : θ₀.ker = N := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact QuotientGroup.ker_mk' N
  have hsyl := h.hyp.h1.sylow
  let S1 : Subgroup ↥K1 := (S ⊓ K1).subgroupOf K1
  have hS1p : IsPGroup 2 S1 := by
    intro x
    obtain ⟨n, hn⟩ := h.hyp.h1.pgroup ⟨(x : ↥K1).1, (Subgroup.mem_subgroupOf.mp x.2).1⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hn
  have hS1i : ¬ 2 ∣ S1.index := hsyl.2.2
  have hNle : N ≤ S1 := by
    intro x hx
    have hmem : (x : G) ∈ pCoreOf 2 K1 := ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (isSylowTwoOf_pCoreOf_le hsyl hmem)
  have hP0p : IsPGroup 2 (S1.map θ₀) := hS1p.map θ₀
  have hP0i : ¬ 2 ∣ (S1.map θ₀).index := fun hd =>
    hS1i (dvd_trans hd (Subgroup.index_map_dvd S1 hθ₀s))
  have hK4p : IsPGroup 2 ↥K4 := IsPGroup.of_card (n := 2) (by rw [card_K4]; norm_num)
  have hK4i : ¬ 2 ∣ K4.index := odd_index_of_card_four K4 card_A5 card_K4
  obtain ⟨g, hg⟩ := exists_conj_eq_of_isPGroup_of_odd_index hP0p hP0i hK4p hK4i
  let θ : ↥K1 →* A5 := (MulAut.conj g).toMonoidHom.comp θ₀
  have hθs : Function.Surjective θ := (MulAut.conj g).surjective.comp hθ₀s
  have hθS1 : S1.map θ = K4 := by
    have : S1.map θ = (S1.map θ₀).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_map]
    rw [this, hg]
  have hker : θ.ker = N := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective]
    exact hker₀
  have key : ∀ k : ↥K1, θ k ∈ A4s → ∀ s : ↥K1, s ∈ S1 → k * s * k⁻¹ ∈ S1 := by
    intro k hk s hs
    have h1 : θ s ∈ K4 := hθS1 ▸ Subgroup.mem_map_of_mem θ hs
    have h2 : θ (k * s * k⁻¹) ∈ K4 := by
      rw [map_mul, map_mul, map_inv]
      exact K4_norm _ hk _ h1
    rw [← hθS1] at h2
    obtain ⟨s'', hs'', hs''e⟩ := h2
    have hmem : (k * s * k⁻¹) * s''⁻¹ ∈ N := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hs''e, mul_inv_cancel]
    have := S1.mul_mem (hNle hmem) hs''
    simpa using this
  refine ⟨θ, hθs, ?_⟩
  · intro k
    constructor
    · intro hk
      refine Subgroup.mem_inf.mpr ⟨k.2, ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hfwd : ∀ (k' : ↥K1), θ k' ∈ A4s → ∀ x : G, x ∈ S ⊓ K1 → (k' : G) * x * (k' : G)⁻¹ ∈ S ⊓ K1 := by
        intro k' hk' x hx
        have := key k' hk' ⟨x, hx.2⟩ (Subgroup.mem_subgroupOf.mpr hx)
        exact Subgroup.mem_subgroupOf.mp this
      constructor
      · intro hx
        exact hfwd k hk x hx
      · intro hx
        have hk' : θ k⁻¹ ∈ A4s := by
          rw [map_inv]
          exact A4s.inv_mem hk
        have := hfwd k⁻¹ hk' _ hx
        simpa [mul_assoc] using this
    · intro hk
      have hkN := (Subgroup.mem_inf.mp hk).2
      apply mem_A4s_of_normalizes_K4
      intro q hq
      rw [← hθS1] at hq
      obtain ⟨s, hs, rfl⟩ := hq
      rw [← map_inv, ← map_mul, ← map_mul, ← hθS1]
      refine ⟨k * s * k⁻¹, ?_, rfl⟩
      have hs' : (s : G) ∈ S ⊓ K1 := Subgroup.mem_subgroupOf.mp hs
      have := (Subgroup.mem_normalizer_iff.mp hkN _).mp hs'
      refine Subgroup.mem_subgroupOf.mpr ?_
      simpa using this

end F112J2

end CFSG.Quasithin
