module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompModel
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint Matrix CFSG.SeitzReduction.LinearPilot

namespace LinTorus

variable {m : ℕ} {F : Type} [Field F] {G : Type} [Group G]

theorem exists_scalar_diag_mul [CharP F 2] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {δ : G → Fin (m + 1) → Fˣ} {e e' : G}
    (he : (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ)
    (he' : (e', InnerDiagA.diagGL (δ e')) ∈ LinFusion.ggInducedPairs ψ)
    (hee' : (e * e', InnerDiagA.diagGL (δ (e * e'))) ∈ LinFusion.ggInducedPairs ψ) :
    ∃ c : Fˣ, ∀ k, δ (e * e') k = c * (δ e k * δ e' k) := by
  have hmul := (LinFusion.ggInducedPairs ψ).mul_mem he he'
  rw [Prod.mk_mul_mk, ← LinFusion.diagGL_mul] at hmul
  obtain ⟨c, hc⟩ := exists_scalar_mul_of_mem_ggInducedPairs hker hmul hee'
  refine ⟨c, fun k => Units.ext ?_⟩
  have h := congrArg (fun A : GL (Fin (m + 1)) F => (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k k)
    hc
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, InnerDiagA.coe_diagGL, scalar_apply,
    diagonal_mul_diagonal, diagonal_apply_eq, Pi.mul_apply] at h
  rw [h, Units.val_mul, Units.val_mul]

@[expose] noncomputable def ratioChar [CharP F 2]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {E : Subgroup G} {δ : G → Fin (m + 1) → Fˣ}
    (hδE : ∀ e ∈ E, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ)
    (i j : Fin (m + 1)) : E →* Fˣ :=
  MonoidHom.mk' (fun e => δ (e : G) i / δ (e : G) j) fun a b => by
    obtain ⟨c, hc⟩ := exists_scalar_diag_mul hker (hδE a a.2) (hδE b b.2) (hδE _ (a * b).2)
    change δ ((a : G) * b) i / δ ((a : G) * b) j = _
    rw [hc i, hc j, mul_div_mul_left_eq_div, mul_div_mul_comm]

theorem ratioChar_apply [CharP F 2] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {E : Subgroup G} {δ : G → Fin (m + 1) → Fˣ}
    (hδE : ∀ e ∈ E, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ)
    (i j : Fin (m + 1)) (e : E) : ratioChar hker hδE i j e = δ (e : G) i / δ (e : G) j :=
  rfl

theorem relIndex_centralizer_le_of_card_two [CharP F 2] [Finite F] [Finite G] {p : ℕ}
    [NeZero p] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {E : Subgroup G} (hE : ∀ e ∈ E, e ^ p = 1) {δ : G → Fin (m + 1) → Fˣ}
    (hδE : ∀ e ∈ E, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ)
    {i j : Fin (m + 1)} {J : Subgroup G}
    (hJ : J ≤ (blockSpecialLinear (K := F) ({i, j} : Finset (Fin (m + 1)))).map ψ) :
    (Subgroup.centralizer (J : Set G)).relIndex E ≤ p := by
  set χ := ratioChar hker hδE i j with hχ
  have hk : χ.ker ≤ (Subgroup.centralizer (J : Set G)).subgroupOf E := by
    intro e he
    rw [Subgroup.mem_subgroupOf]
    have h1 : δ (e : G) i = δ (e : G) j := by
      rw [MonoidHom.mem_ker, hχ, ratioChar_apply] at he
      exact div_eq_one.mp he
    have hc := mem_centralizer_map_blockSpecialLinear (hδE e e.2)
      (I := ({i, j} : Finset (Fin (m + 1)))) fun a ha b hb => by
        rw [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        exacts [rfl, h1, h1.symm, rfl]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hJ) hc
  have hr : Nat.card χ.range ≤ p := by
    refine (Subgroup.card_le_of_le (K := rootsOfUnity p F) ?_).trans (card_rootsOfUnity F p)
    rintro _ ⟨e, rfl⟩
    rw [mem_rootsOfUnity, ← map_pow]
    have he : e ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hE e e.2]; rfl)
    rw [he, map_one]
  calc (Subgroup.centralizer (J : Set G)).relIndex E =
        ((Subgroup.centralizer (J : Set G)).subgroupOf E).index := rfl
    _ ≤ χ.ker.index := Subgroup.index_antitone hk
    _ = Nat.card χ.range := Subgroup.index_ker χ
    _ ≤ p := hr


theorem three_le_card_diagClass [CharP F 2] [Finite F] [Finite G] {p : ℕ} (hp : p.Prime)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {E : Subgroup G} (hE : ∀ e ∈ E, e ^ p = 1) {δ : G → Fin (m + 1) → Fˣ}
    (hδE : ∀ e ∈ E, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ) {S : Set G}
    {i : Fin (m + 1)} {J : Subgroup G} (hJq : CFSG.Assembly.IsQuasisimple J)
    (hJI : J ≤ (blockSpecialLinear (K := F) (diagClass S δ i)).map ψ)
    (hidx : p ^ 2 ≤ (Subgroup.centralizer (J : Set G)).relIndex E) :
    3 ≤ (diagClass S δ i).card := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h1 : 1 ≤ (diagClass S δ i).card :=
    Finset.card_pos.mpr ⟨i, self_mem_diagClass S δ i⟩
  by_contra hlt
  push Not at hlt
  rcases (show (diagClass S δ i).card = 1 ∨ (diagClass S δ i).card = 2 by omega) with h | h
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    rw [ha, blockSpecialLinear_singleton, Subgroup.map_bot] at hJI
    apply commutator_ne_bot_of_isQuasisimple hJq
    rw [le_bot_iff.mp hJI]
    exact Subgroup.commutator_bot_left _
  · obtain ⟨a, b, -, hab⟩ := Finset.card_eq_two.mp h
    rw [hab] at hJI
    have h2 := relIndex_centralizer_le_of_card_two hker hE hδE hJI
    have hp2 := hp.two_le
    nlinarith

theorem exists_component_of_diag [CharP F 2] [Finite F] [Finite G] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {E : Subgroup G} (hE : ∀ e ∈ E, e ^ p = 1) {δ : G → Fin (m + 1) → Fˣ}
    (hδE : ∀ e ∈ E, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ)
    {E₀ : Subgroup G} (hE₀ : E₀ ≤ E) {J : Subgroup G}
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hidx : p ^ 2 ≤ (Subgroup.centralizer (J : Set G)).relIndex E) {e : G} (he : e ∈ E₀) :
    ∃ K : Subgroup G, IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {e}) ∧ J ≤ K ∧
      GGTypeAk f K := by
  obtain ⟨i, hJI⟩ := exists_le_map_blockSpecialLinear hker (fun e' he' => hδE e' (hE₀ he')) hJ
  have hI3 := three_le_card_diagClass hp hker hE hδE hJ.2.2 hJI hidx
  set V := diagClass ({e} : Set G) δ i with hV
  have hIV : diagClass (E₀ : Set G) δ i ⊆ V := fun k hk =>
    mem_diagClass.mpr fun e' he' => by
      rw [Set.mem_singleton_iff.mp he']
      exact mem_diagClass.mp hk e he
  have hV3 : 3 ≤ V.card := hI3.trans (Finset.card_le_card hIV)
  have hδe : ∀ e' ∈ ({e} : Set G), (e', InnerDiagA.diagGL (δ e')) ∈ LinFusion.ggInducedPairs ψ :=
    fun e' he' => by
      rw [Set.mem_singleton_iff.mp he']
      exact hδE e (hE₀ he)
  have hsub := isSubnormal_map_blockSpecialLinear hker hδe i
  exact ⟨(blockSpecialLinear (K := F) V).map ψ, ⟨isSubnormal_le_of_assembly hsub, hsub,
    isQuasisimple_map_blockSpecialLinear hker hV3⟩,
    hJI.trans (Subgroup.map_mono (blockSpecialLinear_mono hIV)), V.card, hV3,
    Or.inl (lieModel_map_blockSpecialLinear hF hf hker hV3)⟩

end LinTorus

end CFSG.StandardType
