module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUModel
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover

namespace SUTorus

variable {K : Type} [Field K] {f m : ℕ} {G : Type} [Group G]

theorem exists_scalar_diag_mul (h : UnitaryFieldData 2 f K) (hn : 3 ≤ m + 1)
    (hnq : (m + 1, 2 ^ f) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    {ψ : ↥(unitarySU 2 f K (m + 1)) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1))) {δ : G → Fin (m + 1) → Kˣ}
    {e e' : G} (he : (e, diagHom (m + 1) (δ e)) ∈ suPairs ψ)
    (he' : (e', diagHom (m + 1) (δ e')) ∈ suPairs ψ)
    (hee' : (e * e', diagHom (m + 1) (δ (e * e'))) ∈ suPairs ψ) :
    ∃ c : Kˣ, ∀ k, δ (e * e') k = c * (δ e k * δ e' k) := by
  have hmul := (suPairs ψ).mul_mem he he'
  rw [Prod.mk_mul_mk, ← map_mul] at hmul
  obtain ⟨c, hc⟩ := exists_scalar_mul_of_mem_suPairs h hn hnq hp hpq hker hmul hee'
  refine ⟨c, fun k => Units.ext ?_⟩
  have h1 := congrArg (fun A : GL (Fin (m + 1)) K =>
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) k k) hc
  simpa [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    diagonal_mul_diagonal] using h1

theorem relIndex_centralizer_le_of_card_two [Finite G] (h : UnitaryFieldData 2 f K)
    (hn : 3 ≤ m + 1) (hnq : (m + 1, 2 ^ f) ≠ (3, 2)) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ f + 1) {ψ : ↥(unitarySU 2 f K (m + 1)) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1))) {E : Subgroup G}
    (hE : ∀ e ∈ E, e ^ p = 1) {δ : G → Fin (m + 1) → Kˣ}
    (hδE : ∀ e ∈ E, (e, diagHom (m + 1) (δ e)) ∈ suPairs ψ) {i j : Fin (m + 1)}
    {J : Subgroup G}
    (hJ : J ≤ (TableBUE.blockSU (K := K) (n := f) ({i, j} : Finset (Fin (m + 1)))).map ψ) :
    (Subgroup.centralizer (J : Set G)).relIndex E ≤ p := by
  have : Finite K := h.finite
  have : NeZero p := ⟨hp.ne_zero⟩
  let χ : E →* Kˣ := MonoidHom.mk' (fun e => δ (e : G) i / δ (e : G) j) fun a b => by
    obtain ⟨c, hc⟩ := exists_scalar_diag_mul h hn hnq hp hpq hker (hδE a a.2) (hδE b b.2)
      (hδE _ (a * b).2)
    change δ ((a : G) * b) i / δ ((a : G) * b) j = _
    rw [hc i, hc j, mul_div_mul_left_eq_div, mul_div_mul_comm]
  have hk : χ.ker ≤ (Subgroup.centralizer (J : Set G)).subgroupOf E := by
    intro e he
    rw [Subgroup.mem_subgroupOf]
    have h0 : δ (e : G) i / δ (e : G) j = 1 := he
    have h1 : δ (e : G) i = δ (e : G) j := div_eq_one.mp h0
    have hc := mem_centralizer_map_blockSU (hδE e e.2) (I := ({i, j} : Finset (Fin (m + 1))))
      fun a ha b hb => by
        rw [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        exacts [rfl, h1, h1.symm, rfl]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hJ) hc
  have hr : Nat.card χ.range ≤ p := by
    refine (Subgroup.card_le_of_le (K := rootsOfUnity p K) ?_).trans (card_rootsOfUnity K p)
    rintro _ ⟨e, rfl⟩
    rw [mem_rootsOfUnity, ← map_pow]
    have he : e ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hE e e.2]; rfl)
    rw [he, map_one]
  calc (Subgroup.centralizer (J : Set G)).relIndex E =
        ((Subgroup.centralizer (J : Set G)).subgroupOf E).index := rfl
    _ ≤ χ.ker.index := Subgroup.index_antitone hk
    _ = Nat.card χ.range := Subgroup.index_ker χ
    _ ≤ p := hr

theorem three_le_card_diagClass [Finite G] (h : UnitaryFieldData 2 f K) (hn : 3 ≤ m + 1)
    (hnq : (m + 1, 2 ^ f) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    {ψ : ↥(unitarySU 2 f K (m + 1)) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1))) {E : Subgroup G}
    (hE : ∀ e ∈ E, e ^ p = 1) {δ : G → Fin (m + 1) → Kˣ}
    (hδE : ∀ e ∈ E, (e, diagHom (m + 1) (δ e)) ∈ suPairs ψ) {S : Set G} {i : Fin (m + 1)}
    {J : Subgroup G} (hJq : CFSG.Assembly.IsQuasisimple J)
    (hJI : J ≤ (TableBUE.blockSU (K := K) (n := f) (LinTorus.diagClass S δ i)).map ψ)
    (hidx : p ^ 2 ≤ (Subgroup.centralizer (J : Set G)).relIndex E) :
    3 ≤ (LinTorus.diagClass S δ i).card := by
  have h1 : 1 ≤ (LinTorus.diagClass S δ i).card :=
    Finset.card_pos.mpr ⟨i, LinTorus.self_mem_diagClass S δ i⟩
  by_contra hlt
  push Not at hlt
  rcases (show (LinTorus.diagClass S δ i).card = 1 ∨ (LinTorus.diagClass S δ i).card = 2 by
    omega) with h' | h'
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h'
    rw [ha, blockSU_singleton h, Subgroup.map_bot] at hJI
    apply commutator_ne_bot_of_isQuasisimple hJq
    rw [le_bot_iff.mp hJI]
    exact Subgroup.commutator_bot_left _
  · obtain ⟨a, b, -, hab⟩ := Finset.card_eq_two.mp h'
    rw [hab] at hJI
    have h2 := relIndex_centralizer_le_of_card_two h hn hnq hp hpq hker hE hδE hJI
    have hp2 := hp.two_le
    nlinarith

theorem exists_component_of_diag [Finite G] (h : UnitaryFieldData 2 f K) (hn : 3 ≤ m + 1)
    (hq : 2 ^ f ≠ 2) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    {ψ : ↥(unitarySU 2 f K (m + 1)) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1))) {E : Subgroup G}
    (hE : ∀ e ∈ E, e ^ p = 1) {δ : G → Fin (m + 1) → Kˣ}
    (hδE : ∀ e ∈ E, (e, diagHom (m + 1) (δ e)) ∈ suPairs ψ) {E₀ : Subgroup G} (hE₀ : E₀ ≤ E)
    {J : Subgroup G} (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hidx : p ^ 2 ≤ (Subgroup.centralizer (J : Set G)).relIndex E) {e : G} (he : e ∈ E₀) :
    ∃ L : Subgroup G, IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {e}) ∧ J ≤ L ∧
      GGTypeAk f L := by
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => hq (congrArg Prod.snd h')
  obtain ⟨i, hJI⟩ := exists_le_map_blockSU h hp hpq hker (fun e' he' => hδE e' (hE₀ he')) hJ
  have hI3 := three_le_card_diagClass h hn hnq hp hpq hker hE hδE hJ.2.2 hJI hidx
  set V := LinTorus.diagClass ({e} : Set G) δ i with hV
  have hIV : LinTorus.diagClass (E₀ : Set G) δ i ⊆ V := fun k hk =>
    LinTorus.mem_diagClass.mpr fun e' he' => by
      rw [Set.mem_singleton_iff.mp he']
      exact LinTorus.mem_diagClass.mp hk e he
  have hV3 : 3 ≤ V.card := hI3.trans (Finset.card_le_card hIV)
  have hVq : (V.card, 2 ^ f) ≠ (3, 2) := fun h' => hq (congrArg Prod.snd h')
  have hδe : ∀ e' ∈ ({e} : Set G), (e', diagHom (m + 1) (δ e')) ∈ suPairs ψ := fun e' he' => by
    rw [Set.mem_singleton_iff.mp he']
    exact hδE e (hE₀ he)
  have hsub := isSubnormal_map_blockSU hker hδe i
  exact ⟨(TableBUE.blockSU (K := K) (n := f) V).map ψ, ⟨isSubnormal_le_of_assembly hsub, hsub,
    isQuasisimple_map_blockSU h hker hV3 hVq⟩, hJI.trans (Subgroup.map_mono (blockSU_mono hIV)),
    V.card, hV3, Or.inr (lieModel_map_blockSU h hker hV3 hVq)⟩

end SUTorus

end CFSG.StandardType
