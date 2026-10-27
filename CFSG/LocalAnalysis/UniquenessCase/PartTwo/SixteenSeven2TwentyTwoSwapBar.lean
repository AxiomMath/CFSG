module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def s16c167_barHom {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) : ↥M →* ↥(Mbar M ⊥ V hV) :=
  ((actTil ⊥ V hV).comp
      (Subgroup.inclusion (fun _ hm => s16c167_mem_stabTil_bot (hM hm)))).codRestrict
    _ (fun m => actTil_mem_barSub ⊥ V hV m.2 (s16c167_mem_stabTil_bot (hM m.2)))

theorem s16c167_barHom_apply {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (m : ↥M) :
    (s16c167_barHom hV hM m : MulAut (Vtil ⊥ V hV)) =
      actTil ⊥ V hV ⟨(m : G), s16c167_mem_stabTil_bot (hM m.2)⟩ :=
  rfl

theorem s16c167_twenty_two_family {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) {F : Fin 3 → Subgroup (Vtil ⊥ V hV)}
    {π : ↥(Mbar M ⊥ V hV) →* Equiv.Perm (Fin 3)}
    (hact : ∀ (x : ↥(Mbar M ⊥ V hV)) (i : Fin 3),
      (F i).map (x : MulAut (Vtil ⊥ V hV)).toMonoidHom = F (π x i))
    (hne : ∀ i, F i ≠ ⊥) (hpair : ∀ i j : Fin 3, i ≠ j → F i ⊓ F j = ⊥ ∧ F i ⊔ F j = ⊤) :
    (∀ i, preTil ⊥ V hV (F i) ≠ ⊥) ∧
      (∀ i j : Fin 3, i ≠ j → preTil ⊥ V hV (F i) ⊓ preTil ⊥ V hV (F j) = ⊥ ∧
        preTil ⊥ V hV (F i) ⊔ preTil ⊥ V hV (F j) = V) ∧
      (∀ (m : ↥M) (i : Fin 3), conjSubgroup (preTil ⊥ V hV (F i)) (m : G)⁻¹ =
        preTil ⊥ V hV (F (π (s16c167_barHom hV hM m) i))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i h
    apply hne i
    rw [← imgTil_preTil ⊥ V hV (F i), h, s16c167_twenty_two_imgTil_bot ⊥ V hV]
  · intro i j hij
    obtain ⟨h1, h2⟩ := hpair i j hij
    refine ⟨?_, ?_⟩
    · rw [← s16c167_twenty_two_preTil_inf, h1, preTil_bot]
      simp
    · rw [← s16c167_twenty_two_preTil_sup, h2, preTil_top]
  · intro m i
    have hm : (m : G) ∈ stabTil ⊥ V := s16c167_mem_stabTil_bot (hM m.2)
    have hminv : (m : G)⁻¹ ∈ stabTil ⊥ V := (stabTil ⊥ V).inv_mem hm
    have hinv : (actTil ⊥ V hV ⟨(m : G)⁻¹, hminv⟩)⁻¹ = actTil ⊥ V hV ⟨(m : G), hm⟩ := by
      have : (⟨(m : G)⁻¹, hminv⟩ : ↥(stabTil ⊥ V)) = (⟨(m : G), hm⟩ : ↥(stabTil ⊥ V))⁻¹ := rfl
      rw [this, map_inv, inv_inv]
    rw [← s15_Infra_preTil_map_actTil ⊥ V hV hminv, ← hact, hinv]
    rfl

theorem s16c167_twenty_two_centralizer {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) {π : ↥(Mbar M ⊥ V hV) →* Equiv.Perm (Fin 3)}
    (hcomm : ∀ x : ↥(Mbar M ⊥ V hV), (∃ k : ℕ, x ^ (2 ^ k) = 1) →
      ((∀ y ∈ oddBar M ⊥ V hV, (x : MulAut (Vtil ⊥ V hV)) * y = y * x) ↔ π x = 1))
    (m : ↥M) (hm2 : m ^ 2 = 1) :
    (m : G) ∈ preBarSub M ⊥ V hV (centralizer ((oddBar M ⊥ V hV :
        Subgroup (MulAut (Vtil ⊥ V hV))) : Set (MulAut (Vtil ⊥ V hV)))) ↔
      π (s16c167_barHom hV hM m) = 1 := by
  have hx2 : ∃ k : ℕ, (s16c167_barHom hV hM m) ^ (2 ^ k) = 1 :=
    ⟨1, by rw [pow_one, ← map_pow, hm2, map_one]⟩
  rw [← hcomm _ hx2, mem_preBarSub]
  constructor
  · rintro ⟨-, h, hc⟩ y hy
    have := (Subgroup.mem_centralizer_iff.1 hc) y hy
    exact this.symm
  · intro h
    refine ⟨m.2, s16c167_mem_stabTil_bot (hM m.2), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (h y hy).symm

theorem s16c167_twenty_two_nontrivial {M V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hAM : A ≤ M) (hAel : IsElemAbelian 2 A)
    {π : ↥(Mbar M ⊥ V hV) →* Equiv.Perm (Fin 3)}
    (hcomm : ∀ x : ↥(Mbar M ⊥ V hV), (∃ k : ℕ, x ^ (2 ^ k) = 1) →
      ((∀ y ∈ oddBar M ⊥ V hV, (x : MulAut (Vtil ⊥ V hV)) * y = y * x) ↔ π x = 1))
    (h : ⁅oddBar M ⊥ V hV, barSub ⊥ V hV A⁆ ≠ ⊥) :
    ∃ m : ↥M, (m : G) ∈ A ∧ π (s16c167_barHom hV hM m) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro φ hφ
  obtain ⟨g, hgA, rfl⟩ := (mem_barSub ⊥ V hV A φ).1 hφ
  have hgM : (g : G) ∈ M := hAM hgA
  let m : ↥M := ⟨(g : G), hgM⟩
  have hm2 : m ^ 2 = 1 := Subtype.ext (by simpa [m, sq] using hAel.2 _ hgA)
  have hx2 : ∃ k : ℕ, (s16c167_barHom hV hM m) ^ (2 ^ k) = 1 :=
    ⟨1, by rw [pow_one, ← map_pow, hm2, map_one]⟩
  have h1 : π (s16c167_barHom hV hM m) = 1 := hcon m hgA
  exact ((hcomm _ hx2).2 h1) y hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
