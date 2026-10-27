module

public import CFSG.Quasithin.Background.C124AsmZ3Main
public import CFSG.Quasithin.Background.C124AsmLiftL2
public import CFSG.Quasithin.Background.C126A5ExtractAux

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV) {Γ : Type} [Group Γ] (B : XBar X V hV E.hXN Γ)
  {A : Subgroup Γ} {Ys : Subgroup (MulAut (IntMod V hV))}

include E

theorem exists_Y (hA1 : Nat.card A = 3)
    (hA2 : ∀ a ∈ A, ∃ (l : G) (hl : l ∈ L), B.π ⟨l, E.hLX hl⟩ = a)
    (hA3 : ∀ (s : G) (hs : s ∈ baum R), ∀ a ∈ A,
      B.π ⟨s, E.R_le_X (E.baum_le_R hs)⟩ * a * (B.π ⟨s, E.R_le_X (E.baum_le_R hs)⟩)⁻¹ ∈ A)
    (hA4 : ∀ φ ∈ Ys, ∃ a ∈ A, B.ρ a = φ) :
    ∃ Y : Subgroup G, Y ≤ L ∧ twoResidual Y = Y ∧ pCoreOf 2 X ≤ Subgroup.normalizer (Y : Set G) ∧
      baum R ≤ Subgroup.normalizer (Y : Set G) ∧ (Y ⊓ pCoreOf 2 X).relIndex Y = 3 ∧
      Ys ≤ autI hV Y := by
  set Y0' := Y0 E.hLX B.π A with hY0'
  set Y := twoResidual Y0' with hY
  have hYY0 : Y ≤ Y0' := twoResidual_le _
  have hYL : Y ≤ L := hYY0.trans (Y0_le E.hLX B.π A)
  have hYX : Y ≤ X := hYL.trans E.hLX
  have hA3' : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    have := pow_card_eq_one' (G := ↥A) (x := ⟨a, ha⟩)
    rw [hA1] at this
    exact congrArg Subtype.val this
  have hpow : ∀ a : Γ, a ^ 3 = 1 → ∀ k : ℕ, a ^ (2 ^ k * 2 ^ k) = a := by
    intro a ha k
    have h4 : ∀ j : ℕ, a ^ (4 ^ j) = a := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, pow_mul, ih]
        calc a ^ 4 = a ^ 3 * a := by rw [← pow_succ]
          _ = a := by rw [ha, one_mul]
    rw [← mul_pow]
    exact h4 k
  have honto : ∀ a ∈ A, ∃ (g : G) (hg : g ∈ Y), B.π ⟨g, hYX hg⟩ = a := by
    intro a ha
    obtain ⟨l, hl, hla⟩ := hA2 a ha
    have hlY0 : l ∈ Y0' := ⟨hl, by rw [hla]; exact ha⟩
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient Y0' l hlY0
    refine ⟨(l ^ 2 ^ k) ^ 2 ^ k, Y.pow_mem hk _, ?_⟩
    have e : (⟨(l ^ 2 ^ k) ^ 2 ^ k, hYX (Y.pow_mem hk _)⟩ : ↥X) =
        (⟨l, E.hLX hl⟩ : ↥X) ^ (2 ^ k * 2 ^ k) := Subtype.ext (by simp [pow_mul])
    rw [e, map_pow, hla]
    exact hpow a (hA3' a ha) k
  have hrange : (B.π.comp (Subgroup.inclusion hYX)).range = A := by
    ext a
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact (hYY0 y.2).2
    · intro ha
      obtain ⟨g, hg, hga⟩ := honto a ha
      exact ⟨⟨g, hg⟩, hga⟩
  have hker : (B.π.comp (Subgroup.inclusion hYX)).ker = (Y ⊓ pCoreOf 2 X).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨y.2, (B.ker _).1 h⟩, fun h => (B.ker _).2 h.2⟩
  have hidx : (Y ⊓ pCoreOf 2 X).relIndex Y = 3 := by
    show ((Y ⊓ pCoreOf 2 X).subgroupOf Y).index = 3
    rw [← hker, Subgroup.index_ker, hrange, hA1]
  have hnorm := CFSG.Quasithin.C126.A5.normalizer_le_normalizer_twoResidual Y0'
  refine ⟨Y, hYL, twoResidual_twoResidual Y0', (E.Q_le_normalizer_Y0 B).trans hnorm,
    (E.S_le_normalizer_Y0 B hA3).trans hnorm, hidx, ?_⟩
  intro φ hφ
  obtain ⟨a, ha, rfl⟩ := hA4 φ hφ
  obtain ⟨g, hg, rfl⟩ := honto a ha
  rw [B.act]
  exact convI_mem_autI hV hg _

theorem fixV_J_le_R₁ {v : IntMod V hV} (hv : v ∈ fixV (autI hV (thompsonJ R))) :
    v.val ∈ quasithinOmegaOneCenter (Z3.R₁ X R) := by
  have hvS : v.val ∈ quasithinOmegaOneCenter (baum R) := E.fixV_J_le hv
  have hvCS : v.val ∈ Subgroup.centralizer (baum R : Set G) :=
    (Subgroup.closure_le _).2 (fun z hz => hz.1.2) hvS
  have hvQ : v.val ∈ pCoreOf 2 X := le_pCoreOf_of_reduced E.red v.val_mem
  have hQv : pCoreOf 2 X ≤ Subgroup.centralizer ({v.val} : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (pCoreOf_le_centralizer E.red hq) v.val v.val_mem).symm
  have hSv : baum R ≤ Subgroup.centralizer ({v.val} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hvCS s hs)
  have hR₁v : Z3.R₁ X R ≤ Subgroup.centralizer ({v.val} : Set G) := sup_le hQv hSv
  have hvR₁ : v.val ∈ Z3.R₁ X R := (le_sup_left : pCoreOf 2 X ≤ Z3.R₁ X R) hvQ
  have hvC : v.val ∈ Subgroup.centralizer (Z3.R₁ X R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hR₁v hh)
  exact Subgroup.subset_closure ⟨⟨hvR₁, hvC⟩, E.red.2.2.1.2 v.val v.val_mem⟩

end EntryPlus

end CFSG.Quasithin.C124
