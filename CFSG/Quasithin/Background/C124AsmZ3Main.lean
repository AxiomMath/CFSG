module

public import CFSG.Quasithin.Background.C124AsmFrattini
public import CFSG.Quasithin.Background.C124AsmZ3Quot

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

@[expose] def Y0 {X L : Subgroup G} (hLX : L ≤ X) {Γ : Type} [Group Γ] (π : ↥X →* Γ)
    (A : Subgroup Γ) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ L, π ⟨g, hLX hg⟩ ∈ A}
  one_mem' := ⟨L.one_mem, by
    have : π ⟨1, hLX L.one_mem⟩ = 1 := map_one π
    rw [this]
    exact A.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨L.mul_mem ha hb, ?_⟩
    have : π ⟨a * b, hLX (L.mul_mem ha hb)⟩ = π ⟨a, hLX ha⟩ * π ⟨b, hLX hb⟩ := by
      rw [← map_mul]
      rfl
    rw [this]
    exact A.mul_mem ha' hb'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨L.inv_mem ha, ?_⟩
    have : π ⟨a⁻¹, hLX (L.inv_mem ha)⟩ = (π ⟨a, hLX ha⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [this]
    exact A.inv_mem ha'

theorem Y0_le {X L : Subgroup G} (hLX : L ≤ X) {Γ : Type} [Group Γ] (π : ↥X →* Γ)
    (A : Subgroup Γ) : Y0 hLX π A ≤ L := fun _ hg => hg.1

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV) {Γ : Type} [Group Γ] (B : XBar X V hV E.hXN Γ)
  {A : Subgroup Γ}

include E

theorem Q_le_normalizer_Y0 :
    pCoreOf 2 X ≤ Subgroup.normalizer (Y0 E.hLX B.π A : Set G) := by
  have key : ∀ q ∈ pCoreOf 2 X, ∀ g ∈ Y0 E.hLX B.π A, q * g * q⁻¹ ∈ Y0 E.hLX B.π A := by
    intro q hq g hg
    obtain ⟨hgL, hgA⟩ := hg
    have hqX : q ∈ X := pCoreOf_le 2 X hq
    refine ⟨(Subgroup.mem_normalizer_iff.1 (E.normal hqX) g).1 hgL, ?_⟩
    have h1 := E.pi_conj B hqX (E.hLX hgL)
    rw [(B.ker ⟨q, hqX⟩).2 hq, one_mul, inv_one, mul_one] at h1
    rw [← h1]
    exact hgA
  intro q hq
  exact mem_normalizer_of_conj (key q hq) (fun g hg => by
    simpa using key q⁻¹ ((pCoreOf 2 X).inv_mem hq) g hg)

theorem S_le_normalizer_Y0
    (hA : ∀ (s : G) (hs : s ∈ baum R), ∀ a ∈ A,
      B.π ⟨s, E.R_le_X (E.baum_le_R hs)⟩ * a * (B.π ⟨s, E.R_le_X (E.baum_le_R hs)⟩)⁻¹ ∈ A) :
    baum R ≤ Subgroup.normalizer (Y0 E.hLX B.π A : Set G) := by
  have key : ∀ s (hs : s ∈ baum R), ∀ g ∈ Y0 E.hLX B.π A, s * g * s⁻¹ ∈ Y0 E.hLX B.π A := by
    intro s hs g hg
    obtain ⟨hgL, hgA⟩ := hg
    have hsX : s ∈ X := E.R_le_X (E.baum_le_R hs)
    refine ⟨(Subgroup.mem_normalizer_iff.1 (E.normal hsX) g).1 hgL, ?_⟩
    rw [← E.pi_conj B hsX (E.hLX hgL)]
    exact hA s hs _ hgA
  intro s hs
  exact mem_normalizer_of_conj (key s hs) (fun g hg => by
    simpa using key s⁻¹ ((baum R).inv_mem hs) g hg)

end EntryPlus

end CFSG.Quasithin.C124
