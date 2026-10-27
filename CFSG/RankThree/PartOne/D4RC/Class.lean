module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.SEITZ7.D4BrN

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7 CFSG.Timmesfeld.ARS

variable {K : Type} [Field K] (σ : K →+* K)

noncomputable abbrev Xh : Subgroup (twistedGroup σ) := twistedRootGroup σ (rt 7)

@[expose] noncomputable def longClass : Set (Subgroup (twistedGroup σ)) :=
  Set.range (conjSub (Xh σ))

variable {σ}

theorem rcg_conjSub_mem {A : Subgroup (twistedGroup σ)} (hA : A ∈ longClass σ)
    (g : twistedGroup σ) : conjSub A g ∈ longClass σ := by
  obtain ⟨h, rfl⟩ := hA
  exact ⟨g * h, conjSub_mul (Xh σ) g h⟩

theorem rcg_Xh_mem : Xh σ ∈ longClass σ := ⟨1, conjSub_one (Xh σ)⟩

theorem mem_Xh_iff [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (g : twistedGroup σ) :
    g ∈ Xh σ ↔ ∃ c, σ c = c ∧ (g : adjointGroup d4 K) = xH c := by
  show (g : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (rt 7) ↔ _
  rw [mem_XH hσ]

theorem rcg_ne_bot [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {A : Subgroup (twistedGroup σ)}
    (hA : A ∈ longClass σ) : A ≠ ⊥ := by
  obtain ⟨g, rfl⟩ := hA
  intro h
  have h1 : xHg hσ 1 (map_one σ) ∈ Xh σ := xHg_mem hσ 1 (map_one σ)
  have h2 : (MulAut.conj g).toMonoidHom (xHg hσ 1 (map_one σ)) ∈ conjSub (Xh σ) g := ⟨_, h1, rfl⟩
  rw [h, Subgroup.mem_bot] at h2
  have h3 : xHg hσ 1 (map_one σ) = 1 := by
    have : (MulAut.conj g).toMonoidHom (xHg hσ 1 (map_one σ)) = 1 := h2
    simpa using this
  exact xH_ne_one (K := K) one_ne_zero (congrArg Subtype.val h3)

theorem rcg_mul_self [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {A : Subgroup (twistedGroup σ)}
    (hA : A ∈ longClass σ) : ∀ a ∈ A, a * a = 1 := by
  obtain ⟨g, rfl⟩ := hA
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, -, hc⟩ := (mem_Xh_iff hσ x).1 hx
  have hxx : x * x = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, hc, Subgroup.coe_one]
    exact xd_mul_self 22 c)
  show (MulAut.conj g).toMonoidHom x * (MulAut.conj g).toMonoidHom x = 1
  rw [← map_mul, hxx, map_one]

end CFSG.RankThree.PartOne.D4RC
