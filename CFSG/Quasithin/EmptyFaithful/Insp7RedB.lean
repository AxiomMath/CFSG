module

public import CFSG.Quasithin.EmptyFaithful.Insp7RedA

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.Quasithin.EmptyFaithful.S143NO

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.Blueprint

namespace Insp7

@[expose] def ListCases (L : Type) [Group L] : Prop :=
  (IsSimpleGroup L ∧ Lemma115LieCharTwo L) ∨
    (Subgroup.center L ≠ ⊥ ∧ Subgroup.center L = CFSG.pCore 2 L ∧
      IsL34OrG24 (L ⧸ CFSG.pCore 2 L)) ∨
    (CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 3 3 1 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧
        CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 2 p 1) ∨
    (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧
      Nonempty ((L ⧸ CFSG.pCore 2 L) ≃* NativeSporadic.Carrier s))

theorem listCases_of_lemma115Cases {G : Type} [Group G] {L : Subgroup G} {z : G} (hz : z ∈ L)
    (h : Lemma115Cases L z) : ListCases ↥L := by
  rcases h with hA | hB | hC | hD | hE | hF
  · exact Or.inl ⟨hA.1, hA.2.1⟩
  · exact Or.inr (Or.inl ⟨hB.1, hB.2.1, hB.2.2.1⟩)
  · exact absurd hC (not_lemma115CaseC hz)
  · exact absurd hD (not_lemma115CaseD hz)
  · exact Or.inr (Or.inr (Or.inl hE.1))
  · exact Or.inr (Or.inr (Or.inr hF.1))

@[expose] def InspNum : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → ListCases L →
    ∀ z : L, z * z = 1 → z ∉ Subgroup.center L →
      ∀ (Gc : Type) [Group Gc] [Finite Gc] (ρ : Gc →* MulAut L), Function.Injective ρ →
        (∀ l : L, MulAut.conj l ∈ ρ.range) →
        ∀ ž : Gc, ρ ž = MulAut.conj z →
          ∀ Ŝ : Subgroup Gc, IsPGroup 2 Ŝ → ¬ 2 ∣ Ŝ.index →
            Ŝ ≤ Subgroup.centralizer ({ž} : Set Gc) →
            ∀ P : Subgroup Gc, P ≤ Subgroup.centralizer ({ž} : Set Gc) →
              P.relIndex (Subgroup.centralizer ({ž} : Set Gc)) ≤ 2 → ¬ S143.ExtQ8SqS3S3 ↥P

theorem inspect_aux {G : Type} [Group G] [Finite G] {H S M L : Subgroup G} {z d : G}
    (hnum : InspNum) (hHd : H ≤ Subgroup.centralizer ({d} : Set G)) (hd2 : d * d = 1)
    (hO : pCoreOf 2 H = Subgroup.zpowers d) (h : Lemma115Hyp H S M z)
    (hLc : IsComponentIn L H) (hzL : z ∈ L) (hcases : Lemma115Cases L z) {Gc : Type} [Group Gc]
    (φ : ↥H →* Gc) (hφs : Function.Surjective φ)
    (hφk : φ.ker = (Subgroup.zpowers d).subgroupOf H) (P : Subgroup Gc)
    (hP : P ≤ Subgroup.centralizer ({φ ⟨z, h.z_mem_H⟩} : Set Gc))
    (hrel : P.relIndex (Subgroup.centralizer ({φ ⟨z, h.z_mem_H⟩} : Set Gc)) ≤ 2) :
    ¬ S143.ExtQ8SqS3S3 ↥P := by
  have hzH : z ∈ H := h.z_mem_H
  have hLH : L ≤ H := hLc.1
  have hdc : ∀ g ∈ H, g * d = d * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp (hHd hg) d (Set.mem_singleton d)).symm
  have hLN : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_component h hLc hzL
  have hY : H ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.zpowers d :=
    centralizer_inf_le_zpowers h hHd hd2 hO hLN hzL
  obtain ⟨ρ, hρi, hρφ⟩ := exists_embedding hLN hLH hdc φ hφs hφk hY
  have hq : CFSG.IsQuasisimple ↥L :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hLH)).1 hLc.2.1
  have hlist : ListCases ↥L := listCases_of_lemma115Cases hzL hcases
  have hz2 : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 := by
    apply Subtype.ext
    have := h.z_sq
    rw [pow_two] at this
    exact this
  have hzc : (⟨z, hzL⟩ : ↥L) ∉ Subgroup.center ↥L := by
    intro hc
    have hact := (h.component_action hLc).2.1
    have hcomm : ⁅L, Subgroup.zpowers z⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro l hl
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have h1 : (l : G) * z = z * l := by
        have := Subgroup.mem_center_iff.mp hc ⟨l, hl⟩
        exact congrArg Subtype.val this
      exact (Commute.zpow_left (show Commute z l from h1.symm) k).eq
    rw [hcomm] at hact
    have hbot : L = ⊥ := hact.symm
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot L).mp this hbot
  have hfin : Finite Gc := Finite.of_surjective φ hφs
  have hinn : ∀ l : ↥L, MulAut.conj l ∈ ρ.range := by
    intro l
    refine ⟨φ ⟨l, hLH l.2⟩, ?_⟩
    rw [hρφ]
    ext x
    rw [actOn_apply_coe]
    simp
  have hρz : ρ (φ ⟨z, hzH⟩) = MulAut.conj (⟨z, hzL⟩ : ↥L) := by
    rw [hρφ]
    ext x
    rw [actOn_apply_coe]
    simp
  have hSyl := h.sylow
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.1).symm
  refine hnum ↥L hq hlist ⟨z, hzL⟩ hz2 hzc Gc ρ hρi hinn (φ ⟨z, hzH⟩) hρz
    ((S.subgroupOf H).map φ) (hS2.map φ) ?_ ?_ P hP hrel
  · intro h2
    exact hSyl.2.2 (h2.trans (Subgroup.index_map_dvd (S.subgroupOf H) hφs))
  · rintro _ ⟨s, hs, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hc : (s : G) * z = z * (s : G) := Subgroup.mem_centralizer_iff.mp h.z_central _ hsS
    have : s * (⟨z, hzH⟩ : ↥H) = ⟨z, hzH⟩ * s := Subtype.ext hc
    rw [← map_mul, ← map_mul, this]

theorem lemma14320Inspect_of_num (hnum : InspNum) : S143.Lemma14320Inspect := by
  intro G _ _ _ _ _ S M z d _ hd2 hO h L hLc hzL hcases Gc _ φ hφs hφk P hP hrel
  exact inspect_aux hnum le_rfl hd2 hO h hLc hzL hcases φ hφs hφk P hP hrel

end Insp7

end CFSG.Quasithin
