module

public import CFSG.RankThree.PartOne.S12.InputsCT
public import CFSG.Open.StatedAPI
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSL StatedSU)

theorem statedClassicalModel_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel X t n p f) : StatedClassicalModel Y t n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem isSLModelTwo_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n f : ℕ}
    (h : IsSLModelTwo n f X) : IsSLModelTwo n f Y := by
  obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

theorem isSUModelTwo_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n f : ℕ}
    (h : IsSUModelTwo n f X) : IsSUModelTwo n f Y := by
  obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

theorem centrallyLThree_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {f : ℕ}
    (h : CentrallyLThree f X) : CentrallyLThree f Y :=
  h.imp (isSLModelTwo_of_equiv e) (statedClassicalModel_of_equiv e)

theorem centrallyUThree_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {f : ℕ}
    (h : CentrallyUThree f X) : CentrallyUThree f Y :=
  h.imp (isSUModelTwo_of_equiv e) (statedClassicalModel_of_equiv e)

section Subgroup

variable {G : Type} [Group G]

theorem nonempty_sup_subgroupOf_equiv {I A B : Subgroup G} (hA : A ≤ I) (hB : B ≤ I) :
    Nonempty (↥(A.subgroupOf I ⊔ B.subgroupOf I) ≃* ↥(A ⊔ B)) := by
  have hmap : (A.subgroupOf I ⊔ B.subgroupOf I).map I.subtype = A ⊔ B := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB]
  exact ⟨(Subgroup.equivMapOfInjective _ I.subtype I.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

theorem statedClassicalModel_subgroupOf {I K : Subgroup G} (hK : K ≤ I)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (h : StatedClassicalModel ↥K t n p f) :
    StatedClassicalModel ↥(K.subgroupOf I) t n p f :=
  statedClassicalModel_of_equiv (Subgroup.subgroupOfEquivOfLe hK).symm h

theorem isElementaryAbelian_of_equiv {p : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hX : IsElementaryAbelian p X) : IsElementaryAbelian p Y :=
  CFSG.IsElementaryAbelian.of_mulEquiv e hX

theorem centralizer_subgroupOf_eq {I S : Subgroup G} (hS : S ≤ I) :
    Subgroup.centralizer ((S.subgroupOf I : Subgroup I) : Set I) =
      (Subgroup.centralizer (S : Set G)).subgroupOf I := by
  ext ⟨x, hx⟩
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h g hg
    have := h ⟨g, hS hg⟩ (by simpa [Subgroup.mem_subgroupOf] using hg)
    exact congrArg Subtype.val this
  · intro h g hg
    have hg' : (g : G) ∈ S := by simpa [Subgroup.mem_subgroupOf] using hg
    exact Subtype.ext (h _ hg')

theorem inf_subgroupOf_eq {I : Subgroup G} (H H' : Subgroup G) :
    (H ⊓ H').subgroupOf I = H.subgroupOf I ⊓ H'.subgroupOf I := by
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem ctTorusCondition_subgroupOf {ι : Type} {p : ℕ} {I E : Subgroup G} {K : ι → Subgroup G}
    (hEI : E ≤ I) (hKI : ∀ i, K i ≤ I) (h : CTTorusCondition p E K) :
    CTTorusCondition p (E.subgroupOf I) (fun i => (K i).subgroupOf I) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
  · rw [centralizer_subgroupOf_eq (hKI i), ← inf_subgroupOf_eq, ← inf_subgroupOf_eq,
      ← Subgroup.subgroupOf_sup (inf_le_left.trans hEI) (inf_le_left.trans hEI), ← (h1 i).1]
  · rw [centralizer_subgroupOf_eq (hKI i), ← inf_subgroupOf_eq,
      Subgroup.relIndex_subgroupOf hEI]
    exact (h1 i).2
  · have hKij : K i ⊔ K j ≤ I := sup_le (hKI i) (hKI j)
    rw [← Subgroup.subgroupOf_sup (hKI i) (hKI j), centralizer_subgroupOf_eq hKij,
      ← inf_subgroupOf_eq, Subgroup.relIndex_subgroupOf hEI]
    exact h2 i j hij

theorem extPhan_ambient (hPhan : ExtPhan) {I E : Subgroup G} {n f p : ℕ}
    {K : Fin n → Subgroup G} [Finite G] (hn : 3 ≤ n) (hf : 2 ≤ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpf : p ∣ 2 ^ f + 1) (hE : IsElementaryAbelian p E) (hEI : E ≤ I) (hKI : ∀ i, K i ≤ I)
    (hgen : (⨆ i, K i) = I) (hmodel : ∀ i, StatedClassicalModel ↥(K i) .PSL 2 2 f)
    (hcomm : ∀ i j, i ≠ j → ¬ chainAdj i j →
      K i ≤ Subgroup.centralizer (K j : Set G) ∧ K i ⊓ K j = ⊥)
    (hadj : ∀ i j, chainAdj i j → CentrallyUThree f ↥(K i ⊔ K j))
    (htor : CTTorusCondition p E K) :
    StatedClassicalModel (↥I ⧸ Subgroup.center ↥I) .PSU (n + 1) 2 f := by
  have hgen' : (⨆ i, (K i).subgroupOf I) = ⊤ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp_rw [Subgroup.map_subgroupOf_eq_of_le (hKI _)]
    exact hgen
  refine hPhan ↥I n f p (fun i => (K i).subgroupOf I) (E.subgroupOf I) hn hf hp hp3 hpf
    (isElementaryAbelian_of_equiv (Subgroup.subgroupOfEquivOfLe hEI).symm hE) hgen'
    (fun i => statedClassicalModel_subgroupOf (hKI i) (hmodel i)) (fun i j hij hnadj => ?_)
    (fun i j hadjij => ?_) (ctTorusCondition_subgroupOf hEI hKI htor)
  · obtain ⟨h1, h2⟩ := hcomm i j hij hnadj
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hx' : (x : G) ∈ K i := by simpa [Subgroup.mem_subgroupOf] using hx
      have hy' : (y : G) ∈ K j := by simpa [Subgroup.mem_subgroupOf] using hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (h1 hx') y hy')
    · rw [← inf_subgroupOf_eq, h2, Subgroup.bot_subgroupOf]
  · obtain ⟨e⟩ := nonempty_sup_subgroupOf_equiv (hKI i) (hKI j)
    exact centrallyUThree_of_equiv e.symm (hadj i j hadjij)

theorem iSup_subgroupOf_eq_top {ι : Type} {I : Subgroup G} {K : ι → Subgroup G}
    (hKI : ∀ i, K i ≤ I) (hgen : (⨆ i, K i) = I) : (⨆ i, (K i).subgroupOf I) = ⊤ := by
  apply Subgroup.map_injective I.subtype_injective
  rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
  simp_rw [Subgroup.map_subgroupOf_eq_of_le (hKI _)]
  exact hgen

theorem sup_three_subgroupOf_eq_top {I K₁ K₂ K₃ : Subgroup G} (h₁ : K₁ ≤ I) (h₂ : K₂ ≤ I)
    (h₃ : K₃ ≤ I) (hgen : K₁ ⊔ K₂ ⊔ K₃ = I) :
    K₁.subgroupOf I ⊔ K₂.subgroupOf I ⊔ K₃.subgroupOf I = ⊤ := by
  apply Subgroup.map_injective I.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le h₁, Subgroup.map_subgroupOf_eq_of_le h₂,
    Subgroup.map_subgroupOf_eq_of_le h₃]
  exact hgen

theorem commuting_subgroupOf {I A B : Subgroup G}
    (h : A ≤ Subgroup.centralizer (B : Set G) ∧ A ⊓ B = ⊥) :
    A.subgroupOf I ≤ Subgroup.centralizer ((B.subgroupOf I : Subgroup I) : Set I) ∧
      A.subgroupOf I ⊓ B.subgroupOf I = ⊥ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hx' : (x : G) ∈ A := by simpa [Subgroup.mem_subgroupOf] using hx
    have hy' : (y : G) ∈ B := by simpa [Subgroup.mem_subgroupOf] using hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (h1 hx') y hy')
  · rw [← inf_subgroupOf_eq, h2, Subgroup.bot_subgroupOf]

theorem ctTorusCondition_subgroupOf_three {p : ℕ} {I E K₁ K₂ K₃ : Subgroup G} (hEI : E ≤ I)
    (h₁ : K₁ ≤ I) (h₂ : K₂ ≤ I) (h₃ : K₃ ≤ I) (h : CTTorusCondition p E ![K₁, K₂, K₃]) :
    CTTorusCondition p (E.subgroupOf I)
      ![K₁.subgroupOf I, K₂.subgroupOf I, K₃.subgroupOf I] := by
  have hKI : ∀ i, (![K₁, K₂, K₃] : Fin 3 → Subgroup G) i ≤ I := by
    intro i
    fin_cases i <;> assumption
  have h' := ctTorusCondition_subgroupOf hEI hKI h
  have he : (fun i => ((![K₁, K₂, K₃] : Fin 3 → Subgroup G) i).subgroupOf I) =
      ![K₁.subgroupOf I, K₂.subgroupOf I, K₃.subgroupOf I] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h'
  exact h'

theorem extCurtisTitsA_ambient (h : ExtCurtisTitsA) {I E : Subgroup G} {n f p : ℕ}
    {K : Fin n → Subgroup G} [Finite G] (hn : 3 ≤ n) (hf : 2 ≤ f) (hp : p.Prime)
    (hpf : p ∣ 2 ^ f - 1) (hE : IsElementaryAbelian p E) (hEI : E ≤ I) (hKI : ∀ i, K i ≤ I)
    (hgen : (⨆ i, K i) = I) (hmodel : ∀ i, StatedClassicalModel ↥(K i) .PSL 2 2 f)
    (hcomm : ∀ i j, i ≠ j → ¬ chainAdj i j →
      K i ≤ Subgroup.centralizer (K j : Set G) ∧ K i ⊓ K j = ⊥)
    (hadj : ∀ i j, chainAdj i j → CentrallyLThree f ↥(K i ⊔ K j))
    (htor : CTTorusCondition p E K) :
    StatedClassicalModel (↥I ⧸ Subgroup.center ↥I) .PSL (n + 1) 2 f ∧
      (Nat.Coprime (n + 1) (2 ^ f - 1) → StatedClassicalModel ↥I .PSL (n + 1) 2 f) :=
  h ↥I n f p (fun i => (K i).subgroupOf I) (E.subgroupOf I) hn hf hp hpf
    (isElementaryAbelian_of_equiv (Subgroup.subgroupOfEquivOfLe hEI).symm hE)
    (iSup_subgroupOf_eq_top hKI hgen)
    (fun i => statedClassicalModel_subgroupOf (hKI i) (hmodel i))
    (fun i j hij hnadj => commuting_subgroupOf (hcomm i j hij hnadj))
    (fun i j hadjij => by
      obtain ⟨e⟩ := nonempty_sup_subgroupOf_equiv (hKI i) (hKI j)
      exact centrallyLThree_of_equiv e.symm (hadj i j hadjij))
    (ctTorusCondition_subgroupOf hEI hKI htor)

theorem extCurtisTitsCThreeSp_ambient (h : ExtCurtisTitsCThreeSp)
    {I E K₁ K₂ K₃ : Subgroup G} {f p : ℕ} [Finite G] (hf : 2 ≤ f) (hp : p.Prime)
    (hpf : p ∣ 2 ^ f - 1) (hE : IsElementaryAbelian p E) (hEI : E ≤ I) (h₁ : K₁ ≤ I)
    (h₂ : K₂ ≤ I) (h₃ : K₃ ≤ I) (hgen : K₁ ⊔ K₂ ⊔ K₃ = I)
    (hm₁ : StatedClassicalModel ↥K₁ .PSL 2 2 f) (hm₂ : StatedClassicalModel ↥K₂ .PSL 2 2 f)
    (hm₃ : StatedClassicalModel ↥K₃ .PSL 2 2 f)
    (hcomm : K₁ ≤ Subgroup.centralizer (K₃ : Set G) ∧ K₁ ⊓ K₃ = ⊥)
    (hL : CentrallyLThree f ↥(K₁ ⊔ K₂)) (hSp : StatedClassicalModel ↥(K₂ ⊔ K₃) .PSp 2 2 f)
    (htor : CTTorusCondition p E ![K₁, K₂, K₃]) : StatedClassicalModel ↥I .PSp 3 2 f := by
  obtain ⟨e12⟩ := nonempty_sup_subgroupOf_equiv h₁ h₂
  obtain ⟨e23⟩ := nonempty_sup_subgroupOf_equiv h₂ h₃
  exact h ↥I f p (K₁.subgroupOf I) (K₂.subgroupOf I) (K₃.subgroupOf I) (E.subgroupOf I) hf hp hpf
    (isElementaryAbelian_of_equiv (Subgroup.subgroupOfEquivOfLe hEI).symm hE)
    (sup_three_subgroupOf_eq_top h₁ h₂ h₃ hgen) (statedClassicalModel_subgroupOf h₁ hm₁)
    (statedClassicalModel_subgroupOf h₂ hm₂) (statedClassicalModel_subgroupOf h₃ hm₃)
    (commuting_subgroupOf hcomm) (centrallyLThree_of_equiv e12.symm hL)
    (statedClassicalModel_of_equiv e23.symm hSp)
    (ctTorusCondition_subgroupOf_three hEI h₁ h₂ h₃ htor)

theorem not_le_centralizer_subgroupOf {I E K L : Subgroup G} (hEI : E ≤ I) (hLI : L ≤ I)
    (h : ¬ (E ⊓ K ≤ Subgroup.centralizer (L : Set G))) :
    ¬ (E.subgroupOf I ⊓ K.subgroupOf I ≤
      Subgroup.centralizer ((L.subgroupOf I : Subgroup ↥I) : Set ↥I)) := by
  intro hle
  apply h
  intro x hx
  have hxI : x ∈ I := hEI hx.1
  have hmem : (⟨x, hxI⟩ : ↥I) ∈ E.subgroupOf I ⊓ K.subgroupOf I :=
    ⟨Subgroup.mem_subgroupOf.2 hx.1, Subgroup.mem_subgroupOf.2 hx.2⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := Subgroup.mem_centralizer_iff.1 (hle hmem) ⟨y, hLI hy⟩ (Subgroup.mem_subgroupOf.2 hy)
  exact congrArg Subtype.val h1

theorem extCurtisTitsBThree_ambient (h : ExtCurtisTitsBThree)
    {I E K₁ K₂ K₃ : Subgroup G} {f p : ℕ} [Finite G] (hf : 2 ≤ f) (hp : p.Prime)
    (hpf : p ∣ 2 ^ f - 1) (hE : IsElementaryAbelian p E) (hEI : E ≤ I) (h₁ : K₁ ≤ I)
    (h₂ : K₂ ≤ I) (h₃ : K₃ ≤ I) (hgen : K₁ ⊔ K₂ ⊔ K₃ = I)
    (hm₁ : StatedClassicalModel ↥K₁ .PSL 2 2 f) (hm₂ : StatedClassicalModel ↥K₂ .PSL 2 2 f)
    (hm₃ : StatedClassicalModel ↥K₃ .PSL 2 2 (2 * f))
    (hcomm : K₁ ≤ Subgroup.centralizer (K₃ : Set G) ∧ K₁ ⊓ K₃ = ⊥)
    (hL : CentrallyLThree f ↥(K₁ ⊔ K₂)) (hU : StatedClassicalModel ↥(K₂ ⊔ K₃) .PSU 4 2 f)
    (htor : CTTorusCondition p E ![K₁, K₂, K₃])
    (hstd : ¬ (E ⊓ K₂ ≤ Subgroup.centralizer (K₃ : Set G))) :
    StatedClassicalModel ↥I .POmegaMinus 4 2 f := by
  obtain ⟨e12⟩ := nonempty_sup_subgroupOf_equiv h₁ h₂
  obtain ⟨e23⟩ := nonempty_sup_subgroupOf_equiv h₂ h₃
  exact h ↥I f p (K₁.subgroupOf I) (K₂.subgroupOf I) (K₃.subgroupOf I) (E.subgroupOf I) hf hp hpf
    (isElementaryAbelian_of_equiv (Subgroup.subgroupOfEquivOfLe hEI).symm hE)
    (sup_three_subgroupOf_eq_top h₁ h₂ h₃ hgen) (statedClassicalModel_subgroupOf h₁ hm₁)
    (statedClassicalModel_subgroupOf h₂ hm₂) (statedClassicalModel_subgroupOf h₃ hm₃)
    (commuting_subgroupOf hcomm) (centrallyLThree_of_equiv e12.symm hL)
    (statedClassicalModel_of_equiv e23.symm hU)
    (ctTorusCondition_subgroupOf_three hEI h₁ h₂ h₃ htor)
    (not_le_centralizer_subgroupOf hEI h₃ hstd)

theorem extCurtisTitsCThreeU_ambient (h : ExtCurtisTitsCThreeU)
    {I E K₁ K₂ K₃ : Subgroup G} {f p : ℕ} [Finite G] (hf : 2 ≤ f) (hp : p.Prime)
    (hpf : p ∣ 2 ^ f - 1) (hE : IsElementaryAbelian p E) (hEI : E ≤ I) (h₁ : K₁ ≤ I)
    (h₂ : K₂ ≤ I) (h₃ : K₃ ≤ I) (hgen : K₁ ⊔ K₂ ⊔ K₃ = I)
    (hm₁ : StatedClassicalModel ↥K₁ .PSL 2 2 (2 * f))
    (hm₂ : StatedClassicalModel ↥K₂ .PSL 2 2 (2 * f))
    (hm₃ : StatedClassicalModel ↥K₃ .PSL 2 2 f)
    (hcomm : K₁ ≤ Subgroup.centralizer (K₃ : Set G) ∧ K₁ ⊓ K₃ = ⊥)
    (hL : CentrallyLThree (2 * f) ↥(K₁ ⊔ K₂)) (hU : StatedClassicalModel ↥(K₂ ⊔ K₃) .PSU 4 2 f)
    (htor : CTTorusCondition p E ![K₁, K₂, K₃])
    (hstd : ¬ (E ⊓ K₃ ≤ Subgroup.centralizer (K₂ : Set G))) :
    StatedClassicalModel (↥I ⧸ Subgroup.center ↥I) .PSU 6 2 f := by
  obtain ⟨e12⟩ := nonempty_sup_subgroupOf_equiv h₁ h₂
  obtain ⟨e23⟩ := nonempty_sup_subgroupOf_equiv h₂ h₃
  exact h ↥I f p (K₁.subgroupOf I) (K₂.subgroupOf I) (K₃.subgroupOf I) (E.subgroupOf I) hf hp hpf
    (isElementaryAbelian_of_equiv (Subgroup.subgroupOfEquivOfLe hEI).symm hE)
    (sup_three_subgroupOf_eq_top h₁ h₂ h₃ hgen) (statedClassicalModel_subgroupOf h₁ hm₁)
    (statedClassicalModel_subgroupOf h₂ hm₂) (statedClassicalModel_subgroupOf h₃ hm₃)
    (commuting_subgroupOf hcomm) (centrallyLThree_of_equiv e12.symm hL)
    (statedClassicalModel_of_equiv e23.symm hU)
    (ctTorusCondition_subgroupOf_three hEI h₁ h₂ h₃ htor)
    (not_le_centralizer_subgroupOf hEI h₂ hstd)

end Subgroup

end CFSG.RankThree.PartOne
