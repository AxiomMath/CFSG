module

public import CFSG.RankThree.PartOne.KF.ToralQuot

public section

namespace CFSG.RankThree.PartOne.KFU

theorem exists_toral_quot_aut {G P : Type} [Group G] [Group P] {p : ℕ}
    {L F A : Subgroup G} {T : Subgroup P}
    (ε₀ : ↥L →* P) (hε₀ : IsCentralPQuot p ε₀)
    (hTexp : ∀ t ∈ T, t ^ p = 1) (hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hFL : F ≤ L) (hAF : A ≤ F)
    (hDiag : ∀ X : Subgroup P, (∀ x ∈ X, x ^ p = 1) → (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) →
      (∀ (a : G) (ha : a ∈ A), ε₀ (Subgroup.inclusion (hAF.trans hFL) ⟨a, ha⟩) ∈ X) →
      ∃ α : MulAut P, ∀ x ∈ X, α x ∈ T)
    (hFexp : ∀ f ∈ F, f ^ p = 1) (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hmax : ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → F ≤ F' → F' = F) :
    ∃ ε : ↥L →* P, IsCentralPQuot p ε ∧
      (∀ t ∈ T, ∃ f : F, ε (Subgroup.inclusion hFL f) = t) ∧
      ∀ f : F, ∃ t ∈ T, ε (Subgroup.inclusion hFL f) = t := by
  classical
  let Fl : F →* ↥L := Subgroup.inclusion hFL
  have hFlexp : ∀ f : F, Fl f ^ p = 1 := fun f => Subtype.ext (hFexp _ f.2)
  let Fb : Subgroup P := (F.subgroupOf L).map ε₀
  have hFb_mem : ∀ f : F, ε₀ (Fl f) ∈ Fb := fun f =>
    ⟨Fl f, Subgroup.mem_subgroupOf.mpr f.2, rfl⟩
  have hFb_comm : ∀ a ∈ Fb, ∀ b ∈ Fb, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hFcomm _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy)
  have hFb_exp : ∀ a ∈ Fb, a ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (hFexp _ (Subgroup.mem_subgroupOf.mp hx))
    rw [this, map_one]
  obtain ⟨α, hα⟩ := hDiag Fb hFb_exp hFb_comm (fun a ha => hFb_mem ⟨a, hAF ha⟩)
  let ε : ↥L →* P := α.toMonoidHom.comp ε₀
  have hker : ε.ker = ε₀.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact MulEquiv.map_eq_one_iff α
  have hε : IsCentralPQuot p ε :=
    ⟨α.surjective.comp hε₀.surjective, hker ▸ hε₀.central, by rw [hker]; exact hε₀.coprime⟩
  have hεx : ∀ x : ↥L, ε x = α (ε₀ x) := fun x => rfl
  have hstep3 : ∀ f : F, ∃ t ∈ T, ε (Fl f) = t := fun f =>
    ⟨α (ε₀ (Fl f)), hα _ (hFb_mem f), rfl⟩
  refine ⟨ε, hε, ?_, hstep3⟩
  intro t ht
  have ht1 : t ^ p = 1 := hTexp t ht
  obtain ⟨y, hy1, hy2⟩ := hε.exists_lift ht1
  set S : Set G := insert (y : G) (F : Set G) with hS
  have hSL : S ⊆ L := by
    intro x hx
    rcases hx with rfl | hx
    · exact y.2
    · exact hFL hx
  have hyF : ∀ f ∈ F, (y : G) * f = f * (y : G) := by
    intro f hf
    obtain ⟨t', ht', hft'⟩ := hstep3 ⟨f, hf⟩
    have hc : Commute y (Fl ⟨f, hf⟩) := hε.commute_of_map_commute hy2 (by
      show ε y * ε (Fl ⟨f, hf⟩) = ε (Fl ⟨f, hf⟩) * ε y
      rw [hy1, hft']
      exact hTcomm t ht t' ht')
    have := congrArg (fun x : ↥L => (x : G)) hc.eq
    exact this
  have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact hyF b hb
    · exact (hyF a ha).symm
    · exact hFcomm a ha b hb
  have hSexp : ∀ a ∈ S, a ^ p = 1 := by
    intro a ha
    rcases ha with rfl | ha
    · have := congrArg (fun x : ↥L => (x : G)) hy2
      simpa using this
    · exact hFexp a ha
  obtain ⟨hcl1, hcl2⟩ := closure_comm_exp S hScomm hSexp
  have hFle : F ≤ Subgroup.closure S := fun f hf =>
    Subgroup.subset_closure (Set.mem_insert_of_mem _ hf)
  have hF'eq := hmax (Subgroup.closure S) ((Subgroup.closure_le _).mpr hSL) hcl2 hcl1 hFle
  have hyF' : (y : G) ∈ F := by
    rw [← hF'eq]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  exact ⟨⟨y, hyF'⟩, hy1⟩

end CFSG.RankThree.PartOne.KFU
