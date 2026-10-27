module

public import CFSG.RankThree.PartOne.KF.CentralQuot

public section

namespace CFSG.RankThree.PartOne.KFU

theorem closure_comm_exp {G : Type*} [Group G] {p : ℕ} (S : Set G)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hexp : ∀ a ∈ S, a ^ p = 1) :
    (∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a) ∧
      ∀ a ∈ Subgroup.closure S, a ^ p = 1 := by
  have h1 : ∀ a ∈ Subgroup.closure S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {b} :=
      (Subgroup.closure_le _).mpr fun x hx y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hcomm y hb x hx
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b rfl).symm
  have h2 : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    intro a ha b hb
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {a} :=
      (Subgroup.closure_le _).mpr fun x hx y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact h1 y ha x hx
    exact (Subgroup.mem_centralizer_iff.mp (hle hb) a rfl)
  refine ⟨h2, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hexp x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := h2 x hx y hy
    rw [hc.mul_pow, ihx, ihy, mul_one]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem exists_toral_quot {G M P : Type} [Group G] [Group M] [Group P] {p : ℕ}
    {L F : Subgroup G} {T : Subgroup M}
    (q : M →* P) (hq : IsCentralPQuot p q) (ε₀ : ↥L →* P) (hε₀ : IsCentralPQuot p ε₀)
    (hTexp : ∀ t ∈ T, t ^ p = 1) (hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hDiag : ∀ X : Subgroup M, (∀ x ∈ X, x ^ p = 1) → (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) →
      ∃ g : M, ∀ x ∈ X, g * x * g⁻¹ ∈ T)
    (hFL : F ≤ L) (hFexp : ∀ f ∈ F, f ^ p = 1) (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hmax : ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → F ≤ F' → F' = F) :
    ∃ ε : ↥L →* P, IsCentralPQuot p ε ∧
      (∀ t ∈ T, ∃ f : F, ε (Subgroup.inclusion hFL f) = q t) ∧
      ∀ f : F, ∃ t ∈ T, ε (Subgroup.inclusion hFL f) = q t := by
  classical
  let Fl : F →* ↥L := Subgroup.inclusion hFL
  have hFlexp : ∀ f : F, Fl f ^ p = 1 := fun f =>
    Subtype.ext (hFexp _ f.2)
  let Fb : Subgroup P := (F.subgroupOf L).map ε₀
  have hFb_mem : ∀ f : F, ε₀ (Fl f) ∈ Fb := fun f => ⟨Fl f, Subgroup.mem_subgroupOf.mpr f.2, rfl⟩
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
  let Fh : Subgroup M :=
    { carrier := {x | x ^ p = 1 ∧ q x ∈ Fb}
      mul_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        have hc : Commute x y := hq.commute_of_map_commute hx1 (by
          show q x * q y = q y * q x
          exact hFb_comm _ hx2 _ hy2)
        refine ⟨?_, ?_⟩
        · rw [hc.mul_pow, hx1, hy1, mul_one]
        · rw [map_mul]
          exact Fb.mul_mem hx2 hy2
      one_mem' := ⟨one_pow p, by rw [map_one]; exact Fb.one_mem⟩
      inv_mem' := by
        rintro x ⟨hx1, hx2⟩
        exact ⟨by rw [inv_pow, hx1, inv_one], by rw [map_inv]; exact Fb.inv_mem hx2⟩ }
  have hFh_comm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x := fun x hx y hy =>
    (hq.commute_of_map_commute hx.1 (by
      show q x * q y = q y * q x
      exact hFb_comm _ hx.2 _ hy.2)).eq
  obtain ⟨g, hg⟩ := hDiag Fh (fun x hx => hx.1) hFh_comm
  let ε : ↥L →* P := (MulAut.conj (q g)).toMonoidHom.comp ε₀
  have hker : ε.ker = ε₀.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact MulEquiv.map_eq_one_iff (MulAut.conj (q g))
  have hε : IsCentralPQuot p ε :=
    ⟨(MulAut.conj (q g)).surjective.comp hε₀.surjective, hker ▸ hε₀.central, by
      rw [hker]; exact hε₀.coprime⟩
  have hεx : ∀ x : ↥L, ε x = q g * ε₀ x * (q g)⁻¹ := fun x => rfl
  have hstep3 : ∀ f : F, ∃ t ∈ T, ε (Fl f) = q t := by
    intro f
    obtain ⟨x, hx1, hx2⟩ := hq.exists_lift (hFb_exp _ (hFb_mem f))
    have hxF : x ∈ Fh := ⟨hx2, by rw [hx1]; exact hFb_mem f⟩
    refine ⟨g * x * g⁻¹, hg x hxF, ?_⟩
    rw [hεx, ← hx1, map_mul, map_mul, map_inv]
  refine ⟨ε, hε, ?_, hstep3⟩
  intro t ht
  have ht1 : q t ^ p = 1 := by rw [← map_pow, hTexp t ht, map_one]
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
      have := hTcomm t ht t' ht'
      rw [← map_mul, ← map_mul, this])
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
