module

public import CFSG.RankThree.PartOne.CTP.SeitzToral

public section

namespace CFSG.RankThree.PartOne.CTP

theorem closure_centralizers_of_lift {G Q : Type*} [Group G] [Group Q] [Finite G] {p : ℕ}
    [Fact p.Prime] (π : G →* Q) (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker)
    (E : Subgroup Q) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hG : ∀ E' : Subgroup G, (∀ a ∈ E', ∀ b ∈ E', a * b = b * a) → (∀ a ∈ E', a ^ p = 1) →
      Nat.card E' = Nat.card E → (IsCyclic E' → IsCyclic E) →
      Subgroup.closure {h : G | ∃ x ∈ E', x ≠ 1 ∧ h * x = x * h} = ⊤) :
    Subgroup.closure {k : Q | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨E', hE'map, hE'dis⟩ := SeitzToral.exists_lift_of_coprime_ker π hπ hker E hEp
  have hE'mem : ∀ x ∈ E', π x ∈ E := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' := E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha))
      (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have := hcomm _ (hE'mem a ha) _ (hE'mem b hb)
      rw [this]
      group
    have := Subgroup.disjoint_def.mp hE'dis hc hk
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
    intro a ha
    have hk : a ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hexp _ (hE'mem a ha)
    exact Subgroup.disjoint_def.mp hE'dis (E'.pow_mem ha p) hk
  let fπ : E' →* E := (π.comp E'.subtype).codRestrict E (fun x => hE'mem x.1 x.2)
  have hfπsurj : Function.Surjective fπ := by
    intro e
    have : (e : Q) ∈ E'.map π := hE'map ▸ e.2
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hfπinj : Function.Injective fπ := by
    intro x y hxy
    have h1 : π x.1 = π y.1 := congrArg Subtype.val hxy
    have h2 : x.1⁻¹ * y.1 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : x.1⁻¹ * y.1 = 1 :=
      Subgroup.disjoint_def.mp hE'dis (E'.mul_mem (E'.inv_mem x.2) y.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have hcard : Nat.card E' = Nat.card E :=
    Nat.card_congr (Equiv.ofBijective fπ ⟨hfπinj, hfπsurj⟩)
  have htop := hG E' hE'comm hE'exp hcard fun _ => isCyclic_of_surjective fπ hfπsurj
  rw [eq_top_iff]
  have : (Subgroup.closure {h : G | ∃ x ∈ E', x ≠ 1 ∧ h * x = x * h}).map π ≤ Subgroup.closure
      {k : Q | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨h, ⟨x, hx, hx1, hxc⟩, rfl⟩
    refine Subgroup.subset_closure ⟨π x, hE'mem x hx, ?_, by rw [← map_mul, ← map_mul, hxc]⟩
    intro hπx
    exact hx1 (Subgroup.disjoint_def.mp hE'dis hx (by rwa [MonoidHom.mem_ker]))
  rw [htop, Subgroup.map_top_of_surjective π hπ] at this
  exact this

end CFSG.RankThree.PartOne.CTP
