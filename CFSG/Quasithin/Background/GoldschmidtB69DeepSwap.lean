module

public import CFSG.Quasithin.Background.B69SL3

public section

namespace CFSG.Quasithin

open B6

namespace B69

theorem exists_twist_element {V : Type} [CommGroup V] [Finite V] {X T M L : Subgroup (MulAut V)}
    (hmp : MinParabolic X T M) (hL : CFSG.Open.IsComponentOf L X) {G₀ : Type} [Group G₀]
    [Nontrivial G₀] {TP : MulAut G₀ → Prop} (hgeo : SwapGeo G₀ TP) (hev : Even (Nat.card G₀))
    (hZ : Subgroup.center G₀ = ⊥) (π₀ : ↥L →* G₀) (hπ₀ : Function.Surjective π₀) :
    ∃ t : MulAut V, (∀ x ∈ L, t * x * t⁻¹ ∈ L) ∧ (∀ x ∈ L, t⁻¹ * x * t ∈ L) ∧
      ∃ thb : MulAut G₀, (∀ l l' : ↥L, (l' : MulAut V) = t * l * t⁻¹ → thb (π₀ l) = π₀ l') ∧
        ¬ TP thb := by
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLX : L ≤ X := hL.1
  have : Finite (MulAut V) := MulEquiv.finite_left
  have hker₀ : π₀.ker = Subgroup.center ↥L := ker_eq_center_of_surj hLq hZ π₀ hπ₀
  have hLhat : CFSG.Open.IsComponentOf (L.subgroupOf X) ⊤ := isComponentOf_subgroupOf hL
  let e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  let πh : ↥(L.subgroupOf X) →* G₀ := π₀.comp e0.toMonoidHom
  have hπh : Function.Surjective πh := hπ₀.comp e0.surjective
  have hkerh : πh.ker = Subgroup.center ↥(L.subgroupOf X) :=
    ker_eq_center_of_surj hLhat.2.2 hZ πh hπh
  obtain ⟨t, -, htN, hall⟩ := exists_swap hgeo hev hmp.subgroupOf hLhat πh hπh hkerh
  have ht : ∀ x ∈ L, (t : MulAut V) * x * (t : MulAut V)⁻¹ ∈ L := by
    intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥X) ∈ (L.subgroupOf X) := hx
    have := (Subgroup.mem_normalizer_iff.mp htN ⟨x, hLX hx⟩).mp hx'
    exact this
  have ht' : ∀ x ∈ L, (t : MulAut V)⁻¹ * x * (t : MulAut V) ∈ L := by
    intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥X) ∈ (L.subgroupOf X) := hx
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem htN) ⟨x, hLX hx⟩).mp hx'
    exact this
  have htV : (t : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    mem_normalizer_of_forall_mem ht ht'
  obtain ⟨thb, hthb⟩ := exists_aut_of_ker_eq π₀ hπ₀ (indAut L (t : MulAut V)) (by
    intro l
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hker₀]
    exact mem_center_map_iff _ l)
  have hind : ∀ l l' : ↥L, (l' : MulAut V) = (t : MulAut V) * l * (t : MulAut V)⁻¹ →
      indAut L (t : MulAut V) l = l' := by
    intro l l' hl'
    apply Subtype.ext
    rw [coe_indAut_apply htV, hl']
  have hnot : ¬ TP thb := by
    refine hall thb fun l l' hl' => ?_
    have h1 : indAut L (t : MulAut V) (e0 l) = e0 l' := by
      apply hind
      show ((l' : ↥X) : MulAut V) = _
      rw [hl']
      rfl
    show thb (π₀ (e0 l)) = π₀ (e0 l')
    rw [hthb, h1]
  exact ⟨(t : MulAut V), ht, ht', thb, fun l l' hl' => by
    have := hthb l
    rw [hind l l' hl'] at this
    exact this, hnot⟩

end B69

end CFSG.Quasithin
