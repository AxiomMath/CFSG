module

public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.G10Comp
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Adapters.GeneralizedFittingTop

public section

namespace CFSG.Quasithin

namespace G11

theorem nonempty_mulEquiv_perm_of_normal_alt {G : Type} [Group G] [Finite G] {n : ℕ}
    (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (N : Subgroup G) [N.Normal]
    (e : ↥N ≃* ↥(alternatingGroup (Fin n)))
    (hC : ∀ c : G, (∀ h ∈ N, c * h = h * c) → c = 1) (hne : N ≠ ⊤) :
    Nonempty (G ≃* Equiv.Perm (Fin n)) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  let θ : G →* MulAut ↥N := MulAut.conjNormal
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    apply hC
    intro h hh
    have h1 := congrArg (fun f : MulAut ↥N => ((f ⟨h, hh⟩ : ↥N) : G)) hc
    have h2 : c * h * c⁻¹ = h := by simpa [θ, MulAut.conjNormal_apply] using h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  let eAut : MulAut ↥N ≃* Equiv.Perm (Fin n) :=
    (MulAut.congr e).trans (MulEquiv.ofBijective _ hbij).symm
  have hcardAut : Nat.card (MulAut ↥N) = n.factorial := by
    rw [Nat.card_congr eAut.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
  have hcardN : Nat.card ↥N * 2 = n.factorial := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    exact Nat.div_mul_cancel (Nat.dvd_factorial two_pos (by omega))
  have hcardG : n.factorial ≤ Nat.card G := by
    have h1 : N.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
    have h2 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h3 := Subgroup.card_mul_index N
    have h4 : 2 ≤ N.index := by omega
    calc n.factorial = Nat.card ↥N * 2 := hcardN.symm
      _ ≤ Nat.card ↥N * N.index := Nat.mul_le_mul_left _ h4
      _ = Nat.card G := h3
  have : Finite (MulAut ↥N) := Finite.of_equiv _ eAut.toEquiv.symm
  have hle : Nat.card (MulAut ↥N) ≤ Nat.card G := by
    rw [hcardAut]
    exact hcardG
  have hθbij : Function.Bijective θ := hθinj.bijective_of_nat_card_le hle
  exact ⟨(MulEquiv.ofBijective θ hθbij).trans eAut⟩

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem nonempty_mulEquiv_perm_of_alt [Finite V] {Γ H : Subgroup (GLV V)} {n : ℕ} (hn5 : 5 ≤ n)
    (hn6 : n ≠ 6) (hHΓ : H ≤ Γ) (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (e : ↥H ≃* ↥(alternatingGroup (Fin n)))
    (hC : ∀ c ∈ Γ, (∀ h ∈ H, c * h = h * c) → c = 1) (hx : ∃ x ∈ Γ, x ∉ H) :
    Nonempty (↥Γ ≃* Equiv.Perm (Fin n)) := by
  have : Finite (GLV V) := Finite.of_injective _ DFunLike.coe_injective
  have : (H.subgroupOf Γ).Normal := ⟨fun h hh g => by
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    have := hN (g : GLV V) g.2 (h : GLV V) hh
    simpa using this⟩
  refine nonempty_mulEquiv_perm_of_normal_alt hn5 hn6 (H.subgroupOf Γ)
    ((Subgroup.subgroupOfEquivOfLe hHΓ).trans e) (fun c hc => ?_) ?_
  · apply Subtype.ext
    refine hC c c.2 fun h hh => ?_
    have := hc ⟨h, hHΓ hh⟩ (by simpa [Subgroup.mem_subgroupOf] using hh)
    exact congrArg Subtype.val this
  · obtain ⟨x, hxΓ, hxH⟩ := hx
    intro htop
    have : (⟨x, hxΓ⟩ : ↥Γ) ∈ H.subgroupOf Γ := by rw [htop]; exact Subgroup.mem_top _
    exact hxH (by simpa [Subgroup.mem_subgroupOf] using this)

theorem layer_le_of_centralizer_eq_one [Finite V] {Γ H : Subgroup (GLV V)} (hHΓ : H ≤ Γ)
    (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hC : ∀ c ∈ Γ, (∀ h ∈ H, c * h = h * c) → c = 1) :
    (CFSG.Open.genFittingLayer ↥Γ).map Γ.subtype ≤ H := by
  have : Finite (GLV V) := Finite.of_injective _ DFunLike.coe_injective
  have : (H.subgroupOf Γ).Normal := ⟨fun h hh g => by
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    have := hN (g : GLV V) g.2 (h : GLV V) hh
    simpa using this⟩
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun J hJ => ?_
  have hsn : CFSG.Open.IsSubnormal (H.subgroupOf Γ) (⊤ : Subgroup ↥Γ) :=
    (CFSG.Adapters.isSubnormal_top_iff _).2 (Subgroup.Normal.isSubnormal inferInstance)
  rcases B113.component_le_or_commutator_eq_bot hJ hsn with hle | hcomm
  · exact hle
  · exfalso
    have hJ1 : J = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro j hj
      apply Subtype.ext
      refine hC j j.2 fun h hh => ?_
      have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm) hj
      have h2 := Subgroup.mem_centralizer_iff.1 h1 ⟨h, hHΓ hh⟩
        (by simpa [Subgroup.mem_subgroupOf] using hh)
      exact (congrArg Subtype.val h2).symm
    have hnt := (Comp.gwQuasisimple_of_open hJ.2.2).1
    rw [hJ1] at hnt
    exact not_nontrivial _ hnt

end G11

end CFSG.Quasithin
