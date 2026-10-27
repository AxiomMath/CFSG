module

public import CFSG.Timmesfeld.Bridge.OddTranspBasic
public import CFSG.Timmesfeld.Bridge.Asc72Minimal
public import CFSG.Timmesfeld.Bridge.RootSetsSolv

public section

namespace CFSG.Timmesfeld.Bridge.OddTransp

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] {D : Set G}

theorem isRootInvolutionSet_of_isOddTransp (hD : IsOddTransp D) : IsRootInvolutionSet D := by
  refine ⟨hD.1, fun d hd e he => ?_, fun d hd e he h4 => ?_⟩
  · rcases hD.2 d hd e he with h | h
    · rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
      · right; right; rw [h1]; exact odd_one
      · left; exact h2
    · right; right; exact h
  · exfalso
    rcases hD.2 d hd e he with h | h <;> rw [h4] at h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by norm_num)
    · exact absurd h (by decide)

theorem eq_bot_of_isPGroup_quotient_pCore (N : Subgroup (G ⧸ CFSG.pCore 2 G)) (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 G)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hle : N.comap π ≤ CFSG.pCore 2 G :=
    le_sSup ⟨Subgroup.Normal.comap hN π, h2.comap_of_ker_isPGroup π hker⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 G) y
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr (hle hy)

theorem solvableRadical_eq_zStar [Finite G] (hS : Setup G D) (h : MeetsSq D) :
    CFSG.solvableRadical G = zStar G := by
  refine le_antisymm ?_ zStar_le_solvableRadical
  set P := CFSG.pCore 2 G
  set π := QuotientGroup.mk' P
  have hPs : Group.IsSolvable P := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (CFSG.pCore_isPGroup (p := 2) (G := G)).isNilpotent
    infer_instance
  have hπ1 : ∀ d ∈ D, π d ≠ 1 := fun d hd h1 =>
    not_mem_of_isSolvable hS h hPs hd ((QuotientGroup.eq_one_iff d).mp h1)
  have hS' := hS.map π (QuotientGroup.mk'_surjective P) hπ1
  obtain ⟨u, ⟨u', hu', rfl⟩, v, ⟨v', hv', rfl⟩, hne, hc, huv⟩ := h.map hS.oddT π hπ1
  have hRn : ((CFSG.solvableRadical G).map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective P)
  have hRs : Group.IsSolvable ((CFSG.solvableRadical G).map π) := by
    have := isSolvable_solvableRadical (G := G)
    refine Group.isSolvable_of_surjective
      (f := (π.comp (CFSG.solvableRadical G).subtype).codRestrict
        _ fun x => ⟨x, x.2, rfl⟩) ?_
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hcent := le_center_of_isSolvable hS'.isClass (isRootInvolutionSet_of_isOddTransp hS'.oddT)
    hS'.gen ⟨u', hu', rfl⟩ ⟨v', hv', rfl⟩ hne hc huv
    (fun N hN h2 => eq_bot_of_isPGroup_quotient_pCore N hN h2) hRn hRs
  intro x hx
  exact hcent ⟨x, hx, rfl⟩

theorem eq_bot_or_eq_top_of_normal [Finite G] (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (h : MeetsSq D)
    (N : Subgroup G) [N.Normal] : N = ⊥ ∨ N = ⊤ := by
  rcases hS.subset_or_disjoint N with hsub | hdisj
  · exact Or.inr (hS.eq_top_of_subset N hsub)
  left
  by_contra hN1
  obtain ⟨u, hu, v, hv, -, hc, huvD⟩ := h
  have hui : u⁻¹ = u := hS.oddT.inv_eq hu
  have h1 : u⁻¹ * v ∉ N := by rw [hui]; exact hdisj _ huvD
  have h2 : u⁻¹ * (u * v) ∉ N := by rw [inv_mul_cancel_left]; exact hdisj _ hv
  have huuv : Commute u (u * v) := (Commute.refl u).mul_right hc
  have key : ∀ x ∈ conjOrbit N u, Commute x u := by
    intro x hx
    have hxv := commute_of_mem_conjOrbit hS hu hv hc h1 hx (self_mem_conjOrbit N v)
    have hxuv := commute_of_mem_conjOrbit hS hu huvD huuv h2 hx (self_mem_conjOrbit N (u * v))
    have e : u = u * v * v := by rw [mul_assoc, hS.oddT.mul_self_eq_one hv, mul_one]
    rw [e]
    exact hxuv.mul_right hxv
  have hpair : ∀ x ∈ conjOrbit N u, ∀ y ∈ conjOrbit N u, Commute x y := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩
    have h3 := key ((m⁻¹ * m') * u * (m⁻¹ * m')⁻¹) ⟨m⁻¹ * m', N.mul_mem (N.inv_mem hm) hm', rfl⟩
    have h4 := h3.symm.map (MulAut.conj m).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h4
    convert h4 using 1
    group
  have hK : Subgroup.closure (conjOrbit N u) ⊓ N = ⊥ := by
    refine eq_bot_of_le_of_isSolvable hrad inf_le_right
      (fun m hm x hx => conj_mem_closure_conjOrbit_inf hm hx) ?_
    refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
    exact (Asc72.commute_of_mem_closure hpair a.2.1 b.2.1).eq
  exact not_mem_centralizer_of_ne_bot hS hrad hN1 hu (mem_centralizer_of_inf_eq_bot hK)

theorem isSimpleGroup_quotient_zStar [Finite G] (hS : Setup G D) (h : MeetsSq D) :
    IsSimpleGroup (G ⧸ zStar G) := by
  set R := CFSG.solvableRadical G
  have hRs : Group.IsSolvable R := isSolvable_solvableRadical
  set π := QuotientGroup.mk' R
  have hπ1 : ∀ d ∈ D, π d ≠ 1 := fun d hd h1 =>
    not_mem_of_isSolvable hS h hRs hd ((QuotientGroup.eq_one_iff d).mp h1)
  have hS' := hS.map π (QuotientGroup.mk'_surjective R) hπ1
  have h' : MeetsSq (π '' D) := h.map hS.oddT π hπ1
  have hrad : ∀ N : Subgroup (G ⧸ R), N.Normal → Group.IsSolvable N → N = ⊥ :=
    fun N hN hNs => eq_bot_of_quotient_solvableRadical N hN hNs
  have hsimple : IsSimpleGroup (G ⧸ R) := by
    obtain ⟨d, hd⟩ := hS'.nonempty
    have : Nontrivial (G ⧸ R) := ⟨⟨d, 1, hS'.oddT.ne_one hd⟩⟩
    exact ⟨fun N hN => eq_bot_or_eq_top_of_normal hS' hrad h' N⟩
  have e : G ⧸ zStar G ≃* G ⧸ R :=
    QuotientGroup.quotientMulEquivOfEq (solvableRadical_eq_zStar hS h).symm
  exact e.isSimpleGroup

theorem oddTranspSimple : OddTranspSimple := fun _ _ _ _ hS h =>
  ⟨solvableRadical_eq_zStar hS h, isSimpleGroup_quotient_zStar hS h⟩

end CFSG.Timmesfeld.Bridge.OddTransp
