module

public import CFSG.Monster.B.TwoA.Amalgam.DistTwoModel
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphRoot

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

theorem orderOf_eq_or_two_mul_of_mk {G : Type*} [Group G] {c : G} (hc : c * c = 1)
    [(Subgroup.zpowers c).Normal] (z : G) :
    orderOf z = orderOf (z : G ⧸ Subgroup.zpowers c) ∨
      orderOf z = 2 * orderOf (z : G ⧸ Subgroup.zpowers c) := by
  obtain ⟨n, hn⟩ : ∃ n, orderOf (z : G ⧸ Subgroup.zpowers c) = n := ⟨_, rfl⟩
  rw [hn]
  have hd : n ∣ orderOf z := by
    rw [← hn]
    exact orderOf_map_dvd (QuotientGroup.mk' (Subgroup.zpowers c)) z
  have hz : z ^ n ∈ Subgroup.zpowers c := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hn, pow_orderOf_eq_one]
  have h2 : z ^ (2 * n) = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [mul_comm, pow_mul, ← hk, sq, ← (Commute.refl c).mul_zpow, hc, one_zpow]
  have hd2 : orderOf z ∣ 2 * n := orderOf_dvd_of_pow_eq_one h2
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · left
    rw [h0] at hd ⊢
    exact Nat.eq_zero_of_zero_dvd hd
  · obtain ⟨k, hk⟩ := hd
    rw [hk, mul_comm 2 n] at hd2
    rcases (Nat.dvd_prime Nat.prime_two).1 (Nat.dvd_of_mul_dvd_mul_left hpos hd2) with rfl | rfl
    · left
      rw [hk, mul_one]
    · right
      rw [hk, mul_comm]

theorem exists_eq_cvMul_nbr
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) {a : CVert}
    (ha : cgraph.Adj v a) :
    ∃ e : Eam, a = cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s := by
  subst hs
  have h : cgraph.Adj cv0 (cvMul a s⁻¹) := by
    have h1 := (cgraph_adj_cvMul (cvMul cv0 s) a s⁻¹).2 ha
    rwa [cvMul_inv_cancel] at h1
  obtain ⟨u, hu⟩ := exists_nbr_of_adj a0_mem_Ehat a0_not_mem_N1 h
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective u
  exact ⟨e, by rw [hu, cvMul_inv_cancel']⟩

theorem orderOf_clabel_mul_of_root
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) {v : CVert}
    {s : Shat} (hs : cvMul cv0 s = v) (iv : cgraph.neighborSet v ≃ rootClass)
    (H1 : ∀ (e : Eam) (h : cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s ∈
        cgraph.neighborSet v),
      SemidirectProduct.inl (iv ⟨_, h⟩ : stdGroup) = θ (QuotientGroup.mk (xconj e)))
    (a b : cgraph.neighborSet v) :
    orderOf (clabel a * clabel b) = orderOf ((SemidirectProduct.inl (iv a : stdGroup) : GStar) *
        SemidirectProduct.inl (iv b : stdGroup)) ∨
      orderOf (clabel a * clabel b) =
        2 * orderOf ((SemidirectProduct.inl (iv a : stdGroup) : GStar) *
          SemidirectProduct.inl (iv b : stdGroup)) := by
  obtain ⟨e, he⟩ := exists_eq_cvMul_nbr hs a.2
  obtain ⟨f, hf⟩ := exists_eq_cvMul_nbr hs b.2
  have hpa : (SemidirectProduct.inl (iv a : stdGroup) : GStar) =
      θ (QuotientGroup.mk (xconj e)) := by
    rw [← H1 e (he ▸ a.2)]
    exact congrArg (fun z => (SemidirectProduct.inl (iv z : stdGroup) : GStar)) (Subtype.ext he)
  have hpb : (SemidirectProduct.inl (iv b : stdGroup) : GStar) =
      θ (QuotientGroup.mk (xconj f)) := by
    rw [← H1 f (hf ▸ b.2)]
    exact congrArg (fun z => (SemidirectProduct.inl (iv z : stdGroup) : GStar)) (Subtype.ext hf)
  have hl : clabel a * clabel b = ((s : Dfull))⁻¹ * ((xconj e * xconj f : Eam) : Dfull) * s := by
    rw [he, hf, clabel_cvMul, clabel_cvMul, clabel_nbr, clabel_nbr]
    have hxe : (e : Dfull)⁻¹ * xhat * e ∈ Eam := (xconj e).2
    calc ((s : Dfull))⁻¹ * (cQ * ((e : Dfull)⁻¹ * xhat * e)) * s *
          (((s : Dfull))⁻¹ * (cQ * ((f : Dfull)⁻¹ * xhat * f)) * s)
        = ((s : Dfull))⁻¹ * ((cQ * ((e : Dfull)⁻¹ * xhat * e)) *
          (cQ * ((f : Dfull)⁻¹ * xhat * f))) * s := by group
      _ = ((s : Dfull))⁻¹ * (((e : Dfull)⁻¹ * xhat * e) * ((f : Dfull)⁻¹ * xhat * f)) * s := by
          rw [mul_mul_of_comm (cQ_comm_of_mem_Eam hxe) cQ_mul_self]
      _ = ((s : Dfull))⁻¹ * ((xconj e * xconj f : Eam) : Dfull) * s := rfl
  have h1 : orderOf (clabel a * clabel b) = orderOf (xconj e * xconj f) := by
    rw [hl, ← Subgroup.orderOf_coe (xconj e * xconj f)]
    exact (SemiconjBy.orderOf_eq ((s : Dfull))⁻¹ (by unfold SemiconjBy; group)).symm
  have h2 : orderOf ((SemidirectProduct.inl (iv a : stdGroup) : GStar) *
      SemidirectProduct.inl (iv b : stdGroup)) =
        orderOf (QuotientGroup.mk (xconj e * xconj f) : Eam ⧸ Subgroup.zpowers cE') := by
    rw [hpa, hpb, ← map_mul θ, ← QuotientGroup.mk_mul, MulEquiv.orderOf_eq]
  rw [h1, h2]
  exact orderOf_eq_or_two_mul_of_mk (Subtype.ext cQ_mul_self) _

theorem exists_rootModel
    (v : CVert) : ∃ M : RootModel v, M.LabelCompat := by
  obtain ⟨θ, -, hθ⟩ := native_coset_graph_exact_root_local_geometry
  obtain ⟨s, hs, iv, H1, H2, H3, H4, -⟩ := hθ v
  refine ⟨⟨iv, H2, fun γ => ?_, fun y hy => ?_⟩, orderOf_clabel_mul_of_root θ hs iv H1⟩
  · obtain ⟨y, rfl⟩ := H4 γ
    exact ⟨y, y.2, fun u => ⟨(stabAct y u).2, H3 y u⟩⟩
  · exact ⟨rhoV θ hs ⟨y, hy⟩, fun u => ⟨(stabAct ⟨y, hy⟩ u).2, H3 ⟨y, hy⟩ u⟩⟩

end CFSG.Monster.B.TwoA.Amalgam
