module

public import CFSG.Quasithin.H13.NQCatLieCentralCore
public import CFSG.Quasithin.Vol2.F134LieU3

public section

namespace CFSG.Quasithin.H13.NQCat.LieCentral.U3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def commHom (h : UnitaryFieldData 2 f K) (a : K) : K →+ K where
  toFun c := h.bar c * a - h.bar a * c
  map_zero' := by simp
  map_add' c d := by
    rw [map_add]
    ring

theorem eq_zero_of_relIndex_le_two (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) {a b : K}
    (hab : h.norm a + h.trace b = 0)
    (hidx : (rkOneUStar h ⊓ Subgroup.centralizer ({rkOneU h a b hab} :
      Set (Equiv.Perm (hypIsotropicLines h 1 1)))).relIndex (rkOneUStar h) ≤ 2) : a = 0 := by
  have := h.finite
  have : Finite (Equiv.Perm (hypIsotropicLines h 1 1)) := inferInstance
  by_contra ha
  have hφ : Function.Surjective (rkOneAHom h) := fun m => by
    obtain ⟨d, hd⟩ := exists_norm_add_trace_eq_zero h (Multiplicative.toAdd m)
    exact ⟨⟨rkOneU h _ d hd, rkOneU_mem h hd⟩, by rw [rkOneAHom_rkOneU]; rfl⟩
  have h1 := card_range_le_two_of_commute' (rkOneAHom h) hφ (commHom h a) hidx (fun y hy => by
    obtain ⟨c, d, hcd, hy'⟩ := (mem_rkOneUStar h).mp y.2
    have hy'' : rkOneU h a b hab * rkOneU h c d hcd * (rkOneU h a b hab)⁻¹ *
        (rkOneU h c d hcd)⁻¹ = 1 := by
      rw [hy', ← hy, mul_inv_cancel_right, mul_inv_cancel]
    rw [rkOneU_commutator, ← rkOneU_zero_zero h] at hy''
    have h2 := (rkOneU_injective hy'').2
    have hyc : rkOneAHom h y = Multiplicative.ofAdd c := by
      rw [show y = ⟨rkOneU h c d hcd, rkOneU_mem h hcd⟩ from Subtype.ext hy'.symm,
        rkOneAHom_rkOneU]
    rw [hyc, toAdd_ofAdd]
    exact h2)
  have hker : Nat.card (AddMonoidHom.toMultiplicative (commHom h a)).ker ≤ 2 ^ f := by
    rw [← h.card_fixedField]
    refine Nat.card_le_card_of_injective (fun c =>
      ⟨Multiplicative.toAdd (c : Multiplicative K) / a, ?_⟩) fun c c' hcc => ?_
    · have hc := c.2
      rw [MonoidHom.mem_ker, AddMonoidHom.toMultiplicative_apply_apply, ← ofAdd_zero,
        Multiplicative.ofAdd.injective.eq_iff] at hc
      change h.bar _ * a - h.bar a * _ = 0 at hc
      rw [UnitaryFieldData.mem_fixedField, map_div₀]
      have hba : h.bar a ≠ 0 := (UnitaryFieldData.bar_eq_zero_iff h).not.2 ha
      rw [div_eq_div_iff hba ha]
      linear_combination hc
    · have h2 := congrArg Subtype.val hcc
      simp only at h2
      exact Subtype.ext (Multiplicative.toAdd.injective ((div_left_inj' ha).1 h2))
  have h3 := Subgroup.card_mul_index (AddMonoidHom.toMultiplicative (commHom h a)).ker
  rw [Subgroup.index_ker, show Nat.card (Multiplicative K) = Nat.card K from
    Nat.card_congr Multiplicative.toAdd, h.card_eq_sq] at h3
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h5 : (2 ^ f) ^ 2 ≤ 2 ^ f * 2 := by
    rw [← h3]
    exact Nat.mul_le_mul hker h1
  nlinarith

theorem centralIndex_rkOneG (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hU : IsSylowTwoOf (rkOneUStar h) (rkOneG h)) : CentralIndex ↥(rkOneG h) := by
  have := h.finite
  have : Finite (Equiv.Perm (hypIsotropicLines h 1 1)) := inferInstance
  refine centralIndex_of_le (rkOneUStar_le_rkOneG h) hU fun x hx hidx => ?_
  obtain ⟨a, b, hab, rfl⟩ := (mem_rkOneUStar h).mp hx
  have ha := eq_zero_of_relIndex_le_two h hf hab hidx
  subst ha
  have hC : rkOneU h 0 b hab ∈ rkOneC h :=
    (mem_rkOneC h).2 ⟨b, mem_traceZero_of_norm_zero h hab, rfl⟩
  rw [rkOneC_eq_center] at hC
  obtain ⟨z, hz, hzx⟩ := hC
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  rw [← hzx]
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩)

theorem centralIndex_psu3 {S : Type} [Group S] [Finite S] (hf : 2 ≤ f)
    (hS : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSU 3 2 f) : CentralIndex S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, h, Φ, hΦ, hrange, hT⟩ :=
    F134.LieU3.exists_perm_comap_rkOneUStar_eq hS (default : Sylow 2 S)
  have := h.finite
  have : Finite (Equiv.Perm (hypIsotropicLines h 1 1)) := inferInstance
  let e : S ≃* ↥(rkOneG h) :=
    (MonoidHom.ofInjective hΦ).trans (MulEquiv.subgroupCongr hrange)
  refine CentralIndex.of_mulEquiv e (centralIndex_rkOneG h hf ?_)
  have hUmap : ((default : Sylow 2 S) : Subgroup S).map Φ = rkOneUStar h := by
    rw [← hT, Subgroup.map_comap_eq, hrange, inf_eq_right.2 (rkOneUStar_le_rkOneG h)]
  have h1 := Setup.X6.isSylowOf_map_injective (p := 2) Φ hΦ
    (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 (isSylowTwoOf_top_of_sylow (default : Sylow 2 S)))
  rw [hUmap, ← MonoidHom.range_eq_map, hrange] at h1
  exact Setup.X6.isSylowTwoOf_iff_isSylowOf.2 h1

end CFSG.Quasithin.H13.NQCat.LieCentral.U3
