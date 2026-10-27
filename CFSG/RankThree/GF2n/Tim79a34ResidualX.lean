module

public import CFSG.RankThree.GF2n.Tim79a34SpFacts
public import CFSG.RankThree.GF2n.Tim79aIdentCore

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem eq_top_of_surjective_perfect {X Y : Type} [Group X] [Group Y] [Finite Y]
    (ψ : X →* Y) (hψ : Function.Surjective ψ) (hY : Group.IsPerfect Y) (L : Subgroup X)
    [L.Normal] (hker : ψ.ker ≤ L) (h2 : ∀ x : X, ∃ k : ℕ, x ^ 2 ^ k ∈ L) : L = ⊤ := by
  have hLn : (L.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
  have hQperf : Group.IsPerfect (Y ⧸ L.map ψ) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (L.map ψ))
      (QuotientGroup.mk'_surjective _)
  have hQ2 : IsPGroup 2 (Y ⧸ L.map ψ) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (L.map ψ) q
    obtain ⟨x, rfl⟩ := hψ y
    obtain ⟨k, hk⟩ := h2 x
    refine ⟨k, ?_⟩
    rw [← map_pow, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_map_of_mem ψ hk
  have hsub : Subsingleton (Y ⧸ L.map ψ) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (Y ⧸ L.map ψ) (IsPGroup.isNilpotent hQ2)
  have hLtop : L.map ψ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have h1 : (QuotientGroup.mk' (L.map ψ) y : Y ⧸ L.map ψ) = 1 :=
      Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff y).mp h1
  rw [eq_top_iff]
  intro x _
  have hx : ψ x ∈ L.map ψ := by rw [hLtop]; exact Subgroup.mem_top _
  obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hx
  have hk : l⁻¹ * x ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlx, inv_mul_cancel]
  have hmem : l⁻¹ * x ∈ L := hker hk
  have := L.mul_mem hl hmem
  simpa using this

variable {G : Type} [Group G]

theorem isPerfect_xbar_of_statedSp {n : ℕ} (hn : 3 ≤ n) {V H : Subgroup G}
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (e : ↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H) : Group.IsPerfect (Xbar V H) := by
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  haveI hP : Group.IsPerfect (StatedSp n (GaloisField 2 1)) :=
    Group.isPerfect_def.mpr (commutator_statedSp_eq_top hn hF)
  let e' : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  exact Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective

theorem xOf_le_pResidual_two [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H)
    (hperf : Group.IsPerfect (Xbar V H)) : xOf V H ≤ pResidual 2 G := by
  refine le_iInf fun N => le_iInf fun hN => le_iInf fun hp => ?_
  haveI : N.Normal := hN
  have hVH : V ≤ H := hc.V_le_H
  have hW : wOf V H ≤ xOf V H := wOf_le_xOf V H
  have hXH : xOf V H ≤ H := xOf_le_H hVH
  have hWn : ((wOf V H).subgroupOf (xOf V H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hW).2
      (fun x hx => H_le_normalizer_wOf V H (hXH hx))
  haveI : (N.subgroupOf (xOf V H)).Normal := hN.subgroupOf (xOf V H)
  let Lx : Subgroup ↥(xOf V H) := (N.subgroupOf (xOf V H)) ⊔ ((wOf V H).subgroupOf (xOf V H))
  haveI : Lx.Normal := Subgroup.sup_normal _ _
  let ψ : ↥(xOf V H) →* Xbar V H := xToXbar hVH
  have hψs : Function.Surjective ψ := xToXbar_surjective hVH
  have hker : ψ.ker ≤ Lx := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : ((ψ x : Xbar V H) : Hbar V H) = 1 := by rw [hx]; rfl
    rw [show ψ x = xToXbar hVH x from rfl, coe_xToXbar] at h1
    have h2 : (x : G) ∈ wOf V H := (piBar_eq_one_iff _).mp h1
    exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr h2)
  have h2 : ∀ x : ↥(xOf V H), ∃ k : ℕ, x ^ 2 ^ k ∈ Lx := by
    intro x
    obtain ⟨k, hk⟩ := hp (x : G)
    refine ⟨k, Subgroup.mem_sup_left ?_⟩
    rw [Subgroup.mem_subgroupOf]
    simpa using hk
  have hLtop : Lx = ⊤ := eq_top_of_surjective_perfect ψ hψs hperf Lx hker h2
  have hdec : ∀ x ∈ xOf V H, ∃ n ∈ N, ∃ u ∈ wOf V H, x = n * u := by
    intro x hx
    have hxL : (⟨x, hx⟩ : ↥(xOf V H)) ∈ Lx := by rw [hLtop]; exact Subgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_right).mp hxL
    refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, (z : G),
      Subgroup.mem_subgroupOf.mp hz, ?_⟩
    have := congrArg Subtype.val hyz
    simpa using this.symm
  have hWab : ∀ a ∈ wOf V H, ∀ b ∈ wOf V H, a * b = b * a := by
    intro a ha b hb
    have hc' := (hc.wOf_isElemAbelian).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val hc'
  have hWN : wOf V H ≤ N := by
    calc wOf V H = ⁅wOf V H, xOf V H⁆ := hc.commutator_wOf_xOf.symm
      _ ≤ N := by
        refine Subgroup.commutator_le.2 fun w hw x hx => ?_
        obtain ⟨n, hn, u, hu, rfl⟩ := hdec x hx
        have hwu : w * u = u * w := hWab w hw u hu
        have hcomm : Commute w u := hwu
        have hconj : u * w⁻¹ * u⁻¹ = w⁻¹ := by
          rw [← hcomm.inv_left.eq, mul_inv_cancel_right]
        have hcw : ⁅w, n⁆ ∈ N := by
          rw [commutatorElement_def]
          exact N.mul_mem (hN.conj_mem n hn w) (N.inv_mem hn)
        have key : ⁅w, n * u⁆ = ⁅w, n⁆ := by
          simp only [commutatorElement_def]
          calc w * (n * u) * w⁻¹ * (n * u)⁻¹ = w * n * (u * w⁻¹ * u⁻¹) * n⁻¹ := by group
            _ = w * n * w⁻¹ * n⁻¹ := by rw [hconj]
        rw [key]
        exact hcw
  intro x hx
  obtain ⟨n, hn, u, hu, rfl⟩ := hdec x hx
  exact N.mul_mem hn (hWN hu)

end CFSG.RankThree.GF2n.Tim79a
