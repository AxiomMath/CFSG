module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PerfectCoreCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi22SixInvolutionS3
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.RowAssembly
import all TauCeti.GroupTheory.Presentation.GroupPresentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.CosetTable CFSG.Sporadic.Presentation.Fi22Exact

theorem fi22F_of_mul_self (i : Fin 6) :
    (PresentedGroup.of i : PG 6 wsF) * PresentedGroup.of i = 1 := by
  have h : FreeGroup.mk [(i, true), (i, true)] ∈
      {r : FreeGroup (Fin 6) | r ∈ wsF.map FreeGroup.mk} := by
    simp only [Set.mem_ofPred_eq, List.mem_map, wsF, List.mem_append]
    exact ⟨[(i, true), (i, true)], Or.inl ⟨i, List.mem_finRange i, rfl⟩, rfl⟩
  have := PresentedGroup.one_of_mem h
  rw [← this]
  rfl


theorem fi22F_hom_word {H : Type*} [Group H] (φ : PG 6 wsF →* H) (w : List (Fin 6 × Bool)) :
    φ (PresentedGroup.mk _ (FreeGroup.mk w)) =
      (w.map fun p => cond p.2 (φ (PresentedGroup.of p.1)) (φ (PresentedGroup.of p.1))⁻¹).prod := by
  have h : φ.comp (PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ wsF.map FreeGroup.mk}) =
      FreeGroup.lift (fun i : Fin 6 => φ (PresentedGroup.of i)) := by
    apply FreeGroup.ext_hom
    intro i
    simp [PresentedGroup.of]
  have := DFunLike.congr_fun h (FreeGroup.mk w)
  rw [FreeGroup.lift_mk] at this
  exact this

theorem fi22F_closure_involutions :
    Subgroup.closure {x : PG 6 wsF | x * x = 1} = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of]
  apply Subgroup.closure_mono
  rintro _ ⟨i, rfl⟩
  exact fi22F_of_mul_self i

theorem fi22F_not_surjective_perm3 (φ : PG 6 wsF →* Equiv.Perm (Fin 3)) :
    ¬ Function.Surjective φ := by
  intro hφ
  have hconst := Fi22S3.six_involution_eq_of_relators (fun i => φ (PresentedGroup.of i))
    (fun i => by rw [← map_mul, fi22F_of_mul_self, map_one])
    (fun w hw => by
      rw [← fi22F_hom_word φ w]
      have : PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ wsF.map FreeGroup.mk}
          (FreeGroup.mk w) = 1 :=
        PresentedGroup.one_of_mem (by simp only [Set.mem_ofPred_eq, List.mem_map]; exact ⟨w, hw, rfl⟩)
      rw [this, map_one])
  have hrange : φ.range ≤ Subgroup.zpowers (φ (PresentedGroup.of 0)) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, hconst i]
    exact Subgroup.mem_zpowers _
  have htop : Subgroup.zpowers (φ (PresentedGroup.of 0)) = ⊤ := by
    rw [eq_top_iff, ← MonoidHom.range_eq_top_of_surjective φ hφ]
    exact hrange
  have : IsCyclic (Equiv.Perm (Fin 3)) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨_, htop⟩
  have hcomm := IsCyclic.isMulCommutative (α := Equiv.Perm (Fin 3))
  have h := hcomm.is_comm.comm (Equiv.swap 0 1) (Equiv.swap 1 2)
  revert h
  decide


open CFSG.Blueprint in
theorem fi22F_cover :
    ∃ θ : PG 6 wsF →* NativeSporadic.Carrier .Fi22, Finite (PG 6 wsF) ∧ Function.Surjective θ ∧
      Nat.card θ.ker ∣ 12 ∧ ∃ g ∈ θ.ker, 6 ∣ orderOf g := by
  obtain ⟨hfin, hcard⟩ := card_F_le
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  let e' : GG ≃* NativeSporadic.Carrier .Fi22 := e.symm
  let θ : PG 6 wsF →* NativeSporadic.Carrier .Fi22 := e'.toMonoidHom.comp thetaHom
  have hθ : Function.Surjective θ := e'.surjective.comp thetaHom_surjective
  have hg1 : θ (PresentedGroup.mk _ (FreeGroup.mk g1w)) = 1 := by
    show e' (thetaHom (PresentedGroup.mk _ (FreeGroup.mk g1w))) = 1
    rw [thetaHom_g1, map_one]
  have hfac := Subgroup.card_ker_mul_card_of_surjective hθ
  have hX : Nat.card (NativeSporadic.Carrier .Fi22) = 64561751654400 :=
    CFSG.Sporadic.Fi22.card_Fi22
  rw [hX] at hfac
  have hpos : 0 < Nat.card (PG 6 wsF) := Nat.card_pos
  have hle : Nat.card θ.ker ≤ 12 := by
    have : Nat.card θ.ker * 64561751654400 ≤ 12 * 64561751654400 := by omega
    exact Nat.le_of_mul_le_mul_right this (by norm_num)
  have h6 : 6 ∣ Nat.card θ.ker :=
    six_dvd_orderOf_g1.trans (Subgroup.orderOf_dvd_natCard θ.ker (MonoidHom.mem_ker.2 hg1))
  obtain ⟨k, hk⟩ := h6
  have hk12 : k = 1 ∨ k = 2 := by omega
  refine ⟨θ, hfin, hθ, ?_, _, hg1, six_dvd_orderOf_g1⟩
  rcases hk12 with rfl | rfl
  · exact ⟨2, by omega⟩
  · exact ⟨1, by omega⟩


open CFSG.Blueprint CFSG.RankThree.PerfectCover in
theorem fi22_native_facts :
    IsSimpleGroup (NativeSporadic.Carrier .Fi22) ∧ Group.IsPerfect (NativeSporadic.Carrier .Fi22) ∧
      Nat.card (NativeSporadic.Carrier .Fi22) = 64561751654400 := by
  have hs : IsSimpleGroup (NativeSporadic.Carrier .Fi22) := CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
  have hX : Nat.card (NativeSporadic.Carrier .Fi22) = 64561751654400 :=
    CFSG.Sporadic.Fi22.card_Fi22
  refine ⟨hs, ?_, hX⟩
  exact PerfectCoreCover.isPerfect_of_isSimpleGroup_of_not_prime (by rw [hX]; norm_num)

open CFSG.Blueprint CFSG.RankThree.PerfectCover in
theorem three_dvd_card_hopfMultiplier_Fi22 :
    3 ∣ Nat.card (hopfMultiplier (NativeSporadic.Carrier .Fi22)) := by
  obtain ⟨θ, hfin, hθ, hK, g, hg, hg6⟩ := fi22F_cover
  obtain ⟨hs, hp, hX⟩ := fi22_native_facts
  obtain ⟨E, _, _, hE, π, hπ, hc, h3⟩ := PerfectCoreCover.exists_perfect_central_cover_three_dvd
    θ hθ fi22F_closure_involutions fi22F_not_surjective_perm3 hK (by rw [hX]; decide)
    hg hg6
  exact h3.trans (CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hE π hπ hc)


theorem lift_conjW_gen {G : Type*} [Group G] (g : Fin 6 → G) (i : Fin 6) (c : List (Fin 6)) :
    FreeGroup.lift g (FreeGroup.mk (conjW i c)) = (c.map g).prod⁻¹ * g i * (c.map g).prod := by
  unfold conjW
  rw [FreeGroup.lift_mk]
  simp only [List.map_append, List.prod_append, List.map_map, List.map_reverse]
  simp [Function.comp_def, List.prod_inv_reverse]

theorem lift_qWord_gen {G : Type*} [Group G] (g : Fin 6 → G)
    (q : Fin 6 × List (Fin 6) × Fin 6 × List (Fin 6)) :
    FreeGroup.lift g (FreeGroup.mk (qWord q)) =
      ((q.2.1.map g).prod⁻¹ * g q.1 * (q.2.1.map g).prod) *
        ((q.2.2.2.map g).prod⁻¹ * g q.2.2.1 * (q.2.2.2.map g).prod)⁻¹ := by
  unfold qWord
  rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_inv, lift_conjW_gen, lift_conjW_gen]

theorem fi22F_exists_lift {E X : Type} [Group E] [Finite E] [Group X] (π : E →* X)
    (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker))
    (θ : PG 6 wsF →* X) : ∃ ψ : PG 6 wsF →* E, π.comp ψ = θ := by
  classical
  have hlift : ∀ i : Fin 6, ∃ t : E, π t = θ (PresentedGroup.of i) ∧ t * t = 1 := fun i =>
    PerfectCoreCover.exists_involution_lift π hπ hodd (by
      rw [← map_mul, fi22F_of_mul_self, map_one])
  choose f hf1 hf2 using hlift
  have hconj : ∀ (i : Fin 6) (c : List (Fin 6)),
      ((c.map f).prod⁻¹ * f i * (c.map f).prod) * ((c.map f).prod⁻¹ * f i * (c.map f).prod) = 1 := by
    intro i c
    calc ((c.map f).prod⁻¹ * f i * (c.map f).prod) * ((c.map f).prod⁻¹ * f i * (c.map f).prod)
        = (c.map f).prod⁻¹ * (f i * f i) * (c.map f).prod := by group
      _ = 1 := by rw [hf2 i]; group
  have hπlift : ∀ (w : List (Fin 6 × Bool)), π (FreeGroup.lift f (FreeGroup.mk w)) =
      θ (PresentedGroup.mk _ (FreeGroup.mk w)) := by
    intro w
    rw [fi22F_hom_word θ w, FreeGroup.lift_mk, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    rintro ⟨i, b⟩ _
    cases b <;> simp [hf1]
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ wsF.map FreeGroup.mk},
      FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map, wsF, List.mem_append] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rcases hw with hw | hw
    · obtain ⟨i, -, rfl⟩ := hw
      rw [FreeGroup.lift_mk]
      simp [hf2]
    · obtain ⟨q, hq, rfl⟩ := hw
      have hmem : FreeGroup.mk (qWord q) ∈ {r : FreeGroup (Fin 6) | r ∈ wsF.map FreeGroup.mk} :=
        List.mem_map.2 ⟨qWord q, List.mem_append_right _ (List.mem_map.2 ⟨q, hq, rfl⟩), rfl⟩
      have hker : π (FreeGroup.lift f (FreeGroup.mk (qWord q))) = 1 := by
        rw [hπlift, PresentedGroup.one_of_mem hmem, map_one]
      rw [lift_qWord_gen] at hker ⊢
      rw [map_mul, map_inv, mul_inv_eq_one] at hker
      rw [PerfectCoreCover.eq_of_involution_lift π hc hodd (hconj _ _) (hconj _ _) hker]
      exact mul_inv_cancel _
  refine ⟨PresentedGroup.toGroup hrel, ?_⟩
  apply PresentedGroup.ext
  intro i
  simp [PresentedGroup.toGroup.of, hf1]


open CFSG.Blueprint in
theorem card_ker_dvd_three_of_perfect_central_Fi22
    (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* NativeSporadic.Carrier .Fi22)
    (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E) (hp : IsPGroup 3 π.ker) :
    Nat.card π.ker ∣ 3 := by
  obtain ⟨θ, hfin, hθ, hK, -, -⟩ := fi22F_cover
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd (Nat.card π.ker) := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide)
  obtain ⟨ψ, hψ⟩ := fi22F_exists_lift π hπ hc hodd θ
  have hψs : Function.Surjective ψ :=
    PerfectCoreCover.surjective_of_perfect_of_central_ker π hc ψ (hψ ▸ hθ)
  have h1 := PerfectCoreCover.card_ker_dvd_card_ker_comp ψ π hψs hπ
  rw [hψ] at h1
  exact PerfectCoreCover.card_dvd_three_of_isPGroup_of_card_dvd_twelve hp (h1.trans hK)


open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster in
theorem nativeCell3_Fi22 :
    PrimaryCentralKernelOrder (NativeSporadic.Carrier .Fi22) 3 1 := by
  obtain ⟨-, hp, hX⟩ := fi22_native_facts
  have : Finite (NativeSporadic.Carrier .Fi22) := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine primaryCentralKernelOrder_of_bounds (fun E _ _ _ π hπ hc hpg => ?_) ?_
  · rw [pow_one]
    exact card_ker_dvd_three_of_perfect_central_Fi22 E π hπ hc hpg
  · rw [pow_one]
    exact three_dvd_card_hopfMultiplier_Fi22

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
