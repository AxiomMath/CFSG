module

public import CFSG.RankThree.PartOne.KC.LinearThreeFourInnerDefining

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank

theorem inSubgroup_theta_solvable_normal_prime_complement {M : Type*} [Group M] [Finite M]
    {p : ℕ} (hp : p.Prime) (C : Subgroup M) :
    inSubgroup (aschbacherSolvableCore p) C ≤ C ∧
      ((inSubgroup (aschbacherSolvableCore p) C).subgroupOf C).Normal ∧
      ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore p) C) ∧
      Group.IsSolvable (inSubgroup (aschbacherSolvableCore p) C) := by
  obtain ⟨h1, h2, h3⟩ := inSubgroup_theta_normal_prime_complement hp C
  refine ⟨h1, h2, h3, ?_⟩
  have := (solvable_prime_complement_core_characterization (H := C) hp).1
  exact Group.isSolvable_of_surjective (C.subtype.subgroupMap_surjective _)

theorem inSubgroup_theta_centralizer_eq_bot_of_simple_fixed_group {T : Type*} [Group T] [Finite T]
    {p : ℕ} (hp : p.Prime) (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    {a : MulAut T} (hord : orderOf a = p) {H : Subgroup T} (hH : ∀ x : T, x ∈ H ↔ a x = x)
    (hsimple : IsSimpleGroup H) (hnonab : ¬ ∀ x y : H, x * y = y * x)
    (hstab : ∀ s : MulAut T, (∀ x ∈ H, s x = x) → s ∈ zpowers a)
    {B : Subgroup (MulAut T)} (hB : (MulAut.conj : T →* MulAut T).range ≤ B) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer ({a} : Set (MulAut T))) =
      ⊥ := by
  classical
  have : Finite (MulAut T) := inferInstance
  set C : Subgroup (MulAut T) := B ⊓ Subgroup.centralizer ({a} : Set (MulAut T)) with hC
  set W : Subgroup (MulAut T) := H.map (MulAut.conj : T →* MulAut T) with hW
  obtain ⟨hSC, hSn, hSp, hSs⟩ := inSubgroup_theta_solvable_normal_prime_complement hp C
  generalize inSubgroup (aschbacherSolvableCore p) C = S at hSC hSn hSp hSs ⊢
  have hSnorm : ∀ y ∈ C, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    have := hSn.conj_mem ⟨s, hSC hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hcH : ∀ c ∈ C, ∀ x ∈ H, c x ∈ H := by
    intro c hc x hx
    have hca : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.1 hc).2
    have h1 := congrArg (fun γ : MulAut T => γ x) hca
    simp only [MulAut.mul_apply] at h1
    rw [hH] at hx ⊢
    rw [hx] at h1
    exact h1.symm
  have hWC : W ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hB ⟨x, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := CFSG.RankThree.RegularUnipotent.conj_apply_mulAut a x
    rw [(hH x).mp hx] at h1
    calc MulAut.conj x * a = (a * MulAut.conj x * a⁻¹) * a := by rw [← h1]
      _ = a * MulAut.conj x := by group
  have hWnorm : ∀ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    rintro c hc _ ⟨x, hx, rfl⟩
    exact ⟨c x, hcH c hc x hx, CFSG.RankThree.RegularUnipotent.conj_apply_mulAut c x⟩
  have hSWtriv : ∀ x ∈ H, MulAut.conj x ∈ S → x = 1 := by
    intro x hx hxS
    let N : Subgroup H := S.comap ((MulAut.conj : T →* MulAut T).comp H.subtype)
    have hNn : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hgC : (MulAut.conj (g : T) : MulAut T) ∈ C := hWC ⟨g, g.2, rfl⟩
      have := hSnorm _ hgC _ hn
      simpa [N, map_mul, map_inv] using this
    have := hNn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · have hmem : (⟨x, hx⟩ : H) ∈ N := hxS
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exfalso
      apply hnonab
      rw [IsSimpleGroup.comm_iff_isSolvable (G := H)]
      let f : H →* S := ((MulAut.conj : T →* MulAut T).comp H.subtype).codRestrict S
        (fun y => by
          have : y ∈ N := h ▸ Subgroup.mem_top y
          exact this)
      have hfinj : Function.Injective f := by
        intro y z hyz
        apply Subtype.ext
        apply hinj
        exact congrArg Subtype.val hyz
      exact Group.isSolvable_of_isSolvable_injective hfinj
  have hSpt : ∀ s ∈ S, ∀ x ∈ H, s x = x := by
    intro s hs x hx
    have hsC := hSC hs
    have hWx : MulAut.conj x ∈ W := ⟨x, hx, rfl⟩
    have h1 : s * MulAut.conj x * s⁻¹ * (MulAut.conj x)⁻¹ ∈ W :=
      W.mul_mem (hWnorm s hsC _ hWx) (W.inv_mem hWx)
    have h2 : s * MulAut.conj x * s⁻¹ * (MulAut.conj x)⁻¹ ∈ S := by
      have := S.mul_mem hs (hSnorm _ (hWC hWx) s⁻¹ (S.inv_mem hs))
      rwa [← mul_assoc, ← mul_assoc] at this
    obtain ⟨y, hy, hyeq⟩ := h1
    have hyS : MulAut.conj y ∈ S := hyeq ▸ h2
    have hy1 : y = 1 := hSWtriv y hy hyS
    rw [hy1, map_one] at hyeq
    have h3 : s * MulAut.conj x = MulAut.conj x * s := by
      calc s * MulAut.conj x
          = s * MulAut.conj x * s⁻¹ * (MulAut.conj x)⁻¹ * (MulAut.conj x * s) := by group
        _ = MulAut.conj x * s := by rw [← hyeq, one_mul]
    apply hinj
    rw [CFSG.RankThree.RegularUnipotent.conj_apply_mulAut, h3, mul_inv_cancel_right]
  have hSle : S ≤ zpowers a := fun s hs => hstab s (hSpt s hs)
  have hdvd : Nat.card S ∣ p := by
    have := Subgroup.card_dvd_of_le hSle
    rwa [Nat.card_zpowers, hord] at this
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exact absurd (h ▸ dvd_refl _) hSp

end CFSG.RankThree.PartOne
