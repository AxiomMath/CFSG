module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.Quasithin.H13.A6S13821Hat6b
public import CFSG.Quasithin.EmptyFaithful.R3c13A6
public import CFSG.Quasithin.Background.A318PHat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

private theorem w85g_eq_one_of_sq_cube {G : Type*} [Group G] {x : G}
    (h2 : x ^ 2 = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  calc x = x ^ 2 * x := by rw [h2, one_mul]
    _ = x ^ 3 := by group
    _ = 1 := h3

theorem isPerfect_of_barSituation {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : BarSituation X S) (hZ : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) : Group.IsPerfect X := by
  let π : X →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center X
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hmap : Subgroup.map π (commutator X) = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π hπ]
    exact commutator_alternatingGroup_eq_top (α := Fin 6) (by simp)
  have hsup : commutator X ⊔ Subgroup.center X = ⊤ := by
    have h := Subgroup.comap_map_eq (f := π) (commutator X)
    rw [hmap, Subgroup.comap_top, hker] at h
    exact h.symm
  have hS_le : (S : Set X) ⊆ (commutator X : Set X) := by
    intro s hs
    have hmem : s ∈ commutator X ⊔ Subgroup.center X := by rw [hsup]; trivial
    obtain ⟨c, hc, z, hz, hcz⟩ := (Subgroup.mem_sup_of_normal_right.mp hmem)
    have hqs2 : (QuotientGroup.mk s : X ⧸ commutator X) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow, hS.elemAbelian.2 s hs, QuotientGroup.mk_one]
    have hz3 : z ^ 3 = 1 := by
      have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Subgroup.center X))
      rw [hZ] at h
      simpa [Subgroup.coe_pow] using congrArg Subtype.val h
    have hqs : (QuotientGroup.mk s : X ⧸ commutator X) = 1 := by
      have hqcs : (QuotientGroup.mk s : X ⧸ commutator X) = QuotientGroup.mk z := by
        rw [← hcz, QuotientGroup.mk_mul]
        have hc1 : (QuotientGroup.mk c : X ⧸ commutator X) = 1 :=
          (QuotientGroup.eq_one_iff c).mpr hc
        rw [hc1, one_mul]
      refine w85g_eq_one_of_sq_cube hqs2 ?_
      rw [hqcs, ← QuotientGroup.mk_pow, hz3, QuotientGroup.mk_one]
    exact (QuotientGroup.eq_one_iff s).mp hqs
  have hperf : commutator X = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hS.normalClosure_eq_top]
    exact Subgroup.normalClosure_le_normal hS_le
  exact ⟨hperf⟩

theorem exists_mem_of_involutory {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    {S : Subgroup X} (hZ : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) (hS4 : Nat.card S = 4)
    (hS2 : ∀ s ∈ S, s * s = 1) {a : MulAut X} (ha2 : a * a = 1) (haS : ∀ s ∈ S, a s = s)
    (haZ : ∀ z ∈ Subgroup.center X, a z = z) :
    ∃ s ∈ S, ∀ x : X, (QuotientGroup.mk (a x) : X ⧸ Subgroup.center X) =
      QuotientGroup.mk (s * x * s⁻¹) := by
  obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.A6.Hat6.exists_inner_of_invol hZ e a ha2 haZ
  let π : X →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hkerS : ∀ s ∈ S, π s = 1 → s = 1 := by
    intro s hs h
    have hcenter : s ∈ Subgroup.center X := by
      have h' : e (QuotientGroup.mk s) = 1 := h
      rw [MulEquiv.map_eq_one_iff] at h'
      exact (QuotientGroup.eq_one_iff s).mp h'
    have hs3 : s ^ 3 = 1 := by
      have h3 := pow_card_eq_one' (x := (⟨s, hcenter⟩ : Subgroup.center X))
      rw [hZ] at h3
      simpa [Subgroup.coe_pow] using congrArg Subtype.val h3
    have hs2 : s ^ 2 = 1 := by rw [pow_two]; exact hS2 s hs
    exact w85g_eq_one_of_sq_cube hs2 hs3
  let E : Subgroup (alternatingGroup (Fin 6)) := S.map π
  have hEcard : Nat.card E = 4 := by
    have hmap_eq : (⊤ : Subgroup S).map (π.comp S.subtype) = E := by
      ext y
      constructor
      · rintro ⟨x, -, rfl⟩
        exact ⟨x.1, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    have hinj : Function.Injective (π.comp S.subtype) := by
      intro s t hst
      have hst' : π s.1 = π t.1 := hst
      have h1 : π (s.1 * t.1⁻¹) = 1 := by
        rw [map_mul, map_inv, hst', mul_inv_cancel]
      have h2 : s.1 * t.1⁻¹ = 1 :=
        hkerS _ (S.mul_mem s.2 (S.inv_mem t.2)) h1
      exact Subtype.ext (mul_inv_eq_one.mp h2)
    have hcard := Subgroup.card_map_of_injective (K := (⊤ : Subgroup S)) hinj
    rw [Subgroup.card_top, hS4, hmap_eq] at hcard
    exact hcard
  have hE2 : ∀ v ∈ E, v * v = 1 := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := hv
    rw [← map_mul, hS2 s hs, map_one]
  have hgE : g ∈ E := by
    refine CFSG.Quasithin.R3c13.kleinSelfCent_alt6 E hEcard hE2 g ?_
    intro v hv
    obtain ⟨s, hs, rfl⟩ := hv
    have h1 := hg s
    rw [haS s hs] at h1
    have h1' : π s = g * π s * g⁻¹ := h1
    calc g * π s = g * π s * g⁻¹ * g := by group
      _ = π s * g := by rw [← h1']
  obtain ⟨s₀, hs₀, hπs₀⟩ := hgE
  refine ⟨s₀, hs₀, fun x => ?_⟩
  apply e.injective
  rw [hg x, ← hπs₀]
  change e (QuotientGroup.mk s₀) * e (QuotientGroup.mk x) * (e (QuotientGroup.mk s₀))⁻¹ =
    e (QuotientGroup.mk (s₀ * x * s₀⁻¹))
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem card_le_of_forall_exists_conj {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    {S : Subgroup X} (A : Subgroup (MulAut X)) (haZ : ∀ a ∈ A, ∀ z ∈ Subgroup.center X, a z = z)
    (hconj : ∀ a ∈ A, ∃ s ∈ S, ∀ x : X, (QuotientGroup.mk (a x) : X ⧸ Subgroup.center X) =
      QuotientGroup.mk (s * x * s⁻¹)) :
    Nat.card A ≤ Nat.card S := by
  classical
  have hchoice : ∀ a : A, ∃ s ∈ S, ∀ x : X,
      (QuotientGroup.mk (a.1 x) : X ⧸ Subgroup.center X) =
        QuotientGroup.mk (s * x * s⁻¹) := fun a => hconj a.1 a.2
  choose s hsS hsP using hchoice
  let f : A → S := fun a => ⟨s a, hsS a⟩
  refine Nat.card_le_card_of_injective f ?_
  intro a b hab
  have hsab : s a = s b := congrArg Subtype.val hab
  apply Subtype.ext
  have hτ : (b : MulAut X)⁻¹ * (a : MulAut X) = 1 := by
    refine CFSG.Quasithin.A318P.mulAut_eq_one_of_inv_mul_mem_center ?_
    intro x
    have ha := hsP a x
    have hb := hsP b x
    have hmk : (QuotientGroup.mk (a.1 x) : X ⧸ Subgroup.center X) =
        QuotientGroup.mk (b.1 x) := by
      rw [ha, hb, hsab]
    have hzc : (b.1 x)⁻¹ * (a.1 x) ∈ Subgroup.center X :=
      QuotientGroup.eq.1 hmk.symm
    have hmem : (b.1)⁻¹ ((b.1 x)⁻¹ * (a.1 x)) ∈ Subgroup.center X := by
      have hmap := Subgroup.map_center_eq ((b.1)⁻¹)
      rw [← hmap]
      exact Subgroup.mem_map.mpr ⟨_, hzc, rfl⟩
    have heq : x⁻¹ * (((b.1)⁻¹ * (a.1) : MulAut X) x) =
        (b.1)⁻¹ ((b.1 x)⁻¹ * (a.1 x)) := by
      rw [MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply_self]
    rw [heq]
    exact hmem
  calc (a : MulAut X) = (b : MulAut X) * ((b : MulAut X)⁻¹ * (a : MulAut X)) := by group
    _ = (b : MulAut X) := by rw [hτ, mul_one]

theorem card_le_of_threeCover {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : BarSituation X S) (hZ : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) (hS4 : Nat.card S = 4)
    {A : Subgroup (MulAut X)} (hA : IsElemAbelian 2 A) (hAS : ∀ a ∈ A, ∀ s ∈ S, a s = s)
    (hAZ : ∀ a ∈ A, ∀ z ∈ Subgroup.center X, a z = z) : Nat.card A ≤ Nat.card S := by
  haveI := isPerfect_of_barSituation hS hZ e
  refine card_le_of_forall_exists_conj A hAZ fun a ha => ?_
  exact exists_mem_of_involutory hZ e hS4
    (fun s hs => by simpa [pow_two] using hS.elemAbelian.2 s hs)
    (by simpa [pow_two] using hA.2 a ha) (hAS a ha) (hAZ a ha)

theorem gap3_one_holds : ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X), BarSituation X S →
    Nat.card (Subgroup.center X) = 3 → SevenElevenASixShape X S →
    ∀ A : Subgroup (MulAut X), IsElemAbelian 2 A → (∀ a ∈ A, ∀ s ∈ S, a s = s) →
      (∀ a ∈ A, ∀ z ∈ Subgroup.center X, a z = z) → Nat.card A ≤ Nat.card S := by
  intro X _ _ S hS hZ hshape A hA hAS hAZ
  obtain ⟨⟨e⟩, hS4, -⟩ := hshape
  exact card_le_of_threeCover hS hZ e hS4 hA hAS hAZ

end CFSG.LocalAnalysis.WeakClosure81

end
