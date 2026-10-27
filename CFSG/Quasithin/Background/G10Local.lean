module

public import CFSG.Quasithin.Background.G10Clifford

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace G11

@[expose] def fixIn (X : Subgroup (GLV V)) (w : V) : Subgroup (GLV V) :=
  X ⊓ MulAction.stabilizer (GLV V) w

theorem sup_eq_of_relIndex_two {G : Type*} [Group G] {K K' X : Subgroup G} (hK : K ≤ X)
    (hK' : K' ≤ X) (h : K.relIndex X = 2) (h' : K'.relIndex X = 2) (hne : K ≠ K') :
    K ⊔ K' = X := by
  have hM : K ⊔ K' ≤ X := sup_le hK hK'
  have h1 := Subgroup.relIndex_mul_relIndex K (K ⊔ K') X le_sup_left hM
  have h2 := Subgroup.relIndex_mul_relIndex K' (K ⊔ K') X le_sup_right hM
  rw [h] at h1
  rw [h'] at h2
  have hdvd : (K ⊔ K').relIndex X ∣ 2 := ⟨K.relIndex (K ⊔ K'), by rw [← h1, mul_comm]⟩
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h3 | h3
  · exact le_antisymm hM (Subgroup.relIndex_eq_one.1 h3)
  · exfalso
    rw [h3] at h1 h2
    have e1 : K.relIndex (K ⊔ K') = 1 := by omega
    have e2 : K'.relIndex (K ⊔ K') = 1 := by omega
    have l1 : K ⊔ K' ≤ K := Subgroup.relIndex_eq_one.1 e1
    have l2 : K ⊔ K' ≤ K' := Subgroup.relIndex_eq_one.1 e2
    exact hne (le_antisymm (le_sup_left.trans l2) (le_sup_right.trans l1))

end G11

namespace G101Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)} (h : G101Hyp B Γ v₁ W X X₀)

include h

theorem apply_eq_or {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ X) {w : V} (hw : w ∈ W) :
    x w = w ∨ x w = w + v₁ := by
  obtain ⟨f, -, hf⟩ := h.transvection x hx
  have h1 := hf ⟨w, hw⟩
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc (f ⟨w, hw⟩) with h0 | h0
  · left
    rw [h0, zero_smul, add_zero] at h1
    exact h1
  · right
    rw [h0, one_smul] at h1
    exact h1

theorem exists_apply_eq_add {w : V} (hw : w ∈ W) (hwv : w ∉ Submodule.span (ZMod 2) {v₁}) :
    ∃ x ∈ X, x w = w + v₁ := by
  have hnot : (⟨w, hw⟩ : W) ∉ Submodule.span (ZMod 2) {(⟨v₁, h.mem_W⟩ : W)} := by
    intro hmem
    apply hwv
    have := Submodule.apply_mem_span_image_of_mem_span W.subtype hmem
    simpa [Set.image_singleton] using this
  obtain ⟨f, hfw, hfv⟩ := Submodule.exists_le_ker_of_notMem hnot
  have hc : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hf1 : f ⟨w, hw⟩ = 1 := hc _ hfw
  have hf0 : f ⟨v₁, h.mem_W⟩ = 0 := hfv (Submodule.mem_span_singleton_self _)
  obtain ⟨x, hx, hxf⟩ := h.transvection_full f hf0
  refine ⟨x, hx, ?_⟩
  have := hxf ⟨w, hw⟩
  rw [hf1, one_smul] at this
  exact this

theorem relIndex_fixIn {w : V} (hw : w ∈ W) (hwv : w ∉ Submodule.span (ZMod 2) {v₁}) :
    (fixIn X w).relIndex X = 2 := by
  have hsub : (fixIn X w).subgroupOf X = MulAction.stabilizer ↥X w := by
    ext x
    simp only [fixIn, MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      SetLike.coe_mem, true_and]
    rfl
  rw [Subgroup.relIndex, hsub, MulAction.index_stabilizer]
  have horb : MulAction.orbit ↥X w = {w, w + v₁} := by
    ext z
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      rcases h.apply_eq_or hx hw with h0 | h0
      · exact Or.inl h0
      · exact Or.inr h0
    · rintro (rfl | rfl)
      · exact MulAction.mem_orbit_self _
      · obtain ⟨x, hx, hxw⟩ := h.exists_apply_eq_add hw hwv
        exact ⟨⟨x, hx⟩, hxw⟩
  rw [horb, Set.ncard_pair]
  intro heq
  apply h.point
  simpa using heq

theorem fixIn_ne {w w' : V} (hw : w ∈ W) (hw' : w' ∈ W) (hwv : w ∉ Submodule.span (ZMod 2) {v₁})
    (hw'v : w' ∉ Submodule.span (ZMod 2) {v₁, w}) : fixIn X w ≠ fixIn X w' := by
  intro heq
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hnot : (⟨w, hw⟩ : W) ∉
      Submodule.span (ZMod 2) {(⟨v₁, h.mem_W⟩ : W), (⟨w', hw'⟩ : W)} := by
    intro hmem
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hmem
    have hab' : a • v₁ + b • w' = w := congrArg Subtype.val hab
    rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl
    · apply hwv
      rw [zero_smul, zero_smul, add_zero] at hab'
      rw [← hab']
      exact Submodule.zero_mem _
    · apply hw'v
      rw [zero_smul, one_smul, zero_add] at hab'
      rw [hab']
      exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
    · apply hwv
      rw [one_smul, zero_smul, add_zero] at hab'
      rw [← hab']
      exact Submodule.mem_span_singleton_self _
    · apply hw'v
      rw [one_smul, one_smul] at hab'
      have h2v : v₁ + v₁ = 0 := by
        rw [← two_smul (ZMod 2) v₁, show (2 : ZMod 2) = 0 from rfl, zero_smul]
      have hw'eq : w' = w + v₁ := by
        rw [← hab']
        calc w' = w' + 0 := (add_zero w').symm
          _ = w' + (v₁ + v₁) := by rw [h2v]
          _ = v₁ + w' + v₁ := by abel
      rw [hw'eq]
      exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
        (Submodule.subset_span (Set.mem_insert _ _))
  obtain ⟨f, hfw, hfle⟩ := Submodule.exists_le_ker_of_notMem hnot
  have hcne : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hf1 : f ⟨w, hw⟩ = 1 := hcne _ hfw
  have hf0 : f ⟨v₁, h.mem_W⟩ = 0 := hfle (Submodule.subset_span (Set.mem_insert _ _))
  have hf0' : f ⟨w', hw'⟩ = 0 := hfle (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  obtain ⟨x, hx, hxf⟩ := h.transvection_full f hf0
  have hxw : x w = w + v₁ := by
    have := hxf ⟨w, hw⟩
    rw [hf1, one_smul] at this
    exact this
  have hxw' : x w' = w' := by
    have := hxf ⟨w', hw'⟩
    rw [hf0', zero_smul, add_zero] at this
    exact this
  have hx' : x ∈ fixIn X w' := ⟨hx, hxw'⟩
  rw [← heq] at hx'
  have : w + v₁ = w := hxw.symm.trans hx'.2
  apply h.point
  simpa using this

end G101Hyp

namespace G11

namespace G108Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem g10_11 (h10 : G1010Concl Γ v₁ X L) : G1011Concl Γ v₁ X L := by
  intro I hI
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  constructor
  · intro hX
    have hHX : Invariant (normalClosure Γ L ⊔ X) I := hI.1.sup_subgroup hX
    exact (h10 I hirr.ne_bot hHX).1
  · intro hv x hx u hu
    have hxΓ : x ∈ Γ := hyp.X_le hx
    rcases hirr.conj_eq_or_inf_eq_bot (normalClosure_normal Γ L) hxΓ with h | h
    · rw [← h]
      exact apply_mem_conjSub hu
    · exfalso
      have hmem : v₁ ∈ conjSub x I ⊓ I := by
        refine ⟨?_, hv⟩
        have := apply_mem_conjSub (g := x) hv
        rwa [hyp.X_fixes x hx] at this
      rw [h] at hmem
      exact hyp.point ((Submodule.mem_bot _).1 hmem)

theorem fixIn_le_stabilizerOf {I : Submodule (ZMod 2) V} (hI : IsIrr (normalClosure Γ L) I)
    {w : V} (hwI : w ∈ I) (hw0 : w ≠ 0) : fixIn X w ≤ stabilizerOf X I := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rcases hI.conj_eq_or_inf_eq_bot (normalClosure_normal Γ L) (hyp.X_le hx.1) with h | h
  · exact h
  · exfalso
    have hmem : w ∈ conjSub x I ⊓ I := by
      refine ⟨?_, hwI⟩
      have hxw : x w = w := hx.2
      have := apply_mem_conjSub (g := x) hwI
      rwa [hxw] at this
    rw [h] at hmem
    exact hw0 ((Submodule.mem_bot _).1 hmem)

theorem g10_12 (h11 : G1011Concl Γ v₁ X L) : G1012Concl Γ v₁ W X L := by
  intro I hI hv
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hXnot : ¬ Invariant X I := fun hXI => hv ((h11 I hI).1 hXI)
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hnot : ∀ w ∈ I, w ≠ 0 → w ∉ Submodule.span (ZMod 2) {v₁} := by
    intro w hwI hw0 hws
    obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.1 hws
    rcases hc c with rfl | rfl
    · rw [zero_smul] at hc'
      exact hw0 hc'.symm
    · rw [one_smul] at hc'
      exact hv (hc' ▸ hwI)
  have hNneX : stabilizerOf X I ≠ X := by
    intro heq
    apply hXnot
    intro x hx u hu
    have hxs : x ∈ stabilizerOf X I := by
      rw [heq]
      exact hx
    rw [← hxs.2]
    exact apply_mem_conjSub hu
  have hNle : stabilizerOf X I ≤ X := fun _ hx => hx.1
  refine ⟨?_, ?_⟩
  ·
    by_contra hlt
    have hlt' : 1 < Module.finrank (ZMod 2) ↥(I ⊓ W) := not_le.1 hlt
    have : Nontrivial ↥(I ⊓ W) :=
      Module.nontrivial_of_finrank_pos (R := ZMod 2) (Nat.lt_trans Nat.zero_lt_one hlt')
    obtain ⟨⟨w, hw⟩, hw0⟩ := exists_ne (0 : ↥(I ⊓ W))
    have hw0' : w ≠ 0 := fun h0 => hw0 (Subtype.ext h0)
    have hex : ∃ w' ∈ I ⊓ W, w' ∉ Submodule.span (ZMod 2) {w} := by
      by_contra hcon
      push Not at hcon
      have : Module.finrank (ZMod 2) ↥(I ⊓ W) ≤ 1 := by
        rw [finrank_le_one_iff]
        refine ⟨⟨w, hw⟩, fun y => ?_⟩
        have := hcon y y.2
        obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.1 (hcon y y.2)
        exact ⟨c, Subtype.ext hc'⟩
      omega
    obtain ⟨w', hw', hw'n⟩ := hex
    have hwv := hnot w hw.1 hw0'
    have hw'v : w' ∉ Submodule.span (ZMod 2) {v₁, w} := by
      intro hmem
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hmem
      rcases hc a with rfl | rfl
      · rw [zero_smul, zero_add] at hab
        exact hw'n (hab ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      · rw [one_smul] at hab
        have hv' : v₁ = w' - b • w := by rw [← hab]; abel
        exact hv (hv' ▸ I.sub_mem hw'.1 (I.smul_mem _ hw.1))
    have hne := hyp.toG101Hyp.fixIn_ne hw.2 hw'.2 hwv hw'v
    have h1 := hyp.toG101Hyp.relIndex_fixIn hw.2 hwv
    have h2 := hyp.toG101Hyp.relIndex_fixIn hw'.2
      (fun hs => hw'v (Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) hs))
    have hle1 : fixIn X w ≤ X := fun x hx => hx.1
    have hle2 : fixIn X w' ≤ X := fun x hx => hx.1
    have hsup := sup_eq_of_relIndex_two hle1 hle2 h1 h2 hne
    apply hNneX
    refine le_antisymm hNle ?_
    calc X = fixIn X w ⊔ fixIn X w' := hsup.symm
      _ ≤ stabilizerOf X I :=
        sup_le (hyp.fixIn_le_stabilizerOf hirr hw.1 hw0')
          (hyp.fixIn_le_stabilizerOf hirr hw'.1 (fun h0 => hw'n (h0 ▸ Submodule.zero_mem _)))
  ·
    intro hne
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hwv := hnot w hw.1 hw0
    have h1 := hyp.toG101Hyp.relIndex_fixIn hw.2 hwv
    have hle := hyp.fixIn_le_stabilizerOf hirr hw.1 hw0
    have hmul := Subgroup.relIndex_mul_relIndex (fixIn X w) (stabilizerOf X I) X hle hNle
    rw [h1] at hmul
    have hdvd : (stabilizerOf X I).relIndex X ∣ 2 := Dvd.intro_left _ hmul
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h3 | h3
    · exact absurd (le_antisymm hNle (Subgroup.relIndex_eq_one.1 h3)) hNneX
    · exact h3

theorem g10_13 (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L) :
    G1013Concl B Γ v₁ L := by
  intro I hI hv
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  rcases hyp.isotropic_or_nondegOn hirr with hiso | hnd
  · exact Or.inl hiso
  · right
    have hcompl := hyp.isCompl_orthogonal hnd
    have hXI : Invariant X I := (h11 I hI).2 hv
    have hXperp : Invariant X (B.orthogonal I) :=
      hXI.orthogonal (fun k hk => hyp.isometry k (hyp.X_le hk))
    have hHperp : Invariant (normalClosure Γ L) (B.orthogonal I) :=
      hirr.1.orthogonal hyp.H_isometry
    have hHX : Invariant (normalClosure Γ L ⊔ X) (B.orthogonal I) := hHperp.sup_subgroup hXperp
    have hbot : B.orthogonal I = ⊥ := by
      by_contra hne
      have hv' : v₁ ∈ B.orthogonal I := (h10 _ hne hHX).1
      have hmem : v₁ ∈ I ⊓ B.orthogonal I := ⟨hv, hv'⟩
      rw [hcompl.disjoint.eq_bot] at hmem
      exact hyp.point ((Submodule.mem_bot _).1 hmem)
    have htop : I = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [hbot, sup_bot_eq] at this
    exact ⟨htop, htop ▸ hirr⟩

end G108Hyp

theorem g10_11 (h10 : G1010Stmt) : G1011Stmt :=
  fun V _ _ _ B Γ v₁ W X X₀ L hyp => hyp.g10_11 (h10 V B Γ v₁ W X X₀ L hyp)

theorem g10_12 (h11 : G1011Stmt) : G1012Stmt :=
  fun V _ _ _ B Γ v₁ W X X₀ L hyp => hyp.g10_12 (h11 V B Γ v₁ W X X₀ L hyp)

theorem g10_13 (h10 : G1010Stmt) (h11 : G1011Stmt) : G1013Stmt :=
  fun V _ _ _ B Γ v₁ W X X₀ L hyp =>
    hyp.g10_13 (h10 V B Γ v₁ W X X₀ L hyp) (h11 V B Γ v₁ W X X₀ L hyp)

end G11

end CFSG.Quasithin
