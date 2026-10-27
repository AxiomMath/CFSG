module

public import CFSG.Quasithin.Background.G10FifteenCX

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem commutator_fixes {H : Subgroup (GLV V)} {M : Submodule (ZMod 2) V} (hM : Invariant H M)
    {y h : GLV V} (hh : h ∈ H) (hy : ∀ m ∈ M, y m = m) {u : V} (hu : u ∈ M) :
    (y * h * y⁻¹ * h⁻¹) u = u := by
  have h1 : h⁻¹ u ∈ M := hM h⁻¹ (H.inv_mem hh) u hu
  have h2 : y⁻¹ (h⁻¹ u) = h⁻¹ u := by
    have := hy _ h1
    calc y⁻¹ (h⁻¹ u) = y⁻¹ (y (h⁻¹ u)) := by rw [this]
      _ = h⁻¹ u := LinearEquiv.symm_apply_apply y _
  have h3 : h (h⁻¹ u) = u := LinearEquiv.apply_symm_apply h u
  show y (h (y⁻¹ (h⁻¹ u))) = u
  rw [h2, h3]
  exact hy u hu

theorem card_le_of_transvections [Finite V] {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V}
    {c : V} (hT : ∀ k ∈ K, ∃ f : ↥U →ₗ[ZMod 2] ZMod 2, ∀ u : ↥U, k (u : V) = (u : V) + f u • c)
    (hfaith : ∀ k ∈ K, (∀ u ∈ U, k u = u) → k = 1) :
    Nat.card K ≤ 2 ^ Module.finrank (ZMod 2) U := by
  classical
  have := finite_dual U
  let F : K → (↥U →ₗ[ZMod 2] ZMod 2) := fun k => Classical.choose (hT k k.2)
  have hF : ∀ (k : K) (u : ↥U), (k : GLV V) (u : V) = (u : V) + F k u • c := fun k u =>
    Classical.choose_spec (hT k k.2) u
  have hinj : Function.Injective F := by
    intro k k' hkk'
    have h1 : ∀ u : ↥U, (k : GLV V) (u : V) = (k' : GLV V) (u : V) := by
      intro u
      rw [hF k u, hF k' u, hkk']
    have h2 : (k' : GLV V)⁻¹ * (k : GLV V) = 1 := by
      refine hfaith _ (K.mul_mem (K.inv_mem k'.2) k.2) fun u hu => ?_
      show (k' : GLV V)⁻¹ ((k : GLV V) u) = u
      have := h1 ⟨u, hu⟩
      simp only at this
      rw [this]
      exact LinearEquiv.symm_apply_apply (k' : GLV V) u
    apply Subtype.ext
    exact (inv_mul_eq_one.1 h2).symm
  exact (Nat.card_le_card_of_injective F hinj).trans (card_dual_le U)

theorem two_mul_finrank_le_of_isotropic [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    (hnd : B.Nondegenerate) {S : Submodule (ZMod 2) V} (hS : Isotropic B S) :
    2 * Module.finrank (ZMod 2) S ≤ Module.finrank (ZMod 2) V := by
  have hle : S ≤ B.orthogonal S := fun w hw => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact fun n hn => hS n hn w hw
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hnd S
  have h3 : Module.finrank (ZMod 2) S ≤ Module.finrank (ZMod 2) V := Submodule.finrank_le S
  omega

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem faithfulOn_stabilizerOf (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) : FaithfulOn (stabilizerOf X I) I := by
  rw [faithfulOn_iff]
  intro y hy hyI
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hirr' : IsIrr (normalClosure Γ L) (conjSub x I) :=
    hirr.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)
  have hyI' : ∀ w ∈ conjSub x I, y w = w := by
    intro w hw
    have hu : x.symm w ∈ I := mem_conjSub.1 hw
    have : w = x (x.symm w) := (LinearEquiv.apply_symm_apply x w).symm
    rw [this, hyp.X_comm_apply hy.1 hx, hyI _ hu]
  refine hyp.centralizer_X_eq_one h10 h11 h12 hI hfix hx hne hy.1 fun h hh => ?_
  have hyΓ : y ∈ Γ := hyp.X_le hy.1
  have hc : y * h * y⁻¹ * h⁻¹ = 1 := by
    set c := y * h * y⁻¹ * h⁻¹ with hcdef
    have hcH : c ∈ normalClosure Γ L := by
      have h1 : y * h * y⁻¹ ∈ normalClosure Γ L := normalClosure_normal Γ L y hyΓ h hh
      exact (normalClosure Γ L).mul_mem h1 ((normalClosure Γ L).inv_mem hh)
    have hcI : ∀ u ∈ I, c u = u := fun u hu => commutator_fixes hI.1 hh hyI hu
    have hcI' : ∀ u ∈ conjSub x I, c u = u := fun u hu =>
      commutator_fixes (hI.1.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)) hh hyI' hu
    have hcΓ : (⟨c, hyp.H_le hcH⟩ : Γ) = 1 := by
      apply Subtype.ext
      refine eq_one_of_fixes_sSup (S := {J | IsIrr (normalClosure Γ L) J}) ?_ ?_
      · exact hyp.sSup_isIrr
      · intro J hJ u hu
        rcases hyp.hiso_or_hiso_of_isIrr h10 hI hfix hx hne hJ with hJI | hJI
        · have hce := centralizerOn_eq_of_hiso hJ.1 hirr.1 hJI
          have hmem : c ∈ centralizerOn (normalClosure Γ L) I := ⟨hcH, hcI⟩
          rw [← hce] at hmem
          exact hmem.2 u hu
        · have hce := centralizerOn_eq_of_hiso hJ.1 hirr'.1 hJI
          have hmem : c ∈ centralizerOn (normalClosure Γ L) (conjSub x I) := ⟨hcH, hcI'⟩
          rw [← hce] at hmem
          exact hmem.2 u hu
    exact congrArg Subtype.val hcΓ
  have h1 : y * h * y⁻¹ = h := mul_inv_eq_one.1 hc
  calc y * h = (y * h * y⁻¹) * y := by group
    _ = h * y := by rw [h1]


theorem nondegOn_sup_conj (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) : NondegOn B (I ⊔ conjSub x I) := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hTI := hyp.conj_inf_eq_bot hI hx hne
  have hrefl := hyp.toG101Hyp.isRefl
  have hHXΓ : normalClosure Γ L ⊔ X ≤ Γ := sup_le hyp.H_le hyp.X_le
  have hSinv := hyp.invariant_sup_conj hI hfix hx hne
  have hperp : Invariant (normalClosure Γ L ⊔ X) (B.orthogonal (I ⊔ conjSub x I)) :=
    hSinv.orthogonal (fun k hk => hyp.isometry k (hHXΓ hk))
  have hR : Invariant (normalClosure Γ L ⊔ X) ((I ⊔ conjSub x I) ⊓ B.orthogonal (I ⊔ conjSub x I)) :=
    hSinv.inf hperp
  by_cases hR0 : (I ⊔ conjSub x I) ⊓ B.orthogonal (I ⊔ conjSub x I) = ⊥
  · intro u hu hall
    have : u ∈ (I ⊔ conjSub x I) ⊓ B.orthogonal (I ⊔ conjSub x I) := by
      refine Submodule.mem_inf.2 ⟨hu, ?_⟩
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      exact hrefl _ _ (hall w hw)
    rw [hR0, Submodule.mem_bot] at this
    exact this
  · exfalso
    have hHinv : Invariant (normalClosure Γ L) ((I ⊔ conjSub x I) ⊓ B.orthogonal (I ⊔ conjSub x I)) :=
      hR.mono le_sup_left
    have hXinv : Invariant X ((I ⊔ conjSub x I) ⊓ B.orthogonal (I ⊔ conjSub x I)) :=
      hR.mono le_sup_right
    have hRS : (I ⊔ conjSub x I) ⊓ B.orthogonal (I ⊔ conjSub x I) = I ⊔ conjSub x I := by
      rcases hyp.le_of_le_sup_conj hI hfix hx hne hHinv inf_le_left hR0 with h | h
      · have h' : conjSub x I ≤ (I ⊔ conjSub x I) ⊓ B.orthogonal (I ⊔ conjSub x I) :=
          (conjSub_mono x h).trans (hXinv.conjSub_le hx)
        exact le_antisymm inf_le_left (sup_le h h')
      · have h1 := conjSub_mono x h
        rw [conjSub_conjSub_of_sq (hyp.X_sq x hx)] at h1
        have h' : I ≤ (I ⊔ conjSub x I) ⊓ B.orthogonal (I ⊔ conjSub x I) :=
          h1.trans (hXinv.conjSub_le hx)
        exact le_antisymm inf_le_left (sup_le h' h)
    have hiso : Isotropic B (I ⊔ conjSub x I) := fun u hu u' hu' => by
      have hmem : u ∈ (I ⊔ conjSub x I) ⊓ B.orthogonal (I ⊔ conjSub x I) := by
        rw [hRS]
        exact hu
      exact hrefl _ _ ((LinearMap.BilinForm.mem_orthogonal_iff.1 hmem.2) u' hu')
    obtain ⟨i, hi, hi0, hv, hY⟩ := hyp.exists_i h10 hI hfix hx hne
    have hvS : v₁ ∈ I ⊔ conjSub x I := by
      rw [hv]
      exact Submodule.add_mem_sup hi.1 (apply_mem_conjSub hi.1)
    have hU : I ⊓ perp B v₁ = I := inf_eq_left.2 fun u hu =>
      mem_perp_iff_decomp.2 (hiso v₁ hvS u (Submodule.mem_sup_left hu))
    have hFT := hyp.fullTransvections hI hfix hx hne hi hv
    have hfaith := hyp.faithfulOn_stabilizerOf h10 h11 h12 hI hfix hx hne
    rw [faithfulOn_iff] at hfaith
    have hbound : Nat.card (stabilizerOf X I) ≤ 2 ^ Module.finrank (ZMod 2) ↥(I ⊓ perp B v₁) := by
      refine card_le_of_transvections (c := i) (fun y hy => ?_) (fun k hk hkU => ?_)
      · obtain ⟨f, -, hf⟩ := hFT.1 y hy
        exact ⟨f, hf⟩
      · exact hfaith k hk fun u hu => hkU u (by rw [hU]; exact hu)
    rw [hU] at hbound
    have hYX : stabilizerOf X I ≤ X := fun y hy => hy.1
    have hmulcard := Subgroup.relIndex_mul_card (stabilizerOf X I) X
    rw [inf_eq_left.2 hYX, relIndex_stabilizerOf_eq_two hyp hI hfix hx hne] at hmulcard
    have hXcard : Nat.card X ≤ 2 ^ (Module.finrank (ZMod 2) I + 1) := by
      rw [← hmulcard, pow_succ]
      omega
    have hrelle : X₀.relIndex X ≤ 2 ^ (Module.finrank (ZMod 2) I + 1) :=
      (Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card X₀ X)).trans hXcard
    have hlog : Nat.log 2 (X₀.relIndex X) ≤ Module.finrank (ZMod 2) I + 1 := by
      calc Nat.log 2 (X₀.relIndex X) ≤ Nat.log 2 (2 ^ (Module.finrank (ZMod 2) I + 1)) :=
          Nat.log_mono_right hrelle
        _ = Module.finrank (ZMod 2) I + 1 := Nat.log_pow Nat.one_lt_two _
    have h2d := hyp.toG101Hyp.dim_le_two_mul
    have h4 := two_mul_finrank_le_of_isotropic hyp.toG101Hyp.nondegenerate' hiso
    have h5 := Submodule.finrank_sup_add_finrank_inf_eq I (conjSub x I)
    rw [inf_comm, hTI, finrank_bot, add_zero, finrank_conjSub] at h5
    have h3 := hyp.two_lt_finrank hirr
    omega

theorem isCompl_sup_conj (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) : IsCompl I (conjSub x I) := by
  have hTI := hyp.conj_inf_eq_bot hI hx hne
  have hnd := hyp.nondegOn_sup_conj h10 h11 h12 hI hfix hx hne
  have hHXΓ : normalClosure Γ L ⊔ X ≤ Γ := sup_le hyp.H_le hyp.X_le
  have hSinv := hyp.invariant_sup_conj hI hfix hx hne
  have hperp : Invariant (normalClosure Γ L ⊔ X) (B.orthogonal (I ⊔ conjSub x I)) :=
    hSinv.orthogonal (fun k hk => hyp.isometry k (hHXΓ hk))
  have hcompl := hyp.isCompl_orthogonal hnd
  obtain ⟨i, hiI, hi0, hv, -⟩ := hyp.exists_decomp h10 hI hfix hx hne
  have hvS : v₁ ∈ I ⊔ conjSub x I := by
    rw [hv]
    exact Submodule.add_mem_sup hiI (apply_mem_conjSub hiI)
  have hbot : B.orthogonal (I ⊔ conjSub x I) = ⊥ := by
    by_contra hne0
    have hvo : v₁ ∈ B.orthogonal (I ⊔ conjSub x I) := (h10 _ hne0 hperp).1
    have : v₁ ∈ (I ⊔ conjSub x I) ⊓ B.orthogonal (I ⊔ conjSub x I) := ⟨hvS, hvo⟩
    rw [hcompl.disjoint.eq_bot, Submodule.mem_bot] at this
    exact hyp.point this
  have htop : I ⊔ conjSub x I = ⊤ := by
    have := hcompl.sup_eq_top
    rwa [hbot, sup_bot_eq] at this
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff, inf_comm]
    exact hTI
  · rw [codisjoint_iff]
    exact htop

end G108Hyp

end G11

end CFSG.Quasithin
