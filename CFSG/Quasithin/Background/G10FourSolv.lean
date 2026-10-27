module

public import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private noncomputable def subspaceActHom (Δ : Subgroup (GLV V)) (𝒮 : Set (Submodule (ZMod 2) V))
    (h : ∀ δ ∈ Δ, ∀ S ∈ 𝒮, conjSub δ S ∈ 𝒮) : Δ →* Equiv.Perm 𝒮 where
  toFun δ :=
    { toFun := fun S => ⟨conjSub (δ : GLV V) S, h δ δ.2 S S.2⟩
      invFun := fun S => ⟨conjSub (δ : GLV V)⁻¹ S, h _ (Δ.inv_mem δ.2) S S.2⟩
      left_inv := fun S => Subtype.ext (conjSub_inv_conjSub _ _)
      right_inv := fun S => Subtype.ext (conjSub_conjSub_inv _ _) }
  map_one' := by
    ext S
    simp
  map_mul' a b := by
    ext S
    simp [conjSub_mul]

private theorem finite_submodule_zmod_two [Finite V] : Finite (Submodule (ZMod 2) V) :=
  Finite.of_injective (fun S : Submodule (ZMod 2) V => (S : Set V)) SetLike.coe_injective

private theorem isSolvable_of_subspaceAct [Finite V] (Δ : Subgroup (GLV V))
    (𝒮 : Set (Submodule (ZMod 2) V)) (h : ∀ δ ∈ Δ, ∀ S ∈ 𝒮, conjSub δ S ∈ 𝒮)
    (hc : 𝒮.ncard ≤ 4)
    (hK : ∀ K : Subgroup (GLV V), K ≤ Δ → (∀ k ∈ K, ∀ S ∈ 𝒮, conjSub k S = S) →
      Group.IsSolvable K) : Group.IsSolvable Δ := by
  have := finite_submodule_zmod_two (V := V)
  have : Finite 𝒮 := inferInstance
  have hperm : Group.IsSolvable (Equiv.Perm 𝒮) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_coe_set_eq]; exact hc)
  let ψ := subspaceActHom Δ 𝒮 h
  have h1 : Group.IsSolvable (ψ.ker.map Δ.subtype) := by
    refine hK _ (Subgroup.map_subtype_le _) ?_
    rintro k ⟨δ, hδ, rfl⟩ S hS
    have := congrArg (fun σ : Equiv.Perm 𝒮 => ((σ ⟨S, hS⟩ : 𝒮) : Submodule (ZMod 2) V))
      (MonoidHom.mem_ker.1 hδ)
    exact this
  have h2 : Group.IsSolvable ψ.ker :=
    Group.isSolvable_of_isSolvable_injective
      (f := (ψ.ker.equivMapOfInjective Δ.subtype Subtype.val_injective).toMonoidHom)
      (ψ.ker.equivMapOfInjective Δ.subtype Subtype.val_injective).injective
  exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ (by simp)

private theorem isSolvable_of_centralizerOn [Finite V] (Δ : Subgroup (GLV V))
    (I : Submodule (ZMod 2) V) (hI : Invariant Δ I) (hd : Module.finrank (ZMod 2) I ≤ 2)
    (hC : Group.IsSolvable (centralizerOn Δ I)) : Group.IsSolvable Δ := by
  have hle : centralizerOn Δ I ≤ Δ := fun k hk => hk.1
  have h2 : Group.IsSolvable (I ≃ₗ[ZMod 2] I) := isSolvable_linearEquiv_of_finrank_le_two I hd
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) (restrictHom Δ I hI) ?_
  intro k hk
  have hk1 : ∀ i ∈ I, (k : GLV V) i = i := restrictHom_eq_one_iff.1 (MonoidHom.mem_ker.1 hk)
  exact ⟨⟨k, ⟨k.2, hk1⟩⟩, rfl⟩

private theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

private theorem alt_symm (B : LinearMap.BilinForm (ZMod 2) V) (halt : ∀ v, B v v = 0) (x y : V) :
    B x y = B y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  have h2 := zmod_two_add_self (B y x)
  exact add_left_cancel (h.trans h2.symm)

private theorem nondeg_of_alt (B : LinearMap.BilinForm (ZMod 2) V) (halt : ∀ v, B v v = 0)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) : B.Nondegenerate := by
  have hrefl : B.IsRefl := LinearMap.BilinForm.IsAlt.isRefl (B₁ := B) halt
  exact ⟨hnd, fun y hy => hnd y (fun w => hrefl w y (hy w))⟩

private theorem finrank_orthogonal_four [Finite V] (B : LinearMap.BilinForm (ZMod 2) V)
    (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hd : Module.finrank (ZMod 2) V = 4) (Z : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) (B.orthogonal Z) = 4 - Module.finrank (ZMod 2) Z := by
  rw [LinearMap.BilinForm.finrank_orthogonal (nondeg_of_alt B halt hnd) Z, hd]

private theorem isSolvable_of_invariant_two [Finite V] (B : LinearMap.BilinForm (ZMod 2) V)
    (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hd : Module.finrank (ZMod 2) V = 4) (Δ : Subgroup (GLV V))
    (hΔ : ∀ γ ∈ Δ, ∀ v w, B (γ v) (γ w) = B v w) (Z : Submodule (ZMod 2) V)
    (hZ : Invariant Δ Z) (h2 : Module.finrank (ZMod 2) Z = 2) : Group.IsSolvable Δ := by
  have hnd' : B.Nondegenerate := nondeg_of_alt B halt hnd
  have hrefl : B.IsRefl := LinearMap.BilinForm.IsAlt.isRefl (B₁ := B) halt
  have hZ' : Invariant Δ (B.orthogonal Z) := Invariant.orthogonal hΔ hZ
  have h2' : Module.finrank (ZMod 2) (B.orthogonal Z) = 2 := by
    rw [finrank_orthogonal_four B halt hnd hd, h2]
  have hdd : B.orthogonal (B.orthogonal Z) = Z :=
    LinearMap.BilinForm.orthogonal_orthogonal hnd' hrefl Z
  have hle1 : centralizerOn Δ Z ≤ Δ := fun k hk => hk.1
  refine isSolvable_of_centralizerOn Δ Z hZ h2.le ?_
  refine isSolvable_of_centralizerOn (centralizerOn Δ Z) (B.orthogonal Z)
    (hZ'.mono hle1) h2'.le ?_
  have key : ∀ k : GLV V, k ∈ centralizerOn (centralizerOn Δ Z) (B.orthogonal Z) →
      (∀ v, k v - v ∈ Z) ∧ (∀ z ∈ Z, k z = z) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := hk
    obtain ⟨hkΔ, hkZ⟩ := hk1
    refine ⟨fun v => ?_, hkZ⟩
    rw [← hdd, LinearMap.BilinForm.mem_orthogonal_iff]
    intro z' hz'
    have e1 : B z' (k v) = B z' v := by
      have := hΔ k hkΔ z' v
      rwa [hk2 z' hz'] at this
    rw [map_sub, e1]
    exact sub_self _
  refine Group.isSolvable_of_comm ?_
  intro a b
  apply Subtype.ext
  ext v
  show (a : GLV V) ((b : GLV V) v) = (b : GLV V) ((a : GLV V) v)
  have ha := key a a.2
  have hb := key b b.2
  have hav : (a : GLV V) ((b : GLV V) v - v) = (b : GLV V) v - v := ha.2 _ (hb.1 v)
  have hbv : (b : GLV V) ((a : GLV V) v - v) = (a : GLV V) v - v := hb.2 _ (ha.1 v)
  rw [map_sub] at hav hbv
  have e1 : (a : GLV V) ((b : GLV V) v) = (b : GLV V) v - v + (a : GLV V) v := by
    rw [← hav]
    abel
  have e2 : (b : GLV V) ((a : GLV V) v) = (a : GLV V) v - v + (b : GLV V) v := by
    rw [← hbv]
    abel
  rw [e1, e2]
  abel

private theorem finrank_span_pair_eq_two [Finite V] {z w : V} (hz : z ≠ 0)
    (hw : w ∉ Submodule.span (ZMod 2) {z}) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {z, w}) = 2 := by
  rw [Submodule.span_insert, Submodule.finrank_sup_span_singleton hw, finrank_span_singleton hz]

private theorem finrank_span_singleton_le_one [Finite V] (z : V) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {z}) ≤ 1 := by
  by_cases hz : z = 0
  · rw [hz, Submodule.span_zero_singleton]
    simp
  · rw [finrank_span_singleton hz]

private theorem exists_not_mem_span_singleton [Finite V] (S : Submodule (ZMod 2) V) (z : V)
    (hS : 2 ≤ Module.finrank (ZMod 2) S) : ∃ w ∈ S, w ∉ Submodule.span (ZMod 2) {z} := by
  by_contra hcon
  push Not at hcon
  have hle : S ≤ Submodule.span (ZMod 2) {z} := fun w hw => hcon w hw
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_span_singleton_le_one (V := V) z
  omega

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem exists_generator_of_finrank_one [Finite V] (Z : Submodule (ZMod 2) V)
    (h1 : Module.finrank (ZMod 2) Z = 1) : ∃ z ∈ Z, z ≠ 0 ∧ ∀ w ∈ Z, w = 0 ∨ w = z := by
  obtain ⟨⟨z, hzZ⟩, hv0, hv⟩ := finrank_eq_one_iff'.1 h1
  refine ⟨z, hzZ, fun h => hv0 (Subtype.ext h), ?_⟩
  intro w hw
  obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
  have hc' : c • z = w := congrArg Subtype.val hc
  rcases zmod_two_cases c with rfl | rfl
  · left
    rw [← hc', zero_smul]
  · right
    rw [← hc', one_smul]

private theorem isSolvable_of_invariant_one [Finite V] (B : LinearMap.BilinForm (ZMod 2) V)
    (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hd : Module.finrank (ZMod 2) V = 4) (Δ : Subgroup (GLV V))
    (hΔ : ∀ γ ∈ Δ, ∀ v w, B (γ v) (γ w) = B v w) (Z : Submodule (ZMod 2) V)
    (hZ : Invariant Δ Z) (h1 : Module.finrank (ZMod 2) Z = 1) : Group.IsSolvable Δ := by
  classical
  obtain ⟨z, hzZ, hz0, hZz⟩ := exists_generator_of_finrank_one Z h1
  have hfix : ∀ δ ∈ Δ, δ z = z := by
    intro δ hδ
    rcases hZz _ (hZ δ hδ z hzZ) with h | h
    · exact absurd (δ.injective (h.trans (map_zero δ).symm)) hz0
    · exact h
  set W : Submodule (ZMod 2) V := B.orthogonal Z with hWdef
  have hW : Invariant Δ W := Invariant.orthogonal hΔ hZ
  have hW3 : Module.finrank (ZMod 2) W = 3 := by
    rw [hWdef, finrank_orthogonal_four B halt hnd hd, h1]
  have hzW : z ∈ W := by
    rw [hWdef, LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rcases hZz n hn with rfl | rfl
    · simp
    · exact halt _
  let X : Set (Submodule (ZMod 2) V) := {S | z ∈ S ∧ S ≤ W ∧ Module.finrank (ZMod 2) S = 2}
  have hclosed : ∀ δ ∈ Δ, ∀ S ∈ X, conjSub δ S ∈ X := by
    rintro δ hδ S ⟨hzS, hSW, hS2⟩
    refine ⟨?_, ?_, ?_⟩
    · have := apply_mem_conjSub (g := δ) hzS
      rwa [hfix δ hδ] at this
    · exact (conjSub_mono δ hSW).trans (hW.conjSub_eq hδ).le
    · rw [finrank_conjSub]
      exact hS2
  have hcard : X.ncard ≤ 4 := by
    have hex : ∀ S : X, ∃ w ∈ (S : Submodule (ZMod 2) V), w ∉ Submodule.span (ZMod 2) {z} :=
      fun S => exists_not_mem_span_singleton S.1 z (by rw [S.2.2.2])
    choose r hrS hrz using hex
    have hWcard : Nat.card W = 8 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hW3]
      norm_num
    let f : X × ZMod 2 → W := fun p =>
      ⟨r p.1 + p.2 • z, W.add_mem (p.1.2.2.1 (hrS p.1)) (W.smul_mem _ hzW)⟩
    have hinj : Function.Injective f := by
      rintro ⟨S, c⟩ ⟨S', c'⟩ h
      have h' : r S + c • z = r S' + c' • z := congrArg Subtype.val h
      have hS'z : ∀ a : ZMod 2, a • z ∈ (S' : Submodule (ZMod 2) V) :=
        fun a => (S' : Submodule (ZMod 2) V).smul_mem a S'.2.1
      have hrS_S' : r S ∈ (S' : Submodule (ZMod 2) V) := by
        have : r S = r S' + c' • z - c • z := by
          rw [← h']
          abel
        rw [this]
        exact (S' : Submodule (ZMod 2) V).sub_mem
          ((S' : Submodule (ZMod 2) V).add_mem (hrS S') (hS'z c')) (hS'z c)
      have hspan : Submodule.span (ZMod 2) {z, r S} = (S : Submodule (ZMod 2) V) := by
        refine Submodule.eq_of_le_of_finrank_le ?_ ?_
        · refine Submodule.span_le.2 ?_
          intro x hx
          rcases hx with rfl | rfl
          · exact S.2.1
          · exact hrS S
        · rw [finrank_span_pair_eq_two hz0 (hrz S), S.2.2.2]
      have hSS' : (S : Submodule (ZMod 2) V) ≤ S' := by
        rw [← hspan]
        refine Submodule.span_le.2 ?_
        intro x hx
        rcases hx with rfl | rfl
        · exact S'.2.1
        · exact hrS_S'
      have hSeq : S = S' :=
        Subtype.ext (Submodule.eq_of_le_of_finrank_le hSS' (by rw [S.2.2.2, S'.2.2.2]))
      subst hSeq
      have hcc : c • z = c' • z := add_left_cancel h'
      have : c = c' := by
        rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases c' with rfl | rfl
        · rfl
        · exact absurd (by simpa using hcc.symm : z = 0) hz0
        · exact absurd (by simpa using hcc : z = 0) hz0
        · rfl
      rw [this]
    have := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_prod, Nat.card_zmod, hWcard, Nat.card_coe_set_eq] at this
    omega
  obtain ⟨w, hwW, hwz⟩ := exists_not_mem_span_singleton W z (by rw [hW3]; omega)
  have hS0 : Submodule.span (ZMod 2) {z, w} ∈ X := by
    refine ⟨Submodule.subset_span (by simp), ?_, finrank_span_pair_eq_two hz0 hwz⟩
    refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact hzW
    · exact hwW
  refine isSolvable_of_subspaceAct Δ X hclosed hcard ?_
  intro K hKΔ hKfix
  have hinv : Invariant K (Submodule.span (ZMod 2) {z, w}) := by
    intro k hk u hu
    have := apply_mem_conjSub (g := k) hu
    rwa [hKfix k hk _ hS0] at this
  exact isSolvable_of_invariant_two B halt hnd hd K (fun γ hγ => hΔ γ (hKΔ hγ)) _ hinv
    (finrank_span_pair_eq_two hz0 hwz)

theorem isSolvable_of_invariant_subspace_four [Finite V] (B : LinearMap.BilinForm (ZMod 2) V)
    (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hd : Module.finrank (ZMod 2) V = 4) (Δ : Subgroup (GLV V))
    (hΔ : ∀ γ ∈ Δ, ∀ v w, B (γ v) (γ w) = B v w) (Z : Submodule (ZMod 2) V)
    (hZ : Invariant Δ Z) (hbot : Z ≠ ⊥) (htop : Z ≠ ⊤) : Group.IsSolvable ↥Δ := by
  have h1 : 1 ≤ Module.finrank (ZMod 2) Z := Submodule.one_le_finrank_iff.2 hbot
  have h2 : Module.finrank (ZMod 2) Z < 4 := by
    rw [← hd]
    exact Submodule.finrank_lt htop
  have h3 : Module.finrank (ZMod 2) Z = 1 ∨ Module.finrank (ZMod 2) Z = 2 ∨
      Module.finrank (ZMod 2) Z = 3 := by omega
  rcases h3 with h | h | h
  · exact isSolvable_of_invariant_one B halt hnd hd Δ hΔ Z hZ h
  · exact isSolvable_of_invariant_two B halt hnd hd Δ hΔ Z hZ h
  · exact isSolvable_of_invariant_one B halt hnd hd Δ hΔ (B.orthogonal Z)
      (Invariant.orthogonal hΔ hZ) (by rw [finrank_orthogonal_four B halt hnd hd, h])

private theorem mem_plane_cases [Finite V] {U : Submodule (ZMod 2) V}
    (hU : Module.finrank (ZMod 2) U = 2) {u u' : V} (hu : u ∈ U) (hu' : u' ∈ U) (hu0 : u ≠ 0)
    (hu'0 : u' ≠ 0) (hne : u' ≠ u) :
    ∀ v ∈ U, v = 0 ∨ v = u ∨ v = u' ∨ v = u + u' := by
  have hnot : u' ∉ Submodule.span (ZMod 2) {u} := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨a, ha⟩
    rcases zmod_two_cases a with rfl | rfl
    · exact hu'0 (by rw [← ha, zero_smul])
    · exact hne (by rw [← ha, one_smul])
  have hspan : Submodule.span (ZMod 2) {u, u'} = U := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · refine Submodule.span_le.2 ?_
      intro x hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hu'
    · rw [finrank_span_pair_eq_two hu0 hnot, hU]
  intro v hv
  rw [← hspan, Submodule.mem_span_pair] at hv
  obtain ⟨c, d, rfl⟩ := hv
  rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases d with rfl | rfl <;> simp

private theorem order_three_of_fixedPointFree [Finite V] {U : Submodule (ZMod 2) V}
    (hU : Module.finrank (ZMod 2) U = 2) (g : GLV V) (hg : ∀ u ∈ U, g u ∈ U)
    (hfix : ∀ u ∈ U, g u = u → u = 0) : ∀ u ∈ U, g (g u) + g u + u = 0 := by
  intro u hu
  by_cases hu0 : u = 0
  · subst hu0
    simp
  have hgu : g u ∈ U := hg u hu
  have hgu0 : g u ≠ 0 := fun h => hu0 (g.injective (h.trans (map_zero g).symm))
  have hgun : g u ≠ u := fun h => hu0 (hfix u hu h)
  rcases mem_plane_cases hU hu hgu hu0 hgu0 hgun (g (g u)) (hg _ hgu) with h | h | h | h
  · exact absurd (g.injective (h.trans (map_zero g).symm)) hgu0
  · exfalso
    have hw : g (u + g u) = u + g u := by
      rw [map_add, h, add_comm]
    have h0 := hfix (u + g u) (U.add_mem hu hgu) hw
    apply hgun
    have := eq_neg_of_add_eq_zero_right h0
    rw [this, ZModModule.neg_eq_self]
  · exact absurd (g.injective h) hgun
  · rw [h]
    abel_nf
    simp only [two_zsmul, ZModModule.add_self]

private theorem add_add_self_left' (a b : V) : a + (a + b) = b := by
  rw [← add_assoc, ZModModule.add_self, zero_add]

private theorem add_add_self_right' (a b : V) : a + b + b = a := by
  rw [add_assoc, ZModModule.add_self, add_zero]

private theorem exists_fixedPointFree [Finite V] {H : Subgroup (GLV V)} {U : Submodule (ZMod 2) V}
    (hU : IsIrr H U) (h2 : Module.finrank (ZMod 2) U = 2) :
    ∃ g ∈ H, ∀ u ∈ U, g u = u → u = 0 := by
  by_contra hcon
  push Not at hcon
  have hmove : ∀ w ∈ U, w ≠ 0 → ∃ h ∈ H, h w ≠ w := by
    intro w hw hw0
    by_contra hall
    push Not at hall
    have hinv : Invariant H (Submodule.span (ZMod 2) {w}) := by
      intro h hh x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [map_smul, hall h hh]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    have hle : Submodule.span (ZMod 2) {w} ≤ U := Submodule.span_le.2 (by simpa using hw)
    rcases hU.eq_bot_or_eq hinv hle with h | h
    · exact hw0 (Submodule.span_singleton_eq_bot.1 h)
    · have := finrank_span_singleton (K := ZMod 2) hw0
      rw [h, h2] at this
      omega
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ U, u ≠ 0 := by
    by_contra hh
    push Not at hh
    have : U = ⊥ := (Submodule.eq_bot_iff U).2 hh
    rw [this, finrank_bot] at h2
    omega
  obtain ⟨h₁, hh₁, hh₁u⟩ := hmove u hu hu0
  have hu'U : h₁ u ∈ U := hU.1 h₁ hh₁ u hu
  have hu'0 : h₁ u ≠ 0 := fun h => hu0 (h₁.injective (h.trans (map_zero h₁).symm))
  have hcases := mem_plane_cases h2 hu hu'U hu0 hu'0 hh₁u
  set u' := h₁ u with hu'def
  have hwU : u + u' ∈ U := U.add_mem hu hu'U
  have hw0 : u + u' ≠ 0 := by
    intro h
    apply hh₁u
    have := eq_neg_of_add_eq_zero_right h
    rw [this, ZModModule.neg_eq_self]
  have hwu : u + u' ≠ u := fun h => hu'0 (add_left_cancel (h.trans (add_zero u).symm))
  have hwu' : u + u' ≠ u' := fun h => hu0 (add_right_cancel (h.trans (zero_add _).symm))
  obtain ⟨v, hvU, hv, hv0⟩ := hcon h₁ hh₁
  have hh₁w : h₁ (u + u') = u + u' := by
    rcases hcases v hvU with h | h | h | h
    · exact absurd h hv0
    · rw [h] at hv
      exact absurd hv hh₁u
    · rw [h] at hv
      exact absurd (h₁.injective hv) hh₁u
    · rw [← h]
      exact hv
  have hh₁u' : h₁ u' = u := by
    have h := hh₁w
    rw [map_add, ← hu'def] at h
    have : u' + h₁ u' = u' + u := by rw [h, add_comm]
    exact add_left_cancel this
  obtain ⟨h₂, hh₂, hh₂w⟩ := hmove (u + u') hwU hw0
  obtain ⟨v₂, hv₂U, hv₂, hv₂0⟩ := hcon h₂ hh₂
  have hh₂wU : h₂ (u + u') ∈ U := hU.1 h₂ hh₂ _ hwU
  have hh₂w0 : h₂ (u + u') ≠ 0 := fun h => hw0 (h₂.injective (h.trans (map_zero h₂).symm))
  obtain ⟨v₃, hv₃U, hv₃, hv₃0⟩ := hcon (h₁ * h₂) (H.mul_mem hh₁ hh₂)
  have hmul : ∀ x, (h₁ * h₂) x = h₁ (h₂ x) := fun x => rfl
  rw [hmul] at hv₃
  rcases hcases v₂ hv₂U with h | h | h | h
  · exact absurd h hv₂0
  · rw [h] at hv₂
    rcases hcases _ hh₂wU with h' | h' | h' | h'
    · exact absurd h' hh₂w0
    · exact hwu (h₂.injective (h'.trans hv₂.symm))
    · have hh₂u' : h₂ u' = u + u' := by
        have h3 := h'
        rw [map_add, hv₂] at h3
        calc h₂ u' = u + (u + h₂ u') := (add_add_self_left' u _).symm
          _ = u + u' := by rw [h3]
      rcases hcases v₃ hv₃U with h'' | h'' | h'' | h''
      · exact hv₃0 h''
      · rw [h'', hv₂, ← hu'def] at hv₃
        exact hh₁u hv₃
      · rw [h'', hh₂u', hh₁w] at hv₃
        exact hwu' hv₃
      · rw [h'', h', hh₁u'] at hv₃
        exact hwu hv₃.symm
    · exact hh₂w h'
  · rw [h] at hv₂
    rcases hcases _ hh₂wU with h' | h' | h' | h'
    · exact absurd h' hh₂w0
    · have hh₂u : h₂ u = u + u' := by
        have h3 := h'
        rw [map_add, hv₂] at h3
        calc h₂ u = h₂ u + u' + u' := (add_add_self_right' _ _).symm
          _ = u + u' := by rw [h3]
      rcases hcases v₃ hv₃U with h'' | h'' | h'' | h''
      · exact hv₃0 h''
      · rw [h'', hh₂u, hh₁w] at hv₃
        exact hwu hv₃
      · rw [h'', hv₂, hh₁u'] at hv₃
        exact hh₁u hv₃.symm
      · rw [h'', h', ← hu'def] at hv₃
        exact hwu' hv₃.symm
    · exact hwu' (h₂.injective (h'.trans hv₂.symm))
    · exact hh₂w h'
  · rw [h] at hv₂
    exact hh₂w hv₂

private theorem char2_eq_of_add_eq_zero {x y : V} (h : x + y = 0) : x = y := by
  have := eq_neg_of_add_eq_zero_left h
  rw [this, ZModModule.neg_eq_self]

private theorem eq_or_eq_sq_on [Finite V] {U : Submodule (ZMod 2) V}
    (hU : Module.finrank (ZMod 2) U = 2) (σ τ : GLV V) (hσ : ∀ u ∈ U, σ u ∈ U)
    (hτ : ∀ u ∈ U, τ u ∈ U) (hσ3 : ∀ u ∈ U, σ (σ u) + σ u + u = 0)
    (hτ3 : ∀ u ∈ U, τ (τ u) + τ u + u = 0) :
    (∀ u ∈ U, τ u = σ u) ∨ (∀ u ∈ U, τ u = σ (σ u)) := by
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ U, u ≠ 0 := by
    by_contra hh
    push Not at hh
    have : U = ⊥ := (Submodule.eq_bot_iff U).2 hh
    rw [this, finrank_bot] at hU
    omega
  have hσu : σ u ∈ U := hσ u hu
  have hσu0 : σ u ≠ 0 := fun h => hu0 (σ.injective (h.trans (map_zero σ).symm))
  have hfp : ∀ (ρ : GLV V), (∀ u ∈ U, ρ (ρ u) + ρ u + u = 0) → ∀ u ∈ U, ρ u = u → u = 0 := by
    intro ρ hρ x hx hρx
    have := hρ x hx
    rw [hρx, hρx] at this
    have h3 : x + x + x = x := by
      rw [ZModModule.add_self, zero_add]
    rw [h3] at this
    exact this
  have hσun : σ u ≠ u := fun h => hu0 (hfp σ hσ3 u hu h)
  have hσσ : σ (σ u) = σ u + u := by
    have := hσ3 u hu
    exact char2_eq_of_add_eq_zero (by rw [← this]; abel_nf)
  have hspan : Submodule.span (ZMod 2) {u, σ u} = U := by
    have hnot : σ u ∉ Submodule.span (ZMod 2) {u} := by
      rw [Submodule.mem_span_singleton]
      rintro ⟨a, ha⟩
      rcases zmod_two_cases a with rfl | rfl
      · exact hσu0 (by rw [← ha, zero_smul])
      · exact hσun (by rw [← ha, one_smul])
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · refine Submodule.span_le.2 ?_
      intro x hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hσu
    · rw [finrank_span_pair_eq_two hu0 hnot, hU]
  have hτu : τ u ∈ U := hτ u hu
  have hτu0 : τ u ≠ 0 := fun h => hu0 (τ.injective (h.trans (map_zero τ).symm))
  have hτun : τ u ≠ u := fun h => hu0 (hfp τ hτ3 u hu h)
  have hτττ : τ (τ u) = τ u + u := by
    have := hτ3 u hu
    exact char2_eq_of_add_eq_zero (by rw [← this]; abel_nf)
  rcases mem_plane_cases hU hu hσu hu0 hσu0 hσun (τ u) hτu with h | h | h | h
  · exact absurd h hτu0
  · exact absurd h hτun
  · left
    have hle : U ≤ LinearMap.eqLocus τ.toLinearMap σ.toLinearMap := by
      rw [← hspan]
      refine Submodule.span_le.2 ?_
      intro x hx
      rcases hx with rfl | rfl
      · exact h
      · show τ (σ u) = σ (σ u)
        have h1 : τ (σ u) = τ u + u := by
          rw [← h]
          exact hτττ
        rw [h1, hσσ, h]
    intro v hv
    exact hle hv
  · right
    have hσσσ : σ (σ (σ u)) = u := by
      rw [hσσ, map_add, hσσ]
      abel_nf
      simp only [two_zsmul, ZModModule.add_self, zero_add]
    have hτσ : τ (σ u) = u := by
      have e1 : τ (u + σ u) = σ u := by
        rw [← h, hτττ, h]
        abel_nf
        simp only [two_zsmul, ZModModule.add_self, zero_add]
      have e2 : σ u = (u + σ u) + u := by
        abel_nf
        simp only [two_zsmul, ZModModule.add_self, zero_add]
      calc τ (σ u) = τ ((u + σ u) + u) := by rw [← e2]
        _ = τ (u + σ u) + τ u := map_add τ _ _
        _ = u := by
          rw [e1, h]
          abel_nf
          simp only [two_zsmul, ZModModule.add_self, zero_add]
    have hle : U ≤ LinearMap.eqLocus τ.toLinearMap (σ.toLinearMap ∘ₗ σ.toLinearMap) := by
      rw [← hspan]
      refine Submodule.span_le.2 ?_
      intro x hx
      rcases hx with rfl | rfl
      · show τ x = σ (σ x)
        rw [h, hσσ]
        abel_nf
      · show τ (σ u) = σ (σ (σ u))
        rw [hτσ, hσσσ]
    intro v hv
    exact hle hv

private theorem sup_eq_top_of_finrank_two [Finite V] (hd : Module.finrank (ZMod 2) V = 4)
    {U U' : Submodule (ZMod 2) V} (h : Module.finrank (ZMod 2) U = 2)
    (h' : Module.finrank (ZMod 2) U' = 2) (hi : U ⊓ U' = ⊥) : U ⊔ U' = ⊤ := by
  have := Submodule.finrank_sup_add_finrank_inf_eq U U'
  rw [hi, finrank_bot] at this
  exact Submodule.eq_top_of_finrank_eq (by rw [hd]; omega)

private theorem pivot_eq_zero [Finite V] (hd : Module.finrank (ZMod 2) V = 4)
    {U₁ U₂ U₃ : Submodule (ZMod 2) V} (h1 : Module.finrank (ZMod 2) U₁ = 2)
    (h2 : Module.finrank (ZMod 2) U₂ = 2) (h3 : Module.finrank (ZMod 2) U₃ = 2)
    (h12 : U₁ ⊓ U₂ = ⊥) (h13 : U₁ ⊓ U₃ = ⊥) (h23 : U₂ ⊓ U₃ = ⊥)
    (T : V →ₗ[ZMod 2] V) (hT2 : ∀ u ∈ U₂, T u ∈ U₂) (hT3 : ∀ u ∈ U₃, T u ∈ U₃)
    (hT1 : ∀ u ∈ U₁, T u = 0) : T = 0 := by
  have s12 := sup_eq_top_of_finrank_two hd h1 h2 h12
  have s13 := sup_eq_top_of_finrank_two hd h1 h3 h13
  have s23 := sup_eq_top_of_finrank_two hd h2 h3 h23
  have hz2 : ∀ x ∈ U₂, T x = 0 := by
    intro x hx
    have hx' : x ∈ U₁ ⊔ U₃ := by
      rw [s13]
      exact Submodule.mem_top
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hx'
    have hTx : T (a + c) ∈ U₂ := hT2 _ hx
    rw [map_add, hT1 a ha, zero_add] at hTx ⊢
    have : T c ∈ U₂ ⊓ U₃ := ⟨hTx, hT3 c hc⟩
    rw [h23] at this
    exact this
  have hz3 : ∀ x ∈ U₃, T x = 0 := by
    intro x hx
    have hx' : x ∈ U₁ ⊔ U₂ := by
      rw [s12]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx'
    have hTx : T (a + b) ∈ U₃ := hT3 _ hx
    rw [map_add, hT1 a ha, zero_add] at hTx ⊢
    have : T b ∈ U₂ ⊓ U₃ := ⟨hT2 b hb, hTx⟩
    rw [h23] at this
    exact this
  ext v
  have hv : v ∈ U₂ ⊔ U₃ := by
    rw [s23]
    exact Submodule.mem_top
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
  simp [hz2 b hb, hz3 c hc]

private theorem exists_normalized_order_three [Finite V]
    (hd : Module.finrank (ZMod 2) V = 4) (Γ H : Subgroup (GLV V))
    (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) {U₁ U₂ U₃ : Submodule (ZMod 2) V}
    (hU₁ : IsIrr H U₁) (hI₂ : Invariant H U₂) (hI₃ : Invariant H U₃)
    (h1 : Module.finrank (ZMod 2) U₁ = 2) (h2 : Module.finrank (ZMod 2) U₂ = 2)
    (h3 : Module.finrank (ZMod 2) U₃ = 2) (h12 : U₁ ⊓ U₂ = ⊥) (h13 : U₁ ⊓ U₃ = ⊥)
    (h23 : U₂ ⊓ U₃ = ⊥) :
    ∃ g ∈ H, (∀ v, g (g v) + g v + v = 0) ∧
      ∀ γ ∈ Γ, γ * g * γ⁻¹ = g ∨ γ * g * γ⁻¹ = g * g := by
  obtain ⟨g, hgH, hgfix⟩ := exists_fixedPointFree hU₁ h1
  have hg1 : ∀ u ∈ U₁, g u ∈ U₁ := hU₁.1 g hgH
  have hp1 := order_three_of_fixedPointFree h1 g hg1 hgfix
  have hp : ∀ x, g (g x) + g x + x = 0 := by
    intro x
    have := pivot_eq_zero hd h1 h2 h3 h12 h13 h23
      ((g : V →ₗ[ZMod 2] V) ∘ₗ (g : V →ₗ[ZMod 2] V) + (g : V →ₗ[ZMod 2] V) + LinearMap.id)
      (fun u hu => by
        simpa using Submodule.add_mem _ (Submodule.add_mem _ (hI₂ g hgH _ (hI₂ g hgH u hu))
          (hI₂ g hgH u hu)) hu)
      (fun u hu => by
        simpa using Submodule.add_mem _ (Submodule.add_mem _ (hI₃ g hgH _ (hI₃ g hgH u hu))
          (hI₃ g hgH u hu)) hu)
      (fun u hu => by simpa using hp1 u hu)
    simpa using LinearMap.congr_fun this x
  refine ⟨g, hgH, hp, ?_⟩
  intro γ hγ
  have hg'H : γ * g * γ⁻¹ ∈ H := hHn γ hγ g hgH
  have hp' : ∀ x, (γ * g * γ⁻¹) ((γ * g * γ⁻¹) x) + (γ * g * γ⁻¹) x + x = 0 := by
    intro x
    have := congrArg γ (hp (γ⁻¹ x))
    simpa [map_add] using this
  have hg'1 : ∀ u ∈ U₁, (γ * g * γ⁻¹) u ∈ U₁ := hU₁.1 _ hg'H
  rcases eq_or_eq_sq_on h1 g (γ * g * γ⁻¹) hg1 hg'1 hp1 (fun u _ => hp' u) with h | h
  · left
    have := pivot_eq_zero hd h1 h2 h3 h12 h13 h23
      (((γ * g * γ⁻¹ : GLV V) : V →ₗ[ZMod 2] V) - (g : V →ₗ[ZMod 2] V))
      (fun u hu => by simpa using Submodule.sub_mem _ (hI₂ _ hg'H u hu) (hI₂ g hgH u hu))
      (fun u hu => by simpa using Submodule.sub_mem _ (hI₃ _ hg'H u hu) (hI₃ g hgH u hu))
      (fun u hu => by
        show (γ * g * γ⁻¹ : GLV V) u - g u = 0
        rw [h u hu, sub_self])
    ext x
    have hx := LinearMap.congr_fun this x
    simpa [sub_eq_zero] using hx
  · right
    have := pivot_eq_zero hd h1 h2 h3 h12 h13 h23
      (((γ * g * γ⁻¹ : GLV V) : V →ₗ[ZMod 2] V) - (g : V →ₗ[ZMod 2] V) ∘ₗ (g : V →ₗ[ZMod 2] V))
      (fun u hu => by
        simpa using Submodule.sub_mem _ (hI₂ _ hg'H u hu) (hI₂ g hgH _ (hI₂ g hgH u hu)))
      (fun u hu => by
        simpa using Submodule.sub_mem _ (hI₃ _ hg'H u hu) (hI₃ g hgH _ (hI₃ g hgH u hu)))
      (fun u hu => by
        show (γ * g * γ⁻¹ : GLV V) u - g (g u) = 0
        rw [h u hu, sub_self])
    ext x
    have hx := LinearMap.congr_fun this x
    simpa [sub_eq_zero] using hx

private theorem g_sq (g : GLV V) (hg3 : ∀ v, g (g v) + g v + v = 0) (v : V) :
    g (g v) = g v + v :=
  char2_eq_of_add_eq_zero ((add_assoc (g (g v)) (g v) v).symm.trans (hg3 v))

private theorem g_cube (g : GLV V) (hg3 : ∀ v, g (g v) + g v + v = 0) (v : V) :
    g (g (g v)) = v := by
  rw [g_sq g hg3 v, map_add, g_sq g hg3 v, add_comm (g v) v, add_assoc, ZModModule.add_self,
    add_zero]

private theorem g_fpf (g : GLV V) (hg3 : ∀ v, g (g v) + g v + v = 0) (v : V) (h : g v = v) :
    v = 0 := by
  have := hg3 v
  rw [h, h] at this
  have h3 : v + v + v = v := by
    rw [ZModModule.add_self, zero_add]
  rw [h3] at this
  exact this

private theorem B_g_left (B : LinearMap.BilinForm (ZMod 2) V) (g : GLV V)
    (hgB : ∀ x y, B (g x) (g y) = B x y) (hg3 : ∀ v, g (g v) + g v + v = 0) (x y : V) :
    B (g x) y = B x (g y) + B x y := by
  calc B (g x) y = B (g x) (g (g (g y))) := by rw [g_cube g hg3 y]
    _ = B x (g (g y)) := hgB x (g (g y))
    _ = B x (g y) + B x y := by rw [g_sq g hg3 y, map_add]

private theorem q_add (B : LinearMap.BilinForm (ZMod 2) V) (halt : ∀ v, B v v = 0) (g : GLV V)
    (hgB : ∀ x y, B (g x) (g y) = B x y) (hg3 : ∀ v, g (g v) + g v + v = 0) (x y : V) :
    B (x + y) (g (x + y)) = B x (g x) + B y (g y) + B x y := by
  have e1 : B y (g x) = B x (g y) + B x y := by
    rw [alt_symm B halt y (g x), B_g_left B g hgB hg3 x y]
  simp only [map_add, LinearMap.add_apply, e1]
  have key : ∀ a b c d : ZMod 2, c + (a + b) + (a + d) = c + d + b := by decide
  exact key (B x (g y)) (B x y) (B x (g x)) (B y (g y))

private theorem exists_q_eq_one [Finite V] (B : LinearMap.BilinForm (ZMod 2) V)
    (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hd : Module.finrank (ZMod 2) V = 4) (g : GLV V) (hgB : ∀ x y, B (g x) (g y) = B x y)
    (hg3 : ∀ v, g (g v) + g v + v = 0) : ∃ x, B x (g x) = 1 := by
  by_contra hcon
  push Not at hcon
  have hq0 : ∀ x, B x (g x) = 0 := fun x => by
    rcases zmod_two_cases (B x (g x)) with h | h
    · exact h
    · exact absurd h (hcon x)
  have hB0 : ∀ x y, B x y = 0 := fun x y => by
    have := q_add B halt g hgB hg3 x y
    rw [hq0, hq0, hq0, zero_add, zero_add] at this
    exact this.symm
  have hall : ∀ v : V, v = 0 := fun v => hnd v (fun w => hB0 v w)
  have : Subsingleton V := ⟨fun a b => (hall a).trans (hall b).symm⟩
  have := Module.finrank_zero_of_subsingleton (R := ZMod 2) (M := V)
  omega

private theorem line_finrank [Finite V] (g : GLV V) (hg3 : ∀ v, g (g v) + g v + v = 0) {y : V}
    (hy : y ≠ 0) : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {y, g y}) = 2 := by
  refine finrank_span_pair_eq_two hy ?_
  rw [Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  rcases zmod_two_cases a with rfl | rfl
  · rw [zero_smul] at ha
    exact hy (g.injective (ha.symm.trans (map_zero g).symm))
  · rw [one_smul] at ha
    exact hy (g_fpf g hg3 y ha.symm)

private theorem line_inv (g : GLV V) (hg3 : ∀ v, g (g v) + g v + v = 0) (y : V) :
    ∀ a ∈ Submodule.span (ZMod 2) {y, g y}, g a ∈ Submodule.span (ZMod 2) {y, g y} := by
  intro a ha
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 ha
  rw [map_add, map_smul, map_smul, g_sq g hg3 y]
  have h1 : g y ∈ Submodule.span (ZMod 2) {y, g y} := Submodule.subset_span (by simp)
  have h2 : y ∈ Submodule.span (ZMod 2) {y, g y} := Submodule.subset_span (by simp)
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1)
    (Submodule.smul_mem _ _ (Submodule.add_mem _ h1 h2))

private theorem line_cases [Finite V] (g : GLV V) (hg3 : ∀ v, g (g v) + g v + v = 0) {y : V}
    (hy : y ≠ 0) : ∀ a ∈ Submodule.span (ZMod 2) {y, g y},
      a = 0 ∨ a = y ∨ a = g y ∨ a = g (g y) := by
  intro a ha
  have hgy0 : g y ≠ 0 := fun h => hy (g.injective (h.trans (map_zero g).symm))
  have hgyn : g y ≠ y := fun h => hy (g_fpf g hg3 y h)
  have h1 : g y ∈ Submodule.span (ZMod 2) {y, g y} := Submodule.subset_span (by simp)
  have h2 : y ∈ Submodule.span (ZMod 2) {y, g y} := Submodule.subset_span (by simp)
  rcases mem_plane_cases (line_finrank g hg3 hy) h2 h1 hy hgy0 hgyn a ha with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [h, g_sq g hg3 y, add_comm]

private theorem plane_eq [Finite V] (g : GLV V) (hg3 : ∀ v, g (g v) + g v + v = 0) {y : V}
    (hy : y ≠ 0) {J J' : Submodule (ZMod 2) V} (hJ : ∀ a ∈ J, g a ∈ J)
    (hJ' : ∀ a ∈ J', g a ∈ J') (h2 : Module.finrank (ZMod 2) J = 2)
    (h2' : Module.finrank (ZMod 2) J' = 2) (hyJ : y ∈ J) (hyJ' : y ∈ J') : J = J' := by
  have e : ∀ K : Submodule (ZMod 2) V, (∀ a ∈ K, g a ∈ K) → Module.finrank (ZMod 2) K = 2 →
      y ∈ K → Submodule.span (ZMod 2) {y, g y} = K := by
    intro K hK hK2 hyK
    refine Submodule.eq_of_le_of_finrank_le ?_ (by rw [line_finrank g hg3 hy, hK2])
    refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact hyK
    · exact hK y hyK
  rw [← e J hJ h2 hyJ, ← e J' hJ' h2' hyJ']

private theorem isSolvable_of_normalized_order_three [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (halt : ∀ v, B v v = 0)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) (hd : Module.finrank (ZMod 2) V = 4)
    (Γ : Subgroup (GLV V)) (hΓ : ∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) (g : GLV V)
    (hgΓ : g ∈ Γ) (hg3 : ∀ v, g (g v) + g v + v = 0)
    (hnorm : ∀ γ ∈ Γ, γ * g * γ⁻¹ = g ∨ γ * g * γ⁻¹ = g * g) : Group.IsSolvable Γ := by
  have hgB : ∀ x y, B (g x) (g y) = B x y := hΓ g hgΓ
  have hnd' : B.Nondegenerate := nondeg_of_alt B halt hnd
  have hrefl : B.IsRefl := LinearMap.BilinForm.IsAlt.isRefl (B₁ := B) halt
  have hconj : ∀ γ ∈ Γ, ∀ x, ∃ g' : GLV V, (g' = g ∨ g' = g * g) ∧ g (γ x) = γ (g' x) := by
    intro γ hγ x
    refine ⟨γ⁻¹ * g * γ, ?_, ?_⟩
    · have := hnorm γ⁻¹ (Γ.inv_mem hγ)
      simpa using this
    · simp [mul_assoc]
  have hq_inv : ∀ γ ∈ Γ, ∀ x, B (γ x) (g (γ x)) = B x (g x) := by
    intro γ hγ x
    obtain ⟨g', hg', hgx⟩ := hconj γ hγ x
    rw [hgx, hΓ γ hγ]
    rcases hg' with h | h
    · rw [h]
    · rw [h]
      show B x (g (g x)) = B x (g x)
      rw [g_sq g hg3 x, map_add, halt x, add_zero]
  have hq_g : ∀ x, B (g x) (g (g x)) = B x (g x) := fun x => hgB x (g x)
  obtain ⟨x₁, hx₁⟩ := exists_q_eq_one B halt hnd hd g hgB hg3
  have hx₀ : x₁ ≠ 0 := by
    rintro rfl
    simp at hx₁
  set A₁ : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {x₁, g x₁} with hA₁
  have hA₁2 : Module.finrank (ZMod 2) A₁ = 2 := line_finrank g hg3 hx₀
  have hA₁g : ∀ a ∈ A₁, g a ∈ A₁ := line_inv g hg3 x₁
  have hcol₁ : ∀ a ∈ A₁, a ≠ 0 → B a (g a) = 1 := by
    intro a ha ha0
    rcases line_cases g hg3 hx₀ a ha with h | h | h | h
    · exact absurd h ha0
    · rw [h]
      exact hx₁
    · rw [h]
      exact (hq_g x₁).trans hx₁
    · rw [h]
      exact (hq_g (g x₁)).trans ((hq_g x₁).trans hx₁)
  set A₂ : Submodule (ZMod 2) V := B.orthogonal A₁ with hA₂
  have hA₂g : ∀ a ∈ A₂, g a ∈ A₂ := by
    intro a ha
    rw [hA₂, LinearMap.BilinForm.mem_orthogonal_iff] at ha ⊢
    intro n hn
    have h1 : B (g (g n)) a = 0 := ha _ (hA₁g _ (hA₁g _ hn))
    calc B n (g a) = B (g (g (g n))) (g a) := by rw [g_cube g hg3 n]
      _ = B (g (g n)) a := hgB _ _
      _ = 0 := h1
  have hA₂2 : Module.finrank (ZMod 2) A₂ = 2 := by
    rw [hA₂, finrank_orthogonal_four B halt hnd hd, hA₁2]
  have hinf : A₁ ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    by_contra hv0
    have hv0' : v ≠ 0 := fun h => hv0 (by rw [h]; exact Submodule.zero_mem _)
    have hq1 := hcol₁ v hv1 hv0'
    have h0 : B (g v) v = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.1 hv2) (g v) (hA₁g v hv1)
    rw [alt_symm B halt v (g v), h0] at hq1
    exact zero_ne_one hq1
  have hsup : A₁ ⊔ A₂ = ⊤ := sup_eq_top_of_finrank_two hd hA₁2 hA₂2 hinf
  have hcol₂ : ∀ b ∈ A₂, b ≠ 0 → B b (g b) = 1 := by
    intro b hb hb0
    by_contra hq
    have hq0 : B b (g b) = 0 := by
      rcases zmod_two_cases (B b (g b)) with h | h
      · exact h
      · exact absurd h hq
    have hPb : Submodule.span (ZMod 2) {b, g b} = A₂ := by
      refine Submodule.eq_of_le_of_finrank_le ?_ (by rw [line_finrank g hg3 hb0, hA₂2])
      refine Submodule.span_le.2 ?_
      intro x hx
      rcases hx with rfl | rfl
      · exact hb
      · exact hA₂g b hb
    have hvan : ∀ u ∈ A₂, ∀ u' ∈ A₂, B u u' = 0 := by
      intro u hu u' hu'
      rw [← hPb] at hu hu'
      obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hu
      obtain ⟨c', d', rfl⟩ := Submodule.mem_span_pair.1 hu'
      have e1 : B (g b) b = 0 := by
        rw [← alt_symm B halt b (g b)]
        exact hq0
      simp [map_add, map_smul, halt b, hq0, e1, halt (g b)]
    have hle : A₂ ≤ A₁ := by
      intro a ha
      have : a ∈ B.orthogonal A₂ :=
        LinearMap.BilinForm.mem_orthogonal_iff.2 (fun n hn => hvan n hn a ha)
      rwa [show B.orthogonal A₂ = A₁ from
        LinearMap.BilinForm.orthogonal_orthogonal hnd' hrefl A₁] at this
    have hbot : A₂ ≤ ⊥ := by
      intro a ha
      rw [← hinf]
      exact ⟨hle ha, ha⟩
    have := Submodule.finrank_mono hbot
    rw [finrank_bot] at this
    omega
  have hanis : ∀ z, B z (g z) = 1 → z ∈ A₁ ∨ z ∈ A₂ := by
    intro z hz
    have hz' : z ∈ A₁ ⊔ A₂ := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz'
    have hab : B a b = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hb) a ha
    rw [q_add B halt g hgB hg3 a b, hab, add_zero] at hz
    by_cases ha0 : a = 0
    · right
      rw [ha0, zero_add]
      exact hb
    · by_cases hb0 : b = 0
      · left
        rw [hb0, add_zero]
        exact ha
      · exfalso
        rw [hcol₁ a ha ha0, hcol₂ b hb hb0] at hz
        exact absurd hz (by decide)
  have hclosed_aux : ∀ γ ∈ Γ, ∀ A : Submodule (ZMod 2) V, (∀ a ∈ A, g a ∈ A) →
      Module.finrank (ZMod 2) A = 2 → (∀ a ∈ A, a ≠ 0 → B a (g a) = 1) →
      conjSub γ A = A₁ ∨ conjSub γ A = A₂ := by
    intro γ hγ A hAg hA2 hAcol
    obtain ⟨a₀, ha₀, ha₀0⟩ : ∃ a ∈ A, a ≠ 0 := by
      by_contra hh
      push Not at hh
      have : A = ⊥ := (Submodule.eq_bot_iff A).2 hh
      rw [this, finrank_bot] at hA2
      omega
    have hy0 : γ a₀ ≠ 0 := fun h => ha₀0 (γ.injective (h.trans (map_zero γ).symm))
    have hyA : γ a₀ ∈ conjSub γ A := apply_mem_conjSub ha₀
    have hq : B (γ a₀) (g (γ a₀)) = 1 := by
      rw [hq_inv γ hγ a₀]
      exact hAcol a₀ ha₀ ha₀0
    have hgA : ∀ v ∈ conjSub γ A, g v ∈ conjSub γ A := by
      intro v hv
      obtain ⟨a, ha, rfl⟩ := hv
      obtain ⟨g', hg', hgx⟩ := hconj γ hγ a
      have hmem : g' a ∈ A := by
        rcases hg' with h | h
        · rw [h]
          exact hAg a ha
        · rw [h]
          exact hAg _ (hAg a ha)
      show g (γ a) ∈ conjSub γ A
      rw [hgx]
      exact ⟨g' a, hmem, rfl⟩
    have hA'2 : Module.finrank (ZMod 2) (conjSub γ A) = 2 := by
      rw [finrank_conjSub]
      exact hA2
    rcases hanis _ hq with h | h
    · exact Or.inl (plane_eq g hg3 hy0 hgA hA₁g hA'2 hA₁2 hyA h)
    · exact Or.inr (plane_eq g hg3 hy0 hgA hA₂g hA'2 hA₂2 hyA h)
  let 𝒮 : Set (Submodule (ZMod 2) V) := {A₁, A₂}
  have hclosed : ∀ δ ∈ Γ, ∀ S ∈ 𝒮, conjSub δ S ∈ 𝒮 := by
    intro δ hδ S hS
    simp only [𝒮, Set.mem_insert_iff, Set.mem_singleton_iff] at hS ⊢
    rcases hS with h | h
    · rw [h]
      exact hclosed_aux δ hδ A₁ hA₁g hA₁2 hcol₁
    · rw [h]
      exact hclosed_aux δ hδ A₂ hA₂g hA₂2 hcol₂
  refine isSolvable_of_subspaceAct Γ 𝒮 hclosed (le_trans (Set.ncard_insert_le _ _) (by simp)) ?_
  intro K hKΓ hKfix
  have hinv : Invariant K A₁ := by
    intro k hk u hu
    have := apply_mem_conjSub (g := k) hu
    rwa [hKfix k hk A₁ (Set.mem_insert _ _)] at this
  exact isSolvable_of_invariant_two B halt hnd hd K (fun γ hγ => hΓ γ (hKΓ hγ)) A₁ hinv hA₁2

theorem isSolvable_of_normal_invariant_two [Finite V] (B : LinearMap.BilinForm (ZMod 2) V)
    (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hd : Module.finrank (ZMod 2) V = 4) (Γ H : Subgroup (GLV V))
    (hΓ : ∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) (hHΓ : H ≤ Γ)
    (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hH1 : H ≠ ⊥) (U : Submodule (ZMod 2) V)
    (hU : Module.finrank (ZMod 2) U = 2) (hUi : Invariant H U) : Group.IsSolvable ↥Γ := by
  have hfin := finite_submodule_zmod_two (V := V)
  by_cases hC : fixedSpace H = ⊥
  swap
  · refine isSolvable_of_invariant_subspace_four B halt hnd hd Γ hΓ (fixedSpace H)
      (invariant_fixedSpace hHn) hC ?_
    intro htop
    apply hH1
    rw [Subgroup.eq_bot_iff_forall]
    exact fixedSpace_eq_top_iff.1 htop
  have hirr : IsIrr H U := by
    refine ⟨hUi, ?_, ?_⟩
    · refine bot_lt_iff_ne_bot.2 ?_
      intro h
      rw [h, finrank_bot] at hU
      omega
    · intro J hJ _ hJU
      by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ Module.finrank (ZMod 2) J := Submodule.one_le_finrank_iff.2 hcon.1
      have h2 : Module.finrank (ZMod 2) J < Module.finrank (ZMod 2) U :=
        Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hJU hcon.2)
      obtain ⟨z, hzJ, hz0, hZz⟩ := exists_generator_of_finrank_one J (by omega)
      apply hz0
      have hzfix : z ∈ fixedSpace H := by
        intro h hh
        rcases hZz _ (hJ h hh z hzJ) with h' | h'
        · exact absurd (h.injective (h'.trans (map_zero h).symm)) hz0
        · exact h'
      rw [hC] at hzfix
      exact hzfix
  let 𝒪 : Set (Submodule (ZMod 2) V) := {S | ∃ γ ∈ Γ, S = conjSub γ U}
  have hclosed : ∀ δ ∈ Γ, ∀ S ∈ 𝒪, conjSub δ S ∈ 𝒪 := by
    rintro δ hδ S ⟨γ, hγ, rfl⟩
    exact ⟨δ * γ, Γ.mul_mem hδ hγ, (conjSub_mul δ γ U).symm⟩
  by_cases hc : 𝒪.ncard ≤ 4
  · refine isSolvable_of_subspaceAct Γ 𝒪 hclosed hc ?_
    intro K hKΓ hKfix
    have hUO : U ∈ 𝒪 := ⟨1, Γ.one_mem, (conjSub_one U).symm⟩
    have hinv : Invariant K U := by
      intro k hk u hu
      have := apply_mem_conjSub (g := k) hu
      rwa [hKfix k hk U hUO] at this
    exact isSolvable_of_invariant_two B halt hnd hd K (fun γ hγ => hΓ γ (hKΓ hγ)) U hinv hU
  · have h2 : 2 < 𝒪.ncard := by omega
    obtain ⟨S₁, S₂, S₃, h1, h2', h3, h12, h13, h23⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite 𝒪)).1 h2
    have hmem : ∀ S ∈ 𝒪, IsIrr H S ∧ Module.finrank (ZMod 2) S = 2 := by
      rintro S ⟨γ, hγ, rfl⟩
      exact ⟨hirr.conj_of_normal hHn hγ, by rw [finrank_conjSub]; exact hU⟩
    have hti : ∀ S ∈ 𝒪, ∀ S' ∈ 𝒪, S ≠ S' → S ⊓ S' = ⊥ := by
      rintro S ⟨γ, hγ, rfl⟩ S' ⟨δ, hδ, rfl⟩ hne
      have hirr' : IsIrr H (conjSub δ U) := hirr.conj_of_normal hHn hδ
      have := hirr'.conj_eq_or_inf_eq_bot hHn (Γ.mul_mem hγ (Γ.inv_mem hδ))
      have e : conjSub (γ * δ⁻¹) (conjSub δ U) = conjSub γ U := by
        rw [← conjSub_mul, inv_mul_cancel_right]
      rw [e] at this
      rcases this with h | h
      · exact absurd h hne
      · exact h
    obtain ⟨g, hgH, hg3, hnorm⟩ := exists_normalized_order_three hd Γ H hHn (hmem S₁ h1).1
      (hmem S₂ h2').1.1 (hmem S₃ h3).1.1 (hmem S₁ h1).2 (hmem S₂ h2').2 (hmem S₃ h3).2
      (hti S₁ h1 S₂ h2' h12) (hti S₁ h1 S₃ h3 h13) (hti S₂ h2' S₃ h3 h23)
    exact isSolvable_of_normalized_order_three B halt hnd hd Γ hΓ g (hHΓ hgH) hg3 hnorm

end G11

end CFSG.Quasithin
