module

public import CFSG.Quasithin.Background.G10FifteenSwap

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem mem_perp_iff_decomp {B : LinearMap.BilinForm (ZMod 2) V} {v w : V} : w ∈ perp B v ↔ B v w = 0 :=
  LinearMap.mem_ker

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem conj_inf_eq_bot {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    {x : GLV V} (hx : x ∈ X) (hne : conjSub x I ≠ I) : conjSub x I ⊓ I = ⊥ := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  rcases hirr.conj_eq_or_inf_eq_bot (normalClosure_normal Γ L) (hyp.X_le hx) with h | h
  · exact absurd h hne
  · exact h

theorem X_comm_apply {y z : GLV V} (hy : y ∈ X) (hz : z ∈ X) (v : V) : y (z v) = z (y v) := by
  have := hyp.X_comm y hy z hz
  exact congrArg (fun g : GLV V => g v) this

omit [Finite V] hyp in
theorem phi_inj {I : Submodule (ZMod 2) V} {x : GLV V} (hTI : conjSub x I ⊓ I = ⊥) {a b : V}
    (ha : a ∈ I) (hb : b ∈ I) (h : x a + a = x b + b) : a = b := by
  have h1 : x (a + b) + (a + b) = 0 := by
    rw [map_add]
    calc x a + x b + (a + b) = (x a + a) + (x b + b) := by abel
      _ = (x b + b) + (x b + b) := by rw [h]
      _ = 0 := add_self_eq_zero_of_zmod2 _
  have h2 : a + b = 0 := eq_zero_of_conj_add hTI (I.add_mem ha hb) h1
  have h3 : a = -b := eq_neg_of_add_eq_zero_left h2
  rw [h3]
  exact neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_zmod2 b)

theorem relIndex_stabilizerOf_eq_two {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) : (stabilizerOf X I).relIndex X = 2 := by
  have hperm := hyp.permutes hI hfix hx hne
  have hXc := hyp.X_comm
  have hX2 := hyp.X_sq
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨x, hx⟩, fun b => ?_⟩
  have hb : (b : GLV V) ∈ X := b.2
  have hbx : (b : GLV V) * x = x * b := hXc _ hb x hx
  have hmem : ∀ c : ↥X, c ∈ (stabilizerOf X I).subgroupOf X ↔ conjSub (c : GLV V) I = I := by
    intro c
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨c.2, h⟩⟩
  have hbxI : conjSub ((b : GLV V) * x) I = conjSub x (conjSub (b : GLV V) I) := by
    rw [hbx, conjSub_mul]
  have hxI' : conjSub x (conjSub x I) = I := conjSub_conjSub_of_sq (hX2 x hx) I
  show Xor (b * ⟨x, hx⟩ ∈ (stabilizerOf X I).subgroupOf X) (b ∈ (stabilizerOf X I).subgroupOf X)
  rw [hmem, hmem]
  show Xor (conjSub ((b : GLV V) * x) I = I) (conjSub (b : GLV V) I = I)
  rw [hbxI]
  rcases hperm b hb with h | h
  · rw [h]
    exact Or.inr ⟨rfl, fun hh => hne hh⟩
  · rw [h, hxI']
    exact Or.inl ⟨rfl, fun hh => hne hh⟩


theorem invariant_sup_conj {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) :
    Invariant (normalClosure Γ L ⊔ X) (I ⊔ conjSub x I) := by
  have hperm := hyp.permutes hI hfix hx hne
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hHI : Invariant (normalClosure Γ L) (I ⊔ conjSub x I) :=
    hI.1.sup (hI.1.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx))
  have hXI : Invariant X (I ⊔ conjSub x I) := by
    rw [invariant_iff_conjSub_le]
    intro y hy
    rw [conjSub_sup]
    have hcomm : x * y = y * x := hyp.X_comm x hx y hy
    have h1 : conjSub y (conjSub x I) = conjSub x (conjSub y I) := (conjSub_comm hcomm.symm I)
    have h2 : conjSub x (conjSub x I) = I := conjSub_conjSub_of_sq (hyp.X_sq x hx) I
    rw [h1]
    rcases hperm y hy with h | h
    · rw [h]
    · rw [h, h2]
      exact sup_le le_sup_right le_sup_left
  exact hHI.sup_subgroup hXI

theorem exists_decomp (h10 : G1010Concl Γ v₁ X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) :
    ∃ i, i ∈ I ∧ i ≠ 0 ∧ v₁ = i + x i ∧ ∀ y ∈ stabilizerOf X I, y i = i := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hTI := hyp.conj_inf_eq_bot hI hx hne
  have hinv := hyp.invariant_sup_conj hI hfix hx hne
  have hbot : I ⊔ conjSub x I ≠ ⊥ := fun h => hirr.ne_bot (le_bot_iff.1 (h ▸ le_sup_left))
  have hv : v₁ ∈ I ⊔ conjSub x I := (h10 _ hbot hinv).1
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv
  have hxx : conjSub x (conjSub x I) = I := conjSub_conjSub_of_sq (hyp.X_sq x hx) I
  have hxa : x a ∈ conjSub x I := apply_mem_conjSub ha
  have hxb : x b ∈ I := by
    have := apply_mem_conjSub (g := x) hb
    rwa [hxx] at this
  have hfixed : x (a + b) = a + b := by rw [hab]; exact hyp.X_fixes x hx
  have hxb' : x b = a := by
    have h1 : (x b + a) + (x a + b) = 0 := by
      rw [map_add] at hfixed
      calc (x b + a) + (x a + b) = (x a + x b) + (a + b) := by abel
        _ = (a + b) + (a + b) := by rw [hfixed]
        _ = 0 := add_self_eq_zero_of_zmod2 _
    have hd : x b + a ∈ conjSub x I ⊓ I := by
      refine ⟨?_, I.add_mem hxb ha⟩
      have : x b + a = -(x a + b) := eq_neg_of_add_eq_zero_left h1
      rw [this]
      exact (conjSub x I).neg_mem ((conjSub x I).add_mem hxa hb)
    rw [hTI, Submodule.mem_bot] at hd
    have : x b = -a := eq_neg_of_add_eq_zero_left hd
    rw [this]
    exact neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_zmod2 a)
  have hbxa : b = x a := by
    have : x (x b) = x a := by rw [hxb']
    have h2 : x (x b) = b := by
      have := congrArg (fun g : GLV V => g b) (hyp.X_sq x hx)
      simpa using this
    rw [← h2, hxb']
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · rintro rfl
    apply hyp.point
    rw [← hab, hbxa, map_zero, add_zero]
  · rw [← hab, hbxa]
  · intro y hy
    have hyI : conjSub y I = I := hy.2
    have hyv : y v₁ = v₁ := hyp.X_fixes y hy.1
    have hv' : v₁ = a + x a := by rw [← hab, hbxa]
    rw [hv', map_add] at hyv
    have hya : y a ∈ I := by
      have := apply_mem_conjSub (g := y) ha
      rwa [hyI] at this
    have hyxa : y (x a) = x (y a) := hyp.X_comm_apply hy.1 hx a
    rw [hyxa] at hyv
    have h1 : (y a + a) + (x (y a) + x a) = 0 := by
      calc (y a + a) + (x (y a) + x a) = (y a + x (y a)) + (a + x a) := by abel
        _ = (a + x a) + (a + x a) := by rw [hyv]
        _ = 0 := add_self_eq_zero_of_zmod2 _
    have hd : y a + a ∈ conjSub x I ⊓ I := by
      have h2 : x (y a) + x a ∈ conjSub x I := by
        rw [← map_add]
        exact apply_mem_conjSub (I.add_mem hya ha)
      have h3 : y a + a = -(x (y a) + x a) := eq_neg_of_add_eq_zero_left h1
      refine ⟨?_, I.add_mem hya ha⟩
      rw [h3]
      exact (conjSub x I).neg_mem h2
    rw [hTI, Submodule.mem_bot] at hd
    have : y a = -a := eq_neg_of_add_eq_zero_left hd
    rw [this]
    exact neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_zmod2 a)

theorem exists_stab_not_mem_X₀ {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) : ∃ y ∈ stabilizerOf X I, y ∉ X₀ := by
  by_contra hcon
  push Not at hcon
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hTI := hyp.conj_inf_eq_bot hI hx hne
  have hYX₀ : stabilizerOf X I ≤ X₀ := fun y hy => hcon y hy
  have hmul := Subgroup.relIndex_mul_relIndex (stabilizerOf X I) X₀ X hYX₀ hyp.X₀_le
  rw [relIndex_stabilizerOf_eq_two hyp hI hfix hx hne] at hmul
  have hdvd : X₀.relIndex X ∣ 2 := Dvd.intro_left _ hmul
  have hle2 : X₀.relIndex X ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hlog : Nat.log 2 (X₀.relIndex X) ≤ 1 := by
    calc Nat.log 2 (X₀.relIndex X) ≤ Nat.log 2 2 := Nat.log_mono_right hle2
      _ = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h1 := hyp.rank
  have h2 := hyp.toG101Hyp.finrank_isotropic_le
  have h3 := hyp.two_lt_finrank hirr
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq I (conjSub x I)
  rw [inf_comm, hTI, finrank_bot, add_zero, finrank_conjSub] at h4
  have h5 : Module.finrank (ZMod 2) ↥(I ⊔ conjSub x I) ≤ Module.finrank (ZMod 2) V :=
    Submodule.finrank_le _
  omega


theorem phi_mem_W {x : GLV V} (hx : x ∈ X) {u : V} (hu : u ∈ perp B v₁) : x u + u ∈ W := by
  have h1 := hyp.commutator_le x hx u hu
  have h2 : x u + u = x u - u := by
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (add_self_eq_zero_of_zmod2 u)]
  rw [h2]
  exact h1

theorem exists_i (h10 : G1010Concl Γ v₁ X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) :
    ∃ i, ∃ _ : i ∈ I ⊓ perp B v₁, i ≠ 0 ∧ v₁ = i + x i ∧ ∀ y ∈ stabilizerOf X I, y i = i := by
  obtain ⟨i, hiI, hi0, hv, hY⟩ := hyp.exists_decomp h10 hI hfix hx hne
  obtain ⟨y, hy, hyX₀⟩ := hyp.exists_stab_not_mem_X₀ hI hfix hx hne
  have hperp : i ∈ perp B v₁ := mem_perp_iff_decomp.2 (hyp.centralizer_le y hy.1 hyX₀ i (hY y hy))
  exact ⟨i, ⟨hiI, hperp⟩, hi0, hv, hY⟩

theorem fullTransvections {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) {i : V} (hi : i ∈ I ⊓ perp B v₁) (hv : v₁ = i + x i) :
    FullTransvections (stabilizerOf X I) (I ⊓ perp B v₁) i hi := by
  have hTI := hyp.conj_inf_eq_bot hI hx hne
  have hperm := hyp.permutes hI hfix hx hne
  have hxv : x v₁ = v₁ := hyp.X_fixes x hx
  have hv' : x i + i = v₁ := by rw [hv, add_comm]
  let ψ : ↥(I ⊓ perp B v₁) →ₗ[ZMod 2] ↥W :=
    { toFun := fun u => ⟨x (u : V) + (u : V), hyp.phi_mem_W hx u.2.2⟩
      map_add' := fun a b => Subtype.ext (by
        show x ((a + b : ↥(I ⊓ perp B v₁)) : V) + ((a + b : ↥(I ⊓ perp B v₁)) : V) = _
        simp only [Submodule.coe_add, map_add]
        abel)
      map_smul' := fun c a => Subtype.ext (by
        show x ((c • a : ↥(I ⊓ perp B v₁)) : V) + ((c • a : ↥(I ⊓ perp B v₁)) : V) = _
        simp only [Submodule.coe_smul, map_smul, smul_add, RingHom.id_apply]) }
  have hψ : ∀ u : ↥(I ⊓ perp B v₁), ((ψ u : ↥W) : V) = x (u : V) + (u : V) := fun u => rfl
  have hψi : ψ ⟨i, hi⟩ = ⟨v₁, hyp.mem_W⟩ := Subtype.ext (by rw [hψ]; exact hv')
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun w : ↥W => (w : V)) hab
    exact phi_inj hTI a.2.1 b.2.1 this
  have key : ∀ (f : ↥(I ⊓ perp B v₁) →ₗ[ZMod 2] ZMod 2) (y : GLV V), y ∈ stabilizerOf X I →
      (∀ u : ↥(I ⊓ perp B v₁), y (x (u : V) + (u : V)) = (x (u : V) + (u : V)) + f u • v₁) →
      ∀ u : ↥(I ⊓ perp B v₁), y (u : V) = (u : V) + f u • i := by
    intro f y hy hP u
    have hyI : y (u : V) ∈ I := by
      have := apply_mem_conjSub (g := y) u.2.1
      rwa [hy.2] at this
    have hI2 : (u : V) + f u • i ∈ I := I.add_mem u.2.1 (I.smul_mem _ hi.1)
    apply phi_inj hTI hyI hI2
    have e1 : x (y (u : V)) + y (u : V) = y (x (u : V) + (u : V)) := by
      rw [map_add, hyp.X_comm_apply hx hy.1]
    have h3 : f u • v₁ = f u • (i + x i) := congrArg (fun w => f u • w) hv
    have e2 : x ((u : V) + f u • i) + ((u : V) + f u • i) =
        (x (u : V) + (u : V)) + f u • v₁ := by
      rw [map_add, map_smul, h3, smul_add]
      abel
    rw [e1, e2]
    exact hP u
  refine ⟨fun y hy => ?_, fun f hf => ?_⟩
  · obtain ⟨f', hf'0, hf'⟩ := hyp.transvection y hy.1
    refine ⟨f'.comp ψ, ?_, ?_⟩
    · show f' (ψ ⟨i, hi⟩) = 0
      rw [hψi]
      exact hf'0
    · refine key (f'.comp ψ) y hy (fun u => ?_)
      have := hf' (ψ u)
      rw [hψ] at this
      exact this
  ·
    let f₀ : ↥(LinearMap.range ψ) →ₗ[ZMod 2] ZMod 2 :=
      f.comp (LinearEquiv.ofInjective ψ hψinj).symm.toLinearMap
    obtain ⟨g, hg⟩ := Subspace.dualRestrict_surjective (W := LinearMap.range ψ) f₀
    have hgψ : ∀ u : ↥(I ⊓ perp B v₁), g (ψ u) = f u := by
      intro u
      have h1 := congrArg (fun h : Module.Dual (ZMod 2) ↥(LinearMap.range ψ) =>
        h (LinearEquiv.ofInjective ψ hψinj u)) hg
      simp only [Submodule.dualRestrict_apply] at h1
      have h2 : ((LinearEquiv.ofInjective ψ hψinj u : ↥(LinearMap.range ψ)) : ↥W) = ψ u := rfl
      rw [h2] at h1
      rw [h1]
      show f ((LinearEquiv.ofInjective ψ hψinj).symm (LinearEquiv.ofInjective ψ hψinj u)) = f u
      rw [LinearEquiv.symm_apply_apply]
    have hg0 : g ⟨v₁, hyp.mem_W⟩ = 0 := by
      rw [← hψi, hgψ]
      exact hf
    obtain ⟨z, hz, hzf⟩ := hyp.transvection_full g hg0
    have hP : ∀ u : ↥(I ⊓ perp B v₁), z (x (u : V) + (u : V)) = (x (u : V) + (u : V)) + f u • v₁ := by
      intro u
      have := hzf (ψ u)
      rw [hψ, hgψ] at this
      exact this
    by_cases hzY : conjSub z I = I
    · exact ⟨z, ⟨hz, hzY⟩, key f z ⟨hz, hzY⟩ hP⟩
    · have hzI' : conjSub z I = conjSub x I := (hperm z hz).resolve_left hzY
      have hxz : conjSub (x * z) I = I := by
        rw [conjSub_mul, hzI', conjSub_conjSub_of_sq (hyp.X_sq x hx)]
      have hxzY : x * z ∈ stabilizerOf X I := ⟨X.mul_mem hx hz, hxz⟩
      refine ⟨x * z, hxzY, key f (x * z) hxzY (fun u => ?_)⟩
      show x (z (x (u : V) + (u : V))) = _
      rw [hP u, map_add, map_smul, hxv]
      have hx2 : x (x (u : V) + (u : V)) = (u : V) + x (u : V) := by
        rw [map_add]
        have := congrArg (fun g : GLV V => g (u : V)) (hyp.X_sq x hx)
        simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] at this
        rw [this]
      rw [hx2]
      abel


omit [Finite V] hyp in
theorem not_mem_of_ne (h11 : G1011Concl Γ v₁ X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I) {x : GLV V} (hx : x ∈ X) (hne : conjSub x I ≠ I) :
    v₁ ∉ I := by
  intro hv
  have hXI : Invariant X I := (h11 I hI).2 hv
  exact hne (hXI.conjSub_eq hx)

theorem inf_W_eq_span (h11 : G1011Concl Γ v₁ X L) (h12 : G1012Concl Γ v₁ W X L)
    {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) {i : V} (hi : i ∈ I ⊓ perp B v₁) (hi0 : i ≠ 0)
    (hv : v₁ = i + x i) : I ⊓ W = Submodule.span (ZMod 2) {i} := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hFT := hyp.fullTransvections hI hfix hx hne hi hv
  have hdim : 2 ≤ Module.finrank (ZMod 2) ↥(I ⊓ perp B v₁) := by
    have h1 := finrank_le_finrank_inf_perp_add_one hyp.toG101Hyp.nondegenerate' hyp.point I
    have h2 := hyp.two_lt_finrank hirr
    omega
  obtain ⟨u, hu, u', hu', hu0, hu'0, huu'⟩ := exists_two_ne hdim
  obtain ⟨u₀, hu₀, hu₀0, hu₀i⟩ : ∃ u₀ ∈ I ⊓ perp B v₁, u₀ ≠ 0 ∧ u₀ ≠ i := by
    by_cases h : u = i
    · exact ⟨u', hu', hu'0, fun h' => huu' (h.trans h'.symm)⟩
    · exact ⟨u, hu, hu0, h⟩
  have hnot : (⟨u₀, hu₀⟩ : ↥(I ⊓ perp B v₁)) ∉ Submodule.span (ZMod 2)
      {(⟨i, hi⟩ : ↥(I ⊓ perp B v₁))} := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    have hc' : c • i = u₀ := congrArg Subtype.val hc
    rcases hc2 c with rfl | rfl
    · rw [zero_smul] at hc'
      exact hu₀0 hc'.symm
    · rw [one_smul] at hc'
      exact hu₀i hc'.symm
  obtain ⟨f, hfu, hfle⟩ := Submodule.exists_le_ker_of_notMem hnot
  have hfi : f ⟨i, hi⟩ = 0 := hfle (Submodule.mem_span_singleton_self _)
  have hf1 : f ⟨u₀, hu₀⟩ = 1 := by
    have hc : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    exact hc _ hfu
  obtain ⟨y, hy, hyf⟩ := hFT.2 f hfi
  have hyu := hyf ⟨u₀, hu₀⟩
  rw [hf1, one_smul] at hyu
  have hiW : i ∈ W := by
    have h1 := hyp.phi_mem_W hy.1 hu₀.2
    have h2 : y u₀ + u₀ = i := by
      show y ((⟨u₀, hu₀⟩ : ↥(I ⊓ perp B v₁)) : V) + u₀ = i
      rw [hyu, add_assoc, add_comm i u₀, ← add_assoc, add_self_eq_zero_of_zmod2, zero_add]
    rw [h2] at h1
    exact h1
  have hle : Submodule.span (ZMod 2) {i} ≤ I ⊓ W := by
    rw [Submodule.span_le]
    rintro _ rfl
    exact ⟨hi.1, hiW⟩
  have hvI := not_mem_of_ne h11 hI hx hne
  have hfin := (h12 I hI hvI).1
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [finrank_span_singleton hi0]
  exact hfin

theorem fixedSpace_stabilizerOf_inf {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) {i : V} (hiI : i ∈ I) (hi0 : i ≠ 0)
    (hv : v₁ = i + x i) (hYi : ∀ y ∈ stabilizerOf X I, y i = i)
    (hfs : fixedSpace X = Submodule.span (ZMod 2) {v₁}) :
    fixedSpace (stabilizerOf X I) ⊓ I = Submodule.span (ZMod 2) {i} := by
  have hTI := hyp.conj_inf_eq_bot hI hx hne
  have hX2 := hyp.X_sq x hx
  have hperm := hyp.permutes hI hfix hx hne
  have hxx : ∀ v : V, x (x v) = v := fun v => by
    have := congrArg (fun g : GLV V => g v) hX2
    simpa using this
  refine le_antisymm ?_ ?_
  · rintro a ⟨ha1, ha2⟩
    have hfa : ∀ y ∈ stabilizerOf X I, y a = a := fun y hy => ha1 y hy
    have hfixX : x a + a ∈ fixedSpace X := by
      intro z hz
      rw [map_add, hyp.X_comm_apply hz hx a]
      by_cases hzY : conjSub z I = I
      · rw [hfa z ⟨hz, hzY⟩]
      · have hzI' : conjSub z I = conjSub x I := (hperm z hz).resolve_left hzY
        have hxz : x * z ∈ stabilizerOf X I := ⟨X.mul_mem hx hz, by
          rw [conjSub_mul, hzI', conjSub_conjSub_of_sq hX2]⟩
        have h1 : z a = x a := by
          have := hfa _ hxz
          have h2 : x (z a) = a := this
          calc z a = x (x (z a)) := (hxx _).symm
            _ = x a := by rw [h2]
        rw [h1, hxx a]
        exact add_comm _ _
    rw [hfs] at hfixX
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hfixX
    have hv' : x i + i = v₁ := by rw [hv, add_comm]
    rcases hc2 c with rfl | rfl
    · rw [zero_smul] at hc
      have : a = 0 := phi_inj hTI ha2 (Submodule.zero_mem _) (by rw [← hc, map_zero, add_zero])
      rw [this]
      exact Submodule.zero_mem _
    · rw [one_smul] at hc
      have : a = i := phi_inj hTI ha2 hiI (hc.symm.trans hv'.symm)
      rw [this]
      exact Submodule.mem_span_singleton_self _
  · rw [Submodule.span_le]
    rintro _ rfl
    exact ⟨fun y hy => hYi y hy, hiI⟩

end G108Hyp

end G11

end CFSG.Quasithin
