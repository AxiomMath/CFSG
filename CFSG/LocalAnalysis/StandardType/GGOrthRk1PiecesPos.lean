module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Pieces

public section

open Module Multiplicative

namespace CFSG.StandardType

namespace OrthTorus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

private theorem mem_reflFixedCoordPos_iff (i j : Fin r)
    (f : Fin r → Multiplicative (ZMod p)) :
    f ∈ reflFixedCoordPos p r i j ↔ f i * f j = 1 := by
  unfold reflFixedCoordPos
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply, Pi.evalMonoidHom_apply, Pi.evalMonoidHom_apply]

private theorem mem_reflFixedCoordPos_mulSingle (i j k : Fin r) (hki : k ≠ i) (hkj : k ≠ j) :
    Pi.mulSingle k (ofAdd (1 : ZMod p)) ∈ reflFixedCoordPos p r i j := by
  rw [mem_reflFixedCoordPos_iff]
  rw [Pi.mulSingle_eq_of_ne (Ne.symm hki), Pi.mulSingle_eq_of_ne (Ne.symm hkj), one_mul]

omit [Finite K] [FiniteDimensional K V] in
private theorem tau_mem_piece (Δ : TBJOmData Q p A r)
    (f : Fin r → Multiplicative (ZMod p)) (l : Fin r) :
    ∀ u ∈ Δ.F.U l, Δ.τ f u ∈ Δ.F.U l := by
  intro u hu
  rw [← Δ.θ_range l] at hu
  obtain ⟨d, rfl⟩ := hu
  rw [Δ.tau_theta, ← Δ.θ_range l]
  exact LinearMap.mem_range_self _ _

omit [Finite K] [FiniteDimensional K V] in
private theorem tau_eq_self_of_coord_zero (Δ : TBJOmData Q p A r)
    (f : Fin r → Multiplicative (ZMod p)) {l : Fin r} (h : toAdd (f l) = 0) :
    ∀ u ∈ Δ.F.U l, Δ.τ f u = u := by
  intro u hu
  rw [← Δ.θ_range l] at hu
  obtain ⟨d, rfl⟩ := hu
  rw [Δ.tau_theta, h]
  simp

omit [Finite K] in
private theorem tau_sub_mem (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (f : Fin r → Multiplicative (ZMod p)) (S : Submodule K V)
    (hU : ∀ l, Δ.F.U l ≤ S ∨ toAdd (f l) = 0) :
    ∀ v, Δ.τ f v - v ∈ S := by
  intro v
  have hv : v ∈ ⨆ l, Δ.F.U l := by
    rw [Δ.iSup_U_eq_top hfix]
    exact Submodule.mem_top
  refine Submodule.iSup_induction (p := fun l => Δ.F.U l)
    (motive := fun x => Δ.τ f x - x ∈ S) hv (fun l x hx => ?_) ?_ ?_
  · rcases hU l with hle | hz
    · exact S.sub_mem (hle (tau_mem_piece Δ f l x hx)) (hle hx)
    · rw [tau_eq_self_of_coord_zero Δ f hz x hx, sub_self]
      exact S.zero_mem
  · rw [map_zero, sub_self]
    exact S.zero_mem
  · intro x y hx hy
    have : Δ.τ f (x + y) - (x + y) = (Δ.τ f x - x) + (Δ.τ f y - y) := by
      rw [map_add]
      abel
    rw [this]
    exact S.add_mem hx hy

omit [Finite K] [FiniteDimensional K V] in
private theorem tau_sub_eq_zero_single [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (f : Fin r → Multiplicative (ZMod p)) (l : Fin r) (h : toAdd (f l) = 1) :
    ∀ u ∈ Δ.F.U l, Δ.τ f u - u = 0 → u = 0 := by
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  intro u hu hzu
  rw [← Δ.θ_range l] at hu
  obtain ⟨d, rfl⟩ := hu
  rw [Δ.tau_theta, sub_eq_zero] at hzu
  have hval : (toAdd (f l)).val = 1 := by rw [h, ZMod.val_one]
  rw [hval, pow_one] at hzu
  have hcd : (Δ.c : Δ.D →ₗ[K] Δ.D) d = d := Δ.θ_inj l hzu
  have hd : d = 0 := Δ.c_fix d hcd
  rw [hd, map_zero]

private theorem zmod_val_neg_one_add_one (hp : p.Prime) : (-1 : ZMod p).val + 1 = p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hlt : (-1 : ZMod p).val < p := ZMod.val_lt _
  have hdiv : p ∣ (-1 : ZMod p).val + 1 := by
    rw [← ZMod.natCast_eq_zero_iff (((-1 : ZMod p).val + 1)) p]
    simp
  have hle : p ≤ (-1 : ZMod p).val + 1 := Nat.le_of_dvd (Nat.succ_pos _) hdiv
  omega

omit [Finite K] [FiniteDimensional K V] in
private theorem tau_sub_eq_zero_neg [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (f : Fin r → Multiplicative (ZMod p)) (l : Fin r) (h : toAdd (f l) = -1) :
    ∀ u ∈ Δ.F.U l, Δ.τ f u - u = 0 → u = 0 := by
  intro u hu hzu
  rw [← Δ.θ_range l] at hu
  obtain ⟨d, rfl⟩ := hu
  rw [Δ.tau_theta, sub_eq_zero] at hzu
  have hcd : (Δ.c ^ (toAdd (f l)).val) d = d := Δ.θ_inj l hzu
  set n := (toAdd (f l)).val with hn
  have hval : n + 1 = p := by
    rw [hn, h]
    exact zmod_val_neg_one_add_one (Fact.out : p.Prime)
  have hstep : (Δ.c ^ (n + 1)) d = Δ.c d := by
    rw [pow_succ', LinearEquiv.mul_apply]
    exact congrArg (fun x => Δ.c x) hcd
  have hfixd : d = 0 := by
    refine Δ.c_fix d ?_
    rw [hval] at hstep
    rw [Δ.c_pow] at hstep
    simpa using hstep.symm
  rw [hfixd, map_zero]

omit [Finite K] in
private theorem tau_sub_surj_of_inj_on (Δ : TBJOmData Q p A r)
    (f : Fin r → Multiplicative (ZMod p)) (l : Fin r)
    (hinj : ∀ u ∈ Δ.F.U l, Δ.τ f u - u = 0 → u = 0) :
    ∀ u ∈ Δ.F.U l, ∃ u' ∈ Δ.F.U l, Δ.τ f u' - u' = u := by
  intro u hu
  let φ : Δ.F.U l →ₗ[K] Δ.F.U l :=
    ((Δ.τ f).toLinearMap - 1).restrict (p := Δ.F.U l) (q := Δ.F.U l) (fun x hx => by
      simpa using (Δ.F.U l).sub_mem (tau_mem_piece Δ f l x hx) hx)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero φ]
    intro x hx0
    have h : Δ.τ f x.1 - x.1 = 0 := by
      have h' := congrArg Subtype.val hx0
      simpa [φ] using h'
    exact Subtype.ext (hinj x.1 x.2 h)
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hφinj) ⟨u, hu⟩
  refine ⟨x.1, x.2, ?_⟩
  have h' := congrArg Subtype.val hx
  simpa [φ] using h'

omit [Finite K] [FiniteDimensional K V] in
private theorem mapsTo_of_tau (Δ : TBJOmData Q p A r) (g : V ≃ₗ[K] V)
    (f : Fin r → Multiplicative (ZMod p)) (S : Submodule K V)
    (hcomm : Δ.τ f * g = g * Δ.τ f)
    (hsub : ∀ v, Δ.τ f v - v ∈ S)
    (hsurj : ∀ u ∈ S, ∃ u' ∈ S, Δ.τ f u' - u' = u) :
    ∀ u ∈ S, g u ∈ S := by
  intro u hu
  obtain ⟨u', -, hu'⟩ := hsurj u hu
  have h1 : g u = Δ.τ f (g u') - g u' := by
    have h2 : g (Δ.τ f u') = Δ.τ f (g u') := by
      have h' := congrArg (fun e : V ≃ₗ[K] V => e u') hcomm
      simpa [LinearEquiv.mul_apply] using h'.symm
    rw [← hu', map_sub, h2]
  rw [h1]
  exact hsub (g u')

omit [Finite K] in
private theorem mapsTo_piece_of_single [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (i j k : Fin r)
    (hki : k ≠ i) (hkj : k ≠ j) {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer (Δ.reflFixedPos i j : Set (V ≃ₗ[K] V))) :
    ∀ u ∈ Δ.F.U k, g u ∈ Δ.F.U k := by
  let f : Fin r → Multiplicative (ZMod p) := Pi.mulSingle k (ofAdd (1 : ZMod p))
  have hfcoord : f ∈ reflFixedCoordPos p r i j :=
    mem_reflFixedCoordPos_mulSingle i j k hki hkj
  have hy : Δ.τ f ∈ Δ.reflFixedPos i j := Subgroup.mem_map_of_mem _ hfcoord
  have hcomm : Δ.τ f * g = g * Δ.τ f := Subgroup.mem_centralizer_iff.mp hg _ hy
  have hsub : ∀ v, Δ.τ f v - v ∈ Δ.F.U k := by
    refine tau_sub_mem Δ hfix f (Δ.F.U k) ?_
    intro l
    by_cases hlk : l = k
    · subst hlk
      exact Or.inl le_rfl
    · refine Or.inr ?_
      simp only [f]
      rw [Pi.mulSingle_eq_of_ne hlk]
      exact toAdd_one
  have hfk : toAdd (f k) = (1 : ZMod p) := by
    simp only [f]
    rw [Pi.mulSingle_eq_same, toAdd_ofAdd]
  have hsurj : ∀ u ∈ Δ.F.U k, ∃ u' ∈ Δ.F.U k, Δ.τ f u' - u' = u :=
    tau_sub_surj_of_inj_on Δ f k (tau_sub_eq_zero_single Δ f k hfk)
  exact mapsTo_of_tau Δ g f (Δ.F.U k) hcomm hsub hsurj

omit [Finite K] [FiniteDimensional K V] in
private theorem tau_mulSingle_theta [Fact p.Prime] (Δ : TBJOmData Q p A r) (k : Fin r)
    (d : Δ.D) :
    Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) (Δ.θ k d) = Δ.θ k (Δ.c d) := by
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  rw [Δ.tau_theta, Pi.mulSingle_eq_same, toAdd_ofAdd, ZMod.val_one, pow_one]

omit [Finite K] in
theorem TBJOmData.centralizerPos_mapsTo [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (i j : Fin r) (hij : i ≠ j) {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer (Δ.reflFixedPos i j : Set (V ≃ₗ[K] V))) :
    (∀ k, k ≠ i → k ≠ j → ∀ u ∈ Δ.F.U k, g u ∈ Δ.F.U k) ∧
      ∀ w ∈ Δ.F.U i ⊔ Δ.F.U j, g w ∈ Δ.F.U i ⊔ Δ.F.U j := by
  constructor
  · intro k hki hkj
    exact mapsTo_piece_of_single Δ hfix i j k hki hkj hg
  · let fW : Fin r → Multiplicative (ZMod p) :=
      Function.update (Function.update (1 : Fin r → Multiplicative (ZMod p)) i (ofAdd 1)) j
        (ofAdd (-1))
    have hfWi : fW i = ofAdd (1 : ZMod p) := by
      change Function.update (Function.update (1 : Fin r → Multiplicative (ZMod p)) i (ofAdd 1))
        j (ofAdd (-1)) i = ofAdd 1
      rw [Function.update_of_ne hij, Function.update_self]
    have hfWj : fW j = ofAdd (-1 : ZMod p) := by
      change Function.update (Function.update (1 : Fin r → Multiplicative (ZMod p)) i (ofAdd 1))
        j (ofAdd (-1)) j = ofAdd (-1)
      rw [Function.update_self]
    have hfWcoord : fW ∈ reflFixedCoordPos p r i j := by
      rw [mem_reflFixedCoordPos_iff, hfWi, hfWj]
      rw [← ofAdd_add, add_neg_cancel, ofAdd_zero]
    have hyW : Δ.τ fW ∈ Δ.reflFixedPos i j := Subgroup.mem_map_of_mem _ hfWcoord
    have hcommW : Δ.τ fW * g = g * Δ.τ fW := Subgroup.mem_centralizer_iff.mp hg _ hyW
    have hfWzero : ∀ l, l ≠ i → l ≠ j → toAdd (fW l) = 0 := by
      intro l hli hlj
      change toAdd (Function.update (Function.update (1 : Fin r → Multiplicative (ZMod p)) i
        (ofAdd 1)) j (ofAdd (-1)) l) = (0 : ZMod p)
      rw [Function.update_of_ne hlj, Function.update_of_ne hli]
      exact toAdd_one
    have hsubW : ∀ v, Δ.τ fW v - v ∈ Δ.F.U i ⊔ Δ.F.U j := by
      refine tau_sub_mem Δ hfix fW _ ?_
      intro l
      by_cases hli : l = i
      · subst hli
        exact Or.inl le_sup_left
      · by_cases hlj : l = j
        · subst hlj
          exact Or.inl le_sup_right
        · exact Or.inr (hfWzero l hli hlj)
    have hsurjW : ∀ u ∈ Δ.F.U i ⊔ Δ.F.U j,
        ∃ u' ∈ Δ.F.U i ⊔ Δ.F.U j, Δ.τ fW u' - u' = u := by
      intro u hu
      rw [Submodule.mem_sup] at hu
      obtain ⟨a, ha, b, hb, rfl⟩ := hu
      have hfi : toAdd (fW i) = 1 := by rw [hfWi, toAdd_ofAdd]
      have hfj : toAdd (fW j) = -1 := by rw [hfWj, toAdd_ofAdd]
      obtain ⟨a', ha'i, ha'⟩ :=
        tau_sub_surj_of_inj_on Δ fW i (tau_sub_eq_zero_single Δ fW i hfi) a ha
      obtain ⟨b', hb'j, hb'⟩ :=
        tau_sub_surj_of_inj_on Δ fW j (tau_sub_eq_zero_neg Δ fW j hfj) b hb
      refine ⟨a' + b', Submodule.add_mem_sup ha'i hb'j, ?_⟩
      rw [map_add]
      have h : Δ.τ fW a' + Δ.τ fW b' - (a' + b') =
          (Δ.τ fW a' - a') + (Δ.τ fW b' - b') := by abel
      rw [h, ha', hb']
    exact mapsTo_of_tau Δ g fW (Δ.F.U i ⊔ Δ.F.U j) hcommW hsubW hsurjW

omit [Finite K] in
theorem TBJOmData.centralizerPos_two_fix [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (i j : Fin r) {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer (Δ.reflFixedPos i j : Set (V ≃ₗ[K] V))) {m : ℕ}
    (hm : g ^ (2 ^ m) = 1) (k : Fin r) (hki : k ≠ i) (hkj : k ≠ j) :
    ∀ u ∈ Δ.F.U k, g u = u := by
  have hmap : ∀ u ∈ Δ.F.U k, g u ∈ Δ.F.U k := mapsTo_piece_of_single Δ hfix i j k hki hkj hg
  have htau : ∀ d, Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) (Δ.θ k d) = Δ.θ k (Δ.c d) :=
    tau_mulSingle_theta Δ k
  let e : Δ.D ≃ₗ[K] LinearMap.range (Δ.θ k) := LinearEquiv.ofInjective (Δ.θ k) (Δ.θ_inj k)
  let g' : Module.End K Δ.D :=
    e.symm.toLinearMap ∘ₗ (g.toLinearMap ∘ₗ Δ.θ k).codRestrict (LinearMap.range (Δ.θ k))
      (fun d => by
        rw [Δ.θ_range k]
        exact hmap _ (by rw [← Δ.θ_range k]; exact LinearMap.mem_range_self _ _))
  have hθg' : ∀ d, Δ.θ k (g' d) = g (Δ.θ k d) := by
    intro d
    show Δ.θ k (e.symm ((g.toLinearMap ∘ₗ Δ.θ k).codRestrict (LinearMap.range (Δ.θ k)) _ d)) =
      g (Δ.θ k d)
    exact LinearEquiv.ofInjective_symm_apply (Δ.θ k) _
  have hcomm : g' ∘ₗ (Δ.c : Δ.D →ₗ[K] Δ.D) = (Δ.c : Δ.D →ₗ[K] Δ.D) ∘ₗ g' := by
    ext d
    have hgy : g (Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) (Δ.θ k d)) =
        Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) (g (Δ.θ k d)) := by
      have hfcoord : Pi.mulSingle k (ofAdd (1 : ZMod p)) ∈ reflFixedCoordPos p r i j :=
        mem_reflFixedCoordPos_mulSingle i j k hki hkj
      have hy : Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) ∈ Δ.reflFixedPos i j :=
        Subgroup.mem_map_of_mem _ hfcoord
      have hcomm' := Subgroup.mem_centralizer_iff.mp hg _ hy
      have h' := congrArg (fun e : V ≃ₗ[K] V => e (Δ.θ k d)) hcomm'
      simpa [LinearEquiv.mul_apply] using h'.symm
    apply Δ.θ_inj k
    calc
      Δ.θ k ((g' ∘ₗ (Δ.c : Δ.D →ₗ[K] Δ.D)) d) = Δ.θ k (g' (Δ.c d)) := rfl
      _ = g (Δ.θ k (Δ.c d)) := hθg' (Δ.c d)
      _ = g (Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) (Δ.θ k d)) := by rw [← htau d]
      _ = Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) (g (Δ.θ k d)) := hgy
      _ = Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) (Δ.θ k (g' d)) := by rw [hθg' d]
      _ = Δ.θ k (Δ.c (g' d)) := htau (g' d)
      _ = Δ.θ k (((Δ.c : Δ.D →ₗ[K] Δ.D) ∘ₗ g') d) := rfl
  have hpow : ∀ n d, Δ.θ k ((g' ^ n) d) = (g ^ n) (Δ.θ k d) := by
    intro n
    induction n with
    | zero =>
      intro d
      simp
    | succ n ih =>
      intro d
      rw [pow_succ, pow_succ, Module.End.mul_apply, LinearEquiv.mul_apply, ih (g' d)]
      exact congrArg (g ^ n) (hθg' d)
  have hg'pow : g' ^ (2 ^ m) = 1 := by
    ext d
    apply Δ.θ_inj k
    rw [hpow (2 ^ m) d, hm]
    simp
  have hg'1 : g' = 1 := (Δ.rk1Block hp2).eq_one_of_commute hcomm hg'pow
  intro u hu
  rw [← Δ.θ_range k] at hu
  obtain ⟨d, rfl⟩ := hu
  rw [← hθg' d, hg'1]
  simp

end OrthTorus

end CFSG.StandardType

end
