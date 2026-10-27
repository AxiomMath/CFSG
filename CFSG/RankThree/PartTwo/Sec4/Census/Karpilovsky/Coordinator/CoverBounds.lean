module

public import CFSG.Sporadic.Recognition.CoverRecipeSq
public import CFSG.GH74.Generic.GKFCover
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.RankThree.PerfectCover Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] {m : ℕ} {g : Fin m → X} {R : List (List (Fin m × Bool))}
  {cw : Fin m → List (Fin m × Bool)}

theorem lift_coverWords_eq_one {Y : Type} [Group Y] {e : Fin m → Y}
    (hc : ∀ r ∈ R, FreeGroup.lift e (FreeGroup.mk r) ∈ center Y)
    (hfix : ∀ i, FreeGroup.lift e (FreeGroup.mk (cw i)) = e i) :
    ∀ r ∈ wordSet (coverWords R cw), FreeGroup.lift e r = 1 := by
  intro r hr
  rw [← coverRelators_wordSet R cw] at hr
  refine (lift_coverRelators_eq_one_iff (e := e) (R := wordSet R)
    (w := fun i => FreeGroup.mk (cw i))).2 ⟨fun i r' hr' => ?_, hfix⟩ r hr
  obtain ⟨r'', hr'', rfl⟩ := List.mem_map.1 hr'
  exact commutatorElement_eq_one_iff_mul_comm.2 ((mem_center_iff.mp (hc r'' hr'')) (e i))

theorem card_ker_mul_le_card_of_forall (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {ws : List (List (Fin m × Bool))}
    (hfin : Finite (PG m ws)) {Q : Type} [Group Q] [Finite Q]
    (hQ : Group.IsPerfect Q) (q : Q →* X) (hqs : Function.Surjective q)
    (hker : q.ker ≤ center Q)
    (hws : ∀ ee : Fin m → Q, (∀ i, q (ee i) = g i) →
      (∀ i, FreeGroup.lift ee (FreeGroup.mk (cw i)) = ee i) →
        ∀ w ∈ ws, FreeGroup.lift ee (FreeGroup.mk w) = 1) :
    Nat.card q.ker * Nat.card X ≤ Nat.card (PG m ws) := by
  classical
  have hcomp : ∀ b : Fin m → Q, q.comp (FreeGroup.lift b) = FreeGroup.lift (fun i => q (b i)) :=
    fun b => FreeGroup.ext_hom _ _ fun i => by simp
  choose a ha using fun i => hqs (g i)
  set ee : Fin m → Q := fun i => FreeGroup.lift a (FreeGroup.mk (cw i)) with hee
  have hqa : (fun i => q (a i)) = g := funext ha
  have hqee : (fun i => q (ee i)) = g := by
    funext i
    simp only [hee]
    rw [← MonoidHom.comp_apply, hcomp, hqa, hwg]
  have hfix : ∀ i, FreeGroup.lift ee (FreeGroup.mk (cw i)) = ee i := fun i =>
    eq_of_mem_commutator_of_central q hker (FreeGroup.lift ee) (FreeGroup.lift a)
      (by rw [hcomp, hcomp, hqa, hqee]) (hw i)
  have hrel0 := hws ee (fun i => congrFun hqee i) hfix
  have hrel : ∀ r ∈ wordSet ws, FreeGroup.lift ee r = 1 := fun r hr => by
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hr
    exact hrel0 w hw'
  have hE0 : Subgroup.closure (Set.range ee) = ⊤ := by
    set E0 := Subgroup.closure (Set.range ee) with hE0def
    have hmap : E0.map q = ⊤ := by
      rw [hE0def, MonoidHom.map_closure, ← Set.range_comp]
      have : (q ∘ ee) = g := hqee
      rw [this]
      exact hgen
    have hsplit : ∀ x : Q, ∃ y ∈ E0, ∃ z ∈ center Q, x = y * z := fun x => by
      have : q x ∈ E0.map q := by rw [hmap]; trivial
      obtain ⟨y, hy, hyx⟩ := this
      refine ⟨y, hy, y⁻¹ * x, hker ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have hcom : commutator Q ≤ E0 := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨x1, hx1, z1, hz1, rfl⟩ := hsplit x
      obtain ⟨y1, hy1, z2, hz2, rfl⟩ := hsplit y
      rw [commutator_mul_center hz1 hz2, commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx1 hy1) (inv_mem hx1)) (inv_mem hy1)
    exact eq_top_iff.2 ((Group.isPerfect_def.1 hQ) ▸ hcom)
  let ψ : PG m ws →* Q := PresentedGroup.toGroup (f := ee) hrel
  have hψs : Function.Surjective ψ := by
    intro x
    have hy : x ∈ Subgroup.closure (Set.range ee) := by rw [hE0]; trivial
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of hrel⟩
    | one => exact ⟨1, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨p', hp'⟩ := hy
      exact ⟨p * p', by rw [map_mul, hp, hp']⟩
    | inv x _ hx =>
      obtain ⟨p, hp⟩ := hx
      exact ⟨p⁻¹, by rw [map_inv, hp]⟩
  have h1 := Nat.card_le_card_of_surjective ψ hψs
  rw [CFSG.GH74.Generic.card_eq_card_mul_card_ker q hqs, mul_comm] at h1
  exact h1

theorem card_ker_mul_le_card_cover (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1)
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {ws : List (List (Fin m × Bool))}
    (hsub : ∀ w ∈ ws, w ∈ coverWords R cw) (hfin : Finite (PG m ws)) {Q : Type} [Group Q]
    [Finite Q] (hQ : Group.IsPerfect Q) (q : Q →* X) (hqs : Function.Surjective q)
    (hker : q.ker ≤ center Q) :
    Nat.card q.ker * Nat.card X ≤ Nat.card (PG m ws) := by
  refine card_ker_mul_le_card_of_forall hgen hw hwg hfin hQ q hqs hker fun ee hee hfix w hw' => ?_
  have hrc : ∀ r ∈ R, FreeGroup.lift ee (FreeGroup.mk r) ∈ center Q := fun r hr => by
    refine hker ?_
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply,
      show q.comp (FreeGroup.lift ee) = FreeGroup.lift (fun i => q (ee i)) from
        FreeGroup.ext_hom _ _ fun i => by simp,
      show (fun i => q (ee i)) = g from funext hee]
    exact hR r hr
  exact lift_coverWords_eq_one hrc hfix _ (List.mem_map_of_mem (hsub w hw'))

theorem isPerfect_PG_of_cw (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    {ws : List (List (Fin m × Bool))} (hcw : ∀ i, (i, false) :: cw i ∈ ws) :
    Group.IsPerfect (PG m ws) := by
  rw [Group.isPerfect_def, eq_top_iff, ← PresentedGroup.closure_range_of, closure_le]
  rintro _ ⟨i, rfl⟩
  have h : (PresentedGroup.of i : PG m ws) = PresentedGroup.mk _ (FreeGroup.mk (cw i)) := by
    have h1 : (FreeGroup.of i)⁻¹ * FreeGroup.mk (cw i) = FreeGroup.mk ((i, false) :: cw i) := rfl
    exact PresentedGroup.mk_eq_mk_of_inv_mul_mem (by
      rw [h1]
      exact List.mem_map_of_mem (hcw i))
  rw [h]
  have h2 := mem_map_of_mem (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk})
    (hw i)
  rw [map_commutator_eq] at h2
  rw [_root_.commutator_def]
  exact commutator_mono le_top le_top h2

theorem exists_coverHom' (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    {ws : List (List (Fin m × Bool))}
    (hg : ∀ w ∈ ws, FreeGroup.lift g (FreeGroup.mk w) = 1) (hcw : ∀ i, (i, false) :: cw i ∈ ws) :
    ∃ ψ : PG m ws →* X, Function.Surjective ψ ∧
      (∀ w : List (Fin m × Bool), ψ (PresentedGroup.mk
        {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk w)) =
          FreeGroup.lift g (FreeGroup.mk w)) ∧
      Group.IsPerfect (PG m ws) := by
  have hrel : ∀ r ∈ wordSet ws, FreeGroup.lift g r = 1 := fun r hr => by
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hr
    exact hg w hw'
  have hψs : Function.Surjective (PresentedGroup.toGroup (f := g) hrel) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of hrel⟩
  have hperf : Group.IsPerfect (PG m ws) := isPerfect_PG_of_cw hw hcw
  exact ⟨PresentedGroup.toGroup (f := g) hrel, hψs, fun w => rfl, hperf⟩

theorem exists_coverHom (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1)
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {ws : List (List (Fin m × Bool))}
    (hsub : ∀ w ∈ ws, w ∈ coverWords R cw) (hcw : ∀ i, (i, false) :: cw i ∈ ws) :
    ∃ ψ : PG m ws →* X, Function.Surjective ψ ∧
      (∀ w : List (Fin m × Bool), ψ (PresentedGroup.mk
        {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk w)) =
          FreeGroup.lift g (FreeGroup.mk w)) ∧
      Group.IsPerfect (PG m ws) := by
  have hrel0 : ∀ r ∈ wordSet (coverWords R cw), FreeGroup.lift g r = 1 :=
    lift_coverWords_eq_one (fun r hr => by rw [hR r hr]; exact one_mem _) hwg
  exact exists_coverHom' hgen hw (fun w hw' => hrel0 _ (List.mem_map_of_mem (hsub w hw'))) hcw

theorem card_hopfMultiplier_le_of_cover
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1)
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {ws : List (List (Fin m × Bool))}
    (hsub : ∀ w ∈ ws, w ∈ coverWords R cw) (hcw : ∀ i, (i, false) :: cw i ∈ ws)
    (hfin : Finite (PG m ws)) {p : ℕ} (hcard : Nat.card (PG m ws) ≤ p * Nat.card X) :
    0 < Nat.card (hopfMultiplier X) ∧ Nat.card (hopfMultiplier X) ≤ p := by
  obtain ⟨ψ, hψs, -, hperf⟩ := exists_coverHom hgen hR hw hwg hsub hcw
  have : Finite X := Finite.of_surjective ψ hψs
  have : Group.IsPerfect X := Group.IsPerfect.ofSurjective hψs
  have : Finite (HopfCover X) := finite_hopfCover inferInstance
  have : Group.IsPerfect (HopfCover X) := hopfCover_isPerfect
  have h := card_ker_mul_le_card_cover hgen hR hw hwg hsub hfin
    ‹Group.IsPerfect (HopfCover X)› (hopfCoverMap X) (hopfCoverMap_surjective (S := X))
    hopfMultiplier_le_center
  have hX : 0 < Nat.card X := Nat.card_pos
  have := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
  exact ⟨Nat.card_pos, Nat.le_of_mul_le_mul_right (h.trans hcard) hX⟩

theorem card_hopfMultiplier_le_of_forall (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {ws : List (List (Fin m × Bool))}
    (hg : ∀ w ∈ ws, FreeGroup.lift g (FreeGroup.mk w) = 1) (hcw : ∀ i, (i, false) :: cw i ∈ ws)
    (hfin : Finite (PG m ws)) {p : ℕ} (hcard : Nat.card (PG m ws) ≤ p * Nat.card X)
    (hws : ∀ {Q : Type} [Group Q] [Finite Q], Group.IsPerfect Q → ∀ q : Q →* X,
      Function.Surjective q → q.ker ≤ center Q → ∀ ee : Fin m → Q, (∀ i, q (ee i) = g i) →
        (∀ i, FreeGroup.lift ee (FreeGroup.mk (cw i)) = ee i) →
          ∀ w ∈ ws, FreeGroup.lift ee (FreeGroup.mk w) = 1) :
    0 < Nat.card (hopfMultiplier X) ∧ Nat.card (hopfMultiplier X) ≤ p := by
  obtain ⟨ψ, hψs, -, hperf⟩ := exists_coverHom' hgen hw hg hcw
  have : Finite X := Finite.of_surjective ψ hψs
  have : Group.IsPerfect X := Group.IsPerfect.ofSurjective hψs
  have : Finite (HopfCover X) := finite_hopfCover inferInstance
  have : Group.IsPerfect (HopfCover X) := hopfCover_isPerfect
  have h := card_ker_mul_le_card_of_forall hgen hw hwg hfin ‹Group.IsPerfect (HopfCover X)›
    (hopfCoverMap X) (hopfCoverMap_surjective (S := X)) hopfMultiplier_le_center
    (hws ‹Group.IsPerfect (HopfCover X)› (hopfCoverMap X) (hopfCoverMap_surjective (S := X))
      hopfMultiplier_le_center)
  have hX : 0 < Nat.card X := Nat.card_pos
  have := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
  exact ⟨Nat.card_pos, Nat.le_of_mul_le_mul_right (h.trans hcard) hX⟩

theorem iota_eq_one_of_twist {H Q : Type*} [Group H] [Group Q] (hH : Group.IsPerfect H)
    (q : Q →* X) (hker : q.ker ≤ center Q) (σ : H →* X) (ι : H →* Q) (hqι : q.comp ι = σ)
    (α : H →* H) (τ : Q)
    (hα : ∀ h : H, q (τ * ι h * τ⁻¹) = q (ι (α h))) {ζ : H} (hσζ : σ ζ = 1)
    (hαζ : α ζ = ζ⁻¹) (h3 : ζ ^ 3 = 1) : ι ζ = 1 := by
  have hcongr : ∀ h : H, τ * ι h * τ⁻¹ = ι (α h) := by
    let β : H →* Q := (MulAut.conj τ).toMonoidHom.comp ι
    have hb : ∀ h, β h = τ * ι h * τ⁻¹ := fun h => rfl
    have hq : q.comp β = q.comp (ι.comp α) := by
      ext h
      simp only [MonoidHom.comp_apply, hb]
      exact hα h
    intro h
    have hh : h ∈ commutator H := by
      rw [hH.commutator_eq_top]; trivial
    have := eq_of_mem_commutator_of_central q hker β (ι.comp α) hq hh
    simpa [hb] using this
  have hz : ι ζ ∈ center Q := by
    refine hker ?_
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hqι]
    exact hσζ
  have h1 : ι (ζ⁻¹) = ι ζ := by
    rw [← hαζ, ← hcongr ζ]
    exact ((mem_center_iff.mp hz) τ).symm ▸ by group
  have h2 : (ι ζ) ^ 2 = 1 := by
    rw [map_inv] at h1
    have : (ι ζ)⁻¹ = ι ζ := h1
    calc (ι ζ) ^ 2 = ι ζ * ι ζ := sq _
      _ = ι ζ * (ι ζ)⁻¹ := by rw [this]
      _ = 1 := mul_inv_cancel _
  have h3' : (ι ζ) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  calc ι ζ = (ι ζ) ^ 3 * ((ι ζ) ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3', h2]; simp

theorem commute_of_normal_zpowers_of_perfect {P : Type} [Group P] (hP : Group.IsPerfect P) {u : P}
    (hn : (zpowers u).Normal) (k : P) : k * u = u * k := by
  let ρ : P →* (ZMod (Nat.card (zpowers u)))ˣ :=
    (IsCyclic.mulAutMulEquiv (zpowers u)).toMonoidHom.comp
      (MulAut.conjNormal (H := zpowers u))
  have hker : ρ.ker = ⊤ := by
    have h := Abelianization.commutator_subset_ker ρ
    rwa [hP.commutator_eq_top, top_le_iff] at h
  have h1 : ρ k = 1 := MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top _)
  have h2 : (MulAut.conjNormal (H := zpowers u) k) = 1 :=
    (IsCyclic.mulAutMulEquiv (zpowers u)).injective (by simpa [ρ] using h1)
  have h3 := MulAut.conjNormal_apply (H := zpowers u) k ⟨u, Subgroup.mem_zpowers u⟩
  rw [h2] at h3
  have h4 : u = k * u * k⁻¹ := h3
  calc k * u = (k * u * k⁻¹) * k := by group
    _ = u * k := by rw [← h4]

theorem dvd_card_hopfMultiplier_of_cover (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1)
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {ws : List (List (Fin m × Bool))}
    (hsub : ∀ w ∈ ws, w ∈ coverWords R cw) (hcw : ∀ i, (i, false) :: cw i ∈ ws)
    (hfin : Finite (PG m ws)) {ℓ : ℕ} (hcard : Nat.card (PG m ws) ≤ ℓ * Nat.card X)
    {w : List (Fin m × Bool)} (hw1 : FreeGroup.lift g (FreeGroup.mk w) = 1)
    (hord : ℓ ∣ orderOf (PresentedGroup.mk
      {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk w))) :
    ℓ ∣ Nat.card (hopfMultiplier X) := by
  classical
  obtain ⟨ψ, hψs, hψmk, hperf⟩ := exists_coverHom hgen hR hw hwg hsub hcw
  have hXfin : Finite X := Finite.of_surjective ψ hψs
  set z : PG m ws :=
    PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk w) with hz
  have hzK : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hz, hψmk]
    exact hw1
  have hcardP := CFSG.GH74.Generic.card_eq_card_mul_card_ker ψ hψs
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hKpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hKle : Nat.card ψ.ker ≤ ℓ := by
    rw [hcardP, mul_comm] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hXpos
  have hdvdK : ℓ ∣ Nat.card ψ.ker := by
    refine hord.trans ?_
    rw [← Subgroup.orderOf_mk z hzK]
    exact orderOf_dvd_natCard _
  have hKeq : Nat.card ψ.ker = ℓ := le_antisymm hKle (Nat.le_of_dvd hKpos hdvdK)
  have hordz : orderOf z = ℓ := by
    refine Nat.dvd_antisymm ?_ hord
    rw [← hKeq, ← Subgroup.orderOf_mk z hzK]
    exact orderOf_dvd_natCard _
  have hzp : zpowers z = ψ.ker := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hzK) ?_
    rw [Nat.card_zpowers, hordz, hKeq]
  have hnorm : (zpowers z).Normal := by rw [hzp]; infer_instance
  have hcen : ψ.ker ≤ center (PG m ws) := by
    rw [← hzp]
    intro y hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
    rw [mem_center_iff]
    intro k
    exact ((show Commute k z from
      commute_of_normal_zpowers_of_perfect hperf hnorm k).zpow_right n).eq
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hperf ψ hψs hcen
  rwa [hKeq] at hdvd

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
