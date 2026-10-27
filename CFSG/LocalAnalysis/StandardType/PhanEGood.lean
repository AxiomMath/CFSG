module

public import CFSG.LocalAnalysis.StandardType.PhanEGoodTorus

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {w₀ : (coxeterMatrix D.isFiniteType).Group}
  {F : FrobData D n H w₀} {n₀ : K} (L : StdLevi F n₀)
  {G : Type} [Group G] {ρ : G →* K} (hρ : Function.Injective ρ) (hρr : ρ.range = stdFix F n₀)
  {Kf : Type} [Field Kf] [Finite Kf] {f : ℕ} [CharP Kf 2] (κ : Kf ≃+* L.Fld)
  (hκ : ∀ c, κ (unitaryInvolution Kf 2 f c) = L.θ (κ c))

private theorem hmbGood_rho_iota (hext : SteinbergExtras D n H) (i : Fin D.rank)
    (A : Su Kf 2 f 2) :
    ρ ((stdFamily L hρ hρr κ hκ hext).ι i A) = L.ε i (suToSL (f := f) κ 2 A) :=
  ρ_stdIota L hρ hρr κ hκ i A

private theorem hmbGood_rho_theta (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (hij : i < j) (h3 : coxeterMatrix D.isFiniteType i j = 3) (A : Su Kf 2 f 3) :
    ρ ((stdFamily L hρ hρr κ hκ hext).θ i j A) = L.ε₂ i j (suToSL (f := f) κ 3 A) :=
  ρ_stdTheta L hρ hρr κ hκ hij h3 A

private theorem hmbGood_iota_inj (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    Function.Injective ((stdFamily L hρ hρr κ hκ hext).ι i) := by
  intro a b hab
  apply suToSL_injective (f := f) κ 2
  apply L.ε_inj i
  have h := congrArg ρ hab
  rwa [hmbGood_rho_iota L hρ hρr κ hκ hext i a,
    hmbGood_rho_iota L hρ hρr κ hκ hext i b] at h

private theorem hmbGood_theta_inj (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (hij : i < j) (h3 : coxeterMatrix D.isFiniteType i j = 3) :
    Function.Injective ((stdFamily L hρ hρr κ hκ hext).θ i j) := by
  intro a b hab
  apply suToSL_injective (f := f) κ 3
  apply L.ε₂_inj i j hij h3
  have h := congrArg ρ hab
  rwa [hmbGood_rho_theta L hρ hρr κ hκ hext hij h3 a,
    hmbGood_rho_theta L hρ hρr κ hκ hext hij h3 b] at h

private theorem hmbGood_disj (hext : SteinbergExtras D n H)
    (hsl : ∀ i j : Fin D.rank, i ≠ j →
      coxeterMatrix D.isFiniteType i j = 2 ∨ coxeterMatrix D.isFiniteType i j = 3)
    (i j : Fin D.rank) (hij : i ≠ j) :
    ((stdFamily L hρ hρr κ hκ hext).ι i).range ⊓
      ((stdFamily L hρ hρr κ hκ hext).ι j).range = ⊥ := by
  haveI : CharP L.Fld 2 :=
    charP_of_injective_ringHom (f := (κ : Kf →+* L.Fld)) κ.injective 2
  rw [eq_bot_iff]
  rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  rw [Subgroup.mem_bot]
  have hε : L.ε i (suToSL (f := f) κ 2 a) = L.ε j (suToSL (f := f) κ 2 b) := by
    have h := congrArg ρ hb
    rw [hmbGood_rho_iota L hρ hρr κ hκ hext j b,
      hmbGood_rho_iota L hρ hρr κ hκ hext i a] at h
    exact h.symm
  rcases hsl i j hij with h2 | h3
  · have h2' : coxeterMatrix D.isFiniteType j i = 2 :=
      (CoxeterMatrix.symmetric (coxeterMatrix D.isFiniteType) j i).trans h2
    have hA1 : suToSL (f := f) κ 2 a = 1 := by
      apply sl2_eq_one_of_commute
      intro A'
      have hcomm : Commute (L.ε j (suToSL (f := f) κ 2 b)) (L.ε i A') :=
        L.ε_commute hext h2' (suToSL (f := f) κ 2 b) A'
      have hcomm' : Commute (L.ε i (suToSL (f := f) κ 2 a)) (L.ε i A') :=
        hε.symm ▸ hcomm
      refine (L.ε_inj i).eq_iff.mp ?_
      rw [map_mul, map_mul]
      exact hcomm'.eq
    have ha1 : a = 1 := suToSL_injective (f := f) κ 2 (by rw [hA1, map_one])
    rw [ha1, map_one]
  · rcases lt_or_gt_of_ne hij with hij' | hji'
    · have hAB : WeakCT.blk L.Fld 0 (suToSL (f := f) κ 2 a) =
          WeakCT.blk L.Fld 1 (suToSL (f := f) κ 2 b) := by
        apply (L.ε₂_inj i j hij' h3)
        rw [show L.ε₂ i j (WeakCT.blk L.Fld 0 (suToSL (f := f) κ 2 a)) =
            L.ε i (suToSL (f := f) κ 2 a) from
          DFunLike.congr_fun (L.ε₂_left i j hij' h3) (suToSL (f := f) κ 2 a),
          show L.ε₂ i j (WeakCT.blk L.Fld 1 (suToSL (f := f) κ 2 b)) =
            L.ε j (suToSL (f := f) κ 2 b) from
          DFunLike.congr_fun (L.ε₂_right i j hij' h3) (suToSL (f := f) κ 2 b)]
        exact hε
      obtain ⟨hA1, -⟩ := blk_zero_eq_blk_one hAB
      have ha1 : a = 1 := suToSL_injective (f := f) κ 2 (by rw [hA1, map_one])
      rw [ha1, map_one]
    · have h3' : coxeterMatrix D.isFiniteType j i = 3 :=
        (CoxeterMatrix.symmetric (coxeterMatrix D.isFiniteType) j i).trans h3
      have hAB : WeakCT.blk L.Fld 0 (suToSL (f := f) κ 2 b) =
          WeakCT.blk L.Fld 1 (suToSL (f := f) κ 2 a) := by
        apply (L.ε₂_inj j i hji' h3')
        rw [show L.ε₂ j i (WeakCT.blk L.Fld 0 (suToSL (f := f) κ 2 b)) =
            L.ε j (suToSL (f := f) κ 2 b) from
          DFunLike.congr_fun (L.ε₂_left j i hji' h3') (suToSL (f := f) κ 2 b),
          show L.ε₂ j i (WeakCT.blk L.Fld 1 (suToSL (f := f) κ 2 a)) =
            L.ε i (suToSL (f := f) κ 2 a) from
          DFunLike.congr_fun (L.ε₂_right j i hji' h3') (suToSL (f := f) κ 2 a)]
        exact hε.symm
      obtain ⟨hB1, -⟩ := blk_zero_eq_blk_one hAB
      have hA1 : suToSL (f := f) κ 2 a = 1 := by
        have h1 : L.ε i (suToSL (f := f) κ 2 a) = L.ε i 1 := by
          rw [hε, hB1]
          simp
        exact (L.ε_inj i) h1
      have ha1 : a = 1 := suToSL_injective (f := f) κ 2 (by rw [hA1, map_one])
      rw [ha1, map_one]

private theorem hmbGood_indep
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H) :
    iSupIndep fun i => ((stdFamily L hρ hρr κ hκ hext).nodeTor i).range := by
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff]
  apply (Subgroup.map_injective hρ)
  rw [Subgroup.map_inf _ _ ρ hρ, Subgroup.map_bot]
  simp_rw [Subgroup.map_iSup]
  have hmap : ∀ k, ((stdFamily L hρ hρr κ hκ hext).nodeTor k).range.map ρ =
      H k ⊓ stdFix F n₀ := fun k => map_range_nodeTor_stdFamily L hρ hρr κ hκ hext k
  simp_rw [hmap]
  refine le_antisymm ?_ bot_le
  have h1 : (H i ⊓ stdFix F n₀) ⊓ (⨆ j, ⨆ (_ : j ≠ i), H j ⊓ stdFix F n₀) ≤
      H i ⊓ (⨆ j, ⨆ (_ : j ≠ i), H j) :=
    inf_le_inf inf_le_left (iSup_le fun j => iSup_le fun hj =>
      (inf_le_left : H j ⊓ stdFix F n₀ ≤ H j).trans (le_iSup₂_of_le j hj le_rfl))
  have h2 : H i ⊓ (⨆ j, ⨆ (_ : j ≠ i), H j) = ⊥ :=
    disjoint_iff.mp ((iSupIndep_def.mp hext.torus_iSupIndep) i)
  exact h2 ▸ h1

private theorem hmbGood_torus_inf_ge (hext : SteinbergExtras D n H) (J : Set (Fin D.rank)) :
    (⨆ j ∈ J, ((stdFamily L hρ hρr κ hκ hext).nodeTor j).range) ≤
      (⨆ j ∈ J, ((stdFamily L hρ hρr κ hκ hext).ι j).range) ⊓
        (stdFamily L hρ hρr κ hκ hext).torus := by
  refine le_inf ?_ ?_
  · refine iSup_le fun j => iSup_le fun hj => ?_
    have hnode : ((stdFamily L hρ hρr κ hκ hext).nodeTor j).range ≤
        ((stdFamily L hρ hρr κ hκ hext).ι j).range := by
      rintro x ⟨u, rfl⟩
      exact ⟨torusTwo (unitaryInvolution Kf 2 f) u, rfl⟩
    exact hnode.trans (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  · refine iSup_le fun j => iSup_le fun hj => le_iSup_of_le j le_rfl

private theorem hmbGood_torus_inf_single
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (i : Fin D.rank) :
    ((stdFamily L hρ hρr κ hκ hext).ι i).range ⊓
      (stdFamily L hρ hρr κ hκ hext).torus =
      ((stdFamily L hρ hρr κ hκ hext).nodeTor i).range := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨⟨a, rfl⟩, hxT⟩
    have hyT : L.ε i (suToSL (f := f) κ 2 a) ∈ ⨆ k, H k := by
      have hxmap : ρ ((stdFamily L hρ hρr κ hκ hext).ι i a) ∈
          (stdFamily L hρ hρr κ hκ hext).torus.map ρ := ⟨_, hxT, rfl⟩
      rw [map_torus_stdFamily L hρ hρr κ hκ hext] at hxmap
      rw [hmbGood_rho_iota L hρ hρr κ hκ hext i a] at hxmap
      have hle : (⨆ k, H k ⊓ stdFix F n₀) ≤ (⨆ k, H k) := iSup_mono fun k => inf_le_left
      exact hle hxmap
    obtain ⟨s, hs⟩ := hmbGood_sl2_torus L hct
      (A := suToSL (f := f) κ 2 a) (y := L.ε i (suToSL (f := f) κ 2 a)) rfl hyT
    obtain ⟨u, hu, -⟩ := hmbGood_exists_torusTwo_of_suToSL_torusHom L κ hκ hs
    refine ⟨u, ?_⟩
    change (stdFamily L hρ hρr κ hκ hext).ι i (torusTwo (unitaryInvolution Kf 2 f) u) =
      (stdFamily L hρ hρr κ hκ hext).ι i a
    rw [hu]
  · refine le_inf ?_ ?_
    · rintro x ⟨u, rfl⟩
      exact ⟨torusTwo (unitaryInvolution Kf 2 f) u, rfl⟩
    · exact le_iSup (fun i => ((stdFamily L hρ hρr κ hκ hext).nodeTor i).range) i

private theorem hmbGood_torus_inf_pair
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hsl : ∀ i j : Fin D.rank, i ≠ j →
      coxeterMatrix D.isFiniteType i j = 2 ∨ coxeterMatrix D.isFiniteType i j = 3)
    (i j : Fin D.rank) (hij : i ≠ j) :
    (((stdFamily L hρ hρr κ hκ hext).ι i).range ⊔
      ((stdFamily L hρ hρr κ hκ hext).ι j).range) ⊓
      (stdFamily L hρ hρr κ hκ hext).torus =
    ((stdFamily L hρ hρr κ hκ hext).nodeTor i).range ⊔
      ((stdFamily L hρ hρr κ hκ hext).nodeTor j).range := by
  refine le_antisymm ?_ (le_inf (sup_le ?_ ?_) (sup_le ?_ ?_))
  · intro x hx
    obtain ⟨hxL, hxT⟩ := Subgroup.mem_inf.1 hx
    have hyT : ρ x ∈ ⨆ k, H k := by
      have hxmap : ρ x ∈ (stdFamily L hρ hρr κ hκ hext).torus.map ρ := ⟨x, hxT, rfl⟩
      rw [map_torus_stdFamily L hρ hρr κ hκ hext] at hxmap
      have hle : (⨆ k, H k ⊓ stdFix F n₀) ≤ (⨆ k, H k) := iSup_mono fun k => inf_le_left
      exact hle hxmap
    rcases hsl i j hij with h2 | h3
    · have h2' : coxeterMatrix D.isFiniteType j i = 2 :=
        (CoxeterMatrix.symmetric (coxeterMatrix D.isFiniteType) j i).trans h2
      have hcomm : ∀ a ∈ ((stdFamily L hρ hρr κ hκ hext).ι i).range,
          ∀ b ∈ ((stdFamily L hρ hρr κ hκ hext).ι j).range, Commute a b := by
        rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
        have : ρ ((stdFamily L hρ hρr κ hκ hext).ι i A *
            (stdFamily L hρ hρr κ hκ hext).ι j B) =
            ρ ((stdFamily L hρ hρr κ hκ hext).ι j B *
              (stdFamily L hρ hρr κ hκ hext).ι i A) := by
          rw [map_mul, map_mul, hmbGood_rho_iota L hρ hρr κ hκ hext i A,
            hmbGood_rho_iota L hρ hρr κ hκ hext j B]
          exact (L.ε_commute hext h2' (suToSL (f := f) κ 2 B)
            (suToSL (f := f) κ 2 A)).eq.symm
        exact hρ this
      have hle : ((stdFamily L hρ hρr κ hκ hext).ι i).range ≤
          Subgroup.normalizer (((stdFamily L hρ hρr κ hκ hext).ι j).range : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        intro a ha b hb
        rw [show a * b * a⁻¹ = b by rw [(hcomm a ha b hb).eq]; group]
        exact hb
      change x ∈ (↑(((stdFamily L hρ hρr κ hκ hext).ι i).range ⊔
        ((stdFamily L hρ hρr κ hκ hext).ι j).range) : Set G) at hxL
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hxL
      obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.1 hxL
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨b, rfl⟩ := hz
      have hyT' : L.ε i (suToSL (f := f) κ 2 a) * L.ε j (suToSL (f := f) κ 2 b) ∈
          ⨆ k, H k := by
        have heq : ρ x = L.ε i (suToSL (f := f) κ 2 a) * L.ε j (suToSL (f := f) κ 2 b) := by
          rw [← hyz, map_mul, hmbGood_rho_iota L hρ hρr κ hκ hext i a,
            hmbGood_rho_iota L hρ hρr κ hκ hext j b]
        rwa [← heq]
      obtain ⟨⟨s, hs⟩, t, ht⟩ := hmbGood_sl2_torus_prod L κ hct hext h2 rfl hyT'
      obtain ⟨u, hu, hκu⟩ := hmbGood_exists_torusTwo_of_suToSL_torusHom L κ hκ hs
      obtain ⟨v, hv, hκv⟩ := hmbGood_exists_torusTwo_of_suToSL_torusHom L κ hκ ht
      have hxeq : x = (stdFamily L hρ hρr κ hκ hext).ι i
          (torusTwo (unitaryInvolution Kf 2 f) u) *
          (stdFamily L hρ hρr κ hκ hext).ι j
            (torusTwo (unitaryInvolution Kf 2 f) v) := by
        have h1 : ρ ((stdFamily L hρ hρr κ hκ hext).ι i
              (torusTwo (unitaryInvolution Kf 2 f) u) *
              (stdFamily L hρ hρr κ hκ hext).ι j
                (torusTwo (unitaryInvolution Kf 2 f) v)) =
            L.ε i (WeakCT.torusHom L.Fld s) * L.ε j (WeakCT.torusHom L.Fld t) := by
          rw [map_mul, hmbGood_rho_iota L hρ hρr κ hκ hext i _,
            hmbGood_rho_iota L hρ hρr κ hκ hext j _,
            hmbGood_suToSL_torusTwo, hmbGood_suToSL_torusTwo]
          rw [show Units.map κ.toMonoidHom ((u : normOne (unitaryInvolution Kf 2 f)) : Kfˣ) =
              s from Units.ext hκu,
            show Units.map κ.toMonoidHom ((v : normOne (unitaryInvolution Kf 2 f)) : Kfˣ) =
              t from Units.ext hκv]
        apply hρ
        rw [h1, ← hyz, map_mul, hmbGood_rho_iota L hρ hρr κ hκ hext i a,
          hmbGood_rho_iota L hρ hρr κ hκ hext j b, hs, ht]
      rw [hxeq]
      exact Subgroup.mul_mem_sup ⟨u, rfl⟩ ⟨v, rfl⟩
    · rcases lt_or_gt_of_ne hij with hij' | hji'
      · have hsub : ((stdFamily L hρ hρr κ hκ hext).ι i).range ⊔
            ((stdFamily L hρ hρr κ hκ hext).ι j).range ≤
            ((stdFamily L hρ hρr κ hκ hext).θ i j).range := by
          apply sup_le
          · rintro _ ⟨A, rfl⟩
            exact ⟨embSUid (unitaryInvolution Kf 2 f) 2 A,
              DFunLike.congr_fun (stdTheta_left L hρ hρr κ hκ hij' h3) A⟩
          · rintro _ ⟨A, rfl⟩
            exact ⟨embSUid (unitaryInvolution Kf 2 f) 0 A,
              DFunLike.congr_fun (stdTheta_right L hρ hρr κ hκ hij' h3) A⟩
        obtain ⟨a, rfl⟩ := hsub hxL
        have hyT' : L.ε₂ i j (suToSL (f := f) κ 3 a) ∈ ⨆ k, H k := by
          have heq : ρ ((stdFamily L hρ hρr κ hκ hext).θ i j a) =
              L.ε₂ i j (suToSL (f := f) κ 3 a) :=
            hmbGood_rho_theta L hρ hρr κ hκ hext hij' h3 a
          rwa [heq] at hyT
        obtain ⟨s, t, hst⟩ := hmbGood_sl3_torus L hct hij' h3
          (A := suToSL (f := f) κ 3 a) (y := L.ε₂ i j (suToSL (f := f) κ 3 a)) rfl hyT'
        have hAfix : suToSL (f := f) κ 3 a ∈ slSU L.θ 3 :=
          (range_suToSL L.θ κ hκ 3) ▸ ⟨a, rfl⟩
        rw [hst] at hAfix
        obtain ⟨hsθ, htθ⟩ := hmbGood_blk_torus_mem_slSU L hAfix
        have hu : Units.map κ.symm.toMonoidHom s ∈ normOne (unitaryInvolution Kf 2 f) :=
          hmbGood_normOne_units_map_symm L κ hκ hsθ
        have hv : Units.map κ.symm.toMonoidHom t ∈ normOne (unitaryInvolution Kf 2 f) :=
          hmbGood_normOne_units_map_symm L κ hκ htθ
        have hxeq : (stdFamily L hρ hρr κ hκ hext).θ i j a =
            (stdFamily L hρ hρr κ hκ hext).ι i
              (torusTwo (unitaryInvolution Kf 2 f) ⟨_, hu⟩) *
            (stdFamily L hρ hρr κ hκ hext).ι j
              (torusTwo (unitaryInvolution Kf 2 f) ⟨_, hv⟩) := by
          have h1 : ρ ((stdFamily L hρ hρr κ hκ hext).ι i
                (torusTwo (unitaryInvolution Kf 2 f) ⟨_, hu⟩) *
                (stdFamily L hρ hρr κ hκ hext).ι j
                  (torusTwo (unitaryInvolution Kf 2 f) ⟨_, hv⟩)) =
              L.ε i (WeakCT.torusHom L.Fld s) * L.ε j (WeakCT.torusHom L.Fld t) := by
            rw [map_mul, hmbGood_rho_iota L hρ hρr κ hκ hext i _,
              hmbGood_rho_iota L hρ hρr κ hκ hext j _,
              hmbGood_suToSL_torusTwo, hmbGood_suToSL_torusTwo]
            rw [hmbGood_units_map_symm L κ s, hmbGood_units_map_symm L κ t]
          have h2 : ρ ((stdFamily L hρ hρr κ hκ hext).θ i j a) =
              L.ε i (WeakCT.torusHom L.Fld s) * L.ε j (WeakCT.torusHom L.Fld t) := by
            rw [hmbGood_rho_theta L hρ hρr κ hκ hext hij' h3 a, hst, map_mul,
              show L.ε₂ i j (WeakCT.blk L.Fld 0 (WeakCT.torusHom L.Fld s)) =
                L.ε i (WeakCT.torusHom L.Fld s) from
                DFunLike.congr_fun (L.ε₂_left i j hij' h3) (WeakCT.torusHom L.Fld s),
              show L.ε₂ i j (WeakCT.blk L.Fld 1 (WeakCT.torusHom L.Fld t)) =
                L.ε j (WeakCT.torusHom L.Fld t) from
                DFunLike.congr_fun (L.ε₂_right i j hij' h3) (WeakCT.torusHom L.Fld t)]
          exact (hρ (h1.trans h2.symm)).symm
        rw [hxeq]
        exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
      · have h3' : coxeterMatrix D.isFiniteType j i = 3 :=
          (CoxeterMatrix.symmetric (coxeterMatrix D.isFiniteType) j i).trans h3
        have hsub : ((stdFamily L hρ hρr κ hκ hext).ι i).range ⊔
            ((stdFamily L hρ hρr κ hκ hext).ι j).range ≤
            ((stdFamily L hρ hρr κ hκ hext).θ j i).range := by
          rw [sup_comm]
          apply sup_le
          · rintro _ ⟨A, rfl⟩
            exact ⟨embSUid (unitaryInvolution Kf 2 f) 2 A,
              DFunLike.congr_fun (stdTheta_left L hρ hρr κ hκ hji' h3') A⟩
          · rintro _ ⟨A, rfl⟩
            exact ⟨embSUid (unitaryInvolution Kf 2 f) 0 A,
              DFunLike.congr_fun (stdTheta_right L hρ hρr κ hκ hji' h3') A⟩
        obtain ⟨a, rfl⟩ := hsub hxL
        have hyT' : L.ε₂ j i (suToSL (f := f) κ 3 a) ∈ ⨆ k, H k := by
          have heq : ρ ((stdFamily L hρ hρr κ hκ hext).θ j i a) =
              L.ε₂ j i (suToSL (f := f) κ 3 a) :=
            hmbGood_rho_theta L hρ hρr κ hκ hext hji' h3' a
          rwa [heq] at hyT
        obtain ⟨s, t, hst⟩ := hmbGood_sl3_torus L hct hji' h3'
          (A := suToSL (f := f) κ 3 a) (y := L.ε₂ j i (suToSL (f := f) κ 3 a)) rfl hyT'
        have hAfix : suToSL (f := f) κ 3 a ∈ slSU L.θ 3 :=
          (range_suToSL L.θ κ hκ 3) ▸ ⟨a, rfl⟩
        rw [hst] at hAfix
        obtain ⟨hsθ, htθ⟩ := hmbGood_blk_torus_mem_slSU L hAfix
        have hu : Units.map κ.symm.toMonoidHom s ∈ normOne (unitaryInvolution Kf 2 f) :=
          hmbGood_normOne_units_map_symm L κ hκ hsθ
        have hv : Units.map κ.symm.toMonoidHom t ∈ normOne (unitaryInvolution Kf 2 f) :=
          hmbGood_normOne_units_map_symm L κ hκ htθ
        have hxeq : (stdFamily L hρ hρr κ hκ hext).θ j i a =
            (stdFamily L hρ hρr κ hκ hext).ι j
              (torusTwo (unitaryInvolution Kf 2 f) ⟨_, hu⟩) *
            (stdFamily L hρ hρr κ hκ hext).ι i
              (torusTwo (unitaryInvolution Kf 2 f) ⟨_, hv⟩) := by
          have h1 : ρ ((stdFamily L hρ hρr κ hκ hext).ι j
                (torusTwo (unitaryInvolution Kf 2 f) ⟨_, hu⟩) *
                (stdFamily L hρ hρr κ hκ hext).ι i
                  (torusTwo (unitaryInvolution Kf 2 f) ⟨_, hv⟩)) =
              L.ε j (WeakCT.torusHom L.Fld s) * L.ε i (WeakCT.torusHom L.Fld t) := by
            rw [map_mul, hmbGood_rho_iota L hρ hρr κ hκ hext j _,
              hmbGood_rho_iota L hρ hρr κ hκ hext i _,
              hmbGood_suToSL_torusTwo, hmbGood_suToSL_torusTwo]
            rw [hmbGood_units_map_symm L κ s, hmbGood_units_map_symm L κ t]
          have h2 : ρ ((stdFamily L hρ hρr κ hκ hext).θ j i a) =
              L.ε j (WeakCT.torusHom L.Fld s) * L.ε i (WeakCT.torusHom L.Fld t) := by
            rw [hmbGood_rho_theta L hρ hρr κ hκ hext hji' h3' a, hst, map_mul,
              show L.ε₂ j i (WeakCT.blk L.Fld 0 (WeakCT.torusHom L.Fld s)) =
                L.ε j (WeakCT.torusHom L.Fld s) from
                DFunLike.congr_fun (L.ε₂_left j i hji' h3') (WeakCT.torusHom L.Fld s),
              show L.ε₂ j i (WeakCT.blk L.Fld 1 (WeakCT.torusHom L.Fld t)) =
                L.ε i (WeakCT.torusHom L.Fld t) from
                DFunLike.congr_fun (L.ε₂_right j i hji' h3') (WeakCT.torusHom L.Fld t)]
          exact (hρ (h1.trans h2.symm)).symm
        rw [hxeq, sup_comm]
        exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · rintro x ⟨u, rfl⟩
    exact Subgroup.mem_sup_left (show (stdFamily L hρ hρr κ hκ hext).ι i
      (torusTwo (unitaryInvolution Kf 2 f) u) ∈
      ((stdFamily L hρ hρr κ hκ hext).ι i).range from ⟨_, rfl⟩)
  · rintro x ⟨u, rfl⟩
    exact Subgroup.mem_sup_right (show (stdFamily L hρ hρr κ hκ hext).ι j
      (torusTwo (unitaryInvolution Kf 2 f) u) ∈
      ((stdFamily L hρ hρr κ hκ hext).ι j).range from ⟨_, rfl⟩)
  · exact le_iSup (fun i => ((stdFamily L hρ hρr κ hκ hext).nodeTor i).range) i
  · exact le_iSup (fun i => ((stdFamily L hρ hρr κ hκ hext).nodeTor i).range) j

private theorem hmbGood_torus_inf
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hsl : ∀ i j : Fin D.rank, i ≠ j →
      coxeterMatrix D.isFiniteType i j = 2 ∨ coxeterMatrix D.isFiniteType i j = 3)
    (J : Set (Fin D.rank)) (hJ : J.encard ≤ 2) :
    (⨆ j ∈ J, ((stdFamily L hρ hρr κ hκ hext).ι j).range) ⊓
      (stdFamily L hρ hρr κ hκ hext).torus =
    ⨆ j ∈ J, ((stdFamily L hρ hρr κ hκ hext).nodeTor j).range := by
  refine le_antisymm ?_ (hmbGood_torus_inf_ge L hρ hρr κ hκ hext J)
  rcases J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp
  · have hle1 : (J \ {i}).encard ≤ 1 := by
      have h := Set.encard_sdiff_singleton_add_one hi
      have h2 : (J \ {i}).encard + 1 ≤ 1 + 1 := by
        rw [h]
        simpa only [one_add_one_eq_two] using hJ
      exact (ENat.add_le_add_iff_right (by norm_num : (1 : ENat) ≠ ⊤)).mp h2
    rcases Set.encard_le_one_iff_eq.1 hle1 with h0 | ⟨j, hj⟩
    · have hJeq : J = {i} := by
        apply Set.Subset.antisymm
        · intro x hx
          by_contra hxi
          have hmem : x ∈ J \ {i} := ⟨hx, hxi⟩
          rw [h0] at hmem
          exact hmem
        · intro x hx
          rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact hi
      subst hJeq
      simp only [iSup_singleton]
      rw [hmbGood_torus_inf_single L hρ hρr κ hκ hct hext i]
    · have hjmem : j ∈ J \ {i} := by rw [hj]; exact Set.mem_singleton j
      have hji : j ≠ i := hjmem.2
      have hJeq : J = {i, j} := by
        apply Set.Subset.antisymm
        · intro x hx
          rcases eq_or_ne x i with hxi | hxi
          · rw [hxi]
            exact Set.mem_insert i {j}
          · have hx' : x ∈ J \ {i} := ⟨hx, hxi⟩
            rw [hj] at hx'
            rw [Set.mem_singleton_iff] at hx'
            rw [hx']
            exact Set.mem_insert_of_mem i rfl
        · intro x hx
          rcases hx with rfl | rfl
          · exact hi
          · exact hjmem.1
      subst hJeq
      simp only [iSup_insert, iSup_singleton]
      rw [hmbGood_torus_inf_pair L hρ hρr κ hκ hct hext hsl i j (Ne.symm hji)]

theorem stdFamily_good (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hsl : ∀ i j : Fin D.rank, i ≠ j →
      coxeterMatrix D.isFiniteType i j = 2 ∨ coxeterMatrix D.isFiniteType i j = 3) :
    (stdFamily L hρ hρr κ hκ hext).Good :=
  ⟨hsl, fun i => hmbGood_iota_inj L hρ hρr κ hκ hext i,
    fun i j hij => hmbGood_disj L hρ hρr κ hκ hext hsl i j hij,
    fun i j hij h3 => hmbGood_theta_inj L hρ hρr κ hκ hext hij h3,
    hmbGood_indep L hρ hρr κ hκ hct hext,
    fun J hJ => hmbGood_torus_inf L hρ hρr κ hκ hct hext hsl J hJ⟩

end CFSG.ClassicalInvolution.Phan.PhanE
