module

public import CFSG.RankThree.CentralLift.CrossSymplectic
public import CFSG.RankThree.CentralLiftSO.SplitTriangular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryRootGen
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasThree

public section

namespace CFSG.RankThree.CentralLift

open Matrix CFSG.LieType.CentralExt CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup orthogonal_elementary_perfect)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (liftTorus simpleLift hSimple
  hSimple_mem roots posRoots eps rootSubgroup unipotent weylGroup signedPermAut signedPermAut_eps
  rootSubgroup_le_unipotent flag mem_flag_iff_coord posBorel mem_posBorel posUnip_le_posBorel
  unipotent_eq_posUnip sqTorus rootSupr orthogonal_geometry_split_root_generation coordWt
  coordWt_inl finrank_flag quadPlus_eq_zero_of_mem_flag)
open CFSG.RankThree.CentralLiftSO.SplitO (LargeHyp liftUnip liftUnipExcept liftBorel xPlus xMinus
  sLift liftWeyl sLift_sq_mem normal_liftTorus_subgroupOf weylHom ker_weylHom
  apply_single_weylHom weylHom_surjective map_conj_rootSubgroup_weylHom sqTorus_le_posBorel
  xPlus_mem_liftUnip
  odd_split_orthogonal_cross_characteristic_central_prime_triangular_factorization)
open CFSG.LieType.Chevalley (uSL vSL)
open scoped Pointwise

variable {r : ℕ} {k : Type} [Field k] [Finite k] {E : Type*} [Group E] [Finite E]
  {π : E →* orthElementaryGroup (quadPlus r k)}

theorem weylHom_eq_one_of_mem_posBorel (hS : LargeHyp π) (hr : 2 ≤ r) (v : liftWeyl π)
    (hv : ((π v : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ posBorel r k) :
    weylHom hS hr v = 1 := by
  obtain ⟨-, hflag⟩ := mem_posBorel.1 hv
  have key : ∀ j : Fin r, ∃ m : Fin r, m ≤ j ∧
      ((weylHom hS hr v : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (eps r j) = eps r m := by
    intro j
    obtain ⟨μ, c', hgc, hc'⟩ := apply_single_weylHom hS hr v (Sum.inl j)
    have hmem : ((π v : orthElementaryGroup (quadPlus r k)) :
        (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) (Pi.single (Sum.inl j) 1) ∈
        flag r k (j + 1) := by
      rw [← hflag (j + 1)]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩)
    rw [hgc, mem_flag_iff_coord] at hmem
    rcases c' with m | m
    · refine ⟨m, ?_, ?_⟩
      · by_contra hlt
        have h0 := hmem.2 m (by rw [Fin.not_le] at hlt; exact hlt)
        simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h0
        exact μ.ne_zero h0
      · rw [← coordWt_inl, ← hc', coordWt_inl]
    · exfalso
      have h0 := hmem.1 m
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h0
      exact μ.ne_zero h0
  choose m hm hmw using key
  have hinj : Function.Injective m := by
    intro a b hab
    have h1 : ((weylHom hS hr v : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (eps r a) =
        ((weylHom hS hr v : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (eps r b) := by
      rw [hmw, hmw, hab]
    have h2 := ((weylHom hS hr v : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)).injective h1
    have h3 := congrFun h2 a
    simp only [eps, Pi.single_eq_same] at h3
    by_contra hne
    rw [Pi.single_eq_of_ne hne] at h3
    exact one_ne_zero h3
  have hbij : Function.Bijective m := Finite.injective_iff_bijective.1 hinj
  have hperm : Equiv.ofBijective m hbij = 1 :=
    LinearRoots.perm_eq_one_of_forall_le fun a => hm a
  have hmid : ∀ j, m j = j := fun j => by
    have := congrArg (fun τ : Equiv.Perm (Fin r) => τ j) hperm
    simpa using this
  refine Subtype.ext ?_
  change ((weylHom hS hr v : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) =
    LinearEquiv.refl ℤ (Fin r → ℤ)
  refine (Pi.basisFun ℤ (Fin r)).ext' fun j => ?_
  rw [Pi.basisFun_apply, LinearEquiv.refl_apply]
  change ((weylHom hS hr v : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (eps r j) = eps r j
  rw [hmw, hmid]

theorem exists_weylGroup_neg {β : Fin r → ℤ} (hβ : β ∈ posRoots r) :
    ∃ w ∈ weylGroup r, w β = -β := by
  obtain ⟨i, j, hij, hβ⟩ := hβ
  rcases hβ with rfl | rfl
  · refine ⟨signedPermAut r (Equiv.swap i j) 1, ⟨Equiv.swap i j, 1, by simp, rfl⟩, ?_⟩
    rw [map_sub, signedPermAut_eps, signedPermAut_eps, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    simp
  · set δ : Fin r → ℤˣ := Pi.mulSingle i (-1) * Pi.mulSingle j (-1) with hδ
    have hδi : δ i = -1 := by
      rw [hδ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.ne, mul_one]
    have hδj : δ j = -1 := by
      rw [hδ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.ne', one_mul]
    refine ⟨signedPermAut r 1 δ, ⟨1, δ, ?_, rfl⟩, ?_⟩
    · rw [hδ]
      simp only [Pi.mul_apply]
      rw [Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle']
      simp
    · rw [map_add, signedPermAut_eps, signedPermAut_eps, hδi, hδj]
      simp only [Equiv.Perm.one_apply, Units.val_neg, Units.val_one, neg_smul, one_smul]
      abel

theorem sup_map_eq_top_split (hS : LargeHyp π) (hr : 3 ≤ r) {B : Subgroup E}
    (hU : ∀ u ∈ unipotent r k, ∃ b ∈ B, ((π b : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) = u) :
    B.map π ⊔ (liftWeyl π).map π = ⊤ := by
  have hr2 : 2 ≤ r := by omega
  set T := B.map π ⊔ (liftWeyl π).map π with hT
  set T' := T.map (orthElementaryGroup (quadPlus r k)).subtype with hT'
  have hBT : ∀ b ∈ B, ((π b : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ T' := fun b hb =>
    ⟨π b, Subgroup.mem_sup_left ⟨b, hb, rfl⟩, rfl⟩
  have hNT : ∀ v ∈ liftWeyl π, ((π v : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ T' := fun v hv =>
    ⟨π v, Subgroup.mem_sup_right ⟨v, hv, rfl⟩, rfl⟩
  have hpos : ∀ β ∈ posRoots r, rootSubgroup r k β ≤ T' := fun β hβ x hx => by
    obtain ⟨b, hb, rfl⟩ := hU x (rootSubgroup_le_unipotent hβ hx)
    exact hBT b hb
  have hroot : ∀ α ∈ roots r, rootSubgroup r k α ≤ T' := by
    intro α hα
    by_cases hαp : α ∈ posRoots r
    · exact hpos α hαp
    · have hnα : -α ∈ posRoots r := by
        obtain ⟨i, j, hij, h⟩ := hα
        rcases h with rfl | rfl | rfl | rfl
        · exact absurd ⟨i, j, hij, Or.inl rfl⟩ hαp
        · exact ⟨i, j, hij, Or.inl (by abel)⟩
        · exact absurd ⟨i, j, hij, Or.inr rfl⟩ hαp
        · exact ⟨i, j, hij, Or.inr (by abel)⟩
      obtain ⟨w, hw, hwα⟩ := exists_weylGroup_neg hnα
      obtain ⟨v, hv⟩ := weylHom_surjective hS hr2 hr ⟨w, hw⟩
      have hmap := map_conj_rootSubgroup_weylHom hS hr2 v
        (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.posRoots_subset_roots hnα)
      rw [hv] at hmap
      change _ = rootSubgroup r k (w (-α)) at hmap
      rw [hwα, neg_neg] at hmap
      rw [← hmap]
      rintro _ ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem (hNT v v.2) (hpos _ hnα hy)) (inv_mem (hNT v v.2))
  have hsup : rootSupr r k ≤ T' := iSup₂_le hroot
  rw [eq_top_iff]
  intro g _
  have hg : ((g : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ rootSupr r k := by
    rw [← (orthogonal_geometry_split_root_generation (K := k) hr).1]
    exact g.2
  obtain ⟨t, ht, hteq⟩ := hsup hg
  rwa [Subtype.ext hteq] at ht

omit [Finite k] in
theorem isPerfect_orthElementaryGroup_quadPlus (hr : 3 ≤ r) :
    Group.IsPerfect (orthElementaryGroup (quadPlus r k)) :=
  (orthogonal_elementary_perfect (nondegenerate_polarBilin_quadPlus r k)
    ⟨flag r k 3, finrank_flag hr, fun _ hx => quadPlus_eq_zero_of_mem_flag hx⟩).1

theorem split_orthogonal_cross_splitting {p ℓ f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hpℓ : p ≠ ℓ) (_hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f) (hr : 3 ≤ r)
    (π : E →* orthElementaryGroup (quadPlus r k)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    (∃! s : orthElementaryGroup (quadPlus r k) →* E, π.comp s = MonoidHom.id _) ∧
      ∀ s : orthElementaryGroup (quadPlus r k) →* E, π.comp s = MonoidHom.id _ →
        ∃ e : π.ker × s.range ≃* E, ∀ c g, e (c, g) = (c : E) * g := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP k ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hk])
  have hchar : ringChar k = ℓ := ringChar.eq k ℓ
  have hk2 : ringChar k ≠ 2 := by
    rw [hchar]
    exact hℓodd.ne_two_of_dvd_nat (dvd_refl ℓ)
  have : Fact (ringChar k).Prime := ⟨hchar ▸ hℓ⟩
  have hpℓ' : p ≠ ringChar k := hchar ▸ hpℓ
  have hr2 : 2 ≤ r := by omega
  have hS : LargeHyp π := ⟨hk2, ⟨hπ, hC, ⟨p, hp, hp3, hCp⟩⟩⟩
  obtain ⟨-, -, hBset, hBmap, -, -, -, hBinj, -, -, hsimple⟩ :=
    odd_split_orthogonal_cross_characteristic_central_prime_triangular_factorization hk2 hr hp
      hp3 hpℓ' hπ hC hCp
  let Xp : Fin r → Subgroup E := fun i => ((simpleLift π i).comp LinearRoots.uSLHom).range
  let Xm : Fin r → Subgroup E := fun i => ((simpleLift π i).comp vSLHom).range
  have hmemXp : ∀ i x, x ∈ Xp i ↔ ∃ t : k, xPlus π i t = x := fun i x =>
    ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
  have hmemXm : ∀ i x, x ∈ Xm i ↔ ∃ t : k, xMinus π i t = x := fun i x =>
    ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
  have hInj : Set.InjOn π (liftBorel π : Set E) := fun x hx y hy hxy =>
    congrArg Subtype.val (hBinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hfact : ∀ i, (liftBorel π : Set E) =
      (Xp i : Set E) * (liftUnipExcept π i : Set E) * (liftTorus π : Set E) := by
    intro i
    ext x
    rw [SetLike.mem_coe, ((hsimple i).2.2.2.1) x]
    constructor
    · rintro ⟨t, u, hu, h, hh, rfl⟩
      exact ⟨_, ⟨_, (hmemXp i _).2 ⟨t, rfl⟩, u, hu, rfl⟩, h, hh, rfl⟩
    · rintro ⟨_, ⟨y, hy, u, hu, rfl⟩, h, hh, rfl⟩
      obtain ⟨t, rfl⟩ := (hmemXp i y).1 hy
      exact ⟨t, u, hu, h, hh, rfl⟩
  have hXpU : ∀ i, Xp i ≤ liftUnip π := fun i x hx => by
    obtain ⟨t, rfl⟩ := (hmemXp i x).1 hx
    exact xPlus_mem_liftUnip hS hr2 i t
  have hrew : ∀ i, ∀ x ∈ Xp i, x ≠ 1 → x * sLift π i ∈
      (Xm i : Set E) * (liftTorus π : Set E) * (Xp i : Set E) := by
    intro i x hx hx1
    obtain ⟨t, rfl⟩ := (hmemXp i x).1 hx
    have ht : t ≠ 0 := by
      rintro rfl
      apply hx1
      change simpleLift π i (uSL 0) = 1
      rw [LinearRoots.uSL_zero, map_one]
    rw [(hsimple i).2.2.2.2.2.1 t ht]
    exact ⟨_, ⟨_, (hmemXm i _).2 ⟨t⁻¹, rfl⟩, _, hSimple_mem i _, rfl⟩, _,
      (hmemXp i _).2 ⟨-t⁻¹, rfl⟩, rfl⟩
  have hsign : ∀ n ∈ liftWeyl π, ∀ i, (∀ x ∈ Xp i, n * x * n⁻¹ ∈ liftUnip π) ∨
      (∀ y ∈ Xm i, n * y * n⁻¹ ∈ liftUnip π) := by
    intro n hn i
    rcases (hsimple i).2.2.2.2.2.2 n hn with h | h
    · left
      intro x hx
      obtain ⟨t, rfl⟩ := (hmemXp i x).1 hx
      exact h t
    · right
      intro y hy
      obtain ⟨t, rfl⟩ := (hmemXm i y).1 hy
      exact h t
  have hBpos : ∀ b ∈ liftBorel π, ((π b : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ posBorel r k := by
    intro b hb
    have hb' : ((π b : orthElementaryGroup (quadPlus r k)) :
        (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈
        ((liftBorel π).map ((orthElementaryGroup (quadPlus r k)).subtype.comp π) :
          Set ((Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k))) := ⟨b, hb, rfl⟩
    rw [hBmap] at hb'
    obtain ⟨u, hu, t, ht, hut⟩ := hb'
    rw [← hut]
    refine mul_mem (posUnip_le_posBorel ?_) (sqTorus_le_posBorel ht)
    rw [← unipotent_eq_posUnip]
    exact hu
  have hBN : ∀ n ∈ liftWeyl π, π n ∈ (liftBorel π).map π → n ∈ liftTorus π := by
    intro n hn hnB
    obtain ⟨b, hb, hbn⟩ := hnB
    have h1 := weylHom_eq_one_of_mem_posBorel hS hr2 ⟨n, hn⟩ (by
      change ((π n : orthElementaryGroup (quadPlus r k)) :
        (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ posBorel r k
      rw [← hbn]
      exact hBpos b hb)
    have h2 : (⟨n, hn⟩ : liftWeyl π) ∈ (weylHom hS hr2).ker := h1
    rw [ker_weylHom hS hr2] at h2
    exact Subgroup.mem_subgroupOf.1 h2
  have hU : ∀ u ∈ unipotent r k, ∃ b ∈ liftBorel π, ((π b : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) = u := by
    intro u hu
    have hu' : u ∈ ((liftBorel π).map ((orthElementaryGroup (quadPlus r k)).subtype.comp π) :
        Set ((Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k))) := by
      rw [hBmap]
      exact ⟨u, hu, 1, one_mem _, mul_one u⟩
    obtain ⟨b, hb, hbu⟩ := hu'
    exact ⟨b, hb, hbu⟩
  obtain ⟨-, -, σ, hσ⟩ :=
    CFSG.RankThree.CentralExtension.central_extension_faithful_bruhat_lift_splitting π hC hBset
      hInj (normal_liftTorus_subgroupOf hS hr2) (sLift π) rfl (fun i => sLift_sq_mem i) Xp Xm
      (liftUnipExcept π) hXpU hfact (fun i => (hsimple i).2.2.2.2.1) hrew hsign hBN
      (sup_map_eq_top_split hS hr hU)
  have : Group.IsPerfect (orthElementaryGroup (quadPlus r k)) :=
    isPerfect_orthElementaryGroup_quadPlus hr
  refine ⟨⟨σ, hσ, fun σ' hσ' => section_eq_of_forall π hC (fun δ hδ =>
    eq_one_of_isPerfect_of_mem_center δ fun x => hC (hδ x)) hσ' hσ⟩,
    fun s hs => LinearRoots.exists_mulEquiv_prod_of_section hC hs⟩

end CFSG.RankThree.CentralLift
