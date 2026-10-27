module

public import CFSG.RankThree.PartOne.KD4T.InjBasic
public import CFSG.RankThree.PartOne.KD4T.InjSign
public import CFSG.RankThree.Chevalley.SteinbergBID4Kernel

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open scoped Pointwise

@[expose] def d4Set (τ : Tag) : Set (Fin τ.rank) := {i | 1 ≤ i.val ∧ i.val ≤ 4}

theorem lt_six_of_mem_d4Set {τ : Tag} {i : Fin τ.rank} (hi : i ∈ d4Set τ) :
    i.val < Tag.E6.rank := by
  have h := hi.2
  change i.val < 6
  omega

theorem one_le_val_iff : ∀ k : Fin Tag.E6.rank, (1 ≤ k.val ∧ k.val ≤ 4) ↔ (k ≠ 0 ∧ k ≠ 5) := by
  decide

section Support

variable {τ : Tag} [hτ : E6Sub τ]

theorem e6Idx_mem_d4Set_iff (k : Fin Tag.E6.rank) :
    e6Idx (τ := τ) k ∈ d4Set τ ↔ k ∈ d4Support :=
  one_le_val_iff k

theorem height_e6Lat (β : Fin Tag.E6.rank → ℤ) : height (e6Lat τ β) = height β := by
  rw [height, height, sum_eq_sum_e6Idx _ (fun i hi => e6Lat_apply_of_le hi)]
  exact Finset.sum_congr rfl fun k _ => e6Lat_apply_e6Idx β k

end Support

section Roots

variable {τ : Tag} [hτ : E6Sub τ]

theorem mem_parabolicRoots_d4Set_iff {γ : Fin τ.rank → ℤ} :
    γ ∈ parabolicRoots τ (d4Set τ) ↔ ∃ γ' ∈ parabolicRoots Tag.E6 d4Support, e6Lat τ γ' = γ := by
  constructor
  · rintro ⟨hγ, hz⟩
    have h6 : ∀ i : Fin τ.rank, Tag.E6.rank ≤ i.val → γ i = 0 := fun i hi =>
      hz i (fun hmem => by have := hmem.2; change 6 ≤ i.val at hi; omega)
    have hlat : e6Lat τ (fun k => γ (e6Idx k)) = γ := e6Lat_comp_e6Idx h6
    refine ⟨fun k => γ (e6Idx k), ⟨isRoot_e6Lat_iff.1 (hlat ▸ hγ), fun k hk => ?_⟩, hlat⟩
    exact hz _ (fun hmem => hk ((e6Idx_mem_d4Set_iff k).1 hmem))
  · rintro ⟨γ', ⟨hγ', hz'⟩, rfl⟩
    refine ⟨isRoot_e6Lat_iff.2 hγ', fun i hi => ?_⟩
    by_cases h : i.val < Tag.E6.rank
    · obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) h
      rw [e6Lat_apply_e6Idx]
      exact hz' k (fun hk => hi ((e6Idx_mem_d4Set_iff k).2 hk))
    · exact e6Lat_apply_of_le (not_lt.1 h)

theorem range_e6Lat_d4Lat_d4PosRoot :
    Set.range (fun k => e6Lat τ (d4Lat (d4PosRoot k))) = parabolicPosRoots τ (d4Set τ) := by
  ext γ
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨hΦ, hroot, hpos⟩ : d4Lat (d4PosRoot k) ∈ parabolicPosRoots Tag.E6 d4Support :=
      range_d4Lat_d4PosRoot ▸ Set.mem_range_self k
    exact ⟨mem_parabolicRoots_d4Set_iff.2 ⟨_, hΦ, rfl⟩, isRoot_e6Lat_iff.2 hroot,
      by rw [height_e6Lat]; exact hpos⟩
  · rintro ⟨hΦ, -, hpos⟩
    obtain ⟨γ', hγ', rfl⟩ := mem_parabolicRoots_d4Set_iff.1 hΦ
    have hmem : γ' ∈ parabolicPosRoots Tag.E6 d4Support :=
      ⟨hγ', hγ'.1, by rw [← height_e6Lat (τ := τ)]; exact hpos⟩
    rw [← range_d4Lat_d4PosRoot] at hmem
    obtain ⟨k, rfl⟩ := hmem
    exact ⟨k, rfl⟩

end Roots


section Torus

variable {τ : Tag} [hτ : E6Sub τ] {K : Type} [Field K]

omit hτ in
theorem eq_one_of_torusRootChar_single {J : Set (Fin τ.rank)} {h : ModGL τ K}
    (hh : h ∈ supportedTorus τ K J)
    (h1 : ∀ i : Fin τ.rank, torusRootChar h (Pi.single i 1) = 1) : h = 1 := by
  classical
  have : Fintype J := Fintype.ofFinite J
  obtain ⟨a, rfl⟩ := mem_supportedTorus.1 hh
  refine (supportedTorusHom_eq_one_iff J a).2 fun i => ?_
  have h2 := h1 i
  rw [torusRootChar_supportedTorusHom J a (isRoot_single τ i)] at h2
  have e : ∀ j : J, (∑ l, τ.cartan j l * (Pi.single i 1 : Fin τ.rank → ℤ) l) = τ.cartan j i :=
    fun j => by simp [Pi.single_apply]
  simp only [e] at h2
  exact Units.ext (by simpa using h2)

theorem torusRootChar_single_of_le {h : ModGL τ K} (hh : h ∈ supportedTorus τ K (d4Set τ))
    {i : Fin τ.rank} (hi : Tag.E6.rank ≤ i.val) : torusRootChar h (Pi.single i 1) = 1 := by
  classical
  have : Fintype (d4Set τ) := Fintype.ofFinite _
  obtain ⟨a, rfl⟩ := mem_supportedTorus.1 hh
  rw [torusRootChar_supportedTorusHom _ a (isRoot_single τ i)]
  have e : ∀ j : d4Set τ, (∑ l, τ.cartan j l * (Pi.single i 1 : Fin τ.rank → ℤ) l) = 0 :=
    fun j => by
      have := hτ.cartan_zero j i j.2.1 j.2.2 hi
      simpa [Pi.single_apply] using this
  simp [e]

omit hτ in
theorem coeff_torus_mul_unitriangular {h u : ModGL τ K} (hh : h ∈ torusGroup τ K)
    (hu : IsUpperUnitriangular (u : Module.End K (RootModule τ K))) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) :
    (((h * u : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K α))
      (Sum.inr ⟨α, hα⟩) = torusRootChar h α := by
  have hdiag := torusGroup_le_diagonalGroup hh
  obtain ⟨c, hc⟩ := exists_apply_single_of_mem_diagonalGroup hdiag (Sum.inr ⟨α, hα⟩ : Label τ)
  have hcv : (h : Module.End K (RootModule τ K)) (rootVec τ K α) = (c : K) • rootVec τ K α := by
    rw [rootVec_eq_single_of_isRoot hα]
    exact hc
  have hχ : torusRootChar h α = c := torusRootChar_eq_of_apply hα hcv
  rw [Units.val_mul, Module.End.mul_apply, rootVec_eq_single_of_isRoot hα,
    apply_apply_of_mem_diagonalGroup hdiag _ hc, hu.1, mul_one, hχ]

end Torus

section Unipotent

variable {τ : Tag} [hτ : E6Sub τ] {K : Type} [Field K]

theorem pinnedX_e6Lat_mem_subsystemGroup {β : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ parabolicRoots Tag.E6 d4Support) (c : K) :
    pinnedX τ K (e6Lat τ β) c ∈ subsystemGroup τ K (d4Set τ) :=
  rootSubgroup_le_subsystemGroup (mem_parabolicRoots_d4Set_iff.2 ⟨β, hβ, rfl⟩)
    (Subgroup.subset_closure ⟨c, rfl⟩)

theorem exists_sign_e6Res_pinnedX {β : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ parabolicRoots Tag.E6 d4Support) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (L : Type) [Field L] (c : L),
      e6Res L (fun _ hi => lt_six_of_mem_d4Set hi)
        ⟨pinnedX τ L (e6Lat τ β) c, pinnedX_e6Lat_mem_subsystemGroup hβ c⟩ =
        pinnedX Tag.E6 L β ((ε : L) * c) := by
  obtain ⟨ε, hε, h⟩ := exists_sign_pinnedX_comp_e6Emb (τ := τ) hβ.1
  exact ⟨ε, hε, fun L _ c => e6Res_eq _ fun v => LinearMap.congr_fun (h L c) v⟩

theorem eq_one_of_mem_parabolicLeviUnipotent_e6Res {u : subsystemGroup τ K (d4Set τ)}
    (hu : (u : ModGL τ K) ∈ parabolicLeviUnipotent τ K (d4Set τ))
    (h1 : e6Res K (fun _ hi => lt_six_of_mem_d4Set hi) u = 1) : u = 1 := by
  have hinj : Function.Injective (fun k => e6Lat τ (d4Lat (d4PosRoot k))) := fun i j h =>
    d4PosRoot_injective (d4Lat_injective (e6Lat_injective h))
  have hinj6 : Function.Injective (fun k => d4Lat (d4PosRoot k)) := fun i j h =>
    d4PosRoot_injective (d4Lat_injective h)
  have hβ : ∀ k, d4Lat (d4PosRoot k) ∈ parabolicRoots Tag.E6 d4Support := fun k =>
    ((range_d4Lat_d4PosRoot ▸ Set.mem_range_self k :
      d4Lat (d4PosRoot k) ∈ parabolicPosRoots Tag.E6 d4Support)).1
  obtain ⟨c, -, hc⟩ := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) _ hinj
    range_e6Lat_d4Lat_d4PosRoot).surjOn hu
  choose ε hε hεeq using fun k => exists_sign_e6Res_pinnedX (τ := τ) (hβ k)
  set l : List (subsystemGroup τ K (d4Set τ)) := List.ofFn fun k =>
    ⟨pinnedX τ K (e6Lat τ (d4Lat (d4PosRoot k))) (c k),
      pinnedX_e6Lat_mem_subsystemGroup (hβ k) (c k)⟩
  have hul : u = l.prod := by
    apply Subtype.ext
    rw [Subgroup.val_list_prod, List.map_ofFn]
    exact hc.symm
  have hr : e6Res K (fun _ hi => lt_six_of_mem_d4Set hi) u = (List.ofFn fun k =>
      pinnedX Tag.E6 K (d4Lat (d4PosRoot k)) ((ε k : K) * c k)).prod := by
    rw [hul, map_list_prod, List.map_ofFn]
    exact congrArg (fun f => (List.ofFn f).prod) (funext fun k => hεeq k K (c k))
  have h0 : (List.ofFn fun k => pinnedX Tag.E6 K (d4Lat (d4PosRoot k)) ((ε k : K) * c k)).prod =
      (List.ofFn fun k => pinnedX Tag.E6 K (d4Lat (d4PosRoot k)) ((fun _ => (0 : K)) k)).prod := by
    rw [← hr, h1]
    simp [pinnedX_zero]
  have hz := (bijOn_prod_pinnedX_parabolicPosRoots (τ := Tag.E6) (K := K) (J := d4Support)
    (fun k => d4Lat (d4PosRoot k)) hinj6 range_d4Lat_d4PosRoot).injOn (Set.mem_univ _)
    (Set.mem_univ (fun _ => (0 : K))) h0
  have hc0 : c = 0 := funext fun k => by
    have := congrFun hz k
    rcases hε k with he | he <;> simp [he] at this <;> exact this
  rw [hul]
  apply Subtype.ext
  rw [Subgroup.val_list_prod, List.map_ofFn, Subgroup.coe_one]
  simp [hc0, pinnedX_zero]

end Unipotent

section Kernel

variable {τ : Tag} [hτ : E6Sub τ] {K : Type} [Field K]

variable (τ K) in
@[expose] def nuQ : subsystemGroup τ K (d4Set τ) →* ModGL Tag.E6 K :=
  e6Res K (fun _ hi => lt_six_of_mem_d4Set hi)

theorem nuQ_apply (g : subsystemGroup τ K (d4Set τ)) (v : RootModule Tag.E6 K) :
    ((g : ModGL τ K) : Module.End K (RootModule τ K)) (e6Emb τ K v) =
      e6Emb τ K ((nuQ τ K g : Module.End K (RootModule Tag.E6 K)) v) :=
  e6Res_apply (fun _ hi => lt_six_of_mem_d4Set hi) g v

theorem nuQ_injective : Function.Injective (nuQ τ K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hlt : ∀ i ∈ d4Set τ, i.val < Tag.E6.rank := fun _ hi => lt_six_of_mem_d4Set hi
  have hgfix : ∀ v, ((g : ModGL τ K) : Module.End K (RootModule τ K)) (e6Emb τ K v) =
      e6Emb τ K v := by
    intro v
    rw [nuQ_apply g v, hg, Units.val_one, Module.End.one_apply]
  obtain ⟨⟨v, h, u, u'⟩, ⟨hv, hh, hu, hu', hgeq⟩, -⟩ := existsUnique_supportedCell_factors g.2
  simp only at hv hh hu hu' hgeq
  have hhQ : h ∈ subsystemGroup τ K (d4Set τ) := supportedTorus_le_subsystemGroup _ hh
  have huQ : u ∈ subsystemGroup τ K (d4Set τ) := parabolicLeviUnipotent_le_subsystemGroup hu
  have hu'Q : u' ∈ subsystemGroup τ K (d4Set τ) := by
    rw [subsystemGroup_eq_rootSpan]
    exact rootSpan_mono Set.inter_subset_left hu'
  have hhB : h ∈ borelGroup τ K :=
    torusGroup_le_borelGroup (supportedTorus_le_torusGroup _ hh)
  have huB : u ∈ borelGroup τ K :=
    Subgroup.mem_sup_right (parabolicLeviUnipotent_le_posUnipotent _ hu)
  have hu'B : u' ∈ borelGroup τ K :=
    Subgroup.mem_sup_right (rootSpan_le_posUnipotent (fun _ hα => ⟨hα.2.1, hα.2.2.1⟩) hu')
  have hb : (h * u)⁻¹ * u'⁻¹ ∈ borelGroup τ K :=
    mul_mem (inv_mem (mul_mem hhB huB)) (inv_mem hu'B)
  have hn : canonicalRep (coxeterSystem τ) K v = (h * u)⁻¹ * (g : ModGL τ K) * u'⁻¹ := by
    rw [← hgeq]
    group
  have hfix : ∀ γ ∈ parabolicRoots τ (d4Set τ),
      (canonicalRep (coxeterSystem τ) K v : Module.End K (RootModule τ K)) (rootVec τ K γ) =
        (((h * u)⁻¹ * u'⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K γ) := by
    intro γ hγ
    obtain ⟨γ', -, rfl⟩ := mem_parabolicRoots_d4Set_iff.1 hγ
    have e1 : ((u'⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K (e6Lat τ γ')) =
        e6Emb τ K ((nuQ τ K ⟨u'⁻¹, inv_mem hu'Q⟩ : Module.End K (RootModule Tag.E6 K))
          (rootVec Tag.E6 K γ')) := by
      rw [← e6Emb_rootVec, ← nuQ_apply ⟨u'⁻¹, inv_mem hu'Q⟩]
    have e2 : ((g : ModGL τ K) : Module.End K (RootModule τ K))
        (((u'⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K (e6Lat τ γ'))) =
        ((u'⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K (e6Lat τ γ')) := by
      rw [e1, hgfix]
    rw [hn, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, e2,
      Units.val_mul, Module.End.mul_apply]
  have hvγ : ∀ γ ∈ parabolicRoots τ (d4Set τ), v • γ = γ := by
    intro γ hγ
    have hmaps := mapsRootLines_canonicalRep (R := K) v
    have hγneg : -γ ∈ parabolicRoots τ (d4Set τ) := neg_mem_parabolicRoots hγ
    have n1 := not_precedes_of_apply_eq_borel hb hmaps hγ.1 (hfix γ hγ)
    have n2 := not_precedes_of_apply_eq_borel hb hmaps hγneg.1 (hfix (-γ) hγneg)
    exact eq_of_not_precedes_of_not_precedes_neg _ _ _ _ rfl (by rw [smul_neg]) n1 n2
  have hv1 : v = 1 := eq_one_of_fix_of_mem_parabolicWeylGroup hv fun j hj =>
    hvγ _ (single_mem_parabolicRoots hj)
  subst hv1
  have hu'1 : u' = 1 := by
    rw [inversionSet_one, Set.inter_empty] at hu'
    simpa [rootSpan] using hu'
  rw [hu'1, canonicalRep_one, mul_one, mul_one] at hgeq
  have hhT : h ∈ torusGroup τ K := supportedTorus_le_torusGroup _ hh
  have huU : IsUpperUnitriangular (u : Module.End K (RootModule τ K)) :=
    (positive_root_triangularity.{0, 0} τ).1 K |>.1 u
      (parabolicLeviUnipotent_le_posUnipotent _ hu)
  have hχ : ∀ i : Fin τ.rank, torusRootChar h (Pi.single i 1) = 1 := by
    intro i
    by_cases hi : i.val < Tag.E6.rank
    · obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) hi
      have hα : IsRoot τ (Pi.single (e6Idx k) 1) := isRoot_single τ _
      rw [← coeff_torus_mul_unitriangular hhT huU hα, hgeq]
      have hv : rootVec τ K (Pi.single (e6Idx k) 1) = e6Emb τ K (rootVec Tag.E6 K (Pi.single k 1)) := by
        rw [e6Emb_rootVec, e6Lat_single]
      rw [hv, hgfix, ← hv, rootVec_eq_single_of_isRoot hα, Finsupp.single_eq_same]
    · exact torusRootChar_single_of_le hh (not_lt.1 hi)
  have hh1 : h = 1 := eq_one_of_torusRootChar_single hh hχ
  subst hh1
  rw [one_mul] at hgeq
  have hgu : g = ⟨u, huQ⟩ := Subtype.ext hgeq.symm
  rw [hgu] at hg ⊢
  exact eq_one_of_mem_parabolicLeviUnipotent_e6Res hu hg

end Kernel

end CFSG.RankThree.PartOne.KD4T
