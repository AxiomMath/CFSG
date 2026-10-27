module

public import CFSG.RankThree.PartOne.KE6.E6LBruhat
public import CFSG.RankThree.PartOne.KD4T.Inj
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Steinberg.Minuscule.Unipotent

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

section Min

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {K : Type} [Field K]

theorem m27Res_mem_minGroup (g : subsystemGroup τ K (e6Set τ)) :
    m27Res K e6Set_lt' g ∈ e6Data_valid.minGroup K := by
  have hle : (⊤ : Subgroup (subsystemGroup τ K (e6Set τ))) ≤
      (e6Data_valid.minGroup K).comap (m27Res K e6Set_lt') := by
    rw [← closure_Q_generators (τ := τ) (K := K), Subgroup.closure_le]
    rintro ⟨x, hx'⟩ ⟨i, hi, c, h | h⟩
    · obtain ⟨k, rfl⟩ := exists_e6Id_eq hi
      have e : (⟨x, hx'⟩ : subsystemGroup τ K (e6Set τ)) =
          ⟨xUnit τ K (e6Idx k) c, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set k) c⟩ :=
        Subtype.ext h
      rw [SetLike.mem_coe, Subgroup.mem_comap, e, m27Res_xUnit e6Set_lt' k (e6Idx_mem_e6Set k) c]
      exact e6Data_valid.xu_mem K _ _
    · obtain ⟨k, rfl⟩ := exists_e6Id_eq hi
      have e : (⟨x, hx'⟩ : subsystemGroup τ K (e6Set τ)) =
          ⟨yUnit τ K (e6Idx k) c, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set k) c⟩ :=
        Subtype.ext h
      rw [SetLike.mem_coe, Subgroup.mem_comap, e, m27Res_yUnit e6Set_lt' k (e6Idx_mem_e6Set k) c]
      exact e6Data_valid.xu_mem K _ _
  exact hle (Subgroup.mem_top g)

variable (τ K) in
@[expose] def m27ResMin : subsystemGroup τ K (e6Set τ) →* e6Data_valid.minGroup K :=
  (m27Res K e6Set_lt').codRestrict _ m27Res_mem_minGroup

theorem m27ResMin_xUnit (j : Fin Tag.E6.rank) (c : K) :
    m27ResMin τ K ⟨xUnit τ K (e6Idx j) c, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set j) c⟩ =
      e6Data_valid.xm K (Pi.single j 1) c :=
  Subtype.ext (m27Res_xUnit e6Set_lt' j (e6Idx_mem_e6Set j) c)

theorem m27ResMin_yUnit (j : Fin Tag.E6.rank) (c : K) :
    m27ResMin τ K ⟨yUnit τ K (e6Idx j) c, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set j) c⟩ =
      e6Data_valid.xm K (-Pi.single j 1) c :=
  Subtype.ext (m27Res_yUnit e6Set_lt' j (e6Idx_mem_e6Set j) c)

omit [M27Ok τ] in
theorem pinnedX_e6Lat_mem_subsystemGroup {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (c : K) : pinnedX τ K (e6Lat τ β) c ∈ subsystemGroup τ K (e6Set τ) :=
  rootSubgroup_le_subsystemGroup (mem_parabolicRoots_e6Set_iff.2 ⟨β, hβ, rfl⟩)
    (Subgroup.subset_closure ⟨c, rfl⟩)

theorem m27ResMin_pinnedX {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      m27ResMin τ K ⟨pinnedX τ K (e6Lat τ β) c, pinnedX_e6Lat_mem_subsystemGroup hβ c⟩ =
        e6Data_valid.xm K β (ε * c) := by
  obtain ⟨ε, hε, h⟩ := exists_sign_pinnedX_comp_m27Emb (τ := τ) (L := K) hβ
  exact ⟨ε, hε, fun c => Subtype.ext (m27Res_eq _ fun v => LinearMap.congr_fun (h c) v)⟩

end Min

section Torus

variable {τ : Tag} [hτ : E6Sub τ] {K : Type} [Field K]

omit hτ in
theorem eq_one_of_torusRootChar_single' {J : Set (Fin τ.rank)} {h : ModGL τ K}
    (hh : h ∈ supportedTorus τ K J)
    (h1 : ∀ i : Fin τ.rank, torusRootChar h (Pi.single i 1) = 1) : h = 1 := by
  exact KD4T.eq_one_of_torusRootChar_single hh h1

omit hτ in
theorem coeff_torus_mul_unitriangular' {h u : ModGL τ K} (hh : h ∈ torusGroup τ K)
    (hu : IsUpperUnitriangular (u : Module.End K (RootModule τ K))) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) :
    (((h * u : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K α))
      (Sum.inr ⟨α, hα⟩) = torusRootChar h α := by
  exact KD4T.coeff_torus_mul_unitriangular hh hu hα

omit hτ in
theorem exists_rootChar_eq {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    ∃ b : Fin τ.rank → Kˣ, ∀ β, IsRoot τ β →
      torusRootChar h β = ((rootChar b β : Kˣ) : K) := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  exact ⟨b, fun β hβ => (eq_torusRootChar_of_conj hh hβ
    (fun c => rootDiagUnit_conj_pinnedX b hβ c)).symm⟩

theorem cartan_e6_zero_E7 : ∀ j i : Fin Tag.E7.rank, j.val < 6 → 7 ≤ i.val →
    Tag.E7.cartan j i = 0 := fun j i h1 h2 =>
  sub_zero (Tag.E7.cartan j i) ▸ (by decide +kernel : ∀ j i : Fin Tag.E7.rank, j.val < 6 → 7 ≤ i.val →
    Tag.E7.cartan j i - 0 = 0) j i h1 h2

theorem cartan_e6_zero_E8 : ∀ j i : Fin Tag.E8.rank, j.val < 6 → 7 ≤ i.val →
    Tag.E8.cartan j i = 0 := fun j i h1 h2 =>
  sub_zero (Tag.E8.cartan j i) ▸ (by decide +kernel : ∀ j i : Fin Tag.E8.rank, j.val < 6 → 7 ≤ i.val →
    Tag.E8.cartan j i - 0 = 0) j i h1 h2

theorem cartan_e6_zero {τ : Tag} [M27Ok τ] (j i : Fin τ.rank) (hj : j.val < 6) (hi : 7 ≤ i.val) :
    τ.cartan j i = 0 := by
  rcases M27Ok.isE7E8 (τ := τ) with rfl | rfl
  · exact cartan_e6_zero_E7 j i hj hi
  · exact cartan_e6_zero_E8 j i hj hi

omit hτ in
theorem torusRootChar_single_of_ge_seven [M27Ok τ] {h : ModGL τ K}
    (hh : h ∈ supportedTorus τ K (e6Set τ)) {i : Fin τ.rank} (hi : 7 ≤ i.val) :
    torusRootChar h (Pi.single i 1) = 1 := by
  classical
  have : Fintype (e6Set τ) := Fintype.ofFinite _
  obtain ⟨a, rfl⟩ := mem_supportedTorus.1 hh
  rw [torusRootChar_supportedTorusHom _ a (isRoot_single τ i)]
  have e : ∀ j : e6Set τ, (∑ l, τ.cartan j l * (Pi.single i 1 : Fin τ.rank → ℤ) l) = 0 :=
    fun j => by
      have := cartan_e6_zero (τ := τ) j i (e6Set_lt j.2) hi
      simpa [Pi.single_apply] using this
  simp [e]

theorem m27Root_last_E7 : ∃ a : Fin e6Data.d, m27Root Tag.E7 a = Pi.single ⟨6, by decide⟩ 1 := by
  decide +kernel

theorem m27Root_last_E8 : ∃ a : Fin e6Data.d, m27Root Tag.E8 a = Pi.single ⟨6, by decide⟩ 1 := by
  decide +kernel

theorem exists_m27Root_eq_single_six [M27Ok τ] {i : Fin τ.rank} (hi : i.val = 6) :
    ∃ a : Fin e6Data.d, m27Root τ a = Pi.single i 1 := by
  rcases M27Ok.isE7E8 (τ := τ) with rfl | rfl
  · obtain rfl : i = ⟨6, by decide⟩ := Fin.ext hi
    exact m27Root_last_E7
  · obtain rfl : i = ⟨6, by decide⟩ := Fin.ext hi
    exact m27Root_last_E8

theorem torusRootChar_single_eq_one [M27Ok τ] {h : ModGL τ K}
    (hh : h ∈ supportedTorus τ K (e6Set τ))
    (h27 : ∀ a : Fin e6Data.d, torusRootChar h (m27Root τ a) = 1) (i : Fin τ.rank) :
    torusRootChar h (Pi.single i 1) = 1 := by
  by_cases hi6 : i.val < 6
  · have hhT : h ∈ torusGroup τ K := supportedTorus_le_torusGroup _ hh
    obtain ⟨b, hb⟩ := exists_rootChar_eq hhT
    obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) hi6
    obtain ⟨a, ha⟩ := exists_wt_neg_one k
    have hs := m27_add_single (τ := τ) a k ha
    have h1 := h27 a
    have h2 := h27 ⟨e6Data.weyl a k, e6Data_weyl_lt a k⟩
    rw [hb _ (m27_isRoot M27Ok.isE7E8 a)] at h1
    rw [hb _ (m27_isRoot M27Ok.isE7E8 _), hs, rootChar_add] at h2
    rw [hb _ (isRoot_single τ _)]
    have e1 : rootChar b (m27Root τ a) = 1 := Units.val_eq_one.1 h1
    rw [e1, one_mul] at h2
    exact h2
  · by_cases hi7 : i.val = 6
    · obtain ⟨a, ha⟩ := exists_m27Root_eq_single_six (τ := τ) hi7
      rw [← ha]
      exact h27 a
    · exact torusRootChar_single_of_ge_seven hh (by omega)

end Torus

section Unipotent

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {K : Type} [Field K]

theorem eq_one_of_mem_parabolicLeviUnipotent_m27ResMin
    {u : subsystemGroup τ K (e6Set τ)}
    (hu : (u : ModGL τ K) ∈ parabolicLeviUnipotent τ K (e6Set τ))
    (h1 : m27ResMin τ K u = 1) : u = 1 := by
  have hinj := e6Lat_posRoot6_injective (τ := τ)
  obtain ⟨c, -, hc⟩ := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) _ hinj
    range_e6Lat_posRoot6).surjOn hu
  choose ε hε hεeq using fun k => m27ResMin_pinnedX (τ := τ) (K := K) (posRoot6_isRoot' k)
  set l : List (subsystemGroup τ K (e6Set τ)) := List.ofFn fun k =>
    ⟨pinnedX τ K (e6Lat τ (posRoot6 k)) (c k),
      pinnedX_e6Lat_mem_subsystemGroup (posRoot6_isRoot' k) (c k)⟩ with hl
  have hul : u = l.prod := by
    apply Subtype.ext
    rw [Subgroup.val_list_prod, List.map_ofFn]
    exact hc.symm
  have hr : m27ResMin τ K u = (List.ofFn fun k =>
      e6Data_valid.xm K (posRoot6 k) (ε k * c k)).prod := by
    rw [hul, map_list_prod, List.map_ofFn]
    exact congrArg (fun f => (List.ofFn f).prod) (funext fun k => hεeq k (c k))
  have hnd : (List.ofFn posRoot6).Nodup := List.nodup_ofFn.2 posRoot6_injective
  have hroot : ∀ γ ∈ List.ofFn posRoot6, IsRoot Tag.E6 γ ∧ 0 < 1 * CFSG.LieType.Steinberg.ht γ := by
    intro γ hγ
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hγ
    exact ⟨posRoot6_isRoot' k, by rw [one_mul]; exact posRoot6_pos k⟩
  have hsort : (List.ofFn posRoot6).Pairwise
      (fun γ δ => 1 * CFSG.LieType.Steinberg.ht γ ≤ 1 * CFSG.LieType.Steinberg.ht δ) :=
    posRoot6_sorted.imp fun h => by simpa [CFSG.LieType.Steinberg.ht, height] using h
  have hPI := e6Data_valid.prodInjective posDef_cartan_E6 (k := K) 1 (List.ofFn posRoot6) hnd hroot
    hsort
  let fe : (Fin Tag.E6.rank → ℤ) → K := Function.extend posRoot6 (fun k => ε k * c k) fun _ => 0
  have hfe : ∀ k, fe (posRoot6 k) = ε k * c k := fun k =>
    posRoot6_injective.extend_apply _ _ k
  have hmem : ∀ (γ : Fin Tag.E6.rank → ℤ) (x : K), e6Data_valid.xm K γ x ∈ e6Data_valid.rootGroup K γ :=
    fun γ x => e6Data_valid.xm_mem_rootGroup K γ x
  have key := hPI (fun γ => e6Data_valid.xm K γ (fe γ)) (fun γ => e6Data_valid.xm K γ 0)
    (fun γ _ => hmem γ _) (fun γ _ => hmem γ _) (by
      rw [List.map_ofFn, List.map_ofFn]
      have e1 : ((fun γ => e6Data_valid.xm K γ (fe γ)) ∘ posRoot6) =
          fun k => e6Data_valid.xm K (posRoot6 k) (ε k * c k) := by
        funext k
        simp only [Function.comp_apply, hfe]
      have e2 : ((fun γ => e6Data_valid.xm K γ (0 : K)) ∘ posRoot6) =
          fun k => (1 : e6Data_valid.minGroup K) := by
        funext k
        simp only [Function.comp_apply, e6Data_valid.xm_zero]
      rw [e1, e2, ← hr, h1]
      simp)
  have hc0 : c = 0 := funext fun k => by
    have := key (posRoot6 k) (List.mem_ofFn.2 ⟨k, rfl⟩)
    simp only [hfe, e6Data_valid.xm_zero] at this
    have h0 := e6Data_valid.xm_injective K (posRoot6_isRoot' k) (this.trans (e6Data_valid.xm_zero K _).symm)
    rcases hε k with he | he <;> simp [he] at h0 <;> exact h0
  rw [hul]
  apply Subtype.ext
  rw [Subgroup.val_list_prod, List.map_ofFn, Subgroup.coe_one]
  simp [hc0, pinnedX_zero]

end Unipotent

end CFSG.RankThree.PartOne.KE6
