module

public import CFSG.RankThree.Lattice.SteinbergBIGenOrbitRankOne
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedUnipotent

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem not_isRoot_nsmul_add_nsmul_of_mem_thetaOrbit {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ kernelRoots D.χ) {α β : Fin τ.rank → ℤ} (hα : α ∈ thetaOrbit D.θ γ)
    (hβ : β ∈ thetaOrbit D.θ γ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬IsRoot τ (a • α + b • β) :=
  D.not_isRoot_nsmul_add_nsmul_of_orthogonal (D.thetaOrbit_subset_kernelRoots hγ hα).1
    (D.thetaOrbit_subset_kernelRoots hγ hβ).1 (D.orbit_orthogonal γ hγ α hα β hβ) ha hb

theorem bijOn_thetaOrbit {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots D.χ) :
    Set.BijOn D.θ (toReal '' thetaOrbit D.θ γ) (toReal '' thetaOrbit D.θ γ) := by
  have hmaps : Set.MapsTo D.θ (toReal '' thetaOrbit D.θ γ) (toReal '' thetaOrbit D.θ γ) := by
    rintro _ ⟨β, ⟨m, hm⟩, rfl⟩
    have hspec := D.thetaPowVec_spec hγ (m + 1)
    refine ⟨_, hspec.2.1, ?_⟩
    rw [hspec.1, ← hm, pow_succ', Module.End.mul_apply]
  exact (Set.Finite.injOn_iff_bijOn_of_mapsTo ((D.finite_thetaOrbit hγ).image _) hmaps).1
    D.theta_injective.injOn

theorem coe_F_mem_rootSpan_thetaOrbit {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots D.χ)
    {x : adjointGroup τ k} (hx : (x : ModGL τ k) ∈ rootSpan τ k (thetaOrbit D.θ γ)) :
    (D.F x : ModGL τ k) ∈ rootSpan τ k (thetaOrbit D.θ γ) := by
  have h := D.map_rootSpan_subgroupOf (D.thetaOrbit_subset_kernelRoots hγ) (D.bijOn_thetaOrbit hγ)
  have h1 : D.F x ∈ ((rootSpan τ k (thetaOrbit D.θ γ)).subgroupOf (adjointGroup τ k)).map
      D.F.toMonoidHom := ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [h] at h1
  exact Subgroup.mem_subgroupOf.1 h1

theorem exists_fixed_block_factors {S : Set (Fin τ.rank → ℤ)} (hSΨ : S ⊆ D.posRootsJ)
    (hθS : ∀ α ∈ S, thetaOrbit D.θ α ⊆ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S)
    {L : List (Set (Fin τ.rank → ℤ))} (hLnd : L.Nodup)
    (hL : ∀ Q, Q ∈ L ↔ ∃ γ ∈ S, Q = thetaOrbit D.θ γ)
    {x : adjointGroup τ k} (hx : x ∈ D.fixedRootSpan S) :
    ∃ y : Set (Fin τ.rank → ℤ) → adjointGroup τ k, (∀ Q ∈ L, y Q ∈ D.fixedRootSpan Q) ∧
      x = (L.map y).prod := by
  classical
  obtain ⟨hxU, hxF⟩ := D.mem_fixedRootSpan.1 hx
  have hSK : ∀ α ∈ S, α ∈ kernelRoots D.χ := fun α hα => (hSΨ hα).1.1
  have hSpos : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α := fun α hα =>
    ⟨isRoot_of_mem_unionRoots (hSΨ hα).1, (hSΨ hα).2⟩
  have hQ : ∀ Q ∈ L, ∃ γ ∈ S, Q = thetaOrbit D.θ γ := fun Q hQ' => (hL Q).1 hQ'
  set enum : Set (Fin τ.rank → ℤ) → List (Fin τ.rank → ℤ) :=
    fun Q => if h : Q.Finite then h.toFinset.toList else [] with henumdef
  have henum : ∀ Q ∈ L, (enum Q).Nodup ∧ ∀ α, α ∈ enum Q ↔ α ∈ Q := fun Q hQ' => by
    obtain ⟨γ, hγ, rfl⟩ := hQ Q hQ'
    have hfin := D.finite_thetaOrbit (hSK γ hγ)
    simp only [henumdef, dite_eq_left_of_eq_true (eq_true hfin)]
    exact ⟨Finset.nodup_toList _, fun α => Finset.mem_toList.trans hfin.mem_toFinset⟩
  have horb : ∀ Q ∈ L, ∀ α ∈ Q, thetaOrbit D.θ α = Q := fun Q hQ' α hα => by
    obtain ⟨γ, hγ, rfl⟩ := hQ Q hQ'
    exact D.thetaOrbit_eq_of_mem (hSK γ hγ) hα
  set l := L.flatMap enum with hl
  have hlnd : l.Nodup := by
    refine List.nodup_flatMap.2 ⟨fun Q hQ' => (henum Q hQ').1, ?_⟩
    refine hLnd.imp_of_mem fun hQ₁ hQ₂ hne => ?_
    rw [Function.onFun, List.disjoint_left]
    intro α h₁ h₂
    exact hne ((horb _ hQ₁ α ((henum _ hQ₁).2 α |>.1 h₁)).symm.trans
      (horb _ hQ₂ α ((henum _ hQ₂).2 α |>.1 h₂)))
  have hlmem : ∀ α, α ∈ l ↔ α ∈ S := fun α => by
    rw [hl, List.mem_flatMap]
    constructor
    · rintro ⟨Q, hQ', hα⟩
      obtain ⟨γ, hγ, rfl⟩ := hQ Q hQ'
      exact hθS γ hγ ((henum _ hQ').2 α |>.1 hα)
    · intro hα
      have hQ' : thetaOrbit D.θ α ∈ L := (hL _).2 ⟨α, hα, rfl⟩
      exact ⟨_, hQ', (henum _ hQ').2 α |>.2 (self_mem_thetaOrbit _ α)⟩
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq k hSpos hclosed hlnd hlmem hxU
  have hprod : ∀ e : (Fin τ.rank → ℤ) → k, (l.map fun α => pinnedX τ k α (e α)).prod =
      (L.map fun Q => ((enum Q).map fun α => pinnedX τ k α (e α)).prod).prod := fun e => by
    rw [hl, List.map_flatMap, list_prod_flatMap]
  set y : Set (Fin τ.rank → ℤ) → adjointGroup τ k := fun Q =>
    ⟨((enum Q).map fun α => pinnedX τ k α (c α)).prod, Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨α, -, rfl⟩ := List.mem_map.1 hz
      exact pinnedX_mem_adjointGroup α (c α)⟩ with hy
  have hxy : x = (L.map y).prod := by
    apply Subtype.ext
    rw [← hc, hprod, Subgroup.val_list_prod, List.map_map]
    rfl
  have hyU : ∀ Q ∈ L, ((y Q : adjointGroup τ k) : ModGL τ k) ∈ rootSpan τ k Q := fun Q hQ' =>
    list_map_prod_pinnedX_mem_rootSpan k (fun α hα => (henum Q hQ').2 α |>.1 hα) c
  have hFy : ∀ Q ∈ L, ∃ d : (Fin τ.rank → ℤ) → k,
      ((enum Q).map fun α => pinnedX τ k α (d α)).prod = (D.F (y Q) : ModGL τ k) := by
    intro Q hQ'
    obtain ⟨γ, hγ, rfl⟩ := hQ Q hQ'
    have hγK := hSK γ hγ
    refine exists_list_prod_pinnedX_eq k (fun α hα => hSpos α (hθS γ hγ hα))
      (fun α hα β hβ a b ha hb hr =>
        absurd hr (D.not_isRoot_nsmul_add_nsmul_of_mem_thetaOrbit hγK hα hβ ha hb))
      (henum _ hQ').1 (henum _ hQ').2 (D.coe_F_mem_rootSpan_thetaOrbit hγK (hyU _ hQ'))
  choose! d hd using hFy
  set d' : (Fin τ.rank → ℤ) → k := fun α => d (thetaOrbit D.θ α) α with hd'
  have hblock : ∀ Q ∈ L, ∀ e e' : (Fin τ.rank → ℤ) → k, (∀ α ∈ Q, e α = e' α) →
      ((enum Q).map fun α => pinnedX τ k α (e α)).prod =
        ((enum Q).map fun α => pinnedX τ k α (e' α)).prod := fun Q hQ' e e' h =>
    congrArg List.prod (List.map_congr_left fun α hα => by rw [h α ((henum Q hQ').2 α |>.1 hα)])
  have hFd : ∀ Q ∈ L, ((enum Q).map fun α => pinnedX τ k α (d' α)).prod =
      (D.F (y Q) : ModGL τ k) := fun Q hQ' => by
    rw [← hd Q hQ']
    exact hblock Q hQ' _ _ fun α hα => by
      show d (thetaOrbit D.θ α) α = d Q α
      rw [horb Q hQ' α hα]
  have hFx : (D.F x : ModGL τ k) = (l.map fun α => pinnedX τ k α (d' α)).prod := by
    rw [hprod, hxy, map_list_prod, Subgroup.val_list_prod, List.map_map, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun Q hQ' => (hFd Q hQ').symm)
  have hcoord := pinnedX_list_prod_injective l hlnd (fun α hα => hSpos α ((hlmem α).1 hα)) d' c
    (by rw [← hFx, hxF, hc])
  have hyF : ∀ Q ∈ L, D.F (y Q) = y Q := fun Q hQ' => Subtype.ext (by
    rw [← hFd Q hQ']
    show _ = ((enum Q).map fun α => pinnedX τ k α (c α)).prod
    exact hblock Q hQ' _ _ fun α hα => hcoord α ((hlmem α).2 (by
      obtain ⟨γ, hγ, rfl⟩ := hQ Q hQ'
      exact hθS γ hγ hα)))
  exact ⟨y, fun Q hQ' => D.mem_fixedRootSpan.2 ⟨hyU Q hQ', hyF Q hQ'⟩, hxy⟩

theorem mem_orbitGroup_of_mem_fixedRootSpan {S : Set (Fin τ.rank → ℤ)} (hSΨ : S ⊆ D.posRootsJ)
    (hθS : ∀ α ∈ S, thetaOrbit D.θ α ⊆ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S)
    {x : adjointGroup τ k} (hx : x ∈ D.fixedRootSpan S) : (x : ModGL τ k) ∈ D.orbitGroup := by
  have hSfin : S.Finite := D.finite_roots.subset fun α hα => (hSΨ hα).1
  have h𝒪fin : ((thetaOrbit D.θ) '' S).Finite := hSfin.image _
  obtain ⟨y, hy, hxy⟩ := D.exists_fixed_block_factors hSΨ hθS hclosed
    (Finset.nodup_toList h𝒪fin.toFinset) (fun Q => by
      rw [Finset.mem_toList, Set.Finite.mem_toFinset]
      exact ⟨fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩, fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩⟩) hx
  rw [hxy, Subgroup.val_list_prod, List.map_map]
  refine Subgroup.list_prod_mem _ fun z hz => ?_
  obtain ⟨Q, hQ', rfl⟩ := List.mem_map.1 hz
  obtain ⟨γ, hγ, rfl⟩ := (Set.Finite.mem_toFinset h𝒪fin).1 (Finset.mem_toList.1 hQ')
  exact D.fixedRootSpan_thetaOrbit_subset_orbitGroup (hSΨ hγ).1 ⟨y _, hy _ hQ', rfl⟩

end GenFixedRootDatum

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

omit [IsAlgClosed k] in
theorem entrywise_rootSL2 (σ : k →+* k) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (A : SL2 k) :
    Units.map (entrywiseHom σ) (rootSL2 τ k β A) =
      rootSL2 τ k β (Matrix.SpecialLinearGroup.map σ A) :=
  OrthogonalSemilinearFixedRootDatum.entrywise_rootSL2 σ hβ A

omit [IsAlgClosed k] in
theorem rootSpan_singleton (δ : Fin τ.rank → ℤ) : rootSpan τ k {δ} = rootSubgroup τ k δ :=
  OrthogonalSemilinearFixedRootDatum.rootSpan_singleton δ

omit [IsAlgClosed k] in
theorem map_conj_rootSubgroup_of_mem_monomialSubgroup {n : ModGL τ k}
    (hn : n ∈ monomialSubgroup τ k) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    (rootSubgroup τ k δ).map (MulAut.conj n).toMonoidHom =
      rootSubgroup τ k (weylQuotientHom τ k ⟨n, hn⟩ • δ) :=
  OrthogonalSemilinearFixedRootDatum.map_conj_rootSubgroup_of_mem_monomialSubgroup hn hδ

theorem rootSpanJ_le_closure :
    D.rootSpanJ ≤ Subgroup.closure (⋃ β ∈ D.simpleRootsJ, Set.range (rootSL2 τ k β)) := by
  set C := Subgroup.closure (⋃ β ∈ D.simpleRootsJ, Set.range (rootSL2 τ k β)) with hC
  have hL : ∀ β ∈ D.simpleRootsJ, rootRankOneGroup τ k β ≤ C := fun β hβ => by
    rintro _ ⟨A, rfl⟩
    exact Subgroup.subset_closure (Set.mem_biUnion hβ ⟨A, rfl⟩)
  have hroot : ∀ β ∈ D.simpleRootsJ, IsRoot τ β := fun β hβ =>
    isRoot_of_mem_unionSimpleRoots (D.mem_simpleRootsJ_iff.1 hβ)
  have hU : ∀ β ∈ D.simpleRootsJ, rootSubgroup τ k β ≤ C := fun β hβ => by
    refine le_trans ?_ (hL β hβ)
    rw [(exceptional_Lang_root_rank_one_torus_transport τ k (hroot β hβ)).1]
    exact le_sup_left
  have hstep : ∀ γ ∈ D.simpleRootsJ, ∀ δ, IsRoot τ δ → rootSubgroup τ k δ ≤ C →
      rootSubgroup τ k (rootReflection γ • δ) ≤ C := by
    intro γ hγ δ hδ hδC
    obtain ⟨hN, hw⟩ :=
      (exceptional_Lang_root_rank_one_torus_transport τ k (hroot γ hγ)).2.2.1 1
    have hnC : rootWeylSL2 τ k γ 1 ∈ C := hL γ hγ ⟨_, rfl⟩
    have h := map_conj_rootSubgroup_of_mem_monomialSubgroup hN hδ
    rw [hw] at h
    rw [← h]
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hnC (hδC hy)) (inv_mem hnC)
  have hW : ∀ w ∈ D.weylJ, ∀ δ, IsRoot τ δ → rootSubgroup τ k δ ≤ C →
      rootSubgroup τ k (w • δ) ≤ C := by
    intro w hw
    induction hw using Subgroup.closure_induction'' with
    | mem x hx =>
      obtain ⟨γ, hγ, rfl⟩ := hx
      exact hstep γ hγ
    | inv_mem x hx =>
      obtain ⟨γ, hγ, rfl⟩ := hx
      rw [rootReflection_inv (hroot γ hγ)]
      exact hstep γ hγ
    | one => exact fun δ _ h => by rwa [one_smul]
    | mul x y _ _ hx hy =>
      exact fun δ hδ h => by
        rw [mul_smul]
        exact hx _ (IsRoot.smul hδ y) (hy δ hδ h)
  refine iSup₂_le fun α hα => ?_
  obtain ⟨w, hw, β, hβ, rfl⟩ := exists_smul_unionSimpleRoot hα
  have hβ' : β ∈ D.simpleRootsJ := D.mem_simpleRootsJ_iff.2 hβ
  exact hW w (D.weylJ_eq ▸ hw) β (hroot β hβ') (hU β hβ')

theorem coe_F_pow_rootSL2 {β : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots D.χ Set.univ)
    (A : SL2 k) (m : ℕ) {x : adjointGroup τ k} (hx : (x : ModGL τ k) = rootSL2 τ k β A) :
    ((D.F ^ m) x : ModGL τ k) = rootSL2 τ k (thetaPowVec D.θ m β)
      (Matrix.SpecialLinearGroup.map (iterateFrobenius k p₀ (D.e * m)) A) := by
  have hβK : β ∈ kernelRoots D.χ := by
    obtain ⟨i, -, hi⟩ := hβ
    exact (simpleRoots_subset hi).1
  have hΔ : ∀ j, thetaPowVec D.θ j β ∈ unionSimpleRoots D.χ Set.univ := fun j =>
    thetaOrbit_subset_of_mapsTo D.bijOn_simpleRoots.mapsTo hβ (D.thetaPowVec_spec hβK j).2.1
  induction m with
  | zero =>
    rw [pow_zero, MulAut.one_apply, hx, D.map_frobenius_zero,
      thetaPowVec_eq (by rw [pow_zero, Module.End.one_apply])]
  | succ m ih =>
    have hθ : D.θ (toReal (thetaPowVec D.θ m β)) = toReal (thetaPowVec D.θ (m + 1) β) := by
      rw [(D.thetaPowVec_spec hβK m).1, (D.thetaPowVec_spec hβK (m + 1)).1, pow_succ',
        Module.End.mul_apply]
    rw [pow_succ', MulAut.mul_apply, D.map_rootSL2 _ (hΔ m) _ hθ _ _ ih,
      D.map_frobenius_map_frobenius]

theorem exists_F_pow_eq_entrywise :
    ∃ n, 0 < n ∧ ∀ x : adjointGroup τ k, (x : ModGL τ k) ∈ D.rootSpanJ →
      ((D.F ^ n) x : ModGL τ k) =
        Units.map (entrywiseHom (iterateFrobenius k p₀ (D.e * n))) (x : ModGL τ k) := by
  obtain ⟨n, hn, hper⟩ := D.exists_pow_eq_on_kernelRoots
  refine ⟨n, hn, fun x hx => ?_⟩
  set σ := iterateFrobenius k p₀ (D.e * n)
  have hCadj : Subgroup.closure (⋃ β ∈ D.simpleRootsJ, Set.range (rootSL2 τ k β)) ≤
      adjointGroup τ k := by
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨β, -, A, rfl⟩ := Set.mem_iUnion₂.1 hg
    exact rootSL2_mem_adjointGroup _ _
  have key : ∀ g (hg : g ∈ Subgroup.closure (⋃ β ∈ D.simpleRootsJ, Set.range (rootSL2 τ k β))),
      ((D.F ^ n) ⟨g, hCadj hg⟩ : ModGL τ k) = Units.map (entrywiseHom σ) g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨β, hβ, A, rfl⟩ := Set.mem_iUnion₂.1 hg
      have hβK := D.mem_kernelRoots_of_mem_simpleRootsJ hβ
      rw [D.coe_F_pow_rootSL2 hβ.1 A n rfl,
        thetaPowVec_eq (hper β hβK).symm, entrywise_rootSL2 σ
          (isRoot_of_mem_unionSimpleRoots (D.mem_simpleRootsJ_iff.1 hβ))]
    | one =>
      have h1 : (⟨1, hCadj (one_mem _)⟩ : adjointGroup τ k) = 1 := rfl
      rw [h1, map_one, map_one]
      rfl
    | mul g h hg hh ihg ihh =>
      have e : (⟨g * h, hCadj (mul_mem hg hh)⟩ : adjointGroup τ k) =
          ⟨g, hCadj hg⟩ * ⟨h, hCadj hh⟩ := rfl
      rw [e, map_mul, Subgroup.coe_mul, ihg, ihh, map_mul]
    | inv g hg ihg =>
      have e : (⟨g⁻¹, hCadj (inv_mem hg)⟩ : adjointGroup τ k) = (⟨g, hCadj hg⟩)⁻¹ := rfl
      rw [e, map_inv, Subgroup.coe_inv, ihg, map_inv]
  exact key _ (D.rootSpanJ_le_closure hx)

theorem finite_entrywise_fixed {N : ℕ} (hN : 0 < N) :
    {g : ModGL τ k | Units.map (entrywiseHom (iterateFrobenius k p₀ N)) g = g}.Finite :=
  OrthogonalSemilinearFixedRootDatum.finite_entrywise_fixed hN

theorem F_pow_eq_self {x : adjointGroup τ k} (hx : D.F x = x) (m : ℕ) : (D.F ^ m) x = x := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ', MulAut.mul_apply, ih, hx]

theorem finite_fixedGroup : Finite D.fixedGroup := by
  obtain ⟨n, hn, hFn⟩ := D.exists_F_pow_eq_entrywise
  have hfin := finite_entrywise_fixed (τ := τ) (k := k) (p₀ := p₀) (N := D.e * n)
    (Nat.mul_pos D.one_le_e hn)
  have : Finite ↥{g : ModGL τ k |
      Units.map (entrywiseHom (iterateFrobenius k p₀ (D.e * n))) g = g} := hfin.to_subtype
  have hmem : ∀ x : D.fixedGroup, ((x : adjointGroup τ k) : ModGL τ k) ∈
      {g : ModGL τ k | Units.map (entrywiseHom (iterateFrobenius k p₀ (D.e * n))) g = g} := by
    rintro ⟨x, hx⟩
    obtain ⟨hxS, hxF⟩ := Subgroup.mem_inf.1 hx
    show Units.map (entrywiseHom (iterateFrobenius k p₀ (D.e * n))) (x : ModGL τ k) = x
    rw [← hFn x (Subgroup.mem_subgroupOf.1 hxS), D.F_pow_eq_self hxF]
  exact Finite.of_injective (fun x : D.fixedGroup => (⟨_, hmem x⟩ : ↥{g : ModGL τ k |
      Units.map (entrywiseHom (iterateFrobenius k p₀ (D.e * n))) g = g}))
    fun x y h => Subtype.ext (Subtype.ext (by
      have := congrArg Subtype.val h
      exact this))

end GenFixedRootDatum

end CFSG.RankThree.Lattice
