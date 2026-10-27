module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBFrameChange
public import CFSG.LocalAnalysis.StandardType.GGTBJWeylParabolicLE3
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LocalAnalysis.StandardType.GGTWReflConj
public import CFSG.LocalAnalysis.StandardType.GGResIICell
public import CFSG.Permutation.SupportedAdjacent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Monster.B.Geometry SpCoord

namespace TypeBDatum

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem tbT_mem_closure_singleton_eq {E : Type} [Group E] {g t : E}
    (hg : g * g = 1) (ht : t ∈ Subgroup.closure ({g} : Set E)) : t = 1 ∨ t = g := by
  refine Subgroup.closure_induction (p := fun (t : E) (_ : t ∈ Subgroup.closure ({g} : Set E)) =>
    t = 1 ∨ t = g) ?_ ?_ ?_ ?_ ht
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact Or.inr hx
  · exact Or.inl rfl
  · intro x y hx hy ihx ihy
    rcases ihx with hx1 | hxg <;> rcases ihy with hy1 | hyg
    · exact Or.inl (by simp [hx1, hy1])
    · exact Or.inr (by simp [hx1, hyg])
    · exact Or.inr (by simp [hxg, hy1])
    · exact Or.inl (by rw [hxg, hyg]; exact hg)
  · intro x hx ih
    rcases ih with hx1 | hxg
    · exact Or.inl (by rw [hx1]; exact inv_one)
    · exact Or.inr (by rw [hxg]; exact inv_eq_of_mul_eq_one_right hg)

private theorem tbT_refl_ne_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {φ : MulAut ↥Bs} (hr : GGIsReflection p φ) : φ ≠ 1 := by
  haveI : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
  haveI : Nonempty ↥Bs := ⟨(1 : ↥Bs)⟩
  rintro rfl
  obtain ⟨-, hc⟩ := hr
  simp only [MulAut.one_apply] at hc
  have hc' : Nat.card {b : ↥Bs // True} * p = Nat.card ↥Bs := by simpa using hc
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)] at hc'
  have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  nlinarith

private theorem tbT_reflConjSimple_subsingleton {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {Λ : Type} [Nonempty Λ]
    (φ : Λ → MulAut ↥Bs) (hA : A = Subgroup.closure (Set.range φ))
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hsub : Subsingleton Λ) :
    GGReflConjSimple p A φ := by
  let i₀ : Λ := Classical.arbitrary Λ
  intro t ht hr
  rw [hA] at ht
  have hrange : Set.range φ = {φ i₀} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg φ (hsub.allEq i i₀))
    · rintro rfl
      exact ⟨i₀, rfl⟩
  rw [hrange] at ht
  have hg : φ i₀ * φ i₀ = 1 := by
    have h := (hrefl i₀).1
    simpa [pow_two] using h
  have ht' : t = 1 ∨ t = φ i₀ := tbT_mem_closure_singleton_eq hg ht
  rcases ht' with h | h
  · exact absurd h (tbT_refl_ne_one hr)
  · exact ⟨1, Subgroup.one_mem _, i₀, by rw [h]; group⟩

private lemma tbT_A_apply {n : ℕ} (i j : Fin n) :
    (CoxeterMatrix.A n) i j =
      (if i = j then 1
        else if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then 3 else 2) := by
  rw [CoxeterMatrix.A]
  simp only [CoxeterMatrix.M, Matrix.of_apply]
  split_ifs <;> omega

private lemma tbT_B_apply {n : ℕ} (i j : Fin n) :
    (CoxeterMatrix.B n) i j =
      (if i = j then 1
        else if ((i : ℕ) = n - 1 ∧ (j : ℕ) = n - 2) ∨
          ((j : ℕ) = n - 1 ∧ (i : ℕ) = n - 2) then 4
        else if ((i : ℕ) + 1 = (j : ℕ)) ∨ ((j : ℕ) + 1 = (i : ℕ)) then 3 else 2) := by
  rw [CoxeterMatrix.B]
  simp only [Matrix.of_apply]
  split_ifs <;> omega

private theorem tbT_isWeyl_B (m : ℕ) (hm : 2 ≤ m) : GGIsWeylMatrix (CoxeterMatrix.B m) :=
  Or.inl ⟨m, Equiv.refl _, by omega, Or.inr (Or.inl ⟨hm, by
    ext i j; simp [CoxeterMatrix.reindex_apply]⟩)⟩

private theorem tbT_permSupportedAut_Hd_eq_adjacent {m p b : ℕ} (hb : 2 ≤ b) (hbm : b ≤ m) :
    permSupportedAut m p (Finset.univ.image (Fin.castLE hbm)) =
      Subgroup.closure (Set.range fun j : Fin (b - 1) =>
        permAut (p := p) (Equiv.swap (Fin.castLE (by omega : b - 1 + 1 ≤ m) j.castSucc)
          (Fin.castLE (by omega : b - 1 + 1 ≤ m) j.succ))) := by
  classical
  let Hd : Finset (Fin m) := Finset.univ.image (Fin.castLE hbm)
  change permSupportedAut m p Hd = _
  let eHd : Fin b ≃ Hd :=
    { toFun := fun i => ⟨Fin.castLE hbm i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
      invFun := fun x => ⟨x.1.val, by
        rcases Finset.mem_image.mp x.2 with ⟨i, -, hi⟩
        rw [← hi]; exact i.isLt⟩
      left_inv := fun i => by ext; rfl
      right_inv := fun x => by ext; rfl }
  let e : Fin (b - 1 + 1) ≃ Hd := (finCongr (by omega : b - 1 + 1 = b)).trans eHd
  have hfix :=
    CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_closure_adjacent Hd e
  have hmapfix : permSupportedAut m p Hd =
      (fixingSubgroup (Equiv.Perm (Fin m)) ((Hd : Set (Fin m))ᶜ)).map
        (permAutHom m p) := by
    apply le_antisymm
    · rw [permSupportedAut, Subgroup.closure_le]
      rintro σ ⟨a, ha, b', hb', hab, rfl⟩
      exact Subgroup.mem_map.mpr ⟨Equiv.swap a b', by
        rw [mem_fixingSubgroup_iff]
        intro x hx
        exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h ▸ ha)) (fun h => hx (h ▸ hb')), rfl⟩
    · rw [hfix, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨j, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨(e j.castSucc : Fin m), (e j.castSucc).2,
        (e j.succ : Fin m), (e j.succ).2, ?_, rfl⟩
      intro h
      have hv := congrArg Fin.val h
      simp [e, eHd, finCongr] at hv
  have hgen : (fun j : Fin (b - 1) =>
        (permAutHom m p) (Equiv.swap (e j.castSucc) (e j.succ))) =
      (fun j : Fin (b - 1) =>
        permAut (p := p) (Equiv.swap (Fin.castLE (by omega : b - 1 + 1 ≤ m) j.castSucc)
          (Fin.castLE (by omega : b - 1 + 1 ≤ m) j.succ))) := by
    funext j
    apply congrArg (fun x => permAut (p := p) x)
    apply congrArg₂ Equiv.swap <;> exact Fin.ext rfl
  rw [hmapfix, hfix, MonoidHom.map_closure, ← Set.range_comp]
  change Subgroup.closure (Set.range fun j : Fin (b - 1) =>
    (permAutHom m p) (Equiv.swap (e j.castSucc) (e j.succ))) = _
  rw [hgen]

open CFSG.Permutation.TranspositionCentralizer in
private theorem tbT_parabolicRestricted
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    {M : CoxeterMatrix (Fin n)} {φ : Fin n → MulAut ↥Bs}
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range (φ ∘ Fin.castLE hkn)))
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hBs : IsElemAbelian p Bs)
    {Jset : Set (Fin n)} [Fintype Jset] [DecidableEq Jset]
    (hJlt : ∀ j : Jset, j.val.val < k) (eJ : Jset ≃ Fin k)
    (hcast : ∀ i : Fin k, ((eJ.symm i : Jset) : Fin n) = Fin.castLE hkn i)
    (hMJ_eq : parMatrix M Jset = (CoxeterMatrix.A k).reindex eJ.symm) :
    (∃ fJ : (parMatrix M Jset).Group ≃* ↥(ggAutomizer J Bs),
        ∀ j : Jset, (fJ ((parMatrix M Jset).simple j) : MulAut ↥Bs) = φ j) ∧
      (ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Jset => φ j)) ∧
      GGReflConjSimple p (ggAutomizer J Bs) (fun j : Jset => φ j) := by
  classical
  let MJ : CoxeterMatrix Jset := parMatrix M Jset
  let cs := M.toCoxeterSystem
  let gSub : MJ.Group →* ↥(ggAutomizer X Bs) := f.toMonoidHom.comp (parToGroup cs Jset)
  let g : MJ.Group →* MulAut ↥Bs := (Subgroup.subtype (ggAutomizer X Bs)).comp gSub
  have hg_simple : ∀ j : Jset, g (MJ.simple j) = φ j := by
    intro j
    change (f (parToGroup cs Jset (MJ.simple j)) : MulAut Bs) = _
    rw [parToGroup_simple]
    exact hf j
  have hg_inj : Function.Injective g := by
    intro x y h
    exact f.injective.comp (parToGroup_injective cs Jset) (Subtype.ext h)
  have hg_mem : ∀ x : MJ.Group, g x ∈ ggAutomizer J Bs := by
    have hle : Subgroup.closure (Set.range (MJ.simple)) ≤
        Subgroup.comap g (ggAutomizer J Bs) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      change g (MJ.simple j) ∈ ggAutomizer J Bs
      rw [hg_simple, hJ]
      have hj : j.val.val < k := hJlt j
      let i : Fin k := ⟨j.val.val, hj⟩
      have hi : Fin.castLE hkn i = j.val := by ext; rfl
      rw [← hi]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    intro x
    have hx : x ∈ Subgroup.closure (Set.range (MJ.simple)) := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple,
        (MJ.toCoxeterSystem).subgroup_closure_range_simple]
      exact Subgroup.mem_top x
    exact hle hx
  let g' : MJ.Group →* ↥(ggAutomizer J Bs) :=
    { toFun := fun x => ⟨g x, hg_mem x⟩
      map_one' := by ext; simp [g]
      map_mul' := by intro x y; ext; simp [g] }
  have hg'_inj : Function.Injective g' := by
    intro x y hxy
    apply hg_inj
    exact congrArg (fun z : ggAutomizer J Bs => (z : MulAut Bs)) hxy
  have hg'_surj : Function.Surjective g' := by
    intro y
    have hy : (y : MulAut ↥Bs) ∈ Subgroup.closure
        (Set.range (φ ∘ Fin.castLE hkn)) := by
      rw [← hJ]
      exact y.property
    have h : ∃ a : MJ.Group, (g' a : MulAut ↥Bs) = (y : MulAut ↥Bs) := by
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
      · intro x hx
        rcases hx with ⟨i, rfl⟩
        refine ⟨MJ.simple (eJ.symm i), ?_⟩
        change g (MJ.simple (eJ.symm i)) = φ (Fin.castLE _ i)
        rw [hg_simple]
        exact congrArg φ (hcast i)
      · exact ⟨1, by change g 1 = 1; exact g.map_one⟩
      · intro x z hx hz ihx ihz
        rcases ihx with ⟨a, ha⟩
        rcases ihz with ⟨b, hb'⟩
        refine ⟨a * b, ?_⟩
        change g (a * b) = x * z
        rw [map_mul]
        exact congrArg₂ (· * ·) ha hb'
      · intro x hx ih
        rcases ih with ⟨a, ha⟩
        refine ⟨a⁻¹, ?_⟩
        change g a⁻¹ = x⁻¹
        rw [map_inv]
        exact congrArg Inv.inv ha
    rcases h with ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  let fJ : MJ.Group ≃* ↥(ggAutomizer J Bs) :=
    MulEquiv.ofBijective g' ⟨hg'_inj, hg'_surj⟩
  have hfJ : ∀ j : Jset, (fJ (MJ.simple j) : MulAut ↥Bs) = φ j := fun j => hg_simple j
  have hALJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Jset => φ j) := by
    rw [hJ]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨eJ.symm i, ?_⟩
      exact congrArg φ (hcast i)
    · rintro ⟨j, rfl⟩
      refine ⟨eJ j, ?_⟩
      have h := hcast (eJ j)
      rw [Equiv.symm_apply_apply] at h
      exact congrArg φ h.symm
  have hconjJ : GGReflConjSimple p (ggAutomizer J Bs) (fun j : Jset => φ j) := by
    by_cases hsmall : k = 1
    · haveI : Nonempty Jset := ⟨eJ.symm ⟨0, by omega⟩⟩
      have hsub : Subsingleton Jset := ⟨fun a b => eJ.injective (Fin.ext (by
        have ha := (eJ a).isLt
        have hb := (eJ b).isLt
        omega))⟩
      exact tbT_reflConjSimple_subsingleton (fun j : Jset => φ j) hALJ
        (fun j => hrefl j.val) hsub
    · have h2 : 2 ≤ k := by omega
      intro s hs hr
      exact ggTW_refl_conj_of_typeA hp h2 hBs eJ.symm hMJ_eq
        (ggAutomizer J Bs) fJ (fun j : Jset => φ j) hfJ (fun j => hrefl j.val) s hs hr
  exact ⟨⟨fJ, hfJ⟩, hALJ, hconjJ⟩

theorem ggTBJTypeB_sideDatum_twistedPerm {G : Type} [Group G] [Finite G] {p m : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hm : 2 ≤ m) {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    {W₀ : Type} [Group W₀] (Θ : ((Fin m → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs)
    (hX : ggAutomizer X Bs = (signedAut m p).map (liftBs Θ))
    {S : Finset (Fin m)} (hS : 2 ≤ S.card) (hc3 : m + 1 - S.card ≤ 3)
    {s : Fin m → ZMod p} (hs : ∀ i, s i * s i = 1)
    (hJ : ggAutomizer J Bs =
      (twistedPermAut m p S s hs).map (liftBs Θ)) :
    (m + 1 - S.card = 1 → GGResSideDatum p Bs X J) ∧
      (2 ≤ m + 1 - S.card → GGResLeviSideDatumLE3 p Bs X J) := by
  classical
  set b : ℕ := S.card with hb
  have hb2 : 2 ≤ b := by rw [hb]; exact hS
  have hbm : b ≤ m := by rw [hb]; simpa using Finset.card_le_univ S
  let T : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => b - 1 ≤ i.val)
  let Jset : Set (Fin m) := {j : Fin m | j ∉ T}
  have hJlt : ∀ j : Jset, j.1.val < b - 1 := by
    intro j
    have hj : ¬ (b - 1 ≤ j.1.val) := by
      intro hle
      exact j.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
    omega
  let eJ : Jset ≃ Fin (b - 1) :=
    { toFun := fun j => ⟨j.1.val, hJlt j⟩
      invFun := fun i => ⟨⟨i.val, by omega⟩, by
        intro hmem
        have hle : b - 1 ≤ i.val := (Finset.mem_filter.mp hmem).2
        omega⟩
      left_inv := fun j => by ext; rfl
      right_inv := fun i => by ext; rfl }
  have hcast : ∀ i : Fin (b - 1),
      ((eJ.symm i : Jset) : Fin m) = Fin.castLE (by omega : b - 1 ≤ m) i :=
    fun i => Fin.ext rfl
  have hcardS : Nat.card S = b := by rw [hb, Nat.card_eq_finsetCard]
  let eS : Fin b ≃ S := (Finite.equivFinOfCardEq hcardS).symm
  let first : Fin b ↪ Fin m := ⟨Fin.castLE hbm, Fin.castLE_injective _⟩
  let enumerated : Fin b ↪ Fin m := eS.toEmbedding.trans (Function.Embedding.subtype (· ∈ S))
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_smul_eq_embedding first enumerated
  have hτi : ∀ i : Fin b, τ (first i) = (eS i : Fin m) := by
    intro i
    have hh := congrArg (fun e : Fin b ↪ Fin m => e i) hτ
    simpa only [Function.Embedding.smul_apply, Equiv.Perm.smul_def, enumerated,
      Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Function.Embedding.coe_subtype,
      first] using hh
  have hHdτ : (Finset.univ.image (Fin.castLE hbm)).image τ = S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨i, -, rfl⟩
      change τ (first i) ∈ S
      rw [hτi i]
      exact (eS i).2
    · intro hx
      refine Finset.mem_image.mpr ⟨first (eS.symm ⟨x, hx⟩), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨eS.symm ⟨x, hx⟩, Finset.mem_univ _, rfl⟩
      · change τ (first (eS.symm ⟨x, hx⟩)) = x
        rw [hτi (eS.symm ⟨x, hx⟩)]; simp
  let D : MulAut (Fin m → Multiplicative (ZMod p)) := diagAut s hs
  let N : MulAut (Fin m → Multiplicative (ZMod p)) := permAut (p := p) τ
  let P : MulAut (Fin m → Multiplicative (ZMod p)) := D * N
  let Θ' : ((Fin m → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs :=
    (MulEquiv.prodCongr P (MulEquiv.refl W₀)).trans Θ
  have hlift : liftBs (Bs := Bs) Θ' =
      (liftBs (Bs := Bs) Θ).comp (MulAut.conj P).toMonoidHom :=
    liftBs_prodCongr Θ P
  have hD_mem : D ∈ signedAut m p := by
    refine mem_of_isSignedPerm ?_ ?_ ?_
    · intro i
      exact Subgroup.subset_closure (Or.inl ⟨i, Finset.mem_univ i, rfl⟩)
    · intro a b hab
      exact Subgroup.subset_closure (Or.inr ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩)
    · exact ⟨1, s, fun i => sign_of_sq_one (hs i), fun f i => by
        rw [Equiv.Perm.one_apply, diagAut_apply, toAdd_ofAdd]⟩
  have hN_mem : N ∈ signedAut m p := by
    refine mem_of_isSignedPerm ?_ ?_ (isSignedPerm_permAut τ)
    · intro i
      exact Subgroup.subset_closure (Or.inl ⟨i, Finset.mem_univ i, rfl⟩)
    · intro a b hab
      exact Subgroup.subset_closure (Or.inr ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩)
  have hP_mem : P ∈ signedAut m p := Subgroup.mul_mem _ hD_mem hN_mem
  have hX' : ggAutomizer X Bs = (signedAut m p).map (liftBs Θ') := by
    rw [hX, hlift, ← Subgroup.map_map, l05nBL_closure_conj (signedAut m p) P hP_mem]
  have hSN : permSupportedAut m p S =
      (permSupportedAut m p (Finset.univ.image (Fin.castLE hbm))).map
        (MulAut.conj N).toMonoidHom := by
    rw [← hHdτ]
    exact (permSupportedAut_map_conj τ (Finset.univ.image (Fin.castLE hbm))).symm
  have hJ'_orig : ggAutomizer J Bs =
      (permSupportedAut m p (Finset.univ.image (Fin.castLE hbm))).map (liftBs Θ') := by
    rw [hJ, hlift]
    calc (twistedPermAut m p S s hs).map (liftBs Θ)
        = ((permSupportedAut m p S).map (MulAut.conj D).toMonoidHom).map (liftBs Θ) := by
            rw [show twistedPermAut m p S s hs =
              (permSupportedAut m p S).map (MulAut.conj D).toMonoidHom from rfl]
      _ = (permSupportedAut m p S).map ((liftBs Θ).comp (MulAut.conj D).toMonoidHom) := by
            rw [Subgroup.map_map]
      _ = ((permSupportedAut m p (Finset.univ.image (Fin.castLE hbm))).map
              (MulAut.conj N).toMonoidHom).map
              ((liftBs Θ).comp (MulAut.conj D).toMonoidHom) := by rw [hSN]
      _ = (permSupportedAut m p (Finset.univ.image (Fin.castLE hbm))).map
              (((liftBs Θ).comp (MulAut.conj D).toMonoidHom).comp
                (MulAut.conj N).toMonoidHom) := by rw [Subgroup.map_map]
      _ = (permSupportedAut m p (Finset.univ.image (Fin.castLE hbm))).map
              ((liftBs Θ).comp (MulAut.conj P).toMonoidHom) := by
            have hhom : ((liftBs Θ).comp (MulAut.conj D).toMonoidHom).comp
                (MulAut.conj N).toMonoidHom =
                (liftBs Θ).comp (MulAut.conj P).toMonoidHom := by
              ext x
              simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
              rw [conj_apply_comp D N x]
            rw [hhom]
  obtain ⟨V, instV, instMod, ι, φ, h, α, C, hMC, hlin, hrefl, hpair, ⟨f, hf⟩, hclos,
    hφexplicit⟩ :=
    exists_typeB_datum_of_signedAut (G := G) (p := p) (m := m) hp2 hm hBs Θ' hX'
  letI : AddCommGroup V := instV
  letI : Module (ZMod p) V := instMod
  have hφswap : ∀ i : Fin (b - 1),
      φ (Fin.castLE (by omega : b - 1 ≤ m) i) =
        (liftBs Θ') (permAut (p := p) (Equiv.swap
          (Fin.castLE (by omega : b - 1 + 1 ≤ m) i.castSucc)
          (Fin.castLE (by omega : b - 1 + 1 ≤ m) i.succ))) := by
    intro i
    rw [hφexplicit (Fin.castLE (by omega : b - 1 ≤ m) i),
      dif_pos (by have h := i.isLt; simp only [Fin.val_castLE]; omega)]
    exact (congrArg (liftBs Θ') (congrArg₂ (fun x y => permAut (p := p) (Equiv.swap x y))
      (Fin.ext rfl) (Fin.ext rfl))).symm
  have hJ_fin : ggAutomizer J Bs = Subgroup.closure
      (Set.range (φ ∘ Fin.castLE (by omega : b - 1 ≤ m))) := by
    rw [hJ'_orig, tbT_permSupportedAut_Hd_eq_adjacent hb2 hbm]
    rw [MonoidHom.map_closure, ← Set.range_comp]
    apply congrArg Subgroup.closure
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, hφswap i⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, (hφswap i).symm⟩
  have hMJ_eq : parMatrix (CoxeterMatrix.B m) Jset =
      (CoxeterMatrix.A (b - 1)).reindex eJ.symm := by
    ext j j'
    rw [parMatrix_apply, CoxeterMatrix.reindex_apply, Equiv.symm_symm]
    change (CoxeterMatrix.B m) j.1 j'.1 =
      (CoxeterMatrix.A (b - 1)) ⟨j.1.val, hJlt j⟩ ⟨j'.1.val, hJlt j'⟩
    by_cases hij : j.1 = j'.1
    · have hjj : j = j' := Subtype.ext hij
      subst hjj
      rw [tbT_B_apply, tbT_A_apply]
      simp
    · have hij' : (⟨j.1.val, hJlt j⟩ : Fin (b - 1)) ≠ ⟨j'.1.val, hJlt j'⟩ :=
        fun h => hij (Fin.ext (by simpa using congrArg Fin.val h))
      have h4 : ¬ (((j.1 : ℕ) = m - 1 ∧ (j'.1 : ℕ) = m - 2) ∨
          ((j'.1 : ℕ) = m - 1 ∧ (j.1 : ℕ) = m - 2)) := by
        rintro (⟨h, -⟩ | ⟨h, -⟩)
        · have hj := hJlt j; omega
        · have hj := hJlt j'; omega
      rw [tbT_B_apply, tbT_A_apply, if_neg hij, if_neg h4, if_neg hij']
  have hWM : GGIsWeylMatrix (CoxeterMatrix.B m) := tbT_isWeyl_B m hm
  have hWMJ : GGIsWeylMatrix (parMatrix (CoxeterMatrix.B m) Jset) := by
    rw [hMJ_eq]
    exact l05nBL_weyl_reindex (ggResII_isWeyl_A (by omega : 1 ≤ b - 1)) eJ.symm
  obtain ⟨⟨fJ, hfJ⟩, hALJ, hconjJ⟩ :=
    tbT_parabolicRestricted (p := p) (X := X) (J := J) (f := f) (M := CoxeterMatrix.B m)
      hp2 (by omega : 1 ≤ b - 1) (by omega : b - 1 ≤ m) hf hJ_fin hrefl hBs
      hJlt eJ hcast hMJ_eq
  have hTcard : T.card = m + 1 - S.card := by
    have h1 : T.card = Fintype.card {i : Fin m // b - 1 ≤ i.val} := by
      rw [show T = Finset.univ.filter (fun i : Fin m => b - 1 ≤ i.val) from rfl]
      exact (Fintype.card_subtype (p := fun i : Fin m => b - 1 ≤ i.val)).symm
    rw [h1]
    have h2 : Fintype.card {i : Fin m // b - 1 ≤ i.val} = m + 1 - b := by
      let ef : {i : Fin m // b - 1 ≤ i.val} ≃ Fin (m + 1 - b) :=
        { toFun := fun i => ⟨i.1.val - (b - 1), by have := i.2; omega⟩
          invFun := fun j => ⟨⟨b - 1 + j.val, by have := j.isLt; omega⟩, by
            show b - 1 ≤ b - 1 + j.val; omega⟩
          left_inv := fun i => by ext; simp only [Fin.val_mk]; have := i.2; omega
          right_inv := fun j => by ext; simp only [Fin.val_mk]; omega }
      exact (Fintype.card_congr ef).trans (Fintype.card_fin _)
    rw [h2, hb]
  have hT1 : 1 ≤ T.card := by rw [hTcard]; omega
  have hT3 : T.card ≤ 3 := by rw [hTcard]; exact hc3
  have hres := ggTBJWeylParabolicLE3 (G := G) (p := p) (Bs := Bs) (X := X) (J := J)
    (Λ := Fin m) (M := CoxeterMatrix.B m) (C := C) hWM hMC
    (ι := ι) (φ := φ) (h := h) (α := α) hlin hrefl hpair (f := f) hf hclos
    T hT1 hT3 hALJ hWMJ hconjJ
  constructor
  · intro hc1
    obtain ⟨b', hb'⟩ := Finset.card_eq_one.mp (by rw [hTcard]; exact hc1)
    exact hres.1 b' hb'
  · intro hc2
    exact hres.2 (by rw [hTcard]; exact hc2)

end TypeBDatum

end CFSG.StandardType

end
