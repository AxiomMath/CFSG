module

public import CFSG.RankThree.Chevalley.SteinbergBID4Restrict

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

variable (K) in
@[expose] def d4TorusHom : (Fin 4 → Kˣ) →* ModGL Tag.E6 K :=
  MonoidHom.noncommPiCoprod (fun k : Fin 4 => torusEltHom Tag.E6 K (d4Idx k))
    (fun i j _ t u => torusElt_mul_comm (d4Idx i) (d4Idx j) t u)

theorem d4TorusHom_mulSingle (k : Fin 4) (s : Kˣ) :
    d4TorusHom K (Pi.mulSingle k s) = torusElt Tag.E6 K (d4Idx k) s :=
  MonoidHom.noncommPiCoprod_mulSingle (fun k : Fin 4 => torusEltHom Tag.E6 K (d4Idx k)) k s

theorem d4TorusHom_apply (t : Fin 4 → Kˣ) :
    d4TorusHom K t = torusElt Tag.E6 K 1 (t 0) * torusElt Tag.E6 K 2 (t 1) *
      torusElt Tag.E6 K 3 (t 2) * torusElt Tag.E6 K 4 (t 3) := by
  have ht : t = Pi.mulSingle 0 (t 0) * Pi.mulSingle 1 (t 1) * Pi.mulSingle 2 (t 2) *
      Pi.mulSingle 3 (t 3) := by
    funext k
    fin_cases k <;> simp
  conv_lhs => rw [ht]
  rw [map_mul, map_mul, map_mul, d4TorusHom_mulSingle, d4TorusHom_mulSingle,
    d4TorusHom_mulSingle, d4TorusHom_mulSingle]
  rfl

theorem d4TorusHom_mem_torusGroup (t : Fin 4 → Kˣ) :
    d4TorusHom K t ∈ torusGroup Tag.E6 K := by
  rw [d4TorusHom_apply]
  exact mul_mem (mul_mem (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
    (torusElt_mem_torusGroup _ _)) (torusElt_mem_torusGroup _ _)

abbrev e6Pair (i : Fin Tag.E6.rank) (α : Fin Tag.E6.rank → ℤ) : ℤ := ∑ j, Tag.E6.cartan i j * α j

theorem torusRootChar_d4TorusHom (t : Fin 4 → Kˣ) {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) :
    torusRootChar (d4TorusHom K t) α = ((t 0 ^ e6Pair 1 α * t 1 ^ e6Pair 2 α *
      t 2 ^ e6Pair 3 α * t 3 ^ e6Pair 4 α : Kˣ) : K) := by
  have hd : ∀ (i : Fin Tag.E6.rank) (s : Kˣ), torusElt Tag.E6 K i s ∈ diagonalGroup := fun i s =>
    torusGroup_le_diagonalGroup (torusElt_mem_torusGroup i s)
  rw [d4TorusHom_apply, torusRootChar_mul (mul_mem (mul_mem (hd _ _) (hd _ _)) (hd _ _)) (hd _ _),
    torusRootChar_mul (mul_mem (hd _ _) (hd _ _)) (hd _ _), torusRootChar_mul (hd _ _) (hd _ _),
    torusRootChar_torusElt _ _ hα, torusRootChar_torusElt _ _ hα, torusRootChar_torusElt _ _ hα,
    torusRootChar_torusElt _ _ hα]
  simp only [Units.val_mul]

theorem e6Pair_single (i l : Fin Tag.E6.rank) : e6Pair i (Pi.single l 1) = Tag.E6.cartan i l := by
  rw [e6Pair, Finset.sum_eq_single l (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
    (fun h => absurd (Finset.mem_univ l) h), Pi.single_eq_same, mul_one]

theorem range_d4TorusHom : (d4TorusHom K).range = supportedTorus Tag.E6 K d4Support := by
  rw [supportedTorus_eq_subsystemTorus]
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨t, rfl⟩
    rw [d4TorusHom_apply]
    have h : ∀ k : Fin 4, ∀ s : Kˣ,
        torusElt Tag.E6 K (d4Idx k) s ∈ subsystemTorus Tag.E6 K d4Support := fun k s =>
      torusElt_mem_subsystemTorus (d4Idx_mem k) s
    exact mul_mem (mul_mem (mul_mem (h 0 _) (h 1 _)) (h 2 _)) (h 3 _)
  · rintro _ ⟨i, hi, s, rfl⟩
    obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
    exact ⟨Pi.mulSingle k s, d4TorusHom_mulSingle k s⟩

theorem d4TorusHom_injective : Function.Injective (d4TorusHom K) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have e : ∀ l : Fin Tag.E6.rank, t 0 ^ Tag.E6.cartan 1 l * t 1 ^ Tag.E6.cartan 2 l *
      t 2 ^ Tag.E6.cartan 3 l * t 3 ^ Tag.E6.cartan 4 l = 1 := fun l => by
    have h := torusRootChar_d4TorusHom t (isRoot_single Tag.E6 l)
    rw [ht, torusRootChar_one, e6Pair_single, e6Pair_single, e6Pair_single, e6Pair_single] at h
    exact Units.ext h.symm
  have e0 := e 0
  have e5 := e 5
  have e2 := e 2
  have e3 := e 3
  simp only [show Tag.E6.cartan 1 0 = 0 by decide, show Tag.E6.cartan 2 0 = -1 by decide,
    show Tag.E6.cartan 3 0 = 0 by decide, show Tag.E6.cartan 4 0 = 0 by decide,
    show Tag.E6.cartan 1 5 = 0 by decide, show Tag.E6.cartan 2 5 = 0 by decide,
    show Tag.E6.cartan 3 5 = 0 by decide, show Tag.E6.cartan 4 5 = -1 by decide,
    show Tag.E6.cartan 1 2 = 0 by decide, show Tag.E6.cartan 2 2 = 2 by decide,
    show Tag.E6.cartan 3 2 = -1 by decide, show Tag.E6.cartan 4 2 = 0 by decide,
    show Tag.E6.cartan 1 3 = -1 by decide, show Tag.E6.cartan 2 3 = -1 by decide,
    show Tag.E6.cartan 3 3 = 2 by decide, show Tag.E6.cartan 4 3 = -1 by decide,
    zpow_zero, zpow_neg, zpow_one, one_mul, mul_one] at e0 e5 e2 e3
  have h1 : t 1 = 1 := inv_eq_one.1 e0
  have h3 : t 3 = 1 := inv_eq_one.1 e5
  simp only [h1, one_zpow, one_mul, inv_eq_one] at e2
  simp only [h1, h3, e2, inv_one, one_zpow, mul_one, inv_eq_one] at e3
  funext k
  fin_cases k
  · exact e3
  · exact h1
  · exact e2
  · exact h3

theorem d4Res_eq_one_iff (g : subsystemGroup Tag.E6 K d4Support) :
    d4Res K g = 1 ↔
      ∀ v, ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (d4Emb K v) = d4Emb K v := by
  constructor
  · intro h v
    rw [d4Res_apply, h, Units.val_one, Module.End.one_apply]
  · intro h
    exact d4Res_eq fun v => by rw [h, Units.val_one, Module.End.one_apply]

theorem apply_rootVec_d4Lat_of_d4Res_eq_one {g : subsystemGroup Tag.E6 K d4Support}
    (hg : d4Res K g = 1) (β : Fin Tag.D4.rank → ℤ) :
    ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K (d4Lat β)) =
      rootVec Tag.E6 K (d4Lat β) := by
  rw [← d4Emb_rootVec]
  exact (d4Res_eq_one_iff g).1 hg _

theorem eq_of_not_precedes_of_not_precedes_neg {β γ β' γ' : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) (hγ : IsRoot Tag.E6 γ) (hβ' : IsRoot Tag.E6 β')
    (hγ' : IsRoot Tag.E6 γ') (eβ : β' = -β) (eγ : γ' = -γ)
    (h1 : ¬Label.Precedes (Sum.inr ⟨β, hβ⟩ : Label Tag.E6) (Sum.inr ⟨γ, hγ⟩))
    (h2 : ¬Label.Precedes (Sum.inr ⟨β', hβ'⟩ : Label Tag.E6) (Sum.inr ⟨γ', hγ'⟩)) : γ = β := by
  subst eβ eγ
  simp only [Label.Precedes, Label.weight, height_neg, not_or, not_and, not_lt] at h1 h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have hh : height β = height γ := by omega
  have l1 : toLex γ ≤ toLex β := not_lt.1 (h1b hh)
  have l2 : toLex (-γ) ≤ toLex (-β) := not_lt.1 (h2b (by rw [hh]))
  have l2' : toLex β ≤ toLex γ := neg_le_neg_iff.1 l2
  exact toLex.injective (le_antisymm l1 l2')

theorem not_precedes_of_apply_eq_borel {n b : ModGL Tag.E6 K} (hb : b ∈ borelGroup Tag.E6 K)
    {w : WeylGroup Tag.E6} (hn : MapsRootLines n w) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β)
    (h : (n : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β) =
      (b : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β)) :
    ¬Label.Precedes (Sum.inr ⟨β, hβ⟩ : Label Tag.E6) (Sum.inr ⟨w • β, IsRoot.smul hβ w⟩) := by
  intro hp
  obtain ⟨c, hc⟩ := hn β hβ
  have h0 := (triangular_borel_structure.{0, 0} Tag.E6 K).2.2.2.2.2.2.2.2.2.1 b hb _ _ hp
  rw [← rootVec_eq_single_of_isRoot hβ, ← h, hc, rootVec_eq_single_of_isRoot (IsRoot.smul hβ w),
    Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h0
  exact c.ne_zero h0

theorem smul_eq_of_mem_parabolicWeylGroup_of_pair {J : Set (Fin Tag.E6.rank)}
    {w : WeylGroup Tag.E6} (hw : w ∈ parabolicWeylGroup Tag.E6 J) {v : Fin Tag.E6.rank → ℤ}
    (hv : ∀ j ∈ J, ∑ k, Tag.E6.cartan j k * v k = 0) : w • v = v := by
  have hle : parabolicWeylGroup Tag.E6 J ≤ MulAction.stabilizer (WeylGroup Tag.E6) v := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, simple_smul, reflect, hv j hj, zero_smul,
      sub_zero]
  exact hle hw

@[expose] def d4OrthoFirst : Fin Tag.E6.rank → ℤ := (![2, 1, 2, 2, 1, 0] : Fin 6 → ℤ)

@[expose] def d4OrthoLast : Fin Tag.E6.rank → ℤ := (![0, 1, 1, 2, 2, 2] : Fin 6 → ℤ)

theorem pair_d4Ortho : ∀ j : Fin Tag.E6.rank, j ≠ 0 → j ≠ 5 →
    ∑ k, Tag.E6.cartan j k * d4OrthoFirst k = 0 ∧ ∑ k, Tag.E6.cartan j k * d4OrthoLast k = 0 := by
  decide

theorem two_single_zero_eq : (Pi.single 0 1 + Pi.single 0 1 : Fin Tag.E6.rank → ℤ) =
    d4OrthoFirst - (Pi.single 1 1 + Pi.single 2 1 + Pi.single 2 1 + Pi.single 3 1 +
      Pi.single 3 1 + Pi.single 4 1) := by
  decide

theorem two_single_five_eq : (Pi.single 5 1 + Pi.single 5 1 : Fin Tag.E6.rank → ℤ) =
    d4OrthoLast - (Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 3 1 +
      Pi.single 4 1 + Pi.single 4 1) := by
  decide

theorem eq_one_of_fix_d4Support {w : WeylGroup Tag.E6}
    (hw : w ∈ parabolicWeylGroup Tag.E6 d4Support)
    (h : ∀ k : Fin Tag.D4.rank,
      w • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (d4Idx k) 1) : w = 1 := by
  have h1 : w • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) = Pi.single 1 1 := h 0
  have h2 : w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = Pi.single 2 1 := h 1
  have h3 : w • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = Pi.single 3 1 := h 2
  have h4 : w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = Pi.single 4 1 := h 3
  have hJ : ∀ j ∈ d4Support, j ≠ 0 ∧ j ≠ 5 := fun j hj => hj
  have hF : w • d4OrthoFirst = d4OrthoFirst := smul_eq_of_mem_parabolicWeylGroup_of_pair hw
    fun j hj => (pair_d4Ortho j (hJ j hj).1 (hJ j hj).2).1
  have hL : w • d4OrthoLast = d4OrthoLast := smul_eq_of_mem_parabolicWeylGroup_of_pair hw
    fun j hj => (pair_d4Ortho j (hJ j hj).1 (hJ j hj).2).2
  have half : ∀ v : Fin Tag.E6.rank → ℤ, w • (v + v) = v + v → w • v = v := fun v e => by
    rw [smul_add] at e
    funext l
    have := congrFun e l
    simp only [Pi.add_apply] at this
    omega
  have h0 : w • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = Pi.single 0 1 := half _ (by
    rw [two_single_zero_eq, smul_sub, hF]
    simp only [smul_add, h1, h2, h3, h4])
  have h5 : w • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = Pi.single 5 1 := half _ (by
    rw [two_single_five_eq, smul_sub, hL]
    simp only [smul_add, h1, h2, h3, h4])
  refine ext_single fun i => ?_
  rw [one_smul]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

@[expose] def d4PosRoot : Fin 12 → Fin Tag.D4.rank → ℤ :=
  (![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 0, 1, 0], ![0, 1, 1, 0],
    ![0, 0, 1, 1], ![1, 1, 1, 0], ![1, 0, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 2, 1]] :
    Fin 12 → Fin 4 → ℤ)

theorem d4PosRoot_injective : Function.Injective d4PosRoot := by
  intro i j h
  revert i j
  decide

theorem d4PosRoot_check : ∀ k : Fin 12, List.ofFn (d4PosRoot k) ∈ Tag.D4.artifactRoots ∧
    0 < height (d4PosRoot k) := by
  decide +kernel

theorem d4PosRoot_complete : ∀ l ∈ Tag.D4.artifactRoots, 0 < l.sum →
    ∃ k : Fin 12, List.ofFn (d4PosRoot k) = l := by
  decide +kernel

theorem height_eq_sum_ofFn {τ : Tag} (v : Fin τ.rank → ℤ) : height v = (List.ofFn v).sum := by
  rw [height, List.sum_ofFn]

theorem isRoot_d4PosRoot (k : Fin 12) : IsRoot Tag.D4 (d4PosRoot k) :=
  isRoot_iff_mem_artifactRoots.2 (d4PosRoot_check k).1

theorem range_d4PosRoot : Set.range d4PosRoot = parabolicPosRoots Tag.D4 Set.univ := by
  ext α
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨isRoot_d4PosRoot k, fun i hi => absurd (Set.mem_univ i) hi⟩, isRoot_d4PosRoot k,
      (d4PosRoot_check k).2⟩
  · rintro ⟨-, hα, hpos⟩
    obtain ⟨k, hk⟩ := d4PosRoot_complete _ (isRoot_iff_mem_artifactRoots.1 hα)
      (by rw [← height_eq_sum_ofFn]; exact hpos)
    exact ⟨k, List.ofFn_injective hk⟩

theorem height_d4Lat (β : Fin Tag.D4.rank → ℤ) : height (d4Lat β) = height β := by
  rw [height_eq_sum_ofFn, height_eq_sum_ofFn, ofFn_d4Lat]
  simp

theorem range_d4Lat_d4PosRoot :
    Set.range (fun k => d4Lat (d4PosRoot k)) = parabolicPosRoots Tag.E6 d4Support := by
  ext γ
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨d4Lat_mem_parabolicRoots (isRoot_d4PosRoot k), isRoot_d4Lat_iff.2 (isRoot_d4PosRoot k),
      by rw [height_d4Lat]; exact (d4PosRoot_check k).2⟩
  · rintro ⟨hγ, -, hpos⟩
    obtain ⟨β, hβ, rfl⟩ := mem_parabolicRoots_d4Support_iff.1 hγ
    rw [height_d4Lat] at hpos
    obtain ⟨k, hk⟩ : β ∈ Set.range d4PosRoot := by
      rw [range_d4PosRoot]
      exact ⟨⟨hβ, fun i hi => absurd (Set.mem_univ i) hi⟩, hβ, hpos⟩
    exact ⟨k, congrArg d4Lat hk⟩

theorem eq_one_of_mem_parabolicLeviUnipotent {u : subsystemGroup Tag.E6 K d4Support}
    (hu : (u : ModGL Tag.E6 K) ∈ parabolicLeviUnipotent Tag.E6 K d4Support)
    (h1 : d4Res K u = 1) : u = 1 := by
  have hinj : Function.Injective (fun k => d4Lat (d4PosRoot k)) := fun i j h =>
    d4PosRoot_injective (d4Lat_injective h)
  obtain ⟨c, -, hc⟩ := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) _ hinj
    range_d4Lat_d4PosRoot).surjOn hu
  have hs := fun k => exists_sign_d4Res_pinnedX (isRoot_d4PosRoot k)
  choose ε hε hεeq using hs
  set l : List (subsystemGroup Tag.E6 K d4Support) := List.ofFn fun k =>
    ⟨pinnedX Tag.E6 K (d4Lat (d4PosRoot k)) (c k), pinnedX_mem_d4Q (isRoot_d4PosRoot k) (c k)⟩
  have hul : u = l.prod := by
    apply Subtype.ext
    rw [Subgroup.val_list_prod, List.map_ofFn]
    exact hc.symm
  have hr : d4Res K u = (List.ofFn fun k =>
      pinnedX Tag.D4 K (d4PosRoot k) ((ε k : K) * c k)).prod := by
    rw [hul, map_list_prod, List.map_ofFn]
    exact congrArg (fun f => (List.ofFn f).prod) (funext fun k => hεeq k K (c k))
  have h0 : (List.ofFn fun k => pinnedX Tag.D4 K (d4PosRoot k) ((ε k : K) * c k)).prod =
      (List.ofFn fun k => pinnedX Tag.D4 K (d4PosRoot k) ((fun _ => (0 : K)) k)).prod := by
    rw [← hr, h1]
    simp [pinnedX_zero]
  have hz := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) d4PosRoot d4PosRoot_injective
    range_d4PosRoot).injOn (Set.mem_univ (fun k => (ε k : K) * c k)) (Set.mem_univ _) h0
  have hc0 : c = 0 := funext fun k => by
    have := congrFun hz k
    rcases hε k with he | he <;> simp [he] at this <;> exact this
  rw [hul]
  apply Subtype.ext
  rw [Subgroup.val_list_prod, List.map_ofFn, Subgroup.coe_one]
  simp [hc0, pinnedX_zero]


variable (K) in
@[expose] def d4KernelSet : Set (ModGL Tag.E6 K) :=
  {g | ∃ a b d : Kˣ, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ d ^ 2 = 1 ∧ a * b * d = 1 ∧
    g = torusElt Tag.E6 K 1 a * torusElt Tag.E6 K 2 b * torusElt Tag.E6 K 4 d}

theorem d4TorusHom_sign (a b d : Kˣ) :
    d4TorusHom K ![a, b, 1, d] =
      torusElt Tag.E6 K 1 a * torusElt Tag.E6 K 2 b * torusElt Tag.E6 K 4 d := by
  rw [d4TorusHom_apply]
  simp [torusElt_one]

theorem d4_cartan_rows (β : Fin Tag.D4.rank → ℤ) :
    ∑ l, Tag.D4.cartan 0 l * β l = 2 * β 0 - β 2 ∧ ∑ l, Tag.D4.cartan 1 l * β l = 2 * β 1 - β 2 ∧
      ∑ l, Tag.D4.cartan 3 l * β l = 2 * β 3 - β 2 := by
  have h4 : ∀ f : Fin Tag.D4.rank → ℤ, ∑ j, f j = f 0 + f 1 + f 2 + f 3 := fun f =>
    Fin.sum_univ_four f
  rw [h4, h4, h4]
  rw [show Tag.D4.cartan 0 0 = 2 from rfl, show Tag.D4.cartan 0 1 = 0 from rfl,
    show Tag.D4.cartan 0 2 = -1 from rfl, show Tag.D4.cartan 0 3 = 0 from rfl,
    show Tag.D4.cartan 1 0 = 0 from rfl, show Tag.D4.cartan 1 1 = 2 from rfl,
    show Tag.D4.cartan 1 2 = -1 from rfl, show Tag.D4.cartan 1 3 = 0 from rfl,
    show Tag.D4.cartan 3 0 = 0 from rfl, show Tag.D4.cartan 3 1 = 0 from rfl,
    show Tag.D4.cartan 3 2 = -1 from rfl, show Tag.D4.cartan 3 3 = 2 from rfl]
  refine ⟨by ring, by ring, by ring⟩

theorem torusRootChar_d4TorusHom_sign_d4Lat {a b d : Kˣ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hd : d ^ 2 = 1) (habd : a * b * d = 1) {β : Fin Tag.D4.rank → ℤ} (hβ : IsRoot Tag.D4 β) :
    torusRootChar (d4TorusHom K ![a, b, 1, d]) (d4Lat β) = 1 := by
  rw [torusRootChar_d4TorusHom _ (isRoot_d4Lat_iff.2 hβ)]
  obtain ⟨r0, r1, r3⟩ := d4_cartan_rows β
  have e0 : e6Pair 1 (d4Lat β) = 2 * β 0 - β 2 := (sum_cartan_d4Lat 0 β).trans r0
  have e1 : e6Pair 2 (d4Lat β) = 2 * β 1 - β 2 := (sum_cartan_d4Lat 1 β).trans r1
  have e3 : e6Pair 4 (d4Lat β) = 2 * β 3 - β 2 := (sum_cartan_d4Lat 3 β).trans r3
  have hz : ∀ (x : Kˣ) (m n : ℤ), x ^ 2 = 1 → x ^ (2 * m - n) = x ^ (-n) := fun x m n hx => by
    rw [sub_eq_add_neg, zpow_add, zpow_mul, show x ^ (2 : ℤ) = x ^ 2 from zpow_ofNat x 2, hx,
      one_zpow, one_mul]
  have v0 : (![a, b, 1, d] : Fin 4 → Kˣ) 0 = a := rfl
  have v1 : (![a, b, 1, d] : Fin 4 → Kˣ) 1 = b := rfl
  have v2 : (![a, b, 1, d] : Fin 4 → Kˣ) 2 = 1 := rfl
  have v3 : (![a, b, 1, d] : Fin 4 → Kˣ) 3 = d := rfl
  rw [v0, v1, v2, v3, one_zpow, mul_one, e0, e1, e3, hz a _ _ ha, hz b _ _ hb, hz d _ _ hd,
    ← mul_zpow, ← mul_zpow, habd, one_zpow, Units.val_one]

theorem d4TorusHom_sign_comp_d4Emb {a b d : Kˣ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hd : d ^ 2 = 1) (habd : a * b * d = 1) (v : RootModule Tag.D4 K) :
    ((d4TorusHom K ![a, b, 1, d] : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
      (d4Emb K v) = d4Emb K v := by
  have hT := d4TorusHom_mem_torusGroup (K := K) ![a, b, 1, d]
  have h : ((d4TorusHom K ![a, b, 1, d] : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
      ∘ₗ d4Emb K = d4Emb K := by
    refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rcases x with k | ⟨β, hβ⟩
    · rw [← hVec, d4Emb_hVec]
      exact ((triangular_borel_structure.{0, 0} Tag.E6 K).2.1 _ hT).1 _
    · rw [← rootVec_eq_single_of_isRoot hβ, d4Emb_rootVec, apply_rootVec_of_mem_torusGroup hT
        (isRoot_d4Lat_iff.2 hβ), torusRootChar_d4TorusHom_sign_d4Lat ha hb hd habd hβ, one_smul]
  exact LinearMap.congr_fun h v


theorem d4TorusHom_mem_d4Q (t : Fin 4 → Kˣ) :
    d4TorusHom K t ∈ subsystemGroup Tag.E6 K d4Support :=
  supportedTorus_le_subsystemGroup _ (by rw [← range_d4TorusHom]; exact ⟨t, rfl⟩)

theorem d4Res_d4TorusHom (t : Fin 4 → Kˣ) :
    d4Res K ⟨d4TorusHom K t, d4TorusHom_mem_d4Q t⟩ =
      torusElt Tag.D4 K 0 (t 0) * torusElt Tag.D4 K 1 (t 1) * torusElt Tag.D4 K 2 (t 2) *
        torusElt Tag.D4 K 3 (t 3) := by
  have e : (⟨d4TorusHom K t, d4TorusHom_mem_d4Q t⟩ : subsystemGroup Tag.E6 K d4Support) =
      ⟨_, torusElt_mem_d4Q 0 (t 0)⟩ * ⟨_, torusElt_mem_d4Q 1 (t 1)⟩ *
        ⟨_, torusElt_mem_d4Q 2 (t 2)⟩ * ⟨_, torusElt_mem_d4Q 3 (t 3)⟩ :=
    Subtype.ext (d4TorusHom_apply t)
  rw [e, map_mul, map_mul, map_mul, d4Res_torusElt, d4Res_torusElt, d4Res_torusElt,
    d4Res_torusElt]

theorem d4Res_mem_posUnipotent {u : subsystemGroup Tag.E6 K d4Support}
    (hu : (u : ModGL Tag.E6 K) ∈ parabolicLeviUnipotent Tag.E6 K d4Support) :
    d4Res K u ∈ posUnipotent Tag.D4 K := by
  have hle : parabolicLeviUnipotent Tag.E6 K d4Support ≤
      ((posUnipotent Tag.D4 K).comap (d4Res K)).map
        (subsystemGroup Tag.E6 K d4Support).subtype := by
    refine iSup₂_le fun α hα => ?_
    obtain ⟨β, hβ, rfl⟩ := mem_parabolicRoots_d4Support_iff.1 hα.1
    obtain ⟨ε, -, hεeq⟩ := exists_sign_d4Res_pinnedX hβ
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    refine ⟨⟨_, pinnedX_mem_d4Q hβ c⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, hεeq K c]
    have hpos : 0 < height β := by
      rw [← height_d4Lat]
      exact hα.2.2
    exact pinnedX_mem_rootSpan (S := {α | IsRoot Tag.D4 α ∧ 0 < height α}) ⟨hβ, hpos⟩ _
  obtain ⟨y, hy, hyu⟩ := hle hu
  have e : y = u := Subtype.ext hyu
  rw [← e]
  exact hy

theorem mem_supportedTorus_of_d4Res_eq_one {g : subsystemGroup Tag.E6 K d4Support}
    (hg : d4Res K g = 1) : (g : ModGL Tag.E6 K) ∈ supportedTorus Tag.E6 K d4Support := by
  obtain ⟨⟨v, h, u, u'⟩, ⟨hv, hh, hu, hu', hgeq⟩, -⟩ := existsUnique_supportedCell_factors g.2
  simp only at hv hh hu hu' hgeq
  have hhQ : h ∈ subsystemGroup Tag.E6 K d4Support := supportedTorus_le_subsystemGroup _ hh
  have huQ : u ∈ subsystemGroup Tag.E6 K d4Support := parabolicLeviUnipotent_le_subsystemGroup hu
  have hu'Q : u' ∈ subsystemGroup Tag.E6 K d4Support := by
    rw [subsystemGroup_eq_rootSpan]
    exact rootSpan_mono Set.inter_subset_left hu'
  have hhB : h ∈ borelGroup Tag.E6 K :=
    torusGroup_le_borelGroup (supportedTorus_le_torusGroup _ hh)
  have huB : u ∈ borelGroup Tag.E6 K :=
    Subgroup.mem_sup_right (parabolicLeviUnipotent_le_posUnipotent _ hu)
  have hu'B : u' ∈ borelGroup Tag.E6 K :=
    Subgroup.mem_sup_right (rootSpan_le_posUnipotent (fun _ hα => ⟨hα.2.1, hα.2.2.1⟩) hu')
  have hb : (h * u)⁻¹ * u'⁻¹ ∈ borelGroup Tag.E6 K :=
    mul_mem (inv_mem (mul_mem hhB huB)) (inv_mem hu'B)
  have hn : canonicalRep (coxeterSystem Tag.E6) K v = (h * u)⁻¹ * (g : ModGL Tag.E6 K) * u'⁻¹ := by
    rw [← hgeq]
    group
  have hfix : ∀ β, IsRoot Tag.D4 β →
      (canonicalRep (coxeterSystem Tag.E6) K v : Module.End K (RootModule Tag.E6 K))
        (rootVec Tag.E6 K (d4Lat β)) = (((h * u)⁻¹ * u'⁻¹ : ModGL Tag.E6 K) :
          Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K (d4Lat β)) := by
    intro β _
    have e1 : ((u'⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
        (rootVec Tag.E6 K (d4Lat β)) = d4Emb K ((d4Res K ⟨u'⁻¹, inv_mem hu'Q⟩ :
          Module.End K (RootModule Tag.D4 K)) (rootVec Tag.D4 K β)) := by
      rw [← d4Emb_rootVec, ← d4Res_apply]
    rw [hn, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, e1,
      (d4Res_eq_one_iff g).1 hg, ← e1, Units.val_mul, Module.End.mul_apply]
  have hvβ : ∀ β, IsRoot Tag.D4 β → v • d4Lat β = d4Lat β := by
    intro β hβ
    have hmaps := mapsRootLines_canonicalRep (R := K) v
    have n1 := not_precedes_of_apply_eq_borel hb hmaps (isRoot_d4Lat_iff.2 hβ) (hfix β hβ)
    have n2 := not_precedes_of_apply_eq_borel hb hmaps (isRoot_d4Lat_iff.2 (IsRoot.neg hβ))
      (hfix (-β) (IsRoot.neg hβ))
    exact eq_of_not_precedes_of_not_precedes_neg _ _ _ _ (d4Lat_neg β)
      (by rw [d4Lat_neg, smul_neg]) n1 n2
  have hv1 : v = 1 := eq_one_of_fix_d4Support hv fun k => by
    rw [← d4Lat_single]
    exact hvβ _ (isRoot_single Tag.D4 k)
  subst hv1
  have hu'1 : u' = 1 := by
    rw [inversionSet_one, Set.inter_empty] at hu'
    simpa [rootSpan] using hu'
  rw [hu'1, canonicalRep_one, mul_one, mul_one] at hgeq
  obtain ⟨t, rfl⟩ : ∃ t, d4TorusHom K t = h := by
    rw [← range_d4TorusHom] at hh
    exact hh
  have hgQ : g = ⟨_, d4TorusHom_mem_d4Q t⟩ * ⟨u, huQ⟩ := Subtype.ext hgeq.symm
  have hr : d4Res K ⟨d4TorusHom K t, d4TorusHom_mem_d4Q t⟩ * d4Res K ⟨u, huQ⟩ = 1 := by
    rw [← map_mul, ← hgQ, hg]
  have hT : d4Res K ⟨d4TorusHom K t, d4TorusHom_mem_d4Q t⟩ ∈ torusGroup Tag.D4 K := by
    rw [d4Res_d4TorusHom]
    exact mul_mem (mul_mem (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
      (torusElt_mem_torusGroup _ _)) (torusElt_mem_torusGroup _ _)
  have hU := d4Res_mem_posUnipotent (u := ⟨u, huQ⟩) hu
  have hinf : d4Res K ⟨u, huQ⟩ ∈ torusGroup Tag.D4 K ⊓ posUnipotent Tag.D4 K := by
    refine Subgroup.mem_inf.2 ⟨?_, hU⟩
    rw [eq_inv_of_mul_eq_one_right hr]
    exact inv_mem hT
  rw [torusGroup_inf_posUnipotent, Subgroup.mem_bot] at hinf
  have hu1 : (⟨u, huQ⟩ : subsystemGroup Tag.E6 K d4Support) = 1 :=
    eq_one_of_mem_parabolicLeviUnipotent hu hinf
  rw [hgQ, hu1, mul_one]
  exact hh

theorem d4Res_eq_one_iff_mem_d4KernelSet (g : subsystemGroup Tag.E6 K d4Support) :
    d4Res K g = 1 ↔ (g : ModGL Tag.E6 K) ∈ d4KernelSet K := by
  constructor
  · intro hg
    have hgH := mem_supportedTorus_of_d4Res_eq_one hg
    rw [← range_d4TorusHom] at hgH
    obtain ⟨t, ht⟩ := hgH
    have hχ : ∀ k : Fin Tag.D4.rank, t 0 ^ Tag.E6.cartan 1 (d4Idx k) *
        t 1 ^ Tag.E6.cartan 2 (d4Idx k) * t 2 ^ Tag.E6.cartan 3 (d4Idx k) *
          t 3 ^ Tag.E6.cartan 4 (d4Idx k) = 1 := by
      intro k
      have h1 := apply_rootVec_d4Lat_of_d4Res_eq_one hg (Pi.single k 1)
      rw [d4Lat_single, ← ht] at h1
      have h2 := torusRootChar_eq_of_apply (h := d4TorusHom K t)
        (isRoot_single Tag.E6 (d4Idx k)) (c := (1 : K)) (by rw [h1, one_smul])
      rw [torusRootChar_d4TorusHom _ (isRoot_single _ _), e6Pair_single, e6Pair_single,
        e6Pair_single, e6Pair_single] at h2
      exact Units.ext h2
    have e1 := hχ 0
    have e2 := hχ 1
    have e3 := hχ 2
    have e4 := hχ 3
    simp only [show Tag.E6.cartan 1 (d4Idx 0) = 2 by decide,
      show Tag.E6.cartan 2 (d4Idx 0) = 0 by decide, show Tag.E6.cartan 3 (d4Idx 0) = -1 by decide,
      show Tag.E6.cartan 4 (d4Idx 0) = 0 by decide, show Tag.E6.cartan 1 (d4Idx 1) = 0 by decide,
      show Tag.E6.cartan 2 (d4Idx 1) = 2 by decide, show Tag.E6.cartan 3 (d4Idx 1) = -1 by decide,
      show Tag.E6.cartan 4 (d4Idx 1) = 0 by decide, show Tag.E6.cartan 1 (d4Idx 2) = -1 by decide,
      show Tag.E6.cartan 2 (d4Idx 2) = -1 by decide, show Tag.E6.cartan 3 (d4Idx 2) = 2 by decide,
      show Tag.E6.cartan 4 (d4Idx 2) = -1 by decide, show Tag.E6.cartan 1 (d4Idx 3) = 0 by decide,
      show Tag.E6.cartan 2 (d4Idx 3) = 0 by decide, show Tag.E6.cartan 3 (d4Idx 3) = -1 by decide,
      show Tag.E6.cartan 4 (d4Idx 3) = 2 by decide, zpow_zero, zpow_neg, zpow_one, one_mul,
      mul_one, show ∀ x : Kˣ, x ^ (2 : ℤ) = x ^ 2 from fun x => zpow_ofNat x 2] at e1 e2 e3 e4
    have ha : t 0 ^ 2 = t 2 := mul_inv_eq_one.1 e1
    have hb : t 1 ^ 2 = t 2 := mul_inv_eq_one.1 e2
    have hd : t 3 ^ 2 = t 2 := (inv_mul_eq_one.1 e4).symm
    have habd : t 0 * t 1 * t 3 = t 2 ^ 2 := by
      refine inv_mul_eq_one.1 ?_
      calc (t 0 * t 1 * t 3)⁻¹ * t 2 ^ 2 = (t 0)⁻¹ * (t 1)⁻¹ * (t 3)⁻¹ * t 2 ^ 2 := by
            rw [mul_inv, mul_inv]
        _ = (t 0)⁻¹ * (t 1)⁻¹ * t 2 ^ 2 * (t 3)⁻¹ := mul_right_comm _ _ _
        _ = 1 := e3
    have hc : t 2 = 1 := by
      have h4 : t 2 ^ 3 * t 2 = t 2 ^ 3 * 1 := by
        calc t 2 ^ 3 * t 2 = (t 2 ^ 2) ^ 2 := by group
          _ = (t 0 * t 1 * t 3) ^ 2 := by rw [habd]
          _ = t 0 ^ 2 * t 1 ^ 2 * t 3 ^ 2 := by rw [mul_pow, mul_pow]
          _ = t 2 ^ 3 * 1 := by rw [ha, hb, hd, mul_one, pow_three, mul_assoc]
      exact mul_left_cancel h4
    refine ⟨t 0, t 1, t 3, by rw [ha, hc], by rw [hb, hc], by rw [hd, hc],
      by rw [habd, hc, one_pow], ?_⟩
    rw [← ht, ← d4TorusHom_sign]
    congr 1
    funext k
    fin_cases k
    · rfl
    · rfl
    · exact hc
    · rfl
  · rintro ⟨a, b, d, ha, hb, hd, habd, he⟩
    rw [← d4TorusHom_sign] at he
    exact (d4Res_eq_one_iff g).2 fun v => by
      rw [he]
      exact d4TorusHom_sign_comp_d4Emb ha hb hd habd v


theorem mem_center_of_d4Res_eq_one {g : subsystemGroup Tag.E6 K d4Support}
    (hg : d4Res K g = 1) : g ∈ Subgroup.center (subsystemGroup Tag.E6 K d4Support) := by
  rw [mem_center_subsystemGroup_iff]
  refine ⟨mem_supportedTorus_of_d4Res_eq_one hg, fun α hα => ?_⟩
  obtain ⟨β, hβ, rfl⟩ := mem_parabolicRoots_d4Support_iff.1 hα
  exact torusRootChar_eq_of_apply (isRoot_d4Lat_iff.2 hβ)
    (by rw [apply_rootVec_d4Lat_of_d4Res_eq_one hg β, one_smul])

theorem d4Sign_injective {a b d a' b' d' : Kˣ}
    (h : torusElt Tag.E6 K 1 a * torusElt Tag.E6 K 2 b * torusElt Tag.E6 K 4 d =
      torusElt Tag.E6 K 1 a' * torusElt Tag.E6 K 2 b' * torusElt Tag.E6 K 4 d') :
    a = a' ∧ b = b' ∧ d = d' := by
  rw [← d4TorusHom_sign, ← d4TorusHom_sign] at h
  have e := d4TorusHom_injective h
  exact ⟨congrFun e 0, congrFun e 1, congrFun e 3⟩

theorem eq_one_of_sq_eq_one_of_ringChar_eq_two (h2 : ringChar K = 2) {x : Kˣ} (hx : x ^ 2 = 1) :
    x = 1 := by
  have : CharP K 2 := ringChar.of_eq h2
  have hx' : ((x : K) + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, one_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one,
      CharTwo.add_self_eq_zero]
  have h1 : (x : K) + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.1 hx'
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  exact Units.ext (by rw [Units.val_one]; linear_combination h1 - h2K)

theorem d4Res_injective_of_ringChar_eq_two (h2 : ringChar K = 2) :
    Function.Injective (d4Res K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨a, b, d, ha, hb, hd, -, he⟩ := (d4Res_eq_one_iff_mem_d4KernelSet g).1 hg
  apply Subtype.ext
  rw [he, eq_one_of_sq_eq_one_of_ringChar_eq_two h2 ha,
    eq_one_of_sq_eq_one_of_ringChar_eq_two h2 hb,
    eq_one_of_sq_eq_one_of_ringChar_eq_two h2 hd, torusElt_one, torusElt_one, torusElt_one,
    one_mul, one_mul, Subgroup.coe_one]

@[expose] def zmodTwoSign (x : ZMod 2) : Kˣ := if x = 0 then 1 else -1

theorem zmodTwoSign_zero : (zmodTwoSign (0 : ZMod 2) : Kˣ) = 1 := ite_eq_left rfl

theorem zmodTwoSign_one : (zmodTwoSign (1 : ZMod 2) : Kˣ) = -1 := ite_eq_right (by decide)

theorem zmodTwo_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem zmodTwoSign_add (x y : ZMod 2) :
    (zmodTwoSign (x + y) : Kˣ) = zmodTwoSign x * zmodTwoSign y := by
  rcases zmodTwo_cases x with rfl | rfl <;> rcases zmodTwo_cases y with rfl | rfl
  · rw [add_zero, zmodTwoSign_zero, one_mul]
  · rw [zero_add, zmodTwoSign_zero, one_mul]
  · rw [add_zero, zmodTwoSign_zero, mul_one]
  · rw [show (1 + 1 : ZMod 2) = 0 by decide, zmodTwoSign_zero, zmodTwoSign_one, neg_one_mul,
      neg_neg]

theorem zmodTwoSign_sq (x : ZMod 2) : (zmodTwoSign x : Kˣ) ^ 2 = 1 := by
  rcases zmodTwo_cases x with rfl | rfl
  · rw [zmodTwoSign_zero, one_pow]
  · rw [zmodTwoSign_one, neg_one_sq]

theorem zmodTwoSign_eq_one_iff (h2 : ringChar K ≠ 2) {x : ZMod 2} :
    (zmodTwoSign x : Kˣ) = 1 ↔ x = 0 := by
  have hne : (-1 : Kˣ) ≠ 1 := fun h => h2 (neg_one_eq_one_iff.1 (by
    have := congrArg Units.val h
    simpa using this))
  rcases zmodTwo_cases x with rfl | rfl
  · exact ⟨fun _ => rfl, fun _ => zmodTwoSign_zero⟩
  · rw [zmodTwoSign_one]
    exact ⟨fun h => absurd h hne, fun h => absurd h (by decide)⟩

theorem d4TorusHom_signs_mem (a b : Kˣ) :
    d4TorusHom K ![a, b, 1, a * b] ∈ subsystemGroup Tag.E6 K d4Support :=
  d4TorusHom_mem_d4Q _

theorem d4Res_d4TorusHom_signs {a b : Kˣ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    d4Res K ⟨_, d4TorusHom_signs_mem a b⟩ = 1 := by
  refine (d4Res_eq_one_iff_mem_d4KernelSet _).2 ⟨a, b, a * b, ha, hb, by rw [mul_pow, ha, hb,
    one_mul], by rw [← sq, mul_pow, ha, hb, one_mul], d4TorusHom_sign a b (a * b)⟩

variable (K) in
@[expose] def d4KernelHom : Multiplicative (ZMod 2 × ZMod 2) →* (d4Res K).ker where
  toFun p := ⟨⟨_, d4TorusHom_signs_mem (zmodTwoSign (Multiplicative.toAdd p).1)
      (zmodTwoSign (Multiplicative.toAdd p).2)⟩,
    d4Res_d4TorusHom_signs (zmodTwoSign_sq _) (zmodTwoSign_sq _)⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    have e : (![zmodTwoSign (0 : ZMod 2), zmodTwoSign (0 : ZMod 2), 1,
        zmodTwoSign (0 : ZMod 2) * zmodTwoSign (0 : ZMod 2)] : Fin 4 → Kˣ) = 1 := by
      rw [zmodTwoSign_zero, mul_one]
      funext k
      fin_cases k <;> rfl
    simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero, e, map_one]
    rfl
  map_mul' p q := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, zmodTwoSign_add]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul]
    congr 1
    funext k
    fin_cases k <;> simp [mul_mul_mul_comm]

theorem d4KernelHom_bijective (h2 : ringChar K ≠ 2) : Function.Bijective (d4KernelHom K) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun p hp => ?_, fun z => ?_⟩
  · have h := congrArg (fun z : (d4Res K).ker => ((z : subsystemGroup Tag.E6 K d4Support) :
      ModGL Tag.E6 K)) hp
    simp only [d4KernelHom, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h
    have e := d4TorusHom_injective (h.trans (map_one _).symm)
    have e0 := congrFun e 0
    have e1 := congrFun e 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.one_apply,
      zmodTwoSign_eq_one_iff h2] at e0 e1
    exact Prod.ext e0 e1
  · obtain ⟨⟨g, hgQ⟩, hgk⟩ := z
    obtain ⟨a, b, d, ha, hb, hd, habd, he⟩ := (d4Res_eq_one_iff_mem_d4KernelSet _).1 hgk
    have hs : ∀ x : Kˣ, x ^ 2 = 1 → ∃ y : ZMod 2, zmodTwoSign y = x := fun x hx => by
      have hx' : (x : K) * x = 1 := by
        rw [← sq, ← Units.val_pow_eq_pow_val, hx, Units.val_one]
      rcases mul_self_eq_one_iff.1 hx' with h | h
      · exact ⟨0, by simp [zmodTwoSign, Units.ext_iff, h]⟩
      · exact ⟨1, by simp [zmodTwoSign, Units.ext_iff, h]⟩
    obtain ⟨x, rfl⟩ := hs a ha
    obtain ⟨y, rfl⟩ := hs b hb
    have hd' : d = zmodTwoSign x * zmodTwoSign y := by
      have hinv : ∀ c : Kˣ, c ^ 2 = 1 → c⁻¹ = c := fun c hc => by
        rw [inv_eq_iff_mul_eq_one, ← sq, hc]
      rw [eq_inv_of_mul_eq_one_right habd, mul_inv, hinv _ ha, hinv _ hb]
    refine ⟨Multiplicative.ofAdd (x, y), Subtype.ext (Subtype.ext ?_)⟩
    simp only [d4KernelHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    rw [hd'] at he
    rw [d4TorusHom_sign]
    exact he.symm

@[expose] def d4KernelEquiv (h2 : ringChar K ≠ 2) :
    Multiplicative (ZMod 2 × ZMod 2) ≃* (d4Res K).ker :=
  MulEquiv.ofBijective (d4KernelHom K) (d4KernelHom_bijective h2)

end CFSG.RankThree.Chevalley
