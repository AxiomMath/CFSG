module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Klein
public import CFSG.LocalAnalysis.WeakClosure81.W183Abs4

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.Quasithin CFSG.Open Subgroup

theorem w183finSp44G2Y_map_conj {G H : Type*} [Group G] [Group H] (σ : G →* H)
    (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map σ =
      (A.map σ).map (MulAut.conj (σ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul]

theorem w183finSp44G2Y_isTISub_map_iff {G H : Type*} [Group G] [Group H] (σ : G ≃* H)
    (A : Subgroup G) :
    IsTISub H (A.map σ.toMonoidHom) ↔ IsTISub G A := by
  have hnorm : (Subgroup.normalizer (A : Set G)).map σ.toMonoidHom =
      Subgroup.normalizer ((A.map σ.toMonoidHom : Subgroup H) : Set H) :=
    Subgroup.map_normalizer_eq_of_bijective A σ.bijective
  constructor
  · intro hTI a ha ha1 g hg
    have hσ : σ g ∈ Subgroup.normalizer ((A.map σ.toMonoidHom : Subgroup H) : Set H) := by
      refine hTI (σ a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩) ?_ (σ g) ?_
      · intro h
        exact ha1 (σ.injective (by rw [h, map_one]))
      · rw [← map_mul, ← map_mul, hg]
    rw [← hnorm] at hσ
    obtain ⟨n, hn, hnσ⟩ := Subgroup.mem_map.mp hσ
    rwa [σ.injective hnσ] at hn
  · intro hTI h hh hh1 g hg
    have hcomm : σ.symm g * σ.symm h = σ.symm h * σ.symm g := by
      rw [← σ.symm.map_mul, ← σ.symm.map_mul, hg]
    have hmem : σ.symm g ∈ Subgroup.normalizer (A : Set G) := by
      refine hTI (σ.symm h) ?_ ?_ (σ.symm g) hcomm
      · obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hh
        simpa [← hae] using ha
      · intro hcon
        apply hh1
        rw [← σ.apply_symm_apply h, hcon, map_one]
    rw [← hnorm]
    exact Subgroup.mem_map.mpr ⟨σ.symm g, hmem, σ.apply_symm_apply g⟩

theorem w183finSp44G2Y_corConfig_map {G H : Type*} [Group G] [Group H] (σ : G ≃* H)
    (A : Subgroup G) (h : CorConfig G A) : CorConfig H (A.map σ.toMonoidHom) := by
  let f : G →* H := σ.toMonoidHom
  change CorConfig H (A.map f)
  obtain ⟨A', S, y, ⟨gA, hA'eq⟩, hS, hy, hrel, hnn, hcomm⟩ := h
  refine ⟨A'.map f, Subgroup.map f '' S, f y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨f gA, by rw [hA'eq, w183finSp44G2Y_map_conj]⟩
  · rintro _ ⟨X, hX, rfl⟩
    obtain ⟨g, hg⟩ := hS X hX
    exact ⟨f g, by rw [hg, w183finSp44G2Y_map_conj]⟩
  · intro heq
    apply hy
    have h1 := w183finSp44G2Y_map_conj f A y
    have h2 : (A.map (MulAut.conj y).toMonoidHom).map f = A.map f := by
      rw [h1]; exact heq
    exact Subgroup.map_injective σ.injective h2
  · rintro s' hs'
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hs'
    obtain ⟨z, hz, hzrel⟩ := hrel s hs
    refine ⟨f z, ?_, ?_⟩
    · have hsub : f '' (⋃ X ∈ S, (X : Set G)) ⊆
          ⋃ X ∈ (Subgroup.map f '' S), (X : Set H) := by
        rintro w ⟨v, hv, rfl⟩
        rw [Set.mem_iUnion] at hv
        obtain ⟨X, hv⟩ := hv
        rw [Set.mem_iUnion] at hv
        obtain ⟨hX, hvX⟩ := hv
        simp only [Set.mem_iUnion]
        exact ⟨Subgroup.map f X, ⟨X, hX, rfl⟩, Subgroup.mem_map.mpr ⟨v, hvX, rfl⟩⟩
      have hmem : f z ∈ (Subgroup.closure (⋃ X ∈ S, (X : Set G))).map f :=
        Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      rw [MonoidHom.map_closure] at hmem
      exact Subgroup.closure_mono hsub hmem
    · simpa only [map_mul, map_inv] using congrArg f hzrel
  · intro hle
    apply hnn
    intro a ha
    have ha' : f a ∈ (A.map f : Subgroup H) := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hmem := hle ha'
    rw [← Subgroup.map_normalizer_eq_of_bijective A' σ.bijective] at hmem
    obtain ⟨n, hn, hna⟩ := Subgroup.mem_map.mp hmem
    rwa [σ.injective hna] at hn
  · rintro _ ⟨X, hX, rfl⟩
    rcases hcomm X hX with hXA | hXc
    · exact Or.inl (by rw [hXA])
    · refine Or.inr ?_
      intro a' ha' x' hx'
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
      simpa only [map_mul] using congrArg f (hXc a ha x hx)

theorem w183finSp44G2Y_corConfig_map_iff {G H : Type*} [Group G] [Group H] (σ : G ≃* H)
    (A : Subgroup G) :
    CorConfig G A ↔ CorConfig H (A.map σ.toMonoidHom) := by
  refine ⟨w183finSp44G2Y_corConfig_map σ A, fun h => ?_⟩
  have h' := w183finSp44G2Y_corConfig_map σ.symm (A.map σ.toMonoidHom) h
  rw [Subgroup.map_map, show σ.symm.toMonoidHom.comp σ.toMonoidHom = MonoidHom.id G from by
    ext x; simp, Subgroup.map_id] at h'
  exact h'


theorem w183finSp44G2Y_mem_klein_iff {a b x : El} :
    x ∈ klein a b ↔ x = oneE ∨ x = a ∨ x = b ∨ x = gmulE a b := by
  rw [klein]
  simp only [List.mem_cons, List.mem_nil_iff, List.not_mem_nil, false_or, or_false]

theorem w183finSp44G2Y_valid_klein {a b x : El} (ha : validB a = true)
    (hb : validB b = true) (hx : x ∈ klein a b) : validB x = true := by
  rw [w183finSp44G2Y_mem_klein_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact validB_oneE
  · exact ha
  · exact hb
  · exact validB_gmulE ha hb

theorem w183finSp44G2Y_mem_invsA {i : Nat} (hi : i < n127) : invsA[i]! ∈ invs := by
  rw [invsA, List.getElem!_toArray, List.getElem!_eq_getElem?_getD]
  have hsome : invs[i]? = some (invs[i]'hi) :=
    (List.getElem?_eq_some_getElem_iff hi).mpr trivial
  simpa [hsome] using List.mem_of_getElem? hsome

theorem w183finSp44G2Y_valid_invsA {i : Nat} (hi : i < n127) : validB invsA[i]! = true :=
  Pel_valid _ (List.mem_filter.mp (w183finSp44G2Y_mem_invsA hi)).1

theorem w183finSp44G2Y_ne_one_of_mem_invs {x : El} (hx : x ∈ invs) : x ≠ oneE := by
  have hcond := (List.mem_filter.mp hx).2
  rw [Bool.and_eq_true_iff] at hcond
  exact of_decide_eq_true hcond.1

theorem w183finSp44G2Y_gmulE_self_of_mem_invs {x : El} (hx : x ∈ invs) :
    gmulE x x = oneE := by
  have hcond := (List.mem_filter.mp hx).2
  rw [Bool.and_eq_true_iff] at hcond
  exact beq_iff_eq.mp hcond.2

theorem w183finSp44G2Y_valid_a {p : Nat × Nat} (hp : p ∈ pairsL) :
    validB invsA[p.1]! = true := by
  obtain ⟨h12, h2, -⟩ := (mem_pairsL_iff p).mp hp
  have h2n : p.2 < n127 := by
    have : n127 = 127 := invs_length
    rwa [this]
  exact w183finSp44G2Y_valid_invsA (lt_trans h12 h2n)

theorem w183finSp44G2Y_valid_b {p : Nat × Nat} (hp : p ∈ pairsL) :
    validB invsA[p.2]! = true := by
  obtain ⟨-, h2, -⟩ := (mem_pairsL_iff p).mp hp
  refine w183finSp44G2Y_valid_invsA ?_
  have : n127 = 127 := invs_length
  rwa [this]

theorem w183finSp44G2Y_memK_eq_true {K : List El} {x : El} : memK K x = true ↔ x ∈ K := by
  rw [memK, List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [beq_iff_eq] at hyx
    simpa [hyx] using hy
  · intro hx
    exact ⟨x, hx, by rw [beq_iff_eq]⟩

theorem w183finSp44G2Y_sameSet_eq_true {K L : List El} :
    sameSet K L = true ↔ ∀ x, x ∈ K ↔ x ∈ L := by
  rw [sameSet, Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩ x
    exact ⟨fun hx => w183finSp44G2Y_memK_eq_true.mp ((List.all_eq_true.mp h1) x hx),
      fun hx => w183finSp44G2Y_memK_eq_true.mp ((List.all_eq_true.mp h2) x hx)⟩
  · intro h
    exact ⟨List.all_eq_true.mpr fun x hx => w183finSp44G2Y_memK_eq_true.mpr ((h x).mp hx),
      List.all_eq_true.mpr fun x hx => w183finSp44G2Y_memK_eq_true.mpr ((h x).mpr hx)⟩

theorem w183finSp44G2Y_autOf_mem_kleinSub {p : Nat × Nat} (hp : p ∈ pairsL) {x : El}
    (hx : validB x = true) :
    autOf x ∈ kleinSub invsA[p.1]! invsA[p.2]! ↔
      x ∈ klein invsA[p.1]! invsA[p.2]! := by
  rw [mem_kleinSub_iff hp]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hvz := w183finSp44G2Y_valid_klein (w183finSp44G2Y_valid_a hp)
      (w183finSp44G2Y_valid_b hp) hz
    rwa [autOf_inj hvz hx hzx] at hz
  · exact fun hx' => ⟨x, hx', rfl⟩

theorem w183finSp44G2Y_autOf_mem_map_conjE {p : Nat × Nat} (hp : p ∈ pairsL) {g : El}
    (hg : validB g = true) {z : El} (hz : validB z = true) :
    autOf z ∈ (kleinSub invsA[p.1]! invsA[p.2]!).map
        (MulAut.conj (autOf g)).toMonoidHom ↔
      z ∈ (klein invsA[p.1]! invsA[p.2]!).map (conjE g) := by
  constructor
  · intro hz'
    rw [Subgroup.mem_map] at hz'
    obtain ⟨s, hs, hsz⟩ := hz'
    obtain ⟨w, hw, hws⟩ := (mem_kleinSub_iff hp s).mp hs
    have hvw := w183finSp44G2Y_valid_klein (w183finSp44G2Y_valid_a hp)
      (w183finSp44G2Y_valid_b hp) hw
    have hconj : conjE g w = z := by
      apply autOf_inj (validB_conjE hg hvw) hz
      change autOf g * s * (autOf g)⁻¹ = autOf z at hsz
      rw [autOf_conjE hg hvw, hws]
      exact hsz
    exact List.mem_map.mpr ⟨w, hw, hconj⟩
  · intro hz'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz'
    have hvw := w183finSp44G2Y_valid_klein (w183finSp44G2Y_valid_a hp)
      (w183finSp44G2Y_valid_b hp) hw
    rw [Subgroup.mem_map]
    exact ⟨autOf w, (mem_kleinSub_iff hp (autOf w)).mpr ⟨w, hw, rfl⟩, by
      change autOf g * autOf w * (autOf g)⁻¹ = autOf (conjE g w)
      exact (autOf_conjE hg hvw).symm⟩

theorem w183finSp44G2Y_autOf_self_of_klein {p : Nat × Nat} (hp : p ∈ pairsL) {x : El}
    (hx : x ∈ klein invsA[p.1]! invsA[p.2]!) : autOf x * autOf x = 1 := by
  obtain ⟨h12, h2, hcomm⟩ := (mem_pairsL_iff p).mp hp
  have hva := w183finSp44G2Y_valid_a hp
  have hvb := w183finSp44G2Y_valid_b hp
  have h2n : p.2 < n127 := by
    have : n127 = 127 := invs_length
    rwa [this]
  have h1n : p.1 < n127 := lt_trans h12 h2n
  have ha2 : autOf invsA[p.1]! * autOf invsA[p.1]! = 1 := by
    rw [← autOf_gmulE hva hva, w183finSp44G2Y_gmulE_self_of_mem_invs
      (w183finSp44G2Y_mem_invsA h1n), autOf_oneE]
  have hb2 : autOf invsA[p.2]! * autOf invsA[p.2]! = 1 := by
    rw [← autOf_gmulE hvb hvb, w183finSp44G2Y_gmulE_self_of_mem_invs
      (w183finSp44G2Y_mem_invsA h2n), autOf_oneE]
  have hab : autOf invsA[p.1]! * autOf invsA[p.2]! =
      autOf invsA[p.2]! * autOf invsA[p.1]! := by
    rw [← autOf_gmulE hva hvb, ← autOf_gmulE hvb hva, hcomm]
  rcases w183finSp44G2Y_mem_klein_iff.mp hx with h | h | h | h
  · rw [h, autOf_oneE, one_mul]
  · rw [h]; exact ha2
  · rw [h]; exact hb2
  · rw [h, autOf_gmulE hva hvb]
    calc (autOf invsA[p.1]! * autOf invsA[p.2]!) *
          (autOf invsA[p.1]! * autOf invsA[p.2]!)
        = autOf invsA[p.1]! * (autOf invsA[p.2]! * autOf invsA[p.1]!) *
            autOf invsA[p.2]! := by group
      _ = autOf invsA[p.1]! * (autOf invsA[p.1]! * autOf invsA[p.2]!) *
            autOf invsA[p.2]! := by rw [hab]
      _ = (autOf invsA[p.1]! * autOf invsA[p.1]!) *
            (autOf invsA[p.2]! * autOf invsA[p.2]!) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]

theorem w183finSp44G2Y_conjE_conjE {x z : El} (hx : validB x = true) (hz : validB z = true)
    (hxx : gmulE x x = oneE) : conjE x (conjE x z) = z := by
  have hx2 : autOf x * autOf x = 1 := by
    rw [← autOf_gmulE hx hx, hxx, autOf_oneE]
  apply autOf_inj (validB_conjE hx (validB_conjE hx hz)) hz
  rw [autOf_conjE hx (validB_conjE hx hz), autOf_conjE hx hz]
  calc autOf x * (autOf x * autOf z * (autOf x)⁻¹) * (autOf x)⁻¹
      = (autOf x * autOf x) * autOf z * ((autOf x)⁻¹ * (autOf x)⁻¹) := by group
    _ = autOf z := by rw [hx2, one_mul, ← mul_inv_rev, hx2, inv_one, mul_one]

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
