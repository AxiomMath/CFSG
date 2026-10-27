module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369u_commSub_map_conj (L : Subgroup (MulAut W)) (g : MulAut W) :
    commSub ⊤ (L.map (MulAut.conj g).toMonoidHom) = (commSub ⊤ L).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, -, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    refine ⟨x₀ (g⁻¹ w) * (g⁻¹ w)⁻¹, ⟨x₀, hx₀, g⁻¹ w, trivial, rfl⟩, ?_⟩
    change g (x₀ (g⁻¹ w) * (g⁻¹ w)⁻¹) = (MulAut.conj g x₀) w * w⁻¹
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.apply_inv_self, map_mul, map_inv]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x₀, hx₀, v, -, rfl⟩ := hs
    refine ⟨MulAut.conj g x₀, ⟨x₀, hx₀, rfl⟩, g v, trivial, ?_⟩
    change (MulAut.conj g x₀) (g v) * (g v)⁻¹ = g (x₀ v * v⁻¹)
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.inv_apply_self,
      map_mul, map_inv]

private theorem w1369u_le_stabSub_of_stableUnder {K : Subgroup (MulAut W)} {U : Subgroup W}
    (h : StableUnder K U) : K ≤ stabSub U := by
  intro k hk
  rw [mem_stabSub]
  intro u
  exact ⟨fun hu => by
      have h1 := h k⁻¹ (K.inv_mem hk) (k u) hu
      simpa using h1,
    fun hu => h k hk u hu⟩

private theorem w1369u_centSub_iSup {ι : Sort*} (U : ι → Subgroup W) :
    centSub (⨆ i, U i) = ⨅ i, centSub (U i) := by
  ext g
  constructor
  · intro h
    rw [Subgroup.mem_iInf]
    intro i
    rw [mem_centSub]
    intro u hu
    exact (mem_centSub.mp h) u (Subgroup.mem_iSup_of_mem i hu)
  · intro h
    rw [Subgroup.mem_iInf] at h
    rw [mem_centSub]
    intro u hu
    exact Subgroup.iSup_induction U hu (C := fun x => g x = x)
      (fun i x hx => (mem_centSub.mp (h i)) x hx)
      (map_one g) (fun x y hx hy => by rw [map_mul, hx, hy])

private theorem w1369u_centSub_top : centSub (⊤ : Subgroup W) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  ext w
  simpa using (mem_centSub.mp hg) w (Subgroup.mem_top w)

private theorem w1369u_le_centSub_top_of_family {s : Set (Subgroup W)}
    (hspan : (⨆ X ∈ s, X) = ⊤) {H : Subgroup (MulAut W)}
    (h : ∀ X ∈ s, H ≤ centSub X) : H ≤ centSub ⊤ := by
  have hspan' : (⨆ X : {X : Subgroup W // X ∈ s}, (X : Subgroup W)) = ⊤ :=
    (iSup_subtype'' s (fun X : Subgroup W => X)).trans hspan
  rw [← hspan']
  rw [w1369u_centSub_iSup (U := fun X : {X : Subgroup W // X ∈ s} => (X : Subgroup W))]
  exact le_iInf fun X => h X X.2

theorem lemmaU (hw2 : ∀ w : W, w * w = 1) {A L N : Subgroup (MulAut W)} (hLN : L ≤ N)
    (hNA : N ≤ A) (hN : (N.subgroupOf A).Normal)
    (hU1 : ∀ n ∈ N, ∀ w ∈ commSub ⊤ L, n w ∈ commSub ⊤ L)
    (hind : sSupIndep (conjSubs A (commSub ⊤ L)))
    (hspan : (⨆ X ∈ conjSubs A (commSub ⊤ L), X) = ⊤)
    (hU3 : ∀ g ∈ A, (commSub ⊤ L).map g.toMonoidHom = commSub ⊤ L →
      L.map (MulAut.conj g).toMonoidHom = L) :
    ∀ g ∈ A, g ∉ Subgroup.normalizer (L : Set (MulAut W)) →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
        commSub (commSub ⊤ L) (L.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  intro g hgA hgN
  let W₁ : Subgroup W := commSub ⊤ L
  let Lg : Subgroup (MulAut W) := L.map (MulAut.conj g).toMonoidHom
  let W₂ : Subgroup W := W₁.map g.toMonoidHom
  show ⁅L, Lg⁆ = ⊥ ∧ commSub W₁ Lg = ⊥
  have hWdLg : commSub ⊤ Lg = W₂ := w1369u_commSub_map_conj L g
  have hNconjmem : ∀ k ∈ A, ∀ n ∈ N, k * n * k⁻¹ ∈ N :=
    fun k hk n hn => (Subgroup.normal_subgroupOf_iff hNA).mp hN n k hn hk
  have hNconj : ∀ h ∈ A, StableUnder N (W₁.map h.toMonoidHom) := by
    intro h hhA n hn u hu
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hu
    have hn' : h⁻¹ * n * h ∈ N := hNconjmem h⁻¹ (A.inv_mem hhA) n hn
    refine Subgroup.mem_map.mpr ⟨(h⁻¹ * n * h) w, hU1 _ hn' w hw, ?_⟩
    show h.toMonoidHom ((h⁻¹ * n * h) w) = n.toMonoidHom (h.toMonoidHom w)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.apply_inv_self]
  have hLg_le_N : Lg ≤ N := by
    rw [Subgroup.map_le_iff_le_comap]
    intro l hl
    rw [Subgroup.mem_comap]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hNconjmem g hgA l (hLN hl)
  have hW1mem : W₁ ∈ conjSubs A W₁ := by
    refine ⟨1, A.one_mem, ?_⟩
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.one_apply]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  have hW2mem : W₂ ∈ conjSubs A W₁ := ⟨g, hgA, rfl⟩
  have hW12ne : W₁ ≠ W₂ := by
    intro heq
    apply hgN
    have hLg_eq : Lg = L := hU3 g hgA (show W₁.map g.toMonoidHom = W₁ from heq.symm)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLg_eq
  have hcomm2 : commSub W₁ Lg = ⊥ := by
    have hle1 : commSub W₁ Lg ≤ W₁ :=
      commSub_le_of_invariant fun b hb w hw => hU1 b (hLg_le_N hb) w hw
    have hle2 : commSub W₁ Lg ≤ W₂ := by
      have h : commSub W₁ Lg ≤ commSub ⊤ Lg := commSub_mono le_top le_rfl
      rwa [hWdLg] at h
    have hdisj : W₁ ⊓ W₂ = ⊥ :=
      disjoint_iff.mp (hind.pairwiseDisjoint hW1mem hW2mem hW12ne)
    have h := le_inf hle1 hle2
    rw [hdisj] at h
    exact le_bot_iff.mp h
  have hperX : ∀ X ∈ conjSubs A W₁, ⁅L, Lg⁆ ≤ centSub X := by
    intro X hXmem
    obtain ⟨h, hhA, hXeq⟩ := hXmem
    have hXmem' : X ∈ conjSubs A W₁ := ⟨h, hhA, hXeq⟩
    have hStable : StableUnder N X := by rw [hXeq]; exact hNconj h hhA
    have hNX : N ≤ stabSub X := w1369u_le_stabSub_of_stableUnder hStable
    have hleX : ∀ (K : Subgroup (MulAut W)) (hK : K ≤ N), commSub X K ≤ X :=
      fun K hK => commSub_le_of_invariant fun k hk w hw =>
        (mem_stabSub.mp (hNX (hK hk)) w).mpr hw
    by_cases hX1 : X = W₁
    ·
      have hXne2 : X ≠ W₂ := by rw [hX1]; exact hW12ne
      have hdisj : X ⊓ W₂ = ⊥ :=
        disjoint_iff.mp (hind.pairwiseDisjoint hXmem' hW2mem hXne2)
      have hcommLg_bot : commSub X Lg = ⊥ := by
        have hleW2 : commSub X Lg ≤ W₂ := by
          have h' : commSub X Lg ≤ commSub ⊤ Lg := commSub_mono le_top le_rfl
          rwa [hWdLg] at h'
        have h := le_inf (hleX Lg hLg_le_N) hleW2
        rw [hdisj] at h
        exact le_bot_iff.mp h
      have hfix_b : ∀ b ∈ Lg, b ∈ centSub X := fun b hb =>
        mem_centSub.mpr fun u hu => mem_fixV.mp (commSub_eq_bot_iff.mp hcommLg_bot hu) b hb
      refine (Subgroup.commutator_le).mpr fun a ha b hb => ?_
      refine mem_centSub.mpr fun u hu => ?_
      rw [commutatorElement_def]
      simp only [MulAut.mul_apply]
      have hb_inv : b⁻¹ u = u := by
        calc b⁻¹ u = b⁻¹ (b u) := by rw [mem_centSub.mp (hfix_b b hb) u hu]
          _ = u := MulAut.inv_apply_self W b u
      have ha_inv_mem : a⁻¹ u ∈ X :=
        (mem_stabSub.mp (hNX (N.inv_mem (hLN ha))) u).mpr hu
      have hba : b (a⁻¹ u) = a⁻¹ u := mem_centSub.mp (hfix_b b hb) (a⁻¹ u) ha_inv_mem
      rw [hb_inv, hba, MulAut.apply_inv_self]
    ·
      have hdisj : X ⊓ W₁ = ⊥ :=
        disjoint_iff.mp (hind.pairwiseDisjoint hXmem' hW1mem hX1)
      have hcommL_bot : commSub X L = ⊥ := by
        have hleW1 : commSub X L ≤ W₁ := commSub_mono le_top le_rfl
        have h := le_inf (hleX L hLN) hleW1
        rw [hdisj] at h
        exact le_bot_iff.mp h
      have hfix_a : ∀ a ∈ L, a ∈ centSub X := fun a ha =>
        mem_centSub.mpr fun u hu => mem_fixV.mp (commSub_eq_bot_iff.mp hcommL_bot hu) a ha
      refine (Subgroup.commutator_le).mpr fun a ha b hb => ?_
      refine mem_centSub.mpr fun u hu => ?_
      rw [commutatorElement_def]
      simp only [MulAut.mul_apply]
      have hb1 : b⁻¹ u ∈ X :=
        (mem_stabSub.mp (hNX (N.inv_mem (hLg_le_N hb))) u).mpr hu
      have hainv : a⁻¹ (b⁻¹ u) = b⁻¹ u :=
        calc a⁻¹ (b⁻¹ u) = a⁻¹ (a (b⁻¹ u)) := by
              rw [mem_centSub.mp (hfix_a a ha) (b⁻¹ u) hb1]
          _ = b⁻¹ u := MulAut.inv_apply_self W a (b⁻¹ u)
      rw [hainv, MulAut.apply_inv_self]
      exact mem_centSub.mp (hfix_a a ha) u hu
  have hle : ⁅L, Lg⁆ ≤ centSub ⊤ := w1369u_le_centSub_top_of_family hspan hperX
  rw [w1369u_centSub_top] at hle
  exact ⟨le_bot_iff.mp hle, hcomm2⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
