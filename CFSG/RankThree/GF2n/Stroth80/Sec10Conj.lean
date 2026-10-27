module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs
public import CFSG.RankThree.GF2n.Smith81.Sec220Conj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

private theorem conjSubgroup_sup_aux (g : G) (A B : Subgroup G) :
    conjSubgroup g (A ⊔ B) = conjSubgroup g A ⊔ conjSubgroup g B :=
  Subgroup.map_sup A B (MulAut.conj g).toMonoidHom

private def idxConj (g t : G) (M L : Subgroup G) :
    {m : G // m ∈ M ∧ t ∈ conjSubgroup m L} ≃
      {m' : G // m' ∈ conjSubgroup g M ∧
        g * t * g⁻¹ ∈ conjSubgroup m' (conjSubgroup g L)} where
  toFun i := by
    refine ⟨g * i.1 * g⁻¹, ?_, ?_⟩
    · rw [mem_conjSubgroup]
      simpa [mul_assoc] using i.2.1
    · have h : conjSubgroup (g * i.1 * g⁻¹) (conjSubgroup g L) =
          conjSubgroup g (conjSubgroup i.1 L) := by
        rw [← conjSubgroup_mul (g * i.1 * g⁻¹) g L, ← conjSubgroup_mul g i.1 L]
        congr 1
        group
      rw [h, mem_conjSubgroup]
      simpa [mul_assoc] using i.2.2
  invFun j := by
    refine ⟨g⁻¹ * j.1 * g, ?_, ?_⟩
    · exact mem_conjSubgroup.mp j.2.1
    · have h1 : conjSubgroup j.1 (conjSubgroup g L) = conjSubgroup (j.1 * g) L :=
        (conjSubgroup_mul j.1 g L).symm
      have h2 : conjSubgroup g (conjSubgroup (g⁻¹ * j.1 * g) L) =
          conjSubgroup (g * (g⁻¹ * j.1 * g)) L :=
        (conjSubgroup_mul g (g⁻¹ * j.1 * g) L).symm
      have h : conjSubgroup j.1 (conjSubgroup g L) =
          conjSubgroup g (conjSubgroup (g⁻¹ * j.1 * g) L) := by
        rw [h1, h2]
        congr 1
        group
      have hj := j.2.2
      rw [h, mem_conjSubgroup] at hj
      simpa [mul_assoc] using hj
  left_inv i := by
    ext
    group
  right_inv j := by
    ext
    group

theorem Vt_conjG (g : G) (M L B Z : Subgroup G) (t : G) :
    Vt (conjSubgroup g M) (conjSubgroup g L) (conjSubgroup g B) (conjSubgroup g Z)
      (g * t * g⁻¹) = conjSubgroup g (Vt M L B Z t) := by
  have hV : Vt M L B Z t =
      Z ⊔ ⨆ i : {m : G // m ∈ M ∧ t ∈ conjSubgroup m L}, conjSubgroup i.1 B := by
    simp only [Vt, iSup_and, iSup_subtype]
  have hV' : Vt (conjSubgroup g M) (conjSubgroup g L) (conjSubgroup g B)
        (conjSubgroup g Z) (g * t * g⁻¹) =
      conjSubgroup g Z ⊔ ⨆ j : {m' : G // m' ∈ conjSubgroup g M ∧
        g * t * g⁻¹ ∈ conjSubgroup m' (conjSubgroup g L)},
        conjSubgroup j.1 (conjSubgroup g B) := by
    simp only [Vt, iSup_and, iSup_subtype]
  rw [hV, hV', conjSubgroup_sup_aux]
  have hmap : conjSubgroup g
      (⨆ i : {m : G // m ∈ M ∧ t ∈ conjSubgroup m L}, conjSubgroup i.1 B) =
      ⨆ i : {m : G // m ∈ M ∧ t ∈ conjSubgroup m L},
        conjSubgroup g (conjSubgroup i.1 B) := by
    change (⨆ i : {m : G // m ∈ M ∧ t ∈ conjSubgroup m L},
      conjSubgroup i.1 B).map (MulAut.conj g).toMonoidHom = _
    rw [Subgroup.map_iSup]
    rfl
  rw [hmap]
  congr 1
  exact (Equiv.iSup_congr (idxConj g t M L) fun i => by
    change conjSubgroup (g * i.1 * g⁻¹) (conjSubgroup g B) =
      conjSubgroup g (conjSubgroup i.1 B)
    rw [← conjSubgroup_mul (g * i.1 * g⁻¹) g B, ← conjSubgroup_mul g i.1 B]
    congr 1
    group).symm

theorem GenByB.conjG {M Q B : Subgroup G} (h : GenByB M Q B) (g : G) :
    GenByB (conjSubgroup g M) (conjSubgroup g Q) (conjSubgroup g B) := by
  unfold GenByB at h ⊢
  rw [h]
  have hmap : conjSubgroup g (⨆ (m : G) (_ : m ∈ M), conjSubgroup m B) =
      ⨆ (m : G) (_ : m ∈ M), conjSubgroup g (conjSubgroup m B) := by
    change (⨆ (m : G) (_ : m ∈ M), conjSubgroup m B).map
      (MulAut.conj g).toMonoidHom = _
    simp only [Subgroup.map_iSup]
    rfl
  refine le_antisymm ?_ ?_
  · rw [hmap]
    refine iSup₂_le fun m hm => ?_
    have hterm : conjSubgroup g (conjSubgroup m B) =
        conjSubgroup (g * m * g⁻¹) (conjSubgroup g B) := by
      rw [← conjSubgroup_mul (g * m * g⁻¹) g B, ← conjSubgroup_mul g m B]
      congr 1
      group
    rw [hterm]
    refine le_iSup₂_of_le (g * m * g⁻¹) ?_ le_rfl
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hm
  · rw [hmap]
    refine iSup₂_le fun m' hm' => ?_
    have hm : g⁻¹ * m' * g ∈ M := mem_conjSubgroup.mp hm'
    have h1 : conjSubgroup m' (conjSubgroup g B) = conjSubgroup (m' * g) B :=
      (conjSubgroup_mul m' g B).symm
    have h2 : conjSubgroup g (conjSubgroup (g⁻¹ * m' * g) B) =
        conjSubgroup (g * (g⁻¹ * m' * g)) B :=
      (conjSubgroup_mul g (g⁻¹ * m' * g) B).symm
    have hterm : conjSubgroup m' (conjSubgroup g B) =
        conjSubgroup g (conjSubgroup (g⁻¹ * m' * g) B) := by
      rw [h1, h2]
      congr 1
      group
    rw [hterm]
    exact le_iSup₂_of_le (g⁻¹ * m' * g) hm le_rfl

theorem Width.conjG {Q Z : Subgroup G} {n : ℕ} (h : Width Q Z n) (g : G) :
    Width (conjSubgroup g Q) (conjSubgroup g Z) n := by
  unfold Width at h ⊢
  rw [card_conjSubgroup, card_conjSubgroup, h]

theorem Sec5Hyp.conjG [Finite G] {M Q Z B : Subgroup G}
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (h : Sec5Hyp hc n t) (g : G) :
    Sec5Hyp (hc.conjBy g) n (g * t * g⁻¹) where
  width := h.width.conjG g
  n_gt := h.n_gt
  noA2 := by
    rw [Smith81.LB_conj]
    exact (Smith81.noA2_conj_iff g).mpr h.noA2
  gen := h.gen.conjG g
  mem := by
    rw [Smith81.LB_conj]
    exact Subgroup.mem_map_of_mem _ h.mem
  notQ := by
    intro hq
    rw [mem_conjSubgroup] at hq
    apply h.notQ
    simpa [mul_assoc] using hq

theorem NaturalRep.conjG {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {X : Subgroup (GL ι K)} {R V Z N : Subgroup G} (h : NaturalRep K X R V Z N) (g : G) :
    NaturalRep K X (conjSubgroup g R) (conjSubgroup g V) (conjSubgroup g Z)
      (conjSubgroup g N) := by
  let e : G ≃* G := MulAut.conj g
  change NaturalRep K X (Subgroup.map (e : G →* G) R)
    (Subgroup.map (e : G →* G) V) (Subgroup.map (e : G →* G) Z)
    (Subgroup.map (e : G →* G) N)
  obtain ⟨φ, hrange, hker, hact⟩ := h
  let c : ↥(Subgroup.map (e : G →* G) R) ≃* ↥R := (MulEquiv.subgroupMap e R).symm
  let φ' : ↥(Subgroup.map (e : G →* G) R) →* GL ι K := φ.comp c.toMonoidHom
  have hφ : ∀ s : ↥R,
      φ' ⟨e ↑s, Subgroup.mem_map_of_mem (e : G →* G) s.2⟩ = φ s := by
    intro s
    show φ (c ((MulEquiv.subgroupMap e R) s)) = φ s
    congr 1
    exact MulEquiv.symm_apply_apply _ _
  have hsec : SectionAct K (Subgroup.map (e : G →* G) R)
      (Subgroup.map (e : G →* G) V) (Subgroup.map (e : G →* G) Z)
      φ' (fun g => (g : Matrix ι ι K)) :=
    SectionAct.map (e := e) hact (φ' := φ') hφ
  refine ⟨φ', ?_, ?_, hsec⟩
  · rw [← hrange]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨c x, rfl⟩
    · rintro ⟨r, rfl⟩
      refine ⟨c.symm r, ?_⟩
      show φ (c (c.symm r)) = φ r
      rw [c.apply_symm_apply]
  · ext x
    change φ (c x) = 1 ↔
      x ∈ (Subgroup.map (e : G →* G) N).subgroupOf (Subgroup.map (e : G →* G) R)
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hc : ((MulEquiv.subgroupMap e R).symm x : G) = e.symm (x : G) := by
      rw [MulEquiv.subgroupMap_symm_apply]
    have hEN : Subgroup.map ((e : G ≃* G) : G →* G) N = conjSubgroup g N := rfl
    rw [hEN]
    change ((MulEquiv.subgroupMap e R).symm x : G) ∈ N ↔ (x : G) ∈ conjSubgroup g N
    rw [hc, mem_conjSubgroup]
    rfl

theorem Ctx.CN_conjG [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) (g : G) (t : G) :
    (hc.conjBy g).CN (g * t * g⁻¹) = conjSubgroup g (hc.CN t) := by
  ext x
  change x ∈ CNt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q)
      (conjSubgroup g B)) (conjSubgroup g B) (conjSubgroup g Z) (g * t * g⁻¹) ↔
    x ∈ conjSubgroup g (hc.CN t)
  rw [Smith81.LB_conj, mem_conjSubgroup]
  change x ∈ CNt (conjSubgroup g M) (conjSubgroup g (LB M Q B)) (conjSubgroup g B)
      (conjSubgroup g Z) (g * t * g⁻¹) ↔ g⁻¹ * x * g ∈ CNt M (LB M Q B) B Z t
  have hset : CNt (conjSubgroup g M) (conjSubgroup g (LB M Q B)) (conjSubgroup g B)
      (conjSubgroup g Z) (g * t * g⁻¹) =
      {y | g⁻¹ * y * g ∈ CNt M (LB M Q B) B Z t} := by
    ext y
    unfold CNt
    rw [Set.mem_setOf_eq, Smith81.Rt_conj, Vt_conjG]
    constructor
    · rintro ⟨hyR, hyV⟩
      refine ⟨mem_conjSubgroup.mp hyR, fun v hv => ?_⟩
      have hv' : g * v * g⁻¹ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
        Subgroup.mem_map_of_mem _ hv
      have := hyV _ hv'
      rw [mem_conjSubgroup] at this
      rwa [show g⁻¹ * ⁅y, g * v * g⁻¹⁆ * g = ⁅g⁻¹ * y * g, v⁆ by
        simp only [commutatorElement_def]
        group] at this
    · rintro ⟨hyR, hyV⟩
      refine ⟨mem_conjSubgroup.mpr hyR, fun v hv => ?_⟩
      obtain ⟨w, hw, rfl⟩ := hv
      rw [mem_conjSubgroup]
      rw [show g⁻¹ * ⁅y, (MulEquiv.toMonoidHom (MulAut.conj g)) w⁆ * g =
        ⁅g⁻¹ * y * g, w⁆ by
        simp only [commutatorElement_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group]
      exact hyV w hw
  rw [hset, Set.mem_setOf_eq]

theorem SLMNat.conjG [Finite G] {M Q Z B : Subgroup G}
    {hc : Ctx M Q Z B} {t : G} {m : ℕ} (h : SLMNat hc t m) (g : G) :
    SLMNat (hc.conjBy g) (g * t * g⁻¹) m := by
  obtain ⟨K, hK, hKf, hcard, hrep⟩ := h
  refine ⟨K, hK, hKf, ?_, ?_⟩
  · rw [card_conjSubgroup]
    exact hcard
  · rw [Smith81.LB_conj, Smith81.Rt_conj, Vt_conjG, Ctx.CN_conjG]
    exact hrep.conjG g

theorem SpMNat.conjG [Finite G] {M Q Z B : Subgroup G}
    {hc : Ctx M Q Z B} {t : G} {m : ℕ} (h : SpMNat hc t m) (g : G) :
    SpMNat (hc.conjBy g) (g * t * g⁻¹) m := by
  obtain ⟨K, hK, hKf, hcard, hrep⟩ := h
  refine ⟨K, hK, hKf, ?_, ?_⟩
  · rw [card_conjSubgroup]
    exact hcard
  · rw [Smith81.LB_conj, Smith81.Rt_conj, Vt_conjG, Ctx.CN_conjG]
    exact hrep.conjG g

theorem SLlike.conjG [Finite G] {M Q Z B : Subgroup G}
    {hc : Ctx M Q Z B} {t : G} (h : SLlike hc t) (g : G) :
    SLlike (hc.conjBy g) (g * t * g⁻¹) := by
  obtain ⟨m, hm2, hm | ⟨hm, hsp⟩⟩ := h
  · exact ⟨m, hm2, Or.inl (hm.conjG g)⟩
  · exact ⟨m, hm2, Or.inr ⟨hm, hsp.conjG g⟩⟩

end CFSG.RankThree.GF2n.Stroth80
