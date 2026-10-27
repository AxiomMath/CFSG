module

public import CFSG.Quasithin.Background.G12Forms
public import CFSG.Quasithin.Background.G12Part4Stmt
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.Quasithin.G11

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V}

theorem g12_exists_mem_hyperplane_inter (hB : IsSymplectic B) (hd : 4 ≤ Module.finrank (ZMod 2) V)
    {W : Submodule (ZMod 2) V} (hW : Module.finrank (ZMod 2) W + 1 = Module.finrank (ZMod 2) V)
    {v w : V} (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    ∃ x ∈ W, x ≠ 0 ∧ B v x = 0 ∧ B w x = 0 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (perp B v)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ perp B v) (perp B w)
  have h3 := Submodule.finrank_le (W ⊔ perp B v)
  have h4 := Submodule.finrank_le ((W ⊓ perp B v) ⊔ perp B w)
  have hpv := hB.finrank_perp hv0
  have hpw := hB.finrank_perp hw0
  have hpos : 0 < Module.finrank (ZMod 2) ↥(W ⊓ perp B v ⊓ perp B w) := by omega
  obtain ⟨x, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hxm := x.2
  rw [Submodule.mem_inf, Submodule.mem_inf] at hxm
  exact ⟨x, hxm.1.1, fun h => hx0 (Subtype.ext h), mem_perp_iff.1 hxm.1.2, mem_perp_iff.1 hxm.2⟩

theorem g12_hyperplane_eq_perp (hB : IsSymplectic B) (hd : 4 ≤ Module.finrank (ZMod 2) V)
    {Q : Subgroup (GLV V)} (hQ : Q ≤ spSub B) {W : Submodule (ZMod 2) V}
    (hW : Module.finrank (ZMod 2) W + 1 = Module.finrank (ZMod 2) V) {v : V}
    (hv_mem : v ∈ W) (hv0 : v ≠ 0) (hT : FullTransvections Q W v hv_mem) : W = perp B v := by
  have hle : W ≤ perp B v := by
    intro w hw
    rw [mem_perp_iff]
    by_contra hne
    have hvw : B v w = 1 := g12_eq_one_of_ne_zero _ hne
    have hw0 : w ≠ 0 := fun h => by
      rw [h, map_zero] at hvw
      exact absurd hvw (by decide)
    obtain ⟨x, hxW, hx0, hvx, hwx⟩ := g12_exists_mem_hyperplane_inter hB hd hW hv0 hw0
    have hxv : x ≠ v := fun h => by
      rw [h, hB.symm' w v, hvw] at hwx
      exact absurd hwx (by decide)
    have hnot : (⟨x, hxW⟩ : ↥W) ∉ Submodule.span (ZMod 2) {(⟨v, hv_mem⟩ : ↥W)} := by
      intro hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have hc' : c • v = x := congrArg Subtype.val hc
      rcases g12_eq_zero_or_one c with h0 | h1
      · rw [h0, zero_smul] at hc'
        exact hx0 hc'.symm
      · rw [h1, one_smul] at hc'
        exact hxv hc'.symm
    obtain ⟨φ, hφp, hφx⟩ := LinearMap.exists_extend_of_notMem
      (0 : Submodule.span (ZMod 2) {(⟨v, hv_mem⟩ : ↥W)} →ₗ[ZMod 2] ZMod 2) hnot 1
    have hφv : φ ⟨v, hv_mem⟩ = 0 := by
      have := congrArg (fun g => g ⟨⟨v, hv_mem⟩, Submodule.mem_span_singleton_self _⟩) hφp
      simpa using this
    obtain ⟨y, hyQ, hy⟩ := hT.2 φ hφv
    have hyx := hy ⟨x, hxW⟩
    have hyw := hy ⟨w, hw⟩
    simp only [hφx, one_smul] at hyx
    have hiso := hQ hyQ x w
    have hxw : B x w = 0 := by rw [hB.symm']; exact hwx
    have hxv' : B x v = 0 := by rw [hB.symm']; exact hvx
    have hyx' : y x = x + v := hyx
    have hyw' : y w = w + φ ⟨w, hw⟩ • v := hyw
    rw [hyx', hyw'] at hiso
    simp only [map_add, LinearMap.add_apply, map_smul, smul_eq_mul, hxw, hxv',
      hvw, hB.1 v, mul_zero, add_zero, zero_add] at hiso
    exact absurd hiso (by decide)
  exact Submodule.eq_of_le_of_finrank_eq hle (by have := hB.finrank_perp hv0; omega)

omit [Finite V] in
theorem g12_exists_mem_orbit_not_mem {K : Subgroup (GLV V)} (hirr : IsIrr K ⊤) {v : V} (hv0 : v ≠ 0)
    {W : Submodule (ZMod 2) V} (hW : W ≠ ⊤) : ∃ k ∈ K, k v ∉ W := by
  by_contra H
  simp only [not_exists, not_and, not_not] at H
  have hinv : Invariant K (Submodule.span (ZMod 2) (orbitSet K v)) := by
    intro k hk u hu
    induction hu using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (orbitSet_apply_mem hk hx)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  have hv : v ∈ Submodule.span (ZMod 2) (orbitSet K v) :=
    Submodule.subset_span (mem_orbitSet_self (Γ := K))
  rcases hirr.2.2 _ hinv bot_le le_top with h | h
  · rw [h] at hv
    exact hv0 (by simpa using hv)
  · apply hW
    rw [eq_top_iff, ← h]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    exact H k hk

section Main

variable {Q K H : Subgroup (GLV V)}

theorem g12_12_of_part4 (h : G121Stmt) (h4 : G1212Part4) : G1212Stmt := by
  intro V _ _ _ H K Q W v hyp
  have hd3 : 3 ≤ Module.finrank (ZMod 2) V := hyp.dim
  have hK2 : ∀ g ∈ Q, ∀ k ∈ K, g⁻¹ * k * g ∈ K := fun g hg k hk => by
    have := hyp.normal g⁻¹ (H.inv_mem (hyp.q_le hg)) k hk
    simpa using this
  obtain ⟨f0, hf0, hf0i⟩ : ∃ f0 : LinearMap.BilinForm (ZMod 2) V, f0 ≠ 0 ∧ FormInv K f0 := by
    obtain ⟨f, hnd, hinv⟩ := hyp.selfDual
    let e : V →ₗ[ZMod 2] ↥(⊤ : Submodule (ZMod 2) V) :=
      (Submodule.topEquiv.symm : V ≃ₗ[ZMod 2] ↥(⊤ : Submodule (ZMod 2) V)).toLinearMap
    refine ⟨f.compl₁₂ e e, ?_, fun k hk x y => ?_⟩
    · intro h0
      obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 :=
        (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2) (M := V)).1 (by omega)
      have h1 : (⟨x, trivial⟩ : ↥(⊤ : Submodule (ZMod 2) V)) = 0 := by
        apply hnd.1
        intro y'
        have h2 : (f.compl₁₂ e e) x y'.1 = 0 := by rw [h0]; rfl
        exact h2
      exact hx (congrArg Subtype.val h1)
    · exact hinv k hk ⟨x, trivial⟩ ⟨y, trivial⟩ ⟨k x, trivial⟩ ⟨k y, trivial⟩ rfl rfl
  obtain ⟨f, hf, hfK, hfQ⟩ := g12_exists_symplectic_form hyp.irr hd3 ⟨f0, hf0, hf0i⟩ hK2 hyp.q_sq
  have hKsp : K ≤ spSub f := fun k hk x y => hfK k hk x y
  have hQsp : Q ≤ spSub f := fun g hg x y => hfQ g hg x y
  have hKQ : K ⊔ Q ≤ spSub f := sup_le hKsp hQsp
  have hd4 : 4 ≤ Module.finrank (ZMod 2) V := by
    obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank hf.1 hf.nondegenerate
    omega
  have hW : W = perp f v :=
    g12_hyperplane_eq_perp hf hd4 hQsp hyp.hyperplane hyp.v_mem hyp.v_ne hyp.transvections
  have hstar : IsStarVec f (K ⊔ Q) v := by
    rw [isStarVec_iff_rad hf hKQ]
    refine ⟨hyp.v_ne, fun a hva => ?_⟩
    let φ : ↥W →ₗ[ZMod 2] ZMod 2 := (f.flip a).comp W.subtype
    have hφ : φ ⟨v, hyp.v_mem⟩ = 0 := hva
    obtain ⟨y, hyQ, hy⟩ := hyp.transvections.2 φ hφ
    refine exists_radE_of_fix hf hKQ hva (Subgroup.mem_sup_right hyQ) fun u hu => ?_
    have hu' : u ∈ W := by rw [hW]; exact hu
    exact hy ⟨u, hu'⟩
  have hstarK : ∀ k ∈ K, IsStarVec f (K ⊔ Q) (k v) := fun k hk =>
    hstar.conj hf hKQ (Subgroup.mem_sup_left hk)
  have hWtop : W ≠ ⊤ := fun h' => by
    have := hyp.hyperplane
    rw [h', finrank_top] at this
    omega
  obtain ⟨k0, hk0, hk0W⟩ := g12_exists_mem_orbit_not_mem hyp.irr hyp.v_ne hWtop
  have hbk : f (k0 v) v ≠ 0 := by
    intro h0
    apply hk0W
    rw [hW, mem_perp_iff, hf.symm']
    exact h0
  have hconcl : G121Concl f (K ⊔ Q) v :=
    h V f (K ⊔ Q) (k0 v) v hf hKQ (hstarK k0 hk0) hstar hbk hd4
  have hconclH : H ≤ spSub f → G121Concl f H v := fun hHf =>
    h V f H (k0 v) v hf hHf (IsStarVec.mono hf hKQ hHf (sup_le hyp.le hyp.q_le) (hstarK k0 hk0))
      (IsStarVec.mono hf hKQ hHf (sup_le hyp.le hyp.q_le) hstar) hbk hd4
  exact ⟨f, hf, hKQ, hW, hstarK, ⟨k0, hyp.le hk0, hk0W⟩, h4 V H K Q W v f hyp hf hKQ hW hconcl,
    hconcl, hconclH⟩

end Main


end NoInst

end CFSG.Quasithin.G11
