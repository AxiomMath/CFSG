module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineModelAux
public import CFSG.LocalAnalysis.StandardType.FS81.OrthInner
public import CFSG.LocalAnalysis.StandardType.FS81.OrthParity
public import CFSG.LocalAnalysis.StandardType.FS81.RowElemAbOrth
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MExt
public import CFSG.ClassicalGroups.Orthogonal.CharTwoReflectGen
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open
  CFSG.GroupTheory.WeirSylow
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
open CFSG.RankThree.Classical2 (orthDerived)

private theorem frameRot_Q_eq_one {A : Subgroup (V5 ≃ₗ[ZMod 2] V5)}
    (hAΩ : A ≤ orthDerived Q5) (F : SevOm.Frame Q5 3 A 5)
    (hU : ∀ k, finrank (ZMod 2) (F.U k) = 2) (i : Fin 5)
    {u : V5} (hu : u ∈ F.U i) (hu0 : u ≠ 0) : Q5 u = 1 := by
  classical
  let x : V5 ≃ₗ[ZMod 2] V5 := frameRot F i
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q5 :=
    (hAΩ.trans (Subgroup.commutator_le_self _)) (frameRot_mem F i)
  have hx3 : x ^ 3 = 1 := frameRot_pow_three F i
  have hxmaps : ∀ v ∈ F.U i, x v ∈ F.U i := fun v hv => F.mapsTo _ i v hv
  have hfpf : ∀ v ∈ F.U i, x v = v → v = 0 := by
    intro v hv h
    exact F.fpf (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3))) i
      (by rw [toAdd_ofAdd, Pi.single_eq_same]; exact one_ne_zero) v hv h
  by_contra hQ1
  have hQ0 : Q5 u = 0 := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Q5 u) with h | h
    · exact h
    · exact absurd h hQ1
  have hQxu : Q5 (x u) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hxO, hQ0]
  have hx2u : x (x u) = u + x u := by
    have hx3u : x (x (x u)) = u := by
      have h := congrArg (fun g => g u) hx3
      simpa [pow_succ, LinearEquiv.mul_apply] using h
    have hmem : x (x u) + x u + u ∈ F.U i :=
      (F.U i).add_mem ((F.U i).add_mem (hxmaps _ (hxmaps u hu)) (hxmaps u hu)) hu
    have hfix : x (x (x u) + x u + u) = x (x u) + x u + u := by
      simp only [map_add]
      rw [hx3u]
      abel
    have hzero : x (x u) + x u + u = 0 := hfpf _ hmem hfix
    have h1 : x (x u) + (x u + u) = 0 := by rw [← add_assoc]; exact hzero
    have h2 : x (x u) = -(x u + u) := eq_neg_of_add_eq_zero_left h1
    have h2' : x (x u) = u + x u := by
      rw [neg_add, CharTwo.neg_eq, CharTwo.neg_eq, add_comm] at h2
      exact h2
    exact h2'
  have hQx2u : Q5 (x (x u)) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hxO (x u), hQxu]
  have hQux : Q5 (u + x u) = 0 := by
    rw [← hx2u]
    exact hQx2u
  have hpolar : polar Q5 u (x u) = 0 := by
    have h := QuadraticMap.map_add Q5 u (x u)
    rw [hQux, hQ0, hQxu, zero_add, zero_add] at h
    exact h.symm
  have hli : LinearIndependent (ZMod 2) ![u, x u] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) a with ha | ha <;>
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) b with hb | hb
    · exact ⟨ha, hb⟩
    · subst ha; subst hb
      simp only [zero_smul, one_smul, zero_add] at hab
      exact absurd ((x.map_eq_zero_iff.mp hab)) hu0
    · subst ha; subst hb
      simp only [one_smul, zero_smul, add_zero] at hab
      exact absurd hab hu0
    · subst ha; subst hb
      simp only [one_smul] at hab
      have hxeq : u = x u := by
        have := eq_neg_of_add_eq_zero_left hab
        rwa [CharTwo.neg_eq] at this
      exact absurd (hfpf u hu hxeq.symm) hu0
  have hle : Submodule.span (ZMod 2) ({u, x u} : Set V5) ≤ F.U i := by
    rw [Submodule.span_le]
    intro v hv
    rcases hv with rfl | rfl
    · exact hu
    · exact hxmaps u hu
  have hspan : Submodule.span (ZMod 2) ({u, x u} : Set V5) = F.U i := by
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_)
    have hset : ({u, x u} : Set V5) = Set.range ![u, x u] := by
      ext v
      simp [or_comm]
    rw [hset, finrank_span_eq_card hli, hU i]
    simp
  have hvan : ∀ v ∈ F.U i, polar Q5 v u = 0 := by
    intro v hv
    have hvspan : v ∈ Submodule.span (ZMod 2) ({u, x u} : Set V5) := by
      rw [hspan]; exact hv
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hvspan
    rw [← hab]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_self, hQ0,
      QuadraticMap.polar_comm, hpolar]
    simp
  exact hu0 (F.nondeg i u hu hvan)

private lemma maps_perp_of_commute {W : Submodule (ZMod 2) V5} {h x : V5 ≃ₗ[ZMod 2] V5}
    (hxfix : ∀ v, x v = v ↔ v ∈ perpOf Q5 W) (hrel : h * x = x * h) :
    ∀ v ∈ perpOf Q5 W, h v ∈ perpOf Q5 W := by
  intro v hv
  have hvx : x v = v := (hxfix v).mpr hv
  have h1 : h (x v) = x (h v) := by
    have := congrArg (fun g => g v) hrel
    simpa [LinearEquiv.mul_apply] using this
  rw [hvx] at h1
  exact (hxfix (h v)).mp h1.symm

private lemma maps_perp_of_inv {W : Submodule (ZMod 2) V5} {h x : V5 ≃ₗ[ZMod 2] V5}
    (hxfix : ∀ v, x v = v ↔ v ∈ perpOf Q5 W) (hrel : h * x = x⁻¹ * h) :
    ∀ v ∈ perpOf Q5 W, h v ∈ perpOf Q5 W := by
  intro v hv
  have hvx : x v = v := (hxfix v).mpr hv
  have h1 : h (x v) = x⁻¹ (h v) := by
    have := congrArg (fun g => g v) hrel
    simpa [LinearEquiv.mul_apply] using this
  rw [hvx] at h1
  have h2 : x (h v) = h v := by
    have := congrArg (fun w => x w) h1
    simpa using this
  exact (hxfix (h v)).mp h2

private lemma maps_mem_of_maps_perp {W : Submodule (ZMod 2) V5} {h : V5 ≃ₗ[ZMod 2] V5}
    (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q5)
    (hperp_inv : ∀ v ∈ perpOf Q5 W, h⁻¹ v ∈ perpOf Q5 W) :
    ∀ v ∈ W, h v ∈ W := by
  intro v hv
  have hW : W = perpOf Q5 (perpOf Q5 W) := by
    rw [perpOf, perpOf, LinearMap.BilinForm.orthogonal_orthogonal nondegenerate_Q5
      (QuadraticMap.isSymm_polarBilin Q5).isRefl]
  rw [hW] at hv ⊢
  exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4.map_mem_perp hO hperp_inv hv

private lemma frameRot_sq_apply_of_mem {A : Subgroup (V5 ≃ₗ[ZMod 2] V5)}
    (F : SevOm.Frame Q5 3 A 5) {k : Fin 5} {w : V5} (hw : w ∈ F.U k) :
    frameRot F k (frameRot F k w) = w + frameRot F k w := by
  let x := frameRot F k
  have hx3 : x ^ 3 = 1 := frameRot_pow_three F k
  have hxmaps : ∀ v ∈ F.U k, x v ∈ F.U k := fun v hv => F.mapsTo _ k v hv
  have hfpf : ∀ v ∈ F.U k, x v = v → v = 0 := by
    intro v hv h
    exact F.fpf (Multiplicative.ofAdd (Pi.single k (1 : ZMod 3))) k
      (by rw [toAdd_ofAdd, Pi.single_eq_same]; exact one_ne_zero) v hv h
  have hx3w : x (x (x w)) = w := by
    have h := congrArg (fun g => g w) hx3
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  have hmem : x (x w) + x w + w ∈ F.U k :=
    (F.U k).add_mem ((F.U k).add_mem (hxmaps _ (hxmaps w hw)) (hxmaps w hw)) hw
  have hfix : x (x (x w) + x w + w) = x (x w) + x w + w := by
    simp only [map_add]
    rw [hx3w]
    abel
  have hzero : x (x w) + x w + w = 0 := hfpf _ hmem hfix
  have h1 : x (x w) + (x w + w) = 0 := by rw [← add_assoc]; exact hzero
  have h2 : x (x w) = -(x w + w) := eq_neg_of_add_eq_zero_left h1
  rw [neg_add, CharTwo.neg_eq, CharTwo.neg_eq, add_comm] at h2
  exact h2

private lemma span_frameRot_pair {A : Subgroup (V5 ≃ₗ[ZMod 2] V5)}
    (F : SevOm.Frame Q5 3 A 5) (hU : ∀ k, finrank (ZMod 2) (F.U k) = 2)
    {k : Fin 5} {w : V5} (hw : w ∈ F.U k) (hw0 : w ≠ 0) :
    Submodule.span (ZMod 2) ({w, frameRot F k w} : Set V5) = F.U k := by
  let x := frameRot F k
  have hxw_ne : x w ≠ w := by
    intro h
    exact hw0 (F.fpf (Multiplicative.ofAdd (Pi.single k (1 : ZMod 3))) k
      (by rw [toAdd_ofAdd, Pi.single_eq_same]; exact one_ne_zero) w hw h)
  have hli : LinearIndependent (ZMod 2) ![w, x w] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) a with ha | ha <;>
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) b with hb | hb
    · exact ⟨ha, hb⟩
    · subst ha; subst hb
      simp only [zero_smul, one_smul, zero_add] at hab
      exact absurd (x.map_eq_zero_iff.mp hab) hw0
    · subst ha; subst hb
      simp only [one_smul, zero_smul, add_zero] at hab
      exact absurd hab hw0
    · subst ha; subst hb
      simp only [one_smul] at hab
      have hxw : w = x w := by
        have := eq_neg_of_add_eq_zero_left hab
        rwa [CharTwo.neg_eq] at this
      exact absurd hxw.symm hxw_ne
  have hle : Submodule.span (ZMod 2) ({w, x w} : Set V5) ≤ F.U k := by
    rw [Submodule.span_le]
    intro v hv
    rcases hv with rfl | rfl
    · exact hw
    · exact F.mapsTo _ k w hw
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_)
  have hset : ({w, x w} : Set V5) = Set.range ![w, x w] := by
    ext v
    simp [or_comm]
  rw [hset, finrank_span_eq_card hli, hU k]
  simp

private lemma eq_one_on_piece_of_commute {A : Subgroup (V5 ≃ₗ[ZMod 2] V5)}
    (F : SevOm.Frame Q5 3 A 5) (hU : ∀ k, finrank (ZMod 2) (F.U k) = 2)
    {k : Fin 5} {h : V5 ≃ₗ[ZMod 2] V5} (hh2 : h * h = 1)
    (hmaps : ∀ v ∈ F.U k, h v ∈ F.U k)
    (hcomm : h * frameRot F k = frameRot F k * h) :
    ∀ v ∈ F.U k, h v = v := by
  by_contra hne
  push Not at hne
  obtain ⟨v, hv, hhv⟩ := hne
  let w : V5 := h v + v
  have hw_mem : w ∈ F.U k := (F.U k).add_mem (hmaps v hv) hv
  have hw_ne : w ≠ 0 := by
    intro h0
    apply hhv
    have h1 : h v = v := by
      have := eq_neg_of_add_eq_zero_left h0
      rwa [CharTwo.neg_eq] at this
    exact h1
  have hw_fix : h w = w := by
    dsimp only [w]
    rw [map_add, ← LinearEquiv.mul_apply, hh2]
    change v + h v = h v + v
    rw [add_comm]
  have hxw_ne : frameRot F k w ≠ w := by
    intro hxw
    exact hw_ne (F.fpf (Multiplicative.ofAdd (Pi.single k (1 : ZMod 3))) k
      (by rw [toAdd_ofAdd, Pi.single_eq_same]; exact one_ne_zero) w hw_mem hxw)
  have hxw_fix : h (frameRot F k w) = frameRot F k w := by
    have h1 := congrArg (fun g => g w) hcomm
    simpa [LinearEquiv.mul_apply, hw_fix] using h1
  have hspan := span_frameRot_pair F hU hw_mem hw_ne
  have hfix_all : ∀ y ∈ F.U k, h y = y := by
    intro y hy
    have hyspan : y ∈ Submodule.span (ZMod 2) ({w, frameRot F k w} : Set V5) := by
      rw [hspan]; exact hy
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hyspan
    rw [← hab, map_add, map_smul, map_smul, hw_fix, hxw_fix]
  exact hhv (hfix_all v hv)

private lemma maps_piece_of_perp {W : Submodule (ZMod 2) V5} {h : V5 ≃ₗ[ZMod 2] V5}
    (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q5)
    (hperp : ∀ v ∈ perpOf Q5 W, h v ∈ perpOf Q5 W) :
    ∀ v ∈ W, h v ∈ W := by
  have hperp_eq : Submodule.map (h : V5 →ₗ[ZMod 2] V5) (perpOf Q5 W) = perpOf Q5 W := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact hperp v hv
    · rw [LinearEquiv.finrank_map_eq]
  have hperp_inv : ∀ v ∈ perpOf Q5 W, h⁻¹ v ∈ perpOf Q5 W := by
    intro v hv
    rcases Submodule.mem_map.mp (hperp_eq ▸ hv) with ⟨w, hw, hwu⟩
    have : h⁻¹ v = w := by
      rw [← hwu]
      simp
    rwa [this]
  exact maps_mem_of_maps_perp hO hperp_inv

theorem mem_of_commute_frameRot {A : Subgroup (V5 ≃ₗ[ZMod 2] V5)}
    (hAΩ : A ≤ orthDerived Q5) (F : SevOm.Frame Q5 3 A 5)
    {c : V5 ≃ₗ[ZMod 2] V5} (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q5)
    (hcomm : ∀ k : Fin 5, c * frameRot F k * c⁻¹ = frameRot F k) : c ∈ A := by
  have hdim : finrank (ZMod 2) V5 = 2 * 5 := by
    simp [V5, Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
  have htype : IsPlusType Q5 ↔ Even 5 := by
    constructor
    · intro hplus
      exact absurd hplus (not_isPlusType_quadMinus (n := 5) (by norm_num)
        (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0))
    · rintro ⟨k, hk⟩
      omega
  have hcardA : Nat.card A = 3 ^ 5 := by
    have h := Subgroup.card_map_of_injective
      (K := (⊤ : Subgroup (Multiplicative (Fin 5 → ZMod 3)))) (f := F.ι) F.inj
    rw [Subgroup.map_top, F.range, Subgroup.card_top] at h
    rw [h]
    simp
  have hAel : IsElemAbelian 3 A := by
    have htop : IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (Fin 5 → ZMod 3))) := by
      rw [← Subgroup.closure_univ]
      refine IsElemAbelian.closure_of_commute ?_ ?_
      · intro a _ b _; exact mul_comm a b
      · intro x _
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one]
        ext i
        have h3 : (3 : ℕ) • (Multiplicative.toAdd x i) = 0 :=
          (by decide : ∀ z : ZMod 3, (3 : ℕ) • z = 0) _
        simpa using h3
    have h := htop.map F.ι
    rwa [Subgroup.map_top, F.range] at h
  have hmax : ∀ E' : Subgroup (V5 ≃ₗ[ZMod 2] V5),
      E' ≤ orthDerived Q5 → IsElemAbelian 3 E' → A ≤ E' → E' = A := by
    intro E' hE'Ω hE'el hAE'
    refine (Subgroup.eq_of_le_of_card_ge hAE' ?_).symm
    rw [hcardA]
    exact orth_card_elemAb3_le nondegenerate_Q5 hdim
      (hE'Ω.trans (Subgroup.commutator_le_self _)) hE'el
  obtain ⟨l, hl, hlen, hAtorus⟩ :=
    fs81_orth_maxElemAb3_eq_torus nondegenerate_Q5 hdim htype hAΩ hAel hmax
  have hgen : Subgroup.closure (Set.range (fun k : Fin 5 => frameRot F k)) = A := by
    have hg : Subgroup.closure (Set.range (fun k : Fin 5 =>
        Multiplicative.ofAdd (Pi.single k (1 : ZMod 3)))) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hsplit : x = ∏ i : Fin 5,
          Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd x i)) := by
        conv_lhs => rw [← ofAdd_toAdd x, ← Finset.univ_sum_single (Multiplicative.toAdd x),
          ofAdd_sum]
      rw [hsplit]
      refine Subgroup.prod_mem _ fun i _ => ?_
      have hsingle : Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd x i)) =
          (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin 5 → ZMod 3)) ^
            (Multiplicative.toAdd x i).val := by
        rw [← ofAdd_nsmul]
        congr 1
        rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd x i)]
        ext j
        by_cases hj : j = i <;> simp [hj]
      rw [hsingle]
      have hmem : Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin 5 → ZMod 3) ∈
          Subgroup.closure (Set.range (fun k : Fin 5 =>
            Multiplicative.ofAdd (Pi.single k (1 : ZMod 3) : Fin 5 → ZMod 3))) :=
        Subgroup.subset_closure ⟨i, rfl⟩
      exact Subgroup.pow_mem _ hmem _
    have hmap := MonoidHom.map_closure F.ι (Set.range fun k : Fin 5 =>
        Multiplicative.ofAdd (Pi.single k (1 : ZMod 3)))
    rw [hg, Subgroup.map_top, F.range] at hmap
    rw [← Set.range_comp] at hmap
    simpa [frameRot, Function.comp_def] using hmap.symm
  have hcA : c ∈ Subgroup.centralizer (A : Set (V5 ≃ₗ[ZMod 2] V5)) := by
    have hle : A ≤ Subgroup.centralizer ({c} : Set (V5 ≃ₗ[ZMod 2] V5)) := by
      rw [← hgen, Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have h := congrArg (fun y => y * c) (hcomm k)
      simpa [mul_assoc] using h.symm
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  have hcommrot : ∀ p ∈ l, Commute c (rot Q5 p.1 p.2) := by
    intro p hp
    have hrotA : rot Q5 p.1 p.2 ∈ A := by
      rw [hAtorus]
      exact rot_mem_torus hp
    have hmem' : rot Q5 p.1 p.2 ∈ Subgroup.centralizer ({c} : Set (V5 ≃ₗ[ZMod 2] V5)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hcA) (rot Q5 p.1 p.2) hrotA)
    exact (Subgroup.mem_centralizer_singleton_iff.mp hmem').symm
  have hfull : finrank (ZMod 2) V5 = 2 * l.length := by
    rw [hlen, hdim]
  have hcT := mem_torus_of_commute_rot hl hfull hc hcommrot
  rwa [← hAtorus] at hcT

theorem exists_eq_reflect_of_conj_frameRot {A : Subgroup (V5 ≃ₗ[ZMod 2] V5)}
    (hAΩ : A ≤ orthDerived Q5) (F : SevOm.Frame Q5 3 A 5)
    (hU : ∀ k, finrank (ZMod 2) (F.U k) = 2) (i : Fin 5) {h : V5 ≃ₗ[ZMod 2] V5}
    (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q5) (h2 : h * h = 1)
    (hconj : ∀ k : Fin 5, h * frameRot F k * h⁻¹ =
      if k = i then (frameRot F k)⁻¹ else frameRot F k) :
    ∃ u ∈ F.U i, Q5 u = 1 ∧ h = reflect Q5 u := by
  classical
  have hmaps : ∀ k : Fin 5, ∀ v ∈ F.U k, h v ∈ F.U k := by
    intro k v hv
    have hperp : ∀ w ∈ perpOf Q5 (F.U k), h w ∈ perpOf Q5 (F.U k) := by
      by_cases hki : k = i
      · subst hki
        have hrel : h * frameRot F k = (frameRot F k)⁻¹ * h := by
          have := hconj k
          rw [if_pos rfl] at this
          exact mul_inv_eq_iff_eq_mul.mp this
        exact maps_perp_of_inv (frameRot_fix_iff F k) hrel
      · have hrel : h * frameRot F k = frameRot F k * h := by
          have := hconj k
          rw [if_neg hki] at this
          exact mul_inv_eq_iff_eq_mul.mp this
        exact maps_perp_of_commute (frameRot_fix_iff F k) hrel
    exact maps_piece_of_perp hO hperp v hv
  have hfix_other : ∀ k : Fin 5, k ≠ i → ∀ v ∈ F.U k, h v = v := by
    intro k hki v hv
    have hrel : h * frameRot F k = frameRot F k * h := by
      have := hconj k
      rw [if_neg hki] at this
      exact mul_inv_eq_iff_eq_mul.mp this
    exact eq_one_on_piece_of_commute F hU h2 (hmaps k) hrel v hv
  have hne_i : ∃ v ∈ F.U i, h v ≠ v := by
    by_contra hno
    push Not at hno
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (F.U i)).mp (F.ne_bot i)
    have hvi : h v = v := hno v hv
    have hxvi : h (frameRot F i v) = frameRot F i v := hno _ (F.mapsTo _ i v hv)
    have hrel : h * frameRot F i = (frameRot F i)⁻¹ * h := by
      have := hconj i
      rw [if_pos rfl] at this
      exact mul_inv_eq_iff_eq_mul.mp this
    have h1 := congrArg (fun g => g v) hrel
    have h2 : frameRot F i v = (frameRot F i)⁻¹ v := by
      simpa [LinearEquiv.mul_apply, hvi, hxvi] using h1
    have h3 : frameRot F i (frameRot F i v) = v := by
      have := congrArg (fun w => frameRot F i w) h2
      simpa using this
    have hx3 := frameRot_pow_three F i
    have hx3v : frameRot F i (frameRot F i (frameRot F i v)) = v := by
      have := congrArg (fun g => g v) hx3
      simpa [pow_succ, LinearEquiv.mul_apply] using this
    have hxv : frameRot F i v = v := by
      have h4 : frameRot F i (frameRot F i (frameRot F i v)) = frameRot F i v := by
        rw [h3]
      rw [h4] at hx3v
      exact hx3v
    exact hv0 (F.fpf (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3))) i
      (by rw [toAdd_ofAdd, Pi.single_eq_same]; exact one_ne_zero) v hv hxv)
  obtain ⟨v, hv, hhv⟩ := hne_i
  let u : V5 := h v + v
  have hu_mem : u ∈ F.U i := (F.U i).add_mem (hmaps i v hv) hv
  have hu_ne : u ≠ 0 := by
    intro h0
    apply hhv
    have h1 : h v = v := by
      have := eq_neg_of_add_eq_zero_left h0
      rwa [CharTwo.neg_eq] at this
    exact h1
  have hu_fix : h u = u := by
    dsimp only [u]
    rw [map_add, ← LinearEquiv.mul_apply, h2]
    change v + h v = h v + v
    rw [add_comm]
  have hQu : Q5 u = 1 := frameRot_Q_eq_one hAΩ F hU i hu_mem hu_ne
  have hx2u : frameRot F i (frameRot F i u) = u + frameRot F i u :=
    frameRot_sq_apply_of_mem F hu_mem
  have hrel_i : h * frameRot F i = (frameRot F i)⁻¹ * h := by
    have := hconj i
    rw [if_pos rfl] at this
    exact mul_inv_eq_iff_eq_mul.mp this
  have hxinv : (frameRot F i)⁻¹ u = frameRot F i (frameRot F i u) := by
    have hx3 := frameRot_pow_three F i
    have hx2 : (frameRot F i)⁻¹ = frameRot F i ^ 2 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx3)
    rw [hx2, pow_two, LinearEquiv.mul_apply]
  have hu_x : h (frameRot F i u) = u + frameRot F i u := by
    have h1 := congrArg (fun g => g u) hrel_i
    simp only [LinearEquiv.mul_apply, hu_fix] at h1
    rw [hxinv, hx2u] at h1
    exact h1
  have hxune : frameRot F i u ≠ 0 := by
    intro h0
    exact hu_ne ((frameRot F i).map_eq_zero_iff.mp h0)
  have hQxu : Q5 (frameRot F i u) = 1 :=
    frameRot_Q_eq_one hAΩ F hU i (F.mapsTo _ i u hu_mem) hxune
  have hx2u_mem : frameRot F i (frameRot F i u) ∈ F.U i := by
    rw [hx2u]
    exact (F.U i).add_mem hu_mem (F.mapsTo _ i u hu_mem)
  have hx2u_ne : frameRot F i (frameRot F i u) ≠ 0 := by
    intro h0
    exact hu_ne ((frameRot F i).map_eq_zero_iff.mp ((frameRot F i).map_eq_zero_iff.mp h0))
  have hQx2u : Q5 (frameRot F i (frameRot F i u)) = 1 :=
    frameRot_Q_eq_one hAΩ F hU i hx2u_mem hx2u_ne
  have hQsum : Q5 (u + frameRot F i u) = 1 := by
    rw [← hx2u]
    exact hQx2u
  have hpolar_ux : polar Q5 u (frameRot F i u) = 1 := by
    have h := QuadraticMap.map_add Q5 u (frameRot F i u)
    rw [hQsum, hQu, hQxu] at h
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rw [h11, zero_add] at h
    exact h.symm
  have hρu : reflect Q5 u u = u := by
    rw [reflect_apply_of_map_eq_one hQu, QuadraticMap.polar_self, hQu]
    have h2 : (2 : ℕ) • (1 : ZMod 2) = 0 := by decide
    rw [h2, zero_smul, add_zero]
  have hρxu : reflect Q5 u (frameRot F i u) = frameRot F i u + u := by
    rw [reflect_apply_of_map_eq_one hQu, QuadraticMap.polar_comm, hpolar_ux, one_smul]
  have hspan_i : Submodule.span (ZMod 2) ({u, frameRot F i u} : Set V5) = F.U i :=
    span_frameRot_pair F hU hu_mem hu_ne
  have hdim : finrank (ZMod 2) V5 = 2 * 5 := by
    simp [V5, Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
  have htop : (iSup (fun j : {j : Fin 5 // True} => (F.U j.1 : Submodule (ZMod 2) V5))) = ⊤ := by
    have hfr := CFSG.StandardType.OrthTorusGen.finrank_iSup_frame_pieces F hU
      (fun _ : Fin 5 => True)
    apply Submodule.eq_top_of_finrank_eq
    rw [hfr, hdim]
    simp
  refine ⟨u, hu_mem, hQu, ?_⟩
  apply LinearEquiv.ext
  intro y
  have hy : y ∈ iSup (fun j : {j : Fin 5 // True} => (F.U j.1 : Submodule (ZMod 2) V5)) := by
    rw [htop]; trivial
  refine Submodule.iSup_induction
    (fun j : {j : Fin 5 // True} => (F.U j.1 : Submodule (ZMod 2) V5))
    (motive := fun y => h y = reflect Q5 u y) hy ?_ ?_ ?_
  · intro j y hyj
    by_cases hji : j.1 = i
    · have hyj' : y ∈ F.U i := by simpa [hji] using hyj
      have hyspan : y ∈ Submodule.span (ZMod 2) ({u, frameRot F i u} : Set V5) := by
        rw [hspan_i]; exact hyj'
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hyspan
      rw [← hab]
      change h (a • u + b • frameRot F i u) =
        reflect Q5 u (a • u + b • frameRot F i u)
      simp only [map_add, map_smul, hu_fix, hu_x, hρu, hρxu]
      rw [add_comm (frameRot F i u) u]
    · rw [hfix_other j.1 hji y hyj]
      exact (reflect_apply_of_polar_eq_zero
        (F.orth i j.1 (Ne.symm hji) u hu_mem y hyj)).symm
  · simp
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

end CFSG.StandardType.FrameRoute.FS81

end
