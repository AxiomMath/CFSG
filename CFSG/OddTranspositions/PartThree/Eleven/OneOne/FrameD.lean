module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.FrameLift
import CFSG.OddTranspositions.SixEight
import CFSG.OddTranspositions.FusionStep
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.SecondKindCoset

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity


variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenOneHyp

variable {hC : HypothesisC D}

private theorem s11f3_inter_D_centralizer_eq (h : ElevenOneHyp hC) {a : G} (ha1 : a ≠ 1)
    (ha : ∀ x ∈ ({hC.d} : Set G) ∪ DalphaStar D hC.alpha, Commute a x) :
    D ∩ (Subgroup.centralizer ({a} : Set G) : Set G) =
      ({hC.d} : Set G) ∪ DalphaStar D hC.alpha := by
  set X : Subgroup G :=
    Subgroup.closure (D ∩ (Subgroup.centralizer ({a} : Set G) : Set G)) with hXdef
  have hXle : X ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [hXdef]
    exact (Subgroup.closure_le _).mpr (fun x hx => hx.2)
  have hXinter : (X : Set G) ∩ D =
      D ∩ (Subgroup.centralizer ({a} : Set G) : Set G) := by
    ext x
    constructor
    · rintro ⟨hxX, hxD⟩
      exact ⟨hxD, hXle hxX⟩
    · rintro ⟨hxD, hxC⟩
      exact ⟨Subgroup.subset_closure ⟨hxD, hxC⟩, hxD⟩
  have hXclosure : X = Subgroup.closure ((X : Set G) ∩ D) := by
    rw [hXinter, ← hXdef]
  have hdX : hC.d ∈ X := by
    rw [hXdef]
    exact Subgroup.subset_closure
      ⟨hC.hd, Subgroup.mem_centralizer_singleton_iff.mpr (ha hC.d (Or.inl rfl)).symm⟩
  have hEX : hC.E ⊆ (X : Set G) := by
    intro e he
    rw [← hC.DalphaStar_alpha] at he
    rw [hXdef]
    exact Subgroup.subset_closure
      ⟨DalphaStar_subset hC.isBlock_alpha he,
        Subgroup.mem_centralizer_singleton_iff.mpr (ha e (Or.inr he)).symm⟩
  have hproper : X ≠ ⊤ := by
    intro htop
    have hcenter : a ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hgX : g ∈ X := htop.symm ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp (hXle hgX)
    have hbot : Subgroup.center G = ⊥ :=
      h.rad (Subgroup.center G) inferInstance inferInstance
    have : a ∈ (⊥ : Subgroup G) := hbot ▸ hcenter
    exact ha1 (by simpa using this)
  have hsub := inter_D_subset_perp hC hXclosure hdX hEX hproper
  rw [hXinter] at hsub
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    have := hsub hx
    nth_rewrite 1 [h.alpha_eq] at this
    exact this
  · rintro x (rfl | hxE)
    · exact ⟨hC.hd, Subgroup.mem_centralizer_singleton_iff.mpr (ha hC.d (Or.inl rfl)).symm⟩
    · exact ⟨DalphaStar_subset hC.isBlock_alpha hxE,
        Subgroup.mem_centralizer_singleton_iff.mpr (ha x (Or.inr hxE)).symm⟩

private theorem s11f3_prod_ofFn_four {α : Type*} [Group α] (f : Fin 4 → α) :
    (List.ofFn f).prod = f 0 * f 1 * f 2 * f 3 := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  have h1 : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := rfl
  have h2 : ((Fin.succ (0 : Fin 2) : Fin 3).succ : Fin 4) = 2 := rfl
  have h3 : (((Fin.succ (0 : Fin 1) : Fin 2).succ : Fin 3).succ : Fin 4) = 3 := rfl
  rw [h1, h2, h3]
  group

private theorem s11f3_prod_map_conj_eq {n : G} {l : List G} (hnodup : l.Nodup)
    (hmem : ∀ x, x ∈ l ↔ n * x * n⁻¹ ∈ l)
    (hcomm : ∀ x ∈ l, ∀ y ∈ l, Commute x y) :
    (l.map (fun x => n * x * n⁻¹)).prod = l.prod := by
  have hinj : Function.Injective (fun x : G => n * x * n⁻¹) := by
    intro a b hab
    have := congrArg (fun y => n⁻¹ * y * n) hab
    simpa using this
  have hmem' : ∀ x ∈ l.map (fun x => n * x * n⁻¹), x ∈ l := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact (hmem y).mp hy
  have hmem'' : ∀ x ∈ l, x ∈ l.map (fun x => n * x * n⁻¹) := by
    intro x hx
    have hx' : n * (n⁻¹ * x * n) * n⁻¹ ∈ l := by
      rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group]
      exact hx
    exact List.mem_map.mpr ⟨n⁻¹ * x * n, (hmem _).mpr hx', by group⟩
  have hperm : List.Perm (l.map (fun x => n * x * n⁻¹)) l :=
    List.Subperm.antisymm
      (List.Nodup.subperm (List.Nodup.map hinj hnodup) hmem')
      (List.Nodup.subperm hnodup hmem'')
  refine List.Perm.prod_eq' hperm ?_
  exact List.Nodup.pairwise_of_forall_ne (List.Nodup.map hinj hnodup) (fun x hx y hy _ => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    exact (hcomm a ha b hb).conj n)

theorem d_mem_Halpha_of_frameLift (h : ElevenOneHyp hC) {T : Sylow 2 (Halpha D hC.alpha)}
    {r : Fin 4 → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hr : O4PlusFrame (imageClass hC) ((T : Subgroup (Halpha D hC.alpha)).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))) r)
    {w : Fin 4 → Halpha D hC.alpha}
    (hwr : ∀ i, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w i) = r i)
    (hw : (T : Set (Halpha D hC.alpha)) ∩ DstarH hC = Set.range w) {S : Sylow 2 G}
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S)
    (hd : hC.d ∈ (S : Subgroup G)) (hp : w 0 * w 1 * w 2 * w 3 ≠ 1) :
    hC.d ∈ Halpha D hC.alpha := by
  classical
  by_contra hu
  let v : Fin 4 → G := fun i => (w i : G)
  let p : Halpha D hC.alpha := w 0 * w 1 * w 2 * w 3
  let e : G := hC.d * (p : G)
  let l : List G := hC.d :: List.ofFn v
  have hΔ : (S : Set G) ∩ D = insert hC.d (Set.range v) := by
    simpa [v] using inter_D_eq_of_frameLift h hw S.isPGroup' hTS hd
  have hw_mem : ∀ i, w i ∈ DstarH hC := by
    intro i
    have : w i ∈ Set.range w := Set.mem_range_self i
    rw [← hw] at this
    exact this.2
  have hv_mem : ∀ i, v i ∈ DalphaStar D hC.alpha := fun i =>
    (mem_DstarH_iff hC).mp (hw_mem i)
  have hv_inj : Function.Injective v := by
    intro i j hij
    have hwij : w i = w j := Subtype.ext hij
    exact hr.injective (by rw [← hwr i, ← hwr j, hwij])
  have hd_notin : hC.d ∉ Set.range v := by
    rintro ⟨i, hi⟩
    exact hu (Subgroup.subset_closure (hi ▸ hv_mem i))
  have hl_nodup : l.Nodup := by
    dsimp only [l]
    rw [List.nodup_cons, List.nodup_ofFn]
    exact ⟨fun hmem => by
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
      exact hd_notin ⟨i, hi⟩, hv_inj⟩
  have mem_l : ∀ x : G, x ∈ l ↔ x ∈ (S : Set G) ∩ D := by
    intro x
    rw [hΔ]
    dsimp only [l]
    simp only [List.mem_cons, List.mem_ofFn, Set.mem_insert_iff, Set.mem_range]
  have hcomm : ∀ x ∈ l, ∀ y ∈ l, Commute x y := by
    intro x hx y hy
    exact hC.setup.oddT.commute_of_isPGroup S.isPGroup'
      ((mem_l x).mp hx).2 ((mem_l y).mp hy).2 ((mem_l x).mp hx).1 ((mem_l y).mp hy).1
  have hpM : p ∈ CFSG.solvableRadical (Halpha D hC.alpha) :=
    prod_frameLift_mem (hC := hC) hr hwr
  have hpZ : p ∈ Subgroup.center (Halpha D hC.alpha) := by
    rwa [h.center] at hpM
  have he1 : e ≠ 1 := by
    intro he
    apply hu
    have he' : hC.d * (p : G) = 1 := by simpa only [e] using he
    rw [eq_inv_of_mul_eq_one_left he']
    exact Subgroup.inv_mem _ p.2
  have he_comm : ∀ x ∈ ({hC.d} : Set G) ∪ DalphaStar D hC.alpha, Commute e x := by
    intro x hx
    rcases hx with hx | hxE
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      have hpu : Commute (p : G) hC.d :=
        Subgroup.mem_centralizer_singleton_iff.mp (Halpha_le_centralizer_d hC p.2)
      have hup : Commute hC.d (p : G) := hpu.symm
      have : Commute (hC.d * (p : G)) hC.d := ((Commute.refl hC.d).mul_right hup).symm
      simpa only [e] using this
    · have hux : Commute hC.d x := (hC.DalphaStar_subset_commute hxE).2.symm
      have hpx : Commute (p : G) x := by
        have hment : x ∈ Halpha D hC.alpha := Subgroup.subset_closure hxE
        have hc : (⟨x, hment⟩ : Halpha D hC.alpha) * p = p * ⟨x, hment⟩ :=
          Subgroup.mem_center_iff.mp hpZ (⟨x, hment⟩ : Halpha D hC.alpha)
        exact Subtype.ext_iff.mp hc.symm
      have : Commute (hC.d * (p : G)) x := hux.mul_left hpx
      simpa only [e] using this
  have hCe := s11f3_inter_D_centralizer_eq (h := h) he1 he_comm
  have hf : (w 0 : G) ∈ (S : Set G) ∩ D := by
    rw [hΔ]
    exact Or.inr ⟨0, rfl⟩
  obtain ⟨n, hn, hnu⟩ :=
    sylow_inter_D_transitive hC.setup.isClass hC.setup.oddT S ⟨hd, hC.hd⟩ hf
  have hmem_n : ∀ x, x ∈ l ↔ n * x * n⁻¹ ∈ l := by
    intro x
    have hn' : ∀ h : G, h ∈ ((S : Set G) ∩ D) ↔ n * h * n⁻¹ ∈ ((S : Set G) ∩ D) :=
      Subgroup.mem_set_normalizer_iff.mp hn
    rw [mem_l x, mem_l (n * x * n⁻¹)]
    exact hn' x
  have hconj_e : n * e * n⁻¹ = e := by
    have hprod := s11f3_prod_map_conj_eq (l := l) hl_nodup hmem_n hcomm
    have hl'_prod : (l.map (fun x => n * x * n⁻¹)).prod = n * l.prod * n⁻¹ := by
      have h := List.prod_map_hom l id (MulAut.conj n)
      have hfun : (fun x : G => n * x * n⁻¹) = ⇑(MulAut.conj n) := by
        funext x
        rw [MulAut.conj_apply]
      rw [hfun]
      simpa using h
    have he_l : e = l.prod := by
      dsimp only [e, p, l, v]
      rw [List.prod_cons, s11f3_prod_ofFn_four]
      rfl
    rw [he_l, ← hl'_prod]
    exact hprod
  have hv0_comm : ∀ x ∈ DalphaStar D hC.alpha, Commute (w 0 : G) x := by
    intro x hxE
    have hxD : x ∈ D := DalphaStar_subset hC.isBlock_alpha hxE
    have hyD : n⁻¹ * x * n ∈ D := by
      simpa only [inv_inv] using hC.setup.normal n⁻¹ x hxD
    have hex : Commute e x := he_comm x (Or.inr hxE)
    have hninv_e : n⁻¹ * e * n = e := by
      calc n⁻¹ * e * n = n⁻¹ * (n * e * n⁻¹) * n := by rw [hconj_e]
        _ = e := by group
    have he_y : Commute e (n⁻¹ * x * n) := by
      have hc := hex.conj n⁻¹
      rwa [inv_inv, hninv_e] at hc
    have hy_union : n⁻¹ * x * n ∈ ({hC.d} : Set G) ∪ DalphaStar D hC.alpha := by
      have : n⁻¹ * x * n ∈ D ∩ (Subgroup.centralizer ({e} : Set G) : Set G) :=
        ⟨hyD, Subgroup.mem_centralizer_singleton_iff.mpr he_y.symm⟩
      rwa [hCe] at this
    have hu_y : Commute hC.d (n⁻¹ * x * n) := by
      rcases hy_union with hy | hy
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
      · exact (hC.DalphaStar_subset_commute hy).2.symm
    have hconj_u := hu_y.conj n
    rw [show (n * (n⁻¹ * x * n)) * n⁻¹ = x by group] at hconj_u
    simpa [hnu] using hconj_u
  have hw0 : w 0 ∈ DstarH hC := hw_mem 0
  have hπw0 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w 0) ∈
      imageClass hC := ⟨w 0, hw0, rfl⟩
  obtain ⟨b, hb, hnc⟩ := h.facts.noncomm _ hπw0
  obtain ⟨bH, hbH, hbeq⟩ := hb
  have hcommG : Commute (w 0 : G) (bH : G) := hv0_comm (bH : G) ((mem_DstarH_iff hC).mp hbH)
  have hcommπ : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w 0))
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) bH) :=
    (h.commute_iff hw0 hbH).mp (Subtype.ext hcommG)
  exact hnc (hbeq ▸ hcommπ)

end ElevenOneHyp

end CFSG.OddTranspositions.PartThree
