module

public import CFSG.LocalAnalysis.StandardType.PhanELocalFlag
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3Crit
public import CFSG.ClassicalInvolution.Phan.Geometry.Collinear

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable {K : Type} [Field K]

@[expose] def HasCh (A : Set (FlagK K 4)) (p L H : Submodule K (Fin 4 → K)) : Prop :=
  ∃ x ∈ A, x.E 1 = p ∧ x.E 2 = L ∧ x.E 3 = H

@[expose] def PtAdj (A : Set (FlagK K 4)) (p r : Submodule K (Fin 4 → K)) : Prop :=
  p ≠ r ∧ ∃ L H, HasCh A p L H ∧ HasCh A r L H

@[expose] def PlanarPts (A : Set (FlagK K 4)) (x y z : Submodule K (Fin 4 → K)) : Prop :=
  ∃ H L₁ L₂ L₃, HasCh A x L₁ H ∧ HasCh A y L₁ H ∧ HasCh A y L₂ H ∧ HasCh A z L₂ H ∧
    HasCh A z L₃ H ∧ HasCh A x L₃ H

@[expose] def FibreConn (A : Set (FlagK K 4)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x.E 1 = y.E 1 →
    Relation.ReflTransGen (fun u v : FlagK K 4 =>
      u ∈ A ∧ v ∈ A ∧ u.E 1 = v.E 1 ∧ (u.E 3 = v.E 3 ∨ u.E 2 = v.E 2)) x y

@[expose] def CommonNbr (A : Set (FlagK K 4)) : Prop :=
  ∀ s : Finset (Submodule K (Fin 4 → K)), s.Nonempty → s.card ≤ 4 →
    (∀ p ∈ s, ∃ x ∈ A, x.E 1 = p) → ∃ t, ∀ p ∈ s, PtAdj A p t

@[expose] def CommonNbrW (A : Set (FlagK K 4)) : Prop :=
  (∀ u v : Submodule K (Fin 4 → K), (∃ x ∈ A, x.E 1 = u) → (∃ x ∈ A, x.E 1 = v) →
    ∃ t, PtAdj A u t ∧ PtAdj A v t) ∧
  (∀ a b c d : Submodule K (Fin 4 → K), PtAdj A a b → PtAdj A b c → PtAdj A c d → PtAdj A d a →
    ∃ t, PtAdj A a t ∧ PtAdj A b t ∧ PtAdj A c t ∧ PtAdj A d t) ∧
  (∀ u c d : Submodule K (Fin 4 → K), (∃ x ∈ A, x.E 1 = u) → PtAdj A c d →
    ∃ t, PtAdj A u t ∧ PtAdj A c t ∧ PtAdj A d t)

@[expose] def ConeTri (A : Set (FlagK K 4)) : Prop :=
  ∀ x y z, PtAdj A x y → PtAdj A y z → PtAdj A z x →
    ∃ t, PtAdj A x t ∧ PtAdj A y t ∧ PtAdj A z t ∧ PlanarPts A x y t ∧ PlanarPts A y z t ∧
      PlanarPts A z x t

@[expose] def CommonNbrD (A : Set (FlagK K 4)) : Prop :=
  (∀ u v : Submodule K (Fin 4 → K), (∃ x ∈ A, x.E 1 = u) → (∃ x ∈ A, x.E 1 = v) →
    ∃ t, PtAdj A u t ∧ PtAdj A v t) ∧
  (∀ a b c d : Submodule K (Fin 4 → K), PtAdj A a b → PtAdj A b c → PtAdj A c d → PtAdj A d a →
    a ≠ c → ¬ PtAdj A a c → b ≠ d → ¬ PtAdj A b d →
    ∃ t, PtAdj A a t ∧ PtAdj A b t ∧ PtAdj A c t ∧ PtAdj A d t) ∧
  (∀ u c d : Submodule K (Fin 4 → K), (∃ x ∈ A, x.E 1 = u) → PtAdj A c d →
    ∃ t, PtAdj A u t ∧ PtAdj A c t ∧ PtAdj A d t)

@[expose] def ConeTriD (A : Set (FlagK K 4)) : Prop :=
  ∀ x y z, PtAdj A x y → PtAdj A y z → PtAdj A z x → PlanarPts A x y z ∨
    ∃ t, PtAdj A x t ∧ PtAdj A y t ∧ PtAdj A z t ∧ PlanarPts A x y t ∧ PlanarPts A y z t ∧
      PlanarPts A z x t

private lemma plh_E_two_eq_sup {x y : FlagK K 4} (h2 : x.E 2 = y.E 2)
    (hne : x.E 1 ≠ y.E 1) : x.E 2 = x.E 1 ⊔ y.E 1 := by
  have hle : x.E 1 ⊔ y.E 1 ≤ x.E 2 :=
    sup_le (FlagK.E_one_le_two x) (by rw [h2]; exact FlagK.E_one_le_two y)
  exact (Submodule.eq_of_le_of_finrank_eq hle
    (by rw [finrank_sup_of_ne_pts (FlagK.finrank_E_one x) (FlagK.finrank_E_one y) hne,
      FlagK.finrank_E_two])).symm

private lemma plh_gallery_of_reflTransGen {A : Set (FlagK K 4)} {u v : FlagK K 4}
    (hu : u ∈ A)
    (h : Relation.ReflTransGen (fun a b : FlagK K 4 =>
      a ∈ A ∧ b ∈ A ∧ a.E 1 = b.E 1 ∧ (a.E 3 = b.E 3 ∨ a.E 2 = b.E 2)) u v) :
    ∀ (hv : v ∈ A),
      ∃ τ : List (Fin 3 × ↥A),
        IsJGallery ((flagSys K 3).restrict A) ({1, 2} : Set (Fin 3)) ⟨u, hu⟩ τ ∧
          galleryEnd ⟨u, hu⟩ τ = ⟨v, hv⟩ := by
  induction h with
  | refl =>
    intro hv
    exact ⟨[], IsJGallery.nil, Subtype.ext rfl⟩
  | tail hab hbc ih =>
    rename_i b c
    intro hv
    obtain ⟨hbA, _, h1eq, h23⟩ := hbc
    obtain ⟨τ, hτ, hend⟩ := ih hbA
    rcases h23 with hplane | hline
    · have hadj : ((flagSys K 3).restrict A).adj 1 (galleryEnd ⟨u, hu⟩ τ) ⟨c, hv⟩ :=
        (flagSys_adj_one _ c).mpr
          ⟨by rw [hend]; exact h1eq, by rw [hend]; exact hplane⟩
      have htail : IsJGallery ((flagSys K 3).restrict A) ({1, 2} : Set (Fin 3))
          (galleryEnd ⟨u, hu⟩ τ) [(1, ⟨c, hv⟩)] :=
        IsJGallery.cons (by simp) hadj IsJGallery.nil
      exact ⟨τ ++ [(1, ⟨c, hv⟩)], hτ.append htail, by rw [galleryEnd_append]; simp⟩
    · have hadj : ((flagSys K 3).restrict A).adj 2 (galleryEnd ⟨u, hu⟩ τ) ⟨c, hv⟩ :=
        (flagSys_adj_two _ c).mpr
          ⟨by rw [hend]; exact h1eq, by rw [hend]; exact hline⟩
      have htail : IsJGallery ((flagSys K 3).restrict A) ({1, 2} : Set (Fin 3))
          (galleryEnd ⟨u, hu⟩ τ) [(2, ⟨c, hv⟩)] :=
        IsJGallery.cons (by simp) hadj IsJGallery.nil
      exact ⟨τ ++ [(2, ⟨c, hv⟩)], hτ.append htail, by rw [galleryEnd_append]; simp⟩

theorem flagSystem_simplyTwoConnected_of_criterion_diag (A : Set (FlagK K 4)) (h1 : FibreConn A)
    (h2 : CommonNbrD A) (h3 : ConeTriD A) :
    ((flagSys K 3).restrict A).Connected ∧ ((flagSys K 3).restrict A).SimplyTwoConnected := by
  classical
  let X : ChamberSystem (Fin 3) ↥A := (flagSys K 3).restrict A
  let V := {p : Submodule K (Fin 4 → K) // ∃ x ∈ A, x.E 1 = p}
  let P : ↥A → V := fun x => ⟨x.1.E 1, x.1, x.2, rfl⟩
  have hI : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by
    intro i
    fin_cases i <;> simp
  have hadj0 : ∀ e f : ↥A, X.adj 0 e f ↔ e.1.E 2 = f.1.E 2 ∧ e.1.E 3 = f.1.E 3 :=
    fun e f => flagSys_adj_zero e.1 f.1
  have hadj1 : ∀ e f : ↥A, X.adj 1 e f ↔ e.1.E 1 = f.1.E 1 ∧ e.1.E 3 = f.1.E 3 :=
    fun e f => flagSys_adj_one e.1 f.1
  have hadj2 : ∀ e f : ↥A, X.adj 2 e f ↔ e.1.E 1 = f.1.E 1 ∧ e.1.E 2 = f.1.E 2 :=
    fun e f => flagSys_adj_two e.1 f.1
  have hP : Function.Surjective P := by
    rintro ⟨p, hp⟩
    obtain ⟨x, hx, hpx⟩ := hp
    exact ⟨⟨x, hx⟩, Subtype.ext hpx⟩
  have hPb : ∀ {e f : ↥A}, X.adj 1 e f → P e = P f := by
    intro e f hef
    exact Subtype.ext ((hadj1 e f).mp hef).1
  have hPc : ∀ {e f : ↥A}, X.adj 2 e f → P e = P f := by
    intro e f hef
    exact Subtype.ext ((hadj2 e f).mp hef).1
  have hinj : ∀ {e f : ↥A}, X.adj 0 e f → P e = P f → e = f := by
    intro e f hef heqf
    obtain ⟨h2, h3⟩ := (hadj0 e f).mp hef
    have h1 : e.1.E 1 = f.1.E 1 := congrArg Subtype.val heqf
    exact Subtype.ext (FlagK.ext4 h1 h2 h3)
  have hfib : ∀ e f : ↥A, P e = P f →
      ∃ τ : List (Fin 3 × ↥A), IsJGallery X {1, 2} e τ ∧ galleryEnd e τ = f := by
    intro e f hef
    have h1eq : e.1.E 1 = f.1.E 1 := congrArg Subtype.val hef
    obtain ⟨τ, hτ, hend⟩ :=
      plh_gallery_of_reflTransGen e.2 (h1 e.1 e.2 f.1 f.2 h1eq) f.2
    exact ⟨τ, hτ, hend⟩
  have plh_adj_iff : ∀ p r : V, (pointGraph X 0 P).Adj p r ↔ PtAdj A p.1 r.1 := by
    intro p r
    constructor
    · rintro ⟨hpne, e, f, hef, hpe, hpf⟩
      obtain ⟨hef2, hef3⟩ := (hadj0 e f).mp hef
      refine ⟨?_, e.1.E 2, e.1.E 3, ⟨e.1, e.2, congrArg Subtype.val hpe, rfl, rfl⟩,
        ⟨f.1, f.2, congrArg Subtype.val hpf, hef2.symm, hef3.symm⟩⟩
      intro h
      exact hpne (Subtype.ext h)
    · rintro ⟨hpne, L, H, hpH, hrH⟩
      obtain ⟨x, hx, hx1, hx2, hx3⟩ := hpH
      obtain ⟨y, hy, hy1, hy2, hy3⟩ := hrH
      refine ⟨?_, ⟨x, hx⟩, ⟨y, hy⟩, ?_, Subtype.ext hx1, Subtype.ext hy1⟩
      · intro h
        exact hpne (congrArg Subtype.val h)
      · show (flagSys K 3).adj 0 x y
        exact (flagSys_adj_zero x y).mpr ⟨hx2.trans hy2.symm, hx3.trans hy3.symm⟩
  have plh_planar : ∀ x y z : V, PlanarPts A x.1 y.1 z.1 → PlanarTriple X 0 1 P x y z := by
    intro x y z h
    obtain ⟨H, L₁, L₂, L₃, hx1, hy1, hy2, hz2, hz3, hx3⟩ := h
    obtain ⟨ex, hex, hex1, hex2, hex3⟩ := hx1
    obtain ⟨fy, hfy, hfy1, hfy2, hfy3⟩ := hy1
    obtain ⟨ey, hey, hey1, hey2, hey3⟩ := hy2
    obtain ⟨fz, hfz, hfz1, hfz2, hfz3⟩ := hz2
    obtain ⟨ez, hez, hez1, hez2, hez3⟩ := hz3
    obtain ⟨fx, hfx, hfx1, hfx2, hfx3⟩ := hx3
    refine ⟨⟨ex, hex⟩, ⟨fy, hfy⟩, ⟨ey, hey⟩, ⟨fz, hfz⟩, ⟨ez, hez⟩, ⟨fx, hfx⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (flagSys K 3).adj 0 ex fy
      exact (flagSys_adj_zero ex fy).mpr ⟨hex2.trans hfy2.symm, hex3.trans hfy3.symm⟩
    · show (flagSys K 3).adj 1 fy ey
      exact (flagSys_adj_one fy ey).mpr ⟨hfy1.trans hey1.symm, hfy3.trans hey3.symm⟩
    · show (flagSys K 3).adj 0 ey fz
      exact (flagSys_adj_zero ey fz).mpr ⟨hey2.trans hfz2.symm, hey3.trans hfz3.symm⟩
    · show (flagSys K 3).adj 1 fz ez
      exact (flagSys_adj_one fz ez).mpr ⟨hfz1.trans hez1.symm, hfz3.trans hez3.symm⟩
    · show (flagSys K 3).adj 0 ez fx
      exact (flagSys_adj_zero ez fx).mpr ⟨hez2.trans hfx2.symm, hez3.trans hfx3.symm⟩
    · show (flagSys K 3).adj 1 fx ex
      exact (flagSys_adj_one fx ex).mpr ⟨hfx1.trans hex1.symm, hfx3.trans hex3.symm⟩
    · exact Subtype.ext hex1
    · exact Subtype.ext hfy1
    · exact Subtype.ext hfz1
    · exact Subtype.ext hfx1
  have hedge : ∀ {e e' f f' : ↥A}, X.adj 0 e f → X.adj 0 e' f' → P e = P e' →
      P f = P f' → P e ≠ P f →
      ∃ τ τ' : List (Fin 3 × ↥A), IsJGallery X {1, 2} e τ ∧ galleryEnd e τ = e' ∧
        IsJGallery X {1, 2} f τ' ∧ galleryEnd f τ' = f' ∧
        X.TwoHomotopic e (τ ++ [(0, f')]) ((0, f) :: τ') := by
    intro e e' f f' hef he'f' hpe hpf hpne
    obtain ⟨hef2, _⟩ := (hadj0 e f).mp hef
    obtain ⟨he'f'2, _⟩ := (hadj0 e' f').mp he'f'
    have hpe1 : e.1.E 1 = e'.1.E 1 := congrArg Subtype.val hpe
    have hpf1 : f.1.E 1 = f'.1.E 1 := congrArg Subtype.val hpf
    have hpt : e.1.E 1 ≠ f.1.E 1 := fun h => hpne (Subtype.ext h)
    have hp't' : e'.1.E 1 ≠ f'.1.E 1 := fun h => hpt (hpe1.trans (h.trans hpf1.symm))
    have hline1 : e.1.E 2 = e.1.E 1 ⊔ f.1.E 1 := plh_E_two_eq_sup hef2 hpt
    have hline2 : e'.1.E 2 = e'.1.E 1 ⊔ f'.1.E 1 := plh_E_two_eq_sup he'f'2 hp't'
    have hE2 : e.1.E 2 = e'.1.E 2 := by rw [hline1, hline2, hpe1, hpf1]
    have hF2 : f.1.E 2 = f'.1.E 2 := by rw [← hef2, hE2, he'f'2]
    have h2ee' : X.adj 2 e e' := (hadj2 e e').mpr ⟨hpe1, hE2⟩
    have h2ff' : X.adj 2 f f' := (hadj2 f f').mpr ⟨hpf1, hF2⟩
    have hτ : IsJGallery X ({1, 2} : Set (Fin 3)) e [(2, e')] :=
      IsJGallery.cons (by simp) h2ee' IsJGallery.nil
    have hτ' : IsJGallery X ({1, 2} : Set (Fin 3)) f [(2, f')] :=
      IsJGallery.cons (by simp) h2ff' IsJGallery.nil
    have hη : X.IsGallery e [(2, e'), (0, f')] := ⟨h2ee', he'f', trivial⟩
    have hη' : X.IsGallery e [(0, f), (2, f')] := ⟨hef, h2ff', trivial⟩
    have hηJ : ∀ i ∈ galleryType [(2, e'), (0, f')], i ∈ ({0, 2} : Set (Fin 3)) := by
      intro i hi
      have hi' : i = 2 ∨ i = 0 := by simpa using hi
      rcases hi' with rfl | rfl <;> simp
    have hη'J : ∀ i ∈ galleryType [(0, f), (2, f')], i ∈ ({0, 2} : Set (Fin 3)) := by
      intro i hi
      have hi' : i = 0 ∨ i = 2 := by simpa using hi
      rcases hi' with rfl | rfl <;> simp
    have hJ : ({0, 2} : Set (Fin 3)).encard ≤ 2 := by
      rw [Set.encard_pair (by decide)]
    have hmove : X.ElemMove e ([(2, e')] ++ [(0, f')]) ([(0, f)] ++ [(2, f')]) :=
      ElemMove.mk (X := X) (x := e) [] [(2, e'), (0, f')] [(0, f), (2, f')] []
        ({0, 2} : Set (Fin 3)) hJ hη hη' hηJ hη'J (by rfl)
    exact ⟨[(2, e')], [(2, f')], hτ, by simp, hτ', by simp, TwoHomotopic.of_elemMove hmove⟩
  have hptV : ∀ {t : Submodule K (Fin 4 → K)} {p : Submodule K (Fin 4 → K)}, PtAdj A p t →
      ∃ w ∈ A, w.E 1 = t := by
    intro t p hpt
    obtain ⟨_, L, H, _, htH⟩ := hpt
    obtain ⟨w, hw, hw1, _, _⟩ := htH
    exact ⟨w, hw, hw1⟩
  have hcn2 : ∀ u v : V, ∃ t : V, (pointGraph X 0 P).Adj u t ∧ (pointGraph X 0 P).Adj v t := by
    intro u v
    obtain ⟨t, hut, hvt⟩ := h2.1 u.1 v.1 u.2 v.2
    obtain ⟨w, hw, hw1⟩ := hptV hut
    exact ⟨⟨t, ⟨w, hw, hw1⟩⟩, (plh_adj_iff u ⟨t, ⟨w, hw, hw1⟩⟩).mpr hut,
      (plh_adj_iff v ⟨t, ⟨w, hw, hw1⟩⟩).mpr hvt⟩
  have hcn4 : ∀ u v w z : V, (pointGraph X 0 P).Adj u v → (pointGraph X 0 P).Adj v w →
      (pointGraph X 0 P).Adj w z → (pointGraph X 0 P).Adj z u → u ≠ w →
      ¬ (pointGraph X 0 P).Adj u w → v ≠ z → ¬ (pointGraph X 0 P).Adj v z →
      ∃ t : V, (pointGraph X 0 P).Adj u t ∧ (pointGraph X 0 P).Adj v t ∧
        (pointGraph X 0 P).Adj w t ∧ (pointGraph X 0 P).Adj z t := by
    intro u v w z huv hvw hwz hzu huw hnuw hvz hnvz
    obtain ⟨t, hut, hvt, hwt, hzt⟩ := h2.2.1 u.1 v.1 w.1 z.1 ((plh_adj_iff u v).mp huv)
      ((plh_adj_iff v w).mp hvw) ((plh_adj_iff w z).mp hwz) ((plh_adj_iff z u).mp hzu)
      (fun h => huw (Subtype.ext h)) (fun h => hnuw ((plh_adj_iff u w).mpr h))
      (fun h => hvz (Subtype.ext h)) (fun h => hnvz ((plh_adj_iff v z).mpr h))
    obtain ⟨y, hy, hy1⟩ := hptV hut
    exact ⟨⟨t, ⟨y, hy, hy1⟩⟩, (plh_adj_iff u ⟨t, ⟨y, hy, hy1⟩⟩).mpr hut,
      (plh_adj_iff v ⟨t, ⟨y, hy, hy1⟩⟩).mpr hvt, (plh_adj_iff w ⟨t, ⟨y, hy, hy1⟩⟩).mpr hwt,
      (plh_adj_iff z ⟨t, ⟨y, hy, hy1⟩⟩).mpr hzt⟩
  have hcn3 : ∀ u c d : V, (pointGraph X 0 P).Adj c d →
      ∃ t : V, (pointGraph X 0 P).Adj t c ∧ (pointGraph X 0 P).Adj t d ∧
        (pointGraph X 0 P).Adj u t := by
    intro u c d hcd
    obtain ⟨t, hut, hct, hdt⟩ := h2.2.2 u.1 c.1 d.1 u.2 ((plh_adj_iff c d).mp hcd)
    obtain ⟨y, hy, hy1⟩ := hptV hut
    exact ⟨⟨t, ⟨y, hy, hy1⟩⟩, ((plh_adj_iff c ⟨t, ⟨y, hy, hy1⟩⟩).mpr hct).symm,
      ((plh_adj_iff d ⟨t, ⟨y, hy, hy1⟩⟩).mpr hdt).symm,
      (plh_adj_iff u ⟨t, ⟨y, hy, hy1⟩⟩).mpr hut⟩
  have hcone : ∀ {x y z : V}, (pointGraph X 0 P).Adj x y → (pointGraph X 0 P).Adj y z →
      (pointGraph X 0 P).Adj z x → PlanarTriple X 0 1 P x y z ∨
      ∃ t : V, (pointGraph X 0 P).Adj x t ∧ (pointGraph X 0 P).Adj y t ∧
        (pointGraph X 0 P).Adj z t ∧ PlanarTriple X 0 1 P x y t ∧
        PlanarTriple X 0 1 P y z t ∧ PlanarTriple X 0 1 P z x t := by
    intro x y z hxy hyz hzx
    rcases h3 x.1 y.1 z.1 ((plh_adj_iff x y).mp hxy) ((plh_adj_iff y z).mp hyz)
        ((plh_adj_iff z x).mp hzx) with hpl | ⟨t, hxt, hyt, hzt, hp1, hp2, hp3⟩
    · exact Or.inl (plh_planar x y z hpl)
    have hxt' := hxt
    obtain ⟨hxne, L, H, hpx, htH⟩ := hxt'
    obtain ⟨w, hw, hw1, hw2, hw3⟩ := htH
    exact Or.inr ⟨⟨t, ⟨w, hw, hw1⟩⟩, (plh_adj_iff x ⟨t, ⟨w, hw, hw1⟩⟩).mpr hxt,
      (plh_adj_iff y ⟨t, ⟨w, hw, hw1⟩⟩).mpr hyt,
      (plh_adj_iff z ⟨t, ⟨w, hw, hw1⟩⟩).mpr hzt,
      plh_planar x y ⟨t, ⟨w, hw, hw1⟩⟩ hp1,
      plh_planar y z ⟨t, ⟨w, hw, hw1⟩⟩ hp2,
      plh_planar z x ⟨t, ⟨w, hw, hw1⟩⟩ hp3⟩
  show X.Connected ∧ X.SimplyTwoConnected
  exact simplyTwoConnected_of_pointGraph_diag X 0 1 2 hI P hP hPb hPc hinj hfib hedge hcn2 hcn4 hcn3
    hcone

theorem commonNbrD_of_commonNbrW {A : Set (FlagK K 4)} (h : CommonNbrW A) : CommonNbrD A :=
  ⟨h.1, fun a b c d hab hbc hcd hda _ _ _ _ => h.2.1 a b c d hab hbc hcd hda, h.2.2⟩

theorem coneTriD_of_coneTri {A : Set (FlagK K 4)} (h : ConeTri A) : ConeTriD A :=
  fun x y z hxy hyz hzx => Or.inr (h x y z hxy hyz hzx)

theorem flagSystem_simplyTwoConnected_of_criterion_weak (A : Set (FlagK K 4)) (h1 : FibreConn A)
    (h2 : CommonNbrW A) (h3 : ConeTri A) :
    ((flagSys K 3).restrict A).Connected ∧ ((flagSys K 3).restrict A).SimplyTwoConnected :=
  flagSystem_simplyTwoConnected_of_criterion_diag A h1 (commonNbrD_of_commonNbrW h2)
    (coneTriD_of_coneTri h3)

theorem commonNbrW_of_commonNbr {A : Set (FlagK K 4)} (h : CommonNbr A) : CommonNbrW A := by
  classical
  have hL : ∀ {p r : Submodule K (Fin 4 → K)}, PtAdj A p r → ∃ x ∈ A, x.E 1 = p := by
    intro p r hpr
    obtain ⟨_, L, H, ⟨x, hx, hx1, _, _⟩, _⟩ := hpr
    exact ⟨x, hx, hx1⟩
  have hR : ∀ {p r : Submodule K (Fin 4 → K)}, PtAdj A p r → ∃ x ∈ A, x.E 1 = r := by
    intro p r hpr
    obtain ⟨_, L, H, _, ⟨x, hx, hx1, _, _⟩⟩ := hpr
    exact ⟨x, hx, hx1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu hv
    obtain ⟨t, ht⟩ := h {u, v} ⟨u, by simp⟩
      ((Finset.card_le_two (a := u) (b := v)).trans (by norm_num))
      (by
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact hu
        · rw [Finset.mem_singleton.mp hp]; exact hv)
    exact ⟨t, ht u (by simp), ht v (by simp)⟩
  · intro a b c d hab hbc hcd hda
    obtain ⟨t, ht⟩ := h {a, b, c, d} ⟨a, by simp⟩
      (Finset.card_le_four (a := a) (b := b) (c := c) (d := d))
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact hL hab
        · exact hL hbc
        · exact hL hcd
        · exact hL hda)
    exact ⟨t, ht a (by simp), ht b (by simp), ht c (by simp), ht d (by simp)⟩
  · intro u c d hu hcd
    obtain ⟨t, ht⟩ := h {u, c, d} ⟨u, by simp⟩
      ((Finset.card_le_three (a := u) (b := c) (c := d)).trans (by norm_num))
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl
        · exact hu
        · exact hL hcd
        · exact hR hcd)
    exact ⟨t, ht u (by simp), ht c (by simp), ht d (by simp)⟩

theorem flagSystem_simplyTwoConnected_of_criterion (A : Set (FlagK K 4)) (h1 : FibreConn A)
    (h2 : CommonNbr A) (h3 : ConeTri A) :
    ((flagSys K 3).restrict A).Connected ∧ ((flagSys K 3).restrict A).SimplyTwoConnected :=
  flagSystem_simplyTwoConnected_of_criterion_weak A h1 (commonNbrW_of_commonNbr h2) h3

end CFSG.ClassicalInvolution.Phan.PhanE

end
