module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3NGeo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.F53
open CFSG.Quasithin.F53Mod CFSG.Quasithin.CosetGeom

namespace F53B3

structure NatFacts (G : Type) [Group G] : Prop where
  card16 : ∀ F L X : Subgroup G, IsNatSec F L X → L.relIndex X = 16
  inv4 : ∀ F L X : Subgroup G, IsNatSec F L X → L ≤ X → ∀ a ∈ F, a ∉ cSecIn F L X →
    a ^ 2 ∈ cSecIn F L X →
    secIdx (Subgroup.zpowers a) L X = 4 ∧ L.relIndex (commSec (Subgroup.zpowers a) L X) = 4
  l2 : ∀ F L X S₀ : Subgroup G, IsNatSec F L X → IsSylowTwoOf S₀ F →
    ∀ U : Subgroup G, L ≤ U → U ≤ X → S₀ ≤ Subgroup.normalizer (U : Set G) → L.relIndex U = 4 →
    cSecIn S₀ L U = S₀ ⊓ (oTwoRes F ⊔ cSecIn F L X) ∧
      (cSecIn F L X).relIndex (S₀ ⊓ (oTwoRes F ⊔ cSecIn F L X)) = 4

variable {G : Type} [Group G] {H M S : Subgroup G}

@[expose] def That (α x : Geo H M) : Subgroup G :=
  (stab α ⊓ stab x) ⊓ (oTwoRes (stab x) ⊔ Qv x)

namespace N37

theorem step2 [Finite G] (hB : B3Facts H M S) (hBl : B3Block H M S) (hN : NatFacts G)
    {x y α : Geo H M} (hx : vtype x = false) (hy : vtype y = false)
    (hxα : (graph (H ⊔ M) H M).Adj x α) (hαy : (graph (H ⊔ M) H M).Adj α y) (hxy : x ≠ y) :
    (∀ A : Subgroup G, A ≤ stab α ⊓ stab x →
      (∀ c ∈ A, ∀ r ∈ Vn x ⊓ Vn y, c * r = r * c) → A ≤ That α x) ∧
      (Qv x).relIndex (That α x) = 4 := by
  have hvα : vtype α = true := vtype_nbr_of_false hxα hx
  have hdist : dist x y = 2 := dist_eq_two_of_nbrs hxα.symm hαy hxy
  have hdist' : dist y x = 2 := by rw [CosetGeom.dist_comm]; exact hdist
  have hnat := hB.nat x hx
  have hcsec := cSecIn_nat_eq_Qv hB hBl hx
  have hXF : Vn x ≤ stab x := Vn_le_stab_self hBl x
  have hFL := stab_le_normalizer_Cv x
  have hRn : stab α ≤ Subgroup.normalizer ((Vn x ⊓ Vn y : Subgroup G) : Set G) :=
    hBl.vn_inf_normal y α x hxy.symm hvα hxα.symm hαy
  obtain ⟨a, haY, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp (hBl.not_vn_le_qv y x hy hdist')
  have haF : a ∈ stab x := hBl.vn_le_stab y x hdist'.le haY
  have ha2 : a ^ 2 ∈ cSecIn (stab x) (Cv x) (Vn x) := by
    rw [hcsec, (hBl.elemAbelian_vn y).2 a haY]
    exact (Qv x).one_mem
  have h4 := hN.inv4 (stab x) (Cv x) (Vn x) hnat (Cv_le_Vn x) a haF (by rw [hcsec]; exact haQ) ha2
  have hR4 : (Cv x).relIndex (Vn x ⊓ Vn y ⊔ Cv x) = 4 :=
    N37.relIndex_sup_eq_four (Cv_le_Vn x) hXF hFL inf_le_left inf_le_right
      (fun u hu w hw => elemAbelian_comm (hBl.elemAbelian_vn y) hu hw) haY haF
      (hBl.comm_vn_vn x y hdist) (hN.card16 _ _ _ hnat) h4
  have hnorm : stab α ⊓ stab x ≤ Subgroup.normalizer ((Vn x ⊓ Vn y ⊔ Cv x : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (inf_le_left.trans hRn) (inf_le_right.trans hFL)
  have hl2 := hN.l2 (stab x) (Cv x) (Vn x) (stab α ⊓ stab x) hnat
    (sylow_inf_stab hB.amalgam hxα) (Vn x ⊓ Vn y ⊔ Cv x) le_sup_right
    (sup_le inf_le_left (Cv_le_Vn x)) hnorm hR4
  rw [hcsec] at hl2
  refine ⟨fun A hA hAc => ?_, hl2.2⟩
  have hRL : Vn x ⊓ Vn y ≤ Subgroup.normalizer (Cv x : Set G) :=
    (inf_le_left.trans hXF).trans hFL
  have hAc' : A ≤ cSecIn (stab α ⊓ stab x) (Cv x) (Vn x ⊓ Vn y ⊔ Cv x) :=
    N37.le_cSecIn_sup hA inf_le_right hFL hRL fun r hr c hc => by
      rw [hAc c hc r hr]
      simp
  rw [hl2.1] at hAc'
  exact hAc'

end N37

end F53B3

end CFSG.Quasithin
