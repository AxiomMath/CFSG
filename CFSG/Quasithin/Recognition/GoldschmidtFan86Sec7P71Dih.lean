module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Idx
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Ind
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7Stmt

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem closure_pair_equiv (g a b : G) :
    Nonempty (↥(Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹} : Set G)) ≃*
      ↥(Subgroup.closure ({a, b} : Set G))) := by
  have h : Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹} : Set G) =
      (Subgroup.closure ({a, b} : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]
    simp [MulAut.conj_apply]
  exact ⟨(MulEquiv.subgroupCongr h).trans
    (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm⟩

theorem valence_eight (F : FanTree Γ G) (A : Arc Γ 8) (h0 : Fan86.valence Γ (A.vert 0) = 5) :
    Fan86.valence Γ (A.vert 4) = 5 ∧ Fan86.valence Γ (A.vert 8) = 5 :=
  ⟨valence_four_of_zero F A h0, valence_of_dist_even F h0 (by
    rw [Arc.dist_eq F.isTree A 8 le_rfl])⟩

theorem stab_eq_inf_centralizer (F : FanTree Γ G) (L : ZLab Γ G) (h65 : Fan65 F)
    (hb : ∀ l, Fan86.valence Γ l = 5 → L.z l ∈ ballStab Γ G 4 l) (P : Arc Γ 8)
    (h0 : Fan86.valence Γ (P.vert 0) = 5) {x : G}
    (hx : x ∈ Subgroup.closure ({L.z (P.vert 0), L.z (P.vert 8)} : Set G)) (hxo : orderOf x = 5) :
    nbrStab Γ G (P.vert 4) ⊓ Subgroup.centralizer ({x} : Set G) = P.stab G := by
  obtain ⟨h4, h8⟩ := valence_eight F P h0
  have f0 : L.z (P.vert 0) • P.vert 4 = P.vert 4 := by
    refine mem_ballStab.1 (hb _ h0) _ ?_
    rw [Arc.dist_eq F.isTree P 4 (by norm_num)]
  have f8 : L.z (P.vert 8) • P.vert 4 = P.vert 4 := by
    refine mem_ballStab.1 (hb _ h8) _ ?_
    rw [SimpleGraph.dist_comm, Arc.dist_vert F.isTree P (by norm_num) le_rfl]
  have hxs : x ∈ MulAction.stabilizer G (P.vert 4) := by
    have hle : Subgroup.closure ({L.z (P.vert 0), L.z (P.vert 8)} : Set G) ≤
        MulAction.stabilizer G (P.vert 4) := by
      rw [Subgroup.closure_le]
      rintro y (hy | hy)
      · rw [hy]
        exact MulAction.mem_stabilizer_iff.2 f0
      · rw [hy]
        exact MulAction.mem_stabilizer_iff.2 f8
    exact hle hx
  have hK := h65.1 _ h4 x hxs hxo
  have hSC : P.stab G ≤ Subgroup.centralizer ({x} : Set G) := by
    intro g hg
    rw [Arc.mem_stab] at hg
    have g0 := hg 0 (by norm_num)
    have g8 := hg 8 (by norm_num)
    have cs : g * L.z (P.vert 0) = L.z (P.vert 0) * g := by
      have := L.equivariant g (P.vert 0) h0
      rw [g0] at this
      exact (eq_mul_inv_iff_mul_eq.1 this).symm
    have ct : g * L.z (P.vert 8) = L.z (P.vert 8) * g := by
      have := L.equivariant g (P.vert 8) h8
      rw [g8] at this
      exact (eq_mul_inv_iff_mul_eq.1 this).symm
    have hsub : Subgroup.closure ({L.z (P.vert 0), L.z (P.vert 8)} : Set G) ≤
        Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.closure_le]
      rintro y (hy | hy)
      · rw [hy]
        refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        rw [Set.mem_singleton_iff.1 hh]
        exact cs
      · rw [hy]
        refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        rw [Set.mem_singleton_iff.1 hh]
        exact ct
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh]
    exact (Subgroup.mem_centralizer_iff.1 (hsub hx) g rfl).symm
  have hSK : P.stab G ≤ nbrStab Γ G (P.vert 4) := by
    intro g hg
    rw [Arc.mem_stab] at hg
    refine mem_nbrStab.2 fun w hw => ?_
    exact F.frobenius_two (P.vert 4) (P.vert 3) (P.vert 5) (P.adj 3 (by norm_num)).symm
      (P.adj 4 (by norm_num)) (P.nb 3 (by norm_num)) g
      (MulAction.mem_stabilizer_iff.2 (hg 4 (by norm_num))) (hg 3 (by norm_num))
      (hg 5 (by norm_num)) w hw
  have hle : P.stab G ≤ Subgroup.centralizer ({x} : Set G) ⊓ nbrStab Γ G (P.vert 4) :=
    le_inf hSC hSK
  have hfinK : Finite (nbrStab Γ G (P.vert 4)) := finite_nbrStab F _
  have hfin2 : Finite ↥(Subgroup.centralizer ({x} : Set G) ⊓ nbrStab Γ G (P.vert 4)) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_right : _ ≤ nbrStab Γ G (P.vert 4)))
      (Subgroup.inclusion_injective _)
  have hpos : (P.stab G).relIndex
      (Subgroup.centralizer ({x} : Set G) ⊓ nbrStab Γ G (P.vert 4)) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have h1 := Subgroup.relIndex_mul_relIndex (P.stab G)
    (Subgroup.centralizer ({x} : Set G) ⊓ nbrStab Γ G (P.vert 4)) (nbrStab Γ G (P.vert 4)) hle
    inf_le_right
  rw [Subgroup.inf_relIndex_right, hK] at h1
  have h2 := stab_relIndex_le F P h4
  have h3 : (P.stab G).relIndex
      (Subgroup.centralizer ({x} : Set G) ⊓ nbrStab Γ G (P.vert 4)) = 1 := by
    have : (P.stab G).relIndex
        (Subgroup.centralizer ({x} : Set G) ⊓ nbrStab Γ G (P.vert 4)) * 2 ^ 8 ≤ 2 ^ 8 := by
      rw [h1]
      exact h2
    have h5 : 0 < (P.stab G).relIndex
        (Subgroup.centralizer ({x} : Set G) ⊓ nbrStab Γ G (P.vert 4)) := Nat.pos_of_ne_zero hpos
    omega
  have h6 := Subgroup.relIndex_eq_one.1 h3
  refine le_antisymm (fun y hy => h6 ⟨hy.2, hy.1⟩) (fun y hy => ⟨hSK hy, hSC hy⟩)

theorem fan71a_of (F : FanTree Γ G) (L : ZLab Γ G) (h65 : Fan65 F)
    (hb : ∀ l, Fan86.valence Γ l = 5 → L.z l ∈ ballStab Γ G 4 l) (hA : ArcTrans Γ G)
    (hD : ∃ A : Arc Γ 8, Fan86.valence Γ (A.vert 0) = 5 ∧
      Nonempty (↥(Subgroup.closure ({L.z (A.vert 0), L.z (A.vert 8)} : Set G)) ≃*
        DihedralGroup 5)) : Fan71a F L := by
  intro P h0
  refine ⟨?_, fun x hx hxo => stab_eq_inf_centralizer F L h65 hb P h0 hx hxo⟩
  obtain ⟨A, hA0, ⟨e⟩⟩ := hD
  obtain ⟨g, hg⟩ := hA A P hA0 h0
  obtain ⟨-, hA8⟩ := valence_eight F A hA0
  have e0 : L.z (P.vert 0) = g * L.z (A.vert 0) * g⁻¹ := by
    rw [← hg 0 (Nat.zero_le _)]
    exact L.equivariant g _ hA0
  have e8 : L.z (P.vert 8) = g * L.z (A.vert 8) * g⁻¹ := by
    rw [← hg 8 le_rfl]
    exact L.equivariant g _ hA8
  rw [e0, e8]
  obtain ⟨e'⟩ := closure_pair_equiv g (L.z (A.vert 0)) (L.z (A.vert 8))
  exact ⟨e'.trans e⟩

end P71

end CFSG.Quasithin.Fan86
