module

public import CFSG.Quasithin.Vol2.Ch6StatementsSec2
public import CFSG.Quasithin.Vol2.Ch6NatFacts
public import CFSG.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

theorem stmt6_2_19Sec2_of (h6213 : Stmt6_2_13) (hcase2 : Stmt6_2_19Case2) : Stmt6_2_19Sec2 := by
  intro G _ _ T M L V h
  have hle : ch6ZS T L V ≤
      V ⊓ conjClosure (ch6ZS T L V)
        (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :=
    le_inf inf_le_left (le_conjClosure _ _)
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd hlt (hcase2 G T M L V h)
  · exact h6213 G T M L V h heq

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem Hyp611.commutator_le (h : Hyp611 G T M L V n) : ⁅V, L⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have : l * v⁻¹ * l⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (h.L_le_normalizer hl) v⁻¹).mp (V.inv_mem hv)
  have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [e]
  exact V.mul_mem hv this

theorem Hyp611.sup_le_normalizer_commutator (h : Hyp611 G T M L V n) :
    L ⊔ T ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
  have hTL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (h.T_le.trans h.normal)
  intro x hx
  have hxV := h.sup_le_normalizer hx
  have hxL := hTL hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hmap : (⁅V, L⁆).map (MulAut.conj x).toMonoidHom = ⁅V, L⁆ := by
    rw [Subgroup.map_commutator]
    have hV : V.map (MulAut.conj x).toMonoidHom = V := by
      ext z
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
      · intro hz
        refine ⟨x⁻¹ * z * x, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxV) z).mp hz
        simpa using this
    have hL : L.map (MulAut.conj x).toMonoidHom = L := by
      ext z
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hxL v).mp hv
      · intro hz
        refine ⟨x⁻¹ * z * x, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxL) z).mp hz
        simpa using this
    rw [hV, hL]
  constructor
  · intro hy
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← hmap] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
    have : z = y := by
      have := congrArg (fun w => x⁻¹ * w * x) hzy
      simpa [mul_assoc] using this
    rw [← this]; exact hz

theorem Hyp611.toNat (h : Hyp611 G T M L V n) (hnat : IsNatModCh5 L ⁅V, L⁆ n) :
    Hyp611Nat G T M L ⁅V, L⁆ n where
  toHyp611 :=
    { toHyp5_0_1 := h.toHyp5_0_1
      module := ⟨h.commutator_le.trans h.module.1,
        (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp
          (hnat.isTwoReducedIn le_sup_left (h.commutator_le.trans h.module.1)
            h.sup_le_normalizer_commutator
            (sup_le Subgroup.le_normalizer (h.T_le.trans h.normal))
            (B2F.isElemAbelian_mono h.commutator_le h.isElemAbelian))).2,
        by rw [hnat.commutator_eq]; exact h.module.2.2⟩
      not_a5 := by
        rw [hnat.commutator_eq]
        exact h.not_a5
      nParam_eq_one := h.nParam_eq_one
      noLie := h.noLie }
  comm_eq := hnat.commutator_eq
  natural := hnat

theorem stmt6_2_19_of (h6127 : Stmt6_1_27) (hsec2 : Stmt6_2_19Sec2) : Stmt6_2_19 := by
  intro G _ _ T M L V n h
  obtain ⟨rfl, ⟨hnat, -⟩, hZS, -⟩ := h6127 G T M L V n h
  exact hsec2 G T M L ⁅V, L⁆ ⟨h.toNat hnat, hZS⟩

end CFSG.Quasithin.H13
