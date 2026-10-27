module

public import CFSG.Quasithin.Background.PGroupIrrTrivial
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
private theorem D31.Mp_le_M_aux {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D31 M Mp T L V) : Mp ≤ M := by
  rw [hD.Mp_eq]
  exact conjClosure_le fun s hs l hl =>
    M.mul_mem (M.mul_mem (hD.sylow.1 hs) (le_of_mem_cComp hD.comp hl)) (M.inv_mem (hD.sylow.1 hs))

private theorem D31.eq_bot_of_normal_isPGroup {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D31 M Mp T L V) {Y : Subgroup (MulAut W)} (hYM : Y ≤ M)
    (hYn : M ≤ Subgroup.normalizer (Y : Set (MulAut W))) (hY2 : IsPGroup 2 Y) : Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : T ≤ M := hD.sylow.1
  have hLM : L ≤ M := le_of_mem_cComp hD.comp
  have hMpM : Mp ≤ M := hD.Mp_le_M_aux
  have hYT : Y ≤ T := by
    have hS2 : IsPGroup 2 (T.subgroupOf M) :=
      hD.sylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
    let P : Sylow 2 M := hS2.toSylow hD.sylow.2.2
    have hnormal : (Y.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr hYn
    have hY' : IsPGroup 2 (Y.subgroupOf M) := hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYM).symm
    have hle : Y.subgroupOf M ≤ (P : Subgroup M) := hY'.le_sylow_of_normal P
    intro x hx
    exact hle (show (⟨x, hYM hx⟩ : M) ∈ Y.subgroupOf M from hx)
  have hYO : Y ≤ pCoreOf 2 (Mp ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hYT.trans le_sup_right)
      ((sup_le hMpM hTM).trans hYn) hY2
  have hYV : ∀ y ∈ Y, ∀ v ∈ V, y v ∈ V := fun y hy v hv => hD.o2inv y (hYO hy) v hv
  have hLY : ∀ l ∈ L, ∀ y ∈ Y, y * l = l * y := by
    have hcomp : CFSG.IsComponent (L.subgroupOf M) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLM).symm hD.quasi,
        A3.subnormal_top_iff.mp (subnormal_of_mem_cComp (subgroupOf_mem_cComp hD.comp))⟩
    have hYp' : IsPGroup 2 ↥(Y.subgroupOf M) :=
      hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYM).symm
    have : Group.IsNilpotent ↥(Y.subgroupOf M) := hYp'.isNilpotent
    have hsolv : Group.IsSolvable ↥(Y.subgroupOf M) := inferInstance
    have hsub : (Y.subgroupOf M).IsSubnormal :=
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr hYn).isSubnormal
    have hbot : ⁅L.subgroupOf M, Y.subgroupOf M⁆ = ⊥ :=
      (CFSG.LocalCores.component_solvable_centralizer hsolv hsub).1 _ hcomp
    intro l hl y hy
    have h := Subgroup.commutator_mem_commutator
      (show (⟨l, hLM hl⟩ : M) ∈ L.subgroupOf M from hl)
      (show (⟨y, hYM hy⟩ : M) ∈ Y.subgroupOf M from hy)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact (congrArg Subtype.val h).symm
  have hYMp : ∀ y ∈ Y, ∀ m ∈ Mp, y * m = m * y := by
    have h : Mp ≤ Subgroup.centralizer (Y : Set (MulAut W)) := by
      rw [hD.Mp_eq]
      refine conjClosure_le fun s hs l hl => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : s⁻¹ * y * s ∈ Y := (Subgroup.mem_normalizer_iff''.mp (hYn (hTM hs)) y).mp hy
      have hc := hLY l hl _ hy'
      calc y * (s * l * s⁻¹) = s * ((s⁻¹ * y * s) * l) * s⁻¹ := by group
        _ = s * (l * (s⁻¹ * y * s)) * s⁻¹ := by rw [hc]
        _ = s * l * s⁻¹ * y := by group
    intro y hy m hm
    exact Subgroup.mem_centralizer_iff.mp (h hm) y hy
  have hY1 : ∀ y ∈ Y, ∀ v ∈ V, y v = v :=
    trivial_on_of_isPGroup_commute hD.exp hD.irr hY2 hYV hYMp
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hgen : (⨆ g ∈ M, V.map g.toMonoidHom) ≤ (y : MulAut W).toMonoidHom.eqLocus (MonoidHom.id W) := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨v, hv, rfl⟩
    have hconj : g⁻¹ * y * g ∈ Y := (Subgroup.mem_normalizer_iff''.mp (hYn hg) y).mp hy
    have h1 := hY1 _ hconj v hv
    simp only [MulAut.mul_apply] at h1
    show y (g v) = g v
    calc y (g v) = g (g⁻¹ (y (g v))) := by simp
      _ = g v := by rw [h1]
  ext w
  have hw : w ∈ (⨆ g ∈ M, V.map g.toMonoidHom) := by rw [hD.gen]; trivial
  exact hgen hw

theorem D31.pCoreOf_Mp_eq_bot {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D31 M Mp T L V) : pCoreOf 2 Mp = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hD.eq_bot_of_normal_isPGroup
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 Mp).trans hD.Mp_le_M_aux)
    (hD.Mp_normal.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Mp))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Mp)

theorem D31.pCoreOf_eq_bot {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D31 M Mp T L V) : pCoreOf 2 M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hD.eq_bot_of_normal_isPGroup (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)

end CFSG.Quasithin
