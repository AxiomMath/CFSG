module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeKeyLemma
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.FourInputN.Orbit
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

omit [Finite G] in
private theorem iSup_map_conj_eq_of_map_conj_eq {T K K' : Subgroup G} {t s : T}
    (h : K.map (MulAut.conj (t : G)).toMonoidHom = K'.map (MulAut.conj (s : G)).toMonoidHom) :
    (⨆ u : T, K'.map (MulAut.conj (u : G)).toMonoidHom) =
      ⨆ u : T, K.map (MulAut.conj (u : G)).toMonoidHom := by
  have hcomp (H : Subgroup G) (a b : G) :
      (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
        H.map (MulAut.conj (b * a)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  set r : T := s⁻¹ * t with hr
  have hrG : (r : G) = ((s⁻¹ : T) : G) * (t : G) := by
    rw [hr, Subgroup.coe_mul]
  have hK' : K' = K.map (MulAut.conj (r : G)).toMonoidHom := by
    have h2 := congrArg
      (fun H : Subgroup G => H.map (MulAut.conj ((s⁻¹ : T) : G)).toMonoidHom) h
    have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext z
      simp
    have hss : ((s⁻¹ : T) : G) * (s : G) = 1 := by
      rw [Subgroup.coe_inv]
      exact inv_mul_cancel _
    rw [hcomp, hcomp, ← hrG, hss, hone, Subgroup.map_id] at h2
    exact h2.symm
  rw [hK']
  calc (⨆ u : T, (K.map (MulAut.conj (r : G)).toMonoidHom).map
        (MulAut.conj (u : G)).toMonoidHom)
      = ⨆ u : T, K.map (MulAut.conj ((u * r : T) : G)).toMonoidHom :=
        iSup_congr fun u => hcomp K r u
    _ = ⨆ u : T, K.map (MulAut.conj (u : G)).toMonoidHom := by
      refine le_antisymm (iSup_le fun u => le_iSup
        (fun v : T => K.map (MulAut.conj (v : G)).toMonoidHom) (u * r))
        (iSup_le fun v => ?_)
      have hv : (v : G) = ((v * r⁻¹ : T) : G) * (r : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hv, ← Subgroup.coe_mul]
      exact le_iSup
        (fun u : T => K.map (MulAut.conj ((u * r : T) : G)).toMonoidHom) (v * r⁻¹)

theorem commutator_le_centralizer_V_of_mem_calLOf (c : Ctx23L D Ch) (h208 : S20_8 D)
    (h1930 : H1930 D) {L' : Subgroup G} (hL' : L' ∈ calLOf D.T D.M c.N) (hne : L' ≠ c.L) :
    ⁅L', c.L⁆ ≤ centralizer (c.V : Set G) := by
  obtain ⟨K, hK, hLK⟩ := c.hL.1.2.2.2
  obtain ⟨K', hK', hL'K'⟩ := hL'.1.2.2.2
  have hLsub : IsSubnormal c.L c.N := (N_facts c h208 h1930).2.2.1
  have hKN : K ∈ calC c.N :=
    ⟨CFSG.Quasithin.A3.subnormal_trans hK.1 hLsub, hK.2.1, hK.2.2⟩
  have hK'N : K' ∈ calC c.N :=
    ⟨CFSG.Quasithin.A3.subnormal_trans hK'.1 hL'.2, hK'.2.1, hK'.2.2⟩
  have hTN : D.T ≤ c.N := T_le_N c
  have hcalC : ∀ M₀ ∈ calC c.N, ∀ t : D.T,
      M₀.map (MulAut.conj (t : G)).toMonoidHom ∈ calC c.N := fun M₀ hM₀ t => by
    have hNmap : c.N.map (MulAut.conj (t : G)).toMonoidHom = c.N :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hTN t.2))
    exact UC6S846.calC_map c.N (MulAut.conj (t : G)) hNmap hM₀
  have hKt := hcalC K hKN
  have hK't := hcalC K' hK'N
  have hNV : c.N ≤ normalizer (c.V : Set G) :=
    uc22p22v_le_normalizer_conjClosure c.N D.Z
  have hO2 : pCoreOf 2 c.N ≤ centralizer (c.V : Set G) :=
    Subgroup.le_centralizer_iff.mp (V_le_centralizer_pCore c)
  have hne_ts : ∀ (t s : D.T),
      K.map (MulAut.conj (t : G)).toMonoidHom ≠
        K'.map (MulAut.conj (s : G)).toMonoidHom := by
    intro t s heq
    apply hne
    rw [hLK, hL'K']
    exact iSup_map_conj_eq_of_map_conj_eq heq
  have hinner : ∀ s : D.T, ⁅K'.map (MulAut.conj (s : G)).toMonoidHom, c.L⁆ ≤
      centralizer (c.V : Set G) := by
    intro s
    have h1 : ⁅c.L, K'.map (MulAut.conj (s : G)).toMonoidHom⁆ ≤
        centralizer (c.V : Set G) := by
      rw [hLK]
      refine commutator_iSup_le_centralizer
        (A := fun t : D.T => K.map (MulAut.conj (t : G)).toMonoidHom)
        (fun t => ?_) (fun t => ?_)
      · exact (hKt t).1.le.trans hNV
      · refine Subgroup.commutator_le.mpr fun k hk k' hk' => ?_
        exact hO2 (commutator_mem_pCoreOf_of_ne (hKt t) (hK't s) (hne_ts t s) hk hk')
    rwa [Subgroup.commutator_comm] at h1
  rw [hL'K']
  exact commutator_iSup_le_centralizer
    (A := fun s : D.T => K'.map (MulAut.conj (s : G)).toMonoidHom)
    (fun s => (hK't s).1.le.trans hNV) hinner

theorem X23_4_eq_L (c : Ctx23L D Ch) (h208 : S20_8 D) (h1930 : H1930 D)
    (hU : D.U = c.infCentralizer) :
    X23_4 D c.N = c.L := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun L' hL' => ?_
    by_cases hEq : L' = c.L
    · rw [hEq]
    · have hcomm : ⁅c.L, L'⁆ ≤ centralizer (c.V : Set G) := by
        rw [Subgroup.commutator_comm]
        exact commutator_le_centralizer_V_of_mem_calLOf c h208 h1930 hL' hEq
      have hstep : ∀ x ∈ L', ∀ u ∈ c.infCentralizer,
          x * u * x⁻¹ ∈ c.infCentralizer := by
        intro x hx u hu
        have hxN : x ∈ c.N := hL'.2.le hx
        have hxV : x ∈ normalizer (c.V : Set G) :=
          uc22p22v_le_normalizer_conjClosure c.N D.Z hxN
        have hxv : x * u * x⁻¹ ∈ c.V :=
          (Subgroup.mem_normalizer_iff.mp hxV u).mp (Subgroup.mem_inf.mp hu).1
        refine Subgroup.mem_inf.mpr ⟨hxv, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have hd : ⁅q, x⁆ ∈ centralizer (c.V : Set G) :=
          hcomm (Subgroup.commutator_mem_commutator hq.2 hx)
        have hqu : q * u * q⁻¹ = u := by
          have h1 := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2) q hq
          rw [h1]
          group
        have hd' : ⁅q, x⁆ * (x * u * x⁻¹) = (x * u * x⁻¹) * ⁅q, x⁆ :=
          ((Subgroup.mem_centralizer_iff.mp hd) (x * u * x⁻¹) hxv).symm
        have hqv : q * (x * u * x⁻¹) * q⁻¹ = x * u * x⁻¹ := by
          calc q * (x * u * x⁻¹) * q⁻¹
              = (q * x) * u * (q * x)⁻¹ := by group
            _ = (⁅q, x⁆ * x * q) * u * (⁅q, x⁆ * x * q)⁻¹ := by
                rw [show q * x = ⁅q, x⁆ * x * q from by rw [commutatorElement_def]; group]
            _ = ⁅q, x⁆ * (x * (q * u * q⁻¹) * x⁻¹) * ⁅q, x⁆⁻¹ := by group
            _ = ⁅q, x⁆ * (x * u * x⁻¹) * ⁅q, x⁆⁻¹ := by rw [hqu]
            _ = x * u * x⁻¹ := by rw [hd']; group
        calc q * (x * u * x⁻¹) = (q * (x * u * x⁻¹) * q⁻¹) * q := by group
          _ = (x * u * x⁻¹) * q := by rw [hqv]
      have hnorm : L' ≤ normalizer (c.infCentralizer : Set G) := by
        intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro u
        constructor
        · exact hstep x hx u
        · intro hu
          have h := hstep x⁻¹ (L'.inv_mem hx) (x * u * x⁻¹) hu
          have heq : x⁻¹ * (x * u * x⁻¹) * (x⁻¹)⁻¹ = u := by group
          rwa [heq] at h
      have hN : normalizer (c.infCentralizer : Set G) = D.M := by
        rw [← hU, Data.normalizer_U_eq D]
      rw [hN] at hnorm
      exact absurd hnorm (uc22p20i_not_le_M D hL'.1)
  · exact le_iSup₂_of_le c.L ⟨c.hL.1, (N_facts c h208 h1930).2.2.1⟩ le_rfl

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
