module

public import CFSG.Quasithin.H13.A6S137Hat
public import CFSG.Quasithin.H13.A6S4L0
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] def TransvAt (x : P6) : Prop :=
  InW4 x → act4f (swap 4 5) x * x⁻¹ = 1 ∨ act4f (swap 4 5) x * x⁻¹ = e0123

instance (x : P6) : Decidable (TransvAt x) := by unfold TransvAt; infer_instance

theorem transvAt_all : ∀ x : P6, TransvAt x := by decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem comm_mem_V1_of_rho {u : ↥(Subgroup.normalizer (V : Set G))}
    (hu : S.frame.ρ u = 1 ∨ S.frame.ρ u = swap 4 5) {v : G} (hv : v ∈ V) :
    (u : G) * v * (u : G)⁻¹ * v⁻¹ ∈ fsuV1 T V := by
  have hm : (u : G) * v * (u : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp u.2 v).mp hv
  have hw : (u : G) * v * (u : G)⁻¹ * v⁻¹ ∈ V := V.mul_mem hm (V.inv_mem hv)
  have hψ : ((S.frame.ψ ⟨_, hw⟩ : ↥W4) : P6) =
      act4f (S.frame.ρ u) (S.frame.ψ ⟨v, hv⟩ : P6) * (S.frame.ψ ⟨v, hv⟩ : P6)⁻¹ := by
    have e : (⟨_, hw⟩ : ↥V) = ⟨_, hm⟩ * (⟨v, hv⟩ : ↥V)⁻¹ := rfl
    rw [e, map_mul, map_inv, S.psi_conj u ⟨v, hv⟩]
    rfl
  rw [S.mem_V1_iff]
  have key : ((S.frame.ψ ⟨_, hw⟩ : ↥W4) : P6) = 1 ∨
      ((S.frame.ψ ⟨_, hw⟩ : ↥W4) : P6) = e0123 := by
    rw [hψ]
    rcases hu with h | h
    · left
      rw [h]
      rw [act4f_one _ (S.frame.ψ ⟨v, hv⟩).2]
      exact mul_inv_cancel _
    · rw [h]
      exact transvAt_all _ (S.frame.ψ ⟨v, hv⟩).2
  rcases key with h | h
  · left
    have : (⟨_, hw⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [map_one]; exact Subtype.ext h)
    exact congrArg Subtype.val this
  · right
    have : (⟨_, hw⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ :=
      S.frame.ψ.injective (by rw [S.psi_z]; exact Subtype.ext h)
    exact congrArg Subtype.val this

section Abelian

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem rho_UH {u : G} (hu : u ∈ conjClosure S.V3 H) :
    ∃ huN : u ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨u, huN⟩ = 1 ∨ S.frame.ρ ⟨u, huN⟩ = swap 4 5 := by
  have huT : u ∈ T := S.UH_le_T hNS h1356two h13315 hH hu
  have huN : u ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le huT
  have huC : u ∈ Subgroup.centralizer (S.V3 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val
      (hab.1.is_comm.comm ⟨x, le_conjClosure _ _ hx⟩ ⟨u, hu⟩)
  exact ⟨huN, fixW3_iff _ (S.fixW3_of_centralizer (x := ⟨u, huN⟩) huC)⟩

theorem V_le_QH : V ≤ pCoreOf 2 H := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  rw [hF.le_pCoreOf_iff_le_centralizerMod]
  intro v hv
  refine ⟨hF.V_le_H hv, hF.V_le_normalizer_V₁ hv, fun u hu => ?_⟩
  obtain ⟨huN, hρ⟩ := S.rho_UH hNS h13315 h1356two hH hab hu
  have h := S.comm_mem_V1_of_rho (u := ⟨u, huN⟩) hρ hv
  have e : v * u * v⁻¹ * u⁻¹ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by group
  rw [e]
  exact (fsuV1 T V).inv_mem h

theorem conjSub_le_centralizer_UH {h : G} (hh : h ∈ H) :
    conjSub h V ≤ Subgroup.centralizer (conjClosure S.V3 H : Set G) := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hV := hF.le_pCoreOf_iff_le_centralizer.1 (S.V_le_QH hNS h13315 h1356two hH hab)
  intro w hw
  rw [mem_conjSub] at hw
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : h⁻¹ * u * h⁻¹⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (H.inv_mem hh)) u).mp hu
  have hc := Subgroup.mem_centralizer_iff.mp (hV hw).2 _ hu'
  calc u * w = h * ((h⁻¹ * u * h⁻¹⁻¹) * (h⁻¹ * w * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * w * h) * (h⁻¹ * u * h⁻¹⁻¹)) * h⁻¹ := by rw [hc]
    _ = w * u := by group

theorem conjSub_le_T {h : G} (hh : h ∈ H) : conjSub h V ≤ T := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  exact (hF.conjSub_le_pCoreOf (S.V_le_QH hNS h13315 h1356two hH hab) hh).trans
    (pCoreOf_le_of_sylow S.h13.sylow hF.T_le_H)

theorem rho_conjSub_V {h : G} (hh : h ∈ H) {w : G}
    (hw : w ∈ conjSub h V) :
    ∃ hwN : w ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨w, hwN⟩ = 1 ∨ S.frame.ρ ⟨w, hwN⟩ = swap 4 5 := by
  have hwN : w ∈ Subgroup.normalizer (V : Set G) :=
    S.frame.T_le (S.conjSub_le_T hNS h13315 h1356two hH hab hh hw)
  have hwC : w ∈ Subgroup.centralizer (S.V3 : Set G) :=
    Subgroup.centralizer_le (le_conjClosure S.V3 H)
      (S.conjSub_le_centralizer_UH hNS h13315 h1356two hH hab hh hw)
  exact ⟨hwN, fixW3_iff _ (S.fixW3_of_centralizer (x := ⟨w, hwN⟩) hwC)⟩

theorem conjSub_le_centralizer_V_of_hat (hhat : IsHatA6 L)
    {h : G} (hh : h ∈ H) : conjSub h V ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := S.hypF91 hNS h13315 h1356two hH
  intro w hw
  obtain ⟨hwN, hρ⟩ := S.rho_conjSub_V hNS h13315 h1356two hH hab hh hw
  rcases hρ with h1 | h45
  · exact (S.rho_eq_one_iff ⟨w, hwN⟩).1 h1
  exfalso
  have hwQ : w ∈ pCoreOf 2 H :=
    hF.conjSub_le_pCoreOf (S.V_le_QH hNS h13315 h1356two hH hab) hh hw
  have hwT : w ∈ T := S.conjSub_le_T hNS h13315 h1356two hH hab hh hw
  obtain ⟨c, hc0, hc3, hcO, -⟩ := exists_l0_c hhat.2.1
  have hcZ : c ∈ o2Z L := oTwoRes_le _ hc0
  have hinv := S.conj_inv_mod_pCoreOf hhat (t := ⟨w, hwN⟩) (S.T_le_NL hwT) h45 hcZ
  have hcH : c ∈ H := hF.L₁T_le_H (Subgroup.mem_sup_left (S.l0_le_L1 hc0))
  have hwl0 : w ∈ Subgroup.normalizer (l0 L : Set G) := S.normalizer_le_l0 hwN
  have hd0 : w * c * w⁻¹ * c⁻¹ ∈ l0 L :=
    (l0 L).mul_mem ((Subgroup.mem_normalizer_iff.mp hwl0 c).mp hc0) ((l0 L).inv_mem hc0)
  have hdQ : w * c * w⁻¹ * c⁻¹ ∈ pCoreOf 2 H := by
    have h1 : c * w⁻¹ * c⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hcH) _).mp
        ((pCoreOf 2 H).inv_mem hwQ)
    have e : w * c * w⁻¹ * c⁻¹ = w * (c * w⁻¹ * c⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem hwQ h1
  have hdO : w * c * w⁻¹ * c⁻¹ ∈ pCoreOf 2 L := by
    refine pCoreOf_l0_le (le_pCoreOf_of_le_normalizer 2
      (inf_le_left : l0 L ⊓ pCoreOf 2 H ≤ l0 L)
      (F7.le_normalizer_inf Subgroup.le_normalizer
        ((S.l0_le_L1.trans (le_sup_left.trans hF.L₁T_le_H)).trans
          (le_normalizer_pCoreOf 2 H)))
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right) ⟨hd0, hdQ⟩)
  have hc2 : c * c ∈ pCoreOf 2 L := by
    have e : c * c = (w * c * w⁻¹ * c⁻¹)⁻¹ * (w * c * w⁻¹ * c) := by group
    rw [e]
    exact (pCoreOf 2 L).mul_mem ((pCoreOf 2 L).inv_mem hdO) hinv
  apply hcO
  have e : c = (c * c) * (c * c) := by
    calc c = c ^ 3 * c := by rw [hc3, one_mul]
      _ = (c * c) * (c * c) := by rw [pow_three]; group
  rw [e]
  exact (pCoreOf 2 L).mul_mem hc2 hc2

theorem isElemAbelian_VH_of_hat (hhat : IsHatA6 L) :
    IsElemAbelian 2 (conjClosure V H) := by
  refine HypF91.isElemAbelian_conjClosure_of_forall S.elemAbelian_V fun k hk v hv => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp
    (S.conjSub_le_centralizer_V_of_hat hNS h13315 h1356two hH hab hhat hk hw) v hv).symm

end Abelian

end Setting4

end CFSG.Quasithin.H13.A6
