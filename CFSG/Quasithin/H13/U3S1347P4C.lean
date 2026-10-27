module

public import CFSG.Quasithin.H13.U3S1347P4B
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.H13.U3S132210B

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

theorem d0123_props : InD6 (swap 0 1 * swap 2 3) ∧
    swap 0 1 * swap 2 3 ∈ alternatingGroup (Fin 6) ∧ InE8 (swap 0 1 * swap 2 3) ∧
    c2perm * (swap 0 1 * swap 2 3) * c2perm⁻¹ * (swap 0 1 * swap 2 3)⁻¹ ≠ 1 := by
  refine ⟨by decide, Perm.mem_alternatingGroup.2 (by decide), by decide, by decide⟩

theorem c2_decomp : ∀ x : P6, (∑ i, Multiplicative.toAdd x i = 0) → ∃ y : P6,
    (∑ i, Multiplicative.toAdd y i = 0) ∧ (x = y * (G6.permAct 6 c2perm y)⁻¹ ∨
      x = y * (G6.permAct 6 c2perm y)⁻¹ * G6.allOnes 6) := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem le_of_isMaxElemAbelian {S A U : Subgroup G} [Finite G] (hA : IsMaxElemAbelian S A)
    (hUS : U ≤ S) (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hUA : U ≤ centralizer (A : Set G)) : U ≤ A := by
  rw [eq_omegaOneOf_centralizer hA]
  intro u hu
  exact subset_closure ⟨⟨hUS hu, hUA hu⟩, hU2 u hu⟩

theorem s1347_four_count (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) (hB : H13.IsA6Block L)
    {V₀ : Subgroup G} (hV₀T : T ≤ normalizer (V₀ : Set G)) (hV₀O : V₀ ≤ pCoreOf 2 (L ⊔ T))
    (hzV : S.zV ∈ V₀) {c : G} (hcL2 : c ∈ l2Of S)
    (hcN : c ∈ normalizer (V : Set G)) (hcρ : S.frame.ρ ⟨c, hcN⟩ = c2perm) (hc3 : c ^ 3 = 1)
    (hcV₀ : c ∈ normalizer (V₀ : Set G))
    (h16 : 16 ≤ (centralizer ({c} : Set G)).relIndex V₀) :
    V ≤ V₀ ∧ ∀ q ∈ pCoreOf 2 (L ⊔ T), c * q * c⁻¹ * q⁻¹ ∈ V₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({c} : Set G) with hC
  set R₂ := pCoreOf 2 (l2Of S ⊔ T) with hR₂def
  set O := pCoreOf 2 (L ⊔ T) with hOdef
  have hR₂ : R₂ = T ⊓ centralizer (v2Of S : Set G) := s134_pCoreOf_L2T S he
  have hO : O = T ⊓ centralizer (V : Set G) := (s134_cT S).symm
  have hcL : c ∈ L := s134_L2_le_L S hcL2
  have hOR : O ≤ R₂ := by
    rw [hO, hR₂]
    exact inf_le_inf_left T (centralizer_le (SetLike.coe_subset_coe.2 (S.pre_le_V _)))
  have hR₂T : R₂ ≤ T := s134_R2_le_T S
  have hR₂2 : IsPGroup 2 R₂ := pCoreOf_isPGroup 2 _
  have hON : L ⊔ T ≤ normalizer (O : Set G) := le_normalizer_pCoreOf 2 _
  have hR₂N : R₂ ≤ normalizer (O : Set G) := hR₂T.trans (le_sup_right.trans hON)
  have hcO : c ∈ normalizer (O : Set G) := hON (mem_sup_left hcL)
  have hcR₂ : c ∈ normalizer (R₂ : Set G) := le_normalizer_pCoreOf 2 _ (mem_sup_left hcL2)
  have hupper : C.relIndex R₂ ≤ 64 := s134_relIndex_R2_le S hB hcL2 hc3
  have hb : 4 ≤ (O ⊔ (R₂ ⊓ C)).relIndex R₂ := by
    rcases relIndex_sup_eq_one_or hc3 hR₂2 hOR hR₂N hcO hcR₂ with h | h
    · exfalso
      obtain ⟨hD, hA, hE, hne⟩ := d0123_props
      obtain ⟨r, ⟨hrT, -⟩, hrρ⟩ := s134_exists_TL S hD hA
      have hrR : (r : G) ∈ R₂ := by
        rw [hR₂]
        exact ⟨hrT, s134_mem_centralizer_V2_of_inE8 S r (by rw [hrρ]; exact hE)⟩
      have hrs := relIndex_eq_one.1 h hrR
      obtain ⟨q, hq, z, hz, hqz⟩ :=
        (mem_sup_iff_of_le_normalizer (inf_le_left.trans hR₂N)).1 hrs
      have hzc : Commute z c := mem_centralizer_singleton_iff.1 (mem_inf.1 hz).2
      have hzc' : z * c⁻¹ = c⁻¹ * z := hzc.inv_right.eq
      have hrqz : (r : G) = q * z := by first | exact hqz | exact hqz.symm
      have hcomm : c * r * c⁻¹ * (r : G)⁻¹ = c * q * c⁻¹ * q⁻¹ := by
        rw [hrqz]
        calc c * (q * z) * c⁻¹ * (q * z)⁻¹ = c * q * (z * c⁻¹) * z⁻¹ * q⁻¹ := by group
          _ = c * q * (c⁻¹ * z) * z⁻¹ * q⁻¹ := by rw [hzc']
          _ = c * q * c⁻¹ * q⁻¹ := by group
      have hmem : c * r * c⁻¹ * (r : G)⁻¹ ∈ O := by
        rw [hcomm]
        exact mul_mem ((mem_normalizer_iff.1 hcO q).1 hq) (inv_mem hq)
      rw [hO] at hmem
      have h1 := (s134_rho_eq_one_iff S (⟨c, hcN⟩ * r * (⟨c, hcN⟩)⁻¹ * r⁻¹)).2 (mem_inf.1 hmem).2
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcρ, hrρ] at h1
      exact hne h1
    · exact h
  have hON₀ : O ≤ normalizer (V₀ : Set G) :=
    (pCoreOf_le_of_sylow S.h13.sylow le_sup_right).trans hV₀T
  have hmul1 := relIndex_centralizer_eq_mul (x := c) hOR hR₂N
  have hmul2 := relIndex_centralizer_eq_mul (x := c) hV₀O hON₀
  have hpos : 0 < (V₀ ⊔ (O ⊓ C)).relIndex O := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have h1 : (V₀ ⊔ (O ⊓ C)).relIndex O = 1 := by
    by_contra hne
    have h2 : 2 ≤ (V₀ ⊔ (O ⊓ C)).relIndex O := by omega
    have h3 : 4 * (2 * 16) ≤ C.relIndex R₂ := by
      rw [hmul1, hmul2]
      exact Nat.mul_le_mul hb (Nat.mul_le_mul h2 h16)
    omega
  have hOle := relIndex_eq_one.1 h1
  have hcomm : ∀ q ∈ O, c * q * c⁻¹ * q⁻¹ ∈ V₀ := by
    intro q hq
    obtain ⟨a, ha, z, hz, haz⟩ :=
      (mem_sup_iff_of_le_normalizer (inf_le_left.trans hON₀)).1 (hOle hq)
    have hzc : Commute z c := mem_centralizer_singleton_iff.1 (mem_inf.1 hz).2
    have hzc' : z * c⁻¹ = c⁻¹ * z := hzc.inv_right.eq
    have hqaz : q = a * z := by first | exact haz | exact haz.symm
    have e : c * q * c⁻¹ * q⁻¹ = c * a * c⁻¹ * a⁻¹ := by
      rw [hqaz]
      calc c * (a * z) * c⁻¹ * (a * z)⁻¹ = c * a * (z * c⁻¹) * z⁻¹ * a⁻¹ := by group
        _ = c * a * (c⁻¹ * z) * z⁻¹ * a⁻¹ := by rw [hzc']
        _ = c * a * c⁻¹ * a⁻¹ := by group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.1 hcV₀ a).1 ha) (inv_mem ha)
  refine ⟨?_, hcomm⟩
  have hVc : V ≤ centralizer (V : Set G) := fun v hv =>
    mem_centralizer_iff.2 fun w hw => (B6.isElemAbelian_iff.1 (s134_elemAbelian_V S)).1 w hw v hv
  have hVO : V ≤ O := by rw [hO]; exact le_inf S.V_le_T hVc
  intro v hv
  obtain ⟨y, hy0, hy⟩ := c2_decomp (S.frame.ψ ⟨v, hv⟩ : P6)
    (G6.mem_coreMod.1 (S.frame.ψ ⟨v, hv⟩).2)
  set w : ↥V := S.frame.ψ.symm ⟨y, G6.mem_coreMod.2 hy0⟩ with hw
  have hψw : (S.frame.ψ w : P6) = y := by rw [hw, MulEquiv.apply_symm_apply]
  have hcw : c * (w : G) * c⁻¹ ∈ V := (mem_normalizer_iff.1 hcN w).1 w.2
  have hψcw : (S.frame.ψ ⟨c * w * c⁻¹, hcw⟩ : P6) = G6.permAct 6 c2perm y := by
    have h2 := S.psi_conj ⟨c, hcN⟩ w
    rw [hcρ] at h2
    have e : (⟨c * w * c⁻¹, hcw⟩ : ↥V) =
        ⟨((⟨c, hcN⟩ : ↥(normalizer (V : Set G))) : G) * w *
          ((⟨c, hcN⟩ : ↥(normalizer (V : Set G))) : G)⁻¹,
          (mem_normalizer_iff.mp (⟨c, hcN⟩ : ↥(normalizer (V : Set G))).2 w).mp w.2⟩ := rfl
    rw [e, h2, G6.coreAct_coe, hψw]
  set u : ↥V := w * (⟨c * w * c⁻¹, hcw⟩ : ↥V)⁻¹ with hu
  have hψu : (S.frame.ψ u : P6) = y * (G6.permAct 6 c2perm y)⁻¹ := by
    rw [hu, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hψw, hψcw]
  have huV₀ : (u : G) ∈ V₀ := by
    have h2 := hcomm (w : G)⁻¹ (inv_mem (hVO w.2))
    have e : (u : G) = c * (w : G)⁻¹ * c⁻¹ * ((w : G)⁻¹)⁻¹ := by
      rw [hu, Subgroup.coe_mul, Subgroup.coe_inv]
      show (w : G) * (c * w * c⁻¹)⁻¹ = c * (w : G)⁻¹ * c⁻¹ * ((w : G)⁻¹)⁻¹
      have hcomm' := (B6.isElemAbelian_iff.1 (s134_elemAbelian_V S)).1 _ w.2 _
        (inv_mem hcw)
      calc (w : G) * (c * w * c⁻¹)⁻¹ = (c * w * c⁻¹)⁻¹ * w := hcomm'
        _ = c * (w : G)⁻¹ * c⁻¹ * ((w : G)⁻¹)⁻¹ := by group
    rw [e]
    exact h2
  rcases hy with h1 | h1
  · have : (⟨v, hv⟩ : ↥V) = u := S.frame.ψ.injective (Subtype.ext (by rw [hψu]; exact h1))
    rw [show v = (u : G) from congrArg Subtype.val this]
    exact huV₀
  · have : (⟨v, hv⟩ : ↥V) = u * ⟨S.zV, S.zV_mem_V⟩ := S.frame.ψ.injective (Subtype.ext (by
      rw [map_mul, Subgroup.coe_mul, hψu, S.psi_zV]
      exact h1))
    rw [show v = (u : G) * S.zV from congrArg Subtype.val this]
    exact mul_mem huV₀ hzV

end CFSG.Quasithin.H13.U3
