module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3Defs
public import CFSG.Quasithin.EmptyFaithful.SzF53B3EAlg
public import CFSG.Quasithin.EmptyFaithful.SzF53A1
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace F53B3.NoE

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_three_element {H : Subgroup G}
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) :
    ∃ d ∈ H, d ∉ pCoreOf 2 H ∧ d ^ 3 ∈ pCoreOf 2 H := by
  obtain ⟨ι⟩ := hq
  let π : ↥H →* Equiv.Perm (Fin 5) :=
    ι.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))
  have hπ : Function.Surjective π := ι.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = (pCoreOf 2 H).subgroupOf H := by
    rw [S152Fin.pCoreOf_subgroupOf]
    ext y
    simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  let c : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2
  have hc1 : c ≠ 1 := by decide
  have hc3 : c ^ 3 = 1 := by decide
  obtain ⟨x, hx⟩ := hπ c
  refine ⟨x, x.2, fun hQ => hc1 ?_, ?_⟩
  · have : x ∈ π.ker := by rw [hker]; exact hQ
    rw [← hx]
    exact this
  · have h3 : x ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hx]; exact hc3
    rw [hker] at h3
    exact h3

omit [Finite G] in
theorem cSecIn_eq_pCoreOf {H C V : Subgroup G}
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) (hNat : IsNatSec H C V)
    (hQ : ∀ q ∈ pCoreOf 2 H, ∀ x ∈ V, q * x * q⁻¹ * x⁻¹ ∈ C) : cSecIn H C V = pCoreOf 2 H := by
  have hQle : pCoreOf 2 H ≤ cSecIn H C V := fun q hq' =>
    Subgroup.subset_closure ⟨pCoreOf_le 2 H hq', hQ q hq'⟩
  obtain ⟨-, θ, -, hθs, hθk, -⟩ := hNat
  have h1 : ((cSecIn H C V).subgroupOf H).index = 120 := by
    rw [← hθk, Subgroup.index_ker, θ.range_eq_top_of_surjective hθs, Subgroup.card_top,
      S152Fin.card_Perm_five]
  have h2 := SzF53A1.index_pCoreOf_eq hq
  have hle : (pCoreOf 2 H).subgroupOf H ≤ (cSecIn H C V).subgroupOf H := fun x hx => hQle hx
  have hrel := Subgroup.relIndex_mul_index hle
  rw [h1, h2] at hrel
  have hr1 : ((pCoreOf 2 H).subgroupOf H).relIndex ((cSecIn H C V).subgroupOf H) = 1 := by
    omega
  have h3 := Subgroup.relIndex_eq_one.mp hr1
  refine le_antisymm (fun x hx => ?_) hQle
  have hxH : x ∈ H := S152Fin.cSecIn_le_left H C V hx
  exact h3 (show (⟨x, hxH⟩ : ↥H) ∈ (cSecIn H C V).subgroupOf H from hx)

structure VertexFacts (H V C Z : Subgroup G) : Prop where
  V_le_Q : V ≤ pCoreOf 2 H
  normV : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V
  comm_V : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x
  central : ∀ z ∈ Z, ∀ h ∈ H, h * z * h⁻¹ = z
  sq_Z : ∀ z ∈ Z, z * z = 1
  C_le_V : C ≤ V
  normC : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C
  C_cent : ∀ c ∈ C, ∀ l ∈ oTwoRes H, l * c * l⁻¹ = c
  Z_le_C : Z ≤ C
  comm_Q : ∀ q ∈ pCoreOf 2 H, ∀ x ∈ V, ⁅q, x⁆ ∈ Z

theorem VertexFacts.of_geometry {H M S : Subgroup G} (hB : B3Facts H M S) (hBl : B3Block H M S)
    {β : Geo H M} (hβ : vtype β = false) (hst : stab β = H) :
    VertexFacts H (Vn β) (Cv β) (Zv β) := by
  have hA : F53Amalgam H M S := hB.amalgam
  have hQ : Qv β = pCoreOf 2 H := by unfold Qv; rw [hst]
  have hVQ : Vn β ≤ Qv β := hBl.vn_le_qv β β (by rw [CosetGeom.dist_self]; exact Nat.zero_le _)
  have hnormV : H ≤ Subgroup.normalizer (Vn β : Set G) := by
    have := stab_le_normalizer_Vn (H := H) (M := M) β
    rw [hst] at this
    exact this
  have hCdef : Cv β = Vn β ⊓ Subgroup.centralizer (oTwoRes H : Set G) := by
    unfold Cv; rw [hst]
  have hcentral : ∀ z ∈ Zv β, ∀ h ∈ H, h * z * h⁻¹ = z := by
    intro z hz h hh
    have hzc := hB.central β hβ hz
    rw [hst] at hzc
    have h1 := Subgroup.mem_centralizer_iff.mp hzc.2 h hh
    calc h * z * h⁻¹ = z * h * h⁻¹ := by rw [h1]
      _ = z := by group
  have hZV : Zv β ≤ Vn β := by
    obtain ⟨μ, hμ⟩ := exists_adj β
    exact (hBl.zv_le_zv β μ hβ hμ).trans (le_iSup₂_of_le
      (f := fun (μ' : Geo H M) (_ : μ' ∈ nbrs β) => Zv μ') μ (show μ ∈ nbrs β from hμ) le_rfl)
  refine ⟨?_, ?_, ?_, hcentral, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hQ]; exact hVQ
  · intro h hh v hv
    exact (Subgroup.mem_normalizer_iff.mp (hnormV hh) v).mp hv
  · exact fun x hx y hy => isElemAbelian_comm (hBl.elemAbelian_vn β) hx hy
  · intro z hz
    have := isElemAbelian_pow_eq_one (isElemAbelian_Zv hA β) hz
    rw [← sq]
    exact this
  · rw [hCdef]; exact inf_le_left
  · intro h hh c hc
    rw [hCdef] at hc ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hnormV hh) c).mp hc.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
    have hl' : h⁻¹ * l * h ∈ oTwoRes H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes H (H.inv_mem hh)) l).mp hl
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hl'
    calc l * (h * c * h⁻¹) = h * ((h⁻¹ * l * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * l * h)) * h⁻¹ := by rw [h1]
      _ = (h * c * h⁻¹) * l := by group
  · intro c hc l hl
    rw [hCdef] at hc
    have h1 := Subgroup.mem_centralizer_iff.mp hc.2 l hl
    calc l * c * l⁻¹ = c * l * l⁻¹ := by rw [h1]
      _ = c := by group
  · intro z hz
    rw [hCdef]
    refine ⟨hZV hz, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have h1 := hcentral z hz l (oTwoRes_le H hl)
    calc l * z = (l * z * l⁻¹) * l := by group
      _ = z * l := by rw [h1]
  · intro q hq' x hx
    have h1 : ⁅x, q⁆ ∈ ⁅Vn β, Qv β⁆ := Subgroup.commutator_mem_commutator hx (by rw [hQ]; exact hq')
    rw [hBl.comm_vn_qv β hβ] at h1
    rw [← commutatorElement_inv x q]
    exact (Zv β).inv_mem h1

namespace VertexFacts

variable {H V C Z : Subgroup G}

omit [Finite G] in
theorem hcube (hF : VertexFacts H V C Z) {d : G} (hd3 : d ^ 3 ∈ pCoreOf 2 H) :
    ∀ w ∈ V, d ^ 3 * w * (d ^ 3)⁻¹ * w⁻¹ ∈ C :=
  fun w hw => hF.Z_le_C (hF.comm_Q _ hd3 w hw)

end VertexFacts

omit [Finite G] in
theorem hfix_of_nat3 {H V C Z : Subgroup G} (hF : VertexFacts H V C Z)
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) (hNat : IsNatSec H C V)
    (hnat3 : ∀ F L X : Subgroup G, IsNatSec F L X → ∀ d ∈ F, d ∉ cSecIn F L X →
      d ^ 3 ∈ cSecIn F L X → ∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ L → x ∈ L)
    {d : G} (hd : d ∈ H) (hdQ : d ∉ pCoreOf 2 H) (hd3 : d ^ 3 ∈ pCoreOf 2 H) :
    ∀ y ∈ V, d * y * d⁻¹ * y⁻¹ ∈ C → y ∈ C := by
  have hcs : cSecIn H C V = pCoreOf 2 H :=
    cSecIn_eq_pCoreOf hq hNat fun q hq' x hx => hF.Z_le_C (hF.comm_Q q hq' x hx)
  intro y hy hdy
  exact hnat3 H C V hNat d hd (by rw [hcs]; exact hdQ) (by rw [hcs]; exact hd3) y hy hdy

theorem pair_mem_Z {H M S : Subgroup G} (hB : B3Facts H M S) (hBl : B3Block H M S)
    {β : Geo H M} (hβ : vtype β = false) (hst : stab β = H) {E : Subgroup G}
    (hEQ : E ≤ pCoreOf 2 H) (hEn : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E)
    (hS1 : E ⊓ Vn β ≤ Cv β) : ∀ e ∈ E, ∀ v ∈ Vn β, ⁅e, v⁆ ∈ Zv β := by
  have hA : F53Amalgam H M S := hB.amalgam
  have hF := VertexFacts.of_geometry hB hBl hβ hst
  have hQ : Qv β = pCoreOf 2 H := by unfold Qv; rw [hst]
  have hEH : E ≤ H := hEQ.trans (pCoreOf_le 2 H)
  have hbase : PairBase H E (Vn β) (Zv β) :=
    ⟨hEH, hEn, hF.normV, hF.comm_V, hF.central, hF.sq_Z⟩
  intro e he
  let T : Subgroup G :=
    { carrier := {v | v ∈ Vn β ∧ ⁅e, v⁆ ∈ Zv β}
      one_mem' := ⟨(Vn β).one_mem, by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨(Vn β).mul_mem ha.1 hb.1, by
        rw [hbase.pair_mul_right he ha.1 hb.1]; exact (Zv β).mul_mem ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨(Vn β).inv_mem ha.1, by
        have h1 := hbase.pair_mul_right he ha.1 ((Vn β).inv_mem ha.1)
        rw [mul_inv_cancel] at h1
        have h3 : ⁅e, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
        rw [h3] at h1
        rw [eq_inv_of_mul_eq_one_right h1.symm]
        exact (Zv β).inv_mem ha.2⟩ }
  have hVT : Vn β ≤ T := by
    unfold Vn
    refine iSup₂_le fun μ hμ z hz => ?_
    have hzV : z ∈ Vn β := le_iSup₂_of_le
      (f := fun (μ' : Geo H M) (_ : μ' ∈ nbrs β) => Zv μ') μ hμ le_rfl hz
    refine ⟨hzV, ?_⟩
    have heμ : e ∈ stab μ := Qv_le_stab_of_mem_nbrs hA hμ (by rw [hQ]; exact hEQ he)
    have h1 : e * z * e⁻¹ ∈ Zv μ :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA μ heμ) z).mp hz
    have h2 : ⁅e, z⁆ ∈ Zv μ := by
      have := (Zv μ).mul_mem h1 ((Zv μ).inv_mem hz)
      exact this
    have hzH : z ∈ H := pCoreOf_le 2 H (hF.V_le_Q hzV)
    have h3 : ⁅e, z⁆ ∈ E := by
      have := E.mul_mem he (hEn z hzH e⁻¹ (E.inv_mem he))
      have e1 : ⁅e, z⁆ = e * (z * e⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
      rw [e1]
      exact this
    have h4 : ⁅e, z⁆ ∈ Vn β := hbase.pair_mem_V he hzV
    have h5 : ⁅e, z⁆ ∈ Cv β := hS1 ⟨h3, h4⟩
    have h6 : ⁅e, z⁆ ∈ Cv β ⊓ Zv μ := ⟨h5, h2⟩
    rw [hBl.cv_inf_zv β μ hβ hμ] at h6
    exact h6
  intro v hv
  exact (hVT hv).2

end F53B3.NoE

end CFSG.Quasithin
