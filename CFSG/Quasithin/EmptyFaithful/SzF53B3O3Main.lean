module

public import CFSG.Quasithin.Background.F8G2
public import CFSG.Quasithin.EmptyFaithful.SzF53B3NGeo
public import CFSG.Quasithin.EmptyFaithful.SzF53B3OrthDefs
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O3Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.F53
open CFSG.Quasithin.F53Mod CFSG.Quasithin.CosetGeom

namespace F53B3

variable {G : Type} [Group G] {H M S : Subgroup G}

namespace N37

theorem cSecIn_eq_pCoreOf_of_orth [Finite G] {F L X : Subgroup G}
    (hq : Nonempty (OTwoQuot F ≃* Equiv.Perm (Fin 5))) (hN : IsOrthSec F L X)
    (hle : pCoreOf 2 F ≤ cSecIn F L X) : cSecIn F L X = pCoreOf 2 F := by
  obtain ⟨_, θ, β, hθs, hθk, _⟩ := hN
  have hc : ((cSecIn F L X).subgroupOf F).index = 120 := by
    rw [← hθk, Subgroup.index_ker, θ.range_eq_top_of_surjective hθs, Subgroup.card_top]
    exact S152Fin.card_Perm_five
  have hp := SzF53A1.index_pCoreOf_eq hq
  have hsub : (pCoreOf 2 F).subgroupOf F ≤ (cSecIn F L X).subgroupOf F := fun x hx => hle hx
  have hrel := Subgroup.relIndex_mul_index hsub
  rw [hc, hp] at hrel
  have h1 : ((pCoreOf 2 F).subgroupOf F).relIndex ((cSecIn F L X).subgroupOf F) = 1 := by
    omega
  have h2 := Subgroup.relIndex_eq_one.mp h1
  refine le_antisymm (fun x hx => ?_) hle
  have hxF : x ∈ F := S152Fin.cSecIn_le_left F L X hx
  exact h2 (show (⟨x, hxF⟩ : ↥F) ∈ (cSecIn F L X).subgroupOf F from hx)

theorem cSecIn_orth_eq_Qv [Finite G] (hB : B3FactsO H M S) (hBl : B3Block H M S) {x : Geo H M}
    (hx : vtype x = false) : cSecIn (stab x) (Cv x) (Vn x) = Qv x := by
  have hq := quot_stab_five hB.amalgam hx
  refine cSecIn_eq_pCoreOf_of_orth hq (hB.orth x hx) fun q hq' => ?_
  refine Subgroup.subset_closure ⟨Qv_le_stab_self x hq', fun v hv => ?_⟩
  have h1 : v * q * v⁻¹ * q⁻¹ ∈ ⁅Vn x, Qv x⁆ := Subgroup.commutator_mem_commutator hv hq'
  rw [hBl.comm_vn_qv x hx] at h1
  have e : q * v * q⁻¹ * v⁻¹ = (v * q * v⁻¹ * q⁻¹)⁻¹ := by group
  rw [e]
  exact Zv_le_Cv hBl hx (Zv x |>.inv_mem h1)

theorem orth_step2 [Finite G] (hB : B3FactsO H M S) (hBl : B3Block H M S) (hC1 : OrthC1 H M S)
    (hT1 : ∀ F L X S₀ : Subgroup G, IsOrthSec F L X → IsSylowTwoOf S₀ F → ∀ U : Subgroup G,
      L ≤ U → U ≤ X → S₀ ≤ Subgroup.normalizer (U : Set G) → L.relIndex U = 4 →
      (cSecIn F L X).relIndex (cSecIn S₀ L U) = 4)
    {x y μ : Geo H M} (hx : vtype x = false) (hvμ : vtype μ = true)
    (hμx : (graph (H ⊔ M) H M).Adj μ x) (hμy : (graph (H ⊔ M) H M).Adj μ y) (hxy : x ≠ y) :
    (Qv x).relIndex (cSecIn (stab μ ⊓ stab x) (Cv x) (Vn x ⊓ Vn y ⊔ Cv x)) = 4 ∧
      ∀ A : Subgroup G, A ≤ stab μ ⊓ stab x →
        (∀ c ∈ A, ∀ r ∈ Vn x ⊓ Vn y, c * r = r * c) →
        A ≤ cSecIn (stab μ ⊓ stab x) (Cv x) (Vn x ⊓ Vn y ⊔ Cv x) := by
  have hcsec := cSecIn_orth_eq_Qv hB hBl hx
  have hXF : Vn x ≤ stab x := Vn_le_stab_self hBl x
  have hFL := stab_le_normalizer_Cv x
  have hRn : stab μ ≤ Subgroup.normalizer ((Vn x ⊓ Vn y : Subgroup G) : Set G) :=
    hBl.vn_inf_normal y μ x hxy.symm hvμ hμx hμy
  have hZR : Zv x ≤ Vn x ⊓ Vn y :=
    (hBl.zv_le_zv x μ hx hμx.symm).trans (le_inf (Zv_le_Vn_of_adj hμx.symm)
      (Zv_le_Vn_of_adj hμy.symm))
  have hCx : Cv x = Zv x := hC1.cv_eq x hx
  have hR4 : (Cv x).relIndex (Vn x ⊓ Vn y ⊔ Cv x) = 4 := by
    rw [hCx, sup_of_le_left hZR]
    have h1 := Subgroup.relIndex_mul_card (H := Zv x) (K := Vn x ⊓ Vn y)
    rw [inf_of_le_left hZR, hB.card_two x hx, hC1.card_R x y μ hxy hvμ hμx hμy] at h1
    omega
  have hnorm : stab μ ⊓ stab x ≤
      Subgroup.normalizer ((Vn x ⊓ Vn y ⊔ Cv x : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (inf_le_left.trans hRn) (inf_le_right.trans hFL)
  have hl2 := hT1 (stab x) (Cv x) (Vn x) (stab μ ⊓ stab x) (hB.orth x hx)
    (sylow_inf_stab hB.amalgam hμx.symm) (Vn x ⊓ Vn y ⊔ Cv x) le_sup_right
    (sup_le inf_le_left (Cv_le_Vn x)) hnorm hR4
  rw [hcsec] at hl2
  refine ⟨hl2, fun A hA hAc => ?_⟩
  have hRL : Vn x ⊓ Vn y ≤ Subgroup.normalizer (Cv x : Set G) :=
    (inf_le_left.trans hXF).trans hFL
  exact le_cSecIn_sup hA inf_le_right hFL hRL fun r hr c hc => by
    rw [hAc c hc r hr]
    simp

theorem step_central_orth [Finite G] (hB : B3FactsO H M S) (hBl : B3Block H M S)
    (hC1 : OrthC1 H M S) (hS4 : OrthS4 H M S)
    (hT1 : ∀ F L X S₀ : Subgroup G, IsOrthSec F L X → IsSylowTwoOf S₀ F → ∀ U : Subgroup G,
      L ≤ U → U ≤ X → S₀ ≤ Subgroup.normalizer (U : Set G) → L.relIndex U = 4 →
      (cSecIn F L X).relIndex (cSecIn S₀ L U) = 4)
    (hM6 : ∀ K U A B : Subgroup G, Nonempty (OTwoQuot K ≃* Equiv.Perm (Fin 5)) → U ≤ K →
      U ≤ pCoreOf 2 K → IsChiefStep K U A B → ¬ IsCentralStep K A B →
      ∀ a ∈ K, a ∉ pCoreOf 2 K → a ^ 2 ∈ pCoreOf 2 K →
      a ∈ oTwoRes K ⊔ pCoreOf 2 K → 2 < secIdx (Subgroup.zpowers a) A B)
    {β : Geo H M} (hβ : vtype β = false) {A B : Subgroup G}
    (hstep : IsChiefStep (stab β) (Kq β) A B) (hVA : Vn β ≤ A) :
    IsCentralStep (stab β) A B := by
  by_contra hnc
  obtain ⟨α, γ, hβα, hαγ, hγβ, hvα, hvγ, hdist⟩ := exists_arc hB.amalgam hβ
  have hdist' : dist γ β = 2 := by rw [CosetGeom.dist_comm]; exact hdist
  have hq := quot_stab_five hB.amalgam hβ
  have hS2γ := orth_step2 hB hBl hC1 hT1 hvγ hvα hαγ hβα.symm hγβ
  have hKS : Kq β ≤ stab α ⊓ stab γ := by
    have h1 : Kq β ≤ Qv α := hBl.kq_le_qv β α hβ hβα
    exact le_inf (h1.trans (Qv_le_stab_self α)) (h1.trans (Qv_le_stab_of_mem_nbrs hB.amalgam hαγ))
  have hKT := hS2γ.2 (Kq β) hKS fun c hc r hr =>
    (Subgroup.mem_centralizer_iff.mp hc.2 r hr.2).symm
  have hVT : Vn γ ≤ oTwoRes (stab β) ⊔ Qv β := hS4.le_A5 γ β α hγβ hvα hαγ hβα.symm
  have hY2 : ((Kq β ⊓ Qv γ) ⊔ Vn β).relIndex (Kq β) ≤ 2 :=
    relIndex_sup_le_two hKT hS2γ.1 (Vn_le_Kq hBl β) (hBl.not_vn_le_qv β γ hβ hdist)
  have hZV : Zv γ ≤ Vn β :=
    (hBl.zv_le_zv γ α hvγ hαγ.symm).trans (Zv_le_Vn_of_adj hβα)
  have hY1 : Kq β ⊓ Qv γ ≤ centralizerMod (Vn β) ⊤ (Vn γ) := by
    intro y hy
    refine ⟨trivial, (Subgroup.mem_normalizer_iff.mpr ?_ : y ∈ _), fun u hu => ?_⟩
    · exact fun z => (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β
        (Kq_le_stab β hy.1)) z)
    · have h1 : y * u * y⁻¹ * u⁻¹ ∈ ⁅Qv γ, Vn γ⁆ := Subgroup.commutator_mem_commutator hy.2 hu
      rw [Subgroup.commutator_comm, hBl.comm_vn_qv γ hvγ] at h1
      exact hZV h1
  have hY2' : Vn β ≤ centralizerMod (Vn β) ⊤ (Vn γ) := by
    intro y hy
    refine ⟨trivial, (Subgroup.mem_normalizer_iff.mpr ?_ : y ∈ _), fun u hu => ?_⟩
    · exact fun z => (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β
        (Vn_le_stab_self hBl β hy)) z)
    · have h1 : y * u * y⁻¹ * u⁻¹ ∈ ⁅Vn β, Vn γ⁆ := Subgroup.commutator_mem_commutator hy hu
      exact (hBl.comm_vn_vn β γ hdist h1).1
  have hYc : ∀ y ∈ (Kq β ⊓ Qv γ) ⊔ Vn β, ∀ u ∈ Vn γ, y * u * y⁻¹ * u⁻¹ ∈ Vn β :=
    fun y hy u hu => ((sup_le hY1 hY2') hy).2.2 u hu
  obtain ⟨v, hvV, hvQ⟩ := IsConcreteLE.not_le_iff_exists.mp (hBl.not_vn_le_qv γ β hvγ hdist')
  have hv2 : v ^ 2 = 1 := (hBl.elemAbelian_vn γ).2 v hvV
  have hlow := hM6 (stab β) (Kq β) A B hq (Kq_le_stab β) (Kq_le_Qv β) hstep hnc v
    (hBl.vn_le_stab γ β hdist'.le hvV) hvQ (by rw [hv2]; exact (pCoreOf 2 (stab β)).one_mem)
    (hVT hvV)
  have hup := secIdx_le_of_centralizes (K := Kq β) (Y := (Kq β ⊓ Qv γ) ⊔ Vn β) hstep.1.1 hVA hvV hYc
  omega

end N37

theorem n37_orth {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
    (hB : B3FactsO H M S) (hBl : B3Block H M S) (hC1 : OrthC1 H M S) (hS4 : OrthS4 H M S)
    (hT1 : ∀ F L X S₀ : Subgroup G, IsOrthSec F L X → IsSylowTwoOf S₀ F → ∀ U : Subgroup G,
      L ≤ U → U ≤ X → S₀ ≤ Subgroup.normalizer (U : Set G) → L.relIndex U = 4 →
      (cSecIn F L X).relIndex (cSecIn S₀ L U) = 4)
    (hM6 : ∀ K U A B : Subgroup G, Nonempty (OTwoQuot K ≃* Equiv.Perm (Fin 5)) → U ≤ K →
      U ≤ pCoreOf 2 K → IsChiefStep K U A B → ¬ IsCentralStep K A B →
      ∀ a ∈ K, a ∉ pCoreOf 2 K → a ^ 2 ∈ pCoreOf 2 K →
      a ∈ oTwoRes K ⊔ pCoreOf 2 K → 2 < secIdx (Subgroup.zpowers a) A B)
    {β : Geo H M} (hβ : vtype β = false) :
    ⁅Kq β, oTwoRes (stab β)⁆ ≤ Vn β := by
  rw [oTwoRes_eq_oTwoUpper]
  have hW : IsNormalIn (stab β) (Kq β) (Vn β) :=
    ⟨N37.Vn_le_Kq hBl β, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β hg) x).mp hx⟩
  have hK : IsNormalIn (stab β) (Kq β) (Kq β) :=
    ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (N37.stab_le_normalizer_Kq β hg) x).mp hx⟩
  exact N37.commutator_le_of_central_steps (N37.Kq_le_stab β) (N37.Kq_le_Qv β) hW hK
    (N37.Vn_le_Kq hBl β) fun A B hstep hVA =>
      N37.step_central_orth hB hBl hC1 hS4 hT1 hM6 hβ hstep hVA

theorem n37_orth_of_hM6 {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
    (hB : B3FactsO H M S) (hBl : B3Block H M S) (hC1 : OrthC1 H M S) (hS4 : OrthS4 H M S)
    (hM6 : ∀ K U A B : Subgroup G, Nonempty (OTwoQuot K ≃* Equiv.Perm (Fin 5)) → U ≤ K →
      U ≤ pCoreOf 2 K → IsChiefStep K U A B → ¬ IsCentralStep K A B →
      ∀ a ∈ K, a ∉ pCoreOf 2 K → a ^ 2 ∈ pCoreOf 2 K →
      a ∈ oTwoRes K ⊔ pCoreOf 2 K → 2 < secIdx (Subgroup.zpowers a) A B)
    {β : Geo H M} (hβ : vtype β = false) :
    ⁅Kq β, oTwoRes (stab β)⁆ ≤ Vn β :=
  n37_orth hB hBl hC1 hS4
    (fun _ _ _ _ h hS _ hLU hUX hn h4 => IsOrthSec.relIndex_centralizer_l2 h hS hLU hUX hn h4)
    hM6 hβ

end F53B3

end CFSG.Quasithin
