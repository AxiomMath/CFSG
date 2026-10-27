module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3NStep2
public import CFSG.Quasithin.Background.F8G2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.F53
open CFSG.Quasithin.F53Mod CFSG.Quasithin.CosetGeom

namespace F53B3

variable {G : Type} [Group G] {H M S : Subgroup G}

namespace N37

theorem step_central [Finite G] (hB : B3Facts H M S) (hBl : B3Block H M S) (hN : NatFacts G)
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
  have hS2γ := step2 hB hBl hN hvγ hβ hαγ.symm hβα.symm hγβ
  have hKS : Kq β ≤ stab α ⊓ stab γ := by
    have h1 : Kq β ≤ Qv α := hBl.kq_le_qv β α hβ hβα
    exact le_inf (h1.trans (Qv_le_stab_self α)) (h1.trans (Qv_le_stab_of_mem_nbrs hB.amalgam hαγ))
  have hKT : Kq β ≤ That α γ := hS2γ.1 (Kq β) hKS fun c hc r hr =>
    (Subgroup.mem_centralizer_iff.mp hc.2 r hr.2).symm
  have hS2β := step2 hB hBl hN hβ hvγ hβα hαγ hγβ.symm
  have hVS : Vn γ ≤ stab α ⊓ stab β :=
    le_inf ((hBl.vn_le_qv γ α (dist_le_one_of_adj hαγ.symm)).trans (Qv_le_stab_self α))
      (hBl.vn_le_stab γ β hdist'.le)
  have hVT : Vn γ ≤ oTwoRes (stab β) ⊔ Qv β :=
    (hS2β.1 (Vn γ) hVS fun c hc r hr => elemAbelian_comm (hBl.elemAbelian_vn γ) hc hr.2).trans
      inf_le_right
  have hY2 : ((Kq β ⊓ Qv γ) ⊔ Vn β).relIndex (Kq β) ≤ 2 :=
    relIndex_sup_le_two hKT hS2γ.2 (Vn_le_Kq hBl β) (hBl.not_vn_le_qv β γ hβ hdist)
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

theorem n37 {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
    (hB : B3Facts H M S) (hBl : B3Block H M S)
    (hcard16 : ∀ F L X : Subgroup G, IsNatSec F L X → L.relIndex X = 16)
    (hinv4 : ∀ F L X : Subgroup G, IsNatSec F L X → L ≤ X → ∀ a ∈ F, a ∉ cSecIn F L X →
      a ^ 2 ∈ cSecIn F L X →
      secIdx (Subgroup.zpowers a) L X = 4 ∧ L.relIndex (commSec (Subgroup.zpowers a) L X) = 4)
    (hl2 : ∀ F L X S₀ : Subgroup G, IsNatSec F L X → IsSylowTwoOf S₀ F →
      ∀ U : Subgroup G, L ≤ U → U ≤ X → S₀ ≤ Subgroup.normalizer (U : Set G) →
      L.relIndex U = 4 →
      cSecIn S₀ L U = S₀ ⊓ (oTwoRes F ⊔ cSecIn F L X) ∧
      (cSecIn F L X).relIndex (S₀ ⊓ (oTwoRes F ⊔ cSecIn F L X)) = 4)
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
      N37.step_central hB hBl ⟨hcard16, hinv4, hl2⟩ hM6 hβ hstep hVA

end F53B3

end CFSG.Quasithin
