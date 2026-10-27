module

public import CFSG.Quasithin.EmptyFaithful.S146F22
public import CFSG.Quasithin.EmptyFaithful.S146C3
public import CFSG.Quasithin.EmptyFaithful.S146C1
public import CFSG.Quasithin.EmptyFaithful.S146C2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

@[expose] def Input14624KMoves : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), Ctx24 T M K U₁ U₂ s u →
      (∃ x ∈ K, x * u * x⁻¹ ≠ u) ∧
        ∀ t ∈ T, t ∉ tZero T u →
          ∃ x ∈ K, x * (u * (t * u * t⁻¹)) * x⁻¹ ≠ u * (t * u * t⁻¹)

section Steps

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem not_mem_centralizer_pCoreOf_of_mem_oTwoFstarIn (S : Setting146 G T M) (h5 : Stage1461Five)
    {H : Subgroup G} (hH : IsHTM T M H) {v : G} (hv : v ∈ conjClosure (VZ T M) H) {x : G}
    (hx : x ∈ oTwoFstarIn (mcOf T)) (hxv : x * v * x⁻¹ ≠ v) :
    v ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) := by
  intro hvc
  have hchar : CharTwo (mcOf T) := charTwo_of_inH' S.hyp.qtke S.hyp.sylow S.isHTM_mcOf.1
  have hvG : v ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hv
  have hvQ : v ∈ pCoreOf 2 (mcOf T) := hchar ⟨hvG, hvc⟩
  have hvZ : v ∈ centerOf (pCoreOf 2 (mcOf T)) := Subgroup.mem_inf.mpr ⟨hvQ, hvc⟩
  have hvsq : v ^ 2 = 1 := isElemAbelian_pow_eq_one (S.lemma_14_5_15_two hH) hv
  have hvΩ : v ∈ omegaOneCenterOf (pCoreOf 2 (mcOf T)) := Subgroup.subset_closure ⟨hvZ, hvsq⟩
  have hxC := h5 G T M S (mcOf T) S.isHTM_mcOf hx
  have hcomm : v * x = x * v := Subgroup.mem_centralizer_iff.mp hxC v hvΩ
  apply hxv
  calc x * v * x⁻¹ = (x * v) * x⁻¹ := rfl
    _ = (v * x) * x⁻¹ := by rw [hcomm]
    _ = v := by group

end Steps

theorem input14624U2_of_moves (h5 : Stage1461Five) (iKM : Input14624KMoves) : Input14624U2 := by
  intro G _ _ T M S hB K U₁ U₂ s u hctx
  have hctx' := hctx
  obtain ⟨-, -, -, hK, -, -, hdec, hch⟩ := hctx'
  have hH : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKF : K ≤ oTwoFstarIn (mcOf T) := le_oTwoFstarIn_of_mem_cComp (hB (mcOf T) hH) hK
  have huU : u ∈ conjClosure (VZ T M) (mcOf T) := Ctx24.mem_U hK hdec hch
  obtain ⟨⟨x, hxK, hxu⟩, hmoves⟩ := iKM G T M S hB K U₁ U₂ s u hctx
  refine ⟨not_mem_centralizer_pCoreOf_of_mem_oTwoFstarIn S h5 hH huU (hKF hxK) hxu, ?_⟩
  intro t htT htn
  obtain ⟨y, hyK, hyv⟩ := hmoves t htT htn
  have htG : t ∈ mcOf T := hH.1.1 htT
  have htu : t * u * t⁻¹ ∈ conjClosure (VZ T M) (mcOf T) :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure (VZ T M) (mcOf T) htG) u).mp huU
  exact not_mem_centralizer_pCoreOf_of_mem_oTwoFstarIn S h5 hH
    ((conjClosure (VZ T M) (mcOf T)).mul_mem huU htu) (hKF hyK) hyv

theorem stage14624_of_fine_inputs_v2 (h5 : Stage1461Five) (h21 : Stage14621) (h22 : Stage14622)
    (iU1 : Input14624U1) (iU3 : Input14624U3) (iKM : Input14624KMoves) (iG : Input14624Geom)
    (i3A : Input14624ThreeA) (i3B : Input14624ThreeB) (i3C : Input14624ThreeC)
    (i3D : Input14624ThreeD) (i2 : Input14624Two) (iNT : Input14624NotTwoGroup)
    (iRk : Input14624FourRank) (i4A : Input14624FourA) (i4B : Input14624FourB) :
    Stage14624 :=
  stage14624_of_fine_inputs h21 h22 iU1 iU3 (input14624U2_of_moves h5 iKM) iG i3A i3B i3C i3D i2
    iNT iRk i4A i4B

end CFSG.Quasithin
