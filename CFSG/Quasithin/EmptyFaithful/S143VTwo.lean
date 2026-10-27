module

public import CFSG.Quasithin.EmptyFaithful.S143VBr
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabTwelveA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143V

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

section

variable (h : Hyp1281Two G T M L) (D : HatModel T M)

include h in
theorem inH_of_le_mcOf {K : Subgroup G} (hTK : T ≤ K) (hKH : K ≤ mcOf T) : InH T K := by
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (Hyp1281Two.omegaOneCenter_le_VZ T M).trans h.isTwoReducedIn.2
  have hKnorm : K ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    hKH.trans (Subgroup.centralizer_le_normalizer _)
  have hZp : IsPGroup 2 (quasithinOmegaOneCenter T) := h.sylow.1.to_le hZT
  have hpc : quasithinOmegaOneCenter T ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 (hZT.trans hTK) hKnorm hZp
  exact ⟨hTK, fun hbot => h.omegaOneCenter_ne_bot (le_bot_iff.mp (hbot ▸ hpc))⟩

include h in
theorem relIndex_eq_relIndex_img (hker : Hyp1281Two.centralizerHat T M ≤ T) :
    T.relIndex (mcOf T) = (D.img T).relIndex (D.img (mcOf T)) := by
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hker' : (rhoH h D).ker ≤ T.subgroupOf (mcOf T) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hker ((mem_ker_rhoH h D x).mp hx))
  have hmapT : (T.subgroupOf (mcOf T)).map (rhoH h D) = D.img T := map_rhoH h D hTH
  have hcomap : Subgroup.comap (rhoH h D) (D.img T) = T.subgroupOf (mcOf T) := by
    rw [← hmapT, Subgroup.comap_map_eq, sup_eq_left.mpr hker']
  have h1 : T.relIndex (mcOf T) = (Subgroup.comap (rhoH h D) (D.img T)).index := by
    rw [hcomap]
    rfl
  rw [h1, Subgroup.index_comap, range_rhoH h D]

include h in
theorem card_img_ne_six
    (h35 : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M)
    (hker : Hyp1281Two.centralizerHat T M ≤ T) (hcard : Nat.card (D.img (mcOf T)) = 6) : False := by
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hSyl := isSylowTwoOf_img_T h D
  obtain ⟨j, hj⟩ := hSyl.2.1.exists_card_eq
  have hodd : ¬ 2 ∣ (D.img T).relIndex (D.img (mcOf T)) := hSyl.2.2
  have hle : D.img T ≤ D.img (mcOf T) := HatModel.img_mono hTH
  have hmul := Subgroup.relIndex_mul_card (D.img T) (D.img (mcOf T))
  rw [inf_eq_left.mpr hle, hj, hcard] at hmul
  have hr3 : (D.img T).relIndex (D.img (mcOf T)) = 3 := by
    set r := (D.img T).relIndex (D.img (mcOf T)) with hr
    rcases j with _ | _ | j
    · exfalso
      apply hodd
      simp at hmul
      exact ⟨3, by omega⟩
    · omega
    · exfalso
      have h4 : 4 ∣ r * 2 ^ (j + 1 + 1) := ⟨r * 2 ^ j, by ring⟩
      rw [hmul] at h4
      omega
  have hrel : T.relIndex (mcOf T) = 3 := by rw [relIndex_eq_relIndex_img h D hker]; exact hr3
  have hinH := inH_of_le_mcOf h hTH le_rfl
  exact h.not_le (h35 (mcOf T) hinH (Or.inl hrel))

end

end S143V

end CFSG.Quasithin
