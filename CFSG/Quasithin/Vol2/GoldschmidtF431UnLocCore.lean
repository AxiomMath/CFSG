module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLoc442K
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutGenA

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431

universe u

section Core


variable {Mb : Type u} [Group Mb] [Finite Mb] [DecidableEq Mb] {G : Type} [Group G] [Finite G]
  {T N N' : Subgroup Mb} {I : Finset Mb} {z t : Mb} {b : ↥N →* G} {b' : ↥N' →* G}
  {M M' : Subgroup G}

theorem un_local_core (LK : F431LieK T N N' I z) (S : UnGSetup N N' b b' M M')
    (hI : I = {z, t}) (hzt : z * t = t * z) (cz : Subgroup.centralizer ({z} : Set Mb) ≤ N)
    (ct : Subgroup.centralizer ({t} : Set Mb) ≤ N')
    (hSylt : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t} : Set Mb))
      (Subgroup.centralizer ({t} : Set Mb)))
    {V4 V Uc R K : Subgroup Mb} (hzZ : z ∈ centerOf (perfectCore N)) (hV4T : V4 ≤ T)
    (hV4ab : ∀ a ∈ V4, ∀ c ∈ V4, a * c = c * a) (hV4sq : ∀ a ∈ V4, a ^ 2 = 1)
    (hV4eq : V4 = centerOf (pCoreOf 2 N'))
    (hV4u : ∀ E : Subgroup Mb, E ≤ T → (∀ a ∈ E, ∀ c ∈ E, a * c = c * a) →
      (∀ a ∈ E, a ^ 2 = 1) → Nat.card E = Nat.card V4 → E = V4)
    (hzV4 : z ∈ V4) (htV4 : t ∈ V4) (hnc : ¬ IsConj z t)
    (Lie : UnLoc442Lie T z t V Uc R K) :
    ¬ IsConj (amalgamMap b b' z) (amalgamMap b b' t) ∧
      Subgroup.centralizer ({amalgamMap b b' z} : Set G) ≤ M ∧
      Subgroup.centralizer ({amalgamMap b b' t} : Set G) ≤ M' := by
  have hI' : ∀ i ∈ I, i = z ∨ i = t := by
    intro i hi
    rw [hI] at hi
    simpa using hi
  have ht : t ∈ I := by
    rw [hI]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hzT : z ∈ T := LK.mem_T z LK.z_mem
  have htT : t ∈ T := LK.mem_T t ht
  have hzN : z ∈ N := LK.T_le₁ hzT
  have htN : t ∈ N := LK.T_le₁ htT
  have hz' : amalgamMap b b' z = b ⟨z, hzN⟩ := amalgamMap_of_mem₁ b b' hzN
  have ht' : amalgamMap b b' t = b ⟨t, htN⟩ := amalgamMap_of_mem₁ b b' htN
  have hz2 : orderOf z = 2 := LK.order_two z LK.z_mem
  have hcentb : Subgroup.centralizer ({amalgamMap b b' z} : Set G) ≤ M := by
    rw [hz']
    exact S.cent _ (map_mem_centerOf_perfectCore S.comp.inj₁ S.range hzN hzZ)
      ((orderOf_img S.comp.inj₁ hzN).trans hz2)
  have hnf : ¬ IsConj (b ⟨z, hzN⟩) (b ⟨t, htN⟩) :=
    S.not_isConj_zt hzN htN LK.sylow LK.T_le₁ LK.T_le₂ hzT hz2 hzZ
      (fun w hw hc hw1 => by
        obtain ⟨m, hm, h⟩ := LK.center_T w hw hc hw1
        exact ⟨m, hm.1, h⟩) hV4T hV4ab hV4sq hV4eq hV4u hzV4 htV4 hnc
  have hnf' : ¬ IsConj (amalgamMap b b' z) (amalgamMap b b' t) := by
    rw [hz', ht']
    exact hnf
  refine ⟨hnf', hcentb, ?_⟩
  have hb : Subgroup.centralizer ({amalgamMap b b' z} : Set G) ≤ b.range := S.range ▸ hcentb
  have h := loc442U LK S.comp hI' ht hzt cz ct hSylt hb hnf' Lie
  rwa [S.range'] at h

end Core

end CFSG.Quasithin.H13.F431.Un
