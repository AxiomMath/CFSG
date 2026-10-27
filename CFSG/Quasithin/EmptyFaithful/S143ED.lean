module

public import CFSG.Quasithin.EmptyFaithful.S143EC
public import CFSG.Quasithin.EmptyFaithful.S143Invol
public import CFSG.Quasithin.EmptyFaithful.S143EA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

section Tilde

variable (h : Hyp1281Two G T M (yOfL22 T M))

include h

theorem tilde_isMulCommutative :
    IsMulCommutative ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨x, hxU, hxa⟩ := mem_secImg.1 a.2
  obtain ⟨y, hyU, hyb⟩ := mem_secImg.1 b.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hxa, ← hyb, ← map_mul, ← map_mul, secMk_eq_secMk_iff]
  have := h.commutator_mem_omegaOneCenter (x := (y : G)⁻¹) (y := (x : G)⁻¹)
    (Subgroup.inv_mem _ hyU) (Subgroup.inv_mem _ hxU)
  simpa [mul_assoc] using this

theorem tilde_mul_self (w : ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) : w * w = 1 := by
  obtain ⟨x, hxU, hxw⟩ := mem_secImg.1 w.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_one]
  rw [← hxw, ← map_mul, secMk_eq_one_iff]
  have := h.sq_mem_omegaOneCenter hxU
  rwa [sq] at this

end Tilde

theorem Counter.goodElt {g : G} (c : Counter T M g) : GoodElt128 T (yOfL22 T M) g :=
  ⟨c.g_mem, by rw [normalizer_Z_eq_centralizer_of_hyp c.h1281]; exact c.g_nmem⟩

theorem E_eq_VZ {g : G} (c : Counter T M g) :
    Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g = VZ T M := by
  have h := c.h1281
  have hU := c.nonab
  have hg := c.goodElt
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := c.c15.orth
  have hHN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    h.uOfL22_le_g1.trans hHN
  have hEW : Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g ≤ Hyp1281Two.wOfU T M :=
    inf_le_left
  have hEU : Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g ≤ uOfL22 T M :=
    hEW.trans (Hyp1281Two.wOfU_le_uOfL22 T M)
  have hZE := h.omegaOneCenter_le_inf_rconj hU hg
  have hE2 : ∀ e ∈ Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g, e ^ 2 = 1 :=
    fun e he => c.c15.eSing g c.g_mem c.g_nmem e he
  have hle := card_le_of_invariant hHN hHU hUN hEU hZE (tilde_isMulCommutative h)
    (tilde_mul_self h) q hq1 hq2 hq3 hq4 hq5 hq6 (sylow_G1_of_hyp h)
    (T_le_normalizer_E h hU hg) hE2
  rw [h.card_omegaOneCenter] at hle
  have hVE : VZ T M ≤ Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g := by
    rw [h.wOfU_inf_rconj_eq hU hg]
    exact h.VZ_le_inf_rconj hU hg
  exact (Subgroup.eq_of_le_of_card_ge hVE (by rw [h.rank_two]; exact hle)).symm


section Orders

variable {g : G} (c : Counter T M g)

include c

theorem uOfL22_le_qOf : uOfL22 T M ≤ qOf T :=
  le_pCoreOf_of_le_normalizer 2 c.h1281.uOfL22_le_g1 c.h1281.g1_le_normalizer_uOfL22
    (c.h1281.sylow.1.to_le (uOfL22_le_T_of_hyp c.h1281))

theorem centralizerMod_eq_qOf :
    centralizerMod (quasithinOmegaOneCenter T) (mcOf T) (uOfL22 T M) = qOf T :=
  c.h1281.lemma_12_8_4_four c.h1281.isHz_centralizer

theorem qOf_inf_rconj :
    qOf T ⊓ rconj (Hyp1281Two.wOfU T M) g = VZ T M := by
  have h := c.h1281
  have hU := c.nonab
  have hg := c.goodElt
  have hEV := E_eq_VZ c
  apply le_antisymm
  · rintro y ⟨hyQ, hyX⟩
    have hyc : y ∈ centralizerMod (quasithinOmegaOneCenter T) (mcOf T) (uOfL22 T M) := by
      rw [centralizerMod_eq_qOf c]; exact hyQ
    have hyX' : y ∈ centralizerMod (quasithinOmegaOneCenter T) (rconj (Hyp1281Two.wOfU T M) g)
        (uOfL22 T M) := ⟨hyX, hyc.2.1, hyc.2.2⟩
    rw [(h.lemma_12_8_9_five hU hg).2, hEV] at hyX'
    exact hyX'
  · intro v hv
    have hvE : v ∈ Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g := hEV ▸ hv
    exact ⟨uOfL22_le_qOf c (Hyp1281Two.VZ_le_uOfL22 T M hv), hvE.2⟩

theorem rOf_eq_pCoreOf_sup :
    rOf T M = pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M) := by
  unfold rOf; rw [iTwo_eq c.h1281 c.nonab]

theorem card_rOf : Nat.card (rOf T M) = 64 := by
  have h := c.h1281
  have hU := c.nonab
  have hg := c.goodElt
  have hEV := E_eq_VZ c
  have hWX : Hyp1281Two.wOfU T M ≤
      Subgroup.normalizer (rconj (Hyp1281Two.wOfU T M) g : Set G) :=
    (h.wOfU_le_pCoreOf hU hg).trans (h.pCoreOf_sup_uOfL22_le_normalizer_X hU hg)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hWX
  rw [sup_comm, ← (h.pCoreOf_sup_uOfL22_eq_wOfU_sup hU hg).1, inf_comm, hEV, h.rank_two,
    card_rconj_eq] at hprod
  have hW : Nat.card (Hyp1281Two.wOfU T M) = 16 := card_wOf c
  rw [hW] at hprod
  rw [rOf_eq_pCoreOf_sup c]
  omega

theorem rOf_inf_qOf : rOf T M ⊓ qOf T = Hyp1281Two.wOfU T M := by
  have h := c.h1281
  have hU := c.nonab
  have hg := c.goodElt
  apply le_antisymm
  · rintro s ⟨hsS, hsQ⟩
    rw [rOf_eq_pCoreOf_sup c] at hsS
    obtain ⟨w, hw, x, hx, rfl⟩ := h.exists_mul_of_mem_pCoreOf_sup hU hg hsS
    have hwQ : w ∈ qOf T := uOfL22_le_qOf c (Hyp1281Two.wOfU_le_uOfL22 T M hw)
    have hxQ : x ∈ qOf T := by
      have := (qOf T).mul_mem ((qOf T).inv_mem hwQ) hsQ
      simpa using this
    have hxV : x ∈ VZ T M := (qOf_inf_rconj c) ▸ ⟨hxQ, hx⟩
    exact (Hyp1281Two.wOfU T M).mul_mem hw (h.VZ_le_wOfU hxV)
  · refine le_inf ?_ (uOfL22_le_qOf c |> fun h1 => (Hyp1281Two.wOfU_le_uOfL22 T M).trans h1)
    rw [rOf_eq_pCoreOf_sup c]
    exact h.wOfU_le_pCoreOf hU hg

end Orders

end S143

end CFSG.Quasithin
