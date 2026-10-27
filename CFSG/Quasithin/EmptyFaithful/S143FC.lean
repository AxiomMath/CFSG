module

public import CFSG.Quasithin.EmptyFaithful.S143FB
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabNatural

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section CounterA

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.quotSetting :
    QuotSetting (yOfL22 T M ⊔ uOfL22 T M) (pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M))
      (Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g) :=
  c.h1281.quotSetting c.nonab c.goodElt

theorem Counter.VZ_sq {e : G} (he : e ∈ VZ T M) : e * e = 1 := by
  have := c.h1281.almostSpecialHyp_g1.sq_eq_one_of_mem_V he
  simpa [sq] using this

theorem Counter.rOf_comm_VZ {s e : G} (hs : s ∈ rOf T M) (he : e ∈ VZ T M) : e * s = s * e := by
  have hs' : s ∈ pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M) := by
    rw [← rOf_eq_pCoreOf_sup c]; exact hs
  rw [c.h1281.pCoreOf_sup_uOfL22_eq c.nonab c.goodElt] at hs'
  exact Subgroup.mem_centralizer_iff.mp hs'.2 e he

theorem Counter.kdata {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M)
    (hr2 : r * r = 1) : KData c.quotSetting g r := by
  obtain ⟨u, huU, huW⟩ := exists_mem_U_not_mem_W c.h1281 c.nonab
  have hmod := c.h1281.module_relations c.nonab c.goodElt huU huW
  have hEV := E_eq_VZ c
  exact
    { g_mem := c.goodElt.mem_sup _
      g3 := c.h1281.mul_mul_mem_pCoreOf_sup c.nonab c.goodElt
      fix := hmod.2.2.2
      r_mem := c.h1281.wOfU_le_pCoreOf c.nonab c.goodElt hrW
      r_sq := hr2
      r_nE := fun hE => hrV (hEV ▸ hE)
      norm := hmod.1 r hrW }

theorem Counter.gen {u : G} (huU : u ∈ uOfL22 T M) (huW : u ∉ Hyp1281Two.wOfU T M) :
    ∀ γ ∈ yOfL22 T M ⊔ uOfL22 T M, ∃ w : G,
      (w = 1 ∨ w = u ∨ w = g ∨ w = g * g ∨ w = u * g ∨ w = u * (g * g)) ∧
        γ * w⁻¹ ∈ pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M) := by
  have h := c.h1281
  have hU := c.nonab
  have hg := c.goodElt
  have huI : u ∈ yOfL22 T M ⊔ uOfL22 T M := Subgroup.mem_sup_right huU
  have hgI : g ∈ yOfL22 T M ⊔ uOfL22 T M := hg.mem_sup _
  have ha2 : phiI h ⟨u, huI⟩ ^ 2 = 1 := by
    rw [← map_pow, phiI_eq_one_iff]
    exact h.sq_mem_pCoreOf_LT huU
  have ha1 : phiI h ⟨u, huI⟩ ≠ 1 := fun he => h.not_mem_pCoreOf_LT_of_not_mem_W huU huW
    ((phiI_eq_one_iff h ⟨u, huI⟩).mp he)
  have hb3 : phiI h ⟨g, hgI⟩ ^ 3 = 1 := by
    rw [← map_pow, phiI_eq_one_iff]
    exact h.pow_three_mem_pCoreOf_LT hg.mem
  have hb1 : phiI h ⟨g, hgI⟩ ≠ 1 := fun he => h.not_mem_pCoreOf_LT_of_goodElt hg
    ((phiI_eq_one_iff h ⟨g, hgI⟩).mp he)
  have hker := ker_phiI h hU hg
  intro γ hγ
  have key : ∀ (w : G) (hw : w ∈ yOfL22 T M ⊔ uOfL22 T M),
      phiI h ⟨γ, hγ⟩ = phiI h ⟨w, hw⟩ → γ * w⁻¹ ∈ pCoreOf 2 (yOfL22 T M ⊔ uOfL22 T M) := by
    intro w hw hphi
    have h1 : phiI h (⟨γ, hγ⟩ * ⟨w, hw⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, hphi, mul_inv_cancel]
    have h2 : (⟨γ, hγ⟩ * ⟨w, hw⟩⁻¹ : ↥(yOfL22 T M ⊔ uOfL22 T M)) ∈
        CFSG.Open.pCore 2 ↥(yOfL22 T M ⊔ uOfL22 T M) := hker ▸ h1
    exact (mem_pCore_iff _).mp h2
  rcases perm3_words _ _ ha2 ha1 hb3 hb1 (phiI h ⟨γ, hγ⟩) with hx | hx | hx | hx | hx | hx
  · exact ⟨1, Or.inl rfl, key 1 (Subgroup.one_mem _) (by rw [hx]; exact (map_one _).symm)⟩
  · exact ⟨u, Or.inr (Or.inl rfl), key u huI hx⟩
  · exact ⟨g, Or.inr (Or.inr (Or.inl rfl)), key g hgI hx⟩
  · refine ⟨g * g, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
      key (g * g) (Subgroup.mul_mem _ hgI hgI) ?_⟩
    rw [hx]
    exact (map_mul (phiI h) ⟨g, hgI⟩ ⟨g, hgI⟩).symm
  · refine ⟨u * g, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      key (u * g) (Subgroup.mul_mem _ huI hgI) ?_⟩
    rw [hx]
    exact (map_mul (phiI h) ⟨u, huI⟩ ⟨g, hgI⟩).symm
  · refine ⟨u * (g * g), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
      key (u * (g * g)) (Subgroup.mul_mem _ huI (Subgroup.mul_mem _ hgI hgI)) ?_⟩
    rw [hx]
    have : (⟨u * (g * g), Subgroup.mul_mem _ huI (Subgroup.mul_mem _ hgI hgI)⟩ :
        ↥(yOfL22 T M ⊔ uOfL22 T M)) = ⟨u, huI⟩ * (⟨g, hgI⟩ * ⟨g, hgI⟩) := rfl
    rw [this, map_mul, map_mul]

theorem Counter.udata {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M)
    (hr2 : r * r = 1) {u : G} (huU : u ∈ uOfL22 T M) (huW : u ∉ Hyp1281Two.wOfU T M) :
    KData.UData (c.kdata hrW hrV hr2) u where
  u_mem := Subgroup.mem_sup_right huU
  u_r := by
    have h1 := c.h1281.commutator_mem_omegaOneCenter (x := u) (y := r⁻¹) huU
      ((uOfL22 T M).inv_mem hrW.1)
    have e : (u * r * u⁻¹)⁻¹ * r = u * r⁻¹ * u⁻¹ * r⁻¹⁻¹ := by group
    rw [e, E_eq_VZ c]
    exact Hyp1281Two.omegaOneCenter_le_VZ T M h1
  u_g := c.h1281.mul_mul_inv_mul_mem_pCoreOf_sup c.nonab c.goodElt huU huW
  gen := c.gen huU huW

noncomputable def Counter.Ac {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M)
    (hr2 : r * r = 1) : Subgroup G :=
  @KData.A G _ _ _ _ c.quotSetting g r c.quotSetting.normal (c.kdata hrW hrV hr2)

variable {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include hrW hrV hr2

theorem Counter.Ac_le_rOf : c.Ac hrW hrV hr2 ≤ rOf T M := by
  have := c.quotSetting.normal
  exact (c.kdata hrW hrV hr2).A_le_S.trans (le_of_eq (rOf_eq_pCoreOf_sup c).symm)

theorem Counter.VZ_le_Ac : VZ T M ≤ c.Ac hrW hrV hr2 := by
  have := c.quotSetting.normal
  exact (le_of_eq (E_eq_VZ c).symm).trans (c.kdata hrW hrV hr2).E_le_A

theorem Counter.card_Ac : Nat.card (c.Ac hrW hrV hr2) = 16 := by
  have := c.quotSetting.normal
  refine (c.kdata hrW hrV hr2).card_A ?_
  rw [E_eq_VZ c]
  exact c.h1281.rank_two

theorem Counter.sq_Ac {x : G} (hx : x ∈ c.Ac hrW hrV hr2) : x * x = 1 := by
  have := c.quotSetting.normal
  refine (c.kdata hrW hrV hr2).sq_of_mem_A ?_ ?_ hx
  · intro e he s hs
    rw [E_eq_VZ c] at he
    exact c.rOf_comm_VZ (by rw [rOf_eq_pCoreOf_sup c]; exact hs) he
  · intro e he
    rw [E_eq_VZ c] at he
    exact c.VZ_sq he

theorem Counter.mem_Ac_cases {x : G} (hx : x ∈ c.Ac hrW hrV hr2) :
    ∃ e ∈ VZ T M, x = e ∨ x = r * e ∨ x = g * r * g⁻¹ * e ∨ x = g * g * r * (g * g)⁻¹ * e := by
  have := c.quotSetting.normal
  obtain ⟨e, he, hcases⟩ := (c.kdata hrW hrV hr2).mem_A_cases hx
  exact ⟨e, E_eq_VZ c ▸ he, hcases⟩

theorem Counter.r_mem_Ac : r ∈ c.Ac hrW hrV hr2 := by
  have := c.quotSetting.normal
  exact (c.kdata hrW hrV hr2).r_mem_A

theorem Counter.r1_mem_Ac : g * r * g⁻¹ ∈ c.Ac hrW hrV hr2 := by
  have := c.quotSetting.normal
  exact (c.kdata hrW hrV hr2).r1_mem_A

theorem Counter.r2_mem_Ac : g * g * r * (g * g)⁻¹ ∈ c.Ac hrW hrV hr2 := by
  have := c.quotSetting.normal
  exact (c.kdata hrW hrV hr2).r2_mem_A

theorem Counter.Ac_conj_mem {γ x : G} (hγ : γ ∈ iTwo T M) (hx : x ∈ c.Ac hrW hrV hr2) :
    γ * x * γ⁻¹ ∈ c.Ac hrW hrV hr2 := by
  have := c.quotSetting.normal
  obtain ⟨u, huU, huW⟩ := exists_mem_U_not_mem_W c.h1281 c.nonab
  rw [iTwo_eq c.h1281 c.nonab] at hγ
  exact (c.kdata hrW hrV hr2).conj_mem_A (c.udata hrW hrV hr2 huU huW) hγ hx

end CounterA

end S143

end CFSG.Quasithin
