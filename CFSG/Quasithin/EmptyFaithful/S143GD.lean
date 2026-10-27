module

public import CFSG.Quasithin.EmptyFaithful.S143EH
public import CFSG.Quasithin.EmptyFaithful.S143FK
public import CFSG.Quasithin.EmptyFaithful.S143GB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section KStructure

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.centralizer_inf_rOf_Ac {t : G} (htT : t ∈ T) (htRQ : t ∉ rOf T M ⊔ qOf T) :
    Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ⊓ rOf T M = c.Ac hrW hrV hr2 := by
  apply le_antisymm
  · rintro x ⟨hxC, hxR⟩
    have hAiTwo : c.Ac hrW hrV hr2 ≤ iTwo T M := (c.Ac_le_rOf hrW hrV hr2).trans
      (pCoreOf_le 2 (iTwo T M))
    have hAN : c.Ac hrW hrV hr2 ≤
        Subgroup.normalizer (conjSubgroup (c.Ac hrW hrV hr2) t : Set G) := fun γ hγ => by
      refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
      · exact c.conjAc_conj_mem hrW hrV hr2 htT (hAiTwo hγ) hy
      · have := c.conjAc_conj_mem hrW hrV hr2 htT ((iTwo T M).inv_mem (hAiTwo hγ)) hy
        simpa using this
    have hxR' : x ∈ rOf T M := hxR
    rw [← c.Ac_sup_conj hrW hrV hr2 htT htRQ, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hxR'
    obtain ⟨a, ha, a', ha', hxa⟩ := Set.mem_mul.mp hxR'
    subst hxa
    by_cases ha'V : a' ∈ VZ T M
    · exact (c.Ac hrW hrV hr2).mul_mem ha (c.VZ_le_Ac hrW hrV hr2 ha'V)
    · exfalso
      apply c.comm_r_ne_one_of_mem_conj hrW hrV hr2 htT htRQ ha' ha'V
      have haA : a ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
        exact mul_comm_of_sq_eq_one (fun z hz => c.sq_Ac hrW hrV hr2 hz) hy ha
      have ha'C : a' ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) := by
        have := (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).mul_mem
          ((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).inv_mem haA) hxC
        simpa using this
      have h1 : r * a' = a' * r := Subgroup.mem_centralizer_iff.mp ha'C r
        (c.r_mem_Ac hrW hrV hr2)
      calc r * a' * r⁻¹ * a'⁻¹ = (a' * r) * r⁻¹ * a'⁻¹ := by rw [h1]
        _ = 1 := by group
  · intro x hx
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => ?_, c.Ac_le_rOf hrW hrV hr2 hx⟩
    exact mul_comm_of_sq_eq_one (fun z hz => c.sq_Ac hrW hrV hr2 hz) hy hx

omit c hrW hrV hr2 [Finite G] in
theorem oTwoUpper_kOf (A : Subgroup G) : oTwoUpper (kOf T M A) = kOf T M A := by
  apply le_antisymm (oTwoUpper_le _)
  refine sup_le ?_ ?_
  · calc oTwoUpper (mcOf T ⊓ Subgroup.normalizer (A : Set G))
        = oTwoUpper (oTwoUpper (mcOf T ⊓ Subgroup.normalizer (A : Set G))) :=
          (A4.oTwoUpper_oTwoUpper _).symm
      _ ≤ oTwoUpper (kOf T M A) := oTwoUpper_mono le_sup_left
  · calc yOfL22 T M = oTwoUpper (yOfL22 T M) := (oTwoUpper_yOfL22 T M).symm
      _ ≤ oTwoUpper (kOf T M A) := oTwoUpper_mono le_sup_right

theorem Counter.kOf_le_normalizer_Ac :
    kOf T M (c.Ac hrW hrV hr2) ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := by
  refine sup_le ((oTwoUpper_le _).trans inf_le_right) ?_
  have hLI : yOfL22 T M ≤ iTwo T M := by
    rw [iTwo_eq c.h1281 c.nonab]; exact le_sup_left
  exact hLI.trans (c.iTwo_le_normalizer_Ac hrW hrV hr2)

theorem Counter.uOfL22_le_oTwoUpper_inf_normalizer_Ac :
    uOfL22 T M ≤ oTwoUpper (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) := by
  have h := c.h1281
  have hUN := c.hUN
  have hHN := hHN_of T
  have hHU := c.hHU
  have hαT := c.alphaOf_mem_T hrW hrV hr2
  have hα1 := c.alphaOf_ne_one hrW hrV hr2
  have hα2 := c.alphaOf_sq hrW hrV hr2
  have hαx := c.alphaOf_tclsE hrW hrV hr2
  set Y := oTwoUpper (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) with hY
  have hUA : uOfL22 T M ≤ mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := fun u hu =>
    ⟨h.uOfL22_le_g1 hu,
      c.normal_Ac hrW hrV hr2 (Subgroup.mem_sup_right (uOfL22_le_qOf c hu))⟩
  obtain ⟨y₀, hy₀C, hy₀3, hffp⟩ := c.exists_ffp_centralizer hrW hrV hr2 hαT hα1 hα2 hαx
  obtain ⟨ω, hωodd, hω⟩ := exists_odd_lift c.actK hy₀C.2 (by rw [hy₀3]; decide)
  have hωN : (ω : G) ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    (c.mem_normalizer_Ac_iff hrW hrV hr2 ω).mpr
      (by rw [hω]; exact Subgroup.mem_centralizer_singleton_iff.mp hy₀C.1)
  have hωY : (ω : G) ∈ Y :=
    mem_oTwoUpper_of_odd ⟨ω.2, hωN⟩ (by rw [Subgroup.orderOf_coe]; exact hωodd)
  have hdec : ∀ u ∈ uOfL22 T M, ∃ k ∈ Y, ∃ z ∈ quasithinOmegaOneCenter T, u = k * z := by
    intro u hu
    let _ : CommGroup (UT T M) := c.tildeCommGroup
    obtain ⟨b, hb⟩ := exists_mul_inv_apply_eq (c.actK ω)
      (fun w hw => hffp w (by rw [← hω]; exact hw)) (tclsE hUN hu)
    obtain ⟨xs, hxU', hxb⟩ := mem_secImg.1 b.2
    set x : G := (xs : G) with hxdef
    have hxU : x ∈ uOfL22 T M := hxU'
    have hbx : b = tclsE hUN hxU := Subtype.ext (hxb.symm.trans (tclsE_val hUN hxU).symm)
    have hωx : (ω : G) * x * (ω : G)⁻¹ ∈ uOfL22 T M :=
      (Subgroup.mem_normalizer_iff.mp (hHU ω.2) x).mp hxU
    have hρb : c.actK ω b = tclsE hUN hωx := by
      rw [hbx]; exact actTilde_tclsE hUN hHN hHU ω hxU hωx
    set x₁ : ↥(uOfL22 T M) := ⟨x, hxU⟩ with hx₁
    set x₂ : ↥(uOfL22 T M) := ⟨(ω : G) * x * (ω : G)⁻¹, hωx⟩ with hx₂
    have hψ : tclsHom hUN (x₁ * x₂⁻¹) = tclsE hUN hu := by
      rw [map_mul, map_inv]
      have e1 : tclsHom hUN x₁ = b := by rw [hbx]; rfl
      have e2 : tclsHom hUN x₂ = c.actK ω b := by rw [hρb]; rfl
      rw [e1, e2, hb]
    have hz := (tclsE_eq_iff hUN (x₁ * x₂⁻¹).2 hu).mp hψ
    have hk0 : ((x₁ * x₂⁻¹ : ↥(uOfL22 T M)) : G) = (x * (ω : G) * x⁻¹) * (ω : G)⁻¹ := by
      show x * ((ω : G) * x * (ω : G)⁻¹)⁻¹ = x * (ω : G) * x⁻¹ * (ω : G)⁻¹
      group
    have hkY : ((x₁ * x₂⁻¹ : ↥(uOfL22 T M)) : G) ∈ Y := by
      rw [hk0]
      exact Y.mul_mem (conj_mem_oTwoUpper (Subgroup.le_normalizer (hUA hxU)) hωY)
        (Y.inv_mem hωY)
    refine ⟨((x₁ * x₂⁻¹ : ↥(uOfL22 T M)) : G), hkY, _, hz, ?_⟩
    group
  have hZY : quasithinOmegaOneCenter T ≤ Y := by
    have hU := c.nonab
    obtain ⟨a, b, hab⟩ : ∃ a b : ↥(uOfL22 T M), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact hU ⟨⟨fun a b => hcon a b⟩⟩
    obtain ⟨k₁, hk₁, z₁, hz₁, he₁⟩ := hdec a a.2
    have hz₁c : ∀ y ∈ uOfL22 T M, z₁ * y = y * z₁ := fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 hz₁).2 y hy).symm
    have hcomm : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ Y := by
      have e : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ = k₁ * ((b : G) * k₁⁻¹ * (b : G)⁻¹) := by
        have hzb := hz₁c (b : G) b.2
        rw [he₁]
        calc k₁ * z₁ * (b : G) * (k₁ * z₁)⁻¹ * (b : G)⁻¹
            = k₁ * (z₁ * (b : G)) * z₁⁻¹ * k₁⁻¹ * (b : G)⁻¹ := by group
          _ = k₁ * ((b : G) * z₁) * z₁⁻¹ * k₁⁻¹ * (b : G)⁻¹ := by rw [hzb]
          _ = k₁ * ((b : G) * k₁⁻¹ * (b : G)⁻¹) := by group
      rw [e]
      exact Y.mul_mem hk₁
        (conj_mem_oTwoUpper (Subgroup.le_normalizer (hUA b.2)) (Y.inv_mem hk₁))
    have hZ : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ quasithinOmegaOneCenter T :=
      h.commutator_mem_omegaOneCenter a.2 b.2
    have hne : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ≠ 1 := by
      intro he
      apply hab
      apply Subtype.ext
      have h1 : (a : G) * (b : G) * (a : G)⁻¹ = (b : G) := mul_inv_eq_one.mp he
      have h2 : (a : G) * (b : G) = (b : G) * (a : G) := by
        calc (a : G) * (b : G) = ((a : G) * (b : G) * (a : G)⁻¹) * (a : G) := by group
          _ = (b : G) * (a : G) := by rw [h1]
      simpa using h2
    intro z hz
    obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : ↥(quasithinOmegaOneCenter T))).mp
      h.card_omegaOneCenter
    have h1 : (⟨_, hZ⟩ : ↥(quasithinOmegaOneCenter T)) ≠ 1 := fun he =>
      hne (congrArg Subtype.val he)
    have hz' : z = 1 ∨ z = (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ := by
      by_cases hz1 : (⟨z, hz⟩ : ↥(quasithinOmegaOneCenter T)) = 1
      · exact Or.inl (congrArg Subtype.val hz1)
      · exact Or.inr (congrArg Subtype.val ((hw _ hz1).trans (hw _ h1).symm))
    rcases hz' with rfl | rfl
    · exact Y.one_mem
    · exact hcomm
  intro u hu
  obtain ⟨k, hk, z, hz, rfl⟩ := hdec u hu
  exact Y.mul_mem hk (hZY hz)

theorem Counter.rOf_sup_uOfL22_le_kOf :
    rOf T M ⊔ uOfL22 T M ≤ kOf T M (c.Ac hrW hrV hr2) := by
  refine sup_le ?_ ?_
  · rw [(lemma_14_3_18_a G T M g c).r_eq]
    exact (pCoreOf_le 2 (yOfL22 T M)).trans le_sup_right
  · exact (c.uOfL22_le_oTwoUpper_inf_normalizer_Ac hrW hrV hr2).trans le_sup_left

end KStructure

end S143

end CFSG.Quasithin
