module

public import CFSG.Quasithin.EmptyFaithful.S1422Inputs
public import CFSG.Quasithin.EmptyFaithful.S1422Extra
public import CFSG.Quasithin.Recognition.U33Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

section U33Bridge

variable {G : Type} [Group G]

theorem isSymThreeQuotient_pCoreOf {C : Subgroup G}
    (h : Nonempty (oTwoQuot ↥C ≃* Equiv.Perm (Fin 3))) :
    IsSymThreeQuotient ((pCoreOf 2 C).subgroupOf C) := by
  obtain ⟨e⟩ := h
  have hN : (pCoreOf 2 C).subgroupOf C = CFSG.Open.pCore 2 ↥C :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  rw [hN]
  exact isSymThreeQuotient_of_mulEquiv e

private theorem zpow_sq_eq_one_cases {z : G} (hz2 : z ^ 2 = 1) (k : ℤ) :
    z ^ k = 1 ∨ z ^ k = z := by
  have h2 : z ^ (2 : ℤ) = 1 := by exact_mod_cast hz2
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem not_isWeaklyClosedIn_zpowers_of_moved {z : G} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    {Q : Subgroup G} (h : ∃ g : G, g * z * g⁻¹ ≠ z ∧ g * z * g⁻¹ ∈ Q) :
    ¬ IsWeaklyClosedIn (Subgroup.zpowers z) Q := by
  intro hwc
  obtain ⟨g, hg1, hg2⟩ := h
  have hle : conjSubgroup (Subgroup.zpowers z) g⁻¹ ≤ Q := by
    intro x hx
    rw [mem_conjSubgroup_iff, inv_inv] at hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hxk : x = (g * z * g⁻¹) ^ k := by
      rw [conj_zpow, hk]
      group
    rw [hxk]
    exact Subgroup.zpow_mem _ hg2 k
  have hmem : g * z * g⁻¹ ∈ Subgroup.zpowers z := by
    have : g * z * g⁻¹ ∈ conjSubgroup (Subgroup.zpowers z) g⁻¹ := by
      rw [mem_conjSubgroup_iff, inv_inv]
      have : g⁻¹ * (g * z * g⁻¹) * g = z := by group
      rw [this]
      exact Subgroup.mem_zpowers z
    rwa [hwc g⁻¹ hle] at this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rcases zpow_sq_eq_one_cases hz2 k with h | h
  · apply hz1
    have h1 : g * z * g⁻¹ = 1 := by rw [← hk, h]
    have := congrArg (fun x => g⁻¹ * x * g) h1
    simpa [mul_assoc] using this
  · exact hg1 (hk.symm.trans h)

end U33Bridge

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

theorem exists_z (S : Setting1422 T M Y H) :
    ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧ z ^ 2 = 1 ∧
      ∀ w ∈ quasithinOmegaOneCenter T, w = 1 ∨ w = z := by
  obtain ⟨x, hx⟩ := (Nat.card_eq_two_iff' (1 : ↥(quasithinOmegaOneCenter T))).mp
    S.hyp.card_omegaOneCenter
  refine ⟨x, x.2, fun h => hx.1 (Subtype.ext h), sq_eq_one_of_mem_omegaOneCenter T x.2, ?_⟩
  intro w hw
  by_cases h1 : w = 1
  · exact Or.inl h1
  · right
    exact congrArg Subtype.val (hx.2 ⟨w, hw⟩ (fun h => h1 (congrArg Subtype.val h)))

omit [Finite G] in
theorem centralizer_singleton_eq {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hZ : ∀ w ∈ quasithinOmegaOneCenter T, w = 1 ∨ w = z) :
    Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro w hw
    rcases hZ w hw with h | h
    · rw [h]; simp
    · rw [h]; exact hx z rfl
  · exact Subgroup.centralizer_le (by simpa using hz)

theorem M_eq_YT (hSz : Nat.card ↥(Sz 0) = 20) (S : Setting1422 T M Y H)
    (hHc : H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) : M = Y ⊔ T := by
  apply le_antisymm _ S.YT_le_M
  refine S.data.generate.trans (sup_le le_rfl ?_)
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le (le_conjClosure (quasithinOmegaOneCenter T) M) hx.2
  have hxH : x ∈ H := hHc ▸ hxC
  have : x ∈ H ⊓ M := ⟨hxH, hx.1⟩
  rw [S.H_inf_M hSz] at this
  exact T_le_YT this

theorem exists_moved (S : Setting1422 T M Y H) (hV : VZ T M ≤ pCoreOf 2 H) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T)
    (hZ : ∀ w ∈ quasithinOmegaOneCenter T, w = 1 ∨ w = z) :
    ∃ g : G, g * z * g⁻¹ ≠ z ∧ g * z * g⁻¹ ∈ pCoreOf 2 H := by
  by_contra hne
  have hfix : ∀ m ∈ M, m * z * m⁻¹ = z := by
    intro m hm
    by_contra hmz
    exact hne ⟨m, hmz, hV (mem_conjClosure hm hz)⟩
  have hle : VZ T M ≤ quasithinOmegaOneCenter T := by
    refine conjClosure_le fun m hm w hw => ?_
    rcases hZ w hw with h | h
    · rw [h]; simp
    · rw [h, hfix m hm]; exact hz
  have h1 : Nat.card ↥(VZ T M) ≤ Nat.card ↥(quasithinOmegaOneCenter T) :=
    Subgroup.card_le_of_le hle
  rw [S.hyp.rank_two, S.hyp.card_omegaOneCenter] at h1
  omega

theorem mem_H_of_mem_Z (S : Setting1422 T M Y H) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) :
    z ∈ H :=
  S.T_le_H (quasithinOmegaOneCenter_le_center T hz).1

theorem tits_case (hF : F431Statement) (S : Setting1422 T M Y H)
    (hHc : H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hC : CaseTits H (Y ⊔ T)) : Nonempty (G ≃* quasithinTits) := by
  obtain ⟨z, hz, hz1, hz2, hZ⟩ := S.exists_z
  have hCz : Subgroup.centralizer ({z} : Set G) = H := by
    rw [centralizer_singleton_eq hz hZ, hHc]
  exact hF.1 G S.hyp.simple H (Y ⊔ T) z hC.1 hC.2.1 (S.mem_H_of_mem_Z hz) hz1 hz2 hCz.ge hCz.le

theorem twoF4_case (hF : F431Statement) (hNS : ModelNotSimple) (S : Setting1422 T M Y H)
    (hHc : H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hC : Case2F4 H (Y ⊔ T)) : False := by
  obtain ⟨z, hz, hz1, hz2, hZ⟩ := S.exists_z
  have hCz : Subgroup.centralizer ({z} : Set G) = H := by
    rw [centralizer_singleton_eq hz hZ, hHc]
  obtain ⟨e⟩ := hF.2.1 G S.hyp.simple H (Y ⊔ T) z hC.1 hC.2.1 (S.mem_H_of_mem_Z hz) hz1 hz2
    hCz.ge hCz.le
  exact hNS.1 (e.isSimpleGroup_congr.mp S.hyp.simple)

theorem g2_case (hF : F431Statement) (hNS : ModelNotSimple) (S : Setting1422 T M Y H)
    (hHc : H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hC : CaseG2 H (Y ⊔ T)) : False := by
  obtain ⟨z, hz, hz1, hz2, hZ⟩ := S.exists_z
  have hCz : Subgroup.centralizer ({z} : Set G) = H := by
    rw [centralizer_singleton_eq hz hZ, hHc]
  obtain ⟨e⟩ := hF.2.2 G S.hyp.simple H (Y ⊔ T) z hC.1 hC.2.1 hC.2.2.2.1 (S.mem_H_of_mem_Z hz) hz1
    hz2 hCz.ge hCz.le
  exact hNS.2 (e.isSimpleGroup_congr.mp S.hyp.simple)

theorem g22p_case (hSz : Nat.card ↥(Sz 0) = 20) (hABG : ABGWreathedRecognition)
    (hAm : G22pAmalgamFacts) (hV : VZ T M ≤ pCoreOf 2 H) (S : Setting1422 T M Y H)
    (hHc : H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hC : CaseG22P H (Y ⊔ T)) : Nonempty (G ≃* PSU3 3 1) := by
  obtain ⟨z, hz, hz1, hz2, hZ⟩ := S.exists_z
  have hCz : Subgroup.centralizer ({z} : Set G) = H := by
    rw [centralizer_singleton_eq hz hZ, hHc]
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hmoved := S.exists_moved hV hz hZ
  obtain ⟨P, hP⟩ := S.exists_sylow
  have hTw : Nonempty ((P : Subgroup G) ≃* WreathedTwoGroup 2) := by
    obtain ⟨e⟩ := hAm G H (Y ⊔ T) hC.1
    exact ⟨(MulEquiv.subgroupCongr (hP.trans (S.H_inf_YT hSz).symm)).trans e⟩
  have hHS := hC.2.1.perm_three
  have hweak := not_isWeaklyClosedIn_zpowers_of_moved hz2 hz1 hmoved
  have := S.hyp.simple
  subst hCz
  exact u33_recognition_of_wreathed_sylow_of_pCore hABG hord S.charTwo_H hC.2.2.2.1
    (isSymThreeQuotient_pCoreOf hHS) hweak P hTw

theorem m12_case (hI46 : CFSG.GH74.M12.S_Asc03_simple) (hM12 : M12AmalgamFacts)
    (hV : VZ T M ≤ pCoreOf 2 H) (S : Setting1422 T M Y H)
    (hHc : H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hC : CaseM12 H (Y ⊔ T)) : Nonempty (G ≃* quasithinM12) := by
  obtain ⟨z, hz, hz1, hz2, hZ⟩ := S.exists_z
  have hCz : Subgroup.centralizer ({z} : Set G) = H := by
    rw [centralizer_singleton_eq hz hZ, hHc]
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hmoved := S.exists_moved hV hz hZ
  subst hCz
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCdef
  obtain ⟨hA, hqH, hQ, hqY, hcard⟩ := hC
  obtain ⟨hmm1, hmm2⟩ := hM12 G C (Y ⊔ T) hA hqH hQ hqY hcard
  have hzcen : z ∈ centerOf (pCoreOf 2 C) := by
    obtain ⟨P, hP⟩ := S.exists_sylow
    exact omegaOneCenter_le_centerOf_pCoreOf C P (hP ▸ S.T_le_H) S.charTwo_H (hP ▸ hz)
  have hzO : z ∈ pCoreOf 2 C := hzcen.1
  have hzC : ∀ y ∈ pCoreOf 2 C, z * y = y * z := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hzcen.2 y hy).symm
  have hQabs : IsQ8Sq ↥(CFSG.pCore 2 ↥C) := hQ.of_mulEquiv (pCoreEquiv C).symm
  have hco := (centerOrderTwo_of_isQ8Sq hQ).of_mulEquiv (pCoreEquiv C).symm
  obtain ⟨w, hw1, hwc, hwu⟩ := hco
  let z' : ↥(CFSG.pCore 2 ↥C) := (pCoreEquiv C).symm ⟨z, hzO⟩
  have hz'coe : (((z' : ↥C)) : G) = z := by
    have := pCoreEquiv_coe C z'
    rw [show pCoreEquiv C z' = ⟨z, hzO⟩ from (pCoreEquiv C).apply_symm_apply _] at this
    exact this.symm
  have hz'c : ∀ y : ↥(CFSG.pCore 2 ↥C), z' * y = y * z' := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    have := hzC (((y : ↥C)) : G) (by rw [← pCoreEquiv_coe C y]; exact (pCoreEquiv C y).2)
    simpa [hz'coe] using this
  have hz'1 : z' ≠ 1 := by
    intro h1
    apply hz1
    rw [← hz'coe, h1]
    rfl
  have hz'w : z' = w := (hwu z' hz'c).resolve_left hz'1
  have hAsc : CFSG.GH74.M12.Asc03Hyp G z :=
    { orderTwo := hord
      card_core := by
        rw [Nat.card_congr (pCoreEquiv C).toEquiv]; exact hQ.1
      extraspecial := isExtraspecial_of_isQ8Sq hQabs
      quotient_S3 := by
        obtain ⟨e⟩ := hqH.perm_three
        exact ⟨(QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥C 2)).trans e⟩
      centralizer_X := by
        intro X q hq hX
        have hqc := hmm1 X q hq hX
        have hqz : (⟨q, hq⟩ : ↥(CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G)))) = 1 ∨
            (⟨q, hq⟩ : ↥(CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G)))) = w :=
          hwu _ (fun y => Subtype.ext (hqc y y.2))
        rcases hqz with h1 | h1
        · have : (q : G) = 1 := by
            have := congrArg (fun u : ↥(CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))) =>
              (((u : ↥(Subgroup.centralizer ({z} : Set G)))) : G)) h1
            simpa using this
          rw [this]; exact Subgroup.one_mem _
        · have : (q : G) = z := by
            have := congrArg (fun u : ↥(CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))) =>
              (((u : ↥(Subgroup.centralizer ({z} : Set G)))) : G)) h1
            rw [← hz'w] at this
            simpa [hz'coe] using this
          rw [this]; exact Subgroup.mem_zpowers z
      not_weakly_closed := by
        obtain ⟨g, hg1, hg2⟩ := hmoved
        refine ⟨g, hg1, ((pCoreEquiv C).symm ⟨_, hg2⟩ : ↥(CFSG.pCore 2 ↥C)).1,
          ((pCoreEquiv C).symm ⟨_, hg2⟩).2, ?_⟩
        have := pCoreEquiv_coe C ((pCoreEquiv C).symm ⟨_, hg2⟩)
        rw [(pCoreEquiv C).apply_symm_apply] at this
        exact this.symm }
  exact hI46 G S.hyp.simple z hAsc hmm2

end Setting1422

end CFSG.Quasithin
