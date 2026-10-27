module

public import CFSG.Quasithin.EmptyFaithful.S143KE
public import CFSG.Quasithin.EmptyFaithful.S143IC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

section Hyp

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.mem_Ac_inf_qOf_of_centralizes {u : G} (hu : u ∈ uOfL22 T M)
    (hcomm : ∀ e ∈ c.Ac hrW hrV hr2 ⊓ qOf T, u * e = e * u) : u ∈ c.Ac hrW hrV hr2 ⊓ qOf T := by
  by_contra hnot
  set E₀ := c.Ac hrW hrV hr2 ⊓ qOf T with hE₀
  have hE₀U : E₀ ≤ uOfL22 T M := c.Ac_inf_qOf_le_uOfL22 hrW hrV hr2
  have hE₀card : Nat.card E₀ = 8 := c.card_inf_qOf_Ac hrW hrV hr2
  have hE₀comm : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := fun a ha b hb =>
    mul_comm_of_sq_eq_one (fun y hy => c.sq_Ac hrW hrV hr2 hy) ha.1 hb.1
  have hfix : ∀ e ∈ E₀, u * e * u⁻¹ = e := fun e he => by
    rw [hcomm e he]; group
  have hunorm : u ∈ Subgroup.normalizer (E₀ : Set G) := by
    refine mem_normalizer_of_conj_mem (fun e he => ?_) (fun e he => ?_)
    · rw [hfix e he]; exact he
    · have : u⁻¹ * e * u = e := by
        calc u⁻¹ * e * u = u⁻¹ * (u * e * u⁻¹) * u := by rw [hfix e he]
          _ = e := by group
      rw [this]; exact he
  set D := E₀ ⊔ Subgroup.zpowers u with hD
  have hDU : D ≤ uOfL22 T M := sup_le hE₀U (Subgroup.zpowers_le.mpr hu)
  have huD : u ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hEleD : E₀ ≤ D := le_sup_left
  have hDcard : 16 ≤ Nat.card D := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hEleD
    have hne : Nat.card D ≠ Nat.card E₀ := by
      intro h
      have := Subgroup.eq_of_le_of_card_ge hEleD (le_of_eq h)
      exact hnot (this ▸ huD)
    have hpos : 0 < Nat.card D := Nat.card_pos
    rw [hE₀card] at hne hk
    rw [hk] at hne hpos ⊢
    have hk1 : k ≠ 1 := fun h => hne (by rw [h])
    have hk0 : k ≠ 0 := fun h => by simp [h] at hpos
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := c.exists_noncomm_of_card_ge hDU hDcard
  apply hab
  have hzle : Subgroup.zpowers u ≤ Subgroup.normalizer (E₀ : Set G) :=
    Subgroup.zpowers_le.mpr hunorm
  have hwe : ∀ w ∈ Subgroup.zpowers u, ∀ e ∈ E₀, w * e = e * w := by
    intro w hw e he
    obtain ⟨k, rfl⟩ := hw
    exact (Commute.zpow_left (show Commute u e from hcomm e he) k).eq
  have hww : ∀ w ∈ Subgroup.zpowers u, ∀ w' ∈ Subgroup.zpowers u, w * w' = w' * w := by
    intro w hw w' hw'
    obtain ⟨k, rfl⟩ := hw
    obtain ⟨k', rfl⟩ := hw'
    exact ((Commute.refl u).zpow_zpow k k').eq
  obtain ⟨e₁, he₁, w₁, hw₁, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hzle).1 ha
  obtain ⟨e₂, he₂, w₂, hw₂, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hzle).1 hb
  calc e₁ * w₁ * (e₂ * w₂) = e₁ * (w₁ * e₂) * w₂ := by group
    _ = e₁ * (e₂ * w₁) * w₂ := by rw [hwe w₁ hw₁ e₂ he₂]
    _ = (e₁ * e₂) * (w₁ * w₂) := by group
    _ = (e₂ * e₁) * (w₂ * w₁) := by rw [hE₀comm e₁ he₁ e₂ he₂, hww w₁ hw₁ w₂ hw₂]
    _ = e₂ * (e₁ * w₂) * w₁ := by group
    _ = e₂ * (w₂ * e₁) * w₁ := by rw [hwe w₂ hw₂ e₁ he₁]
    _ = e₂ * w₂ * (e₁ * w₁) := by group

theorem Counter.centralizer_inf_uOfL22_le_Ac {t : G} (htT : t ∈ T) (htRQ : t ∉ rOf T M ⊔ qOf T)
    {u : G} (hu : u ∈ uOfL22 T M) (hC : u ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) :
    u ∈ c.Ac hrW hrV hr2 := by
  have hW : u ∈ Hyp1281Two.wOfU T M :=
    ⟨hu, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_iff.mp hC v (c.VZ_le_Ac hrW hrV hr2 hv)⟩
  have hRC := c.centralizer_inf_rOf_Ac hrW hrV hr2 htT htRQ
  have : u ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ⊓ rOf T M := ⟨hC, c.mem_rOf_of_mem_wOfU hW⟩
  rwa [hRC] at this

theorem Counter.card_uOfL22_inf_Ac : Nat.card ↥(uOfL22 T M ⊓ c.Ac hrW hrV hr2) = 8 := by
  have : uOfL22 T M ⊓ c.Ac hrW hrV hr2 = c.Ac hrW hrV hr2 ⊓ qOf T := by
    apply le_antisymm
    · exact fun x hx => ⟨hx.2, uOfL22_le_qOf c hx.1⟩
    · exact fun x hx => ⟨c.Ac_inf_qOf_le_uOfL22 hrW hrV hr2 hx, hx.1⟩
  rw [this]
  exact c.card_inf_qOf_Ac hrW hrV hr2

omit hrW hrV hr2 in
theorem Counter.mul_self_mem_Z {u : G} (hu : u ∈ uOfL22 T M) :
    u * u ∈ quasithinOmegaOneCenter T := by
  have h1 := tilde_mul_self c.h1281 (tclsE c.hUN hu)
  rw [← tclsE_mul c.hUN hu hu] at h1
  exact (tclsE_eq_one_iff c.hUN ((uOfL22 T M).mul_mem hu hu)).mp h1

variable {c hrW hrV hr2}

variable {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T)

include hS htT htRQ

omit htT htRQ in
theorem Setup.faithful_on_E {u : G} (hu : u ∈ uOfL22 T M) (hne : cmat z a r r1 u ≠ I4) :
    (cmat z a r r1 u).r1 ≠ I4.r1 ∨ (cmat z a r r1 u).r2 ≠ I4.r2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply hne
  have hB := hS.basis
  have huH : u ∈ mcOf T := c.h1281.uOfL22_le_g1 hu
  have huI : u ∈ iTwo T M := le_conjClosure _ _ hu
  have huN := c.iTwo_le_normalizer_Ac hrW hrV hr2 huI
  have hcz : Commute u z := (Subgroup.mem_centralizer_iff.mp huH z hS.z_mem).symm
  have hca : Commute u a := by
    have : u * a * u⁻¹ = a := by
      apply hB.coordsOf_inj (conj_mem_of_mem_normalizer huN hS.a_A) hS.a_A
      rw [hB.coordsOf_e1, ← cmat_r1]
      exact h1
    exact mul_inv_eq_iff_eq_mul.mp this
  have hcr : Commute u r := by
    have : u * r * u⁻¹ = r := by
      apply hB.coordsOf_inj (conj_mem_of_mem_normalizer huN (c.r_mem_Ac hrW hrV hr2))
        (c.r_mem_Ac hrW hrV hr2)
      rw [hB.coordsOf_e2, ← cmat_r2]
      exact h2
    exact mul_inv_eq_iff_eq_mul.mp this
  have hite : ∀ (b : Bool) (e : G), Commute u e → Commute u (if b = true then e else 1) := by
    intro b e he; cases b <;> simp [he]
  have hcomm : ∀ e ∈ c.Ac hrW hrV hr2 ⊓ qOf T, u * e = e * u := by
    intro e he
    have hx3 := hS.coords_x3_of_mem_Q he.1 he.2
    have hemb : e = embV z a r r1 (coordsOf z a r r1 e) := (hB.embV_coordsOf he.1).symm
    have e' : e = (if (coordsOf z a r r1 e).x0 = true then z else 1) *
        (if (coordsOf z a r r1 e).x1 = true then a else 1) *
        (if (coordsOf z a r r1 e).x2 = true then r else 1) := by
      conv_lhs => rw [hemb]
      simp [embV, hx3]
    have : Commute u e := by
      rw [e']
      exact ((hite _ z hcz).mul_right (hite _ a hca)).mul_right (hite _ r hcr)
    exact this
  have huE := c.mem_Ac_inf_qOf_of_centralizes hrW hrV hr2 hu hcomm
  exact (hB.cmat_eq_one_iff_mem_centralizer huN).mpr
    (Subgroup.mem_centralizer_iff.mpr fun a' ha' => hB.comm a' ha' u huE.1)

theorem Setup.exists_UHyp {R1 R2 : Mat4}
    (hR : ∀ P, P ∈ [I4, R1, R2, mm R1 R2] ↔ ∃ ρ' ∈ rOf T M, cmat z a r r1 ρ' = P) :
    ∃ N1 N2 : Mat4, IsUMat N1 ∧ IsUMat N2 ∧ UHypL [I4, R1, R2, mm R1 R2] N1 N2 ∧
      ∀ P, P ∈ [I4, N1, N2, mm N1 N2] ↔ ∃ u ∈ uOfL22 T M, cmat z a r r1 u = P := by
  have hB := hS.basis
  have hUI : ∀ u ∈ uOfL22 T M, u ∈ iTwo T M := fun u hu => le_conjClosure _ _ hu
  have hUN : ∀ u ∈ uOfL22 T M, u ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    fun u hu => c.iTwo_le_normalizer_Ac hrW hrV hr2 (hUI u hu)
  have hAC : ∀ w ∈ c.Ac hrW hrV hr2, w ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
    fun w hw => Subgroup.mem_centralizer_iff.mpr fun a' ha' => hB.comm a' ha' w hw
  have hZA : ∀ w ∈ quasithinOmegaOneCenter T, w ∈ c.Ac hrW hrV hr2 := fun w hw =>
    c.VZ_le_Ac hrW hrV hr2 (Hyp1281Two.omegaOneCenter_le_VZ T M hw)
  have hEq : ∀ u ∈ uOfL22 T M, ∀ u' ∈ uOfL22 T M,
      cmat z a r r1 u = cmat z a r r1 u' ↔ u⁻¹ * u' ∈ uOfL22 T M ⊓ c.Ac hrW hrV hr2 := by
    intro u hu u' hu'
    rw [hB.cmat_eq_iff_mem_centralizer (hUN u hu) (hUN u' hu')]
    have hw : u⁻¹ * u' ∈ uOfL22 T M := (uOfL22 T M).mul_mem ((uOfL22 T M).inv_mem hu) hu'
    constructor
    · intro h
      exact ⟨hw, c.centralizer_inf_uOfL22_le_Ac hrW hrV hr2 htT htRQ hw h⟩
    · intro h
      exact hAC _ h.2
  have hcard := ncard_image_mul_card (inf_le_left : uOfL22 T M ⊓ c.Ac hrW hrV hr2 ≤ uOfL22 T M)
    (cmat z a r r1) hEq
  rw [c.card_uOfL22_inf_Ac hrW hrV hr2, c.c15.q8sq.1] at hcard
  have hX : ((cmat z a r r1) '' (uOfL22 T M : Set G)).ncard = 4 := by omega
  set X := (cmat z a r r1) '' (uOfL22 T M : Set G) with hXdef
  have hI4 : I4 ∈ X := ⟨1, (uOfL22 T M).one_mem, hB.cmat_one⟩
  obtain ⟨N1, hN1X, hN1⟩ : ∃ N1 ∈ X, N1 ≠ I4 := by
    by_contra hh
    push Not at hh
    have h1 : X ⊆ {I4} := fun P hP => hh P hP
    have h2 := Set.ncard_le_ncard h1 (Set.finite_singleton _)
    rw [Set.ncard_singleton] at h2
    omega
  obtain ⟨N2, hN2X, hN2, hN21⟩ : ∃ N2 ∈ X, N2 ≠ I4 ∧ N2 ≠ N1 := by
    by_contra hh
    push Not at hh
    have h1 : X ⊆ {I4, N1} := fun P hP => by
      by_cases h : P = I4
      · exact Or.inl h
      · exact Or.inr (hh P hP h)
    have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
    have h3 : ({I4, N1} : Set Mat4).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    omega
  obtain ⟨u₁, hu₁, hu₁'⟩ := hN1X
  obtain ⟨u₂, hu₂, hu₂'⟩ := hN2X
  rw [← hu₁'] at hN1 hN21
  rw [← hu₂'] at hN2 hN21
  clear hu₁' hu₂'
  have hm1 : IsUMat (cmat z a r r1 u₁) := hS.isUMat_cmat hu₁
  have hm2 : IsUMat (cmat z a r r1 u₂) := hS.isUMat_cmat hu₂
  have hN1N2 : mm (cmat z a r r1 u₁) (cmat z a r r1 u₂) = cmat z a r r1 (u₂ * u₁) :=
    (hB.cmat_mul (hUN u₂ hu₂) (hUN u₁ hu₁)).symm
  have hN2N1 : mm (cmat z a r r1 u₂) (cmat z a r r1 u₁) = cmat z a r r1 (u₁ * u₂) :=
    (hB.cmat_mul (hUN u₁ hu₁) (hUN u₂ hu₂)).symm
  have hcommN : mm (cmat z a r r1 u₁) (cmat z a r r1 u₂) = mm (cmat z a r r1 u₂) (cmat z a r r1 u₁) := by
    rw [hN1N2, hN2N1, hB.cmat_eq_iff_mem_centralizer
      (hUN _ ((uOfL22 T M).mul_mem hu₂ hu₁)) (hUN _ ((uOfL22 T M).mul_mem hu₁ hu₂))]
    apply hAC
    apply hZA
    have := c.h1281.commutator_mem_omegaOneCenter ((uOfL22 T M).inv_mem hu₁)
      ((uOfL22 T M).inv_mem hu₂)
    have e : (u₂ * u₁)⁻¹ * (u₁ * u₂) = u₁⁻¹ * u₂⁻¹ * u₁⁻¹⁻¹ * u₂⁻¹⁻¹ := by group
    rw [e]; exact this
  have hsq : ∀ u ∈ uOfL22 T M, mm (cmat z a r r1 u) (cmat z a r r1 u) = I4 := by
    intro u hu
    rw [← hB.cmat_mul (hUN u hu) (hUN u hu)]
    exact (hB.cmat_eq_one_iff_mem_centralizer (hUN _ ((uOfL22 T M).mul_mem hu hu))).mpr
      (hAC _ (hZA _ (c.mul_self_mem_Z hu)))
  have hs1 := hsq u₁ hu₁
  have hs2 := hsq u₂ hu₂
  have hd := IsUMat.mm_distinct hm1 hm2 hcommN hs1 hs2 hN1 hN2 (fun h => hN21 h.symm)
  have hnd : [I4, (cmat z a r r1 u₁), (cmat z a r r1 u₂), mm (cmat z a r r1 u₁) (cmat z a r r1 u₂)].Nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr
      ⟨?_, List.nodup_singleton _⟩⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hN1.symm, hN2.symm, hd.1.symm⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hN21 h.symm, hd.2.1.symm⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact hd.2.2.symm
  have hsub : (↑([I4, (cmat z a r r1 u₁), (cmat z a r r1 u₂), mm (cmat z a r r1 u₁) (cmat z a r r1 u₂)].toFinset) : Set Mat4) ⊆ X := by
    intro P hP
    have hP' : P ∈ [I4, (cmat z a r r1 u₁), (cmat z a r r1 u₂), mm (cmat z a r r1 u₁) (cmat z a r r1 u₂)] := List.mem_toFinset.mp (Finset.mem_coe.mp hP)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP'
    rcases hP' with rfl | rfl | rfl | rfl
    · exact hI4
    · exact ⟨u₁, hu₁, rfl⟩
    · exact ⟨u₂, hu₂, rfl⟩
    · exact ⟨u₂ * u₁, (uOfL22 T M).mul_mem hu₂ hu₁, hN1N2.symm⟩
  have hcardS : (↑([I4, (cmat z a r r1 u₁), (cmat z a r r1 u₂), mm (cmat z a r r1 u₁) (cmat z a r r1 u₂)].toFinset) : Set Mat4).ncard = 4 := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]; rfl
  have hEqX := Set.eq_of_subset_of_ncard_le hsub (by rw [hcardS, hX]) (Set.toFinite _)
  have hset : ∀ P, P ∈ [I4, (cmat z a r r1 u₁), (cmat z a r r1 u₂), mm (cmat z a r r1 u₁) (cmat z a r r1 u₂)] ↔ P ∈ X := by
    intro P
    have := Set.ext_iff.mp hEqX P
    simpa using this
  refine ⟨(cmat z a r r1 u₁), (cmat z a r r1 u₂), hm1, hm2, ⟨hcommN, hs1, hs2, hN1, hN2, fun h => hN21 h.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hS.faithful_on_E hu₁ hN1
  · exact hS.faithful_on_E hu₂ hN2
  · rw [hN1N2]
    exact hS.faithful_on_E ((uOfL22 T M).mul_mem hu₂ hu₁) (hN1N2 ▸ hd.1)
  ·
    intro P hP
    obtain ⟨ρ', hρ'R, hρ'⟩ := (hR P).mp hP
    have hRN := c.rOf_le_normalizer_Ac hrW hrV hr2
    have hu₁R : u₁ ∈ Subgroup.normalizer (rOf T M : Set G) :=
      le_normalizer_pCoreOf 2 (iTwo T M) (hUI u₁ hu₁)
    have hρ'' : u₁ * ρ' * u₁⁻¹ ∈ rOf T M := (Subgroup.mem_normalizer_iff.mp hu₁R ρ').mp hρ'R
    refine ⟨cmat z a r r1 (u₁ * ρ' * u₁⁻¹), (hR _).mpr ⟨_, hρ'', rfl⟩, ?_⟩
    rw [← hρ', ← hB.cmat_mul (hUN u₁ hu₁) (hRN hρ'R),
      ← hB.cmat_mul (hRN hρ'') (hUN u₁ hu₁)]
    congr 1
    group
  · intro P hP
    obtain ⟨ρ', hρ'R, hρ'⟩ := (hR P).mp hP
    have hRN := c.rOf_le_normalizer_Ac hrW hrV hr2
    have hu₂R : u₂ ∈ Subgroup.normalizer (rOf T M : Set G) :=
      le_normalizer_pCoreOf 2 (iTwo T M) (hUI u₂ hu₂)
    have hρ'' : u₂ * ρ' * u₂⁻¹ ∈ rOf T M := (Subgroup.mem_normalizer_iff.mp hu₂R ρ').mp hρ'R
    refine ⟨cmat z a r r1 (u₂ * ρ' * u₂⁻¹), (hR _).mpr ⟨_, hρ'', rfl⟩, ?_⟩
    rw [← hρ', ← hB.cmat_mul (hUN u₂ hu₂) (hRN hρ'R),
      ← hB.cmat_mul (hRN hρ'') (hUN u₂ hu₂)]
    congr 1
    group
  ·
    obtain ⟨w, hwW, hwA⟩ : ∃ w ∈ Hyp1281Two.wOfU T M, w ∉ c.Ac hrW hrV hr2 := by
      by_contra hh
      push Not at hh
      have h1 : Nat.card (Hyp1281Two.wOfU T M) ≤ Nat.card ↥(c.Ac hrW hrV hr2 ⊓ qOf T) :=
        Subgroup.card_le_of_le fun x hx => ⟨hh x hx, c.wOfU_le_qOf hx⟩
      have hW : Nat.card ↥(Hyp1281Two.wOfU T M) = 16 := card_wOf c
      rw [hW, c.card_inf_qOf_Ac hrW hrV hr2] at h1
      omega
    have hwU : w ∈ uOfL22 T M := hwW.1
    have hwR : w ∈ rOf T M := c.mem_rOf_of_mem_wOfU hwW
    have hwne : cmat z a r r1 w ≠ I4 := by
      intro h
      apply hwA
      have hRC := c.centralizer_inf_rOf_Ac hrW hrV hr2 htT htRQ
      have : w ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ⊓ rOf T M :=
        ⟨(hB.cmat_eq_one_iff_mem_centralizer (hUN w hwU)).mp h, hwR⟩
      rwa [hRC] at this
    have hwX : cmat z a r r1 w ∈ [I4, (cmat z a r r1 u₁), (cmat z a r r1 u₂), mm (cmat z a r r1 u₁) (cmat z a r r1 u₂)] := (hset _).mpr ⟨w, hwU, rfl⟩
    refine ⟨cmat z a r r1 w, ?_, (hR _).mpr ⟨w, hwR, rfl⟩, hwne⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwX ⊢
    rcases hwX with h | h | h | h
    · exact absurd h hwne
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro P
    rw [hset P]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

end Hyp

end S143

end CFSG.Quasithin
