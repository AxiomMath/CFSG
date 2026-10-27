module

public import CFSG.Quasithin.EmptyFaithful.S143FD
public import CFSG.Quasithin.EmptyFaithful.S143FC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Util

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem {A : Subgroup G} {γ : G} (h1 : ∀ x ∈ A, γ * x * γ⁻¹ ∈ A)
    (h2 : ∀ x ∈ A, γ⁻¹ * x * γ ∈ A) : γ ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨h1 x, fun hx => by simpa [mul_assoc] using h2 _ hx⟩

theorem mul_comm_of_sq_eq_one {A : Subgroup G} (hsq : ∀ x ∈ A, x * x = 1) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) : a * b = b * a := by
  have h1 := hsq (a * b) (A.mul_mem ha hb)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  have h3 : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [mul_inv_rev, hai, hbi] at h3
  exact h3

theorem comm_mul_central {a b e₁ e₂ : G} (h1 : e₁ * b = b * e₁) (h2 : e₂ * a = a * e₂)
    (h12 : e₁ * e₂ = e₂ * e₁) :
    (a * e₁) * (b * e₂) * (a * e₁)⁻¹ * (b * e₂)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h12' : e₂ * e₁⁻¹ = e₁⁻¹ * e₂ := (Commute.inv_right (show Commute e₂ e₁ from h12.symm)).eq
  have h2' : e₂ * a⁻¹ = a⁻¹ * e₂ := (Commute.inv_right (show Commute e₂ a from h2)).eq
  calc (a * e₁) * (b * e₂) * (a * e₁)⁻¹ * (b * e₂)⁻¹
      = a * (e₁ * b) * (e₂ * e₁⁻¹) * a⁻¹ * e₂⁻¹ * b⁻¹ := by group
    _ = a * (b * e₁) * (e₁⁻¹ * e₂) * a⁻¹ * e₂⁻¹ * b⁻¹ := by rw [h1, h12']
    _ = a * b * (e₂ * a⁻¹) * e₂⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * e₂) * e₂⁻¹ * b⁻¹ := by rw [h2']
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_mul_right {a b c : G} (h : (a * c * a⁻¹ * c⁻¹) * b = b * (a * c * a⁻¹ * c⁻¹)) :
    a * (b * c) * a⁻¹ * (b * c)⁻¹ = (a * b * a⁻¹ * b⁻¹) * (a * c * a⁻¹ * c⁻¹) := by
  calc a * (b * c) * a⁻¹ * (b * c)⁻¹
      = (a * b * a⁻¹ * b⁻¹) * (b * (a * c * a⁻¹ * c⁻¹) * b⁻¹) := by group
    _ = (a * b * a⁻¹ * b⁻¹) * ((a * c * a⁻¹ * c⁻¹) * b * b⁻¹) := by rw [← h]
    _ = (a * b * a⁻¹ * b⁻¹) * (a * c * a⁻¹ * c⁻¹) := by group

theorem le_or_le_of_forall_mem {A B C : Subgroup G} (h : ∀ x ∈ C, x ∈ A ∨ x ∈ B) :
    C ≤ A ∨ C ≤ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hCA, hCB⟩ := hcon
  obtain ⟨x, hxC, hxA⟩ : ∃ x ∈ C, x ∉ A := by
    by_contra hx
    push Not at hx
    exact hCA hx
  obtain ⟨y, hyC, hyB⟩ : ∃ y ∈ C, y ∉ B := by
    by_contra hy
    push Not at hy
    exact hCB hy
  have hxB : x ∈ B := (h x hxC).resolve_left hxA
  have hyA : y ∈ A := (h y hyC).resolve_right hyB
  rcases h (x * y) (C.mul_mem hxC hyC) with hxy | hxy
  · apply hxA
    have := A.mul_mem hxy (A.inv_mem hyA)
    simpa using this
  · apply hyB
    have := B.mul_mem (B.inv_mem hxB) hxy
    simpa using this

end Util

section Normalizer

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.centerOf_uOfL22_eq : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T :=
  (Subgroup.eq_of_le_of_card_ge c.h1281.omegaOneCenter_le_centerOf_uOfL22 (by
    rw [isQ8Sq_card_centerOf c.c15.q8sq, c.h1281.card_omegaOneCenter])).symm

theorem Counter.wOfU_not_comm :
    ¬ ∀ w ∈ Hyp1281Two.wOfU T M, ∀ w' ∈ Hyp1281Two.wOfU T M, w * w' = w' * w := by
  intro hall
  have h := c.h1281
  have hWc : Hyp1281Two.wOfU T M ≤ centerOf (Hyp1281Two.wOfU T M) := fun w hw =>
    ⟨hw, Subgroup.mem_centralizer_iff.mpr fun w' hw' => hall w' hw' w hw⟩
  rw [h.centerOf_wOfU_eq c.nonab, c.centerOf_uOfL22_eq,
    sup_eq_left.mpr (Hyp1281Two.omegaOneCenter_le_VZ T M)] at hWc
  have hcard : Nat.card (Hyp1281Two.wOfU T M) ≤ Nat.card (VZ T M) := Subgroup.card_le_of_le hWc
  have hW : Nat.card (Hyp1281Two.wOfU T M) = 16 := card_wOf c
  rw [hW, h.rank_two] at hcard
  omega

theorem Counter.mem_rOf_of_mem_wOfU {w : G} (hw : w ∈ Hyp1281Two.wOfU T M) : w ∈ rOf T M := by
  rw [rOf_eq_pCoreOf_sup c]
  exact c.h1281.wOfU_le_pCoreOf c.nonab c.goodElt hw

theorem Counter.dOf_commutator_mem {d x : G} (hd : d ∈ dOf T M) (hx : x ∈ rOf T M) :
    d * x * d⁻¹ * x⁻¹ ∈ quasithinOmegaOneCenter T := by
  have h := c.h1281
  have hxH : x ∈ mcOf T := rOf_le_mcOf c hx
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22
  have hd1 : x * d⁻¹ * x⁻¹ ∈ dOf T M := by
    refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (mcOf T) hxH) d⁻¹).mp
        ((qOf T).inv_mem hd.1), Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    · have hxu : x⁻¹ * u * x⁻¹⁻¹ ∈ uOfL22 T M :=
        (Subgroup.mem_normalizer_iff.mp (hHU ((mcOf T).inv_mem hxH)) u).mp hu
      have hyd := Subgroup.mem_centralizer_iff.mp ((dOf T M).inv_mem hd).2 _ hxu
      calc u * (x * d⁻¹ * x⁻¹) = x * ((x⁻¹ * u * x⁻¹⁻¹) * d⁻¹) * x⁻¹ := by group
        _ = x * (d⁻¹ * (x⁻¹ * u * x⁻¹⁻¹)) * x⁻¹ := by rw [hyd]
        _ = (x * d⁻¹ * x⁻¹) * u := by group
  have hDmem : d * x * d⁻¹ * x⁻¹ ∈ dOf T M := by
    have e : d * x * d⁻¹ * x⁻¹ = d * (x * d⁻¹ * x⁻¹) := by group
    rw [e]
    exact (dOf T M).mul_mem hd hd1
  have hRmem : d * x * d⁻¹ * x⁻¹ ∈ rOf T M := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (qOf_le_normalizer_rOf c hd.1) x).mp hx
    exact (rOf T M).mul_mem h1 ((rOf T M).inv_mem hx)
  have hRQ : d * x * d⁻¹ * x⁻¹ ∈ rOf T M ⊓ qOf T := ⟨hRmem, hDmem.1⟩
  rw [rOf_inf_qOf c] at hRQ
  have hZ : d * x * d⁻¹ * x⁻¹ ∈ centerOf (uOfL22 T M) :=
    ⟨hRQ.1, hDmem.2⟩
  rwa [c.centerOf_uOfL22_eq] at hZ

section TNorm

variable {t : G} (htT : t ∈ T)

include htT

theorem Counter.T_le_normalizer_rOf' : t ∈ Subgroup.normalizer (rOf T M : Set G) :=
  (c.hyp.m_max.1.2).trans (M_le_normalizer_rOf c) htT

theorem Counter.T_mem_normalizer_VZ : t ∈ Subgroup.normalizer (VZ T M : Set G) := by
  rw [c.h1281.normalizer_VZ]; exact c.hyp.m_max.1.2 htT

theorem Counter.T_mem_normalizer_iTwo : t ∈ Subgroup.normalizer (iTwo T M : Set G) :=
  normal_i2_of_hyp c.h1281 (c.hyp.m_max.1.2 htT)

end TNorm

variable {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include hrW hrV hr2

theorem Counter.iTwo_le_normalizer_Ac : iTwo T M ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
  fun γ hγ => mem_normalizer_of_conj_mem (fun _ hx => c.Ac_conj_mem hrW hrV hr2 hγ hx)
    (fun _ hx => c.Ac_conj_mem hrW hrV hr2 ((iTwo T M).inv_mem hγ) hx |> fun h' => by
      simpa using h')

theorem Counter.normal_Ac :
    iTwo T M ⊔ qOf T ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := by
  refine sup_le (c.iTwo_le_normalizer_Ac hrW hrV hr2) ?_
  rw [(lemma_14_3_19_one c).q_eq]
  refine sup_le ?_ ?_
  · intro u hu
    exact c.iTwo_le_normalizer_Ac hrW hrV hr2 (le_conjClosure _ _ hu)
  · intro d hd
    have hcomm : ∀ x ∈ c.Ac hrW hrV hr2, ∀ δ ∈ dOf T M, δ * x * δ⁻¹ ∈ c.Ac hrW hrV hr2 := by
      intro x hx δ hδ
      have hxR : x ∈ rOf T M := c.Ac_le_rOf hrW hrV hr2 hx
      have h1 := c.dOf_commutator_mem hδ hxR
      have e : δ * x * δ⁻¹ = (δ * x * δ⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact (c.Ac hrW hrV hr2).mul_mem (c.VZ_le_Ac hrW hrV hr2
        (Hyp1281Two.omegaOneCenter_le_VZ T M h1)) hx
    exact mem_normalizer_of_conj_mem (hcomm · · d hd) (fun x hx => by
      simpa using hcomm x hx d⁻¹ ((dOf T M).inv_mem hd))

theorem Counter.norm_mem_VZ :
    r * (g * r * g⁻¹) * (g * g * r * (g * g)⁻¹) ∈ VZ T M := by
  have := (c.kdata hrW hrV hr2).norm
  rwa [E_eq_VZ c] at this

theorem Counter.Ac_not_le_wOfU : ¬ c.Ac hrW hrV hr2 ≤ Hyp1281Two.wOfU T M := by
  intro hle
  have hW : Nat.card (Hyp1281Two.wOfU T M) = 16 := card_wOf c
  have hcard : Nat.card (Hyp1281Two.wOfU T M) ≤ Nat.card (c.Ac hrW hrV hr2) := by
    rw [hW, c.card_Ac hrW hrV hr2]
  have heq : c.Ac hrW hrV hr2 = Hyp1281Two.wOfU T M := Subgroup.eq_of_le_of_card_ge hle hcard
  apply c.wOfU_not_comm
  intro w hw w' hw'
  rw [← heq] at hw hw'
  exact mul_comm_of_sq_eq_one (fun x hx => c.sq_Ac hrW hrV hr2 hx) hw hw'

theorem Counter.r1_not_mem_wOfU : g * r * g⁻¹ ∉ Hyp1281Two.wOfU T M := by
  intro hr1
  have h := c.h1281
  refine c.Ac_not_le_wOfU hrW hrV hr2 fun x hx => ?_
  obtain ⟨e, he, hcases⟩ := c.mem_Ac_cases hrW hrV hr2 hx
  have heW : e ∈ Hyp1281Two.wOfU T M := Hyp1281Two.VZ_le_wOfU h he
  have he₀ := c.norm_mem_VZ hrW hrV hr2
  have hr2W : g * g * r * (g * g)⁻¹ ∈ Hyp1281Two.wOfU T M := by
    have e' : g * g * r * (g * g)⁻¹ =
        (r * (g * r * g⁻¹))⁻¹ * (r * (g * r * g⁻¹) * (g * g * r * (g * g)⁻¹)) := by group
    rw [e']
    exact (Hyp1281Two.wOfU T M).mul_mem ((Hyp1281Two.wOfU T M).inv_mem
      ((Hyp1281Two.wOfU T M).mul_mem hrW hr1)) (Hyp1281Two.VZ_le_wOfU h he₀)
  rcases hcases with rfl | rfl | rfl | rfl
  · exact heW
  · exact (Hyp1281Two.wOfU T M).mul_mem hrW heW
  · exact (Hyp1281Two.wOfU T M).mul_mem hr1 heW
  · exact (Hyp1281Two.wOfU T M).mul_mem hr2W heW

theorem Counter.r2_not_mem_wOfU : g * g * r * (g * g)⁻¹ ∉ Hyp1281Two.wOfU T M := by
  intro hr2'
  apply c.r1_not_mem_wOfU hrW hrV hr2
  have h := c.h1281
  have he₀ := c.norm_mem_VZ hrW hrV hr2
  have e' : g * r * g⁻¹ = r⁻¹ * (r * (g * r * g⁻¹) * (g * g * r * (g * g)⁻¹)) *
      (g * g * r * (g * g)⁻¹)⁻¹ := by group
  rw [e']
  exact (Hyp1281Two.wOfU T M).mul_mem ((Hyp1281Two.wOfU T M).mul_mem
    ((Hyp1281Two.wOfU T M).inv_mem hrW) (Hyp1281Two.VZ_le_wOfU h he₀))
    ((Hyp1281Two.wOfU T M).inv_mem hr2')

variable {t : G} (htT : t ∈ T)

include htT

theorem Counter.conjAc_le_rOf : conjSubgroup (c.Ac hrW hrV hr2) t ≤ rOf T M := by
  intro x hx
  have h1 : t * x * t⁻¹ ∈ c.Ac hrW hrV hr2 := mem_conjSubgroup_iff.mp hx
  have h2 : t * x * t⁻¹ ∈ rOf T M := c.Ac_le_rOf hrW hrV hr2 h1
  have hN : t⁻¹ ∈ Subgroup.normalizer (rOf T M : Set G) :=
    Subgroup.inv_mem _ (c.T_le_normalizer_rOf' htT)
  have := (Subgroup.mem_normalizer_iff.mp hN _).mp h2
  simpa [mul_assoc] using this

theorem Counter.VZ_le_conjAc : VZ T M ≤ conjSubgroup (c.Ac hrW hrV hr2) t := by
  intro v hv
  refine mem_conjSubgroup_iff.mpr (c.VZ_le_Ac hrW hrV hr2 ?_)
  exact (Subgroup.mem_normalizer_iff.mp (c.T_mem_normalizer_VZ htT) v).mp hv

omit htT in
theorem Counter.card_conjAc : Nat.card (conjSubgroup (c.Ac hrW hrV hr2) t) = 16 := by
  rw [← c.card_Ac hrW hrV hr2]
  exact Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective

omit htT in
theorem Counter.sq_conjAc {x : G} (hx : x ∈ conjSubgroup (c.Ac hrW hrV hr2) t) : x * x = 1 := by
  have h1 := c.sq_Ac hrW hrV hr2 (mem_conjSubgroup_iff.mp hx)
  have e : x * x = t⁻¹ * (t * x * t⁻¹ * (t * x * t⁻¹)) * t := by group
  rw [e, h1]
  group

theorem Counter.conjAc_conj_mem {γ x : G} (hγ : γ ∈ iTwo T M)
    (hx : x ∈ conjSubgroup (c.Ac hrW hrV hr2) t) :
    γ * x * γ⁻¹ ∈ conjSubgroup (c.Ac hrW hrV hr2) t := by
  refine mem_conjSubgroup_iff.mpr ?_
  have h1 := mem_conjSubgroup_iff.mp hx
  have hγ' : t * γ * t⁻¹ ∈ iTwo T M :=
    (Subgroup.mem_normalizer_iff.mp (c.T_mem_normalizer_iTwo htT) γ).mp hγ
  have h2 := c.Ac_conj_mem hrW hrV hr2 hγ' h1
  have e : t * (γ * x * γ⁻¹) * t⁻¹ = (t * γ * t⁻¹) * (t * x * t⁻¹) * (t * γ * t⁻¹)⁻¹ := by group
  rw [e]
  exact h2

omit hrW hrV hr2 htT in
theorem Counter.g_mem_iTwo : g ∈ iTwo T M := by
  rw [iTwo_eq c.h1281 c.nonab]
  exact c.goodElt.mem_sup _

theorem Counter.Ac_conj_ne (htRQ : t ∉ rOf T M ⊔ qOf T) :
    conjSubgroup (c.Ac hrW hrV hr2) t ≠ c.Ac hrW hrV hr2 := by
  intro hEq
  have h := c.h1281
  have h1 : t * r * t⁻¹ ∈ c.Ac hrW hrV hr2 := by
    have : r ∈ conjSubgroup (c.Ac hrW hrV hr2) t := by
      rw [hEq]; exact c.r_mem_Ac hrW hrV hr2
    exact mem_conjSubgroup_iff.mp this
  have hW : t * r * t⁻¹ ∈ Hyp1281Two.wOfU T M :=
    (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer_wOfU htT) r).mp hrW
  obtain ⟨e, he, hcases⟩ := c.mem_Ac_cases hrW hrV hr2 h1
  have heW : e ∈ Hyp1281Two.wOfU T M := Hyp1281Two.VZ_le_wOfU h he
  rcases hcases with h3 | h3 | h3 | h3
  · apply hrV
    have hN : t⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
      Subgroup.inv_mem _ (c.T_mem_normalizer_VZ htT)
    have := (Subgroup.mem_normalizer_iff.mp hN e).mp he
    have e' : t⁻¹ * e * t⁻¹⁻¹ = r := by rw [← h3]; group
    rwa [e'] at this
  · exact c.conj_ne_coset hrW hrV hr2 htT htRQ e he h3
  · apply c.r1_not_mem_wOfU hrW hrV hr2
    have e' : g * r * g⁻¹ = (t * r * t⁻¹) * e⁻¹ := by rw [h3]; group
    rw [e']
    exact (Hyp1281Two.wOfU T M).mul_mem hW ((Hyp1281Two.wOfU T M).inv_mem heW)
  · apply c.r2_not_mem_wOfU hrW hrV hr2
    have e' : g * g * r * (g * g)⁻¹ = (t * r * t⁻¹) * e⁻¹ := by rw [h3]; group
    rw [e']
    exact (Hyp1281Two.wOfU T M).mul_mem hW ((Hyp1281Two.wOfU T M).inv_mem heW)

omit hrV hr2 in
theorem Counter.conj_mem_wOfU : t⁻¹ * r * t ∈ Hyp1281Two.wOfU T M := by
  have := (Subgroup.mem_normalizer_iff.mp
    (c.h1281.T_le_normalizer_wOfU (T.inv_mem htT)) r).mp hrW
  simpa using this

omit hrW hr2 in
theorem Counter.conj_not_mem_VZ : t⁻¹ * r * t ∉ VZ T M := by
  intro hmem
  apply hrV
  have := (Subgroup.mem_normalizer_iff.mp (c.T_mem_normalizer_VZ htT) _).mp hmem
  have e : t * (t⁻¹ * r * t) * t⁻¹ = r := by group
  rwa [e] at this

omit [Finite G] c hrW hrV htT in
theorem Counter.conj_sq : (t⁻¹ * r * t) * (t⁻¹ * r * t) = 1 := by
  have e : (t⁻¹ * r * t) * (t⁻¹ * r * t) = t⁻¹ * (r * r) * t := by group
  rw [e, hr2]
  group

theorem Counter.Ac_conj_eq :
    c.Ac (c.conj_mem_wOfU hrW htT) (c.conj_not_mem_VZ hrV htT)
      (Counter.conj_sq hr2) = conjSubgroup (c.Ac hrW hrV hr2) t := by
  have hVA := c.VZ_le_conjAc hrW hrV hr2 htT
  have hr'mem : t⁻¹ * r * t ∈ conjSubgroup (c.Ac hrW hrV hr2) t := by
    refine mem_conjSubgroup_iff.mpr ?_
    have e : t * (t⁻¹ * r * t) * t⁻¹ = r := by group
    rw [e]
    exact c.r_mem_Ac hrW hrV hr2
  have hr'1 := c.conjAc_conj_mem hrW hrV hr2 htT c.g_mem_iTwo hr'mem
  have hr'2 : g * g * (t⁻¹ * r * t) * (g * g)⁻¹ ∈ conjSubgroup (c.Ac hrW hrV hr2) t := by
    have := c.conjAc_conj_mem hrW hrV hr2 htT c.g_mem_iTwo hr'1
    have e : g * (g * (t⁻¹ * r * t) * g⁻¹) * g⁻¹ = g * g * (t⁻¹ * r * t) * (g * g)⁻¹ := by group
    rwa [e] at this
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
  · obtain ⟨e, he, hcases⟩ := c.mem_Ac_cases _ _ _ hx
    have heA := hVA he
    rcases hcases with rfl | rfl | rfl | rfl
    · exact heA
    · exact (conjSubgroup (c.Ac hrW hrV hr2) t).mul_mem hr'mem heA
    · exact (conjSubgroup (c.Ac hrW hrV hr2) t).mul_mem hr'1 heA
    · exact (conjSubgroup (c.Ac hrW hrV hr2) t).mul_mem hr'2 heA
  · rw [c.card_conjAc hrW hrV hr2, c.card_Ac _ _ _]

theorem Counter.Ac_inf_conj (htRQ : t ∉ rOf T M ⊔ qOf T) :
    c.Ac hrW hrV hr2 ⊓ conjSubgroup (c.Ac hrW hrV hr2) t = VZ T M := by
  have hVA := c.VZ_le_conjAc hrW hrV hr2 htT
  apply le_antisymm
  · intro x hx
    by_contra hxV
    obtain ⟨hxA, hxAt⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨e, he, hcases⟩ := c.mem_Ac_cases hrW hrV hr2 hxA
    have heAt := hVA he
    have hgI : g ∈ iTwo T M := c.g_mem_iTwo
    have hginv : g⁻¹ ∈ iTwo T M := (iTwo T M).inv_mem hgI
    have hr : r ∈ conjSubgroup (c.Ac hrW hrV hr2) t := by
      rcases hcases with rfl | rfl | rfl | rfl
      · exact absurd he hxV
      · have := (conjSubgroup (c.Ac hrW hrV hr2) t).mul_mem hxAt
          ((conjSubgroup (c.Ac hrW hrV hr2) t).inv_mem heAt)
        simpa using this
      · have h1 : g * r * g⁻¹ ∈ conjSubgroup (c.Ac hrW hrV hr2) t := by
          have := (conjSubgroup (c.Ac hrW hrV hr2) t).mul_mem hxAt
            ((conjSubgroup (c.Ac hrW hrV hr2) t).inv_mem heAt)
          have e : g * r * g⁻¹ * e * e⁻¹ = g * r * g⁻¹ := by group
          rwa [e] at this
        have h2 := c.conjAc_conj_mem hrW hrV hr2 htT hginv h1
        have e1 : g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r := by group
        rwa [e1] at h2
      · have h1 : g * g * r * (g * g)⁻¹ ∈ conjSubgroup (c.Ac hrW hrV hr2) t := by
          have := (conjSubgroup (c.Ac hrW hrV hr2) t).mul_mem hxAt
            ((conjSubgroup (c.Ac hrW hrV hr2) t).inv_mem heAt)
          have e : g * g * r * (g * g)⁻¹ * e * e⁻¹ = g * g * r * (g * g)⁻¹ := by group
          rwa [e] at this
        have h2 := c.conjAc_conj_mem hrW hrV hr2 htT hginv h1
        have h3 := c.conjAc_conj_mem hrW hrV hr2 htT hginv h2
        have e1 : g⁻¹ * (g⁻¹ * (g * g * r * (g * g)⁻¹) * g⁻¹⁻¹) * g⁻¹⁻¹ = r := by group
        rwa [e1] at h3
    have hr1 := c.conjAc_conj_mem hrW hrV hr2 htT hgI hr
    have hr2' : g * g * r * (g * g)⁻¹ ∈ conjSubgroup (c.Ac hrW hrV hr2) t := by
      have := c.conjAc_conj_mem hrW hrV hr2 htT hgI hr1
      have e : g * (g * r * g⁻¹) * g⁻¹ = g * g * r * (g * g)⁻¹ := by group
      rwa [e] at this
    have hle : c.Ac hrW hrV hr2 ≤ conjSubgroup (c.Ac hrW hrV hr2) t := by
      intro y hy
      obtain ⟨e', he', hc'⟩ := c.mem_Ac_cases hrW hrV hr2 hy
      have he'A := hVA he'
      rcases hc' with rfl | rfl | rfl | rfl
      · exact he'A
      · exact (conjSubgroup (c.Ac hrW hrV hr2) t).mul_mem hr he'A
      · exact (conjSubgroup (c.Ac hrW hrV hr2) t).mul_mem hr1 he'A
      · exact (conjSubgroup (c.Ac hrW hrV hr2) t).mul_mem hr2' he'A
    have heq := Subgroup.eq_of_le_of_card_ge hle (by
      rw [c.card_conjAc hrW hrV hr2, c.card_Ac hrW hrV hr2])
    exact c.Ac_conj_ne hrW hrV hr2 htT htRQ heq.symm
  · exact le_inf (c.VZ_le_Ac hrW hrV hr2) hVA

theorem Counter.Ac_sup_conj (htRQ : t ∉ rOf T M ⊔ qOf T) :
    c.Ac hrW hrV hr2 ⊔ conjSubgroup (c.Ac hrW hrV hr2) t = rOf T M := by
  have h := c.h1281
  have hle : c.Ac hrW hrV hr2 ⊔ conjSubgroup (c.Ac hrW hrV hr2) t ≤ rOf T M :=
    sup_le (c.Ac_le_rOf hrW hrV hr2) (c.conjAc_le_rOf hrW hrV hr2 htT)
  have hN : conjSubgroup (c.Ac hrW hrV hr2) t ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    fun x hx => c.iTwo_le_normalizer_Ac hrW hrV hr2
      (pCoreOf_le 2 (iTwo T M) (c.conjAc_le_rOf hrW hrV hr2 htT hx))
  have hprod := card_sup_mul_card_inf_of_le_normalizer hN
  rw [c.Ac_inf_conj hrW hrV hr2 htT htRQ, h.rank_two, c.card_Ac hrW hrV hr2,
    c.card_conjAc hrW hrV hr2] at hprod
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_rOf c]
  omega

omit hrW hrV hr2 htT in
theorem Counter.centerOf_wOfU_eq_VZ : centerOf (Hyp1281Two.wOfU T M) = VZ T M := by
  rw [c.h1281.centerOf_wOfU_eq c.nonab, c.centerOf_uOfL22_eq,
    sup_eq_left.mpr (Hyp1281Two.omegaOneCenter_le_VZ T M)]

omit htT in
theorem Counter.comm_ne_of_not_mem_Ac {w : G} (hwW : w ∈ Hyp1281Two.wOfU T M)
    (hwA : w ∉ c.Ac hrW hrV hr2) : r * w * r⁻¹ * w⁻¹ ≠ 1 := by
  intro hcomm
  have h := c.h1281
  have hr1 : r ≠ 1 := fun he => hrV (he ▸ (VZ T M).one_mem)
  have hrR : r ∈ rOf T M := c.mem_rOf_of_mem_wOfU hrW
  have hVW : VZ T M ≤ Hyp1281Two.wOfU T M := Hyp1281Two.VZ_le_wOfU h
  have hrz : Nat.card (Subgroup.zpowers r) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [← sq] at hr2; exact hr2) hr1
  have hrN : r ∈ Subgroup.normalizer (VZ T M : Set G) := by
    rw [h.normalizer_VZ]; exact c.hyp.m_max.1.2 (rOf_le_T_of_hyp h hrR)
  have hbot : Nat.card ↥(VZ T M ⊓ Subgroup.zpowers r) = 1 := by
    have hdvd : Nat.card ↥(VZ T M ⊓ Subgroup.zpowers r) ∣ 2 := by
      rw [← hrz]; exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact h1
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_right : VZ T M ⊓ Subgroup.zpowers r ≤
        Subgroup.zpowers r) (by rw [hrz, h1])
      apply hrV
      have : r ∈ Subgroup.zpowers r := Subgroup.mem_zpowers r
      rw [← heq] at this
      exact this.1
  have hA₀card : Nat.card ↥(VZ T M ⊔ Subgroup.zpowers r) = 8 := by
    have hprod := card_sup_mul_card_inf_of_le_normalizer
      (Subgroup.zpowers_le.mpr hrN : Subgroup.zpowers r ≤ Subgroup.normalizer (VZ T M : Set G))
    rw [hbot, h.rank_two, hrz] at hprod
    omega
  have hA₀A : VZ T M ⊔ Subgroup.zpowers r ≤ c.Ac hrW hrV hr2 :=
    sup_le (c.VZ_le_Ac hrW hrV hr2) (Subgroup.zpowers_le.mpr (c.r_mem_Ac hrW hrV hr2))
  have hrcent : r ∈ Subgroup.centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => by rw [Set.mem_singleton_iff.mp hy]
  have hA₀C : VZ T M ⊔ Subgroup.zpowers r ≤
      Hyp1281Two.wOfU T M ⊓ Subgroup.centralizer ({r} : Set G) := by
    refine le_inf (sup_le hVW (Subgroup.zpowers_le.mpr hrW))
      (sup_le ?_ (Subgroup.zpowers_le.mpr hrcent))
    intro e he
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    exact (c.rOf_comm_VZ hrR he).symm
  have hcomm' : r * w = w * r := by
    calc r * w = (r * w * r⁻¹ * w⁻¹) * (w * r) := by group
      _ = w * r := by rw [hcomm, one_mul]
  have hwcent : w ∈ Subgroup.centralizer ({r} : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    exact hcomm'
  have hA₁C : (VZ T M ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers w ≤
      Hyp1281Two.wOfU T M ⊓ Subgroup.centralizer ({r} : Set G) :=
    sup_le hA₀C (Subgroup.zpowers_le.mpr ⟨hwW, hwcent⟩)
  have hA₁W : (VZ T M ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers w ≤ Hyp1281Two.wOfU T M :=
    hA₁C.trans inf_le_left
  have hwA₁ : w ∈ (VZ T M ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers w :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hwnA₀ : w ∉ VZ T M ⊔ Subgroup.zpowers r := fun hm => hwA (hA₀A hm)
  have hne : VZ T M ⊔ Subgroup.zpowers r ≠ (VZ T M ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers w := by
    intro he
    apply hwnA₀
    rw [he]
    exact hwA₁
  have hW : Nat.card (Hyp1281Two.wOfU T M) = 16 := card_wOf c
  have hdvd : 8 ∣ Nat.card ↥((VZ T M ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers w) := by
    rw [← hA₀card]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hle16 : Nat.card ↥((VZ T M ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers w) ≤ 16 := by
    rw [← hW]
    exact Subgroup.card_le_of_le hA₁W
  have hne8 : Nat.card ↥((VZ T M ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers w) ≠ 8 := by
    intro h8
    exact hne (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hA₀card, h8]))
  have hA₁card : Nat.card ↥((VZ T M ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers w) = 16 := by
    have hpos : Nat.card ↥((VZ T M ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers w) > 0 :=
      Nat.card_pos
    omega
  have hA₁eq : (VZ T M ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers w = Hyp1281Two.wOfU T M :=
    Subgroup.eq_of_le_of_card_ge hA₁W (by rw [hW, hA₁card])
  have hWC : Hyp1281Two.wOfU T M ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [← hA₁eq]
    exact hA₁C.trans inf_le_right
  have hcen : r ∈ centerOf (Hyp1281Two.wOfU T M) :=
    ⟨hrW, Subgroup.mem_centralizer_iff.mpr fun w' hw' =>
      (Subgroup.mem_centralizer_iff.mp (hWC hw') r (Set.mem_singleton r)).symm⟩
  rw [c.centerOf_wOfU_eq_VZ] at hcen
  exact hrV hcen

theorem Counter.comm_r_r'_ne_one (htRQ : t ∉ rOf T M ⊔ qOf T) :
    r * (t⁻¹ * r * t) * r⁻¹ * (t⁻¹ * r * t)⁻¹ ≠ 1 := by
  have hr'W := c.conj_mem_wOfU hrW htT
  have hr'V := c.conj_not_mem_VZ hrV htT
  have hr'A : t⁻¹ * r * t ∈ conjSubgroup (c.Ac hrW hrV hr2) t := by
    refine mem_conjSubgroup_iff.mpr ?_
    have e : t * (t⁻¹ * r * t) * t⁻¹ = r := by group
    rw [e]
    exact c.r_mem_Ac hrW hrV hr2
  have hr'nA : t⁻¹ * r * t ∉ c.Ac hrW hrV hr2 := by
    intro hmem
    apply hr'V
    have : t⁻¹ * r * t ∈ c.Ac hrW hrV hr2 ⊓ conjSubgroup (c.Ac hrW hrV hr2) t := ⟨hmem, hr'A⟩
    rwa [c.Ac_inf_conj hrW hrV hr2 htT htRQ] at this
  exact c.comm_ne_of_not_mem_Ac hrW hrV hr2 hr'W hr'nA

omit htT in
theorem Counter.comm_ne_one_aux {r' : G} (hr'W : r' ∈ Hyp1281Two.wOfU T M) (hr'V : r' ∉ VZ T M)
    (hr'2 : r' * r' = 1) (h0 : r * r' * r⁻¹ * r'⁻¹ ≠ 1) :
    r * (g * r' * g⁻¹) * r⁻¹ * (g * r' * g⁻¹)⁻¹ ≠ 1 ∧
      r * (g * g * r' * (g * g)⁻¹) * r⁻¹ * (g * g * r' * (g * g)⁻¹)⁻¹ ≠ 1 := by
  have h := c.h1281
  obtain ⟨u, huU, huW⟩ := exists_mem_U_not_mem_W h c.nonab
  have hrR : r ∈ rOf T M := c.mem_rOf_of_mem_wOfU hrW
  have hr'R : r' ∈ rOf T M := c.mem_rOf_of_mem_wOfU hr'W
  have hgM : g ∈ M := h.le c.goodElt.mem
  have hgN : g ∈ Subgroup.normalizer (rOf T M : Set G) := M_le_normalizer_rOf c hgM
  have hr1R : g * r' * g⁻¹ ∈ rOf T M := (Subgroup.mem_normalizer_iff.mp hgN r').mp hr'R
  have hr2R : g * g * r' * (g * g)⁻¹ ∈ rOf T M := by
    have := (Subgroup.mem_normalizer_iff.mp hgN _).mp hr1R
    have e : g * (g * r' * g⁻¹) * g⁻¹ = g * g * r' * (g * g)⁻¹ := by group
    rwa [e] at this
  have hVc : ∀ e ∈ VZ T M, ∀ s ∈ rOf T M, e * s = s * e := fun e he s hs => c.rOf_comm_VZ hs he
  have hVR : VZ T M ≤ rOf T M := (c.VZ_le_Ac hrW hrV hr2).trans (c.Ac_le_rOf hrW hrV hr2)
  have hcommV : ∀ a ∈ rOf T M, ∀ b ∈ rOf T M, a * b * a⁻¹ * b⁻¹ ∈ VZ T M := by
    intro a ha b hb
    have := h.commutator_mem_inf_of_mem_pCoreOf c.nonab c.goodElt
      (by rw [← rOf_eq_pCoreOf_sup c]; exact ha) (by rw [← rOf_eq_pCoreOf_sup c]; exact hb)
    rwa [E_eq_VZ c] at this
  have UD := c.udata hrW hrV hr2 huU huW
  have UD' := c.udata hr'W hr'V hr'2 huU huW
  set r1 : G := g * r' * g⁻¹ with hr1def
  set r2 : G := g * g * r' * (g * g)⁻¹ with hr2def
  have hf₁ : (u * r * u⁻¹)⁻¹ * r ∈ VZ T M := by
    have := (c.kdata hrW hrV hr2).conj_r UD
    rwa [E_eq_VZ c] at this
  have hf₂ : (u * r1 * u⁻¹)⁻¹ * r2 ∈ VZ T M := by
    have := c.quotSetting.normal
    have h2 := (c.kdata hr'W hr'V hr'2).conj_r1 UD'
    rwa [E_eq_VZ c] at h2
  set f₁ : G := (u * r * u⁻¹)⁻¹ * r with hf₁def
  set f₂ : G := (u * r1 * u⁻¹)⁻¹ * r2 with hf₂def
  have hur : u * r * u⁻¹ = r * f₁⁻¹ := by rw [hf₁def]; group
  have hur1 : u * r1 * u⁻¹ = r2 * f₂⁻¹ := by rw [hf₂def]; group
  have hu : u * (r * r1 * r⁻¹ * r1⁻¹) * u⁻¹ = r * r2 * r⁻¹ * r2⁻¹ := by
    calc u * (r * r1 * r⁻¹ * r1⁻¹) * u⁻¹
        = (u * r * u⁻¹) * (u * r1 * u⁻¹) * (u * r * u⁻¹)⁻¹ * (u * r1 * u⁻¹)⁻¹ := by group
      _ = (r * f₁⁻¹) * (r2 * f₂⁻¹) * (r * f₁⁻¹)⁻¹ * (r2 * f₂⁻¹)⁻¹ := by rw [hur, hur1]
      _ = r * r2 * r⁻¹ * r2⁻¹ :=
        comm_mul_central (hVc _ ((VZ T M).inv_mem hf₁) _ hr2R) (hVc _ ((VZ T M).inv_mem hf₂) _ hrR)
          (hVc _ ((VZ T M).inv_mem hf₁) _ (hVR ((VZ T M).inv_mem hf₂)))
  have hn := c.norm_mem_VZ hr'W hr'V hr'2
  have hr12 : r1 * r2 = r'⁻¹ * (r' * r1 * r2) := by group
  have hy2V : r * r2 * r⁻¹ * r2⁻¹ ∈ VZ T M := hcommV r hrR r2 hr2R
  have hbil : r * (r1 * r2) * r⁻¹ * (r1 * r2)⁻¹ =
      (r * r1 * r⁻¹ * r1⁻¹) * (r * r2 * r⁻¹ * r2⁻¹) := comm_mul_right (hVc _ hy2V _ hr1R)
  have hr'inv : r'⁻¹ = r' := inv_eq_of_mul_eq_one_right hr'2
  have hcent : r * (r'⁻¹ * (r' * r1 * r2)) * r⁻¹ * (r'⁻¹ * (r' * r1 * r2))⁻¹ =
      r * r'⁻¹ * r⁻¹ * r'⁻¹⁻¹ := by
    have := comm_mul_central (a := r) (b := r'⁻¹) (e₁ := 1) (e₂ := r' * r1 * r2)
      (by simp) (hVc _ hn _ hrR) (by simp)
    simpa using this
  have hprod : (r * r1 * r⁻¹ * r1⁻¹) * (r * r2 * r⁻¹ * r2⁻¹) = r * r' * r⁻¹ * r'⁻¹ := by
    rw [← hbil, hr12, hcent, inv_inv, hr'inv]
  constructor
  · intro hy1
    apply h0
    have hy2 : r * r2 * r⁻¹ * r2⁻¹ = 1 := by rw [← hu, hy1]; group
    rw [← hprod, hy1, hy2, one_mul]
  · intro hy2
    apply h0
    have hy1 : r * r1 * r⁻¹ * r1⁻¹ = 1 := by
      have : u * (r * r1 * r⁻¹ * r1⁻¹) * u⁻¹ = 1 := by rw [hu, hy2]
      have e : r * r1 * r⁻¹ * r1⁻¹ = u⁻¹ * (u * (r * r1 * r⁻¹ * r1⁻¹) * u⁻¹) * u := by group
      rw [e, this]; group
    rw [← hprod, hy1, hy2, one_mul]

theorem Counter.comm_r_ne_one_of_mem_conj (htRQ : t ∉ rOf T M ⊔ qOf T) {a' : G}
    (ha' : a' ∈ conjSubgroup (c.Ac hrW hrV hr2) t) (ha'V : a' ∉ VZ T M) :
    r * a' * r⁻¹ * a'⁻¹ ≠ 1 := by
  have hr'W := c.conj_mem_wOfU hrW htT
  have hr'V := c.conj_not_mem_VZ hrV htT
  have hr'2 : (t⁻¹ * r * t) * (t⁻¹ * r * t) = 1 := Counter.conj_sq hr2
  have h0 := c.comm_r_r'_ne_one hrW hrV hr2 htT htRQ
  obtain ⟨h1, h2⟩ := c.comm_ne_one_aux hrW hrV hr2 hr'W hr'V hr'2 h0
  have hrR := c.mem_rOf_of_mem_wOfU hrW
  have hVc : ∀ e ∈ VZ T M, ∀ s ∈ rOf T M, e * s = s * e := fun e he s hs => c.rOf_comm_VZ hs he
  rw [← c.Ac_conj_eq hrW hrV hr2 htT] at ha'
  obtain ⟨e, he, hcases⟩ := c.mem_Ac_cases hr'W hr'V hr'2 ha'
  have key : ∀ b : G, ∀ e ∈ VZ T M, r * (b * e) * r⁻¹ * (b * e)⁻¹ = r * b * r⁻¹ * b⁻¹ :=
    fun b e he => by
      have := comm_mul_central (a := r) (b := b) (e₁ := 1) (e₂ := e) (by simp)
        (hVc e he r hrR) (by simp)
      simpa using this
  rcases hcases with rfl | rfl | rfl | rfl
  · exact absurd he ha'V
  · rw [key _ _ he]; exact h0
  · rw [key _ _ he]; exact h1
  · rw [key _ _ he]; exact h2

omit hrW hrV hr2 htT in
theorem Counter.iTwo_le_M : iTwo T M ≤ M := by
  rw [iTwo_eq c.h1281 c.nonab]
  exact sup_le c.h1281.le (c.h1281.uOfL22_le_T.trans c.hyp.m_max.1.2)

theorem Counter.not_comm_of_mem (htRQ : t ∉ rOf T M ⊔ qOf T) {a a' : G}
    (ha : a ∈ c.Ac hrW hrV hr2) (haV : a ∉ VZ T M)
    (ha' : a' ∈ conjSubgroup (c.Ac hrW hrV hr2) t) (ha'V : a' ∉ VZ T M) : a * a' ≠ a' * a := by
  intro hcomm
  have h := c.h1281
  have hrR := c.mem_rOf_of_mem_wOfU hrW
  have hVc : ∀ e ∈ VZ T M, ∀ s ∈ rOf T M, e * s = s * e := fun e he s hs => c.rOf_comm_VZ hs he
  have hgI : g ∈ iTwo T M := c.g_mem_iTwo
  have hVI : ∀ γ ∈ iTwo T M, ∀ v ∈ VZ T M, γ * v * γ⁻¹ ∈ VZ T M := by
    intro γ hγ v hv
    have hγN : γ ∈ Subgroup.normalizer (VZ T M : Set G) := by
      rw [h.normalizer_VZ]; exact c.iTwo_le_M hγ
    exact (Subgroup.mem_normalizer_iff.mp hγN v).mp hv
  have hmain : ∀ e' ∈ VZ T M, ∀ b ∈ conjSubgroup (c.Ac hrW hrV hr2) t, b ∉ VZ T M →
      (r * e') * b = b * (r * e') → False := by
    intro e' he' b hb hbV hc
    have hcb : e' * b = b * e' := hVc e' he' b (c.conjAc_le_rOf hrW hrV hr2 htT hb)
    have hrb : r * b = b * r := by
      have h1 : (r * e') * b = (r * b) * e' := by rw [mul_assoc, hcb, ← mul_assoc]
      have h2 : b * (r * e') = (b * r) * e' := by rw [mul_assoc]
      rw [h1, h2] at hc
      exact mul_right_cancel hc
    apply c.comm_r_ne_one_of_mem_conj hrW hrV hr2 htT htRQ hb hbV
    calc r * b * r⁻¹ * b⁻¹ = (b * r) * r⁻¹ * b⁻¹ := by rw [hrb]
      _ = 1 := by group
  have hred : ∀ γ ∈ iTwo T M, (γ * a * γ⁻¹) * (γ * a' * γ⁻¹) = (γ * a' * γ⁻¹) * (γ * a * γ⁻¹) := by
    intro γ _
    calc (γ * a * γ⁻¹) * (γ * a' * γ⁻¹) = γ * (a * a') * γ⁻¹ := by group
      _ = γ * (a' * a) * γ⁻¹ := by rw [hcomm]
      _ = (γ * a' * γ⁻¹) * (γ * a * γ⁻¹) := by group
  have hnotV : ∀ γ ∈ iTwo T M, γ * a' * γ⁻¹ ∉ VZ T M := by
    intro γ hγ hmem
    apply ha'V
    have := hVI γ⁻¹ ((iTwo T M).inv_mem hγ) _ hmem
    simpa [mul_assoc] using this
  obtain ⟨e, he, hcases⟩ := c.mem_Ac_cases hrW hrV hr2 ha
  rcases hcases with rfl | rfl | rfl | rfl
  · exact haV he
  · exact hmain e he a' ha' ha'V hcomm
  ·
    have hginv : g⁻¹ ∈ iTwo T M := (iTwo T M).inv_mem hgI
    have e1 : g⁻¹ * (g * r * g⁻¹ * e) * g⁻¹⁻¹ = r * (g⁻¹ * e * g⁻¹⁻¹) := by group
    have h1 := hred g⁻¹ hginv
    rw [e1] at h1
    exact hmain _ (hVI g⁻¹ hginv e he) _ (c.conjAc_conj_mem hrW hrV hr2 htT hginv ha')
      (hnotV g⁻¹ hginv) h1
  · have hginv : (g * g)⁻¹ ∈ iTwo T M := (iTwo T M).inv_mem ((iTwo T M).mul_mem hgI hgI)
    have e1 : (g * g)⁻¹ * (g * g * r * (g * g)⁻¹ * e) * (g * g)⁻¹⁻¹ =
        r * ((g * g)⁻¹ * e * (g * g)⁻¹⁻¹) := by group
    have h1 := hred (g * g)⁻¹ hginv
    rw [e1] at h1
    exact hmain _ (hVI _ hginv e he) _ (c.conjAc_conj_mem hrW hrV hr2 htT hginv ha')
      (hnotV _ hginv) h1

theorem Counter.maximal_Ac (htRQ : t ∉ rOf T M ⊔ qOf T) {B : Subgroup G} (hB : B ≤ rOf T M)
    (hBe : IsElemAbelian 2 B) :
    B ≤ c.Ac hrW hrV hr2 ∨ B ≤ conjSubgroup (c.Ac hrW hrV hr2) t := by
  apply le_or_le_of_forall_mem
  intro x hxB
  have hxR := hB hxB
  have hx2 : x * x = 1 := by have := hBe.2 x hxB; rwa [sq] at this
  have hAiTwo : c.Ac hrW hrV hr2 ≤ iTwo T M := (c.Ac_le_rOf hrW hrV hr2).trans
    (pCoreOf_le 2 (iTwo T M))
  have hAN : c.Ac hrW hrV hr2 ≤ Subgroup.normalizer (conjSubgroup (c.Ac hrW hrV hr2) t : Set G) :=
    fun γ hγ => by
      refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
      · exact c.conjAc_conj_mem hrW hrV hr2 htT (hAiTwo hγ) hy
      · have := c.conjAc_conj_mem hrW hrV hr2 htT ((iTwo T M).inv_mem (hAiTwo hγ)) hy
        simpa using this
  rw [← c.Ac_sup_conj hrW hrV hr2 htT htRQ, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hxR
  obtain ⟨a, ha, a', ha', hxa⟩ := Set.mem_mul.mp hxR
  subst hxa
  by_cases haV : a ∈ VZ T M
  · right
    exact (conjSubgroup (c.Ac hrW hrV hr2) t).mul_mem (c.VZ_le_conjAc hrW hrV hr2 htT haV) ha'
  by_cases ha'V : a' ∈ VZ T M
  · left
    exact (c.Ac hrW hrV hr2).mul_mem ha (c.VZ_le_Ac hrW hrV hr2 ha'V)
  exfalso
  apply c.not_comm_of_mem hrW hrV hr2 htT htRQ ha haV ha' ha'V
  have h3 : a * a' = (a * a')⁻¹ := eq_inv_of_mul_eq_one_left hx2
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (c.sq_Ac hrW hrV hr2 ha),
    inv_eq_of_mul_eq_one_right (c.sq_conjAc hrW hrV hr2 ha')] at h3
  exact h3

end Normalizer

end S143

end CFSG.Quasithin
