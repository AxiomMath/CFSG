module

public import CFSG.Quasithin.EmptyFaithful.S143KB
public import CFSG.Quasithin.EmptyFaithful.S143FK

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

theorem cmat_r0 {G : Type*} [Group G] (e0 e1 e2 e3 γ : G) :
    (cmat e0 e1 e2 e3 γ).r0 = coordsOf e0 e1 e2 e3 (γ * e0 * γ⁻¹) := rfl

theorem cmat_r1 {G : Type*} [Group G] (e0 e1 e2 e3 γ : G) :
    (cmat e0 e1 e2 e3 γ).r1 = coordsOf e0 e1 e2 e3 (γ * e1 * γ⁻¹) := rfl

theorem cmat_r2 {G : Type*} [Group G] (e0 e1 e2 e3 γ : G) :
    (cmat e0 e1 e2 e3 γ).r2 = coordsOf e0 e1 e2 e3 (γ * e2 * γ⁻¹) := rfl

theorem cmat_r3 {G : Type*} [Group G] (e0 e1 e2 e3 γ : G) :
    (cmat e0 e1 e2 e3 γ).r3 = coordsOf e0 e1 e2 e3 (γ * e3 * γ⁻¹) := rfl

section Shapes

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

theorem Counter.commutator_rOf_Ac_mem {t : G} (htT : t ∈ T) (htRQ : t ∉ rOf T M ⊔ qOf T) {ρ e : G}
    (hρ : ρ ∈ rOf T M) (he : e ∈ c.Ac hrW hrV hr2) : ρ * e * ρ⁻¹ * e⁻¹ ∈ VZ T M := by
  have hAiTwo : c.Ac hrW hrV hr2 ≤ iTwo T M :=
    (c.Ac_le_rOf hrW hrV hr2).trans (pCoreOf_le 2 (iTwo T M))
  have hRiTwo : rOf T M ≤ iTwo T M := pCoreOf_le 2 (iTwo T M)
  have hAN : c.Ac hrW hrV hr2 ≤
      Subgroup.normalizer (conjSubgroup (c.Ac hrW hrV hr2) t : Set G) := fun γ hγ => by
    refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
    · exact c.conjAc_conj_mem hrW hrV hr2 htT (hAiTwo hγ) hy
    · have := c.conjAc_conj_mem hrW hrV hr2 htT ((iTwo T M).inv_mem (hAiTwo hγ)) hy
      simpa using this
  have hcomm : ∀ a ∈ c.Ac hrW hrV hr2, ∀ b ∈ c.Ac hrW hrV hr2, a * b = b * a := fun a ha b hb =>
    mul_comm_of_sq_eq_one (fun y hy => c.sq_Ac hrW hrV hr2 hy) ha hb
  rw [← c.Ac_sup_conj hrW hrV hr2 htT htRQ, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hρ
  obtain ⟨a₀, ha₀, a', ha', rfl⟩ := Set.mem_mul.mp hρ
  have ha'R : a' ∈ rOf T M := c.conjAc_le_rOf hrW hrV hr2 htT ha'
  have hfA : a' * e * a'⁻¹ ∈ c.Ac hrW hrV hr2 :=
    c.Ac_conj_mem hrW hrV hr2 (hRiTwo ha'R) he
  have e1 : a₀ * a' * e * (a₀ * a')⁻¹ * e⁻¹ = (a' * e * a'⁻¹) * e⁻¹ := by
    have h1 : a₀ * (a' * e * a'⁻¹) = (a' * e * a'⁻¹) * a₀ := hcomm a₀ ha₀ _ hfA
    calc a₀ * a' * e * (a₀ * a')⁻¹ * e⁻¹ = (a₀ * (a' * e * a'⁻¹) * a₀⁻¹) * e⁻¹ := by group
      _ = (a' * e * a'⁻¹) * e⁻¹ := by rw [h1]; group
  rw [e1, ← c.Ac_inf_conj hrW hrV hr2 htT htRQ]
  refine ⟨(c.Ac hrW hrV hr2).mul_mem hfA ((c.Ac hrW hrV hr2).inv_mem he), ?_⟩
  have h2 : e * a'⁻¹ * e⁻¹ ∈ conjSubgroup (c.Ac hrW hrV hr2) t :=
    c.conjAc_conj_mem hrW hrV hr2 htT (hAiTwo he) ((conjSubgroup (c.Ac hrW hrV hr2) t).inv_mem ha')
  have e2 : a' * e * a'⁻¹ * e⁻¹ = a' * (e * a'⁻¹ * e⁻¹) := by group
  rw [e2]
  exact (conjSubgroup (c.Ac hrW hrV hr2) t).mul_mem ha' h2

include c hrW hrV hr2

theorem Counter.commutator_Ac_mem_qOf {y : G} (hyH : y ∈ mcOf T)
    (hyN : y ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) {e : G}
    (he : e ∈ c.Ac hrW hrV hr2) : y * e * y⁻¹ * e⁻¹ ∈ qOf T := by
  have heH := c.Ac_le_mcOf hrW hrV hr2 he
  have hcomm := (c.mem_normalizer_Ac_iff hrW hrV hr2 ⟨y, hyH⟩).mp hyN
  have hqH : y * e * y⁻¹ * e⁻¹ ∈ mcOf T :=
    (mcOf T).mul_mem ((mcOf T).mul_mem ((mcOf T).mul_mem hyH heH) ((mcOf T).inv_mem hyH))
      ((mcOf T).inv_mem heH)
  apply c.mem_qOf_of_actK_eq_one (x := ⟨y * e * y⁻¹ * e⁻¹, hqH⟩)
  have : (⟨y * e * y⁻¹ * e⁻¹, hqH⟩ : ↥(mcOf T)) =
      ⟨y, hyH⟩ * ⟨e, heH⟩ * ⟨y, hyH⟩⁻¹ * ⟨e, heH⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_mul, map_inv, map_inv]
  rcases c.actK_Ac hrW hrV hr2 he with h | h
  · rw [h]; group
  · rw [h]
    calc c.actK ⟨y, hyH⟩ * c.alphaOf hrW hrV hr2 * (c.actK ⟨y, hyH⟩)⁻¹ * (c.alphaOf hrW hrV hr2)⁻¹
        = (c.alphaOf hrW hrV hr2 * c.actK ⟨y, hyH⟩) * (c.actK ⟨y, hyH⟩)⁻¹ *
            (c.alphaOf hrW hrV hr2)⁻¹ := by rw [hcomm]
      _ = 1 := by group

variable {c hrW hrV hr2}

variable {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1)

include hS

theorem Setup.x_iTwo : x ∈ iTwo T M := by
  rw [iTwo_eq c.h1281 c.nonab]; exact Subgroup.mem_sup_left hS.x_mem

theorem Setup.x_cube : x * x * x = 1 := by
  rw [← pow_three', ← hS.x_ord]; exact pow_orderOf_eq_one x

theorem Setup.z_V : z ∈ VZ T M := Hyp1281Two.omegaOneCenter_le_VZ T M hS.z_mem

theorem Setup.z_A : z ∈ c.Ac hrW hrV hr2 := c.VZ_le_Ac hrW hrV hr2 hS.z_V

theorem Setup.a_V : a ∈ VZ T M := by
  rw [hS.a_def]
  exact (Subgroup.mem_normalizer_iff.mp (c.iTwo_le_normalizer_VZ hS.x_iTwo) z).mp hS.z_V

theorem Setup.a_A : a ∈ c.Ac hrW hrV hr2 := c.VZ_le_Ac hrW hrV hr2 hS.a_V

theorem Setup.r1_A : r1 ∈ c.Ac hrW hrV hr2 := by
  rw [hS.r1_def]; exact c.Ac_conj_mem hrW hrV hr2 hS.x_iTwo (c.r_mem_Ac hrW hrV hr2)

theorem Setup.coords_V {e : G} (he : e ∈ VZ T M) :
    (coordsOf z a r r1 e).x2 = false ∧ (coordsOf z a r r1 e).x3 = false := by
  have hB := hS.basis
  rcases hS.V_cases e he with rfl | rfl | rfl | rfl
  · rw [hB.coordsOf_one]; exact ⟨rfl, rfl⟩
  · rw [hB.coordsOf_e0]; exact ⟨rfl, rfl⟩
  · rw [hB.coordsOf_e1]; exact ⟨rfl, rfl⟩
  · rw [hB.coordsOf_mul hS.z_A hS.a_A, hB.coordsOf_e0, hB.coordsOf_e1]; exact ⟨rfl, rfl⟩

theorem Setup.cmat_x : cmat z a r r1 x = Mx := by
  have hB := hS.basis
  have hcomm := hB.comm
  have hsq := hB.sq
  have hx3 := hS.x_cube
  have hfpf := hS.x_fpf
  have t1 := c.trace_eq_one hrW hrV hr2 hS.x_iTwo hx3 hfpf hS.z_A
  have t2 := c.trace_eq_one hrW hrV hr2 hS.x_iTwo hx3 hfpf (c.r_mem_Ac hrW hrV hr2)
  have e0 : x * z * x⁻¹ = a := hS.a_def.symm
  have e2 : x * r * x⁻¹ = r1 := hS.r1_def.symm
  have hxa : x * a * x⁻¹ = z * a := by
    have h1 : x * x * z * (x * x)⁻¹ = x * a * x⁻¹ := by rw [hS.a_def]; group
    rw [e0, h1] at t1
    rw [eq_inv_of_mul_eq_one_right t1]
    exact inv_eq_of_mul_eq_one_right (hsq _ ((c.Ac hrW hrV hr2).mul_mem hS.z_A hS.a_A))
  have hxr1 : x * r1 * x⁻¹ = r * r1 := by
    have h1 : x * x * r * (x * x)⁻¹ = x * r1 * x⁻¹ := by rw [hS.r1_def]; group
    rw [e2, h1] at t2
    rw [eq_inv_of_mul_eq_one_right t2]
    exact inv_eq_of_mul_eq_one_right (hsq _ ((c.Ac hrW hrV hr2).mul_mem (c.r_mem_Ac hrW hrV hr2) hS.r1_A))
  show (⟨coordsOf z a r r1 (x * z * x⁻¹), coordsOf z a r r1 (x * a * x⁻¹),
    coordsOf z a r r1 (x * r * x⁻¹), coordsOf z a r r1 (x * r1 * x⁻¹)⟩ : Mat4) = Mx
  rw [e0, hxa, e2, hxr1, hB.coordsOf_e1, hB.coordsOf_mul hS.z_A hS.a_A, hB.coordsOf_e0,
    hB.coordsOf_e1, hB.coordsOf_e3, hB.coordsOf_mul (c.r_mem_Ac hrW hrV hr2) hS.r1_A, hB.coordsOf_e2, hB.coordsOf_e3]
  rfl

theorem Setup.coords_Z {e : G} (he : e ∈ quasithinOmegaOneCenter T) :
    (coordsOf z a r r1 e).x1 = false ∧ (coordsOf z a r r1 e).x2 = false ∧
      (coordsOf z a r r1 e).x3 = false := by
  have hB := hS.basis
  rcases c.mem_Z_cases hS.z_mem hS.z_ne he with rfl | rfl
  · rw [hB.coordsOf_one]; exact ⟨rfl, rfl, rfl⟩
  · rw [hB.coordsOf_e0]; exact ⟨rfl, rfl, rfl⟩

theorem Setup.coords_x3_of_mem_Q {e : G} (he : e ∈ c.Ac hrW hrV hr2) (heQ : e ∈ qOf T) :
    (coordsOf z a r r1 e).x3 = false := by
  have hB := hS.basis
  obtain ⟨v, hv, hcases⟩ := c.mem_Ac_cases hrW hrV hr2 he
  have hvQ : v ∈ qOf T := c.wOfU_le_qOf (Hyp1281Two.VZ_le_wOfU c.h1281 hv)
  have hrQ : r ∈ qOf T := c.wOfU_le_qOf hrW
  have hvA : v ∈ c.Ac hrW hrV hr2 := c.VZ_le_Ac hrW hrV hr2 hv
  rcases hcases with rfl | rfl | h | h
  · exact (hS.coords_V hv).2
  · rw [hB.coordsOf_mul (c.r_mem_Ac hrW hrV hr2) hvA, hB.coordsOf_e2]
    simp [V4.add, (hS.coords_V hv).2]
  · exfalso
    apply c.r1_not_mem_qOf hrW hrV hr2
    have : g * r * g⁻¹ = e * v⁻¹ := by rw [h]; group
    rw [this]
    exact (qOf T).mul_mem heQ ((qOf T).inv_mem hvQ)
  · exfalso
    apply c.r1_not_mem_qOf hrW hrV hr2
    have hn := c.norm_mem_VZ hrW hrV hr2
    have hnQ : r * (g * r * g⁻¹) * (g * g * r * (g * g)⁻¹) ∈ qOf T :=
      c.wOfU_le_qOf (Hyp1281Two.VZ_le_wOfU c.h1281 hn)
    have hr2Q : g * g * r * (g * g)⁻¹ ∈ qOf T := by
      have : g * g * r * (g * g)⁻¹ = e * v⁻¹ := by rw [h]; group
      rw [this]
      exact (qOf T).mul_mem heQ ((qOf T).inv_mem hvQ)
    have : g * r * g⁻¹ = r⁻¹ * (r * (g * r * g⁻¹) * (g * g * r * (g * g)⁻¹)) *
        (g * g * r * (g * g)⁻¹)⁻¹ := by group
    rw [this]
    exact (qOf T).mul_mem ((qOf T).mul_mem ((qOf T).inv_mem hrQ) hnQ) ((qOf T).inv_mem hr2Q)

theorem Setup.isRMat_cmat {t : G} (htT : t ∈ T) (htRQ : t ∉ rOf T M ⊔ qOf T) {ρ : G}
    (hρ : ρ ∈ rOf T M) : IsRMat (cmat z a r r1 ρ) := by
  have hB := hS.basis
  have hVA := c.VZ_le_Ac hrW hrV hr2
  have hzc : ρ * z * ρ⁻¹ = z := by rw [← c.rOf_comm_VZ hρ hS.z_V]; group
  have hac : ρ * a * ρ⁻¹ = a := by rw [← c.rOf_comm_VZ hρ hS.a_V]; group
  obtain ⟨e2, he2V, he2⟩ : ∃ e ∈ VZ T M, ρ * r * ρ⁻¹ = e * r :=
    ⟨ρ * r * ρ⁻¹ * r⁻¹, c.commutator_rOf_Ac_mem hrW hrV hr2 htT htRQ hρ
      (c.r_mem_Ac hrW hrV hr2), by group⟩
  obtain ⟨e3, he3V, he3⟩ : ∃ e ∈ VZ T M, ρ * r1 * ρ⁻¹ = e * r1 :=
    ⟨ρ * r1 * ρ⁻¹ * r1⁻¹, c.commutator_rOf_Ac_mem hrW hrV hr2 htT htRQ hρ hS.r1_A, by group⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cmat_r0, hzc, hB.coordsOf_e0]
  · rw [cmat_r1, hac, hB.coordsOf_e1]
  · rw [cmat_r2, he2, hB.coordsOf_mul (hVA he2V) (c.r_mem_Ac hrW hrV hr2), hB.coordsOf_e2]
    simp [V4.add, (hS.coords_V he2V).1]
  · rw [cmat_r2, he2, hB.coordsOf_mul (hVA he2V) (c.r_mem_Ac hrW hrV hr2), hB.coordsOf_e2]
    simp [V4.add, (hS.coords_V he2V).2]
  · rw [cmat_r3, he3, hB.coordsOf_mul (hVA he3V) hS.r1_A, hB.coordsOf_e3]
    simp [V4.add, (hS.coords_V he3V).1]
  · rw [cmat_r3, he3, hB.coordsOf_mul (hVA he3V) hS.r1_A, hB.coordsOf_e3]
    simp [V4.add, (hS.coords_V he3V).2]

theorem Setup.isUMat_cmat {u : G} (hu : u ∈ uOfL22 T M) : IsUMat (cmat z a r r1 u) := by
  have hB := hS.basis
  have huH : u ∈ mcOf T := c.h1281.uOfL22_le_g1 hu
  have huI : u ∈ iTwo T M := le_conjClosure _ _ hu
  have hzc : u * z * u⁻¹ = z := by
    rw [← Subgroup.mem_centralizer_iff.mp huH z hS.z_mem]; group
  have hZ : ∀ w ∈ uOfL22 T M, u * w * u⁻¹ * w⁻¹ ∈ quasithinOmegaOneCenter T := fun w hw =>
    c.h1281.commutator_mem_omegaOneCenter hu hw
  have haU : a ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M hS.a_V
  obtain ⟨ε1, hε1, he1⟩ : ∃ ε ∈ quasithinOmegaOneCenter T, u * a * u⁻¹ = ε * a :=
    ⟨u * a * u⁻¹ * a⁻¹, hZ a haU, by group⟩
  obtain ⟨ε2, hε2, he2⟩ : ∃ ε ∈ quasithinOmegaOneCenter T, u * r * u⁻¹ = ε * r :=
    ⟨u * r * u⁻¹ * r⁻¹, hZ r hrW.1, by group⟩
  have hε1A : ε1 ∈ c.Ac hrW hrV hr2 := c.VZ_le_Ac hrW hrV hr2
    (Hyp1281Two.omegaOneCenter_le_VZ T M hε1)
  have hε2A : ε2 ∈ c.Ac hrW hrV hr2 := c.VZ_le_Ac hrW hrV hr2
    (Hyp1281Two.omegaOneCenter_le_VZ T M hε2)
  have hr1R : r1 ∈ rOf T M := c.Ac_le_rOf hrW hrV hr2 hS.r1_A
  have hr1N : r1 ∈ Subgroup.normalizer (uOfL22 T M : Set G) := c.hHU (rOf_le_mcOf c hr1R)
  have hfU : u * r1 * u⁻¹ * r1⁻¹ ∈ uOfL22 T M := by
    have h1 : r1 * u⁻¹ * r1⁻¹ ∈ uOfL22 T M :=
      (Subgroup.mem_normalizer_iff.mp hr1N u⁻¹).mp ((uOfL22 T M).inv_mem hu)
    have e : u * r1 * u⁻¹ * r1⁻¹ = u * (r1 * u⁻¹ * r1⁻¹) := by group
    rw [e]; exact (uOfL22 T M).mul_mem hu h1
  have hfA : u * r1 * u⁻¹ * r1⁻¹ ∈ c.Ac hrW hrV hr2 :=
    (c.Ac hrW hrV hr2).mul_mem (c.Ac_conj_mem hrW hrV hr2 huI hS.r1_A)
      ((c.Ac hrW hrV hr2).inv_mem hS.r1_A)
  have hf3 := hS.coords_x3_of_mem_Q hfA (uOfL22_le_qOf c hfU)
  have e3 : u * r1 * u⁻¹ = (u * r1 * u⁻¹ * r1⁻¹) * r1 := by group
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cmat_r0, hzc, hB.coordsOf_e0]
  · rw [cmat_r1, he1, hB.coordsOf_mul hε1A hS.a_A, hB.coordsOf_e1]
    simp [V4.add, (hS.coords_Z hε1).1]
  · rw [cmat_r1, he1, hB.coordsOf_mul hε1A hS.a_A, hB.coordsOf_e1]
    simp [V4.add, (hS.coords_Z hε1).2.1]
  · rw [cmat_r1, he1, hB.coordsOf_mul hε1A hS.a_A, hB.coordsOf_e1]
    simp [V4.add, (hS.coords_Z hε1).2.2]
  · rw [cmat_r2, he2, hB.coordsOf_mul hε2A (c.r_mem_Ac hrW hrV hr2), hB.coordsOf_e2]
    simp [V4.add, (hS.coords_Z hε2).1]
  · rw [cmat_r2, he2, hB.coordsOf_mul hε2A (c.r_mem_Ac hrW hrV hr2), hB.coordsOf_e2]
    simp [V4.add, (hS.coords_Z hε2).2.1]
  · rw [cmat_r2, he2, hB.coordsOf_mul hε2A (c.r_mem_Ac hrW hrV hr2), hB.coordsOf_e2]
    simp [V4.add, (hS.coords_Z hε2).2.2]
  · rw [cmat_r3, e3, hB.coordsOf_mul hfA hS.r1_A, hB.coordsOf_e3]
    simp [V4.add, hf3]

theorem Setup.isYMat_cmat {y : G} (hyH : y ∈ mcOf T)
    (hyN : y ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) : IsYMat (cmat z a r r1 y) := by
  have hB := hS.basis
  have hQn : mcOf T ≤ Subgroup.normalizer (qOf T : Set G) := le_normalizer_pCoreOf 2 _
  have hzc : y * z * y⁻¹ = z := by
    rw [← Subgroup.mem_centralizer_iff.mp hyH z hS.z_mem]; group
  have haQ : a ∈ qOf T := c.wOfU_le_qOf (Hyp1281Two.VZ_le_wOfU c.h1281 hS.a_V)
  have hrQ : r ∈ qOf T := c.wOfU_le_qOf hrW
  have h1 := hS.coords_x3_of_mem_Q (conj_mem_of_mem_normalizer hyN hS.a_A)
    ((Subgroup.mem_normalizer_iff.mp (hQn hyH) a).mp haQ)
  have h2 := hS.coords_x3_of_mem_Q (conj_mem_of_mem_normalizer hyN (c.r_mem_Ac hrW hrV hr2))
    ((Subgroup.mem_normalizer_iff.mp (hQn hyH) r).mp hrQ)
  have hfA : y * r1 * y⁻¹ * r1⁻¹ ∈ c.Ac hrW hrV hr2 :=
    (c.Ac hrW hrV hr2).mul_mem (conj_mem_of_mem_normalizer hyN hS.r1_A)
      ((c.Ac hrW hrV hr2).inv_mem hS.r1_A)
  have hf3 := hS.coords_x3_of_mem_Q hfA (c.commutator_Ac_mem_qOf hrW hrV hr2 hyH hyN hS.r1_A)
  have e3 : y * r1 * y⁻¹ = (y * r1 * y⁻¹ * r1⁻¹) * r1 := by group
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cmat_r0, hzc, hB.coordsOf_e0]
  · rw [cmat_r1]; exact h1
  · rw [cmat_r2]; exact h2
  · rw [cmat_r3, e3, hB.coordsOf_mul hfA hS.r1_A, hB.coordsOf_e3]
    simp [V4.add, hf3]

end Shapes

end S143

end CFSG.Quasithin
