module

public import CFSG.Quasithin.EmptyFaithful.S143Struct
public import CFSG.Quasithin.Background.G12Stmts
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabEleven
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatImg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143V

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

section

theorem exists_zgen_sq (h : Hyp1281Two G T M L) :
    ∃ z : G, z ∈ quasithinOmegaOneCenter T ∧ z ≠ 1 ∧ z * z = 1 ∧
      ∀ w ∈ quasithinOmegaOneCenter T, w = 1 ∨ w = z := by
  obtain ⟨z, hzZ, hz1, hall⟩ := h.exists_zgen
  refine ⟨z, hzZ, hz1, ?_, hall⟩
  rcases hall (z * z) ((quasithinOmegaOneCenter T).mul_mem hzZ hzZ) with h1 | h1
  · exact h1
  · exfalso
    apply hz1
    have : z * z = z * 1 := by rw [h1, mul_one]
    exact mul_left_cancel this

theorem centralizerHat_le_T (h : Hyp1281Two G T M L) (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T) :
    Hyp1281Two.centralizerHat T M ≤ T := by
  have h4 := Hyp1281Two.lemma_12_8_4_four h h.isHz_centralizer
  have e : Hyp1281Two.centralizerHat T M = pCoreOf 2 (mcOf T) := by
    unfold Hyp1281Two.centralizerHat
    rw [hZU]
    exact h4
  rw [e]
  exact S143.qOf_le_T_of_hyp h

end

section Quad

variable (h : Hyp1281Two G T M L) (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T)
  (D : HatModel T M)

open scoped Classical in
@[expose] noncomputable def qhat (v : D.V) : ZMod 2 := if (D.rep v) ^ 2 = 1 then 0 else 1

open scoped Classical in
include h in
theorem ind_mul_of_mem_Z (a b : G) (ha : a ∈ quasithinOmegaOneCenter T)
    (hb : b ∈ quasithinOmegaOneCenter T) :
    (if a * b = 1 then (0 : ZMod 2) else 1) =
      (if a = 1 then (0 : ZMod 2) else 1) + (if b = 1 then (0 : ZMod 2) else 1) := by
  obtain ⟨z, hzZ, hz1, hzz, hall⟩ := exists_zgen_sq h
  rcases hall a ha with rfl | rfl <;> rcases hall b hb with rfl | rfl
  · simp
  · simp [hz1]
  · simp [hz1]
  · simp [hzz, hz1]
    decide

open scoped Classical in
include h hZU in
theorem qhat_π {u : G} (hu : u ∈ uOfL22 T M) :
    qhat D (D.π u) = if u ^ 2 = 1 then 0 else 1 := by
  set r := D.rep (D.π u) with hr
  have hrU : r ∈ uOfL22 T M := D.rep_mem _
  have hπ : D.π r = D.π u := D.π_rep _
  have hz : r⁻¹ * u ∈ centerOf (uOfL22 T M) := (D.π_eq_iff r hrU u hu).mp hπ
  rw [hZU] at hz
  obtain ⟨z, hzZ, hz1, hzz, hall⟩ := exists_zgen_sq h
  have hcom : r * (r⁻¹ * u) = (r⁻¹ * u) * r := by
    exact Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 hz).2 r hrU
  have hsq : u ^ 2 = r ^ 2 * (r⁻¹ * u) ^ 2 := by
    set c := r⁻¹ * u with hc
    have hu' : u = r * c := by rw [hc]; group
    calc u ^ 2 = u * u := pow_two u
      _ = (r * c) * (r * c) := by rw [← hu']
      _ = r * (c * r) * c := by group
      _ = r * (r * c) * c := by rw [← hcom]
      _ = r ^ 2 * c ^ 2 := by simp only [pow_two]; group
  have hc2 : (r⁻¹ * u) ^ 2 = 1 := by
    rcases hall _ hz with h1 | h1
    · rw [h1]; simp
    · rw [h1, pow_two]; exact hzz
  unfold qhat
  rw [← hr, hsq, hc2, mul_one]

open scoped Classical in
omit [Finite G] in
theorem B_eq_ind (D : HatModel T M) {u u' : G} (hu : u ∈ uOfL22 T M) (hu' : u' ∈ uOfL22 T M) :
    D.B (D.π u) (D.π u') = if u * u' * u⁻¹ * u'⁻¹ = 1 then 0 else 1 := by
  have hspec := D.B_spec u hu u' hu'
  by_cases hc : u * u' * u⁻¹ * u'⁻¹ = 1
  · simp only [hc, ite_true]
    exact hspec.mpr hc
  · simp only [hc, ite_false]
    have hne : D.B (D.π u) (D.π u') ≠ 0 := fun h0 => hc (hspec.mp h0)
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hne

open scoped Classical in
include h hZU in
theorem qhat_add (v w : D.V) : qhat D (v + w) = qhat D v + qhat D w + D.B v w := by
  obtain ⟨u, hu, rfl⟩ := D.π_surj v
  obtain ⟨u', hu', rfl⟩ := D.π_surj w
  have hmul : D.π u + D.π u' = D.π (u * u') := (D.π_mul u hu u' hu').symm
  rw [hmul, qhat_π h hZU D ((uOfL22 T M).mul_mem hu hu'), qhat_π h hZU D hu, qhat_π h hZU D hu',
    B_eq_ind D hu hu']
  have hd : u * u' * u⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T := h.commutator_mem_omegaOneCenter hu hu'
  have hu2 : u ^ 2 ∈ quasithinOmegaOneCenter T := h.sq_mem_omegaOneCenter hu
  have hu'2 : u' ^ 2 ∈ quasithinOmegaOneCenter T := h.sq_mem_omegaOneCenter hu'
  have hcomm2 : u' * u ^ 2 = u ^ 2 * u' := by
    have := Subgroup.mem_centralizer_iff.mp
      (h.omegaOneCenter_le_centerOf_uOfL22 hu2).2 u' hu'
    exact this
  have hsq : (u * u') ^ 2 = (u * u' * u⁻¹ * u'⁻¹) * (u ^ 2 * u' ^ 2) := by
    calc (u * u') ^ 2 = (u * u') * (u * u') := pow_two _
      _ = ((u * u' * u⁻¹ * u'⁻¹) * (u' * u)) * (u * u') := by group
      _ = (u * u' * u⁻¹ * u'⁻¹) * (u' * u ^ 2 * u') := by simp only [pow_two]; group
      _ = (u * u' * u⁻¹ * u'⁻¹) * (u ^ 2 * u' * u') := by rw [hcomm2]
      _ = (u * u' * u⁻¹ * u'⁻¹) * (u ^ 2 * u' ^ 2) := by simp only [pow_two]; group
  rw [hsq, ind_mul_of_mem_Z h _ _ hd ((quasithinOmegaOneCenter T).mul_mem hu2 hu'2),
    ind_mul_of_mem_Z h _ _ hu2 hu'2]
  ring

open scoped Classical in
include h hZU in
theorem img_le_orthSub : D.img (mcOf T) ≤ G11.orthSub (qhat D) := by
  intro γ hγ
  obtain ⟨x, hxH, hxN, rfl⟩ := HatModel.mem_img.mp hγ
  show ∀ v, qhat D (D.rho ⟨x, hxN⟩ v) = qhat D v
  intro v
  obtain ⟨u, hu, rfl⟩ := D.π_surj v
  rw [D.rho_π ⟨x, hxN⟩ hu]
  have hxu : x * u * x⁻¹ ∈ uOfL22 T M := HatModel.conj_mem_uOfL22 hxN hu
  rw [qhat_π h hZU D hxu, qhat_π h hZU D hu]
  have hu2 : u ^ 2 ∈ quasithinOmegaOneCenter T := h.sq_mem_omegaOneCenter hu
  have hx2 : (x * u * x⁻¹) ^ 2 = u ^ 2 := by
    have hcen : x * u ^ 2 = u ^ 2 * x := by
      have := Subgroup.mem_centralizer_iff.mp hxH (u ^ 2) hu2
      exact this.symm
    calc (x * u * x⁻¹) ^ 2 = x * u ^ 2 * x⁻¹ := by simp only [pow_two]; group
      _ = u ^ 2 * x * x⁻¹ := by rw [hcen]
      _ = u ^ 2 := by group
  rw [hx2]

end Quad

end S143V

end CFSG.Quasithin
