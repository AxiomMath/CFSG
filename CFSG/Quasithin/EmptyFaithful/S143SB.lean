module

public import CFSG.Quasithin.EmptyFaithful.S1422Extra
public import CFSG.Quasithin.EmptyFaithful.S143RC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

section Generic

variable {G : Type*} [Group G]

@[expose] def commSubgroup (A : Subgroup G) (w : G) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hwA : ∀ e ∈ A, w * e * w⁻¹ ∈ A) : Subgroup G where
  carrier := {v | ∃ e ∈ A, v = w * e * w⁻¹ * e⁻¹}
  mul_mem' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    refine ⟨e * e', A.mul_mem he he', ?_⟩
    have hc' : w * e' * w⁻¹ * e'⁻¹ ∈ A := A.mul_mem (hwA e' he') (A.inv_mem he')
    have h1 := hAc _ hc' e⁻¹ (A.inv_mem he)
    calc w * e * w⁻¹ * e⁻¹ * (w * e' * w⁻¹ * e'⁻¹)
        = w * e * w⁻¹ * (e⁻¹ * (w * e' * w⁻¹ * e'⁻¹)) := by group
      _ = w * e * w⁻¹ * ((w * e' * w⁻¹ * e'⁻¹) * e⁻¹) := by rw [← h1]
      _ = w * (e * e') * w⁻¹ * (e * e')⁻¹ := by group
  one_mem' := ⟨1, A.one_mem, by group⟩
  inv_mem' := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨e⁻¹, A.inv_mem he, ?_⟩
    have hc : w * e⁻¹ * w⁻¹ ∈ A := hwA e⁻¹ (A.inv_mem he)
    have h1 := hAc _ hc e he
    calc (w * e * w⁻¹ * e⁻¹)⁻¹ = e * w * e⁻¹ * w⁻¹ := by group
      _ = e * (w * e⁻¹ * w⁻¹) := by group
      _ = (w * e⁻¹ * w⁻¹) * e := by rw [← h1]
      _ = w * e⁻¹ * w⁻¹ * e⁻¹⁻¹ := by group

omit [Group G] in
theorem comm_mul_mem {G : Type*} [Group G] {V : Subgroup G} {A : Subgroup G} {ξ η : G}
    (hξ : ∀ v ∈ V, ξ * v * ξ⁻¹ ∈ V) (hξe : ∀ e ∈ A, ξ * e * ξ⁻¹ * e⁻¹ ∈ V)
    (hηe : ∀ e ∈ A, η * e * η⁻¹ * e⁻¹ ∈ V) :
    ∀ e ∈ A, (ξ * η) * e * (ξ * η)⁻¹ * e⁻¹ ∈ V := by
  intro e he
  have e1 : (ξ * η) * e * (ξ * η)⁻¹ * e⁻¹ =
      (ξ * (η * e * η⁻¹ * e⁻¹) * ξ⁻¹) * (ξ * e * ξ⁻¹ * e⁻¹) := by group
  rw [e1]
  exact V.mul_mem (hξ _ (hηe e he)) (hξe e he)

theorem conj_comm_identity {G : Type*} [Group G] (x δ e : G) :
    (x * δ * x⁻¹) * e * (x * δ * x⁻¹)⁻¹ * e⁻¹ =
      x * (δ * (x⁻¹ * e * x) * δ⁻¹ * (x⁻¹ * e * x)⁻¹) * x⁻¹ := by group

end Generic

section CommA

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t : G}
  (c : Counter T M g) (c18 : Concl14318 T M g A t)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
  {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3)

include c c18 hxL in
theorem x_normalizes_A : ∀ e ∈ A, x * e * x⁻¹ ∈ A := by
  have hxI : x ∈ iTwo T M := by rw [iTwo_eq c.h1281 c.nonab]; exact Subgroup.mem_sup_left hxL
  intro e he
  exact (Subgroup.mem_normalizer_iff.mp (c18.b.normal_A (Subgroup.mem_sup_left hxI)) e).mp he

include c c18 hxL in
theorem xinv_normalizes_A : ∀ e ∈ A, x⁻¹ * e * x ∈ A := by
  have hxI : x ∈ iTwo T M := by rw [iTwo_eq c.h1281 c.nonab]; exact Subgroup.mem_sup_left hxL
  intro e he
  have := (Subgroup.mem_normalizer_iff.mp
    ((Subgroup.normalizer _).inv_mem (c18.b.normal_A (Subgroup.mem_sup_left hxI))) e).mp he
  simpa using this

include c c18 hD in
theorem comm_d_mem_V : ∀ e ∈ A, d * e * d⁻¹ * e⁻¹ ∈ VZ T M := by
  intro e he
  have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  exact Hyp1281Two.omegaOneCenter_le_VZ T M (c.dOf_commutator_mem hd (c18.b.A_le he))

include c c18 hD hxL in
theorem comm_d1_mem_V : ∀ e ∈ A, (x * d * x⁻¹) * e * (x * d * x⁻¹)⁻¹ * e⁻¹ ∈ VZ T M := by
  intro e he
  have hxV : x ∈ Subgroup.normalizer (VZ T M : Set G) :=
    c.h1281.LT_le_normalizer_VZ (Subgroup.mem_sup_left hxL)
  have h1 := comm_d_mem_V c c18 hD _ (xinv_normalizes_A c c18 hxL e he)
  have h2 := (Subgroup.mem_normalizer_iff.mp hxV _).mp h1
  rw [conj_comm_identity]; exact h2

include c c18 hD hxL in
theorem comm_d2_mem_V : ∀ e ∈ A, (x * (x * d * x⁻¹) * x⁻¹) * e * (x * (x * d * x⁻¹) * x⁻¹)⁻¹ * e⁻¹ ∈
    VZ T M := by
  intro e he
  have hxV : x ∈ Subgroup.normalizer (VZ T M : Set G) :=
    c.h1281.LT_le_normalizer_VZ (Subgroup.mem_sup_left hxL)
  have h1 := comm_d1_mem_V c c18 hD hxL _ (xinv_normalizes_A c c18 hxL e he)
  have h2 := (Subgroup.mem_normalizer_iff.mp hxV _).mp h1
  rw [conj_comm_identity]; exact h2

include c c18 hD hd4 hxL in
theorem comm_w_mem_V : ∀ e ∈ A, wOfX d x * e * (wOfX d x)⁻¹ * e⁻¹ ∈ VZ T M := by
  have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have hc := Xgen_comm c hD hd4
  have h0 : d ∈ Xgen T M := le_Wgen (dOf_mem_delta c) hd
  have h1 := d1_mem_Xgen c hxL hd
  have h2 := d2_mem_Xgen c hxL hd
  have hV := VZ_le_Xgen c
  have hconj : ∀ ξ ∈ Xgen T M, ∀ v ∈ VZ T M, ξ * v * ξ⁻¹ ∈ VZ T M := by
    intro ξ hξ v hv
    have : ξ * v * ξ⁻¹ = v := by
      calc ξ * v * ξ⁻¹ = (v * ξ) * ξ⁻¹ := by rw [hc ξ hξ v (hV hv)]
        _ = v := by group
    rw [this]; exact hv
  have hd01 := comm_mul_mem (V := VZ T M) (A := A) (hconj d h0) (comm_d_mem_V c c18 hD)
    (comm_d1_mem_V c c18 hD hxL)
  have hw := comm_mul_mem (V := VZ T M) (A := A) (hconj (d * (x * d * x⁻¹))
    ((Xgen T M).mul_mem h0 h1)) hd01 (comm_d2_mem_V c c18 hD hxL)
  exact hw

omit [Finite G] in
theorem VZ_le_A (c18 : Concl14318 T M g A t) : VZ T M ≤ A := by
  rw [c18.b.v_eq_inf]; exact inf_le_left

include c c18 hD hd4 hxL hx3 in
theorem exists_comm_eq_of_mem_V
    (hΓ : Subgroup.centralizer (A : Set G) = A) {v : G} (hv : v ∈ VZ T M) :
    ∃ e ∈ A, wOfX d x * e * (wOfX d x)⁻¹ * e⁻¹ = v := by
  obtain ⟨a, ha, haV, haZ, hza, haa, hxa, hall⟩ := three_cycle_x c hD hd4 hxL hx3
  have hxw := x_comm_wOfX c hD hd4 hxL hx3
  have hzz : (d * d) * (d * d) = 1 := (dd_facts hd4).1
  have hVA := VZ_le_A c18
  have hAc : ∀ u ∈ A, ∀ u' ∈ A, u * u' = u' * u := by
    intro u hu u' hu'
    exact congrArg Subtype.val (c18.b.A_elem.1.is_comm.comm ⟨u, hu⟩ ⟨u', hu'⟩)
  have hcw := comm_w_mem_V c c18 hD hd4 hxL
  have hwA : ∀ e ∈ A, wOfX d x * e * (wOfX d x)⁻¹ ∈ A := by
    intro e he
    have := A.mul_mem (hVA (hcw e he)) he
    simpa [mul_assoc] using this
  have hxA := x_normalizes_A c c18 hxL
  let Wc := commSubgroup A (wOfX d x) hAc hwA
  have hW : ∀ u, u ∈ Wc ↔ ∃ e ∈ A, u = wOfX d x * e * (wOfX d x)⁻¹ * e⁻¹ := fun u => Iff.rfl
  have hxW : ∀ u ∈ Wc, x * u * x⁻¹ ∈ Wc := by
    intro u hu
    obtain ⟨e, he, rfl⟩ := (hW u).mp hu
    refine (hW _).mpr ⟨x * e * x⁻¹, hxA e he, ?_⟩
    calc x * (wOfX d x * e * (wOfX d x)⁻¹ * e⁻¹) * x⁻¹
        = (x * wOfX d x * x⁻¹) * (x * e * x⁻¹) * (x * wOfX d x * x⁻¹)⁻¹ * (x * e * x⁻¹)⁻¹ := by group
      _ = wOfX d x * (x * e * x⁻¹) * (wOfX d x)⁻¹ * (x * e * x⁻¹)⁻¹ := by rw [hxw]
  have hwnA : wOfX d x ∉ A := fun h =>
    wOfX_not_mem_RU c c18 hΓ hD hd4 hxL (Subgroup.mem_sup_left (c18.b.A_le h))
  have hne : ∃ e0 ∈ A, wOfX d x * e0 * (wOfX d x)⁻¹ * e0⁻¹ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hwnA
    rw [← hΓ]
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have h1 := hcon h hh
    have h2 : wOfX d x * h * (wOfX d x)⁻¹ = h := mul_inv_eq_one.mp h1
    calc h * wOfX d x = (wOfX d x * h * (wOfX d x)⁻¹) * wOfX d x := by rw [h2]
      _ = wOfX d x * h := by group
  obtain ⟨e0, he0, hne0⟩ := hne
  have hu0W : wOfX d x * e0 * (wOfX d x)⁻¹ * e0⁻¹ ∈ Wc := (hW _).mpr ⟨e0, he0, rfl⟩
  have hu0V := hcw e0 he0
  have hallW : d * d ∈ Wc ∧ a ∈ Wc ∧ (d * d) * a ∈ Wc := by
    rcases hall _ hu0V with h | h | h | h
    · exact absurd h hne0
    · have h1 : d * d ∈ Wc := h ▸ hu0W
      have h2 : a ∈ Wc := by rw [ha]; exact hxW _ h1
      exact ⟨h1, h2, Wc.mul_mem h1 h2⟩
    · have h2 : a ∈ Wc := h ▸ hu0W
      have h3 : (d * d) * a ∈ Wc := by rw [← hxa]; exact hxW _ h2
      have h1 : d * d ∈ Wc := by
        have : d * d = ((d * d) * a) * a := by rw [mul_assoc, haa, mul_one]
        rw [this]; exact Wc.mul_mem h3 h2
      exact ⟨h1, h2, h3⟩
    · have h3 : (d * d) * a ∈ Wc := h ▸ hu0W
      have h1 : d * d ∈ Wc := by
        have h4 := hxW _ h3
        have e : x * ((d * d) * a) * x⁻¹ = d * d := by
          calc x * ((d * d) * a) * x⁻¹ = (x * (d * d) * x⁻¹) * (x * a * x⁻¹) := by group
            _ = a * ((d * d) * a) := by rw [← ha, hxa]
            _ = ((d * d) * a) * a := by rw [← mul_assoc, ← hza]
            _ = d * d := by rw [mul_assoc, haa, mul_one]
        rwa [e] at h4
      have h2 : a ∈ Wc := by
        have : a = (d * d) * ((d * d) * a) := by rw [← mul_assoc, hzz, one_mul]
        rw [this]; exact Wc.mul_mem h1 h3
      exact ⟨h1, h2, h3⟩
  have hvW : v ∈ Wc := by
    rcases hall v hv with h | h | h | h
    · rw [h]; exact Wc.one_mem
    · rw [h]; exact hallW.1
    · rw [h]; exact hallW.2.1
    · rw [h]; exact hallW.2.2
  obtain ⟨e, he, hev⟩ := (hW v).mp hvW
  exact ⟨e, he, hev.symm⟩

include c c18 hD hd4 hxL hx3 in
theorem exists_conj_wOfX_eq_mul_sq
    (hΓ : Subgroup.centralizer (A : Set G) = A) :
    ∃ s : G, s * wOfX d x * s⁻¹ = wOfX d x * (d * d) := by
  have hzZ := sq_mem_omegaOneCenter c hD hd4
  have hzV : d * d ∈ VZ T M := Hyp1281Two.omegaOneCenter_le_VZ T M hzZ
  obtain ⟨e, he, hwe⟩ := exists_comm_eq_of_mem_V c c18 hD hd4 hxL hx3 hΓ hzV
  have hzA : d * d ∈ A := VZ_le_A c18 hzV
  have hzw : (d * d) * wOfX d x = wOfX d x * (d * d) := by
    have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
    have hzX : d * d ∈ Xgen T M := (Xgen T M).mul_mem (le_Wgen (dOf_mem_delta c) hd)
      (le_Wgen (dOf_mem_delta c) hd)
    exact Xgen_comm c hD hd4 _ hzX _ (wOfX_mem_Xgen c hD hxL)
  have hez : e⁻¹ * (d * d) * e = d * d := by
    have h1 : (d * d) * e = e * (d * d) := by
      exact congrArg Subtype.val (c18.b.A_elem.1.is_comm.comm ⟨d * d, hzA⟩ ⟨e, he⟩)
    calc e⁻¹ * (d * d) * e = e⁻¹ * (e * (d * d)) := by rw [mul_assoc, ← h1]
      _ = d * d := by group
  have h1 : wOfX d x * e = (d * d) * e * wOfX d x := by
    calc wOfX d x * e = (wOfX d x * e * (wOfX d x)⁻¹ * e⁻¹) * e * wOfX d x := by group
      _ = (d * d) * e * wOfX d x := by rw [hwe]
  refine ⟨e⁻¹, ?_⟩
  calc e⁻¹ * wOfX d x * e⁻¹⁻¹ = e⁻¹ * (wOfX d x * e) := by group
    _ = e⁻¹ * ((d * d) * e * wOfX d x) := by rw [h1]
    _ = (e⁻¹ * (d * d) * e) * wOfX d x := by group
    _ = (d * d) * wOfX d x := by rw [hez]
    _ = wOfX d x * (d * d) := hzw

end CommA

section N1

theorem sq_eq_of_isQ8Sq {P : Type*} [Group P] [Finite P] (h : IsQ8Sq P) (u v : P) (hu : u * u ≠ 1)
    (hv : v * v ≠ 1) : u * u = v * v := by
  have hc := centerOrderTwo_of_isQ8Sq h
  obtain ⟨w₀, hw1, hwc, hunique⟩ := hc
  obtain ⟨hcard, A, B, ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩ := h
  have hBA : B ≤ Subgroup.centralizer (A : Set P) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hAB ha) y hy).symm
  have hgen' : B ⊔ A = ⊤ := by rw [sup_comm]; exact hgen
  have hsq : ∀ y : P, ∀ g : P, (y * y) * g = g * (y * y) := by
    intro y g
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hAB (hgen ▸ Subgroup.mem_top y)
    have hba : b * a = a * b := Subgroup.mem_centralizer_iff.mp (hAB ha) b hb
    have e : (a * b) * (a * b) = (a * a) * (b * b) := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hba]
        _ = (a * a) * (b * b) := by group
    rw [e]
    have h1 := sq_central_of_q8 hAB hgen eA ⟨a, ha⟩
    have h2 := sq_central_of_q8 hBA hgen' eB ⟨b, hb⟩
    rw [Subgroup.mem_center_iff] at h1 h2
    simp only [pow_two] at h1 h2
    calc (a * a) * (b * b) * g = (a * a) * ((b * b) * g) := by group
      _ = (a * a) * (g * (b * b)) := by rw [h2 g]
      _ = ((a * a) * g) * (b * b) := by group
      _ = (g * (a * a)) * (b * b) := by rw [h1 g]
      _ = g * ((a * a) * (b * b)) := by group
  have hu' := hunique (u * u) (fun y => hsq u y)
  have hv' := hunique (v * v) (fun y => hsq v y)
  rcases hu' with h | h
  · exact absurd h hu
  rcases hv' with h' | h'
  · exact absurd h' hv
  rw [h, h']

end N1

section N1b

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t : G}
  (c : Counter T M g) (c18 : Concl14318 T M g A t)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
  {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3)

include c in
theorem mem_U_of_two_power {h : G} (ho : h ∈ oTwoUpper (mcOf T)) {k : ℕ} (hk : h ^ 2 ^ k = 1) :
    h ∈ uOfL22 T M := by
  have hH : h ∈ mcOf T := oTwoUpper_le _ ho
  have hk' : (⟨h, hH⟩ : ↥(mcOf T)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  have h3 := c.actK_cube_of_mem_oTwoUpper (x := ⟨h, hH⟩) ho
  have h2k : c.actK ⟨h, hH⟩ ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
  have hone : c.actK ⟨h, hH⟩ = 1 := by
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have hd1 : orderOf (c.actK ⟨h, hH⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2k
    have hd2 : orderOf (c.actK ⟨h, hH⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hg : orderOf (c.actK ⟨h, hH⟩) ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd hd1 hd2
    rw [hcop] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  exact inf_qOf_le_uOfL22 c ⟨ho, c.mem_qOf_of_actK_eq_one hone⟩

include c hD hd4 hxL hx3 in
theorem wOfX_not_conj_sq (y : G) : y * (d * d) * y⁻¹ ≠ wOfX d x := by
  intro hy
  obtain ⟨a, ha, haV, haZ, hza, haa, hxa, hall⟩ := three_cycle_x c hD hd4 hxL hx3
  have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have hc := Xgen_comm c hD hd4
  have h0 : d ∈ Xgen T M := le_Wgen (dOf_mem_delta c) hd
  have h1 := d1_mem_Xgen c hxL hd
  have h2 := d2_mem_Xgen c hxL hd
  have hxw := x_comm_wOfX c hD hd4 hxL hx3
  have hwX := wOfX_mem_Xgen c hD hxL
  have hzZ := sq_mem_omegaOneCenter c hD hd4
  have hz1 := (dd_facts hd4).2
  have hzz : (d * d) * (d * d) = 1 := (dd_facts hd4).1
  have hx3' : x * x * x = 1 := by rw [← pow_three', ← hx3]; exact pow_orderOf_eq_one x
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ (quasithinOmegaOneCenter T).one_mem)
  have haz : (d * d) ≠ a := fun h => haZ (h ▸ hzZ)
  have hd₂x : x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹ = d := by
    have : x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * d * (x * x * x)⁻¹ := by group
    rw [this, hx3']; group
  have e1sq : (d * (x * d * x⁻¹)) * (d * (x * d * x⁻¹)) = (d * d) * a := by
    have hcm : Commute (x * d * x⁻¹) d := (hc _ h1 _ h0)
    calc (d * (x * d * x⁻¹)) * (d * (x * d * x⁻¹))
        = d * ((x * d * x⁻¹) * d) * (x * d * x⁻¹) := by group
      _ = d * (d * (x * d * x⁻¹)) * (x * d * x⁻¹) := by rw [hcm.eq]
      _ = (d * d) * ((x * d * x⁻¹) * (x * d * x⁻¹)) := by group
      _ = (d * d) * a := by rw [ha]; group
  have e2sq : ((x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)) * ((x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)) =
      d * d := by
    have hcm : Commute (x * (x * d * x⁻¹) * x⁻¹) (x * d * x⁻¹) := hc _ h2 _ h1
    have hs1 : (x * d * x⁻¹) * (x * d * x⁻¹) = a := by rw [ha]; group
    have hs2 : (x * (x * d * x⁻¹) * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) = (d * d) * a := by
      rw [← hxa, ← hs1]; group
    calc ((x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)) * ((x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹))
        = (x * d * x⁻¹) * ((x * (x * d * x⁻¹) * x⁻¹) * (x * d * x⁻¹)) * (x * (x * d * x⁻¹) * x⁻¹) := by
          group
      _ = (x * d * x⁻¹) * ((x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)) * (x * (x * d * x⁻¹) * x⁻¹) := by
          rw [hcm.eq]
      _ = ((x * d * x⁻¹) * (x * d * x⁻¹)) * ((x * (x * d * x⁻¹) * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)) := by
          group
      _ = a * ((d * d) * a) := by rw [hs1, hs2]
      _ = d * d := by
          calc a * ((d * d) * a) = (a * (d * d)) * a := by group
            _ = ((d * d) * a) * a := by rw [← hza]
            _ = d * d := by rw [mul_assoc, haa, mul_one]
  have hzX : d * d ∈ Xgen T M := (Xgen T M).mul_mem h0 h0
  have haX : a ∈ Xgen T M := VZ_le_Xgen c haV
  have key : d * (x * d * x⁻¹) =
      (((x * (x * d * x⁻¹) * x⁻¹) * d) * (d * (x * d * x⁻¹))⁻¹) *
        (((x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)) * (d * (x * d * x⁻¹))⁻¹) := by
    let _ : CommGroup ↥(Xgen T M) :=
      { (inferInstance : Group ↥(Xgen T M)) with
        mul_comm := fun u v => Subtype.ext (Xgen_comm c hD hd4 u u.2 v v.2) }
    let D0 : ↥(Xgen T M) := ⟨d, h0⟩
    let D1 : ↥(Xgen T M) := ⟨x * d * x⁻¹, h1⟩
    let D2 : ↥(Xgen T M) := ⟨x * (x * d * x⁻¹) * x⁻¹, h2⟩
    let ZZ : ↥(Xgen T M) := ⟨d * d, hzX⟩
    let AA : ↥(Xgen T M) := ⟨a, haX⟩
    have hD0 : D0 * D0 = ZZ := Subtype.ext rfl
    have hD1 : D1 * D1 = AA := Subtype.ext (by
      show (x * d * x⁻¹) * (x * d * x⁻¹) = a
      rw [ha]; group)
    have hD2 : D2 * D2 = ZZ * AA := Subtype.ext (by
      show (x * (x * d * x⁻¹) * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) = (d * d) * a
      rw [← hxa]
      have hs1 : (x * d * x⁻¹) * (x * d * x⁻¹) = a := by rw [ha]; group
      rw [← hs1]; group)
    have hZZ : ZZ * ZZ = 1 := Subtype.ext hzz
    have hAA : AA * AA = 1 := Subtype.ext haa
    have F3 : (D0 * D1) * (D1 * D2) * (D2 * D0) = 1 := by
      calc (D0 * D1) * (D1 * D2) * (D2 * D0) = (D0 * D0) * (D1 * D1) * (D2 * D2) := by
            simp only [mul_comm, mul_left_comm, mul_assoc]
        _ = (ZZ * ZZ) * (AA * AA) := by
            rw [hD0, hD1, hD2]; simp only [mul_comm, mul_left_comm, mul_assoc]
        _ = 1 := by rw [hZZ, hAA, one_mul]
    have F4 : (D0 * D1) * (D0 * D1) * ((D0 * D1) * (D0 * D1)) = 1 := by
      have h5 : (D0 * D1) * (D0 * D1) = ZZ * AA := by
        calc (D0 * D1) * (D0 * D1) = (D0 * D0) * (D1 * D1) := by
              simp only [mul_comm, mul_left_comm, mul_assoc]
          _ = ZZ * AA := by rw [hD0, hD1]
      rw [h5]
      calc ZZ * AA * (ZZ * AA) = (ZZ * ZZ) * (AA * AA) := by
            simp only [mul_comm, mul_left_comm, mul_assoc]
        _ = 1 := by rw [hZZ, hAA, one_mul]
    have h23 : (D1 * D2) * (D2 * D0) = (D0 * D1)⁻¹ := by
      have := F3
      rw [mul_assoc] at this
      exact eq_inv_of_mul_eq_one_right this
    have hE : D0 * D1 = (((D2 * D0) * (D0 * D1)⁻¹) * ((D1 * D2) * (D0 * D1)⁻¹)) := by
      set E1 := D0 * D1 with hE1
      set E2 := D1 * D2 with hE2
      set E3 := D2 * D0 with hE3
      have h4 : E1 * (E1 * E1 * E1) = 1 := by
        rw [← F4]; simp only [mul_assoc]
      have h4' : E1 * E1 * E1 = E1⁻¹ := eq_inv_of_mul_eq_one_right h4
      calc E1 = (E1⁻¹)⁻¹ := (inv_inv E1).symm
        _ = (E1 * E1 * E1)⁻¹ := by rw [h4']
        _ = (E2 * E3) * (E1⁻¹ * E1⁻¹) := by
            rw [h23]; simp only [mul_inv_rev, mul_assoc]
        _ = (E3 * E1⁻¹) * (E2 * E1⁻¹) := by simp only [mul_comm, mul_left_comm, mul_assoc]
    have := congrArg Subtype.val hE
    simpa [D0, D1, D2] using this
  set e₁ : G := d * (x * d * x⁻¹) with he₁
  set e₂ : G := (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) with he₂
  set e₃ : G := (x * (x * d * x⁻¹) * x⁻¹) * d with he₃
  have he₁X : e₁ ∈ Xgen T M := (Xgen T M).mul_mem h0 h1
  have he₂X : e₂ ∈ Xgen T M := (Xgen T M).mul_mem h1 h2
  have F1 : x * e₁ * x⁻¹ = e₂ := by
    calc x * e₁ * x⁻¹ = (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) := by rw [he₁]; group
      _ = e₂ := rfl
  have F2 : x * e₂ * x⁻¹ = e₃ := by
    calc x * e₂ * x⁻¹ = (x * (x * d * x⁻¹) * x⁻¹) * (x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹) := by
          rw [he₂]; group
      _ = e₃ := by rw [hd₂x]
  have he₁sq : e₁ * e₁ = (d * d) * a := e1sq
  have he₂sq : e₂ * e₂ = d * d := e2sq
  have he₁4 : e₁ * e₁ * e₁ * e₁ = 1 := by
    calc e₁ * e₁ * e₁ * e₁ = (e₁ * e₁) * (e₁ * e₁) := by group
      _ = 1 := by
        rw [he₁sq]
        calc (d * d) * a * ((d * d) * a) = (d * d) * (a * (d * d)) * a := by group
          _ = (d * d) * ((d * d) * a) * a := by rw [← hza]
          _ = ((d * d) * (d * d)) * (a * a) := by group
          _ = 1 := by rw [hzz, haa, one_mul]
  set N := oTwoUpper (mcOf T) with hN
  have hNn : mcOf T ≤ Subgroup.normalizer (N : Set G) := le_normalizer_oTwoUpper (mcOf T)
  have hzy : d * d = y⁻¹ * wOfX d x * y := by rw [← hy]; group
  have hH : ∀ u ∈ Xgen T M, y⁻¹ * u * y ∈ mcOf T := by
    intro u hu
    refine c.mem_mcOf_of_comm hzZ hz1 ?_
    have hcu := hc u hu _ hwX
    calc (y⁻¹ * u * y) * (d * d) = y⁻¹ * (u * wOfX d x) * y := by rw [hzy]; group
      _ = y⁻¹ * (wOfX d x * u) * y := by rw [hcu]
      _ = (d * d) * (y⁻¹ * u * y) := by rw [hzy]; group
  have hxH : y⁻¹ * x * y ∈ mcOf T := by
    refine c.mem_mcOf_of_comm hzZ hz1 ?_
    have hxw' : x * wOfX d x = wOfX d x * x := by
      calc x * wOfX d x = (x * wOfX d x * x⁻¹) * x := by group
        _ = wOfX d x * x := by rw [hxw]
    calc (y⁻¹ * x * y) * (d * d) = y⁻¹ * (x * wOfX d x) * y := by rw [hzy]; group
      _ = y⁻¹ * (wOfX d x * x) * y := by rw [hxw']
      _ = (d * d) * (y⁻¹ * x * y) := by rw [hzy]; group
  have hx'ord : orderOf (y⁻¹ * x * y) = 3 := by
    have e : y⁻¹ * x * y = (MulAut.conj y⁻¹ : MulAut G) x := by simp
    rw [e, MulEquiv.orderOf_eq]; exact hx3
  have hx'N : y⁻¹ * x * y ∈ N :=
    mem_oTwoUpper_of_odd hxH (by rw [hx'ord]; decide)
  have hcomm : ∀ u : G, y⁻¹ * u * y ∈ mcOf T → y⁻¹ * (x * u * x⁻¹ * u⁻¹) * y ∈ N := by
    intro u hu
    have e : y⁻¹ * (x * u * x⁻¹ * u⁻¹) * y =
        (y⁻¹ * x * y) * ((y⁻¹ * u * y) * (y⁻¹ * x * y)⁻¹ * (y⁻¹ * u * y)⁻¹) := by group
    rw [e]
    refine N.mul_mem hx'N ?_
    exact (Subgroup.mem_normalizer_iff.mp (hNn hu) _).mp (N.inv_mem hx'N)
  have hP1 : y⁻¹ * (e₂ * e₁⁻¹) * y ∈ N := by
    have := hcomm e₁ (hH e₁ he₁X)
    rw [F1] at this; exact this
  have hP2 : y⁻¹ * (e₃ * e₂⁻¹) * y ∈ N := by
    have := hcomm e₂ (hH e₂ he₂X)
    rw [F2] at this; exact this
  have hP3 : y⁻¹ * (e₃ * e₁⁻¹) * y ∈ N := by
    have e : y⁻¹ * (e₃ * e₁⁻¹) * y = (y⁻¹ * (e₃ * e₂⁻¹) * y) * (y⁻¹ * (e₂ * e₁⁻¹) * y) := by group
    rw [e]; exact N.mul_mem hP2 hP1
  have hE1N : y⁻¹ * e₁ * y ∈ N := by
    have e : y⁻¹ * e₁ * y = (y⁻¹ * (e₃ * e₁⁻¹) * y) * (y⁻¹ * (e₂ * e₁⁻¹) * y) := by
      calc y⁻¹ * e₁ * y = y⁻¹ * ((e₃ * e₁⁻¹) * (e₂ * e₁⁻¹)) * y := by rw [← key]
        _ = (y⁻¹ * (e₃ * e₁⁻¹) * y) * (y⁻¹ * (e₂ * e₁⁻¹) * y) := by group
    rw [e]; exact N.mul_mem hP3 hP1
  have hE2N : y⁻¹ * e₂ * y ∈ N := by
    have e : y⁻¹ * e₂ * y = (y⁻¹ * (e₂ * e₁⁻¹) * y) * (y⁻¹ * e₁ * y) := by group
    rw [e]; exact N.mul_mem hP1 hE1N
  have hU1 : y⁻¹ * e₁ * y ∈ uOfL22 T M := by
    refine mem_U_of_two_power c hE1N (k := 2) ?_
    calc (y⁻¹ * e₁ * y) ^ 2 ^ 2 = y⁻¹ * (e₁ * e₁ * e₁ * e₁) * y := by
          rw [show (2 : ℕ) ^ 2 = 4 from rfl]; simp only [pow_succ, pow_zero, one_mul]; group
      _ = 1 := by rw [he₁4]; group
  have hU2 : y⁻¹ * e₂ * y ∈ uOfL22 T M := by
    refine mem_U_of_two_power c hE2N (k := 2) ?_
    have he₂4 : e₂ * e₂ * e₂ * e₂ = 1 := by
      calc e₂ * e₂ * e₂ * e₂ = (e₂ * e₂) * (e₂ * e₂) := by group
        _ = 1 := by rw [he₂sq, hzz]
    calc (y⁻¹ * e₂ * y) ^ 2 ^ 2 = y⁻¹ * (e₂ * e₂ * e₂ * e₂) * y := by
          rw [show (2 : ℕ) ^ 2 = 4 from rfl]; simp only [pow_succ, pow_zero, one_mul]; group
      _ = 1 := by rw [he₂4]; group
  have hza1 : (d * d) * a ≠ 1 := by
    intro h
    apply haz
    have : (d * d) = a⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]; exact inv_eq_of_mul_eq_one_right haa
  have hconj1 : ∀ u : G, y⁻¹ * u * y = 1 → u = 1 := by
    intro u h
    calc u = y * (y⁻¹ * u * y) * y⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hsq := sq_eq_of_isQ8Sq c.c15.q8sq (⟨y⁻¹ * e₁ * y, hU1⟩ : ↥(uOfL22 T M)) ⟨y⁻¹ * e₂ * y, hU2⟩
    (fun h => hza1 (by
      have h' := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, OneMemClass.coe_one] at h'
      have h7 : y⁻¹ * (e₁ * e₁) * y = 1 := by rw [← h']; group
      rw [he₁sq] at h7
      exact hconj1 _ h7))
    (fun h => hz1 (by
      have h' := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, OneMemClass.coe_one] at h'
      have h7 : y⁻¹ * (e₂ * e₂) * y = 1 := by rw [← h']; group
      rw [he₂sq] at h7
      exact hconj1 _ h7))
  have hsq' := congrArg Subtype.val hsq
  simp only [Subgroup.coe_mul] at hsq'
  have h5 : y⁻¹ * (e₁ * e₁) * y = y⁻¹ * (e₂ * e₂) * y := by
    calc y⁻¹ * (e₁ * e₁) * y = (y⁻¹ * e₁ * y) * (y⁻¹ * e₁ * y) := by group
      _ = (y⁻¹ * e₂ * y) * (y⁻¹ * e₂ * y) := hsq'
      _ = y⁻¹ * (e₂ * e₂) * y := by group
  rw [he₁sq, he₂sq] at h5
  have h6 : (d * d) * a = d * d := by
    have := congrArg (fun u => y * u * y⁻¹) h5
    simpa using this
  apply ha1
  have : (d * d) * a = (d * d) * 1 := by rw [h6, mul_one]
  exact mul_left_cancel this

end N1b

end S143

end CFSG.Quasithin
