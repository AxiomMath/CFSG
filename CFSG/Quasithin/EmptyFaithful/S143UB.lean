module

public import CFSG.Quasithin.EmptyFaithful.S143RB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

open A6Model

section SetupX

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2 in
theorem Counter.exists_setup_of_x (c18a : Concl18a T M g) {x z : G} (hxL : x ∈ yOfL22 T M)
    (hx3 : orderOf x = 3) (hzZ : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (hV4 : ∀ w ∈ VZ T M, w = 1 ∨ w = z ∨ w = x * z * x⁻¹ ∨ w = z * (x * z * x⁻¹)) :
    Setup c hrW hrV hr2 x z (x * z * x⁻¹) (x * r * x⁻¹) := by
  have hxI : x ∈ iTwo T M := by
    rw [iTwo_eq c.h1281 c.nonab]; exact Subgroup.mem_sup_left hxL
  have hfpf := c18a.r_fpf x hxI hx3
  have hx3' : x * x * x = 1 := by
    rw [← pow_three', ← hx3]; exact pow_orderOf_eq_one x
  have hzV : z ∈ VZ T M := Hyp1281Two.omegaOneCenter_le_VZ T M hzZ
  have hzA : z ∈ c.Ac hrW hrV hr2 := c.VZ_le_Ac hrW hrV hr2 hzV
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := c.iTwo_le_normalizer_VZ hxI
  have haV : x * z * x⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hxN z).mp hzV
  have haA : x * z * x⁻¹ ∈ c.Ac hrW hrV hr2 := c.VZ_le_Ac hrW hrV hr2 haV
  have hzR : z ∈ rOf T M := c.Ac_le_rOf hrW hrV hr2 hzA
  have ha1 : x * z * x⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this, h]; group
  have haz : x * z * x⁻¹ ≠ z := fun h => hz1 (hfpf z hzR h)
  have hmemV : ∀ b0 b1 : Bool, (if b0 = true then z else 1) * (if b1 = true then x * z * x⁻¹ else 1)
      ∈ VZ T M := by
    intro b0 b1
    refine (VZ T M).mul_mem ?_ ?_
    · cases b0 <;> simp [hzV]
    · cases b1 <;> simp [haV]
  have hrA : r ∈ c.Ac hrW hrV hr2 := c.r_mem_Ac hrW hrV hr2
  have hr1A : x * r * x⁻¹ ∈ c.Ac hrW hrV hr2 := c.Ac_conj_mem hrW hrV hr2 hxI hrA
  have hxinvN : x⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) := (Subgroup.normalizer _).inv_mem hxN
  refine ⟨hxL, hx3, hfpf, hzZ, hz1, rfl, rfl, ?_, hV4⟩
  refine isBasis_of_conditions hzA haA hrA hr1A
    (fun a ha b hb => mul_comm_of_sq_eq_one (fun y hy => c.sq_Ac hrW hrV hr2 hy) ha hb)
    (fun y hy => c.sq_Ac hrW hrV hr2 hy) (c.card_Ac hrW hrV hr2) hz1 ?_ ?_ ?_
  · intro b0
    cases b0
    · simpa using ha1
    · simpa using haz
  · intro b0 b1 h
    apply hrV
    rw [h]
    exact hmemV b0 b1
  · intro b0 b1 b2 h
    cases b2
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at h
      apply hrV
      have hr : r = x⁻¹ * (x * r * x⁻¹) * x := by group
      have hmem : x⁻¹ * (x * r * x⁻¹) * x⁻¹⁻¹ ∈ VZ T M := by
        refine (Subgroup.mem_normalizer_iff.mp hxinvN _).mp ?_
        rw [h]; exact hmemV b0 b1
      rw [hr]
      simpa using hmem
    · simp only [↓reduceIte] at h
      exact c.not_conj_eq hrW hrV hr2 hxI hx3' hfpf (hmemV b0 b1) h

end SetupX

section RStd

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T)

include hS htT htRQ in
theorem Setup.cmat_mem_Rstd4 {ρ : G} (hρ : ρ ∈ rOf T M) : cmat z a r r1 ρ ∈ Rstd4 := by
  obtain ⟨R1, R2, hR1, hR2, hRH, hR⟩ := hS.exists_RHyp htT htRQ
  obtain ⟨a0, a1, a2, a3, rfl⟩ := hR1.exists_Rpar
  obtain ⟨b0, b1, b2, b3, rfl⟩ := hR2.exists_Rpar
  have hRc := stageR a0 a1 a2 a3 b0 b1 b2 b3 hRH
  have hmem := (hR (cmat z a r r1 ρ)).mpr ⟨ρ, hρ, rfl⟩
  have h1 := hRc.1
  simp only [Rstd4, List.mem_cons, List.not_mem_nil, or_false] at h1 hmem ⊢
  rcases hmem with h | h | h | h
  · exact Or.inl h
  · rcases h1.1 with h' | h' | h' <;> simp [h, h']
  · rcases h1.2.1 with h' | h' | h' <;> simp [h, h']
  · rcases h1.2.2 with h' | h' | h' <;> simp [h, h']

end RStd

section U0

@[expose] def u0Of {G : Type*} [Group G] (d x : G) : G :=
  (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)

theorem wOfX_eq_mul_u0Of {G : Type*} [Group G] (d x : G) : wOfX d x = d * u0Of d x := by
  unfold wOfX u0Of
  rw [mul_assoc]

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
  {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3)

include c hD hd4 hxL hx3 in
theorem u0Of_sq : u0Of d x * u0Of d x = d * d := by
  obtain ⟨a, ha, haV, haZ, hza, haa, hxa, hall⟩ := three_cycle_x c hD hd4 hxL hx3
  have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have hc := Xgen_comm c hD hd4
  have h1 := d1_mem_Xgen c hxL hd
  have h2 := d2_mem_Xgen c hxL hd
  have hs1 : (x * d * x⁻¹) * (x * d * x⁻¹) = a := by rw [ha]; group
  have hs2 : (x * (x * d * x⁻¹) * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) = (d * d) * a := by
    rw [← hxa, ← hs1]; group
  have hcm : Commute (x * (x * d * x⁻¹) * x⁻¹) (x * d * x⁻¹) := hc _ h2 _ h1
  unfold u0Of
  calc (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) * ((x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹))
      = (x * d * x⁻¹) * ((x * (x * d * x⁻¹) * x⁻¹) * (x * d * x⁻¹)) *
          (x * (x * d * x⁻¹) * x⁻¹) := by group
    _ = (x * d * x⁻¹) * ((x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)) * (x * (x * d * x⁻¹) * x⁻¹) := by
        rw [hcm.eq]
    _ = ((x * d * x⁻¹) * (x * d * x⁻¹)) * ((x * (x * d * x⁻¹) * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)) := by
        group
    _ = a * ((d * d) * a) := by rw [hs1, hs2]
    _ = d * d := by
        calc a * ((d * d) * a) = (a * (d * d)) * a := by group
          _ = ((d * d) * a) * a := by rw [← hza]
          _ = d * d := by rw [mul_assoc, haa, mul_one]

end U0

section CmatU0

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1)

include hS in
theorem Setup.cmat_u0Of {d : G} (hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))
    (hdT : cmat z a r r1 d = Tz) : cmat z a r r1 (u0Of d x) = Rs2 := by
  have hB := hS.basis
  have hxN : x ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    c.iTwo_le_normalizer_Ac hrW hrV hr2 hS.x_iTwo
  have hxinv : x⁻¹ = x * x := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hS.x_cube)
  have hxiN : x⁻¹ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := Subgroup.inv_mem _ hxN
  have hMi : cmat z a r r1 x⁻¹ = mm Mx Mx := by rw [hxinv, hB.cmat_mul hxN hxN, hS.cmat_x]
  have hd1N : x * d * x⁻¹ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hdN) hxiN
  have hd2N : x * (x * d * x⁻¹) * x⁻¹ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hd1N) hxiN
  have hc1 : cmat z a r r1 (x * d * x⁻¹) = mm (mm Mx Mx) (mm Tz Mx) := by
    rw [hB.cmat_mul (Subgroup.mul_mem _ hxN hdN) hxiN, hB.cmat_mul hxN hdN, hMi, hdT, hS.cmat_x]
  have hc2 : cmat z a r r1 (x * (x * d * x⁻¹) * x⁻¹) =
      mm (mm Mx Mx) (mm (mm (mm Mx Mx) (mm Tz Mx)) Mx) := by
    rw [hB.cmat_mul (Subgroup.mul_mem _ hxN hd1N) hxiN, hB.cmat_mul hxN hd1N, hMi, hc1,
      hS.cmat_x]
  unfold u0Of
  rw [hB.cmat_mul hd1N hd2N, hc1, hc2]
  exact mat4Eq_iff.mp (by decide +kernel)

end CmatU0

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t : G}
  (c : Counter T M g) (c18 : Concl14318 T M g A t)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
  {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3)

include c c18 hD hd4 hxL hx3 in
theorem u0Of_mem_U (hΓ : Subgroup.centralizer (A : Set G) = A) : u0Of d x ∈ uOfL22 T M := by
  classical
  have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have hzZ := sq_mem_omegaOneCenter c hD hd4
  have hz1 : d * d ≠ 1 := (dd_facts hd4).2
  have hdZ : d ∉ quasithinOmegaOneCenter T := by
    intro h
    have h2 := sq_eq_one_of_mem_omegaOneCenter T h
    rw [pow_two] at h2
    exact hz1 h2
  have hsq := u0Of_sq c hD hd4 hxL hx3
  obtain ⟨a₀, ha₀, haV, haZ, hza, haa, hxa, hall⟩ := three_cycle_x c hD hd4 hxL hx3
  have htT := c18.b.t_mem
  have htRQ := c18.b.t_nmem
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq c18.b
  have hS := c.exists_setup_of_x hrW hrV hr2 c18.a hxL hx3 hzZ hz1 (by rw [← ha₀]; exact hall)
  have hB := hS.basis
  have hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2) hd
  have hdT : cmat (d * d) (x * (d * d) * x⁻¹) r (x * r * x⁻¹) d = Tz := by
    rcases D_cmat hS hd with h | h
    · exfalso
      have h1 : d ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
        (hB.cmat_eq_one_iff_mem_centralizer hdN).mp h
      rw [hΓ] at h1
      exact hdZ (D_inf_Ac_le_Z hd h1)
    · exact h
  have hcu := hS.cmat_u0Of hdN hdT
  have hxN : x ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    c.iTwo_le_normalizer_Ac hrW hrV hr2 hS.x_iTwo
  have hxiN : x⁻¹ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := Subgroup.inv_mem _ hxN
  have hd1N : x * d * x⁻¹ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hdN) hxiN
  have hd2N : x * (x * d * x⁻¹) * x⁻¹ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hd1N) hxiN
  have hu₀N : u0Of d x ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    Subgroup.mul_mem _ hd1N hd2N
  obtain ⟨w₀, hw₀W, hw₀A⟩ : ∃ w₀ ∈ Hyp1281Two.wOfU T M, w₀ ∉ c.Ac hrW hrV hr2 := by
    by_contra hcon
    push Not at hcon
    have hWle : Hyp1281Two.wOfU T M ≤ uOfL22 T M ⊓ c.Ac hrW hrV hr2 :=
      fun w hw => ⟨hw.1, hcon w hw⟩
    have h1 := Subgroup.card_le_of_le hWle
    have hW : Nat.card ↥(Hyp1281Two.wOfU T M) = 16 := card_wOf c
    rw [hW, c.card_uOfL22_inf_Ac hrW hrV hr2] at h1
    omega
  have hw₀U : w₀ ∈ uOfL22 T M := hw₀W.1
  have hw₀R : w₀ ∈ rOf T M := c.mem_rOf_of_mem_wOfU hw₀W
  have hw₀N : w₀ ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    c.rOf_le_normalizer_Ac hrW hrV hr2 hw₀R
  have hR4 := hS.cmat_mem_Rstd4 htT htRQ hw₀R
  have hU4 := hS.isUMat_cmat hw₀U
  have hnI : cmat (d * d) (x * (d * d) * x⁻¹) r (x * r * x⁻¹) w₀ ≠ I4 := by
    intro h
    apply hw₀A
    have h1 := (hB.cmat_eq_one_iff_mem_centralizer hw₀N).mp h
    rw [hΓ] at h1
    exact h1
  have hcw : cmat (d * d) (x * (d * d) * x⁻¹) r (x * r * x⁻¹) w₀ = Rs2 := by
    simp only [Rstd4, List.mem_cons, List.not_mem_nil, or_false] at hR4
    rcases hR4 with h | h | h | h
    · exact absurd h hnI
    · exfalso
      rw [h] at hU4
      exact absurd hU4.2.2.2.2.1 (by decide)
    · exact h
    · exfalso
      rw [h] at hU4
      exact absurd hU4.2.2.2.2.1 (by decide)
  have hC := (hB.cmat_eq_iff_mem_centralizer hw₀N hu₀N).mp (hcw.trans hcu.symm)
  rw [hΓ] at hC
  set e := w₀⁻¹ * u0Of d x with he
  have heA : e ∈ c.Ac hrW hrV hr2 := hC
  have hu₀eq : u0Of d x = w₀ * e := by rw [he]; group
  have hww : w₀ * w₀ ∈ quasithinOmegaOneCenter T := c.mul_self_mem_Z hw₀U
  have hwwA : w₀ * w₀ ∈ c.Ac hrW hrV hr2 :=
    c.VZ_le_Ac hrW hrV hr2 (Hyp1281Two.omegaOneCenter_le_VZ T M hww)
  have hbA : w₀ * e * w₀⁻¹ ∈ c.Ac hrW hrV hr2 := (Subgroup.mem_normalizer_iff.mp hw₀N e).mp heA
  have hsq' : (w₀ * e * w₀⁻¹) * (w₀ * w₀) * e = d * d := by
    calc (w₀ * e * w₀⁻¹) * (w₀ * w₀) * e = (w₀ * e) * (w₀ * e) := by group
      _ = u0Of d x * u0Of d x := by rw [hu₀eq]
      _ = d * d := hsq
  have hcoords := congrArg (coordsOf (d * d) (x * (d * d) * x⁻¹) r (x * r * x⁻¹)) hsq'
  rw [hB.coordsOf_mul ((c.Ac hrW hrV hr2).mul_mem hbA hwwA) heA, hB.coordsOf_mul hbA hwwA,
    hB.cmat_spec hw₀N heA, hcw, hB.coordsOf_e0] at hcoords
  obtain ⟨hz1', hz2', hz3'⟩ := hS.coords_Z hww
  have hx3e : (coordsOf (d * d) (x * (d * d) * x⁻¹) r (x * r * x⁻¹) e).x3 = false := by
    have h1 := congrArg V4.x1 hcoords
    simp only [V4.add, vm, V4.sm, Rs2, Rpar] at h1
    rw [hz1'] at h1
    generalize coordsOf (d * d) (x * (d * d) * x⁻¹) r (x * r * x⁻¹) e = v at h1 ⊢
    obtain ⟨v0, v1, v2, v3⟩ := v
    revert h1
    cases v0 <;> cases v1 <;> cases v2 <;> cases v3 <;> decide
  have hzU : d * d ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M hS.z_V
  have haU : x * (d * d) * x⁻¹ ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M hS.a_V
  have hrU : r ∈ uOfL22 T M := hrW.1
  have hite : ∀ (b : Bool) (y : G), y ∈ uOfL22 T M → (if b = true then y else 1) ∈ uOfL22 T M := by
    intro b y hy
    cases b <;> simp [hy]
  have heU : e ∈ uOfL22 T M := by
    have h := hB.embV_coordsOf heA
    rw [← h]
    unfold embV
    rw [hx3e]
    simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    exact (uOfL22 T M).mul_mem ((uOfL22 T M).mul_mem (hite _ _ hzU) (hite _ _ haU)) (hite _ _ hrU)
  rw [hu₀eq]
  exact (uOfL22 T M).mul_mem hw₀U heU

end Main

end S143

end CFSG.Quasithin
