module

public import CFSG.Quasithin.EmptyFaithful.S143SB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_isSylowTwoOf_of_le {K S P : Subgroup G} (hS : IsSylowTwoOf S K) (hSP : S ≤ P)
    (hPK : P ≤ K) (hP : IsPGroup 2 P) : P = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hidx⟩ := hS
  have h1 : S.relIndex P * P.relIndex K = S.relIndex K := Subgroup.relIndex_mul_relIndex S P K hSP hPK
  have hodd : ¬ 2 ∣ S.relIndex P := fun h => hidx (by
    have := h.mul_right (P.relIndex K)
    rw [h1] at this
    exact this)
  obtain ⟨n, hn⟩ := hP.index (S.subgroupOf P)
  have hn' : S.relIndex P = 2 ^ n := hn
  have hn0 : n = 0 := by
    by_contra hne
    exact hodd (hn' ▸ dvd_pow_self 2 hne)
  rw [hn0, pow_zero] at hn'
  exact le_antisymm ((Subgroup.relIndex_eq_one.mp hn')) hSP

theorem isZ4Sq_of_commuting_cyclic {C : Subgroup G} {a b : G} (hab : a * b = b * a)
    (ha : orderOf a = 4) (hb : orderOf b = 4) (hne : a * a ≠ b * b) (haC : a ∈ C) (hbC : b ∈ C)
    (hcard : Nat.card C ≤ 16) : IsZ4Sq ↥C := by
  have ha4 : a ^ 4 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb4 : b ^ 4 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have haa : (a * a) * (a * a) = 1 := by
    calc (a * a) * (a * a) = a ^ 4 := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := ha4
  have hbb : (b * b) * (b * b) = 1 := by
    calc (b * b) * (b * b) = b ^ 4 := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := hb4
  have ha1 : a * a ≠ 1 := by
    intro h
    have : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [ha] at this; omega
  have hb1 : b * b ≠ 1 := by
    intro h
    have : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hb] at this; omega
  have hsqa : ∀ y ∈ Subgroup.zpowers a, y * y = 1 ∨ y * y = a * a := by
    intro y hy
    rcases mem_zpowers_four (d := a) (z := a * a) rfl haa hy with h | h | h | h
    · left; rw [h]; simp
    · right; rw [h]
    · left; rw [h]; exact haa
    · right; rw [h]
      calc a * (a * a) * (a * (a * a)) = (a * a) * (a * a) * (a * a) := by group
        _ = a * a := by rw [haa, one_mul]
  have hsqb : ∀ y ∈ Subgroup.zpowers b, y * y = 1 ∨ y * y = b * b := by
    intro y hy
    rcases mem_zpowers_four (d := b) (z := b * b) rfl hbb hy with h | h | h | h
    · left; rw [h]; simp
    · right; rw [h]
    · left; rw [h]; exact hbb
    · right; rw [h]
      calc b * (b * b) * (b * (b * b)) = (b * b) * (b * b) * (b * b) := by group
        _ = b * b := by rw [hbb, one_mul]
  have hinter : ∀ y : G, y ∈ Subgroup.zpowers a → y ∈ Subgroup.zpowers b → y = 1 := by
    intro y hya hyb
    have hy2 : y * y = 1 := by
      rcases hsqa y hya with h | h
      · exact h
      · rcases hsqb y hyb with h' | h'
        · exact h'
        · exact absurd (h.symm.trans h') hne
    have hya' : y = 1 ∨ y = a * a := by
      rcases mem_zpowers_four (d := a) (z := a * a) rfl haa hya with h | h | h | h
      · left; exact h
      · exfalso; rw [h] at hy2; exact ha1 hy2
      · right; exact h
      · exfalso
        rw [h] at hy2
        apply ha1
        calc a * a = a * (a * a) * (a * (a * a)) := by
              calc a * a = ((a * a) * (a * a)) * (a * a) := by rw [haa, one_mul]
                _ = a * (a * a) * (a * (a * a)) := by group
          _ = 1 := hy2
    have hyb' : y = 1 ∨ y = b * b := by
      rcases mem_zpowers_four (d := b) (z := b * b) rfl hbb hyb with h | h | h | h
      · left; exact h
      · exfalso; rw [h] at hy2; exact hb1 hy2
      · right; exact h
      · exfalso
        rw [h] at hy2
        apply hb1
        calc b * b = b * (b * b) * (b * (b * b)) := by
              calc b * b = ((b * b) * (b * b)) * (b * b) := by rw [hbb, one_mul]
                _ = b * (b * b) * (b * (b * b)) := by group
          _ = 1 := hy2
    rcases hya' with h | h
    · exact h
    · rcases hyb' with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hne
  have hcomm : ∀ (u : ↥(Subgroup.zpowers a)) (v : ↥(Subgroup.zpowers b)),
      Commute ((Subgroup.zpowers a).subtype u) ((Subgroup.zpowers b).subtype v) := by
    intro u v
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp v.2
    show Commute (u : G) (v : G)
    rw [← hi, ← hj]
    exact Commute.zpow_zpow (show Commute a b from hab) i j
  let φ : ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers b) →* G :=
    MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers b).subtype hcomm
  have hφ : ∀ p, φ p = (p.1 : G) * p.2 := fun p => rfl
  have hZ1C : Subgroup.zpowers a ≤ C := Subgroup.zpowers_le.mpr haC
  have hZ2C : Subgroup.zpowers b ≤ C := Subgroup.zpowers_le.mpr hbC
  let φ' : ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers b) →* ↥C :=
    φ.codRestrict C (fun p => by rw [hφ]; exact C.mul_mem (hZ1C p.1.2) (hZ2C p.2.2))
  have hinj : Function.Injective φ' := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, v⟩ h
    have h1 : (u : G) * v = 1 := by
      have := congrArg Subtype.val h
      simpa [φ', hφ] using this
    have hu : (u : G) = (v : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hu1 : (u : G) = 1 := hinter u u.2 (by rw [hu]; exact (Subgroup.zpowers b).inv_mem v.2)
    have hv1 : (v : G) = 1 := by rw [hu1, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hu1) (Subtype.ext hv1)
  have hcZ1 : Nat.card ↥(Subgroup.zpowers a) = 4 := by rw [Nat.card_zpowers, ha]
  have hcZ2 : Nat.card ↥(Subgroup.zpowers b) = 4 := by rw [Nat.card_zpowers, hb]
  have hcprod : Nat.card (↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers b)) = 16 := by
    rw [Nat.card_prod, hcZ1, hcZ2]
  have hbij : Function.Bijective φ' := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcprod]; exact hcard
  let e : (↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers b)) ≃* ↥C := MulEquiv.ofBijective φ' hbij
  have e1 : ↥(Subgroup.zpowers a) ≃* Multiplicative (ZMod 4) := by
    have := zmodCyclicMulEquiv (inferInstance : IsCyclic ↥(Subgroup.zpowers a))
    rw [hcZ1] at this
    exact this.symm
  have e2 : ↥(Subgroup.zpowers b) ≃* Multiplicative (ZMod 4) := by
    have := zmodCyclicMulEquiv (inferInstance : IsCyclic ↥(Subgroup.zpowers b))
    rw [hcZ2] at this
    exact this.symm
  exact ⟨e.symm.trans (MulEquiv.prodCongr e1 e2)⟩

omit [Finite G] in
theorem orderOf_eq_four_of_sq {u : G} (h1 : u * u ≠ 1) (h2 : (u * u) * (u * u) = 1) : orderOf u = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : orderOf u = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · intro h
      apply h1
      simpa [pow_two] using h
    · have h4 : u ^ 2 ^ (1 + 1) = (u * u) * (u * u) := by
        rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 from rfl, pow_add, pow_two]
      rw [h4]; exact h2
  simpa using h3

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t : G}
  (c : Counter T M g) (c18 : Concl14318 T M g A t) (c19 : Concl14319 T M A)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
  {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3)

include c c19 in
theorem inf_T_kOf_eq :
    T ⊓ kOf T M A = rOf T M ⊔ uOfL22 T M := by
  have hRU_T : rOf T M ⊔ uOfL22 T M ≤ T :=
    sup_le (rOf_le_T_of_hyp c.h1281) ((uOfL22_le_qOf c).trans (qOf_le_T_of_hyp c.h1281))
  have hRU_K : rOf T M ⊔ uOfL22 T M ≤ kOf T M A := c19.b.sylow_RU.1
  exact eq_of_isSylowTwoOf_of_le c19.b.sylow_RU (le_inf hRU_T hRU_K) inf_le_right
    (c.hyp.sylow.1.to_le inf_le_left)

include c c18 hD hd4 hxL hx3 in
theorem card_centralizer_R_le
    (hΓ : Subgroup.centralizer (A : Set G) = A) :
    Nat.card ↥(rOf T M ⊓ Subgroup.centralizer ({wOfX d x} : Set G)) ≤ 16 := by
  classical
  obtain ⟨a, ha, haV, haZ, hza, haa, hxa, hall⟩ := three_cycle_x c hD hd4 hxL hx3
  have hzZ := sq_mem_omegaOneCenter c hD hd4
  have hz1 : d * d ≠ 1 := (dd_facts hd4).2
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ (quasithinOmegaOneCenter T).one_mem)
  have haz : (d * d) ≠ a := fun h => haZ (h ▸ hzZ)
  set C := rOf T M ⊓ Subgroup.centralizer ({wOfX d x} : Set G) with hC
  have hCR : C ≤ rOf T M := inf_le_left
  let C' : Subgroup ↥(rOf T M) := C.subgroupOf (rOf T M)
  let v : Fin 4 → G := ![1, d * d, a, (d * d) * a]
  have hzV : d * d ∈ VZ T M := Hyp1281Two.omegaOneCenter_le_VZ T M hzZ
  have hvV : ∀ i, v i ∈ VZ T M := by
    intro i
    fin_cases i
    · exact (VZ T M).one_mem
    · exact hzV
    · exact haV
    · exact (VZ T M).mul_mem hzV haV
  have hvinj : Function.Injective v := by
    intro i j h
    have hza1 : (d * d) * a ≠ 1 := by
      intro h'
      apply haz
      have : (d * d) = a⁻¹ := eq_inv_of_mul_eq_one_left h'
      rw [this]; exact inv_eq_of_mul_eq_one_right haa
    fin_cases i <;> fin_cases j <;> simp [v] at h ⊢ <;>
      first
        | exact hz1 h
        | exact hz1 h.symm
        | exact ha1 h
        | exact ha1 h.symm
        | exact haz h
        | exact haz h.symm
        | exact hza1 h
        | exact hza1 h.symm
  choose e he hev using fun i => exists_comm_eq_of_mem_V c c18 hD hd4 hxL hx3 hΓ (hvV i)
  have heR : ∀ i, e i ∈ rOf T M := fun i => c18.b.A_le (he i)
  let F : Fin 4 → ↥(rOf T M) ⧸ C' := fun i => QuotientGroup.mk ⟨e i, heR i⟩
  have hF : Function.Injective F := by
    intro i j hij
    have h := QuotientGroup.eq.mp hij
    have hk : (e i)⁻¹ * e j ∈ C := Subgroup.mem_subgroupOf.mp h
    have hkw : wOfX d x * ((e i)⁻¹ * e j) = ((e i)⁻¹ * e j) * wOfX d x :=
      Subgroup.mem_centralizer_iff.mp hk.2 (wOfX d x) (Set.mem_singleton _)
    have hkw' : ((e i)⁻¹ * e j) * (wOfX d x)⁻¹ * ((e i)⁻¹ * e j)⁻¹ = (wOfX d x)⁻¹ := by
      have h' : wOfX d x * ((e i)⁻¹ * e j) * (wOfX d x)⁻¹ = (e i)⁻¹ * e j := by
        calc wOfX d x * ((e i)⁻¹ * e j) * (wOfX d x)⁻¹ = (((e i)⁻¹ * e j) * wOfX d x) * (wOfX d x)⁻¹ := by
              rw [hkw]
          _ = (e i)⁻¹ * e j := by group
      calc ((e i)⁻¹ * e j) * (wOfX d x)⁻¹ * ((e i)⁻¹ * e j)⁻¹
          = ((wOfX d x)⁻¹ * (wOfX d x * ((e i)⁻¹ * e j) * (wOfX d x)⁻¹)) * ((e i)⁻¹ * e j)⁻¹ := by group
        _ = (wOfX d x)⁻¹ := by rw [h']; group
    have hvij : v j = v i := by
      calc v j = wOfX d x * e j * (wOfX d x)⁻¹ * (e j)⁻¹ := (hev j).symm
        _ = wOfX d x * e i * (((e i)⁻¹ * e j) * (wOfX d x)⁻¹ * ((e i)⁻¹ * e j)⁻¹) * (e i)⁻¹ := by
            group
        _ = wOfX d x * e i * (wOfX d x)⁻¹ * (e i)⁻¹ := by rw [hkw']
        _ = v i := hev i
    exact (hvinj hvij).symm
  have hcard4 : 4 ≤ Nat.card (↥(rOf T M) ⧸ C') := by
    have := Nat.card_le_card_of_injective F hF
    simpa using this
  have h64 := Subgroup.card_eq_card_quotient_mul_card_subgroup C'
  rw [card_rOf c] at h64
  have hC'C : Nat.card ↥C' = Nat.card ↥C := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCR).toEquiv
  rw [hC'C] at h64
  nlinarith

include c c18 c19 hD hd4 hxL hx3 in
theorem isZ4Sq_centralizer_R
    (hΓ : Subgroup.centralizer (A : Set G) = A) :
    IsZ4Sq ↥(rOf T M ⊓ Subgroup.centralizer ({wOfX d x} : Set G)) := by
  classical
  obtain ⟨a, ha, haV, haZ, hza, haa, hxa, hall⟩ := three_cycle_x c hD hd4 hxL hx3
  have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have hc := Xgen_comm c hD hd4
  have h0 : d ∈ Xgen T M := le_Wgen (dOf_mem_delta c) hd
  have h1 := d1_mem_Xgen c hxL hd
  have h2 := d2_mem_Xgen c hxL hd
  have hwX := wOfX_mem_Xgen c hD hxL
  have hzZ := sq_mem_omegaOneCenter c hD hd4
  have hz1 : d * d ≠ 1 := (dd_facts hd4).2
  have hzz : (d * d) * (d * d) = 1 := (dd_facts hd4).1
  have hx3' : x * x * x = 1 := by rw [← pow_three', ← hx3]; exact pow_orderOf_eq_one x
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ (quasithinOmegaOneCenter T).one_mem)
  have haz : (d * d) ≠ a := fun h => haZ (h ▸ hzZ)
  have hzX : d * d ∈ Xgen T M := (Xgen T M).mul_mem h0 h0
  have haX : a ∈ Xgen T M := VZ_le_Xgen c haV
  have hd₂x : x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹ = d := by
    have : x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * d * (x * x * x)⁻¹ := by group
    rw [this, hx3']; group
  have hs1 : (x * d * x⁻¹) * (x * d * x⁻¹) = a := by rw [ha]; group
  have hs2 : (x * (x * d * x⁻¹) * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) = (d * d) * a := by
    rw [← hxa, ← hs1]; group
  set e₁ : G := d * (x * d * x⁻¹) with he₁
  set e₂ : G := (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) with he₂
  set e₃ : G := x * e₂ * x⁻¹ with he₃
  have he₁X : e₁ ∈ Xgen T M := (Xgen T M).mul_mem h0 h1
  have he₂X : e₂ ∈ Xgen T M := (Xgen T M).mul_mem h1 h2
  have F1 : x * e₁ * x⁻¹ = e₂ := by
    calc x * e₁ * x⁻¹ = (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) := by rw [he₁]; group
      _ = e₂ := rfl
  have F3 : e₁ * e₂ * e₃ = 1 := by
    have he₃' : e₃ = (x * (x * d * x⁻¹) * x⁻¹) * d := by
      calc e₃ = (x * (x * d * x⁻¹) * x⁻¹) * (x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹) := by
            rw [he₃, he₂]; group
        _ = (x * (x * d * x⁻¹) * x⁻¹) * d := by rw [hd₂x]
    let _ : CommGroup ↥(Xgen T M) :=
      { (inferInstance : Group ↥(Xgen T M)) with
        mul_comm := fun u v => Subtype.ext (Xgen_comm c hD hd4 u u.2 v v.2) }
    let D0 : ↥(Xgen T M) := ⟨d, h0⟩
    let D1 : ↥(Xgen T M) := ⟨x * d * x⁻¹, h1⟩
    let D2 : ↥(Xgen T M) := ⟨x * (x * d * x⁻¹) * x⁻¹, h2⟩
    let ZZ : ↥(Xgen T M) := ⟨d * d, hzX⟩
    let AA : ↥(Xgen T M) := ⟨a, haX⟩
    have hD0 : D0 * D0 = ZZ := Subtype.ext rfl
    have hD1 : D1 * D1 = AA := Subtype.ext hs1
    have hD2 : D2 * D2 = ZZ * AA := Subtype.ext hs2
    have hZZ : ZZ * ZZ = 1 := Subtype.ext hzz
    have hAA : AA * AA = 1 := Subtype.ext haa
    have key : (D0 * D1) * (D1 * D2) * (D2 * D0) = 1 := by
      calc (D0 * D1) * (D1 * D2) * (D2 * D0) = (D0 * D0) * (D1 * D1) * (D2 * D2) := by
            simp only [mul_comm, mul_left_comm, mul_assoc]
        _ = (ZZ * ZZ) * (AA * AA) := by
            rw [hD0, hD1, hD2]; simp only [mul_comm, mul_left_comm, mul_assoc]
        _ = 1 := by rw [hZZ, hAA, one_mul]
    have := congrArg Subtype.val key
    rw [he₃']
    simpa [D0, D1, D2, he₁, he₂] using this
  obtain ⟨r, hrW, hrV, hr2, hAeq⟩ := c.exists_Ac_eq c18.b
  subst hAeq
  have hRU := c.rOf_sup_uOfL22_le_kOf hrW hrV hr2
  have hxK : x ∈ kOf T M (c.Ac hrW hrV hr2) := (le_sup_right : yOfL22 T M ≤ _) hxL
  have hxK' : x⁻¹ ∈ kOf T M (c.Ac hrW hrV hr2) := (kOf T M (c.Ac hrW hrV hr2)).inv_mem hxK
  have hdxd : d * x * d⁻¹ ∈ kOf T M (c.Ac hrW hrV hr2) :=
    (Subgroup.mem_normalizer_iff.mp (c.dOf_le_normalizer_kOf hrW hrV hr2 hd) x).mp hxK
  have hzK : d * d ∈ kOf T M (c.Ac hrW hrV hr2) :=
    hRU (Subgroup.mem_sup_left (c.Ac_le_rOf hrW hrV hr2 (c.VZ_le_Ac hrW hrV hr2
      (Hyp1281Two.omegaOneCenter_le_VZ T M hzZ))))
  have he₁K : e₁ ∈ kOf T M (c.Ac hrW hrV hr2) := by
    have e : e₁ = (d * x * d⁻¹) * (d * d) * x⁻¹ := by rw [he₁]; group
    rw [e]
    exact (kOf T M (c.Ac hrW hrV hr2)).mul_mem ((kOf T M (c.Ac hrW hrV hr2)).mul_mem hdxd hzK) hxK'
  have he₂K : e₂ ∈ kOf T M (c.Ac hrW hrV hr2) := by
    have e : e₂ = x * (d * x * d⁻¹) * (d * d) * x⁻¹ * x⁻¹ := by rw [he₂]; group
    rw [e]
    exact (kOf T M (c.Ac hrW hrV hr2)).mul_mem ((kOf T M (c.Ac hrW hrV hr2)).mul_mem
      ((kOf T M (c.Ac hrW hrV hr2)).mul_mem ((kOf T M (c.Ac hrW hrV hr2)).mul_mem hxK hdxd) hzK)
      hxK') hxK'
  have he₁RU : e₁ ∈ rOf T M ⊔ uOfL22 T M := by
    rw [← inf_T_kOf_eq c c19]; exact ⟨Xgen_le_T he₁X, he₁K⟩
  have he₂RU : e₂ ∈ rOf T M ⊔ uOfL22 T M := by
    rw [← inf_T_kOf_eq c c19]; exact ⟨Xgen_le_T he₂X, he₂K⟩
  have hle : rOf T M ≤ rOf T M ⊔ uOfL22 T M := le_sup_left
  have hidx2 : ((rOf T M).subgroupOf (rOf T M ⊔ uOfL22 T M)).index = 2 := by
    have h1 := Subgroup.card_mul_index ((rOf T M).subgroupOf (rOf T M ⊔ uOfL22 T M))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_rOf c,
      c.card_rOf_sup_uOfL22] at h1
    omega
  have hprod : ∀ p q : G, p ∈ rOf T M ⊔ uOfL22 T M → q ∈ rOf T M ⊔ uOfL22 T M → p ∉ rOf T M →
      q ∉ rOf T M → p * q ∈ rOf T M := by
    intro p q hp hq hpR hqR
    have hmul := Subgroup.mul_mem_iff_of_index_two hidx2 (a := (⟨p, hp⟩ : ↥(rOf T M ⊔ uOfL22 T M)))
      (b := ⟨q, hq⟩)
    have hpR' : (⟨p, hp⟩ : ↥(rOf T M ⊔ uOfL22 T M)) ∉ (rOf T M).subgroupOf (rOf T M ⊔ uOfL22 T M) :=
      fun h => hpR (Subgroup.mem_subgroupOf.mp h)
    have hqR' : (⟨q, hq⟩ : ↥(rOf T M ⊔ uOfL22 T M)) ∉ (rOf T M).subgroupOf (rOf T M ⊔ uOfL22 T M) :=
      fun h => hqR (Subgroup.mem_subgroupOf.mp h)
    exact Subgroup.mem_subgroupOf.mp (hmul.mpr ⟨fun h => absurd h hpR', fun h => absurd h hqR'⟩)
  have hxR : ∀ u, x * u * x⁻¹ ∈ rOf T M ↔ u ∈ rOf T M := by
    intro u
    have hxN : x ∈ Subgroup.normalizer (rOf T M : Set G) := M_le_normalizer_rOf c (c.h1281.le hxL)
    exact (Subgroup.mem_normalizer_iff.mp hxN u).symm
  have he₁R : e₁ ∈ rOf T M := by
    by_contra hn1
    have hn2 : e₂ ∉ rOf T M := fun h => hn1 ((hxR e₁).mp (by rw [F1]; exact h))
    have hn3 : e₃ ∉ rOf T M := fun h => hn2 ((hxR e₂).mp (by rw [← he₃]; exact h))
    have hmem := hprod e₁ e₂ he₁RU he₂RU hn1 hn2
    apply hn3
    have : e₃ = (e₁ * e₂)⁻¹ := eq_inv_of_mul_eq_one_right F3
    rw [this]; exact (rOf T M).inv_mem hmem
  have he₂R : e₂ ∈ rOf T M := by rw [← F1]; exact (hxR e₁).mpr he₁R
  have hwX' : ∀ e ∈ Xgen T M, e ∈ Subgroup.centralizer ({wOfX d x} : Set G) := by
    intro e he
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh; subst hh
    exact hc _ hwX _ he
  have he₁sq : e₁ * e₁ = (d * d) * a := by
    have hcm : Commute (x * d * x⁻¹) d := hc _ h1 _ h0
    calc e₁ * e₁ = d * ((x * d * x⁻¹) * d) * (x * d * x⁻¹) := by rw [he₁]; group
      _ = d * (d * (x * d * x⁻¹)) * (x * d * x⁻¹) := by rw [hcm.eq]
      _ = (d * d) * ((x * d * x⁻¹) * (x * d * x⁻¹)) := by group
      _ = (d * d) * a := by rw [hs1]
  have he₂sq : e₂ * e₂ = d * d := by
    have hcm : Commute (x * (x * d * x⁻¹) * x⁻¹) (x * d * x⁻¹) := hc _ h2 _ h1
    calc e₂ * e₂ = (x * d * x⁻¹) * ((x * (x * d * x⁻¹) * x⁻¹) * (x * d * x⁻¹)) *
          (x * (x * d * x⁻¹) * x⁻¹) := by rw [he₂]; group
      _ = (x * d * x⁻¹) * ((x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)) * (x * (x * d * x⁻¹) * x⁻¹) := by
          rw [hcm.eq]
      _ = ((x * d * x⁻¹) * (x * d * x⁻¹)) * ((x * (x * d * x⁻¹) * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹)) := by
          group
      _ = a * ((d * d) * a) := by rw [hs1, hs2]
      _ = d * d := by
          calc a * ((d * d) * a) = (a * (d * d)) * a := by group
            _ = ((d * d) * a) * a := by rw [← hza]
            _ = d * d := by rw [mul_assoc, haa, mul_one]
  have hza1 : (d * d) * a ≠ 1 := by
    intro h'
    apply haz
    have : (d * d) = a⁻¹ := eq_inv_of_mul_eq_one_left h'
    rw [this]; exact inv_eq_of_mul_eq_one_right haa
  have hord1 : orderOf e₁ = 4 := by
    refine orderOf_eq_four_of_sq (by rw [he₁sq]; exact hza1) ?_
    rw [he₁sq]
    calc (d * d) * a * ((d * d) * a) = (d * d) * (a * (d * d)) * a := by group
      _ = (d * d) * ((d * d) * a) * a := by rw [← hza]
      _ = ((d * d) * (d * d)) * (a * a) := by group
      _ = 1 := by rw [hzz, haa, one_mul]
  have hord2 : orderOf e₂ = 4 := by
    refine orderOf_eq_four_of_sq (by rw [he₂sq]; exact hz1) ?_
    rw [he₂sq]; exact hzz
  have hne : e₁ * e₁ ≠ e₂ * e₂ := by
    rw [he₁sq, he₂sq]
    intro h'
    apply ha1
    have : (d * d) * a = (d * d) * 1 := by rw [h', mul_one]
    exact mul_left_cancel this
  exact isZ4Sq_of_commuting_cyclic (hc _ he₁X _ he₂X) hord1 hord2 hne
    ⟨he₁R, hwX' _ he₁X⟩ ⟨he₂R, hwX' _ he₂X⟩ (card_centralizer_R_le c c18 hD hd4 hxL hx3 hΓ)

end Main

end S143

end CFSG.Quasithin
