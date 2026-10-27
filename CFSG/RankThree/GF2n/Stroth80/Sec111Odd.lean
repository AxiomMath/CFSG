module

public import CFSG.RankThree.GF2n.Stroth80.Sec11LinAlg

public section


namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.mem_normalizer_QB_of_centralizes (hc : Ctx M Q Z B) {y : G}
    (hy : ∀ b ∈ B, y * b * y⁻¹ = b) :
    y ∈ Subgroup.normalizer ((QB B : Subgroup G) : Set G) := by
  obtain ⟨g, hg⟩ := hc.conj
  have hyN : y ∈ Subgroup.normalizer (B : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    rw [hy b hb]
    exact hb
  have : Subgroup.normalizer (B : Set G) = conjSubgroup g M := (Ctx.QB_eq hc hg).1
  rw [(Ctx.QB_eq hc hg).2, mem_normalizer_conj_iff]
  rw [this] at hyN
  exact hc.hyp.Q_normal.2 (mem_conjSubgroup.mp hyN)

theorem Ctx.card_QB_pow (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) :
    ∃ j : ℕ, Nat.card (QB B) = 2 ^ j := by
  obtain ⟨g, hg⟩ := hc.conj
  obtain ⟨k, k', hZk, -⟩ := hc.hyp.cp
  refine ⟨k * (2 * n + 1), ?_⟩
  rw [(Ctx.QB_eq hc hg).2, card_conjSubgroup]
  unfold Width at hw
  rw [hw, hZk, ← pow_mul]

theorem Ctx.eq_one_of_odd_comm (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) {x : G}
    (hxH : x ∈ H0 M Z) (hL : ∀ t ∈ LB M Q B, ⁅x, t⁆ ∈ Q) (hB : ∀ u ∈ B, ⁅x, u⁆ ∈ Z)
    (hodd : Odd (orderOf x)) : x = 1 := by
  classical
  have hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp hxH.2 z hz
    rw [← this]
    group
  have hxB : ∀ u ∈ B, x * u * x⁻¹ = u := by
    intro u hu
    set z := ⁅x, u⁆ with hzdef
    have hzZ : z ∈ Z := hB u hu
    have hzu : x * u * x⁻¹ = z * u := by rw [hzdef, commutatorElement_def]; group
    have hpow : ∀ k : ℕ, x ^ k * u * (x ^ k)⁻¹ = z ^ k * u := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have e1 : x ^ (k + 1) * u * (x ^ (k + 1))⁻¹ = x * (x ^ k * u * (x ^ k)⁻¹) * x⁻¹ := by
          rw [pow_succ']
          group
        rw [e1, ih]
        have e2 : x * (z ^ k * u) * x⁻¹ = (x * z * x⁻¹) ^ k * (x * u * x⁻¹) := by
          rw [conj_pow]
          group
        rw [e2, hxZ z hzZ, hzu, pow_succ]
        group
    have h1 := hpow (orderOf x)
    rw [pow_orderOf_eq_one, inv_one, mul_one, one_mul] at h1
    have h2 : z ^ orderOf x = 1 := by
      have h3 : z ^ orderOf x * u = 1 * u := by rw [← h1, one_mul]
      exact mul_right_cancel h3
    obtain ⟨j, hj⟩ := hodd
    have hz2 : z ^ 2 = 1 := hc.hyp.toHyp79.sq_eq_one z hzZ
    have hz1 : z = 1 := by
      calc z = z ^ (2 * j + 1) := by rw [pow_succ, pow_mul, hz2, one_pow, one_mul]
        _ = 1 := by rw [← hj]; exact h2
    rw [hzu, hz1, one_mul]
  obtain ⟨ω, h1, h2, h3, h4⟩ := hc.exists_swap'
  set x' := ω⁻¹ * x * ω with hx'def
  have hωZ : ∀ z ∈ Z, ω * z * ω⁻¹ ∈ B := fun z hz => by
    rw [← h3]
    exact mem_conjSubgroup.mpr (by rw [show ω⁻¹ * (ω * z * ω⁻¹) * ω = z by group]; exact hz)
  have hωB : ∀ u ∈ B, ω * u * ω⁻¹ ∈ Z := fun u hu => by
    rw [← h4]
    exact mem_conjSubgroup.mpr (by rw [show ω⁻¹ * (ω * u * ω⁻¹) * ω = u by group]; exact hu)
  have hx'Z : ∀ z ∈ Z, x' * z * x'⁻¹ = z := by
    intro z hz
    have e : x' * z * x'⁻¹ = ω⁻¹ * (x * (ω * z * ω⁻¹) * x⁻¹) * ω := by
      simp only [hx'def]
      group
    rw [e, hxB _ (hωZ z hz)]
    group
  have hx'B : ∀ u ∈ B, x' * u * x'⁻¹ = u := by
    intro u hu
    have e : x' * u * x'⁻¹ = ω⁻¹ * (x * (ω * u * ω⁻¹) * x⁻¹) * ω := by
      simp only [hx'def]
      group
    rw [e, hxZ _ (hωB u hu)]
    group
  have hx'H : x' ∈ H0 M Z := by
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    · rw [← hc.hyp.normalizer_Z.1]
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      rw [hx'Z z hz]
      exact hz
    · exact (mul_inv_eq_iff_eq_mul.mp (hx'Z z hz)).symm
  have hx'pow : x' ^ orderOf x = 1 := by
    have : x' ^ orderOf x = ω⁻¹ * x ^ orderOf x * ω := by
      have := conj_pow (a := ω⁻¹) (b := x) (i := orderOf x)
      rw [inv_inv] at this
      exact this
    rw [this, pow_orderOf_eq_one]
    group
  obtain ⟨m, γ, M₀, hm, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, hbs, hBline, hcent, -⟩ := hc.dictB h
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  set T : M₀.E ≃ₗ[GaloisField 2 m] M₀.E := φ ⟨x', hx'H⟩ with hTdef
  have hTπ : ∀ y ∈ Q, M₀.π (x' * y * x'⁻¹) = T (M₀.π y) := fun y hy => hφπ ⟨x', hx'H⟩ y hy
  have hTb : T b = b := by
    obtain ⟨u, huB, huQ, hu⟩ : b ∈ M₀.img B := (hBline b).mpr ⟨1, (one_smul _ b).symm⟩
    rw [← hu, ← hTπ u huQ, hx'B u huB]
  have hTiso : ∀ e, M₀.Qf (T e) = M₀.Qf e := hφiso ⟨x', hx'H⟩
  have hTpow : T ^ orderOf x = 1 := by
    rw [hTdef, ← map_pow]
    have : (⟨x', hx'H⟩ : ↥(H0 M Z)) ^ orderOf x = 1 := Subtype.ext (by simpa using hx'pow)
    rw [this, map_one]
  have hTpowLin : (T : M₀.E →ₗ[GaloisField 2 m] M₀.E) ^ orderOf x = 1 :=
    linearMap_pow_eq_one_of_equiv_pow_eq_one hTpow
  set D : Subgroup G := Q ⊓ QB B with hDdef
  have hS4 : ∀ v : M₀.E, M₀.B v b = 0 → T v - v ∈ M₀.img D := by
    intro v hv
    obtain ⟨c, hcQ, rfl⟩ := M₀.π_surj v
    have hcC : c ∈ Subgroup.centralizer (B : Set G) := (hcent c hcQ).mpr hv
    have hy : ω * c * ω⁻¹ ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) := by
      rw [← hc.conj_centralizer_B h1 h4]
      exact mem_conjSubgroup.mpr (by
        rw [show ω⁻¹ * (ω * c * ω⁻¹) * ω = c by group]
        exact ⟨hcQ, hcC⟩)
    have hyL : ω * c * ω⁻¹ ∈ LB M Q B := by
      have : ω * c * ω⁻¹ ∈ QB B ⊓ M := by rw [hc.QB_inf_M_eq]; exact hy
      exact Subgroup.mem_sup_right this
    have hxQ1 : ⁅x, ω * c * ω⁻¹⁆ ∈ Q := hL _ hyL
    have hxQ2 : ⁅x, ω * c * ω⁻¹⁆ ∈ QB B := by
      have hN := hc.mem_normalizer_QB_of_centralizes hxB
      rw [commutatorElement_def]
      exact (QB B).mul_mem ((Subgroup.mem_normalizer_iff.mp hN _).mp hy.1) ((QB B).inv_mem hy.1)
    have hcomm : ⁅x', c⁆ = ω⁻¹ * ⁅x, ω * c * ω⁻¹⁆ * ω := by
      simp only [hx'def, commutatorElement_def]
      group
    have hcommD : ⁅x', c⁆ ∈ D := by
      rw [hcomm]
      have hw' : ⁅x, ω * c * ω⁻¹⁆ ∈ conjSubgroup ω D := by
        rw [hDdef, conjSubgroup_inf, h1, h2, inf_comm]
        exact ⟨hxQ1, hxQ2⟩
      exact mem_conjSubgroup.mp hw'
    have hcQ' : ⁅x', c⁆ ∈ Q := hcommD.1
    have e3 : x' * c * x'⁻¹ = ⁅x', c⁆ * c := by rw [commutatorElement_def]; group
    have h5 : M₀.π (x' * c * x'⁻¹) = M₀.π ⁅x', c⁆ + M₀.π c := by
      rw [e3, M₀.π_mul _ hcQ' _ hcQ]
    rw [hTπ c hcQ] at h5
    have h6 : T (M₀.π c) - M₀.π c = M₀.π ⁅x', c⁆ := by rw [h5]; abel
    rw [h6]
    exact M₀.pi_mem_img hcommD hcQ'
  have hS5 : ∀ e, M₀.B (T e - e) b = 0 := by
    intro e
    have h7 := Tim79.QuadModel.B_iso (T := (T : M₀.E →ₗ[GaloisField 2 m] M₀.E)) hTiso e b
    rw [map_sub, LinearMap.sub_apply]
    have h8 : M₀.B (T e) b = M₀.B e b := by
      have := h7
      rwa [show (T : M₀.E →ₗ[GaloisField 2 m] M₀.E) b = b from hTb] at this
    rw [h8, sub_self]
  have hrange : ∀ e, T e - e ∈ M₀.img D := by
    intro e
    have hmem : T e - e ∈ LinearMap.range ((T : M₀.E →ₗ[GaloisField 2 m] M₀.E) - 1) :=
      ⟨e, by simp⟩
    obtain ⟨w, ⟨e', rfl⟩, hw'⟩ :=
      range_sub_one_le_map_range hodd hTpowLin hmem
    have := hS4 (((T : M₀.E →ₗ[GaloisField 2 m] M₀.E) - 1) e') (by
      simpa using hS5 e')
    simpa [← hw'] using this
  have hDiso : ∀ v ∈ M₀.img D, ∀ v' ∈ M₀.img D, M₀.B v v' = 0 := by
    rintro _ ⟨y, hyD, hyQ, rfl⟩ _ ⟨y', hy'D, hy'Q, rfl⟩
    have hcomm := hc.inf_QB_elemAbelian.1.is_comm.comm ⟨y, hyD⟩ ⟨y', hy'D⟩
    exact (M₀.comm_iff_B h.reg hyQ hy'Q).mp (congrArg Subtype.val hcomm)
  have hsq : ∀ e, T (T e) = e :=
    Tim79.QuadModel.sq_eq_one_of_isotropic_range M₀ hTiso fun e e' =>
      hDiso _ (hrange e) _ (hrange e')
  have hT1 : T = 1 := by
    have hTT : T * T = 1 := LinearEquiv.ext fun e => hsq e
    obtain ⟨j, hj⟩ := hodd
    have hT2 : T ^ 2 = 1 := by rw [sq]; exact hTT
    have : T ^ (orderOf x) = T := by
      rw [hj, pow_succ, pow_mul, hT2, one_pow, one_mul]
    rw [← this]
    exact hTpow
  have hx'Q : x' ∈ Q := (hφker ⟨x', hx'H⟩).mp hT1
  have hxQB : x ∈ QB B := by
    rw [← h1]
    exact mem_conjSubgroup.mpr hx'Q
  obtain ⟨j, hj⟩ := hc.card_QB_pow hw
  have hdvd : orderOf x ∣ 2 ^ j := by
    rw [← hj]
    exact Subgroup.orderOf_dvd_natCard (QB B) hxQB
  have hcop : Nat.Coprime (orderOf x) (2 ^ j) := Nat.Coprime.pow_right j hodd.coprime_two_right
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

end CFSG.RankThree.GF2n.Stroth80
