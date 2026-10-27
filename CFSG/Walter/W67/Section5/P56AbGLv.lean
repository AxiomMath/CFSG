module

public import CFSG.Walter.W67.Section5.P56AbQ0

public section

namespace CFSG.Walter.W67

open P56Ab

namespace P56AbData

variable {G : Type} [Group G] [Finite G] (d : P56AbData G)

theorem factorization_card_GL_le {v n : ℕ} (hv : v.Prime) (hvn : orderOf (3 : ZMod v) = n)
    (hv2 : v ≠ 2) (hn : 0 < n) :
    (∏ i : Fin (2 * n), (3 ^ (2 * n) - 3 ^ (i : ℕ))).factorization v ≤
      2 * (3 ^ n - 1).factorization v := by
  have hv3 : v ≠ 3 := by
    rintro rfl
    have h0 : (3 : ZMod 3) = 0 := rfl
    rw [h0, orderOf_eq_zero_iff.mpr] at hvn
    · omega
    · rw [isOfFinOrder_iff_pow_eq_one]
      rintro ⟨k, hk, hk1⟩
      rw [zero_pow hk.ne'] at hk1
      exact zero_ne_one hk1
  rw [Fin.prod_univ_eq_prod_range (fun i => 3 ^ (2 * n) - 3 ^ i) (2 * n)]
  have hne : ∀ i ∈ Finset.range (2 * n), 3 ^ (2 * n) - 3 ^ i ≠ 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : 3 ^ i < 3 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) hi
    omega
  rw [Nat.factorization_prod hne, Finset.sum_apply']
  have hfac : ∀ i ∈ Finset.range (2 * n),
      (3 ^ (2 * n) - 3 ^ i).factorization v = (3 ^ (2 * n - i) - 1).factorization v := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : 3 ^ (2 * n) - 3 ^ i = 3 ^ i * (3 ^ (2 * n - i) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi.le]
    have h2 : 3 ^ (2 * n - i) - 1 ≠ 0 := by
      have : 1 < 3 ^ (2 * n - i) := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    rw [h1, Nat.factorization_mul (by positivity) h2, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hv3 ((Nat.prime_dvd_prime_iff_eq hv
        Nat.prime_three).mp h)), smul_zero, zero_add]
  rw [Finset.sum_congr rfl hfac]
  have hsub : ({0, n} : Finset ℕ) ⊆ Finset.range (2 * n) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_subset hsub (fun i hi hi' => by
    rw [Finset.mem_range] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi'
    apply Nat.factorization_eq_zero_of_not_dvd
    rw [dvd_three_pow_sub_one_iff_of_orderOf hvn]
    intro h
    obtain ⟨c, hc⟩ := h
    have hle : 2 * n - i ≤ 2 * n := Nat.sub_le _ _
    have : c = 1 ∨ c = 2 := by
      rcases c with _ | _ | _ | c
      · omega
      · left; rfl
      · right; rfl
      · rw [hc] at hle
        nlinarith
    rcases this with rfl | rfl <;> omega)]
  rw [Finset.sum_pair (by omega), Nat.sub_zero, show 2 * n - n = n by omega]
  have h2n : 3 ^ (2 * n) - 1 = (3 ^ n - 1) * (3 ^ n + 1) := by
    have : 3 ^ (2 * n) = 3 ^ n * 3 ^ n := by rw [two_mul, pow_add]
    rw [this]
    obtain ⟨y, hy⟩ : ∃ y, 3 ^ n = y + 1 := ⟨3 ^ n - 1, by
      have : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
      omega⟩
    rw [hy, Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)
  have hplus : ¬ v ∣ 3 ^ n + 1 := by
    intro h
    have hm : v ∣ 3 ^ n - 1 := (dvd_three_pow_sub_one_iff_of_orderOf hvn n).mpr dvd_rfl
    have : v ∣ (3 ^ n + 1) - (3 ^ n - 1) := Nat.dvd_sub h hm
    have h2 : (3 ^ n + 1) - (3 ^ n - 1) = 2 := by
      have : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
      omega
    rw [h2] at this
    exact hv2 ((Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp this)
  have hne1 : 3 ^ n - 1 ≠ 0 := by
    have : 1 < 3 ^ n := Nat.one_lt_pow hn.ne' (by norm_num)
    omega
  rw [h2n, Nat.factorization_mul hne1 (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hplus]
  omega

@[expose] noncomputable def prodEquivV : d.P₁ × d.P₂ ≃* d.V :=
  MulEquiv.ofBijective
    ({ toFun := fun p => ⟨(p.1 : G) * p.2,
          d.V.mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
       map_one' := Subtype.ext (by simp)
       map_mul' := fun p q => Subtype.ext (by
         simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
         calc (p.1 : G) * q.1 * (p.2 * q.2) = (p.1 : G) * ((q.1 : G) * p.2) * q.2 := by group
           _ = (p.1 : G) * ((p.2 : G) * q.1) * q.2 := by rw [d.P₁_comm_P₂ _ q.1.2 _ p.2.2]
           _ = (p.1 : G) * p.2 * (q.1 * q.2) := by group) } : d.P₁ × d.P₂ →* d.V)
    ⟨fun p q h => by
      have h' : (p.1 : G) * p.2 = q.1 * q.2 := congrArg Subtype.val h
      have h1 : (q.1 : G)⁻¹ * p.1 = q.2 * (p.2 : G)⁻¹ := by
        calc (q.1 : G)⁻¹ * p.1 = (q.1 : G)⁻¹ * ((p.1 : G) * p.2) * (p.2 : G)⁻¹ := by group
          _ = (q.1 : G)⁻¹ * ((q.1 : G) * q.2) * (p.2 : G)⁻¹ := by rw [h']
          _ = q.2 * (p.2 : G)⁻¹ := by group
      have h2 : (q.1 : G)⁻¹ * p.1 ∈ d.P₁ ⊓ d.P₂ :=
        Subgroup.mem_inf.mpr ⟨d.P₁.mul_mem (d.P₁.inv_mem q.1.2) p.1.2,
          h1 ▸ d.P₂.mul_mem q.2.2 (d.P₂.inv_mem p.2.2)⟩
      rw [d.P₁_inf_P₂, Subgroup.mem_bot, inv_mul_eq_one] at h2
      have h3 : (p.2 : G) = q.2 := by
        rw [← h2] at h'
        exact mul_left_cancel h'
      exact Prod.ext (Subtype.ext h2.symm) (Subtype.ext h3),
     fun m => by
      obtain ⟨a, ha, b, hb, hab⟩ := d.mem_V.mp m.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩⟩

theorem prodEquivV_apply_coe (p : d.P₁ × d.P₂) : ((d.prodEquivV p : d.V) : G) = p.1 * p.2 := rfl

@[expose] noncomputable def prodAut (A B : Type*) [Group A] [Group B] :
    MulAut A × MulAut B →* MulAut (A × B) where
  toFun αβ := MulEquiv.prodCongr αβ.1 αβ.2
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

theorem U_le_normalizer_P₁ {v : ℕ} : d.U v ≤ Subgroup.normalizer (d.P₁ : Set G) :=
  d.U_le_B.trans d.B_le_normalizer₁

theorem U_le_normalizer_P₂ {v : ℕ} : d.U v ≤ Subgroup.normalizer (d.P₂ : Set G) :=
  d.U_le_B.trans d.B_le_normalizer₂

@[expose] noncomputable def theta (v : ℕ) : d.U v × d.U v →* MulAut d.V :=
  (MulAut.congr d.prodEquivV).toMonoidHom.comp ((prodAut d.P₁ d.P₂).comp
    ((conjAut (d.U v) d.P₁ d.U_le_normalizer_P₁).prodMap
      (conjAut (d.U v) d.P₂ d.U_le_normalizer_P₂)))

theorem theta_apply {v : ℕ} (u : d.U v × d.U v) (p : d.P₁ × d.P₂) :
    d.theta v u (d.prodEquivV p) =
      d.prodEquivV (conjAut (d.U v) d.P₁ d.U_le_normalizer_P₁ u.1 p.1,
        conjAut (d.U v) d.P₂ d.U_le_normalizer_P₂ u.2 p.2) := by
  change d.prodEquivV ((prodAut d.P₁ d.P₂ ((conjAut (d.U v) d.P₁ d.U_le_normalizer_P₁ u.1,
    conjAut (d.U v) d.P₂ d.U_le_normalizer_P₂ u.2))) (d.prodEquivV.symm (d.prodEquivV p))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem eq_one_of_mem_B_of_comm_P {P : Subgroup G} (hP : P = d.P₁ ∨ P = d.P₂) {b : G}
    (hb : b ∈ d.B) (hbP : ∀ y ∈ P, b * y = y * b) : b = 1 := by
  by_contra hb1
  have hfpf : ∀ y ∈ P, b * y = y * b → y = 1 := by
    rcases hP with rfl | rfl
    · exact d.fixedPointFree₁ b hb hb1
    · exact d.fixedPointFree₂ b hb hb1
  have hPbot : P = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    exact hfpf y hy (hbP y hy)
  have hcard : Nat.card P = 3 ^ d.n := by
    rcases hP with rfl | rfl
    · exact d.card_P₁
    · exact d.card_P₂
  rw [hPbot, Subgroup.card_bot] at hcard
  have : 1 < 3 ^ d.n := Nat.one_lt_pow (by have := d.three_le_n; omega) (by norm_num)
  omega

theorem theta_injective (v : ℕ) : Function.Injective (d.theta v) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨u₁, u₂⟩ hu
  rw [MonoidHom.mem_ker] at hu
  rw [Subgroup.mem_bot]
  have h1 : ∀ a : d.P₁, ((conjAut (d.U v) d.P₁ d.U_le_normalizer_P₁ u₁ a : d.P₁) : G) = a := by
    intro a
    have := congrArg (fun γ : MulAut d.V => ((γ (d.prodEquivV (a, 1)) : d.V) : G)) hu
    simp only [theta_apply, prodEquivV_apply_coe, map_one, OneMemClass.coe_one, mul_one,
      MulAut.one_apply] at this
    exact this
  have h2 : ∀ b : d.P₂, ((conjAut (d.U v) d.P₂ d.U_le_normalizer_P₂ u₂ b : d.P₂) : G) = b := by
    intro b
    have := congrArg (fun γ : MulAut d.V => ((γ (d.prodEquivV (1, b)) : d.V) : G)) hu
    simp only [theta_apply, prodEquivV_apply_coe, map_one, OneMemClass.coe_one, one_mul,
      MulAut.one_apply] at this
    exact this
  have hu₁ : (u₁ : G) = 1 := by
    apply d.eq_one_of_mem_B_of_comm_P (Or.inl rfl) (d.U_le_B u₁.2)
    intro y hy
    have := h1 ⟨y, hy⟩
    rw [conjAut_apply_coe] at this
    calc (u₁ : G) * y = (u₁ : G) * y * (u₁ : G)⁻¹ * u₁ := by group
      _ = y * u₁ := by rw [this]
  have hu₂ : (u₂ : G) = 1 := by
    apply d.eq_one_of_mem_B_of_comm_P (Or.inr rfl) (d.U_le_B u₂.2)
    intro y hy
    have := h2 ⟨y, hy⟩
    rw [conjAut_apply_coe] at this
    calc (u₂ : G) * y = (u₂ : G) * y * (u₂ : G)⁻¹ * u₂ := by group
      _ = y * u₂ := by rw [this]
  exact Prod.ext (Subtype.ext hu₁) (Subtype.ext hu₂)

theorem pow_le_card_U {v : ℕ} [hv : Fact v.Prime] :
    v ^ (Nat.card d.B).factorization v ≤ Nat.card (d.U v) := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow v d.B))
  have hS : Nat.card S = v ^ (Nat.card d.B).factorization v := Sylow.card_eq_multiplicity S
  have hle : (S : Subgroup d.B).map d.B.subtype ≤ d.U v := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_⟩
    have h1 : (⟨s, hs⟩ : S) ^ (v ^ (Nat.card d.B).factorization v) = 1 := by
      rw [← hS]
      exact pow_card_eq_one'
    have := congrArg (fun z : S => (((z : d.B) : G))) h1
    simpa using this
  have := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective d.B.subtype_injective, hS] at this
  exact this

theorem factorization_card_B {v : ℕ} [hv : Fact v.Prime] (hvn : orderOf (3 : ZMod v) = d.n) :
    (3 ^ d.n - 1).factorization v = (Nat.card d.B).factorization v := by
  rw [← d.card_B, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h => d.v_ne_two hvn
      ((Nat.prime_dvd_prime_iff_eq hv.out Nat.prime_two).mp h)), zero_add]

theorem vsubgroup_mulAut {v : ℕ} [hv : Fact v.Prime] (hvn : orderOf (3 : ZMod v) = d.n)
    {R : Subgroup (MulAut d.V)} (hR : IsPGroup v R) :
    (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧
      ∀ E : Subgroup (MulAut d.V), E ≤ R → (∀ x ∈ E, x ^ v = 1) → Nat.card E ≤ v ^ 2 := by
  set T := (d.theta v).range with hTdef
  have hT : (Nat.card (MulAut d.V)).factorization v ≤ (Nat.card T).factorization v := by
    obtain ⟨e⟩ := SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3)
      (W := d.V) (fun a b => Subtype.ext (d.V_comm a.2 b.2))
      (fun a => Subtype.ext (by simpa using d.V_pow a.2)) d.card_V
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [SectionRank.Ccomm.card_mulAut_eq_card_GL e, SectionRank.Ccomm.card_GL_zmod]
    have h1 := factorization_card_GL_le hv.out hvn (d.v_ne_two hvn)
      (by have := d.three_le_n; omega)
    rw [d.factorization_card_B hvn] at h1
    have hTcard : Nat.card T = Nat.card (d.U v) * Nat.card (d.U v) := by
      rw [hTdef, MonoidHom.range_eq_map, Subgroup.card_map_of_injective (d.theta_injective v),
        Subgroup.card_top, Nat.card_prod]
    have hU := d.pow_le_card_U (v := v)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (d.U_isPGroup (v := v))
    rw [hTcard, hk, ← pow_add, Nat.Prime.factorization_pow hv.out, Finsupp.single_eq_same]
    rw [hk] at hU
    have := (Nat.pow_le_pow_iff_right hv.out.one_lt).mp hU
    omega
  obtain ⟨f, hf⟩ := exists_injective_of_factorization_le T hT R hR
  let eT : (d.U v × d.U v) ≃* T :=
    MulEquiv.ofBijective (d.theta v).rangeRestrict
      ⟨fun a b h => d.theta_injective v (congrArg Subtype.val h),
        (d.theta v).rangeRestrict_surjective⟩
  let g : R →* d.U v × d.U v := eT.symm.toMonoidHom.comp f
  have hg : Function.Injective g := eT.symm.injective.comp hf
  have hcycB : IsCyclic d.B := d.B_cyclic
  have hcyc : IsCyclic (d.U v) := Subgroup.isCyclic_of_le d.U_le_B
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    have h := hg.eq_iff (a := ⟨a, ha⟩ * ⟨b, hb⟩) (b := ⟨b, hb⟩ * ⟨a, ha⟩)
    have hcomm : ∀ x y : d.U v × d.U v, x * y = y * x := by
      intro x y
      have hU : ∀ s t : d.U v, s * t = t * s := fun s t =>
        Subtype.ext (d.B_comm (d.U_le_B s.2) (d.U_le_B t.2))
      exact Prod.ext (hU _ _) (hU _ _)
    have : g (⟨a, ha⟩ * ⟨b, hb⟩) = g (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul, hcomm]
    exact congrArg Subtype.val (h.mp this)
  · intro E hER hE
    have hEcard : Nat.card E = Nat.card ((E.subgroupOf R).map g) := by
      rw [Subgroup.card_map_of_injective hg,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hER).toEquiv]
    rw [hEcard]
    refine card_le_sq_of_ker_inf (MonoidHom.fst _ _) (MonoidHom.snd _ _)
      (fun x h1 h2 => Prod.ext h1 h2) hv.out.pos _ ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ v = 1 := Subtype.ext (by simpa using hE _ hx)
    rw [this, map_one]


end P56AbData

end CFSG.Walter.W67
