module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7B
public import CFSG.Quasithin.Vol2.Ch10SecQ3CS
public import CFSG.Quasithin.Vol2.Ch10SecQ3CW

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS.K7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem B0_le_normalizer_fsuUL (hyp : Hyp10 G T L I) :
    B0 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
  (Subgroup.closure_le _).mpr fun _ ⟨⟨hx, hxN⟩, _⟩ => (normalizes_of_mem hyp hx hxN).1

theorem B0_le_normalizer_conjugate (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) :
    B0 T L ≤ Subgroup.normalizer (CFSG.conjugate (fsuUL T L I) t : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨⟨hy, hyN⟩, -⟩
  obtain ⟨h2L0, h2N⟩ := conj_mem_of_mem ht hy hyN
  have hN := (normalizes_of_mem hyp h2L0 h2N).1
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro x
  rw [SecA.mem_conjugate_iff, SecA.mem_conjugate_iff]
  have e : t * (y * x * y⁻¹) * t⁻¹ = (t * y * t⁻¹) * (t * x * t⁻¹) * (t * y * t⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hN _

theorem exists_E9_aux (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1 : Case10_1_1One T L I n)
    (hn3 : 3 ∣ 2 ^ n - 1) : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) ∧
      ∃ a ∈ B0 T L, ∃ b ∈ B0 T L, orderOf a = 3 ∧ orderOf b = 3 ∧
      (∀ v ∈ CFSG.conjugate (fsuUL T L I) t, a * v * a⁻¹ = v) ∧
      (¬ ∀ v ∈ fsuUL T L I, a * v * a⁻¹ = v) ∧ (∀ v ∈ fsuUL T L I, b * v * b⁻¹ = v) ∧
      (¬ ∀ v ∈ CFSG.conjugate (fsuUL T L I) t, b * v * b⁻¹ = v) := by
  obtain ⟨hUab, F, _, _, _, hn2, hF, ⟨nc⟩⟩ := SecA.exists_natCoord hyp h1
  obtain ⟨l, hlL, hlN, hlT0, hlo, μ, hμ, hl⟩ := exists_torus_gen h37 h38 hyp hF (by omega) nc
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hyp.not_normal h
  have hLV₂ := SecA.conjugate_fsuUL_le_centralizer h37 h38 hyp ht htn
  have htn' : t⁻¹ ∉ Subgroup.normalizer (L : Set G) := fun h => htn (by
    simpa using Subgroup.inv_mem _ h)
  have hLV₁ := SecA.conjugate_fsuUL_le_centralizer h37 h38 hyp (T.inv_mem ht) htn'
  have hlo3 : 3 ∣ orderOf l := by
    refine hn3.trans ?_
    have h := orderOf_map_dvd (conjAct (fsuUL T L I)) ⟨l, hlN⟩
    rw [hl, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_conj_dU hF hμ,
      Subgroup.orderOf_mk] at h
    exact h
  set a := l ^ (orderOf l / 3) with ha
  have ha3 : orderOf a = 3 := orderOf_pow_orderOf_div (orderOf_pos l).ne' hlo3
  have haL : a ∈ L := L.pow_mem hlL _
  have haL0 : a ∈ fsuL0 T L := SecA.le_fsuL0 T L haL
  have haN : a ∈ Subgroup.normalizer (T0 T L : Set G) := Subgroup.pow_mem _ hlT0 _
  have haB : a ∈ B0 T L := mem_oTwoUpper_of_odd ⟨haL0, haN⟩ (by rw [ha3]; decide)
  have haV₂ : ∀ v ∈ CFSG.conjugate (fsuUL T L I) t, a * v * a⁻¹ = v := fun v hv => by
    rw [Subgroup.mem_centralizer_iff.mp (hLV₂ hv) a haL, mul_inv_cancel_right]
  have haV₁ : ¬ ∀ v ∈ fsuUL T L I, a * v * a⁻¹ = v := fun h => by
    have := SecA.eq_one_of_forall_conj_eq h37 h38 hyp ht htn haL0 (by rw [ha3]; decide) h haV₂
    rw [this, orderOf_one] at ha3
    omega
  have hb3 : orderOf (t⁻¹ * a * t) = 3 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj t⁻¹) a
    simp only [MulAut.conj_apply, inv_inv] at h
    rw [h, ha3]
  have hbB : t⁻¹ * a * t ∈ B0 T L := by
    have := (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_B0 T L (T.inv_mem ht)) a).mp haB
    simpa using this
  have hbV₁ : ∀ v ∈ fsuUL T L I, (t⁻¹ * a * t) * v * (t⁻¹ * a * t)⁻¹ = v := by
    intro v hv
    have hv' : t * v * t⁻¹ ∈ CFSG.conjugate (fsuUL T L I) t⁻¹ := by
      rw [SecA.mem_conjugate_iff]
      simpa [mul_assoc] using hv
    have hc := Subgroup.mem_centralizer_iff.mp (hLV₁ hv') a haL
    calc (t⁻¹ * a * t) * v * (t⁻¹ * a * t)⁻¹ = t⁻¹ * (a * (t * v * t⁻¹)) * a⁻¹ * t := by group
      _ = t⁻¹ * ((t * v * t⁻¹) * a) * a⁻¹ * t := by rw [hc]
      _ = v := by group
  have hbV₂ : ¬ ∀ v ∈ CFSG.conjugate (fsuUL T L I) t,
      (t⁻¹ * a * t) * v * (t⁻¹ * a * t)⁻¹ = v := by
    intro h
    apply haV₁
    intro v hv
    have hv' : t⁻¹ * v * t ∈ CFSG.conjugate (fsuUL T L I) t := by
      rw [SecA.mem_conjugate_iff]
      simpa [mul_assoc] using hv
    have := h _ hv'
    calc a * v * a⁻¹ = t * ((t⁻¹ * a * t) * (t⁻¹ * v * t) * (t⁻¹ * a * t)⁻¹) * t⁻¹ := by group
      _ = v := by rw [this]; group
  exact ⟨t, ht, htn, a, haB, _, hbB, ha3, hb3, haV₂, haV₁, hbV₁, hbV₂⟩

omit [Finite G] in
theorem exists_pow_of_mem_closure {V : Subgroup G} {a b : G}
    (haN : a ∈ Subgroup.normalizer (V : Set G)) (hbV : ∀ v ∈ V, b * v * b⁻¹ = v) {y : G}
    (hy : y ∈ Subgroup.closure ({a, b} : Set G)) :
    ∃ k : ℤ, ∀ v ∈ V, y * v * y⁻¹ = a ^ k * v * (a ^ k)⁻¹ := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, fun v _ => by rw [zpow_one]⟩
    · exact ⟨0, fun v hv => by rw [hbV v hv, zpow_zero, one_mul, inv_one, mul_one]⟩
  | one => exact ⟨0, fun v _ => by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨k + m, fun v hv => ?_⟩
    have hv' : a ^ m * v * (a ^ m)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ haN m) v).mp hv
    calc x * y * v * (x * y)⁻¹ = x * (y * v * y⁻¹) * x⁻¹ := by group
      _ = x * (a ^ m * v * (a ^ m)⁻¹) * x⁻¹ := by rw [hm v hv]
      _ = a ^ k * (a ^ m * v * (a ^ m)⁻¹) * (a ^ k)⁻¹ := hk _ hv'
      _ = a ^ (k + m) * v * (a ^ (k + m))⁻¹ := by rw [zpow_add]; group
  | inv x _ hx =>
    obtain ⟨k, hk⟩ := hx
    refine ⟨-k, fun v hv => ?_⟩
    have hv' : a ^ (-k) * v * (a ^ (-k))⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ haN (-k)) v).mp hv
    have h := hk _ hv'
    have e : a ^ k * (a ^ (-k) * v * (a ^ (-k))⁻¹) * (a ^ k)⁻¹ = v := by
      rw [zpow_neg]; group
    rw [e] at h
    calc x⁻¹ * v * x⁻¹⁻¹ = x⁻¹ * (x * (a ^ (-k) * v * (a ^ (-k))⁻¹) * x⁻¹) * x := by
          rw [h]; group
      _ = a ^ (-k) * v * (a ^ (-k))⁻¹ := by group

theorem exists_E9 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1 : Case10_1_1One T L I n)
    (hn3 : 3 ∣ 2 ^ n - 1) :
    ∃ E : Subgroup G, E ≤ B0 T L ∧ Nat.card E = 9 ∧ ∀ y ∈ E, y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, ht, htn, a, haB, b, hbB, ha3, hb3, haV₂, haV₁, hbV₁, hbV₂⟩ :=
    exists_E9_aux h37 h38 hyp h1 hn3
  set Q := Subgroup.closure ({a, b} : Set G) with hQ
  have hQB : Q ≤ B0 T L := by
    rw [hQ, Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [haB, hbB]
  have hN₁ := B0_le_normalizer_fsuUL hyp
  have hN₂ := B0_le_normalizer_conjugate hyp ht
  set ψ : ↥Q →* MulAut ↥(CFSG.conjugate (fsuUL T L I) t) :=
    (conjAct (CFSG.conjugate (fsuUL T L I) t)).comp (Subgroup.inclusion (hQB.trans hN₂)) with hψ
  have haQ : a ∈ Q := Subgroup.subset_closure (by simp)
  have hbQ : b ∈ Q := Subgroup.subset_closure (by simp)
  have hak : (⟨a, haQ⟩ : ↥Q) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    ext v
    exact haV₂ v v.2
  have h3k : 3 ∣ Nat.card ψ.ker := by
    have h := Subgroup.orderOf_dvd_natCard ψ.ker hak
    rwa [Subgroup.orderOf_mk, ha3] at h
  have hψb : orderOf (ψ ⟨b, hbQ⟩) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
      have : (⟨b, hbQ⟩ : ↥Q) ^ 3 = 1 := Subtype.ext (by simpa using hb3')
      rw [this, map_one]
    · intro h
      apply hbV₂
      intro v hv
      have := congrArg (fun φ : MulAut ↥(CFSG.conjugate (fsuUL T L I) t) =>
        ((φ ⟨v, hv⟩ : ↥(CFSG.conjugate (fsuUL T L I) t)) : G)) h
      exact this
  have h3r : 3 ∣ Nat.card ψ.range := by
    rw [← hψb]
    exact Subgroup.orderOf_dvd_natCard _ ⟨_, rfl⟩
  have h9 : 3 ^ 2 ∣ Nat.card ↥Q := by
    rw [← Subgroup.card_mul_index ψ.ker, Subgroup.index_ker, pow_two]
    exact Nat.mul_dvd_mul h3k h3r
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  refine ⟨E'.map Q.subtype, (Subgroup.map_subtype_le E').trans hQB, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, hE']
    norm_num
  · rintro _ ⟨y, hy, rfl⟩
    have hyo : orderOf y ∣ 9 := by
      have := Subgroup.orderOf_dvd_natCard E' hy
      rwa [hE'] at this
    have hyB := hQB y.2
    obtain ⟨k, hk⟩ := exists_pow_of_mem_closure (hN₁ haB) hbV₁ y.2
    obtain ⟨m, hm⟩ := exists_pow_of_mem_closure (hN₂ hbB) haV₂
      (show (y : G) ∈ Subgroup.closure ({b, a} : Set G) by rw [Set.pair_comm]; exact y.2)
    have ha3' : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
    have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
    have hcube : ∀ {V : Subgroup G} {c : G} {j : ℤ}, c ^ 3 = 1 →
        c ∈ Subgroup.normalizer (V : Set G) →
        (∀ v ∈ V, (y : G) * v * (y : G)⁻¹ = c ^ j * v * (c ^ j)⁻¹) →
        ∀ v ∈ V, (y : G) ^ 3 * v * ((y : G) ^ 3)⁻¹ = v := by
      intro V c j hc3 hcN hy v hv
      generalize (y : G) = g at hy ⊢
      have hc' : ∀ w ∈ V, c ^ j * w * (c ^ j)⁻¹ ∈ V := fun w hw =>
        (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hcN j) w).mp hw
      have e1 := hy v hv
      have e2 := hy _ (hc' v hv)
      have e3 := hy _ (hc' _ (hc' v hv))
      have hcj : (c ^ j) ^ 3 = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hc3, one_zpow]
      calc g ^ 3 * v * (g ^ 3)⁻¹ = g * (g * (g * v * g⁻¹) * g⁻¹) * g⁻¹ := by
            rw [pow_three]; group
        _ = c ^ j * (c ^ j * (c ^ j * v * (c ^ j)⁻¹) * (c ^ j)⁻¹) * (c ^ j)⁻¹ := by
          rw [e1, e2, e3]
        _ = (c ^ j) ^ 3 * v * ((c ^ j) ^ 3)⁻¹ := by rw [pow_three]; group
        _ = v := by rw [hcj]; group
    have hodd : Odd (orderOf ((y : G) ^ 3)) := by
      refine Odd.of_dvd_nat (by decide : Odd 9) ((orderOf_pow_dvd _).trans ?_)
      rw [← Subgroup.orderOf_coe] at hyo
      exact hyo
    have hy3 := SecA.eq_one_of_forall_conj_eq h37 h38 hyp ht htn
      ((fsuL0 T L).pow_mem (oTwoUpper_le _ hyB).1 3) hodd (hcube ha3' (hN₁ haB) hk)
      (hcube hb3' (hN₂ hbB) hm)
    exact hy3

end C11AmS.K7

end CFSG.Quasithin.Vol2.Ch10.SecB
