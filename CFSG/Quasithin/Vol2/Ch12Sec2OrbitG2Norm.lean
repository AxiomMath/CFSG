module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2
public import CFSG.Quasithin.Vol2.Ch12Sec4Orbit

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H.Mathieu

section Norm

variable {K : Type} [Field K]

theorem zornNorm_add_add (a b c : quasithinZorn K) :
    zornNorm (a + b + c) = zornNorm (a + b) + zornNorm (a + c) + zornNorm (b + c) -
      zornNorm a - zornNorm b - zornNorm c := by
  simp only [zornNorm, Prod.fst_add, Prod.snd_add, Pi.add_apply, Fin.sum_univ_three]
  ring

@[expose] def zornUv (a : Fin 3 → K) : quasithinZorn K := (0, a, 0, 0)

theorem zornUv_add (a b : Fin 3 → K) : zornUv a + zornUv b = zornUv (a + b) := by
  apply zorn_ext <;> (try intro i) <;> simp [zornUv]

theorem zornUv_mem (a : Fin 3 → K) : (zornUv a).1 + (zornUv a).2.2.2 = 0 := by
  simp [zornUv]

theorem zornClsD_zornUv [DecidableEq K] {a : Fin 3 → K} (ha : a ≠ 0) : zornClsD (zornUv a) = 0 := by
  have h0 : zornUv a ≠ 0 := fun h => ha (congrArg (fun x => x.2.1) h)
  have h1 : zornUv a ≠ zornOne := fun h => by
    have := congrArg Prod.fst h
    simp [zornUv, zornOne] at this
  have hn : zornNorm (zornUv a) = 0 := by simp [zornNorm, zornUv]
  unfold zornClsD
  rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left hn]

end Norm

theorem g2WeylNormalizerOrbits : G2WeylNormalizerOrbits := by
  intro W _ _ H hH x hx w
  obtain ⟨K, _, _, hK2, hR0⟩ := hH
  classical
  obtain ⟨π, β, hR⟩ := (realizes_iff _ H ⊤ ⊥).1 hR0
  clear hR0
  let f : (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).Amb → ℕ :=
    fun y => zornClsD (Multiplicative.toAdd (α := quasithinZorn K) y)
  have hker : ∀ m ∈ (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec,
      ∀ k ∈ (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).ker, f (m * k) = f m := by
    intro m _ k hk
    rw [(Subgroup.mem_bot.1 hk : k = 1), mul_one]
  have hact : ∀ γ : (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).Gam,
      ∀ m ∈ (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec,
        f ((zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).act γ m) = f m := by
    intro γ m _
    exact zornClsD_g2 (derived_le _ γ.2) _
  have htrans : ∀ m ∈ (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec,
      ∀ m' ∈ (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec, f m = f m' →
        ∃ γ : (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).Gam,
          ∃ k ∈ (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).ker,
            (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).act γ m = m' * k := by
    intro m hm m' hm' h
    obtain ⟨γ, hγ, hγm⟩ := exists_g2Derived_of_cls hK2 hm hm' h
    refine ⟨⟨γ, hγ⟩, 1, Subgroup.one_mem _, ?_⟩
    rw [mul_one]
    change Multiplicative.ofAdd (γ (Multiplicative.toAdd (α := quasithinZorn K) m)) = m'
    rw [hγm]
    rfl
  choose r hr using fun v : W => QuotientGroup.mk_surjective (coordOf β v)
  let c : W → quasithinZorn K := fun v => Multiplicative.toAdd (α := quasithinZorn K) (r v).1
  have hc_mem : ∀ v, (c v).1 + (c v).2.2.2 = 0 := fun v => (r v).2
  have hmk_inj : ∀ a b : ↥(zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec,
      (QuotientGroup.mk a : ↥(zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec ⧸
        (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).ker.subgroupOf
          (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec) =
          QuotientGroup.mk b → a = b := by
    intro a b h
    have h1 : ((a⁻¹ * b : ↥(zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec) :
        (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).Amb) = 1 :=
      Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h))
    exact inv_mul_eq_one.1 (Subtype.ext h1)
  have hc_mul : ∀ v v', c (v * v') = c v + c v' := by
    intro v v'
    have h : r (v * v') = r v * r v' := by
      apply hmk_inj
      rw [hr, coordOf_mul, ← hr v, ← hr v', QuotientGroup.mk_mul]
    exact congrArg (fun y : ↥(zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec =>
      Multiplicative.toAdd (α := quasithinZorn K) y.1) h
  have hc_surj : ∀ m : quasithinZorn K, m.1 + m.2.2.2 = 0 → ∃ v, c v = m := by
    intro m hm
    obtain ⟨v, hv⟩ := coordOf_surjective hR (QuotientGroup.mk ⟨Multiplicative.ofAdd m, hm⟩)
    refine ⟨v, ?_⟩
    have := hmk_inj _ _ ((hr v).trans hv)
    exact congrArg (fun y : ↥(zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec =>
      Multiplicative.toAdd (α := quasithinZorn K) y.1) this
  have hc_inj : ∀ v v', c v = c v' → v = v' := by
    intro v v' h
    apply coordOf_injective hR
    rw [← hr, ← hr]
    congr 1
    exact Subtype.ext (Multiplicative.toAdd.injective h)
  have horb : ∀ v v' : W, (∃ h ∈ H, (h : MulAut W) v = v') ↔ zornClsD (c v) = zornClsD (c v') :=
    fun v v' => exists_eq_iff_of_classFn f hR hker hact htrans (hr v).symm (hr v').symm
  have hmapsto : ∀ y : MulAut W, (∀ h, h ∈ H ↔ y * h * y⁻¹ ∈ H) → ∀ v v' : W,
      zornClsD (c v) = zornClsD (c v') → zornClsD (c (y v)) = zornClsD (c (y v')) := by
    intro y hy v v' h
    obtain ⟨g, hg, rfl⟩ := (horb v v').2 h
    apply (horb _ _).1
    refine ⟨y * g * y⁻¹, (hy g).1 hg, ?_⟩
    simp
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_two hK2
  have hc1 : c 1 = 0 := by
    have h := hc_mul 1 1
    rw [mul_one] at h
    exact left_eq_add.1 h
  have hc_one_iff : ∀ v, c v = 0 ↔ v = 1 :=
    fun v => ⟨fun h => hc_inj _ _ (h.trans hc1.symm), fun h => by rw [h, hc1]⟩
  obtain ⟨z₁, hz₁⟩ := hc_surj zornOne (by rw [zornOne_tr, h2])
  have hcz_iff : ∀ v, c v = zornOne ↔ v = z₁ :=
    fun v => ⟨fun h => hc_inj _ _ (h.trans hz₁.symm), fun h => by rw [h, hz₁]⟩
  have hclass_two : ∀ m : quasithinZorn K, m.1 + m.2.2.2 = 0 → zornClsD m < 2 →
      ∃ m' : quasithinZorn K, m'.1 + m'.2.2.2 = 0 ∧ zornClsD m' = zornClsD m ∧ m' ≠ m := by
    intro m hm hlt
    have hcands : ∀ k : ℕ, k < 2 → ∃ p q : quasithinZorn K, p.1 + p.2.2.2 = 0 ∧
        q.1 + q.2.2.2 = 0 ∧ zornClsD p = k ∧ zornClsD q = k ∧ p ≠ q := by
      intro k hk
      interval_cases k
      · refine ⟨zornUv (Pi.single 0 1), zornUv (Pi.single 1 1), zornUv_mem _, zornUv_mem _,
          zornClsD_zornUv ?_, zornClsD_zornUv ?_, ?_⟩
        · exact Pi.single_ne_zero_iff.2 one_ne_zero
        · exact Pi.single_ne_zero_iff.2 one_ne_zero
        · intro h
          have := congrFun (congrArg (fun x => x.2.1) h) 0
          simp [zornUv] at this
      · refine ⟨(0, Pi.single 0 1, Pi.single 0 1, 0), (0, Pi.single 1 1, Pi.single 1 1, 0),
          by simp, by simp, ?_, ?_, ?_⟩
        · have h0 : ((0, Pi.single 0 1, Pi.single 0 1, 0) : quasithinZorn K) ≠ 0 := fun h => by
            have := congrFun (congrArg (fun x => x.2.1) h) 0
            simp at this
          have h1 : ((0, Pi.single 0 1, Pi.single 0 1, 0) : quasithinZorn K) ≠ zornOne :=
            fun h => by
              have := congrArg Prod.fst h
              simp [zornOne] at this
          have hn : zornNorm ((0, Pi.single 0 1, Pi.single 0 1, 0) : quasithinZorn K) ≠ 0 := by
            simp [zornNorm, Fin.sum_univ_three]
          unfold zornClsD
          rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right hn]
        · have h0 : ((0, Pi.single 1 1, Pi.single 1 1, 0) : quasithinZorn K) ≠ 0 := fun h => by
            have := congrFun (congrArg (fun x => x.2.1) h) 1
            simp at this
          have h1 : ((0, Pi.single 1 1, Pi.single 1 1, 0) : quasithinZorn K) ≠ zornOne :=
            fun h => by
              have := congrArg Prod.fst h
              simp [zornOne] at this
          have hn : zornNorm ((0, Pi.single 1 1, Pi.single 1 1, 0) : quasithinZorn K) ≠ 0 := by
            simp [zornNorm, Fin.sum_univ_three]
          unfold zornClsD
          rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right hn]
        · intro h
          have := congrFun (congrArg (fun x => x.2.1) h) 0
          simp at this
    obtain ⟨p, q, hp, hq, hpk, hqk, hpq⟩ := hcands (zornClsD m) hlt
    by_cases hpm : p = m
    · exact ⟨q, hq, hqk, fun h => hpq (hpm.trans h.symm)⟩
    · exact ⟨p, hp, hpk, hpm⟩
  have hfix_cls : ∀ v : W, (∀ g ∈ H, (g : MulAut W) v = v) → 2 ≤ zornClsD (c v) := by
    intro v hv
    by_contra hlt
    push Not at hlt
    obtain ⟨m', hm', hcls, hne⟩ := hclass_two (c v) (hc_mem v) hlt
    obtain ⟨v', rfl⟩ := hc_surj m' hm'
    obtain ⟨g, hg, hgv⟩ := (horb v v').2 hcls.symm
    rw [hv g hg] at hgv
    exact hne (by rw [hgv])
  have hcls_lt : ∀ v, zornClsD (c v) < 4 := by
    intro v
    unfold zornClsD
    split_ifs <;> norm_num
  have hcls2 : ∀ v, zornClsD (c v) = 2 ↔ v = 1 := by
    intro v
    rw [← hc_one_iff]
    unfold zornClsD
    constructor
    · intro h
      by_contra h0
      rw [ite_eq_right h0] at h
      split_ifs at h <;> omega
    · intro h
      rw [ite_eq_left h]
  have hcls3 : ∀ v, zornClsD (c v) = 3 ↔ v = z₁ := by
    intro v
    rw [← hcz_iff]
    unfold zornClsD
    constructor
    · intro h
      by_contra h1
      by_cases h0 : c v = 0
      · rw [ite_eq_left h0] at h
        omega
      · rw [ite_eq_right h0, ite_eq_right h1] at h
        split_ifs at h
        omega
    · intro h
      have h0 : c v ≠ 0 := by
        rw [h]
        intro h'
        have := congrArg Prod.fst h'
        simp [zornOne] at this
      rw [ite_eq_right h0, ite_eq_left h]
  have hyz : ∀ y : MulAut W, (∀ h, h ∈ H ↔ y * h * y⁻¹ ∈ H) → y z₁ = z₁ := by
    intro y hy
    have hzfix : ∀ g ∈ H, (g : MulAut W) z₁ = z₁ := by
      intro g hg
      have h := (horb z₁ _).1 ⟨g, hg, rfl⟩
      rw [(hcls3 z₁).2 rfl] at h
      exact ((hcls3 _).1 h.symm)
    have hyfix : ∀ g ∈ H, (g : MulAut W) (y z₁) = y z₁ := by
      intro g hg
      have hg' : y⁻¹ * g * y ∈ H := by
        have := (hy (y⁻¹ * g * y)).2
        simpa [mul_assoc] using this (by simpa [mul_assoc] using hg)
      have := hzfix _ hg'
      simp only [MulAut.mul_apply] at this
      calc (g : MulAut W) (y z₁) = y (y⁻¹ (g (y z₁))) := by simp
        _ = y z₁ := by rw [this]
    have h := hfix_cls _ hyfix
    have h4 := hcls_lt (y z₁)
    have hne1 : y z₁ ≠ 1 := by
      intro h1
      have : z₁ = 1 := y.injective (h1.trans (map_one y).symm)
      rw [this, hc1] at hz₁
      have := congrArg Prod.fst hz₁
      simp [zornOne] at this
    have h3 : zornClsD (c (y z₁)) ≠ 2 := fun h' => hne1 ((hcls2 _).1 h')
    exact (hcls3 _).1 (by omega)
  have hy0 : ∀ y : MulAut W, (∀ h, h ∈ H ↔ y * h * y⁻¹ ∈ H) → ∀ v : W,
      zornClsD (c v) = 0 → zornClsD (c (y v)) = 0 := by
    intro y hy v hv
    by_contra hne
    have hv1 : v ≠ 1 := fun h => by rw [(hcls2 v).2 h] at hv; omega
    have hvz : v ≠ z₁ := fun h => by rw [(hcls3 v).2 h] at hv; omega
    have hyv1 : y v ≠ 1 := fun h => hv1 (y.injective (h.trans (map_one y).symm))
    have hyvz : y v ≠ z₁ := fun h => hvz (y.injective (h.trans (hyz y hy).symm))
    have hyv : zornClsD (c (y v)) = 1 := by
      have h4 := hcls_lt (y v)
      have h2' : zornClsD (c (y v)) ≠ 2 := fun h => hyv1 ((hcls2 _).1 h)
      have h3' : zornClsD (c (y v)) ≠ 3 := fun h => hyvz ((hcls3 _).1 h)
      omega
    obtain ⟨u0, hu0⟩ := hc_surj (zornUv (Pi.single 0 1)) (zornUv_mem _)
    obtain ⟨u1, hu1⟩ := hc_surj (zornUv (Pi.single 1 1)) (zornUv_mem _)
    obtain ⟨u2, hu2⟩ := hc_surj (zornUv (Pi.single 2 1)) (zornUv_mem _)
    have hnorm1 : ∀ u : W, (∃ a : Fin 3 → K, a ≠ 0 ∧ c u = zornUv a) →
        zornNorm (c (y u)) = 1 := by
      rintro u ⟨a, ha, hua⟩
      have h1 : zornClsD (c (y u)) = 1 := by
        rw [← hyv]
        apply hmapsto y hy
        rw [hua, zornClsD_zornUv ha, hv]
      have h0 : c (y u) ≠ 0 := fun h => by
        unfold zornClsD at h1
        rw [ite_eq_left h] at h1
        omega
      have h1' : c (y u) ≠ zornOne := fun h => by
        unfold zornClsD at h1
        rw [ite_eq_right h0, ite_eq_left h] at h1
        omega
      unfold zornClsD at h1
      rw [ite_eq_right h0, ite_eq_right h1'] at h1
      have hn : zornNorm (c (y u)) ≠ 0 := fun h => by rw [ite_eq_left h] at h1; omega
      rcases eq_zero_or_one_of_card_two hK2 (zornNorm (c (y u))) with h | h
      · exact absurd h hn
      · exact h
    have hcu : ∀ (a b : Fin 3 → K) (u u' : W), c u = zornUv a → c u' = zornUv b →
        c (u * u') = zornUv (a + b) := by
      intro a b u u' hu hu'
      rw [hc_mul, hu, hu', zornUv_add]
    have hne0 : ∀ a : Fin 3 → K, a 0 ≠ 0 ∨ a 1 ≠ 0 → a ≠ 0 := by
      rintro a (h | h) rfl <;> exact h rfl
    have n0 := hnorm1 u0 ⟨_, Pi.single_ne_zero_iff.2 one_ne_zero, hu0⟩
    have n1 := hnorm1 u1 ⟨_, Pi.single_ne_zero_iff.2 one_ne_zero, hu1⟩
    have n2 := hnorm1 u2 ⟨_, Pi.single_ne_zero_iff.2 one_ne_zero, hu2⟩
    have n01 := hnorm1 (u0 * u1) ⟨_, hne0 _ (Or.inl (by simp)), hcu _ _ u0 u1 hu0 hu1⟩
    have n02 := hnorm1 (u0 * u2) ⟨_, hne0 _ (Or.inl (by simp)), hcu _ _ u0 u2 hu0 hu2⟩
    have n12 := hnorm1 (u1 * u2) ⟨_, hne0 _ (Or.inr (by simp)), hcu _ _ u1 u2 hu1 hu2⟩
    have n012 := hnorm1 (u0 * u1 * u2) ⟨_, hne0 _ (Or.inl (by simp)),
      hcu _ _ (u0 * u1) u2 (hcu _ _ u0 u1 hu0 hu1) hu2⟩
    have k01 : c (y (u0 * u1)) = c (y u0) + c (y u1) := by rw [map_mul, hc_mul]
    have k02 : c (y (u0 * u2)) = c (y u0) + c (y u2) := by rw [map_mul, hc_mul]
    have k12 : c (y (u1 * u2)) = c (y u1) + c (y u2) := by rw [map_mul, hc_mul]
    have k012 : c (y (u0 * u1 * u2)) = c (y u0) + c (y u1) + c (y u2) := by
      rw [map_mul, map_mul, hc_mul, hc_mul]
    have key := zornNorm_add_add (c (y u0)) (c (y u1)) (c (y u2))
    rw [← k012, ← k01, ← k02, ← k12, n012, n01, n02, n12, n0, n1, n2] at key
    have h3 : (1 : K) = 0 := by linear_combination key
    exact one_ne_zero h3
  have hxinv : ∀ h, h ∈ H ↔ x⁻¹ * h * x⁻¹⁻¹ ∈ H := by
    intro h
    constructor
    · intro hh
      have := (hx (x⁻¹ * h * x)).2 (by simpa [mul_assoc] using hh)
      simpa [mul_assoc] using this
    · intro hh
      have := (hx (x⁻¹ * h * x⁻¹⁻¹)).1 hh
      simpa [mul_assoc] using this
  apply (horb w (x w)).2
  by_cases h0 : zornClsD (c w) = 0
  · rw [h0, hy0 x hx w h0]
  by_cases h1 : zornClsD (c w) = 1
  · have hxw : zornClsD (c (x w)) = 1 := by
      by_contra hne
      have hw1 : w ≠ 1 := fun h => by rw [(hcls2 w).2 h] at h1; omega
      have hwz : w ≠ z₁ := fun h => by rw [(hcls3 w).2 h] at h1; omega
      have hxw1 : x w ≠ 1 := fun h => hw1 (x.injective (h.trans (map_one x).symm))
      have hxwz : x w ≠ z₁ := fun h => hwz (x.injective (h.trans (hyz x hx).symm))
      have h4 := hcls_lt (x w)
      have h2' : zornClsD (c (x w)) ≠ 2 := fun h => hxw1 ((hcls2 _).1 h)
      have h3' : zornClsD (c (x w)) ≠ 3 := fun h => hxwz ((hcls3 _).1 h)
      have hxw0 : zornClsD (c (x w)) = 0 := by omega
      have := hy0 x⁻¹ hxinv (x w) hxw0
      rw [MulAut.inv_apply_self] at this
      omega
    rw [h1, hxw]
  by_cases h2 : zornClsD (c w) = 2
  · rw [(hcls2 w).1 h2, map_one]
  have h3 : zornClsD (c w) = 3 := by
    have := hcls_lt w
    omega
  rw [(hcls3 w).1 h3, hyz x hx]

end CFSG.Quasithin.H13.Orbit
