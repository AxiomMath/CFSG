module

public import CFSG.Quasithin.Recognition.J2RecFive
public import CFSG.Quasithin.Recognition.J2RecGlobal
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.Quasithin.Recognition.J2RecEndgameProof

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.LieType.BorelTits J2Cz J2Cz.QM

theorem J2Cz.eq_of_comm_pa_pc : ∀ σ : Perm (Fin 5), σ * pa = pa * σ → σ * pc = pc * σ →
    σ = 1 ∨ σ = pa ∨ σ = pc ∨ σ = pa * pc := by
  decide +kernel

@[expose] def J2A5Five.powSub {G : Type} [Group G] (f : G) :
    Subgroup ↥(Subgroup.centralizer ({f} : Set G)) :=
  Subgroup.zpowers ⟨f, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

instance J2A5Five.powSub_normal {G : Type} [Group G] (f : G) : (J2A5Five.powSub f).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hg : g * ⟨f, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ =
      ⟨f, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ * g :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  rw [(Commute.zpow_right hg k).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers _ k

theorem J2A5Five.mem_powSub_iff {G : Type} [Group G] {f : G}
    {g : ↥(Subgroup.centralizer ({f} : Set G))} :
    g ∈ J2A5Five.powSub f ↔ (g : G) ∈ Subgroup.zpowers f := by
  rw [J2A5Five.powSub, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk]; rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by rw [← hk]; rfl)⟩

namespace J2A5Config

variable {G : Type} [Group G] [Finite G] {z : G} {A R : Subgroup G} {y : G} (c : J2A5Config z A R y)
include c

theorem not_mem_zpowers {f : G} (hf : J2A5Five A z f) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    r ∉ Subgroup.zpowers f := fun h1 => by
  obtain ⟨i, hi⟩ := J2A5Five.exists_pow_eq h1
  apply hr1
  rw [← hi]
  refine J2A5Five.pow_eq_one_of_two_pow_of_five (hf.pow_pow_five i) (k := 1) ?_
  rw [hi, pow_one, pow_two]
  exact c.mul_self r hr

theorem nonempty_mulEquiv_quot (h : IsTypeH2 G z) (hcount : involutionClassCount G = 2) {f : G}
    (hf : J2A5Five A z f) :
    Nonempty (↥(Subgroup.centralizer ({f} : Set G)) ⧸ J2A5Five.powSub f ≃*
      alternatingGroup (Fin 5)) := by
  set Cf := Subgroup.centralizer ({f} : Set G) with hCf
  set N := J2A5Five.powSub f with hN
  set q : ↥Cf →* ↥Cf ⧸ N := QuotientGroup.mk' N with hq
  obtain ⟨t, s, ht, hs, ht1, hs1, hst⟩ := c.exists_two
  have hRCf := c.R_le_centralizer_f hf
  set tC : ↥Cf := ⟨t, hRCf ht⟩ with htC
  set sC : ↥Cf := ⟨s, hRCf hs⟩ with hsC
  have hqeq : ∀ a b : ↥Cf, q a = q b ↔ ((a : G)⁻¹ * b) ∈ Subgroup.zpowers f := fun a b => by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      J2A5Five.mem_powSub_iff]
    rfl
  have hq1 : ∀ a : ↥Cf, q a = 1 ↔ (a : G) ∈ Subgroup.zpowers f := fun a => by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, J2A5Five.mem_powSub_iff]
  have hRq : ∀ r (hr : r ∈ R), r ≠ 1 → q ⟨r, hRCf hr⟩ ≠ 1 := fun r hr hr1 h1 =>
    c.not_mem_zpowers hf hr hr1 ((hq1 _).mp h1)
  refine ⟨Classical.choice (nonempty_mulEquiv_alt5_of_centralizer (z := q tC) (s := q sC) ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_)⟩
  · rw [← map_mul, show tC * tC = 1 from Subtype.ext (c.mul_self t ht), map_one]
  · exact hRq t ht ht1
  · rw [← map_mul, show sC * sC = 1 from Subtype.ext (c.mul_self s hs), map_one]
  · exact hRq s hs hs1
  · intro h1
    rw [hqeq] at h1
    have h2 : s⁻¹ * t ≠ 1 := fun h3 => hst (by
      calc s = s * (s⁻¹ * t) := by rw [h3, mul_one]
        _ = t := by group)
    exact c.not_mem_zpowers hf (R.mul_mem (R.inv_mem hs) ht) h2 h1
  · rw [← map_mul, ← map_mul, show tC * sC = sC * tC from Subtype.ext (c.comm_R ht hs)]
  ·
    intro gb hgb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gb
    rw [← map_mul, ← map_mul] at hgb
    have h1 := (hqeq _ _).mp hgb
    obtain ⟨i, hi⟩ := J2A5Five.exists_pow_eq h1
    have hti : (g : G)⁻¹ * t * g = t * f ^ i := by
      have e1 : ((g * tC : ↥Cf) : G)⁻¹ * (tC * g : ↥Cf) = t * ((g : G)⁻¹ * t * g) := by
        simp only [Subgroup.coe_mul, htC]
        rw [mul_inv_rev, show t⁻¹ = t from inv_eq_of_mul_eq_one_right (c.mul_self t ht)]
        group
      rw [hi, e1, ← mul_assoc, c.mul_self t ht, one_mul]
    have hfi : f ^ i = 1 := by
      refine J2A5Five.pow_eq_one_of_two_pow_of_five (hf.pow_pow_five i) (k := 1) ?_
      rw [pow_one, pow_two]
      have h2 : ((g : G)⁻¹ * t * g) * ((g : G)⁻¹ * t * g) = 1 := by
        calc ((g : G)⁻¹ * t * g) * ((g : G)⁻¹ * t * g) = (g : G)⁻¹ * (t * t) * g := by group
          _ = 1 := by rw [c.mul_self t ht]; group
      rw [hti] at h2
      have h3 : t * f ^ i * (t * f ^ i) = f ^ i * f ^ i := by
        rw [mul_assoc t, ← mul_assoc (f ^ i), (Commute.pow_right (c.comm_f hf ht) i).symm.eq]
        rw [← mul_assoc, ← mul_assoc, c.mul_self t ht, one_mul]
      rw [← h3]
      exact h2
    rw [hfi, mul_one] at hti
    have hgt : (g : G) ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g : G) * t = (g : G) * ((g : G)⁻¹ * t * g) := by rw [hti]
        _ = t * g := by group
    obtain ⟨r, hr, j, hrj⟩ := c.mem_R_mul_pow h hcount hf ht ht1 hgt g.2
    have hqg : q g = q ⟨r, hRCf hr⟩ := by
      rw [hqeq]
      rw [hrj]
      show (r * f ^ j)⁻¹ * r ∈ Subgroup.zpowers f
      rw [show (r * f ^ j)⁻¹ * r = (f ^ j)⁻¹ by group]
      exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ j)
    rw [hqg]
    rcases c.mem_four ht hs ht1 hs1 hst hr with rfl | rfl | rfl | rfl
    · left
      exact (map_one q).symm ▸ congrArg q (Subtype.ext rfl)
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right
      rw [← map_mul]
      rfl
  ·
    intro ub hub2 hub1
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N ub
    rw [← map_mul, hq1] at hub2
    obtain ⟨k, hk⟩ := J2A5Five.exists_pow_eq hub2
    set u' : ↥Cf := u ^ 5 with hu'
    have hu'2 : (u' : G) * u' = 1 := by
      rw [hu', Subgroup.coe_pow, ← pow_add,
        show 5 + 5 = 2 * 5 by norm_num, pow_mul, pow_two, ← Subgroup.coe_mul, ← hk,
        hf.pow_pow_five]
    have hqu' : q u' = q u := by
      have h2 : (q u) ^ 2 = 1 := by
        rw [pow_two, ← map_mul]
        exact (hq1 _).mpr hub2
      rw [hu', map_pow, show (5 : ℕ) = 2 * 2 + 1 by norm_num, pow_succ, pow_mul, h2, one_pow,
        one_mul]
    have hu'1 : (u' : G) ≠ 1 := fun h1 => hub1 (by
      rw [← hqu', (hq1 _).mpr (by rw [h1]; exact Subgroup.one_mem _)])
    obtain ⟨g, hgf, hg⟩ := c.exists_conj_eq_of_mul_self h hcount hf ht ht1 u'.2 hu'2 hu'1
    refine ⟨q ⟨g, hgf⟩, ?_⟩
    rw [← hqu', ← map_inv, ← map_mul, ← map_mul]
    exact congrArg q (Subtype.ext hg)
  ·
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hN5 : Nat.card N = 5 := by
      rw [hN, J2A5Five.powSub, Nat.card_zpowers, Subgroup.orderOf_mk, hf.orderOf_eq]
    rw [hN5] at h1
    have h2 := c.dvd_card_centralizer_five h hcount hf
    have h3 : 5 * 5 ∣ Nat.card (↥Cf ⧸ N) * 5 := by rw [← h1]; exact h2
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3

@[expose] noncomputable def conjZ (z f : G) (hzf : z * f * z = f⁻¹) (hzz : z * z = 1) :
    ↥(Subgroup.centralizer ({f} : Set G)) →* ↥(Subgroup.centralizer ({f} : Set G)) where
  toFun g := ⟨z * g * z⁻¹, by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    have hgf : (g : G) * f⁻¹ = f⁻¹ * g :=
      (Commute.inv_right (Subgroup.mem_centralizer_singleton_iff.mp g.2)).eq
    have hzf' : z⁻¹ * f * z = f⁻¹ := by rw [hzi]; exact hzf
    have hzf'' : z * f⁻¹ * z⁻¹ = f := by
      have h1 : z * f * z⁻¹ = f⁻¹ := by rw [hzi]; exact hzf
      calc z * f⁻¹ * z⁻¹ = (z * f * z⁻¹)⁻¹ := by group
        _ = f := by rw [h1, inv_inv]
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc z * g * z⁻¹ * f = z * g * (z⁻¹ * f * z) * z⁻¹ := by group
      _ = z * ((g : G) * f⁻¹) * z⁻¹ := by rw [hzf']; group
      _ = z * (f⁻¹ * g) * z⁻¹ := by rw [hgf]
      _ = (z * f⁻¹ * z⁻¹) * (z * g * z⁻¹) := by group
      _ = f * (z * g * z⁻¹) := by rw [hzf'']⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit c [Finite G] in
theorem conjZ_apply {z f : G} (hzf : z * f * z = f⁻¹) (hzz : z * z = 1)
    (g : ↥(Subgroup.centralizer ({f} : Set G))) :
    ((conjZ z f hzf hzz g : ↥(Subgroup.centralizer ({f} : Set G))) : G) = z * g * z⁻¹ := rfl

theorem exists_conj_eq_mul_pow (h : IsTypeH2 G z) (hcount : involutionClassCount G = 2) {f : G}
    (hf : J2A5Five A z f) {g : G} (hg : g ∈ Subgroup.centralizer ({f} : Set G)) :
    ∃ k : ℕ, z * g * z⁻¹ = g * f ^ k := by
  have hzz : z * z = 1 := by rw [← pow_two]; exact h.sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  set Cf := Subgroup.centralizer ({f} : Set G) with hCf
  set N := J2A5Five.powSub f with hN
  set q : ↥Cf →* ↥Cf ⧸ N := QuotientGroup.mk' N with hq
  set φ₀ := conjZ z f hf.inv hzz with hφ₀
  have hφN : N ≤ N.comap φ₀ := by
    intro n hn
    rw [Subgroup.mem_comap, J2A5Five.mem_powSub_iff]
    rw [J2A5Five.mem_powSub_iff] at hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [conjZ_apply, ← hk, ← conj_zpow, hzi, hf.inv, inv_zpow']
    exact Subgroup.zpow_mem_zpowers _ _
  set φ : ↥Cf ⧸ N →* ↥Cf ⧸ N := QuotientGroup.map N N φ₀ hφN with hφ
  have hφq : ∀ a, φ (q a) = q (φ₀ a) := fun a => QuotientGroup.map_mk N N φ₀ hφN a
  have hφφ : ∀ x, φ (φ x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [hφq, hφq]
    congr 1
    apply Subtype.ext
    rw [conjZ_apply, conjZ_apply]
    calc z * (z * (a : G) * z⁻¹) * z⁻¹ = (z * z) * a * (z * z)⁻¹ := by group
      _ = a := by rw [hzz]; group
  obtain ⟨e⟩ := c.nonempty_mulEquiv_quot h hcount hf
  set ψ : MulAut (alternatingGroup (Fin 5)) :=
    { toFun := fun a => e (φ (e.symm a))
      invFun := fun a => e (φ (e.symm a))
      left_inv := fun a => by simp [hφφ]
      right_inv := fun a => by simp [hφφ]
      map_mul' := fun a b => by simp } with hψ
  obtain ⟨σ, hσ⟩ := SteinbergCB.conjPerm_surjective (n := 5) (Or.inl rfl) ψ
  have hσapp : ∀ a : alternatingGroup (Fin 5),
      ((e (φ (e.symm a)) : alternatingGroup (Fin 5)) : Perm (Fin 5)) = σ * a * σ⁻¹ := by
    intro a
    rw [← SteinbergCB.conjPerm_apply, hσ]
    rfl
  have hfix : ∀ x, φ x = x → σ * (e x : Perm (Fin 5)) = (e x : Perm (Fin 5)) * σ := by
    intro x hx
    have h1 := hσapp (e x)
    rw [MulEquiv.symm_apply_apply, hx] at h1
    calc σ * (e x : Perm (Fin 5)) = σ * (e x : Perm (Fin 5)) * σ⁻¹ * σ := by group
      _ = (e x : Perm (Fin 5)) * σ := by rw [← h1]
  obtain ⟨t, s, ht, hs, ht1, hs1, hst⟩ := c.exists_two
  obtain ⟨w, hwA, hwN, -, hwmove⟩ := c.exists_odd_mover h hcount hf
  have hRCf := c.R_le_centralizer_f hf
  have hwCf : w ∈ Cf := Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp hwA) f hf.mem).symm
  have hzcomm : ∀ {u : G}, u ∈ Subgroup.centralizer (A : Set G) → z * u * z⁻¹ = u := fun hu => by
    rw [(Subgroup.mem_centralizer_iff.mp hu) z c.z_mem, mul_inv_cancel_right]
  have hφfix : ∀ {u : G} (hu : u ∈ Subgroup.centralizer (A : Set G)) (huf : u ∈ Cf),
      φ (q ⟨u, huf⟩) = q ⟨u, huf⟩ := fun hu huf => by
    rw [hφq]
    exact congrArg q (Subtype.ext (by rw [conjZ_apply]; exact hzcomm hu))
  set α : Perm (Fin 5) := (e (q ⟨t, hRCf ht⟩) : Perm (Fin 5)) with hα
  set β : Perm (Fin 5) := (e (q ⟨s, hRCf hs⟩) : Perm (Fin 5)) with hβ
  set γ : Perm (Fin 5) := (e (q ⟨w, hwCf⟩) : Perm (Fin 5)) with hγ
  have hσα : σ * α = α * σ := hfix _ (hφfix (c.le_centralizer ht) _)
  have hσβ : σ * β = β * σ := hfix _ (hφfix (c.le_centralizer hs) _)
  have hσγ : σ * γ = γ * σ := hfix _ (hφfix hwA _)
  have hqinj : ∀ {a b : ↥Cf}, q a = q b → ((a : G)⁻¹ * b) ∈ Subgroup.zpowers f := fun h1 => by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      J2A5Five.mem_powSub_iff] at h1
    exact h1
  have heinj : ∀ {a b : ↥Cf}, (e (q a) : Perm (Fin 5)) = e (q b) →
      ((a : G)⁻¹ * b) ∈ Subgroup.zpowers f := fun h1 =>
    hqinj (e.injective (Subtype.ext h1))
  have hRne : ∀ {r r' : G} (hr : r ∈ R) (hr' : r' ∈ R), r ≠ r' →
      (e (q ⟨r, hRCf hr⟩) : Perm (Fin 5)) ≠ e (q ⟨r', hRCf hr'⟩) := fun {r r'} hr hr' hne h1 => by
    have h2 := heinj h1
    have h3 : r⁻¹ * r' ≠ 1 := fun h4 => hne (by
      calc r = r * (r⁻¹ * r') := by rw [h4, mul_one]
        _ = r' := by group)
    exact c.not_mem_zpowers hf (R.mul_mem (R.inv_mem hr) hr') h3 h2
  have hemul : ∀ (a b : ↥Cf), (e (q (a * b)) : Perm (Fin 5)) = e (q a) * e (q b) := fun a b => by
    rw [map_mul, map_mul]
    rfl
  have hα2 : α * α = 1 := by
    rw [hα, ← hemul, show (⟨t, hRCf ht⟩ * ⟨t, hRCf ht⟩ : ↥Cf) = 1 from
      Subtype.ext (c.mul_self t ht), map_one, map_one]
    rfl
  have hα1 : α ≠ 1 := by
    have h1 := hRne ht (R.one_mem) ht1
    rwa [show (⟨1, hRCf R.one_mem⟩ : ↥Cf) = 1 from rfl, map_one, map_one] at h1
  have hsign : ∀ x, Perm.sign (e x : Perm (Fin 5)) = 1 := fun x =>
    Perm.mem_alternatingGroup.mp (e x).2
  have hγmove : ∀ {r : G} (hr : r ∈ R), r ≠ 1 →
      γ * (e (q ⟨r, hRCf hr⟩) : Perm (Fin 5)) ≠ e (q ⟨r, hRCf hr⟩) * γ := by
    intro r hr hr1 h1
    have hwr : w * r * w⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hwN r).mp hr
    have h2 : (e (q ⟨w * r * w⁻¹, hRCf hwr⟩) : Perm (Fin 5)) = e (q ⟨r, hRCf hr⟩) := by
      rw [show (⟨w * r * w⁻¹, hRCf hwr⟩ : ↥Cf) = ⟨w, hwCf⟩ * ⟨r, hRCf hr⟩ * ⟨w, hwCf⟩⁻¹ from rfl,
        hemul, hemul, map_inv, map_inv, Subgroup.coe_inv, ← hγ, h1]
      group
    exact hwmove r hr hr1 (by
      by_contra hne
      exact hRne hwr hr hne h2)
  obtain ⟨π, hπ, hπα⟩ := exists_conj_pa α (hsign _) hα2 hα1
  set β' := π * β * π⁻¹ with hβ'
  have hαβ : α * β = β * α := by
    rw [hα, hβ, ← hemul, ← hemul, show (⟨t, hRCf ht⟩ * ⟨s, hRCf hs⟩ : ↥Cf) =
      ⟨s, hRCf hs⟩ * ⟨t, hRCf ht⟩ from Subtype.ext (c.comm_R ht hs)]
  have hβ'pa : β' * pa = pa * β' := by
    rw [hβ', ← hπα]
    calc π * β * π⁻¹ * (π * α * π⁻¹) = π * (β * α) * π⁻¹ := by group
      _ = π * (α * β) * π⁻¹ := by rw [hαβ]
      _ = π * α * π⁻¹ * (π * β * π⁻¹) := by group
  have hβ'sign : Perm.sign β' = 1 := by
    rw [hβ', map_mul, map_mul, map_inv, hπ, hsign]
    simp
  have hβ'1 : β' ≠ 1 := fun h1 => by
    have h2 : β = 1 := by
      calc β = π⁻¹ * β' * π := by rw [hβ']; group
        _ = 1 := by rw [h1]; group
    have h3 := hRne hs (R.one_mem) hs1
    rw [show (⟨1, hRCf R.one_mem⟩ : ↥Cf) = 1 from rfl, map_one, map_one] at h3
    exact h3 h2
  have hβ'a : β' ≠ pa := fun h1 => by
    have h2 : β = α := by
      calc β = π⁻¹ * β' * π := by rw [hβ']; group
        _ = π⁻¹ * (π * α * π⁻¹) * π := by rw [h1, hπα]
        _ = α := by group
    exact hRne hs ht hst h2
  have hβ'c : β' = pc ∨ β' = pa * pc := by
    rcases eq_of_comm_pa β' hβ'pa hβ'sign with h1 | h1 | h1 | h1
    · exact absurd h1 hβ'1
    · exact absurd h1 hβ'a
    · exact Or.inl h1
    · exact Or.inr h1
  set σ' := π * σ * π⁻¹ with hσ'
  set γ' := π * γ * π⁻¹ with hγ'
  have hconj_comm : ∀ {a b : Perm (Fin 5)}, a * b = b * a →
      (π * a * π⁻¹) * (π * b * π⁻¹) = (π * b * π⁻¹) * (π * a * π⁻¹) := fun {a b} h1 => by
    calc (π * a * π⁻¹) * (π * b * π⁻¹) = π * (a * b) * π⁻¹ := by group
      _ = π * (b * a) * π⁻¹ := by rw [h1]
      _ = (π * b * π⁻¹) * (π * a * π⁻¹) := by group
  have hσ'pa : σ' * pa = pa * σ' := by rw [← hπα]; exact hconj_comm hσα
  have hσ'β' : σ' * β' = β' * σ' := hconj_comm hσβ
  have hσ'γ' : σ' * γ' = γ' * σ' := hconj_comm hσγ
  have hσ'pc : σ' * pc = pc * σ' := by
    rcases hβ'c with h1 | h1
    · rw [← h1]; exact hσ'β'
    · have h2 : pc = pa * β' := by rw [h1, ← mul_assoc, pa_sq, one_mul]
      rw [h2]
      calc σ' * (pa * β') = (σ' * pa) * β' := by group
        _ = pa * (σ' * β') := by rw [hσ'pa]; group
        _ = pa * β' * σ' := by rw [hσ'β']; group
  have hγ'move : ∀ {r : G} (hr : r ∈ R), r ≠ 1 →
      γ' * (π * (e (q ⟨r, hRCf hr⟩) : Perm (Fin 5)) * π⁻¹) ≠
        (π * (e (q ⟨r, hRCf hr⟩) : Perm (Fin 5)) * π⁻¹) * γ' := fun hr hr1 h1 => by
    apply hγmove hr hr1
    calc γ * (e (q ⟨_, hRCf hr⟩) : Perm (Fin 5)) =
          π⁻¹ * (γ' * (π * (e (q ⟨_, hRCf hr⟩) : Perm (Fin 5)) * π⁻¹)) * π := by
          rw [hγ']; group
      _ = π⁻¹ * ((π * (e (q ⟨_, hRCf hr⟩) : Perm (Fin 5)) * π⁻¹) * γ') * π := by rw [h1]
      _ = (e (q ⟨_, hRCf hr⟩) : Perm (Fin 5)) * γ := by rw [hγ']; group
  have hts1 : t * s ≠ 1 := fun h1 => hst (by
    calc s = t * (t * s) := by rw [← mul_assoc, c.mul_self t ht, one_mul]
      _ = t := by rw [h1, mul_one])
  have hpaβ' : π * (e (q ⟨t * s, hRCf (R.mul_mem ht hs)⟩) : Perm (Fin 5)) * π⁻¹ = pa * β' := by
    rw [show (⟨t * s, hRCf (R.mul_mem ht hs)⟩ : ↥Cf) = ⟨t, hRCf ht⟩ * ⟨s, hRCf hs⟩ from rfl,
      hemul, ← hα, ← hβ, ← hπα, hβ']
    group
  have hpapapc : pa * (pa * pc) = pc := by rw [← mul_assoc, pa_sq, one_mul]
  have hσ'1 : σ' = 1 := by
    rcases eq_of_comm_pa_pc σ' hσ'pa hσ'pc with h1 | h1 | h1 | h1
    · exact h1
    · exfalso
      apply hγ'move ht ht1
      rw [← hα, hπα, ← h1]
      exact hσ'γ'.symm
    · exfalso
      rcases hβ'c with h2 | h2
      · apply hγ'move hs hs1
        rw [← hβ, ← hβ', h2, ← h1]
        exact hσ'γ'.symm
      · apply hγ'move (R.mul_mem ht hs) hts1
        rw [hpaβ', h2, hpapapc, ← h1]
        exact hσ'γ'.symm
    · exfalso
      rcases hβ'c with h2 | h2
      · apply hγ'move (R.mul_mem ht hs) hts1
        rw [hpaβ', h2, ← h1]
        exact hσ'γ'.symm
      · apply hγ'move hs hs1
        rw [← hβ, ← hβ', h2, ← h1]
        exact hσ'γ'.symm
  have hσ1 : σ = 1 := by
    calc σ = π⁻¹ * σ' * π := by rw [hσ']; group
      _ = 1 := by rw [hσ'1]; group
  have hφid : ∀ x, φ x = x := by
    intro x
    apply e.injective
    apply Subtype.ext
    have h1 := hσapp (e x)
    rw [MulEquiv.symm_apply_apply, hσ1, one_mul, inv_one, mul_one] at h1
    exact h1
  have h1 := hφid (q ⟨g, hg⟩)
  rw [hφq] at h1
  have h2 := hqinj h1.symm
  rw [conjZ_apply] at h2
  obtain ⟨k, hk⟩ := J2A5Five.exists_pow_eq h2
  refine ⟨k, ?_⟩
  rw [hk]
  group

theorem exists_complement_five_dvd (h : IsTypeH2 G z) (hcount : involutionClassCount G = 2) :
    ∃ L : Subgroup G, L ≤ Subgroup.centralizer ({z} : Set G) ∧
      L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) = ⊥ ∧ Nat.card L = 60 ∧
      5 ∣ Nat.card (Subgroup.centralizer (L : Set G)) := by
  obtain ⟨f, hf⟩ := c.exists_five h
  have hzz : z * z = 1 := by rw [← pow_two]; exact h.sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  set Cf := Subgroup.centralizer ({f} : Set G) with hCf
  set N := J2A5Five.powSub f with hN
  set q : ↥Cf →* ↥Cf ⧸ N := QuotientGroup.mk' N with hq
  set L := Subgroup.centralizer ({z} : Set G) ⊓ Cf with hL
  obtain ⟨e⟩ := c.nonempty_mulEquiv_quot h hcount hf
  have hqeq : ∀ a b : ↥Cf, q a = q b ↔ ((a : G)⁻¹ * b) ∈ Subgroup.zpowers f := fun a b => by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      J2A5Five.mem_powSub_iff]
    rfl
  have hzf : ∀ k : ℕ, z * f ^ k * z⁻¹ = (f ^ k)⁻¹ := fun k => by
    rw [← conj_pow, hzi, hf.inv, inv_pow]
  set lam : ↥L → ↥Cf ⧸ N := fun l => q ⟨l, (Subgroup.mem_inf.mp l.2).2⟩ with hlam
  have hlaminj : Function.Injective lam := by
    intro l l' h1
    have h2 : ((l : G)⁻¹ * l') ∈ Subgroup.zpowers f := by
      have h3 : q ⟨(l : G), (Subgroup.mem_inf.mp l.2).2⟩ =
          q ⟨(l' : G), (Subgroup.mem_inf.mp l'.2).2⟩ := h1
      exact (hqeq _ _).mp h3
    obtain ⟨k, hk⟩ := J2A5Five.exists_pow_eq h2
    have hlz : (l : G) * z = z * l :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp l.2).1)
    have hl'z : (l' : G) * z = z * l' :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp l'.2).1)
    have hkz : z * f ^ k * z⁻¹ = f ^ k := by
      rw [hk]
      calc z * ((l : G)⁻¹ * l') * z⁻¹ = (z * l * z⁻¹)⁻¹ * (z * l' * z⁻¹) := by group
        _ = (l : G)⁻¹ * l' := by
          rw [← hlz, ← hl'z, mul_inv_cancel_right, mul_inv_cancel_right]
    rw [hzf] at hkz
    have hfk : f ^ k = 1 := by
      refine J2A5Five.pow_eq_one_of_two_pow_of_five (hf.pow_pow_five k) (k := 1) ?_
      rw [pow_one, pow_two]
      calc f ^ k * f ^ k = f ^ k * (f ^ k)⁻¹ := by rw [hkz]
        _ = 1 := mul_inv_cancel _
    apply Subtype.ext
    calc (l : G) = l * ((l : G)⁻¹ * l') := by rw [← hk, hfk, mul_one]
      _ = l' := by group
  have hlamsurj : Function.Surjective lam := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨k, hk⟩ := c.exists_conj_eq_mul_pow h hcount hf g.2
    have hgf : (g : G) * f = f * g := Subgroup.mem_centralizer_singleton_iff.mp g.2
    have hlz : (g : G) * f ^ (3 * k) ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hf6 : f ^ (6 * k) = f ^ k := by
        rw [show 6 * k = 5 * k + k by ring, pow_add, pow_mul, hf.pow_five, one_pow, one_mul]
      have h2 : f ^ k * (f ^ (3 * k))⁻¹ = f ^ (3 * k) := by
        rw [mul_inv_eq_iff_eq_mul, ← pow_add, show 3 * k + 3 * k = 6 * k by ring, hf6]
      have h1 : z * ((g : G) * f ^ (3 * k)) * z⁻¹ = (g : G) * f ^ (3 * k) := by
        calc z * ((g : G) * f ^ (3 * k)) * z⁻¹ = (z * g * z⁻¹) * (z * f ^ (3 * k) * z⁻¹) := by
              group
          _ = g * (f ^ k * (f ^ (3 * k))⁻¹) := by rw [hk, hzf, mul_assoc]
          _ = g * f ^ (3 * k) := by rw [h2]
      calc (g : G) * f ^ (3 * k) * z = z * ((g : G) * f ^ (3 * k)) * z⁻¹ * z := by rw [h1]
        _ = z * ((g : G) * f ^ (3 * k)) := by group
    have hlf : (g : G) * f ^ (3 * k) ∈ Cf :=
      Cf.mul_mem g.2 (Subgroup.pow_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr rfl) _)
    refine ⟨⟨_, Subgroup.mem_inf.mpr ⟨hlz, hlf⟩⟩, ?_⟩
    show q ⟨(g : G) * f ^ (3 * k), hlf⟩ = q g
    rw [hqeq]
    show ((g : G) * f ^ (3 * k))⁻¹ * g ∈ Subgroup.zpowers f
    rw [mul_inv_rev, inv_mul_cancel_right]
    exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _)
  have hL60 : Nat.card L = 60 := by
    rw [Nat.card_congr (Equiv.ofBijective lam ⟨hlaminj, hlamsurj⟩), Nat.card_congr e.toEquiv,
      nat_card_alternatingGroup, Nat.card_fin]
    rfl
  refine ⟨L, inf_le_left, ?_, hL60, ?_⟩
  ·
    obtain ⟨t, -, ht, -, ht1, -, -⟩ := c.exists_two
    rw [eq_bot_iff]
    by_contra hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥(L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) :=
      (pCoreOf_isPGroup 2 _).to_le inf_le_right
    have hnt : Nontrivial ↥(L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      exact fun h1 => hne (le_of_eq h1)
    obtain ⟨n, hn0, hn⟩ := hp.nontrivial_iff_card.mp hnt
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(L ⊓ pCoreOf 2
      (Subgroup.centralizer ({z} : Set G)))) 2 (by rw [hn]; exact dvd_pow_self 2 hn0.ne')
    have hu2 : (u : G) * u = 1 := by
      have h0 := pow_orderOf_eq_one u
      rw [hu, pow_two] at h0
      exact congrArg Subtype.val h0
    have hu1 : (u : G) ≠ 1 := fun h1 => by
      have h2 : u = 1 := Subtype.ext h1
      rw [h2, orderOf_one] at hu
      norm_num at hu
    have huL := (Subgroup.mem_inf.mp u.2).1
    have huQ := (Subgroup.mem_inf.mp u.2).2
    obtain ⟨g, -, hg⟩ := c.exists_conj_eq_of_mul_self h hcount hf ht ht1
      (Subgroup.mem_inf.mp huL).2 hu2 hu1
    exact c.not_isConj t ht ht1 ((h.isConj_of_mem_pCoreOf huQ hu2 hu1).trans
      (isConj_iff.mpr ⟨g, hg⟩))
  ·
    have hfL : f ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hl).2
    have h1 := Subgroup.orderOf_dvd_natCard _ hfL
    rwa [hf.orderOf_eq] at h1

theorem nonempty_mulEquiv_J2
    (h : IsTypeH2 G z) (hcount : involutionClassCount G = 2) :
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  obtain ⟨L, hLC, hLQ, hL, h5⟩ := c.exists_complement_five_dvd h hcount
  obtain ⟨F, rfl⟩ := J2Frame.exists_frame h hLC hLQ hL
  exact F.nonempty_mulEquiv_J2 j2LineEndgame hcount h5

end J2A5Config

end CFSG.Quasithin
