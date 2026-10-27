module

public import CFSG.RankThree.GF2n.Smith81.Orth28Route

public section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80

namespace CFSG.RankThree.GF2n.Smith81.Orth213

section Abstract

theorem exists_sqrt_split {H : Type*} [Group H] {a b : H} (ha : a * a = 1) (hb : b * b = 1)
    {k N : ℕ} (hk : Odd k) (hcop : Nat.Coprime k N) (hkN : (a * b) ^ (k * N) = 1) :
    ∃ v d : H, Commute v (a * b) ∧ (∃ s : ℤ, d = ((a * b) ^ k) ^ s) ∧
      v⁻¹ * a * v * b = d ∧ (d = 1 → (a * b) ^ k = 1) := by
  set c := a * b with hc
  obtain ⟨s, t, hst⟩ : IsCoprime (k : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hac : a * c * a⁻¹ = c⁻¹ := by
    rw [hc, mul_inv_rev, hainv, hbinv]
    calc a * (a * b) * a = (a * a) * b * a := by simp only [mul_assoc]
      _ = b * a := by rw [ha, one_mul]
  set P : H := c ^ (t * (N : ℤ)) with hP
  have hcP : Commute P c := ((Commute.refl c).zpow_left _)
  have hPk : P ^ k = 1 := by
    rw [hP, ← zpow_natCast, ← zpow_mul]
    have : t * (N : ℤ) * (k : ℤ) = ((k * N : ℕ) : ℤ) * t := by push_cast; ring
    rw [this, zpow_mul, zpow_natCast, hkN, one_zpow]
  have haP : a * P * a⁻¹ = P⁻¹ := by
    rw [hP, ← conj_zpow, hac, inv_zpow]
  have hPcomm : ∀ n : ℕ, a * P ^ n * a⁻¹ = (P ^ n)⁻¹ := fun n => by
    rw [← conj_pow, haP, inv_pow]
  obtain ⟨r, hr⟩ := hk
  set v : H := P ^ (r + 1) with hv
  have hvv : v * v = P := by
    rw [hv, ← pow_add]
    have : r + 1 + (r + 1) = k + 1 := by omega
    rw [this, pow_succ, hPk, one_mul]
  have hvc : Commute v c := hcP.pow_left (r + 1)
  have hav : a * v * a⁻¹ = v⁻¹ := hPcomm (r + 1)
  have h1 : v⁻¹ * a * v = P⁻¹ * a := by
    have h2 : a * v = v⁻¹ * a := by
      have := hav
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    calc v⁻¹ * a * v = v⁻¹ * (a * v) := by rw [mul_assoc]
      _ = v⁻¹ * (v⁻¹ * a) := by rw [h2]
      _ = (v * v)⁻¹ * a := by rw [mul_inv_rev, mul_assoc]
      _ = P⁻¹ * a := by rw [hvv]
  have hcsplit : c = (c ^ k) ^ s * P := by
    have e1 : c = c ^ ((k : ℤ) * s + t * (N : ℤ)) := by
      have : (k : ℤ) * s + t * (N : ℤ) = 1 := by rw [mul_comm (k : ℤ) s]; exact hst
      rw [this, zpow_one]
    rw [zpow_add, zpow_mul, zpow_natCast] at e1
    exact e1
  have hcomm : Commute ((c ^ k) ^ s) P := ((hcP.pow_right k).zpow_right s).symm
  refine ⟨v, (c ^ k) ^ s, hvc, ⟨s, rfl⟩, ?_, ?_⟩
  · rw [h1]
    calc P⁻¹ * a * b = P⁻¹ * c := by rw [hc, mul_assoc]
      _ = P⁻¹ * ((c ^ k) ^ s * P) := by rw [← hcsplit]
      _ = P⁻¹ * (P * (c ^ k) ^ s) := by rw [hcomm.eq]
      _ = (c ^ k) ^ s := inv_mul_cancel_left P _
  · intro hd1
    have hcP' : c = P := by
      calc c = (c ^ k) ^ s * P := hcsplit
        _ = 1 * P := by rw [hd1]
        _ = P := one_mul P
    rw [hcP']
    exact hPk

end Abstract

section Situations

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem exists_sit_conj {X : Subgroup G} {x m : G} (hs : Sit M Q Z X x) (hm : m ∈ M) :
    ∃ X' : Subgroup G, Sit M Q Z X' (m⁻¹ * x * m) := by
  obtain ⟨g, hg⟩ := hs.conj
  refine ⟨conjSubgroup (m⁻¹ * g) Z, hs.hyp, ⟨m⁻¹ * g, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [mem_conjSubgroup]
    have h := hs.mem
    rw [hg, mem_conjSubgroup] at h
    have e : (m⁻¹ * g)⁻¹ * (m⁻¹ * x * m) * (m⁻¹ * g) = g⁻¹ * x * g := by group
    rw [e]
    exact h
  · intro h
    apply hs.ne_one
    have : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
    rw [this, h]
    group
  · exact M.mul_mem (M.mul_mem (M.inv_mem hm) hs.memM) hm
  · intro h
    apply hs.notQ
    have h1 := conj_mem_Q hs.hyp hm h
    have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rwa [e] at h1

theorem isConj_of_sit {X Y : Subgroup G} {x y : G} (hsa : Sit M Q Z X x) (hsb : Sit M Q Z Y y) :
    IsConj x y := by
  obtain ⟨g, hg⟩ := hsa.conj
  obtain ⟨h, hh⟩ := hsb.conj
  have hx : g⁻¹ * x * g ∈ Z := by
    have := hsa.mem
    rwa [hg, mem_conjSubgroup] at this
  have hy : h⁻¹ * y * h ∈ Z := by
    have := hsb.mem
    rwa [hh, mem_conjSubgroup] at this
  have hx1 : g⁻¹ * x * g ≠ 1 := by
    intro h1
    apply hsa.ne_one
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h1]
    group
  have hy1 : h⁻¹ * y * h ≠ 1 := by
    intro h1
    apply hsb.ne_one
    have : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
    rw [this, h1]
    group
  obtain ⟨m, -, hm⟩ := Z_isConj hsa.hyp hx hx1 hy hy1
  refine isConj_iff.mpr ⟨h * m * g⁻¹, ?_⟩
  calc h * m * g⁻¹ * x * (h * m * g⁻¹)⁻¹ = h * (m * (g⁻¹ * x * g) * m⁻¹) * h⁻¹ := by group
    _ = h * (h⁻¹ * y * h) * h⁻¹ := by rw [hm]
    _ = y := by group

end Situations

section GroupPart

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem odd_orderOf_mul_of_actions
    (hc : SmithOrthCfg M Q Z B) (h28 : Smith28OrthStatement) (h4 : Orth212C4CondStatement)
    (h7 : Orth212C7CondStatement)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (ρ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hρπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = ρ m (M₀.π x))
    (hρker : ∀ m : ↥(H0 M Z), ρ m = 1 ↔ (m : G) ∈ Q)
    {X Y : Subgroup G} {a b : ↥(H0 M Z)}
    (hsa : Sit M Q Z X (a : G)) (hsb : Sit M Q Z Y (b : G))
    (hodd : ∃ k : ℕ, Odd k ∧ (ρ a * ρ b) ^ k = 1)
    (hint : ∀ e ∈ LinearMap.range ((ρ a : M₀.E →ₗ[K] M₀.E) - 1),
      (ρ a * ρ b) e = e → e = 0) :
    Odd (orderOf ((a : G) * (b : G))) := by
  have H : StrothHyp M Q Z := hsa.hyp
  obtain ⟨k, hk, hρk⟩ := hodd
  have haa : a * a = 1 := Subtype.ext hsa.x_sq
  have hbb : b * b = 1 := Subtype.ext hsb.x_sq
  have hwρ : ρ ((a * b) ^ k) = 1 := by rw [map_pow, map_mul]; exact hρk
  have hwQ : (((a * b) ^ k : ↥(H0 M Z)) : G) ∈ Q := (hρker _).mp hwρ
  obtain ⟨n, hn⟩ := isPGroup_Q' H ⟨_, hwQ⟩
  have hkN : (a * b) ^ (k * 2 ^ n) = 1 := by
    rw [pow_mul]
    apply Subtype.ext
    have := congrArg Subtype.val hn
    simpa using this
  have hcop : Nat.Coprime k (2 ^ n) := Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hk)
  obtain ⟨v, d, hvc, ⟨s, hds⟩, hvd, hd1⟩ := exists_sqrt_split haa hbb hk hcop hkN
  obtain ⟨a', ha'⟩ : ∃ a' : ↥(H0 M Z), a' = v⁻¹ * a * v := ⟨_, rfl⟩
  have hvM : (v : G) ∈ M := (v.2 : (v : G) ∈ M ⊓ Subgroup.centralizer (Z : Set G)).1
  have ha'M : (a' : G) ∈ M := (a'.2 : (a' : G) ∈ M ⊓ Subgroup.centralizer (Z : Set G)).1
  obtain ⟨X', hs'⟩ := exists_sit_conj hsa hvM
  have hs'a : Sit M Q Z X' (a' : G) := by rw [ha']; exact hs'
  have ha'a' : a' * a' = 1 := by
    rw [ha']
    calc v⁻¹ * a * v * (v⁻¹ * a * v) = v⁻¹ * (a * a) * v := by group
      _ = 1 := by rw [haa]; group
  have hx'x' : (a' : G) * (a' : G) = 1 := by
    have := congrArg Subtype.val ha'a'
    simpa using this
  have hx'inv : (a' : G)⁻¹ = (a' : G) := inv_eq_of_mul_eq_one_right hx'x'
  have hd' : a' * b = d := by rw [ha']; exact hvd
  have hva' : v * a' = a * v := by rw [ha']; group
  have hρva' : ∀ e, ρ v (ρ a' e) = ρ a (ρ v e) := fun e => by
    have h := congrArg (fun T => T e)
      (show ρ v * ρ a' = ρ a * ρ v by rw [← map_mul, ← map_mul, hva'])
    exact h
  have hne' : Q ⊓ QB X' ≠ ⊥ := by
    obtain ⟨v₀, hv₀, hvQ, hvX⟩ := h28 G M Q Z B hc X' _ hs'a
    intro h
    have hm : v₀ ∈ Q ⊓ QB X' := ⟨hvQ, hvX⟩
    rw [h, Subgroup.mem_bot] at hm
    exact ne_one_of_isConj_Z hs'a.ne_one hv₀ hm
  have hdρ : ρ d = 1 := by rw [hds, map_zpow, hwρ, one_zpow]
  have hdQ : (d : G) ∈ Q := (hρker d).mp hdρ
  have hy : (a' : G) * (d : G) = (b : G) := by
    have : a' * d = b := by rw [← hd', ← mul_assoc, ha'a', one_mul]
    rw [← Subgroup.coe_mul, this]
  have hconj : IsConj (a' : G) (b : G) := isConj_of_sit hs'a hsb
  obtain ⟨h, hh⟩ := isConj_iff.mp hconj
  have hh' : h * (a' : G) * h⁻¹ = (a' : G) * (d : G) := by rw [hy]; exact hh
  obtain ⟨q', hq'Q, hq'⟩ := h7 G M Q Z B hc X' (a' : G) hs'a hne' h (d : G) hdQ hh'
  have hbq : (b : G) = q' * (a' : G) * q'⁻¹ := hh.symm.trans hq'
  have hpid : M₀.π (d : G) = ρ a' (M₀.π q') - M₀.π q' := by
    have e : (d : G) = ((a' : G) * q' * (a' : G)⁻¹) * q'⁻¹ := by
      rw [← hd', Subgroup.coe_mul, hbq, hx'inv]
      group
    have h1 : (a' : G) * q' * (a' : G)⁻¹ ∈ Q := conj_mem_Q H ha'M hq'Q
    rw [e, M₀.π_mul _ h1 _ (Q.inv_mem hq'Q), hρπ a' q' hq'Q, Tim79.QuadModel.pi_inv M₀ hq'Q,
      sub_eq_add_neg]
  have hcdG : ((a * b : ↥(H0 M Z)) : G) * (d : G) = (d : G) * ((a * b : ↥(H0 M Z)) : G) := by
    have hcomm : (a * b) * d = d * (a * b) := by
      rw [hds]
      exact (((Commute.refl (a * b)).pow_right k).zpow_right s).eq
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm]
  have hfix : ρ (a * b) (M₀.π (d : G)) = M₀.π (d : G) := by
    rw [← hρπ (a * b) d hdQ, mul_inv_eq_iff_eq_mul.mpr hcdG]
  have hρvc : ∀ e, ρ v (ρ (a * b) e) = ρ (a * b) (ρ v e) := fun e => by
    have h := congrArg (fun T => T e)
      (show ρ v * ρ (a * b) = ρ (a * b) * ρ v by rw [← map_mul, ← map_mul, hvc.eq])
    exact h
  have hf_range : ρ v (M₀.π (d : G)) ∈ LinearMap.range ((ρ a : M₀.E →ₗ[K] M₀.E) - 1) := by
    refine ⟨ρ v (M₀.π q'), ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply, hpid, map_sub, hρva']
    rfl
  have hf_fix : (ρ a * ρ b) (ρ v (M₀.π (d : G))) = ρ v (M₀.π (d : G)) := by
    rw [← map_mul, ← hρvc, hfix]
  have hπd : M₀.π (d : G) = 0 := (ρ v).map_eq_zero_iff.mp (hint _ hf_range hf_fix)
  have hdZ : (d : G) ∈ Z := (M₀.π_ker _ hdQ).mp hπd
  have hconj' : IsConj (a' : G) ((a' : G) * (d : G)) := by rw [hy]; exact hconj
  have hd1' : (d : G) = 1 := h4 G M Q Z B hc X' (a' : G) hs'a hne' (d : G) hdZ hconj'
  have hk1 : (a * b) ^ k = 1 := hd1 (Subtype.ext hd1')
  have hk1' : ((a : G) * (b : G)) ^ k = 1 := by
    have := congrArg Subtype.val hk1
    simpa using this
  exact Odd.of_dvd_nat hk (orderOf_dvd_of_pow_eq_one hk1')

end GroupPart

end CFSG.RankThree.GF2n.Smith81.Orth213
