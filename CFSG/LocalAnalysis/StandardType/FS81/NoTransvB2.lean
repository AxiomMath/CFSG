module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvCube

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

variable {G : Type} [Group G]

@[expose] def SignRealized {n : ℕ} (B : Basis3 G (n + 1)) (E : Subgroup G)
    (s : Fin (n + 1) → ZMod 3) : Prop :=
  IsSign s ∧ s 0 = 1 ∧ ∃ d ∈ Subgroup.normalizer (E : Set G), B.Acts d (spMat 1 s)

@[expose] def KleinSigns {n : ℕ} (B : Basis3 G (n + 1)) (E : Subgroup G) : Prop :=
  ∃ s s' : Fin (n + 1) → ZMod 3, SignRealized B E s ∧ SignRealized B E s' ∧
    SignRealized B E (s * s') ∧ ∀ k : Fin (n + 1), k ≠ 0 → s k = -1 ∨ s' k = -1

@[expose] def DiagSigns3 {n : ℕ} (B : Basis3 G (n + 1)) (E : Subgroup G) : Prop :=
  ∀ i j k : Fin (n + 1), i ≠ 0 → j ≠ 0 → k ≠ 0 → j ≠ i →
    ∃ s : Fin (n + 1) → ZMod 3, SignRealized B E s ∧ s k ≠ s i * s j

@[expose] def trace4 (σ σ' τ x : G) : G :=
  x * (σ * x * σ⁻¹) * (σ' * x * σ'⁻¹) * (τ * x * τ⁻¹)

theorem mul_eight_comm {Q : Type*} [Group Q] {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Q}
    (h1 : Commute a₂ b₁) (h2 : Commute a₂ c₁) (h3 : Commute a₂ d₁) (h4 : Commute b₂ c₁)
    (h5 : Commute b₂ d₁) (h6 : Commute c₂ d₁) :
    a₁ * a₂ * (b₁ * b₂) * (c₁ * c₂) * (d₁ * d₂) = a₁ * b₁ * c₁ * d₁ * (a₂ * b₂ * c₂ * d₂) := by
  simp only [mul_assoc]
  rw [h1.left_comm, h4.left_comm, h2.left_comm, h6.left_comm, h5.left_comm, h3.left_comm]

namespace TransvP1

variable [Finite G] {b₀ : G} {K E P₁ : Subgroup G}

theorem fix_of_coprime (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {c : G}
    (hc : c ∈ Subgroup.centralizer (E : Set G)) (hcP : c ∈ Subgroup.normalizer (P₁ : Set G))
    (hco : (orderOf c).Coprime 3) {x : G} (hx : x ∈ P₁) : c * x * c⁻¹ = x := by
  have hcxP : c * x * c⁻¹ ∈ P₁ := (Subgroup.mem_normalizer_iff.mp hcP x).mp hx
  set e := c * x * c⁻¹ * x⁻¹ with he
  have heE : e ∈ E := hP.mem_E h (P₁.mul_mem hcxP (P₁.inv_mem hx)) (by
    have hc0 : c * b₀ * c⁻¹ = b₀ := by
      rw [← Subgroup.mem_centralizer_iff.mp hc b₀ h.b0_mem, mul_inv_cancel_right]
    rw [tb_mul (hP.le hcxP) (hP.le (P₁.inv_mem hx)), tb_conj hc0, tb_inv (hP.le hx),
      ← Subgroup.mem_centralizer_iff.mp hc _ (tb_mem (hP.le hx)).1, mul_inv_cancel_right,
      mul_inv_cancel])
  have hce : c * e = e * c := (Subgroup.mem_centralizer_iff.mp hc e heE).symm
  have hpow : ∀ m : ℕ, c ^ m * x * (c ^ m)⁻¹ = e ^ m * x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc c ^ (m + 1) * x * (c ^ (m + 1))⁻¹ = c * (c ^ m * x * (c ^ m)⁻¹) * c⁻¹ := by group
        _ = c * (e ^ m * x) * c⁻¹ := by rw [ih]
        _ = e ^ m * (c * x * c⁻¹) := by
          rw [show c * (e ^ m * x) * c⁻¹ = (c * e ^ m) * x * c⁻¹ by group,
            ((Commute.pow_right hce m).eq)]
          group
        _ = e ^ (m + 1) * x := by rw [show c * x * c⁻¹ = e * x by rw [he]; group, pow_succ]; group
  have hem : e ^ orderOf c = 1 := by
    have := hpow (orderOf c)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at this
    exact (mul_eq_right.mp this.symm)
  have he3 : e ^ 3 = 1 := h.elem.2 e heE
  have hord : orderOf e = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hem
    have h3 := orderOf_dvd_of_pow_eq_one he3
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hco) h3
  have he1 : e = 1 := orderOf_eq_one_iff.mp hord
  rw [he] at he1
  exact mul_inv_eq_one.mp he1

theorem comm_centralizer_mem_A (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {c : G}
    (hc : c ∈ Subgroup.centralizer (E : Set G)) (hcP : c ∈ Subgroup.normalizer (P₁ : Set G))
    {x : G} (hx : x ∈ P₁) : c * x * c⁻¹ * x⁻¹ ∈ E ⊓ K := by
  obtain ⟨a, b, hab, ⟨k, hak⟩, hbc, haz, hbz⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.exists_mul_eq_isPGroup_coprime c Nat.prime_three
  have hzC : Subgroup.zpowers c ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.zpowers_le.mpr hc
  have hzP : Subgroup.zpowers c ≤ Subgroup.normalizer (P₁ : Set G) :=
    Subgroup.zpowers_le.mpr hcP
  have haE : a ∈ E := h.syl a (hzC haz) k hak
  have hbx : b * x * b⁻¹ = x := hP.fix_of_coprime h (hzC hbz) (hzP hbz) hbc hx
  have h1 : c * x * c⁻¹ * x⁻¹ = a * x * a⁻¹ * x⁻¹ := by
    rw [← hab, show a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ by group, hbx]
  rw [h1]
  have := Subgroup.inv_mem _ (h.comm_E_mem_A (hP.le hx) haE)
  rwa [show (x * a * x⁻¹ * a⁻¹)⁻¹ = a * x * a⁻¹ * x⁻¹ by group] at this

theorem conj_congr_A (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {m m' : G}
    (hmP : m ∈ Subgroup.normalizer (P₁ : Set G))
    (hm' : m' ∈ Subgroup.normalizer (E : Set G)) (hm'P : m' ∈ Subgroup.normalizer (P₁ : Set G))
    (hmm' : ∀ y ∈ E, m * y * m⁻¹ = m' * y * m'⁻¹) {x : G} (hx : x ∈ P₁) :
    m * x * m⁻¹ * (m' * x * m'⁻¹)⁻¹ ∈ E ⊓ K := by
  have hc : m'⁻¹ * m ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hmm' y hy
    calc y * (m'⁻¹ * m) = m'⁻¹ * (m' * y * m'⁻¹) * m := by group
      _ = m'⁻¹ * (m * y * m⁻¹) * m := by rw [h1]
      _ = m'⁻¹ * m * y := by group
  have hcP : m'⁻¹ * m ∈ Subgroup.normalizer (P₁ : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hm'P) hmP
  have h1 := hP.comm_centralizer_mem_A h hc hcP hx
  have h2 := h.inv m' hm' _ h1
  rwa [show m' * (m'⁻¹ * m * x * (m'⁻¹ * m)⁻¹ * x⁻¹) * m'⁻¹ =
    m * x * m⁻¹ * (m' * x * m'⁻¹)⁻¹ by group] at h2

end TransvP1

theorem acts_vec_sign {n : ℕ} (B : Basis3 G (n + 1)) {E : Subgroup G} (hBE : B.span = E) {d : G}
    (hdN : d ∈ Subgroup.normalizer (E : Set G)) {t : Fin (n + 1) → ZMod 3}
    (hd : B.Acts d (spMat 1 t)) (e : Coords (n + 1)) :
    d * B.vec e * d⁻¹ = B.vec (fun i => t i * e i) := by
  rw [B.acts_vec' (by rw [hBE]; exact hdN) hd, spMat_mulVec]
  rfl

theorem sign_comm_on {n : ℕ} (B : Basis3 G (n + 1)) {E : Subgroup G} (hBE : B.span = E) {d d' : G}
    (hdN : d ∈ Subgroup.normalizer (E : Set G)) (hd'N : d' ∈ Subgroup.normalizer (E : Set G))
    {t t' : Fin (n + 1) → ZMod 3} (hd : B.Acts d (spMat 1 t)) (hd' : B.Acts d' (spMat 1 t'))
    {y : G} (hy : y ∈ E) : d * d' * y * (d * d')⁻¹ = d' * d * y * (d' * d)⁻¹ := by
  obtain ⟨e, rfl⟩ := B.exists_vec_eq (hBE ▸ hy)
  rw [show d * d' * B.vec e * (d * d')⁻¹ = d * (d' * B.vec e * d'⁻¹) * d⁻¹ by group,
    show d' * d * B.vec e * (d' * d)⁻¹ = d' * (d * B.vec e * d⁻¹) * d'⁻¹ by group,
    acts_vec_sign B hBE hd'N hd', acts_vec_sign B hBE hdN hd, acts_vec_sign B hBE hdN hd,
    acts_vec_sign B hBE hd'N hd']
  congr 1
  funext i
  ring

theorem sign_fix_b0 {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G} (hb0 : B.b 0 = b₀) {d : G}
    {t : Fin (n + 1) → ZMod 3} (hd : B.Acts d (spMat 1 t)) (ht0 : t 0 = 1) :
    d * b₀ * d⁻¹ = b₀ := by
  have := B.acts_spMat_one hd 0
  rwa [ht0, ZMod.val_one, pow_one, hb0] at this

namespace TransvP1

variable [Finite G] {b₀ : G} {K E P₁ : Subgroup G}

theorem exists_sign_lift (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) {t : Fin (n + 1) → ZMod 3}
    (ht : SignRealized B E t) :
    ∃ d ∈ Subgroup.normalizer (E : Set G), d ∈ Subgroup.normalizer (P₁ : Set G) ∧
      B.Acts d (spMat 1 t) ∧ d * b₀ * d⁻¹ = b₀ := by
  obtain ⟨-, ht0, d, hdN, hd⟩ := ht
  obtain ⟨d', hd'N, hd'P, hd'⟩ := hP.exists_lift h hdN
  have hbE : ∀ i, B.b i ∈ E := fun i => hB.1 ▸ B.b_mem_span i
  have hacts : B.Acts d' (spMat 1 t) := fun j => by rw [hd' _ (hbE j)]; exact hd j
  exact ⟨d', hd'N, hd'P, hacts, sign_fix_b0 B hB.2.1 hacts ht0⟩

end TransvP1

namespace TransvP1

variable [Finite G] {b₀ : G} {K E P₁ : Subgroup G}

theorem trace4_mul_mem (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E) {σ σ' τ : G}
    (hσ : σ ∈ Subgroup.normalizer (P₁ : Set G)) (hσ' : σ' ∈ Subgroup.normalizer (P₁ : Set G))
    (hτ : τ ∈ Subgroup.normalizer (P₁ : Set G)) {x y : G} (hx : x ∈ P₁) (hy : y ∈ P₁) :
    trace4 σ σ' τ (x * y) * (trace4 σ σ' τ x * trace4 σ σ' τ y)⁻¹ ∈ E ⊓ K := by
  have := h.normal_A
  have hcj : ∀ {g z : G}, g ∈ Subgroup.normalizer (P₁ : Set G) → z ∈ P₁ → g * z * g⁻¹ ∈ P₁ :=
    fun hg hz => (Subgroup.mem_normalizer_iff.mp hg _).mp hz
  let np : ∀ {z : G}, z ∈ P₁ → ↥(Subgroup.normalizer (E : Set G)) :=
    fun {z} hz => ⟨z, mem_normalizer hP.toSylowN1 hz⟩
  have hc : ∀ {u v : G} (hu : u ∈ P₁) (hv : v ∈ P₁),
      Commute (QuotientGroup.mk (np hu) :
        _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) (QuotientGroup.mk (np hv)) :=
    fun hu hv => quot_commute_of_mem (u := np hu) (v := np hv) (hP.comm_mem_A h B hB hsc hu hv)
  have hTP : ∀ {z : G}, z ∈ P₁ → trace4 σ σ' τ z ∈ P₁ := fun hz =>
    P₁.mul_mem (P₁.mul_mem (P₁.mul_mem hz (hcj hσ hz)) (hcj hσ' hz)) (hcj hτ hz)
  have hTq : ∀ {z : G} (hz : z ∈ P₁),
      (QuotientGroup.mk (np (hTP hz)) :
        _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) =
      QuotientGroup.mk (np hz) * QuotientGroup.mk (np (hcj hσ hz)) *
        QuotientGroup.mk (np (hcj hσ' hz)) * QuotientGroup.mk (np (hcj hτ hz)) := by
    intro z hz
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have hxy := P₁.mul_mem hx hy
  have hkey : (QuotientGroup.mk (np (hTP hxy)) :
      _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) =
      QuotientGroup.mk (np (hTP hx)) * QuotientGroup.mk (np (hTP hy)) := by
    have e1 : np (hTP hxy) = np hx * np hy * (np (hcj hσ hx) * np (hcj hσ hy)) *
        (np (hcj hσ' hx) * np (hcj hσ' hy)) * (np (hcj hτ hx) * np (hcj hτ hy)) :=
      Subtype.ext (by simp only [np, trace4, Subgroup.coe_mul]; group)
    rw [e1, hTq hx, hTq hy]
    simp only [QuotientGroup.mk_mul]
    exact mul_eight_comm (hc hy (hcj hσ hx)) (hc hy (hcj hσ' hx)) (hc hy (hcj hτ hx))
      (hc (hcj hσ hy) (hcj hσ' hx)) (hc (hcj hσ hy) (hcj hτ hx)) (hc (hcj hσ' hy) (hcj hτ hx))
  have := (quot_eq_one_iff (A := E ⊓ K)
    (np (hTP hxy) * (np (hTP hx) * np (hTP hy))⁻¹)).mp (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, hkey, mul_inv_cancel])
  simpa [np] using this

end TransvP1

namespace TransvP1

variable [Finite G] {b₀ : G} {K E P₁ : Subgroup G}

omit [Finite G] in
theorem quot_eq_of_mem {N A : Subgroup G} [(A.subgroupOf N).Normal] {u v : ↥N}
    (huv : (u : G) * (v : G)⁻¹ ∈ A) :
    (QuotientGroup.mk u : ↥N ⧸ A.subgroupOf N) = QuotientGroup.mk v := by
  have h1 : (QuotientGroup.mk (u * v⁻¹) : ↥N ⧸ A.subgroupOf N) = 1 :=
    (quot_eq_one_iff _).mpr (by simpa using huv)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h1
  exact h1

theorem exists_B2 (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E)
    (hKl : KleinSigns B E) :
    ∃ B₂ : Subgroup G, B₂ ≤ P₁ ∧ E ⊓ K ≤ B₂ ∧ (∀ x ∈ B₂, x ∈ E → x ∈ E ⊓ K) ∧
      (∀ x ∈ P₁, ∃ j : ℤ, x * b₀ ^ j ∈ B₂) ∧ b₀ ∉ B₂ ∧
      ∀ d ∈ Subgroup.normalizer (E : Set G), d ∈ Subgroup.normalizer (P₁ : Set G) →
        ∀ t : Fin (n + 1) → ZMod 3, t 0 = 1 → B.Acts d (spMat 1 t) →
          ∀ x ∈ B₂, d * x * d⁻¹ ∈ B₂ := by
  have := h.normal_A
  obtain ⟨s, s', hs, hs', hss', hcov⟩ := hKl
  obtain ⟨σ, hσN, hσP, hσA, hσb⟩ := hP.exists_sign_lift h B hB hs
  obtain ⟨σ', hσ'N, hσ'P, hσ'A, hσ'b⟩ := hP.exists_sign_lift h B hB hs'
  obtain ⟨τ, hτN, hτP, hτA, hτb⟩ := hP.exists_sign_lift h B hB hss'
  have hcj : ∀ {g z : G}, g ∈ Subgroup.normalizer (P₁ : Set G) → z ∈ P₁ → g * z * g⁻¹ ∈ P₁ :=
    fun hg hz => (Subgroup.mem_normalizer_iff.mp hg _).mp hz
  set T := trace4 σ σ' τ with hTdef
  have hmulT : ∀ {x y : G}, x ∈ P₁ → y ∈ P₁ → T (x * y) * (T x * T y)⁻¹ ∈ E ⊓ K :=
    fun hx hy => hP.trace4_mul_mem h B hB hsc hσP hσ'P hτP hx hy
  have hT1 : T 1 = 1 := by simp [hTdef, trace4]
  have hTP : ∀ {z : G}, z ∈ P₁ → T z ∈ P₁ := fun hz =>
    P₁.mul_mem (P₁.mul_mem (P₁.mul_mem hz (hcj hσP hz)) (hcj hσ'P hz)) (hcj hτP hz)
  let B₂ : Subgroup G :=
    { carrier := {x | x ∈ P₁ ∧ T x ∈ E ⊓ K}
      mul_mem' := fun {x y} hx hy => ⟨P₁.mul_mem hx.1 hy.1, by
        have := Subgroup.mul_mem _ (hmulT hx.1 hy.1) (Subgroup.mul_mem _ hx.2 hy.2)
        rwa [inv_mul_cancel_right] at this⟩
      one_mem' := ⟨P₁.one_mem, by rw [hT1]; exact Subgroup.one_mem _⟩
      inv_mem' := fun {x} hx => ⟨P₁.inv_mem hx.1, by
        have h1 := hmulT (P₁.inv_mem hx.1) hx.1
        rw [inv_mul_cancel, hT1, one_mul] at h1
        have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) (Subgroup.inv_mem _ hx.2)
        rwa [inv_inv, mul_inv_cancel_right] at h2⟩ }
  have hmemB₂ : ∀ {x : G}, x ∈ B₂ ↔ x ∈ P₁ ∧ T x ∈ E ⊓ K := Iff.rfl
  have hTb : ∀ m : ℤ, T (b₀ ^ m) = b₀ ^ m := by
    intro m
    have hb3 : b₀ ^ 3 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one b₀
    simp only [hTdef, trace4]
    rw [← conj_zpow, ← conj_zpow, ← conj_zpow, hσb, hσ'b, hτb]
    rw [← zpow_add, ← zpow_add, ← zpow_add]
    have : m + m + m + m = m + 3 * m := by ring
    rw [this, zpow_add, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hb3,
      one_zpow, mul_one]
  have hTE : ∀ {x : G}, x ∈ P₁ → T x ∈ E := by
    intro x hx
    refine hP.mem_E h (hTP hx) ?_
    have hxN := hP.le hx
    have hgN := fun {g : G} (hg : g ∈ Subgroup.normalizer (P₁ : Set G)) => hP.le (hcj hg hx)
    have hxA := tb_mem hxN
    have hxS : tb b₀ x ∈ B.span := hB.1 ▸ hxA.1
    set e := B.coords ⟨tb b₀ x, hxS⟩ with hedef
    have he : B.vec e = tb b₀ x := B.vec_coords _
    have he0 : e 0 = 0 :=
      B.coords_zero_of_mem hB.2.1 h.ord hB.2.2 (hB.1 ▸ h.disj) ⟨tb b₀ x, hxS⟩ hxA.2
    simp only [hTdef, trace4]
    rw [tb_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN (hgN hσP)) (hgN hσ'P)) (hgN hτP),
      tb_mul (Subgroup.mul_mem _ hxN (hgN hσP)) (hgN hσ'P), tb_mul hxN (hgN hσP),
      tb_conj hσb, tb_conj hσ'b, tb_conj hτb, ← he,
      acts_vec_sign B hB.1 hσN hσA, acts_vec_sign B hB.1 hσ'N hσ'A,
      acts_vec_sign B hB.1 hτN hτA, ← B.vec_add, ← B.vec_add, ← B.vec_add]
    have hz : (e + (fun i => s i * e i) + (fun i => s' i * e i) +
        fun i => (s * s') i * e i) = 0 := by
      funext k
      simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply]
      by_cases hk : k = 0
      · rw [hk, he0]; ring
      · rcases hcov k hk with h1 | h1 <;> rw [h1] <;> ring
    rw [hz, B.vec_zero]
  let np : ∀ {z : G}, z ∈ P₁ → ↥(Subgroup.normalizer (E : Set G)) :=
    fun {z} hz => ⟨z, mem_normalizer hP.toSylowN1 hz⟩
  have hTq : ∀ {z : G} (hz : z ∈ P₁),
      (QuotientGroup.mk (np (hTP hz)) :
        _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) =
      QuotientGroup.mk (np hz) * QuotientGroup.mk (np (hcj hσP hz)) *
        QuotientGroup.mk (np (hcj hσ'P hz)) * QuotientGroup.mk (np (hcj hτP hz)) := by
    intro z hz
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have hb0P : b₀ ∈ P₁ := hP.E_le h.b0_mem
  refine ⟨B₂, fun x hx => hx.1, fun a ha => ⟨hP.E_le ha.1, ?_⟩, ?_, ?_, ?_, ?_⟩
  ·
    simp only [hTdef, trace4]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha (h.inv σ hσN a ha))
      (h.inv σ' hσ'N a ha)) (h.inv τ hτN a ha)
  ·
    intro x hx hxE
    have hxP := hx.1
    have hfix : ∀ {g : G} (hgN : g ∈ Subgroup.normalizer (E : Set G))
        (hgP : g ∈ Subgroup.normalizer (P₁ : Set G)), g * b₀ * g⁻¹ = b₀ →
        (QuotientGroup.mk (np (hcj hgP hxP)) :
          _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) =
          QuotientGroup.mk (np hxP) := fun hgN _ hgb =>
      quot_eq_of_mem (h.conj_mul_inv_mem_A hgN hgb hxE)
    have h4 : (QuotientGroup.mk (np hxP) :
        _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) ^ 4 = 1 := by
      have := hTq hxP
      rw [hfix hσN hσP hσb, hfix hσ'N hσ'P hσ'b, hfix hτN hτP hτb,
        (quot_eq_one_iff (np (hTP hxP))).mpr hx.2] at this
      rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_succ,
        pow_zero, one_mul]
      exact this.symm
    have h3 : (QuotientGroup.mk (np hxP) :
        _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      exact (quot_eq_one_iff _).mpr (by simp [np, h.elem.2 x hxE])
    have h1 : (QuotientGroup.mk (np hxP) :
        _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) = 1 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h3, one_mul] at h4
      exact h4
    exact (quot_eq_one_iff (np hxP)).mp h1
  ·
    intro x hx
    have hTxE := hTE hx
    rw [← h.sup] at hTxE
    obtain ⟨y, hy, a, ha, hya⟩ := fs81Sp_mem_sup_of_commute (A := Subgroup.zpowers b₀)
      (B := E ⊓ K) (fun y hy z hz => h.comm (h.sup ▸ Subgroup.mem_sup_left hy) hz.1) hTxE
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨-i, P₁.mul_mem hx (P₁.zpow_mem hb0P _), ?_⟩
    have h1 := hmulT hx (P₁.zpow_mem hb0P (-i))
    rw [hTb] at h1
    have h2 : T x * b₀ ^ (-i) ∈ E ⊓ K := by
      rw [hya, zpow_neg, h.comm (E.zpow_mem h.b0_mem i) ha.1, mul_inv_cancel_right]
      exact ha
    have := Subgroup.mul_mem _ h1 h2
    rwa [inv_mul_cancel_right] at this
  ·
    intro hb
    have h1 : T b₀ ∈ E ⊓ K := hb.2
    rw [show T b₀ = b₀ by simpa using hTb 1] at h1
    have h2 : b₀ ∈ Subgroup.zpowers b₀ ⊓ (E ⊓ K) := ⟨Subgroup.mem_zpowers b₀, h1⟩
    rw [disjoint_iff.mp h.disj, Subgroup.mem_bot] at h2
    have := h.ord
    rw [h2, orderOf_one] at this
    exact absurd this (by norm_num)
  ·
    intro d hdN hdP t ht0 hdA x hx
    have hxP := hx.1
    have hdb := sign_fix_b0 B hB.2.1 hdA ht0
    have hdxP : d * x * d⁻¹ ∈ P₁ := hcj hdP hxP
    refine ⟨hdxP, ?_⟩
    have hswap : ∀ {g : G}, g ∈ Subgroup.normalizer (E : Set G) →
        (hgP : g ∈ Subgroup.normalizer (P₁ : Set G)) → ∀ {u : Fin (n + 1) → ZMod 3},
        B.Acts g (spMat 1 u) →
        (QuotientGroup.mk (np (hcj hgP hdxP)) :
          _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) =
          QuotientGroup.mk (np (hcj hdP (hcj hgP hxP))) := by
      intro g hgN hgP u hgA
      refine quot_eq_of_mem ?_
      have := hP.conj_congr_A h (Subgroup.mul_mem _ hgP hdP)
        (Subgroup.mul_mem _ hdN hgN) (Subgroup.mul_mem _ hdP hgP)
        (fun y hy => sign_comm_on B hB.1 hgN hdN hgA hdA hy) hxP
      rwa [show g * d * x * (g * d)⁻¹ * (d * g * x * (d * g)⁻¹)⁻¹ =
        g * (d * x * d⁻¹) * g⁻¹ * (d * (g * x * g⁻¹) * d⁻¹)⁻¹ by group] at this
    have hdT : d * T x * d⁻¹ ∈ E ⊓ K := h.inv d hdN _ hx.2
    have hdTP : d * T x * d⁻¹ ∈ P₁ := hcj hdP (hTP hxP)
    have hq : (QuotientGroup.mk (np (hTP hdxP)) :
        _ ⧸ (E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))) =
        QuotientGroup.mk (np hdTP) := by
      rw [hTq hdxP, hswap hσN hσP hσA, hswap hσ'N hσ'P hσ'A, hswap hτN hτP hτA,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (by simp only [np, hTdef, trace4, Subgroup.coe_mul]; group)
    exact (quot_eq_one_iff (np (hTP hdxP))).mp (hq.trans ((quot_eq_one_iff (np hdTP)).mpr hdT))

end TransvP1

theorem comm_inv_left_eq {u v : G} (hc : Commute (u * v * u⁻¹ * v⁻¹) u) :
    u⁻¹ * v * u⁻¹⁻¹ * v⁻¹ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by
  calc u⁻¹ * v * u⁻¹⁻¹ * v⁻¹ = u⁻¹ * ((u * v * u⁻¹ * v⁻¹)⁻¹ * u) := by group
    _ = u⁻¹ * (u * (u * v * u⁻¹ * v⁻¹)⁻¹) := by rw [hc.inv_left.eq]
    _ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by group

theorem comm_inv_right_eq {u v : G} (hc : Commute (u * v * u⁻¹ * v⁻¹) v) :
    u * v⁻¹ * u⁻¹ * v⁻¹⁻¹ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by
  calc u * v⁻¹ * u⁻¹ * v⁻¹⁻¹ = v⁻¹ * ((u * v * u⁻¹ * v⁻¹)⁻¹ * v) := by group
    _ = v⁻¹ * (v * (u * v * u⁻¹ * v⁻¹)⁻¹) := by rw [hc.inv_left.eq]
    _ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by group

theorem comm_mul_central_eq {α α' u v : G} (h1 : Commute α u) (h2 : Commute α α')
    (h3 : Commute α v) (h4 : Commute α' v) (h5 : Commute α' u) :
    α * u * (α' * v) * (α * u)⁻¹ * (α' * v)⁻¹ = u * v * u⁻¹ * v⁻¹ := by
  rw [mul_inv_rev, mul_inv_rev]
  simp only [mul_assoc]
  rw [h1.left_comm, h2.left_comm, h3.left_comm, h1.inv_right.left_comm, mul_inv_cancel_left,
    h4.left_comm, h5.inv_right.left_comm, h4.inv_right.left_comm, mul_inv_cancel, mul_one]

namespace TransvP1

variable [Finite G] {b₀ : G} {K E P₁ : Subgroup G}

theorem tb_eq_one_of_mem_E (h : TransvSetup b₀ K E) {e : G} (he : e ∈ E) : tb b₀ e = 1 := by
  rw [tb, h.comm he h.b0_mem, mul_inv_cancel_right, inv_mul_cancel]

theorem forall_of_gen_B2 (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) {B₂ : Subgroup G} (hB₂P : B₂ ≤ P₁)
    (hB₂E : ∀ x ∈ B₂, x ∈ E → x ∈ E ⊓ K) {p : G → Prop}
    (hmul : ∀ x y, x ∈ B₂ → y ∈ B₂ → p x → p y → p (x * y)) (hinv : ∀ x, x ∈ B₂ → p x → p x⁻¹)
    (hA : ∀ a ∈ E ⊓ K, p a) (hgen : ∀ k : Fin (n + 1), k ≠ 0 → ∃ x ∈ B₂, tb b₀ x = B.b k ∧ p x) :
    ∀ y ∈ B₂, p y := by
  let T : Subgroup G :=
    { carrier := {a | ∃ x ∈ B₂, p x ∧ tb b₀ x = a}
      mul_mem' := fun {a a'} ⟨x, hx, hpx, hxa⟩ ⟨x', hx', hpx', hxa'⟩ =>
        ⟨x * x', B₂.mul_mem hx hx', hmul x x' hx hx' hpx hpx', by
          rw [tb_mul (hP.le (hB₂P hx)) (hP.le (hB₂P hx')), hxa, hxa']⟩
      one_mem' := ⟨1, B₂.one_mem, hA 1 (Subgroup.one_mem _), tb_one b₀⟩
      inv_mem' := fun {a} ⟨x, hx, hpx, hxa⟩ =>
        ⟨x⁻¹, B₂.inv_mem hx, hinv x hx hpx, by rw [tb_inv (hP.le (hB₂P hx)), hxa]⟩ }
  have hbT : ∀ i : Fin (n + 1), i ≠ 0 → B.b i ∈ T := fun i hi => by
    obtain ⟨x, hx, hxb, hpx⟩ := hgen i hi
    exact ⟨x, hx, hpx, hxb⟩
  intro y hy
  have hyP := hB₂P hy
  have hyA : tb b₀ y ∈ E ⊓ K := tb_mem (hP.le hyP)
  have hyS : tb b₀ y ∈ B.span := hB.1 ▸ hyA.1
  have hdisj : Disjoint (Subgroup.zpowers b₀) (B.span ⊓ K) := hB.1 ▸ h.disj
  have h0 := B.coords_zero_of_mem hB.2.1 h.ord hB.2.2 hdisj ⟨tb b₀ y, hyS⟩ hyA.2
  have hT : tb b₀ y ∈ T := by
    have := B.vec_mem_of_zero (K := T) hbT h0
    rwa [B.vec_coords] at this
  obtain ⟨x, hx, hpx, hxy⟩ := hT
  have hxyB : x⁻¹ * y ∈ B₂ := B₂.mul_mem (B₂.inv_mem hx) hy
  have hxyE : x⁻¹ * y ∈ E := hP.mem_E h (hB₂P hxyB) (by
    rw [tb_mul (hP.le (hB₂P (B₂.inv_mem hx))) (hP.le hyP), tb_inv (hP.le (hB₂P hx)), hxy,
      inv_mul_cancel])
  have := hmul x (x⁻¹ * y) hx hxyB hpx (hA _ (hB₂E _ hxyB hxyE))
  rwa [mul_inv_cancel_left] at this

theorem B2_comm (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E)
    (hd3 : DiagSigns3 B E) {B₂ : Subgroup G} (hB₂P : B₂ ≤ P₁)
    (hB₂E : ∀ x ∈ B₂, x ∈ E → x ∈ E ⊓ K) (hcos : ∀ x ∈ P₁, ∃ j : ℤ, x * b₀ ^ j ∈ B₂)
    (hinv : ∀ d ∈ Subgroup.normalizer (E : Set G), d ∈ Subgroup.normalizer (P₁ : Set G) →
      ∀ t : Fin (n + 1) → ZMod 3, t 0 = 1 → B.Acts d (spMat 1 t) → ∀ x ∈ B₂, d * x * d⁻¹ ∈ B₂) :
    ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x := by
  have hbE : ∀ i, B.b i ∈ E := fun i => hB.1 ▸ B.b_mem_span i
  have hbA : ∀ i : Fin (n + 1), i ≠ 0 → B.b i ∈ E ⊓ K := fun i hi => ⟨hbE i, hB.2.2 i hi⟩
  have hpre : ∀ k : Fin (n + 1), k ≠ 0 → ∃ x ∈ B₂, tb b₀ x = B.b k := by
    intro k hk
    obtain ⟨x, hx, hxb⟩ := hP.surj _ (hbA k hk)
    obtain ⟨j, hj⟩ := hcos x hx
    refine ⟨x * b₀ ^ j, hj, ?_⟩
    rw [tb_mul (hP.le hx) (hP.le (hP.E_le (E.zpow_mem h.b0_mem j))),
      tb_eq_one_of_mem_E h (E.zpow_mem h.b0_mem j), mul_one, hxb]
  choose! xk hxkB hxkb using hpre
  have hcen : ∀ {a u : G}, a ∈ E ⊓ K → u ∈ P₁ → Commute a u := fun {a u} ha hu => by
    have h1 : u * a * u⁻¹ = a := (hP.le hu).2.1 _ ha
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have heig : ∀ {d : G}, d ∈ Subgroup.normalizer (E : Set G) →
      d ∈ Subgroup.normalizer (P₁ : Set G) → ∀ {t : Fin (n + 1) → ZMod 3}, t 0 = 1 →
      B.Acts d (spMat 1 t) → ∀ {i : Fin (n + 1)}, i ≠ 0 → ∀ {w : G}, w ∈ B₂ →
      tb b₀ w = B.b i ^ (t i).val → ∃ a ∈ E ⊓ K, d * xk i * d⁻¹ = a * w := by
    intro d hdN hdP t ht0 hdA i hi w hwB htbw
    have hdb := sign_fix_b0 B hB.2.1 hdA ht0
    have hx := hxkB i hi
    have hdx : d * xk i * d⁻¹ ∈ B₂ := hinv d hdN hdP t ht0 hdA _ hx
    have htb : tb b₀ (d * xk i * d⁻¹) = B.b i ^ (t i).val := by
      rw [tb_conj hdb, hxkb i hi, B.acts_spMat_one hdA]
    have hq : d * xk i * d⁻¹ * w⁻¹ ∈ B₂ := B₂.mul_mem hdx (B₂.inv_mem hwB)
    have hqE : d * xk i * d⁻¹ * w⁻¹ ∈ E := hP.mem_E h (hB₂P hq) (by
      rw [tb_mul (hP.le (hB₂P hdx)) (hP.le (hB₂P (B₂.inv_mem hwB))), tb_inv (hP.le (hB₂P hwB)),
        htb, htbw, mul_inv_cancel])
    exact ⟨_, hB₂E _ hq hqE, by group⟩
  have htb_pos : ∀ {i : Fin (n + 1)}, i ≠ 0 → ∀ {u : ZMod 3}, u = 1 →
      tb b₀ (xk i) = B.b i ^ u.val := fun {i} hi {u} hu => by
    rw [hu, ZMod.val_one, pow_one, hxkb _ hi]
  have htb_neg : ∀ {i : Fin (n + 1)}, i ≠ 0 → ∀ {u : ZMod 3}, u = -1 →
      tb b₀ (xk i)⁻¹ = B.b i ^ u.val := fun {i} hi {u} hu => by
    have h3 : B.b i ^ 3 = 1 := by rw [← B.ord i]; exact pow_orderOf_eq_one _
    rw [hu, show ((-1 : ZMod 3)).val = 2 from rfl, tb_inv (hP.le (hB₂P (hxkB i hi))), hxkb _ hi]
    exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)).symm
  have hgen : ∀ i : Fin (n + 1), i ≠ 0 → ∀ j : Fin (n + 1), j ≠ 0 →
      xk i * xk j = xk j * xk i := by
    intro i hi j hj
    by_cases hji : j = i
    · rw [hji]
    have hxi := hB₂P (hxkB i hi)
    have hxj := hB₂P (hxkB j hj)
    set c := xk i * xk j * (xk i)⁻¹ * (xk j)⁻¹ with hc
    have hcA : c ∈ E ⊓ K := hP.comm_mem_A h B hB hsc hxi hxj
    have hcS : c ∈ B.span := hB.1 ▸ hcA.1
    set γ := B.coords ⟨c, hcS⟩ with hγ
    have hγc : B.vec γ = c := B.vec_coords _
    have hγ0 : γ 0 = 0 :=
      B.coords_zero_of_mem hB.2.1 h.ord hB.2.2 (hB.1 ▸ h.disj) ⟨c, hcS⟩ hcA.2
    suffices hγz : γ = 0 by
      have : c = 1 := by rw [← hγc, hγz, B.vec_zero]
      rw [hc] at this
      have h1 := mul_inv_eq_one.mp this
      exact mul_inv_eq_iff_eq_mul.mp h1
    funext k
    by_cases hk : k = 0
    · rw [hk, hγ0]; rfl
    obtain ⟨t, ⟨hts, ht0, d₀, hd₀N, hd₀A⟩, htk⟩ := hd3 i j k hi hj hk hji
    obtain ⟨d, hdN, hdP, hdA, hdb⟩ :=
      hP.exists_sign_lift h B hB ⟨hts, ht0, d₀, hd₀N, hd₀A⟩
    have hcen' : ∀ {u : G}, u ∈ P₁ → Commute c u := fun hu => hcen hcA hu
    have hdconj : d * c * d⁻¹ = (d * xk i * d⁻¹) * (d * xk j * d⁻¹) * (d * xk i * d⁻¹)⁻¹ *
        (d * xk j * d⁻¹)⁻¹ := by rw [hc]; group
    have hvec := acts_vec_sign B hB.1 hdN hdA γ
    rw [hγc] at hvec
    have hfix1 : d * c * d⁻¹ = c → t k * γ k = γ k := fun hd1 => by
      have := congrFun (B.vec_injective (hγc.trans (hd1.symm.trans hvec))) k
      exact this.symm
    have hfix2 : d * c * d⁻¹ = c⁻¹ → t k * γ k = -γ k := fun hd1 => by
      have h1 : c⁻¹ = B.vec (-γ) := by rw [B.vec_neg', hγc]
      have := congrFun (B.vec_injective (h1.symm.trans (hd1.symm.trans hvec))) k
      rw [Pi.neg_apply] at this
      exact this.symm
    have hcomm1 := hcen' hxi
    have hcomm2 := hcen' hxj
    have key1 : ∀ a : ZMod 3, a = 1 * 1 * a := by decide
    have key2 : ∀ a : ZMod 3, -a = 1 * -1 * a := by decide
    have key3 : ∀ a : ZMod 3, -a = -1 * 1 * a := by decide
    have key4 : ∀ a : ZMod 3, a = -1 * -1 * a := by decide
    have hkey : t k * γ k = t i * t j * γ k := by
      rcases hts i with hi1 | hi1 <;> rcases hts j with hj1 | hj1
      · obtain ⟨a, ha, hda⟩ := heig hdN hdP ht0 hdA hi (hxkB i hi) (htb_pos hi hi1)
        obtain ⟨a', ha', hda'⟩ := heig hdN hdP ht0 hdA hj (hxkB j hj) (htb_pos hj hj1)
        have hdc : d * c * d⁻¹ = c := by
          rw [hdconj, hda, hda', comm_mul_central_eq (hcen ha hxi) (hcen ha (hP.E_le ha'.1))
            (hcen ha hxj) (hcen ha' hxj) (hcen ha' hxi)]
        rw [hfix1 hdc, hi1, hj1]
        exact key1 _
      · obtain ⟨a, ha, hda⟩ := heig hdN hdP ht0 hdA hi (hxkB i hi) (htb_pos hi hi1)
        obtain ⟨a', ha', hda'⟩ := heig hdN hdP ht0 hdA hj (B₂.inv_mem (hxkB j hj))
          (htb_neg hj hj1)
        have hdc : d * c * d⁻¹ = c⁻¹ := by
          rw [hdconj, hda, hda', comm_mul_central_eq (hcen ha hxi) (hcen ha (hP.E_le ha'.1))
            (hcen ha (P₁.inv_mem hxj)) (hcen ha' (P₁.inv_mem hxj)) (hcen ha' hxi),
            comm_inv_right_eq hcomm2]
        rw [hfix2 hdc, hi1, hj1]
        exact key2 _
      · obtain ⟨a, ha, hda⟩ := heig hdN hdP ht0 hdA hi (B₂.inv_mem (hxkB i hi))
          (htb_neg hi hi1)
        obtain ⟨a', ha', hda'⟩ := heig hdN hdP ht0 hdA hj (hxkB j hj) (htb_pos hj hj1)
        have hdc : d * c * d⁻¹ = c⁻¹ := by
          rw [hdconj, hda, hda', comm_mul_central_eq (hcen ha (P₁.inv_mem hxi))
            (hcen ha (hP.E_le ha'.1)) (hcen ha hxj) (hcen ha' hxj) (hcen ha' (P₁.inv_mem hxi)),
            comm_inv_left_eq hcomm1]
        rw [hfix2 hdc, hi1, hj1]
        exact key3 _
      · obtain ⟨a, ha, hda⟩ := heig hdN hdP ht0 hdA hi (B₂.inv_mem (hxkB i hi))
          (htb_neg hi hi1)
        obtain ⟨a', ha', hda'⟩ := heig hdN hdP ht0 hdA hj (B₂.inv_mem (hxkB j hj))
          (htb_neg hj hj1)
        have hdc : d * c * d⁻¹ = c := by
          rw [hdconj, hda, hda', comm_mul_central_eq (hcen ha (P₁.inv_mem hxi))
            (hcen ha (hP.E_le ha'.1)) (hcen ha (P₁.inv_mem hxj)) (hcen ha' (P₁.inv_mem hxj))
            (hcen ha' (P₁.inv_mem hxi))]
          rw [comm_inv_left_eq (u := xk i) (v := (xk j)⁻¹) (by
            rw [comm_inv_right_eq hcomm2]; exact hcomm1.inv_left), comm_inv_right_eq hcomm2,
            inv_inv]
        rw [hfix1 hdc, hi1, hj1]
        exact key4 _
    have hne : t k - t i * t j ≠ 0 := sub_ne_zero.mpr htk
    have : (t k - t i * t j) * γ k = 0 := by rw [sub_mul, hkey, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne
  have hstep : ∀ i : Fin (n + 1), i ≠ 0 → ∀ y ∈ B₂, xk i * y = y * xk i := fun i hi =>
    hP.forall_of_gen_B2 h B hB hB₂P hB₂E (p := fun y => xk i * y = y * xk i)
      (fun y y' _ _ h1 h2 => by rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc])
      (fun y _ h1 => by
        calc xk i * y⁻¹ = y⁻¹ * (y * xk i) * y⁻¹ := by group
          _ = y⁻¹ * (xk i * y) * y⁻¹ := by rw [h1]
          _ = y⁻¹ * xk i := by group)
      (fun a ha => (hcen ha (hB₂P (hxkB i hi))).eq.symm)
      (fun j hj => ⟨xk j, hxkB j hj, hxkb j hj, hgen i hi j hj⟩)
  intro x hx
  exact hP.forall_of_gen_B2 h B hB hB₂P hB₂E (p := fun x => ∀ y ∈ B₂, x * y = y * x)
    (fun x x' _ _ h1 h2 y hy => by rw [mul_assoc, h2 y hy, ← mul_assoc, h1 y hy, mul_assoc])
    (fun x _ h1 y hy => by
      calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * y) * x⁻¹ := by rw [h1 y hy]
        _ = y * x⁻¹ := by group)
    (fun a ha y hy => (hcen ha (hB₂P hy)).eq)
    (fun i hi => ⟨xk i, hxkB i hi, hxkb i hi, hstep i hi⟩) x hx

end TransvP1

namespace TransvP1

variable [Finite G] {b₀ : G} {K E P₁ : Subgroup G}

theorem B2_unique (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁)
    (hcomm : ∀ x ∈ P₁, ∀ y ∈ P₁, x * y * x⁻¹ * y⁻¹ ∈ E ⊓ K) {B₂ B' : Subgroup G}
    (hB₂P : B₂ ≤ P₁) (hAB₂ : E ⊓ K ≤ B₂) (hB₂E : ∀ x ∈ B₂, x ∈ E → x ∈ E ⊓ K)
    (hcos : ∀ x ∈ P₁, ∃ j : ℤ, x * b₀ ^ j ∈ B₂) (hab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x)
    (hA9 : 9 ≤ Nat.card ↥(E ⊓ K)) (hB'P : B' ≤ P₁) (hab' : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x)
    (hcard : Nat.card B₂ ≤ Nat.card B') : B' ≤ B₂ := by
  have hb3 : b₀ ^ 3 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one b₀
  have hb3z : ∀ m : ℤ, b₀ ^ (3 * m) = 1 := fun m => by
    rw [zpow_mul, zpow_ofNat, hb3, one_zpow]
  have hb0P : b₀ ∈ P₁ := hP.E_le h.b0_mem
  have hnorm : ∀ {p b : G}, p ∈ P₁ → b ∈ B₂ → p * b * p⁻¹ ∈ B₂ := fun {p b} hp hb => by
    have h1 := hAB₂ (hcomm p hp b (hB₂P hb))
    have := B₂.mul_mem h1 hb
    rwa [show p * b * p⁻¹ * b⁻¹ * b = p * b * p⁻¹ by group] at this
  by_contra hne
  obtain ⟨y, hyB', hyB₂⟩ := Set.not_subset.mp hne
  obtain ⟨j, hj⟩ := hcos y (hB'P hyB')
  have hj3 : ¬ (3 : ℤ) ∣ j := by
    rintro ⟨m, rfl⟩
    apply hyB₂
    rwa [hb3z, mul_one] at hj
  have hinter : ∀ z ∈ B', z ∈ B₂ → z ∈ E ⊓ K := by
    intro z hzB' hzB₂
    have h1 : y * z = z * y := hab' y hyB' z hzB'
    have h2 : (y * b₀ ^ j) * z = z * (y * b₀ ^ j) := hab _ hj z hzB₂
    have h3 : b₀ ^ j * z = z * b₀ ^ j := by
      have : y * (b₀ ^ j * z) = y * (z * b₀ ^ j) := by
        rw [← mul_assoc, h2, ← mul_assoc, ← mul_assoc, h1, mul_assoc]
      exact mul_left_cancel this
    have hgen : b₀ ∈ Subgroup.zpowers (b₀ ^ j) := by
      have hcop : IsCoprime j 3 := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        have h3 : Int.gcd j 3 = 1 ∨ Int.gcd j 3 = 3 := by
          have hd : Int.gcd j 3 ∣ 3 := by exact_mod_cast Int.gcd_dvd_right j 3
          exact (Nat.dvd_prime Nat.prime_three).mp hd
        rcases h3 with h3 | h3
        · exact h3
        · exfalso; apply hj3
          have := Int.gcd_dvd_left j 3
          rw [h3] at this
          exact_mod_cast this
      obtain ⟨u, v, huv⟩ := hcop
      refine Subgroup.mem_zpowers_iff.mpr ⟨u, ?_⟩
      have : b₀ ^ (u * j + v * 3) = b₀ := by rw [huv, zpow_one]
      rw [zpow_add, mul_comm v 3, hb3z, mul_one] at this
      rw [← zpow_mul, mul_comm j u]
      exact this
    have hzb : b₀ * z = z * b₀ := by
      obtain ⟨u, hu⟩ := Subgroup.mem_zpowers_iff.mp hgen
      have : (b₀ ^ j) ^ u * z = z * (b₀ ^ j) ^ u := ((Commute.zpow_left h3 u).eq)
      rwa [hu] at this
    have hzE : z ∈ E := hP.mem_E h (hB₂P hzB₂) (by
      rw [tb, ← hzb, mul_inv_cancel_right, inv_mul_cancel])
    exact hB₂E z hzB₂ hzE
  have hrel : B₂.relIndex P₁ ≤ 3 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    let f : Fin 3 → ↥P₁ ⧸ B₂.subgroupOf P₁ := fun m =>
      QuotientGroup.mk ⟨b₀ ^ (m : ℕ), P₁.pow_mem hb0P _⟩
    have hf : Function.Surjective f := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨i, hi⟩ := hcos x x.2
        refine ⟨⟨((-i) % 3).toNat, by omega⟩, ?_⟩
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        have hpow : b₀ ^ ((((-i) % 3).toNat : ℕ) : ℤ) = b₀ ^ (-i) := by
          rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
          have := zpow_mod_orderOf b₀ (-i)
          rwa [h.ord] at this
        have h2 := hnorm (P₁.zpow_mem hb0P i) hi
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← zpow_natCast, hpow]
        rwa [show b₀ ^ i * (x * b₀ ^ i) * (b₀ ^ i)⁻¹ = (b₀ ^ (-i))⁻¹ * x by group] at h2
    have := Nat.card_le_card_of_surjective f hf
    simpa using this
  have hrel' : B₂.relIndex B' ≤ 3 := le_trans (Subgroup.relIndex_le_of_le_right hB'P
    (Subgroup.index_ne_zero_of_finite (H := B₂.subgroupOf P₁))) hrel
  have hcardB' : Nat.card B' ≤ 3 * Nat.card ↥(E ⊓ K) := by
    rw [← Subgroup.relIndex_mul_card B₂ B']
    refine Nat.mul_le_mul hrel' (Nat.card_le_card_of_injective
      (fun z => (⟨z, hinter z z.2.2 z.2.1⟩ : ↥(E ⊓ K))) fun a b hab => Subtype.ext ?_)
    exact congrArg (fun z : ↥(E ⊓ K) => (z : G)) hab
  have hcardB₂ : Nat.card ↥(E ⊓ K) * Nat.card ↥(E ⊓ K) ≤ Nat.card B₂ := by
    let f : ↥B₂ →* ↥(E ⊓ K) := (transvBeta b₀ K E).comp
      (Subgroup.inclusion (hB₂P.trans hP.le))
    have hsurj : Function.Surjective f := by
      rintro ⟨a, ha⟩
      obtain ⟨x, hx, hxa⟩ := hP.surj a ha
      obtain ⟨i, hi⟩ := hcos x hx
      refine ⟨⟨_, hi⟩, Subtype.ext ?_⟩
      show tb b₀ (x * b₀ ^ i) = a
      rw [tb_mul (hP.le hx) (hP.le (hP.E_le (E.zpow_mem h.b0_mem i))),
        tb_eq_one_of_mem_E h (E.zpow_mem h.b0_mem i), mul_one, hxa]
    have hker : Nat.card ↥(E ⊓ K) ≤ Nat.card f.ker :=
      Nat.card_le_card_of_injective (fun a => (⟨⟨a, hAB₂ a.2⟩, by
        show transvBeta b₀ K E _ = 1
        exact Subtype.ext (tb_eq_one_of_mem_E h a.2.1)⟩ : f.ker))
        fun a b hab => Subtype.ext (by simpa using congrArg (fun z : f.ker => ((z : ↥B₂) : G)) hab)
    have := Subgroup.card_ker_mul_card_range f
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top] at this
    rw [← this]
    exact Nat.mul_le_mul_right _ hker
  have h1 : Nat.card ↥(E ⊓ K) * Nat.card ↥(E ⊓ K) ≤ 3 * Nat.card ↥(E ⊓ K) :=
    (hcardB₂.trans hcard).trans hcardB'
  have := Nat.le_of_mul_le_mul_right h1 (by omega)
  omega

end TransvP1

namespace TransvP1

variable [Finite G] {b₀ : G} {K E P₁ : Subgroup G}

theorem B2_normalizer (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁)
    (hcomm : ∀ x ∈ P₁, ∀ y ∈ P₁, x * y * x⁻¹ * y⁻¹ ∈ E ⊓ K) {B₂ : Subgroup G}
    (hB₂P : B₂ ≤ P₁) (hAB₂ : E ⊓ K ≤ B₂) (hB₂E : ∀ x ∈ B₂, x ∈ E → x ∈ E ⊓ K)
    (hcos : ∀ x ∈ P₁, ∃ j : ℤ, x * b₀ ^ j ∈ B₂) (hab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x)
    (hA9 : 9 ≤ Nat.card ↥(E ⊓ K)) {m : G} (hm : m ∈ Subgroup.normalizer (P₁ : Set G)) :
    ∀ x ∈ B₂, m * x * m⁻¹ ∈ B₂ := by
  have hle := hP.B2_unique h hcomm hB₂P hAB₂ hB₂E hcos hab hA9
    (B' := B₂.map (MulAut.conj m).toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hm x).mp (hB₂P hx))
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show m * x * m⁻¹ * (m * y * m⁻¹) = m * (x * y) * m⁻¹ by group, hab x hx y hy]
      group)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj m).injective])
  exact fun x hx => hle ⟨x, hx, rfl⟩

end TransvP1

end CFSG.StandardType.FrameRoute.FS81

end
