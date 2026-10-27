module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall6Y
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallOmega

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.CGT.PushingUpLit.SolK Equiv Equiv.Perm
open CFSG.RankThree.PartTwo.Sec19.SolEven.Comb (barPar)

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6}

@[expose] noncomputable def piv (D : C.PiData) (k : G) (hk : k ∈ C.K) : permBar 6 :=
  Multiplicative.toAdd (D.π ⟨k, hk⟩)

theorem piv_mul (D : C.PiData) {k k' : G} (hk : k ∈ C.K) (hk' : k' ∈ C.K) :
    piv D (k * k') (C.K.mul_mem hk hk') = piv D k hk + piv D k' hk' := by
  unfold piv
  rw [← toAdd_mul, ← map_mul]
  rfl

theorem piv_inv (D : C.PiData) {k : G} (hk : k ∈ C.K) :
    piv D k⁻¹ (C.K.inv_mem hk) = piv D k hk := by
  have h := piv_mul D (C.K.inv_mem hk) hk
  have e : piv D (k⁻¹ * k) (C.K.mul_mem (C.K.inv_mem hk) hk) = 0 := by
    unfold piv
    have : (⟨k⁻¹ * k, C.K.mul_mem (C.K.inv_mem hk) hk⟩ : ↥C.K) = 1 := Subtype.ext (by simp)
    rw [this, map_one, toAdd_one]
  rw [e] at h
  calc piv D k⁻¹ _ = piv D k⁻¹ _ + (piv D k hk + piv D k hk) := by
        rw [permBar_add_self, add_zero]
    _ = (piv D k⁻¹ _ + piv D k hk) + piv D k hk := by rw [add_assoc]
    _ = piv D k hk := by rw [← h, zero_add]

theorem piv_conj (D : C.PiData) {m : G} (hm : m ∈ M) {k : G} (hk : k ∈ C.K)
    (hk' : m * k * m⁻¹ ∈ C.K) :
    piv D (m * k * m⁻¹) hk' = barAct (C.θ ⟨m, hm⟩) (piv D k hk) :=
  D.equivar ⟨m, hm⟩ ⟨k, hk⟩ ⟨_, hk'⟩ rfl

theorem piv_eq_zero_iff (D : C.PiData) {k : G} (hk : k ∈ C.K) :
    piv D k hk = 0 ↔ k ∈ Subgroup.centralizer (X : Set G) := by
  unfold piv
  rw [← D.ker ⟨k, hk⟩, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff]

theorem inv_mul_mem_K {x s : G} (hx : x ∈ M) (hs : s ∈ M) (hθ : C.θ ⟨x, hx⟩ = C.θ ⟨s, hs⟩) :
    x⁻¹ * s ∈ C.K := by
  refine C.mem_K.2 ⟨M.mul_mem (M.inv_mem hx) hs, ?_⟩
  have e : (⟨x⁻¹ * s, M.mul_mem (M.inv_mem hx) hs⟩ : ↥M) = (⟨x, hx⟩ : ↥M)⁻¹ * ⟨s, hs⟩ := rfl
  rw [e, map_mul, map_inv, hθ, inv_mul_cancel]

theorem parK_lift_eq (D : C.PiData)
    (hA : ∀ y (hy : y ∈ CFSG.Open.pCoreOf 2 X), parK D ⟨y, Y_le_K C hy⟩ = 0)
    {x x' s : G} (hx : x ∈ X) (hx' : x' ∈ X) (hθ : C.θ ⟨x, C.S.le hx⟩ = C.θ ⟨x', C.S.le hx'⟩)
    (h1 : x⁻¹ * s ∈ C.K) (h2 : x'⁻¹ * s ∈ C.K) :
    parK D ⟨x⁻¹ * s, h1⟩ = parK D ⟨x'⁻¹ * s, h2⟩ := by
  have hd : x'⁻¹ * x ∈ C.K := inv_mul_mem_K (C.S.le hx') (C.S.le hx) hθ.symm
  have hdY : x'⁻¹ * x ∈ CFSG.Open.pCoreOf 2 X :=
    mem_Y_of_mem_K C (X.mul_mem (X.inv_mem hx') hx) hd
  have e : (⟨x'⁻¹ * s, h2⟩ : ↥C.K) = ⟨x'⁻¹ * x, hd⟩ * ⟨x⁻¹ * s, h1⟩ :=
    Subtype.ext (by simp [mul_assoc])
  rw [e, parK_mul, hA _ hdY, zero_add]

theorem parK_conj_lift (D : C.PiData) {z x s : G} (hz : z ∈ M) (h1 : x⁻¹ * s ∈ C.K)
    (h2 : (z * x * z⁻¹)⁻¹ * (z * s * z⁻¹) ∈ C.K) :
    parK D ⟨(z * x * z⁻¹)⁻¹ * (z * s * z⁻¹), h2⟩ = parK D ⟨x⁻¹ * s, h1⟩ := by
  have e : (z * x * z⁻¹)⁻¹ * (z * s * z⁻¹) = z * (x⁻¹ * s) * z⁻¹ := by group
  exact parK_conj D ⟨z, hz⟩ ⟨x⁻¹ * s, h1⟩ ⟨_, h2⟩ e

theorem parK_mul_lift (D : C.PiData) {x₁ x₂ s₁ s₂ : G} (hx₂ : x₂ ∈ M) (h1 : x₁⁻¹ * s₁ ∈ C.K)
    (h2 : x₂⁻¹ * s₂ ∈ C.K) (h12 : (x₁ * x₂)⁻¹ * (s₁ * s₂) ∈ C.K) :
    parK D ⟨(x₁ * x₂)⁻¹ * (s₁ * s₂), h12⟩ = parK D ⟨x₁⁻¹ * s₁, h1⟩ + parK D ⟨x₂⁻¹ * s₂, h2⟩ := by
  have hc : x₂⁻¹ * (x₁⁻¹ * s₁) * x₂⁻¹⁻¹ ∈ C.K := RSmall.K_normalized C (M.inv_mem hx₂) h1
  have e : (⟨(x₁ * x₂)⁻¹ * (s₁ * s₂), h12⟩ : ↥C.K) =
      ⟨x₂⁻¹ * (x₁⁻¹ * s₁) * x₂⁻¹⁻¹, hc⟩ * ⟨x₂⁻¹ * s₂, h2⟩ := Subtype.ext (by simp; group)
  rw [e, parK_mul, parK_conj D ⟨x₂⁻¹, M.inv_mem hx₂⟩ ⟨x₁⁻¹ * s₁, h1⟩ ⟨_, hc⟩ rfl]

theorem piv_sq (D : C.PiData) {x s : G} (hx : x ∈ M) (hs : s ∈ M) (hss : s * s = 1)
    (hθ : C.θ ⟨x, hx⟩ = C.θ ⟨s, hs⟩) (hσ : C.θ ⟨s, hs⟩ * C.θ ⟨s, hs⟩ = 1)
    (hd : x⁻¹ * s ∈ C.K) (hxx : x * x ∈ C.K) :
    piv D (x * x) hxx = barAct (C.θ ⟨s, hs⟩) (piv D (x⁻¹ * s) hd) + piv D (x⁻¹ * s) hd := by
  set d := x⁻¹ * s with hd'
  have hdi : d⁻¹ ∈ C.K := C.K.inv_mem hd
  have hc : x⁻¹ * d⁻¹ * x⁻¹⁻¹ ∈ C.K := RSmall.K_normalized C (M.inv_mem hx) hdi
  have e : x * x = d⁻¹ * (x⁻¹ * d⁻¹ * x⁻¹⁻¹) := by
    have hs' : s = x * d := by rw [hd']; group
    have h1 : x * d * (x * d) = 1 := by rw [← hs']; exact hss
    have hinv : x * d = (x * d)⁻¹ := eq_inv_of_mul_eq_one_left h1
    calc x * x = x * d * d⁻¹ * x := by group
      _ = (x * d)⁻¹ * d⁻¹ * x := by rw [← hinv]
      _ = d⁻¹ * (x⁻¹ * d⁻¹ * x⁻¹⁻¹) := by group
  have hθi : C.θ ⟨x⁻¹, M.inv_mem hx⟩ = C.θ ⟨s, hs⟩ := by
    have : (⟨x⁻¹, M.inv_mem hx⟩ : ↥M) = (⟨x, hx⟩ : ↥M)⁻¹ := rfl
    rw [this, map_inv, hθ, inv_eq_of_mul_eq_one_left hσ]
  have h2 : piv D (x * x) hxx = piv D (d⁻¹ * (x⁻¹ * d⁻¹ * x⁻¹⁻¹)) (C.K.mul_mem hdi hc) := by
    unfold piv
    congr 2
    exact Subtype.ext e
  rw [h2, piv_mul D hdi hc, piv_conj D (M.inv_mem hx) hdi hc, hθi, piv_inv D hd, add_comm]

theorem piv_comm (D : C.PiData) {x₁ x₂ s₁ s₂ : G} (hx₁ : x₁ ∈ M) (hx₂ : x₂ ∈ M) (hs₁ : s₁ ∈ M)
    (hs₂ : s₂ ∈ M) (hcomm : s₁ * s₂ = s₂ * s₁)
    (hθ₁ : C.θ ⟨x₁, hx₁⟩ = C.θ ⟨s₁, hs₁⟩) (hθ₂ : C.θ ⟨x₂, hx₂⟩ = C.θ ⟨s₂, hs₂⟩)
    (hσ₁ : C.θ ⟨s₁, hs₁⟩ * C.θ ⟨s₁, hs₁⟩ = 1) (hσ₂ : C.θ ⟨s₂, hs₂⟩ * C.θ ⟨s₂, hs₂⟩ = 1)
    (hd₁ : x₁⁻¹ * s₁ ∈ C.K) (hd₂ : x₂⁻¹ * s₂ ∈ C.K) (hk : (x₂ * x₁)⁻¹ * (x₁ * x₂) ∈ C.K) :
    piv D ((x₂ * x₁)⁻¹ * (x₁ * x₂)) hk =
      (barAct (C.θ ⟨s₁, hs₁⟩) (piv D (x₂⁻¹ * s₂) hd₂) + piv D (x₂⁻¹ * s₂) hd₂) +
      (barAct (C.θ ⟨s₂, hs₂⟩) (piv D (x₁⁻¹ * s₁) hd₁) + piv D (x₁⁻¹ * s₁) hd₁) := by
  set d₁ := x₁⁻¹ * s₁ with hd₁'
  set d₂ := x₂⁻¹ * s₂ with hd₂'
  have hθi : ∀ {x s : G} (hx : x ∈ M) (hs : s ∈ M), C.θ ⟨x, hx⟩ = C.θ ⟨s, hs⟩ →
      C.θ ⟨s, hs⟩ * C.θ ⟨s, hs⟩ = 1 → C.θ ⟨x⁻¹, M.inv_mem hx⟩ = C.θ ⟨s, hs⟩ := by
    intro x s hx hs hθ hσ
    have : (⟨x⁻¹, M.inv_mem hx⟩ : ↥M) = (⟨x, hx⟩ : ↥M)⁻¹ := rfl
    rw [this, map_inv, hθ, inv_eq_of_mul_eq_one_left hσ]
  have ha : x₁⁻¹ * d₂ * x₁⁻¹⁻¹ ∈ C.K := RSmall.K_normalized C (M.inv_mem hx₁) hd₂
  have hb : x₂⁻¹ * d₁⁻¹ * x₂⁻¹⁻¹ ∈ C.K := RSmall.K_normalized C (M.inv_mem hx₂) (C.K.inv_mem hd₁)
  have e : (x₂ * x₁)⁻¹ * (x₁ * x₂) =
      x₁⁻¹ * d₂ * x₁⁻¹⁻¹ * (d₁ * (d₂⁻¹ * (x₂⁻¹ * d₁⁻¹ * x₂⁻¹⁻¹))) := by
    have h1 : s₁ = x₁ * d₁ := by rw [hd₁']; group
    have h2 : s₂ = x₂ * d₂ := by rw [hd₂']; group
    have h3 : x₁ * d₁ * (x₂ * d₂) = x₂ * d₂ * (x₁ * d₁) := by rw [← h1, ← h2]; exact hcomm
    calc (x₂ * x₁)⁻¹ * (x₁ * x₂)
        = x₁⁻¹ * x₂⁻¹ * (x₁ * d₁ * (x₂ * d₂)) * d₂⁻¹ * x₂⁻¹ * d₁⁻¹ * x₂ := by group
      _ = x₁⁻¹ * x₂⁻¹ * (x₂ * d₂ * (x₁ * d₁)) * d₂⁻¹ * x₂⁻¹ * d₁⁻¹ * x₂ := by rw [h3]
      _ = x₁⁻¹ * d₂ * x₁⁻¹⁻¹ * (d₁ * (d₂⁻¹ * (x₂⁻¹ * d₁⁻¹ * x₂⁻¹⁻¹))) := by group
  have hk' : x₁⁻¹ * d₂ * x₁⁻¹⁻¹ * (d₁ * (d₂⁻¹ * (x₂⁻¹ * d₁⁻¹ * x₂⁻¹⁻¹))) ∈ C.K :=
    C.K.mul_mem ha (C.K.mul_mem hd₁ (C.K.mul_mem (C.K.inv_mem hd₂) hb))
  have h2 : piv D ((x₂ * x₁)⁻¹ * (x₁ * x₂)) hk = piv D _ hk' := by
    unfold piv
    congr 2
    exact Subtype.ext e
  rw [h2, piv_mul D ha (C.K.mul_mem hd₁ (C.K.mul_mem (C.K.inv_mem hd₂) hb)),
    piv_mul D hd₁ (C.K.mul_mem (C.K.inv_mem hd₂) hb), piv_mul D (C.K.inv_mem hd₂) hb,
    piv_conj D (M.inv_mem hx₁) hd₂ ha, piv_conj D (M.inv_mem hx₂) (C.K.inv_mem hd₁) hb,
    hθi hx₁ hs₁ hθ₁ hσ₁, hθi hx₂ hs₂ hθ₂ hσ₂, piv_inv D hd₁, piv_inv D hd₂]
  abel

theorem exists_involution_of_lift (D : C.PiData)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    (hRel : ∀ r ∈ Rc X, r * r = 1) {t : G} (htM : t ∈ M) (htt : t * t = 1) {x : G} (hx : x ∈ X)
    (hxt : C.θ ⟨x, C.S.le hx⟩ = C.θ ⟨t, htM⟩)
    (hY : ∃ y, ∃ hy : y ∈ CFSG.Open.pCoreOf 2 X,
      D.π ⟨y, Y_le_K C hy⟩ = D.π ⟨x⁻¹ * t, inv_mul_mem_K (C.S.le hx) htM hxt⟩) :
    ∃ a, ∃ ha : a ∈ X, ∃ c ∈ Rc X, t = a * c ∧ a * a = 1 ∧
      C.θ ⟨a, C.S.le ha⟩ = C.θ ⟨t, htM⟩ ∧ ∀ z ∈ X, (z * t = t * z ↔ z * a = a * z) := by
  obtain ⟨y, hy, hπy⟩ := hY
  have hk := inv_mul_mem_K (C.S.le hx) htM hxt
  have hyX : y ∈ X := pCoreOf_le_self X hy
  set a := x * y with ha'
  have ha : a ∈ X := X.mul_mem hx hyX
  set c := a⁻¹ * t with hc'
  have hcK : c ∈ C.K := by
    have e : c = y⁻¹ * (x⁻¹ * t) := by rw [hc', ha']; group
    rw [e]
    exact C.K.mul_mem (C.K.inv_mem (Y_le_K C hy)) hk
  have hcX : c ∈ Subgroup.centralizer (X : Set G) := by
    rw [← (D.ker ⟨c, hcK⟩)]
    have e : (⟨c, hcK⟩ : ↥C.K) = (⟨y, Y_le_K C hy⟩ : ↥C.K)⁻¹ * ⟨x⁻¹ * t, hk⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc', ha']; group)
    rw [e, map_mul, map_inv, hπy, inv_mul_cancel]
  have hta : t = a * c := by rw [hc']; group
  have hac : a * c = c * a := Subgroup.mem_centralizer_iff.1 hcX a ha
  have haacc : a * a * (c * c) = 1 := by
    calc a * a * (c * c) = a * (a * c) * c := by group
      _ = a * (c * a) * c := by rw [hac]
      _ = (a * c) * (a * c) := by group
      _ = 1 := by rw [← hta]; exact htt
  have hcc : c * c = (a * a)⁻¹ := eq_inv_of_mul_eq_one_right haacc
  have hccY : c * c ∈ CFSG.Open.pCoreOf 2 X := by
    apply mem_Y_of_mem_centralizer C (by rw [hcc]; exact X.inv_mem (X.mul_mem ha ha))
    exact (Subgroup.centralizer (X : Set G)).mul_mem hcX hcX
  have hcR : c ∈ Rc X := by
    obtain ⟨j, hj⟩ := isPGroup_pCoreOf' X ⟨c * c, hccY⟩
    have hj' : (c * c) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    have hj'' : c ^ (2 ^ (j + 1)) = 1 := by
      have e : c ^ (2 ^ (j + 1)) = (c * c) ^ (2 ^ j) := by
        rw [← sq, ← pow_mul, pow_succ']
      rw [e, hj']
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hj'')
    have h2 : IsPGroup 2 (Subgroup.zpowers c) := IsPGroup.of_card (n := i)
      (by rw [Nat.card_zpowers, hi])
    exact hRsyl _ h2 (Subgroup.zpowers_le.2 hcX) (Subgroup.mem_zpowers c)
  have hcc1 : c * c = 1 := hRel c hcR
  have haa : a * a = 1 := by
    have := haacc
    rwa [hcc1, mul_one] at this
  refine ⟨a, ha, c, hcR, hta, haa, ?_, ?_⟩
  · have hcQ : c ∈ C.K := hcK
    have hθc : C.θ ⟨c, C.K_le hcK⟩ = 1 := (C.mem_K.1 hcQ).2
    have e : (⟨t, htM⟩ : ↥M) = ⟨a, C.S.le ha⟩ * ⟨c, C.K_le hcK⟩ := Subtype.ext hta
    rw [e, map_mul, hθc, mul_one]
  · intro z hz
    have hzc : z * c = c * z := Subgroup.mem_centralizer_iff.1 hcX z hz
    rw [hta]
    constructor
    · intro h
      apply mul_right_cancel (b := c)
      calc z * a * c = z * (a * c) := by group
        _ = a * c * z := h
        _ = a * (c * z) := by group
        _ = a * (z * c) := by rw [hzc]
        _ = a * z * c := by group
    · intro h
      calc z * (a * c) = z * a * c := by group
        _ = a * z * c := by rw [h]
        _ = a * (z * c) := by group
        _ = a * (c * z) := by rw [hzc]
        _ = a * c * z := by group

theorem comm_conj_of_mul_self (D : C.PiData)
    (hYel : ∀ y ∈ CFSG.Open.pCoreOf 2 X, y * y = 1)
    {a r : G} (ha : a ∈ X) (hr : r ∈ X) (haa : a * a = 1) (hr3 : r ^ 3 = 1)
    {σ σ' ρ : Perm (Fin 6)} (hθa : C.θ ⟨a, C.S.le ha⟩ = σ) (hθr : C.θ ⟨r, C.S.le hr⟩ = ρ)
    (h1 : ρ * σ * ρ⁻¹ = σ') (h2 : ρ * σ' * ρ⁻¹ = σ * σ') (h3 : σ * σ' = σ' * σ)
    (hB : ∀ v : permBar 6, barAct σ v = v → barAct σ' v = v → barAct ρ v = v) :
    a * (r * a * r⁻¹) = (r * a * r⁻¹) * a := by
  set b := r * a * r⁻¹ with hb'
  set b' := r * b * r⁻¹ with hb''
  have hbX : b ∈ X := X.mul_mem (X.mul_mem hr ha) (X.inv_mem hr)
  have hb'X : b' ∈ X := X.mul_mem (X.mul_mem hr hbX) (X.inv_mem hr)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbb : b * b = 1 := by
    calc b * b = r * (a * a) * r⁻¹ := by rw [hb']; group
      _ = 1 := by rw [haa]; group
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hb'b' : b' * b' = 1 := by
    have : b' * b' = r * (b * b) * r⁻¹ := by rw [hb'']; group
    rw [this, hbb]; group
  have hb'i : b'⁻¹ = b' := inv_eq_of_mul_eq_one_right hb'b'
  have hrb' : r * b' * r⁻¹ = a := by
    have h3' : r * r * r = 1 := by rw [← pow_three', hr3]
    calc r * b' * r⁻¹ = (r * r * r) * a * (r * r * r)⁻¹ := by rw [hb'', hb']; group
      _ = a := by rw [h3']; group
  have hθ : ∀ {g : G} (hg : g ∈ X), C.θ ⟨g, C.S.le hg⟩ = C.θ ⟨g, C.S.le hg⟩ := fun _ => rfl
  have hθb : C.θ ⟨b, C.S.le hbX⟩ = σ' := by
    have e : (⟨b, C.S.le hbX⟩ : ↥M) = ⟨r, C.S.le hr⟩ * ⟨a, C.S.le ha⟩ * ⟨r, C.S.le hr⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hθa, hθr, h1]
  have hθb' : C.θ ⟨b', C.S.le hb'X⟩ = σ * σ' := by
    have e : (⟨b', C.S.le hb'X⟩ : ↥M) = ⟨r, C.S.le hr⟩ * ⟨b, C.S.le hbX⟩ * ⟨r, C.S.le hr⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hθb, hθr, h2]
  have hσσ : σ * σ = 1 := by
    have e : (⟨a, C.S.le ha⟩ : ↥M) * ⟨a, C.S.le ha⟩ = 1 := Subtype.ext haa
    have := congrArg C.θ e
    rwa [map_mul, map_one, hθa] at this
  have hσ'σ' : σ' * σ' = 1 := by
    rw [← h1]
    calc ρ * σ * ρ⁻¹ * (ρ * σ * ρ⁻¹) = ρ * (σ * σ) * ρ⁻¹ := by group
      _ = 1 := by rw [hσσ]; group
  have hY : ∀ {g : G} (hg : g ∈ X), C.θ ⟨g, C.S.le hg⟩ = 1 → g ∈ CFSG.Open.pCoreOf 2 X :=
    fun hg h => mem_Y_of_mem_K C hg (C.mem_K.2 ⟨C.S.le hg, h⟩)
  set v := a * b * a * b with hv'
  have hvX : v ∈ X := X.mul_mem (X.mul_mem (X.mul_mem ha hbX) ha) hbX
  have hvY : v ∈ CFSG.Open.pCoreOf 2 X := by
    apply hY hvX
    have e : (⟨v, C.S.le hvX⟩ : ↥M) =
        ⟨a, C.S.le ha⟩ * ⟨b, C.S.le hbX⟩ * ⟨a, C.S.le ha⟩ * ⟨b, C.S.le hbX⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, hθa, hθb]
    calc σ * σ' * σ * σ' = σ * (σ' * σ) * σ' := by group
      _ = σ * (σ * σ') * σ' := by rw [h3]
      _ = (σ * σ) * (σ' * σ') := by group
      _ = 1 := by rw [hσσ, hσ'σ', one_mul]
  have hvK : v ∈ C.K := Y_le_K C hvY
  have hvv : v * v = 1 := hYel v hvY
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hav : a * v * a⁻¹ = v := by
    calc a * v * a⁻¹ = (a * a) * b * a * b * a⁻¹ := by rw [hv']; group
      _ = b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ := by rw [haa, hai, hbi]; group
      _ = v⁻¹ := by rw [hv']; group
      _ = v := hvi
  have hbv : b * v * b⁻¹ = v := by
    calc b * v * b⁻¹ = b * a * b * a := by rw [hv']; group
      _ = b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ := by rw [hai, hbi]
      _ = v⁻¹ := by rw [hv']; group
      _ = v := hvi
  have hfix : ∀ {g : G} (hg : g ∈ X), g * v * g⁻¹ = v →
      barAct (C.θ ⟨g, C.S.le hg⟩) (piv D v hvK) = piv D v hvK := by
    intro g hg h
    have hk' : g * v * g⁻¹ ∈ C.K := by rw [h]; exact hvK
    rw [← piv_conj D (C.S.le hg) hvK hk']
    unfold piv
    congr 2
    exact Subtype.ext h
  have hρ := hB _ (hθa ▸ hfix ha hav) (hθb ▸ hfix hbX hbv)
  have hrvK : r * v * r⁻¹ ∈ C.K := RSmall.K_normalized C (C.S.le hr) hvK
  have heK : r * v * r⁻¹ * v⁻¹ ∈ C.K := C.K.mul_mem hrvK (C.K.inv_mem hvK)
  have heX : r * v * r⁻¹ * v⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    rw [← piv_eq_zero_iff D heK, piv_mul D hrvK (C.K.inv_mem hvK), piv_inv D hvK,
      piv_conj D (C.S.le hr) hvK hrvK, hθr, hρ, permBar_add_self]
  have heY : r * v * r⁻¹ * v⁻¹ ∈ CFSG.Open.pCoreOf 2 X := by
    apply hY (X.mul_mem (X.mul_mem (X.mul_mem hr hvX) (X.inv_mem hr)) (X.inv_mem hvX))
    have hK := heK
    exact (C.mem_K.1 hK).2
  set e := r * v * r⁻¹ * v⁻¹ with he'
  have hre : r * e = e * r := Subgroup.mem_centralizer_iff.1 heX r hr
  have hrv : r * v * r⁻¹ = e * v := by rw [he']; group
  have he3 : e * e * e = 1 := by
    have h3' : r * r * r = 1 := by rw [← pow_three', hr3]
    have hre' : r⁻¹ * e = e * r⁻¹ := by
      calc r⁻¹ * e = r⁻¹ * (e * r) * r⁻¹ := by group
        _ = r⁻¹ * (r * e) * r⁻¹ := by rw [hre]
        _ = e * r⁻¹ := by group
    have : (r * r * r) * v * (r * r * r)⁻¹ = e * e * e * v := by
      calc (r * r * r) * v * (r * r * r)⁻¹ = r * (r * (r * v * r⁻¹) * r⁻¹) * r⁻¹ := by group
        _ = r * (r * (e * v) * r⁻¹) * r⁻¹ := by rw [hrv]
        _ = r * ((r * e) * v * r⁻¹) * r⁻¹ := by group
        _ = r * ((e * r) * v * r⁻¹) * r⁻¹ := by rw [hre]
        _ = r * (e * (r * v * r⁻¹)) * r⁻¹ := by group
        _ = r * (e * (e * v)) * r⁻¹ := by rw [hrv]
        _ = (r * e) * e * (v * r⁻¹) := by group
        _ = (e * r) * e * (v * r⁻¹) := by rw [hre]
        _ = e * (r * e) * v * r⁻¹ := by group
        _ = e * (e * r) * v * r⁻¹ := by rw [hre]
        _ = e * e * (r * v * r⁻¹) := by group
        _ = e * e * (e * v) := by rw [hrv]
        _ = e * e * e * v := by group
    rw [h3'] at this
    have h' : v = e * e * e * v := by simpa using this
    calc e * e * e = e * e * e * v * v⁻¹ := by group
      _ = v * v⁻¹ := by rw [← h']
      _ = 1 := mul_inv_cancel v
  have he1 : e = 1 := by
    have hee : e * e = 1 := hYel e heY
    calc e = e * e * e := by rw [hee, one_mul]
      _ = 1 := he3
  have hrv' : r * v * r⁻¹ = v := by rw [hrv, he1, one_mul]
  have hrv'' : r⁻¹ * v * r = v := by
    calc r⁻¹ * v * r = r⁻¹ * (r * v * r⁻¹) * r := by rw [hrv']
      _ = v := by group
  have hbb'2 : b * b' * (b * b') = v := by
    calc b * b' * (b * b') = r * (a * b * a * b) * r⁻¹ := by rw [hb'', hb']; group
      _ = v := hrv'
  have hb'a2 : b' * a * (b' * a) = v := by
    calc b' * a * (b' * a) = r * (b * b' * (b * b')) * r⁻¹ := by
          rw [← hrb', hb'']; group
      _ = v := by rw [hbb'2, hrv']
  have hb'v : b' * v = v * b' := by
    have : b' * v * b'⁻¹ = v := by
      calc b' * v * b'⁻¹ = r * (b * (r⁻¹ * v * r) * b⁻¹) * r⁻¹ := by rw [hb'']; group
        _ = v := by rw [hrv'', hbv, hrv']
    calc b' * v = b' * v * b'⁻¹ * b' := by group
      _ = v * b' := by rw [this]
  have hav' : a * v = v * a := by
    calc a * v = a * v * a⁻¹ * a := by group
      _ = v * a := by rw [hav]
  have hbv' : b * v = v * b := by
    calc b * v = b * v * b⁻¹ * b := by group
      _ = v * b := by rw [hbv]
  have rel : ∀ {p q : G}, p * p = 1 → q * q = 1 → p * q * (p * q) = v → q * p = v * (p * q) := by
    intro p q hp hq hpq
    have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
    have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
    calc q * p = q⁻¹ * p⁻¹ := by rw [hpi, hqi]
      _ = v⁻¹ * (p * q) := by rw [← hpq]; group
      _ = v * (p * q) := by rw [hvi]
  have R1 : b * a = v * (a * b) := rel haa hbb (by rw [hv']; group)
  have R3 : a * b' = v * (b' * a) := rel hb'b' haa hb'a2
  have hy'X : a * b * b' ∈ X := X.mul_mem (X.mul_mem ha hbX) hb'X
  have hy'Y : a * b * b' ∈ CFSG.Open.pCoreOf 2 X := by
    apply hY hy'X
    have e : (⟨a * b * b', C.S.le hy'X⟩ : ↥M) =
        ⟨a, C.S.le ha⟩ * ⟨b, C.S.le hbX⟩ * ⟨b', C.S.le hb'X⟩ := rfl
    rw [e, map_mul, map_mul, hθa, hθb, hθb']
    calc σ * σ' * (σ * σ') = σ * (σ' * σ) * σ' := by group
      _ = σ * (σ * σ') * σ' := by rw [h3]
      _ = (σ * σ) * (σ' * σ') := by group
      _ = 1 := by rw [hσσ, hσ'σ', one_mul]
  have hsq : a * b * b' * (a * b * b') = v := by
    have hR3' : b' * a = v * (a * b') := by
      calc b' * a = v * v * (b' * a) := by rw [hvv, one_mul]
        _ = v * (v * (b' * a)) := by group
        _ = v * (a * b') := by rw [← R3]
    calc a * b * b' * (a * b * b') = a * b * (b' * a) * b * b' := by group
      _ = a * b * (v * (a * b')) * b * b' := by rw [hR3']
      _ = a * (b * v) * a * b' * b * b' := by group
      _ = a * (v * b) * a * b' * b * b' := by rw [hbv']
      _ = (a * v) * b * a * b' * b * b' := by group
      _ = (v * a) * b * a * b' * b * b' := by rw [hav']
      _ = v * (a * (b * a) * b' * b * b') := by group
      _ = v * (a * (v * (a * b)) * b' * b * b') := by rw [R1]
      _ = v * ((a * v) * a * b * b' * b * b') := by group
      _ = v * ((v * a) * a * b * b' * b * b') := by rw [hav']
      _ = v * v * (a * a) * (b * b' * (b * b')) := by group
      _ = v := by rw [hvv, haa, one_mul, one_mul, hbb'2]
  have hv1 : v = 1 := by rw [← hsq]; exact hYel _ hy'Y
  have hab : a * b * (a * b) = 1 := by
    calc a * b * (a * b) = v := by rw [hv']; group
      _ = 1 := hv1
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hai, hbi]

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6
