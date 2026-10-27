module

public import CFSG.RankThree.GF2n.Stroth80.Sec103Root

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_img_eq_of_inf_eq_bot {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) {S : Subgroup G} (hSQ : S ≤ Q) (hSZ : S ⊓ Z = ⊥) :
    Nat.card (M₀.img S) = Nat.card S := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun x : S => (⟨M₀.π x, M₀.pi_mem_img x.2 (hSQ x.2)⟩ : M₀.img S)) ⟨?_, ?_⟩)).symm
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have h1 : M₀.π x = M₀.π y := congrArg Subtype.val hxy
    have h2 : x⁻¹ * y ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ (hSQ hx) (hSQ hy)).mp h1
    have h3 : x⁻¹ * y ∈ S ⊓ Z := ⟨S.mul_mem (S.inv_mem hx) hy, h2⟩
    rw [hSZ, Subgroup.mem_bot] at h3
    have e : y = x := by
      calc y = x * (x⁻¹ * y) := by group
        _ = x := by rw [h3, mul_one]
    exact Subtype.ext e.symm
  · rintro ⟨e, x, hxS, hxQ, rfl⟩
    exact ⟨⟨x, hxS⟩, rfl⟩


theorem exists_comm_eq_of_smul_mem {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (R : Tim79.GammaReg Q Z γ) {S : Subgroup G} (hSQ : S ≤ Q)
    (hK : ∀ (s : K) (e : M₀.E), e ∈ M₀.img S → s • e ∈ M₀.img S) {h α : G} (hh : h ∈ Q)
    (hα : α ∈ S) (hhα : h * α ≠ α * h) {z : G} (hz : z ∈ Z) : ∃ a ∈ S, ⁅h, a⁆ = z := by
  have hb : M₀.B (M₀.π h) (M₀.π α) ≠ 0 := fun h0 =>
    hhα ((Tim79.QuadModel.comm_iff_B M₀ R hh (hSQ hα)).mpr h0)
  obtain ⟨a, haS, haQ, hae⟩ := hK (γ z / M₀.B (M₀.π h) (M₀.π α)) (M₀.π α)
    (M₀.pi_mem_img hα (hSQ hα))
  refine ⟨a, haS, R.eq_of_γ_eq (M₀.comm_mem h hh a haQ) hz ?_⟩
  rw [M₀.comm_eq h hh a haQ, hae, map_smul, smul_eq_mul, div_mul_cancel₀ _ hb]

theorem exists_line_avoiding {K E : Type} [Field K] [Finite K] [AddCommGroup E] [Module K E]
    [Finite E] (S : Submodule K E) (T : AddSubgroup E)
    (hcard : Nat.card K * Nat.card T ≤ Nat.card S) :
    ∃ e ∈ S, e ≠ 0 ∧ ∀ s : K, s • e ∈ T → s = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  let f : {s : K // s ≠ 0} × T → E := fun p => (p.1 : K)⁻¹ • (p.2 : E)
  have hsub : ∀ e ∈ S, ∃ p, f p = e := by
    intro e he
    by_cases he0 : e = 0
    · exact ⟨(⟨1, one_ne_zero⟩, 0), by simp [f, he0]⟩
    · obtain ⟨s, hsT, hs0⟩ := hcon e he he0
      exact ⟨(⟨s, hs0⟩, ⟨s • e, hsT⟩), by simp [f, smul_smul, inv_mul_cancel₀ hs0]⟩
  choose g hg using hsub
  have h1 : Nat.card S ≤ Nat.card ({s : K // s ≠ 0} × T) := by
    refine Nat.card_le_card_of_injective (fun x : S => g x.1 x.2) fun x y hxy => ?_
    apply Subtype.ext
    calc (x : E) = f (g x.1 x.2) := (hg _ _).symm
      _ = f (g y.1 y.2) := congrArg f hxy
      _ = y := hg _ _
  rw [Nat.card_prod] at h1
  have h2 : Nat.card {s : K // s ≠ 0} < Nat.card K :=
    Finite.card_subtype_lt (p := fun s : K => s ≠ 0) (x := 0) (by simp)
  have hT : 0 < Nat.card T := Nat.card_pos
  have h3 : Nat.card {s : K // s ≠ 0} * Nat.card T < Nat.card K * Nat.card T :=
    Nat.mul_lt_mul_of_pos_right h2 hT
  exact lt_irrefl _ (lt_of_le_of_lt (hcard.trans h1) h3)

private theorem exists_line_le_of_avoiding {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) {A : Subgroup G} (hAQ : A ≤ Q)
    (hK : ∀ (s : K) (e : M₀.E), e ∈ M₀.img A → s • e ∈ M₀.img A) {e : M₀.E}
    (heS : e ∈ M₀.img A) :
    ∃ L : Subgroup G, L ≤ A ∧ ∀ v : M₀.E, v ∈ M₀.img L ↔ ∃ s : K, v = s • e := by
  let L : Subgroup G :=
    { carrier := {x | x ∈ A ∧ ∃ s : K, M₀.π x = s • e}
      mul_mem' := by
        rintro x y ⟨hxA, s, hs⟩ ⟨hyA, s', hs'⟩
        exact ⟨A.mul_mem hxA hyA, s + s', by
          rw [M₀.π_mul x (hAQ hxA) y (hAQ hyA), hs, hs', add_smul]⟩
      one_mem' := ⟨A.one_mem, 0, by rw [Tim79.QuadModel.pi_one M₀, zero_smul]⟩
      inv_mem' := by
        rintro x ⟨hxA, s, hs⟩
        exact ⟨A.inv_mem hxA, -s, by rw [Tim79.QuadModel.pi_inv M₀ (hAQ hxA), hs, neg_smul]⟩ }
  have hLimg : ∀ v : M₀.E, v ∈ M₀.img L ↔ ∃ s : K, v = s • e := by
    intro v
    constructor
    · rintro ⟨x, ⟨-, s, hs⟩, -, rfl⟩
      exact ⟨s, hs⟩
    · rintro ⟨s, rfl⟩
      obtain ⟨x, hxA, hxQ, hx⟩ := M₀.mem_img.mp (hK s e heS)
      exact ⟨x, ⟨hxA, s, hx⟩, hxQ, hx⟩
  exact ⟨L, fun x hx => hx.1, hLimg⟩

private theorem line_inf_eq_bot_of_avoiding {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) {A A₀ : Subgroup G} (hAQ : A ≤ Q)
    (hAZ : A ⊓ Z = ⊥) (hA₀ : A₀ ≤ A) {L : Subgroup G} (hLA : L ≤ A) {e : M₀.E}
    (heT : ∀ s : K, s • e ∈ M₀.img A₀ → s = 0)
    (hLimg : ∀ v : M₀.E, v ∈ M₀.img L ↔ ∃ s : K, v = s • e) : L ⊓ A₀ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxA₀⟩
  obtain ⟨s, hs⟩ := (hLimg (M₀.π x)).mp (M₀.pi_mem_img hxL (hLA.trans hAQ hxL))
  have hs0 : s = 0 := heT s (hs ▸ M₀.pi_mem_img hxA₀ (hAQ (hA₀ hxA₀)))
  rw [hs0, zero_smul] at hs
  have hxZ : x ∈ Z := (M₀.π_ker x (hAQ (hA₀ hxA₀))).mp hs
  have h : x ∈ A ⊓ Z := ⟨hA₀ hxA₀, hxZ⟩
  rwa [hAZ] at h

private theorem line_inf_Z_eq_bot_of_le {A L : Subgroup G} (hAZ : A ⊓ Z = ⊥) (hLA : L ≤ A) :
    L ⊓ Z = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxZ⟩
  have h : x ∈ A ⊓ Z := ⟨hLA hxL, hxZ⟩
  rwa [hAZ] at h

private theorem card_line_of_image {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) {A : Subgroup G} (hAQ : A ≤ Q) (hAZ : A ⊓ Z = ⊥)
    {L : Subgroup G} (hLA : L ≤ A) (hLZ : L ⊓ Z = ⊥) {e : M₀.E} (he0 : e ≠ 0)
    (hLimg : ∀ v : M₀.E, v ∈ M₀.img L ↔ ∃ s : K, v = s • e) :
    Nat.card L = Nat.card K := by
  rw [← card_img_eq_of_inf_eq_bot M₀ (hLA.trans hAQ) hLZ]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun s : K => (⟨s • e, (hLimg _).mpr ⟨s, rfl⟩⟩ : M₀.img L)) ⟨?_, ?_⟩)).symm
  · intro s s' hss'
    exact smul_left_injective K he0 (congrArg Subtype.val hss')
  · rintro ⟨v, hv⟩
    obtain ⟨s, rfl⟩ := (hLimg v).mp hv
    exact ⟨s, rfl⟩

theorem exists_isLine_le {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) {A A₀ : Subgroup G} (hAQ : A ≤ Q) (hAZ : A ⊓ Z = ⊥)
    (hA₀ : A₀ ≤ A) (hK : ∀ (s : K) (e : M₀.E), e ∈ M₀.img A → s • e ∈ M₀.img A)
    (hcard : Nat.card K * Nat.card A₀ ≤ Nat.card A) :
    ∃ L : Subgroup G, L ≤ A ∧ M₀.IsLine L ∧ L ⊓ A₀ = ⊥ ∧ Nat.card L = Nat.card K := by
  haveI : Finite M₀.E := Module.finite_of_finite K
  let S : Submodule K M₀.E :=
    { carrier := (M₀.img A : Set M₀.E)
      add_mem' := fun ha hb => (M₀.img A).add_mem ha hb
      zero_mem' := (M₀.img A).zero_mem
      smul_mem' := fun s e he => hK s e he }
  have hA₀Z : A₀ ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h : x ∈ A ⊓ Z := ⟨hA₀ hx.1, hx.2⟩
    rwa [hAZ] at h
  have hSc : Nat.card S = Nat.card A := card_img_eq_of_inf_eq_bot M₀ hAQ hAZ
  have hTc : Nat.card (M₀.img A₀) = Nat.card A₀ :=
    card_img_eq_of_inf_eq_bot M₀ (hA₀.trans hAQ) hA₀Z
  obtain ⟨e, heS, he0, heT⟩ :=
    exists_line_avoiding S (M₀.img A₀) (by rw [hSc, hTc]; exact hcard)
  obtain ⟨L, hLA, hLimg⟩ := exists_line_le_of_avoiding M₀ hAQ hK heS
  have hL0 : L ⊓ A₀ = ⊥ :=
    line_inf_eq_bot_of_avoiding M₀ hAQ hAZ hA₀ hLA heT hLimg
  have hLZ : L ⊓ Z = ⊥ := line_inf_Z_eq_bot_of_le hAZ hLA
  exact ⟨L, hLA, ⟨e, he0, hLimg⟩, hL0, card_line_of_image M₀ hAQ hAZ hLA hLZ he0 hLimg⟩

omit [Finite G] in
theorem conjSubgroup_eq_of_mem_centralizer {c : G} {B : Subgroup G}
    (hcB : c ∈ Subgroup.centralizer (B : Set G)) : conjSubgroup c B = B := by
  ext b
  rw [mem_conjSubgroup]
  constructor
  · intro h
    have hb' : c⁻¹ * b * c * c = c * (c⁻¹ * b * c) := Subgroup.mem_centralizer_iff.mp hcB _ h
    have e : b = c⁻¹ * b * c := by
      calc b = c * (c⁻¹ * b * c) * c⁻¹ := by group
        _ = c⁻¹ * b * c * c * c⁻¹ := by rw [← hb']
        _ = c⁻¹ * b * c := by group
    rw [e]; exact h
  · intro hb
    have hb' : b * c = c * b := Subgroup.mem_centralizer_iff.mp hcB b hb
    have e : c⁻¹ * b * c = b := by
      calc c⁻¹ * b * c = c⁻¹ * (b * c) := by group
        _ = c⁻¹ * (c * b) := by rw [hb']
        _ = b := by group
    rw [e]; exact hb


theorem StrothHyp.exists_conj_eq_mul (H : StrothHyp M Q Z) {e z : G} (he : e ∈ Q)
    (heZ : e ∉ Z) (hz : z ∈ Z) : ∃ k ∈ Q, k * e * k⁻¹ = e * z := by
  obtain ⟨k, hk, hke⟩ := exists_comm_eq H he heZ hz
  refine ⟨k, hk, ?_⟩
  calc k * e * k⁻¹ = ⁅k, e⁆ * e := by simp only [commutatorElement_def]; group
    _ = z * e := by rw [hke]
    _ = e * z := Z_central H hz he

theorem Ctx.mem_QB_conj_iff {X : Subgroup G} (hX : Ctx M Q Z X) {k a : G} (hk : k ∈ Q)
    (ha : a ∈ Q) : a ∈ QB (conjSubgroup k X) ↔ a ∈ QB X := by
  rw [QB_conj, mem_conjSubgroup]
  have hζ : ⁅a⁻¹, k⁻¹⁆ ∈ Z := comm_mem_Z hX.hyp (Q.inv_mem ha) (Q.inv_mem hk)
  have hZX : Z ≤ QB X := hX.Z_le_QB.1
  have e : k⁻¹ * a * k = a * ⁅a⁻¹, k⁻¹⁆ := by simp only [commutatorElement_def]; group
  rw [e]
  constructor
  · intro h
    have h' := (QB X).mul_mem h ((QB X).inv_mem (hZX hζ))
    rwa [mul_inv_cancel_right] at h'
  · intro h
    exact (QB X).mul_mem h (hZX hζ)

theorem Sit.le_QB {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) : X ≤ QB X := by
  obtain ⟨g, hgY, hQBY, -⟩ := hs.QB_eq
  rw [hQBY, hgY]
  exact Subgroup.map_mono hs.hyp.Z_normal.1

theorem Sit.comm_comm_of_mem_inf_QB {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) {c a : G}
    (hcQ : c ∈ Q) (ha : a ∈ Q ⊓ QB Y) : ⁅t, c⁆ * a = a * ⁅t, c⁆ := by
  have hat : a * t = t * a :=
    Subgroup.mem_centralizer_singleton_iff.mp ((smith_1_13 hs).2.2.2.1 ha).2
  have hζ : ⁅a, c⁆ ∈ Z := comm_mem_Z hs.hyp ha.1 hcQ
  have htζ : t * ⁅a, c⁆ * t⁻¹ = ⁅a, c⁆ := hs.x_cent (smith_1_12 hs) _ hζ
  have hxQ : ⁅t, c⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hs.hyp.Q_normal.2 hs.memM) c).mp hcQ)
      (Q.inv_mem hcQ)
  have hζx : ⁅a, c⁆ * ⁅t, c⁆ = ⁅t, c⁆ * ⁅a, c⁆ := Z_central hs.hyp hζ hxQ
  have hac : a * c * a⁻¹ = ⁅a, c⁆ * c := by simp only [commutatorElement_def]; group
  have hata : a * t * a⁻¹ = t := by rw [hat]; group
  have e : a * ⁅t, c⁆ * a⁻¹ = ⁅t, c⁆ := by
    calc a * ⁅t, c⁆ * a⁻¹
        = (a * t * a⁻¹) * (a * c * a⁻¹) * (a * t * a⁻¹)⁻¹ * (a * c * a⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = t * (⁅a, c⁆ * c) * t⁻¹ * (⁅a, c⁆ * c)⁻¹ := by rw [hata, hac]
      _ = (t * ⁅a, c⁆ * t⁻¹) * (t * c * t⁻¹ * c⁻¹) * ⁅a, c⁆⁻¹ := by group
      _ = ⁅a, c⁆ * ⁅t, c⁆ * ⁅a, c⁆⁻¹ := by rw [htζ, ← commutatorElement_def]
      _ = ⁅t, c⁆ := by rw [hζx]; group
  calc ⁅t, c⁆ * a = (a * ⁅t, c⁆ * a⁻¹) * a := by rw [e]
    _ = a * ⁅t, c⁆ := by group

theorem Sit.comm_of_conj_eq_mul {Y : Subgroup G} {w : G} (hs : Sit M Q Z Y w) {k a z : G}
    (hk : k ∈ Q) (ha : a ∈ Q ⊓ QB Y) (hz : z ∈ Z) (h : k * w * k⁻¹ = w * a * z) :
    k * a = a * k := by
  have h12 := smith_1_12 hs
  have hζ : ⁅k, a⁆ ∈ Z := comm_mem_Z hs.hyp hk ha.1
  have ha2 : a * a = 1 := by
    have h1 : a ^ 2 ∈ Z ⊓ QB Y := ⟨sq_mem_Z hs.hyp ha.1, (QB Y).pow_mem ha.2 2⟩
    rw [Z_inf_QB_eq_bot hs h12, Subgroup.mem_bot] at h1
    rwa [pow_two] at h1
  have hz2 : z * z = 1 := by rw [← pow_two]; exact Z_sq hs.hyp hz
  have hk2 : k * k ∈ Z := by rw [← pow_two]; exact sq_mem_Z hs.hyp hk
  have hwk : w * (k * k) * w⁻¹ = k * k := hs.x_cent h12 _ hk2
  have hkz : k * z * k⁻¹ = z := by rw [← Z_central hs.hyp hz hk]; group
  have hzQ : z * a = a * z := Z_central hs.hyp hz ha.1
  have hζa : ⁅k, a⁆ * a = a * ⁅k, a⁆ := Z_central hs.hyp hζ ha.1
  have hζz : ⁅k, a⁆ * z = z * ⁅k, a⁆ := Z_central hs.hyp hζ (hs.hyp.Z_normal.1 hz)
  have hkak : k * a * k⁻¹ = ⁅k, a⁆ * a := by simp only [commutatorElement_def]; group
  have e1 : (k * k) * w * (k * k)⁻¹ = w * ⁅k, a⁆ := by
    calc (k * k) * w * (k * k)⁻¹ = k * (k * w * k⁻¹) * k⁻¹ := by group
      _ = k * (w * a * z) * k⁻¹ := by rw [h]
      _ = (k * w * k⁻¹) * (k * a * k⁻¹) * (k * z * k⁻¹) := by group
      _ = (w * a * z) * (⁅k, a⁆ * a) * z := by rw [h, hkak, hkz]
      _ = w * a * (z * ⁅k, a⁆) * a * z := by group
      _ = w * a * (⁅k, a⁆ * z) * a * z := by rw [← hζz]
      _ = w * a * ⁅k, a⁆ * (z * a) * z := by group
      _ = w * a * ⁅k, a⁆ * (a * z) * z := by rw [hzQ]
      _ = w * (a * ⁅k, a⁆) * a * (z * z) := by group
      _ = w * (⁅k, a⁆ * a) * a * (z * z) := by rw [hζa]
      _ = w * ⁅k, a⁆ * (a * a) * (z * z) := by group
      _ = w * ⁅k, a⁆ := by rw [ha2, hz2, mul_one, mul_one]
  have e2 : (k * k) * w * (k * k)⁻¹ = w := by
    calc (k * k) * w * (k * k)⁻¹ = (w * (k * k) * w⁻¹) * w * (k * k)⁻¹ := by rw [hwk]
      _ = w := by group
  have hζ1 : ⁅k, a⁆ = 1 := by
    have : w * ⁅k, a⁆ = w * 1 := by rw [mul_one, ← e1, e2]
    exact mul_left_cancel this
  exact commutatorElement_eq_one_iff_mul_comm.mp hζ1

theorem Ctx.isRoot_of_mem_Ut_of_not_caseA (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (hB : ¬ CaseA Q Z t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {β : G}
    (hβ : β ∈ Q ⊓ QB Y ⊓ Ut Q Z t) (hβ1 : β ≠ 1) :
    ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = β := by
  obtain ⟨y, hy, hyt⟩ := hc.exists_conj_eq_mul_of_not_caseA ht hB hβ.2
  exact Sit.isRoot_of_conj hs hβ.1 hβ1 ⟨y, hyt⟩


theorem Ctx.exists_comm_mul_inv_mem_Z_of_mem_Tt (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ LB M Q B) {V : Subgroup G} (hVU : V ≤ Ut Q Z t) {v : G} (hv : v ∈ Tt Q Z V t) :
    ∃ w ∈ Wt Q V, ⁅w, t⁆ * v⁻¹ ∈ Z := by
  have hTU : Tt Q Z V t ≤ Ut Q Z t :=
    sup_le_sup_right (Subgroup.commutator_mono inf_le_left le_rfl) Z
  obtain ⟨x, hx, hxv⟩ := hc.exists_comm_mul_inv_mem_Z ht (hTU hv)
  refine ⟨x, (hc.comm_mem_Tt_iff ht hVU hx).mp ?_, hxv⟩
  have e : ⁅x, t⁆ = (⁅x, t⁆ * v⁻¹) * v := by group
  rw [e]
  exact (Tt Q Z V t).mul_mem (Subgroup.mem_sup_right hxv) hv

private theorem comm_eq_one_of_mem_Tt_centralizer (hc : Ctx M Q Z B) {t w c₀ : G}
    (ht : t ∈ LB M Q B) (ht2 : t * t = 1) (hc₀ : c₀ ∈ Q) {V : Subgroup G}
    (hV : ⁅c₀, t⁆ ∈ V) (hwQ : w ∈ Q)
    (hwV : w ∈ Subgroup.centralizer (V : Set G)) : ⁅⁅w, t⁆, c₀⁆ = 1 := by
  have htM : t ∈ M := hc.LB_le_M ht
  have hwV' : ⁅c₀, t⁆ * w = w * ⁅c₀, t⁆ := Subgroup.mem_centralizer_iff.mp hwV _ hV
  obtain ⟨htQ, -⟩ := hc.conj_mem_Q_of_mem_M htM
  have hw'Q : t * w * t⁻¹ ∈ Q := htQ w hwQ
  have hc'Q : t * c₀ * t⁻¹ ∈ Q := htQ c₀ hc₀
  have hζ₃ : ⁅w, t * c₀ * t⁻¹⁆ ∈ Z := comm_mem_Z hc.hyp hwQ hc'Q
  have hA : ⁅w, c₀⁆ = ⁅w, t * c₀ * t⁻¹⁆ := by
    have hdQ : ⁅c₀, t⁆ ∈ Q := hc.comm_mem_Q htM hc₀
    have hd : c₀ = ⁅c₀, t⁆ * (t * c₀ * t⁻¹) := by simp only [commutatorElement_def]; group
    have hwd : w * ⁅c₀, t⁆ * w⁻¹ = ⁅c₀, t⁆ := by rw [← hwV']; group
    calc ⁅w, c₀⁆ = ⁅w, ⁅c₀, t⁆ * (t * c₀ * t⁻¹)⁆ := by rw [← hd]
      _ = (w * ⁅c₀, t⁆ * w⁻¹) * ⁅w, t * c₀ * t⁻¹⁆ * ⁅c₀, t⁆⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = ⁅c₀, t⁆ * ⁅w, t * c₀ * t⁻¹⁆ * ⁅c₀, t⁆⁻¹ := by rw [hwd]
      _ = ⁅w, t * c₀ * t⁻¹⁆ := by rw [← Smith81.Z_central hc.hyp hζ₃ hdQ]; group
  have hB : ⁅t * w * t⁻¹, c₀⁆ = ⁅w, t * c₀ * t⁻¹⁆ := by
    have h1 : t * ⁅w, t * c₀ * t⁻¹⁆ * t⁻¹ = ⁅w, t * c₀ * t⁻¹⁆ :=
      hc.LB_centralizes_Z ht _ hζ₃
    have h2 : t * (t * c₀ * t⁻¹) * t⁻¹ = c₀ := by
      calc t * (t * c₀ * t⁻¹) * t⁻¹ = (t * t) * c₀ * (t * t)⁻¹ := by group
        _ = c₀ := by rw [ht2]; group
    calc ⁅t * w * t⁻¹, c₀⁆ = ⁅t * w * t⁻¹, t * (t * c₀ * t⁻¹) * t⁻¹⁆ := by rw [h2]
      _ = t * ⁅w, t * c₀ * t⁻¹⁆ * t⁻¹ := by simp only [commutatorElement_def]; group
      _ = ⁅w, t * c₀ * t⁻¹⁆ := h1
  have hw'Q' : (t * w * t⁻¹)⁻¹ ∈ Q := Q.inv_mem hw'Q
  have hζ₄ : ⁅(t * w * t⁻¹)⁻¹, c₀⁆ ∈ Z := comm_mem_Z hc.hyp hw'Q' hc₀
  have e1 : ⁅(t * w * t⁻¹)⁻¹, c₀⁆ = ⁅t * w * t⁻¹, c₀⁆⁻¹ := by
    have hζ₅ : ⁅c₀, t * w * t⁻¹⁆ ∈ Z := comm_mem_Z hc.hyp hc₀ hw'Q
    calc ⁅(t * w * t⁻¹)⁻¹, c₀⁆ = (t * w * t⁻¹)⁻¹ * ⁅c₀, t * w * t⁻¹⁆ * (t * w * t⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = ⁅c₀, t * w * t⁻¹⁆ := by rw [← Smith81.Z_central hc.hyp hζ₅ hw'Q']; group
      _ = ⁅t * w * t⁻¹, c₀⁆⁻¹ := by rw [commutatorElement_inv]
  have e2 : ⁅⁅w, t⁆, c₀⁆ = ⁅(t * w * t⁻¹)⁻¹, c₀⁆ * ⁅w, c₀⁆ := by
    calc ⁅⁅w, t⁆, c₀⁆ = w * ⁅(t * w * t⁻¹)⁻¹, c₀⁆ * w⁻¹ * ⁅w, c₀⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅(t * w * t⁻¹)⁻¹, c₀⁆ * ⁅w, c₀⁆ := by rw [← Smith81.Z_central hc.hyp hζ₄ hwQ]; group
  exact by rw [e2, e1, hB, ← hA, inv_mul_cancel]

theorem Ctx.Tt_le_centralizer_of_comm_mem (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (ht2 : t * t = 1) {V : Subgroup G} {c₀ : G} (hc₀ : c₀ ∈ Q) (hV : ⁅c₀, t⁆ ∈ V) :
    Tt Q Z V t ≤ Subgroup.centralizer ({c₀} : Set G) := by
  have htM : t ∈ M := hc.LB_le_M ht
  have htk : ∀ k : ℤ, t ^ k = 1 ∨ t ^ k = t := by
    intro k
    have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
    rw [zpow_eq_zpow_emod k h2]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left; rw [hk, zpow_zero]
    · right; rw [hk, zpow_one]
  have hZc : Z ≤ Subgroup.centralizer ({c₀} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Smith81.Z_central hc.hyp hz hc₀)
  refine sup_le ?_ hZc
  rw [Subgroup.commutator_le]
  intro w hw k hk
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  rcases htk j with h1 | h1
  · rw [h1, commutatorElement_one_right]
    exact Subgroup.one_mem _
  rw [h1]
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (commutatorElement_eq_one_iff_mul_comm.mp
      (comm_eq_one_of_mem_Tt_centralizer hc ht ht2 hc₀ hV hw.1 hw.2))
theorem Sit.exists_conj_eq_mul_of_comm {X : Subgroup G} {r : G} (hs : Sit M Q Z X r) {α : G}
    (hα : α ∈ Q) (hαr : α * r = r * α) (hcomm : ∀ h ∈ Q, ⁅h, r⁆ ∈ Z → h * α = α * h) :
    ∃ h ∈ Q, ∃ z ∈ Z, h * r * h⁻¹ = r * α * z := by
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hs.hyp
  have hrM : r ∈ M := hs.memM
  have hrZ : ∀ z ∈ Z, r * z * r⁻¹ = z := hs.x_cent (smith_1_12 hs)
  obtain ⟨A⟩ := exists_xact hD hrM hrZ
  have hrQ : ∀ x ∈ Q, r * x * r⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hs.hyp.Q_normal.2 hrM) x).mp hx
  have hrange : M₀.π α ∈ LinearMap.range ((A.T : M₀.E →ₗ[K] M₀.E) - 1) := by
    refine (Tim79.QuadModel.mem_range_sub_one_iff' A.hB _).mpr fun f hf => ?_
    obtain ⟨h, hhQ, rfl⟩ := M₀.π_surj f
    have hhr : ⁅h, r⁆ ∈ Z := by
      have h1 : ⁅r, h⁆ ∈ Z := (comm_mem_iff_fix hrQ A.hπ hhQ).mpr hf
      rw [← commutatorElement_inv]
      exact Z.inv_mem h1
    exact (Tim79.QuadModel.comm_iff_B M₀ hD.reg hα hhQ).mp (hcomm h hhQ hhr).symm
  obtain ⟨f, hf⟩ := hrange
  obtain ⟨q, hq, rfl⟩ := M₀.π_surj f
  have hrq : r * q * r⁻¹ ∈ Q := hrQ q hq
  have hf' : A.T (M₀.π q) - M₀.π q = M₀.π α := by simpa using hf
  have hπ : M₀.π (r * q * r⁻¹ * q⁻¹) = M₀.π α := by
    rw [M₀.π_mul _ hrq _ (Q.inv_mem hq), A.hπ q hq, Tim79.QuadModel.pi_inv M₀ hq,
      ← sub_eq_add_neg, hf']
  have hz₀ : α⁻¹ * (r * q * r⁻¹ * q⁻¹) ∈ Z :=
    (Tim79.QuadModel.pi_eq_iff M₀ hα (Q.mul_mem hrq (Q.inv_mem hq))).mp hπ.symm
  have hζ : α⁻¹ * α⁻¹ ∈ Z := by
    have h := Z.inv_mem (sq_mem_Z hs.hyp hα)
    rwa [pow_two, mul_inv_rev] at h
  refine ⟨q, hq, (α⁻¹ * (r * q * r⁻¹ * q⁻¹))⁻¹ * (α⁻¹ * α⁻¹), Z.mul_mem (Z.inv_mem hz₀) hζ, ?_⟩
  have hz₀α : (α⁻¹ * (r * q * r⁻¹ * q⁻¹))⁻¹ * α = α * (α⁻¹ * (r * q * r⁻¹ * q⁻¹))⁻¹ :=
    Z_central hs.hyp (Z.inv_mem hz₀) hα
  have hzr : r * ((α⁻¹ * (r * q * r⁻¹ * q⁻¹))⁻¹ * (α⁻¹ * α⁻¹)) * r⁻¹ =
      (α⁻¹ * (r * q * r⁻¹ * q⁻¹))⁻¹ * (α⁻¹ * α⁻¹) := hrZ _ (Z.mul_mem (Z.inv_mem hz₀) hζ)
  calc q * r * q⁻¹ = (α⁻¹ * (r * q * r⁻¹ * q⁻¹))⁻¹ * α * (α⁻¹ * α⁻¹) * r := by group
    _ = α * (α⁻¹ * (r * q * r⁻¹ * q⁻¹))⁻¹ * (α⁻¹ * α⁻¹) * r := by rw [hz₀α]
    _ = α * (r * ((α⁻¹ * (r * q * r⁻¹ * q⁻¹))⁻¹ * (α⁻¹ * α⁻¹)) * r⁻¹) * r := by
        rw [hzr]; group
    _ = α * r * ((α⁻¹ * (r * q * r⁻¹ * q⁻¹))⁻¹ * (α⁻¹ * α⁻¹)) := by group
    _ = r * α * ((α⁻¹ * (r * q * r⁻¹ * q⁻¹))⁻¹ * (α⁻¹ * α⁻¹)) := by rw [hαr]

end CFSG.RankThree.GF2n.Stroth80
