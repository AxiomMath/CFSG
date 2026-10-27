module

public import CFSG.Quasithin.EmptyFaithful.S14110AuxSwap
public import CFSG.Quasithin.EmptyFaithful.S14110AuxDiag
public import CFSG.Quasithin.EmptyFaithful.S14110AuxWreath

public section

namespace CFSG.Quasithin.S14110

open CFSG.Open CFSG.LieType.BorelTits Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_comm {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ normalizer (B : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have : a * b * a⁻¹ = b := by rw [h a ha b hb]; group
    rwa [this]
  · intro hu
    have h2 : a * (a * b * a⁻¹) = a * b := by
      calc a * (a * b * a⁻¹) = (a * b * a⁻¹) * a := h a ha _ hu
        _ = a * b := by group
    have h3 : a * b * a⁻¹ = b := mul_left_cancel h2
    rwa [h3] at hu

omit [Finite G] in
theorem sq_eq_one_sup {A B : Subgroup G} (hA : ∀ a ∈ A, a ^ 2 = 1) (hB : ∀ b ∈ B, b ^ 2 = 1)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : ∀ u ∈ A ⊔ B, u ^ 2 = 1 := by
  intro u hu
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A B (le_normalizer_of_comm hAB)] at hu
  obtain ⟨a, ha, b, hb, rfl⟩ := hu
  have h1 := hA a ha
  have h2 := hB b hb
  have h3 : a * b = b * a := hAB a ha b hb
  calc (a * b) ^ 2 = a * b * (a * b) := pow_two _
    _ = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← h3]
    _ = a ^ 2 * b ^ 2 := by simp [pow_two, mul_assoc]
    _ = 1 := by rw [h1, h2, mul_one]

namespace A4Data

omit [Finite G] in
theorem cj_W {A B WA WB : Subgroup G} {cA cB : G} (hA : A4Data A WA cA) (hB : A4Data B WB cB)
    {m : G} (h : cj m A = B) : cj m WA = WB := by
  have h1 : A4Data (cj m A) (cj m WA) (m * cA * m⁻¹) := hA.map (MulAut.conj m)
  rw [h] at h1
  exact (hB.W_eq h1).symm

end A4Data

namespace TwoConj

variable {M X Y W W' : Subgroup G} {c c' : G}

omit [Finite G] in
theorem le_normalizer_sup (h : TwoConj M X Y) :
    M ≤ normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff_cj, cj_sup]
  rcases h.two m hm with h1 | h1
  · rw [h1, (h.cj_Y hm).1 h1]
  · rw [h1, (h.cj_Y hm).2 h1, sup_comm]

omit [Finite G] in
theorem le_normalizer_W_sup (h : TwoConj M X Y) (hX : A4Data X W c) (hY : A4Data Y W' c') :
    M ≤ normalizer ((W ⊔ W' : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff_cj, cj_sup]
  rcases h.two m hm with h1 | h1
  · rw [hX.cj_W hX h1, hY.cj_W hY ((h.cj_Y hm).1 h1)]
  · rw [hX.cj_W hY h1, hY.cj_W hX ((h.cj_Y hm).2 h1), sup_comm]

omit [Finite G] in
theorem odd_mem_sup_centralizer (h : TwoConj M X Y) (hX : A4Data X W c) (hY : A4Data Y W' c')
    (hXM : X ≤ M) (hYM : Y ≤ M) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {g : G} (hg : g ∈ M)
    (hord : Odd (orderOf g)) :
    g ∈ (M ⊓ centralizer ((X ⊔ Y : Subgroup G) : Set G)) ⊔ (X ⊔ Y) := by
  have hgn : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have hgX : g ∈ normalizer (X : Set G) := by
    by_contra hgX
    obtain ⟨h1, h2⟩ := h.swap hg hgX
    have hsq : cj (g * g) X = X := by rw [← cj_cj, h1, h2]
    have hind : ∀ j : ℕ, cj (g ^ (2 * j + 1)) X = Y := by
      intro j
      induction j with
      | zero => simpa using h1
      | succ j ih =>
        rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, pow_add, pow_two, ← cj_cj, hsq]
        exact ih
    obtain ⟨j, hj⟩ := hord
    have := hind j
    rw [← hj, hgn, cj_one] at this
    exact h.ne this.symm
  have hgY : g ∈ normalizer (Y : Set G) := (h.mem_normalizer_Y_iff hg).2 hgX
  obtain ⟨x, hx, hxc⟩ := hX.exists_mem_mul_centralizer_of_odd hgX hord
    (by rw [hgn]; exact one_mem _)
  set k₁ : G := x⁻¹ * g with hk₁
  have hxY : x ∈ normalizer (Y : Set G) := le_normalizer_of_comm hXY hx
  have hk₁Y : k₁ ∈ normalizer (Y : Set G) := Subgroup.mul_mem _ (inv_mem hxY) hgY
  have hconj1 : ∀ v ∈ Y, k₁ * v * k₁⁻¹ = g * v * g⁻¹ := by
    intro v hv
    have hgv : g * v * g⁻¹ ∈ Y := (mem_normalizer_iff.1 hgY v).1 hv
    have hc := hXY x hx _ hgv
    calc k₁ * v * k₁⁻¹ = x⁻¹ * (g * v * g⁻¹) * x := by rw [hk₁]; group
      _ = x⁻¹ * ((g * v * g⁻¹) * x) := by group
      _ = x⁻¹ * (x * (g * v * g⁻¹)) := by rw [← hc]
      _ = g * v * g⁻¹ := by group
  have hconjn : ∀ j : ℕ, ∀ u ∈ Y, k₁ ^ j * u * (k₁ ^ j)⁻¹ = g ^ j * u * (g ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro u hu; simp
    | succ j ih =>
      intro u hu
      have hgj : g ^ j ∈ normalizer (Y : Set G) := Subgroup.pow_mem _ hgY j
      have hv : g ^ j * u * (g ^ j)⁻¹ ∈ Y := (mem_normalizer_iff.1 hgj u).1 hu
      calc k₁ ^ (j + 1) * u * (k₁ ^ (j + 1))⁻¹
          = k₁ * (k₁ ^ j * u * (k₁ ^ j)⁻¹) * k₁⁻¹ := by group
        _ = k₁ * (g ^ j * u * (g ^ j)⁻¹) * k₁⁻¹ := by rw [ih u hu]
        _ = g * (g ^ j * u * (g ^ j)⁻¹) * g⁻¹ := hconj1 _ hv
        _ = g ^ (j + 1) * u * (g ^ (j + 1))⁻¹ := by group
  have hk₁n : k₁ ^ orderOf g ∈ centralizer (W' : Set G) := by
    rw [mem_centralizer_iff]
    intro u hu
    have h1 := hconjn (orderOf g) u (hY.le hu)
    rw [hgn] at h1
    have h2 : k₁ ^ orderOf g * u * (k₁ ^ orderOf g)⁻¹ = u := by simpa using h1
    calc u * k₁ ^ orderOf g = (k₁ ^ orderOf g * u * (k₁ ^ orderOf g)⁻¹) * k₁ ^ orderOf g := by
          rw [h2]
      _ = k₁ ^ orderOf g * u := by group
  obtain ⟨y, hy, hyc⟩ := hY.exists_mem_mul_centralizer_of_odd hk₁Y hord hk₁n
  set k₂ : G := y⁻¹ * k₁ with hk₂
  have hk₂M : k₂ ∈ M :=
    M.mul_mem (M.inv_mem (hYM hy)) (M.mul_mem (M.inv_mem (hXM hx)) hg)
  have hle : X ⊔ Y ≤ centralizer ({k₂} : Set G) := by
    refine sup_le (fun x' hx' => ?_) (fun y' hy' => ?_)
    · rw [mem_centralizer_singleton_iff]
      have h1 : x' * k₁ = k₁ * x' := mem_centralizer_iff.1 hxc x' hx'
      have h2 : x' * y⁻¹ = y⁻¹ * x' := hXY x' hx' y⁻¹ (Y.inv_mem hy)
      calc x' * k₂ = (x' * y⁻¹) * k₁ := by rw [hk₂]; group
        _ = y⁻¹ * (x' * k₁) := by rw [h2]; group
        _ = y⁻¹ * (k₁ * x') := by rw [h1]
        _ = k₂ * x' := by rw [hk₂]; group
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 hyc y' hy'
  have hk₂C : k₂ ∈ centralizer ((X ⊔ Y : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (hle hl)
  have hg' : g = x * y * k₂ := by rw [hk₂, hk₁]; group
  rw [hg']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_left hx))
    (Subgroup.mem_sup_right (Subgroup.mem_sup_right hy))) (Subgroup.mem_sup_left ⟨hk₂M, hk₂C⟩)

end TwoConj

omit [Finite G] in
theorem conj_mem_centralizer_of_cj {s : G} {A B : Subgroup G} (hs : cj s A = B) {x : G}
    (hx : x ∈ centralizer (A : Set G)) : s * x * s⁻¹ ∈ centralizer (B : Set G) := by
  rw [mem_centralizer_iff]
  intro b hb
  rw [← hs] at hb
  obtain ⟨a, ha, rfl⟩ := mem_cj_iff.1 hb
  have := mem_centralizer_iff.1 hx a ha
  calc s * a * s⁻¹ * (s * x * s⁻¹) = s * (a * x) * s⁻¹ := by group
    _ = s * (x * a) * s⁻¹ := by rw [this]
    _ = s * x * s⁻¹ * (s * a * s⁻¹) := by group

omit [Finite G] in
theorem cj_inv_eq {s : G} {A B : Subgroup G} (hs : cj s A = B) : cj s⁻¹ B = A := by
  rw [← hs, cj_inv_cj]

theorem nonempty_mulEquiv_wreath_of_two_conj {T M X W R Y W' : Subgroup G} {c c' : G}
    (hT : quasithinIsSylowTwo T) (hTM : T ≤ M) (hX : A4Data X W c) (hY : A4Data Y W' c')
    (hTC : TwoConj M X Y) (hXM : X ≤ M) (hYM : Y ≤ M) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hWQ : W ≤ pCoreOf 2 M) (hW'Q : W' ≤ pCoreOf 2 M) (hQR : pCoreOf 2 M ≤ R) (hRT : R ≤ T)
    (hJ : ⁅X, thompsonJ R⁆ = X)
    (hK : M ⊓ centralizer ((X ⊔ Y : Subgroup G) : Set G) = ⊥) :
    Nonempty (↥M ≃* Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2)) := by
  classical
  set M₁ : Subgroup G := M ⊓ centralizer (Y : Set G) with hM₁
  set M₂ : Subgroup G := M ⊓ centralizer (X : Set G) with hM₂
  set N : Subgroup G := M ⊓ normalizer (X : Set G) with hN
  have hK0 : ∀ k ∈ M, k ∈ centralizer (X : Set G) → k ∈ centralizer (Y : Set G) → k = 1 := by
    intro k hk hkX hkY
    have hle : X ⊔ Y ≤ centralizer ({k} : Set G) :=
      sup_le (fun x hx => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hkX x hx))
        (fun y hy => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hkY y hy))
    have : k ∈ M ⊓ centralizer ((X ⊔ Y : Subgroup G) : Set G) :=
      ⟨hk, mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (hle hl)⟩
    rw [hK] at this
    exact Subgroup.mem_bot.1 this
  obtain ⟨t, htT, htn⟩ := hTC.exists_mem_not_mem_normalizer hT hTM
  have htM : t ∈ M := hTM htT
  obtain ⟨hts1, hts2⟩ := hTC.swap htM htn
  have hM₁N : ∀ m ∈ M₁, m ∈ normalizer (X : Set G) := fun m hm =>
    (hTC.mem_normalizer_Y_iff hm.1).1 (Subgroup.centralizer_le_normalizer (Y : Set G) hm.2)
  have hM₂N : ∀ m ∈ M₂, m ∈ normalizer (X : Set G) := fun m hm =>
    Subgroup.centralizer_le_normalizer (X : Set G) hm.2
  have hM₂nY : ∀ m ∈ M₂, m ∈ normalizer (Y : Set G) := fun m hm =>
    (hTC.mem_normalizer_Y_iff hm.1).2 (hM₂N m hm)
  have hXM₁ : X ≤ M₁ := fun x hx => ⟨hXM hx, mem_centralizer_iff.2 fun y hy => (hXY x hx y hy).symm⟩
  have hYM₂ : Y ≤ M₂ := fun y hy => ⟨hYM hy, mem_centralizer_iff.2 fun x hx => hXY x hx y hy⟩
  have hcomm : ∀ a ∈ M₁, ∀ b ∈ M₂, a * b = b * a := by
    intro a ha b hb
    have h1 : a * b * a⁻¹ * b⁻¹ ∈ centralizer (X : Set G) :=
      Subgroup.mul_mem _
        (conj_mem_centralizer (M := normalizer (X : Set G)) le_rfl (hM₁N a ha) hb.2)
        (inv_mem hb.2)
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ centralizer (Y : Set G) := by
      have : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha.2
        (conj_mem_centralizer (M := normalizer (Y : Set G)) le_rfl (hM₂nY b hb) (inv_mem ha.2))
    have h3 : a * b * a⁻¹ * b⁻¹ = 1 :=
      hK0 _ (M.mul_mem (M.mul_mem (M.mul_mem ha.1 hb.1) (M.inv_mem ha.1)) (M.inv_mem hb.1)) h1 h2
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h3, one_mul]
  have hdisj : ∀ x ∈ M₁, x ∈ M₂ → x = 1 := fun x hx1 hx2 => hK0 x hx1.1 hx2.2 hx1.2
  have hS2 : ∃ a ∈ M₁, a ∉ X := by
    by_contra hcon0
    have hM₁X : ∀ a ∈ M₁, a ∈ X := fun a ha => by_contra fun h' => hcon0 ⟨a, ha, h'⟩
    have hM₂Y : ∀ b ∈ M₂, b ∈ Y := by
      intro b hb
      have hconj : t⁻¹ * b * t ∈ M₁ := by
        refine ⟨M.mul_mem (M.mul_mem (M.inv_mem htM) hb.1) htM, ?_⟩
        have := conj_mem_centralizer_of_cj (cj_inv_eq hts2) hb.2
        simpa using this
      have h1 := hM₁X _ hconj
      have h2 : t * (t⁻¹ * b * t) * t⁻¹ ∈ cj t X := conj_mem_cj h1
      rw [hts1, show t * (t⁻¹ * b * t) * t⁻¹ = b by group] at h2
      exact h2
    have hJM : ∀ a ∈ thompsonJ R, a ∈ M := fun a ha => hTM (hRT (thompsonJ_le_self R ha))
    have hJX := le_normalizer_of_commutator_eq hJ
    have hJY : thompsonJ R ≤ normalizer (Y : Set G) := fun a ha =>
      (hTC.mem_normalizer_Y_iff (hJM a ha)).2 (hJX ha)
    refine false_of_diagonal hX hY hXY (hWQ.trans hQR) (hW'Q.trans hQR) hJX hJY ?_ ?_ hJ
    · intro a ha hac
      obtain ⟨w, hw, hwc⟩ := hX.exists_mul_mem_centralizer (hJX ha) hac
      have hwM : w ∈ M := hXM (hX.le hw)
      have hb : w⁻¹ * a ∈ M₂ := ⟨M.mul_mem (M.inv_mem hwM) (hJM a ha), hwc⟩
      have : a = w * (w⁻¹ * a) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hX.le hw))
        (Subgroup.mem_sup_right (hM₂Y _ hb))
    · intro a ha hac
      obtain ⟨w, hw, hwc⟩ := hY.exists_mul_mem_centralizer (hJY ha) hac
      have hwM : w ∈ M := hYM (hY.le hw)
      have hb : w⁻¹ * a ∈ M₁ := ⟨M.mul_mem (M.inv_mem hwM) (hJM a ha), hwc⟩
      have : a = w * (w⁻¹ * a) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hY.le hw))
        (Subgroup.mem_sup_left (hM₁X _ hb))
  obtain ⟨a₀, ha₀M₁, ha₀X⟩ := hS2
  have ha₀N : a₀ ∈ normalizer (X : Set G) := hM₁N a₀ ha₀M₁
  have hfactN : ∀ n ∈ N, ∃ a ∈ M₁, ∃ b ∈ M₂, n = a * b := by
    intro n hn
    have hna₀ : ∀ i : ℤ, (c ^ i)⁻¹ * a₀ ∉ centralizer (W : Set G) := by
      intro i hi
      have hcX : (c ^ i)⁻¹ ∈ normalizer (X : Set G) :=
        Subgroup.le_normalizer (inv_mem (zpow_mem hX.mem_X i))
      have hnx : (c ^ i)⁻¹ * a₀ ∈ normalizer (X : Set G) := Subgroup.mul_mem _ hcX ha₀N
      obtain ⟨w, hw, hwc⟩ := hX.exists_mul_mem_centralizer hnx hi
      have hk : w⁻¹ * ((c ^ i)⁻¹ * a₀) = 1 := by
        refine hK0 _ ?_ hwc ?_
        · exact M.mul_mem (M.inv_mem (hXM (hX.le hw)))
            (M.mul_mem (M.inv_mem (hXM (zpow_mem hX.mem_X i))) ha₀M₁.1)
        · refine mem_centralizer_iff.2 fun y hy => ?_
          have h1 : y * w⁻¹ = w⁻¹ * y := (hXY w⁻¹ (X.inv_mem (hX.le hw)) y hy).symm
          have h2 : y * (c ^ i)⁻¹ = (c ^ i)⁻¹ * y :=
            (hXY _ (X.inv_mem (zpow_mem hX.mem_X i)) y hy).symm
          have h3 : y * a₀ = a₀ * y := mem_centralizer_iff.1 ha₀M₁.2 y hy
          calc y * (w⁻¹ * ((c ^ i)⁻¹ * a₀)) = (y * w⁻¹) * ((c ^ i)⁻¹ * a₀) := by group
            _ = w⁻¹ * (y * (c ^ i)⁻¹) * a₀ := by rw [h1]; group
            _ = w⁻¹ * ((c ^ i)⁻¹ * y) * a₀ := by rw [h2]
            _ = w⁻¹ * ((c ^ i)⁻¹ * (y * a₀)) := by group
            _ = w⁻¹ * ((c ^ i)⁻¹ * (a₀ * y)) := by rw [h3]
            _ = w⁻¹ * ((c ^ i)⁻¹ * a₀) * y := by group
      apply ha₀X
      have : a₀ = c ^ i * w := by
        calc a₀ = c ^ i * (w * (w⁻¹ * ((c ^ i)⁻¹ * a₀))) := by group
          _ = c ^ i * w := by rw [hk]; group
      rw [this]
      exact X.mul_mem (zpow_mem hX.mem_X i) (hX.le hw)
    have hnW : n ∈ normalizer (W : Set G) := hX.normalizer_le_normalizer_W hn.2
    have ha₀W : a₀ ∈ normalizer (W : Set G) := hX.normalizer_le_normalizer_W ha₀N
    obtain ⟨i, hi⟩ := hX.exists_zpow_or_zpow_mul hnW ha₀W hna₀
    have hex : ∃ a ∈ M₁, a⁻¹ * n ∈ centralizer (W : Set G) := by
      rcases hi with hi | hi
      · refine ⟨c ^ i, hXM₁ (zpow_mem hX.mem_X i), ?_⟩
        simpa using hi
      · refine ⟨c ^ i * a₀, M₁.mul_mem (hXM₁ (zpow_mem hX.mem_X i)) ha₀M₁, ?_⟩
        simpa using hi
    obtain ⟨a, haM₁, hac⟩ := hex
    have haN : a ∈ normalizer (X : Set G) := hM₁N a haM₁
    have hanN : a⁻¹ * n ∈ normalizer (X : Set G) := Subgroup.mul_mem _ (inv_mem haN) hn.2
    obtain ⟨w, hw, hwc⟩ := hX.exists_mul_mem_centralizer hanN hac
    have hwM₁ : w ∈ M₁ := hXM₁ (hX.le hw)
    have hb : w⁻¹ * (a⁻¹ * n) ∈ M₂ :=
      ⟨M.mul_mem (M.inv_mem hwM₁.1) (M.mul_mem (M.inv_mem haM₁.1) hn.1), hwc⟩
    refine ⟨a * w, M₁.mul_mem haM₁ hwM₁, _, hb, ?_⟩
    group
  have htt : t * t ∈ N := by
    refine ⟨M.mul_mem htM htM, ?_⟩
    show t * t ∈ normalizer (X : Set G)
    rw [mem_normalizer_iff_cj, ← cj_cj, hts1, hts2]
  obtain ⟨a, ha, b, hb, hab⟩ := hfactN _ htt
  have hta : t * a * t⁻¹ ∈ M₂ :=
    ⟨M.mul_mem (M.mul_mem htM ha.1) (M.inv_mem htM), conj_mem_centralizer_of_cj hts2 ha.2⟩
  have htb : t * b * t⁻¹ ∈ M₁ :=
    ⟨M.mul_mem (M.mul_mem htM hb.1) (M.inv_mem htM), conj_mem_centralizer_of_cj hts1 hb.2⟩
  have hprod : (t * b * t⁻¹) * (t * a * t⁻¹) = a * b := by
    have h1 : (t * a * t⁻¹) * (t * b * t⁻¹) = a * b := by
      calc (t * a * t⁻¹) * (t * b * t⁻¹) = t * (a * b) * t⁻¹ := by group
        _ = t * (t * t) * t⁻¹ := by rw [← hab]
        _ = t * t := by group
        _ = a * b := hab
    rw [← h1]
    exact hcomm _ htb _ hta
  have hu : a⁻¹ * (t * b * t⁻¹) = b * (t * a * t⁻¹)⁻¹ := by
    have h1 : t * b * t⁻¹ = a * (b * (t * a * t⁻¹)⁻¹) := by
      calc t * b * t⁻¹ = ((t * b * t⁻¹) * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
        _ = (a * b) * (t * a * t⁻¹)⁻¹ := by rw [hprod]
        _ = a * (b * (t * a * t⁻¹)⁻¹) := by group
    rw [h1]; group
  have hu1 : a⁻¹ * (t * b * t⁻¹) = 1 :=
    hdisj _ (M₁.mul_mem (M₁.inv_mem ha) htb)
      (by rw [hu]; exact M₂.mul_mem hb (M₂.inv_mem hta))
  have hta' : t * a * t⁻¹ = b := by
    have h1 : b * (t * a * t⁻¹)⁻¹ = 1 := by rw [← hu]; exact hu1
    exact (mul_inv_eq_one.1 h1).symm
  set s : G := a⁻¹ * t with hs
  have hsM : s ∈ M := M.mul_mem (M.inv_mem ha.1) htM
  have haN : a ∈ normalizer (X : Set G) := hM₁N a ha
  have hsN : s ∉ normalizer (X : Set G) := by
    intro hsn
    apply htn
    have : t = a * s := by rw [hs]; group
    rw [this]
    exact Subgroup.mul_mem _ haN hsn
  have hs2 : s * s = 1 := by
    have h1 : t * a⁻¹ * t⁻¹ = b⁻¹ := by
      rw [show t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ by group, hta']
    calc s * s = a⁻¹ * (t * a⁻¹ * t⁻¹) * (t * t) := by rw [hs]; group
      _ = a⁻¹ * b⁻¹ * (a * b) := by rw [h1, hab]
      _ = 1 := by rw [hcomm a ha b hb]; group
  obtain ⟨hss1, hss2⟩ := hTC.swap hsM hsN
  have hs₁ : ∀ x ∈ M₁, s * x * s⁻¹ ∈ M₂ := fun x hx =>
    ⟨M.mul_mem (M.mul_mem hsM hx.1) (M.inv_mem hsM), conj_mem_centralizer_of_cj hss2 hx.2⟩
  have hs₂ : ∀ x ∈ M₂, s * x * s⁻¹ ∈ M₁ := fun x hx =>
    ⟨M.mul_mem (M.mul_mem hsM hx.1) (M.inv_mem hsM), conj_mem_centralizer_of_cj hss1 hx.2⟩
  have hcosets : ∀ m ∈ M, m ∈ N ∨ m * s⁻¹ ∈ N := by
    intro m hm
    by_cases hmn : m ∈ normalizer (X : Set G)
    · exact Or.inl ⟨hm, hmn⟩
    · right
      refine ⟨M.mul_mem hm (M.inv_mem hsM), ?_⟩
      show m * s⁻¹ ∈ normalizer (X : Set G)
      rw [mem_normalizer_iff_cj, cj_mul, cj_inv_eq hss2, (hTC.swap hm hmn).2]
  obtain ⟨φ⟩ := nonempty_mulEquiv_perm_four hX hXM₁ (fun m hm => hM₁N m hm)
    (fun m hm hcom => hK0 m hm.1 (mem_centralizer_iff.2 fun x hx => (hcom x hx).symm) hm.2)
    ⟨a₀, ha₀M₁, ha₀X⟩
  exact nonempty_mulEquiv_wreath M N M₁ M₂ s (fun x hx => hx.1) hsM
    (fun x hx => ⟨hx.1, hM₁N x hx⟩) (fun x hx => ⟨hx.1, hM₂N x hx⟩) hcomm hdisj hs2
    (fun hsn => hsN hsn.2) hcosets hfactN hs₁ hs₂ φ


theorem case_nonnormal {T Mc M X W R : Subgroup G} {c : G} (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) (hX : A4Data X W c) (hXM : X ≤ M) (hWQ : W ≤ pCoreOf 2 M)
    (hQR : pCoreOf 2 M ≤ R) (hRT : R ≤ T) (hJ : ⁅X, thompsonJ R⁆ = X)
    (hDC : ∀ m ∈ M, cj m X = X ∨ ∀ x ∈ X, ∀ y ∈ cj m X, x * y = y * x)
    (hrank : CFSG.Open.pRank 3 M ≤ 2)
    (hno : ¬ Nonempty (↥M ≃* Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2)))
    {m₀ : G} (hm₀ : m₀ ∈ M) (hne : cj m₀ X ≠ X) :
    M = Mc ∧ 2 < Nat.card (quasithinOmegaOneCenter T) := by
  classical
  have hTM : T ≤ M := hM.2
  set Y : Subgroup G := cj m₀ X with hYdef
  have hTC : TwoConj M X Y := ⟨hne, ⟨m₀, hm₀, rfl⟩, two_conj hX hXM hDC hrank hm₀ hne⟩
  have hYM : Y ≤ M := cj_le hXM hm₀
  set W' : Subgroup G := cj m₀ W with hW'def
  have hY : A4Data Y W' (m₀ * c * m₀⁻¹) := hX.map (MulAut.conj m₀)
  have hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := (hDC m₀ hm₀).resolve_left hne
  have hW'Q : W' ≤ pCoreOf 2 M := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := mem_cj_iff.1 hy
    exact (mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 M hm₀) w).1 (hWQ hw)
  have hX₀M : X ⊔ Y ≤ M := sup_le hXM hYM
  have hX₀n := hTC.le_normalizer_sup
  have hcen := center_sup_eq_one hX.center hY.center hXY
  have hWW' : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w := fun w hw w' hw' =>
    hXY w (hX.le hw) w' (hY.le hw')
  have hUX : W ⊔ W' ≤ X ⊔ Y := sup_le_sup hX.le hY.le
  have hU : W ⊔ W' ≠ ⊥ := by
    intro hb
    have hW1 : W = ⊥ := le_bot_iff.1 (hb ▸ le_sup_left)
    have := hX.card_W
    rw [hW1, Subgroup.card_bot] at this
    omega
  have hUel := sq_eq_one_sup hX.sq_eq_one hY.sq_eq_one hWW'
  have hUn := hTC.le_normalizer_W_sup hX hY
  set K : Subgroup G := M ⊓ centralizer ((X ⊔ Y : Subgroup G) : Set G) with hK
  have hKn : M ≤ normalizer (K : Set G) := le_normalizer_inf_centralizer hX₀n
  have hX₀nK : X ⊔ Y ≤ normalizer (K : Set G) := hX₀M.trans hKn
  have hNM : K ⊔ (X ⊔ Y) ≤ M := sup_le inf_le_left hX₀M
  have hMN : M ≤ normalizer ((K ⊔ (X ⊔ Y) : Subgroup G) : Set G) := fun m hm =>
    Subgroup.inf_normalizer_le_normalizer_sup K (X ⊔ Y) ⟨hKn hm, hX₀n hm⟩
  have hfact : ∀ m ∈ M, ∃ k ∈ K, ∃ x ∈ X ⊔ Y, ∃ t ∈ T, m = k * x * t := by
    intro m hm
    obtain ⟨n, hn, t, ht, rfl⟩ := exists_mul_of_odd_mem hNM hMN hTM
      (not_two_dvd_index_subgroupOf h.sylow hTM)
      (fun g hg hord => hTC.odd_mem_sup_centralizer hX hY hXM hYM hXY hg hord) m hm
    have hn' : n ∈ ((K ⊔ (X ⊔ Y) : Subgroup G) : Set G) := hn
    rw [coe_mul_of_right_le_normalizer_left K (X ⊔ Y) hX₀nK] at hn'
    obtain ⟨k, hk, x, hx, rfl⟩ := hn'
    exact ⟨k, hk, x, hx, t, ht, by group⟩
  by_cases hCT : T ⊓ centralizer ((X ⊔ Y : Subgroup G) : Set G) = ⊥
  · exfalso
    have hK1 : K = ⊥ := centralizer_eq_bot_of_centralizer_inf_eq_bot h hM hX₀n hCT
    exact hno (nonempty_mulEquiv_wreath_of_two_conj h.sylow hTM hX hY hTC hXM hYM hXY hWQ hW'Q
      hQR hRT hJ hK1)
  · exact eq_mc_of_centralizer_ne_bot h hM hX₀M hX₀n hcen hUX hU hUel hUn hfact hCT


end CFSG.Quasithin.S14110
