module

public import CFSG.RankThree.PartTwo.Sec12.Item123

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace ActOnA

variable {G : Type*} [Group G]

theorem mem_of_zpow_mem {H : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) {k : ℤ} (hk : x ^ k ∈ H)
    (hk3 : ¬ (3 : ℤ) ∣ k) : x ∈ H := by
  have hx3' : x ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hx3]
  rw [zpow_eq_zpow_emod k hx3'] at hk
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have h1 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have h2 : k % 3 ≠ 0 := fun h => hk3 (Int.dvd_of_emod_eq_zero h)
  have : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h
  · rw [h, zpow_one] at hk
    exact hk
  · rw [h] at hk
    have e : x = (x ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul, show (2 : ℤ) * 2 = 3 + 1 by norm_num, zpow_add, hx3', one_mul, zpow_one]
    rw [e]
    exact H.zpow_mem hk 2

theorem zpow_eq_one_of_dvd {x : G} (hx3 : x ^ 3 = 1) {k : ℤ} (hk : (3 : ℤ) ∣ k) : x ^ k = 1 := by
  obtain ⟨m, rfl⟩ := hk
  rw [zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hx3, one_zpow]

theorem exists_pow_three_inv_conj {Γ : Type*} [Group Γ]
    (h : Nonempty (Γ ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (Γ ≃* DihedralGroup 6)) :
    ∃ σ τ : Γ, σ ≠ 1 ∧ σ ^ 3 = 1 ∧ τ * σ * τ⁻¹ = σ⁻¹ := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    refine ⟨e.symm (Equiv.swap 0 1 * Equiv.swap 1 2), e.symm (Equiv.swap 0 1), ?_, ?_, ?_⟩
    · rw [Ne, MulEquiv.map_eq_one_iff]
      decide
    · rw [← map_pow, MulEquiv.map_eq_one_iff]
      decide
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
      exact congrArg e.symm (by decide)
  · obtain ⟨e⟩ := h
    refine ⟨e.symm (DihedralGroup.r 2), e.symm (DihedralGroup.sr 0), ?_, ?_, ?_⟩
    · rw [Ne, MulEquiv.map_eq_one_iff]
      decide
    · rw [← map_pow, MulEquiv.map_eq_one_iff]
      decide
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
      exact congrArg e.symm (by decide)

theorem three_dvd_sub_one_of_dvd_one_sub_cube {i : ℤ} (h : (3 : ℤ) ∣ 1 - i * (i * i)) :
    (3 : ℤ) ∣ i - 1 := by
  have h' : ((1 - i * (i * i) : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast h)
  have e : ((i - 1 : ℤ) : ZMod 3) = 0 := by
    push_cast at h' ⊢
    generalize (i : ZMod 3) = z at h' ⊢
    revert h'
    revert z
    decide
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp e

theorem zpow_sub_eq_zpow_sub {a d : G} {i j k l : ℤ} (h : a ^ i * d ^ j = a ^ k * d ^ l) :
    a ^ (i - k) = d ^ (l - j) := by
  calc a ^ (i - k) = (a ^ k)⁻¹ * (a ^ i * d ^ j) * (d ^ j)⁻¹ := by group
    _ = (a ^ k)⁻¹ * (a ^ k * d ^ l) * (d ^ j)⁻¹ := by rw [h]
    _ = d ^ (l - j) := by group

theorem exists_zpow_mul_of_mem {A : Subgroup G} {c a d : G}
    (hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hA : A = Subgroup.closure {c, a, d}) {z : G}
    (hz : z ∈ A) : ∃ i : ℤ, ∃ b ∈ Subgroup.closure ({a, d} : Set G), z = c ^ i * b := by
  have hcA : c ∈ A := hA ▸ Subgroup.subset_closure (by simp)
  have hBA : Subgroup.closure ({a, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hA ▸ Subgroup.subset_closure (by simp)
    · exact hA ▸ Subgroup.subset_closure (by simp)
  rw [hA] at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨1, 1, Subgroup.one_mem _, by simp⟩
    · exact ⟨0, x, Subgroup.subset_closure (by simp), by simp⟩
    · exact ⟨0, x, Subgroup.subset_closure (by simp), by simp⟩
  | one => exact ⟨0, 1, Subgroup.one_mem _, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨i, b, hb, rfl⟩ := ihx
    obtain ⟨j, b', hb', rfl⟩ := ihy
    refine ⟨i + j, b * b', Subgroup.mul_mem _ hb hb', ?_⟩
    have hcb : b * c ^ j = c ^ j * b := hcomm b (hBA hb) (c ^ j) (A.zpow_mem hcA j)
    rw [zpow_add]
    calc c ^ i * b * (c ^ j * b') = c ^ i * (b * c ^ j) * b' := by group
      _ = c ^ i * (c ^ j * b) * b' := by rw [hcb]
      _ = c ^ i * c ^ j * (b * b') := by group
  | inv x _ ih =>
    obtain ⟨i, b, hb, rfl⟩ := ih
    refine ⟨-i, b⁻¹, Subgroup.inv_mem _ hb, ?_⟩
    have hcb : b⁻¹ * c ^ (-i) = c ^ (-i) * b⁻¹ :=
      hcomm _ (Subgroup.inv_mem _ (hBA hb)) _ (A.zpow_mem hcA _)
    rw [mul_inv_rev, ← zpow_neg, hcb]

theorem conj_mul_inv_mem_zpowers {A Y : Subgroup G} {c a d g t : G}
    (hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hexp : ∀ y ∈ A, y ^ 3 = 1)
    (hA : A = Subgroup.closure {c, a, d}) (hacd : a ∉ Subgroup.closure ({c, d} : Set G))
    (hcad : c ∉ Subgroup.closure ({a, d} : Set G))
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (htA : t ∈ Subgroup.normalizer (A : Set G))
    (hga : g * a = a * g) (hgd : g * d = d * g) (hta : t * a = a * t)
    (htd : t ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hg3 : ∀ z ∈ A, g ^ 3 * z * (g ^ 3)⁻¹ = z)
    (hinv : ∀ z ∈ A, t * g * t⁻¹ * z * (t * g * t⁻¹)⁻¹ = g⁻¹ * z * g)
    (hgY : g ∈ Y) (htY : t ∈ Y) (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hdY : d ∈ Y)
    (hacY : ¬ (a ∈ Y ∧ c ∈ Y)) :
    g * c * g⁻¹ * c⁻¹ ∈ Subgroup.zpowers d := by
  set B := Subgroup.closure ({a, d} : Set G) with hBdef
  have hcA : c ∈ A := hA ▸ Subgroup.subset_closure (by simp)
  have haA : a ∈ A := hA ▸ Subgroup.subset_closure (by simp)
  have hdA : d ∈ A := hA ▸ Subgroup.subset_closure (by simp)
  have hBA : B ≤ A := by
    rw [hBdef, Subgroup.closure_le]
    rintro y (rfl | rfl)
    exacts [haA, hdA]
  have hc3 : c ^ 3 = 1 := hexp c hcA
  have ha3 : a ^ 3 = 1 := hexp a haA
  have hgB : ∀ b ∈ B, g * b * g⁻¹ = b := by
    intro b hb
    have hle : B ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [hBdef, Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hga.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hgd.symm
    have hbg := Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
    rw [← hbg, mul_inv_cancel_right]
  set u := g * c * g⁻¹ * c⁻¹ with hu
  obtain ⟨i, b₀, hb₀, hgc⟩ :=
    exists_zpow_mul_of_mem hcomm hA ((Subgroup.mem_normalizer_iff.mp hgA c).mp hcA)
  have hgact : ∀ (k : ℤ) (b : G), b ∈ B →
      ∃ b' ∈ B, g * (c ^ k * b) * g⁻¹ = c ^ (i * k) * b' := by
    intro k b hb
    refine ⟨b₀ ^ k * b, B.mul_mem (B.zpow_mem hb₀ k) hb, ?_⟩
    have e1 : g * (c ^ k * b) * g⁻¹ = (g * c * g⁻¹) ^ k * (g * b * g⁻¹) := by
      rw [conj_zpow]
      group
    have hcb : Commute (c ^ i) b₀ := hcomm _ (A.zpow_mem hcA i) _ (hBA hb₀)
    rw [e1, hgB b hb, hgc, hcb.mul_zpow, ← zpow_mul]
    group
  obtain ⟨b₁, hb₁, h1⟩ := hgact i b₀ hb₀
  obtain ⟨b₂, hb₂, h2⟩ := hgact (i * i) b₁ hb₁
  have h3 : c = c ^ (i * (i * i)) * b₂ := by
    have e : g ^ 3 * c * (g ^ 3)⁻¹ = g * (g * (g * c * g⁻¹) * g⁻¹) * g⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    calc c = g ^ 3 * c * (g ^ 3)⁻¹ := (hg3 c hcA).symm
      _ = g * (g * (g * c * g⁻¹) * g⁻¹) * g⁻¹ := e
      _ = c ^ (i * (i * i)) * b₂ := by rw [hgc, h1, h2]
  have hk : c ^ (1 - i * (i * i)) ∈ B := by
    have hcb₂ : Commute (c ^ (i * (i * i))) b₂ := hcomm _ (A.zpow_mem hcA _) _ (hBA hb₂)
    have e : c ^ (1 - i * (i * i)) = b₂ := by
      rw [zpow_sub, zpow_one]
      calc c * (c ^ (i * (i * i)))⁻¹ = c ^ (i * (i * i)) * b₂ * (c ^ (i * (i * i)))⁻¹ := by
            rw [← h3]
        _ = b₂ := by rw [hcb₂.eq]; group
    rw [e]
    exact hb₂
  have hi : (3 : ℤ) ∣ i - 1 := by
    refine three_dvd_sub_one_of_dvd_one_sub_cube ?_
    by_contra h3'
    exact hcad (mem_of_zpow_mem hc3 hk h3')
  have hci : c ^ i = c := by
    rw [← sub_add_cancel i 1, zpow_add, zpow_eq_one_of_dvd hc3 hi, one_mul, zpow_one]
  have hub : u = b₀ := by
    rw [hu, hgc, hci]
    calc c * b₀ * c⁻¹ = b₀ * c * c⁻¹ := by rw [hcomm c hcA b₀ (hBA hb₀)]
      _ = b₀ := by group
  have huB : u ∈ B := hub ▸ hb₀
  have huA : u ∈ A := hBA huB
  have huc : u * c = g * c * g⁻¹ := by rw [hu]; group
  have huY : u ∈ Y := by
    have hc : c * g⁻¹ * c⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hAY hcA) g⁻¹).mp (Y.inv_mem hgY)
    have e : u = g * (c * g⁻¹ * c⁻¹) := by rw [hu]; group
    rw [e]
    exact Y.mul_mem hgY hc
  obtain ⟨α, β, huab⟩ :=
    Sec12.exists_zpow_mul_zpow_of_mem_closure_pair (hcomm a haA d hdA) huB
  have hu1 : a ^ α = 1 := by
    by_contra hα
    have h3α : ¬ (3 : ℤ) ∣ α := fun h => hα (zpow_eq_one_of_dvd ha3 h)
    by_cases haY : a ∈ Y
    · have hcY : c ∉ Y := fun hc => hacY ⟨haY, hc⟩
      have hBY : B ≤ Y := by
        rw [hBdef, Subgroup.closure_le]
        rintro y (rfl | rfl)
        exacts [haY, hdY]
      have hAYB : ∀ z ∈ A, z ∈ Y → z ∈ B := by
        intro z hz hzY
        obtain ⟨k, b, hb, rfl⟩ := exists_zpow_mul_of_mem hcomm hA hz
        have hck : c ^ k ∈ Y := by
          have := Y.mul_mem hzY (Y.inv_mem (hBY hb))
          rwa [mul_inv_cancel_right] at this
        have h3k : (3 : ℤ) ∣ k := by
          by_contra h3
          exact hcY (mem_of_zpow_mem hc3 hck h3)
        rw [zpow_eq_one_of_dvd hc3 h3k, one_mul]
        exact hb
      set v := t * c * t⁻¹ * c⁻¹ with hv
      have hvA : v ∈ A := A.mul_mem ((Subgroup.mem_normalizer_iff.mp htA c).mp hcA)
        (A.inv_mem hcA)
      have hvY : v ∈ Y := by
        have hc : c * t⁻¹ * c⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp (hAY hcA) t⁻¹).mp (Y.inv_mem htY)
        have e : v = t * (c * t⁻¹ * c⁻¹) := by rw [hv]; group
        rw [e]
        exact Y.mul_mem htY hc
      have hvB : v ∈ B := hAYB v hvA hvY
      have htB : ∀ b ∈ B, t⁻¹ * b * t ∈ B := by
        have hle : B ≤ B.comap (MulAut.conj t⁻¹).toMonoidHom := by
          rw [hBdef, Subgroup.closure_le]
          rintro y (rfl | rfl)
          · change t⁻¹ * y * t⁻¹⁻¹ ∈ B
            rw [inv_inv, show t⁻¹ * y * t = y by
              rw [mul_assoc, ← hta, ← mul_assoc, inv_mul_cancel, one_mul]]
            exact Subgroup.subset_closure (by simp)
          · change t⁻¹ * y * t⁻¹⁻¹ ∈ B
            have := (Subgroup.mem_normalizer_iff.mp (inv_mem htd) y).mp (Subgroup.mem_zpowers y)
            exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) this
        intro b hb
        have := hle hb
        simpa using this
      have hv1 : t⁻¹ * v * t ∈ B := htB v hvB
      have hLHS : t * g * t⁻¹ * c * (t * g * t⁻¹)⁻¹ = t * u * t⁻¹ * c := by
        have e1 : t⁻¹ * c * t = (t⁻¹ * v * t)⁻¹ * c := by rw [hv]; group
        have e2 : g * ((t⁻¹ * v * t)⁻¹ * c) * g⁻¹ = (t⁻¹ * v * t)⁻¹ * (u * c) := by
          have hg1 := hgB _ (B.inv_mem hv1)
          calc g * ((t⁻¹ * v * t)⁻¹ * c) * g⁻¹ =
              (g * (t⁻¹ * v * t)⁻¹ * g⁻¹) * (g * c * g⁻¹) := by group
            _ = (t⁻¹ * v * t)⁻¹ * (u * c) := by rw [hg1, huc]
        have htuA : t * u * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htA u).mp huA
        have hcomm' : v⁻¹ * (t * u * t⁻¹) = (t * u * t⁻¹) * v⁻¹ :=
          hcomm _ (A.inv_mem hvA) _ htuA
        calc t * g * t⁻¹ * c * (t * g * t⁻¹)⁻¹ = t * (g * (t⁻¹ * c * t) * g⁻¹) * t⁻¹ := by
              group
          _ = t * ((t⁻¹ * v * t)⁻¹ * (u * c)) * t⁻¹ := by rw [e1, e2]
          _ = v⁻¹ * (t * u * t⁻¹) * (t * c * t⁻¹) := by group
          _ = (t * u * t⁻¹) * v⁻¹ * (v * c) := by rw [hcomm']; rw [hv]; group
          _ = t * u * t⁻¹ * c := by group
      have hRHS : g⁻¹ * c * g = u⁻¹ * c := by
        have hgu : g⁻¹ * u * g = u := by
          calc g⁻¹ * u * g = g⁻¹ * (g * u * g⁻¹) * g := by rw [hgB u huB]
            _ = u := by group
        calc g⁻¹ * c * g = u⁻¹ * (u * (g⁻¹ * c * g)) := by group
          _ = u⁻¹ * ((g⁻¹ * u * g) * (g⁻¹ * c * g)) := by rw [hgu]
          _ = u⁻¹ * (g⁻¹ * (u * c) * g) := by group
          _ = u⁻¹ * (g⁻¹ * (g * c * g⁻¹) * g) := by rw [huc]
          _ = u⁻¹ * c := by group
      have htu : t * u * t⁻¹ = u⁻¹ :=
        mul_right_cancel (hLHS.symm.trans ((hinv c hcA).trans hRHS))
      obtain ⟨ε, hε⟩ := Subgroup.mem_zpowers_iff.mp
        ((Subgroup.mem_normalizer_iff.mp htd d).mp (Subgroup.mem_zpowers d))
      have hta' : t * a * t⁻¹ = a := by rw [hta, mul_inv_cancel_right]
      have e3 : t * u * t⁻¹ = a ^ α * d ^ (ε * β) := by
        rw [huab]
        calc t * (a ^ α * d ^ β) * t⁻¹ = (t * a * t⁻¹) ^ α * (t * d * t⁻¹) ^ β := by
              rw [conj_zpow, conj_zpow]
              group
          _ = a ^ α * d ^ (ε * β) := by rw [hta', ← hε, ← zpow_mul]
      have had : Commute a d := hcomm a haA d hdA
      have e4 : a ^ α * d ^ (ε * β) = a ^ (-α) * d ^ (-β) := by
        rw [← e3, htu, huab, mul_inv_rev, ← zpow_neg, ← zpow_neg]
        exact ((had.zpow_zpow (-α) (-β)).eq).symm
      have e5 := zpow_sub_eq_zpow_sub e4
      apply hacd
      refine mem_of_zpow_mem ha3 (k := α - -α) ?_ (by omega)
      rw [e5]
      exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _
    · apply haY
      refine mem_of_zpow_mem ha3 ?_ h3α
      have e : a ^ α = u * (d ^ β)⁻¹ := by rw [huab]; group
      rw [e]
      exact Y.mul_mem huY (Y.inv_mem (Y.zpow_mem hdY β))
  rw [huab, hu1, one_mul]
  exact Subgroup.zpow_mem_zpowers d β

end ActOnA

end CFSG.RankThree.PartTwo.Sec11
