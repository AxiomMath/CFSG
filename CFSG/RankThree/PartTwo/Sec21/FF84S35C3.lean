module

public import CFSG.RankThree.PartTwo.Sec21.FF84S35
public import CFSG.RankThree.PartTwo.Sec21.FF84S35C2
public import CFSG.RankThree.PartTwo.Sec21.FF84S35C1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84.S3

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem S3.conj_eq_of_theta {θ : G → P8} (P : PreTheta L θ) (hZ : Subgroup.center L = ⊥)
    {g x y : G} (hgL : g ∈ L) (hx : x ∈ L) (hy : y ∈ L)
    (h : θ g * θ x * (θ g)⁻¹ = θ y) : g * x * g⁻¹ = y :=
  theta_inj P hZ (mul_mem (mul_mem hgL hx) (inv_mem hgL)) hy (by
    rw [P.conj (Subgroup.le_normalizer hgL) (Subgroup.le_normalizer hx)]
    exact h)

theorem S3.U₁_le_A8s : U₁ ≤ A8s := by
  rw [U₁, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · show _ ∈ alternatingGroup (Fin 8)
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide

theorem S3.pow_eq_one_two_pow_false {x : G} (hx : orderOf x = 3) {k : ℕ} (h : x ^ (2 ^ k) = 1) :
    False := by
  have h1 : 3 ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one h
  have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
  omega

theorem S3.exists_swap_b₂ (h : FF84Sec3 b L B b₁ b₂) :
    ∃ n ∈ Nor B, n * b * n⁻¹ = b₂ ∧ n * b₂ * n⁻¹ = b ∧ n * b₁ * n⁻¹ = b₁ := by
  obtain ⟨n, hn, hn'⟩ := P_monomial h (Equiv.swap 0 2) 1
  refine ⟨n, hn, ?_, ?_, ?_⟩
  · simpa using hn' 0
  · simpa using hn' 2
  · have e : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
    simpa [e] using hn' 1

section Contra

open S3

theorem F5_contra_theta (hA10 : A10Stmt) (h33 : FF84_3_3) (h : FF84Sec3 b L B b₁ b₂)
    (hZ : Subgroup.center L = ⊥) (hbL : Subgroup.zpowers b ⊓ L = ⊥)
    (hCL : Subgroup.zpowers b ⊔ L = Cen b) (hCB : CenS B = B) {θ : G → P8}
    (H : HasTheta L b₁ b₂ θ) {t : G} (htN : t ∈ Nor L) (htθ : θ t = τ₀)
    (htb : t * b * t⁻¹ = b⁻¹) (htb₁ : t * b₁ * t⁻¹ = b₁) (htb₂ : t * b₂ * t⁻¹ = b₂) :
    False := by
  have P := H.toPreTheta
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  have hbCL : b ∈ CenS L := P_b_mem_CenS h
  have hbc : ∀ l ∈ L, b * l = l * b := fun l hl =>
    (Subgroup.mem_centralizer_iff.1 hbCL l hl).symm
  obtain ⟨⟨hU₁2, -, -, hEo₁, -, -⟩, -⟩ := id hA10
  obtain ⟨s₁, s₂, hs₁A, hs₂A, -, -, hs₁m₁, hs₁m₂, hs₂m₂, hs₂m₁, hs₁N, hs₂N⟩ := A9_transvections
  obtain ⟨t₁, ht₁L, ht₁θ⟩ := P.surj s₁ hs₁A
  obtain ⟨t₂, ht₂L, ht₂θ⟩ := P.surj s₂ hs₂A
  set U := preImg P U₁ with hUdef
  have hU₁p : IsPGroup 2 U₁ := IsPGroup.of_card hU₁2.2
  have hU2 : IsPGroup 2 U := isPGroup_preImg P hZ hU₁p
  have hUne : U ≠ ⊥ := by
    have hne : U₁ ≠ ⊥ := by
      intro h0
      have := hU₁2.2
      rw [h0] at this
      simp at this
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    obtain ⟨u, huL, huθ⟩ := P.surj a (U₁_le_A8s a.2)
    intro h0
    have hu : u ∈ U := ⟨huL, by rw [huθ]; exact a.2⟩
    rw [h0, Subgroup.mem_bot] at hu
    apply ha
    apply Subtype.ext
    rw [← huθ, hu, P.one]
    rfl
  have hEoN : ∀ z ∈ Eo, z ∈ Nor U₁ := fun z hz => hEo₁ hz
  have hm₁ : m₁ ∈ Eo := Subgroup.subset_closure (by simp)
  have hm₂ : m₂ ∈ Eo := Subgroup.subset_closure (by simp)
  have hbU : b ∈ Nor U := by
    apply Subgroup.mem_normalizer_fintype
    intro u hu
    have : b * u * b⁻¹ = u := by
      rw [hbc u hu.1]; group
    rw [this]; exact hu
  have hb₁U : b₁ ∈ Nor U := nor_preImg P (Subgroup.le_normalizer hb₁L) (by
    rw [H.hb₁]; exact hEoN _ hm₁)
  have hb₂U : b₂ ∈ Nor U := nor_preImg P (Subgroup.le_normalizer hb₂L) (by
    rw [H.hb₂]; exact hEoN _ hm₂)
  have ht₁U : t₁ ∈ Nor U := nor_preImg P (Subgroup.le_normalizer ht₁L) (by rw [ht₁θ]; exact hs₁N)
  have ht₂U : t₂ ∈ Nor U := nor_preImg P (Subgroup.le_normalizer ht₂L) (by rw [ht₂θ]; exact hs₂N)
  set V : Subgroup G := Op 2 (Nor U) with hVdef
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Nor U)
  have hUV : Nor U ≤ Nor V := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Nor U)
  have hB : B = Subgroup.closure {b, b₁, b₂} := h.mono.2.1
  have hBV : B ≤ Nor V := by
    rw [hB, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hUV hbU
    · exact hUV hb₁U
    · exact hUV hb₂U
  have hb₁θ : θ b₁ = m₁ := H.hb₁
  have hb₂θ : θ b₂ = m₂ := H.hb₂
  have hinvθ : ∀ {x : G}, x ∈ L → θ x⁻¹ = (θ x)⁻¹ := fun {x} hx =>
    P.inv (Subgroup.le_normalizer hx)
  have h1b₁ : t₁ * b₁ * t₁⁻¹ = b₁⁻¹ :=
    conj_eq_of_theta P hZ ht₁L hb₁L (inv_mem hb₁L) (by
      rw [ht₁θ, hb₁θ, hinvθ hb₁L, hb₁θ]; exact hs₁m₁)
  have h1b₂ : t₁ * b₂ * t₁⁻¹ = b₂ :=
    conj_eq_of_theta P hZ ht₁L hb₂L hb₂L (by rw [ht₁θ, hb₂θ]; exact hs₁m₂)
  have h2b₂ : t₂ * b₂ * t₂⁻¹ = b₂⁻¹ :=
    conj_eq_of_theta P hZ ht₂L hb₂L (inv_mem hb₂L) (by
      rw [ht₂θ, hb₂θ, hinvθ hb₂L, hb₂θ]; exact hs₂m₂)
  have h2b₁ : t₂ * b₁ * t₂⁻¹ = b₁ :=
    conj_eq_of_theta P hZ ht₂L hb₁L hb₁L (by rw [ht₂θ, hb₁θ]; exact hs₂m₁)
  have h1b : t₁ * b * t₁⁻¹ = b := by
    have := hbc t₁ ht₁L
    rw [mul_inv_eq_iff_eq_mul, this]
  have h2b : t₂ * b * t₂⁻¹ = b := by
    have := hbc t₂ ht₂L
    rw [mul_inv_eq_iff_eq_mul, this]
  have hnoY : ∀ Y : Subgroup G, Y ≤ L → IsPGroup 2 Y → B ⊓ L ≤ Nor Y → t ∈ Nor Y → Y = ⊥ :=
    fun Y hY hY2 hBY htY =>
      F5_noY_theta hA10 P hZ H.hb₁ H.hb₂ hb₁L hb₂L htN htθ Y hY hY2 (hBY h.hb₁) (hBY h.hb₂) htY
  obtain ⟨-, -, -, -, ⟨n₁, hn₁, e1b, e1b1, e1b2⟩, -⟩ := h.mono
  obtain ⟨n₂, hn₂, e2b, e2b2, e2b1⟩ := exists_swap_b₂ h
  have hC₁ : V ⊓ Cen b₁ = ⊥ :=
    F5_Ci h hbL hCL hCB (mem_B_b₁ h) hB hn₁ e1b e1b1 e1b2 htb htb₁ htb₂ hnoY hV2 hBV
      (hUV ht₁U) h1b₁ h1b h1b₂
  have hC₂ : V ⊓ Cen b₂ = ⊥ :=
    F5_Ci h hbL hCL hCB (mem_B_b₂ h) (by rw [hB, Set.pair_comm]) hn₂ e2b e2b2 e2b1 htb htb₂ htb₁
      hnoY hV2 hBV (hUV ht₂U) h2b₂ h2b h2b₁
  have h3 := (h33 G b L B b₁ b₂ h).2.2 V hV2 hBV
  rw [hC₁, hC₂, bot_sup_eq, bot_sup_eq] at h3
  have hVb : ∀ v ∈ V, v * b = b * v := fun v hv => by
    have : v ∈ V ⊓ Cen b := by rw [h3]; exact hv
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 this).2
  have hbCV : b ∈ CenS V := Subgroup.mem_centralizer_iff.2 hVb
  have hbNU : b ∈ Nor U ⊓ CenS V := Subgroup.mem_inf.2 ⟨hbU, hbCV⟩
  have hbV : b ∈ V := B_charTwo h.hyp.char2 U hUne hU2 hbNU
  obtain ⟨k, hk⟩ := hV2 ⟨b, hbV⟩
  exact pow_eq_one_two_pow_false h.hyp.ord (k := k) (congrArg Subtype.val hk)

end Contra

theorem f5Contra_of_A10 (hA10 : A10Stmt) (h31 : FF84_3_1) (h33 : FF84_3_3) (h34 : FF84_3_4) :
    F5Contra := by
  intro G _ _ b L B b₁ b₂ hs hC t ht hb hb₁ hb₂
  obtain ⟨-, hZ⟩ := h31 G b L B b₁ b₂ hs
  obtain ⟨-, hbL, hCB⟩ := h34 G b L B b₁ b₂ hs
  obtain ⟨θ, H⟩ := S3.exists_theta hs (by rw [hZ]; simp)
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have htN : t ∈ Nor (Subgroup.zpowers b) := by
    apply Subgroup.mem_normalizer_fintype
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine Subgroup.mem_zpowers_iff.2 ⟨-k, ?_⟩
    rw [← conj_zpow, hb, zpow_neg, inv_zpow]
  have htL : t ∈ Nor L := P_Nb_normalizes_L hs htN
  have hb₁L : b₁ ∈ Nor L := Subgroup.le_normalizer (Subgroup.mem_inf.1 hs.hb₁).2
  have hb₂L : b₂ ∈ Nor L := Subgroup.le_normalizer (Subgroup.mem_inf.1 hs.hb₂).2
  rcases S3.F5_t_theta H hb₁L hb₂L htL ht2 (mul_inv_eq_iff_eq_mul.1 hb₁)
      (mul_inv_eq_iff_eq_mul.1 hb₂) with hc | hθ
  · exact hc
  · exact (F5_contra_theta hA10 h33 hs hZ hbL hC hCB H htL hθ hb hb₁ hb₂).elim

theorem ff84_3_5_of_A10 (hA10 : A10Stmt) (h31 : FF84_3_1) (h33 : FF84_3_3) (h34 : FF84_3_4) :
    FF84_3_5 :=
  ff84_3_5_of h31 h34 (f5Contra_of_A10 hA10 h31 h33 h34)

end CFSG.RankThree.PartTwo.Sec21.FF84
