module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FI
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FH

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

section Generic

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_sylow_three_of_card_six_ch615 {F : Subgroup Γ} (h6 : Nat.card F = 6) :
    ∃ P : Subgroup Γ, P ≤ F ∧ Nat.card P = 3 ∧ ∀ x ∈ F, x ^ 3 = 1 → x ∈ P := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 ↥F) := Sylow.nonempty
  have hQ : Nat.card Q = 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have hdvd : 3 ^ k ∣ 6 := hk ▸ h6 ▸ Subgroup.card_subgroup_dvd_card (Q : Subgroup ↥F)
    have hk1 : k ≤ 1 := by
      by_contra h
      have : 3 ^ 2 ∣ 6 := (Nat.pow_dvd_pow 3 (by omega)).trans hdvd
      omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply Q.not_dvd_index
      have := (Q : Subgroup ↥F).index_mul_card
      rw [hk, pow_zero, mul_one, h6] at this
      rw [this]
      norm_num
    rw [hk, show k = 1 by omega, pow_one]
  have hidx : (Q : Subgroup ↥F).index = 2 := by
    have := (Q : Subgroup ↥F).index_mul_card
    rw [hQ, h6] at this
    omega
  have hcard := card_sylow_modEq_one 3 ↥F
  have hdvd := Sylow.card_dvd_index Q
  rw [hidx] at hdvd
  have h1 : Nat.card (Sylow 3 ↥F) = 1 := by
    have hle : Nat.card (Sylow 3 ↥F) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 3 ↥F) := Nat.card_pos
    unfold Nat.ModEq at hcard
    omega
  have hsub : Subsingleton (Sylow 3 ↥F) := (Nat.card_eq_one_iff_unique.mp h1).1
  refine ⟨(Q : Subgroup ↥F).map F.subtype, Subgroup.map_subtype_le _, by
    rw [Subgroup.card_map_of_injective F.subtype_injective, hQ], fun x hx hx3 => ?_⟩
  have hx3' : (⟨x, hx⟩ : ↥F) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hP : IsPGroup 3 (Subgroup.zpowers (⟨x, hx⟩ : ↥F)) :=
    IsPGroup.of_card (n := (orderOf (⟨x, hx⟩ : ↥F)).factorization 3) (by
      rw [Nat.card_zpowers]
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3') with h | h
      · rw [h]; simp
      · rw [h]; simp [Nat.Prime.factorization_self Nat.prime_three])
  obtain ⟨Q', hQ'⟩ := hP.exists_le_sylow
  have hQQ : Q' = Q := Subsingleton.elim _ _
  rw [hQQ] at hQ'
  exact ⟨⟨x, hx⟩, hQ' (Subgroup.mem_zpowers _), rfl⟩

omit [Finite Γ] in
theorem commutatorElement_mul_ch615 {G₁ G₂ : Subgroup Γ}
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) {a a' b b' : Γ} (ha : a ∈ G₁) (ha' : a' ∈ G₁)
    (hb : b ∈ G₂) (hb' : b' ∈ G₂) : ⁅a * b, a' * b'⁆ = ⁅a, a'⁆ * ⁅b, b'⁆ := by
  simp only [commutatorElement_def]
  have h1 := hc a' ha' b hb
  have h7 := hc a⁻¹ (G₁.inv_mem ha) b'⁻¹ (G₂.inv_mem hb')
  calc a * b * (a' * b') * (a * b)⁻¹ * (a' * b')⁻¹
      = a * (b * a') * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by group
    _ = a * (a' * b) * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by rw [h1]
    _ = a * a' * (b * b' * b⁻¹) * (a⁻¹ * b'⁻¹) * a'⁻¹ := by group
    _ = a * a' * (b * b' * b⁻¹) * (b'⁻¹ * a⁻¹) * a'⁻¹ := by rw [h7]
    _ = a * a' * (b * b' * b⁻¹ * b'⁻¹) * (a⁻¹ * a'⁻¹) := by group
    _ = a * a' * a⁻¹ * a'⁻¹ * (b * b' * b⁻¹ * b'⁻¹) := by
        have hc' : ∀ x ∈ G₁, ∀ y ∈ G₂, y * x = x * y := fun x hx y hy => (hc x hx y hy).symm
        have hy : b * b' * b⁻¹ * b'⁻¹ ∈ G₂ :=
          G₂.mul_mem (G₂.mul_mem (G₂.mul_mem hb hb') (G₂.inv_mem hb)) (G₂.inv_mem hb')
        have hx : a⁻¹ * a'⁻¹ ∈ G₁ := G₁.mul_mem (G₁.inv_mem ha) (G₁.inv_mem ha')
        rw [mul_assoc (a * a'), hc' _ hx _ hy]
        group

end Generic

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

theorem mem_fixV_of_conj_ch615 {W : Type*} [CommGroup W] {F : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ Subgroup.normalizer (F : Set (MulAut W))) {w : W} (hw : w ∈ fixV F) :
    t w ∈ fixV F :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer ht hw

namespace Cx615C

theorem false_of_le_factor_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hfF : FactorFacts_ch615 F)
    (hTF : autI hU T ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hDF : autI hU D ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hKF : autI hU (oTwoUpper H) ≤ F) (hS : IsSylowTwoOf (autI hU T ⊓ F) F)
    (hKJ : autI hU (oTwoUpper H) ≤ ⁅autI hU (oTwoUpper H), autI hU T ⊓ F⁆)
    (hfix : fixV F ≠ ⊥) : False := by
  classical
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hHN : H ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_sup_right.trans hXN
  have hKne := c.autI_oTwoUpper_ne_bot_ch615 hU
  have hgen : ∀ x ∈ H, Odd (orderOf x) → ∀ hxN : x ∈ Subgroup.normalizer (UX615 T L H : Set G),
      convI hU ⟨x, hxN⟩ ∈ autI hU (oTwoUpper H) ∧ Odd (orderOf (convI hU ⟨x, hxN⟩)) :=
    fun x hxH hxo hxN => ⟨convI_mem_autI hU (mem_oTwoUpper_of_odd hxH hxo) hxN,
      Odd.of_dvd_nat hxo (by
        have := orderOf_map_dvd (convI hU) ⟨x, hxN⟩
        rwa [Subgroup.orderOf_mk] at this)⟩
  have hKle : ∀ C : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      (∀ y ∈ autI hU (oTwoUpper H), Odd (orderOf y) → y ∈ C) → autI hU (oTwoUpper H) ≤ C := by
    intro C hC
    refine autI_le_of_le_preI615 ((Subgroup.closure_le _).mpr ?_)
    rintro x ⟨hxH, hxo⟩
    obtain ⟨h1, h2⟩ := hgen x hxH hxo (hHN hxH)
    exact mem_preI615 (hHN hxH) (hC _ h1 h2)
  rcases hfF.kind with h6 | hB | hC
  ·
    obtain ⟨P, hPF, hP3, hPx⟩ := exists_sylow_three_of_card_six_ch615 h6
    have hKP : autI hU (oTwoUpper H) ≤ P := hKle P fun y hy hyo => by
      refine hPx y (hKF hy) (orderOf_dvd_iff_pow_eq_one.mp ?_)
      have h6' : orderOf y ∣ 6 := h6 ▸ Subgroup.orderOf_dvd_natCard F (hKF hy)
      exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hyo)
        (by simpa using h6'))
    have hKeq : autI hU (oTwoUpper H) = P := by
      have hdvd : Nat.card (autI hU (oTwoUpper H)) ∣ 3 := hP3 ▸ Subgroup.card_dvd_of_le hKP
      have hne : Nat.card (autI hU (oTwoUpper H)) ≠ 1 := fun h1 =>
        hKne (Subgroup.eq_bot_of_card_eq _ h1)
      have h3 : Nat.card (autI hU (oTwoUpper H)) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd h hne
        · exact h
      exact Subgroup.eq_of_le_of_card_ge hKP (by rw [h3, hP3])
    apply c.not_hall_normalizes_ch615 hU hD hN
    intro y hy k hk
    rw [hKeq] at hk ⊢
    refine hPx _ ((Subgroup.mem_normalizer_iff.mp (hDF hy) k).mp (hPF hk)) ?_
    have hk3 : k ^ 3 = 1 := by
      rw [← hP3]
      exact (Subgroup.orderOf_dvd_natCard P hk).trans (by rfl) |> orderOf_dvd_iff_pow_eq_one.mp
    rw [conj_pow, hk3, mul_one, mul_inv_cancel]
  ·
    obtain ⟨-, hout, hNS, hself⟩ := hB
    by_cases hDc : autI hU D ≤ Subgroup.centralizer (F : Set (MulAut _))
    · apply c.not_hall_normalizes_ch615 hU hD hN
      intro y hy k hk
      rw [← Subgroup.mem_centralizer_iff.mp (hDc hy) k (hKF hk), mul_inv_cancel_right]
      exact hk
    have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
      have hodd : Odd (Nat.card (autI hU D)) := by
        rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
        exact hD.2.1
      exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
    obtain ⟨d, hdD, hdF, hd1, -⟩ := exists_mem_of_not_le_centralizer_ch615 hout hfF.center
      hS.isPGroup hS.le (hNS _ hS) (hself _ hS) (inf_le_left.trans (autI_mono hU le_sup_right))
      (autI_mono hU (hD.1.trans le_sup_left)) (c.isSolvable_autI_ch615 hU) hDF hDsodd
      (fun y hy ho => c.mem_autI_borelL_of_odd_ch615 hU hy ho)
      (fun p hp hp2 x hx y hy hxp hyp hxy hx1 =>
        c.mem_zpowers_of_autI_borelL_prime_ch615 hU hp hp2 hx hy hxp hyp hxy hx1) hDc
    obtain ⟨w, hwF, hw1, hwT⟩ := exists_fix_ch615 IntMod.sq_eq_one (c.isPGroup_autI_ch615 hU)
      hfix fun t ht w hw => mem_fixV_of_conj_ch615 (hTF ht) hw
    exact c.false_of_fix_ch615 h432 hU hD hw1 hwT (fun k hk => hwF k (hKF hk)) hdD hd1
      (hwF d hdF)
  ·
    obtain ⟨-, hBor⟩ := hC
    have hTK : autI hU T ⊓ F ≤ Subgroup.normalizer (autI hU (oTwoUpper H) : Set (MulAut _)) := by
      have hTK' : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
        c.hH.1.1.trans (le_normalizer_oTwoUpper H)
      intro y hy
      refine Subgroup.mem_normalizer_iff.mpr fun a =>
        ⟨fun ha => C124.autI_conj_mem hU hTK' y hy.1 a ha, fun ha => ?_⟩
      have := C124.autI_conj_mem hU hTK' y⁻¹ ((autI hU T).inv_mem hy.1) _ ha
      simpa [mul_assoc] using this
    have hKs := c.isSolvable_autI_oTwoUpper_ch615 hU
    have hT2s : Group.IsSolvable ↥(autI hU T ⊓ F) := by
      have := hS.isPGroup.isNilpotent
      infer_instance
    have hRs : Group.IsSolvable ↥(autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F)) :=
      A3.isSolvable_sup_of_le_normalizer hTK
    have hnorm := hBor _ hS _ le_sup_right (sup_le hKF inf_le_right) hRs
    have hKT : autI hU (oTwoUpper H) ≤ autI hU T ⊓ F := by
      refine hKJ.trans (Subgroup.commutator_le.mpr fun k hk s hs => ?_)
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (hnorm k (Subgroup.mem_sup_left hk) s hs)
        (Subgroup.inv_mem _ hs)
    apply hKne
    rw [eq_bot_iff]
    refine hKle ⊥ fun y hy hyo => ?_
    exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_mem_l32_ch615 hS.isPGroup (hKT hy) hyo)

theorem false_of_swap_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    {G₁ G₂ : Subgroup (MulAut (IntMod (UX615 T L H) hU))}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hinf : G₁ ⊓ G₂ = ⊥)
    (hf₁ : FactorFacts_ch615 G₁)
    {t : MulAut (IntMod (UX615 T L H) hU)} (htT : t ∈ autI hU T)
    (ht₁ : G₁.map (MulAut.conj t).toMonoidHom = G₂) (ht₂ : G₂.map (MulAut.conj t).toMonoidHom = G₁)
    (hD₁ : autI hU D ≤ Subgroup.normalizer (G₁ : Set (MulAut _)))
    (hD₂ : autI hU D ≤ Subgroup.normalizer (G₂ : Set (MulAut _)))
    (hKG : autI hU (oTwoUpper H) ≤ G₁ ⊔ G₂)
    (hsplit : autI hU (oTwoUpper H) ≤
      (autI hU (oTwoUpper H) ⊓ G₁) ⊔ (autI hU (oTwoUpper H) ⊓ G₂))
    (hS₁ : IsSylowTwoOf (autI hU T ⊓ G₁) G₁)
    (hJ : autI hU (thompsonJ T) ≤ (autI hU T ⊓ G₁) ⊔ (autI hU T ⊓ G₂)) : False := by
  classical
  set Ks := autI hU (oTwoUpper H) with hKs
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hHN : H ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_sup_right.trans hXN
  have hKne := c.autI_oTwoUpper_ne_bot_ch615 hU
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hTK : autI hU T ≤ Subgroup.normalizer (Ks : Set (MulAut _)) := by
    have hTK' : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
      c.hH.1.1.trans (le_normalizer_oTwoUpper H)
    intro y hy
    refine Subgroup.mem_normalizer_iff.mpr fun a =>
      ⟨fun ha => C124.autI_conj_mem hU hTK' y hy a ha, fun ha => ?_⟩
    have := C124.autI_conj_mem hU hTK' y⁻¹ ((autI hU T).inv_mem hy) _ ha
    simpa [mul_assoc] using this
  have hmem₁ : ∀ x ∈ G₁, t * x * t⁻¹ ∈ G₂ := fun x hx => by rw [← ht₁]; exact ⟨x, hx, rfl⟩
  have hmem₂ : ∀ x ∈ G₂, t * x * t⁻¹ ∈ G₁ := fun x hx => by rw [← ht₂]; exact ⟨x, hx, rfl⟩
  have hmem₂' : ∀ x ∈ G₂, t⁻¹ * x * t ∈ G₁ := fun x hx => by
    rw [← ht₁] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simpa [mul_assoc] using hy
  have hKt : ∀ k ∈ Ks, t * k * t⁻¹ ∈ Ks := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp (hTK htT) k).mp hk
  have hKt' : ∀ k ∈ Ks, t⁻¹ * k * t ∈ Ks := fun k hk => by
    have := (Subgroup.mem_normalizer_iff.mp (hTK ((autI hU T).inv_mem htT)) k).mp hk
    simpa using this
  have hKle : ∀ C : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      (∀ y ∈ Ks, Odd (orderOf y) → y ∈ C) → Ks ≤ C := by
    intro C hC
    refine autI_le_of_le_preI615 ((Subgroup.closure_le _).mpr ?_)
    rintro x ⟨hxH, hxo⟩
    have hxN := hHN hxH
    refine mem_preI615 hxN (hC _ (convI_mem_autI hU (mem_oTwoUpper_of_odd hxH hxo) hxN) ?_)
    have := orderOf_map_dvd (convI hU) ⟨x, hxN⟩
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hxo this
  have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
    have hodd : Odd (Nat.card (autI hU D)) := by
      rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
      exact hD.2.1
    exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
  have hnotc : ¬ (autI hU D ≤ Subgroup.centralizer (G₁ : Set (MulAut _)) ∧
      autI hU D ≤ Subgroup.centralizer (G₂ : Set (MulAut _))) := by
    rintro ⟨h1, h2⟩
    apply c.not_hall_normalizes_ch615 hU hD hN
    intro y hy k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute_ch615 hcomm).mp (hKG hk)
    have hya := Subgroup.mem_centralizer_iff.mp (h1 hy) a ha
    have hyb := Subgroup.mem_centralizer_iff.mp (h2 hy) b hb
    have : y * (a * b) * y⁻¹ = a * b := by
      calc y * (a * b) * y⁻¹ = (y * a) * b * y⁻¹ := by group
        _ = (a * y) * b * y⁻¹ := by rw [hya]
        _ = a * (y * b) * y⁻¹ := by group
        _ = a * (b * y) * y⁻¹ := by rw [hyb]
        _ = a * b := by group
    rw [this]
    exact hk
  rcases hf₁.kind with h6 | hB | hC
  ·
    obtain ⟨P₁, hP₁G, hP₁3, hP₁x⟩ := exists_sylow_three_of_card_six_ch615 h6
    set P₂ := P₁.map (MulAut.conj t).toMonoidHom with hP₂
    have hP₂G : P₂ ≤ G₂ := by rintro _ ⟨x, hx, rfl⟩; exact hmem₁ x (hP₁G hx)
    have hP₂3 : Nat.card P₂ = 3 := by
      rw [hP₂, Subgroup.card_map_of_injective (MulAut.conj t).injective, hP₁3]
    have hP₂x : ∀ x ∈ G₂, x ^ 3 = 1 → x ∈ P₂ := by
      intro x hx hx3
      have h1 := hP₁x _ (hmem₂' x hx) (by
        rw [show t⁻¹ * x * t = t⁻¹ * x * t⁻¹⁻¹ by rw [inv_inv], conj_pow, hx3]
        group)
      refine ⟨_, h1, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h6₂ : Nat.card G₂ = 6 := by
      rw [← ht₁, Subgroup.card_map_of_injective (MulAut.conj t).injective, h6]
    have hcube : ∀ (Gi : Subgroup (MulAut (IntMod (UX615 T L H) hU))), Nat.card Gi = 6 →
        ∀ a ∈ Gi, Odd (orderOf a) → a ^ 3 = 1 := by
      intro Gi hGi a ha hao
      refine orderOf_dvd_iff_pow_eq_one.mp ?_
      have h6' : orderOf a ∣ 6 := hGi ▸ Subgroup.orderOf_dvd_natCard Gi ha
      exact (Nat.coprime_two_right.mpr hao).dvd_of_dvd_mul_left (by simpa using h6')
    have hKP : Ks ≤ P₁ ⊔ P₂ := hKle _ fun y hy hyo => by
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute_ch615 hcomm).mp (hKG hy)
      have hab : (a * b) ^ orderOf (a * b) = 1 := pow_orderOf_eq_one _
      rw [(show Commute a b from hcomm a ha b hb).mul_pow] at hab
      have hu := Lin2.unique_decomp hinf (G₁.pow_mem ha _) G₁.one_mem (G₂.pow_mem hb _) G₂.one_mem
        (hab.trans (mul_one 1).symm)
      have hao : Odd (orderOf a) := Odd.of_dvd_nat hyo (orderOf_dvd_of_pow_eq_one hu.1)
      have hbo : Odd (orderOf b) := Odd.of_dvd_nat hyo (orderOf_dvd_of_pow_eq_one hu.2)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hP₁x a ha (hcube G₁ h6 a ha hao)))
        (Subgroup.mem_sup_right (hP₂x b hb (hcube G₂ h6₂ b hb hbo)))
    have hKGi : ∀ (Gi Gj Pi Pj : Subgroup (MulAut (IntMod (UX615 T L H) hU))),
        Gi ⊓ Gj = ⊥ → (∀ a ∈ Gi, ∀ b ∈ Gj, a * b = b * a) → Pi ≤ Gi → Pj ≤ Gj →
        Ks ≤ Pi ⊔ Pj → Ks ⊓ Gi ≤ Pi := by
      rintro Gi Gj Pi Pj hij hcij hPi hPj hK x ⟨hxK, hxG⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute_ch615
        (fun a ha b hb => hcij a (hPi ha) b (hPj hb))).mp (hK hxK)
      have hu := Lin2.unique_decomp hij (hPi ha) hxG (hPj hb) Gj.one_mem (mul_one (a * b)).symm
      rw [hu.2, mul_one]
      exact ha
    have hK₁ : Ks ⊓ G₁ ≤ P₁ := hKGi G₁ G₂ P₁ P₂ hinf hcomm hP₁G hP₂G hKP
    have hK₂ : Ks ⊓ G₂ ≤ P₂ := hKGi G₂ G₁ P₂ P₁ (by rw [inf_comm]; exact hinf) hc' hP₂G hP₁G
      (by rw [sup_comm]; exact hKP)
    have hne₁ : Ks ⊓ G₁ ≠ ⊥ := by
      intro h1
      apply hKne
      rw [eq_bot_iff]
      refine hsplit.trans (sup_le (le_of_eq h1) ?_)
      rintro y ⟨hyK, hyG⟩
      have : t⁻¹ * y * t ∈ Ks ⊓ G₁ := ⟨hKt' y hyK, hmem₂' y hyG⟩
      rw [h1, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      calc y = t * (t⁻¹ * y * t) * t⁻¹ := by group
        _ = 1 := by rw [this]; group
    have hne₂ : Ks ⊓ G₂ ≠ ⊥ := by
      intro h2
      apply hne₁
      rw [eq_bot_iff]
      rintro y ⟨hyK, hyG⟩
      have : t * y * t⁻¹ ∈ Ks ⊓ G₂ := ⟨hKt y hyK, hmem₁ y hyG⟩
      rw [h2, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
        _ = 1 := by rw [this]; group
    have heq : ∀ (A P : Subgroup (MulAut (IntMod (UX615 T L H) hU))), A ≤ P → Nat.card P = 3 →
        A ≠ ⊥ → A = P := by
      intro A P hAP hP3 hA
      have hdvd : Nat.card A ∣ 3 := hP3 ▸ Subgroup.card_dvd_of_le hAP
      have hne : Nat.card A ≠ 1 := fun h1 => hA (Subgroup.eq_bot_of_card_eq _ h1)
      have h3 : Nat.card A = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd h hne
        · exact h
      exact Subgroup.eq_of_le_of_card_ge hAP (by rw [h3, hP3])
    have hKeq : Ks = P₁ ⊔ P₂ := by
      refine le_antisymm hKP (sup_le ?_ ?_)
      · rw [← heq _ _ hK₁ hP₁3 hne₁]
        exact inf_le_left
      · rw [← heq _ _ hK₂ hP₂3 hne₂]
        exact inf_le_left
    have hDP : ∀ (Gi Pi : Subgroup (MulAut (IntMod (UX615 T L H) hU))),
        autI hU D ≤ Subgroup.normalizer (Gi : Set (MulAut _)) → Pi ≤ Gi →
        (∀ x ∈ Gi, x ^ 3 = 1 → x ∈ Pi) → Nat.card Pi = 3 → ∀ y ∈ autI hU D, ∀ x ∈ Pi,
          y * x * y⁻¹ ∈ Pi := by
      intro Gi Pi hDi hPi hPix hPi3 y hy x hx
      refine hPix _ ((Subgroup.mem_normalizer_iff.mp (hDi hy) x).mp (hPi hx)) ?_
      have hx3 : x ^ 3 = 1 := by
        rw [← hPi3]
        exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard Pi hx)
      rw [conj_pow, hx3, mul_one, mul_inv_cancel]
    apply c.not_hall_normalizes_ch615 hU hD hN
    intro y hy k hk
    change k ∈ Ks at hk
    change y * k * y⁻¹ ∈ Ks
    rw [hKeq] at hk ⊢
    have hn₁ := mem_normalizer_of_conj_mem_l32_ch615 (hDP G₁ P₁ hD₁ hP₁G hP₁x hP₁3 y hy)
    have hn₂ := mem_normalizer_of_conj_mem_l32_ch615 (hDP G₂ P₂ hD₂ hP₂G hP₂x hP₂3 y hy)
    have hn : y ∈ Subgroup.normalizer ((P₁ ⊔ P₂ : Subgroup _) : Set (MulAut _)) := by
      have hle : P₁ ⊔ P₂ ≤ (P₁ ⊔ P₂).map (MulAut.conj y⁻¹).toMonoidHom := by
        refine sup_le (fun x hx => ⟨y * x * y⁻¹, Subgroup.mem_sup_left
          ((Subgroup.mem_normalizer_iff.mp hn₁ x).mp hx), by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩)
          (fun x hx => ⟨y * x * y⁻¹, Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp hn₂ x).mp hx), by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩)
      refine mem_normalizer_of_conj_mem_l32_ch615 fun x hx => ?_
      obtain ⟨z, hz, rfl⟩ := hle hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have : y * (y⁻¹ * z * y⁻¹⁻¹) * y⁻¹ = z := by group
      rw [this]
      exact hz
    exact (Subgroup.mem_normalizer_iff.mp hn k).mp hk
  ·
    obtain ⟨-, hout, hNS, hself⟩ := hB
    have hYt : t ∈ autI hU (borelL T L ⊔ T) := autI_mono hU le_sup_right htT
    have key : ∀ D' : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
        D' ≤ autI hU (borelL T L ⊔ T) → D' ≤ Subgroup.normalizer (G₁ : Set (MulAut _)) →
        (∀ d ∈ D', Odd (orderOf d)) → ¬ D' ≤ Subgroup.centralizer (G₁ : Set (MulAut _)) →
        False := by
      intro D' hD'Y hD'N hD'odd hD'c
      obtain ⟨d, hdD, hdG, hd1, p, hp, hp2, hdp⟩ := exists_mem_of_not_le_centralizer_ch615 hout
        hf₁.center hS₁.isPGroup hS₁.le (hNS _ hS₁) (hself _ hS₁)
        (inf_le_left.trans (autI_mono hU le_sup_right)) hD'Y (c.isSolvable_autI_ch615 hU) hD'N
        hD'odd (fun y hy ho => c.mem_autI_borelL_of_odd_ch615 hU hy ho)
        (fun p hp hp2 x hx y hy hxp hyp hxy hx1 =>
          c.mem_zpowers_of_autI_borelL_prime_ch615 hU hp hp2 hx hy hxp hyp hxy hx1) hD'c
      have heG : t * d * t⁻¹ ∈ G₂ := hmem₁ d hdG
      have heY : t * d * t⁻¹ ∈ autI hU (borelL T L ⊔ T) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hYt (hD'Y hdD)) (Subgroup.inv_mem _ hYt)
      have hep : (t * d * t⁻¹) ^ p = 1 := by rw [conj_pow, hdp, mul_one, mul_inv_cancel]
      have heo : Odd (orderOf (t * d * t⁻¹)) :=
        Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hep)
      have hdB := c.mem_autI_borelL_of_odd_ch615 hU (hD'Y hdD) (hD'odd d hdD)
      have heB := c.mem_autI_borelL_of_odd_ch615 hU heY heo
      have hz := c.mem_zpowers_of_autI_borelL_prime_ch615 hU hp hp2 hdB heB hdp hep
        (hcomm d hdG _ heG) hd1
      have h1 : t * d * t⁻¹ ∈ G₁ ⊓ G₂ := ⟨(Subgroup.zpowers_le.mpr hdG) hz, heG⟩
      rw [hinf, Subgroup.mem_bot] at h1
      apply hd1
      calc d = t⁻¹ * (t * d * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group
    by_cases hc1 : autI hU D ≤ Subgroup.centralizer (G₁ : Set (MulAut _))
    · have hc2 : ¬ autI hU D ≤ Subgroup.centralizer (G₂ : Set (MulAut _)) := fun hc2 =>
        hnotc ⟨hc1, hc2⟩
      refine key ((autI hU D).map (MulAut.conj t⁻¹).toMonoidHom) ?_ ?_ ?_ ?_
      · rintro _ ⟨d, hd, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hYt)
          (autI_mono hU (hD.1.trans le_sup_left) hd)) hYt
      · rintro _ ⟨d, hd, rfl⟩
        refine mem_normalizer_of_conj_mem_l32_ch615 fun x hx => ?_
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        have h1 := hmem₁ x hx
        have h2 := (Subgroup.mem_normalizer_iff.mp (hD₂ hd) _).mp h1
        have h3 := hmem₂' _ h2
        have e : t⁻¹ * d * t * x * (t⁻¹ * d * t)⁻¹ = t⁻¹ * (d * (t * x * t⁻¹) * d⁻¹) * t := by
          group
        rw [e]
        exact h3
      · rintro _ ⟨d, hd, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
        exact hDsodd d hd
      · intro hle
        apply hc2
        intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 := Subgroup.mem_centralizer_iff.mp (hle ⟨d, hd, rfl⟩) _ (hmem₂' x hx)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
        have h2 : t * (t⁻¹ * x * t * (t⁻¹ * d * t)) * t⁻¹ =
            t * (t⁻¹ * d * t * (t⁻¹ * x * t)) * t⁻¹ := by rw [h1]
        simpa [mul_assoc] using h2
    · exact key (autI hU D) (autI_mono hU (hD.1.trans le_sup_left)) hD₁ hDsodd hc1
  ·
    obtain ⟨-, hBor⟩ := hC
    have hKs := c.isSolvable_autI_oTwoUpper_ch615 hU
    have hA₁s : Group.IsSolvable ↥(Ks ⊓ G₁) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
        (inf_le_left : Ks ⊓ G₁ ≤ Ks))
    have hS₁s : Group.IsSolvable ↥(autI hU T ⊓ G₁) := by
      have := hS₁.isPGroup.isNilpotent
      infer_instance
    have hS₁N : autI hU T ⊓ G₁ ≤ Subgroup.normalizer ((Ks ⊓ G₁ : Subgroup _) : Set (MulAut _)) :=
      fun s hs => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hTK hs.1, Subgroup.le_normalizer hs.2⟩
    have hR₁s : Group.IsSolvable ↥((Ks ⊓ G₁) ⊔ (autI hU T ⊓ G₁)) :=
      A3.isSolvable_sup_of_le_normalizer hS₁N
    have hB₁ := hBor _ hS₁ _ le_sup_right (sup_le inf_le_right inf_le_right) hR₁s
    have hc₁ : ∀ k ∈ Ks ⊓ G₁, ∀ s ∈ autI hU T ⊓ G₁, ⁅k, s⁆ ∈ autI hU T ⊓ G₁ := by
      intro k hk s hs
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (hB₁ k (Subgroup.mem_sup_left hk) s hs) (Subgroup.inv_mem _ hs)
    have hc₂ : ∀ k ∈ Ks ⊓ G₂, ∀ s ∈ autI hU T ⊓ G₂, ⁅k, s⁆ ∈ autI hU T ⊓ G₂ := by
      intro k hk s hs
      have hk' : t⁻¹ * k * t ∈ Ks ⊓ G₁ := ⟨hKt' k hk.1, hmem₂' k hk.2⟩
      have hs' : t⁻¹ * s * t ∈ autI hU T ⊓ G₁ :=
        ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ((autI hU T).inv_mem htT) hs.1) htT,
          hmem₂' s hs.2⟩
      have h1 := hc₁ _ hk' _ hs'
      have e : ⁅k, s⁆ = t * ⁅t⁻¹ * k * t, t⁻¹ * s * t⁆ * t⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ htT h1.1) ((autI hU T).inv_mem htT),
        hmem₁ _ h1.2⟩
    have hKT : Ks ≤ autI hU T := by
      refine (c.le_commutator_ch615 hU).trans (Subgroup.commutator_le.mpr fun k hk j hj => ?_)
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_sup_iff_of_commute_ch615
        (fun a ha b hb => hcomm a (Subgroup.mem_inf.mp ha).2 b (Subgroup.mem_inf.mp hb).2)).mp
        (hsplit hk)
      obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := (mem_sup_iff_of_commute_ch615
        (fun a ha b hb => hcomm a (Subgroup.mem_inf.mp ha).2 b (Subgroup.mem_inf.mp hb).2)).mp
        (hJ hj)
      rw [commutatorElement_mul_ch615 hcomm (Subgroup.mem_inf.mp hk₁).2
        (Subgroup.mem_inf.mp hs₁).2 (Subgroup.mem_inf.mp hk₂).2 (Subgroup.mem_inf.mp hs₂).2]
      exact Subgroup.mul_mem _ (hc₁ k₁ hk₁ s₁ hs₁).1 (hc₂ k₂ hk₂ s₂ hs₂).1
    apply hKne
    rw [eq_bot_iff]
    refine hKle ⊥ fun y hy hyo => ?_
    exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_mem_l32_ch615 (c.isPGroup_autI_ch615 hU)
      (hKT hy) hyo)

theorem false_of_b56Case3_ch615 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2)
    (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hF : ∀ F : Subgroup (MulAut (IntMod (UX615 T L H) hU)), B56FactorList ↥F →
      FactorFacts_ch615 F)
    (h3 : B56Case3 (ffJ (autI hU (borelL T L ⊔ H)))) : False := by
  classical
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, hl₁, hl₂, W₁, W₂, -, -, -, -, -, hW, hp₁, hp₂⟩ := h3
  have hf₁ := hF G₁ hl₁
  have hf₂ := hF G₂ hl₂
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hinf' : G₂ ⊓ G₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hTsX : autI hU T ≤ autI hU (borelL T L ⊔ H) := autI_mono hU (c.hH.1.1.trans le_sup_right)
  have hDsY : autI hU D ≤ autI hU (borelL T L ⊔ T) := autI_mono hU (hD.1.trans le_sup_left)
  have hYsX : autI hU (borelL T L ⊔ T) ≤ autI hU (borelL T L ⊔ H) :=
    autI_mono hU (sup_le le_sup_left (c.hH.1.1.trans le_sup_right))
  have hGsX : G₁ ⊔ G₂ ≤ autI hU (borelL T L ⊔ H) := hsup ▸ B6.ffJ_le _
  have hnorm : ∀ x ∈ autI hU (borelL T L ⊔ H),
      x ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup _) : Set (MulAut _)) := fun x hx =>
    hsup ▸ B6.le_normalizer_ffJ _ hx
  have hKG : autI hU (oTwoUpper H) ≤ G₁ ⊔ G₂ := hsup ▸ (c.le_ffJ_ch615 hU).2
  have hJG : autI hU (thompsonJ T) ≤ G₁ ⊔ G₂ := hsup ▸ (c.le_ffJ_ch615 hU).1
  have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
    have hodd : Odd (Nat.card (autI hU D)) := by
      rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
      exact hD.2.1
    exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
  have hGsn : ((G₁ ⊔ G₂).subgroupOf (autI hU (borelL T L ⊔ H))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hGsX).mpr fun x hx => hnorm x hx
  have hP : IsSylowTwoOf (autI hU T ⊓ (G₁ ⊔ G₂)) (G₁ ⊔ G₂) :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (c.isSylowTwoOf_autI_ch615 hU) hGsX
      hGsn.isSubnormal
  have hn₁ : (G₁.subgroupOf (G₁ ⊔ G₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le_normalizer_ch615 hcomm)
  have hn₂ : (G₂.subgroupOf (G₁ ⊔ G₂)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr ?_
    rw [sup_comm]
    exact sup_le_normalizer_ch615 hc'
  have hS : ∀ Gi : Subgroup (MulAut (IntMod (UX615 T L H) hU)), Gi ≤ G₁ ⊔ G₂ →
      (Gi.subgroupOf (G₁ ⊔ G₂)).Normal → IsSylowTwoOf (autI hU T ⊓ Gi) Gi := by
    intro Gi hGi hn
    have := RankOneRecog.isSylowTwoOf_inf_of_subnormal hP hGi hn.isSubnormal
    rwa [inf_assoc, inf_eq_right.mpr hGi] at this
  have hS₁ := hS G₁ le_sup_left hn₁
  have hS₂ := hS G₂ le_sup_right hn₂
  have hJsplit : autI hU (thompsonJ T) ≤ (autI hU T ⊓ G₁) ⊔ (autI hU T ⊓ G₂) := by
    exact ((le_inf (autI_mono hU (thompsonJ_le_self T)) hJG).trans
      (le_sup_inf_of_isSylowTwoOf_ch615 hcomm hinf hP)).trans
      (sup_le_sup (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_left))
  have hTK : autI hU T ≤ Subgroup.normalizer (autI hU (oTwoUpper H) : Set (MulAut _)) := by
    have hTK' : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
      c.hH.1.1.trans (le_normalizer_oTwoUpper H)
    intro y hy
    refine Subgroup.mem_normalizer_iff.mpr fun a =>
      ⟨fun ha => C124.autI_conj_mem hU hTK' y hy a ha, fun ha => ?_⟩
    have := C124.autI_conj_mem hU hTK' y⁻¹ ((autI hU T).inv_mem hy) _ ha
    simpa [mul_assoc] using this
  have hsplit : autI hU (oTwoUpper H) ≤
      (autI hU (oTwoUpper H) ⊓ G₁) ⊔ (autI hU (oTwoUpper H) ⊓ G₂) :=
    (c.le_commutator_ch615 hU).trans (commutator_le_sup_inf_ch615 hcomm
      (P := autI hU T ⊓ (G₁ ⊔ G₂)) hKG ((le_inf (autI_mono hU (thompsonJ_le_self T)) hJG).trans
        (le_sup_inf_of_isSylowTwoOf_ch615 hcomm hinf hP)) (inf_le_left.trans hTK))
  have hcW : ∀ (Gi : Subgroup (MulAut (IntMod (UX615 T L H) hU))) (Wi C : Subgroup _),
      B56Piece Gi Wi C → commV Gi ≤ Wi := by
    intro Gi Wi C h
    rcases h with ⟨hWi, -⟩ | ⟨hWi, -⟩ | ⟨-, hle, -⟩
    · rw [hWi]; exact le_sup_left
    · rw [hWi]; exact le_sup_left
    · exact hle
  have hfix : ∀ (Gi Gj : Subgroup (MulAut (IntMod (UX615 T L H) hU))) (Wi Wj : Subgroup _),
      Gi ≤ G₁ ⊔ G₂ → Gj ≠ ⊥ → (∀ a ∈ Gi, ∀ b ∈ Gj, a * b = b * a) →
      commV Gi ≤ Wi → commV Gj ≤ Wj → Wi ⊓ Wj = fixV (G₁ ⊔ G₂) → fixV Gi ≠ ⊥ := by
    intro Gi Gj Wi Wj hGi hGj hcij hWi hWj hWij hb
    by_cases h0 : fixV (G₁ ⊔ G₂) = ⊥
    · apply commV_ne_bot_ch615 hGj
      rw [eq_bot_iff, ← hb]
      intro w hw g hg
      have h1 : g w * w⁻¹ ∈ commV Gi := Subgroup.subset_closure ⟨g, hg, w, rfl⟩
      have h2 : g w * w⁻¹ ∈ commV Gj :=
        (commV Gj).mul_mem (mem_commV_of_conj_ch615 (fun x hx => by
          rw [hcij g hg x hx, mul_inv_cancel_right]; exact hx) hw) ((commV Gj).inv_mem hw)
      have h3 : g w * w⁻¹ ∈ Wi ⊓ Wj := ⟨hWi h1, hWj h2⟩
      rw [hWij, h0, Subgroup.mem_bot, mul_inv_eq_one] at h3
      exact h3
    · apply h0
      rw [eq_bot_iff, ← hb]
      exact fun v hv x hx => hv x (hGi hx)
  rw [← hsup] at hW
  have hfix₁ := hfix G₁ G₂ W₁ W₂ le_sup_left hf₂.ne_bot hcomm (hcW _ _ _ hp₁) (hcW _ _ _ hp₂)
    (hsup ▸ hW)
  have hfix₂ := hfix G₂ G₁ W₂ W₁ le_sup_right hf₁.ne_bot hc' (hcW _ _ _ hp₂) (hcW _ _ _ hp₁)
    (by rw [inf_comm]; exact hsup ▸ hW)
  have hperm := fun x (hx : x ∈ autI hU (borelL T L ⊔ H)) => map_conj_eq_or_swap_ch615 hcomm hinf
    hf₁.center hf₂.center hf₁.indec hf₂.indec hf₁.ne_bot hf₂.ne_bot (hnorm x hx)
  have hodd : ∀ x ∈ autI hU (borelL T L ⊔ H), Odd (orderOf x) →
      x ∈ Subgroup.normalizer (G₁ : Set (MulAut _)) ∧
        x ∈ Subgroup.normalizer (G₂ : Set (MulAut _)) := by
    intro x hx hxo
    rcases hperm x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨mem_normalizer_of_map_eq_ch615 h1, mem_normalizer_of_map_eq_ch615 h2⟩
    · have hx2 : ∀ (Gi Gj : Subgroup (MulAut (IntMod (UX615 T L H) hU))),
          Gi.map (MulAut.conj x).toMonoidHom = Gj → Gj.map (MulAut.conj x).toMonoidHom = Gi →
          x ^ 2 ∈ Subgroup.normalizer (Gi : Set (MulAut _)) := by
        intro Gi Gj hij hji
        refine mem_normalizer_of_conj_mem_l32_ch615 fun g hg => ?_
        have h1' : x * g * x⁻¹ ∈ Gj := by rw [← hij]; exact ⟨g, hg, rfl⟩
        have h2' : x * (x * g * x⁻¹) * x⁻¹ ∈ Gi := by rw [← hji]; exact ⟨_, h1', rfl⟩
        have e2 : x ^ 2 * g * (x ^ 2)⁻¹ = x * (x * g * x⁻¹) * x⁻¹ := by
          rw [pow_two, mul_inv_rev]
          group
        rw [e2]
        exact h2'
      obtain ⟨k, hk⟩ := hxo
      have ex : x = (x ^ 2) ^ (k + 1) := by
        rw [← pow_mul]
        calc x = x ^ orderOf x * x := by rw [pow_orderOf_eq_one, one_mul]
          _ = x ^ (2 * (k + 1)) := by rw [← pow_succ, hk]; ring_nf
      rw [ex]
      exact ⟨Subgroup.pow_mem _ (hx2 G₁ G₂ h1 h2) _, Subgroup.pow_mem _ (hx2 G₂ G₁ h2 h1) _⟩
  have hDs₁ : autI hU D ≤ Subgroup.normalizer (G₁ : Set (MulAut _)) := fun d hd =>
    (hodd d (hYsX (hDsY hd)) (hDsodd d hd)).1
  have hDs₂ : autI hU D ≤ Subgroup.normalizer (G₂ : Set (MulAut _)) := fun d hd =>
    (hodd d (hYsX (hDsY hd)) (hDsodd d hd)).2
  by_cases hsw : ∀ t ∈ autI hU T, G₁.map (MulAut.conj t).toMonoidHom = G₁
  ·
    have hTs₁ : autI hU T ≤ Subgroup.normalizer (G₁ : Set (MulAut _)) := fun t ht =>
      mem_normalizer_of_map_eq_ch615 (hsw t ht)
    have hTs₂ : autI hU T ≤ Subgroup.normalizer (G₂ : Set (MulAut _)) := fun t ht =>
      mem_normalizer_right_ch615 hcomm hf₁.center (hnorm t (hTsX ht)) (hTs₁ ht)
    have hor := c.le_or_le_ch615 h331 hU (A := autI hU (oTwoUpper H) ⊓ G₁)
      (B := autI hU (oTwoUpper H) ⊓ G₂) inf_le_left inf_le_left
      (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨hTK ht, hTs₁ ht⟩)
      (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨hTK ht, hTs₂ ht⟩)
      (fun k hk => (mem_sup_iff_of_commute_ch615 (fun a ha b hb =>
        hcomm a (Subgroup.mem_inf.mp ha).2 b (Subgroup.mem_inf.mp hb).2)).mp (hsplit hk))
    have hKJ : ∀ (Gi Gj : Subgroup (MulAut (IntMod (UX615 T L H) hU))),
        (∀ a ∈ Gi, ∀ b ∈ Gj, a * b = b * a) →
        autI hU (thompsonJ T) ≤ (autI hU T ⊓ Gi) ⊔ (autI hU T ⊓ Gj) →
        autI hU (oTwoUpper H) ≤ Gi →
        autI hU (oTwoUpper H) ≤ ⁅autI hU (oTwoUpper H), autI hU T ⊓ Gi⁆ := by
      intro Gi Gj hcij hJij hKi
      refine (c.le_commutator_ch615 hU).trans (Subgroup.commutator_le.mpr fun k hk j hj => ?_)
      obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := (mem_sup_iff_of_commute_ch615 (fun a ha b hb =>
        hcij a (Subgroup.mem_inf.mp ha).2 b (Subgroup.mem_inf.mp hb).2)).mp (hJij hj)
      have hks : ⁅k, s₂⁆ = 1 := by
        rw [commutatorElement_def, hcij k (hKi hk) s₂ (Subgroup.mem_inf.mp hs₂).2]
        group
      have e : ⁅k, s₁ * s₂⁆ = ⁅k, s₁⁆ * (s₁ * ⁅k, s₂⁆ * s₁⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e, hks, mul_one, mul_inv_cancel, mul_one]
      exact Subgroup.commutator_mem_commutator hk hs₁
    rcases hor with h | h
    · have hK₁ : autI hU (oTwoUpper H) ≤ G₁ := h.trans inf_le_right
      exact c.false_of_le_factor_ch615 h432 hU hN hD hf₁ hTs₁ hDs₁ hK₁ hS₁
        (hKJ G₁ G₂ hcomm hJsplit hK₁) hfix₁
    · have hK₂ : autI hU (oTwoUpper H) ≤ G₂ := h.trans inf_le_right
      exact c.false_of_le_factor_ch615 h432 hU hN hD hf₂ hTs₂ hDs₂ hK₂ hS₂
        (hKJ G₂ G₁ hc' (by rw [sup_comm]; exact hJsplit) hK₂) hfix₂
  ·
    push Not at hsw
    obtain ⟨t, htT, htn⟩ := hsw
    rcases hperm t (hTsX htT) with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact htn h1
    · exact c.false_of_swap_ch615 hU hN hD hcomm hinf hf₁ htT h1 h2 hDs₁ hDs₂ hKG hsplit hS₁
        hJsplit

end Cx615C

end CFSG.Quasithin.H13
