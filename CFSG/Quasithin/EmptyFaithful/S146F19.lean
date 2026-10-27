module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.EmptyFaithful.S146F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Counting

variable {G : Type} [Group G] [Finite G]

theorem twoPart_eq_of_card_eq_odd_mul {X Q : Subgroup G} (hQ : IsPGroup 2 Q) {a m : ℕ}
    (hm : ¬ 2 ∣ m) (hX : Nat.card X = m * 2 ^ a * Nat.card Q) :
    twoPart X = 2 ^ a * Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero 2)
  have h6 : Nat.card X = m * 2 ^ (a + k) := by rw [hX, hk]; ring
  unfold twoPart
  rw [h6, Nat.factorization_mul hm0 (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, hk]
  ring

theorem isPGroup_two_sup_of_le_normalizer {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) (hpA : IsPGroup 2 A) (hpB : IsPGroup 2 B) :
    IsPGroup 2 ↥(A ⊔ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.1 hpA
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hpB
  have h := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hA
  have hdvd : Nat.card (A ⊔ B : Subgroup G) ∣ 2 ^ (i + j) := by
    refine ⟨Nat.card (A ⊓ B : Subgroup G), ?_⟩
    rw [pow_add, ← hi, ← hj]
    exact h.symm
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact IsPGroup.iff_card.2 ⟨m, hm⟩

end Counting

section Sylow

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem IsDec12.card_H₁ (hp : p = 3) (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    Nat.card H₁ = 6 * Nat.card (pCoreOf 2 H) := by
  subst hp
  obtain ⟨hQn, ⟨e⟩⟩ := h.dihedral₁
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((pCoreOf 2 H).subgroupOf H₁)
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Q₁).toEquiv] at h1
  have h6 : Nat.card (DihedralGroup 3) = 6 := by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
  rw [h1, h6]

omit [Finite G] in
theorem IsDec12.card_H₂ (hp : p = 3) (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    Nat.card H₂ = 6 * Nat.card (pCoreOf 2 H) :=
  h.swap.card_H₁ hp

omit [Finite G] in
theorem IsDec12.le_normalizer_H₂ (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    H₁ ≤ Subgroup.normalizer (H₂ : Set G) := by
  refine S146A.le_normalizer_of_commutator_le h.Q₂ ?_
  rw [Subgroup.commutator_comm]
  exact h.comm

theorem IsDec12.isSylowTwoOf_sup (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hp : p = 3) (h : IsDec12 T M H p H₀ H₁ H₂ t)
    {V' : Subgroup G} (hV' : IsElemAbelian 2 V') (hV'H : V' ≤ H₁) (hV'Q : ¬ V' ≤ pCoreOf 2 H) :
    IsSylowTwoOf ((V' ⊔ pCoreOf 2 H) ⊔ ((T ⊓ H₀) ⊓ H₂)) H₀ := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hT₀ : IsSylowTwoOf (T ⊓ H₀) H₀ := B6.isSylowTwoOf_inf_normal hTsyl h.le h.le_normalizer_H₀
  set Q := pCoreOf 2 H with hQdef
  have hQT : Q ≤ T := S.pCoreOf_le_T hH
  have hQ2 : IsPGroup 2 Q := hTsyl.isPGroup.to_le hQT
  have hQ₀ : Q ≤ T ⊓ H₀ := le_inf hQT (h.Q₁.trans h.le₁)
  have hN₂ : H₁ ≤ Subgroup.normalizer (H₂ : Set G) := h.le_normalizer_H₂
  have hH₀N₂ : H₀ ≤ Subgroup.normalizer (H₂ : Set G) := by
    rw [h.sup]
    exact sup_le hN₂ Subgroup.le_normalizer
  have hT₂ : IsSylowTwoOf ((T ⊓ H₀) ⊓ H₂) H₂ := B6.isSylowTwoOf_inf_normal hT₀ h.le₂ hH₀N₂
  have h1 := h.card_H₁ hp
  have h2 := h.card_H₂ hp
  have htw₁ : twoPart H₁ = 2 ^ 1 * Nat.card Q :=
    twoPart_eq_of_card_eq_odd_mul hQ2 (by norm_num : ¬ 2 ∣ 3) (by rw [h1]; ring)
  have htw₂ : twoPart H₂ = 2 ^ 1 * Nat.card Q :=
    twoPart_eq_of_card_eq_odd_mul hQ2 (by norm_num : ¬ 2 ∣ 3) (by rw [h2]; ring)
  have hcT₂ : Nat.card ↥((T ⊓ H₀) ⊓ H₂) = 2 * Nat.card Q := by
    rw [hT₂.card_eq, htw₂]
    ring
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hV'2 : IsPGroup 2 V' := fun x => ⟨1, Subtype.ext (by simpa using hV'.2 x x.2)⟩
  have hV'N : V' ≤ Subgroup.normalizer (Q : Set G) :=
    (hV'H.trans (h.le₁.trans h.le)).trans (le_normalizer_pCoreOf 2 H)
  have hR2 : IsPGroup 2 ↥(V' ⊔ Q) := isPGroup_two_sup_of_le_normalizer hV'N hV'2 hQ2
  have hRH₁ : V' ⊔ Q ≤ H₁ := sup_le hV'H h.Q₁
  have hRle : Nat.card ↥(V' ⊔ Q) ≤ 2 * Nat.card Q := by
    have := card_le_twoPart hRH₁ hR2
    rw [htw₁] at this
    simpa using this
  have hQR : Nat.card Q ∣ Nat.card ↥(V' ⊔ Q) := Subgroup.card_dvd_of_le le_sup_right
  have hRne : Nat.card ↥(V' ⊔ Q) ≠ Nat.card Q := by
    intro hc
    apply hV'Q
    have hEq : Q = V' ⊔ Q := Subgroup.eq_of_le_of_card_ge le_sup_right hc.le
    exact le_sup_left.trans hEq.ge
  have hcardR : Nat.card ↥(V' ⊔ Q) = 2 * Nat.card Q := by
    obtain ⟨m, hm⟩ := hQR
    have hm2 : m ≤ 2 := by
      by_contra hc
      have hc3 : 3 ≤ m := by omega
      have : Nat.card Q * 3 ≤ Nat.card Q * m := Nat.mul_le_mul_left _ hc3
      omega
    have hm0 : m ≠ 0 := by
      rintro rfl
      have : 0 < Nat.card ↥(V' ⊔ Q) := Nat.card_pos
      omega
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hRne (by omega)
    have hm2' : m = 2 := by omega
    rw [hm, hm2']
    ring
  have hRT₂N : (V' ⊔ Q) ≤ Subgroup.normalizer (((T ⊓ H₀) ⊓ H₂ : Subgroup G) : Set G) := by
    refine S146A.le_normalizer_of_commutator_le (A := (T ⊓ H₀) ⊓ H₂) (B := V' ⊔ Q) (Q := Q)
      (le_inf hQ₀ h.Q₂) ?_
    calc ⁅(T ⊓ H₀) ⊓ H₂, V' ⊔ Q⁆ ≤ ⁅H₂, H₁⁆ := Subgroup.commutator_mono inf_le_right hRH₁
      _ = ⁅H₁, H₂⁆ := Subgroup.commutator_comm _ _
      _ ≤ Q := h.comm
  have hinf : (V' ⊔ Q) ⊓ ((T ⊓ H₀) ⊓ H₂) = Q := by
    apply le_antisymm
    · calc (V' ⊔ Q) ⊓ ((T ⊓ H₀) ⊓ H₂) ≤ H₁ ⊓ H₂ := inf_le_inf hRH₁ inf_le_right
        _ = Q := h.inf
    · exact le_inf le_sup_right (le_inf hQ₀ h.Q₂)
  have hcsup := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hRT₂N
  rw [hinf, hcardR, hcT₂] at hcsup
  have hcardS : Nat.card ↥((V' ⊔ Q) ⊔ ((T ⊓ H₀) ⊓ H₂)) = 4 * Nat.card Q := by
    have : Nat.card ↥((V' ⊔ Q) ⊔ ((T ⊓ H₀) ⊓ H₂)) * Nat.card Q = (4 * Nat.card Q) * Nat.card Q := by
      rw [hcsup]
      ring
    exact Nat.eq_of_mul_eq_mul_right hQpos this
  have hH₀card := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hN₂
  rw [h.inf, ← h.sup, h1, h2] at hH₀card
  have hH₀ : Nat.card H₀ = 36 * Nat.card Q :=
    Nat.eq_of_mul_eq_mul_right hQpos (by rw [hH₀card]; ring)
  have htw₀ : twoPart H₀ = 2 ^ 2 * Nat.card Q :=
    twoPart_eq_of_card_eq_odd_mul hQ2 (by norm_num : ¬ 2 ∣ 9) (by rw [hH₀]; ring)
  refine isSylowTwoOf_of_card_eq (sup_le (hRH₁.trans h.le₁) (inf_le_right.trans h.le₂))
    (isPGroup_two_sup_of_le_normalizer hRT₂N hR2 hT₂.isPGroup) ?_
  rw [hcardS, htw₀]
  ring

end Sylow

theorem input14617Gamma_proved : Input14617Gamma := by
  intro G _ _ T M S H PQ p hred hp H₀ H₁ H₂ t h V' hV' hV'H hV'Q w hwV' hwU
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hT₀ : IsSylowTwoOf (T ⊓ H₀) H₀ := B6.isSylowTwoOf_inf_normal hTsyl h.le h.le_normalizer_H₀
  have hS := h.isSylowTwoOf_sup S hred hp hV' hV'H hV'Q
  obtain ⟨g, hg, hgeq⟩ := hT₀.exists_conj hS
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hH₂H : H₂ ≤ H := h.le₂.trans h.le
  have hwU' : w ∈ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H hwU
  have hSA : (V' ⊔ pCoreOf 2 H) ⊔ ((T ⊓ H₀) ⊓ H₂) ≤
      centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers w) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      have hxH : x ∈ H := hH₁H (hV'H hx)
      refine mem_centralizerMod.mpr ⟨hxH, S.normalizer_Z.ge (hHG hxH), fun v hv => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have hc : Commute w x := isElemAbelian_comm hV' hwV' hx
      have hc' : Commute (w ^ k) x := hc.zpow_left k
      have : x * w ^ k * x⁻¹ * (w ^ k)⁻¹ = 1 := by
        rw [← hc'.eq]
        group
      rw [this]
      exact Subgroup.one_mem _
    · intro x hx
      refine mem_centralizerMod.mpr ⟨pCoreOf_le 2 H hx, S.normalizer_Z.ge (hHG (pCoreOf_le 2 H hx)),
        fun v hv => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact S.comm_mem_Z hH ((conjClosure (VZ T M) H).zpow_mem hwU' k) hx
    · intro x hx
      have hxH : x ∈ H := hTH hx.1.1
      refine mem_centralizerMod.mpr ⟨hxH, S.normalizer_Z.ge (hHG hxH), fun v hv => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have h1 := (quasithinOmegaOneCenter T).inv_mem
        (h.cent₁ (Subgroup.commutator_mem_commutator ((uHi T M H H₁).zpow_mem hwU k) hx.2))
      rw [commutatorElement_inv] at h1
      simpa [commutatorElement_def, mul_assoc] using h1
  refine ⟨g⁻¹, H₀.inv_mem hg, ?_⟩
  rw [h.inf_normalizer_eq hTH]
  intro x hx
  have hxT : x ∈ T := hx.1
  have hxH : x ∈ H := hTH hxT
  have hmem : g * x * g⁻¹ ∈ (V' ⊔ pCoreOf 2 H) ⊔ ((T ⊓ H₀) ⊓ H₂) := by
    rw [hgeq]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hA := (mem_centralizerMod.mp (hSA hmem)).2.2
  refine mem_centralizerMod.mpr ⟨hxT, S.normalizer_Z.ge (hHG hxH), fun v hv => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hc : (g * x * g⁻¹) * w ^ k * (g * x * g⁻¹)⁻¹ * (w ^ k)⁻¹ ∈ quasithinOmegaOneCenter T :=
    hA (w ^ k) (Subgroup.zpow_mem_zpowers w k)
  have hgG : g ∈ mcOf T := hHG (h.le hg)
  have hcomm : g⁻¹ * ((g * x * g⁻¹) * w ^ k * (g * x * g⁻¹)⁻¹ * (w ^ k)⁻¹) =
      ((g * x * g⁻¹) * w ^ k * (g * x * g⁻¹)⁻¹ * (w ^ k)⁻¹) * g⁻¹ :=
    S146T.comm_Z (Subgroup.inv_mem _ hgG) hc
  have hconj : (g⁻¹ * w * g⁻¹⁻¹) ^ k = g⁻¹ * w ^ k * g⁻¹⁻¹ := conj_zpow
  rw [hconj]
  have e : x * (g⁻¹ * w ^ k * g⁻¹⁻¹) * x⁻¹ * (g⁻¹ * w ^ k * g⁻¹⁻¹)⁻¹ =
      g⁻¹ * ((g * x * g⁻¹) * w ^ k * (g * x * g⁻¹)⁻¹ * (w ^ k)⁻¹) * g⁻¹⁻¹ := by
    generalize w ^ k = u
    group
  rw [e, hcomm]
  simpa [mul_assoc] using hc

end CFSG.Quasithin
