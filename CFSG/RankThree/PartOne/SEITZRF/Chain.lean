module

public import CFSG.RankThree.PartOne.SEITZRF.Defs
public import CFSG.RankThree.PartOne.SEITZQ1.Endgame
public import CFSG.RankThree.PartOne.SEITZ9.SzField

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom pairedTorusHom_apply f4i torusPair torusWeight
  torusWeight_apply torusExp1 torusPair_conj_pinnedX)

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

variable (K a) in
@[expose] def R1Dich (β : K ≃+* K) : Prop :=
  ∀ Y : Subgroup (ModGL F4.tag K), Y ≤ rankOneGroupOne K a → rankOneGroupOne K a ⊓ Rf K a β ≤ Y →
    ¬ Y ≤ Rf K a β → Y = rankOneGroupOne K a

variable (K a) in
@[expose] def R2Dich (β : K ≃+* K) : Prop :=
  ∀ Y : Subgroup (ModGL F4.tag K), Y ≤ rankOneGroupTwo K a → rankOneGroupTwo K a ⊓ Rf K a β ≤ Y →
    ¬ Y ≤ Rf K a β → Y = rankOneGroupTwo K a

variable (K a) in
@[expose] def R1Dich2 (β : K ≃+* K) : Prop :=
  ∀ Y : Subgroup (ModGL F4.tag K), Y ≤ rankOneGroupOne K a → rankOneGroupOne K a ⊓ Rf K a β ≤ Y →
    ∀ s : K, β s ≠ s → sylowA a K s ∈ Y → Y = rankOneGroupOne K a

variable (K a) in
@[expose] def R2Dich2 (β : K ≃+* K) : Prop :=
  ∀ Y : Subgroup (ModGL F4.tag K), Y ≤ rankOneGroupTwo K a → rankOneGroupTwo K a ⊓ Rf K a β ≤ Y →
    ∀ b c : K, ¬ (β b = b ∧ β c = c) → sylowB a K b c ∈ Y → Y = rankOneGroupTwo K a

theorem sylowA_mem_rankOneGroupOne' (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    sylowA a K c ∈ rankOneGroupOne K a :=
  Subgroup.subset_closure (Or.inl (Or.inl (sylowA_mem_U1 hK c)))

theorem torusOne_mem_rankOneGroupOne' (u : Kˣ) :
    pairedTorusHom a (f4i 0) (f4i 3) u ∈ rankOneGroupOne K a :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨u, rfl⟩))

theorem sylowB_mem_rankOneGroupTwo' (hK : Nat.card K = 2 ^ (2 * a + 1)) (b c : K) :
    sylowB a K b c ∈ rankOneGroupTwo K a :=
  Subgroup.subset_closure (Or.inl (Or.inl (sylowB_mem_U2 hK b c)))

theorem torusTwo_mem_rankOneGroupTwo' (u : Kˣ) :
    pairedTorusHom a (f4i 1) (f4i 2) u ∈ rankOneGroupTwo K a :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨u, rfl⟩))

omit [Finite K] [CharP K F4.prime] in
theorem pairedTorusHom_mem_fixGL (β : K ≃+* K) {u : Kˣ} (hu : β u = u) (j l : Fin F4.tag.rank) :
    pairedTorusHom a j l u ∈ fixGL K β := by
  rw [mem_fixGL, pairedTorusHom_apply, map_mul, entrywise_torusElt, entrywise_torusElt]
  have h1 : Units.map β.toRingHom.toMonoidHom u = u := Units.ext hu
  have h2 : Units.map β.toRingHom.toMonoidHom (u ^ 2 ^ a) = u ^ 2 ^ a := by rw [map_pow, h1]
  rw [h1, h2]

theorem torusOne_mem_Rf (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) {u : Kˣ}
    (hu : β u = u) : pairedTorusHom a (f4i 0) (f4i 3) u ∈ Rf K a β :=
  ⟨reeFixedTorus_le_reeGamma' (rankOneTorusOne_le hK ⟨u, rfl⟩), pairedTorusHom_mem_fixGL β hu _ _⟩

theorem sylowA_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (c : K) :
    sylowA a K c ∈ Rf K a β ↔ β c = c := by
  have e : sylowA a K c = sylowVec a K ![c, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    rw [← sylowV_eq_sylowA]
    rfl
  rw [e, sylowVec_mem_Rf_iff hK]
  constructor
  · intro h
    simpa using h 0
  · intro h i
    fin_cases i <;> simp [h]

theorem sylowB_one_zero_mem_Rf (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) :
    sylowB a K 1 0 ∈ Rf K a β := by
  have e : sylowB a K 1 0 = sylowVec a K ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    simp [sylowVec, sylowV, sylowA_zero, sylowD_zero_zero, sylowF_zero_zero, sylowJ_zero,
      sylowK_zero, sylowH, sylowL, sylowX, largeReeSigma_zero, pinnedX_zero]
  rw [e, sylowVec_mem_Rf_iff hK]
  intro i
  fin_cases i <;> simp

theorem centralZ_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (c : K) :
    centralZ K a c ∈ Rf K a β ↔ β c = c := by
  have e : centralZ K a c = sylowVec a K ![0, 0, 0, 0, 0, 0, 0, 0, c, 0, 0, 0] := by
    rw [← sylowH_zero_eq_centralZ, (blocks_eq_sylowV 0 0 0 c 0 0 0).2.2.2.1]
    rfl
  rw [e, sylowVec_mem_Rf_iff hK]
  constructor
  · intro h
    simpa using h 8
  · intro h i
    fin_cases i <;> simp [h]

omit [CharP K F4.prime] in
theorem torusTwo_conj_sylowA (hK : Nat.card K = 2 ^ (2 * a + 1))
    (u : Kˣ) (c : K) :
    pairedTorusHom a (f4i 1) (f4i 2) u * sylowA a K c * (pairedTorusHom a (f4i 1) (f4i 2) u)⁻¹ =
      sylowA a K (((u⁻¹ : Kˣ) : K) ^ 2 ^ a * c) := by
  obtain ⟨⟨-, h1, h2, -⟩, ⟨-, h1', h2', -⟩, -⟩ := cartanPair_A_B
  have w24 : ((torusWeight a (RootOps.orbitCertRoot F4.tag 24) (1, u) : Kˣ) : K) =
      ((u⁻¹ : Kˣ) : K) ^ 2 ^ a := by
    rw [torusWeight_apply, one_zpow, one_mul, ← Units.val_pow_eq_pow_val, inv_pow,
      ← zpow_natCast, ← zpow_neg]
    simp only [torusExp1]
    rw [h1, h2]
    push_cast
    ring_nf
  have w33 : ((torusWeight a (RootOps.orbitCertRoot F4.tag 33) (1, u) : Kˣ) : K) =
      largeReeSigma a (((u⁻¹ : Kˣ) : K) ^ 2 ^ a) := by
    rw [torusWeight_apply, one_zpow, one_mul, largeReeSigma, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, ← pow_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    simp only [torusExp1]
    rw [h1', h2']
    congr 1
    refine units_zpow_congr hK u 1 ?_
    push_cast
    rw [show ((2 : ℤ) ^ (2 * a + 1)) = 2 * (2 ^ a) ^ 2 by ring]
    ring
  rw [← rankOneTorusPair_right, sylowA, sylowA, sylowX, sylowX, sylowX, sylowX, weyl_conj_mul,
    torusPair_conj_pinnedX a (1, u) (sylowRoot_pos (r := 24) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX a (1, u) (sylowRoot_pos (r := 33) (by norm_num) (by norm_num)).1,
    w24, w33, largeReeSigma_mul]

omit [Finite K] in
theorem eq_of_map_pow_two_pow_eq (β : K ≃+* K) (n : ℕ) {x : K} (h : β (x ^ 2 ^ n) = x ^ 2 ^ n) :
    β x = x := by
  rw [map_pow] at h
  have hinj : Function.Injective (fun y : K => y ^ 2 ^ n) := by
    have : CharP K 2 := ‹CharP K F4.prime›
    intro y z hyz
    have h' : (y - z) ^ 2 ^ n = 0 := by
      rw [sub_pow_char_pow, sub_eq_zero]
      exact hyz
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero n two_ne_zero) |>.1 h')
  exact hinj h

theorem exists_pow_two_pow_eq_of_mem (k : Subfield K) (n : ℕ) {c : K} (hc : c ∈ k) :
    ∃ κ ∈ k, κ ^ 2 ^ n = c := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have : Finite k := Subtype.finite
  have hinj : Function.Injective (fun y : k => y ^ 2 ^ n) := by
    intro y z hyz
    apply Subtype.ext
    have h' : ((y : K) - z) ^ 2 ^ n = 0 := by
      rw [sub_pow_char_pow, sub_eq_zero]
      exact congrArg Subtype.val hyz
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero n two_ne_zero) |>.1 h')
  obtain ⟨κ, hκ⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨c, hc⟩
  exact ⟨κ, κ.2, congrArg Subtype.val hκ⟩

theorem reeGamma_le_of_rankOneGroupOne_le
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) {H : Subgroup (ModGL F4.tag K)}
    (hRH : Rf K a β ≤ H) (hR1 : rankOneGroupOne K a ≤ H) : F4.reeGamma K a ≤ H := by
  refine SEITZQ1.reeGamma_le_of_localBlock_zero hK H ?_ (hRH (sylowB_one_zero_mem_Rf hK β))
    (hRH (weylTwo_mem_Rf β))
  intro x hx
  apply hR1
  rw [rankOneGroupOne_eq_range hK, largeReeA1Hom_range hK]
  exact hx

theorem reeGamma_le_of_rankOneGroupTwo_le
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (hd1 : R1Dich2 K a β)
    {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H) (hR2 : rankOneGroupTwo K a ≤ H)
    {l : Kˣ} (hl : β (l : K) ≠ l) : F4.reeGamma K a ≤ H := by
  refine reeGamma_le_of_rankOneGroupOne_le hK β hRH ?_
  have hT : pairedTorusHom a (f4i 1) (f4i 2) l ∈ H := hR2 (torusTwo_mem_rankOneGroupTwo' l)
  set c : K := ((l⁻¹ : Kˣ) : K) ^ 2 ^ a * 1 with hc
  have hA : sylowA a K c ∈ H := by
    have h1 := H.mul_mem (H.mul_mem hT (hRH ((sylowA_mem_Rf_iff hK β 1).2 (map_one β))))
      (H.inv_mem hT)
    rwa [torusTwo_conj_sylowA hK] at h1
  have hck : β c ≠ c := by
    intro h
    rw [hc, mul_one] at h
    have h' := eq_of_map_pow_two_pow_eq β a h
    apply hl
    have : ((l⁻¹ : Kˣ) : K) = (l : K)⁻¹ := Units.val_inv_eq_inv_val l
    rw [this, map_inv₀] at h'
    exact inv_injective h'
  have hY := hd1 (rankOneGroupOne K a ⊓ H) inf_le_left
    (le_inf inf_le_left fun x hx => hRH hx.2) c hck ⟨sylowA_mem_rankOneGroupOne' hK c, hA⟩
  rw [← hY]
  exact inf_le_right

theorem reeGamma_le_of_centralZ
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (hd1 : R1Dich2 K a β)
    (hd2 : R2Dich2 K a β) {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H)
    (hz : ∀ c : K, centralZ K a c ∈ H)
    {l : Kˣ} (hl : β (l : K) ≠ l) : F4.reeGamma K a ≤ H := by
  refine reeGamma_le_of_rankOneGroupTwo_le hK β hd1 hRH ?_ hl
  have hn : weylOne K * weylTwo K * weylOne K ∈ H :=
    H.mul_mem (H.mul_mem (hRH (weylOne_mem_Rf β)) (hRH (weylTwo_mem_Rf β)))
      (hRH (weylOne_mem_Rf β))
  have hB : ∀ c : K, sylowB a K 0 c ∈ H := fun c => by
    have h1 := H.mul_mem (H.mul_mem (H.inv_mem hn) (hz c)) hn
    rw [← sylowH_zero_eq_centralZ, ← weyl_conj_sylowB_zero c] at h1
    simpa [mul_assoc] using h1
  have hY := hd2 (rankOneGroupTwo K a ⊓ H) inf_le_left
    (le_inf inf_le_left fun x hx => hRH hx.2) 0 l (fun h => hl h.2)
      ⟨sylowB_mem_rankOneGroupTwo' hK 0 l, hB l⟩
  rw [← hY]
  exact inf_le_right

theorem reeGamma_le_of_le_Y1 (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (hd1 : R1Dich2 K a β)
    (hd2 : R2Dich2 K a β) {p : ℕ} (hp : p.Prime)
    (hKk : Nat.card K = Nat.card (CFSG.LieType.Chevalley.fixSubfield β) ^ p)
    {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H) (hY : rankOneGroupOne K a ≤ Y1 K a hK H)
    {μ : Kˣ} (hμ : β (μ : K) ≠ μ) : F4.reeGamma K a ≤ H := by
  obtain ⟨-, v, hv, hvT⟩ := hY (torusOne_mem_rankOneGroupOne' μ)
  have hvU : v ∈ F4.reeFixedPosUnipotent K a := reeFixedOrbitComplementUnipotent_le _ hv
  set M : Set K := {c | centralZ K a c ∈ H} with hMdef
  have hzR : ∀ c : K, β c = c → centralZ K a c ∈ H := fun c hc =>
    hRH ((centralZ_mem_Rf_iff hK β c).2 hc)
  have h1 : (1 : K) ∈ M := hzR 1 (map_one β)
  have hadd : ∀ x ∈ M, ∀ y ∈ M, x + y ∈ M := fun x hx y hy => by
    show centralZ K a (x + y) ∈ H
    rw [← sylowH_zero_eq_centralZ, ← sylowH_mul hK, sylowH_zero_eq_centralZ,
      sylowH_zero_eq_centralZ]
    exact H.mul_mem hx hy
  have hconj : ∀ (t : Kˣ), pairedTorusHom a (f4i 0) (f4i 3) t ∈ H → ∀ x ∈ M,
      (t : K) ^ 2 ^ a * x ∈ M := fun t ht x hx => by
    show centralZ K a ((t : K) ^ 2 ^ a * x) ∈ H
    rw [← torusPair_conj_centralZ hK t 1 x, rankOneTorusPair_left]
    exact H.mul_mem (H.mul_mem ht hx) (H.inv_mem ht)
  have hk : ∀ c ∈ CFSG.LieType.Chevalley.fixSubfield β, ∀ x ∈ M, c * x ∈ M := by
    intro c hc x hx
    by_cases hc0 : c = 0
    · rw [hc0, zero_mul]
      show centralZ K a 0 ∈ H
      rw [centralZ_zero]
      exact H.one_mem
    · obtain ⟨κ, hκ, hκc⟩ := exists_pow_two_pow_eq_of_mem _ a hc
      have hκ0 : κ ≠ 0 := by
        rintro rfl
        rw [zero_pow (pow_ne_zero a two_ne_zero)] at hκc
        exact hc0 hκc.symm
      have hT := hRH (torusOne_mem_Rf hK β (u := Units.mk0 κ hκ0) hκ)
      have := hconj _ hT x hx
      rwa [Units.val_mk0, hκc] at this
  have hμM : ∀ x ∈ M, (μ : K) ^ 2 ^ a * x ∈ M := by
    intro x hx
    show centralZ K a ((μ : K) ^ 2 ^ a * x) ∈ H
    have e : (v * pairedTorusHom a (f4i 0) (f4i 3) μ) * centralZ K a x *
        (v * pairedTorusHom a (f4i 0) (f4i 3) μ)⁻¹ = centralZ K a ((μ : K) ^ 2 ^ a * x) := by
      rw [← rankOneTorusPair_left]
      calc v * torusPair a (μ, 1) * centralZ K a x * (v * torusPair a (μ, 1))⁻¹ =
          v * (torusPair a (μ, 1) * centralZ K a x * (torusPair a (μ, 1))⁻¹) * v⁻¹ := by group
        _ = v * centralZ K a ((μ : K) ^ 2 ^ a * x) * v⁻¹ := by
          rw [torusPair_conj_centralZ hK]
        _ = centralZ K a ((μ : K) ^ 2 ^ a * x) := by
          rw [commute_centralZ ha hK hvU]
          group
    rw [← e]
    exact H.mul_mem (H.mul_mem hvT hx) (H.inv_mem hvT)
  have hμk : (μ : K) ^ 2 ^ a ∉ CFSG.LieType.Chevalley.fixSubfield β := fun h =>
    hμ (eq_of_map_pow_two_pow_eq β a h)
  have hM := SEITZ9.eq_univ_of_smul_closed hp hKk M h1 hadd hk hμM hμk
  refine reeGamma_le_of_centralZ hK β hd1 hd2 hRH (fun c => ?_) hμ
  have : c ∈ M := hM ▸ Set.mem_univ c
  exact this

end CFSG.RankThree.PartOne.SEITZRF
