module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Lift

variable {L L0 : Type} [Group L] [Group L0] {c : L →* L0}

private lemma qTwoLMDivCoordInner_lift_orderOf_two_pow (hc2 : IsPGroup 2 c.ker) {z : L}
    (hz : z ∈ c.ker) : ∃ k, orderOf z = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hc2.exists_orderOf_eq_pow ⟨z, hz⟩
  exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩

private lemma qTwoLMDivCoordInner_lift_eq_one_of_mem_ker_of_pow (hc2 : IsPGroup 2 c.ker) {z : L}
    (hz : z ∈ c.ker) (hz3 : z ^ 3 = 1) : z = 1 := by
  obtain ⟨k, hk⟩ := qTwoLMDivCoordInner_lift_orderOf_two_pow hc2 hz
  have hdvd : 2 ^ k ∣ 3 := by
    rw [← hk]
    exact orderOf_dvd_iff_pow_eq_one.mpr hz3
  have hk0 : 2 ^ k = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact h
    · exfalso
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, pow_zero] at h
        norm_num at h
      · have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hkpos)
        rw [h] at h2
        norm_num at h2
  have h1 : orderOf z = 1 := by rw [hk, hk0]
  exact orderOf_eq_one_iff.mp h1

private lemma qTwoLMDivCoordInner_lift_exists_lift_pow_eq_one (hcs : Function.Surjective c)
    (hck : c.ker ≤ Subgroup.center L) (hc2 : IsPGroup 2 c.ker)
    {g : L0} (hg : g ^ 3 = 1) : ∃ n : L, c n = g ∧ n ^ 3 = 1 := by
  obtain ⟨n₀, rfl⟩ := hcs g
  set z := n₀ ^ 3 with hz
  have hzk : z ∈ c.ker := by rw [MonoidHom.mem_ker, hz, map_pow, hg]
  have h3z : ¬ 3 ∣ orderOf z := by
    obtain ⟨k, hk⟩ := qTwoLMDivCoordInner_lift_orderOf_two_pow hc2 hzk
    rw [hk]
    intro hdvd
    have : 3 ∣ 2 := (by norm_num : Nat.Prime 3).dvd_of_dvd_pow hdvd
    norm_num at this
  have hcop : (3 : ℕ).Coprime (orderOf z) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr h3z
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime (x := z) hcop
  have hcomm : Commute n₀ (z ^ t)⁻¹ :=
    Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ (Subgroup.pow_mem _ (hck hzk) t)) n₀
  refine ⟨n₀ * (z ^ t)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, map_pow, MonoidHom.mem_ker.mp hzk, one_pow, inv_one, mul_one]
  · rw [hcomm.mul_pow, ← hz, inv_pow, ← pow_mul, mul_comm t 3, pow_mul, ht, mul_inv_cancel]

private lemma qTwoLMDivCoordInner_lift_eq_of_lift_pow_eq_one (hck : c.ker ≤ Subgroup.center L)
    (hc2 : IsPGroup 2 c.ker) {x y : L} (hxy : c x = c y) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    x = y := by
  set z := x⁻¹ * y with hz
  have hzk : z ∈ c.ker := by rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hxy, inv_mul_cancel]
  have hyz : y = x * z := by rw [hz, mul_inv_cancel_left]
  have hcomm : Commute x z := Subgroup.mem_center_iff.mp (hck hzk) x
  have hzp : z ^ 3 = 1 := by
    have h1 := hy
    rw [hyz, hcomm.mul_pow, hx, one_mul] at h1
    exact h1
  rw [hyz, qTwoLMDivCoordInner_lift_eq_one_of_mem_ker_of_pow hc2 hzk hzp, mul_one]

private lemma qTwoLMDivCoordInner_lift_commute_of_lift_pow_eq_one (hck : c.ker ≤ Subgroup.center L)
    (hc2 : IsPGroup 2 c.ker) {x y : L} (hxy : c x * c y = c y * c x) (hy : y ^ 3 = 1) :
    x * y = y * x := by
  have h1 : x * y * x⁻¹ = y := by
    refine qTwoLMDivCoordInner_lift_eq_of_lift_pow_eq_one hck hc2 ?_ ?_ hy
    · rw [map_mul, map_mul, map_inv, hxy, mul_inv_cancel_right]
    · rw [conj_pow, hy, mul_one, mul_inv_cancel]
  calc x * y = x * y * x⁻¹ * x := by group
    _ = y * x := by rw [h1]

end Lift

theorem qTwoLMDivCoordInner_section {L L0 : Type} [Group L] [Group L0] [Finite L] (c : L →* L0)
    (hcs : Function.Surjective c) (hck : c.ker ≤ Subgroup.center L) (hc2 : IsPGroup 2 c.ker)
    {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 3 = 1) (τ : V →* L0) :
    ∃ s : V →* L, c.comp s = τ ∧ ∀ v, s v ^ 3 = 1 := by
  choose s hs hsp using fun v => qTwoLMDivCoordInner_lift_exists_lift_pow_eq_one hcs hck hc2
    (g := τ v) (by rw [← map_pow, hV, map_one])
  have hmul : ∀ v w, s (v * w) = s v * s w := by
    intro v w
    have hc : s v * s w = s w * s v :=
      qTwoLMDivCoordInner_lift_commute_of_lift_pow_eq_one hck hc2
        (by rw [hs, hs, ← map_mul, ← map_mul, mul_comm]) (hsp w)
    refine qTwoLMDivCoordInner_lift_eq_of_lift_pow_eq_one hck hc2 ?_ (hsp _) ?_
    · rw [map_mul, hs, hs, hs, map_mul]
    · rw [(show Commute (s v) (s w) from hc).mul_pow, hsp, hsp, one_mul]
  exact ⟨MonoidHom.mk' s hmul, MonoidHom.ext fun v => hs v, hsp⟩

section KerPi

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}

private lemma qTwoLMDivCoordInner_lift_center_scalar_units (hF0 : Nat.card F0 = 4) (hm : 4 ≤ m)
    {ζ : Su F0 2 1 m} (hζ : ζ ∈ Subgroup.center (Su F0 2 1 m)) :
    ∃ c : F0ˣ, ((ζ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun _ => (c : F0)) := by
  classical
  obtain ⟨c, hc⟩ := qTwoLMDivCoordInner_center_scalar hF0 hm hζ
  have hdet : ((ζ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0).det = 1 :=
    (mem_SUid.mp ζ.2).1
  have hcm : c ^ m = 1 := by
    have h := congrArg Matrix.det hc
    rw [hdet, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega : m ≠ 0)] at hcm
    exact zero_ne_one hcm
  exact ⟨Units.mk0 c hc0, by simpa using hc⟩

private lemma qTwoLMDivCoordInner_lift_center_cube (hF0 : Nat.card F0 = 4) (hm : 4 ≤ m)
    {ζ : Su F0 2 1 m} (hζ : ζ ∈ Subgroup.center (Su F0 2 1 m)) : ζ ^ 3 = 1 := by
  classical
  obtain ⟨c, hc⟩ := qTwoLMDivCoordInner_lift_center_scalar_units hF0 hm hζ
  haveI : Fintype F0 := Fintype.ofFinite F0
  have hcard : Fintype.card F0ˣ = 3 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hF0]
  have hc3 : (c : F0) ^ 3 = 1 := by
    have h : c ^ 3 = 1 := by
      simpa only [hcard] using pow_card_eq_one (x := c) (G := F0ˣ)
    simpa using congrArg (fun u : F0ˣ => (u : F0)) h
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, Units.val_one, hc]
  rw [Matrix.diagonal_pow]
  rw [show (fun _ : Fin m => (c : F0)) ^ 3 = (fun _ : Fin m => (c : F0) ^ 3) by
    funext i; rw [Pi.pow_apply]]
  rw [hc3]
  exact Matrix.diagonal_one

private lemma qTwoLMDivCoordInner_lift_center_card_le (hF0 : Nat.card F0 = 4) (hm : 4 ≤ m) :
    Nat.card (Subgroup.center (Su F0 2 1 m)) ≤ 3 := by
  classical
  haveI : Fintype F0 := Fintype.ofFinite F0
  have hcard : Nat.card F0ˣ = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF0]
  let f : Subgroup.center (Su F0 2 1 m) → F0ˣ := fun ζ =>
    Classical.choose (qTwoLMDivCoordInner_lift_center_scalar_units hF0 hm ζ.2)
  have hf : Function.Injective f := by
    intro ζ η hζη
    have hζ := Classical.choose_spec (qTwoLMDivCoordInner_lift_center_scalar_units hF0 hm ζ.2)
    have hη := Classical.choose_spec (qTwoLMDivCoordInner_lift_center_scalar_units hF0 hm η.2)
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [hζ, hη]
    exact congrArg Matrix.diagonal
      (funext fun _ => congrArg (fun u : F0ˣ => (u : F0)) hζη)
  calc Nat.card (Subgroup.center (Su F0 2 1 m)) ≤ Nat.card F0ˣ :=
        Nat.card_le_card_of_injective f hf
    _ = 3 := hcard

end KerPi

section Perfect

private lemma qTwoLMDivCoordInner_lift_commutator_hom {H : Type} [Group H]
    (x : H) (hcen : ∀ y : H, ⁅x, y⁆ ∈ Subgroup.center H) :
    ∃ φ : H →* Subgroup.center H, ∀ y : H, (φ y : H) = ⁅x, y⁆ := by
  refine ⟨MonoidHom.mk' (fun y => ⟨⁅x, y⁆, hcen y⟩) (fun y z => Subtype.ext ?_),
    fun y => rfl⟩
  show ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆
  have hc : y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ := by
    rw [Subgroup.mem_center_iff.1 (hcen z) y, mul_inv_cancel_right]
  calc ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by rw [hc]

private lemma qTwoLMDivCoordInner_lift_hom_center_eq_one {H : Type} [Group H]
    (hperf : commutator H = ⊤) (φ : H →* Subgroup.center H) (y : H) : φ y = 1 := by
  have hle : commutator H ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    apply Subtype.ext
    show (⁅(φ a : H), (φ b : H)⁆ : H) = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (φ a).2 (φ b)).symm
  have htop : ⊤ ≤ φ.ker := hperf ▸ hle
  have hy : y ∈ φ.ker := htop trivial
  simpa [MonoidHom.mem_ker] using hy

end Perfect

theorem qTwoLMDivCoordInner_kerpi {Bs L : Subgroup G} (hperf : commutator ↥L = ⊤)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 4 ≤ m) {F0 : Type}
    [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0] {c : ↥L →* L0}
    {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) :
    (3 ∣ Nat.card (Subgroup.center ↥L) → π.ker = ⊥) ∧
      (¬ 3 ∣ Nat.card (Subgroup.center ↥L) → ∀ z ∈ Subgroup.center (Su F0 2 1 m), z ∈ π.ker) := by
  classical
  have hK : Nat.card F0 = (2 ^ 1) ^ 2 := by rw [hU.card]; norm_num
  have hperfS : commutator (Su F0 2 1 m) = ⊤ := by
    have h3 : m = 3 → ∃ s : F0, s ≠ 0 ∧ unitaryInvolution F0 2 1 s * s ≠ 1 := by
      intro hm3
      exfalso
      omega
    exact CFSG.ClassicalGroups.Unitary.commutator_SUid_eq_top
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) (by omega) h3
  constructor
  · intro h3dvd
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    by_contra hk1
    have hkZ : k ∈ Subgroup.center (Su F0 2 1 m) := hU.π_ker hk
    have hk3 : k ^ 3 = 1 := qTwoLMDivCoordInner_lift_center_cube hU.card hm hkZ
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hordk : orderOf k = 3 := orderOf_eq_prime hk3 hk1
    have hker_eq : π.ker = Subgroup.center (Su F0 2 1 m) := by
      refine Subgroup.eq_of_le_of_card_ge hU.π_ker ?_
      have h3le : 3 ≤ Nat.card π.ker := by
        have hz : Subgroup.zpowers k ≤ π.ker := Subgroup.zpowers_le.mpr hk
        have hcard : Nat.card (Subgroup.zpowers k) = 3 :=
          (Nat.card_zpowers (a := k)).trans hordk
        calc (3 : ℕ) = Nat.card (Subgroup.zpowers k) := hcard.symm
          _ ≤ Nat.card π.ker := Subgroup.card_le_of_le hz
      exact le_trans (qTwoLMDivCoordInner_lift_center_card_le hU.card hm) h3le
    obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' 3 (G := Subgroup.center ↥L) h3dvd
    have hz3 : (z : ↥L) ^ 3 = 1 := by
      have h : z ^ 3 = 1 := by
        rw [← hzord]
        exact pow_orderOf_eq_one z
      rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
    have hcz_ne : c (z : ↥L) ≠ 1 := by
      intro hc1
      have hzk : (z : ↥L) ∈ c.ker := MonoidHom.mem_ker.mpr hc1
      have hz1 : (z : ↥L) = 1 :=
        qTwoLMDivCoordInner_lift_eq_one_of_mem_ker_of_pow hU.c_two hzk hz3
      have hz1sub : z = 1 := Subtype.ext hz1
      rw [hz1sub, orderOf_one] at hzord
      exact absurd hzord (by norm_num)
    have hcz_center : c (z : ↥L) ∈ Subgroup.center L0 := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨l, rfl⟩ := hU.c_surj y
      calc c l * c ↑z = c (l * ↑z) := (map_mul c l ↑z).symm
        _ = c (↑z * l) := by rw [Subgroup.mem_center_iff.mp z.2 l]
        _ = c ↑z * c l := map_mul c ↑z l
    obtain ⟨s, hs⟩ := hU.π_surj (c (z : ↥L))
    have hmem : ∀ s' : Su F0 2 1 m, ⁅s, s'⁆ ∈ Subgroup.center (Su F0 2 1 m) := by
      intro s'
      apply hU.π_ker
      rw [MonoidHom.mem_ker, map_commutatorElement, hs]
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hcz_center (π s')).symm
    have hsZ : s ∈ Subgroup.center (Su F0 2 1 m) := by
      obtain ⟨φ, hφ⟩ := qTwoLMDivCoordInner_lift_commutator_hom s hmem
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : s * y = y * s := by
        have h1 : (φ y : Su F0 2 1 m) = 1 := by
          simpa using congrArg (fun z : Subgroup.center (Su F0 2 1 m) => (z : Su F0 2 1 m))
            (qTwoLMDivCoordInner_lift_hom_center_eq_one hperfS φ y)
        have h2 : ⁅s, y⁆ = 1 := by rw [← hφ y, h1]
        exact commutatorElement_eq_one_iff_mul_comm.mp h2
      exact hy.symm
    have hs_ker : s ∈ π.ker := by rw [hker_eq]; exact hsZ
    rw [MonoidHom.mem_ker] at hs_ker
    exact hcz_ne (hs ▸ hs_ker)
  · intro h3notdvd z hz
    rw [MonoidHom.mem_ker]
    by_contra hzne
    have hz3 : z ^ 3 = 1 := qTwoLMDivCoordInner_lift_center_cube hU.card hm hz
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hordz : orderOf (π z) = 3 := by
      apply orderOf_eq_prime
      · rw [← map_pow, hz3, map_one]
      · exact hzne
    have hzcenter : π z ∈ Subgroup.center L0 := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨s', rfl⟩ := hU.π_surj y
      calc π s' * π z = π (s' * z) := (map_mul π s' z).symm
        _ = π (z * s') := by rw [Subgroup.mem_center_iff.mp hz s']
        _ = π z * π s' := map_mul π z s'
    obtain ⟨l, hl⟩ := hU.c_surj (π z)
    have hmemL : ∀ l' : ↥L, ⁅l, l'⁆ ∈ Subgroup.center ↥L := by
      intro l'
      apply hU.c_ker
      rw [MonoidHom.mem_ker, map_commutatorElement, hl]
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hzcenter (c l')).symm
    have hlZ : l ∈ Subgroup.center ↥L := by
      obtain ⟨φ, hφ⟩ := qTwoLMDivCoordInner_lift_commutator_hom l hmemL
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : l * y = y * l := by
        have h1 : (φ y : ↥L) = 1 := by
          simpa using congrArg (fun z : Subgroup.center ↥L => (z : ↥L))
            (qTwoLMDivCoordInner_lift_hom_center_eq_one hperf φ y)
        have h2 : ⁅l, y⁆ = 1 := by rw [← hφ y, h1]
        exact commutatorElement_eq_one_iff_mul_comm.mp h2
      exact hy.symm
    have h3dvd : 3 ∣ Nat.card (Subgroup.center ↥L) := by
      have h1 : orderOf (π z) = orderOf (c l) := by rw [← hl]
      rw [← hordz, h1]
      exact (orderOf_map_dvd c l).trans (by
        rw [← Subgroup.orderOf_mk l hlZ]
        exact orderOf_dvd_natCard _)
    exact h3notdvd h3dvd

end CFSG.StandardType.QTwo

end
