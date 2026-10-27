module

public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofDefs
import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)

namespace Item8KFactsProof

theorem exists_mem_center_orderOf_three {X : Type*} [Group X] [Finite X] (Q : Sylow 3 X)
    (hQ : Nontrivial Q) : ∃ z : X, z ∈ (Q : Subgroup X) ∧ orderOf z = 3 ∧
      ∀ y ∈ (Q : Subgroup X), z * y = y * z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Nontrivial (Subgroup.center Q) := Q.isPGroup'.center_nontrivial
  have hZp : IsPGroup 3 (Subgroup.center Q) := Q.isPGroup'.to_subgroup _
  have hdvd : 3 ∣ Nat.card (Subgroup.center Q) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne'
    · exact h
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨((w : Q) : X), ((w : Q)).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  · intro y hy
    have := Subgroup.mem_center_iff.mp w.2 ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm

theorem isPGroup_of_pow_three {X : Type*} [Group X] {E : Subgroup X}
    (h : ∀ x ∈ E, x ^ 3 = 1) : IsPGroup 3 E := fun x =>
  ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using h x x.2)⟩

theorem mem_zpowers_of_mem_zpowers {X : Type*} [Group X] {x z : X} (hx3 : x ^ 3 = 1)
    (hz : z ∈ Subgroup.zpowers x) (hz1 : z ≠ 1) : x ∈ Subgroup.zpowers z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  have hk : x ^ k = x ^ (k % 3) := by
    have hx3o : orderOf x = 3 := orderOf_eq_prime hx3 (by rintro rfl; exact hz1 (by simp))
    rw [← zpow_mod_orderOf, hx3o]
    rfl
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · exact absurd (by rw [hk, hr, zpow_zero]) hz1
  · rw [hk, hr, zpow_one]
    exact Subgroup.mem_zpowers x
  · refine Subgroup.mem_zpowers_iff.mpr ⟨2, ?_⟩
    rw [hk, hr, ← zpow_mul]
    have : x ^ ((2 : ℤ) * 2) = x ^ (3 : ℤ) * x := by
      rw [← zpow_add_one]
      norm_num
    rw [this, h3, one_mul]

theorem pow_three_of_mem_closure_pair {X : Type*} [Group X] {u v : X} (hu3 : u ^ 3 = 1)
    (hv3 : v ^ 3 = 1) (huv : u * v = v * u) :
    ∀ x ∈ Subgroup.closure ({u, v} : Set X), x ^ 3 = 1 := by
  have hS : ∀ s ∈ ({u, v} : Set X), ∀ t ∈ ({u, v} : Set X), s * t = t * s := by
    rintro s (rfl | rfl) t (rfl | rfl)
    · rfl
    · exact huv
    · exact huv.symm
    · rfl
  have hcomm : ∀ x ∈ Subgroup.closure ({u, v} : Set X),
      ∀ y ∈ Subgroup.closure ({u, v} : Set X), x * y = y * x := by
    intro x hx y hy
    have h1 : Subgroup.closure ({u, v} : Set X) ≤ Subgroup.centralizer ({u, v} : Set X) := by
      rw [Subgroup.closure_le]
      intro s hs
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro t ht
      exact hS t ht s hs
    have h2 : Subgroup.closure ({u, v} : Set X) ≤ Subgroup.centralizer ({x} : Set X) := by
      rw [Subgroup.closure_le]
      intro s hs
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro t rfl
      exact (Subgroup.mem_centralizer_iff.mp (h1 hx) s hs).symm
    exact (Subgroup.mem_centralizer_iff.mp (h2 hy) x rfl)
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with rfl | rfl
    · exact hu3
    · exact hv3
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (hcomm x hx y hy) 3), ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem e9Closed_of_commuting {X : Type*} [Group X] [Finite X] {u v : X} (hu1 : u ≠ 1)
    (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (huv : u * v = v * u)
    (hvu : v ∉ Subgroup.zpowers u) : E9Closed X := by
  intro x hx3 hx1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hEP⟩ :=
    (isPGroup_of_pow_three (pow_three_of_mem_closure_pair hu3 hv3 huv)).exists_le_sylow
  have hxp : ∀ y ∈ Subgroup.zpowers x, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  obtain ⟨Q, hxQ⟩ := (isPGroup_of_pow_three hxp).exists_le_sylow
  have hxQ' : x ∈ (Q : Subgroup X) := hxQ (Subgroup.mem_zpowers x)
  have hQnt : Nontrivial Q := ⟨⟨⟨x, hxQ'⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  obtain ⟨z, -, hz3, hzc⟩ := exists_mem_center_orderOf_three Q hQnt
  by_cases hzx : z ∈ Subgroup.zpowers x
  ·
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hz3
      omega
    have hxz := mem_zpowers_of_mem_zpowers hx3 hzx hz1
    have hxc : ∀ y ∈ (Q : Subgroup X), x * y = y * x := by
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
      exact (Commute.zpow_left (hzc y hy) k)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
    have hconjQ : ∀ w ∈ Subgroup.closure ({u, v} : Set X),
        g * w * g⁻¹ ∈ (Q : Subgroup X) := by
      intro w hw
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨w, hEP hw, rfl⟩
    have huQ := hconjQ u (Subgroup.subset_closure (by simp))
    have hvQ := hconjQ v (Subgroup.subset_closure (by simp))
    by_cases hux : g * u * g⁻¹ ∈ Subgroup.zpowers x
    · refine ⟨g * v * g⁻¹, ?_, hxc _ hvQ, fun hvx => hvu ?_⟩
      · rw [conj_pow, hv3, mul_one, mul_inv_cancel]
      · have hu1' : g * u * g⁻¹ ≠ 1 := by
          intro h
          apply hu1
          have := congrArg (fun w => g⁻¹ * w * g) h
          simpa [mul_assoc] using this
        have hxu := mem_zpowers_of_mem_zpowers hx3 hux hu1'
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvx
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxu
        refine Subgroup.mem_zpowers_iff.mpr ⟨j * k, ?_⟩
        have h1 : (g * u * g⁻¹) ^ (j * k) = g * v * g⁻¹ := by rw [zpow_mul, hj, hk]
        rw [conj_zpow] at h1
        have := congrArg (fun w => g⁻¹ * w * g) h1
        simpa [mul_assoc] using this
    · exact ⟨g * u * g⁻¹, by rw [conj_pow, hu3, mul_one, mul_inv_cancel], hxc _ huQ, hux⟩
  · exact ⟨z, by rw [← hz3]; exact pow_orderOf_eq_one z, (hzc x hxQ').symm, hzx⟩

theorem exists_pair_of_isElemAbelian {X : Type*} [Group X] {E : Subgroup X}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    ∃ u v : X, u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧ v ∉ Subgroup.zpowers u := by
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [h9]; norm_num)
  have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [h9]; norm_num)
  obtain ⟨⟨u, huE⟩, hu1⟩ := exists_ne (1 : E)
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu3 := hE.2 u huE
  have : Finite (Subgroup.zpowers u) :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hu3⟩).finite_zpowers
  have hnle : ¬ (E : Set X) ⊆ Subgroup.zpowers u := by
    intro hle
    have hle' : E ≤ Subgroup.zpowers u := hle
    have h1 := Subgroup.card_le_of_le hle'
    rw [Nat.card_zpowers, h9] at h1
    have h2 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨v, hvE, hvu⟩ := Set.not_subset.mp hnle
  refine ⟨u, v, hu1', hu3, hE.2 v hvE, ?_, hvu⟩
  exact congrArg Subtype.val (hE.1.1.comm ⟨u, huE⟩ ⟨v, hvE⟩)

theorem exists_pair_of_injective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f)
    (h : ∃ u v : X, u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧ v ∉ Subgroup.zpowers u) :
    ∃ u v : Y, u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧ v ∉ Subgroup.zpowers u := by
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := h
  refine ⟨f u, f v, fun h1 => hu1 (hf (h1.trans (map_one f).symm)), by rw [← map_pow, hu3,
    map_one], by rw [← map_pow, hv3, map_one], by rw [← map_mul, huv, map_mul], fun hv => hvu ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, hf (by rw [map_zpow, hk])⟩

theorem e9Pair_of_map_eq {A B C : Type*} [Group A] [Group B] [Group C] (ψ : A →* B)
    (hψ : Function.Injective ψ) (Φ : C →* B) (hΦ : Function.Injective Φ) {u v : A} {c d : C}
    (hu : ψ u = Φ c) (hv : ψ v = Φ d) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hcd : c * d = d * c) (hdc : d ∉ Subgroup.zpowers c) :
    u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧ v ∉ Subgroup.zpowers u := by
  refine ⟨fun h => hc1 (hΦ (by rw [← hu, h, map_one, map_one])), hψ ?_, hψ ?_, hψ ?_, ?_⟩
  · rw [map_pow, hu, ← map_pow, hc3, map_one, map_one]
  · rw [map_pow, hv, ← map_pow, hd3, map_one, map_one]
  · rw [map_mul, map_mul, hu, hv, ← map_mul, ← map_mul, hcd]
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hdc
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, hΦ ?_⟩
    rw [map_zpow, ← hu, ← map_zpow, hk, hv]

theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

end Item8KFactsProof

open Item8KFactsProof

theorem kF82E9GTwo_holds :
    KF82E9GTwo := by
  intro K _ _ n _ _
  have : Finite (CFSG.Blueprint.Chevalley.ModGL .G2 K) := CFSG.LieType.Chevalley.finite_modGL
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := Sec11.KS11Lie2Proof.g2_exists_e9 K
  exact e9Closed_of_commuting hu1 hu3 hv3 huv hvu

theorem finite_and_exists_pair_of_isoPGUThree {n : ℕ} (hn : Odd n) {X : Type} [Group X]
    (h : IsoPGUThree X (2 ^ n)) :
    Finite X ∧ ∃ u v : X, u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧
      v ∉ Subgroup.zpowers u := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hPi : Sec4.PiField false 2 n K := ⟨Nat.prime_two, hn.pos, by rw [hK]; rfl⟩
  have hq : Sec4.ModThree false (2 ^ n) := two_pow_mod_three_of_odd hn
  obtain ⟨D, hD, h9⟩ := Sec13.exists_elemAbelian_nine_projImage_slPi hPi hq
  have hU := hPi.unitary
  have hle : projImage (Sec4.slPi false 3 (2 ^ n) K) ≤
      projImage (Sec4.glPi false 3 (2 ^ n) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (fun _ => hU))
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) := by
    unfold Matrix.ProjGenLinGroup
    infer_instance
  exact ⟨Finite.of_equiv _ e.symm.toEquiv,
    exists_pair_of_injective (e.symm.toMonoidHom.comp (Subgroup.inclusion hle))
      (e.symm.injective.comp (Subgroup.inclusion_injective hle))
      (exists_pair_of_isElemAbelian hD h9)⟩

theorem kF82E9PGUThree_holds : KF82E9PGUThree := by
  intro X _ n hn h
  obtain ⟨hX, u, v, hu1, hu3, hv3, huv, hvu⟩ := finite_and_exists_pair_of_isoPGUThree hn h
  exact e9Closed_of_commuting hu1 hu3 hv3 huv hvu

end CFSG.RankThree.PartTwo.Sec8
