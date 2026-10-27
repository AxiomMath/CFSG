module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.RankThree.PartTwo.Sec15.Sylow155CDTest
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec21.FF84S23Sub
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Quasithin.Vol2.Ch11SKFIto

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

variable {Q : Type} [Group Q]

private theorem zpow_cases_of_pow_three {u : Q} (hu3 : u ^ 3 = 1) (j : ℤ) :
    u ^ j = 1 ∨ u ^ j = u ∨ u ^ j = u ^ 2 := by
  rw [zpow_eq_zpow_emod' j hu3]
  have hj : j % ((3 : ℕ) : ℤ) = 0 ∨ j % ((3 : ℕ) : ℤ) = 1 ∨ j % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hj with hj | hj | hj <;> rw [hj] <;> simp

private theorem zpow_eq_one_of_commute {u x : Q} (hu3 : u ^ 3 = 1) (hux : u * x ≠ x * u) (j : ℤ)
    (hj : u ^ j * x = x * u ^ j) : u ^ j = 1 := by
  rcases zpow_cases_of_pow_three hu3 j with h | h | h
  · exact h
  · rw [h] at hj
    exact absurd hj hux
  · rw [h] at hj
    refine absurd ?_ hux
    have h4 : (u ^ 2) ^ 2 = u := by
      calc (u ^ 2) ^ 2 = u ^ 3 * u := by group
        _ = u := by rw [hu3, one_mul]
    have h5 := (Commute.pow_left (show Commute (u ^ 2) x from hj) 2).eq
    rwa [h4] at h5

private theorem mem_zpowers_of_mem_zpowers_of_pow_three {z d : Q} (hz3 : z ^ 3 = 1) (hd1 : d ≠ 1)
    (hd : d ∈ Subgroup.zpowers z) : z ∈ Subgroup.zpowers d := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
  rcases zpow_cases_of_pow_three hz3 j with h | h | h
  · exact absurd h hd1
  · rw [h]
    exact Subgroup.mem_zpowers z
  · rw [h]
    have h4 : (z ^ 2) ^ 2 = z := by
      calc (z ^ 2) ^ 2 = z ^ 3 * z := by group
        _ = z := by rw [hz3, one_mul]
    have h5 := Subgroup.pow_mem (Subgroup.zpowers (z ^ 2)) (Subgroup.mem_zpowers (z ^ 2)) 2
    rwa [h4] at h5

private theorem exists_mul_of_mem_sup {H N : Subgroup Q}
    (hHN : ∀ a ∈ H, ∀ b ∈ N, a * b = b * a) {x : Q} (hx : x ∈ H ⊔ N) :
    ∃ a ∈ H, ∃ b ∈ N, a * b = x := by
  have hN : N ≤ Subgroup.normalizer (H : Set Q) := fun b hb =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hHN a ha b hb)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left H N hN] at hx
  exact Set.mem_mul.mp hx

private theorem mem_zpowers_of_mem_sup {z u x d : Q} (hzu : z * u = u * z) (hu3 : u ^ 3 = 1)
    (hxz : x * z = z * x) (hxd : x * d = d * x) (hux : u * x ≠ x * u)
    (hd : d ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers u) : d ∈ Subgroup.zpowers z := by
  have hcomm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers u, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute z u from hzu) i j).eq
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hd
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hxzi : x * z ^ i = z ^ i * x := (Commute.zpow_right (show Commute x z from hxz) i).eq
  have hxuj : u ^ j * x = x * u ^ j := by
    refine mul_left_cancel (a := z ^ i) ?_
    calc z ^ i * (u ^ j * x) = (z ^ i * u ^ j) * x := by rw [mul_assoc]
      _ = x * (z ^ i * u ^ j) := hxd.symm
      _ = (x * z ^ i) * u ^ j := by rw [mul_assoc]
      _ = (z ^ i * x) * u ^ j := by rw [hxzi]
      _ = z ^ i * (x * u ^ j) := by rw [mul_assoc]
  rw [zpow_eq_one_of_commute hu3 hux j hxuj, mul_one]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) i

private theorem comm_of_ne [Finite Q] {J₁ J₂ : Subgroup Q} (h₁ : CFSG.IsComponent J₁)
    (h₂ : CFSG.IsComponent J₂) (hne : J₁ ≠ J₂) : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute h₁ h₂ with h | h
  · exact absurd h hne
  · intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm

namespace Res3QBase

variable [Finite Q] {c d : Q} {A B₀ K : Subgroup Q}

private theorem isComponent_K (h : Res3QBase c d A B₀ K) : CFSG.IsComponent K :=
  ⟨h.K_quasi, h.K_subnormal⟩

private theorem card_zpowers_d (h : Res3QBase c d A B₀ K) :
    Nat.card (Subgroup.zpowers d) = 3 := by
  rw [← h.K_center, Subgroup.card_map_of_injective K.subtype_injective]
  exact h.K_cover.1

private theorem d_pow (h : Res3QBase c d A B₀ K) : d ^ 3 = 1 := h.B₀_pow d h.d_mem

private theorem d_ne_one (h : Res3QBase c d A B₀ K) : d ≠ 1 := by
  intro hd
  have h3 := h.card_zpowers_d
  rw [hd, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
  exact absurd h3 (by norm_num)

private theorem d_commute (h : Res3QBase c d A B₀ K) (g : Q) : g * d = d * g :=
  Subgroup.mem_center_iff.mp h.d_center g

private theorem d_mem_centralizer (h : Res3QBase c d A B₀ K) :
    d ∈ Subgroup.centralizer (K : Set Q) :=
  Subgroup.center_le_centralizer _ h.d_center

private theorem mem_zpowers_of_mem_centralizer (h : Res3QBase c d A B₀ K) {x : Q} (hxK : x ∈ K)
    (hx : x ∈ Subgroup.centralizer (K : Set Q)) : x ∈ Subgroup.zpowers d := by
  rw [← h.K_center]
  refine ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx g g.2)

private theorem exists_mul_of_mem_A (h : Res3QBase c d A B₀ K) {x : Q} (hx : x ∈ A) :
    ∃ b ∈ B₀, ∃ z ∈ Subgroup.zpowers c, b * z = x := by
  rw [h.A_eq] at hx
  refine exists_mul_of_mem_sup (fun a ha b hb => ?_) hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_right
    (show Commute a c from Subgroup.mem_centralizer_iff.mp h.c_cent a (h.B₀_le ha)) k).eq

theorem inf_centralizer (h : Res3QBase c d A B₀ K) :
    A ⊓ Subgroup.centralizer (K : Set Q) = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  have hcA : Subgroup.zpowers c ≤ A := by
    rw [h.A_eq]
    exact le_sup_right
  have hdA : d ∈ A := by
    rw [h.A_eq]
    exact Subgroup.mem_sup_left h.d_mem
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro x ⟨hxA, hxK⟩
    obtain ⟨b, hb, z, hz, rfl⟩ := h.exists_mul_of_mem_A hxA
    have hzK : z ∈ Subgroup.centralizer (K : Set Q) := Subgroup.zpowers_le.mpr h.c_cent hz
    have hbK : b ∈ Subgroup.centralizer (K : Set Q) := by
      have := Subgroup.mul_mem _ hxK (Subgroup.inv_mem _ hzK)
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right (h.mem_zpowers_of_mem_centralizer (h.B₀_le hb) hbK))
      (Subgroup.mem_sup_left hz)
  · exact le_inf hcA (Subgroup.zpowers_le.mpr h.c_cent)
  · exact Subgroup.zpowers_le.mpr ⟨hdA, h.d_mem_centralizer⟩

theorem mem_of_pow_three (h : Res3QBase c d A B₀ K) {x : Q}
    (hxK : x ∈ Subgroup.centralizer (K : Set Q)) (hxc : Commute x c) (hx3 : x ^ 3 = 1) :
    x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  rw [← h.inf_centralizer]
  refine ⟨h.A_max x ?_ hx3, hxK⟩
  have hA : A ≤ Subgroup.centralizer ({x} : Set Q) := by
    rw [h.A_eq]
    refine sup_le (fun b hb => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxK b (h.B₀_le hb))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hxc.eq.symm
  exact Subgroup.mem_centralizer_iff.mpr fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hA ha)

theorem le_centralizer (h : Res3QBase c d A B₀ K) {J : Subgroup Q} (hJ : CFSG.IsComponent J)
    (hJK : J ≠ K) : J ≤ Subgroup.centralizer (K : Set Q) := by
  rcases CFSG.LocalCores.distinct_components_commute hJ h.isComponent_K with h1 | h1
  · exact absurd h1 hJK
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1

theorem mem_normalizer (h : Res3QBase c d A B₀ K) {x : Q}
    (hx : x ∈ Subgroup.centralizer (B₀ : Set Q)) : x ∈ Subgroup.normalizer (K : Set Q) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hKx : CFSG.IsComponent (K.map (MulAut.conj x : Q →* Q)) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) h.isComponent_K
  have hcent := h.le_centralizer hKx hne
  have hB₀ : B₀ ≤ K.map (MulAut.conj x : Q →* Q) := fun b hb =>
    ⟨b, h.B₀_le hb, by
      have hbx := Subgroup.mem_centralizer_iff.mp hx b hb
      show x * b * x⁻¹ = b
      rw [← hbx, mul_inv_cancel_right]⟩
  have hle : B₀ ≤ Subgroup.zpowers d := fun b hb =>
    h.mem_zpowers_of_mem_centralizer (h.B₀_le hb) (hcent (hB₀ hb))
  have hcard := Subgroup.card_le_of_le hle
  rw [h.B₀_card, h.card_zpowers_d] at hcard
  omega

private theorem eq_bot_of_isSubnormal (h : Res3QBase c d A B₀ K) {N : Subgroup Q}
    (hN : N.IsSubnormal) (h3 : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  have hO3 : CFSG.pPrimeCore 3 Q = ⊥ :=
    CFSG.pPrimeCore_eq_bot_iff.mpr fun M hM hcop =>
      h.oThreePrime M hM ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop)
  have hle := CFSG.RankThree.PartTwo.Sec21.FF84.le_pPrimeCore_of_isSubnormal' (p := 3) hN
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  rw [hO3] at hle
  exact le_bot_iff.mp hle

theorem three_dvd_card (h : Res3QBase c d A B₀ K) {J : Subgroup Q} (hJ : CFSG.IsComponent J) :
    3 ∣ Nat.card J := by
  by_contra h3
  have hJ1 : J = ⊥ := h.eq_bot_of_isSubnormal hJ.2 h3
  haveI := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
  exact (Subgroup.nontrivial_iff_ne_bot J).mp this hJ1

theorem isPGroup_center (h : Res3QBase c d A B₀ K) {J : Subgroup Q} (hJ : CFSG.IsComponent J) :
    IsPGroup 3 (Subgroup.center ↥J) := by
  rintro ⟨z, hz⟩
  have hzc : ∀ g ∈ J, g * (z : Q) = (z : Q) * g := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
  obtain ⟨e, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (z : Q)).ne' 3 (by norm_num)
  set w : Q := (z : Q) ^ 3 ^ e with hw
  have hwo : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (pow_ne_zero e (by norm_num)) (hord ▸ dvd_mul_right _ _), hord]
    exact Nat.mul_div_cancel_left m (pow_pos (by norm_num) e)
  have hwJ : w ∈ J := J.pow_mem z.2 _
  have hWJ : Subgroup.zpowers w ≤ J := Subgroup.zpowers_le.mpr hwJ
  have hWn : ((Subgroup.zpowers w).subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hWJ]
    intro g hg
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hgw : Commute g w := Commute.pow_right (show Commute g (z : Q) from hzc g hg) (3 ^ e)
    exact (hgw.zpow_right k).eq.symm
  have hsn : (Subgroup.zpowers w).IsSubnormal :=
    Subgroup.IsSubnormal.step _ J hWJ hJ.2 hWn
  have hW3 : ¬ 3 ∣ Nat.card (Subgroup.zpowers w) := by
    rw [Nat.card_zpowers, hwo]
    exact hm
  have hw1 : w = 1 := Subgroup.zpowers_eq_bot.mp (h.eq_bot_of_isSubnormal hsn hW3)
  exact ⟨e, Subtype.ext (Subtype.ext hw1)⟩

theorem exists_pow_three_noncomm_of_isComponent (h : Res3QBase c d A B₀ K) {J : Subgroup Q}
    (hJ : CFSG.IsComponent J) : ∃ u ∈ J, u ^ 3 = 1 ∧ ∃ x ∈ J, u * x ≠ x * u := by
  haveI : Group.IsPerfect ↥J := hJ.1.1
  obtain ⟨u, hu3, huZ⟩ := CFSG.Quasithin.Vol2.Ch11.SecS.KF.exists_pow_eq_one_not_mem_center
    (p := 3) (L := ↥J) (by norm_num) (h.three_dvd_card hJ)
  refine ⟨u, u.2, by simpa using congrArg Subtype.val hu3, ?_⟩
  by_contra! hcon
  exact huZ (Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hcon g g.2).symm)

theorem d_mem_of_card_nine_le_centralizer (h : Res3QBase c d A B₀ K) {E : Subgroup Q}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEK : E ≤ Subgroup.centralizer (K : Set Q)) : d ∈ E := by
  by_contra hd
  obtain ⟨hE₂, hE₂c⟩ := Sec5.isElemAbelian_sup_zpowers (p := 3) hE hd h.d_pow
    fun a _ => h.d_commute a
  have hE₂K : E ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer (K : Set Q) :=
    sup_le hEK (Subgroup.zpowers_le.mpr h.d_mem_centralizer)
  obtain ⟨y, hy3, hyZ, V, hV2, hV1, hyV⟩ :=
    Sylow155CD.exists_pow_three_le_normalizer_two h.K_cover
  have hkK : (y : Q) ∈ K := y.2
  have hk3 : (y : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
  have hkE₂ : (y : Q) ∉ E ⊔ Subgroup.zpowers d := fun hk =>
    hyZ (Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hE₂K hk) g g.2))
  obtain ⟨hE₃, hE₃c⟩ := Sec5.isElemAbelian_sup_zpowers (p := 3) hE₂ hkE₂ hk3
    fun a ha => (Subgroup.mem_centralizer_iff.mp (hE₂K ha) (y : Q) hkK).symm
  have hE81 : Nat.card ↥(E ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers (y : Q)) = 81 := by
    rw [hE₃c, hE₂c, hE9]
  refine h.R4 _ (V.map K.subtype) hE₃ hE81 (hV2.map K.subtype) ?_ ?_
  · intro hbot
    exact hV1 ((Subgroup.map_eq_bot_iff_of_injective V K.subtype_injective).mp hbot)
  · refine sup_le (fun g hg => Subgroup.centralizer_le_normalizer _ ?_)
      (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
        Subgroup.mem_centralizer_iff.mp (hE₂K hg) t (Subgroup.map_subtype_le V ht)
    · exact Subgroup.le_normalizer_map K.subtype ⟨y, hyV, rfl⟩

theorem eq_of_isComponent (h : Res3QBase c d A B₀ K) {J₁ J₂ : Subgroup Q}
    (h₁ : CFSG.IsComponent J₁) (h₂ : CFSG.IsComponent J₂) (h₁K : J₁ ≠ K) (h₂K : J₂ ≠ K) :
    J₁ = J₂ := by
  by_contra hne
  obtain ⟨u₁, hu₁J, hu₁3, x₁, hx₁J, hx₁⟩ := h.exists_pow_three_noncomm_of_isComponent h₁
  obtain ⟨u₂, hu₂J, hu₂3, x₂, hx₂J, hx₂⟩ := h.exists_pow_three_noncomm_of_isComponent h₂
  have hcomm := comm_of_ne h₁ h₂ hne
  have hu₁₂ : u₁ * u₂ = u₂ * u₁ := hcomm u₁ hu₁J u₂ hu₂J
  have hu₁1 : u₁ ≠ 1 := fun h1 => hx₁ (by rw [h1, one_mul, mul_one])
  have hu₂1 : u₂ ≠ 1 := fun h1 => hx₂ (by rw [h1, one_mul, mul_one])
  have hu₂n : u₂ ∉ Subgroup.zpowers u₁ := by
    intro hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : u₁ ^ j = 1 := zpow_eq_one_of_commute hu₁3 hx₁ j (by
      rw [hj]
      exact (hcomm x₁ hx₁J u₂ hu₂J).symm)
    rw [hj] at h1
    exact hu₂1 h1
  obtain ⟨hE, hEc⟩ := Sec5.isElemAbelian_sup_zpowers (p := 3)
    (CFSG.Open.isElemAbelian_zpowers hu₁3) hu₂n hu₂3 fun a ha => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (show Commute u₁ u₂ from hu₁₂) i).eq
  have hE9 : Nat.card ↥(Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂) = 9 := by
    rw [hEc, Nat.card_zpowers, orderOf_eq_prime hu₁3 hu₁1]
  have hEK : Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ ≤ Subgroup.centralizer (K : Set Q) :=
    sup_le (Subgroup.zpowers_le.mpr (h.le_centralizer h₁ h₁K hu₁J))
      (Subgroup.zpowers_le.mpr (h.le_centralizer h₂ h₂K hu₂J))
  have hd := h.d_mem_of_card_nine_le_centralizer hE hE9 hEK
  have hd₂ : d ∈ Subgroup.zpowers u₂ :=
    mem_zpowers_of_mem_sup hu₁₂.symm hu₁3 (hcomm x₁ hx₁J u₂ hu₂J) (h.d_commute x₁) hx₁
      (by rwa [sup_comm] at hd)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hd₂
  have h1 : u₂ ^ j = 1 := zpow_eq_one_of_commute hu₂3 hx₂ j (by
    rw [hj]
    exact (h.d_commute x₂).symm)
  rw [hj] at h1
  exact h.d_ne_one h1

theorem mem_zpowers_of_mem_center (h : Res3QBase c d A B₀ K) {J : Subgroup Q}
    (hJ : CFSG.IsComponent J) (hJK : J ≠ K) {z : Q}
    (hz : z ∈ (Subgroup.center ↥J).map J.subtype) (hz3 : z ^ 3 = 1) :
    z ∈ Subgroup.zpowers d := by
  have hz' : z ∈ J ∧ ∀ g ∈ J, g * z = z * g := by
    obtain ⟨zJ, hzJ, rfl⟩ := hz
    exact ⟨zJ.2, fun g hg => congrArg Subtype.val (Subgroup.mem_center_iff.mp hzJ ⟨g, hg⟩)⟩
  obtain ⟨hzJ, hzc⟩ := hz'
  by_cases hz1 : z = 1
  · rw [hz1]
    exact Subgroup.one_mem _
  obtain ⟨u, huJ, hu3, x, hxJ, hx⟩ := h.exists_pow_three_noncomm_of_isComponent hJ
  have hzu : z * u = u * z := (hzc u huJ).symm
  have hun : u ∉ Subgroup.zpowers z := by
    intro hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine hx ?_
    rw [← hj]
    exact (Commute.zpow_right (show Commute x z from hzc x hxJ) j).eq.symm
  obtain ⟨hE, hEc⟩ := Sec5.isElemAbelian_sup_zpowers (p := 3)
    (CFSG.Open.isElemAbelian_zpowers hz3) hun hu3 fun a ha => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (show Commute z u from hzu) i).eq
  have hE9 : Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers u) = 9 := by
    rw [hEc, Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
  have hEK : Subgroup.zpowers z ⊔ Subgroup.zpowers u ≤ Subgroup.centralizer (K : Set Q) :=
    sup_le (Subgroup.zpowers_le.mpr (h.le_centralizer hJ hJK hzJ))
      (Subgroup.zpowers_le.mpr (h.le_centralizer hJ hJK huJ))
  have hd := h.d_mem_of_card_nine_le_centralizer hE hE9 hEK
  have hdz : d ∈ Subgroup.zpowers z :=
    mem_zpowers_of_mem_sup hzu hu3 (hzc x hxJ) (h.d_commute x) hx hd
  exact mem_zpowers_of_mem_zpowers_of_pow_three hz3 h.d_ne_one hdz

end Res3QBase

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
