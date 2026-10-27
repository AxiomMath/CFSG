module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartTwo.Sec21.FF81Sec44
import CFSG.RankThree.PartTwo.Sec21.FF81KFacts
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81J
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.GenCoreBT
import CFSG.GroupTheory.ElemAbelianClosure

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem eq_one_of_pow_two_of_odd {c : G} {k m : ℕ} (hk : c ^ (2 ^ k) = 1) (hm : orderOf c ∣ m)
    (hodd : Odd m) : c = 1 := by
  have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hc : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp ((hc.coprime_dvd_left h1).eq_one_of_dvd hm)

theorem mem_conjBy_iff {g y : G} {U : Subgroup G} : y ∈ conjBy g U ↔ g⁻¹ * y * g ∈ U := by
  change y ∈ U.map (MulAut.conj g).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem mem_nor_conjBy {g y : G} {U : Subgroup G}
    (h : ∀ u ∈ U, (g⁻¹ * y * g) * u * (g⁻¹ * y * g)⁻¹ ∈ U) :
    y ∈ Nor (conjBy g U) := by
  refine Subgroup.mem_normalizer_fintype fun r hr => ?_
  rw [SetLike.mem_coe, mem_conjBy_iff] at hr ⊢
  have := h _ hr
  rwa [show (g⁻¹ * y * g) * (g⁻¹ * r * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * r * y⁻¹) * g by group]
    at this

theorem conjBy_inf_cen (g x : G) (U : Subgroup G) :
    conjBy g (U ⊓ Cen x) = conjBy g U ⊓ Cen (g * x * g⁻¹) := by
  rw [cen_conj]
  exact Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective

theorem card_conjBy (g : G) (U : Subgroup G) : Nat.card ↥(conjBy g U) = Nat.card U :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conj_mem_of_closure {S : Set G} {K : Subgroup G} {n : G}
    (h : ∀ x ∈ S, n * x * n⁻¹ ∈ K) {x : G} (hx : x ∈ Subgroup.closure S) : n * x * n⁻¹ ∈ K := by
  have hle : Subgroup.closure S ≤ K.comap (MulAut.conj n).toMonoidHom :=
    (Subgroup.closure_le _).mpr fun y hy => by simpa using h y hy
  simpa using hle hx

theorem cen_eq_nor_zpowers_of_two {t : G} (ht : orderOf t = 2) :
    Cen t = Nor (Subgroup.zpowers t) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [show g * t ^ k * g⁻¹ = t ^ k by rw [(Commute.zpow_right hg k).eq]; group]
    exact Subgroup.zpow_mem_zpowers t k
  · intro hg
    have h1 : g * t * g⁻¹ ∈ Subgroup.zpowers t :=
      (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
    have h2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    have hne : g * t * g⁻¹ ≠ 1 := fun h => by
      have : t = 1 := by
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
      rw [this, orderOf_one] at ht
      exact absurd ht (by norm_num)
    have hmem : g * t * g⁻¹ = t := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      rw [zpow_eq_zpow_emod' k h2] at hk
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · rw [show k % ((2 : ℕ) : ℤ) = 0 from h, zpow_zero] at hk
        exact absurd hk.symm hne
      · rw [show k % ((2 : ℕ) : ℤ) = 1 from h, zpow_one] at hk
        exact hk.symm
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [hmem]

theorem exists_pow_mul_pow_of_mem_closure {x y : G} (hxy : x * y = y * x) (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) {e : G} (he : e ∈ Subgroup.closure ({x, y} : Set G)) :
    ∃ i j : ℕ, e = x ^ i * y ^ j := by
  have hc : Commute x y := hxy
  induction he using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul a c _ _ ha hc' =>
    obtain ⟨i, j, rfl⟩ := ha
    obtain ⟨k, l, rfl⟩ := hc'
    refine ⟨i + k, j + l, ?_⟩
    have : y ^ j * x ^ k = x ^ k * y ^ j := ((hc.pow_pow k j).eq).symm
    rw [pow_add, pow_add]
    calc x ^ i * y ^ j * (x ^ k * y ^ l) = x ^ i * (y ^ j * x ^ k) * y ^ l := by
          simp only [mul_assoc]
      _ = x ^ i * (x ^ k * y ^ j) * y ^ l := by rw [this]
      _ = x ^ i * x ^ k * (y ^ j * y ^ l) := by simp only [mul_assoc]
  | inv a _ ha =>
    obtain ⟨i, j, rfl⟩ := ha
    refine ⟨2 * i, 2 * j, ?_⟩
    have hxi : (x ^ i)⁻¹ = x ^ (2 * i) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_add, show 2 * i + i = 3 * i by ring, pow_mul, hx, one_pow]
    have hyj : (y ^ j)⁻¹ = y ^ (2 * j) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_add, show 2 * j + j = 3 * j by ring, pow_mul, hy, one_pow]
    rw [mul_inv_rev, hxi, hyj]
    exact ((hc.pow_pow (2 * i) (2 * j)).eq).symm

theorem pow_mod_three {x : G} (hx : x ^ 3 = 1) (i : ℕ) : x ^ i = x ^ (i % 3) := by
  conv_lhs => rw [← Nat.div_add_mod i 3, pow_add, pow_mul, hx, one_pow, one_mul]

theorem mem_cen_line {x y v e : G} (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (he : e ∈ Subgroup.closure ({x, y} : Set G)) (he1 : e ≠ 1) (hv : v ∈ Cen e) :
    v ∈ Cen x ∨ v ∈ Cen y ∨ v ∈ Cen (x * y) ∨ v ∈ Cen (x * y⁻¹) := by
  have hc : Commute x y := hxy
  obtain ⟨i, j, rfl⟩ := exists_pow_mul_pow_of_mem_closure hxy hx hy he
  rw [pow_mod_three hx i, pow_mod_three hy j] at he1 hv
  have hsq : ∀ a c : ℕ, Cen (x ^ a * y ^ c) ≤ Cen (x ^ (2 * a) * y ^ (2 * c)) := fun a c => by
    have : x ^ (2 * a) * y ^ (2 * c) = (x ^ a * y ^ c) ^ 2 := by
      rw [(hc.pow_pow a c).mul_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm c]
    rw [this]
    exact cen_le_cen_of_mem_zpowers (Subgroup.npow_mem_zpowers _ 2)
  have hy2 : y ^ 2 = y⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hy])
  have hx4 : x ^ 4 = x := by rw [show 4 = 3 + 1 by rfl, pow_succ, hx, one_mul]
  have hy4 : y ^ 4 = y := by rw [show 4 = 3 + 1 by rfl, pow_succ, hy, one_mul]
  have hi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize i % 3 = a at hi he1 hv
  generalize j % 3 = c at hj he1 hv
  interval_cases a <;> interval_cases c
  · simp at he1
  · right; left; simpa using hv
  · right; left
    have := hsq 0 2 hv
    simpa [hy4] using this
  · left; simpa using hv
  · right; right; left; simpa using hv
  · right; right; right; simpa [hy2] using hv
  · left
    have := hsq 2 0 hv
    simpa [hx4] using this
  · right; right; right
    have := hsq 2 1 hv
    simpa [hx4, hy2] using this
  · right; right; left
    have := hsq 2 2 hv
    simpa [hx4, hy4] using this

theorem card_pair_of_card_triple {x y z : G} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hyz : y * z = z * y) (hxy : x * y = y * x) (hxz : x * z = z * x)
    (h27 : Nat.card (Subgroup.closure ({x, y, z} : Set G)) = 27) :
    Nat.card (Subgroup.closure ({y, z} : Set G)) = 9 := by
  set E := Subgroup.closure ({y, z} : Set G) with hE
  have hle : Subgroup.closure ({x, y, z} : Set G) ≤ Subgroup.zpowers x ⊔ E := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro w (rfl | rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hxE : E ≤ Cen x := (Subgroup.closure_le _).mpr (by
    rintro w (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm)
  have hN : Subgroup.zpowers x ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    rw [show x * w = w * x from (Subgroup.mem_centralizer_singleton_iff.mp (hxE hw)).symm,
      mul_inv_cancel_right]
    exact hw
  have e := card_sup_mul_card_inf _ _ hN
  have h1 := Subgroup.card_le_of_le hle
  rw [h27] at h1
  have h2 : 0 < Nat.card ↥(Subgroup.zpowers x ⊓ E) := Nat.card_pos
  have h3 : Nat.card (Subgroup.zpowers x) ≤ 3 := by
    rw [Nat.card_zpowers]; exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx)
  have h4 : Nat.card E ≤ 9 := card_closure_pair_le hy hz hyz
  refine le_antisymm h4 ?_
  nlinarith

theorem FF81Basis.mem_of_pow_two (hB : FF81Basis b L B b₁ b₂ b₃) {g : G} (hg : g ∈ Cen b)
    {k : ℕ} (hk : g ^ (2 ^ k) = 1) : g ∈ L := by
  obtain ⟨l, hlL, hl⟩ := kf_sp62Out G L hB.hyp.model g (hB.hyp.hLN hg)
  set d := l⁻¹ * g with hd
  have hdL : d ∈ CenS L := Subgroup.mem_centralizer_iff.mpr fun y hy => by
    have := hl y hy
    calc y * d = l⁻¹ * (l * y * l⁻¹) * g := by rw [hd]; group
      _ = l⁻¹ * (g * y * g⁻¹) * g := by rw [this]
      _ = d * y := by rw [hd]; group
  have hdb : d ∈ Cen b := (Cen b).mul_mem ((Cen b).inv_mem (hB.hyp.hLC hlL)) hg
  have hdl : Commute l d := Subgroup.mem_centralizer_iff.mp hdL l hlL
  have hgl : g = l * d := by rw [hd]; group
  have hpow : l ^ (2 ^ k) * d ^ (2 ^ k) = 1 := by rw [← hdl.mul_pow, ← hgl, hk]
  have hlN : l ^ (2 ^ k) ∈ L ⊓ CenS L := by
    refine ⟨L.pow_mem hlL _, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hpow]
    exact (CenS L).inv_mem ((CenS L).pow_mem hdL _)
  rw [hB.inf_cenS_self, Subgroup.mem_bot] at hlN
  rw [hlN, one_mul] at hpow
  have hdco : Nat.Coprime 3 (orderOf d) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hpow)
      (Nat.Coprime.pow_right _ (by norm_num))
  have hdO := hB.mem_opp_of_mem_cen_inf ⟨hdb, hdL⟩ hdco
  have hd1 : d = 1 := eq_one_of_pow_two_of_odd hpow (Subgroup.orderOf_dvd_natCard _ hdO) hB.o3odd
  rw [hgl, hd1, mul_one]
  exact hlL

theorem FF81Basis.le_of_isPGroup (hB : FF81Basis b L B b₁ b₂ b₃) {R : Subgroup G}
    (hRb : R ≤ Cen b) (hR : IsPGroup 2 R) : R ≤ L := fun g hg => by
  obtain ⟨k, hk⟩ := hR ⟨g, hg⟩
  exact hB.mem_of_pow_two (hRb hg) (k := k) (by simpa using congrArg Subtype.val hk)

theorem FF81Basis.monoL_stab (hB : FF81Basis b L B b₁ b₂ b₃) :
    ∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set G),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G) := by
  intro n hnL hnN x hx
  have hnb : n * b * n⁻¹ = b := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hnL)]; group
  have hnB : n ∈ Nor B := by
    rw [hB.mono.2.1]
    refine Subgroup.mem_normalizer_fintype fun y hy => conj_mem_of_closure (fun w hw => ?_) hy
    rcases hw with rfl | hw
    · rw [hnb]; exact Subgroup.subset_closure (Set.mem_insert _ _)
    · have : n * w * n⁻¹ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hnN w).mp (Subgroup.subset_closure hw)
      exact Subgroup.closure_mono (Set.subset_insert _ _) this
  have hz : conjBy n (Subgroup.zpowers b) = Subgroup.zpowers b := by
    rw [conjBy_zpowers, hnb]
  exact (hB.stab n hnB hz).2 x hx

theorem FF81Sec4.exists_swap {t₀ : G} (h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀) :
    ∃ σ : G, σ * σ = 1 ∧ σ * b * σ⁻¹ = b₂ ∧ σ * b₂ * σ⁻¹ = b ∧ σ * b₁ * σ⁻¹ = b₁ ∧
      σ * b₃ * σ⁻¹ = b₃ := by
  have hB := h4.basis
  obtain ⟨-, hBeq, -, ⟨τ, -, hτ0, hτ1, hτ2, hτ3⟩, ⟨c, -, hc0, hc1, hc2, hc3⟩⟩ := h4.caseI.1.1
  have inv : ∀ {a x y : G}, a * x * a⁻¹ = y → a⁻¹ * y * a = x := fun h => by rw [← h]; group
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : G, σ₀ = τ * (c * τ * c⁻¹) * τ⁻¹ := ⟨_, rfl⟩
  have key : ∀ x : G, σ₀ * x * σ₀⁻¹ =
      τ * (c * (τ * (c⁻¹ * (τ⁻¹ * x * τ) * c) * τ⁻¹) * c⁻¹) * τ⁻¹ := by
    intro x; rw [hσ₀]; group
  have e0 : σ₀ * b * σ₀⁻¹ = b₂ := by rw [key, inv hτ1, inv hc0, hτ0, hc1, hτ2]
  have e2 : σ₀ * b₂ * σ₀⁻¹ = b := by rw [key, inv hτ2, inv hc1, hτ1, hc0, hτ1]
  have e1 : σ₀ * b₁ * σ₀⁻¹ = b₁ := by rw [key, inv hτ0, inv hc3, hτ3, hc3, hτ0]
  have e3 : σ₀ * b₃ * σ₀⁻¹ = b₃ := by rw [key, inv hτ3, inv hc2, hτ2, hc2, hτ3]
  obtain ⟨z, hz⟩ : ∃ z : G, z = σ₀ * σ₀ := ⟨_, rfl⟩
  have hfix : ∀ x ∈ ({b, b₁, b₂, b₃} : Set G), z * x * z⁻¹ = x := by
    intro x hx
    have hzx : z * x * z⁻¹ = σ₀ * (σ₀ * x * σ₀⁻¹) * σ₀⁻¹ := by rw [hz]; group
    rcases hx with rfl | rfl | rfl | rfl
    · rw [hzx, e0, e2]
    · rw [hzx, e1, e1]
    · rw [hzx, e2, e0]
    · rw [hzx, e3, e3]
  have hzx : ∀ x ∈ ({b, b₁, b₂, b₃} : Set G), z * x = x * z := fun x hx => by
    calc z * x = (z * x * z⁻¹) * z := by group
      _ = x * z := by rw [hfix x hx]
  have hBz : B ≤ Cen z := by
    rw [hBeq]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hzx x hx).symm
  have hzC : z ∈ CenS B := Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hBz hy)
  have hodd : Odd (orderOf z) := Odd.of_dvd_nat hB.cenOdd (Subgroup.orderOf_dvd_natCard _ hzC)
  obtain ⟨j, hj⟩ := hodd
  have hcz : σ₀ * z = z * σ₀ := by rw [hz]; group
  have hczj : σ₀ * z ^ j = z ^ j * σ₀ := (Commute.pow_right hcz j).eq
  have hσσ : σ₀ * z ^ j * (σ₀ * z ^ j) = 1 := by
    calc σ₀ * z ^ j * (σ₀ * z ^ j) = σ₀ * (z ^ j * σ₀) * z ^ j := by simp only [mul_assoc]
      _ = σ₀ * (σ₀ * z ^ j) * z ^ j := by rw [hczj]
      _ = z * z ^ j * z ^ j := by rw [← mul_assoc σ₀ σ₀, ← hz]
      _ = z ^ (j + j + 1) := by rw [mul_assoc, ← pow_add, ← pow_succ']
      _ = 1 := by rw [show j + j + 1 = orderOf z by omega, pow_orderOf_eq_one]
  have hconj : ∀ x ∈ ({b, b₁, b₂, b₃} : Set G),
      (σ₀ * z ^ j) * x * (σ₀ * z ^ j)⁻¹ = σ₀ * x * σ₀⁻¹ := by
    intro x hx
    have hzjx : z ^ j * x = x * z ^ j := (Commute.pow_left (hzx x hx) j).eq
    calc (σ₀ * z ^ j) * x * (σ₀ * z ^ j)⁻¹ = σ₀ * (z ^ j * x) * (z ^ j)⁻¹ * σ₀⁻¹ := by group
      _ = σ₀ * x * σ₀⁻¹ := by rw [hzjx]; group
  refine ⟨σ₀ * z ^ j, hσσ, ?_, ?_, ?_, ?_⟩
  · rw [hconj b (by simp), e0]
  · rw [hconj b₂ (by simp), e2]
  · rw [hconj b₁ (by simp), e1]
  · rw [hconj b₃ (by simp), e3]

theorem op_two_isPGroup (t₀ : G) : IsPGroup 2 (Op 2 (Cen t₀)) :=
  CFSG.pCore_isPGroup.map (Cen t₀).subtype

theorem op_two_le (t₀ : G) : Op 2 (Cen t₀) ≤ Cen t₀ := Subgroup.map_subtype_le _

theorem op_two_conj {t₀ g u : G} (hg : g ∈ Cen t₀) (hu : u ∈ Op 2 (Cen t₀)) :
    g * u * g⁻¹ ∈ Op 2 (Cen t₀) :=
  inSubgroup_conj_mem (CFSG.pCore_normal (p := 2) (G := ↥(Cen t₀))) hg hu

theorem isPGroup_zpowers_of_two {t₀ : G} (ht : orderOf t₀ = 2) :
    IsPGroup 2 (Subgroup.zpowers t₀) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])

theorem mem_op_two_self {t₀ : G} (ht : orderOf t₀ = 2) : t₀ ∈ Op 2 (Cen t₀) := by
  set c : Cen t₀ := ⟨t₀, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hn : (Subgroup.zpowers c).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hgc : g * c = c * g := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
    rw [(Commute.zpow_right hgc k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers c k⟩
  have hp : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht, pow_one])
  have hle : Subgroup.zpowers c ≤ CFSG.pCore 2 ↥(Cen t₀) := le_sSup ⟨hn, hp⟩
  exact ⟨c, hle (Subgroup.mem_zpowers c), rfl⟩

theorem FF81Basis.mem_op_two_of_comm (hB : FF81Basis b L B b₁ b₂ b₃) {t₀ : G}
    (ht : orderOf t₀ = 2) {g : G} (hg : g ∈ Cen t₀) (hc : ∀ u ∈ Op 2 (Cen t₀), g * u = u * g) :
    g ∈ Op 2 (Cen t₀) := by
  have hne : Subgroup.zpowers t₀ ≠ ⊥ := fun h => by
    have : t₀ ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers t₀
    rw [Subgroup.mem_bot] at this
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  exact hB.hyp.char2 _ ⟨Subgroup.zpowers t₀, hne, isPGroup_zpowers_of_two ht,
    cen_eq_nor_zpowers_of_two ht⟩ ⟨hg, Subgroup.mem_centralizer_iff.mpr fun u hu => (hc u hu).symm⟩

theorem FF81Basis.b_facts (hB : FF81Basis b L B b₁ b₂ b₃) :
    b₁ ^ 3 = 1 ∧ b₂ ^ 3 = 1 ∧ b₃ ^ 3 = 1 ∧ b₁ * b₂ = b₂ * b₁ ∧ b₁ * b₃ = b₃ * b₁ ∧
      b₂ * b₃ = b₃ * b₂ := by
  haveI := hB.elem.1
  have hm : ∀ x ∈ ({b₁, b₂, b₃} : Set G), x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) :=
    fun x hx => Subgroup.subset_closure hx
  have hc := comm_of_isElemAb hB.elem
  exact ⟨CFSG.elemPow_eq_one_of_isElementaryAbelian _ (hm _ (by simp)),
    CFSG.elemPow_eq_one_of_isElementaryAbelian _ (hm _ (by simp)),
    CFSG.elemPow_eq_one_of_isElementaryAbelian _ (hm _ (by simp)),
    hc _ (hm _ (by simp)) _ (hm _ (by simp)), hc _ (hm _ (by simp)) _ (hm _ (by simp)),
    hc _ (hm _ (by simp)) _ (hm _ (by simp))⟩

theorem FF81Basis.comm_E (hB : FF81Basis b L B b₁ b₂ b₃) :
    ∀ a ∈ Subgroup.closure ({b₂, b₃} : Set G), ∀ c ∈ Subgroup.closure ({b₂, b₃} : Set G),
      a * c = c * a := fun a ha c hc =>
  comm_of_isElemAb hB.elem a (Subgroup.closure_mono (Set.subset_insert _ _) ha) c
    (Subgroup.closure_mono (Set.subset_insert _ _) hc)

theorem FF81Basis.card_E (hB : FF81Basis b L B b₁ b₂ b₃) :
    Nat.card (Subgroup.closure ({b₂, b₃} : Set G)) = 9 := by
  obtain ⟨h1, h2, h3, h12, h13, h23⟩ := hB.b_facts
  exact card_pair_of_card_triple h1 h2 h3 h23 h12 h13 (by rw [hB.elem.2]; norm_num)

theorem FF81Sec4.L_le_cen {t₀ : G} (h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀) : L ≤ Cen t₀ := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h4.ht₀L x hx)

theorem FF81Sec4.step1 {t₀ : G} (h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀) (h42 : FF81Conc4_2 b₂ b₃)
    {x : G} (hx : x ∈ ({b₂ * b₃, b₂ * b₃⁻¹} : Set G)) {v : G} (hvT : v ∈ Op 2 (Cen t₀))
    (hvx : v ∈ Cen x) : v ∈ Cen b₂ ∧ v ∈ Cen b₃ := by
  have hB := h4.basis
  set E := Subgroup.closure ({b₂, b₃} : Set G) with hE
  have hEc := hB.comm_E
  have hb2E : b₂ ∈ E := Subgroup.subset_closure (by simp)
  have hb3E : b₃ ∈ E := Subgroup.subset_closure (by simp)
  have hxE : x ∈ E := by
    rcases hx with rfl | rfl
    · exact E.mul_mem hb2E hb3E
    · exact E.mul_mem hb2E (E.inv_mem hb3E)
  have hEx : E ≤ Cen x := fun e he => Subgroup.mem_centralizer_singleton_iff.mpr (hEc e he x hxE)
  set O := Opp 3 (Cen x) with hO
  have hON := CFSG.pPrimeCore_normal (p := 3) (G := ↥(Cen x))
  have hEN : E ≤ Subgroup.normalizer (O : Set G) := fun e he =>
    Subgroup.mem_normalizer_fintype fun o ho => inSubgroup_conj_mem hON (hEx he) ho
  have e := card_sup_mul_card_inf E O hEN
  rw [hB.card_E] at e
  have hodd : Odd (Nat.card ↥(E ⊔ O)) :=
    Odd.of_dvd_nat (Odd.mul (by decide) (h42 x hx).1) (Dvd.intro _ e)
  have hv : v ∈ setMul O (Cen x ⊓ Nor E) := by rw [(h42 x hx).2]; exact hvx
  obtain ⟨o, ho, n, hn, hvon⟩ := hv
  have key : ∀ e ∈ E, e ∈ L → v * e = e * v := by
    intro e heE heL
    set c := v * e * v⁻¹ * e⁻¹ with hc
    have hcT : c ∈ Op 2 (Cen t₀) := by
      rw [hc, show v * e * v⁻¹ * e⁻¹ = v * (e * v⁻¹ * e⁻¹) by group]
      exact Subgroup.mul_mem _ hvT (op_two_conj (h4.L_le_cen heL) (Subgroup.inv_mem _ hvT))
    have hcS : c ∈ E ⊔ O := by
      have hne : n * e * n⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hn.2 e).mp heE
      rw [hc, hvon, show o * n * e * (o * n)⁻¹ * e⁻¹ = o * (n * e * n⁻¹) * o⁻¹ * e⁻¹ by group]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right ho)
        (Subgroup.mem_sup_left hne)) (Subgroup.mem_sup_right (Subgroup.inv_mem _ ho)))
        (Subgroup.mem_sup_left (Subgroup.inv_mem _ heE))
    obtain ⟨k, hk⟩ := op_two_isPGroup t₀ ⟨c, hcT⟩
    have hc1 : c = 1 := eq_one_of_pow_two_of_odd (k := k)
      (by simpa using congrArg Subtype.val hk) (Subgroup.orderOf_dvd_natCard _ hcS) hodd
    calc v * e = c * (e * v) := by rw [hc]; group
      _ = e * v := by rw [hc1, one_mul]
  exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (key b₂ hb2E hB.hb₂),
    Subgroup.mem_centralizer_singleton_iff.mpr (key b₃ hb3E hB.hb₃)⟩

theorem FF81Sec4.le_of_le_le {t₀ : G} (h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀) (h42 : FF81Conc4_2 b₂ b₃)
    {P : Subgroup G} (h2 : Op 2 (Cen t₀) ⊓ Cen b₂ ≤ P) (h3 : Op 2 (Cen t₀) ⊓ Cen b₃ ≤ P) :
    Op 2 (Cen t₀) ≤ P := by
  have hB := h4.basis
  obtain ⟨-, hb2, hb3, -, -, hb23⟩ := hB.b_facts
  have hEc := hB.comm_E
  refine CFSG.HardMathSupport.Solomon.Coordinator.YS08.le_of_inf_centralizer_le_three
    (E := Subgroup.closure ({b₂, b₃} : Set G))
    ⟨⟨⟨fun a c => Subtype.ext (hEc a a.2 c c.2)⟩⟩, fun y hy => ?_⟩ hB.card_E
    (op_two_isPGroup t₀) ?_ ?_
  · haveI := hB.elem.1
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian _
      (Subgroup.closure_mono (Set.subset_insert b₁ ({b₂, b₃} : Set G)) hy)
  · intro e he
    have heL : e ∈ L := (Subgroup.closure_le L).mpr (by
      rintro y (rfl | rfl); exacts [hB.hb₂, hB.hb₃]) he
    exact Subgroup.mem_normalizer_fintype fun _ hu => op_two_conj (h4.L_le_cen heL) hu
  · intro e he he1 v hvT hev
    have hv : v ∈ Cen e := Subgroup.mem_centralizer_singleton_iff.mpr hev.symm
    rcases mem_cen_line hb23 hb2 hb3 he he1 hv with h | h | h | h
    · exact h2 ⟨hvT, h⟩
    · exact h3 ⟨hvT, h⟩
    · exact h2 ⟨hvT, (h4.step1 h42 (by simp) hvT h).1⟩
    · exact h2 ⟨hvT, (h4.step1 h42 (by simp) hvT h).1⟩

theorem conjBy_op_two {t₀ n : G} (hn : n ∈ Cen t₀) : conjBy n (Op 2 (Cen t₀)) = Op 2 (Cen t₀) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.mem_normalizer_fintype fun _ hu => op_two_conj hn hu)

theorem conjBy_op_two_inf_cen {t₀ n : G} (hn : n ∈ Cen t₀) (x : G) :
    conjBy n (Op 2 (Cen t₀) ⊓ Cen x) = Op 2 (Cen t₀) ⊓ Cen (n * x * n⁻¹) := by
  rw [conjBy_inf_cen, conjBy_op_two hn]

theorem FF81Sec4.swap_data {t₀ : G} (h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀) :
    ∃ σ : G, σ * σ = 1 ∧ σ * b * σ⁻¹ = b₂ ∧ σ * b₂ * σ⁻¹ = b ∧ σ * b₁ * σ⁻¹ = b₁ ∧
      σ * b₃ * σ⁻¹ = b₃ ∧ σ * t₀ * σ⁻¹ ∈ L ∧ σ * t₀ * σ⁻¹ ∈ Cen b ∧
      orderOf (σ * t₀ * σ⁻¹) = 2 ∧ σ * t₀ * σ⁻¹ * b₁ = b₁ * (σ * t₀ * σ⁻¹) ∧
      σ * t₀ * σ⁻¹ * b₃ = b₃ * (σ * t₀ * σ⁻¹) ∧
      σ * t₀ * σ⁻¹ * b₂ * (σ * t₀ * σ⁻¹)⁻¹ = b₂⁻¹ := by
  obtain ⟨σ, hσ2, hσb, hσb₂, hσb₁, hσb₃⟩ := h4.exists_swap
  have hB := h4.basis
  have hcomm : ∀ y ∈ L, t₀ * y = y * t₀ := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp h4.ht₀L y hy).symm
  have hsb : σ * t₀ * σ⁻¹ ∈ Cen b := by
    have := conj_commute (a := σ) (hcomm b₂ hB.hb₂)
    rw [hσb₂] at this
    exact Subgroup.mem_centralizer_singleton_iff.mpr this
  have ht2 : t₀ * t₀ = 1 := by
    have := pow_orderOf_eq_one t₀
    rwa [h4.ht₀, sq] at this
  have hs1 : σ * t₀ * σ⁻¹ * b₁ = b₁ * (σ * t₀ * σ⁻¹) := by
    have := conj_commute (a := σ) (hcomm b₁ hB.hb₁)
    rwa [hσb₁] at this
  have hs3 : σ * t₀ * σ⁻¹ * b₃ = b₃ * (σ * t₀ * σ⁻¹) := by
    have := conj_commute (a := σ) (hcomm b₃ hB.hb₃)
    rwa [hσb₃] at this
  have e1 : σ⁻¹ * b₂ * σ = b := by rw [← hσb]; group
  refine ⟨σ, hσ2, hσb, hσb₂, hσb₁, hσb₃, hB.mem_of_pow_two hsb (k := 1) ?_, hsb, ?_, hs1, hs3, ?_⟩
  · calc (σ * t₀ * σ⁻¹) ^ (2 ^ 1) = σ * (t₀ * t₀) * σ⁻¹ := by rw [pow_one, sq]; group
      _ = 1 := by rw [ht2]; group
  · show orderOf (MulAut.conj σ t₀) = 2
    rw [MulEquiv.orderOf_eq]; exact h4.ht₀
  · calc σ * t₀ * σ⁻¹ * b₂ * (σ * t₀ * σ⁻¹)⁻¹ = σ * (t₀ * (σ⁻¹ * b₂ * σ) * t₀⁻¹) * σ⁻¹ := by
          group
      _ = (σ * b * σ⁻¹)⁻¹ := by rw [e1, h4.ht₀b]; group
      _ = b₂⁻¹ := by rw [hσb]

theorem FF81Sec4.ff81_4_3_T (hKF : KF_Sp6Transv) {t₀ : G} (h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀)
    (h42 : FF81Conc4_2 b₂ b₃) :
    IsElemAb 2 7 (Op 2 (Cen t₀)) ∧ t₀ ∈ ⁅Cen t₀, Cen t₀⁆ ∧
      Nat.card ↥(Op 2 (Cen t₀) ⊓ Cen b₂) = 32 ∧
      Nat.card ↥(Op 2 (Cen t₀) ⊓ Cen b₂ ⊓ Cen b₃) = 8 := by
  have hB := h4.basis
  set T := Op 2 (Cen t₀) with hT
  set Q₂ := T ⊓ Cen b₂ with hQ₂
  set Q₃ := T ⊓ Cen b₃ with hQ₃
  have hTp := op_two_isPGroup t₀
  have hLC := h4.L_le_cen
  obtain ⟨σ, -, -, hσb₂, -, hσb₃, hsL, -, hs2, hs1, hs3, hsinv⟩ := h4.swap_data
  set s := σ * t₀ * σ⁻¹ with hs
  obtain ⟨n, hnL, -, hn2, -⟩ := hB.monoL
  have hQ₃eq : conjBy n Q₂ = Q₃ := by
    rw [hQ₂, hT, conjBy_op_two_inf_cen (hLC hnL), hn2]
  set R := conjBy σ Q₂ with hR
  have hRs : R ≤ Cen s := by
    rw [hs, cen_conj]; exact Subgroup.map_mono (inf_le_left.trans (op_two_le t₀))
  have hRb : R ≤ Cen b := by
    rw [hR, hQ₂, conjBy_inf_cen, hσb₂]; exact inf_le_right
  have hRp : IsPGroup 2 R := (hTp.to_le inf_le_left).map _
  have hRL : R ≤ L := hB.le_of_isPGroup hRb hRp
  have hnor : ∀ U : Subgroup G, (∀ y ∈ Cen t₀ ⊓ Cen b₂, ∀ u ∈ U, y * u * y⁻¹ ∈ U) →
      L ⊓ Cen s ≤ Nor (conjBy σ U) := by
    intro U hU y hy
    refine mem_nor_conjBy fun u hu => hU _ ⟨?_, ?_⟩ u hu
    · have := hy.2; rw [hs, cen_conj] at this; exact mem_conjBy_iff.mp this
    · have := hB.hyp.hLC hy.1; rw [← hσb₂, cen_conj] at this; exact mem_conjBy_iff.mp this
  have hQ₂N : ∀ y ∈ Cen t₀ ⊓ Cen b₂, ∀ u ∈ Q₂, y * u * y⁻¹ ∈ Q₂ := fun y hy u hu =>
    ⟨op_two_conj hy.1 hu.1, (Cen b₂).mul_mem ((Cen b₂).mul_mem hy.2 hu.2) ((Cen b₂).inv_mem hy.2)⟩
  obtain ⟨-, -, hKs⟩ := hKF G L hB.hyp.model b₁ b₂ b₃ hB.hb₁ hB.hb₂ hB.hb₃ hB.elem hB.selfcen
    hB.monoL_stab
  obtain ⟨-, hKR⟩ := hKs s hsL hs2 hs1 hs3 hsinv
  rcases hKR R (le_inf hRL hRs) hRp (hnor Q₂ hQ₂N) with hA |
    ⟨hR32, hRab, hRex, -, hRb₃, -, -, -, hscomm⟩
  ·
    exfalso
    have hQ₂t : Q₂ ≤ Subgroup.zpowers t₀ := by
      have : R ≤ conjBy σ (Subgroup.zpowers t₀) := by rw [conjBy_zpowers]; exact hA
      exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj σ).injective).mp this
    have hQ₃t : Q₃ ≤ Subgroup.zpowers t₀ :=
      calc Q₃ = conjBy n Q₂ := hQ₃eq.symm
        _ ≤ conjBy n (Subgroup.zpowers t₀) := Subgroup.map_mono hQ₂t
        _ = Subgroup.zpowers t₀ := by
          rw [conjBy_zpowers, Subgroup.mem_centralizer_singleton_iff.mp (hLC hnL)]; group
    have hTt : T ≤ Subgroup.zpowers t₀ := h4.le_of_le_le h42 hQ₂t hQ₃t
    have hLT : L ≤ T := fun l hl => hB.mem_op_two_of_comm h4.ht₀ (hLC hl) fun u hu => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hTt hu)
      exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)) k).eq
    have := Subgroup.card_le_of_le (hLT.trans hTt)
    rw [hB.card_L, Nat.card_zpowers, h4.ht₀] at this
    norm_num at this
  have hconjmem : ∀ u ∈ Q₂, σ * u * σ⁻¹ ∈ R := fun u hu => Subgroup.mem_map_of_mem _ hu
  have hQ₂ab : ∀ x ∈ Q₂, ∀ y ∈ Q₂, x * y = y * x := by
    intro x hx y hy
    have := hRab _ (hconjmem x hx) _ (hconjmem y hy)
    calc x * y = σ⁻¹ * (σ * x * σ⁻¹ * (σ * y * σ⁻¹)) * σ := by group
      _ = σ⁻¹ * (σ * y * σ⁻¹ * (σ * x * σ⁻¹)) * σ := by rw [this]
      _ = y * x := by group
  have hQ₂ex : ∀ x ∈ Q₂, x * x = 1 := by
    intro x hx
    have := hRex _ (hconjmem x hx)
    calc x * x = σ⁻¹ * (σ * x * σ⁻¹ * (σ * x * σ⁻¹)) * σ := by group
      _ = 1 := by rw [this]; group
  have hQ₂32 : Nat.card Q₂ = 32 := by rw [← card_conjBy σ Q₂]; exact hR32
  have hW8 : Nat.card ↥(Q₂ ⊓ Cen b₃) = 8 := by
    rw [← card_conjBy σ, conjBy_inf_cen, hσb₃]; exact hRb₃
  have hQ₃ab : ∀ x ∈ Q₃, ∀ y ∈ Q₃, x * y = y * x := by
    intro x hx y hy
    rw [← hQ₃eq] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_commute (hQ₂ab x' hx' y' hy')
  have hQ₃ex : ∀ x ∈ Q₃, x * x = 1 := by
    intro x hx
    rw [← hQ₃eq] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc n * x' * n⁻¹ * (n * x' * n⁻¹) = n * (x' * x') * n⁻¹ := by group
      _ = 1 := by rw [hQ₂ex x' hx']; group
  have hWZ : ∀ w ∈ Q₂ ⊓ Cen b₃, ∀ u ∈ T, w * u = u * w := by
    intro w hw u hu
    have hwQ₃ : w ∈ Q₃ := ⟨hw.1.1, hw.2⟩
    have hle : T ≤ Cen w := h4.le_of_le_le h42
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr (hQ₂ab v hv w hw.1))
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr (hQ₃ab v hv w hwQ₃))
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hu)).symm
  have hZN : ∀ y ∈ Cen t₀ ⊓ Cen b₂, ∀ u ∈ Q₂ ⊓ CenS T, y * u * y⁻¹ ∈ Q₂ ⊓ CenS T := by
    intro y hy u hu
    refine ⟨hQ₂N y hy u hu.1, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hz' : y⁻¹ * z * y ∈ T := by
      have := op_two_conj ((Cen t₀).inv_mem hy.1) hz; rwa [inv_inv] at this
    have hc := Subgroup.mem_centralizer_iff.mp hu.2 _ hz'
    calc z * (y * u * y⁻¹) = y * ((y⁻¹ * z * y) * u) * y⁻¹ := by group
      _ = y * (u * (y⁻¹ * z * y)) * y⁻¹ := by rw [hc]
      _ = y * u * y⁻¹ * z := by group
  have hZ := hKR (conjBy σ (Q₂ ⊓ CenS T)) ((Subgroup.map_mono inf_le_left).trans (le_inf hRL hRs))
    (hRp.to_le (Subgroup.map_mono inf_le_left)) (hnor _ hZN)
  have hWle : Q₂ ⊓ Cen b₃ ≤ Q₂ ⊓ CenS T := fun w hw =>
    ⟨hw.1, Subgroup.mem_centralizer_iff.mpr fun u hu => (hWZ w hw u hu).symm⟩
  have h8 : 8 ≤ Nat.card ↥(Q₂ ⊓ CenS T) := hW8 ▸ Subgroup.card_le_of_le hWle
  have hZ32 : Nat.card ↥(Q₂ ⊓ CenS T) = 32 := by
    rcases hZ with h | ⟨h, -⟩
    · exfalso
      have := Subgroup.card_le_of_le h
      rw [card_conjBy, Nat.card_zpowers, hs2] at this
      omega
    · rwa [card_conjBy] at h
  have hQ₂Z : Q₂ ≤ CenS T := by
    have := Subgroup.eq_of_le_of_card_ge (inf_le_left : Q₂ ⊓ CenS T ≤ Q₂)
      (by rw [hZ32, hQ₂32])
    rw [← this]; exact inf_le_right
  have hQ₃Z : Q₃ ≤ CenS T := by
    rw [← hQ₃eq]
    rintro _ ⟨u, hu, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hz' : n⁻¹ * z * n ∈ T := by
      have := op_two_conj (hLC (L.inv_mem hnL)) hz; rwa [inv_inv] at this
    have hc := Subgroup.mem_centralizer_iff.mp (hQ₂Z hu) _ hz'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc z * (n * u * n⁻¹) = n * ((n⁻¹ * z * n) * u) * n⁻¹ := by group
      _ = n * (u * (n⁻¹ * z * n)) * n⁻¹ := by rw [hc]
      _ = n * u * n⁻¹ * z := by group
  have hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    have hle := h4.le_of_le_le h42 hQ₂Z hQ₃Z
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm
  let P : Subgroup G :=
    { carrier := {u | u ∈ T ∧ u * u = 1}
      mul_mem' := fun {a c} ha hc => ⟨T.mul_mem ha.1 hc.1, by
        calc a * c * (a * c) = a * (c * a) * c := by group
          _ = a * (a * c) * c := by rw [hTab c hc.1 a ha.1]
          _ = a * a * (c * c) := by group
          _ = 1 := by rw [ha.2, hc.2, one_mul]⟩
      one_mem' := ⟨T.one_mem, mul_one 1⟩
      inv_mem' := fun {a} ha => ⟨T.inv_mem ha.1, by rw [← mul_inv_rev, ha.2, inv_one]⟩ }
  have hTP : T ≤ P := h4.le_of_le_le h42 (fun u hu => ⟨hu.1, hQ₂ex u hu⟩)
    (fun u hu => ⟨hu.1, hQ₃ex u hu⟩)
  have hTeq : T = Q₂ ⊔ Q₃ :=
    le_antisymm (h4.le_of_le_le h42 le_sup_left le_sup_right) (sup_le inf_le_left inf_le_left)
  have hQ₃32 : Nat.card Q₃ = 32 := by rw [← hQ₃eq, card_conjBy]; exact hQ₂32
  have hN : Q₂ ≤ Subgroup.normalizer (Q₃ : Set G) := fun x hx =>
    Subgroup.mem_normalizer_fintype fun y hy => by
      rw [hTab x hx.1 y hy.1, mul_inv_cancel_right]; exact hy
  have e := card_sup_mul_card_inf Q₂ Q₃ hN
  have hinf : Q₂ ⊓ Q₃ = Q₂ ⊓ Cen b₃ :=
    le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      (le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
  rw [← hTeq, hinf, hW8, hQ₂32, hQ₃32] at e
  have hT128 : Nat.card T = 2 ^ 7 := by omega
  have ht₀ : t₀ ∈ ⁅Cen t₀, Cen t₀⁆ := by
    have h1 : s ∈ ⁅Cen s, Cen s⁆ := Subgroup.commutator_mono hRs inf_le_right hscomm
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj σ⁻¹).toMonoidHom h1
    have hc : conjBy σ⁻¹ (Cen s) = Cen t₀ := by
      rw [← cen_conj, show σ⁻¹ * s * σ⁻¹⁻¹ = t₀ by rw [hs]; group]
    rw [Subgroup.map_commutator] at h2
    change _ ∈ ⁅conjBy σ⁻¹ (Cen s), conjBy σ⁻¹ (Cen s)⁆ at h2
    rw [hc] at h2
    have e2 : (MulAut.conj σ⁻¹).toMonoidHom s = t₀ := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hs]; group
    rwa [e2] at h2
  exact ⟨⟨CFSG.IsElementaryAbelian.of_forall hTab fun x hx => by rw [sq]; exact (hTP hx).2,
    hT128⟩, ht₀, hQ₂32, hW8⟩

theorem FF81Sec4.not_dvd_card_cen (hKF : KF_Sp6Transv) {t₀ : G}
    (h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀) : ¬ 2 ^ 10 ∣ Nat.card ↥(Cen t₀ ⊓ Cen b₂) := by
  intro hdvd
  have hB := h4.basis
  obtain ⟨σ, -, -, hσb₂, -, -, hsL, -, hs2, hs1, hs3, hsinv⟩ := h4.swap_data
  obtain ⟨-, -, hKs⟩ := hKF G L hB.hyp.model b₁ b₂ b₃ hB.hb₁ hB.hb₂ hB.hb₃ hB.elem hB.selfcen
    hB.monoL_stab
  obtain ⟨h23040, -⟩ := hKs _ hsL hs2 hs1 hs3 hsinv
  have hcard : Nat.card ↥(Cen (σ * t₀ * σ⁻¹) ⊓ Cen b) = Nat.card ↥(Cen t₀ ⊓ Cen b₂) := by
    rw [← card_conjBy σ (Cen t₀ ⊓ Cen b₂), conjBy_inf_cen, hσb₂, ← cen_conj]
  rw [← hcard] at hdvd
  set D := Cen (σ * t₀ * σ⁻¹) ⊓ Cen b
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  have hK'card : Nat.card ↥(K.map D.subtype) = 2 ^ 10 := by
    rw [Subgroup.card_map_of_injective D.subtype_injective]; exact hK
  have hK'D : K.map D.subtype ≤ D := Subgroup.map_subtype_le _
  have hK'L : K.map D.subtype ≤ L :=
    hB.le_of_isPGroup (hK'D.trans inf_le_right) (IsPGroup.of_card hK'card)
  have := Subgroup.card_dvd_of_le (le_inf hK'L (hK'D.trans inf_le_left))
  rw [hK'card, h23040] at this
  norm_num at this

theorem ff81_4_3 :
    KF_Sp6Transv → KF_Sp6Overgroup → ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G)
      (b₁ b₂ b₃ t₀ : G), FF81Sec4 b L B b₁ b₂ b₃ t₀ → FF81Conc4_2 b₂ b₃ → FF81Conc4_3 L t₀ := by
  intro hKF hOv G _ _ b L B b₁ b₂ b₃ t₀ h4 h42
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB := h4.basis
  obtain ⟨hT7, ht₀C, -, -⟩ := h4.ff81_4_3_T hKF h42
  obtain ⟨h2160, -, -⟩ := hKF G L hB.hyp.model b₁ b₂ b₃ hB.hb₁ hB.hb₂ hB.hb₃ hB.elem hB.selfcen
    hB.monoL_stab
  have ht1 : t₀ ≠ 1 := fun h => by
    have := h4.ht₀; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  have hb21 : b₂ ≠ 1 := fun h => by
    have e := h2160
    have hL : L ⊓ Cen b₂ = L :=
      inf_eq_left.mpr fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (by rw [h]; group)
    rw [hL, hB.card_L] at e
    exact absurd e (by norm_num)
  have hb2 : orderOf b₂ = 3 := orderOf_eq_prime hB.b_facts.2.1 hb21
  refine ⟨hOv G (Cen t₀) (Op 2 (Cen t₀)) L t₀ b₂ (op_two_le t₀) (fun g hg u hu => op_two_conj hg hu)
    hT7 (fun g hg => hB.mem_op_two_of_comm h4.ht₀ hg.1 fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hg.2 u hu).symm) h4.L_le_cen hB.hyp.model
    (mem_op_two_self h4.ht₀) ht1 le_rfl hB.hb₂ hb2 h2160 (h4.not_dvd_card_cen hKF), hT7, ht₀C⟩

end CFSG.RankThree.PartTwo.Sec21.FF81
