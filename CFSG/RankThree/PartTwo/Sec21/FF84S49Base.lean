module

public import CFSG.RankThree.PartTwo.Sec21.FF84S47
public import CFSG.RankThree.PartTwo.Sec21.FF84S3M0
public import CFSG.RankThree.PartTwo.Sec21.FF84S48Orb
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreSec45

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s card_inf_of_cycleType3 cycleType_c M0_card_cen)

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem piStar_of_le {X A A' U : Subgroup G} {q : ℕ} (hA' : A' ≤ A) (hAU : A ≤ Nor U)
    (h : U ∈ PiStar X A' q) : U ∈ PiStar X A q :=
  ⟨h.1, h.2.1, hAU, fun V hUV hVX hVq hAV => h.2.2.2 V hUV hVX hVq (hA'.trans hAV)⟩

theorem conj_piStar {X A U : Subgroup G} {q : ℕ} (g : G) (hU : U ∈ PiStar X A q) :
    conjBy g U ∈ PiStar (conjBy g X) (conjBy g A) q := by
  obtain ⟨hUX, hUq, hAU, hmax⟩ := hU
  refine ⟨?_, hUq.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hUX hx, rfl⟩
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := ha
    have h1 := hAU ha'
    rw [mem_nor_iff_conjBy] at h1 ⊢
    show conjBy (MulAut.conj g a') (conjBy g U) = conjBy g U
    have e : conjBy (MulAut.conj g a') (conjBy g U) = conjBy g (conjBy a' U) := by
      rw [← conjBy_mul, ← conjBy_mul]
      congr 1
      simp [MulAut.conj_apply]
    rw [e, h1]
  · intro V hUV hVX hVq hAV
    have h1 : U ≤ conjBy g⁻¹ V := by
      intro x hx
      rw [mem_conjBy_iff']
      apply hUV
      rw [mem_conjBy_iff]; simpa [mul_assoc] using hx
    have h2 : conjBy g⁻¹ V ≤ X := by
      intro x hx
      rw [mem_conjBy_iff'] at hx
      have := hVX hx
      rw [mem_conjBy_iff] at this
      simpa [mul_assoc] using this
    have h3 : IsPGroup q (conjBy g⁻¹ V) := hVq.map (MulAut.conj g⁻¹).toMonoidHom
    have h4 : A ≤ Nor (conjBy g⁻¹ V) := by
      intro a ha
      have ha' : g * a * g⁻¹ ∈ conjBy g A := ⟨a, ha, by simp [MulAut.conj_apply]⟩
      have := hAV ha'
      rw [mem_nor_iff_conjBy] at this ⊢
      have e : conjBy a (conjBy g⁻¹ V) = conjBy g⁻¹ (conjBy (g * a * g⁻¹) V) := by
        rw [← conjBy_mul, ← conjBy_mul]
        congr 1
        group
      rw [e, this]
    have h5 := hmax _ h1 h2 h3 h4
    rw [← conjBy_conjBy_inv g V, h5]

theorem cen_zpow_of {z : G} (hz : z ^ 3 = 1) {k : ℤ} (hk : ¬ (3 : ℤ) ∣ k) :
    Cen (z ^ k) = Cen z := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact comm_of_comm_zpow hz hk h
  · intro h
    exact (Commute.zpow_right (show Commute x z from h) k).eq

theorem card_le_four_of_dvd_180 {V : Subgroup G} (hV : IsPGroup 2 V) {M : Subgroup G}
    (hVM : V ≤ M) (hM : Nat.card M = 180) : Nat.card V ≤ 4 := by
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  have hd : Nat.card V ∣ Nat.card M := Subgroup.card_dvd_of_le hVM
  rw [hk, hM] at hd
  by_contra hlt
  have hk3 : 3 ≤ k := by
    by_contra h
    have : k ≤ 2 := by omega
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    rw [hk] at hlt
    omega
  have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 hk3
  have := h8.trans hd
  omega

theorem op2_cen_eq (hchar : CFSG.Assembly.IsCharTwoType G) {S E : Subgroup G} {x : G}
    (hS : EA2 S) (hEN : E ≤ Nor S) (hmax : S ∈ PiStar ⊤ E 2) (hx : x ∈ S) (hx1 : x ≠ 1)
    (hEx : E ≤ Cen x) : Op 2 (Cen x) = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSx : S ≤ Cen x := fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hS.1 s hs x hx)
  have hQN : Cen x ≤ Nor (Op 2 (Cen x)) := le_nor_op2 _
  have hSQ : S ≤ Nor (Op 2 (Cen x)) := hSx.trans hQN
  have hsup : IsPGroup 2 (S ⊔ Op 2 (Cen x) : Subgroup G) :=
    hS.isPGroup.to_sup_of_normal_right' (op2_isPGroup _) hSQ
  have hEsup : E ≤ Nor (S ⊔ Op 2 (Cen x)) := fun g hg => nor_sup_pt (hEN hg) (hQN (hEx hg))
  have h1 : S ⊔ Op 2 (Cen x) = S := hmax.2.2.2 _ le_sup_left le_top hsup hEsup
  have hQS : Op 2 (Cen x) ≤ S := sup_eq_left.1 h1
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by simpa [pow_two] using hS.2 x hx) hx1
  have hSQc : S ≤ Cen x ⊓ CenS (Op 2 (Cen x)) :=
    le_inf hSx fun s hs => Subgroup.mem_centralizer_iff.2 fun q hq => hS.1 q (hQS hq) s hs
  exact le_antisymm hQS (hSQc.trans (B_charTwo_cen hchar hx2))

theorem le_cen_of_mem_cenS {E : Subgroup G} {x : G} (hx : x ∈ CenS E) : E ≤ Cen x := fun e he =>
  Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hx e he)

theorem conjBy_top (g : G) : conjBy g (⊤ : Subgroup G) = ⊤ := by
  ext x
  rw [mem_conjBy_iff]
  simp

namespace S48Ctx

variable (c : S48Ctx b L B K b₁ b₂) {U : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2)

include c

theorem E_le_B : Subgroup.closure ({b, b₁} : Set G) ≤ B := closure_pair_le c.sec

theorem E_comm : ∀ x ∈ Subgroup.closure ({b, b₁} : Set G), ∀ y ∈ Subgroup.closure ({b, b₁} : Set G),
    x * y = y * x := fun x hx y hy => c.hBcomm x (E_le_B c hx) y (E_le_B c hy)

theorem E_cube : ∀ x ∈ Subgroup.closure ({b, b₁} : Set G), x ^ 3 = 1 :=
  fun x hx => c.hB3 x (E_le_B c hx)

theorem E_isEA : IsElementaryAbelian 3 (Subgroup.closure ({b, b₁} : Set G)) :=
  isEA_of 3 (E_comm c) (E_cube c)

theorem E_card : 9 ≤ Nat.card (Subgroup.closure ({b, b₁} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Subgroup.closure ({b, b₁} : Set G) with hE
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  have hb₁E : b₁ ∈ E := Subgroup.subset_closure (by simp)
  have hpg : IsPGroup 3 E := by
    intro x
    exact ⟨1, Subtype.ext (by simpa using E_cube c x.1 x.2)⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hz : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, c.ord_b]
  have hzE : Subgroup.zpowers b ≤ E := (Subgroup.zpowers_le).2 hbE
  have hd : 3 ∣ Nat.card E := hz ▸ Subgroup.card_dvd_of_le hzE
  have hlt : Subgroup.zpowers b < E := by
    refine lt_of_le_of_ne hzE fun h => ?_
    exact b₁_notin_zpowers_b c.sec (h ▸ hb₁E)
  have hcard : 3 < Nat.card E := by
    rw [← hz]
    exact Subgroup.card_lt_of_lt hlt
  rw [hn] at hcard ⊢
  rcases n with _ | _ | n
  · simp at hcard
  · simp at hcard
  · calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem E_cen_cases {e : G} (he : e ∈ Subgroup.closure ({b, b₁} : Set G)) (he1 : e ≠ 1) :
    Cen e = Cen b ∨ Cen e = Cen b₁ ∨ Cen e = Cen (b * b₁) ∨ Cen e = Cen (b * b₁⁻¹) := by
  have hb3 : b ^ 3 = 1 := c.hB3 b (mem_b c.sec)
  have hb₁3 : b₁ ^ 3 = 1 := c.hB3 b₁ (mem_b₁ c.sec)
  have hcomm : b * b₁ = b₁ * b := c.hBcomm b (mem_b c.sec) b₁ (mem_b₁ c.sec)
  have hcbb : Commute b b₁ := hcomm
  obtain ⟨i, j, rfl⟩ := mem_closure_pair_comm hcomm he
  have h3b : (b * b₁) ^ 3 = 1 := c.hB3 _ (mul_mem (mem_b c.sec) (mem_b₁ c.sec))
  have h3b' : (b * b₁⁻¹) ^ 3 = 1 :=
    c.hB3 _ (mul_mem (mem_b c.sec) (inv_mem (mem_b₁ c.sec)))
  by_cases hj : (3 : ℤ) ∣ j
  · left
    have hj1 : b₁ ^ j = 1 := by
      obtain ⟨m, rfl⟩ := hj
      rw [zpow_mul]
      have : b₁ ^ (3 : ℤ) = 1 := by exact_mod_cast hb₁3
      rw [this, one_zpow]
    rw [hj1, mul_one] at he1 ⊢
    have hi : ¬ (3 : ℤ) ∣ i := by
      rintro ⟨m, rfl⟩
      apply he1
      rw [zpow_mul]
      have : b ^ (3 : ℤ) = 1 := by exact_mod_cast hb3
      rw [this, one_zpow]
    exact cen_zpow_of hb3 hi
  by_cases hi : (3 : ℤ) ∣ i
  · right; left
    have hi1 : b ^ i = 1 := by
      obtain ⟨m, rfl⟩ := hi
      rw [zpow_mul]
      have : b ^ (3 : ℤ) = 1 := by exact_mod_cast hb3
      rw [this, one_zpow]
    rw [hi1, one_mul]
    exact cen_zpow_of hb₁3 hj
  by_cases hij : j % 3 = i % 3
  · right; right; left
    have : b ^ i * b₁ ^ j = (b * b₁) ^ i := by
      rw [hcbb.mul_zpow, zpow_eq_of_mod hb₁3 hij]
    rw [this]
    exact cen_zpow_of h3b hi
  · right; right; right
    have hmod : j % 3 = (-i) % 3 := by omega
    have : b ^ i * b₁ ^ j = (b * b₁⁻¹) ^ i := by
      rw [(show Commute b b₁⁻¹ from hcbb.inv_right).mul_zpow, zpow_eq_of_mod hb₁3 hmod,
        inv_zpow']
    rw [this]
    exact cen_zpow_of h3b' hi

include hU

theorem S_core {cc : G} (hcc : cc = b₁ ∨ cc = b₂) :
    ∃ n, CoreData b cc n B (Op 2 (Nor U)) U :=
  c.core_ex hU (op2_isPGroup _) (B_le_nor_S c hU) (S48_CSb c hU) hcc

theorem U_piStar_E : U ∈ PiStar (Cen b) (Subgroup.closure ({b, b₁} : Set G)) 2 := by
  obtain ⟨U₁, U₂, -, -, -, h⟩ := c.f47
  obtain ⟨-, -, -, -, -, h6, -⟩ := h U hU
  exact piStar_of_le (by
    refine (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp)))
    (hU.2.2.1.trans' (E_le_B c)) h6

theorem W_piStar_E :
    Op 2 (Nor U) ⊓ Cen b₁ ∈ PiStar (Cen b₁) (Subgroup.closure ({b, b₁} : Set G)) 2 := by
  obtain ⟨-, -, -, -, ⟨n, hn, hn1, hn2, hn3⟩, -⟩ := c.sec.mono
  obtain ⟨hV, -⟩ := orbit_key c hU hn
  obtain ⟨U₁, U₂, -, -, -, h⟩ := c.f47
  obtain ⟨-, -, -, -, -, h6, -⟩ := h _ hV
  have h7 := conj_piStar n⁻¹ h6
  have a1 : n⁻¹ * b * n = b₁ := conj_inv_of hn2
  have a2 : n⁻¹ * b₁ * n = b := conj_inv_of hn1
  have e1 : conjBy n⁻¹ (Cen b) = Cen b₁ := by rw [conjBy_cen, inv_inv, a1]
  have e2 : conjBy n⁻¹ (Subgroup.zpowers b₁) = Subgroup.zpowers b := by
    rw [conjBy_zpowers, inv_inv, a2]
  have e3 : conjBy n⁻¹ (conjBy n (Op 2 (Nor U)) ⊓ Cen b) = Op 2 (Nor U) ⊓ Cen b₁ := by
    rw [conjBy_inf, conjBy_inv_conjBy, e1]
  rw [e3, e1, e2] at h7
  refine piStar_of_le (A' := Subgroup.zpowers b) ((Subgroup.zpowers_le).2
    (Subgroup.subset_closure (by simp))) ?_ h7
  exact (B_nor_inf_cen c hU (mem_b₁ c.sec) (B_le_nor_S c hU)).trans' (E_le_B c)

theorem UW_piStar_E (h180 : Nat.card ↥(L ⊓ Cen b₁) = 180) {c' : G} (hc' : c' = b₁ ∨ c' = b₁⁻¹) :
    U ⊓ Cen b₁ ∈ PiStar (Cen (b * c')) (Subgroup.closure ({b, b₁} : Set G)) 2 := by
  have hc'B : c' ∈ B := by
    rcases hc' with rfl | rfl
    · exact mem_b₁ c.sec
    · exact inv_mem (mem_b₁ c.sec)
  have hcen : Cen c' = Cen b₁ := by
    rcases hc' with rfl | rfl
    · rfl
    · exact cen_inv b₁
  have hD : Cen (b * c') ≤ Nor (Subgroup.closure ({b, c'} : Set G)) := by
    rcases hc' with rfl | rfl
    · exact c.hD
    · exact c.hD_b₁inv
  have hcl : Subgroup.closure ({b, c'} : Set G) ≤ B := by
    refine (Subgroup.closure_le _).2 ?_
    intro z hz
    rcases hz with rfl | hz
    · exact mem_b c.sec
    · rw [Set.mem_singleton_iff.1 hz]; exact hc'B
  have hE3 : ∀ w ∈ Subgroup.closure ({b, c'} : Set G), w ^ 3 = 1 := fun w hw => c.hB3 w (hcl hw)
  have hle : U ⊓ Cen b₁ ≤ Cen (b * c') := by
    intro x hx
    obtain ⟨hxU, hxc⟩ := hx
    have hxb : x ∈ Cen b := hU.1 hxU
    have h1 : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 hxb
    have h3 : x * c' = c' * x := by
      have : x ∈ Cen c' := hcen ▸ hxc
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc x * (b * c') = (x * b) * c' := by rw [mul_assoc]
      _ = (b * x) * c' := by rw [h1]
      _ = b * (x * c') := by rw [mul_assoc]
      _ = b * (c' * x) := by rw [h3]
      _ = b * c' * x := by rw [mul_assoc]
  have hBn : B ≤ Nor (U ⊓ Cen b₁) := B_nor_inf_cen c hU (mem_b₁ c.sec) hU.2.2.1
  refine ⟨hle, hU.2.1.to_inf_left, hBn.trans' (E_le_B c), ?_⟩
  intro V hUV hVD hV2 hEV
  have hbV : b ∈ Nor V := hEV (Subgroup.subset_closure (by simp))
  have hV1 : V ≤ Cen b ⊓ Cen c' := E_cen_2sub hE3 hD hV2 hVD hbV
  have hVL : V ≤ L := le_L_of_isPGroup c.post (hV1.trans inf_le_left) hV2
  have hVM : V ≤ L ⊓ Cen b₁ := le_inf hVL (hcen ▸ (hV1.trans inf_le_right))
  have hcard : Nat.card V ≤ 4 := card_le_four_of_dvd_180 hV2 hVM h180
  have h4 : Nat.card ↥(U ⊓ Cen b₁) = 4 := by
    rw [(c.piU hU).2.1.2]; norm_num
  exact (Subgroup.eq_of_le_of_card_ge hUV (by omega)).symm

theorem S_piStar_E (h180 : Nat.card ↥(L ⊓ Cen b₁) = 180) :
    Op 2 (Nor U) ∈ PiStar ⊤ (Subgroup.closure ({b, b₁} : Set G)) 2 := by
  haveI := E_isEA c
  refine B_max_of_centralizers (E := Subgroup.closure ({b, b₁} : Set G)) (E_card c)
    ⟨le_top, op2_isPGroup _, (B_le_nor_S c hU).trans' (E_le_B c)⟩ ?_
  intro e he he1
  rw [top_inf_eq]
  rcases E_cen_cases c he he1 with h | h | h | h
  · rw [h, S48_CSb c hU]; exact U_piStar_E c hU
  · rw [h]; exact W_piStar_E c hU
  · obtain ⟨n, d⟩ := S_core c hU (Or.inl rfl)
    rw [h, d.cbb1]; exact UW_piStar_E c hU h180 (Or.inl rfl)
  · obtain ⟨n, d⟩ := S_core c hU (Or.inl rfl)
    rw [h, d.cbb2]; exact UW_piStar_E c hU h180 (Or.inr rfl)

theorem cycle : ∃ n ∈ Nor (Op 2 (Nor U)) ⊓ Nor B, n * b * n⁻¹ = b₁ ∧ n * b₁ * n⁻¹ = b₂ ∧
    n * b₂ * n⁻¹ = b := by
  obtain ⟨U', hU', hne, hP⟩ := c.exists_other hU
  obtain ⟨-, -, -, -, -, ⟨n, hn, hn1, hn2, hn3⟩⟩ := c.sec.mono
  have hn3B : n * (n * n) ∈ B := by
    have hcen : n * (n * n) ∈ CenS B := by
      refine IsoAux.cen_of_gen c.sec.mono.2.1 ?_
      have e1 : (n * n) * b * (n * n)⁻¹ = b₂ := conj_comp hn1 hn2
      have e2 : (n * (n * n)) * b * (n * (n * n))⁻¹ = b := conj_comp e1 hn3
      have f1 : (n * n) * b₁ * (n * n)⁻¹ = b := conj_comp hn2 hn3
      have f2 : (n * (n * n)) * b₁ * (n * (n * n))⁻¹ = b₁ := conj_comp f1 hn1
      have g1 : (n * n) * b₂ * (n * n)⁻¹ = b₁ := conj_comp hn3 hn1
      have g2 : (n * (n * n)) * b₂ * (n * (n * n))⁻¹ = b₂ := conj_comp g1 hn2
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact (IsoAux.commute_of_sg e2).symm
      · exact (IsoAux.commute_of_sg f2).symm
      · exact (IsoAux.commute_of_sg g2).symm
    rwa [c.post.cB] at hcen
  have hnS : n ∈ Nor (Op 2 (Nor U)) := by
    rw [mem_nor_iff_conjBy]
    rcases orbit_pair c hP hne.symm hn with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · exact k1
    · exfalso
      have h3 : conjBy (n * (n * n)) (Op 2 (Nor U)) = Op 2 (Nor U) :=
        mem_nor_iff_conjBy.1 (B_le_nor_S c hU hn3B)
      rw [conjBy_mul, conjBy_mul, k1, k2, k1] at h3
      exact S_inj c hU' hU hne h3
  exact ⟨n, ⟨hnS, hn⟩, hn1, hn2, hn3⟩

theorem S_iso :
    Nat.card ↥⁅Op 2 (Nor U), Subgroup.zpowers b⁆ = 4 ∧
      Nat.card ↥⁅Op 2 (Nor U), Subgroup.zpowers b₁⁆ = 4 ∧
      Nat.card ↥⁅Op 2 (Nor U), Subgroup.zpowers b₂⁆ = 4 ∧
      ⁅Op 2 (Nor U), Subgroup.zpowers b⁆ ⊔ ⁅Op 2 (Nor U), Subgroup.zpowers b₁⁆ ⊔
        ⁅Op 2 (Nor U), Subgroup.zpowers b₂⁆ = Op 2 (Nor U) ∧
      ⁅Op 2 (Nor U), Subgroup.zpowers b⁆ ≤ CenS (Subgroup.closure {b₁, b₂}) ∧
      ⁅Op 2 (Nor U), Subgroup.zpowers b₁⁆ ≤ CenS (Subgroup.closure {b, b₂}) ∧
      ⁅Op 2 (Nor U), Subgroup.zpowers b₂⁆ ≤ CenS (Subgroup.closure {b, b₁}) := by
  obtain ⟨hEA6, -⟩ := c.S48_elemab hU
  obtain ⟨hb2, hb1, hC⟩ := c.S48_b2 hU
  have h₀ : Nat.card ↥(Op 2 (Nor U) ⊓ Cen b) = 16 := by
    rw [c.S48_CSb hU]; exact c.piU_card hU
  exact B_isotypic hEA6 c.sec.mono.1 (c.B_le_nor_S hU) c.sec.mono.2.1 h₀ hb1 hb2 hC

theorem S_piStar_E₁ (h180 : Nat.card ↥(L ⊓ Cen b₁) = 180) :
    Op 2 (Nor U) ∈ PiStar ⊤ (Subgroup.closure ({b₁, b₂} : Set G)) 2 := by
  obtain ⟨n, hnH, hn1, hn2, -⟩ := c.cycle hU
  have h := conj_piStar n (c.S_piStar_E hU h180)
  rwa [conjBy_top, conjBy_closure_pair, hn1, hn2, mem_nor_iff_conjBy.1 hnH.1] at h

theorem S_piStar_E₂ (h180 : Nat.card ↥(L ⊓ Cen b₁) = 180) :
    Op 2 (Nor U) ∈ PiStar ⊤ (Subgroup.closure ({b₂, b} : Set G)) 2 := by
  obtain ⟨n, hnH, hn1, hn2, hn3⟩ := c.cycle hU
  have hnn : n * n ∈ Nor (Op 2 (Nor U)) := mul_mem hnH.1 hnH.1
  have h := conj_piStar (n * n) (c.S_piStar_E hU h180)
  rwa [conjBy_top, conjBy_closure_pair, conj_comp hn1 hn2, conj_comp hn2 hn3,
    mem_nor_iff_conjBy.1 hnn] at h

theorem S_ea2 : EA2 (Op 2 (Nor U)) := EA2.of_isElemAb (c.S48_elemab hU).1

theorem comm_le_S {z : G} (hz : z ∈ B) : ⁅Op 2 (Nor U), Subgroup.zpowers z⁆ ≤ Op 2 (Nor U) := by
  have hSEA := c.S_ea2 hU
  exact IsoAux.W_le_S hSEA.1 hSEA.2 (c.B_le_nor_S hU hz) (c.hB3 z hz)

theorem S49_one_comp₂ (h180 : Nat.card ↥(L ⊓ Cen b₁) = 180) {x : G}
    (hx : x ∈ ⁅Op 2 (Nor U), Subgroup.zpowers b₂⁆) (hx1 : x ≠ 1) :
    Op 2 (Cen x) = Op 2 (Nor U) := by
  have hE : Subgroup.closure ({b, b₁} : Set G) ≤ Nor (Op 2 (Nor U)) :=
    (c.B_le_nor_S hU).trans' (c.E_le_B)
  exact op2_cen_eq c.sec.hyp.char2 (c.S_ea2 hU) hE (c.S_piStar_E hU h180)
    (c.comm_le_S hU (mem_b₂ c.sec) hx) hx1 (le_cen_of_mem_cenS ((c.S_iso hU).2.2.2.2.2.2 hx))

theorem S49_one_comp₀ (h180 : Nat.card ↥(L ⊓ Cen b₁) = 180) {x : G}
    (hx : x ∈ ⁅Op 2 (Nor U), Subgroup.zpowers b⁆) (hx1 : x ≠ 1) :
    Op 2 (Cen x) = Op 2 (Nor U) := by
  have hE : Subgroup.closure ({b₁, b₂} : Set G) ≤ Nor (Op 2 (Nor U)) := by
    refine (Subgroup.closure_le _).2 ?_
    intro z hz
    rcases hz with rfl | hz
    · exact c.B_le_nor_S hU (mem_b₁ c.sec)
    · rw [Set.mem_singleton_iff.1 hz]; exact c.B_le_nor_S hU (mem_b₂ c.sec)
  exact op2_cen_eq c.sec.hyp.char2 (c.S_ea2 hU) hE (c.S_piStar_E₁ hU h180)
    (c.comm_le_S hU (mem_b c.sec) hx) hx1 (le_cen_of_mem_cenS ((c.S_iso hU).2.2.2.2.1 hx))

theorem S49_one_comp₁ (h180 : Nat.card ↥(L ⊓ Cen b₁) = 180) {x : G}
    (hx : x ∈ ⁅Op 2 (Nor U), Subgroup.zpowers b₁⁆) (hx1 : x ≠ 1) :
    Op 2 (Cen x) = Op 2 (Nor U) := by
  have hE : Subgroup.closure ({b₂, b} : Set G) ≤ Nor (Op 2 (Nor U)) := by
    refine (Subgroup.closure_le _).2 ?_
    intro z hz
    rcases hz with rfl | hz
    · exact c.B_le_nor_S hU (mem_b₂ c.sec)
    · rw [Set.mem_singleton_iff.1 hz]; exact c.B_le_nor_S hU (mem_b c.sec)
  have hcen : Subgroup.closure ({b₂, b} : Set G) ≤ Cen x := by
    refine le_cen_of_mem_cenS ?_
    have := (c.S_iso hU).2.2.2.2.2.1 hx
    rwa [Set.pair_comm] at this
  exact op2_cen_eq c.sec.hyp.char2 (c.S_ea2 hU) hE (c.S_piStar_E₂ hU h180)
    (c.comm_le_S hU (mem_b₁ c.sec) hx) hx1 hcen

end S48Ctx

theorem cc_eq_formPerm : cc = (List.formPerm [0, 1, 2] : P8) := by decide +kernel

theorem card_L_cen_b₁ (hA : A8Model L)
    (h : FF84Post b L B K b₁ b₂) : Nat.card ↥(L ⊓ Cen b₁) = 180 := by
  obtain ⟨e, he₁, -⟩ := M0_model hA h
  have hb₁ : b₁ ∈ L := (Subgroup.mem_inf.1 h.sec.hb₁).2
  have h1 := M0_card_cen e ⟨b₁, hb₁⟩
  have h2 : ((e ⟨b₁, hb₁⟩ : A8s) : P8) = cc := he₁ ⟨b₁, hb₁⟩ rfl
  change Nat.card ↥(Subgroup.centralizer ({((e ⟨b₁, hb₁⟩ : A8s) : P8)} : Set P8) ⊓ A8s) =
    Nat.card ↥(L ⊓ Cen b₁) at h1
  rw [h2, cc_eq_formPerm] at h1
  rw [← h1]
  exact card_inf_of_cycleType3 cycleType_c

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
