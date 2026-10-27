module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBB
public import CFSG.GroupTheory.BinaryFixedFreeRank
public import CFSG.Quasithin.Background.D2Tools

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

structure InvCfg131 (p : ℕ) (t : MulAut W) (P : Subgroup (MulAut W)) : Prop where
  hW : ∀ w : W, w ^ 2 = 1
  ht : orderOf t = 2
  hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3
  hp : p.Prime
  hP : IsPGroup p ↥P
  hne : P ≠ ⊥
  hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P
  hc : ⁅P, Subgroup.zpowers t⁆ = P
  hgood : 3 < p ∨ InducesTransvection t ⊤

theorem eq_one_of_inverted_elemAbelian (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : orderOf t = 2) (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hgood : 3 < p ∨ InducesTransvection t ⊤) (hn : 0 < n)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelianOfRank p n ↥X)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) : n = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hbridge := n_mul_dihedralDeg_le_two_mul_rk hW ht hp hp2 hn hX hinv
  have h6 : n * dihedralDeg p ≤ 6 := by
    calc n * dihedralDeg p ≤ 2 * rk ↥(commSub ⊤ (Subgroup.zpowers t)) := hbridge
      _ ≤ 2 * 3 := by gcongr
      _ = 6 := by norm_num
  have hp7 : p ≤ 7 := by
    by_contra h
    push Not at h
    have h8 : 7 < p := by omega
    have hgt := six_lt_dihedralDeg_of_seven_lt hp h8
    nlinarith [h6, hgt, hn]
  have hd3 : dihedralDeg 3 = 2 := by
    unfold dihedralDeg dParam
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [orderOf_eq_prime (p := 2) (by decide) (by decide)]
    norm_num
  have hd5 : dihedralDeg 5 = 4 := by
    unfold dihedralDeg dParam
    have hnot : ¬ (2 : ZMod 5) ^ 2 ^ 1 = 1 := by decide
    have hfin : (2 : ZMod 5) ^ 2 ^ (1 + 1) = 1 := by decide
    have h := orderOf_eq_prime_pow (x := (2 : ZMod 5)) (p := 2) (n := 1) hnot hfin
    norm_num at h
    rw [h]
    norm_num
  have hd7 : dihedralDeg 7 = 6 := by
    unfold dihedralDeg dParam
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [orderOf_eq_prime (p := 3) (by decide) (by decide)]
    norm_num
  have hcases : p = 3 ∨ p = 5 ∨ p = 7 := by
    have h2 : 2 ≤ p := hp.two_le
    have hp4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
    have hp6 : p ≠ 6 := fun h => by rw [h] at hp; norm_num at hp
    omega
  rcases hcases with rfl | rfl | rfl
  · rw [hd3] at h6
    rcases hgood with h | h
    · omega
    · have h1 : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 1 := h.2
      rw [hd3, h1] at hbridge
      omega
  · rw [hd5] at h6
    omega
  · rw [hd7] at h6
    omega

theorem false_of_inverted_orderOf_sq (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : orderOf t = 2) (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hgood : 3 < p ∨ InducesTransvection t ⊤) {c : MulAut W}
    (hc : orderOf c = p ^ 2) (hinv : t * c * t⁻¹ = c⁻¹) : False :=
  w16g_false_of_inverted_orderOf_sq hW ht hrk hp hp2 hgood hc hinv

theorem eq_one_or_orderOf_eq_prime_of_inverted {p : ℕ} {t : MulAut W}
    {P : Subgroup (MulAut W)} (h : InvCfg131 p t P) {c : MulAut W} (hcP : c ∈ P)
    (hinv : t * c * t⁻¹ = c⁻¹) : c = 1 ∨ orderOf c = p := by
  haveI : Fact p.Prime := ⟨h.hp⟩
  obtain ⟨k, hk⟩ := h.hP.exists_orderOf_eq_pow (⟨c, hcP⟩ : ↥P)
  have hck : orderOf c = p ^ k := by
    rw [← Subgroup.orderOf_mk c hcP]
    exact hk
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · left
      rw [pow_zero] at hck
      exact orderOf_eq_one_iff.mp hck
    · right
      simpa using hck
  · exfalso
    have hp2 : p ≠ 2 := by
      intro hp2
      have htt : t * t = 1 := by
        have := pow_orderOf_eq_one t
        rw [h.ht, pow_two] at this
        exact this
      exact h.hne (eq_bot_of_isPGroup_two_of_comm_eq_self htt (hp2 ▸ h.hP) h.hn h.hc)
    have hdord : orderOf (c ^ p ^ (k - 2)) = p ^ 2 := by
      rw [orderOf_pow, hck]
      have hle : k - 2 ≤ k := Nat.sub_le _ _
      have hgcd : Nat.gcd (p ^ k) (p ^ (k - 2)) = p ^ (k - 2) :=
        Nat.gcd_eq_right (pow_dvd_pow p hle)
      rw [hgcd, Nat.pow_div hle h.hp.pos]
      congr 1
      omega
    exact false_of_inverted_orderOf_sq h.hW h.ht h.hrk h.hp hp2 h.hgood hdord
      (w16g_conj_pow_inv hinv (p ^ (k - 2)))

theorem le_closure_inverted {t : MulAut W} (ht : t * t = 1) {P : Subgroup (MulAut W)}
    (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P) (hc : ⁅P, Subgroup.zpowers t⁆ = P) :
    P ≤ Subgroup.closure {c | c ∈ P ∧ t * c * t⁻¹ = c⁻¹} := by
  have hmain : ⁅P, Subgroup.zpowers t⁆ ≤ Subgroup.closure {c | c ∈ P ∧ t * c * t⁻¹ = c⁻¹} := by
    apply Subgroup.commutator_le.mpr
    intro p hp s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · rw [hm, zpow_mul, h2, one_zpow, commutatorElement_one_right]
      exact Subgroup.subset_closure ⟨P.one_mem, by simp [ht, htinv]⟩
    · rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one, commutatorElement_def]
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · have hmem : t * p⁻¹ * t⁻¹ ∈ P := hn p⁻¹ (P.inv_mem hp)
        simpa [htinv, mul_assoc] using P.mul_mem hp hmem
      · simp [ht, htinv, mul_assoc]
  rwa [hc] at hmain

theorem card_eq_prime_of_central_inverted {p : ℕ} {t : MulAut W} {P : Subgroup (MulAut W)}
    (h : InvCfg131 p t P) {z : MulAut W} (hzP : z ∈ P) (hz : orderOf z = p)
    (hzc : ∀ y ∈ P, y * z = z * y) (hzi : t * z * t⁻¹ = z⁻¹) : Nat.card P = p := by
  haveI : Fact p.Prime := ⟨h.hp⟩
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at this
    exact this
  have hp2 : p ≠ 2 := by
    intro hp2
    exact h.hne (eq_bot_of_isPGroup_two_of_comm_eq_self htt (hp2 ▸ h.hP) h.hn h.hc)
  have hkey : ∀ y ∈ P, t * y * t⁻¹ = y⁻¹ → y ∈ Subgroup.zpowers z := by
    intro y hyP hyinv
    rcases eq_one_or_orderOf_eq_prime_of_inverted h hyP hyinv with hy1 | hyord
    · rw [hy1]; exact Subgroup.one_mem _
    · set X : Subgroup (MulAut W) := Subgroup.closure ({y, z} : Set (MulAut W)) with hX
      have hyX : y ∈ X := Subgroup.subset_closure (by simp)
      have hzX : z ∈ X := Subgroup.subset_closure (by simp)
      have hpair : ({y, z} : Set (MulAut W)).Pairwise Commute := by
        intro a ha b hb _
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with ha | ha
        · rcases hb with hb | hb
          · simpa [ha, hb] using Commute.refl y
          · simpa [ha, hb] using (commute_iff_eq y z).mpr (hzc y hyP)
        · rcases hb with hb | hb
          · simpa [ha, hb] using (commute_iff_eq z y).mpr (hzc y hyP).symm
          · simpa [ha, hb] using Commute.refl z
      have hEc : IsMulCommutative X := Subgroup.isMulCommutative_closure hpair
      have hcommX : ∀ a b : ↥X, a * b = b * a := fun a b => hEc.is_comm.comm a b
      have hy_pow : y ^ p = 1 := by
        have := pow_orderOf_eq_one y
        rwa [hyord] at this
      have hz_pow : z ^ p = 1 := by
        have := pow_orderOf_eq_one z
        rwa [hz] at this
      have hcommW : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a haX b hbX =>
        congrArg Subtype.val (hcommX ⟨a, haX⟩ ⟨b, hbX⟩)
      have hpowX : ∀ a : ↥X, a ^ p = 1 := by
        have hgen : ∀ x ∈ X, x ^ p = 1 := by
          apply Subgroup.closure_induction (p := fun x _ => x ^ p = 1)
          · rintro x (rfl | rfl)
            · exact hy_pow
            · exact hz_pow
          · exact one_pow p
          · rintro a b haX hbX ha hb
            rw [Commute.mul_pow (show Commute a b from hcommW a haX b hbX) p, ha, hb, one_mul]
          · rintro a haX ha
            rw [inv_pow, ha, inv_one]
        intro a
        exact Subtype.ext (hgen a.1 a.2)
      have hinvX : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹ := by
        have hgen : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹ := by
          apply Subgroup.closure_induction (p := fun x _ => t * x * t⁻¹ = x⁻¹)
          · rintro x (rfl | rfl)
            · exact hyinv
            · exact hzi
          · simp
          · rintro a b haX hbX ha hb
            have h1 : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
            rw [h1, ha, hb]
            calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
              _ = (a * b)⁻¹ := by rw [← hcommW a haX b hbX]
          · rintro a haX ha
            rw [show t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ by group, ha, inv_inv]
        exact hgen
      have hXle : X ≤ P := by
        rw [hX, Subgroup.closure_le]
        intro w hw
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with hw | hw
        · rw [hw]; exact hyP
        · rw [hw]; exact hzP
      have hXp : IsPGroup p ↥X := fun x => by
        obtain ⟨k, hk⟩ := h.hP ⟨x.1, hXle x.2⟩
        exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).mp hXp
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hpos
        · exfalso
          have hdvd : p ∣ Nat.card ↥X := by
            have := orderOf_dvd_natCard (⟨z, hzX⟩ : ↥X)
            rwa [Subgroup.orderOf_mk, hz] at this
          rw [hk, hk0, pow_zero] at hdvd
          exact h.hp.not_dvd_one hdvd
        · exact hpos
      have hrank : IsElemAbelianOfRank p k ↥X :=
        w16g_isElemAbelianOfRank_of_card hcommX hpowX hk
      have hk1 : k = 1 :=
        eq_one_of_inverted_elemAbelian h.hW h.ht h.hrk h.hp hp2 h.hgood hkpos hrank hinvX
      have hXcard : Nat.card ↥X = p := by rw [hk, hk1, pow_one]
      have hzXcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
      have heq : X = Subgroup.zpowers z :=
        (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzX)
          (by rw [hXcard, hzXcard])).symm
      exact heq ▸ hyX
  have hgen := le_closure_inverted (t := t) htt h.hn h.hc
  have hclosure : Subgroup.closure {c | c ∈ P ∧ t * c * t⁻¹ = c⁻¹} ≤ Subgroup.zpowers z := by
    rw [Subgroup.closure_le]
    rintro c ⟨hcP, hcinv⟩
    exact hkey c hcP hcinv
  have hPeq : P = Subgroup.zpowers z :=
    le_antisymm (hgen.trans hclosure) (Subgroup.zpowers_le.2 hzP)
  rw [hPeq, Nat.card_zpowers, hz]

private theorem w16g_subgroupOf_commutator {M : Type*} [Group M] {H₁ H₂ K : Subgroup M}
    (h₁ : H₁ ≤ K) (h₂ : H₂ ≤ K) :
    ⁅H₁.subgroupOf K, H₂.subgroupOf K⁆ = (⁅H₁, H₂⁆).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h₁,
    Subgroup.map_subgroupOf_eq_of_le h₂,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le h₁ h₂)]

private theorem w16g_map_inclusion_subgroupOf {W : Type} [CommGroup W]
    {G K : Subgroup (MulAut W)} (hGK : G ≤ K) {P : Subgroup (MulAut W)} (hPG : P ≤ G) :
    (P.subgroupOf G).map (Subgroup.inclusion hGK) = P.subgroupOf K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hy
  · intro hx
    exact ⟨⟨(x : MulAut W), hPG (Subgroup.mem_subgroupOf.mp hx)⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), Subtype.ext rfl⟩

private theorem w16g_conj_inv_of_involution {A : Type*} [Group A] {t y : A} (ht : t * t = 1) :
    t * (y⁻¹ * (t * y * t⁻¹)) * t⁻¹ = (y⁻¹ * (t * y * t⁻¹))⁻¹ := by
  have hφ : MulAut.conj t (MulAut.conj t y) = y := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
    rw [MulAut.conj_apply, MulAut.conj_apply, htinv]
    calc t * (t * y * t) * t = t * t * y * (t * t) := by group
      _ = y := by simp [ht]
  calc t * (y⁻¹ * (t * y * t⁻¹)) * t⁻¹
      = MulAut.conj t (y⁻¹ * (t * y * t⁻¹)) := (MulAut.conj_apply t _).symm
    _ = MulAut.conj t (y⁻¹ * MulAut.conj t y) := by
          rw [show t * y * t⁻¹ = MulAut.conj t y from (MulAut.conj_apply t y).symm]
    _ = (MulAut.conj t y)⁻¹ * y := by rw [map_mul, map_inv, hφ]
    _ = (y⁻¹ * (t * y * t⁻¹))⁻¹ := by rw [mul_inv_rev, inv_inv, MulAut.conj_apply]

private theorem w16g_card_eq_prime_of_comm_le {p : ℕ} {t : MulAut W}
    {P : Subgroup (MulAut W)} (h : InvCfg131 p t P) (htt : t * t = 1) {x : MulAut W}
    (hxP : x ∈ P) (hxinv : t * x * t⁻¹ = x⁻¹) (hxord : orderOf x = p)
    {Q : Subgroup (MulAut W)} (hQcentral : ∀ q ∈ Q, t * q * t⁻¹ = q)
    (hdecomp : ∀ g ∈ P, ∃ q ∈ Q, ∃ j : ℤ, g⁻¹ = q * x ^ j) : Nat.card P = p := by
  have hzpt : ∀ s ∈ Subgroup.zpowers t, s = 1 ∨ s = t := by
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      rw [hm, zpow_mul, show t ^ (2 : ℤ) = 1 from by rw [zpow_two, htt], one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, show t ^ (2 : ℤ) = 1 from by rw [zpow_two, htt], one_zpow,
        one_mul, zpow_one]
  have hcomm_le : ⁅P, Subgroup.zpowers t⁆ ≤ Subgroup.zpowers x := by
    apply Subgroup.commutator_le.mpr
    intro g hg s hs
    rcases hzpt s hs with h1 | h1
    · rw [h1, commutatorElement_one_right]; exact Subgroup.one_mem _
    · rw [h1]
      obtain ⟨q, hq, j, hqj⟩ := hdecomp g hg
      have hqt : t * q * t⁻¹ = q := hQcentral q hq
      have htj : t * x ^ j * t⁻¹ = x ^ (-j) := by
        calc t * x ^ j * t⁻¹ = MulAut.conj t (x ^ j) := (MulAut.conj_apply t _).symm
          _ = (MulAut.conj t x) ^ j := map_zpow (MulAut.conj t) x j
          _ = (x⁻¹) ^ j := by
                rw [show MulAut.conj t x = x⁻¹ from by rw [MulAut.conj_apply, hxinv]]
          _ = x ^ (-j) := by rw [inv_zpow']
      have htg : t * g⁻¹ * t⁻¹ = q * x ^ (-j) := by
        rw [hqj]
        calc t * (q * x ^ j) * t⁻¹ = (t * q * t⁻¹) * (t * x ^ j * t⁻¹) := by group
          _ = q * x ^ (-j) := by rw [hqt, htj]
      have hg_eq : g = x ^ (-j) * q⁻¹ := by
        rw [← inv_inv g, hqj, mul_inv_rev, ← zpow_neg]
      have hcomm_eq : ⁅g, t⁆ = x ^ (-2 * j) := by
        calc ⁅g, t⁆ = g * (t * g⁻¹ * t⁻¹) := by
              rw [commutatorElement_def]; group
          _ = (x ^ (-j) * q⁻¹) * (q * x ^ (-j)) := by rw [htg, hg_eq]
          _ = x ^ (-2 * j) := by
              have h2 : x ^ (-j) * x ^ (-j) = x ^ (-2 * j) := by
                rw [← zpow_add]; congr 1; ring
              rw [show (x ^ (-j) * q⁻¹) * (q * x ^ (-j)) = x ^ (-j) * x ^ (-j) by group, h2]
      rw [hcomm_eq]
      exact Subgroup.zpow_mem_zpowers x (-2 * j)
  have hPle_x : P ≤ Subgroup.zpowers x := by
    rw [← h.hc]
    exact hcomm_le
  have hPcard_le : Nat.card P ≤ p := by
    have h1 : Nat.card P ≤ Nat.card ↥(Subgroup.zpowers x) :=
      Nat.card_le_card_of_injective
        (fun y : ↥P => (⟨y.1, hPle_x y.2⟩ : ↥(Subgroup.zpowers x)))
        (fun y z hyz => Subtype.ext
          (congrArg (Subtype.val : ↥(Subgroup.zpowers x) → MulAut W) hyz))
    rwa [Nat.card_zpowers, hxord] at h1
  have hPcard_ge : p ≤ Nat.card P := by
    have h1 : orderOf x ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hxP
    rw [hxord] at h1
    exact Nat.le_of_dvd Nat.card_pos h1
  exact le_antisymm hPcard_le hPcard_ge

private theorem w16g_card_eq_prime_of_restriction {p : ℕ} {t : MulAut W}
    {P : Subgroup (MulAut W)} (h : InvCfg131 p t P) {V₀ : Subgroup W}
    (ht_stab : t ∈ stabSub V₀) (hPstab : P ≤ stabSub V₀)
    (φ : ↥P →* MulAut ↥V₀) (hrange : φ.range = autSub P V₀)
    (hφeq : φ = (resHom V₀).comp (Subgroup.inclusion hPstab))
    {Q : Subgroup (MulAut W)} (hker : ∀ g : ↥P, g ∈ φ.ker ↔ (g : MulAut W) ∈ Q)
    (hQcentral : ∀ q ∈ Q, t * q * t⁻¹ = q)
    (hne' : autSub P V₀ ≠ ⊥) (hP'card : Nat.card ↥(autSub P V₀) = p)
    (hc' : ⁅autSub P V₀, Subgroup.zpowers (resHom V₀ ⟨t, ht_stab⟩)⁆ = autSub P V₀) :
    Nat.card P = p := by
  have htt : t * t = 1 := by
    have h2 := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at h2
    exact h2
  let t' : MulAut ↥V₀ := resHom V₀ ⟨t, ht_stab⟩
  obtain ⟨a, haP', ha1⟩ : ∃ a ∈ autSub P V₀, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne' (eq_bot_iff.mpr hcon)
  have hagen : Subgroup.zpowers a = autSub P V₀ := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haP')
    have hdiv : orderOf a ∣ p := by
      have h2 := Subgroup.orderOf_dvd_natCard (autSub P V₀) haP'
      rwa [hP'card] at h2
    have hord : orderOf a = p := by
      rcases (Nat.dvd_prime h.hp).mp hdiv with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) ha1
      · exact h1
    rw [Nat.card_zpowers, hord, hP'card]
  obtain ⟨y₀, hy₀_eq⟩ : ∃ y : ↥P, φ y = a :=
    MonoidHom.mem_range.mp (hrange ▸ haP' : a ∈ φ.range)
  set x : MulAut W := (y₀ : MulAut W)⁻¹ * (t * (y₀ : MulAut W) * t⁻¹) with hxdef
  have hxP : x ∈ P := P.mul_mem (P.inv_mem y₀.2) (h.hn _ y₀.2)
  have hxinv : t * x * t⁻¹ = x⁻¹ := by
    rw [hxdef]
    exact w16g_conj_inv_of_involution htt
  have hφx : φ ⟨x, hxP⟩ = a⁻¹ * (t' * a * t'⁻¹) := by
    have hx_eq : (⟨x, hPstab hxP⟩ : stabSub V₀)
        = (⟨y₀, hPstab y₀.2⟩ : stabSub V₀)⁻¹
          * (⟨t, ht_stab⟩ * ⟨y₀, hPstab y₀.2⟩ * ⟨t, ht_stab⟩⁻¹) := by
      apply Subtype.ext
      change x = (y₀ : MulAut W)⁻¹ * (t * (y₀ : MulAut W) * t⁻¹)
      rw [hxdef]
    have hmap := congrArg (resHom V₀) hx_eq
    simp only [map_mul, map_inv] at hmap
    have hy₀_res : resHom V₀ (⟨y₀, hPstab y₀.2⟩ : stabSub V₀) = a := by
      rw [← hy₀_eq, hφeq]; rfl
    have hx_res : resHom V₀ (⟨x, hPstab hxP⟩ : stabSub V₀) = φ ⟨x, hxP⟩ := by
      rw [hφeq]; rfl
    rw [hx_res, hy₀_res,
      show resHom V₀ (⟨t, ht_stab⟩ : stabSub V₀) = t' from rfl] at hmap
    exact hmap
  have hφx_ne : φ ⟨x, hxP⟩ ≠ 1 := by
    intro h1
    have h2 : t' * a * t'⁻¹ = a := by
      have h3 : a⁻¹ * (t' * a * t'⁻¹) = 1 := hφx.symm.trans h1
      calc t' * a * t'⁻¹ = a * (a⁻¹ * (t' * a * t'⁻¹)) := by group
        _ = a * 1 := by rw [h3]
        _ = a := by simp
    have hcomm : Commute t' a := by
      rw [commute_iff_eq]
      calc t' * a = t' * a * t'⁻¹ * t' := by group
        _ = a * t' := by rw [h2]
    have hcent : autSub P V₀ ≤ Subgroup.centralizer (Subgroup.zpowers t') := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hagen ▸ hy : y ∈ Subgroup.zpowers a)
      rw [← hk, ← hm]
      exact (hcomm.zpow_left k).zpow_right m |>.eq
    have hbot : ⁅autSub P V₀, Subgroup.zpowers t'⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
    rw [hc'] at hbot
    exact hne' hbot
  have hx_ne : x ≠ 1 := by
    intro hx1
    have h2 : φ ⟨x, hxP⟩ = 1 := by
      have hthis : (⟨x, hxP⟩ : ↥P) = 1 := by
        apply Subtype.ext
        exact hx1
      rw [hthis, map_one]
    exact hφx_ne h2
  have hxord : orderOf x = p := by
    rcases eq_one_or_orderOf_eq_prime_of_inverted h hxP hxinv with h1 | h1
    · exact absurd h1 hx_ne
    · exact h1
  have hφx_mem : φ ⟨x, hxP⟩ ∈ autSub P V₀ :=
    hrange ▸ (MonoidHom.mem_range.mpr ⟨⟨x, hxP⟩, rfl⟩ : φ ⟨x, hxP⟩ ∈ φ.range)
  have hφx_ord : orderOf (φ ⟨x, hxP⟩) = p := by
    have hdiv : orderOf (φ ⟨x, hxP⟩) ∣ p := by
      have h2 := Subgroup.orderOf_dvd_natCard (autSub P V₀) hφx_mem
      rwa [hP'card] at h2
    rcases (Nat.dvd_prime h.hp).mp hdiv with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hφx_ne
    · exact h1
  have hgen_x : Subgroup.zpowers (φ ⟨x, hxP⟩) = autSub P V₀ := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hφx_mem)
    rw [Nat.card_zpowers, hφx_ord, hP'card]
  have hdecomp : ∀ g ∈ P, ∃ q ∈ Q, ∃ j : ℤ, g⁻¹ = q * x ^ j := by
    intro g hg
    have hginv : g⁻¹ ∈ P := P.inv_mem hg
    have hmem : φ ⟨g⁻¹, hginv⟩ ∈ Subgroup.zpowers (φ ⟨x, hxP⟩) := by
      rw [hgen_x]
      exact hrange ▸ MonoidHom.mem_range.mpr ⟨⟨g⁻¹, hginv⟩, rfl⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hker_mem : (⟨g⁻¹, hginv⟩ * (⟨x, hxP⟩) ^ (-j) : ↥P) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, ← hj]
      simp
    have hqQ : ((⟨g⁻¹, hginv⟩ * (⟨x, hxP⟩) ^ (-j) : ↥P) : MulAut W) ∈ Q :=
      (hker _).mp hker_mem
    refine ⟨((⟨g⁻¹, hginv⟩ * (⟨x, hxP⟩) ^ (-j) : ↥P) : MulAut W), hqQ, j, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
    group
  exact w16g_card_eq_prime_of_comm_le h htt hxP hxinv hxord hQcentral hdecomp

theorem card_eq_prime_of_central_comm_eq_bot {p : ℕ} {t : MulAut W} {P : Subgroup (MulAut W)}
    (h : InvCfg131 p t P)
    (ih : ∀ (W' : Type) [CommGroup W'] [Finite W'] (t' : MulAut W')
      (P' : Subgroup (MulAut W')), Nat.card W' < Nat.card W → InvCfg131 p t' P' →
        Nat.card P' = p)
    {Z : Subgroup (MulAut W)} (hZP : Z ≤ P) (hZc : ∀ z ∈ Z, ∀ y ∈ P, y * z = z * y)
    (hZ : IsElemAbelianOfRank p 1 ↥Z) (hZt : ∀ z ∈ Z, t * z * t⁻¹ = z)
    (h0 : commSub (commSub ⊤ Z) (Subgroup.zpowers t) = ⊥) : Nat.card P = p := by
  haveI : Fact p.Prime := ⟨h.hp⟩
  have htt : t * t = 1 := by
    have h2 := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at h2
    exact h2
  have hp2 : p ≠ 2 := by
    intro hp2
    exact h.hne (eq_bot_of_isPGroup_two_of_comm_eq_self htt (hp2 ▸ h.hP) h.hn h.hc)
  have hZcard : Nat.card Z = p := (w16g_isElemAbelianOfRank_one_iff h.hp).mp hZ
  have hZodd : Odd (Nat.card Z) := by rw [hZcard]; exact h.hp.odd_of_ne_two hp2
  set V₀ : Subgroup W := fixV Z with hV₀def
  set V₁ : Subgroup W := commSub ⊤ Z with hV₁def
  have hsup : V₀ ⊔ V₁ = ⊤ := by
    rw [hV₀def, hV₁def]
    exact CFSG.Quasithin.Asc81c.fixV_sup_commSub_eq_top' h.hW hZodd
  have hinf : V₀ ⊓ V₁ = ⊥ := by
    rw [hV₀def, hV₁def]
    exact CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' h.hW hZodd
  have hZPnorm : ∀ y ∈ P, ∀ z ∈ Z, y * z * y⁻¹ ∈ Z := by
    intro y hy z hz
    rw [hZc z hz y hy, mul_assoc, mul_inv_cancel, mul_one]
    exact hz
  have hZconj : ∀ x ∈ Subgroup.zpowers t, ∀ z ∈ Z, x * z * x⁻¹ ∈ Z := by
    intro x hx z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : Commute t z := by
      rw [commute_iff_eq]
      have h2 := hZt z hz
      rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right htt] at h2
      calc t * z = t * z * (t * t) := by rw [htt, mul_one]
        _ = t * z * t * t := by group
        _ = z * t := by rw [h2]
    have h2 : Commute (t ^ k) z := h1.zpow_left k
    rw [h2.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact hz
  have hPV₀ : StableUnder P V₀ := by
    rw [hV₀def]
    exact stableUnder_fixV hZPnorm
  have hPV₁ : StableUnder P V₁ := by
    rw [hV₁def]
    exact stableUnder_commSub hZPnorm (fun _ _ _ _ => Subgroup.mem_top _)
  have htV₀ : StableUnder (Subgroup.zpowers t) V₀ := by
    rw [hV₀def]
    exact stableUnder_fixV hZconj
  have htV₁ : StableUnder (Subgroup.zpowers t) V₁ := by
    rw [hV₁def]
    exact stableUnder_commSub hZconj (fun _ _ _ _ => Subgroup.mem_top _)
  have hV₁_fix : V₁ ≤ fixV (Subgroup.zpowers t) := by
    rw [hV₁def]
    exact commSub_eq_bot_iff.mp h0
  have htV₁triv : ∀ b ∈ V₁, t b = b := fun b hb =>
    (mem_fixV.mp (hV₁_fix hb)) t (Subgroup.mem_zpowers t)
  have htV₀mem : ∀ a ∈ V₀, t a ∈ V₀ := fun a ha => htV₀ t (Subgroup.mem_zpowers t) a ha
  have htinvV₀mem : ∀ a ∈ V₀, t⁻¹ a ∈ V₀ :=
    fun a ha => htV₀ t⁻¹ (Subgroup.inv_mem (Subgroup.zpowers t) (Subgroup.mem_zpowers t)) a ha
  have htinvV₁triv : ∀ b ∈ V₁, t⁻¹ b = b := fun b hb =>
    (mem_fixV.mp (hV₁_fix hb)) t⁻¹ (Subgroup.inv_mem (Subgroup.zpowers t) (Subgroup.mem_zpowers t))
  have hV₀_ne_top : V₀ ≠ ⊤ := by
    intro htop
    have hZbot : Z = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hz1 : z = 1 := by
        ext w
        have hw : w ∈ V₀ := by rw [htop]; exact Subgroup.mem_top w
        exact (mem_fixV.mp hw) z hz
      rw [hz1, Subgroup.mem_bot]
    have h1 : Nat.card Z = 1 := by rw [hZbot, Subgroup.card_bot]
    exact h.hp.ne_one (hZcard ▸ h1)
  have hcard_lt : Nat.card ↥V₀ < Nat.card W := by
    have hle : Nat.card ↥V₀ ≤ Nat.card W :=
      Nat.card_le_card_of_injective (Subtype.val : ↥V₀ → W) Subtype.val_injective
    exact lt_of_le_of_ne hle fun heq => hV₀_ne_top (Subgroup.eq_top_of_card_eq V₀ heq)
  have ht_stab : t ∈ stabSub V₀ := by
    rw [mem_stabSub]
    intro u
    exact ⟨fun htu => by
      have h1 : t⁻¹ (t u) ∈ V₀ := htinvV₀mem (t u) htu
      simpa using h1, fun hu => htV₀mem u hu⟩
  let t' : MulAut ↥V₀ := resHom V₀ ⟨t, ht_stab⟩
  have hW' : ∀ w : ↥V₀, w ^ 2 = 1 := by
    intro w
    apply Subtype.ext
    simpa using h.hW (w : W)
  have htop : V₀ ⊔ fixV (Subgroup.zpowers t) = ⊤ :=
    top_le_iff.mp (hsup.ge.trans (sup_le_sup_left hV₁_fix V₀))
  have ht' : orderOf t' = 2 := by
    rw [show t' = resHom V₀ ⟨t, ht_stab⟩ from rfl, orderOf_resHom_eq ht_stab htop]
    exact h.ht
  have hrk_res : rk ↥(commSub ⊤ (Subgroup.zpowers t')) =
      rk ↥(commSub V₀ (Subgroup.zpowers t)) := by
    rw [show t' = resHom V₀ ⟨t, ht_stab⟩ from rfl, ← commV_eq_commSub]
    exact rk_commV_resHom ht_stab (fun x hx w hw => htV₀ x hx w hw)
  have hcommTop : commSub ⊤ (Subgroup.zpowers t) = commSub V₀ (Subgroup.zpowers t) := by
    rw [← hsup, commSub_sup_left, hV₁def, h0, sup_bot_eq]
  have hrk' : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤ 3 := by
    rw [hrk_res, ← hcommTop]
    exact h.hrk
  have hPstab : P ≤ stabSub V₀ := by
    intro x hx
    rw [mem_stabSub]
    intro u
    exact ⟨fun hxu => by
      have h1 : x⁻¹ (x u) ∈ V₀ := hPV₀ x⁻¹ (P.inv_mem hx) (x u) hxu
      simpa using h1, fun hu => hPV₀ x hx u hu⟩
  let φ : ↥P →* MulAut ↥V₀ := (resHom V₀).comp (Subgroup.inclusion hPstab)
  have hrange : φ.range = autSub P V₀ := by
    rw [show φ = (resHom V₀).comp (Subgroup.inclusion hPstab) from rfl,
      MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hP' : IsPGroup p ↥(autSub P V₀) := by
    have htopP : IsPGroup p ↥(⊤ : Subgroup ↥P) := h.hP.of_equiv Subgroup.topEquiv.symm
    have h1 := htopP.map φ
    rw [← MonoidHom.range_eq_map, hrange] at h1
    exact h1
  set Q : Subgroup (MulAut W) := P ⊓ centSub V₀ with hQdef
  have hker : ∀ g : ↥P, g ∈ φ.ker ↔ (g : MulAut W) ∈ Q := by
    intro g
    rw [MonoidHom.mem_ker, hQdef, Subgroup.mem_inf]
    constructor
    · intro hg
      refine ⟨g.2, ?_⟩
      rw [mem_centSub]
      intro u hu
      have h1 := congrArg (fun ψ : MulAut ↥V₀ => ((ψ ⟨u, hu⟩ : ↥V₀) : W)) hg
      simpa [φ, resHom_apply] using h1
    · rintro ⟨_, hcent⟩
      have h2 : Subgroup.inclusion hPstab g ∈ (resHom V₀).ker := by
        rw [ker_resHom, Subgroup.mem_subgroupOf]
        exact hcent
      rw [show φ = (resHom V₀).comp (Subgroup.inclusion hPstab) from rfl,
        MonoidHom.comp_apply, ← MonoidHom.mem_ker]
      exact h2
  have hQcentral : ∀ q ∈ Q, t * q * t⁻¹ = q := by
    intro q hq
    have hqV₀ : ∀ a ∈ V₀, q a = a := mem_centSub.mp hq.2
    have hqV₁ : ∀ b ∈ V₁, q b ∈ V₁ := fun b hb => hPV₁ q hq.1 b hb
    ext w
    have hw : w ∈ V₀ ⊔ V₁ := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    calc (t * q * t⁻¹) (a * b) = t (q (t⁻¹ (a * b))) := by simp [MulAut.mul_apply]
      _ = t (q (t⁻¹ a * t⁻¹ b)) := by rw [map_mul]
      _ = t (q (t⁻¹ a) * q (t⁻¹ b)) := by rw [map_mul]
      _ = t (t⁻¹ a * q b) := by
            rw [hqV₀ (t⁻¹ a) (htinvV₀mem a ha), htinvV₁triv b hb]
      _ = t (t⁻¹ a) * t (q b) := by rw [map_mul]
      _ = a * q b := by rw [MulAut.apply_inv_self, htV₁triv (q b) (hqV₁ b hb)]
      _ = q a * q b := by rw [hqV₀ a ha]
      _ = q (a * b) := by rw [map_mul]
  have hne' : autSub P V₀ ≠ ⊥ := by
    intro hbot
    have hle : P ≤ centSub V₀ := by
      intro g hg
      have hmem : (⟨g, hg⟩ : ↥P) ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        have h1 : φ ⟨g, hg⟩ ∈ φ.range := MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, rfl⟩
        rw [hrange, hbot] at h1
        exact Subgroup.mem_bot.mp h1
      exact ((hker ⟨g, hg⟩).mp hmem).2
    have hcomm : ∀ y ∈ P, t * y * t⁻¹ = y := fun y hy => hQcentral y ⟨hy, hle hy⟩
    have hcent : P ≤ Subgroup.centralizer (Subgroup.zpowers t) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
      have hty : Commute t y := by
        rw [commute_iff_eq]
        calc t * y = t * y * t⁻¹ * t := by group
          _ = y * t := by rw [hcomm y hy]
      rw [← hk]
      exact (hty.zpow_left k).eq
    have hPbot : ⁅P, Subgroup.zpowers t⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
    rw [h.hc] at hPbot
    exact h.hne hPbot
  have hn' : ∀ x ∈ autSub P V₀, t' * x * t'⁻¹ ∈ autSub P V₀ := by
    intro x hx
    obtain ⟨q, hqX, hqx⟩ := mem_autSub.mp hx
    refine mem_autSub.mpr ⟨⟨t, ht_stab⟩ * q * ⟨t, ht_stab⟩⁻¹, ?_, ?_⟩
    · change t * (q : MulAut W) * t⁻¹ ∈ P
      exact h.hn _ hqX
    · simp only [map_mul, map_inv, hqx]
      rfl
  let G : Subgroup (MulAut W) := P ⊔ Subgroup.zpowers t
  have hPG : P ≤ G := le_sup_left
  have htG : t ∈ G := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hGV : G ≤ stabSub V₀ := sup_le hPstab (Subgroup.zpowers_le.mpr ht_stab)
  let σ : G →* MulAut ↥V₀ := (resHom V₀).comp (Subgroup.inclusion hGV)
  have hmapσ : (P.subgroupOf G).map σ = autSub P V₀ := by
    rw [show σ = (resHom V₀).comp (Subgroup.inclusion hGV) from rfl,
      ← Subgroup.map_map (K := P.subgroupOf G) (g := resHom V₀) (f := Subgroup.inclusion hGV),
      w16g_map_inclusion_subgroupOf hGV hPG]
    rfl
  have hzp : ((Subgroup.zpowers t).subgroupOf G).map σ = Subgroup.zpowers t' := by
    have h1 : (Subgroup.zpowers t).subgroupOf G = Subgroup.zpowers (⟨t, htG⟩ : G) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa using hn)⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    rw [h1, MonoidHom.map_zpowers]
    rfl
  have hcommG : ⁅P.subgroupOf G, (Subgroup.zpowers t).subgroupOf G⁆ = P.subgroupOf G := by
    rw [w16g_subgroupOf_commutator hPG (Subgroup.zpowers_le.mpr htG), h.hc]
  have hc' : ⁅autSub P V₀, Subgroup.zpowers t'⁆ = autSub P V₀ := by
    have hmap := Subgroup.map_commutator (P.subgroupOf G)
      ((Subgroup.zpowers t).subgroupOf G) σ
    rw [hcommG, hmapσ, hzp] at hmap
    exact hmap.symm
  have hgood' : 3 < p ∨ InducesTransvection t' ⊤ := by
    rcases h.hgood with hg | hg
    · exact Or.inl hg
    · refine Or.inr ⟨?_, ?_⟩
      · rw [mem_stabSub]; intro u; simp
      · rw [hrk_res, ← hcommTop]; exact hg.2
  have hcfg : InvCfg131 p t' (autSub P V₀) :=
    { hW := hW', ht := ht', hrk := hrk', hp := h.hp, hP := hP', hne := hne',
      hn := hn', hc := hc', hgood := hgood' }
  have hP'card : Nat.card ↥(autSub P V₀) = p := ih ↥V₀ t' (autSub P V₀) hcard_lt hcfg
  exact w16g_card_eq_prime_of_restriction h ht_stab hPstab φ hrange rfl hker hQcentral
    hne' hP'card hc'

theorem eq_seven_of_central_comm_ne_bot {p : ℕ} {t : MulAut W} {P : Subgroup (MulAut W)}
    (h : InvCfg131 p t P) {Z : Subgroup (MulAut W)} (hZP : Z ≤ P)
    (hZc : ∀ z ∈ Z, ∀ y ∈ P, y * z = z * y) (hZ : IsElemAbelianOfRank p 1 ↥Z)
    (hZt : ∀ z ∈ Z, t * z * t⁻¹ = z)
    (hS : commSub (commSub ⊤ Z) (Subgroup.zpowers t) ≠ ⊥) : p = 7 := by
  haveI : Fact p.Prime := ⟨h.hp⟩
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at this
    exact this
  have hp2 : p ≠ 2 := by
    intro hp2
    exact h.hne (eq_bot_of_isPGroup_two_of_comm_eq_self htt (hp2 ▸ h.hP) h.hn h.hc)
  have hZcard : Nat.card Z = p := (w16g_isElemAbelianOfRank_one_iff h.hp).mp hZ
  have hZp : IsPGroup p ↥Z := IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
  have hZodd : Odd (Nat.card Z) := by rw [hZcard]; exact h.hp.odd_of_ne_two hp2
  have hZZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b * a⁻¹ ∈ Z := by
    intro a ha b hb
    have hcomm := (w16g_isElemAbelianOfRank_comm_pow hZ).1
    have : a * b = b * a := congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [this, mul_assoc, mul_inv_cancel, mul_one]
    exact hb
  have hM1 : StableUnder Z (commSub ⊤ Z) :=
    stableUnder_commSub (H := Z) (X := Z) hZZ (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
  have hzt : ∀ z ∈ Z, z * t * z⁻¹ = t := by
    intro z hz
    have h1 : t * z = z * t := by
      have h2 := hZt z hz
      rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right htt] at h2
      calc t * z = t * z * (t * t) := by rw [htt, mul_one]
        _ = t * z * t * t := by group
        _ = z * t := by rw [h2]
    rw [← h1]; group
  have hZn : ∀ z ∈ Z, ∀ x ∈ Subgroup.zpowers t, z * x * z⁻¹ ∈ Subgroup.zpowers t := by
    intro z hz x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hk : z * t ^ k * z⁻¹ = (z * t * z⁻¹) ^ k := by
      rw [show z * t ^ k * z⁻¹ = MulAut.conj z (t ^ k) from (MulAut.conj_apply z _).symm,
        map_zpow, MulAut.conj_apply]
    rw [hk, hzt z hz]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hM2 : StableUnder Z (commSub (commSub ⊤ Z) (Subgroup.zpowers t)) :=
    stableUnder_commSub (H := Z) (X := Subgroup.zpowers t) hZn hM1
  have hZconj : ∀ x ∈ Subgroup.zpowers t, ∀ z ∈ Z, x * z * x⁻¹ ∈ Z := by
    intro x hx z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : Commute t z := by
      rw [commute_iff_eq]
      have h2 := hZt z hz
      rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right htt] at h2
      calc t * z = t * z * (t * t) := by rw [htt, mul_one]
        _ = t * z * t * t := by group
        _ = z * t := by rw [h2]
    have h2 : Commute (t ^ k) z := h1.zpow_left k
    rw [h2.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact hz
  have hMt : StableUnder (Subgroup.zpowers t) (commSub ⊤ Z) :=
    stableUnder_commSub (H := Subgroup.zpowers t) (X := Z) hZconj (M := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _)
  have hSZ : commSub (commSub ⊤ Z) (Subgroup.zpowers t) ≤ commSub ⊤ Z :=
    commSub_le_of_invariant (fun x hx w hw => hMt x hx w hw)
  have hfix : commSub (commSub ⊤ Z) (Subgroup.zpowers t) ⊓ fixV Z = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have h3 : w ∈ fixV Z ⊓ commSub ⊤ Z := ⟨hw.2, hSZ hw.1⟩
    rw [CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' h.hW hZodd] at h3
    exact h3
  have hdvd : dParam p ∣ rk ↥(commSub (commSub ⊤ Z) (Subgroup.zpowers t)) :=
    CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot h.hW hZp hM2 hfix
  have hrkS : rk ↥(commSub (commSub ⊤ Z) (Subgroup.zpowers t)) ≤ 3 :=
    le_trans (rk_mono (commSub_mono le_top le_rfl)) h.hrk
  have hdpos : 0 < rk ↥(commSub (commSub ⊤ Z) (Subgroup.zpowers t)) := by
    rw [Nat.pos_iff_ne_zero, Ne, rk_eq_zero_iff h.hW]
    exact hS
  have hdle : dParam p ≤ 3 := le_trans (Nat.le_of_dvd hdpos hdvd) hrkS
  have hdP : dParam p = orderOf (2 : ZMod p) := rfl
  have hdne1 : dParam p ≠ 1 := by
    intro h1
    have h2 : orderOf (2 : ZMod p) = 1 := hdP ▸ h1
    have h3 : (2 : ZMod p) = 1 := orderOf_eq_one_iff.mp h2
    have h5 : (2 : ZMod p) - 1 = 0 := by rw [h3, sub_self]
    have h6 : ((1 : ℕ) : ZMod p) = 0 := by
      have h7 : (2 : ZMod p) - 1 = ((1 : ℕ) : ZMod p) := by norm_num
      rwa [h7] at h5
    exact h.hp.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 p).mp h6)
  have hdppos : 0 < dParam p := by
    rcases Nat.eq_zero_or_pos (dParam p) with h0 | hpos
    · rw [h0] at hdvd
      simp at hdvd
      omega
    · exact hpos
  have hd23 : dParam p = 2 ∨ dParam p = 3 := by omega
  rcases hd23 with hd2 | hd3
  · exfalso
    have hp3 : p = 3 := by
      have hpow : (2 : ZMod p) ^ 2 = 1 := by
        have h := pow_orderOf_eq_one (2 : ZMod p)
        rwa [hdP.symm.trans hd2] at h
      have h4 : ((4 : ℕ) : ZMod p) = 1 := by
        have h7 : (2 : ZMod p) ^ 2 = ((4 : ℕ) : ZMod p) := by norm_num
        rwa [h7] at hpow
      have h5 : ((4 : ℕ) : ZMod p) - 1 = 0 := by rw [h4, sub_self]
      have h6 : ((4 : ℕ) : ZMod p) - 1 = ((3 : ℕ) : ZMod p) := by norm_num
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by rwa [h6] at h5
      exact (Nat.prime_dvd_prime_iff_eq h.hp Nat.prime_three).mp
        ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
    subst hp3
    rcases h.hgood with hg | hg
    · omega
    · have h1 : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 1 := hg.2
      have hrkS1 : rk ↥(commSub (commSub ⊤ Z) (Subgroup.zpowers t)) ≤ 1 := by
        calc rk ↥(commSub (commSub ⊤ Z) (Subgroup.zpowers t))
            ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := rk_mono (commSub_mono le_top le_rfl)
          _ = 1 := h1
      rw [hd2] at hdvd
      obtain ⟨m, hm⟩ := hdvd
      omega
  · have hp7 : p = 7 := by
      have hpow : (2 : ZMod p) ^ 3 = 1 := by
        have h := pow_orderOf_eq_one (2 : ZMod p)
        rwa [hdP.symm.trans hd3] at h
      have h4 : ((8 : ℕ) : ZMod p) = 1 := by
        have h7 : (2 : ZMod p) ^ 3 = ((8 : ℕ) : ZMod p) := by norm_num
        rwa [h7] at hpow
      have h5 : ((8 : ℕ) : ZMod p) - 1 = 0 := by rw [h4, sub_self]
      have h6 : ((8 : ℕ) : ZMod p) - 1 = ((7 : ℕ) : ZMod p) := by norm_num
      have h3 : ((7 : ℕ) : ZMod p) = 0 := by rwa [h6] at h5
      exact (Nat.prime_dvd_prime_iff_eq h.hp Nat.prime_seven).mp
        ((ZMod.natCast_eq_zero_iff 7 p).mp h3)
    exact hp7


end CFSG.LocalAnalysis.WeakClosure81
