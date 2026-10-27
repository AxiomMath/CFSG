module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenSeven
public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenNoExotic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_eq_of_mem_sup_of_commute_elementwise {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  have key : ∀ a ∈ A, ∀ h ∈ B, a * h * a⁻¹ ∈ B := by
    intro a ha h hh
    rw [hAB a ha h hh, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have hle : A ≤ normalizer (B : Set G) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key a ha h hh, fun hh => ?_⟩
    have h2 := key a⁻¹ (A.inv_mem ha) _ hh
    have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rwa [e] at h2
  have := Subgroup.coe_mul_of_left_le_normalizer_right A B hle
  have hg' : g ∈ ((A ⊔ B : Subgroup G) : Set G) := hg
  rw [this] at hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := hg'
  exact ⟨a, ha, b, hb, rfl⟩

theorem eleven11_mem_mul_of_central {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) {z : G} (hzQ : z ∈ Q)
    (hz : ∀ q ∈ Q, q * z = z * q) :
    ∃ l ∈ ⁅V, X⁆, ∃ p ∈ Q ⊓ Subgroup.centralizer (L : Set G), z = l * p := by
  obtain ⟨t, ht, ht0⟩ := eleven11_exists_elem hd h8
  have htL : t ∈ L := (Subgroup.mem_inf.1 ht).1
  have htQ : t ∈ Q := (Subgroup.mem_inf.1 ht).2
  have hzD : z ∈ Q ⊓ centralizerModCore L := by
    rw [← eleven11_cent_blockU_eq hd h8]
    refine Subgroup.mem_inf.2 ⟨hzQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hz w (eleven11_blockU_le_Q hd hw)
  obtain ⟨w, hw, p, hp, rfl⟩ := eleven11_exists_mul_of_mem_D hd h8 hzD
  have hpt : t * p = p * t :=
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hp).2 t htL
  have hwt : w ∈ blockU L ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hw, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : t * (w * p) = (w * p) * t := hz t htQ
    have h2 : (t * w) * p = (w * t) * p := by
      calc (t * w) * p = t * (w * p) := by rw [mul_assoc]
        _ = (w * p) * t := h1
        _ = w * (p * t) := by rw [mul_assoc]
        _ = w * (t * p) := by rw [hpt]
        _ = (w * t) * p := by rw [mul_assoc]
    exact (mul_right_cancel h2).symm
  rw [eleven11_blockU_inf_centralizer hd h8 ht ht0] at hwt
  obtain ⟨hle, -, -, -, -⟩ := eleven11_commutator_VX hd h8
  have hcomm : ∀ a ∈ ⁅V, X⁆, ∀ b ∈ blockZ L, a * b = b * a := fun a ha b hb =>
    eleven11_blockU_comm hd a (Subgroup.mem_inf.1 (hle ha)).2 b (blockZ_le_blockU L hb)
  obtain ⟨l, hl, z', hz', rfl⟩ := exists_mul_eq_of_mem_sup_of_commute_elementwise hcomm hwt
  have hz'P : z' ∈ Q ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_inf.2 ⟨eleven11_blockU_le_Q hd (blockZ_le_blockU L hz'), hz'.2⟩
  exact ⟨l, hl, z' * p, (Q ⊓ Subgroup.centralizer (L : Set G)).mul_mem hz'P hp, by group⟩

theorem eleven11_central_involution_mem
    {M V Q U L X : Subgroup G} (hd : Eleven11Data M V Q U L X)
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3) (h8 : Nat.card V = 8) {z : G}
    (hzQ : z ∈ Q) (hz : ∀ q ∈ Q, q * z = z * q) (hz2 : z ^ 2 = 1) : z ∈ V := by
  classical
  by_contra hzV
  have hz1 : z ≠ 1 := fun h => hzV (h ▸ V.one_mem)
  have hVQ : V ≤ Q := hd.setting.V_le_Q
  have hVC : V ≤ Subgroup.centralizer (Q : Set G) :=
    eleven_a (hd.setting.sylowQ.1.trans inf_le_right)
  have hzC : Subgroup.zpowers z ≤ Subgroup.centralizer (Q : Set G) := by
    refine Subgroup.zpowers_le.2 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hz q hq
  have hEC : V ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer (Q : Set G) := sup_le hVC hzC
  have hEQ : V ⊔ Subgroup.zpowers z ≤ Q := sup_le hVQ (Subgroup.zpowers_le.2 hzQ)
  have hEcomm : ∀ x ∈ V ⊔ Subgroup.zpowers z, ∀ y ∈ V ⊔ Subgroup.zpowers z, x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.1 (hEC hx) y (hEQ hy)).symm
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hEcard : Nat.card ↥(V ⊔ Subgroup.zpowers z) = 16 := by
    have hcomm : ∀ a ∈ V, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := fun a ha b hb =>
      hEcomm a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb)
    have hmul := B2F.card_sup_mul_card_inf_of_commute hcomm
    have hbot : V ⊓ Subgroup.zpowers z = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxV, hxz⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxz
      have h1 : z ^ (n % 2) = z ^ n := by
        have := zpow_mod_orderOf z n
        rwa [hord] at this
      rcases Int.emod_two_eq_zero_or_one n with h | h
      · rw [h, zpow_zero] at h1
        rw [← h1]
        exact Subgroup.one_mem _
      · rw [h, zpow_one] at h1
        exact absurd (h1 ▸ hxV) hzV
    rw [hbot, Subgroup.card_bot, mul_one, h8, Nat.card_zpowers, hord] at hmul
    omega
  obtain ⟨A, L', X', hfam, hdist⟩ := eleven11_exists_family hd h21 h3 h8
  choose hd' h3' using hfam
  let K : Fin 7 → Subgroup G := fun i =>
    (V ⊔ Subgroup.zpowers z) ⊓ (Q ⊓ Subgroup.centralizer (L' i : Set G))
  have hK4 : ∀ i, Nat.card (K i) = 4 := by
    intro i
    obtain ⟨hle, hcard, -, -, hUl⟩ := eleven11_commutator_VX (hd' i) h8
    have hKE : K i ≤ V ⊔ Subgroup.zpowers z := inf_le_left
    have hlE : ⁅V, X' i⁆ ≤ V ⊔ Subgroup.zpowers z :=
      (hle.trans inf_le_left).trans le_sup_left
    have hbot : ⁅V, X' i⁆ ⊓ K i = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxl, hxK⟩ := Subgroup.mem_inf.1 hx
      have hxV : x ∈ V := (Subgroup.mem_inf.1 (hle hxl)).1
      have hxC : x ∈ Subgroup.centralizer (L' i : Set G) :=
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hxK).2).2
      have hxU : x ∈ A i := eleven11_inf_centralizer_le (hd' i) (Subgroup.mem_inf.2 ⟨hxV, hxC⟩)
      have : x ∈ A i ⊓ ⁅V, X' i⁆ := Subgroup.mem_inf.2 ⟨hxU, hxl⟩
      rw [hUl] at this
      exact (Subgroup.mem_bot.1 this ▸ Subgroup.one_mem _)
    have hsup : ⁅V, X' i⁆ ⊔ K i = V ⊔ Subgroup.zpowers z := by
      refine le_antisymm (sup_le hlE hKE) ?_
      intro e he
      have heQ : e ∈ Q := hEQ he
      have hecent : ∀ q ∈ Q, q * e = e * q := fun q hq =>
        (Subgroup.mem_centralizer_iff.1 (hEC he) q hq)
      obtain ⟨l, hl, p, hp, rfl⟩ := eleven11_mem_mul_of_central (hd' i) h8 heQ hecent
      have hlV : l ∈ V := (Subgroup.mem_inf.1 (hle hl)).1
      have hpE : p ∈ V ⊔ Subgroup.zpowers z := by
        have := (V ⊔ Subgroup.zpowers z).mul_mem ((V ⊔ Subgroup.zpowers z).inv_mem
          (Subgroup.mem_sup_left hlV)) he
        simpa using this
      exact (⁅V, X' i⁆ ⊔ K i).mul_mem (Subgroup.mem_sup_left hl)
        (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hpE, hp⟩))
    have hcomm : ∀ a ∈ ⁅V, X' i⁆, ∀ b ∈ K i, a * b = b * a := fun a ha b hb =>
      hEcomm a (hlE ha) b (hKE hb)
    have hmul := B2F.card_sup_mul_card_inf_of_commute hcomm
    rw [hbot, Subgroup.card_bot, mul_one, hsup, hEcard, hcard] at hmul
    omega
  have hinf : ∀ i j, i ≠ j → K i ⊓ K j = ⊥ := by
    intro i j hij
    have := eleven11_cent_inf_cent_eq_bot (hd' i) (hd' j) h21 (h3' i) (h3' j) (hdist i j hij)
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxi, hxj⟩ := Subgroup.mem_inf.1 hx
    have : x ∈ (Q ⊓ Subgroup.centralizer (L' i : Set G)) ⊓
        (Q ⊓ Subgroup.centralizer (L' j : Set G)) :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxi).2, (Subgroup.mem_inf.1 hxj).2⟩
    rwa [‹(Q ⊓ Subgroup.centralizer (L' i : Set G)) ⊓
        (Q ⊓ Subgroup.centralizer (L' j : Set G)) = ⊥›] at this
  have hcount := card_add_mul_le_of_inf_eq (B := ⊥) (Q := V ⊔ Subgroup.zpowers z) (K := K)
    (b := 1) (k := 4) Subgroup.card_bot hK4 bot_le (fun i => bot_le) (fun i => inf_le_left) hinf
  rw [hEcard] at hcount
  simp at hcount

end CFSG.LocalAnalysis.WeakClosure81
