module

public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.RankThree.PartTwo.Sec13.Item13GL
import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha
import CFSG.RankThree.PartTwo.Sec13.Ronan138SRefl
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec4.Item423Res5Proof
import CFSG.RankThree.PartTwo.Sec13.Ronan138SSN
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SP

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Frame

theorem zpowers_eq_of_mem {a b : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1)
    (hb1 : b ≠ 1) (hab : a ∈ Subgroup.zpowers b) : Subgroup.zpowers a = Subgroup.zpowers b :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hab)
    (by rw [card_zpowers_of_pow_three ha3 ha1, card_zpowers_of_pow_three hb3 hb1])

structure Frame138 (A L E F : Subgroup G) (c x y t : G) : Prop where
  hH : Hyp138 A c L E
  hF : IsF138N L E F
  hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E)
  hxE : x ∈ E
  hyF : y ∈ F
  frame : HeisFrame (E ⊓ F) x y
  hd1 : ⁅x, y⁆ ≠ 1
  hdL : ⁅x, y⁆ ∈ L
  hcF : c ∈ F
  h81 : Nat.card (E ⊔ F : Subgroup G) = 81
  h9 : Nat.card (E ⊓ F : Subgroup G) = 9
  hEL : E ⊓ L = Subgroup.zpowers ⁅x, y⁆
  htL : t ∈ L
  htE : t ∈ Subgroup.normalizer (E : Set G)
  htd : t * ⁅x, y⁆ * t⁻¹ = ⁅x, y⁆⁻¹
  htc : t * c = c * t

theorem exists_frame138_t {A L E F : Subgroup G} {c : G} (hH : Hyp138 A c L E)
    (hF : IsF138N L E F) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E)) :
    ∃ x y t : G, Frame138 A L E F c x y t := by
  obtain ⟨x, y, hxE, hyF, hframe, hd1, hdL, hcF, h81, h9, hELd⟩ := exists_frame138 hH hF hPGL
  obtain ⟨d', t, hd'E, hd'L, hd'1, htL, htN, htd'⟩ := exists_inverting_of_hyp138 hH
  have hH' := hH
  obtain ⟨h, -, -, hE3, -, -, -, -, -⟩ := hH'
  set d := ⁅x, y⁆ with hd
  have hd3 : d ^ 3 = 1 := hframe.comm_pow_three
  have hd'mem : d' ∈ Subgroup.zpowers d := hELd ▸ Subgroup.mem_inf.mpr ⟨hd'E, hd'L⟩
  have htd : t * d * t⁻¹ = d⁻¹ := by
    have hd'3 : d' ^ 3 = 1 := hE3.2 d' hd'E
    have hdd' : d ∈ Subgroup.zpowers d' := by
      have heq : Subgroup.zpowers d' = Subgroup.zpowers d := Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr hd'mem)
        (by rw [card_zpowers_of_pow_three hd3 hd1, card_zpowers_of_pow_three hd'3 hd'1])
      rw [heq]
      exact Subgroup.mem_zpowers d
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hdd'
    rw [← hm, ← conj_zpow, htd', inv_zpow]
  have htc : t * c = c * t :=
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer htL)
  exact ⟨x, y, t, hH, hF, hPGL, hxE, hyF, hframe, hd1, hdL, hcF, h81, h9, hELd, htL, htN, htd,
    htc⟩

namespace Frame138

variable {A L E F : Subgroup G} {c x y t : G} (h : Frame138 A L E F c x y t)
include h

theorem hE3 : ∀ a ∈ E, a ^ 3 = 1 := h.hH.2.2.2.1.2
theorem hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.hH.2.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
theorem hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.hF.1.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
theorem hE27 : Nat.card E = 27 := h.hH.2.2.2.2.1
theorem hF27 : Nat.card F = 27 := h.hF.1.2.2.1
theorem hFN : F ≤ Subgroup.normalizer (E : Set G) := h.hF.1.2.2.2.2
theorem hcE : c ∈ E := h.hH.2.2.1
theorem hc1 : c ≠ 1 := h.hH.1.ne_one
theorem hc3 : c ^ 3 = 1 := h.hE3 c h.hcE
theorem hd3 : ⁅x, y⁆ ^ 3 = 1 := h.frame.comm_pow_three
theorem hdZ : ⁅x, y⁆ ∈ E ⊓ F := h.frame.comm_mem
theorem hdE : ⁅x, y⁆ ∈ E := (Subgroup.mem_inf.mp h.hdZ).1
theorem hcZ : c ∈ E ⊓ F := Subgroup.mem_inf.mpr ⟨h.hcE, h.hcF⟩

theorem hcL : c ∉ L := by
  obtain ⟨hD, -, -, -, -, -, -, -, hC⟩ := h.hH
  obtain ⟨π, p, f, Kf, _, hKf, hq, φ, -⟩ := hC
  have hL := hD.mem_thetaComponentsAt
  have hq2 := two_lt_of_mulEquiv (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL) hKf hq φ
  exact Sec13.not_mem_of_center_eq_bot hD
    (Sec13.center_eq_bot_of_mulEquiv φ (Sec13.center_projImage_slPi hKf hq hq2))

theorem hdc : ⁅x, y⁆ ∉ Subgroup.zpowers c := by
  intro hdc
  have heq := zpowers_eq_of_mem h.hd3 h.hd1 h.hc3 h.hc1 hdc
  apply h.hcL
  have hc : c ∈ Subgroup.zpowers ⁅x, y⁆ := heq ▸ Subgroup.mem_zpowers c
  exact Subgroup.zpowers_le.mpr h.hdL hc

theorem hZgen : ∀ z ∈ E ⊓ F, ∃ α β : ℕ, z = c ^ α * ⁅x, y⁆ ^ β := by
  intro z hz
  have hcd : Subgroup.zpowers c ⊓ Subgroup.zpowers ⁅x, y⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [← zpowers_inf_eq_bot h.hc3 h.hcL]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw).1,
      Subgroup.zpowers_le.mpr h.hdL (Subgroup.mem_inf.mp hw).2⟩
  exact exists_pow_mul_pow_of_card h.hcZ h.hdZ (h.hEab c h.hcE _ h.hdE) h.hc3 h.hc1 h.hd3 h.hd1
    hcd h.h9 hz

end Frame138

end Frame

section Omega

theorem range_conj_le_autThetaQuot {c : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c) :
    (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut _).range ≤
      Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L := by
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  rintro _ ⟨z, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
  refine Sec4.mem_autThetaQuot_iff.mpr ⟨l, L.le_normalizer l.2,
    centralizer_le_normalizer_zpowers c (hLc l.2), ?_⟩
  ext q
  induction q using QuotientGroup.induction_on with
  | H m =>
    change (((L.normalizerMonoidHom ⟨(l : G), L.le_normalizer l.2⟩ m : L)) : ↥L ⧸ θ) =
      (l : ↥L ⧸ θ) * (m : ↥L ⧸ θ) * (l : ↥L ⧸ θ)⁻¹
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

theorem mem_partTwoF_of_hyp138 {A L E : Subgroup G} {c : G} (hH : Hyp138 A c L E) :
    E ∈ partTwoF G ∧ E ∉ partTwoT G := by
  obtain ⟨h, -, -, -, -, -, -, hST, -⟩ := hH
  have hXE : E ∈ partTwoE G ∧ E ∉ partTwoT G := by
    rcases hST with hS | hT
    · exact ⟨hS.1, hS.2.1⟩
    · exact ⟨hT.1, hT.2.1⟩
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  exact ⟨hFE ▸ hXE.1, hXE.2⟩

theorem zpowers_not_mem_omegaA (hsetAt : Item13SetupAt) {A L E : Subgroup G} {c : G}
    (hH : Hyp138 A c L E) {d : G} (hdE : d ∈ E) (hdL : d ∈ L) (hdc : d ∉ Subgroup.zpowers c) :
    Subgroup.zpowers c ∉ omegaA E := by
  intro hcΩ
  have hXF := mem_partTwoF_of_hyp138 hH
  obtain ⟨h, -, hcE, hE3, -, hEN, -, -, hC⟩ := hH
  obtain ⟨K, hK⟩ := hsetAt G h.toPartTwoStanding h.partTwoS_eq E hXF.1 hXF.2 c hcΩ
  have hL := h.mem_thetaComponentsAt
  have hEc : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun a ha =>
    centralizer_le_normalizer_zpowers c (Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hE3.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcE⟩)))
  by_cases hKL : K = L
  · subst hKL
    apply hK.2.2.2
    obtain ⟨π, p, f, Kf, _, hKf, hq, e, D, hD, h1, h2⟩ := hC
    exact Sec4.k423TypeCAlpha_holds _ (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL) π p f Kf
      hKf hq e D hD _ _ (range_conj_le_autThetaQuot hL) (autThetaQuot_mono hEc K) h1 h2
  · have hdK : d ∈ Sec4.thetaQuotCentralizer K :=
      mem_thetaQuotCentralizer_of_ne_mem_thetaComponentsAt hL hK.1 (Ne.symm hKL) hdL
        (hK.2.1 hdE)
    have hCE := sectionCentralizer_eq_inf hK.2.1
    rw [hK.2.2.1] at hCE
    have hd' : d ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hdE, hdK⟩
    rw [← hCE] at hd'
    exact hdc hd'

end Omega

section Lines

variable {E F : Subgroup G} {x y : G}

theorem conj_y_eq_of_not_mem (hframe : HeisFrame (E ⊓ F) x y) (hxE : x ∈ E) (hyF : y ∈ F)
    (hE27 : Nat.card E = 27) (hF27 : Nat.card F = 27) (h9 : Nat.card (E ⊓ F : Subgroup G) = 9)
    (hFN : F ≤ Subgroup.normalizer (E : Set G)) (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    {a : G} (haE : a ∈ E) (haZ : a ∉ F) :
    ∃ k : ℕ, ¬ 3 ∣ k ∧ y * a * y⁻¹ = a * ⁅x, y⁆ ^ k := by
  obtain ⟨i, z, hz, rfl⟩ := isNF_of_mem_left hframe hxE hE27 h9 haE
  have hi : ¬ 3 ∣ i := by
    intro hi
    apply haZ
    have hnf : IsNF (E ⊓ F) x y (x ^ i * y ^ 0 * z) i 0 := ⟨z, hz, rfl⟩
    refine (mem_right_iff hframe hyF hF27 h9 hnf).mpr ?_
    obtain ⟨m, rfl⟩ := hi
    push_cast
    rw [show ((3 : ZMod 3)) = 0 from rfl, zero_mul]
  have hdx : Commute ⁅x, y⁆ x := hframe.zx _ hframe.comm_mem
  have hyx : y * x * y⁻¹ = x * ⁅x, y⁆ ^ 2 := by
    have hd3 : ⁅x, y⁆ ^ 3 = 1 := hframe.comm_pow_three
    have h1 : ⁅x, y⁆⁻¹ = ⁅x, y⁆ ^ 2 := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, hd3]
    have h2 : y * x * y⁻¹ = ⁅x, y⁆⁻¹ * x := by
      rw [commutatorElement_def]
      group
    rw [h2, h1, (hdx.pow_left 2).eq]
  have hyz : y * z * y⁻¹ = z := by
    rw [(hframe.zy z hz).symm.eq, mul_inv_cancel_right]
  refine ⟨2 * i, fun h3 => hi ?_, ?_⟩
  · exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)
  · have hdz : Commute ⁅x, y⁆ z := (hframe.zz _ hframe.comm_mem z hz)
    rw [pow_zero, mul_one, show y * (x ^ i * z) * y⁻¹ = (y * x * y⁻¹) ^ i * (y * z * y⁻¹) by
      rw [conj_pow]; group, hyx, hyz, (hdx.pow_left 2).symm.mul_pow i, ← pow_mul, mul_assoc,
      (hdz.pow_left _).eq, ← mul_assoc]

theorem three_dvd_or_of_conj_mem {c d t : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hd3 : d ^ 3 = 1)
    (hd1 : d ≠ 1) (hcd : c * d = d * c) (htc : t * c * t⁻¹ = c) (htd : t * d * t⁻¹ = d⁻¹)
    {α β : ℕ} (h1 : c ^ α * d ^ β ≠ 1)
    (hta : t * (c ^ α * d ^ β) * t⁻¹ ∈ Subgroup.zpowers (c ^ α * d ^ β)) : 3 ∣ α ∨ 3 ∣ β := by
  have hcdc : Commute c d := hcd
  have ha3 : (c ^ α * d ^ β) ^ 3 = 1 := by
    rw [(hcdc.pow_pow α β).mul_pow, ← pow_mul, ← pow_mul, mul_comm α, mul_comm β, pow_mul,
      pow_mul, hc3, hd3, one_pow, one_pow, one_mul]
  have hconj : t * (c ^ α * d ^ β) * t⁻¹ = c ^ α * (d⁻¹) ^ β := by
    rw [show t * (c ^ α * d ^ β) * t⁻¹ = (t * c * t⁻¹) ^ α * (t * d * t⁻¹) ^ β by
      rw [conj_pow, conj_pow]; group, htc, htd]
  have hordc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hordd : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hdinv : (d⁻¹) ^ β = d ^ (2 * β) := by
    rw [inv_pow, eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_add,
      show 2 * β + β = 3 * β by ring, pow_mul, hd3, one_pow]
  rcases eq_of_mem_zpowers_of_pow_three ha3 hta with h | h | h
  · exact absurd (by simpa [mul_inv_eq_one] using h) h1
  ·
    right
    rw [hconj, hdinv] at h
    have h2 : d ^ (2 * β) = d ^ β := mul_left_cancel h
    rw [two_mul, pow_add] at h2
    have := orderOf_dvd_of_pow_eq_one (mul_eq_left.mp h2)
    rwa [hordd] at this
  ·
    left
    rw [hconj, hdinv, (hcdc.pow_pow α β).mul_pow, ← pow_mul, ← pow_mul, mul_comm α 2,
      mul_comm β 2] at h
    have h2 : c ^ α = c ^ (2 * α) := mul_right_cancel h
    rw [two_mul, pow_add] at h2
    have := orderOf_dvd_of_pow_eq_one (mul_eq_left.mp h2.symm)
    rwa [hordc] at this

theorem zpowers_eq_or_eq_of_normalizes (hframe : HeisFrame (E ⊓ F) x y) (hd1 : ⁅x, y⁆ ≠ 1)
    (hxE : x ∈ E) (hyF : y ∈ F) (hE27 : Nat.card E = 27) (hF27 : Nat.card F = 27)
    (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) (hFN : F ≤ Subgroup.normalizer (E : Set G))
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    {c t : G} (hc1 : c ≠ 1) (hcE : c ∈ E)
    (hZgen : ∀ z ∈ E ⊓ F, ∃ α β : ℕ, z = c ^ α * ⁅x, y⁆ ^ β)
    (htc : t * c * t⁻¹ = c) (htd : t * ⁅x, y⁆ * t⁻¹ = ⁅x, y⁆⁻¹)
    {a : G} (haE : a ∈ E) (ha1 : a ≠ 1)
    (hya : y * a * y⁻¹ ∈ Subgroup.zpowers a) (hta : t * a * t⁻¹ ∈ Subgroup.zpowers a) :
    Subgroup.zpowers a = Subgroup.zpowers c ∨ Subgroup.zpowers a = Subgroup.zpowers ⁅x, y⁆ := by
  set d := ⁅x, y⁆ with hd
  have hd3 : d ^ 3 = 1 := hframe.comm_pow_three
  have hdZ : d ∈ E ⊓ F := hframe.comm_mem
  have ha3 : a ^ 3 = 1 := hE3 a haE
  have hc3 : c ^ 3 = 1 := hE3 c hcE
  have haF : a ∈ F := by
    by_contra haF
    obtain ⟨k, hk, hyk⟩ := conj_y_eq_of_not_mem hframe hxE hyF hE27 hF27 h9 hFN hEab haE haF
    have hdk : d ^ k ∈ Subgroup.zpowers a := by
      have := (Subgroup.zpowers a).mul_mem (inv_mem (Subgroup.mem_zpowers a)) (hyk ▸ hya)
      rwa [inv_mul_cancel_left] at this
    have hda : d ∈ Subgroup.zpowers a :=
      Subgroup.zpowers_le.mpr hdk (mem_zpowers_pow_of_not_dvd hd3 hk)
    have heq := zpowers_eq_of_mem hd3 hd1 ha3 ha1 hda
    apply haF
    have haD : a ∈ Subgroup.zpowers d := heq ▸ Subgroup.mem_zpowers a
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hdZ).2 haD
  obtain ⟨α, β, rfl⟩ := hZgen _ (Subgroup.mem_inf.mpr ⟨haE, haF⟩)
  have hcd : c * d = d * c := hEab c hcE d (Subgroup.mem_inf.mp hdZ).1
  rcases three_dvd_or_of_conj_mem hc3 hc1 hd3 hd1 hcd htc htd ha1 hta with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · right
    rw [pow_mul, hc3, one_pow, one_mul] at ha1 ha3 ⊢
    exact zpowers_eq_of_mem ha3 ha1 hd3 hd1 (pow_mem (Subgroup.mem_zpowers d) _)
  · left
    rw [pow_mul, hd3, one_pow, mul_one] at ha1 ha3 ⊢
    exact zpowers_eq_of_mem ha3 ha1 hc3 hc1 (pow_mem (Subgroup.mem_zpowers c) _)

end Lines

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
