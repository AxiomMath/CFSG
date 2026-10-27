module

public import CFSG.RankThree.GF2n.Stroth80.Sec103ATools

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private def LineConj (w : G) (L Q Z : Subgroup G) : Set (G × G) :=
  {p : G × G | p.1 ∈ L ∧ p.2 ∈ Z ∧ ∃ k ∈ Q, k * w * k⁻¹ = w * p.1 * p.2}

private theorem line_centralizer_of_comm_ne_one {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {Y : Subgroup G} {w : G}
    (hs : Sit M Q Z Y w) {L : Subgroup G} (hLA : L ≤ Q ⊓ QB Y) (hline : M₀.IsLine L)
    {k a' : G} (hk : k ∈ Q) (ha' : a' ∈ L) (ha'1 : a' ≠ 1) (hcomm : k * a' = a' * k) :
    ∀ a ∈ L, k * a = a * k := by
  obtain ⟨e, -, he⟩ := hline
  have hLQ : L ≤ Q := hLA.trans inf_le_left
  have hLZ : L ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h : x ∈ Z ⊓ QB Y := ⟨hx.2, (hLA hx.1).2⟩
    rwa [Z_inf_QB_eq_bot hs (smith_1_12 hs), Subgroup.mem_bot] at h
  have ha'Z : a' ∉ Z := fun h => ha'1 (by
    have h2 : a' ∈ L ⊓ Z := ⟨ha', h⟩
    rwa [hLZ, Subgroup.mem_bot] at h2)
  obtain ⟨s, hs'⟩ := (he _).mp (M₀.pi_mem_img ha' (hLQ ha'))
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hs'
    exact ha'Z ((M₀.π_ker a' (hLQ ha')).mp hs')
  have hB : M₀.B (M₀.π k) (M₀.π a') = 0 :=
    (Tim79.QuadModel.comm_iff_B M₀ hD.reg hk (hLQ ha')).mp hcomm
  rw [hs', map_smul, smul_eq_mul] at hB
  have hBe : M₀.B (M₀.π k) e = 0 := (mul_eq_zero.mp hB).resolve_left hs0
  have hkC : k ∈ Subgroup.centralizer (L : Set G) :=
    (Tim79.QuadModel.centralizer_iff hD.reg hLQ he hk).mpr hBe
  exact fun a ha => (Subgroup.mem_centralizer_iff.mp hkC a ha).symm

private theorem lineConj_one (w : G) (L Q Z : Subgroup G) :
    ((1, 1) : G × G) ∈ LineConj w L Q Z :=
  ⟨L.one_mem, Z.one_mem, 1, Q.one_mem, by
    show (1 : G) * w * 1⁻¹ = w * 1 * 1
    group⟩

private theorem lineConj_mul {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {Y : Subgroup G} {w : G}
    (hs : Sit M Q Z Y w) {L : Subgroup G} (hLA : L ≤ Q ⊓ QB Y) (hline : M₀.IsLine L)
    {p q : G × G} (hp : p ∈ LineConj w L Q Z) (hq : q ∈ LineConj w L Q Z) :
    p * q ∈ LineConj w L Q Z := by
  obtain ⟨hpL, hpZ, k, hkQ, hk⟩ := hp
  obtain ⟨hqL, hqZ, k', hk'Q, hk'⟩ := hq
  have hpQ : p.1 ∈ Q ⊓ QB Y := hLA hpL
  have hqQ : q.1 ∈ Q ⊓ QB Y := hLA hqL
  have hk'q : k' * q.1 = q.1 * k' := Sit.comm_of_conj_eq_mul hs hk'Q hqQ hqZ hk'
  have hz : ∀ z ∈ Z, ∀ a ∈ Q, z * a = a * z := fun z hz a ha => Z_central hs.hyp hz ha
  have hkz' : k * q.2 * k⁻¹ = q.2 := by rw [← hz q.2 hqZ k hkQ]; group
  have hk'z : k' * p.2 * k'⁻¹ = p.2 := by rw [← hz p.2 hpZ k' hk'Q]; group
  by_cases hq1 : q.1 = 1
  · refine ⟨L.mul_mem hpL hqL, Z.mul_mem hpZ hqZ, k * k', Q.mul_mem hkQ hk'Q, ?_⟩
    calc (k * k') * w * (k * k')⁻¹ = k * (k' * w * k'⁻¹) * k⁻¹ := by group
      _ = k * (w * q.1 * q.2) * k⁻¹ := by rw [hk']
      _ = k * (w * q.2) * k⁻¹ := by rw [hq1, mul_one]
      _ = (k * w * k⁻¹) * (k * q.2 * k⁻¹) := by group
      _ = (w * p.1 * p.2) * q.2 := by rw [hk, hkz']
      _ = w * (p.1 * q.1) * (p.2 * q.2) := by rw [hq1, mul_one]; group
  · have hk'L : ∀ a₀ ∈ L, k' * a₀ = a₀ * k' :=
      line_centralizer_of_comm_ne_one hD hs hLA hline hk'Q hqL hq1 hk'q
    have hk'p : k' * p.1 * k'⁻¹ = p.1 := by rw [hk'L p.1 hpL]; group
    refine ⟨L.mul_mem hpL hqL, Z.mul_mem hpZ hqZ, k' * k, Q.mul_mem hk'Q hkQ, ?_⟩
    calc (k' * k) * w * (k' * k)⁻¹ = k' * (k * w * k⁻¹) * k'⁻¹ := by group
      _ = k' * (w * p.1 * p.2) * k'⁻¹ := by rw [hk]
      _ = (k' * w * k'⁻¹) * (k' * p.1 * k'⁻¹) * (k' * p.2 * k'⁻¹) := by group
      _ = (w * q.1 * q.2) * p.1 * p.2 := by rw [hk', hk'p, hk'z]
      _ = w * q.1 * (q.2 * p.1) * p.2 := by group
      _ = w * q.1 * (p.1 * q.2) * p.2 := by rw [hz q.2 hqZ p.1 hpQ.1]
      _ = w * (q.1 * p.1) * (q.2 * p.2) := by group
      _ = w * (p.1 * q.1) * (p.2 * q.2) := by
          rw [← (smith_1_13 hs).2.2.2.2 p.1 hpQ q.1 ((smith_1_13 hs).2.2.2.1 hqQ),
            Z_central hs.hyp hqZ (hs.hyp.Z_normal.1 hpZ)]

private theorem lineConj_inv {Y : Subgroup G} {w : G} (hs : Sit M Q Z Y w) {L : Subgroup G}
    (hLA : L ≤ Q ⊓ QB Y) {p : G × G} (hp : p ∈ LineConj w L Q Z) :
    p⁻¹ ∈ LineConj w L Q Z := by
  obtain ⟨hpL, hpZ, k, hkQ, hk⟩ := hp
  have hpQ : p.1 ∈ Q ⊓ QB Y := hLA hpL
  have hka : k * p.1 = p.1 * k := Sit.comm_of_conj_eq_mul hs hkQ hpQ hpZ hk
  have hzk : p.2 * k = k * p.2 := Z_central hs.hyp hpZ hkQ
  have hconj : k⁻¹ * (p.1 * p.2) * k = p.1 * p.2 := by
    calc k⁻¹ * (p.1 * p.2) * k = k⁻¹ * ((p.1 * p.2) * k) := by group
      _ = k⁻¹ * (k * (p.1 * p.2)) := by
          rw [show k * (p.1 * p.2) = (p.1 * p.2) * k by
            rw [← mul_assoc, hka, mul_assoc, ← hzk, mul_assoc]]
      _ = p.1 * p.2 := by group
  have h1 : w = (k⁻¹ * w * k) * (p.1 * p.2) := by
    calc w = k⁻¹ * (k * w * k⁻¹) * k := by group
      _ = k⁻¹ * (w * p.1 * p.2) * k := by rw [hk]
      _ = (k⁻¹ * w * k) * (k⁻¹ * (p.1 * p.2) * k) := by group
      _ = (k⁻¹ * w * k) * (p.1 * p.2) := by rw [hconj]
  have h2 : (p.1 * p.2)⁻¹ = p.1⁻¹ * p.2⁻¹ := by
    rw [← Z_central hs.hyp hpZ hpQ.1, mul_inv_rev]
  refine ⟨L.inv_mem hpL, Z.inv_mem hpZ, k⁻¹, Q.inv_mem hkQ, ?_⟩
  rw [inv_inv]
  calc k⁻¹ * w * k = (k⁻¹ * w * k) * (p.1 * p.2) * (p.1 * p.2)⁻¹ := by group
    _ = w * (p.1 * p.2)⁻¹ := by rw [← h1]
    _ = w * p.1⁻¹ * p.2⁻¹ := by rw [h2]; group

private theorem lineConj_fst_surj (hc : Ctx M Q Z B) {Y : Subgroup G} {w : G}
    (hs : Sit M Q Z Y w) (hwL : w ∈ LB M Q B) {L : Subgroup G} (hLA : L ≤ Q ⊓ QB Y)
    (hLU : L ≤ Ut Q Z w) :
    ∀ a ∈ L, ∃ p : G × G, p ∈ LineConj w L Q Z ∧ p.1 = a := by
  intro a ha
  obtain ⟨x, hxQ, hxz⟩ := hc.exists_comm_mul_inv_mem_Z hwL (hLU ha)
  have haQ : a ∈ Q := (hLA ha).1
  have haw : a * w = w * a :=
    Subgroup.mem_centralizer_singleton_iff.mp ((smith_1_13 hs).2.2.2.1 (hLA ha)).2
  have hζu : (⁅x, w⁆ * a⁻¹) * a = a * (⁅x, w⁆ * a⁻¹) := Z_central hs.hyp hxz haQ
  have hζw : w * (⁅x, w⁆ * a⁻¹) * w⁻¹ = ⁅x, w⁆ * a⁻¹ := hs.x_cent (smith_1_12 hs) _ hxz
  refine ⟨(a, ⁅x, w⁆ * a⁻¹), ⟨ha, hxz, x, hxQ, ?_⟩, rfl⟩
  calc x * w * x⁻¹ = (⁅x, w⁆ * a⁻¹ * a) * w := by
        simp only [commutatorElement_def]; group
    _ = a * (⁅x, w⁆ * a⁻¹) * w := by rw [hζu]
    _ = a * ((⁅x, w⁆ * a⁻¹) * w) := by group
    _ = a * (w * (⁅x, w⁆ * a⁻¹)) := by
        rw [show (⁅x, w⁆ * a⁻¹) * w = w * (⁅x, w⁆ * a⁻¹) by
          calc (⁅x, w⁆ * a⁻¹) * w = (w * (⁅x, w⁆ * a⁻¹) * w⁻¹) * w := by rw [hζw]
            _ = w * (⁅x, w⁆ * a⁻¹) := by group]
    _ = w * a * (⁅x, w⁆ * a⁻¹) := by rw [← mul_assoc, ← haw]

private theorem lineConj_snd_inj {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {Y : Subgroup G} {w : G}
    (hs : Sit M Q Z Y w) {L : Subgroup G} (hLA : L ≤ Q ⊓ QB Y) (hline : M₀.IsLine L)
    (hroot : ∀ a ∈ L, (∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = a) → a = 1)
    {p p' : G × G} (hp : p ∈ LineConj w L Q Z) (hp' : p' ∈ LineConj w L Q Z)
    (h2 : p.2 = p'.2) : p.1 = p'.1 := by
  have hmul : p * p'⁻¹ ∈ LineConj w L Q Z :=
    lineConj_mul hD hs hLA hline hp (lineConj_inv hs hLA hp')
  have hq2 : (p * p'⁻¹).2 = 1 := by
    show p.2 * p'.2⁻¹ = 1
    rw [h2, mul_inv_cancel]
  obtain ⟨hqL, -, k, hkQ, hk⟩ := hmul
  have hk' : k * w * k⁻¹ = w * (p * p'⁻¹).1 := by rw [hk, hq2, mul_one]
  by_cases hq1 : (p * p'⁻¹).1 = 1
  · exact congrArg Prod.fst (mul_inv_eq_one.mp (Prod.ext hq1 hq2))
  · exact absurd (hroot _ hqL (Sit.isRoot_of_conj hs (hLA hqL) hq1 ⟨k, hk'⟩)) hq1

private theorem lineConj_conclusion {S : Subgroup (G × G)} {w : G} {L Q Z : Subgroup G}
    (hS : ∀ p : G × G, p ∈ S ↔ p ∈ LineConj w L Q Z)
    (hfst : ∀ p ∈ S, ∀ p' ∈ S, p.1 = p'.1 → p = p')
    (hsnd : ∀ z ∈ Z, ∃ p ∈ S, p.2 = z) :
    (∀ h ∈ Q, ∀ z ∈ Z, h * w * h⁻¹ = w * z → z = 1) ∧
      ∀ z ∈ Z, ∃ a ∈ L, ∃ k ∈ Q, k * w * k⁻¹ = w * a * z := by
  refine ⟨?_, ?_⟩
  · intro h hhQ z hz hhz
    have h1 : ((1, z) : G × G) ∈ S := (hS _).mpr ⟨L.one_mem, hz, h, hhQ, by
      show h * w * h⁻¹ = w * 1 * z
      rw [hhz]; group⟩
    have h2 : ((1, 1) : G × G) ∈ S := (hS _).mpr (lineConj_one w L Q Z)
    exact congrArg (fun p : G × G => p.2) (hfst _ h1 _ h2 rfl)
  · intro z hz
    obtain ⟨p, hp, hpz⟩ := hsnd z hz
    obtain ⟨hpL, -, k, hkQ, hk⟩ := (hS p).mp hp
    exact ⟨p.1, hpL, k, hkQ, by rw [hk, hpz]⟩

theorem Sit.line_fusion (hc : Ctx M Q Z B) {Y : Subgroup G} {w : G} (hs : Sit M Q Z Y w)
    (hwL : w ∈ LB M Q B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {L : Subgroup G}
    (hLA : L ≤ Q ⊓ QB Y) (hLU : L ≤ Ut Q Z w) (hline : M₀.IsLine L)
    (hLcard : Nat.card L = Nat.card Z)
    (hroot : ∀ a ∈ L, (∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = a) → a = 1) :
    (∀ h ∈ Q, ∀ z ∈ Z, h * w * h⁻¹ = w * z → z = 1) ∧
      ∀ z ∈ Z, ∃ a ∈ L, ∃ k ∈ Q, k * w * k⁻¹ = w * a * z := by
  let S : Subgroup (G × G) :=
    { carrier := LineConj w L Q Z
      mul_mem' := fun hp hq => lineConj_mul hD hs hLA hline hp hq
      one_mem' := lineConj_one w L Q Z
      inv_mem' := fun hp => lineConj_inv hs hLA hp }
  have hS : ∀ p : G × G, p ∈ S ↔ p ∈ LineConj w L Q Z := fun p => Iff.rfl
  let fstMap : S → L := fun p => ⟨p.1.1, (hS p.1).mp p.2 |>.1⟩
  let sndMap : S → Z := fun p => ⟨p.1.2, (hS p.1).mp p.2 |>.2.1⟩
  have hfstMap : ∀ p : S, (fstMap p : G) = p.1.1 := fun _ => rfl
  have hsndMap : ∀ p : S, (sndMap p : G) = p.1.2 := fun _ => rfl
  have hfst_surj : Function.Surjective fstMap := by
    intro a
    obtain ⟨p, hp, hpa⟩ := lineConj_fst_surj hc hs hwL hLA hLU a.1 a.2
    exact ⟨⟨p, (hS p).mpr hp⟩, Subtype.ext (by rw [hfstMap]; exact hpa)⟩
  have hsnd_inj : Function.Injective sndMap := by
    intro p p' hpp'
    have h2 : p.1.2 = p'.1.2 := by rw [← hsndMap p, ← hsndMap p', hpp']
    have h1 : p.1.1 = p'.1.1 :=
      lineConj_snd_inj hD hs hLA hline hroot ((hS p.1).mp p.2) ((hS p'.1).mp p'.2) h2
    exact Subtype.ext (Prod.ext h1 h2)
  have hS_le : Nat.card S ≤ Nat.card Z := Nat.card_le_card_of_injective sndMap hsnd_inj
  have hL_le : Nat.card L ≤ Nat.card S := Nat.card_le_card_of_surjective fstMap hfst_surj
  have hS_card : Nat.card S = Nat.card Z := le_antisymm hS_le (by rw [← hLcard]; exact hL_le)
  have hfst_inj : ∀ p ∈ S, ∀ p' ∈ S, p.1 = p'.1 → p = p' := by
    intro p hp p' hp' h
    have hb : (⟨p, hp⟩ : S) = ⟨p', hp'⟩ :=
      (hfst_surj.bijective_of_nat_card_le (by rw [hS_card, ← hLcard])).1
        (Subtype.ext (by rw [hfstMap, hfstMap]; exact h))
    exact congrArg (fun q : S => (q : G × G)) hb
  have hsnd_surj : ∀ z ∈ Z, ∃ p ∈ S, p.2 = z := by
    intro z hz
    obtain ⟨p, hp⟩ := (hsnd_inj.bijective_of_nat_card_le (by rw [hS_card])).2 ⟨z, hz⟩
    refine ⟨p.1, p.2, ?_⟩
    rw [← hsndMap p]
    exact congrArg Subtype.val hp
  exact lineConj_conclusion hS hfst_inj hsnd_surj

theorem Sit.not_isRoot_mul_of_line (hc : Ctx M Q Z B) {Y : Subgroup G} {w : G}
    (hs : Sit M Q Z Y w) (hwL : w ∈ LB M Q B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {L : Subgroup G}
    (hLA : L ≤ Q ⊓ QB Y) (hLU : L ≤ Ut Q Z w) (hline : M₀.IsLine L)
    (hLcard : Nat.card L = Nat.card Z)
    (hroot : ∀ a ∈ L, (∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = a) → a = 1) {z : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) : ¬ ∃ g : G, ∃ z' ∈ Z, z' ≠ 1 ∧ g * z' * g⁻¹ = w * z := by
  rintro ⟨g, z', hz', hz'1, hg⟩
  obtain ⟨h0, hfus⟩ := Sit.line_fusion hc hs hwL hD hLA hLU hline hLcard hroot
  obtain ⟨a, haL, k, hk, hkw⟩ := hfus z hz
  have ha1 : a ≠ 1 := fun ha1 => hz1 (h0 k hk z hz (by rw [hkw, ha1, mul_one]))
  have hkz : k * z * k⁻¹ = z := by rw [← Z_central hs.hyp hz hk]; group
  have hz2 : z * z = 1 := by rw [← pow_two]; exact Z_sq hs.hyp hz
  have hwa : k * (w * z) * k⁻¹ = w * a := by
    calc k * (w * z) * k⁻¹ = (k * w * k⁻¹) * (k * z * k⁻¹) := by group
      _ = w * a * (z * z) := by rw [hkw, hkz]; group
      _ = w * a := by rw [hz2, mul_one]
  obtain ⟨gY, hgY⟩ := hs.conj
  have hwZ : gY⁻¹ * w * gY ∈ Z := mem_conjSubgroup.mp (hgY ▸ hs.mem)
  have hwZ1 : gY⁻¹ * w * gY ≠ 1 := fun h => hs.ne_one (by
    calc w = gY * (gY⁻¹ * w * gY) * gY⁻¹ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨m, -, hm⟩ := Z_isConj hs.hyp hwZ hwZ1 hz' hz'1
  have hconj : (k * g * m * gY⁻¹) * w * (k * g * m * gY⁻¹)⁻¹ = w * a := by
    calc (k * g * m * gY⁻¹) * w * (k * g * m * gY⁻¹)⁻¹
        = k * (g * (m * (gY⁻¹ * w * gY) * m⁻¹) * g⁻¹) * k⁻¹ := by group
      _ = k * (w * z) * k⁻¹ := by rw [hm, hg]
      _ = w * a := hwa
  exact ha1 (hroot a haL (Sit.isRoot_of_conj hs (hLA haL) ha1 ⟨_, hconj⟩))

theorem Sit.exists_conj_of_isRoot_of_line (hc : Ctx M Q Z B) {Y : Subgroup G} {w : G}
    (hs : Sit M Q Z Y w) (hwL : w ∈ LB M Q B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {L : Subgroup G}
    (hLA : L ≤ Q ⊓ QB Y) (hLU : L ≤ Ut Q Z w) (hline : M₀.IsLine L)
    (hLcard : Nat.card L = Nat.card Z)
    (hroot : ∀ a ∈ L, (∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = a) → a = 1) {u z : G}
    (hu : u ∈ Q ⊓ QB Y ⊓ Ut Q Z w) (hz : z ∈ Z)
    (hr : ∃ g : G, ∃ z' ∈ Z, z' ≠ 1 ∧ g * z' * g⁻¹ = w * u * z) :
    ∃ k ∈ Q, k * w * k⁻¹ = w * u * z := by
  obtain ⟨x, hxQ, hx⟩ := hc.exists_comm_mul_inv_mem_Z hwL hu.2
  have huw : u * w = w * u :=
    Subgroup.mem_centralizer_singleton_iff.mp ((smith_1_13 hs).2.2.2.1 hu.1).2
  have hζw : w * (⁅x, w⁆ * u⁻¹) * w⁻¹ = ⁅x, w⁆ * u⁻¹ := hs.x_cent (smith_1_12 hs) _ hx
  have hζu : ⁅x, w⁆ * u⁻¹ * u = u * (⁅x, w⁆ * u⁻¹) := Z_central hs.hyp hx hu.1.1
  have hxw : x * w * x⁻¹ = w * u * (⁅x, w⁆ * u⁻¹) := by
    calc x * w * x⁻¹ = (⁅x, w⁆ * u⁻¹ * u) * w := by simp only [commutatorElement_def]; group
      _ = u * (⁅x, w⁆ * u⁻¹) * w := by rw [hζu]
      _ = u * ((⁅x, w⁆ * u⁻¹) * w) := by group
      _ = u * (w * (⁅x, w⁆ * u⁻¹)) := by
          rw [show (⁅x, w⁆ * u⁻¹) * w = w * (⁅x, w⁆ * u⁻¹) by
            calc (⁅x, w⁆ * u⁻¹) * w = (w * (⁅x, w⁆ * u⁻¹) * w⁻¹) * w := by rw [hζw]
              _ = w * (⁅x, w⁆ * u⁻¹) := by group]
      _ = w * u * (⁅x, w⁆ * u⁻¹) := by rw [← mul_assoc, ← huw]
  have hxz : x * ((⁅x, w⁆ * u⁻¹)⁻¹ * z) * x⁻¹ = (⁅x, w⁆ * u⁻¹)⁻¹ * z := by
    rw [← Z_central hs.hyp (Z.mul_mem (Z.inv_mem hx) hz) hxQ]; group
  by_cases h1 : (⁅x, w⁆ * u⁻¹)⁻¹ * z = 1
  · refine ⟨x, hxQ, ?_⟩
    rw [hxw]
    congr 1
    calc ⁅x, w⁆ * u⁻¹ = (⁅x, w⁆ * u⁻¹) * ((⁅x, w⁆ * u⁻¹)⁻¹ * z) := by rw [h1, mul_one]
      _ = z := by group
  · exfalso
    apply Sit.not_isRoot_mul_of_line hc hs hwL hD hLA hLU hline hLcard hroot
      (Z.mul_mem (Z.inv_mem hx) hz) h1
    obtain ⟨g, z', hz', hz'1, hg⟩ := hr
    refine ⟨x⁻¹ * g, z', hz', hz'1, ?_⟩
    have e : x * (w * ((⁅x, w⁆ * u⁻¹)⁻¹ * z)) * x⁻¹ = w * u * z := by
      calc x * (w * ((⁅x, w⁆ * u⁻¹)⁻¹ * z)) * x⁻¹
          = (x * w * x⁻¹) * (x * ((⁅x, w⁆ * u⁻¹)⁻¹ * z) * x⁻¹) := by group
        _ = w * u * z := by rw [hxw, hxz]; group
    calc x⁻¹ * g * z' * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * z' * g⁻¹) * x := by group
      _ = x⁻¹ * (x * (w * ((⁅x, w⁆ * u⁻¹)⁻¹ * z)) * x⁻¹) * x := by rw [hg, e]
      _ = w * ((⁅x, w⁆ * u⁻¹)⁻¹ * z) := by group


end CFSG.RankThree.GF2n.Stroth80
