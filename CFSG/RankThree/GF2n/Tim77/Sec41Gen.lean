module

public import CFSG.RankThree.GF2n.Tim77.Sec3Basic
public import CFSG.RankThree.GF2n.Tim77Prop24Inv
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

theorem sec41g_conj_cancel (g : G) (T : Subgroup G) :
    conjSubgroup g⁻¹ (conjSubgroup g T) = T := by
  rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

theorem sec41g_conj_cancel' (g : G) (T : Subgroup G) :
    conjSubgroup g (conjSubgroup g⁻¹ T) = T := by
  rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]

theorem sec41g_conj_inj {g : G} {T U : Subgroup G}
    (h : conjSubgroup g T = conjSubgroup g U) : T = U :=
  calc T = conjSubgroup g⁻¹ (conjSubgroup g T) := (sec41g_conj_cancel g T).symm
    _ = conjSubgroup g⁻¹ (conjSubgroup g U) := by rw [h]
    _ = U := sec41g_conj_cancel g U

theorem sec41g_conj_ne_bot {g : G} {T : Subgroup G} (hT : T ≠ ⊥) :
    conjSubgroup g T ≠ ⊥ := by
  intro h
  apply hT
  exact (sec41g_conj_cancel g T).symm.trans
    ((congrArg (conjSubgroup g⁻¹) h).trans (Subgroup.map_bot _))

theorem sec41g_conj_normalizer (g : G) (S : Subgroup G) :
    conjSubgroup g (Subgroup.normalizer (S : Set G)) =
      Subgroup.normalizer ((conjSubgroup g S : Subgroup G) : Set G) :=
  Subgroup.map_equiv_normalizer_eq S (MulAut.conj g)

theorem sec41g_conj_inf_normalizer (g : G) (T S : Subgroup G) :
    conjSubgroup g (T ⊓ Subgroup.normalizer (S : Set G)) =
      conjSubgroup g T ⊓ Subgroup.normalizer ((conjSubgroup g S : Subgroup G) : Set G) := by
  rw [conjSubgroup_inf, sec41g_conj_normalizer]

theorem sec41g_mem_conj {T : Subgroup G} {g a : G} (ha : a ∈ T) :
    g * a * g⁻¹ ∈ conjSubgroup g T := by
  rw [mem_conjSubgroup, show g⁻¹ * (g * a * g⁻¹) * g = a by group]
  exact ha

theorem sec41g_not_mem_conj {T : Subgroup G} {g a : G} (ha : a ∉ T) :
    g * a * g⁻¹ ∉ conjSubgroup g T := by
  intro hmem
  apply ha
  have h1 := mem_conjSubgroup.mp hmem
  rwa [show g⁻¹ * (g * a * g⁻¹) * g = a by group] at h1

theorem sec41g_invol {A : Subgroup G} (hA : IsElemAbelian 2 A) {a : G} (ha : a ∈ A) :
    a * a = 1 := by
  rw [← sq]
  exact hA.2 a ha

theorem sec41g_conj_sq {g a : G} (ha : a * a = 1) : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
  calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
    _ = 1 := by rw [ha, mul_one, mul_inv_cancel]

theorem sec41g_order_of_comm {d e : G} (hd : d * d = 1) (he : e * e = 1)
    (hc : d * e = e * d) : orderOf (d * e) = 2 ∨ Odd (orderOf (d * e)) := by
  have hpow : (d * e) ^ 2 = 1 := by
    rw [sq]
    calc d * e * (d * e) = d * (e * d) * e := by group
      _ = d * (d * e) * e := by rw [hc]
      _ = (d * d) * (e * e) := by group
      _ = 1 := by rw [hd, he, mul_one]
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow) with h1 | h1
  · right
    rw [h1]
    exact odd_one
  · left
    exact h1

@[expose] def sec41g_D (W A A₀ : Subgroup G) : Set G :=
  {t | ∃ y ∈ W, ∃ a ∈ A, a ∉ A₀ ∧ t = y * a * y⁻¹}

theorem sec41g_mem_D {W A A₀ : Subgroup G} {t : G} :
    t ∈ sec41g_D W A A₀ ↔ ∃ y ∈ W, ∃ a ∈ A, a ∉ A₀ ∧ t = y * a * y⁻¹ := by
  unfold sec41g_D
  exact Iff.rfl

theorem sec41g_D_conj {W A A₀ : Subgroup G} {g e : G} (hg : g ∈ W)
    (he : e ∈ sec41g_D W A A₀) : g * e * g⁻¹ ∈ sec41g_D W A A₀ := by
  obtain ⟨y, hy, a, ha, haA₀, rfl⟩ := sec41g_mem_D.mp he
  refine sec41g_mem_D.mpr ⟨g * y, mul_mem hg hy, a, ha, haA₀, ?_⟩
  group

theorem sec41g_key [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {W N₀ : Subgroup G} (hAN : ∀ y ∈ W, conjSubgroup y (Section3.A0 A Abar) ≤ N₀)
    (hNc : ∀ x ∈ N₀, ∀ w ∈ N₀, x * w = w * x)
    {y z : G} (hy : y ∈ W) (hz : z ∈ W)
    (hnc : ¬ ∀ x ∈ conjSubgroup y A, ∀ w ∈ conjSubgroup z A, x * w = w * x) :
    conjSubgroup y A ⊓ Subgroup.normalizer (conjSubgroup z A : Set G) =
      conjSubgroup y (Section3.A0 A Abar) := by
  have hS : Prop24Setup A Abar (Section3.A0 A Abar) (Section3.Abar0 A Abar)
      (Section3.M A Abar) := h.setup
  have hA₀A : Section3.A0 A Abar ≤ A := hS.L_le
  have hA₀ne : Section3.A0 A Abar ≠ ⊥ := hS.ne_bot
  have hAy0 : conjSubgroup y (Section3.A0 A Abar) ≤ N₀ := hAN y hy
  have hAz0 : conjSubgroup z (Section3.A0 A Abar) ≤ N₀ := hAN z hz
  obtain ⟨⟨x₁, hx₁⟩, hx₁1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (sec41g_conj_ne_bot (g := z) hA₀ne)
  have hx₁1' : x₁ ≠ 1 := fun h' => hx₁1 (Subtype.ext h')
  have hx₁A : x₁ ∈ conjSubgroup z A := by
    rw [mem_conjSubgroup]
    exact hA₀A (mem_conjSubgroup.mp hx₁)
  have hx₁N : x₁ ∈ N₀ := hAz0 hx₁
  have hA₀le : conjSubgroup y (Section3.A0 A Abar) ≤
      conjSubgroup y A ⊓ Subgroup.normalizer (conjSubgroup z A : Set G) := by
    intro c hc
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_conjSubgroup] at hc ⊢
      exact hA₀A hc
    · exact mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup h.hyp.ti z) hx₁A hx₁1'
        (hNc c (hAy0 hc) x₁ hx₁N)
  have hne_Ay : conjSubgroup y A ⊓ Subgroup.normalizer (conjSubgroup z A : Set G) ≠
      conjSubgroup y A := by
    intro heq
    have hconj : conjSubgroup (y * z⁻¹) (conjSubgroup z A) = conjSubgroup y A := by
      rw [← conjSubgroup_mul, inv_mul_cancel_right]
    have hg : conjSubgroup (y * z⁻¹) (conjSubgroup z A) ≤
        Subgroup.normalizer (conjSubgroup z A : Set G) := by
      rw [hconj]
      intro c hc
      have hc' : c ∈ conjSubgroup y A ⊓ Subgroup.normalizer (conjSubgroup z A : Set G) := by
        rw [heq]
        exact hc
      exact (Subgroup.mem_inf.mp hc').2
    have hel := tim77_2_3 (isElemAbelian_conj h.hyp.elemAbelian z)
      (isTI_conjSubgroup h.hyp.ti z) hg
    apply hnc
    intro x hx w hw
    have hx' : x ∈ conjSubgroup (y * z⁻¹) (conjSubgroup z A) := by
      rw [hconj]
      exact hx
    have hcomm := congrArg Subtype.val (hel.1.is_comm.comm
      (⟨w, Subgroup.mem_sup_left hw⟩ :
        ↥(conjSubgroup z A ⊔ conjSubgroup (y * z⁻¹) (conjSubgroup z A)))
      ⟨x, Subgroup.mem_sup_right hx'⟩)
    exact hcomm.symm
  have hAy : conjSubgroup y⁻¹ (conjSubgroup y A) = A := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hAz : conjSubgroup y⁻¹ (conjSubgroup z A) = conjSubgroup (y⁻¹ * z) A := by
    rw [← conjSubgroup_mul]
  have hL₀ : conjSubgroup y⁻¹ (conjSubgroup y A ⊓ Subgroup.normalizer (conjSubgroup z A : Set G))
      = A ⊓ Subgroup.normalizer (conjSubgroup (y⁻¹ * z) A : Set G) := by
    rw [sec41g_conj_inf_normalizer, hAy, hAz]
  have hL₁ne : conjSubgroup y A ⊓ Subgroup.normalizer (conjSubgroup z A : Set G) ≠ ⊥ := by
    intro h'
    have h'' := hA₀le
    rw [h'] at h''
    exact sec41g_conj_ne_bot hA₀ne (le_bot_iff.mp h'')
  have hL₀ne : A ⊓ Subgroup.normalizer (conjSubgroup (y⁻¹ * z) A : Set G) ≠ ⊥ := by
    rw [← hL₀]
    exact sec41g_conj_ne_bot hL₁ne
  have hL₀A : A ⊓ Subgroup.normalizer (conjSubgroup (y⁻¹ * z) A : Set G) ≠ A := by
    intro h'
    apply hne_Ay
    calc conjSubgroup y A ⊓ Subgroup.normalizer (conjSubgroup z A : Set G)
        = conjSubgroup y (conjSubgroup y⁻¹ (conjSubgroup y A ⊓
            Subgroup.normalizer (conjSubgroup z A : Set G))) := (sec41g_conj_cancel' y _).symm
      _ = conjSubgroup y (A ⊓ Subgroup.normalizer (conjSubgroup (y⁻¹ * z) A : Set G)) := by
          rw [hL₀]
      _ = conjSubgroup y A := by rw [h']
  have S' : Prop24Setup A (conjSubgroup (y⁻¹ * z) A)
      (A ⊓ Subgroup.normalizer (conjSubgroup (y⁻¹ * z) A : Set G))
      (conjSubgroup (y⁻¹ * z) A ⊓ Subgroup.normalizer (A : Set G))
      ((A ⊓ Subgroup.normalizer (conjSubgroup (y⁻¹ * z) A : Set G)) ⊔
        (conjSubgroup (y⁻¹ * z) A ⊓ Subgroup.normalizer (A : Set G))) :=
    { elem := h.hyp.elemAbelian
      ti := h.hyp.ti
      conj := ⟨y⁻¹ * z, rfl⟩
      hL := rfl
      hLb := rfl
      hM := rfl
      ne_bot := hL₀ne
      ne := hL₀A }
  have hcardL : Nat.card ↥(conjSubgroup y A ⊓ Subgroup.normalizer (conjSubgroup z A : Set G))
      = Nat.card ↥(A ⊓ Subgroup.normalizer (conjSubgroup (y⁻¹ * z) A : Set G)) := by
    rw [← hL₀, card_conjSubgroup]
  have hmax := h.nota.choice.2.2 (y⁻¹ * z)
    (by unfold normalizerIn; exact ⟨S'.Lb_ne_bot, S'.Lb_ne⟩)
  have hcard : Nat.card ↥(conjSubgroup y A ⊓ Subgroup.normalizer (conjSubgroup z A : Set G))
      ≤ Nat.card ↥(Section3.A0 A Abar) := by
    rw [hcardL, ← S'.card_Lb_eq, ← hS.card_Lb_eq]
    exact hmax
  have heq : conjSubgroup y (Section3.A0 A Abar) =
      conjSubgroup y A ⊓ Subgroup.normalizer (conjSubgroup z A : Set G) := by
    apply Subgroup.eq_of_le_of_card_ge hA₀le
    rw [card_conjSubgroup]
    exact hcard
  exact heq.symm

theorem sec41g_prop24 [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {W N₀ : Subgroup G} (hAN : ∀ y ∈ W, conjSubgroup y (Section3.A0 A Abar) ≤ N₀)
    (hNc : ∀ x ∈ N₀, ∀ w ∈ N₀, x * w = w * x)
    {y z : G} (hy : y ∈ W) (hz : z ∈ W)
    (hnc : ¬ ∀ x ∈ conjSubgroup y A, ∀ w ∈ conjSubgroup z A, x * w = w * x) :
    Prop24Setup (conjSubgroup y A) (conjSubgroup z A) (conjSubgroup y (Section3.A0 A Abar))
      (conjSubgroup z (Section3.A0 A Abar))
      (conjSubgroup y (Section3.A0 A Abar) ⊔ conjSubgroup z (Section3.A0 A Abar)) := by
  have hnc' : ¬ ∀ x ∈ conjSubgroup z A, ∀ w ∈ conjSubgroup y A, x * w = w * x :=
    fun hall => hnc fun x hx w hw => (hall w hw x hx).symm
  refine
    { elem := isElemAbelian_conj h.hyp.elemAbelian y
      ti := isTI_conjSubgroup h.hyp.ti y
      conj := ⟨z * y⁻¹, ?_⟩
      hL := (sec41g_key h hAN hNc hy hz hnc).symm
      hLb := (sec41g_key h hAN hNc hz hy hnc').symm
      hM := rfl
      ne_bot := sec41g_conj_ne_bot h.a0_ne_bot
      ne := ?_ }
  · rw [← conjSubgroup_mul, inv_mul_cancel_right]
  · intro heq
    exact h.a0_ne (sec41g_conj_inj heq)

theorem sec41g_centralizer [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {W N₀ : Subgroup G} (hAN : ∀ y ∈ W, conjSubgroup y (Section3.A0 A Abar) ≤ N₀)
    (hNc : ∀ x ∈ N₀, ∀ w ∈ N₀, x * w = w * x)
    {z a e : G} (hz : z ∈ W) (ha : a ∈ A) (ha1 : a ≠ 1)
    (he : e ∈ conjSubgroup z A) (heA : e ∉ conjSubgroup z (Section3.A0 A Abar))
    (hea : e * a = a * e) : conjSubgroup z A ≤ Subgroup.centralizer (A : Set G) := by
  by_contra hcon
  have hnc : ¬ ∀ x ∈ conjSubgroup z A, ∀ w ∈ conjSubgroup 1 A, x * w = w * x := by
    intro hall
    apply hcon
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hall x hx b (by rw [conjSubgroup_one]; exact hb)).symm
  have hkey := sec41g_key h hAN hNc hz (Subgroup.one_mem _) hnc
  rw [conjSubgroup_one] at hkey
  apply heA
  rw [← hkey]
  exact Subgroup.mem_inf.mpr ⟨he, mem_normalizer_of_commute_of_isTI h.hyp.ti ha ha1 hea⟩

theorem sec41g_comm_pair [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {W N₀ : Subgroup G} (hAN : ∀ y ∈ W, conjSubgroup y (Section3.A0 A Abar) ≤ N₀)
    (hNc : ∀ x ∈ N₀, ∀ w ∈ N₀, x * w = w * x)
    {z w e f : G} (hz : z ∈ W) (hw : w ∈ W)
    (he : e ∈ conjSubgroup z A) (hf : f ∈ conjSubgroup w A)
    (hC1 : conjSubgroup z A ≤ Subgroup.centralizer (A : Set G))
    (hC2 : conjSubgroup w A ≤ Subgroup.centralizer (A : Set G)) : e * f = f * e := by
  by_contra hef
  have hnc : ¬ ∀ x ∈ conjSubgroup z A, ∀ v ∈ conjSubgroup w A, x * v = v * x :=
    fun hall => hef (hall e he f hf)
  have S12 := sec41g_prop24 h hAN hNc hz hw hnc
  obtain ⟨x, hxmem, hxeq⟩ := S12.exists_conj_eq
  have hxC : x ∈ Subgroup.centralizer (A : Set G) := (sup_le hC1 hC2) hxmem
  obtain ⟨-, -, -, hcomm⟩ := h.hyp.rootTypeInCentralizer z hC1
  have hf' : f ∈ conjSubgroup x (conjSubgroup z A) := by
    rw [← hxeq]
    exact hf
  have hne : normalizerIn (conjSubgroup z A) (conjSubgroup x (conjSubgroup z A)) ≠ ⊥ := by
    rw [← hxeq]
    unfold normalizerIn
    rw [← S12.hL]
    exact sec41g_conj_ne_bot h.a0_ne_bot
  exact hef (hcomm x hxC hne e he f hf')

theorem sec41g_comm_a [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {W N₀ : Subgroup G} (hAN : ∀ y ∈ W, conjSubgroup y (Section3.A0 A Abar) ≤ N₀)
    (hNc : ∀ x ∈ N₀, ∀ w ∈ N₀, x * w = w * x)
    {a : G} (ha : a ∈ A) (haA₀ : a ∉ Section3.A0 A Abar)
    {e f : G} (he : e ∈ sec41g_D W A (Section3.A0 A Abar)) (hea : e * a = a * e)
    (hf : f ∈ sec41g_D W A (Section3.A0 A Abar)) (hfa : f * a = a * f) : e * f = f * e := by
  have ha1 : a ≠ 1 := fun h1 => haA₀ (by rw [h1]; exact Subgroup.one_mem _)
  obtain ⟨z, hz, b, hb, hbA₀, rfl⟩ := sec41g_mem_D.mp he
  obtain ⟨w, hw, c, hc, hcA₀, rfl⟩ := sec41g_mem_D.mp hf
  have hC1 := sec41g_centralizer h hAN hNc hz ha ha1 (sec41g_mem_conj hb)
    (sec41g_not_mem_conj hbA₀) hea
  have hC2 := sec41g_centralizer h hAN hNc hw ha ha1 (sec41g_mem_conj hc)
    (sec41g_not_mem_conj hcA₀) hfa
  exact sec41g_comm_pair h hAN hNc hz hw (sec41g_mem_conj hb) (sec41g_mem_conj hc) hC1 hC2

theorem sec41g_comm_gen [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {W N₀ : Subgroup G} (hAN : ∀ y ∈ W, conjSubgroup y (Section3.A0 A Abar) ≤ N₀)
    (hNc : ∀ x ∈ N₀, ∀ w ∈ N₀, x * w = w * x)
    {d e f : G} (hd : d ∈ sec41g_D W A (Section3.A0 A Abar))
    (he : e ∈ sec41g_D W A (Section3.A0 A Abar)) (hed : e * d = d * e)
    (hf : f ∈ sec41g_D W A (Section3.A0 A Abar)) (hfd : f * d = d * f) : e * f = f * e := by
  obtain ⟨y, hy, a, ha, haA₀, rfl⟩ := sec41g_mem_D.mp hd
  have key : ∀ x ∈ sec41g_D W A (Section3.A0 A Abar),
      x * (y * a * y⁻¹) = (y * a * y⁻¹) * x →
      y⁻¹ * x * y ∈ sec41g_D W A (Section3.A0 A Abar) ∧
        (y⁻¹ * x * y) * a = a * (y⁻¹ * x * y) := by
    intro x hx hxd
    refine ⟨?_, ?_⟩
    · have := sec41g_D_conj (inv_mem hy) hx
      rwa [inv_inv] at this
    · calc y⁻¹ * x * y * a = y⁻¹ * (x * (y * a * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * a * y⁻¹) * x) * y := by rw [hxd]
        _ = a * (y⁻¹ * x * y) := by group
  obtain ⟨he', hea⟩ := key e he hed
  obtain ⟨hf', hfa⟩ := key f hf hfd
  have hcomm := sec41g_comm_a h hAN hNc ha haA₀ he' hea hf' hfa
  calc e * f = y * ((y⁻¹ * e * y) * (y⁻¹ * f * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * f * y) * (y⁻¹ * e * y)) * y⁻¹ := by rw [hcomm]
    _ = f * e := by group

theorem sec41g_order [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {W N₀ : Subgroup G} (hAN : ∀ y ∈ W, conjSubgroup y (Section3.A0 A Abar) ≤ N₀)
    (hNc : ∀ x ∈ N₀, ∀ w ∈ N₀, x * w = w * x)
    {d e : G} (hd : d ∈ sec41g_D W A (Section3.A0 A Abar))
    (he : e ∈ sec41g_D W A (Section3.A0 A Abar)) :
    orderOf (d * e) = 2 ∨ Odd (orderOf (d * e)) := by
  obtain ⟨y, hy, a, ha, haA₀, rfl⟩ := sec41g_mem_D.mp hd
  obtain ⟨z, hz, b, hb, hbA₀, rfl⟩ := sec41g_mem_D.mp he
  by_cases hc : (y * a * y⁻¹) * (z * b * z⁻¹) = (z * b * z⁻¹) * (y * a * y⁻¹)
  · exact sec41g_order_of_comm (sec41g_conj_sq (sec41g_invol h.hyp.elemAbelian ha))
      (sec41g_conj_sq (sec41g_invol h.hyp.elemAbelian hb)) hc
  · right
    have hnc : ¬ ∀ x ∈ conjSubgroup y A, ∀ w ∈ conjSubgroup z A, x * w = w * x :=
      fun hall => hc (hall _ (sec41g_mem_conj ha) _ (sec41g_mem_conj hb))
    exact (sec41g_prop24 h hAN hNc hy hz hnc).odd_orderOf_mul (sec41g_mem_conj ha)
      (sec41g_not_mem_conj haA₀) (sec41g_mem_conj hb) (sec41g_not_mem_conj hbA₀)

theorem sec41g_ne_four [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {W N₀ : Subgroup G} (hAN : ∀ y ∈ W, conjSubgroup y (Section3.A0 A Abar) ≤ N₀)
    (hNc : ∀ x ∈ N₀, ∀ w ∈ N₀, x * w = w * x)
    {d e : G} (hd : d ∈ sec41g_D W A (Section3.A0 A Abar))
    (he : e ∈ sec41g_D W A (Section3.A0 A Abar)) :
    orderOf (d * e) ≠ 4 := by
  rcases sec41g_order h hAN hNc hd he with h2 | ho
  · omega
  · intro h4
    rw [h4] at ho
    norm_num at ho

end CFSG.RankThree.GF2n.Tim77
