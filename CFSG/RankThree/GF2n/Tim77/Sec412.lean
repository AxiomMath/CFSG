module

public import CFSG.RankThree.GF2n.Tim77.Sec48
public import CFSG.RankThree.GF2n.Tim77.Sec49
public import CFSG.RankThree.GF2n.Tim77.Sec411
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup

theorem sec412_comm_conj (h49 : Tim77Sec49Statement) {G : Type} [Group G] [Finite G]
    {A Abar S₀ B : Subgroup G} (hctx : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2)
    (hA0 : Sec4A0LeCenterH A Abar) {a x g : G} (ha : a ∈ A)
    (ha0 : a ∉ Section3.A0 A Abar) (hx : x ∈ conjSubgroup g A) (hord : orderOf (a * x) = 4) :
    ∀ b ∈ A, ∀ y ∈ conjSubgroup x A, b * y = y * b := by
  have hxA : IsElemAbelian 2 (conjSubgroup g A) := isElemAbelian_conj hctx.hyp.elemAbelian g
  have hx2 : x * x = 1 := by rw [← sq]; exact hxA.2 x hx
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have ha2 : a * a = 1 := by rw [← sq]; exact hctx.hyp.elemAbelian.2 a ha
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have ha1 : a ≠ 1 := by
    intro h
    apply ha0
    rw [h]
    exact Subgroup.one_mem _
  obtain ⟨t, ht_def⟩ : ∃ t : G, t = x * a * x⁻¹ := ⟨_, rfl⟩
  have ht2 : t * t = 1 := by
    rw [ht_def]
    calc x * a * x⁻¹ * (x * a * x⁻¹) = x * (a * a) * x⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ht1 : t ≠ 1 := by
    intro h
    apply ha1
    have e : a = x⁻¹ * t * x := by rw [ht_def]; group
    rw [e, h]
    group
  have htx : t ∈ conjSubgroup x A := by
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup,
      show x⁻¹ * t * x = a by rw [ht_def]; group]
    exact ha
  have hsq : (a * x) * (a * x) = a * t * (x * x) := by rw [ht_def]; group
  rw [hx2, mul_one] at hsq
  have hP4 : (a * x) ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hPt : (a * x) ^ 4 = (a * t) * (a * t) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hsq]
  have hat2 : (a * t) * (a * t) = 1 := by
    rw [← hPt]
    exact hP4
  have hatc : t * a = a * t := by
    have hinv : (a * t)⁻¹ = a * t := inv_eq_of_mul_eq_one_right hat2
    rw [mul_inv_rev, ha_inv, ht_inv] at hinv
    exact hinv
  have htN : t ∈ Subgroup.normalizer (A : Set G) :=
    mem_normalizer_of_commute_of_isTI hctx.hyp.ti ha ha1 hatc
  have h9 := (h49 G A Abar S₀ B hctx hq hA0).2.2.2 t htN ht1 ⟨x, htx⟩
  have hbt : ∀ b ∈ A, b * t = t * b := by
    rcases h9 with h9 | h9
    · exfalso
      apply ha0
      rw [h9]
      refine Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hatc
    · intro b hb
      exact Subgroup.mem_centralizer_iff.mp h9 b hb
  have hTx : IsTI (conjSubgroup x A) := isTI_conjSubgroup hctx.hyp.ti x
  have hbN : ∀ b ∈ A, b ∈ Subgroup.normalizer (conjSubgroup x A : Set G) := fun b hb =>
    mem_normalizer_of_commute_of_isTI hTx htx ht1 (hbt b hb)
  have hconjN : ∀ b ∈ A, x⁻¹ * b * x ∈ Subgroup.normalizer (A : Set G) := by
    intro b hb
    rw [← conjSubgroup_eq_self_iff, conjSubgroup_mul, conjSubgroup_mul,
      conjSubgroup_eq_self_iff.mpr (hbN b hb), ← conjSubgroup_mul, inv_mul_cancel,
      conjSubgroup_one]
  have hg : conjSubgroup x⁻¹ A ≤ Subgroup.normalizer (A : Set G) := by
    intro c hc
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, inv_inv] at hc
    have e := hconjN _ hc
    rwa [show x⁻¹ * (x * c * x⁻¹) * x = c by group] at e
  have hE := tim77_2_3 hctx.hyp.elemAbelian hctx.hyp.ti hg
  have hcomm : ∀ c ∈ A, ∀ z ∈ conjSubgroup x⁻¹ A, c * z = z * c := fun c hc z hz =>
    congrArg Subtype.val
      (hE.1.is_comm.comm ⟨c, Subgroup.mem_sup_left hc⟩ ⟨z, Subgroup.mem_sup_right hz⟩)
  intro b hb y hy
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hy
  have hz : x⁻¹ * b * x ∈ conjSubgroup x⁻¹ A := by
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, inv_inv,
      show x * (x⁻¹ * b * x) * x⁻¹ = b by group]
    exact hb
  have hcz := hcomm _ hy _ hz
  calc b * y = x * ((x⁻¹ * b * x) * (x⁻¹ * y * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * y * x) * (x⁻¹ * b * x)) * x⁻¹ := by rw [← hcz]
    _ = y * b := by group

theorem sec412_orderOf_mul_x {G : Type} [Group G] [Finite G] {A : Subgroup G} (hTI : IsTI A)
    {x b : G} (hx : x * x = 1) (hb : b ∈ A) (hb1 : b ≠ 1) (hb2 : b * b = 1)
    (hxN : x ∉ Subgroup.normalizer (A : Set G))
    (hcomm : ∀ c ∈ A, ∀ y ∈ conjSubgroup x A, c * y = y * c) :
    orderOf (b * x) = 4 ∧ x * (b * x * b) = (b * x * b) * x := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hconjb : x⁻¹ * (x * b * x) * x = b := by
    rw [hxinv]
    calc x * (x * b * x) * x = (x * x) * b * (x * x) := by group
      _ = b := by rw [hx, one_mul, mul_one]
  have hw' : x * b * x ∈ conjSubgroup x A := by
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, hconjb]
    exact hb
  have hbw : b * (x * b * x) = (x * b * x) * b := hcomm b hb _ hw'
  have hw2 : (x * b * x) * (x * b * x) = 1 := by
    calc (x * b * x) * (x * b * x) = x * (b * (x * x) * b) * x := by group
      _ = 1 := by rw [hx, mul_one, hb2, mul_one, hx]
  have hbw2 : (b * (x * b * x)) * (b * (x * b * x)) = 1 := by
    calc (b * (x * b * x)) * (b * (x * b * x))
        = b * ((x * b * x) * b) * (x * b * x) := by group
      _ = b * (b * (x * b * x)) * (x * b * x) := by rw [← hbw]
      _ = (b * b) * ((x * b * x) * (x * b * x)) := by group
      _ = 1 := by rw [hb2, hw2, one_mul]
  have hw1 : x * b * x ≠ b := by
    intro h
    apply hxN
    rw [← conjSubgroup_eq_self_iff]
    apply conjSubgroup_eq_of_isTI hTI
    intro hbot
    apply hb1
    have hmem : b ∈ A ⊓ conjSubgroup x A := Subgroup.mem_inf.mpr ⟨hb, h ▸ hw'⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hbw_ne : b * (x * b * x) ≠ 1 := by
    intro h
    apply hw1
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hb2]
  have hP2 : (b * x) * (b * x) = b * (x * b * x) := by group
  have hP4 : (b * x) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hP2]
    exact hbw2
  have hord : orderOf (b * x) = 4 := by
    have h1 : ¬ (b * x) ^ (2 ^ 1) = 1 := by
      show ¬ (b * x) ^ 2 = 1
      rw [sq, hP2]
      exact hbw_ne
    have h2 : (b * x) ^ (2 ^ (1 + 1)) = 1 := by
      show (b * x) ^ 4 = 1
      exact hP4
    exact orderOf_eq_prime_pow h1 h2
  have huu : (b * x * b) * (b * x * b) = 1 := by
    calc (b * x * b) * (b * x * b) = b * (x * (b * b) * x) * b := by group
      _ = 1 := by rw [hb2, mul_one, hx, mul_one, hb2]
  have hbxbx : b * x * b * x = b * (x * b * x) := by group
  have huxu : (b * x * b * x) * (b * x * b * x) = 1 := by
    rw [hbxbx]
    exact hbw2
  have hcomm2 : x * (b * x * b) = (b * x * b) * x := by
    have hu_inv : (b * x * b)⁻¹ = b * x * b := inv_eq_of_mul_eq_one_right huu
    have hinv : (b * x * b * x)⁻¹ = b * x * b * x := inv_eq_of_mul_eq_one_right huxu
    rw [mul_inv_rev, hxinv, hu_inv] at hinv
    exact hinv
  exact ⟨hord, hcomm2⟩

variable {G : Type} [Group G]

theorem sec412_conj_comm {Y C : Subgroup G}
    (hcomm : ∀ c ∈ C, ∀ y ∈ Y, ∀ z ∈ conjSubgroup c Y, y * z = z * y)
    {c d u v : G} (hc : c ∈ C) (hd : d ∈ C) (hu : u ∈ conjSubgroup c Y)
    (hv : v ∈ conjSubgroup d Y) : u * v = v * u := by
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hu hv
  have heC : c⁻¹ * d ∈ C := C.mul_mem (C.inv_mem hc) hd
  have hz' : c⁻¹ * v * c ∈ conjSubgroup (c⁻¹ * d) Y := by
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup,
      show (c⁻¹ * d)⁻¹ * (c⁻¹ * v * c) * (c⁻¹ * d) = d⁻¹ * v * d by group]
    exact hv
  have key := hcomm _ heC _ hu _ hz'
  calc u * v = c * ((c⁻¹ * u * c) * (c⁻¹ * v * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * v * c) * (c⁻¹ * u * c)) * c⁻¹ := by rw [key]
    _ = v * u := by group

theorem sec412_two_group [Finite G] {Y C : Subgroup G} (hY : IsElemAbelian 2 Y)
    (hC : IsElemAbelian 2 C)
    (hcomm : ∀ c ∈ C, ∀ y ∈ Y, ∀ z ∈ conjSubgroup c Y, y * z = z * y) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ Y ≤ P ∧ C ≤ P := by
  have hIcomm : ∀ x ∈ sec48Conjs Y C, ∀ y ∈ sec48Conjs Y C, x * y = y * x := by
    intro x hx y hy
    obtain ⟨c, hc, hxc⟩ := mem_sec48Conjs.1 hx
    obtain ⟨d, hd, hyd⟩ := mem_sec48Conjs.1 hy
    exact sec412_conj_comm hcomm hc hd hxc hyd
  have hIsq : ∀ x ∈ sec48Conjs Y C, x * x = 1 := by
    intro x hx
    obtain ⟨c, _, hxc⟩ := mem_sec48Conjs.1 hx
    rw [← sq]
    exact (isElemAbelian_conj hY c).2 x hxc
  have hIconj : ∀ d ∈ C, ∀ x ∈ sec48Conjs Y C, d * x * d⁻¹ ∈ sec48Conjs Y C := by
    intro d hd x hx
    obtain ⟨c, hc, hxc⟩ := mem_sec48Conjs.1 hx
    refine mem_sec48Conjs.2 ⟨d * c, C.mul_mem hd hc, ?_⟩
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hxc ⊢
    rw [show (d * c)⁻¹ * (d * x * d⁻¹) * (d * c) = c⁻¹ * x * c by group]
    exact hxc
  have hE : IsElemAbelian 2 (Subgroup.closure (sec48Conjs Y C)) :=
    sec48_closure_elemAbelian hIcomm hIsq
  have hEp : IsPGroup 2 (Subgroup.closure (sec48Conjs Y C)) :=
    notation_isPGroup_two_of_le hE le_rfl
  have hCp : IsPGroup 2 C := notation_isPGroup_two_of_le hC le_rfl
  have hconjE : ∀ d ∈ C, ∀ x ∈ Subgroup.closure (sec48Conjs Y C),
      d * x * d⁻¹ ∈ Subgroup.closure (sec48Conjs Y C) := by
    intro d hd x hx
    have hle : Subgroup.closure (sec48Conjs Y C) ≤
        (Subgroup.closure (sec48Conjs Y C)).comap (MulAut.conj d).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      exact Subgroup.subset_closure (hIconj d hd y hy)
    exact hle hx
  have hCN : C ≤ normalizer ((Subgroup.closure (sec48Conjs Y C) : Subgroup G) : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconjE d hd x
    · intro hx
      have h3 := hconjE d⁻¹ (C.inv_mem hd) _ hx
      rwa [show d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x by group] at h3
  refine ⟨Subgroup.closure (sec48Conjs Y C) ⊔ C,
    IsPGroup.to_sup_of_normal_left' hEp hCp hCN, ?_, le_sup_right⟩
  intro b hb
  exact Subgroup.mem_sup_left (Subgroup.subset_closure
    (mem_sec48Conjs.2 ⟨1, C.one_mem, by rw [conjSubgroup_one]; exact hb⟩))

theorem sec412_comm_of_le_normalizer [Finite G] {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hBTI : IsTI B) {g : G} (hg : conjSubgroup g B ≤ normalizer (B : Set G)) :
    ∀ b ∈ B, ∀ z ∈ conjSubgroup g B, b * z = z * b := by
  have hE := tim77_2_3 hB hBTI hg
  intro b hb z hz
  exact congrArg Subtype.val
    (hE.1.is_comm.comm ⟨b, Subgroup.mem_sup_left hb⟩ ⟨z, Subgroup.mem_sup_right hz⟩)

theorem sec412_homog_eq {T Tb L Lb M X : Subgroup G} (S : Prop24Setup T Tb L Lb M)
    [Finite G] (hLb : Lb ≠ ⊥)
    (hX : ∀ y ∈ Tb, y ≠ 1 → y ∈ normalizer (T : Set G) →
      T ⊓ centralizer ({y} : Set G) = X ∨ y ∈ centralizer (T : Set G)) : L = X := by
  obtain ⟨⟨y, hyLb⟩, hy1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hLb
  have hy1 : y ≠ 1 := fun e => hy1' (Subtype.ext e)
  have hcent : T ⊓ centralizer ({y} : Set G) = L := by
    ext c
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hcT, hcy⟩
      exact S.mem_L_of_commute hcT (S.mem_Lb.mp hyLb).1 hy1
        ((hcy y (Set.mem_singleton y)).symm)
    · intro hcL
      refine ⟨S.L_le hcL, fun h hh => ?_⟩
      rw [Set.mem_singleton_iff.mp hh]
      exact (S.comm_L_Lb hcL hyLb).symm
  have hyTb : y ∈ Tb := (S.mem_Lb.mp hyLb).1
  have hyN : y ∈ normalizer (T : Set G) := (S.mem_Lb.mp hyLb).2
  rcases hX y hyTb hy1 hyN with h1 | h1
  · exact hcent.symm.trans h1
  · exfalso
    apply S.ne
    have hTc : T ⊓ centralizer ({y} : Set G) = T := by
      apply le_antisymm inf_le_left
      intro t ht
      refine Subgroup.mem_inf.mpr ⟨ht, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact (Subgroup.mem_centralizer_iff.mp h1 t ht).symm
    exact hcent.symm.trans hTc

theorem sec412_eq_of_relIndex_two {X T H : Subgroup G} (h2 : X.relIndex T = 2)
    (hXH : X ≤ H) (hHT : H ≤ T) (hne : H ≠ T) : H = X := by
  have e1 : X.relIndex H * H.relIndex T = X.relIndex T :=
    Subgroup.relIndex_mul_relIndex X H T hXH hHT
  rw [h2] at e1
  have hdvd : H.relIndex T ∣ 2 := Dvd.intro_left _ e1
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (le_antisymm hHT (Subgroup.relIndex_eq_one.mp h)) hne
  · rw [h] at e1
    have hX1 : X.relIndex H = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hX1) hXH

theorem sec412_bad_config [Finite G] (h49 : Tim77Sec49Statement)
    {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2)
    (hA0 : Sec4A0LeCenterH A Abar) {g b x : G} (hbA : b ∈ A)
    (hbad : ¬ ∀ t ∈ conjSubgroup g A, ∀ s ∈ conjSubgroup (b * g) A, t * s = s * t)
    (hxT : x ∈ conjSubgroup g A) (hx1 : x ≠ 1)
    (hxN : x ∈ normalizer (conjSubgroup (b * g) A : Set G)) :
    normalizerIn (conjSubgroup g A) (conjSubgroup (b * g) A) =
        conjSubgroup g (Section3.A0 A Abar) ∧
      normalizerIn (conjSubgroup (b * g) A) (conjSubgroup g A) =
        conjSubgroup (b * g) (Section3.A0 A Abar) ∧
      ∀ l ∈ normalizerIn (conjSubgroup g A) (conjSubgroup (b * g) A),
        ∀ lb ∈ normalizerIn (conjSubgroup (b * g) A) (conjSubgroup g A), l * lb = lb * l := by
  have hbb : b * b = 1 := by
    rw [← sq]
    exact h.hyp.elemAbelian.2 b hbA
  have hconjT : conjSubgroup (b * g) A = conjSubgroup b (conjSubgroup g A) :=
    conjSubgroup_mul b g A
  have hbTb : conjSubgroup b (conjSubgroup (b * g) A) = conjSubgroup g A := by
    rw [← conjSubgroup_mul, show b * (b * g) = g by rw [← mul_assoc, hbb, one_mul]]
  have hTel : IsElemAbelian 2 (conjSubgroup g A) := isElemAbelian_conj h.hyp.elemAbelian g
  have hTti : IsTI (conjSubgroup g A) := isTI_conjSubgroup h.hyp.ti g
  have hTbel : IsElemAbelian 2 (conjSubgroup (b * g) A) :=
    isElemAbelian_conj h.hyp.elemAbelian (b * g)
  have hTbti : IsTI (conjSubgroup (b * g) A) := isTI_conjSubgroup h.hyp.ti (b * g)
  have hLne : normalizerIn (conjSubgroup g A) (conjSubgroup (b * g) A) ≠ ⊥ := by
    intro e
    have hxL : x ∈ normalizerIn (conjSubgroup g A) (conjSubgroup (b * g) A) :=
      Subgroup.mem_inf.mpr ⟨hxT, hxN⟩
    rw [e, Subgroup.mem_bot] at hxL
    exact hx1 hxL
  have hLT : normalizerIn (conjSubgroup g A) (conjSubgroup (b * g) A) ≠
      conjSubgroup g A := by
    intro e
    have hTN : conjSubgroup b (conjSubgroup (b * g) A) ≤
        normalizer (conjSubgroup (b * g) A : Set G) := by
      rw [hbTb]
      intro t ht
      have ht' : t ∈ normalizerIn (conjSubgroup g A) (conjSubgroup (b * g) A) := by
        rw [e]
        exact ht
      exact (Subgroup.mem_inf.mp ht').2
    have hc := sec412_comm_of_le_normalizer hTbel hTbti hTN
    apply hbad
    intro t ht s hs
    exact (hc s hs t (by rw [hbTb]; exact ht)).symm
  let S : Prop24Setup (conjSubgroup g A) (conjSubgroup (b * g) A)
      (normalizerIn (conjSubgroup g A) (conjSubgroup (b * g) A))
      (normalizerIn (conjSubgroup (b * g) A) (conjSubgroup g A))
      (normalizerIn (conjSubgroup g A) (conjSubgroup (b * g) A) ⊔
        normalizerIn (conjSubgroup (b * g) A) (conjSubgroup g A)) :=
    { elem := hTel
      ti := hTti
      conj := ⟨b, hconjT⟩
      hL := rfl
      hLb := rfl
      hM := rfl
      ne_bot := hLne
      ne := hLT }
  have hX : ∀ y ∈ conjSubgroup (b * g) A, y ≠ 1 → y ∈ normalizer (conjSubgroup g A : Set G) →
      conjSubgroup g A ⊓ centralizer ({y} : Set G) = conjSubgroup g (Section3.A0 A Abar) ∨
        y ∈ centralizer (conjSubgroup g A : Set G) := by
    intro y hyTb hy1 hyN
    have hq' : Section3.q (conjSubgroup g A) (conjSubgroup g Abar) = 2 :=
      (section3_q_conj A Abar g).trans hq
    have hA0' : Sec4A0LeCenterH (conjSubgroup g A) (conjSubgroup g Abar) :=
      (sec4A0LeCenterH_conj_iff A Abar g).2 hA0
    have hyT : ∃ k : G, y ∈ conjSubgroup k (conjSubgroup g A) :=
      ⟨b, by rw [← hconjT]; exact hyTb⟩
    have H := (h49 G (conjSubgroup g A) (conjSubgroup g Abar) (conjSubgroup g S₀)
      (conjSubgroup g B) (h.conj g) hq' hA0').2.2.2 y hyN hy1 hyT
    rw [section3_A0_conj] at H
    exact Or.imp Eq.symm id H
  have hX' : ∀ y ∈ conjSubgroup g A, y ≠ 1 → y ∈ normalizer (conjSubgroup (b * g) A : Set G) →
      conjSubgroup (b * g) A ⊓ centralizer ({y} : Set G) =
          conjSubgroup (b * g) (Section3.A0 A Abar) ∨
        y ∈ centralizer (conjSubgroup (b * g) A : Set G) := by
    intro y hyT hy1 hyN
    have hq' : Section3.q (conjSubgroup (b * g) A) (conjSubgroup (b * g) Abar) = 2 :=
      (section3_q_conj A Abar (b * g)).trans hq
    have hA0' : Sec4A0LeCenterH (conjSubgroup (b * g) A) (conjSubgroup (b * g) Abar) :=
      (sec4A0LeCenterH_conj_iff A Abar (b * g)).2 hA0
    have hyTb : ∃ k : G, y ∈ conjSubgroup k (conjSubgroup (b * g) A) :=
      ⟨b, by rw [hbTb]; exact hyT⟩
    have H := (h49 G (conjSubgroup (b * g) A) (conjSubgroup (b * g) Abar)
      (conjSubgroup (b * g) S₀) (conjSubgroup (b * g) B) (h.conj (b * g)) hq' hA0').2.2.2 y
      hyN hy1 hyTb
    rw [section3_A0_conj] at H
    exact Or.imp Eq.symm id H
  exact ⟨sec412_homog_eq S S.Lb_ne_bot hX, sec412_homog_eq S.symm hLne hX',
    fun l hl lb hlb => S.comm_L_Lb hl hlb⟩


theorem sec412_absurd_comm {a x : G} (ha2 : a * a = 1) (hx2 : x * x = 1) (hc : a * x = x * a)
    (hord : orderOf (a * x) = 4) : False := by
  have hsq : (a * x) ^ 2 = 1 := by
    rw [sq]
    calc a * x * (a * x) = a * (x * a) * x := by group
      _ = a * (a * x) * x := by rw [hc]
      _ = (a * a) * (x * x) := by group
      _ = 1 := by rw [ha2, hx2, mul_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [hord] at hdvd
  norm_num at hdvd

theorem sec412_elemAbelian_mono {K E : Subgroup G} (hE : IsElemAbelian 2 E) (hK : K ≤ E) :
    IsElemAbelian 2 K :=
  by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x (hK hx)⟩
  have h := hE.1.is_comm.comm (⟨a.1, hK a.2⟩ : ↥E) ⟨b.1, hK b.2⟩
  have h2 := congrArg Subtype.val h
  exact h2

theorem sec412_conj_involution {A : Subgroup G} {g b x : G} (hbb : b * b = 1)
    (hx : x ∈ conjSubgroup g A) : b * x * b ∈ conjSubgroup (b * g) A := by
  have hinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  rw [conjSubgroup_mul, CFSG.CGT.Timmesfeld75.mem_conjSubgroup, hinv,
    show b * (b * x * b) * b = (b * b) * x * (b * b) by group, hbb, one_mul, mul_one]
  exact hx

theorem sec412_sylow_setup [Finite G] {A S₀' : Subgroup G} (hA : IsElemAbelian 2 A)
    (hS₀ : IsPGroup 2 S₀') (hmax : ∀ T : Subgroup G, IsPGroup 2 T → S₀' ≤ T → T = S₀')
    (hSN : S₀' ≤ normalizer (A : Set G)) {P : Subgroup G} (hP : IsPGroup 2 P) (hPA : A ≤ P) :
    ∃ m : G, IsPGroup 2 (conjSubgroup m S₀') ∧
      (∀ T : Subgroup G, IsPGroup 2 T → conjSubgroup m S₀' ≤ T → T = conjSubgroup m S₀') ∧
      P ≤ conjSubgroup m S₀' ∧ conjSubgroup m A ≤ conjSubgroup m S₀' ∧
      conjSubgroup m S₀' ≤ normalizer (conjSubgroup m A : Set G) := by
  have hAp : IsPGroup 2 A := notation_isPGroup_two_of_le hA le_rfl
  have hA_le : A ≤ S₀' := by
    have hsup : IsPGroup 2 (A ⊔ S₀' : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hAp hS₀ hSN
    exact (le_sup_left : A ≤ A ⊔ S₀').trans (hmax (A ⊔ S₀') hsup le_sup_right).le
  obtain ⟨k, hk⟩ := sec48_sylow_conj hS₀ hmax hP
  refine ⟨k⁻¹, isPGroup_conj_map_t77 hS₀ k⁻¹, fun T hT hST => ?_, ?_, ?_, ?_⟩
  · exact (isPGroup_maximal_conj_t77 k⁻¹ S₀' hS₀ ⊤
      (fun T' hT' _ hST' => hmax T' hT' hST')).2 T hT
      (by rw [conjSubgroup_top_t77]; exact le_top) hST
  · intro x hx
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, inv_inv]
    exact hk x hx
  · exact (conjSubgroup_le_conj_iff k⁻¹).2 hA_le
  · rw [← conjSubgroup_map_normalizer]
    exact (conjSubgroup_le_conj_iff k⁻¹).2 hSN

theorem sec412_isChoice_conj [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {g m : G}
    (hX1 : conjSubgroup g (Section3.A0 A Abar) ≤
      normalizerIn (conjSubgroup g A) (conjSubgroup m A))
    (hne : normalizerIn (conjSubgroup g A) (conjSubgroup m A) ≠ ⊥)
    (hne' : normalizerIn (conjSubgroup g A) (conjSubgroup m A) ≠ conjSubgroup g A) :
    Section3.IsChoice (conjSubgroup m A) (conjSubgroup g A) := by
  refine ⟨⟨g * m⁻¹, ?_⟩, ⟨hne, hne'⟩, ?_⟩
  · rw [conjSubgroup_mul, conjSubgroup_inv_conj_cancel]
  · intro g'' hg''
    obtain ⟨hne2, hne2'⟩ := hg''
    have hD : conjSubgroup g'' (conjSubgroup m A) =
        conjSubgroup m (conjSubgroup (m⁻¹ * g'' * m) A) :=
      conjSubgroup_conj_twist m g'' A
    have e1 : normalizerIn (conjSubgroup g'' (conjSubgroup m A)) (conjSubgroup m A) =
        conjSubgroup m (normalizerIn (conjSubgroup (m⁻¹ * g'' * m) A) A) := by
      rw [hD, normalizerIn_conjSubgroup_t77]
    have hk'1 : normalizerIn (conjSubgroup (m⁻¹ * g'' * m) A) A ≠ ⊥ := by
      intro e
      apply hne2
      rw [e1, e, conjSubgroup_bot_t77]
    have hk'2 : normalizerIn (conjSubgroup (m⁻¹ * g'' * m) A) A ≠
        conjSubgroup (m⁻¹ * g'' * m) A := by
      intro e
      apply hne2'
      rw [e1, hD, e]
    have hcard : Nat.card (normalizerIn (conjSubgroup g'' (conjSubgroup m A))
        (conjSubgroup m A)) = Nat.card (normalizerIn (conjSubgroup (m⁻¹ * g'' * m) A) A) := by
      rw [e1, card_conjSubgroup]
    have hX : Nat.card (Section3.A0 A Abar) ≤
        Nat.card (normalizerIn (conjSubgroup g A) (conjSubgroup m A)) := by
      rw [← card_conjSubgroup g (Section3.A0 A Abar)]
      exact Subgroup.card_le_of_le hX1
    rw [hcard]
    calc Nat.card (normalizerIn (conjSubgroup (m⁻¹ * g'' * m) A) A)
        ≤ Nat.card (Section3.Abar0 A Abar) := h.nota.choice.2.2 _ ⟨hk'1, hk'2⟩
      _ = Nat.card (Section3.A0 A Abar) := h.setup.card_Lb_eq
      _ ≤ Nat.card (normalizerIn (conjSubgroup g A) (conjSubgroup m A)) := hX

theorem sec412_B1_contra [Finite G] (h47 : Tim77Sec47Statement)
    {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2)
    {g m x : G} {S₀' : Subgroup G} (hx1 : x ≠ 1)
    (hxX1 : x ∈ conjSubgroup g (Section3.A0 A Abar)) (hxN : x ∉ normalizer (A : Set G))
    (hS : IsPGroup 2 (conjSubgroup m S₀'))
    (hSmax : ∀ T : Subgroup G, IsPGroup 2 T → conjSubgroup m S₀' ≤ T → T = conjSubgroup m S₀')
    (hSN : conjSubgroup m S₀' ≤ normalizer (conjSubgroup m A : Set G))
    (hCS : conjSubgroup m A ≤ conjSubgroup m S₀') (hAS : A ≤ conjSubgroup m S₀')
    (hX1S : conjSubgroup g (Section3.A0 A Abar) ≤ conjSubgroup m S₀')
    (hTN : ¬ conjSubgroup g A ≤ normalizer (conjSubgroup m A : Set G)) : False := by
  have hA_el : IsElemAbelian 2 A := h.hyp.elemAbelian
  have hC_el : IsElemAbelian 2 (conjSubgroup m A) := isElemAbelian_conj hA_el m
  have hC_ti : IsTI (conjSubgroup m A) := isTI_conjSubgroup h.hyp.ti m
  have hA_N : conjSubgroup m⁻¹ (conjSubgroup m A) ≤
      normalizer (conjSubgroup m A : Set G) := by
    rw [conjSubgroup_inv_conj_cancel]
    exact hAS.trans hSN
  have hCA : ∀ c ∈ conjSubgroup m A, ∀ z ∈ A, c * z = z * c := by
    have hc := sec412_comm_of_le_normalizer hC_el hC_ti hA_N
    intro c hc' z hz
    exact hc c hc' z (by rw [conjSubgroup_inv_conj_cancel]; exact hz)
  have hA0A : Section3.A0 A Abar ≤ A := inf_le_left
  have hX1T : conjSubgroup g (Section3.A0 A Abar) ≤ conjSubgroup g A :=
    (conjSubgroup_le_conj_iff g).2 hA0A
  have hX1N : conjSubgroup g (Section3.A0 A Abar) ≤
      normalizerIn (conjSubgroup g A) (conjSubgroup m A) := fun y hy =>
    Subgroup.mem_inf.mpr ⟨hX1T hy, hSN (hX1S hy)⟩
  have h2A0 : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [← h.setup.relIndex_Lb]
    exact hq
  have h2X : (conjSubgroup g (Section3.A0 A Abar)).relIndex (conjSubgroup g A) = 2 := by
    rw [relIndex_conjSubgroup_t77]
    exact h2A0
  have hne_ne : normalizerIn (conjSubgroup g A) (conjSubgroup m A) ≠ conjSubgroup g A := by
    intro e
    apply hTN
    intro t ht
    have ht' : t ∈ normalizerIn (conjSubgroup g A) (conjSubgroup m A) := by
      rw [e]
      exact ht
    exact (Subgroup.mem_inf.mp ht').2
  have hEq : normalizerIn (conjSubgroup g A) (conjSubgroup m A) =
      conjSubgroup g (Section3.A0 A Abar) :=
    sec412_eq_of_relIndex_two h2X hX1N inf_le_left hne_ne
  have hne : normalizerIn (conjSubgroup g A) (conjSubgroup m A) ≠ ⊥ := by
    intro e
    have hxN' := hX1N hxX1
    rw [e, Subgroup.mem_bot] at hxN'
    exact hx1 hxN'
  have hqC : Section3.q (conjSubgroup m A) (conjSubgroup g A) = 2 := by
    show (normalizerIn (conjSubgroup g A) (conjSubgroup m A)).relIndex (conjSubgroup g A) = 2
    rw [hEq, relIndex_conjSubgroup_t77]
    exact h2A0
  have hchoice : Section3.IsChoice (conjSubgroup m A) (conjSubgroup g A) :=
    sec412_isChoice_conj h hX1N hne hne_ne
  have hnota : Section3.Notation (conjSubgroup m A) (conjSubgroup g A) (conjSubgroup m S₀') A :=
    { choice := hchoice
      sylow := ⟨hS, hSN, fun T' hT' _ hST' => hSmax T' hT' hST'⟩
      contains := sup_le hCS (by
        show normalizerIn (conjSubgroup g A) (conjSubgroup m A) ≤ conjSubgroup m S₀'
        rw [hEq]
        exact hX1S)
      conj := ⟨m⁻¹, (conjSubgroup_inv_conj_cancel m A).symm⟩
      ne := by
        intro e
        apply hxN
        have hxC : x ∈ normalizer (conjSubgroup m A : Set G) := hSN (hX1S hxX1)
        rw [← e] at hxC
        exact hxC
      le := by
        intro a ha
        refine Subgroup.mem_inf.mpr ⟨hAS ha, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        exact hCA c hc a ha }
  have hctx : Sec3Ctx (conjSubgroup m A) (conjSubgroup g A) (conjSubgroup m S₀') A :=
    { hyp := elementaryAbelianTIRootCentralizerHypothesis_conj_t77 h.hyp m
      not_root := (h.conj m).not_root
      not_wc := (h.conj m).not_wc
      nota := hnota }
  have hres := h47 G (conjSubgroup m A) (conjSubgroup g A) (conjSubgroup m S₀') A hctx hqC A
    ⟨m⁻¹, (conjSubgroup_inv_conj_cancel m A).symm⟩ hAS
  have hxA : x ∈ normalizer (A : Set G) := by
    apply hres
    show x ∈ normalizerIn (conjSubgroup g A) (conjSubgroup m A)
    rw [hEq]
    exact hxX1
  exact hxN hxA

theorem sec412_of
    (h47 : Tim77Sec47Statement) : Tim77Sec412Statement := by
  intro G _ _ A Abar S₀ B h hq hA0 a ha ha0 g x hx hord
  have h49 : Tim77Sec49Statement := tim77Sec49_holds
  have h48 : Tim77Sec48Statement := sec48_of h47
  have h411 : Tim77Sec411Statement := sec411_of h48
  by_contra hxN
  have hA_el : IsElemAbelian 2 A := h.hyp.elemAbelian
  have hA_ti : IsTI A := h.hyp.ti
  have hT_el : IsElemAbelian 2 (conjSubgroup g A) := isElemAbelian_conj hA_el g
  have hx2 : x * x = 1 := by
    rw [← sq]
    exact hT_el.2 x hx
  have hx1 : x ≠ 1 := by
    intro e
    apply hxN
    rw [e]
    exact Subgroup.one_mem _
  have ha2 : a * a = 1 := by
    rw [← sq]
    exact hA_el.2 a ha
  have hcommi := sec412_comm_conj h49 h hq hA0 ha ha0 hx hord
  have hii : ∀ b ∈ A, b ≠ 1 → x * (b * x * b) = (b * x * b) * x := by
    intro b hb hb1
    have hbb : b * b = 1 := by
      rw [← sq]
      exact hA_el.2 b hb
    exact (sec412_orderOf_mul_x hA_ti hx2 hb hb1 hbb hxN hcommi).2
  have hxNb : ∀ b ∈ A, x ∈ normalizer (conjSubgroup (b * g) A : Set G) := by
    intro b hb
    by_cases hb1 : b = 1
    · subst hb1
      rw [one_mul]
      exact Subgroup.le_normalizer hx
    · have hbb : b * b = 1 := by
        rw [← sq]
        exact hA_el.2 b hb
      have hy := sec412_conj_involution hbb hx
      have hy1 : b * x * b ≠ 1 := by
        intro e
        apply hx1
        calc x = b * (b * x * b) * b := by
              rw [show b * (b * x * b) * b = (b * b) * x * (b * b) by group, hbb, one_mul,
                mul_one]
          _ = 1 := by rw [e, mul_one, hbb]
      exact mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hA_ti (b * g)) hy hy1
        (hii b hb hb1)
  by_cases hbad : ∃ b ∈ A, ¬ ∀ t ∈ conjSubgroup g A, ∀ s ∈ conjSubgroup (b * g) A,
      t * s = s * t
  ·
    obtain ⟨b₀, hb₀A, hb₀bad⟩ := hbad
    obtain ⟨hcfg1, -, -⟩ := sec412_bad_config h49 h hq hA0 hb₀A hb₀bad hx hx1 (hxNb b₀ hb₀A)
    have hX1x : x ∈ conjSubgroup g (Section3.A0 A Abar) := by
      rw [← hcfg1]
      exact Subgroup.mem_inf.mpr ⟨hx, hxNb b₀ hb₀A⟩
    have hA0A : Section3.A0 A Abar ≤ A := inf_le_left
    have hX1_el : IsElemAbelian 2 (conjSubgroup g (Section3.A0 A Abar)) :=
      isElemAbelian_conj (sec412_elemAbelian_mono hA_el hA0A) g
    have hfam : ∀ c ∈ A, ∀ y ∈ conjSubgroup g (Section3.A0 A Abar),
        ∀ z ∈ conjSubgroup c (conjSubgroup g (Section3.A0 A Abar)), y * z = z * y := by
      intro c hc y hy z hz
      by_cases hgood : ∀ t ∈ conjSubgroup g A, ∀ s ∈ conjSubgroup (c * g) A, t * s = s * t
      · have hyT : y ∈ conjSubgroup g A := (conjSubgroup_le_conj_iff g).2 hA0A hy
        have hzT : z ∈ conjSubgroup (c * g) A := by
          have hz2 := (conjSubgroup_le_conj_iff c).2 ((conjSubgroup_le_conj_iff g).2 hA0A) hz
          rw [← conjSubgroup_mul] at hz2
          exact hz2
        exact hgood y hyT z hzT
      · obtain ⟨hc1, hc2, hc3⟩ := sec412_bad_config h49 h hq hA0 hc hgood hx hx1 (hxNb c hc)
        have hy' : y ∈ normalizerIn (conjSubgroup g A) (conjSubgroup (c * g) A) := by
          rw [hc1]
          exact hy
        have hz' : z ∈ normalizerIn (conjSubgroup (c * g) A) (conjSubgroup g A) := by
          rw [hc2, conjSubgroup_mul]
          exact hz
        exact hc3 y hy' z hz'
    obtain ⟨P, hP, hX1P, hAP⟩ := sec412_two_group hX1_el hA_el hfam
    obtain ⟨S₀', hS₀, hmaxS, hS₀N⟩ := h.hyp.sylow
    obtain ⟨m, hS, hSmax, hPS, hCS, hSN⟩ :=
      sec412_sylow_setup hA_el hS₀ hmaxS hS₀N hP hAP
    have hAS : A ≤ conjSubgroup m S₀' := hAP.trans hPS
    have hX1S : conjSubgroup g (Section3.A0 A Abar) ≤ conjSubgroup m S₀' := hX1P.trans hPS
    have hC_el : IsElemAbelian 2 (conjSubgroup m A) := isElemAbelian_conj hA_el m
    have hC_ti : IsTI (conjSubgroup m A) := isTI_conjSubgroup hA_ti m
    have hA_N : conjSubgroup m⁻¹ (conjSubgroup m A) ≤
        normalizer (conjSubgroup m A : Set G) := by
      rw [conjSubgroup_inv_conj_cancel]
      exact hAS.trans hSN
    have hCA : ∀ c ∈ conjSubgroup m A, ∀ z ∈ A, c * z = z * c := by
      have hc := sec412_comm_of_le_normalizer hC_el hC_ti hA_N
      intro c hc' z hz
      exact hc c hc' z (by rw [conjSubgroup_inv_conj_cancel]; exact hz)
    by_cases hTC : conjSubgroup g A = conjSubgroup m A
    ·
      have hxC : x ∈ conjSubgroup m A := by
        rw [← hTC]
        exact hx
      exact sec412_absurd_comm ha2 hx2 (hCA x hxC a ha).symm hord
    · by_cases hTN' : conjSubgroup g A ≤ normalizer (conjSubgroup m A : Set G)
      ·
        have hTeq : conjSubgroup (g * m⁻¹) (conjSubgroup m A) = conjSubgroup g A := by
          rw [conjSubgroup_mul, conjSubgroup_inv_conj_cancel]
        have hTN'' : conjSubgroup (g * m⁻¹) (conjSubgroup m A) ≤
            normalizer (conjSubgroup m A : Set G) := by
          rw [hTeq]
          exact hTN'
        have hcomm3 := sec412_comm_of_le_normalizer hC_el hC_ti hTN''
        have hTle : conjSubgroup (g * m⁻¹) (conjSubgroup m A) ≤
            centralizer (conjSubgroup m A : Set G) := by
          intro t ht
          rw [Subgroup.mem_centralizer_iff]
          intro c hc
          exact hcomm3 c hc t ht
        have hRT :=
          (elementaryAbelianTIRootCentralizerHypothesis_conj_t77 h.hyp m).rootTypeInCentralizer
            (g * m⁻¹) hTle
        rw [hTeq] at hRT
        obtain ⟨-, -, -, hnorm⟩ := hRT
        have hb₀C : b₀ ∈ centralizer (conjSubgroup m A : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro c hc
          exact hCA c hc b₀ hb₀A
        have hxN' : x ∈ normalizer (conjSubgroup b₀ (conjSubgroup g A) : Set G) := by
          rw [← conjSubgroup_mul]
          exact hxNb b₀ hb₀A
        have hne3 : normalizerIn (conjSubgroup g A) (conjSubgroup b₀ (conjSubgroup g A)) ≠ ⊥ := by
          intro e
          have hxm : x ∈ normalizerIn (conjSubgroup g A) (conjSubgroup b₀ (conjSubgroup g A)) :=
            Subgroup.mem_inf.mpr ⟨hx, hxN'⟩
          rw [e, Subgroup.mem_bot] at hxm
          exact hx1 hxm
        have hcomm_b := hnorm b₀ hb₀C hne3
        apply hb₀bad
        intro t ht s hs
        have hs' : s ∈ conjSubgroup b₀ (conjSubgroup g A) := by
          rw [conjSubgroup_mul] at hs
          exact hs
        exact hcomm_b t ht s hs'
      ·
        exact sec412_B1_contra h47 h hq hx1 hX1x hxN hS hSmax hSN hCS hAS hX1S hTN'
  ·
    have hbad' : ∀ b ∈ A, ∀ t ∈ conjSubgroup g A, ∀ s ∈ conjSubgroup (b * g) A,
        t * s = s * t := fun b hb t ht s hs => by
      by_contra hc
      exact hbad ⟨b, hb, fun hall => hc (hall t ht s hs)⟩
    have hTcomm : ∀ c ∈ A, ∀ y ∈ conjSubgroup g A, ∀ z ∈ conjSubgroup c (conjSubgroup g A),
        y * z = z * y := by
      intro c hc y hy z hz
      have hz' : z ∈ conjSubgroup (c * g) A := by
        rw [conjSubgroup_mul]
        exact hz
      exact hbad' c hc y hy z hz'
    obtain ⟨P, hP, hTP, hAP⟩ := sec412_two_group hT_el hA_el hTcomm
    obtain ⟨k, hk⟩ := sec48_conj_into_S0 h hP
    have hkA : conjSubgroup k A ≤ S₀ := by
      intro u hu
      obtain ⟨a', ha', rfl⟩ := (mem_conjSubgroup_exists_t77 k A _).1 hu
      exact hk a' (hAP ha')
    have hkT : conjSubgroup k (conjSubgroup g A) ≤ S₀ := by
      intro v hv
      obtain ⟨a', ha', rfl⟩ := (mem_conjSubgroup_exists_t77 k (conjSubgroup g A) _).1 hv
      exact hk a' (hTP ha')
    have hkgA : conjSubgroup (k * g) A ≤ S₀ := by
      rw [conjSubgroup_mul]
      exact hkT
    have hE := h411 G A Abar S₀ B h hq hA0
    have hsupA : ∀ u ∈ conjSubgroup k A,
        u ∈ ⨆ (g' : G) (_ : conjSubgroup g' A ≤ S₀), conjSubgroup g' A := fun u hu =>
      Subgroup.mem_iSup_of_mem k (by rw [iSup_pos hkA]; exact hu)
    have hsupT : ∀ v ∈ conjSubgroup k (conjSubgroup g A),
        v ∈ ⨆ (g' : G) (_ : conjSubgroup g' A ≤ S₀), conjSubgroup g' A := fun v hv =>
      Subgroup.mem_iSup_of_mem (k * g) (by
        rw [iSup_pos hkgA, conjSubgroup_mul]
        exact hv)
    have hcomm_k : ∀ u ∈ conjSubgroup k A, ∀ v ∈ conjSubgroup k (conjSubgroup g A),
        u * v = v * u := by
      intro u hu v hv
      have key := hE.1.is_comm.comm (⟨u, hsupA u hu⟩ : ↥(⨆ (g' : G) (_ : conjSubgroup g' A ≤ S₀),
        conjSubgroup g' A)) ⟨v, hsupT v hv⟩
      have key2 := congrArg Subtype.val key
      exact key2
    have hax : a * x = x * a := by
      have hk1 := hcomm_k (k * a * k⁻¹) ((mem_conjSubgroup_exists_t77 k A _).2 ⟨a, ha, rfl⟩)
        (k * x * k⁻¹) ((mem_conjSubgroup_exists_t77 k (conjSubgroup g A) _).2 ⟨x, hx, rfl⟩)
      calc a * x = k⁻¹ * ((k * a * k⁻¹) * (k * x * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * x * k⁻¹) * (k * a * k⁻¹)) * k := by rw [hk1]
        _ = x * a := by group
    exact sec412_absurd_comm ha2 hx2 hax hord

end CFSG.RankThree.GF2n.Tim77
