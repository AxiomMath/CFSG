module

public import CFSG.RankThree.GF2n.Tim77.Sec3Notation
public import CFSG.RankThree.GF2n.Tim77.Sec3Conj
public import CFSG.RankThree.GF2n.Tim77Prop24Inv
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.RankThree.GF2n.Tim77.Sec3Basic

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

theorem sec48_conj_trans {A B C : Subgroup G} {g h : G} (hB : B = conjSubgroup g A)
    (hC : C = conjSubgroup h A) : ∃ k : G, C = conjSubgroup k B := by
  subst hB hC
  exact ⟨h * g⁻¹, by rw [conjSubgroup_mul, conjSubgroup_inv_conj_cancel]⟩

theorem sec48_comm_of_sq {b x : G} (hb : b * b = 1) (hx : x * x = 1)
    (h : (b * x) * (b * x) = 1) : b * x = x * b := by
  have h1 := inv_eq_of_mul_eq_one_right h
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right hx] at h1
  exact h1.symm

theorem sec48_no_comm [Finite G] {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    {B C : Subgroup G} (hB : ∃ g : G, B = conjSubgroup g A) (hC : ∃ h : G, C = conjSubgroup h A)
    (hnc : ¬ ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hord : ∀ b ∈ B, b ≠ 1 → ∀ c ∈ C, c ≠ 1 → orderOf (b * c) = 2 ∨ orderOf (b * c) = 4) :
    ∀ b ∈ B, b ≠ 1 → ∀ c ∈ C, c ≠ 1 → b * c ≠ c * b := by
  obtain ⟨g, rfl⟩ := hB
  obtain ⟨h, rfl⟩ := hC
  intro b hb hb1 c hc hc1 hbc
  have hBTI : IsTI (conjSubgroup g A) := isTI_conjSubgroup hTI g
  have hBel : IsElemAbelian 2 (conjSubgroup g A) := isElemAbelian_conj hA g
  have hCel : IsElemAbelian 2 (conjSubgroup h A) := isElemAbelian_conj hA h
  have hCTI : IsTI (conjSubgroup h A) := isTI_conjSubgroup hTI h
  have hCB : conjSubgroup h A = conjSubgroup (h * g⁻¹) (conjSubgroup g A) := by
    rw [conjSubgroup_mul, conjSubgroup_inv_conj_cancel]
  have e : conjSubgroup (g * h⁻¹) (conjSubgroup h A) = conjSubgroup g A := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hbN : b ∈ normalizer (conjSubgroup h A : Set G) :=
    mem_normalizer_of_commute_of_isTI hCTI hc hc1 hbc
  have hN : normalizerIn (conjSubgroup g A) (conjSubgroup h A) ≠ ⊥ := by
    intro h0
    have hmem : b ∈ normalizerIn (conjSubgroup g A) (conjSubgroup h A) :=
      Subgroup.mem_inf.mpr ⟨hb, hbN⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact hb1 hmem
  by_cases hLB : normalizerIn (conjSubgroup g A) (conjSubgroup h A) = conjSubgroup g A
  ·
    apply hnc
    have hBN : conjSubgroup g A ≤ normalizer (conjSubgroup h A : Set G) := by
      intro x hx
      have hx' : x ∈ normalizerIn (conjSubgroup g A) (conjSubgroup h A) := by
        rw [hLB]
        exact hx
      exact (Subgroup.mem_inf.mp hx').2
    have hk : conjSubgroup (g * h⁻¹) (conjSubgroup h A) ≤
        normalizer (conjSubgroup h A : Set G) := by
      rw [e]
      exact hBN
    have hel := tim77_2_3 hCel hCTI hk
    rw [e] at hel
    intro x hx y hy
    exact congrArg Subtype.val
      (hel.1.is_comm.comm ⟨x, Subgroup.mem_sup_right hx⟩ ⟨y, Subgroup.mem_sup_left hy⟩)
  ·
    exfalso
    have S : Prop24Setup (conjSubgroup g A) (conjSubgroup h A)
        (normalizerIn (conjSubgroup g A) (conjSubgroup h A))
        (normalizerIn (conjSubgroup h A) (conjSubgroup g A))
        (normalizerIn (conjSubgroup g A) (conjSubgroup h A) ⊔
          normalizerIn (conjSubgroup h A) (conjSubgroup g A)) :=
      { elem := hBel
        ti := hBTI
        conj := ⟨h * g⁻¹, hCB⟩
        hL := rfl
        hLb := rfl
        hM := rfl
        ne_bot := hN
        ne := hLB }
    obtain ⟨a, ha, haL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
    obtain ⟨c', hc', hc'L⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
    have hodd := S.odd_orderOf_mul ha haL hc' hc'L
    have ha1 : a ≠ 1 := fun e1 => haL (by rw [e1]; exact Subgroup.one_mem _)
    have hc'1 : c' ≠ 1 := fun e1 => hc'L (by rw [e1]; exact Subgroup.one_mem _)
    obtain ⟨m, hm⟩ := hodd
    rcases hord a ha ha1 c' hc' hc'1 with h2 | h4 <;> omega

theorem sec48_comm_conj [Finite G] {B C : Subgroup G} (hBel : IsElemAbelian 2 B)
    (hBTI : IsTI B) (hCel : IsElemAbelian 2 C)
    (hord : ∀ b ∈ B, b ≠ 1 → ∀ c ∈ C, c ≠ 1 → orderOf (b * c) = 2 ∨ orderOf (b * c) = 4)
    {c : G} (hc : c ∈ C) : ∀ b ∈ B, ∀ y ∈ conjSubgroup c B, b * y = y * b := by
  have hc2 : c * c = 1 := by
    rw [← sq]
    exact hCel.2 c hc
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hTel : IsElemAbelian 2 (conjSubgroup c B) := isElemAbelian_conj hBel c
  have hTTI : IsTI (conjSubgroup c B) := isTI_conjSubgroup hBTI c
  have hBN : ∀ b ∈ B, b ∈ normalizer (conjSubgroup c B : Set G) := by
    intro b hb
    by_cases hb1 : b = 1
    · rw [hb1]
      exact Subgroup.one_mem _
    have hx : c * b * c⁻¹ ∈ conjSubgroup c B :=
      mem_conjSubgroup.mpr (by
        rw [show c⁻¹ * (c * b * c⁻¹) * c = b by group]
        exact hb)
    have hx1 : c * b * c⁻¹ ≠ 1 := fun e1 => hb1 ((conj_eq_one_iff_t77 c b).1 e1)
    have hx2 : (c * b * c⁻¹) * (c * b * c⁻¹) = 1 := by
      rw [← sq]
      exact hTel.2 _ hx
    have hb2 : b * b = 1 := by
      rw [← sq]
      exact hBel.2 b hb
    have hcomm : b * (c * b * c⁻¹) = (c * b * c⁻¹) * b := by
      by_cases hc1 : c = 1
      · rw [hc1]
        simp
      · have hu : orderOf (b * c) = 2 ∨ orderOf (b * c) = 4 := hord b hb hb1 c hc hc1
        have hdvd : orderOf (b * c) ∣ 4 := by
          rcases hu with h | h <;> rw [h] <;> norm_num
        have h4 : (b * c) ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
        have e1 : b * (c * b * c⁻¹) = (b * c) * (b * c) := by
          rw [hcinv]
          group
        have hsq : (b * (c * b * c⁻¹)) * (b * (c * b * c⁻¹)) = 1 := by
          rw [e1]
          calc (b * c) * (b * c) * ((b * c) * (b * c)) = (b * c) ^ 4 := by
                simp only [pow_succ, pow_zero, one_mul, mul_assoc]
            _ = 1 := h4
        exact sec48_comm_of_sq hb2 hx2 hsq
    exact mem_normalizer_of_commute_of_isTI hTTI hx hx1 hcomm
  have hle : conjSubgroup c⁻¹ (conjSubgroup c B) ≤ normalizer (conjSubgroup c B : Set G) := by
    rw [conjSubgroup_inv_conj_cancel]
    intro b hb
    exact hBN b hb
  have hel := tim77_2_3 hTel hTTI hle
  rw [conjSubgroup_inv_conj_cancel] at hel
  intro b hb y hy
  exact (congrArg Subtype.val
    (hel.1.is_comm.comm ⟨y, Subgroup.mem_sup_left hy⟩ ⟨b, Subgroup.mem_sup_right hb⟩)).symm

def sec48Conjs (B C : Subgroup G) : Set G := {x | ∃ c ∈ C, x ∈ conjSubgroup c B}

theorem mem_sec48Conjs {B C : Subgroup G} {x : G} :
    x ∈ sec48Conjs B C ↔ ∃ c ∈ C, x ∈ conjSubgroup c B := Iff.rfl

theorem sec48_conjs_comm [Finite G] {B C : Subgroup G} (hBel : IsElemAbelian 2 B)
    (hBTI : IsTI B) (hCel : IsElemAbelian 2 C)
    (hord : ∀ b ∈ B, b ≠ 1 → ∀ c ∈ C, c ≠ 1 → orderOf (b * c) = 2 ∨ orderOf (b * c) = 4)
    {c d x y : G} (hc : c ∈ C) (hd : d ∈ C) (hx : x ∈ conjSubgroup c B)
    (hy : y ∈ conjSubgroup d B) : x * y = y * x := by
  obtain ⟨b1, hb1, rfl⟩ := (mem_conjSubgroup_exists_t77 c B x).1 hx
  obtain ⟨b2, hb2, rfl⟩ := (mem_conjSubgroup_exists_t77 d B y).1 hy
  have he : c⁻¹ * d ∈ C := C.mul_mem (C.inv_mem hc) hd
  have hyc : c⁻¹ * (d * b2 * d⁻¹) * c ∈ conjSubgroup (c⁻¹ * d) B := by
    rw [mem_conjSubgroup,
      show (c⁻¹ * d)⁻¹ * (c⁻¹ * (d * b2 * d⁻¹) * c) * (c⁻¹ * d) = b2 by group]
    exact hb2
  have key := sec48_comm_conj hBel hBTI hCel hord he b1 hb1 _ hyc
  have e1 : c * (c⁻¹ * (d * b2 * d⁻¹) * c) * c⁻¹ = d * b2 * d⁻¹ := by group
  have h2 := (conj_mul_comm_t77 c b1 _).2 key
  rw [e1] at h2
  exact h2

theorem sec48_closure_elemAbelian {S : Set G} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (h2 : ∀ x ∈ S, x * x = 1) : IsElemAbelian 2 (Subgroup.closure S) := by
  have h1 : ∀ x ∈ S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      intro s hs
      show s ∈ Subgroup.centralizer ({x} : Set G)
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hS x hx s hs
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy)) x (Set.mem_singleton x)
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      intro s hs
      show s ∈ Subgroup.centralizer ({x} : Set G)
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact (h1 s hs x hx).symm
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy)) x (Set.mem_singleton x)
  have hexp : ∀ x ∈ Subgroup.closure S, x ^ 2 = 1 := by
    intro x hx
    rw [sq]
    refine Subgroup.closure_induction (p := fun x _ => x * x = 1)
      (fun s hs => h2 s hs) ?_ ?_ ?_ hx
    · exact mul_one 1
    · intro a b ha hb hab hbb
      have hab' : a * b = b * a := hcomm a ha b hb
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab']
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [hab, hbb, mul_one]
    · intro a _ hab
      rw [inv_eq_of_mul_eq_one_right hab]
      exact hab
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, fun x hx => hexp x hx⟩

theorem sec48_two_group [Finite G] {B C : Subgroup G} (hBel : IsElemAbelian 2 B)
    (hBTI : IsTI B) (hCel : IsElemAbelian 2 C)
    (hord : ∀ b ∈ B, b ≠ 1 → ∀ c ∈ C, c ≠ 1 → orderOf (b * c) = 2 ∨ orderOf (b * c) = 4) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ B ≤ P ∧ C ≤ P := by
  have hIcomm : ∀ x ∈ sec48Conjs B C, ∀ y ∈ sec48Conjs B C, x * y = y * x := by
    intro x hx y hy
    obtain ⟨c, hc, hxc⟩ := mem_sec48Conjs.1 hx
    obtain ⟨d, hd, hyd⟩ := mem_sec48Conjs.1 hy
    exact sec48_conjs_comm hBel hBTI hCel hord hc hd hxc hyd
  have hIsq : ∀ x ∈ sec48Conjs B C, x * x = 1 := by
    intro x hx
    obtain ⟨c, _, hxc⟩ := mem_sec48Conjs.1 hx
    rw [← sq]
    exact (isElemAbelian_conj hBel c).2 x hxc
  have hIconj : ∀ d ∈ C, ∀ x ∈ sec48Conjs B C, d * x * d⁻¹ ∈ sec48Conjs B C := by
    intro d hd x hx
    obtain ⟨c, hc, hxc⟩ := mem_sec48Conjs.1 hx
    refine mem_sec48Conjs.2 ⟨d * c, C.mul_mem hd hc, ?_⟩
    rw [mem_conjSubgroup] at hxc ⊢
    rw [show (d * c)⁻¹ * (d * x * d⁻¹) * (d * c) = c⁻¹ * x * c by group]
    exact hxc
  have hE : IsElemAbelian 2 (Subgroup.closure (sec48Conjs B C)) :=
    sec48_closure_elemAbelian hIcomm hIsq
  have hEp : IsPGroup 2 (Subgroup.closure (sec48Conjs B C)) :=
    notation_isPGroup_two_of_le hE le_rfl
  have hCp : IsPGroup 2 C := notation_isPGroup_two_of_le hCel le_rfl
  have hconjE : ∀ d ∈ C, ∀ x ∈ Subgroup.closure (sec48Conjs B C),
      d * x * d⁻¹ ∈ Subgroup.closure (sec48Conjs B C) := by
    intro d hd x hx
    have hle : Subgroup.closure (sec48Conjs B C) ≤
        (Subgroup.closure (sec48Conjs B C)).comap (MulAut.conj d).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      exact Subgroup.subset_closure (hIconj d hd y hy)
    exact hle hx
  have hCN : C ≤ normalizer ((Subgroup.closure (sec48Conjs B C) : Subgroup G) : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconjE d hd x
    · intro hx
      have h3 := hconjE d⁻¹ (C.inv_mem hd) _ hx
      rwa [show d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x by group] at h3
  refine ⟨Subgroup.closure (sec48Conjs B C) ⊔ C,
    IsPGroup.to_sup_of_normal_left' hEp hCp hCN, ?_, le_sup_right⟩
  intro b hb
  exact Subgroup.mem_sup_left (Subgroup.subset_closure
    (mem_sec48Conjs.2 ⟨1, C.one_mem, by rw [conjSubgroup_one]; exact hb⟩))

theorem sec48_mem_smul_sylow {P : Sylow 2 G} {k z : G} :
    z ∈ ((k • P : Sylow 2 G) : Subgroup G) ↔ k⁻¹ * z * k ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem sec48_sylow_conj [Finite G] {S : Subgroup G} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup G, IsPGroup 2 T → S ≤ T → T = S) {P : Subgroup G}
    (hP : IsPGroup 2 P) : ∃ k : G, ∀ x ∈ P, k * x * k⁻¹ ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS.exists_le_sylow
  have hQS : (Q : Subgroup G) = S := hmax _ Q.isPGroup' hQ
  obtain ⟨R, hR⟩ := hP.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G R Q
  refine ⟨k, fun x hx => ?_⟩
  rw [← hQS, ← hk]
  refine sec48_mem_smul_sylow.2 ?_
  rw [show k⁻¹ * (k * x * k⁻¹) * k = x by group]
  exact hR hx

theorem sec48_exists_conj_le_S0 [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (A : Set G)) :
    ∃ n ∈ normalizer (A : Set G), ∀ b ∈ P, n * b * n⁻¹ ∈ S₀ := by
  obtain ⟨Q, hQ⟩ := notation_exists_sylow_le h.isPGroup_s0 h.s0_le_normalizer
  have hQS : (Q : Subgroup ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype = S₀ :=
    h.nota.sylow.2.2 _ (notation_sylow_map_max Q).1 (notation_sylow_map_max Q).2.1 hQ
  obtain ⟨n, hn, hnP⟩ := notation_exists_conj_le_sylow hP hPN Q
  refine ⟨n, hn, fun b hb => ?_⟩
  rw [← hQS]
  exact hnP b hb

theorem sec48_conj_into_S0 [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {P : Subgroup G} (hP : IsPGroup 2 P) : ∃ k : G, ∀ x ∈ P, k * x * k⁻¹ ∈ S₀ := by
  obtain ⟨S, hS, hmax, hSN⟩ := h.hyp.sylow
  obtain ⟨k₁, hk₁⟩ := sec48_sylow_conj hS hmax hP
  have hP' : IsPGroup 2 (conjSubgroup k₁ P) := isPGroup_conj_map_t77 hP k₁
  have hP'N : conjSubgroup k₁ P ≤ normalizer (A : Set G) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_conjSubgroup_exists_t77 k₁ P _).1 hy
    exact hSN (hk₁ x hx)
  obtain ⟨n, -, hn⟩ := sec48_exists_conj_le_S0 h hP' hP'N
  refine ⟨n * k₁, fun x hx => ?_⟩
  have h3 := hn (k₁ * x * k₁⁻¹) ((mem_conjSubgroup_exists_t77 k₁ P _).2 ⟨x, hx, rfl⟩)
  rwa [show n * k₁ * x * (n * k₁)⁻¹ = n * (k₁ * x * k₁⁻¹) * n⁻¹ by group]

theorem sec48_not_le_normalizer [Finite G] {A Abar S₀ B B'' : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hB : ∃ g : G, B'' = conjSubgroup g A) (hBS : B'' ≤ S₀) :
    ¬ Abar ≤ normalizer (B'' : Set G) := by
  intro hAbN
  obtain ⟨g1, rfl⟩ := hB
  obtain ⟨g0, hg0⟩ := h.exists_abar_eq
  have hAbN' : conjSubgroup g0 A ≤ normalizer (conjSubgroup g1 A : Set G) := by
    rw [← hg0]
    exact hAbN
  have hB1N : conjSubgroup g1 A ≤ normalizer (A : Set G) := hBS.trans h.s0_le_normalizer
  have hAB := tim77_2_3 h.hyp.elemAbelian h.hyp.ti hB1N
  have hAcomm : ∀ a ∈ A, ∀ b ∈ conjSubgroup g1 A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val
      (hAB.1.is_comm.comm ⟨a, Subgroup.mem_sup_left ha⟩ ⟨b, Subgroup.mem_sup_right hb⟩)
  have hBel : IsElemAbelian 2 (conjSubgroup g1 A) := isElemAbelian_conj h.hyp.elemAbelian g1
  have hBTI : IsTI (conjSubgroup g1 A) := isTI_conjSubgroup h.hyp.ti g1
  have e : conjSubgroup (g0 * g1⁻¹) (conjSubgroup g1 A) = conjSubgroup g0 A := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hAB' := tim77_2_3 hBel hBTI (g := g0 * g1⁻¹) (by rw [e]; exact hAbN')
  rw [e] at hAB'
  have hAbcomm : ∀ x ∈ conjSubgroup g0 A, ∀ b ∈ conjSubgroup g1 A, b * x = x * b :=
    fun x hx b hb => congrArg Subtype.val
      (hAB'.1.is_comm.comm ⟨b, Subgroup.mem_sup_left hb⟩ ⟨x, Subgroup.mem_sup_right hx⟩)
  have hX : A ⊔ Abar ≤ centralizer (conjSubgroup g1 A : Set G) := by
    rw [hg0, sup_le_iff]
    constructor
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hAcomm a ha b hb).symm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hAbcomm x hx b hb
  have hA_le : conjSubgroup g1⁻¹ (conjSubgroup g1 A) ≤
      centralizer (conjSubgroup g1 A : Set G) := by
    rw [conjSubgroup_inv_conj_cancel]
    intro a ha
    exact (sup_le_iff.mp hX).1 ha
  have hrt := (elementaryAbelianTIRootCentralizerHypothesis_conj_t77 h.hyp g1).rootTypeInCentralizer
    g1⁻¹ hA_le
  rw [conjSubgroup_inv_conj_cancel] at hrt
  obtain ⟨-, -, -, hnorm⟩ := hrt
  obtain ⟨x, hxX, hxeq⟩ := h.setup.exists_conj_eq
  have hxC : x ∈ centralizer (conjSubgroup g1 A : Set G) := hX hxX
  have hne : normalizerIn A (conjSubgroup x A) ≠ ⊥ := by
    rw [← hxeq]
    exact h.a0_ne_bot
  have hcomm' := hnorm x hxC hne
  have hAN : A ≤ normalizer (Abar : Set G) := by
    apply le_normalizer_of_comm
    intro a ha b hb
    apply hcomm' a ha b
    rw [← hxeq]
    exact hb
  apply h.a0_ne
  unfold Section3.A0 normalizerIn
  exact le_antisymm inf_le_left (le_inf le_rfl hAN)

theorem sec48_setup [Finite G] {A Abar S₀ B C' : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hC : ∃ g : G, C' = conjSubgroup g A)
    (hA0 : Section3.Abar0 A Abar ≤ normalizer (C' : Set G))
    (hnot : ¬ Abar ≤ normalizer (C' : Set G)) :
    Prop24Setup Abar C' (normalizerIn Abar C') (normalizerIn C' Abar)
      (normalizerIn Abar C' ⊔ normalizerIn C' Abar) := by
  obtain ⟨g0, hg0⟩ := h.exists_abar_eq
  obtain ⟨g2, hg2⟩ := hC
  obtain ⟨k, hk⟩ := sec48_conj_trans hg0 hg2
  have hL0 : normalizerIn Abar A ≤ normalizerIn Abar C' := fun x hx =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hA0 hx⟩
  have hel : IsElemAbelian 2 Abar := by
    rw [hg0]
    exact isElemAbelian_conj h.hyp.elemAbelian g0
  have hti : IsTI Abar := by
    rw [hg0]
    exact isTI_conjSubgroup h.hyp.ti g0
  refine
    { elem := hel
      ti := hti
      conj := ⟨k, hk⟩
      hL := rfl
      hLb := rfl
      hM := rfl
      ne_bot := ?_
      ne := ?_ }
  · intro e
    apply h.nota.choice.2.1.1
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ normalizerIn Abar C' := hL0 hx
    rw [e] at hx'
    exact hx'
  · intro e
    apply hnot
    intro x hx
    have hx' : x ∈ normalizerIn Abar C' := by
      rw [e]
      exact hx
    exact (Subgroup.mem_inf.mp hx').2

theorem sec48_card_sup [Finite G] {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hinf : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hKN : K ≤ normalizer (H : Set G) :=
    le_normalizer_of_comm fun k hk h hh => (hcomm h hh k hk).symm
  let f : H × K → ↥(H ⊔ K) := fun p =>
    ⟨p.1.1 * p.2.1, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨h1, hh1⟩, ⟨k1, hk1⟩⟩ ⟨⟨h2, hh2⟩, ⟨k2, hk2⟩⟩ hpq
      have hpq' : h1 * k1 = h2 * k2 := congrArg Subtype.val hpq
      have e : h2⁻¹ * h1 = k2 * k1⁻¹ := by
        calc h2⁻¹ * h1 = h2⁻¹ * (h1 * k1) * k1⁻¹ := by group
          _ = h2⁻¹ * (h2 * k2) * k1⁻¹ := by rw [hpq']
          _ = k2 * k1⁻¹ := by group
      have hmem : h2⁻¹ * h1 ∈ H ⊓ K := by
        refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem hh2) hh1, ?_⟩
        rw [e]
        exact K.mul_mem hk2 (K.inv_mem hk1)
      rw [hinf, Subgroup.mem_bot] at hmem
      have hkk : k2 * k1⁻¹ = 1 := by
        rw [← e]
        exact hmem
      have hh : h1 = h2 := (inv_mul_eq_one.mp hmem).symm
      have hk : k1 = k2 := (mul_inv_eq_one.mp hkk).symm
      subst hh hk
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨v, hv, u, hu, rfl⟩ := exists_mul_of_mem_sup hKN hx
      exact ⟨(⟨v, hv⟩, ⟨u, hu⟩), rfl⟩
  calc Nat.card ↥(H ⊔ K) = Nat.card (↥H × ↥K) := (Nat.card_eq_of_bijective f hf).symm
    _ = Nat.card H * Nat.card K := Nat.card_prod _ _

theorem sec48_L_eq [Finite G] {A Abar S₀ B C' : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hC : ∃ g : G, C' = conjSubgroup g A)
    (hA0 : Section3.Abar0 A Abar ≤ normalizer (C' : Set G))
    (hnot : ¬ Abar ≤ normalizer (C' : Set G)) :
    normalizerIn Abar C' = Section3.Abar0 A Abar ∧
      Nat.card (normalizerIn C' Abar) = Nat.card (Section3.Abar0 A Abar) := by
  have S := sec48_setup h hC hA0 hnot
  obtain ⟨g0, hg0⟩ := h.exists_abar_eq
  obtain ⟨g2, hg2⟩ := hC
  have hL0 : normalizerIn Abar A ≤ normalizerIn Abar C' := fun x hx =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hA0 hx⟩
  have e1 : conjSubgroup (g0⁻¹ * g2) A = conjSubgroup g0⁻¹ C' := by
    rw [conjSubgroup_mul, hg2]
  have e2 : conjSubgroup g0⁻¹ Abar = A := by
    rw [hg0, conjSubgroup_inv_conj_cancel]
  have hT : normalizerIn (conjSubgroup (g0⁻¹ * g2) A) A =
      conjSubgroup g0⁻¹ (normalizerIn C' Abar) := by
    have h3 := normalizerIn_conjSubgroup_t77 g0⁻¹ C' Abar
    rw [e2] at h3
    rw [e1]
    exact h3
  have hLne : normalizerIn C' Abar ≠ ⊥ := S.Lb_ne_bot
  have hLne' : normalizerIn C' Abar ≠ C' := S.Lb_ne
  have hne1 : normalizerIn (conjSubgroup (g0⁻¹ * g2) A) A ≠ ⊥ := by
    rw [hT]
    intro e
    exact hLne ((conjSubgroup_eq_bot_t77 g0⁻¹ _).1 e)
  have hne2 : normalizerIn (conjSubgroup (g0⁻¹ * g2) A) A ≠ conjSubgroup (g0⁻¹ * g2) A := by
    rw [hT, e1]
    intro e
    exact hLne' (conjSubgroup_inj_t77 g0⁻¹ e)
  have hcard : Nat.card (normalizerIn C' Abar) ≤ Nat.card (Section3.Abar0 A Abar) := by
    have hm := h.nota.choice.2.2 (g0⁻¹ * g2) ⟨hne1, hne2⟩
    rwa [hT, card_conjSubgroup] at hm
  have hcard' : Nat.card (normalizerIn Abar C') ≤ Nat.card (Section3.Abar0 A Abar) := by
    rw [← S.card_Lb_eq]
    exact hcard
  have hL : normalizerIn Abar C' = Section3.Abar0 A Abar :=
    (Subgroup.eq_of_le_of_card_ge hL0 hcard').symm
  exact ⟨hL, by rw [S.card_Lb_eq, hL]⟩

theorem sec48_ctx_conj [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hq : Section3.q A Abar = 2) {c : G} (hcS : c ∈ S₀) :
    Sec3Ctx A (conjSubgroup c Abar) S₀ B ∧ Section3.q A (conjSubgroup c Abar) = 2 ∧
      Section3.Abar0 A (conjSubgroup c Abar) = conjSubgroup c (Section3.Abar0 A Abar) := by
  have hcN : c ∈ normalizer (A : Set G) := h.s0_le_normalizer hcS
  have hcA : conjSubgroup c A = A := conjSubgroup_eq_self_iff.mpr hcN
  have hN0 : normalizerIn (conjSubgroup c Abar) A = conjSubgroup c (normalizerIn Abar A) := by
    have h3 := normalizerIn_conjSubgroup_t77 c Abar A
    rw [hcA] at h3
    exact h3
  obtain ⟨g0, hg0⟩ := h.exists_abar_eq
  have hne0 : normalizerIn Abar A ≠ ⊥ := h.nota.choice.2.1.1
  have hne1 : normalizerIn Abar A ≠ Abar := h.nota.choice.2.1.2
  have hchoice : Section3.IsChoice A (conjSubgroup c Abar) := by
    refine ⟨⟨c * g0, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [hg0, conjSubgroup_mul]
    · rw [hN0]
      intro e
      exact hne0 ((conjSubgroup_eq_bot_t77 c _).1 e)
    · rw [hN0]
      intro e
      exact hne1 (conjSubgroup_inj_t77 c e)
    · intro g hg
      have hm := h.nota.choice.2.2 g hg
      rw [hN0, card_conjSubgroup]
      exact hm
  have hcontains : A ⊔ Section3.Abar0 A (conjSubgroup c Abar) ≤ S₀ := by
    refine sup_le h.a_le_s0 ?_
    intro x hx
    have hx' : x ∈ conjSubgroup c (normalizerIn Abar A) := by
      rw [← hN0]
      exact hx
    obtain ⟨y, hy, rfl⟩ := (mem_conjSubgroup_exists_t77 c _ x).1 hx'
    exact S₀.mul_mem (S₀.mul_mem hcS (h.abar0_le_s0 hy)) (S₀.inv_mem hcS)
  have hnota : Section3.Notation A (conjSubgroup c Abar) S₀ B :=
    { choice := hchoice
      sylow := h.nota.sylow
      contains := hcontains
      conj := h.nota.conj
      ne := h.nota.ne
      le := h.nota.le }
  have hq' : Section3.q A (conjSubgroup c Abar) = 2 := by
    have h3 := section3_q_conj A Abar c
    rw [hcA] at h3
    exact h3.trans hq
  exact ⟨⟨h.hyp, h.not_root, h.not_wc, hnota⟩, hq', hN0⟩

theorem sec48_Lb_le [Finite G] {A Abar S₀ B C' : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hC : ∃ g : G, C' = conjSubgroup g A) (hC'S : C' ≤ S₀)
    (hA0 : Section3.Abar0 A Abar ≤ normalizer (C' : Set G))
    (hnot : ¬ Abar ≤ normalizer (C' : Set G)) {c : G} (hcC : c ∈ C')
    (hcLb : c ∉ normalizerIn C' Abar) :
    normalizerIn C' Abar ≤ Section3.Abar0 A Abar ⊔ conjSubgroup c (Section3.Abar0 A Abar) := by
  have S := sec48_setup h hC hA0 hnot
  obtain ⟨hL, hcardLb⟩ := sec48_L_eq h hC hA0 hnot
  obtain ⟨g0, hg0⟩ := h.exists_abar_eq
  have hATI : IsTI Abar := by
    rw [hg0]
    exact isTI_conjSubgroup h.hyp.ti g0
  have hcN : c ∈ normalizer ((normalizerIn Abar C' ⊔ normalizerIn C' Abar : Subgroup G) :
      Set G) := S.sup_le_normalizer_M (Subgroup.mem_sup_right hcC)
  have hxM : Section3.Abar0 A Abar ≤ normalizerIn Abar C' ⊔ normalizerIn C' Abar := fun x hx =>
    Subgroup.mem_sup_left (by
      rw [hL]
      exact hx)
  have hconjM : conjSubgroup c (Section3.Abar0 A Abar) ≤
      normalizerIn Abar C' ⊔ normalizerIn C' Abar := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_conjSubgroup_exists_t77 c _ y).1 hy
    exact (Subgroup.mem_normalizer_iff.mp hcN x).mp (hxM hx)
  have hsub : Section3.Abar0 A Abar ⊔ conjSubgroup c (Section3.Abar0 A Abar) ≤
      normalizerIn Abar C' ⊔ normalizerIn C' Abar := sup_le hxM hconjM
  have hcomm : ∀ x ∈ Section3.Abar0 A Abar, ∀ y ∈ conjSubgroup c (Section3.Abar0 A Abar),
      x * y = y * x := fun x hx y hy => S.comm_M (hxM hx) (hconjM hy)
  have hinf1 : Abar ⊓ conjSubgroup c Abar = ⊥ := by
    apply inf_conjSubgroup_eq_bot_of_isTI hATI
    intro e
    apply hcLb
    have hcN' : c ∈ normalizer (Abar : Set G) := conjSubgroup_eq_self_iff.mp e
    exact Subgroup.mem_inf.mpr ⟨hcC, hcN'⟩
  have hinf : Section3.Abar0 A Abar ⊓ conjSubgroup c (Section3.Abar0 A Abar) = ⊥ := by
    have hle : Section3.Abar0 A Abar ⊓ conjSubgroup c (Section3.Abar0 A Abar) ≤
        Abar ⊓ conjSubgroup c Abar :=
      inf_le_inf (fun x hx => (Subgroup.mem_inf.mp hx).1)
        ((conjSubgroup_le_conj_iff c).2 (fun x hx => (Subgroup.mem_inf.mp hx).1))
    exact le_bot_iff.mp (hle.trans_eq hinf1)
  have hinfL : normalizerIn Abar C' ⊓ normalizerIn C' Abar = ⊥ := by
    have hle : normalizerIn Abar C' ⊓ normalizerIn C' Abar ≤ Abar ⊓ C' :=
      inf_le_inf (fun x hx => (Subgroup.mem_inf.mp hx).1)
        (fun x hx => (Subgroup.mem_inf.mp hx).1)
    exact le_bot_iff.mp (hle.trans_eq S.inf_eq_bot)
  have hMcard : Nat.card ↥(normalizerIn Abar C' ⊔ normalizerIn C' Abar) =
      Nat.card (Section3.Abar0 A Abar) * Nat.card (Section3.Abar0 A Abar) := by
    rw [sec48_card_sup (fun x hx y hy => S.comm_L_Lb hx hy) hinfL, S.card_Lb_eq, hL]
  have hH'card : Nat.card ↥(Section3.Abar0 A Abar ⊔ conjSubgroup c (Section3.Abar0 A Abar)) =
      Nat.card (Section3.Abar0 A Abar) * Nat.card (Section3.Abar0 A Abar) := by
    rw [sec48_card_sup hcomm hinf, card_conjSubgroup]
  have hMeq : Section3.Abar0 A Abar ⊔ conjSubgroup c (Section3.Abar0 A Abar) =
      normalizerIn Abar C' ⊔ normalizerIn C' Abar :=
    Subgroup.eq_of_le_of_card_ge hsub (hMcard.trans hH'card.symm).le
  intro y hy
  rw [hMeq]
  exact Subgroup.mem_sup_right hy

theorem sec48_core [Finite G] (h47 : Tim77Sec47Statement) {A Abar S₀ B : Subgroup G}
    (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2) {B' C' : Subgroup G}
    (hB' : ∃ g : G, B' = conjSubgroup g A) (hC' : ∃ g : G, C' = conjSubgroup g A)
    (hB'S : B' ≤ S₀) (hC'S : C' ≤ S₀)
    (hord : ∀ b ∈ B', b ≠ 1 → ∀ c ∈ C', c ≠ 1 → orderOf (b * c) = 2 ∨ orderOf (b * c) = 4) :
    ∀ b ∈ B', ∀ c ∈ C', b * c = c * b := by
  by_contra hnc
  have hstep := sec48_no_comm h.hyp.elemAbelian h.hyp.ti hB' hC' hnc hord
  have hB'el : IsElemAbelian 2 B' := by
    obtain ⟨g, hg⟩ := hB'
    rw [hg]
    exact isElemAbelian_conj h.hyp.elemAbelian g
  have hC'el : IsElemAbelian 2 C' := by
    obtain ⟨g, hg⟩ := hC'
    rw [hg]
    exact isElemAbelian_conj h.hyp.elemAbelian g
  have hB'ne : B' ≠ ⊥ := by
    obtain ⟨g, hg⟩ := hB'
    rw [hg]
    exact fun e => h.setup.A_ne_bot ((conjSubgroup_eq_bot_t77 g A).1 e)
  have hB'N : Section3.Abar0 A Abar ≤ normalizer (B' : Set G) :=
    h47 G A Abar S₀ B h hq B' hB' hB'S
  have hC'N : Section3.Abar0 A Abar ≤ normalizer (C' : Set G) :=
    h47 G A Abar S₀ B h hq C' hC' hC'S
  have hC'not := sec48_not_le_normalizer h hC' hC'S
  have hS := sec48_setup h hC' hC'N hC'not
  obtain ⟨c, hcC, hcLb⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hS.Lb_le hS.Lb_ne)
  obtain ⟨hctx', hq', hconj⟩ := sec48_ctx_conj h hq (hC'S hcC)
  have hB'c := h47 G A (conjSubgroup c Abar) S₀ B hctx' hq' B' hB' hB'S
  have hC'c := h47 G A (conjSubgroup c Abar) S₀ B hctx' hq' C' hC' hC'S
  rw [hconj] at hB'c hC'c
  have hLb := sec48_Lb_le h hC' hC'S hC'N hC'not hcC hcLb
  have hLbN : normalizerIn C' Abar ≤ normalizer (B' : Set G) :=
    hLb.trans (sup_le hB'N hB'c)
  obtain ⟨⟨c₀, hc₀⟩, hc₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS.Lb_ne_bot
  have hc₀1 : c₀ ≠ 1 := fun e => hc₀1' (Subtype.ext e)
  have hc₀C : c₀ ∈ C' := (Subgroup.mem_inf.mp hc₀).1
  have hc₀N : c₀ ∈ normalizer (B' : Set G) := hLbN hc₀
  have hc₀sq : c₀ * c₀ = 1 := by
    rw [← sq]
    exact hC'el.2 c₀ hc₀C
  obtain ⟨x, hxB', hx1, hcx⟩ := exists_ne_one_commute hB'el hB'ne hc₀N hc₀sq
  exact hstep x hxB' hx1 c₀ hc₀C hc₀1 hcx.symm

theorem sec48_of (h47 : Tim77Sec47Statement) : Tim77Sec48Statement := by
  intro G _ _ A Abar S₀ B h hq B' C' hB' hC' hord
  have hB'el : IsElemAbelian 2 B' := by
    obtain ⟨g, hg⟩ := hB'
    rw [hg]
    exact isElemAbelian_conj h.hyp.elemAbelian g
  have hB'TI : IsTI B' := by
    obtain ⟨g, hg⟩ := hB'
    rw [hg]
    exact isTI_conjSubgroup h.hyp.ti g
  have hC'el : IsElemAbelian 2 C' := by
    obtain ⟨g, hg⟩ := hC'
    rw [hg]
    exact isElemAbelian_conj h.hyp.elemAbelian g
  obtain ⟨P, hP, hBP, hCP⟩ := sec48_two_group hB'el hB'TI hC'el hord
  obtain ⟨k, hk⟩ := sec48_conj_into_S0 h hP
  have hB''conj : ∃ g : G, conjSubgroup k B' = conjSubgroup g A := by
    obtain ⟨g, hg⟩ := hB'
    exact ⟨k * g, by rw [hg, conjSubgroup_mul]⟩
  have hC''conj : ∃ g : G, conjSubgroup k C' = conjSubgroup g A := by
    obtain ⟨g, hg⟩ := hC'
    exact ⟨k * g, by rw [hg, conjSubgroup_mul]⟩
  have hB''S : conjSubgroup k B' ≤ S₀ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_conjSubgroup_exists_t77 k B' y).1 hy
    exact hk x (hBP hx)
  have hC''S : conjSubgroup k C' ≤ S₀ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_conjSubgroup_exists_t77 k C' y).1 hy
    exact hk x (hCP hx)
  have hord'' : ∀ b ∈ conjSubgroup k B', b ≠ 1 → ∀ c ∈ conjSubgroup k C', c ≠ 1 →
      orderOf (b * c) = 2 ∨ orderOf (b * c) = 4 := by
    intro y hy hy1 z hz hz1
    obtain ⟨b, hb, rfl⟩ := (mem_conjSubgroup_exists_t77 k B' y).1 hy
    obtain ⟨c, hc, rfl⟩ := (mem_conjSubgroup_exists_t77 k C' z).1 hz
    have hb1 : b ≠ 1 := fun e => hy1 (by rw [e]; group)
    have hc1 : c ≠ 1 := fun e => hz1 (by rw [e]; group)
    have e : k * b * k⁻¹ * (k * c * k⁻¹) = k * (b * c) * k⁻¹ := by group
    rw [e, orderOf_conjugate_t77]
    exact hord b hb hb1 c hc hc1
  have core := sec48_core h47 h hq hB''conj hC''conj hB''S hC''S hord''
  intro b hb c hc
  have h3 := core (k * b * k⁻¹) ((mem_conjSubgroup_exists_t77 k B' _).2 ⟨b, hb, rfl⟩)
    (k * c * k⁻¹) ((mem_conjSubgroup_exists_t77 k C' _).2 ⟨c, hc, rfl⟩)
  exact (conj_mul_comm_t77 k b c).1 h3

end CFSG.RankThree.GF2n.Tim77
