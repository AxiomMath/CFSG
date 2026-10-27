module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.S14610P0
public import CFSG.Quasithin.EmptyFaithful.S1469Sev

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem conj_mem_omegaOneCenterOf_of_normalizer {S : Subgroup G} {g a : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (ha : a ∈ omegaOneCenterOf S) :
    g * a * g⁻¹ ∈ omegaOneCenterOf S := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (S : Set G) := (Subgroup.normalizer (S : Set G)).inv_mem hg
  unfold omegaOneCenterOf omegaOneOf at ha ⊢
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    obtain ⟨hxc, hx2⟩ := hx
    have hxS : x ∈ S := hxc.1
    have hxC : x ∈ Subgroup.centralizer (S : Set G) := hxc.2
    have hgC : g * x * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hs' : g⁻¹ * s * g ∈ S := by
        have := (Subgroup.mem_normalizer_iff.mp hg' s).mp hs
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hxC _ hs'
      calc s * (g * x * g⁻¹) = g * ((g⁻¹ * s * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by rw [hc]
        _ = (g * x * g⁻¹) * s := by group
    refine ⟨⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxS, hgC⟩, ?_⟩
    calc (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hx2]; group
  | one => simp
  | mul x y _ _ ihx ihy =>
    simpa [mul_assoc] using Subgroup.mul_mem _ ihx ihy
  | inv x _ ih =>
    simpa [mul_assoc] using Subgroup.inv_mem _ ih

theorem Setting146.vz_le_wOf1469 {H : Subgroup G} {u : G} {I I₂ : Subgroup G}
    (c : Facts14610 T M H u I I₂) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) :
    VZ T M ≤ wOf1469 (oTwoUpper I) := by
  have S : Setting146 G T M := c.setting
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hV4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  obtain ⟨hVred, -⟩ := S.hyp1281.isTwoReducedIn
  have hVab : ∀ a ∈ VZ T M, ∀ b ∈ VZ T M, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVred.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVsq : ∀ a ∈ VZ T M, a * a = 1 := fun a ha => by
    simpa [sq] using hVred.2.2.1.2 a ha
  have hy : ∃ y ∈ yOfL22 T M ⊓ I, Odd (orderOf y) ∧ y ∉ mcOf T := by
    by_contra hcon
    push Not at hcon
    exact S.not_lI_le_mcOf hLT ((Subgroup.closure_le _).mpr fun y hy => hcon y hy.1 hy.2)
  obtain ⟨y, hyLI, hyodd, hyG⟩ := hy
  obtain ⟨z, hzZ, hzy⟩ : ∃ z ∈ quasithinOmegaOneCenter T, ¬ (z * y = y * z) := by
    by_contra hno
    push Not at hno
    exact hyG (Subgroup.mem_centralizer_iff.mpr hno)
  have hzT : z ∈ T := S146T.Z_le hzZ
  have hzV : z ∈ VZ T M := le_conjClosure _ _ hzZ
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hzy (by simp)
  have hz2 : z ^ 2 = 1 := S146T.Z_sq hzZ
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have huQ : u ∈ pCoreOf 2 (mcOf T) := S.conjClosure_le_pCoreOf_mcOf c.hH c.hu.mem
  have hQ1T : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_mcOf_le
  have hzu : z ∈ tU T u := (S146T.mem_tU_iff).mpr ⟨hzT,
    commutatorElement_eq_one_iff_mul_comm.mpr (S146T.comm_Z_T (hQ1T huQ) hzZ).symm⟩
  have hzI : z ∈ I := c.hI.1.1.1 hzu
  have hyL : y ∈ yOfL22 T M := hyLI.1
  have hyI : y ∈ I := hyLI.2
  have hyM : y ∈ M := S.hyp1281.le hyL
  obtain ⟨z', hz'def⟩ : ∃ z' : G, z' = y * z * y⁻¹ := ⟨_, rfl⟩
  have hz'V : z' ∈ VZ T M := hz'def ▸ (Subgroup.mem_normalizer_iff.mp (hMV hyM) z).mp hzV
  have hz'I : z' ∈ I := hz'def ▸ I.mul_mem (I.mul_mem hyI hzI) (I.inv_mem hyI)
  have hz'z : z' ≠ z := by
    intro h
    apply hzy
    have h1 : y * z * y⁻¹ = z := hz'def ▸ h
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    have h1 : y * z * y⁻¹ = 1 := hz'def ▸ h
    calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  have hz'z' : z' * z' = 1 := hVsq z' hz'V
  obtain ⟨z'', hz''def⟩ : ∃ z'' : G, z'' = y * z' * y⁻¹ := ⟨_, rfl⟩
  have hz''V : z'' ∈ VZ T M := hz''def ▸ (Subgroup.mem_normalizer_iff.mp (hMV hyM) z').mp hz'V
  have hz''1 : z'' ≠ 1 := by
    intro h
    apply hz'1
    have h1 : y * z' * y⁻¹ = 1 := hz''def ▸ h
    calc z' = y⁻¹ * (y * z' * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  have hz''z' : z'' ≠ z' := by
    intro h
    apply hz'z
    have h1 : y * z' * y⁻¹ = y * z * y⁻¹ := by
      rw [← hz''def, h]
      exact hz'def
    exact mul_left_cancel (mul_right_cancel h1)
  have hz''z : z'' ≠ z := by
    intro h
    apply hzy
    obtain ⟨m, hm⟩ := hyodd
    have h1 : y * (y * z * y⁻¹) * y⁻¹ = z := by
      rw [← hz'def, ← hz''def]
      exact h
    have hc : (y * y) * z = z * (y * y) := by
      calc y * y * z = y * (y * z * y⁻¹) * y⁻¹ * (y * y) := by group
        _ = z * (y * y) := by rw [h1]
    have hcp : ∀ k : ℕ, (y * y) ^ k * z = z * (y * y) ^ k := fun k =>
      ((Commute.pow_left (show Commute (y * y) z from hc) k) : Commute ((y * y) ^ k) z)
    have hyy : (y * y) ^ (m + 1) = y := by
      rw [← pow_two, ← pow_mul]
      have : 2 * (m + 1) = orderOf y + 1 := by omega
      rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
    have := hcp (m + 1)
    rw [hyy] at this
    exact this.symm
  have hzz'V : z * z' ∈ VZ T M := (VZ T M).mul_mem hzV hz'V
  have hd1 : z * z' ≠ 1 := by
    intro h
    apply hz'z
    have : z' = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_eq_of_mul_eq_one_right hzz
  have hdz : z * z' ≠ z := fun h => hz'1 (mul_eq_left.mp h)
  have hdz' : z * z' ≠ z' := fun h => hz1 (mul_eq_right.mp h)
  have hall : ∀ w ∈ VZ T M, w = 1 ∨ w = z ∨ w = z' ∨ w = z * z' := by
    intro w hw
    rcases eq_or_eq_or_eq_or_eq_of_card_four hV4 (a := (1 : VZ T M)) (b := ⟨z, hzV⟩)
      (c := ⟨z', hz'V⟩) (d := ⟨z * z', hzz'V⟩)
      (fun he => hz1 (congrArg Subtype.val he).symm) (fun he => hz'1 (congrArg Subtype.val he).symm)
      (fun he => hd1 (congrArg Subtype.val he).symm) (fun he => hz'z (congrArg Subtype.val he).symm)
      (fun he => hdz (congrArg Subtype.val he).symm) (fun he => hdz' (congrArg Subtype.val he).symm)
      ⟨w, hw⟩ with h | h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))
  have hz''eq : z'' = z * z' := by
    rcases hall z'' hz''V with h | h | h | h
    · exact absurd h hz''1
    · exact absurd h hz''z
    · exact absurd h hz''z'
    · exact h
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'z'
  have hyz'' : y * z'' * y⁻¹ = z := by
    calc y * z'' * y⁻¹ = y * (z * z') * y⁻¹ := by rw [hz''eq]
      _ = (y * z * y⁻¹) * (y * z' * y⁻¹) := by group
      _ = z' * z'' := by rw [← hz'def, ← hz''def]
      _ = z' * (z * z') := by rw [hz''eq]
      _ = (z' * z) * z' := (mul_assoc z' z z').symm
      _ = (z * z') * z' := by rw [hVab z' hz'V z hzV]
      _ = z * (z' * z') := mul_assoc z z' z'
      _ = z := by rw [hz'z', mul_one]
  set K : Subgroup G := oTwoUpper I with hKdef
  have hKI : K ≤ I := oTwoUpper_le I
  have hKn : I ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper I
  have hyK : y ∈ K := mem_oTwoUpper_of_odd hyI hyodd
  have hzy'K : z' * y⁻¹ * z'⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hKn hz'I) y⁻¹).mp (K.inv_mem hyK)
  have hzK : z ∈ K := by
    have e : z = y * (z' * y⁻¹ * z'⁻¹) := by
      calc z = (z * z') * z'⁻¹ := by group
        _ = z'' * z'⁻¹ := by rw [hz''eq]
        _ = y * z' * y⁻¹ * z'⁻¹ := by rw [hz''def]
        _ = y * (z' * y⁻¹ * z'⁻¹) := by group
    rw [e]
    exact K.mul_mem hyK hzy'K
  have hO2T : pCoreOf 2 I ≤ T := (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl).trans inf_le_left
  have hzO2I : z ∈ pCoreOf 2 I :=
    c.c4 ⟨hzI, Subgroup.mem_centralizer_iff.mpr fun p hp => S146T.comm_Z_T (hO2T hp) hzZ⟩
  have hO2KI : pCoreOf 2 K ≤ pCoreOf 2 I :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKI)
      (hKn.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hzO2K : z ∈ pCoreOf 2 K := by
    have h : pCoreOf 2 I ⊓ K ≤ pCoreOf 2 K :=
      le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_pCoreOf 2 I (hKI hk), Subgroup.le_normalizer hk⟩)
        ((pCoreOf_isPGroup 2 I).to_le inf_le_left)
    exact h ⟨hzO2I, hzK⟩
  have hzcent : z ∈ Subgroup.centralizer (pCoreOf 2 K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun p hp => S146T.comm_Z_T (hO2T (hO2KI hp)) hzZ
  have hzA : z ∈ omegaOneCenterOf (pCoreOf 2 K) := Subgroup.subset_closure ⟨⟨hzO2K, hzcent⟩, hz2⟩
  have hyN : y ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K hyK
  have hz'A : z' ∈ omegaOneCenterOf (pCoreOf 2 K) := by
    rw [hz'def]
    exact conj_mem_omegaOneCenterOf_of_normalizer hyN hzA
  have hz''A : z'' ∈ omegaOneCenterOf (pCoreOf 2 K) := by
    rw [hz''eq]
    exact (omegaOneCenterOf (pCoreOf 2 K)).mul_mem hzA hz'A
  have hzW : z ∈ wOf1469 K := by
    have h1 : ⁅z', y⁆ ∈ wOf1469 K := Subgroup.commutator_mem_commutator hz'A hyK
    have h2 := (wOf1469 K).inv_mem h1
    have e : z = ⁅z', y⁆⁻¹ := by
      rw [commutatorElement_def]
      calc z = y * z' * y⁻¹ * z'⁻¹ := by rw [← hz''def, hz''eq]; group
        _ = (z' * y * z'⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact h2
  have hz'W : z' ∈ wOf1469 K := by
    have h1 : ⁅z'', y⁆ ∈ wOf1469 K := Subgroup.commutator_mem_commutator hz''A hyK
    have h2 := (wOf1469 K).inv_mem h1
    have hzz''inv : z * z''⁻¹ = z' := by
      rw [hz''eq, mul_inv_rev, hzinv, hz'inv]
      calc z * (z' * z) = (z * z') * z := (mul_assoc z z' z).symm
        _ = (z' * z) * z := by rw [hVab z hzV z' hz'V]
        _ = z' * (z * z) := mul_assoc z' z z
        _ = z' := by rw [hzz, mul_one]
    have e : z' = ⁅z'', y⁆⁻¹ := by
      rw [commutatorElement_def]
      calc z' = z * z''⁻¹ := hzz''inv.symm
        _ = y * z'' * y⁻¹ * z''⁻¹ := by rw [hyz'']
        _ = (z'' * y * z''⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact h2
  intro w hw
  rcases hall w hw with rfl | rfl | rfl | rfl
  · exact (wOf1469 K).one_mem
  · exact hzW
  · exact hz'W
  · exact (wOf1469 K).mul_mem hzW hz'W

end CFSG.Quasithin
