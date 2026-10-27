module

public import CFSG.Quasithin.Background.SimsE214NatCoord
public import CFSG.Quasithin.Background.SimsE214Eleven
public import CFSG.Quasithin.Background.SimsE213M

public section

open scoped commutatorElement

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E214N

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem sq_eq_one_of_conj {X T M V : Subgroup Γ} {g : Γ} (hp : E2.Pair X T M V g)
    (hconj : ∀ x ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V), x ∉ V ⊓ B6.conjSub g V →
      ∀ b ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V), b ∉ V ⊓ B6.conjSub g V →
        ∃ i ∈ X, (i * b * i⁻¹)⁻¹ * x ∈ V ⊓ B6.conjSub g V) :
    ∀ x ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V), x ^ 2 = 1 := by
  intro x hx
  by_cases hxZ : x ∈ V ⊓ B6.conjSub g V
  · exact hp.elem.2 x hxZ.1
  obtain ⟨b, hbB, hbZ⟩ : ∃ b ∈ kerIn M X ⊓ V, b ∉ V ⊓ B6.conjSub g V := by
    by_contra hno
    push Not at hno
    apply hxZ
    have hBZ : kerIn M X ⊓ V ≤ V ⊓ B6.conjSub g V := fun b hb => hno b hb
    have hAZ : B6.conjSub g (kerIn M X ⊓ V) ≤ V ⊓ B6.conjSub g V :=
      ((B6.conjSub g).monotone hBZ).trans (hp.conjSub_inf_conj hp.mem).le
    exact (sup_le hBZ hAZ) hx
  obtain ⟨i, hiX, hz⟩ := hconj x hx hxZ b (le_sup_left (a := kerIn M X ⊓ V) hbB) hbZ
  have hyX : i * b * i⁻¹ ∈ X := X.mul_mem (X.mul_mem hiX (hp.V_le hbB.2)) (X.inv_mem hiX)
  have hzc := hp.mem_center hz hyX
  have hb2 : b * b = 1 := by
    rw [← pow_two]
    exact hp.elem.2 b hbB.2
  have hz2 : ((i * b * i⁻¹)⁻¹ * x) * ((i * b * i⁻¹)⁻¹ * x) = 1 := by
    rw [← pow_two]
    exact hp.elem.2 _ hz.1
  have hy2 : (i * b * i⁻¹) * (i * b * i⁻¹) = 1 := by
    calc (i * b * i⁻¹) * (i * b * i⁻¹) = i * (b * b) * i⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  have hxz : x = (i * b * i⁻¹) * ((i * b * i⁻¹)⁻¹ * x) := by group
  rw [hxz, pow_two]
  calc (i * b * i⁻¹) * ((i * b * i⁻¹)⁻¹ * x) * ((i * b * i⁻¹) * ((i * b * i⁻¹)⁻¹ * x)) =
      (i * b * i⁻¹) * (((i * b * i⁻¹)⁻¹ * x) * (i * b * i⁻¹)) * ((i * b * i⁻¹)⁻¹ * x) := by
        group
    _ = (i * b * i⁻¹) * ((i * b * i⁻¹) * ((i * b * i⁻¹)⁻¹ * x)) * ((i * b * i⁻¹)⁻¹ * x) := by
        rw [hzc]
    _ = ((i * b * i⁻¹) * (i * b * i⁻¹)) *
        (((i * b * i⁻¹)⁻¹ * x) * ((i * b * i⁻¹)⁻¹ * x)) := by group
    _ = 1 := by rw [hy2, hz2, one_mul]

theorem qOf_le_one_of_comm {H T M V I : Subgroup Γ} {g : Γ}
    (h : E2.Hyp28 H T M V) (hI : IsInIHTV H T M V I) (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g)
    (hcharI : CharTwo I)
    (hcomm : ∀ b ∈ kerIn (M ⊓ I) I ⊓ V, ∀ a ∈ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V),
      b * a = a * b) :
    qOf (autI h.elem I) ≤ ((1 : ℚ) : WithTop ℚ) := by
  obtain ⟨hIV, hrank⟩ := E213M.ne_and_rank h hI hp hcharI
  obtain ⟨-, -, hAel, -, hnc, hCA⟩ := Ch3n.exists_cubic_of_pair hp hcharI hIV
  set B := kerIn (M ⊓ I) I ⊓ V with hB
  set A := B6.conjSub g B with hA
  set Z := V ⊓ B6.conjSub g V with hZ
  have hAN : A ≤ Subgroup.normalizer (V : Set Γ) :=
    hp.A_le_pCoreOf.trans hp.pCoreOf_le_normalizer
  have hAI : A ≤ I := hp.A_le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I)
  have hconjZ : B6.conjSub g Z = Z := hp.conjSub_inf_conj hp.mem
  have hrelAB : Z.relIndex A = Z.relIndex B := by
    rw [hA]
    conv_lhs => rw [← hconjZ]
    show (Z.map (MulAut.conj g).toMonoidHom).relIndex (B.map (MulAut.conj g).toMonoidHom) = _
    exact Subgroup.relIndex_map_map_of_injective _ _ fun x y hxy => (MulAut.conj g).injective hxy
  have hcardA : Nat.card (autI h.elem A) = Z.relIndex B := by
    rw [card_autI_eq h.elem hAN, hCA, hrelAB]
  have hBC : B ≤ V ⊓ Subgroup.centralizer (A : Set Γ) := fun b hb =>
    ⟨hb.2, Subgroup.mem_centralizer_iff.2 fun a ha => (hcomm b hb a ha).symm⟩
  have hFF : IsFFModule (autI h.elem I) := by
    refine ⟨autI h.elem A, autI_mono h.elem hAI, ?_, ?_, ?_⟩
    · exact fun hb => hnc ((autI_eq_bot_iff h.elem hAN).1 hb)
    · exact isElemAbelian2_autI h.elem hAel hAN
    · rw [card_fixV_autI h.elem hAN, hcardA]
      have h2 := Subgroup.relIndex_mul_card B V
      rw [inf_eq_left.2 (inf_le_right : B ≤ V)] at h2
      calc Nat.card (IntMod V h.elem) = Nat.card V := rfl
        _ = B.relIndex V * Nat.card B := h2.symm
        _ ≤ Z.relIndex B * Nat.card B := Nat.mul_le_mul_right _ hrank
        _ ≤ Z.relIndex B * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set Γ)) :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hBC)
  have hq := (B1_4_5 (fun v => IntMod.sq_eq_one v) (autI h.elem I)).out 1 3
  rw [WithTop.coe_one]
  exact hq.mp hFF

end E214N

open E214N E214E

theorem e214_five {Γ : Type} [Group Γ] [Finite Γ]
    (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V) : CharTwo H → IsTISetIn V M →
    ∀ (I : Subgroup Γ) (g : Γ), IsInIHTV H T M V I → g ∈ I → I = V ⊔ conjSubgroup V g →
      V ⊓ conjSubgroup V g ≠ ⊥ →
      ∀ (MI TI JI B A P Z : Subgroup Γ) (k : ℕ),
        MI = M ⊓ I → TI = T ⊓ I → JI = kerIn MI I → B = V ⊓ pCoreOf 2 I →
        A = conjSubgroup V g ⊓ pCoreOf 2 I → P = A ⊔ B → Z = V ⊓ conjSubgroup V g →
        E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (k : ℕ∞) →
        ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
            (IsNaturalSection I P Z JI (CFSG.Open.StatedSL 2 F) ∨
              IsNaturalSection I P Z JI (CFSG.Open.StatedSp 2 F))) →
          (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ qOf (autI h.elem I) ≤ ((1 : ℚ) : WithTop ℚ)) := by
  intro hc _ I g hI hg hgen _ MI TI JI B A P Z k hMI _ hJI hB hA hP hZ _ hnat
  obtain ⟨F, _, _, hF, hnat⟩ := hnat
  have hp := pair_of_isInIHTV h hI hg hgen
  subst hMI hJI hB hA hP hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hgen' : I = V ⊔ B6.conjSub g⁻¹ V := by
    rw [← conjSubgroup_eq_conjSub_inv]
    exact hgen
  have hcharI : CharTwo I := by
    have := E2.charTwo_of_charTwo h (hI.1 (I.inv_mem hg)) hc
    rwa [← hgen'] at this
  have hPeq : B6.conjSub g⁻¹ V ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I =
      (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V) := by
    rw [hp.conjSub_kerIn_inf_eq, hp.kerIn_inf_eq, sup_comm]
  rw [conjSubgroup_eq_conjSub_inv V g] at hnat ⊢
  rw [hPeq] at hnat ⊢
  have hconj : ∀ x ∈ (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V),
      x ∉ V ⊓ B6.conjSub g⁻¹ V →
      ∀ b ∈ (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V),
        b ∉ V ⊓ B6.conjSub g⁻¹ V → ∃ i ∈ I, (i * b * i⁻¹)⁻¹ * x ∈ V ⊓ B6.conjSub g⁻¹ V := by
    intro x hx hxZ b hb hbZ
    rcases hnat with hN | hN
    · obtain ⟨i, hi, -, hz⟩ := exists_conj_of_isNaturalSection
        (fun u w hu hw => statedSL_exists_mulVec_eq hu hw) hN hx hxZ hb hbZ
      exact ⟨i, hi, hz⟩
    · obtain ⟨i, hi, -, hz⟩ := exists_conj_of_isNaturalSection
        (fun u w hu hw => statedSp_exists_mulVec_eq hu hw) hN hx hxZ hb hbZ
      exact ⟨i, hi, hz⟩
  have hsq := sq_eq_one_of_conj hp hconj
  have hab : ∀ x ∈ (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V),
      ∀ y ∈ (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V), x * y = y * x := by
    intro x hx y hy
    have e1 : x * y * (x * y) = 1 := by
      rw [← pow_two]
      exact hsq _ (Subgroup.mul_mem _ hx hy)
    have e2 : x * x = 1 := by
      rw [← pow_two]
      exact hsq x hx
    have e3 : y * y = 1 := by
      rw [← pow_two]
      exact hsq y hy
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right e1).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right e2, inv_eq_of_mul_eq_one_right e3]
  refine ⟨hab, qOf_le_one_of_comm h hI hp hcharI fun b hb a ha => ?_⟩
  exact hab b (le_sup_left (a := kerIn (M ⊓ I) I ⊓ V) hb) a
    (le_sup_right (b := B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V)) ha)

end CFSG.Quasithin.SimsE2
