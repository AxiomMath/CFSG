module

public import CFSG.Quasithin.Vol2.Ch11SecD556H
public import CFSG.Quasithin.H13.U3S13227P
public import CFSG.Quasithin.H13.U3S1348D
public import CFSG.Quasithin.Vol2.Ch11SecD556A

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

theorem c012_mul_c123_mem : c012 * c123 ∈ K4L := by decide

theorem c012_pres45 : Pres45 c012 := by decide

theorem K4x_comm : ∀ a ∈ K4xList, ∀ b ∈ K4xList, a * b = b * a := by decide +kernel

theorem fix_comm_W1 : ∀ x : P6, x ∈ G6.coreMod 6 →
    G6.permAct 6 ((c012 * c123) * c012 * (c012 * c123)⁻¹ * c012⁻¹) x = x →
    G6.permAct 6 ((c012 * (c012 * c123) * c012⁻¹) * c012 * (c012 * (c012 * c123) * c012⁻¹)⁻¹ *
      c012⁻¹) x = x → InW1 x := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_false_of_comm_le_V1 (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H VH : Subgroup G}
    (hL1H : L₁Of L (fsuV1 T V) ≤ H) (hC : H ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hX : ⁅VH, L₁Of L (fsuV1 T V)⁆ ≤ fsuV1 T V) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hcL, hc3, hcN, hc⟩ := s134_exists_L1_cube S he c012_props.1 c012_props.2.1
    c012_props.2.2
  have hcV1 : ∀ w ∈ fsuV1 T V, c * w * c⁻¹ = w := by
    intro w hw
    obtain ⟨hwV, hwW⟩ := S.mem_V1_iff.1 hw
    refine (S.conj_eq_iff ⟨c, hcN⟩ ⟨w, hwV⟩).2 (Subtype.ext ?_)
    rw [G6.coreAct_coe, hc]
    exact fix_W1_of_pres45 _ c012_pres45 _ hwW
  have hc2 : c * c ∈ centralizer (VH : Set G) := by
    refine mem_centralizer_iff.2 fun u hu => ?_
    have hdX : c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V := by
      have h1 : ⁅c, u⁆ ∈ ⁅L₁Of L (fsuV1 T V), VH⁆ := commutator_mem_commutator hcL hu
      rw [commutator_comm] at h1
      exact hX h1
    have hd2 : (c * u * c⁻¹ * u⁻¹) * (c * u * c⁻¹ * u⁻¹) = 1 := by
      have := (s134_elemAbelian_V S).2 _ (S.mem_V1_iff.1 hdX).1
      rwa [pow_two] at this
    have hcd : c * (c * u * c⁻¹ * u⁻¹) * c⁻¹ = c * u * c⁻¹ * u⁻¹ := hcV1 _ hdX
    have key : (c * c) * u * (c * c)⁻¹ = u := by
      have e1 : (c * c) * u * (c * c)⁻¹ =
          (c * (c * u * c⁻¹ * u⁻¹) * c⁻¹) * (c * u * c⁻¹ * u⁻¹) * u := by group
      rw [e1, hcd, hd2, one_mul]
    calc u * (c * c) = ((c * c) * u * (c * c)⁻¹) * (c * c) := by rw [key]
      _ = (c * c) * u := by group
  have hcC : c ∈ centralizer (VH : Set G) := by
    have h4 : c = (c * c) * (c * c) := by
      calc c = c ^ 3 * c := by rw [hc3, one_mul]
        _ = (c * c) * (c * c) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h4]
    exact mul_mem hc2 hc2
  have hcO : c ∈ pCoreOf 2 H := hC ▸ mem_inf.2 ⟨hL1H hcL, hcC⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨c, hcO⟩
  have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hg : c ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.2 ⟨hc3, hk'⟩
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at hg
  have h1 : (⟨c, hcN⟩ : ↥(normalizer (V : Set G))) = 1 := Subtype.ext hg
  rw [h1, map_one] at hc
  exact absurd hc.symm (by decide)

theorem s134_pCoreOf_L_le_centralizer_VH (S : A6.Setting134 G T L V) (hL : IsShort2 L)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {VH : Subgroup G}
    (hVHQ : VH ≤ pCoreOf 2 (L ⊔ T)) : pCoreOf 2 L ≤ centralizer (VH : Set G) :=
  le_centralizer_iff.1 (hVHQ.trans (s134_pCoreOf_LT_le_centralizer S hL he))

omit [Finite G] in
theorem le_pCoreOf_of_commutator_le [Finite G] {H P : Subgroup G} (hPH : P ≤ H)
    (hP2 : IsPGroup 2 P) (h : ⁅P, H⁆ ≤ pCoreOf 2 H) : P ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pCoreOf 2 H with hO
  have hKH : P ⊔ O ≤ H := sup_le hPH (pCoreOf_le 2 H)
  have hHK : H ≤ normalizer ((P ⊔ O : Subgroup G) : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun x hx k hk => ?_
    have hle : P ⊔ O ≤ (P ⊔ O).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun p hp => ?_) (fun o ho => ?_)
      · show x * p * x⁻¹ ∈ P ⊔ O
        have h1 : ⁅p, x⁆ ∈ O := h (commutator_mem_commutator hp hx)
        have e : x * p * x⁻¹ = ⁅p, x⁆⁻¹ * p := by rw [commutatorElement_def]; group
        rw [e]
        exact mul_mem (mem_sup_right (inv_mem h1)) (mem_sup_left hp)
      · show x * o * x⁻¹ ∈ P ⊔ O
        exact mem_sup_right ((mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hx) o).mp ho)
    exact hle hk
  have hK2 : IsPGroup 2 ↥(P ⊔ O) := IsPGroup.to_sup_of_normal_right' hP2 (pCoreOf_isPGroup 2 H)
    (hPH.trans (le_normalizer_pCoreOf 2 H))
  exact le_sup_left.trans (le_pCoreOf_of_le_normalizer 2 hKH hHK hK2)

theorem s134_P_le_pCoreOf (S : A6.Setting134 G T L V) (hL : IsShort2 L)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H VH : Subgroup G}
    (hsolv : Group.IsSolvable ↥H) (hL1H : L₁Of L (fsuV1 T V) ≤ H) (hO2 : pCoreOf 2 H ≠ ⊥)
    (hVHQ : VH ≤ pCoreOf 2 (L ⊔ T)) (hC : H ⊓ centralizer (VH : Set G) = pCoreOf 2 H) {c : G}
    (hcL : c ∈ L₁Of L (fsuV1 T V)) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    ⁅pCoreOf 2 (L₁Of L (fsuV1 T V)), zpowers c⁆ ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set X := zpowers c with hXdef
  set P := ⁅pCoreOf 2 L₁, X⁆ with hPdef
  have hXL : X ≤ L₁ := zpowers_le.2 hcL
  have hXN : X ≤ normalizer (pCoreOf 2 L₁ : Set G) := hXL.trans (le_normalizer_pCoreOf 2 L₁)
  have hX3 : IsPGroup 3 ↥X := by
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hcop : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 L₁) := by
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 L₁).exists_card_eq
    rw [hn]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  have hPX : ⁅P, X⁆ = P := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent
    3 Nat.prime_three X (pCoreOf 2 L₁) hX3 hXN
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hcop)
  have hPO : P ≤ pCoreOf 2 L₁ := by
    rw [hPdef, commutator_le]
    intro o ho x hx
    rw [commutatorElement_def]
    have h1 : x * o⁻¹ * x⁻¹ ∈ pCoreOf 2 L₁ := (mem_normalizer_iff.mp (hXN hx) _).mp (inv_mem ho)
    have e : o * x * o⁻¹ * x⁻¹ = o * (x * o⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem ho h1
  have hPL1 : P ≤ L₁ := hPO.trans (pCoreOf_le 2 L₁)
  have hPH : P ≤ H := hPL1.trans hL1H
  have hP2 : IsPGroup 2 ↥P := (pCoreOf_isPGroup 2 L₁).to_le hPO
  have hPN : P ≤ normalizer (V : Set G) := hPL1.trans ((L1Of_le L _).trans S.frame.L_le)
  have hPK : ∀ x : ↥P, S.frame.ρ (Subgroup.inclusion hPN x) ∈ K4xList := by
    intro x
    have hxO := hPO x.2
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L₁ ⟨x, hxO⟩
    have hk' : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : S.frame.ρ (Subgroup.inclusion hPN x) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (Subgroup.inclusion hPN x) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, map_one]
    exact K4_le_K4x _ (A4_two_K4 _ (s134_rho_L1 S (hPN x.2) (hPL1 x.2))
      (pow_sixteen_of_two_pow h1))
  have hΦ : (frattini ↥P).map P.subtype ≤ pCoreOf 2 H := by
    let f : ↥P →* ↥K4xsub := (S.frame.ρ.comp (Subgroup.inclusion hPN)).codRestrict K4xsub hPK
    have hcomm : ∀ a b : ↥K4xsub, a * b = b * a := fun a b => Subtype.ext (K4x_comm a a.2 b b.2)
    have hpow : ∀ a : ↥K4xsub, a ^ 2 = 1 := fun a => Subtype.ext (by
      rw [SubmonoidClass.coe_pow, pow_two]
      exact K4x_sq a a.2)
    have hle := CFSG.SectionRank.Ccomm.frattini_le_ker_of_elementary (p := 2) f hcomm hpow
    rintro _ ⟨x, hx, rfl⟩
    have hfx : f x = 1 := hle hx
    have hρx : S.frame.ρ (Subgroup.inclusion hPN x) = 1 := congrArg Subtype.val hfx
    have hxC : (x : G) ∈ centralizer (V : Set G) := (s134_rho_eq_one_iff S _).1 hρx
    have hxQ : (x : G) ∈ pCoreOf 2 L := by
      rw [s134_pCoreOf_L_eq S he]
      exact ⟨(L1Of_le L _) (hPL1 x.2), hxC⟩
    rw [← hC]
    exact ⟨hPH x.2, s134_pCoreOf_L_le_centralizer_VH S hL he hVHQ hxQ⟩
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup G, E ≤ H → IsElemAbelian p E →
      ∀ r, Nat.card E = p ^ r → r ≤ 2 := fun p hp hp2 E hE hEab r hr =>
    Vol2.Ch11.SecD.le_two_of_elemAbelian S.fsu.qtke.2.2 hO2 (pCoreOf_isPGroup 2 H) hp hp2
      (hE.trans (le_normalizer_pCoreOf 2 H)) hEab hr
  have hXodd : Odd (Nat.card ↥X) := by
    rw [hXdef, Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
    decide
  have hPY : ⁅P, perfectCore H⁆ ≤ pCoreOf 2 H := by
    rw [(isSolvable_iff_perfectCore_eq_bot H).1 hsolv, commutator_bot_right]
    exact bot_le
  have h := Vol2.Ch11.SecD.commutator_le_pCoreOf_of_perfectCore hrank le_rfl le_normalizer
    (hXL.trans hL1H) hXodd hPH hP2 hPX hΦ hPY
  exact le_pCoreOf_of_commutator_le hPH hP2 h

theorem s134_false_of_not_normal (S : A6.Setting134 G T L V) (hL : IsShort2 L)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H VH : Subgroup G}
    (hsolv : Group.IsSolvable ↥H) (hL1H : L₁Of L (fsuV1 T V) ≤ H) (hO2 : pCoreOf 2 H ≠ ⊥)
    (hHN : H ≤ normalizer (VH : Set G)) (hVHQ : VH ≤ pCoreOf 2 (L ⊔ T))
    (hC : H ⊓ centralizer (VH : Set G) = pCoreOf 2 H) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  have P1 := s134Plus_L1 S he
  have hXV : ⁅VH, L₁⁆ ≤ V := by
    rw [commutator_le]
    intro u hu l hl
    rw [commutatorElement_def]
    exact s134_commutator_mem_V S hL (hVHQ hu) (L1Of_le L _ hl)
  have hXVH : ⁅VH, L₁⁆ ≤ VH := by
    rw [commutator_le]
    intro u hu l hl
    rw [commutatorElement_def]
    have h1 : l * u⁻¹ * l⁻¹ ∈ VH := (mem_normalizer_iff.mp (hHN (hL1H hl)) _).mp (inv_mem hu)
    have e : u * l * u⁻¹ * l⁻¹ = u * (l * u⁻¹ * l⁻¹) := by group
    rw [e]
    exact mul_mem hu h1
  obtain ⟨c, hcL, hc3, hcN, hc⟩ := s134_exists_L1_cube S he c012_props.1 c012_props.2.1
    c012_props.2.2
  have hc1 : c ≠ 1 := by
    rintro rfl
    have h1 : (⟨1, hcN⟩ : ↥(normalizer (V : Set G))) = 1 := rfl
    rw [h1, map_one] at hc
    exact absurd hc.symm (by decide)
  have hPO := s134_P_le_pCoreOf S hL he hsolv hL1H hO2 hVHQ hC hcL hc3 hc1
  obtain ⟨y₁, hy₁L, hy₁N, hy₁⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1
    c012_props.2.2
  obtain ⟨y₂, hy₂L, hy₂N, hy₂⟩ := s134_exists_mem_L1 S c123_props.1 c123_props.2.1
    c123_props.2.2
  have hyN : y₁ * y₂ ∈ normalizer (V : Set G) := mul_mem hy₁N hy₂N
  have hyρ : S.frame.ρ ⟨y₁ * y₂, hyN⟩ = c012 * c123 := by
    rw [show (⟨y₁ * y₂, hyN⟩ : ↥(normalizer (V : Set G))) = ⟨y₁, hy₁N⟩ * ⟨y₂, hy₂N⟩ from rfl,
      map_mul, hy₁, hy₂]
  have hyO : y₁ * y₂ ∈ pCoreOf 2 L₁ :=
    P1.mem_pCoreOf_of_K4 (x := ⟨y₁ * y₂, hyN⟩) (mul_mem hy₁L hy₂L) (hyρ ▸ c012_mul_c123_mem)
  have hy'O : c * (y₁ * y₂) * c⁻¹ ∈ pCoreOf 2 L₁ :=
    (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L₁ hcL) _).mp hyO
  have ha₁ : ⁅y₁ * y₂, c⁆ ∈ centralizer (VH : Set G) :=
    (hC.symm.le (hPO (commutator_mem_commutator hyO (mem_zpowers c)))).2
  have ha₂ : ⁅c * (y₁ * y₂) * c⁻¹, c⁆ ∈ centralizer (VH : Set G) :=
    (hC.symm.le (hPO (commutator_mem_commutator hy'O (mem_zpowers c)))).2
  have hy'N : c * (y₁ * y₂) * c⁻¹ ∈ normalizer (V : Set G) :=
    mul_mem (mul_mem hcN hyN) (inv_mem hcN)
  have hy'ρ : S.frame.ρ ⟨c * (y₁ * y₂) * c⁻¹, hy'N⟩ = c012 * (c012 * c123) * c012⁻¹ := by
    rw [show (⟨c * (y₁ * y₂) * c⁻¹, hy'N⟩ : ↥(normalizer (V : Set G))) =
      ⟨c, hcN⟩ * ⟨y₁ * y₂, hyN⟩ * ⟨c, hcN⟩⁻¹ from rfl, map_mul, map_mul, map_inv, hc, hyρ]
  have hcommN : ∀ x : G, x ∈ normalizer (V : Set G) → ⁅x, c⁆ ∈ normalizer (V : Set G) :=
    fun x hx => mul_mem (mul_mem (mul_mem hx hcN) (inv_mem hx)) (inv_mem hcN)
  have hρcomm : ∀ (x : G) (hx : x ∈ normalizer (V : Set G)),
      S.frame.ρ ⟨⁅x, c⁆, hcommN x hx⟩ =
        S.frame.ρ ⟨x, hx⟩ * c012 * (S.frame.ρ ⟨x, hx⟩)⁻¹ * c012⁻¹ := by
    intro x hx
    rw [show (⟨⁅x, c⁆, hcommN x hx⟩ : ↥(normalizer (V : Set G))) =
        ⟨x, hx⟩ * ⟨c, hcN⟩ * ⟨x, hx⟩⁻¹ * ⟨c, hcN⟩⁻¹ from rfl,
      map_mul, map_mul, map_mul, map_inv, map_inv, hc]
  refine s134_false_of_comm_le_V1 S he hL1H hC fun w hw => ?_
  have hwV := hXV hw
  have hwVH := hXVH hw
  have hfix : ∀ (x : G) (hx : x ∈ normalizer (V : Set G)), x ∈ centralizer (VH : Set G) →
      G6.permAct 6 (S.frame.ρ ⟨x, hx⟩) (S.frame.ψ ⟨w, hwV⟩ : P6) = S.frame.ψ ⟨w, hwV⟩ := by
    intro x hx hxC
    have h1 : x * w * x⁻¹ = w := by
      rw [(mem_centralizer_iff.1 hxC w hwVH).symm]
      group
    have h2 := congrArg Subtype.val ((S.conj_eq_iff ⟨x, hx⟩ ⟨w, hwV⟩).1 h1)
    rwa [G6.coreAct_coe] at h2
  have h1 := hfix _ (hcommN _ hyN) ha₁
  have h2 := hfix _ (hcommN _ hy'N) ha₂
  rw [hρcomm _ hyN, hyρ] at h1
  rw [hρcomm _ hy'N, hy'ρ] at h2
  exact S.mem_V1_iff.2 ⟨hwV, fix_comm_W1 _ (S.frame.ψ ⟨w, hwV⟩).2 h1 h2⟩

end CFSG.Quasithin.H13.U3
