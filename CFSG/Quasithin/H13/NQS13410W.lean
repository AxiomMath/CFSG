module

public import CFSG.Quasithin.H13.NQS134Hat8
public import CFSG.Quasithin.H13.KGFactHatA6
public import CFSG.Quasithin.H13.NQS13410N
public import CFSG.Quasithin.H13.NQS13410T

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem exists_hat_c (S : A6.Setting134 G T L V)
    (hhat : A6.IsHatA6 L) :
    ∃ c : G, c ∈ A6.l0 L ∧ c ∈ L₁Of L (fsuV1 T V) ∧ orderOf c = 3 ∧ c ∈ A6.o2Z L ∧
      c ∈ centralizer (V : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hcL0, hc3, hcO, -⟩ := A6.exists_l0_c hhat.2.1
  have hcZ : c ∈ A6.o2Z L := oTwoRes_le _ hcL0
  have hc1 : c ≠ 1 := fun h => hcO (h ▸ one_mem _)
  exact ⟨c, hcL0, U3.s134_l0_le_L1 S hcL0, orderOf_eq_prime hc3 hc1, hcZ,
    U3.s134_o2Z_le_centralizer S hcZ⟩

theorem not_le_normalizer_l0 (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L) {K : Subgroup G}
    (hKM : ¬ K ≤ normalizer (L : Set G)) : ¬ K ≤ normalizer (A6.l0 L : Set G) := fun h =>
  hKM (h.trans (U3.normalizer_l0_le hhat
    (A5.charTwo_of_faithful S.h13.qtke.2.1 S.h13.sylow S.h13.faithful) S.T_le_NL S.uniqueM))

theorem pCoreOf_l0_le_T (S : A6.Setting134 G T L V) : pCoreOf 2 (A6.l0 L) ≤ T := by
  refine A6.pCoreOf_l0_le.trans ((A6.pCoreOf_le_pCoreOf_sup S.T_le_NL).trans ?_)
  rw [← U3.s134_cT S]
  exact inf_le_left

theorem T_le_normalizer_l0 (S : A6.Setting134 G T L V) : T ≤ normalizer (A6.l0 L : Set G) :=
  A5.le_normalizer_oTwoRes_of_le_normalizer (S.T_le_NL.trans A6.normalizer_L_le_o2Z)

theorem pCoreOf_le_T_of_sylow {K : Subgroup G} (hTK : T ≤ normalizer (K : Set G))
    (hTsyl : IsSylowTwoOf T (K ⊔ T)) : pCoreOf 2 K ≤ T :=
  (A6.pCoreOf_le_pCoreOf_sup hTK).trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)

theorem false_of_l0_le_centralizer (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L)
    {K W : Subgroup G} (hKM : ¬ K ≤ normalizer (L : Set G)) (hTK : T ≤ normalizer (K : Set G))
    (hTsyl : IsSylowTwoOf T (K ⊔ T)) (hL0K : A6.l0 L ≤ normalizer (K : Set G))
    (hKW : K ≤ normalizer (W : Set G)) (hTW : T ≤ normalizer (W : Set G))
    (hCK : K ⊓ centralizer (W : Set G) ≤ pCoreOf 2 K) {x : G} (hxL0 : x ∈ A6.l0 L)
    (hx3 : orderOf x = 3) (hxW : x ∈ centralizer (W : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₀ := A6.l0 L with hL₀
  set P := pCoreOf 2 K with hP
  have hNC : normalizer (W : Set G) ≤ normalizer (centralizer (W : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer W
  have hL0W : L₀ ≤ centralizer (W : Set G) :=
    U3.l0_le_of_mem hhat ((pCoreOf_l0_le_T S).trans (hTW.trans hNC)) hxW hxL0 hx3
  have hPT : P ≤ T := pCoreOf_le_T_of_sylow hTK hTsyl
  have hTL0 : T ≤ normalizer (L₀ : Set G) := T_le_normalizer_l0 S
  have hP2 : IsPGroup 2 ↥P := LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hKN : K ≤ normalizer ((L₀ ⊔ P : Subgroup G) : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun k hk y hy => ?_
    obtain ⟨l, hl, p, hp, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer (hPT.trans hTL0) hy
    have hlW : l ∈ centralizer (W : Set G) := hL0W hl
    have hklK : k * l * k⁻¹ * l⁻¹ ∈ K := by
      have h1 : l * k⁻¹ * l⁻¹ ∈ K := (mem_normalizer_iff.mp (hL0K hl) _).mp (inv_mem hk)
      have e : k * l * k⁻¹ * l⁻¹ = k * (l * k⁻¹ * l⁻¹) := by group
      rw [e]
      exact mul_mem hk h1
    have hklW : k * l * k⁻¹ * l⁻¹ ∈ centralizer (W : Set G) :=
      mul_mem ((mem_normalizer_iff.mp (hNC (hKW hk)) l).mp hlW) (inv_mem hlW)
    have hklP : k * l * k⁻¹ * l⁻¹ ∈ P := hCK (mem_inf.2 ⟨hklK, hklW⟩)
    have hkp : k * p * k⁻¹ ∈ P :=
      (mem_normalizer_iff.mp (LieType.BorelTits.le_normalizer_pCoreOf 2 K hk) p).mp hp
    have e : k * (l * p) * k⁻¹ = (k * l * k⁻¹ * l⁻¹) * l * (k * p * k⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem (mem_sup_right hklP) (mem_sup_left hl)) (mem_sup_right hkp)
  have hO2 : oTwoRes (L₀ ⊔ P) = L₀ := by
    refine le_antisymm (U3.oTwoRes_le_of_le_sup le_rfl hP2 (hPT.trans hTL0)) ?_
    have h1 : L₀ ≤ oTwoRes L₀ := U3.oTwoRes_le_oTwoRes (A6.o2Z L)
    exact h1.trans (A6.oTwoRes_mono le_sup_left)
  have hKL0 : K ≤ normalizer (L₀ : Set G) := by
    have h1 := A5.le_normalizer_oTwoRes_of_le_normalizer hKN
    rwa [hO2] at h1
  exact not_le_normalizer_l0 S hhat hKM hKL0

theorem false_of_l0_l0 (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L) {K : Subgroup G}
    (hhatK : A6.IsHatA6 K) (hKM : ¬ K ≤ normalizer (L : Set G)) (hTK : T ≤ normalizer (K : Set G))
    (hTsyl : IsSylowTwoOf T (K ⊔ T)) {x : G} (hxL : x ∈ A6.l0 L) (hxK : x ∈ A6.l0 K)
    (hx3 : orderOf x = 3) : False := by
  have hTK0 : T ≤ normalizer (A6.l0 K : Set G) :=
    A5.le_normalizer_oTwoRes_of_le_normalizer (hTK.trans A6.normalizer_L_le_o2Z)
  have h1 : A6.l0 L ≤ A6.l0 K :=
    U3.l0_le_of_mem hhat ((pCoreOf_l0_le_T S).trans hTK0) hxK hxL hx3
  have hOK : pCoreOf 2 (A6.l0 K) ≤ T :=
    A6.pCoreOf_l0_le.trans (pCoreOf_le_T_of_sylow hTK hTsyl)
  have h2 : A6.l0 K ≤ A6.l0 L :=
    U3.l0_le_of_mem hhatK (hOK.trans (T_le_normalizer_l0 S)) hxL hxK hx3
  have heq : A6.l0 K = A6.l0 L := le_antisymm h2 h1
  exact not_le_normalizer_l0 S hhat hKM (heq ▸ A6.L_le_normalizer_l0)

omit [Finite G] in
theorem false_of_e9 {Γ Γ' : Type*} [Group Γ] [Group Γ'] {N : Subgroup G} (φ : ↥N →* Γ)
    (ψ : ↥N →* Γ') (Y : Set Γ)
    (hdec : ∀ a ∈ Y, ∀ b ∈ Y, a ^ 3 = 1 → b ^ 3 = 1 →
      ∃ i j : Fin 3, (i ≠ 0 ∨ j ≠ 0) ∧ (a ^ (i : ℕ) * b ^ (j : ℕ)) ^ 4 = 1)
    (hker : ∀ g : ↥N, φ g ^ 4 = 1 → ∃ k : ℕ, g ^ 2 ^ k = 1) {x y : ↥N} (hxY : φ x ∈ Y)
    (hyY : φ y ∈ Y) (hx3' : φ x ^ 3 = 1) (hy3' : φ y ^ 3 = 1) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hψx : ψ x = 1) (hψy3 : ψ y ^ 3 = 1) (hψy1 : ψ y ≠ 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, j, hij, h4⟩ := hdec _ hxY _ hyY hx3' hy3'
  obtain ⟨k, hk⟩ := hker (x ^ (i : ℕ) * y ^ (j : ℕ)) (by rw [map_mul, map_pow, map_pow]; exact h4)
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hψ : ψ y ^ ((j : ℕ) * 2 ^ k) = 1 := by
    have h1 := congrArg ψ hk
    rw [map_pow, map_mul, map_pow, map_pow, hψx, one_pow, one_mul, map_one, ← pow_mul] at h1
    exact h1
  have hj : (j : ℕ) = 0 := by
    have hd := orderOf_dvd_of_pow_eq_one hψ
    rw [orderOf_eq_prime hψy3 hψy1] at hd
    have h3 : 3 ∣ (j : ℕ) := hcop.dvd_of_dvd_mul_right hd
    have hj3 := j.isLt
    omega
  have hx : x ^ ((i : ℕ) * 2 ^ k) = 1 := by
    rw [hj, pow_zero, mul_one, ← pow_mul] at hk
    exact hk
  have hi : (i : ℕ) = 0 := by
    have hd := orderOf_dvd_of_pow_eq_one hx
    rw [orderOf_eq_prime hx3 hx1] at hd
    have h3 : 3 ∣ (i : ℕ) := hcop.dvd_of_dvd_mul_right hd
    have hi3 := i.isLt
    omega
  rcases hij with h | h
  · exact h (Fin.ext hi)
  · exact h (Fin.ext hj)

theorem false_of_thompsonJ_le (S : A6.Setting134 G T L V)
    (hhat : A6.IsHatA6 L) {K Y : Subgroup G} (hKM : ¬ K ≤ normalizer (L : Set G))
    (hJY : thompsonJ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ≤ Y)
    (hYR : Y ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hKY : K ≤ normalizer (Y : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := B6.thompsonJ_eq_of_le hJY hYR
  have h8 := (stmt13_2_2_8Hat_of KGHatA6.hatA6OddInverts_holds G T L V S hhat).1
  set X := thompsonJ (pCoreOf 2 (L ⊔ T)) with hX
  have hKX : K ≤ normalizer (X : Set G) := by
    rw [← h8, ← hJ]
    exact hKY.trans (normalizer_le_normalizer_thompsonJ Y)
  have hXT : X ≤ T := by
    refine (iSup₂_le fun A hA => hA.1 : X ≤ pCoreOf 2 (L ⊔ T)).trans ?_
    rw [← U3.s134_cT S]
    exact inf_le_left
  have hX1 : X ≠ ⊥ := by
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian (pCoreOf 2 (L ⊔ T))
    intro hX0
    have hAX : A ≤ X := B6.le_thompsonJ hA
    rw [hX0] at hAX
    have hVab := U3.s134_elemAbelian_V S
    have hVO : V ≤ pCoreOf 2 (L ⊔ T) := by
      rw [← U3.s134_cT S]
      exact le_inf S.V_le_T fun v hv => mem_centralizer_iff.2 fun w hw =>
        congrArg Subtype.val (hVab.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
    have h1 := hA.2.2 V hVO hVab
    rw [le_bot_iff.1 hAX, Subgroup.card_bot, S.card_V] at h1
    omega
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨X, hX1, S.h13.sylow.1.to_le hXT, rfl⟩ : IsTwoLocal (normalizer (X : Set G)))
  have hM := S.uniqueM.2 M' ⟨hM', ((LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
    (normalizer_le_normalizer_thompsonJ _)).trans hle⟩
  exact hKM (hKX.trans (hM ▸ hle))

theorem false_of_thompsonJ_le_centralizer
    (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L) {K U : Subgroup G}
    (hKM : ¬ K ≤ normalizer (L : Set G)) (hTK : T ≤ normalizer (K : Set G))
    (hTsyl : IsSylowTwoOf T (K ⊔ T)) (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hKU : K ≤ normalizer (U : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hCK : IsPGroup 2 ↥(K ⊓ centralizer (U : Set G)))
    (hJ : thompsonJ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ≤ centralizer (U : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hR
  have hRT : R ≤ T := s134_R_le_T S
  have hR2 : IsPGroup 2 ↥R := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRK : R ≤ normalizer (K : Set G) := hRT.trans hTK
  have hL1TR : L₁ ⊔ T ≤ normalizer (R : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
  set Y := pCoreOf 2 (K ⊔ R) with hY
  have hC2 : IsPGroup 2 ↥((K ⊔ R) ⊓ centralizer (U : Set G)) := by
    intro c
    obtain ⟨k, hk⟩ := U3.exists_pow_two_pow_mem_of_mem_sup hR2 hRK c.2.1
    have hkC : (c : G) ^ 2 ^ k ∈ K ⊓ centralizer (U : Set G) := ⟨hk, pow_mem c.2.2 _⟩
    obtain ⟨m, hm⟩ := hCK ⟨_, hkC⟩
    have hm' : ((c : G) ^ 2 ^ k) ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    refine ⟨k + m, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, hm']
  have hEU : K ⊔ R ≤ normalizer (U : Set G) := sup_le hKU (hRT.trans hTU)
  have hCn : (((K ⊔ R) ⊓ centralizer (U : Set G)).subgroupOf (K ⊔ R)).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer inf_le_left).2 ?_
    exact (le_inf le_normalizer (hEU.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  have hCY : (K ⊔ R) ⊓ centralizer (U : Set G) ≤ Y :=
    LieType.BorelTits.le_pCoreOf 2 inf_le_left hCn hC2
  have hJY : thompsonJ R ≤ Y :=
    (le_inf ((B6.thompsonJ_le R).trans le_sup_right) hJ).trans hCY
  have hTKR : T ≤ normalizer ((K ⊔ R : Subgroup G) : Set G) :=
    le_normalizer_sup_of hRK hTK (le_sup_right.trans hL1TR)
  have hL1KR : L₁ ≤ normalizer ((K ⊔ R : Subgroup G) : Set G) :=
    le_normalizer_sup_of hRK hL1K (le_sup_left.trans hL1TR)
  have hNY : normalizer ((K ⊔ R : Subgroup G) : Set G) ≤ normalizer (Y : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
  have hY2 : IsPGroup 2 ↥Y := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hYT : Y ≤ T := by
    have h1 : Y ≤ pCoreOf 2 (K ⊔ T) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le_sup_left hRT K))
        ((sup_le (le_sup_left.trans le_normalizer) hTKR).trans hNY) hY2
    exact h1.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)
  have hYR : Y ≤ R :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hYT.trans le_sup_right)
      ((sup_le hL1KR hTKR).trans hNY) hY2
  exact false_of_thompsonJ_le S hhat hKM hJY hYR
    (le_sup_left.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _))

theorem exists_mem_T_inf_L (S : A6.Setting134 G T L V) {β : Perm (Fin 6)} (hβ : β ∈ a6D) :
    ∃ t : ↥(normalizer (V : Set G)), (t : G) ∈ T ⊓ L ∧ S.frame.ρ t = β := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hsyl : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer S.T_le_NL)
  set f := rhoL S with hf
  have hfs : Function.Surjective f := by
    rintro ⟨σ, hσ⟩
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 hσ
    exact ⟨⟨g, hgL⟩, Subtype.ext (by rw [rhoL_apply]; exact hg)⟩
  set P := ((T ⊓ L).subgroupOf L).map f with hP
  have hidx : ¬ 2 ∣ P.index := fun h => hsyl.2.2 (h.trans (Subgroup.index_map_dvd _ hfs))
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h8 : 8 ∣ Nat.card ↥P := by
    have h1 := P.index_mul_card
    rw [Nat.card_eq_fintype_card (α := ↥(alternatingGroup (Fin 6))), ← Nat.card_eq_fintype_card,
      h360] at h1
    have hcop : Nat.Coprime 8 P.index :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.2 (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hidx)))
    exact hcop.dvd_of_dvd_mul_left ⟨45, by omega⟩
  set P' := P.map (alternatingGroup (Fin 6)).subtype with hP'
  have hP'D : P' ≤ a6D := by
    rintro _ ⟨σ, ⟨l, hl, rfl⟩, rfl⟩
    have hlT : (l : G) ∈ T := (mem_inf.1 (mem_subgroupOf.1 hl)).1
    refine (mem_a6D_iff _).2 ⟨?_, Perm.mem_alternatingGroup.1 (f l).2⟩
    show InD6 ((f l : Perm (Fin 6)))
    rw [rhoL_apply]
    exact S.frame.T_D _ hlT
  have hcard : Nat.card ↥P' = Nat.card ↥P :=
    Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective
  have hP'eq : P' = a6D :=
    eq_of_le_of_card_ge hP'D (by rw [card_a6D, hcard]; exact Nat.le_of_dvd Nat.card_pos h8)
  rw [← hP'eq] at hβ
  obtain ⟨σ, ⟨l, hl, rfl⟩, rfl⟩ := hβ
  exact ⟨⟨l, S.frame.L_le l.2⟩, mem_inf.2 ⟨(mem_inf.1 (mem_subgroupOf.1 hl)).1, l.2⟩,
    (rhoL_apply S l).symm⟩

end CFSG.Quasithin.H13.NQS134
