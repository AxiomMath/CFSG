module

public import CFSG.Quasithin.H13.NQS134108C
public import CFSG.Quasithin.H13.NQS13411

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem mul_mul_eq_one_of_card_four {U : Subgroup G} (hU : Nat.card ↥U = 4)
    (h2 : ∀ u ∈ U, u * u = 1) {a b c : G} (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : a * b * c = 1 := by
  classical
  by_contra h
  have hab1 : a * b ≠ 1 := fun e => hab (by
    have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [h1, inv_eq_of_mul_eq_one_right (h2 a ha)])
  have haba : a * b ≠ a := fun e => hb1 (mul_eq_left.mp e)
  have habb : a * b ≠ b := fun e => ha1 (mul_eq_right.mp e)
  have hcab : c ≠ a * b := fun e => h (by rw [e]; exact h2 _ (mul_mem ha hb))
  have : Fintype ↥U := Fintype.ofFinite _
  have hs : ({⟨1, one_mem _⟩, ⟨a, ha⟩, ⟨b, hb⟩, ⟨a * b, mul_mem ha hb⟩, ⟨c, hc⟩} :
      Finset ↥U).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_pair_eq_two_iff.2]
    · exact fun e => hcab (congrArg Subtype.val e).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
      exact ⟨fun e => habb e.symm, hbc⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
      exact ⟨hab, fun e => haba e.symm, hac⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
      exact ⟨fun e => ha1 e.symm, fun e => hb1 e.symm, fun e => hab1 e.symm, fun e => hc1 e.symm⟩
  have h5 := Finset.card_le_univ ({⟨1, one_mem _⟩, ⟨a, ha⟩, ⟨b, hb⟩, ⟨a * b, mul_mem ha hb⟩,
    ⟨c, hc⟩} : Finset ↥U)
  rw [hs, ← Nat.card_eq_fintype_card, hU] at h5
  omega

theorem c2perm_e45 :
    let q := G6.permAct 6 U3.c2perm e45
    let r := G6.permAct 6 U3.c2perm q
    e45 ≠ 1 ∧ q ≠ 1 ∧ r ≠ 1 ∧ e45 ≠ q ∧ e45 ≠ r ∧ q ≠ r ∧ e45 * q * r ≠ 1 := by
  decide +kernel

theorem wt6_e0123 : (Finset.univ.filter fun i : Fin 6 =>
    Multiplicative.toAdd (e0123 : G6.PermMod 6) i = 1).card = 4 := by
  decide +kernel

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem psi_z_cases :
    (S.frame.ψ ⟨z, D.zV1.1⟩ : G6.PermMod 6) = e0123 ∨
      (S.frame.ψ ⟨z, D.zV1.1⟩ : G6.PermMod 6) = e45 := by
  obtain ⟨hzV, hW⟩ := S.mem_V1_iff.1 D.zV1
  rcases W1_cases _ (S.frame.ψ ⟨z, hzV⟩).2 hW with h | h | h | h
  · exfalso
    have h1 : S.frame.ψ ⟨z, D.zV1.1⟩ = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h1
    exact D.z_ne_one (congrArg Subtype.val h1)
  · exfalso
    have h1 : S.frame.ψ ⟨z, D.zV1.1⟩ = S.frame.ψ ⟨S.zV, S.zV_mem_V⟩ := by
      rw [S.psi_zV]
      exact Subtype.ext h
    have h2 := congrArg Subtype.val (S.frame.ψ.injective h1)
    apply D.zL
    rw [show z = S.zV from h2]
    exact (S.mem_ZV_iff.2 (Or.inr rfl)).2
  · exact Or.inl h
  · exact Or.inr h

theorem eight_i (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h1222 : Stmt12_2_2) (h1347 : U3.Stmt13_4_7L2)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hnhat : ¬ A6.IsHatA6 L) {H₂ : Subgroup G} (hstar : IsHStar T (normalizer (L : Set G)) H₂)
    (hH₂H : H₂ ≤ H) (hi : U3.Concl1347i T H₂ (U3.l2Of S ⊔ T)) :
    (S.frame.ψ ⟨z, D.zV1.1⟩ : G6.PermMod 6) = e0123 ∧ V ⊓ centralizer (L : Set G) ≤ W ∧
      ∃ k ∈ K, k ∈ H₂ ∧ (∃ m : ℕ, Odd m ∧ k ^ m = 1) ∧ k * S.zV * k⁻¹ ≠ S.zV ∧
        S.zV * (k * S.zV * k⁻¹) * (k * (k * S.zV * k⁻¹) * k⁻¹) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : normalizer (L : Set G) = L ⊔ T := D.M4.resolve_right hnhat
  obtain ⟨hVKW, -, -, -, -, -⟩ := D.main_of_a6 hC137 h1332 h1228 hC58 h317 h56 he
  obtain ⟨-, -, -, -, -, -, hZV1, -⟩ := D.one_six hC137 h1332 h1228 hC58 h317 h56 he
  obtain ⟨-, hHKT, -, -⟩ := D.seven hC137 h1332 h1228 hC58 h317 h56 he hnhat
  obtain ⟨-, -, -, hinc2, -, hInH0, -, -, -, -⟩ :=
    D.eight_setup hC137 h1332 h1228 hC58 h317 h56 h1222 h1347 he hnhat hstar hH₂H
  have hK2 : oTwoRes (U3.l2Of S ⊔ T) = U3.l2Of S := U3.s134_oTwoRes_L2T S
  obtain ⟨-, hcomm, -, -, -, h6, h7, h8, h9⟩ := hi
  rw [hK2] at hcomm h6 h7 h9
  have hH₂Gz : H₂ ≤ centralizer ({z} : Set G) := hH₂H.trans D.Hz
  have hH₂KT : H₂ ≤ K ⊔ T := hH₂H.trans hHKT.le
  have hTH0 : T ≤ H₂ ⊔ (U3.l2Of S ⊔ T) := le_sup_right.trans le_sup_right
  have hTsylH0 := A5.isSylowTwoOf_of_le S.h13.sylow hTH0
  have hred0 := isTwoReducedIn_conjClosure_of_sylowIn hTsylH0.1 hTsylH0.2.1 hTsylH0.2.2
    (U3.s134_charTwo_of_inH S hInH0) (le_rfl : quasithinOmegaOneCenter T ≤ _)
  have hV0e : IsElemAbelian 2 (U3.v0Of T H₂ (U3.l2Of S ⊔ T)) := hred0.2.2.1
  have h2V0 : ∀ v ∈ U3.v0Of T H₂ (U3.l2Of S ⊔ T), v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact hV0e.2 v hv
  have hV0N : H₂ ⊔ (U3.l2Of S ⊔ T) ≤ normalizer (U3.v0Of T H₂ (U3.l2Of S ⊔ T) : Set G) :=
    le_normalizer_conjClosure _ _
  have hL2N : U3.l2Of S ≤ normalizer (oTwoRes H₂ : Set G) := by
    refine U3.le_normalizer_of_conj_mem' fun l hl k hk => ?_
    have hlk : ⁅l, k⁆ ∈ ⁅oTwoRes H₂, U3.l2Of S⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator hl hk
    have hc : ⁅l, k⁆ ∈ pCoreOf 2 (oTwoRes H₂) := (mem_inf.1 (hcomm hlk)).1
    have e : l * k * l⁻¹ = ⁅l, k⁆ * k := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (LieType.BorelTits.pCoreOf_le 2 _ hc) hk
  have hU1 : ∀ g ∈ U3.l2Of S, ∀ x ∈ U3.v0Of T H₂ (U3.l2Of S ⊔ T) ⊓
      centralizer (oTwoRes H₂ : Set G), g * x * g⁻¹ ∈ U3.v0Of T H₂ (U3.l2Of S ⊔ T) ⊓
        centralizer (oTwoRes H₂ : Set G) := by
    intro g hg x hx
    have hgN : g ∈ normalizer ((U3.v0Of T H₂ (U3.l2Of S ⊔ T) ⊓
        centralizer (oTwoRes H₂ : Set G) : Subgroup G) : Set G) :=
      inf_normalizer_le_normalizer_inf
        ⟨hV0N ((le_sup_left.trans le_sup_right : U3.l2Of S ≤ H₂ ⊔ (U3.l2Of S ⊔ T)) hg),
          le_normalizer_centralizer_of hL2N hg⟩
    exact (mem_normalizer_iff.mp hgN x).mp hx
  have hzU1 : z ∈ U3.v0Of T H₂ (U3.l2Of S ⊔ T) ⊓ centralizer (oTwoRes H₂ : Set G) :=
    mem_inf.2 ⟨le_conjClosure _ _ D.zV1.2,
      U3.mem_centralizer_of_le_centralizer ((oTwoRes_le _).trans hH₂Gz)⟩
  have hpsi : (S.frame.ψ ⟨z, D.zV1.1⟩ : G6.PermMod 6) = e0123 := by
    refine (D.psi_z_cases).resolve_right fun h45 => ?_
    obtain ⟨c, hcL2, hcN, hcρ⟩ := U3.s134_exists_c2_mem_L2 S
    set zV : ↥V := ⟨z, D.zV1.1⟩ with hzV
    set bV : ↥V := ⟨c * z * c⁻¹, (mem_normalizer_iff.mp hcN z).mp D.zV1.1⟩ with hbV
    set dV : ↥V := ⟨c * (c * z * c⁻¹) * c⁻¹, (mem_normalizer_iff.mp hcN _).mp bV.2⟩ with hdV
    have hb : (S.frame.ψ bV : G6.PermMod 6) = G6.permAct 6 U3.c2perm e45 := by
      have h1 := S.psi_conj ⟨c, hcN⟩ zV
      rw [hcρ] at h1
      rw [← h45, ← G6.coreAct_coe, ← h1]
    have hd : (S.frame.ψ dV : G6.PermMod 6) =
        G6.permAct 6 U3.c2perm (G6.permAct 6 U3.c2perm e45) := by
      have h1 := S.psi_conj ⟨c, hcN⟩ bV
      rw [hcρ] at h1
      rw [← hb, ← G6.coreAct_coe, ← h1]
    obtain ⟨e1, q1, r1, eq, er, qr, eqr⟩ := c2perm_e45
    have hne : ∀ x y : ↥V, (S.frame.ψ x : G6.PermMod 6) ≠ S.frame.ψ y → (x : G) ≠ y :=
      fun x y h e => h (by rw [Subtype.ext e])
    have hne1 : ∀ x : ↥V, (S.frame.ψ x : G6.PermMod 6) ≠ 1 → (x : G) ≠ 1 := fun x h e => h (by
      have : x = 1 := Subtype.ext e
      rw [this, map_one]
      rfl)
    have hmul := mul_mul_eq_one_of_card_four h9 (fun u hu => h2V0 u (h7 ▸ hu).1)
      (h7 ▸ hzU1) (h7 ▸ hU1 c hcL2 z hzU1) (h7 ▸ hU1 c hcL2 _ (hU1 c hcL2 z hzU1))
      (hne1 zV (by rw [h45]; exact e1)) (hne1 bV (by rw [hb]; exact q1))
      (hne1 dV (by rw [hd]; exact r1)) (hne zV bV (by rw [h45, hb]; exact eq))
      (hne zV dV (by rw [h45, hd]; exact er)) (hne bV dV (by rw [hb, hd]; exact qr))
    apply eqr
    have h1 : zV * bV * dV = 1 := Subtype.ext hmul
    have h2 := congrArg (fun x => (S.frame.ψ x : G6.PermMod 6)) h1
    simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] at h2
    rw [h45, hb, hd] at h2
    exact h2
  refine ⟨hpsi, ?_⟩
  have hzVZ : S.zV ∈ quasithinOmegaOneCenter T := U3.s134_zV_mem_Z S
  have hzVL : S.zV ∈ centralizer (L : Set G) := (S.mem_ZV_iff.2 (Or.inr rfl)).2
  have hzVU2 : S.zV ∈ U3.v0Of T H₂ (U3.l2Of S ⊔ T) ⊓ centralizer (U3.l2Of S : Set G) :=
    mem_inf.2 ⟨le_conjClosure _ _ hzVZ,
      centralizer_le (SetLike.coe_subset_coe.2 (U3.s134_L2_le_L S)) hzVL⟩
  have hex : ∃ k ∈ H₂, (∃ m : ℕ, Odd m ∧ k ^ m = 1) ∧ k * S.zV * k⁻¹ ≠ S.zV := by
    by_contra hno
    push Not at hno
    have hO : oTwoRes H₂ ≤ centralizer ({S.zV} : Set G) := by
      rw [oTwoRes, closure_le]
      rintro k ⟨hk, hodd⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      have h1 := hno k hk hodd
      calc k * S.zV = k * S.zV * k⁻¹ * k := by group
        _ = S.zV * k := by rw [h1]
    have hTz : T ≤ centralizer ({S.zV} : Set G) := fun t ht =>
      mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.1 hzVZ).2.1 t ht)
    have hH₂z : H₂ ≤ centralizer ({S.zV} : Set G) :=
      (le_oTwoRes_sup_of_isSylowTwoOf (A5.isSylowTwoOf_of_le S.h13.sylow hstar.1.1)).trans
        (sup_le hO hTz)
    apply hinc2
    intro g hg
    refine centralizer_Z_le_L1T S hM hZV1 ?_
    rw [hZV1]
    refine mem_centralizer_V1 S D.zV1 D.zL (mem_centralizer_iff.2 fun x hx => ?_)
      (mem_centralizer_singleton_iff.mp (hH₂Gz hg))
    rcases S.mem_ZV_iff.1 hx with rfl | rfl
    · simp
    · exact (mem_centralizer_singleton_iff.mp (hH₂z hg)).symm
  obtain ⟨k, hkH₂, hodd, hkz⟩ := hex
  have hkK : k ∈ K := by
    rw [← oTwoRes_sup_eq_of_faithful D.Kf D.T_le_K]
    exact subset_closure ⟨hH₂KT hkH₂, hodd⟩
  have hkK₂ : k ∈ oTwoRes H₂ := subset_closure ⟨hkH₂, hodd⟩
  have hkU2 : k ∈ normalizer ((⁅U3.v0Of T H₂ (U3.l2Of S ⊔ T), oTwoRes H₂⁆ : Subgroup G) :
      Set G) :=
    SBd5.mem_normalizer_commutator_of (hV0N (le_sup_left (b := U3.l2Of S ⊔ T) hkH₂))
      (le_normalizer hkK₂)
  rw [h6] at hkU2 h8
  have hconj : ∀ x ∈ U3.v0Of T H₂ (U3.l2Of S ⊔ T) ⊓ centralizer (U3.l2Of S : Set G),
      k * x * k⁻¹ ∈ U3.v0Of T H₂ (U3.l2Of S ⊔ T) ⊓ centralizer (U3.l2Of S : Set G) :=
    fun x hx => (mem_normalizer_iff.mp hkU2 x).mp hx
  obtain ⟨a, ha⟩ : ∃ a, k * S.zV * k⁻¹ = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, k * a * k⁻¹ = b := ⟨_, rfl⟩
  have haU : a ∈ U3.v0Of T H₂ (U3.l2Of S ⊔ T) ⊓ centralizer (U3.l2Of S : Set G) :=
    ha ▸ hconj _ hzVU2
  have hbU : b ∈ U3.v0Of T H₂ (U3.l2Of S ⊔ T) ⊓ centralizer (U3.l2Of S : Set G) :=
    hb ▸ hconj _ haU
  have hzV1 : S.zV ≠ 1 := S.zV_ne_one
  have hza : S.zV ≠ a := fun h => hkz (ha.trans h.symm)
  have ha1 : a ≠ 1 := fun h => hzV1 (by
    have e : S.zV = k⁻¹ * (k * S.zV * k⁻¹) * k := by group
    rw [e, ha, h]
    group)
  have hb1 : b ≠ 1 := fun h => ha1 (by
    have e : a = k⁻¹ * (k * a * k⁻¹) * k := by group
    rw [e, hb, h]
    group)
  have hab : a ≠ b := fun h => hkz (by
    have h1 : k * a = a * k := by
      calc k * a = k * a * k⁻¹ * k := by group
        _ = a * k := by rw [hb, ← h]
    rw [ha]
    calc a = k⁻¹ * (k * a) := by group
      _ = k⁻¹ * (a * k) := by rw [h1]
      _ = k⁻¹ * (k * S.zV * k⁻¹) * k := by rw [ha]; group
      _ = S.zV := by group)
  have hzb : S.zV ≠ b := fun h => by
    obtain ⟨m, ⟨j, rfl⟩, hm⟩ := hodd
    have hk2z : k ^ 2 * S.zV * (k ^ 2)⁻¹ = S.zV := by
      calc k ^ 2 * S.zV * (k ^ 2)⁻¹ = k * (k * S.zV * k⁻¹) * k⁻¹ := by rw [pow_two]; group
        _ = S.zV := by rw [ha, hb, ← h]
    have hk2 : ∀ i : ℕ, (k ^ 2) ^ i * S.zV * ((k ^ 2) ^ i)⁻¹ = S.zV := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        calc (k ^ 2) ^ (i + 1) * S.zV * ((k ^ 2) ^ (i + 1))⁻¹ =
            (k ^ 2) ^ i * (k ^ 2 * S.zV * (k ^ 2)⁻¹) * ((k ^ 2) ^ i)⁻¹ := by group
          _ = S.zV := by rw [hk2z, ih]
    have hk : k = (k ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, hm, one_mul]
    apply hkz
    rw [hk]
    exact hk2 (j + 1)
  have hmul := mul_mul_eq_one_of_card_four h8 (fun u hu => h2V0 u (mem_inf.1 hu).1) hzVU2 haU
    hbU hzV1 ha1 hb1 hza hzb hab
  refine ⟨?_, k, hkK, hkH₂, hodd, hkz, by rw [ha, hb]; exact hmul⟩
  have hcommV : ∀ x ∈ U3.v0Of T H₂ (U3.l2Of S ⊔ T), ∀ y ∈ U3.v0Of T H₂ (U3.l2Of S ⊔ T),
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hV0e.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbeq : b = S.zV * a := by
    have h1 : S.zV * a * (S.zV * a) = 1 :=
      h2V0 _ (mul_mem (mem_inf.1 hzVU2).1 (mem_inf.1 haU).1)
    calc b = (S.zV * a * (S.zV * a)) * b := by rw [h1, one_mul]
      _ = S.zV * a * (S.zV * a * b) := by group
      _ = S.zV * a := by rw [hmul, mul_one]
  have hcomm_a : ⁅a, k⁆ = S.zV := by
    rw [commutatorElement_def]
    have h1 : k * a⁻¹ * k⁻¹ = b⁻¹ := by rw [← hb]; group
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h2V0 b (mem_inf.1 hbU).1)
    calc a * k * a⁻¹ * k⁻¹ = a * (k * a⁻¹ * k⁻¹) := by group
      _ = a * (S.zV * a) := by rw [h1, hbinv, hbeq]
      _ = S.zV * (a * a) := by
        rw [← mul_assoc, hcommV a (mem_inf.1 haU).1 S.zV (mem_inf.1 hzVU2).1, mul_assoc]
      _ = S.zV := by rw [h2V0 a (mem_inf.1 haU).1, mul_one]
  have haVH : a ∈ conjClosure (quasithinOmegaOneCenter T) K := ha ▸ mem_conjClosure hkK hzVZ
  have hzVW : S.zV ∈ W := by
    rw [← hVKW, ← hcomm_a]
    exact commutator_mem_commutator haVH hkK
  intro x hx
  rcases S.mem_ZV_iff.1 hx with rfl | rfl
  · exact one_mem _
  · exact hzVW

end Data13410

end CFSG.Quasithin.H13.NQS134
