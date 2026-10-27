module

public import CFSG.Quasithin.H13.NQS13410Y
public import CFSG.Quasithin.H13.NQS134HatNu
public import CFSG.Quasithin.H13.NQS13410X

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative commutatorElement

theorem l3_comm_pow_four : ∀ g : L3.Γ, g ≠ 1 → g ^ 4 = 1 →
    ∃ h : L3.Γ, (g * h * g⁻¹ * h⁻¹) ^ 4 ≠ 1 := by
  decide +kernel

theorem l3_moves : ∀ p : L3.Vec, p ≠ 0 → ∃ g : L3.Γ, L3.act g p ≠ p := by decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem isTwoReducedIn_of_l32 {K W X : Subgroup G} (C : L3Coords K W) (hKX : K ≤ X)
    (hWX : W ≤ X) (hXW : X ≤ normalizer (W : Set G)) (hWe : IsElemAbelian 2 W) :
    IsTwoReducedIn X W := by
  refine ⟨hWX, hXW, hWe, fun D hDX hXD h2 => fun d hd => ?_⟩
  by_contra hdC
  have hdN : d ∈ normalizer (W : Set G) := hXW (hDX hd)
  have hρ1 : C.ρ ⟨d, hdN⟩ ≠ 1 := fun h => hdC ((C.ker _).1 h)
  have h4 : ∀ e : G, ∀ he : e ∈ D, C.ρ ⟨e, hXW (hDX he)⟩ ^ 4 = 1 := by
    intro e he
    obtain ⟨k, hk⟩ := h2 e he
    have hek : e ^ 2 ^ k ∈ normalizer (W : Set G) := pow_mem (hXW (hDX he)) _
    have h1 : C.ρ ⟨e ^ 2 ^ k, hek⟩ = 1 := (C.ker _).2 hk
    have e1 : (⟨e ^ 2 ^ k, hek⟩ : ↥(normalizer (W : Set G))) = ⟨e, hXW (hDX he)⟩ ^ 2 ^ k :=
      Subtype.ext (by rw [Subgroup.coe_pow])
    rw [e1, map_pow] at h1
    exact l3_pow_four _ (l3_pow_eight (k := k) h1)
  obtain ⟨h, hh⟩ := l3_comm_pow_four _ hρ1 (h4 d hd)
  obtain ⟨k, hkK, hkh⟩ := C.image_K h
  have hkX : (k : G) ∈ X := hKX hkK
  have hkd : (k : G) * d⁻¹ * (k : G)⁻¹ ∈ D :=
    (mem_normalizer_iff.mp (hXD hkX) _).mp (inv_mem hd)
  have he : d * (k : G) * d⁻¹ * (k : G)⁻¹ ∈ D := by
    have e : d * (k : G) * d⁻¹ * (k : G)⁻¹ = d * ((k : G) * d⁻¹ * (k : G)⁻¹) := by group
    rw [e]
    exact mul_mem hd hkd
  have h5 := h4 _ he
  have e2 : (⟨d * (k : G) * d⁻¹ * (k : G)⁻¹, hXW (hDX he)⟩ : ↥(normalizer (W : Set G))) =
      ⟨d, hdN⟩ * k * ⟨d, hdN⟩⁻¹ * k⁻¹ := rfl
  rw [e2, map_mul, map_mul, map_mul, map_inv, map_inv, hkh] at h5
  exact hh h5

theorem relIndex_le_sixteen_of_l3Block {K R : Subgroup G} (hB : IsLnBlock K 3) {x : G}
    (hxK : x ∈ K) (hx3 : x ^ 3 = 1) (hR2 : IsPGroup 2 ↥R) (hQR : pCoreOf 2 K ≤ R)
    (hRK : R ≤ normalizer (K : Set G)) (hxR : x ∈ normalizer (R : Set G)) :
    (centralizer ({x} : Set G)).relIndex R ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLQ := (U3.block_cards (Or.inl hB)).2
  obtain ⟨-, α, hα, hker, β, hβ, hβker, -⟩ := hB
  set Q := pCoreOf 2 K with hQ
  set C := centralizer ({x} : Set G) with hC
  have hQ2 : IsPGroup 2 Q := LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hKQn : K ≤ normalizer (Q : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hUQ : blockU K ≤ Q := le_normalizer_iff_commutator_le_left.mp hKQn
  have hU2 : IsPGroup 2 (blockU K) := hQ2.to_le hUQ
  have hxQ : x ∈ normalizer (Q : Set G) := hKQn hxK
  have hxU : x ∈ normalizer (blockU K : Set G) :=
    mem_normalizer_commutator (hKQn hxK) (le_normalizer hxK)
  have hQU : Q ≤ normalizer (blockU K : Set G) := fun q hq =>
    mem_normalizer_commutator (le_normalizer hq)
      (le_normalizer (LieType.BorelTits.pCoreOf_le 2 K hq))
  have hUZ : (blockZ K).relIndex (blockU K) = 8 := by
    have := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβ).toEquiv
    rw [hβker] at this
    rw [relIndex, index_eq_card, this]
    change Nat.card (Fin 3 → ZMod 2) = 8
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hZC : blockZ K ≤ C ⊓ blockU K := by
    refine le_inf (fun z hz => ?_) inf_le_left
    rw [hC, mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.mp (mem_inf.mp hz).2) x hxK).symm
  have hcU8 : C.relIndex (blockU K) ≤ 8 := by
    calc C.relIndex (blockU K) = (C ⊓ blockU K).relIndex (blockU K) :=
          (inf_relIndex_right C (blockU K)).symm
      _ ≤ (blockZ K).relIndex (blockU K) :=
          relIndex_le_of_le_left hZC
            (index_ne_zero_of_finite (H := (blockZ K).subgroupOf (blockU K)))
      _ = 8 := hUZ
  have hcU : C.relIndex (blockU K) ≤ 4 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hU2
    exact U3.le_four_of_le_eight (U3.relIndex_centralizer_modEq_one hx3 hxU hU2)
      (hn ▸ index_dvd_card _) hcU8
  have hcommQ : ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ blockU K := by
    intro q hq
    have h := commutator_mem_commutator hxK hq
    rw [commutator_comm] at h
    rwa [commutatorElement_def] at h
  have hcQ : C.relIndex Q = C.relIndex (blockU K) := by
    have h1 := U3.sup_inf_centralizer_eq hx3 hU2 hUQ hQU hxU hcommQ
    have hmul := U3.relIndex_centralizer_eq_mul (x := x) hUQ hQU
    rw [h1, relIndex_self, one_mul] at hmul
    exact hmul
  have hQRK : Q ≤ R ⊓ K := le_inf hQR (LieType.BorelTits.pCoreOf_le 2 K)
  have hRK2 : IsPGroup 2 ↥(R ⊓ K) := hR2.to_le inf_le_left
  have hRKQ : R ⊓ K ≤ normalizer (Q : Set G) := inf_le_right.trans hKQn
  have hxRK : x ∈ normalizer ((R ⊓ K : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf (mem_inf.2 ⟨hxR, le_normalizer hxK⟩)
  have h8 : Q.relIndex (R ⊓ K) ≤ 8 := by
    have h1 := relIndex_mul_relIndex Q (R ⊓ K) K hQRK inf_le_right
    have hdvd : Q.relIndex (R ⊓ K) ∣ Q.relIndex K := Dvd.intro _ h1
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hRK2
    have hdvd2 : Q.relIndex (R ⊓ K) ∣ 2 ^ n := hn ▸ index_dvd_card _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
    rw [hk] at hdvd ⊢
    by_contra h9
    have hk4 : 4 ≤ k := by
      by_contra h10
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h16 : 2 ^ 4 ∣ Q.relIndex K := (Nat.pow_dvd_pow 2 hk4).trans hdvd
    rcases hLQ with h | h <;> rw [h] at h16 <;> norm_num at h16
  have hcRK : C.relIndex (R ⊓ K) ≤ 4 * C.relIndex Q := by
    rw [U3.relIndex_centralizer_eq_mul (x := x) hQRK hRKQ]
    exact Nat.mul_le_mul_right _ (U3.relIndex_sup_le_four hx3 hRK2 hQRK hRKQ hxQ hxRK h8)
  have hRn : R ≤ normalizer ((R ⊓ K : Subgroup G) : Set G) := fun r hr =>
    inf_normalizer_le_normalizer_inf (mem_inf.2 ⟨le_normalizer hr, hRK hr⟩)
  have hcommR : ∀ r ∈ R, x * r * x⁻¹ * r⁻¹ ∈ R ⊓ K := by
    intro r hr
    refine mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.mp hxR r).mp hr) (inv_mem hr), ?_⟩
    have h1 : r * x⁻¹ * r⁻¹ ∈ K := (mem_normalizer_iff.mp (hRK hr) _).mp (inv_mem hxK)
    have e : x * r * x⁻¹ * r⁻¹ = x * (r * x⁻¹ * r⁻¹) := by group
    rw [e]
    exact mul_mem hxK h1
  have hcR : C.relIndex R = C.relIndex (R ⊓ K) := by
    have h2 := U3.sup_inf_centralizer_eq hx3 hRK2 inf_le_left hRn hxRK hcommR
    have hmul := U3.relIndex_centralizer_eq_mul (x := x) (inf_le_left : R ⊓ K ≤ R) hRn
    rw [h2, relIndex_self, one_mul] at hmul
    exact hmul
  rw [hcR]
  omega

omit [Finite G] in
theorem isSylowTwoOf_restrict {P H A : Subgroup G} (hP : IsSylowTwoOf P A) (hPH : P ≤ H)
    (hHA : H ≤ A) : IsSylowTwoOf P H := by
  refine ⟨hPH, hP.2.1, fun h => hP.2.2 ?_⟩
  show 2 ∣ P.relIndex A
  rw [← relIndex_mul_relIndex P H A hPH hHA]
  exact Dvd.dvd.mul_right h _

theorem c137_KR (hC137 : U3.C137StatementFiveZ) (S : A6.Setting134 G T L V) {K W : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K) (hTK : T ≤ normalizer (K : Set G))
    (hTsyl : IsSylowTwoOf T (K ⊔ T)) (hcharK : CharTwo K)
    (hK3 : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1)
    [IsMulCommutative ↥W] (hnat : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1)
    (C : L3Coords K W) (hKW : K ≤ normalizer (W : Set G)) (hTW : T ≤ normalizer (W : Set G))
    (hWK : ⁅W, K⁆ = W) (hWT : W ≤ T) (hWe : IsElemAbelian 2 W)
    (hCK : K ⊓ centralizer (W : Set G) ≤ pCoreOf 2 K) {u : G} (huW : u ∈ W) (hu1 : u ≠ 1)
    (huT : u ∈ centralizer (T : Set G)) :
    U3.CharNormal (baum (pCoreOf 2 ((K ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ⊓
        centralizer ({u} : Set G)))) (K ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ∨
      IsLnBlock K 3 ∨
      Nat.card ↥(autOn (K ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) W) = 12096 ∨
      (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hR
  set X := K ⊔ R with hX
  set TX := T ⊓ X with hTX
  set M₀ := X ⊓ centralizer ({u} : Set G) with hM₀
  have hRT : R ≤ T := s134_R_le_T S
  have hR2 : IsPGroup 2 ↥R := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRK : R ≤ normalizer (K : Set G) := hRT.trans hTK
  have hL1TR : L₁ ⊔ T ≤ normalizer (R : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hTX' : T ≤ normalizer (X : Set G) := le_normalizer_sup_of hRK hTK (le_sup_right.trans hL1TR)
  have hcharX : CharTwo X := charTwo_sup_of_normalizes hR2 hRK hcharK
  have hXKT : X ≤ K ⊔ T := sup_le le_sup_left (hRT.trans le_sup_right)
  have hsylX : IsSylowTwoOf TX X :=
    A4.isSylowTwoOf_inf_normal hTsyl hXKT (sup_le (le_sup_left.trans le_normalizer) hTX')
  have hRTX : R ≤ TX := le_inf hRT le_sup_right
  have hXeq : K ⊔ TX = X :=
    le_antisymm (sup_le le_sup_left inf_le_right) (sup_le le_sup_left (hRTX.trans le_sup_right))
  have hdecomp : ∀ x ∈ X, ∃ l ∈ K, ∃ t ∈ TX, x = l * t := fun x hx => by
    obtain ⟨k, hk, r, hr, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hRK hx
    exact ⟨k, hk, r, hRTX hr, rfl⟩
  have hcomp : K ∈ cComp X := by
    obtain ⟨hne, hperf, hsub, hmin⟩ := hKf.1.2.1
    refine ⟨hne, hperf, ?_, fun K' hK'K hK'ne hK'perf hK'sub => ?_⟩
    · exact IsSubnormal.step le_sup_left (Subgroup.normal_subgroupOf_of_le_normalizer
        (_root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hRK)) (IsSubnormal.refl _)
    · exact hmin K' hK'K hK'ne hK'perf
        (A3.subnormal_trans (A3.subnormal_of_le_of_le hK'sub hK'K.le le_sup_left) hsub)
  have hautT : autOn TX W ≤ autOn K W := by
    rw [autOn_eq_top_of_l32 hnat]
    exact le_top
  have huC : T ≤ centralizer ({u} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.mp huT t ht)
  have hTXM : TX ≤ M₀ := le_inf inf_le_right (inf_le_left.trans huC)
  set uW : ↥W := ⟨u, huW⟩ with huWdef
  have hp0 : C.c uW ≠ 0 := C.c_ne_zero (fun h => hu1 (congrArg Subtype.val h))
  have hfixu : ∀ g : ↥(normalizer (W : Set G)),
      L3.act (C.ρ g) (C.c uW) = C.c uW ↔ (g : G) ∈ centralizer ({u} : Set G) := by
    intro g
    rw [mem_centralizer_singleton_iff, ← C.fix_iff g uW]
    constructor
    · intro h
      calc (g : G) * u = (g : G) * u * (g : G)⁻¹ * g := by group
        _ = u * g := by rw [h]
    · intro h
      show (g : G) * u * (g : G)⁻¹ = u
      rw [h, mul_inv_cancel_right]
  have huK : ¬ K ≤ centralizer ({u} : Set G) := fun h => by
    obtain ⟨γ, hγ⟩ := l3_moves _ hp0
    obtain ⟨g, hgK, hgγ⟩ := C.image_K γ
    exact hγ (hgγ ▸ (hfixu g).2 (h hgK))
  have hM₀X : M₀ < X := lt_of_le_of_ne inf_le_left fun h =>
    huK (le_sup_left.trans (h.symm.le.trans inf_le_right))
  have hO2TX : pCoreOf 2 K ≤ TX :=
    le_inf (pCoreOf_le_T_of_sylow hTK hTsyl) ((LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
  have D : ParData K TX W M₀ C.ρ ⊤ (l3Stab (C.c uW)) :=
    { KU := hKW
      TK := inf_le_left.trans hTK
      L1T_le := inf_le_left.trans hXeq.symm.le
      T_le := hTXM
      ker := fun g hgK h1 => hO2TX (hCK (mem_inf.2 ⟨hgK, (C.ker g).1 h1⟩))
      img := fun γ _ => C.image_K γ
      img_le := fun _ _ => mem_top _
      P_iff := fun g hgK => by
        rw [mem_l3Stab, hfixu]
        exact ⟨fun h => mem_inf.2 ⟨mem_sup_left hgK, h⟩, fun h => (mem_inf.1 h).2⟩ }
  have hmax : ∀ H : Subgroup G, M₀ ≤ H → H ≤ X → H = M₀ ∨ H = X := fun H h1 h2 => by
    rcases D.eq_or_eq_of_le_sup le_top (fun Y hY _ => l3Stab_max hp0 hY) h1
      (h2.trans hXeq.symm.le) with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hXeq)
  have hWK' : W ≤ K := by
    rw [← hWK]
    exact le_normalizer_iff_commutator_le_right.mp (hWT.trans hTK)
  have hXW : X ≤ normalizer (W : Set G) := sup_le hKW (hRT.trans hTW)
  have hredX := isTwoReducedIn_of_l32 C le_sup_left (hWK'.trans le_sup_left) hXW hWe
  have hW1 : W ≠ ⊥ := fun h => hu1 (by rw [h] at huW; exact mem_bot.1 huW)
  have hWK1 : ⁅W, K⁆ ≠ ⊥ := by
    rw [hWK]
    exact hW1
  have hclause : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 →
      Nat.card ↥⁅W, K⁆ = 8 ∧ ∃ v ∈ ⁅W, K⁆, v ≠ 1 ∧ M₀ = X ⊓ centralizer ({v} : Set G) :=
    fun _ => ⟨by rw [hWK]; exact card_eq_eight_of_l32 hnat, u, by rw [hWK]; exact huW, hu1, rfl⟩
  rcases hC137 G X TX W K M₀ M₀ hcharX hsylX hdecomp hcomp hcharK (Or.inl hK3)
      (Or.inr (Or.inl hautT)) hTXM le_rfl hM₀X hmax (Or.inl rfl) hredX hWK1 hclause with
    h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (h.1 hK3))
  · exact Or.inr (Or.inr (Or.inl h.1))
  · exact Or.inr (Or.inr (Or.inr h.1))

theorem centralizer_u_le_L1T (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V) {K W : Subgroup G} (hsyl : IsSylowTwoOf (T ⊓ K) K)
    (hCK : K ⊓ centralizer (W : Set G) ≤ pCoreOf 2 K) (C : L3Coords K W)
    (hKW : K ≤ normalizer (W : Set G)) {u : G} (huW : u ∈ W) (hu1 : u ≠ 1)
    (huT : u ∈ centralizer (T : Set G))
    (hKuZ : K ⊓ centralizer ({u} : Set G) ≤ centralizer (quasithinOmegaOneCenter T : Set G)) :
    K ⊓ centralizer ({u} : Set G) ≤ L₁Of L (fsuV1 T V) ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := K ⊓ centralizer ({u} : Set G) with hY
  have hTKY : T ⊓ K ≤ Y := le_inf inf_le_right fun t ht =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.mp huT t (mem_inf.1 ht).1)
  have hsylY : IsSylowTwoOf (T ⊓ K) Y := isSylowTwoOf_restrict hsyl hTKY inf_le_left
  set uW : ↥W := ⟨u, huW⟩ with huWdef
  have hp0 : C.c uW ≠ 0 := C.c_ne_zero (fun h => hu1 (congrArg Subtype.val h))
  have hO : oTwoRes Y ≤ L₁Of L (fsuV1 T V) := by
    refine (closure_le _).2 fun x hx => ?_
    obtain ⟨hxY, m, hm, hxm⟩ := hx
    obtain ⟨hxK, hxu⟩ := mem_inf.1 hxY
    have hxW : x ∈ normalizer (W : Set G) := hKW hxK
    have hxp : L3.act (C.ρ ⟨x, hxW⟩) (C.c uW) = C.c uW := by
      refine (C.fix_iff ⟨x, hxW⟩ uW).1 ?_
      show x * u * x⁻¹ = u
      rw [mem_centralizer_singleton_iff.mp hxu, mul_inv_cancel_right]
    have hρm : C.ρ ⟨x, hxW⟩ ^ m = 1 := by
      rw [← map_pow]
      have : (⟨x, hxW⟩ : ↥(normalizer (W : Set G))) ^ m = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hxm)
      rw [this, map_one]
    have hρ3 : C.ρ ⟨x, hxW⟩ ^ 3 = 1 := by
      rcases l3Stab_cube_or _ hp0 _ hxp with h | h
      · exact h
      · have hcop : Nat.Coprime 4 m := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hm)
        rw [orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
          (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_of_pow_eq_one hρm)), one_pow]
    have hx3 : x ^ 3 = 1 := by
      have h1 : x ^ 3 ∈ K ⊓ centralizer (W : Set G) := by
        refine mem_inf.2 ⟨pow_mem hxK 3, ?_⟩
        have h2 : C.ρ (⟨x, hxW⟩ ^ 3) = 1 := by rw [map_pow, hρ3]
        simpa using (C.ker _).1 h2
      obtain ⟨s, hs⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hCK h1⟩
      have hs' : (x ^ 3) ^ 2 ^ s = 1 := by
        have := congrArg Subtype.val hs
        simpa using this
      have hm' : (x ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
      exact mem_bot.1 (mem_of_pow_odd_mem hs' hm (by rw [hm']; exact one_mem _))
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    · exact mem_L1_of_orderOf_three h1332 h1228 S (hKuZ hxY) (orderOf_eq_prime hx3 hx1)
  exact (le_oTwoRes_sup_of_isSylowTwoOf hsylY).trans
    (sup_le_sup hO (inf_le_left : T ⊓ K ≤ T))

theorem pCoreOf_centralizer_u_eq (S : A6.Setting134 G T L V) {K : Subgroup G}
    (hTK : T ≤ normalizer (K : Set G)) (hTsyl : IsSylowTwoOf T (K ⊔ T))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G)) {u : G}
    (huZ : u ∈ quasithinOmegaOneCenter T)
    (hKu : K ⊓ centralizer ({u} : Set G) ≤ L₁Of L (fsuV1 T V) ⊔ T) :
    pCoreOf 2 ((K ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ⊓ centralizer ({u} : Set G)) =
      pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hR
  set X := K ⊔ R with hX
  set M₀ := X ⊓ centralizer ({u} : Set G) with hM₀
  have hRT : R ≤ T := s134_R_le_T S
  have hR2 : IsPGroup 2 ↥R := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRK : R ≤ normalizer (K : Set G) := hRT.trans hTK
  have hL1TR : L₁ ⊔ T ≤ normalizer (R : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hZC : ∀ {g : G}, g ∈ centralizer (quasithinOmegaOneCenter T : Set G) →
      g ∈ centralizer ({u} : Set G) := fun {g} hg =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.mp hg u huZ).symm
  have hTu : T ≤ centralizer ({u} : Set G) := fun t ht =>
    hZC (mem_centralizer_iff.2 fun z hz =>
      (mem_centralizer_iff.mp (U3.s134_Z_le_center T hz).2 t ht).symm)
  have hRM₀ : R ≤ M₀ := le_inf le_sup_right (hRT.trans hTu)
  have hM₀R : M₀ ≤ normalizer (R : Set G) := by
    intro m hm
    obtain ⟨hmX, hmu⟩ := mem_inf.1 hm
    obtain ⟨k, hk, r, hr, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hRK hmX
    have hku : k ∈ centralizer ({u} : Set G) := by
      have e : k = k * r * r⁻¹ := by group
      rw [e]
      exact mul_mem hmu (inv_mem (hTu (hRT hr)))
    exact mul_mem (hL1TR (hKu (mem_inf.2 ⟨hk, hku⟩))) (le_normalizer hr)
  have h1 : R ≤ pCoreOf 2 M₀ := LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRM₀ hM₀R hR2
  have hTX' : T ≤ normalizer (X : Set G) := le_normalizer_sup_of hRK hTK (le_sup_right.trans hL1TR)
  have hL1X : L₁ ≤ normalizer (X : Set G) := le_normalizer_sup_of hRK hL1K (le_sup_left.trans hL1TR)
  have hNu : L₁ ⊔ T ≤ normalizer (centralizer ({u} : Set G) : Set G) :=
    (sup_le (fun g hg => hZC (hL1Z hg)) hTu).trans le_normalizer
  have hNM₀ : L₁ ⊔ T ≤ normalizer (M₀ : Set G) :=
    (le_inf (sup_le hL1X hTX') hNu).trans inf_normalizer_le_normalizer_inf
  have hXKT : X ≤ K ⊔ T := sup_le le_sup_left (hRT.trans le_sup_right)
  have hsylX : IsSylowTwoOf (T ⊓ X) X :=
    A4.isSylowTwoOf_inf_normal hTsyl hXKT (sup_le (le_sup_left.trans le_normalizer) hTX')
  have hsylM : IsSylowTwoOf (T ⊓ X) M₀ :=
    isSylowTwoOf_restrict hsylX (le_inf inf_le_right (inf_le_left.trans hTu)) inf_le_left
  have hOT : pCoreOf 2 M₀ ≤ T :=
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylM).trans inf_le_left
  have h2 : pCoreOf 2 M₀ ≤ R :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
      (hNM₀.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact le_antisymm h2 h1

theorem not_l32_of_hat_of_mem (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L)
    {K W : Subgroup G} (hKf : quasithinIsFaithfulLocal T K) (hKM : ¬ K ≤ normalizer (L : Set G))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hK3 : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1)
    [IsMulCommutative ↥W] (hnat : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1)
    (hKW : K ≤ normalizer (W : Set G)) (hTW : T ≤ normalizer (W : Set G)) (hWK : ⁅W, K⁆ = W)
    (hWR : W ≤ reducedAggregate (K ⊔ T)) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G))
    {y : G} (hyK : y ∈ K) (hyL1 : y ∈ L₁Of L (fsuV1 T V)) (hy3 : y ^ 3 = 1)
    (hyW : y ∉ centralizer (W : Set G)) (hyV : y ∈ centralizer (V : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hR
  set Z := quasithinOmegaOneCenter T with hZdef
  obtain ⟨-, ⟨hTK, -, -, -⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hZK : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    center_eq_bot_of_simple_types (Or.inr (Or.inl hK3))
  have hCK : K ⊓ centralizer (W : Set G) ≤ pCoreOf 2 K := by
    rw [← ho2Z]
    exact o2Z_le_pCoreOf_of_center hZK
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
  have hcharK : CharTwo K := A5.charTwo_of_faithful S.h13.qtke.2.1 S.h13.sylow hKf
  have hRT : R ≤ T := s134_R_le_T S
  have hR2 : IsPGroup 2 ↥R := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRK : R ≤ normalizer (K : Set G) := hRT.trans hTK
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hyL : y ∈ L := hL1L hyL1
  have hyZL : y ∈ A6.o2Z L := U3.s134_centralizer_le_o2Z S ⟨hyL, hyV⟩
  have hred := twoReduced_R2 (K ⊔ T)
  have hWe : IsElemAbelian 2 W := ⟨‹_›, fun w hw => hred.2.2.1.2 w (hWR hw)⟩
  have hWT : W ≤ T := (hWR.trans (R2_le_pCoreOf (K ⊔ T))).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)
  have hW1 : W ≠ ⊥ := by
    intro h
    have h8 := card_eq_eight_of_l32 hnat
    rw [h, Subgroup.card_bot] at h8
    omega
  obtain ⟨u, huW, huT, hu1⟩ := exists_mem_centralizer_ne_one hKf.1.1 hWT hTW hW1
  have huZ : u ∈ Z := subset_closure ⟨⟨hWT huW, huT⟩, hred.2.2.1.2 u (hWR huW)⟩
  obtain ⟨C⟩ := exists_l3Coords hnat
  have hKuZ : K ⊓ centralizer ({u} : Set G) ≤ centralizer (Z : Set G) := by
    obtain ⟨D⟩ := hnat.toL3Coord
    have h0 : l3coord D (1 : ↥W) = 0 := by
      show Multiplicative.toAdd (D.β ⟨1, mem_top 1⟩) = 0
      rw [show (⟨1, mem_top 1⟩ : ↥(⊤ : Subgroup ↥W)) = 1 from rfl, map_one]
      rfl
    have hne : ∀ w : ↥W, w ≠ 1 → l3coord D w ≠ 0 := fun w hw h =>
      hw (l3coord_injective D (h.trans h0.symm))
    intro k hk
    obtain ⟨hkK, hku⟩ := mem_inf.1 hk
    rw [mem_centralizer_iff]
    intro z hz
    have hZT : Z ≤ T := fun x hx => (U3.s134_Z_le_center T hx).1
    have hcN : U3.cZ T K ≤ normalizer (W : Set G) := (inf_le_left.trans hZT).trans hTW
    obtain ⟨w, hw, c, hc, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hcN (hZW hz)
    have hwZ : w ∈ Z := by
      have e : w = w * c * c⁻¹ := by group
      rw [e]
      exact mul_mem hz (inv_mem (mem_inf.1 hc).1)
    have hwT : w ∈ centralizer (T : Set G) := (U3.s134_Z_le_center T hwZ).2
    have hkw : w * k = k * w := by
      by_cases hw1 : (⟨w, hw⟩ : ↥W) = 1
      · rw [show w = 1 from congrArg Subtype.val hw1, one_mul, mul_one]
      · have h1 := l32_coord_unique hKW hsyl D ⟨w, hw⟩ ⟨u, huW⟩ hwT huT (hne _ hw1)
          (hne _ (fun h => hu1 (congrArg Subtype.val h)))
        have h2 : w = u := congrArg Subtype.val (l3coord_injective D h1)
        rw [h2]
        exact (mem_centralizer_singleton_iff.mp hku).symm
    have hkc : c * k = k * c := (mem_centralizer_iff.mp (mem_inf.1 hc).2 k hkK).symm
    calc w * c * k = w * (k * c) := by rw [mul_assoc, hkc]
      _ = k * (w * c) := by rw [← mul_assoc, hkw, mul_assoc]
  have hKu := centralizer_u_le_L1T h1332 h1228 S hsyl hCK C hKW huW hu1 huT hKuZ
  have hM₀R := pCoreOf_centralizer_u_eq S hTK hTsyl hL1K hL1Z huZ hKu
  rcases c137_KR hC137 S hKf hTK hTsyl hcharK hK3 hnat C hKW hTW hWK hWT hWe hCK huW hu1 huT with
    hCN | hB | h12096 | h6
  ·
    obtain ⟨Cc, hCB, hC1, hCchar, hXC⟩ := hCN
    rw [hM₀R, (stmt13_2_2_8Hat_of KGHatA6.hatA6OddInverts_holds G T L V S hhat).2] at hCB hCchar
    set Q := pCoreOf 2 (L ⊔ T) with hQ
    have hQT : Q ≤ T := by
      rw [hQ, ← U3.s134_cT S]
      exact inf_le_left
    have := hCchar
    have h2 : normalizer (baum Q : Set G) ≤ normalizer (Cc : Set G) := by
      have h3 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (Cc.subgroupOf (baum Q))
      rwa [Subgroup.map_subgroupOf_eq_of_le hCB] at h3
    have hLC : L ⊔ T ≤ normalizer (Cc : Set G) :=
      (LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
        ((normalizer_le_normalizer_baum Q).trans h2)
    have hCT : Cc ≤ T := hCB.trans (inf_le_left.trans hQT)
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
      (⟨Cc, hC1, S.h13.sylow.1.to_le hCT, rfl⟩ : IsTwoLocal (normalizer (Cc : Set G)))
    have hM := S.uniqueM.2 M' ⟨hM', hLC.trans hle⟩
    exact hKM ((le_sup_left.trans hXC).trans (hM ▸ hle))
  ·
    have hQK2 : IsPGroup 2 ↥(pCoreOf 2 K) := LieType.BorelTits.pCoreOf_isPGroup 2 K
    have hQKR : pCoreOf 2 K ≤ R :=
      le_R_of_le S hTK hTsyl hL1K (LieType.BorelTits.pCoreOf_le 2 K) hQK2
        (LieType.BorelTits.le_normalizer_pCoreOf 2 K)
        (hTK.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    have hyR : y ∈ normalizer (R : Set G) :=
      LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ T) (mem_sup_left hyL1)
    have h16 := relIndex_le_sixteen_of_l3Block hB hyK hy3 hR2 hQKR hRK hyR
    have hcharL : CharTwo L := A5.charTwo_of_faithful S.h13.qtke.2.1 S.h13.sylow S.h13.faithful
    have hLp : ⁅L, L⁆ = L := perfect_of_mem_cComp S.h13.faithful.1.2.1
    have hcO : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
      intro l hl
      obtain ⟨-, h⟩ := mem_o2Z_iff.1 hyZL
      have e : l * y * l⁻¹ * y⁻¹ = (y * l * y⁻¹ * l⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem (h l hl)
    have hcY : ∃ q ∈ pCoreOf 2 L, y * q ≠ q * y := by
      by_contra hno
      push Not at hno
      have hyC : y ∈ L ⊓ centralizer (pCoreOf 2 L : Set G) :=
        mem_inf.2 ⟨hyL, mem_centralizer_iff.2 fun q hq => (hno q hq).symm⟩
      obtain ⟨s, hs⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨y, hcharL hyC⟩
      have hs' : y ^ 2 ^ s = 1 := by
        have := congrArg Subtype.val hs
        simpa using this
      have hy1 : y = 1 := mem_bot.1 (mem_of_pow_odd_mem (m := 3) hs' (Nat.odd_iff.2 rfl)
        (by rw [hy3]; exact one_mem _))
      exact hyW (hy1 ▸ one_mem _)
    have h64 := four_pow_three_le_nu_pCoreOf hLp hyL hy3 hcO
      (LieType.BorelTits.pCoreOf_isPGroup 2 L) (LieType.BorelTits.le_normalizer_pCoreOf 2 L) hcY
    have hle : A6.nu y (pCoreOf 2 L) ≤ (centralizer ({y} : Set G)).relIndex R := by
      have h1 := nu_le_nu_of_le y (s134_pCoreOf_L_le_R S)
      rwa [nu_eq_relIndex y (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))] at h1
    omega
  ·
    have h1 : Nat.card ↥(autOn (K ⊔ R) W) =
        Nat.card ↥(((K ⊔ R).subgroupOf (normalizer (W : Set G))).map C.ρ) :=
      Nat.card_congr (U3.mapMulEquivOfKer (conjAct W) C.ρ C.conjAct_eq_one_iff
        ((K ⊔ R).subgroupOf (normalizer (W : Set G)))).toEquiv
    have h2 := Subgroup.card_le_card_group (((K ⊔ R).subgroupOf (normalizer (W : Set G))).map C.ρ)
    rw [card_l3Γ] at h2
    have h3 : Nat.card ↥(autOn (K ⊔ R) W) = 12096 := h12096
    omega
  ·
    have hc : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 168 :=
      card_of_statedClassicalModel_psl32 (statedClassicalModel_of_lieModel_psl32 hK3)
    have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rcases h6 with he | ⟨-, hz, ⟨e⟩⟩
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, h360] at hc
      omega
    · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (center (↥K ⧸ CFSG.pCore 2 ↥K))
      rw [Nat.card_congr e.toEquiv, h360, hz, hc] at h1
      omega

end CFSG.Quasithin.H13.NQS134
