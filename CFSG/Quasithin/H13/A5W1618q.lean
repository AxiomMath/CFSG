module

public import CFSG.Quasithin.H13.A5W1618l

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

local notation "StSL" => Assembly.LowTwoRank.StatedSL

theorem pact_e34_of_pow_three : ∀ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 → σ ≠ 1 → σ 3 = 3 →
    σ 4 = 4 → pact σ (Multiplicative.ofAdd (e2 3 4)) = Multiplicative.ofAdd (e2 3 4) ∧
      pact σ E12 ≠ E12 := by
  decide +kernel

theorem eq_one_of_natAct_eq {K : Type} [Field K] [CharP K 2] {γ : ↥(StSL 2 K)} (h3 : γ ^ 3 = 1)
    (h1 : γ ≠ 1) {m : Multiplicative (Fin 2 → K)} (hm : natAct (StSL 2 K) γ m = m) : m = 1 := by
  have hM3 : ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := by
    have := congrArg (fun g : ↥(StSL 2 K) => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h3
    simpa using this
  have hM1 : ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ 1 := fun h =>
    h1 (Subtype.ext (Units.ext (by rw [h]; rfl)))
  have hx : ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd m) =
      Multiplicative.toAdd m := congrArg Multiplicative.toAdd hm
  exact Multiplicative.toAdd.injective
    (eq_zero_of_mulVec_eq_of_pow_three (det_of_mem_statedSL γ) hM3 hM1 hx)

theorem exists_pow_three_of_isAltType {G : Type} [Group G] [Finite G] {K₀ : Subgroup G}
    {α : ↥K₀ →* ↥(alternatingGroup (Fin 5))} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥K₀) :
    ∃ y : ↥K₀, y ^ 3 = 1 ∧ ∃ j : ℕ, ((α y : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
      c3p ^ 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y₀, hy₀⟩ := hαs c3A
  obtain ⟨j, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y₀).ne'
  set y := y₀ ^ 2 ^ j with hy
  have hord : orderOf y = m := by
    rw [hy, orderOf_pow_of_dvd (by positivity) ⟨m, hn⟩, hn]
    exact Nat.mul_div_cancel_left m (by positivity)
  have hαy : ((α y : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = c3p ^ 2 ^ j := by
    rw [hy, map_pow, hy₀, Subgroup.coe_pow]
    rfl
  refine ⟨y, ?_, j, hαy⟩
  have hy3 : y ^ 3 ∈ CFSG.pCore 2 ↥K₀ := by
    rw [← hαk, MonoidHom.mem_ker, map_pow]
    apply Subtype.ext
    rw [Subgroup.coe_pow, hαy, ← pow_mul, mul_comm, pow_mul, c3p_cube, one_pow]
    rfl
  have h2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥K₀) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨k, hk⟩ := h2 ⟨y ^ 3, hy3⟩
  have hk' : (y ^ 3) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hodd : (orderOf (y ^ 3)).Coprime (2 ^ k) := by
    have h1 : orderOf (y ^ 3) ∣ m := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one,
        one_pow])
    exact Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_left h1
      (Nat.coprime_two_right.mpr hm))
  have h3 : orderOf (y ^ 3) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  rw [← orderOf_eq_one_iff, Nat.Coprime.eq_one_of_dvd hodd h3]

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_altBlock_of_natural (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} [IsMulCommutative ↥(S.WK K)] (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {K₀ : Subgroup G} (hK₀K : K₀ ≤ K)
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hK₀im : autOn K₀ (S.WK K) = S.plus K) (hshort : IsShort2 K₀) (h5 : IsAltType K₀ 5)
    {U C : Subgroup ↥(S.WK K)} {K' : Type} [Field K'] [Finite K'] {π : ↥(StSL 2 K') →* ↥(S.plus K)}
    (hK'4 : Nat.card K' = 4) (hπ : (FFModel.nat (StSL 2 K')).RealizesVia (S.plus K) U C π)
    (hCfix : ∀ g ∈ S.plus K, ∀ c ∈ C, g c = c)
    (hUV : ∀ g ∈ S.plus K, ∀ v : ↥(S.WK K), g v * v⁻¹ ∈ U) : False := by
  classical
  have hcharK : CharP K' 2 := R3c.charP_two_of_natCard_eq_two_pow (f := 2) (by rw [hK'4]; norm_num)
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hK.1 hT
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans hR.2.1
  have hK₀W := hK₀K.trans hKW
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  have hHK : K₀ ⊔ S.Tv ≤ S.HK K :=
    sup_le (hK₀K.trans (le_sup_left.trans le_sup_left)) (S.Tv_le_HK K)
  have hVW : conjClosure S.V1 (K₀ ⊔ S.Tv) ≤ S.WK K := by
    rw [S.WK_eq hT]
    exact conjClosure_mono le_rfl hHK
  have hzT : S.z ∈ S.Tv :=
    (Subgroup.closure_le _).mpr (fun x hx => hx.1.1) (S.V1_le_omega_Tv (Subgroup.mem_zpowers _))
  have hVH : conjClosure S.V1 (K₀ ⊔ S.Tv) ≤ K₀ ⊔ S.Tv := by
    refine conjClosure_le fun h hh x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (K₀ ⊔ S.Tv).mul_mem ((K₀ ⊔ S.Tv).mul_mem hh
      (Subgroup.mem_sup_right (S.Tv.zpow_mem hzT k))) ((K₀ ⊔ S.Tv).inv_mem hh)
  have hHV : K₀ ⊔ S.Tv ≤ Subgroup.normalizer
      ((conjClosure S.V1 (K₀ ⊔ S.Tv) : Subgroup G) : Set G) := le_normalizer_conjClosure _ _
  have hHK₀ : K₀ ⊔ S.Tv ≤ Subgroup.normalizer (K₀ : Set G) := sup_le Subgroup.le_normalizer hTK₀
  set V' := conjClosure S.V1 (K₀ ⊔ S.Tv) with hV'def
  have hV2 : ∀ x ∈ V', x ^ 2 = 1 := fun x hx => hR.2.2.1.2 x (hVW hx)
  have hz := S.not_le_centralizer_z_of_plus_eq h1222 h517 hF hK hT hK₀im
  have hzV : S.z ∈ V' := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have hK₀V : ¬ K₀ ≤ Subgroup.centralizer (V' : Set G) := fun h =>
    hz fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (h hk) _ hzV).symm
  have hQK : blockQ K₀ ≤ K₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀
  have hQn : K₀ ≤ Subgroup.normalizer (blockQ K₀ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀
  have hcK₀ : ∀ a ∈ V', ∀ k ∈ K₀, k⁻¹ * a * k * a⁻¹ ∈ K₀ ⊓ V' := by
    intro a ha k hk
    have haK : a * k * a⁻¹ ∈ K₀ :=
      (Subgroup.mem_normalizer_iff.mp (hHK₀ (hVH ha)) k).mp hk
    have hkV : k⁻¹ * a * k ∈ V' := by
      have := (Subgroup.mem_normalizer_iff.mp (hHV (Subgroup.mem_sup_left (K₀.inv_mem hk)))
        a).mp ha
      rwa [inv_inv] at this
    refine ⟨?_, V'.mul_mem hkV (V'.inv_mem ha)⟩
    have e : k⁻¹ * a * k * a⁻¹ = k⁻¹ * (a * k * a⁻¹) := by group
    rw [e]
    exact K₀.mul_mem (K₀.inv_mem hk) haK
  have hKVQ : K₀ ⊓ V' ≤ blockQ K₀ := by
    refine le_pCoreOf_of_normalizes inf_le_left (fun k hk => ?_) ?_
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, hHV (Subgroup.mem_sup_left hk)⟩
    · intro g
      exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hV2 _ g.2.2, Subgroup.coe_one])⟩
  have hcomm : ∀ a ∈ V', ∀ k ∈ K₀, k⁻¹ * a * k * a⁻¹ ∈ blockU K₀ := fun a ha =>
    comm_mem_commutator_of_perfect hQK hQn hK₀p (hHK₀ (hVH ha)) fun k hk => hKVQ (hcK₀ a ha k hk)
  set X : Subgroup G := ⁅K₀, V'⁆ with hXdef
  have hXU : X ≤ blockU K₀ := by
    rw [hXdef, Subgroup.commutator_le]
    intro k hk a ha
    have := hcomm a ha k⁻¹ (K₀.inv_mem hk)
    rwa [inv_inv, ← commutatorElement_def] at this
  have hXV : X ≤ V' := by
    rw [hXdef, Subgroup.commutator_le]
    intro k hk a ha
    have hkV : k * a * k⁻¹ ∈ V' :=
      (Subgroup.mem_normalizer_iff.mp (hHV (Subgroup.mem_sup_left hk)) a).mp ha
    rw [commutatorElement_def]
    exact V'.mul_mem hkV (V'.inv_mem ha)
  have hXK : X ≤ K₀ := hXU.trans ((Subgroup.commutator_mono hQK le_rfl).trans
    (A3.commutator_self_le K₀))
  have hXn : K₀ ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_commutator Subgroup.le_normalizer
      (fun k hk => hHV (Subgroup.mem_sup_left hk))
  obtain ⟨-, -, -, -, -, hirr⟩ := hshort
  have hUK : blockU K₀ ≤ K₀ :=
    (Subgroup.commutator_mono hQK le_rfl).trans (A3.commutator_self_le K₀)
  have hZK : blockZ K₀ ≤ K₀ := inf_le_left.trans hUK
  have hUn : K₀ ≤ Subgroup.normalizer (blockU K₀ : Set G) :=
    le_normalizer_commutator hQn Subgroup.le_normalizer
  have hZn : K₀ ≤ Subgroup.normalizer (blockZ K₀ : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hUn hk, mem_normalizer_centralizer_of_mem_normalizer (Subgroup.le_normalizer hk)⟩
  have hXZn : K₀ ≤ Subgroup.normalizer ((X ⊔ blockZ K₀ : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXn hk),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hZn hk)]
  rcases hirr (X ⊔ blockZ K₀) le_sup_right (sup_le hXU inf_le_left) hXZn with hXZ | hXZ
  · exfalso
    have hXZ' : X ≤ blockZ K₀ := hXZ ▸ le_sup_left
    apply hK₀V
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : ∀ k ∈ K₀, k⁻¹ * a * k * a⁻¹ ∈ blockZ K₀ := fun k hk => hXZ' (by
      have : ⁅k⁻¹, a⁆ ∈ X := Subgroup.commutator_mem_commutator (K₀.inv_mem hk) ha
      rwa [commutatorElement_def, inv_inv] at this)
    have h2 := comm_mem_commutator_of_perfect hZK hZn hK₀p (hHK₀ (hVH ha)) h1 k hk
    have hZc : ⁅blockZ K₀, K₀⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
    rw [hZc, Subgroup.mem_bot] at h2
    calc a * k = k * (k⁻¹ * a * k * a⁻¹) * a := by group
      _ = k * a := by rw [h2, mul_one]
  obtain ⟨α, hαs, hαk, β₀, hβs, hβk, hβe⟩ := h5
  obtain ⟨y, hy3, j, hαy⟩ := exists_pow_three_of_isAltType hαs hαk
  set σ : Equiv.Perm (Fin 5) := ((α y : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
    with hσdef
  have hc3 : orderOf c3p = 3 := orderOf_eq_prime c3p_cube (by decide)
  have hσ3 : σ ^ 3 = 1 := by rw [hαy, ← pow_mul, mul_comm, pow_mul, c3p_cube, one_pow]
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [hαy] at h
    have h3 : 3 ∣ 2 ^ j := hc3 ▸ orderOf_dvd_of_pow_eq_one h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hσ3' : σ 3 = 3 := by
    rw [hαy]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (by decide) _
  have hσ4 : σ 4 = 4 := by
    rw [hαy]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self c3p_four _
  obtain ⟨hfix34, hmov12⟩ := pact_e34_of_pow_three σ hσ3 hσ1 hσ3' hσ4
  have hβe' : ∀ (ℓ : ↥K₀) (u v : ↥(blockU K₀)), (v : G) = ℓ * u * ℓ⁻¹ →
      β₀ v = pact ((α ℓ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) (β₀ u) := by
    intro ℓ u v h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    exact hβe ℓ u v h i
  have hcXZ : ∀ a ∈ X, ∀ b ∈ blockZ K₀, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 a (hXK ha)
  have hpre : ∀ w : W5, ∃ x ∈ X, ∃ hxU : x ∈ blockU K₀, β₀ ⟨x, hxU⟩ = w := by
    intro w
    obtain ⟨u, rfl⟩ := hβs w
    have hu : (u : G) ∈ X ⊔ blockZ K₀ := by rw [hXZ]; exact u.2
    obtain ⟨x, hx, z, hz, hxz⟩ := S1417.exists_mul_of_mem_sup_of_commute hcXZ hu
    refine ⟨x, hx, hXU hx, ?_⟩
    have hzk : (⟨z, hz.1⟩ : ↥(blockU K₀)) ∈ β₀.ker := by
      rw [hβk]
      exact hz
    have e : u = ⟨x, hXU hx⟩ * ⟨z, hz.1⟩ := Subtype.ext hxz.symm
    rw [e, map_mul, hzk, mul_one]
  obtain ⟨x₁, hx₁X, hx₁U, hx₁⟩ := hpre (Multiplicative.ofAdd (A5Model.e2 3 4))
  obtain ⟨x₂, hx₂X, hx₂U, hx₂⟩ := hpre A5.E12
  have hyW : (y : G) ∈ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hK₀W y.2
  by_cases hyc : (y : G) ∈ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)
  ·
    have h1 : x₂ = (y : G) * x₂ * (y : G)⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.mp hyc x₂ (hVW (hXV hx₂X)), mul_inv_cancel_right]
    have h2 := hβe' y ⟨x₂, hx₂U⟩ ⟨x₂, hx₂U⟩ h1
    rw [hx₂] at h2
    exact hmov12 h2.symm
  ·
    set yp : MulAut ↥(S.WK K) := conjAct (S.WK K) ⟨(y : G), hyW⟩ with hypdef
    have hyN : yp ∈ S.plus K := hK₀im ▸ Setup.mem_autOn_iff.2 ⟨⟨(y : G), hyW⟩, y.2, rfl⟩
    have hπi : Function.Injective π := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StSL 2 K'), π γ = ⟨yp, hyN⟩ := hπ.1 _
    have hyp3 : yp ^ 3 = 1 := by
      have : (⟨(y : G), hyW⟩ : ↥(Subgroup.normalizer ((S.WK K : Subgroup G) : Set G))) ^ 3 = 1 :=
        Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          exact congrArg Subtype.val hy3)
      rw [hypdef, ← map_pow, this, map_one]
    have hγ3 : γ ^ 3 = 1 := by
      apply hπi
      rw [map_pow, hγ, map_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hyp3)
    have hγ1 : γ ≠ 1 := by
      intro h
      rw [h, map_one] at hγ
      apply hyc
      exact A4.conjAct_eq_one_iff.mp (congrArg Subtype.val hγ).symm
    obtain ⟨f, -, hfk, hfe⟩ := FFC.RealizesVia.secMap (D := FFModel.nat (StSL 2 K')) rfl hπ
    have hπγ : ∀ w : ↥(S.WK K), (((π γ : ↥(S.plus K)) : MulAut ↥(S.WK K)) w : G) =
        (y : G) * w * (y : G)⁻¹ := by
      intro w
      rw [hγ]
      exact InternalSec.coe_conjAct_apply _ w
    have hXUW : ∀ x (hx : x ∈ X), (⟨x, hVW (hXV hx)⟩ : ↥(S.WK K)) ∈ U := by
      have hle : X ≤ U.map (S.WK K).subtype := by
        rw [hXdef, Subgroup.commutator_le]
        intro k hk a ha
        have hkW := hK₀W hk
        have hkN : conjAct (S.WK K) ⟨k, hkW⟩ ∈ S.plus K :=
          hK₀im ▸ Setup.mem_autOn_iff.2 ⟨⟨k, hkW⟩, hk, rfl⟩
        refine ⟨_, hUV _ hkN ⟨a, hVW ha⟩, ?_⟩
        rw [Subgroup.subtype_apply, Subgroup.coe_mul, InternalSec.coe_conjAct_apply,
          Subgroup.coe_inv, commutatorElement_def]
      intro x hx
      obtain ⟨w, hwU, hw⟩ := hle hx
      have : w = ⟨x, hVW (hXV hx)⟩ := Subtype.ext hw
      rw [← this]
      exact hwU
    have hfix : ∀ (w : ↥(S.WK K)) (hw : w ∈ U),
        (((π γ : ↥(S.plus K)) : MulAut ↥(S.WK K)) w) = w → f ⟨w, hw⟩ = 1 := by
      intro w hw h
      have hu : ((π γ : ↥(S.plus K)) : MulAut ↥(S.WK K)) w ∈ U := by rw [h]; exact hw
      have h1 := hfe γ ⟨w, hw⟩ hu
      have e : (⟨((π γ : ↥(S.plus K)) : MulAut ↥(S.WK K)) w, hu⟩ : ↥U) = ⟨w, hw⟩ :=
        Subtype.ext h
      have h3 := congrArg
        (fun u : ↥U => ((f u : ↥(FFModel.nat (StSL 2 K')).sec) : (FFModel.nat (StSL 2 K')).Amb)) e
      exact Subtype.ext (eq_one_of_natAct_eq hγ3 hγ1 (h3.symm.trans h1).symm)
    set xW : ↥(S.WK K) := ⟨x₁, hVW (hXV hx₁X)⟩ with hxWdef
    have hxWU : xW ∈ U := hXUW x₁ hx₁X
    have hyxU : (y : G) * x₁ * (y : G)⁻¹ ∈ blockU K₀ :=
      (Subgroup.mem_normalizer_iff.mp (hUn y.2) x₁).mp hx₁U
    have hc : (y : G) * x₁ * (y : G)⁻¹ * x₁⁻¹ ∈ blockZ K₀ := by
      have h1 := hβe' y ⟨x₁, hx₁U⟩ ⟨_, hyxU⟩ rfl
      rw [hx₁, hfix34] at h1
      have h2 : (⟨_, (blockU K₀).mul_mem hyxU ((blockU K₀).inv_mem hx₁U)⟩ : ↥(blockU K₀)) ∈
          β₀.ker := by
        rw [MonoidHom.mem_ker]
        have e : (⟨_, (blockU K₀).mul_mem hyxU ((blockU K₀).inv_mem hx₁U)⟩ : ↥(blockU K₀)) =
            ⟨_, hyxU⟩ * (⟨x₁, hx₁U⟩)⁻¹ := rfl
        rw [e, map_mul, map_inv, h1, hx₁, mul_inv_cancel]
      rw [hβk] at h2
      exact h2
    have hcV : (y : G) * x₁ * (y : G)⁻¹ * x₁⁻¹ ∈ S.WK K :=
      (S.WK K).mul_mem ((Subgroup.mem_normalizer_iff.mp hyW x₁).mp (hVW (hXV hx₁X)))
        ((S.WK K).inv_mem (hVW (hXV hx₁X)))
    set cW : ↥(S.WK K) := ⟨_, hcV⟩ with hcWdef
    have hcWe : cW = yp xW * xW⁻¹ := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hypdef, InternalSec.coe_conjAct_apply])
    have hcWU : cW ∈ U := hcWe ▸ hUV yp hyN xW
    have hcfix : (((π γ : ↥(S.plus K)) : MulAut ↥(S.WK K)) cW) = cW := by
      apply Subtype.ext
      rw [hπγ]
      show (y : G) * ((y : G) * x₁ * (y : G)⁻¹ * x₁⁻¹) * (y : G)⁻¹ =
        (y : G) * x₁ * (y : G)⁻¹ * x₁⁻¹
      rw [Subgroup.mem_centralizer_iff.mp hc.2 (y : G) y.2, mul_inv_cancel_right]
    have hfc := hfix cW hcWU hcfix
    have hpy : ((π γ : ↥(S.plus K)) : MulAut ↥(S.WK K)) = yp := by rw [hγ]
    have hyx : (((π γ : ↥(S.plus K)) : MulAut ↥(S.WK K)) xW) = xW * cW := by
      rw [hcWe, hpy, mul_comm (yp xW) xW⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
    have hfx : f ⟨xW, hxWU⟩ = 1 := by
      have hu : ((π γ : ↥(S.plus K)) : MulAut ↥(S.WK K)) xW ∈ U := by
        rw [hyx]
        exact U.mul_mem hxWU hcWU
      have h1 := hfe γ ⟨xW, hxWU⟩ hu
      have e : (⟨((π γ : ↥(S.plus K)) : MulAut ↥(S.WK K)) xW, hu⟩ : ↥U) =
          ⟨xW, hxWU⟩ * ⟨cW, hcWU⟩ := Subtype.ext hyx
      have h3 := congrArg
        (fun u : ↥U => ((f u : ↥(FFModel.nat (StSL 2 K')).sec) : (FFModel.nat (StSL 2 K')).Amb)) e
      rw [map_mul, hfc, mul_one] at h3
      exact Subtype.ext (eq_one_of_natAct_eq hγ3 hγ1 (h3.symm.trans h1).symm)
    have hxC : xW ∈ C := (hfk ⟨xW, hxWU⟩).mp hfx
    have hxZ : x₁ ∈ blockZ K₀ := by
      refine ⟨hx₁U, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      have hkW := hK₀W hk
      have hkN : conjAct (S.WK K) ⟨k, hkW⟩ ∈ S.plus K :=
        hK₀im ▸ Setup.mem_autOn_iff.2 ⟨⟨k, hkW⟩, hk, rfl⟩
      have h1 := congrArg Subtype.val (hCfix _ hkN xW hxC)
      rw [InternalSec.coe_conjAct_apply] at h1
      calc k * x₁ = k * x₁ * k⁻¹ * k := by group
        _ = x₁ * k := by rw [h1]
    have h0 : β₀ ⟨x₁, hx₁U⟩ = 1 := by
      have : (⟨x₁, hx₁U⟩ : ↥(blockU K₀)) ∈ β₀.ker := by rw [hβk]; exact hxZ
      exact this
    rw [hx₁] at h0
    exact absurd h0 (by decide +kernel)

end Setting

end CFSG.Quasithin.H13.A5
