module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zv
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zl
public import CFSG.Walter.Cited.HuppertBasic
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2

public section

namespace CFSG.Quasithin.H13.S127.Mod

theorem i1_inv_zs6 : ∀ z ∈ zs6, i1.comp z = (z.comp z).comp i1 := by decide

theorem r1_noncentral : ∀ r ∈ r1, r ≠ B6.id → ∃ g ∈ l1, g.comp r ≠ r.comp g := by decide

theorem w6_mem_zs6 : w6 ∈ zs6 := by decide

theorem w6_sq_mem_zs6 : w6.comp w6 ∈ zs6 := by decide

end CFSG.Quasithin.H13.S127.Mod

namespace CFSG.Quasithin.H13.S127.D1

variable {W : Type*} [CommGroup W]

theorem eq_one_of_mem_range_of_fix (hW : ∀ w : W, w ^ 2 = 1) {τ : MulAut W} (hτ3 : τ ^ 3 = 1)
    {s : W} (hs : s ∈ (NoTransv.commHom τ).range) (hfix : τ s = s) : s = 1 := by
  obtain ⟨x, rfl⟩ := hs
  have hts : ∀ w, τ (NoTransv.commHom τ w) = NoTransv.commHom τ (τ w) := fun w => by
    rw [NoTransv.commHom_apply, NoTransv.commHom_apply, map_mul, map_inv]
  have h3 : τ (τ (τ x)) = x := by
    have : (τ ^ 3) x = x := by rw [hτ3]; rfl
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply] using this
  have key : NoTransv.commHom τ x * NoTransv.commHom τ (τ x) *
      NoTransv.commHom τ (τ (τ x)) = 1 := by
    rw [NoTransv.commHom_apply, NoTransv.commHom_apply, NoTransv.commHom_apply, h3]
    group
  have e1 : NoTransv.commHom τ (τ x) = NoTransv.commHom τ x := by rw [← hts, hfix]
  have e2 : NoTransv.commHom τ (τ (τ x)) = NoTransv.commHom τ x := by rw [← hts, e1, hfix]
  rw [e1, e2] at key
  set c := NoTransv.commHom τ x with hc
  have hx2 := hW c
  calc c = c * c * c * (c ^ 2)⁻¹ := by group
    _ = 1 := by rw [key, hx2, inv_one, mul_one]

theorem mem_range_of_comm {τ ρ : MulAut W} (hρτ : ρ * τ = τ * ρ) {w : W}
    (hw : w ∈ (NoTransv.commHom τ).range) : ρ w ∈ (NoTransv.commHom τ).range := by
  obtain ⟨x, rfl⟩ := hw
  refine ⟨ρ x, ?_⟩
  rw [NoTransv.commHom_apply, NoTransv.commHom_apply, map_mul, map_inv]
  congr 1
  rw [← MulAut.mul_apply, ← hρτ, MulAut.mul_apply]

theorem apply_eq_of_inv (hW : ∀ w : W, w ^ 2 = 1) {τ ρ μ : MulAut W} (hτ3 : τ ^ 3 = 1)
    (hρτ : ρ * τ = τ * ρ) (hμτ : μ * τ * μ⁻¹ = τ⁻¹)
    (hq : ∀ w, μ (NoTransv.commHom ρ w) = NoTransv.commHom ρ w) {w : W}
    (hw : w ∈ (NoTransv.commHom τ).range) : ρ w = w := by
  set s := NoTransv.commHom ρ w with hs
  have hsR : s ∈ (NoTransv.commHom τ).range := by
    rw [hs, NoTransv.commHom_apply]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) (mem_range_of_comm hρτ hw)
  have hτs : τ s = NoTransv.commHom ρ (τ w) := by
    rw [hs, NoTransv.commHom_apply, NoTransv.commHom_apply, map_mul, map_inv]
    congr 1
    rw [← MulAut.mul_apply, ← hρτ, MulAut.mul_apply]
  have h1 : μ (τ s) = τ s := by rw [hτs]; exact hq _
  have h2 : μ (τ s) = τ⁻¹ s := by
    have e : μ * τ = τ⁻¹ * μ := by
      rw [← hμτ]
      group
    calc μ (τ s) = (μ * τ) s := rfl
      _ = (τ⁻¹ * μ) s := by rw [e]
      _ = τ⁻¹ (μ s) := rfl
      _ = τ⁻¹ s := by rw [hs, hq w]
  have h3 : τ s = s := by
    have h4 : τ (τ s) = s := by
      have := congrArg τ (h1.symm.trans h2)
      rw [MulAut.apply_inv_self] at this
      exact this
    have h5 : (τ ^ 3) s = s := by rw [hτ3]; rfl
    have e : (τ ^ 3) s = τ (τ (τ s)) := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
    rw [e, h4] at h5
    exact h5
  have hs1 := eq_one_of_mem_range_of_fix hW hτ3 hsR h3
  rw [hs, NoTransv.commHom_apply] at hs1
  exact (inv_mul_eq_one.mp hs1).symm

end CFSG.Quasithin.H13.S127.D1

namespace CFSG.Quasithin.H13.S127.D1

variable {G : Type} [Group G] [Finite G]

abbrev Qbar (Q V : Subgroup G) : Type := ↥Q ⧸ V.subgroupOf Q

abbrev Wq (Q V : Subgroup G) [(V.subgroupOf Q).Normal] : Type :=
  Qbar Q V ⧸ frattini (Qbar Q V)

noncomputable def piW (Q V : Subgroup G) [(V.subgroupOf Q).Normal] : ↥Q →* Wq Q V :=
  (QuotientGroup.mk' (frattini (Qbar Q V))).comp (QuotientGroup.mk' (V.subgroupOf Q))

noncomputable def psiW (Q V K : Subgroup G) [(V.subgroupOf Q).Normal]
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    ↥K →* MulAut (Wq Q V) :=
  (CFSG.Walter.Huppert.frattiniAut (Qbar Q V)).comp (NoTransv.quotConj Q V K hKQ hKV)

variable {Q V K : Subgroup G} [(V.subgroupOf Q).Normal]
  {hKQ : K ≤ Subgroup.normalizer (Q : Set G)} {hKV : K ≤ Subgroup.normalizer (V : Set G)}

omit [Finite G] in
theorem piW_surjective : Function.Surjective (piW Q V) := by
  intro w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ w
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective _ x
  exact ⟨p, rfl⟩

omit [Finite G] in
theorem piW_eq_one {p : ↥Q} (hp : (p : G) ∈ V) : piW Q V p = 1 := by
  have h1 : QuotientGroup.mk' (V.subgroupOf Q) p = 1 :=
    (QuotientGroup.eq_one_iff p).mpr (Subgroup.mem_subgroupOf.mpr hp)
  show QuotientGroup.mk' _ (QuotientGroup.mk' (V.subgroupOf Q) p) = 1
  rw [h1, map_one]

omit [Finite G] in
theorem piW_eq_of_inv_mul_mem {p₁ p₂ : ↥Q} (h : (p₁ : G)⁻¹ * p₂ ∈ V) :
    piW Q V p₁ = piW Q V p₂ := by
  have h1 : piW Q V (p₁⁻¹ * p₂) = 1 := piW_eq_one (by simpa using h)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem psiW_piW (k : ↥K) (p : ↥Q) :
    psiW Q V K hKQ hKV k (piW Q V p) =
      piW Q V ⟨k * p * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hKQ k.2) p).mp p.2⟩ := by
  show CFSG.Walter.Huppert.frattiniAut (Qbar Q V) (NoTransv.quotConj Q V K hKQ hKV k)
    (QuotientGroup.mk' _ (QuotientGroup.mk' (V.subgroupOf Q) p)) = _
  rw [QuotientGroup.mk'_apply, CFSG.Walter.Huppert.frattiniAut_mk, NoTransv.quotConj_mk]
  show (QuotientGroup.mk' (V.subgroupOf Q) (Q.normalizerMonoidHom ⟨k, hKQ k.2⟩ p) :
    Qbar Q V ⧸ frattini (Qbar Q V)) = _
  congr 2

theorem isElementaryAbelian_Wq (hQ2 : IsPGroup 2 ↥Q) :
    IsElementaryAbelian 2 (Wq Q V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 (Qbar Q V)) := ⟨hQ2.to_quotient _⟩
  exact CFSG.isElementaryAbelian_quotient_frattini

theorem sq_Wq (hQ2 : IsPGroup 2 ↥Q) (w : Wq Q V) : w ^ 2 = 1 := by
  have h := (isElementaryAbelian_Wq (V := V) hQ2).exponent_dvd_p
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h w

theorem comm_Wq (hQ2 : IsPGroup 2 ↥Q) (a b : Wq Q V) : a * b = b * a :=
  ((isElementaryAbelian_Wq (V := V) hQ2).toIsMulCommutative).is_comm.comm a b

theorem psiW_eq_one_of_mem (hQ2 : IsPGroup 2 ↥Q) {k : ↥K} (hk : (k : G) ∈ Q) :
    psiW Q V K hKQ hKV k = 1 := by
  refine MulEquiv.ext fun w => ?_
  obtain ⟨p, rfl⟩ := piW_surjective w
  rw [psiW_piW, MulAut.one_apply]
  have e : (⟨k * p * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hKQ k.2) p).mp p.2⟩ : ↥Q) =
      ⟨k, hk⟩ * p * ⟨k, hk⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, comm_Wq hQ2 (piW Q V ⟨k, hk⟩), mul_inv_cancel_right]

theorem psiW_eq_of_mem (hQ2 : IsPGroup 2 ↥Q) {k k' : ↥K} (hk : ((k⁻¹ * k' : ↥K) : G) ∈ Q) :
    psiW Q V K hKQ hKV k = psiW Q V K hKQ hKV k' := by
  have h1 := psiW_eq_one_of_mem (hKQ := hKQ) (hKV := hKV) hQ2 hk
  rw [map_mul, map_inv] at h1
  exact (inv_mul_eq_one.mp h1)

end CFSG.Quasithin.H13.S127.D1

namespace CFSG.Quasithin.H13.S127.Mod

theorem i1_mem_s0p : i1 ∈ s0p := by decide

theorem exists_r1_ne : ∃ r ∈ r1, r ≠ B6.id := by decide

theorem w6_pow3 : (w6.pow 3) = B6.id := by decide

theorem w6_sq_ne_id : w6.comp w6 ≠ B6.id := by decide

end CFSG.Quasithin.H13.S127.Mod

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127 S127.Mod S127.D1
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

theorem comm_y_mem_V
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V}
    (hC : Std C T L) (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V)
    (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8)
    {y : G} (hyL : y ∈ L) (hyN : y ∈ Subgroup.normalizer (V : Set G)) (hy3 : y ^ 3 = 1)
    (hyz : C.cB (conjAct V ⟨y, hyN⟩) ∈ zs6) :
    ∀ q ∈ pCoreOf 2 (L ⊔ T), y * q * y⁻¹ * q⁻¹ ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.setting.hyp
  have hy := h.hyp
  obtain ⟨-, -, hTV⟩ := S127.card_eq_of_1222 h1222 h
  obtain ⟨hOn, hq, -, -⟩ := h.hatA6
  obtain ⟨-, -, hLC, -, -, -⟩ := setup1271_of h1222 G T L V h
  have hT2 : IsPGroup 2 T := hy.sylow.1
  have hVT : V ≤ T := S127.L713.V_le_T h1222 h
  have hV2 : IsPGroup 2 V := hT2.to_le hVT
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := S127.Mod.L_le_normalizer h
  have hUT := s.U_le_T h1222
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hsylLT : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    S127.L713.isSylowTwoOf_of_le hy.sylow le_sup_right
  have hQT : Q ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsylLT
  have hVQ : V ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hVT.trans le_sup_right) (sup_le hLV hTV) hV2
  have hQC : Q ≤ Subgroup.centralizer (V : Set G) := S127.Mod.Q_le_centralizer h1222 h
  have hKQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hKV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hinfQ : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ Q :=
    S127.inf_centralizer_le_Q h1222 h
  have hVn : (V.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVQ).mpr
      (hQC.trans (Subgroup.centralizer_le_normalizer _))
  let _ : CommGroup (Wq Q V) :=
    { (inferInstance : Group (Wq Q V)) with mul_comm := comm_Wq hQ2 }
  have hW2 : ∀ w : Wq Q V, w ^ 2 = 1 := sq_Wq hQ2
  set ψ := psiW Q V (L ⊔ T) hKQ hKV with hψ
  have hψeq : ∀ k k' : ↥(L ⊔ T), (∀ hk : (k : G) ∈ Subgroup.normalizer (V : Set G),
      ∀ hk' : (k' : G) ∈ Subgroup.normalizer (V : Set G),
        conjAct V ⟨k, hk⟩ = conjAct V ⟨k', hk'⟩) → ψ k = ψ k' := by
    intro k k' hkk
    refine psiW_eq_of_mem hQ2 (hinfQ ⟨(k⁻¹ * k').2, ?_⟩)
    show ((k : G))⁻¹ * k' ∈ Subgroup.centralizer (V : Set G)
    have hkN := hKV k.2
    have hk'N := hKV k'.2
    have h1 := hkk hkN hk'N
    rw [← conjAct_eq_one' (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) hk'N)]
    have e : (⟨(k : G)⁻¹ * k', Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) hk'N⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = ⟨k, hkN⟩⁻¹ * ⟨k', hk'N⟩ := rfl
    rw [e, map_mul, map_inv, h1, inv_mul_cancel]
  set yK : ↥(L ⊔ T) := ⟨y, Subgroup.mem_sup_left hyL⟩ with hyK
  obtain ⟨a₁, -, ha₁⟩ := T_surj h1222 h hC hne hT i1 i1_mem_s0p
  have ha₁U : a₁ ∈ autOn (U714 T L V z) V := (hbig a₁).2 (ha₁ ▸ i1_mem_e8)
  obtain ⟨u₁, hu₁N, hu₁U, rfl⟩ := mem_autOn'.1 ha₁U
  set uK : ↥(L ⊔ T) := ⟨u₁, Subgroup.mem_sup_right (hUT.1 hu₁U)⟩ with huK
  obtain ⟨r₀, hr₀, hr₀1⟩ := exists_r1_ne
  obtain ⟨ρ', hρ'R, hρ'c⟩ := s.exists_R1_code h1222 hC hr₀
  have hρ'U : ρ' ∈ autOn (U714 T L V z) V := (hbig ρ').2 (hρ'c ▸ mem_e8_of_r1 hr₀)
  obtain ⟨r, hrN, hrU, rfl⟩ := mem_autOn'.1 hρ'U
  set rK : ↥(L ⊔ T) := ⟨r, Subgroup.mem_sup_right (hUT.1 hrU)⟩ with hrK
  set τ := ψ yK with hτ
  set ρ := ψ rK with hρ
  set μ := ψ uK with hμ
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← map_pow]
    have : yK ^ 3 = 1 := Subtype.ext (by simpa [hyK] using hy3)
    rw [this, map_one]
  have hry : conjAct V ⟨r, hrN⟩ * conjAct V ⟨y, hyN⟩ =
      conjAct V ⟨y, hyN⟩ * conjAct V ⟨r, hrN⟩ := by
    apply C.cB_injective
    rw [C.cB_mul, C.cB_mul, hρ'c]
    exact (zs6_comm _ hyz _ (r1_sub r₀ hr₀).1).symm
  have hρτ : ρ * τ = τ * ρ := by
    rw [hρ, hτ, ← map_mul, ← map_mul]
    refine hψeq _ _ fun hk hk' => ?_
    have e1 : (⟨((rK * yK : ↥(L ⊔ T)) : G), hk⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨r, hrN⟩ * ⟨y, hyN⟩ := rfl
    have e2 : (⟨((yK * rK : ↥(L ⊔ T)) : G), hk'⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨y, hyN⟩ * ⟨r, hrN⟩ := rfl
    rw [e1, e2, map_mul, map_mul, hry]
  have hui : conjAct V ⟨u₁, hu₁N⟩ * conjAct V ⟨y, hyN⟩ =
      conjAct V ⟨y, hyN⟩ * conjAct V ⟨y, hyN⟩ * conjAct V ⟨u₁, hu₁N⟩ := by
    apply C.cB_injective
    rw [C.cB_mul, C.cB_mul, C.cB_mul, ha₁]
    exact i1_inv_zs6 _ hyz
  have hμτ : μ * τ * μ⁻¹ = τ⁻¹ := by
    have h1 : μ * τ = τ * τ * μ := by
      rw [hμ, hτ, ← map_mul, ← map_mul, ← map_mul]
      refine hψeq _ _ fun hk hk' => ?_
      have e1 : (⟨((uK * yK : ↥(L ⊔ T)) : G), hk⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨u₁, hu₁N⟩ * ⟨y, hyN⟩ := rfl
      have e2 : (⟨((yK * yK * uK : ↥(L ⊔ T)) : G), hk'⟩ :
          ↥(Subgroup.normalizer (V : Set G))) = ⟨y, hyN⟩ * ⟨y, hyN⟩ * ⟨u₁, hu₁N⟩ := rfl
      rw [e1, e2, map_mul, map_mul, map_mul, hui]
    have h3 : τ * τ = τ⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv, ← pow_two, ← pow_succ, hτ3]
    rw [h1, h3, mul_inv_cancel_right]
  have hq' : ∀ w, μ (NoTransv.commHom ρ w) = NoTransv.commHom ρ w := by
    intro w
    obtain ⟨p, rfl⟩ := piW_surjective w
    have hpT : (p : G) ∈ T := hQT p.2
    have hrpQ : r * p * r⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hKQ rK.2) p).mp p.2
    have hxQ : (p : G)⁻¹ * (r * p * r⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem p.2) hrpQ
    have hxU : (p : G)⁻¹ * (r * p * r⁻¹) ∈ U714 T L V z := by
      have hpr : (p : G)⁻¹ * r * p ∈ U714 T L V z := by
        have := (Subgroup.mem_normalizer_iff.mp (hUT.2 (T.inv_mem hpT)) r).mp hrU
        simpa using this
      have e : (p : G)⁻¹ * (r * p * r⁻¹) = ((p : G)⁻¹ * r * p) * r⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hpr (Subgroup.inv_mem _ hrU)
    have hc : NoTransv.commHom ρ (piW Q V p) = piW Q V ⟨_, hxQ⟩ := by
      rw [NoTransv.commHom_apply, hρ, psiW_piW, ← map_inv, ← map_mul]
      rfl
    rw [hc, hμ, psiW_piW]
    set x : G := (p : G)⁻¹ * (r * p * r⁻¹) with hx
    have hcz : x⁻¹ * (u₁ * x * u₁⁻¹) ∈ V := by
      have h1 := s.comm_mem_U h1222 (U714 T L V z |>.inv_mem hxU) hu₁U
      have e : x⁻¹ * (u₁ * x * u₁⁻¹) = (x⁻¹ * u₁ * x⁻¹⁻¹ * u₁⁻¹) := by group
      rw [e]
      exact (Subgroup.zpowers_le_of_mem s.z_mem_V) h1
    apply piW_eq_of_inv_mul_mem
    show (u₁ * x * u₁⁻¹)⁻¹ * x ∈ V
    have e : (u₁ * x * u₁⁻¹)⁻¹ * x = (x⁻¹ * (u₁ * x * u₁⁻¹))⁻¹ := by group
    rw [e]
    exact V.inv_mem hcz
  have hW' : ∀ w ∈ (NoTransv.commHom τ).range, ρ w = w := fun w hw =>
    D1.apply_eq_of_inv hW2 hτ3 hρτ hμτ hq' hw
  set W' := (NoTransv.commHom τ).range with hW'def
  set φL : ↥L →* MulAut (Wq Q V) := ψ.comp (Subgroup.inclusion le_sup_left) with hφL
  have hφLτ : ∀ g : ↥L, φL g * τ = τ * φL g := by
    intro g
    rw [hφL, hτ, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    refine hψeq _ _ fun hk hk' => ?_
    have hgN := hLV g.2
    have e1 : (⟨((Subgroup.inclusion le_sup_left g * yK : ↥(L ⊔ T)) : G), hk⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = ⟨g, hgN⟩ * ⟨y, hyN⟩ := rfl
    have e2 : (⟨((yK * Subgroup.inclusion le_sup_left g : ↥(L ⊔ T)) : G), hk'⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = ⟨y, hyN⟩ * ⟨g, hgN⟩ := rfl
    rw [e1, e2, map_mul, map_mul]
    apply C.cB_injective
    rw [C.cB_mul, C.cB_mul]
    exact (zs6_comm _ hyz _ ((hC.1.1 _).1 (conjAct_mem_autOn g.2 hgN))).symm
  have hW'inv : ∀ g : ↥L, ∀ w ∈ W', φL g w ∈ W' := fun g w hw =>
    D1.mem_range_of_comm (hφLτ g) hw
  set N : Subgroup ↥L := (fixingSubgroup (MulAut (Wq Q V)) (W' : Set (Wq Q V))).comap φL with hN
  have hmemN : ∀ g : ↥L, g ∈ N ↔ ∀ w ∈ W', φL g w = w := fun g => by
    rw [hN, Subgroup.mem_comap, mem_fixingSubgroup_iff]
    rfl
  have hNn : N.Normal := by
    refine ⟨fun n hn g => (hmemN _).2 fun w hw => ?_⟩
    have hn' := (hmemN n).1 hn
    have hw' : φL g⁻¹ w ∈ W' := hW'inv g⁻¹ w hw
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hn' _ hw', ← MulAut.mul_apply,
      ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  obtain ⟨ℓ, hℓN, hℓL, hℓe⟩ := mem_autOn'.1 ((hC.1.1 (conjAct V ⟨r, hrN⟩)).2
    (hρ'c ▸ (r1_sub r₀ hr₀).1))
  have hℓρ : φL ⟨ℓ, hℓL⟩ = ρ := by
    rw [hφL, MonoidHom.comp_apply, hρ]
    exact hψeq _ _ fun hk hk' => hℓe
  have hℓmem : (⟨ℓ, hℓL⟩ : ↥L) ∈ N := (hmemN _).2 fun w hw => by rw [hℓρ]; exact hW' w hw
  have hℓc : QuotientGroup.mk' ((Subgroup.centralizer (V : Set G)).subgroupOf L) ⟨ℓ, hℓL⟩ ∉
      Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) := by
    intro hc
    obtain ⟨g, hg, hgr⟩ := r1_noncentral r₀ hr₀ hr₀1
    obtain ⟨b, hb⟩ := hC.1.2 g (l1_sub_gm6 g hg)
    obtain ⟨g', hg'N, hg'L, rfl⟩ := mem_autOn'.1 ((hC.1.1 b).2 (hb ▸ l1_sub_gm6 g hg))
    have h1 := Subgroup.mem_center_iff.mp hc (QuotientGroup.mk' _ ⟨g', hg'L⟩)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have hm : (g' * ℓ)⁻¹ * (ℓ * g') ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hg'N hℓN))
        (Subgroup.mul_mem _ hℓN hg'N)
    have h2 := (conjAct_eq_one' hm).2 h1
    have e : (⟨(g' * ℓ)⁻¹ * (ℓ * g'), hm⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        (⟨g', hg'N⟩ * ⟨ℓ, hℓN⟩)⁻¹ * (⟨ℓ, hℓN⟩ * ⟨g', hg'N⟩) := rfl
    rw [e, map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at h2
    have h3 := congrArg C.cB h2
    rw [C.cB_mul, C.cB_mul, hℓe, hρ'c, hb] at h3
    exact hgr h3
  have hO2 : IsPGroup 2 ↥((Subgroup.centralizer (V : Set G)).subgroupOf L) := by
    rintro ⟨x, hx⟩
    have hxP : (x : G) ∈ pCoreOf 2 L := by rw [← hLC]; exact ⟨x.2, hx⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hxP⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have htop := NoTransv.eq_top_of_not_mem_center hO2 hq (no2_of_hyp hy) hℓmem hℓc
  have hφy : φL ⟨y, hyL⟩ = τ := by
    rw [hφL, MonoidHom.comp_apply, hτ]
    rfl
  have hyW' : ∀ w ∈ W', τ w = w := by
    have hyN' : (⟨y, hyL⟩ : ↥L) ∈ N := by rw [htop]; exact Subgroup.mem_top _
    intro w hw
    rw [← hφy]
    exact (hmemN _).1 hyN' w hw
  have hτ1 : τ = 1 := by
    refine MulEquiv.ext fun w => ?_
    have hc : NoTransv.commHom τ w ∈ W' := ⟨w, rfl⟩
    have h1 := D1.eq_one_of_mem_range_of_fix hW2 hτ3 hc (hyW' _ hc)
    rw [NoTransv.commHom_apply, inv_mul_eq_one] at h1
    exact h1.symm
  set σ := NoTransv.quotConj Q V (L ⊔ T) hKQ hKV yK with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : yK ^ 3 = 1 := Subtype.ext (by simpa [hyK] using hy3)
    rw [this, map_one]
  have hcop : Nat.Coprime 2 (orderOf σ) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hσ3) (by norm_num)
  have hσ1 : σ = 1 := CFSG.Walter.Huppert.eq_one_of_frattiniAut_eq_one (hQ2.to_quotient _) hcop
    (by rw [← hτ1]; rfl)
  intro q hq
  have h1 : σ (QuotientGroup.mk' _ ⟨q, hq⟩) = QuotientGroup.mk' _ ⟨q, hq⟩ := by
    rw [hσ1, MulAut.one_apply]
  rw [hσ, NoTransv.quotConj_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  have hyq : (y * q * y⁻¹)⁻¹ * q ∈ V := by
    have e := NoTransv.normalizerMonoidHom_coe Q ⟨y, hKQ yK.2⟩ ⟨q, hq⟩
    simp only [Subgroup.coe_inv, Subgroup.coe_mul] at h1
    rw [e] at h1
    exact h1
  have hqc := Subgroup.mem_centralizer_iff.mp (hQC hq) _ (V.inv_mem hyq)
  have e2 : y * q * y⁻¹ * q⁻¹ = q * ((y * q * y⁻¹)⁻¹ * q)⁻¹ * q⁻¹ := by group
  rw [e2, ← hqc, mul_inv_cancel_right]
  exact V.inv_mem hyq

end CFSG.Quasithin.H13.S127.L715.Set714
