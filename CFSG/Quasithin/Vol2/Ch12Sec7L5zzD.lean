module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zzC
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zw
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318T
public import CFSG.Quasithin.Background.SmithB45AltBase

public section

namespace CFSG.Quasithin.H13.S127

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S127.Mod
open scoped IsMulCommutative

variable {G : Type} [Group G]

structure Theta4a (T L V : Subgroup G) [IsMulCommutative ↥V] (C : Coding ↥V) where
  Θ : ℕ → G
  zero : Θ 0 = 1
  xor : ∀ m m', Θ (m ^^^ m') = Θ m * Θ m'
  inj : ∀ m < 16, Θ m = 1 → m = 0
  mem : ∀ m, Θ m ∈ WZ T L
  equiv : ∀ g, g ∈ L ⊔ T → ∀ (hgN : g ∈ Subgroup.normalizer (V : Set G)) (m : ℕ),
    g * Θ m * g⁻¹ = Θ (act4 (permFn (C.cB (conjAct V ⟨g, hgN⟩))) m)
  comm : ∀ m, ∀ v ∈ V, Θ m * v = v * Θ m

namespace Theta4a

variable {T L V : Subgroup G} [IsMulCommutative ↥V] {C : Coding ↥V} (d : Theta4a T L V C)

theorem sq (m : ℕ) : d.Θ m * d.Θ m = 1 := by
  rw [← d.xor, Nat.xor_self, d.zero]

theorem inv_eq (m : ℕ) : (d.Θ m)⁻¹ = d.Θ m := inv_eq_of_mul_eq_one_right (d.sq m)

@[expose] def V0 : Subgroup G where
  carrier := {x | ∃ v ∈ V, ∃ m < 16, x = v * d.Θ m}
  mul_mem' := by
    rintro _ _ ⟨v, hv, m, hm, rfl⟩ ⟨v', hv', m', hm', rfl⟩
    refine ⟨v * v', V.mul_mem hv hv', m ^^^ m', Nat.xor_lt_two_pow (n := 4) hm hm', ?_⟩
    rw [d.xor, mul_assoc, ← mul_assoc (d.Θ m), d.comm m v' hv']
    group
  one_mem' := ⟨1, V.one_mem, 0, by norm_num, by rw [d.zero, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨v, hv, m, hm, rfl⟩
    refine ⟨v⁻¹, V.inv_mem hv, m, hm, ?_⟩
    rw [mul_inv_rev, d.inv_eq, d.comm m _ (V.inv_mem hv)]

theorem le_V0 : V ≤ d.V0 := fun v hv => ⟨v, hv, 0, by norm_num, by rw [d.zero, mul_one]⟩

theorem mul_mem_V0 {v : G} (hv : v ∈ V) {m : ℕ} (hm : m < 16) : v * d.Θ m ∈ d.V0 :=
  ⟨v, hv, m, hm, rfl⟩

theorem eq_of_mul_eq (hVW : ∀ w ∈ WZ T L, w ∈ V → w = 1) {v v' : G} (hv : v ∈ V)
    (hv' : v' ∈ V) {m m' : ℕ} (hm : m < 16) (hm' : m' < 16) (h : v * d.Θ m = v' * d.Θ m') :
    v = v' ∧ m = m' := by
  have e : v'⁻¹ * v = d.Θ (m' ^^^ m) := by
    rw [d.xor, ← d.inv_eq m]
    calc v'⁻¹ * v = v'⁻¹ * (v * d.Θ m) * (d.Θ m)⁻¹ := by group
      _ = d.Θ m' * (d.Θ m)⁻¹ := by rw [h]; group
  have h1 := hVW _ (d.mem _) (e ▸ V.mul_mem (V.inv_mem hv') hv)
  have h2 : m' ^^^ m = 0 := d.inj _ (Nat.xor_lt_two_pow (n := 4) hm' hm) h1
  have hmm : m = m' := by
    calc m = (m' ^^^ m') ^^^ m := by rw [Nat.xor_self, Nat.zero_xor]
      _ = m' ^^^ (m' ^^^ m) := Nat.xor_assoc _ _ _
      _ = m' := by rw [h2, Nat.xor_zero]
  refine ⟨?_, hmm⟩
  rw [h1] at e
  exact (inv_mul_eq_one.mp e).symm

end Theta4a

end CFSG.Quasithin.H13.S127

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open S127 S127.Mod
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

theorem V_le_Q
    (h1222 : Stmt12_2_2) : V ≤ pCoreOf 2 (L ⊔ T) := by
  have h := s.setting.hyp
  have hVT : V ≤ T := S127.L713.V_le_T h1222 h
  exact le_pCoreOf_of_le_normalizer 2 (hVT.trans le_sup_right)
    (sup_le (S127.Mod.L_le_normalizer h) (S127.Mod.T_le_normalizer h1222 h))
    (h.hyp.sylow.1.to_le hVT)

theorem nonempty_theta4a
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2)
    (h712 : Lemma12_7_12) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) (hW1 : ∃ w ∈ WZ T L, w ≠ 1) :
    Nonempty (Theta4a T L V C) := by
  obtain ⟨Θ, h0, hxor, hinj, hmem, hequiv⟩ := s.exists_theta h1222 h712 hC hne hT hbig hW1
  have hVQ := s.V_le_Q h1222
  exact ⟨⟨Θ, h0, hxor, hinj, hmem, hequiv, fun m v hv =>
    (Subgroup.mem_centralizer_iff.mp (hmem m).2.1 v (hVQ hv)).symm⟩⟩

theorem exists_code
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (d : Theta4a T L V C)
    (hN : L ⊔ T ≤ Subgroup.normalizer (d.V0 : Set G)) :
    ∃ B : MulAut ↥d.V0 → B6, ∀ g (hg : g ∈ L ⊔ T),
      B (conjAct d.V0 ⟨g, hN hg⟩) = C.cB (conjAct V ⟨g, s.LT_le_normalizer_V h1222 hg⟩) := by
  classical
  have hrep : ∀ a ∈ autOn (L ⊔ T) d.V0, ∃ g, ∃ hg : g ∈ L ⊔ T, conjAct d.V0 ⟨g, hN hg⟩ = a := by
    intro a ha
    obtain ⟨g, hg0, hgLT, rfl⟩ := mem_autOn'.1 ha
    exact ⟨g, hgLT, rfl⟩
  refine ⟨fun a => if h : a ∈ autOn (L ⊔ T) d.V0 then
    C.cB (conjAct V ⟨(hrep a h).choose, s.LT_le_normalizer_V h1222 (hrep a h).choose_spec.1⟩)
    else B6.id, fun g hg => ?_⟩
  have hmem : conjAct d.V0 ⟨g, hN hg⟩ ∈ autOn (L ⊔ T) d.V0 := conjAct_mem_autOn hg _
  simp only [hmem, ↓reduceDIte]
  obtain ⟨hg', he⟩ := (hrep _ hmem).choose_spec
  set g' := (hrep _ hmem).choose
  congr 1
  refine MulEquiv.ext fun v => Subtype.ext ?_
  rw [conjAct_val, conjAct_val]
  have h1 := congrArg (fun a : MulAut ↥d.V0 => ((a ⟨v, d.le_V0 v.2⟩ : ↥d.V0) : G)) he
  simp only [conjAct_val] at h1
  exact h1

theorem false_of_theta4a
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2)
    (h331 : Stmt3_3_1) (h316 : Theorem316Statement) {C : Coding ↥V} (hC : Std C T L)
    (d : Theta4a T L V C) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.setting.hyp
  have hy := h.hyp
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hVQ : V ≤ Q := s.V_le_Q h1222
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := S127.Mod.Q_le_centralizer h1222 h
  have hQT : Q ≤ T := S127.Mod.Q_le_T h
  have hLTV := s.LT_le_normalizer_V h1222
  have hVW : ∀ w ∈ WZ T L, w ∈ V → w = 1 := fun w hw hv => s.eq_one_of_mem_WZ h1222 hC hw hv
  set V₀ := d.V0 with hV₀
  have hV0Q : V₀ ≤ Q := by
    rintro _ ⟨v, hv, m, -, rfl⟩
    exact Q.mul_mem (hVQ hv) (d.mem m).1
  have hV0Z : V₀ ≤ Subgroup.centralizer (Q : Set G) := by
    rintro _ ⟨v, hv, m, -, rfl⟩
    refine Subgroup.mul_mem _ ?_ (d.mem m).2.1
    exact Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (Subgroup.mem_centralizer_iff.mp (hQV hq) v hv).symm
  have hQV0 : Q ≤ Subgroup.centralizer (V₀ : Set G) := Subgroup.le_centralizer_iff.mp hV0Z
  have hN : L ⊔ T ≤ Subgroup.normalizer (V₀ : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨v, hv, m, -, rfl⟩ := hx
    have e : g * (v * d.Θ m) * g⁻¹ = (g * v * g⁻¹) * (g * d.Θ m * g⁻¹) := by group
    rw [e, d.equiv g hg (hLTV hg)]
    exact d.mul_mem_V0 ((Subgroup.mem_normalizer_iff.mp (hLTV hg) v).mp hv) (act4_lt _ _)
  have hV0c : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hV0Z ha) b (hV0Q hb)).symm
  have hV0sq : ∀ x ∈ V₀, x ^ 2 = 1 := by
    rintro _ ⟨v, hv, m, -, rfl⟩
    have hv2 : v * v = 1 := by rw [← pow_two]; exact S127.sq_eq_one_of_mem h.hyp hv
    rw [pow_two]
    calc v * d.Θ m * (v * d.Θ m) = v * (d.Θ m * v) * d.Θ m := by group
      _ = 1 := by rw [d.comm m v hv, ← mul_assoc, hv2, one_mul, d.sq]
  have hV0el : IsElemAbelian 2 V₀ :=
    ⟨⟨⟨fun a b => Subtype.ext (hV0c a a.2 b b.2)⟩⟩, hV0sq⟩
  have hRV : IsTwoReducedIn (L ⊔ T) V := by
    rcases h1222 G T hy.simple hy.nonabelian hy.qtke hy.sylow with hAlt | h3
    · exact absurd hAlt hy.notAlt
    obtain ⟨-, -, hall⟩ := h3 L hy.maximal hy.faithful hy.quasisimple
    obtain ⟨⟨hVT, -, hred, -⟩, -, -, -⟩ := hall V hy.irrPlus
    exact isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVT.trans le_sup_right, hred⟩
  have hCLT := S127.inf_centralizer_le_Q h1222 h
  have hred0 : IsTwoReducedIn (L ⊔ T) V₀ := by
    refine ⟨hV0Q.trans (pCoreOf_le 2 _), hN, hV0el, ?_⟩
    intro D hD hDN hD2
    have hDV : D ≤ Subgroup.centralizer (V : Set G) := by
      refine hRV.2.2.2 D hD hDN fun x hx => ?_
      obtain ⟨k, hk⟩ := hD2 x hx
      exact ⟨k, Subgroup.centralizer_le d.le_V0 hk⟩
    exact fun x hx => hQV0 (hCLT ⟨hD hx, hDV hx⟩)
  have hQ0 : Q = T ⊓ Subgroup.centralizer (V₀ : Set G) := by
    refine le_antisymm (le_inf hQT hQV0) fun x hx => hCLT ⟨Subgroup.mem_sup_right hx.1, ?_⟩
    exact Subgroup.centralizer_le d.le_V0 hx.2
  obtain ⟨⟨hmax, hle, huniq⟩, -, ⟨H₀, hH₀⟩, -, -⟩ :=
    (h331 G T hy.simple hy.nonabelian hy.qtke hy.sylow).2 L hy.maximal hy.quasisimple
  rw [hy.conjClosure_eq] at hmax hle huniq hH₀
  have hperf : L = oTwoUpper L := (hy.faithful.2.1 _ (oTwoUpper_le L)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
      (le_normalizer_oTwoUpper L))
    fun _ hx => exists_pow_mem_oTwoUpper L hx).symm
  have h318 : Hyp318 T (Subgroup.normalizer (L : Set G)) L V₀ :=
    { inM := ⟨hmax, hy.normalizes⟩
      nonempty := ⟨H₀, hH₀⟩
      perfect := hperf
      le_M := Subgroup.le_normalizer
      normal := le_rfl
      unique := ⟨⟨hmax, hle⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
      reduced := hred0
      centralizer := hQ0 }
  have hq := theorem318_one_of_316 h316 hy.simple hy.nonabelian hy.qtke hy.sylow h318
  let _ : CommGroup ↥V₀ := commGroupOfElemAbelian hV0el
  have hsq : ∀ v : ↥V₀, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_pow, hV0sq v v.2, Subgroup.coe_one])
  unfold qhatInt at hq
  rw [show (2 : WithTop ℚ) = ((2 : ℚ) : WithTop ℚ) by norm_cast] at hq
  obtain ⟨A, ⟨hAX, hA1, hAc, hA2⟩, -, hidx⟩ := B45Alt.exists_cubic_of_qhatOf_le_two hsq hq
  obtain ⟨B, hB⟩ := s.exists_code h1222 d hN
  have hLTM : L ⊔ T ≤ h.hyp.MV := sup_le (S127.Mod.L_le_MV h) (S127.Mod.T_le_MV h1222 h)
  have hBrep : ∀ a ∈ autOn (L ⊔ T) V₀, ∃ g, ∃ hg : g ∈ L ⊔ T, conjAct V₀ ⟨g, hN hg⟩ = a ∧
      B a = C.cB (conjAct V ⟨g, hLTV hg⟩) := by
    intro a ha
    obtain ⟨g, hg0, hgLT, rfl⟩ := mem_autOn'.1 ha
    exact ⟨g, hgLT, rfl, hB g hgLT⟩
  have hBmul : ∀ a ∈ autOn (L ⊔ T) V₀, ∀ b ∈ autOn (L ⊔ T) V₀, B (a * b) = (B a).comp (B b) := by
    intro a ha b hb
    obtain ⟨g, hg, rfl, hga⟩ := hBrep a ha
    obtain ⟨g', hg', rfl, hgb⟩ := hBrep b hb
    have hgg : g * g' ∈ L ⊔ T := Subgroup.mul_mem _ hg hg'
    have e : conjAct V₀ ⟨g, hN hg⟩ * conjAct V₀ ⟨g', hN hg'⟩ = conjAct V₀ ⟨g * g', hN hgg⟩ := by
      rw [← map_mul]
      rfl
    rw [e, hB _ hgg, hga, hgb, ← C.cB_mul, ← map_mul]
    rfl
  have hBinj : ∀ a ∈ autOn (L ⊔ T) V₀, ∀ b ∈ autOn (L ⊔ T) V₀, B a = B b → a = b := by
    intro a ha b hb hab
    obtain ⟨g, hg, rfl, hga⟩ := hBrep a ha
    obtain ⟨g', hg', rfl, hgb⟩ := hBrep b hb
    rw [hga, hgb] at hab
    have hc := C.cB_injective hab
    have hmN : g⁻¹ * g' ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLTV hg)) (hLTV hg')
    have hm : g⁻¹ * g' ∈ Subgroup.centralizer (V : Set G) := by
      rw [← conjAct_eq_one' hmN]
      have e : (⟨g⁻¹ * g', hmN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          (⟨g, hLTV hg⟩)⁻¹ * ⟨g', hLTV hg'⟩ := rfl
      rw [e, map_mul, map_inv, hc, inv_mul_cancel]
    have hq : g⁻¹ * g' ∈ Q := hCLT ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hg', hm⟩
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [conjAct_val, conjAct_val]
    have hx := Subgroup.mem_centralizer_iff.mp (hQV0 hq) x x.2
    calc g * x * g⁻¹ = g * (x * (g⁻¹ * g')) * g'⁻¹ := by group
      _ = g * ((g⁻¹ * g') * x) * g'⁻¹ := by rw [hx]
      _ = g' * x * g'⁻¹ := by group
  have hBone : B 1 = B6.id := by
    have h1 := hB 1 (L ⊔ T).one_mem
    have e1 : (⟨1, hN (L ⊔ T).one_mem⟩ : ↥(Subgroup.normalizer (V₀ : Set G))) = 1 := rfl
    have e2 : (⟨1, hLTV (L ⊔ T).one_mem⟩ : ↥(Subgroup.normalizer (V : Set G))) = 1 := rfl
    rw [e1, e2, map_one, map_one, C.cB_one] at h1
    exact h1
  have hBnm6 : ∀ a ∈ autOn (L ⊔ T) V₀, B a ∈ nm6 ∧ (B a).Valid := by
    intro a ha
    obtain ⟨g, hg, -, hga⟩ := hBrep a ha
    rw [hga]
    exact ⟨(MVbar_code h hC.1 (conjAct_mem_autOn (hLTM hg) (hLTV hg))).1, C.cB_valid _⟩
  have hact : ∀ a ∈ autOn (L ⊔ T) V₀, ∀ v (hv : v ∈ V) m (hm : m < 16),
      ((a ⟨v * d.Θ m, d.mul_mem_V0 hv hm⟩ : ↥V₀) : G) =
        (C.dc ((B a).app (C.cd ⟨v, hv⟩)) : G) * d.Θ (act4 (permFn (B a)) m) := by
    intro a ha v hv m hm
    obtain ⟨g, hg, rfl, hga⟩ := hBrep a ha
    rw [conjAct_val, hga]
    have e1 : g * (v * d.Θ m) * g⁻¹ = (g * v * g⁻¹) * (g * d.Θ m * g⁻¹) := by group
    rw [e1, d.equiv g hg (hLTV hg)]
    congr 1
    rw [← C.cd_apply, C.dc_cd, conjAct_val]
  have hfixiff : ∀ a ∈ autOn (L ⊔ T) V₀, ∀ v (hv : v ∈ V) m (hm : m < 16),
      a ⟨v * d.Θ m, d.mul_mem_V0 hv hm⟩ = ⟨v * d.Θ m, d.mul_mem_V0 hv hm⟩ →
        (B a).app (C.cd ⟨v, hv⟩) = C.cd ⟨v, hv⟩ ∧ act4 (permFn (B a)) m = m := by
    intro a ha v hv m hm hfx
    have h1 := congrArg Subtype.val hfx
    rw [hact a ha v hv m hm] at h1
    obtain ⟨h2, h3⟩ := d.eq_of_mul_eq hVW (C.dc _).2 hv (act4_lt _ _) hm h1
    refine ⟨?_, h3⟩
    have h4 : C.dc ((B a).app (C.cd ⟨v, hv⟩)) = ⟨v, hv⟩ := Subtype.ext h2
    have h5 := congrArg C.cd h4
    rwa [C.cd_dc _ (B6.app_lt (hBnm6 a ha).2 _)] at h5
  have hcount : ∀ gs : List (MulAut ↥V₀), (∀ a ∈ gs, a ∈ A) →
      Nat.card ↥(fixV A) ≤ fVl (gs.map B) * f4l (gs.map B) := by
    classical
    intro gs hgs
    set l₁ := (List.range 64).filter fun c => (gs.map B).all fun B' => B'.app c == c with hl₁
    set l₂ := (List.range 16).filter fun m => (gs.map B).all fun B' => act4 (permFn B') m == m
      with hl₂
    have e1 : fVl (gs.map B) = l₁.length := rfl
    have e2 : f4l (gs.map B) = l₂.length := rfl
    let F : ℕ × ℕ → ↥V₀ := fun p =>
      ⟨(C.dc p.1 : G) * d.Θ (p.2 % 16), d.mul_mem_V0 (C.dc p.1).2 (Nat.mod_lt _ (by norm_num))⟩
    have hsub : (fixV A : Set ↥V₀) ⊆ ↑((l₁.toFinset ×ˢ l₂.toFinset).image F) := by
      intro x hx
      obtain ⟨v, hv, m, hm, hxe⟩ := x.2
      have hxe' : x = ⟨v * d.Θ m, d.mul_mem_V0 hv hm⟩ := Subtype.ext hxe
      have hfx : ∀ a ∈ gs, (B a).app (C.cd ⟨v, hv⟩) = C.cd ⟨v, hv⟩ ∧
          act4 (permFn (B a)) m = m := by
        intro a ha
        have hxa : a x = x := hx a (hgs a ha)
        rw [hxe'] at hxa
        exact hfixiff a (hAX (hgs a ha)) v hv m hm hxa
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨(C.cd ⟨v, hv⟩, m), ?_, ?_⟩
      · rw [Finset.mem_product, List.mem_toFinset, List.mem_toFinset, hl₁, hl₂, List.mem_filter,
          List.mem_filter]
        refine ⟨⟨List.mem_range.2 (C.cd_lt _), ?_⟩, ⟨List.mem_range.2 hm, ?_⟩⟩
        · rw [List.all_eq_true]
          intro B' hB'
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hB'
          exact beq_iff_eq.mpr (hfx a ha).1
        · rw [List.all_eq_true]
          intro B' hB'
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hB'
          exact beq_iff_eq.mpr (hfx a ha).2
      · rw [hxe']
        apply Subtype.ext
        show (C.dc (C.cd ⟨v, hv⟩) : G) * d.Θ (m % 16) = v * d.Θ m
        rw [C.dc_cd, Nat.mod_eq_of_lt hm]
    rw [e1, e2]
    calc Nat.card ↥(fixV A) = (fixV A : Set ↥V₀).ncard := Nat.card_coe_set_eq _
      _ ≤ (↑((l₁.toFinset ×ˢ l₂.toFinset).image F) : Set ↥V₀).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ((l₁.toFinset ×ˢ l₂.toFinset).image F).card := Set.ncard_coe_finset _
      _ ≤ (l₁.toFinset ×ˢ l₂.toFinset).card := Finset.card_image_le
      _ = l₁.toFinset.card * l₂.toFinset.card := Finset.card_product _ _
      _ ≤ l₁.length * l₂.length :=
          Nat.mul_le_mul (List.toFinset_card_le _) (List.toFinset_card_le _)
  have hV0card : 1024 ≤ Nat.card ↥V₀ := by
    let f : Fin 64 × Fin 16 → ↥V₀ := fun p =>
      ⟨(C.dc p.1 : G) * d.Θ p.2, d.mul_mem_V0 (C.dc p.1).2 p.2.2⟩
    have hinj : Function.Injective f := by
      rintro ⟨c, m⟩ ⟨c', m'⟩ hcm
      have h1 : (C.dc c : G) * d.Θ m = C.dc c' * d.Θ m' := congrArg Subtype.val hcm
      obtain ⟨h2, h3⟩ := d.eq_of_mul_eq hVW (C.dc c).2 (C.dc c').2 m.2 m'.2 h1
      have h4 : C.dc c = C.dc c' := Subtype.ext h2
      have h5 : (c : ℕ) = c' := by rw [← C.cd_dc c c.2, h4, C.cd_dc c' c'.2]
      exact Prod.ext (Fin.ext h5) (Fin.ext h3)
    have := Nat.card_le_card_of_injective f hinj
    simpa using this
  have hcardA : ∀ cl : List B6, (∀ a ∈ A, B a ∈ cl) → Nat.card ↥A ≤ cl.length := by
    classical
    intro cl hcl
    have hinj : Function.Injective (fun a : ↥A => (⟨B a, hcl a a.2⟩ : {b : B6 // b ∈ cl})) := by
      intro a b hab
      exact Subtype.ext (hBinj a (hAX a.2) b (hAX b.2) (congrArg Subtype.val hab))
    have h1 := Nat.card_le_card_of_injective _ hinj
    have e2 : {b : B6 // b ∈ cl} ≃ ↥cl.toFinset := Equiv.subtypeEquivRight fun b => by simp
    rw [Nat.card_congr e2, Nat.card_eq_finsetCard] at h1
    exact h1.trans (List.toFinset_card_le _)
  have hfinal : ∀ k f, Nat.card ↥A ≤ k → Nat.card ↥(fixV A) ≤ f → f * k ^ 2 < 1024 → False := by
    intro k f hk hf hlt
    have h1 := Subgroup.card_mul_index (fixV A)
    have h2 : Nat.card ↥V₀ ≤ f * k ^ 2 := by
      calc Nat.card ↥V₀ = Nat.card ↥(fixV A) * (fixV A).index := h1.symm
        _ ≤ f * Nat.card ↥A ^ 2 := Nat.mul_le_mul hf hidx
        _ ≤ f * k ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk 2)
    exact Nat.lt_irrefl _ (lt_of_le_of_lt (hV0card.trans h2) hlt)
  have hinv : ∀ a ∈ A, a ≠ 1 → B a ∈ invs6 := by
    intro a ha ha1
    have haX := hAX ha
    refine List.mem_filter.2 ⟨(hBnm6 a haX).1, ?_⟩
    have hsq2 : (B a).comp (B a) = B6.id := by
      rw [← hBmul a haX a haX, ← pow_two, hA2 a ha, hBone]
    have hne : B a ≠ B6.id := fun h1 =>
      ha1 (hBinj a haX 1 (Subgroup.one_mem _) (h1.trans hBone.symm))
    simp [hsq2, hne]
  have hcommB : ∀ a ∈ A, ∀ b ∈ A, (B a).comp (B b) = (B b).comp (B a) := by
    intro a ha b hb
    rw [← hBmul a (hAX ha) b (hAX hb), ← hBmul b (hAX hb) a (hAX ha), hAc a ha b hb]
  have hmapB : ∀ x ∈ autOn (L ⊔ T) V₀, ∀ ys : List (MulAut ↥V₀),
      (∀ y ∈ ys, y ∈ autOn (L ⊔ T) V₀) → B x ∈ ys.map B → x ∈ ys := by
    intro x hx ys hys hmem
    obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hmem
    rw [← hBinj y (hys y hy) x hx hyx]
    exact hy
  obtain ⟨⟨a₁, ha₁⟩, ha₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have ha₁1' : a₁ ≠ 1 := fun h1 => ha₁1 (Subtype.ext h1)
  have hi1 := hinv a₁ ha₁ ha₁1'
  by_cases hr1 : ∀ a ∈ A, a = 1 ∨ a = a₁
  · refine hfinal 2 _ (hcardA [B6.id, B a₁] fun a ha => ?_) (hcount [a₁] (by simpa using ha₁)) ?_
    · rcases hr1 a ha with rfl | rfl
      · simp [hBone]
      · simp
    · have := cert54_one _ hi1
      simpa using this
  push Not at hr1
  obtain ⟨a₂, ha₂, ha₂1, ha₂a₁⟩ := hr1
  have hi2 := hinv a₂ ha₂ ha₂1
  have hB12 : B a₂ ≠ B a₁ := fun h1 => ha₂a₁ (hBinj _ (hAX ha₂) _ (hAX ha₁) h1)
  have hX12 : a₁ * a₂ ∈ autOn (L ⊔ T) V₀ := Subgroup.mul_mem _ (hAX ha₁) (hAX ha₂)
  have e12 : B (a₁ * a₂) = (B a₁).comp (B a₂) := hBmul _ (hAX ha₁) _ (hAX ha₂)
  have hs2 : span2 (B a₁) (B a₂) = [1, a₁, a₂, a₁ * a₂].map B := by
    simp only [span2, List.map_cons, List.map_nil, hBone, e12]
  have hL4 : ∀ y ∈ [1, a₁, a₂, a₁ * a₂], y ∈ autOn (L ⊔ T) V₀ := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hAX ha₁
    · exact hAX ha₂
    · exact hX12
  by_cases hr2 : ∀ a ∈ A, a = 1 ∨ a = a₁ ∨ a = a₂ ∨ a = a₁ * a₂
  · refine hfinal 4 _ (hcardA (span2 (B a₁) (B a₂)) fun a ha => ?_)
      (hcount [a₁, a₂] (by simp [ha₁, ha₂])) ?_
    · rw [hs2]
      apply List.mem_map_of_mem
      rcases hr2 a ha with rfl | rfl | rfl | rfl <;> simp
    · have := cert54_two _ hi1 _ hi2 (hcommB a₁ ha₁ a₂ ha₂) hB12
      simpa using this
  push Not at hr2
  obtain ⟨a₃, ha₃, h31, h3a1, h3a2, h3a12⟩ := hr2
  have hi3 := hinv a₃ ha₃ h31
  have hB3 : B a₃ ∉ span2 (B a₁) (B a₂) := by
    rw [hs2]
    intro hm
    have := hmapB a₃ (hAX ha₃) _ hL4 hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h
    · exact h31 h
    · exact h3a1 h
    · exact h3a2 h
    · exact h3a12 h
  have e13 : B (a₁ * a₃) = (B a₁).comp (B a₃) := hBmul _ (hAX ha₁) _ (hAX ha₃)
  have e23 : B (a₂ * a₃) = (B a₂).comp (B a₃) := hBmul _ (hAX ha₂) _ (hAX ha₃)
  have e123 : B (a₁ * a₂ * a₃) = ((B a₁).comp (B a₂)).comp (B a₃) := by
    rw [hBmul _ hX12 _ (hAX ha₃), e12]
  have hid3 : B6.id.comp (B a₃) = B a₃ := B6.id_comp (hBnm6 a₃ (hAX ha₃)).2
  set L8 : List (MulAut ↥V₀) := [1, a₁, a₂, a₁ * a₂, a₃, a₁ * a₃, a₂ * a₃, a₁ * a₂ * a₃]
    with hL8def
  have hs3 : span3 (B a₁) (B a₂) (B a₃) = L8.map B := by
    simp only [span3, span2, hL8def, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, hBone, e12, e13, e23, e123, hid3]
  have hL8 : ∀ y ∈ L8, y ∈ autOn (L ⊔ T) V₀ := by
    intro y hy
    simp only [hL8def, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hAX ha₁
    · exact hAX ha₂
    · exact hX12
    · exact hAX ha₃
    · exact Subgroup.mul_mem _ (hAX ha₁) (hAX ha₃)
    · exact Subgroup.mul_mem _ (hAX ha₂) (hAX ha₃)
    · exact Subgroup.mul_mem _ hX12 (hAX ha₃)
  by_cases hr3 : ∀ a ∈ A, a ∈ L8
  · refine hfinal 8 _ (hcardA (span3 (B a₁) (B a₂) (B a₃)) fun a ha => ?_)
      (hcount [a₁, a₂, a₃] (by simp [ha₁, ha₂, ha₃])) ?_
    · rw [hs3]
      exact List.mem_map_of_mem (hr3 a ha)
    · have := cert54_three _ hi1 _ hi2 (hcommB a₁ ha₁ a₂ ha₂) hB12 _ hi3
        (hcommB a₁ ha₁ a₃ ha₃) (hcommB a₂ ha₂ a₃ ha₃) hB3
      simpa using this
  push Not at hr3
  obtain ⟨a₄, ha₄, h4⟩ := hr3
  have h41 : a₄ ≠ 1 := fun h1 => h4 (by rw [h1, hL8def]; exact List.mem_cons_self)
  have := cert54_rank _ hi1 _ hi2 (hcommB a₁ ha₁ a₂ ha₂) hB12 _ hi3 (hcommB a₁ ha₁ a₃ ha₃)
    (hcommB a₂ ha₂ a₃ ha₃) hB3 _ (hinv a₄ ha₄ h41) (hcommB a₁ ha₁ a₄ ha₄) (hcommB a₂ ha₂ a₄ ha₄)
    (hcommB a₃ ha₃ a₄ ha₄)
  rw [hs3] at this
  exact h4 (hmapB a₄ (hAX ha₄) L8 hL8 this)

theorem comm_le_V_of_big
    [IsMulCommutative ↥V]
    (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1) (h712 : Lemma12_7_12) (h316 : Theorem316Statement)
    {C : Coding ↥V} (hC : Std C T L) (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V)
    (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) : ⁅pCoreOf 2 L, L⁆ ≤ V := by
  rcases s.comm_le_or_exists h1222 hC hne hT hbig with h | ⟨w, hwQ, hwZ, hwX, hw1, hw2⟩
  · exact h
  · exfalso
    obtain ⟨d⟩ := s.nonempty_theta4a h1222 h712 hC hne hT hbig ⟨w, ⟨hwQ, hwZ, hwX, hw2⟩, hw1⟩
    exact s.false_of_theta4a h1222 h331 h316 hC d

theorem comm_le_V_of_ne
    [IsMulCommutative ↥V]
    (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1) (h712 : Lemma12_7_12) (h316 : Theorem316Statement)
    (hU : autOn (U714 T L V z) V ≠ autOn (R1 T L V) V) :
    s.setting.hyp.hyp.MVbar ≠ autOn L V ∧ ∃ C : Coding ↥V, Std C T L ∧
      (∀ a ∈ autOn T V, C.cB a ∈ s0p) ∧ (∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) ∧
      ⁅pCoreOf 2 L, L⁆ ≤ V := by
  obtain ⟨hne, C, hC, hT, hcases⟩ := s.autOn_U_cases h1222 hU
  rcases hcases with hsmall | hbig
  · exact (s.false_of_small h1222 hC hsmall).elim
  · exact ⟨hne, C, hC, hT, hbig,
      s.comm_le_V_of_big h1222 h331 h712 h316 hC hne hT hbig⟩

end CFSG.Quasithin.H13.S127.L715.Set714
