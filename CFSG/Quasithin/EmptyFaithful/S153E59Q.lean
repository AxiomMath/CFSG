module

public import CFSG.Quasithin.EmptyFaithful.S153E59P
public import CFSG.Quasithin.EmptyFaithful.S153E54G
public import CFSG.Quasithin.EmptyFaithful.S153E55D
public import CFSG.Quasithin.EmptyFaithful.S153E59I

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section Elements

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}

include cx in
theorem pCoreOf_Y_le_centralizer :
    pCoreOf 2 (Y153 Mc M) ≤ Subgroup.centralizer (VZ T M : Set G) := by
  rw [cx.r49.case_one.1]
  exact inf_le_right

include cx in
theorem pCoreOf_Y_le_Ni (N : Subgroup (MulAut ↥(VZ T M))) :
    pCoreOf 2 (Y153 Mc M) ≤ Ni153 T Mc M V₁ N := by
  intro ρ hρ
  have hρY : ρ ∈ Y153 Mc M := pCoreOf_le 2 _ hρ
  have hρN : ρ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    cx.c.hyp.le_normalizer (Y153_le Mc M hρY)
  refine S153E.mem_preAut153.2 ⟨Subgroup.mem_sup_left hρY, hρN, ?_⟩
  have : conjAct (VZ T M) ⟨ρ, hρN⟩ = 1 :=
    (conjAct_eq_one_iff _ _).2 (pCoreOf_Y_le_centralizer cx hρ)
  rw [this]
  exact N.one_mem

omit [Finite G] in
theorem exists_mul_of_sup {Y D R : Subgroup G} (hDN : D ≤ Subgroup.normalizer (R : Set G))
    (hYD : Y = R ⊔ D) {y : G} (hy : y ∈ Y) : ∃ d ∈ D, ∃ ρ ∈ R, y = d * ρ := by
  have e := Subgroup.coe_mul_of_left_le_normalizer_right D R hDN
  rw [sup_comm, ← hYD] at e
  have hy' : y ∈ (Y : Set G) := hy
  rw [e] at hy'
  obtain ⟨d, hd, ρ, hρ, rfl⟩ := hy'
  exact ⟨d, hd, ρ, hρ, rfl⟩

theorem exists_d12 (h113 : StageLemma14113) (c : Chain15354 cx N₁ N₂ g s) {D : Subgroup G}
    (hDY : D ≤ Y153 Mc M) (hYD : Y153 Mc M = pCoreOf 2 (Y153 Mc M) ⊔ D) :
    ∃ d₁ d₂ : G, d₁ ∈ D ∧ d₂ ∈ D ∧ d₁ ∈ Ni153 T Mc M V₁ N₁ ∧ d₂ ∈ Ni153 T Mc M V₁ N₂ ∧
      (∀ v ∈ VZ T M, d₁ * v * d₁⁻¹ = v → v = 1) ∧ (∀ v ∈ VZ T M, d₂ * v * d₂⁻¹ = v → v = 1) := by
  obtain ⟨y₁, y₂, hy₁Y, hy₂Y, -, -, hy₁f, hy₂f, hy₁N, hy₂N, -, -⟩ := S153E55.exists_y12 h113 cx c
  have hDN : D ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
    hDY.trans (le_normalizer_pCoreOf 2 (Y153 Mc M))
  have key : ∀ y : G, y ∈ Y153 Mc M → (∀ v ∈ VZ T M, y * v * y⁻¹ = v → v = 1) →
      ∀ N : Subgroup (MulAut ↥(VZ T M)), y ∈ Ni153 T Mc M V₁ N →
      ∃ d : G, d ∈ D ∧ d ∈ Ni153 T Mc M V₁ N ∧ (∀ v ∈ VZ T M, d * v * d⁻¹ = v → v = 1) := by
    intro y hyY hyf N hyN
    obtain ⟨d, hd, ρ, hρ, rfl⟩ := exists_mul_of_sup hDN hYD hyY
    have hρC : ρ ∈ Subgroup.centralizer (VZ T M : Set G) := pCoreOf_Y_le_centralizer cx hρ
    refine ⟨d, hd, ?_, ?_⟩
    · have h1 : d = (d * ρ) * ρ⁻¹ := by group
      rw [h1]
      exact (Ni153 T Mc M V₁ N).mul_mem hyN ((Ni153 T Mc M V₁ N).inv_mem (pCoreOf_Y_le_Ni cx N hρ))
    · intro v hv hdv
      apply hyf v hv
      have hc : ρ⁻¹ * v * ρ = v := by
        have := Subgroup.mem_centralizer_iff.mp hρC v hv
        calc ρ⁻¹ * v * ρ = ρ⁻¹ * (v * ρ) := by group
          _ = ρ⁻¹ * (ρ * v) := by rw [this]
          _ = v := by group
      calc d * ρ * v * (d * ρ)⁻¹ = d * (ρ * v * ρ⁻¹) * d⁻¹ := by group
        _ = d * v * d⁻¹ := by
          have h2 : ρ * v * ρ⁻¹ = v := by
            have := Subgroup.mem_centralizer_iff.mp hρC v hv
            rw [← this]; group
          rw [h2]
        _ = v := hdv
  obtain ⟨d₁, hd₁D, hd₁N, hd₁f⟩ := key y₁ hy₁Y hy₁f N₁ hy₁N
  obtain ⟨d₂, hd₂D, hd₂N, hd₂f⟩ := key y₂ hy₂Y hy₂f N₂ hy₂N
  exact ⟨d₁, d₂, hd₁D, hd₂D, hd₁N, hd₂N, hd₁f, hd₂f⟩

theorem centralizer_normalizes_Ni (cx : Ctx15350 T Mc M V₁ V₂ t) (N : Subgroup (MulAut ↥(VZ T M)))
    {r n : G} (hrT : r ∈ T) (hrC : r ∈ Subgroup.centralizer (VZ T M : Set G))
    (hn : n ∈ Ni153 T Mc M V₁ N) : r * n * r⁻¹ ∈ Ni153 T Mc M V₁ N := by
  obtain ⟨hnI, hnN, hnc⟩ := S153E.mem_preAut153.1 hn
  have hrN : r ∈ Subgroup.normalizer (VZ T M : Set G) :=
    cx.c.hyp.le_normalizer (S153E.T_le_M cx hrT)
  have hrI : r * n * r⁻¹ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc :=
    (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_IYU cx hrT) n).mp hnI
  have hrnN : r * n * r⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hnN) (Subgroup.inv_mem _ hrN)
  refine S153E.mem_preAut153.2 ⟨hrI, hrnN, ?_⟩
  have h1 : conjAct (VZ T M) ⟨r, hrN⟩ = 1 := (conjAct_eq_one_iff _ _).2 hrC
  have : conjAct (VZ T M) ⟨r * n * r⁻¹, hrnN⟩ =
      conjAct (VZ T M) ⟨r, hrN⟩ * conjAct (VZ T M) ⟨n, hnN⟩ * (conjAct (VZ T M) ⟨r, hrN⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [this, h1, one_mul, inv_one, mul_one]
  exact hnc

section PD

variable {I P V N₁ N₂ P₁ P₂ : Subgroup G}

omit [Finite G] in
theorem normalizes_P₁ (pd : S153E55.PDecomp I P V N₁ N₂ P₁ P₂) {r : G}
    (hrP : r ∈ Subgroup.normalizer (P : Set G)) (hrNV : r ∈ Subgroup.normalizer (V : Set G))
    (hrV : ∀ v ∈ V, r * v * r⁻¹ = v) (hrN : ∀ n ∈ N₂, r⁻¹ * n * r ∈ N₂) {x : G} (hx : x ∈ P₁) :
    r * x * r⁻¹ ∈ P₁ := by
  have hx' := hx
  rw [pd.cent₁] at hx'
  obtain ⟨hxP, hxV, hxn⟩ := hx'
  rw [pd.cent₁]
  refine ⟨(Subgroup.mem_normalizer_iff.mp hrP x).mp hxP,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hrNV hxV) (Subgroup.inv_mem _ hrNV), ?_⟩
  intro n hn
  have h1 := hxn _ (hrN n hn)
  have h2 : (r * x * r⁻¹) * n * (r * x * r⁻¹)⁻¹ * n⁻¹ =
      r * (x * (r⁻¹ * n * r) * x⁻¹ * (r⁻¹ * n * r)⁻¹) * r⁻¹ := by group
  rw [h2, hrV _ h1]
  exact h1

end PD

include cx in
theorem centralizer_T_le_pCoreOf_Y (h113 : StageLemma14113) (c : Chain15354 cx N₁ N₂ g s)
    (hs : s = 1) :
    T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ pCoreOf 2 (Y153 Mc M) := by
  subst hs
  have hV := cx.c.hyp.elemAbelian
  have hI := c.h54.one
  have pd := S153E55.pdecomp cx c
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, -, hDY, hD3, hDi⟩ := S153E.exists_sylow_ge (p := 3) (Q := (⊥ : Subgroup G))
    (K := Y153 Mc M) (IsPGroup.of_card (p := 3) (n := 0) (by simp)) bot_le
  have hYD := S153E.Y_eq_sup_of_sylow cx hDY hD3 hDi
  obtain ⟨d₁, d₂, hd₁D, hd₂D, hd₁N, hd₂N, hd₁f, hd₂f⟩ := exists_d12 cx h113 c hDY hYD
  have hBeq : pCoreOf 2 (Y153 Mc M ⊔ T) = T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    Hyp153.lemma_15_3_7_pCore h113 cx.c.hyp
  have hBnorm : Y153 Mc M ⊔ T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) := by
    rw [← hBeq]
    exact le_normalizer_pCoreOf 2 _
  have hRC := pCoreOf_Y_le_centralizer cx
  have hRY : pCoreOf 2 (Y153 Mc M) ≤ Y153 Mc M := pCoreOf_le 2 _
  have hRT : pCoreOf 2 (Y153 Mc M) ≤ T := pCoreOf_Y_le_T cx
  have hR2 : IsPGroup 2 ↥(pCoreOf 2 (Y153 Mc M)) := pCoreOf_isPGroup 2 _
  have hRp : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 (Y153 Mc M)) := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hVD : ∀ d ∈ D, ∀ v ∈ pCoreOf 2 (Y153 Mc M), d * v * d⁻¹ ∈ pCoreOf 2 (Y153 Mc M) :=
    fun d hd v hv =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (Y153 Mc M) (hDY hd)) v).mp hv
  intro b hb
  have hinv : ∀ d ∈ D, b⁻¹ * (d * b * d⁻¹) ∈ pCoreOf 2 (Y153 Mc M) := by
    intro d hd
    have hdY := hDY hd
    have hB1 : d * b * d⁻¹ ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hBnorm (Subgroup.mem_sup_left hdY)) b).mp hb
    have hB2 : b⁻¹ * (d * b * d⁻¹) ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) hB1
    have hY1 : b⁻¹ * (d * b * d⁻¹) ∈ Y153 Mc M := by
      have h1 : b⁻¹ * d * b⁻¹⁻¹ ∈ Y153 Mc M :=
        (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_Y cx (T.inv_mem hb.1)) d).mp hdY
      have e : b⁻¹ * (d * b * d⁻¹) = (b⁻¹ * d * b⁻¹⁻¹) * d⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hdY)
    rw [cx.r49.case_one.1]
    exact ⟨hY1, hB2.2⟩
  obtain ⟨r, hrR, hrD⟩ := S153E.exists_fixed_in_coset hD3 hRp hinv hVD
  have hrB : r ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    have e : r = b * (b⁻¹ * r) := by group
    rw [e]
    exact Subgroup.mul_mem _ hb ⟨hRT hrR, hRC hrR⟩
  have hrT : r ∈ T := hrB.1
  have hrC : r ∈ Subgroup.centralizer (VZ T M : Set G) := hrB.2
  have hrd : ∀ d ∈ D, r * d = d * r := fun d hd => by
    have := hrD d hd
    calc r * d = (d * r * d⁻¹) * d := by rw [this]
      _ = d * r := by group
  have hrNV : r ∈ Subgroup.normalizer (VZ T M : Set G) := cx.c.hyp.le_normalizer (S153E.T_le_M cx hrT)
  have hrV : ∀ v ∈ VZ T M, r * v * r⁻¹ = v := fun v hv => by
    have := Subgroup.mem_centralizer_iff.mp hrC v hv
    calc r * v * r⁻¹ = (v * r) * r⁻¹ := by rw [this]
      _ = v := by group
  have hrP : r ∈ Subgroup.normalizer (Pgp153 T M V₁ Mc g : Set G) := S153E55.T_le_normalizer_P hI cx hrT
  have hT2 : IsPGroup 2 T := cx.hF.sylow_H.2.1
  obtain ⟨m, hm⟩ := hT2 ⟨r, hrT⟩
  have hr2 : r ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hVab : ∀ v ∈ VZ T M, ∀ w ∈ VZ T M, v * w = w * v := fun v hv w hw => by
    have := hV.1
    exact setLike_mul_comm hv hw
  have hrN : ∀ (N : Subgroup (MulAut ↥(VZ T M))) (n : G), n ∈ Ni153 T Mc M V₁ N →
      r⁻¹ * n * r ∈ Ni153 T Mc M V₁ N := fun N n hn => by
    have := centralizer_normalizes_Ni cx N (T.inv_mem hrT) (Subgroup.inv_mem _ hrC) hn
    simpa using this
  have hVne : ∀ d : G, (∀ v ∈ VZ T M, d * v * d⁻¹ = v → v = 1) → d ∈ Pgp153 T M V₁ Mc g → False := by
    intro d hdf hd
    have hcard := cx.c.hyp.card_VZ
    have hbot : VZ T M = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have h1 : d * v * d⁻¹ = v := by
        have := pd.V_central v hv d hd
        calc d * v * d⁻¹ = (v * d) * d⁻¹ := by rw [← this]
          _ = v := by group
      exact (Subgroup.mem_bot).2 (hdf v hv h1)
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hP₁ : ∀ x ∈ Pi153 T Mc M V₁ N₁ g, r * x * r⁻¹ * x⁻¹ = 1 := by
    obtain ⟨k, hk⟩ := hD3 ⟨d₁, hd₁D⟩
    have hdk : d₁ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine centralizes_Pi c.h54.four_nat₁ hd₁N (fun h => hVne d₁ hd₁f h) hdk
      (fun x hx => pd.conj_P₁ (pd.N₁_le_I hd₁N) hx)
      (fun x hx => normalizes_P₁ pd hrP hrNV hrV (hrN N₂) hx) (hrd d₁ hd₁D) (hrd d₂ hd₂D) hrV hr2
      hVab hd₂f (fun x hx => ?_)
    have hx' := hx
    rw [pd.cent₁] at hx'
    obtain ⟨-, -, hxn⟩ := hx'
    have h := hxn d₂ hd₂N
    have e : d₂ * x * d₂⁻¹ * x⁻¹ = (x * d₂ * x⁻¹ * d₂⁻¹)⁻¹ := by group
    rw [e]
    exact (VZ T M).inv_mem h
  have hP₂ : ∀ x ∈ Pi153 T Mc M V₁ N₂ g, r * x * r⁻¹ * x⁻¹ = 1 := by
    obtain ⟨k, hk⟩ := hD3 ⟨d₂, hd₂D⟩
    have hdk : d₂ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine centralizes_Pi c.h54.four_nat₂ hd₂N (fun h => hVne d₂ hd₂f h) hdk
      (fun x hx => pd.symm.conj_P₁ (pd.N₂_le_I hd₂N) hx)
      (fun x hx => normalizes_P₁ pd.symm hrP hrNV hrV (hrN N₁) hx) (hrd d₂ hd₂D) (hrd d₁ hd₁D)
      hrV hr2 hVab hd₁f (fun x hx => ?_)
    have hx' := hx
    rw [pd.symm.cent₁] at hx'
    obtain ⟨-, -, hxn⟩ := hx'
    have h := hxn d₁ hd₁N
    have e : d₁ * x * d₁⁻¹ * x⁻¹ = (x * d₁ * x⁻¹ * d₁⁻¹)⁻¹ := by group
    rw [e]
    exact (VZ T M).inv_mem h
  have hrP' : ∀ x ∈ Pgp153 T M V₁ Mc g, r * x = x * r := by
    intro x hx
    obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := pd.exists_mul hx
    have h1 := hP₁ p₁ hp₁
    have h2 := hP₂ p₂ hp₂
    have e1 : r * p₁ = p₁ * r := by
      calc r * p₁ = (r * p₁ * r⁻¹ * p₁⁻¹) * (p₁ * r) := by group
        _ = p₁ * r := by rw [h1, one_mul]
    have e2 : r * p₂ = p₂ * r := by
      calc r * p₂ = (r * p₂ * r⁻¹ * p₂⁻¹) * (p₂ * r) := by group
        _ = p₂ * r := by rw [h2, one_mul]
    calc r * (p₁ * p₂) = (r * p₁) * p₂ := by group
      _ = p₁ * (r * p₂) := by rw [e1]; group
      _ = p₁ * (p₂ * r) := by rw [e2]
      _ = (p₁ * p₂) * r := by group
  have hRP : pCoreOf 2 (Y153 Mc M) ≤ Pgp153 T M V₁ Mc g := by
    rw [S153E55.P_eq hI]
    refine le_pCoreOf_of_le_normalizer 2 (hRY.trans le_sup_left) ?_ hR2
    exact sup_le (le_normalizer_pCoreOf 2 _)
      ((S153E55.U_le_normalizer_Y cx).trans (normalizer_le_normalizer_pCoreOf 2 _))
  have hrY : ∀ y ∈ Y153 Mc M, y * r = r * y := by
    intro y hy
    obtain ⟨d, hd, ρ, hρ, rfl⟩ := exists_mul_of_sup
      (hDY.trans (le_normalizer_pCoreOf 2 (Y153 Mc M))) hYD hy
    have h1 := hrd d hd
    have h2 := hrP' ρ (hRP hρ)
    calc d * ρ * r = d * (ρ * r) := by group
      _ = d * (r * ρ) := by rw [h2]
      _ = (d * r) * ρ := by group
      _ = (r * d) * ρ := by rw [h1]
      _ = r * (d * ρ) := by group
  have hr1 : r = 1 := S153E54.centralizer_T_Y_trivial h113 cx hrT hrY
  rw [hr1, mul_one] at hrR
  have := (pCoreOf 2 (Y153 Mc M)).inv_mem hrR
  simpa using this

end Elements

end S153E59

end CFSG.Quasithin
