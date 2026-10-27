module

public import CFSG.Quasithin.H13.L32A76S2d

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Q511 CFSG.Quasithin.H13.L32A.M76 CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V H Y : Subgroup G} {γ γ' : F8.Geom T L H}
  {g : ↥((L ⊔ T) ⊔ H)}

namespace Ctx

variable (C : Ctx G T L V H Y)
include C

theorem good_of_setup [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    (s : F8Setup T V L H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)))
    (hle : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G))) :
    ∃ e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H)), Good C γ γ' g e₁ e₂ b := by
  obtain ⟨d₁, d₂, hd₁, hd₂, hL, hEp⟩ := C.exists_lines
  obtain ⟨hmγ, hmH, hne, b, hb, hBz, hcase⟩ := C.rank_one s hpos hle hL hEp hd₁ hd₂
  have hb2 : b ^ 2 = 1 := (C.unpack s hpos hle).2.2.1.2 b hb
  have hV₁ := C.V₁_le_comm s hpos hle hL hEp hd₁ hd₂
  have hA := C.comm_eq_preimage s hb hBz hb2 hV₁
  have hrk : rk (cw b) = 2 := by rcases hcase with h | h <;> exact h.2.2.2
  have hcard := C.card_comm hA hV₁ hrk
  have hl1 := C.l1_le_normalizer s hb hA
  have hA₁ := C.A₁_le_comm hne
  rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact ⟨d₁, d₂, b, ⟨s, hmγ, hmH, hL, hd₁, hd₂, hEp, hb, hBz, h1, h2, h3, h4, hA, hV₁,
      hA₁, hcard, hl1⟩⟩
  · exact ⟨d₂, d₁, b, ⟨s, hmγ, hmH, hL.symm, hd₂, hd₁,
      fun e he => hL.inE_swap (hEp e he), hb, hBz, h1, h2, h3, h4, hA, hV₁, hA₁, hcard, hl1⟩⟩

theorem A_le_UH (s : F8Setup T V L H γ γ' g) :
    ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ ≤ conjClosure V H :=
  (C.h98.F913_3 s (X := V) (Y := V) (Or.inl rfl) (Or.inl rfl)).trans inf_le_left

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
  {e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}

theorem comm_Dγ_ne_bot (D : Good C γ γ' g e₁ e₂ b) :
    ⁅F8.Dγ V (fsuV1 T V) H (g : G), conjClosure V H⁆ ≠ ⊥ := by
  have hlt : F8.Dγ V (fsuV1 T V) H (g : G) < F8.Uγ V H (g : G) := by
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun he => ?_
    have h := D.mγ
    rw [he] at h
    simp [mIdx] at h
  obtain ⟨δ, δ', k, y, sk, -, -, hUδ, hUH, hDHk, hDδk⟩ :=
    C.h98.exists_symmetric_setup D.s (C.h98.not_Vγ_le_ballStab_of_lt D.s hlt)
  have hmγk : mIdx (F8.Uγ V H (k : G)) (F8.Dγ V (fsuV1 T V) H (k : G)) = 1 := by
    rw [hUδ, hDδk, F9.mIdx_conjSub, D.mH]
  have hmHk : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (k : G)) = 1 := by
    rw [hDHk, ← hUH, F9.mIdx_conjSub, D.mγ]
  obtain ⟨-, -, hnek, -⟩ := C.rank_one sk (by omega) (by omega) D.lines D.inE D.e₁E D.e₂E
  have e : ⁅F8.DH V (fsuV1 T V) H (k : G), F8.Uγ V H (k : G)⁆ =
      Quasithin.conjSub (y : G) ⁅F8.Dγ V (fsuV1 T V) H (g : G), conjClosure V H⁆ := by
    rw [hDHk, hUδ]
    exact (Subgroup.map_commutator _ _ _).symm
  intro hbot
  apply hnek
  rw [e, hbot]
  exact Subgroup.map_bot _

theorem ZH_le_DH (D : Good C γ γ' g e₁ e₂ b) :
    conjClosure V H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤
      F8.DH V (fsuV1 T V) H (g : G) := by
  obtain ⟨x, hx, u₀, hu₀, hxu⟩ : ∃ x ∈ F8.Dγ V (fsuV1 T V) H (g : G), ∃ u₀ ∈ conjClosure V H,
      x * u₀ ≠ u₀ * x := by
    by_contra hcon
    push Not at hcon
    apply C.comm_Dγ_ne_bot D
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx u hu
    rw [Subgroup.mem_bot, commutatorElement_def, hcon x hx u hu, mul_inv_cancel_right,
      mul_inv_cancel]
  have hxQ : x ∈ pCoreOf 2 H := by
    rw [C.h98.Dγ_eq_inf_pCoreOf D.s] at hx
    exact hx.2
  have hDC : F8.DH V (fsuV1 T V) H (g : G) ≤
      conjClosure V H ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro d hd
    refine ⟨centralizerMod_le_left _ _ _ hd, Subgroup.mem_centralizer_iff.mpr fun x' hx' => ?_⟩
    rw [Set.mem_singleton_iff.mp hx']
    have hc : ⁅d, x⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hd hx
      rwa [C.h98.F913_7 D.s, Subgroup.mem_bot] at this
    rw [commutatorElement_def] at hc
    calc x * d = (d * x * d⁻¹ * x⁻¹)⁻¹ * d * x := by group
      _ = d * x := by rw [hc, inv_one, one_mul]
  have hnot : ¬ conjClosure V H ≤ conjClosure V H ⊓ Subgroup.centralizer ({x} : Set G) :=
    fun hle => hxu (Subgroup.mem_centralizer_iff.mp (hle hu₀).2 x (Set.mem_singleton x))
  have hU2 : IsPGroup 2 (conjClosure V H) :=
    (pCoreOf_isPGroup 2 H).to_le C.h91.conjClosure_Vp_le_pCoreOf
  have hidx : (F8.DH V (fsuV1 T V) H (g : G)).relIndex (conjClosure V H) = 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hU2, D.mH, pow_one]
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hDC inf_le_left
  rw [hidx] at hmul
  have h1 : (conjClosure V H ⊓ Subgroup.centralizer ({x} : Set G)).relIndex
      (conjClosure V H) ≠ 1 := fun e => hnot (Subgroup.relIndex_eq_one.mp e)
  have h2 : (F8.DH V (fsuV1 T V) H (g : G)).relIndex
      (conjClosure V H ⊓ Subgroup.centralizer ({x} : Set G)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro_left _ hmul) with h | h
    · exact absurd h h1
    · rw [h] at hmul
      omega
  refine le_trans ?_ (Subgroup.relIndex_eq_one.mp h2)
  intro z hz
  refine ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun x' hx' => ?_⟩
  rw [Set.mem_singleton_iff.mp hx']
  exact Subgroup.mem_centralizer_iff.mp hz.2 x hxQ

theorem inf_ZH_le (D : Good C γ γ' g e₁ e₂ b) :
    ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ ⊓
        (conjClosure V H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) ≤ fsuV1 T V := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set Z := conjClosure V H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) with hZ
  intro a ha
  obtain ⟨haA, haZ⟩ := Subgroup.mem_inf.mp ha
  by_contra haV
  have hUγH := C.h98.Uγ_le_H D.s
  rw [D.A_eq] at haA
  obtain ⟨w, hw, rfl⟩ := haA
  have hw1 : C.piU w ≠ 1 := fun h => haV ((C.piU_eq_one_iff).mp h)
  have hwe : C.piU w ∈ cw e₁ := D.cw_le (Subgroup.mem_comap.mp hw)
  have hZH : ∀ y : ↥H, ∀ z ∈ Z, (y : G) * z * (y : G)⁻¹ ∈ Z := by
    intro y z hz
    refine ⟨conj_mem_UH y.2 hz.1, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have hq' : (y : G)⁻¹ * q * (y : G) ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem y.2)) q).mp hq
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hq'
    calc q * ((y : G) * z * (y : G)⁻¹)
        = (y : G) * (((y : G)⁻¹ * q * (y : G)) * z) * (y : G)⁻¹ := by group
      _ = (y : G) * (z * ((y : G)⁻¹ * q * (y : G))) * (y : G)⁻¹ := by rw [hc]
      _ = (y : G) * z * (y : G)⁻¹ * q := by group
  set PZ := (Z.subgroupOf (conjClosure V H)).map C.piU with hPZ
  set X := PZ ⊓ cw e₁ with hX
  have hwX : C.piU w ∈ X := ⟨⟨w, Subgroup.mem_subgroupOf.mpr haZ, rfl⟩, hwe⟩
  obtain ⟨y, -, hye⟩ := (FixR.mem_autOn_tilde_iff C.h91 C.hYH).mp D.e₁E
  have hT : ∀ (f : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))),
      ∀ t ∈ (⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V H))), f t ∈ (⊤ : Subgroup _) :=
    fun _ _ _ => Subgroup.mem_top _
  have hXe : ∀ t ∈ X, e₁ t ∈ X := by
    rintro t ⟨⟨z, hz, rfl⟩, ht⟩
    refine ⟨⟨⟨(y : G) * z * (y : G)⁻¹, conj_mem_UH y.2 z.2⟩,
      Subgroup.mem_subgroupOf.mpr (hZH y z (Subgroup.mem_subgroupOf.mp hz)), ?_⟩, ?_⟩
    · rw [← hye]
      exact C.piU_conj y z
    · exact map_commHom_invariant rfl (hT e₁) _ ht
  have hfix : X ⊓ fixV (Subgroup.zpowers e₁) = ⊥ :=
    inf_fix_le_of_le inf_le_right e₁ D.lines.fpf₁
  have hdvd := dvd_two_pow_rk_sub_one D.lines.hV hXe D.lines.h5₁ hfix
  have hX4 : rk X ≤ 4 := by
    have := rk_mono (inf_le_right : X ≤ cw e₁)
    rwa [D.lines.rk₁] at this
  have hXeq : X = cw e₁ := by
    rcases rk_of_dvd_five hdvd hX4 with h0 | h4
    · exfalso
      have hbot : X = ⊥ := (rk_eq_zero_iff D.lines.hV).mp h0
      rw [hbot] at hwX
      exact hw1 (Subgroup.mem_bot.mp hwX)
    · exact eq_of_le_of_rk_le D.lines.hV inf_le_right (by rw [D.lines.rk₁, h4])
  have hle1 : cw e₁ ≤ PZ := by
    rw [← hXeq]
    exact inf_le_left
  obtain ⟨u, huγ, hub⟩ := (FixR.mem_autOn_tilde_iff C.h91 hUγH).mp D.bB
  have hA₁U : F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure V H := D.A₁_le.trans (C.A_le_UH D.s)
  set PA := ((F8.A₁ (fsuV1 T V) (g : G)).subgroupOf (conjClosure V H)).map C.piU with hPA
  have hle2 : (cw e₁).map (commHom b) ≤ PA := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hle1 ht
    have hzD : (z : G) ∈ F8.DH V (fsuV1 T V) H (g : G) :=
      C.ZH_le_DH D (Subgroup.mem_subgroupOf.mp hz)
    have hcomm : (u : G) * z * (u : G)⁻¹ * (z : G)⁻¹ ∈ F8.A₁ (fsuV1 T V) (g : G) := by
      have h1 := hzD.2.2 u huγ
      have e : ((z : G) * u * (z : G)⁻¹ * (u : G)⁻¹)⁻¹ =
          (u : G) * z * (u : G)⁻¹ * (z : G)⁻¹ := by group
      rw [← e]
      exact Subgroup.inv_mem _ h1
    refine ⟨⟨_, comm_mem_UH u.2 z.2⟩, Subgroup.mem_subgroupOf.mpr hcomm, ?_⟩
    rw [C.piU_comm u z, hub]
  have hb2 : b ^ 2 = 1 :=
    (C.unpack D.s (by rw [D.mγ]; norm_num) (by rw [D.mγ, D.mH])).2.2.1.2 b D.bB
  have hrk2 := (D.lines.rk_inv hb2 D.inv).1
  have hcardPA : Nat.card PA ≤ 2 := by
    have h1 : Nat.card PA ∣ Nat.card ↥((F8.A₁ (fsuV1 T V) (g : G)).subgroupOf
        (conjClosure V H)) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥((F8.A₁ (fsuV1 T V) (g : G)).subgroupOf (conjClosure V H)) =
        Nat.card (F8.A₁ (fsuV1 T V) (g : G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁U).toEquiv
    rw [h2, C.h98.card_A₁] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  have hcard4 : Nat.card ↥((cw e₁).map (commHom b)) = 4 := by
    rw [card_eq_two_pow D.lines.hV, hrk2]
    norm_num
  have := Subgroup.card_le_of_le hle2
  omega

theorem exists_noncomm (D : Good C γ γ' g e₁ e₂ b) {x : G}
    (hxA : x ∈ ⁅conjClosure V H, F8.Uγ V H (g : G)⁆) (hxV : x ∉ fsuV1 T V) :
    ∃ q ∈ pCoreOf 2 H, q * x ≠ x * q := by
  by_contra hcon
  push Not at hcon
  exact hxV (C.inf_ZH_le D ⟨hxA, C.A_le_UH D.s hxA,
    Subgroup.mem_centralizer_iff.mpr fun q hq => hcon q hq⟩)

theorem pCoreOf_le_normalizer_A (D : Good C γ γ' g e₁ e₂ b) :
    pCoreOf 2 H ≤
      Subgroup.normalizer ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G) := by
  intro q hq
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  have h1 := C.h91.commutator_mem_V₁ hq (C.A_le_UH D.s ha)
  have e : q * a * q⁻¹ = (q * a * q⁻¹ * a⁻¹) * a := by group
  rw [e]
  exact Subgroup.mul_mem _ (D.V₁_le h1) ha

end Ctx

end CFSG.Quasithin.H13.L32A.S2

end
