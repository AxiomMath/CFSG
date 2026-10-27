module

public import CFSG.Quasithin.H13.A5S1327z
public import CFSG.Quasithin.H13.A5S1327w
public import CFSG.Quasithin.H13.A5S1327x

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.A5Model

@[expose] def e04 : W5 := Multiplicative.ofAdd (e2 0 4)

@[expose] def e14 : W5 := Multiplicative.ofAdd (e2 1 4)

@[expose] def c014 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 4

theorem c014_props : Equiv.Perm.sign c014 = 1 ∧ pact c014 e23 = e23 ∧ pact c014 e01 ≠ e01 ∧
    pact c014 e04 ≠ e04 ∧ pact c014 e14 ≠ e14 := by
  decide +kernel

theorem swap01_props : pact (Equiv.swap 0 1) e01 = e01 ∧ pact (Equiv.swap 0 1) e04 ≠ e04 := by
  decide +kernel

theorem pres014 : ∀ σ : Equiv.Perm (Fin 5), pact σ e23 = e23 → ∀ v : W5,
    (v = e01 ∨ v = e04 ∨ v = e14) → (pact σ v = e01 ∨ pact σ v = e04 ∨ pact σ v = e14) := by
  decide +kernel

theorem fix014 : ∀ σ : Equiv.Perm (Fin 5),
    (pact σ e23 = e23 ∧ pact σ e01 = e01 ∧ pact σ e04 = e04 ∧ pact σ e14 = e14) →
    σ * σ = 1 := by
  decide +kernel

theorem e014_ne : e01 ≠ e04 ∧ e01 ≠ e14 ∧ e04 ≠ e14 := by
  decide +kernel

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

@[expose] def T0e : Subgroup G := T ⊓ Subgroup.centralizer ({S.e2} : Set G)

@[expose] def G1e (H : Subgroup G) : Subgroup G := H ⊓ Subgroup.centralizer ({S.e2} : Set G)

@[expose] def G2e : Subgroup G := (L ⊔ T) ⊓ Subgroup.centralizer ({S.e2} : Set G)

include S

theorem T0_le_G1 {H : Subgroup G} (hTH : T ≤ H) : S.T0e ≤ S.G1e H :=
  inf_le_inf_right _ hTH

theorem T0_le_G2 : S.T0e ≤ S.G2e := inf_le_inf_right _ le_sup_right

theorem quotient_G1 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) {hU : IsElemAbelian 2 (S.UH H)}
    {K₁ K₂ : Subgroup (MulAut (IntMod (S.UH H) hU))} (D : S2A S H hU K₁ K₂) :
    Nonempty (↥(S.G1e H) ⧸ CFSG.Open.pCore 2 ↥(S.G1e H) ≃* Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have B := D.blocks
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  have hHN : H ≤ Subgroup.normalizer (S.UH H : Set G) := B.le_norm
  have hCU : H ⊓ Subgroup.centralizer (S.UH H : Set G) ≤ pCoreOf 2 H :=
    S.centralizer_UH_le_pCoreOf_all h331 h1222 h5172 hH hHZ hsolv
  have hP2 : IsPGroup 2 ↥(pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  have hst₁ : ∀ l ∈ K₁, ∀ u ∈ commV K₁, l u ∈ commV K₁ := fun l hl u hu => commV_stable K₁ hl hu
  have hst₂ : ∀ l ∈ K₂, ∀ u ∈ commV K₂, l u ∈ commV K₂ := fun l hl u hu => commV_stable K₂ hl hu
  obtain ⟨c₁, hc₁L, hc₁N, hc₁3, hc₁K, hc₁1⟩ := B.exists_c' hP2 hCU
  have hy₁3 : convI hU ⟨c₁, hc₁N⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c₁, hc₁N⟩ : ↥(Subgroup.normalizer (S.UH H : Set G))) ^ 3 = 1 := Subtype.ext hc₁3
    rw [this, map_one]
  obtain ⟨y₂, hy₂, hy₂3, hy₂1⟩ := S1417.exists_orderThree B.nat₂
  have hL := B.autI_twoResidual_eq hc₁K hy₁3 hc₁1 hy₂ hy₂3 hy₂1
  set ε₂ := IntMod.mk hU ⟨S.e2, D.e2_mem⟩ with hε₂
  have hε₂1 : ε₂ ≠ 1 := fun h => S.e2_ne_one (congrArg IntMod.val h)
  have hfixε : ∀ (x : G) (hxN : x ∈ Subgroup.normalizer (S.UH H : Set G)),
      x ∈ Subgroup.centralizer ({S.e2} : Set G) → convI hU ⟨x, hxN⟩ ε₂ = ε₂ := by
    intro x hxN hx
    apply IntMod.val_injective
    rw [convI_apply_val]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hx
    show x * S.e2 * x⁻¹ = S.e2
    rw [h1]; group
  have hgL : ∀ (x : G) (hxH : x ∈ H), ∀ φ ∈ autI hU (twoResidual H),
      convI hU ⟨x, hHN hxH⟩ * φ * (convI hU ⟨x, hHN hxH⟩)⁻¹ ∈ autI hU (twoResidual H) := by
    intro x hxH φ hφ
    obtain ⟨y, hy, rfl⟩ := (mem_autI hU).1 hφ
    rw [← map_inv, ← map_mul, ← map_mul]
    refine (mem_autI hU).2 ⟨_, ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H hxH) y).mp hy
  have hpres : ∀ x ∈ S.G1e H, ∀ u ∈ blk hU K₁, x * u * x⁻¹ ∈ blk hU K₁ := by
    intro x hx u hu
    have hxN := hHN hx.1
    obtain ⟨h1, -⟩ := B.preserves_of_fix hc₁K hy₁3 hc₁1 hy₂ hy₂3 hy₂1 (hgL x hx.1) D.e2_U2 hε₂1
      (hfixε x hxN hx.2)
    have := conj_mem_blk hxN hu
    obtain ⟨huU, huK⟩ := mem_blk.1 hu
    have hxu : x * u * x⁻¹ ∈ S.UH H := (Subgroup.mem_normalizer_iff.mp hxN u).mp huU
    refine mem_blk.2 ⟨hxu, ?_⟩
    have h2 := h1 _ huK
    have e : convI hU ⟨x, hxN⟩ (IntMod.mk hU ⟨u, huU⟩) = IntMod.mk hU ⟨x * u * x⁻¹, hxu⟩ := by
      apply IntMod.val_injective
      rw [convI_apply_val]; rfl
    rwa [e] at h2
  set P₁ : Set G := (blk hU K₁ : Set G) \ {1} with hP₁
  have h3 : Nat.card ↥P₁ = 3 := by
    have h4 : Nat.card ↥(blk hU K₁) = 4 := by
      rw [card_blk]; exact (S1417.card_of_actsAsNaturalL2 B.nat₁).2
    rw [hP₁, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (blk hU K₁).one_mem,
      ← Nat.card_coe_set_eq]
    rw [show Nat.card ↥(blk hU K₁ : Set G) = Nat.card ↥(blk hU K₁) from rfl, h4]
  have hP : ∀ x ∈ S.G1e H, ∀ p ∈ P₁, x * p * x⁻¹ ∈ P₁ := by
    intro x hx p hp
    refine ⟨hpres x hx p hp.1, fun h => hp.2 ?_⟩
    have h1 : x * p * x⁻¹ = 1 := h
    have : p = x⁻¹ * (x * p * x⁻¹) * x := by group
    rw [this, h1]; simp
  have hc₁H : c₁ ∈ H := twoResidual_le H hc₁L
  have hc₁G : c₁ ∈ S.G1e H := by
    refine ⟨hc₁H, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : convI hU ⟨c₁, hc₁N⟩ ε₂ = ε₂ := B.apply_eq₁ hc₁K D.e2_U2
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    have h3' : c₁ * S.e2 * c₁⁻¹ = S.e2 := h2
    calc c₁ * S.e2 = (c₁ * S.e2 * c₁⁻¹) * c₁ := by group
      _ = S.e2 * c₁ := by rw [h3']
  have hc : ∀ p ∈ P₁, c₁ * p * c₁⁻¹ ≠ p := by
    intro p hp hfix
    obtain ⟨hpU, hpK⟩ := mem_blk.1 hp.1
    apply hp.2
    have h1 : convI hU ⟨c₁, hc₁N⟩ (IntMod.mk hU ⟨p, hpU⟩) = IntMod.mk hU ⟨p, hpU⟩ := by
      apply IntMod.val_injective
      rw [convI_apply_val]
      exact hfix
    have := natL2_fix_eq_one B.nat₁ hst₁ hc₁K hy₁3 hc₁1 hpK h1
    exact congrArg IntMod.val this
  have hJH := (E2_3_two_sylow_of_isSolvable hU (S.hyp501.minParabolic_of_isHStar h331 hH).1
    hsolv (fun p hp hp2 => by
      obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
      have : Fact p.Prime := ⟨hp⟩
      have h1 := hq p hp hp2
      rwa [← pRank_top_subtype]) (conjClosure_isTwoReducedIn_of_charTwo hsyl
        (S.charTwo_of_inH hH.1) le_rfl).2.2
    (S.thompsonJ_not_le_centralizer_UH h331 h5172 hH hHZ)).2
  rw [B.eqJ] at hJH
  obtain ⟨s₁, s₂, a₁, a₂, hd⟩ :=
    S1417.exists_sylowData hJH B.nat₁ B.nat₂ B.comm B.inf B.commV_inf D.top
  obtain ⟨j₁, hj₁J, hj₁⟩ := (mem_autI hU).1 hd.s₁_mem_S
  have hj₁T : (j₁ : G) ∈ T := thompsonJ_le_self T hj₁J
  have hJV2 : ∀ v ∈ S.V2, (j₁ : G) * v * (j₁ : G)⁻¹ = v := by
    intro v hv
    have := Subgroup.mem_centralizer_iff.mp (S.thompsonJ_le_centralizer_V2 hj₁J) v hv
    rw [← this]; group
  have hj₁G : (j₁ : G) ∈ S.G1e H := by
    refine ⟨hTH hj₁T, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := hJV2 S.e2 S.e2_mem_V2
    calc (j₁ : G) * S.e2 = ((j₁ : G) * S.e2 * (j₁ : G)⁻¹) * j₁ := by group
      _ = S.e2 * j₁ := by rw [this]
  have he1P : S.e1 ∈ P₁ := ⟨mem_blk.2 ⟨D.e1_mem, D.e1_U1⟩, S.e1_ne_one⟩
  obtain ⟨u, hu, hsu⟩ : ∃ u ∈ commV K₁, s₁ u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact hd.s₁_ne (S1417.eq_one_of_forall_apply_eq B.nat₁ hst₁ hd.s₁_mem_L hcon)
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hsu (map_one s₁)
  have huP : u.val ∈ P₁ := ⟨mem_blk.2 ⟨u.val_mem, hu⟩, fun h => hu1 (IntMod.val_injective h)⟩
  have hju : (j₁ : G) * u.val * (j₁ : G)⁻¹ ≠ u.val := by
    intro h
    apply hsu
    apply IntMod.val_injective
    rw [← hj₁, convI_apply_val]
    exact h
  have hker : ∀ x ∈ S.G1e H, (∀ p ∈ P₁, x * p * x⁻¹ = p) → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx hxP
    obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, ?_⟩
    set y := x ^ 2 ^ a with hy
    have hyG : y ∈ S.G1e H := Subgroup.pow_mem _ hx _
    have hyN := hHN hyG.1
    have hyodd : Odd (orderOf y) := by
      have h2a : (2 ^ a : ℕ) ≠ 0 := by positivity
      rw [hy, orderOf_pow' _ h2a, ham, Nat.gcd_mul_right_left,
        Nat.mul_div_cancel_left _ (by positivity)]
      exact hm
    have hyP : ∀ p ∈ P₁, y * p * y⁻¹ = p := by
      intro p hp
      have key : ∀ n : ℕ, x ^ n * p * (x ^ n)⁻¹ = p := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          calc x ^ (n + 1) * p * (x ^ (n + 1))⁻¹ = x ^ n * (x * p * x⁻¹) * (x ^ n)⁻¹ := by
                rw [pow_succ]; group
            _ = p := by rw [hxP p hp, ih]
      exact key _
    have hφodd : Odd (orderOf (convI hU ⟨y, hyN⟩)) :=
      Odd.of_dvd_nat hyodd ((orderOf_map_dvd _ _).trans (by rw [Subgroup.orderOf_mk]))
    have hφL := mem_autI_twoResidual_of_odd hU (convI_mem_autI hU hyG.1 hyN) hφodd
    rw [hL] at hφL
    have hcz : ∀ a ∈ Subgroup.zpowers (convI hU ⟨c₁, hc₁N⟩), ∀ b ∈ Subgroup.zpowers y₂,
        a * b = b * a := fun a ha b hb =>
      B.comm a ((Subgroup.zpowers_le).2 hc₁K ha) b ((Subgroup.zpowers_le).2 hy₂ hb)
    obtain ⟨p, hp, q, hq, hpq⟩ := S1417.exists_mul_of_mem_sup_of_commute hcz hφL
    have hpK : p ∈ K₁ := (Subgroup.zpowers_le).2 hc₁K hp
    have hqK : q ∈ K₂ := (Subgroup.zpowers_le).2 hy₂ hq
    have hp3 : p ^ 3 = 1 := by
      obtain ⟨i, rfl⟩ := hp
      simp only
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy₁3, one_zpow]
    have hq3 : q ^ 3 = 1 := by
      obtain ⟨i, rfl⟩ := hq
      simp only
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy₂3, one_zpow]
    have hp1 : p = 1 := by
      by_contra hp1
      apply hu1
      have h1 : p u = u := by
        have h2 : (p * q) u = u := by
          rw [hpq]
          apply IntMod.val_injective
          rw [convI_apply_val]
          exact hyP u.val huP
        rwa [MulAut.mul_apply, B.apply_eq₂ hqK hu] at h2
      exact natL2_fix_eq_one B.nat₁ hst₁ hpK hp3 hp1 hu h1
    have hq1 : q = 1 := by
      by_contra hq1
      apply hε₂1
      have h1 : q ε₂ = ε₂ := by
        have h2 : (p * q) ε₂ = ε₂ := by rw [hpq]; exact hfixε y hyN hyG.2
        rwa [hp1, one_mul] at h2
      exact natL2_fix_eq_one B.nat₂ hst₂ hqK hq3 hq1 D.e2_U2 h1
    rw [hp1, hq1, one_mul] at hpq
    have hyU : y ∈ pCoreOf 2 H := hCU ⟨hyG.1, (convI_eq_one_iff hU _).1 hpq.symm⟩
    obtain ⟨k, hk⟩ := hP2 ⟨y, hyU⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hym : y ^ orderOf y = 1 := pow_orderOf_eq_one y
    exact eq_one_of_pow_coprime hk' hym (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hyodd))
  exact quotient_pCore_equiv_perm3_of_conjPerm h3 hP hc₁G hc hj₁G he1P (hJV2 S.e1 S.e1_mem_V2)
    huP hju hker


@[expose] noncomputable def v04 : G := (S.frame.ψ.symm e04 : G)

@[expose] noncomputable def v14 : G := (S.frame.ψ.symm e14 : G)

theorem v04_mem_V : S.v04 ∈ V := (S.frame.ψ.symm e04).2

theorem v14_mem_V : S.v14 ∈ V := (S.frame.ψ.symm e14).2

theorem psi_v04 : S.frame.ψ ⟨S.v04, S.v04_mem_V⟩ = e04 := by
  have : (⟨S.v04, S.v04_mem_V⟩ : ↥V) = S.frame.ψ.symm e04 := Subtype.ext rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem psi_v14 : S.frame.ψ ⟨S.v14, S.v14_mem_V⟩ = e14 := by
  have : (⟨S.v14, S.v14_mem_V⟩ : ↥V) = S.frame.ψ.symm e14 := Subtype.ext rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem mem_P2_iff {x : G} (hx : x ∈ V) :
    (x = S.e1 ∨ x = S.v04 ∨ x = S.v14) ↔
      (S.frame.ψ ⟨x, hx⟩ = e01 ∨ S.frame.ψ ⟨x, hx⟩ = e04 ∨ S.frame.ψ ⟨x, hx⟩ = e14) := by
  have key : ∀ (y : G) (hy : y ∈ V) (w : W5), S.frame.ψ ⟨y, hy⟩ = w →
      (x = y ↔ S.frame.ψ ⟨x, hx⟩ = w) := by
    intro y hy w hw
    constructor
    · rintro rfl; exact hw
    · intro h
      have := S.frame.ψ.injective (h.trans hw.symm)
      exact congrArg Subtype.val this
  rw [key _ S.e1_mem_V e01 S.psi_e1, key _ S.v04_mem_V e04 S.psi_v04,
    key _ S.v14_mem_V e14 S.psi_v14]

theorem quotient_G2 (h5172 : Stmt5_1_7_two) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    Nonempty (↥S.G2e ⧸ CFSG.Open.pCore 2 ↥S.G2e ≃* Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le
  set P₂ : Set G := {S.e1, S.v04, S.v14} with hP₂
  have hmem : ∀ x : G, x ∈ P₂ ↔ (x = S.e1 ∨ x = S.v04 ∨ x = S.v14) := by
    intro x
    simp [hP₂]
  have hP₂V : ∀ x ∈ P₂, x ∈ V := by
    intro x hx
    rcases (hmem x).1 hx with rfl | rfl | rfl
    · exact S.e1_mem_V
    · exact S.v04_mem_V
    · exact S.v14_mem_V
  have h3 : Nat.card ↥P₂ = 3 := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_three]
    obtain ⟨n1, n2, n3⟩ := e014_ne
    refine ⟨S.e1, S.v04, S.v14, fun h => n1 ?_, fun h => n2 ?_, fun h => n3 ?_, rfl⟩
    · rw [← S.psi_e1, ← S.psi_v04]; congr 1; exact Subtype.ext h
    · rw [← S.psi_e1, ← S.psi_v14]; congr 1; exact Subtype.ext h
    · rw [← S.psi_v04, ← S.psi_v14]; congr 1; exact Subtype.ext h
  have hρ23 : ∀ (g : G) (hg : g ∈ S.G2e), pact (S.frame.ρ ⟨g, hLTN hg.1⟩) e23 = e23 := by
    intro g hg
    have h1 := (S.conj_eq_iff ⟨g, hLTN hg.1⟩ ⟨S.e2, S.e2_mem_V⟩).1 (by
      have := Subgroup.mem_centralizer_singleton_iff.mp hg.2
      show g * S.e2 * g⁻¹ = S.e2
      rw [this]; group)
    rwa [S.psi_e2] at h1
  have hconjψ : ∀ (g : G) (hg : g ∈ L ⊔ T) (x : G) (hx : x ∈ V),
      S.frame.ψ ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hLTN hg) x).mp hx⟩ =
        pact (S.frame.ρ ⟨g, hLTN hg⟩) (S.frame.ψ ⟨x, hx⟩) := fun g hg x hx =>
    S.psi_conj ⟨g, hLTN hg⟩ ⟨x, hx⟩
  have hP : ∀ g ∈ S.G2e, ∀ p ∈ P₂, g * p * g⁻¹ ∈ P₂ := by
    intro g hg p hp
    have hpV := hP₂V p hp
    have hgp : g * p * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLTN hg.1) p).mp hpV
    rw [hmem, S.mem_P2_iff hgp, hconjψ g hg.1 p hpV]
    exact pres014 _ (hρ23 g hg) _ ((S.mem_P2_iff hpV).1 ((hmem p).1 hp))
  obtain ⟨l, hlL, hl⟩ := (S.frame.image_L c014).2 c014_props.1
  have hlLT : (l : G) ∈ L ⊔ T := Subgroup.mem_sup_left hlL
  have hlG : (l : G) ∈ S.G2e := by
    refine ⟨hlLT, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := (S.conj_eq_iff l ⟨S.e2, S.e2_mem_V⟩).2 (by rw [S.psi_e2, hl]; exact c014_props.2.1)
    have h2 : (l : G) * S.e2 * (l : G)⁻¹ = S.e2 := h1
    calc (l : G) * S.e2 = ((l : G) * S.e2 * (l : G)⁻¹) * l := by group
      _ = S.e2 * l := by rw [h2]
  have hc : ∀ p ∈ P₂, (l : G) * p * (l : G)⁻¹ ≠ p := by
    intro p hp hfix
    have hpV := hP₂V p hp
    have h1 := hconjψ l hlLT p hpV
    have e : (⟨(l : G) * p * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLTN hlLT) p).mp hpV⟩ :
        ↥V) = ⟨p, hpV⟩ := Subtype.ext hfix
    rw [e, show (⟨(l : G), hLTN hlLT⟩ : ↥(Subgroup.normalizer (V : Set G))) = l from rfl,
      hl] at h1
    rcases (S.mem_P2_iff hpV).1 ((hmem p).1 hp) with h | h | h
    · rw [h] at h1; exact c014_props.2.2.1 h1.symm
    · rw [h] at h1; exact c014_props.2.2.2.1 h1.symm
    · rw [h] at h1; exact c014_props.2.2.2.2 h1.symm
  obtain ⟨⟨j, hjJ, hjN, hj⟩, -⟩ :=
    S.lemma_13_2_4_two_b (S.thompsonJ_not_le_centralizer h5172 hH hHZ)
  have hjT : j ∈ T := thompsonJ_le_self T hjJ
  have hjLT : j ∈ L ⊔ T := Subgroup.mem_sup_right hjT
  have hJV2 : ∀ v ∈ S.V2, j * v * j⁻¹ = v := by
    intro v hv
    have := Subgroup.mem_centralizer_iff.mp (S.thompsonJ_le_centralizer_V2 hjJ) v hv
    rw [← this]; group
  have hjG : j ∈ S.G2e := by
    refine ⟨hjLT, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := hJV2 S.e2 S.e2_mem_V2
    calc j * S.e2 = (j * S.e2 * j⁻¹) * j := by group
      _ = S.e2 * j := by rw [this]
  have he1P : S.e1 ∈ P₂ := (hmem _).2 (Or.inl rfl)
  have hv04P : S.v04 ∈ P₂ := (hmem _).2 (Or.inr (Or.inl rfl))
  have hjv : j * S.v04 * j⁻¹ ≠ S.v04 := by
    intro hfix
    have h1 := hconjψ j hjLT S.v04 S.v04_mem_V
    have e : (⟨j * S.v04 * j⁻¹, (Subgroup.mem_normalizer_iff.mp (hLTN hjLT) S.v04).mp
        S.v04_mem_V⟩ : ↥V) = ⟨S.v04, S.v04_mem_V⟩ := Subtype.ext hfix
    rw [e, S.psi_v04, show (⟨j, hLTN hjLT⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨j, hjN⟩
      from rfl, hj] at h1
    exact swap01_props.2 h1.symm
  have hker : ∀ x ∈ S.G2e, (∀ p ∈ P₂, x * p * x⁻¹ = p) → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx hxP
    have hfixv : ∀ (v : G) (hv : v ∈ V), v ∈ P₂ →
        pact (S.frame.ρ ⟨x, hLTN hx.1⟩) (S.frame.ψ ⟨v, hv⟩) = S.frame.ψ ⟨v, hv⟩ := by
      intro v hv hvP
      exact (S.conj_eq_iff ⟨x, hLTN hx.1⟩ ⟨v, hv⟩).1 (hxP v hvP)
    have hsq := fix014 (S.frame.ρ ⟨x, hLTN hx.1⟩) ⟨hρ23 x hx,
      by have := hfixv S.e1 S.e1_mem_V he1P; rwa [S.psi_e1] at this,
      by have := hfixv S.v04 S.v04_mem_V hv04P; rwa [S.psi_v04] at this,
      by have := hfixv S.v14 S.v14_mem_V ((hmem _).2 (Or.inr (Or.inr rfl)));
         rwa [S.psi_v14] at this⟩
    have hx2 : S.frame.ρ (⟨x, hLTN hx.1⟩ * ⟨x, hLTN hx.1⟩) = 1 := by rw [map_mul]; exact hsq
    have hx2C := S.frame.mem_centralizer_of_rho _ hx2
    have hx2Q : x * x ∈ pCoreOf 2 (L ⊔ T) := by
      rw [← S.cLT]; exact ⟨(L ⊔ T).mul_mem hx.1 hx.1, hx2C⟩
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (L ⊔ T) ⟨x * x, hx2Q⟩
    refine ⟨k + 1, ?_⟩
    have hk' : (x * x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [pow_succ', pow_mul, sq]
    exact hk'
  exact quotient_pCore_equiv_perm3_of_conjPerm h3 hP hlG hc hjG he1P
    (hJV2 S.e1 S.e1_mem_V2) hv04P hjv hker

theorem goldschmidt_triple (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) (h5172 : Stmt5_1_7_two) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) {hU : IsElemAbelian 2 (S.UH H)}
    {K₁ K₂ : Subgroup (MulAut (IntMod (S.UH H) hU))} (D : S2A S H hU K₁ K₂) :
    F6.IsGoldschmidtTripleIn (S.G1e H ⊔ S.G2e) (S.G1e H) S.G2e ∧ S.G1e H ⊓ S.G2e = S.T0e := by
  have hTH : T ≤ H := hH.1.1
  have hinf : S.G1e H ⊓ S.G2e = S.T0e := by
    apply le_antisymm
    · intro x hx
      have hxM : x ∈ H ⊓ Subgroup.normalizer (L : Set G) :=
        ⟨hx.1.1, sup_le Subgroup.le_normalizer S.T_le_NL hx.2.1⟩
      rw [S.inf_M_eq_T h331 h1222 h5172 hH hHZ hsolv D.blocks D.top] at hxM
      exact ⟨hxM, hx.1.2⟩
    · exact le_inf (S.T0_le_G1 hTH) S.T0_le_G2
  refine ⟨⟨rfl, S.quotient_G1 h331 h1222 h5172 hH hHZ hsolv D, S.quotient_G2 h5172 hH hHZ, ?_⟩,
    hinf⟩
  rw [hinf]
  have hsyl := S.isSylowTwoOf_centralizer h1222 h517 S.e2_mem_V2 S.e2_not_mem_V1
  have hle : S.G1e H ⊔ S.G2e ≤ Subgroup.centralizer ({S.e2} : Set G) :=
    sup_le inf_le_right inf_le_right
  have hT0 : S.T0e ≤ S.G1e H ⊔ S.G2e := (S.T0_le_G1 hTH).trans le_sup_left
  refine ⟨hT0, hsyl.2.1, fun h2 => hsyl.2.2 ?_⟩
  change 2 ∣ S.T0e.relIndex (Subgroup.centralizer ({S.e2} : Set G))
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hT0 hle]
  exact Dvd.dvd.mul_right h2 _

end Setting

end CFSG.Quasithin.H13.A5
