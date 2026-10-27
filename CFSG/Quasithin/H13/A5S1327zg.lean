module

public import CFSG.Quasithin.H13.A5S1327za

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

theorem perm3_trivial_of_conj_inv : ∀ σ τ : Equiv.Perm (Fin 3),
    (σ ^ 3 = 1 ∧ σ ≠ 1 ∧ τ ^ 2 = 1 ∧ (τ * (σ * τ * σ⁻¹)) ^ 2 = 1) → τ = 1 := by
  decide +kernel

theorem perm3_sq_of_pow_two_pow (τ : Equiv.Perm (Fin 3)) {k : ℕ} (h : τ ^ 2 ^ k = 1) :
    τ ^ 2 = 1 := by
  have h1 : orderOf τ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h6 : orderOf τ ∣ 2 * 3 := by
    have := orderOf_dvd_natCard τ
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at this
    exact this
  have hcop : Nat.Coprime (orderOf τ) 3 :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k (by decide))
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right h6)

section Three

variable {G : Type} [Group G]

theorem fix_of_normal_two [Finite G] {X : Subgroup G} {P : Set G} (h3 : Nat.card ↥P = 3)
    (hP : ∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P) {c : G} (hcX : c ∈ X)
    (hc : ∀ p ∈ P, c * p * c⁻¹ ≠ p) {N : Subgroup G} (hNX : N ≤ X) (hN2 : IsPGroup 2 ↥N)
    (hcN : ∀ q ∈ N, c * q * c⁻¹ ∈ N) : ∀ q ∈ N, ∀ p ∈ P, q * p * q⁻¹ = p := by
  classical
  set e : ↥P ≃ Fin 3 := (Finite.equivFin ↥P).trans (finCongr h3) with he
  set F : ↥X →* Equiv.Perm (Fin 3) := (Equiv.permCongrHom e).toMonoidHom.comp (conjPerm hP)
    with hF
  have hFapp : ∀ (x : ↥X) (i : Fin 3), F x i = e (conjPerm hP x (e.symm i)) := fun x i => rfl
  have hfix : ∀ (x : ↥X) (i : Fin 3), F x i = i ↔
      (x : G) * (e.symm i : G) * (x : G)⁻¹ = (e.symm i : G) := by
    intro x i
    rw [hFapp]
    constructor
    · intro h
      have h1 := congrArg e.symm h
      rw [Equiv.symm_apply_apply] at h1
      exact congrArg Subtype.val h1
    · intro h
      have h1 : conjPerm hP x (e.symm i) = e.symm i := Subtype.ext h
      rw [h1, Equiv.apply_symm_apply]
  have hFc : F ⟨c, hcX⟩ ^ 3 = 1 ∧ F ⟨c, hcX⟩ ≠ 1 := by
    refine perm3_fpf _ fun i h => ?_
    exact hc _ (e.symm i).2 ((hfix _ i).1 h)
  have hsq : ∀ q (hq : q ∈ N), F ⟨q, hNX hq⟩ ^ 2 = 1 := by
    intro q hq
    obtain ⟨k, hk⟩ := hN2 ⟨q, hq⟩
    refine perm3_sq_of_pow_two_pow _ (k := k) ?_
    rw [← map_pow]
    have : (⟨q, hNX hq⟩ : ↥X) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  intro q hq p hp
  have hq' : c * q * c⁻¹ ∈ N := hcN q hq
  have hqq : q * (c * q * c⁻¹) ∈ N := N.mul_mem hq hq'
  have h1 := hsq _ hqq
  have e1 : F ⟨q * (c * q * c⁻¹), hNX hqq⟩ =
      F ⟨q, hNX hq⟩ * (F ⟨c, hcX⟩ * F ⟨q, hNX hq⟩ * (F ⟨c, hcX⟩)⁻¹) := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]; rfl
  rw [e1] at h1
  have hτ := perm3_trivial_of_conj_inv _ _ ⟨hFc.1, hFc.2, hsq q hq, h1⟩
  have := (hfix ⟨q, hNX hq⟩ (e ⟨p, hp⟩)).1 (by rw [hτ]; rfl)
  simpa using this

end Three

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem exists_side1 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) {hU : IsElemAbelian 2 (S.UH H)}
    {K₁ K₂ : Subgroup (MulAut (IntMod (S.UH H) hU))} (D : S2A S H hU K₁ K₂) :
    ∃ c₁ ∈ twoResidual H, ∃ hc₁N : c₁ ∈ Subgroup.normalizer (S.UH H : Set G),
      c₁ ^ 3 = 1 ∧ convI hU ⟨c₁, hc₁N⟩ ∈ K₁ ∧ convI hU ⟨c₁, hc₁N⟩ ≠ 1 ∧ c₁ ∈ S.G1e H ∧
      S.G1e H ≤ Subgroup.normalizer (blk hU K₁ : Set G) ∧
      (∀ q ∈ pCoreOf 2 (S.G1e H), ∀ u ∈ blk hU K₁, q * u = u * q) ∧
      ∃ j ∈ S.T0e, ∃ u ∈ blk hU K₁, j * u * j⁻¹ ≠ u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have B := D.blocks
  have hHN : H ≤ Subgroup.normalizer (S.UH H : Set G) := B.le_norm
  have hCU : H ⊓ Subgroup.centralizer (S.UH H : Set G) ≤ pCoreOf 2 H :=
    S.centralizer_UH_le_pCoreOf_all h331 h1222 h5172 hH hHZ hsolv
  have hP2 : IsPGroup 2 ↥(pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  have hst₁ : ∀ l ∈ K₁, ∀ u ∈ commV K₁, l u ∈ commV K₁ := fun l hl u hu => commV_stable K₁ hl hu
  obtain ⟨c₁, hc₁L, hc₁N, hc₁3, hc₁K, hc₁1⟩ := B.exists_c' hP2 hCU
  have hy₁3 : convI hU ⟨c₁, hc₁N⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c₁, hc₁N⟩ : ↥(Subgroup.normalizer (S.UH H : Set G))) ^ 3 = 1 := Subtype.ext hc₁3
    rw [this, map_one]
  obtain ⟨y₂, hy₂, hy₂3, hy₂1⟩ := S1417.exists_orderThree B.nat₂
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
    obtain ⟨huU, huK⟩ := mem_blk.1 hu
    have hxu : x * u * x⁻¹ ∈ S.UH H := (Subgroup.mem_normalizer_iff.mp hxN u).mp huU
    refine mem_blk.2 ⟨hxu, ?_⟩
    have h2 := h1 _ huK
    have e : convI hU ⟨x, hxN⟩ (IntMod.mk hU ⟨u, huU⟩) = IntMod.mk hU ⟨x * u * x⁻¹, hxu⟩ := by
      apply IntMod.val_injective
      rw [convI_apply_val]; rfl
    rwa [e] at h2
  have hNU : S.G1e H ≤ Subgroup.normalizer (blk hU K₁ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨hpres g hg u, fun h => ?_⟩
    have := hpres g⁻¹ ((S.G1e H).inv_mem hg) _ h
    simpa [mul_assoc] using this
  have hc₁H : c₁ ∈ H := twoResidual_le H hc₁L
  have hc₁G : c₁ ∈ S.G1e H := by
    refine ⟨hc₁H, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : convI hU ⟨c₁, hc₁N⟩ ε₂ = ε₂ := B.apply_eq₁ hc₁K D.e2_U2
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    have h3' : c₁ * S.e2 * c₁⁻¹ = S.e2 := h2
    calc c₁ * S.e2 = (c₁ * S.e2 * c₁⁻¹) * c₁ := by group
      _ = S.e2 * c₁ := by rw [h3']
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
  have hfixN := fix_of_normal_two h3 hP hc₁G hc (pCoreOf_le 2 _) (pCoreOf_isPGroup 2 _)
    (fun q hq => (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (S.G1e H) hc₁G) q).mp
      hq)
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
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
  have hj₁T0 : (j₁ : G) ∈ S.T0e := by
    refine ⟨hj₁T, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := Subgroup.mem_centralizer_iff.mp (S.thompsonJ_le_centralizer_V2 hj₁J) S.e2
      S.e2_mem_V2
    exact this.symm
  obtain ⟨u, hu, hsu⟩ : ∃ u ∈ commV K₁, s₁ u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact hd.s₁_ne (S1417.eq_one_of_forall_apply_eq B.nat₁ hst₁ hd.s₁_mem_L hcon)
  have hju : (j₁ : G) * u.val * (j₁ : G)⁻¹ ≠ u.val := by
    intro h
    apply hsu
    apply IntMod.val_injective
    rw [← hj₁, convI_apply_val]
    exact h
  refine ⟨c₁, hc₁L, hc₁N, hc₁3, hc₁K, hc₁1, hc₁G, hNU, fun q hq u hu => ?_,
    j₁, hj₁T0, u.val, mem_blk.2 ⟨u.val_mem, hu⟩, hju⟩
  by_cases hu1 : u = 1
  · rw [hu1]; group
  · have := hfixN q hq u ⟨hu, hu1⟩
    calc q * u = (q * u * q⁻¹) * q := by group
      _ = u * q := by rw [this]

end Setting

end CFSG.Quasithin.H13.A5
