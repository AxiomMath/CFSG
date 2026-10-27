module

public import CFSG.Quasithin.Vol2.Ch12Sec6L20d

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c S126FE S126N S126L19 S126L19b S126L19d S126L20 S126L20a S126L20b S126L20c
  S126L20d Equiv
open scoped IsMulCommutative commutatorElement

namespace S126L20e

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem conjAct_eq_of_actsAs (F : Frame126 T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {x x' : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hx' : x' ∈ Subgroup.normalizer (V : Set G))
    {σ : Perm (Fin 8)} (h : ActsAs F x σ) (h' : ActsAs F x' σ) :
    conjAct V ⟨x, hx⟩ = conjAct V ⟨x', hx'⟩ :=
  MulEquiv.ext fun v => beta_inj F hZ ((h v _ rfl).trans (h' v _ rfl).symm)

omit [Finite G] [IsMulCommutative ↥V] in
theorem mem_normalizer_of_centralizes {U : Subgroup G} {l : G}
    (h : ∀ u ∈ U, l * u * l⁻¹ = u) : l ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [h n hn]
    exact hn
  · intro hn
    have h1 := h _ hn
    have h2 : l * n * l⁻¹ = n := by
      calc l * n * l⁻¹ = l⁻¹ * (l * (l * n * l⁻¹) * l⁻¹) * l := by group
        _ = l⁻¹ * (l * n * l⁻¹) * l := by rw [h1]
        _ = n := by group
    rw [← h2]
    exact hn

omit [Finite G] [IsMulCommutative ↥V] in
theorem maps_U {U : Subgroup G} {x : MulAut ↥V}
    (hx : x ∈ autOn (L ⊓ Subgroup.normalizer (U : Set G)) V) {v : ↥V} (hv : (v : G) ∈ U) :
    ((x v : ↥V) : G) ∈ U := by
  obtain ⟨l, hl, ⟨-, hlU⟩, rfl⟩ := mem_autOn_iff_exists.mp hx
  exact (Subgroup.mem_normalizer_iff.1 hlU v).1 hv

theorem rho0_conj' : ∀ k : Fin 8, rho0⁻¹ * xt k * rho0 = xt (rho0⁻¹ k) := by
  decide

theorem rho0_fixD_iff {z : D8} : z ∈ fixD B0 ↔ dAct rho0 z ∈ fixD B0 := by
  constructor
  · intro hz
    rw [mem_fixD]
    rintro _ ⟨k, rfl⟩
    have h1 := (mem_fixD.1 hz) _ (xt_mem (rho0⁻¹ k))
    have e : xt k * rho0 = rho0 * xt (rho0⁻¹ k) := by
      rw [← rho0_conj']
      group
    rw [← dAct_mul, e, dAct_mul, h1]
  · intro hz
    rw [mem_fixD]
    rintro _ ⟨k, rfl⟩
    have h1 := (mem_fixD.1 hz) _ (xt_mem (rho0 k))
    have e : xt (rho0 k) * rho0 = rho0 * xt k := by
      rw [← rho0_conj]
      group
    rw [← dAct_mul, e, dAct_mul] at h1
    have h2 := congrArg (dAct rho0⁻¹) h1
    rwa [dAct_inv_dAct, dAct_inv_dAct] at h2

section Main

variable (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
  (F : Frame126 T L V) (hH : Hyp126 G T L V)
  (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
  {g : G} (hg : Hyp4 V g)

include h1262 hfus in
theorem mem_U_iff (v : ↥V) :
    (v : G) ∈ V ⊓ conjSubgroup V g ↔ F.β v ∈ fixD (permGrp h331 h1222 F hH hg) := by
  rw [inter_eq h331 h1222 h1262 F hH hfus hg]
  exact ⟨fun h => (mem_centralizer_iff F hH _ _ (bot_of_hyp4 h331 h1222 h1262 F hH hfus hg) v).1
    h.2, fun h => ⟨v.2, (mem_centralizer_iff F hH _ _
      (bot_of_hyp4 h331 h1222 h1262 F hH hfus hg) v).2 h⟩⟩

include h331 h1222 h1262 F hH hfus hg in
theorem autOn_le :
    autOn (conjSubgroup V g) V ≤
      autOn (L ⊓ Subgroup.normalizer ((V ⊓ conjSubgroup V g : Subgroup G) : Set G)) V := by
  have hZ := bot_of_hyp4 h331 h1222 h1262 F hH hfus hg
  intro a ha
  obtain ⟨y, hyN, hy, rfl⟩ := mem_autOn_iff_exists.mp ha
  have hyL := hg.le_M h331 h1222 F hH hy
  have hσ := actsAs_perm8 F hH hyL hyN
  set σ := perm8 F hH hyL hyN with hσdef
  have hσB : σ ∈ permGrp h331 h1222 F hH hg := (mem_permGrp h331 h1222 F hH hg).2 ⟨y, hy, hσ⟩
  obtain ⟨τ, hτ⟩ := exists_conj h331 h1222 h1262 F hH hfus hg
  have hσA : σ ∈ alternatingGroup (Fin 8) := by
    have h1 : τ⁻¹ * σ * τ ∈ alternatingGroup (Fin 8) := B0_le_A8 ((hτ σ).1 hσB)
    have h2 := (inferInstance : (alternatingGroup (Fin 8)).Normal).conj_mem _ h1 τ
    rwa [show τ * (τ⁻¹ * σ * τ) * τ⁻¹ = σ by group] at h2
  obtain ⟨l, hl, hlL, hla⟩ := mem_autOn_iff_exists.mp (F.π ⟨σ, hσA⟩).2
  have hlσ : ActsAs F l σ := actsAs_of_pi F hl ⟨σ, hσA⟩ hla
  have heq : conjAct V ⟨l, hl⟩ = conjAct V ⟨y, hyN⟩ := conjAct_eq_of_actsAs F hZ hl hyN hlσ hσ
  rw [← heq]
  refine mem_autOn_iff_exists.mpr ⟨l, hl, ⟨hlL, mem_normalizer_of_centralizes fun u hu => ?_⟩, rfl⟩
  have h1 := congrArg (fun a : MulAut ↥V => ((a ⟨u, hu.1⟩ : ↥V) : G)) heq
  change l * u * l⁻¹ = y * u * y⁻¹ at h1
  rw [h1, conj_comm hy hu.2]
  group

include h331 h1222 h1262 F hH hfus hg in
theorem mem_autOn_of_fix {x : MulAut ↥V}
    (hx : x ∈ autOn (L ⊓ Subgroup.normalizer ((V ⊓ conjSubgroup V g : Subgroup G) : Set G)) V)
    (hfix : ∀ v : ↥V, (v : G) ∈ V ⊓ conjSubgroup V g → x v = v) :
    x ∈ autOn (conjSubgroup V g) V := by
  have hZ := bot_of_hyp4 h331 h1222 h1262 F hH hfus hg
  obtain ⟨l, hl, ⟨hlL, -⟩, rfl⟩ := mem_autOn_iff_exists.mp hx
  have hlLN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hlL
  have hσ := actsAs_perm8 F hH hlLN hl
  set σ := perm8 F hH hlLN hl with hσdef
  obtain ⟨τ, hτ⟩ := exists_conj h331 h1222 h1262 F hH hfus hg
  have hfixB : ∀ y ∈ fixD (permGrp h331 h1222 F hH hg), dAct σ y = y := by
    intro y hy
    obtain ⟨v, rfl⟩ := F.β_surj y
    have hvU := (mem_U_iff h331 h1222 h1262 F hH hfus hg v).2 hy
    have h2 := hσ v (conjAct V ⟨l, hl⟩ v) rfl
    rw [← h2, hfix v hvU]
  have hσ0 : τ⁻¹ * σ * τ ∈ B0 := mem_B0_of_fix fun y₀ hy₀ => by
    have h1 : dAct τ y₀ ∈ fixD (permGrp h331 h1222 F hH hg) :=
      (mem_fixD_iff hτ).2 (by rw [dAct_inv_dAct]; exact hy₀)
    rw [dAct_mul, dAct_mul, hfixB _ h1, dAct_inv_dAct]
  obtain ⟨y, hy, hyσ⟩ := (mem_permGrp h331 h1222 F hH hg).1 ((hτ σ).2 hσ0)
  have hyN := hg.le_normalizer hy
  rw [conjAct_eq_of_actsAs F hZ hl hyN hσ hyσ]
  exact mem_autOn_iff_exists.mpr ⟨y, hyN, hy, rfl⟩

omit [Finite G] in
theorem autOn_fix {a : MulAut ↥V} (ha : a ∈ autOn (conjSubgroup V g) V) (v : ↥V)
    (hv : (v : G) ∈ V ⊓ conjSubgroup V g) : a v = v := by
  obtain ⟨y, hyN, hy, rfl⟩ := mem_autOn_iff_exists.mp ha
  apply Subtype.ext
  change y * v * y⁻¹ = v
  rw [conj_comm hy hv.2]
  group

include h331 h1222 h1262 F hH hfus hg in
theorem autOn_eq :
    autOn (conjSubgroup V g) V = pCoreOf 2
      (autOn (L ⊓ Subgroup.normalizer ((V ⊓ conjSubgroup V g : Subgroup G) : Set G)) V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := bot_of_hyp4 h331 h1222 h1262 F hH hfus hg
  set U := V ⊓ conjSubgroup V g with hUdef
  set X := autOn (L ⊓ Subgroup.normalizer (U : Set G)) V with hXdef
  set A := autOn (conjSubgroup V g) V with hAdef
  have hAX : A ≤ X := autOn_le h331 h1222 h1262 F hH hfus hg
  have key : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
    intro x hx a ha
    refine mem_autOn_of_fix h331 h1222 h1262 F hH hfus hg
      (X.mul_mem (X.mul_mem hx (hAX ha)) (X.inv_mem hx)) fun v hv => ?_
    have h1 : (((x⁻¹ : MulAut ↥V) v : ↥V) : G) ∈ U := maps_U (X.inv_mem hx) hv
    rw [MulAut.mul_apply, MulAut.mul_apply, autOn_fix ha _ h1, ← MulAut.mul_apply,
      mul_inv_cancel, MulAut.one_apply]
  have hnorm : X ≤ Subgroup.normalizer (A : Set (MulAut ↥V)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨key x hx a, fun h => ?_⟩
    have h1 := key x⁻¹ (X.inv_mem hx) _ h
    rwa [show x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a by group] at h1
  have hA2 : IsPGroup 2 A := by
    have hV : Nat.card V = 64 := by rw [card_V F, hZ, Subgroup.card_bot]
    have h1 : IsPGroup 2 (conjSubgroup V g) :=
      IsPGroup.of_card (n := 6) (by rw [E3.card_conjSubgroup, hV]; norm_num)
    have h2 : IsPGroup 2 ((conjSubgroup V g).subgroupOf (Subgroup.normalizer (V : Set G))) :=
      h1.of_equiv (Subgroup.subgroupOfEquivOfLe hg.le_normalizer).symm
    exact h2.map (conjAct V)
  refine le_antisymm (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hAX hnorm hA2) ?_
  set P := pCoreOf 2 X with hPdef
  have hPX : P ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXP : X ≤ Subgroup.normalizer (P : Set (MulAut ↥V)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hUV : U ≤ V := inf_le_left
  let S := {u : ↥U // u ≠ 1}
  let _ : MulAction ↥P S :=
    { smul := fun p u => ⟨⟨(((p : MulAut ↥V) ⟨u.1, hUV u.1.2⟩ : ↥V) : G),
          maps_U (hPX p.2) u.1.2⟩, by
        intro h
        apply u.2
        have h1 : (p : MulAut ↥V) ⟨u.1, hUV u.1.2⟩ = 1 :=
          Subtype.ext (congrArg (fun w : ↥U => (w : G)) h)
        rw [MulEquiv.map_eq_one_iff] at h1
        exact Subtype.ext (congrArg (fun w : ↥V => (w : G)) h1)⟩
      one_smul := fun u => Subtype.ext (Subtype.ext rfl)
      mul_smul := fun p q u => Subtype.ext (Subtype.ext rfl) }
  have hU8 : Nat.card U = 8 := card_inter h331 h1222 h1262 F hH hfus hg
  have hS : Nat.card S = 7 := by
    classical
    have : Fintype ↥U := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {u : ↥U // ¬ (u = 1)} = 7
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hU8]
  obtain ⟨u₀, hu₀⟩ := hP2.nonempty_fixed_point_of_prime_not_dvd_card S (by rw [hS]; decide)
  set w₀ : ↥V := ⟨u₀.1, hUV u₀.1.2⟩ with hw₀
  have hw₀fix : ∀ p ∈ P, (p : MulAut ↥V) w₀ = w₀ := by
    intro p hp
    have h1 := (MulAction.mem_fixedPoints.1 hu₀) ⟨p, hp⟩
    exact Subtype.ext (congrArg (fun s : S => ((s.1 : ↥U) : G)) h1)
  have hw₀U : (w₀ : G) ∈ U := u₀.1.2
  have hw₀1 : w₀ ≠ 1 := fun h => u₀.2 (Subtype.ext (congrArg (fun w : ↥V => (w : G)) h))
  obtain ⟨τ, hτ⟩ := exists_conj h331 h1222 h1262 F hH hfus hg
  set ρ := τ * rho0 * τ⁻¹ with hρ
  have hρA : ρ ∈ alternatingGroup (Fin 8) :=
    (inferInstance : (alternatingGroup (Fin 8)).Normal).conj_mem _ rho0_mem_A8 τ
  obtain ⟨l, hl, hlL, hla⟩ := mem_autOn_iff_exists.mp (F.π ⟨ρ, hρA⟩).2
  have hlρ : ActsAs F l ρ := actsAs_of_pi F hl ⟨ρ, hρA⟩ hla
  have hρU : ∀ y : D8, y ∈ fixD (permGrp h331 h1222 F hH hg) ↔
      dAct ρ y ∈ fixD (permGrp h331 h1222 F hH hg) := by
    intro y
    rw [mem_fixD_iff hτ, mem_fixD_iff hτ, hρ, dAct_mul, dAct_mul, dAct_inv_dAct]
    exact rho0_fixD_iff
  have hlU : l ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    by_cases hn : n ∈ V
    · have hln : l * n * l⁻¹ ∈ V := conj_mem hl ⟨n, hn⟩
      have h1 := mem_U_iff h331 h1222 h1262 F hH hfus hg ⟨n, hn⟩
      have h2 := mem_U_iff h331 h1222 h1262 F hH hfus hg ⟨l * n * l⁻¹, hln⟩
      rw [hlρ ⟨n, hn⟩ ⟨l * n * l⁻¹, hln⟩ rfl] at h2
      exact h1.trans ((hρU _).trans h2.symm)
    · constructor
      · intro h
        exact absurd h.1 hn
      · intro h
        exfalso
        apply hn
        have h3 := conj_mem (Subgroup.inv_mem _ hl) ⟨_, h.1⟩
        rwa [show l⁻¹ * (l * n * l⁻¹) * l⁻¹⁻¹ = n by group] at h3
  set xρ : MulAut ↥V := conjAct V ⟨l, hl⟩ with hxρ
  have hxρX : xρ ∈ X := mem_autOn_iff_exists.mpr ⟨l, hl, ⟨hlL, hlU⟩, rfl⟩
  have htrans : ∀ u : ↥V, (u : G) ∈ U → u ≠ 1 → ∃ n : ℕ, (xρ ^ n) w₀ = u := by
    intro u hu h1
    have hz := (mem_fixD_iff hτ).1 ((mem_U_iff h331 h1222 h1262 F hH hfus hg w₀).1 hw₀U)
    have hz' := (mem_fixD_iff hτ).1 ((mem_U_iff h331 h1222 h1262 F hH hfus hg u).1 hu)
    have hne : ∀ w : ↥V, w ≠ 1 → dAct τ⁻¹ (F.β w) ≠ 1 := fun w hw h => hw (beta_inj F hZ (by
      have h4 := congrArg (dAct τ) h
      rwa [dAct_dAct_inv, map_one, ← map_one F.β] at h4))
    obtain ⟨n, hn⟩ := exists_pow_rho0 hz hz' (hne w₀ hw₀1) (hne u h1)
    refine ⟨n, beta_inj F hZ ?_⟩
    have hpow : xρ ^ n = conjAct V ⟨l ^ n, Subgroup.pow_mem _ hl n⟩ := by
      rw [hxρ, ← map_pow]
      rfl
    rw [hpow, (hlρ.pow hl n) w₀ _ rfl, hρ, conj_pow, dAct_mul, dAct_mul, hn, dAct_dAct_inv]
  have hfixP : ∀ n : ℕ, ∀ p ∈ P, (p : MulAut ↥V) ((xρ ^ n) w₀) = (xρ ^ n) w₀ := by
    intro n
    induction n with
    | zero =>
      intro p hp
      rw [pow_zero, MulAut.one_apply]
      exact hw₀fix p hp
    | succ n ih =>
      intro p hp
      have hp' : xρ⁻¹ * p * xρ ∈ P := by
        have h1 := (Subgroup.mem_normalizer_iff.1 (hXP (X.inv_mem hxρX)) p).1 hp
        rwa [inv_inv] at h1
      have h2 := ih _ hp'
      rw [pow_succ', MulAut.mul_apply]
      have e : (p : MulAut ↥V) (xρ ((xρ ^ n) w₀)) = xρ ((xρ⁻¹ * p * xρ) ((xρ ^ n) w₀)) := by
        simp only [MulAut.mul_apply, MulAut.apply_inv_self]
      rw [e, h2]
  intro p hp
  refine mem_autOn_of_fix h331 h1222 h1262 F hH hfus hg (hPX hp) fun v hv => ?_
  by_cases hv1 : v = 1
  · rw [hv1, map_one]
  · obtain ⟨n, hn⟩ := htrans v hv hv1
    rw [← hn]
    exact hfixP n p hp

end Main

end S126L20e

theorem lemma12_6_20_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (h1219 : Lemma12_6_19) : Lemma12_6_20 := by
  intro G _ _ T L V _ F hH
  have hfus := (h1219 G T L V F hH).1
  obtain ⟨hr3, hr4⟩ := S126L20.rParam_bounds h331 h1222 h1262 F hH hfus
  refine ⟨fun g hg _ => ⟨fun x hx hx1 =>
    S126L20.wt4_of_mem_inter h331 h1222 h1262 F hH hfus hg hx hx1,
    S126L20.card_inter_le h331 h1222 h1262 F hH hfus hg,
    fun v hv => S126L20.exists_centralizer_conj hH.hyp.irrPlus.2.2.1 hfus hv,
    fun hne hle => ?_⟩, hr3, hr4⟩
  have hg4 : S126L20c.Hyp4 V g := ⟨hg, hne, hle⟩
  exact ⟨S126L20c.bot_of_hyp4 h331 h1222 h1262 F hH hfus hg4,
    S126L20d.card_inter h331 h1222 h1262 F hH hfus hg4,
    S126L20e.autOn_eq h331 h1222 h1262 F hH hfus hg4⟩

end CFSG.Quasithin.H13
