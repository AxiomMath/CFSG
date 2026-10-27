module

public import CFSG.Quasithin.Background.F6CatG22Psi
public import CFSG.Quasithin.Background.F6CatG22ShapeChk
public import CFSG.Quasithin.Background.F6CatShapeM12

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open CFSG.QuasithinUnique

namespace F6

theorem prime_dvd_six {q : ℕ} (hq : q.Prime) (h : q ∣ 6) : q = 2 ∨ q = 3 := by
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases q <;> simp_all <;> norm_num at hq

theorem isExtensionOf_dihedral_of {G : Type*} [Group G] {P N : Subgroup G} [Finite ↥P] {n : ℕ}
    (hn : 0 < n) (hNP : N ≤ P) (hnorm : P ≤ Subgroup.normalizer (N : Set G))
    (hcard : Nat.card ↥P = 2 * n * Nat.card ↥N) {r a : G} (hr : r ∈ P) (ha : a ∈ P)
    (hσ2 : a * a ∈ N) (hrel : a * r * a⁻¹ * r ∈ N) (hn' : r ^ n ∈ N)
    (hord : ∀ q, q.Prime → q ∣ n → r ^ (n / q) ∉ N) (hnot : ∀ m < n, ∀ x ∈ N, a ≠ r ^ m * x) :
    IsExtensionOf ↥P (DihedralGroup n) ↥N := by
  have : (N.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hnorm
  set N' := N.subgroupOf P with hN'
  have hN'card : Nat.card ↥N' = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  have hNpos : 0 < Nat.card ↥N' := Nat.card_pos
  have hQ : Nat.card (↥P ⧸ N') = 2 * n := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
    rw [hcard, hN'card] at h1
    rw [hN'card] at hNpos
    exact (Nat.eq_of_mul_eq_mul_right hNpos h1).symm
  have hmk : ∀ b : ↥P, (QuotientGroup.mk b : ↥P ⧸ N') = 1 ↔ (b : G) ∈ N :=
    fun b => by rw [QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
  set ρ : ↥P ⧸ N' := QuotientGroup.mk (⟨r, hr⟩ : ↥P) with hρ
  set σ : ↥P ⧸ N' := QuotientGroup.mk (⟨a, ha⟩ : ↥P) with hσ
  have hσ2' : σ ^ 2 = 1 := by
    rw [hσ, ← QuotientGroup.mk_pow, hmk, pow_two]
    exact hσ2
  have hrel' : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [hσ, hρ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hmk]
    exact hrel
  have hρpow : ∀ m : ℕ, ρ ^ m = 1 ↔ r ^ m ∈ N := fun m => by
    rw [hρ, ← QuotientGroup.mk_pow, hmk]
    rfl
  have hρo : orderOf ρ = n := orderOf_eq_of_pow_and_pow_div_prime hn ((hρpow n).mpr hn')
    fun q hq hqn => by rw [Ne, hρpow]; exact hord q hq hqn
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro h1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
    have h0 := Int.emod_nonneg j (by omega : (n : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos j (by omega : (0 : ℤ) < n)
    have hj' : ρ ^ (j % n).toNat = σ := by
      rw [← hj, ← zpow_natCast, Int.toNat_of_nonneg h0,
        show (n : ℤ) = ((orderOf ρ : ℕ) : ℤ) by rw [hρo], zpow_mod_orderOf]
    have hm : (j % n).toNat < n := by omega
    rw [hρ, hσ, ← QuotientGroup.mk_pow, QuotientGroup.eq, hN', Subgroup.mem_subgroupOf] at hj'
    refine hnot _ hm _ hj' ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow]
    group
  obtain ⟨eD⟩ := nonempty_dihedral_of_inverting hσ2' hrel' hσρ
  rw [hρo] at eD
  have htop : Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, hQ]
  let e : ↥P ⧸ N' ≃* DihedralGroup n :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans eD
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' N'), e.surjective.comp
    (QuotientGroup.mk'_surjective N'), ⟨?_⟩⟩
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' N')).ker = N' := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (MulEquiv.subgroupCongr hker).trans (Subgroup.subgroupOfEquivOfLe hNP)

namespace G22Shape

open G22Perm

variable {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

include hk2

theorem reprN_mul
    {l m : List ℕ} {g h : G2Group k} (hg : RepL l (psi h2 hk2 g))
    (hh : RepL m (psi h2 hk2 h)) : RepL (compL l m) (psi h2 hk2 (g * h)) := by
  rw [map_mul]
  exact repL_mul hg hh

theorem eqN
    {l : List ℕ} {g h : G2Group k} (hg : RepL l (psi h2 hk2 g))
    (hh : RepL l (psi h2 hk2 h)) : g = h :=
  psi_injective h2 hk2 (eq_of_repL hg hh)

theorem reprN_gen
    (j : ℕ) (hj : j < 5) :
    RepL (g22gl j) (psi h2 hk2 (g2HomC h2 (u33GenPG j))) := by
  rw [psi_f, u33PresHom_genPG]
  exact u33_genTab_rep j hj

theorem reprN_genInv
    (j : ℕ) (hj : j < 5) :
    RepL (g22gil j) (psi h2 hk2 (g2HomC h2 (u33GenPG j))⁻¹) := by
  rw [map_inv, psi_f, u33PresHom_genPG]
  exact u33_genInvTab_rep j hj

theorem reprN_rho
    : RepL u33PiTab (psi h2 hk2 (g2RhoC h2)) := by
  rw [psi_rho]
  exact u33_pi_rep

theorem reprN_one
    : RepL g22id (psi h2 hk2 1) := by
  rw [map_one]
  exact repL_one 28

theorem sEl_zero
    : sEl h2 0 = 1 :=
  eqN h2 hk2 (repL_psi_sEl h2 hk2 0 (by norm_num)) (by rw [u33X_zero]; exact reprN_one h2 hk2)

theorem sEl_mul
    {i j l : ℕ} (hi : i < 64) (hj : j < 64) (hl : l < 64)
    (h : compL (u33XL i) (u33XL j) = u33XL l) : sEl h2 i * sEl h2 j = sEl h2 l :=
  eqN h2 hk2 (reprN_mul h2 hk2 (repL_psi_sEl h2 hk2 i hi) (repL_psi_sEl h2 hk2 j hj))
    (h ▸ repL_psi_sEl h2 hk2 l hl)

theorem sEl_injective
    {i j : ℕ} (hi : i < 64) (hj : j < 64) (h : sEl h2 i = sEl h2 j) : i = j :=
  u33X_inj i hi j hj (repL_unique (repL_psi_sEl h2 hk2 i hi) (h ▸ repL_psi_sEl h2 hk2 j hj))

theorem eq_sEl_of_repL
    {l : List ℕ} {g : G2Group k} (hg : RepL l (psi h2 hk2 g)) {I : List ℕ}
    (hI : ∀ i ∈ I, i < 64) (h : ∃ i ∈ I, l = u33XL i) : ∃ i ∈ I, g = sEl h2 i := by
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hi, eqN h2 hk2 hg (repL_psi_sEl h2 hk2 i (hI i hi))⟩

@[expose] noncomputable def idxSub
    (I : List ℕ) (hlt : ∀ i ∈ I, i < 64) (h0 : 0 ∈ I)
    (hmul : ∀ i ∈ I, ∀ j ∈ I, ∃ l ∈ I, compL (u33XL i) (u33XL j) = u33XL l)
    (hinv : ∀ i ∈ I, ∃ l ∈ I, compL (u33XL i) (u33XL l) = g22id) : Subgroup (G2Group k) where
  carrier := {g | ∃ i ∈ I, g = sEl h2 i}
  one_mem' := ⟨0, h0, (sEl_zero h2 hk2).symm⟩
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    obtain ⟨l, hl, hl'⟩ := hmul i hi j hj
    exact ⟨l, hl, sEl_mul h2 hk2 (hlt i hi) (hlt j hj) (hlt l hl) hl'⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨l, hl, hl'⟩ := hinv i hi
    refine ⟨l, hl, (eq_inv_of_mul_eq_one_right ?_).symm⟩
    exact eqN h2 hk2 (reprN_mul h2 hk2 (repL_psi_sEl h2 hk2 i (hlt i hi))
      (repL_psi_sEl h2 hk2 l (hlt l hl))) (hl' ▸ reprN_one h2 hk2)

theorem mem_idxSub
    {I : List ℕ} {hlt h0 hmul hinv} {g : G2Group k} :
    g ∈ idxSub h2 hk2 I hlt h0 hmul hinv ↔ ∃ i ∈ I, g = sEl h2 i := Iff.rfl

theorem card_idxSub
    {I : List ℕ} {hlt h0 hmul hinv} (hnd : I.Nodup) :
    Nat.card ↥(idxSub h2 hk2 I hlt h0 hmul hinv) = I.length := by
  classical
  let e : {i // i ∈ I} ≃ ↥(idxSub h2 hk2 I hlt h0 hmul hinv) :=
    Equiv.ofBijective (fun i => ⟨sEl h2 i, i, i.2, rfl⟩) ⟨fun i j h =>
      Subtype.ext (sEl_injective h2 hk2 (hlt _ i.2) (hlt _ j.2) (congrArg Subtype.val h)),
      fun ⟨g, i, hi, hg⟩ => ⟨⟨i, hi⟩, Subtype.ext hg.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_congr (Equiv.subtypeEquivRight
    (fun _ => List.mem_toFinset.symm) : {i // i ∈ I} ≃ ↥I.toFinset), Nat.card_eq_fintype_card,
    Fintype.card_coe, List.toFinset_card_of_nodup hnd]

@[expose] noncomputable def lat
    : CFSG.Quasithin.TwoLocalLattice (G2Group k) :=
  have D := g2IndexTwoData h2 hk2
  have hT := u33Phi'_T
  have hA := u33Phi'_A
  have hB := u33Phi'_B
  have hPA := u33Phi'_PA
  have hPB := u33Phi'_PB
  { S := D.ext u33Data.T hT
    P₁ := D.ext u33Data.A hA
    P₂ := D.ext u33Data.B hB
    sylow := ⟨D.isPGroup_ext hT u33Extra.syl.1, by rw [D.index_ext_T hT]; exact u33Extra.syl.2⟩
    lattice := D.lattice hT hA hB
    S_le_P₁ := D.ext_mono hT hA u33Data.T_le_A
    S_le_P₂ := D.ext_mono hT hB u33Data.T_le_B
    S_ne_P₁ := fun h => IndexTwoData.x_not_mem_T u33Extra (D.mem_of_map_mem_ext (hH := hT)
      (h ▸ D.map_le_ext hA ⟨u33Data.x, u33Data.x_mem_A, rfl⟩))
    S_ne_P₂ := fun h => IndexTwoData.y_not_mem_T u33Extra (D.mem_of_map_mem_ext (hH := hT)
      (h ▸ D.map_le_ext hB ⟨u33Data.y, u33Data.y_mem_B, rfl⟩))
    P₁_not_le_P₂ := fun h => u33Data.T_ne_A (le_antisymm u33Data.T_le_A (by
      rw [← u33Data.inf_AB]
      exact le_inf le_rfl fun x hx => D.mem_of_map_mem_ext (h (D.map_le_ext hA ⟨x, hx, rfl⟩))))
    P₂_not_le_P₁ := fun h => u33Data.T_ne_B (le_antisymm u33Data.T_le_B (by
      rw [← u33Data.inf_AB]
      exact le_inf (fun x hx => D.mem_of_map_mem_ext (h (D.map_le_ext hB ⟨x, hx, rfl⟩))) le_rfl))
    O₂ := fun Q hQ hQp => D.eq_bot_of_normal u33Extra Q hQ hQp
    loc₁ := ⟨u33Extra.PA.map (g2HomC h2),
      (Subgroup.map_eq_bot_iff_of_injective u33Extra.PA D.inj).not.2 u33Extra.PA_ne,
      u33Extra.PA_p.map _, D.ext_le_normalizer hA hPA u33Extra.PA_norm⟩
    loc₂ := ⟨u33Extra.PB.map (g2HomC h2),
      (Subgroup.map_eq_bot_iff_of_injective u33Extra.PB D.inj).not.2 u33Extra.PB_ne,
      u33Extra.PB_p.map _, D.ext_le_normalizer hB hPB u33Extra.PB_norm⟩
    normS := by
      have hSM : D.ext u33Data.T hT ≤ Subgroup.normalizer
          ((D.ext u33Data.T hT : Subgroup (G2Group k)) : Set (G2Group k)) :=
        Subgroup.le_normalizer
      rcases D.lattice hT hA hB _ hSM with h | h | h | h
      · exact h.le
      · exfalso
        have hfx : g2HomC h2 u33Data.x ∈ Subgroup.normalizer
            ((D.ext u33Data.T hT : Subgroup (G2Group k)) : Set (G2Group k)) := by
          rw [h]; exact D.map_le_ext hA ⟨u33Data.x, u33Data.x_mem_A, rfl⟩
        obtain ⟨i, hi⟩ := u33Extra.xN
        have h1 : g2HomC h2 (u33Data.Tel i) ∈ D.ext u33Data.T hT :=
          D.map_le_ext hT ⟨u33Data.Tel i, u33Data.Tel_mem_T i, rfl⟩
        have h2' := (Subgroup.mem_normalizer_iff.1 hfx _).1 h1
        have h3 : g2HomC h2 (u33Data.x * u33Data.Tel i * u33Data.x⁻¹) ∈ D.ext u33Data.T hT := by
          simpa [map_mul, map_inv] using h2'
        obtain ⟨i', hi'⟩ := (u33Data.mem_T_iff _).1 (D.mem_of_map_mem_ext h3)
        exact hi i' hi'.symm
      · exfalso
        have hfy : g2HomC h2 u33Data.y ∈ Subgroup.normalizer
            ((D.ext u33Data.T hT : Subgroup (G2Group k)) : Set (G2Group k)) := by
          rw [h]; exact D.map_le_ext hB ⟨u33Data.y, u33Data.y_mem_B, rfl⟩
        obtain ⟨i, hi⟩ := u33Extra.yN
        have h1 : g2HomC h2 (u33Data.Tel i) ∈ D.ext u33Data.T hT :=
          D.map_le_ext hT ⟨u33Data.Tel i, u33Data.Tel_mem_T i, rfl⟩
        have h2' := (Subgroup.mem_normalizer_iff.1 hfy _).1 h1
        have h3 : g2HomC h2 (u33Data.y * u33Data.Tel i * u33Data.y⁻¹) ∈ D.ext u33Data.T hT := by
          simpa [map_mul, map_inv] using h2'
        obtain ⟨i', hi'⟩ := (u33Data.mem_T_iff _).1 (D.mem_of_map_mem_ext h3)
        exact hi i' hi'.symm
      · exfalso
        have hn : (D.ext u33Data.T hT).Normal := Subgroup.normalizer_eq_top_iff.1 h
        have hbot := D.eq_bot_of_normal u33Extra _ hn (D.isPGroup_ext hT u33Extra.syl.1)
        have hρ : g2RhoC h2 ∈ D.ext u33Data.T hT := D.rho_mem_ext hT
        rw [hbot] at hρ
        exact D.rho_not_mem ⟨1, by rw [map_one, (Subgroup.mem_bot.1 hρ)]⟩ }

theorem lat_S
    : (lat h2 hk2).S = (g2IndexTwoData h2 hk2).ext u33Data.T u33Phi'_T := rfl

theorem lat_P₁
    : (lat h2 hk2).P₁ = (g2IndexTwoData h2 hk2).ext u33Data.A u33Phi'_A := rfl

theorem lat_P₂
    : (lat h2 hk2).P₂ = (g2IndexTwoData h2 hk2).ext u33Data.B u33Phi'_B := rfl

omit hk2 in
theorem phi_phi
    (x : U33G) : u33Phi' (u33Phi' x) = x := by
  apply u33PresHom_injective
  rw [u33PresHom_phi', u33PresHom_phi', ← mul_assoc, ← mul_assoc, u33Pi_sq, one_mul, mul_assoc,
    u33Pi_sq, mul_one]

theorem mem_S_iff
    {g : G2Group k} : g ∈ (lat h2 hk2).S ↔ ∃ i < 64, g = sEl h2 i := by
  have D := g2IndexTwoData h2 hk2
  rw [lat_S]
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, htg⟩)
    · obtain ⟨j, rfl⟩ := (u33Data.mem_T_iff t).mp ht
      refine ⟨j, by omega, ?_⟩
      simp [sEl, j.2]
      rfl
    · obtain ⟨j, hj⟩ := (u33Data.mem_T_iff (u33Phi' t)).mp (u33Phi'_T t ht)
      refine ⟨j + 32, by omega, ?_⟩
      have hg : g = g2HomC h2 t * g2RhoC h2 := by
        rw [htg, mul_assoc, D.sq, mul_one]
      rw [hg, sEl]
      simp only [show ¬ ((j : ℕ) + 32 < 32) by omega, ↓reduceIte, Nat.add_sub_cancel]
      rw [rho_mul h2 hk2]
      congr 2
      change u33Tel u33GenPG j = _ at hj
      rw [show u33Tel u33GenPG (j : ℕ) = u33Phi' t from hj, phi_phi]
  · rintro ⟨i, hi, rfl⟩
    by_cases hi32 : i < 32
    · refine Or.inl ⟨u33Tel u33GenPG i, ?_, by simp [sEl, hi32]⟩
      exact u33Data.Tel_mem_T ⟨i, hi32⟩
    · refine Or.inr ⟨u33Phi' (u33Tel u33GenPG (i - 32)), u33Phi'_T _
        (u33Data.Tel_mem_T ⟨i - 32, by omega⟩), ?_⟩
      rw [sEl]
      simp only [hi32, ↓reduceIte]
      rw [rho_mul h2 hk2, mul_assoc, D.sq, mul_one]

theorem sEl_mem_S
    {i : ℕ} (hi : i < 64) : sEl h2 i ∈ (lat h2 hk2).S :=
  (mem_S_iff h2 hk2).mpr ⟨i, hi, rfl⟩

theorem card_S
    : Nat.card ↥(lat h2 hk2).S = 64 := by
  let e : Fin 64 ≃ ↥(lat h2 hk2).S :=
    Equiv.ofBijective (fun i => ⟨sEl h2 i, sEl_mem_S h2 hk2 i.2⟩) ⟨fun i j h =>
      Fin.ext (sEl_injective h2 hk2 i.2 j.2 (congrArg Subtype.val h)), fun ⟨g, hg⟩ => by
        obtain ⟨i, hi, rfl⟩ := (mem_S_iff h2 hk2).mp hg
        exact ⟨⟨i, hi⟩, rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_fin]

theorem ext_le_closure
    {X : Set U33G}
    (hH : ∀ x ∈ Subgroup.closure X, u33Phi' x ∈ Subgroup.closure X) :
    (g2IndexTwoData h2 hk2).ext (Subgroup.closure X) hH ≤
      Subgroup.closure (g2HomC h2 '' X ∪ {g2RhoC h2}) := by
  have D := g2IndexTwoData h2 hk2
  have hf : (Subgroup.closure X).map (g2HomC h2) ≤
      Subgroup.closure (g2HomC h2 '' X ∪ {g2RhoC h2}) := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono Set.subset_union_left
  have hρ : g2RhoC h2 ∈ Subgroup.closure (g2HomC h2 '' X ∪ {g2RhoC h2}) :=
    Subgroup.subset_closure (Set.mem_union_right _ rfl)
  rintro g (hg | hg)
  · exact hf hg
  · have : g = g * g2RhoC h2 * g2RhoC h2 := by rw [mul_assoc, D.sq, mul_one]
    rw [this]
    exact Subgroup.mul_mem _ (hf hg) hρ


theorem conj_of_conjIn
    {I : List ℕ} (hI : ∀ i ∈ I, i < 64) {ks : List ℕ} (hks : ∀ g ∈ ks, g < 5)
    {j : ℕ} (hj : j < 64) (h : g22ConjIn ks I j = true) :
    (∀ g ∈ ks, (∃ i ∈ I, g2HomC h2 (u33GenPG g) * sEl h2 j * (g2HomC h2 (u33GenPG g))⁻¹ =
        sEl h2 i) ∧
      ∃ i ∈ I, (g2HomC h2 (u33GenPG g))⁻¹ * sEl h2 j * g2HomC h2 (u33GenPG g) = sEl h2 i) ∧
    ∃ i ∈ I, g2RhoC h2 * sEl h2 j * (g2RhoC h2)⁻¹ = sEl h2 i := by
  have D := g2IndexTwoData h2 hk2
  simp only [g22ConjIn, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨hg, hP⟩ := h
  have hrj := repL_psi_sEl h2 hk2 j hj
  refine ⟨fun g hgk => ?_, ?_⟩
  · obtain ⟨⟨i₁, hi₁, e₁⟩, ⟨i₂, hi₂, e₂⟩⟩ := hg g hgk
    have hg5 := hks g hgk
    exact ⟨⟨i₁, hi₁, eqN h2 hk2 (reprN_mul h2 hk2 (reprN_mul h2 hk2 (reprN_gen h2 hk2 g hg5) hrj)
        (reprN_genInv h2 hk2 g hg5)) (e₁ ▸ repL_psi_sEl h2 hk2 i₁ (hI i₁ hi₁))⟩,
      ⟨i₂, hi₂, eqN h2 hk2 (reprN_mul h2 hk2 (reprN_mul h2 hk2 (reprN_genInv h2 hk2 g hg5) hrj)
        (reprN_gen h2 hk2 g hg5)) (e₂ ▸ repL_psi_sEl h2 hk2 i₂ (hI i₂ hi₂))⟩⟩
  · obtain ⟨i, hi, e⟩ := hP
    refine ⟨i, hi, ?_⟩
    rw [D.rho_inv]
    exact eqN h2 hk2 (reprN_mul h2 hk2 (reprN_mul h2 hk2 (reprN_rho h2 hk2) hrj)
      (reprN_rho h2 hk2)) (e ▸ repL_psi_sEl h2 hk2 i (hI i hi))

theorem ext_le_normalizer_of_conjIn
    {H : Subgroup (G2Group k)} {I : List ℕ}
    (hI : ∀ i ∈ I, i < 64) (hH : ∀ g, g ∈ H ↔ ∃ i ∈ I, g = sEl h2 i) {ks : List ℕ}
    (hks : ∀ g ∈ ks, g < 5) (hc : ∀ j ∈ I, g22ConjIn ks I j = true)
    (hX : ∀ x ∈ Subgroup.closure {x | ∃ g ∈ ks, x = u33GenPG g},
      u33Phi' x ∈ Subgroup.closure {x | ∃ g ∈ ks, x = u33GenPG g}) :
    (g2IndexTwoData h2 hk2).ext (Subgroup.closure {x | ∃ g ∈ ks, x = u33GenPG g}) hX ≤
      Subgroup.normalizer (H : Set (G2Group k)) := by
  refine (ext_le_closure h2 hk2 hX).trans (closure_le_normalizer_of_conj _ H fun t ht z hz => ?_)
  obtain ⟨j, hj, rfl⟩ := (hH z).mp hz
  obtain ⟨hgen, hρ⟩ := conj_of_conjIn h2 hk2 hI hks (hI j hj) (hc j hj)
  have D := g2IndexTwoData h2 hk2
  rcases ht with ⟨_, ⟨g, hg, rfl⟩, rfl⟩ | ht
  · obtain ⟨⟨i₁, hi₁, e₁⟩, ⟨i₂, hi₂, e₂⟩⟩ := hgen g hg
    exact ⟨(hH _).mpr ⟨i₁, hi₁, e₁⟩, (hH _).mpr ⟨i₂, hi₂, e₂⟩⟩
  · rw [Set.mem_singleton_iff] at ht
    subst ht
    obtain ⟨i, hi, e⟩ := hρ
    refine ⟨(hH _).mpr ⟨i, hi, e⟩, (hH _).mpr ⟨i, hi, ?_⟩⟩
    rw [D.rho_inv] at e ⊢
    exact e

omit hk2 in
theorem A_eq_closure
    : u33Data.A = Subgroup.closure {x | ∃ g ∈ [0, 1, 2, 3], x = u33GenPG g} := by
  change Subgroup.closure _ = _
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_ofPred_eq, exists_eq_or_imp, exists_eq_left]
  rfl

omit hk2 in
theorem B_eq_closure
    : u33Data.B = Subgroup.closure {x | ∃ g ∈ [0, 1, 2, 4], x = u33GenPG g} := by
  change Subgroup.closure _ = _
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_ofPred_eq, exists_eq_or_imp, exists_eq_left]
  rfl

theorem P₁_le_normalizer
    {H : Subgroup (G2Group k)} {I : List ℕ} (hI : ∀ i ∈ I, i < 64)
    (hH : ∀ g, g ∈ H ↔ ∃ i ∈ I, g = sEl h2 i) (hc : ∀ j ∈ I, g22ConjIn [0, 1, 2, 3] I j = true) :
    (lat h2 hk2).P₁ ≤ Subgroup.normalizer (H : Set (G2Group k)) := by
  have hX : ∀ x ∈ Subgroup.closure {x | ∃ g ∈ [0, 1, 2, 3], x = u33GenPG g},
      u33Phi' x ∈ Subgroup.closure {x | ∃ g ∈ [0, 1, 2, 3], x = u33GenPG g} := by
    rw [← A_eq_closure]; exact u33Phi'_A
  have := ext_le_normalizer_of_conjIn h2 hk2 hI hH (by decide) hc hX
  convert this using 2
  rw [lat_P₁]
  congr 1
  exact A_eq_closure

theorem P₂_le_normalizer
    {H : Subgroup (G2Group k)} {I : List ℕ} (hI : ∀ i ∈ I, i < 64)
    (hH : ∀ g, g ∈ H ↔ ∃ i ∈ I, g = sEl h2 i) (hc : ∀ j ∈ I, g22ConjIn [0, 1, 2, 4] I j = true) :
    (lat h2 hk2).P₂ ≤ Subgroup.normalizer (H : Set (G2Group k)) := by
  have hX : ∀ x ∈ Subgroup.closure {x | ∃ g ∈ [0, 1, 2, 4], x = u33GenPG g},
      u33Phi' x ∈ Subgroup.closure {x | ∃ g ∈ [0, 1, 2, 4], x = u33GenPG g} := by
    rw [← B_eq_closure]; exact u33Phi'_B
  have := ext_le_normalizer_of_conjIn h2 hk2 hI hH (by decide) hc hX
  convert this using 2
  rw [lat_P₂]
  congr 1
  exact B_eq_closure


@[expose] noncomputable def z4Hom
    :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* G2Group k where
  toFun g := sEl h2 (g22z4Idx g)
  map_one' := by rw [g22_z4_one_chk]; exact sEl_zero h2 hk2
  map_mul' g h := (sEl_mul h2 hk2 (g22_Z_lt_chk _ (g22_z4_mem_chk g))
    (g22_Z_lt_chk _ (g22_z4_mem_chk h)) (g22_Z_lt_chk _ (g22_z4_mem_chk (g * h)))
    (g22_z4_mul_chk g h)).symm

theorem z4Hom_injective
    : Function.Injective (z4Hom h2 hk2) := fun g h hgh =>
  g22_z4_inj_chk g h (sEl_injective h2 hk2 (g22_Z_lt_chk _ (g22_z4_mem_chk g))
    (g22_Z_lt_chk _ (g22_z4_mem_chk h)) hgh)

@[expose] noncomputable def Z
    : Subgroup (G2Group k) := (z4Hom h2 hk2).range

theorem mem_Z_iff
    (g : G2Group k) : g ∈ Z h2 hk2 ↔ ∃ i ∈ g22ZIdx, g = sEl h2 i := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, g22_z4_mem_chk x, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨x, hx⟩ := g22_z4_surj_chk i hi
    exact ⟨x, by rw [← hx]; rfl⟩

noncomputable def ZEquiv
    : ↥(Z h2 hk2) ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  (MonoidHom.ofInjective (z4Hom_injective h2 hk2)).symm

theorem card_Z
    : Nat.card ↥(Z h2 hk2) = 16 := by
  rw [Nat.card_congr (ZEquiv h2 hk2).toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem Z_le_S
    : Z h2 hk2 ≤ (lat h2 hk2).S := fun g hg => by
  obtain ⟨i, hi, rfl⟩ := (mem_Z_iff h2 hk2 g).mp hg
  exact sEl_mem_S h2 hk2 (g22_Z_lt_chk i hi)

theorem P₁_le_normalizer_Z
    : (lat h2 hk2).P₁ ≤ Subgroup.normalizer (Z h2 hk2 : Set (G2Group k)) :=
  P₁_le_normalizer h2 hk2 g22_Z_lt_chk (mem_Z_iff h2 hk2) g22_Z_norm_chk

@[expose] noncomputable def R1
    : Subgroup (G2Group k) :=
  idxSub h2 hk2 g22R1Idx g22_R1_lt_chk (by decide) g22_R1_mul_chk g22_R1_inv_chk

@[expose] noncomputable def R2
    : Subgroup (G2Group k) :=
  idxSub h2 hk2 g22R2Idx g22_R2_lt_chk (by decide) g22_R2_mul_chk g22_R2_inv_chk

theorem card_R1
    : Nat.card ↥(R1 h2 hk2) = 32 := by
  rw [R1, card_idxSub h2 hk2 g22_R1_len_chk.2, g22_R1_len_chk.1]

theorem card_R2
    : Nat.card ↥(R2 h2 hk2) = 32 := by
  rw [R2, card_idxSub h2 hk2 g22_R2_len_chk.2, g22_R2_len_chk.1]

theorem R1_le_S
    : R1 h2 hk2 ≤ (lat h2 hk2).S := fun _ ⟨i, hi, hg⟩ =>
  hg ▸ sEl_mem_S h2 hk2 (g22_R1_lt_chk i hi)

theorem R2_le_S
    : R2 h2 hk2 ≤ (lat h2 hk2).S := fun _ ⟨i, hi, hg⟩ =>
  hg ▸ sEl_mem_S h2 hk2 (g22_R2_lt_chk i hi)

omit hk2 in
theorem eq_pCoreOf {R P : Subgroup (G2Group k)} (hRP : R ≤ P)
    (hn : P ≤ Subgroup.normalizer (R : Set (G2Group k))) (hR2 : IsPGroup 2 R)
    (hc : Nat.card ↥(pCoreOf 2 P) ≤ Nat.card ↥R) [Finite (G2Group k)] : R = pCoreOf 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRP hn hR2
  exact Subgroup.eq_of_le_of_card_ge hle hc

@[expose] noncomputable def qAHom
    : QuaternionGroup 2 →* G2Group k where
  toFun g := sEl h2 (g22qAIdx g)
  map_one' := by rw [g22_q_one_chk.1]; exact sEl_zero h2 hk2
  map_mul' g h := (sEl_mul h2 hk2 (g22_R2_lt_chk _ (g22_q_mem_chk g).1)
    (g22_R2_lt_chk _ (g22_q_mem_chk h).1) (g22_R2_lt_chk _ (g22_q_mem_chk (g * h)).1)
    (g22_qA_mul_chk g h)).symm

@[expose] noncomputable def qBHom
    : QuaternionGroup 2 →* G2Group k where
  toFun g := sEl h2 (g22qBIdx g)
  map_one' := by rw [g22_q_one_chk.2]; exact sEl_zero h2 hk2
  map_mul' g h := (sEl_mul h2 hk2 (g22_R2_lt_chk _ (g22_q_mem_chk g).2)
    (g22_R2_lt_chk _ (g22_q_mem_chk h).2) (g22_R2_lt_chk _ (g22_q_mem_chk (g * h)).2)
    (g22_qB_mul_chk g h)).symm

theorem qAHom_injective
    : Function.Injective (qAHom h2 hk2) := fun g h hgh =>
  g22_qA_inj_chk g h (sEl_injective h2 hk2 (g22_R2_lt_chk _ (g22_q_mem_chk g).1)
    (g22_R2_lt_chk _ (g22_q_mem_chk h).1) hgh)

theorem qBHom_injective
    : Function.Injective (qBHom h2 hk2) := fun g h hgh =>
  g22_qB_inj_chk g h (sEl_injective h2 hk2 (g22_R2_lt_chk _ (g22_q_mem_chk g).2)
    (g22_R2_lt_chk _ (g22_q_mem_chk h).2) hgh)

theorem qA_le_R2
    : (qAHom h2 hk2).range ≤ R2 h2 hk2 := by
  rintro _ ⟨g, rfl⟩
  exact ⟨_, (g22_q_mem_chk g).1, rfl⟩

theorem qB_le_R2
    : (qBHom h2 hk2).range ≤ R2 h2 hk2 := by
  rintro _ ⟨g, rfl⟩
  exact ⟨_, (g22_q_mem_chk g).2, rfl⟩

theorem isCentralProduct₂_R2
    :
    IsCentralProduct₂ ↥(R2 h2 hk2) (QuaternionGroup 2) (QuaternionGroup 2) := by
  set A' := (qAHom h2 hk2).range with hA'
  set B' := (qBHom h2 hk2).range with hB'
  have hAR := qA_le_R2 h2 hk2
  have hBR := qB_le_R2 h2 hk2
  have hsup : A' ⊔ B' = R2 h2 hk2 := by
    refine le_antisymm (sup_le hAR hBR) fun g ⟨i, hi, hg⟩ => ?_
    obtain ⟨x, y, hxy⟩ := g22_q_gen_chk i hi
    have : g = qAHom h2 hk2 x * qBHom h2 hk2 y := by
      rw [hg]
      exact (sEl_mul h2 hk2 (g22_R2_lt_chk _ (g22_q_mem_chk x).1)
        (g22_R2_lt_chk _ (g22_q_mem_chk y).2) (g22_R2_lt_chk i hi) hxy).symm
    rw [this]
    exact Subgroup.mul_mem_sup ⟨x, rfl⟩ ⟨y, rfl⟩
  have hcomm : ∀ a ∈ A', ∀ b ∈ B', a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact eqN h2 hk2 (reprN_mul h2 hk2 (repL_psi_sEl h2 hk2 _ (g22_R2_lt_chk _
      (g22_q_mem_chk x).1)) (repL_psi_sEl h2 hk2 _ (g22_R2_lt_chk _ (g22_q_mem_chk y).2)))
      ((g22_q_comm_chk x y) ▸ reprN_mul h2 hk2 (repL_psi_sEl h2 hk2 _ (g22_R2_lt_chk _
        (g22_q_mem_chk y).2)) (repL_psi_sEl h2 hk2 _ (g22_R2_lt_chk _ (g22_q_mem_chk x).1)))
  have hinf : Nat.card ↥(A' ⊓ B') = 2 := by
    have hz : ∀ g, g ∈ A' ⊓ B' ↔ g = 1 ∨ g = qAHom h2 hk2 (.a 2) := by
      intro g
      constructor
      · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
        have hxy : g22qAIdx x = g22qBIdx y := sEl_injective h2 hk2
          (g22_R2_lt_chk _ (g22_q_mem_chk x).1) (g22_R2_lt_chk _ (g22_q_mem_chk y).2) hy.symm
        rcases g22_q_inf_chk x y hxy with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact Or.inl (map_one _)
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact Subgroup.one_mem _
        · refine ⟨⟨_, rfl⟩, ⟨.a 2, ?_⟩⟩
          change sEl h2 (g22qBIdx (.a 2)) = sEl h2 (g22qAIdx (.a 2))
          rfl
    have hne : qAHom h2 hk2 (.a 2) ≠ 1 := by
      intro h1
      have := qAHom_injective h2 hk2 (h1.trans (map_one _).symm)
      exact absurd this (by decide)
    have : Nat.card ↥(A' ⊓ B') = Nat.card ({1, qAHom h2 hk2 (.a 2)} : Set (G2Group k)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun g => by
        rw [hz g, Set.mem_insert_iff, Set.mem_singleton_iff])
    rw [this, Nat.card_coe_set_eq, Set.ncard_pair hne.symm]
  refine ⟨A'.subgroupOf (R2 h2 hk2), B'.subgroupOf (R2 h2 hk2), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.subgroupOf_sup hAR hBR, hsup, Subgroup.subgroupOf_self]
  · intro a ha b hb
    exact Subtype.ext (hcomm a ha b hb)
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hAR).trans
      (MonoidHom.ofInjective (qAHom_injective h2 hk2)).symm⟩
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hBR).trans
      (MonoidHom.ofInjective (qBHom_injective h2 hk2)).symm⟩
  · have heq : A'.subgroupOf (R2 h2 hk2) ⊓ B'.subgroupOf (R2 h2 hk2) =
        (A' ⊓ B').subgroupOf (R2 h2 hk2) := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [heq, ← hinf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hAR)).toEquiv


theorem S_le_normalizer_Z
    : (lat h2 hk2).S ≤ Subgroup.normalizer (Z h2 hk2 : Set (G2Group k)) :=
  (lat h2 hk2).S_le_P₁.trans (P₁_le_normalizer_Z h2 hk2)

theorem S_shape
    [Finite k] : IsExtensionOf ↥(lat h2 hk2).S
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  have : Finite (G2Group k) := finite_g2Group
  have hZS := Z_le_S h2 hk2
  have : ((Z h2 hk2).subgroupOf (lat h2 hk2).S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZS).mpr (S_le_normalizer_Z h2 hk2)
  set N' := (Z h2 hk2).subgroupOf (lat h2 hk2).S with hN'
  have hN'card : Nat.card ↥N' = 16 := by
    rw [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv, card_Z]
  have hQ4 : Nat.card (↥(lat h2 hk2).S ⧸ N') = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
    rw [card_S, hN'card] at h1
    omega
  have hK : IsKleinFour (↥(lat h2 hk2).S ⧸ N') := by
    refine isKleinFour_of_card_four_of_mul_self hQ4 fun q => ?_
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
    obtain ⟨i, hi, hti⟩ := (mem_S_iff h2 hk2).mp t.2
    obtain ⟨l, hl, hll⟩ := g22_S_sq_chk i hi
    rw [Subgroup.coe_mul, hti, mem_Z_iff]
    exact ⟨l, hl, sEl_mul h2 hk2 hi hi (g22_Z_lt_chk l hl) hll⟩
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := ↥(lat h2 hk2).S ⧸ N')
    (G₂ := Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' N'), e.surjective.comp
    (QuotientGroup.mk'_surjective N'), ⟨?_⟩⟩
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' N')).ker = N' := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (MulEquiv.subgroupCongr hker).trans
    ((Subgroup.subgroupOfEquivOfLe hZS).trans (ZEquiv h2 hk2))

theorem reprN_rhoP
    : RepL g22rhoL (psi h2 hk2 (g2RhoC h2 * g2HomC h2 (u33GenPG 3))) :=
  reprN_mul h2 hk2 (reprN_rho h2 hk2) (reprN_gen h2 hk2 3 (by norm_num))

theorem reprN_rhoPow
    (m : ℕ) :
    RepL (g22rhoPowL m) (psi h2 hk2 ((g2RhoC h2 * g2HomC h2 (u33GenPG 3)) ^ m)) := by
  induction m with
  | zero => rw [pow_zero]; exact reprN_one h2 hk2
  | succ m ih => rw [pow_succ]; exact reprN_mul h2 hk2 ih (reprN_rhoP h2 hk2)

theorem mem_Z_of_repL
    {l : List ℕ} {g : G2Group k} (hg : RepL l (psi h2 hk2 g))
    (h : ∃ i ∈ g22ZIdx, l = u33XL i) : g ∈ Z h2 hk2 :=
  (mem_Z_iff h2 hk2 _).mpr (eq_sEl_of_repL h2 hk2 hg g22_Z_lt_chk h)

theorem not_mem_Z_of_repL
    {l : List ℕ} {g : G2Group k} (hg : RepL l (psi h2 hk2 g))
    (h : ∀ i ∈ g22ZIdx, l ≠ u33XL i) : g ∉ Z h2 hk2 := fun hgZ => by
  obtain ⟨i, hi, rfl⟩ := (mem_Z_iff h2 hk2 _).mp hgZ
  exact h i hi (repL_unique hg (repL_psi_sEl h2 hk2 i (g22_Z_lt_chk i hi)))

theorem P₁_shape
    [Finite k] (hP : Nat.card ↥(lat h2 hk2).P₁ = 192) :
    IsExtensionOf ↥(lat h2 hk2).P₁ (DihedralGroup 6)
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  have : Finite (G2Group k) := finite_g2Group
  have D := g2IndexTwoData h2 hk2
  have hρP : g2RhoC h2 ∈ (lat h2 hk2).P₁ := D.rho_mem_ext u33Phi'_A
  have hxP : g2HomC h2 (u33GenPG 3) ∈ (lat h2 hk2).P₁ :=
    D.map_le_ext u33Phi'_A ⟨u33Data.x, u33Data.x_mem_A, rfl⟩
  have hsP : g2HomC h2 (u33GenPG 2) ∈ (lat h2 hk2).P₁ :=
    (lat h2 hk2).S_le_P₁ (D.map_le_ext u33Phi'_T ⟨u33Data.s, u33Data.s_mem_T, rfl⟩)
  have hs := reprN_gen h2 hk2 2 (by norm_num)
  have hord : ∀ q, q.Prime → q ∣ 6 →
      (g2RhoC h2 * g2HomC h2 (u33GenPG 3)) ^ (6 / q) ∉ Z h2 hk2 := fun q hq hq6 => by
    obtain rfl | rfl := prime_dvd_six hq hq6
    · exact not_mem_Z_of_repL h2 hk2 (reprN_rhoPow h2 hk2 3) g22_rho_three_chk
    · exact not_mem_Z_of_repL h2 hk2 (reprN_rhoPow h2 hk2 2) g22_rho_two_chk
  have hnot : ∀ m < 6, ∀ x ∈ Z h2 hk2,
      g2HomC h2 (u33GenPG 2) ≠ (g2RhoC h2 * g2HomC h2 (u33GenPG 3)) ^ m * x := by
    intro m hm x hx hax
    obtain ⟨i, hi, rfl⟩ := (mem_Z_iff h2 hk2 _).mp hx
    exact g22_sigma_not_chk m hm i hi (repL_unique (reprN_mul h2 hk2 (reprN_rhoPow h2 hk2 m)
      (repL_psi_sEl h2 hk2 i (g22_Z_lt_chk i hi))) (hax ▸ hs))
  obtain ⟨φ, hφ, ⟨eN⟩⟩ := isExtensionOf_dihedral_of (n := 6) (by norm_num)
    ((Z_le_S h2 hk2).trans (lat h2 hk2).S_le_P₁) (P₁_le_normalizer_Z h2 hk2)
    (by rw [hP, card_Z]) (Subgroup.mul_mem _ hρP hxP) hsP
    (mem_Z_of_repL h2 hk2 (reprN_mul h2 hk2 hs hs) g22_sigma_sq_chk)
    (mem_Z_of_repL h2 hk2 (reprN_mul h2 hk2 (reprN_mul h2 hk2 (reprN_mul h2 hk2 hs
      (reprN_rhoP h2 hk2)) (reprN_genInv h2 hk2 2 (by norm_num))) (reprN_rhoP h2 hk2))
      g22_sigma_rho_chk)
    (mem_Z_of_repL h2 hk2 (reprN_rhoPow h2 hk2 6) g22_rho_six_chk) hord hnot
  exact ⟨φ, hφ, ⟨eN.trans (ZEquiv h2 hk2)⟩⟩

theorem R1_le_P₁
    : R1 h2 hk2 ≤ (lat h2 hk2).P₁ := (R1_le_S h2 hk2).trans (lat h2 hk2).S_le_P₁

theorem R2_le_P₂
    : R2 h2 hk2 ≤ (lat h2 hk2).P₂ := (R2_le_S h2 hk2).trans (lat h2 hk2).S_le_P₂

theorem R1_eq_pCoreOf
    [Finite k] (hc : Nat.card ↥(pCoreOf 2 (lat h2 hk2).P₁) ≤ 32) :
    R1 h2 hk2 = pCoreOf 2 (lat h2 hk2).P₁ := by
  have : Finite (G2Group k) := finite_g2Group
  exact eq_pCoreOf (R1_le_P₁ h2 hk2)
    (P₁_le_normalizer h2 hk2 g22_R1_lt_chk (fun _ => Iff.rfl) g22_R1_norm_chk)
    ((lat h2 hk2).sylow.1.to_le (R1_le_S h2 hk2)) (by rw [card_R1]; exact hc)

theorem R2_eq_pCoreOf
    [Finite k] (hc : Nat.card ↥(pCoreOf 2 (lat h2 hk2).P₂) ≤ 32) :
    R2 h2 hk2 = pCoreOf 2 (lat h2 hk2).P₂ := by
  have : Finite (G2Group k) := finite_g2Group
  exact eq_pCoreOf (R2_le_P₂ h2 hk2)
    (P₂_le_normalizer h2 hk2 g22_R2_lt_chk (fun _ => Iff.rfl) g22_R2_norm_chk)
    ((lat h2 hk2).sylow.1.to_le (R2_le_S h2 hk2)) (by rw [card_R2]; exact hc)

theorem card_center_R1_ne
    : Nat.card ↥(Subgroup.center ↥(R1 h2 hk2)) ≠ 2 := by
  have hcen : ∀ i (hi : i ∈ g22R1Idx),
      (∀ j ∈ g22R1Idx, compL (u33XL i) (u33XL j) = compL (u33XL j) (u33XL i)) →
      (⟨sEl h2 i, i, hi, rfl⟩ : ↥(R1 h2 hk2)) ∈ Subgroup.center ↥(R1 h2 hk2) := by
    intro i hi hc
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, j, hj, rfl⟩
    have hi' := g22_R1_lt_chk i hi
    have hj' := g22_R1_lt_chk j hj
    have h1 : sEl h2 j * sEl h2 i = sEl h2 i * sEl h2 j :=
      eqN h2 hk2 (reprN_mul h2 hk2 (repL_psi_sEl h2 hk2 j hj') (repL_psi_sEl h2 hk2 i hi'))
        ((hc j hj) ▸ reprN_mul h2 hk2 (repL_psi_sEl h2 hk2 i hi') (repL_psi_sEl h2 hk2 j hj'))
    exact Subtype.ext h1
  obtain ⟨hc, h8, h12⟩ := g22_R1_center_chk
  intro h
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center ↥(R1 h2 hk2)))).1 h
  have hval : ∀ {z w : ↥(Subgroup.center ↥(R1 h2 hk2))}, z = w →
      ((z : ↥(R1 h2 hk2)) : G2Group k) = ((w : ↥(R1 h2 hk2)) : G2Group k) := fun h => h ▸ rfl
  have hne : ∀ {i j : ℕ}, i < 64 → j < 64 → i ≠ j → sEl h2 i ≠ sEl h2 j :=
    fun hi hj hij h => hij (sEl_injective h2 hk2 hi hj h)
  have e8 := huniq ⟨_, hcen 8 h8 fun j hj => (hc j hj).1⟩ fun h1 =>
    hne (i := 8) (j := 0) (by norm_num) (by norm_num) (by norm_num)
      ((hval h1).trans (sEl_zero h2 hk2).symm)
  have e12 := huniq ⟨_, hcen 12 h12 fun j hj => (hc j hj).2⟩ fun h1 =>
    hne (i := 12) (j := 0) (by norm_num) (by norm_num) (by norm_num)
      ((hval h1).trans (sEl_zero h2 hk2).symm)
  exact hne (i := 8) (j := 12) (by norm_num) (by norm_num) (by norm_num) (hval (e8.trans e12.symm))

end G22Shape

end F6

end CFSG.Quasithin
