module

import all CFSG.Quasithin.Background.Harris.OrdinaryProofs.F5SevenCore
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.F5SevenCore
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.F5SevenPull
public import CFSG.Quasithin.Background.Harris.KFact2d.ModelL3
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.F5P7

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.E2P.Asc80
  CFSG.Quasithin.Background.Harris.OrdinaryProofs
open scoped MatrixGroups

section Kernel

variable {p : ℕ} [Fact p.Prime]

theorem mem_ker_rhoL_iff (B : GL (Fin 2) (ZMod p)) :
    B ∈ (rhoL p).ker ↔
      ∃ r : ZMod p, r ^ 3 = 1 ∧ (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = Matrix.scalar (Fin 2) r := by
  constructor
  · intro h
    have hk : leviHom p B ∈ (piL p).ker := h
    rw [ker_piL] at hk
    obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk
    refine ⟨r, by simpa using hr3, ?_⟩
    have h00 := congrFun (congrFun hr 0) 0
    have h01 := congrFun (congrFun hr 0) 1
    have h10 := congrFun (congrFun hr 1) 0
    have h11 := congrFun (congrFun hr 1) 1
    simp [coe_leviHom, Matrix.scalar_apply] at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply] <;> grind
  · rintro ⟨r, hr3, hB⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr3
    show piL p (leviHom p B) = 1
    rw [← MonoidHom.mem_ker, ker_piL]
    refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨r, by simpa using hr3, ?_⟩
    rw [coe_leviHom, hB]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
    exact (inv_eq_of_mul_eq_one_right (by linear_combination hr3)).symm

theorem range_rhoL : (rhoL p).range = leviC p := by
  unfold rhoL leviC leviBlock
  exact MonoidHom.range_comp _ _

end Kernel

section GL7

open Certificates.F5Seven CFSG.Quasithin.Background.Harris.OrdinaryProofs.F5Seven

abbrev zt : GL (Fin 2) (ZMod 7) := mkU zeta7 zeta7_det

abbrev st : GL (Fin 2) (ZMod 7) := mkU sigma7 sigma7_det

theorem coe_zt : (zt : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![1, 5; 2, 1] := by rfl

theorem coe_zt_pow (n : ℕ) :
    ((zt ^ n : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) = (!![1, 5; 2, 1]) ^ n := by
  rw [Units.val_pow_eq_pow_val, coe_zt]

theorem coe_st : (st : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![1, 0; 0, 6] := by rfl

theorem zt_pow_48 : zt ^ 48 = 1 := by
  apply Units.ext
  rw [coe_zt_pow]
  show _ = (1 : Matrix (Fin 2) (Fin 2) (ZMod 7))
  decide +kernel

theorem zt_pow_24 : zt ^ 24 ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 2) (ZMod 7) => (g : Matrix (Fin 2) (Fin 2) (ZMod 7))) h
  simp only [coe_zt_pow] at this
  revert this
  decide +kernel

theorem zt_pow_16 : zt ^ 16 ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 2) (ZMod 7) => (g : Matrix (Fin 2) (Fin 2) (ZMod 7))) h
  simp only [coe_zt_pow] at this
  revert this
  decide +kernel

theorem orderOf_zt : orderOf zt = 48 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) zt_pow_48 ?_
  intro q hq hqd
  have : q = 2 ∨ q = 3 := by
    have h48 : q ∣ 2 ^ 4 * 3 := by norm_num; exact hqd
    rcases (Nat.Prime.dvd_mul hq).mp h48 with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h)
  rcases this with rfl | rfl
  · exact zt_pow_24
  · exact zt_pow_16

theorem st_mul_st : st * st = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_st, Units.val_one]
  decide +kernel

theorem st_zt_st : st * zt * st = zt ^ 7 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_zt_pow, coe_st, coe_zt]
  decide +kernel

theorem zt_pow_16_eq : ((zt ^ 16 : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) =
    Matrix.scalar (Fin 2) (4 : ZMod 7) := by
  rw [coe_zt_pow]
  decide +kernel

theorem zt_pow_32_eq : ((zt ^ 32 : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) =
    Matrix.scalar (Fin 2) (2 : ZMod 7) := by
  rw [coe_zt_pow]
  decide +kernel

theorem st_mem_conj (n : GL (Fin 2) (ZMod 7)) (hn : n ∈ Subgroup.zpowers zt) :
    st * n * st ∈ Subgroup.zpowers zt := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hinv : st⁻¹ = st := inv_eq_of_mul_eq_one_right st_mul_st
  have h : MulAut.conj st zt = zt ^ 7 := by
    rw [MulAut.conj_apply, hinv, st_zt_st]
  have h2 := map_zpow (MulAut.conj st) zt k
  rw [h, MulAut.conj_apply, hinv] at h2
  rw [h2]
  exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers zt) 7) k

theorem st_mul_st_mul (a : GL (Fin 2) (ZMod 7)) : st * (st * a) = a := by
  rw [← mul_assoc, st_mul_st, one_mul]

theorem st_notMem_zpowers : st ∉ Subgroup.zpowers zt := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hc : st * zt = zt * st := by
    rw [← hk]
    exact ((Commute.refl zt).zpow_left k).eq
  have h7 : zt ^ 7 = zt := by
    rw [← st_zt_st, hc, mul_assoc, st_mul_st, mul_one]
  have h6 : zt ^ 6 = 1 := by
    have : zt ^ 6 * zt = 1 * zt := by rw [← pow_succ, one_mul]; exact h7
    exact mul_right_cancel this
  have := orderOf_dvd_of_pow_eq_one h6
  rw [orderOf_zt] at this
  omega

theorem mem_uHat7_cases {g : GL (Fin 2) (ZMod 7)} (hg : g ∈ uHat7) :
    g ∈ Subgroup.zpowers zt ∨ g * st ∈ Subgroup.zpowers zt := by
  have hinv : st⁻¹ = st := inv_eq_of_mul_eq_one_right st_mul_st
  unfold uHat7 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inl (Subgroup.mem_zpowers zt)
    · exact Or.inr (by rw [st_mul_st]; exact Subgroup.one_mem _)
  | one => exact Or.inl (Subgroup.one_mem _)
  | mul x y _ _ ihx ihy =>
    rcases ihx with hx | hx <;> rcases ihy with hy | hy
    · exact Or.inl (Subgroup.mul_mem _ hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact Subgroup.mul_mem _ hx hy)
    · refine Or.inr ?_
      have : x * y * st = (x * st) * (st * y * st) := by
        simp only [mul_assoc, st_mul_st_mul]
      rw [this]
      exact Subgroup.mul_mem _ hx (st_mem_conj y hy)
    · refine Or.inl ?_
      have : x * y = (x * st) * (st * (y * st) * st) := by
        simp only [mul_assoc, st_mul_st_mul, st_mul_st, mul_one]
      rw [this]
      exact Subgroup.mul_mem _ hx (st_mem_conj _ hy)
  | inv x _ ihx =>
    rcases ihx with hx | hx
    · exact Or.inl (Subgroup.inv_mem _ hx)
    · refine Or.inr ?_
      have h1 : st * x⁻¹ ∈ Subgroup.zpowers zt := by
        have := Subgroup.inv_mem _ hx
        rwa [mul_inv_rev, hinv] at this
      have : x⁻¹ * st = st * (st * x⁻¹) * st := by
        simp only [st_mul_st_mul]
      rw [this]
      exact st_mem_conj _ h1

theorem card_uHat7 : Nat.card uHat7 = 96 := by
  have hN : Subgroup.zpowers zt ≤ uHat7 := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hst : st ∈ uHat7 := Subgroup.subset_closure (by simp)
  have hidx : ((Subgroup.zpowers zt).subgroupOf uHat7).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨st, hst⟩, fun b => ?_⟩
    have hb := mem_uHat7_cases b.2
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases h : (b : GL (Fin 2) (ZMod 7)) ∈ Subgroup.zpowers zt
    · refine Or.inr ⟨h, fun h2 => st_notMem_zpowers ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h) h2
      simpa using this
    · refine Or.inl ⟨hb.resolve_left h, h⟩
  have h1 := Subgroup.card_mul_index ((Subgroup.zpowers zt).subgroupOf uHat7)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv, Nat.card_zpowers,
    orderOf_zt] at h1
  omega

theorem ker_rhoL_seven : (rhoL 7).ker = Subgroup.zpowers (zt ^ 16) := by
  ext B
  rw [mem_ker_rhoL_iff]
  constructor
  · rintro ⟨r, hr3, hB⟩
    have hr : r = 1 ∨ r = 2 ∨ r = 4 := by
      have key : ∀ r : ZMod 7, r ^ 3 = 1 → r = 1 ∨ r = 2 ∨ r = 4 := by decide
      exact key r hr3
    rcases hr with rfl | rfl | rfl
    · have : B = 1 := Units.ext (by rw [hB, map_one]; rfl)
      rw [this]; exact Subgroup.one_mem _
    · have : B = (zt ^ 16) ^ 2 := by
        apply Units.ext
        rw [hB, ← pow_mul]
        exact zt_pow_32_eq.symm
      rw [this]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
    · have : B = zt ^ 16 := Units.ext (by rw [hB]; exact zt_pow_16_eq.symm)
      rw [this]; exact Subgroup.mem_zpowers _
  · intro h
    have h' : zt ^ 16 ∈ (rhoL 7).ker := (mem_ker_rhoL_iff _).2 ⟨4, by decide, zt_pow_16_eq⟩
    rw [mem_ker_rhoL_iff] at h'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    have := Subgroup.zpow_mem _ ((mem_ker_rhoL_iff _).2 h') k
    rw [mem_ker_rhoL_iff] at this
    exact this

theorem card_ker_rhoL_seven : Nat.card (rhoL 7).ker = 3 := by
  rw [ker_rhoL_seven, Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) (by rw [orderOf_zt]; norm_num),
    orderOf_zt]

theorem ker_rhoL_le_uHat7 : (rhoL 7).ker ≤ uHat7 := by
  rw [ker_rhoL_seven, Subgroup.zpowers_le]
  have : zt ^ 16 ∈ Subgroup.zpowers zt := Subgroup.pow_mem _ (Subgroup.mem_zpowers zt) 16
  have h2 : Subgroup.zpowers zt ≤ uHat7 := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  exact h2 this

theorem card_GL2_seven : Nat.card (GL (Fin 2) (ZMod 7)) = 2016 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

theorem card_range_rhoL_seven : Nat.card (rhoL 7).range = 672 := by
  have h := Subgroup.card_ker_mul_card_range (rhoL 7)
  rw [card_ker_rhoL_seven, card_GL2_seven] at h
  omega

theorem index_uHat7 : uHat7.index = 21 := by
  have h := Subgroup.card_mul_index uHat7
  rw [card_uHat7, card_GL2_seven] at h
  omega

theorem map_uHat7_subgroupOf :
    (uHat7.map (rhoL 7)).subgroupOf (rhoL 7).range = uHat7.map (rhoL 7).rangeRestrict := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hx⟩
    exact ⟨h, hh, Subtype.ext hx⟩
  · rintro ⟨h, hh, hx⟩
    exact ⟨h, hh, congrArg Subtype.val hx⟩

theorem isSylowTwoOf_map_uHat7 : IsSylowTwoOf (uHat7.map (rhoL 7)) (rhoL 7).range := by
  have hle : uHat7.map (rhoL 7) ≤ (rhoL 7).range := by
    rintro _ ⟨h, -, rfl⟩
    exact ⟨h, rfl⟩
  have hidx : (uHat7.map (rhoL 7).rangeRestrict).index = 21 := by
    rw [Subgroup.index_map_eq _ (MonoidHom.rangeRestrict_surjective _)
      (by rw [MonoidHom.ker_rangeRestrict]; exact ker_rhoL_le_uHat7), index_uHat7]
  have hcard : Nat.card (uHat7.map (rhoL 7)) = 32 := by
    have h := Subgroup.card_mul_index (uHat7.map (rhoL 7).rangeRestrict)
    rw [hidx, card_range_rhoL_seven] at h
    have e : Nat.card (uHat7.map (rhoL 7)) =
        Nat.card ((uHat7.map (rhoL 7)).subgroupOf (rhoL 7).range) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm
    rw [map_uHat7_subgroupOf] at e
    omega
  refine ⟨hle, IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num), ?_⟩
  rw [map_uHat7_subgroupOf, hidx]
  omega

theorem leviC_maximal {U₀ : Subgroup (PSL3 7)}
    (hU₀ : SpecialSylowL 7 U₀) :
    ∀ V : Subgroup (PSL3 7), U₀ ≤ V → V ≤ leviC 7 → V = U₀ ∨ V = leviC 7 := by
  have hU0L : IsSylowTwoOf U₀ (rhoL 7).range :=
    B6.isSylowTwoOf_mono hU₀.1 (by rw [range_rhoL]; exact hU₀.2.1) le_top
  obtain ⟨c, hc, hUc⟩ := B6.isSylowTwoOf_exists_conj isSylowTwoOf_map_uHat7 hU0L
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hc
  have hU₀eq : U₀ = (B6.conjSub g uHat7).map (rhoL 7) := by
    ext x
    rw [hUc, B6.mem_conjSub]
    constructor
    · rintro ⟨h, hh, hρ⟩
      refine ⟨g * h * g⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, B6.mem_conjSub]
        simpa [mul_assoc] using hh
      · rw [map_mul, map_mul, map_inv, hρ]
        group
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, B6.mem_conjSub] at hy
      refine ⟨g⁻¹ * y * g, hy, ?_⟩
      simp [map_mul, map_inv]
  have hker : (rhoL 7).ker ≤ B6.conjSub g uHat7 := by
    intro k hk
    rw [B6.mem_conjSub]
    have := (MonoidHom.normal_ker (rhoL 7)).conj_mem k hk g⁻¹
    rw [inv_inv] at this
    exact ker_rhoL_le_uHat7 this
  have hcomap : U₀.comap (rhoL 7) = B6.conjSub g uHat7 := by
    rw [hU₀eq, Subgroup.comap_map_eq, sup_eq_left.mpr hker]
  refine maximal_of_comap_maximal (Ψ := rhoL 7) range_rhoL (U := U₀) ?_
  rw [hcomap]
  intro H hle
  let H₁ : Subgroup (GL (Fin 2) (ZMod 7)) := H.comap (MulAut.conj g).toMonoidHom
  have hH₁ : ∀ x, x ∈ H₁ ↔ g * x * g⁻¹ ∈ H := fun x => Iff.rfl
  have hU : uHat7 ≤ H₁ := by
    intro x hx
    rw [hH₁]
    refine hle ?_
    rw [B6.mem_conjSub]
    simpa [mul_assoc] using hx
  rcases f5SevenCore_maximal H₁ hU with h | h
  · left
    refine le_antisymm (fun y hy => ?_) hle
    have : g⁻¹ * y * g ∈ H₁ := by
      rw [hH₁]
      simpa [mul_assoc] using hy
    rw [h] at this
    rw [B6.mem_conjSub]
    exact this
  · right
    refine eq_top_iff.mpr fun y _ => ?_
    have : g⁻¹ * y * g ∈ H₁ := by rw [h]; exact Subgroup.mem_top _
    rw [hH₁] at this
    simpa [mul_assoc] using this

end GL7

section CenMax

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem map_centralizer_zOf {L : Type} [Group L] {K : Subgroup X} {S : Subgroup X}
    (e : ↥K ≃* L) (U₀ : Subgroup L) (hmap : (S.subgroupOf K).map e.toMonoidHom = U₀) :
    (Subgroup.centralizer (E2P.zOf (S.subgroupOf K) : Set ↥K)).map e.toMonoidHom =
      Subgroup.centralizer (E2P.zOf U₀ : Set L) := by
  rw [← hmap]
  ext w
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have hy' := (mem_zOf_map_iff e _ y).1 hy
    have := h _ hy'
    apply e.symm.injective
    simpa using this
  · intro h z hz
    have hz' : e z ∈ E2P.zOf ((S.subgroupOf K).map e.toMonoidHom) :=
      (mem_zOf_map_iff e _ (e z)).2 (by simpa using hz)
    have := h _ hz'
    apply e.injective
    simpa using this

omit [Finite X] in
theorem cenZ_eq_map_centralizer {K S : Subgroup X} (hS : S ≤ K) :
    cenZ K S = (Subgroup.centralizer (E2P.zOf (S.subgroupOf K) : Set ↥K)).map K.subtype := by
  ext x
  rw [mem_cenZ_iff hS, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyc⟩
    exact ⟨y, hyc, hy⟩
  · rintro ⟨y, hyc, hy⟩
    exact ⟨y, hy, hyc⟩

theorem cenMax_seven {K T : Subgroup X}
    (hK : IsPSL 3 7 1 ↥K) (hS : IsSylowTwoOf (T ⊓ K) K) : CenMax K T := by
  obtain ⟨e, U₀, hU₀, hmap⟩ := exists_equiv_special (p := 7) (by norm_num) hK hS
  have hC : Subgroup.centralizer (E2P.zOf U₀ : Set (PSL3 7)) = leviC 7 :=
    centralizer_zOf_eq_leviC (by norm_num) hU₀.1 hU₀.2.1
  have hcen := map_centralizer_zOf (K := K) e U₀ hmap
  rw [hC] at hcen
  have hcenK := cenZ_eq_map_centralizer hS.1
  have hmax := leviC_maximal hU₀
  set C₀ := Subgroup.centralizer (E2P.zOf ((T ⊓ K).subgroupOf K) : Set ↥K) with hC₀
  intro B hSB hBC
  have hBK : B ≤ K := hBC.trans inf_le_left
  have hB₀C : B.subgroupOf K ≤ C₀ := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hcenK ▸ hBC hx)
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have hS₀B : (T ⊓ K).subgroupOf K ≤ B.subgroupOf K := fun x hx => hSB hx
  have hV1 : U₀ ≤ (B.subgroupOf K).map e.toMonoidHom := hmap ▸ Subgroup.map_mono hS₀B
  have hV2 : (B.subgroupOf K).map e.toMonoidHom ≤ leviC 7 := hcen ▸ Subgroup.map_mono hB₀C
  have hinj : Function.Injective (Subgroup.map e.toMonoidHom : Subgroup ↥K → Subgroup (PSL3 7)) :=
    Subgroup.map_injective e.injective
  rcases hmax _ hV1 hV2 with hV | hV
  · left
    have h0 : B.subgroupOf K = (T ⊓ K).subgroupOf K := hinj (hV.trans hmap.symm)
    refine le_antisymm (fun x hx => ?_) hSB
    have : (⟨x, hBK hx⟩ : ↥K) ∈ B.subgroupOf K := hx
    rw [h0] at this
    exact this
  · right
    have h0 : B.subgroupOf K = C₀ := hinj (hV.trans hcen.symm)
    refine le_antisymm hBC (fun x hx => ?_)
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hcenK ▸ hx)
    have : y ∈ B.subgroupOf K := h0 ▸ hy
    exact hyx ▸ this

theorem f5_seven : StarStmtFor fun q => q = 7 := by
  intro X _ _ K T M V p hp hX hV hVT hTV hA
  subst hp
  obtain ⟨hX', -, -, hL, hM⟩ := hX
  have hK : IsPSL 3 7 1 ↥K := by
    rcases hL with ⟨h, -⟩ | ⟨-, h, -⟩
    · omega
    · exact h
  have := hX'.normal
  have hCen : CenMax K T := cenMax_seven hK hX'.isSylow_inf
  have hTM : T ≤ M := by
    have hmem : M ∈ maxOver (⊤ : Subgroup X) T := by
      rw [hX'.minPar.uniqueMax]
      exact Set.mem_singleton M
    exact hmem.2
  exact V_le_pCoreOf_of_cenMax hX'.sup hTM hM hCen hVT hV hA

end CenMax

end CFSG.Quasithin.Background.Harris.KFact2d

end
