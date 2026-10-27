module

public import CFSG.Quasithin.Vol2.Ch9Sec2Swap
public import CFSG.Quasithin.Vol2.Ch9Sec3Diag

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

theorem sl2_four_equiv_alt_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 5)) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hAr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    rw [Subgroup.mem_bot]
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have hr1 : r = 1 := by
      have h3 : (r - 1) ^ 2 = 0 := by linear_combination hr2 - (r - 1) * h2
      exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3)
    rw [hr1, map_one] at hAr
    exact Subtype.ext hAr.symm
  obtain ⟨e⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inl hK)
  let e1 : Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
  exact ⟨e1.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).trans
    e)⟩

theorem isL2Quot_two_of_alt_five {G : Type} [Group G]
    {K : Subgroup G} (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) :
    IsL2Quot 2 (oTwoQuot ↥K) := by
  obtain ⟨eA⟩ := hKA
  have e1 : oTwoQuot ↥K ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2).symm).trans eA
  have hF : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hF)
  exact ⟨e1.trans (e5.symm.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 2 2)).symm)⟩

theorem uni_mul_comm {K : Type} [Field K] {x y : SpecialLinearGroup (Fin 2) K} (hx : x ∈ uni K)
    (hy : y ∈ uni K) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm]

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem bar_eq_one_of_mem_centralizer {K : Type} [Field K] (e : ↥(fsuV T I) ≃* Om4.VM K) {x : G}
    (hx : x ∈ Subgroup.normalizer (fsuV T I : Set G))
    (hxC : x ∈ Subgroup.centralizer (fsuV T I : Set G)) : bar e ⟨x, hx⟩ = 1 := by
  refine MulEquiv.ext fun X => ?_
  obtain ⟨v, rfl⟩ := e.surjective X
  rw [bar_apply, MulAut.one_apply]
  congr 1
  refine Subtype.ext ?_
  show x * (v : G) * x⁻¹ = v
  rw [← Subgroup.mem_centralizer_iff.mp hxC v v.2, mul_inv_cancel_right]

namespace Setup

variable (S : Setup T L I n)
include S

theorem oTwoQuot_L_facts (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := S.exists_quot_equiv_sl2 h37c h38c
  rw [h2] at hF
  obtain ⟨e5⟩ := sl2_four_equiv_alt_five (K := F) (by rw [hF]; norm_num)
  exact ⟨e.trans e5⟩

namespace IsCoord

variable {S} {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem mem_normalizer_L_of_lr (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    {x : G} (hx : x ∈ fsuM T L) {A B : GL (Fin 2) K}
    (hform : bar e ⟨x, S.hMN hx⟩ = Om4.lr A B) : x ∈ Subgroup.normalizer (L : Set G) :=
  hc.mem_normalizer_L_of_isNS h37 h38 h37c h38c hx (τ := 1)
    (by rw [Om4.frM_one, mul_one]; exact hform)

theorem L0_le_normalizer_L (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) :
    fsuL0 T L ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
  hc.mem_normalizer_L_of_lr h37 h38 h37c h38c (Setup.L0_le_fsuM hx) (by
    rw [show (⟨x, S.hMN (Setup.L0_le_fsuM hx)⟩ : ↥(Subgroup.normalizer (fsuV T I : Set G))) =
      Subgroup.inclusion S.L0_le_normalizer_V ⟨x, hx⟩ from rfl, hc.bar_L0, Om4.rho_apply])

theorem r0_le_normalizer_L (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) :
    (T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) ≤
      Subgroup.normalizer (L : Set G) := by
  refine sup_le (inf_le_right.trans (hc.L0_le_normalizer_L h37 h38 h37c h38c)) ?_
  intro q hq
  refine hc.mem_normalizer_L_of_lr h37 h38 h37c h38c (Setup.T_le_fsuM hq.1) (A := 1) (B := 1) ?_
  rw [Om4.lr_one]
  exact bar_eq_one_of_mem_centralizer e _ hq.2

theorem mem_Q_of_psi_eq_one (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (k : ↥(fsuL0 T L)) (hk : ψ k = 1) :
    (k : G) ∈ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  have h := hc.bar_L0 k
  rw [hk, map_one] at h
  exact S.sup_inf_centralizer_le h37c h38c ⟨Subgroup.mem_sup_left k.2, mem_centralizer_of_bar e _ h⟩

theorem isSylowTwoOf_inf_L (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) :
    IsSylowTwoOf (T ⊓ L) L := by
  have h := A4.isSylowTwoOf_inf_normal S.isSylowTwoOf_T_inf_L0 S.L_le_L0
    (hc.L0_le_normalizer_L h37 h38 h37c h38c)
  rwa [inf_assoc, inf_eq_right.mpr S.L_le_L0] at h

theorem exists_mem_inf_L (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat)
    {γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
    (hγ : γ ∈ (uni K).prod (uni K)) (hγL : γ ∈ (L.subgroupOf (fsuL0 T L)).map ψ) :
    ∃ l ∈ T ⊓ L, ∃ hl : l ∈ fsuL0 T L, ψ ⟨l, hl⟩ = γ := by
  rw [← hc.sylow] at hγ
  obtain ⟨w, hw, hψw⟩ := hγ
  obtain ⟨l, hl, hψl⟩ := hγL
  have hq := hc.mem_Q_of_psi_eq_one h37c h38c (w * l⁻¹) (by
    rw [map_mul, map_inv, hψw, hψl, mul_inv_cancel])
  have hwT : (w : G) ∈ T := (Subgroup.mem_subgroupOf.mp hw).1
  have hlT : (l : G) ∈ T := by
    have e : (l : G) = ((w * l⁻¹ : ↥(fsuL0 T L)) : G)⁻¹ * w := by simp
    rw [e]
    exact T.mul_mem (T.inv_mem hq.1) hwT
  exact ⟨l, ⟨hlT, Subgroup.mem_subgroupOf.mp hl⟩, l.2, hψl⟩

theorem borelOf_L_le (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G))) :
    L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ D ⊔ T := by
  rintro x ⟨hxL, hxN⟩
  have hxL0 : x ∈ fsuL0 T L := S.L_le_L0 hxL
  have hψxL : ψ ⟨x, hxL0⟩ ∈ (L.subgroupOf (fsuL0 T L)).map ψ :=
    ⟨⟨x, hxL0⟩, Subgroup.mem_subgroupOf.mpr hxL, rfl⟩
  have hut : ∀ g : SpecialLinearGroup (Fin 2) K, g * u1 K * g⁻¹ ∈ uni K → g ∈ utT K := by
    intro g hg
    obtain ⟨c, hc'⟩ := mem_uni_iff.mp hg
    have h1 := FactsFrob.isUT_of_conj_u1 (G := Matrix.SpecialLinearGroup.toGL g) (c := c) (by
      rw [← map_inv]
      show (g : Matrix (Fin 2) (Fin 2) K) * (u1 K : Matrix (Fin 2) (Fin 2) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
      rw [← hc', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul])
    exact h1
  have hconjT : ∀ l ∈ T ⊓ L, ∀ hl : l ∈ fsuL0 T L,
      ψ ⟨x * l * x⁻¹, (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem hxL0 hl)
        ((fsuL0 T L).inv_mem hxL0)⟩ ∈ (uni K).prod (uni K) := by
    intro l hl hlL
    have h1 : x * l * x⁻¹ ∈ T ⊓ L := (Subgroup.mem_normalizer_iff.mp hxN l).mp hl
    exact (hc.mem_T_iff h37c h38c _).mp h1.1
  have hψ : ψ ⟨x, hxL0⟩ ∈ (utT K).prod (utT K) := by
    rcases hc.map_L h37c h38c with hL | hL
    · rw [hL] at hψxL
      have hx2 : (ψ ⟨x, hxL0⟩).2 = 1 := hψxL
      obtain ⟨l, hl, hlL, hψl⟩ := hc.exists_mem_inf_L h37c h38c
        (γ := (u1 K, 1)) ⟨u1_mem, (uni K).one_mem⟩ (by rw [hL]; exact MonoidHom.mem_ker.mpr rfl)
      have h2 := hconjT l hl hlL
      have e : (⟨x * l * x⁻¹, (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem hxL0 hlL)
          ((fsuL0 T L).inv_mem hxL0)⟩ : ↥(fsuL0 T L)) = ⟨x, hxL0⟩ * ⟨l, hlL⟩ * ⟨x, hxL0⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hψl] at h2
      refine ⟨hut _ h2.1, ?_⟩
      rw [hx2]
      exact (utT K).one_mem
    · rw [hL] at hψxL
      have hx1 : (ψ ⟨x, hxL0⟩).1 = 1 := hψxL
      obtain ⟨l, hl, hlL, hψl⟩ := hc.exists_mem_inf_L h37c h38c
        (γ := (1, u1 K)) ⟨(uni K).one_mem, u1_mem⟩ (by rw [hL]; exact MonoidHom.mem_ker.mpr rfl)
      have h2 := hconjT l hl hlL
      have e : (⟨x * l * x⁻¹, (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem hxL0 hlL)
          ((fsuL0 T L).inv_mem hxL0)⟩ : ↥(fsuL0 T L)) = ⟨x, hxL0⟩ * ⟨l, hlL⟩ * ⟨x, hxL0⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hψl] at h2
      refine ⟨?_, hut _ h2.2⟩
      rw [hx1]
      exact (utT K).one_mem
  rw [← hc.map_normalizer h37c h38c] at hψ
  obtain ⟨m, hm, hψm⟩ := hψ
  have hq := hc.mem_Q_of_psi_eq_one h37c h38c (⟨x, hxL0⟩ * m⁻¹) (by
    rw [map_mul, map_inv, hψm, mul_inv_cancel])
  have hmN : (m : G) ∈ fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) :=
    Subgroup.mem_subgroupOf.mp hm
  have hN₀ : fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) ≤ D ⊔ T :=
    (le_antisymm (Vol2.Ch10.SecB.C11AmS.le_sup_of_hall S.isSylowTwoOf_T_inf_L0_normalizer hD)
      (sup_le S.isSylowTwoOf_T_inf_L0_normalizer.1 hD.1)).le.trans
        (sup_le (inf_le_left.trans le_sup_right) le_sup_left)
  have e : x = ((⟨x, hxL0⟩ * m⁻¹ : ↥(fsuL0 T L)) : G) * m := by simp
  rw [e]
  exact mul_mem (Subgroup.mem_sup_right hq.1) (hN₀ hmN)

theorem comm_mem_Q (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) {s u : G} (hs : s ∈ T ⊓ fsuL0 T L)
    (hu : u ∈ T ⊓ fsuL0 T L) :
    s * u * s⁻¹ * u⁻¹ ∈ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  have hs' := (hc.mem_T_iff h37c h38c ⟨s, hs.2⟩).mp hs.1
  have hu' := (hc.mem_T_iff h37c h38c ⟨u, hu.2⟩).mp hu.1
  have h1 := uni_mul_comm hs'.1 hu'.1
  have h2 := uni_mul_comm hs'.2 hu'.2
  exact hc.mem_Q_of_psi_eq_one h37c h38c (⟨s, hs.2⟩ * ⟨u, hu.2⟩ * ⟨s, hs.2⟩⁻¹ * ⟨u, hu.2⟩⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    apply Prod.ext
    · simp only [Prod.fst_mul, Prod.fst_inv, Prod.fst_one]
      rw [h1]
      group
    · simp only [Prod.snd_mul, Prod.snd_inv, Prod.snd_one]
      rw [h2]
      group)

theorem exists_other_factor (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) :
    ∃ u₀ ∈ T ⊓ fsuL0 T L, u₀ ∉ L ∧
      ∀ l ∈ L, l * u₀ * l⁻¹ * u₀⁻¹ ∈ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  have hu : u1 K ≠ 1 := fun h1 => by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 1) h1
    simp [u1] at this
  rcases hc.map_L h37c h38c with hL | hL
  · obtain ⟨w, hw, hψw⟩ := (show ((1, u1 K) : SpecialLinearGroup (Fin 2) K × _) ∈
        ((T ⊓ fsuL0 T L).subgroupOf (fsuL0 T L)).map ψ by
      rw [hc.sylow]; exact ⟨(uni K).one_mem, u1_mem⟩)
    refine ⟨w, Subgroup.mem_subgroupOf.mp hw, fun hwL => hu ?_, fun l hl => ?_⟩
    · have h1 : ψ w ∈ (L.subgroupOf (fsuL0 T L)).map ψ :=
        ⟨w, Subgroup.mem_subgroupOf.mpr hwL, rfl⟩
      rw [hL, hψw] at h1
      exact h1
    · have hl2 : (ψ ⟨l, S.L_le_L0 hl⟩).2 = 1 := by
        have h1 : ψ ⟨l, S.L_le_L0 hl⟩ ∈ (L.subgroupOf (fsuL0 T L)).map ψ :=
          ⟨⟨l, S.L_le_L0 hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
        rw [hL] at h1
        exact h1
      have hq := hc.mem_Q_of_psi_eq_one h37c h38c
        (⟨l, S.L_le_L0 hl⟩ * w * ⟨l, S.L_le_L0 hl⟩⁻¹ * w⁻¹)
        (by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hψw]
          apply Prod.ext
          · simp
          · simp [hl2])
      exact hq
  · obtain ⟨w, hw, hψw⟩ := (show ((u1 K, 1) : SpecialLinearGroup (Fin 2) K × _) ∈
        ((T ⊓ fsuL0 T L).subgroupOf (fsuL0 T L)).map ψ by
      rw [hc.sylow]; exact ⟨u1_mem, (uni K).one_mem⟩)
    refine ⟨w, Subgroup.mem_subgroupOf.mp hw, fun hwL => hu ?_, fun l hl => ?_⟩
    · have h1 : ψ w ∈ (L.subgroupOf (fsuL0 T L)).map ψ :=
        ⟨w, Subgroup.mem_subgroupOf.mpr hwL, rfl⟩
      rw [hL, hψw] at h1
      exact h1
    · have hl1 : (ψ ⟨l, S.L_le_L0 hl⟩).1 = 1 := by
        have h1 : ψ ⟨l, S.L_le_L0 hl⟩ ∈ (L.subgroupOf (fsuL0 T L)).map ψ :=
          ⟨⟨l, S.L_le_L0 hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
        rw [hL] at h1
        exact h1
      have hq := hc.mem_Q_of_psi_eq_one h37c h38c
        (⟨l, S.L_le_L0 hl⟩ * w * ⟨l, S.L_le_L0 hl⟩⁻¹ * w⁻¹)
        (by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hψw]
          apply Prod.ext
          · simp [hl1]
          · simp)
      exact hq

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
