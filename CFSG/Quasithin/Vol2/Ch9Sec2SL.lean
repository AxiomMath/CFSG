module

public import CFSG.Quasithin.Vol2.Ch9Sec2Z

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin.H CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open CFSG.QuasithinUnique

section Prod

variable {A B : Type*} [Group A] [Group B]

theorem nonempty_ker_snd_equiv : Nonempty (↥(MonoidHom.snd A B).ker ≃* A) := by
  refine ⟨MulEquiv.ofBijective ((MonoidHom.fst A B).comp (MonoidHom.snd A B).ker.subtype)
    ⟨fun x y hxy => ?_, fun a => ⟨⟨(a, 1), rfl⟩, rfl⟩⟩⟩
  have hx : (x : A × B).2 = 1 := x.2
  have hy : (y : A × B).2 = 1 := y.2
  exact Subtype.ext (Prod.ext hxy (hx.trans hy.symm))

theorem nonempty_ker_fst_equiv : Nonempty (↥(MonoidHom.fst A B).ker ≃* B) := by
  refine ⟨MulEquiv.ofBijective ((MonoidHom.snd A B).comp (MonoidHom.fst A B).ker.subtype)
    ⟨fun x y hxy => ?_, fun b => ⟨⟨(1, b), rfl⟩, rfl⟩⟩⟩
  have hx : (x : A × B).1 = 1 := x.2
  have hy : (y : A × B).1 = 1 := y.2
  exact Subtype.ext (Prod.ext (hx.trans hy.symm) hxy)

theorem eq_of_le_of_isSimpleGroup {N C : Subgroup (A × B)} [IsSimpleGroup ↥N] (hC : C.Normal)
    (hCN : C ≤ N) (hC1 : C ≠ ⊥) : C = N := by
  refine le_antisymm hCN fun x hx => ?_
  have := hC.subgroupOf N
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.subgroupOf N) with h | h
  · exfalso
    apply hC1
    rw [eq_bot_iff]
    intro c hc
    have hc' : (⟨c, hCN hc⟩ : ↥N) ∈ C.subgroupOf N := hc
    rw [h, Subgroup.mem_bot] at hc'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hc')
  · have : (⟨x, hx⟩ : ↥N) ∈ C.subgroupOf N := h ▸ Subgroup.mem_top _
    exact this

theorem eq_ker_of_normal_of_isSimpleGroup [IsSimpleGroup A] [IsSimpleGroup B]
    (hcA : Subgroup.center A = ⊥) (hcB : Subgroup.center B = ⊥) {N : Subgroup (A × B)}
    (hN : N.Normal) [IsSimpleGroup ↥N] :
    N = (MonoidHom.snd A B).ker ∨ N = (MonoidHom.fst A B).ker := by
  have := hN.comap (MonoidHom.inl A B)
  have := hN.comap (MonoidHom.inr A B)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inl A B)) with h1 | h1
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inr A B)) with h2 | h2
    · exfalso
      obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : ↥N)
      apply hx1
      have hx₁ : x.1 = 1 := by
        have hc : x.1 ∈ Subgroup.center A := Subgroup.mem_center_iff.mpr fun a => by
          have hm : x * (MonoidHom.inl A B a * x⁻¹ * (MonoidHom.inl A B a)⁻¹) ∈ N :=
            N.mul_mem hx (hN.conj_mem _ (N.inv_mem hx) _)
          have he : x * (MonoidHom.inl A B a * x⁻¹ * (MonoidHom.inl A B a)⁻¹) =
              MonoidHom.inl A B (x.1 * (a * x.1⁻¹ * a⁻¹)) := by
            ext <;> simp
          rw [he, ← Subgroup.mem_comap, h1, Subgroup.mem_bot] at hm
          calc a * x.1 = (x.1 * (a * x.1⁻¹ * a⁻¹))⁻¹ * (x.1 * a) := by group
            _ = x.1 * a := by rw [hm, inv_one, one_mul]
        rw [hcA, Subgroup.mem_bot] at hc
        exact hc
      have hx₂ : x.2 = 1 := by
        have hc : x.2 ∈ Subgroup.center B := Subgroup.mem_center_iff.mpr fun b => by
          have hm : x * (MonoidHom.inr A B b * x⁻¹ * (MonoidHom.inr A B b)⁻¹) ∈ N :=
            N.mul_mem hx (hN.conj_mem _ (N.inv_mem hx) _)
          have he : x * (MonoidHom.inr A B b * x⁻¹ * (MonoidHom.inr A B b)⁻¹) =
              MonoidHom.inr A B (x.2 * (b * x.2⁻¹ * b⁻¹)) := by
            ext <;> simp
          rw [he, ← Subgroup.mem_comap, h2, Subgroup.mem_bot] at hm
          calc b * x.2 = (x.2 * (b * x.2⁻¹ * b⁻¹))⁻¹ * (x.2 * b) := by group
            _ = x.2 * b := by rw [hm, inv_one, one_mul]
        rw [hcB, Subgroup.mem_bot] at hc
        exact hc
      exact Subtype.ext (Prod.ext hx₁ hx₂)
    · right
      have hle : (MonoidHom.fst A B).ker ≤ N := fun x hx => by
        have h3 : x.2 ∈ N.comap (MonoidHom.inr A B) := h2 ▸ Subgroup.mem_top _
        have e : x = MonoidHom.inr A B x.2 := Prod.ext hx rfl
        rw [e]
        exact h3
      have hne : (MonoidHom.fst A B).ker ≠ ⊥ := by
        obtain ⟨b, hb⟩ := exists_ne (1 : B)
        intro h0
        have : MonoidHom.inr A B b ∈ (MonoidHom.fst A B).ker := rfl
        rw [h0, Subgroup.mem_bot] at this
        exact hb (congrArg Prod.snd this)
      exact (eq_of_le_of_isSimpleGroup (MonoidHom.normal_ker _) hle hne).symm
  · left
    have hle : (MonoidHom.snd A B).ker ≤ N := fun x hx => by
      have h3 : x.1 ∈ N.comap (MonoidHom.inl A B) := h1 ▸ Subgroup.mem_top _
      have e : x = MonoidHom.inl A B x.1 := Prod.ext rfl hx
      rw [e]
      exact h3
    have hne : (MonoidHom.snd A B).ker ≠ ⊥ := by
      obtain ⟨a, ha⟩ := exists_ne (1 : A)
      intro h0
      have : MonoidHom.inl A B a ∈ (MonoidHom.snd A B).ker := rfl
      rw [h0, Subgroup.mem_bot] at this
      exact ha (congrArg Prod.fst this)
    exact (eq_of_le_of_isSimpleGroup (MonoidHom.normal_ker _) hle hne).symm

theorem center_eq_bot_of_commutator_eq_top [IsSimpleGroup A]
    (h : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤) : Subgroup.center A = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center A) with h1 | h1
  · exact h1
  · exfalso
    have h0 : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top x) y
    rw [h0] at h
    exact bot_ne_top h

end Prod

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem inf_centralizer_L_le (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) :
    L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 L := by
  rw [← Vol2.Ch10.SecA.inf_pCoreOf_fsuL0 S.hyp.fsu.maximal.1]
  exact fun x hx => ⟨hx.1, S.inf_centralizer_L0_le h37c h38c ⟨S.L_le_L0 hx.1, hx.2⟩⟩

theorem pCoreOf_L_le_centralizer : pCoreOf 2 L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  rw [← Vol2.Ch10.SecA.inf_pCoreOf_fsuL0 S.hyp.fsu.maximal.1]
  exact fun x hx => (S.pCoreOf_L0_le_Q hx.2).2

theorem exists_quot_equiv_sl2 (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  obtain ⟨K, _, _, _, hK, e, he⟩ := S.exists_coord
  have hK' : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) S.two_le
  have := Om4.sl2_isSimple hK4
  have hc := center_eq_bot_of_commutator_eq_top (Om4.sl2_commutator_eq_top hK4)
  have hloc := S.hyp.fsu.maximal.1
  have hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G) := S.L_le_L0.trans S.L0_le_normalizer_V
  let ψ : ↥L →* MulAut (Om4.VM K) := (MulAut.congr e).toMonoidHom.comp
    ((conjAct (fsuV T I)).comp (Subgroup.inclusion hLN))
  have hψ : ∀ l : ↥L, ψ l = MulAut.congr e (conjAct (fsuV T I) (Subgroup.inclusion hLN l)) :=
    fun _ => rfl
  have hψρ : ψ.range ≤ (Om4.rho (K := K)).range := by
    rintro _ ⟨l, rfl⟩
    obtain ⟨γ, hγ⟩ := exists_rho_of_mem_L0 he (k := Subgroup.inclusion hLN l) (S.L_le_L0 l.2)
    exact ⟨γ, by rw [hψ, hγ]⟩
  have hnorm : (ψ.range.comap (Om4.rho (K := K))).Normal := by
    refine ⟨fun h hh g => ?_⟩
    rw [Subgroup.mem_comap] at hh ⊢
    obtain ⟨l, hl⟩ := hh
    obtain ⟨x, hxL, hx⟩ := exists_mem_L0_of_rho he g
    have hxl : (x : G) * l * (x : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Vol2.Ch10.SecA.fsuL0_le_normalizer hloc hxL) l).mp l.2
    refine ⟨⟨_, hxl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv, ← hl, ← hx, hψ, hψ, ← map_inv, ← map_mul, ← map_mul,
      ← map_inv, ← map_mul, ← map_mul]
    congr 2
  have hker : ψ.ker = CFSG.pCore 2 ↥L := by
    rw [← Vol2.Ch10.SecA.subgroupOf_pCoreOf]
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ, MulEquiv.map_eq_one_iff,
      A4.conjAct_eq_one_iff]
    exact ⟨fun h => S.inf_centralizer_L_le h37c h38c ⟨l.2, h⟩,
      fun h => S.pCoreOf_L_le_centralizer h⟩
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Vol2.Ch10.SecA.isSimpleGroup_of_not_normal h37c h38c S.hyp.fsu.simple S.hyp.fsu.nonabelian
      S.hyp.fsu.qtke S.hyp.fsu.faithful S.not_le_normalizer_L
  let e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  have hmap : (ψ.range.comap (Om4.rho (K := K))).map (Om4.rho (K := K)) = ψ.range :=
    Subgroup.map_comap_eq_self hψρ
  let e2 : ↥(ψ.range.comap (Om4.rho (K := K))) ≃* ↥ψ.range :=
    (Subgroup.equivMapOfInjective _ _ Om4.rho_injective).trans (MulEquiv.subgroupCongr hmap)
  let e3 : ↥(ψ.range.comap (Om4.rho (K := K))) ≃* (↥L ⧸ CFSG.pCore 2 ↥L) := e2.trans e1.symm
  have : IsSimpleGroup ↥(ψ.range.comap (Om4.rho (K := K))) := e3.isSimpleGroup
  refine ⟨K, inferInstance, inferInstance, hK', ?_⟩
  rcases eq_ker_of_normal_of_isSimpleGroup hc hc hnorm with h | h
  · obtain ⟨f⟩ := nonempty_ker_snd_equiv (A := Matrix.SpecialLinearGroup (Fin 2) K)
      (B := Matrix.SpecialLinearGroup (Fin 2) K)
    exact ⟨e3.symm.trans ((MulEquiv.subgroupCongr h).trans f)⟩
  · obtain ⟨f⟩ := nonempty_ker_fst_equiv (A := Matrix.SpecialLinearGroup (Fin 2) K)
      (B := Matrix.SpecialLinearGroup (Fin 2) K)
    exact ⟨e3.symm.trans ((MulEquiv.subgroupCongr h).trans f)⟩

end Setup

end CFSG.Quasithin.H13.Ch9
